#!/usr/bin/env python3
"""embed.py -- the SEARCH lane's vector layer.  LOCAL EMBEDDINGS ONLY.

PRIVACY LAW (hard, not negotiable): corpus content never leaves this machine.
Both backends run the model locally.  The only network traffic this script can
ever cause is a ONE-TIME download of model WEIGHTS (HuggingFace, for the
sentence-transformers backend) -- weights come in, nothing goes out.  No corpus
text is ever sent to any API, and there is no code path here that could.

Backends, tried in order (`--backend` overrides):

  1. ollama   -- if the daemon answers on localhost:11434 AND has pulled an
                 embedding model (nomic-embed-text / mxbai-embed-large).
                 Best quality, zero setup cost if you already run ollama.
  2. sentence-transformers -- in scripts/search/.venv, model all-MiniLM-L6-v2
                 (23M params, 384-dim: small and fast, which is what a smoke
                 pass wants).

Incremental by content hash: `{hash -> vector}` is carried across runs, so a
rebuild after editing three files re-embeds three files' worth of chunks.  That
is the derived-never-remembered law with a cache in front of it.

    python3 scripts/search/embed.py                 # SMOKE: ledger+doc+500 decls
    python3 scripts/search/embed.py --full          # the whole corpus (SLOW)
    python3 scripts/search/embed.py --backends      # what's available, then exit

Run `--full` only when the machine is free: it is ~20k forward passes.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

# Quiet + single-threaded BEFORE anything imports huggingface_hub: the token
# nag and the weight-loading progress bar are emitted at import time, so they
# cannot be silenced from inside the model loader.
for _k, _v in (
    ("OMP_NUM_THREADS", "1"),
    ("TOKENIZERS_PARALLELISM", "false"),
    ("HF_HUB_DISABLE_PROGRESS_BARS", "1"),
    ("HF_HUB_DISABLE_TELEMETRY", "1"),
    ("HF_HUB_DISABLE_IMPLICIT_TOKEN", "1"),
    ("TRANSFORMERS_VERBOSITY", "error"),
    ("TRANSFORMERS_NO_ADVISORY_WARNINGS", "1"),
):
    os.environ.setdefault(_k, _v)


def _hf_cached(repo: str) -> bool:
    """Is `repo` already in the local HuggingFace cache?"""
    root = os.environ.get("HF_HUB_CACHE") or (
        os.path.join(os.environ["HF_HOME"], "hub")
        if os.environ.get("HF_HOME")
        else os.path.expanduser("~/.cache/huggingface/hub")
    )
    return os.path.isdir(os.path.join(root, "models--" + repo.replace("/", "--")))


HERE = Path(__file__).resolve().parent
INDEX = HERE / "index"
CHUNKS = INDEX / "chunks.jsonl"
VECTORS = INDEX / "vectors.npy"
VEC_META = INDEX / "vec_meta.json"
VENV_PY = HERE / ".venv" / "bin" / "python"

OLLAMA_URL = "http://localhost:11434"
OLLAMA_PREFERRED = ("nomic-embed-text", "mxbai-embed-large", "all-minilm", "bge-m3")
ST_MODEL = "sentence-transformers/all-MiniLM-L6-v2"

# Once the weights are on disk, go fully offline.  This must be decided BEFORE
# huggingface_hub is imported -- its native download layer reads the setting at
# import time and prints an auth nag on every single query otherwise.  A search
# tool that touches the network to answer a question is the wrong tool.
if _hf_cached(ST_MODEL):
    os.environ.setdefault("HF_HUB_OFFLINE", "1")

SMOKE_DECLS = 500
EMBED_CHARS = 1200  # embedding models truncate anyway; keep the head


# --------------------------------------------------------------------------
# Backend discovery
# --------------------------------------------------------------------------


def ollama_models(timeout: float = 2.0):
    """Embedding models the local ollama daemon has pulled, or None if no daemon."""
    try:
        with urllib.request.urlopen(f"{OLLAMA_URL}/api/tags", timeout=timeout) as r:
            tags = json.loads(r.read())
    except (urllib.error.URLError, OSError, ValueError, TimeoutError):
        return None
    names = [m.get("name", "") for m in tags.get("models", [])]
    found = []
    for pref in OLLAMA_PREFERRED:
        for nm in names:
            if nm.split(":")[0] == pref or nm == pref:
                found.append(nm)
    return found


def have_sentence_transformers() -> bool:
    try:
        import sentence_transformers  # noqa: F401
        return True
    except ImportError:
        return False


def detect_backend(prefer: str = "auto"):
    """Return (backend, model) or (None, None)."""
    if prefer in ("auto", "ollama"):
        models = ollama_models()
        if models:
            return "ollama", models[0]
        if prefer == "ollama":
            if models is None:
                print("ollama: daemon not answering on :11434 (`ollama serve`)", file=sys.stderr)
            else:
                print(
                    "ollama: running, but no embedding model pulled "
                    f"(try `ollama pull {OLLAMA_PREFERRED[0]}`)",
                    file=sys.stderr,
                )
            return None, None
    if prefer in ("auto", "sentence-transformers"):
        if have_sentence_transformers():
            return "sentence-transformers", ST_MODEL
    return None, None


# --------------------------------------------------------------------------
# Embedding
# --------------------------------------------------------------------------

_ST_CACHE: dict = {}


def _st_model(model: str):
    if model not in _ST_CACHE:
        import logging
        import warnings

        warnings.filterwarnings("ignore")
        logging.getLogger("sentence_transformers").setLevel(logging.ERROR)
        for noisy in ("transformers", "huggingface_hub", "huggingface_hub.file_download"):
            logging.getLogger(noisy).setLevel(logging.ERROR)

        import torch
        from sentence_transformers import SentenceTransformer

        torch.set_num_threads(1)  # the ceremony owns the cores; we take one
        _ST_CACHE[model] = SentenceTransformer(model, device="cpu")
    return _ST_CACHE[model]


def embed_texts(texts, model: str, backend: str):
    """Embed a list of strings.  Returns a list of float lists (unnormalised)."""
    if backend == "ollama":
        req = urllib.request.Request(
            f"{OLLAMA_URL}/api/embed",
            data=json.dumps({"model": model, "input": list(texts)}).encode(),
            headers={"Content-Type": "application/json"},
        )
        with urllib.request.urlopen(req, timeout=300) as r:
            return json.loads(r.read())["embeddings"]
    if backend == "sentence-transformers":
        m = _st_model(model)
        return m.encode(list(texts), batch_size=16, show_progress_bar=False).tolist()
    raise RuntimeError(f"unknown embedding backend {backend!r}")


# --------------------------------------------------------------------------
# Selection + driver
# --------------------------------------------------------------------------


def load_chunks(path: Path):
    if not path.exists():
        raise SystemExit(f"no chunks at {path} -- run extract.py first")
    with path.open(encoding="utf-8") as fh:
        return [json.loads(line) for line in fh]


def select(chunks, full: bool, smoke_decls: int):
    """--full is everything; the smoke pass is all prose + a declaration sample.

    Prose first because that is where the amnesia lives: the ledger and the
    design docs are what we fail to re-find, and there are only ~1.8k of them.
    """
    if full:
        return chunks
    prose = [c for c in chunks if c["kind"] in ("ledger", "doc")]
    decls = [c for c in chunks if c["kind"] == "decl"]
    step = max(1, len(decls) // smoke_decls) if smoke_decls else 1
    return prose + decls[::step][:smoke_decls]


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--full", action="store_true", help="embed every chunk (slow)")
    ap.add_argument("--backend", default="auto",
                    choices=["auto", "ollama", "sentence-transformers"])
    ap.add_argument("--backends", action="store_true", help="report availability and exit")
    ap.add_argument("--smoke-decls", type=int, default=SMOKE_DECLS)
    ap.add_argument("--batch", type=int, default=32)
    ap.add_argument("--chunks", default=str(CHUNKS))
    args = ap.parse_args(argv)

    # Re-exec into the venv when the current interpreter can't do the work.
    # Done before ANY reporting so that `--backends` describes the interpreter
    # that would actually run, not the bare system python that launched us.
    if not os.environ.get("SALT_EMBED_REEXEC"):
        try:
            import numpy  # noqa: F401
            ok = have_sentence_transformers() or bool(ollama_models())
        except ImportError:
            ok = False
        if not ok and VENV_PY.exists():
            os.environ["SALT_EMBED_REEXEC"] = "1"
            os.execv(str(VENV_PY), [str(VENV_PY), str(Path(__file__).resolve()), *sys.argv[1:]])

    if args.backends:
        om = ollama_models()
        print(f"ollama daemon        : {'up' if om is not None else 'down'}")
        print(f"ollama embed models  : {om if om else '(none)'}")
        print(f"sentence-transformers: {'yes' if have_sentence_transformers() else 'no'}")
        print(f"venv                 : {VENV_PY if VENV_PY.exists() else '(absent)'}")
        b, m = detect_backend(args.backend)
        print(f"selected             : {b} / {m}")
        return 0

    try:
        os.nice(10)  # never outbid a running ceremony for a core
    except OSError:
        pass

    import numpy as np

    backend, model = detect_backend(args.backend)
    if backend is None:
        print(
            "no local embedding backend available.\n"
            "  -> `ollama serve` + `ollama pull nomic-embed-text`, or\n"
            "  -> python3 -m venv scripts/search/.venv && "
            "scripts/search/.venv/bin/pip install sentence-transformers\n"
            "the lexical+alias engine works without this; vectors are an addition.",
            file=sys.stderr,
        )
        return 2

    chunks = load_chunks(Path(args.chunks))
    todo = select(chunks, args.full, args.smoke_decls)
    mode = "FULL" if args.full else f"SMOKE ({args.smoke_decls} decl sample)"
    print(f"backend={backend} model={model}  mode={mode}  chunks={len(todo)}", file=sys.stderr)

    # --- incremental: reuse vectors whose content hash is unchanged --------
    cache: dict[str, "np.ndarray"] = {}
    if VECTORS.exists() and VEC_META.exists():
        try:
            old_meta = json.loads(VEC_META.read_text(encoding="utf-8"))
            if old_meta.get("model") == model and old_meta.get("backend") == backend:
                old = np.load(VECTORS)
                for i, h in enumerate(old_meta.get("hashes", [])):
                    if i < len(old):
                        cache[h] = old[i]
                print(f"cache: {len(cache)} vectors reusable", file=sys.stderr)
        except Exception as exc:
            print(f"cache: ignored ({exc})", file=sys.stderr)

    need = [c for c in todo if c["hash"] not in cache]
    print(f"to embed: {len(need)} new, {len(todo) - len(need)} cached", file=sys.stderr)

    t0 = time.time()
    for i in range(0, len(need), args.batch):
        batch = need[i : i + args.batch]
        vecs = embed_texts([c["text"][:EMBED_CHARS] for c in batch], model, backend)
        for c, v in zip(batch, vecs):
            cache[c["hash"]] = np.asarray(v, dtype="float32")
        done = min(i + args.batch, len(need))
        el = time.time() - t0
        rate = done / el if el else 0
        eta = (len(need) - done) / rate if rate else 0
        print(f"\r  {done}/{len(need)}  {rate:.1f}/s  eta {eta:0.0f}s   ",
              end="", file=sys.stderr, flush=True)
    if need:
        print(file=sys.stderr)

    # --- write, L2-normalised so cosine is a plain dot product ------------
    mat = np.stack([cache[c["hash"]] for c in todo]).astype("float32")
    norms = np.linalg.norm(mat, axis=1, keepdims=True)
    norms[norms == 0] = 1.0
    mat /= norms

    INDEX.mkdir(parents=True, exist_ok=True)
    np.save(VECTORS, mat)
    VEC_META.write_text(
        json.dumps(
            {
                "model": model,
                "backend": backend,
                "dim": int(mat.shape[1]),
                "full": bool(args.full),
                "count": len(todo),
                "built": time.strftime("%Y-%m-%dT%H:%M:%S"),
                "ids": [c["id"] for c in todo],
                "hashes": [c["hash"] for c in todo],
            },
            ensure_ascii=False,
        ),
        encoding="utf-8",
    )
    print(
        f"wrote {VECTORS} {mat.shape} ({VECTORS.stat().st_size / 1e6:.1f} MB) "
        f"in {time.time() - t0:.0f}s",
        file=sys.stderr,
    )
    if not args.full:
        print("NOTE: smoke pass. `python3 scripts/search/embed.py --full` when the cores are free.",
              file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
