#!/usr/bin/env python3
"""query.py -- the SEARCH lane's CLI.  Ask the corpus a question in English.

    python3 scripts/search/query.py "did we prove a Heath-Brown repulsion?"

Pipeline:

    query
      -> ASCII-fold + tokenise
      -> ALIAS EXPANSION (aliases.json): a query naming any member of a group
         also searches every other member, at a discount
      -> LEXICAL: SQLite FTS5, several passes (all-terms AND, any-term OR,
         one pass per expansion term)
      -> VECTOR: cosine top-K over local embeddings, IF vectors.npy exists
      -> RECIPROCAL RANK FUSION over every pass
      -> ranked, deduped, printed with file:line and a snippet

Degradation is graceful and total: with no vectors the tool runs lexical+alias
only, which is the mode all four acceptance tests are stated in.  Nothing here
ever contacts the network.

Options:
    -n N          how many results (default 12)
    --kind K      restrict to decl | ledger | doc (repeatable)
    --no-vector   force lexical-only even if vectors exist
    --no-alias    force literal search (useful for measuring what alias buys)
    --explain     show the expansion and the per-pass contributions
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from extract import fold  # noqa: E402
import bm25  # noqa: E402

HERE = Path(__file__).resolve().parent
INDEX = HERE / "index"
DB = INDEX / "lexical.db"
ALIASES = HERE / "aliases.json"
VECTORS = INDEX / "vectors.npy"
VEC_META = INDEX / "vec_meta.json"
VENV_PY = HERE / ".venv" / "bin" / "python"

# --- fusion constants ------------------------------------------------------
RRF_K = 60.0          # the standard reciprocal-rank-fusion damping
W_AND = 3.0           # a doc matching ALL the user's words is the best signal
W_OR = 1.5            # ...then one matching some of them
W_TERM = 1.0          # ...then a single literal term
W_NAMECOL = 2.5       # ...a hit in the declaration name beats one in prose
ALIAS_WEIGHT = 0.55   # an expansion is a guess; price it below what was typed
W_VECTOR = 1.2        # semantic neighbours, when we have them

# An EXACT declaration-name match is not a ranked pass, it is an answer: added
# as a flat bonus, sized to clear the top of a typical RRF stack (~0.15).  The
# whole point of the lane is that asking about the Toll returns
# `towerFlat_width_ge`, not the six memos that mention it.
BONUS_EXACT = 0.30
BONUS_EXACT_ALIAS = 0.18

TOKEN_RE = re.compile(r"[A-Za-z0-9_'][A-Za-z0-9_.']*")
STOP = {
    "a", "an", "the", "we", "did", "do", "does", "is", "are", "was", "were",
    "of", "in", "on", "for", "to", "and", "or", "it", "this", "that", "with",
    "have", "has", "had", "prove", "proved", "proof", "there", "any", "what",
    "where", "which", "who", "how", "our", "us", "i", "you", "be", "been",
    "from", "by", "at", "as", "not", "but", "can", "could", "will", "would",
    "should", "must", "may", "might", "all", "some", "no", "than", "then",
    "when", "why", "get", "got", "use", "used", "using", "need", "about",
    "into", "over", "under", "out", "up", "if", "so", "such", "here", "its",
    "already", "still", "ever", "just", "only", "also", "actually", "really",
    "anything", "something", "thing", "stuff", "know", "think", "say", "said",
}


# --------------------------------------------------------------------------
# Alias expansion
# --------------------------------------------------------------------------


def load_groups(path: Path):
    if not path.exists():
        return []
    data = json.loads(path.read_text(encoding="utf-8"))
    return data.get("groups", [])


def expand(query: str, groups) -> tuple[list[str], list[tuple[str, str]]]:
    """Return (expansion_terms, matched_groups).

    A single-token alias matches as a whole word; a multi-word alias matches as
    a folded substring.  Both sides are folded, so `Matomaki` hits `Matomäki`.
    """
    q = fold(query).lower()
    qwords = set(TOKEN_RE.findall(q))
    terms, matched = [], []
    seen = set()
    for g in groups:
        hit = None
        for a in g["aliases"] + [g["canonical"]]:
            fa = fold(a).lower()
            if " " in fa or "-" in fa:
                if fa in q:
                    hit = a
                    break
            elif fa in qwords:
                hit = a
                break
        if hit is None:
            continue
        matched.append((g["canonical"], hit))
        for a in g["aliases"]:
            key = fold(a).lower()
            if key in seen or key in qwords:
                continue
            seen.add(key)
            terms.append(a)
    return terms, matched


# --------------------------------------------------------------------------
# Vector layer (optional)
# --------------------------------------------------------------------------


def maybe_reexec_into_venv() -> None:
    """If vectors exist but numpy does not, re-exec under scripts/search/.venv.

    Lets `python3 query.py ...` do the right thing from a bare system python:
    lexical-only needs nothing, and the vector path silently upgrades itself.
    """
    if os.environ.get("SALT_SEARCH_REEXEC"):
        return
    if not (VECTORS.exists() and VEC_META.exists()):
        return
    # The test is "can this interpreter embed a query", not "does numpy import":
    # the system python may well have numpy and no torch, which would leave the
    # vector layer silently idle forever.
    try:
        import numpy  # noqa: F401
        import embed as _embed

        if _embed.detect_backend("auto")[0] is not None:
            return
    except ImportError:
        pass
    if VENV_PY.exists():
        os.environ["SALT_SEARCH_REEXEC"] = "1"
        os.execv(str(VENV_PY), [str(VENV_PY), str(Path(__file__).resolve()), *sys.argv[1:]])


def vector_search(query: str, limit: int):
    """Cosine top-`limit` over the local embedding matrix.  Returns
    [(cid, score)] or None when the vector layer is unavailable."""
    if not (VECTORS.exists() and VEC_META.exists()):
        return None
    try:
        import numpy as np
    except ImportError:
        return None
    try:
        import embed
    except Exception:
        return None
    meta = json.loads(VEC_META.read_text(encoding="utf-8"))
    try:
        qv = embed.embed_texts([query], meta["model"], meta["backend"])
    except Exception as exc:  # backend gone, model unpulled, ollama stopped
        print(f"  (vector layer idle: {exc})", file=sys.stderr)
        return None
    mat = np.load(VECTORS)
    q = np.asarray(qv[0], dtype="float32")
    n = np.linalg.norm(q)
    if n == 0:
        return None
    q /= n
    sims = mat @ q
    k = min(limit, len(sims))
    idx = np.argpartition(-sims, k - 1)[:k]
    idx = idx[np.argsort(-sims[idx])]
    ids = meta["ids"]
    return [(ids[i], float(sims[i])) for i in idx]


# --------------------------------------------------------------------------
# Snippets
# --------------------------------------------------------------------------


def snippet(text: str, needles, width: int = 108, lines: int = 2) -> list[str]:
    body = [ln.strip() for ln in text.splitlines() if ln.strip()]
    if not body:
        return []
    best, best_score = 0, -1
    for i, ln in enumerate(body):
        low = fold(ln).lower()
        score = sum(1 for nd in needles if nd and nd in low)
        if i == 0:
            score += 0.5  # the head line names the thing; mild default
        if score > best_score:
            best, best_score = i, score
    out = []
    for ln in body[best : best + lines]:
        out.append(ln if len(ln) <= width else ln[: width - 1] + "…")
    return out


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------


def run(query: str, n: int, kinds, use_vector: bool, use_alias: bool, explain: bool) -> int:
    con = bm25.connect(DB)
    groups = load_groups(ALIASES) if use_alias else []

    # Fold BEFORE tokenising: `Matomäki` must survive as one token, not split
    # into `Matom` + `ki` by an ASCII-only word pattern.
    raw_terms = [
        t for t in TOKEN_RE.findall(fold(query)) if t.lower() not in STOP and len(t) > 1
    ]
    alias_terms, matched = expand(query, groups) if use_alias else ([], [])

    if explain:
        print(f"query terms : {raw_terms}", file=sys.stderr)
        for canonical, hit in matched:
            print(f"alias group : {canonical!r}  (triggered by {hit!r})", file=sys.stderr)
        print(f"expansion   : {len(alias_terms)} terms", file=sys.stderr)

    # --- gather ranked passes -------------------------------------------
    passes = []  # (label, weight, [(rowid, score)])

    bonus: dict[int, float] = {}

    def add_term(term: str, label: str, weight: float, bonus_size: float) -> None:
        ft = fold(term)
        q = bm25.fts_quote(ft)
        passes.append((label, weight, bm25.search(con, q, 100)))
        # the same term restricted to the declaration-name column
        passes.append((label + "~name", weight * W_NAMECOL, bm25.search(con, f"name : {q}", 60)))
        for rowid in bm25.exact_name(con, ft):
            bonus[rowid] = max(bonus.get(rowid, 0.0), bonus_size)

    if raw_terms:
        if len(raw_terms) > 1:
            m = " AND ".join(bm25.fts_quote(t) for t in raw_terms)
            passes.append(("AND", W_AND, bm25.search(con, m, 100)))
        m = " OR ".join(bm25.fts_quote(t) for t in raw_terms)
        passes.append(("OR", W_OR, bm25.search(con, m, 200)))
        for t in raw_terms:
            add_term(t, f"term:{t}", W_TERM, BONUS_EXACT)
        # the whole query, as typed, is also a candidate identifier
        joined = "".join(raw_terms)
        for rowid in bm25.exact_name(con, joined):
            bonus[rowid] = max(bonus.get(rowid, 0.0), BONUS_EXACT)

    for a in alias_terms:
        # multi-word aliases become FTS5 phrase queries
        add_term(a, f"alias:{a}", W_TERM * ALIAS_WEIGHT, BONUS_EXACT_ALIAS)

    # --- vector pass -----------------------------------------------------
    vec_used = False
    cid_to_row = None
    if use_vector:
        vres = vector_search(query, 20)
        if vres:
            cids = [c for c, _ in vres]
            qs = ",".join("?" * len(cids))
            cur = con.execute(f"SELECT rowid, cid FROM chunks WHERE cid IN ({qs})", cids)
            cid_to_row = {r["cid"]: r["rowid"] for r in cur}
            rows = [(cid_to_row[c], s) for c, s in vres if c in cid_to_row]
            if rows:
                passes.append(("vector", W_VECTOR, rows))
                vec_used = True

    # --- reciprocal rank fusion -----------------------------------------
    fused: dict[int, float] = {}
    contrib: dict[int, list[str]] = {}
    for label, weight, hits in passes:
        for rank, (rowid, _score) in enumerate(hits):
            fused[rowid] = fused.get(rowid, 0.0) + weight / (RRF_K + rank + 1)
            contrib.setdefault(rowid, []).append(label)

    for rowid, b in bonus.items():
        fused[rowid] = fused.get(rowid, 0.0) + b
        contrib.setdefault(rowid, []).append("EXACT-NAME")

    if not fused:
        print("no hits.", file=sys.stderr)
        return 1

    order = sorted(fused.items(), key=lambda kv: -kv[1])
    recs = bm25.fetch(con, [r for r, _ in order[: n * 6 + 40]])
    if kinds:
        order = [(r, s) for r, s in order if recs.get(r, {}).get("kind") in kinds]
    order = order[:n]

    needles = [fold(t).lower() for t in raw_terms] + [fold(a).lower() for a in alias_terms]

    mode = "lexical+alias" + ("+vector" if vec_used else "")
    if not use_alias:
        mode = "lexical" + ("+vector" if vec_used else "")
    print(f"\n\033[1m{len(order)} hits\033[0m  [{mode}]  for: {query}\n")
    for i, (rowid, score) in enumerate(order, 1):
        r = recs[rowid]
        date = f"  {r['date']}" if r.get("date") else ""
        head = r["name"] or "(section)"
        if len(head) > 96:  # ledger headers are whole paragraphs
            head = head[:95] + "…"
        kind = r["kind"]
        print(f"\033[1m{i:2d}.\033[0m [{kind}] \033[1m{head}\033[0m")
        print(f"     {r['file']}:{r['line']}{date}   score {score:.4f}")
        for ln in snippet(r["text"], needles):
            print(f"     \033[2m{ln}\033[0m")
        if explain:
            print(f"     via: {', '.join(sorted(set(contrib[rowid])))[:160]}")
        print()
    return 0


def main(argv=None) -> int:
    maybe_reexec_into_venv()
    ap = argparse.ArgumentParser(
        description=__doc__.splitlines()[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("query", nargs="+")
    ap.add_argument("-n", type=int, default=12)
    ap.add_argument("--kind", action="append", choices=["decl", "ledger", "doc"])
    ap.add_argument("--no-vector", action="store_true")
    ap.add_argument("--no-alias", action="store_true")
    ap.add_argument("--explain", action="store_true")
    args = ap.parse_args(argv)
    return run(
        " ".join(args.query),
        args.n,
        set(args.kind) if args.kind else None,
        not args.no_vector,
        not args.no_alias,
        args.explain,
    )


if __name__ == "__main__":
    raise SystemExit(main())
