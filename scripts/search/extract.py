#!/usr/bin/env python3
"""extract.py -- the SEARCH lane's chunk extractor.

Walks the salt corpus and emits one JSONL record per retrievable chunk.
Three sources:

  (a) DECLARATIONS -- every top-level `theorem/lemma/def/structure/abbrev/...`
      under `Salt/**/*.lean`, with its docstring (the `/-- ... -/` immediately
      above, attributes allowed in between), its statement text (source lines
      through the `:=` / `where` / `by` that ends the signature, capped at
      MAX_STMT_LINES), and `file:line`.

  (b) LEDGER -- `docs/blueprints/flags.md`, split on `## ` headers, carrying
      the header's date stamp where present.

  (c) DOCS -- every other `docs/**/*.md`, split on `## ` headers.

The extraction is deliberately REGEX-BASED over source text.  That is not a
shortcut: the retrieval surface that failed us is the one `grep` sees, so the
index must be built from exactly that surface.  No `lake`/`lean` invocation --
this script must be runnable while the cores are busy.

Derived, never remembered: the output is a pure function of the working tree.
Rebuild by re-running; never hand-edit `chunks.jsonl`.

Usage:
    python3 scripts/search/extract.py                 # -> scripts/search/index/chunks.jsonl
    python3 scripts/search/extract.py --out FILE
    python3 scripts/search/extract.py --stats         # counts only, no write
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import unicodedata
from pathlib import Path

# --------------------------------------------------------------------------
# Layout
# --------------------------------------------------------------------------

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent  # scripts/search/ -> scripts/ -> repo root
DEFAULT_OUT = HERE / "index" / "chunks.jsonl"

LEAN_ROOT = REPO / "Salt"
DOCS_ROOT = REPO / "docs"
FLAGS = DOCS_ROOT / "blueprints" / "flags.md"

# Directories under docs/ that hold external, copyright-encumbered source
# material.  They are local-only (see .gitignore / OPERATIONS) and stay out of
# the index so that no derived artifact can carry them.
DOCS_SKIP_DIRS = {"sources"}

MAX_STMT_LINES = 15
MAX_CHUNK_CHARS = 4000

# --------------------------------------------------------------------------
# Text normalisation
# --------------------------------------------------------------------------

# SQLite FTS5's `remove_diacritics 2` folds combining marks, but NOT letters
# that are their own codepoint with no decomposition -- `ł`, `ø`, `đ`, `ħ`.
# Radziwiłł is exactly that case, and it is a name we search for.  So we fold
# in Python, at index AND at query time, over the same table.
_HARD_FOLD = str.maketrans(
    {
        "ł": "l", "Ł": "L",
        "ø": "o", "Ø": "O",
        "đ": "d", "Đ": "D",
        "ħ": "h", "Ħ": "H",
        "ı": "i", "İ": "I",
        "æ": "ae", "Æ": "AE",
        "œ": "oe", "Œ": "OE",
        "ß": "ss",
        "’": "'", "‘": "'",
        "“": '"', "”": '"',
        "–": "-", "—": "-",
    }
)


def fold(s: str) -> str:
    """ASCII-fold for the lexical index: NFKD, drop combining marks, hard-map
    the stroked/slashed letters.  Applied identically to documents and queries."""
    s = s.translate(_HARD_FOLD)
    s = unicodedata.normalize("NFKD", s)
    return "".join(ch for ch in s if not unicodedata.combining(ch))


def content_hash(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


# --------------------------------------------------------------------------
# (a) Lean declarations
# --------------------------------------------------------------------------

DECL_KEYWORDS = (
    "theorem", "lemma", "def", "structure", "abbrev",
    "instance", "class", "inductive", "opaque", "axiom",
)

_MODIFIERS = r"(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+"

# A top-level declaration starts at column 0.  Attributes may sit on the same
# line (`@[simp] lemma foo ...`) or on their own lines above.
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"          # inline attributes
    r"(?:" + _MODIFIERS + r")*"      # modifiers, any order
    r"(" + "|".join(DECL_KEYWORDS) + r")"
    r"(?:\s+([^\s:({\[⦃⟨]+))?"       # the name (absent for anonymous instances)
    r"(?=\s|$|:|\(|\{|\[)"
)

ATTR_LINE_RE = re.compile(r"^\s*@\[")


def comment_mask(lines: list[str]) -> list[bool]:
    """True for each line whose column 0 lies inside a `/- ... -/` block comment.

    Lean block comments nest, and the corpus is full of long `/-! ... -/` module
    docstrings containing prose that starts a line with `theorem`.  Without this
    mask the extractor would invent declarations out of documentation.
    """
    mask = []
    depth = 0
    for line in lines:
        mask.append(depth > 0)
        i, n = 0, len(line)
        in_str = False
        while i < n:
            ch = line[i]
            if in_str:
                if ch == "\\":
                    i += 2
                    continue
                if ch == '"':
                    in_str = False
                i += 1
                continue
            if depth == 0 and ch == '"':
                in_str = True
                i += 1
                continue
            if ch == "-" and i + 1 < n and line[i + 1] == "-" and depth == 0:
                break  # line comment
            if ch == "/" and i + 1 < n and line[i + 1] == "-":
                depth += 1
                i += 2
                continue
            if ch == "-" and i + 1 < n and line[i + 1] == "/" and depth > 0:
                depth -= 1
                i += 2
                continue
            i += 1
    return mask


def grab_docstring(lines: list[str], decl_idx: int) -> str:
    """The `/-- ... -/` immediately above `decl_idx`, skipping attribute lines."""
    j = decl_idx - 1
    while j >= 0 and (ATTR_LINE_RE.match(lines[j]) or not lines[j].strip()):
        # blank lines break the association; attribute lines do not
        if not lines[j].strip():
            return ""
        j -= 1
    if j < 0:
        return ""
    if not lines[j].rstrip().endswith("-/"):
        return ""
    end = j
    while j >= 0 and "/--" not in lines[j]:
        j -= 1
        if end - j > 200:
            return ""
    if j < 0:
        return ""
    body = "\n".join(lines[j : end + 1])
    body = body.replace("/--", "", 1)
    body = body.rsplit("-/", 1)[0]
    return "\n".join(ln.strip() for ln in body.splitlines()).strip()


def grab_statement(lines: list[str], decl_idx: int) -> str:
    """Source lines from the declaration head through the end of its signature.

    Stops at the `:=` / `where` / `by` that opens the proof or body, or after
    MAX_STMT_LINES, whichever comes first.
    """
    out = []
    for k in range(decl_idx, min(decl_idx + MAX_STMT_LINES, len(lines))):
        raw = lines[k]
        stripped = raw.rstrip()
        cut = None
        for marker in (" := ", ":=", " where", " by"):
            pos = stripped.find(marker)
            if pos != -1 and (cut is None or pos < cut):
                cut = pos
        if cut is not None:
            piece = stripped[:cut].rstrip()
            if piece:
                out.append(piece)
            break
        out.append(stripped)
    return "\n".join(out).strip()


def extract_lean(root: Path, repo: Path):
    chunks = []
    for path in sorted(root.rglob("*.lean")):
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            print(f"warn: cannot read {path}: {exc}", file=sys.stderr)
            continue
        lines = text.splitlines()
        mask = comment_mask(lines)
        rel = str(path.relative_to(repo))
        for i, line in enumerate(lines):
            if mask[i] or not line or line[0].isspace():
                continue
            m = DECL_RE.match(line)
            if not m:
                continue
            kw, name = m.group(1), m.group(2)
            if name is None or name in ("where", "by", "extends"):
                if kw == "instance":
                    name = f"instance@{path.stem}:{i + 1}"
                else:
                    continue
            doc = grab_docstring(lines, i)
            stmt = grab_statement(lines, i)
            # Docstring first, then the statement.  The name is NOT prepended:
            # the statement's own head line already carries `<keyword> <name>`,
            # and the name is separately indexed in the FTS `name` column, so
            # repeating it here would only spoil the snippet's first line.
            body = ((doc + "\n") if doc else "") + stmt
            body = body[:MAX_CHUNK_CHARS] or name
            chunks.append(
                {
                    "id": f"decl:{rel}:{i + 1}:{name}",
                    "kind": "decl",
                    "name": name,
                    "keyword": kw,
                    "text": body,
                    "file": rel,
                    "line": i + 1,
                    "hash": content_hash(body),
                }
            )
    return chunks


# --------------------------------------------------------------------------
# (b) + (c) Markdown
# --------------------------------------------------------------------------

DATE_RE = re.compile(r"\b(\d{4}-\d{2}-\d{2})\b")
H2_RE = re.compile(r"^## +(.*\S)\s*$")
H1_RE = re.compile(r"^# +(.*\S)\s*$")


def split_markdown(path: Path, repo: Path, kind: str):
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        print(f"warn: cannot read {path}: {exc}", file=sys.stderr)
        return []
    lines = text.splitlines()
    rel = str(path.relative_to(repo))

    title = ""
    for ln in lines[:40]:
        m = H1_RE.match(ln)
        if m:
            title = m.group(1)
            break

    # section boundaries: (start_line_idx, header_text)
    bounds = [(i, m.group(1)) for i, ln in enumerate(lines) if (m := H2_RE.match(ln))]
    sections = []
    if not bounds or bounds[0][0] > 0:
        end = bounds[0][0] if bounds else len(lines)
        sections.append((0, title or path.stem, lines[0:end]))
    for n, (start, header) in enumerate(bounds):
        end = bounds[n + 1][0] if n + 1 < len(bounds) else len(lines)
        sections.append((start, header, lines[start:end]))

    out = []
    for start, header, seg in sections:
        body_txt = "\n".join(seg).strip()
        if not body_txt:
            continue
        head = f"{title} :: {header}" if title and title != header else header
        body = (head + "\n" + body_txt)[:MAX_CHUNK_CHARS]
        m = DATE_RE.search(header) or DATE_RE.search(body_txt[:400])
        rec = {
            "id": f"{kind}:{rel}:{start + 1}",
            "kind": kind,
            "name": header,
            "text": body,
            "file": rel,
            "line": start + 1,
            "hash": content_hash(body),
        }
        if m:
            rec["date"] = m.group(1)
        out.append(rec)
    return out


def extract_docs(docs_root: Path, repo: Path):
    ledger, docs = [], []
    if FLAGS.exists():
        ledger = split_markdown(FLAGS, repo, "ledger")
    for path in sorted(docs_root.rglob("*.md")):
        if path.resolve() == FLAGS.resolve():
            continue
        parts = set(path.relative_to(docs_root).parts[:-1])
        if parts & DOCS_SKIP_DIRS:
            continue
        docs.extend(split_markdown(path, repo, "doc"))
    return ledger, docs


# --------------------------------------------------------------------------
# Driver
# --------------------------------------------------------------------------


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", default=str(DEFAULT_OUT), help="output JSONL path")
    ap.add_argument("--repo", default=str(REPO), help="repository root")
    ap.add_argument("--stats", action="store_true", help="print counts, write nothing")
    args = ap.parse_args(argv)

    repo = Path(args.repo).resolve()
    decls = extract_lean(repo / "Salt", repo)
    ledger, docs = extract_docs(repo / "docs", repo)
    allc = decls + ledger + docs

    seen, uniq = set(), []
    for c in allc:
        if c["id"] in seen:
            continue
        seen.add(c["id"])
        uniq.append(c)

    print(
        f"decl={len(decls)} ledger={len(ledger)} doc={len(docs)} "
        f"total={len(uniq)} (dropped {len(allc) - len(uniq)} duplicate ids)",
        file=sys.stderr,
    )
    by_kw = {}
    for c in decls:
        by_kw[c["keyword"]] = by_kw.get(c["keyword"], 0) + 1
    print("  by keyword: " + ", ".join(f"{k}={v}" for k, v in sorted(by_kw.items())), file=sys.stderr)

    if args.stats:
        return 0

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    tmp = out.with_suffix(out.suffix + ".tmp")
    with tmp.open("w", encoding="utf-8") as fh:
        for c in uniq:
            fh.write(json.dumps(c, ensure_ascii=False) + "\n")
    os.replace(tmp, out)
    print(f"wrote {out} ({out.stat().st_size / 1e6:.1f} MB)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
