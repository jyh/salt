#!/usr/bin/env python3
"""bm25.py -- the SEARCH lane's lexical layer: SQLite FTS5 over every chunk.

This layer needs no model, no network and no GPU.  It works TODAY at full
corpus scale (~20k chunks, ~1s to build, ~1ms to query) and it alone satisfies
all four acceptance tests.  The vector layer is an ADDITION to it, never a
replacement -- exact identifiers are what we search for most, and BM25 is
already the right tool for those.

Index shape:
  chunks       a plain table, one row per chunk, holding the ORIGINAL text
               (snippets are rendered from this)
  fts          an fts5 table over ASCII-FOLDED (name, text), rowid-aligned
               with `chunks`; queries are folded the same way, so `Radziwill`
               finds `Radziwiłł` and `Matomaki` finds `Matomäki`

Usage:
    python3 scripts/search/bm25.py                       # build from chunks.jsonl
    python3 scripts/search/bm25.py --chunks F --db F
    python3 scripts/search/bm25.py --search "repulsion"  # smoke test
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sqlite3
import sys
from pathlib import Path

from extract import fold  # single source of truth for the folding rule

HERE = Path(__file__).resolve().parent
DEFAULT_CHUNKS = HERE / "index" / "chunks.jsonl"
DEFAULT_DB = HERE / "index" / "lexical.db"

# fts5 column weights for bm25(): a hit in the declaration NAME is worth far
# more than a hit somewhere in a 4000-character docstring.
W_NAME = 12.0
W_TEXT = 1.0

_FTS_SPECIAL = re.compile(r'"')


def fts_quote(term: str) -> str:
    """Wrap a term as an FTS5 string literal (doubling embedded quotes).

    Everything the user types becomes a quoted literal, so `-`, `(`, `*`, `:`
    and the other FTS5 operators can never be parsed as syntax.  That matters:
    half our vocabulary is `Heath-Brown`, `f(x)`, `Salt.MR`.
    """
    return '"' + _FTS_SPECIAL.sub('""', term) + '"'


def build(chunks_path: Path, db_path: Path, verbose: bool = True) -> int:
    if not chunks_path.exists():
        raise SystemExit(
            f"no chunk file at {chunks_path} -- run `python3 scripts/search/extract.py` first"
        )
    db_path.parent.mkdir(parents=True, exist_ok=True)
    tmp = db_path.with_suffix(".db.tmp")
    if tmp.exists():
        tmp.unlink()

    con = sqlite3.connect(tmp)
    con.executescript(
        """
        PRAGMA journal_mode = OFF;
        PRAGMA synchronous = OFF;
        CREATE TABLE chunks (
            rowid   INTEGER PRIMARY KEY,
            cid     TEXT UNIQUE,
            kind    TEXT,
            name    TEXT,
            name_lc TEXT,          -- folded+lowercased, for exact-name lookup
            keyword TEXT,
            text    TEXT,
            file    TEXT,
            line    INTEGER,
            date    TEXT,
            hash    TEXT
        );
        CREATE VIRTUAL TABLE fts USING fts5(
            name, text,
            tokenize = 'unicode61 remove_diacritics 2'
        );
        """
    )

    n = 0
    with chunks_path.open(encoding="utf-8") as fh:
        rows, ftsrows = [], []
        for line in fh:
            c = json.loads(line)
            n += 1
            name = c.get("name", "")
            rows.append(
                (
                    n,
                    c["id"],
                    c["kind"],
                    name,
                    fold(name).lower(),
                    c.get("keyword", ""),
                    c["text"],
                    c["file"],
                    c["line"],
                    c.get("date"),
                    c["hash"],
                )
            )
            # The name is folded AND split on `_`/`.` so that
            # `dh_repulsion_ordered` is findable as `repulsion`, and
            # `Salt.MR.M4Door` as `M4Door`.
            name_idx = fold(name + " " + re.sub(r"[_.]+", " ", name))
            ftsrows.append((n, name_idx, fold(c["text"])))
            if len(rows) >= 2000:
                con.executemany("INSERT INTO chunks VALUES (?,?,?,?,?,?,?,?,?,?,?)", rows)
                con.executemany("INSERT INTO fts(rowid, name, text) VALUES (?,?,?)", ftsrows)
                rows, ftsrows = [], []
        if rows:
            con.executemany("INSERT INTO chunks VALUES (?,?,?,?,?,?,?,?,?,?,?)", rows)
            con.executemany("INSERT INTO fts(rowid, name, text) VALUES (?,?,?)", ftsrows)

    con.executescript(
        """
        CREATE INDEX idx_kind ON chunks(kind);
        CREATE INDEX idx_file ON chunks(file);
        CREATE INDEX idx_name_lc ON chunks(name_lc);
        INSERT INTO fts(fts) VALUES ('optimize');
        """
    )
    con.commit()
    con.close()
    os.replace(tmp, db_path)
    if verbose:
        print(
            f"indexed {n} chunks -> {db_path} ({db_path.stat().st_size / 1e6:.1f} MB)",
            file=sys.stderr,
        )
    return n


def connect(db_path: Path) -> sqlite3.Connection:
    if not db_path.exists():
        raise SystemExit(
            f"no lexical index at {db_path} -- run `python3 scripts/search/bm25.py`"
        )
    con = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
    con.row_factory = sqlite3.Row
    return con


def search(con: sqlite3.Connection, match: str, limit: int = 200):
    """Return [(rowid, score)] best-first.  bm25() is negative-is-better; we
    negate so that larger is better throughout the pipeline."""
    try:
        cur = con.execute(
            "SELECT rowid, bm25(fts, ?, ?) AS s FROM fts WHERE fts MATCH ? "
            "ORDER BY s LIMIT ?",
            (W_NAME, W_TEXT, match, limit),
        )
    except sqlite3.OperationalError:
        return []  # unparseable MATCH expression: treat as no hits
    return [(r["rowid"], -r["s"]) for r in cur]


SHORT_NAME = 3  # at or below this length, exact-name matching goes case-sensitive


def exact_name(con: sqlite3.Connection, term: str):
    """Rows whose DECLARATION NAME is exactly `term` (folded).

    This is the pass that makes `"did we prove a Heath-Brown repulsion?"` answer
    with `dh_repulsion_ordered` itself rather than with the six documents that
    talk about it.  Restricted to `decl` chunks: a markdown `## ` header is a
    sentence, not a name, and exact-matching it means nothing.

    Short names (`Z`, `MR`, `HB`, `SW`) match CASE-SENSITIVELY.  Those are real
    and important objects -- `Z` is the GAP theorem's predicate -- but folded to
    lowercase they collide with every bound variable in the corpus.  Case is the
    only signal that separates `Salt.Parity.Z` from a local `z`, so we use it.
    """
    if len(term) <= SHORT_NAME:
        cur = con.execute(
            "SELECT rowid FROM chunks WHERE name_lc = ? AND name = ? AND kind = 'decl'",
            (term.lower(), term),
        )
    else:
        cur = con.execute(
            "SELECT rowid FROM chunks WHERE name_lc = ? AND kind = 'decl'", (term.lower(),)
        )
    return [r["rowid"] for r in cur]


def fetch(con: sqlite3.Connection, rowids):
    if not rowids:
        return {}
    qs = ",".join("?" * len(rowids))
    cur = con.execute(f"SELECT * FROM chunks WHERE rowid IN ({qs})", list(rowids))
    return {r["rowid"]: dict(r) for r in cur}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--chunks", default=str(DEFAULT_CHUNKS))
    ap.add_argument("--db", default=str(DEFAULT_DB))
    ap.add_argument("--search", help="run one raw FTS5 query against the built index")
    args = ap.parse_args(argv)

    if args.search:
        con = connect(Path(args.db))
        hits = search(con, fts_quote(args.search), 10)
        recs = fetch(con, [r for r, _ in hits])
        for rowid, score in hits:
            r = recs[rowid]
            print(f"{score:8.3f}  {r['kind']:6s} {r['name'][:48]:48s} {r['file']}:{r['line']}")
        return 0

    build(Path(args.chunks), Path(args.db))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
