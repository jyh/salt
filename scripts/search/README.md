# The SEARCH lane — hybrid corpus search

A local, hybrid (lexical + vector + alias) search engine over the salt corpus.
It is the query layer of the amnesia countermeasure: the thing you reach for
when you know *we did this* but not what we called it.

## The failure it exists to fix

`Salt/MR` is 47% of the corpus and the whole of it implements
Matomäki–Radziwiłł(–Tao). The ledger never once writes the word "Matomäki".
So `grep -ri matomaki` returns nothing, and the honest conclusion from a
grep — *we have not done this* — is the exact opposite of the truth.

That is worse than a gap. It is a **confident false negative**, and no amount
of care at write-time prevents it: we name things in Lean by what they *do*
(`MRTUniformityXi`, `doorLadder`, `towerFlat_width_ge`) and we name them in
conversation by *who they are from*. The two vocabularies never touch.

The fix is three layers, in increasing order of cleverness and decreasing
order of reliability:

1. **lexical** (BM25 over SQLite FTS5) — exact identifiers, ~1ms, always right;
2. **alias** (`aliases.json`) — the human-name ↔ corpus-name bridge, hand-kept;
3. **vector** (local embeddings) — for when you can't name the thing at all.

Layer 1 alone answers every acceptance test below. Layers 2 and 3 are
additions to it, never replacements: when the vectors are missing the tool
runs lexical+alias and says so.

## Usage

```sh
# build (order matters; both are fast)
python3 scripts/search/extract.py      # corpus -> index/chunks.jsonl   (~2s)
python3 scripts/search/bm25.py         # chunks -> index/lexical.db     (~1s)

# ask
python3 scripts/search/query.py "did we prove a Heath-Brown repulsion?"
python3 scripts/search/query.py "the Toll" -n 20 --kind decl
python3 scripts/search/query.py "Matomäki" --explain     # show alias expansion
python3 scripts/search/query.py "parity wall" --no-alias # what alias buys
```

Flags: `-n N` (results), `--kind decl|ledger|doc` (repeatable), `--no-vector`,
`--no-alias`, `--explain` (expansion + per-pass contributions).

Query cost: **~0.15s lexical-only**, ~5s with vectors (the model load
dominates; the search itself is a single matrix multiply).

## The derived-never-remembered law

Everything under `index/` is a **pure function of the working tree**. Nothing
in it is a record; nothing in it is authoritative; none of it is committed.
If the index and the corpus disagree, the index is wrong — rebuild it:

```sh
python3 scripts/search/extract.py && python3 scripts/search/bm25.py
```

Never hand-edit `chunks.jsonl`. Never "fix" a search result by patching the
index — fix the corpus, or fix `aliases.json`, and rebuild.

Rebuilds are cheap because chunks are **content-hashed**: `embed.py` carries a
`{hash → vector}` cache across runs, so re-embedding after a day's work costs
only that day's changed chunks. The lexical index is rebuilt from scratch every
time; at 1 second, incrementality would be a pure loss.

The single exception — the one file here that is *remembered*, not derived — is
`aliases.json`. It holds knowledge that exists nowhere in the corpus (that "the
Toll" is `towerFlat_width_ge`, that "the door" is MRT). Add to it whenever you
catch yourself saying a name the corpus does not spell.

## The privacy law

**Corpus content never leaves this machine.** Both embedding backends run
locally. There is no code path in this directory that sends corpus text to any
network service, and there must never be one.

The only network traffic any of this can cause is a one-time download of model
*weights* from HuggingFace (sentence-transformers backend). Weights come in;
nothing goes out. Once cached, `embed.py` sets `HF_HUB_OFFLINE=1` and the
network is not touched again.

## Layers

### `extract.py` — the chunk extractor

Three sources, one JSONL record each
(`{id, kind, name, text, file, line, date?, hash}`):

| kind | source | split on |
|---|---|---|
| `decl` | `Salt/**/*.lean` | each top-level declaration |
| `ledger` | `docs/blueprints/flags.md` | `## ` headers, date-stamped |
| `doc` | `docs/**/*.md` | `## ` headers |

Declarations carry their docstring (the `/-- … -/` immediately above,
attributes allowed in between) and their statement text (source lines through
the `:=`/`where`/`by` that ends the signature, capped at 15 lines).

Extraction is **regex over source text, deliberately**. It is not a shortcut
for calling Lean: the retrieval surface that failed us is the one `grep` sees,
so the index must be built from exactly that surface. It also means the
extractor never invokes `lake`, and so can run while a ceremony owns the cores.

The one place this needs real care is block comments. The corpus has enormous
`/-! … -/` module docstrings full of prose that wraps so a line begins with
`theorem` or `class`; a naive line regex invents ~40 declarations out of
documentation. `comment_mask()` tracks nesting depth (Lean block comments
nest) and string literals, and column 0 inside a comment is never a
declaration. Verified: `grep` finds 27 lines starting with `class ` under
`Salt/`, of which **2** are declarations and 25 are wrapped prose.

`docs/sources/` is excluded: it holds external copyright-encumbered material.

### `aliases.json` — the canonical-name table

`[{canonical, aliases:[…]}]`. A query naming any member of a group also
searches every other member, at a discount (`ALIAS_WEIGHT = 0.55` — an
expansion is a guess, and is priced below what the user actually typed).

Seeded with the 22 groups the fleet actually says out loud: MRT/the door,
the M4 road, S0–S16, Heath-Brown/T-BAL/repulsion, the Toll/width law, the
fulcrum, TwinBar/parity wall/Z/GAP, VMVT/VK, SW, BV, Chen, Brun, Maynard,
Ramaré, Halász, Shiu, Rosser-Iwaniec, Turán-Kubilius, Pólya-Vinogradov,
Weil/Stepanov, van der Corput, entropy/Chowla.

### `bm25.py` — the lexical layer

SQLite FTS5, `unicode61 remove_diacritics 2`, plus a Python ASCII fold applied
identically to documents and queries. The fold matters: FTS5 folds combining
marks, so `Matomäki` → `matomaki` for free, but **not** letters that are their
own codepoint — `ł`, `ø`, `đ`. `Radziwiłł` is exactly that case and it is a
name we search for.

Ranking inputs, fused by reciprocal rank fusion (`RRF_K = 60`):

| pass | weight | what it catches |
|---|---|---|
| exact declaration name | **+0.30 flat** | you named the thing |
| all query terms (AND) | 3.0 | the document is about all of it |
| any query term (OR) | 1.5 | partial topical match |
| per-term, name column | 2.5 | `repulsion` inside `dh_repulsion_ordered` |
| per-term, full text | 1.0 | ordinary BM25 |
| alias-expanded terms | × 0.55 | the bridge |
| vector top-20 | 1.2 | you couldn't name it at all |

Exact-name match is a flat bonus rather than a ranked pass, sized to clear the
top of a typical RRF stack: asking about the Toll must return
`towerFlat_width_ge`, not the six memos that mention it. Names of ≤3
characters (`Z`, `MR`, `HB`, `SW`) match **case-sensitively** — real and
important objects, but folded to lowercase they collide with every bound
variable in the corpus, and case is the only signal separating
`Salt.Parity.Z` from a local `z`.

### `embed.py` — the vector layer

Backends, tried in order (`--backend` overrides):

1. **ollama** — if the daemon answers on `localhost:11434` *and* has an
   embedding model pulled (`nomic-embed-text`, `mxbai-embed-large`, …).
2. **sentence-transformers** — in `scripts/search/.venv`, `all-MiniLM-L6-v2`
   (23M params, 384-dim: small and fast, which is what a smoke pass wants).

```sh
python3 scripts/search/embed.py --backends   # what's available
python3 scripts/search/embed.py              # SMOKE pass
python3 scripts/search/embed.py --full       # the whole corpus
```

`query.py` and `embed.py` both re-exec into `.venv` automatically when the
system interpreter can't do the work, so plain `python3 …` is always correct.
The test is "can this interpreter embed a query", not "does numpy import" —
a system python with numpy and no torch would otherwise leave the vector
layer silently idle forever.

## ⚠ The `--full` pass is DEFERRED

The landed vector index is a **smoke pass only**: all 1,824 ledger+doc chunks
plus an evenly-spaced 500-declaration sample = 2,324 of 20,577 chunks. It was
run single-threaded and `nice`-d because a ceremony held the cores.

**The vector layer is therefore incomplete for declarations.** Lexical+alias
covers all 20,577 and is unaffected.

To finish it, when the machine is free:

```sh
nice -n 15 python3 scripts/search/embed.py --full
```

Measured smoke rate was 52 chunks/s single-threaded, so `--full` is ~7 minutes
and ~30 MB of `vectors.npy`. It is incremental — the 2,324 already-embedded
chunks are reused from the hash cache, so only ~18k are new.

## What is committed

Committed: `extract.py`, `bm25.py`, `embed.py`, `query.py`, `aliases.json`,
this README. Not committed (all gitignored): `.venv/`, `index/` —
`chunks.jsonl`, `lexical.db`, `vectors.npy`, `vec_meta.json`. Derived, never
remembered.

## Acceptance tests

The four queries the lane was built to answer, all in **lexical+alias** mode
(no vectors required). Re-run them after any change to ranking or aliases:

```sh
python3 scripts/search/query.py "Matomäki"            --no-vector -n 4
python3 scripts/search/query.py "Heath-Brown repulsion" --no-vector -n 4
python3 scripts/search/query.py "parity barrier"      --no-vector -n 4
python3 scripts/search/query.py "width law"           --no-vector -n 4
```

| # | query | must surface | result |
|---|---|---|---|
| a | `Matomäki` | `Salt/…/MRTDoor.lean`, `Salt/MR` | ✅ `MRTUniformityXiL2` / `MRTUniformityXi` / `MRTUniformity` at ranks 1–3 — **via the alias table alone**; the literal string appears nowhere in those files |
| b | `Heath-Brown repulsion` | `dh_repulsion_ordered` | ✅ rank 3 (`Salt/SW/TBalR8.lean:1752`), under the ledger entry recording it landing and the `RESULTS.md` row naming it |
| c | `parity barrier` | `Salt/Parity/Z.lean` theorems | ✅ `ParityBarrier` rank 1 (`Z.lean:107`); `Z`, `TwinPrimeConjecture`, `sufficient_true_not_parityInv` follow |
| d | `width law` | `towerFlat_width_ge` / `towerShape_width_ge` | ✅ ranks 2, 3, 4 (`towerFlat_width_ge`, `towerFlat_width_le`, `towerShape_width_ge`), under the ⟦THE TOLL CHRISTENED⟧ ruling that named them |

Test (a) is the whole lane in one line: the alias table turns a name we only
ever *say* into the three declarations that are the thing itself.

## Extending

- **A search came back empty and shouldn't have** → the name you used is
  missing from `aliases.json`. Add it to the right group. That is the
  expected maintenance mode, and it is the cheapest fix in the system.
- **A wrong hit outranks the right one** → tune weights at the top of
  `query.py`; re-run the acceptance tests before committing.
- **New corpus location** → add a source to `extract.py`; keep the record
  shape identical so the downstream layers need no change.
