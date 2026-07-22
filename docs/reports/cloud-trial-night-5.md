# Cloud Trial — Night 5 Full-Ladder Report

**Trial:** `salt-night-shift-trial-5` — the "full ladder with measured numbers"
run. The hypothesis that blocked Nights 1–4 (GitHub-releases egress /
repo-scope) is **already CONFIRMED resolved** by a probe minutes before this
firing: `github.com/leanprover/lean4/releases` returned **200** in this
environment (the sources-array fix works). This mission is no longer about
*whether* the ladder runs — it is about *what it costs*: toolchain, cache,
build, checker, measured end to end.
**Executor:** SALT NIGHT-5 agent (Opus 4.8, `claude-opus-4-8`), scheduled
routine.
**Start (UTC):** 2026-07-22 22:49 UTC.
**Predecessors:** `cloud-trial-night-1.md` … `-night-4.md` (all NO-GO at the
egress / toolchain-acquisition layer); local audit `lean4checker-local-1.md`
(the checker recipe — 259 content modules across 7 tracks).

**Verdict up front:** _pending — filled at finalize (Step 6)._

This report is written **incrementally** (the incremental-report law): a
skeleton first, then an update committed+pushed after every step, so the
`cloud-trial/night-5` branch tells the story live even if the session is killed
mid-run.

---

## 0. Freshness check

_pending (Step 1)_

## 1. Environment

_pending (Step 1)_

## 2. Toolchain acquisition (elan + first `lake`)

_pending (Step 2)_

## 3. Mathlib cache (`lake exe cache get`)

_pending (Step 3)_

## 4. Corpus build (`lake build`)

_pending (Step 4)_

## 5. Kernel re-verification (built-in `leanchecker`)

_pending (Step 5)_

## 6. Finalize: per-session setup cost, GO/NO-GO, night-mission template

_pending (Step 6)_

---

### Step timings (wall-clock) — running tally

| Step | What | Wall-clock | Status |
|---|---|---|---|
| 0 | Skeleton report + branch | — | ✅ done |
| 1 | Freshness + environment | — | pending |
| 2 | Toolchain (elan + first lake) | — | pending |
| 3 | Cache get | — | pending |
| 4 | Build | — | pending |
| 5 | Checker | — | pending |
| 6 | Finalize | — | pending |
