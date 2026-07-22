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

| Ref | Value |
|---|---|
| Checkout HEAD at container boot | `b41d51f play: evening wake -- cloud sweep empty …` (2026-07-22 15:36 -0700) |
| `git ls-remote origin main` | `cfe59c6…` (`play: SOURCES-ARRAY CONFIRMED (probe 200) …`, 2026-07-22 15:49 -0700) |
| Staleness | **1 commit / ~13 min behind.** The boot checkout was one commit stale; `origin/main` had advanced `b41d51f → cfe59c6`. Negligible and content-irrelevant (the newer commit is the trial-armed play note itself). This branch was cut from the fresh `origin/main` (`cfe59c6`), so the report works from current tip. |

**Egress hypothesis re-confirmed independently** (probe at Step 1, 22:49 UTC):

| Host | HTTP |
|---|---|
| `github.com/leanprover/lean4/releases` | **200** |
| `elan.lean-lang.org/elan-init.sh` | **200** |
| `release.lean-lang.org` | **200** |

The Night-1…4 blocker (GitHub-releases 403 repo-scope) is gone. The sources-array
fix is live. Ladder is clear to run.

## 1. Environment

| Property | Value | Δ vs Night 4 |
|---|---|---|
| OS / kernel | Linux 6.18.5 `#1 SMP PREEMPT_DYNAMIC`, x86_64 | same |
| CPU count | **4 vCPU** | same |
| RAM | 16.46 GB (`MemTotal 16461176 kB`) | same |
| Disk | `/dev/vda` 252 G, **30 G available**, 22% used | same |
| Working dir | `/home/user/salt` (cloned fresh at boot) | same |
| Target toolchain | `leanprover/lean4:v4.32.0-rc1` (from `lean-toolchain`) | same |
| Pre-installed | `curl` (`/usr/bin/curl`); **no `elan`, no `lake`** at boot | same — toolchain must be acquired |

The 4-vCPU / 16 GB profile is unchanged from Night 4, so build+checker timings
here are directly comparable to the M5-Pro/18-core numbers in
`lean4checker-local-1.md` as a cloud-vs-workstation contrast.

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
| 1 | Freshness + environment | ~1 min | ✅ done |
| 2 | Toolchain (elan + first lake) | — | pending |
| 3 | Cache get | — | pending |
| 4 | Build | — | pending |
| 5 | Checker | — | pending |
| 6 | Finalize | — | pending |
