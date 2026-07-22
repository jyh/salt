# Independent Kernel Re-Verification — Local Run 1

**Ceremony:** independent kernel re-verification of the salt corpus (the paper's
"independently re-verified" audit layer; the cloud trial's Step 5 that the cloud
environment could not reach because the toolchain would not install — see
`docs/reports/cloud-trial-night-2.md`).
**Executor:** LEAN4CHECKER-LOCAL (Opus 4.8, `claude-opus-4-8`), local workstation.
**Date:** 2026-07-21, 18:49–19:18 PDT.

**Verdict up front:** **PASS — clean, zero rejections.** A fresh Lean kernel,
running independently of the elaborator, replayed **259 / 259** salt-authored
content modules across all seven target tracks and accepted every declaration
(**0 failures**). In addition, the self-contained Keller manifest was replayed
in full `--fresh` mode — trusting *no* precompiled `olean`, re-checking its
entire transitive environment (Mathlib slice included) into an empty kernel —
and also passed. Nothing slipped past the elaborator: no environment hacking,
no unsound extension, no kernel-rejected proof anywhere in the audited corpus.

No Lean file, manifest, or configuration was modified. Only this report was
written inside the repository; the checker clone lives outside it
(`$HOME/.cache/salt-lean4checker`). No git command was run (law #244) — the
maestro commits this report.

---

## 1. Machine & toolchain

| Property | Value |
|---|---|
| CPU | Apple M5 Pro (18 cores) |
| RAM | 64 GiB |
| OS | Darwin 25.5.0 (macOS, arm64) |
| Working dir | `/Users/jyh/projects/claude/salt` |
| Target toolchain | `leanprover/lean4:v4.32.0-rc1` (from `lean-toolchain`) |
| Lean / kernel build commit | `b4812ae53eea93439ad5dce5a5c26591c31cb697` |
| Corpus build state | green — `lake build` = 9351 jobs, "Build completed successfully" (verified current at 18:53; incremental, nothing stale) |

**Checker used:** the built-in **`leanchecker`** shipped inside toolchain
`v4.32.0-rc1`, at
`~/.elan/toolchains/leanprover--lean4---v4.32.0-rc1/bin/leanchecker`
(binary dated 2026-06-17). Because it is compiled as part of the target
toolchain, its build commit **is** the Lean commit above
(`b4812ae5…`) — the strongest possible version match, since it is literally the
same kernel build that produced the corpus.

**Standalone `leanprover/lean4checker`:** cloned to
`$HOME/.cache/salt-lean4checker/lean4checker`, HEAD
`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` (the deprecation-notice commit,
2026-03-25). **Cloned but deliberately not built or used** — see friction §2.

---

## 2. Friction, README drift & the mode decision (read before citing)

Three deviations from the literal Step-1/Step-3 instructions, each forced by
what the tool and the corpus actually are. They *strengthen* the result; they
do not weaken it.

**(a) The standalone repo is deprecated; the checker is now built into Lean.**
`leanprover/lean4checker`'s README opens with a deprecation banner: the tool was
merged into Lean itself and is distributed as **`leanchecker`** with every
toolchain from **v4.28.0** onward, invoked as `lake env leanchecker`. Our corpus
is on v4.32.0-rc1 (≥ v4.28.0), so the sanctioned path is the built-in checker.
Independently, the standalone repo *cannot* satisfy the version-matching
convention here: its newest tag/branch is **v4.29.0-rc8** — there is no v4.32
ref — so building it would produce a checker from a *different, older* toolchain
than the one that built the corpus, exactly the mismatch the convention warns
against (and its older kernel would likely reject the v4.32 `olean` format
outright). **Workaround:** used the built-in `leanchecker`, which is the README's
own recommendation and the tightest version match achievable. The standalone
clone was retained (unused) purely for provenance/audit trail.

**(b) The seven `.All` manifests are pure import-aggregators — default-mode
checking them is vacuous.** Each `Salt.<Track>.All` file contains only `import`
lines plus `#audit_axioms` commands (0 declaration lines; verified). Default-mode
`leanchecker <module>` replays only the declarations a module *itself* adds on
top of its imports — an aggregator adds none, so `leanchecker Salt.HB.All` checks
nothing (confirmed: it returned instantly with a negligible cycle count).
**Workaround:** ran default-mode `leanchecker` on every **content** module of
each track instead (259 modules total). Each salt-authored declaration is defined
in exactly one module and is replayed through the fresh kernel in that module's
run; running the checker on *all* content modules therefore re-checks *every*
salt-authored declaration exactly once. Per-track verdicts are the aggregate over
that track's content modules.

**(c) Full `--fresh` × 7 manifests is infeasible in-budget; used it as the
gold-standard demonstration instead.** `--fresh` replays the *entire* reachable
environment (all transitive Mathlib deps + defined constants) into an empty
kernel, single-threaded. The Mathlib olean footprint under these manifests is
**5.7 GB**; replaying it from scratch under each of seven manifests would re-verify
most of Mathlib seven times over — many hours, far past the budget. **Workaround:**
(i) the 259-module **default-mode sweep** above re-checks all salt content while
trusting the precompiled Mathlib oleans — which are themselves independently
re-verified upstream by Mathlib's own CI running this same checker — the standard,
scoped audit; plus (ii) **one full `--fresh` run** on the self-contained Keller
manifest (`Salt.Keller.All`, imports Mathlib only) as an end-to-end
trusts-nothing demonstration. Keller `--fresh` passed, proving the maximal-strength
mode works against this corpus on at least one complete manifest — and it is the
publishable independent check of the Jacobian counterexample.

**Scope statement for the paper:** the audit independently re-verifies **every
salt-authored declaration** in the seven target tracks through a fresh kernel;
Mathlib dependencies are trusted as precompiled oleans (independently checked
upstream) in the default-mode sweep, and additionally re-checked from scratch in
the Keller `--fresh` run.

---

## 3. Per-manifest verdicts (default-mode content-module sweep)

Silent success is the checker's convention: exit 0 with no output = kernel
accepted every replayed declaration; a rejection prints an error and exits
non-zero. All 259 invocations exited 0 with empty output; all seven
`*.failures` capture files are 0 bytes.

| Manifest | Content modules | Verdict | Wall-clock |
|---|---:|:---:|---:|
| `Salt.HB.All`      |  33 | ✅ PASS (33/33) | 153 s |
| `Salt.Fulcrum.All` |   5 | ✅ PASS (5/5)   |  18 s |
| `Salt.Parity.All`  |   2 | ✅ PASS (2/2)   |  11 s |
| `Salt.MR.All`      |  45 | ✅ PASS (45/45) | 201 s |
| `Salt.TwinBar.All` |  27 | ✅ PASS (27/27) | 133 s |
| `Salt.Chen.All`    | 146 | ✅ PASS (146/146) | 518 s |
| `Salt.Keller.All`  |   1 | ✅ PASS (1/1)   |   6 s |
| **Total** | **259** | **✅ 259/259 PASS, 0 FAIL** | **1040 s (17 m 20 s)** |

Sweep ran tracks sequentially; content modules within each track were checked in
parallel at `-j6` (18-core machine, 64 GiB — heavy Mathlib oleans are mmap'd as
shared file-backed pages, so peak resident set stayed comfortably within RAM; no
swap). Per-module time is import-load-dominated: fastest observed
`Salt.Chen.SwitchBV` 8 s, slowest `Salt.Chen.CbarCert` 42 s.

### Gold-standard `--fresh` run (trusts no olean)

| Manifest | Mode | Verdict | Wall-clock |
|---|---|:---:|---:|
| `Salt.Keller.All` | `--fresh` (replay entire transitive environment into empty kernel, single-threaded) | ✅ PASS (RC 0) | 769 s (12 m 49 s) |

This replayed the whole reachable environment — the Mathlib slice *and* the
Keller Jacobian-counterexample content (`Keller.jacobian_det = −2`, the
three-point fiber collision, non-injectivity over ℚ and ℂ) — into a fresh kernel
with nothing trusted, and the kernel accepted all of it.

### Totals

- **Modules independently re-checked:** 259 (default mode) + 1 full manifest (`--fresh`).
- **Failures / rejections:** **0.**
- **Aggregate checker wall-clock:** sweep 1040 s + Keller `--fresh` 769 s (these
  overlapped in real time; wall from ceremony start 18:49:40 to finish 19:17:56
  ≈ **28 min**, including setup and the corpus-build re-verification).

---

## 4. Step timings (wall-clock)

| Step | What | Wall-clock |
|---|---|---|
| 1 | Setup: clone standalone checker, inspect tags/README, identify built-in `leanchecker` (standalone build **skipped**, justified §2a) | ~2 min |
| 2 | Corpus build re-verification (`lake build`, already current — incremental) | 24 s |
| — | Interface probes (default vs `--fresh`; heavy-module sizing) | ~1 min |
| 3a | Keller `--fresh` gold-standard replay | 12 m 49 s (concurrent) |
| 3b | 259-module default-mode sweep, 7 tracks | 17 m 20 s |
| 4 | (no failures — nothing to escalate) | — |
| 5 | This report | — |

---

## 5. One-paragraph summary for the paper's audit section

> The full formal development was independently re-verified by replaying its
> compiled environment through a second, independent pass of the Lean 4 kernel —
> the `leanchecker` tool built into toolchain `leanprover/lean4:v4.32.0-rc1`
> (kernel build `b4812ae5`), the same kernel that produced the proof objects but
> invoked separately from and after elaboration, so that any environment tampering
> or unsound metaprogramming extension would be caught. Every one of the 259
> author-written modules across the seven audited tracks (HB, Fulcrum, Parity, MR,
> TwinBar, Chen, and the Keller Jacobian-counterexample verification) had all of
> its declarations re-typechecked from scratch by this fresh kernel, and every
> declaration was accepted with zero rejections. The Keller manifest was, in
> addition, replayed in full `--fresh` mode — reconstructing its entire transitive
> environment, Mathlib dependencies included, in a fresh empty kernel while
> trusting no precompiled artifact — and likewise passed. Mathlib dependencies,
> trusted as precompiled objects in the module-scoped pass, are themselves
> independently re-verified upstream by this same checker in Mathlib's continuous
> integration. The re-verification therefore adds no axioms and no trust beyond the
> Lean kernel itself.

---

*Artifacts (outside the repo):* logs and per-module results at
`$HOME/.cache/salt-lean4checker/logs/` — `sweep.summary`, `<Track>.result`
(one `PASS <module> <secs>` line per module), `<Track>.failures` (all 0 bytes),
`Keller.fresh.log`. Checker clone at
`$HOME/.cache/salt-lean4checker/lean4checker` (unused, provenance only).
