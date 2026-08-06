# TS-1 / TS-2 PRE-DERIVATION ADDENDUM — Mac Mini relight, 2026-08-06 ~15:55 PDT

Written by the MATHEMATICS seat during the pre-gate window (gate = 20:00 PDT). Everything here
was derived by **reading only** — no Lean was invoked, the standing order was not broken.

**Precedence:** this addendum AMENDS `docs/exploration/tau-sharp-ts1-ts2-briefs-0806.md` on the
four points below. Where they differ, this file is correct — each item is verified against the
bytes at the cited line, and the verification command is given so the next reader can re-run it.

---

## ⛔ AMENDMENT 1 — THE γ-COLLAPSE CENSUS IS **FOUR** SITES, NOT THREE

The brief's §"USE EXACT RATIONALS" table names three collapse steps. **There are four.**
`TBalR8:939-940` is **TBalR8's own Eρ row** — the forked twin of `TBalTall:1644-1645` — and it is
absent from the brief entirely.

```
grep -n "rpow_le_rpow_of_exponent_ge" Salt/SW/TBalR8.lean Salt/SW/TBalTall.lean
```

| # | row | `hcγ` site | `hg` hypothesis | discharge site | exponent in code | γ(σ) | **floor** |
|---|---|---|---|---|---|---|---|
| 1 | A | `R8:542-543` | `R8:454` | `R8:1674`, `Tall:1987` | `49/50 − 14(β₀−σ)` | — | `133/850` |
| 2 | Eβ | `R8:816-817` | `R8:746` | `R8:1683`, `Tall:1996` | `−1 −3 −9/100 −14(1/2−σ)` | `14σ − 1109/100` | `3547/1700` |
| 3 | **Eρ (R8)** | **`R8:939-940`** | **`R8:872`** | **`R8:1693`** | `−3 −9/100 −14(1/2−σ)` | `14σ − 1009/100` | **`5247/1700`** |
| 4 | Eρ (Tall) | `Tall:1644-1645` | `Tall:1578` | `Tall:2006` | `−3 −9/100 −14(1/2−σ)` | `14σ − 1009/100` | `5247/1700` |

Rows 3 and 4 carry the **identical exponent** and therefore the **identical floor** `5247/1700`;
they differ only in the constant (`(564 + 72·Z₀)` in R8, `636`→`570` in Tall). `hσlo` is in scope
at all four (each side goal already reads `by nlinarith [hσlo]`), so the brief's "no uniformity
trap" ruling extends to the fourth site unchanged.

**Consequence for TS-2's scope:** the edit surface is ~double the brief's estimate —
**4 `hcγ` side goals + 4 `hg` statements + 6 discharge sites (3 per tower) + 2 arm definitions.**
The two Eρ arms are `hc_t7` in *both* mins (`R8:1387` free-`Z₀`, `Tall:2097-2098` numeral).
An executor that edits three sites will leave `R8:940` at `1/8` and the R8 Eρ arm unmoved —
a silent half-landing that still builds green.

### The arithmetic, re-derived independently (the brief's numbers are CORRECT)
γ_Eρ: `−3 − 9/100 − 14(1/2−σ) = 14σ − 1009/100`. At `σ = 16/17`:
`14·16/17 = 22400/1700`, `1009/100 = 17153/1700`, difference **`5247/1700 = 3.086470588…`**.
The freeze's `3.0865` exceeds it by `2.941e−5` ⇒ **false at the endpoint**. ✓
γ_Eβ: `14σ − 1109/100` ⇒ `3547/1700 = 2.086470588…`; freeze's `2.0865` false by the same margin. ✓
A-row: `133/850 = 0.156470588…`; freeze's `0.15647` is **true** (margin `5.88e−7`) — the one
admissible freeze numeral, and therefore **not** a mutation candidate. ✓

---

## ✅ AMENDMENT 2 — S6's OPEN QUESTION IS ANSWERED: **R8 DOES NOT OVER-COUNT. NO CHANGE.**

The brief asked the executor to determine whether `TBalR8` has a `C2Rho_le` that also over-counts,
and to *say so explicitly* if not. **It does not, and here is the proof — the executor should
spend zero attempts on it.**

- `TBalR8:1292` states `C2Rho q Z₀ ρ ≤ (564 + 72·Z₀)·(Q^{1/2}·L₂²)·(1/c₀)`, and its own
  `hfold2` (`R8:1349`) proves `150 + 414·M + 72·M·Z₀ ≤ (564 + 72·Z₀)·B`.
  **`150 + 414 = 564` exactly**, and the `Z₀` term is exactly `72·Z₀`. The coefficient *is* the
  fold total. **Tight by construction — there is no slack to retire.**
- The tall slack exists for a different reason: `C2Rho_le_tall`'s four folds total
  `102 + 108 + 162 + 198 = 570` (the `108` is `54·(M·Q)·Z₀` absorbed through `Z₀ ≤ 2Q`), but the
  landed *statement* said `636` — which is `564 + 72·Z₀` evaluated at `Z₀ ⇝ 1`, i.e. the tall
  statement **inherited R8's coefficient shape instead of using its own fold total.**

So S6 is a tall-only stone by its nature, not by oversight. Record this in flags and move on.

---

## ✅ AMENDMENT 3 — THE BANKED PATCH IS BROADER THAN THE BRIEF SAYS: S5(a) IS **BOTH TOWERS**

The brief describes the patch as S5(a) propagated "through `C2Rho_le_tall → row_Eρ_cap_tall → KEρ`",
which reads as tall-only. **It is not.** The patch's R8 hunks (`@@ -697` `logz_factor_le`,
`@@ -743`/`@@ -804` `row_Eβ_cap`, `@@ -869`/`@@ -904` `row_Eρ_cap`) carry `627 → 248` through
**TBalR8 as well**. `627` survives nowhere in either tower after the patch.

**Do not re-do R8's S5(a).** Apply the patch and check, don't re-derive.

**Measured** (patch applied to a scratch copy, then reverted — see the caution below):
pre-patch `grep -cF 627` is **41 lines in R8, 26 in Tall** (43 / 28 occurrences). The patch removes
`627` from **67** lines and adds it back on exactly **one** — the S5(a) provenance docstring.
Post-patch the correct census is therefore:

```
grep -cF "627" Salt/SW/TBalR8.lean     # expect 1  <- docstring at :705 only, INTENTIONAL
grep -cF "627" Salt/SW/TBalTall.lean   # expect 0
```

A surviving `627` anywhere else is a missed propagation site.

⚠️ **Caution learned the hard way (this seat, 15:49):** do **not** answer a read-only question by
applying the patch to the live tree. `/Users/jyh/projects/claude/salt` is shared and a full
`lake build` may be in flight; a 40-second window of foreign edits in another seat's tree is a
cross-seat incident waiting to happen. Use `git apply --check` / `--numstat`, read the patch, or
apply in a throwaway `git worktree`. (This seat did apply-and-revert, verified byte-identity, and
confirmed the concurrent build had cleared both SW modules ten minutes earlier — no harm done, but
it was luck, not design.)

---

## ⭐ AMENDMENT 4 — THE MUTATION CHECK NEEDS A VALIDITY RULE (this seat's own ruling, refined)

The standing instruction reads *"a mutated build that PASSES = stop and flag."* **That is correct
for the γ_Eρ mutation and wrong for the S1 mutation**, and shipping it unqualified would manufacture
a false campaign halt. The distinction:

> **A mutation is a valid positive control only if it makes the mutated goal FALSE — not merely
> unreachable by one route.** Removing one sufficient route from an over-determined hypothesis set
> is a coverage probe, not a control.

**γ_Eρ `5247/1700 → 3.0865` — VALID CONTROL.** The side goal becomes `3.0865 ≤ 14σ − 1009/100`
with only `hσlo : 16/17 ≤ σ` available. The RHS's infimum over the admissible σ is exactly
`3.086470588…`, so the goal is **arithmetically false at the closed endpoint**. No tactic can close
it from a consistent hypothesis set, and there is no alternative route because the *goal itself* is
false. **MUST fail. If it passes ⇒ STOP AND FLAG** — the arm table is not measuring what it claims.

**S1 `1/40 → (>1)` — NOT a valid control by itself.** It removes `hc_t1` as a route to
`hc : c ≤ 1`, but `c` is a `min` that still contains the `1/2` arm (and `1/18`, `1/576`, …), so
`c ≤ 1` **remains true and provable another way**. Whether the build breaks depends only on whether
the proof text happens to route through `hc_t1`. **A pass here proves nothing about vacuity.**
If it passes: determine *which* hypothesis discharged `hc1`, record that, and **do not halt** —
report it as a routing fact, not a defect.

⛔ **And the literal `1/40 → 1` is a no-op mutation: `c ≤ 1` is satisfied at equality, so it
should pass trivially and tests nothing.** Use a value **strictly greater than 1** (e.g. `2`).

### The third guard — a green mutated build must be a build that actually happened
Before recording *any* mutation outcome, confirm the build **re-elaborated the mutated file**
(the output must show the module compiling). A green from a cached/no-op build is the exact shape
of the silicon seat's 14:04 finding — `#audit_axioms` printed `✓ [0 axioms]` for two theorems that
had never elaborated. **A pass from a build that did no work is not evidence of anything.**

---

## PRE-FLIGHT ALREADY COMPLETED (do not repeat)

| check | result |
|---|---|
| `git pull --ff-only` | already up to date |
| `Salt/SW/{TBalR8,TBalTall,All}.lean` clean in the shared tree | ✓ (untouched since `5939730`) |
| `git apply --check ~/.claude/salt-ts1-wip/ts1-partial.patch` | **CLEAN** |
| `git apply --check docs/exploration/wip/ts1-partial-0806.patch` | **CLEAN** |
| home copy ≡ repo copy (patch and scratch) | **byte-identical** |
| `saltbuild.sh` present, executable, `lake` answers | ✓ Lake 5.0.0 / Lean 4.32.0-rc1 |
| Mini hardware | Mac16,11 · **64 GB** · 14 cores (10 perf) — same envelope as the laptop |

## ⚠️ STANDING RISK, UNCHANGED AND CAPTAIN-RATIFIED
`saltbuild.sh:27` is `lake build "$@"` with **no `-M`**. The cap applies only to the `*.lean`
audit branch. **This wave runs with no memory bound**, on the two files the standing order called
the 8+GB elaborations. Verified again on the Mini at 15:47: live `lean` children of a `lake build`
at 2.33 GB with no `-M` anywhere in argv. The lakefile fix is the maestro/Captain's open item and
was deliberately **not** rushed in before tonight. Mitigation is procedural: targeted builds, one
at a time, `TBalR8` **before** `TBalTall` (dependency chain via `Salt.SW.TauExt`), lock announced.

## 🔧 INSTRUMENT NOTE FOR EVERY SEAT — `grep` AND `^` IN LEAN SOURCE
`grep -n "c ^ (1 / 8" Salt/SW/TBal*.lean` returns **nothing**. `grep -nF` on the same pattern
returns **28 matches**. BSD `grep` treats `^` mid-pattern as an anchor, so any unescaped `^`
silently yields *zero matches instead of an error*. In a Lean codebase — where `^` is in nearly
every expression — **an empty grep is not evidence of absence.** Use `grep -F`, or escape `\^`.
This nearly cost this seat the Amendment-1 finding.
