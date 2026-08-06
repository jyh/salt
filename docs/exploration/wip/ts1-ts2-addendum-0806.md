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

## ⚠️ AMENDMENT 5 — S1's THREADING MAKES `hc_t1` **UNUSED**, WHICH THE EXIT TEST WILL CATCH

Pre-derived by reading; **not yet confirmed by a build** — treat the warning claim as a prediction
with a recommended handling, not as a measurement.

The two consumer sites are **byte-identical** 5-line blocks (`R8:1422-1428`, `Tall:1727-1733`):

```lean
have hsplit := tbal_tau_le_split hQ1 hw0
rw [← hL₂def] at hsplit
have hbase_nn : (0 : ℝ) ≤ Q ^ (-(680 * w)) / L₂ ^ (14 : ℝ) := by positivity
have hτle : c * Q ^ (-(680 * w)) / L₂ ^ (14 : ℝ)
    ≤ 2 ^ (-(250 : ℝ)) * Q ^ (-(680 * w)) / L₂ ^ (14 : ℝ) := by
  rw [mul_div_assoc, mul_div_assoc]; exact mul_le_mul_of_nonneg_right hc_t1 hbase_nn
linarith only [hτle, hsplit, htriv]
```

`hbase_nn` + `hτle` exist **only** to bridge from the `2^{−250}`-specific lemma to the actual `c`,
using `hc_t1`. The generalised lemma delivers the bound **at `c` directly**, so the whole block
collapses to:

```lean
have hsplit := tbal_tau_le_split hQ1 hw0 hcpos.le hc1
rw [← hL₂def] at hsplit
linarith only [hsplit, htriv]
```

`hcpos : 0 < c` and `hc1 : c ≤ 1` are **already in scope** at both sites (`R8:1383`, `Tall:1684`) —
S1 needs no new hypothesis. That is −4 lines per tower, and it is the whole S1 threading.

⛔ **The consequence:** `hc_t1` is consumed at **exactly one place in each tower** — this block
(verified: `grep -nF hc_t1` gives declaration, this site, the min projection, and the pass-through,
and nothing else). After S1 it is **unused**, and `lakefile.toml` runs
`weak.linter.mathlibStandardSet`. **Expect an unused-variable warning, which fails exit test #1
("no new warnings").**

**Recommended handling — keep the churn at zero:**
1. **Keep the head arm** in both mins, renumbered `2^(-(250:ℝ))` → `1/40`. The arm's *numeral* is
   what delivers `173.29 → 3.69`; that is independent of whether the *hypothesis* is consumed.
   Keeping the arm keeps **every projection index below it unchanged** (the brief's core ruling —
   deleting a min head would shift `hc_t2` two deep through `hc_t10` nine deep, ~123 lines).
2. **Rename the binder** `hc_t1` → `_hc_t1` at `R8:1383` and `Tall:1684` only. The local
   `have hc_t1` (`R8:1796`, `Tall:2124`) stays as-is — it is still used, passed positionally at
   `R8:1847` / `Tall:2179`.
   *This file already uses that idiom* — `(_hCρnn : 0 ≤ Cρ)` at `Tall:1578` — so it is the
   codebase's own convention, not an invention.
3. `hp1` becomes `by norm_num` at `R8:1780` / `Tall:2109`, per the brief.

If the build turns out **not** to warn, drop step 2 and say so in flags — do not add an underscore
the compiler did not ask for.

## 📊 AMENDMENT 6 — THE ARM TABLE, RECOMPUTED INDEPENDENTLY: TWO "AFTER" CELLS ARE STALE

Recomputed from scratch (`log`, exact rationals) rather than copied. **The brief's landed column
reproduces exactly at every entry** — `log(1/c₀) = 11.7507`, `86.23`, `83.71`, `536.67`, `631.58` —
so both the brief's arithmetic and the arm model below are confirmed. **The headline claim is
correct and now independently verified end-to-end: MAX `631.58 → 86.23`, binding arm
`(c₀/32)^{17/3}`, unchanged by this amendment.**

Two "after TS-1+TS-2" cells were computed **without TS-1's own stones applied**:

| arm | landed | brief's "after" | **corrected "after"** | why |
|---|---|---|---|---|
| `(1/KEβ)^8` → γ_Eβ | 536.67 ✓ | 32.15 | **28.15** | brief used `627^9`; S5(a) makes it `248^9` |
| `(c₀/KEρ)^8` → γ_Eρ | 631.58 ✓ | 25.58 | **22.84** | brief used `627^9`,`636`; S5(a)+S6 give `248^9`,`570` |

`32.15` is *exactly* the value at `627^9`, and `25.58` is *exactly* the value at `627^9`/`636` —
so both cells are the pre-TS-1 numbers sitting in a post-TS-1 column. The Eρ cell at least carried
a parenthetical "(less, w/ S5+S6)"; the Eβ cell carries no caveat and is simply stale.

**Nothing downstream moves** — both stay far below the binding `86.23`, which is exactly the brief's
own point that S5 and S6 "deliver 0.00 to this program's grade." Recorded so the executor's reported
table can be *checked* rather than accepted, and so nobody later quotes `32.15` as a measured
post-wave figure.

Formulas, for re-derivation: with `γ₀` the row's floor, the arm becomes `(1/(8K))^{1/γ₀}` and
`log(1/arm) = (1/γ₀)·log(8K)`. Tall numerals: `KEβ = 16·(328+48·5)·248⁹`, `KEρ = 16·570·248⁹`,
`c₀ = 1/126848`. **This is a TALL-tower table only** — R8's KEβ/KEρ arms carry a free `Z₀`
(`R8:1387-1388`) and cannot be priced numerically at all, which is the brief's own warning that the
table "does not price that tower".

## 🚦 AMENDMENT 7 — RULING: **TS-1 DOES NOT ATTEMPT S5(b) TONIGHT** (execution call, overrulable)

The brief calls S5(b) (the δ re-tune `1/100 → ≈1/50`, `248 → ≈137`) **"GUARDED, and it is
optional"**, with a stop-rule to abandon it if it costs >~40 lines or breaks any window check.
**This seat rules that it is not started at all tonight.** Three grounds, the third being new:

1. **It delivers 0.00 to this program's grade, now quantified.** Amendment 6 puts the two arms it
   shrinks at `28.15` (Eβ) and `22.84` (Eρ) *after* S5(a)+S6 — already far below the binding
   `86.23`. S5(b) makes small numbers smaller. The brief says this itself; Amendment 6 measures it.
2. **Its blast radius is the widest of any stone here.** It changes the `u`-exponent `−9/100` at
   *every* consumer of `logz_factor_pow9_le` — every γ-floor and every window `nlinarith`.
3. ⛔ **NEW, and it is the decisive one: S5(b) COUPLES THE TWO WAVES.** Every exact rational in
   Amendment 1 (`5247/1700`, `3547/1700`) is derived at the `−9/100` exponent. If TS-1 lands S5(b),
   **all four of TS-2's floors must be re-derived** (`5247/1700 − 9/100`, `3547/1700 − 9/100`) before
   a single numeral is written — and the mutation check's inadmissible value moves with them.
   Two waves that are otherwise **independent** become order-dependent, on the night, for **0.00**.

**Therefore:** TS-1 lands S1 + S5(a) + S6 and stops. **If** it finishes early, the tree is green and
committed, and there is appetite, S5(b) may be attempted **strictly last and in a SEPARATE commit** —
in which case **TS-2 must re-derive its floors and must not use Amendment 1's numerals as written.**
The TS-2 prompt already instructs the executor to read the TS-1 flags entry to find out which
happened rather than assume; that instruction becomes load-bearing if this option is exercised.

*This is an execution call about an explicitly-optional item, not a statement change — the maestro
or the Captain can overrule it at dispatch time and the wave still runs.*

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
