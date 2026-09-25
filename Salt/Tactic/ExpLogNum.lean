/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Tactic.AuditAxioms

/-!
# `ExpLogNum` — numeral bounds on `exp`/`log` at integer exponent (ledger T3, first cut, rung (a))

The O15 census of 2026-09-24 (h2c; seat record `3f2fab874`) counted the corpus's repeated proof
shapes over 72 ladder/door/supply modules (1,090 tactic-mode proofs, 35,945 proof lines).  The one
multi-line shape a tactic can collapse is the NUMERIC TRANSCENDENTAL FACT — `c ≤ exp n`,
`exp n ≤ c`, `log d ≤ k` — re-proved by the same six-to-nine-line dance at 581 sites (1,316 lines,
283 of them multi-line): `(1096 : ℝ) ≤ Real.exp 7` at four sites, `(19 : ℝ) ≤ Real.exp 6` at
three, `(10 : ℝ) ^ 8 ≤ Real.exp 518` at nine.  Its integer-exponent core is 111 sites, 379 lines.

This module is rung (a) of the schema ladder (`docs/blueprints/tactics.md`): seven LEMMAS and
no metaprogramming, turning every such site into one line — the four `exp` forms `c ≤ exp n`,
`c < exp n`, `exp n ≤ c`, `exp n < c` and the two `log` transposes `log d ≤ k`, `k ≤ log d`.
The landing of 2026-09-24 carried six; `lt_exp_nat_of_lt_pow` (the strict lower form) and the
red-first arms below were added the same day on the helm's order.  The route is the one every
landed site already walks by hand — `Real.exp n = (Real.exp 1) ^ n`, the decimal bounds
`Real.exp_one_gt_d9` and `Real.exp_one_lt_d9` raised to `n` by `pow_le_pow_left₀`, one
`norm_num` — packaged once.

## Coverage, DECLARED (the incompleteness doctrine: fail cleanly, never half-transform)

* the exponent `n` (or the `log` bound `k`) is a natural numeral; the lemmas are stated at
  `Real.exp ((n : ℕ) : ℝ)` and `exact_mod_cast` bridges that to a site's `Real.exp 7`;
* the hypothesis is a rational inequality `norm_num` closes; for `n > 256` the site must raise
  `exponentiation.threshold` (the modules carrying `10^8 ≤ exp 518` already set 4000 file-wide);
* a bound tighter than an integer on the `log` side (`2.0794 ≤ Real.log 8`) is OUTSIDE this rung —
  it needs the `Real.log_two_gt_d9` route, a later cut;
* rung (c) — an `elab` that reads `n` off the goal so a site is the bare word `explog_num` — is not
  landed here; rung (a) already pays the whole line saving.

## Usage

```
have hexp15 : Real.exp 15 ≤ 4000000 := by
  exact_mod_cast Salt.Tactic.exp_nat_le_of_pow_le 15 (c := 4000000) (by norm_num)
have he7 : (1096 : ℝ) ≤ Real.exp 7 := by
  exact_mod_cast Salt.Tactic.le_exp_nat_of_le_pow 7 (by norm_num)
```

First consumer: `Salt.MR.s13_smallGradeFits_h_L` (`Salt/MR/StrideDoorAllGrades.lean`), its two
eight-line blocks (`exp 15 ≤ 4000000`, `exp 2 ≤ 15`) rewritten with the statement token-identical:
lines 175 → 162, heartbeats 90,294 → 85,228 (re-taken at the landing), the kernel receipt unchanged.
-/

namespace Salt.Tactic

/-- `Real.exp n = (Real.exp 1) ^ n` for a natural `n` — the rewrite every site does first. -/
theorem exp_nat_eq_pow (n : ℕ) : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
  rw [← Real.exp_nat_mul, mul_one]

/-- `c ≤ exp n` from `c ≤ 2.7182818283 ^ n` (the d9 lower bound of `e`, `Real.exp_one_gt_d9`). -/
theorem le_exp_nat_of_le_pow (n : ℕ) {c : ℝ} (h : c ≤ (2.7182818283 : ℝ) ^ n) :
    c ≤ Real.exp (n : ℝ) := by
  rw [exp_nat_eq_pow]
  exact le_trans h (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n)

/-- `c < exp n` from `c < 2.7182818283 ^ n` (the d9 lower bound of `e`). -/
theorem lt_exp_nat_of_lt_pow (n : ℕ) {c : ℝ} (h : c < (2.7182818283 : ℝ) ^ n) :
    c < Real.exp (n : ℝ) :=
  lt_of_lt_of_le h (le_exp_nat_of_le_pow n le_rfl)

/-- `exp n ≤ c` from `2.7182818286 ^ n ≤ c` (the d9 upper bound of `e`, `Real.exp_one_lt_d9`). -/
theorem exp_nat_le_of_pow_le (n : ℕ) {c : ℝ} (h : (2.7182818286 : ℝ) ^ n ≤ c) :
    Real.exp (n : ℝ) ≤ c := by
  rw [exp_nat_eq_pow]
  exact le_trans (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n) h

/-- `exp n < c` from `2.7182818286 ^ n < c`. -/
theorem exp_nat_lt_of_pow_lt (n : ℕ) {c : ℝ} (h : (2.7182818286 : ℝ) ^ n < c) :
    Real.exp (n : ℝ) < c :=
  lt_of_le_of_lt (exp_nat_le_of_pow_le n le_rfl) h

/-- `log d ≤ k` from `d ≤ 2.7182818283 ^ k` and `0 < d`, at an integer `k`. -/
theorem log_le_nat_of_le_pow (k : ℕ) {d : ℝ} (hd : 0 < d) (h : d ≤ (2.7182818283 : ℝ) ^ k) :
    Real.log d ≤ (k : ℝ) :=
  (Real.log_le_iff_le_exp hd).mpr (le_exp_nat_of_le_pow k h)

/-- `k ≤ log d` from `2.7182818286 ^ k ≤ d` and `0 < d`, at an integer `k`. -/
theorem nat_le_log_of_pow_le (k : ℕ) {d : ℝ} (hd : 0 < d) (h : (2.7182818286 : ℝ) ^ k ≤ d) :
    (k : ℝ) ≤ Real.log d :=
  (Real.le_log_iff_exp_le hd).mpr (exp_nat_le_of_pow_le k h)

end Salt.Tactic

/-! ## Self-tests — the census's own sites, one line each; `#audit_axioms` dogfoods T5

Red-first, one arm per FORM (`c ≤ exp n` · `c < exp n` · `exp n ≤ c` · `exp n < c` · `log d ≤ k` ·
`k ≤ log d`), the numeral EDGES (`n = 0`, `n = 1`, a `^`-numeral side, `n = 518` above the
default `exponentiation.threshold`), and three REFUSALS the incompleteness doctrine promises (a
false numeral at the `e ^ 7` edge · a non-integer exponent · a decimal `log` bound outside this
rung). Each refusal is a `fail_if_success` around a TACTIC-level use of the lemma — never a
nested `by`, which logs its failure and recovers so the enclosing `have` succeeds and the arm
never fires; the numeral side is a NAMED hole closed by `case num => norm_num`, because the
tactic `have` rotates its continuation goal to the front and a focused bullet would close
`True` instead. So each arm turns RED the day the rung starts closing a goal it declares outside
its coverage; the mutant drive that reddened these arms is in the arms PR's receipts. -/

section Tests
open Salt.Tactic

example : (1096 : ℝ) ≤ Real.exp 7 := by exact_mod_cast le_exp_nat_of_le_pow 7 (by norm_num)
example : (19 : ℝ) ≤ Real.exp 6 := by exact_mod_cast le_exp_nat_of_le_pow 6 (by norm_num)
example : Real.exp 14 < 1202605 := by exact_mod_cast exp_nat_lt_of_pow_lt 14 (by norm_num)
example : Real.exp 15 ≤ 4000000 := by
  exact_mod_cast exp_nat_le_of_pow_le 15 (c := 4000000) (by norm_num)
example : Real.exp 2 ≤ 15 := by exact_mod_cast exp_nat_le_of_pow_le 2 (c := 15) (by norm_num)
example : Real.exp 40 ≤ 3 ^ (40 : ℕ) := by
  have := exp_nat_le_of_pow_le 40 (c := (3 : ℝ) ^ (40 : ℕ)) (by norm_num)
  simpa using this
example : Real.log 1096 ≤ 7 := by
  exact_mod_cast log_le_nat_of_le_pow 7 (by norm_num) (by norm_num)

-- the fourth `exp` form, `c < exp n` (no lemma at the landing), at the `e ^ 7 = 1096.63…` edge
example : (1096 : ℝ) < Real.exp 7 := by exact_mod_cast lt_exp_nat_of_lt_pow 7 (by norm_num)
-- `k ≤ log d` (`nat_le_log_of_pow_le` had no selftest at the landing): `e ^ 2 = 7.389… ≤ 8`
example : (2 : ℝ) ≤ Real.log 8 := by
  exact_mod_cast nat_le_log_of_pow_le 2 (by norm_num) (by norm_num)
-- edges: `n = 0` and `n = 1` (the census's `exp 1 ≤ 3`, seven sites)
example : (1 : ℝ) ≤ Real.exp 0 := by exact_mod_cast le_exp_nat_of_le_pow 0 (by norm_num)
example : Real.exp 1 ≤ 3 := by exact_mod_cast exp_nat_le_of_pow_le 1 (c := 3) (by norm_num)
-- edge: `n = 518` (the census's `10 ^ 8 ≤ exp 518`, nine sites) — above the default
-- `exponentiation.threshold` (256), so the site raises it, as the modules carrying it already do
set_option exponentiation.threshold 600 in
set_option maxHeartbeats 1000000 in
-- `norm_num` evaluates `2.7182818283 ^ 518` exactly (a 5,400-digit numerator): ~4× the default
example : (10 : ℝ) ^ 8 ≤ Real.exp 518 := by
  exact_mod_cast le_exp_nat_of_le_pow 518 (by norm_num)

-- REFUSAL 1 — a FALSE numeral one unit past the edge (`e ^ 7 = 1096.63…`): `1097 ≤ exp 7`
example : True := by
  fail_if_success
    have _h : (1097 : ℝ) ≤ Real.exp 7 := le_exp_nat_of_le_pow 7 ?num
    case num => norm_num
  trivial
-- REFUSAL 2 — a NON-INTEGER exponent: the lemmas are stated at `((n : ℕ) : ℝ)`; `1.5` is none
example : True := by
  fail_if_success
    -- refused at unification: `Real.exp ↑1` is not `Real.exp 1.5`
    have _h : (2 : ℝ) ≤ Real.exp 1.5 := le_exp_nat_of_le_pow 1 ?num
  trivial
-- REFUSAL 3 — a DECIMAL `log` bound (`2.0794 ≤ log 8` is the `log 2` route, a later rung)
example : True := by
  fail_if_success
    -- refused at unification: `(↑2 : ℝ)` is not `2.0794`
    have _h : (2.0794 : ℝ) ≤ Real.log 8 := nat_le_log_of_pow_le 2 ?pos ?num
  trivial

#audit_axioms Salt.Tactic.exp_nat_eq_pow Salt.Tactic.le_exp_nat_of_le_pow
  Salt.Tactic.lt_exp_nat_of_lt_pow
  Salt.Tactic.exp_nat_le_of_pow_le Salt.Tactic.exp_nat_lt_of_pow_lt
  Salt.Tactic.log_le_nat_of_le_pow Salt.Tactic.nat_le_log_of_pow_le

end Tests
