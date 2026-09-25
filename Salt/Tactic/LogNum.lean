/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Tactic.AuditAxioms

/-!
# `LogNum` — base-2 decimal bounds on `log` and the power identity (ledger T3, cut 2, rung (a))

Nothing here bears on twin primes: this is proof-engineering debt, a toolkit module.

The O15 pull-3 census of 2026-09-25 (math; seat record `ac00ad4a9`) counted the corpus's
`Real.log`-at-a-numeral shapes: the identity `log 4 = 2 * log 2` (and its `log 8`, `log 16`,
`log 9` siblings) and the decimal bounds `(1.3862 : ℝ) ≤ Real.log 4`, `(2.0794 : ℝ) ≤ Real.log 8`,
each re-proved by the same three-to-four-line dance — `rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
Real.log_pow]; push_cast; ring`, then `linarith [Real.log_two_gt_d9]` — at ~190 sites (183–197 by
needle variant; the count is spelling-sensitive).

This module complements `Salt.Tactic.ExpLogNum` (T3 first cut), whose REFUSAL 3 names
`2.0794 ≤ log 8` as "the `log 2` route, a later cut": this is that cut.  Five LEMMAS and no
metaprogramming — the identity `log_eq_nat_mul_log` and the four base-2 decimal forms
`c ≤ log d`, `c < log d`, `log d ≤ c`, `log d < c` at `d = 2 ^ k` — turning each such site into
one line.  The route is the one every landed site already walks by hand: `Real.log_pow`, then
mathlib's d9 decimals `Real.log_two_gt_d9` (`0.6931471803 < log 2`) and `Real.log_two_lt_d9`
(`log 2 < 0.6931471808`) scaled by `k`, one `norm_num`.

## Coverage, DECLARED (the incompleteness doctrine: fail cleanly, never half-transform)

IN: base-2 decimal bounds, and the identity `log (b ^ k) = k * log b` for any real `b` and
natural `k` (so `log 9 = 2 * log 3` and base-3/base-10 identities are IN; only their DECIMAL
bounds are OUT).  The d9 constants give ~5·10⁻¹⁰·k of slack; a bound tighter than that is
refused (REFUSAL 1 is one unit past the edge at four decimals).

OUT:
* decimal bounds at a base other than 2 (`log 3`, `log 10`: 7 census sites, R4);
* a rational argument (`log (7/6)`);
* a `k` that is not a numeral where `norm_num` must prove `hd`;
* `hd` for an EXPANDED numeral `d = 2 ^ k` with `k > 256` unless the site raises
  `exponentiation.threshold` (a symbolic `2 ^ k` closes at any `k`; driven at `2 ^ 300`);
* the R3 identity shapes no lemma here reaches — sums (`log 6 = log 2 + log 3`), reciprocals
  (`log (1/3) = −log 3`, `log (1/2^344)`), numeral subtraction (`log ((4:ℝ)−1)`), ratios —
  **61 of the census's 209 R3 sites**.

Embedded `rw [...] at h` sites convert as `rw [log_eq_nat_mul_log b k (by norm_num)] at h`, with a
smaller saving than span − 1.

## Measured price (pricing scratch, run 2, `Elab.async false`)

Named landed proof `Salt.MR.chowlaRegimeFlat_exists_param_head_xceil_mul_at_L`
(`StrideDoorAllGrades.lean:618–737`), verbatim copy vs the two blocks replaced: **lines 120 → 114;
heartbeats 79,094 → 72,746 (−8.0 %)**, both copies at three axioms.  Corpus: **≈254 lines, an
UPPER BOUND** (in-coverage R3 148 sites / 176 saved + R2 36 / 114, less 36 counted twice through
nesting).  The candidate stays a CANDIDATE until a landed proof converts; that is the debt lane's
work, and no landed file moves here.

## Usage

```
have hlog4 : (1.3862 : ℝ) ≤ Real.log 4 :=
  Salt.Tactic.LogNum.le_log_two_pow 2 (by norm_num) (by norm_num)
have h : Real.log 8 = 3 * Real.log 2 := by
  exact_mod_cast Salt.Tactic.LogNum.log_eq_nat_mul_log 2 3 (by norm_num)
```
-/

namespace Salt.Tactic.LogNum

/-- `log d = k · log b` for a numeral power `d = b ^ k` — the rewrite every site does first. -/
theorem log_eq_nat_mul_log (b : ℝ) (k : ℕ) {d : ℝ} (h : d = b ^ k) :
    Real.log d = k * Real.log b := by
  rw [h, Real.log_pow]

/-- `c ≤ log d` for `d = 2 ^ k`, from `c ≤ k · 0.6931471803` (the d9 lower bound of `log 2`,
`Real.log_two_gt_d9`). -/
theorem le_log_two_pow (k : ℕ) {c d : ℝ} (hd : d = 2 ^ k) (h : c ≤ k * 0.6931471803) :
    c ≤ Real.log d := by
  rw [log_eq_nat_mul_log 2 k hd]
  exact le_trans h (mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg k))

/-- `c < log d` for `d = 2 ^ k`, from `c < k · 0.6931471803`. -/
theorem lt_log_two_pow (k : ℕ) {c d : ℝ} (hd : d = 2 ^ k) (h : c < k * 0.6931471803) :
    c < Real.log d :=
  lt_of_lt_of_le h (le_log_two_pow k hd le_rfl)

/-- `log d ≤ c` for `d = 2 ^ k`, from `k · 0.6931471808 ≤ c` (the d9 upper bound of `log 2`,
`Real.log_two_lt_d9`). -/
theorem log_two_pow_le (k : ℕ) {c d : ℝ} (hd : d = 2 ^ k) (h : k * 0.6931471808 ≤ c) :
    Real.log d ≤ c := by
  rw [log_eq_nat_mul_log 2 k hd]
  exact le_trans (mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg k)) h

/-- `log d < c` for `d = 2 ^ k`, from `k · 0.6931471808 < c`. -/
theorem log_two_pow_lt (k : ℕ) {c d : ℝ} (hd : d = 2 ^ k) (h : k * 0.6931471808 < c) :
    Real.log d < c :=
  lt_of_le_of_lt (log_two_pow_le k hd le_rfl) h

end Salt.Tactic.LogNum

/-! ## Self-tests — the census's own site forms, one line each; `#audit_axioms` dogfoods T5

Ten site forms read off the census's top types (the identity at `log 4` in both spellings,
`log 8`, `log 16`, the base-3 `log 9`; the four decimal forms, including `1/2 ≤ log 2` at `k = 1`),
then two REFUSALS the incompleteness doctrine promises (a false bound one unit past the d9 edge ·
a non-power argument), each with a POSITIVE TWIN of the identical arm shape on a true goal, which
must close.  Each refusal is a `fail_if_success` around a TACTIC-level use of the lemma — never a
nested `by`, which logs its failure and recovers so the enclosing `have` succeeds and the arm
never fires; the hypotheses are NAMED holes closed by `case … => norm_num`.  In REFUSAL 2 the
`num` case comes before the `pw` case, so that on the refused goal no tactic is left unreachable
(the other order raised `this tactic is never executed`) while a true-goal mutant still closes
both holes. -/

section Tests
open Salt.Tactic.LogNum

example : Real.log 4 = 2 * Real.log 2 := by exact_mod_cast log_eq_nat_mul_log 2 2 (by norm_num)
example : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  exact_mod_cast log_eq_nat_mul_log 2 2 (by norm_num)
example : Real.log 8 = 3 * Real.log 2 := by exact_mod_cast log_eq_nat_mul_log 2 3 (by norm_num)
example : Real.log 16 = 4 * Real.log 2 := by exact_mod_cast log_eq_nat_mul_log 2 4 (by norm_num)
example : Real.log 9 = 2 * Real.log 3 := by exact_mod_cast log_eq_nat_mul_log 3 2 (by norm_num)
example : (1.3862 : ℝ) ≤ Real.log 4 := le_log_two_pow 2 (by norm_num) (by norm_num)
example : (2.0794 : ℝ) ≤ Real.log 8 := le_log_two_pow 3 (by norm_num) (by norm_num)
example : Real.log 4 < 1.3863 := log_two_pow_lt 2 (by norm_num) (by norm_num)
example : (1 : ℝ) / 2 ≤ Real.log 2 := le_log_two_pow 1 (by norm_num) (by norm_num)
example : Real.log 512 ≤ 6.2384 := log_two_pow_le 9 (by norm_num) (by norm_num)

-- REFUSAL 1 — a FALSE bound one unit past the d9 edge: `2 * 0.6931471803 = 1.3862943606 < 1.3863`
example : True := by
  fail_if_success
    have _h : (1.3863 : ℝ) ≤ Real.log 4 := le_log_two_pow 2 ?pw ?num
    case pw => norm_num
    case num => norm_num
  trivial
-- its positive twin: the identical arm shape on the true `1.3862` closes
example : (1.3862 : ℝ) ≤ Real.log 4 := by
  have _h : (1.3862 : ℝ) ≤ Real.log 4 := le_log_two_pow 2 ?pw ?num
  case pw => norm_num
  case num => norm_num
  exact _h
-- REFUSAL 2 — a NON-POWER argument: `6 = 2 ^ 2` is false, refused at `hd`
example : True := by
  fail_if_success
    have _h : (1 : ℝ) ≤ Real.log 6 := le_log_two_pow 2 ?pw ?num
    case num => norm_num
    case pw => norm_num
  trivial
-- its positive twin: the identical arm shape on the power `4 = 2 ^ 2` closes
example : (1 : ℝ) ≤ Real.log 4 := by
  have _h : (1 : ℝ) ≤ Real.log 4 := le_log_two_pow 2 ?pw ?num
  case num => norm_num
  case pw => norm_num
  exact _h

#audit_axioms Salt.Tactic.LogNum.log_eq_nat_mul_log Salt.Tactic.LogNum.le_log_two_pow
  Salt.Tactic.LogNum.lt_log_two_pow
  Salt.Tactic.LogNum.log_two_pow_le Salt.Tactic.LogNum.log_two_pow_lt

end Tests
