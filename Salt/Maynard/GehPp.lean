/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehBridge
import Salt.BV.AbelCore

/-!
# The prime-power (pp-in-AP) level `PpLevel` — root-counting floor (node G-PpLevel)

`Salt/Maynard/GehBridge.lean` carries the prime-power correction sum as the named
hypothesis `PpLevel θ` (θ = 3999/4000): the summed sequence discrepancy of the
`ppTerm` weight (`Λ(n)/log n − 1_{n prime}`, supported on proper prime powers
`p^k`, `k ≥ 2`, value `1/k`) over the haircut modulus range is `≤ C x/(log x)^A`.

## Status: FLOOR only.  The sharp discharge needs root-counting mod composite `q`.

The honest per-`q` decomposition is
`seqDiscrepancy ppTerm x q ≤ (max residue-class pp-mass) + (coprime pp-mean)`.
The recon target `∑_{q≤Q} … ≪ √x·log²x + x^θ·log x ≪ x/(log x)^A` is reached only
through the per-class count
`#{p ≤ √x : p² ≡ a (mod q)} ≤ 2^{ω(q)+1}·(√x/φ(q) + 1)`, i.e. the number of square
roots of `a` modulo the COMPOSITE modulus `q` is `≤ 2^{ω(q)+1}`.  The two sharp
pieces then read off as
* mean part `∑_{q≤Q} pp-mass/φ(q) ≪ (√x·log x)·∑_{q≤Q} 1/φ(q) ≪ √x·log²x`;
* residue part `∑_{q≤Q} 2^{ω(q)}·(√x/q + 1) ≪ √x·∑ 2^{ω(q)}/q + ∑ 2^{ω(q)}
  ≪ √x·log²x + x^θ·log x`.

### The obstruction ledger (why this is a floor, not the discharge)

1. **Root-counting mod composite `q` (the load-bearing gap).**  Mathlib provides
   the square-root count only for a PRIME modulus `p ≠ 2` (`ZMod.card_sqrts`,
   `Mathlib/NumberTheory/LegendreSymbol/Basic.lean`), and `Polynomial.card_roots`
   only over a FIELD.  The bound `≤ 2^{ω(q)+1}` for composite `q` needs a CRT
   assembly `ZMod q ≃ ∏ ZMod p^{e_p}` combined with the per-prime-power counts
   (`≤ 2` for odd `p`, `≤ 4` mod `2^e`) — a fresh multi-hundred-line development.
2. **The arithmetic sums are absent.**  `∑_{q≤Q} 2^{ω(q)}/q ≪ log²Q`,
   `∑_{q≤Q} 2^{ω(q)} ≪ Q·log Q`, and `∑_{q≤Q} 1/φ(q) ≪ log Q` are not in mathlib
   nor in `Salt/`.  The nearest codebase tool `Salt.BV.sum_omega_mul_le` is the
   wrong shape (`∑ ω(q)/φ(q)`, additive `ω`, not `2^{ω}`).
3. **The crude route provably explodes.**  `seqDiscrepancy_ppTerm_le` bounds each
   `q` uniformly by `2√x·log x/log 2`; `sum_seqDiscrepancy_ppTerm_le_crude` sums
   it to `≤ Q·(2√x·log x/log 2) ≈ x^{θ+1/2}`.  As `θ + 1/2 = 3999/4000 + 1/2 > 1`,
   NO choice of haircut `B` makes this `≤ C x/(log x)^A`; the per-class count is
   unavoidable.  (The same crude route DOES yield `PpLevel θ` for any `θ < 1/2`,
   but that θ is not the one the GEH door consumes.)

What is discharged below, sorry-free, is the crude uniform building block that a
full proof still consumes for its mean part and its small-`x` corner.
-/

open Finset ArithmeticFunction

/-- The `ppTerm` mass on `[1,x]` equals the `Ioc` mass (`ppTerm 1 = 0`), hence is
`≤ √x·log x/log 2` by `Salt.BV.sum_ppTerm_le`.  Stated with `|·|` (harmless, as
`ppTerm ≥ 0`) to feed the `ℓ¹`-mass slot of `seqDiscrepancy_le_two_mul_sum_abs`. -/
lemma sum_abs_ppTerm_le (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, |Salt.BV.ppTerm n|
      ≤ Real.sqrt x * Real.log x / Real.log 2 := by
  have habs : ∀ n, |Salt.BV.ppTerm n| = Salt.BV.ppTerm n :=
    fun n => abs_of_nonneg (Salt.BV.ppTerm_nonneg n)
  simp only [habs]
  have hpp1 : Salt.BV.ppTerm 1 = 0 := by
    unfold Salt.BV.ppTerm
    simp [ArithmeticFunction.vonMangoldt_apply_one, Nat.not_prime_one]
  have hIcc : ∑ n ∈ Finset.Icc 1 x, Salt.BV.ppTerm n
      = ∑ n ∈ Finset.Ioc 1 x, Salt.BV.ppTerm n := by
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx; simp
    · have hins : Finset.Icc 1 x = insert 1 (Finset.Ioc 1 x) := by
        ext n; rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ioc]; omega
      have hnot : (1 : ℕ) ∉ Finset.Ioc 1 x := by rw [Finset.mem_Ioc]; omega
      rw [hins, Finset.sum_insert hnot, hpp1, zero_add]
  rw [hIcc]
  exact Salt.BV.sum_ppTerm_le x

/-- **Crude uniform per-`q` bound for `ppTerm`.**  For every modulus `q`, the
sequence discrepancy of the prime-power correction is `≤ 2·√x·log x/log 2`,
UNIFORMLY in `q`.  Immediate from the universal `ℓ¹` bound
`seqDiscrepancy_le_two_mul_sum_abs` and the `ppTerm` mass bound.  This is the
building block a full `PpLevel` discharge consumes for its mean part and its
small-`x` corner; on its own it is too weak once summed (see
`sum_seqDiscrepancy_ppTerm_le_crude`). -/
theorem seqDiscrepancy_ppTerm_le (x q : ℕ) :
    seqDiscrepancy (fun n => Salt.BV.ppTerm n) x q
      ≤ 2 * (Real.sqrt x * Real.log x / Real.log 2) := by
  refine (seqDiscrepancy_le_two_mul_sum_abs (fun n => Salt.BV.ppTerm n) x q).trans ?_
  exact mul_le_mul_of_nonneg_left (sum_abs_ppTerm_le x) (by norm_num)

/-- **The crude route's freight, made explicit.**  Summing the uniform per-`q`
bound over `q ∈ [1,Q]` gives `≤ Q·(2√x·log x/log 2)`.  With the haircut
`Q ≈ x^θ/(log x)^B` this is `≈ x^{θ+1/2}` freight; since `θ + 1/2 = 3999/4000 +
1/2 > 1`, the crude route CANNOT reach `PpLevel (3999/4000)` — the sharp route's
per-class root-count (the mathlib gap in the module docstring) is unavoidable. -/
theorem sum_seqDiscrepancy_ppTerm_le_crude (x Q : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, seqDiscrepancy (fun n => Salt.BV.ppTerm n) x q
      ≤ (Q : ℝ) * (2 * (Real.sqrt x * Real.log x / Real.log 2)) := by
  have hconst : ∑ _q ∈ Finset.Icc 1 Q, (2 * (Real.sqrt x * Real.log x / Real.log 2))
      = (Q : ℝ) * (2 * (Real.sqrt x * Real.log x / Real.log 2)) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  exact (Finset.sum_le_sum (fun q _ => seqDiscrepancy_ppTerm_le x q)).trans (le_of_eq hconst)
