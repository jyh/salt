/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.EulerEff
import Salt.Mertens.Third

/-!
# T-BAL R5 — the ζ-side effective Mertens reciprocal (`H_lower`, stone 2 of 4)

The one bankable, unconditionally-true link of R5's `H_lower`: the effective LOWER bound for the
ζ-side factor `∏_{p≤z}(1−1/p)⁻¹` of the smooth product `P(z)` (`selHFull_eq_zeta_mul_L`). It is the
reciprocal of the corpus `Salt.Mertens.mertens_third` (`|∏_{p≤n}(1−1/p)·log n − e^{−γ}| ≤ C/log n`),
re-indexed to `(primorial z).primeFactors` via `primorial_primeFactors`. This supplies the
`e^γ·log z` growth (hence the `1/u` pole at the deep scale `z = e^{1/u}`) that the freeze's R5
target `H(z) ≥ (1−…)·L₁/(u(2−β₀))` needs on the ζ-side.

The OTHER three R5 stones (the L-side effective link, the δ_b Rankin cap, and the final assembly) do
NOT land — see the R5-FINISH flag (`docs/blueprints/flags.md`) for the two hard obstructions:
the L-side needs prime character sums (the strip tool bridges all-integer, not prime, partial sums),
and the δ_b `≤ 300 z^{−0.4}` cap is numerically FALSE for the landed primorial-Rankin machinery
(the fixed-α tail explodes). R5's honest closure requires an effective Selberg-mean constant, not
the framed decaying δ_b. This file banks only the TRUE stone.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no `sorry`.
-/

open Finset

noncomputable section

namespace Salt.SW

variable {q : ℕ}

/-- The ζ-side reciprocal product is the inverse of the Mertens product over the primes `≤ z`
(the `mertens_third` index). Product of inverses `=` inverse of the product. -/
lemma zeta_side_prod_eq (z : ℕ) :
    (∏ p ∈ (primorial z).primeFactors, (1 - 1 / (p : ℝ))⁻¹)
      = (∏ p ∈ (Finset.range (z + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))⁻¹ := by
  rw [primorial_primeFactors, ← Finset.prod_inv_distrib]

/-- The Mertens product `∏_{p≤z}(1−1/p)` is positive (each factor `∈ [1/2, 1)`). -/
lemma mertens_prod_pos (z : ℕ) :
    0 < ∏ p ∈ (Finset.range (z + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  refine Finset.prod_pos fun p hp => ?_
  have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
  have : (1 : ℝ) / p ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); exact_mod_cast hp2
  linarith

/-- **Stone 2 — the ζ-side effective lower bound.** For `z ≥ 3`,
`e^γ·log z·(1 − C/log z) ≤ ∏_{p≤z}(1−1/p)⁻¹`, with `C` the corpus `mertens_third` constant scaled by
`e^γ`. The reciprocal of Mertens' third theorem, giving the `e^γ log z ~ 1/u` growth of the ζ-side
factor of the smooth product `P(z)`. -/
theorem zeta_side_ge :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℕ, 3 ≤ z →
      Real.exp Real.eulerMascheroniConstant * Real.log z
          * (1 - C / Real.log z)
        ≤ ∏ p ∈ (primorial z).primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
  obtain ⟨C₀, hC₀, hM⟩ := Salt.Mertens.mertens_third
  set γ := Real.eulerMascheroniConstant with hγ
  set eg := Real.exp γ with heg
  set e0 := Real.exp (-γ) with he0def
  have hegpos : 0 < eg := Real.exp_pos _
  have he0pos : 0 < e0 := Real.exp_pos _
  have hgg : eg * e0 = 1 := by rw [heg, he0def, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have he0inv : e0 = 1 / eg := (eq_div_iff (ne_of_gt hegpos)).mpr (by rw [mul_comm]; exact hgg)
  refine ⟨C₀ * eg, by positivity, fun z hz => ?_⟩
  have hzR : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  set Lz := Real.log z with hLzdef
  have hLz : 0 < Lz := Real.log_pos (by linarith)
  set P₀ := ∏ p ∈ (Finset.range (z + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) with hP₀def
  have hP₀ : 0 < P₀ := mertens_prod_pos z
  -- the upper half of mertens_third: `P₀·Lz ≤ e0 + C₀/Lz`
  have hupper : P₀ * Lz ≤ e0 + C₀ / Lz := by
    have h := (abs_le.mp (hM z hz)).2
    rw [hP₀def, hLzdef, he0def]; linarith
  -- `e0 + C₀/Lz > 0`
  have hD : 0 < e0 + C₀ / Lz := by positivity
  rw [zeta_side_prod_eq, ← hP₀def]
  have hLzne : Lz ≠ 0 := ne_of_gt hLz
  have hegne : eg ≠ 0 := ne_of_gt hegpos
  -- step 2: `Lz/(e0+C₀/Lz) ≤ P₀⁻¹`
  have step2 : Lz / (e0 + C₀ / Lz) ≤ P₀⁻¹ := by
    rw [div_le_iff₀ hD, inv_mul_eq_div, le_div_iff₀ hP₀, mul_comm]
    exact hupper
  -- step 1: the exact value `A·D = Lz − (eg·C₀)²/Lz`, hence `A·D ≤ Lz`, hence `A ≤ Lz/D`.
  refine le_trans ?_ step2
  rw [le_div_iff₀ hD]
  have hval : eg * Lz * (1 - C₀ * eg / Lz) * (e0 + C₀ / Lz)
      = Lz - (eg * C₀) ^ 2 / Lz := by
    rw [he0inv]; field_simp; ring
  rw [hval]
  have hnn : 0 ≤ (eg * C₀) ^ 2 / Lz := by positivity
  linarith

end Salt.SW

end
