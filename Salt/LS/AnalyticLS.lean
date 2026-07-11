/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.Deriv
import Salt.LS.Spacing
import Salt.LS.Gallagher

/-!
# Large sieve track, node L3.1: the analytic large sieve

Blueprint: `docs/blueprints/largesieve.md`.

**L3.1** (`analytic_LS`, FROZEN): for a `δ`-spaced system `α : Fin R → ℝ` with
`0 < δ ≤ 1/2`,
`∑ r, ‖expSum N a (α r)‖² ≤ (δ⁻¹ + 13·N) · ∑_{n<N} ‖aₙ‖²`.

Assembly (all inputs are landed W1/W2 nodes):
* `gallagher_pointwise` (L4.1) at `f := expSum N a` for each `r`, using
  `contDiff_expSum` (L2.1);
* sum over `r` and push the two integral families through
  `sum_integral_le_period` (L5) — both `‖expSum·‖²` and `‖expSum·‖·‖deriv·‖`
  are 1-periodic (from `expSum_add_one`), nonnegative, continuous;
* `parseval` (L1.2) evaluates `∫₀¹ ‖expSum‖² = P`;
* the cross term is closed with an **elementary Young inequality**
  `2xy ≤ 5N·x² + y²/(5N)` (integrated form `10N·∫xy ≤ 25N²·∫x² + ∫y²`), the
  derivative Parseval bound `∫₀¹ ‖deriv‖² ≤ (2πN)²P` (L2.2), and `π² ≤ 10`
  (`Real.pi_lt_d2`), giving `2·∫₀¹ ‖expSum‖·‖deriv‖ ≤ 13N·P` (`25 + 4π² ≤ 65`).
No Cauchy–Schwarz/`rpow` needed; the frozen constant `13 ≥ 4π` absorbs the slack.
-/

namespace Salt.LS

open scoped BigOperators
open MeasureTheory intervalIntegral Complex

/-- `e(n) = 1` for a natural number `n`. -/
lemma e_natCast (n : ℕ) : e (n : ℝ) = 1 := by
  have h : e ((n : ℝ)) = Complex.exp (((n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    unfold e; push_cast; ring_nf
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- `expSum N a` is 1-periodic. -/
lemma expSum_add_one (N : ℕ) (a : ℕ → ℂ) (α : ℝ) :
    expSum N a (α + 1) = expSum N a α := by
  unfold expSum
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [show (n : ℝ) * (α + 1) = (n : ℝ) * α + (n : ℝ) from by ring, e_add, e_natCast, mul_one]

/-- `deriv (expSum N a)` is 1-periodic. -/
lemma deriv_expSum_add_one (N : ℕ) (a : ℕ → ℂ) (α : ℝ) :
    deriv (expSum N a) (α + 1) = deriv (expSum N a) α := by
  rw [deriv_expSum, deriv_expSum]
  exact expSum_add_one N (twist a) α

/-- **L3.1 — analytic large sieve (FROZEN).** -/
theorem analytic_LS {R N : ℕ} {δ : ℝ} {α : Fin R → ℝ} (a : ℕ → ℂ)
    (hsp : Spaced δ α) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∑ r, ‖expSum N a (α r)‖ ^ 2 ≤ (δ⁻¹ + 13 * N) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [expSum]
  -- N ≥ 1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set P : ℝ := ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 with hP
  have hP_nonneg : 0 ≤ P := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  set S : ℝ → ℂ := expSum N a with hS
  have hcontS : Continuous S := continuous_expSum N a
  have hcontDS : Continuous (deriv S) := continuous_deriv_expSum N a
  have hC1 : ContDiff ℝ 1 S := contDiff_expSum N a
  -- periodicity / nonnegativity / continuity of the two integrand families
  have hg1_per : ∀ x, ‖S (x + 1)‖ ^ 2 = ‖S x‖ ^ 2 := by
    intro x; simp only [hS, expSum_add_one]
  have hg1_nonneg : ∀ x, 0 ≤ ‖S x‖ ^ 2 := fun x => sq_nonneg _
  have hg1_cont : Continuous (fun t => ‖S t‖ ^ 2) := hcontS.norm.pow 2
  have hg2_per : ∀ x, ‖S (x + 1)‖ * ‖deriv S (x + 1)‖ = ‖S x‖ * ‖deriv S x‖ := by
    intro x; simp only [hS]; rw [expSum_add_one, deriv_expSum_add_one]
  have hg2_nonneg : ∀ x, 0 ≤ ‖S x‖ * ‖deriv S x‖ := fun x => by positivity
  have hg2_cont : Continuous (fun t => ‖S t‖ * ‖deriv S t‖) := hcontS.norm.mul hcontDS.norm
  -- Gallagher, summed
  have hgall : ∀ r, ‖S (α r)‖ ^ 2 ≤
      δ⁻¹ * (∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ ^ 2)
        + 2 * ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ * ‖deriv S t‖ :=
    fun r => gallagher_pointwise hC1 hδ (α r)
  -- periodic unfolding (L5), twice
  have hper1 : (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ ^ 2)
      ≤ ∫ t in (0:ℝ)..1, ‖S t‖ ^ 2 :=
    sum_integral_le_period (fun t => ‖S t‖ ^ 2) hg1_per hg1_nonneg hg1_cont hsp hδ hδ2
  set G : ℝ := ∫ t in (0:ℝ)..1, ‖S t‖ * ‖deriv S t‖ with hG
  have hper2 : (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ * ‖deriv S t‖) ≤ G :=
    sum_integral_le_period (fun t => ‖S t‖ * ‖deriv S t‖) hg2_per hg2_nonneg hg2_cont hsp hδ hδ2
  -- Parseval and derivative Parseval
  have hparse : (∫ t in (0:ℝ)..1, ‖S t‖ ^ 2) = P := by rw [hS, hP]; exact parseval N a
  have hL22 : (∫ t in (0:ℝ)..1, ‖deriv S t‖ ^ 2) ≤ (2 * Real.pi * N) ^ 2 * P := by
    rw [hS, hP]; exact integral_norm_deriv_sq_le N a
  -- Young inequality, integrated
  have hcont_x2 : Continuous (fun t => ‖S t‖ ^ 2) := hg1_cont
  have hcont_y2 : Continuous (fun t => ‖deriv S t‖ ^ 2) := hcontDS.norm.pow 2
  have hint_lhs : IntervalIntegrable (fun t => 10 * (N : ℝ) * (‖S t‖ * ‖deriv S t‖)) volume 0 1 :=
    (continuous_const.mul hg2_cont).intervalIntegrable 0 1
  have hint_x2 : IntervalIntegrable (fun t => 25 * (N : ℝ) ^ 2 * ‖S t‖ ^ 2) volume 0 1 :=
    (continuous_const.mul hcont_x2).intervalIntegrable 0 1
  have hint_y2 : IntervalIntegrable (fun t => ‖deriv S t‖ ^ 2) volume 0 1 :=
    hcont_y2.intervalIntegrable 0 1
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
      10 * (N : ℝ) * (‖S t‖ * ‖deriv S t‖) ≤ 25 * (N : ℝ) ^ 2 * ‖S t‖ ^ 2 + ‖deriv S t‖ ^ 2 := by
    intro t _
    nlinarith [sq_nonneg (5 * (N : ℝ) * ‖S t‖ - ‖deriv S t‖), norm_nonneg (S t),
      norm_nonneg (deriv S t), hNpos.le]
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hint_lhs
    (hint_x2.add hint_y2) hpt
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hint_x2 hint_y2,
    intervalIntegral.integral_const_mul, ← hG] at hmono
  -- hmono : 10*N*G ≤ 25*N²*(∫‖S‖²) + ∫‖deriv S‖²
  have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hyoung : 10 * (N : ℝ) * G ≤ 65 * (N : ℝ) ^ 2 * P := by
    have hNP : (0 : ℝ) ≤ (N : ℝ) ^ 2 * P := mul_nonneg (sq_nonneg _) hP_nonneg
    have hkey : (0 : ℝ) ≤ ((N : ℝ) ^ 2 * P) * (10 - Real.pi ^ 2) :=
      mul_nonneg hNP (by linarith [hpi])
    have hb : 25 * (N : ℝ) ^ 2 * (∫ t in (0:ℝ)..1, ‖S t‖ ^ 2)
        + (∫ t in (0:ℝ)..1, ‖deriv S t‖ ^ 2) ≤ 65 * (N : ℝ) ^ 2 * P := by
      rw [hparse]
      nlinarith [hL22, hkey]
    linarith [hmono, hb]
  have h5N : (0 : ℝ) < 5 * (N : ℝ) := by linarith
  have hfin : 2 * G ≤ 13 * (N : ℝ) * P := by nlinarith [hyoung, h5N]
  -- combine
  have hδinv : (0 : ℝ) ≤ δ⁻¹ := by positivity
  have hA : δ⁻¹ * (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ ^ 2) ≤ δ⁻¹ * P := by
    apply mul_le_mul_of_nonneg_left _ hδinv
    calc (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ ^ 2)
        ≤ ∫ t in (0:ℝ)..1, ‖S t‖ ^ 2 := hper1
      _ = P := hparse
  have hB : 2 * (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ * ‖deriv S t‖)
      ≤ 13 * (N : ℝ) * P := by
    have : 2 * (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ * ‖deriv S t‖) ≤ 2 * G :=
      mul_le_mul_of_nonneg_left hper2 (by norm_num)
    linarith [this, hfin]
  calc ∑ r, ‖S (α r)‖ ^ 2
      ≤ δ⁻¹ * (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ ^ 2)
          + 2 * (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ * ‖deriv S t‖) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum (fun r _ => hgall r)
    _ ≤ δ⁻¹ * P + 13 * (N : ℝ) * P := by linarith [hA, hB]
    _ = (δ⁻¹ + 13 * N) * P := by ring

end Salt.LS
