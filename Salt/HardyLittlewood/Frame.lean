/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Brun.M5BigO
import Salt.TwinBar.TwinDoor

/-!
# The Hardy–Littlewood twin frame

Three cheap deliverables that assemble the landed foundations into the standard
Hardy–Littlewood packaging for twin primes.

* **HL-1** names the twin constant `Pi2 = ∏_{p>2} (1 − (p−1)⁻²)` and the singular
  series `𝔖 = 2·Pi2`, and states the open Hardy–Littlewood twin conjecture
  `HardyLittlewoodTwin` as an `Asymptotics.IsEquivalent` (a *statement* definition
  — no proof; it is the conjecture).  `pi2_multipliable` re-exports the honest
  convergence datum so the frame self-documents that `Pi2` is a real product.
* **HL-2** is the constant theory: `Pi2 ∈ (0, 1)` and `𝔖 ∈ (0, 2)`.
* **HL-3a** wraps the landed Selberg upper bound `Salt.M5BigO.nat_absorb` into an
  order-sharp `twinPrimeCounting N ≤ C·N/(log N)²` with `C = 25700`.

## On the constant in HL-3a

The Hardy–Littlewood conjecture predicts the sharp constant `𝔖 = 2·Pi2 ≈ 1.32`.
The landed Selberg sieve delivers the correct *order* with the explicit — but far
from sharp — constant `C = 25700`.  Closing the gap to `(4 + ε)·2·Pi2` (the sharp
order-of-magnitude upper bound, Selberg's `4·𝔖` in the twin setting) is the
registered **HL-3b** arc, which is gated on Mertens' third theorem
`∏_{p ≤ x} (1 − 1/p) ∼ e^{−γ}/log x`; it is *not* attempted here.
-/

open Filter Asymptotics

namespace Salt.HardyLittlewood

/-! ## HL-1 — the frame -/

/-- **The Hardy–Littlewood twin constant** `Π₂ = ∏_{p>2} (1 − 1/(p−1)²)`, the
convergent Euler product landed as `Salt.TwinBar.twinC2`. -/
noncomputable def Pi2 : ℝ := Salt.TwinBar.twinC2

/-- **The twin singular series** `𝔖 = 2·Π₂` — the constant `(1.2)` of
Hardy–Littlewood (1923) / Heath-Brown (1983). -/
noncomputable def twinSingularSeries : ℝ := 2 * Pi2

/-- **The Hardy–Littlewood twin conjecture** (a *statement* definition — the open
conjecture, so no proof is offered): the twin-prime counting function is
asymptotically equivalent to `𝔖 · x / (log x)²`. -/
def HardyLittlewoodTwin : Prop :=
  Asymptotics.IsEquivalent Filter.atTop
    (fun x : ℝ => (twinPrimeCounting ⌊x⌋₊ : ℝ))
    (fun x : ℝ => twinSingularSeries * x / (Real.log x) ^ 2)

/-- The factor family of `Π₂` is genuinely `Multipliable`, so `Pi2` is an honest
convergent product, not a junk default.  (Re-export of `twinC2_multipliable`.) -/
theorem pi2_multipliable :
    Multipliable (fun p : Salt.TwinBar.PrimesGt2 => 1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹) :=
  Salt.TwinBar.twinC2_multipliable

/-! ## HL-2 — constant theory -/

/-- **`0 < Π₂`.**  (Re-export of `twinC2_pos`.) -/
theorem pi2_pos : 0 < Pi2 := Salt.TwinBar.twinC2_pos

/-- **`Π₂ < 1`.**  `twinC2 = exp(∑' log factor)` with every log factor `≤ 0`
(factors lie in `(0, 1]`) and at least one strictly negative (`p = 3` gives factor
`3/4`, `log(3/4) < 0`); hence the exponent is `< 0` and `twinC2 < exp 0 = 1`. -/
theorem pi2_lt_one : Pi2 < 1 := by
  -- `f p = log(factor p)`; `twinC2 = exp(∑' f)`.  Show `∑' f < 0`.
  set f : Salt.TwinBar.PrimesGt2 → ℝ :=
    fun p => Real.log (1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹) with hf
  have hf_summable : Summable f := Salt.TwinBar.twinC2_log_summable
  -- every log factor is `≤ 0` (factors lie in `(0, 1]`).
  have hf_nonpos : ∀ j, f j ≤ 0 := by
    intro j
    have hle1 : (1 - ((((j : ℕ) : ℝ) - 1) ^ 2)⁻¹) ≤ 1 := by
      have : (0 : ℝ) ≤ ((((j : ℕ) : ℝ) - 1) ^ 2)⁻¹ := by positivity
      linarith
    exact Real.log_nonpos (le_of_lt (Salt.TwinBar.twinC2_factor_pos j)) hle1
  -- a witness prime `p = 3` with strictly negative log factor `log(3/4)`.
  obtain ⟨p3, hp3val⟩ : ∃ p : Salt.TwinBar.PrimesGt2, ((p : ℕ) : ℝ) = 3 :=
    ⟨⟨3, by norm_num, by norm_num⟩, by norm_num⟩
  have hp3neg : f p3 < 0 := by
    simp only [hf, hp3val]
    apply Real.log_neg <;> norm_num
  -- `∑' f ≤ f p3 < 0` via `le_tsum` on `-f`.
  have hle := hf_summable.neg.le_tsum p3 (fun j _ => neg_nonneg.mpr (hf_nonpos j))
  rw [tsum_neg] at hle
  have hs_le : ∑' p, f p ≤ f p3 := by linarith
  have hs_neg : ∑' p, f p < 0 := lt_of_le_of_lt hs_le hp3neg
  -- conclude `Pi2 = twinC2 = exp(∑' f) < exp 0 = 1`.
  have hexp : Salt.TwinBar.twinC2 = Real.exp (∑' p, f p) := by
    rw [Salt.TwinBar.twinC2]
    exact (Real.rexp_tsum_eq_tprod Salt.TwinBar.twinC2_factor_pos hf_summable).symm
  unfold Pi2
  rw [hexp]
  have h1 := Real.exp_lt_exp.mpr hs_neg
  rwa [Real.exp_zero] at h1

/-- **`0 < 𝔖`.** -/
theorem twinSingularSeries_pos : 0 < twinSingularSeries := by
  unfold twinSingularSeries; linarith [pi2_pos]

/-- **`𝔖 < 2`.** -/
theorem twinSingularSeries_lt_two : twinSingularSeries < 2 := by
  unfold twinSingularSeries; linarith [pi2_lt_one]

/-! ## HL-3a — the order-sharp upper bound (wrapper) -/

/-- **Order-sharp upper bound.**  There is a constant `C > 0` (here `C = 25700`)
with `twinPrimeCounting N ≤ C·N/(log N)²` for all large `N` — the landed Selberg
sieve `Salt.M5BigO.nat_absorb`, packaged as an eventual bound.  The sharp constant
`𝔖 = 2·Π₂ ≈ 1.32` is the Hardy–Littlewood prediction; the sharp `(4+ε)·𝔖`
order bound is the registered HL-3b arc gated on Mertens' third theorem. -/
theorem twinCounting_upper_order :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (twinPrimeCounting N : ℝ) ≤ C * (N : ℝ) / (Real.log N) ^ 2 := by
  obtain ⟨N1, hN1⟩ := Salt.M5BigO.nat_absorb
  refine ⟨25700, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop N1] with N hN
  exact hN1 N hN

end Salt.HardyLittlewood
