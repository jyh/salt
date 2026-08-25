/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MRTPortRowLam
import Salt.MR.MRTPortTrivialSplit

/-!
# `MRTPortExitLam` — D8 INTO D9 (node E2)

The one live composition on the δ₀-split road under the ruling that the major arc is
out of scope: `MRTPortRowLam.m4_doorSq_of_rowMeanSqLam` (the sieve-free row descent,
which lands on the SQUARED door integral) chained into
`MRTPortTrivialSplit.m4_exit_socket_split_sq_trivial` (which consumes a squared door
bound at a fixed constant grade `c` and returns `¬ logChowla2Fails`).

The two binders agree token-for-token left of `≤`; the only work is the arithmetic on
the right, isolated below as `exit_lam_tail_absorb`:

* the row grade: `6 * MS H ≤ c` gives `3 * MS H * H² ≤ (c/2) * H²`;
* the additive ladder tail: `8 * 2^k ≤ c * x * Z * H₋` with `H₋ ≤ H` gives
  `4 * 2^k * H / x / Z ≤ (c/2) * H²`.

⚠️ SCOPE.  The `α` binder CANCELS here — `m4_doorSq_of_rowMeanSqLam` forwards exactly the
`NearRatTight` premise the socket consumes — so this composition is arc-free WORK.  Its
remaining input `M4RowMeanSqLam R k MS` is NOT arc-free MATHEMATICS: it is the unsieved
row mean square at every tight-major `α`, i.e. GAP α in the row's currency (class D).
The conclusion is also delivered at an `∃ R`-chosen regime — unboundedly many scales,
NOT all large scales.  Nothing here closes either gap.

This module is not yet rooted in any aggregate — it must be built targeted.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **The tail absorption, stated abstractly.**  The whole arithmetic content of the
D8 → D9 composition: the row grade `6 * MSH ≤ c` pays for the leading term and the
`H`-uniform ladder tail pays for the additive one, each against half of `c * Hr²`. -/
theorem exit_lam_tail_absorb {c MSH Hr Hlor xr Z tk : ℝ}
    (hc : 0 < c) (hx : 0 < xr) (hZ : 0 < Z) (hH : 0 < Hr)
    (hlo : Hlor ≤ Hr) (hprice : 6 * MSH ≤ c)
    (htail : 8 * tk ≤ c * xr * Z * Hlor) :
    3 * (MSH * Hr ^ 2) + 4 * tk * Hr / xr / Z ≤ c * Hr ^ 2 := by
  have hxZ : (0 : ℝ) < xr * Z := mul_pos hx hZ
  have hA : 3 * (MSH * Hr ^ 2) ≤ c / 2 * Hr ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c - 6 * MSH) (sq_nonneg Hr)]
  have hB : 4 * tk * Hr / xr / Z ≤ c / 2 * Hr ^ 2 := by
    rw [div_div, div_le_iff₀ hxZ]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c * xr * Z * Hlor - 8 * tk) hH.le,
      mul_nonneg (by linarith : (0 : ℝ) ≤ Hr - Hlor)
        (by positivity : (0 : ℝ) ≤ c * (xr * Z) * Hr)]
  linarith

/-- **THE ROW CHAIN.**  `m4_doorSq_of_rowMeanSqLam` (D8) composed into
`m4_exit_socket_split_sq_trivial` (D9): the sieve-free row mean-square input, plus the
three ladder gates, the row pricing line `6 * MS H ≤ c` and the `H`-uniform ladder tail,
give `¬ logChowla2Fails` at the socket's own regime. -/
theorem m4_exit_lam_of_rowMeanSqLam :
    ∃ (ε : ℚ) (c : ℝ), 0 < ε ∧ 0 < c ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          (∀ (k : ℕ) (MS : ℕ → ℝ),
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → doorLadder R.x H k ≤ R.x / R.ω) →
            2 ^ (k + 1) ≤ R.x →
            ((k : ℝ) ≤ 3 * ∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 6 * MS H ≤ c) →
            (8 * 2 ^ k
              ≤ c * (R.x : ℝ) * (∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹)
                  * (R.Hlo : ℝ)) →
            M4RowMeanSqLam R k MS →
              ¬ logChowla2Fails R.eps R.x R.ω)
:= by
  obtain ⟨ε, c, hε, hc, hsock⟩ := m4_exit_socket_split_sq_trivial
  refine ⟨ε, c, hε, hc, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hRU1, hRg, hRtow, hR⟩ := hsock U1floor g
  refine ⟨R, hReps, hRU1, hRg, hRtow, ?_⟩
  intro k MS hreach hpow hk3 hprice htail hrow
  refine hR ?_
  intro H hH hlo hhi α harc
  haveI : NeZero H := hH
  have hH0 : 0 < H := by
    have := R.hHlo_floor
    omega
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have hx0 : (0 : ℝ) < (R.x : ℝ) := by
    have := R.hx
    have : 0 < R.x := by omega
    exact_mod_cast this
  have hZ0 : (0 : ℝ) < ∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹ :=
    door_norm_pos R.hx R.hω
  have hHloR : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo
  refine le_trans (m4_doorSq_of_rowMeanSqLam hreach hpow hk3 hrow H hlo hhi α harc) ?_
  exact exit_lam_tail_absorb hc hx0 hZ0 hHR hHloR (hprice H hlo hhi) htail

end Salt.MR

end
