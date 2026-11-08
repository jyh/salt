/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S12Compose

/-!
# The regime scale reads (`RegimeScaleReads`)

Once a capstone consumer holds `hfl : loglogFloor50 ≤ R.Hlo` (from `regime_floors_of_U1`), it
reads the three scale facts of its regime in five lines: `50 ≤ loglog R.Hlo`,
`50 ≤ loglog R.Hhi` (through `R.hHlohi`), and the register hypothesis `hHreg` at every window
length `R.Hlo ≤ H ≤ R.Hhi`, each from `regime_Hfloor_of_loglogFloor50`. This module states those
reads once (the tactics catalogue's candidate #12, here at 38 sites in 22 Salt/MR files).
-/

namespace Salt.MR

open Salt.Entropy.Chowla

/-- The three scale reads of a regime past the `loglogFloor50` floor: `50 ≤ loglog R.Hlo`,
`50 ≤ loglog R.Hhi`, and `0 ≤ log H ∧ 50 ≤ loglog H` at every `R.Hlo ≤ H ≤ R.Hhi`, each by
`regime_Hfloor_of_loglogFloor50` (at `R.Hlo`, at `R.Hhi` through `R.hHlohi`, and at `H`). -/
theorem regime_scale_reads (R : ChowlaRegime) (hfl : loglogFloor50 ≤ R.Hlo) :
    50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ∧ 50 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ∧
      ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
        0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
  ⟨(regime_Hfloor_of_loglogFloor50 hfl).2,
    (regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)).2,
    fun _ hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)⟩

/-- The scale reads with the regime's tower read attached, in its `exp (· / 2)` shape:
the three reads of `regime_scale_reads`, then `loglog R.Hhi ≤ exp (loglog R.Hlo / 2)` from the
regime's tower hypothesis `hRtow` at the first read. -/
theorem regime_scale_reads_tow_exp (R : ChowlaRegime) (hfl : loglogFloor50 ≤ R.Hlo)
    (hRtow : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) →
      Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2)) :
    50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ∧ 50 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ∧
      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
        0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) ∧
      Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) :=
  let h := regime_scale_reads R hfl
  ⟨h.1, h.2.1, h.2.2, hRtow h.1⟩

/-- The scale reads with the regime's tower read attached, in its `(·) ^ (9/2)` shape:
the three reads of `regime_scale_reads`, then `loglog R.Hhi ≤ (loglog R.Hlo) ^ (9/2)` from the
regime's tower hypothesis `hRtow` at the first read. -/
theorem regime_scale_reads_tow_pow (R : ChowlaRegime) (hfl : loglogFloor50 ≤ R.Hlo)
    (hRtow : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) →
      Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        ≤ (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) ^ ((9 : ℝ) / 2)) :
    50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ∧ 50 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ∧
      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
        0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) ∧
      Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        ≤ (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) ^ ((9 : ℝ) / 2) :=
  let h := regime_scale_reads R hfl
  ⟨h.1, h.2.1, h.2.2, hRtow h.1⟩

end Salt.MR
