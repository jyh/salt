import Mathlib

/-!
S1-BUDGET kernel probes.  Everything here is about the REDUCTION, not the endpoint.
-/

namespace S1Budget

open Real

/-- **P1 — THE CANCELLATION.**  The frozen ratio of `budget_facts` (iv) is, at its
literal `κ` and its literal `F = gcap + log 2`, completely `H`-free and `log H`-free:
both sides carry `H / log H`, and the only survivor is `1 / logloglog H`. -/
theorem P1_cancellation (Hr L L3 e : ℝ) (hH : 0 < Hr) (hL : 0 < L) (hL3 : 0 < L3)
    (he : 0 < e) :
    (Hr / (L * L3)) / (e ^ 6 * Hr / (18 * (2 * Real.log 4) * L))
      = 36 * Real.log 4 / (e ^ 6 * L3) := by
  have h4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  field_simp
  ring

/-- **P2 — THE DEMAND IS FORCED BY THE CONTRACT** (not by `budgetX`).
Conclusion (iv) of `budget_facts`, taken verbatim, at the literal `κ = H/(log H · lll H)`
and the literal `gcap`, ALREADY implies `logloglog H ≥ 576·log 4/(ε⁶β²)`.
So no re-derivation that keeps the five frozen conclusions can charge less. -/
theorem P2_demand_forced (Hr L L3 e b : ℝ) (hH : 0 < Hr) (hL : 0 < L) (hL3 : 0 < L3)
    (he : 0 < e) (hb : 0 < b)
    (hgpos : 0 < e ^ 6 * Hr / (18 * (2 * Real.log 4) * L) - Real.log 2)
    (hiv : (Hr / (L * L3) + Real.log 2)
        / (e ^ 6 * Hr / (18 * (2 * Real.log 4) * L) - Real.log 2) ≤ (b / 4) ^ 2) :
    576 * Real.log 4 / (e ^ 6 * b ^ 2) ≤ L3 := by
  have h4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set F : ℝ := e ^ 6 * Hr / (18 * (2 * Real.log 4) * L) with hF
  set κ : ℝ := Hr / (L * L3) with hκ
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hFpos : 0 < F := by linarith
  -- (iv) ⇒ κ + log 2 ≤ (b/4)^2 * (F - log 2) ≤ (b/4)^2 * F
  have h1 : κ + Real.log 2 ≤ (b / 4) ^ 2 * (F - Real.log 2) :=
    (div_le_iff₀ hgpos).mp hiv
  have h2 : κ ≤ (b / 4) ^ 2 * F := by nlinarith [sq_nonneg (b/4), hl2]
  -- unfold and clear denominators
  rw [hκ, hF] at h2
  have hkey : 576 * Real.log 4 ≤ e ^ 6 * b ^ 2 * L3 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < L * L3)] at h2
    -- h2 : Hr ≤ (b/4)^2 * (e^6*Hr/(36 log4 * L)) * (L*L3)
    have hLne : L ≠ 0 := hL.ne'
    have hexp : (b / 4) ^ 2 * (e ^ 6 * Hr / (18 * (2 * Real.log 4) * L)) * (L * L3)
        = Hr * (e ^ 6 * b ^ 2 * L3) / (576 * Real.log 4) := by
      field_simp; ring
    rw [hexp] at h2
    have h3 : Hr * (576 * Real.log 4) ≤ Hr * (e ^ 6 * b ^ 2 * L3) :=
      (le_div_iff₀ (by positivity : (0:ℝ) < 576 * Real.log 4)).mp h2
    nlinarith [h3, hH]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < e ^ 6 * b ^ 2)]
  linarith [hkey]

/-! ## P3 — the numerics of the forced demand -/

theorem log_four_gt : (1.386 : ℝ) < Real.log 4 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [h]; nlinarith [Real.log_two_gt_d9]

/-- **P3a — the absolute floor of the shape.**  Even at `ε = 1/2` (the largest
admissible ε) and `β = 1` (a *thousandfold* beyond any admissible door grade —
the true frame value is `β ≈ 6·10⁻⁶`), the forced demand is `logloglog H ≥ 51000`. -/
theorem P3a_floor_at_generous : (51000 : ℝ) ≤ 576 * Real.log 4 / ((1/2:ℝ) ^ 6 * (1:ℝ) ^ 2) := by
  have h := log_four_gt
  rw [le_div_iff₀ (by norm_num)]
  nlinarith [h]

/-- **P3b — what the register's ceiling would cost.**  If `logloglog H ≤ 6.24`
(the sieve register's cap) is to be compatible with the forced demand at `ε = 1/2`,
then `β ≥ 90`.  β is an ERROR GRADE bounded by `cD3/(288·log 4) < 10⁻³`. -/
theorem P3b_beta_needed (b : ℝ) (hb : 0 < b)
    (hcomp : 576 * Real.log 4 / ((1/2:ℝ) ^ 6 * b ^ 2) ≤ 6.24) : (90 : ℝ) ≤ b := by
  have h := log_four_gt
  rw [div_le_iff₀ (by positivity)] at hcomp
  nlinarith [hcomp, hb, sq_nonneg (b - 90)]

/-- **P3c — the frame value.**  At the pinned `ε = 1/500` and
`β = cD3·ε/(144·log 4)` with `cD3 = 1/4`, the forced demand exceeds `10^30`. -/
theorem P3c_frame :
    (10:ℝ) ^ 30 ≤ 576 * Real.log 4
      / (((1:ℝ)/500) ^ 6 * ((1/4) * (1/500) / (144 * Real.log 4)) ^ 2) := by
  have h := log_four_gt
  have h4 : Real.log 4 < 1.3863 := by
    have hh : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [hh]; nlinarith [Real.log_two_lt_d9]
  have hpos : (0:ℝ) < Real.log 4 := by linarith
  rw [le_div_iff₀ (by positivity)]
  have hexp : ((1:ℝ)/500) ^ 6 * ((1/4) * (1/500) / (144 * Real.log 4)) ^ 2
      = 1 / (500 ^ 8 * 4 ^ 2 * 144 ^ 2 * Real.log 4 ^ 2) := by
    field_simp
  rw [hexp]
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  nlinarith [h, h4, hpos, sq_nonneg (Real.log 4)]

/-! ## P4 — the sharp bracket: how much of the 576 is bookkeeping -/

/-- **P4 — the SHARP bracket.**  `bracket_close`'s hypothesis `(κ+log2)/g ≤ (β/4)²`
can be replaced by the AM–GM-optimal `(κ+log2)/g ≤ ((β − 2log2/g)/2)²`: the
`/4` is a factor-2 (hence factor-4 in the demand) bookkeeping loss.  The
minimal honest constant of the SAME shape is therefore `144·log 4`, not `576·log 4`. -/
theorem P4_bracket_sharp (g b κ κD : ℝ) (hg : 0 < g) (hb : 0 < b)
    (hs : 0 < κ + Real.log 2) (hκD : κD ≤ κ + Real.log 2)
    (hmar : 0 ≤ b - 2 * Real.log 2 / g)
    (hiv : (κ + Real.log 2) / g ≤ ((b - 2 * Real.log 2 / g) / 2) ^ 2) :
    (Real.sqrt (g * (κ + Real.log 2)) + 2 * Real.log 2) / g
      + κD / Real.sqrt (g * (κ + Real.log 2)) ≤ b := by
  set s := κ + Real.log 2 with hs_def
  have hgs : 0 < g * s := mul_pos hg hs
  set t := Real.sqrt (g * s) with ht_def
  have ht_pos : 0 < t := Real.sqrt_pos.mpr hgs
  have hsg : 0 ≤ s / g := le_of_lt (div_pos hs hg)
  set r := Real.sqrt (s / g) with hr_def
  have htg_sq : (t / g) ^ 2 = s / g := by
    rw [div_pow, ht_def, Real.sq_sqrt hgs.le]; field_simp
  have htg_nonneg : 0 ≤ t / g := div_nonneg ht_pos.le hg.le
  have htg : t / g = r := by rw [hr_def, ← htg_sq, Real.sqrt_sq htg_nonneg]
  have hst_sq : (s / t) ^ 2 = s / g := by
    rw [div_pow, ht_def, Real.sq_sqrt hgs.le]; field_simp
  have hst_nonneg : 0 ≤ s / t := div_nonneg hs.le ht_pos.le
  have hst : s / t = r := by rw [hr_def, ← hst_sq, Real.sqrt_sq hst_nonneg]
  have hκDt : κD / t ≤ s / t := by gcongr
  have hκDr : κD / t ≤ r := hst ▸ hκDt
  have hr_le : r ≤ (b - 2 * Real.log 2 / g) / 2 := by
    rw [hr_def]
    have h1 : Real.sqrt (s / g) ≤ Real.sqrt (((b - 2 * Real.log 2 / g) / 2) ^ 2) :=
      Real.sqrt_le_sqrt hiv
    rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ (b - 2 * Real.log 2 / g) / 2)] at h1
  rw [add_div, htg]
  have : (2 : ℝ) * Real.log 2 / g = 2 * Real.log 2 / g := rfl
  linarith [hr_le, hκDr]

end S1Budget
