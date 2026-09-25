/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HardyLittlewood.Selberg16.Lev

/-! # HL-3c node M6b — the crown from the mean value

`crown_of_mean` takes M5's statement as a hypothesis and assembles
`π₂(N) ≤ (16·Π₂ + ε)·N/(log N)²` from the level-`N^(1−δ)` sieve (`Lev.lean`):
`S ≥ mainTermSum z + mainTermSum (z/2) ≥ (1−θ)⁵·(log N)²/(16·Π₂)`,
with `δ = θ = min (1/10) (ε/1000)`.
-/

open Finset Filter

namespace Salt.HardyLittlewood.Sel

/-- `zSel θ N / 2 → ∞`. -/
lemma tendsto_zSel_half {θ : ℝ} (hθ : θ < 1) :
    Tendsto (fun N : ℕ => zSel θ N / 2) atTop atTop := by
  have hc : 0 < (1 - θ) / 2 := by linarith
  have h1 : Tendsto (fun N : ℕ => zSel θ N) atTop atTop := by
    unfold zSel
    exact tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop)
  exact Nat.tendsto_div_const_atTop (by norm_num) |>.comp h1

/-- `log (zSel θ N / 2) ≥ ((1−θ)/2)·log N − log 8` once `N^((1−θ)/2) ≥ 8`. -/
lemma log_zSel_half_ge {θ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (h8 : (8 : ℝ) ≤ (N : ℝ) ^ ((1 - θ) / 2)) :
    (1 - θ) / 2 * Real.log N - Real.log 8 ≤ Real.log ((zSel θ N / 2 : ℕ) : ℝ) := by
  set X := (N : ℝ) ^ ((1 - θ) / 2) with hX
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hz : X - 1 ≤ (zSel θ N : ℝ) := by
    have := Nat.lt_floor_add_one X
    unfold zSel; rw [← hX]; linarith
  have hz2 : X / 8 ≤ ((zSel θ N / 2 : ℕ) : ℝ) := by
    have h := Nat.div_mul_le_self (zSel θ N) 2
    have h' : (zSel θ N : ℝ) < ((zSel θ N / 2 : ℕ) : ℝ) * 2 + 2 := by
      have := Nat.lt_div_mul_add (a := zSel θ N) (b := 2) (by norm_num)
      exact_mod_cast this
    linarith
  have hX8 : 0 < X / 8 := by linarith
  have hlog := Real.log_le_log hX8 hz2
  rw [Real.log_div (by linarith) (by norm_num), hX, Real.log_rpow hNpos] at hlog
  linarith

/-- `zSel θ N → ∞`. -/
lemma tendsto_zSel {θ : ℝ} (hθ : θ < 1) :
    Tendsto (fun N : ℕ => zSel θ N) atTop atTop := by
  have hc : 0 < (1 - θ) / 2 := by linarith
  unfold zSel
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop)

/-- The crown from the mean value (M5's statement taken as a hypothesis). -/
theorem crown_of_mean
    (hM5 : ∀ {η : ℝ}, 0 < η → ∀ᶠ z : ℕ in atTop,
      (1 - η) * (Real.log z) ^ 2 / (8 * Pi2) ≤ Salt.M3Assembly.mainTermSum z)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (twinPrimeCounting N : ℝ) ≤ (16 * Pi2 + ε) * N / (Real.log N) ^ 2 := by
  set θ : ℝ := min (1 / 10) (ε / 1000) with hθdef
  have hθ0 : 0 < θ := lt_min (by norm_num) (by linarith)
  have hθ10 : θ ≤ 1 / 10 := min_le_left _ _
  have hθε : θ ≤ ε / 1000 := min_le_right _ _
  have hθ1 : θ < 1 := by linarith
  set c : ℝ := (1 - θ) / 2 with hcdef
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hP0 := pi2_pos
  have hP1 := pi2_lt_one
  -- the eventual facts
  have E1 := twin_le_sel hθ0 hθ1 (η := ε / 2) (by linarith)
  have E2 := (tendsto_zSel_half hθ1).eventually (hM5 hθ0)
  have E3 := (tendsto_zSel hθ1).eventually (hM5 hθ0)
  have E4 : ∀ᶠ N : ℕ in atTop, (8 : ℝ) ≤ (N : ℝ) ^ c :=
    ((tendsto_rpow_atTop hc0).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 8)
  have E5 : ∀ᶠ N : ℕ in atTop, Real.log 8 / (θ * c) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  have E6 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  filter_upwards [E1, E2, E3, E4, E5, E6] with N h1 h2 h3 h4 h5 h6
  have hN : 1 ≤ N := by omega
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast h6
  set L := Real.log N with hLdef
  have hL0 : 0 < L := Real.log_pos (by linarith)
  set z := zSel θ N with hzdef
  set a := Real.log ((z / 2 : ℕ) : ℝ) with hadef
  -- a ≥ (1−θ)·c·L
  have ha1 : c * L - Real.log 8 ≤ a := log_zSel_half_ge hN h4
  have hlog8 : Real.log 8 ≤ θ * c * L := by
    have hθc : 0 < θ * c := mul_pos hθ0 hc0
    have := (div_le_iff₀ hθc).mp h5
    linarith
  have ha2 : (1 - θ) * c * L ≤ a := by nlinarith
  have hapos : 0 < a := lt_of_lt_of_le (by positivity) ha2
  -- z/2 ≥ 1, so log z ≥ a
  have hz2pos : (1 : ℝ) < ((z / 2 : ℕ) : ℝ) := by
    by_contra hle
    have : a ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) (not_lt.mp hle)
    linarith
  have hlogz : a ≤ Real.log (z : ℝ) := by
    apply Real.log_le_log (by linarith)
    exact_mod_cast Nat.div_le_self z 2
  -- the denominator
  have hS := selbergBoundingSum_sel_ge hθ1 N hN
  set S := Salt.SelbergPort.selbergBoundingSum (twinSieveSel θ hθ1 N hN) with hSdef
  have hsq1 : a ^ 2 ≤ (Real.log (z : ℝ)) ^ 2 := pow_le_pow_left₀ hapos.le hlogz 2
  have hK : 0 < (1 - θ) := by linarith
  have hmt1 : (1 - θ) * a ^ 2 / (8 * Pi2) ≤ Salt.M3Assembly.mainTermSum z := by
    refine le_trans ?_ h3
    gcongr
  have hSlow : (1 - θ) ^ 5 * L ^ 2 / (16 * Pi2) ≤ S := by
    have hca : ((1 - θ) * c * L) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by positivity) ha2 2
    have hsum : 2 * ((1 - θ) * a ^ 2 / (8 * Pi2)) ≤ S := by linarith
    have hc2 : c = (1 - θ) / 2 := hcdef
    have : (1 - θ) ^ 5 * L ^ 2 / (16 * Pi2) ≤ 2 * ((1 - θ) * a ^ 2 / (8 * Pi2)) := by
      rw [div_le_iff₀ (by positivity)]
      have e : 2 * ((1 - θ) * a ^ 2 / (8 * Pi2)) * (16 * Pi2) = 4 * (1 - θ) * a ^ 2 := by
        field_simp; ring
      rw [e]
      have : (1 - θ) ^ 5 * L ^ 2 = 4 * (1 - θ) * ((1 - θ) * c * L) ^ 2 := by
        rw [hc2]; ring
      rw [this]
      gcongr
    linarith
  -- the constant
  set K := (1 - θ) ^ 5 with hKdef
  have hKge : 1 - 5 * θ ≤ K := by
    have := one_add_mul_le_pow (a := -θ) (by linarith) 5
    rw [hKdef]; push_cast at this; linarith
  have hKpos : 0 < K := by linarith
  have hconst : 16 * Pi2 / K ≤ 16 * Pi2 + ε / 2 := by
    rw [div_le_iff₀ hKpos]
    nlinarith
  have hlowpos : 0 < K * L ^ 2 / (16 * Pi2) := by positivity
  have hNS : (N : ℝ) / S ≤ (16 * Pi2 + ε / 2) * N / L ^ 2 := by
    calc (N : ℝ) / S ≤ (N : ℝ) / (K * L ^ 2 / (16 * Pi2)) :=
          div_le_div_of_nonneg_left (by positivity) hlowpos hSlow
      _ = (16 * Pi2 / K) * N / L ^ 2 := by field_simp
      _ ≤ (16 * Pi2 + ε / 2) * N / L ^ 2 := by gcongr
  have := h1 hN
  calc (twinPrimeCounting N : ℝ) ≤ (N : ℝ) / S + ε / 2 * N / L ^ 2 := this
    _ ≤ (16 * Pi2 + ε / 2) * N / L ^ 2 + ε / 2 * N / L ^ 2 := by linarith
    _ = (16 * Pi2 + ε) * N / L ^ 2 := by ring

end Salt.HardyLittlewood.Sel
