/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.SuperProfileDef
import Salt.Chen.SuperProfile
import Salt.Chen.LogToolkit

/-!
# SS3c — the hSE domination panels + the numeric-keystone close (even side)

Design: `docs/blueprints/flags.md`, `2026-07-13 SS2`/`SS3`.  Part of the 3-way SS3 transcription.
This file discharges the **even super-solution inequality** `hSE` (SuperSolution.lean's slot),
transcribing the exact-rational certificate of `scripts/ss2_profile.py`:

  `hSE`:  for `v ≥ 2`, `fseq 2 v + (1/v)·∫_v^b Obar(t−1) dt ≤ Ebar v`  (all `b ≥ v`).

## Structure

* `TObar`/`TObar_ge`/`hTO`: the universal tail bound.  Because `Obar ≥ 0`, `∫_v^b Obar(t−1) =
  ∫_{v−1}^{b−1} Obar ≤ TObar (v−1)`, a fixed rational upper bound on each panel; this discharges the
  `∀ b` quantifier (`hSE_reduce`).
* `Obar_suffix`: the right-to-left cumulative `∫_{1+j/20}^{12} Obar = sufKnots j`, proven by one
  downward induction over a `decide`-verified numerator recurrence (`suf_rec_bulk`) — linear, no
  200 separate partial-sum evaluations.
* `Obar_partial`: the moving-lower-endpoint partial-panel integral (quadratic in the endpoint).
* `hptE_0 … hptE_199`: the 200 panel checks.  Panels `0..39` (`v ∈ [2,4)`) carry `fseq 2` and use
  the chord log-majorant (`fseq2_upper_of_log_lower` + `log_half_ge_chord`, 8-digit log knots);
  panels `40..199` are pure rational.  Each is an `nlinarith` quadratic ≥ 0 on its panel.
* `hpt_tail`: the `v ≥ 12` power-tail seam (`(v−2)² ≥ 2` self-domination + the `[12,13)` closure).
* `hpt_holds` (dispatch) → `hSE_holds` (via `hSE_reduce`).

The `Ebar`/`Obar` knot tables are the frozen `ebarNumList`/`obarNumList` of `SuperProfileDef`; the
per-panel margins are certified positive in exact rationals (worst even margin ≈ `5·10⁻⁹`).
-/

open Finset MeasureTheory intervalIntegral Set

namespace Salt.Chen

set_option maxRecDepth 100000
-- MACHINE-GENERATED from `scripts/ss2_profile.py` (SS3c generator): dense exact-rational panel
-- certificates.  Long-line + operator-whitespace style linters disabled for the generated body
-- (cf. `LogToolkit`/`SuperPanelsO`).
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-- Suffix cumulative numerators: `sufNumList[j] = Σ_{k=j}^{219}(ObarNum k + ObarNum (k+1))`,
so `∫_{1+j/20}^{12} Obar = sufNumList[j]/400000000` (`Obar_suffix`). -/
def sufNumList : List ℕ := [282228525, 271234843, 260753062, 250737609, 241148740, 231951587, 223115389, 214612874, 206419750, 198514284, 190876957, 183490171, 176338006, 169406014, 162681041, 156151078, 149805131, 143633111, 137625738, 131774454, 126071352, 120509111, 115080939, 109780525, 104601992, 99539860, 94589011, 89744657, 85002312, 80357768, 75807073, 71346509, 66972574, 62681967, 58471572, 54338445, 50279801, 46293003, 42375551, 38525074, 34739321, 31173248, 27963804, 25074871, 22474255, 20133206, 18026003, 16129598, 14423308, 12888545, 11508586, 10268368, 9154309, 8154150, 7256819, 6452308, 5731564, 5086395, 4509383, 3993809, 3533586, 3123199, 2757648, 2432402, 2143355, 1886786, 1659326, 1457923, 1279816, 1122508, 983741, 861478, 753882, 659298, 576238, 503366, 439485, 383526, 334536, 291668, 254172, 221387, 192732, 167696, 145832, 126748, 110099, 95582, 82932, 71916, 62328, 53988, 46739, 40443, 34978, 30238, 26130, 22572, 19492, 16828, 14526, 12537, 10820, 9339, 8062, 6962, 6014, 5198, 4496, 3892, 3373, 2927, 2544, 2215, 1932, 1688, 1478, 1298, 1144, 1012, 898, 800, 716, 643, 580, 526, 479, 438, 403, 373, 347, 324, 304, 287, 272, 259, 247, 236, 226, 217, 209, 202, 196, 190, 184, 178, 173, 169, 165, 161, 157, 153, 149, 145, 141, 137, 133, 129, 125, 122, 120, 118, 116, 114, 112, 110, 108, 106, 104, 102, 100, 98, 96, 94, 92, 90, 88, 86, 84, 82, 80, 78, 76, 74, 72, 70, 68, 66, 64, 62, 60, 58, 56, 54, 52, 50, 48, 46, 44, 42, 40, 38, 36, 34, 32, 30, 28, 26, 24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2, 0]

noncomputable def sufKnots (j : ℕ) : ℝ := (sufNumList.getD j 0 : ℝ) / 400000000

theorem suf_rec_bulk : ∀ j ∈ Finset.range 220,
    sufNumList.getD j 0 = (ObarNum j + ObarNum (j+1)) + sufNumList.getD (j+1) 0 := by decide

/-- **Right-to-left cumulative.**  `∫_{1+j/20}^{12} Obar = sufKnots j`, via one downward induction
over the `decide`-checked numerator recurrence (linear, not 220 partial sums). -/
theorem Obar_suffix (j : ℕ) (hj : j ≤ 220) :
    (∫ w in (1+(j:ℝ)/20)..12, Obar w) = sufKnots j := by
  suffices h : ∀ m, m ≤ 220 →
      (∫ w in (1+(((220-m:ℕ)):ℝ)/20)..12, Obar w) = sufKnots (220-m) by
    have hh := h (220-j) (by omega)
    rwa [show 220-(220-j) = j by omega] at hh
  intro m
  induction m with
  | zero =>
    intro _
    rw [show (220 - 0 : ℕ) = 220 from rfl, Nat.cast_ofNat,
        show (1:ℝ)+(220:ℝ)/20 = 12 from by norm_num,
        intervalIntegral.integral_same, sufKnots]
    norm_num [sufNumList]
  | succ n ih =>
    intro hn
    have hn' : n ≤ 220 := by omega
    have hlt : 220 - (n+1) < 220 := by omega
    set j := 220 - (n+1) with hjdef
    have hj1 : (220 - n) = j + 1 := by omega
    rw [hj1] at ih
    have ihv := ih hn'
    rw [Nat.cast_add, Nat.cast_one] at ihv
    have hsplit : (∫ w in (1+(j:ℝ)/20)..12, Obar w)
        = (∫ w in (1+(j:ℝ)/20)..(1+((j:ℝ)+1)/20), Obar w)
          + (∫ w in (1+((j:ℝ)+1)/20)..12, Obar w) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
    have hpi := Obar_panel_integral j hlt
    rw [hsplit, hpi, ihv, sufKnots, sufKnots, suf_rec_bulk j (Finset.mem_range.mpr hlt)]
    have ho : (ObarKnots j : ℝ) = (ObarNum j : ℝ)/10000000 := by rw [ObarKnots]; push_cast; ring
    have ho1 : (ObarKnots (j+1) : ℝ) = (ObarNum (j+1) : ℝ)/10000000 := by
      rw [ObarKnots]; push_cast; ring
    rw [ho, ho1]; push_cast; ring

/-- **Moving-endpoint partial-panel integral.**  On Obar panel `i`, `∫_x^{1+(i+1)/20} Obar` is the
trapezoid from `x` (a quadratic in `x`). -/
theorem Obar_partial (i : ℕ) (hi : i < 220) (x : ℝ)
    (hxl : 1 + (i:ℝ)/20 ≤ x) (hxr : x ≤ 1 + ((i:ℝ)+1)/20) :
    (∫ w in x..(1 + ((i:ℝ)+1)/20), Obar w)
      = (ObarKnots i - ((ObarKnots (i+1):ℝ)-ObarKnots i)*20*(1+(i:ℝ)/20)) * ((1+((i:ℝ)+1)/20) - x)
        + (((ObarKnots (i+1):ℝ)-ObarKnots i)*20) * ((1+((i:ℝ)+1)/20)^2 - x^2)/2 := by
  set lo := 1 + (i:ℝ)/20
  set hi' := 1 + ((i:ℝ)+1)/20
  set ci := (ObarKnots i : ℝ)
  set cj := (ObarKnots (i+1) : ℝ)
  have hcong : ∀ᵐ w ∂volume, w ∈ Set.uIoc x hi' →
      Obar w = (ci - (cj-ci)*20*lo) + ((cj-ci)*20)*w := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton hi')] with w hw hmem
    rw [Set.uIoc_of_le hxr] at hmem
    have hwR : w < hi' := lt_of_le_of_ne hmem.2 (by simpa using hw)
    have hwlo : lo ≤ w := le_trans hxl hmem.1.le
    rw [Obar_panel_eq i hi w ⟨hwlo, hwR⟩]; ring
  rw [intervalIntegral.integral_congr_ae hcong, integral_line]

/-- The universal tail bound: `∫_x^{12} Obar + K/(2·12²)` below `12`, the power tail above. -/
noncomputable def TObar (x : ℝ) : ℝ :=
  if x ≤ 12 then (∫ w in x..(12:ℝ), Obar w) + (1/10000)/(2*12^2) else (1/10000)/(2*x^2)

theorem TObar_ge (x : ℝ) (c : ℝ) (hc : x ≤ c) : (∫ w in x..c, Obar w) ≤ TObar x := by
  unfold TObar
  by_cases h12 : x ≤ 12
  · rw [if_pos h12]
    rcases le_or_gt c 12 with hc12 | hc12
    · have hmono : (∫ w in x..c, Obar w) ≤ ∫ w in x..12, Obar w := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
              (Obar_intervalIntegrable x c) (Obar_intervalIntegrable c 12)]
        have : (0:ℝ) ≤ ∫ w in c..12, Obar w :=
          intervalIntegral.integral_nonneg hc12 (fun t _ => Obar_nonneg t)
        linarith
      have : (0:ℝ) ≤ (1/10000)/(2*12^2) := by norm_num
      linarith
    · have hsp : (∫ w in x..c, Obar w) = (∫ w in x..12, Obar w) + ∫ w in (12:ℝ)..c, Obar w :=
        (intervalIntegral.integral_add_adjacent_intervals
          (Obar_intervalIntegrable x 12) (Obar_intervalIntegrable 12 c)).symm
      have htaileq : (∫ w in (12:ℝ)..c, Obar w) = ∫ w in (12:ℝ)..c, (1/10000)/w^3 := by
        apply intervalIntegral.integral_congr
        intro w hw; rw [Set.uIcc_of_le hc12.le] at hw; exact Obar_tail_eq w hw.1
      have htb : (∫ w in (12:ℝ)..c, (1/10000:ℝ)/w^3) ≤ (1/10000)/(2*12^2) :=
        tail_integral_le (by norm_num) (by norm_num) hc12.le
      rw [hsp, htaileq]; linarith
  · rw [if_neg h12]
    replace h12 : (12:ℝ) < x := not_le.mp h12
    have htaileq : (∫ w in x..c, Obar w) = ∫ w in x..c, (1/10000)/w^3 := by
      apply intervalIntegral.integral_congr
      intro w hw; rw [Set.uIcc_of_le hc] at hw; exact Obar_tail_eq w (by linarith [hw.1])
    rw [htaileq]
    exact tail_integral_le (by norm_num) (by linarith) hc

/-- The `∀ b`-family Obar-integral bound (`hSE_reduce`'s `hTO`). -/
theorem hTO : ∀ v, (2:ℝ) ≤ v → ∀ b, v ≤ b → (∫ t in v..b, Obar (t-1)) ≤ TObar (v-1) := by
  intro v _ b hvb
  rw [show (∫ t in v..b, Obar (t-1)) = ∫ w in (v-1)..(b-1), Obar w by
        rw [integral_comp_sub_right (fun w => Obar w) 1]]
  exact TObar_ge (v-1) (b-1) (by linarith)

/-! ## Certified 8-digit log sandwiches for the fseq2 chord majorant -/

theorem le_log_2c : (34657359/50000000 : ℝ) ≤ Real.log 2 :=
  le_log_of_taylor (n:=10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem log_two_le_c : Real.log 2 ≤ 69314719/100000000 :=
  log_le_of_taylor (by norm_num) 10 (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem log_threehalf_le_c : Real.log (3/2) ≤ 40546511/100000000 :=
  log_le_of_taylor (by norm_num) 9 (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem L3up_c : Real.log 3 ≤ 10986123/10000000 := by
  rw [show (3:ℝ) = 2*(3/2) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [log_two_le_c, log_threehalf_le_c]

theorem loglow_0 : (0:ℝ) ≤ Real.log 1 := by rw [Real.log_one]

theorem loglow_1 : (609877/12500000 : ℝ) ≤ Real.log (21/20) :=
  le_log_of_taylor (n:=6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_2 : (9531017/100000000 : ℝ) ≤ Real.log (11/10) :=
  le_log_of_taylor (n:=6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_3 : (6988097/50000000 : ℝ) ≤ Real.log (23/20) :=
  le_log_of_taylor (n:=6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_4 : (3646431/20000000 : ℝ) ≤ Real.log (6/5) :=
  le_log_of_taylor (n:=6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_5 : (4462871/20000000 : ℝ) ≤ Real.log (5/4) :=
  le_log_of_taylor (n:=7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_6 : (13118213/50000000 : ℝ) ≤ Real.log (13/10) :=
  le_log_of_taylor (n:=7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_7 : (30010459/100000000 : ℝ) ≤ Real.log (27/20) :=
  le_log_of_taylor (n:=8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_8 : (33647223/100000000 : ℝ) ≤ Real.log (7/5) :=
  le_log_of_taylor (n:=8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_9 : (7431271/20000000 : ℝ) ≤ Real.log (29/20) :=
  le_log_of_taylor (n:=8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_10 : (4054651/10000000 : ℝ) ≤ Real.log (3/2) :=
  le_log_of_taylor (n:=8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_11 : (43825493/100000000 : ℝ) ≤ Real.log (31/20) :=
  le_log_of_taylor (n:=9) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_12 : (23500181/50000000 : ℝ) ≤ Real.log (8/5) :=
  le_log_of_taylor (n:=8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_13 : (6259691/12500000 : ℝ) ≤ Real.log (33/20) :=
  le_log_of_taylor (n:=8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_14 : (2122513/4000000 : ℝ) ≤ Real.log (17/10) :=
  le_log_of_taylor (n:=9) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_15 : (27980789/50000000 : ℝ) ≤ Real.log (7/4) :=
  le_log_of_taylor (n:=9) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_16 : (29389333/50000000 : ℝ) ≤ Real.log (9/5) :=
  le_log_of_taylor (n:=9) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_17 : (61518563/100000000 : ℝ) ≤ Real.log (37/20) :=
  le_log_of_taylor (n:=9) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_18 : (16046347/25000000 : ℝ) ≤ Real.log (19/10) :=
  le_log_of_taylor (n:=9) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_19 : (66782937/100000000 : ℝ) ≤ Real.log (39/20) :=
  le_log_of_taylor (n:=9) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem loglow_20 : (34657359/50000000 : ℝ) ≤ Real.log (2) :=
  le_log_of_taylor (n:=10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem logh_21 : (2469261/100000000 : ℝ) ≤ Real.log (41/40) :=
  le_log_of_taylor (n:=6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_21 : (71783979/100000000 : ℝ) ≤ Real.log (41/20) := by
  rw [show (41/20:ℝ) = 2*(41/40) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_21]

theorem logh_22 : (609877/12500000 : ℝ) ≤ Real.log (21/20) :=
  le_log_of_taylor (n:=6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_22 : (37096867/50000000 : ℝ) ≤ Real.log (21/10) := by
  rw [show (21/10:ℝ) = 2*(21/20) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_22]

theorem logh_23 : (3616033/50000000 : ℝ) ≤ Real.log (43/40) :=
  le_log_of_taylor (n:=6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_23 : (2392087/3125000 : ℝ) ≤ Real.log (43/20) := by
  rw [show (43/20:ℝ) = 2*(43/40) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_23]

theorem logh_24 : (9531017/100000000 : ℝ) ≤ Real.log (11/10) :=
  le_log_of_taylor (n:=6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_24 : (15769147/20000000 : ℝ) ≤ Real.log (11/5) := by
  rw [show (11/5:ℝ) = 2*(11/10) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_24]

theorem logh_25 : (11778303/100000000 : ℝ) ≤ Real.log (9/8) :=
  le_log_of_taylor (n:=6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_25 : (81093021/100000000 : ℝ) ≤ Real.log (9/4) := by
  rw [show (9/4:ℝ) = 2*(9/8) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_25]

theorem logh_26 : (6988097/50000000 : ℝ) ≤ Real.log (23/20) :=
  le_log_of_taylor (n:=6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_26 : (2602841/3125000 : ℝ) ≤ Real.log (23/10) := by
  rw [show (23/10:ℝ) = 2*(23/20) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_26]

theorem logh_27 : (8063407/50000000 : ℝ) ≤ Real.log (47/40) :=
  le_log_of_taylor (n:=6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_27 : (21360383/25000000 : ℝ) ≤ Real.log (47/20) := by
  rw [show (47/20:ℝ) = 2*(47/40) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_27]

theorem logh_28 : (3646431/20000000 : ℝ) ≤ Real.log (6/5) :=
  le_log_of_taylor (n:=6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_28 : (87546873/100000000 : ℝ) ≤ Real.log (12/5) := by
  rw [show (12/5:ℝ) = 2*(6/5) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_28]

theorem logh_29 : (5073521/25000000 : ℝ) ≤ Real.log (49/40) :=
  le_log_of_taylor (n:=7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_29 : (44804401/50000000 : ℝ) ≤ Real.log (49/20) := by
  rw [show (49/20:ℝ) = 2*(49/40) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_29]

theorem logh_30 : (4462871/20000000 : ℝ) ≤ Real.log (5/4) :=
  le_log_of_taylor (n:=7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_30 : (91629073/100000000 : ℝ) ≤ Real.log (5/2) := by
  rw [show (5/2:ℝ) = 2*(5/4) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_30]

theorem logh_31 : (24294617/100000000 : ℝ) ≤ Real.log (51/40) :=
  le_log_of_taylor (n:=7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_31 : (18721867/20000000 : ℝ) ≤ Real.log (51/20) := by
  rw [show (51/20:ℝ) = 2*(51/40) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_31]

theorem logh_32 : (13118213/50000000 : ℝ) ≤ Real.log (13/10) :=
  le_log_of_taylor (n:=7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_32 : (11943893/12500000 : ℝ) ≤ Real.log (13/5) := by
  rw [show (13/5:ℝ) = 2*(13/10) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_32]

theorem logh_33 : (5628249/20000000 : ℝ) ≤ Real.log (53/40) :=
  le_log_of_taylor (n:=7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_33 : (97455963/100000000 : ℝ) ≤ Real.log (53/20) := by
  rw [show (53/20:ℝ) = 2*(53/40) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_33]

theorem logh_34 : (30010459/100000000 : ℝ) ≤ Real.log (27/20) :=
  le_log_of_taylor (n:=8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_34 : (99325177/100000000 : ℝ) ≤ Real.log (27/10) := by
  rw [show (27/10:ℝ) = 2*(27/20) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_34]

theorem logh_35 : (31845373/100000000 : ℝ) ≤ Real.log (11/8) :=
  le_log_of_taylor (n:=8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_35 : (101160091/100000000 : ℝ) ≤ Real.log (11/4) := by
  rw [show (11/4:ℝ) = 2*(11/8) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_35]

theorem logh_36 : (33647223/100000000 : ℝ) ≤ Real.log (7/5) :=
  le_log_of_taylor (n:=8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_36 : (102961941/100000000 : ℝ) ≤ Real.log (14/5) := by
  rw [show (14/5:ℝ) = 2*(7/5) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_36]

theorem logh_37 : (35417181/100000000 : ℝ) ≤ Real.log (57/40) :=
  le_log_of_taylor (n:=8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_37 : (104731899/100000000 : ℝ) ≤ Real.log (57/20) := by
  rw [show (57/20:ℝ) = 2*(57/40) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_37]

theorem logh_38 : (7431271/20000000 : ℝ) ≤ Real.log (29/20) :=
  le_log_of_taylor (n:=8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_38 : (106471073/100000000 : ℝ) ≤ Real.log (29/10) := by
  rw [show (29/10:ℝ) = 2*(29/20) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_38]

theorem logh_39 : (19432899/50000000 : ℝ) ≤ Real.log (59/40) :=
  le_log_of_taylor (n:=8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_39 : (27045129/25000000 : ℝ) ≤ Real.log (59/20) := by
  rw [show (59/20:ℝ) = 2*(59/40) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_39]

theorem logh_40 : (4054651/10000000 : ℝ) ≤ Real.log (3/2) :=
  le_log_of_taylor (n:=8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem loglow_40 : (27465307/25000000 : ℝ) ≤ Real.log (3) := by
  rw [show (3:ℝ) = 2*(3/2) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [le_log_2c, logh_40]

/-! ## Chord log-majorants (panels carrying `fseq 2`) -/

theorem chord_0 (v : ℝ) (hvl : (2:ℝ) ≤ v) (hvr : v ≤ 41/20) :
    20*(0)*(41/20-v) + 20*(609877/12500000)*(v-2) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(2-1)) (q:=2*((41/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=0) (lq:=609877/12500000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(2-1))/2 = (1:ℝ) by ring]; exact loglow_0)
    (by rw [show (2*((41/20:ℝ)-1))/2 = (21/20:ℝ) by ring]; exact loglow_1)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(0)*(41/20-v) + 20*(609877/12500000)*(v-2)
      = (0:ℝ)*((2*((41/20:ℝ)-1)-2*(v-1))/(2*((41/20:ℝ)-1)-2*(2-1)))
            + (609877/12500000)*((2*(v-1)-2*(2-1))/(2*((41/20:ℝ)-1)-2*(2-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_1 (v : ℝ) (hvl : (41/20:ℝ) ≤ v) (hvr : v ≤ 21/10) :
    20*(609877/12500000)*(21/10-v) + 20*(9531017/100000000)*(v-41/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(41/20-1)) (q:=2*((21/10:ℝ)-1)) (s:=2*(v-1))
    (lp:=609877/12500000) (lq:=9531017/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(41/20-1))/2 = (21/20:ℝ) by ring]; exact loglow_1)
    (by rw [show (2*((21/10:ℝ)-1))/2 = (11/10:ℝ) by ring]; exact loglow_2)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(609877/12500000)*(21/10-v) + 20*(9531017/100000000)*(v-41/20)
      = (609877/12500000:ℝ)*((2*((21/10:ℝ)-1)-2*(v-1))/(2*((21/10:ℝ)-1)-2*(41/20-1)))
            + (9531017/100000000)*((2*(v-1)-2*(41/20-1))/(2*((21/10:ℝ)-1)-2*(41/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_2 (v : ℝ) (hvl : (21/10:ℝ) ≤ v) (hvr : v ≤ 43/20) :
    20*(9531017/100000000)*(43/20-v) + 20*(6988097/50000000)*(v-21/10) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(21/10-1)) (q:=2*((43/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=9531017/100000000) (lq:=6988097/50000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(21/10-1))/2 = (11/10:ℝ) by ring]; exact loglow_2)
    (by rw [show (2*((43/20:ℝ)-1))/2 = (23/20:ℝ) by ring]; exact loglow_3)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(9531017/100000000)*(43/20-v) + 20*(6988097/50000000)*(v-21/10)
      = (9531017/100000000:ℝ)*((2*((43/20:ℝ)-1)-2*(v-1))/(2*((43/20:ℝ)-1)-2*(21/10-1)))
            + (6988097/50000000)*((2*(v-1)-2*(21/10-1))/(2*((43/20:ℝ)-1)-2*(21/10-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_3 (v : ℝ) (hvl : (43/20:ℝ) ≤ v) (hvr : v ≤ 11/5) :
    20*(6988097/50000000)*(11/5-v) + 20*(3646431/20000000)*(v-43/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(43/20-1)) (q:=2*((11/5:ℝ)-1)) (s:=2*(v-1))
    (lp:=6988097/50000000) (lq:=3646431/20000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(43/20-1))/2 = (23/20:ℝ) by ring]; exact loglow_3)
    (by rw [show (2*((11/5:ℝ)-1))/2 = (6/5:ℝ) by ring]; exact loglow_4)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(6988097/50000000)*(11/5-v) + 20*(3646431/20000000)*(v-43/20)
      = (6988097/50000000:ℝ)*((2*((11/5:ℝ)-1)-2*(v-1))/(2*((11/5:ℝ)-1)-2*(43/20-1)))
            + (3646431/20000000)*((2*(v-1)-2*(43/20-1))/(2*((11/5:ℝ)-1)-2*(43/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_4 (v : ℝ) (hvl : (11/5:ℝ) ≤ v) (hvr : v ≤ 9/4) :
    20*(3646431/20000000)*(9/4-v) + 20*(4462871/20000000)*(v-11/5) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(11/5-1)) (q:=2*((9/4:ℝ)-1)) (s:=2*(v-1))
    (lp:=3646431/20000000) (lq:=4462871/20000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(11/5-1))/2 = (6/5:ℝ) by ring]; exact loglow_4)
    (by rw [show (2*((9/4:ℝ)-1))/2 = (5/4:ℝ) by ring]; exact loglow_5)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(3646431/20000000)*(9/4-v) + 20*(4462871/20000000)*(v-11/5)
      = (3646431/20000000:ℝ)*((2*((9/4:ℝ)-1)-2*(v-1))/(2*((9/4:ℝ)-1)-2*(11/5-1)))
            + (4462871/20000000)*((2*(v-1)-2*(11/5-1))/(2*((9/4:ℝ)-1)-2*(11/5-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_5 (v : ℝ) (hvl : (9/4:ℝ) ≤ v) (hvr : v ≤ 23/10) :
    20*(4462871/20000000)*(23/10-v) + 20*(13118213/50000000)*(v-9/4) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(9/4-1)) (q:=2*((23/10:ℝ)-1)) (s:=2*(v-1))
    (lp:=4462871/20000000) (lq:=13118213/50000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(9/4-1))/2 = (5/4:ℝ) by ring]; exact loglow_5)
    (by rw [show (2*((23/10:ℝ)-1))/2 = (13/10:ℝ) by ring]; exact loglow_6)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(4462871/20000000)*(23/10-v) + 20*(13118213/50000000)*(v-9/4)
      = (4462871/20000000:ℝ)*((2*((23/10:ℝ)-1)-2*(v-1))/(2*((23/10:ℝ)-1)-2*(9/4-1)))
            + (13118213/50000000)*((2*(v-1)-2*(9/4-1))/(2*((23/10:ℝ)-1)-2*(9/4-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_6 (v : ℝ) (hvl : (23/10:ℝ) ≤ v) (hvr : v ≤ 47/20) :
    20*(13118213/50000000)*(47/20-v) + 20*(30010459/100000000)*(v-23/10) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(23/10-1)) (q:=2*((47/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=13118213/50000000) (lq:=30010459/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(23/10-1))/2 = (13/10:ℝ) by ring]; exact loglow_6)
    (by rw [show (2*((47/20:ℝ)-1))/2 = (27/20:ℝ) by ring]; exact loglow_7)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(13118213/50000000)*(47/20-v) + 20*(30010459/100000000)*(v-23/10)
      = (13118213/50000000:ℝ)*((2*((47/20:ℝ)-1)-2*(v-1))/(2*((47/20:ℝ)-1)-2*(23/10-1)))
            + (30010459/100000000)*((2*(v-1)-2*(23/10-1))/(2*((47/20:ℝ)-1)-2*(23/10-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_7 (v : ℝ) (hvl : (47/20:ℝ) ≤ v) (hvr : v ≤ 12/5) :
    20*(30010459/100000000)*(12/5-v) + 20*(33647223/100000000)*(v-47/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(47/20-1)) (q:=2*((12/5:ℝ)-1)) (s:=2*(v-1))
    (lp:=30010459/100000000) (lq:=33647223/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(47/20-1))/2 = (27/20:ℝ) by ring]; exact loglow_7)
    (by rw [show (2*((12/5:ℝ)-1))/2 = (7/5:ℝ) by ring]; exact loglow_8)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(30010459/100000000)*(12/5-v) + 20*(33647223/100000000)*(v-47/20)
      = (30010459/100000000:ℝ)*((2*((12/5:ℝ)-1)-2*(v-1))/(2*((12/5:ℝ)-1)-2*(47/20-1)))
            + (33647223/100000000)*((2*(v-1)-2*(47/20-1))/(2*((12/5:ℝ)-1)-2*(47/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_8 (v : ℝ) (hvl : (12/5:ℝ) ≤ v) (hvr : v ≤ 49/20) :
    20*(33647223/100000000)*(49/20-v) + 20*(7431271/20000000)*(v-12/5) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(12/5-1)) (q:=2*((49/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=33647223/100000000) (lq:=7431271/20000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(12/5-1))/2 = (7/5:ℝ) by ring]; exact loglow_8)
    (by rw [show (2*((49/20:ℝ)-1))/2 = (29/20:ℝ) by ring]; exact loglow_9)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(33647223/100000000)*(49/20-v) + 20*(7431271/20000000)*(v-12/5)
      = (33647223/100000000:ℝ)*((2*((49/20:ℝ)-1)-2*(v-1))/(2*((49/20:ℝ)-1)-2*(12/5-1)))
            + (7431271/20000000)*((2*(v-1)-2*(12/5-1))/(2*((49/20:ℝ)-1)-2*(12/5-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_9 (v : ℝ) (hvl : (49/20:ℝ) ≤ v) (hvr : v ≤ 5/2) :
    20*(7431271/20000000)*(5/2-v) + 20*(4054651/10000000)*(v-49/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(49/20-1)) (q:=2*((5/2:ℝ)-1)) (s:=2*(v-1))
    (lp:=7431271/20000000) (lq:=4054651/10000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(49/20-1))/2 = (29/20:ℝ) by ring]; exact loglow_9)
    (by rw [show (2*((5/2:ℝ)-1))/2 = (3/2:ℝ) by ring]; exact loglow_10)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(7431271/20000000)*(5/2-v) + 20*(4054651/10000000)*(v-49/20)
      = (7431271/20000000:ℝ)*((2*((5/2:ℝ)-1)-2*(v-1))/(2*((5/2:ℝ)-1)-2*(49/20-1)))
            + (4054651/10000000)*((2*(v-1)-2*(49/20-1))/(2*((5/2:ℝ)-1)-2*(49/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_10 (v : ℝ) (hvl : (5/2:ℝ) ≤ v) (hvr : v ≤ 51/20) :
    20*(4054651/10000000)*(51/20-v) + 20*(43825493/100000000)*(v-5/2) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(5/2-1)) (q:=2*((51/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=4054651/10000000) (lq:=43825493/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(5/2-1))/2 = (3/2:ℝ) by ring]; exact loglow_10)
    (by rw [show (2*((51/20:ℝ)-1))/2 = (31/20:ℝ) by ring]; exact loglow_11)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(4054651/10000000)*(51/20-v) + 20*(43825493/100000000)*(v-5/2)
      = (4054651/10000000:ℝ)*((2*((51/20:ℝ)-1)-2*(v-1))/(2*((51/20:ℝ)-1)-2*(5/2-1)))
            + (43825493/100000000)*((2*(v-1)-2*(5/2-1))/(2*((51/20:ℝ)-1)-2*(5/2-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_11 (v : ℝ) (hvl : (51/20:ℝ) ≤ v) (hvr : v ≤ 13/5) :
    20*(43825493/100000000)*(13/5-v) + 20*(23500181/50000000)*(v-51/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(51/20-1)) (q:=2*((13/5:ℝ)-1)) (s:=2*(v-1))
    (lp:=43825493/100000000) (lq:=23500181/50000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(51/20-1))/2 = (31/20:ℝ) by ring]; exact loglow_11)
    (by rw [show (2*((13/5:ℝ)-1))/2 = (8/5:ℝ) by ring]; exact loglow_12)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(43825493/100000000)*(13/5-v) + 20*(23500181/50000000)*(v-51/20)
      = (43825493/100000000:ℝ)*((2*((13/5:ℝ)-1)-2*(v-1))/(2*((13/5:ℝ)-1)-2*(51/20-1)))
            + (23500181/50000000)*((2*(v-1)-2*(51/20-1))/(2*((13/5:ℝ)-1)-2*(51/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_12 (v : ℝ) (hvl : (13/5:ℝ) ≤ v) (hvr : v ≤ 53/20) :
    20*(23500181/50000000)*(53/20-v) + 20*(6259691/12500000)*(v-13/5) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(13/5-1)) (q:=2*((53/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=23500181/50000000) (lq:=6259691/12500000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(13/5-1))/2 = (8/5:ℝ) by ring]; exact loglow_12)
    (by rw [show (2*((53/20:ℝ)-1))/2 = (33/20:ℝ) by ring]; exact loglow_13)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(23500181/50000000)*(53/20-v) + 20*(6259691/12500000)*(v-13/5)
      = (23500181/50000000:ℝ)*((2*((53/20:ℝ)-1)-2*(v-1))/(2*((53/20:ℝ)-1)-2*(13/5-1)))
            + (6259691/12500000)*((2*(v-1)-2*(13/5-1))/(2*((53/20:ℝ)-1)-2*(13/5-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_13 (v : ℝ) (hvl : (53/20:ℝ) ≤ v) (hvr : v ≤ 27/10) :
    20*(6259691/12500000)*(27/10-v) + 20*(2122513/4000000)*(v-53/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(53/20-1)) (q:=2*((27/10:ℝ)-1)) (s:=2*(v-1))
    (lp:=6259691/12500000) (lq:=2122513/4000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(53/20-1))/2 = (33/20:ℝ) by ring]; exact loglow_13)
    (by rw [show (2*((27/10:ℝ)-1))/2 = (17/10:ℝ) by ring]; exact loglow_14)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(6259691/12500000)*(27/10-v) + 20*(2122513/4000000)*(v-53/20)
      = (6259691/12500000:ℝ)*((2*((27/10:ℝ)-1)-2*(v-1))/(2*((27/10:ℝ)-1)-2*(53/20-1)))
            + (2122513/4000000)*((2*(v-1)-2*(53/20-1))/(2*((27/10:ℝ)-1)-2*(53/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_14 (v : ℝ) (hvl : (27/10:ℝ) ≤ v) (hvr : v ≤ 11/4) :
    20*(2122513/4000000)*(11/4-v) + 20*(27980789/50000000)*(v-27/10) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(27/10-1)) (q:=2*((11/4:ℝ)-1)) (s:=2*(v-1))
    (lp:=2122513/4000000) (lq:=27980789/50000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(27/10-1))/2 = (17/10:ℝ) by ring]; exact loglow_14)
    (by rw [show (2*((11/4:ℝ)-1))/2 = (7/4:ℝ) by ring]; exact loglow_15)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(2122513/4000000)*(11/4-v) + 20*(27980789/50000000)*(v-27/10)
      = (2122513/4000000:ℝ)*((2*((11/4:ℝ)-1)-2*(v-1))/(2*((11/4:ℝ)-1)-2*(27/10-1)))
            + (27980789/50000000)*((2*(v-1)-2*(27/10-1))/(2*((11/4:ℝ)-1)-2*(27/10-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_15 (v : ℝ) (hvl : (11/4:ℝ) ≤ v) (hvr : v ≤ 14/5) :
    20*(27980789/50000000)*(14/5-v) + 20*(29389333/50000000)*(v-11/4) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(11/4-1)) (q:=2*((14/5:ℝ)-1)) (s:=2*(v-1))
    (lp:=27980789/50000000) (lq:=29389333/50000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(11/4-1))/2 = (7/4:ℝ) by ring]; exact loglow_15)
    (by rw [show (2*((14/5:ℝ)-1))/2 = (9/5:ℝ) by ring]; exact loglow_16)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(27980789/50000000)*(14/5-v) + 20*(29389333/50000000)*(v-11/4)
      = (27980789/50000000:ℝ)*((2*((14/5:ℝ)-1)-2*(v-1))/(2*((14/5:ℝ)-1)-2*(11/4-1)))
            + (29389333/50000000)*((2*(v-1)-2*(11/4-1))/(2*((14/5:ℝ)-1)-2*(11/4-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_16 (v : ℝ) (hvl : (14/5:ℝ) ≤ v) (hvr : v ≤ 57/20) :
    20*(29389333/50000000)*(57/20-v) + 20*(61518563/100000000)*(v-14/5) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(14/5-1)) (q:=2*((57/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=29389333/50000000) (lq:=61518563/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(14/5-1))/2 = (9/5:ℝ) by ring]; exact loglow_16)
    (by rw [show (2*((57/20:ℝ)-1))/2 = (37/20:ℝ) by ring]; exact loglow_17)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(29389333/50000000)*(57/20-v) + 20*(61518563/100000000)*(v-14/5)
      = (29389333/50000000:ℝ)*((2*((57/20:ℝ)-1)-2*(v-1))/(2*((57/20:ℝ)-1)-2*(14/5-1)))
            + (61518563/100000000)*((2*(v-1)-2*(14/5-1))/(2*((57/20:ℝ)-1)-2*(14/5-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_17 (v : ℝ) (hvl : (57/20:ℝ) ≤ v) (hvr : v ≤ 29/10) :
    20*(61518563/100000000)*(29/10-v) + 20*(16046347/25000000)*(v-57/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(57/20-1)) (q:=2*((29/10:ℝ)-1)) (s:=2*(v-1))
    (lp:=61518563/100000000) (lq:=16046347/25000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(57/20-1))/2 = (37/20:ℝ) by ring]; exact loglow_17)
    (by rw [show (2*((29/10:ℝ)-1))/2 = (19/10:ℝ) by ring]; exact loglow_18)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(61518563/100000000)*(29/10-v) + 20*(16046347/25000000)*(v-57/20)
      = (61518563/100000000:ℝ)*((2*((29/10:ℝ)-1)-2*(v-1))/(2*((29/10:ℝ)-1)-2*(57/20-1)))
            + (16046347/25000000)*((2*(v-1)-2*(57/20-1))/(2*((29/10:ℝ)-1)-2*(57/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_18 (v : ℝ) (hvl : (29/10:ℝ) ≤ v) (hvr : v ≤ 59/20) :
    20*(16046347/25000000)*(59/20-v) + 20*(66782937/100000000)*(v-29/10) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(29/10-1)) (q:=2*((59/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=16046347/25000000) (lq:=66782937/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(29/10-1))/2 = (19/10:ℝ) by ring]; exact loglow_18)
    (by rw [show (2*((59/20:ℝ)-1))/2 = (39/20:ℝ) by ring]; exact loglow_19)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(16046347/25000000)*(59/20-v) + 20*(66782937/100000000)*(v-29/10)
      = (16046347/25000000:ℝ)*((2*((59/20:ℝ)-1)-2*(v-1))/(2*((59/20:ℝ)-1)-2*(29/10-1)))
            + (66782937/100000000)*((2*(v-1)-2*(29/10-1))/(2*((59/20:ℝ)-1)-2*(29/10-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_19 (v : ℝ) (hvl : (59/20:ℝ) ≤ v) (hvr : v ≤ 3) :
    20*(66782937/100000000)*(3-v) + 20*(34657359/50000000)*(v-59/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(59/20-1)) (q:=2*((3:ℝ)-1)) (s:=2*(v-1))
    (lp:=66782937/100000000) (lq:=34657359/50000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(59/20-1))/2 = (39/20:ℝ) by ring]; exact loglow_19)
    (by rw [show (2*((3:ℝ)-1))/2 = (2:ℝ) by ring]; exact loglow_20)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(66782937/100000000)*(3-v) + 20*(34657359/50000000)*(v-59/20)
      = (66782937/100000000:ℝ)*((2*((3:ℝ)-1)-2*(v-1))/(2*((3:ℝ)-1)-2*(59/20-1)))
            + (34657359/50000000)*((2*(v-1)-2*(59/20-1))/(2*((3:ℝ)-1)-2*(59/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_20 (v : ℝ) (hvl : (3:ℝ) ≤ v) (hvr : v ≤ 61/20) :
    20*(34657359/50000000)*(61/20-v) + 20*(71783979/100000000)*(v-3) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(3-1)) (q:=2*((61/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=34657359/50000000) (lq:=71783979/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(3-1))/2 = (2:ℝ) by ring]; exact loglow_20)
    (by rw [show (2*((61/20:ℝ)-1))/2 = (41/20:ℝ) by ring]; exact loglow_21)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(34657359/50000000)*(61/20-v) + 20*(71783979/100000000)*(v-3)
      = (34657359/50000000:ℝ)*((2*((61/20:ℝ)-1)-2*(v-1))/(2*((61/20:ℝ)-1)-2*(3-1)))
            + (71783979/100000000)*((2*(v-1)-2*(3-1))/(2*((61/20:ℝ)-1)-2*(3-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_21 (v : ℝ) (hvl : (61/20:ℝ) ≤ v) (hvr : v ≤ 31/10) :
    20*(71783979/100000000)*(31/10-v) + 20*(37096867/50000000)*(v-61/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(61/20-1)) (q:=2*((31/10:ℝ)-1)) (s:=2*(v-1))
    (lp:=71783979/100000000) (lq:=37096867/50000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(61/20-1))/2 = (41/20:ℝ) by ring]; exact loglow_21)
    (by rw [show (2*((31/10:ℝ)-1))/2 = (21/10:ℝ) by ring]; exact loglow_22)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(71783979/100000000)*(31/10-v) + 20*(37096867/50000000)*(v-61/20)
      = (71783979/100000000:ℝ)*((2*((31/10:ℝ)-1)-2*(v-1))/(2*((31/10:ℝ)-1)-2*(61/20-1)))
            + (37096867/50000000)*((2*(v-1)-2*(61/20-1))/(2*((31/10:ℝ)-1)-2*(61/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_22 (v : ℝ) (hvl : (31/10:ℝ) ≤ v) (hvr : v ≤ 63/20) :
    20*(37096867/50000000)*(63/20-v) + 20*(2392087/3125000)*(v-31/10) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(31/10-1)) (q:=2*((63/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=37096867/50000000) (lq:=2392087/3125000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(31/10-1))/2 = (21/10:ℝ) by ring]; exact loglow_22)
    (by rw [show (2*((63/20:ℝ)-1))/2 = (43/20:ℝ) by ring]; exact loglow_23)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(37096867/50000000)*(63/20-v) + 20*(2392087/3125000)*(v-31/10)
      = (37096867/50000000:ℝ)*((2*((63/20:ℝ)-1)-2*(v-1))/(2*((63/20:ℝ)-1)-2*(31/10-1)))
            + (2392087/3125000)*((2*(v-1)-2*(31/10-1))/(2*((63/20:ℝ)-1)-2*(31/10-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_23 (v : ℝ) (hvl : (63/20:ℝ) ≤ v) (hvr : v ≤ 16/5) :
    20*(2392087/3125000)*(16/5-v) + 20*(15769147/20000000)*(v-63/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(63/20-1)) (q:=2*((16/5:ℝ)-1)) (s:=2*(v-1))
    (lp:=2392087/3125000) (lq:=15769147/20000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(63/20-1))/2 = (43/20:ℝ) by ring]; exact loglow_23)
    (by rw [show (2*((16/5:ℝ)-1))/2 = (11/5:ℝ) by ring]; exact loglow_24)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(2392087/3125000)*(16/5-v) + 20*(15769147/20000000)*(v-63/20)
      = (2392087/3125000:ℝ)*((2*((16/5:ℝ)-1)-2*(v-1))/(2*((16/5:ℝ)-1)-2*(63/20-1)))
            + (15769147/20000000)*((2*(v-1)-2*(63/20-1))/(2*((16/5:ℝ)-1)-2*(63/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_24 (v : ℝ) (hvl : (16/5:ℝ) ≤ v) (hvr : v ≤ 13/4) :
    20*(15769147/20000000)*(13/4-v) + 20*(81093021/100000000)*(v-16/5) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(16/5-1)) (q:=2*((13/4:ℝ)-1)) (s:=2*(v-1))
    (lp:=15769147/20000000) (lq:=81093021/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(16/5-1))/2 = (11/5:ℝ) by ring]; exact loglow_24)
    (by rw [show (2*((13/4:ℝ)-1))/2 = (9/4:ℝ) by ring]; exact loglow_25)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(15769147/20000000)*(13/4-v) + 20*(81093021/100000000)*(v-16/5)
      = (15769147/20000000:ℝ)*((2*((13/4:ℝ)-1)-2*(v-1))/(2*((13/4:ℝ)-1)-2*(16/5-1)))
            + (81093021/100000000)*((2*(v-1)-2*(16/5-1))/(2*((13/4:ℝ)-1)-2*(16/5-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_25 (v : ℝ) (hvl : (13/4:ℝ) ≤ v) (hvr : v ≤ 33/10) :
    20*(81093021/100000000)*(33/10-v) + 20*(2602841/3125000)*(v-13/4) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(13/4-1)) (q:=2*((33/10:ℝ)-1)) (s:=2*(v-1))
    (lp:=81093021/100000000) (lq:=2602841/3125000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(13/4-1))/2 = (9/4:ℝ) by ring]; exact loglow_25)
    (by rw [show (2*((33/10:ℝ)-1))/2 = (23/10:ℝ) by ring]; exact loglow_26)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(81093021/100000000)*(33/10-v) + 20*(2602841/3125000)*(v-13/4)
      = (81093021/100000000:ℝ)*((2*((33/10:ℝ)-1)-2*(v-1))/(2*((33/10:ℝ)-1)-2*(13/4-1)))
            + (2602841/3125000)*((2*(v-1)-2*(13/4-1))/(2*((33/10:ℝ)-1)-2*(13/4-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_26 (v : ℝ) (hvl : (33/10:ℝ) ≤ v) (hvr : v ≤ 67/20) :
    20*(2602841/3125000)*(67/20-v) + 20*(21360383/25000000)*(v-33/10) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(33/10-1)) (q:=2*((67/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=2602841/3125000) (lq:=21360383/25000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(33/10-1))/2 = (23/10:ℝ) by ring]; exact loglow_26)
    (by rw [show (2*((67/20:ℝ)-1))/2 = (47/20:ℝ) by ring]; exact loglow_27)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(2602841/3125000)*(67/20-v) + 20*(21360383/25000000)*(v-33/10)
      = (2602841/3125000:ℝ)*((2*((67/20:ℝ)-1)-2*(v-1))/(2*((67/20:ℝ)-1)-2*(33/10-1)))
            + (21360383/25000000)*((2*(v-1)-2*(33/10-1))/(2*((67/20:ℝ)-1)-2*(33/10-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_27 (v : ℝ) (hvl : (67/20:ℝ) ≤ v) (hvr : v ≤ 17/5) :
    20*(21360383/25000000)*(17/5-v) + 20*(87546873/100000000)*(v-67/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(67/20-1)) (q:=2*((17/5:ℝ)-1)) (s:=2*(v-1))
    (lp:=21360383/25000000) (lq:=87546873/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(67/20-1))/2 = (47/20:ℝ) by ring]; exact loglow_27)
    (by rw [show (2*((17/5:ℝ)-1))/2 = (12/5:ℝ) by ring]; exact loglow_28)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(21360383/25000000)*(17/5-v) + 20*(87546873/100000000)*(v-67/20)
      = (21360383/25000000:ℝ)*((2*((17/5:ℝ)-1)-2*(v-1))/(2*((17/5:ℝ)-1)-2*(67/20-1)))
            + (87546873/100000000)*((2*(v-1)-2*(67/20-1))/(2*((17/5:ℝ)-1)-2*(67/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_28 (v : ℝ) (hvl : (17/5:ℝ) ≤ v) (hvr : v ≤ 69/20) :
    20*(87546873/100000000)*(69/20-v) + 20*(44804401/50000000)*(v-17/5) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(17/5-1)) (q:=2*((69/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=87546873/100000000) (lq:=44804401/50000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(17/5-1))/2 = (12/5:ℝ) by ring]; exact loglow_28)
    (by rw [show (2*((69/20:ℝ)-1))/2 = (49/20:ℝ) by ring]; exact loglow_29)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(87546873/100000000)*(69/20-v) + 20*(44804401/50000000)*(v-17/5)
      = (87546873/100000000:ℝ)*((2*((69/20:ℝ)-1)-2*(v-1))/(2*((69/20:ℝ)-1)-2*(17/5-1)))
            + (44804401/50000000)*((2*(v-1)-2*(17/5-1))/(2*((69/20:ℝ)-1)-2*(17/5-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_29 (v : ℝ) (hvl : (69/20:ℝ) ≤ v) (hvr : v ≤ 7/2) :
    20*(44804401/50000000)*(7/2-v) + 20*(91629073/100000000)*(v-69/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(69/20-1)) (q:=2*((7/2:ℝ)-1)) (s:=2*(v-1))
    (lp:=44804401/50000000) (lq:=91629073/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(69/20-1))/2 = (49/20:ℝ) by ring]; exact loglow_29)
    (by rw [show (2*((7/2:ℝ)-1))/2 = (5/2:ℝ) by ring]; exact loglow_30)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(44804401/50000000)*(7/2-v) + 20*(91629073/100000000)*(v-69/20)
      = (44804401/50000000:ℝ)*((2*((7/2:ℝ)-1)-2*(v-1))/(2*((7/2:ℝ)-1)-2*(69/20-1)))
            + (91629073/100000000)*((2*(v-1)-2*(69/20-1))/(2*((7/2:ℝ)-1)-2*(69/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_30 (v : ℝ) (hvl : (7/2:ℝ) ≤ v) (hvr : v ≤ 71/20) :
    20*(91629073/100000000)*(71/20-v) + 20*(18721867/20000000)*(v-7/2) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(7/2-1)) (q:=2*((71/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=91629073/100000000) (lq:=18721867/20000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(7/2-1))/2 = (5/2:ℝ) by ring]; exact loglow_30)
    (by rw [show (2*((71/20:ℝ)-1))/2 = (51/20:ℝ) by ring]; exact loglow_31)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(91629073/100000000)*(71/20-v) + 20*(18721867/20000000)*(v-7/2)
      = (91629073/100000000:ℝ)*((2*((71/20:ℝ)-1)-2*(v-1))/(2*((71/20:ℝ)-1)-2*(7/2-1)))
            + (18721867/20000000)*((2*(v-1)-2*(7/2-1))/(2*((71/20:ℝ)-1)-2*(7/2-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_31 (v : ℝ) (hvl : (71/20:ℝ) ≤ v) (hvr : v ≤ 18/5) :
    20*(18721867/20000000)*(18/5-v) + 20*(11943893/12500000)*(v-71/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(71/20-1)) (q:=2*((18/5:ℝ)-1)) (s:=2*(v-1))
    (lp:=18721867/20000000) (lq:=11943893/12500000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(71/20-1))/2 = (51/20:ℝ) by ring]; exact loglow_31)
    (by rw [show (2*((18/5:ℝ)-1))/2 = (13/5:ℝ) by ring]; exact loglow_32)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(18721867/20000000)*(18/5-v) + 20*(11943893/12500000)*(v-71/20)
      = (18721867/20000000:ℝ)*((2*((18/5:ℝ)-1)-2*(v-1))/(2*((18/5:ℝ)-1)-2*(71/20-1)))
            + (11943893/12500000)*((2*(v-1)-2*(71/20-1))/(2*((18/5:ℝ)-1)-2*(71/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_32 (v : ℝ) (hvl : (18/5:ℝ) ≤ v) (hvr : v ≤ 73/20) :
    20*(11943893/12500000)*(73/20-v) + 20*(97455963/100000000)*(v-18/5) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(18/5-1)) (q:=2*((73/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=11943893/12500000) (lq:=97455963/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(18/5-1))/2 = (13/5:ℝ) by ring]; exact loglow_32)
    (by rw [show (2*((73/20:ℝ)-1))/2 = (53/20:ℝ) by ring]; exact loglow_33)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(11943893/12500000)*(73/20-v) + 20*(97455963/100000000)*(v-18/5)
      = (11943893/12500000:ℝ)*((2*((73/20:ℝ)-1)-2*(v-1))/(2*((73/20:ℝ)-1)-2*(18/5-1)))
            + (97455963/100000000)*((2*(v-1)-2*(18/5-1))/(2*((73/20:ℝ)-1)-2*(18/5-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_33 (v : ℝ) (hvl : (73/20:ℝ) ≤ v) (hvr : v ≤ 37/10) :
    20*(97455963/100000000)*(37/10-v) + 20*(99325177/100000000)*(v-73/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(73/20-1)) (q:=2*((37/10:ℝ)-1)) (s:=2*(v-1))
    (lp:=97455963/100000000) (lq:=99325177/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(73/20-1))/2 = (53/20:ℝ) by ring]; exact loglow_33)
    (by rw [show (2*((37/10:ℝ)-1))/2 = (27/10:ℝ) by ring]; exact loglow_34)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(97455963/100000000)*(37/10-v) + 20*(99325177/100000000)*(v-73/20)
      = (97455963/100000000:ℝ)*((2*((37/10:ℝ)-1)-2*(v-1))/(2*((37/10:ℝ)-1)-2*(73/20-1)))
            + (99325177/100000000)*((2*(v-1)-2*(73/20-1))/(2*((37/10:ℝ)-1)-2*(73/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_34 (v : ℝ) (hvl : (37/10:ℝ) ≤ v) (hvr : v ≤ 15/4) :
    20*(99325177/100000000)*(15/4-v) + 20*(101160091/100000000)*(v-37/10) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(37/10-1)) (q:=2*((15/4:ℝ)-1)) (s:=2*(v-1))
    (lp:=99325177/100000000) (lq:=101160091/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(37/10-1))/2 = (27/10:ℝ) by ring]; exact loglow_34)
    (by rw [show (2*((15/4:ℝ)-1))/2 = (11/4:ℝ) by ring]; exact loglow_35)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(99325177/100000000)*(15/4-v) + 20*(101160091/100000000)*(v-37/10)
      = (99325177/100000000:ℝ)*((2*((15/4:ℝ)-1)-2*(v-1))/(2*((15/4:ℝ)-1)-2*(37/10-1)))
            + (101160091/100000000)*((2*(v-1)-2*(37/10-1))/(2*((15/4:ℝ)-1)-2*(37/10-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_35 (v : ℝ) (hvl : (15/4:ℝ) ≤ v) (hvr : v ≤ 19/5) :
    20*(101160091/100000000)*(19/5-v) + 20*(102961941/100000000)*(v-15/4) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(15/4-1)) (q:=2*((19/5:ℝ)-1)) (s:=2*(v-1))
    (lp:=101160091/100000000) (lq:=102961941/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(15/4-1))/2 = (11/4:ℝ) by ring]; exact loglow_35)
    (by rw [show (2*((19/5:ℝ)-1))/2 = (14/5:ℝ) by ring]; exact loglow_36)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(101160091/100000000)*(19/5-v) + 20*(102961941/100000000)*(v-15/4)
      = (101160091/100000000:ℝ)*((2*((19/5:ℝ)-1)-2*(v-1))/(2*((19/5:ℝ)-1)-2*(15/4-1)))
            + (102961941/100000000)*((2*(v-1)-2*(15/4-1))/(2*((19/5:ℝ)-1)-2*(15/4-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_36 (v : ℝ) (hvl : (19/5:ℝ) ≤ v) (hvr : v ≤ 77/20) :
    20*(102961941/100000000)*(77/20-v) + 20*(104731899/100000000)*(v-19/5) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(19/5-1)) (q:=2*((77/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=102961941/100000000) (lq:=104731899/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(19/5-1))/2 = (14/5:ℝ) by ring]; exact loglow_36)
    (by rw [show (2*((77/20:ℝ)-1))/2 = (57/20:ℝ) by ring]; exact loglow_37)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(102961941/100000000)*(77/20-v) + 20*(104731899/100000000)*(v-19/5)
      = (102961941/100000000:ℝ)*((2*((77/20:ℝ)-1)-2*(v-1))/(2*((77/20:ℝ)-1)-2*(19/5-1)))
            + (104731899/100000000)*((2*(v-1)-2*(19/5-1))/(2*((77/20:ℝ)-1)-2*(19/5-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_37 (v : ℝ) (hvl : (77/20:ℝ) ≤ v) (hvr : v ≤ 39/10) :
    20*(104731899/100000000)*(39/10-v) + 20*(106471073/100000000)*(v-77/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(77/20-1)) (q:=2*((39/10:ℝ)-1)) (s:=2*(v-1))
    (lp:=104731899/100000000) (lq:=106471073/100000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(77/20-1))/2 = (57/20:ℝ) by ring]; exact loglow_37)
    (by rw [show (2*((39/10:ℝ)-1))/2 = (29/10:ℝ) by ring]; exact loglow_38)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(104731899/100000000)*(39/10-v) + 20*(106471073/100000000)*(v-77/20)
      = (104731899/100000000:ℝ)*((2*((39/10:ℝ)-1)-2*(v-1))/(2*((39/10:ℝ)-1)-2*(77/20-1)))
            + (106471073/100000000)*((2*(v-1)-2*(77/20-1))/(2*((39/10:ℝ)-1)-2*(77/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_38 (v : ℝ) (hvl : (39/10:ℝ) ≤ v) (hvr : v ≤ 79/20) :
    20*(106471073/100000000)*(79/20-v) + 20*(27045129/25000000)*(v-39/10) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(39/10-1)) (q:=2*((79/20:ℝ)-1)) (s:=2*(v-1))
    (lp:=106471073/100000000) (lq:=27045129/25000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(39/10-1))/2 = (29/10:ℝ) by ring]; exact loglow_38)
    (by rw [show (2*((79/20:ℝ)-1))/2 = (59/20:ℝ) by ring]; exact loglow_39)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(106471073/100000000)*(79/20-v) + 20*(27045129/25000000)*(v-39/10)
      = (106471073/100000000:ℝ)*((2*((79/20:ℝ)-1)-2*(v-1))/(2*((79/20:ℝ)-1)-2*(39/10-1)))
            + (27045129/25000000)*((2*(v-1)-2*(39/10-1))/(2*((79/20:ℝ)-1)-2*(39/10-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

theorem chord_39 (v : ℝ) (hvl : (79/20:ℝ) ≤ v) (hvr : v ≤ 4) :
    20*(27045129/25000000)*(4-v) + 20*(27465307/25000000)*(v-79/20) ≤ Real.log (v-1) := by
  have h := log_half_ge_chord (p:=2*(79/20-1)) (q:=2*((4:ℝ)-1)) (s:=2*(v-1))
    (lp:=27045129/25000000) (lq:=27465307/25000000)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by rw [show (2*(79/20-1))/2 = (59/20:ℝ) by ring]; exact loglow_39)
    (by rw [show (2*((4:ℝ)-1))/2 = (3:ℝ) by ring]; exact loglow_40)
  rw [show (2*(v-1))/2 = v-1 by ring] at h
  calc 20*(27045129/25000000)*(4-v) + 20*(27465307/25000000)*(v-79/20)
      = (27045129/25000000:ℝ)*((2*((4:ℝ)-1)-2*(v-1))/(2*((4:ℝ)-1)-2*(79/20-1)))
            + (27465307/25000000)*((2*(v-1)-2*(79/20-1))/(2*((4:ℝ)-1)-2*(79/20-1))) := by field_simp; ring
    _ ≤ Real.log (v-1) := h

/-! ## The 200 hSE panels -/

theorem hptE_0 : ∀ v ∈ Set.Ico (2+((0:ℕ):ℝ)/20) (2+(((0:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 41/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(0)*(41/20-v) + 20*(609877/12500000)*(v-2))
    (L3up := 10986123/10000000) hv2 hv4 (chord_0 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 0 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 0 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((0:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 1 := by
    rw [show (1+(((0:ℕ):ℝ)+1)/20) = 1+((1:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 1 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((0:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((0:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 0:ℝ) = 5630910/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 1:ℝ) = 5362772/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 0:ℝ) = 10007043/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 1:ℝ) = 9158801/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 1 = 271234843/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(0)*(41/20-v) + 20*(609877/12500000)*(v-2)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((5630910/10000000 - ((5362772/10000000:ℝ)-5630910/10000000)*20*(1+((0:ℕ):ℝ)/20))*((1+(((0:ℕ):ℝ)+1)/20)-(v-1))
              + ((5362772/10000000:ℝ)-5630910/10000000)*20*((1+(((0:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (271234843:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 10007043/10000000 + ((9158801/10000000:ℝ)-10007043/10000000)*(v-(2+((0:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-2) (by push_cast at hvr; linarith : (0:ℝ) ≤ 41/20-v),
      sq_nonneg (v-2), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_1 : ∀ v ∈ Set.Ico (2+((1:ℕ):ℝ)/20) (2+(((1:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (41/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 21/10 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(609877/12500000)*(21/10-v) + 20*(9531017/100000000)*(v-41/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_1 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 1 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 1 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((1:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 2 := by
    rw [show (1+(((1:ℕ):ℝ)+1)/20) = 1+((2:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 2 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((1:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((1:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 1:ℝ) = 5362772/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 2:ℝ) = 5119009/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 1:ℝ) = 9158801/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 2:ℝ) = 8389475/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 2 = 260753062/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(609877/12500000)*(21/10-v) + 20*(9531017/100000000)*(v-41/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((5362772/10000000 - ((5119009/10000000:ℝ)-5362772/10000000)*20*(1+((1:ℕ):ℝ)/20))*((1+(((1:ℕ):ℝ)+1)/20)-(v-1))
              + ((5119009/10000000:ℝ)-5362772/10000000)*20*((1+(((1:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (260753062:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 9158801/10000000 + ((8389475/10000000:ℝ)-9158801/10000000)*(v-(2+((1:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-41/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 21/10-v),
      sq_nonneg (v-41/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_2 : ∀ v ∈ Set.Ico (2+((2:ℕ):ℝ)/20) (2+(((2:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (21/10:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 43/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(9531017/100000000)*(43/20-v) + 20*(6988097/50000000)*(v-21/10))
    (L3up := 10986123/10000000) hv2 hv4 (chord_2 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 2 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 2 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((2:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 3 := by
    rw [show (1+(((2:ℕ):ℝ)+1)/20) = 1+((3:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 3 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((2:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((2:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 2:ℝ) = 5119009/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 3:ℝ) = 4896444/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 2:ℝ) = 8389475/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 3:ℝ) = 7690212/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 3 = 250737609/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(9531017/100000000)*(43/20-v) + 20*(6988097/50000000)*(v-21/10)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((5119009/10000000 - ((4896444/10000000:ℝ)-5119009/10000000)*20*(1+((2:ℕ):ℝ)/20))*((1+(((2:ℕ):ℝ)+1)/20)-(v-1))
              + ((4896444/10000000:ℝ)-5119009/10000000)*20*((1+(((2:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (250737609:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 8389475/10000000 + ((7690212/10000000:ℝ)-8389475/10000000)*(v-(2+((2:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-21/10) (by push_cast at hvr; linarith : (0:ℝ) ≤ 43/20-v),
      sq_nonneg (v-21/10), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_3 : ∀ v ∈ Set.Ico (2+((3:ℕ):ℝ)/20) (2+(((3:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (43/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 11/5 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(6988097/50000000)*(11/5-v) + 20*(3646431/20000000)*(v-43/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_3 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 3 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 3 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((3:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 4 := by
    rw [show (1+(((3:ℕ):ℝ)+1)/20) = 1+((4:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 4 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((3:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((3:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 3:ℝ) = 4896444/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 4:ℝ) = 4692425/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 3:ℝ) = 7690212/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 4:ℝ) = 7053385/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 4 = 241148740/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(6988097/50000000)*(11/5-v) + 20*(3646431/20000000)*(v-43/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((4896444/10000000 - ((4692425/10000000:ℝ)-4896444/10000000)*20*(1+((3:ℕ):ℝ)/20))*((1+(((3:ℕ):ℝ)+1)/20)-(v-1))
              + ((4692425/10000000:ℝ)-4896444/10000000)*20*((1+(((3:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (241148740:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 7690212/10000000 + ((7053385/10000000:ℝ)-7690212/10000000)*(v-(2+((3:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-43/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 11/5-v),
      sq_nonneg (v-43/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_4 : ∀ v ∈ Set.Ico (2+((4:ℕ):ℝ)/20) (2+(((4:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (11/5:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 9/4 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(3646431/20000000)*(9/4-v) + 20*(4462871/20000000)*(v-11/5))
    (L3up := 10986123/10000000) hv2 hv4 (chord_4 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 4 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 4 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((4:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 5 := by
    rw [show (1+(((4:ℕ):ℝ)+1)/20) = 1+((5:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 5 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((4:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((4:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 4:ℝ) = 4692425/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 5:ℝ) = 4504728/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 4:ℝ) = 7053385/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 5:ℝ) = 6472381/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 5 = 231951587/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(3646431/20000000)*(9/4-v) + 20*(4462871/20000000)*(v-11/5)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((4692425/10000000 - ((4504728/10000000:ℝ)-4692425/10000000)*20*(1+((4:ℕ):ℝ)/20))*((1+(((4:ℕ):ℝ)+1)/20)-(v-1))
              + ((4504728/10000000:ℝ)-4692425/10000000)*20*((1+(((4:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (231951587:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 7053385/10000000 + ((6472381/10000000:ℝ)-7053385/10000000)*(v-(2+((4:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-11/5) (by push_cast at hvr; linarith : (0:ℝ) ≤ 9/4-v),
      sq_nonneg (v-11/5), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_5 : ∀ v ∈ Set.Ico (2+((5:ℕ):ℝ)/20) (2+(((5:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (9/4:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 23/10 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(4462871/20000000)*(23/10-v) + 20*(13118213/50000000)*(v-9/4))
    (L3up := 10986123/10000000) hv2 hv4 (chord_5 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 5 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 5 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((5:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 6 := by
    rw [show (1+(((5:ℕ):ℝ)+1)/20) = 1+((6:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 6 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((5:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((5:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 5:ℝ) = 4504728/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 6:ℝ) = 4331470/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 5:ℝ) = 6472381/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 6:ℝ) = 5941449/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 6 = 223115389/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(4462871/20000000)*(23/10-v) + 20*(13118213/50000000)*(v-9/4)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((4504728/10000000 - ((4331470/10000000:ℝ)-4504728/10000000)*20*(1+((5:ℕ):ℝ)/20))*((1+(((5:ℕ):ℝ)+1)/20)-(v-1))
              + ((4331470/10000000:ℝ)-4504728/10000000)*20*((1+(((5:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (223115389:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 6472381/10000000 + ((5941449/10000000:ℝ)-6472381/10000000)*(v-(2+((5:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-9/4) (by push_cast at hvr; linarith : (0:ℝ) ≤ 23/10-v),
      sq_nonneg (v-9/4), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_6 : ∀ v ∈ Set.Ico (2+((6:ℕ):ℝ)/20) (2+(((6:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (23/10:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 47/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(13118213/50000000)*(47/20-v) + 20*(30010459/100000000)*(v-23/10))
    (L3up := 10986123/10000000) hv2 hv4 (chord_6 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 6 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 6 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((6:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 7 := by
    rw [show (1+(((6:ℕ):ℝ)+1)/20) = 1+((7:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 7 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((6:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((6:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 6:ℝ) = 4331470/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 7:ℝ) = 4171045/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 6:ℝ) = 5941449/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 7:ℝ) = 5455558/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 7 = 214612874/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(13118213/50000000)*(47/20-v) + 20*(30010459/100000000)*(v-23/10)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((4331470/10000000 - ((4171045/10000000:ℝ)-4331470/10000000)*20*(1+((6:ℕ):ℝ)/20))*((1+(((6:ℕ):ℝ)+1)/20)-(v-1))
              + ((4171045/10000000:ℝ)-4331470/10000000)*20*((1+(((6:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (214612874:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 5941449/10000000 + ((5455558/10000000:ℝ)-5941449/10000000)*(v-(2+((6:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-23/10) (by push_cast at hvr; linarith : (0:ℝ) ≤ 47/20-v),
      sq_nonneg (v-23/10), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_7 : ∀ v ∈ Set.Ico (2+((7:ℕ):ℝ)/20) (2+(((7:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (47/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 12/5 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(30010459/100000000)*(12/5-v) + 20*(33647223/100000000)*(v-47/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_7 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 7 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 7 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((7:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 8 := by
    rw [show (1+(((7:ℕ):ℝ)+1)/20) = 1+((8:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 8 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((7:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((7:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 7:ℝ) = 4171045/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 8:ℝ) = 4022079/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 7:ℝ) = 5455558/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 8:ℝ) = 5010292/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 8 = 206419750/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(30010459/100000000)*(12/5-v) + 20*(33647223/100000000)*(v-47/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((4171045/10000000 - ((4022079/10000000:ℝ)-4171045/10000000)*20*(1+((7:ℕ):ℝ)/20))*((1+(((7:ℕ):ℝ)+1)/20)-(v-1))
              + ((4022079/10000000:ℝ)-4171045/10000000)*20*((1+(((7:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (206419750:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 5455558/10000000 + ((5010292/10000000:ℝ)-5455558/10000000)*(v-(2+((7:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-47/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 12/5-v),
      sq_nonneg (v-47/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_8 : ∀ v ∈ Set.Ico (2+((8:ℕ):ℝ)/20) (2+(((8:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (12/5:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 49/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(33647223/100000000)*(49/20-v) + 20*(7431271/20000000)*(v-12/5))
    (L3up := 10986123/10000000) hv2 hv4 (chord_8 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 8 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 8 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((8:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 9 := by
    rw [show (1+(((8:ℕ):ℝ)+1)/20) = 1+((9:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 9 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((8:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((8:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 8:ℝ) = 4022079/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 9:ℝ) = 3883387/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 8:ℝ) = 5010292/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 9:ℝ) = 4601766/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 9 = 198514284/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(33647223/100000000)*(49/20-v) + 20*(7431271/20000000)*(v-12/5)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((4022079/10000000 - ((3883387/10000000:ℝ)-4022079/10000000)*20*(1+((8:ℕ):ℝ)/20))*((1+(((8:ℕ):ℝ)+1)/20)-(v-1))
              + ((3883387/10000000:ℝ)-4022079/10000000)*20*((1+(((8:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (198514284:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 5010292/10000000 + ((4601766/10000000:ℝ)-5010292/10000000)*(v-(2+((8:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-12/5) (by push_cast at hvr; linarith : (0:ℝ) ≤ 49/20-v),
      sq_nonneg (v-12/5), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_9 : ∀ v ∈ Set.Ico (2+((9:ℕ):ℝ)/20) (2+(((9:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (49/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 5/2 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(7431271/20000000)*(5/2-v) + 20*(4054651/10000000)*(v-49/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_9 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 9 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 9 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((9:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 10 := by
    rw [show (1+(((9:ℕ):ℝ)+1)/20) = 1+((10:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 10 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((9:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((9:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 9:ℝ) = 3883387/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 10:ℝ) = 3753940/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 9:ℝ) = 4601766/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 10:ℝ) = 4226538/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 10 = 190876957/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(7431271/20000000)*(5/2-v) + 20*(4054651/10000000)*(v-49/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((3883387/10000000 - ((3753940/10000000:ℝ)-3883387/10000000)*20*(1+((9:ℕ):ℝ)/20))*((1+(((9:ℕ):ℝ)+1)/20)-(v-1))
              + ((3753940/10000000:ℝ)-3883387/10000000)*20*((1+(((9:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (190876957:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 4601766/10000000 + ((4226538/10000000:ℝ)-4601766/10000000)*(v-(2+((9:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-49/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 5/2-v),
      sq_nonneg (v-49/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_10 : ∀ v ∈ Set.Ico (2+((10:ℕ):ℝ)/20) (2+(((10:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (5/2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 51/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(4054651/10000000)*(51/20-v) + 20*(43825493/100000000)*(v-5/2))
    (L3up := 10986123/10000000) hv2 hv4 (chord_10 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 10 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 10 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((10:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 11 := by
    rw [show (1+(((10:ℕ):ℝ)+1)/20) = 1+((11:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 11 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((10:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((10:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 10:ℝ) = 3753940/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 11:ℝ) = 3632846/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 10:ℝ) = 4226538/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 11:ℝ) = 3881561/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 11 = 183490171/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(4054651/10000000)*(51/20-v) + 20*(43825493/100000000)*(v-5/2)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((3753940/10000000 - ((3632846/10000000:ℝ)-3753940/10000000)*20*(1+((10:ℕ):ℝ)/20))*((1+(((10:ℕ):ℝ)+1)/20)-(v-1))
              + ((3632846/10000000:ℝ)-3753940/10000000)*20*((1+(((10:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (183490171:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 4226538/10000000 + ((3881561/10000000:ℝ)-4226538/10000000)*(v-(2+((10:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-5/2) (by push_cast at hvr; linarith : (0:ℝ) ≤ 51/20-v),
      sq_nonneg (v-5/2), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_11 : ∀ v ∈ Set.Ico (2+((11:ℕ):ℝ)/20) (2+(((11:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (51/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 13/5 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(43825493/100000000)*(13/5-v) + 20*(23500181/50000000)*(v-51/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_11 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 11 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 11 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((11:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 12 := by
    rw [show (1+(((11:ℕ):ℝ)+1)/20) = 1+((12:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 12 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((11:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((11:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 11:ℝ) = 3632846/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 12:ℝ) = 3519319/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 11:ℝ) = 3881561/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 12:ℝ) = 3564122/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 12 = 176338006/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(43825493/100000000)*(13/5-v) + 20*(23500181/50000000)*(v-51/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((3632846/10000000 - ((3519319/10000000:ℝ)-3632846/10000000)*20*(1+((11:ℕ):ℝ)/20))*((1+(((11:ℕ):ℝ)+1)/20)-(v-1))
              + ((3519319/10000000:ℝ)-3632846/10000000)*20*((1+(((11:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (176338006:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 3881561/10000000 + ((3564122/10000000:ℝ)-3881561/10000000)*(v-(2+((11:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-51/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 13/5-v),
      sq_nonneg (v-51/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_12 : ∀ v ∈ Set.Ico (2+((12:ℕ):ℝ)/20) (2+(((12:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (13/5:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 53/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(23500181/50000000)*(53/20-v) + 20*(6259691/12500000)*(v-13/5))
    (L3up := 10986123/10000000) hv2 hv4 (chord_12 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 12 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 12 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((12:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 13 := by
    rw [show (1+(((12:ℕ):ℝ)+1)/20) = 1+((13:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 13 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((12:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((12:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 12:ℝ) = 3519319/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 13:ℝ) = 3412673/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 12:ℝ) = 3564122/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 13:ℝ) = 3271799/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 13 = 169406014/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(23500181/50000000)*(53/20-v) + 20*(6259691/12500000)*(v-13/5)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((3519319/10000000 - ((3412673/10000000:ℝ)-3519319/10000000)*20*(1+((12:ℕ):ℝ)/20))*((1+(((12:ℕ):ℝ)+1)/20)-(v-1))
              + ((3412673/10000000:ℝ)-3519319/10000000)*20*((1+(((12:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (169406014:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 3564122/10000000 + ((3271799/10000000:ℝ)-3564122/10000000)*(v-(2+((12:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-13/5) (by push_cast at hvr; linarith : (0:ℝ) ≤ 53/20-v),
      sq_nonneg (v-13/5), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_13 : ∀ v ∈ Set.Ico (2+((13:ℕ):ℝ)/20) (2+(((13:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (53/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 27/10 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(6259691/12500000)*(27/10-v) + 20*(2122513/4000000)*(v-53/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_13 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 13 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 13 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((13:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 14 := by
    rw [show (1+(((13:ℕ):ℝ)+1)/20) = 1+((14:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 14 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((13:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((13:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 13:ℝ) = 3412673/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 14:ℝ) = 3312300/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 13:ℝ) = 3271799/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 14:ℝ) = 3002427/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 14 = 162681041/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(6259691/12500000)*(27/10-v) + 20*(2122513/4000000)*(v-53/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((3412673/10000000 - ((3312300/10000000:ℝ)-3412673/10000000)*20*(1+((13:ℕ):ℝ)/20))*((1+(((13:ℕ):ℝ)+1)/20)-(v-1))
              + ((3312300/10000000:ℝ)-3412673/10000000)*20*((1+(((13:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (162681041:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 3271799/10000000 + ((3002427/10000000:ℝ)-3271799/10000000)*(v-(2+((13:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-53/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 27/10-v),
      sq_nonneg (v-53/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_14 : ∀ v ∈ Set.Ico (2+((14:ℕ):ℝ)/20) (2+(((14:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (27/10:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 11/4 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(2122513/4000000)*(11/4-v) + 20*(27980789/50000000)*(v-27/10))
    (L3up := 10986123/10000000) hv2 hv4 (chord_14 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 14 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 14 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((14:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 15 := by
    rw [show (1+(((14:ℕ):ℝ)+1)/20) = 1+((15:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 15 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((14:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((14:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 14:ℝ) = 3312300/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 15:ℝ) = 3217663/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 14:ℝ) = 3002427/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 15:ℝ) = 2754065/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 15 = 156151078/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(2122513/4000000)*(11/4-v) + 20*(27980789/50000000)*(v-27/10)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((3312300/10000000 - ((3217663/10000000:ℝ)-3312300/10000000)*20*(1+((14:ℕ):ℝ)/20))*((1+(((14:ℕ):ℝ)+1)/20)-(v-1))
              + ((3217663/10000000:ℝ)-3312300/10000000)*20*((1+(((14:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (156151078:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 3002427/10000000 + ((2754065/10000000:ℝ)-3002427/10000000)*(v-(2+((14:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-27/10) (by push_cast at hvr; linarith : (0:ℝ) ≤ 11/4-v),
      sq_nonneg (v-27/10), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_15 : ∀ v ∈ Set.Ico (2+((15:ℕ):ℝ)/20) (2+(((15:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (11/4:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 14/5 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(27980789/50000000)*(14/5-v) + 20*(29389333/50000000)*(v-11/4))
    (L3up := 10986123/10000000) hv2 hv4 (chord_15 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 15 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 15 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((15:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 16 := by
    rw [show (1+(((15:ℕ):ℝ)+1)/20) = 1+((16:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 16 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((15:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((15:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 15:ℝ) = 3217663/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 16:ℝ) = 3128284/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 15:ℝ) = 2754065/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 16:ℝ) = 2524966/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 16 = 149805131/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(27980789/50000000)*(14/5-v) + 20*(29389333/50000000)*(v-11/4)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((3217663/10000000 - ((3128284/10000000:ℝ)-3217663/10000000)*20*(1+((15:ℕ):ℝ)/20))*((1+(((15:ℕ):ℝ)+1)/20)-(v-1))
              + ((3128284/10000000:ℝ)-3217663/10000000)*20*((1+(((15:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (149805131:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 2754065/10000000 + ((2524966/10000000:ℝ)-2754065/10000000)*(v-(2+((15:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-11/4) (by push_cast at hvr; linarith : (0:ℝ) ≤ 14/5-v),
      sq_nonneg (v-11/4), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_16 : ∀ v ∈ Set.Ico (2+((16:ℕ):ℝ)/20) (2+(((16:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (14/5:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 57/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(29389333/50000000)*(57/20-v) + 20*(61518563/100000000)*(v-14/5))
    (L3up := 10986123/10000000) hv2 hv4 (chord_16 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 16 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 16 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((16:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 17 := by
    rw [show (1+(((16:ℕ):ℝ)+1)/20) = 1+((17:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 17 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((16:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((16:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 16:ℝ) = 3128284/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 17:ℝ) = 3043736/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 16:ℝ) = 2524966/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 17:ℝ) = 2313556/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 17 = 143633111/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(29389333/50000000)*(57/20-v) + 20*(61518563/100000000)*(v-14/5)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((3128284/10000000 - ((3043736/10000000:ℝ)-3128284/10000000)*20*(1+((16:ℕ):ℝ)/20))*((1+(((16:ℕ):ℝ)+1)/20)-(v-1))
              + ((3043736/10000000:ℝ)-3128284/10000000)*20*((1+(((16:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (143633111:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 2524966/10000000 + ((2313556/10000000:ℝ)-2524966/10000000)*(v-(2+((16:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-14/5) (by push_cast at hvr; linarith : (0:ℝ) ≤ 57/20-v),
      sq_nonneg (v-14/5), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_17 : ∀ v ∈ Set.Ico (2+((17:ℕ):ℝ)/20) (2+(((17:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (57/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 29/10 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(61518563/100000000)*(29/10-v) + 20*(16046347/25000000)*(v-57/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_17 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 17 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 17 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((17:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 18 := by
    rw [show (1+(((17:ℕ):ℝ)+1)/20) = 1+((18:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 18 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((17:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((17:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 17:ℝ) = 3043736/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 18:ℝ) = 2963637/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 17:ℝ) = 2313556/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 18:ℝ) = 2118415/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 18 = 137625738/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(61518563/100000000)*(29/10-v) + 20*(16046347/25000000)*(v-57/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((3043736/10000000 - ((2963637/10000000:ℝ)-3043736/10000000)*20*(1+((17:ℕ):ℝ)/20))*((1+(((17:ℕ):ℝ)+1)/20)-(v-1))
              + ((2963637/10000000:ℝ)-3043736/10000000)*20*((1+(((17:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (137625738:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 2313556/10000000 + ((2118415/10000000:ℝ)-2313556/10000000)*(v-(2+((17:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-57/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 29/10-v),
      sq_nonneg (v-57/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_18 : ∀ v ∈ Set.Ico (2+((18:ℕ):ℝ)/20) (2+(((18:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (29/10:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 59/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(16046347/25000000)*(59/20-v) + 20*(66782937/100000000)*(v-29/10))
    (L3up := 10986123/10000000) hv2 hv4 (chord_18 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 18 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 18 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((18:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 19 := by
    rw [show (1+(((18:ℕ):ℝ)+1)/20) = 1+((19:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 19 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((18:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((18:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 18:ℝ) = 2963637/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 19:ℝ) = 2887647/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 18:ℝ) = 2118415/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 19:ℝ) = 1938256/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 19 = 131774454/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(16046347/25000000)*(59/20-v) + 20*(66782937/100000000)*(v-29/10)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2963637/10000000 - ((2887647/10000000:ℝ)-2963637/10000000)*20*(1+((18:ℕ):ℝ)/20))*((1+(((18:ℕ):ℝ)+1)/20)-(v-1))
              + ((2887647/10000000:ℝ)-2963637/10000000)*20*((1+(((18:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (131774454:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 2118415/10000000 + ((1938256/10000000:ℝ)-2118415/10000000)*(v-(2+((18:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-29/10) (by push_cast at hvr; linarith : (0:ℝ) ≤ 59/20-v),
      sq_nonneg (v-29/10), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_19 : ∀ v ∈ Set.Ico (2+((19:ℕ):ℝ)/20) (2+(((19:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (59/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 3 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(66782937/100000000)*(3-v) + 20*(34657359/50000000)*(v-59/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_19 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 19 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 19 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((19:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 20 := by
    rw [show (1+(((19:ℕ):ℝ)+1)/20) = 1+((20:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 20 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((19:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((19:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 19:ℝ) = 2887647/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 20:ℝ) = 2815455/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 19:ℝ) = 1938256/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 20:ℝ) = 1771915/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 20 = 126071352/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(66782937/100000000)*(3-v) + 20*(34657359/50000000)*(v-59/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2887647/10000000 - ((2815455/10000000:ℝ)-2887647/10000000)*20*(1+((19:ℕ):ℝ)/20))*((1+(((19:ℕ):ℝ)+1)/20)-(v-1))
              + ((2815455/10000000:ℝ)-2887647/10000000)*20*((1+(((19:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (126071352:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 1938256/10000000 + ((1771915/10000000:ℝ)-1938256/10000000)*(v-(2+((19:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-59/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 3-v),
      sq_nonneg (v-59/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_20 : ∀ v ∈ Set.Ico (2+((20:ℕ):ℝ)/20) (2+(((20:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (3:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 61/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(34657359/50000000)*(61/20-v) + 20*(71783979/100000000)*(v-3))
    (L3up := 10986123/10000000) hv2 hv4 (chord_20 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 20 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 20 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((20:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 21 := by
    rw [show (1+(((20:ℕ):ℝ)+1)/20) = 1+((21:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 21 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((20:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((20:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 20:ℝ) = 2815455/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 21:ℝ) = 2746786/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 20:ℝ) = 1771915/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 21:ℝ) = 1618331/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 21 = 120509111/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(34657359/50000000)*(61/20-v) + 20*(71783979/100000000)*(v-3)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2815455/10000000 - ((2746786/10000000:ℝ)-2815455/10000000)*20*(1+((20:ℕ):ℝ)/20))*((1+(((20:ℕ):ℝ)+1)/20)-(v-1))
              + ((2746786/10000000:ℝ)-2815455/10000000)*20*((1+(((20:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (120509111:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 1771915/10000000 + ((1618331/10000000:ℝ)-1771915/10000000)*(v-(2+((20:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-3) (by push_cast at hvr; linarith : (0:ℝ) ≤ 61/20-v),
      sq_nonneg (v-3), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_21 : ∀ v ∈ Set.Ico (2+((21:ℕ):ℝ)/20) (2+(((21:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (61/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 31/10 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(71783979/100000000)*(31/10-v) + 20*(37096867/50000000)*(v-61/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_21 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 21 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 21 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((21:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 22 := by
    rw [show (1+(((21:ℕ):ℝ)+1)/20) = 1+((22:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 22 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((21:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((21:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 21:ℝ) = 2746786/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 22:ℝ) = 2681386/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 21:ℝ) = 1618331/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 22:ℝ) = 1476541/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 22 = 115080939/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(71783979/100000000)*(31/10-v) + 20*(37096867/50000000)*(v-61/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2746786/10000000 - ((2681386/10000000:ℝ)-2746786/10000000)*20*(1+((21:ℕ):ℝ)/20))*((1+(((21:ℕ):ℝ)+1)/20)-(v-1))
              + ((2681386/10000000:ℝ)-2746786/10000000)*20*((1+(((21:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (115080939:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 1618331/10000000 + ((1476541/10000000:ℝ)-1618331/10000000)*(v-(2+((21:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-61/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 31/10-v),
      sq_nonneg (v-61/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_22 : ∀ v ∈ Set.Ico (2+((22:ℕ):ℝ)/20) (2+(((22:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (31/10:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 63/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(37096867/50000000)*(63/20-v) + 20*(2392087/3125000)*(v-31/10))
    (L3up := 10986123/10000000) hv2 hv4 (chord_22 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 22 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 22 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((22:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 23 := by
    rw [show (1+(((22:ℕ):ℝ)+1)/20) = 1+((23:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 23 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((22:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((22:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 22:ℝ) = 2681386/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 23:ℝ) = 2619028/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 22:ℝ) = 1476541/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 23:ℝ) = 1345668/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 23 = 109780525/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(37096867/50000000)*(63/20-v) + 20*(2392087/3125000)*(v-31/10)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2681386/10000000 - ((2619028/10000000:ℝ)-2681386/10000000)*20*(1+((22:ℕ):ℝ)/20))*((1+(((22:ℕ):ℝ)+1)/20)-(v-1))
              + ((2619028/10000000:ℝ)-2681386/10000000)*20*((1+(((22:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (109780525:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 1476541/10000000 + ((1345668/10000000:ℝ)-1476541/10000000)*(v-(2+((22:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-31/10) (by push_cast at hvr; linarith : (0:ℝ) ≤ 63/20-v),
      sq_nonneg (v-31/10), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_23 : ∀ v ∈ Set.Ico (2+((23:ℕ):ℝ)/20) (2+(((23:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (63/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 16/5 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(2392087/3125000)*(16/5-v) + 20*(15769147/20000000)*(v-63/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_23 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 23 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 23 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((23:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 24 := by
    rw [show (1+(((23:ℕ):ℝ)+1)/20) = 1+((24:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 24 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((23:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((23:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 23:ℝ) = 2619028/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 24:ℝ) = 2559505/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 23:ℝ) = 1345668/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 24:ℝ) = 1224908/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 24 = 104601992/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(2392087/3125000)*(16/5-v) + 20*(15769147/20000000)*(v-63/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2619028/10000000 - ((2559505/10000000:ℝ)-2619028/10000000)*20*(1+((23:ℕ):ℝ)/20))*((1+(((23:ℕ):ℝ)+1)/20)-(v-1))
              + ((2559505/10000000:ℝ)-2619028/10000000)*20*((1+(((23:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (104601992:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 1345668/10000000 + ((1224908/10000000:ℝ)-1345668/10000000)*(v-(2+((23:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-63/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 16/5-v),
      sq_nonneg (v-63/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_24 : ∀ v ∈ Set.Ico (2+((24:ℕ):ℝ)/20) (2+(((24:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (16/5:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 13/4 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(15769147/20000000)*(13/4-v) + 20*(81093021/100000000)*(v-16/5))
    (L3up := 10986123/10000000) hv2 hv4 (chord_24 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 24 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 24 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((24:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 25 := by
    rw [show (1+(((24:ℕ):ℝ)+1)/20) = 1+((25:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 25 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((24:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((24:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 24:ℝ) = 2559505/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 25:ℝ) = 2502627/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 24:ℝ) = 1224908/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 25:ℝ) = 1113528/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 25 = 99539860/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(15769147/20000000)*(13/4-v) + 20*(81093021/100000000)*(v-16/5)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2559505/10000000 - ((2502627/10000000:ℝ)-2559505/10000000)*20*(1+((24:ℕ):ℝ)/20))*((1+(((24:ℕ):ℝ)+1)/20)-(v-1))
              + ((2502627/10000000:ℝ)-2559505/10000000)*20*((1+(((24:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (99539860:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 1224908/10000000 + ((1113528/10000000:ℝ)-1224908/10000000)*(v-(2+((24:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-16/5) (by push_cast at hvr; linarith : (0:ℝ) ≤ 13/4-v),
      sq_nonneg (v-16/5), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_25 : ∀ v ∈ Set.Ico (2+((25:ℕ):ℝ)/20) (2+(((25:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (13/4:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 33/10 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(81093021/100000000)*(33/10-v) + 20*(2602841/3125000)*(v-13/4))
    (L3up := 10986123/10000000) hv2 hv4 (chord_25 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 25 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 25 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((25:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 26 := by
    rw [show (1+(((25:ℕ):ℝ)+1)/20) = 1+((26:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 26 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((25:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((25:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 25:ℝ) = 2502627/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 26:ℝ) = 2448222/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 25:ℝ) = 1113528/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 26:ℝ) = 1010856/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 26 = 94589011/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(81093021/100000000)*(33/10-v) + 20*(2602841/3125000)*(v-13/4)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2502627/10000000 - ((2448222/10000000:ℝ)-2502627/10000000)*20*(1+((25:ℕ):ℝ)/20))*((1+(((25:ℕ):ℝ)+1)/20)-(v-1))
              + ((2448222/10000000:ℝ)-2502627/10000000)*20*((1+(((25:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (94589011:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 1113528/10000000 + ((1010856/10000000:ℝ)-1113528/10000000)*(v-(2+((25:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-13/4) (by push_cast at hvr; linarith : (0:ℝ) ≤ 33/10-v),
      sq_nonneg (v-13/4), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_26 : ∀ v ∈ Set.Ico (2+((26:ℕ):ℝ)/20) (2+(((26:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (33/10:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 67/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(2602841/3125000)*(67/20-v) + 20*(21360383/25000000)*(v-33/10))
    (L3up := 10986123/10000000) hv2 hv4 (chord_26 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 26 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 26 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((26:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 27 := by
    rw [show (1+(((26:ℕ):ℝ)+1)/20) = 1+((27:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 27 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((26:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((26:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 26:ℝ) = 2448222/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 27:ℝ) = 2396132/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 26:ℝ) = 1010856/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 27:ℝ) = 916278/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 27 = 89744657/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(2602841/3125000)*(67/20-v) + 20*(21360383/25000000)*(v-33/10)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2448222/10000000 - ((2396132/10000000:ℝ)-2448222/10000000)*20*(1+((26:ℕ):ℝ)/20))*((1+(((26:ℕ):ℝ)+1)/20)-(v-1))
              + ((2396132/10000000:ℝ)-2448222/10000000)*20*((1+(((26:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (89744657:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 1010856/10000000 + ((916278/10000000:ℝ)-1010856/10000000)*(v-(2+((26:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-33/10) (by push_cast at hvr; linarith : (0:ℝ) ≤ 67/20-v),
      sq_nonneg (v-33/10), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_27 : ∀ v ∈ Set.Ico (2+((27:ℕ):ℝ)/20) (2+(((27:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (67/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 17/5 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(21360383/25000000)*(17/5-v) + 20*(87546873/100000000)*(v-67/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_27 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 27 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 27 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((27:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 28 := by
    rw [show (1+(((27:ℕ):ℝ)+1)/20) = 1+((28:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 28 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((27:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((27:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 27:ℝ) = 2396132/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 28:ℝ) = 2346213/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 27:ℝ) = 916278/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 28:ℝ) = 829227/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 28 = 85002312/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(21360383/25000000)*(17/5-v) + 20*(87546873/100000000)*(v-67/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2396132/10000000 - ((2346213/10000000:ℝ)-2396132/10000000)*20*(1+((27:ℕ):ℝ)/20))*((1+(((27:ℕ):ℝ)+1)/20)-(v-1))
              + ((2346213/10000000:ℝ)-2396132/10000000)*20*((1+(((27:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (85002312:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 916278/10000000 + ((829227/10000000:ℝ)-916278/10000000)*(v-(2+((27:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-67/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 17/5-v),
      sq_nonneg (v-67/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_28 : ∀ v ∈ Set.Ico (2+((28:ℕ):ℝ)/20) (2+(((28:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (17/5:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 69/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(87546873/100000000)*(69/20-v) + 20*(44804401/50000000)*(v-17/5))
    (L3up := 10986123/10000000) hv2 hv4 (chord_28 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 28 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 28 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((28:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 29 := by
    rw [show (1+(((28:ℕ):ℝ)+1)/20) = 1+((29:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 29 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((28:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((28:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 28:ℝ) = 2346213/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 29:ℝ) = 2298331/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 28:ℝ) = 829227/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 29:ℝ) = 749182/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 29 = 80357768/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(87546873/100000000)*(69/20-v) + 20*(44804401/50000000)*(v-17/5)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2346213/10000000 - ((2298331/10000000:ℝ)-2346213/10000000)*20*(1+((28:ℕ):ℝ)/20))*((1+(((28:ℕ):ℝ)+1)/20)-(v-1))
              + ((2298331/10000000:ℝ)-2346213/10000000)*20*((1+(((28:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (80357768:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 829227/10000000 + ((749182/10000000:ℝ)-829227/10000000)*(v-(2+((28:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-17/5) (by push_cast at hvr; linarith : (0:ℝ) ≤ 69/20-v),
      sq_nonneg (v-17/5), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_29 : ∀ v ∈ Set.Ico (2+((29:ℕ):ℝ)/20) (2+(((29:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (69/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 7/2 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(44804401/50000000)*(7/2-v) + 20*(91629073/100000000)*(v-69/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_29 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 29 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 29 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((29:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 30 := by
    rw [show (1+(((29:ℕ):ℝ)+1)/20) = 1+((30:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 30 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((29:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((29:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 29:ℝ) = 2298331/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 30:ℝ) = 2252364/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 29:ℝ) = 749182/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 30:ℝ) = 675666/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 30 = 75807073/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(44804401/50000000)*(7/2-v) + 20*(91629073/100000000)*(v-69/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2298331/10000000 - ((2252364/10000000:ℝ)-2298331/10000000)*20*(1+((29:ℕ):ℝ)/20))*((1+(((29:ℕ):ℝ)+1)/20)-(v-1))
              + ((2252364/10000000:ℝ)-2298331/10000000)*20*((1+(((29:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (75807073:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 749182/10000000 + ((675666/10000000:ℝ)-749182/10000000)*(v-(2+((29:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-69/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 7/2-v),
      sq_nonneg (v-69/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_30 : ∀ v ∈ Set.Ico (2+((30:ℕ):ℝ)/20) (2+(((30:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (7/2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 71/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(91629073/100000000)*(71/20-v) + 20*(18721867/20000000)*(v-7/2))
    (L3up := 10986123/10000000) hv2 hv4 (chord_30 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 30 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 30 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((30:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 31 := by
    rw [show (1+(((30:ℕ):ℝ)+1)/20) = 1+((31:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 31 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((30:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((30:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 30:ℝ) = 2252364/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 31:ℝ) = 2208200/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 30:ℝ) = 675666/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 31:ℝ) = 608236/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 31 = 71346509/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(91629073/100000000)*(71/20-v) + 20*(18721867/20000000)*(v-7/2)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2252364/10000000 - ((2208200/10000000:ℝ)-2252364/10000000)*20*(1+((30:ℕ):ℝ)/20))*((1+(((30:ℕ):ℝ)+1)/20)-(v-1))
              + ((2208200/10000000:ℝ)-2252364/10000000)*20*((1+(((30:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (71346509:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 675666/10000000 + ((608236/10000000:ℝ)-675666/10000000)*(v-(2+((30:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-7/2) (by push_cast at hvr; linarith : (0:ℝ) ≤ 71/20-v),
      sq_nonneg (v-7/2), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_31 : ∀ v ∈ Set.Ico (2+((31:ℕ):ℝ)/20) (2+(((31:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (71/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 18/5 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(18721867/20000000)*(18/5-v) + 20*(11943893/12500000)*(v-71/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_31 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 31 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 31 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((31:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 32 := by
    rw [show (1+(((31:ℕ):ℝ)+1)/20) = 1+((32:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 32 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((31:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((31:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 31:ℝ) = 2208200/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 32:ℝ) = 2165735/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 31:ℝ) = 608236/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 32:ℝ) = 546485/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 32 = 66972574/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(18721867/20000000)*(18/5-v) + 20*(11943893/12500000)*(v-71/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2208200/10000000 - ((2165735/10000000:ℝ)-2208200/10000000)*20*(1+((31:ℕ):ℝ)/20))*((1+(((31:ℕ):ℝ)+1)/20)-(v-1))
              + ((2165735/10000000:ℝ)-2208200/10000000)*20*((1+(((31:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (66972574:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 608236/10000000 + ((546485/10000000:ℝ)-608236/10000000)*(v-(2+((31:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-71/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 18/5-v),
      sq_nonneg (v-71/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_32 : ∀ v ∈ Set.Ico (2+((32:ℕ):ℝ)/20) (2+(((32:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (18/5:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 73/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(11943893/12500000)*(73/20-v) + 20*(97455963/100000000)*(v-18/5))
    (L3up := 10986123/10000000) hv2 hv4 (chord_32 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 32 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 32 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((32:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 33 := by
    rw [show (1+(((32:ℕ):ℝ)+1)/20) = 1+((33:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 33 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((32:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((32:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 32:ℝ) = 2165735/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 33:ℝ) = 2124872/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 32:ℝ) = 546485/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 33:ℝ) = 490037/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 33 = 62681967/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(11943893/12500000)*(73/20-v) + 20*(97455963/100000000)*(v-18/5)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2165735/10000000 - ((2124872/10000000:ℝ)-2165735/10000000)*20*(1+((32:ℕ):ℝ)/20))*((1+(((32:ℕ):ℝ)+1)/20)-(v-1))
              + ((2124872/10000000:ℝ)-2165735/10000000)*20*((1+(((32:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (62681967:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 546485/10000000 + ((490037/10000000:ℝ)-546485/10000000)*(v-(2+((32:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-18/5) (by push_cast at hvr; linarith : (0:ℝ) ≤ 73/20-v),
      sq_nonneg (v-18/5), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_33 : ∀ v ∈ Set.Ico (2+((33:ℕ):ℝ)/20) (2+(((33:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (73/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 37/10 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(97455963/100000000)*(37/10-v) + 20*(99325177/100000000)*(v-73/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_33 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 33 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 33 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((33:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 34 := by
    rw [show (1+(((33:ℕ):ℝ)+1)/20) = 1+((34:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 34 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((33:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((33:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 33:ℝ) = 2124872/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 34:ℝ) = 2085523/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 33:ℝ) = 490037/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 34:ℝ) = 438544/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 34 = 58471572/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(97455963/100000000)*(37/10-v) + 20*(99325177/100000000)*(v-73/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2124872/10000000 - ((2085523/10000000:ℝ)-2124872/10000000)*20*(1+((33:ℕ):ℝ)/20))*((1+(((33:ℕ):ℝ)+1)/20)-(v-1))
              + ((2085523/10000000:ℝ)-2124872/10000000)*20*((1+(((33:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (58471572:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 490037/10000000 + ((438544/10000000:ℝ)-490037/10000000)*(v-(2+((33:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-73/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 37/10-v),
      sq_nonneg (v-73/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_34 : ∀ v ∈ Set.Ico (2+((34:ℕ):ℝ)/20) (2+(((34:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (37/10:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 15/4 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(99325177/100000000)*(15/4-v) + 20*(101160091/100000000)*(v-37/10))
    (L3up := 10986123/10000000) hv2 hv4 (chord_34 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 34 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 34 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((34:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 35 := by
    rw [show (1+(((34:ℕ):ℝ)+1)/20) = 1+((35:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 35 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((34:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((34:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 34:ℝ) = 2085523/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 35:ℝ) = 2047604/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 34:ℝ) = 438544/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 35:ℝ) = 391682/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 35 = 54338445/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(99325177/100000000)*(15/4-v) + 20*(101160091/100000000)*(v-37/10)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2085523/10000000 - ((2047604/10000000:ℝ)-2085523/10000000)*20*(1+((34:ℕ):ℝ)/20))*((1+(((34:ℕ):ℝ)+1)/20)-(v-1))
              + ((2047604/10000000:ℝ)-2085523/10000000)*20*((1+(((34:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (54338445:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 438544/10000000 + ((391682/10000000:ℝ)-438544/10000000)*(v-(2+((34:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-37/10) (by push_cast at hvr; linarith : (0:ℝ) ≤ 15/4-v),
      sq_nonneg (v-37/10), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_35 : ∀ v ∈ Set.Ico (2+((35:ℕ):ℝ)/20) (2+(((35:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (15/4:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 19/5 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(101160091/100000000)*(19/5-v) + 20*(102961941/100000000)*(v-15/4))
    (L3up := 10986123/10000000) hv2 hv4 (chord_35 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 35 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 35 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((35:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 36 := by
    rw [show (1+(((35:ℕ):ℝ)+1)/20) = 1+((36:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 36 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((35:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((35:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 35:ℝ) = 2047604/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 36:ℝ) = 2011040/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 35:ℝ) = 391682/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 36:ℝ) = 349155/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 36 = 50279801/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(101160091/100000000)*(19/5-v) + 20*(102961941/100000000)*(v-15/4)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2047604/10000000 - ((2011040/10000000:ℝ)-2047604/10000000)*20*(1+((35:ℕ):ℝ)/20))*((1+(((35:ℕ):ℝ)+1)/20)-(v-1))
              + ((2011040/10000000:ℝ)-2047604/10000000)*20*((1+(((35:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (50279801:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 391682/10000000 + ((349155/10000000:ℝ)-391682/10000000)*(v-(2+((35:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-15/4) (by push_cast at hvr; linarith : (0:ℝ) ≤ 19/5-v),
      sq_nonneg (v-15/4), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_36 : ∀ v ∈ Set.Ico (2+((36:ℕ):ℝ)/20) (2+(((36:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (19/5:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 77/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(102961941/100000000)*(77/20-v) + 20*(104731899/100000000)*(v-19/5))
    (L3up := 10986123/10000000) hv2 hv4 (chord_36 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 36 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 36 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((36:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 37 := by
    rw [show (1+(((36:ℕ):ℝ)+1)/20) = 1+((37:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 37 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((36:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((36:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 36:ℝ) = 2011040/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 37:ℝ) = 1975758/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 36:ℝ) = 349155/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 37:ℝ) = 310684/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 37 = 46293003/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(102961941/100000000)*(77/20-v) + 20*(104731899/100000000)*(v-19/5)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((2011040/10000000 - ((1975758/10000000:ℝ)-2011040/10000000)*20*(1+((36:ℕ):ℝ)/20))*((1+(((36:ℕ):ℝ)+1)/20)-(v-1))
              + ((1975758/10000000:ℝ)-2011040/10000000)*20*((1+(((36:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (46293003:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 349155/10000000 + ((310684/10000000:ℝ)-349155/10000000)*(v-(2+((36:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-19/5) (by push_cast at hvr; linarith : (0:ℝ) ≤ 77/20-v),
      sq_nonneg (v-19/5), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_37 : ∀ v ∈ Set.Ico (2+((37:ℕ):ℝ)/20) (2+(((37:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (77/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 39/10 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(104731899/100000000)*(39/10-v) + 20*(106471073/100000000)*(v-77/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_37 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 37 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 37 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((37:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 38 := by
    rw [show (1+(((37:ℕ):ℝ)+1)/20) = 1+((38:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 38 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((37:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((37:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 37:ℝ) = 1975758/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 38:ℝ) = 1941694/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 37:ℝ) = 310684/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 38:ℝ) = 276011/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 38 = 42375551/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(104731899/100000000)*(39/10-v) + 20*(106471073/100000000)*(v-77/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((1975758/10000000 - ((1941694/10000000:ℝ)-1975758/10000000)*20*(1+((37:ℕ):ℝ)/20))*((1+(((37:ℕ):ℝ)+1)/20)-(v-1))
              + ((1941694/10000000:ℝ)-1975758/10000000)*20*((1+(((37:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (42375551:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 310684/10000000 + ((276011/10000000:ℝ)-310684/10000000)*(v-(2+((37:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-77/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 39/10-v),
      sq_nonneg (v-77/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_38 : ∀ v ∈ Set.Ico (2+((38:ℕ):ℝ)/20) (2+(((38:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (39/10:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 79/20 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(106471073/100000000)*(79/20-v) + 20*(27045129/25000000)*(v-39/10))
    (L3up := 10986123/10000000) hv2 hv4 (chord_38 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 38 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 38 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((38:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 39 := by
    rw [show (1+(((38:ℕ):ℝ)+1)/20) = 1+((39:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 39 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((38:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((38:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 38:ℝ) = 1941694/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 39:ℝ) = 1908783/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 38:ℝ) = 276011/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 39:ℝ) = 244898/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 39 = 38525074/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(106471073/100000000)*(79/20-v) + 20*(27045129/25000000)*(v-39/10)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((1941694/10000000 - ((1908783/10000000:ℝ)-1941694/10000000)*20*(1+((38:ℕ):ℝ)/20))*((1+(((38:ℕ):ℝ)+1)/20)-(v-1))
              + ((1908783/10000000:ℝ)-1941694/10000000)*20*((1+(((38:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (38525074:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 276011/10000000 + ((244898/10000000:ℝ)-276011/10000000)*(v-(2+((38:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-39/10) (by push_cast at hvr; linarith : (0:ℝ) ≤ 79/20-v),
      sq_nonneg (v-39/10), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_39 : ∀ v ∈ Set.Ico (2+((39:ℕ):ℝ)/20) (2+(((39:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hv2 : (2:ℝ) ≤ v := by push_cast at hvl; linarith
  have hv4 : v ≤ 4 := by push_cast at hvr; linarith
  have hvl' : (79/20:ℝ) ≤ v := by push_cast at hvl; linarith
  have hvap : v ≤ 4 := by push_cast at hvr; linarith
  have hmaj := fseq2_upper_of_log_lower (v:=v)
    (clog := 20*(27045129/25000000)*(4-v) + 20*(27465307/25000000)*(v-79/20))
    (L3up := 10986123/10000000) hv2 hv4 (chord_39 v hvl' hvap) L3up_c
  have hE := Ebar_panel_eq 39 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 39 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((39:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 40 := by
    rw [show (1+(((39:ℕ):ℝ)+1)/20) = 1+((40:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 40 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((39:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((39:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 39:ℝ) = 1908783/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 40:ℝ) = 1876970/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 39:ℝ) = 244898/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 40:ℝ) = 217122/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 40 = 34739321/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1]
  have key : (v - 3*(20*(27045129/25000000)*(4-v) + 20*(27465307/25000000)*(v-79/20)) + 3*(10986123/10000000) - 4)/v
      + (1/v)*((1908783/10000000 - ((1876970/10000000:ℝ)-1908783/10000000)*20*(1+((39:ℕ):ℝ)/20))*((1+(((39:ℕ):ℝ)+1)/20)-(v-1))
              + ((1876970/10000000:ℝ)-1908783/10000000)*20*((1+(((39:ℕ):ℝ)+1)/20)^2-(v-1)^2)/2
              + (34739321:ℝ)/400000000 + (1/10000)/(2*12^2))
      ≤ 244898/10000000 + ((217122/10000000:ℝ)-244898/10000000)*(v-(2+((39:ℕ):ℝ)/20))*20 := by
    rw [one_div_mul_eq_div, ← add_div, div_le_iff₀ hv0]
    push_cast
    nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v-79/20) (by push_cast at hvr; linarith : (0:ℝ) ≤ 4-v),
      sq_nonneg (v-79/20), hv0, hvl', hv4]
  linarith [hmaj, key]

theorem hptE_40 : ∀ v ∈ Set.Ico (2+((40:ℕ):ℝ)/20) (2+(((40:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 40 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 40 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((40:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 41 := by
    rw [show (1+(((40:ℕ):ℝ)+1)/20) = 1+((41:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 41 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((40:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((40:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 40:ℝ) = 1876970/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 41:ℝ) = 1689103/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 40:ℝ) = 217122/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 41:ℝ) = 192429/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 41 = 31173248/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+40/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+41/20) - v), hv0]

theorem hptE_41 : ∀ v ∈ Set.Ico (2+((41:ℕ):ℝ)/20) (2+(((41:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 41 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 41 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((41:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 42 := by
    rw [show (1+(((41:ℕ):ℝ)+1)/20) = 1+((42:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 42 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((41:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((41:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 41:ℝ) = 1689103/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 42:ℝ) = 1520341/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 41:ℝ) = 192429/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 42:ℝ) = 170512/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 42 = 27963804/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+41/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+42/20) - v), hv0]

theorem hptE_42 : ∀ v ∈ Set.Ico (2+((42:ℕ):ℝ)/20) (2+(((42:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 42 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 42 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((42:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 43 := by
    rw [show (1+(((42:ℕ):ℝ)+1)/20) = 1+((43:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 43 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((42:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((42:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 42:ℝ) = 1520341/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 43:ℝ) = 1368592/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 42:ℝ) = 170512/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 43:ℝ) = 151055/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 43 = 25074871/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+42/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+43/20) - v), hv0]

theorem hptE_43 : ∀ v ∈ Set.Ico (2+((43:ℕ):ℝ)/20) (2+(((43:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 43 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 43 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((43:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 44 := by
    rw [show (1+(((43:ℕ):ℝ)+1)/20) = 1+((44:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 44 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((43:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((43:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 43:ℝ) = 1368592/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 44:ℝ) = 1232024/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 43:ℝ) = 151055/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 44:ℝ) = 133777/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 44 = 22474255/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+43/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+44/20) - v), hv0]

theorem hptE_44 : ∀ v ∈ Set.Ico (2+((44:ℕ):ℝ)/20) (2+(((44:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 44 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 44 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((44:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 45 := by
    rw [show (1+(((44:ℕ):ℝ)+1)/20) = 1+((45:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 45 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((44:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((44:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 44:ℝ) = 1232024/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 45:ℝ) = 1109025/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 44:ℝ) = 133777/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 45:ℝ) = 118432/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 45 = 20133206/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+44/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+45/20) - v), hv0]

theorem hptE_45 : ∀ v ∈ Set.Ico (2+((45:ℕ):ℝ)/20) (2+(((45:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 45 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 45 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((45:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 46 := by
    rw [show (1+(((45:ℕ):ℝ)+1)/20) = 1+((46:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 46 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((45:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((45:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 45:ℝ) = 1109025/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 46:ℝ) = 998178/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 45:ℝ) = 118432/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 46:ℝ) = 104804/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 46 = 18026003/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+45/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+46/20) - v), hv0]

theorem hptE_46 : ∀ v ∈ Set.Ico (2+((46:ℕ):ℝ)/20) (2+(((46:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 46 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 46 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((46:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 47 := by
    rw [show (1+(((46:ℕ):ℝ)+1)/20) = 1+((47:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 47 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((46:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((46:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 46:ℝ) = 998178/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 47:ℝ) = 898227/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 46:ℝ) = 104804/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 47:ℝ) = 92700/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 47 = 16129598/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+46/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+47/20) - v), hv0]

theorem hptE_47 : ∀ v ∈ Set.Ico (2+((47:ℕ):ℝ)/20) (2+(((47:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 47 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 47 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((47:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 48 := by
    rw [show (1+(((47:ℕ):ℝ)+1)/20) = 1+((48:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 48 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((47:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((47:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 47:ℝ) = 898227/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 48:ℝ) = 808063/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 47:ℝ) = 92700/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 48:ℝ) = 81952/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 48 = 14423308/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+47/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+48/20) - v), hv0]

theorem hptE_48 : ∀ v ∈ Set.Ico (2+((48:ℕ):ℝ)/20) (2+(((48:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 48 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 48 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((48:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 49 := by
    rw [show (1+(((48:ℕ):ℝ)+1)/20) = 1+((49:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 49 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((48:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((48:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 48:ℝ) = 808063/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 49:ℝ) = 726700/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 48:ℝ) = 81952/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 49:ℝ) = 72409/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 49 = 12888545/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+48/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+49/20) - v), hv0]

theorem hptE_49 : ∀ v ∈ Set.Ico (2+((49:ℕ):ℝ)/20) (2+(((49:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 49 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 49 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((49:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 50 := by
    rw [show (1+(((49:ℕ):ℝ)+1)/20) = 1+((50:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 50 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((49:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((49:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 49:ℝ) = 726700/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 50:ℝ) = 653259/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 49:ℝ) = 72409/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 50:ℝ) = 63938/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 50 = 11508586/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+49/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+50/20) - v), hv0]

theorem hptE_50 : ∀ v ∈ Set.Ico (2+((50:ℕ):ℝ)/20) (2+(((50:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 50 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 50 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((50:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 51 := by
    rw [show (1+(((50:ℕ):ℝ)+1)/20) = 1+((51:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 51 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((50:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((50:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 50:ℝ) = 653259/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 51:ℝ) = 586959/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 50:ℝ) = 63938/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 51:ℝ) = 56421/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 51 = 10268368/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+50/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+51/20) - v), hv0]

theorem hptE_51 : ∀ v ∈ Set.Ico (2+((51:ℕ):ℝ)/20) (2+(((51:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 51 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 51 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((51:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 52 := by
    rw [show (1+(((51:ℕ):ℝ)+1)/20) = 1+((52:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 52 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((51:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((51:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 51:ℝ) = 586959/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 52:ℝ) = 527100/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 51:ℝ) = 56421/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 52:ℝ) = 49753/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 52 = 9154309/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+51/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+52/20) - v), hv0]

theorem hptE_52 : ∀ v ∈ Set.Ico (2+((52:ℕ):ℝ)/20) (2+(((52:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 52 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 52 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((52:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 53 := by
    rw [show (1+(((52:ℕ):ℝ)+1)/20) = 1+((53:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 53 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((52:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((52:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 52:ℝ) = 527100/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 53:ℝ) = 473059/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 52:ℝ) = 49753/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 53:ℝ) = 43841/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 53 = 8154150/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+52/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+53/20) - v), hv0]

theorem hptE_53 : ∀ v ∈ Set.Ico (2+((53:ℕ):ℝ)/20) (2+(((53:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 53 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 53 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((53:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 54 := by
    rw [show (1+(((53:ℕ):ℝ)+1)/20) = 1+((54:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 54 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((53:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((53:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 53:ℝ) = 473059/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 54:ℝ) = 424272/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 53:ℝ) = 43841/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 54:ℝ) = 38601/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 54 = 7256819/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+53/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+54/20) - v), hv0]

theorem hptE_54 : ∀ v ∈ Set.Ico (2+((54:ℕ):ℝ)/20) (2+(((54:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 54 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 54 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((54:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 55 := by
    rw [show (1+(((54:ℕ):ℝ)+1)/20) = 1+((55:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 55 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((54:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((54:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 54:ℝ) = 424272/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 55:ℝ) = 380239/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 54:ℝ) = 38601/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 55:ℝ) = 33961/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 55 = 6452308/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+54/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+55/20) - v), hv0]

theorem hptE_55 : ∀ v ∈ Set.Ico (2+((55:ℕ):ℝ)/20) (2+(((55:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 55 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 55 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((55:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 56 := by
    rw [show (1+(((55:ℕ):ℝ)+1)/20) = 1+((56:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 56 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((55:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((55:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 55:ℝ) = 380239/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 56:ℝ) = 340505/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 55:ℝ) = 33961/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 56:ℝ) = 29853/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 56 = 5731564/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+55/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+56/20) - v), hv0]

theorem hptE_56 : ∀ v ∈ Set.Ico (2+((56:ℕ):ℝ)/20) (2+(((56:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 56 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 56 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((56:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 57 := by
    rw [show (1+(((56:ℕ):ℝ)+1)/20) = 1+((57:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 57 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((56:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((56:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 56:ℝ) = 340505/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 57:ℝ) = 304664/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 56:ℝ) = 29853/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 57:ℝ) = 26220/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 57 = 5086395/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+56/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+57/20) - v), hv0]

theorem hptE_57 : ∀ v ∈ Set.Ico (2+((57:ℕ):ℝ)/20) (2+(((57:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 57 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 57 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((57:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 58 := by
    rw [show (1+(((57:ℕ):ℝ)+1)/20) = 1+((58:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 58 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((57:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((57:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 57:ℝ) = 304664/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 58:ℝ) = 272348/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 57:ℝ) = 26220/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 58:ℝ) = 23008/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 58 = 4509383/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+57/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+58/20) - v), hv0]

theorem hptE_58 : ∀ v ∈ Set.Ico (2+((58:ℕ):ℝ)/20) (2+(((58:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 58 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 58 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((58:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 59 := by
    rw [show (1+(((58:ℕ):ℝ)+1)/20) = 1+((59:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 59 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((58:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((58:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 58:ℝ) = 272348/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 59:ℝ) = 243226/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 58:ℝ) = 23008/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 59:ℝ) = 20172/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 59 = 3993809/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+58/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+59/20) - v), hv0]

theorem hptE_59 : ∀ v ∈ Set.Ico (2+((59:ℕ):ℝ)/20) (2+(((59:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 59 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 59 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((59:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 60 := by
    rw [show (1+(((59:ℕ):ℝ)+1)/20) = 1+((60:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 60 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((59:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((59:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 59:ℝ) = 243226/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 60:ℝ) = 216997/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 59:ℝ) = 20172/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 60:ℝ) = 17669/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 60 = 3533586/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+59/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+60/20) - v), hv0]

theorem hptE_60 : ∀ v ∈ Set.Ico (2+((60:ℕ):ℝ)/20) (2+(((60:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 60 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 60 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((60:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 61 := by
    rw [show (1+(((60:ℕ):ℝ)+1)/20) = 1+((61:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 61 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((60:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((60:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 60:ℝ) = 216997/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 61:ℝ) = 193390/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 60:ℝ) = 17669/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 61:ℝ) = 15463/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 61 = 3123199/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+60/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+61/20) - v), hv0]

theorem hptE_61 : ∀ v ∈ Set.Ico (2+((61:ℕ):ℝ)/20) (2+(((61:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 61 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 61 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((61:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 62 := by
    rw [show (1+(((61:ℕ):ℝ)+1)/20) = 1+((62:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 62 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((61:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((61:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 61:ℝ) = 193390/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 62:ℝ) = 172161/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 61:ℝ) = 15463/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 62:ℝ) = 13519/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 62 = 2757648/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+61/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+62/20) - v), hv0]

theorem hptE_62 : ∀ v ∈ Set.Ico (2+((62:ℕ):ℝ)/20) (2+(((62:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 62 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 62 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((62:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 63 := by
    rw [show (1+(((62:ℕ):ℝ)+1)/20) = 1+((63:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 63 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((62:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((62:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 62:ℝ) = 172161/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 63:ℝ) = 153085/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 62:ℝ) = 13519/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 63:ℝ) = 11809/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 63 = 2432402/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+62/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+63/20) - v), hv0]

theorem hptE_63 : ∀ v ∈ Set.Ico (2+((63:ℕ):ℝ)/20) (2+(((63:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 63 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 63 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((63:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 64 := by
    rw [show (1+(((63:ℕ):ℝ)+1)/20) = 1+((64:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 64 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((63:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((63:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 63:ℝ) = 153085/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 64:ℝ) = 135962/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 63:ℝ) = 11809/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 64:ℝ) = 10306/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 64 = 2143355/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+63/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+64/20) - v), hv0]

theorem hptE_64 : ∀ v ∈ Set.Ico (2+((64:ℕ):ℝ)/20) (2+(((64:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 64 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 64 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((64:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 65 := by
    rw [show (1+(((64:ℕ):ℝ)+1)/20) = 1+((65:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 65 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((64:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((64:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 64:ℝ) = 135962/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 65:ℝ) = 120607/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 64:ℝ) = 10306/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 65:ℝ) = 8986/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 65 = 1886786/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+64/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+65/20) - v), hv0]

theorem hptE_65 : ∀ v ∈ Set.Ico (2+((65:ℕ):ℝ)/20) (2+(((65:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 65 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 65 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((65:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 66 := by
    rw [show (1+(((65:ℕ):ℝ)+1)/20) = 1+((66:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 66 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((65:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((65:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 65:ℝ) = 120607/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 66:ℝ) = 106853/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 65:ℝ) = 8986/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 66:ℝ) = 7828/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 66 = 1659326/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+65/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+66/20) - v), hv0]

theorem hptE_66 : ∀ v ∈ Set.Ico (2+((66:ℕ):ℝ)/20) (2+(((66:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 66 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 66 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((66:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 67 := by
    rw [show (1+(((66:ℕ):ℝ)+1)/20) = 1+((67:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 67 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((66:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((66:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 66:ℝ) = 106853/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 67:ℝ) = 94550/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 66:ℝ) = 7828/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 67:ℝ) = 6814/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 67 = 1457923/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+66/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+67/20) - v), hv0]

theorem hptE_67 : ∀ v ∈ Set.Ico (2+((67:ℕ):ℝ)/20) (2+(((67:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 67 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 67 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((67:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 68 := by
    rw [show (1+(((67:ℕ):ℝ)+1)/20) = 1+((68:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 68 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((67:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((67:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 67:ℝ) = 94550/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 68:ℝ) = 83557/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 67:ℝ) = 6814/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 68:ℝ) = 5926/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 68 = 1279816/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+67/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+68/20) - v), hv0]

theorem hptE_68 : ∀ v ∈ Set.Ico (2+((68:ℕ):ℝ)/20) (2+(((68:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 68 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 68 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((68:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 69 := by
    rw [show (1+(((68:ℕ):ℝ)+1)/20) = 1+((69:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 69 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((68:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((68:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 68:ℝ) = 83557/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 69:ℝ) = 73751/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 68:ℝ) = 5926/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 69:ℝ) = 5150/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 69 = 1122508/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+68/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+69/20) - v), hv0]

theorem hptE_69 : ∀ v ∈ Set.Ico (2+((69:ℕ):ℝ)/20) (2+(((69:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 69 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 69 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((69:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 70 := by
    rw [show (1+(((69:ℕ):ℝ)+1)/20) = 1+((70:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 70 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((69:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((69:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 69:ℝ) = 73751/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 70:ℝ) = 65016/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 69:ℝ) = 5150/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 70:ℝ) = 4473/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 70 = 983741/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+69/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+70/20) - v), hv0]

theorem hptE_70 : ∀ v ∈ Set.Ico (2+((70:ℕ):ℝ)/20) (2+(((70:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 70 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 70 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((70:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 71 := by
    rw [show (1+(((70:ℕ):ℝ)+1)/20) = 1+((71:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 71 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((70:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((70:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 70:ℝ) = 65016/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 71:ℝ) = 57247/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 70:ℝ) = 4473/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 71:ℝ) = 3882/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 71 = 861478/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+70/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+71/20) - v), hv0]

theorem hptE_71 : ∀ v ∈ Set.Ico (2+((71:ℕ):ℝ)/20) (2+(((71:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 71 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 71 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((71:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 72 := by
    rw [show (1+(((71:ℕ):ℝ)+1)/20) = 1+((72:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 72 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((71:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((71:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 71:ℝ) = 57247/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 72:ℝ) = 50349/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 71:ℝ) = 3882/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 72:ℝ) = 3367/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 72 = 753882/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+71/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+72/20) - v), hv0]

theorem hptE_72 : ∀ v ∈ Set.Ico (2+((72:ℕ):ℝ)/20) (2+(((72:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 72 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 72 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((72:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 73 := by
    rw [show (1+(((72:ℕ):ℝ)+1)/20) = 1+((73:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 73 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((72:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((72:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 72:ℝ) = 50349/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 73:ℝ) = 44235/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 72:ℝ) = 3367/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 73:ℝ) = 2918/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 73 = 659298/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+72/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+73/20) - v), hv0]

theorem hptE_73 : ∀ v ∈ Set.Ico (2+((73:ℕ):ℝ)/20) (2+(((73:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 73 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 73 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((73:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 74 := by
    rw [show (1+(((73:ℕ):ℝ)+1)/20) = 1+((74:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 74 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((73:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((73:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 73:ℝ) = 44235/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 74:ℝ) = 38825/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 73:ℝ) = 2918/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 74:ℝ) = 2528/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 74 = 576238/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+73/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+74/20) - v), hv0]

theorem hptE_74 : ∀ v ∈ Set.Ico (2+((74:ℕ):ℝ)/20) (2+(((74:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 74 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 74 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((74:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 75 := by
    rw [show (1+(((74:ℕ):ℝ)+1)/20) = 1+((75:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 75 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((74:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((74:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 74:ℝ) = 38825/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 75:ℝ) = 34047/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 74:ℝ) = 2528/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 75:ℝ) = 2190/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 75 = 503366/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+74/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+75/20) - v), hv0]

theorem hptE_75 : ∀ v ∈ Set.Ico (2+((75:ℕ):ℝ)/20) (2+(((75:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 75 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 75 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((75:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 76 := by
    rw [show (1+(((75:ℕ):ℝ)+1)/20) = 1+((76:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 76 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((75:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((75:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 75:ℝ) = 34047/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 76:ℝ) = 29834/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 75:ℝ) = 2190/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 76:ℝ) = 1895/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 76 = 439485/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+75/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+76/20) - v), hv0]

theorem hptE_76 : ∀ v ∈ Set.Ico (2+((76:ℕ):ℝ)/20) (2+(((76:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 76 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 76 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((76:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 77 := by
    rw [show (1+(((76:ℕ):ℝ)+1)/20) = 1+((77:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 77 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((76:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((76:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 76:ℝ) = 29834/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 77:ℝ) = 26125/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 76:ℝ) = 1895/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 77:ℝ) = 1640/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 77 = 383526/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+76/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+77/20) - v), hv0]

theorem hptE_77 : ∀ v ∈ Set.Ico (2+((77:ℕ):ℝ)/20) (2+(((77:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 77 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 77 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((77:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 78 := by
    rw [show (1+(((77:ℕ):ℝ)+1)/20) = 1+((78:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 78 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((77:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((77:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 77:ℝ) = 26125/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 78:ℝ) = 22865/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 77:ℝ) = 1640/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 78:ℝ) = 1419/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 78 = 334536/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+77/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+78/20) - v), hv0]

theorem hptE_78 : ∀ v ∈ Set.Ico (2+((78:ℕ):ℝ)/20) (2+(((78:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 78 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 78 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((78:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 79 := by
    rw [show (1+(((78:ℕ):ℝ)+1)/20) = 1+((79:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 79 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((78:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((78:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 78:ℝ) = 22865/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 79:ℝ) = 20003/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 78:ℝ) = 1419/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 79:ℝ) = 1227/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 79 = 291668/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+78/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+79/20) - v), hv0]

theorem hptE_79 : ∀ v ∈ Set.Ico (2+((79:ℕ):ℝ)/20) (2+(((79:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 79 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 79 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((79:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 80 := by
    rw [show (1+(((79:ℕ):ℝ)+1)/20) = 1+((80:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 80 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((79:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((79:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 79:ℝ) = 20003/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 80:ℝ) = 17493/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 79:ℝ) = 1227/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 80:ℝ) = 1060/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 80 = 254172/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+79/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+80/20) - v), hv0]

theorem hptE_80 : ∀ v ∈ Set.Ico (2+((80:ℕ):ℝ)/20) (2+(((80:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 80 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 80 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((80:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 81 := by
    rw [show (1+(((80:ℕ):ℝ)+1)/20) = 1+((81:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 81 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((80:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((80:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 80:ℝ) = 17493/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 81:ℝ) = 15292/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 80:ℝ) = 1060/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 81:ℝ) = 916/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 81 = 221387/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+80/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+81/20) - v), hv0]

theorem hptE_81 : ∀ v ∈ Set.Ico (2+((81:ℕ):ℝ)/20) (2+(((81:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 81 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 81 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((81:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 82 := by
    rw [show (1+(((81:ℕ):ℝ)+1)/20) = 1+((82:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 82 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((81:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((81:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 81:ℝ) = 15292/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 82:ℝ) = 13363/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 81:ℝ) = 916/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 82:ℝ) = 791/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 82 = 192732/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+81/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+82/20) - v), hv0]

theorem hptE_82 : ∀ v ∈ Set.Ico (2+((82:ℕ):ℝ)/20) (2+(((82:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 82 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 82 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((82:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 83 := by
    rw [show (1+(((82:ℕ):ℝ)+1)/20) = 1+((83:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 83 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((82:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((82:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 82:ℝ) = 13363/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 83:ℝ) = 11673/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 82:ℝ) = 791/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 83:ℝ) = 683/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 83 = 167696/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+82/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+83/20) - v), hv0]

theorem hptE_83 : ∀ v ∈ Set.Ico (2+((83:ℕ):ℝ)/20) (2+(((83:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 83 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 83 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((83:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 84 := by
    rw [show (1+(((83:ℕ):ℝ)+1)/20) = 1+((84:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 84 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((83:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((83:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 83:ℝ) = 11673/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 84:ℝ) = 10191/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 83:ℝ) = 683/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 84:ℝ) = 589/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 84 = 145832/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+83/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+84/20) - v), hv0]

theorem hptE_84 : ∀ v ∈ Set.Ico (2+((84:ℕ):ℝ)/20) (2+(((84:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 84 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 84 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((84:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 85 := by
    rw [show (1+(((84:ℕ):ℝ)+1)/20) = 1+((85:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 85 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((84:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((84:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 84:ℝ) = 10191/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 85:ℝ) = 8893/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 84:ℝ) = 589/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 85:ℝ) = 508/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 85 = 126748/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+84/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+85/20) - v), hv0]

theorem hptE_85 : ∀ v ∈ Set.Ico (2+((85:ℕ):ℝ)/20) (2+(((85:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 85 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 85 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((85:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 86 := by
    rw [show (1+(((85:ℕ):ℝ)+1)/20) = 1+((86:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 86 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((85:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((85:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 85:ℝ) = 8893/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 86:ℝ) = 7756/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 85:ℝ) = 508/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 86:ℝ) = 438/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 86 = 110099/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+85/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+86/20) - v), hv0]

theorem hptE_86 : ∀ v ∈ Set.Ico (2+((86:ℕ):ℝ)/20) (2+(((86:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 86 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 86 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((86:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 87 := by
    rw [show (1+(((86:ℕ):ℝ)+1)/20) = 1+((87:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 87 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((86:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((86:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 86:ℝ) = 7756/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 87:ℝ) = 6761/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 86:ℝ) = 438/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 87:ℝ) = 377/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 87 = 95582/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+86/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+87/20) - v), hv0]

theorem hptE_87 : ∀ v ∈ Set.Ico (2+((87:ℕ):ℝ)/20) (2+(((87:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 87 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 87 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((87:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 88 := by
    rw [show (1+(((87:ℕ):ℝ)+1)/20) = 1+((88:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 88 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((87:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((87:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 87:ℝ) = 6761/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 88:ℝ) = 5889/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 87:ℝ) = 377/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 88:ℝ) = 325/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 88 = 82932/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+87/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+88/20) - v), hv0]

theorem hptE_88 : ∀ v ∈ Set.Ico (2+((88:ℕ):ℝ)/20) (2+(((88:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 88 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 88 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((88:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 89 := by
    rw [show (1+(((88:ℕ):ℝ)+1)/20) = 1+((89:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 89 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((88:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((88:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 88:ℝ) = 5889/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 89:ℝ) = 5127/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 88:ℝ) = 325/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 89:ℝ) = 280/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 89 = 71916/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+88/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+89/20) - v), hv0]

theorem hptE_89 : ∀ v ∈ Set.Ico (2+((89:ℕ):ℝ)/20) (2+(((89:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 89 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 89 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((89:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 90 := by
    rw [show (1+(((89:ℕ):ℝ)+1)/20) = 1+((90:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 90 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((89:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((89:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 89:ℝ) = 5127/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 90:ℝ) = 4461/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 89:ℝ) = 280/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 90:ℝ) = 241/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 90 = 62328/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+89/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+90/20) - v), hv0]

theorem hptE_90 : ∀ v ∈ Set.Ico (2+((90:ℕ):ℝ)/20) (2+(((90:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 90 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 90 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((90:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 91 := by
    rw [show (1+(((90:ℕ):ℝ)+1)/20) = 1+((91:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 91 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((90:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((90:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 90:ℝ) = 4461/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 91:ℝ) = 3879/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 90:ℝ) = 241/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 91:ℝ) = 207/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 91 = 53988/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+90/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+91/20) - v), hv0]

theorem hptE_91 : ∀ v ∈ Set.Ico (2+((91:ℕ):ℝ)/20) (2+(((91:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 91 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 91 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((91:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 92 := by
    rw [show (1+(((91:ℕ):ℝ)+1)/20) = 1+((92:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 92 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((91:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((91:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 91:ℝ) = 3879/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 92:ℝ) = 3370/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 91:ℝ) = 207/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 92:ℝ) = 178/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 92 = 46739/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+91/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+92/20) - v), hv0]

theorem hptE_92 : ∀ v ∈ Set.Ico (2+((92:ℕ):ℝ)/20) (2+(((92:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 92 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 92 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((92:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 93 := by
    rw [show (1+(((92:ℕ):ℝ)+1)/20) = 1+((93:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 93 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((92:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((92:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 92:ℝ) = 3370/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 93:ℝ) = 2926/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 92:ℝ) = 178/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 93:ℝ) = 153/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 93 = 40443/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+92/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+93/20) - v), hv0]

theorem hptE_93 : ∀ v ∈ Set.Ico (2+((93:ℕ):ℝ)/20) (2+(((93:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 93 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 93 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((93:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 94 := by
    rw [show (1+(((93:ℕ):ℝ)+1)/20) = 1+((94:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 94 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((93:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((93:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 93:ℝ) = 2926/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 94:ℝ) = 2539/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 93:ℝ) = 153/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 94:ℝ) = 132/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 94 = 34978/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+93/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+94/20) - v), hv0]

theorem hptE_94 : ∀ v ∈ Set.Ico (2+((94:ℕ):ℝ)/20) (2+(((94:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 94 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 94 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((94:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 95 := by
    rw [show (1+(((94:ℕ):ℝ)+1)/20) = 1+((95:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 95 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((94:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((94:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 94:ℝ) = 2539/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 95:ℝ) = 2201/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 94:ℝ) = 132/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 95:ℝ) = 113/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 95 = 30238/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+94/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+95/20) - v), hv0]

theorem hptE_95 : ∀ v ∈ Set.Ico (2+((95:ℕ):ℝ)/20) (2+(((95:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 95 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 95 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((95:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 96 := by
    rw [show (1+(((95:ℕ):ℝ)+1)/20) = 1+((96:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 96 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((95:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((95:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 95:ℝ) = 2201/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 96:ℝ) = 1907/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 95:ℝ) = 113/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 96:ℝ) = 97/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 96 = 26130/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+95/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+96/20) - v), hv0]

theorem hptE_96 : ∀ v ∈ Set.Ico (2+((96:ℕ):ℝ)/20) (2+(((96:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 96 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 96 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((96:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 97 := by
    rw [show (1+(((96:ℕ):ℝ)+1)/20) = 1+((97:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 97 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((96:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((96:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 96:ℝ) = 1907/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 97:ℝ) = 1651/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 96:ℝ) = 97/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 97:ℝ) = 83/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 97 = 22572/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+96/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+97/20) - v), hv0]

theorem hptE_97 : ∀ v ∈ Set.Ico (2+((97:ℕ):ℝ)/20) (2+(((97:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 97 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 97 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((97:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 98 := by
    rw [show (1+(((97:ℕ):ℝ)+1)/20) = 1+((98:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 98 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((97:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((97:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 97:ℝ) = 1651/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 98:ℝ) = 1429/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 97:ℝ) = 83/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 98:ℝ) = 72/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 98 = 19492/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+97/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+98/20) - v), hv0]

theorem hptE_98 : ∀ v ∈ Set.Ico (2+((98:ℕ):ℝ)/20) (2+(((98:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 98 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 98 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((98:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 99 := by
    rw [show (1+(((98:ℕ):ℝ)+1)/20) = 1+((99:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 99 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((98:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((98:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 98:ℝ) = 1429/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 99:ℝ) = 1235/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 98:ℝ) = 72/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 99:ℝ) = 62/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 99 = 16828/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+98/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+99/20) - v), hv0]

theorem hptE_99 : ∀ v ∈ Set.Ico (2+((99:ℕ):ℝ)/20) (2+(((99:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 99 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 99 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((99:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 100 := by
    rw [show (1+(((99:ℕ):ℝ)+1)/20) = 1+((100:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 100 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((99:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((99:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 99:ℝ) = 1235/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 100:ℝ) = 1067/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 99:ℝ) = 62/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 100:ℝ) = 53/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 100 = 14526/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+99/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+100/20) - v), hv0]

theorem hptE_100 : ∀ v ∈ Set.Ico (2+((100:ℕ):ℝ)/20) (2+(((100:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 100 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 100 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((100:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 101 := by
    rw [show (1+(((100:ℕ):ℝ)+1)/20) = 1+((101:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 101 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((100:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((100:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 100:ℝ) = 1067/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 101:ℝ) = 922/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 100:ℝ) = 53/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 101:ℝ) = 45/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 101 = 12537/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+100/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+101/20) - v), hv0]

theorem hptE_101 : ∀ v ∈ Set.Ico (2+((101:ℕ):ℝ)/20) (2+(((101:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 101 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 101 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((101:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 102 := by
    rw [show (1+(((101:ℕ):ℝ)+1)/20) = 1+((102:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 102 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((101:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((101:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 101:ℝ) = 922/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 102:ℝ) = 795/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 101:ℝ) = 45/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 102:ℝ) = 39/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 102 = 10820/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+101/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+102/20) - v), hv0]

theorem hptE_102 : ∀ v ∈ Set.Ico (2+((102:ℕ):ℝ)/20) (2+(((102:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 102 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 102 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((102:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 103 := by
    rw [show (1+(((102:ℕ):ℝ)+1)/20) = 1+((103:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 103 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((102:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((102:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 102:ℝ) = 795/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 103:ℝ) = 686/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 102:ℝ) = 39/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 103:ℝ) = 34/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 103 = 9339/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+102/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+103/20) - v), hv0]

theorem hptE_103 : ∀ v ∈ Set.Ico (2+((103:ℕ):ℝ)/20) (2+(((103:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 103 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 103 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((103:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 104 := by
    rw [show (1+(((103:ℕ):ℝ)+1)/20) = 1+((104:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 104 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((103:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((103:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 103:ℝ) = 686/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 104:ℝ) = 591/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 103:ℝ) = 34/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 104:ℝ) = 29/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 104 = 8062/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+103/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+104/20) - v), hv0]

theorem hptE_104 : ∀ v ∈ Set.Ico (2+((104:ℕ):ℝ)/20) (2+(((104:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 104 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 104 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((104:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 105 := by
    rw [show (1+(((104:ℕ):ℝ)+1)/20) = 1+((105:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 105 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((104:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((104:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 104:ℝ) = 591/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 105:ℝ) = 509/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 104:ℝ) = 29/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 105:ℝ) = 25/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 105 = 6962/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+104/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+105/20) - v), hv0]

theorem hptE_105 : ∀ v ∈ Set.Ico (2+((105:ℕ):ℝ)/20) (2+(((105:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 105 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 105 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((105:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 106 := by
    rw [show (1+(((105:ℕ):ℝ)+1)/20) = 1+((106:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 106 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((105:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((105:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 105:ℝ) = 509/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 106:ℝ) = 439/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 105:ℝ) = 25/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 106:ℝ) = 22/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 106 = 6014/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+105/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+106/20) - v), hv0]

theorem hptE_106 : ∀ v ∈ Set.Ico (2+((106:ℕ):ℝ)/20) (2+(((106:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 106 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 106 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((106:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 107 := by
    rw [show (1+(((106:ℕ):ℝ)+1)/20) = 1+((107:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 107 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((106:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((106:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 106:ℝ) = 439/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 107:ℝ) = 377/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 106:ℝ) = 22/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 107:ℝ) = 19/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 107 = 5198/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+106/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+107/20) - v), hv0]

theorem hptE_107 : ∀ v ∈ Set.Ico (2+((107:ℕ):ℝ)/20) (2+(((107:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 107 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 107 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((107:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 108 := by
    rw [show (1+(((107:ℕ):ℝ)+1)/20) = 1+((108:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 108 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((107:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((107:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 107:ℝ) = 377/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 108:ℝ) = 325/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 107:ℝ) = 19/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 108:ℝ) = 16/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 108 = 4496/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+107/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+108/20) - v), hv0]

theorem hptE_108 : ∀ v ∈ Set.Ico (2+((108:ℕ):ℝ)/20) (2+(((108:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 108 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 108 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((108:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 109 := by
    rw [show (1+(((108:ℕ):ℝ)+1)/20) = 1+((109:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 109 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((108:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((108:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 108:ℝ) = 325/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 109:ℝ) = 279/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 108:ℝ) = 16/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 109:ℝ) = 14/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 109 = 3892/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+108/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+109/20) - v), hv0]

theorem hptE_109 : ∀ v ∈ Set.Ico (2+((109:ℕ):ℝ)/20) (2+(((109:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 109 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 109 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((109:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 110 := by
    rw [show (1+(((109:ℕ):ℝ)+1)/20) = 1+((110:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 110 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((109:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((109:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 109:ℝ) = 279/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 110:ℝ) = 240/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 109:ℝ) = 14/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 110:ℝ) = 12/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 110 = 3373/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+109/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+110/20) - v), hv0]

theorem hptE_110 : ∀ v ∈ Set.Ico (2+((110:ℕ):ℝ)/20) (2+(((110:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 110 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 110 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((110:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 111 := by
    rw [show (1+(((110:ℕ):ℝ)+1)/20) = 1+((111:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 111 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((110:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((110:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 110:ℝ) = 240/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 111:ℝ) = 206/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 110:ℝ) = 12/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 111:ℝ) = 11/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 111 = 2927/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+110/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+111/20) - v), hv0]

theorem hptE_111 : ∀ v ∈ Set.Ico (2+((111:ℕ):ℝ)/20) (2+(((111:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 111 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 111 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((111:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 112 := by
    rw [show (1+(((111:ℕ):ℝ)+1)/20) = 1+((112:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 112 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((111:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((111:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 111:ℝ) = 206/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 112:ℝ) = 177/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 111:ℝ) = 11/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 112:ℝ) = 9/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 112 = 2544/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+111/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+112/20) - v), hv0]

theorem hptE_112 : ∀ v ∈ Set.Ico (2+((112:ℕ):ℝ)/20) (2+(((112:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 112 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 112 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((112:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 113 := by
    rw [show (1+(((112:ℕ):ℝ)+1)/20) = 1+((113:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 113 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((112:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((112:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 112:ℝ) = 177/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 113:ℝ) = 152/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 112:ℝ) = 9/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 113:ℝ) = 8/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 113 = 2215/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+112/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+113/20) - v), hv0]

theorem hptE_113 : ∀ v ∈ Set.Ico (2+((113:ℕ):ℝ)/20) (2+(((113:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 113 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 113 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((113:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 114 := by
    rw [show (1+(((113:ℕ):ℝ)+1)/20) = 1+((114:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 114 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((113:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((113:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 113:ℝ) = 152/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 114:ℝ) = 131/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 113:ℝ) = 8/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 114:ℝ) = 7/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 114 = 1932/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+113/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+114/20) - v), hv0]

theorem hptE_114 : ∀ v ∈ Set.Ico (2+((114:ℕ):ℝ)/20) (2+(((114:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 114 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 114 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((114:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 115 := by
    rw [show (1+(((114:ℕ):ℝ)+1)/20) = 1+((115:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 115 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((114:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((114:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 114:ℝ) = 131/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 115:ℝ) = 113/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 114:ℝ) = 7/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 115:ℝ) = 6/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 115 = 1688/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+114/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+115/20) - v), hv0]

theorem hptE_115 : ∀ v ∈ Set.Ico (2+((115:ℕ):ℝ)/20) (2+(((115:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 115 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 115 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((115:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 116 := by
    rw [show (1+(((115:ℕ):ℝ)+1)/20) = 1+((116:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 116 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((115:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((115:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 115:ℝ) = 113/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 116:ℝ) = 97/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 115:ℝ) = 6/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 116:ℝ) = 6/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 116 = 1478/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+115/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+116/20) - v), hv0]

theorem hptE_116 : ∀ v ∈ Set.Ico (2+((116:ℕ):ℝ)/20) (2+(((116:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 116 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 116 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((116:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 117 := by
    rw [show (1+(((116:ℕ):ℝ)+1)/20) = 1+((117:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 117 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((116:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((116:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 116:ℝ) = 97/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 117:ℝ) = 83/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 116:ℝ) = 6/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 117:ℝ) = 5/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 117 = 1298/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+116/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+117/20) - v), hv0]

theorem hptE_117 : ∀ v ∈ Set.Ico (2+((117:ℕ):ℝ)/20) (2+(((117:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 117 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 117 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((117:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 118 := by
    rw [show (1+(((117:ℕ):ℝ)+1)/20) = 1+((118:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 118 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((117:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((117:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 117:ℝ) = 83/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 118:ℝ) = 71/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 117:ℝ) = 5/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 118:ℝ) = 5/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 118 = 1144/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+117/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+118/20) - v), hv0]

theorem hptE_118 : ∀ v ∈ Set.Ico (2+((118:ℕ):ℝ)/20) (2+(((118:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 118 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 118 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((118:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 119 := by
    rw [show (1+(((118:ℕ):ℝ)+1)/20) = 1+((119:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 119 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((118:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((118:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 118:ℝ) = 71/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 119:ℝ) = 61/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 118:ℝ) = 5/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 119:ℝ) = 4/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 119 = 1012/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+118/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+119/20) - v), hv0]

theorem hptE_119 : ∀ v ∈ Set.Ico (2+((119:ℕ):ℝ)/20) (2+(((119:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 119 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 119 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((119:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 120 := by
    rw [show (1+(((119:ℕ):ℝ)+1)/20) = 1+((120:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 120 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((119:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((119:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 119:ℝ) = 61/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 120:ℝ) = 53/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 119:ℝ) = 4/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 120:ℝ) = 4/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 120 = 898/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+119/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+120/20) - v), hv0]

theorem hptE_120 : ∀ v ∈ Set.Ico (2+((120:ℕ):ℝ)/20) (2+(((120:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 120 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 120 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((120:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 121 := by
    rw [show (1+(((120:ℕ):ℝ)+1)/20) = 1+((121:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 121 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((120:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((120:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 120:ℝ) = 53/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 121:ℝ) = 45/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 120:ℝ) = 4/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 121:ℝ) = 3/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 121 = 800/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+120/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+121/20) - v), hv0]

theorem hptE_121 : ∀ v ∈ Set.Ico (2+((121:ℕ):ℝ)/20) (2+(((121:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 121 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 121 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((121:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 122 := by
    rw [show (1+(((121:ℕ):ℝ)+1)/20) = 1+((122:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 122 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((121:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((121:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 121:ℝ) = 45/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 122:ℝ) = 39/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 121:ℝ) = 3/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 122:ℝ) = 3/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 122 = 716/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+121/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+122/20) - v), hv0]

theorem hptE_122 : ∀ v ∈ Set.Ico (2+((122:ℕ):ℝ)/20) (2+(((122:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 122 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 122 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((122:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 123 := by
    rw [show (1+(((122:ℕ):ℝ)+1)/20) = 1+((123:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 123 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((122:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((122:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 122:ℝ) = 39/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 123:ℝ) = 34/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 122:ℝ) = 3/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 123:ℝ) = 3/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 123 = 643/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+122/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+123/20) - v), hv0]

theorem hptE_123 : ∀ v ∈ Set.Ico (2+((123:ℕ):ℝ)/20) (2+(((123:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 123 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 123 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((123:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 124 := by
    rw [show (1+(((123:ℕ):ℝ)+1)/20) = 1+((124:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 124 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((123:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((123:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 123:ℝ) = 34/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 124:ℝ) = 29/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 123:ℝ) = 3/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 124:ℝ) = 3/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 124 = 580/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+123/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+124/20) - v), hv0]

theorem hptE_124 : ∀ v ∈ Set.Ico (2+((124:ℕ):ℝ)/20) (2+(((124:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 124 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 124 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((124:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 125 := by
    rw [show (1+(((124:ℕ):ℝ)+1)/20) = 1+((125:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 125 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((124:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((124:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 124:ℝ) = 29/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 125:ℝ) = 25/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 124:ℝ) = 3/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 125:ℝ) = 3/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 125 = 526/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+124/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+125/20) - v), hv0]

theorem hptE_125 : ∀ v ∈ Set.Ico (2+((125:ℕ):ℝ)/20) (2+(((125:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 125 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 125 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((125:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 126 := by
    rw [show (1+(((125:ℕ):ℝ)+1)/20) = 1+((126:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 126 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((125:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((125:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 125:ℝ) = 25/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 126:ℝ) = 22/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 125:ℝ) = 3/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 126:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 126 = 479/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+125/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+126/20) - v), hv0]

theorem hptE_126 : ∀ v ∈ Set.Ico (2+((126:ℕ):ℝ)/20) (2+(((126:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 126 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 126 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((126:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 127 := by
    rw [show (1+(((126:ℕ):ℝ)+1)/20) = 1+((127:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 127 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((126:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((126:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 126:ℝ) = 22/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 127:ℝ) = 19/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 126:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 127:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 127 = 438/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+126/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+127/20) - v), hv0]

theorem hptE_127 : ∀ v ∈ Set.Ico (2+((127:ℕ):ℝ)/20) (2+(((127:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 127 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 127 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((127:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 128 := by
    rw [show (1+(((127:ℕ):ℝ)+1)/20) = 1+((128:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 128 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((127:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((127:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 127:ℝ) = 19/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 128:ℝ) = 16/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 127:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 128:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 128 = 403/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+127/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+128/20) - v), hv0]

theorem hptE_128 : ∀ v ∈ Set.Ico (2+((128:ℕ):ℝ)/20) (2+(((128:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 128 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 128 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((128:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 129 := by
    rw [show (1+(((128:ℕ):ℝ)+1)/20) = 1+((129:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 129 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((128:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((128:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 128:ℝ) = 16/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 129:ℝ) = 14/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 128:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 129:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 129 = 373/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+128/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+129/20) - v), hv0]

theorem hptE_129 : ∀ v ∈ Set.Ico (2+((129:ℕ):ℝ)/20) (2+(((129:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 129 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 129 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((129:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 130 := by
    rw [show (1+(((129:ℕ):ℝ)+1)/20) = 1+((130:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 130 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((129:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((129:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 129:ℝ) = 14/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 130:ℝ) = 12/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 129:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 130:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 130 = 347/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+129/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+130/20) - v), hv0]

theorem hptE_130 : ∀ v ∈ Set.Ico (2+((130:ℕ):ℝ)/20) (2+(((130:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 130 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 130 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((130:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 131 := by
    rw [show (1+(((130:ℕ):ℝ)+1)/20) = 1+((131:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 131 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((130:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((130:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 130:ℝ) = 12/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 131:ℝ) = 11/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 130:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 131:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 131 = 324/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+130/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+131/20) - v), hv0]

theorem hptE_131 : ∀ v ∈ Set.Ico (2+((131:ℕ):ℝ)/20) (2+(((131:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 131 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 131 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((131:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 132 := by
    rw [show (1+(((131:ℕ):ℝ)+1)/20) = 1+((132:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 132 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((131:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((131:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 131:ℝ) = 11/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 132:ℝ) = 9/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 131:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 132:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 132 = 304/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+131/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+132/20) - v), hv0]

theorem hptE_132 : ∀ v ∈ Set.Ico (2+((132:ℕ):ℝ)/20) (2+(((132:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 132 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 132 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((132:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 133 := by
    rw [show (1+(((132:ℕ):ℝ)+1)/20) = 1+((133:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 133 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((132:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((132:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 132:ℝ) = 9/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 133:ℝ) = 8/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 132:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 133:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 133 = 287/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+132/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+133/20) - v), hv0]

theorem hptE_133 : ∀ v ∈ Set.Ico (2+((133:ℕ):ℝ)/20) (2+(((133:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 133 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 133 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((133:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 134 := by
    rw [show (1+(((133:ℕ):ℝ)+1)/20) = 1+((134:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 134 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((133:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((133:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 133:ℝ) = 8/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 134:ℝ) = 7/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 133:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 134:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 134 = 272/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+133/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+134/20) - v), hv0]

theorem hptE_134 : ∀ v ∈ Set.Ico (2+((134:ℕ):ℝ)/20) (2+(((134:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 134 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 134 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((134:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 135 := by
    rw [show (1+(((134:ℕ):ℝ)+1)/20) = 1+((135:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 135 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((134:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((134:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 134:ℝ) = 7/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 135:ℝ) = 6/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 134:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 135:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 135 = 259/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+134/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+135/20) - v), hv0]

theorem hptE_135 : ∀ v ∈ Set.Ico (2+((135:ℕ):ℝ)/20) (2+(((135:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 135 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 135 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((135:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 136 := by
    rw [show (1+(((135:ℕ):ℝ)+1)/20) = 1+((136:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 136 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((135:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((135:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 135:ℝ) = 6/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 136:ℝ) = 6/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 135:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 136:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 136 = 247/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+135/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+136/20) - v), hv0]

theorem hptE_136 : ∀ v ∈ Set.Ico (2+((136:ℕ):ℝ)/20) (2+(((136:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 136 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 136 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((136:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 137 := by
    rw [show (1+(((136:ℕ):ℝ)+1)/20) = 1+((137:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 137 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((136:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((136:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 136:ℝ) = 6/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 137:ℝ) = 5/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 136:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 137:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 137 = 236/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+136/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+137/20) - v), hv0]

theorem hptE_137 : ∀ v ∈ Set.Ico (2+((137:ℕ):ℝ)/20) (2+(((137:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 137 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 137 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((137:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 138 := by
    rw [show (1+(((137:ℕ):ℝ)+1)/20) = 1+((138:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 138 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((137:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((137:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 137:ℝ) = 5/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 138:ℝ) = 5/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 137:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 138:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 138 = 226/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+137/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+138/20) - v), hv0]

theorem hptE_138 : ∀ v ∈ Set.Ico (2+((138:ℕ):ℝ)/20) (2+(((138:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 138 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 138 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((138:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 139 := by
    rw [show (1+(((138:ℕ):ℝ)+1)/20) = 1+((139:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 139 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((138:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((138:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 138:ℝ) = 5/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 139:ℝ) = 4/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 138:ℝ) = 2/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 139:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 139 = 217/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+138/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+139/20) - v), hv0]

theorem hptE_139 : ∀ v ∈ Set.Ico (2+((139:ℕ):ℝ)/20) (2+(((139:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 139 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 139 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((139:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 140 := by
    rw [show (1+(((139:ℕ):ℝ)+1)/20) = 1+((140:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 140 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((139:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((139:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 139:ℝ) = 4/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 140:ℝ) = 4/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 139:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 140:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 140 = 209/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+139/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+140/20) - v), hv0]

theorem hptE_140 : ∀ v ∈ Set.Ico (2+((140:ℕ):ℝ)/20) (2+(((140:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 140 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 140 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((140:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 141 := by
    rw [show (1+(((140:ℕ):ℝ)+1)/20) = 1+((141:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 141 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((140:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((140:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 140:ℝ) = 4/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 141:ℝ) = 3/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 140:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 141:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 141 = 202/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+140/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+141/20) - v), hv0]

theorem hptE_141 : ∀ v ∈ Set.Ico (2+((141:ℕ):ℝ)/20) (2+(((141:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 141 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 141 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((141:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 142 := by
    rw [show (1+(((141:ℕ):ℝ)+1)/20) = 1+((142:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 142 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((141:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((141:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 141:ℝ) = 3/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 142:ℝ) = 3/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 141:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 142:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 142 = 196/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+141/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+142/20) - v), hv0]

theorem hptE_142 : ∀ v ∈ Set.Ico (2+((142:ℕ):ℝ)/20) (2+(((142:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 142 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 142 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((142:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 143 := by
    rw [show (1+(((142:ℕ):ℝ)+1)/20) = 1+((143:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 143 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((142:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((142:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 142:ℝ) = 3/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 143:ℝ) = 3/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 142:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 143:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 143 = 190/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+142/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+143/20) - v), hv0]

theorem hptE_143 : ∀ v ∈ Set.Ico (2+((143:ℕ):ℝ)/20) (2+(((143:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 143 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 143 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((143:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 144 := by
    rw [show (1+(((143:ℕ):ℝ)+1)/20) = 1+((144:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 144 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((143:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((143:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 143:ℝ) = 3/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 144:ℝ) = 3/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 143:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 144:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 144 = 184/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+143/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+144/20) - v), hv0]

theorem hptE_144 : ∀ v ∈ Set.Ico (2+((144:ℕ):ℝ)/20) (2+(((144:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 144 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 144 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((144:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 145 := by
    rw [show (1+(((144:ℕ):ℝ)+1)/20) = 1+((145:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 145 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((144:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((144:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 144:ℝ) = 3/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 145:ℝ) = 3/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 144:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 145:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 145 = 178/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+144/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+145/20) - v), hv0]

theorem hptE_145 : ∀ v ∈ Set.Ico (2+((145:ℕ):ℝ)/20) (2+(((145:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 145 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 145 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((145:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 146 := by
    rw [show (1+(((145:ℕ):ℝ)+1)/20) = 1+((146:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 146 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((145:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((145:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 145:ℝ) = 3/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 146:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 145:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 146:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 146 = 173/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+145/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+146/20) - v), hv0]

theorem hptE_146 : ∀ v ∈ Set.Ico (2+((146:ℕ):ℝ)/20) (2+(((146:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 146 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 146 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((146:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 147 := by
    rw [show (1+(((146:ℕ):ℝ)+1)/20) = 1+((147:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 147 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((146:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((146:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 146:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 147:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 146:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 147:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 147 = 169/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+146/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+147/20) - v), hv0]

theorem hptE_147 : ∀ v ∈ Set.Ico (2+((147:ℕ):ℝ)/20) (2+(((147:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 147 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 147 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((147:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 148 := by
    rw [show (1+(((147:ℕ):ℝ)+1)/20) = 1+((148:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 148 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((147:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((147:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 147:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 148:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 147:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 148:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 148 = 165/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+147/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+148/20) - v), hv0]

theorem hptE_148 : ∀ v ∈ Set.Ico (2+((148:ℕ):ℝ)/20) (2+(((148:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 148 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 148 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((148:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 149 := by
    rw [show (1+(((148:ℕ):ℝ)+1)/20) = 1+((149:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 149 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((148:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((148:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 148:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 149:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 148:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 149:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 149 = 161/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+148/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+149/20) - v), hv0]

theorem hptE_149 : ∀ v ∈ Set.Ico (2+((149:ℕ):ℝ)/20) (2+(((149:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 149 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 149 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((149:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 150 := by
    rw [show (1+(((149:ℕ):ℝ)+1)/20) = 1+((150:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 150 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((149:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((149:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 149:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 150:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 149:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 150:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 150 = 157/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+149/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+150/20) - v), hv0]

theorem hptE_150 : ∀ v ∈ Set.Ico (2+((150:ℕ):ℝ)/20) (2+(((150:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 150 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 150 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((150:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 151 := by
    rw [show (1+(((150:ℕ):ℝ)+1)/20) = 1+((151:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 151 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((150:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((150:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 150:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 151:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 150:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 151:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 151 = 153/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+150/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+151/20) - v), hv0]

theorem hptE_151 : ∀ v ∈ Set.Ico (2+((151:ℕ):ℝ)/20) (2+(((151:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 151 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 151 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((151:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 152 := by
    rw [show (1+(((151:ℕ):ℝ)+1)/20) = 1+((152:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 152 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((151:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((151:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 151:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 152:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 151:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 152:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 152 = 149/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+151/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+152/20) - v), hv0]

theorem hptE_152 : ∀ v ∈ Set.Ico (2+((152:ℕ):ℝ)/20) (2+(((152:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 152 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 152 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((152:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 153 := by
    rw [show (1+(((152:ℕ):ℝ)+1)/20) = 1+((153:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 153 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((152:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((152:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 152:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 153:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 152:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 153:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 153 = 145/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+152/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+153/20) - v), hv0]

theorem hptE_153 : ∀ v ∈ Set.Ico (2+((153:ℕ):ℝ)/20) (2+(((153:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 153 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 153 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((153:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 154 := by
    rw [show (1+(((153:ℕ):ℝ)+1)/20) = 1+((154:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 154 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((153:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((153:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 153:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 154:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 153:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 154:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 154 = 141/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+153/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+154/20) - v), hv0]

theorem hptE_154 : ∀ v ∈ Set.Ico (2+((154:ℕ):ℝ)/20) (2+(((154:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 154 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 154 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((154:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 155 := by
    rw [show (1+(((154:ℕ):ℝ)+1)/20) = 1+((155:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 155 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((154:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((154:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 154:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 155:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 154:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 155:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 155 = 137/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+154/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+155/20) - v), hv0]

theorem hptE_155 : ∀ v ∈ Set.Ico (2+((155:ℕ):ℝ)/20) (2+(((155:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 155 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 155 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((155:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 156 := by
    rw [show (1+(((155:ℕ):ℝ)+1)/20) = 1+((156:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 156 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((155:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((155:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 155:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 156:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 155:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 156:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 156 = 133/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+155/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+156/20) - v), hv0]

theorem hptE_156 : ∀ v ∈ Set.Ico (2+((156:ℕ):ℝ)/20) (2+(((156:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 156 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 156 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((156:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 157 := by
    rw [show (1+(((156:ℕ):ℝ)+1)/20) = 1+((157:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 157 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((156:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((156:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 156:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 157:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 156:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 157:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 157 = 129/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+156/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+157/20) - v), hv0]

theorem hptE_157 : ∀ v ∈ Set.Ico (2+((157:ℕ):ℝ)/20) (2+(((157:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 157 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 157 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((157:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 158 := by
    rw [show (1+(((157:ℕ):ℝ)+1)/20) = 1+((158:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 158 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((157:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((157:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 157:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 158:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 157:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 158:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 158 = 125/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+157/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+158/20) - v), hv0]

theorem hptE_158 : ∀ v ∈ Set.Ico (2+((158:ℕ):ℝ)/20) (2+(((158:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 158 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 158 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((158:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 159 := by
    rw [show (1+(((158:ℕ):ℝ)+1)/20) = 1+((159:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 159 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((158:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((158:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 158:ℝ) = 2/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 159:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 158:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 159:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 159 = 122/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+158/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+159/20) - v), hv0]

theorem hptE_159 : ∀ v ∈ Set.Ico (2+((159:ℕ):ℝ)/20) (2+(((159:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 159 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 159 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((159:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 160 := by
    rw [show (1+(((159:ℕ):ℝ)+1)/20) = 1+((160:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 160 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((159:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((159:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 159:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 160:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 159:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 160:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 160 = 120/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+159/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+160/20) - v), hv0]

theorem hptE_160 : ∀ v ∈ Set.Ico (2+((160:ℕ):ℝ)/20) (2+(((160:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 160 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 160 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((160:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 161 := by
    rw [show (1+(((160:ℕ):ℝ)+1)/20) = 1+((161:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 161 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((160:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((160:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 160:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 161:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 160:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 161:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 161 = 118/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+160/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+161/20) - v), hv0]

theorem hptE_161 : ∀ v ∈ Set.Ico (2+((161:ℕ):ℝ)/20) (2+(((161:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 161 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 161 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((161:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 162 := by
    rw [show (1+(((161:ℕ):ℝ)+1)/20) = 1+((162:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 162 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((161:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((161:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 161:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 162:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 161:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 162:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 162 = 116/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+161/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+162/20) - v), hv0]

theorem hptE_162 : ∀ v ∈ Set.Ico (2+((162:ℕ):ℝ)/20) (2+(((162:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 162 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 162 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((162:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 163 := by
    rw [show (1+(((162:ℕ):ℝ)+1)/20) = 1+((163:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 163 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((162:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((162:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 162:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 163:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 162:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 163:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 163 = 114/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+162/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+163/20) - v), hv0]

theorem hptE_163 : ∀ v ∈ Set.Ico (2+((163:ℕ):ℝ)/20) (2+(((163:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 163 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 163 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((163:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 164 := by
    rw [show (1+(((163:ℕ):ℝ)+1)/20) = 1+((164:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 164 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((163:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((163:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 163:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 164:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 163:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 164:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 164 = 112/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+163/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+164/20) - v), hv0]

theorem hptE_164 : ∀ v ∈ Set.Ico (2+((164:ℕ):ℝ)/20) (2+(((164:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 164 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 164 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((164:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 165 := by
    rw [show (1+(((164:ℕ):ℝ)+1)/20) = 1+((165:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 165 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((164:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((164:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 164:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 165:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 164:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 165:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 165 = 110/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+164/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+165/20) - v), hv0]

theorem hptE_165 : ∀ v ∈ Set.Ico (2+((165:ℕ):ℝ)/20) (2+(((165:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 165 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 165 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((165:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 166 := by
    rw [show (1+(((165:ℕ):ℝ)+1)/20) = 1+((166:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 166 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((165:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((165:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 165:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 166:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 165:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 166:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 166 = 108/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+165/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+166/20) - v), hv0]

theorem hptE_166 : ∀ v ∈ Set.Ico (2+((166:ℕ):ℝ)/20) (2+(((166:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 166 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 166 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((166:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 167 := by
    rw [show (1+(((166:ℕ):ℝ)+1)/20) = 1+((167:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 167 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((166:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((166:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 166:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 167:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 166:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 167:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 167 = 106/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+166/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+167/20) - v), hv0]

theorem hptE_167 : ∀ v ∈ Set.Ico (2+((167:ℕ):ℝ)/20) (2+(((167:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 167 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 167 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((167:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 168 := by
    rw [show (1+(((167:ℕ):ℝ)+1)/20) = 1+((168:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 168 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((167:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((167:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 167:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 168:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 167:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 168:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 168 = 104/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+167/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+168/20) - v), hv0]

theorem hptE_168 : ∀ v ∈ Set.Ico (2+((168:ℕ):ℝ)/20) (2+(((168:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 168 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 168 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((168:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 169 := by
    rw [show (1+(((168:ℕ):ℝ)+1)/20) = 1+((169:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 169 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((168:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((168:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 168:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 169:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 168:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 169:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 169 = 102/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+168/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+169/20) - v), hv0]

theorem hptE_169 : ∀ v ∈ Set.Ico (2+((169:ℕ):ℝ)/20) (2+(((169:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 169 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 169 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((169:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 170 := by
    rw [show (1+(((169:ℕ):ℝ)+1)/20) = 1+((170:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 170 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((169:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((169:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 169:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 170:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 169:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 170:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 170 = 100/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+169/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+170/20) - v), hv0]

theorem hptE_170 : ∀ v ∈ Set.Ico (2+((170:ℕ):ℝ)/20) (2+(((170:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 170 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 170 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((170:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 171 := by
    rw [show (1+(((170:ℕ):ℝ)+1)/20) = 1+((171:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 171 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((170:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((170:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 170:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 171:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 170:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 171:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 171 = 98/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+170/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+171/20) - v), hv0]

theorem hptE_171 : ∀ v ∈ Set.Ico (2+((171:ℕ):ℝ)/20) (2+(((171:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 171 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 171 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((171:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 172 := by
    rw [show (1+(((171:ℕ):ℝ)+1)/20) = 1+((172:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 172 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((171:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((171:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 171:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 172:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 171:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 172:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 172 = 96/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+171/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+172/20) - v), hv0]

theorem hptE_172 : ∀ v ∈ Set.Ico (2+((172:ℕ):ℝ)/20) (2+(((172:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 172 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 172 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((172:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 173 := by
    rw [show (1+(((172:ℕ):ℝ)+1)/20) = 1+((173:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 173 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((172:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((172:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 172:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 173:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 172:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 173:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 173 = 94/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+172/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+173/20) - v), hv0]

theorem hptE_173 : ∀ v ∈ Set.Ico (2+((173:ℕ):ℝ)/20) (2+(((173:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 173 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 173 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((173:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 174 := by
    rw [show (1+(((173:ℕ):ℝ)+1)/20) = 1+((174:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 174 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((173:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((173:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 173:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 174:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 173:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 174:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 174 = 92/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+173/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+174/20) - v), hv0]

theorem hptE_174 : ∀ v ∈ Set.Ico (2+((174:ℕ):ℝ)/20) (2+(((174:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 174 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 174 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((174:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 175 := by
    rw [show (1+(((174:ℕ):ℝ)+1)/20) = 1+((175:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 175 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((174:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((174:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 174:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 175:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 174:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 175:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 175 = 90/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+174/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+175/20) - v), hv0]

theorem hptE_175 : ∀ v ∈ Set.Ico (2+((175:ℕ):ℝ)/20) (2+(((175:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 175 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 175 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((175:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 176 := by
    rw [show (1+(((175:ℕ):ℝ)+1)/20) = 1+((176:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 176 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((175:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((175:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 175:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 176:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 175:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 176:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 176 = 88/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+175/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+176/20) - v), hv0]

theorem hptE_176 : ∀ v ∈ Set.Ico (2+((176:ℕ):ℝ)/20) (2+(((176:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 176 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 176 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((176:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 177 := by
    rw [show (1+(((176:ℕ):ℝ)+1)/20) = 1+((177:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 177 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((176:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((176:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 176:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 177:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 176:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 177:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 177 = 86/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+176/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+177/20) - v), hv0]

theorem hptE_177 : ∀ v ∈ Set.Ico (2+((177:ℕ):ℝ)/20) (2+(((177:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 177 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 177 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((177:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 178 := by
    rw [show (1+(((177:ℕ):ℝ)+1)/20) = 1+((178:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 178 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((177:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((177:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 177:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 178:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 177:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 178:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 178 = 84/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+177/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+178/20) - v), hv0]

theorem hptE_178 : ∀ v ∈ Set.Ico (2+((178:ℕ):ℝ)/20) (2+(((178:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 178 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 178 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((178:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 179 := by
    rw [show (1+(((178:ℕ):ℝ)+1)/20) = 1+((179:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 179 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((178:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((178:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 178:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 179:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 178:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 179:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 179 = 82/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+178/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+179/20) - v), hv0]

theorem hptE_179 : ∀ v ∈ Set.Ico (2+((179:ℕ):ℝ)/20) (2+(((179:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 179 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 179 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((179:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 180 := by
    rw [show (1+(((179:ℕ):ℝ)+1)/20) = 1+((180:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 180 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((179:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((179:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 179:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 180:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 179:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 180:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 180 = 80/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+179/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+180/20) - v), hv0]

theorem hptE_180 : ∀ v ∈ Set.Ico (2+((180:ℕ):ℝ)/20) (2+(((180:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 180 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 180 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((180:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 181 := by
    rw [show (1+(((180:ℕ):ℝ)+1)/20) = 1+((181:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 181 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((180:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((180:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 180:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 181:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 180:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 181:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 181 = 78/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+180/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+181/20) - v), hv0]

theorem hptE_181 : ∀ v ∈ Set.Ico (2+((181:ℕ):ℝ)/20) (2+(((181:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 181 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 181 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((181:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 182 := by
    rw [show (1+(((181:ℕ):ℝ)+1)/20) = 1+((182:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 182 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((181:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((181:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 181:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 182:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 181:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 182:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 182 = 76/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+181/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+182/20) - v), hv0]

theorem hptE_182 : ∀ v ∈ Set.Ico (2+((182:ℕ):ℝ)/20) (2+(((182:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 182 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 182 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((182:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 183 := by
    rw [show (1+(((182:ℕ):ℝ)+1)/20) = 1+((183:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 183 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((182:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((182:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 182:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 183:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 182:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 183:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 183 = 74/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+182/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+183/20) - v), hv0]

theorem hptE_183 : ∀ v ∈ Set.Ico (2+((183:ℕ):ℝ)/20) (2+(((183:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 183 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 183 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((183:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 184 := by
    rw [show (1+(((183:ℕ):ℝ)+1)/20) = 1+((184:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 184 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((183:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((183:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 183:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 184:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 183:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 184:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 184 = 72/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+183/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+184/20) - v), hv0]

theorem hptE_184 : ∀ v ∈ Set.Ico (2+((184:ℕ):ℝ)/20) (2+(((184:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 184 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 184 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((184:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 185 := by
    rw [show (1+(((184:ℕ):ℝ)+1)/20) = 1+((185:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 185 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((184:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((184:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 184:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 185:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 184:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 185:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 185 = 70/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+184/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+185/20) - v), hv0]

theorem hptE_185 : ∀ v ∈ Set.Ico (2+((185:ℕ):ℝ)/20) (2+(((185:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 185 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 185 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((185:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 186 := by
    rw [show (1+(((185:ℕ):ℝ)+1)/20) = 1+((186:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 186 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((185:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((185:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 185:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 186:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 185:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 186:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 186 = 68/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+185/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+186/20) - v), hv0]

theorem hptE_186 : ∀ v ∈ Set.Ico (2+((186:ℕ):ℝ)/20) (2+(((186:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 186 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 186 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((186:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 187 := by
    rw [show (1+(((186:ℕ):ℝ)+1)/20) = 1+((187:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 187 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((186:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((186:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 186:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 187:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 186:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 187:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 187 = 66/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+186/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+187/20) - v), hv0]

theorem hptE_187 : ∀ v ∈ Set.Ico (2+((187:ℕ):ℝ)/20) (2+(((187:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 187 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 187 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((187:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 188 := by
    rw [show (1+(((187:ℕ):ℝ)+1)/20) = 1+((188:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 188 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((187:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((187:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 187:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 188:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 187:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 188:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 188 = 64/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+187/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+188/20) - v), hv0]

theorem hptE_188 : ∀ v ∈ Set.Ico (2+((188:ℕ):ℝ)/20) (2+(((188:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 188 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 188 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((188:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 189 := by
    rw [show (1+(((188:ℕ):ℝ)+1)/20) = 1+((189:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 189 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((188:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((188:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 188:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 189:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 188:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 189:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 189 = 62/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+188/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+189/20) - v), hv0]

theorem hptE_189 : ∀ v ∈ Set.Ico (2+((189:ℕ):ℝ)/20) (2+(((189:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 189 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 189 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((189:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 190 := by
    rw [show (1+(((189:ℕ):ℝ)+1)/20) = 1+((190:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 190 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((189:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((189:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 189:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 190:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 189:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 190:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 190 = 60/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+189/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+190/20) - v), hv0]

theorem hptE_190 : ∀ v ∈ Set.Ico (2+((190:ℕ):ℝ)/20) (2+(((190:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 190 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 190 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((190:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 191 := by
    rw [show (1+(((190:ℕ):ℝ)+1)/20) = 1+((191:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 191 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((190:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((190:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 190:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 191:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 190:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 191:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 191 = 58/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+190/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+191/20) - v), hv0]

theorem hptE_191 : ∀ v ∈ Set.Ico (2+((191:ℕ):ℝ)/20) (2+(((191:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 191 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 191 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((191:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 192 := by
    rw [show (1+(((191:ℕ):ℝ)+1)/20) = 1+((192:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 192 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((191:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((191:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 191:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 192:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 191:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 192:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 192 = 56/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+191/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+192/20) - v), hv0]

theorem hptE_192 : ∀ v ∈ Set.Ico (2+((192:ℕ):ℝ)/20) (2+(((192:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 192 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 192 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((192:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 193 := by
    rw [show (1+(((192:ℕ):ℝ)+1)/20) = 1+((193:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 193 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((192:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((192:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 192:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 193:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 192:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 193:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 193 = 54/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+192/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+193/20) - v), hv0]

theorem hptE_193 : ∀ v ∈ Set.Ico (2+((193:ℕ):ℝ)/20) (2+(((193:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 193 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 193 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((193:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 194 := by
    rw [show (1+(((193:ℕ):ℝ)+1)/20) = 1+((194:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 194 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((193:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((193:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 193:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 194:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 193:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 194:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 194 = 52/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+193/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+194/20) - v), hv0]

theorem hptE_194 : ∀ v ∈ Set.Ico (2+((194:ℕ):ℝ)/20) (2+(((194:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 194 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 194 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((194:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 195 := by
    rw [show (1+(((194:ℕ):ℝ)+1)/20) = 1+((195:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 195 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((194:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((194:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 194:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 195:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 194:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 195:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 195 = 50/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+194/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+195/20) - v), hv0]

theorem hptE_195 : ∀ v ∈ Set.Ico (2+((195:ℕ):ℝ)/20) (2+(((195:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 195 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 195 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((195:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 196 := by
    rw [show (1+(((195:ℕ):ℝ)+1)/20) = 1+((196:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 196 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((195:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((195:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 195:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 196:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 195:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 196:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 196 = 48/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+195/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+196/20) - v), hv0]

theorem hptE_196 : ∀ v ∈ Set.Ico (2+((196:ℕ):ℝ)/20) (2+(((196:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 196 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 196 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((196:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 197 := by
    rw [show (1+(((196:ℕ):ℝ)+1)/20) = 1+((197:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 197 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((196:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((196:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 196:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 197:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 196:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 197:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 197 = 46/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+196/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+197/20) - v), hv0]

theorem hptE_197 : ∀ v ∈ Set.Ico (2+((197:ℕ):ℝ)/20) (2+(((197:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 197 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 197 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((197:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 198 := by
    rw [show (1+(((197:ℕ):ℝ)+1)/20) = 1+((198:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 198 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((197:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((197:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 197:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 198:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 197:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 198:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 198 = 44/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+197/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+198/20) - v), hv0]

theorem hptE_198 : ∀ v ∈ Set.Ico (2+((198:ℕ):ℝ)/20) (2+(((198:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 198 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 198 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((198:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 199 := by
    rw [show (1+(((198:ℕ):ℝ)+1)/20) = 1+((199:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 199 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((198:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((198:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 198:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 199:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 198:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 199:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 199 = 42/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+198/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+199/20) - v), hv0]

theorem hptE_199 : ∀ v ∈ Set.Ico (2+((199:ℕ):ℝ)/20) (2+(((199:ℕ):ℝ)+1)/20),
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  rintro v ⟨hvl, hvr⟩
  have hv0 : (0:ℝ) < v := by push_cast at hvl; linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast at hvl ⊢; linarith)
  have hE := Ebar_panel_eq 199 (by norm_num) v ⟨hvl, hvr⟩
  have hx12 : v - 1 ≤ 12 := by push_cast at hvr; linarith
  have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
    unfold TObar; rw [if_pos hx12]
  have hpart := Obar_partial 199 (by norm_num) (v-1) (by push_cast at hvl ⊢; linarith) (by push_cast at hvr ⊢; linarith)
  have hsuf : (∫ w in (1+(((199:ℕ):ℝ)+1)/20)..12, Obar w) = sufKnots 200 := by
    rw [show (1+(((199:ℕ):ℝ)+1)/20) = 1+((200:ℕ):ℝ)/20 by push_cast; norm_num]
    exact Obar_suffix 200 (by norm_num)
  have hsplit : (∫ w in (v-1)..12, Obar w)
      = (∫ w in (v-1)..(1+(((199:ℕ):ℝ)+1)/20), Obar w)
        + (∫ w in (1+(((199:ℕ):ℝ)+1)/20)..12, Obar w) :=
    (intervalIntegral.integral_add_adjacent_intervals (Obar_intervalIntegrable _ _) (Obar_intervalIntegrable _ _)).symm
  have oki : (ObarKnots 199:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have oki1 : (ObarKnots 200:ℝ) = 1/10000000 := by norm_num [ObarKnots, ObarNum, obarNumList]
  have eki : (EbarKnots 199:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have eki1 : (EbarKnots 200:ℝ) = 1/10000000 := by norm_num [EbarKnots, EbarNum, ebarNumList]
  have hsufv : sufKnots 200 = 40/400000000 := by norm_num [sufKnots, sufNumList]
  rw [hf2, hE, hTOe, hsplit, hpart, hsuf, hsufv, oki, oki1, eki, eki1, zero_add,
      one_div_mul_eq_div, div_le_iff₀ hv0]
  push_cast
  nlinarith [mul_nonneg (by push_cast at hvl; linarith : (0:ℝ) ≤ v - (2+199/20))
    (by push_cast at hvr; linarith : (0:ℝ) ≤ (2+200/20) - v), hv0]

/-! ## The `v ≥ 12` power-tail seam -/

theorem hptE_tail : ∀ v, (12:ℝ) ≤ v → fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  intro v hv
  have hv0 : (0:ℝ) < v := by linarith
  have hf2 : fseq 2 v = 0 := fseq_eq_zero_of_ge 2 v (by push_cast; linarith)
  have hE : Ebar v = (1/10000)/v^3 := Ebar_tail_eq v hv
  rw [hf2, hE, zero_add]
  by_cases hx12 : v - 1 ≤ 12
  · have hTOe : TObar (v-1) = (∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2) := by
      unfold TObar; rw [if_pos hx12]
    have hge11 : (11:ℝ) ≤ v-1 := by linarith
    have hint : (∫ w in (v-1)..12, Obar w) ≤ (∫ w in (11:ℝ)..12, Obar w) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
            (Obar_intervalIntegrable 11 (v-1)) (Obar_intervalIntegrable (v-1) 12)]
      have h0 : (0:ℝ) ≤ ∫ w in (11:ℝ)..(v-1), Obar w :=
        intervalIntegral.integral_nonneg hge11 (fun t _ => Obar_nonneg t)
      linarith
    have h1112 : (∫ w in (11:ℝ)..12, Obar w) = sufKnots 200 := by
      have hh := Obar_suffix 200 (by norm_num)
      rwa [show (1+((200:ℕ):ℝ)/20) = 11 by norm_num] at hh
    have hsufv : sufKnots 200 = 1/10000000 := by norm_num [sufKnots, sufNumList]
    have hle : (∫ w in (v-1)..12, Obar w) ≤ 1/10000000 := by rw [← hsufv, ← h1112]; exact hint
    rw [hTOe]
    have hstep : (1/v)*((∫ w in (v-1)..12, Obar w) + (1/10000)/(2*12^2))
        ≤ (1/v)*(1/10000000 + (1/10000)/(2*12^2)) :=
      mul_le_mul_of_nonneg_left (by linarith [hle]) (by positivity)
    have hfin : (1/v)*(1/10000000 + (1/10000)/(2*12^2)) ≤ (1/10000)/v^3 := by
      rw [show (1/v)*((1/10000000:ℝ) + (1/10000)/(2*12^2)) = ((1/10000000:ℝ) + (1/10000)/(2*12^2))/v by ring,
          div_le_div_iff₀ hv0 (by positivity)]
      nlinarith [hv, hx12, hv0, sq_nonneg v, mul_pos hv0 hv0]
    linarith [hstep, hfin]
  · replace hx12 : (12:ℝ) < v - 1 := not_le.mp hx12
    have hv1 : (0:ℝ) < v-1 := by linarith
    have hTOe : TObar (v-1) = (1/10000)/(2*(v-1)^2) := by
      unfold TObar; rw [if_neg (by linarith)]
    rw [hTOe,
        show (1/v)*((1/10000:ℝ)/(2*(v-1)^2)) = (1/10000:ℝ)/(2*v*(v-1)^2) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (v-2), hx12, hv0, hv1, mul_pos hv0 (mul_pos hv1 hv1)]

/-! ## The panel dispatch and `hSE_holds` -/

/-- Panel dispatch for `v ∈ [2+0/20, 2+20/20)` (panels 0..19). -/
theorem hpt_disp_0 (v : ℝ)
    (hlo : 2+((0:ℕ):ℝ)/20 ≤ v) (hhi : v < 2+((20:ℕ):ℝ)/20) :
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  have hlow0 : 2+((0:ℕ):ℝ)/20 ≤ v := hlo
  by_cases hcut0 : v < 2+(((0:ℕ):ℝ)+1)/20
  · exact hptE_0 v ⟨hlow0, hcut0⟩
  replace hcut0 : 2+(((0:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut0
  have hlow1 : 2+((1:ℕ):ℝ)/20 ≤ v := by push_cast at hcut0 ⊢; linarith
  by_cases hcut1 : v < 2+(((1:ℕ):ℝ)+1)/20
  · exact hptE_1 v ⟨hlow1, hcut1⟩
  replace hcut1 : 2+(((1:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut1
  have hlow2 : 2+((2:ℕ):ℝ)/20 ≤ v := by push_cast at hcut1 ⊢; linarith
  by_cases hcut2 : v < 2+(((2:ℕ):ℝ)+1)/20
  · exact hptE_2 v ⟨hlow2, hcut2⟩
  replace hcut2 : 2+(((2:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut2
  have hlow3 : 2+((3:ℕ):ℝ)/20 ≤ v := by push_cast at hcut2 ⊢; linarith
  by_cases hcut3 : v < 2+(((3:ℕ):ℝ)+1)/20
  · exact hptE_3 v ⟨hlow3, hcut3⟩
  replace hcut3 : 2+(((3:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut3
  have hlow4 : 2+((4:ℕ):ℝ)/20 ≤ v := by push_cast at hcut3 ⊢; linarith
  by_cases hcut4 : v < 2+(((4:ℕ):ℝ)+1)/20
  · exact hptE_4 v ⟨hlow4, hcut4⟩
  replace hcut4 : 2+(((4:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut4
  have hlow5 : 2+((5:ℕ):ℝ)/20 ≤ v := by push_cast at hcut4 ⊢; linarith
  by_cases hcut5 : v < 2+(((5:ℕ):ℝ)+1)/20
  · exact hptE_5 v ⟨hlow5, hcut5⟩
  replace hcut5 : 2+(((5:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut5
  have hlow6 : 2+((6:ℕ):ℝ)/20 ≤ v := by push_cast at hcut5 ⊢; linarith
  by_cases hcut6 : v < 2+(((6:ℕ):ℝ)+1)/20
  · exact hptE_6 v ⟨hlow6, hcut6⟩
  replace hcut6 : 2+(((6:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut6
  have hlow7 : 2+((7:ℕ):ℝ)/20 ≤ v := by push_cast at hcut6 ⊢; linarith
  by_cases hcut7 : v < 2+(((7:ℕ):ℝ)+1)/20
  · exact hptE_7 v ⟨hlow7, hcut7⟩
  replace hcut7 : 2+(((7:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut7
  have hlow8 : 2+((8:ℕ):ℝ)/20 ≤ v := by push_cast at hcut7 ⊢; linarith
  by_cases hcut8 : v < 2+(((8:ℕ):ℝ)+1)/20
  · exact hptE_8 v ⟨hlow8, hcut8⟩
  replace hcut8 : 2+(((8:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut8
  have hlow9 : 2+((9:ℕ):ℝ)/20 ≤ v := by push_cast at hcut8 ⊢; linarith
  by_cases hcut9 : v < 2+(((9:ℕ):ℝ)+1)/20
  · exact hptE_9 v ⟨hlow9, hcut9⟩
  replace hcut9 : 2+(((9:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut9
  have hlow10 : 2+((10:ℕ):ℝ)/20 ≤ v := by push_cast at hcut9 ⊢; linarith
  by_cases hcut10 : v < 2+(((10:ℕ):ℝ)+1)/20
  · exact hptE_10 v ⟨hlow10, hcut10⟩
  replace hcut10 : 2+(((10:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut10
  have hlow11 : 2+((11:ℕ):ℝ)/20 ≤ v := by push_cast at hcut10 ⊢; linarith
  by_cases hcut11 : v < 2+(((11:ℕ):ℝ)+1)/20
  · exact hptE_11 v ⟨hlow11, hcut11⟩
  replace hcut11 : 2+(((11:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut11
  have hlow12 : 2+((12:ℕ):ℝ)/20 ≤ v := by push_cast at hcut11 ⊢; linarith
  by_cases hcut12 : v < 2+(((12:ℕ):ℝ)+1)/20
  · exact hptE_12 v ⟨hlow12, hcut12⟩
  replace hcut12 : 2+(((12:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut12
  have hlow13 : 2+((13:ℕ):ℝ)/20 ≤ v := by push_cast at hcut12 ⊢; linarith
  by_cases hcut13 : v < 2+(((13:ℕ):ℝ)+1)/20
  · exact hptE_13 v ⟨hlow13, hcut13⟩
  replace hcut13 : 2+(((13:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut13
  have hlow14 : 2+((14:ℕ):ℝ)/20 ≤ v := by push_cast at hcut13 ⊢; linarith
  by_cases hcut14 : v < 2+(((14:ℕ):ℝ)+1)/20
  · exact hptE_14 v ⟨hlow14, hcut14⟩
  replace hcut14 : 2+(((14:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut14
  have hlow15 : 2+((15:ℕ):ℝ)/20 ≤ v := by push_cast at hcut14 ⊢; linarith
  by_cases hcut15 : v < 2+(((15:ℕ):ℝ)+1)/20
  · exact hptE_15 v ⟨hlow15, hcut15⟩
  replace hcut15 : 2+(((15:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut15
  have hlow16 : 2+((16:ℕ):ℝ)/20 ≤ v := by push_cast at hcut15 ⊢; linarith
  by_cases hcut16 : v < 2+(((16:ℕ):ℝ)+1)/20
  · exact hptE_16 v ⟨hlow16, hcut16⟩
  replace hcut16 : 2+(((16:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut16
  have hlow17 : 2+((17:ℕ):ℝ)/20 ≤ v := by push_cast at hcut16 ⊢; linarith
  by_cases hcut17 : v < 2+(((17:ℕ):ℝ)+1)/20
  · exact hptE_17 v ⟨hlow17, hcut17⟩
  replace hcut17 : 2+(((17:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut17
  have hlow18 : 2+((18:ℕ):ℝ)/20 ≤ v := by push_cast at hcut17 ⊢; linarith
  by_cases hcut18 : v < 2+(((18:ℕ):ℝ)+1)/20
  · exact hptE_18 v ⟨hlow18, hcut18⟩
  replace hcut18 : 2+(((18:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut18
  have hlow19 : 2+((19:ℕ):ℝ)/20 ≤ v := by push_cast at hcut18 ⊢; linarith
  exact hptE_19 v ⟨hlow19, by push_cast at hhi ⊢; linarith⟩

/-- Panel dispatch for `v ∈ [2+20/20, 2+40/20)` (panels 20..39). -/
theorem hpt_disp_1 (v : ℝ)
    (hlo : 2+((20:ℕ):ℝ)/20 ≤ v) (hhi : v < 2+((40:ℕ):ℝ)/20) :
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  have hlow20 : 2+((20:ℕ):ℝ)/20 ≤ v := hlo
  by_cases hcut20 : v < 2+(((20:ℕ):ℝ)+1)/20
  · exact hptE_20 v ⟨hlow20, hcut20⟩
  replace hcut20 : 2+(((20:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut20
  have hlow21 : 2+((21:ℕ):ℝ)/20 ≤ v := by push_cast at hcut20 ⊢; linarith
  by_cases hcut21 : v < 2+(((21:ℕ):ℝ)+1)/20
  · exact hptE_21 v ⟨hlow21, hcut21⟩
  replace hcut21 : 2+(((21:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut21
  have hlow22 : 2+((22:ℕ):ℝ)/20 ≤ v := by push_cast at hcut21 ⊢; linarith
  by_cases hcut22 : v < 2+(((22:ℕ):ℝ)+1)/20
  · exact hptE_22 v ⟨hlow22, hcut22⟩
  replace hcut22 : 2+(((22:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut22
  have hlow23 : 2+((23:ℕ):ℝ)/20 ≤ v := by push_cast at hcut22 ⊢; linarith
  by_cases hcut23 : v < 2+(((23:ℕ):ℝ)+1)/20
  · exact hptE_23 v ⟨hlow23, hcut23⟩
  replace hcut23 : 2+(((23:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut23
  have hlow24 : 2+((24:ℕ):ℝ)/20 ≤ v := by push_cast at hcut23 ⊢; linarith
  by_cases hcut24 : v < 2+(((24:ℕ):ℝ)+1)/20
  · exact hptE_24 v ⟨hlow24, hcut24⟩
  replace hcut24 : 2+(((24:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut24
  have hlow25 : 2+((25:ℕ):ℝ)/20 ≤ v := by push_cast at hcut24 ⊢; linarith
  by_cases hcut25 : v < 2+(((25:ℕ):ℝ)+1)/20
  · exact hptE_25 v ⟨hlow25, hcut25⟩
  replace hcut25 : 2+(((25:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut25
  have hlow26 : 2+((26:ℕ):ℝ)/20 ≤ v := by push_cast at hcut25 ⊢; linarith
  by_cases hcut26 : v < 2+(((26:ℕ):ℝ)+1)/20
  · exact hptE_26 v ⟨hlow26, hcut26⟩
  replace hcut26 : 2+(((26:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut26
  have hlow27 : 2+((27:ℕ):ℝ)/20 ≤ v := by push_cast at hcut26 ⊢; linarith
  by_cases hcut27 : v < 2+(((27:ℕ):ℝ)+1)/20
  · exact hptE_27 v ⟨hlow27, hcut27⟩
  replace hcut27 : 2+(((27:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut27
  have hlow28 : 2+((28:ℕ):ℝ)/20 ≤ v := by push_cast at hcut27 ⊢; linarith
  by_cases hcut28 : v < 2+(((28:ℕ):ℝ)+1)/20
  · exact hptE_28 v ⟨hlow28, hcut28⟩
  replace hcut28 : 2+(((28:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut28
  have hlow29 : 2+((29:ℕ):ℝ)/20 ≤ v := by push_cast at hcut28 ⊢; linarith
  by_cases hcut29 : v < 2+(((29:ℕ):ℝ)+1)/20
  · exact hptE_29 v ⟨hlow29, hcut29⟩
  replace hcut29 : 2+(((29:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut29
  have hlow30 : 2+((30:ℕ):ℝ)/20 ≤ v := by push_cast at hcut29 ⊢; linarith
  by_cases hcut30 : v < 2+(((30:ℕ):ℝ)+1)/20
  · exact hptE_30 v ⟨hlow30, hcut30⟩
  replace hcut30 : 2+(((30:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut30
  have hlow31 : 2+((31:ℕ):ℝ)/20 ≤ v := by push_cast at hcut30 ⊢; linarith
  by_cases hcut31 : v < 2+(((31:ℕ):ℝ)+1)/20
  · exact hptE_31 v ⟨hlow31, hcut31⟩
  replace hcut31 : 2+(((31:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut31
  have hlow32 : 2+((32:ℕ):ℝ)/20 ≤ v := by push_cast at hcut31 ⊢; linarith
  by_cases hcut32 : v < 2+(((32:ℕ):ℝ)+1)/20
  · exact hptE_32 v ⟨hlow32, hcut32⟩
  replace hcut32 : 2+(((32:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut32
  have hlow33 : 2+((33:ℕ):ℝ)/20 ≤ v := by push_cast at hcut32 ⊢; linarith
  by_cases hcut33 : v < 2+(((33:ℕ):ℝ)+1)/20
  · exact hptE_33 v ⟨hlow33, hcut33⟩
  replace hcut33 : 2+(((33:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut33
  have hlow34 : 2+((34:ℕ):ℝ)/20 ≤ v := by push_cast at hcut33 ⊢; linarith
  by_cases hcut34 : v < 2+(((34:ℕ):ℝ)+1)/20
  · exact hptE_34 v ⟨hlow34, hcut34⟩
  replace hcut34 : 2+(((34:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut34
  have hlow35 : 2+((35:ℕ):ℝ)/20 ≤ v := by push_cast at hcut34 ⊢; linarith
  by_cases hcut35 : v < 2+(((35:ℕ):ℝ)+1)/20
  · exact hptE_35 v ⟨hlow35, hcut35⟩
  replace hcut35 : 2+(((35:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut35
  have hlow36 : 2+((36:ℕ):ℝ)/20 ≤ v := by push_cast at hcut35 ⊢; linarith
  by_cases hcut36 : v < 2+(((36:ℕ):ℝ)+1)/20
  · exact hptE_36 v ⟨hlow36, hcut36⟩
  replace hcut36 : 2+(((36:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut36
  have hlow37 : 2+((37:ℕ):ℝ)/20 ≤ v := by push_cast at hcut36 ⊢; linarith
  by_cases hcut37 : v < 2+(((37:ℕ):ℝ)+1)/20
  · exact hptE_37 v ⟨hlow37, hcut37⟩
  replace hcut37 : 2+(((37:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut37
  have hlow38 : 2+((38:ℕ):ℝ)/20 ≤ v := by push_cast at hcut37 ⊢; linarith
  by_cases hcut38 : v < 2+(((38:ℕ):ℝ)+1)/20
  · exact hptE_38 v ⟨hlow38, hcut38⟩
  replace hcut38 : 2+(((38:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut38
  have hlow39 : 2+((39:ℕ):ℝ)/20 ≤ v := by push_cast at hcut38 ⊢; linarith
  exact hptE_39 v ⟨hlow39, by push_cast at hhi ⊢; linarith⟩

/-- Panel dispatch for `v ∈ [2+40/20, 2+60/20)` (panels 40..59). -/
theorem hpt_disp_2 (v : ℝ)
    (hlo : 2+((40:ℕ):ℝ)/20 ≤ v) (hhi : v < 2+((60:ℕ):ℝ)/20) :
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  have hlow40 : 2+((40:ℕ):ℝ)/20 ≤ v := hlo
  by_cases hcut40 : v < 2+(((40:ℕ):ℝ)+1)/20
  · exact hptE_40 v ⟨hlow40, hcut40⟩
  replace hcut40 : 2+(((40:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut40
  have hlow41 : 2+((41:ℕ):ℝ)/20 ≤ v := by push_cast at hcut40 ⊢; linarith
  by_cases hcut41 : v < 2+(((41:ℕ):ℝ)+1)/20
  · exact hptE_41 v ⟨hlow41, hcut41⟩
  replace hcut41 : 2+(((41:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut41
  have hlow42 : 2+((42:ℕ):ℝ)/20 ≤ v := by push_cast at hcut41 ⊢; linarith
  by_cases hcut42 : v < 2+(((42:ℕ):ℝ)+1)/20
  · exact hptE_42 v ⟨hlow42, hcut42⟩
  replace hcut42 : 2+(((42:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut42
  have hlow43 : 2+((43:ℕ):ℝ)/20 ≤ v := by push_cast at hcut42 ⊢; linarith
  by_cases hcut43 : v < 2+(((43:ℕ):ℝ)+1)/20
  · exact hptE_43 v ⟨hlow43, hcut43⟩
  replace hcut43 : 2+(((43:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut43
  have hlow44 : 2+((44:ℕ):ℝ)/20 ≤ v := by push_cast at hcut43 ⊢; linarith
  by_cases hcut44 : v < 2+(((44:ℕ):ℝ)+1)/20
  · exact hptE_44 v ⟨hlow44, hcut44⟩
  replace hcut44 : 2+(((44:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut44
  have hlow45 : 2+((45:ℕ):ℝ)/20 ≤ v := by push_cast at hcut44 ⊢; linarith
  by_cases hcut45 : v < 2+(((45:ℕ):ℝ)+1)/20
  · exact hptE_45 v ⟨hlow45, hcut45⟩
  replace hcut45 : 2+(((45:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut45
  have hlow46 : 2+((46:ℕ):ℝ)/20 ≤ v := by push_cast at hcut45 ⊢; linarith
  by_cases hcut46 : v < 2+(((46:ℕ):ℝ)+1)/20
  · exact hptE_46 v ⟨hlow46, hcut46⟩
  replace hcut46 : 2+(((46:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut46
  have hlow47 : 2+((47:ℕ):ℝ)/20 ≤ v := by push_cast at hcut46 ⊢; linarith
  by_cases hcut47 : v < 2+(((47:ℕ):ℝ)+1)/20
  · exact hptE_47 v ⟨hlow47, hcut47⟩
  replace hcut47 : 2+(((47:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut47
  have hlow48 : 2+((48:ℕ):ℝ)/20 ≤ v := by push_cast at hcut47 ⊢; linarith
  by_cases hcut48 : v < 2+(((48:ℕ):ℝ)+1)/20
  · exact hptE_48 v ⟨hlow48, hcut48⟩
  replace hcut48 : 2+(((48:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut48
  have hlow49 : 2+((49:ℕ):ℝ)/20 ≤ v := by push_cast at hcut48 ⊢; linarith
  by_cases hcut49 : v < 2+(((49:ℕ):ℝ)+1)/20
  · exact hptE_49 v ⟨hlow49, hcut49⟩
  replace hcut49 : 2+(((49:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut49
  have hlow50 : 2+((50:ℕ):ℝ)/20 ≤ v := by push_cast at hcut49 ⊢; linarith
  by_cases hcut50 : v < 2+(((50:ℕ):ℝ)+1)/20
  · exact hptE_50 v ⟨hlow50, hcut50⟩
  replace hcut50 : 2+(((50:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut50
  have hlow51 : 2+((51:ℕ):ℝ)/20 ≤ v := by push_cast at hcut50 ⊢; linarith
  by_cases hcut51 : v < 2+(((51:ℕ):ℝ)+1)/20
  · exact hptE_51 v ⟨hlow51, hcut51⟩
  replace hcut51 : 2+(((51:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut51
  have hlow52 : 2+((52:ℕ):ℝ)/20 ≤ v := by push_cast at hcut51 ⊢; linarith
  by_cases hcut52 : v < 2+(((52:ℕ):ℝ)+1)/20
  · exact hptE_52 v ⟨hlow52, hcut52⟩
  replace hcut52 : 2+(((52:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut52
  have hlow53 : 2+((53:ℕ):ℝ)/20 ≤ v := by push_cast at hcut52 ⊢; linarith
  by_cases hcut53 : v < 2+(((53:ℕ):ℝ)+1)/20
  · exact hptE_53 v ⟨hlow53, hcut53⟩
  replace hcut53 : 2+(((53:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut53
  have hlow54 : 2+((54:ℕ):ℝ)/20 ≤ v := by push_cast at hcut53 ⊢; linarith
  by_cases hcut54 : v < 2+(((54:ℕ):ℝ)+1)/20
  · exact hptE_54 v ⟨hlow54, hcut54⟩
  replace hcut54 : 2+(((54:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut54
  have hlow55 : 2+((55:ℕ):ℝ)/20 ≤ v := by push_cast at hcut54 ⊢; linarith
  by_cases hcut55 : v < 2+(((55:ℕ):ℝ)+1)/20
  · exact hptE_55 v ⟨hlow55, hcut55⟩
  replace hcut55 : 2+(((55:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut55
  have hlow56 : 2+((56:ℕ):ℝ)/20 ≤ v := by push_cast at hcut55 ⊢; linarith
  by_cases hcut56 : v < 2+(((56:ℕ):ℝ)+1)/20
  · exact hptE_56 v ⟨hlow56, hcut56⟩
  replace hcut56 : 2+(((56:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut56
  have hlow57 : 2+((57:ℕ):ℝ)/20 ≤ v := by push_cast at hcut56 ⊢; linarith
  by_cases hcut57 : v < 2+(((57:ℕ):ℝ)+1)/20
  · exact hptE_57 v ⟨hlow57, hcut57⟩
  replace hcut57 : 2+(((57:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut57
  have hlow58 : 2+((58:ℕ):ℝ)/20 ≤ v := by push_cast at hcut57 ⊢; linarith
  by_cases hcut58 : v < 2+(((58:ℕ):ℝ)+1)/20
  · exact hptE_58 v ⟨hlow58, hcut58⟩
  replace hcut58 : 2+(((58:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut58
  have hlow59 : 2+((59:ℕ):ℝ)/20 ≤ v := by push_cast at hcut58 ⊢; linarith
  exact hptE_59 v ⟨hlow59, by push_cast at hhi ⊢; linarith⟩

/-- Panel dispatch for `v ∈ [2+60/20, 2+80/20)` (panels 60..79). -/
theorem hpt_disp_3 (v : ℝ)
    (hlo : 2+((60:ℕ):ℝ)/20 ≤ v) (hhi : v < 2+((80:ℕ):ℝ)/20) :
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  have hlow60 : 2+((60:ℕ):ℝ)/20 ≤ v := hlo
  by_cases hcut60 : v < 2+(((60:ℕ):ℝ)+1)/20
  · exact hptE_60 v ⟨hlow60, hcut60⟩
  replace hcut60 : 2+(((60:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut60
  have hlow61 : 2+((61:ℕ):ℝ)/20 ≤ v := by push_cast at hcut60 ⊢; linarith
  by_cases hcut61 : v < 2+(((61:ℕ):ℝ)+1)/20
  · exact hptE_61 v ⟨hlow61, hcut61⟩
  replace hcut61 : 2+(((61:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut61
  have hlow62 : 2+((62:ℕ):ℝ)/20 ≤ v := by push_cast at hcut61 ⊢; linarith
  by_cases hcut62 : v < 2+(((62:ℕ):ℝ)+1)/20
  · exact hptE_62 v ⟨hlow62, hcut62⟩
  replace hcut62 : 2+(((62:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut62
  have hlow63 : 2+((63:ℕ):ℝ)/20 ≤ v := by push_cast at hcut62 ⊢; linarith
  by_cases hcut63 : v < 2+(((63:ℕ):ℝ)+1)/20
  · exact hptE_63 v ⟨hlow63, hcut63⟩
  replace hcut63 : 2+(((63:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut63
  have hlow64 : 2+((64:ℕ):ℝ)/20 ≤ v := by push_cast at hcut63 ⊢; linarith
  by_cases hcut64 : v < 2+(((64:ℕ):ℝ)+1)/20
  · exact hptE_64 v ⟨hlow64, hcut64⟩
  replace hcut64 : 2+(((64:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut64
  have hlow65 : 2+((65:ℕ):ℝ)/20 ≤ v := by push_cast at hcut64 ⊢; linarith
  by_cases hcut65 : v < 2+(((65:ℕ):ℝ)+1)/20
  · exact hptE_65 v ⟨hlow65, hcut65⟩
  replace hcut65 : 2+(((65:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut65
  have hlow66 : 2+((66:ℕ):ℝ)/20 ≤ v := by push_cast at hcut65 ⊢; linarith
  by_cases hcut66 : v < 2+(((66:ℕ):ℝ)+1)/20
  · exact hptE_66 v ⟨hlow66, hcut66⟩
  replace hcut66 : 2+(((66:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut66
  have hlow67 : 2+((67:ℕ):ℝ)/20 ≤ v := by push_cast at hcut66 ⊢; linarith
  by_cases hcut67 : v < 2+(((67:ℕ):ℝ)+1)/20
  · exact hptE_67 v ⟨hlow67, hcut67⟩
  replace hcut67 : 2+(((67:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut67
  have hlow68 : 2+((68:ℕ):ℝ)/20 ≤ v := by push_cast at hcut67 ⊢; linarith
  by_cases hcut68 : v < 2+(((68:ℕ):ℝ)+1)/20
  · exact hptE_68 v ⟨hlow68, hcut68⟩
  replace hcut68 : 2+(((68:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut68
  have hlow69 : 2+((69:ℕ):ℝ)/20 ≤ v := by push_cast at hcut68 ⊢; linarith
  by_cases hcut69 : v < 2+(((69:ℕ):ℝ)+1)/20
  · exact hptE_69 v ⟨hlow69, hcut69⟩
  replace hcut69 : 2+(((69:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut69
  have hlow70 : 2+((70:ℕ):ℝ)/20 ≤ v := by push_cast at hcut69 ⊢; linarith
  by_cases hcut70 : v < 2+(((70:ℕ):ℝ)+1)/20
  · exact hptE_70 v ⟨hlow70, hcut70⟩
  replace hcut70 : 2+(((70:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut70
  have hlow71 : 2+((71:ℕ):ℝ)/20 ≤ v := by push_cast at hcut70 ⊢; linarith
  by_cases hcut71 : v < 2+(((71:ℕ):ℝ)+1)/20
  · exact hptE_71 v ⟨hlow71, hcut71⟩
  replace hcut71 : 2+(((71:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut71
  have hlow72 : 2+((72:ℕ):ℝ)/20 ≤ v := by push_cast at hcut71 ⊢; linarith
  by_cases hcut72 : v < 2+(((72:ℕ):ℝ)+1)/20
  · exact hptE_72 v ⟨hlow72, hcut72⟩
  replace hcut72 : 2+(((72:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut72
  have hlow73 : 2+((73:ℕ):ℝ)/20 ≤ v := by push_cast at hcut72 ⊢; linarith
  by_cases hcut73 : v < 2+(((73:ℕ):ℝ)+1)/20
  · exact hptE_73 v ⟨hlow73, hcut73⟩
  replace hcut73 : 2+(((73:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut73
  have hlow74 : 2+((74:ℕ):ℝ)/20 ≤ v := by push_cast at hcut73 ⊢; linarith
  by_cases hcut74 : v < 2+(((74:ℕ):ℝ)+1)/20
  · exact hptE_74 v ⟨hlow74, hcut74⟩
  replace hcut74 : 2+(((74:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut74
  have hlow75 : 2+((75:ℕ):ℝ)/20 ≤ v := by push_cast at hcut74 ⊢; linarith
  by_cases hcut75 : v < 2+(((75:ℕ):ℝ)+1)/20
  · exact hptE_75 v ⟨hlow75, hcut75⟩
  replace hcut75 : 2+(((75:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut75
  have hlow76 : 2+((76:ℕ):ℝ)/20 ≤ v := by push_cast at hcut75 ⊢; linarith
  by_cases hcut76 : v < 2+(((76:ℕ):ℝ)+1)/20
  · exact hptE_76 v ⟨hlow76, hcut76⟩
  replace hcut76 : 2+(((76:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut76
  have hlow77 : 2+((77:ℕ):ℝ)/20 ≤ v := by push_cast at hcut76 ⊢; linarith
  by_cases hcut77 : v < 2+(((77:ℕ):ℝ)+1)/20
  · exact hptE_77 v ⟨hlow77, hcut77⟩
  replace hcut77 : 2+(((77:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut77
  have hlow78 : 2+((78:ℕ):ℝ)/20 ≤ v := by push_cast at hcut77 ⊢; linarith
  by_cases hcut78 : v < 2+(((78:ℕ):ℝ)+1)/20
  · exact hptE_78 v ⟨hlow78, hcut78⟩
  replace hcut78 : 2+(((78:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut78
  have hlow79 : 2+((79:ℕ):ℝ)/20 ≤ v := by push_cast at hcut78 ⊢; linarith
  exact hptE_79 v ⟨hlow79, by push_cast at hhi ⊢; linarith⟩

/-- Panel dispatch for `v ∈ [2+80/20, 2+100/20)` (panels 80..99). -/
theorem hpt_disp_4 (v : ℝ)
    (hlo : 2+((80:ℕ):ℝ)/20 ≤ v) (hhi : v < 2+((100:ℕ):ℝ)/20) :
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  have hlow80 : 2+((80:ℕ):ℝ)/20 ≤ v := hlo
  by_cases hcut80 : v < 2+(((80:ℕ):ℝ)+1)/20
  · exact hptE_80 v ⟨hlow80, hcut80⟩
  replace hcut80 : 2+(((80:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut80
  have hlow81 : 2+((81:ℕ):ℝ)/20 ≤ v := by push_cast at hcut80 ⊢; linarith
  by_cases hcut81 : v < 2+(((81:ℕ):ℝ)+1)/20
  · exact hptE_81 v ⟨hlow81, hcut81⟩
  replace hcut81 : 2+(((81:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut81
  have hlow82 : 2+((82:ℕ):ℝ)/20 ≤ v := by push_cast at hcut81 ⊢; linarith
  by_cases hcut82 : v < 2+(((82:ℕ):ℝ)+1)/20
  · exact hptE_82 v ⟨hlow82, hcut82⟩
  replace hcut82 : 2+(((82:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut82
  have hlow83 : 2+((83:ℕ):ℝ)/20 ≤ v := by push_cast at hcut82 ⊢; linarith
  by_cases hcut83 : v < 2+(((83:ℕ):ℝ)+1)/20
  · exact hptE_83 v ⟨hlow83, hcut83⟩
  replace hcut83 : 2+(((83:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut83
  have hlow84 : 2+((84:ℕ):ℝ)/20 ≤ v := by push_cast at hcut83 ⊢; linarith
  by_cases hcut84 : v < 2+(((84:ℕ):ℝ)+1)/20
  · exact hptE_84 v ⟨hlow84, hcut84⟩
  replace hcut84 : 2+(((84:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut84
  have hlow85 : 2+((85:ℕ):ℝ)/20 ≤ v := by push_cast at hcut84 ⊢; linarith
  by_cases hcut85 : v < 2+(((85:ℕ):ℝ)+1)/20
  · exact hptE_85 v ⟨hlow85, hcut85⟩
  replace hcut85 : 2+(((85:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut85
  have hlow86 : 2+((86:ℕ):ℝ)/20 ≤ v := by push_cast at hcut85 ⊢; linarith
  by_cases hcut86 : v < 2+(((86:ℕ):ℝ)+1)/20
  · exact hptE_86 v ⟨hlow86, hcut86⟩
  replace hcut86 : 2+(((86:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut86
  have hlow87 : 2+((87:ℕ):ℝ)/20 ≤ v := by push_cast at hcut86 ⊢; linarith
  by_cases hcut87 : v < 2+(((87:ℕ):ℝ)+1)/20
  · exact hptE_87 v ⟨hlow87, hcut87⟩
  replace hcut87 : 2+(((87:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut87
  have hlow88 : 2+((88:ℕ):ℝ)/20 ≤ v := by push_cast at hcut87 ⊢; linarith
  by_cases hcut88 : v < 2+(((88:ℕ):ℝ)+1)/20
  · exact hptE_88 v ⟨hlow88, hcut88⟩
  replace hcut88 : 2+(((88:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut88
  have hlow89 : 2+((89:ℕ):ℝ)/20 ≤ v := by push_cast at hcut88 ⊢; linarith
  by_cases hcut89 : v < 2+(((89:ℕ):ℝ)+1)/20
  · exact hptE_89 v ⟨hlow89, hcut89⟩
  replace hcut89 : 2+(((89:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut89
  have hlow90 : 2+((90:ℕ):ℝ)/20 ≤ v := by push_cast at hcut89 ⊢; linarith
  by_cases hcut90 : v < 2+(((90:ℕ):ℝ)+1)/20
  · exact hptE_90 v ⟨hlow90, hcut90⟩
  replace hcut90 : 2+(((90:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut90
  have hlow91 : 2+((91:ℕ):ℝ)/20 ≤ v := by push_cast at hcut90 ⊢; linarith
  by_cases hcut91 : v < 2+(((91:ℕ):ℝ)+1)/20
  · exact hptE_91 v ⟨hlow91, hcut91⟩
  replace hcut91 : 2+(((91:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut91
  have hlow92 : 2+((92:ℕ):ℝ)/20 ≤ v := by push_cast at hcut91 ⊢; linarith
  by_cases hcut92 : v < 2+(((92:ℕ):ℝ)+1)/20
  · exact hptE_92 v ⟨hlow92, hcut92⟩
  replace hcut92 : 2+(((92:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut92
  have hlow93 : 2+((93:ℕ):ℝ)/20 ≤ v := by push_cast at hcut92 ⊢; linarith
  by_cases hcut93 : v < 2+(((93:ℕ):ℝ)+1)/20
  · exact hptE_93 v ⟨hlow93, hcut93⟩
  replace hcut93 : 2+(((93:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut93
  have hlow94 : 2+((94:ℕ):ℝ)/20 ≤ v := by push_cast at hcut93 ⊢; linarith
  by_cases hcut94 : v < 2+(((94:ℕ):ℝ)+1)/20
  · exact hptE_94 v ⟨hlow94, hcut94⟩
  replace hcut94 : 2+(((94:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut94
  have hlow95 : 2+((95:ℕ):ℝ)/20 ≤ v := by push_cast at hcut94 ⊢; linarith
  by_cases hcut95 : v < 2+(((95:ℕ):ℝ)+1)/20
  · exact hptE_95 v ⟨hlow95, hcut95⟩
  replace hcut95 : 2+(((95:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut95
  have hlow96 : 2+((96:ℕ):ℝ)/20 ≤ v := by push_cast at hcut95 ⊢; linarith
  by_cases hcut96 : v < 2+(((96:ℕ):ℝ)+1)/20
  · exact hptE_96 v ⟨hlow96, hcut96⟩
  replace hcut96 : 2+(((96:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut96
  have hlow97 : 2+((97:ℕ):ℝ)/20 ≤ v := by push_cast at hcut96 ⊢; linarith
  by_cases hcut97 : v < 2+(((97:ℕ):ℝ)+1)/20
  · exact hptE_97 v ⟨hlow97, hcut97⟩
  replace hcut97 : 2+(((97:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut97
  have hlow98 : 2+((98:ℕ):ℝ)/20 ≤ v := by push_cast at hcut97 ⊢; linarith
  by_cases hcut98 : v < 2+(((98:ℕ):ℝ)+1)/20
  · exact hptE_98 v ⟨hlow98, hcut98⟩
  replace hcut98 : 2+(((98:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut98
  have hlow99 : 2+((99:ℕ):ℝ)/20 ≤ v := by push_cast at hcut98 ⊢; linarith
  exact hptE_99 v ⟨hlow99, by push_cast at hhi ⊢; linarith⟩

/-- Panel dispatch for `v ∈ [2+100/20, 2+120/20)` (panels 100..119). -/
theorem hpt_disp_5 (v : ℝ)
    (hlo : 2+((100:ℕ):ℝ)/20 ≤ v) (hhi : v < 2+((120:ℕ):ℝ)/20) :
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  have hlow100 : 2+((100:ℕ):ℝ)/20 ≤ v := hlo
  by_cases hcut100 : v < 2+(((100:ℕ):ℝ)+1)/20
  · exact hptE_100 v ⟨hlow100, hcut100⟩
  replace hcut100 : 2+(((100:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut100
  have hlow101 : 2+((101:ℕ):ℝ)/20 ≤ v := by push_cast at hcut100 ⊢; linarith
  by_cases hcut101 : v < 2+(((101:ℕ):ℝ)+1)/20
  · exact hptE_101 v ⟨hlow101, hcut101⟩
  replace hcut101 : 2+(((101:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut101
  have hlow102 : 2+((102:ℕ):ℝ)/20 ≤ v := by push_cast at hcut101 ⊢; linarith
  by_cases hcut102 : v < 2+(((102:ℕ):ℝ)+1)/20
  · exact hptE_102 v ⟨hlow102, hcut102⟩
  replace hcut102 : 2+(((102:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut102
  have hlow103 : 2+((103:ℕ):ℝ)/20 ≤ v := by push_cast at hcut102 ⊢; linarith
  by_cases hcut103 : v < 2+(((103:ℕ):ℝ)+1)/20
  · exact hptE_103 v ⟨hlow103, hcut103⟩
  replace hcut103 : 2+(((103:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut103
  have hlow104 : 2+((104:ℕ):ℝ)/20 ≤ v := by push_cast at hcut103 ⊢; linarith
  by_cases hcut104 : v < 2+(((104:ℕ):ℝ)+1)/20
  · exact hptE_104 v ⟨hlow104, hcut104⟩
  replace hcut104 : 2+(((104:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut104
  have hlow105 : 2+((105:ℕ):ℝ)/20 ≤ v := by push_cast at hcut104 ⊢; linarith
  by_cases hcut105 : v < 2+(((105:ℕ):ℝ)+1)/20
  · exact hptE_105 v ⟨hlow105, hcut105⟩
  replace hcut105 : 2+(((105:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut105
  have hlow106 : 2+((106:ℕ):ℝ)/20 ≤ v := by push_cast at hcut105 ⊢; linarith
  by_cases hcut106 : v < 2+(((106:ℕ):ℝ)+1)/20
  · exact hptE_106 v ⟨hlow106, hcut106⟩
  replace hcut106 : 2+(((106:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut106
  have hlow107 : 2+((107:ℕ):ℝ)/20 ≤ v := by push_cast at hcut106 ⊢; linarith
  by_cases hcut107 : v < 2+(((107:ℕ):ℝ)+1)/20
  · exact hptE_107 v ⟨hlow107, hcut107⟩
  replace hcut107 : 2+(((107:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut107
  have hlow108 : 2+((108:ℕ):ℝ)/20 ≤ v := by push_cast at hcut107 ⊢; linarith
  by_cases hcut108 : v < 2+(((108:ℕ):ℝ)+1)/20
  · exact hptE_108 v ⟨hlow108, hcut108⟩
  replace hcut108 : 2+(((108:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut108
  have hlow109 : 2+((109:ℕ):ℝ)/20 ≤ v := by push_cast at hcut108 ⊢; linarith
  by_cases hcut109 : v < 2+(((109:ℕ):ℝ)+1)/20
  · exact hptE_109 v ⟨hlow109, hcut109⟩
  replace hcut109 : 2+(((109:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut109
  have hlow110 : 2+((110:ℕ):ℝ)/20 ≤ v := by push_cast at hcut109 ⊢; linarith
  by_cases hcut110 : v < 2+(((110:ℕ):ℝ)+1)/20
  · exact hptE_110 v ⟨hlow110, hcut110⟩
  replace hcut110 : 2+(((110:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut110
  have hlow111 : 2+((111:ℕ):ℝ)/20 ≤ v := by push_cast at hcut110 ⊢; linarith
  by_cases hcut111 : v < 2+(((111:ℕ):ℝ)+1)/20
  · exact hptE_111 v ⟨hlow111, hcut111⟩
  replace hcut111 : 2+(((111:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut111
  have hlow112 : 2+((112:ℕ):ℝ)/20 ≤ v := by push_cast at hcut111 ⊢; linarith
  by_cases hcut112 : v < 2+(((112:ℕ):ℝ)+1)/20
  · exact hptE_112 v ⟨hlow112, hcut112⟩
  replace hcut112 : 2+(((112:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut112
  have hlow113 : 2+((113:ℕ):ℝ)/20 ≤ v := by push_cast at hcut112 ⊢; linarith
  by_cases hcut113 : v < 2+(((113:ℕ):ℝ)+1)/20
  · exact hptE_113 v ⟨hlow113, hcut113⟩
  replace hcut113 : 2+(((113:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut113
  have hlow114 : 2+((114:ℕ):ℝ)/20 ≤ v := by push_cast at hcut113 ⊢; linarith
  by_cases hcut114 : v < 2+(((114:ℕ):ℝ)+1)/20
  · exact hptE_114 v ⟨hlow114, hcut114⟩
  replace hcut114 : 2+(((114:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut114
  have hlow115 : 2+((115:ℕ):ℝ)/20 ≤ v := by push_cast at hcut114 ⊢; linarith
  by_cases hcut115 : v < 2+(((115:ℕ):ℝ)+1)/20
  · exact hptE_115 v ⟨hlow115, hcut115⟩
  replace hcut115 : 2+(((115:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut115
  have hlow116 : 2+((116:ℕ):ℝ)/20 ≤ v := by push_cast at hcut115 ⊢; linarith
  by_cases hcut116 : v < 2+(((116:ℕ):ℝ)+1)/20
  · exact hptE_116 v ⟨hlow116, hcut116⟩
  replace hcut116 : 2+(((116:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut116
  have hlow117 : 2+((117:ℕ):ℝ)/20 ≤ v := by push_cast at hcut116 ⊢; linarith
  by_cases hcut117 : v < 2+(((117:ℕ):ℝ)+1)/20
  · exact hptE_117 v ⟨hlow117, hcut117⟩
  replace hcut117 : 2+(((117:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut117
  have hlow118 : 2+((118:ℕ):ℝ)/20 ≤ v := by push_cast at hcut117 ⊢; linarith
  by_cases hcut118 : v < 2+(((118:ℕ):ℝ)+1)/20
  · exact hptE_118 v ⟨hlow118, hcut118⟩
  replace hcut118 : 2+(((118:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut118
  have hlow119 : 2+((119:ℕ):ℝ)/20 ≤ v := by push_cast at hcut118 ⊢; linarith
  exact hptE_119 v ⟨hlow119, by push_cast at hhi ⊢; linarith⟩

/-- Panel dispatch for `v ∈ [2+120/20, 2+140/20)` (panels 120..139). -/
theorem hpt_disp_6 (v : ℝ)
    (hlo : 2+((120:ℕ):ℝ)/20 ≤ v) (hhi : v < 2+((140:ℕ):ℝ)/20) :
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  have hlow120 : 2+((120:ℕ):ℝ)/20 ≤ v := hlo
  by_cases hcut120 : v < 2+(((120:ℕ):ℝ)+1)/20
  · exact hptE_120 v ⟨hlow120, hcut120⟩
  replace hcut120 : 2+(((120:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut120
  have hlow121 : 2+((121:ℕ):ℝ)/20 ≤ v := by push_cast at hcut120 ⊢; linarith
  by_cases hcut121 : v < 2+(((121:ℕ):ℝ)+1)/20
  · exact hptE_121 v ⟨hlow121, hcut121⟩
  replace hcut121 : 2+(((121:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut121
  have hlow122 : 2+((122:ℕ):ℝ)/20 ≤ v := by push_cast at hcut121 ⊢; linarith
  by_cases hcut122 : v < 2+(((122:ℕ):ℝ)+1)/20
  · exact hptE_122 v ⟨hlow122, hcut122⟩
  replace hcut122 : 2+(((122:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut122
  have hlow123 : 2+((123:ℕ):ℝ)/20 ≤ v := by push_cast at hcut122 ⊢; linarith
  by_cases hcut123 : v < 2+(((123:ℕ):ℝ)+1)/20
  · exact hptE_123 v ⟨hlow123, hcut123⟩
  replace hcut123 : 2+(((123:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut123
  have hlow124 : 2+((124:ℕ):ℝ)/20 ≤ v := by push_cast at hcut123 ⊢; linarith
  by_cases hcut124 : v < 2+(((124:ℕ):ℝ)+1)/20
  · exact hptE_124 v ⟨hlow124, hcut124⟩
  replace hcut124 : 2+(((124:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut124
  have hlow125 : 2+((125:ℕ):ℝ)/20 ≤ v := by push_cast at hcut124 ⊢; linarith
  by_cases hcut125 : v < 2+(((125:ℕ):ℝ)+1)/20
  · exact hptE_125 v ⟨hlow125, hcut125⟩
  replace hcut125 : 2+(((125:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut125
  have hlow126 : 2+((126:ℕ):ℝ)/20 ≤ v := by push_cast at hcut125 ⊢; linarith
  by_cases hcut126 : v < 2+(((126:ℕ):ℝ)+1)/20
  · exact hptE_126 v ⟨hlow126, hcut126⟩
  replace hcut126 : 2+(((126:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut126
  have hlow127 : 2+((127:ℕ):ℝ)/20 ≤ v := by push_cast at hcut126 ⊢; linarith
  by_cases hcut127 : v < 2+(((127:ℕ):ℝ)+1)/20
  · exact hptE_127 v ⟨hlow127, hcut127⟩
  replace hcut127 : 2+(((127:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut127
  have hlow128 : 2+((128:ℕ):ℝ)/20 ≤ v := by push_cast at hcut127 ⊢; linarith
  by_cases hcut128 : v < 2+(((128:ℕ):ℝ)+1)/20
  · exact hptE_128 v ⟨hlow128, hcut128⟩
  replace hcut128 : 2+(((128:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut128
  have hlow129 : 2+((129:ℕ):ℝ)/20 ≤ v := by push_cast at hcut128 ⊢; linarith
  by_cases hcut129 : v < 2+(((129:ℕ):ℝ)+1)/20
  · exact hptE_129 v ⟨hlow129, hcut129⟩
  replace hcut129 : 2+(((129:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut129
  have hlow130 : 2+((130:ℕ):ℝ)/20 ≤ v := by push_cast at hcut129 ⊢; linarith
  by_cases hcut130 : v < 2+(((130:ℕ):ℝ)+1)/20
  · exact hptE_130 v ⟨hlow130, hcut130⟩
  replace hcut130 : 2+(((130:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut130
  have hlow131 : 2+((131:ℕ):ℝ)/20 ≤ v := by push_cast at hcut130 ⊢; linarith
  by_cases hcut131 : v < 2+(((131:ℕ):ℝ)+1)/20
  · exact hptE_131 v ⟨hlow131, hcut131⟩
  replace hcut131 : 2+(((131:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut131
  have hlow132 : 2+((132:ℕ):ℝ)/20 ≤ v := by push_cast at hcut131 ⊢; linarith
  by_cases hcut132 : v < 2+(((132:ℕ):ℝ)+1)/20
  · exact hptE_132 v ⟨hlow132, hcut132⟩
  replace hcut132 : 2+(((132:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut132
  have hlow133 : 2+((133:ℕ):ℝ)/20 ≤ v := by push_cast at hcut132 ⊢; linarith
  by_cases hcut133 : v < 2+(((133:ℕ):ℝ)+1)/20
  · exact hptE_133 v ⟨hlow133, hcut133⟩
  replace hcut133 : 2+(((133:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut133
  have hlow134 : 2+((134:ℕ):ℝ)/20 ≤ v := by push_cast at hcut133 ⊢; linarith
  by_cases hcut134 : v < 2+(((134:ℕ):ℝ)+1)/20
  · exact hptE_134 v ⟨hlow134, hcut134⟩
  replace hcut134 : 2+(((134:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut134
  have hlow135 : 2+((135:ℕ):ℝ)/20 ≤ v := by push_cast at hcut134 ⊢; linarith
  by_cases hcut135 : v < 2+(((135:ℕ):ℝ)+1)/20
  · exact hptE_135 v ⟨hlow135, hcut135⟩
  replace hcut135 : 2+(((135:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut135
  have hlow136 : 2+((136:ℕ):ℝ)/20 ≤ v := by push_cast at hcut135 ⊢; linarith
  by_cases hcut136 : v < 2+(((136:ℕ):ℝ)+1)/20
  · exact hptE_136 v ⟨hlow136, hcut136⟩
  replace hcut136 : 2+(((136:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut136
  have hlow137 : 2+((137:ℕ):ℝ)/20 ≤ v := by push_cast at hcut136 ⊢; linarith
  by_cases hcut137 : v < 2+(((137:ℕ):ℝ)+1)/20
  · exact hptE_137 v ⟨hlow137, hcut137⟩
  replace hcut137 : 2+(((137:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut137
  have hlow138 : 2+((138:ℕ):ℝ)/20 ≤ v := by push_cast at hcut137 ⊢; linarith
  by_cases hcut138 : v < 2+(((138:ℕ):ℝ)+1)/20
  · exact hptE_138 v ⟨hlow138, hcut138⟩
  replace hcut138 : 2+(((138:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut138
  have hlow139 : 2+((139:ℕ):ℝ)/20 ≤ v := by push_cast at hcut138 ⊢; linarith
  exact hptE_139 v ⟨hlow139, by push_cast at hhi ⊢; linarith⟩

/-- Panel dispatch for `v ∈ [2+140/20, 2+160/20)` (panels 140..159). -/
theorem hpt_disp_7 (v : ℝ)
    (hlo : 2+((140:ℕ):ℝ)/20 ≤ v) (hhi : v < 2+((160:ℕ):ℝ)/20) :
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  have hlow140 : 2+((140:ℕ):ℝ)/20 ≤ v := hlo
  by_cases hcut140 : v < 2+(((140:ℕ):ℝ)+1)/20
  · exact hptE_140 v ⟨hlow140, hcut140⟩
  replace hcut140 : 2+(((140:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut140
  have hlow141 : 2+((141:ℕ):ℝ)/20 ≤ v := by push_cast at hcut140 ⊢; linarith
  by_cases hcut141 : v < 2+(((141:ℕ):ℝ)+1)/20
  · exact hptE_141 v ⟨hlow141, hcut141⟩
  replace hcut141 : 2+(((141:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut141
  have hlow142 : 2+((142:ℕ):ℝ)/20 ≤ v := by push_cast at hcut141 ⊢; linarith
  by_cases hcut142 : v < 2+(((142:ℕ):ℝ)+1)/20
  · exact hptE_142 v ⟨hlow142, hcut142⟩
  replace hcut142 : 2+(((142:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut142
  have hlow143 : 2+((143:ℕ):ℝ)/20 ≤ v := by push_cast at hcut142 ⊢; linarith
  by_cases hcut143 : v < 2+(((143:ℕ):ℝ)+1)/20
  · exact hptE_143 v ⟨hlow143, hcut143⟩
  replace hcut143 : 2+(((143:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut143
  have hlow144 : 2+((144:ℕ):ℝ)/20 ≤ v := by push_cast at hcut143 ⊢; linarith
  by_cases hcut144 : v < 2+(((144:ℕ):ℝ)+1)/20
  · exact hptE_144 v ⟨hlow144, hcut144⟩
  replace hcut144 : 2+(((144:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut144
  have hlow145 : 2+((145:ℕ):ℝ)/20 ≤ v := by push_cast at hcut144 ⊢; linarith
  by_cases hcut145 : v < 2+(((145:ℕ):ℝ)+1)/20
  · exact hptE_145 v ⟨hlow145, hcut145⟩
  replace hcut145 : 2+(((145:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut145
  have hlow146 : 2+((146:ℕ):ℝ)/20 ≤ v := by push_cast at hcut145 ⊢; linarith
  by_cases hcut146 : v < 2+(((146:ℕ):ℝ)+1)/20
  · exact hptE_146 v ⟨hlow146, hcut146⟩
  replace hcut146 : 2+(((146:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut146
  have hlow147 : 2+((147:ℕ):ℝ)/20 ≤ v := by push_cast at hcut146 ⊢; linarith
  by_cases hcut147 : v < 2+(((147:ℕ):ℝ)+1)/20
  · exact hptE_147 v ⟨hlow147, hcut147⟩
  replace hcut147 : 2+(((147:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut147
  have hlow148 : 2+((148:ℕ):ℝ)/20 ≤ v := by push_cast at hcut147 ⊢; linarith
  by_cases hcut148 : v < 2+(((148:ℕ):ℝ)+1)/20
  · exact hptE_148 v ⟨hlow148, hcut148⟩
  replace hcut148 : 2+(((148:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut148
  have hlow149 : 2+((149:ℕ):ℝ)/20 ≤ v := by push_cast at hcut148 ⊢; linarith
  by_cases hcut149 : v < 2+(((149:ℕ):ℝ)+1)/20
  · exact hptE_149 v ⟨hlow149, hcut149⟩
  replace hcut149 : 2+(((149:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut149
  have hlow150 : 2+((150:ℕ):ℝ)/20 ≤ v := by push_cast at hcut149 ⊢; linarith
  by_cases hcut150 : v < 2+(((150:ℕ):ℝ)+1)/20
  · exact hptE_150 v ⟨hlow150, hcut150⟩
  replace hcut150 : 2+(((150:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut150
  have hlow151 : 2+((151:ℕ):ℝ)/20 ≤ v := by push_cast at hcut150 ⊢; linarith
  by_cases hcut151 : v < 2+(((151:ℕ):ℝ)+1)/20
  · exact hptE_151 v ⟨hlow151, hcut151⟩
  replace hcut151 : 2+(((151:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut151
  have hlow152 : 2+((152:ℕ):ℝ)/20 ≤ v := by push_cast at hcut151 ⊢; linarith
  by_cases hcut152 : v < 2+(((152:ℕ):ℝ)+1)/20
  · exact hptE_152 v ⟨hlow152, hcut152⟩
  replace hcut152 : 2+(((152:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut152
  have hlow153 : 2+((153:ℕ):ℝ)/20 ≤ v := by push_cast at hcut152 ⊢; linarith
  by_cases hcut153 : v < 2+(((153:ℕ):ℝ)+1)/20
  · exact hptE_153 v ⟨hlow153, hcut153⟩
  replace hcut153 : 2+(((153:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut153
  have hlow154 : 2+((154:ℕ):ℝ)/20 ≤ v := by push_cast at hcut153 ⊢; linarith
  by_cases hcut154 : v < 2+(((154:ℕ):ℝ)+1)/20
  · exact hptE_154 v ⟨hlow154, hcut154⟩
  replace hcut154 : 2+(((154:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut154
  have hlow155 : 2+((155:ℕ):ℝ)/20 ≤ v := by push_cast at hcut154 ⊢; linarith
  by_cases hcut155 : v < 2+(((155:ℕ):ℝ)+1)/20
  · exact hptE_155 v ⟨hlow155, hcut155⟩
  replace hcut155 : 2+(((155:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut155
  have hlow156 : 2+((156:ℕ):ℝ)/20 ≤ v := by push_cast at hcut155 ⊢; linarith
  by_cases hcut156 : v < 2+(((156:ℕ):ℝ)+1)/20
  · exact hptE_156 v ⟨hlow156, hcut156⟩
  replace hcut156 : 2+(((156:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut156
  have hlow157 : 2+((157:ℕ):ℝ)/20 ≤ v := by push_cast at hcut156 ⊢; linarith
  by_cases hcut157 : v < 2+(((157:ℕ):ℝ)+1)/20
  · exact hptE_157 v ⟨hlow157, hcut157⟩
  replace hcut157 : 2+(((157:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut157
  have hlow158 : 2+((158:ℕ):ℝ)/20 ≤ v := by push_cast at hcut157 ⊢; linarith
  by_cases hcut158 : v < 2+(((158:ℕ):ℝ)+1)/20
  · exact hptE_158 v ⟨hlow158, hcut158⟩
  replace hcut158 : 2+(((158:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut158
  have hlow159 : 2+((159:ℕ):ℝ)/20 ≤ v := by push_cast at hcut158 ⊢; linarith
  exact hptE_159 v ⟨hlow159, by push_cast at hhi ⊢; linarith⟩

/-- Panel dispatch for `v ∈ [2+160/20, 2+180/20)` (panels 160..179). -/
theorem hpt_disp_8 (v : ℝ)
    (hlo : 2+((160:ℕ):ℝ)/20 ≤ v) (hhi : v < 2+((180:ℕ):ℝ)/20) :
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  have hlow160 : 2+((160:ℕ):ℝ)/20 ≤ v := hlo
  by_cases hcut160 : v < 2+(((160:ℕ):ℝ)+1)/20
  · exact hptE_160 v ⟨hlow160, hcut160⟩
  replace hcut160 : 2+(((160:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut160
  have hlow161 : 2+((161:ℕ):ℝ)/20 ≤ v := by push_cast at hcut160 ⊢; linarith
  by_cases hcut161 : v < 2+(((161:ℕ):ℝ)+1)/20
  · exact hptE_161 v ⟨hlow161, hcut161⟩
  replace hcut161 : 2+(((161:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut161
  have hlow162 : 2+((162:ℕ):ℝ)/20 ≤ v := by push_cast at hcut161 ⊢; linarith
  by_cases hcut162 : v < 2+(((162:ℕ):ℝ)+1)/20
  · exact hptE_162 v ⟨hlow162, hcut162⟩
  replace hcut162 : 2+(((162:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut162
  have hlow163 : 2+((163:ℕ):ℝ)/20 ≤ v := by push_cast at hcut162 ⊢; linarith
  by_cases hcut163 : v < 2+(((163:ℕ):ℝ)+1)/20
  · exact hptE_163 v ⟨hlow163, hcut163⟩
  replace hcut163 : 2+(((163:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut163
  have hlow164 : 2+((164:ℕ):ℝ)/20 ≤ v := by push_cast at hcut163 ⊢; linarith
  by_cases hcut164 : v < 2+(((164:ℕ):ℝ)+1)/20
  · exact hptE_164 v ⟨hlow164, hcut164⟩
  replace hcut164 : 2+(((164:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut164
  have hlow165 : 2+((165:ℕ):ℝ)/20 ≤ v := by push_cast at hcut164 ⊢; linarith
  by_cases hcut165 : v < 2+(((165:ℕ):ℝ)+1)/20
  · exact hptE_165 v ⟨hlow165, hcut165⟩
  replace hcut165 : 2+(((165:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut165
  have hlow166 : 2+((166:ℕ):ℝ)/20 ≤ v := by push_cast at hcut165 ⊢; linarith
  by_cases hcut166 : v < 2+(((166:ℕ):ℝ)+1)/20
  · exact hptE_166 v ⟨hlow166, hcut166⟩
  replace hcut166 : 2+(((166:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut166
  have hlow167 : 2+((167:ℕ):ℝ)/20 ≤ v := by push_cast at hcut166 ⊢; linarith
  by_cases hcut167 : v < 2+(((167:ℕ):ℝ)+1)/20
  · exact hptE_167 v ⟨hlow167, hcut167⟩
  replace hcut167 : 2+(((167:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut167
  have hlow168 : 2+((168:ℕ):ℝ)/20 ≤ v := by push_cast at hcut167 ⊢; linarith
  by_cases hcut168 : v < 2+(((168:ℕ):ℝ)+1)/20
  · exact hptE_168 v ⟨hlow168, hcut168⟩
  replace hcut168 : 2+(((168:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut168
  have hlow169 : 2+((169:ℕ):ℝ)/20 ≤ v := by push_cast at hcut168 ⊢; linarith
  by_cases hcut169 : v < 2+(((169:ℕ):ℝ)+1)/20
  · exact hptE_169 v ⟨hlow169, hcut169⟩
  replace hcut169 : 2+(((169:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut169
  have hlow170 : 2+((170:ℕ):ℝ)/20 ≤ v := by push_cast at hcut169 ⊢; linarith
  by_cases hcut170 : v < 2+(((170:ℕ):ℝ)+1)/20
  · exact hptE_170 v ⟨hlow170, hcut170⟩
  replace hcut170 : 2+(((170:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut170
  have hlow171 : 2+((171:ℕ):ℝ)/20 ≤ v := by push_cast at hcut170 ⊢; linarith
  by_cases hcut171 : v < 2+(((171:ℕ):ℝ)+1)/20
  · exact hptE_171 v ⟨hlow171, hcut171⟩
  replace hcut171 : 2+(((171:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut171
  have hlow172 : 2+((172:ℕ):ℝ)/20 ≤ v := by push_cast at hcut171 ⊢; linarith
  by_cases hcut172 : v < 2+(((172:ℕ):ℝ)+1)/20
  · exact hptE_172 v ⟨hlow172, hcut172⟩
  replace hcut172 : 2+(((172:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut172
  have hlow173 : 2+((173:ℕ):ℝ)/20 ≤ v := by push_cast at hcut172 ⊢; linarith
  by_cases hcut173 : v < 2+(((173:ℕ):ℝ)+1)/20
  · exact hptE_173 v ⟨hlow173, hcut173⟩
  replace hcut173 : 2+(((173:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut173
  have hlow174 : 2+((174:ℕ):ℝ)/20 ≤ v := by push_cast at hcut173 ⊢; linarith
  by_cases hcut174 : v < 2+(((174:ℕ):ℝ)+1)/20
  · exact hptE_174 v ⟨hlow174, hcut174⟩
  replace hcut174 : 2+(((174:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut174
  have hlow175 : 2+((175:ℕ):ℝ)/20 ≤ v := by push_cast at hcut174 ⊢; linarith
  by_cases hcut175 : v < 2+(((175:ℕ):ℝ)+1)/20
  · exact hptE_175 v ⟨hlow175, hcut175⟩
  replace hcut175 : 2+(((175:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut175
  have hlow176 : 2+((176:ℕ):ℝ)/20 ≤ v := by push_cast at hcut175 ⊢; linarith
  by_cases hcut176 : v < 2+(((176:ℕ):ℝ)+1)/20
  · exact hptE_176 v ⟨hlow176, hcut176⟩
  replace hcut176 : 2+(((176:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut176
  have hlow177 : 2+((177:ℕ):ℝ)/20 ≤ v := by push_cast at hcut176 ⊢; linarith
  by_cases hcut177 : v < 2+(((177:ℕ):ℝ)+1)/20
  · exact hptE_177 v ⟨hlow177, hcut177⟩
  replace hcut177 : 2+(((177:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut177
  have hlow178 : 2+((178:ℕ):ℝ)/20 ≤ v := by push_cast at hcut177 ⊢; linarith
  by_cases hcut178 : v < 2+(((178:ℕ):ℝ)+1)/20
  · exact hptE_178 v ⟨hlow178, hcut178⟩
  replace hcut178 : 2+(((178:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut178
  have hlow179 : 2+((179:ℕ):ℝ)/20 ≤ v := by push_cast at hcut178 ⊢; linarith
  exact hptE_179 v ⟨hlow179, by push_cast at hhi ⊢; linarith⟩

/-- Panel dispatch for `v ∈ [2+180/20, 2+200/20)` (panels 180..199). -/
theorem hpt_disp_9 (v : ℝ)
    (hlo : 2+((180:ℕ):ℝ)/20 ≤ v) (hhi : v < 2+((200:ℕ):ℝ)/20) :
    fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  have hlow180 : 2+((180:ℕ):ℝ)/20 ≤ v := hlo
  by_cases hcut180 : v < 2+(((180:ℕ):ℝ)+1)/20
  · exact hptE_180 v ⟨hlow180, hcut180⟩
  replace hcut180 : 2+(((180:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut180
  have hlow181 : 2+((181:ℕ):ℝ)/20 ≤ v := by push_cast at hcut180 ⊢; linarith
  by_cases hcut181 : v < 2+(((181:ℕ):ℝ)+1)/20
  · exact hptE_181 v ⟨hlow181, hcut181⟩
  replace hcut181 : 2+(((181:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut181
  have hlow182 : 2+((182:ℕ):ℝ)/20 ≤ v := by push_cast at hcut181 ⊢; linarith
  by_cases hcut182 : v < 2+(((182:ℕ):ℝ)+1)/20
  · exact hptE_182 v ⟨hlow182, hcut182⟩
  replace hcut182 : 2+(((182:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut182
  have hlow183 : 2+((183:ℕ):ℝ)/20 ≤ v := by push_cast at hcut182 ⊢; linarith
  by_cases hcut183 : v < 2+(((183:ℕ):ℝ)+1)/20
  · exact hptE_183 v ⟨hlow183, hcut183⟩
  replace hcut183 : 2+(((183:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut183
  have hlow184 : 2+((184:ℕ):ℝ)/20 ≤ v := by push_cast at hcut183 ⊢; linarith
  by_cases hcut184 : v < 2+(((184:ℕ):ℝ)+1)/20
  · exact hptE_184 v ⟨hlow184, hcut184⟩
  replace hcut184 : 2+(((184:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut184
  have hlow185 : 2+((185:ℕ):ℝ)/20 ≤ v := by push_cast at hcut184 ⊢; linarith
  by_cases hcut185 : v < 2+(((185:ℕ):ℝ)+1)/20
  · exact hptE_185 v ⟨hlow185, hcut185⟩
  replace hcut185 : 2+(((185:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut185
  have hlow186 : 2+((186:ℕ):ℝ)/20 ≤ v := by push_cast at hcut185 ⊢; linarith
  by_cases hcut186 : v < 2+(((186:ℕ):ℝ)+1)/20
  · exact hptE_186 v ⟨hlow186, hcut186⟩
  replace hcut186 : 2+(((186:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut186
  have hlow187 : 2+((187:ℕ):ℝ)/20 ≤ v := by push_cast at hcut186 ⊢; linarith
  by_cases hcut187 : v < 2+(((187:ℕ):ℝ)+1)/20
  · exact hptE_187 v ⟨hlow187, hcut187⟩
  replace hcut187 : 2+(((187:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut187
  have hlow188 : 2+((188:ℕ):ℝ)/20 ≤ v := by push_cast at hcut187 ⊢; linarith
  by_cases hcut188 : v < 2+(((188:ℕ):ℝ)+1)/20
  · exact hptE_188 v ⟨hlow188, hcut188⟩
  replace hcut188 : 2+(((188:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut188
  have hlow189 : 2+((189:ℕ):ℝ)/20 ≤ v := by push_cast at hcut188 ⊢; linarith
  by_cases hcut189 : v < 2+(((189:ℕ):ℝ)+1)/20
  · exact hptE_189 v ⟨hlow189, hcut189⟩
  replace hcut189 : 2+(((189:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut189
  have hlow190 : 2+((190:ℕ):ℝ)/20 ≤ v := by push_cast at hcut189 ⊢; linarith
  by_cases hcut190 : v < 2+(((190:ℕ):ℝ)+1)/20
  · exact hptE_190 v ⟨hlow190, hcut190⟩
  replace hcut190 : 2+(((190:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut190
  have hlow191 : 2+((191:ℕ):ℝ)/20 ≤ v := by push_cast at hcut190 ⊢; linarith
  by_cases hcut191 : v < 2+(((191:ℕ):ℝ)+1)/20
  · exact hptE_191 v ⟨hlow191, hcut191⟩
  replace hcut191 : 2+(((191:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut191
  have hlow192 : 2+((192:ℕ):ℝ)/20 ≤ v := by push_cast at hcut191 ⊢; linarith
  by_cases hcut192 : v < 2+(((192:ℕ):ℝ)+1)/20
  · exact hptE_192 v ⟨hlow192, hcut192⟩
  replace hcut192 : 2+(((192:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut192
  have hlow193 : 2+((193:ℕ):ℝ)/20 ≤ v := by push_cast at hcut192 ⊢; linarith
  by_cases hcut193 : v < 2+(((193:ℕ):ℝ)+1)/20
  · exact hptE_193 v ⟨hlow193, hcut193⟩
  replace hcut193 : 2+(((193:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut193
  have hlow194 : 2+((194:ℕ):ℝ)/20 ≤ v := by push_cast at hcut193 ⊢; linarith
  by_cases hcut194 : v < 2+(((194:ℕ):ℝ)+1)/20
  · exact hptE_194 v ⟨hlow194, hcut194⟩
  replace hcut194 : 2+(((194:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut194
  have hlow195 : 2+((195:ℕ):ℝ)/20 ≤ v := by push_cast at hcut194 ⊢; linarith
  by_cases hcut195 : v < 2+(((195:ℕ):ℝ)+1)/20
  · exact hptE_195 v ⟨hlow195, hcut195⟩
  replace hcut195 : 2+(((195:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut195
  have hlow196 : 2+((196:ℕ):ℝ)/20 ≤ v := by push_cast at hcut195 ⊢; linarith
  by_cases hcut196 : v < 2+(((196:ℕ):ℝ)+1)/20
  · exact hptE_196 v ⟨hlow196, hcut196⟩
  replace hcut196 : 2+(((196:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut196
  have hlow197 : 2+((197:ℕ):ℝ)/20 ≤ v := by push_cast at hcut196 ⊢; linarith
  by_cases hcut197 : v < 2+(((197:ℕ):ℝ)+1)/20
  · exact hptE_197 v ⟨hlow197, hcut197⟩
  replace hcut197 : 2+(((197:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut197
  have hlow198 : 2+((198:ℕ):ℝ)/20 ≤ v := by push_cast at hcut197 ⊢; linarith
  by_cases hcut198 : v < 2+(((198:ℕ):ℝ)+1)/20
  · exact hptE_198 v ⟨hlow198, hcut198⟩
  replace hcut198 : 2+(((198:ℕ):ℝ)+1)/20 ≤ v := not_lt.mp hcut198
  have hlow199 : 2+((199:ℕ):ℝ)/20 ≤ v := by push_cast at hcut198 ⊢; linarith
  exact hptE_199 v ⟨hlow199, by push_cast at hhi ⊢; linarith⟩

theorem hpt_holds : ∀ v, (2:ℝ) ≤ v → fseq 2 v + (1/v) * TObar (v-1) ≤ Ebar v := by
  intro v hv2
  rcases le_or_gt 12 v with hv12 | hv12
  · exact hptE_tail v hv12
  have hc_0 : 2+((0:ℕ):ℝ)/20 ≤ v := by push_cast; linarith
  by_cases hd0 : v < 2+((20:ℕ):ℝ)/20
  · exact hpt_disp_0 v hc_0 hd0
  replace hd0 : 2+((20:ℕ):ℝ)/20 ≤ v := not_lt.mp hd0
  have hc_1 : 2+((20:ℕ):ℝ)/20 ≤ v := hd0
  by_cases hd1 : v < 2+((40:ℕ):ℝ)/20
  · exact hpt_disp_1 v hc_1 hd1
  replace hd1 : 2+((40:ℕ):ℝ)/20 ≤ v := not_lt.mp hd1
  have hc_2 : 2+((40:ℕ):ℝ)/20 ≤ v := hd1
  by_cases hd2 : v < 2+((60:ℕ):ℝ)/20
  · exact hpt_disp_2 v hc_2 hd2
  replace hd2 : 2+((60:ℕ):ℝ)/20 ≤ v := not_lt.mp hd2
  have hc_3 : 2+((60:ℕ):ℝ)/20 ≤ v := hd2
  by_cases hd3 : v < 2+((80:ℕ):ℝ)/20
  · exact hpt_disp_3 v hc_3 hd3
  replace hd3 : 2+((80:ℕ):ℝ)/20 ≤ v := not_lt.mp hd3
  have hc_4 : 2+((80:ℕ):ℝ)/20 ≤ v := hd3
  by_cases hd4 : v < 2+((100:ℕ):ℝ)/20
  · exact hpt_disp_4 v hc_4 hd4
  replace hd4 : 2+((100:ℕ):ℝ)/20 ≤ v := not_lt.mp hd4
  have hc_5 : 2+((100:ℕ):ℝ)/20 ≤ v := hd4
  by_cases hd5 : v < 2+((120:ℕ):ℝ)/20
  · exact hpt_disp_5 v hc_5 hd5
  replace hd5 : 2+((120:ℕ):ℝ)/20 ≤ v := not_lt.mp hd5
  have hc_6 : 2+((120:ℕ):ℝ)/20 ≤ v := hd5
  by_cases hd6 : v < 2+((140:ℕ):ℝ)/20
  · exact hpt_disp_6 v hc_6 hd6
  replace hd6 : 2+((140:ℕ):ℝ)/20 ≤ v := not_lt.mp hd6
  have hc_7 : 2+((140:ℕ):ℝ)/20 ≤ v := hd6
  by_cases hd7 : v < 2+((160:ℕ):ℝ)/20
  · exact hpt_disp_7 v hc_7 hd7
  replace hd7 : 2+((160:ℕ):ℝ)/20 ≤ v := not_lt.mp hd7
  have hc_8 : 2+((160:ℕ):ℝ)/20 ≤ v := hd7
  by_cases hd8 : v < 2+((180:ℕ):ℝ)/20
  · exact hpt_disp_8 v hc_8 hd8
  replace hd8 : 2+((180:ℕ):ℝ)/20 ≤ v := not_lt.mp hd8
  have hc_9 : 2+((180:ℕ):ℝ)/20 ≤ v := hd8
  exact hpt_disp_9 v hc_9 (by push_cast at hv12 ⊢; linarith)

/-- **`hSE` holds.**  The even super-solution inequality of `SuperSolution.lean`, discharged from
the panel checks via `hSE_reduce` (`TObar` bounds the `∀ b` Obar-integral). -/
theorem hSE_holds : ∀ v, (2:ℝ) ≤ v → ∀ b, v ≤ b →
    fseq 2 v + (1 / v) * ∫ t in v..b, Obar (t - 1) ≤ Ebar v :=
  hSE_reduce Ebar Obar (fun x => TObar (x-1)) (fun v hv b hvb => hTO v hv b hvb) hpt_holds

end Salt.Chen
