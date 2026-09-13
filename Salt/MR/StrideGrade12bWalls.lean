/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# (B1) β W1 E4 — THE GRADED LANE'S NUMERAL WALLS AT `2^12` AND CAP 9

Build freeze v2 v1.1 (2026-09-13), §3.1 rule 6: the graded wall twins live in THIS new module
(importing `StrideGradeReach` and `StrideGrade12Walls`), not beside their sources in
`StrideGradeWalls.lean`, because both of those modules import `StrideGradeWalls` — placing the
twins there would make an import cycle.

Each declaration is its `StrideGradeWalls.lean` source's statement and body with ONLY the freeze's
§3.1 rule-2 raises — door grade `2 ^ 11 ↦ 2 ^ 12` (in `838400 * 2 ^ 11`), shift cap
`log h ≤ 7 ↦ ≤ 9`, `h ≤ 1096 ↦ h ≤ 8103`, and the census's numerals at cap 9 (band 3 rows 17, 21)
— with every derived
supplier replaced by its twin or by the landed `_g14` rung (by weakening `≤ 9 ⇒ ≤ 14`).  No landed
declaration moves; no hypothesis is added; no conclusion is weakened.

THE NUMERALS (`log 2 < 0.6931471808`):
  · the arm's `c = 2^12·h²` at `h ≤ 8103`: `4096·8103² = 268937662464 ≤ 2961933067911168` (the
    `_g14` ceiling, ×1.1·10⁴), `log c ≤ 12·log 2 + 18 = 26.32 ≤ 27 ≤ 36`;
  · the register's charge at cap 9: the envelope floor stays `2^592`, so `411 + 2·9 = 429 ≤ 439`
    (the `_g14` lines' binder).

HONEST LABEL.  Numerals only; nothing here proves an estimate, and nothing bears on twin primes.
-/
import Salt.MR.StrideGradeReach
import Salt.MR.StrideGrade12Walls
import Mathlib

-- The same header context as `StrideGradeWalls.lean` (the sources' module): its one `open private`.
open private xt_exp25 from Salt.MR.XThread

noncomputable section

open Salt.Entropy.Chowla

set_option exponentiation.threshold 4000

namespace Salt.MR

/-- `s15_sel''_L_witness_flat_charge_g` at `2^12` and cap 9
(`s15_sel''_L_witness_flat_charge_g12b`) — SUPPLIER-SWAP (census band 3 row 21): the binders
`hcb : c ≤ 1096 ↦ c ≤ 8103` and `hρlog : −log ρ ≤ 425 ↦ ≤ 429` (`411 + 2·9`; the envelope floor
`2^592` stays, so the grade leaves the charge unmoved); `hbase` from E3's
`s15_sel''_L_witness_flat_b9` at the same FROZEN dummy literals, and the four cap lines from the
landed `_g14` rungs (`c ≤ 439`) by weakening `429 ≤ 439`.  Every other step is the source's,
verbatim. -/
theorem s15_sel''_L_witness_flat_charge_g12b {A : ℝ} (hA : 26 ≤ A) {Cg δ₀ Ct ρ : ℝ}
    {x₀ Mfl c : ℕ} {R : ChowlaRegime} (hc1 : 1 ≤ c) (hcb : c ≤ 8103)
    (hρlog : -Real.log ρ ≤ 429)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L Cg δ₀ Ct ρ x₀ Mfl R (flatDoorM A) := by
  have hbase := s15_sel''_L_witness_flat_b9 (A := A) (Cg := 0) (δ₀ := 1 / 2 ^ 10) (Ct := 1)
    (K := 1) (x₀ := x₀) (Mfl := Mfl) (c := c) (R := R) hA hc1 hcb (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp) hMfl hx0win heps hlo hhi
  have hinv : Real.log (1 / ρ) = -Real.log ρ := by rw [one_div, Real.log_inv]
  have hρlog' : -Real.log ρ ≤ 439 := le_trans hρlog (by norm_num)
  refine
    { hM := hbase.hM
      mfloor := hMfl
      bfloor := hbfl
      gRows := hbase.gRows
      x0M := hbase.x0M
      blk := hbase.blk
      half := ?_
      rho := ?_
      anchor := ?_
      gP1 := ?_
      lvl := ?_ }
  · rw [hinv]
    exact le_trans (flat_half_line_g14 hA hρlog') (by linarith [hlo])
  · linarith [hρlog]
  · rw [hinv]
    -- amended per REF-FLAT-SAT: the wide anchor line, at the doubled `Λ` slot
    exact le_trans (by linarith [hhi]) (flat_anchor_line_wide_g14 hA hρlog')
  · exact flat_gP1_line_g14 hA (by linarith [hρlog]) hCt hCtb hhi
  · exact flat_lvl_line_g14 hA hρlog' hhi

/-- `s15ArmH_log_le_g` at `2^12` and cap 9 (`s15ArmH_log_le_g12b`) — NUMERAL-LIFT (census band 3
row 17): `hh7 : log h ≤ 7 ↦ hh9 : log h ≤ 9` and `hδpin` at `838400 * 2 ^ 12`; conclusion unchanged.
BODY: the source's with `c = 2^12·h²`: `h ≤ 8103` from `h_le_8103_of_hh9`, `hcb : 2^12·h² ≤
268937662464` (`= 4096·8103²`, exact) weakened to the supplier's `2961933067911168`, `hlogc :
log (2^12·h²) ≤ 27` (`12·log 2 + 18 = 26.32`) weakened to `36`, and the supplier
`s15Arm_log_le_scaled_g ↦ s15Arm_log_le_scaled_g14` (landed; its binders hold by `linarith`).  The
`s15ArmH_le_mul` step and the log split are the source's, verbatim. -/
theorem s15ArmH_log_le_g12b {h : ℕ} (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9) {δ₀ Kc : ℝ}
    (hδ₀ : 0 < δ₀) (hδpin : 1 / (838400 * 2 ^ 12 * (h : ℝ) ^ 2) ≤ δ₀)
    (hKc : 0 < Kc) (hKcb : Kc ≤ 2 ^ 539) {Hhi ω : ℕ}
    (hHhi : 4000000 ≤ Hhi) (hΛ : 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ Real.log ((ω : ℕ) : ℝ) + Real.log (h : ℝ) + ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
  have hh1R : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hc1 : (1 : ℝ) ≤ (2 : ℝ) ^ 12 * (h : ℝ) ^ 2 := by nlinarith [hh1R]
  have h8103 : (h : ℝ) ≤ 8103 := by exact_mod_cast h_le_8103_of_hh9 hh hh9
  have hcb0 : (2 : ℝ) ^ 12 * (h : ℝ) ^ 2 ≤ 268937662464 := by nlinarith [hh1R, h8103]
  have hcb : (2 : ℝ) ^ 12 * (h : ℝ) ^ 2 ≤ 2961933067911168 := by linarith
  have hlogc0 : Real.log ((2 : ℝ) ^ 12 * (h : ℝ) ^ 2) ≤ 27 := by
    have hhpos : (0 : ℝ) < (h : ℝ) := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    push_cast
    linarith
  have hlogc : Real.log ((2 : ℝ) ^ 12 * (h : ℝ) ^ 2) ≤ 36 := by linarith
  have hδpin' : 1 / (838400 * ((2 : ℝ) ^ 12 * (h : ℝ) ^ 2)) ≤ δ₀ := by
    rw [← mul_assoc]; exact hδpin
  have hbase := s15Arm_log_le_scaled_g14 hc1 hcb hlogc hδ₀ hδpin' hKc hKcb (ω := ω) hHhi hΛ
  have hle := s15ArmH_le_mul hh δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω
  have hleR : ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ (h : ℝ) * ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hω0 : 0 ≤ Real.log ((ω : ℕ) : ℝ) := Real.log_natCast_nonneg ω
  have hh0 : 0 ≤ Real.log (h : ℝ) := Real.log_natCast_nonneg h
  have hHhi0 : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by positivity
  rcases Nat.eq_zero_or_pos (s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω)
    with hz | hpos
  · rw [hz]; simp only [Nat.cast_zero, Real.log_zero]; linarith
  · have hposR : (0 : ℝ)
        < ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) := by
      exact_mod_cast hpos
    have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    have hbpos : (0 : ℝ)
        < ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) := by
      by_contra hcon
      have hb0 : ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) ≤ 0 :=
        not_lt.mp hcon
      nlinarith [hleR, hposR, hhR, hb0]
    have hlog := Real.log_le_log hposR hleR
    rw [Real.log_mul hhR.ne' hbpos.ne'] at hlog
    linarith

/-! ## ⟦β W2 F1⟧ the charge wall and the three selectors at `2^12`, cap 9

Each is its `StrideGradeWalls.lean` source's statement and body with ONLY the rule-2 raises: the
walls' floor `2 ^ 31 ↦ 2 ^ 32` (the envelope floor `2 ^ 592` stays), the door grade
`838400 * 2 ^ 11 ↦ 838400 * 2 ^ 12`, `log ≤ 7 ↦ ≤ 9`, `c ≤ 1096 ↦ c ≤ 8103`, and the census's
charge `425 ↦ 429 = 411 + 2·9` (band 3 row 23); every derived supplier replaced by its twin
(`_g12b` above, W1 E3's `_b9`, this wave's `flat_blk_line_gk_b9`) or by the landed `_g12` rung. -/

/-- `s16_audit_neglog_rho_le_425_h` at `2^32` and cap 9 (`s16_audit_neglog_rho_le_425_h_g12b`) —
NUMERAL-LIFT (census band 3 row 23): `425 ↦ 429` (`411 + 2·9`; at cap 9 the source's `425` is a
wall, short 4 nats), `hδb` at `2 ^ 31 ↦ 2 ^ 32`, supplier `s16_audit_neglog_rho_le_wide_h_g ↦
s16_audit_neglog_rho_le_wide_h_g12` (landed; charge `411 + 2·log h`, grade-free).  BODY: the
source's `le_trans … (by linarith)`, verbatim. -/
theorem s16_audit_neglog_rho_le_425_h_g12b {h : ℕ} (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9)
    {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K)
    (hδb : 1 / (2 ^ 32 * (h : ℝ) ^ 2) ≤ δ₀) (hKb : K ≤ 2 ^ 539) :
    -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 429 := by
  exact le_trans (s16_audit_neglog_rho_le_wide_h_g12 hh hδ hK hδb hKb) (by linarith)

/-- `s15_sel''_L_witness_flat_wide_g` at `2^12` and cap 9 (`s15_sel''_L_witness_flat_wide_g12b`) —
SUPPLIER-SWAP (census band 3 row 22): binders `hcb : c ≤ 1096 ↦ c ≤ 8103`,
`hh7c ↦ hh9c : log c ≤ 9`, `hδb` at `2 ^ 31 ↦ 2 ^ 32`; suppliers
`s15_sel''_L_witness_flat_charge_g12b` (W1 E4, above) and
`s16_audit_neglog_rho_le_425_h_g12b`.  BODY: the source's, verbatim. -/
theorem s15_sel''_L_witness_flat_wide_g12b {A : ℝ} (hA : 26 ≤ A) {Cg δ₀ Ct K : ℝ}
    {x₀ Mfl c : ℕ} {R : ChowlaRegime}
    (hc1 : 1 ≤ c) (hcb : c ≤ 8103) (hh9c : Real.log (c : ℝ) ≤ 9)
    (hδ : 0 < δ₀) (hδb : 1 / (2 ^ 32 * (c : ℝ) ^ 2) ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 539)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R (flatDoorM A) := by
  exact s15_sel''_L_witness_flat_charge_g12b hA hc1 hcb
    (s16_audit_neglog_rho_le_425_h_g12b hc1 hh9c hδ hK hδb hKb) hCt hCtb
    hbfl hMfl hx0win heps hlo hhi

/-- `s15_sel''_L_gk_witness_flat_wide_g` at `2^12` and cap 9
(`s15_sel''_L_gk_witness_flat_wide_g12b`) — SUPPLIER-SWAP (census band 3 row 20): the binders as
`s15_sel''_L_witness_flat_wide_g12b`; suppliers `s15_sel''_L_witness_flat_wide_g12b` and
`flat_blk_line_gk_b9` (`S15SelLinearWide`, this wave).  BODY: the source's, verbatim. -/
theorem s15_sel''_L_gk_witness_flat_wide_g12b {A : ℝ} (hA : 26 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {Cg δ₀ Ct K : ℝ} {x₀ Mfl c : ℕ}
    {R : ChowlaRegime}
    (hc1 : 1 ≤ c) (hcb : c ≤ 8103) (hh9c : Real.log (c : ℝ) ≤ 9)
    (hδ : 0 < δ₀) (hδb : 1 / (2 ^ 32 * (c : ℝ) ^ 2) ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 539)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L_gk Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R
      (flatDoorM A) := by
  exact s15_sel''_L_gk_of_L Klev
    (s15_sel''_L_witness_flat_wide_g12b hA hc1 hcb hh9c hδ hδb hK hKb hCt hCtb hbfl hMfl hx0win
      heps hlo hhi)
    (flat_blk_line_gk_b9 hA Klev hKle hc1 hcb heps hlo hhi)

/-- `s15_sel''_L_gk_witness_flat_bumped_win_h_g` at `2^12` and cap 9
(`s15_sel''_L_gk_witness_flat_bumped_win_h_g12b`) — SUPPLIER-SWAP (census band 3 row 19):
`hh7 ↦ hh9`, `hδb` at `838400 * 2 ^ 11 ↦ 838400 * 2 ^ 12`; suppliers
`s15_sel''_L_gk_witness_flat_wide_g12b`, the converter `h_le_1096_of_hh7 ↦ h_le_8103_of_hh9`, and
the bump `flatDoorM_bfloor_bump_g ↦ flatDoorM_bfloor_bump_g12` (landed; its `c ≤ 1202604` by
`le_trans`, `8103 ≤ 1202604`).  The bridge `1/(2^32·h²) ≤ 1/(838400·2^12·h²)` is the source's
(`838400·4096 = 3434086400 ≤ 2^32`).  BODY otherwise verbatim. -/
theorem s15_sel''_L_gk_witness_flat_bumped_win_h_g12b {A : ℝ} (hA : 162 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {h : ℕ} (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9)
    {Cg δ₀ Ct K : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime}
    (hδ : 0 < δ₀) (hδb : 1 / (838400 * 2 ^ 12 * (h : ℝ) ^ 2) ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 539)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hCg : Cg ≤ 2 * 10 ^ 12) (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (h : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L_gk Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R (flatDoorM A) := by
  exact s15_sel''_L_gk_witness_flat_wide_g12b (flat162_ge_26 hA) Klev hKle hh
    (h_le_8103_of_hh9 hh hh9) hh9 hδ
    (by
      have h1 : (0 : ℝ) < (h : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
        positivity
      have : (1 : ℝ) / (2 ^ 32 * (h : ℝ) ^ 2) ≤ 1 / (838400 * 2 ^ 12 * (h : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [h1]
      linarith [hδb] : (1 : ℝ) / (2 ^ 32 * (h : ℝ) ^ 2) ≤ δ₀) hK hKb hCt hCtb
    (flatDoorM_bfloor_bump_g12 hh (le_trans (h_le_8103_of_hh9 hh hh9) (by norm_num)) hA hδ hδb hCg)
    hMfl hx0win heps hlo hhi

end Salt.MR

end
