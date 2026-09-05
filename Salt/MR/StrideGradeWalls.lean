/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# λ-BV wave 2-S, step F5 (β) — THE NUMERAL WALLS OF THE GRADED LANE

The graded sibling lane (`StridePairReceiptG`) runs the landed `h`-lane road at the threaded pin
`1/(838400·2^11·h²) ≤ δ₀` instead of `1/(838400·h²) ≤ δ₀`.  The road's grade is paid at the
envelope `ρ_env = doorRhoOfDelta (s12DeltaSock δ₀ Kc) = min 1 (δ₀/(16·Kc·110525))`, LINEAR in
`δ₀`, so every landed lemma that bounds `ρ_env` or `−log ρ_env` by a NUMERAL under the pin — the
census of the envelope's walls (2026-09-04, read-only) — is re-cut here by substitution, each
beside its source with the numeral moved and the slack stated.  The replays of the graded lane
consume EXACTLY TWO landed names at the pin, `s15ArmH_log_le` (the H2→H3 replay) and
`s15_sel''_L_gk_witness_flat_bumped_win_h` (the H3→H4 replay); everything below is what those
two twins reach, and nothing else.  No landed declaration moves.

THE NUMERALS (every one from the statement's own hypotheses; `log 2 < 0.6931471808`,
`Real.log_two_lt_d9`):
  · the pin `838400·2^11 = 1717043200 ≤ 2^31 = 2147483648` (×1.25, the bridge
  `1/2^31 ≤ 1/(838400·2^11)` );
  · the envelope floor `2^592` :
  `16·110525·2^539·2^31 = 110525·2^574 ≤ 2^592 ⇔ 110525 ≤ 2^18 = 262144` (×2.37);
  · the charge `411`: `592·log 2 = 410.343 ≤ 411` (0.657 nats); `425 = 411 + 2·7` (zero slack at
    the composition step, exactly as the landed `417 = 403 + 2·7`; 0.657 nats end to end);
  · the bump `24·2·10¹²·838400·2^11 = 8.2418·10²²`, `× 1201216 = 9.9002·10²⁸ ≤ 2^355 = 7.3·10¹⁰⁶`;
  · the arm's `c`-ceiling `2^11·1201216 = 2460090368`, `log(2^11·1201216) = 21.62 ≤ 22`,
    `128·838400·2460090368 = 2.6401·10¹⁷ ≤ 27·10¹⁶` (the landed `13·10¹³` was cut at 0.8 %),
    and the exponent `7000·Λ + 500·425 + 6600 ≤ e^Λ/2` at `Λ ≥ 50` (the landed proof's own
    `nlinarith` at `v = e^{Λ/2} ≥ 6·10¹⁰`);
  · the four cap lines at `425` in place of `417`: `+8` (or `+24` on the window line) against
    `449×`, `≈5.5·10³×`, `457×` and the binding `4.1·10⁻⁴·e^{3.2A} ≥ 5·10³²` at `A ≥ 26`.

HONEST LABEL.  Numerals only; nothing here proves an estimate, and nothing bears on twin primes.
Statement-only at the freeze.
-/
import Salt.MR.S16Budget
import Salt.MR.S15SelLinearWide
import Salt.MR.FlatFloorBump
import Salt.MR.XThread
import Salt.MR.S16ProducersH
import Salt.MR.HSeamCheck
import Mathlib

-- The arm's body reaches `XThread`'s own private numeral helper `xt_exp25`
-- (`6·10^10 ≤ e^25`) by `open private`, the corpus's sanctioned device.
open private xt_exp25 from Salt.MR.XThread

noncomputable section

open Salt.Entropy.Chowla

set_option exponentiation.threshold 4000

namespace Salt.MR

/-! ## §1 — THE CHARGE CHAIN AT THE GRADED PIN (`S16Budget.lean:990-1047`'s three walls) -/

/-- **⟦W15 TWIN⟧ (class B)** — `s16_audit_rho_ge_wide_h` (`S16Budget.lean:990`) with `2 ^ 20 ↦
2 ^ 31` in `hδb` and `2 ^ 581 ↦ 2 ^ 592` in the conclusion.  BODY: `S16Budget.lean:993-1015`
verbatim — from `hh1` through the `min 1` branch (`rw [doorRhoOfDelta, le_min_iff]`,
`refine ⟨?_, ?_⟩`) to the closing `exact hδb` — with `2 ^ 581 ↦ 2 ^ 592` at `hkey` and `hsplit1`
and `2 ^ 20 ↦ 2 ^ 31` at `hkey` and `hsplit2`; the `nlinarith [hKb, hK]` closing `hkey` compares
`1768400 = 16·110525` against `2^592/(2^539·2^31) = 2^22` — the SAME margin as landed
(`2^581/(2^539·2^20) = 2^22`), ×2.37. -/
theorem s16_audit_rho_ge_wide_h_g {h : ℕ} (hh : 0 < h) {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K)
    (hδb : 1 / (2 ^ 31 * (h : ℝ) ^ 2) ≤ δ₀) (hKb : K ≤ 2 ^ 539) :
    (1 : ℝ) / (2 ^ 592 * (h : ℝ) ^ 2) ≤ doorRhoOfDelta (s12DeltaSock δ₀ K) := by
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hhsq : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith
  have hh0 : (0 : ℝ) < (h : ℝ) := by linarith
  have hinv : (0 : ℝ) < 1 / (h : ℝ) ^ 2 := by positivity
  rw [doorRhoOfDelta, le_min_iff]
  refine ⟨?_, ?_⟩
  · rw [div_le_one (by positivity)]
    nlinarith [hhsq]
  rw [s12DeltaSock_sq hδ hK, div_div, le_div_iff₀ (by positivity)]
  -- ⟦THE SPLIT⟧ the `h²` is a common factor on both sides; peel it off so the
  -- numeral comparison `1768400 ≤ 2^22` is seen by `nlinarith` on its own.
  have hkey : 1 / (2 : ℝ) ^ 592 * (16 * K * 110525) ≤ 1 / (2 : ℝ) ^ 31 := by
    nlinarith [hKb, hK]
  have hsplit1 : 1 / ((2 : ℝ) ^ 592 * (h : ℝ) ^ 2) * (16 * K * 110525)
      = 1 / (2 : ℝ) ^ 592 * (16 * K * 110525) * (1 / (h : ℝ) ^ 2) := by
    field_simp
  have hsplit2 : 1 / (2 : ℝ) ^ 31 * (1 / (h : ℝ) ^ 2)
      = 1 / ((2 : ℝ) ^ 31 * (h : ℝ) ^ 2) := by
    field_simp
  rw [hsplit1]
  refine le_trans (mul_le_mul_of_nonneg_right hkey hinv.le) ?_
  rw [hsplit2]
  exact hδb

/-- **⟦W16 TWIN⟧ (class A)** — `s16_audit_neglog_rho_le_wide_h` (`S16Budget.lean:1023`) at `2 ^ 31`
and `411 + 2·log h`.  BODY: `S16Budget.lean:1026-1038` verbatim (`hh0` … the closing `linarith`)
with `s16_audit_rho_ge_wide_h_g` at `hge`, `2 ^ 581 ↦ 2 ^ 592` (`hpos`, `h1`, `h2` ×2), `581 ↦
592` in `h2`'s normal form; the closing `linarith` has `411 − 592·0.6931471808 = 0.657` nats. -/
theorem s16_audit_neglog_rho_le_wide_h_g {h : ℕ} (hh : 0 < h) {δ₀ K : ℝ} (hδ : 0 < δ₀)
    (hK : 0 < K) (hδb : 1 / (2 ^ 31 * (h : ℝ) ^ 2) ≤ δ₀) (hKb : K ≤ 2 ^ 539) :
    -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 411 + 2 * Real.log (h : ℝ) := by
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hge := s16_audit_rho_ge_wide_h_g hh hδ hK hδb hKb
  have hpos : (0 : ℝ) < 1 / (2 ^ 592 * (h : ℝ) ^ 2) := by positivity
  have h1 : Real.log ((1 : ℝ) / (2 ^ 592 * (h : ℝ) ^ 2))
      ≤ Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := Real.log_le_log hpos hge
  have h2 : Real.log ((1 : ℝ) / (2 ^ 592 * (h : ℝ) ^ 2))
      = -(592 * Real.log 2) - 2 * Real.log (h : ℝ) := by
    rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow]
    push_cast; ring
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [h2] at h1
  linarith

/-- **⟦W17 TWIN⟧ (class A)** — `s16_audit_neglog_rho_le_417_h` (`S16Budget.lean:1043`) at `2 ^ 31`
and `425`.  BODY: `le_trans (s16_audit_neglog_rho_le_wide_h_g hh hδ hK hδb hKb) (by linarith)`
— `411 + 2·7 = 425` exactly, as the landed `403 + 14 = 417`. -/
theorem s16_audit_neglog_rho_le_425_h {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K)
    (hδb : 1 / (2 ^ 31 * (h : ℝ) ^ 2) ≤ δ₀) (hKb : K ≤ 2 ^ 539) :
    -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 425 := by
  exact le_trans (s16_audit_neglog_rho_le_wide_h_g hh hδ hK hδb hKb) (by linarith)

/-! ## §2 — THE FOUR CAP LINES THE CHARGE-GENERIC REGISTER READS, AT `425`
(`S15SelLinearWide.lean:82-160`; hypothesis weakenings, bodies verbatim) -/

/-- **⟦THE WINDOW LINE AT `425`⟧ (class A)** — `flat_half_line` (`S15SelLinearWide.lean:101`) with
`hc : c ≤ 417 ↦ c ≤ 425`.  BODY: `S15SelLinearWide.lean:104-121` verbatim (`hE17` … the closing
`linarith [hsq, hE2, hc]`); that `linarith` pays
`3·8 = 24` more against `4.1·10⁻⁴·e^{3.2A}` (`≥ 5·10³²` at `A ≥ 26`).  THE BINDING LINE of the
lane (`M` sits at its ceiling by design). -/
theorem flat_half_line_g {A c : ℝ} (hA : 26 ≤ A) (hc : c ≤ 425) :
    (7 / 10 : ℝ) * ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ) + 3 * c
      ≤ Real.exp (3.2 * A) / 2 := by
  have hE17 := flat_exp_half_ge hA
  have hE0 : (0 : ℝ) < Real.exp (3.2 * A / 2) := Real.exp_pos _
  have hMle := flatDoorM_le A
  have hM0 : (0 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := Nat.cast_nonneg _
  have hY := flat_exp_sq A
  have hrow : ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ)
      = 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 := by
    rw [doorRowFloorL, AdoorL]; push_cast; ring
  have h1 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 - ((flatDoorM A : ℕ) : ℝ) := by
    linarith
  have h2 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 + ((flatDoorM A : ℕ) : ℝ) := by
    positivity
  have hsq : ((flatDoorM A : ℕ) : ℝ) ^ 2
      ≤ Real.exp (3.2 * A / 2) ^ 2 / 96286710601 := by
    nlinarith [mul_nonneg h1 h2]
  have hE2 : (10 : ℝ) ^ 34 ≤ Real.exp (3.2 * A / 2) ^ 2 := by nlinarith [hE17, hE0]
  rw [hrow, ← hY]
  linarith [hsq, hE2, hc]

/-- **⟦THE `anchor` LINE AT `425`, DOUBLED `Λ` SLOT⟧ (class A)** — `flat_anchor_line_wide`
(`S15SelLinearWide.lean:91`) with `hc : c ≤ 425`.  BODY: `:94-96` verbatim (`hE17`, `hMge`,
`linarith`; `449×`). -/
theorem flat_anchor_line_wide_g {A c : ℝ} (hA : 26 ≤ A) (hc : c ≤ 425) :
    14 * (2 * Real.exp (3.2 * A / 2)) + c + 33
      ≤ 39 * 10 ^ 8 * ((flatDoorM A : ℕ) : ℝ) := by
  have hE17 := flat_exp_half_ge hA
  have hMge := flatDoorM_ge A
  linarith

/-- **⟦THE `𝒯`-LEG BUDGET AT `−425`⟧ (class A)** — `flat_gP1_line` (`S15SelLinearWide.lean:127`)
with `hc : -417 ≤ c ↦ -425 ≤ c`.  BODY: `:131-148` verbatim (`hE17` … `rw [AdoorL_cast]; linarith`;
`≈5.5·10³×`). -/
theorem flat_gP1_line_g {A c Ct Λ : ℝ} (hA : 26 ≤ A) (hc : -425 ≤ c) (hCt : 0 < Ct)
    (hCtb : Ct ≤ 2 ^ 23) (hΛ : Λ ≤ 2 * Real.exp (3.2 * A / 2)) :
    29 + Real.log Ct + 14 * Λ ≤ ((AdoorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2 + c := by
  have hE17 := flat_exp_half_ge hA
  have hMge := flatDoorM_ge A
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hAdlo : 221460 * Real.exp (3.2 * A / 2) - 68719476737
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) := by linarith
  have hpos : (0 : ℝ) ≤ 221460 * Real.exp (3.2 * A / 2) - 68719476737 := by linarith
  have h1 : (221460 * Real.exp (3.2 * A / 2) - 68719476737) * Real.log 2
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hAdlo (by linarith)
  have hAdlog : 153000 * Real.exp (3.2 * A / 2)
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 := by
    nlinarith [hpos, hlog2lo, hE17]
  have hCtl : Real.log Ct ≤ 23 * Real.log 2 := by
    have h := Real.log_le_log hCt hCtb
    rwa [Real.log_pow] at h
  rw [AdoorL_cast]
  linarith

/-- **⟦THE `level1` BUDGET AT `425`⟧ (class A)** — `flat_lvl_line` (`S15SelLinearWide.lean:153`)
with `hc : c ≤ 425`.  BODY: verbatim (`457×`). -/
theorem flat_lvl_line_g {A c Λ : ℝ} (hA : 26 ≤ A) (hc : c ≤ 425)
    (hΛ : Λ ≤ 2 * Real.exp (3.2 * A / 2)) :
    26 + 14 * Λ
        + (1 / 3) * Real.log (Real.log ((calQK (AdoorL (flatDoorM A))
            (3072 * flatDoorM A) (flatDoorM A) 1 : ℕ) : ℝ)) + c
      ≤ (1 / 12) * ((AdoorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2 := by
  have hE17 := flat_exp_half_ge hA
  have hE0 : (0 : ℝ) < Real.exp (3.2 * A / 2) := Real.exp_pos _
  have hMle := flatDoorM_le A
  have hMge := flatDoorM_ge A
  have hM0 : (0 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hrow : ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ)
      = 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 := by
    rw [doorRowFloorL, AdoorL]; push_cast; ring
  have hAdlo : 221460 * Real.exp (3.2 * A / 2) - 68719476737
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) := by linarith
  have hpos : (0 : ℝ) ≤ 221460 * Real.exp (3.2 * A / 2) - 68719476737 := by linarith
  have h1 : (221460 * Real.exp (3.2 * A / 2) - 68719476737) * Real.log 2
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hAdlo (by linarith)
  have hAdlog : 153000 * Real.exp (3.2 * A / 2)
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 := by
    nlinarith [hpos, hlog2lo, hE17]
  rw [AdoorL_cast, s15_log_calQK_L_one, hrow]
  have hQpos : (0 : ℝ) < 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 * Real.log 2 := by
    have hM1N : 1 ≤ flatDoorM A := flatDoorM_one_le hA
    have hM1 : (1 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := by exact_mod_cast hM1N
    have : (0 : ℝ) < Real.log 2 := by linarith
    positivity
  have hd1 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 - ((flatDoorM A : ℕ) : ℝ) := by
    linarith
  have hd2 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 + ((flatDoorM A : ℕ) : ℝ) := by
    positivity
  have hsq : ((flatDoorM A : ℕ) : ℝ) ^ 2
      ≤ Real.exp (3.2 * A / 2) ^ 2 / 96286710601 := by
    nlinarith [mul_nonneg hd1 hd2]
  have hQle : 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 * Real.log 2
      ≤ Real.exp (3.2 * A / 2) ^ 2 := by
    nlinarith [hsq, hlog2hi, sq_nonneg (Real.exp (3.2 * A / 2)), hM0,
      sq_nonneg ((flatDoorM A : ℕ) : ℝ)]
  have hlogQ : Real.log (68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 * Real.log 2)
      ≤ 2 * Real.log (Real.exp (3.2 * A / 2)) := by
    have h := Real.log_le_log hQpos hQle
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlogE : Real.log (Real.exp (3.2 * A / 2)) ≤ Real.exp (3.2 * A / 2) - 1 :=
    Real.log_le_sub_one_of_pos hE0
  have hbud : 12750 * Real.exp (3.2 * A / 2)
      ≤ 1 / 12 * (68719476736 * ((flatDoorM A : ℕ) : ℝ)) * Real.log 2 := by
    linarith [hAdlog]
  linarith [hΛ, hc, hlogQ, hlogE, hbud, hE17]

/-! ## §3 — THE REGISTER WITNESSES AT THE GRADED CHARGE
(`S15SelLinearWide.lean:219-323`; the structure `S15Sel''_L(_gk)` does not move) -/

/-- **⟦THE REGISTER AT THE FLAT DESIGN POINT, CHARGE-GENERIC, AT `425`⟧ (class B)** —
`s15_sel''_L_witness_flat_charge` (`S15SelLinearWide.lean:219`) with `hρlog : -log ρ ≤ 417 ↦ ≤
425`.  BODY: `S15SelLinearWide.lean:231-254` verbatim — `hbase := s15_sel''_L_witness_flat …` at
the FROZEN dummy literals `δ₀ := 1/2^10`, `K := 1` (:231-233; that call reaches the narrow walls
`s15w_rho_ge`/`s15w_neglog_rho_le` at those literals, which β never moves — only the six `ρ`-free
fields `hM`/`gRows`/`x0M`/`blk` (+ `mfloor`/`bfloor` supplied here) are read off it), `hinv`, and
the `refine` package (:235-254) with the four `_g` lines (`flat_half_line_g`,
`flat_anchor_line_wide_g`, `flat_gP1_line_g`, `flat_lvl_line_g`) at `half`/`anchor`/`gP1`/`lvl`;
the `rho` field (`−log ρ ≤ 10^14`) closes by `linarith [hρlog]` as landed. -/
theorem s15_sel''_L_witness_flat_charge_g {A : ℝ} (hA : 26 ≤ A) {Cg δ₀ Ct ρ : ℝ}
    {x₀ Mfl c : ℕ} {R : ChowlaRegime} (hc1 : 1 ≤ c) (hcb : c ≤ 1096)
    (hρlog : -Real.log ρ ≤ 425)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L Cg δ₀ Ct ρ x₀ Mfl R (flatDoorM A) := by
  have hbase := s15_sel''_L_witness_flat (A := A) (Cg := 0) (δ₀ := 1 / 2 ^ 10) (Ct := 1)
    (K := 1) (x₀ := x₀) (Mfl := Mfl) (c := c) (R := R) hA hc1 hcb (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp) hMfl hx0win heps hlo hhi
  have hinv : Real.log (1 / ρ) = -Real.log ρ := by rw [one_div, Real.log_inv]
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
    exact le_trans (flat_half_line_g hA hρlog) (by linarith [hlo])
  · linarith [hρlog]
  · rw [hinv]
    -- amended per REF-FLAT-SAT: the wide anchor line, at the doubled `Λ` slot
    exact le_trans (by linarith [hhi]) (flat_anchor_line_wide_g hA hρlog)
  · exact flat_gP1_line_g hA (by linarith [hρlog]) hCt hCtb hhi
  · exact flat_lvl_line_g hA hρlog hhi

/-- **⟦THE WIDE ACCEPTANCE AT THE GRADED PIN⟧ (class A)** — `s15_sel''_L_witness_flat_wide`
(`S15SelLinearWide.lean:263`) with `hδb : 1/(2^20·c²) ≤ δ₀ ↦ 1/(2^31·c²) ≤ δ₀`.  BODY:
`s15_sel''_L_witness_flat_charge_g hA hc1 hcb (s16_audit_neglog_rho_le_425_h hc1 hh7c hδ hK hδb
hKb) hCt hCtb hbfl hMfl hx0win heps hlo hhi` (the landed `:277-279` with the two `_g` names). -/
theorem s15_sel''_L_witness_flat_wide_g {A : ℝ} (hA : 26 ≤ A) {Cg δ₀ Ct K : ℝ}
    {x₀ Mfl c : ℕ} {R : ChowlaRegime}
    (hc1 : 1 ≤ c) (hcb : c ≤ 1096) (hh7c : Real.log (c : ℝ) ≤ 7)
    (hδ : 0 < δ₀) (hδb : 1 / (2 ^ 31 * (c : ℝ) ^ 2) ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 539)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R (flatDoorM A) := by
  exact s15_sel''_L_witness_flat_charge_g hA hc1 hcb
    (s16_audit_neglog_rho_le_425_h hc1 hh7c hδ hK hδb hKb) hCt hCtb
    hbfl hMfl hx0win heps hlo hhi

/-- **⟦THE LEVERED WIDE ACCEPTANCE AT THE GRADED PIN⟧ (class A)** —
`s15_sel''_L_gk_witness_flat_wide` (`S15SelLinearWide.lean:301`) with `hδb` at `2 ^ 31`.  BODY:
`s15_sel''_L_gk_of_L Klev (s15_sel''_L_witness_flat_wide_g hA hc1 hcb hh7c hδ hδb hK hKb hCt hCtb
hbfl hMfl hx0win heps hlo hhi) (flat_blk_line_gk hA Klev hKle hc1 hcb heps hlo hhi)` — the `blk`
line is charge-free and is the landed one. -/
theorem s15_sel''_L_gk_witness_flat_wide_g {A : ℝ} (hA : 26 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {Cg δ₀ Ct K : ℝ} {x₀ Mfl c : ℕ}
    {R : ChowlaRegime}
    (hc1 : 1 ≤ c) (hcb : c ≤ 1096) (hh7c : Real.log (c : ℝ) ≤ 7)
    (hδ : 0 < δ₀) (hδb : 1 / (2 ^ 31 * (c : ℝ) ^ 2) ≤ δ₀)
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
    (s15_sel''_L_witness_flat_wide_g hA hc1 hcb hh7c hδ hδb hK hKb hCt hCtb hbfl hMfl hx0win
      heps hlo hhi)
    (flat_blk_line_gk hA Klev hKle hc1 hcb heps hlo hhi)

/-! ## §4 — THE BUMP AND THE BUMPED SELECTOR AT THE GRADED PIN (`FlatFloorBump.lean:127-152`,
`HSeamCheck.lean:92-104`) -/

/-- **⟦BUMP 1 AT THE GRADED PIN⟧ (class B)** — `flatDoorM_bfloor_bump` (`FlatFloorBump.lean:127`)
with `hδb : 1/(838400·c²) ≤ δ₀ ↦ 1/(838400·2^11·c²) ≤ δ₀`.  BODY: `:131-152` verbatim with
`hkey : 1/(838400 * 2 ^ 11) ≤ c² · δ₀`, `hstep : 24·Cg/δ₀ ≤ 82418073600000000000000 · c²`
(`= 24·2·10¹²·838400·2048`), `hcap` through `h355 : (10 ^ 29 : ℝ) ≤ 2 ^ 355` (`8.2418·10²²·1201216
= 9.9002·10²⁸`), then `flatDoorM_ge_pow355 hA` as landed — the same route change the landed bump
took (`flatDoorM_ge_bfloorConst` has ZERO slack and cannot carry a factor). -/
theorem flatDoorM_bfloor_bump_g {A Cg δ₀ : ℝ} {c : ℕ} (hc1 : 1 ≤ c) (hcb : c ≤ 1096)
    (hA : 162 ≤ A) (hδ : 0 < δ₀)
    (hδb : 1 / (838400 * 2 ^ 11 * (c : ℝ) ^ 2) ≤ δ₀) (hCg : Cg ≤ 2 * 10 ^ 12) :
    24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ) := by
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hcRb : (c : ℝ) ≤ 1096 := by exact_mod_cast hcb
  have hcsqb : (c : ℝ) ^ 2 ≤ 1201216 := by nlinarith [hcR1, hcRb]
  have hcsq1 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by nlinarith [hcR1]
  -- ⟦THE ROUTE CHANGE⟧ as in the landed bump: `flatDoorM_ge_bfloorConst` has ZERO slack
  -- and cannot carry the `c²`, let alone the extra `2^11`; the route is
  -- `flatDoorM_ge_pow355` (`2^355 ≈ 7.3·10^106`), which clears `9.9·10^28` by 78 orders.
  have hcsqpos : (0 : ℝ) < (c : ℝ) ^ 2 := by nlinarith [hcR1]
  have hkey : (1 : ℝ) / (838400 * 2 ^ 11) ≤ (c : ℝ) ^ 2 * δ₀ := by
    have h := mul_le_mul_of_nonneg_left hδb hcsqpos.le
    calc (1 : ℝ) / (838400 * 2 ^ 11)
        = (c : ℝ) ^ 2 * (1 / (838400 * 2 ^ 11 * (c : ℝ) ^ 2)) := by field_simp
      _ ≤ (c : ℝ) ^ 2 * δ₀ := h
  have hstep : 24 * Cg / δ₀ ≤ (82418073600000000000000 : ℝ) * (c : ℝ) ^ 2 := by
    rw [div_le_iff₀ hδ]
    nlinarith [hkey, hCg]
  have hcap : (82418073600000000000000 : ℝ) * (c : ℝ) ^ 2 ≤ (2 : ℝ) ^ (355 : ℕ) := by
    have h355 : (10 ^ 29 : ℝ) ≤ (2 : ℝ) ^ (355 : ℕ) := by norm_num
    nlinarith [hcsqb, h355]
  have hpow : (2 : ℝ) ^ (355 : ℕ) ≤ ((flatDoorM A : ℕ) : ℝ) := by
    exact_mod_cast flatDoorM_ge_pow355 hA
  linarith [hstep, hcap, hpow]

/-- **⟦THE BUMPED WINDOWED SELECTOR AT SHIFT `h`, GRADED⟧ (class A)** — the name the graded H3→H4
replay calls in place of `s15_sel''_L_gk_witness_flat_bumped_win_h` (`HSeamCheck.lean:92`,
signature identical, `hδb` at `838400 * 2 ^ 11`).  BODY (`FlatFloorBump.lean:353-376`'s
`_bumped_win` at `c := h`, folded): `s15_sel''_L_gk_witness_flat_wide_g (flat162_ge_26 hA) Klev
hKle hh (h_le_1096_of_hh7 hh hh7) hh7 hδ ⟨the bridge⟩ hK hKb hCt hCtb (flatDoorM_bfloor_bump_g hh
(h_le_1096_of_hh7 hh hh7) hA hδ hδb hCg) hMfl hx0win heps hlo hhi`, where ⟨the bridge⟩ is
`1/(2^31·h²) ≤ 1/(838400·2^11·h²) ≤ δ₀` by `div_le_div_iff₀` + `nlinarith [h1]` exactly as at
`FlatFloorBump.lean:372-373` (`h1 : 0 < c²` at :369-371; `838400·2048 = 1717043200 ≤ 2^31`). -/
theorem s15_sel''_L_gk_witness_flat_bumped_win_h_g {A : ℝ} (hA : 162 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {Cg δ₀ Ct K : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime}
    (hδ : 0 < δ₀) (hδb : 1 / (838400 * 2 ^ 11 * (h : ℝ) ^ 2) ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 539)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hCg : Cg ≤ 2 * 10 ^ 12) (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (h : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L_gk Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R (flatDoorM A) := by
  exact s15_sel''_L_gk_witness_flat_wide_g (flat162_ge_26 hA) Klev hKle hh
    (h_le_1096_of_hh7 hh hh7) hh7 hδ
    (by
      have h1 : (0 : ℝ) < (h : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
        positivity
      have : (1 : ℝ) / (2 ^ 31 * (h : ℝ) ^ 2) ≤ 1 / (838400 * 2 ^ 11 * (h : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [h1]
      linarith [hδb] : (1 : ℝ) / (2 ^ 31 * (h : ℝ) ^ 2) ≤ δ₀) hK hKb hCt hCtb
    (flatDoorM_bfloor_bump_g hh (h_le_1096_of_hh7 hh hh7) hA hδ hδb hCg)
    hMfl hx0win heps hlo hhi

/-! ## §5 — THE ARM AT THE GRADED PIN (`XThread.lean:345-533`, `S16ProducersH.lean:793-830`) -/

set_option maxHeartbeats 2000000 in
-- as `XThread.lean:330` above the landed `s15Arm_log_le_scaled`: the arm's four summands,
-- the double exponential's collapse and the closing budget elaborate in one block
/-- **⟦THE ARM, PRICED, AT A `c`-CEILING THAT ADMITS `2^11·h²`⟧ (class B)** —
`s15Arm_log_le_scaled` (`XThread.lean:345`) with `hcb : c ≤ 1201216 ↦ c ≤ 2460090368` and
`hlogc : log c ≤ 14 ↦ ≤ 22`; conclusion unchanged.  ⛔ The landed lemma CANNOT be reused at
`c = 2^11·h²`: both binders fail (`log(2^11·1201216) = 21.62`).  ⚠ `2460090368 = 2^11·1096²`
EXACTLY — the `c`-ceiling has ZERO margin; it is safe only because its sole supplier (`h ≤ 1096`
in `s15ArmH_log_le_g`) is itself the exact `⌊e^7⌋` bound, and a raise of `h`'s cap re-cuts it.
BODY: `XThread.lean:351-534` verbatim — from `have hc0 : 0 < c` and `set ρ := …` (:351-352) to
the closing `linarith [hlog, hprod, hω1, hclose]` (:534) — with NINE numeral sites moved in THREE
families, each anchored by its `have`-name (the line numbers are at `main 9a2b3053`):
  · `hρlog : log(1/ρ) ≤ 417 ↦ ≤ 425` (:355-356; `xt_log_inv_rho_le_scaled` gives `403 + log c`
    and `hlogc` gives `log c ≤ 22`);
  · EVERY `1201216 ↦ 2460090368` — FOUR sites: `hceil1`'s statement (:421), `hdiv` (:425),
    `hpin'` (:427), and `hstep`'s LHS (:472).  ⛔ The fourth is not optional: with :472 left at
    `1201216` the `linarith [hceil1, hceil2, hstep, hmul]` at :482 is unclosable
    (`2.64·10¹⁷·ω ≤ 1.29·10¹⁴·ω` is false for `ω ≥ 1`);
  · `13 * 10 ^ 13 ↦ 27 * 10 ^ 16` — FIVE sites: `hHhibig` (:441, still from `u ≥ 1.8·10²¹`),
    `hfac` (:457), `h2` (:463), `hstep`'s RHS (:474), `hmul` (:477);
    `128·838400·2460090368 = 2.6401·10¹⁷ ≤ 2.7·10¹⁷` (2.27 %).
`hE : E ≤ L/2` closes by the same `nlinarith [hρlog, hΛv, hvv, hv]` (`7000·2(v−1) + 212500 +
6600 ≤ v²/2` at `v ≥ 6·10¹⁰`).  ⛔ THE CONTROL (K5, the executor RECORDS it before landing this
name): with `hcb`/`hlogc` at the new ceiling and `hstep`'s `13 * 10 ^ 13` LEFT LANDED, `hstep`
must FAIL (`128·838400·2460090368 = 2.64·10¹⁷ > 1.3·10¹⁴`, a factor 2048). -/
theorem s15Arm_log_le_scaled_g {c δ₀ Kc : ℝ} (hc1 : 1 ≤ c) (hcb : c ≤ 2460090368)
    (hlogc : Real.log c ≤ 22) (hδ₀ : 0 < δ₀) (hδpin : 1 / (838400 * c) ≤ δ₀)
    (hKc : 0 < Kc) (hKcb : Kc ≤ 2 ^ 539) {Hhi ω : ℕ} (hHhi : 4000000 ≤ Hhi)
    (hΛ : 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ Real.log ((ω : ℕ) : ℝ) + ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
  have hc0 : (0 : ℝ) < c := by linarith
  set ρ : ℝ := doorRhoOfDelta (s12DeltaSock δ₀ Kc) with hρdef
  have hδs : 0 < s12DeltaSock δ₀ Kc := s12DeltaSock_pos hδ₀ hKc
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρlog : Real.log (1 / ρ) ≤ 425 :=
    le_trans (xt_log_inv_rho_le_scaled hc1 hδ₀ hδpin hKc hKcb) (by linarith)
  -- ⟦THE SCALES⟧ `L = log H₊`, `Λ = loglog H₊`, and their two exponential witnesses
  set L : ℝ := Real.log ((Hhi : ℕ) : ℝ) with hLdef
  set Λ : ℝ := Real.log L with hΛdef
  have hHhiR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hHhi
  have hHhipos : (0 : ℝ) < ((Hhi : ℕ) : ℝ) := by linarith
  have hL0 : (0 : ℝ) ≤ L := Real.log_nonneg (by linarith)
  have hL1 : (1 : ℝ) < L := one_lt_log_of_loglog_ge hL0 (by norm_num : (0 : ℝ) < 50) hΛ
  have hΛ0 : (0 : ℝ) ≤ Λ := Real.log_nonneg hL1.le
  -- `v := e^{Λ/2}`, so `v² = L` and `v ≥ 6·10^{10}`
  set v : ℝ := Real.exp (Λ / 2) with hvdef
  have hvv : v * v = L := by
    rw [hvdef, ← Real.exp_add, show Λ / 2 + Λ / 2 = Λ by ring, hΛdef]
    exact Real.exp_log (by linarith)
  have hv : (6e10 : ℝ) ≤ v := by
    refine le_trans xt_exp25 ?_
    rw [hvdef]
    exact Real.exp_le_exp.mpr (by linarith)
  have hΛv : Λ ≤ 2 * (v - 1) := by
    have := Real.add_one_le_exp (Λ / 2)
    rw [← hvdef] at this
    linarith
  have hLbig : (3.6e21 : ℝ) ≤ L := by nlinarith [hvv, hv]
  -- `u := e^{L/2}`, so `u² = H₊`
  set u : ℝ := Real.exp (L / 2) with hudef
  have huu : u * u = ((Hhi : ℕ) : ℝ) := by
    rw [hudef, ← Real.exp_add, show L / 2 + L / 2 = L by ring, hLdef]
    exact Real.exp_log hHhipos
  have hLu : L ≤ 2 * (u - 1) := by
    have := Real.add_one_le_exp (L / 2)
    rw [← hudef] at this
    linarith
  have hu : (1.8e21 : ℝ) ≤ u := by linarith
  -- ⟦THE EXPONENT⟧ `E ≤ L/2`
  set E : ℝ := 7000 * Λ + 500 * Real.log (1 / ρ) + 6600 + 36 * 0 with hEdef
  have hE : E ≤ L / 2 := by
    rw [hEdef]
    nlinarith [hρlog, hΛv, hvv, hv]
  have hexpE : Real.exp E ≤ u := by
    rw [hudef]; exact Real.exp_le_exp.mpr hE
  -- ⟦THE ARM, BOUNDED⟧
  have hωnn : (0 : ℝ) ≤ ((ω : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlogωnn : (0 : ℝ) ≤ Real.log ((ω : ℕ) : ℝ) := Real.log_natCast_nonneg ω
  -- the `ρ`-arm's closed form
  have harc : arcDen 12 Hhi = Real.exp (12 * Λ) := by
    rw [arcDen, ← hLdef, Real.rpow_def_of_pos (by linarith), hΛdef]
    congr 1
    ring
  have hG : gArmDoorRho 0 0 ((ω : ℕ) : ℝ) ρ Hhi
      = 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by
    have hsplit : Real.exp (12 * Λ + Real.exp E)
        = Real.exp (12 * Λ) * Real.exp (Real.exp E) := Real.exp_add _ _
    have hnn : (0 : ℝ) ≤ 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ) * Real.exp (Real.exp E) := by
      positivity
    rw [gArmDoorRho, harc, ← hLdef, ← hΛdef, ← hEdef, max_eq_right hnn, hsplit]
    ring
  -- the sum, cast
  have hcast : ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
      = 2 * ((ω : ℕ) : ℝ) * (((Hhi : ℕ) : ℝ) + 2) + 8 * ((ω : ℕ) : ℝ)
        + ((⌈128 * ((ω : ℕ) : ℝ) / δ₀⌉₊ : ℕ) : ℝ)
        + ((⌈gArmDoorRho 0 0 ((ω : ℕ) : ℝ) ρ Hhi⌉₊ : ℕ) : ℝ) := by
    rw [s15Arm, s13GArm']
    push_cast
    ring
  have hceil1 : ((⌈128 * ((ω : ℕ) : ℝ) / δ₀⌉₊ : ℕ) : ℝ)
      ≤ 128 * 838400 * 2460090368 * ((ω : ℕ) : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ 128 * ((ω : ℕ) : ℝ) / δ₀ := by positivity
    have hlt : ((⌈128 * ((ω : ℕ) : ℝ) / δ₀⌉₊ : ℕ) : ℝ) < 128 * ((ω : ℕ) : ℝ) / δ₀ + 1 :=
      Nat.ceil_lt_add_one h0
    have hdiv : 128 * ((ω : ℕ) : ℝ) / δ₀ ≤ 128 * 838400 * 2460090368 * ((ω : ℕ) : ℝ) := by
      rw [div_le_iff₀ hδ₀]
      have hpin' : 1 / (838400 * 2460090368 : ℝ) ≤ δ₀ := by
        refine le_trans ?_ hδpin
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [hcb, hc0]
      nlinarith [hωnn, hpin']
    linarith
  have hceil2 : ((⌈gArmDoorRho 0 0 ((ω : ℕ) : ℝ) ρ Hhi⌉₊ : ℕ) : ℝ)
      ≤ 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) + 1 := by
    rw [hG]
    have h0 : (0 : ℝ) ≤ 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by positivity
    linarith [Nat.ceil_lt_add_one h0]
  -- ⟦THE ENVELOPE⟧ `S ≤ (ω+1)·e^Y` at `Y = L + 12λ + e^E + 6`
  have hX1 : (1 : ℝ) ≤ Real.exp (12 * Λ + Real.exp E) :=
    Real.one_le_exp (by positivity)
  have hHhibig : (27 * 10 ^ 16 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by nlinarith [huu, hu]
  have he6 : (19 : ℝ) ≤ Real.exp 6 := by
    have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h : Real.exp (6 : ℝ) = (Real.exp 1) ^ (6 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    have hc : (2.7 : ℝ) ^ (6 : ℕ) ≤ (Real.exp 1) ^ (6 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he1.le 6
    have hn : (19 : ℝ) ≤ (2.7 : ℝ) ^ (6 : ℕ) := by norm_num
    linarith
  have hYeq : Real.exp (L + (12 * Λ + Real.exp E) + 6)
      = ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) * Real.exp 6 := by
    rw [Real.exp_add, Real.exp_add, hLdef, Real.exp_log hHhipos]
  have henv : ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
      ≤ (((ω : ℕ) : ℝ) + 1) * Real.exp (L + (12 * Λ + Real.exp E) + 6) := by
    rw [hcast, hYeq]
    have hfac : 2 * ((Hhi : ℕ) : ℝ) + 27 * 10 ^ 16
          + 16 * Real.exp (12 * Λ + Real.exp E)
        ≤ ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) * Real.exp 6 := by
      have h1 : 2 * ((Hhi : ℕ) : ℝ)
          ≤ 2 * (((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E)) := by
        nlinarith [hX1, hHhiR]
      have h2 : (27 * 10 ^ 16 : ℝ)
          ≤ ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by
        nlinarith [hX1, hHhibig]
      have h3 : 16 * Real.exp (12 * Λ + Real.exp E)
          ≤ 16 * (((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E)) := by
        nlinarith [hX1, hHhiR, Real.exp_pos (12 * Λ + Real.exp E)]
      have hprodnn : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by positivity
      nlinarith [h1, h2, h3, he6, hprodnn]
    have hstep : 2 * ((ω : ℕ) : ℝ) * (((Hhi : ℕ) : ℝ) + 2) + 8 * ((ω : ℕ) : ℝ)
        + (128 * 838400 * 2460090368 * ((ω : ℕ) : ℝ) + 1)
        + (16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) + 1)
        ≤ (((ω : ℕ) : ℝ) + 1) * (2 * ((Hhi : ℕ) : ℝ) + 27 * 10 ^ 16
            + 16 * Real.exp (12 * Λ + Real.exp E)) := by
      nlinarith [hωnn, hX1, hHhiR, Real.exp_pos (12 * Λ + Real.exp E)]
    have hmul : (((ω : ℕ) : ℝ) + 1) * (2 * ((Hhi : ℕ) : ℝ) + 27 * 10 ^ 16
          + 16 * Real.exp (12 * Λ + Real.exp E))
        ≤ (((ω : ℕ) : ℝ) + 1)
          * (((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) * Real.exp 6) :=
      mul_le_mul_of_nonneg_left hfac (by linarith)
    linarith [hceil1, hceil2, hstep, hmul]
  -- ⟦THE LOG⟧
  rcases Nat.eq_zero_or_pos (s15Arm δ₀ ρ Hhi ω) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    have : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by positivity
    linarith
  · have hSpos : (0 : ℝ) < ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ) := by exact_mod_cast hpos
    have hlog := Real.log_le_log hSpos henv
    have hprod : Real.log ((((ω : ℕ) : ℝ) + 1) * Real.exp (L + (12 * Λ + Real.exp E) + 6))
        = Real.log (((ω : ℕ) : ℝ) + 1) + (L + (12 * Λ + Real.exp E) + 6) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
    -- `log(ω+1) ≤ log ω + log 2`
    have hω1 : Real.log (((ω : ℕ) : ℝ) + 1) ≤ Real.log ((ω : ℕ) : ℝ) + Real.log 2 := by
      rcases Nat.eq_zero_or_pos ω with hz | hz
      · rw [hz]
        simp only [Nat.cast_zero, Real.log_zero, zero_add, Real.log_one]
        linarith [Real.log_two_gt_d9]
      · have hω1R : (1 : ℝ) ≤ ((ω : ℕ) : ℝ) := by exact_mod_cast hz
        have hle : ((ω : ℕ) : ℝ) + 1 ≤ 2 * ((ω : ℕ) : ℝ) := by linarith
        have h := Real.log_le_log (by linarith : (0 : ℝ) < ((ω : ℕ) : ℝ) + 1) hle
        rwa [Real.log_mul (by norm_num) (by linarith), add_comm (Real.log 2)] at h
    -- the closing budget
    have hΛL : Λ ≤ L := by nlinarith [hΛv, hvv, hv]
    have hclose : Real.log 2 + (L + (12 * Λ + Real.exp E) + 6)
        ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
      -- ⟦THE TOWER STEP⟧ `u = e^{L/2} = (e^{L/4})² ≥ (1 + L/4)²`, so with `L ≥ 3.6·10^21`
      -- the linear witness `u ≥ 1.8·10^21` is upgraded to `u ≥ 8.1·10^41` — which is what
      -- buys the deeper cut `H₊/10^20` in place of `H₊/10^6`.  The headroom here is a TOWER
      -- (`XCeilGate` carries `50 ≤ loglog H₊`), so the extra fourteen orders are free.
      have hq := Real.add_one_le_exp (L / 4)
      have hq0 : (0 : ℝ) ≤ Real.exp (L / 4) := (Real.exp_pos _).le
      have hqL : (9 * 10 ^ 20 : ℝ) ≤ Real.exp (L / 4) := by linarith only [hq, hLbig]
      have hsq : Real.exp (L / 4) * Real.exp (L / 4) = u := by
        rw [← Real.exp_add, show L / 4 + L / 4 = L / 2 by ring, hudef]
      have hu41 : (8 * 10 ^ 41 : ℝ) ≤ u := by
        rw [← hsq]
        calc (8 * 10 ^ 41 : ℝ) ≤ (9 * 10 ^ 20) * (9 * 10 ^ 20) := by norm_num
          _ ≤ Real.exp (L / 4) * Real.exp (L / 4) :=
              mul_le_mul hqL hqL (by norm_num) hq0
      -- keep every step LINEAR in `u`: the one product is isolated in `hsquare`.
      have hupos : (0 : ℝ) < u := by linarith only [hu41]
      have hlin : L + 12 * Λ + Real.exp E + 6.7 ≤ 27 * u := by
        linarith only [hexpE, hΛL, hLu]
      have h27 : (27 : ℝ) * 10 ^ 20 ≤ u := by linarith only [hu41]
      have hsquare : 27 * u * 10 ^ 20 ≤ u * u := by
        have hm := mul_le_mul_of_nonneg_right h27 hupos.le
        linarith only [hm]
      have hstep : L + 12 * Λ + Real.exp E + 6.7 ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
        rw [← huu, le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 20)]
        linarith only [hlin, hsquare]
      linarith [Real.log_two_lt_d9]
    linarith [hlog, hprod, hω1, hclose]

/-- **⟦THE ARM'S LOG AT SHIFT `h`, GRADED⟧ (class A)** — `s15ArmH_log_le` (`S16ProducersH.lean:793`)
with `hδpin` at `838400 * 2 ^ 11`; conclusion unchanged — the name the graded H2→H3 replay calls.
BODY: `S16ProducersH.lean:799-828` verbatim (`hh1R` … the closing `linarith`) with `hcb : (2 ^ 11
: ℝ) * h² ≤ 2460090368` (from `h1096 : h ≤ 1096`; ⚠ EXACT — `2^11·1096² = 2460090368`, zero
margin, safe only because `h_le_1096_of_hh7` is itself the exact `⌊e^7⌋` bound),
`hlogc : log (2 ^ 11 * h²) ≤ 22` (`Real.log_mul`, `Real.log_pow` twice, `11·log 2 < 7.6247`,
`2·log h ≤ 14`), `hδpin' : 1 / (838400 * (2 ^ 11 * h²)) ≤ δ₀` by `rw [← mul_assoc]` from `hδpin`,
`hc1 : 1 ≤ 2 ^ 11 * h²`, and `hbase := s15Arm_log_le_scaled_g hc1 hcb hlogc hδ₀ hδpin' hKc hKcb
hHhi hΛ`; the `s15ArmH_le_mul` step and the log split are the landed ones. -/
theorem s15ArmH_log_le_g {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {δ₀ Kc : ℝ}
    (hδ₀ : 0 < δ₀) (hδpin : 1 / (838400 * 2 ^ 11 * (h : ℝ) ^ 2) ≤ δ₀)
    (hKc : 0 < Kc) (hKcb : Kc ≤ 2 ^ 539) {Hhi ω : ℕ}
    (hHhi : 4000000 ≤ Hhi) (hΛ : 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ Real.log ((ω : ℕ) : ℝ) + Real.log (h : ℝ) + ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
  have hh1R : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hc1 : (1 : ℝ) ≤ (2 : ℝ) ^ 11 * (h : ℝ) ^ 2 := by nlinarith [hh1R]
  have h1096 : (h : ℝ) ≤ 1096 := by exact_mod_cast h_le_1096_of_hh7 hh hh7
  have hcb : (2 : ℝ) ^ 11 * (h : ℝ) ^ 2 ≤ 2460090368 := by nlinarith [hh1R, h1096]
  have hlogc : Real.log ((2 : ℝ) ^ 11 * (h : ℝ) ^ 2) ≤ 22 := by
    have hhpos : (0 : ℝ) < (h : ℝ) := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    push_cast
    linarith
  have hδpin' : 1 / (838400 * ((2 : ℝ) ^ 11 * (h : ℝ) ^ 2)) ≤ δ₀ := by
    rw [← mul_assoc]; exact hδpin
  have hbase := s15Arm_log_le_scaled_g hc1 hcb hlogc hδ₀ hδpin' hKc hKcb (ω := ω) hHhi hΛ
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

end Salt.MR

end
