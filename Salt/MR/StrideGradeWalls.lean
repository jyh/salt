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
  sorry

/-- **⟦W16 TWIN⟧ (class A)** — `s16_audit_neglog_rho_le_wide_h` (`S16Budget.lean:1023`) at `2 ^ 31`
and `411 + 2·log h`.  BODY: `S16Budget.lean:1026-1038` verbatim (`hh0` … the closing `linarith`)
with `s16_audit_rho_ge_wide_h_g` at `hge`, `2 ^ 581 ↦ 2 ^ 592` (`hpos`, `h1`, `h2` ×2), `581 ↦
592` in `h2`'s normal form; the closing `linarith` has `411 − 592·0.6931471808 = 0.657` nats. -/
theorem s16_audit_neglog_rho_le_wide_h_g {h : ℕ} (hh : 0 < h) {δ₀ K : ℝ} (hδ : 0 < δ₀)
    (hK : 0 < K) (hδb : 1 / (2 ^ 31 * (h : ℝ) ^ 2) ≤ δ₀) (hKb : K ≤ 2 ^ 539) :
    -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 411 + 2 * Real.log (h : ℝ) := by
  sorry

/-- **⟦W17 TWIN⟧ (class A)** — `s16_audit_neglog_rho_le_417_h` (`S16Budget.lean:1043`) at `2 ^ 31`
and `425`.  BODY: `le_trans (s16_audit_neglog_rho_le_wide_h_g hh hδ hK hδb hKb) (by linarith)`
— `411 + 2·7 = 425` exactly, as the landed `403 + 14 = 417`. -/
theorem s16_audit_neglog_rho_le_425_h {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K)
    (hδb : 1 / (2 ^ 31 * (h : ℝ) ^ 2) ≤ δ₀) (hKb : K ≤ 2 ^ 539) :
    -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 425 := by
  sorry

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
  sorry

/-- **⟦THE `anchor` LINE AT `425`, DOUBLED `Λ` SLOT⟧ (class A)** — `flat_anchor_line_wide`
(`S15SelLinearWide.lean:91`) with `hc : c ≤ 425`.  BODY: `:94-96` verbatim (`hE17`, `hMge`,
`linarith`; `449×`). -/
theorem flat_anchor_line_wide_g {A c : ℝ} (hA : 26 ≤ A) (hc : c ≤ 425) :
    14 * (2 * Real.exp (3.2 * A / 2)) + c + 33
      ≤ 39 * 10 ^ 8 * ((flatDoorM A : ℕ) : ℝ) := by
  sorry

/-- **⟦THE `𝒯`-LEG BUDGET AT `−425`⟧ (class A)** — `flat_gP1_line` (`S15SelLinearWide.lean:127`)
with `hc : -417 ≤ c ↦ -425 ≤ c`.  BODY: `:131-148` verbatim (`hE17` … `rw [AdoorL_cast]; linarith`;
`≈5.5·10³×`). -/
theorem flat_gP1_line_g {A c Ct Λ : ℝ} (hA : 26 ≤ A) (hc : -425 ≤ c) (hCt : 0 < Ct)
    (hCtb : Ct ≤ 2 ^ 23) (hΛ : Λ ≤ 2 * Real.exp (3.2 * A / 2)) :
    29 + Real.log Ct + 14 * Λ ≤ ((AdoorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2 + c := by
  sorry

/-- **⟦THE `level1` BUDGET AT `425`⟧ (class A)** — `flat_lvl_line` (`S15SelLinearWide.lean:153`)
with `hc : c ≤ 425`.  BODY: verbatim (`457×`). -/
theorem flat_lvl_line_g {A c Λ : ℝ} (hA : 26 ≤ A) (hc : c ≤ 425)
    (hΛ : Λ ≤ 2 * Real.exp (3.2 * A / 2)) :
    26 + 14 * Λ
        + (1 / 3) * Real.log (Real.log ((calQK (AdoorL (flatDoorM A))
            (3072 * flatDoorM A) (flatDoorM A) 1 : ℕ) : ℝ)) + c
      ≤ (1 / 12) * ((AdoorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2 := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-! ## §5 — THE ARM AT THE GRADED PIN (`XThread.lean:345-533`, `S16ProducersH.lean:793-830`) -/

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
  sorry

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
  sorry

end Salt.MR

end
