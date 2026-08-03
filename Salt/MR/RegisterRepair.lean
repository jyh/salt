/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RegisterInhabit

/-!
# `RegisterRepair` — ⟦THE CO-FACTOR REGISTER, REPAIRED AT THE `D`-LADDER⟧

`RegisterInhabit` refuted `CofactorBulkL` at the terminal and priced the repair to the
exponent: the defect is `CofactorBulk` §1's TRIVIAL dilation ladder `D(j) = 1`, which turns
`m4_supplier_complete`'s exit charge `cSq·D^{−1/4}` into a constant floor under a ceiling that
must decay (`s16cof_exit_decay`: `Rbd ≤ (log X)^{−2θ₂₉₃}/√(1728·C_q)`), and the price is
`D ≳ (log X)^{8θ₂₉₃}` (`cofk_dilation_price`).

This file spends that price.  The ladder is re-instantiated at

  **`D(j) := ⌈log X⌉₊`** — one exponent of room over the priced floor, and far under law
  #253's own ceiling `D ≲ √k₀`,

and the register is not carried but **INHABITED**: every one of the seventeen conjuncts is a
theorem at the terminal's own scale, off ONE named hypothesis (the `K_vt` cushion, whose
Siegel-genre opacity `RegisterInhabit` traced to `SiegelArm`'s EVT minimum).

## §1 — THE BAND'S OWN LOWER BOUND, SHARPENED

`RegisterInhabit`'s `cofk_sqrt_le_ramRbot` proved `B_v ≥ √X` at every block.  The `D`-ladder
needs one notch more, because dividing `k₀` by `D` costs `loglog X` in the log: the band's
TRUE bottom is `log B_v ≥ (1 − 1/loglog X)·log X` (`cofkR_band_log_lower`), i.e. exactly the
`caseAS`-page descent gate at the block level.  Off that, `log ⌊k₀/D⌋ ≥ (log X)/2` with an
enormous margin, and the three landed pricing pages (`logW_rpow_le`, `farMain_priced`,
`farErr34_local_closes_of_gate`) all apply at the divided window.

## §2 — THE EXIT, RE-PRICED AGAINST THE **FREE** `C_R`

`S16CofactorSupply_L_gk`'s `C_R` is existential.  With the repaired ladder every summand of the
supplier's exit charge decays at rate at least `ρ₂₉₃ = 3θ₂₉₃`:

| summand | rate | page |
|---|---|---|
| `C₁·e^{−(1/e)·cofactorMfl}` | `ρ₂₉₃` | `cofactorMfl_grade_293` |
| `farCStar2·(log W)^{−1/(32e)}` | `1/(32e) ≈ 3.37·θ₂₉₃` | `logW_rpow_le` |
| `4·(log X_a)^{−1/2+1/1000}` | `0.499` | `logW_rpow_le` |
| `cSq·D^{−1/4}` | `1/4` (at `D = ⌈log X⌉₊`) | the repair |
| `2√2/seamRad X` | `1/46 ≈ 6.4·θ₂₉₃` | `farMain_priced` |
| `farErr34 k₀ M T*₂` | `ρ₂₉₃` | `farErr34_local_closes_of_gate` |

so `S ≤ Sconst·(log X)^{−ρ₂₉₃}` and `R̄₀ ≤ Rconst·(log X)^{−ρ₂₉₃}` with `Sconst`/`Rconst` FIXED
constants (`cofkRSconst`, `cofkRConst`).  Choosing `C_R := 4·Rconst` — a constant, not
`gradeCR2 Cb` — makes the first grading conjunct an identity and turns the second into the
single scale gate `1728·C_q·(4·Rconst)² ≤ (log X)^{2θ₂₉₃}`, which the design constant `A`
absorbs.  THAT is the whole content of the repair: the register's refuted chain
`24·cSq·(log X)^{ρ₂₉₃} ≤ gradeCR2 Cb` is replaced by a gate on `A` that a terminal choosing
`A` AFTER `C_q` can meet.

## §3 — THE TWO CONTOUR BOXES ARE THEOREMS, NOT GATES

`RegisterInhabit` recorded conjuncts 9/10 as needing `Tstar2` monotonicity "which the corpus
does not state at this generality".  That reading was stale: `PinFamily2.Tstar2_mono` is real
valued and fully general above `pin2Gate`, and `FrameWitness.Tstar2_le_self` closes it at the
top — the only missing stone was its side condition `2·(log X)^{3/5} ≤ log X`, three lines
from `pin2_powers` (`cofkR_two_rpow_three_fifths`).  Both boxes fall with a full `X` of slack
(`cofkR_box_of_le`).

## §4 — THE `T`-WINDOW CONJUNCTS ARE THE SOCKET'S OWN ARITHMETIC

Conjuncts 2/3 (`Q ≤ 2T` and `30·log X/loglog X ≤ log 2T`) look like gates on the caller's `T`,
and `RegisterInhabit` left them unexamined.  They are theorems: `S13CapFloor.capfloor_core`
proves `log T_ann ≥ (log X)/2` at EVERY socket and every admissible `T`, because the socket
base forces `2^j ≤ H` and `log H ≤ √H/2 ≤ (log X)/2`.  So the `T`-window costs `loglog X ≥ 60`
and nothing else.

**PURELY ADDITIVE.**  No landed declaration is touched.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — ⟦THE REPAIRED LADDER'S CONSTANTS⟧

Three closed forms.  `cofkRSconst` is the uniform CASE-A exit constant, `cofkRConst` the
uniform `R̄₀` constant (`cofactorRbdGen`'s `3·max(2S, far)` at both), and `cofkRThr` the ONE
scale threshold the whole repair runs on — stated in-statement, never absorbed (law #253). -/

/-- **THE UNIFORM CASE-A EXIT CONSTANT AT THE REPAIRED LADDER** (`cofkRSconst`).
`cSq·(3·C₁(1/e,Cb) + 2·C_far*₂ + 9)`: three units for the grade summand's descent factor, two
for the `1/(32e)` summand, eight for the `0.499` summand, one for the `cSq·D^{−1/4}` charge. -/
def cofkRSconst (Cb : ℝ) : ℝ :=
  cSq * (3 * gradeAbsConstC (1 / Real.exp 1) Cb + 2 * farCStar2 + 9)

/-- **THE UNIFORM `R̄₀` CONSTANT** (`cofkRConst`).  `cofactorRbdGen = 3·max(2S, farSupS34)`
with the far arm at `2√2/seamRad + farErr34 ≤ 5·(log X)^{−ρ₂₉₃}`. -/
def cofkRConst (Cb : ℝ) : ℝ := 3 * (2 * cofkRSconst Cb + 5)

/-- **THE ONE SCALE THRESHOLD** (`cofkRThr`).  Everything the repaired register asks of the
scale, in one closed form on `log H₋`: `10⁶` for headroom, `Xsk` for the
supplier's opaque wide threshold, `Y0` for the GS-7.1 certificate's own threshold
(`farErr34_local_closes`), and `450·log(1 + C_q + Rconst)` for the grading gate
`1728·C_q·(4·Rconst)² ≤ (log X)^{2θ₂₉₃}`.  Every summand is a quantity the terminal's design
constant `A` can be chosen above — provided `A` is chosen AFTER `C_q`, which is what the
`∃C_q ∀K` hoist buys. -/
def cofkRThr (Cq Cb Xsk Y0 : ℝ) : ℝ :=
  10 ^ 6 + Xsk + Y0 + 450 * Real.log (1 + Cq + cofkRConst Cb)

lemma cofkRSconst_pos {Cb : ℝ} (hCb0 : 0 ≤ Cb) : 0 < cofkRSconst Cb := by
  have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have h1 : (0 : ℝ) ≤ gradeAbsConstC (1 / Real.exp 1) Cb := gradeAbsConstC_nonneg hc1 hCb0
  have h2 : (0 : ℝ) ≤ farCStar2 := farCStar2_nonneg
  have h3 : (0 : ℝ) < cSq := cofk_cSq_pos
  rw [cofkRSconst]
  nlinarith

lemma cofkRConst_pos {Cb : ℝ} (hCb0 : 0 ≤ Cb) : 0 < cofkRConst Cb := by
  have h := cofkRSconst_pos hCb0
  rw [cofkRConst]; linarith

/-! ## §1 — ⟦THE BAND'S TRUE BOTTOM⟧ -/

/-- **⟦THE BAND'S LOG-BOTTOM⟧** (`cofkR_band_log_lower`).  Every block index of `ramI H P Q`
sits at or below `⌊H·log Q⌋₊`, so `B_v = X·e^{−v/H} ≥ X/Q`; with `log Q ≤ log X/loglog X`
(`log_le_of_le_Q83`) this is `log B_v ≥ (1 − 1/loglog X)·log X` — the `caseAS` page's own
descent gate, at the block. -/
theorem cofkR_band_log_lower {Xd P Q v : ℕ} {H : ℝ} (hH0 : 0 < H) (hQ1 : 1 ≤ Q)
    (hQhigh : ((Q : ℕ) : ℝ) ≤ Q83 ((Xd : ℕ) : ℝ))
    (hLe2 : Real.exp 2 ≤ Real.log ((Xd : ℕ) : ℝ))
    (hv : v ∈ ramI H P Q) :
    (1 - 1 / Real.log (Real.log ((Xd : ℕ) : ℝ))) * Real.log ((Xd : ℕ) : ℝ)
      ≤ Real.log (ramRbot H Xd v) := by
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLpos : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hLL2 : (2 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos 2) hLe2
    rwa [Real.log_exp] at h
  have hLL0 : (0 : ℝ) < Real.log (Real.log ((Xd : ℕ) : ℝ)) := by linarith
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := by
    rcases lt_or_ge (0 : ℝ) ((Xd : ℕ) : ℝ) with h | h
    · exact h
    · exfalso
      have hz : ((Xd : ℕ) : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
      rw [hz, Real.log_zero] at hLpos
      linarith
  have hQlog : Real.log ((Q : ℕ) : ℝ)
      ≤ Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ)) :=
    log_le_of_le_Q83 hQ1 hQhigh
  -- the block index sits under `H·log Q`
  rw [ramI, Finset.mem_Icc] at hv
  have hQ1R : (1 : ℝ) ≤ ((Q : ℕ) : ℝ) := by exact_mod_cast hQ1
  have hlogQ0 : (0 : ℝ) ≤ Real.log ((Q : ℕ) : ℝ) := Real.log_nonneg hQ1R
  have hvR : (v : ℝ) ≤ H * Real.log ((Q : ℕ) : ℝ) := by
    have h1 : ((⌊H * Real.log ((Q : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) ≤ H * Real.log ((Q : ℕ) : ℝ) :=
      Nat.floor_le (by positivity)
    have h2 : (v : ℝ) ≤ ((⌊H * Real.log ((Q : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hv.2
    linarith
  have hvH : (v : ℝ) / H
      ≤ Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ)) := by
    rw [div_le_iff₀ hH0]
    nlinarith [hvR, mul_le_mul_of_nonneg_left hQlog hH0.le]
  have hrw : Real.log (ramRbot H Xd v)
      = Real.log ((Xd : ℕ) : ℝ) + (-(v : ℝ) / H) := by
    rw [ramRbot, Real.log_mul (ne_of_gt hX0) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  rw [hrw]
  have hid : (1 - 1 / Real.log (Real.log ((Xd : ℕ) : ℝ))) * Real.log ((Xd : ℕ) : ℝ)
      = Real.log ((Xd : ℕ) : ℝ)
        - Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ)) := by
    field_simp
  rw [hid, neg_div]
  linarith

/-! ## §2 — ⟦THE TWO CONTOUR BOXES ARE THEOREMS⟧ -/

/-- `2·L^{3/5} ≤ L` at `L ≥ 32768` — `pin2_powers`' `L^{2/5} ≥ 64` multiplied by `L^{3/5}`.
This is `Tstar2_le_self`'s only side condition, and the reason the wide contour box is a
theorem rather than a carried gate. -/
theorem cofkR_two_rpow_three_fifths {L : ℝ} (hL : 32768 ≤ L) :
    2 * L ^ ((3 : ℝ) / 5) ≤ L := by
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨-, h25, -⟩ := pin2_powers hL
  have hmul : L ^ ((2 : ℝ) / 5) * L ^ ((3 : ℝ) / 5) = L := by
    rw [← Real.rpow_add hL0]; norm_num
  have h35 : (0 : ℝ) < L ^ ((3 : ℝ) / 5) := Real.rpow_pos_of_pos hL0 _
  nlinarith [hmul, h25, h35]

/-- `T*₂(X, log X) ≤ X` above the family gate — `FrameWitness.Tstar2_le_self` with its
threshold discharged. -/
theorem cofkR_Tstar2_le {X : ℝ} (hX : pin2Gate ≤ X) : Tstar2 X (Real.log X) ≤ X := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le pin2Gate_pos hX
  have hgate : Real.exp 32768 ≤ X := hX
  have hlog : (32768 : ℝ) ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 32768) hgate
    rwa [Real.log_exp] at h
  exact Tstar2_le_self hX (cofkR_two_rpow_three_fifths hlog)

/-- **⟦THE CONTOUR BOX, DISCHARGED⟧** (`cofkR_box_of_le`).  `|t| + T*₂(i, log i) ≤ 3X` for
every `i` between the family gate and `X`, and every `|t| ≤ X`: `Tstar2_mono` up to `X`, then
`cofkR_Tstar2_le`.  A full `X` of slack. -/
theorem cofkR_box_of_le {X i t : ℝ} (hpin : pin2Gate ≤ i) (hiX : i ≤ X) (ht : |t| ≤ X) :
    |t| + Tstar2 i (Real.log i) ≤ 3 * X := by
  have hXpin : pin2Gate ≤ X := le_trans hpin hiX
  have h1 : Tstar2 i (Real.log i) ≤ Tstar2 X (Real.log X) := Tstar2_mono hpin hiX
  have h2 : Tstar2 X (Real.log X) ≤ X := cofkR_Tstar2_le hXpin
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le pin2Gate_pos hXpin
  linarith

/-! ## §3 — ⟦THE CRUDE DESCENT⟧

`descent_tail_le` is stated at the SHARP gate `(1 − 1/loglog X)·log X ≤ log W`, which the
divided window `W = ⌊k₀/D⌋` misses by exactly `log D ≈ loglog X`.  The repair does not need
the sharp form: half a log suffices, and the charge is then a constant. -/

/-- **⟦THE DESCENT CHARGE AT HALF A LOG⟧** (`cofkR_descent_crude`).  Sharp Mertens-2 at both
endpoints, with `loglog X − loglog W ≤ log 2` from `log W ≥ (log X)/2`. -/
theorem cofkR_descent_crude {X W : ℝ} (hW2 : 2 ≤ W) (hWX : W ≤ X)
    (hlX : Real.exp 2 ≤ Real.log X)
    (hhalf : 1 / 2 * Real.log X ≤ Real.log W) :
    2 * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W)
      ≤ 2 * Real.log 2 + 24 / Real.log W + 24 / Real.log X := by
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have ha0 : (0 : ℝ) < Real.log X := by linarith
  have hX2 : (2 : ℝ) ≤ X := le_trans hW2 hWX
  have hb0 : (0 : ℝ) < Real.log W := Real.log_pos (by linarith)
  -- `loglog X − loglog W ≤ log 2`
  have hkey : Real.log (Real.log X) - Real.log (Real.log W) ≤ Real.log 2 := by
    have h1 : Real.log (1 / 2 * Real.log X) ≤ Real.log (Real.log W) :=
      Real.log_le_log (by linarith) hhalf
    have h2 : Real.log (1 / 2 * Real.log X) = Real.log (Real.log X) - Real.log 2 := by
      rw [show (1 : ℝ) / 2 * Real.log X = Real.log X / 2 by ring,
        Real.log_div (ne_of_gt ha0) (by norm_num)]
    linarith [h2 ▸ h1]
  have hMX := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hX2)
  have hMW := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hW2)
  have e2 : (24 : ℝ) / Real.log W = 2 * (12 / Real.log W) := by ring
  have e3 : (24 : ℝ) / Real.log X = 2 * (12 / Real.log X) := by ring
  rw [e2, e3]
  linarith [hMX.1, hMX.2, hMW.1, hMW.2]

/-- **⟦THE CASE-A FLOOR VALUE IS A FLOOR AT HALF A LOG⟧** (`cofkR_mfl_nonneg`).
`cofactorMfl_nonneg_of_descent` at the crude gate: the descent charge is `≤ 2·log 2 + 2 < 3.4`
against the grade `(1/32 − θ₂₉₃)·loglog X ≥ loglog X/36`. -/
theorem cofkR_mfl_nonneg {X W : ℝ} (hW2 : 2 ≤ W) (hWX : W ≤ X)
    (hlX : Real.exp 2 ≤ Real.log X)
    (hhalf : 1 / 2 * Real.log X ≤ Real.log W)
    (hLL : (1000 : ℝ) ≤ Real.log (Real.log X)) :
    0 ≤ cofactorMfl X theta293 W := by
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have ha0 : (0 : ℝ) < Real.log X := by linarith
  -- `loglog X ≥ 1000` puts `log X` above `e^{1000} ≥ 1001`
  have hLbig : (1000 : ℝ) ≤ Real.log X := by
    have h := Real.exp_le_exp.mpr hLL
    rw [Real.exp_log ha0] at h
    linarith [Real.add_one_le_exp (1000 : ℝ)]
  have hb0 : (0 : ℝ) < Real.log W := Real.log_pos (by linarith)
  have hW500 : (500 : ℝ) ≤ Real.log W := by linarith
  have hdesc := cofkR_descent_crude hW2 hWX hlX hhalf
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have h24W : (24 : ℝ) / Real.log W ≤ 1 := by
    rw [div_le_iff₀ hb0]; linarith
  have h24X : (24 : ℝ) / Real.log X ≤ 1 := by
    rw [div_le_iff₀ ha0]; linarith
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpos : (0 : ℝ) < 32 * (3 * Real.exp 1 + 1) := by nlinarith
  have hθ : theta293 ≤ 1 / 64 := by
    rw [theta293, div_le_iff₀ hpos]; nlinarith
  have hgrade : (1 / 64 : ℝ) * Real.log (Real.log X)
      ≤ (1 / 32 - theta293) * Real.log (Real.log X) := by
    have h1 : (1 / 64 : ℝ) ≤ 1 / 32 - theta293 := by linarith
    nlinarith
  rw [cofactorMfl]
  linarith

/-! ## §4 — ⟦THE DIVIDED WINDOW STILL SITS ABOVE `√X`⟧

The whole cost of the repair, in one inequality: at `D = ⌈log X⌉₊` the divided window bottom
`⌊k₀/D⌋` still obeys `log ⌊k₀/D⌋ ≥ (log X)/2`, so every landed pricing page — which asks only
for half a log — applies verbatim at the divided scale. -/

/-- The three exponential comparisons the divided window needs, at `L ≥ 1000`. -/
private lemma cofkR_exp_ladder {L : ℝ} (hL : (1000 : ℝ) ≤ L) :
    L + 2 ≤ Real.exp (L / 10)
      ∧ Real.exp (L / 2) * Real.exp (L / 10) = Real.exp (3 * L / 5)
      ∧ 4 * Real.exp (3 * L / 5) ≤ Real.exp (3 * L / 4) := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : 1 + L / 20 ≤ Real.exp (L / 20) := by
      linarith [Real.add_one_le_exp (L / 20)]
    have h2 : Real.exp (L / 20) * Real.exp (L / 20) = Real.exp (L / 10) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [h1, h2]
  · rw [← Real.exp_add]; congr 1; ring
  · have h4 : (4 : ℝ) ≤ Real.exp (3 * L / 20) := by
      have h := Real.add_one_le_exp (3 * L / 20)
      linarith
    have h2 : Real.exp (3 * L / 5) * Real.exp (3 * L / 20) = Real.exp (3 * L / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [h4, h2, Real.exp_pos (3 * L / 5)]

/-- **⟦THE DIVIDED WINDOW BOTTOM⟧** (`cofkR_window_lower`).  `⌊k₀/D⌋ ≥ √X` at the repaired
ladder: `k₀ ≥ B_v − 1 ≥ e^{3L/4} − 1`, `D ≤ L + 1 ≤ e^{L/10}`, and Nat division loses at most
one unit — `4·e^{3L/5} ≤ e^{3L/4}` closes it with three factors to spare. -/
theorem cofkR_window_lower {Xd v D : ℕ} {H L : ℝ}
    (hL : (1000 : ℝ) ≤ L) (hD1 : 1 ≤ D) (hD : ((D : ℕ) : ℝ) ≤ L + 1)
    (hB : Real.exp (3 * L / 4) ≤ ramRbot H Xd v) :
    Real.exp (L / 2) ≤ ((witKk H Xd v / D : ℕ) : ℝ) := by
  obtain ⟨hlin, hmul, hgap⟩ := cofkR_exp_ladder hL
  have hD0 : (0 : ℝ) < ((D : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((D : ℕ) : ℝ) := by exact_mod_cast hD1
    linarith
  have hDexp : ((D : ℕ) : ℝ) ≤ Real.exp (L / 10) := by linarith
  -- `k₀ ≥ B − 1`
  have h5B : (5 : ℝ) ≤ ramRbot H Xd v := by
    have h : (5 : ℝ) ≤ Real.exp (3 * L / 4) := by
      linarith [Real.add_one_le_exp (3 * L / 4)]
    linarith
  have hkk : ramRbot H Xd v - 1 ≤ ((witKk H Xd v : ℕ) : ℝ) := cofkL_ramRbot_le_kk h5B
  -- Nat division loses at most `D`
  have hdiv : ((witKk H Xd v : ℕ) : ℝ) - ((D : ℕ) : ℝ)
      ≤ ((D : ℕ) : ℝ) * ((witKk H Xd v / D : ℕ) : ℝ) := by
    have h := Nat.div_add_mod (witKk H Xd v) D
    have hmod : witKk H Xd v % D < D := Nat.mod_lt _ (by omega)
    have hsplit : ((witKk H Xd v : ℕ) : ℝ)
        = ((D : ℕ) : ℝ) * ((witKk H Xd v / D : ℕ) : ℝ) + ((witKk H Xd v % D : ℕ) : ℝ) := by
      exact_mod_cast h.symm
    have hmodR : ((witKk H Xd v % D : ℕ) : ℝ) < ((D : ℕ) : ℝ) := by exact_mod_cast hmod
    linarith
  -- `D·e^{L/2} + D ≤ 2·e^{3L/5} ≤ e^{3L/4} − 1 ≤ k₀ − D`
  have he12 : (0 : ℝ) < Real.exp (L / 2) := Real.exp_pos _
  have he35 : (1 : ℝ) ≤ Real.exp (3 * L / 5) := Real.one_le_exp (by linarith)
  have hstep1 : ((D : ℕ) : ℝ) * Real.exp (L / 2) ≤ Real.exp (3 * L / 5) := by
    nlinarith [hDexp, hmul, he12]
  have hstep2 : ((D : ℕ) : ℝ) ≤ Real.exp (3 * L / 5) := by
    have h1 : Real.exp (L / 10) ≤ Real.exp (3 * L / 5) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hfin : ((D : ℕ) : ℝ) * Real.exp (L / 2)
      ≤ ((D : ℕ) : ℝ) * ((witKk H Xd v / D : ℕ) : ℝ) := by
    have h1 : (2 : ℝ) * Real.exp (3 * L / 5) + 1 ≤ Real.exp (3 * L / 4) := by
      nlinarith [hgap, he35]
    linarith [hkk, hB, hdiv, hstep1, hstep2]
  exact le_of_mul_le_mul_left (by linarith [hfin]) hD0

/-! ## §5 — ⟦THE EXIT, RE-PRICED⟧ -/

/-- **⟦THE WIDE CASE-A CONSTANT, PRICED AT THE DIVIDED WINDOW⟧** (`cofkR_caseASwide_priced`).
Term by term: the grade summand is `cofactorMfl_grade_293`'s exact identity with the descent
factor capped at `2` by §3; the `1/(32e)` and `0.499` summands are `logW_rpow_le` at the two
landed exponent comparisons (`rho293_le_far`, `rho293_le_desmooth`). -/
theorem cofkR_caseASwide_priced {X W Xa Cb : ℝ} (hCb0 : 0 ≤ Cb)
    (hW2 : 2 ≤ W) (hWX : W ≤ X) (hlX : Real.exp 2 ≤ Real.log X)
    (hLL : (1000 : ℝ) ≤ Real.log (Real.log X))
    (hhalfW : 1 / 2 * Real.log X ≤ Real.log W)
    (hhalfA : 1 / 2 * Real.log X ≤ Real.log Xa) :
    caseASwide (1 / Real.exp 1) Cb (cofactorMfl X theta293 W) W Xa
      ≤ (3 * gradeAbsConstC (1 / Real.exp 1) Cb + 2 * farCStar2 + 8)
        * (Real.log X) ^ (-rho293) := by
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have ha0 : (0 : ℝ) < Real.log X := by linarith
  have hLbig : (1000 : ℝ) ≤ Real.log X := by
    have h := Real.exp_le_exp.mpr hLL
    rw [Real.exp_log ha0] at h
    linarith [Real.add_one_le_exp (1000 : ℝ)]
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hb0 : (0 : ℝ) < Real.log W := Real.log_pos (by linarith)
  have hXe : Real.exp 1 ≤ X := by
    have h1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have hX0 : (0 : ℝ) < X := by linarith [hW2, hWX]
    have h := Real.exp_le_exp.mpr hL1
    rw [Real.exp_log hX0] at h
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow0 : (0 : ℝ) ≤ (Real.log X) ^ (-rho293) := Real.rpow_nonneg ha0.le _
  -- ⟦THE GRADE SUMMAND⟧
  have hgrade := cofactorMfl_grade_293 (X := X) (W := W) hXe
  have hdesc := cofkR_descent_crude hW2 hWX hlX hhalfW
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hW500 : (500 : ℝ) ≤ Real.log W := by linarith
  have h24W : (24 : ℝ) / Real.log W ≤ 1 / 20 := by
    rw [div_le_iff₀ hb0]; linarith
  have h24X : (24 : ℝ) / Real.log X ≤ 1 / 40 := by
    rw [div_le_iff₀ ha0]; linarith
  have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hfac : Real.exp ((2 / Real.exp 1)
      * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W)) ≤ 2 := by
    have hsmall : (2 / Real.exp 1)
        * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W) ≤ Real.log 2 := by
      have hd : 2 * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W) ≤ 3 / 2 := by
        linarith [Real.log_two_lt_d9]
      have hprod : (1.87 : ℝ) ≤ Real.log 2 * Real.exp 1 := by
        nlinarith [Real.log_two_gt_d9, he1]
      have hid : (2 / Real.exp 1) * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W)
          = (2 * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W)) / Real.exp 1 := by
        ring
      rw [hid, div_le_iff₀ (by linarith)]
      linarith
    have h := Real.exp_le_exp.mpr hsmall
    rwa [Real.exp_log (by norm_num)] at h
  have hC10 : (0 : ℝ) ≤ gradeAbsConstC (1 / Real.exp 1) Cb := by
    refine gradeAbsConstC_nonneg ?_ hCb0
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have hA : gradeAbsConstC (1 / Real.exp 1) Cb
      * Real.exp (-(1 / Real.exp 1) * cofactorMfl X theta293 W)
      ≤ 3 * gradeAbsConstC (1 / Real.exp 1) Cb * (Real.log X) ^ (-rho293) := by
    rw [hgrade]
    have h1 : Real.exp ((2 / Real.exp 1)
          * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W)) * (Real.log X) ^ (-rho293)
        ≤ 2 * (Real.log X) ^ (-rho293) := mul_le_mul_of_nonneg_right hfac hpow0
    have h2 := mul_le_mul_of_nonneg_left h1 hC10
    have h3 : (0 : ℝ) ≤ gradeAbsConstC (1 / Real.exp 1) Cb * (Real.log X) ^ (-rho293) :=
      mul_nonneg hC10 hpow0
    nlinarith [h2, h3]
  -- ⟦THE TWO SHIFTED SUMMANDS⟧
  have hfar1 : (1 : ℝ) / (32 * Real.exp 1) ≤ 1 := by
    rw [div_le_one (by nlinarith)]; nlinarith
  have hB : (Real.log W) ^ (-(1 / (32 * Real.exp 1)))
      ≤ 2 * (Real.log X) ^ (-rho293) :=
    logW_rpow_le hL1 hhalfW rho293_le_far hfar1
  have hexp3 : (-(1 : ℝ) / 2 + 1 / 1000) = -(499 / 1000 : ℝ) := by norm_num
  have hC : (Real.log Xa) ^ (-(1 : ℝ) / 2 + 1 / 1000) ≤ 2 * (Real.log X) ^ (-rho293) := by
    rw [hexp3]
    exact logW_rpow_le hL1 hhalfA rho293_le_desmooth (by norm_num)
  rw [caseASwide]
  nlinarith [hA, hB, hC, farCStar2_nonneg, hpow0]

/-- **⟦THE FAR ARM, PRICED⟧** (`cofkR_farSup_priced`).  `2√2/seamRad X ≤ 3·(log X)^{−ρ₂₉₃}`
(`farMain_priced` at the radius pin) plus the GS-7.1 certificate `farErr34 ≤ (log Y)^{−ρ₂₉₃}`
transported to the global scale by `logW_rpow_le`. -/
theorem cofkR_farSup_priced {X W Y : ℝ}
    (hL1 : 1 ≤ Real.log X)
    (hclose : farErr34 W Y (Tstar2 Y (Real.log Y)) ≤ (Real.log Y) ^ (-rho293))
    (hhalfY : 1 / 2 * Real.log X ≤ Real.log Y) :
    farSupS34 W Y (Tstar2 Y (Real.log Y)) (seamRad X) ≤ 5 * (Real.log X) ^ (-rho293) := by
  have hmain := farMain_priced (X := X) (Rrad := seamRad X) hL1 (le_refl _)
  have hrho1 : rho293 ≤ 1 := by
    have := rho293_le_seam
    linarith
  have htrans : (Real.log Y) ^ (-rho293) ≤ 2 * (Real.log X) ^ (-rho293) :=
    logW_rpow_le hL1 hhalfY (le_refl _) hrho1
  rw [farSupS34]
  linarith

/-! ## §6 — ⟦THE CO-FACTOR SUPPLY AT THE REPAIRED LADDER⟧

`CofactorBulk` §4's instantiation, at `D(j) := ⌈log X⌉₊` and with `C_R` taken from the
predicate's OWN existential rather than pinned at `gradeCR2 Cb`.  The seventeen conjuncts are
discharged, not carried: one scale gate (`cofkRThr`, absorbed by the terminal's design
constant) and one named cushion (`K_vt`, Siegel-genre) are all that is left. -/

set_option maxHeartbeats 24000000 in
-- the ~35-binder instantiation of `m4_supplier_complete` and the seventeen discharged
-- conjuncts elaborate in ONE context; no tactic search happens at the top level
/-- **⟦THE CO-FACTOR DEBT, DISCHARGED AT THE REPAIRED LADDER⟧**
(`cofkR_cofactorSupply_L_gk`).  ⟦RULING 9⟧'s co-factor supply
`S16CofactorSupply_L_gk K Cq R M` holds at every socket of every regime whose scale clears
`cofkRThr` — modulo the ONE `K_vt` cushion.

⟦WHAT CHANGED FROM `cofkL_cofactorSupply_L_gk_of_bulk`⟧ the dilation ladder is
`D ≡ ⌈log X⌉₊` instead of `D ≡ 1`, and the exit constant is the freed existential
`C_R := 4·cofkRConst Cb` instead of `gradeCR2 Cb`.  Those two changes turn the refuted chain
`24·cSq·(log X)^{ρ₂₉₃} ≤ gradeCR2 Cb` into the satisfiable gate
`1728·C_q·(4·Rconst)² ≤ (log X)^{2θ₂₉₃}` — and the seventeen carried conjuncts into theorems.

⟦THE ONE NAMED HYPOTHESIS⟧ `32·K_vt(K, Q_m) + 32·(2 log M + log 4 + 50) ≤ (log H₊)/4`.
`K_vt` is `RegisterSupply.cofkL_capFreeFloor_at_socket`'s `_vt` floor constant; its third leg
bottoms out at `SiegelArm`'s EVT minimum of `‖L(s,χ)‖` on a box uniform in `q` — the
Siegel-zero obstruction itself, traced by `REGISTER-INHABIT` — so it is carried by name, with
the trace behind it, and NOT discharged. -/
theorem cofkR_cofactorSupply_L_gk :
    ∃ (Xsk Y0 : ℝ) (Kvt : ℕ → ℕ → ℝ) (Cb : ℝ),
      0 < Xsk ∧ pin2Gate ≤ Y0 ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧ 0 ≤ Cb ∧
      ∀ (K : ℕ) (Cq : ℝ) (R : ChowlaRegime) (M : ℕ), 1 ≤ M → 0 < Cq →
        (1 : ℝ) / 500 ≤ (R.eps : ℝ) →
        (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        loglogFloor50 ≤ R.Hlo →
        cofkRThr Cq Cb Xsk Y0 ≤ Real.log (R.Hlo : ℝ) →
        32 * Kvt K ⌈arcDen 12 R.Hhi⌉₊
            + 32 * (2 * Real.log (M : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
        S16CofactorSupply_L_gk K Cq R M := by
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  obtain ⟨Y0, hY0pin, hfarclose⟩ := farErr34_local_closes
  choose Kvt hKvt0 hKvt using cofkL_capFreeFloor_at_socket
  obtain ⟨Cb, hCb0, hCbound⟩ := exists_shortIntervalDatum
  refine ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, ?_⟩
  intro K Cq R M hM hCq hε hlo hfl hgate hcush H Lw q j A s hb T hTlo hThi
  have hq0 : 0 < q := hb.2.2.2.1
  haveI : NeZero q := ⟨by omega⟩
  have hbb : SocketBase R M H Lw q j A s := socketBase_of_socketBaseL hM hb
  obtain ⟨hH4, hHhi14⟩ := cofkL_socket_floors hb hlo
  have hqQm : q ≤ ⌈arcDen 12 R.Hhi⌉₊ := cofkL_q_le_arcCap hb hH4
  -- ⟦THE SOCKET'S OWN SCALE FACTS⟧
  have h2j0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hAs1 : 0 < A + s := by have := hb.2.2.2.2.2.2.2.1; omega
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs1
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hAsR h2j0) hTlo
  have hTflo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ 2 * T := by linarith
  have hmu2000 : (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := s13CapGrid_mu_2000 hfl hbb
  have hLam : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    s13CapGrid_Lambda_lo hfl hbb
  have hmuF : Real.log (R.Hhi : ℝ) - 14 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    cofkL_mu_floor hb hε hHhi14 hH4
  obtain ⟨-, -, hTpos, hlogT⟩ := capfloor_core hfl hbb (Nat.le_add_right A s) hTflo
  have hPQ : s13BandP (A + s) ≤ s13BandQ (A + s) := s13CapGrid_P_le_Q hmu2000 hLam
  have hQpos : 0 < s13BandQ (A + s) := s13CapGrid_Q_pos hmu2000
  have hfloorχ : ∀ χ : DirichletCharacter ℂ q, ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M)) (((A + s : ℕ)) : ℝ) :=
    fun χ => hKvt K ⌈arcDen 12 R.Hhi⌉₊ χ hb hM hqQm hε hlo hcush
  -- ⟦THE BLOCK SCALE, NAMED ONCE⟧
  obtain ⟨Xd, hXd⟩ : ∃ n : ℕ, A + s = n := ⟨A + s, rfl⟩
  rw [hXd] at hmu2000 hLam hmuF hPQ hQpos hfloorχ hTflo hThi hlogT hAsR ⊢
  -- ⟦THE SCALE ARITHMETIC⟧
  have hLg0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hLgexp : Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ))) = Real.log ((Xd : ℕ) : ℝ) :=
    Real.exp_log hLg0
  have h21 : (10 : ℝ) ^ (21 : ℕ) = 1000000000000000000000 := by norm_num
  rw [h21] at hLam
  have hLg166 : Real.exp 166 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h := Real.exp_le_exp.mpr (show (166 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) by
      linarith)
    rwa [hLgexp] at h
  have hexp165 : (2 : ℝ) ≤ Real.exp 165 := by linarith [Real.add_one_le_exp (165 : ℝ)]
  have hexp166 : Real.exp 166 = Real.exp 1 * Real.exp 165 := by rw [← Real.exp_add]; norm_num
  have he27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hball : 2 * Real.exp 165 + 2 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    nlinarith [hLg166, hexp166, hexp165, he27]
  have hLgbig : (10 : ℝ) ^ 6 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h : (10 : ℝ) ^ 6 ≤ Real.exp 166 := by
      have h1 : (1 : ℝ) + 41.5 ≤ Real.exp 41.5 := by
        linarith [Real.add_one_le_exp (41.5 : ℝ)]
      have h2 : Real.exp 41.5 * Real.exp 41.5 = Real.exp 83 := by
        rw [← Real.exp_add]; norm_num
      have h3 : Real.exp 83 * Real.exp 83 = Real.exp 166 := by rw [← Real.exp_add]; norm_num
      have h4 : (1806 : ℝ) ≤ Real.exp 83 := by nlinarith [h1, h2]
      nlinarith [h3, h4]
    linarith
  -- ⟦THE THRESHOLD, READ AT THE SOCKET⟧
  have hHloHhi : Real.log (R.Hlo : ℝ) ≤ Real.log (R.Hhi : ℝ) := by
    have h1 : R.Hlo ≤ H := hb.1
    have h2 : H ≤ R.Hhi := hb.2.1
    have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
    have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
    have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
    exact Real.log_le_log (by linarith) (by linarith)
  have hthrLL : cofkRThr Cq Cb Xsk Y0 - 14
      ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by linarith
  have hZ1 : (1 : ℝ) ≤ 1 + Cq + cofkRConst Cb := by
    linarith [cofkRConst_pos hCb0]
  have hlogZ0 : (0 : ℝ) ≤ Real.log (1 + Cq + cofkRConst Cb) := Real.log_nonneg hZ1
  have hY00 : (0 : ℝ) < Y0 := lt_of_lt_of_le pin2Gate_pos hY0pin
  have hthrpieces : Xsk ≤ cofkRThr Cq Cb Xsk Y0 ∧ Y0 ≤ cofkRThr Cq Cb Xsk Y0 := by
    rw [cofkRThr]
    constructor <;> nlinarith [hlogZ0, hY00, hXsk0]
  -- `log X ≥ (loglog X)²/4`, the one quadratic the constant-absorption uses
  have hquad : Real.log (Real.log ((Xd : ℕ) : ℝ)) ^ 2 / 4 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h1 : 1 + Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2
        ≤ Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2) := by
      linarith [Real.add_one_le_exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2)]
    have h2 : Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2)
        * Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2)
        = Real.log ((Xd : ℕ) : ℝ) := by
      rw [← Real.exp_add, show Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2
        + Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2
        = Real.log (Real.log ((Xd : ℕ) : ℝ)) by ring, hLgexp]
    nlinarith [h1, h2, hLam]
  have habs : ∀ z : ℝ, 0 < z → z ≤ cofkRThr Cq Cb Xsk Y0 →
      Real.log z ≤ Real.log ((Xd : ℕ) : ℝ) / 4 := by
    intro z hz0 hzthr
    have hlz : Real.log z ≤ z := by
      linarith [Real.log_le_sub_one_of_pos hz0]
    have hthr14 : cofkRThr Cq Cb Xsk Y0 ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) + 14 := by
      linarith
    nlinarith [hquad, hLam, hlz, hzthr, hthr14]
  have hXskgate : Xsk ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) := by
    have h := habs Xsk hXsk0 hthrpieces.1
    have h2 := Real.exp_le_exp.mpr h
    rwa [Real.exp_log hXsk0] at h2
  have hY0gate : Y0 ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) := by
    have h := habs Y0 hY00 hthrpieces.2
    have h2 := Real.exp_le_exp.mpr h
    rwa [Real.exp_log hY00] at h2
  -- ⟦THE GRADING GATE⟧
  have hgradegate : 1728 * Cq * (4 * cofkRConst Cb) ^ 2
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (2 * theta293) := by
    have hθ300 : (1 : ℝ) / 300 ≤ theta293 := by
      have hpos : (0 : ℝ) < 32 * (3 * Real.exp 1 + 1) := by nlinarith
      rw [theta293, le_div_iff₀ hpos]
      nlinarith [Real.exp_one_lt_d9]
    have hpow : (Real.log ((Xd : ℕ) : ℝ)) ^ (2 * theta293)
        = Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) * (2 * theta293)) := by
      rw [Real.rpow_def_of_pos hLg0]
    have hstep : (6666 : ℝ) + 3 * Real.log (1 + Cq + cofkRConst Cb)
        ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) * (2 * theta293) := by
      have hLL0 : (0 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by linarith
      have h1 : Real.log (Real.log ((Xd : ℕ) : ℝ)) / 150
          ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) * (2 * theta293) := by
        nlinarith [hθ300, hLL0]
      have h2 : (10 : ℝ) ^ 6 + 450 * Real.log (1 + Cq + cofkRConst Cb) - 14
          ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by
        have := hthrLL
        rw [cofkRThr] at this
        linarith
      linarith
    have hZ3 : Real.exp ((6666 : ℝ) + 3 * Real.log (1 + Cq + cofkRConst Cb))
        = Real.exp 6666 * (1 + Cq + cofkRConst Cb) ^ 3 := by
      rw [Real.exp_add]
      congr 1
      rw [show (3 : ℝ) * Real.log (1 + Cq + cofkRConst Cb)
        = Real.log ((1 + Cq + cofkRConst Cb) ^ 3) by
          rw [Real.log_pow]; push_cast; ring]
      exact Real.exp_log (pow_pos (by linarith) 3)
    have hbig : Real.exp 6666 * (1 + Cq + cofkRConst Cb) ^ 3
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (2 * theta293) := by
      rw [hpow, ← hZ3]
      exact Real.exp_le_exp.mpr hstep
    have he6666 : (27648 : ℝ) ≤ Real.exp 6666 := by
      have h1 : (1 : ℝ) + 3333 ≤ Real.exp 3333 := by
        linarith [Real.add_one_le_exp (3333 : ℝ)]
      have h2 : Real.exp 3333 * Real.exp 3333 = Real.exp 6666 := by
        rw [← Real.exp_add]; norm_num
      nlinarith
    have hRc0 : (0 : ℝ) < cofkRConst Cb := cofkRConst_pos hCb0
    have hCqZ : Cq ≤ 1 + Cq + cofkRConst Cb := by linarith
    have hRZ : cofkRConst Cb ^ 2 ≤ (1 + Cq + cofkRConst Cb) ^ 2 := by nlinarith
    have hcube : Cq * cofkRConst Cb ^ 2 ≤ (1 + Cq + cofkRConst Cb) ^ 3 := by
      nlinarith [hCqZ, hRZ, hCq.le, hRc0, hZ1]
    have hid : 1728 * Cq * (4 * cofkRConst Cb) ^ 2 = 27648 * (Cq * cofkRConst Cb ^ 2) := by
      ring
    rw [hid]
    have hZ0 : (0 : ℝ) ≤ (1 + Cq + cofkRConst Cb) ^ 3 := pow_nonneg (by linarith) 3
    calc 27648 * (Cq * cofkRConst Cb ^ 2)
        ≤ 27648 * (1 + Cq + cofkRConst Cb) ^ 3 := by linarith
      _ ≤ Real.exp 6666 * (1 + Cq + cofkRConst Cb) ^ 3 := by nlinarith [he6666, hZ0]
      _ ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (2 * theta293) := hbig
  -- ⟦THE BAND⟧
  have hθ0 : (0 : ℝ) < theta293 := theta293_pos
  have hθ32 : theta293 ≤ 1 / 32 := theta293_lt_one_div_32.le
  have hLX : Real.exp 1 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have hLe2 : Real.exp 2 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have hH1 : (1 : ℝ) ≤ H83 ((Xd : ℕ) : ℝ) theta293 := by
    rw [H83]; exact Real.one_le_rpow (by linarith) hθ0.le
  have hH0 : (0 : ℝ) < H83 ((Xd : ℕ) : ℝ) theta293 := by linarith
  have hPlow : P83 ((Xd : ℕ) : ℝ) theta293 ≤ ((s13BandP Xd : ℕ) : ℝ) := s13CapGrid_P_low Xd
  have hQhigh : ((s13BandQ Xd : ℕ) : ℝ) ≤ Q83 ((Xd : ℕ) : ℝ) := s13CapGrid_Q_high Xd
  have hQ1 : 1 ≤ s13BandQ Xd := hQpos
  have hP83pos : (0 : ℝ) < P83 ((Xd : ℕ) : ℝ) theta293 := by rw [P83]; exact Real.exp_pos _
  have hPexp : (2 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - theta293) := by
    have h1 : (Real.exp 1) ^ (1 - theta293)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - theta293) :=
      Real.rpow_le_rpow (Real.exp_pos 1).le hLX (by linarith)
    have h2 : (Real.exp 1) ^ (31 / 32 : ℝ) ≤ (Real.exp 1) ^ (1 - theta293) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : (Real.exp 1) ^ (31 / 32 : ℝ) = Real.exp (31 / 32) := Real.exp_one_rpow _
    have h4 := cofk_two_le_exp_31_32
    rw [h3] at h2
    linarith
  have hP83log : Real.log (P83 ((Xd : ℕ) : ℝ) theta293)
      = (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - theta293) := by rw [P83, Real.log_exp]
  have hP83ge : (3 : ℝ) ≤ P83 ((Xd : ℕ) : ℝ) theta293 := by
    rw [P83]
    have h1 : Real.exp 2 ≤ Real.exp ((Real.log ((Xd : ℕ) : ℝ)) ^ (1 - theta293)) :=
      Real.exp_le_exp.mpr hPexp
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    linarith
  have hP3R : (3 : ℝ) ≤ ((s13BandP Xd : ℕ) : ℝ) := by linarith
  have hP3 : 3 ≤ s13BandP Xd := by exact_mod_cast hP3R
  have hP1 : 1 ≤ s13BandP Xd := by omega
  have hlogP2 : (2 : ℝ) ≤ Real.log ((s13BandP Xd : ℕ) : ℝ) := by
    have h := Real.log_le_log hP83pos hPlow
    rw [hP83log] at h
    linarith
  have hQlog : Real.log ((s13BandQ Xd : ℕ) : ℝ)
      ≤ Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ)) :=
    log_le_of_le_Q83 hQ1 hQhigh
  have hQL : Real.log ((s13BandQ Xd : ℕ) : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have hdiv : Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ))
        ≤ Real.log ((Xd : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hRrad0 : (0 : ℝ) < seamRad ((Xd : ℕ) : ℝ) := by
    rw [seamRad]; exact Real.rpow_pos_of_pos hLg0 _
  -- ⟦CONJUNCTS 2 AND 3: THE `T`-WINDOW IS THE SOCKET'S OWN ARITHMETIC⟧
  have h2T0 : (0 : ℝ) < 2 * T := by linarith
  have hQT : ((s13BandQ Xd : ℕ) : ℝ) ≤ 2 * T := by
    have hQ0R : (0 : ℝ) < ((s13BandQ Xd : ℕ) : ℝ) := by exact_mod_cast hQpos
    have hstep : Real.log ((s13BandQ Xd : ℕ) : ℝ) ≤ Real.log (2 * T) := by
      have hdiv : Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ))
          ≤ Real.log ((Xd : ℕ) : ℝ) / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
        nlinarith
      linarith
    have h := Real.exp_le_exp.mpr hstep
    rwa [Real.exp_log hQ0R, Real.exp_log h2T0] at h
  have h30g : 30 * (Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ)))
      ≤ Real.log (2 * T) := by
    have hdiv : Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ))
        ≤ Real.log ((Xd : ℕ) : ℝ) / 60 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 60)]
      nlinarith
    linarith
  -- ⟦THE BLOCKS⟧
  have hBpos : ∀ v : ℕ, (0 : ℝ) < ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v
    rw [ramRbot]
    exact mul_pos hAsR (Real.exp_pos _)
  have hB34 : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4)
        ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    have hlow := cofkR_band_log_lower hH0 hQ1 hQhigh hLe2 hv
    have hid : (1 - 1 / Real.log (Real.log ((Xd : ℕ) : ℝ))) * Real.log ((Xd : ℕ) : ℝ)
        = Real.log ((Xd : ℕ) : ℝ)
          - (1 / Real.log (Real.log ((Xd : ℕ) : ℝ))) * Real.log ((Xd : ℕ) : ℝ) := by ring
    rw [hid] at hlow
    have hinv : (1 : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 4)]
      linarith
    have hstep : 3 * Real.log ((Xd : ℕ) : ℝ) / 4
        ≤ Real.log (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v) := by
      nlinarith [hlow, hinv, hLg0]
    have h := Real.exp_le_exp.mpr hstep
    rwa [Real.exp_log (hBpos v)] at h
  -- the three exponential comparisons every block fact below runs on
  have hehalf : (1 : ℝ) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) :=
    Real.one_le_exp (by linarith)
  have hequart : (1 : ℝ) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) :=
    Real.one_le_exp (by linarith)
  have hesplit : Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4)
      * Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)
      = Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have he2half : (2 : ℝ) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := by
    linarith [Real.add_one_le_exp (Real.log ((Xd : ℕ) : ℝ) / 2)]
  have he2quart : (2 : ℝ) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) := by
    linarith [Real.add_one_le_exp (Real.log ((Xd : ℕ) : ℝ) / 4)]
  have hquarthalf : Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4)
      ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := Real.exp_le_exp.mpr (by linarith)
  have hgap34 : Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) + 1
      ≤ Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
    nlinarith [hesplit, hehalf, he2quart]
  have hgapq : Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) + 1
      ≤ Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
    nlinarith [hesplit, hehalf, he2quart, hquarthalf]
  have hpinhalf : pin2Gate ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := by
    rw [pin2Gate]
    exact Real.exp_le_exp.mpr (by linarith)
  -- the landed band facts, at the repaired scale
  have hBX : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      2 * ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v ≤ ((Xd : ℕ) : ℝ) :=
    fun v hv => cofkL_two_ramRbot_le hH1 hlogP2 hv
  have hkth : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ballQuarterThreshold + 1 ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
    fun v hv => cofk_ballQuarter_at_band hH0 hQ1 hQhigh hball hv
  have hW5 : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      (5 : ℝ) ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
    fun v hv => cofkL_five_le_ramRbot (hkth v hv)
  have hC16 : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      18 + Real.log (Real.log ((Xd : ℕ) : ℝ))
          - Real.log (Real.log (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)) :=
    fun v hv => cofk_descent_at_band hH0 hQ1 hQhigh (by linarith) (by linarith) hv
  have hRradW : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      seamRad ((Xd : ℕ) : ℝ) ≤ Real.sqrt 2 * ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
    fun v hv => cofk_seamRad_at_band hH0 hQ1 hQhigh (by linarith) hv
  have hXskj : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Xsk ≤ Real.sqrt (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v) :=
    fun v hv => cofk_wideThreshold_at_band hH0 hQ1 hQhigh hLe2 hXskgate hv
  -- ⟦THE REPAIRED LADDER `D = ⌈log X⌉₊`⟧
  have hDge : Real.log ((Xd : ℕ) : ℝ) ≤ ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hDle : ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hLg0.le)
  have hDone : 1 ≤ ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ := by
    have h : (1 : ℝ) ≤ ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by linarith
    exact_mod_cast h
  have hWlow : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
            / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) :=
    fun v hv => cofkR_window_lower (by linarith) hDone hDle (hB34 v hv)
  have hWpos : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      (0 : ℝ) < ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by
    intro v hv; linarith [hWlow v hv, hehalf]
  have hlogW : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      1 / 2 * Real.log ((Xd : ℕ) : ℝ)
        ≤ Real.log (((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
            / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)) := by
    intro v hv
    have h := Real.log_le_log (Real.exp_pos (Real.log ((Xd : ℕ) : ℝ) / 2)) (hWlow v hv)
    rw [Real.log_exp] at h
    linarith only [h]
  have hWXle : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ≤ ((Xd : ℕ) : ℝ) := by
    intro v hv
    have h1 : (witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) ≤ witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
      Nat.div_le_self _ _
    have h1R : ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 := (witKk_cut (H := H83 ((Xd : ℕ) : ℝ) theta293) (Xd := Xd) (j := v)
      (by linarith [hW5 v hv])).1
    linarith [hBX v hv, hBpos v]
  -- ⟦THE WINDOW TOP⟧
  have hMtlow : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)
        ≤ ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
    intro v hv
    have h := (witMt_window (H := H83 ((Xd : ℕ) : ℝ) theta293) (Xd := Xd) (j := v)
      (by linarith [hW5 v hv])).1
    linarith [hB34 v hv, hgap34]
  have hMtX : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) ≤ 2 * ramRbot
        (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
    fun v hv => cofkL_Mt_le_two_ramRbot (hW5 v hv)
  have hlogMt : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      1 / 2 * Real.log ((Xd : ℕ) : ℝ)
        ≤ Real.log (((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)) := by
    intro v hv
    have h := Real.log_le_log (Real.exp_pos (Real.log ((Xd : ℕ) : ℝ) / 2)) (hMtlow v hv)
    rw [Real.log_exp] at h
    linarith only [h]
  have hlogB : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      1 / 2 * Real.log ((Xd : ℕ) : ℝ)
        ≤ Real.log (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v) := by
    intro v hv
    have h := Real.log_le_log (Real.exp_pos (3 * Real.log ((Xd : ℕ) : ℝ) / 4)) (hB34 v hv)
    rw [Real.log_exp] at h
    linarith only [h, hLg0]
  -- ⟦THE EXIT CHARGES, AT THE REPAIRED LADDER⟧
  have hpow0 : (0 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := Real.rpow_nonneg hLg0.le _
  have hcSq0 := cofk_cSq_pos
  have hS0 : (0 : ℝ) ≤ cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) :=
    mul_nonneg (cofkRSconst_pos hCb0).le hpow0
  have hSbd : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      cSq * caseASwide (1 / Real.exp 1) Cb
          (cofactorMfl ((Xd : ℕ) : ℝ) theta293
            ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
              / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ))
          ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
            / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
          (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v)
        + cSq * ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
      ≤ cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
    intro v hv
    have hW2 : (2 : ℝ) ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := le_trans he2half (hWlow v hv)
    have hcase := cofkR_caseASwide_priced hCb0 hW2 (hWXle v hv) hLe2 (by linarith)
      (hlogW v hv) (hlogB v hv)
    have hD4 : ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
      have h1 : ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hLg0 hDge (by norm_num)
      have h2 : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 4 : ℝ))
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith only [hLgbig])
          (by linarith only [rho293_le_seam])
      linarith only [h1, h2]
    have h1 := mul_le_mul_of_nonneg_left hcase hcSq0.le
    have h2 := mul_le_mul_of_nonneg_left hD4 hcSq0.le
    calc cSq * caseASwide (1 / Real.exp 1) Cb
            (cofactorMfl ((Xd : ℕ) : ℝ) theta293
              ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
                / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ))
            ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
              / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
            (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v)
          + cSq * ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
        ≤ cSq * ((3 * gradeAbsConstC (1 / Real.exp 1) Cb + 2 * farCStar2 + 8)
              * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
            + cSq * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by linarith only [h1, h2]
      _ = cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
          rw [cofkRSconst]; ring
  have hMfl0 : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      (0 : ℝ) ≤ cofactorMfl ((Xd : ℕ) : ℝ) theta293
        ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
          / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by
    intro v hv
    exact cofkR_mfl_nonneg (le_trans he2half (hWlow v hv)) (hWXle v hv) hLe2
      (hlogW v hv) (by linarith)
  -- ⟦THE FAR ARM AT EVERY BLOCK⟧
  have hfarb : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      farSupS34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad ((Xd : ℕ) : ℝ))
        ≤ 5 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
    intro v hv
    have hY0Mt : Y0 ≤ ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) :=
      le_trans hY0gate (le_trans hquarthalf (hMtlow v hv))
    have hB2 : (2 : ℝ) ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
      linarith [hW5 v hv]
    have hMt0 : (0 : ℝ) < ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith [hMtlow v hv, hehalf]
    have hlogMtle := Real.log_le_log hMt0 (hMtX v hv)
    have hkkhalf : ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v / 2
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith [cofkL_ramRbot_le_kk (hW5 v hv)]
    have hlogkk := Real.log_le_log (by linarith : (0 : ℝ)
      < ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v / 2) hkkhalf
    rw [Real.log_mul (by norm_num) (ne_of_gt (hBpos v))] at hlogMtle
    rw [Real.log_div (ne_of_gt (hBpos v)) (by norm_num)] at hlogkk
    have hlogBbig : 3 * Real.log 2 ≤ Real.log (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v) := by
      linarith only [hlogB v hv, Real.log_two_lt_d9, hLgbig]
    have hlogMt2kk : Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        ≤ 2 * Real.log ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith only [hlogMtle, hlogkk, hlogBbig]
    exact cofkR_farSup_priced (by linarith only [hLgbig]) (hfarclose _ _ hY0Mt hlogMt2kk)
      (hlogMt v hv)
  -- ⟦THE `R̄₀` CEILING⟧
  have hRbdU : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      cofactorRbdGen (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
          ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad ((Xd : ℕ) : ℝ))
        ≤ cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
    intro v hv
    rw [cofactorRbdGen, cofkRConst]
    have hmax : max (2 * (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)))
        (farSupS34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad ((Xd : ℕ) : ℝ)))
        ≤ (2 * cofkRSconst Cb + 5) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
      have hSP : (0 : ℝ) ≤ cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := hS0
      exact max_le (by linarith only [hpow0])
        (le_trans (hfarb v hv) (by linarith only [hSP]))
    linarith only [hmax]
  -- ⟦THE ENDPOINT CHARGE⟧
  have hLgleB : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.log ((Xd : ℕ) : ℝ) ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    have h1 : 1 + 3 * Real.log ((Xd : ℕ) : ℝ) / 8
        ≤ Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8) := by
      linarith [Real.add_one_le_exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)]
    have h2 : Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)
        * Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)
        = Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [hB34 v hv, h1, h2, hLg0]
  have hsr : seamRad ((Xd : ℕ) : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
    rw [seamRad]
    have h1 : (Real.log ((Xd : ℕ) : ℝ)) ^ ((1 : ℝ) / 46)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rwa [Real.rpow_one] at h1
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
    rwa [Real.sqrt_one] at h
  have hendGen : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      2 / ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        ≤ cofactorRbdGen (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
            ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
              (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
            (seamRad ((Xd : ℕ) : ℝ)) / 3 := by
    intro v hv
    have hMt0 : (0 : ℝ) < ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith [hMtlow v hv, hehalf]
    have hkk0 : (0 : ℝ) < Real.log ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      have h2 : (2 : ℝ) ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
        linarith only [cofkL_ramRbot_le_kk (hW5 v hv), hW5 v hv]
      exact Real.log_pos (by linarith only [h2])
    have hfar0 : (0 : ℝ) ≤ farErr34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ))) :=
      farErr34_nonneg hkk0 (Real.log_nonneg (by linarith [hMtlow v hv, he2half]))
        (Tstar2_pos hMt0).le
    have hchain : 2 / ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        ≤ farSupS34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad ((Xd : ℕ) : ℝ)) := by
      rw [farSupS34]
      have h1 : (2 : ℝ) / ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
          ≤ 2 / Real.log ((Xd : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hLg0 (hLgleB v hv)
      have h2 : (2 : ℝ) / Real.log ((Xd : ℕ) : ℝ) ≤ 2 / seamRad ((Xd : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hRrad0 hsr
      have hinv : (0 : ℝ) < (seamRad ((Xd : ℕ) : ℝ))⁻¹ := inv_pos.mpr hRrad0
      have h3 : (2 : ℝ) / seamRad ((Xd : ℕ) : ℝ)
          ≤ 2 * Real.sqrt 2 / seamRad ((Xd : ℕ) : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        nlinarith [hs2, hinv]
      linarith
    rw [cofactorRbdGen]
    have hfin := le_trans hchain
      (le_max_right (2 * (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)))
      (farSupS34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
        (seamRad ((Xd : ℕ) : ℝ))))
    linarith only [hfin]
  -- ⟦THE LADDER GATES⟧
  have hLg2leB : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.log ((Xd : ℕ) : ℝ) + 2 ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    have h1 : 1 + 3 * Real.log ((Xd : ℕ) : ℝ) / 8
        ≤ Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8) := by
      linarith [Real.add_one_le_exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)]
    have h2 : Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)
        * Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)
        = Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [hB34 v hv, h1, h2, hLgbig]
  have hDdk : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ ≤ witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    have hR : ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith only [hDle, hLg2leB v hv, cofkL_ramRbot_le_kk (hW5 v hv)]
    exact_mod_cast hR
  have hsqXa : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.sqrt (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v)
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
            / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by
    intro v hv
    have hBle : ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ)) := by
      rw [Real.exp_log hAsR]
      linarith only [hBX v hv, hBpos v]
    have hmono := Real.sqrt_le_sqrt hBle
    have hsq : Real.sqrt (Real.exp (Real.log ((Xd : ℕ) : ℝ)))
        = Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := by
      have hsplit2 : Real.exp (Real.log ((Xd : ℕ) : ℝ))
          = Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)
            * Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hsplit2, Real.sqrt_mul_self (Real.exp_pos _).le]
    rw [hsq] at hmono
    linarith only [hmono, hWlow v hv]
  have hpinW : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      pin2Gate ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) :=
    fun v hv => le_trans hpinhalf (hWlow v hv)
  have hXae : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.exp 1 ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    linarith only [hW5 v hv, Real.exp_one_lt_d9]
  -- ⟦THE TWO CONTOUR BOXES⟧
  have hTX : (2 : ℝ) * T ≤ ((Xd : ℕ) : ℝ) := hThi
  have hbox : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ∀ t : ℝ, |t| ≤ 2 * T →
        |t| + Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ))
          ≤ 3 * ((Xd : ℕ) : ℝ) := by
    intro v hv t ht
    exact cofkR_box_of_le (le_trans hpinhalf (hMtlow v hv))
      (by linarith only [hMtX v hv, hBX v hv]) (by linarith only [ht, hTX])
  have hboxw : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ∀ t : ℝ, |t| ≤ 2 * T → ∀ i : ℕ,
        ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
          / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ≤ (i : ℝ) →
          (i : ℝ) ≤ 2 * ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v →
            |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * ((Xd : ℕ) : ℝ) := by
    intro v hv t ht i hi1 hi2
    exact cofkR_box_of_le (le_trans (hpinW v hv) hi1)
      (by linarith only [hi2, hBX v hv]) (by linarith only [ht, hTX])
  -- ⟦`TLBlockGates34` AT THE WITNESS⟧
  have hlogLs0 : (0 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by linarith
  have hrp : (0 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg hLg0.le _
  have hp5 : (0 : ℝ) ≤ (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5 := pow_nonneg hlogLs0 5
  have hcq0 : (0 : ℝ) ≤ 420 * Real.log ((Xd : ℕ) : ℝ)
      * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5 := by
    have h1 : (0 : ℝ) ≤ 420 * Real.log ((Xd : ℕ) : ℝ) := by linarith
    exact mul_nonneg (mul_nonneg h1 hrp) hp5
  have hcqgate : 420 * Real.log ((Xd : ℕ) : ℝ)
        * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5
      ≤ (420 * Real.log ((Xd : ℕ) : ℝ)
          * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5)
        * (Real.log ((s13BandP Xd : ℕ) : ℝ)) ^ 2 := by
    have hsq : (1 : ℝ) ≤ (Real.log ((s13BandP Xd : ℕ) : ℝ)) ^ 2 := by nlinarith [hlogP2]
    nlinarith [hcq0, hsq]
  have hblk : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      TLBlockGates34 (420 * Real.log ((Xd : ℕ) : ℝ)
          * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5)
        (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (2 * Xd) Xd
        (witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
        (witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
        (2 * T) (Real.log ((Xd : ℕ) : ℝ)) (1 / Real.exp 1) Cb
        ((Xd : ℕ) : ℝ) theta293 (seamRad ((Xd : ℕ) : ℝ)) v := by
    intro v hv
    have hbaseQ : ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v ≤ s13BandQ Xd :=
      ramQbase_le_top hH0 hQ1 hPQ hv
    have hbase3 : 3 ≤ ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v :=
      le_trans hP3 (ramQbase_ge_bot _ _ _)
    have hb3R : (3 : ℝ)
        ≤ ((ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v : ℕ) : ℝ) := by
      exact_mod_cast hbase3
    have hblog0 : (0 : ℝ)
        < Real.log ((ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v : ℕ) : ℝ) :=
      Real.log_pos (by linarith only [hb3R])
    have hbQ : Real.log ((ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v : ℕ) : ℝ)
        ≤ Real.log ((s13BandQ Xd : ℕ) : ℝ) :=
      Real.log_le_log (by linarith only [hb3R]) (by exact_mod_cast hbaseQ)
    have h30 : (30 : ℝ) ≤ Real.log (2 * T)
        / Real.log ((ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v : ℕ) : ℝ) := by
      rw [le_div_iff₀ hblog0]
      linarith only [h30g, hbQ, hQlog, hblog0]
    exact tlBlockGates34_at_witness hH1 hP3 hlogP2 hQ1 hPQ hcq0 hv hQT h30 hQL hcqgate
      (by linarith only [hW5 v hv]) (hkth v hv) le_rfl (hBX v hv) (hC16 v hv) hRrad0
      (hRradW v hv)
  -- ⟦THE HEAD⟧
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hce : (1 : ℝ) / Real.exp 1 ≤ 1 / Real.exp 1 := le_refl _
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith [Real.exp_one_gt_d9])]
    linarith [Real.exp_one_gt_d9]
  -- ⟦THE EXIT⟧
  have hRb0 : (0 : ℝ) ≤ 4 * (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)) := by
    linarith only [mul_nonneg (cofkRConst_pos hCb0).le hpow0]
  refine ⟨seamRad ((Xd : ℕ) : ℝ),
    4 * (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)),
    4 * cofkRConst Cb, hRb0, le_of_eq (by ring), hgradegate, ?_⟩
  intro t₁ χ
  have hs := hsup q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M)
    (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd (s13BandP Xd) (s13BandQ Xd) 2 1
    (witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
    (witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
    (fun _ : ℕ => ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊)
    (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
    (420 * Real.log ((Xd : ℕ) : ℝ)
      * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5)
    (Real.log ((Xd : ℕ) : ℝ)) (1 / Real.exp 1) Cb ((Xd : ℕ) : ℝ) theta293
    (seamRad ((Xd : ℕ) : ℝ)) (2 * T) t₁
    (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)) (1 / Real.exp 1)
    (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
    hc0 hce hc1 hCb0 hCbound hP1 (le_refl 1) hRrad0 hθ0 hθ32 hLX hPlow hQhigh hPQ
    (hfloorχ χ) hblk hbox (fun _ _ => hDone) hDdk hXskj hsqXa hpinW hXae hMtX hBX hMfl0
    hboxw hS0 hSbd hendGen hRbdU
  have he : (2 : ℝ) ^ (2 : ℕ) * (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
      = 4 * (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)) := by norm_num
  rwa [he] at hs

end Salt.MR

end
