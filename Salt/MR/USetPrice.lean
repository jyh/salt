/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetBalance

/-!
# USetPrice — the THREE PRICING RESIDUALS of §8.3's `hU` (⟦V5e⟧'s P-a/P-b/P-c)

`USetBalance` supplies the `hU` row STRUCTURALLY: `hU_supplied` carries the two grade budgets
`KS` (the `𝒯_S` per-block constant) and `R̄` (the uniform co-factor bound) as *binders*, and
`hU_balance` collapses the main/remainder legs at the ratified `θ₂₉₃` from *assumed* `hmain`,
`hrem`.  This file PRICES those four slots — the last work of `hU`.

* **§1 (P-b) `KS_priced` / `KS_supplied`** — the `𝒯_S` constant.  `USetThinTS.ramRcoeff_mass_le`
  reduces the coefficient mass to the harmonic-square mass of the co-factor range; the range
  sits in `[m₀, Ms]` with `m₀ ≤ ramRbot H Xd j = Xd·e^{−j/H}`, so `USetBalance`'s telescope
  `sum_inv_sq_Icc_le` gives `Σ 1/m² ≤ 1/(m₀−1)`.  With the sharp length `Ms ≤ 4(m₀−1)`
  (⟦V4a⟧ finding 1 — `Ms ≍ 2·ramRbot`, so this is the honest gate `ramRbot ≥ 3`) the product
  `Ms·Σ 1/m²` is at most `4`, and the whole `𝒯_S` slot is
  `KS = 20512·δ'²·(1 + log 2Tann)` — a CONSTANT in `j`, carrying the level `δ'` squared.
  That `δ'²` is the ⟦V5e⟧ `ε²` absorption: it is what pays for `|I|` appearing twice.

* **§2 (P-c) `Rbd_uniform`** — the uniform `R̄`.  `cofactorRbd = 3·max(2·caseAS …, farSupS …)`
  is ANTITONE in the descent anchor `k₀` (three ways: the floor `cofactorMfl X θ k₀` grows
  with `k₀` through `S(k₀)`, and both `(log k₀)^{−1/(32e)}` and `(log k₀)^{−1/2+1/1000}` fall)
  and MONOTONE in the window top `M` (through `farErr`'s `log(3 + Rmax(1+log M))`).

  **THE WORST-END VERDICT (honest):** the two arms disagree.  `k₀(j) ≍ X e^{−j/H}` falls with
  `j`, so the `caseAS` arm and `farErr`'s denominator are worst at the LARGEST `j` (the
  smallest `k₀`); `Mt j ≍ 2·k₀(j)` also falls with `j`, so `farErr`'s numerator is worst at the
  SMALLEST `j` (the largest `M`).  Neither endpoint dominates: `R̄` is the value at the MIXED
  corner `(kmin, Ymax)`, and `Rbd_uniform` is stated at exactly that corner.

* **§3 (P-a) `balance_priced_main` / `rem_priced`** — `hU_balance`'s two binders at the full
  pin `H := H83 X θ₂₉₃`, `P ≥ P83 X θ₂₉₃`, `Q ≤ Q83 X`.
  - the card page: `|I| = ⌊H log Q⌋ − ⌊H log P⌋ + 1 ≤ H log Q + 1`, and at the pins
    `≤ 2(log X)^{1+θ}` (the `(log X)^{1+θ}/loglog X`-shape of ⟦V5e⟧, majorised by dropping
    the `loglog` gain — the block leg has `(log X)^{−2θ}` of spare and does not need it);
  - the floor page: `H log P ≥ (log X)^θ·(log X)^{1−θ} = log X`, so `⌊H log P⌋ − 1 ≥ log X/2`
    — this is where MR p.29's `1/log P` actually lives;
  - the main page: `4|I|(|I|KS + 54C_q R̄²H²/(⌊H log P⌋−1)) ≤ (log X)^{5θ−2ρ}` at the two
    stated gates `32(log X)^{2+2θ}KS ≤ (log X)^{−θ}` and `1728 C_q ≤ (log X)^{2θ}`.  The
    `𝒯_L` leg lands at `864·C_q·(log X)^{−3θ}` against a budget of `(log X)^{−θ}`: the
    `(log X)^{−2θ}` spare of ⟦V5e⟧, in Lean.
  - the remainder page: Lemma 12's three rows (`RamareErr.ramWindowErr_moment_grade`'s
    `720(T/X+1)/H`, the `p²`-correction row `EP2`, the coprime tail — zero under the §8.3
    support pin) give `2E ≤ (Tann/X+1)(log X)^{−θ+ε}` at the stated absorption `8640 ≤
    (log X)^ε`.

* **§4 (P-d) `hU_fully_priced`** — `USetBalance.hU_discharged` with `hKS`, `hRbdU`, `hmain`,
  `hrem` ALL discharged: the seam row at the pins, carrying only the frame, the geometric
  bundles, and the in-statement thresholds.

**The one grade left as a pin** (⟦V5e⟧'s Zeno line): `R̄ ≤ (log X)^{−ρ₂₉₃}`.  That is U-7's
own exit grade — `CofactorGrade.caseA_grade_numeral` is the identity
`e^{−(1/e)(1/32−θ)loglog W} = (log W)^{−ρ₂₉₃}` at the LOCAL scale `W`, whereas `cofactorMfl`
carries the GLOBAL floor less the priced descent `2(S(X) − S(k₀))`; converting one to the
other needs the Mertens page for `S(X) − S(k₀)` and is not attempted here.  It rides
in-statement (law #253), never assumed off-stage.

Source pins (D5): MR arXiv v4 (`1501.04585v4`) pp. 19–20, 27–29 (§8.3);
`docs/exploration/hsup-design.md` ⟦V4⟧/⟦V4a⟧/⟦V4b⟧/⟦V5c⟧/⟦V5d⟧/⟦V5e⟧.
-/

namespace Salt.MR

open scoped BigOperators
open Finset MeasureTheory

/-! ## §1 — P-b: the `𝒯_S` per-block constant `KS` -/

/-- **The co-factor range sits above its floor.**  Every `m ∈ ramRrange H N Xd j` obeys
`Xd·e^{−j/H} ≤ m` by definition, so any natural `m₀` at or below `ramRbot H Xd j` is a lower
endpoint for the range. -/
lemma ramRrange_subset_Icc_bot (H : ℝ) (N Xd j m₀ Ms : ℕ)
    (hm₀ : ((m₀ : ℕ) : ℝ) ≤ ramRbot H Xd j)
    (hMs : ramRrange H N Xd j ⊆ Finset.Icc 1 Ms) :
    ramRrange H N Xd j ⊆ Finset.Icc m₀ Ms := by
  classical
  intro m hm
  have hup : m ≤ Ms := (Finset.mem_Icc.mp (hMs hm)).2
  have hmem : (Xd : ℝ) * Real.exp (-(j : ℝ) / H) ≤ (m : ℝ) := by
    have h := hm
    simp only [ramRrange, Finset.mem_filter] at h
    exact h.2.1
  have hlow : m₀ ≤ m := by
    have hR : ((m₀ : ℕ) : ℝ) ≤ (m : ℝ) := by
      refine le_trans hm₀ ?_
      rw [ramRbot]
      exact hmem
    exact_mod_cast hR
  exact Finset.mem_Icc.mpr ⟨hlow, hup⟩

/-- **THE HARMONIC-SQUARE PAGE.**  The co-factor coefficient mass at `‖b‖ ≤ 1`, priced by the
telescope: `Σ_{m ≤ Ms} ‖R_m‖²/m² ≤ Σ_{m ∈ range} 1/m² ≤ Σ_{m=m₀}^{Ms} 1/m² ≤ 1/(m₀−1)`.
The range's floor `m₀ ≤ ramRbot H Xd j` is the ⟦V4a⟧ sharp co-factor length in its lower
form — pricing at the dyadic `N` instead would replace `1/(m₀−1)` by `1`. -/
lemma cofactor_mass_le (H : ℝ) (N Xd P Q j : ℕ) (b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1)
    (m₀ Ms : ℕ) (hm₀2 : 2 ≤ m₀) (hm₀ : ((m₀ : ℕ) : ℝ) ≤ ramRbot H Xd j)
    (hMs : ramRrange H N Xd j ⊆ Finset.Icc 1 Ms) :
    (∑ m ∈ Finset.Icc 1 Ms, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
      ≤ 1 / ((m₀ : ℝ) - 1) := by
  refine le_trans (ramRcoeff_mass_le H N Xd P Q j Ms b hb hMs) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (ramRrange_subset_Icc_bot H N Xd j m₀ Ms hm₀ hMs) (fun m _ _ => by positivity)) ?_
  exact sum_inv_sq_Icc_le m₀ Ms hm₀2

/-- **P-b — THE `𝒯_S` PER-BLOCK CONSTANT** (`KS_priced`).  `U-5`'s exit slot, priced:

  `5128·δ'²·Ms·(1 + log 2T)·Σ_{m ≤ Ms} ‖R_m‖²/m² ≤ 20512·δ'²·(1 + log 2T)`.

The whole content is `Ms·Σ 1/m² ≤ 4`, from `cofactor_mass_le` and the stated sharpness gate
`Ms ≤ 4(m₀ − 1)` — honest because `Ms ≍ 2·ramRbot` and `m₀ ≍ ramRbot` (the gate is then
`ramRbot ≥ 3`, which the `𝒯_S` budget already implies with astronomical room).

NOTHING in the exit depends on `j`: this is the "`M·Σ_m 1/m² ≍ 1`" of `USetBalance`:320,
made a numeral. -/
theorem KS_priced (H : ℝ) (N Xd P Q j : ℕ) (b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1)
    (m₀ Ms : ℕ) (hm₀2 : 2 ≤ m₀) (hm₀ : ((m₀ : ℕ) : ℝ) ≤ ramRbot H Xd j)
    (hMs : ramRrange H N Xd j ⊆ Finset.Icc 1 Ms)
    (hMs4 : ((Ms : ℕ) : ℝ) ≤ 4 * ((m₀ : ℝ) - 1))
    (T δ' : ℝ) (hT : 1 ≤ T) :
    5128 * δ' ^ 2 * ((Ms : ℕ) : ℝ) * (1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 Ms, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
      ≤ 20512 * δ' ^ 2 * (1 + Real.log (2 * T)) := by
  have hm0R : (2 : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hm₀2
  have hpos : (0 : ℝ) < (m₀ : ℝ) - 1 := by linarith
  have hlog : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hMs0 : (0 : ℝ) ≤ ((Ms : ℕ) : ℝ) := Nat.cast_nonneg Ms
  have hmass := cofactor_mass_le H N Xd P Q j b hb m₀ Ms hm₀2 hm₀ hMs
  have hkey : ((Ms : ℕ) : ℝ)
      * (∑ m ∈ Finset.Icc 1 Ms, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) ≤ 4 := by
    calc ((Ms : ℕ) : ℝ)
          * (∑ m ∈ Finset.Icc 1 Ms, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
        ≤ ((Ms : ℕ) : ℝ) * (1 / ((m₀ : ℝ) - 1)) := mul_le_mul_of_nonneg_left hmass hMs0
      _ ≤ 4 := by
          rw [mul_one_div, div_le_iff₀ hpos]
          linarith
  have hfront : (0 : ℝ) ≤ 5128 * δ' ^ 2 * (1 + Real.log (2 * T)) := by positivity
  calc 5128 * δ' ^ 2 * ((Ms : ℕ) : ℝ) * (1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 Ms, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
      = (5128 * δ' ^ 2 * (1 + Real.log (2 * T)))
          * (((Ms : ℕ) : ℝ)
              * ∑ m ∈ Finset.Icc 1 Ms, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) := by
        ring
    _ ≤ (5128 * δ' ^ 2 * (1 + Real.log (2 * T))) * 4 := mul_le_mul_of_nonneg_left hkey hfront
    _ = 20512 * δ' ^ 2 * (1 + Real.log (2 * T)) := by ring

/-- **P-b, in `hU_supplied`'s `hKS` shape.**  The per-block slot of `USetBalance.hU_supplied`
at the co-factor datum `b := ellLin g`, discharged uniformly over the block range with the
explicit constant `KS = 20512·δ'²·(1 + log 2Tann)`. -/
theorem KS_supplied (H : ℝ) (N Xd P Q : ℕ) (g : ℕ → ℂ) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1)
    (m₀ Ms : ℕ → ℕ) (Tann δ' : ℝ) (hT : 1 ≤ Tann)
    (hm₀2 : ∀ j ∈ ramI H P Q, 2 ≤ m₀ j)
    (hm₀ : ∀ j ∈ ramI H P Q, ((m₀ j : ℕ) : ℝ) ≤ ramRbot H Xd j)
    (hMs : ∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j))
    (hMs4 : ∀ j ∈ ramI H P Q, ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) :
    ∀ j ∈ ramI H P Q, 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
        * (∑ m ∈ Finset.Icc 1 (Ms j),
            ‖ramRcoeff H N Xd P Q j (ellLin g) m‖ ^ 2 / (m : ℝ) ^ 2)
      ≤ 20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)) := by
  intro j hj
  exact KS_priced H N Xd P Q j (ellLin g) (fun n => ellLin_norm_le_one g hg n) (m₀ j) (Ms j)
    (hm₀2 j hj) (hm₀ j hj) (hMs j hj) (hMs4 j hj) Tann δ' hT

/-! ## §2 — P-c: the uniform co-factor bound `R̄` -/

/-- **The CASE-A floor grows with the descent anchor.**  `cofactorMfl X θ W = (1/32−θ)loglog X
− 2(S(X) − S(W))`: a bigger window bottom pays a smaller descent, so the floor is monotone
in `W` (`SPartial` is monotone). -/
lemma cofactorMfl_mono (X θ : ℝ) {W W' : ℝ} (h : W' ≤ W) :
    cofactorMfl X θ W' ≤ cofactorMfl X θ W := by
  have hS : Salt.Mertens.SPartial W' ≤ Salt.Mertens.SPartial W :=
    SPartial_mono_floor (Nat.floor_mono h)
  unfold cofactorMfl
  linarith

/-- **`caseAS` is antitone in BOTH slots.**  The grade factor `e^{−cM}` falls as the floor `M`
rises (`0 < c`), and both far numerals `(log W)^{−1/(32e)}`, `(log W)^{−1/2+1/1000}` fall as
the scale `W` rises (negative exponents). -/
lemma caseAS_anti {c Cb M M' W W' : ℝ} (hc0 : 0 < c) (hc1 : 2 * c < 1) (hCb0 : 0 ≤ Cb)
    (hM : M' ≤ M) (hW1 : 1 < W') (hW : W' ≤ W) :
    caseAS c Cb M W ≤ caseAS c Cb M' W' := by
  have hC0 : (0 : ℝ) ≤ gradeAbsConstC c Cb := gradeAbsConstC_nonneg hc1 hCb0
  have hlW' : (0 : ℝ) < Real.log W' := Real.log_pos hW1
  have hlW : Real.log W' ≤ Real.log W := Real.log_le_log (by linarith) hW
  have hcM : c * M' ≤ c * M := mul_le_mul_of_nonneg_left hM (le_of_lt hc0)
  have h1 : Real.exp (-c * M) ≤ Real.exp (-c * M') := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.log W ^ (-(1 / (32 * Real.exp 1))) ≤ Real.log W' ^ (-(1 / (32 * Real.exp 1))) :=
    Real.rpow_le_rpow_of_nonpos hlW' hlW (neg_nonpos.mpr (by positivity))
  have h3 : Real.log W ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.log W' ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_le_rpow_of_nonpos hlW' hlW (by norm_num)
  have hA : gradeAbsConstC c Cb * Real.exp (-c * M)
      ≤ gradeAbsConstC c Cb * Real.exp (-c * M') := mul_le_mul_of_nonneg_left h1 hC0
  have hB : farCStar * Real.log W ^ (-(1 / (32 * Real.exp 1)))
      ≤ farCStar * Real.log W' ^ (-(1 / (32 * Real.exp 1))) :=
    mul_le_mul_of_nonneg_left h2 farCStar_nonneg
  unfold caseAS
  linarith

/-- **`farErr` is antitone in the window bottom and monotone in the window top.**  The
numerator carries `log(3 + Rmax(1 + log Y))`, the denominator `√(log W)`. -/
lemma farErr_le {W W' Y Y' Rmax : ℝ} (hW1 : 1 < W') (hW : W' ≤ W) (hRmax : 0 ≤ Rmax)
    (hY : 1 ≤ Y) (hYY : Y ≤ Y') :
    farErr W Y Rmax ≤ farErr W' Y' Rmax := by
  have hlW' : (0 : ℝ) < Real.log W' := Real.log_pos hW1
  have hlW : Real.log W' ≤ Real.log W := Real.log_le_log (by linarith) hW
  have hsq' : (0 : ℝ) < Real.sqrt (Real.log W') := Real.sqrt_pos.mpr hlW'
  have hsq : Real.sqrt (Real.log W') ≤ Real.sqrt (Real.log W) := Real.sqrt_le_sqrt hlW
  have hlY : (0 : ℝ) ≤ Real.log Y := Real.log_nonneg hY
  have hlYY : Real.log Y ≤ Real.log Y' := Real.log_le_log (by linarith) hYY
  have hin0 : (0 : ℝ) < 3 + Rmax * (1 + Real.log Y) := by nlinarith
  have hnum : Real.log (3 + Rmax * (1 + Real.log Y))
      ≤ Real.log (3 + Rmax * (1 + Real.log Y')) := by
    refine Real.log_le_log hin0 ?_
    nlinarith
  have hC := ballSupC_pos
  have htop : 4 * ballSupC * (1 + Real.log (3 + Rmax * (1 + Real.log Y)))
      ≤ 4 * ballSupC * (1 + Real.log (3 + Rmax * (1 + Real.log Y'))) := by nlinarith
  have htop0 : (0 : ℝ) ≤ 4 * ballSupC * (1 + Real.log (3 + Rmax * (1 + Real.log Y'))) := by
    have h1 : (1 : ℝ) ≤ 3 + Rmax * (1 + Real.log Y') := by nlinarith
    have := Real.log_nonneg h1
    nlinarith
  unfold farErr
  exact div_le_div₀ htop0 htop hsq' hsq

/-- **`farSupS` inherits the two monotonicities** (the radius slot `R` is untouched: it is the
ball removal's own datum, the same for every block). -/
lemma farSupS_le {W W' Y Y' Rmax R : ℝ} (hW1 : 1 < W') (hW : W' ≤ W) (hRmax : 0 ≤ Rmax)
    (hY : 1 ≤ Y) (hYY : Y ≤ Y') :
    farSupS W Y Rmax R ≤ farSupS W' Y' Rmax R := by
  have h := farErr_le (W := W) (W' := W') (Y := Y) (Y' := Y') (Rmax := Rmax) hW1 hW hRmax hY hYY
  unfold farSupS
  linarith

/-- **P-c (the monotone step) — `cofactorRbd` at the worst corner.**  `cofactorRbd` falls when
the descent anchor `W` rises and rises when the window top `Y` rises, so its value at
`(kmin, Ymax)` dominates its value at any `(W, Y)` inside `[kmin, ∞) × [1, Ymax]`. -/
theorem cofactorRbd_le_of_worst {cg Cb X θ W W' Y Y' Rmax R : ℝ}
    (hc0 : 0 < cg) (hc1 : 2 * cg < 1) (hCb0 : 0 ≤ Cb)
    (hW1 : 1 < W') (hW : W' ≤ W) (hRmax : 0 ≤ Rmax) (hY : 1 ≤ Y) (hYY : Y ≤ Y') :
    cofactorRbd cg Cb X θ W Y Rmax R ≤ cofactorRbd cg Cb X θ W' Y' Rmax R := by
  have hmfl : cofactorMfl X θ W' ≤ cofactorMfl X θ W := cofactorMfl_mono X θ hW
  have h1 : 2 * caseAS cg Cb (cofactorMfl X θ W) W
      ≤ 2 * caseAS cg Cb (cofactorMfl X θ W') W' := by
    have := caseAS_anti (c := cg) (Cb := Cb) (M := cofactorMfl X θ W)
      (M' := cofactorMfl X θ W') (W := W) (W' := W') hc0 hc1 hCb0 hmfl hW1 hW
    linarith
  have h2 : farSupS W Y Rmax R ≤ farSupS W' Y' Rmax R := farSupS_le hW1 hW hRmax hY hYY
  have hmax := max_le_max h1 h2
  unfold cofactorRbd
  linarith

/-- **P-c — THE UNIFORM `R̄`** (`Rbd_uniform`), in `hU_supplied`'s `hRbdU` shape.

`R̄ := cofactorRbd cg Cb X θ kmin Ymax (Dmax+1) Rrad` — the value at the MIXED worst corner:
`kmin` a lower bound for every block's descent anchor `k₀(j)` (attained at the LARGEST `j`,
since `k₀(j) ≍ X e^{−j/H}` falls), `Ymax` an upper bound for every block's window top `Mt j`
(attained at the SMALLEST `j`).  The two ends genuinely disagree — `caseAS` and `farErr`'s
denominator want small `k₀`, `farErr`'s numerator wants large `M` — so no single block index
is "the worst block"; the corner is. -/
theorem Rbd_uniform (H : ℝ) (P Q : ℕ) (Mt kk : ℕ → ℕ)
    (cg Cb X θ Dmax Rrad kmin Ymax : ℝ)
    (hc0 : 0 < cg) (hc1 : 2 * cg < 1) (hCb0 : 0 ≤ Cb) (hkmin : 1 < kmin)
    (hDmax : 0 ≤ Dmax + 1)
    (hkk : ∀ j ∈ ramI H P Q, kmin ≤ ((kk j : ℕ) : ℝ))
    (hMt1 : ∀ j ∈ ramI H P Q, 1 ≤ ((Mt j : ℕ) : ℝ))
    (hMt : ∀ j ∈ ramI H P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) :
    ∀ j ∈ ramI H P Q,
      cofactorRbd cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ) (Dmax + 1) Rrad
        ≤ cofactorRbd cg Cb X θ kmin Ymax (Dmax + 1) Rrad := fun j hj =>
  cofactorRbd_le_of_worst hc0 hc1 hCb0 hkmin (hkk j hj) hDmax (hMt1 j hj) (hMt j hj)

/-! ## §3 — P-a: the balance binders at the full pin `H₈₃`, `P₈₃`, `Q₈₃` -/

/-- `(log X)^{1+θ}·(log X)^{1+θ} = (log X)^{2+2θ}` — the `|I|²` exponent. -/
lemma pin_pow_sq {X : ℝ} (hL0 : 0 < Real.log X) :
    (Real.log X) ^ (1 + theta293) * (Real.log X) ^ (1 + theta293)
      = (Real.log X) ^ (2 + 2 * theta293) := by
  rw [← Real.rpow_add hL0, show (1 + theta293) + (1 + theta293) = 2 + 2 * theta293 by ring]

/-- `(log X)^{2θ}·(log X)^{−3θ} = (log X)^{−θ}` — the `(log X)^{−2θ}` spare of the `𝒯_L`
leg, as an identity. -/
lemma pin_pow_split {X : ℝ} (hL0 : 0 < Real.log X) :
    (Real.log X) ^ (2 * theta293) * (Real.log X) ^ (-3 * theta293)
      = (Real.log X) ^ (-theta293) := by
  rw [← Real.rpow_add hL0, show 2 * theta293 + -3 * theta293 = -theta293 by ring]

/-- **THE `𝒯_L` BLOCK EXPONENT.**  `(log X)^{1+θ}·(log X)^{−2ρ}·(log X)^{2θ}·(log X)^{−1}
= (log X)^{3θ−2ρ} = (log X)^{−3θ}` at `ρ₂₉₃ = 3θ₂₉₃`: the block count, the co-factor grade
squared, the Ramaré width squared, and MR p.29's `1/log P`, multiplied out. -/
lemma pin_pow_block {X : ℝ} (hL0 : 0 < Real.log X) :
    (Real.log X) ^ (1 + theta293)
        * ((Real.log X) ^ (-2 * rho293) * (Real.log X) ^ (2 * theta293) * (Real.log X)⁻¹)
      = (Real.log X) ^ (-3 * theta293) := by
  rw [← Real.rpow_neg_one (Real.log X), ← Real.rpow_add hL0, ← Real.rpow_add hL0,
    ← Real.rpow_add hL0,
    show (1 + theta293) + (-2 * rho293 + 2 * theta293 + -1) = -3 * theta293 by
      rw [rho293]; ring]

/-- **THE CARD PAGE (crude form).**  `|I| = ⌊H log Q⌋ − ⌊H log P⌋ + 1 ≤ ⌊H log Q⌋ + 1 ≤
H log Q + 1`.  The lower endpoint is dropped: the block leg has `(log X)^{−2θ}` of spare and
does not need the `−⌊H log P⌋` gain. -/
lemma ramI_card_le (H : ℝ) (P Q : ℕ) (hHQ : 0 ≤ H * Real.log (Q : ℝ)) :
    ((ramI H P Q).card : ℝ) ≤ H * Real.log (Q : ℝ) + 1 := by
  have hc : (ramI H P Q).card ≤ ⌊H * Real.log (Q : ℝ)⌋₊ + 1 := by
    rw [ramI, Nat.card_Icc]
    omega
  have h1 : ((ramI H P Q).card : ℝ) ≤ ((⌊H * Real.log (Q : ℝ)⌋₊ : ℕ) : ℝ) + 1 := by
    exact_mod_cast hc
  have h2 : ((⌊H * Real.log (Q : ℝ)⌋₊ : ℕ) : ℝ) ≤ H * Real.log (Q : ℝ) := Nat.floor_le hHQ
  linarith

/-- **THE CARD PAGE AT THE PIN.**  At `H = H₈₃ = (log X)^θ` and `Q ≤ Q₈₃ = exp(log X/loglog X)`
the block count is `|I| ≤ (log X)^{1+θ}/loglog X + 1 ≤ 2(log X)^{1+θ}` — ⟦V5e⟧'s shape, with
the `1/loglog X` gain thrown away (it is not needed and would only complicate the gates). -/
lemma ramI_card_le_pin (X : ℝ) (P Q : ℕ) (hQ0 : 0 < Q) (hQpin : (Q : ℝ) ≤ Q83 X)
    (hLe : Real.exp 1 ≤ Real.log X) :
    ((ramI (H83 X theta293) P Q).card : ℝ) ≤ 2 * (Real.log X) ^ (1 + theta293) := by
  have he1 : (1 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hL1 : (1 : ℝ) < Real.log X := lt_of_lt_of_le he1 hLe
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log (Real.exp_pos 1) hLe
    rwa [Real.log_exp] at h
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ0
  have hQpos : (0 : ℝ) < (Q : ℝ) := by linarith
  have hlogQ0 : (0 : ℝ) ≤ Real.log (Q : ℝ) := Real.log_nonneg hQ1
  have hlogQ : Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) := by
    have h := Real.log_le_log hQpos hQpin
    rwa [Q83, Real.log_exp] at h
  have hH0 : (0 : ℝ) ≤ H83 X theta293 := by
    rw [H83]; exact Real.rpow_nonneg hL0.le _
  have hcard := ramI_card_le (H83 X theta293) P Q (mul_nonneg hH0 hlogQ0)
  have hdiv : Real.log X / Real.log (Real.log X) ≤ Real.log X := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hmul : (Real.log X) ^ (1 + theta293) = (Real.log X) ^ theta293 * Real.log X := by
    rw [show (1 : ℝ) + theta293 = theta293 + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
  have hstep : H83 X theta293 * Real.log (Q : ℝ) ≤ (Real.log X) ^ (1 + theta293) := by
    rw [hmul, H83]
    exact mul_le_mul_of_nonneg_left (le_trans hlogQ hdiv) (Real.rpow_nonneg hL0.le _)
  have h1le : (1 : ℝ) ≤ (Real.log X) ^ (1 + theta293) := by
    have h0 : (Real.log X) ^ (0 : ℝ) ≤ (Real.log X) ^ (1 + theta293) :=
      Real.rpow_le_rpow_of_exponent_le hL1.le (by linarith [theta293_pos])
    rwa [Real.rpow_zero] at h0
  linarith

/-- **THE `P`-PIN, in `log` form.**  `H₈₃·log P ≥ (log X)^θ·(log X)^{1−θ} = log X` for any
window endpoint at or above `P₈₃`. -/
lemma H83_log_P_ge (X : ℝ) (P : ℕ) (hL0 : 0 < Real.log X) (hP : P83 X theta293 ≤ (P : ℝ)) :
    Real.log X ≤ H83 X theta293 * Real.log (P : ℝ) := by
  have hlogP : (Real.log X) ^ (1 - theta293) ≤ Real.log (P : ℝ) := by
    have hP0 : (0 : ℝ) < P83 X theta293 := Real.exp_pos _
    have h := Real.log_le_log hP0 hP
    rwa [P83, Real.log_exp] at h
  have hsplit : (Real.log X) ^ theta293 * (Real.log X) ^ (1 - theta293) = Real.log X := by
    rw [← Real.rpow_add hL0, show theta293 + (1 - theta293) = (1 : ℝ) by ring, Real.rpow_one]
  calc Real.log X = (Real.log X) ^ theta293 * (Real.log X) ^ (1 - theta293) := hsplit.symm
    _ ≤ (Real.log X) ^ theta293 * Real.log (P : ℝ) :=
        mul_le_mul_of_nonneg_left hlogP (Real.rpow_nonneg hL0.le _)
    _ = H83 X theta293 * Real.log (P : ℝ) := by rw [H83]

/-- **THE FLOOR PAGE** — where MR p.29's `1/log P` lives.  At the pin, `⌊H₈₃ log P⌋ ≥
⌊log X⌋ > log X − 1`, so the `Σ_{j∈I} 1/j²` telescope's endpoint obeys
`⌊H log P⌋ − 1 ≥ log X/2` (and in particular `USetBalance.hU_supplied`'s `hj₀` binder
`2 ≤ ⌊H log P⌋` holds). -/
lemma floor_pin (X : ℝ) (P : ℕ) (hL4 : 4 ≤ Real.log X) (hP : P83 X theta293 ≤ (P : ℝ)) :
    2 ≤ ⌊H83 X theta293 * Real.log (P : ℝ)⌋₊ ∧
      Real.log X / 2 ≤ ((⌊H83 X theta293 * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) - 1 := by
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hA := H83_log_P_ge X P hL0 hP
  refine ⟨?_, ?_⟩
  · refine Nat.le_floor ?_
    push_cast
    linarith
  · have hlt : H83 X theta293 * Real.log (P : ℝ)
        < ((⌊H83 X theta293 * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith

/-- **P-a (i)+(ii) — THE MAIN LEG, PRICED** (`balance_priced_main`).  `USetBalance.hU_balance`'s
`hmain` binder, discharged at the pin:

  `4|I|·(|I|·KS + 54·C_q·R̄²·H²/(⌊H log P⌋−1)) ≤ (log X)^{5θ₂₉₃−2ρ₂₉₃}`.

The two legs, each against half the budget `(log X)^{−θ₂₉₃}`:

* the `𝒯_S` leg `4|I|²·KS ≤ 16(log X)^{2+2θ}·KS`, closed by the stated gate
  `32(log X)^{2+2θ}·KS ≤ (log X)^{−θ}`.  With §1's `KS = 20512·δ'²(1+log 2Tann)` this is a
  gate on the LEVEL `δ'` — the ⟦V5e⟧ `ε²` absorption, which is what pays for `|I|` appearing
  twice on the `𝒯_S` side;
* the `𝒯_L` leg `4|I|·54C_q R̄²H²/(⌊H log P⌋−1) ≤ 864·C_q·C_R²·(log X)^{3θ−2ρ} =
  864·C_q·C_R²·(log X)^{−3θ}`, closed by the stated gate `1728·C_q·C_R² ≤ (log X)^{2θ}`.  The
  exponent gap `−3θ` against `−θ` is exactly ⟦V5e⟧'s `(log X)^{−2θ}` spare.

`R̄ ≤ C_R·(log X)^{−ρ₂₉₃}` rides in-statement (see the module docstring's Zeno note).  **The
constant `C_R` is carried and NOT set to `1`**: U-7's exit is
`gradeAbsConstC·(log X)^{−ρ}·e^{(2/e)(S(X)−S(k₀))}` with an absolute front constant, so
demanding `R̄ ≤ (log X)^{−ρ}` outright would be a hypothesis no `X` satisfies — a silent
vacuity.  The constant is instead absorbed by the `C_q`-gate, which is a numeral against a
GROWING power and therefore genuinely satisfiable. -/
theorem balance_priced_main (X H Cq CR KS Rbar : ℝ) (P Q : ℕ)
    (hL0 : 0 < Real.log X) (hH0 : 0 ≤ H)
    (hcard : ((ramI H P Q).card : ℝ) ≤ 2 * (Real.log X) ^ (1 + theta293))
    (hHub : H ≤ (Real.log X) ^ theta293)
    (hfloor : Real.log X / 2 ≤ ((⌊H * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) - 1)
    (hCq0 : 0 ≤ Cq) (hKS0 : 0 ≤ KS) (hRbar0 : 0 ≤ Rbar)
    (hRgrade : Rbar ≤ CR * (Real.log X) ^ (-rho293))
    (hKSgate : 32 * (Real.log X) ^ (2 + 2 * theta293) * KS ≤ (Real.log X) ^ (-theta293))
    (hCqgate : 1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293)) :
    4 * ((ramI H P Q).card : ℝ)
        * (((ramI H P Q).card : ℝ) * KS
            + 54 * Cq * Rbar ^ 2 * H ^ 2 / (((⌊H * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) - 1))
      ≤ (Real.log X) ^ (5 * theta293 - 2 * rho293) := by
  have hLpow0 : ∀ a : ℝ, (0 : ℝ) ≤ (Real.log X) ^ a := fun a => Real.rpow_nonneg hL0.le a
  have hc0 : (0 : ℝ) ≤ ((ramI H P Q).card : ℝ) := Nat.cast_nonneg _
  have hFpos : (0 : ℝ) < ((⌊H * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) - 1 := by linarith
  -- the `𝒯_S` leg
  have hcsq : ((ramI H P Q).card : ℝ) * ((ramI H P Q).card : ℝ)
      ≤ 4 * (Real.log X) ^ (2 + 2 * theta293) := by
    calc ((ramI H P Q).card : ℝ) * ((ramI H P Q).card : ℝ)
        ≤ (2 * (Real.log X) ^ (1 + theta293)) * (2 * (Real.log X) ^ (1 + theta293)) :=
          mul_self_le_mul_self hc0 hcard
      _ = 4 * ((Real.log X) ^ (1 + theta293) * (Real.log X) ^ (1 + theta293)) := by ring
      _ = 4 * (Real.log X) ^ (2 + 2 * theta293) := by rw [pin_pow_sq hL0]
  have hterm1 : 4 * ((ramI H P Q).card : ℝ) * (((ramI H P Q).card : ℝ) * KS)
      ≤ (1 / 2) * (Real.log X) ^ (-theta293) := by
    have h2 : 4 * (((ramI H P Q).card : ℝ) * ((ramI H P Q).card : ℝ)) * KS
        ≤ 4 * (4 * (Real.log X) ^ (2 + 2 * theta293)) * KS := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcsq (by norm_num : (0 : ℝ) ≤ 4)) hKS0
      linarith
    nlinarith [hKSgate, h2]
  -- the `𝒯_L` leg
  have hR2 : Rbar ^ 2 ≤ CR ^ 2 * (Real.log X) ^ (-2 * rho293) := by
    calc Rbar ^ 2 = Rbar * Rbar := sq Rbar
      _ ≤ (CR * (Real.log X) ^ (-rho293)) * (CR * (Real.log X) ^ (-rho293)) :=
          mul_self_le_mul_self hRbar0 hRgrade
      _ = CR ^ 2 * ((Real.log X) ^ (-rho293) * (Real.log X) ^ (-rho293)) := by ring
      _ = CR ^ 2 * (Real.log X) ^ (-2 * rho293) := by
          rw [← Real.rpow_add hL0, show -rho293 + -rho293 = -2 * rho293 by ring]
  have hH2 : H ^ 2 ≤ (Real.log X) ^ (2 * theta293) := by
    calc H ^ 2 = H * H := sq H
      _ ≤ (Real.log X) ^ theta293 * (Real.log X) ^ theta293 := mul_self_le_mul_self hH0 hHub
      _ = (Real.log X) ^ (2 * theta293) := by
          rw [← Real.rpow_add hL0, show theta293 + theta293 = 2 * theta293 by ring]
  have h54 : (0 : ℝ) ≤ 54 * Cq := by linarith
  have hnum : 54 * Cq * Rbar ^ 2 * H ^ 2
      ≤ 54 * Cq * CR ^ 2 * ((Real.log X) ^ (-2 * rho293) * (Real.log X) ^ (2 * theta293)) := by
    have h1 : Rbar ^ 2 * H ^ 2
        ≤ (CR ^ 2 * (Real.log X) ^ (-2 * rho293)) * (Real.log X) ^ (2 * theta293) :=
      mul_le_mul hR2 hH2 (sq_nonneg H) (mul_nonneg (sq_nonneg CR) (hLpow0 _))
    calc 54 * Cq * Rbar ^ 2 * H ^ 2 = (54 * Cq) * (Rbar ^ 2 * H ^ 2) := by ring
      _ ≤ (54 * Cq) * ((CR ^ 2 * (Real.log X) ^ (-2 * rho293)) * (Real.log X) ^ (2 * theta293)) :=
          mul_le_mul_of_nonneg_left h1 h54
      _ = 54 * Cq * CR ^ 2
            * ((Real.log X) ^ (-2 * rho293) * (Real.log X) ^ (2 * theta293)) := by ring
  have hnum0 : (0 : ℝ)
      ≤ 54 * Cq * CR ^ 2 * ((Real.log X) ^ (-2 * rho293) * (Real.log X) ^ (2 * theta293)) :=
    mul_nonneg (mul_nonneg h54 (sq_nonneg CR)) (mul_nonneg (hLpow0 _) (hLpow0 _))
  have hform : ∀ a : ℝ, a / (Real.log X / 2) = 2 * a * (Real.log X)⁻¹ := fun a => by
    rw [div_div_eq_mul_div, div_eq_mul_inv]; ring
  have hZ : 54 * Cq * Rbar ^ 2 * H ^ 2 / (((⌊H * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) - 1)
      ≤ 108 * Cq * CR ^ 2 * ((Real.log X) ^ (-2 * rho293) * (Real.log X) ^ (2 * theta293)
          * (Real.log X)⁻¹) := by
    refine le_trans (div_le_div₀ hnum0 hnum (by linarith) hfloor) ?_
    exact le_of_eq (by rw [hform]; ring)
  have hZnn : (0 : ℝ) ≤ 54 * Cq * Rbar ^ 2 * H ^ 2
      / (((⌊H * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) - 1) :=
    div_nonneg (mul_nonneg (mul_nonneg h54 (sq_nonneg Rbar)) (sq_nonneg H)) hFpos.le
  have hterm2 : 4 * ((ramI H P Q).card : ℝ)
      * (54 * Cq * Rbar ^ 2 * H ^ 2 / (((⌊H * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) - 1))
      ≤ (1 / 2) * (Real.log X) ^ (-theta293) := by
    have hstep : 4 * ((ramI H P Q).card : ℝ)
        * (54 * Cq * Rbar ^ 2 * H ^ 2 / (((⌊H * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) - 1))
        ≤ (8 * (Real.log X) ^ (1 + theta293))
          * (108 * Cq * CR ^ 2 * ((Real.log X) ^ (-2 * rho293) * (Real.log X) ^ (2 * theta293)
              * (Real.log X)⁻¹)) :=
      mul_le_mul (by linarith) hZ hZnn (by positivity)
    have hcollapse : (8 * (Real.log X) ^ (1 + theta293))
          * (108 * Cq * CR ^ 2 * ((Real.log X) ^ (-2 * rho293) * (Real.log X) ^ (2 * theta293)
              * (Real.log X)⁻¹))
        = 864 * Cq * CR ^ 2 * (Real.log X) ^ (-3 * theta293) := by
      rw [← pin_pow_block hL0]; ring
    have hgate := mul_le_mul_of_nonneg_right hCqgate (hLpow0 (-3 * theta293))
    rw [pin_pow_split hL0] at hgate
    rw [hcollapse] at hstep
    linarith
  rw [balance_exponent_293']
  nlinarith [hterm1, hterm2]

/-- **P-a (iii) — THE REMAINDER LEG, PRICED** (`rem_priced`).  `USetBalance.hU_balance`'s
`hrem` binder from Lemma 12's error rows:

  `2E ≤ (Tann/X + 1)·(log X)^{−θ₂₉₃+ε}`.

`E` is fed by `RamareErr.lemma12_meansq_sharp`'s three-row split
(`RamareWindows.ramErr_moment_split`): the seam row at MR's own grade
`720(Tann/X+1)/H` (`ramWindowErr_moment_grade`), the `p²`-correction row `EP2`, and the
coprime tail — identically ZERO under the §8.3 support pin
(`ramCopTail_moment_zero`), which is why only two rows appear here.

At `H = H₈₃ = (log X)^θ` the seam row is `720(Tann/X+1)(log X)^{−θ}`; the absolute `720`
(and the `6` from `2·3`) is absorbed by the stated `o(1)` gate `8640 ≤ (log X)^ε` — the
`loglog_absorb` move of `USetPins`, at an explicit threshold rather than "`X` large". -/
theorem rem_priced (X Tann H ε EP2 E : ℝ) (hL1 : 1 ≤ Real.log X)
    (hX0 : 0 < X) (hTann0 : 0 ≤ Tann)
    (hH : (Real.log X) ^ theta293 ≤ H)
    (habs : 8640 ≤ (Real.log X) ^ ε)
    (hEP2 : 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε))
    (hE : E ≤ 3 * (720 * (Tann / X + 1) / H + EP2)) :
    2 * E ≤ (Tann / X + 1) * (Real.log X) ^ (-theta293 + ε) := by
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hpow : (0 : ℝ) < (Real.log X) ^ theta293 := Real.rpow_pos_of_pos hL0 _
  have hH0 : (0 : ℝ) < H := lt_of_lt_of_le hpow hH
  have hB0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293) := Real.rpow_nonneg hL0.le _
  have hA1 : (1 : ℝ) ≤ Tann / X + 1 := by
    have : (0 : ℝ) ≤ Tann / X := div_nonneg hTann0 hX0.le
    linarith
  have hinv : 1 / H ≤ (Real.log X) ^ (-theta293) := by
    have h1 : 1 / H ≤ 1 / (Real.log X) ^ theta293 := one_div_le_one_div_of_le hpow hH
    rw [Real.rpow_neg hL0.le, ← one_div]
    exact h1
  have hrow : 720 * (Tann / X + 1) / H ≤ 720 * (Tann / X + 1) * (Real.log X) ^ (-theta293) := by
    have hfac : (0 : ℝ) ≤ 720 * (Tann / X + 1) := by linarith
    have := mul_le_mul_of_nonneg_left hinv hfac
    calc 720 * (Tann / X + 1) / H = 720 * (Tann / X + 1) * (1 / H) := by
          rw [mul_one_div]
      _ ≤ 720 * (Tann / X + 1) * (Real.log X) ^ (-theta293) := this
  have hAB0 : (0 : ℝ) ≤ (Tann / X + 1) * (Real.log X) ^ (-theta293) :=
    mul_nonneg (by linarith) hB0
  have hbig : 8640 * ((Tann / X + 1) * (Real.log X) ^ (-theta293))
      ≤ (Tann / X + 1) * (Real.log X) ^ (-theta293) * (Real.log X) ^ ε := by
    have := mul_le_mul_of_nonneg_left habs hAB0
    linarith
  have hBle : (Real.log X) ^ (-theta293) ≤ (Tann / X + 1) * (Real.log X) ^ (-theta293) :=
    le_mul_of_one_le_left hB0 hA1
  -- ⟦R3c — THE ε-GRADED `EP₂` BUDGET⟧ the `p²` row is now priced at `(log X)^{−θ₂₉₃+ε}`,
  -- half an exponent of room for the coprime-tail mass; `(Tann/X + 1) ≥ 1` reabsorbs it
  have hE0 : (0 : ℝ) ≤ (Real.log X) ^ ε := Real.rpow_nonneg hL0.le _
  have hEP2' : 12 * EP2 ≤ (Real.log X) ^ (-theta293) * (Real.log X) ^ ε := by
    rwa [← Real.rpow_add hL0]
  have hBle' : (Real.log X) ^ (-theta293) * (Real.log X) ^ ε
      ≤ (Tann / X + 1) * ((Real.log X) ^ (-theta293) * (Real.log X) ^ ε) :=
    le_mul_of_one_le_left (mul_nonneg hB0 hE0) hA1
  rw [Real.rpow_add hL0]
  nlinarith [hE, hrow, hEP2', hbig, hBle, hBle', hAB0]

/-! ## §4 — P-d: `hU` FULLY PRICED (the row at the pins, all four slots discharged) -/

/-- **P-d — `hU` FULLY PRICED** (`hU_fully_priced`).  `USetBalance.hU_discharged` at the §8.3
pins `H := H₈₃ X θ₂₉₃`, `θ := θ₂₉₃`, `P ≥ P₈₃ X θ₂₉₃`, `Q ≤ Q₈₃ X`, with **all four grade
slots discharged**:

* `hKS` by §1 (`KS_supplied`) at `KS = 20512·δ'²(1 + log 2Tann)`;
* `hRbdU` by §2 (`Rbd_uniform`) at `R̄ = cofactorRbd cg Cb X θ₂₉₃ kmin Ymax (Dmax+1) Rrad`;
* `hmain` by §3 (`balance_priced_main`);
* `hrem` by §3 (`rem_priced`),

so that `USetBalance.hU_balance` collapses the two legs and the row reads

  `∫_{seamAnn} ‖spoly‖² ≤ 8S² + ∫_{(Ann∖ball)∩𝒯tot} ‖spoly‖²
      + 2(Tann/X + 1)(log X)^{−θ₂₉₃+ε}`,

which is `hU_balance_beats_door`'s input — the door's floor `c₀ ≥ 1/500` at margin `1.7067×`.

What remains a HYPOTHESIS, and why (law #253 — every one of these is in-statement, none is an
"`X` large enough"):

* `R̄ ≤ C_R·(log X)^{−ρ₂₉₃}` — U-7's own exit grade, at its own constant (see the module
  docstring);
* `1728·C_q·C_R² ≤ (log X)^{2θ}` and `32(log X)^{2+2θ}·KS ≤ (log X)^{−θ}` — the two block
  gates; the second is a gate on the LEVEL `δ'` (the ⟦V5e⟧ `ε²` absorption);
* `8640 ≤ (log X)^ε` — the `o(1)` absorption of Lemma 12's absolute constants;
* `E ≤ 3(720(Tann/X+1)/H + EP2)` and `12·EP2 ≤ (log X)^{−θ}` — Lemma 12's rows, the seam row
  at `RamareErr.ramWindowErr_moment_grade`'s grade and the `p²`-correction row at `EP2` (the
  coprime tail is identically zero under the §8.3 support pin);
* `kmin`, `Ymax`, `m₀` — the block-range data (worst corner and co-factor floor);
* `4 ≤ log X` and `2 ≤ H₈₃ X θ₂₉₃` — the floor page's and Lemma 12's own thresholds. -/
theorem hU_fully_priced :
    ∃ Cq cq T₀ X₀ C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
      ∀ (g fb a cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖fb n‖ ≤ 1) →
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X Tann t₁ δ δ' V L α η cg Cb Dmax Rrad kmin Ymax CR ε EP2 E S : ℝ),
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        1 < (Qseq Jb : ℝ) → Real.log (Qseq Jb) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        0 < δ → 1 ≤ Jb → Jb ≤ Jset → 1 ≤ V →
        V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ) → V⁻¹ ≤ δ' →
        3 ≤ Pseq Jb → (Qseq Jb : ℝ) ≤ Tann →
        Real.log V ≤ α * Real.log (Pseq Jb) → α ≤ 1 / 4 - η → 2 * η ≤ 1 →
        Real.log V ≤ 100 * Real.log L →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundle Tann V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        0 < cg → cg ≤ 1 / Real.exp 1 → 2 * cg < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 C → 0 < Rrad → Rrad ≤ seamRad X → Tann + |t₁| ≤ Dmax →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates cq X₀ (H83 X theta293) P N Xd Mt kk
          Tann L cg Cb X theta293 Dmax Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          ∀ k : ℕ, kk j ≤ k → k ≤ Mt j → |t| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ 3 * X) →
        1 < kmin → (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        cofactorRbd cg Cb X theta293 kmin Ymax (Dmax + 1) Rrad
            ≤ CR * (Real.log X) ^ (-rho293) →
        1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ seamTtot fb Pseq Qseq δ Jset,
                ‖spoly N a t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, hdis⟩ := hU_discharged
  refine ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, ?_⟩
  intro g fb a cf hg hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk
    X Tann t₁ δ δ' V L α η cg Cb Dmax Rrad kmin Ymax CR ε EP2 E S
    hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hδ0 hJb1 hJbJ hV1 hVinv hVδ hP3 hQT hVα hα hη2 hlogV hMs hbudget
    hm₀2 hm₀ hMs4 hc0 hce hc1 hCb0 hCbound hPlow hQ0 hQhigh hPQ ht₁ hrow hcoll hR0 hRrad
    hDmax hblk hbox hkmin hkk hMt hRgrade hCqgate hKSgate hε0 habs hEP2 hErow herr
    hXN hN2 hsupp hSup
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hH0 : (0 : ℝ) ≤ H83 X theta293 := by linarith
  have hHeq : H83 X theta293 = (Real.log X) ^ theta293 := by rw [H83]
  have hlog2T : (0 : ℝ) ≤ 1 + Real.log (2 * Tann) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * Tann by linarith)
    linarith
  have hKS0 : (0 : ℝ) ≤ 20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)) :=
    mul_nonneg (by positivity) hlog2T
  have hRbar0 : (0 : ℝ) ≤ cofactorRbd cg Cb X theta293 kmin Ymax (Dmax + 1) Rrad :=
    cofactorRbd_nonneg hc1 hCb0 (le_of_lt hkmin)
  have hDmax0 : (0 : ℝ) ≤ Dmax + 1 := by
    have := abs_nonneg t₁
    linarith
  -- the window top is at least `1` (from the block bundle's own co-factor endpoints)
  have hMt1 : ∀ j ∈ ramI (H83 X theta293) P Q, (1 : ℝ) ≤ ((Mt j : ℕ) : ℝ) := by
    intro j hj
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hbot, hlow, -, -, -, -, -, -⟩ := hblk j hj
    have hpos : (0 : ℝ) < ((Mt j : ℕ) : ℝ) := by linarith
    have hnat : 0 < Mt j := by exact_mod_cast hpos
    have hone : 1 ≤ Mt j := hnat
    exact_mod_cast hone
  -- §1: the `𝒯_S` slot
  have hKSb := KS_supplied (H83 X theta293) N Xd P Q g hg m₀ Ms Tann δ' (le_of_lt hT1)
    hm₀2 hm₀ hMs hMs4
  -- §2: the co-factor slot
  have hRb := Rbd_uniform (H83 X theta293) P Q Mt kk cg Cb X theta293 Dmax Rrad kmin Ymax
    hc0 hc1 hCb0 hkmin hDmax0 hkk hMt1 hMt
  -- the floor page
  have hfl := floor_pin X P hL4 hPlow
  -- the row, `hU` discharged at the two explicit budgets
  have hU := hdis g fb a cf hg hfb1 hcf1 (H83 X theta293) hH2 N Xd P Q Jset Jb Pseq Qseq
    Ms Mt kk X Tann t₁ δ δ' V L α η cg Cb theta293 Dmax Rrad
    (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)))
    (cofactorRbd cg Cb X theta293 kmin Ymax (Dmax + 1) Rrad) E S
    hX0 hXe hLXe hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hδ0 hJb1 hJbJ hV1 hVinv hVδ hP3 hQT hVα hα hη2 hlogV hMs hbudget
    hc0 hce hc1 hCb0 hCbound theta293_pos (le_of_lt theta293_lt_one_div_32) hPlow hQhigh
    hPQ ht₁ hrow hcoll hR0 hRrad hDmax hblk hbox hKSb hRb hfl.1 herr hXN hN2 hsupp hSup
  -- §3: the two balance binders
  have hmain := balance_priced_main X (H83 X theta293) Cq CR
    (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)))
    (cofactorRbd cg Cb X theta293 kmin Ymax (Dmax + 1) Rrad) P Q hL0 hH0
    (ramI_card_le_pin X P Q hQ0 hQhigh hLXe) (le_of_eq hHeq) hfl.2
    (le_of_lt hCq) hKS0 hRbar0 hRgrade hKSgate hCqgate
  have hrem := rem_priced X Tann (H83 X theta293) ε EP2 E hL1 hX0 (by linarith)
    (le_of_eq hHeq.symm) habs hEP2 hErow
  have hbal := hU_balance X Tann ε _ _ _ hε0 hL1 hX0 hTgate (le_refl _) hmain hrem
  linarith

/-- **The priced exit CLEARS THE DOOR, as a summand.**  `USetBalance.hU_balance_beats_door`
applied to the third summand of `hU_fully_priced`'s conclusion: at any `o(1)` with
`ε ≤ 1/1000` the `𝒰` term is `2(Tann/X+1)(log X)^{−1/500}`, the door's floor `c₀ ≥ 1/500`
(cleared with the ratified margin `1.7067×`, `CofactorDist.exit_margin_293`). -/
theorem priced_exit_beats_door (X Tann ε A B U : ℝ) (hε : ε ≤ 1 / 1000)
    (hL : 1 ≤ Real.log X) (hX0 : 0 < X) (hTgate : TannGate X Tann)
    (hU : U ≤ A + B + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε))) :
    U ≤ A + B + 2 * ((Tann / X + 1) * (Real.log X) ^ (-(1 : ℝ) / 500)) := by
  have h := hU_balance_beats_door X Tann ε
    (2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε))) hε hL hX0 hTgate (le_refl _)
  linarith

end Salt.MR
