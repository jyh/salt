/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.StridePairReceiptG12b
import Salt.MR.FlatDoorEpsRung2
import Mathlib

/-!
# ⟦TIER S — ROAD F, THE STRIDE AXIS: THE AFFINE DOOR AT EVERY STRIDE, TWIST AND GRADE (ARM Z)⟧
(`StrideDoorAllGrades`)

The graded lane's crown `mrtUniformityXiL2AffW_holds_flat_stride_g12b`
(`StridePairReceiptG12b.lean:1140`) is the affine `L²` MRT door at stride `a` and twist `h` under
THREE caps: `log (a·h) ≤ 9`, the ε-pin `ε = 1/(500·a·h)`, and the grade pinned at
`837782·2^12·(a·h)²`.  ARM Z states the same door with the three caps GONE — stride and twist FREE,
the grade a QUANTIFIER `∀ ρ > 0`, `ε` over its range `[1/(500·a·h), 1/500]` — as the statement of
record `StrideDoorAllGradesW`.

(a) THE HONEST LABEL.  This is a WIDER DOOR, not a step toward the crown: the regime is a flat one
above every floor `A₀`, in the corpus's `∀ A₀ ∃ Ra` shape, and NOT the crown's `∃ H₀ ∀ R`; nothing
here moves that quantifier.  Nothing here bears on twin primes.

(b) THE RULE.  The route is G12b's SHAPE at rung 2's CHARGE.  The six G12b forms
(`StridePairReceiptG12b.lean:47 · 71 · 111 · 212 · 238 · 271`) are re-cut by eight literal rules
into the `_Z` forms below (generated, then copied token for token from the road-F freeze of
ARM Z), and each G12b hop is RE-RUN at the charge `Lc := log c + L` (`1 ≤ c`, `0 ≤ L`, `log h ≤ L`,
`log a ≤ L`), calling rung 2's `_L`/`_T` suppliers at the TRUE `h` where G12b called its capped
twins at the pin, and new `_L` twins where none exists.

(c) WHAT IS OWED.  This file is HALF 1 of 3: the statement, the payload and the six forms; four
transcribed receipts and the Set-door monotonicity; the builder pair at the charge; the head at the
trivial payload; the shrink; the road-exit and capstone hops.  HALVES 2–3 (the conditional, kswin,
v7, the chain, the count floor, the affine assembly, the terminal, the zero levels, the
registration) are OWED, and the theorem `: StrideDoorAllGradesW` does NOT yet exist.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla

set_option exponentiation.threshold 4000

namespace Salt.MR

/-! ## §A — THE SIX FORMS AT THE CHARGE (generated; see the freeze §3 and `gen_z_forms.py`) -/

/-- **⟦FlatHeadFormHG_g12b AT THE CHARGE⟧ (def) — `FlatHeadFormHG_Z`.**
`FlatHeadFormHG_g12b` (StridePairReceiptG12b.lean:47) at rung 2's SUM charge `Lc := log c + L` by
the freeze's rules (a)–(h): ε a parameter; `2^539 ↦ 2^283·c^20·h`; the ε-pin kept and the charge pin
beside it; `838400·2^12·h² ↦ 838400·c`; the `A`-binder `10 + 2·Lc ≤ A`; the stride
`a ≤ 8103 ↦ log a ≤ L`; the riders at `50 + Lc`; the selector at `_T`. Nothing else moves. -/
def FlatHeadFormHG_Z (h : ℕ) (ε : ℚ) (c : ℕ) (L : ℝ) (Xi : XiFamily) (P : ChowlaRegime → Prop) :
    Prop :=
    ∃ (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 283 * (c : ℝ) ^ 20 * (h : ℝ) ∧ 0 < δ₀ ∧
      1 ≤ c ∧ 0 ≤ L ∧ Real.log (h : ℝ) ≤ L ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧
          (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 26 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * (Real.log (c : ℝ) + L) ≤ A →
        ∃ Hcap : ℕ,
          Hcap = max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (a extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → Real.log (a : ℝ) ≤ L →
            XCeilRiderAt (50 + (Real.log (c : ℝ) + L)) ε (fun Hhi ω => a * g Hhi ω) →
                ∃ R : ChowlaRegime,
            R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ a * g R.Hhi R.ω ≤ R.x ∧
            StrideScale a R ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((Xi R.eps H).card : ℝ) ≤ K) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            R.Hlo ≤ max Hcap (max extraFloor U1floor) ∧
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2Set Xi R ρ →
              P R

/-- **⟦FlatRoadExitFormHG_g12b AT THE CHARGE⟧ (def) — `FlatRoadExitFormHG_Z`.**
`FlatRoadExitFormHG_g12b` (StridePairReceiptG12b.lean:71) at rung 2's SUM charge `Lc := log c + L`
by the freeze's rules (a)–(h): ε a parameter; `2^539 ↦ 2^283·c^20·h`; the ε-pin kept and the charge
pin beside it; `838400·2^12·h² ↦ 838400·c`; the `A`-binder `10 + 2·Lc ≤ A`; the stride
`a ≤ 8103 ↦ log a ≤ L`; the riders at `50 + Lc`; the selector at `_T`. Nothing else moves. -/
def FlatRoadExitFormHG_Z (h : ℕ) (ε : ℚ) (c : ℕ) (L : ℝ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg : ℝ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 283 * (c : ℝ) ^ 20 * (h : ℝ) ∧ 0 < δ₀ ∧ 1 ≤ c ∧ 0 ≤ L ∧
          Real.log (h : ℝ) ≤ L ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧
      (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * (Real.log (c : ℝ) + L) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (a U1floor : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → Real.log (a : ℝ) ≤ L →
            XCeilRiderAt (50 + (Real.log (c : ℝ) + L)) ε (fun Hhi ω => a * g Hhi ω) →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ a * g R.Hhi R.ω ≤ R.x ∧
              StrideScale a R ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
                M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
                (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
                (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ((h : ℝ) * arcDen 12 H) ^ 7 ≤ RStr H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  44 * RSan H + 87 * ((h : ℝ) * arcDen 12 H) ≤ (4 / 3 : ℝ) ^ j₀) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  128 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  (h : ℝ) * arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
                      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                    ≤ Braw H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                M4ChiSummedFreeRowH_L_gk h K R M RS →
                  P R

/-- **⟦FlatCapstoneFormHG_g12b AT THE CHARGE⟧ (def) — `FlatCapstoneFormHG_Z`.**
`FlatCapstoneFormHG_g12b` (StridePairReceiptG12b.lean:111) at rung 2's SUM charge `Lc := log c + L`
by the freeze's rules (a)–(h): ε a parameter; `2^539 ↦ 2^283·c^20·h`; the ε-pin kept and the charge
pin beside it; `838400·2^12·h² ↦ 838400·c`; the `A`-binder `10 + 2·Lc ≤ A`; the stride
`a ≤ 8103 ↦ log a ≤ L`; the riders at `50 + Lc`; the selector at `_T`. Nothing else moves. -/
def FlatCapstoneFormHG_Z (h : ℕ) (ε : ℚ) (c : ℕ) (L : ℝ) (Awin : ℝ) (P : ChowlaRegime → Prop) :
    Prop :=
    ∃ (Cg : ℝ) (Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ 0 ≤ L ∧ Real.log (h : ℝ) ≤ L ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧
          (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      Kc ≤ 2 ^ 283 * (c : ℝ) ^ 20 * (h : ℝ) ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * (Real.log (c : ℝ) + L) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (a U1floor : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → Real.log (a : ℝ) ≤ L →
            XCeilRiderAt (50 + (Real.log (c : ℝ) + L)) ε (fun Hhi ω => a * g Hhi ω) →
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ a * g R.Hhi R.ω ≤ R.x ∧
              StrideScale a R ∧
                Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (M : ℕ), Mfl ≤ M → K ≤ 170000000 * M →
                  ∃ C' : ℝ, 0 < C' ∧
                    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                        ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                    ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                      -- ⟦A⟧ THE SPINE ARITHMETIC
                      M4DoorGates_L_gk K Cg R M k δ₀ →
                      8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        4 * Real.log (263 * (h : ℝ) * max 1 (arcDen 12 H))
                          ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        (h : ℝ) * arcDen 12 H
                          < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRhoH (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) h H)
                          (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                          (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                          5 ≤ Real.log (Real.log (2 * T)) →
                          (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                            ≤ 8 * (0 : ℝ) ^ 2
                              + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                    \ seamBall (((A + s : ℕ)) : ℝ) 0)
                                  ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                      (calP (AdoorL M) (s13GK K M))
                                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                      (mrAlpha (1 / 12)) 2,
                                  ‖spoly (2 * (A + s))
                                    (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                              + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                                  * (Real.log (((A + s : ℕ)) : ℝ))
                                      ^ (-theta293 + epsrf (A + s)))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        P R

/-- **⟦FlatConditionalFormHG_g12b AT THE CHARGE⟧ (def) — `FlatConditionalFormHG_Z`.**
`FlatConditionalFormHG_g12b` (StridePairReceiptG12b.lean:212) at rung 2's SUM charge
`Lc := log c + L` by the freeze's rules (a)–(h): ε a parameter; `2^539 ↦ 2^283·c^20·h`; the ε-pin
kept and the charge pin beside it; `838400·2^12·h² ↦ 838400·c`; the `A`-binder `10 + 2·Lc ≤ A`; the
stride `a ≤ 8103 ↦ log a ≤ L`; the riders at `50 + Lc`; the selector at `_T`. Nothing else moves. -/
def FlatConditionalFormHG_Z (h : ℕ) (ε : ℚ) (c : ℕ) (L : ℝ) (Awin : ℝ) (P : ChowlaRegime → Prop) :
    Prop :=
    ∃ (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ 0 ≤ L ∧ Real.log (h : ℝ) ≤ L ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧
          (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      Kc ≤ 2 ^ 283 * (c : ℝ) ^ 20 * (h : ℝ) ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * (Real.log (c : ℝ) + L) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (a U1floor : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → Real.log (a : ℝ) ≤ L →
              XCeilRiderStrictAt (50 + (Real.log (c : ℝ) + L)) ε g →
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ a * g R.Hhi R.ω ≤ R.x ∧
              StrideScale a R ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ M : ℕ, K ≤ 170000000 * M →
                S15Sel''_L_gk_T K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                S15CrossingBound_LH_gk h K R M → P R

/-- **⟦FlatKswinFormHG_g12b AT THE CHARGE⟧ (def) — `FlatKswinFormHG_Z`.**
`FlatKswinFormHG_g12b` (StridePairReceiptG12b.lean:238) at rung 2's SUM charge `Lc := log c + L` by
the freeze's rules (a)–(h): ε a parameter; `2^539 ↦ 2^283·c^20·h`; the ε-pin kept and the charge pin
beside it; `838400·2^12·h² ↦ 838400·c`; the `A`-binder `10 + 2·Lc ≤ A`; the stride
`a ≤ 8103 ↦ log a ≤ L`; the riders at `50 + Lc`; the selector at `_T`. Nothing else moves. -/
def FlatKswinFormHG_Z (h : ℕ) (ε : ℚ) (c : ℕ) (L : ℝ) (Awin : ℝ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ 0 ≤ L ∧ Real.log (h : ℝ) ≤ L ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧
          (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧
        ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
            10 + 2 * (Real.log (c : ℝ) + L) ≤ A →
          K ≤ 170000000 * flatDoorM A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          T₀ ≤ Real.exp (Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ) / 2) →
          Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 →
          ∀ (U1floor : ℕ), flatWitFloor ε β A Hopq ≤ U1floor →
            Real.log (Real.log ((U1floor : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 →
          ∀ (a : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → Real.log (a : ℝ) ≤ L →
              XCeilRiderStrictAt (50 + (Real.log (c : ℝ) + L)) ε g →
            ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = U1floor ∧ a * g R.Hhi R.ω ≤ R.x ∧ StrideScale a R ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            (S16CofactorSupply_LH_gk h K Cq R (flatDoorM A) →
              S16BaseScaleCap96_LH_gk h K R (flatDoorM A) →
                P R))

/-- **⟦V7RatedFormHG_g12b AT THE CHARGE⟧ (def) — `V7RatedFormHG_Z`.**
`V7RatedFormHG_g12b` (StridePairReceiptG12b.lean:271) at rung 2's SUM charge `Lc := log c + L` by
the freeze's rules (a)–(h): ε a parameter; `2^539 ↦ 2^283·c^20·h`; the ε-pin kept and the charge pin
beside it; `838400·2^12·h² ↦ 838400·c`; the `A`-binder `10 + 2·Lc ≤ A`; the stride
`a ≤ 8103 ↦ log a ≤ L`; the riders at `50 + Lc`; the selector at `_T`. Nothing else moves. -/
def V7RatedFormHG_Z (h : ℕ) (ε : ℚ) (c : ℕ) (L : ℝ) (P : ChowlaRegime → Prop) (A₀ : ℝ) : Prop :=
    ∃ (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧ Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ 0 ≤ L ∧ Real.log (h : ℝ) ≤ L ∧
          1 / (500 * (h : ℚ)) ≤ ε ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧
      (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      Mfl ≤ flatDoorM A ∧ 0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∀ (U1floor a : ℕ) (g : ℕ → ℕ → ℕ), flatDesignBase A ≤ U1floor →
        Real.log (Real.log ((U1floor : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 →
        1 ≤ a → Real.log (a : ℝ) ≤ L → XCeilRiderStrictAt (50 + (Real.log (c : ℝ) + L)) ε g →
      ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = U1floor ∧ a * g R.Hhi R.ω ≤ R.x ∧ StrideScale a R ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        P R

/-! ## §B — THE RECEIPT PAYLOAD AT A TARGET GRADE, AND THE STATEMENT OF RECORD -/

/-- **⟦THE RECEIPT PAYLOAD AT THE CHARGE⟧ (def) — `MRTDoorReceiptSetG_Z`.**  What the head+shrink
route hands the assembly through `P R`: the count at the form's ceiling and the Ξ-summed door at
the TARGET grade `ρt` (W-δ's shrink puts the grade here; G12b's receipt pinned it at
`837782·2^12·h²`).  The ε-pin equality is not carried: `R.eps = ε` is a conjunct of every form. -/
def MRTDoorReceiptSetG_Z (h : ℕ) (c : ℕ) (Xi : XiFamily) (ρt : ℝ) (R : ChowlaRegime) : Prop :=
  (∃ K : ℝ, 0 < K ∧ K ≤ 2 ^ 283 * (c : ℝ) ^ 20 * (h : ℝ) ∧
    ∀ (H : ℕ) [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ((Xi R.eps H).card : ℝ) ≤ K) ∧
  MRTUniformityXiL2Set Xi R ρt

/-- **ARM Z — THE AFFINE DOOR AT EVERY STRIDE, EVERY TWIST AND EVERY GRADE
(`StrideDoorAllGradesW`).** The graded lane's crown (`mrtUniformityXiL2AffW_holds_flat_stride_g12b`)
with its three caps gone: the stride `a` and the twist `h` are FREE (no `log (a·h) ≤ 9`), the grade
is a QUANTIFIER `∀ ρ > 0` (W-δ's move; no pin at `837782·2^12·(a·h)²`), and `ε` ranges over
`[1/(500·a·h), 1/500]` (G12b's pin `= 1/(500·a·h)` widened to its range). The regime is a FLAT one
above every floor `A₀` on the design constant, in the corpus's `∀ A₀ ∃ R` shape — NOT the crown's
`∃ H₀ ∀ R`; nothing here moves that quantifier. -/
def StrideDoorAllGradesW : Prop :=
  ∀ (a b h : ℕ), 0 < a → b < a → 0 < h →
    ∀ (ε : ℚ), (1 : ℚ) / (500 * ((a * h : ℕ) : ℚ)) ≤ ε → ε ≤ 1 / 500 →
    ∀ ρ : ℝ, 0 < ρ → ∀ A₀ : ℝ,
      ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧
        ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
          flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
          MRTUniformityXiL2AffW h Ra ρ


/-! ## §C — THE FOUR RECEIPTS -/

/-- **⟦THE NINTH ARM PAYS EVERY BINDER THE CHARGE ADDS⟧** (`zHead_A_pays`) — at `A := 162 + 2·Lc`
with `Lc ≥ 0`: the form's binder `10 + 2·Lc ≤ A`, the builder's gate `50 + Lc ≤ 3.2·A`, the rated
supply's floor `518 + 6·Lc ≤ 3.2·A`, and the base-scale cap's `Lc ≤ exp (3.2·A / 2)`.  ADDENDUM 2's
Z2, stated once at the form's `A`. -/
theorem zHead_A_pays {Lc : ℝ} (hLc0 : 0 ≤ Lc) :
    10 + 2 * Lc ≤ 162 + 2 * Lc ∧ 50 + Lc ≤ 3.2 * (162 + 2 * Lc) ∧
      518 + 6 * Lc ≤ 3.2 * (162 + 2 * Lc) ∧ Lc ≤ Real.exp (3.2 * (162 + 2 * Lc) / 2) := by
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  have h := Real.add_one_le_exp (3.2 * (162 + 2 * Lc) / 2)
  linarith

/-- **⟦THE FORM'S COUNT CEILING IS THE RIDER LEMMA'S `hKbL`⟧** (`zCount_form`) — from
`K ≤ 2^283·c^20·h` and `log h ≤ L`: `log K ≤ 197 + 20·(log c + L)`, i.e. the SUM charge pays the
count with `19·L` to spare (ADDENDUM 2's Z2, now from the form's own conjuncts). -/
theorem zCount_form {K : ℝ} {c h : ℕ} {L : ℝ} (hK0 : 0 < K)
    (hK : K ≤ 2 ^ 283 * (c : ℝ) ^ 20 * (h : ℝ)) (hc1 : 1 ≤ c) (hh : 0 < h)
    (hhL : Real.log (h : ℝ) ≤ L) (hL0 : 0 ≤ L) :
    Real.log K ≤ 197 + 20 * (Real.log (c : ℝ) + L) := by
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hpos : (0 : ℝ) < 2 ^ 283 * (c : ℝ) ^ 20 := by positivity
  have h1 := Real.log_le_log hK0 hK
  rw [Real.log_mul (ne_of_gt hpos) (ne_of_gt hhR)] at h1
  have h2 := epsRung2_log_Kb_le hc1
  linarith

/-- **Z3 — THE BUILDER'S CEILING ABSORBS `+L` WHERE IT ABSORBED `+9`.**  The landed step
(`StridePairReceipt.lean:2712–2715`) is `log H₊ + 9/(30·u) ≤ H₊` at `u ≥ 2`; at Z the reserved room
is `L ≤ log H₊` (from `L ≤ Lc ≤ loglog H₊ ≤ log H₊`), and `log H₊ ≤ H₊/10⁴ + 10⁴` pays it. -/
theorem zBuilder_absorb_L {Hhi : ℕ} (hH4 : 4000000 ≤ Hhi) {u L : ℝ} (hu2 : 2 ≤ u)
    (hL0 : 0 ≤ L) (hLH : L ≤ Real.log ((Hhi : ℕ) : ℝ)) :
    Real.log ((Hhi : ℕ) : ℝ) + L / (30 * u) ≤ ((Hhi : ℕ) : ℝ) := by
  have hHR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hH4
  have hlogH : Real.log ((Hhi : ℕ) : ℝ) ≤ ((Hhi : ℕ) : ℝ) / 10000 + 10000 := by
    have h1 : Real.log (((Hhi : ℕ) : ℝ) / 10000) ≤ ((Hhi : ℕ) : ℝ) / 10000 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (10000 : ℝ) ≤ 10000 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h3 : Real.log ((Hhi : ℕ) : ℝ) = Real.log (((Hhi : ℕ) : ℝ) / 10000) + Real.log 10000 := by
      rw [← Real.log_mul (by positivity) (by norm_num)]
      congr 1
      field_simp
    linarith
  have hu60 : (60 : ℝ) ≤ 30 * u := by linarith
  have hdiv : L / (30 * u) ≤ L / 60 := by
    apply div_le_div_of_nonneg_left hL0 (by norm_num) hu60
  linarith

/-- **⟦THE SET DOOR IS MONOTONE UP IN ITS GRADE⟧** (`mrtUniformityXiL2Set_mono`) — the Set-door
twin of `mrtUniformityXiL2_mono` (`FlatDoorEpsChain.lean:54`): `MRTUniformityXiL2Set Xi R ρ` is
`∀ H …, Σ … ≤ ρ` (`StridePair.lean:337`), so a door at `ρ` is a door at any `ρ' ≥ ρ`. -/
theorem mrtUniformityXiL2Set_mono {Xi : XiFamily} {R : ChowlaRegime} {ρ ρ' : ℝ}
    (hd : MRTUniformityXiL2Set Xi R ρ) (hle : ρ ≤ ρ') : MRTUniformityXiL2Set Xi R ρ' := by
  intro H _ hlo hhi
  exact le_trans (hd H hlo hhi) hle

end Salt.MR

end
