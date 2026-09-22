/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.StridePairReceiptG12b
import Salt.MR.FlatDoorEpsRung2
import Mathlib

-- Needed to transcribe the stride builder's ceiling step (`StridePairReceipt.lean:93` opens the
-- same line for the same body).  MEASURED, not assumed: `#check @xceil_flat_P` and
-- `#check @xceil_flat_step` both fail without this line (`Unknown identifier`).
open private xceil_flat_P xceil_flat_step from Salt.MR.XCeil
-- The door-head's cap shuffle, opened by `StridePairReceiptG12b.lean:28` for the same body.
-- MEASURED: `#check @flatCapH_shuffle` fails without this line (`Unknown identifier`).
open private flatCapH_shuffle from Salt.Entropy.Chowla.HloExportFlatH
-- The road-exit's cap join, opened by `StridePairReceiptG12b.lean:30` for the same body.
-- MEASURED: `#check @flatRootCapH_arc_k` fails without this line (`Unknown identifier`).
open private flatRootCapH_arc_k from Salt.MR.S16ComposeLH

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

/-! ## §D — THE BUILDER PAIR AT THE CHARGE -/

/-- **⟦THE STRIDE BUILDER AT THE CHARGE⟧** (`chowlaRegimeFlat_exists_param_gen_ceiling_mul_L`) —
`chowlaRegimeFlat_exists_param_gen_ceiling_mul_b9` (`StridePairReceipt.lean:2571`) with the stride's
numeral cap gone: (a) `hlogA : log a ≤ 9`, derived there from `a ≤ 8103`, is the BINDER
`haL : log a ≤ L`; (b) the `+ 9` absorbed into the ceiling is `+ L`, closed by `zBuilder_absorb_L`
where the landed proof closes `log H₊ + 9/(30u) ≤ H₊`, its room `L ≤ log H₊` derived from
`hLA : L ≤ 3.2·A` and the design floor (`3.2·A ≤ loglog H₋ ≤ log H₋ - 1 ≤ log H₊`). Every other step
is the source's, verbatim. -/
theorem chowlaRegimeFlat_exists_param_gen_ceiling_mul_L (a : ℕ) (ha : 1 ≤ a) {L : ℝ} (hL0 : 0 ≤ L)
    (haL : Real.log (a : ℝ) ≤ L) (A : ℝ) (hA : 26 ≤ A) (hLA : L ≤ 3.2 * A)
    (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      StrideScale a R.toChowlaRegime ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
  classical
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  -- the scale `m ≥ 1/ε`
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈(1 / eps : ℚ)⌉₊ := ⟨_, rfl⟩
  have hm_ge : (1 / eps : ℚ) ≤ (m : ℚ) := by rw [hmdef]; exact Nat.le_ceil _
  have hem : (1 : ℚ) ≤ eps * (m : ℚ) := by
    have h := mul_le_mul_of_nonneg_left hm_ge (le_of_lt heps)
    rwa [mul_one_div, div_self (ne_of_gt heps)] at h
  have hm1N : 1 ≤ m := by rw [hmdef]; exact Nat.ceil_pos.mpr (div_pos one_pos heps)
  have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm1N
  have hemR : (1 : ℝ) ≤ (eps : ℝ) * (m : ℝ) := by exact_mod_cast hem
  -- ⟦THE RE-BASED BASE⟧
  obtain ⟨Hlo, hHlodef⟩ : ∃ Hlo : ℕ,
      Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * m ^ 4)) := ⟨_, rfl⟩
  have hHloDF : flatDesignFloor A ≤ Hlo := by rw [hHlodef]; exact le_max_left _ _
  have hHlo_floor : 4000000 ≤ Hlo := le_trans (flatDesignFloor_house A) hHloDF
  have hHlo0 : Hlo₀ ≤ Hlo := by
    rw [hHlodef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hHlo4 : 4 * m ^ 4 ≤ Hlo := by
    rw [hHlodef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hHlo4Q : (4 : ℚ) * (m : ℚ) ^ 4 ≤ (Hlo : ℚ) := by exact_mod_cast hHlo4
  have hHlo4R : (4 : ℝ) * (m : ℝ) ^ 4 ≤ (Hlo : ℝ) := by exact_mod_cast hHlo4
  have hHlocap : Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) := by
    rw [hHlodef, hmdef]
  -- ⟦THE DESIGN LAW⟧ and the two floors it and `flatBase` supply
  have hflat : 3.2 * A ≤ Real.log (Real.log (Hlo : ℝ)) := flatDesignFloor_design hHloDF
  have hfl : 100 * (flatC A + Real.log (Real.log (Hlo : ℝ))) ≤ Real.log (Hlo : ℝ) :=
    flatFloor_of_design hA hHlo_floor hflat
  have h50 : (50 : ℝ) ≤ Real.log (Real.log (Hlo : ℝ)) := by linarith
  -- `hcoprime : 1 ≤ ε²·Hlo/2`
  have hcop : ((1 : ℕ) : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) / 2 := by
    have hprod : (1 : ℚ) ≤ (eps * (m : ℚ)) ^ 2 * (m : ℚ) ^ 2 := by
      have h1 : (1 : ℚ) ≤ (eps * (m : ℚ)) ^ 2 := by nlinarith [hem, sq_nonneg (eps * (m : ℚ) - 1)]
      have h2 : (1 : ℚ) ≤ (m : ℚ) ^ 2 := by nlinarith [hm1, sq_nonneg ((m : ℚ) - 1)]
      exact le_trans h1 (le_mul_of_one_le_right (sq_nonneg _) h2)
    have heq : (eps * (m : ℚ)) ^ 2 * (m : ℚ) ^ 2 = eps ^ 2 * (m : ℚ) ^ 4 := by ring
    have h4le : (4 : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) := by
      have hmul : eps ^ 2 * (4 * (m : ℚ) ^ 4) ≤ eps ^ 2 * (Hlo : ℚ) :=
        mul_le_mul_of_nonneg_left hHlo4Q (sq_nonneg eps)
      nlinarith [hmul, hprod, heq]
    rw [Nat.cast_one]; linarith
  -- `hPNTwindow : √Hlo ≤ ε²·Hlo/2`
  have hPNT : Real.sqrt (Hlo : ℝ) ≤ (eps : ℝ) ^ 2 * (Hlo : ℝ) / 2 := by
    have hsqrtHlo : (2 : ℝ) * (m : ℝ) ^ 2 ≤ Real.sqrt (Hlo : ℝ) := by
      have heq : Real.sqrt (4 * (m : ℝ) ^ 4) = 2 * (m : ℝ) ^ 2 := by
        rw [show (4 : ℝ) * (m : ℝ) ^ 4 = (2 * (m : ℝ) ^ 2) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
      calc (2 : ℝ) * (m : ℝ) ^ 2 = Real.sqrt (4 * (m : ℝ) ^ 4) := heq.symm
        _ ≤ Real.sqrt (Hlo : ℝ) := Real.sqrt_le_sqrt hHlo4R
    have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (Hlo : ℝ) := Real.sqrt_nonneg _
    have hHloeq : Real.sqrt (Hlo : ℝ) * Real.sqrt (Hlo : ℝ) = (Hlo : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have h2 : (2 : ℝ) ≤ (eps : ℝ) ^ 2 * Real.sqrt (Hlo : ℝ) := by
      have hstep : (eps : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2) ≤ (eps : ℝ) ^ 2 * Real.sqrt (Hlo : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrtHlo (sq_nonneg _)
      nlinarith [hstep, hemR, sq_nonneg ((eps : ℝ) * (m : ℝ) - 1)]
    have h3 : 2 * Real.sqrt (Hlo : ℝ) ≤ (eps : ℝ) ^ 2 * (Hlo : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right h2 hsqrtnn
      rw [mul_assoc, hHloeq] at hh
      linarith [hh]
    linarith [h3]
  -- ⟦THE TWO TOWERS⟧ at their minimal crossings, and the endpoint that hosts both
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = towerJmin 2 1 Hlo := ⟨_, rfl⟩
  obtain ⟨Jf, hJfdef⟩ : ∃ Jf : ℕ, Jf = towerFlatJmin A 1 Hlo := ⟨_, rfl⟩
  have hJ : Real.log 2 < towerDropSum 2 1 Hlo J := by
    rw [hJdef]; exact towerJmin_spec hHlo_floor
  have hJf : Real.log 2 < towerDropSumFlat A 1 Hlo Jf := by
    rw [hJfdef]; exact towerFlatJmin_spec hA1 hHlo_floor hfl
  obtain ⟨Hhi, hHhidef⟩ : ∃ Hhi : ℕ,
      Hhi = max (chowlaTower 2 1 Hlo J) (chowlaTowerFlat A 1 Hlo Jf) := ⟨_, rfl⟩
  have hfitL : chowlaTower 2 1 Hlo J ≤ Hhi := by rw [hHhidef]; exact le_max_left _ _
  have hfitFl : chowlaTowerFlat A 1 Hlo Jf ≤ Hhi := by rw [hHhidef]; exact le_max_right _ _
  have hHlohi : Hlo ≤ Hhi := le_trans (chowlaTower_base_ge hHlo_floor J) hfitL
  have hHhi_floor : 4000000 ≤ Hhi := le_trans hHlo_floor hHlohi
  -- ⟦THE WIDTH EXPORT⟧ at the flat shape, on both arms of the endpoint
  have hwidth : Real.log (Real.log (Hhi : ℝ))
      ≤ Real.exp (Real.log (Real.log (Hlo : ℝ)) / 2) := by
    rw [hHhidef, hJdef, hJfdef]
    rcases le_total (chowlaTower 2 1 Hlo (towerJmin 2 1 Hlo))
        (chowlaTowerFlat A 1 Hlo (towerFlatJmin A 1 Hlo)) with h | h
    · rw [max_eq_right h]
      exact towerFlat_width_export hA hHlo_floor hflat
    · rw [max_eq_left h]
      exact le_trans (tower_loglog_le_45 hHlo_floor h50) (pow_nine_halves_le_exp_half h50)
  -- the outer scale at this `ε` and endpoint, WITH THE CEILING
  obtain ⟨x, ω, hx2, hω2, hωx, hhead, hhead', hPH, homega, hxb, hxceil⟩ :=
    regime_outer_param_ceiling eps heps heps1 Hhi (4 ^ ⌊eps ^ 2 * (Hhi : ℚ)⌋₊) hHhi_floor
  -- ⟦THE CEILING AT THE BUILDER'S OWN `P`⟧
  have h2q : (2 : ℚ) * eps ≤ 1 := by linarith
  have h2r : (2 : ℝ) * (eps : ℝ) ≤ 1 := by exact_mod_cast h2q
  have hepsHalf : (eps : ℝ) ≤ 1 / 2 := by linarith
  have hHhiR : (4000000 : ℝ) ≤ (Hhi : ℝ) := by exact_mod_cast hHhi_floor
  have hHhipos : (0 : ℝ) < (Hhi : ℝ) := by linarith
  -- ⟦THE MULTIPLIER⟧ `log a ≤ L`, the binder (no numeral cap on `a`)
  have hapos : 0 < a := ha
  have haR0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
  have hlogA : Real.log ((a : ℕ) : ℝ) ≤ L := haL
  -- ⟦THE RESERVED ROOM⟧ `L ≤ 3.2·A ≤ loglog H₋ ≤ log H₋ - 1 ≤ log H₊` (the parametric head's
  -- `hll` chain, one `log y ≤ y - 1` further)
  have hLH : L ≤ Real.log ((Hhi : ℕ) : ℝ) := by
    have hHloR : (4000000 : ℝ) ≤ ((Hlo : ℕ) : ℝ) := by exact_mod_cast hHlo_floor
    have hlogpos : (0 : ℝ) < Real.log ((Hlo : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hll_le : Real.log (Real.log ((Hlo : ℕ) : ℝ)) ≤ Real.log ((Hlo : ℕ) : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hlogpos
    have hmono : Real.log ((Hlo : ℕ) : ℝ) ≤ Real.log ((Hhi : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      exact_mod_cast hHlohi
    linarith
  -- ⟦THE CEILING AT `a·x`⟧ the landed collapse with the `+ L` absorbed into `l`
  have hxceil' : Real.log (((a * x : ℕ)) : ℝ) ≤ 31 / (eps : ℝ) * (Hhi : ℝ) := by
    obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = 1 / (eps : ℝ) := ⟨_, rfl⟩
    have hu2 : (2 : ℝ) ≤ u := by rw [hudef, le_div_iff₀ hepsR]; linarith
    have hupos : (0 : ℝ) < u := by linarith
    have hbr30 : (30 : ℝ) / (eps : ℝ) * Real.log (Hhi : ℝ)
        = 30 * (u * Real.log (Hhi : ℝ)) := by rw [hudef]; ring
    have hbr31 : (31 : ℝ) / (eps : ℝ) * (Hhi : ℝ) = 31 * (u * (Hhi : ℝ)) := by
      rw [hudef]; ring
    have hx0R : (0 : ℝ) < ((x : ℕ) : ℝ) := by
      have hx2R : (2 : ℝ) ≤ ((x : ℕ) : ℝ) := by exact_mod_cast hx2
      linarith
    have hsplit : Real.log (((a * x : ℕ)) : ℝ)
        = Real.log ((a : ℕ) : ℝ) + Real.log ((x : ℕ) : ℝ) := by
      push_cast
      exact Real.log_mul (by positivity) (by positivity)
    have hxu : Real.log (((a * x : ℕ)) : ℝ)
        ≤ 30 * (u * (Real.log (Hhi : ℝ) + L / (30 * u)))
          + 2 * Real.log (((4 ^ ⌊eps ^ 2 * (Hhi : ℚ)⌋₊ : ℕ) : ℝ) + 1) := by
      have hcancel : 30 * (u * (Real.log (Hhi : ℝ) + L / (30 * u)))
          = 30 * (u * Real.log (Hhi : ℝ)) + L := by
        field_simp
      rw [hsplit, hcancel]
      linarith [hxceil, hbr30, hlogA]
    have hPterm := xceil_flat_P heps hepsHalf hepsR hHhiR
    have hlogself : Real.log (Hhi : ℝ) + L / (30 * u) ≤ (Hhi : ℝ) :=
      zBuilder_absorb_L hHhi_floor hu2 hL0 hLH
    have hfin := xceil_flat_step hu2 hHhiR hlogself hxu hPterm
    linarith [hfin, hbr31]
  have hxle : x ≤ a * x := Nat.le_mul_of_pos_left x hapos
  have hdivc : (a * x) / a = x := Nat.mul_div_cancel_left x hapos
  refine ⟨regimeFlatEnlargeX
      { x := x, ω := ω, a := 1, eps := eps, Hlo := Hlo, Hhi := Hhi, C0 := 2, J := J,
        hx := hx2, hω := hω2, hωx := hωx, ha := le_refl 1, heps := heps, heps1 := heps1,
        hHlo := le_trans (by norm_num) hHlo_floor, hHlohi := hHlohi, hC0 := le_refl 2,
        hHlo_floor := hHlo_floor, hheadroom := hhead, hcoprime := hcop, hfit := hfitL,
        hJcon := hJ, hheadroom' := hhead', hPHheadroom := hPH, hPNTwindow := hPNT,
        hωbig := homega, hxbig := hxb,
        A := A, hA := hA, hflat := hflat, Jf := Jf,
        hfitF := by simpa using hfitFl, hJconF := by simpa using hJf } hxle,
    rfl, rfl, hHlo0, ?_, hHlocap, hwidth, ?_⟩
  · refine ⟨dvd_mul_right a x, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_omega, regimeFlatEnlargeX_Hhi,
        regimeFlatEnlargeX_eps, hdivc]
    · exact hx2
    · exact hωx
    · exact hhead
    · exact hhead'
    · exact hPH
    · exact hxb
  · simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_Hhi]
    exact hxceil'

/-- **⟦THE STRIDE HEAD BUILDER AT THE CHARGE, ON THE PARAMETRIC RIDER⟧**
(`chowlaRegimeFlat_exists_param_head_xceil_mul_at_L`) —
`chowlaRegimeFlat_exists_param_head_xceil_mul_b9` (`StridePairReceipt.lean:2749`) on
`chowlaRegimeFlat_exists_param_gen_ceiling_mul_L`, with the rider at the parametric floor `lam0` as
rung 2's `chowlaRegimeFlat_exists_param_head_xceil_at` (`FlatDoorEpsRung2.lean:2900`) carries it:
the `loglog` floor is `hll : lam0 ≤ loglog H₊`, proved from `hlamA : lam0 ≤ 3.2·A` and the design
law exactly as there, read at the gate, and EXPORTED as the last conjunct. `hLlam : L ≤ lam0` pays
the builder's `L ≤ 3.2·A`. Every other step is the source's, verbatim. -/
theorem chowlaRegimeFlat_exists_param_head_xceil_mul_at_L (a : ℕ) (ha : 1 ≤ a) {L : ℝ}
    (hL0 : 0 ≤ L) (haL : Real.log (a : ℝ) ≤ L) (lam0 A : ℝ) (hA : 26 ≤ A)
    (hlamA : lam0 ≤ 3.2 * A) (hLlam : L ≤ lam0)
    (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ)
    (g : ℕ → ℕ → ℕ) (hg : XCeilRiderAt lam0 eps (fun Hhi ω => a * g Hhi ω)) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      a * g R.Hhi R.ω ≤ R.x ∧ StrideScale a R.toChowlaRegime ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
      lam0 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) := by
  obtain ⟨R, hReps, hRA, hRHlo, hstride, hRcap, hRwid, hRx⟩ :=
    chowlaRegimeFlat_exists_param_gen_ceiling_mul_L a ha hL0 haL A hA (by linarith) eps heps
      heps1 Hlo₀
  have hapos : 0 < a := ha
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  -- ⟦THE ENDPOINT FLOOR⟧
  have hHhi4 : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
  have hHhiR : (4000000 : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast hHhi4
  have hHlo4 : (4000000 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast R.hHlo_floor
  -- ⟦THE `loglog` FLOOR AT THE PARAMETER⟧ off `lam0 ≤ 3.2·A = 3.2·R.A ≤ loglog H₋`
  have hll : lam0 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) := by
    have hflat : 3.2 * R.A ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) := R.hflat
    rw [hRA] at hflat
    have hlogpos : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
      Real.log_pos (by linarith)
    have hmono : Real.log ((R.Hlo : ℕ) : ℝ) ≤ Real.log ((R.Hhi : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      exact_mod_cast R.hHlohi
    have := Real.log_le_log hlogpos hmono
    linarith
  -- ⟦THE WIDTH WINDOW⟧ the majorant field read against the ceiling
  have hωgate : Real.log ((R.ω : ℕ) : ℝ) + (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ)
      ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    set P : ℕ := 4 ^ ⌊R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)⌋₊ with hPdef
    set n : ℕ := ⌊R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)⌋₊ with hndef
    have hPH : 8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ) ≤ ((R.x : ℕ) : ℝ) := R.hPHheadroom
    have hP1 : (1 : ℝ) ≤ ((P : ℕ) : ℝ) := by
      rw [hPdef]
      have : (1 : ℕ) ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
      exact_mod_cast this
    have hω1 : (1 : ℝ) ≤ ((R.ω : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ R.ω := le_trans (by norm_num) R.hω
      exact_mod_cast this
    -- `log 8 + 2·log P + log ω ≤ log x`
    have hpos : (0 : ℝ) < 8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ) := by positivity
    have hlogle : Real.log (8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ))
        ≤ Real.log ((R.x : ℕ) : ℝ) := Real.log_le_log hpos hPH
    have hsplit : Real.log (8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ))
        = Real.log 8 + 2 * Real.log ((P : ℕ) : ℝ) + Real.log ((R.ω : ℕ) : ℝ) := by
      rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow]
      push_cast
      ring
    -- `log P = n·log 4 ≥ (ε²H₊ − 1)·log 4`
    have hlogP : Real.log ((P : ℕ) : ℝ) = (n : ℝ) * Real.log 4 := by
      rw [hPdef]
      have h4 : ((4 ^ n : ℕ) : ℝ) = (4 : ℝ) ^ n := by push_cast; ring
      rw [h4, Real.log_pow]
    have hnge : (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) - 1 ≤ (n : ℝ) := by
      have hQ : R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ) < (n : ℚ) + 1 := by
        rw [hndef]; exact Nat.lt_floor_add_one _
      have hR : (R.eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) < (n : ℝ) + 1 := by exact_mod_cast hQ
      rw [hReps] at hR
      linarith
    have hlog4 : (1.3862 : ℝ) ≤ Real.log 4 := by
      have h : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      rw [h]; linarith [Real.log_two_gt_d9]
    have hlog8 : (2.0794 : ℝ) ≤ Real.log 8 := by
      have h : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      rw [h]; linarith [Real.log_two_gt_d9]
    -- ⟦THE COPRIMALITY FLOOR⟧ `ε²·H₊ ≥ 2`
    have hcop : (2 : ℝ) ≤ (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) := by
      have hQ : ((R.a : ℕ) : ℚ) ≤ R.eps ^ 2 * ((R.Hlo : ℕ) : ℚ) / 2 := R.hcoprime
      have ha1 : (1 : ℚ) ≤ ((R.a : ℕ) : ℚ) := by exact_mod_cast R.ha
      have hQ2 : (2 : ℚ) ≤ R.eps ^ 2 * ((R.Hlo : ℕ) : ℚ) := by linarith
      have hR2 : (2 : ℝ) ≤ (R.eps : ℝ) ^ 2 * ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast hQ2
      rw [hReps] at hR2
      have hmono : (eps : ℝ) ^ 2 * ((R.Hlo : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast R.hHlohi) (sq_nonneg _)
      linarith
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith [hlogle, hsplit, hlogP, hnge, hlog4, hlog8, hRx, hcop, hnn]
  have hgx : Real.log (((a * g R.Hhi R.ω : ℕ)) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) :=
    hg R.Hhi R.ω ⟨hHhi4, hll, hωgate⟩
  -- ⟦THE PUSH⟧ the scale to `a * max (R.x / a) (g R.Hhi R.ω)`
  have hxa : a * (R.x / a) = R.x := Nat.mul_div_cancel' hstride.1
  have hxle : R.x ≤ a * max (R.x / a) (g R.Hhi R.ω) := by
    calc R.x = a * (R.x / a) := hxa.symm
      _ ≤ a * max (R.x / a) (g R.Hhi R.ω) := Nat.mul_le_mul_left a (le_max_left _ _)
  have hdivc : (a * max (R.x / a) (g R.Hhi R.ω)) / a = max (R.x / a) (g R.Hhi R.ω) :=
    Nat.mul_div_cancel_left _ hapos
  have hmle : R.x / a ≤ max (R.x / a) (g R.Hhi R.ω) := le_max_left _ _
  have hmleR : ((R.x / a : ℕ) : ℝ) ≤ ((max (R.x / a) (g R.Hhi R.ω) : ℕ) : ℝ) := by
    exact_mod_cast hmle
  have hmdiv : R.x / a / R.ω ≤ max (R.x / a) (g R.Hhi R.ω) / R.ω :=
    Nat.div_le_div_right hmle
  have hmdivR : ((R.x / a / R.ω : ℕ) : ℝ)
      ≤ ((max (R.x / a) (g R.Hhi R.ω) / R.ω : ℕ) : ℝ) := by exact_mod_cast hmdiv
  refine ⟨regimeFlatEnlargeX R hxle, hReps, hRA, hRHlo, ?_, ?_, hRcap, hRwid, ?_, ?_⟩
  · simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_omega, regimeFlatEnlargeX_Hhi]
    exact Nat.mul_le_mul_left a (le_max_right _ _)
  · refine ⟨dvd_mul_right _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_omega, regimeFlatEnlargeX_Hhi,
        regimeFlatEnlargeX_eps, hdivc]
    · exact le_trans hstride.2.1 hmle
    · exact le_trans hstride.2.2.1 hmle
    · exact le_trans hstride.2.2.2.1 hmdiv
    · exact le_trans hstride.2.2.2.2.1 hmdivR
    · exact le_trans hstride.2.2.2.2.2.1 hmleR
    · exact le_trans hstride.2.2.2.2.2.2 hmleR
  · simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_Hhi]
    rcases le_total (R.x / a) (g R.Hhi R.ω) with hc | hc
    · rw [max_eq_right hc]; exact hgx
    · rw [max_eq_left hc, hxa]; exact hRx
  · simp only [regimeFlatEnlargeX_Hhi]
    exact hll

/-! ## §E — THE HEAD AT THE TRIVIAL PAYLOAD, AND THE SHRINK -/

/-- **⟦THE DOOR-HEAD AT THE CHARGE⟧** (`flat_door_head_xceil_h_Z`) — G12b's
`flat_door_head_xceil_h_g12b` (`StridePairReceiptG12b.lean:936`) at the charge and at the TRIVIAL
payload `fun _ => True`: (a) the count `2^539 ↦ 2^283·c^20·h` is `hcount`'s, read at `Xi ε`; the
ε-pin `1/(500h) ≤ ε` is the binder `hεh`, with the charge pin `hcε` beside it; the grade pin
`1/(838400·c) ≤ δ₀` is proved from `hcε` exactly as rung 2's head proves its pin
(`FlatDoorEpsRung2.lean`, `flat_head_uniform_xceil_epsW`: `δ₀ := ε/(256·(1 + 4·log 4))`,
`838400·c·ε ≥ 1676.8` against `256·(1 + 8·log 2) ≤ 1675.5654262784`); (b) the form's conjuncts
`1 ≤ c ∧ 0 ≤ L ∧ log h ≤ L` are the binders; (c) the form's `A`-binder `10 + 2·Lc ≤ A` pays the
builder's `50 + Lc ≤ 3.2·A` (`≤ 45 + A/2` at `A ≥ 26`) and `log c ≥ 0` pays `L ≤ 50 + Lc`; (d) the
builder is `chowlaRegimeFlat_exists_param_head_xceil_mul_at_L` at `lam0 := 50 + Lc`; (e) the
payload apparatus is DROPPED — G12b's `hδ₀le` (the receipt's `837782·2^12·h²` ceiling) and the
`h`-positivity facts that served its `h`-carrying mint have no role (measured by a `clear`-probe),
and the twist positivity `0 < h` is read by nothing, so it is bound as `_hh`.  The tower, cap and
count conjuncts are G12b's. -/
theorem flat_door_head_xceil_h_Z (h : ℕ) (_hh : 0 < h) (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
    (hεh : (1 : ℚ) / (500 * (h : ℚ)) ≤ ε) {c : ℕ} (hc1 : 1 ≤ c)
    (hcε : (1 : ℚ) / (500 * (c : ℚ)) ≤ ε) {L : ℝ} (hL0 : 0 ≤ L) (hhL : Real.log (h : ℝ) ≤ L)
    (Xi : XiFamily)
    (hcount : ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 283 * (c : ℝ) ^ 20 * (h : ℝ) ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧
      ∀ (H : ℕ) [NeZero H], H₀ ≤ H → ((Xi ε H).card : ℝ) ≤ C) :
    FlatHeadFormHG_Z h ε c L Xi (fun _ => True) := by
  classical
  unfold FlatHeadFormHG_Z
  -- ⟦THE LEAF NUMERALS, PINNED⟧ `log 4 = 2·log 2`, the upper `d9` bound on `log 2`
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  obtain ⟨cD3, hcD3def⟩ : ∃ c : ℝ, c = 1 / 4 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ c : ℝ, c = 1 + 2 * (2 * Real.log 4) := ⟨_, rfl⟩
  have hcD3 : 0 < cD3 := by rw [hcD3def]; norm_num
  have hC : 0 < C := by rw [hCdef]; positivity
  -- ⟦THE `ε` BOUNDS⟧ off `ε ≤ 1/500`
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  have hεQ1 : ε ≤ 1 / 2 := by
    have h2 : (1 : ℚ) / 500 ≤ 1 / 2 := by norm_num
    linarith
  -- ⟦THE MINT⟧ the head's `δ₀` at the pinned witnesses is rung 2's term, exactly
  have hmint : cD3 / (16 * C) * (ε : ℝ) / 4 = (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) := by
    rw [hcD3def, hCdef]
    have hne : (1 : ℝ) + 2 * (2 * Real.log 4) ≠ 0 := by positivity
    field_simp
    ring
  -- ⟦THE MINT AGAINST THE PIN, AT THE CHARGE⟧ rung 2's `hqcap`/`hcapR`/`hδnum`: `1 ≤ 500·c·ε`
  -- gives `838400·c·ε ≥ 1676.8`, against the mint's denominator
  -- `256·(1 + 8·log 2) ≤ 256 · 6.5451774464 = 1675.5654262784`
  have hcQ : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcQ0 : (0 : ℚ) < 500 * (c : ℚ) := by linarith
  have hqcap : (1 : ℚ) ≤ 500 * (c : ℚ) * ε := by
    rw [div_le_iff₀ hcQ0] at hcε; linarith
  have hcapR : (1 : ℝ) ≤ 500 * (c : ℝ) * (ε : ℝ) := by exact_mod_cast hqcap
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hδnum : (1 : ℝ) / (838400 * (c : ℝ)) ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    rw [hmint, div_le_div_iff₀ (by linarith) (by positivity), hlog4eq]
    linarith
  -- ⟦THE COUNT HOOK AT THE CHARGE⟧ carrying `K ≤ 2^283·c^20·h`
  obtain ⟨K, hK, hKb, H₀xi, _hH₀xi2, hxi⟩ := hcount
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = cD3 * (ε : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hcD3 hεR0) (by positivity)
  -- ⟦THE HEAD'S OWN FLOOR⟧ the count hook's alone — the door-head has no tail
  obtain ⟨Hopq, hOpqdef⟩ : ∃ n : ℕ, n = H₀xi := ⟨_, rfl⟩
  refine ⟨K, cD3 / (16 * C) * (ε : ℝ) / 4, β, Hopq, hε0, hK, hKb,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num),
    hc1, hL0, hhL, hεh, hcε, hδnum, hβpos, ?_⟩
  -- ⟦THE HOIST⟧ as in the head; the charge's `A`-binder pays the builder's floor
  intro A hA26 _hAge hAL
  have hlogc : 0 ≤ Real.log (c : ℝ) := Real.log_nonneg hcR1
  -- ⟦THE TOWER FLOOR⟧ `50 + Lc ≤ 45 + A/2 ≤ 3.2·A` at `A ≥ 26`
  have hlamA : 50 + (Real.log (c : ℝ) + L) ≤ 3.2 * A := by linarith
  have hLlam : L ≤ 50 + (Real.log (c : ℝ) + L) := by linarith
  obtain ⟨F, hFdef⟩ : ∃ n : ℕ, n = max Hopq (budgetFloorFlat (ε : ℝ) β A) := ⟨_, rfl⟩
  refine ⟨max (flatDesignFloor A) (max F (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), by rw [hFdef], ?_⟩
  intro a extraFloor U1floor g₅ ha haL hg₅
  obtain ⟨Rf, hReps, _hRA, hRHlo, hRg, hstride, _hRcapEq, hRwid, hRx, _hll⟩ :=
    chowlaRegimeFlat_exists_param_head_xceil_mul_at_L a ha hL0 haL (50 + (Real.log (c : ℝ) + L))
      A hA26 hlamA hLlam ε hε0 hεQ1 (max F (max extraFloor U1floor)) g₅ hg₅
  have hFlo : F ≤ Rf.Hlo := le_trans (le_max_left _ _) hRHlo
  have hxiHlo : H₀xi ≤ Rf.Hlo := by
    rw [hFdef, hOpqdef] at hFlo
    exact le_trans (le_max_left _ _) hFlo
  -- ⟦THE COUNT GATE⟧ at this head's own `ε`
  have hcountR : ∀ (H' : ℕ) [NeZero H'], Rf.Hlo ≤ H' → H' ≤ Rf.Hhi →
      ((Xi Rf.eps H').card : ℝ) ≤ K := by
    intro H' _ hlo' _
    rw [hReps]
    exact hxi H' (le_trans hxiHlo hlo')
  refine ⟨Rf.toChowlaRegime, hReps,
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, hstride, hRx,
    hcountR, fun _ => hRwid, ?_, fun _ _ _ _ => trivial⟩
  -- ⟦THE CAP⟧ the flat base equation, shuffled onto the consumer's floors
  rw [_hRcapEq]
  exact flatCapH_shuffle _ _ _ _ _

/-- **⟦THE THRESHOLD SHRINK, ON THE Z HEAD FORM⟧** (`flatHeadFormHG_Z_at_grade`) — W-δ's
`flatHeadFormEpsW_at_grade` (`FlatDoorAllGrades.lean:89`) on `FlatHeadFormHG_Z`: the form reads its
threshold `δ₀` at exactly three conjuncts (`0 < δ₀`, the pin `1/(838400·c) ≤ δ₀`, the final arrow),
so any Z head at the charge `c` is a Z head whose threshold is ANY `ρt` on the pin, with the
receipt `MRTDoorReceiptSetG_Z h c Xi ρt` as its payload: the count is the tuple's own `K` with the
regime's count conjunct, and the door at `ρt` is `mrtUniformityXiL2Set_mono`.  The old payload `Q`
is dropped. -/
theorem flatHeadFormHG_Z_at_grade {h : ℕ} {ε : ℚ} {c : ℕ} {L : ℝ} {Xi : XiFamily}
    {Q : ChowlaRegime → Prop} (hd : FlatHeadFormHG_Z h ε c L Xi Q) {ρt : ℝ} (hρt : 0 < ρt)
    (hpin : (1 : ℝ) / (838400 * (c : ℝ)) ≤ ρt) :
    FlatHeadFormHG_Z h ε c L Xi (MRTDoorReceiptSetG_Z h c Xi ρt) := by
  unfold FlatHeadFormHG_Z at hd ⊢
  obtain ⟨K, δ₀, β, Hopq, hε, hK, hKb, -, hc1, hL0, hhL, hεh, hcε, -, hβ, hbody⟩ := hd
  refine ⟨K, ρt, β, Hopq, hε, hK, hKb, hρt, hc1, hL0, hhL, hεh, hcε, hpin, hβ, ?_⟩
  intro A hA hbud hcA
  obtain ⟨Hcap, hHcap, hR⟩ := hbody A hA hbud hcA
  refine ⟨Hcap, hHcap, ?_⟩
  intro a extraFloor U1floor g ha haL hg
  obtain ⟨R, hReps, hef, hU1, hRg, hstride, hRx, hcount, htow, hcap, -⟩ :=
    hR a extraFloor U1floor g ha haL hg
  exact ⟨R, hReps, hef, hU1, hRg, hstride, hRx, hcount, htow, hcap,
    fun ρ _ hle hdoor => ⟨⟨K, hK, hKb, hcount⟩, mrtUniformityXiL2Set_mono hdoor hle⟩⟩

/-! ## §F — THE ROAD-EXIT HOP AT THE CHARGE, AND THE CONDITIONAL'S `j`-FLOOR LIFT

The capstone hop (`flat_capstone_generic_h_Z`) and the stride-arm split lift
(`xceil_arm_split_mul_h_L`) are NOT in this file: the capstone reads the twist cap `log h ≤ 14` at
two suppliers (`m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling_kwide_14`,
`arc36_of_regime_h_14`) that have no charge-form twin, and the split's landed statement is FALSE
at a free twist (its right side `H₊·(1/(250000·h²) − 10⁻²⁰)` is negative once `h > 2·10⁷`).
Both are recorded in `docs/blueprints/flags.md`. -/

/-- **⟦H0→H1 AT THE CHARGE⟧** (`flat_roadExit_generic_h_Z`) — G12b's
`flat_roadExit_generic_h_g12b` (`StridePairReceiptG12b.lean:320`) on the Z forms: the head's five
charge conjuncts (`1 ≤ c`, `0 ≤ L`, `log h ≤ L`, the ε-pin, the charge pin) are passed through the
tuple, the `A`-application gains the charge binder `hAL`, and the stride bound is
`haL : log a ≤ L` where G12b has `a ≤ 8103`.  The road `m4_second_road_L2_Set_gk_flatRoot_L_khoist`
is called exactly as G12b calls it (it carries no cap).  No cap is read here. -/
theorem flat_roadExit_generic_h_Z (h : ℕ) (hh : 0 < h) (ε : ℚ) (c : ℕ) (L : ℝ) (Xi : XiFamily)
    (harcXi : ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
      ∀ ξ ∈ Xi eps H, NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (P : ChowlaRegime → Prop) (hhead : FlatHeadFormHG_Z h ε c L Xi P) :
    FlatRoadExitFormHG_Z h ε c L P := by
  obtain ⟨Cg, hCg, hCgle, hreg⟩ := m4_second_road_L2_Set_gk_flatRoot_L_khoist h hh Xi harcXi
  obtain ⟨Kb, δ₀, β, Hopq, hε, hKb, hKbb, hδ₀, hc1, hL0, hhL, hεpin, hcε, hδpin, hβ, hhd0⟩ :=
    hhead
  obtain ⟨H₀, hH₀⟩ := hreg ε hε
  refine ⟨Cg, Kb, δ₀, β, max Hopq H₀, hCg, hCgle, hε, hKb, hKbb, hδ₀, hc1, hL0, hhL, hεpin, hcε,
    hδpin, hβ, ?_⟩
  intro K A hA162 hAge hAL
  obtain ⟨Hcap, hCapEq, hhd⟩ := hhd0 A (by linarith) hAge hAL
  refine ⟨max Hcap H₀, by rw [hCapEq]; exact flatRootCapH_arc_k _ _ _ _ _, ?_⟩
  intro a U1floor g ha haL hg
  obtain ⟨R, hReps, hRextra, hRU1, hRg, hstride, hRx, hcount, hRtow, hRcap, hR⟩ :=
    hhd a H₀ U1floor g ha haL hg
  refine ⟨R, hReps, hRU1, hRg, hstride, hRx, hRtow, le_trans hRcap (by omega), ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  have hdoor := hH₀ K R hReps hRextra δ Bceil Kb RS RSan RStr Braw M k j₀ hgates hM hRSan0
    hRStr0 hBraw0 han hG1 hG2 harc3 hdgate hdrift hceil hcount hKb.le hrow
  refine hR δ₀ hδ₀ le_rfl ?_
  intro H _ hlo hhi
  exact le_trans (hdoor H hlo hhi) hbudget

/-- **⟦THE `j`-FLOOR AT THE CHARGE⟧** (`s13_g2_jfloor_of_MSelect'_L_gk_h_L`) —
`s13_g2_jfloor_of_MSelect'_L_gk_h_b9` (`S16FlatTerminalLinear.lean:2574`) at `hhL : log h ≤ L`:
the hypothesis carries the twist as `4·log h ≤ 4·L`, so `h1`'s `+ 36 = 4·9` is `+ 4·L`.  BODY:
the source's, with `L` for `9`. -/
theorem s13_g2_jfloor_of_MSelect'_L_gk_h_L {h : ℕ} (hh : 0 < h) {L : ℝ}
    (hhL : Real.log (h : ℝ) ≤ L)
    {R : ChowlaRegime} {F : ℝ}
    (h1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * max 1 (arcDen 12 H)) + 4 * L ≤ F) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * (h : ℝ) * max 1 (arcDen 12 H)) ≤ F := by
  intro H hlo hhi
  have hx0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hmax : (1 : ℝ) ≤ max 1 (arcDen 12 H) := le_max_left _ _
  have hsplit : Real.log (263 * (h : ℝ) * max 1 (arcDen 12 H))
      = Real.log (263 * max 1 (arcDen 12 H)) + Real.log (h : ℝ) := by
    rw [show (263 : ℝ) * (h : ℝ) * max 1 (arcDen 12 H)
        = (263 * max 1 (arcDen 12 H)) * (h : ℝ) by ring,
      Real.log_mul (by positivity) (ne_of_gt hx0)]
  rw [hsplit]
  linarith [h1 H hlo hhi, hhL]

end Salt.MR

end
