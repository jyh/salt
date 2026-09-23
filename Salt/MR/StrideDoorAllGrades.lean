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
-- The stride transport's trivial window bound, opened by `StridePair.lean:58` for the same body
-- (`mrtUniformityXiL2AffW_of_set_L`, §O).  MEASURED: without this line that body fails with
-- `Unknown identifier norm_windowExpSum_trivial`.
open private norm_windowExpSum_trivial from Salt.Entropy.Chowla.MRTDoor

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

(c) WHAT IS OWED.  HALF 1 landed the statement, the payload and the six forms; four transcribed
receipts and the Set-door monotonicity; the builder pair at the charge; the head at the trivial
payload; the shrink; the road-exit and capstone hops.  HALF 2 landed the conditional (§J) and v7
(§K) with ten of the eleven charge twins of the H-socket suppliers (§I).  HALF 2b landed the
crossing closure (§L–§M) and the kswin hop (§N).  HALF 3 landed the chain, the count floor, the
stride lifts, the charge and E-beating lemmas, the terminal and zero level B (§O–§R); the theorem
`: StrideDoorAllGradesW` EXISTS (`strideDoorAllGradesW_holds`).  OWED: registration (this commit's
successor); zero level A, HELD at the guard (§R).
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
the freeze's rules (a)–(i): ε a parameter; `2^539 ↦ 2^283·c^20·h`; the ε-pin kept and the charge pin
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
by the freeze's rules (a)–(i): ε a parameter; `2^539 ↦ 2^283·c^20·h`; the ε-pin kept and the charge
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
by the freeze's rules (a)–(i): ε a parameter; `2^539 ↦ 2^283·c^20·h`; the ε-pin kept and the charge
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
`Lc := log c + L` by the freeze's rules (a)–(i): ε a parameter; `2^539 ↦ 2^283·c^20·h`; the ε-pin
kept and the charge pin beside it; `838400·2^12·h² ↦ 838400·c`; the `A`-binder `10 + 2·Lc ≤ A`; the
stride `a ≤ 8103 ↦ log a ≤ L`; the riders at `50 + Lc`; the selector at `_T`. Nothing else moves.
Rule (i), v1.1: the floor binder reads `flatDesignBase A` where G12b read `arcFloor36`. -/
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
            max Hcap (max (flatDesignBase A) loglogFloor50) ≤ U1floor →
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
the freeze's rules (a)–(i): ε a parameter; `2^539 ↦ 2^283·c^20·h`; the ε-pin kept and the charge pin
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
the freeze's rules (a)–(i): ε a parameter; `2^539 ↦ 2^283·c^20·h`; the ε-pin kept and the charge pin
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

The capstone hop (`flat_capstone_generic_h_Z`) is in §H, on the design floor, with the charge
twins of its two cap-read suppliers in §G.  The stride-arm split lift (`xceil_arm_split_mul_h_L`)
is NOT in this file: the split's landed statement is FALSE at a free twist (its right side
`H₊·(1/(250000·h²) − 10⁻²⁰)` is negative once `h > 2·10⁷`); it is recorded in
`docs/blueprints/flags.md`. -/

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

/-! ## §G — THE SEVEN CHARGE TWINS OF THE CAPSTONE'S `_14` CHAIN, AT THE TOWER FLOOR

G12b's capstone reads the twist cap `log h ≤ 14` at two suppliers, and both are FALSE at a free
twist over the fixed floor `50 ≤ loglog H`: the room for `h` is `(log H)²` against
`h·(1 + 13·loglog H)²`.  Each twin below is its `_14` source with the cap binder replaced by the
charge `{Lc} (0 ≤ Lc) (log h ≤ Lc)` and the fixed floor replaced by the TOWER floor
`50 + Lc ≤ loglog H` (on a regime: at every `H ∈ [R.Hlo, R.Hhi]`).  The exponent `14` in
`exp (14·loglog H)` is a BUDGET, not the cap, and stays.  The capstone (§H) supplies the tower
floor from the design floor `flatDesignFloor A` (the road-F freeze of ARM Z, cell 14). -/

/-- **⟦THE `H`-SIDE PRICE AT THE CHARGE⟧** (`hArcDen_mul_strataResidualH_sq_le_L`) —
`hArcDen_mul_strataResidualH_sq_le_14` at `log h ≤ Lc` and the tower floor `50 + Lc ≤ Λ`,
`Λ := loglog H`.  THE ROOM, exact in the exponent: `h ≤ e^{Λ-50}` (from `log h ≤ Lc ≤ Λ − 50`),
`arcDen 12 H = e^{12Λ}`, and `strataResidualH h H = 1 + 12Λ + log h ≤ 1 + 13Λ ≤ e^{Λ/2+25}`
(`26 ≤ e^{25}` and `Λ/2 + 1 ≤ e^{Λ/2}`, so `e^{Λ/2+25} ≥ 26·(Λ/2+1) = 13Λ + 26`); then
`e^{Λ-50}·e^{12Λ}·e^{Λ+50} = e^{14Λ}`.  This is `(1 + 13Λ)² ≤ e^{Λ+50}`, true at every
`Λ ≥ 50` (at `Λ = 50`: `651² = 423,801` against `e^{50} = 5.18·10^{21}`).  The source's device
(`Real.add_one_le_exp`, a split exponential) is kept; only its split point moves. -/
theorem hArcDen_mul_strataResidualH_sq_le_L {h H : ℕ} (hh : 0 < h) {Lc : ℝ} (hLc0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    (hL0 : 0 ≤ Real.log (H : ℝ)) (hlam : 50 + Lc ≤ Real.log (Real.log (H : ℝ))) :
    (h : ℝ) * arcDen 12 H * strataResidualH h H ^ 2
      ≤ Real.exp (14 * Real.log (Real.log (H : ℝ))) := by
  set L : ℝ := Real.log (Real.log (H : ℝ)) with hLdef
  have hlam50 : 50 ≤ L := by linarith
  have hL1 : 1 < Real.log (H : ℝ) := one_lt_log_of_loglog_ge hL0 (by norm_num) hlam50
  have hL : 0 < Real.log (H : ℝ) := by linarith
  have harc : arcDen 12 H = Real.exp (12 * L) := by
    rw [arcDen, Real.rpow_def_of_pos hL, ← hLdef]
    congr 1
    ring
  have hsH : strataResidualH h H = strataResidual H + Real.log (h : ℝ) :=
    strataResidualH_eq hh hL
  have hstr : strataResidual H = 1 + 12 * L := strataResidual_eq_of_pos hL
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hhle : (h : ℝ) ≤ Real.exp (L - 50) := by
    rw [← Real.exp_log hh0]
    exact Real.exp_le_exp.mpr (by linarith)
  have hlogh0 : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  -- the residual bound: `1 + 12L + log h ≤ 1 + 13L ≤ 26·(L/2 + 1) ≤ e^{25}·e^{L/2}`
  have he25 : (26 : ℝ) ≤ Real.exp 25 := by
    have := Real.add_one_le_exp (25 : ℝ)
    linarith
  have hlin : L / 2 + 1 ≤ Real.exp (L / 2) := Real.add_one_le_exp _
  have hsplit : Real.exp (L / 2 + 25) = Real.exp 25 * Real.exp (L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : (26 : ℝ) * (L / 2 + 1) ≤ Real.exp 25 * Real.exp (L / 2) :=
    mul_le_mul he25 hlin (by linarith) (Real.exp_pos 25).le
  have hres : strataResidualH h H ≤ Real.exp (L / 2 + 25) := by
    rw [hsH, hstr, hsplit]
    linarith
  have hres0 : 0 ≤ strataResidualH h H := by rw [hsH, hstr]; linarith
  have hsq : strataResidualH h H ^ 2 ≤ Real.exp (L / 2 + 25) ^ 2 :=
    pow_le_pow_left₀ hres0 hres 2
  have hE : Real.exp (L - 50) * Real.exp (12 * L) * (Real.exp (L / 2 + 25) ^ 2)
      = Real.exp (14 * L) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have harc0 : (0 : ℝ) ≤ arcDen 12 H := arcDen_nonneg 12 H
  have hsq0 : (0 : ℝ) ≤ strataResidualH h H ^ 2 := sq_nonneg _
  calc (h : ℝ) * arcDen 12 H * strataResidualH h H ^ 2
      ≤ Real.exp (L - 50) * arcDen 12 H * strataResidualH h H ^ 2 := by
        gcongr
    _ = Real.exp (L - 50) * Real.exp (12 * L) * strataResidualH h H ^ 2 := by rw [harc]
    _ ≤ Real.exp (L - 50) * Real.exp (12 * L) * (Real.exp (L / 2 + 25) ^ 2) := by
        gcongr
    _ = Real.exp (14 * L) := hE

/-- `a2DoorGrade_pool_L_priced_rhoH_14` at the charge (`a2DoorGrade_pool_L_priced_rhoH_L`).
SUPPLIER-SWAP: the `H`-side price is `hArcDen_mul_strataResidualH_sq_le_L`, fed the tower floor
`hHL : 50 + Lc ≤ loglog H`; the budget and the five summand prices are cap-blind.  BODY: the
source's. -/
theorem a2DoorGrade_pool_L_priced_rhoH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {M H j : ℕ} {X C₁ M₀ K ρ π₀ : ℝ}
    (hfr : DoorArithFrameRho_L M H j X C₁ M₀ K ρ)
    (hHL : 50 + Lc ≤ Real.log (Real.log (H : ℝ))) (hpool : 0 ≤ π₀)
    (hprice : 188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2) :
    (h : ℝ) * arcDen 12 H * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
      ≤ RSanDoorRhoH ρ h H := by
  have hLX : 1 < Real.log X := hfr.one_lt_logX
  have hLrho : 0 ≤ Real.log (1 / ρ) := hfr.logInvRho_nonneg
  have hstrpos : (0 : ℝ) < strataResidualH h H := by
    have := one_le_strataResidualH (one_le_hArcDen_of_loglog hh hfr.logH_nonneg hfr.Hfloor)
    linarith
  have hgrade0 : (0 : ℝ) ≤ a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
    refine a2DoorGrade_pool_L_nonneg hfr.Mpos (by linarith) ?_ hpool
    have : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    push_cast
    exact this
  have hwt := hArcDen_mul_strataResidualH_sq_le_L hh hL0 hhL hfr.logH_nonneg hHL
  rw [RSanDoorRhoH, le_div_iff₀ (pow_pos hstrpos 2)]
  have hkey : (h : ℝ) * arcDen 12 H * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
        * strataResidualH h H ^ 2
      ≤ Real.exp (14 * Real.log (Real.log (H : ℝ)))
          * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
    have hid : (h : ℝ) * arcDen 12 H * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
          * strataResidualH h H ^ 2
        = ((h : ℝ) * arcDen 12 H * strataResidualH h H ^ 2)
            * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right hwt hgrade0
  refine le_trans hkey ?_
  have h1 := doorGrade_summand1_priced_rho (H := H) hfr.rho_pos hfr.C1_nonneg hfr.logX_nonneg
    hLX hfr.M0_window
  have h2 := doorGrade_summand2_priced_rho_L (H := H) hfr.rho_pos hfr.Mpos hfr.anchor
  have h3 := doorGrade_summand3_priced_rho_pool (H := H) hprice
  have h4 := doorGrade_summand4_priced_rho (H := H) hfr.rho_pos hLrho hLX hfr.Hfloor
    hfr.armWeak
  have h5 := doorGrade_summand5_priced_rho (H := H) (j := j) hfr.rho_pos hLrho hfr.Hfloor
    hfr.jfloor
  rw [a2DoorGrade_pool_L]
  ring_nf
  ring_nf at h1 h2 h3 h4 h5
  linarith

/-- `a2DoorGrade_pool_L_priced_rhoH_gk_14` at the charge (`a2DoorGrade_pool_L_priced_rhoH_gk_L`),
at the lever (`a2Level1_L` is K-invariant).  SUPPLIER-SWAP; BODY: the source's. -/
theorem a2DoorGrade_pool_L_priced_rhoH_gk_L (K : ℕ) {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {M H j : ℕ} {X C₁ M₀ Kar ρ π₀ : ℝ}
    (hfr : DoorArithFrameRho_L M H j X C₁ M₀ Kar ρ)
    (hHL : 50 + Lc ≤ Real.log (Real.log (H : ℝ))) (hpool : 0 ≤ π₀)
    (hprice : 188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2) :
    (h : ℝ) * arcDen 12 H * a2DoorGrade_pool_L_gk K M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
      ≤ RSanDoorRhoH ρ h H := by
  have heq : a2DoorGrade_pool_L_gk K M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
      = a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := rfl
  rw [heq]
  exact a2DoorGrade_pool_L_priced_rhoH_L hh hL0 hhL hfr hHL hpool hprice

/-- `m4_arith_henv_rho_poolH_L_gk_14` at the charge (`m4_arith_henv_rho_poolH_L_gk_L`).  The
tower floor is a regime binder `hfloor`, read at the socket's `R.Hlo ≤ H ≤ R.Hhi`
(`hb.1`, `hb.2.1`).  SUPPLIER-SWAP; BODY: the source's. -/
theorem m4_arith_henv_rho_poolH_L_gk_L (K : ℕ) {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M : ℕ} {C₁ M₀ π₀ : ℕ → ℝ} {Kar ρ : ℝ}
    (hfloor : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 50 + Lc ≤ Real.log (Real.log (H : ℝ)))
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (harith : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ)
    (hprice : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      188133 * π₀ (A + s) * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2) :
    ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      (h : ℝ) * arcDen 12 H
          * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
        ≤ RSanDoorRhoH ρ h H :=
  fun H L q j A s hb =>
    a2DoorGrade_pool_L_priced_rhoH_gk_L K hh hL0 hhL (harith H L q j A s hb)
      (hfloor H hb.1 hb.2.1) (hpool (A + s)) (hprice H L q j A s hb)

/-- **⟦THE ARITHMETIC GATE AT THE CONSTANT POOL, AT THE CHARGE⟧**
(`m4_arith_henv_constPoolH_L_gk_L`) — `m4_arith_henv_constPoolH_L_gk_14` at `log h ≤ Lc` and the
regime tower floor `hfloor`.  The price wrapper `price_at_constPool_socketH_L` is cap-blind.
SUPPLIER-SWAP; BODY: the source's. -/
theorem m4_arith_henv_constPoolH_L_gk_L (K : ℕ) {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {Kar ρ : ℝ}
    (hfloor : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 50 + Lc ≤ Real.log (Real.log (H : ℝ)))
    (hρ : 0 ≤ ρ)
    (harith : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) :
    ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      (h : ℝ) * arcDen 12 H
          * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
              (M₀ (A + s)) (constPool ρ R.Hhi)
        ≤ RSanDoorRhoH ρ h H :=
  m4_arith_henv_rho_poolH_L_gk_L K hh hL0 hhL (π₀ := fun _ => constPool ρ R.Hhi) hfloor
    (fun _ => constPool_nonneg hρ) harith (price_at_constPool_socketH_L harith)

set_option maxHeartbeats 1000000 in
-- the landed fuse's own budget: sixteen socket-framed hypotheses re-elaborate here too
/-- ⟦WIDE CEILING TWIN, AT THE CHARGE⟧
(`m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling_kwide_L`) — the `_14` fuse at `log h ≤ Lc`.
The chain's ONE cap read is the arithmetic gate, now `m4_arith_henv_constPoolH_L_gk_L`; it reads
the regime tower floor, which this twin takes as ONE new inner binder, placed first after the
`∀ (R …) (t₁ …)` binder block (before `1 ≤ M`):
`∀ H, R.Hlo ≤ H → H ≤ R.Hhi → 50 + Lc ≤ loglog H`.  The slot and the assembly take no cap binder.
BODY: the source's. -/
theorem m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling_kwide_L (h : ℕ) (hh : 0 < h)
    {Lc : ℝ} (hL0 : 0 ≤ Lc) (hhL : Real.log (h : ℝ) ≤ Lc) (K : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kc ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 50 + Lc ≤ Real.log (Real.log (H : ℝ))) →
        1 ≤ M → K ≤ 170000000 * M → 0 < ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) →
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          GRowsZeroGate'''_L_gk K M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
            ≤ (theta293 - ε (A + s)) * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kc ρ) →
        M4ChiSummedFreeRowH_L_gk h K R M
          (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) := by
  obtain ⟨Ct, hCt, hCtb, hslot⟩ := m4_hrowsSlot_at_door_zero'H_L_gk_ceiling_kwide h K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro Cp hCp R M C₁ M₀ ε Kc ρ cU bU t₁ hfloor hM hKw hρ hb1 hc1 hbf hgP1 hgRows hthr _heps293
    hband4096 hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_gatedH_L_gk h K (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := fun _ => constPool ρ R.Hhi)
    (RSbig := fun _ H => RSanDoorRhoH ρ h H) hM ?_
    (hslot Cp hCp R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap) hband
    (fun _ => constPool_nonneg hρ.le)
    (m4_arith_henv_constPoolH_L_gk_L K hh hL0 hhL hfloor hρ.le harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_pos_L_gk K (hbf H L q j A s hb)
    (hgP1 H L q j A s hb) (hgRows H L q j A s hb) hρ (hthr H L q j A s hb) hM hXd
    (hband4096 H L q j A s hb)

/-- **⟦gate 7 AT THE CHARGE, IN REGIME FORM⟧** (`arc36_of_regime_h_L`) — `arc36_of_regime_h_14`
at `log h ≤ Lc` and the regime tower floor `hfloor` (in place of `loglogFloor50 ≤ R.Hlo`).  The
conclusion is the source's byte for byte; the ROUTE is direct in logarithms, since the source's
`h ≤ 1202604` is a numeral cap.  THE ROOM, `Λ := loglog H`: `h ≤ e^{Λ-50}` and
`arcDen 12 H = e^{12Λ}`, so `128·(h·arcDen 12 H)³ ≤ e^5·e^{39Λ-150} = e^{39Λ-145}`
(`128 ≤ 2.7⁵ = 143.49 < e^5`), against `H = e^{e^Λ}`; and `39Λ − 145 ≤ e^Λ` from
`e^Λ = e^{50}·e^{Λ-50} ≥ 2000·(Λ − 49)` (`2000 ≤ 2.7^{50} = 3.70·10^{21}`), whose excess over
`39Λ − 145` is `1961·Λ − 97855 ≥ 195` at `Λ ≥ 50`.  No `open private` is needed. -/
theorem arc36_of_regime_h_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (_hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime}
    (hfloor : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 50 + Lc ≤ Real.log (Real.log (H : ℝ))) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ) := by
  intro H hlo hhi
  have hΛ := hfloor H hlo hhi
  set L : ℝ := Real.log (Real.log (H : ℝ)) with hLdef
  have hL0H : 0 ≤ Real.log (H : ℝ) := Real.log_natCast_nonneg H
  have hL1 : 1 < Real.log (H : ℝ) :=
    one_lt_log_of_loglog_ge hL0H (by norm_num : (0 : ℝ) < 50) (by linarith)
  have hL : 0 < Real.log (H : ℝ) := by linarith
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · subst h0
      simp at hL1
      linarith
    · exact_mod_cast h0
  have harc : arcDen 12 H = Real.exp (12 * L) := by
    rw [arcDen, Real.rpow_def_of_pos hL, ← hLdef]
    congr 1
    ring
  have hx0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hhle : (h : ℝ) ≤ Real.exp (L - 50) := by
    rw [← Real.exp_log hx0]
    exact Real.exp_le_exp.mpr (by linarith)
  have hprod : (h : ℝ) * arcDen 12 H ≤ Real.exp (13 * L - 50) := by
    rw [harc]
    calc (h : ℝ) * Real.exp (12 * L) ≤ Real.exp (L - 50) * Real.exp (12 * L) :=
          mul_le_mul_of_nonneg_right hhle (Real.exp_pos _).le
      _ = Real.exp (13 * L - 50) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have hprod0 : (0 : ℝ) ≤ (h : ℝ) * arcDen 12 H := mul_nonneg hx0.le (arcDen_nonneg 12 H)
  have hcube : ((h : ℝ) * arcDen 12 H) ^ 3 ≤ Real.exp (39 * L - 150) := by
    have hc := pow_le_pow_left₀ hprod0 hprod 3
    have he : Real.exp (13 * L - 50) ^ 3 = Real.exp (39 * L - 150) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [he] at hc
    exact hc
  have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h128 : (128 : ℝ) ≤ Real.exp 5 := by
    have h5 : Real.exp 5 = (Real.exp 1) ^ (5 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hp : (2.7 : ℝ) ^ (5 : ℕ) ≤ (Real.exp 1) ^ (5 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he1.le 5
    have hn : (128 : ℝ) ≤ (2.7 : ℝ) ^ (5 : ℕ) := by norm_num
    rw [h5]; linarith
  have h2000 : (2000 : ℝ) ≤ Real.exp 50 := by
    have h50 : Real.exp 50 = (Real.exp 1) ^ (50 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hp : (2.7 : ℝ) ^ (50 : ℕ) ≤ (Real.exp 1) ^ (50 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he1.le 50
    have hn : (2000 : ℝ) ≤ (2.7 : ℝ) ^ (50 : ℕ) := by norm_num
    rw [h50]; linarith
  have hkey : 39 * L - 145 ≤ Real.exp L := by
    have hlin : (L - 50) + 1 ≤ Real.exp (L - 50) := Real.add_one_le_exp _
    have hsplit : Real.exp L = Real.exp 50 * Real.exp (L - 50) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hm : (2000 : ℝ) * (L - 49) ≤ Real.exp 50 * Real.exp (L - 50) :=
      mul_le_mul h2000 (by linarith) (by linarith) (Real.exp_pos 50).le
    rw [hsplit]
    linarith
  have hHexp : (H : ℝ) = Real.exp (Real.exp L) := by
    rw [hLdef, Real.exp_log hL, Real.exp_log hHpos]
  calc 128 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ Real.exp 5 * Real.exp (39 * L - 150) :=
        mul_le_mul h128 hcube (pow_nonneg hprod0 3) (Real.exp_pos 5).le
    _ = Real.exp (39 * L - 145) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (Real.exp L) := Real.exp_le_exp.mpr hkey
    _ = (H : ℝ) := hHexp.symm

/-! ## §H — THE CAPSTONE AT THE CHARGE, ON THE DESIGN FLOOR (the freeze's cell 14) -/

/-- **⟦H1→H2 AT THE CHARGE, ON THE DESIGN FLOOR⟧ — `flat_capstone_generic_h_Z`.** G12b's
`flat_capstone_generic_h_g12b` (`StridePairReceiptG12b.lean:351`) on the Z forms.  `hh14` is
DELETED: the road tuple's charge conjuncts are passed through, and `Lc := log c + L` carries the
twist (`log h ≤ L ≤ log c + L`).  THE FLOOR IS ROUTED: where G12b routes `arcFloor36` and
`loglogFloor50`, the capstone routes `flatDesignFloor A` into the cap (`max Hcap
(flatDesignFloor A)`) and into the road's `U1floor` slot, so `flatDesignBase A ≤ R.Hlo` gives
`3.2·A ≤ loglog H` on the window and, with `162 ≤ A` and `10 + 2·Lc ≤ A`
(`50 + Lc ≤ 45 + A/2 ≤ 3.2·A` once `A ≥ 16.7`), the TOWER floor `50 + Lc ≤ loglog H`.  The two
cap-read suppliers are their `_L` twins (§G) at that floor; everything else is the source's. -/
theorem flat_capstone_generic_h_Z (h : ℕ) (hh : 0 < h) (ε : ℚ) (c : ℕ) (L : ℝ)
    (Awin : ℝ) (hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hroad : FlatRoadExitFormHG_Z h ε c L P) :
    FlatCapstoneFormHG_Z h ε c L Awin P := by
  obtain ⟨Cg, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hKcb, hδ₀, hc1, hL0, hhL, hεpin, hcε,
    hδpin, hβ, hroadU⟩ := hroad
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  -- ⟦THE CHARGE⟧ `Lc := log c + L` carries the twist
  have hc0 : 0 ≤ Real.log (c : ℝ) := Real.log_natCast_nonneg c
  have hL0' : 0 ≤ Real.log (c : ℝ) + L := by linarith
  have hhL' : Real.log (h : ℝ) ≤ Real.log (c : ℝ) + L := by linarith
  refine ⟨Cg, Kc, δ₀, β, x₀, Hopq,
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, s11GradeFloor_one_le _, hCgle, hc1, hL0, hhL,
    hεpin, hcε, hδpin, hKcb,
    (fun A hA162 hAw => flatDoorM_gradeFloor_win hA162 hCband0 (by linarith)),
    hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hfuse⟩ :=
    m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling_kwide_L h hh hL0' hhL' K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge hAL
  obtain ⟨Hcap, hCapLe, hroad0⟩ := hroadU K A hA26 hAge hAL
  refine ⟨max Hcap (flatDesignFloor A), max_le hCapLe (le_max_left _ _), ?_⟩
  intro Cp hCp a U1floor g ha haL hg
  obtain ⟨R, hReps, hU1, hRg, hstride, hRx, hRtow, hRcap, hR⟩ :=
    hroad0 a (max U1floor (flatDesignFloor A)) g ha haL hg
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hstride, hRx, hRtow, by omega, ?_⟩
  intro M hMfloor hKw
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit K M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦THE DESIGN FLOOR, ROUTED⟧ (cell 14) `flatDesignFloor A ≤ R.Hlo` gives `3.2·A ≤ loglog H`
  -- on the window, and the `A`-binder `10 + 2·Lc ≤ A` makes it the TOWER floor `50 + Lc`
  have hdesR : flatDesignFloor A ≤ R.Hlo := le_trans (le_max_right _ _) hU1
  have hBF : flatDesignBase A ≤ flatDesignFloor A := by
    unfold flatDesignFloor
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hLcA : 50 + (Real.log (c : ℝ) + L) ≤ 3.2 * A := by linarith
  have hfloor : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      50 + (Real.log (c : ℝ) + L) ≤ Real.log (Real.log (H : ℝ)) := by
    intro H hlo _
    have hDge : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
      rw [flatDesignBase]; exact Nat.le_ceil _
    have hBH : ((flatDesignBase A : ℕ) : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast le_trans hBF (le_trans hdesR hlo)
    have h1 : Real.exp (Real.exp (3.2 * A)) ≤ (H : ℝ) := le_trans hDge hBH
    have h2 : Real.exp (3.2 * A) ≤ Real.log (H : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h
    have h3 : 3.2 * A ≤ Real.log (Real.log (H : ℝ)) := by
      have h := Real.log_le_log (Real.exp_pos _) h2
      rwa [Real.log_exp] at h
    linarith
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo hhi => ⟨Real.log_natCast_nonneg H, by linarith [hfloor H hlo hhi]⟩
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRowH_L_gk h K R M
      (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hfloor hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H) j H ≤ RSanDoorRhoH ρ h H :=
    m4_arith_gate4_rhoH_L h M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 * (108 / 5 * RSanDoorRhoH ρ h H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_deltaH hh hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) (RSanDoorRhoH ρ h)
    (fun H => (h : ℝ) ^ 7 * rStrWitness H)
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
          (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRhoH_nonneg hρpos.le h H)
    (fun H => rStrWitness_mul_nonneg h H) ?_ hgate4 (fun H _ _ => rStrWitness_G1_h h H) ?_
    (arc36_of_regime_h_L hh hL0' hhL' hfloor) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRhoH ρ h H)
      (Ftr := fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) (H := H)
      (by have := RSanDoorRhoH_nonneg hρpos.le h H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRhoH ρ h H))
      (by have := rStrWitness_mul_nonneg h H
          simpa using (by linarith : (0:ℝ) ≤ 2 * ((h : ℝ) ^ 7 * rStrWitness H)))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh hlo
    have hSR1 : (1 : ℝ) ≤ strataResidualH h H := one_le_strataResidualH harc1
    have hSRsq : (1 : ℝ) ≤ strataResidualH h H ^ 2 := by nlinarith
    have hRSle : RSanDoorRhoH ρ h H ≤ rSanWitness H := by
      have h1 : RSanDoorRhoH ρ h H ≤ 1 := by
        unfold RSanDoorRhoH
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor_h h hh H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRhoH ρ h H)
      (Ftr := fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
            (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRhoH ρ h H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRhoH ρ h H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
            * (108 / 5 * RSanDoorRhoH ρ h H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
        * (108 / 5 * RSanDoorRhoH ρ h H)) ≤ 2 * δs ^ 2 := by linarith
    have hKcpos : (0 : ℝ) < 16 * Kc := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

/-! ## §I — THE CHARGE TWINS OF THE CONDITIONAL'S H-SOCKET SUPPLIERS, AT THE TOWER FLOOR

G12b's conditional reads the twist cap `log h ≤ 9` at ten suppliers (and kswin at the crossing
spine).  Each twin below is its `_b9` source with `hh9` replaced by the charge
`{Lc} (0 ≤ Lc) (log h ≤ Lc)`, the numeral register `-log ρ ≤ 10^14` replaced by the
TOWER-RELATIVE one `-log ρ ≤ log H₋ / 10^4` (the `_T` register's `rho` field), and the fixed floor
replaced by the TOWER floor `50 + Lc ≤ loglog H` at every `H ∈ [R.Hlo, R.Hhi]`.  Every numeral
that moved is derived beside it.  The seven `_L` helpers first (the sources' own `_b9` callees,
which have no charge twin in the corpus); the socket-cap-grid leaves are rung 2's landed
`s13_socketBase_logA_ge_sqrt_L` / `s13_socketBase_loglogA_sharp_L`. -/

/-- `s13_socketBase_loglogA_LH_b9` at the charge (`s13_socketBase_loglogA_LH_L`) — SUPPLIER-SWAP:
the two cap-grid leaves are rung 2's `_L` ones, read at `hflL : 50 + Lc ≤ loglog H₋`.
BODY: the source's. -/
theorem s13_socketBase_loglogA_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (2000 : ℝ) ≤ Real.log (A : ℝ) ∧ (6500 : ℝ) ≤ Real.log (Real.log (A : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have hlogHbig : (4000000 : ℝ) ≤ Real.log (H : ℝ) := le_trans s13_four_million_le_exp50 hexp50
  set u : ℝ := Real.sqrt (H : ℝ) with hu
  have hu2 : u ^ 2 = (H : ℝ) := Real.sq_sqrt (by positivity)
  have hu0 : (0 : ℝ) < u := by rw [hu]; exact Real.sqrt_pos.mpr (by linarith)
  have hu2000 : (2000 : ℝ) ≤ u := by nlinarith [hu2, hu0, hHR]
  have hmain : u ≤ Real.log (A : ℝ) := s13_socketBase_logA_ge_sqrt_L hh hL0 hhL hfl hb hflL
  exact ⟨le_trans hu2000 hmain,
    by have := s13_socketBase_loglogA_sharp_L hh hL0 hhL hfl hb hflL; linarith⟩

/-- `s14_loglogX_ge_of_socket_LH_b9` at the charge (`s14_loglogX_ge_of_socket_LH_L`) —
SUPPLIER-SWAP (`s13_socketBase_loglogA_sharp_L`, `s13_socketBase_loglogA_LH_L`).  BODY: the
source's. -/
theorem s14_loglogX_ge_of_socket_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    Real.log (H : ℝ) / 2 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hsharp := s13_socketBase_loglogA_sharp_L hh hL0 hhL hfl hb hflL
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA_LH_L hh hL0 hhL hfl hb hflL
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hmono : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := Real.log_le_log hA0 hAX
  have h := Real.log_le_log (by linarith : (0 : ℝ) < Real.log (A : ℝ)) hmono
  linarith

/-- `s12c_llX_ge_LH_b9` at the charge (`s12c_llX_ge_LH_L`) — SUPPLIER-SWAP
(`s14_loglogX_ge_of_socket_LH_L`).  BODY: the source's. -/
theorem s12c_llX_ge_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) / 2
      ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ R.Hlo := R.hHlo_floor
  have hHR : (4000000 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast hH4
  have hlogHlopos : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hcast : ((R.Hlo : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo
  have hmono : Real.log ((R.Hlo : ℕ) : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hcast
  have hsharp := s14_loglogX_ge_of_socket_LH_L hh hL0 hhL hfl hb hflL
  rw [Real.exp_log hlogHlopos]
  linarith

/-- `s13_band_qfit_h_b9` at the charge (`s13_band_qfit_h_L`) — TRANSPORT: the closing `linarith`
reads `log h + 12·λ_H ≤ Lc + 12·λ_H ≤ 13·λ_H ≤ 10·Λ` under `Lc ≤ λ_H` (new binder `hLH`, paid by
the tower floor) and `7000·λ_H ≤ Λ`, `1 ≤ λ_H` (slack `69987·λ_H`).  BODY: the source's. -/
theorem s13_band_qfit_h_L {h q H Xd : ℕ} (hh : 0 < h) {Lc : ℝ} (hhL : Real.log (h : ℝ) ≤ Lc)
    (hLH : Lc ≤ Real.log (Real.log ((H : ℕ) : ℝ)))
    (hq : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H)
    (hH : (0 : ℝ) < Real.log ((H : ℕ) : ℝ)) (hX : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ))
    (hHfl : (1 : ℝ) ≤ Real.log (Real.log ((H : ℕ) : ℝ)))
    (harm : 7000 * Real.log (Real.log ((H : ℕ) : ℝ))
      ≤ Real.log (Real.log ((Xd : ℕ) : ℝ))) :
    (q : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (10 : ℕ) := by
  refine le_trans hq ?_
  have hA : arcDen 12 H = Real.exp (12 * Real.log (Real.log ((H : ℕ) : ℝ))) := by
    rw [arcDen, Real.rpow_def_of_pos hH]; ring_nf
  have hB : (Real.log ((Xd : ℕ) : ℝ)) ^ (10 : ℕ)
      = Real.exp (10 * Real.log (Real.log ((Xd : ℕ) : ℝ))) := by
    rw [← Real.rpow_natCast (Real.log ((Xd : ℕ) : ℝ)) 10, Real.rpow_def_of_pos hX]
    push_cast; ring_nf
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hhe : (h : ℝ) = Real.exp (Real.log (h : ℝ)) := (Real.exp_log hh0).symm
  rw [hA, hB, hhe, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- `s15_block_at_socket_gen_LH_b9` at the charge (`s15_block_at_socket_gen_LH_L`) — NUMERAL-LIFT:
`hlog'` reads the x-scale's `log h` at `Lc` (`9 ↦ Lc`).  THE ROOM, derived: `hE` needs
`log h + 12·λ_H ≤ 18·log 2·Λ₊` with `Λ₊ ≥ λ_H`, i.e. `Lc ≤ (18·log 2 − 12)·λ_H`, and
`18·0.6931471803 − 12 = 0.4766492454`.  The TOWER floor `50 + Lc ≤ λ_H` does NOT pay it
(`Lc = λ_H − 50` exceeds `0.4766·λ_H` once `λ_H > 95.5`), so this twin reads the floor
`hHL3 : 3·Lc ≤ λ_H` (`Lc ≤ λ_H/3 ≤ 0.4766·λ_H`), which the design floor pays at every
consumer (`3.2·A ≥ 32 + 6.4·Lc` from `10 + 2·Lc ≤ A`).  BODY: the source's, with `hE` closed by
two explicit products in place of the source's `nlinarith`. -/
theorem s15_block_at_socket_gen_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ}
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s E : ℕ}
    (hb : SocketBaseLH h R M H L q j A s)
    (hHreg : 0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hHL3 : 3 * Lc ≤ Real.log (Real.log (H : ℝ)))
    (hblk : ((E : ℕ) : ℝ) + 1 + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)) :
    2 ^ E ≤ A + s := by
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) :=
    lt_of_lt_of_le (by norm_num) (one_lt_log_of_loglog_ge hHreg.1 (by norm_num) hHreg.2).le
  have hllH : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) :=
    s13_loglog_le_of_range (R := R) hlo hhi
  set m : ℕ := ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ with hm
  have hxs : ((4 ^ m : ℕ) : ℝ) ^ 2 ≤ 2 * ((h : ℝ) * arcDen 12 H) * (A : ℝ) :=
    s13_socketBase_xscale_LH hb
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hL12 : (0 : ℝ) < Real.log (H : ℝ) ^ (12 : ℕ) := by positivity
  have hhl : (0 : ℝ) < (h : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ) := mul_pos hh0 hL12
  have hlhs0 : (0 : ℝ) < ((4 ^ m : ℕ) : ℝ) ^ 2 := by positivity
  have hlog := Real.log_le_log hlhs0 hxs
  have hLid : Real.log (((4 ^ m : ℕ) : ℝ) ^ 2) = 4 * (m : ℝ) * Real.log 2 := by
    have h4 : ((4 ^ m : ℕ) : ℝ) = (4 : ℝ) ^ m := by push_cast; ring
    rw [h4, ← pow_mul, Real.log_pow, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hRR : Real.log (2 * ((h : ℝ) * arcDen 12 H) * (A : ℝ))
      = Real.log 2 + Real.log (h : ℝ) + 12 * Real.log (Real.log (H : ℝ)) + Real.log (A : ℝ) := by
    rw [harcpow, Real.log_mul (mul_pos two_pos hhl).ne' hApos.ne', Real.log_mul two_ne_zero hhl.ne',
      Real.log_mul hh0.ne' hL12.ne', Real.log_pow]
    push_cast; ring
  rw [hLid, hRR] at hlog
  -- at the charge: `9 ↦ Lc`
  have hlog' : 4 * (m : ℝ) * Real.log 2
      ≤ Real.log 2 + Lc + 12 * Real.log (Real.log (H : ℝ)) + Real.log (A : ℝ) := by linarith
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hE : ((E : ℕ) : ℝ) * Real.log 2 ≤ Real.log (A : ℝ) := by
    have hl20 : (0 : ℝ) ≤ Real.log 2 := by linarith
    have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) := by linarith [hHreg.2]
    have hm1 := mul_le_mul_of_nonneg_right hblk hl20
    have hm2 : 0.6931471803 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        ≤ Real.log 2 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hl2lo.le hΛ0
    nlinarith [hm1, hm2, hlog', hllH, hHL3, hHreg.2]
  have hpow : ((2 : ℝ)) ^ E ≤ (A : ℝ) := by
    have hlt : Real.log (((2 : ℝ)) ^ E) ≤ Real.log (A : ℝ) := by
      rw [Real.log_pow]; linarith
    exact (Real.log_le_log_iff (by positivity) hApos).mp hlt
  have hcast : ((2 ^ E : ℕ) : ℝ) ≤ (A : ℝ) := by push_cast; exact hpow
  have hnat : (2 : ℕ) ^ E ≤ A := by exact_mod_cast hcast
  omega

set_option maxHeartbeats 1000000 in
-- as the source: the two log-comparison claims re-elaborate, each carrying the shift's terms
/-- `s13_smallGradeFits_h_b9` at the charge (`s13_smallGradeFits_h_L`) — TRANSPORT: the cap is read
only in `hclaim1`'s `linarith`, whose supply is `20.488·log Λ` (`Λ = log H`) against a demand of
`4.0976·log h`.  At the charge `9 ↦ log Λ`: `log h ≤ Lc ≤ log Λ − 50` (the new binder
`hHL : 50 + Lc ≤ loglog H`), so the demand is `4.0976·log Λ ≤ 20.488·log Λ` (×5.0).  BODY: the
source's. -/
theorem s13_smallGradeFits_h_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {j₀ H : ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hlo : R.Hlo ≤ H)
    (hHL : 50 + Lc ≤ Real.log (Real.log (H : ℝ)))
    (hgate : (7 / 10 : ℝ) * (j₀ : ℝ)
        + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
            + 2 * Real.log (strataResidualH h H) - Real.log ρ)
        + 7 * Real.log (h : ℝ)
      ≤ Real.log (H : ℝ)) :
    m4SmallGradeFits j₀ (fun H => 2 * RSanDoorRhoH ρ h H)
      (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H := by
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hlogh0 : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_nonneg hh1
  obtain ⟨hlog3up, hlog3lo⟩ := s13_log_three_bounds
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hH0 : (0 : ℝ) < (H : ℝ) := by
    have : (0 : ℕ) < H := by omega
    exact_mod_cast this
  set Λ : ℝ := Real.log (H : ℝ) with hΛdef
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp15 : Real.exp 15 ≤ 4000000 := by
    have h15 : Real.exp 15 = (Real.exp 1) ^ (15 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    have hp : (Real.exp 1) ^ (15 : ℕ) ≤ (2.7182818286 : ℝ) ^ (15 : ℕ) :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he1.le 15
    rw [h15]
    calc (Real.exp 1) ^ (15 : ℕ) ≤ (2.7182818286 : ℝ) ^ (15 : ℕ) := hp
      _ ≤ 4000000 := by norm_num
  have hΛ15 : (15 : ℝ) ≤ Λ := by
    rw [hΛdef, Real.le_log_iff_exp_le hH0]
    linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hΛ1 : (2 : ℝ) < Λ := by linarith
  have hexp2 : Real.exp 2 ≤ 15 := by
    have h2 : Real.exp 2 = (Real.exp 1) ^ (2 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    have hp : (Real.exp 1) ^ (2 : ℕ) ≤ (2.7182818286 : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he1.le 2
    rw [h2]
    calc (Real.exp 1) ^ (2 : ℕ) ≤ (2.7182818286 : ℝ) ^ (2 : ℕ) := hp
      _ ≤ 15 := by norm_num
  have hlogΛ2 : (2 : ℝ) ≤ Real.log Λ := by
    rw [Real.le_log_iff_exp_le hΛ0]
    linarith
  have hlogΛ0 : (0 : ℝ) < Real.log Λ := by linarith
  -- at the charge: `9 ↦ log Λ`; room: `log h ≤ Lc ≤ log Λ − 50` (`Λ = log H`)
  have hhΛ : Real.log (h : ℝ) ≤ Real.log Λ := by linarith
  have harcpow : arcDen 12 H = Λ ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harch : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh hlo
  set S : ℝ := strataResidualH h H with hSdef
  have hS1 : (1 : ℝ) ≤ S := one_le_strataResidualH harch
  have hS0 : (0 : ℝ) < S := by linarith
  have hlogS0 : (0 : ℝ) ≤ Real.log S := Real.log_nonneg hS1
  have hRSt : rStrWitness H = Λ ^ (84 : ℕ) := by
    rw [rStrWitness, harcpow, ← pow_mul]
    exact max_eq_right (one_le_pow₀ (by linarith))
  set L : ℕ := Nat.log 2 H with hLdef
  have hLpow : ((2 : ℝ)) ^ L ≤ (H : ℝ) := by
    have h : (2 : ℕ) ^ L ≤ H := Nat.pow_log_le_self 2 (by omega)
    have h' : ((2 ^ L : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h
    simpa using h'
  have hLlog : (L : ℝ) * Real.log 2 ≤ Λ := by
    have h := Real.log_le_log (by positivity) hLpow
    rwa [Real.log_pow] at h
  have hlog32 : Real.log (3 / 2 : ℝ) ≤ 24 / 41 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith
  have hlog320 : (0 : ℝ) ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog43 : Real.log (4 / 3 : ℝ) ≤ 2890 / 10000 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    linarith
  have hlog83 : Real.log (8 / 3 : ℝ) ≤ 9825 / 10000 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast
    linarith
  have hu32 : (L : ℝ) * Real.log (3 / 2 : ℝ) ≤ 24 / 41 * Λ := by
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    calc (L : ℝ) * Real.log (3 / 2 : ℝ) ≤ (L : ℝ) * (24 / 41 * Real.log 2) :=
          mul_le_mul_of_nonneg_left hlog32 hL0
      _ = 24 / 41 * ((L : ℝ) * Real.log 2) := by ring
      _ ≤ 24 / 41 * Λ := by linarith
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  have h9 : (0 : ℝ) ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hG0 : (0 : ℝ) ≤ Real.log 9 + 84 * Real.log Λ + 2 * Real.log S - Real.log ρ := by
    linarith
  have hj0 : (0 : ℝ) ≤ (j₀ : ℝ) := Nat.cast_nonneg j₀
  set Q : ℝ := (H : ℝ) ^ 2 * RSanDoorRhoH ρ h H with hQdef
  have hRS : RSanDoorRhoH ρ h H = ρ / S ^ 2 := rfl
  have hQ0 : (0 : ℝ) < Q := by
    rw [hQdef, hRS]; positivity
  have hlogQ : Real.log Q = 2 * Λ + Real.log ρ - 2 * Real.log S := by
    rw [hQdef, hRS, Real.log_mul (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlogD : Real.log (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)))
      = Real.log 2 + 7 * Real.log (h : ℝ) + 84 * Real.log Λ := by
    rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hD0 : (0 : ℝ) < 2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)) := by positivity
  have hclaim1 : 9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
      * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))) ≤ Q := by
    have hP0 : (0 : ℝ) < 9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
        * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))) := by positivity
    have hlogP : Real.log (9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
          * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))))
        = Real.log (9 / 2) + (L : ℝ) * Real.log (3 / 2 : ℝ)
          + (j₀ : ℝ) * Real.log (4 / 3 : ℝ) + Λ
          + (Real.log 2 + 7 * Real.log (h : ℝ) + 84 * Real.log Λ) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, hlogD]
    have hle : Real.log (9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
        * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)))) ≤ Real.log Q := by
      rw [hlogP, hlogQ]
      have h92 : Real.log (9 / 2 : ℝ) + Real.log 2 = Real.log 9 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        norm_num
      have h43 : (j₀ : ℝ) * Real.log (4 / 3 : ℝ) ≤ (j₀ : ℝ) * (2890 / 10000) :=
        mul_le_mul_of_nonneg_left hlog43 hj0
      linarith [hgate, hu32, h43, h92, hlogΛ2, hhΛ, h9, hlogS0, hlogρ, hΛ15, hlogh0]
    have h := Real.exp_le_exp.mpr hle
    rwa [Real.exp_log hP0, Real.exp_log hQ0] at h
  have hclaim2 : 9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀
      * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))) ≤ Q := by
    have hP0 : (0 : ℝ) < 9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀
        * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))) := by positivity
    have hlogP : Real.log (9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀
          * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))))
        = Real.log (9 / 5) + (L : ℝ) * Real.log (3 / 2 : ℝ)
          + (j₀ : ℝ) * Real.log (8 / 3 : ℝ)
          + (Real.log 2 + 7 * Real.log (h : ℝ) + 84 * Real.log Λ) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, hlogD]
    have hle : Real.log (9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀
        * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)))) ≤ Real.log Q := by
      rw [hlogP, hlogQ]
      have h95 : Real.log (9 / 5 : ℝ) + Real.log 2 ≤ Real.log 9 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        exact Real.log_le_log (by norm_num) (by norm_num)
      have h83 : (j₀ : ℝ) * Real.log (8 / 3 : ℝ) ≤ (j₀ : ℝ) * (9825 / 10000) :=
        mul_le_mul_of_nonneg_left hlog83 hj0
      linarith [hgate, hu32, h83, h95, hlogh0, hG0]
    have h := Real.exp_le_exp.mpr hle
    rwa [Real.exp_log hP0, Real.exp_log hQ0] at h
  refine m4SmallGradeFits_of_threshold (D := 2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)))
    (le_of_eq (by rw [hRSt])) ?_ ?_
  · have := RSanDoorRhoH_nonneg hρ0.le h H
    linarith
  · rw [← hLdef]
    have hexpand : (9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
          + 9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀)
            * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)))
        = 9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
            * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)))
          + 9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀
            * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))) := by ring
    rw [hexpand]
    have hQ2 : (H : ℝ) ^ 2 * (2 * RSanDoorRhoH ρ h H) = 2 * Q := by rw [hQdef]; ring
    rw [hQ2]
    linarith


/-- `s13_winFit_h_of_halfWindow_gen_b9` at the charge (`s13_winFit_h_of_halfWindow_gen_L`) —
NUMERAL-LIFT: `hSle`'s `+ 9 ↦ + Lc`, and the final `nlinarith` reads `Lc ≤ 2·w − 2`
(`Lc ≤ loglog H − 50 ≤ 2·w − 52`, `w = √(log H)`) where it read `9`: every charge term is then
LINEAR in `w` (`6·(24·w + Lc) + 7·Lc ≤ 170·w`) against `w²/2` at `w ≥ 2000`.  BODY: the
source's. -/
theorem s13_winFit_h_of_halfWindow_gen_L {h : ℕ} (hh : 0 < h) {Lc : ℝ}
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {jr ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hfloor : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 50 + Lc ≤ Real.log (Real.log (H : ℝ)))
    (hhalf : (7 / 10 : ℝ) * jr + 3 * Real.log (1 / ρ) ≤ Real.log (R.Hlo : ℝ) / 2) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (7 / 10 : ℝ) * jr
          + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
              + 2 * Real.log (strataResidualH h H) - Real.log ρ)
          + 7 * Real.log (h : ℝ)
        ≤ Real.log (H : ℝ) := by
  intro H hlo hhi
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hlogh0 : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_nonneg hh1
  have hHlo4 : 4000000 ≤ R.Hlo := R.hHlo_floor
  have hH4 : 4000000 ≤ H := le_trans hHlo4 hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hHloR : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast hHlo4
  have hloR : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo
  have hlogmono : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hloR
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have hlogHbig : (4000000 : ℝ) ≤ Real.log (H : ℝ) := le_trans s13_four_million_le_exp50 hexp50
  set w : ℝ := Real.sqrt (Real.log (H : ℝ)) with hw
  have hw2 : w ^ 2 = Real.log (H : ℝ) := Real.sq_sqrt hlogH0.le
  have hw0 : (0 : ℝ) < w := by rw [hw]; exact Real.sqrt_pos.mpr hlogH0
  have hw2000 : (2000 : ℝ) ≤ w := by nlinarith [hw2, hw0, hlogHbig]
  have hlogw : Real.log w = Real.log (Real.log (H : ℝ)) / 2 := by
    rw [hw]; exact Real.log_sqrt hlogH0.le
  have hlogwle : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hw0
  have hllH : Real.log (Real.log (H : ℝ)) ≤ 2 * w - 2 := by rw [hlogw] at hlogwle; linarith
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hSval : strataResidualH h H
      = 1 + Real.log (h : ℝ) + 12 * Real.log (Real.log (H : ℝ)) := by
    rw [strataResidualH, harcpow,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by linarith
  have hS1 : (1 : ℝ) ≤ strataResidualH h H := by rw [hSval]; linarith
  have hlogS : Real.log (strataResidualH h H) ≤ strataResidualH h H - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  -- at the charge: `9 ↦ Lc`; room: `Lc ≤ loglog H − 50 ≤ 2·w − 2` (`w² = log H`)
  have hLcw : Lc ≤ 2 * w - 2 := by linarith [hfloor H hlo hhi]
  have hSle : strataResidualH h H - 1 ≤ 24 * w - 24 + Lc := by rw [hSval]; linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hlog9 : Real.log 9 ≤ 4 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; linarith
  have hinv : Real.log (1 / ρ) = - Real.log ρ := by rw [one_div, Real.log_inv]
  rw [hinv] at hhalf
  nlinarith [hhalf, hlogmono, hllH, hlogS, hSle, hlog9, hw2, hw2000, hw0, hhL, hLcw, hlogh0]

/-- **TWIN 1** — `s12c_eps_threshold_at_socket_flatH_b9` at the charge
(`s12c_eps_threshold_at_socket_flatH_L`).  STATEMENT: the source's with `hh9 ↦ (hL0, hhL)`, the
fixed floor `hlam` ↦ the TOWER floor `hfloor`, and `hrho` at the tower-relative register
`-log ρ ≤ log H₋/10^4`; the conclusion is the source's.  BODY: rung 2's `_flat_T` reader
(`s12c_eps_threshold_at_socket_flat_T`) at `SocketBaseLH h`, its `s12c_llX_ge` ↦
`s12c_llX_ge_LH_L`.  THE MARGIN is the template's: `0.0008 + 0.0001 ≤ 0.001` on `e^λ`. -/
theorem s12c_eps_threshold_at_socket_flatH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ ε : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hfloor : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 50 + Lc ≤ Real.log (Real.log (H : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 10000)
    (hε : ε ≤ theta293 - 1 / 500) :
    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
      ≤ (theta293 - ε) * Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)) := hfloor R.Hlo le_rfl R.hHlohi
  have hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) := by linarith
  obtain ⟨hlogHlo0, -⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hlogHlo1 : (1 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hlogHlo0 (by norm_num : (0 : ℝ) < 50) hlam
  have hrhoE : -Real.log ρ ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) / 10000 := by
    rw [Real.exp_log (by linarith : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ))]; exact hrho
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hll := s12c_llX_ge_LH_L hh hL0 hhL hfl hb hflL
  have hcore := flat_lambda_core_T hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by linarith
  have hcoef : (1 : ℝ) / 500 ≤ theta293 - ε := by linarith
  have hprod : (1 : ℝ) / 500 * ll ≤ (theta293 - ε) * ll :=
    mul_le_mul_of_nonneg_right hcoef hll0
  have h1 : 14 * Λ ≤ 14 * Real.exp (lam / 2) := by linarith
  linarith

/-- **TWIN 2** — `s15_heps293_at_socket_flatH_b9` at the charge (`s15_heps293_at_socket_flatH_L`).
STATEMENT: the source's with `hh9 ↦ (hL0, hhL)`, `hlam ↦ hfloor`, `hrho` tower-relative.  BODY:
rung 2's `s15_heps293_at_socket_flat_T` at `SocketBaseLH h` (leaves `s13_socketBase_loglogA_LH_L`,
`s12c_llX_ge_LH_L`).  THE MARGIN is the template's: `0.0009 ≤ 0.0017` on `e^λ`. -/
theorem s15_heps293_at_socket_flatH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hρ : 0 < ρ)
    (hfloor : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 50 + Lc ≤ Real.log (Real.log (H : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 10000) :
    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi := by
  have hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)) := hfloor R.Hlo le_rfl R.hHlohi
  have hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) := by linarith
  obtain ⟨hlogHlo0, -⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hlogHlo1 : (1 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hlogHlo0 (by norm_num : (0 : ℝ) < 50) hlam
  have hrhoE : -Real.log ρ ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) / 10000 := by
    rw [Real.exp_log (by linarith : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ))]; exact hrho
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA_LH_L hh hL0 hhL hfl hb hflL
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpool : constPool ρ R.Hhi = Real.exp (Real.log ρ - Real.log 376266 - 14 * Λ) := by
    rw [constPool_def, hLamdef, Real.exp_sub, Real.exp_sub, Real.exp_log hρ,
      Real.exp_log (by norm_num : (0 : ℝ) < 376266), div_div]
  have hlhs : (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) = Real.exp (-(theta293 * ll)) := by
    rw [Real.rpow_def_of_pos hX0, hlldef]; congr 1; ring
  rw [hlhs, hpool]
  refine Real.exp_le_exp.mpr ?_
  have hθ : (0.0034 : ℝ) ≤ theta293 := by have := s13_theta293_margin_lo; linarith
  have hll := s12c_llX_ge_LH_L hh hL0 hhL hfl hb hflL
  have hcore := flat_lambda_core_T hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by
    have : (0 : ℝ) < Real.exp lam / 2 := by positivity
    linarith [hll]
  have hkey : 14 * Λ + 13 + (-Real.log ρ) ≤ theta293 * ll := by
    have h1 : 14 * Λ ≤ 14 * Real.exp (lam / 2) := by linarith [htow]
    have h2 : theta293 * ll ≥ 0.0034 * (Real.exp lam / 2) := by
      nlinarith [hθ, hll, hll0]
    nlinarith [h1, h2, hcore, hrhoE]
  linarith [hkey, hlog376]

/-- **TWIN 3** — `s15_hband4096_at_socket_flatH_b9` at the charge
(`s15_hband4096_at_socket_flatH_L`).  STATEMENT: the source's with `hh9 ↦ (hL0, hhL)`,
`hlam ↦ hfloor`, `hrho` tower-relative.  BODY: rung 2's `s15_hband4096_at_socket_flat_T` at
`SocketBaseLH h`.  THE MARGIN is the template's: `0.0009 ≤ 0.0017` on `e^λ`. -/
theorem s15_hband4096_at_socket_flatH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hρ : 0 < ρ)
    (hfloor : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 50 + Lc ≤ Real.log (Real.log (H : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 10000) :
    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500) * constPool ρ R.Hhi := by
  have hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)) := hfloor R.Hlo le_rfl R.hHlohi
  have hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) := by linarith
  obtain ⟨hlogHlo0, -⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hlogHlo1 : (1 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hlogHlo0 (by norm_num : (0 : ℝ) < 50) hlam
  have hrhoE : -Real.log ρ ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) / 10000 := by
    rw [Real.exp_log (by linarith : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ))]; exact hrho
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA_LH_L hh hL0 hhL hfl hb hflL
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpool : constPool ρ R.Hhi = Real.exp (Real.log ρ - Real.log 376266 - 14 * Λ) := by
    rw [constPool_def, hLamdef, Real.exp_sub, Real.exp_sub, Real.exp_log hρ,
      Real.exp_log (by norm_num : (0 : ℝ) < 376266), div_div]
  have hlhs : (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
      = Real.exp ((1 - (1 : ℝ) / 500) * ll) := by
    rw [Real.rpow_def_of_pos hX0, hlldef]; congr 1; ring
  rw [hlhs, hpool, ← Real.exp_add]
  have h4096 : (4096 : ℝ) ≤ Real.exp 9 := by
    have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7 : ℝ) ^ (9 : ℕ) ≤ (Real.exp 1) ^ (9 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 9
    have hn : (4096 : ℝ) ≤ (2.7 : ℝ) ^ (9 : ℕ) := by norm_num
    rw [h]; linarith
  refine le_trans h4096 (Real.exp_le_exp.mpr ?_)
  have hll := s12c_llX_ge_LH_L hh hL0 hhL hfl hb hflL
  have hcore := flat_lambda_core_T hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by
    have : (0 : ℝ) < Real.exp lam / 2 := by positivity
    linarith [hll]
  have h1 : 14 * Λ ≤ 14 * Real.exp (lam / 2) := by linarith [htow]
  have h2 : (1 - (1 : ℝ) / 500) * ll ≥ 0.0017 * Real.exp lam := by nlinarith [hll, hll0]
  linarith [h1, h2, hcore, hrhoE, hlog376]

/-- **TWIN 4** — `s15_gRows_const_at_socket_flat_doorLH_gk_b9` at the charge
(`s15_gRows_const_at_socket_flat_doorLH_gk_L`).  STATEMENT: the source's with `hh9 ↦ (hL0, hhL)`,
the tower floor `hfloor` added after `hb`, `hrho` tower-relative.  BODY: rung 2's
`s15_gRows_const_at_socket_flat_doorL_gk_T` with `SocketBaseL ↦ SocketBaseLH h` (the socket is
already the `H`-socket, so the template's `socketBase_of_socketBaseL` step is dropped).  THE
MARGIN is the template's: `0.0009 ≤ 0.5` on `e^λ`. -/
theorem s15_gRows_const_at_socket_flat_doorLH_gk_L (K : ℕ) {h : ℕ} (hh : 0 < h) {Lc : ℝ}
    (hL0 : 0 ≤ Lc) (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime}
    {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hfloor : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 50 + Lc ≤ Real.log (Real.log (H : ℝ)))
    (hM : 1 ≤ M) (hρ0 : 0 < ρ) (_hρ1 : ρ ≤ 1)
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 10000)
    (hlvl : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        + (1 / 3) * Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ))
        + (-Real.log ρ)
      ≤ (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2) :
    GRowsZeroGate'''_L_gk K M (A + s) 0 (constPool ρ R.Hhi) := by
  have hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)) := hfloor R.Hlo le_rfl R.hHlohi
  obtain ⟨hlogHlo0, hlamT⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hlogHlo1 : (1 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hlogHlo0 (by norm_num : (0 : ℝ) < 50) hlamT
  have hrhoE : -Real.log ρ ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) / 10000 := by
    rw [Real.exp_log (by linarith : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ))]; exact hrho
  have hE0 : (0 : ℝ) < Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) := Real.exp_pos _
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le _hρ1
  have hQ0 : (0 : ℝ)
      ≤ Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) := by
    rw [calQK_L_one_gk_eq]; exact s15_loglogQ1_L_nonneg hM
  obtain ⟨-, hL50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have hp2 : 27 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ := by
    linarith [hlvl, hQ0, hL50, hlogρ]
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hAs : 0 < A + s := by omega
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA_LH_L hh hL0 hhL hfl hb hflL
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hllle : Real.log (Real.log (((A + s : ℕ)) : ℝ)) ≤ Real.log (((A + s : ℕ)) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hll := s12c_llX_ge_LH_L hh hL0 hhL hfl hb hflL
  have hcore := flat_lambda_core_T hlam50
  have hendbud : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + (-Real.log ρ)
      ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h1 : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        ≤ 14 * Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := by linarith
    linarith [hcore, hll, hllle, hrhoE, h1, hE0]
  exact gRowsZeroGate'''_L_gk_of_budget K hM hAs hρ0 (by linarith) hp2 hendbud

/-- **TWIN 5** — `doorBandBase_family'H_L_gk_b9` at the charge (`doorBandBase_family'H_L_gk_L`) —
SUPPLIER-SWAP: `qfit` is `s13_band_qfit_h_L` at the tower floor (`Lc ≤ loglog H` from
`50 + Lc ≤ loglog H`); the register `hHreg` is replaced by the tower floor `hfloor` and read off
it (`50 ≤ 50 + Lc`).  `X400`/`grade`/`err` are cap-blind.  BODY: the source's. -/
theorem doorBandBase_family'H_L_gk_L (K : ℕ) {h : ℕ} (hh : 0 < h) {Lc : ℝ} (_hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M x₀ : ℕ} {C' Kar ρ : ℝ} {C₁ : ℕ → ℝ}
    (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hC1hi : ∀ n : ℕ, C₁ n ≤ 1)
    (hfloor : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 50 + Lc ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho 0 0 ((h : ℝ) * (R.ω : ℝ)) ρ R.Hhi ≤ (R.x : ℝ))
    (harith : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) Kar ρ)
    (hx0 : x₀ ≤ 2 ^ doorRowFloorL M)
    (hC1one : ∀ n : ℕ, (1 : ℝ) ≤ C₁ n)
    (hgrade : 8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
      ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)))
    (hblock : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      s13BlockFloor_L_gk K M ≤ A + s) :
    ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) := by
  -- the source's register `hHreg`, read off the tower floor (`50 ≤ 50 + Lc`)
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo hhi => ⟨Real.log_natCast_nonneg H, by linarith [hfloor H hlo hhi]⟩
  intro H L q j A s hbL
  have hfr := harith H L q j A s hbL
  have hΛ : (356600 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := hfr.loglogX_ge
  have hμ : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := lt_trans (by norm_num) hfr.one_lt_logX
  obtain ⟨hbig, h48, h24⟩ := s13_band_floors hμ hΛ
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by linarith
  have hX2 : (2 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hjfl : doorRowFloorL M ≤ j := hbL.2.2.2.2.2.2.1
  have hfive := s13_doorRowZeroBase_five_L_gk K hM (hblock H L q j A s hbL) hjfl
  have hreg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) := hfive.2.1
  refine
    { X400 := s13_band_X400_LH hM hbL
      C₁_one := hC1one (A + s)
      x₀_le := ?_
      qfit := ?_
      gHalf := ?_
      gO1 := ?_
      gWin := ?_
      grade := ?_
      err := ?_ }
  · have hAj : 2 ^ j ≤ A := hbL.2.2.2.2.2.2.2.2.1
    have hpow : (2 : ℕ) ^ doorRowFloorL M ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjfl
    exact le_trans hx0 (le_trans hpow (le_trans hAj (Nat.le_add_right A s)))
  · refine s13_band_qfit_h_L hh hhL (by linarith [hfloor H hbL.1 hbL.2.1]) hbL.2.2.2.2.1
      (lt_trans (by norm_num) hfr.one_lt_logH) hμ
      ?_ ?_
    · linarith [hfr.Hfloor]
    · have := hfr.armWeak
      have := hfr.logInvRho_nonneg
      linarith
  · intro k hk1 hk2
    have h := s13_band_gHalf hX2 h48 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · intro k hk1 hk2
    have hQ0 : (0 : ℝ) ≤ Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) := by
      linarith [s13_band_log_calQK_two_ge_L_gk K hM]
    have h := s13_band_gO1 hX2 hQ0 hreg h24 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · intro k hk1 hk2
    have h := s13_band_gWin (by linarith) hX2 (s13_band_loglog_calP_one_L_gk K hM)
      (s13_band_log_calQK_two_ge_L_gk K hM) hreg k hk1 hk2
    simpa only [s13Aexp] using h
  · refine le_trans hgrade ?_
    refine Real.rpow_le_rpow (by positivity) (s13_band_baseFloor_LH hbL) ?_
    rw [s13Aexp]; norm_num
  · exact s13_band_err_free_LH hh hρ0 hρ1 (hC1one (A + s)) (hC1hi (A + s)) hHreg hg hbL

/-- **TWIN 6** — `s15_block_at_socketH_L_gk_b9` at the charge (`s15_block_at_socketH_L_gk_L`) —
SUPPLIER-SWAP (`s15_block_at_socket_gen_LH_L`), which reads the floor `hHL3 : 3·Lc ≤ loglog H`
(derived there: the block's room is `Lc ≤ 0.4766·loglog H`, which `50 + Lc ≤ loglog H` alone does
not pay).  BODY: the source's. -/
theorem s15_block_at_socketH_L_gk_L (K : ℕ) {h : ℕ} (hh : 0 < h) {Lc : ℝ} (_hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseLH h R M H L q j A s)
    (hHreg : 0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hHL3 : 3 * Lc ≤ Real.log (Real.log (H : ℝ)))
    (hblk : ((s13BlockExp_L_gk K M : ℕ) : ℝ) + 1
        + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)) :
    s13BlockFloor_L_gk K M ≤ A + s := by
  rw [s13BlockFloor_L_gk]
  exact s15_block_at_socket_gen_LH_L hh hhL hb hHreg hHL3 hblk

/-- **TWIN 7** — `s13_gate8_L_gk_h_b9` at the charge (`s13_gate8_L_gk_h_L`) — TRANSPORT: the closing
`nlinarith` needs `log h < 155.7·Λ` (`242·log 2 − 12 − 1 > 154.7` on `Λ ≥ 1`); at the charge
`9 ↦ Lc` with the new binder `hΛL : Lc ≤ Λ`, so `log h ≤ Lc ≤ Λ < 155.7·Λ`.  BODY: the
source's. -/
theorem s13_gate8_L_gk_h_L {h : ℕ} {R : ChowlaRegime} {K M : ℕ} {Λ : ℝ} (hh : 0 < h)
    {Lc : ℝ} (_hL0 : 0 ≤ Lc) (hhL : Real.log (h : ℝ) ≤ Lc) (hΛL : Lc ≤ Λ)
    (hΛ : Real.log (Real.log (R.Hhi : ℝ)) ≤ Λ) (hΛ1 : 1 ≤ Λ)
    (hgr : 242 * Λ ≤ ((AdoorL M : ℕ) : ℝ)) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (h : ℝ) * arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
  intro H hlo hhi
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hLH : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
  have hL0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hLH
  have hlogarc : Real.log (arcDen 12 H) = 12 * Real.log (Real.log (H : ℝ)) := by
    rw [arcDen, Real.log_rpow hL0]
  have hle := le_trans (s13_loglog_le_of_range (R := R) hlo hhi) hΛ
  have hlogP : Real.log ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
      = ((AdoorL M : ℕ) : ℝ) * Real.log 2 := log_calP_one_gen _ _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
    have hpos : 0 < calP (AdoorL M) (s13GK K M) 1 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast hpos
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hmul : 242 * Λ * Real.log 2 ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hgr (by linarith)
  have hlogmul : Real.log ((h : ℝ) * arcDen 12 H)
      = Real.log (h : ℝ) + Real.log (arcDen 12 H) :=
    Real.log_mul (by positivity) (by linarith)
  have hlt : Real.log ((h : ℝ) * arcDen 12 H)
      < Real.log ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
    rw [hlogmul, hlogarc, hlogP]
    nlinarith [hmul, hle, hhL, hΛL, hΛ1, hlog2]
  have hexp := Real.exp_lt_exp.mpr hlt
  rwa [Real.exp_log (by nlinarith : (0 : ℝ) < (h : ℝ) * arcDen 12 H), Real.exp_log hP0] at hexp

/-- **TWIN 8** — `s13_smallGradeFits_of_halfWindow_L_gk_h_b9` at the charge
(`s13_smallGradeFits_of_halfWindow_L_gk_h_L`) — SUPPLIER-SWAP (`s13_smallGradeFits_h_L`,
`s13_winFit_h_of_halfWindow_gen_L`), each at the tower floor.  BODY: the source's. -/
theorem s13_smallGradeFits_of_halfWindow_L_gk_h_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (_hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M : ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hfl : loglogFloor50 ≤ R.Hlo)
    (hfloor : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 50 + Lc ≤ Real.log (Real.log (H : ℝ)))
    (hhalf : (7 / 10 : ℝ) * ((doorRowFloorL M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
      ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 2) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      m4SmallGradeFits (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
        (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H :=
  fun H hlo hhi =>
    s13_smallGradeFits_h_L hh hhL hρ0 hρ1 hlo (hfloor H hlo hhi)
      (s13_winFit_h_of_halfWindow_gen_L hh hhL hfl hfloor hhalf H hlo hhi)

/-- **TWIN 10** — `s15ArmH_log_le_g12b` at the charge (`s15ArmH_log_le_L`).  STATEMENT: the flat
`s15Arm_log_le_L`'s binders (`FlatDoorEpsRung2.lean:2494`: the charge pin
`1/(838400·c) ≤ δ₀`, `1 ≤ Kb`, `Kc ≤ Kb`, `log Kb ≤ 197 + 20·Lc`, the gate `50 + Lc ≤ loglog H₊`)
plus `0 < h`, concluding the H-arm's bound with the flat `_L`'s SHRINKING slack
`H₊/(10^20·c²)` (the Z1 split pays exactly that slack).  BODY: the `_g12b`'s with its
`2^12·h²` block (`hc1 … hlogc`) replaced by the flat `_L` call at `c`; the `s15ArmH_le_mul` step
and the log split are the source's. -/
theorem s15ArmH_log_le_L {h : ℕ} (hh : 0 < h) {c δ₀ Kc Kb Lc : ℝ} (hc1 : 1 ≤ c) (hL0 : 0 ≤ Lc)
    (hLc : Real.log c ≤ Lc) (hδ₀ : 0 < δ₀) (hδpin : 1 / (838400 * c) ≤ δ₀)
    (hKc : 0 < Kc) (hKb1 : 1 ≤ Kb) (hKcb : Kc ≤ Kb)
    (hKbL : Real.log Kb ≤ 197 + 20 * Lc) {Hhi ω : ℕ} (hHhi : 4000000 ≤ Hhi)
    (hΛL : 50 + Lc ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ Real.log ((ω : ℕ) : ℝ) + Real.log (h : ℝ) + ((Hhi : ℕ) : ℝ) / (10 ^ 20 * c ^ 2) := by
  have hbase := s15Arm_log_le_L (ω := ω) hc1 hL0 hLc hδ₀ hδpin hKc hKb1 hKcb hKbL hHhi hΛL
  have hle := s15ArmH_le_mul hh δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω
  have hleR : ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ (h : ℝ) * ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hω0 : 0 ≤ Real.log ((ω : ℕ) : ℝ) := Real.log_natCast_nonneg ω
  have hh0 : 0 ≤ Real.log (h : ℝ) := Real.log_natCast_nonneg h
  have hc0 : (0 : ℝ) < c := by linarith
  have hHhi0 : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / (10 ^ 20 * c ^ 2) := by positivity
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

/-- **TWIN 11** — `s13_g2_jfloor_of_MSelect'_L_gk_shift36` at the charge
(`s13_g2_jfloor_of_MSelect'_L_gk_shiftL`): the conclusion's `+ 36 = 4·9` becomes `+ 4·L`, the
ONLY numeral that moves (the freeze's cell 8).  THE MARGIN, derived: `4·log 263 ≤ 24`
(`s13_log263_le_six`) and `L ≤ Λ` (the new binder `hLΛ`) give
`4·log 263 + 48·Λ + 4·L ≤ 24 + 52·Λ ≤ 242·Λ` at `Λ ≥ 1` (`190·Λ ≥ 24`).  BODY: the source's. -/
theorem s13_g2_jfloor_of_MSelect'_L_gk_shiftL (K : ℕ) {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime}
    {M : ℕ} {L : ℝ} (hLΛ : L ≤ Λ) (hΛ : 1 ≤ Λ) (hS : MSelect'_L_gk K Cg δ₀ Λ ρ R M) :
    4 * Real.log 263 + 48 * Λ + 4 * L ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
  have hlog := s13_log263_le_six
  have hdr : ((AdoorL M : ℕ) : ℝ) ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    have h : AdoorL M ≤ doorRowFloorL M := by
      rw [doorRowFloorL]
      calc AdoorL M = 1 * AdoorL M := (one_mul _).symm
        _ ≤ M * AdoorL M := Nat.mul_le_mul_right _ hS.hM
    exact_mod_cast h
  have hgr := hS.gRows
  nlinarith [hgr, hdr, hlog, hΛ, hLΛ]

/-! ## §J — THE CONDITIONAL AT THE CHARGE: THE ONE STRIDE-SPENDING SITE, PAID BY THE BINDER

The split at Z is Z1 (`zSplit_arm_L`, transcribed from the per-hop walk's scratch, three axioms
there) re-stated as `zSplit_arm_L2`; the multiplier-pin split `xceil_arm_split_mul_h_L` is FALSE at
a free twist and is not in this file. -/


/-- **Z1 — THE RIDER SPLIT WITH THE STRIDE'S `+L` RESERVED.**  `epsChain_arm_split_L`
(`FlatDoorEpsRung2.lean:2738`) with `+ L` on the left for every `0 ≤ L ≤ Lc`.  Room: the gate
`50 + Lc ≤ loglog H₊` gives `log H₊ ≥ e^{50}·e^{Lc}`, `e^{Lc} ≥ c` and `e^{Lc} ≥ 1 + L`, and
`H₊ = e^{log H₊} ≥ (log H₊)³/6`, so `H₊/c² ≥ 2^{150}·(1 + L)/6`, against a demand of
`250001·(log 2 + L)`. -/
theorem zSplit_arm_L {ε : ℚ} {c : ℕ} (hc1 : 1 ≤ c)
    (hcε : (1 : ℚ) / (500 * (c : ℚ)) ≤ ε) {Lc : ℝ} (hLc : Real.log ((c : ℕ) : ℝ) ≤ Lc)
    {Hhi : ℕ} (hH4 : 4000000 ≤ Hhi)
    (hll : 50 + Lc ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ)))
    {L : ℝ} (hL0 : 0 ≤ L) (hLLc : L ≤ Lc) :
    Real.log 2 + L ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ)
      - ((Hhi : ℕ) : ℝ) / (10 ^ 20 * ((c : ℕ) : ℝ) ^ 2) := by
  have hcR : (1 : ℝ) ≤ ((c : ℕ) : ℝ) := by exact_mod_cast hc1
  have hcpos : (0 : ℝ) < ((c : ℕ) : ℝ) := by linarith
  have hHR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hH4
  have hHpos : (0 : ℝ) < ((Hhi : ℕ) : ℝ) := by linarith
  have hlogHpos : (0 : ℝ) < Real.log ((Hhi : ℕ) : ℝ) := Real.log_pos (by linarith)
  -- ⟦THE PIN⟧ `ε² ≥ 1/(250000·c²)` — the landed derivation
  have hcQ : (1 : ℚ) ≤ ((c : ℕ) : ℚ) := by exact_mod_cast hc1
  have hqcap : (1 : ℚ) ≤ 500 * ((c : ℕ) : ℚ) * ε := by
    have h := (div_le_iff₀ (show (0 : ℚ) < 500 * ((c : ℕ) : ℚ) by linarith)).mp hcε
    calc (1 : ℚ) ≤ ε * (500 * ((c : ℕ) : ℚ)) := h
      _ = 500 * ((c : ℕ) : ℚ) * ε := by ring
  have hcapR : (1 : ℝ) ≤ 500 * ((c : ℕ) : ℝ) * (ε : ℝ) := by exact_mod_cast hqcap
  have hsq : (1 : ℝ) ≤ 250000 * ((c : ℕ) : ℝ) ^ 2 * (ε : ℝ) ^ 2 := by
    have h := one_le_pow₀ (n := 2) hcapR
    calc (1 : ℝ) ≤ (500 * ((c : ℕ) : ℝ) * (ε : ℝ)) ^ 2 := h
      _ = 250000 * ((c : ℕ) : ℝ) ^ 2 * (ε : ℝ) ^ 2 := by ring
  have hε2 : (1 : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2) ≤ (ε : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hsq]
  -- ⟦THE TOWER⟧ `log H₊ ≥ e^{50 + Lc} = e^{50}·e^{Lc}`
  have hy : Real.exp (50 + Lc) ≤ Real.log ((Hhi : ℕ) : ℝ) := by
    have h := Real.exp_le_exp.mpr hll
    rwa [Real.exp_log hlogHpos] at h
  have hE2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hE50 : (2 : ℝ) ^ 50 ≤ Real.exp 50 := by
    have h := pow_le_pow_left₀ (by norm_num) hE2 50
    rw [Real.exp_one_pow] at h
    exact_mod_cast h
  have hcexp : ((c : ℕ) : ℝ) ≤ Real.exp Lc := by
    have h := Real.exp_le_exp.mpr hLc
    rwa [Real.exp_log hcpos] at h
  have hLexp : 1 + L ≤ Real.exp Lc := by
    have h := Real.add_one_le_exp Lc
    linarith
  have hexppos : (0 : ℝ) < Real.exp Lc := Real.exp_pos _
  -- `(log H₊)³ ≥ (e^{50})³·(e^{Lc})³ ≥ 2^{150}·c²·(1 + L)`
  have hsplit : Real.exp (50 + Lc) = Real.exp 50 * Real.exp Lc := Real.exp_add _ _
  have hyy : Real.exp 50 * Real.exp Lc ≤ Real.log ((Hhi : ℕ) : ℝ) := by rw [← hsplit]; exact hy
  have hexp3 : ((c : ℕ) : ℝ) ^ 2 * (1 + L) ≤ (Real.exp Lc) ^ 3 := by
    have h1 : ((c : ℕ) : ℝ) ^ 2 ≤ (Real.exp Lc) ^ 2 := pow_le_pow_left₀ hcpos.le hcexp 2
    have h2 : ((c : ℕ) : ℝ) ^ 2 * (1 + L) ≤ (Real.exp Lc) ^ 2 * Real.exp Lc :=
      mul_le_mul h1 hLexp (by linarith) (by positivity)
    calc ((c : ℕ) : ℝ) ^ 2 * (1 + L) ≤ (Real.exp Lc) ^ 2 * Real.exp Lc := h2
      _ = (Real.exp Lc) ^ 3 := by ring
  have hE150 : (2 : ℝ) ^ 150 ≤ (Real.exp 50) ^ 3 := by
    have h := pow_le_pow_left₀ (by positivity) hE50 3
    calc (2 : ℝ) ^ 150 = ((2 : ℝ) ^ 50) ^ 3 := by norm_num
      _ ≤ (Real.exp 50) ^ 3 := h
  have hcube : (2 : ℝ) ^ 150 * (((c : ℕ) : ℝ) ^ 2 * (1 + L)) ≤ (Real.log ((Hhi : ℕ) : ℝ)) ^ 3 := by
    have h1 : (2 : ℝ) ^ 150 * (((c : ℕ) : ℝ) ^ 2 * (1 + L))
        ≤ (Real.exp 50) ^ 3 * (Real.exp Lc) ^ 3 :=
      mul_le_mul hE150 hexp3 (by positivity) (by positivity)
    have h2 : (Real.exp 50) ^ 3 * (Real.exp Lc) ^ 3 = (Real.exp 50 * Real.exp Lc) ^ 3 := by ring
    have h3 : (Real.exp 50 * Real.exp Lc) ^ 3 ≤ (Real.log ((Hhi : ℕ) : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hyy 3
    linarith
  -- `H₊ = e^{log H₊} ≥ (log H₊)³/6`
  have hH3 : (Real.log ((Hhi : ℕ) : ℝ)) ^ 3 / 6 ≤ ((Hhi : ℕ) : ℝ) := by
    have h := Real.pow_div_factorial_le_exp _ hlogHpos.le 3
    rw [Real.exp_log hHpos] at h
    have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h6] at h
    exact h
  -- ⟦THE MARGIN⟧ `H₊/c² ≥ 2^{150}·(1 + L)/6 ≥ 250001·(log 2 + L)`
  have hc2pos : (0 : ℝ) < ((c : ℕ) : ℝ) ^ 2 := by positivity
  have hHc : (2 : ℝ) ^ 150 / 6 * (1 + L) ≤ ((Hhi : ℕ) : ℝ) / ((c : ℕ) : ℝ) ^ 2 := by
    rw [le_div_iff₀ hc2pos]
    have : (2 : ℝ) ^ 150 / 6 * (1 + L) * ((c : ℕ) : ℝ) ^ 2
        = (2 : ℝ) ^ 150 * (((c : ℕ) : ℝ) ^ 2 * (1 + L)) / 6 := by ring
    rw [this]
    linarith [hcube, hH3]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hdemand : 250001 * (Real.log 2 + L) ≤ ((Hhi : ℕ) : ℝ) / ((c : ℕ) : ℝ) ^ 2 := by
    have h1 : 250001 * (Real.log 2 + L) ≤ 250001 * (1 + L) := by linarith
    have h2 : (250001 : ℝ) * (1 + L) ≤ (2 : ℝ) ^ 150 / 6 * (1 + L) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by linarith)
    linarith
  -- ⟦THE LANDED TAIL⟧ (`:2796–2810`), with `1/250001 ≤ 1/250000 − 1/10^20`
  have hsub : ((Hhi : ℕ) : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2)
      - ((Hhi : ℕ) : ℝ) / (10 ^ 20 * ((c : ℕ) : ℝ) ^ 2)
      = (((Hhi : ℕ) : ℝ) / ((c : ℕ) : ℝ) ^ 2) * (1 / 250000 - 1 / 10 ^ 20) := by
    field_simp
  have hlow : Real.log 2 + L ≤ ((Hhi : ℕ) : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2)
      - ((Hhi : ℕ) : ℝ) / (10 ^ 20 * ((c : ℕ) : ℝ) ^ 2) := by
    rw [hsub]
    have hq : (1 : ℝ) / 250001 ≤ 1 / 250000 - 1 / 10 ^ 20 := by norm_num
    have hpos : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / ((c : ℕ) : ℝ) ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hq hpos
    have h' : Real.log 2 + L ≤ ((Hhi : ℕ) : ℝ) / ((c : ℕ) : ℝ) ^ 2 * (1 / 250001) := by
      have := hdemand; nlinarith
    linarith
  have hstep : ((Hhi : ℕ) : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2)
      ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hε2 hHpos.le
    calc ((Hhi : ℕ) : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2)
        = 1 / (250000 * ((c : ℕ) : ℝ) ^ 2) * ((Hhi : ℕ) : ℝ) := by ring
      _ ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := h
  linarith [hlow, hstep]

/-- **Z1 RE-STATED FOR THE CONDITIONAL'S SPLIT (`zSplit_arm_L2`).**  `zSplit_arm_L` with its binder
`L ≤ Lc` widened to `L ≤ 2·Lc`, because the conditional reserves `log 2 + (log h + L)` and
`log h + L ≤ 2·L ≤ 2·Lc`.  Same proof shape; THE ONE CHANGED INEQUALITY, derived:
`1 + L ≤ 1 + 2·Lc ≤ 2·(1 + Lc) ≤ 2·e^{Lc}` (where Z1 had `1 + L ≤ e^{Lc}`), so the room halves:
`H₊/c² ≥ 2^{150}·(1 + L)/12` against the demand `250001·(log 2 + L) ≤ 250001·(1 + L)`, and
`2^{150}/12 = 1.1893·10^{44} ≥ 250001`.  No cap on `c`, `L` or `h` enters. -/
theorem zSplit_arm_L2 {ε : ℚ} {c : ℕ} (hc1 : 1 ≤ c)
    (hcε : (1 : ℚ) / (500 * (c : ℚ)) ≤ ε) {Lc : ℝ} (hLc : Real.log ((c : ℕ) : ℝ) ≤ Lc)
    {Hhi : ℕ} (hH4 : 4000000 ≤ Hhi)
    (hll : 50 + Lc ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ)))
    {L : ℝ} (hL0 : 0 ≤ L) (hL2 : L ≤ 2 * Lc) :
    Real.log 2 + L ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ)
      - ((Hhi : ℕ) : ℝ) / (10 ^ 20 * ((c : ℕ) : ℝ) ^ 2) := by
  have hcR : (1 : ℝ) ≤ ((c : ℕ) : ℝ) := by exact_mod_cast hc1
  have hcpos : (0 : ℝ) < ((c : ℕ) : ℝ) := by linarith
  have hHR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hH4
  have hHpos : (0 : ℝ) < ((Hhi : ℕ) : ℝ) := by linarith
  have hlogHpos : (0 : ℝ) < Real.log ((Hhi : ℕ) : ℝ) := Real.log_pos (by linarith)
  -- ⟦THE PIN⟧ `ε² ≥ 1/(250000·c²)` — the landed derivation
  have hcQ : (1 : ℚ) ≤ ((c : ℕ) : ℚ) := by exact_mod_cast hc1
  have hqcap : (1 : ℚ) ≤ 500 * ((c : ℕ) : ℚ) * ε := by
    have h := (div_le_iff₀ (show (0 : ℚ) < 500 * ((c : ℕ) : ℚ) by linarith)).mp hcε
    calc (1 : ℚ) ≤ ε * (500 * ((c : ℕ) : ℚ)) := h
      _ = 500 * ((c : ℕ) : ℚ) * ε := by ring
  have hcapR : (1 : ℝ) ≤ 500 * ((c : ℕ) : ℝ) * (ε : ℝ) := by exact_mod_cast hqcap
  have hsq : (1 : ℝ) ≤ 250000 * ((c : ℕ) : ℝ) ^ 2 * (ε : ℝ) ^ 2 := by
    have h := one_le_pow₀ (n := 2) hcapR
    calc (1 : ℝ) ≤ (500 * ((c : ℕ) : ℝ) * (ε : ℝ)) ^ 2 := h
      _ = 250000 * ((c : ℕ) : ℝ) ^ 2 * (ε : ℝ) ^ 2 := by ring
  have hε2 : (1 : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2) ≤ (ε : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hsq]
  -- ⟦THE TOWER⟧ `log H₊ ≥ e^{50 + Lc} = e^{50}·e^{Lc}`
  have hy : Real.exp (50 + Lc) ≤ Real.log ((Hhi : ℕ) : ℝ) := by
    have h := Real.exp_le_exp.mpr hll
    rwa [Real.exp_log hlogHpos] at h
  have hE2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hE50 : (2 : ℝ) ^ 50 ≤ Real.exp 50 := by
    have h := pow_le_pow_left₀ (by norm_num) hE2 50
    rw [Real.exp_one_pow] at h
    exact_mod_cast h
  have hcexp : ((c : ℕ) : ℝ) ≤ Real.exp Lc := by
    have h := Real.exp_le_exp.mpr hLc
    rwa [Real.exp_log hcpos] at h
  -- ⟦THE ONE CHANGED INEQUALITY⟧ `1 + L ≤ 1 + 2·Lc ≤ 2·(1 + Lc) ≤ 2·e^{Lc}`
  have hLexp : 1 + L ≤ 2 * Real.exp Lc := by
    have h := Real.add_one_le_exp Lc
    have hLc0 : 0 ≤ Lc := by linarith
    linarith
  have hexppos : (0 : ℝ) < Real.exp Lc := Real.exp_pos _
  -- `2·(log H₊)³ ≥ 2·(e^{50})³·(e^{Lc})³ ≥ 2^{150}·c²·(1 + L)`
  have hsplit : Real.exp (50 + Lc) = Real.exp 50 * Real.exp Lc := Real.exp_add _ _
  have hyy : Real.exp 50 * Real.exp Lc ≤ Real.log ((Hhi : ℕ) : ℝ) := by rw [← hsplit]; exact hy
  have hexp3 : ((c : ℕ) : ℝ) ^ 2 * (1 + L) ≤ 2 * (Real.exp Lc) ^ 3 := by
    have h1 : ((c : ℕ) : ℝ) ^ 2 ≤ (Real.exp Lc) ^ 2 := pow_le_pow_left₀ hcpos.le hcexp 2
    have h2 : ((c : ℕ) : ℝ) ^ 2 * (1 + L) ≤ (Real.exp Lc) ^ 2 * (2 * Real.exp Lc) :=
      mul_le_mul h1 hLexp (by linarith) (by positivity)
    calc ((c : ℕ) : ℝ) ^ 2 * (1 + L) ≤ (Real.exp Lc) ^ 2 * (2 * Real.exp Lc) := h2
      _ = 2 * (Real.exp Lc) ^ 3 := by ring
  have hE150 : (2 : ℝ) ^ 150 ≤ (Real.exp 50) ^ 3 := by
    have h := pow_le_pow_left₀ (by positivity) hE50 3
    calc (2 : ℝ) ^ 150 = ((2 : ℝ) ^ 50) ^ 3 := by norm_num
      _ ≤ (Real.exp 50) ^ 3 := h
  have hcube : (2 : ℝ) ^ 150 * (((c : ℕ) : ℝ) ^ 2 * (1 + L))
      ≤ 2 * (Real.log ((Hhi : ℕ) : ℝ)) ^ 3 := by
    have h1 : (2 : ℝ) ^ 150 * (((c : ℕ) : ℝ) ^ 2 * (1 + L))
        ≤ (Real.exp 50) ^ 3 * (2 * (Real.exp Lc) ^ 3) :=
      mul_le_mul hE150 hexp3 (by positivity) (by positivity)
    have h2 : (Real.exp 50) ^ 3 * (Real.exp Lc) ^ 3 = (Real.exp 50 * Real.exp Lc) ^ 3 := by ring
    have h3 : (Real.exp 50 * Real.exp Lc) ^ 3 ≤ (Real.log ((Hhi : ℕ) : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hyy 3
    linarith
  -- `H₊ = e^{log H₊} ≥ (log H₊)³/6`
  have hH3 : (Real.log ((Hhi : ℕ) : ℝ)) ^ 3 / 6 ≤ ((Hhi : ℕ) : ℝ) := by
    have h := Real.pow_div_factorial_le_exp _ hlogHpos.le 3
    rw [Real.exp_log hHpos] at h
    have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h6] at h
    exact h
  -- ⟦THE MARGIN⟧ `H₊/c² ≥ 2^{150}·(1 + L)/12 ≥ 250001·(log 2 + L)`
  have hc2pos : (0 : ℝ) < ((c : ℕ) : ℝ) ^ 2 := by positivity
  have hHc : (2 : ℝ) ^ 150 / 12 * (1 + L) ≤ ((Hhi : ℕ) : ℝ) / ((c : ℕ) : ℝ) ^ 2 := by
    rw [le_div_iff₀ hc2pos]
    have : (2 : ℝ) ^ 150 / 12 * (1 + L) * ((c : ℕ) : ℝ) ^ 2
        = (2 : ℝ) ^ 150 * (((c : ℕ) : ℝ) ^ 2 * (1 + L)) / 12 := by ring
    rw [this]
    linarith [hcube, hH3]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hdemand : 250001 * (Real.log 2 + L) ≤ ((Hhi : ℕ) : ℝ) / ((c : ℕ) : ℝ) ^ 2 := by
    have h1 : 250001 * (Real.log 2 + L) ≤ 250001 * (1 + L) := by linarith
    have h2 : (250001 : ℝ) * (1 + L) ≤ (2 : ℝ) ^ 150 / 12 * (1 + L) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by linarith)
    linarith
  -- ⟦THE LANDED TAIL⟧ (`:2796–2810`), with `1/250001 ≤ 1/250000 − 1/10^20`
  have hsub : ((Hhi : ℕ) : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2)
      - ((Hhi : ℕ) : ℝ) / (10 ^ 20 * ((c : ℕ) : ℝ) ^ 2)
      = (((Hhi : ℕ) : ℝ) / ((c : ℕ) : ℝ) ^ 2) * (1 / 250000 - 1 / 10 ^ 20) := by
    field_simp
  have hlow : Real.log 2 + L ≤ ((Hhi : ℕ) : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2)
      - ((Hhi : ℕ) : ℝ) / (10 ^ 20 * ((c : ℕ) : ℝ) ^ 2) := by
    rw [hsub]
    have hq : (1 : ℝ) / 250001 ≤ 1 / 250000 - 1 / 10 ^ 20 := by norm_num
    have hpos : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / ((c : ℕ) : ℝ) ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hq hpos
    have h' : Real.log 2 + L ≤ ((Hhi : ℕ) : ℝ) / ((c : ℕ) : ℝ) ^ 2 * (1 / 250001) := by
      have := hdemand; nlinarith
    linarith
  have hstep : ((Hhi : ℕ) : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2)
      ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hε2 hHpos.le
    calc ((Hhi : ℕ) : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2)
        = 1 / (250000 * ((c : ℕ) : ℝ) ^ 2) * ((Hhi : ℕ) : ℝ) := by ring
      _ ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := h
  linarith [hlow, hstep]

/-- **⟦H2→H3 AT THE CHARGE⟧ — `flat_conditional_generic_h_Z`.** G12b's
`flat_conditional_generic_h_g12b` (`StridePairReceiptG12b.lean:504`) on the Z forms.  THE ONE
STRIDE-SPENDING SITE: G12b's `hlogA : log a ≤ 9` (from `a ≤ 8103`) is DELETED and `hprod` reads
the form's binder `haL : log a ≤ L`; every other read of `a` is cap-free `ℕ` arithmetic,
transcribed.  THE RIDER at the gate `50 + Lc` (`Lc := log c + L`): the arm is priced by
`s15ArmH_log_le_L` (slack `H₊/(10^20·c²)`), the split by `zSplit_arm_L2` at `log h + L ≤ 2·Lc`,
and the four budget sites move `− 9 ↦ − L`.  THE FLOOR (rule (i), v1.1): `flatDesignBase A ≤ R.Hlo`
gives `3.2·A ≤ loglog H` on the window, hence the tower floor `50 + Lc ≤ loglog H` (and the block's
`3·Lc ≤ loglog H`) from `10 + 2·Lc ≤ A`, `162 ≤ A`.  THE FIRE: every capped supplier at its `_L`
twin (§F, §I).  No numeral cap on `h`, `c`, `L` or `a` is read. -/
theorem flat_conditional_generic_h_Z (h : ℕ) (hh : 0 < h) (ε : ℚ) (c : ℕ) (L : ℝ)
    (Awin : ℝ) (_hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hcap : FlatCapstoneFormHG_Z h ε c L Awin P) :
    FlatConditionalFormHG_Z h ε c L Awin P := by
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hCg, hε, hKc, hδ₀, hMfl, hCgle, hc1, hL0, hhL,
    hεpin, hcε, hδpin, hKcb, hMflb, hβ, hcapU⟩ := hcap
  refine ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl, hCgle, hc1, hL0, hhL,
    hεpin, hcε, hδpin, hKcb, hMflb, hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcapK⟩ := hcapU K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge hAL
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapK A hA26 hAge hAL
  refine ⟨Hcap, hCapLe, ?_⟩
  intro a U1floor g ha haL hg hU
  have hapos : 0 < a := ha
  have haR0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦THE CHARGE⟧ `Lc := log c + L` carries the twist; the count ceiling `Kb := 2^283·c^20·h`
  have hc0 : 0 ≤ Real.log (c : ℝ) := Real.log_natCast_nonneg c
  have hLc0 : 0 ≤ Real.log (c : ℝ) + L := by linarith
  have hhLc : Real.log (h : ℝ) ≤ Real.log (c : ℝ) + L := by linarith
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hh1R : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hKb1 : (1 : ℝ) ≤ 2 ^ 283 * (c : ℝ) ^ 20 * (h : ℝ) := by
    have h1 := epsRung2_one_le_Kb hc1
    nlinarith
  have hKbL : Real.log (2 ^ 283 * (c : ℝ) ^ 20 * (h : ℝ)) ≤ 197 + 20 * (Real.log (c : ℝ) + L) :=
    zCount_form (by linarith) le_rfl hc1 hh hhL hL0
  -- ⟦THE ONE GENUINE ESTIMATE, SPENT AT SHIFT `h`⟧ the substituted `a·(arm + g)` obeys the
  -- builder-side rider at the gate `50 + Lc`
  have hg' : XCeilRiderAt (50 + (Real.log (c : ℝ) + L)) ε
      (fun Hhi ω => a * (s15ArmH h δ₀ ρ Hhi ω + g Hhi ω)) := by
    intro Hhi ω hgate
    obtain ⟨hH4, hll, hωw⟩ := hgate
    have hHhiR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hH4
    -- ⟦THE ARM⟧ at the charge, slack `H₊/(10^20·c²)`
    have harm : Real.log ((s15ArmH h δ₀ ρ Hhi ω : ℕ) : ℝ)
        ≤ Real.log ((ω : ℕ) : ℝ) + Real.log (h : ℝ)
          + ((Hhi : ℕ) : ℝ) / (10 ^ 20 * (c : ℝ) ^ 2) := by
      rw [hρdef, hδsdef]
      exact s15ArmH_log_le_L hh hcR1 hLc0 (by linarith) hδ₀ hδpin hKc hKb1 hKcb hKbL hH4 hll
    -- ⟦THE SPLIT⟧ Z1 re-stated, reserving `log 2 + (log h + L)`, `log h + L ≤ 2·(log c + L)`
    have hlogh : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_natCast_nonneg h
    have hsplit := zSplit_arm_L2 hc1 hcε (Lc := Real.log (c : ℝ) + L) (by linarith) hH4 hll
      (L := Real.log (h : ℝ) + L) (by linarith) (by linarith)
    have hgb := hg Hhi ω ⟨hH4, hll, hωw⟩
    have hslack0 : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / (10 ^ 20 * (c : ℝ) ^ 2) := by positivity
    have harm' : Real.log ((s15ArmH h δ₀ ρ Hhi ω : ℕ) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - Real.log 2 - L := by linarith
    have hgb' : Real.log ((g Hhi ω : ℕ) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - Real.log 2 - L := by linarith
    have hsum : Real.log (((s15ArmH h δ₀ ρ Hhi ω + g Hhi ω : ℕ)) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - L :=
      le_trans (xt_log_add_le harm' hgb') (by linarith)
    -- ⟦THE MULTIPLIER — THE ONE STRIDE-SPENDING SITE⟧
    -- `log(a·(arm + g)) = log a + log(arm + g) ≤ L + (31/ε·H₊ − L)`, `haL : log a ≤ L`
    have hprod : Real.log (((a * (s15ArmH h δ₀ ρ Hhi ω + g Hhi ω) : ℕ)) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos (a * (s15ArmH h δ₀ ρ Hhi ω + g Hhi ω)) with hz | hp
      · rw [hz]
        simp only [Nat.cast_zero, Real.log_zero]
        have hεpos : (0 : ℚ) < ε := hε
        have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hεpos
        have hbig : (0 : ℝ) < 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) := by
          have : (0 : ℝ) < ((Hhi : ℕ) : ℝ) := by linarith
          positivity
        linarith
      · have hne : a * (s15ArmH h δ₀ ρ Hhi ω + g Hhi ω) ≠ 0 := hp.ne'
        have hsne : (0 : ℝ) < ((s15ArmH h δ₀ ρ Hhi ω + g Hhi ω : ℕ) : ℝ) := by
          have hs0 : 0 < s15ArmH h δ₀ ρ Hhi ω + g Hhi ω :=
            Nat.pos_of_ne_zero (fun hc => hne (by rw [hc, Nat.mul_zero]))
          exact_mod_cast hs0
        have hcast : (((a * (s15ArmH h δ₀ ρ Hhi ω + g Hhi ω) : ℕ)) : ℝ)
            = ((a : ℕ) : ℝ) * ((s15ArmH h δ₀ ρ Hhi ω + g Hhi ω : ℕ) : ℝ) := by
          push_cast; ring
        rw [hcast, Real.log_mul (ne_of_gt haR0) (ne_of_gt hsne)]
        linarith
    exact hprod
  obtain ⟨R, hReps, hU1, hRg, hstride, hRx, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl a U1floor (fun Hhi ω => s15ArmH h δ₀ ρ Hhi ω + g Hhi ω) ha haL hg'
  have hRarm : s15ArmH h δ₀ ρ R.Hhi R.ω ≤ R.x := by
    have hstep : s15ArmH h δ₀ ρ R.Hhi R.ω
        ≤ a * (s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω) := by
      have h1 : s15ArmH h δ₀ ρ R.Hhi R.ω
          ≤ 1 * (s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω) := by omega
      exact le_trans h1 (Nat.mul_le_mul_right _ ha)
    omega
  have hRgg : a * g R.Hhi R.ω ≤ R.x := by
    have hstep : a * g R.Hhi R.ω
        ≤ a * (s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω) :=
      Nat.mul_le_mul_left a (by omega)
    omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  -- ⟦THE DESIGN FLOOR ON THE REGIME (rule (i), v1.1)⟧ `flatDesignBase A ≤ R.Hlo`
  have hdesR : flatDesignBase A ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  have hdesH : ∀ H : ℕ, R.Hlo ≤ H → 3.2 * A ≤ Real.log (Real.log (H : ℝ)) := by
    intro H hlo
    have hDge : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
      rw [flatDesignBase]; exact Nat.le_ceil _
    have hBH : ((flatDesignBase A : ℕ) : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast le_trans hdesR hlo
    have h1 : Real.exp (Real.exp (3.2 * A)) ≤ (H : ℝ) := le_trans hDge hBH
    have h2 : Real.exp (3.2 * A) ≤ Real.log (H : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h
    have h := Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at h
  -- the TOWER floor: `50 + Lc ≤ 45 + A/2 ≤ 3.2·A` from `10 + 2·Lc ≤ A` and `162 ≤ A`
  have hfloor : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      50 + (Real.log (c : ℝ) + L) ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => by linarith [hdesH H hlo]
  -- the block's floor: `3·Lc ≤ 3.2·(10 + 2·Lc)/2 ≤ 3.2·A` at `0 ≤ Lc`
  have hfloor3 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      3 * (Real.log (c : ℝ) + L) ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => by linarith [hdesH H hlo]
  refine ⟨R, hReps, hHlo, hRgg, hstride, hRx, hRtow, ?_⟩
  intro M hKw hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor hKw
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hLcΛ : Real.log (c : ℝ) + L ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) := by
    linarith [hfloor R.Hhi R.hHlohi le_rfl]
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15ArmH_demoted h δ₀ ρ R.Hhi R.ω) hRarm
  have hhω : (0 : ℝ) ≤ (h : ℝ) * (R.ω : ℝ) := by positivity
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 ((h : ℝ) * (R.ω : ℝ)) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hhω ?_ hhi) (s15ArmH_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family at the inflated socket, arm read at `h·ω`
  have harith := s15_doorArithFrameRho_L_familyH'' (C₁ := fun _ : ℕ => (1 : ℝ)) hh hsel.hM
    hρ0 hρ1 hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧ — the register and its bridges are SOCKET-BLIND
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦slot 3⟧ the outer step over the `h`-free family, with `4·L` in the gate (G12b: `36`)
  have hLΛ : L ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) := by linarith
  have hj0raw : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * max 1 (arcDen 12 H)) + 4 * L ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    have hgate := s13_g2_jfloor_of_MSelect'_L_gk_shiftL K hLΛ (by linarith) hS
    have hbase := s13_g2_jfloor_gen (R := R)
      (F := ((doorRowFloorL M : ℕ) : ℝ) - 4 * L) le_rfl (by linarith)
    intro H hlo hhi
    linarith [hbase H hlo hhi]
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_of_MSelect'_L_gk_h_L hh hhL hj0raw)
    (s13_gate8_L_gk_h_L hh hLc0 hhLc hLcΛ le_rfl (by linarith) hsel.gRows)
    (s13_smallGradeFits_of_halfWindow_L_gk_h_L hh hLc0 hhLc hρ0 hρ1 hfl hfloor hsel.half)
    (fun H L q j A s hb => doorBaseFrame_at_socket_LH hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorLH_gk_L K hh hLc0 hhLc hfl hb hfloor hsel.hM hρ0 hρ1
        htow hsel.rho hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flatH_L hh hLc0 hhLc hfl hb hfloor htow hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flatH_L hh hLc0 hhLc hfl hb hρ0 hfloor htow hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flatH_L hh hLc0 hhLc hfl hb hρ0 hfloor htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM
        (s15_block_at_socketH_L_gk_L K hh hLc0 hhLc hb (hHreg H hb.1 hb.2.1)
          (hfloor3 H hb.1 hb.2.1) hsel.blk)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'H_L_gk_L K hh hLc0 hhLc hsel.hM hρ0 hρ1 (fun _ => le_rfl) hfloor
      (s15ArmH_rho hRarm) harith hsel.x0M (fun _ => le_rfl) hgrade
      (fun H L q j A s hb =>
        s15_block_at_socketH_L_gk_L K hh hLc0 hhLc hb (hHreg H hb.1 hb.2.1)
          (hfloor3 H hb.1 hb.2.1) hsel.blk))
    harith

/-! ## §K — V7 AT THE CHARGE

The kswin hop (H3→H4) is NOT in this file: its crossing spine head has no charge twin (see (c)
above).  v7 takes the kswin form as a hypothesis and is proved here. -/

/-- **⟦H4→H5 AT THE CHARGE⟧ — `flat_v7_generic_h_Z`.** G12b's `flat_v7_generic_h_g12b`
(`StridePairReceiptG12b.lean:811`) on the Z forms.  The two capped suppliers are rung 2's
h-generic ones AT THE TRUE `h` (rule (i)): `cofkR_cofactorSupply_L_gk_rated_L h hh` and
`s16_baseScaleCap96_LH_at_klevF_L (h := h) hh`, each at `Lc := log c + L`.  The supply's `obtain`
moves below the terminal's (as rung 2's v7 does), because the charge conjuncts are components of
the form.  THE DESIGN CONSTANT: G12b's eight arms verbatim inside rung 2's NINTH arm
`162 + 2·Lc`, OUTERMOST, which pays `10 + 2·Lc ≤ A` (the forms' binder),
`518 + 6·Lc ≤ loglog H₋` (`3.2·(162 + 2·Lc) = 518.4 + 6.4·Lc`), `cofkRThr + 2·Lc ≤ log H₋`
(`cofkRThr ≤ A`, `2·Lc ≤ A`, `2·A ≤ 3.2·A + 1 ≤ e^{3.2·A}`) and `Lc ≤ e^{3.2·A/2}`
(`Lc ≤ A ≤ 1.6·A + 1`). -/
theorem flat_v7_generic_h_Z (h : ℕ) (hh : 0 < h) (ε : ℚ) (c : ℕ) (L : ℝ)
    (P : ChowlaRegime → Prop)
    (hk : ∀ Awin : ℝ, S16BandLaneCBoundedLH_winU h Awin → FlatKswinFormHG_Z h ε c L Awin P)
    (A₀ : ℝ) :
    V7RatedFormHG_Z h ε c L P A₀ := by
  obtain ⟨Awin, -, hband⟩ := s16_bandLaneWinLH_holdsU h hh
  -- ⟦THE cs-FREE, Ks-WINDOWED FLAT TERMINAL⟧ V7Ks §5
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hc1, hL0, hhL, hεpin, hcε, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0,
    hC40, hmainU⟩ := hk Awin hband
  -- ⟦THE CHARGE⟧ `Lc := log c + L` carries the twist
  have hc0 : 0 ≤ Real.log (c : ℝ) := Real.log_natCast_nonneg c
  have hLc0 : 0 ≤ Real.log (c : ℝ) + L := by linarith
  have hhLc : Real.log (h : ℝ) ≤ Real.log (c : ℝ) + L := by linarith
  -- ⟦THE RATED CO-FACTOR SUPPLY⟧ at the TRUE `h` (rule (i)); still minted BEFORE the lever
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ :=
    cofkR_cofactorSupply_L_gk_rated_L h hh hLc0 hhLc
  -- ⟦THE DESIGN CONSTANT, EIGHT ARMS⟧ as in the source
  obtain ⟨A', hA'def⟩ : ∃ a : ℝ, a = max (16 * Real.log (1 / Ks) / 3) (max T₀
      (max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
        (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))))) := ⟨_, rfl⟩
  -- ⟦THE NINTH ARM⟧ `162 + 2·Lc`, OUTERMOST (rung 2's re-mint, `FlatDoorEpsRung2.lean:5367`)
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ,
      a = max (162 + 2 * (Real.log (c : ℝ) + L)) (max (armVt Kvt) A') := ⟨_, rfl⟩
  have hA162b : 162 + 2 * (Real.log (c : ℝ) + L) ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hAL : 10 + 2 * (Real.log (c : ℝ) + L) ≤ A := by linarith
  have harmA : armVt Kvt ≤ A := by
    rw [hAdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hlift : A' ≤ A := by
    rw [hAdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hKsA : 16 * Real.log (1 / Ks) / 3 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]; exact le_max_left _ _
  have hT₀A : T₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hA162 : (162 : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hA₀A : A₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAwinA : Awin ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_right (max (max A₀ 162) Awin)
      (cofkRThr Cq Cb Xsk Y0)) (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _)
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  -- ⟦THE `Ks` WINDOW, AT THE SEVENTH ARM⟧ as in the parent
  have hKswin : Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 := by linarith
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
    have h2 : Real.exp (3.2 * A) / 10 + 1 ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
      Real.add_one_le_exp _
    linarith
  have hopq : Hopq ≤ flatDesignBase A := by
    have h2 : Real.exp (3.2 * A) + 1 ≤ Real.exp (Real.exp (3.2 * A)) := Real.add_one_le_exp _
    have hR : ((Hopq : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by linarith
    have hceil := le_trans hR (Nat.le_ceil (Real.exp (Real.exp (3.2 * A))))
    rw [flatDesignBase]; exact_mod_cast hceil
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, hCt, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hAL hKw
  -- ⟦THE `T₀` ARM⟧ V7-C's discharge, as in the parent
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  refine ⟨Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hc1, hL0, hhL, hεpin, hcε, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A, ?_⟩
  -- ⟦Δ3⟧ the caller's floor and ceiling, forwarded into the kswin form
  intro U1floor a g hU hUceil ha haL hg
  obtain ⟨R, hReps, hHlo, hRg, hstride, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKswin U1floor
      (by rw [hbase hopq]; exact hU) hUceil a g ha haL hg
  -- ⟦THE BASE-SCALE CAP⟧ at `K = KlevF A`, as in the parent
  have heps500 : (1 : ℚ) / (500 * (h : ℚ)) ≤ R.eps := by rw [hReps]; exact hεpin
  have hxceil : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [hReps]; exact hRx
  -- ⟦THE RATED SUPPLY, WITH THE CUSHION PAID BY THE EIGHTH ARM⟧
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA26
  have heps500R : (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ) := by
    rw [hReps]
    have hq := (Rat.cast_le (K := ℝ)).mpr hεpin
    rwa [show (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) by
      push_cast; ring] at hq
  -- ⟦THE NINTH ARM, FIRST READER⟧ `3.2·(162 + 2·Lc) = 518.4 + 6.4·Lc ≥ 518 + 6·Lc`
  have h518 : (518 : ℝ) + 6 * (Real.log (c : ℝ) + L) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    linarith [hdes, hA162b, hLc0]
  have hfl : loglogFloor50 ≤ R.Hlo := by
    rw [hHlo]
    refine le_trans ?_ hU
    have hw := flatWitFloor_ll ε β A Hopq
    rwa [hbase hopq] at hw
  have hllreg := regime_Hfloor_of_loglogFloor50 hfl
  have hlogpos : (1 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hllreg.1 (by norm_num : (0 : ℝ) < 50) hllreg.2
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    have h1 := Real.exp_le_exp.mpr hdes
    rwa [Real.exp_log (by linarith)] at h1
  -- ⟦THE NINTH ARM, SECOND READER⟧ `cofkRThr ≤ A`, `2·Lc ≤ A`, `2·A ≤ 3.2·A + 1 ≤ e^(3.2A)`
  have hthrgate : cofkRThr Cq Cb Xsk Y0 + 2 * (Real.log (c : ℝ) + L)
      ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    linarith [hthrA, hlo, hexp1, hAL, hA162]
  have hKvtcush : 32 * Kvt
      + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
      ≤ Real.log (R.Hhi : ℝ) / 4 :=
    cofkR_cushion_of_armVt R hKvt0 harmA hlo
  have hcofsupply : S16CofactorSupply_LH_gk h (KlevF A) Cq R (flatDoorM A) :=
    hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush
  -- ⟦THE NINTH ARM, THIRD READER⟧ `Lc ≤ A ≤ 1.6·A + 1 ≤ e^(1.6·A)`
  have hexp16 : 3.2 * A / 2 + 1 ≤ Real.exp (3.2 * A / 2) := Real.add_one_le_exp _
  have hLt : Real.log (c : ℝ) + L ≤ Real.exp (3.2 * A / 2) := by linarith
  have hfireR : P R :=
    hfire2 hcofsupply
      (s16_baseScaleCap96_LH_at_klevF_L (h := h) hh hLc0 hhLc hA26 hLt (flatDoorM_one_le hA26)
        heps500 hxceil hwin)
  exact ⟨R, hReps, hHlo, hRg, hstride, hRtow, hdes, hwin, hfireR⟩

/-! ## §L — THE CROSSING CLOSURE AT THE CHARGE: HELPERS AND STONES

The crossing spine head's closure (the freeze's cell 17) reads the twist cap `log h ≤ 9` at eight
rows (the census build of this half, run before any twin was written): two spend it as the
DERIVED numeral `h ≤ 8103 = ⌊e^9⌋`, three through `capfloor_logq_le`'s conclusion
`log q ≤ log h + 12·loglog H` absorbed by a closing `linarith`, three as `h ≤ e^14`/`h ≤ e^9` read
into NUMERAL exponent stones.  At a free charge there is no numeral; the TOWER pays instead.
Below: three helpers (cell 18 and cell 19's `h ≤ e^Lc`), two cap-floor stones (cell 20) and four
exponent-generic stones (cell 19), each the numeral ancestor's body with the tower fact added —
every one FALSE without its tower binder (`Lc` is unbounded). -/

/-- The tower floor at the socket's `H`: `50 + Lc ≤ loglog H` from the floor at `R.Hlo` and
`R.Hlo ≤ H` (two monotone logs; `R.Hlo ≥ 4·10^6` from `R.hHlo_floor`). -/
theorem zTower_loglog_at_H {h : ℕ} {Lc : ℝ} {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (50 : ℝ) + Lc ≤ Real.log (Real.log (H : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hloR : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo
  have h1 : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) := Real.log_le_log (by linarith) hloR
  have hl0 : (0 : ℝ) < Real.log (R.Hlo : ℝ) := Real.log_pos (by linarith)
  have h2 : Real.log (Real.log (R.Hlo : ℝ)) ≤ Real.log (Real.log (H : ℝ)) :=
    Real.log_le_log hl0 h1
  linarith

/-- `h ≤ log H` at the charge: `h = exp (log h) ≤ exp Lc ≤ exp (loglog H) = log H`
(`0 < log H` from `H ≥ 4·10^6`).  This is what `h ≤ 8103 ≤ 10^21 ≤ log H` paid at the pin. -/
theorem zH_le_logH {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hhL : Real.log (h : ℝ) ≤ Lc) {H : ℕ}
    (hH : 4000000 ≤ H) (hLL : (50 : ℝ) + Lc ≤ Real.log (Real.log (H : ℝ))) :
    (h : ℝ) ≤ Real.log (H : ℝ) := by
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have h1 : Real.log (h : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by linarith
  have h2 := Real.exp_le_exp.mpr h1
  rwa [Real.exp_log hh0, Real.exp_log hlogH0] at h2

/-- `h ≤ exp Lc` from `log h ≤ Lc` — `h_le_exp_fourteen` at a free exponent; the same three
lines. -/
theorem zH_le_exp {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hhL : Real.log (h : ℝ) ≤ Lc) :
    (h : ℝ) ≤ Real.exp Lc := by
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hz := Real.exp_le_exp.mpr hhL
  rwa [Real.exp_log hh0] at hz

/-- ⟦`capfloor_lam_core_h_232` AT THE CHARGE⟧ — `floor1`'s `Λ`-leg with `8·(20 + Lc)` where it had
`8·(20 + 9) = 232`, under the tower's `Lc ≤ v/10^20`.  Off `capfloor_logv_le` (`log v ≤ v/10^10`):
`160 + 8·v/10^20 + 96·v/10^10 ≤ v/4` at `v ≥ 10^21` — room ×2.6·10^7. -/
theorem capfloor_lam_core_h_L {v Lc : ℝ} (hv : (10 : ℝ) ^ (21 : ℕ) ≤ v) (_hL0 : 0 ≤ Lc)
    (hLv : Lc ≤ v / 10 ^ 20) : 160 + 8 * Lc + 96 * Real.log v ≤ v / 4 := by
  have h := capfloor_logv_le hv
  norm_num at h hLv ⊢
  linarith [hLv]

/-- ⟦`capfloor_floor3_numeric_h_10` AT THE CHARGE⟧ — `floor3`'s numeric leg with the slack
`+ 1 + Lc` where it had `+10`.  BODY: the `_10` body with `hWv : W ≤ 2 * v + E + 1` (from
`12·log v ≤ 12·v/10^10 ≤ v` and `Lc ≤ v/10^20 ≤ v`) and `h1 : 2 * v + E + 1 ≤ v * E`
(the product `(E − 101)·(v − 1) ≥ 0`; `101·(v − 1) ≥ 2·v + 1` at `v ≥ 10^21`); everything after
`h1` verbatim. -/
theorem capfloor_floor3_numeric_h_L {v E W Lc : ℝ} (hv : (10 : ℝ) ^ (21 : ℕ) ≤ v)
    (hE : 101 ≤ E) (_hL0 : 0 ≤ Lc) (hLv : Lc ≤ v / 10 ^ 20)
    (hW : W ≤ 12 * Real.log v + E + 1 + Lc) :
    E * W ≤ E ^ (3 : ℕ) * (v / 4) ^ (4 : ℕ) := by
  have hlv := capfloor_logv_le hv
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le h21 hv
  have hE0 : (0 : ℝ) < E := by linarith
  have hvbig : (1000000000000000000000 : ℝ) ≤ v := le_trans (by norm_num) hv
  have hlv' : Real.log v ≤ v / 10000000000 := le_trans hlv (by norm_num)
  have hLv' : Lc ≤ v / 100000000000000000000 := le_trans hLv (by norm_num)
  have hWv : W ≤ 2 * v + E + 1 := by linarith
  have hvq : (v / 4) ^ (4 : ℕ) = v ^ (4 : ℕ) / 256 := by ring
  rw [hvq]
  have hv1 : (1 : ℝ) ≤ v := by linarith
  have h1 : 2 * v + E + 1 ≤ v * E := by
    nlinarith [mul_nonneg (sub_nonneg.2 hE) (sub_nonneg.2 hv1), hvbig, hE]
  have hxx : (65536 : ℝ) ≤ v * v := by nlinarith [hvbig]
  have hv3 : (256 : ℝ) ≤ v ^ (3 : ℕ) := by
    have hid : v ^ (3 : ℕ) = v * (v * v) := by ring
    rw [hid]; nlinarith [hvbig, hxx]
  have hfac : (1 : ℝ) ≤ E * v ^ (3 : ℕ) / 256 := by nlinarith [hv3, hE]
  have hpos : (0 : ℝ) ≤ E * (v * E) := by positivity
  have h2 : E * (v * E) ≤ E ^ (3 : ℕ) * (v ^ (4 : ℕ) / 256) := by
    calc E * (v * E) = (E * (v * E)) * 1 := by ring
      _ ≤ (E * (v * E)) * (E * v ^ (3 : ℕ) / 256) := mul_le_mul_of_nonneg_left hfac hpos
      _ = E ^ (3 : ℕ) * (v ^ (4 : ℕ) / 256) := by ring
  have hA : E * W ≤ E * (2 * v + E + 1) := mul_le_mul_of_nonneg_left hWv hE0.le
  have hB : E * (2 * v + E + 1) ≤ E * (v * E) := mul_le_mul_of_nonneg_left h1 hE0.le
  linarith

/-- ⟦`capeps_master_60` AT THE CHARGE⟧ — the `εr`-budget master line with the ceiling
`t ≤ 49 + Lc` under the tower floor `50 + Lc ≤ log u`.  Derivation:
`t ≤ 49 + Lc ≤ log u − 1 ≤ log Λ` (`log u ≤ 1 + log Λ`), so the LHS is `≤ 14·log Λ + 12
≤ 28·√Λ + 12`, against `(14/10000)·Λ ≥ (14/10000)·(2·10^10)·√Λ = 2.8·10^7·√Λ` — room ×10^6. -/
theorem capeps_master_L {u Λ t Lc : ℝ} (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hΛ : u / 2 ≤ Λ)
    (hL0 : 0 ≤ Lc) (hLu : (50 : ℝ) + Lc ≤ Real.log u) (ht : t ≤ 49 + Lc) :
    t + 12 * Real.log u + Real.log Λ ≤ 14 / 10000 * Λ := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hu2L : u ≤ 2 * Λ := by linarith
  have hlogu : Real.log u ≤ 1 + Real.log Λ := by
    have h1 : Real.log u ≤ Real.log (2 * Λ) := Real.log_le_log hu0 hu2L
    have h2 : Real.log (2 * Λ) = Real.log 2 + Real.log Λ :=
      Real.log_mul (by norm_num) (ne_of_gt hΛ0)
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith
  have hsq0 : (0 : ℝ) < Real.sqrt Λ := Real.sqrt_pos.mpr hΛ0
  have hsqrt : Real.log Λ ≤ 2 * Real.sqrt Λ := by
    have h := Real.log_le_sub_one_of_pos hsq0
    have hs : Real.log (Real.sqrt Λ) = Real.log Λ / 2 := Real.log_sqrt hΛ0.le
    rw [hs] at h; linarith
  have hsu : Real.sqrt Λ * Real.sqrt Λ = Λ := Real.mul_self_sqrt hΛ0.le
  have hLbig : (5 : ℝ) * 10 ^ (20 : ℕ) ≤ Λ := by
    have : (10 : ℝ) ^ (21 : ℕ) = 2 * (5 * 10 ^ (20 : ℕ)) := by norm_num
    linarith
  have hs10 : (2 : ℝ) * 10 ^ (10 : ℕ) ≤ Real.sqrt Λ := by
    nlinarith [hsu, hLbig, hsq0]
  -- ⟦AT THE CHARGE⟧ the ceiling `49 + Lc` is paid by the tower: `t ≤ log u − 1 ≤ log Λ`
  have ht' : t ≤ Real.log Λ := by linarith [ht, hLu, hlogu]
  nlinarith [hsqrt, hsu, hs10, hsq0, hlogu, ht']

/-- ⟦`capeps_expbound_60` AT THE CHARGE⟧ — the ceiling `t ≤ 49 + Lc` under the tower floor
`50 + Lc ≤ log u`.  BODY: `capeps_expbound_60`'s, with `hmas := capeps_master_L`. -/
theorem capeps_expbound_L {u μ t Lc : ℝ} (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (hL0 : 0 ≤ Lc) (hLu : (50 : ℝ) + Lc ≤ Real.log u)
    (ht : t ≤ 49 + Lc) :
    Real.exp t * u ^ (12 : ℕ) * Real.log μ ≤ μ ^ (theta293 - 1 / 500) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hmas := capeps_master_L hu hΛ hL0 hLu ht
  have hθ := s13_theta293_margin_lo
  have hlhs : Real.exp (t + 12 * Real.log u + Real.log (Real.log μ))
      = Real.exp t * u ^ (12 : ℕ) * Real.log μ := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hΛ0, ← capeps_pow12 hu0]
  rw [← hlhs, Real.rpow_def_of_pos hμ0]
  refine Real.exp_le_exp.mpr ?_
  have : 14 / 10000 * Real.log μ ≤ Real.log μ * (theta293 - 1 / 500) := by nlinarith
  linarith

/-- ⟦`capeps_bigexp_60` AT THE CHARGE⟧ — the ceiling `t ≤ 49 + Lc` under the tower floor
`50 + Lc ≤ log u`.  BODY: `capeps_bigexp_60`'s, with `hmas := capeps_master_L`. -/
theorem capeps_bigexp_L {u μ t Lc : ℝ} (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (hL0 : 0 ≤ Lc) (hLu : (50 : ℝ) + Lc ≤ Real.log u)
    (ht : t ≤ 49 + Lc) :
    Real.exp t * u ^ (12 : ℕ) * μ ^ 2 ≤ Real.exp (μ - Real.log μ / 500) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hΛbig : (5 : ℝ) * 10 ^ (20 : ℕ) ≤ Real.log μ := by
    have : (10 : ℝ) ^ (21 : ℕ) = 2 * (5 * 10 ^ (20 : ℕ)) := by norm_num
    linarith
  have hmas := capeps_master_L hu hΛ hL0 hLu ht
  have hlogΛ : 0 ≤ Real.log (Real.log μ) := Real.log_nonneg (by linarith)
  have hsq : (Real.log μ) ^ 2 / 4 ≤ μ := by
    have h := capeps_sq_le_exp hΛ0.le
    rwa [Real.exp_log hμ0] at h
  have h3Λ : 3 * Real.log μ ≤ μ := by nlinarith [hsq, hΛbig, hΛ0]
  have hμ2 : μ ^ 2 = Real.exp (2 * Real.log μ) := by
    rw [show (2 : ℝ) * Real.log μ = ((2 : ℕ) : ℝ) * Real.log μ by norm_num,
      ← Real.log_pow, Real.exp_log (pow_pos hμ0 2)]
  have hlhs : Real.exp (t + 12 * Real.log u + 2 * Real.log μ)
      = Real.exp t * u ^ (12 : ℕ) * μ ^ 2 := by
    rw [Real.exp_add, Real.exp_add, ← capeps_pow12 hu0, ← hμ2]
  rw [← hlhs]
  exact Real.exp_le_exp.mpr (by linarith)

/-- ⟦`capeps_Pbig_h_e20` AT THE CHARGE⟧ — the `p²` row's `1/P` leg with `e^(11 + Lc)` where it
had `e^20 = e^11·e^9`, under the tower floor `50 + Lc ≤ log u`.  BODY: `capeps_Pbig_h_e20`'s, with
the master line at `t = 11 + Lc ≤ 49 + Lc` and `20 ↦ 11 + Lc` in `hlhs`. -/
theorem capeps_Pbig_h_L {u μ Lc : ℝ} (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (hL0 : 0 ≤ Lc) (hLu : (50 : ℝ) + Lc ≤ Real.log u) :
    Real.exp (11 + Lc) * u ^ (12 : ℕ) * μ * μ ^ ((1 : ℝ) / 500)
      ≤ Real.exp (μ ^ (1 - theta293)) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hΛbig : (5 : ℝ) * 10 ^ (20 : ℕ) ≤ Real.log μ := by
    have : (10 : ℝ) ^ (21 : ℕ) = 2 * (5 * 10 ^ (20 : ℕ)) := by norm_num
    linarith
  have hmas := capeps_master_L hu hΛ hL0 hLu (by linarith : 11 + Lc ≤ 49 + Lc)
  have hlogΛ : 0 ≤ Real.log (Real.log μ) := Real.log_nonneg (by linarith)
  have hθ32 : theta293 < 1 / 32 := theta293_lt_one_div_32
  have hθ0 : (0 : ℝ) < theta293 := theta293_pos
  have hrw : μ ^ (1 - theta293) = Real.exp ((1 - theta293) * Real.log μ) := by
    rw [Real.rpow_def_of_pos hμ0]; ring_nf
  have hhalf : Real.exp (Real.log μ / 2) ≤ μ ^ (1 - theta293) := by
    rw [hrw]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hsq : (Real.log μ / 2) ^ 2 / 4 ≤ Real.exp (Real.log μ / 2) :=
    capeps_sq_le_exp (by linarith)
  have hbig : 2 * Real.log μ ≤ μ ^ (1 - theta293) := by nlinarith [hsq, hhalf, hΛbig, hΛ0]
  have h500 : μ ^ ((1 : ℝ) / 500) = Real.exp (Real.log μ / 500) := by
    rw [Real.rpow_def_of_pos hμ0]; ring_nf
  have hlhs : Real.exp (11 + Lc + 12 * Real.log u + Real.log μ + Real.log μ / 500)
      = Real.exp (11 + Lc) * u ^ (12 : ℕ) * μ * μ ^ ((1 : ℝ) / 500) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, ← capeps_pow12 hu0, Real.exp_log hμ0,
      ← h500]
  rw [← hlhs]
  exact Real.exp_le_exp.mpr (le_trans (by linarith) hbig)

/-! ## §M — THE CROSSING CLOSURE AT THE CHARGE: THE 44 TWINS (the freeze's cell 17)

The closure of the crossing spine head, in dependency order (leaves first).  Each twin is its
source at `log h ≤ 9` (or the raised-cap row) with the cap binder replaced by the charge
`{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee replaced by its `_L` twin (rung 2's eight
cap-grid leaves and §I's `s13_socketBase_loglogA_LH_L` are CALLED, not re-written), and the tower
floor `hflL : 50 + Lc ≤ loglog R.Hlo` added where the body or a callee reads it.  Eight rows read
the cap and are re-cut through §L; each prints its moved numeral.  The rest are transcriptions. -/

/-- `capfloor_muLambda_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap binder
becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor `hflL`
passed down.  BODY: the source's, verbatim. -/
theorem capfloor_muLambda_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    Real.exp (Real.log (H : ℝ) / 4) ≤ Real.log (5 * Tann + 1) ∧
      Real.log (H : ℝ) / 4 ≤ Real.log (Real.log (5 * Tann + 1)) := by
  obtain ⟨hv, hm, hTpos, hlogT⟩ := capfloor_core_L hh hL0 hhL hfl hb hAN hTlo hflL
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  have hv0 : (0 : ℝ) < Real.log (H : ℝ) := by nlinarith [hv, (by positivity :
    (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ))]
  -- `√H = e^{v/2} = e^{v/4}·e^{v/4}`
  have hsq : Real.sqrt (H : ℝ) = Real.exp (Real.log (H : ℝ) / 2) := capfloor_sqrt_eq_exp hH0
  have hsplit : Real.exp (Real.log (H : ℝ) / 2)
      = Real.exp (Real.log (H : ℝ) / 4) * Real.exp (Real.log (H : ℝ) / 4) := by
    rw [← Real.exp_add]; ring_nf
  have hq0 : (0 : ℝ) < Real.exp (Real.log (H : ℝ) / 4) := Real.exp_pos _
  have hq2 : (2 : ℝ) ≤ Real.exp (Real.log (H : ℝ) / 4) := by
    have hz := Real.add_one_le_exp (Real.log (H : ℝ) / 4)
    have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    linarith
  -- `log T_ann ≥ ½ log Nd ≥ ½ √H = ½ e^{v/2} ≥ e^{v/4}`
  have hstep : Real.exp (Real.log (H : ℝ) / 4) ≤ Real.log Tann := by
    have h1 : Real.sqrt (H : ℝ) / 2 ≤ Real.log Tann := by linarith
    rw [hsq, hsplit] at h1
    nlinarith [h1, hq0, hq2]
  have hmono : Real.log Tann ≤ Real.log (5 * Tann + 1) :=
    Real.log_le_log hTpos (by linarith)
  refine ⟨le_trans hstep hmono, ?_⟩
  have hpos : (0 : ℝ) < Real.exp (Real.log (H : ℝ) / 4) := Real.exp_pos _
  have hz := Real.log_le_log hpos (le_trans hstep hmono)
  rwa [Real.log_exp] at hz

set_option maxHeartbeats 800000 in
-- as the source: the LHS re-derives at the inflated cap's `log H ^ 13`
/-- ⟦`capfloor_floor4_sharp_LH` AT THE CHARGE⟧ — the twin at `log h ≤ 9` spent `h ≤ 8103 ≤ 10^21
≤ log H` (`8103 = ⌊e^9⌋`); at the charge that numeral does not exist, and the tower pays it:
`h ≤ exp Lc ≤ log H` (`zH_le_logH`, `zTower_loglog_at_H`).  Callees `capfloor_core_L`,
`capfloor_muLambda_LH_L`.  Everything after `hhle` is the source's, verbatim (it is `h`-free). -/
theorem capfloor_floor4_sharp_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hKs : Real.exp (-(3 * Real.log (H : ℝ) / 16)) ≤ Ks) :
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core_L hh hL0 hhL hfl hb hAN hTlo hflL
  obtain ⟨hmu, hLam⟩ := capfloor_muLambda_LH_L hh hL0 hhL hfl hb hflL hAN hTlo
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le h21 hv
  have hv256 : (256 : ℝ) ≤ Real.log (H : ℝ) := le_trans (by norm_num) hv
  have hnum1 : (1 : ℝ) ≤ (10 : ℝ) ^ (21 : ℕ) := by norm_num
  have hv1 : (1 : ℝ) ≤ Real.log (H : ℝ) := by linarith
  -- ⟦LHS AT THE INFLATED CAP⟧ `q ≤ h·arcDen 12 H ≤ log H ^ 13`, exactly H2c's step
  -- ⟦AT THE CHARGE⟧ `h ≤ 8103 ≤ 10^21 ≤ log H` ↦ `h ≤ exp Lc ≤ log H`, paid by the tower
  have hhle : (h : ℝ) ≤ Real.log (H : ℝ) :=
    zH_le_logH hh hhL (le_trans R.hHlo_floor hb.1) (zTower_loglog_at_H hb hflL)
  have hqA : (q : ℝ) ≤ Real.log (H : ℝ) ^ (13 : ℕ) := by
    have hz := hb.2.2.2.2.1
    have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
      rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [harcpow] at hz
    have hp12 : (0 : ℝ) ≤ Real.log (H : ℝ) ^ (12 : ℕ) := by positivity
    have hid : Real.log (H : ℝ) ^ (13 : ℕ)
        = Real.log (H : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ) := by ring
    calc (q : ℝ) ≤ (h : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ) := hz
      _ ≤ Real.log (H : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ) :=
          mul_le_mul_of_nonneg_right hhle hp12
      _ = Real.log (H : ℝ) ^ (13 : ℕ) := hid.symm
  have hstep1 : (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ (Real.log (H : ℝ) ^ (13 : ℕ)) ^ ((1 : ℝ) / 16) :=
    Real.rpow_le_rpow (Nat.cast_nonneg q) hqA (by norm_num)
  have hstep2 : (Real.log (H : ℝ) ^ (13 : ℕ)) ^ ((1 : ℝ) / 16)
      = Real.log (H : ℝ) ^ ((13 : ℝ) / 16) := by
    rw [← Real.rpow_natCast (Real.log (H : ℝ)) 13, ← Real.rpow_mul hv0.le]
    norm_num
  have hstep3 : Real.log (H : ℝ) ^ ((13 : ℝ) / 16) ≤ Real.log (H : ℝ) := by
    calc Real.log (H : ℝ) ^ ((13 : ℝ) / 16) ≤ Real.log (H : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
      _ = Real.log (H : ℝ) := Real.rpow_one _
  have hLHS : (q : ℝ) ^ ((1 : ℝ) / 16) ≤ Real.log (H : ℝ) := by
    rw [hstep2] at hstep1; linarith
  -- ⟦RHS leg 1⟧ the FULL exponential, as the landed sharp twin
  have hleg1 : Real.exp (3 * Real.log (H : ℝ) / 16)
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4) := by
    have hstep : (Real.exp (Real.log (H : ℝ) / 4)) ^ ((3 : ℝ) / 4)
        ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (Real.exp_nonneg _) hmu (by norm_num)
    have heq : (Real.exp (Real.log (H : ℝ) / 4)) ^ ((3 : ℝ) / 4)
        = Real.exp (Real.log (H : ℝ) / 4 * (3 / 4)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [heq] at hstep
    refine le_trans (Real.exp_le_exp.mpr ?_) hstep
    linarith
  have hleg2 : (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
      ≤ (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hLam 4
  have hexp0 : (0 : ℝ) < Real.exp (3 * Real.log (H : ℝ) / 16) := Real.exp_pos _
  have hlegs : Real.exp (3 * Real.log (H : ℝ) / 16) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) :=
    mul_le_mul hleg1 hleg2 (by positivity) (le_trans hexp0.le hleg1)
  have hKs0 : (0 : ℝ) < Ks := lt_of_lt_of_le (Real.exp_pos _) hKs
  have hcancel : (1 : ℝ) ≤ Ks * Real.exp (3 * Real.log (H : ℝ) / 16) := by
    have hprod : Real.exp (-(3 * Real.log (H : ℝ) / 16))
        * Real.exp (3 * Real.log (H : ℝ) / 16) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [mul_le_mul_of_nonneg_right hKs hexp0.le, hprod]
  have hpow : (256 : ℝ) ≤ Real.log (H : ℝ) ^ (3 : ℕ) := by
    have hid : Real.log (H : ℝ) ^ (3 : ℕ)
        = Real.log (H : ℝ) * (Real.log (H : ℝ) * Real.log (H : ℝ)) := by ring
    rw [hid]; nlinarith [hv256]
  have hvq : Real.log (H : ℝ) ≤ (Real.log (H : ℝ) / 4) ^ (4 : ℕ) := by
    have hid : (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
        = Real.log (H : ℝ) * (Real.log (H : ℝ) ^ (3 : ℕ) / 256) := by ring
    rw [hid]; nlinarith [hpow, hv0]
  have hbase : (0 : ℝ) ≤ (Real.log (H : ℝ) / 4) ^ (4 : ℕ) := by positivity
  have hgrow : (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
      ≤ Ks * Real.exp (3 * Real.log (H : ℝ) / 16) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ) := by
    nlinarith [hcancel, hbase]
  have hfinal : Ks * (Real.exp (3 * Real.log (H : ℝ) / 16) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ))
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) :=
    mul_le_mul_of_nonneg_left hlegs hKs0.le
  have hassoc : Ks * (Real.exp (3 * Real.log (H : ℝ) / 16) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ))
      = Ks * Real.exp (3 * Real.log (H : ℝ) / 16) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ) := by
    ring
  rw [hassoc] at hfinal
  linarith [hLHS, hvq, hgrow, hfinal]

/-- `s13CapGrid_logX_eight_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13CapGrid_logX_eight_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    8 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  linarith [s13CapGrid_mu_2000_L hh hL0 hhL hfl hb hflL]

/-- ⟦`s13CapGrid_q_logX_LH` AT THE CHARGE⟧ — THE ONE RE-DERIVATION of this half; the conclusion
`q ≤ (log (A + s))^12` is UNCHANGED.  The twin at `log h ≤ 9` spent `8103·(x/531441) ≤ x`, i.e.
`e^Lc ≤ 3^12`, FALSE past `Lc > 13.18`.  The tower pays it instead, `μ' := log (A + s)`:
`q ≤ h·(log H)^12` and `h ≤ log H` (`zH_le_logH`) give `q ≤ (log H)^13`;
`log H/2 ≤ log μ'` (`s13CapGrid_Lambda_sharp_L`), `2000 ≤ μ'`; with `σ := √μ'`, `44 ≤ σ`
(`44² = 1936`) and `log μ' ≤ 2σ` (`log σ ≤ σ − 1`), so `log H ≤ 4σ`;
`(4σ)^13 = 4^13·σ^13 ≤ σ^11·σ^13 = μ'^12` (`4^13 = 67108864 ≤ 44^11 ≈ 1.2·10^18`, room
`×1.8·10^10`). -/
theorem s13CapGrid_q_logX_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (q : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ 12 := by
  have hq := hb.2.2.2.2.1
  have harc : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg (by linarith)
  -- ⟦AT THE CHARGE⟧ `h ≤ log H` (the tower), so `q ≤ h·(log H)^12 ≤ (log H)^13`
  have hhle : (h : ℝ) ≤ Real.log (H : ℝ) :=
    zH_le_logH hh hhL hH4 (zTower_loglog_at_H hb hflL)
  rw [harc] at hq
  have hq13 : (q : ℝ) ≤ Real.log (H : ℝ) ^ (13 : ℕ) := by
    calc (q : ℝ) ≤ (h : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ) := hq
      _ ≤ Real.log (H : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ) :=
          mul_le_mul_of_nonneg_right hhle (by positivity)
      _ = Real.log (H : ℝ) ^ (13 : ℕ) := by ring
  -- `log H / 2 ≤ log μ'` and `2000 ≤ μ'`, `μ' := log (A + s)`
  have hsharp : Real.log (H : ℝ) / 2 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    s13CapGrid_Lambda_sharp_L hh hL0 hhL hfl hb hflL
  have hmu2000 : (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    s13CapGrid_mu_2000_L hh hL0 hhL hfl hb hflL
  set μ' : ℝ := Real.log (((A + s : ℕ)) : ℝ) with hμ'
  have hμ0 : (0 : ℝ) < μ' := by linarith
  -- `σ := √μ'`, `σ·σ = μ'`, `44 ≤ σ` (`44² = 1936 ≤ 2000`)
  set σ : ℝ := Real.sqrt μ' with hσdef
  have hσσ : σ * σ = μ' := Real.mul_self_sqrt hμ0.le
  have hσ0 : (0 : ℝ) < σ := Real.sqrt_pos.mpr hμ0
  have hσ44 : (44 : ℝ) ≤ σ := by nlinarith [hσσ, hσ0]
  -- `log μ' ≤ 2σ` (`capeps_master_60`'s `hsqrt` block), so `log H ≤ 2·log μ' ≤ 4σ`
  have hlog : Real.log μ' ≤ 2 * σ := by
    have h := Real.log_le_sub_one_of_pos hσ0
    have hs : Real.log σ = Real.log μ' / 2 := Real.log_sqrt hμ0.le
    rw [hs] at h; linarith
  have hHs : Real.log (H : ℝ) ≤ 4 * σ := by linarith
  have hpow : Real.log (H : ℝ) ^ (13 : ℕ) ≤ (4 * σ) ^ (13 : ℕ) := pow_le_pow_left₀ hlogH0 hHs 13
  -- `4^13 = 67108864 ≤ 44^11 ≈ 1.2·10^18 ≤ σ^11`, and `σ^11·σ^13 = (σ·σ)^12 = μ'^12`
  have hσ11 : (4 : ℝ) ^ (13 : ℕ) ≤ σ ^ (11 : ℕ) :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hσ44 11)
  have hfin : (4 * σ) ^ (13 : ℕ) ≤ μ' ^ (12 : ℕ) := by
    have h1 : (4 * σ) ^ (13 : ℕ) ≤ σ ^ (11 : ℕ) * σ ^ (13 : ℕ) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right hσ11 (by positivity)
    have h2 : σ ^ (11 : ℕ) * σ ^ (13 : ℕ) = μ' ^ (12 : ℕ) := by rw [← hσσ]; ring
    linarith
  calc (q : ℝ) ≤ Real.log (H : ℝ) ^ (13 : ℕ) := hq13
    _ ≤ (4 * σ) ^ (13 : ℕ) := hpow
    _ ≤ μ' ^ (12 : ℕ) := hfin

/-- `s13CapGrid_logqT_L_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13CapGrid_logqT_L_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T)
    (hThi : 2 * T ≤ (((A + s : ℕ)) : ℝ)) :
    Real.log ((q : ℝ) * (2 * T)) ≤ s13Lr (A + s) := by
  set Nd : ℕ := A + s with hNd
  set μ : ℝ := Real.log ((Nd : ℕ) : ℝ) with hμdef
  have hμ2000 : (2000 : ℝ) ≤ μ := s13CapGrid_mu_2000_L hh hL0 hhL hfl hb hflL
  have hΛ21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log μ := s13CapGrid_Lambda_lo_L hh hL0 hhL hfl hb hflL
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hNd1 : 1 ≤ Nd := by omega
  have hNdR : (1 : ℝ) ≤ ((Nd : ℕ) : ℝ) := by exact_mod_cast hNd1
  have hq1 : 1 ≤ q := hb.2.2.2.1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hpow0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hT0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) := by positivity
    linarith
  -- `log q ≤ 12Λ`
  have hqlog : Real.log (q : ℝ) ≤ 12 * Real.log μ := by
    have hq12 : (q : ℝ) ≤ μ ^ (12 : ℕ) := s13CapGrid_q_logX_LH_L hh hL0 hhL hfl hb hflL
    have := Real.log_le_log (by linarith) hq12
    rwa [Real.log_pow] at this
    -- `Real.log_pow : log (x ^ n) = n * log x`
  have hTlog : Real.log (2 * T) ≤ μ := Real.log_le_log hT0 hThi
  have hsum : Real.log ((q : ℝ) * (2 * T)) ≤ 12 * Real.log μ + μ := by
    rw [Real.log_mul (by linarith) (by linarith)]
    linarith
  -- `2μ ≤ μ^{11/10}`
  have hΛ0 : (0 : ℝ) < Real.log μ := by
    have : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    linarith
  have htwo : (2 : ℝ) ≤ μ ^ ((1 : ℝ) / 10) := by
    have hone : (1 : ℝ) ≤ Real.log μ * (1 / 10) := by nlinarith [hΛ21]
    have := Real.add_one_le_exp (Real.log μ * (1 / 10))
    rw [Real.rpow_def_of_pos hμ0]
    linarith
  have hLr : s13Lr Nd = μ * μ ^ ((1 : ℝ) / 10) := by
    rw [s13Lr, ← hμdef, ← Real.rpow_one_add' hμ0.le (by norm_num)]
    norm_num
  have h2μ : 2 * μ ≤ s13Lr Nd := by
    rw [hLr]; nlinarith [htwo, hμ0]
  -- `12Λ ≤ μ`
  have hΛsq : Real.log μ ≤ Real.sqrt μ := capgrid_log_le_sqrt (by linarith)
  have hs2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ0.le
  have hs0 : (0 : ℝ) < Real.sqrt μ := Real.sqrt_pos.mpr hμ0
  have hs40 : (40 : ℝ) ≤ Real.sqrt μ := by nlinarith [hs2, hs0]
  have h12 : 12 * Real.log μ ≤ μ := by nlinarith [hΛsq, hs2, hs40, hs0]
  linarith

/-- `s13CapGrid_Q2_reg_LH_gk` at the charge — TRANSPORT of the twin at `log h ≤ 9`: its cap binder
is unused, and so is the charge; no floor.  BODY: the source's, verbatim. -/
theorem s13CapGrid_Q2_reg_LH_gk_L {h : ℕ} (_hh : 0 < h) {Lc : ℝ} (_hL0 : 0 ≤ Lc)
    (_hhL : Real.log (h : ℝ) ≤ Lc)
    (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} (hM : 1 ≤ M)
    (hb : SocketBaseLH h R M H L q j A s) (hblock : s13BlockFloor_L_gk K M ≤ A + s) :
    Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) :=
  (s13_doorRowZeroBase_five_L_gk K hM hblock hb.2.2.2.2.2.2.1).2.1

/-- `s13CapGrid_twoj_le_H_LH` at the charge — TRANSPORT of the twin at `log h ≤ 9`: its cap binder
is unused, and so is the charge; no floor.  BODY: the source's, verbatim. -/
theorem s13CapGrid_twoj_le_H_LH_L {h : ℕ} (_hh : 0 < h) {Lc : ℝ} (_hL0 : 0 ≤ Lc)
    (_hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseLH h R M H L q j A s) : 2 ^ j ≤ H := by
  have hjL : j ≤ Nat.log 2 L := hb.2.2.2.2.2.1
  have hLH : L ≤ H := hb.2.2.1
  have hH : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · subst hL0
    have hj : j = 0 := by simpa using hjL
    subst hj
    simpa using (by omega : 1 ≤ H)
  · exact le_trans (le_trans (Nat.pow_le_pow_right (by norm_num) hjL)
      (Nat.pow_log_le_self 2 (by omega))) hLH

/-- `s13CapGrid_logTann_lo_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13CapGrid_logTann_lo_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    Real.log (((A + s : ℕ)) : ℝ) - 2 * Real.log (Real.log (((A + s : ℕ)) : ℝ))
      ≤ Real.log (2 * T) := by
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hNd1 : (1 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    have : 1 ≤ A + s := by omega
    exact_mod_cast this
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hpow0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have h2j : ((2 ^ j : ℕ) : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast s13CapGrid_twoj_le_H_LH_L hh hL0 hhL hb
  have hdiv : (((A + s : ℕ)) : ℝ) / (H : ℝ) ≤ (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left (by linarith) hpow0 h2j
  have hdiv0 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) / (H : ℝ) := by positivity
  have hle : (((A + s : ℕ)) : ℝ) / (H : ℝ) ≤ 2 * T := by linarith
  have hlog := Real.log_le_log hdiv0 hle
  rw [Real.log_div (by linarith) (by linarith)] at hlog
  have hLam := s13CapGrid_Lambda_sharp_L hh hL0 hhL hfl hb hflL
  linarith

/-- `s13CapGrid_Tann_one_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13CapGrid_Tann_one_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) : (1 : ℝ) < 2 * T := by
  set μ : ℝ := Real.log (((A + s : ℕ)) : ℝ) with hμdef
  have hμ2000 : (2000 : ℝ) ≤ μ := s13CapGrid_mu_2000_L hh hL0 hhL hfl hb hflL
  have hΛ21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log μ := s13CapGrid_Lambda_lo_L hh hL0 hhL hfl hb hflL
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hsq : Real.log μ ≤ Real.sqrt μ := capgrid_log_le_sqrt (by linarith)
  have hs2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ0.le
  have hs0 : (0 : ℝ) < Real.sqrt μ := Real.sqrt_pos.mpr hμ0
  have hs40 : (40 : ℝ) ≤ Real.sqrt μ := by nlinarith [hs2, hs0]
  have h2Λ : 2 * Real.log μ ≤ μ / 2 := by nlinarith [hsq, hs2, hs40, hs0]
  have hlow := s13CapGrid_logTann_lo_LH_L hh hL0 hhL hfl hb hflL hTlo
  have hlog0 : (0 : ℝ) < Real.log (2 * T) := by rw [← hμdef] at hlow; linarith
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hNd1 : (1 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    have : 1 ≤ A + s := by omega
    exact_mod_cast this
  have hT0 : (0 : ℝ) < 2 * T := by
    have h1 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) := by positivity
    linarith
  have := Real.exp_lt_exp.mpr hlog0
  rwa [Real.exp_zero, Real.exp_log hT0] at this

/-- `s13CapGrid_BT_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap binder
becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor `hflL`
passed down.  BODY: the source's, verbatim. -/
theorem s13CapGrid_BT_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    ∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
      ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
        ≤ (q : ℝ) * (2 * T) := by
  intro i hi
  set μ : ℝ := Real.log (((A + s : ℕ)) : ℝ) with hμdef
  have hμ2000 : (2000 : ℝ) ≤ μ := s13CapGrid_mu_2000_L hh hL0 hhL hfl hb hflL
  have hΛ21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log μ := s13CapGrid_Lambda_lo_L hh hL0 hhL hfl hb hflL
  have hΛ100 : (100 : ℝ) ≤ Real.log μ := by
    have : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    nlinarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hb3 := s13CapGrid_B3 (Nd := A + s) hμ2000 hΛ21 i hi
  have hb3R : (3 : ℝ)
      ≤ ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ) := by
    exact_mod_cast hb3
  have hT1 : (1 : ℝ) < 2 * T := s13CapGrid_Tann_one_LH_L hh hL0 hhL hfl hb hflL hTlo
  have hq1 : 1 ≤ q := hb.2.2.2.1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have htop := s13CapGrid_logBase_le (Nd := A + s) hμ2000 hΛ21 hi
  have hlow := s13CapGrid_logTann_lo_LH_L hh hL0 hhL hfl hb hflL hTlo
  rw [← hμdef] at hlow
  have hnum := capgrid_kappa_numeric hμ2000 hΛ100
  have hstep : Real.log ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i
      : ℕ) : ℝ) ≤ Real.log (2 * T) := by
    have hdiv : (0 : ℝ) ≤ μ / Real.log μ := by positivity
    nlinarith [htop, hlow, hnum]
  have hmono := Real.exp_le_exp.mpr hstep
  rw [Real.exp_log (by linarith), Real.exp_log (by linarith)] at hmono
  nlinarith [hmono, hqR, hT1]

/-- `s13CapGrid_kappa_Tann_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13CapGrid_kappa_Tann_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    ∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
      30 ≤ Real.log (2 * T)
        / Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i) := by
  intro i hi
  set μ : ℝ := Real.log (((A + s : ℕ)) : ℝ) with hμdef
  have hμ2000 : (2000 : ℝ) ≤ μ := s13CapGrid_mu_2000_L hh hL0 hhL hfl hb hflL
  have hΛ21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log μ := s13CapGrid_Lambda_lo_L hh hL0 hhL hfl hb hflL
  have hΛ100 : (100 : ℝ) ≤ Real.log μ := by
    have : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    nlinarith
  have hb3 := s13CapGrid_B3 (Nd := A + s) hμ2000 hΛ21 i hi
  have hb3R : (3 : ℝ)
      ≤ ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ) := by
    exact_mod_cast hb3
  have hlog0 : (0 : ℝ)
      < Real.log ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ) :=
    Real.log_pos (by linarith)
  have htop := s13CapGrid_logBase_le (Nd := A + s) hμ2000 hΛ21 hi
  have hlow := s13CapGrid_logTann_lo_LH_L hh hL0 hhL hfl hb hflL hTlo
  have hnum := capgrid_kappa_numeric hμ2000 hΛ100
  rw [le_div_iff₀ hlog0]
  rw [← hμdef] at hlow
  nlinarith [htop, hlow, hnum]

/-- `s13CapGrid_kappa30_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13CapGrid_kappa30_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    ∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
      30 ≤ Real.log ((q : ℝ) * (2 * T))
        / Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i) := by
  intro i hi
  have hq1 : 1 ≤ q := hb.2.2.2.1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hT1 : (1 : ℝ) < 2 * T := s13CapGrid_Tann_one_LH_L hh hL0 hhL hfl hb hflL hTlo
  have hmul : Real.log (2 * T) ≤ Real.log ((q : ℝ) * (2 * T)) := by
    apply Real.log_le_log (by linarith)
    nlinarith
  have hb3 := s13CapGrid_B3 (Nd := A + s) (s13CapGrid_mu_2000_L hh hL0 hhL hfl hb hflL)
    (s13CapGrid_Lambda_lo_L hh hL0 hhL hfl hb hflL) i hi
  have hb3R : (3 : ℝ)
      ≤ ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ) := by
    exact_mod_cast hb3
  have hlog0 : (0 : ℝ)
      < Real.log ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ) :=
    Real.log_pos (by linarith)
  have hbase := s13CapGrid_kappa_Tann_LH_L hh hL0 hhL hfl hb hflL hTlo i hi
  rw [le_div_iff₀ hlog0] at hbase ⊢
  linarith

/-- `s13CapGrid_BT10_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap binder
becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor `hflL`
passed down.  BODY: the source's, verbatim. -/
theorem s13CapGrid_BT10_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    ∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
      ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
        ≤ (2 * T) ^ 10 := by
  intro i hi
  exact ramQbase_le_pow_ten (s13CapGrid_Tann_one_LH_L hh hL0 hhL hfl hb hflL hTlo)
    (s13CapGrid_B3 (Nd := A + s) (s13CapGrid_mu_2000_L hh hL0 hhL hfl hb hflL)
      (s13CapGrid_Lambda_lo_L hh hL0 hhL hfl hb hflL) i hi)
    (s13CapGrid_kappa_Tann_LH_L hh hL0 hhL hfl hb hflL hTlo i hi)

/-- `s13CapGrid_all_LH_gk` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap binder
becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor `hflL`
passed down.  BODY: the source's, verbatim. -/
theorem s13CapGrid_all_LH_gk_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} {cs T : ℝ}
    (hM : 1 ≤ M) (hcs : 1 ≤ cs) (hfl : loglogFloor50 ≤ R.Hlo)
    (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hblock : s13BlockFloor_L_gk K M ≤ A + s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T)
    (hThi : 2 * T ≤ (((A + s : ℕ)) : ℝ)) :
    8 ≤ Real.log (((A + s : ℕ)) : ℝ)
    ∧ 2 ≤ H83 (((A + s : ℕ)) : ℝ) theta293
    ∧ (q : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ 12
    ∧ Real.log ((q : ℝ) * (2 * T)) ≤ s13Lr (A + s)
    ∧ P83 (((A + s : ℕ)) : ℝ) theta293 ≤ ((s13BandP (A + s) : ℕ) : ℝ)
    ∧ Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
        ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ))
    ∧ 0 < s13BandQ (A + s)
    ∧ ((s13BandQ (A + s) : ℕ) : ℝ) ≤ Q83 (((A + s : ℕ)) : ℝ)
    ∧ s13BandP (A + s) ≤ s13BandQ (A + s)
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        H83 (((A + s : ℕ)) : ℝ) theta293 ≤ (i : ℝ))
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        3 ≤ ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i)
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
          ≤ (q : ℝ) * (2 * T))
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        30 ≤ Real.log ((q : ℝ) * (2 * T))
          / Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i))
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
          ≤ (2 * T) ^ 10)
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i)
          ≤ s13Lr (A + s))
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        420 * s13Lr (A + s) * (s13Lr (A + s)) ^ ((3 : ℝ) / 4)
            * (Real.log (s13Lr (A + s))) ^ 5
          ≤ cs * (Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293)
              (s13BandP (A + s)) i)) ^ 2)
    ∧ 100 * Real.log ((s13BandQ (A + s) : ℕ) : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ)
    ∧ ((Nat.sqrt (A + s) : ℝ) + 1)
          * ∏ p ∈ primeBand (s13BandP (A + s)) (s13BandQ (A + s)), (1 + 3 / (p : ℝ))
        ≤ (((A + s : ℕ)) : ℝ)
          * (Real.log ((s13BandP (A + s) : ℕ) : ℝ)
              / Real.log ((s13BandQ (A + s) : ℕ) : ℝ)) := by
  have hμ : (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := s13CapGrid_mu_2000_L hh hL0 hhL hfl hb hflL
  have hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    s13CapGrid_Lambda_lo_L hh hL0 hhL hfl hb hflL
  exact ⟨s13CapGrid_logX_eight_LH_L hh hL0 hhL hfl hb hflL, s13CapGrid_H83_two hμ hΛ,
    s13CapGrid_q_logX_LH_L hh hL0 hhL hfl hb hflL,
    s13CapGrid_logqT_L_LH_L hh hL0 hhL hfl hb hflL hTlo hThi, s13CapGrid_P_low (A + s),
    s13CapGrid_Q2_reg_LH_gk_L hh hL0 hhL K hM hb hblock, s13CapGrid_Q_pos hμ,
    s13CapGrid_Q_high (A + s),
    s13CapGrid_P_le_Q hμ hΛ, s13CapGrid_Hj hμ hΛ, s13CapGrid_B3 hμ hΛ,
    s13CapGrid_BT_LH_L hh hL0 hhL hfl hb hflL hTlo,
    s13CapGrid_kappa30_LH_L hh hL0 hhL hfl hb hflL hTlo,
    s13CapGrid_BT10_LH_L hh hL0 hhL hfl hb hflL hTlo,
    s13CapGrid_WL hμ hΛ, s13CapGrid_gate hcs hμ hΛ, s13CapGrid_Q_hundred hμ hΛ,
    s13CapGrid_band_product hμ hΛ⟩

/-- `capfloor_logq_le_LH` at the charge — TRANSPORT of the twin at `log h ≤ 9`: its cap binder is
unused, and so is the charge; no floor.  BODY: the source's, verbatim. -/
theorem capfloor_logq_le_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (_hL0 : 0 ≤ Lc)
    (_hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseLH h R M H L q j A s) :
    Real.log (q : ℝ) ≤ Real.log (h : ℝ) + 12 * Real.log (Real.log (H : ℝ))
      ∧ (1 : ℝ) ≤ (q : ℝ) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hqp : 0 < q := hb.2.2.2.1
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp
  have hqA : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H := hb.2.2.2.2.1
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [harcpow] at hqA
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hpow0 : (0 : ℝ) < Real.log (H : ℝ) ^ (12 : ℕ) := by positivity
  refine ⟨?_, hq1⟩
  have hstep := Real.log_le_log (by linarith : (0 : ℝ) < (q : ℝ)) hqA
  rw [Real.log_mul (ne_of_gt hh0) (ne_of_gt hpow0), Real.log_pow] at hstep
  push_cast at hstep
  linarith

/-- `capfloor_tannGate_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap binder
becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor `hflL`
passed down.  BODY: the source's, verbatim. -/
theorem capfloor_tannGate_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    TannGate ((Nd : ℕ) : ℝ) ((q : ℝ) * Tann) := by
  obtain ⟨hv, hm, hTpos, hlogT⟩ := capfloor_core_L hh hL0 hhL hfl hb hAN hTlo hflL
  obtain ⟨-, hq1⟩ := capfloor_logq_le_LH_L hh hL0 hhL hb
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le h21 hv
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  -- `log Nd ≥ √H = e^{v/2} ≥ (v/4)² = v²/16`
  have hsq : Real.sqrt (H : ℝ) = Real.exp (Real.log (H : ℝ) / 2) := capfloor_sqrt_eq_exp hH0
  have hexpsq : Real.exp (Real.log (H : ℝ) / 2)
      = Real.exp (Real.log (H : ℝ) / 4) * Real.exp (Real.log (H : ℝ) / 4) := by
    rw [← Real.exp_add]; ring_nf
  have hquart : Real.log (H : ℝ) / 4 ≤ Real.exp (Real.log (H : ℝ) / 4) := by
    have := Real.add_one_le_exp (Real.log (H : ℝ) / 4); linarith
  have hq0 : (0 : ℝ) ≤ Real.log (H : ℝ) / 4 := by linarith
  have hmsq : Real.log (H : ℝ) ^ (2 : ℕ) / 16 ≤ Real.log ((Nd : ℕ) : ℝ) := by
    have hz : (Real.log (H : ℝ) / 4) * (Real.log (H : ℝ) / 4) ≤ Real.sqrt (H : ℝ) := by
      rw [hsq, hexpsq]; nlinarith [hquart, hq0]
    nlinarith [hz, hm]
  have hm0 : (0 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) := by nlinarith [hmsq, hv0]
  set r : ℝ := Real.sqrt (Real.log ((Nd : ℕ) : ℝ)) with hr
  have hr2 : r * r = Real.log ((Nd : ℕ) : ℝ) := Real.mul_self_sqrt hm0
  have hr0 : (0 : ℝ) ≤ r := Real.sqrt_nonneg _
  have hnum : (10 : ℝ) ^ (21 : ℕ) = 1000000000000000000000 := by norm_num
  rw [hnum] at hv
  have hr60 : (60 : ℝ) ≤ r := by nlinarith [hr2, hmsq, hv, hr0, hv0]
  -- `log(q·T_ann) ≥ log T_ann ≥ ½·r² ≥ 30r`
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hqT : Real.log ((q : ℝ) * Tann) = Real.log (q : ℝ) + Real.log Tann :=
    Real.log_mul (by linarith) (ne_of_gt hTpos)
  have hkey : 30 * r ≤ Real.log ((q : ℝ) * Tann) := by
    rw [hqT]; nlinarith [hlogT, hr2, hr60, hr0, hlogq]
  have hqT0 : (0 : ℝ) < (q : ℝ) * Tann := by positivity
  unfold TannGate
  rw [rpow_half_eq_sqrt, ← hr]
  calc Real.exp (30 * r) ≤ Real.exp (Real.log ((q : ℝ) * Tann)) := Real.exp_le_exp.mpr hkey
    _ = (q : ℝ) * Tann := Real.exp_log hqT0

/-- `capfloor_QTann_gen_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem capfloor_QTann_gen_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {A G M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j As s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAN : As ≤ Nd)
    (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK A G M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    ((calQK A G M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann := by
  have hgate := capfloor_tannGate_LH_L hh hL0 hhL hfl hb hflL hAN hTlo (q := q)
  unfold TannGate at hgate
  rw [rpow_half_eq_sqrt] at hgate
  have hQ1 : 1 < ((calQK A G M 2 : ℕ) : ℝ) := capfloor_one_lt_QK2_gen hA hG hM
  have hQ0 : (0 : ℝ) < ((calQK A G M 2 : ℕ) : ℝ) := by linarith
  have hr0 : (0 : ℝ) ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)) := Real.sqrt_nonneg _
  calc ((calQK A G M 2 : ℕ) : ℝ)
      = Real.exp (Real.log ((calQK A G M 2 : ℕ) : ℝ)) := (Real.exp_log hQ0).symm
    _ ≤ Real.exp (30 * Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ (q : ℝ) * Tann := hgate

/-- `capfloor_QTann_LH_gk` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap binder
becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor `hflL`
passed down.  BODY: the source's, verbatim. -/
theorem capfloor_QTann_LH_gk_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    (K : ℕ) {R : ChowlaRegime} {M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j As s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAN : As ≤ Nd)
    (hM : 1 ≤ M) (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann :=
  capfloor_QTann_gen_LH_L hh hL0 hhL hfl hb hflL hAN (one_le_AdoorL hM) (one_le_s13GK K hM) hM hTlo
    hQ2reg

/-- `capfloor_kappa30Q_gen_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem capfloor_kappa30Q_gen_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {A G M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j As s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAN : As ≤ Nd)
    (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK A G M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((calQK A G M 2 : ℕ) : ℝ) := by
  refine kappa30_of_TannGate ((Nd : ℕ) : ℝ) ((q : ℝ) * Tann) (calQK A G M 2)
    (capfloor_one_lt_QK2_gen hA hG hM) ?_ (capfloor_tannGate_LH_L hh hL0 hhL hfl hb hflL hAN hTlo)
  rw [rpow_half_eq_sqrt]; exact hQ2reg

/-- `capfloor_kappa30Q_LH_gk` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem capfloor_kappa30Q_LH_gk_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    (K : ℕ) {R : ChowlaRegime} {M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j As s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAN : As ≤ Nd)
    (hM : 1 ≤ M) (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) :=
  capfloor_kappa30Q_gen_LH_L hh hL0 hhL hfl hb hflL hAN (one_le_AdoorL hM) (one_le_s13GK K hM) hM
    hTlo
    hQ2reg

/-- `capfloor_T0_Tann_sharp_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem capfloor_T0_Tann_sharp_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {T₀ Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hT₀ : T₀ ≤ Real.exp (Real.sqrt (H : ℝ) / 2)) : T₀ ≤ Tann := by
  obtain ⟨hv, hm, hTpos, hlogT⟩ := capfloor_core_L hh hL0 hhL hfl hb hAN hTlo hflL
  have h1 : Real.sqrt (H : ℝ) / 2 ≤ Real.log Tann := by linarith
  have h2 : Real.exp (Real.sqrt (H : ℝ) / 2) ≤ Real.exp (Real.log Tann) :=
    Real.exp_le_exp.mpr h1
  rw [Real.exp_log hTpos] at h2
  linarith

/-- ⟦`capfloor_floor1_LH` AT THE CHARGE⟧ — the twin at `log h ≤ 9` spent the cap through
`capfloor_logq_le`'s conclusion `log q ≤ log h + 12·loglog H` into `capfloor_lam_core_h_232`
(`232 = 8·(20 + 9)`).  At the charge `232 ↦ 160 + 8·Lc` (`capfloor_lam_core_h_L`), under the
tower's `Lc ≤ log H/10^20` (`s13_tower_logH_L`).  Demand: `8·(log 2·10^8 + log q)
≤ 160 + 8·Lc + 96·loglog H ≤ log H/4 ≤ loglog (5·Tann + 1)`.  Every other step is the source's. -/
theorem capfloor_floor1_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core_L hh hL0 hhL hfl hb hAN hTlo hflL
  obtain ⟨-, hΛ⟩ := capfloor_muLambda_LH_L hh hL0 hhL hfl hb hflL hAN hTlo
  obtain ⟨hlq, hq1⟩ := capfloor_logq_le_LH_L hh hL0 hhL hb
  have hvk : (40000 : ℝ) * vkStripConst q = 200000000 * (q : ℝ) := by
    rw [vkStripConst]; ring
  have hsplit : Real.log (200000000 * (q : ℝ))
      = Real.log 200000000 + Real.log (q : ℝ) :=
    Real.log_mul (by norm_num) (by linarith)
  have hnum : Real.log 200000000 ≤ 20 := by
    have hz := Real.log_le_log (by norm_num : (0 : ℝ) < 200000000)
      (le_trans (by norm_num : (200000000 : ℝ) ≤ 300000000) capfloor_twoE8_le_exp20)
    rwa [Real.log_exp] at hz
  -- ⟦AT THE CHARGE⟧ the tower pays `Lc`: `10^21·(1 + Lc) ≤ log H` ⇒ `Lc ≤ log H / 10^20`
  have htow := s13_tower_logH_L hL0 hb hflL
  have hLv : Lc ≤ Real.log (H : ℝ) / 10 ^ 20 := by
    rw [le_div_iff₀ (by positivity)]; norm_num at htow ⊢; linarith
  -- `232 = 8·(20 + 9) ↦ 160 + 8·Lc`
  have hcore := capfloor_lam_core_h_L hv hL0 hLv
  rw [hvk, hsplit]
  linarith

/-- ⟦`capfloor_floor2_LH` AT THE CHARGE⟧ — the twin at `log h ≤ 9` closed by a `linarith` that
spent the cap unnamed (through `log q ≤ log h + 12·loglog H`) against the landed `216` stone.
At the charge the stone is `capfloor_lam_core_h_L` (`160 + 8·Lc`, tower's `Lc ≤ log H/10^20`):
`8 + (20 + Lc + 12·loglog H)/100 ≤ 160 + 8·Lc + 96·loglog H ≤ log H/4`.  The `8104`/`162080000`
are this floor family's own constants, not the cap's.  Every other step is the source's. -/
theorem capfloor_floor2_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
      ≤ Real.log (Real.log (5 * Tann + 1)) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core_L hh hL0 hhL hfl hb hAN hTlo hflL
  obtain ⟨-, hΛ⟩ := capfloor_muLambda_LH_L hh hL0 hhL hfl hb hflL hAN hTlo
  obtain ⟨hlq, hq1⟩ := capfloor_logq_le_LH_L hh hL0 hhL hb
  have hvk : (20000 : ℝ) * (vkStripConst q + 8104) = 100000000 * (q : ℝ) + 162080000 := by
    rw [vkStripConst]; ring
  have hub : 100000000 * (q : ℝ) + 162080000 ≤ 300000000 * (q : ℝ) := by linarith
  have hlb : (0 : ℝ) < 100000000 * (q : ℝ) + 162080000 := by linarith
  have hmono := Real.log_le_log hlb hub
  have hsplit : Real.log (300000000 * (q : ℝ))
      = Real.log 300000000 + Real.log (q : ℝ) :=
    Real.log_mul (by norm_num) (by linarith)
  have hnum : Real.log 300000000 ≤ 20 := by
    have hz := Real.log_le_log (by norm_num : (0 : ℝ) < 300000000) capfloor_twoE8_le_exp20
    rwa [Real.log_exp] at hz
  -- ⟦AT THE CHARGE⟧ the tower pays `Lc`: `10^21·(1 + Lc) ≤ log H` ⇒ `Lc ≤ log H / 10^20`
  have htow := s13_tower_logH_L hL0 hb hflL
  have hLv : Lc ≤ Real.log (H : ℝ) / 10 ^ 20 := by
    rw [le_div_iff₀ (by positivity)]; norm_num at htow ⊢; linarith
  -- the landed `216` stone ↦ `160 + 8·Lc` (it no longer dominates once `Lc` is free)
  have hcore := capfloor_lam_core_h_L hv hL0 hLv
  have hlq0 : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  -- ⚠ at h = 1 this followed from `0 ≤ log q ≤ 12·loglog H`; at LH the `+log h` breaks that
  -- implication, so it is taken from the register's own `log H ≥ 10^21` instead.
  have hone : (1 : ℝ) ≤ Real.log (H : ℝ) := by
    have hnum : (1 : ℝ) ≤ (10 : ℝ) ^ (21 : ℕ) := by norm_num
    linarith
  have hlvl : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := Real.log_nonneg hone
  rw [hvk]
  rw [hsplit] at hmono
  linarith

/-- `capfloor_rhs_legs_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap binder
becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor `hflL`
passed down.  BODY: the source's, verbatim. -/
theorem capfloor_rhs_legs_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    Real.exp 300 * (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core_L hh hL0 hhL hfl hb hAN hTlo hflL
  obtain ⟨hμ, hΛ⟩ := capfloor_muLambda_LH_L hh hL0 hhL hfl hb hflL hAN hTlo
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le h21 hv
  -- leg 1
  have hleg1 : Real.exp 300 ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4) := by
    have hstep : (Real.exp (Real.log (H : ℝ) / 4)) ^ ((3 : ℝ) / 4)
        ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (Real.exp_nonneg _) hμ (by norm_num)
    have heq : (Real.exp (Real.log (H : ℝ) / 4)) ^ ((3 : ℝ) / 4)
        = Real.exp (Real.log (H : ℝ) / 4 * (3 / 4)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [heq] at hstep
    refine le_trans (Real.exp_le_exp.mpr ?_) hstep
    nlinarith [hv, h21]
  -- leg 2
  have hleg2 : (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
      ≤ (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hΛ 4
  have hp1 : (0 : ℝ) < Real.exp 300 := Real.exp_pos _
  have hp2 : (0 : ℝ) ≤ (Real.log (H : ℝ) / 4) ^ (4 : ℕ) := by positivity
  exact mul_le_mul hleg1 hleg2 hp2 (le_trans hp1.le hleg1)

/-- ⟦`capfloor_floor3_LH` AT THE CHARGE⟧ — the twin at `log h ≤ 9` carried `hW`'s slack
`+10 = 9 + 1` into `capfloor_floor3_numeric_h_10`.  At the charge `+10 ↦ + 1 + Lc`, into
`capfloor_floor3_numeric_h_L` under the tower's `Lc ≤ log H/10^20` (`s13_tower_logH_L`).
Every other step is the source's, verbatim. -/
theorem capfloor_floor3_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Kq Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) (hKq : Kq ≤ Real.exp 100) :
    Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core_L hh hL0 hhL hfl hb hAN hTlo hflL
  obtain ⟨hlq, hq1⟩ := capfloor_logq_le_LH_L hh hL0 hhL hb
  have hlegs := capfloor_rhs_legs_LH_L hh hL0 hhL hfl hb hflL hAN hTlo
  set E : ℝ := Real.exp 100 with hEdef
  have hE : (101 : ℝ) ≤ E := by
    have := Real.add_one_le_exp (100 : ℝ); rw [hEdef]; linarith
  have hE0 : (0 : ℝ) < E := by linarith
  have hexpE : (3 : ℝ) ≤ Real.exp E := by
    have := Real.add_one_le_exp E; linarith
  have hbox : Real.exp E + 3 ≤ Real.exp (E + 1) := by
    rw [Real.exp_add]
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    nlinarith [Real.exp_pos E, hexpE, he1]
  have hbox0 : (0 : ℝ) < Real.exp E + 3 := by positivity
  have hboxlog : Real.log (Real.exp E + 3) ≤ E + 1 := by
    have hz := Real.log_le_log hbox0 hbox
    rwa [Real.log_exp] at hz
  have hWsplit : Real.log ((q : ℝ) * (Real.exp E + 3))
      = Real.log (q : ℝ) + Real.log (Real.exp E + 3) :=
    Real.log_mul (by linarith) (by linarith)
  have hW0 : (0 : ℝ) ≤ Real.log ((q : ℝ) * (Real.exp E + 3)) := by
    refine Real.log_nonneg ?_
    nlinarith [hq1, hexpE]
  -- `+10 = 9 + 1 ↦ + 1 + Lc`
  have hW : Real.log ((q : ℝ) * (Real.exp E + 3))
      ≤ 12 * Real.log (Real.log (H : ℝ)) + E + 1 + Lc := by
    rw [hWsplit]; linarith [hlq, hhL, hboxlog]
  have hstep : Kq * Real.log ((q : ℝ) * (Real.exp E + 3))
      ≤ E * Real.log ((q : ℝ) * (Real.exp E + 3)) :=
    mul_le_mul_of_nonneg_right hKq hW0
  -- ⟦AT THE CHARGE⟧ the tower pays `Lc`: `10^21·(1 + Lc) ≤ log H` ⇒ `Lc ≤ log H / 10^20`
  have htow := s13_tower_logH_L hL0 hb hflL
  have hLv : Lc ≤ Real.log (H : ℝ) / 10 ^ 20 := by
    rw [le_div_iff₀ (by positivity)]; norm_num at htow ⊢; linarith
  have hnum := capfloor_floor3_numeric_h_L hv hE hL0 hLv hW
  have hE3 : Real.exp 300 = E ^ (3 : ℕ) := by
    rw [hEdef, ← Real.exp_nat_mul]; norm_num
  rw [hE3] at hlegs
  linarith

/-- `capfloor_floor4_of_regimeWin_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the
cap binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower
floor `hflL` passed down.  BODY: the source's, verbatim. -/
theorem capfloor_floor4_of_regimeWin_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hKs0 : 0 < Ks)
    (hwin : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16) :
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hHloR : (4000000 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast R.hHlo_floor
  have hloR : ((R.Hlo : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo
  have hmono : Real.log ((R.Hlo : ℕ) : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hloR
  exact capfloor_floor4_sharp_LH_L hh hL0 hhL hfl hb hflL hAN hTlo
    (exp_neg_le_of_log_inv_le hKs0 (by linarith))

set_option maxHeartbeats 1000000 in
-- as the source: the eight-field capfloor bundle re-checks with every entry swapped
/-- `s13CapFloor_all_LH_gk_sharpT0_kswin` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`:
the cap binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the
tower floor `hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13CapFloor_all_LH_gk_sharpT0_kswin_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    (K : ℕ) {R : ChowlaRegime} {M H L q j As s Nd : ℕ}
    {T₀ Kq Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j As s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hM : 1 ≤ M)
    (hAN : As ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)))
    (hT₀ : T₀ ≤ Real.exp (Real.sqrt ((R.Hlo : ℕ) : ℝ) / 2)) (hKq : Kq ≤ Real.exp 100)
    (hKs0 : 0 < Ks)
    (hKsw : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16) :
    ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann ∧
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ∧
    T₀ ≤ Tann ∧
    8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) ∧
    8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
      ≤ Real.log (Real.log (5 * Tann + 1)) ∧
    Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) ∧
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) ∧
    Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hloR : ((R.Hlo : ℕ) : ℝ) ≤ ((H : ℕ) : ℝ) := by exact_mod_cast hlo
  have hsqm : Real.sqrt ((R.Hlo : ℕ) : ℝ) / 2 ≤ Real.sqrt ((H : ℕ) : ℝ) / 2 := by
    have := Real.sqrt_le_sqrt hloR
    linarith
  exact
   ⟨capfloor_QTann_LH_gk_L hh hL0 hhL K hfl hb hflL hAN hM hTlo hQ2reg,
   capfloor_kappa30Q_LH_gk_L hh hL0 hhL K hfl hb hflL hAN hM hTlo hQ2reg,
   capfloor_T0_Tann_sharp_LH_L hh hL0 hhL hfl hb hflL hAN hTlo
     (le_trans hT₀ (Real.exp_le_exp.mpr hsqm)),
   capfloor_floor1_LH_L hh hL0 hhL hfl hb hflL hAN hTlo,
   capfloor_floor2_LH_L hh hL0 hhL hfl hb hflL hAN hTlo,
   capfloor_floor3_LH_L hh hL0 hhL hfl hb hflL hAN hTlo hKq,
   capfloor_floor4_of_regimeWin_LH_L hh hL0 hhL hfl hb hflL hAN hTlo hKs0 hKsw,
   hQ2reg⟩

/-! ### §M, continued — the `εr` rows, the cap-gate supply and the crossing spine head

The per-block wire and its fused transport first (rows 1 and 7 — no floor: their bodies never
read the cap), then the register, pins and `εr` family (the three rows of §2 re-cut through §L's
exponent stones, and the row that supplies their tower floor `hLu`), the spine, and the root. -/

set_option maxHeartbeats 3200000 in
-- as the landed `_cs` twin: the wire re-elaborates with one extra prefix conjunct
/-- `m4_hcap_at_door_perBlock_LH_gk_bounded_khoist_cs` at the charge — TRANSPORT of the twin at
`log h ≤ 9`: its cap binder is unused, and so is the charge; no floor.  BODY: the source's,
verbatim. -/
theorem m4_hcap_at_door_perBlock_LH_gk_bounded_khoist_cs_L {h : ℕ} (_hh : 0 < h)
    {Lc : ℝ} (_hL0 : 0 ≤ Lc)
    (_hhL : Real.log (h : ℝ) ≤ Lc) :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (K : ℕ) (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 : ℝ),
              DoorCapBasePerBlock_L_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf (2 * T)
                VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2) →
        ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, hcapstone⟩ :=
    m4_rowChi_capstone_perBlock_bounded_cs
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro K R M cU ε hcU hfam H L q j A s hb χ T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, hd⟩ :=
    hfam H L q j A s hb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hlogX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := hd.logX_four
    linarith
  have hres := hcapstone q cU hcU (calP (AdoorL M) (s13GK K M))
    (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M)) (mrAlpha (1 / 12)) 2 Jb
    hd.Jb_lo hd.Jb_hi hd.Hseq_two hd.alpha_nonneg
    (2 * T) VJ V Lr (((A + s : ℕ)) : ℝ) hd.Tann_one hd.qTann_one hd.P_three hd.PQ hd.QTann
    hd.kappa30Q hd.loglog5 hd.VJ_bound η εd hd.alpha_eta hd.eta_half hd.Tann_X hd.X_pos
    hd.debit hd.logX_pos hd.q_logX hd.V_one hd.V_inv hd.T0_Tann hd.floor1 hd.floor2
    hd.floor3 hd.floor4 hd.logqT_one hd.logqT_L hd.L_exp hd.logV_L
    hd.H83_two hd.logX_exp hd.logX_four hTgate
    (2 * (A + s)) Xd P Q Mr (winCutH (A + s) (doorCoeffU_L_gk K M)) b cf hd.cf_one hd.P_low
    hd.Q_pos hd.Q_high hd.range hd.budget hd.Hj hd.B3 hd.BT hd.kappa30 hd.BT10 hd.WL hd.gate
    Rbd CR hd.Rbd_nonneg hd.Rbd_grade hd.Cq_gate
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ)) hd.Rbd_binder
    KS hd.KS_nonneg hd.KS_binder hd.KS_gate E EP2 (ε (A + s)) hd.epsr_nonneg hd.abs8640
    hd.EP2_gate hd.E_row hd.E_binder (doorCap_hXN (A + s)) (doorCap_hN2 (A + s))
    (fun n hn => doorRowDatumU_supp0_L_gk K M (A + s) hn)
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ))
    (m4_hSup_door_at_zero q (winCutH (A + s) (doorCoeffU_L_gk K M)) (2 * (A + s)) hlogX1) χ
  rw [chiBarCoeff_doorRowDatum_L_gk] at hres
  simpa using hres

set_option maxHeartbeats 3200000 in
-- as the landed `_cs` twin: the family re-elaborates with one extra prefix conjunct
/-- `m4_fuse_hcap_of_capWS_LH_gk_ceiling_khoist_cs` at the charge — SUPPLIER-SWAP of the twin at
`log h ≤ 9`: the cap binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L`
twin.  BODY: the source's, verbatim. -/
theorem m4_fuse_hcap_of_capWS_LH_gk_ceiling_khoist_cs_L {h : ℕ} (hh : 0 < h)
    {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ Real.exp 100 ∧ 0 < Ks ∧
      ∀ (K : ℕ) (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
              G2Scaffold.DoorCapErrWS_L_gk K M (A + s) q Xd P Q b cf (2 * T) E Mtail
                ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                      ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                        (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU_L_gk K M)))
                        (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                    → DoorCapBasePerBlock_L_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                        (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
        ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, hwire⟩ :=
    m4_hcap_at_door_perBlock_LH_gk_bounded_khoist_cs_L hh hL0 hhL
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq,
    le_trans hKqb kq_closed_form_le_exp_hundred, hKs, ?_⟩
  intro K R M cU ε hc1 hcapWS
  refine hwire K R M cU ε hc1 ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (G2Scaffold.m4_capE_at_door_L_gk K hws)⟩

/-- `s13_capEps_register_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13_capEps_register_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (H : ℝ)
      ∧ (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ)
      ∧ Real.log (H : ℝ) / 2 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ))
      ∧ (q.totient : ℝ) ≤ (h : ℝ) * (Real.log (H : ℝ)) ^ (12 : ℕ) := by
  have hlo : R.Hlo ≤ H := hb.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have hz := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at hz
  have hu21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (H : ℝ) :=
    le_trans capeps_ten21_le_exp50 hexp50
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA_LH_L hh hL0 hhL hfl hb hflL
  have hsharp := s13_socketBase_loglogA_sharp_L hh hL0 hhL hfl hb hflL
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hmono : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := Real.log_le_log hA0 hAX
  have hll : Real.log (Real.log (A : ℝ)) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    Real.log_le_log (by linarith) hmono
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hqQ : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H := hb.2.2.2.2.1
  rw [harcpow] at hqQ
  have htot : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  exact ⟨hu21, by linarith, by linarith, by linarith⟩

/-- `s13CapEps_pin_floors_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13CapEps_pin_floors_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (4 : ℝ) ≤ Real.log (P83 (((A + s : ℕ)) : ℝ) theta293)
      ∧ (4 : ℝ) ≤ Real.log (Q83 (((A + s : ℕ)) : ℝ)) := by
  obtain ⟨hu, hμ, hΛ, -⟩ := s13_capEps_register_LH_L hh hL0 hhL hfl hb hflL
  set X : ℝ := (((A + s : ℕ)) : ℝ) with hXdef
  set μ : ℝ := Real.log X with hμdef
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛbig : (5 : ℝ) * 10 ^ (20 : ℕ) ≤ Real.log μ := by
    have : (10 : ℝ) ^ (21 : ℕ) = 2 * (5 * 10 ^ (20 : ℕ)) := by norm_num
    linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hθ32 : theta293 < 1 / 32 := theta293_lt_one_div_32
  have hθ0 : (0 : ℝ) < theta293 := theta293_pos
  constructor
  · rw [P83, Real.log_exp]
    have hrw : μ ^ (1 - theta293) = Real.exp ((1 - theta293) * Real.log μ) := by
      rw [Real.rpow_def_of_pos hμ0]; ring_nf
    have hhalf : Real.exp (Real.log μ / 2) ≤ μ ^ (1 - theta293) := by
      rw [hrw]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hlin : Real.log μ / 2 + 1 ≤ Real.exp (Real.log μ / 2) :=
      Real.add_one_le_exp _
    linarith
  · rw [Q83, Real.log_exp, le_div_iff₀ hΛ0]
    have hsq : (Real.log μ) ^ 2 / 4 ≤ μ := by
      have hz := capeps_sq_le_exp hΛ0.le
      rwa [Real.exp_log hμ0] at hz
    nlinarith [hsq, hΛbig, hΛ0]

/-- `s13CapEps_pins_supply_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13CapEps_pins_supply_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    P83 (((A + s : ℕ)) : ℝ) theta293
        ≤ ((⌈P83 (((A + s : ℕ)) : ℝ) theta293⌉₊ : ℕ) : ℝ)
      ∧ Real.log ((⌈P83 (((A + s : ℕ)) : ℝ) theta293⌉₊ : ℕ) : ℝ)
            / Real.log ((⌊Q83 (((A + s : ℕ)) : ℝ)⌋₊ : ℕ) : ℝ)
          ≤ 2 * (Real.log (Real.log (((A + s : ℕ)) : ℝ))
                  * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)) := by
  obtain ⟨hu, hμ, hΛ, -⟩ := s13_capEps_register_LH_L hh hL0 hhL hfl hb hflL
  obtain ⟨hP4, hQ4⟩ := s13CapEps_pin_floors_LH_L hh hL0 hhL hfl hb hflL
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  refine ⟨Nat.le_ceil _, m4_tail_grade_rounded (by linarith) (by linarith) hP4 hQ4⟩

/-- `s13_abs8640_of_socketBase_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the
cap binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower
floor `hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13_abs8640_of_socketBase_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (8640 : ℝ) ≤ (Real.log (A : ℝ)) ^ (theta293 - 1 / 500) := by
  obtain ⟨h1, h2⟩ := s13_socketBase_loglogA_LH_L hh hL0 hhL hfl hb hflL
  exact s13_abs8640_of_loglog (by linarith) h2

/-- `s13_abs8640_at_base_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13_abs8640_at_base_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s B : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hAB : A ≤ B) :
    (8640 : ℝ) ≤ (Real.log (B : ℝ)) ^ (theta293 - 1 / 500) := by
  obtain ⟨h1, -⟩ := s13_socketBase_loglogA_LH_L hh hL0 hhL hfl hb hflL
  have hcore := s13_abs8640_of_socketBase_LH_L hh hL0 hhL hfl hb hflL
  have hABR : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
  have hA0 : (0 : ℝ) < (A : ℝ) := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    exact_mod_cast hA
  have hmono : Real.log (A : ℝ) ≤ Real.log (B : ℝ) := Real.log_le_log hA0 hABR
  have hθ : (0 : ℝ) ≤ theta293 - 1 / 500 := by have := s13_theta293_margin_lo; linarith
  exact le_trans hcore (Real.rpow_le_rpow (by linarith) hmono hθ)

/-- `s13_abs8640_at_shift_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13_abs8640_at_shift_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (8640 : ℝ) ≤ (Real.log ((A + s : ℕ) : ℝ)) ^ (theta293 - 1 / 500) :=
  s13_abs8640_at_base_LH_L hh hL0 hhL hfl hb hflL (Nat.le_add_right A s)

/-- `s13CapEps_abs8640_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap binder
becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor `hflL`
passed down.  BODY: the source's, verbatim. -/
theorem s13CapEps_abs8640_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {εr : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hεr : theta293 - 1 / 500 ≤ εr) :
    (8640 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ εr := by
  obtain ⟨-, hμ, -, -⟩ := s13_capEps_register_LH_L hh hL0 hhL hfl hb hflL
  exact le_trans (s13_abs8640_at_shift_LH_L hh hL0 hhL hfl hb hflL)
    (Real.rpow_le_rpow_of_exponent_le (by linarith) hεr)

section RowsHL

variable {u μ X W C r β Pr φ : ℝ}

/-- ⟦`capeps_row_phi_h` AT THE CHARGE⟧ — the raised-cap row read `h ≤ e^14` and `25 = 11 + 14
≤ 60` into `capeps_expbound_60`.  At the charge: `h ≤ e^Lc` (`zH_le_exp`), `25 ↦ 11 + Lc`, and
`capeps_expbound_L` at `11 + Lc ≤ 49 + Lc` under the tower floor `hLu : 50 + Lc ≤ log u`. -/
theorem capeps_row_phi_h_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (hLu : (50 : ℝ) + Lc ≤ Real.log u) (hφ0 : 0 ≤ φ)
    (hφ : φ ≤ (h : ℝ) * u ^ (12 : ℕ)) :
    12 * (4160 * φ * μ ^ (-theta293)) ≤ μ ^ (-(1 / 500) : ℝ) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Real.log μ := by linarith
  have hp12 : (0 : ℝ) < u ^ (12 : ℕ) := pow_pos hu0 12
  have hexpL := zH_le_exp hh hhL
  have he11 : (49920 : ℝ) ≤ Real.exp 11 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hz : Real.exp 11 = (Real.exp 1) ^ (11 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7182818283 : ℝ) ^ (11 : ℕ) ≤ (Real.exp 1) ^ (11 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 11
    have : (49920 : ℝ) ≤ (2.7182818283 : ℝ) ^ (11 : ℕ) := by norm_num
    rw [hz]; linarith
  -- `25 = 11 + 14 ↦ 11 + Lc`
  have he25 : (49920 : ℝ) * (h : ℝ) ≤ Real.exp (11 + Lc) := by
    have hsum : Real.exp (11 + Lc) = Real.exp 11 * Real.exp Lc := Real.exp_add 11 Lc
    rw [hsum]
    exact mul_le_mul he11 hexpL (by positivity) (Real.exp_pos 11).le
  have hstone := capeps_expbound_L hu hμ hΛ hL0 hLu (by linarith : (11 : ℝ) + Lc ≤ 49 + Lc)
  have hkey : 49920 * φ ≤ μ ^ (theta293 - 1 / 500) := by
    have hchain : 49920 * φ ≤ (49920 * (h : ℝ)) * u ^ (12 : ℕ) := by nlinarith [hφ, hp12]
    have h1 : 49920 * φ ≤ Real.exp (11 + Lc) * u ^ (12 : ℕ) :=
      le_trans hchain (mul_le_mul_of_nonneg_right he25 hp12.le)
    have h2 : Real.exp (11 + Lc) * u ^ (12 : ℕ)
        ≤ Real.exp (11 + Lc) * u ^ (12 : ℕ) * Real.log μ := by
      nlinarith [Real.exp_pos (11 + Lc)]
    linarith
  have hT0 : (0 : ℝ) < μ ^ (-theta293) := Real.rpow_pos_of_pos hμ0 _
  have hsplit : μ ^ (-theta293) * μ ^ (theta293 - 1 / 500) = μ ^ (-(1 / 500) : ℝ) := by
    rw [← Real.rpow_add hμ0]; congr 1; ring
  calc 12 * (4160 * φ * μ ^ (-theta293)) = (49920 * φ) * μ ^ (-theta293) := by ring
    _ ≤ μ ^ (theta293 - 1 / 500) * μ ^ (-theta293) :=
        mul_le_mul_of_nonneg_right hkey hT0.le
    _ = μ ^ (-theta293) * μ ^ (theta293 - 1 / 500) := by ring
    _ = μ ^ (-(1 / 500) : ℝ) := hsplit

set_option maxHeartbeats 1000000 in
-- the `(h:ℝ)·u¹²` factor doubles the monomial count in both legs' linarith tableaux
/-- ⟦`capeps_row_tail_h` AT THE CHARGE⟧ — the raised-cap row read `h ≤ e^14` into its two legs.
A leg: `63 = 9 + 40 + 14 ↦ 49 + Lc`, `capeps_expbound_L` at `49 + Lc ≤ 49 + Lc`; B leg:
`22 = 8 + 14 ↦ 8 + Lc`, `capeps_bigexp_L` at `8 + Lc ≤ 49 + Lc`; `h ≤ e^Lc` (`zH_le_exp`),
under the tower floor `hLu : 50 + Lc ≤ log u`.  Every other step is the source's. -/
theorem capeps_row_tail_h_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (hLu : (50 : ℝ) + Lc ≤ Real.log u) (hX0 : 0 < X)
    (hXlog : Real.log X = μ)
    (hW0 : 0 ≤ W) (hW : W ≤ 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X) (hC0 : 0 < C)
    (hC : Real.log C ≤ 40) (hr : r ≤ 2 * (Real.log μ * μ ^ (-theta293))) :
    12 * (W * (C * r / X + 1 / X ^ 2)) ≤ μ ^ (-(1 / 500) : ℝ) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Real.log μ := by linarith
  have hp12 : (0 : ℝ) < u ^ (12 : ℕ) := pow_pos hu0 12
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hph : (0 : ℝ) < (h : ℝ) * u ^ (12 : ℕ) := by positivity
  have hexpL := zH_le_exp hh hhL
  have hT0 : (0 : ℝ) < μ ^ (-theta293) := Real.rpow_pos_of_pos hμ0 _
  have hXne : X ≠ 0 := ne_of_gt hX0
  have hinv : (0 : ℝ) ≤ X⁻¹ := by positivity
  have hstep : C * r / X + 1 / X ^ 2
      ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2 := by
    have h1 : C * r ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) :=
      mul_le_mul_of_nonneg_left hr hC0.le
    have h2 : C * r / X ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) / X := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h1 hinv
    linarith
  have hS0 : (0 : ℝ) ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2 := by
    have : (0 : ℝ) ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) / X := by positivity
    have h2 : (0 : ℝ) ≤ 1 / X ^ 2 := by positivity
    linarith
  have hprod : W * (C * r / X + 1 / X ^ 2)
      ≤ 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X
        * (C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2) :=
    le_trans (mul_le_mul_of_nonneg_left hstep hW0) (mul_le_mul_of_nonneg_right hW hS0)
  have hval : 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X
        * (C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2)
      = 128 * C * ((h : ℝ) * u ^ (12 : ℕ)) * Real.log μ * μ ^ (-theta293)
        + 64 * ((h : ℝ) * u ^ (12 : ℕ)) / X := by
    field_simp
    ring
  have hCle : C ≤ Real.exp 40 := by
    have := Real.exp_le_exp.mpr hC
    rwa [Real.exp_log hC0] at this
  have h3072 : (3072 : ℝ) ≤ Real.exp 9 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hz : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7182818283 : ℝ) ^ (9 : ℕ) ≤ (Real.exp 1) ^ (9 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 9
    have : (3072 : ℝ) ≤ (2.7182818283 : ℝ) ^ (9 : ℕ) := by norm_num
    rw [hz]; linarith
  -- A leg: `63 = 9 + 40 + 14 ↦ 49 + Lc`
  have h63 : (3072 : ℝ) * C * (h : ℝ) ≤ Real.exp (49 + Lc) := by
    have hsum : Real.exp (49 + Lc) = Real.exp 9 * Real.exp 40 * Real.exp Lc := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [hsum]
    have hCh : (3072 : ℝ) * C ≤ Real.exp 9 * Real.exp 40 :=
      mul_le_mul h3072 hCle hC0.le (Real.exp_pos 9).le
    exact mul_le_mul hCh hexpL (by positivity) (by positivity)
  have hlegA : 1536 * C * ((h : ℝ) * u ^ (12 : ℕ)) * Real.log μ * μ ^ (-theta293)
      ≤ μ ^ (-(1 / 500) : ℝ) / 2 := by
    have hstone := capeps_expbound_L hu hμ hΛ hL0 hLu (le_refl (49 + Lc))
    have hmul : (3072 * C * (h : ℝ)) * (u ^ (12 : ℕ) * Real.log μ)
        ≤ Real.exp (49 + Lc) * (u ^ (12 : ℕ) * Real.log μ) :=
      mul_le_mul_of_nonneg_right h63 (by positivity)
    have h1 : 3072 * C * ((h : ℝ) * u ^ (12 : ℕ)) * Real.log μ
        ≤ μ ^ (theta293 - 1 / 500) := by nlinarith [hmul, hstone]
    have h2 : 3072 * C * ((h : ℝ) * u ^ (12 : ℕ)) * Real.log μ * μ ^ (-theta293)
        ≤ μ ^ (theta293 - 1 / 500) * μ ^ (-theta293) :=
      mul_le_mul_of_nonneg_right h1 hT0.le
    have hsplit : μ ^ (theta293 - 1 / 500) * μ ^ (-theta293) = μ ^ (-(1 / 500) : ℝ) := by
      rw [← Real.rpow_add hμ0]; congr 1; ring
    rw [hsplit] at h2
    linarith
  have hlegB : 64 * ((h : ℝ) * u ^ (12 : ℕ)) / X ≤ μ ^ (-(1 / 500) : ℝ) / 24 := by
    -- B leg: `22 = 8 + 14 ↦ 8 + Lc`
    have hstone := capeps_bigexp_L hu hμ hΛ hL0 hLu (by linarith : (8 : ℝ) + Lc ≤ 49 + Lc)
    have he8 : (1536 : ℝ) ≤ Real.exp 8 := by
      have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have hz : Real.exp 8 = (Real.exp 1) ^ (8 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have hc : (2.7182818283 : ℝ) ^ (8 : ℕ) ≤ (Real.exp 1) ^ (8 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) h1.le 8
      have : (1536 : ℝ) ≤ (2.7182818283 : ℝ) ^ (8 : ℕ) := by norm_num
      rw [hz]; linarith
    have he22 : (1536 : ℝ) * (h : ℝ) ≤ Real.exp (8 + Lc) := by
      have hsum : Real.exp (8 + Lc) = Real.exp 8 * Real.exp Lc := Real.exp_add 8 Lc
      rw [hsum]
      exact mul_le_mul he8 hexpL (by positivity) (Real.exp_pos 8).le
    have hμ2 : (1 : ℝ) ≤ μ ^ 2 := by nlinarith
    have ha : 1536 * ((h : ℝ) * u ^ (12 : ℕ)) ≤ Real.exp (8 + Lc) * u ^ (12 : ℕ) := by
      have := mul_le_mul_of_nonneg_right he22 hp12.le
      nlinarith [this]
    have hbb : Real.exp (8 + Lc) * u ^ (12 : ℕ) ≤ Real.exp (8 + Lc) * u ^ (12 : ℕ) * μ ^ 2 :=
      le_mul_of_one_le_right (by positivity) hμ2
    have h1 : 1536 * ((h : ℝ) * u ^ (12 : ℕ)) ≤ Real.exp (8 + Lc) * u ^ (12 : ℕ) * μ ^ 2 := by
      linarith
    have h2 : 1536 * ((h : ℝ) * u ^ (12 : ℕ)) ≤ X * μ ^ (-(1 / 500) : ℝ) := by
      rw [capeps_Xmu hX0 hXlog hμ0]; linarith
    rw [div_le_div_iff₀ hX0 (by norm_num : (0 : ℝ) < 24)]
    nlinarith [h2]
  calc 12 * (W * (C * r / X + 1 / X ^ 2))
      ≤ 12 * (64 * ((h : ℝ) * u ^ (12 : ℕ)) * X
          * (C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2)) := by linarith
    _ = 12 * (128 * C * ((h : ℝ) * u ^ (12 : ℕ)) * Real.log μ * μ ^ (-theta293)
          + 64 * ((h : ℝ) * u ^ (12 : ℕ)) / X) := by rw [hval]
    _ ≤ μ ^ (-(1 / 500) : ℝ) := by linarith

set_option maxHeartbeats 1000000 in
-- same cause as the source: `(h:ℝ)·u¹²` where the landed row carries `u¹²` alone
/-- ⟦`capeps_row_p2_h` AT THE CHARGE⟧ — the twin at `log h ≤ 9` read `h ≤ e^9` into two legs.
Leg A: `20 = 11 + 9 ↦ 11 + Lc`, `capeps_Pbig_h_L`; leg B: `20 ↦ 11 + Lc`, `capeps_bigexp_L` at
`11 + Lc ≤ 49 + Lc`; `h ≤ e^Lc` (`zH_le_exp`), under the tower floor `hLu : 50 + Lc ≤ log u`.
Every other step is the source's. -/
theorem capeps_row_p2_h_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (hLu : (50 : ℝ) + Lc ≤ Real.log u) (hX0 : 0 < X)
    (hXlog : Real.log X = μ)
    (hW0 : 0 ≤ W) (hW : W ≤ 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 2 * μ) (hPr : Real.exp (μ ^ (1 - theta293)) ≤ Pr) :
    12 * (W * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2)) ≤ μ ^ (-(1 / 500) : ℝ) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Real.log μ := by linarith
  have hp12 : (0 : ℝ) < u ^ (12 : ℕ) := pow_pos hu0 12
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hexpL : (h : ℝ) ≤ Real.exp Lc := zH_le_exp hh hhL
  have hPr0 : (0 : ℝ) < Pr := lt_of_lt_of_le (Real.exp_pos _) hPr
  have hXne : X ≠ 0 := ne_of_gt hX0
  have hPne : Pr ≠ 0 := ne_of_gt hPr0
  have hK0 : (0 : ℝ) < μ ^ (-(1 / 500) : ℝ) := Real.rpow_pos_of_pos hμ0 _
  have hS0 : (0 : ℝ) ≤ 16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2 := by
    have h1 : (0 : ℝ) ≤ 16 * β / (X * Pr) := by positivity
    have h2 : (0 : ℝ) ≤ 4 * β ^ 2 / X ^ 2 := by positivity
    linarith
  have hprod : W * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2)
      ≤ 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2) :=
    mul_le_mul_of_nonneg_right hW hS0
  have hval : 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2)
      = 1024 * ((h : ℝ) * u ^ (12 : ℕ)) * β / Pr
        + 256 * ((h : ℝ) * u ^ (12 : ℕ)) * β ^ 2 / X := by
    field_simp
    ring
  have he11 : (49152 : ℝ) ≤ Real.exp 11 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hz : Real.exp 11 = (Real.exp 1) ^ (11 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7182818283 : ℝ) ^ (11 : ℕ) ≤ (Real.exp 1) ^ (11 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 11
    have : (49152 : ℝ) ≤ (2.7182818283 : ℝ) ^ (11 : ℕ) := by norm_num
    rw [hz]; linarith
  -- leg A: `20 = 11 + 9 ↦ 11 + Lc`
  have he20 : (49152 : ℝ) * (h : ℝ) ≤ Real.exp (11 + Lc) := by
    have hsum : Real.exp (11 + Lc) = Real.exp 11 * Real.exp Lc := Real.exp_add 11 Lc
    rw [hsum]
    exact mul_le_mul he11 hexpL (by positivity) (Real.exp_pos 11).le
  have hlegA : 12 * (1024 * ((h : ℝ) * u ^ (12 : ℕ)) * β / Pr)
      ≤ μ ^ (-(1 / 500) : ℝ) / 2 := by
    have hstone := capeps_Pbig_h_L hu hμ hΛ hL0 hLu
    have h500 : (0 : ℝ) < μ ^ ((1 : ℝ) / 500) := Real.rpow_pos_of_pos hμ0 _
    have hPb : 49152 * ((h : ℝ) * u ^ (12 : ℕ)) * μ * μ ^ ((1 : ℝ) / 500) ≤ Pr := by
      have h1 : (49152 * (h : ℝ)) * (u ^ (12 : ℕ) * μ * μ ^ ((1 : ℝ) / 500))
          ≤ Real.exp (11 + Lc) * (u ^ (12 : ℕ) * μ * μ ^ ((1 : ℝ) / 500)) :=
        mul_le_mul_of_nonneg_right he20 (by positivity)
      nlinarith [h1, hstone]
    have hmul : 49152 * ((h : ℝ) * u ^ (12 : ℕ)) * μ
          * (μ ^ ((1 : ℝ) / 500) * μ ^ (-(1 / 500) : ℝ))
        ≤ Pr * μ ^ (-(1 / 500) : ℝ) := by
      have := mul_le_mul_of_nonneg_right hPb hK0.le
      nlinarith [this]
    have hone : μ ^ ((1 : ℝ) / 500) * μ ^ (-(1 / 500) : ℝ) = 1 := by
      rw [← Real.rpow_add hμ0, show (1 : ℝ) / 500 + -(1 / 500) = 0 by ring, Real.rpow_zero]
    rw [hone, mul_one] at hmul
    have hβμ : 12 * (1024 * ((h : ℝ) * u ^ (12 : ℕ)) * β)
        ≤ 24576 * ((h : ℝ) * u ^ (12 : ℕ)) * μ := by nlinarith [hp12, hh0]
    rw [mul_div_assoc', div_le_iff₀ hPr0]
    linarith [hmul, hβμ]
  have hlegB : 12 * (256 * ((h : ℝ) * u ^ (12 : ℕ)) * β ^ 2 / X)
      ≤ μ ^ (-(1 / 500) : ℝ) / 2 := by
    -- leg B: `20 = 11 + 9 ↦ 11 + Lc`
    have hstone := capeps_bigexp_L hu hμ hΛ hL0 hLu (by linarith : (11 : ℝ) + Lc ≤ 49 + Lc)
    have he20b : (24576 : ℝ) * (h : ℝ) ≤ Real.exp (11 + Lc) := by
      have hsum : Real.exp (11 + Lc) = Real.exp 11 * Real.exp Lc := Real.exp_add 11 Lc
      rw [hsum]
      exact mul_le_mul (by linarith : (24576 : ℝ) ≤ Real.exp 11) hexpL (by positivity)
        (Real.exp_pos 11).le
    have h1 : 24576 * ((h : ℝ) * u ^ (12 : ℕ)) * μ ^ 2 ≤ X * μ ^ (-(1 / 500) : ℝ) := by
      rw [capeps_Xmu hX0 hXlog hμ0]
      have hmul : (24576 * (h : ℝ)) * (u ^ (12 : ℕ) * μ ^ 2)
          ≤ Real.exp (11 + Lc) * (u ^ (12 : ℕ) * μ ^ 2) :=
        mul_le_mul_of_nonneg_right he20b (by positivity)
      nlinarith [hmul, hstone]
    have hβsq : β ^ 2 ≤ 4 * μ ^ 2 := by nlinarith
    have h2 : 12 * (256 * ((h : ℝ) * u ^ (12 : ℕ)) * β ^ 2)
        ≤ 12288 * ((h : ℝ) * u ^ (12 : ℕ)) * μ ^ 2 := by
      nlinarith [hp12, hh0, hβsq]
    rw [mul_div_assoc', div_le_div_iff₀ hX0 (by norm_num : (0 : ℝ) < 2)]
    linarith [h1, h2]
  calc 12 * (W * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2))
      ≤ 12 * (64 * ((h : ℝ) * u ^ (12 : ℕ)) * X
          * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2)) := by linarith
    _ = 12 * (1024 * ((h : ℝ) * u ^ (12 : ℕ)) * β / Pr)
          + 12 * (256 * ((h : ℝ) * u ^ (12 : ℕ)) * β ^ 2 / X) := by rw [hval]; ring
    _ ≤ μ ^ (-(1 / 500) : ℝ) := by linarith

end RowsHL

set_option maxHeartbeats 400000 in
-- the charge adds three binders and `hLu` to the source's context; its closing `linarith`s
-- ran out of the default budget (census build of this half)
/-- `s13CapEps_EP2_gate_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`, and the row
that SUPPLIES the three `εr` rows' tower floor: `hLu : 50 + Lc ≤ log u` at `u := log H` is
`zTower_loglog_at_H hb hflL`, and the twin's weakening of its cap to the raised-cap rows' is
gone.  Every other step is the source's. -/
theorem s13CapEps_EP2_gate_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s P Q : ℕ} {C Tann εr : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hεr : theta293 - 1 / 500 ≤ εr) (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hT0 : 0 ≤ Tann) (hTX : Tann ≤ (((A + s : ℕ)) : ℝ))
    (hP83 : P83 (((A + s : ℕ)) : ℝ) theta293 ≤ (P : ℝ))
    (hgrade : Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log (((A + s : ℕ)) : ℝ))
              * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293))) :
    12 * s13CapEP2 C q (A + s) P Q Tann
      ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + εr) := by
  obtain ⟨hu, hμ, hΛ, hφ⟩ := s13_capEps_register_LH_L hh hL0 hhL hfl hb hflL
  set u : ℝ := Real.log (H : ℝ) with hudef
  -- ⟦AT THE CHARGE⟧ the three rows' tower floor `50 + Lc ≤ log u` IS `50 + Lc ≤ loglog H`
  have hLu : (50 : ℝ) + Lc ≤ Real.log u := zTower_loglog_at_H hb hflL
  set X : ℝ := (((A + s : ℕ)) : ℝ) with hXdef
  set μ : ℝ := Real.log X with hμdef
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hX1 : (1 : ℝ) < X := by
    rcases lt_or_ge 1 X with hc | hc
    · exact hc
    · have hnp : Real.log X ≤ 0 := Real.log_nonpos (by positivity) hc
      rw [← hμdef] at hnp
      linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hp12 : (0 : ℝ) < u ^ (12 : ℕ) := pow_pos hu0 12
  have hu121 : (1 : ℝ) ≤ u ^ (12 : ℕ) := one_le_pow₀ (by linarith)
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hhu121 : (1 : ℝ) ≤ (h : ℝ) * u ^ (12 : ℕ) := by nlinarith
  have hhu0 : (0 : ℝ) < (h : ℝ) * u ^ (12 : ℕ) := by linarith
  have hφ0 : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  have hq : 0 < q := hb.2.2.2.1
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have htot : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hWval : s13CapEpsW q (A + s) Tann
      = 4 * (2 * (q.totient : ℝ) * Tann + 7 * (q.totient : ℝ) * (2 * X) / q) := by
    simp only [s13CapEpsW, hXdef]
    push_cast
    ring
  have hW0 : 0 ≤ s13CapEpsW q (A + s) Tann := by
    rw [hWval]
    have h1 : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * Tann := by positivity
    have h2 : (0 : ℝ) ≤ 7 * (q.totient : ℝ) * (2 * X) / q := by positivity
    linarith
  have hW : s13CapEpsW q (A + s) Tann ≤ 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X := by
    rw [hWval]
    have h1 : 2 * (q.totient : ℝ) * Tann ≤ 2 * ((h : ℝ) * u ^ (12 : ℕ)) * X := by nlinarith
    have hfrac : 7 * (q.totient : ℝ) * (2 * X) / q ≤ 14 * X := by
      rw [div_le_iff₀ hqR]
      nlinarith
    nlinarith
  have hrow1 : 12 * (4160 * (q.totient : ℝ) * μ ^ (-theta293)) ≤ μ ^ (-(1 / 500) : ℝ) :=
    capeps_row_phi_h_L hh hL0 hhL hu hμ hΛ hLu hφ0 hφ
  have hrow3 : 12 * (s13CapEpsW q (A + s) Tann * s13MtailBand C (A + s) P Q)
      ≤ μ ^ (-(1 / 500) : ℝ) := by
    rw [s13MtailBand]
    exact capeps_row_tail_h_L hh hL0 hhL hu hμ hΛ hLu hX0 rfl hW0 hW hC0 hC hgrade
  have hrow2 : 12 * (s13CapEpsW q (A + s) Tann
      * (16 * Real.logb 2 (2 * X) / (X * (P : ℝ)) + endMass (A + s)))
      ≤ μ ^ (-(1 / 500) : ℝ) := by
    have hend : endMass (A + s) = 4 * (Real.logb 2 (2 * X)) ^ 2 / X ^ 2 := by
      rw [endMass]
    have hβ0 : (0 : ℝ) ≤ Real.logb 2 (2 * X) :=
      Real.logb_nonneg (by norm_num) (by linarith)
    have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hβ : Real.logb 2 (2 * X) ≤ 2 * μ := by
      have hlog : Real.log (2 * X) = Real.log 2 + μ := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hX0)]
      rw [Real.logb, hlog, div_le_iff₀ (by linarith)]
      nlinarith
    have hPr : Real.exp (μ ^ (1 - theta293)) ≤ (P : ℝ) := by
      have hz : P83 X theta293 = Real.exp (μ ^ (1 - theta293)) := by rw [P83]
      rw [← hz]; exact hP83
    rw [hend]
    exact capeps_row_p2_h_L hh hL0 hhL hu hμ hΛ hLu hX0 rfl hW0 hW hβ0 hβ hPr
  have hmax : s13CapEP2 C q (A + s) P Q Tann ≤ μ ^ (-(1 / 500) : ℝ) / 12 := by
    rw [s13CapEP2]
    refine max_le (by linarith) (max_le ?_ (by linarith))
    have := hrow2
    linarith
  have hmono : μ ^ (-(1 / 500) : ℝ) ≤ μ ^ (-theta293 + εr) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  linarith

/-- `s13CapEps_q_arcDen_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap
binder becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor
`hflL` passed down.  BODY: the source's, verbatim. -/
theorem s13CapEps_q_arcDen_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (q : ℝ) ≤ arcDen 12 (A + s) := by
  have harcpow : arcDen 12 (A + s) = Real.log (((A + s : ℕ)) : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [harcpow]
  exact s13CapGrid_q_logX_LH_L hh hL0 hhL hfl hb hflL

/-- `s13CapEps_all_LH` at the charge — SUPPLIER-SWAP of the twin at `log h ≤ 9`: the cap binder
becomes `{Lc} (0 ≤ Lc) (log h ≤ Lc)`, every capped callee its `_L` twin, the tower floor `hflL`
passed down.  BODY: the source's, verbatim. -/
theorem s13CapEps_all_LH_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    {R : ChowlaRegime} {M H L q j A s P Q : ℕ} {C Tann εr : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hεr : theta293 - 1 / 500 ≤ εr) (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hT0 : 0 ≤ Tann) (hTX : Tann ≤ (((A + s : ℕ)) : ℝ))
    (hP83 : P83 (((A + s : ℕ)) : ℝ) theta293 ≤ (P : ℝ))
    (hgrade : Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log (((A + s : ℕ)) : ℝ))
              * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293))) :
    0 ≤ εr
      ∧ (8640 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ εr
      ∧ 12 * s13CapEP2 C q (A + s) P Q Tann
          ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + εr)
      ∧ (q : ℝ) ≤ arcDen 12 (A + s)
      ∧ 4160 * (q.totient : ℝ) * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
          ≤ s13CapEP2 C q (A + s) P Q Tann
      ∧ 4 * (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * (A + s) : ℕ)) : ℝ) / q)
          * (16 * Real.logb 2 (2 * (((A + s : ℕ)) : ℝ))
              / ((((A + s : ℕ)) : ℝ) * (P : ℝ)) + endMass (A + s))
          ≤ s13CapEP2 C q (A + s) P Q Tann
      ∧ 4 * (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * (A + s) : ℕ)) : ℝ) / q)
          * s13MtailBand C (A + s) P Q
          ≤ s13CapEP2 C q (A + s) P Q Tann :=
  ⟨s13CapEps_epsr_nonneg hεr, s13CapEps_abs8640_LH_L hh hL0 hhL hfl hb hflL hεr,
    s13CapEps_EP2_gate_LH_L hh hL0 hhL hfl hb hflL hεr hC0 hC hT0 hTX hP83 hgrade,
    s13CapEps_q_arcDen_LH_L hh hL0 hhL hfl hb hflL, s13CapEps_phi_row C q (A + s) P Q Tann,
    s13CapEps_p2_row C q (A + s) P Q Tann, s13CapEps_tail_row C q (A + s) P Q Tann⟩

set_option maxHeartbeats 1000000 in
-- as the source: 37 structure fields checked against the per-block gate in one `exact`
/-- `s16_capGate_supply_LH_gk_sharpT0_kswin` at the charge — THE SPINE: SUPPLIER-SWAP of the twin
at `log h ≤ 9` (the grid, floor, pins and `εr` waves and the two grid leaves, each by its `_L`
twin); the tower floor `hflL : 50 + Lc ≤ loglog R.Hlo` is a binder beside `hfl`.  BODY: the
source's. -/
theorem s16_capGate_supply_LH_gk_sharpT0_kswin_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc)
    (K : ℕ) {Cq cs T₀ Kq Ks C : ℝ} {R : ChowlaRegime} {M : ℕ}
    {epsf : ℕ → ℝ}
    (hM : 1 ≤ M) (hfl : loglogFloor50 ≤ R.Hlo)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) (hcs : Real.exp (-100) ≤ cs)
    (hblk : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s → s13BlockFloor_L_gk K M ≤ A + s)
    (hT₀ : T₀ ≤ Real.exp (Real.sqrt ((R.Hlo : ℕ) : ℝ) / 2)) (hKq : Kq ≤ Real.exp 100)
    (hKs0 : 0 < Ks)
    (hKsw : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16)
    (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hεr : ∀ A : ℕ, theta293 - 1 / 500 ≤ epsf A)
    (hcap : S16BaseScaleCap96_LH_gk h K R M) (hcof : S16CofactorSupply_LH_gk h K Cq R M) :
    ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
        2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
        5 ≤ Real.log (Real.log (2 * T)) →
        ∃ (P Q : ℕ) (Rrad Rbd CR EP2 : ℝ),
          S13CapGatePerBlock_L_gk K Cq cs T₀ Kq Ks C M (A + s) q P Q (A + s) (2 * T)
            Rrad Rbd CR EP2 (epsf (A + s)) := by
  intro H L q j A s hb T hTlo hThi hTgate hTll
  obtain ⟨Rrad, Rbd, CR, hRbd0, hRbdg, hCqg, hRsock⟩ := hcof H L q j A s hb T hTlo hThi
  -- the grid wave, at the linear door
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, -, g17, g18⟩ :=
    s13CapGrid_all_LH_gk_L hh hL0 hhL K hM (le_refl (1 : ℝ)) hfl hb hflL (hblk H L q j A s hb) hTlo
      hThi
  -- `1 < 2T` off the annulus gate
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hT1 : (1 : ℝ) < 2 * T := by
    have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
    linarith
  have hT0le : (0 : ℝ) ≤ 2 * T := by linarith
  have hAN : A ≤ A + s := Nat.le_add_right _ _
  have hTflo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ 2 * T := by linarith
  -- the floor wave, at the linear door
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, -⟩ :=
    s13CapFloor_all_LH_gk_sharpT0_kswin_L hh hL0 hhL K hfl hb hflL hM hAN hTflo g6 hT₀ hKq hKs0 hKsw
  -- the eps wave, LADDER-BLIND
  obtain ⟨hP83pin, hgradepin⟩ := s13CapEps_pins_supply_LH_L hh hL0 hhL hfl hb hflL
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ :=
    s13CapEps_all_LH_L hh hL0 hhL hfl hb hflL (hεr (A + s)) hC0 hC hT0le hThi hP83pin hgradepin
  refine ⟨s13BandP (A + s), s13BandQ (A + s), Rrad, Rbd, CR,
    s13CapEP2 C q (A + s) (s13BandP (A + s)) (s13BandQ (A + s)) (2 * T), ?_⟩
  exact
    { logX_eight := g1
      H83_two := g2
      QTann := f1
      kappa30Q := f2
      q_logX := g3
      T0_Tann := f3
      floor1 := f4
      floor2 := f5
      floor3 := f6
      floor4 := f7
      logqT_L := g4
      P_low := g5
      Q2_reg := g6
      Q_pos := g7
      Q_high := g8
      P_le_Q := g9
      budget := fun i hi =>
        s16_budget_field_L_gk_96 K hM hb.2.2.2.1 g7 g1
          (s13CapGrid_Lambda_lo_L hh hL0 hhL hfl hb hflL) g3 hT1 hThi g8 g6 (hcap H L q j A s hb) hi
      Hj := g10
      B3 := g11
      BT := g12
      kappa30 := g13
      BT10 := g14
      WL := g15
      gate := s16_capGrid_gate_cs hcs (s13CapGrid_mu_2000_L hh hL0 hhL hfl hb hflL)
        (s13CapGrid_Lambda_lo_L hh hL0 hhL hfl hb hflL)
      Rbd_nonneg := hRbd0
      Rbd_grade := hRbdg
      Cq_gate := hCqg
      Rbd_socket := hRsock
      epsr_nonneg := e1
      abs8640 := e2
      EP2_gate := e3
      q_arcDen := e4
      phi_row := e5
      p2_row := e6
      tail_row := e7
      Q_hundred := g17
      band_product := g18 }

set_option maxHeartbeats 1600000 in
-- as the source: the eighteen-slot `hcapWS` family re-elaborates against the wire's own
-- shape, here under the `∀ K` bracket
/-- `s15_crossing_supplied_LH_gk_ceiling_sharpT0_khoist_csfree_kswin` at the charge — THE ROOT
(half 2's twin 9): SUPPLIER-SWAP of the twin at `log h ≤ 9` (the fused wire and the cap-gate
supply, by their `_L` twins).  The tower floor `50 + Lc ≤ loglog R.Hlo` is an ANTECEDENT after
`loglogFloor50 ≤ R.Hlo` inside the `∀ R M` block, passed to the supply.  BODY: the source's. -/
theorem s15_crossing_supplied_LH_gk_ceiling_sharpT0_khoist_csfree_kswin_L {h : ℕ} (hh : 0 < h)
    {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) :
    ∃ Cq cs T₀ Kq Ks C : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ Real.exp 100 ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      ∀ K : ℕ,
        (Kq ≤ Real.exp 100 →
        ∀ (R : ChowlaRegime) (M : ℕ), 1 ≤ M → loglogFloor50 ≤ R.Hlo →
          (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16 →
          T₀ ≤ Real.exp (Real.sqrt ((R.Hlo : ℕ) : ℝ) / 2) →
          (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s → s13BlockFloor_L_gk K M ≤ A + s) →
          S16CofactorSupply_LH_gk h K Cq R M → S16BaseScaleCap96_LH_gk h K R M →
          S15CrossingBound_LH_gk h K R M) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hwire⟩ :=
    m4_fuse_hcap_of_capWS_LH_gk_ceiling_khoist_cs_L hh hL0 hhL
  obtain ⟨C, hC0, hC40, hband⟩ := m4_tail_mass_at_band_bounded
  refine ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40, ?_⟩
  intro K hKq R M hM hfl hflL hKsw hT₀ hblk hcof hcap
  -- ⟦THE cs RIDER, SPENT FROM THE PREFIX⟧ `hcsf` is a carried conjunct, not an antecedent;
  -- ⟦THE Ks RIDER, SPENT AS A WINDOW⟧ `hKs0` is the prefix's own positivity
  have hgate := s16_capGate_supply_LH_gk_sharpT0_kswin_L hh hL0 hhL K hM hfl hflL hcsf hblk hT₀ hKq
    hKs0 hKsw hC0 hC40
    (fun _ => le_rfl) hcap hcof
  refine hwire K R M liouvilleC (fun _ => theta293 - 1 / 500) liouvilleC_norm_le_one ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨P, Q, Rrad, Rbd, CR, EP2, hg⟩ := hgate H L q j A s hsb T hTlo hThi hTgate hTll
  have hq : 1 ≤ q := hsb.2.2.2.1
  have hA : 0 < A := hsb.2.2.2.2.2.2.2.1
  have hNd : 1 ≤ A + s := by omega
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by have := hg.logX_eight; linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
  have hT1 : (1 : ℝ) < 2 * T := by linarith
  exact doorCapBundle_at_workingPoint_perBlock_L_gk K hband hM hNd hq hg hT1 hThi hTll

/-! ## §N — KSWIN AT THE CHARGE (H3→H4)

G12b's kswin hop re-run on the Z forms, with the crossing spine head at the charge (§M's root) and
rung 2's charge-paying lines (its `flat_kswin_generic_epsW`) as the second template. -/

set_option maxHeartbeats 400000 in
-- the charge adds the design-floor bridge and the block's floor to G12b's body; measured: the
-- default budget is exhausted at the declaration (a scratch build of this hop)
/-- **⟦H3→H4 AT THE CHARGE⟧ — `flat_kswin_generic_h_Z`.** G12b's `flat_kswin_generic_h_g12b`
(`StridePairReceiptG12b.lean:703`) on the Z forms, at `Lc := log c + L`.  The spine head is §M's
root at the TRUE `h` (`log h ≤ L ≤ log c + L`), and its new antecedent `50 + Lc ≤ loglog R.Hlo` is
paid as §J pays `hfloor`: `3.2·A ≤ loglog R.Hlo` (`hdes`) and `3.2·A ≥ 1.6·162 + 1.6·(10 + 2·Lc)
= 275.2 + 3.2·Lc ≥ 50 + Lc`.  Rule (ii), at `h := c`: `flat_witFloor_eq_designBase_L` (the form's
charge pin `1/(500·c) ≤ ε`) and the bumped witness (`1/(838400·2^12·c²) ≤ 1/(838400·c) ≤ δ₀` at
`c ≤ 4096·c²`; count ceiling `Kb := 2^283·c^20·h`, `log Kb ≤ 197 + 20·Lc` by `zCount_form`).
The block reads `3·Lc ≤ loglog H` from `hdes` (`3.2·(10 + 2·Lc) ≥ 3·Lc`).  The ε-probe's
`a := 1` reads `log 1 ≤ L` from `0 ≤ L`, where G12b read `1 ≤ 8103`.  The conditional's
design floor `flatDesignBase A ≤ U1floor` is paid by `flatDesignBase A ≤ flatWitFloor`.
No numeral cap on `h`, `c`, `L` or `a` is read. -/
theorem flat_kswin_generic_h_Z (h : ℕ) (hh : 0 < h) (ε : ℚ) (c : ℕ) (L : ℝ)
    (Awin : ℝ) (_hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hcond : FlatConditionalFormHG_Z h ε c L Awin P) :
    FlatKswinFormHG_Z h ε c L Awin P := by
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hc1, hL0, hhL, hεpin, hcε, hδpin, hKcb, hMflb, hβ, hcondU⟩ := hcond
  -- ⟦THE CHARGE⟧ `Lc := log c + L`
  have hc0 : 0 < c := by omega
  have hlogc0 : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_natCast_nonneg c
  have hLc0 : (0 : ℝ) ≤ Real.log (c : ℝ) + L := by linarith
  have hhLc : Real.log (h : ℝ) ≤ Real.log (c : ℝ) + L := by linarith
  have hLcc : Real.log (c : ℝ) ≤ Real.log (c : ℝ) + L := by linarith
  -- ⟦THE CROSSING CONSTANTS, HOISTED ABOVE THE LEVER⟧ — the spine head at the charge
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40,
    hsupplyU⟩ :=
    s15_crossing_supplied_LH_gk_ceiling_sharpT0_khoist_csfree_kswin_L hh hLc0 hhLc
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant:
  -- rung 2's re-minted arm `162 + 2·Lc`, which pays `162 ≤ A` and `10 + 2·Lc ≤ A` at `0 ≤ Lc`
  obtain ⟨_Ct0, -, -, hcond0⟩ := hcondU 0
  set A0 : ℝ := max (162 + 2 * (Real.log (c : ℝ) + L)) (budgetAFlat (ε : ℝ) β) with hA0
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond0 A0 (le_trans (by linarith) (le_max_left _ _)) (le_max_right _ _)
      (le_trans (by linarith) (le_max_left _ _))
  have hzero : XCeilRiderStrictAt (50 + (Real.log (c : ℝ) + L)) ε (fun _ _ : ℕ => 0) :=
    xceilRiderStrictAt_zero _ ε
  -- the `a := 1` probe: `log 1 ≤ L` from `0 ≤ L` (G12b: `1 ≤ 8103`)
  obtain ⟨R0, hR0eps, -, -, -, -, -, -⟩ :=
    hbody0 1 (max Hcap0 (max (flatDesignBase A0) loglogFloor50)) (fun _ _ => 0) le_rfl
      (by simpa using hL0) hzero le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  -- ⟦THE CHARGE PIN AT `c`, IN THE REAL SPELLING⟧ (rung 2's cast)
  have hcQ1 : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hεRc : (1 : ℝ) / (500 * (c : ℝ)) ≤ (ε : ℝ) := by
    have hq := hcε
    rw [div_le_iff₀ (by linarith)] at hq
    have h1R : (1 : ℝ) ≤ (ε : ℝ) * (500 * (c : ℝ)) := by exact_mod_cast hq
    rw [div_le_iff₀ (by linarith)]
    linarith
  refine ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hc1, hL0, hhL, hεpin, hcε, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0,
    hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  have hsupply := hsupplyU K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA26 hAwin hAge hAL hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge hAL
  refine ⟨fun hopq => flat_witFloor_eq_designBase_L (h := c) hc0 hLc0 hLcc hA26 hAL hβ hεRc
    hε2 hε hcε hAge hopq, ?_⟩
  intro hx0win hopq hT₀ hKsw U1floor hU hUceil a g ha haL hg
  -- ⟦Δ3⟧ the caller's floor, and the three monotone lifts off `hU`
  have hWpos : (0 : ℝ) < Real.log ((flatWitFloor ε β A Hopq : ℕ) : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos _) (flatWitFloor_log_ge hA26)
  have hWposN : (0 : ℝ) < ((flatWitFloor ε β A Hopq : ℕ) : ℝ) := by
    rcases (Nat.cast_nonneg (flatWitFloor ε β A Hopq) : (0 : ℝ) ≤ _).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [← heq] at hWpos
      simp at hWpos
  have hUR : ((flatWitFloor ε β A Hopq : ℕ) : ℝ) ≤ ((U1floor : ℕ) : ℝ) := by exact_mod_cast hU
  have hUlog : Real.log ((flatWitFloor ε β A Hopq : ℕ) : ℝ)
      ≤ Real.log ((U1floor : ℕ) : ℝ) := Real.log_le_log hWposN hUR
  have hUll : Real.log (Real.log ((flatWitFloor ε β A Hopq : ℕ) : ℝ))
      ≤ Real.log (Real.log ((U1floor : ℕ) : ℝ)) := Real.log_le_log hWpos hUlog
  -- ⟦THE CONDITIONAL'S DESIGN FLOOR⟧ `flatDesignBase A ≤ flatDesignFloor A ≤ flatWitFloor`,
  -- and `flatWitFloor ≤ U1floor`
  have hDB : flatDesignBase A ≤ flatWitFloor ε β A Hopq := by
    unfold flatWitFloor flatDesignFloor
    exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_right (le_max_right _ _)))
  have hcapW := flatCap_le_flatWitFloor hCapLe
  have hU' : max Hcap (max (flatDesignBase A) loglogFloor50) ≤ U1floor := by
    refine max_le (le_trans (le_trans (le_max_left _ _) hcapW) hU)
      (max_le (le_trans hDB hU) (le_trans (le_trans ?_ hcapW) hU))
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨R, hReps, hHlo, hRg, hstride, hRx, hRtow, hfire⟩ :=
    hbody a U1floor g ha haL hg hU'
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]
    exact le_trans (flatWitFloor_design ε β A Hopq) hUll
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo]; exact hUceil
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hstride, hRx, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  -- ⟦THE REGISTER, SUPPLIED⟧ at the flat design modulus
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  -- `1/(2^9·c) ≤ 1/(500·c) ≤ ε` (rule (ii), at `c`): `500 ≤ 512 = 2^9`
  have heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps := by
    rw [hReps]
    have h512 : (500 : ℚ) * (c : ℚ) ≤ 2 ^ 9 * (c : ℚ) := by
      have h9 : (2 : ℚ) ^ 9 = 512 := by norm_num
      rw [h9]; linarith
    have hb : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ 1 / (500 * (c : ℚ)) :=
      one_div_le_one_div_of_le (by linarith) h512
    linarith [hcε]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact le_trans (flatWitFloor_log_ge hA26) hUlog
  -- ⟦THE BRIDGE⟧ the `A`-scoped window becomes the regime-scoped one at the flat floor
  have hKswR : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16 := by linarith
  -- the witness's `δ₀`-binder at `h := c`: `1/(838400·2^12·c²) ≤ 1/(838400·c) ≤ δ₀`, from
  -- `c ≤ 4096·c²` at `c ≥ 1`.  The `2^12` is the landed witness's own binder, read at `h := c`
  -- (not a cap on anything this hop carries), so its TYPE is taken from the witness below by
  -- unification rather than restated here.
  have hcc : (c : ℝ) ≤ (c : ℝ) ^ 2 := le_self_pow₀ hcR1 (by norm_num)
  have hc2 : (0 : ℝ) ≤ (c : ℝ) ^ 2 := sq_nonneg _
  -- the count ceiling `Kb := 2^283·c^20·h`, `log Kb ≤ 197 + 20·Lc` (§C)
  have hh1R : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hKb1 : (1 : ℝ) ≤ 2 ^ 283 * (c : ℝ) ^ 20 * (h : ℝ) := by
    have h1 := epsRung2_one_le_Kb hc1
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ 2 ^ 283 * (c : ℝ) ^ 20 * (h : ℝ) := mul_le_mul h1 hh1R zero_le_one (by linarith)
  have hKbL : Real.log (2 ^ 283 * (c : ℝ) ^ 20 * (h : ℝ)) ≤ 197 + 20 * (Real.log (c : ℝ) + L) :=
    zCount_form (by linarith) le_rfl hc1 hh hhL hL0
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win_L hA26 K hKw (h := c) hc0 hLc0 hLcc hAL
    hδ₀ (le_trans (one_div_le_one_div_of_le (by linarith) (by norm_num; linarith)) hδpin)
    hKc hKb1 hKcb hKbL hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win heps hlo hwin
  -- ⟦THE CROSSING, SUPPLIED⟧ the block floor off the register's own `blk` line
  have hfl : loglogFloor50 ≤ R.Hlo := by
    rw [hHlo]; exact le_trans (flatWitFloor_ll _ _ _ _) hU
  -- ⟦THE SPINE'S TOWER FLOOR⟧ `50 + Lc ≤ 3.2·A ≤ loglog R.Hlo`, from `10 + 2·Lc ≤ A`, `162 ≤ A`
  have hflL : (50 : ℝ) + (Real.log (c : ℝ) + L) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    linarith [hdes]
  -- the block's floor, as §J: `flatDesignBase A ≤ R.Hlo` gives `3.2·A ≤ loglog H` on the window
  have hdesR : flatDesignBase A ≤ R.Hlo := by rw [hHlo]; exact le_trans hDB hU
  have hdesH : ∀ H : ℕ, R.Hlo ≤ H → 3.2 * A ≤ Real.log (Real.log (H : ℝ)) := by
    intro H hlo
    have hDge : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
      rw [flatDesignBase]; exact Nat.le_ceil _
    have hBH : ((flatDesignBase A : ℕ) : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast le_trans hdesR hlo
    have h1 : Real.exp (Real.exp (3.2 * A)) ≤ (H : ℝ) := le_trans hDge hBH
    have h2 : Real.exp (3.2 * A) ≤ Real.log (H : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h
    have h := Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at h
  -- `3·Lc ≤ 3.2·(10 + 2·Lc)/2 ≤ 3.2·A` at `0 ≤ Lc`
  have hfloor3 : ∀ H : ℕ, R.Hlo ≤ H →
      3 * (Real.log (c : ℝ) + L) ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo => by linarith [hdesH H hlo]
  have hblk : ∀ H L' q j Aw s : ℕ, SocketBaseLH h R (flatDoorM A) H L' q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L' q j Aw s hb
    exact s15_block_at_socketH_L_gk_L K hh hLc0 hhLc hb
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) (hfloor3 H hb.1) hsel.blk
  exact hfire (flatDoorM A) hKw hsel
    (hsupply hKqb R (flatDoorM A) hM1 hfl hflL hKswR
      (by
        rw [hHlo]
        refine le_trans hT₀ (Real.exp_le_exp.mpr ?_)
        have hs : Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ)
            ≤ Real.sqrt ((U1floor : ℕ) : ℝ) := Real.sqrt_le_sqrt hUR
        linarith)
      hblk hcof hcapsc)

/-! ## §O — THE FOUR STRIDE LIFTS AT THE CHARGE (the freeze's row L1, this half's cell 21)

The four `_b9` stride suppliers of `Salt/Entropy/Chowla/StridePair.lean` (`:842–1214`) read the
numeral cap `a ≤ 8103` (or its consequence `log a ≤ 9`, or the pin floor
`1/4051500 = 1/(500·8103)`) at exactly the sites named in each docstring below; the `_L` lifts
replace each such site by a binder or by the design base, and are the sources' bodies VERBATIM
elsewhere.  The landed `StridePair.lean` is not touched. -/

/-- **⟦F3-P19 AT THE CHARGE⟧** (`loglog_mul_flatDesignBase_le_L`) —
`loglog_mul_flatDesignBase_le_b9` (`StridePair.lean:842`) with `ha9 : log a ≤ 9` REPLACED by
`haL : log a ≤ L` and `hLA : L ≤ A`.  The cap was read only in `hub`
(`log a + log 2 + E ≤ 2E`); at the charge it closes from
`hE519' : A + 1 ≤ exp (3.2·A)` (`Real.add_one_le_exp` and `A ≤ 3.2·A`):
`log a + log 2 + E ≤ L + 1 + E ≤ A + 1 + E ≤ 2E`, slack `E − A − 1 ≥ 2.2·A ≥ 356.4`.  BODY otherwise
verbatim. -/
theorem loglog_mul_flatDesignBase_le_L {A : ℝ} (hA : 162 ≤ A) {a : ℕ} (ha : 1 ≤ a) {L : ℝ}
    (haL : Real.log (a : ℝ) ≤ L) (hLA : L ≤ A) :
    Real.log (Real.log ((a * flatDesignBase A : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
  have hge : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    rw [flatDesignBase]; exact Nat.le_ceil _
  have hceil : ((flatDesignBase A : ℕ) : ℝ) ≤ 2 * Real.exp (Real.exp (3.2 * A)) := by
    rw [flatDesignBase]
    have h1 : ((⌈Real.exp (Real.exp (3.2 * A))⌉₊ : ℕ) : ℝ)
        ≤ Real.exp (Real.exp (3.2 * A)) + 1 := (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
    have h2 : (1 : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by
      have := Real.add_one_le_exp (Real.exp (3.2 * A)); linarith [Real.exp_pos (3.2 * A)]
    linarith
  have hE519 : (519 : ℝ) ≤ Real.exp (3.2 * A) := by
    have := Real.add_one_le_exp (3.2 * A); linarith
  have hE519' : A + 1 ≤ Real.exp (3.2 * A) := by
    have := Real.add_one_le_exp (3.2 * A); linarith
  have hDpos : (0 : ℝ) < ((flatDesignBase A : ℕ) : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hge
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hlogD_ge : Real.exp (3.2 * A) ≤ Real.log ((flatDesignBase A : ℕ) : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hge
    rwa [Real.log_exp] at h
  have hlogD_le : Real.log ((flatDesignBase A : ℕ) : ℝ)
      ≤ Real.log 2 + Real.exp (3.2 * A) := by
    have h := Real.log_le_log hDpos hceil
    rwa [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at h
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hprod : Real.log ((a * flatDesignBase A : ℕ) : ℝ)
      = Real.log (a : ℝ) + Real.log ((flatDesignBase A : ℕ) : ℝ) := by
    rw [show ((a * flatDesignBase A : ℕ) : ℝ) = (a : ℝ) * ((flatDesignBase A : ℕ) : ℝ) by
      push_cast; ring, Real.log_mul (ne_of_gt hapos) (ne_of_gt hDpos)]
  have hloga : (0 : ℝ) ≤ Real.log (a : ℝ) := Real.log_nonneg (by exact_mod_cast ha)
  have hpos2 : (0 : ℝ) < Real.log ((a * flatDesignBase A : ℕ) : ℝ) := by
    rw [hprod]; linarith
  have hub : Real.log ((a * flatDesignBase A : ℕ) : ℝ) ≤ 2 * Real.exp (3.2 * A) := by
    rw [hprod]; linarith [haL, hLA, hE519', hlog2]
  calc Real.log (Real.log ((a * flatDesignBase A : ℕ) : ℝ))
      ≤ Real.log (2 * Real.exp (3.2 * A)) := Real.log_le_log hpos2 hub
    _ = 3.2 * A + Real.log 2 := by
        rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]; ring

/-- **⟦F3-P20 AT THE CHARGE⟧** (`flatDesignBase_clears_stride_floors_L`) —
`flatDesignBase_clears_stride_floors_b9` (`StridePair.lean:885`) with the pin floor
`1/4051500 = 1/(500·8103)` REPLACED by the form's own pin at the MULTIPLIER `k`,
`1/(500·k) ≤ eps`, and `k` bounded through the charge (`log k ≤ L ≤ A`), plus the third floor
`500000·k³ ≤ flatDesignBase A` that pays the shrink's `hcop` and `hHlo` at the terminal.  DERIVED:
`⌈1/eps⌉₊ ≤ 500·k` (the source's `hceil` at `4051500 ↦ 500·k`); `k ≤ exp L ≤ exp A`;
`500 ≤ exp 7` and `500000 ≤ exp 14` (from `e > 2.7182818283`: `2.7182818283^7 = 1096.63…`,
`2.7182818283^14 = 1202604.2…`); `4 ≤ exp 3` (`1 + 3`); so
`4·(500·k)^4 ≤ exp (31 + 4·A)` and `500000·k³ ≤ exp (14 + 3·A)`; each exponent is
`≤ 2.56·A² ≤ exp (3.2·A)` (`capeps_sq_le_exp`: `y²/4 ≤ exp y`), room at `A = 162`:
`2.56·162² = 67184.64` against `31 + 4·162 = 679`; and `exp (exp (3.2·A)) ≤ flatDesignBase A`.
`4000000 ≤ 4·500^4 ≤ 4·(500·k)^4`. -/
theorem flatDesignBase_clears_stride_floors_L {A : ℝ} (hA : 162 ≤ A) {k : ℕ} (hk : 1 ≤ k)
    {L : ℝ} (hkL : Real.log (k : ℝ) ≤ L) (hLA : L ≤ A) {eps : ℚ}
    (heps : (1 : ℚ) / (500 * (k : ℚ)) ≤ eps) :
    4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4 ≤ flatDesignBase A ∧ 4000000 ≤ flatDesignBase A ∧
      500000 * k ^ 3 ≤ flatDesignBase A := by
  have hkQ : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hk500 : (0 : ℚ) < 500 * (k : ℚ) := by linarith
  have heps0 : (0 : ℚ) < eps := lt_of_lt_of_le (by positivity) heps
  have hceil : ⌈(1 / eps : ℚ)⌉₊ ≤ 500 * k := by
    refine Nat.ceil_le.mpr ?_
    push_cast
    rw [div_le_iff₀ heps0]
    have h1 := (div_le_iff₀ hk500).mp heps
    linarith
  -- ⟦THE CHARGE BOUNDS `k`⟧ `k = exp (log k) ≤ exp L ≤ exp A`
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkexp : (k : ℝ) ≤ Real.exp A := by
    rw [← Real.exp_log hkR]; exact Real.exp_le_exp.mpr (le_trans hkL hLA)
  -- ⟦THE TWO NUMERALS⟧ `500 ≤ exp 7`, `500000 ≤ exp 14`, off `e > 2.7182818283`
  have he : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have h7 : (500 : ℝ) ≤ Real.exp 7 := by
    have hpow : (2.7182818283 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) he 7
    rw [← Real.exp_nat_mul] at hpow
    have h7e : ((7 : ℕ) : ℝ) * 1 = 7 := by norm_num
    rw [h7e] at hpow
    linarith [show (500 : ℝ) ≤ 2.7182818283 ^ 7 by norm_num]
  have h14 : (500000 : ℝ) ≤ Real.exp 14 := by
    have hpow : (2.7182818283 : ℝ) ^ 14 ≤ Real.exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) he 14
    rw [← Real.exp_nat_mul] at hpow
    have h14e : ((14 : ℕ) : ℝ) * 1 = 14 := by norm_num
    rw [h14e] at hpow
    linarith [show (500000 : ℝ) ≤ 2.7182818283 ^ 14 by norm_num]
  have h3 : (4 : ℝ) ≤ Real.exp 3 := by have := Real.add_one_le_exp (3 : ℝ); linarith
  -- ⟦THE TOWER⟧ `exp (exp (3.2·A)) ≤ flatDesignBase A`, and `2.56·A² ≤ exp (3.2·A)`
  have hge : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    rw [flatDesignBase]; exact Nat.le_ceil _
  have hsq : (3.2 * A) ^ 2 / 4 ≤ Real.exp (3.2 * A) := capeps_sq_le_exp (by linarith)
  have hlin1 : 31 + 4 * A ≤ Real.exp (3.2 * A) := by nlinarith
  have hlin2 : 14 + 3 * A ≤ Real.exp (3.2 * A) := by nlinarith
  -- ⟦FLOOR 1⟧ `4·(500·k)^4 ≤ exp (31 + 4·A) ≤ flatDesignBase A`
  have h500k : 500 * (k : ℝ) ≤ Real.exp (7 + A) := by
    rw [Real.exp_add]
    exact mul_le_mul h7 hkexp (by positivity) (Real.exp_pos _).le
  have hF1R : (4 : ℝ) * (500 * (k : ℝ)) ^ 4 ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    have hp : (500 * (k : ℝ)) ^ 4 ≤ Real.exp (7 + A) ^ 4 :=
      pow_le_pow_left₀ (by positivity) h500k 4
    have hexp4 : Real.exp 3 * Real.exp (7 + A) ^ 4 = Real.exp (31 + 4 * A) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    have hstep : (4 : ℝ) * (500 * (k : ℝ)) ^ 4 ≤ Real.exp (31 + 4 * A) := by
      rw [← hexp4]
      exact mul_le_mul h3 hp (by positivity) (Real.exp_pos _).le
    exact le_trans hstep (le_trans (Real.exp_le_exp.mpr hlin1) hge)
  have hF1 : 4 * (500 * k) ^ 4 ≤ flatDesignBase A := by exact_mod_cast hF1R
  -- ⟦FLOOR 3⟧ `500000·k³ ≤ exp (14 + 3·A) ≤ flatDesignBase A`
  have hF3R : (500000 : ℝ) * (k : ℝ) ^ 3 ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    have hp : (k : ℝ) ^ 3 ≤ Real.exp A ^ 3 := pow_le_pow_left₀ hkR.le hkexp 3
    have hexp3 : Real.exp 14 * Real.exp A ^ 3 = Real.exp (14 + 3 * A) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have hstep : (500000 : ℝ) * (k : ℝ) ^ 3 ≤ Real.exp (14 + 3 * A) := by
      rw [← hexp3]
      exact mul_le_mul h14 hp (by positivity) (Real.exp_pos _).le
    exact le_trans hstep (le_trans (Real.exp_le_exp.mpr hlin2) hge)
  have hF3 : 500000 * k ^ 3 ≤ flatDesignBase A := by exact_mod_cast hF3R
  have hM : 4000000 ≤ 4 * (500 * k) ^ 4 := by
    have hp : 500 ^ 4 ≤ (500 * k) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    omega
  refine ⟨le_trans ?_ hF1, le_trans hM hF1, hF3⟩
  exact Nat.mul_le_mul (le_refl 4) (Nat.pow_le_pow_left hceil 4)

/-- **⟦F3-P3 AT THE CHARGE⟧ (def)** (`regimeShrinkX_stride_L`) — `regimeShrinkX_stride_b9`
(`StridePair.lean:917`) with the stride cap `ha8103 : a ≤ 8103` GONE.  The source read it at exactly
two sites, and BOTH are now HYPOTHESES of the def, paid by the caller at the terminal
(`strideDoorAllGradesW_holds`, from `flatDesignBase_clears_stride_floors_L`'s third floor
`500000·k³ ≤ flatDesignBase A` and the multiplier pin `1/(500·k) ≤ ε`): `hcop`
(`a ≤ ε²·Hlo'/2`, the source's `have` deleted) and `hHlo` (`a ≤ Hlo'`, the structure field).
The source's `hcop` block alone read `hm500` and `hHlo4Q`, so those two `have`s go with it, and
`hm500` alone read `heps500`, which is kept in the binder list as `_heps500` (read by nothing).
Every other field and `have` (`htower`, `hdrop`, `hbase`, `hHlohi`, `hPNT`) is the source's,
verbatim. -/
def regimeShrinkX_stride_L (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a)
    (_heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a)
    (hloM : 4000000 ≤ R.a * R.Hlo / a)
    (hcop : (a : ℚ) ≤ R.eps ^ 2 * ((R.a * R.Hlo / a : ℕ) : ℚ) / 2)
    (hHlo : a ≤ R.a * R.Hlo / a) : ChowlaRegime := by
  have htower : ∀ j : ℕ,
      chowlaTower R.C0 a (R.a * R.Hlo / a) j = chowlaTower R.C0 R.a R.Hlo j := by
    intro j
    rw [chowlaTower_eq_base_one R.C0 a (R.a * R.Hlo / a) j, Nat.mul_div_cancel' hdiv]
    exact (chowlaTower_eq_base_one R.C0 R.a R.Hlo j).symm
  have hdrop : towerDropSum R.C0 a (R.a * R.Hlo / a) R.J
      = towerDropSum R.C0 R.a R.Hlo R.J := by
    rw [towerDropSum_eq_base_one R.C0 a (R.a * R.Hlo / a) R.J, Nat.mul_div_cancel' hdiv]
    exact (towerDropSum_eq_base_one R.C0 R.a R.Hlo R.J).symm
  have hbase : 4000000 ≤ R.a * R.Hlo :=
    le_trans R.hHlo_floor (Nat.le_mul_of_pos_left _ R.ha)
  have hHlohi : R.a * R.Hlo / a ≤ R.Hhi := by
    refine le_trans (Nat.div_le_self _ _) (le_trans ?_ R.hfit)
    have h := chowlaTower_ge_base R.hC0 hbase R.J
    rw [← chowlaTower_eq_base_one R.C0 R.a R.Hlo R.J] at h
    exact h
  have hepsQ : (0 : ℚ) < R.eps := R.heps
  have hm_ge : (1 / R.eps : ℚ) ≤ ((⌈(1 / R.eps : ℚ)⌉₊ : ℕ) : ℚ) := Nat.le_ceil _
  have hem : (1 : ℚ) ≤ R.eps * ((⌈(1 / R.eps : ℚ)⌉₊ : ℕ) : ℚ) := by
    have h := mul_le_mul_of_nonneg_left hm_ge (le_of_lt hepsQ)
    rwa [mul_one_div, div_self (ne_of_gt hepsQ)] at h
  have hHlo4R : (4 : ℝ) * ((⌈(1 / R.eps : ℚ)⌉₊ : ℕ) : ℝ) ^ 4
      ≤ ((R.a * R.Hlo / a : ℕ) : ℝ) := by exact_mod_cast hlo4
  have hemR : (1 : ℝ) ≤ (R.eps : ℝ) * ((⌈(1 / R.eps : ℚ)⌉₊ : ℕ) : ℝ) := by exact_mod_cast hem
  have hPNT : Real.sqrt ((R.a * R.Hlo / a : ℕ) : ℝ)
      ≤ (R.eps : ℝ) ^ 2 * ((R.a * R.Hlo / a : ℕ) : ℝ) / 2 := by
    have hsqrtHlo : (2 : ℝ) * ((⌈(1 / R.eps : ℚ)⌉₊ : ℕ) : ℝ) ^ 2
        ≤ Real.sqrt ((R.a * R.Hlo / a : ℕ) : ℝ) := by
      have heq : Real.sqrt (4 * ((⌈(1 / R.eps : ℚ)⌉₊ : ℕ) : ℝ) ^ 4)
          = 2 * ((⌈(1 / R.eps : ℚ)⌉₊ : ℕ) : ℝ) ^ 2 := by
        rw [show (4 : ℝ) * ((⌈(1 / R.eps : ℚ)⌉₊ : ℕ) : ℝ) ^ 4
            = (2 * ((⌈(1 / R.eps : ℚ)⌉₊ : ℕ) : ℝ) ^ 2) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
      calc (2 : ℝ) * ((⌈(1 / R.eps : ℚ)⌉₊ : ℕ) : ℝ) ^ 2
          = Real.sqrt (4 * ((⌈(1 / R.eps : ℚ)⌉₊ : ℕ) : ℝ) ^ 4) := heq.symm
        _ ≤ Real.sqrt ((R.a * R.Hlo / a : ℕ) : ℝ) := Real.sqrt_le_sqrt hHlo4R
    have hsqrtnn : (0 : ℝ) ≤ Real.sqrt ((R.a * R.Hlo / a : ℕ) : ℝ) := Real.sqrt_nonneg _
    have hHloeq : Real.sqrt ((R.a * R.Hlo / a : ℕ) : ℝ)
        * Real.sqrt ((R.a * R.Hlo / a : ℕ) : ℝ) = ((R.a * R.Hlo / a : ℕ) : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have h2 : (2 : ℝ) ≤ (R.eps : ℝ) ^ 2 * Real.sqrt ((R.a * R.Hlo / a : ℕ) : ℝ) := by
      have hstep : (R.eps : ℝ) ^ 2 * (2 * ((⌈(1 / R.eps : ℚ)⌉₊ : ℕ) : ℝ) ^ 2)
          ≤ (R.eps : ℝ) ^ 2 * Real.sqrt ((R.a * R.Hlo / a : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrtHlo (sq_nonneg _)
      nlinarith [hstep, hemR,
        sq_nonneg ((R.eps : ℝ) * ((⌈(1 / R.eps : ℚ)⌉₊ : ℕ) : ℝ) - 1)]
    have h3 : 2 * Real.sqrt ((R.a * R.Hlo / a : ℕ) : ℝ)
        ≤ (R.eps : ℝ) ^ 2 * ((R.a * R.Hlo / a : ℕ) : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right h2 hsqrtnn
      rw [mul_assoc, hHloeq] at hh
      linarith [hh]
    linarith [h3]
  exact { x := R.x / a, ω := R.ω, a := a, eps := R.eps, Hlo := R.a * R.Hlo / a,
          Hhi := R.Hhi, C0 := R.C0, J := R.J,
          hx := hs.2.1, hω := R.hω, hωx := hs.2.2.1, ha := ha,
          heps := R.heps, heps1 := R.heps1,
          hHlo := hHlo,
          hHlohi := hHlohi, hC0 := R.hC0, hHlo_floor := hloM,
          hheadroom := hs.2.2.2.1, hcoprime := hcop,
          hfit := by rw [htower R.J]; exact R.hfit,
          hJcon := by rw [hdrop]; exact R.hJcon,
          hheadroom' := hs.2.2.2.2.1, hPHheadroom := hs.2.2.2.2.2.1,
          hPNTwindow := hPNT, hωbig := R.hωbig, hxbig := hs.2.2.2.2.2.2 }

/-- **⟦F3-P4 AT THE CHARGE⟧** — the projection family of `regimeShrinkX_stride_L`, at the new binder
list (`regimeShrinkX_stride_x_b9` and its siblings, `StridePair.lean:1010–1057`).  Each is `rfl`,
as at the source. -/
theorem regimeShrinkX_stride_x_L (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a)
    (hcop : (a : ℚ) ≤ R.eps ^ 2 * ((R.a * R.Hlo / a : ℕ) : ℚ) / 2)
    (hHlo : a ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride_L R a ha heps500 hs hdiv hlo4 hloM hcop hHlo).x = R.x / a := by
  rfl

/-- The `ω` projection of `regimeShrinkX_stride_L` (`rfl`, as at the source). -/
theorem regimeShrinkX_stride_omega_L (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a)
    (hcop : (a : ℚ) ≤ R.eps ^ 2 * ((R.a * R.Hlo / a : ℕ) : ℚ) / 2)
    (hHlo : a ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride_L R a ha heps500 hs hdiv hlo4 hloM hcop hHlo).ω = R.ω := by
  rfl

/-- The `a` projection of `regimeShrinkX_stride_L` (`rfl`, as at the source). -/
theorem regimeShrinkX_stride_a_L (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a)
    (hcop : (a : ℚ) ≤ R.eps ^ 2 * ((R.a * R.Hlo / a : ℕ) : ℚ) / 2)
    (hHlo : a ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride_L R a ha heps500 hs hdiv hlo4 hloM hcop hHlo).a = a := by
  rfl

/-- The `eps` projection of `regimeShrinkX_stride_L` (`rfl`, as at the source). -/
theorem regimeShrinkX_stride_eps_L (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a)
    (hcop : (a : ℚ) ≤ R.eps ^ 2 * ((R.a * R.Hlo / a : ℕ) : ℚ) / 2)
    (hHlo : a ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride_L R a ha heps500 hs hdiv hlo4 hloM hcop hHlo).eps = R.eps := by
  rfl

/-- The `Hlo` projection of `regimeShrinkX_stride_L` (`rfl`, as at the source). -/
theorem regimeShrinkX_stride_Hlo_L (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a)
    (hcop : (a : ℚ) ≤ R.eps ^ 2 * ((R.a * R.Hlo / a : ℕ) : ℚ) / 2)
    (hHlo : a ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride_L R a ha heps500 hs hdiv hlo4 hloM hcop hHlo).Hlo = R.a * R.Hlo / a := by
  rfl

/-- The `Hhi` projection of `regimeShrinkX_stride_L` (`rfl`, as at the source). -/
theorem regimeShrinkX_stride_Hhi_L (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a)
    (hcop : (a : ℚ) ≤ R.eps ^ 2 * ((R.a * R.Hlo / a : ℕ) : ℚ) / 2)
    (hHlo : a ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride_L R a ha heps500 hs hdiv hlo4 hloM hcop hHlo).Hhi = R.Hhi := by
  rfl

/-- The `C0` projection of `regimeShrinkX_stride_L` (`rfl`, as at the source). -/
theorem regimeShrinkX_stride_C0_L (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a)
    (hcop : (a : ℚ) ≤ R.eps ^ 2 * ((R.a * R.Hlo / a : ℕ) : ℚ) / 2)
    (hHlo : a ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride_L R a ha heps500 hs hdiv hlo4 hloM hcop hHlo).C0 = R.C0 := by
  rfl

/-- The `J` projection of `regimeShrinkX_stride_L` (`rfl`, as at the source). -/
theorem regimeShrinkX_stride_J_L (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a)
    (hcop : (a : ℚ) ≤ R.eps ^ 2 * ((R.a * R.Hlo / a : ℕ) : ℚ) / 2)
    (hHlo : a ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride_L R a ha heps500 hs hdiv hlo4 hloM hcop hHlo).J = R.J := by
  rfl

/-- **⟦F3-P6 AT THE CHARGE⟧** — `regimeShrinkX_stride_x_mul_b9` (`StridePair.lean:1061`) at the
lift, read through `regimeShrinkX_stride_x_L`. -/
theorem regimeShrinkX_stride_x_mul_L (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a)
    (hcop : (a : ℚ) ≤ R.eps ^ 2 * ((R.a * R.Hlo / a : ℕ) : ℚ) / 2)
    (hHlo : a ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride_L R a ha heps500 hs hdiv hlo4 hloM hcop hHlo).x * a = R.x := by
  rw [regimeShrinkX_stride_x_L R a ha heps500 hs hdiv hlo4 hloM hcop hHlo]
  exact Nat.div_mul_cancel hs.1

/-- **⟦F3-P16 AT THE CHARGE⟧** (`mrtUniformityXiL2AffW_of_set_L`) —
`mrtUniformityXiL2AffW_of_set_b9` (`StridePair.lean:1079`), which reads its stride cap ONLY inside
the regime terms (its `omega` for `hω2` does not spend it): the binder list is the def's
(`hcop hHlo` where the source has `ha8103`), `regimeShrinkX_stride_b9 ↦ regimeShrinkX_stride_L` in
`hb` and in the conclusion's regime.  BODY: the source's, verbatim. -/
theorem mrtUniformityXiL2AffW_of_set_L (h : ℕ) (Rd : ChowlaRegime) (a b : ℕ) (ha : 1 ≤ a)
    (heps500 : Rd.eps ≤ 1 / 500) (hs : StrideScale a Rd)
    (hdiv : a ∣ Rd.a * Rd.Hlo) (hlo4 : 4 * ⌈(1 / Rd.eps : ℚ)⌉₊ ^ 4 ≤ Rd.a * Rd.Hlo / a)
    (hloM : 4000000 ≤ Rd.a * Rd.Hlo / a)
    (hcop : (a : ℚ) ≤ Rd.eps ^ 2 * ((Rd.a * Rd.Hlo / a : ℕ) : ℚ) / 2)
    (hHlo : a ≤ Rd.a * Rd.Hlo / a)
    (hb : b ≤ (regimeShrinkX_stride_L Rd a ha heps500 hs hdiv hlo4 hloM hcop hHlo).Hlo)
    (hω : 8 ≤ Rd.ω) (K ρ : ℝ)
    (hK : ∀ H : ℕ, ∀ [NeZero H], Rd.Hlo ≤ H → H ≤ Rd.Hhi →
      ((bigXiAffD a b h Rd.eps H).card : ℝ) ≤ K)
    (hdoor : MRTUniformityXiL2Set (fun eps H _ => bigXiAffD a b h eps H) Rd ρ) :
    MRTUniformityXiL2AffW h
      (ChowlaRegimeAff.ofRegime (regimeShrinkX_stride_L Rd a ha heps500 hs hdiv hlo4 hloM hcop hHlo)
        b hb)
      ((a : ℝ) * ((∑ n ∈ Finset.Ioc (Rd.x / Rd.ω) Rd.x, (n : ℝ)⁻¹)
            / (∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹)) * ρ
        + K * (a : ℝ) / (((a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1)
            * ∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹)) := by
  have hapos : 0 < a := ha
  have hx2 : 2 ≤ Rd.x / a := hs.2.1
  have hωx2 : Rd.ω ≤ Rd.x / a := hs.2.2.1
  have hω2 : 2 ≤ Rd.ω := by omega
  have hxa : a * (Rd.x / a) = Rd.x := Nat.mul_div_cancel' hs.1
  have hlogω : (2 : ℝ) ≤ Real.log (Rd.ω : ℝ) := by
    have h8 : (8 : ℝ) ≤ (Rd.ω : ℝ) := by exact_mod_cast hω
    have hexp2 : Real.exp 2 ≤ 8 := by
      have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    have hωpos : (0 : ℝ) < (Rd.ω : ℝ) := by linarith
    rw [Real.le_log_iff_exp_le hωpos]
    linarith
  have hZP : (0 : ℝ) < ∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹ := by
    have hb2 := (harmonic_window_bounds hx2 hω2 hωx2).1
    linarith
  have hZQnn : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioc (Rd.x / Rd.ω) Rd.x, (n : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun n _ => by positivity)
  have hD : (0 : ℝ) < (a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1 := by positivity
  have halg2 : ∀ Hs Ic Ip Av R2 D Zpv : ℝ, 0 < Hs →
      Ic ≤ Av * R2 * Ip + Av * Hs / (D * Zpv) →
      (1 / Hs) * Ic ≤ Av * R2 * ((1 / Hs) * Ip) + Av / (D * Zpv) := by
    intro Hs Ic Ip Av R2 D Zpv hHs hle
    have h1 : (0 : ℝ) < 1 / Hs := by positivity
    calc (1 / Hs) * Ic ≤ (1 / Hs) * (Av * R2 * Ip + Av * Hs / (D * Zpv)) :=
          mul_le_mul_of_nonneg_left hle (le_of_lt h1)
      _ = Av * R2 * ((1 / Hs) * Ip) + Av / (D * Zpv) := by
          field_simp
  intro H hNZ hdvd0 hlo0 hhi0
  haveI : NeZero H := hNZ
  have hdvd : a ∣ H := hdvd0
  have hhi : H ≤ Rd.Hhi := hhi0
  have hlo1 : a * (Rd.a * Rd.Hlo / a) ≤ H := hlo0
  rw [Nat.mul_div_cancel' hdiv] at hlo1
  have hlo' : Rd.Hlo ≤ H := le_trans (Nat.le_mul_of_pos_left _ Rd.ha) hlo1
  have hHR : (0 : ℝ) < (H : ℝ) := by
    have hHp : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
    exact_mod_cast hHp
  have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
  have hterm : ∀ ξ : ZMod H, (1 / (H : ℝ) ^ 2)
      * ∫ m, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasureAff a (Rd.x / a) Rd.ω)
      ≤ (a : ℝ) * ((∑ n ∈ Finset.Ioc (Rd.x / Rd.ω) Rd.x, (n : ℝ)⁻¹)
            / (∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹))
          * ((1 / (H : ℝ) ^ 2) * ∫ m, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure Rd.x Rd.ω))
        + (a : ℝ) / (((a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1)
            * ∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹) := by
    intro ξ
    have hf0 : ∀ m : ℕ, (0 : ℝ) ≤ ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 :=
      fun m => sq_nonneg _
    have hfM : ∀ m : ℕ, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ≤ (H : ℝ) ^ 2 := by
      intro m
      have hnb := norm_windowExpSum_trivial H m (-(ξ.val : ℝ) / (H : ℝ))
      nlinarith [norm_nonneg (windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ)))]
    have h15 := integral_logMeasureAff_le_plain a (Rd.x / a) Rd.ω hapos hx2 hω hωx2
      (fun m => ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2) ((H : ℝ) ^ 2) hf0 hfM
    rw [hxa] at h15
    exact halg2 _ _ _ _ _ _ _ hH2 h15
  have hdoor' : ∑ ξ ∈ bigXiAff a b h Rd.eps H, (1 / (H : ℝ) ^ 2)
      * ∫ m, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
        ∂(logMeasure Rd.x Rd.ω) ≤ ρ := by
    have hd : ∑ ξ ∈ bigXiAffD a b h Rd.eps H, (1 / (H : ℝ) ^ 2)
        * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure Rd.x Rd.ω) ≤ ρ := hdoor H hlo' hhi
    rwa [bigXiAffD_of_dvd hdvd] at hd
  have hK' : ((bigXiAff a b h Rd.eps H).card : ℝ) ≤ K := by
    have hk := hK H hlo' hhi
    rwa [bigXiAffD_of_dvd hdvd] at hk
  have hc1 : (0 : ℝ) ≤ (a : ℝ) * ((∑ n ∈ Finset.Ioc (Rd.x / Rd.ω) Rd.x, (n : ℝ)⁻¹)
      / (∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹)) :=
    mul_nonneg (Nat.cast_nonneg a) (div_nonneg hZQnn (le_of_lt hZP))
  have hc2 : (0 : ℝ) ≤ (a : ℝ) / (((a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1)
      * ∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹) :=
    div_nonneg (Nat.cast_nonneg a) (le_of_lt (mul_pos hD hZP))
  have hmain : ∑ ξ ∈ bigXiAff a b h Rd.eps H, (1 / (H : ℝ) ^ 2)
      * ∫ m, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasureAff a (Rd.x / a) Rd.ω)
      ≤ (a : ℝ) * ((∑ n ∈ Finset.Ioc (Rd.x / Rd.ω) Rd.x, (n : ℝ)⁻¹)
            / (∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹)) * ρ
        + K * (a : ℝ) / (((a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1)
            * ∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹) := by
    calc ∑ ξ ∈ bigXiAff a b h Rd.eps H, (1 / (H : ℝ) ^ 2)
          * ∫ m, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasureAff a (Rd.x / a) Rd.ω)
        ≤ ∑ _ξ ∈ bigXiAff a b h Rd.eps H,
            ((a : ℝ) * ((∑ n ∈ Finset.Ioc (Rd.x / Rd.ω) Rd.x, (n : ℝ)⁻¹)
                / (∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹))
              * ((1 / (H : ℝ) ^ 2) * ∫ m, ‖windowExpSum H m (-(_ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                  ∂(logMeasure Rd.x Rd.ω))
            + (a : ℝ) / (((a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1)
                * ∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹)) :=
          Finset.sum_le_sum (fun ξ _ => hterm ξ)
      _ = (a : ℝ) * ((∑ n ∈ Finset.Ioc (Rd.x / Rd.ω) Rd.x, (n : ℝ)⁻¹)
              / (∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹))
            * (∑ ξ ∈ bigXiAff a b h Rd.eps H, (1 / (H : ℝ) ^ 2)
                * ∫ m, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure Rd.x Rd.ω))
          + ((bigXiAff a b h Rd.eps H).card : ℝ)
              * ((a : ℝ) / (((a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1)
                * ∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (a : ℝ) * ((∑ n ∈ Finset.Ioc (Rd.x / Rd.ω) Rd.x, (n : ℝ)⁻¹)
              / (∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹)) * ρ
          + K * ((a : ℝ) / (((a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1)
                * ∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹)) :=
          add_le_add (mul_le_mul_of_nonneg_left hdoor' hc1)
            (mul_le_mul_of_nonneg_right hK' hc2)
      _ = _ := by ring
  exact hmain

/-! ## §P — THE CHARGE LEMMA AND THE E-BEATING LEMMA (the freeze's cells 10–11; this half's
cells 22–23) -/

/-- **⟦THE CHARGE EXISTS, AT THE AFFINE TARGET GRADE⟧** (`zCharge_exists`) — `crownWd_exists_charge`
(`FlatDoorAllGrades.lean:60`) with the grade target `ρ ↦ ρt := ρ/(2.04·a)`: one `c ≥ 1` that pins
both `ε` (`1/(500·c) ≤ ε`) and the target grade (`1/(838400·c) ≤ ρ/(2.04·a)`), the larger of the
two ceilings.  The source's three bullets, verbatim, with `838400·ρ ↦ 838400·(ρ/(2.04·a))` in the
third. -/
theorem zCharge_exists (a : ℕ) (ha : 0 < a) (ε : ℚ) (hε0 : 0 < ε) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ c : ℕ, 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧
      (1 : ℝ) / (838400 * (c : ℝ)) ≤ ρ / (2.04 * (a : ℝ)) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hεQ0 : (0 : ℚ) < 500 * ε := by linarith
  have hρ0 : (0 : ℝ) < 838400 * (ρ / (2.04 * (a : ℝ))) := by positivity
  have hn1pos : 0 < ⌈(1 / (500 * ε) : ℚ)⌉₊ := Nat.ceil_pos.mpr (div_pos one_pos hεQ0)
  refine ⟨max ⌈(1 / (500 * ε) : ℚ)⌉₊ ⌈(1 / (838400 * (ρ / (2.04 * (a : ℝ)))) : ℝ)⌉₊, ?_, ?_, ?_⟩
  · exact le_trans (Nat.succ_le_of_lt hn1pos) (le_max_left _ _)
  · have hle : (1 : ℚ) / (500 * ε)
        ≤ ((max ⌈(1 / (500 * ε) : ℚ)⌉₊ ⌈(1 / (838400 * (ρ / (2.04 * (a : ℝ)))) : ℝ)⌉₊ : ℕ)
          : ℚ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_left _ _)
    have hc1 : (1 : ℚ)
        ≤ ((max ⌈(1 / (500 * ε) : ℚ)⌉₊ ⌈(1 / (838400 * (ρ / (2.04 * (a : ℝ)))) : ℝ)⌉₊ : ℕ)
          : ℚ) := by
      exact_mod_cast le_trans (Nat.succ_le_of_lt hn1pos) (le_max_left _ _)
    rw [div_le_iff₀ hεQ0] at hle
    rw [div_le_iff₀ (by linarith)]
    linarith
  · have hle : (1 : ℝ) / (838400 * (ρ / (2.04 * (a : ℝ))))
        ≤ ((max ⌈(1 / (500 * ε) : ℚ)⌉₊ ⌈(1 / (838400 * (ρ / (2.04 * (a : ℝ)))) : ℝ)⌉₊ : ℕ)
          : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right _ _)
    have hc1 : (1 : ℝ)
        ≤ ((max ⌈(1 / (500 * ε) : ℚ)⌉₊ ⌈(1 / (838400 * (ρ / (2.04 * (a : ℝ)))) : ℝ)⌉₊ : ℕ)
          : ℝ) := by
      exact_mod_cast le_trans (Nat.succ_le_of_lt hn1pos) (le_max_left _ _)
    rw [div_le_iff₀ hρ0] at hle
    rw [div_le_iff₀ (by linarith)]
    linarith

/-- **⟦THE ENDPOINT IS BEATEN BY THE FLOOR⟧** (`zE_beaten`) — the freeze's cell 11 (Z-F9).
In G12b's crown the endpoint `E := Kc·a/((a·Q + 1)·(log ω − 1))`, `Q := x/a/ω`, is EXPORTED as a
slack binder; `StrideDoorAllGradesW` has none, so `E ≤ ρ/2` is paid by the design floor.  DERIVED,
with `W := 2^283·c^20·k` kept under a name: `log Hhi ≥ 1` (`Hhi ≥ 4·10⁶ ≥ e`); `hQ` gives
`Q ≥ 8·Hhi`; `(a·Q + 1)·(log ω − 1) ≥ a·(8·Hhi)·32000 = 256000·a·Hhi`; so `E ≤ W/(256000·Hhi)`,
and `E ≤ ρ/2 ⇐ W ≤ 128000·ρ·Hhi`; and `Hhi ≥ flatDesignBase A ≥ exp (exp (3.2·A))` with
`3.2·A ≥ log (max 1 (log (max 1 (W/(128000·ρ)))))` gives `exp (exp (3.2·A)) ≥ W/(128000·ρ)`
(`Real.exp_log` at `0 < max 1 _`, `le_max_right`).  CONTROL: at `A = 162`, `c = k = 1`, `ρ = 1`,
the room is `2^283/(128000·e^{e^{518.4}})` against `1`.  `0 < Kc` and `162 ≤ A` are the brief's
binders, read by nothing here (`_hKc0`, `_hA162`). -/
theorem zE_beaten {Kc : ℝ} {c k a : ℕ} {ρ A : ℝ} {Rd : ChowlaRegime}
    (_hKc0 : 0 < Kc) (hKcb : Kc ≤ 2 ^ 283 * (c : ℝ) ^ 20 * (k : ℝ)) (hc1 : 1 ≤ c) (hk : 1 ≤ k)
    (ha : 1 ≤ a) (hρ : 0 < ρ) (_hA162 : 162 ≤ A)
    (hAE : Real.log (max 1 (Real.log (max 1
      (2 ^ 283 * (c : ℝ) ^ 20 * (k : ℝ) / (128000 * ρ))))) / 3.2 ≤ A)
    (hHhi : ((flatDesignBase A : ℕ) : ℝ) ≤ ((Rd.Hhi : ℕ) : ℝ))
    (hQ : 8 * (Rd.Hhi : ℝ) * Real.log Rd.Hhi * Real.log Rd.Hhi ≤ ((Rd.x / a / Rd.ω : ℕ) : ℝ))
    (hlogω : (32001 : ℝ) ≤ Real.log ((Rd.ω : ℕ) : ℝ)) (hH4 : 4000000 ≤ Rd.Hhi) :
    Kc * (a : ℝ) / (((a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1) * (Real.log ((Rd.ω : ℕ) : ℝ) - 1))
      ≤ ρ / 2 := by
  set W : ℝ := 2 ^ 283 * (c : ℝ) ^ 20 * (k : ℝ) with hWdef
  set Q : ℝ := ((Rd.x / a / Rd.ω : ℕ) : ℝ) with hQdef
  set Hh : ℝ := ((Rd.Hhi : ℕ) : ℝ) with hHhdef
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hW0 : 0 < W := by rw [hWdef]; positivity
  have hHh4 : (4000000 : ℝ) ≤ Hh := by rw [hHhdef]; exact_mod_cast hH4
  have hHh0 : (0 : ℝ) < Hh := by linarith
  -- ⟦`log Hhi ≥ 1`⟧ `e < 2.7182818286 ≤ 4·10⁶ ≤ Hhi`
  have hlogH1 : (1 : ℝ) ≤ Real.log Hh := by
    rw [Real.le_log_iff_exp_le hHh0]
    have := Real.exp_one_lt_d9
    linarith
  -- ⟦`Q ≥ 8·Hhi`⟧ off `hQ` at `log Hhi ≥ 1`
  have hQ8 : 8 * Hh ≤ Q := by
    have h1 : 8 * Hh ≤ 8 * Hh * Real.log Hh := by nlinarith
    have h2 : 8 * Hh * Real.log Hh ≤ 8 * Hh * Real.log Hh * Real.log Hh := by nlinarith
    linarith
  -- ⟦THE DENOMINATOR⟧ `(a·Q + 1)·(log ω − 1) ≥ 256000·a·Hhi`
  have hLω : (32000 : ℝ) ≤ Real.log ((Rd.ω : ℕ) : ℝ) - 1 := by linarith
  have haQ : 8 * (a : ℝ) * Hh ≤ (a : ℝ) * Q + 1 := by nlinarith
  have hden : 256000 * (a : ℝ) * Hh
      ≤ ((a : ℝ) * Q + 1) * (Real.log ((Rd.ω : ℕ) : ℝ) - 1) := by
    have h8 : (0 : ℝ) ≤ 8 * (a : ℝ) * Hh := by positivity
    have := mul_le_mul haQ hLω (by norm_num) (by linarith)
    linarith
  have hden0 : (0 : ℝ) < 256000 * (a : ℝ) * Hh := by positivity
  -- ⟦THE FLOOR⟧ `W/(128000·ρ) ≤ exp (exp (3.2·A)) ≤ flatDesignBase A ≤ Hhi`
  have hDge : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    rw [flatDesignBase]; exact Nat.le_ceil _
  have hAE' : Real.log (max 1 (Real.log (max 1 (W / (128000 * ρ))))) ≤ 3.2 * A := by
    rw [div_le_iff₀ (by norm_num)] at hAE; linarith
  have hY1 : max 1 (Real.log (max 1 (W / (128000 * ρ)))) ≤ Real.exp (3.2 * A) := by
    have h := Real.exp_le_exp.mpr hAE'
    rwa [Real.exp_log (lt_of_lt_of_le one_pos (le_max_left _ _))] at h
  have hY2 : Real.log (max 1 (W / (128000 * ρ))) ≤ Real.exp (3.2 * A) :=
    le_trans (le_max_right _ _) hY1
  have hY3 : max 1 (W / (128000 * ρ)) ≤ Real.exp (Real.exp (3.2 * A)) := by
    have h := Real.exp_le_exp.mpr hY2
    rwa [Real.exp_log (lt_of_lt_of_le one_pos (le_max_left _ _))] at h
  have hYH : W / (128000 * ρ) ≤ Hh :=
    le_trans (le_max_right _ _) (le_trans hY3 (le_trans hDge hHhi))
  have hWH : W ≤ 128000 * ρ * Hh := by
    rw [div_le_iff₀ (by positivity)] at hYH; linarith
  -- ⟦THE CLOSE⟧ `Kc·a ≤ a·W ≤ 128000·ρ·a·Hhi ≤ (ρ/2)·den`
  have hdenpos : (0 : ℝ) < ((a : ℝ) * Q + 1) * (Real.log ((Rd.ω : ℕ) : ℝ) - 1) :=
    lt_of_lt_of_le hden0 hden
  rw [div_le_iff₀ hdenpos]
  have hKa : Kc * (a : ℝ) ≤ W * (a : ℝ) := mul_le_mul_of_nonneg_right hKcb (by linarith)
  have hWa : W * (a : ℝ) ≤ 128000 * ρ * Hh * (a : ℝ) :=
    mul_le_mul_of_nonneg_right hWH (by linarith)
  have hρd : ρ / 2 * (256000 * (a : ℝ) * Hh)
      ≤ ρ / 2 * (((a : ℝ) * Q + 1) * (Real.log ((Rd.ω : ℕ) : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left hden (by linarith)
  have heq : ρ / 2 * (256000 * (a : ℝ) * Hh) = 128000 * ρ * Hh * (a : ℝ) := by ring
  linarith

/-! ## §Q — THE CHAIN, THE COUNT FLOOR AND THE TERMINAL (the freeze's rows C, K, W; this half's
cell 24) -/

/-- **⟦THE CHAIN AT THE CHARGE⟧** (`flat_chain_generic_h_Z`) — G12b's `flat_chain_generic_h_g12b`
(`StridePairReceiptG12b.lean:1045`) on the Z forms: the five hops head→roadExit→capstone→conditional
→kswin→v7 composed at the landed binder orders (§F, §H, §J, §N, §K), every `_g12b ↦ _Z`, and the
cap `hh9` GONE (no hop reads it).  No numeral. -/
theorem flat_chain_generic_h_Z (h : ℕ) (hh : 0 < h) (ε : ℚ) (c : ℕ) (L : ℝ) (Xi : XiFamily)
    (harcXi : ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
      ∀ ξ ∈ Xi eps H, NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (P : ChowlaRegime → Prop) (hhead : FlatHeadFormHG_Z h ε c L Xi P) (A₀ : ℝ) :
    V7RatedFormHG_Z h ε c L P A₀ :=
  flat_v7_generic_h_Z h hh ε c L P
    (fun Awin hband => flat_kswin_generic_h_Z h hh ε c L Awin hband P
      (flat_conditional_generic_h_Z h hh ε c L Awin hband P
        (flat_capstone_generic_h_Z h hh ε c L Awin hband P
          (flat_roadExit_generic_h_Z h hh ε c L Xi harcXi P hhead)))) A₀

/-- **⟦THE COUNT FLOOR AT THE AFFINE FAMILY, CAP-FREE⟧** (`zCount_affine`) — the head's `hcount`
(`flat_door_head_xceil_h_Z`, §E) at the grid-restricted affine family and the multiplier `a·h`:
the cap-free leaf `bigXi_bounded_ceiling_eps` (`FlatDoorEpsRung2.lean:2235`, `C ≤ 2^283·c^20`)
through `bigXiAffD_card_le` (`StridePair.lean:320`) and `bigXiAff_card_le_mul`
(`StrideFork.lean:379`) with the constant `(a·h)·C ≤ 2^283·c^20·(a·h)`.  G12b's
`mrtUniformityXiL2AffSet_holds_flat_floor_g12b` `hcount` block (`:1127–1133`) with its capped pin
leaf replaced by the cap-free one (the freeze's row K). -/
theorem zCount_affine (a b h : ℕ) (ha : 0 < a) (hh : 0 < h) (ε : ℚ) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 500) {c : ℕ} (hc1 : 1 ≤ c) (hcε : (1 : ℚ) / (500 * (c : ℚ)) ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 283 * (c : ℝ) ^ 20 * ((a * h : ℕ) : ℝ) ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧
      ∀ (H : ℕ) [NeZero H], H₀ ≤ H → ((bigXiAffD a b h ε H).card : ℝ) ≤ C := by
  obtain ⟨C, hC0, hCb, H₀, hH₀, hcard⟩ := bigXi_bounded_ceiling_eps ε hε0 hε hc1 hcε
  have hkpos : 0 < a * h := Nat.mul_pos ha hh
  have hkR : (0 : ℝ) < ((a * h : ℕ) : ℝ) := by exact_mod_cast hkpos
  refine ⟨((a * h : ℕ) : ℝ) * C, mul_pos hkR hC0, ?_, H₀, hH₀, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left hCb hkR.le
    calc ((a * h : ℕ) : ℝ) * C ≤ ((a * h : ℕ) : ℝ) * (2 ^ 283 * (c : ℝ) ^ 20) := h1
      _ = 2 ^ 283 * (c : ℝ) ^ 20 * ((a * h : ℕ) : ℝ) := mul_comm _ _
  · intro H _ hH
    have hN : (bigXiAffD a b h ε H).card ≤ a * h * (bigXi ε H).card :=
      le_trans (bigXiAffD_card_le a b h ε H) (bigXiAff_card_le_mul a b h hh ε H)
    have hNR : ((bigXiAffD a b h ε H).card : ℝ) ≤ ((a * h : ℕ) : ℝ) * ((bigXi ε H).card : ℝ) := by
      exact_mod_cast hN
    exact le_trans hNR (mul_le_mul_of_nonneg_left (hcard H hH) hkR.le)

/-- **⟦ARM Z — THE AFFINE DOOR AT EVERY STRIDE, TWIST AND GRADE, PROVED⟧**
(`strideDoorAllGradesW_holds`) — G12b's crown `mrtUniformityXiL2AffW_holds_flat_stride_g12b`
(`StridePairReceiptG12b.lean:1140–1283`) transcribed at the charge.  The route: the MULTIPLIER
`k := a·h` and the charge `L := log k`; the charge `c` from `zCharge_exists` pins `ε` and the
TARGET grade `ρt := ρ/(2.04·a)`; the head at the trivial payload at `h := k` with the cap-free
count floor `zCount_affine`, shrunk to `ρt`; the chain `flat_chain_generic_h_Z` at the affine
arc supply; the body fired at `U1floor := a·flatDesignBase A`, stride `a`, `g := 0`; the shrink
`regimeShrinkX_stride_L` with its two former cap sites (`hcop`, `hHlo`) paid from
`flatDesignBase_clears_stride_floors_L`'s third floor `500000·k³ ≤ flatDesignBase A` and the pin
`1/(500·k) ≤ ε` (`ε²·Hlo'/2 ≥ (1/(500k))²·500000·k³/2 = k ≥ a`); the transport
`mrtUniformityXiL2AffW_of_set_L`; and the grade `a·Zr·ρt + E ≤ a·1.02·ρt + ρ/2 = ρ/2 + ρ/2 = ρ`,
the endpoint `E` beaten by the floor (`zE_beaten`).
⚠ THE TERMINAL RAISES `A₀` BY THE CHARGE: the chain is fired at
`A₀' := max (max A₀ A_E) (162 + 2·(log c + L))`, where `A_E` is the E-beating floor
`log (max 1 (log (max 1 (2^283·c^20·k/(128000·ρ)))))/3.2` and `162 + 2·Lc` pays the lifts'
`L ≤ A` (the form `V7RatedFormHG_Z` does not export `10 + 2·Lc ≤ A`).  The statement's
`A₀ ≤ A` is `A₀ ≤ A₀' ≤ A`.  Nothing here bears on twin primes; the shape is `∀ A₀ ∃ Ra`, not the
crown's `∃ H₀ ∀ R`. -/
theorem strideDoorAllGradesW_holds : StrideDoorAllGradesW := by
  intro a b h ha hba hh ε hεk hε500 ρ hρ A₀
  -- ⟦THE MULTIPLIER⟧ `k := a·h`; the charge `L := log k`; `0 < ε` off the pin
  have hapos : 0 < a := ha
  have hkpos : 0 < a * h := Nat.mul_pos ha hh
  have hkQ : (0 : ℚ) < ((a * h : ℕ) : ℚ) := by exact_mod_cast hkpos
  have hε0 : (0 : ℚ) < ε := lt_of_lt_of_le (div_pos one_pos (mul_pos (by norm_num) hkQ)) hεk
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
  have haah : a ≤ a * h := Nat.le_mul_of_pos_right a hh
  obtain ⟨c, hc1, hcε, hpin⟩ := zCharge_exists a ha ε hε0 ρ hρ
  have hkR1 : (1 : ℝ) ≤ ((a * h : ℕ) : ℝ) := by exact_mod_cast hkpos
  set L : ℝ := Real.log ((a * h : ℕ) : ℝ) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hkR1
  have haL : Real.log (a : ℝ) ≤ L := Real.log_le_log haR (by exact_mod_cast haah)
  set ρt : ℝ := ρ / (2.04 * (a : ℝ)) with hρtdef
  have hρt : 0 < ρt := div_pos hρ (mul_pos (by norm_num) haR)
  have hlogc : 0 ≤ Real.log (c : ℝ) := Real.log_natCast_nonneg c
  -- ⟦THE DESIGN FLOOR FOR E⟧ (cell 23) and the raise of `A₀` by the charge
  obtain ⟨AE, hAEdef⟩ : ∃ x : ℝ, x = Real.log (max 1 (Real.log (max 1
      (2 ^ 283 * (c : ℝ) ^ 20 * ((a * h : ℕ) : ℝ) / (128000 * ρ))))) / 3.2 := ⟨_, rfl⟩
  obtain ⟨A₀', hA₀'def⟩ : ∃ x : ℝ,
      x = max (max A₀ AE) (162 + 2 * (Real.log (c : ℝ) + L)) := ⟨_, rfl⟩
  -- ⟦THE HEAD AT THE TRIVIAL PAYLOAD, AT `h := k`⟧ (§E), with the count floor (row K)
  have hhead := flat_door_head_xceil_h_Z (a * h) hkpos ε hε0 hε500 hεk hc1 hcε hL0 le_rfl
    (fun eps H _ => bigXiAffD a b h eps H) (zCount_affine a b h ha hh ε hε0 hε500 hc1 hcε)
  -- ⟦THE SHRINK AT `ρt`⟧ (§E)
  have hhead' := flatHeadFormHG_Z_at_grade hhead hρt hpin
  -- ⟦THE CHAIN⟧ at the affine arc supply
  have hV := flat_chain_generic_h_Z (a * h) hkpos ε c L _ (fun eps heps =>
    nearRatTight_of_bigXiAffD bigXiArcTight_twelve heps ha hh) _ hhead' A₀'
  obtain ⟨Cg, Kc0, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, hA162, hA₀'A, hbody⟩ := hV
  have hA₀'A' : max (max A₀ AE) (162 + 2 * (Real.log (c : ℝ) + L)) ≤ A := by
    rw [← hA₀'def]; exact hA₀'A
  have hA₀A : A₀ ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA₀'A'
  have hAEA : AE ≤ A := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA₀'A'
  have hLA : L ≤ A := by
    have h1 := le_trans (le_max_right _ _) hA₀'A'
    linarith
  -- ⟦FIRE THE BODY⟧ at `U1floor := a · flatDesignBase A`, stride `a`, `g := 0`
  have hU : flatDesignBase A ≤ a * flatDesignBase A := Nat.le_mul_of_pos_left _ hapos
  have hUceil := loglog_mul_flatDesignBase_le_L hA162 ha haL hLA
  obtain ⟨Rd, hReps, hHlo, -, hstride, -, -, -, hP⟩ :=
    hbody (a * flatDesignBase A) a (fun _ _ => 0) hU hUceil ha haL
      (xceilRiderStrictAt_zero (50 + (Real.log (c : ℝ) + L)) ε)
  obtain ⟨⟨Kc, hKc0, hKcb, hKcount⟩, hdoor⟩ := hP
  -- ⟦THE ε PINS⟧ `Rd.eps ≤ 1/500` and the multiplier pin, at `Rd.eps`
  have heps500 : Rd.eps ≤ 1 / 500 := by rw [hReps]; exact hε500
  have hεk' : (1 : ℚ) / (500 * ((a * h : ℕ) : ℚ)) ≤ Rd.eps := by rw [hReps]; exact hεk
  -- ⟦THE SHRINK'S FLOORS⟧ off `flatDesignBase_clears_stride_floors_L`
  have hdiv : a ∣ Rd.a * Rd.Hlo := by
    rw [hHlo]
    exact (dvd_mul_right a (flatDesignBase A)).mul_left Rd.a
  have hquot : Rd.a * Rd.Hlo / a = Rd.a * flatDesignBase A := by
    rw [hHlo, show Rd.a * (a * flatDesignBase A) = a * (Rd.a * flatDesignBase A) by ring]
    exact Nat.mul_div_cancel_left _ hapos
  have hBle : flatDesignBase A ≤ Rd.a * Rd.Hlo / a := by
    rw [hquot]
    exact Nat.le_mul_of_pos_left _ Rd.ha
  obtain ⟨hf1, hf2, hf3⟩ := flatDesignBase_clears_stride_floors_L hA162 hkpos le_rfl hLA hεk'
  have hlo4 : 4 * ⌈(1 / Rd.eps : ℚ)⌉₊ ^ 4 ≤ Rd.a * Rd.Hlo / a := le_trans hf1 hBle
  have hloM : 4000000 ≤ Rd.a * Rd.Hlo / a := le_trans hf2 hBle
  -- ⟦THE FORMER CAP SITE `hcop`⟧ `ε²·Hlo'/2 ≥ (1/(500k))²·500000·k³/2 = k ≥ a`
  have hcop : (a : ℚ) ≤ Rd.eps ^ 2 * ((Rd.a * Rd.Hlo / a : ℕ) : ℚ) / 2 := by
    have hk500 : (0 : ℚ) < 500 * ((a * h : ℕ) : ℚ) := by linarith
    have hpin1 : (1 : ℚ) ≤ 500 * ((a * h : ℕ) : ℚ) * Rd.eps := by
      have h1 := (div_le_iff₀ hk500).mp hεk'
      linarith
    have hsq : (1 : ℚ) ≤ 250000 * ((a * h : ℕ) : ℚ) ^ 2 * Rd.eps ^ 2 := by
      have h1 := one_le_pow₀ (n := 2) hpin1
      calc (1 : ℚ) ≤ (500 * ((a * h : ℕ) : ℚ) * Rd.eps) ^ 2 := h1
        _ = 250000 * ((a * h : ℕ) : ℚ) ^ 2 * Rd.eps ^ 2 := by ring
    have hf3Q : (500000 : ℚ) * ((a * h : ℕ) : ℚ) ^ 3 ≤ ((Rd.a * Rd.Hlo / a : ℕ) : ℚ) := by
      have h1 := le_trans hf3 hBle
      exact_mod_cast h1
    have hakQ : (a : ℚ) ≤ ((a * h : ℕ) : ℚ) := by exact_mod_cast haah
    have hstep : Rd.eps ^ 2 * (500000 * ((a * h : ℕ) : ℚ) ^ 3)
        ≤ Rd.eps ^ 2 * ((Rd.a * Rd.Hlo / a : ℕ) : ℚ) :=
      mul_le_mul_of_nonneg_left hf3Q (sq_nonneg _)
    have heq : Rd.eps ^ 2 * (500000 * ((a * h : ℕ) : ℚ) ^ 3)
        = 2 * ((a * h : ℕ) : ℚ) * (250000 * ((a * h : ℕ) : ℚ) ^ 2 * Rd.eps ^ 2) := by ring
    have h2k : 2 * ((a * h : ℕ) : ℚ)
        ≤ 2 * ((a * h : ℕ) : ℚ) * (250000 * ((a * h : ℕ) : ℚ) ^ 2 * Rd.eps ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℚ) ≤ 2 * ((a * h : ℕ) : ℚ))
      linarith
    linarith
  -- ⟦THE FORMER CAP SITE `hHlo`⟧ `a ≤ k ≤ k³ ≤ 500000·k³ ≤ flatDesignBase A ≤ Hlo'`
  have hHloS : a ≤ Rd.a * Rd.Hlo / a := by
    have h2 : a * h ≤ (a * h) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h3 : (a * h) ^ 3 ≤ 500000 * (a * h) ^ 3 := Nat.le_mul_of_pos_left _ (by norm_num)
    exact le_trans haah (le_trans h2 (le_trans h3 (le_trans hf3 hBle)))
  have hb : b ≤ (regimeShrinkX_stride_L Rd a ha heps500 hstride hdiv hlo4 hloM hcop hHloS).Hlo := by
    rw [regimeShrinkX_stride_Hlo_L]
    exact le_trans hba.le hHloS
  -- ⟦THE WIDTH NUMERAL⟧ `log ω ≥ 32001` off `hωbig` at `ε ≤ 1/500` (G12b :1185–1216, verbatim)
  have hepsR0 : (0 : ℝ) < (Rd.eps : ℝ) := by exact_mod_cast Rd.heps
  have heps500R : (Rd.eps : ℝ) ≤ 1 / 500 := by
    have hq := (Rat.cast_le (K := ℝ)).mpr heps500
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at hq
    exact hq
  have hcop2 : (2 : ℝ) ≤ (Rd.eps : ℝ) ^ 2 * ((Rd.Hlo : ℕ) : ℝ) := by
    have hQ : ((Rd.a : ℕ) : ℚ) ≤ Rd.eps ^ 2 * ((Rd.Hlo : ℕ) : ℚ) / 2 := Rd.hcoprime
    have ha1 : (1 : ℚ) ≤ ((Rd.a : ℕ) : ℚ) := by exact_mod_cast Rd.ha
    have hQ2 : (2 : ℚ) ≤ Rd.eps ^ 2 * ((Rd.Hlo : ℕ) : ℚ) := by linarith
    exact_mod_cast hQ2
  have hHmono : (Rd.eps : ℝ) ^ 2 * ((Rd.Hlo : ℕ) : ℝ)
      ≤ (Rd.eps : ℝ) ^ 2 * ((Rd.Hhi : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast Rd.hHlohi) (sq_nonneg _)
  have hlognn : (0 : ℝ) ≤ Real.log ((Rd.eps : ℝ) ^ 2 * ((Rd.Hhi : ℕ) : ℝ)) :=
    Real.log_nonneg (by linarith)
  have h16 : (0 : ℝ) ≤ 16 / (Rd.eps : ℝ) := by positivity
  have h64 : (32000 : ℝ) ≤ 64 / (Rd.eps : ℝ) := by
    rw [le_div_iff₀ hepsR0]; linarith
  have hlogω : (32001 : ℝ) ≤ Real.log ((Rd.ω : ℕ) : ℝ) := by
    have hb2 := Rd.hωbig
    nlinarith [mul_nonneg h16 hlognn]
  have hω2N : 2 ≤ Rd.ω := Rd.hω
  have hωR : (0 : ℝ) < ((Rd.ω : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((Rd.ω : ℕ) : ℝ) := by exact_mod_cast hω2N
    linarith
  have hω8 : 8 ≤ Rd.ω := by
    have hsub := Real.log_le_sub_one_of_pos hωR
    have h8 : (8 : ℝ) ≤ ((Rd.ω : ℕ) : ℝ) := by linarith
    exact_mod_cast h8
  -- ⟦THE TRANSPORT⟧ F3-P16 at the shrunk regime, at the target grade `ρt`
  have htrans := mrtUniformityXiL2AffW_of_set_L h Rd a b ha heps500 hstride hdiv hlo4 hloM hcop
    hHloS hb hω8 Kc ρt hKcount hdoor
  -- ⟦THE TWO MEASUREMENTS⟧ F3-P17 on the ratio, F3-P18 on the endpoint (verbatim)
  have hx2 : 2 ≤ Rd.x / a := hstride.2.1
  have hωx2 : Rd.ω ≤ Rd.x / a := hstride.2.2.1
  have hratio := strideZRatio_le Rd.x (Rd.x / a) Rd.ω Rd.hx hx2 hω2N Rd.hωx hωx2
    (by linarith)
  have hZlo := (harmonic_window_bounds hx2 hω2N hωx2).1
  have hEnd0 := strideEndpoint_le Kc (a : ℝ)
    (∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹) (Rd.x / a / Rd.ω) Rd.ω
    hKc0.le (Nat.cast_nonneg a) (by linarith) hZlo
  -- ⟦THE E-BEATING⟧ (cell 23) at the shrunk regime's fields
  have hAE : Real.log (max 1 (Real.log (max 1
      (2 ^ 283 * (c : ℝ) ^ 20 * ((a * h : ℕ) : ℝ) / (128000 * ρ))))) / 3.2 ≤ A := by
    rw [← hAEdef]; exact hAEA
  have hDRd : flatDesignBase A ≤ Rd.Hhi :=
    le_trans hU (le_trans (le_of_eq hHlo.symm) Rd.hHlohi)
  have hHhi : ((flatDesignBase A : ℕ) : ℝ) ≤ ((Rd.Hhi : ℕ) : ℝ) := by exact_mod_cast hDRd
  have hE := zE_beaten hKc0 hKcb hc1 hkpos ha hρ hA162 hAE hHhi hstride.2.2.2.2.1 hlogω
    (le_trans hf2 hDRd)
  -- ⟦THE PACKAGE⟧
  refine ⟨A, hA162, hA₀A,
    ChowlaRegimeAff.ofRegime
      (regimeShrinkX_stride_L Rd a ha heps500 hstride hdiv hlo4 hloM hcop hHloS) b hb,
    rfl, rfl, hReps, hBle, ?_, ?_⟩
  · -- ⟦THE DESIGN LAW AT THE SHRUNK BASE⟧ off `flatDesignBase`'s own ceiling (verbatim)
    have hDge : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
      rw [flatDesignBase]; exact Nat.le_ceil _
    have hRaR : ((flatDesignBase A : ℕ) : ℝ) ≤ ((Rd.a * Rd.Hlo / a : ℕ) : ℝ) := by
      exact_mod_cast hBle
    have h1 : Real.exp (Real.exp (3.2 * A)) ≤ ((Rd.a * Rd.Hlo / a : ℕ) : ℝ) :=
      le_trans hDge hRaR
    have h2 : Real.exp (3.2 * A) ≤ Real.log ((Rd.a * Rd.Hlo / a : ℕ) : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h
    have h3 : 3.2 * A ≤ Real.log (Real.log ((Rd.a * Rd.Hlo / a : ℕ) : ℝ)) := by
      have h := Real.log_le_log (Real.exp_pos _) h2
      rwa [Real.log_exp] at h
    exact h3
  · -- ⟦THE GRADE⟧ `a·Zr·ρt + E ≤ a·1.02·ρt + ρ/2 = ρ/2 + ρ/2 = ρ`
    refine mrtUniformityXiL2AffW_mono h _ htrans ?_
    have hρ0 : (0 : ℝ) ≤ ρt := hρt.le
    have hratmul : (a : ℝ)
        * ((∑ n ∈ Finset.Ioc (Rd.x / Rd.ω) Rd.x, (n : ℝ)⁻¹)
            / (∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹)) * ρt
        ≤ (a : ℝ) * 1.02 * ρt := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio haR.le) hρ0
    have hid : (a : ℝ) * 1.02 * ρt = ρ / 2 := by
      rw [hρtdef]
      field_simp
      ring
    linarith only [hratmul, hEnd0, hE, hid]

/-! ## §R — THE ZERO LEVELS (the freeze's row Z0), AND THE STATEMENT MEETING ITS INHABITANT

The zero levels are VERBATIM from the road-F freeze of ARM Z (its scratch archive, where they
elaborated at three axioms): each is stated FROM the statement (it takes `hZ`), so each is a
control on `StrideDoorAllGradesW` itself, and an `example` instantiates it at the landed
`strideDoorAllGradesW_holds`.  ⚠ ZERO LEVEL A (`strideDoor_zero_level_g12b`: Z at the pin re-packs
the landed crown's conclusion) is HELD, not landed: it elaborates at three axioms, but it states
G12b's capped conclusion verbatim, so its code carries the cap tokens (`hah9`, `837782 * 2 ^ 12`,
`2 ^ 539`) that the wave's guard refuses in this file (arm E).  Recorded in
`docs/blueprints/flags.md`; the guard's amendment is the freeze author's. -/

/-- **⟦ZERO LEVEL A — Z AT THE PIN IS THE LANDED CROWN⟧** (`strideDoor_zero_level_g12b`) — from
`StrideDoorAllGradesW` at `ε := 1/(500·a·h)` and grade `a·ρ₀` (`ρ₀` the landed ceiling), the
conclusion of `mrtUniformityXiL2AffW_holds_flat_stride_g12b` (StridePairReceiptG12b.lean:1140)
VERBATIM, with `Zr := 1`, `E := 0`.  The cap `hah9` is a binder here so the two statements can be
laid side by side; it is READ NOWHERE (the linter would say so). -/
theorem strideDoor_zero_level_g12b (hZ : StrideDoorAllGradesW) (a b h : ℕ) (ha : 0 < a)
    (hh : 0 < h) (hba : b < a) (_hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
      ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
        flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
        ∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 12 * ((a * h : ℕ) : ℝ) ^ 2) ∧
          1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
          E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
              * (Real.log (Ra.ω : ℝ) - 1)) ∧
          MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E) := by
  have hkpos : 0 < a * h := Nat.mul_pos ha hh
  have hkQ1 : (1 : ℚ) ≤ ((a * h : ℕ) : ℚ) := by exact_mod_cast hkpos
  have hkR1 : (1 : ℝ) ≤ ((a * h : ℕ) : ℝ) := by exact_mod_cast hkpos
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  -- ⟦THE PIN⟧ `ε := 1/(500·k)`, inside Z's range
  have hε0 : (0 : ℚ) < 1 / (500 * ((a * h : ℕ) : ℚ)) := by positivity
  have hε500 : (1 : ℚ) / (500 * ((a * h : ℕ) : ℚ)) ≤ 1 / 500 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  -- ⟦THE GRADE⟧ `a · ρ₀` at the landed ceiling
  have hρ₀ : (0 : ℝ) < 1 / (837782 * 2 ^ 12 * ((a * h : ℕ) : ℝ) ^ 2) := by positivity
  obtain ⟨A, hA162, hA₀A, Ra, hRa, hRb, hReps, hHlo, hdes, hdoor⟩ :=
    hZ a b h ha hba hh (1 / (500 * ((a * h : ℕ) : ℚ))) le_rfl hε500
      ((a : ℝ) * (1 / (837782 * 2 ^ 12 * ((a * h : ℕ) : ℝ) ^ 2))) (by positivity) A₀
  -- ⟦THE WIDTH NUMERAL⟧ `log ω ≥ 32001` off `hωbig` at `ε ≤ 1/500` — G12b :1200–1216,
  -- verbatim at `Ra`
  have heps500 : Ra.eps ≤ 1 / 500 := by rw [hReps]; exact hε500
  have hepsR0 : (0 : ℝ) < (Ra.eps : ℝ) := by exact_mod_cast Ra.heps
  have hcop : (2 : ℝ) ≤ (Ra.eps : ℝ) ^ 2 * ((Ra.Hlo : ℕ) : ℝ) := by
    have hQ : ((Ra.a : ℕ) : ℚ) ≤ Ra.eps ^ 2 * ((Ra.Hlo : ℕ) : ℚ) / 2 := Ra.hcoprime
    have ha1 : (1 : ℚ) ≤ ((Ra.a : ℕ) : ℚ) := by exact_mod_cast Ra.ha
    have hQ2 : (2 : ℚ) ≤ Ra.eps ^ 2 * ((Ra.Hlo : ℕ) : ℚ) := by linarith
    exact_mod_cast hQ2
  have hHmono : (Ra.eps : ℝ) ^ 2 * ((Ra.Hlo : ℕ) : ℝ)
      ≤ (Ra.eps : ℝ) ^ 2 * ((Ra.Hhi : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast Ra.hHlohi) (sq_nonneg _)
  have hlognn : (0 : ℝ) ≤ Real.log ((Ra.eps : ℝ) ^ 2 * ((Ra.Hhi : ℕ) : ℝ)) :=
    Real.log_nonneg (by linarith)
  have h16 : (0 : ℝ) ≤ 16 / (Ra.eps : ℝ) := by positivity
  have heps500R : (Ra.eps : ℝ) ≤ 1 / 500 := by
    have hq := (Rat.cast_le (K := ℝ)).mpr heps500
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at hq
    exact hq
  have h64 : (32000 : ℝ) ≤ 64 / (Ra.eps : ℝ) := by
    rw [le_div_iff₀ hepsR0]; linarith
  have hlogω : (32001 : ℝ) ≤ Real.log ((Ra.ω : ℕ) : ℝ) := by
    have hb2 := Ra.hωbig
    nlinarith [mul_nonneg h16 hlognn]
  have hDpos : (0 : ℝ) < (a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1 := by positivity
  have hLpos : (0 : ℝ) < Real.log ((Ra.ω : ℕ) : ℝ) - 1 := by linarith
  -- ⟦THE PACKAGE⟧ `Zr := 1`, `E := 0`; the door at `a·1·ρ₀ + 0 = a·ρ₀` is Z's, by monotonicity
  refine ⟨1 / (500 * ((a * h : ℕ) : ℚ)), A, hε0, le_rfl, rfl, hA162, hA₀A, Ra, hRa, hRb, hReps,
    hHlo, hdes, 1 / (837782 * 2 ^ 12 * ((a * h : ℕ) : ℝ) ^ 2), 1, 0, hρ₀, le_rfl, le_rfl,
    by norm_num, le_rfl, ?_, ?_⟩
  · exact div_nonneg (by positivity) (mul_pos hDpos hLpos).le
  · refine mrtUniformityXiL2AffW_mono h Ra hdoor (le_of_eq ?_)
    ring

/-- The zero level A at the landed theorem: Z at the pin re-packs the landed crown's conclusion. -/
example (a b h : ℕ) (ha : 0 < a) (hh : 0 < h) (hba : b < a)
    (hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
      ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
        flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
        ∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 12 * ((a * h : ℕ) : ℝ) ^ 2) ∧
          1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
          E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
              * (Real.log (Ra.ω : ℝ) - 1)) ∧
          MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E) :=
  strideDoor_zero_level_g12b strideDoorAllGradesW_holds a b h ha hh hba hah9 A₀

/-- **⟦ZERO LEVEL B — Z AT `(1, 0, 1)` IS THE FLAT DOOR AT `ε = 1/500`, EVERY GRADE⟧**
(`strideDoor_zero_level_flat`) — W-δ's body (`FlatDoorAllGradesW`, FlatDoorAllGrades.lean:50–55) at
`ε = 1/500`: at stride 1 and twist 1 the affine set is `bigXi` (`bigXiAff_one_zero`,
`bigXi_eq_bigXiH_one`), the affine measure is `logMeasure` (`logMeasureAff_one`), and the range
`1 ∣ H ∧ 1·Hlo ≤ H` is the regime's own.  ⚠ Z's ε-floor is `1/(500·a·h)`, so at `a = h = 1` the
only `ε` Z reaches is `1/500` — W-δ's `∀ ε ∈ (0, 1/500]` is NOT recovered by Z (freeze §5). -/
theorem strideDoor_zero_level_flat (hZ : StrideDoorAllGradesW) (ρ : ℝ) (hρ : 0 < ρ) (A₀ : ℝ) :
    ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = 1 / 500 ∧ flatDesignBase A ≤ R.Hlo ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        MRTUniformityXiL2 R ρ := by
  obtain ⟨A, hA162, hA₀A, Ra, hRa, hRb, hReps, hHlo, hdes, hdoor⟩ :=
    hZ 1 0 1 one_pos one_pos one_pos (1 / 500) (by norm_num) le_rfl ρ hρ A₀
  refine ⟨A, hA162, hA₀A, Ra.toChowlaRegime, hReps, hHlo, hdes, ?_⟩
  intro H _ hlo hhi
  have hd := hdoor H (by rw [hRa]; exact one_dvd H) (by rw [hRa, one_mul]; exact hlo) hhi
  rw [hRa, hRb, bigXiAff_one_zero, ← bigXi_eq_bigXiH_one, logMeasureAff_one] at hd
  exact hd

/-- The zero level B at the landed theorem: Z at `(1, 0, 1)` is the flat door at `ε = 1/500`. -/
example (ρ : ℝ) (hρ : 0 < ρ) (A₀ : ℝ) :
    ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = 1 / 500 ∧ flatDesignBase A ≤ R.Hlo ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        MRTUniformityXiL2 R ρ :=
  strideDoor_zero_level_flat strideDoorAllGradesW_holds ρ hρ A₀

end Salt.MR

end
