/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.StridePairReceiptG12b
import Salt.MR.RegimeHead
import Mathlib

/-!
# ⟦TIER S — S-1⟧ THE `∀x'`-BANDED TWIN OF THE `2^12` CHAIN, WITH THE TIGHT CEILING EXPORTED
(`TierSBand`)

**STATEMENT-ONLY FREEZE DRAFT (S-1 design act, salt QUEUE P3 item 11).  Every body below is `sorry`;
nothing here is proved, and nothing bears on twin primes.  This file is the kernel-elaborated form
of
the S-1 freeze's statements and is NOT to be merged as is.**

S-1 is the `∀x'`-BANDED twin of the live (`_g12b`) generation of the flat door chain — H0 head → H1
road-exit → H2 capstone → H3 conditional → H4 Kswin → H5 V7-rated → the crown — carrying the TIGHT
outer-scale ceiling as an EXPORT-ONLY conjunct in the MAX shape, with the band hypothesis on `x'`
left LOOSE.  ONE RULE produces each band form from its `StridePairReceiptG12b.lean` source, byte for
byte otherwise:

  (i)  after the loose ceiling `Real.log R.x ≤ 31/ε · R.Hhi ∧` (for `V7RatedFormHG_g12b`, which
       carries no ceiling, after `StrideScale a R ∧`) INSERT the export-only tight conjunct
         `Real.log R.x ≤ max (xTightCeil ε R.Hhi) (Real.log (a · g R.Hhi R.ω))`
       — `XCeil.lean:494-497`'s `hxu` at the stride builder (`StridePairReceipt.lean:2703`, the
       `+ 9` is `log a ≤ 9` at `a ≤ 8103`), through the enlargement `x ↦ max x (a·g Hhi ω)`;
  (ii) PREFIX the antecedent block with the band quantifier
         `∀ (x' : ℕ) (hx' : R.x ≤ x'), a ∣ x' → Real.log x' ≤ 31/ε · R.Hhi →`
       and REPLACE every occurrence of the regime `R` inside that block by `regimeEnlargeX R hx'`.

WHY THE BAND IS THREADED THROUGH EVERY FORM: each hop passes ONE regime through and the statements
export nothing that ties the output regime to the input regime, so a band that is not in the form
cannot be recovered from the chain's conclusion.  WHY `a ∣ x'`: `StrideScale a R` opens with
`a ∣ R.x`, and the crown divides the scale by `a`.  WHY THE LOOSE ceiling and not the tight one in
the
band: the tight reading gives floor and ceiling the same leading coefficient and empties S-3's set
(freeze v1.1 §2).  WHY THE MAX shape: the builder enlarges `x` to `max x (a·g Hhi ω)`, so the
caller's own `g` is part of the answer (`All.lean:7743-7746`); at `g ≡ 0` the MAX collapses to the
tight arm (`Real.log 0 = 0`).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla

set_option exponentiation.threshold 4000

namespace Salt.MR

/-! ## §0 — the tight ceiling, named once -/

/-- **⟦S-1⟧ THE TIGHT OUTER-SCALE CEILING AT THE STRIDE BUILDER** — `XCeil.lean:494-497`'s `hxu`
with the stride multiplier's `log a ≤ 9` absorbed (`StridePairReceipt.lean:2703-2710`):
`log R.x ≤ (30/ε)·log H₊ + 9 + 2·log(4^⌊ε²H₊⌋ + 1)`.  Against the loose `31/ε · H₊` its
leading term is `2·log 4·ε²·H₊` — smaller by the factor `31/(2·log 4·ε³)` (`1.4·10⁹` at
`ε = 1/500`, `7.4·10²⁰` at the pin `ε = 1/(500·8103)`). -/
def xTightCeil (ε : ℚ) (Hhi : ℕ) : ℝ :=
  30 / (ε : ℝ) * Real.log ((Hhi : ℕ) : ℝ) + 9
    + 2 * Real.log (((4 ^ ⌊ε ^ 2 * (Hhi : ℚ)⌋₊ : ℕ) : ℝ) + 1)

/-! ## §1 — the six band forms (rule (i)+(ii) applied to `StridePairReceiptG12b.lean:47-293`) -/

def FlatHeadFormHG_g12b_band (h : ℕ) (Xi : XiFamily) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (ε : ℚ) (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 539 ∧ 0 < δ₀ ∧
      1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * 2 ^ 12 * (h : ℝ) ^ 2) ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 26 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap = max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (a extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → a ≤ 8103 →
            XCeilRider ε (fun Hhi ω => a * g Hhi ω) → ∃ R : ChowlaRegime,
            R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ a * g R.Hhi R.ω ≤ R.x ∧
            StrideScale a R ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            Real.log ((R.x : ℕ) : ℝ)
              ≤ max (xTightCeil ε R.Hhi) (Real.log ((a * g R.Hhi R.ω : ℕ) : ℝ)) ∧
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((Xi R.eps H).card : ℝ) ≤ K) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            R.Hlo ≤ max Hcap (max extraFloor U1floor) ∧
            ∀ (x' : ℕ) (hx' : R.x ≤ x'), a ∣ x' →
              Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
              ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2Set Xi (regimeEnlargeX R hx') ρ →
                P (regimeEnlargeX R hx')

def FlatRoadExitFormHG_g12b_band (h : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 539 ∧ 0 < δ₀ ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧
      1 / (838400 * 2 ^ 12 * (h : ℝ) ^ 2) ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (a U1floor : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → a ≤ 8103 →
            XCeilRider ε (fun Hhi ω => a * g Hhi ω) →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ a * g R.Hhi R.ω ≤ R.x ∧
              StrideScale a R ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              Real.log ((R.x : ℕ) : ℝ)
                ≤ max (xTightCeil ε R.Hhi) (Real.log ((a * g R.Hhi R.ω : ℕ) : ℝ)) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (x' : ℕ) (hx' : R.x ≤ x'), a ∣ x' →
                Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
                ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
                  M4DoorGates_L_gk K Cg (regimeEnlargeX R hx') M k δ → 1 ≤ M →
                  (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
                  (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    ((h : ℝ) * arcDen 12 H) ^ 7 ≤ RStr H) →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    44 * RSan H + 87 * ((h : ℝ) * arcDen 12 H) ≤ (4 / 3 : ℝ) ^ j₀) →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    128 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ)) →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    (h : ℝ) * arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
                        * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                      ≤ Braw H) →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    Braw H ≤ Bceil) →
                  2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / ((regimeEnlargeX R hx').x : ℝ) ≤ δ₀ →
                  M4ChiSummedFreeRowH_L_gk h K (regimeEnlargeX R hx') M RS →
                    P (regimeEnlargeX R hx')

def FlatCapstoneFormHG_g12b_band (h : ℕ) (Awin : ℝ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * 2 ^ 12 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (a U1floor : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → a ≤ 8103 →
            XCeilRider ε (fun Hhi ω => a * g Hhi ω) →
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ a * g R.Hhi R.ω ≤ R.x ∧
              StrideScale a R ∧
                Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
                Real.log ((R.x : ℕ) : ℝ)
                  ≤ max (xTightCeil ε R.Hhi) (Real.log ((a * g R.Hhi R.ω : ℕ) : ℝ)) ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (x' : ℕ) (hx' : R.x ≤ x'), a ∣ x' →
                  Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
                  ∀ (M : ℕ), Mfl ≤ M → K ≤ 170000000 * M →
                    ∃ C' : ℝ, 0 < C' ∧
                      8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                          ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                      ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                        -- ⟦A⟧ THE SPINE ARITHMETIC
                        M4DoorGates_L_gk K Cg (regimeEnlargeX R hx') M k δ₀ →
                        8 * 2 ^ k / ((regimeEnlargeX R hx').x : ℝ) ≤ δ₀ / 4 →
                        (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                          4 * Real.log (263 * (h : ℝ) * max 1 (arcDen 12 H))
                            ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                        (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                          (h : ℝ) * arcDen 12 H
                            < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                        (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                          m4SmallGradeFits (doorRowFloorL M)
                            (fun H => 2 * RSanDoorRhoH (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) h H)
                            (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H) →
                        -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          DoorBaseFrame (A + s) j) →
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                            ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) (regimeEnlargeX R
                              hx').Hhi) →
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          GRowsZeroGate'''_L_gk K M (A + s) Cp
                            (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) (regimeEnlargeX R
                              hx').Hhi)) →
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          14 * Real.log (Real.log (((regimeEnlargeX R hx').Hhi : ℕ) : ℝ)) +
                            Real.log 376266
                              + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                            ≤ (theta293 - epsrf (A + s))
                                * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                            ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) (regimeEnlargeX R
                              hx').Hhi) →
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                            * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) (regimeEnlargeX R
                              hx').Hhi) →
                        -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                                ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                            (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                            (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                        -- ⟦B4 RAW⟧ the crossing bound, carried
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
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
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                            (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                          P (regimeEnlargeX R hx')

def FlatConditionalFormHG_g12b_band (h : ℕ) (Awin : ℝ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (ε : ℚ) (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * 2 ^ 12 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (a U1floor : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → a ≤ 8103 → XCeilRiderStrict ε g →
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ a * g R.Hhi R.ω ≤ R.x ∧
              StrideScale a R ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              Real.log ((R.x : ℕ) : ℝ)
                ≤ max (xTightCeil ε R.Hhi) (Real.log ((a * g R.Hhi R.ω : ℕ) : ℝ)) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ (x' : ℕ) (hx' : R.x ≤ x'), a ∣ x' →
                Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
                ∀ M : ℕ, K ≤ 170000000 * M →
                  S15Sel''_L_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl
                    (regimeEnlargeX R hx') M →
                  S15CrossingBound_LH_gk h K (regimeEnlargeX R hx') M → P (regimeEnlargeX R hx')

def FlatKswinFormHG_g12b_band (h : ℕ) (Awin : ℝ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (ε : ℚ) (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * 2 ^ 12 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧
        ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
          K ≤ 170000000 * flatDoorM A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          T₀ ≤ Real.exp (Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ) / 2) →
          Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 →
          ∀ (U1floor : ℕ), flatWitFloor ε β A Hopq ≤ U1floor →
            Real.log (Real.log ((U1floor : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 →
          ∀ (a : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → a ≤ 8103 → XCeilRiderStrict ε g →
            ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = U1floor ∧ a * g R.Hhi R.ω ≤ R.x ∧ StrideScale a R ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            Real.log ((R.x : ℕ) : ℝ)
              ≤ max (xTightCeil ε R.Hhi) (Real.log ((a * g R.Hhi R.ω : ℕ) : ℝ)) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            ∀ (x' : ℕ) (hx' : R.x ≤ x'), a ∣ x' →
              Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
              (S16CofactorSupply_LH_gk h K Cq (regimeEnlargeX R hx') (flatDoorM A) →
                S16BaseScaleCap96_LH_gk h K (regimeEnlargeX R hx') (flatDoorM A) →
                  P (regimeEnlargeX R hx')))

def V7RatedFormHG_g12b_band (h : ℕ) (P : ChowlaRegime → Prop) (A₀ : ℝ) : Prop :=
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧ Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧
      1 / (838400 * 2 ^ 12 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Mfl ≤ flatDoorM A ∧ 0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∀ (U1floor a : ℕ) (g : ℕ → ℕ → ℕ), flatDesignBase A ≤ U1floor →
        Real.log (Real.log ((U1floor : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 →
        1 ≤ a → a ≤ 8103 → XCeilRiderStrict ε g →
      ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = U1floor ∧ a * g R.Hhi R.ω ≤ R.x ∧ StrideScale a R ∧
        Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
        Real.log ((R.x : ℕ) : ℝ)
          ≤ max (xTightCeil ε R.Hhi) (Real.log ((a * g R.Hhi R.ω : ℕ) : ℝ)) ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        ∀ (x' : ℕ) (hx' : R.x ≤ x'), a ∣ x' →
          Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
          P (regimeEnlargeX R hx')


/-! ## §2 — the class-A pack the hops consume -/

/-- **⟦S-1 A1⟧** the enlargement at the regime's own scale is the regime. -/
theorem regimeEnlargeX_self (R : ChowlaRegime) : regimeEnlargeX R (le_refl R.x) = R := by
  cases R; rfl

/-- **⟦S-1 A2⟧** `StrideScale` survives the enlargement to any multiple of `a` above `R.x`: every
conjunct reads `R.x / a` or `a ∣ R.x`, and `x' / a ≥ R.x / a` at `a ∣ x'`. -/
theorem strideScale_regimeEnlargeX (a : ℕ) (R : ChowlaRegime) {x' : ℕ} (hx' : R.x ≤ x')
    (hdvd : a ∣ x') (hs : StrideScale a R) : StrideScale a (regimeEnlargeX R hx') := by
  obtain ⟨-, h2, h3, h4, h5, h6, h7⟩ := hs
  have hq : R.x / a ≤ x' / a := Nat.div_le_div_right hx'
  have hqω : R.x / a / R.ω ≤ x' / a / R.ω := Nat.div_le_div_right hq
  have hqR : ((R.x / a : ℕ) : ℝ) ≤ ((x' / a : ℕ) : ℝ) := by exact_mod_cast hq
  have hqωR : ((R.x / a / R.ω : ℕ) : ℝ) ≤ ((x' / a / R.ω : ℕ) : ℝ) := by exact_mod_cast hqω
  refine ⟨hdvd, le_trans h2 hq, le_trans h3 hq, le_trans h4 hqω, ?_, ?_, ?_⟩
  · simp only [regimeEnlargeX_Hhi, regimeEnlargeX_omega, regimeEnlargeX_x]
    exact le_trans h5 hqωR
  · simp only [regimeEnlargeX_Hhi, regimeEnlargeX_omega, regimeEnlargeX_x, regimeEnlargeX_eps]
    exact le_trans h6 hqR
  · simp only [regimeEnlargeX_Hhi, regimeEnlargeX_omega, regimeEnlargeX_x, regimeEnlargeX_eps]
    exact le_trans h7 hqR

/-- **⟦S-1 A3⟧** the tight ceiling is nonnegative, so `max (xTightCeil ε H₊) (Real.log 0)` collapses
to the tight arm at `g ≡ 0` (`0 < ε`, `4·10⁶ ≤ H₊`). -/
theorem xTightCeil_nonneg (ε : ℚ) (hε : 0 < ε) (Hhi : ℕ) (hHhi : 4000000 ≤ Hhi) :
    0 ≤ xTightCeil ε Hhi := by
  unfold xTightCeil
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have h1N : 1 ≤ Hhi := le_trans (by norm_num) hHhi
  have h1 : (1 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast h1N
  have hl : 0 ≤ Real.log ((Hhi : ℕ) : ℝ) := Real.log_nonneg h1
  have hP0 : (0 : ℝ) ≤ ((4 ^ ⌊ε ^ 2 * (Hhi : ℚ)⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hl2 : 0 ≤ Real.log (((4 ^ ⌊ε ^ 2 * (Hhi : ℚ)⌋₊ : ℕ) : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have h30 : 0 ≤ 30 / (ε : ℝ) * Real.log ((Hhi : ℕ) : ℝ) := mul_nonneg (by positivity) hl
  linarith

/-! ## §3 — the builder twins: the tight bound lifted OUT of the proof (`XCeil.lean:494-497`) -/

/-- **⟦S-1 B1⟧** `chowlaRegimeFlat_exists_param_gen_ceiling_mul_b9` (`StridePairReceipt.lean:2571`)
with ITS OWN `hxu` (`:2703`) exported: body verbatim, one conjunct added. -/
theorem chowlaRegimeFlat_exists_param_gen_ceiling_mul_b9_tight (a : ℕ) (ha : 1 ≤ a)
    (ha8103 : a ≤ 8103) (A : ℝ) (hA : 26 ≤ A) (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (Hlo₀ : ℕ) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      StrideScale a R.toChowlaRegime ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ xTightCeil eps R.Hhi := by
  sorry

/-- **⟦S-1 B2⟧** `chowlaRegimeFlat_exists_param_head_xceil_mul_b9` (`:2749`) on B1: the enlargement
`x ↦ max x (a·g H₊ ω)` turns the tight bound into the MAX shape. -/
theorem chowlaRegimeFlat_exists_param_head_xceil_mul_b9_tight (a : ℕ) (ha : 1 ≤ a)
    (ha8103 : a ≤ 8103) (A : ℝ) (hA : 26 ≤ A) (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (Hlo₀ : ℕ) (g : ℕ → ℕ → ℕ) (hg : XCeilRider eps (fun Hhi ω => a * g Hhi ω)) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      a * g R.Hhi R.ω ≤ R.x ∧ StrideScale a R.toChowlaRegime ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
      Real.log ((R.x : ℕ) : ℝ)
        ≤ max (xTightCeil eps R.Hhi) (Real.log ((a * g R.Hhi R.ω : ℕ) : ℝ)) := by
  sorry

/-! ## §4 — the head, the five hops, the chain (each: the `_g12b` source's binders, the band forms)
-/

/-- **⟦S-1 H0⟧** `flat_door_head_xceil_h_g12b` (`:936`) at the band head form: the builder B2
supplies
the tight conjunct; for each `x'` in the band the receipt at `regimeEnlargeX R hx'` is the door at
`regimeEnlargeX R hx'` plus the count (which reads `Hlo`, `Hhi`, `eps` only) and the pin. -/
theorem flat_door_head_xceil_h_g12b_band (h : ℕ) (hh : 0 < h) (_hh9 : Real.log (h : ℝ) ≤ 9)
    (Xi : XiFamily)
    (hcount : ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 539 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((Xi (1 / (500 * (h : ℚ))) H).card : ℝ) ≤ C) :
    FlatHeadFormHG_g12b_band h Xi (MRTDoorReceiptSetG_g12b h Xi) := by
  sorry

/-- **⟦S-1 H0→H1⟧** `flat_roadExit_generic_h_g12b` (`:320`) at the band forms. -/
theorem flat_roadExit_generic_h_g12b_band (h : ℕ) (hh : 0 < h) (_hh9 : Real.log (h : ℝ) ≤ 9)
    (Xi : XiFamily)
    (harcXi : ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
      ∀ ξ ∈ Xi eps H, NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (P : ChowlaRegime → Prop) (hhead : FlatHeadFormHG_g12b_band h Xi P) :
    FlatRoadExitFormHG_g12b_band h P := by
  sorry

/-- **⟦S-1 H1→H2⟧** `flat_capstone_generic_h_g12b` (`:351`) at the band forms. -/
theorem flat_capstone_generic_h_g12b_band (h : ℕ) (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9)
    (Awin : ℝ) (hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hroad : FlatRoadExitFormHG_g12b_band h P) :
    FlatCapstoneFormHG_g12b_band h Awin P := by
  sorry

/-- **⟦S-1 H2→H3⟧** `flat_conditional_generic_h_g12b` (`:504`) at the band forms. -/
theorem flat_conditional_generic_h_g12b_band (h : ℕ) (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9)
    (Awin : ℝ) (_hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hcap : FlatCapstoneFormHG_g12b_band h Awin P) :
    FlatConditionalFormHG_g12b_band h Awin P := by
  sorry

/-- **⟦S-1 H3→H4⟧** `flat_kswin_generic_h_g12b` (`:703`) at the band forms. -/
theorem flat_kswin_generic_h_g12b_band (h : ℕ) (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9)
    (Awin : ℝ) (_hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hcond : FlatConditionalFormHG_g12b_band h Awin P) :
    FlatKswinFormHG_g12b_band h Awin P := by
  sorry

/-- **⟦S-1 H4→H5⟧** `flat_v7_generic_h_g12b` (`:807`) at the band forms.  The two suppliers it fires
at `R` — `cofkR_cofactorSupply_L_gk_rated_h_b9` and `s16_baseScaleCap96_LH_at_klevF_b9 … hxceil
hwin` —
are fired at `regimeEnlargeX R hx'`, the second reading its ceiling FROM THE BAND HYPOTHESIS. -/
theorem flat_v7_generic_h_g12b_band (h : ℕ) (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9)
    (P : ChowlaRegime → Prop)
    (hk : ∀ Awin : ℝ, S16BandLaneCBoundedLH_winU h Awin → FlatKswinFormHG_g12b_band h Awin P)
    (A₀ : ℝ) :
    V7RatedFormHG_g12b_band h P A₀ := by
  sorry

/-- **⟦S-1 CHAIN⟧** `flat_chain_generic_h_g12b` (`:1045`) at the band forms. -/
theorem flat_chain_generic_h_g12b_band (h : ℕ) (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9)
    (Xi : XiFamily)
    (harcXi : ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
      ∀ ξ ∈ Xi eps H, NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (P : ChowlaRegime → Prop) (hhead : FlatHeadFormHG_g12b_band h Xi P) (A₀ : ℝ) :
    V7RatedFormHG_g12b_band h P A₀ := by
  sorry

/-! ## §5 — the crown side: the receipt at every scale of the band -/

/-- **⟦S-1 C1⟧** `mrtUniformityXiL2Set_holds_flat_floor_g12b` (`:1061`) at the band chain: ONE
regime
`R` whose door holds at EVERY `x'` in the band, with the tight ceiling on `R.x` exported. -/
theorem mrtUniformityXiL2Set_holds_flat_floor_g12b_band (h : ℕ) (hh : 0 < h)
    (hh9 : Real.log (h : ℝ) ≤ 9)
    (Xi : XiFamily)
    (harcXi : ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
      ∀ ξ ∈ Xi eps H, NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (hcount : ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 539 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((Xi (1 / (500 * (h : ℚ))) H).card : ℝ) ≤ C)
    (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ ε = 1 / (500 * (h : ℚ)) ∧
      162 ≤ A ∧ A₀ ≤ A ∧
      ∀ (U1floor a : ℕ) (g : ℕ → ℕ → ℕ), flatDesignBase A ≤ U1floor →
        Real.log (Real.log ((U1floor : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 →
        1 ≤ a → a ≤ 8103 → XCeilRiderStrict ε g →
      ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = U1floor ∧ a * g R.Hhi R.ω ≤ R.x ∧ StrideScale a R ∧
        Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
        Real.log ((R.x : ℕ) : ℝ)
          ≤ max (xTightCeil ε R.Hhi) (Real.log ((a * g R.Hhi R.ω : ℕ) : ℝ)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        (∃ K : ℝ, 0 < K ∧ K ≤ 2 ^ 539 ∧ ∀ (H : ℕ) [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
          ((Xi R.eps H).card : ℝ) ≤ K) ∧
        ∀ (x' : ℕ) (hx' : R.x ≤ x'), a ∣ x' →
          Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
          ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 12 * (h : ℝ) ^ 2) ∧
            MRTUniformityXiL2Set Xi (regimeEnlargeX R hx') ρ := by
  sorry

/-- **⟦S-1 C2⟧** `mrtUniformityXiL2AffSet_holds_flat_floor_g12b` (`:1105`) at the band: C1 at the
affine set `bigXiAffD a b h`, `k = a·h`. -/
theorem mrtUniformityXiL2AffSet_holds_flat_floor_g12b_band (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
      ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∀ (U1floor a' : ℕ) (g : ℕ → ℕ → ℕ), flatDesignBase A ≤ U1floor →
        Real.log (Real.log ((U1floor : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 →
        1 ≤ a' → a' ≤ 8103 → XCeilRiderStrict ε g →
      ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = U1floor ∧ a' * g R.Hhi R.ω ≤ R.x ∧ StrideScale a' R ∧
        Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
        Real.log ((R.x : ℕ) : ℝ)
          ≤ max (xTightCeil ε R.Hhi) (Real.log ((a' * g R.Hhi R.ω : ℕ) : ℝ)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        (∃ K : ℝ, 0 < K ∧ K ≤ 2 ^ 539 ∧ ∀ (H : ℕ) [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
          ((bigXiAffD a b h R.eps H).card : ℝ) ≤ K) ∧
        ∀ (x' : ℕ) (hx' : R.x ≤ x'), a' ∣ x' →
          Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
          ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 12 * ((a * h : ℕ) : ℝ) ^ 2) ∧
            MRTUniformityXiL2Set (fun eps H _ => bigXiAffD a b h eps H) (regimeEnlargeX R hx') ρ :=
              by
  sorry

/-- **⟦S-1 CROWN⟧** `mrtUniformityXiL2AffW_holds_flat_stride_g12b` (`:1140`) at the band, stated
over
the AFFINE scale `y = x'/a`: the band's BOTTOM `x₀` carries the tight ceiling (at the crown's own
`g ≡ 0` the MAX collapses), the band's ROOF is the loose ceiling on `a·y`, and at every `y` in the
band
the affine door holds at an affine regime with `Ra.x = y`, the SAME `ω₀`, the SAME `Hhi₀`.  This is
the object S-3 consumes: D12's `hwin` at fixed `ω₀` over `x ∈ [x₀, M]`. -/
theorem mrtUniformityXiL2AffW_holds_flat_stride_g12b_band (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hba : b < a) (hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
      ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ (x₀ ω₀ Hhi₀ : ℕ), 2 ≤ x₀ ∧ 8 ≤ ω₀ ∧ 4000000 ≤ Hhi₀ ∧
        Real.log ((x₀ : ℕ) : ℝ) ≤ xTightCeil ε Hhi₀ ∧
        Real.log ((a * x₀ : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ) ∧
        ∀ y : ℕ, x₀ ≤ y → Real.log ((a * y : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ) →
          ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
            Ra.x = y ∧ Ra.ω = ω₀ ∧ Ra.Hhi = Hhi₀ ∧
            flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
            ∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 12 * ((a * h : ℕ) : ℝ) ^ 2) ∧
              1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
              E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
                  * (Real.log (Ra.ω : ℝ) - 1)) ∧
              MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E) := by
  sorry

/-! ## §6 — the conservativity controls: each band form implies its source (instantiate `x' :=
R.x`) -/

/-- **⟦S-1 K1⟧** the band head form is a conservative extension of `FlatHeadFormHG_g12b`. -/
theorem flatHeadFormHG_g12b_of_band (h : ℕ) (Xi : XiFamily) (P : ChowlaRegime → Prop)
    (hb : FlatHeadFormHG_g12b_band h Xi P) : FlatHeadFormHG_g12b h Xi P := by
  obtain ⟨ε, K, δ₀, β, Hopq, hε, hK, hKb, hδ₀, hεpin, hδpin, hβ, hbody⟩ := hb
  refine ⟨ε, K, δ₀, β, Hopq, hε, hK, hKb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro A hA hAge
  obtain ⟨Hcap, hCap, hmain⟩ := hbody A hA hAge
  refine ⟨Hcap, hCap, ?_⟩
  intro a extraFloor U1floor g ha ha8103 hg
  obtain ⟨R, hReps, hextra, hU1, hRg, hstride, hxceil, -, hcount, hwid, hcap, hband⟩ :=
    hmain a extraFloor U1floor g ha ha8103 hg
  refine ⟨R, hReps, hextra, hU1, hRg, hstride, hxceil, hcount, hwid, hcap, ?_⟩
  intro ρ hρ hρle hdoor
  have h := hband R.x (le_refl _) hstride.1 hxceil ρ hρ hρle
    (by rw [regimeEnlargeX_self]; exact hdoor)
  rwa [regimeEnlargeX_self] at h

/-- **⟦S-1 K2⟧** the band V7-rated form is a conservative extension of `V7RatedFormHG_g12b`. -/
theorem v7RatedFormHG_g12b_of_band (h : ℕ) (P : ChowlaRegime → Prop) (A₀ : ℝ)
    (hb : V7RatedFormHG_g12b_band h P A₀) : V7RatedFormHG_g12b h P A₀ := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCq, hcs, hcsf, hT₀, hKq, hKs, hC, hC40, hCgle, hεpin, hδpin, hMflb, hβ, hA162, hA₀A,
    hbody⟩ := hb
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCq, hcs, hcsf, hT₀, hKq, hKs, hC, hC40, hCgle, hεpin, hδpin, hMflb, hβ, hA162, hA₀A, ?_⟩
  intro U1floor a g hU hUceil ha ha8103 hg
  obtain ⟨R, hReps, hHlo, hRg, hstride, hxceil, -, hRtow, hdes, hwin, hband⟩ :=
    hbody U1floor a g hU hUceil ha ha8103 hg
  refine ⟨R, hReps, hHlo, hRg, hstride, hRtow, hdes, hwin, ?_⟩
  have h := hband R.x (le_refl _) hstride.1 hxceil
  rwa [regimeEnlargeX_self] at h

/-- **⟦S-1 K3⟧** the band crown implies the landed crown's shape at `y := x₀`
(`mrtUniformityXiL2AffW_holds_flat_stride_g12b`'s conclusion, minus nothing). -/
theorem mrtUniformityXiL2AffW_holds_flat_stride_g12b_of_band (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hba : b < a) (hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
      ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
        flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
        ∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 12 * ((a * h : ℕ) : ℝ) ^ 2) ∧
          1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
          E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
              * (Real.log (Ra.ω : ℝ) - 1)) ∧
          MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E) := by
  obtain ⟨ε, A, hε, hεpin, hεeq, hA162, hA₀A, x₀, ω₀, Hhi₀, -, -, -, -, hx₀ceil, hband⟩ :=
    mrtUniformityXiL2AffW_holds_flat_stride_g12b_band a b h ha hh hba hah9 A₀
  obtain ⟨Ra, hRa, hRb, hReps, -, -, -, hHlo, hdes, hgrade⟩ := hband x₀ le_rfl hx₀ceil
  exact ⟨ε, A, hε, hεpin, hεeq, hA162, hA₀A, Ra, hRa, hRb, hReps, hHlo, hdes, hgrade⟩

end Salt.MR

end
