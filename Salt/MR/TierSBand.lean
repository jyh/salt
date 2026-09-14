/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.StridePairReceiptG12b
import Salt.MR.RegimeHead
import Mathlib

-- Needed to transcribe B1/B2/H0/hop1's proofs, the same private names
-- `StridePairReceiptG12b.lean:28-30` opens for the identical purpose.
open private flatCapH_shuffle from Salt.Entropy.Chowla.HloExportFlatH
open private xceil_flat_P xceil_flat_step from Salt.MR.XCeil
open private flatRootCapH_arc_k from Salt.MR.S16ComposeLH

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

  (i-ω) after the loose ceiling `Real.log R.x ≤ 31/ε · R.Hhi ∧` INSERT the RIDER-FREE tight ceiling
       on the width, `Real.log R.ω ≤ xTightCeil ε R.Hhi` — `8·P²·ω ≤ x₀` (`hPHheadroom`) against
       `hxu` at the builder's own `x₀`; `ω` is untouched by the enlargement and by every hop;
  (i-x) then the export-only tight bound on `x` in the MAX shape, in TWO TIERS because hop 3
       (`flat_conditional_generic_h_g12b`, `:610`) instantiates its source at the INFLATED rider
       `s15ArmH … + g` and a rider-relative bound cannot cross it (refuter pass v1, R2 Q2):
         tier A (H0 · H1 · H2, the rider passes verbatim):
           `Real.log R.x ≤ max (xTightCeil ε R.Hhi) (Real.log (a · g R.Hhi R.ω))`
         tier B (H3 · H4 · H5 and the crown side, after the inflation):
           `Real.log R.x ≤ max (xTightCeilArm ε R.Hhi) (Real.log (2 · (a · g R.Hhi R.ω)))`
         where `xTightCeilArm` = `xTightCeil` + the arm's slack `18 + log 2 + H₊/10²⁰`
         (`s15ArmH_log_le_g12b`, `StrideGrade12bWalls.lean:93`: `log arm ≤ log ω + log h + H₊/10²⁰`,
         spent against (i-ω) and `log a ≤ 9`, `log h ≤ 9`);
       — `XCeil.lean:494-497`'s `hxu` at the stride builder (`StridePairReceipt.lean:2703`, the
       `+ 9` is `log a ≤ 9` at `a ≤ 8103`), through the enlargement `x ↦ max x (a·g Hhi ω)`;
  (i′) `V7RatedFormHG_g12b` carries no ceiling: after `StrideScale a R ∧` INSERT the loose ceiling,
       then (i-ω), then (i-x) tier B;
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
tight arm (`Real.log 0 = 0`).  Every line is wrapped to 100 columns by the generator itself, so
`gen_band_forms.py`'s output is byte-identical to §1.
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

/-- **⟦S-1⟧ THE TIGHT CEILING WITH THE ARM'S SLACK** — what survives hop 3's rider inflation
(`StridePairReceiptG12b.lean:610`, `g ↦ s15ArmH h δ₀ ρ + g`): `log (a · s15ArmH …) ≤ 9 + log ω +
log h + H₊/10²⁰` (`s15ArmH_log_le_g12b`) with `log ω ≤ xTightCeil ε H₊` (the (i-ω) export) and
`log h ≤ 9`, plus `log 2` for the sum's larger summand.  The shift's cost is the second `9` in the
`18`, so the definition takes NO shift argument: at C1 the operative shift is `h`, at C2 and the
crown it is `a·h` (`StridePairReceiptG12b.lean:1128`); both are covered by `log (·) ≤ 9`. -/
def xTightCeilArm (ε : ℚ) (Hhi : ℕ) : ℝ :=
  xTightCeil ε Hhi + 18 + Real.log 2 + ((Hhi : ℕ) : ℝ) / 10 ^ 20

/-! ## §1 — the six band forms, by rules (i-ω) (i-x) (i′) (ii) of the header -/

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
            Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
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
              Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
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
                Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
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
                            ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc))
                              (regimeEnlargeX R hx').Hhi) →
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          GRowsZeroGate'''_L_gk K M (A + s) Cp
                            (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc))
                              (regimeEnlargeX R hx').Hhi)) →
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          14 * Real.log (Real.log (((regimeEnlargeX R hx').Hhi : ℕ) : ℝ)) +
                            Real.log 376266
                              + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                            ≤ (theta293 - epsrf (A + s))
                                * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                            ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc))
                              (regimeEnlargeX R hx').Hhi) →
                        (∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
                          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                            * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc))
                              (regimeEnlargeX R hx').Hhi) →
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
              Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
              Real.log ((R.x : ℕ) : ℝ)
                ≤ max (xTightCeilArm ε R.Hhi) (Real.log ((2 * (a * g R.Hhi R.ω) : ℕ) : ℝ)) ∧
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
            Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
            Real.log ((R.x : ℕ) : ℝ)
              ≤ max (xTightCeilArm ε R.Hhi) (Real.log ((2 * (a * g R.Hhi R.ω) : ℕ) : ℝ)) ∧
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
        Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
        Real.log ((R.x : ℕ) : ℝ)
          ≤ max (xTightCeilArm ε R.Hhi) (Real.log ((2 * (a * g R.Hhi R.ω) : ℕ) : ℝ)) ∧
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

/-- **⟦S-1 A4⟧** the arm ceiling is nonnegative too. -/
theorem xTightCeilArm_nonneg (ε : ℚ) (hε : 0 < ε) (Hhi : ℕ) (hHhi : 4000000 ≤ Hhi) :
    0 ≤ xTightCeilArm ε Hhi := by
  unfold xTightCeilArm
  have h0 := xTightCeil_nonneg ε hε Hhi hHhi
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hH : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by positivity
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
      Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil eps R.Hhi ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ xTightCeil eps R.Hhi := by
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
  -- ⟦THE MULTIPLIER⟧ `log a ≤ 9` at `a ≤ 8103`
  have hapos : 0 < a := ha
  have haR0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
  have hlogA : Real.log ((a : ℕ) : ℝ) ≤ 9 := by
    have haR : ((a : ℕ) : ℝ) ≤ 8103 := by exact_mod_cast ha8103
    have he7 : (8103 : ℝ) ≤ Real.exp 9 := by
      have h3 : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have h4 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h5 : (2.7182818283 : ℝ) ^ (9 : ℕ) ≤ (Real.exp 1) ^ (9 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) h4.le 9
      have h6 : (8103 : ℝ) ≤ (2.7182818283 : ℝ) ^ (9 : ℕ) := by norm_num
      rw [h3]; linarith
    calc Real.log ((a : ℕ) : ℝ) ≤ Real.log (Real.exp 9) := Real.log_le_log haR0 (by linarith)
      _ = 9 := Real.log_exp 9
  -- ⟦THE CEILING AT `a·x`⟧ the landed collapse with the `+ 9` absorbed into `l`, AND the tight
  -- ceiling `hxu` itself (`xTightCeil` is `hxu`'s RHS with `u = 1/eps`, term for term)
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
  have hcancel : 30 * (u * (Real.log (Hhi : ℝ) + 9 / (30 * u)))
      = 30 * (u * Real.log (Hhi : ℝ)) + 9 := by
    field_simp
  have hxu : Real.log (((a * x : ℕ)) : ℝ)
      ≤ 30 * (u * (Real.log (Hhi : ℝ) + 9 / (30 * u)))
        + 2 * Real.log (((4 ^ ⌊eps ^ 2 * (Hhi : ℚ)⌋₊ : ℕ) : ℝ) + 1) := by
    rw [hsplit, hcancel]
    linarith [hxceil, hbr30, hlogA]
  have hPterm := xceil_flat_P heps hepsHalf hepsR hHhiR
  have hlogself : Real.log (Hhi : ℝ) + 9 / (30 * u) ≤ (Hhi : ℝ) := by
    have h1 : Real.log (Hhi : ℝ) ≤ (Hhi : ℝ) - 1 := Real.log_le_sub_one_of_pos hHhipos
    have h2 : 9 / (30 * u) ≤ 9 / 60 := by
      have h60 : (60 : ℝ) ≤ 30 * u := by linarith
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h60
    linarith
  have hfin := xceil_flat_step hu2 hHhiR hlogself hxu hPterm
  have hxceil' : Real.log (((a * x : ℕ)) : ℝ) ≤ 31 / (eps : ℝ) * (Hhi : ℝ) := by
    linarith [hfin, hbr31]
  -- ⟦THE TIGHT CEILING⟧ — `hxu` after `hcancel`, `u = 1/eps` unwound, IS `xTightCeil`
  have hxtight : Real.log (((a * x : ℕ)) : ℝ) ≤ xTightCeil eps Hhi := by
    unfold xTightCeil
    linarith [hxu, hcancel, hbr30]
  -- ⟦(i-ω)⟧ `ω ≤ x ≤ a·x`, so `log ω ≤ log (a·x) ≤ xTightCeil`
  have hxle : x ≤ a * x := Nat.le_mul_of_pos_left x hapos
  have hωtight : Real.log ((ω : ℕ) : ℝ) ≤ xTightCeil eps Hhi := by
    have hωax : ω ≤ a * x := le_trans hωx hxle
    have hω0R : (0 : ℝ) < ((ω : ℕ) : ℝ) := by
      have hω2R : (2 : ℝ) ≤ ((ω : ℕ) : ℝ) := by exact_mod_cast hω2
      linarith
    have hωaxR : ((ω : ℕ) : ℝ) ≤ (((a * x : ℕ)) : ℝ) := by exact_mod_cast hωax
    exact le_trans (Real.log_le_log hω0R hωaxR) hxtight
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
    rfl, rfl, hHlo0, ?_, hHlocap, hwidth, ?_, ?_, ?_⟩
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
  · simp only [regimeFlatEnlargeX_omega, regimeFlatEnlargeX_Hhi]
    exact hωtight
  · simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_Hhi]
    exact hxtight

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
      Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil eps R.Hhi ∧
      Real.log ((R.x : ℕ) : ℝ)
        ≤ max (xTightCeil eps R.Hhi) (Real.log ((a * g R.Hhi R.ω : ℕ) : ℝ)) := by
  obtain ⟨R, hReps, hRA, hRHlo, hstride, hRcap, hRwid, hRx, hRωtight, hRxtight⟩ :=
    chowlaRegimeFlat_exists_param_gen_ceiling_mul_b9_tight a ha ha8103 A hA eps heps heps1 Hlo₀
  have hapos : 0 < a := ha
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  -- ⟦THE ENDPOINT FLOOR⟧
  have hHhi4 : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
  have hHhiR : (4000000 : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast hHhi4
  have hHlo4 : (4000000 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast R.hHlo_floor
  -- ⟦THE `loglog` FLOOR⟧ off the design law `3.2·A ≤ loglog H₋` at `A ≥ 26`
  have hll50 : (50 : ℝ) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) := by
    have hflat : 3.2 * R.A ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) := R.hflat
    have hA26 : (26 : ℝ) ≤ R.A := R.hA
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
    hg R.Hhi R.ω ⟨hHhi4, hll50, hωgate⟩
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
  refine ⟨regimeFlatEnlargeX R hxle, hReps, hRA, hRHlo, ?_, ?_, hRcap, hRwid, ?_, ?_, ?_⟩
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
  · simp only [regimeFlatEnlargeX_omega, regimeFlatEnlargeX_Hhi]
    exact hRωtight
  · simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_omega, regimeFlatEnlargeX_Hhi]
    rcases le_total (R.x / a) (g R.Hhi R.ω) with hc | hc
    · rw [max_eq_right hc]; exact le_max_right _ _
    · rw [max_eq_left hc, hxa]; exact le_trans hRxtight (le_max_left _ _)

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
  classical
  unfold FlatHeadFormHG_g12b_band
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hhne : (h : ℝ) ≠ 0 := ne_of_gt hhR
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- ⟦THE LEAF NUMERALS, PINNED⟧ `log 4 = 2·log 2`, both `d9` bounds on `log 2`
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  obtain ⟨cD3, hcD3def⟩ : ∃ c : ℝ, c = 1 / 4 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ c : ℝ, c = (h : ℝ) * (1 + 2 * (2 * Real.log 4)) := ⟨_, rfl⟩
  have hcD3 : 0 < cD3 := by rw [hcD3def]; norm_num
  have hLpos : (0 : ℝ) < 1 + 8 * Real.log 2 := by linarith
  have hLne : (1 : ℝ) + 8 * Real.log 2 ≠ 0 := ne_of_gt hLpos
  have hCval : C = (h : ℝ) * (1 + 8 * Real.log 2) := by rw [hCdef, hlog4eq]; ring
  have hC : 0 < C := by rw [hCval]; positivity
  -- ⟦THE PIN⟧ `ε := 1/(500·h)`
  obtain ⟨ε, hεdef⟩ : ∃ e : ℚ, e = 1 / (500 * (h : ℚ)) := ⟨_, rfl⟩
  have hεR : ((ε : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) := by rw [hεdef]; push_cast; ring
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by rw [hεR]; positivity
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεQ1 : ε ≤ 1 / 2 := by
    have hhQ : (1 : ℚ) ≤ (h : ℚ) := by exact_mod_cast hh
    rw [hεdef]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  -- ⟦THE MINT, READ BOTH WAYS⟧ `δ₀ = 1/(128000·2^12·h²·(1 + 8·log 2))`
  have hval : cD3 / (16 * C) * (ε : ℝ) / 4 / 2 ^ 12
      = 1 / (128000 * 2 ^ 12 * (h : ℝ) ^ 2 * (1 + 8 * Real.log 2)) := by
    rw [hcD3def, hCval, hεR]
    field_simp
    ring
  have hsq0 : (0 : ℝ) ≤ (h : ℝ) ^ 2 := sq_nonneg _
  have hδ₀ge : (1 : ℝ) / (838400 * 2 ^ 12 * (h : ℝ) ^ 2)
      ≤ cD3 / (16 * C) * (ε : ℝ) / 4 / 2 ^ 12 := by
    rw [hval]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hnum : 128000 * (1 + 8 * Real.log 2) ≤ 838400 := by linarith
    nlinarith [hnum, hsq0]
  have hδ₀le : cD3 / (16 * C) * (ε : ℝ) / 4 / 2 ^ 12
      ≤ 1 / (837782 * 2 ^ 12 * (h : ℝ) ^ 2) := by
    rw [hval]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hnum : (837782 : ℝ) ≤ 128000 * (1 + 8 * Real.log 2) := by linarith
    nlinarith [hnum, hsq0]
  -- ⟦THE COUNT HOOK AT THE PIN⟧ carrying `K ≤ 2^539`
  obtain ⟨K, hK, hKb, H₀xi, _hH₀xi2, hxi⟩ := hcount
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = cD3 * (ε : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hcD3 hεR0) (by positivity)
  -- ⟦THE HEAD'S OWN FLOOR⟧ the count hook's alone — the door-head has no tail
  obtain ⟨Hopq, hOpqdef⟩ : ∃ n : ℕ, n = H₀xi := ⟨_, rfl⟩
  refine ⟨ε, K, cD3 / (16 * C) * (ε : ℝ) / 4 / 2 ^ 12, β, Hopq, hεQpos, hK, hKb,
    div_pos (div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num))
      (by positivity),
    hεdef.ge, hδ₀ge, hβpos, ?_⟩
  -- ⟦THE HOIST⟧ as in the head
  intro A hA26 _hAge
  obtain ⟨F, hFdef⟩ : ∃ n : ℕ, n = max Hopq (budgetFloorFlat (ε : ℝ) β A) := ⟨_, rfl⟩
  refine ⟨max (flatDesignFloor A) (max F (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), by rw [hFdef], ?_⟩
  intro a extraFloor U1floor g₅ ha ha8103 hg₅
  obtain ⟨Rf, hReps, _hRA, hRHlo, hRg, hstride, _hRcapEq, hRwid, hRx, hRωtight, hRxtight⟩ :=
    chowlaRegimeFlat_exists_param_head_xceil_mul_b9_tight a ha ha8103 A hA26 ε hεQpos hεQ1
      (max F (max extraFloor U1floor)) g₅ hg₅
  have hFlo : F ≤ Rf.Hlo := le_trans (le_max_left _ _) hRHlo
  have hxiHlo : H₀xi ≤ Rf.Hlo := by
    rw [hFdef, hOpqdef] at hFlo
    exact le_trans (le_max_left _ _) hFlo
  -- ⟦THE COUNT GATE⟧ at this head's own `ε`, reused for the receipt's own conjunct
  have hcountR : ∀ (H' : ℕ) [NeZero H'], Rf.Hlo ≤ H' → H' ≤ Rf.Hhi →
      ((Xi Rf.eps H').card : ℝ) ≤ K := by
    intro H' _ hlo' _
    rw [hReps, hεdef]
    exact hxi H' (le_trans hxiHlo hlo')
  refine ⟨Rf.toChowlaRegime, hReps,
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, hstride, hRx,
    hRωtight, hRxtight, hcountR, fun _ => hRwid, ?_, ?_⟩
  · -- ⟦THE CAP⟧ the flat base equation, shuffled onto the consumer's floors
    rw [_hRcapEq]
    exact flatCapH_shuffle _ _ _ _ _
  · -- ⟦THE DOOR, HANDED OUT INSTEAD OF SPENT⟧ at every `x'` in the band, with the pin and the
    -- count beside it — both `rfl`-transported through `regimeEnlargeX` (it reads no field but
    -- `Hlo`, `Hhi`, `eps`)
    intro x' hx' _hadvd _hxceil' ρ hρpos hρ hdoor
    refine ⟨?_, ⟨K, hK, hKb, ?_⟩, ρ, hρpos, le_trans hρ hδ₀le, hdoor⟩
    · simp only [regimeEnlargeX_eps]
      rw [hReps, hεdef]
    · simp only [regimeEnlargeX_Hlo, regimeEnlargeX_Hhi, regimeEnlargeX_eps]
      exact hcountR

/-- **⟦S-1 H0→H1⟧** `flat_roadExit_generic_h_g12b` (`:320`) at the band forms. -/
theorem flat_roadExit_generic_h_g12b_band (h : ℕ) (hh : 0 < h) (_hh9 : Real.log (h : ℝ) ≤ 9)
    (Xi : XiFamily)
    (harcXi : ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
      ∀ ξ ∈ Xi eps H, NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (P : ChowlaRegime → Prop) (hhead : FlatHeadFormHG_g12b_band h Xi P) :
    FlatRoadExitFormHG_g12b_band h P := by
  obtain ⟨Cg, hCg, hCgle, hreg⟩ := m4_second_road_L2_Set_gk_flatRoot_L_khoist h hh Xi harcXi
  obtain ⟨ε, Kb, δ₀, β, Hopq, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, hhd0⟩ := hhead
  obtain ⟨H₀, hH₀⟩ := hreg ε hε
  refine ⟨Cg, ε, Kb, δ₀, β, max Hopq H₀, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge
  obtain ⟨Hcap, hCapEq, hhd⟩ := hhd0 A (by linarith) hAge
  refine ⟨max Hcap H₀, by rw [hCapEq]; exact flatRootCapH_arc_k _ _ _ _ _, ?_⟩
  intro a U1floor g ha ha8103 hg
  obtain ⟨R, hReps, hRextra, hRU1, hRg, hstride, hRx, hRωtight, hRxtight, hcount, hRtow, hRcap,
    hR⟩ := hhd a H₀ U1floor g ha ha8103 hg
  refine ⟨R, hReps, hRU1, hRg, hstride, hRx, hRωtight, hRxtight, hRtow, le_trans hRcap (by omega),
    ?_⟩
  intro x' hx' hadvd hxc δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1
    hG2 harc3 hdgate hdrift hceil hbudget hrow
  have hReps' : (regimeEnlargeX R hx').eps = ε := by simp only [regimeEnlargeX_eps]; exact hReps
  have hRextra' : H₀ ≤ (regimeEnlargeX R hx').Hlo := by
    simp only [regimeEnlargeX_Hlo]; exact hRextra
  have hdoor := hH₀ K (regimeEnlargeX R hx') hReps' hRextra' δ Bceil Kb RS RSan RStr Braw M k j₀
    hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3 hdgate hdrift hceil hcount hKb.le hrow
  refine hR x' hx' hadvd hxc δ₀ hδ₀ le_rfl ?_
  intro H _ hlo hhi
  exact le_trans (hdoor H hlo hhi) hbudget

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
  exact flat_v7_generic_h_g12b_band h hh hh9 P
    (fun Awin hband => flat_kswin_generic_h_g12b_band h hh hh9 Awin hband P
      (flat_conditional_generic_h_g12b_band h hh hh9 Awin hband P
        (flat_capstone_generic_h_g12b_band h hh hh9 Awin hband P
          (flat_roadExit_generic_h_g12b_band h hh hh9 Xi harcXi P hhead)))) A₀

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
        Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
        Real.log ((R.x : ℕ) : ℝ)
          ≤ max (xTightCeilArm ε R.Hhi) (Real.log ((2 * (a * g R.Hhi R.ω) : ℕ) : ℝ)) ∧
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
        Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
        Real.log ((R.x : ℕ) : ℝ)
          ≤ max (xTightCeilArm ε R.Hhi) (Real.log ((2 * (a' * g R.Hhi R.ω) : ℕ) : ℝ)) ∧
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
the AFFINE scale `y = x'/a`: the band's BOTTOM `x₀` carries the tight ceiling WITH THE ARM'S
SLACK (hop 3's inflation; at the crown's own `g ≡ 0` the MAX collapses), the width the bare one,
the band's ROOF is the loose ceiling on `a·y`, and at every `y` in the
band
the affine door holds at an affine regime with `Ra.x = y`, the SAME `ω₀`, the SAME `Hhi₀`.  This is
the object S-3 consumes: D12's `hwin` at fixed `ω₀` over `x ∈ [x₀, M]`. -/
theorem mrtUniformityXiL2AffW_holds_flat_stride_g12b_band (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hba : b < a) (hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
      ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ (x₀ ω₀ Hhi₀ : ℕ), 2 ≤ x₀ ∧ 8 ≤ ω₀ ∧ 4000000 ≤ Hhi₀ ∧
        Real.log ((ω₀ : ℕ) : ℝ) ≤ xTightCeil ε Hhi₀ ∧
        Real.log ((x₀ : ℕ) : ℝ) ≤ xTightCeilArm ε Hhi₀ ∧
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

/-! ## §6 — the conservativity controls K1–K7: each of the six band forms and the crown band implies
its landed source (instantiate `x' := R.x`, resp. `y := x₀`) -/

/-- **⟦S-1 K1⟧** the band head form is a conservative extension of `FlatHeadFormHG_g12b`. -/
theorem flatHeadFormHG_g12b_of_band (h : ℕ) (Xi : XiFamily) (P : ChowlaRegime → Prop)
    (hb : FlatHeadFormHG_g12b_band h Xi P) : FlatHeadFormHG_g12b h Xi P := by
  obtain ⟨ε, K, δ₀, β, Hopq, hε, hK, hKb, hδ₀, hεpin, hδpin, hβ, hbody⟩ := hb
  refine ⟨ε, K, δ₀, β, Hopq, hε, hK, hKb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro A hA hAge
  obtain ⟨Hcap, hCap, hmain⟩ := hbody A hA hAge
  refine ⟨Hcap, hCap, ?_⟩
  intro a extraFloor U1floor g ha ha8103 hg
  obtain ⟨R, hReps, hextra, hU1, hRg, hstride, hxceil, -, -, hcount, hwid, hcap, hband⟩ :=
    hmain a extraFloor U1floor g ha ha8103 hg
  refine ⟨R, hReps, hextra, hU1, hRg, hstride, hxceil, hcount, hwid, hcap, ?_⟩
  intro ρ hρ hρle hdoor
  have h := hband R.x (le_refl _) hstride.1 hxceil ρ hρ hρle
    (by rw [regimeEnlargeX_self]; exact hdoor)
  rwa [regimeEnlargeX_self] at h

/-- **⟦S-1 K4⟧** the band road-exit form is a conservative extension of its source. -/
theorem flatRoadExitFormHG_g12b_of_band (h : ℕ) (P : ChowlaRegime → Prop)
    (hb : FlatRoadExitFormHG_g12b_band h P) : FlatRoadExitFormHG_g12b h P := by
  obtain ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, hbody⟩ := hb
  refine ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro K A hA hAge
  obtain ⟨Hcap, hCap, hmain⟩ := hbody K A hA hAge
  refine ⟨Hcap, hCap, ?_⟩
  intro a U1floor g ha ha8103 hg
  obtain ⟨R, hReps, hU1, hRg, hstride, hxceil, -, -, hRtow, hcap, hband⟩ :=
    hmain a U1floor g ha ha8103 hg
  refine ⟨R, hReps, hU1, hRg, hstride, hxceil, hRtow, hcap, ?_⟩
  have hh := hband R.x (le_refl _) hstride.1 hxceil
  rwa [regimeEnlargeX_self] at hh

/-- **⟦S-1 K5⟧** the band capstone form is a conservative extension of its source. -/
theorem flatCapstoneFormHG_g12b_of_band (h : ℕ) (Awin : ℝ) (P : ChowlaRegime → Prop)
    (hb : FlatCapstoneFormHG_g12b_band h Awin P) : FlatCapstoneFormHG_g12b h Awin P := by
  obtain ⟨Cg, ε, Kc, δ₀, β, x₀, Hopq, Mfl, hCg, hε, hKc, hδ₀, hMfl, hCgle, hεpin, hδpin, hKcb,
    hMflb, hβ, hbody⟩ := hb
  refine ⟨Cg, ε, Kc, δ₀, β, x₀, Hopq, Mfl, hCg, hε, hKc, hδ₀, hMfl, hCgle, hεpin, hδpin, hKcb,
    hMflb, hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hK⟩ := hbody K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA hAge
  obtain ⟨Hcap, hCap, hmain⟩ := hK A hA hAge
  refine ⟨Hcap, hCap, ?_⟩
  intro Cp hCp a U1floor g ha ha8103 hg
  obtain ⟨R, hReps, hU1, hRg, hstride, hxceil, -, -, hRtow, hcap, hband⟩ :=
    hmain Cp hCp a U1floor g ha ha8103 hg
  refine ⟨R, hReps, hU1, hRg, hstride, hxceil, hRtow, hcap, ?_⟩
  have hh := hband R.x (le_refl _) hstride.1 hxceil
  rwa [regimeEnlargeX_self] at hh

/-- **⟦S-1 K6⟧** the band conditional form is a conservative extension of its source. -/
theorem flatConditionalFormHG_g12b_of_band (h : ℕ) (Awin : ℝ) (P : ChowlaRegime → Prop)
    (hb : FlatConditionalFormHG_g12b_band h Awin P) : FlatConditionalFormHG_g12b h Awin P := by
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl, hCgle, hεpin, hδpin, hKcb,
    hMflb, hβ, hbody⟩ := hb
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl, hCgle, hεpin, hδpin, hKcb,
    hMflb, hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hK⟩ := hbody K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA hAge
  obtain ⟨Hcap, hCap, hmain⟩ := hK A hA hAge
  refine ⟨Hcap, hCap, ?_⟩
  intro a U1floor g ha ha8103 hg hU
  obtain ⟨R, hReps, hHlo, hRg, hstride, hxceil, -, -, hRtow, hband⟩ :=
    hmain a U1floor g ha ha8103 hg hU
  refine ⟨R, hReps, hHlo, hRg, hstride, hxceil, hRtow, ?_⟩
  have hh := hband R.x (le_refl _) hstride.1 hxceil
  rwa [regimeEnlargeX_self] at hh

/-- **⟦S-1 K7⟧** the band Kswin form is a conservative extension of its source. -/
theorem flatKswinFormHG_g12b_of_band (h : ℕ) (Awin : ℝ) (P : ChowlaRegime → Prop)
    (hb : FlatKswinFormHG_g12b_band h Awin P) : FlatKswinFormHG_g12b h Awin P := by
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl, hCgle,
    hεpin, hδpin, hMflb, hβ, hCq, hcs, hcsf, hT₀, hKq, hKs, hC, hC40, hbody⟩ := hb
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl, hCgle,
    hεpin, hδpin, hMflb, hβ, hCq, hcs, hcsf, hT₀, hKq, hKs, hC, hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hK⟩ := hbody K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA hAwin hAge hKw
  obtain ⟨hwit, hmain⟩ := hK A hA hAwin hAge hKw
  refine ⟨hwit, ?_⟩
  intro hx0 hopq hT hKs U1floor hU hUceil a g ha ha8103 hg
  obtain ⟨R, hReps, hHlo, hRg, hstride, hxceil, -, -, hRtow, hdes, hwin, hband⟩ :=
    hmain hx0 hopq hT hKs U1floor hU hUceil a g ha ha8103 hg
  refine ⟨R, hReps, hHlo, hRg, hstride, hxceil, hRtow, hdes, hwin, ?_⟩
  have hh := hband R.x (le_refl _) hstride.1 hxceil
  rwa [regimeEnlargeX_self] at hh

/-- **⟦S-1 K2⟧** the band V7-rated form is a conservative extension of `V7RatedFormHG_g12b`. -/
theorem v7RatedFormHG_g12b_of_band (h : ℕ) (P : ChowlaRegime → Prop) (A₀ : ℝ)
    (hb : V7RatedFormHG_g12b_band h P A₀) : V7RatedFormHG_g12b h P A₀ := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCq, hcs, hcsf, hT₀, hKq, hKs, hC, hC40, hCgle, hεpin, hδpin, hMflb, hβ, hA162, hA₀A,
    hbody⟩ := hb
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCq, hcs, hcsf, hT₀, hKq, hKs, hC, hC40, hCgle, hεpin, hδpin, hMflb, hβ, hA162, hA₀A, ?_⟩
  intro U1floor a g hU hUceil ha ha8103 hg
  obtain ⟨R, hReps, hHlo, hRg, hstride, hxceil, -, -, hRtow, hdes, hwin, hband⟩ :=
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
  obtain ⟨ε, A, hε, hεpin, hεeq, hA162, hA₀A, x₀, ω₀, Hhi₀, -, -, -, -, -, hx₀ceil, hband⟩ :=
    mrtUniformityXiL2AffW_holds_flat_stride_g12b_band a b h ha hh hba hah9 A₀
  obtain ⟨Ra, hRa, hRb, hReps, -, -, -, hHlo, hdes, hgrade⟩ := hband x₀ le_rfl hx₀ceil
  exact ⟨ε, A, hε, hεpin, hεeq, hA162, hA₀A, Ra, hRa, hRb, hReps, hHlo, hdes, hgrade⟩

end Salt.MR

end
