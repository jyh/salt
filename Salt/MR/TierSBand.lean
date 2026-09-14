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
  have hh14 : Real.log (h : ℝ) ≤ 14 := by linarith
  obtain ⟨Cg, ε, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hKcb, hδ₀, hεpin, hδpin, hβ, hroadU⟩ :=
    hroad
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, hKcb,
    (fun A hA162 hAw => flatDoorM_gradeFloor_win hA162 hCband0 (by linarith)),
    hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hfuse⟩ :=
    m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling_kwide_14 h hh hh14 K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hroad0⟩ := hroadU K A hA26 hAge
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp a U1floor g ha ha8103 hg
  obtain ⟨R, hReps, hU1, hRg, hstride, hRx, hRωtight, hRxtight, hRtow, hRcap, hR⟩ :=
    hroad0 a (max U1floor (max arcFloor36 loglogFloor50)) g ha ha8103 hg
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hstride, hRx, hRωtight, hRxtight,
    hRtow, by omega, ?_⟩
  intro x' hx' hadvd hxc M hMfloor hKw
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit K M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the absorbed floor⟧ at `h` only `loglogFloor50` is read (`arc36_of_regime_h_14`)
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseLH h (regimeEnlargeX R hx') M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRowH_L_gk h K (regimeEnlargeX R hx') M
      (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) :=
    hfuse Cp hCp (regimeEnlargeX R hx') M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot (regimeEnlargeX R hx') C₁ M₀ hbandbase) harith
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
  refine hR x' hx' hadvd hxc δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) (RSanDoorRhoH ρ h)
    (fun H => (h : ℝ) ^ 7 * rStrWitness H)
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
          (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRhoH_nonneg hρpos.le h H)
    (fun H => rStrWitness_mul_nonneg h H) ?_ hgate4 (fun H _ _ => rStrWitness_G1_h h H) ?_
    (arc36_of_regime_h_14 hh hh14 hllfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
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
    have hlo' : R.Hlo ≤ H := hlo
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

/-- **⟦S-1 H2→H3⟧** `flat_conditional_generic_h_g12b` (`:504`) at the band forms. -/
theorem flat_conditional_generic_h_g12b_band (h : ℕ) (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9)
    (Awin : ℝ) (_hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hcap : FlatCapstoneFormHG_g12b_band h Awin P) :
    FlatConditionalFormHG_g12b_band h Awin P := by
  obtain ⟨Cg, ε, Kc, δ₀, β, x₀, Hopq, Mfl, hCg, hε, hKc,
    hδ₀, hMfl, hCgle, hεpin, hδpin, hKcb, hMflb,
    hβ, hcapU⟩ := hcap
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcapK⟩ := hcapU K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapK A hA26 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro a U1floor g ha ha8103 hg hU
  have hapos : 0 < a := ha
  have haR0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
  have hlogA : Real.log ((a : ℕ) : ℝ) ≤ 9 := by
    have he9 : (8103 : ℝ) ≤ Real.exp 9 := by
      have h3 : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have h4 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h5 : (2.7182818283 : ℝ) ^ (9 : ℕ) ≤ (Real.exp 1) ^ (9 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) h4.le 9
      have h6 : (8103 : ℝ) ≤ (2.7182818283 : ℝ) ^ (9 : ℕ) := by norm_num
      rw [h3]; linarith
    have haR : ((a : ℕ) : ℝ) ≤ 8103 := by exact_mod_cast ha8103
    calc Real.log ((a : ℕ) : ℝ) ≤ Real.log (Real.exp 9) := Real.log_le_log haR0 (by linarith)
      _ = 9 := Real.log_exp 9
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦THE ONE GENUINE ESTIMATE, SPENT AT SHIFT `h`⟧ as in the source, at the `+ 9` split
  have hh1R : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hεR : (1 : ℝ) / (500 * (h : ℝ)) ≤ (ε : ℝ) := by
    have hq := (Rat.cast_le (K := ℝ)).mpr hεpin
    rwa [show (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) by
      push_cast; ring] at hq
  have hεpos : (0 : ℝ) < (ε : ℝ) := by
    have hb : (0 : ℝ) < 1 / (500 * (h : ℝ)) := by positivity
    linarith
  have hg' : XCeilRider ε
      (fun Hhi ω => a * (s15ArmH h δ₀ ρ Hhi ω + g Hhi ω)) := by
    intro Hhi ω hgate
    obtain ⟨hH4, hll, hωw⟩ := hgate
    have hHhiR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hH4
    -- ⟦THE MARGIN⟧ `ε ≥ 1/(500h) > 0` ⟹ `ε² ≥ 1/(250000h²)`
    have hε2 : (1 : ℝ) / (250000 * (h : ℝ) ^ 2) ≤ (ε : ℝ) ^ 2 := by
      have hsq : (1 : ℝ) / (500 * (h : ℝ)) * (1 / (500 * (h : ℝ))) ≤ (ε : ℝ) * (ε : ℝ) :=
        mul_le_mul hεR hεR (by positivity) (le_of_lt hεpos)
      have he : (1 : ℝ) / (500 * (h : ℝ)) * (1 / (500 * (h : ℝ)))
          = 1 / (250000 * (h : ℝ) ^ 2) := by
        have hne : (h : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      nlinarith [hsq, he.le, he.ge]
    have hεsq : ((Hhi : ℕ) : ℝ) / (250000 * (h : ℝ) ^ 2)
        ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := by
      have hH0 : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by positivity
      have hm := mul_le_mul_of_nonneg_right hε2 hH0
      calc ((Hhi : ℕ) : ℝ) / (250000 * (h : ℝ) ^ 2)
          = 1 / (250000 * (h : ℝ) ^ 2) * ((Hhi : ℕ) : ℝ) := by ring
        _ ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := hm
    -- ⟦THE ARM⟧ wave H1's re-cut, at the `h` lane's own `δ₀` pin at `2^12`
    have harm : Real.log ((s15ArmH h δ₀ ρ Hhi ω : ℕ) : ℝ)
        ≤ Real.log ((ω : ℕ) : ℝ) + Real.log (h : ℝ) + ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
      rw [hρdef, hδsdef]
      exact s15ArmH_log_le_g12b hh hh9 hδ₀ hδpin hKc hKcb hH4 hll
    -- ⟦H2a WORD 4⟧ the split at `+ 9`
    have hsplit := xceil_arm_split_mul_h_b9 hh hh9 hH4 hll
    have hgb := hg Hhi ω ⟨hH4, hll, hωw⟩
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have harm' : Real.log ((s15ArmH h δ₀ ρ Hhi ω : ℕ) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - Real.log 2 - 9 := by linarith
    have hgb' : Real.log ((g Hhi ω : ℕ) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - Real.log 2 - 9 := by
      have hlogh : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_natCast_nonneg h
      have hH20 : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by positivity
      linarith
    have hsum : Real.log (((s15ArmH h δ₀ ρ Hhi ω + g Hhi ω : ℕ)) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - 9 :=
      le_trans (xt_log_add_le harm' hgb') (by linarith)
    -- ⟦THE MULTIPLIER⟧ `log(a·(arm + g)) = log a + log(arm + g) ≤ 9 + (31/ε·H₊ − 9)`
    have hprod : Real.log (((a * (s15ArmH h δ₀ ρ Hhi ω + g Hhi ω) : ℕ)) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos (a * (s15ArmH h δ₀ ρ Hhi ω + g Hhi ω)) with hz | hp
      · rw [hz]
        simp only [Nat.cast_zero, Real.log_zero]
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
  obtain ⟨R, hReps, hU1, hRg, hstride, hRx, hRωtight, hRxtight, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl a U1floor (fun Hhi ω => s15ArmH h δ₀ ρ Hhi ω + g Hhi ω) ha ha8103 hg'
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
  refine ⟨R, hReps, hHlo, hRgg, hstride, hRx, hRωtight, ?_, hRtow, ?_⟩
  · -- ⟦S-1 (i-x) TIER A → TIER B⟧ the rider inflation, paid at the arm's own slack.
    -- `log a ≤ 9` and `log h ≤ 9` make the `18`; the doubling makes the `log 2`; the arm's
    -- residual makes the `H₊/10²⁰`; `log ω ≤ xTightCeil` is the (i-ω) export.
    have hH4R : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
    have hΛR : 50 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) :=
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)).2
    have harmR : Real.log ((s15ArmH h δ₀ ρ R.Hhi R.ω : ℕ) : ℝ)
        ≤ Real.log ((R.ω : ℕ) : ℝ) + Real.log (h : ℝ) + ((R.Hhi : ℕ) : ℝ) / 10 ^ 20 := by
      rw [hρdef, hδsdef]
      exact s15ArmH_log_le_g12b hh hh9 hδ₀ hδpin hKc hKcb hH4R hΛR
    have hlogmono : ∀ {m n : ℕ}, m ≤ n → Real.log ((m : ℕ) : ℝ) ≤ Real.log ((n : ℕ) : ℝ) := by
      intro m n hmn
      rcases Nat.eq_zero_or_pos m with hm0 | hm
      · rw [hm0]
        simpa using Real.log_natCast_nonneg n
      · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmn)
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hH20 : (0 : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) / 10 ^ 20 := by positivity
    have hTC0 : 0 ≤ xTightCeil ε R.Hhi := xTightCeil_nonneg ε hε R.Hhi hH4R
    have hTCA0 : 0 ≤ xTightCeilArm ε R.Hhi := xTightCeilArm_nonneg ε hε R.Hhi hH4R
    have hArmCeil : xTightCeil ε R.Hhi ≤ xTightCeilArm ε R.Hhi := by
      unfold xTightCeilArm; linarith
    rcases le_max_iff.mp hRxtight with hA | hB
    · exact le_trans (le_trans hA hArmCeil) (le_max_left _ _)
    · rcases le_total (g R.Hhi R.ω) (s15ArmH h δ₀ ρ R.Hhi R.ω) with hge | hgg
      · -- ⟦THE ARM CASE⟧ the larger summand is the arm: double it and spend the slack
        refine le_trans hB (le_trans ?_ (le_max_left _ _))
        rcases Nat.eq_zero_or_pos (a * (s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω)) with hz | hp
        · rw [hz]
          simpa using hTCA0
        · have hsne : (0 : ℝ)
              < ((s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω : ℕ) : ℝ) := by
            have hs0 : 0 < s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω :=
              Nat.pos_of_ne_zero (fun hc => hp.ne' (by rw [hc, Nat.mul_zero]))
            exact_mod_cast hs0
          have hcast : (((a * (s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω) : ℕ)) : ℝ)
              = ((a : ℕ) : ℝ) * ((s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω : ℕ) : ℝ) := by
            push_cast; ring
          have hsum : Real.log (((s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω : ℕ)) : ℝ)
              ≤ Real.log 2 + Real.log ((s15ArmH h δ₀ ρ R.Hhi R.ω : ℕ) : ℝ) :=
            xt_log_add_le le_rfl (hlogmono hge)
          rw [hcast, Real.log_mul (ne_of_gt haR0) (ne_of_gt hsne)]
          unfold xTightCeilArm
          linarith [hRωtight]
      · -- ⟦THE `g` CASE⟧ the larger summand is `g`: `a·(arm + g) ≤ 2·(a·g)` in ℕ
        refine le_trans hB (le_trans ?_ (le_max_right _ _))
        refine hlogmono ?_
        have hle : s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω ≤ 2 * g R.Hhi R.ω := by omega
        calc a * (s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω)
            ≤ a * (2 * g R.Hhi R.ω) := Nat.mul_le_mul_left a hle
          _ = 2 * (a * g R.Hhi R.ω) := by ring
  intro x' hx' hadvd hxc M hKw hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire x' hx' hadvd hxc M hsel.mfloor hKw
  intro hcapx
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hRarm' : s15ArmH h δ₀ ρ R.Hhi R.ω ≤ x' := le_trans hRarm hx'
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ x' :=
    le_trans (s15ArmH_demoted h δ₀ ρ R.Hhi R.ω) hRarm'
  have hhω : (0 : ℝ) ≤ (h : ℝ) * (R.ω : ℝ) := by positivity
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 ((h : ℝ) * (R.ω : ℝ)) ρ H ≤ ((x' : ℕ) : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hhω ?_ hhi) (s15ArmH_rho hRarm')
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family at the inflated socket, arm read at `h·ω`
  have harith := s15_doorArithFrameRho_L_familyH'' (C₁ := fun _ : ℕ => (1 : ℝ)) hh hsel.hM
    hρ0 hρ1 hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧ — the register and its bridges are SOCKET-BLIND
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ
      (regimeEnlargeX R hx') M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by simp only [regimeEnlargeX_Hhi]; linarith))
  -- ⟦slot 3⟧ H2a word 6's OUTER step, over the `h`-free family, with the `36` in the gate
  have hj0raw : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * max 1 (arcDen 12 H)) + 36 ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    have hgate := s13_g2_jfloor_of_MSelect'_L_gk_shift36 K (by linarith) hS
    have hbase := s13_g2_jfloor_gen (R := regimeEnlargeX R hx')
      (F := ((doorRowFloorL M : ℕ) : ℝ) - 36) le_rfl
      (by simp only [regimeEnlargeX_Hhi]; linarith)
    intro H hlo hhi
    linarith [hbase H hlo hhi]
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 (regimeEnlargeX R hx') ρ (fun _ => (1 : ℝ)))
    (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount (regimeEnlargeX R hx').ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_of_MSelect'_L_gk_h_b9 hh hh9 hj0raw)
    (s13_gate8_L_gk_h_b9 hh hh9 le_rfl (by simp only [regimeEnlargeX_Hhi]; linarith)
      hsel.gRows)
    (s13_smallGradeFits_of_halfWindow_L_gk_h_b9 hh hh9 hρ0 hρ1 hfl hsel.half)
    (fun H L q j A s hb => doorBaseFrame_at_socket_LH hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorLH_gk_b9 K hh hh9 hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flatH_b9 hh hh9 hfl hb hlam50 htow hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flatH_b9 hh hh9 hfl hb hρ0 hlam50 htow hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flatH_b9 hh hh9 hfl hb hρ0 hlam50 htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM
        (s15_block_at_socketH_L_gk_b9 K hh hh9 hb (hHreg H hb.1 hb.2.1) hsel.blk)
        hb.2.2.2.2.2.2.1)
    hcapx
    (doorBandBase_family'H_L_gk_b9 K hh hh9 hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (s15ArmH_rho hRarm') harith hsel.x0M (fun _ => le_rfl) hgrade
      (fun H L q j A s hb =>
        s15_block_at_socketH_L_gk_b9 K hh hh9 hb (hHreg H hb.1 hb.2.1) hsel.blk))
    harith

/-- **⟦S-1 H3→H4⟧** `flat_kswin_generic_h_g12b` (`:703`) at the band forms. -/
theorem flat_kswin_generic_h_g12b_band (h : ℕ) (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9)
    (Awin : ℝ) (_hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hcond : FlatConditionalFormHG_g12b_band h Awin P) :
    FlatKswinFormHG_g12b_band h Awin P := by
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, hcondU⟩ := hcond
  obtain ⟨_Ct0, -, -, hcond0⟩ := hcondU 0
  -- ⟦THE CROSSING CONSTANTS, HOISTED ABOVE THE LEVER⟧ — §11.4's windowed twin
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40,
    hsupplyU⟩ := s15_crossing_supplied_LH_gk_ceiling_sharpT0_khoist_csfree_kswin_b9 hh hh9
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond0 (max 162 (budgetAFlat (ε : ℝ) β)) (le_max_left _ _) (le_max_right _ _)
  -- the `ε`-probe's own `g ≡ 0` obeys the strict rider trivially
  have hzero : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := by
    intro Hhi ω hgate
    obtain ⟨-, -, hωw⟩ := hgate
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [Real.log_natCast_nonneg ω]
  obtain ⟨R0, hR0eps, -, -, -, -, -, -, -⟩ :=
    hbody0 1 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) le_rfl (by norm_num)
      hzero le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have hεR : (1 : ℝ) / (500 * (h : ℝ)) ≤ (ε : ℝ) := by
    have hq := (Rat.cast_le (K := ℝ)).mpr hεpin
    rwa [show (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) by
      push_cast; ring] at hq
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  have hsupply := hsupplyU K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA26 hAwin hAge hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge
  refine ⟨fun hopq => flat_witFloor_eq_designBase_h_b9 hh hh9 hA26 hβ hεR hε2 hε hεpin hAge hopq,
    ?_⟩
  intro hx0win hopq hT₀ hKsw U1floor hU hUceil a g ha ha8103 hg
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
  obtain ⟨R, hReps, hHlo, hRg, hstride, hRx, hRωtight, hRxtight, hRtow, hfire⟩ :=
    hbody a U1floor g ha ha8103 hg (le_trans (flatCap_le_flatWitFloor hCapLe) hU)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]
    exact le_trans (flatWitFloor_design ε β A Hopq) hUll
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo]; exact hUceil
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hstride, hRx, hRωtight, hRxtight, hRtow, hdes, hwin, ?_⟩
  intro x' hx' hadvd hxc hcof hcapsc
  -- ⟦THE REGISTER, SUPPLIED⟧ at the flat design modulus, at every scale of the band
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have hhQ : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  have heps : (1 : ℚ) / (2 ^ 9 * (h : ℚ)) ≤ R.eps := by
    rw [hReps]
    have hle : (1 : ℚ) / (2 ^ 9 * (h : ℚ)) ≤ 1 / (500 * (h : ℚ)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [hhQ]
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact le_trans (flatWitFloor_log_ge hA26) hUlog
  -- ⟦THE BRIDGE⟧ the `A`-scoped window becomes §11.4's regime-scoped one at the flat floor
  have hKswR : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16 := by linarith
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win_h_g12b (R := regimeEnlargeX R hx')
    hA26 K hKw hh hh9 hδ₀ hδpin hKc hKcb hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win heps hlo hwin
  -- ⟦THE CROSSING, SUPPLIED⟧ the block floor off the register's own `blk` line
  have hfl : loglogFloor50 ≤ R.Hlo := by
    rw [hHlo]; exact le_trans (flatWitFloor_ll _ _ _ _) hU
  have hblk : ∀ H L q j Aw s : ℕ,
      SocketBaseLH h (regimeEnlargeX R hx') (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socketH_L_gk_b9 K hh hh9 hb
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire x' hx' hadvd hxc (flatDoorM A) hKw hsel
    (hsupply hKqb (regimeEnlargeX R hx') (flatDoorM A) hM1 hfl hKswR
      (by
        simp only [regimeEnlargeX_Hlo]
        rw [hHlo]
        refine le_trans hT₀ (Real.exp_le_exp.mpr ?_)
        have hs : Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ)
            ≤ Real.sqrt ((U1floor : ℕ) : ℝ) := Real.sqrt_le_sqrt hUR
        linarith)
      hblk hcof hcapsc)

/-- **⟦S-1 H4→H5⟧** `flat_v7_generic_h_g12b` (`:807`) at the band forms.  The two suppliers it fires
at `R` — `cofkR_cofactorSupply_L_gk_rated_h_b9` and `s16_baseScaleCap96_LH_at_klevF_b9 … hxceil
hwin` —
are fired at `regimeEnlargeX R hx'`, the second reading its ceiling FROM THE BAND HYPOTHESIS. -/
theorem flat_v7_generic_h_g12b_band (h : ℕ) (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9)
    (P : ChowlaRegime → Prop)
    (hk : ∀ Awin : ℝ, S16BandLaneCBoundedLH_winU h Awin → FlatKswinFormHG_g12b_band h Awin P)
    (A₀ : ℝ) :
    V7RatedFormHG_g12b_band h P A₀ := by
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ :=
    cofkR_cofactorSupply_L_gk_rated_h_b9 h hh hh9
  obtain ⟨Awin, -, hband⟩ := s16_bandLaneWinLH_holdsU h hh
  -- ⟦THE cs-FREE, Ks-WINDOWED FLAT TERMINAL⟧ V7Ks §5
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ := hk Awin hband
  -- ⟦THE DESIGN CONSTANT, EIGHT ARMS⟧ as in the source
  obtain ⟨A', hA'def⟩ : ∃ a : ℝ, a = max (16 * Real.log (1 / Ks) / 3) (max T₀
      (max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
        (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))))) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (armVt Kvt) A' := ⟨_, rfl⟩
  have harmA : armVt Kvt ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hlift : A' ≤ A := by rw [hAdef]; exact le_max_right _ _
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
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hKw
  -- ⟦THE `T₀` ARM⟧ V7-C's discharge, as in the parent
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A, ?_⟩
  -- ⟦Δ3⟧ the caller's floor and ceiling, forwarded into the kswin form
  intro U1floor a g hU hUceil ha ha8103 hg
  obtain ⟨R, hReps, hHlo, hRg, hstride, hRx, hRωtight, hRxtight, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKswin U1floor
      (by rw [hbase hopq]; exact hU) hUceil a g ha ha8103 hg
  -- ⟦THE BASE-SCALE CAP⟧ at `K = KlevF A`, as in the parent
  have heps500 : (1 : ℚ) / (500 * (h : ℚ)) ≤ R.eps := by rw [hReps]; exact hεpin
  -- ⟦THE RATED SUPPLY, WITH THE CUSHION PAID BY THE EIGHTH ARM⟧
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA26
  have heps500R : (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ) := by
    rw [hReps]
    have hq := (Rat.cast_le (K := ℝ)).mpr hεpin
    rwa [show (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) by
      push_cast; ring] at hq
  have h518 : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by nlinarith [hdes, hA162]
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
  have hthrgate : cofkRThr Cq Cb Xsk Y0 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    linarith [hthrA, hlo, hexp1]
  refine ⟨R, hReps, hHlo, hRg, hstride, hRx, hRωtight, hRxtight, hRtow, hdes, hwin, ?_⟩
  -- ⟦RULE (ii) AT HOP 5⟧ both suppliers fired at `regimeEnlargeX R hx'`; the base-scale cap
  -- reads its outer-scale ceiling FROM THE BAND HYPOTHESIS, not from `hRx`
  intro x' hx' hadvd hxc
  have hKvtcush : 32 * Kvt
      + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
      ≤ Real.log (((regimeEnlargeX R hx').Hhi : ℕ) : ℝ) / 4 :=
    cofkR_cushion_of_armVt (regimeEnlargeX R hx') hKvt0 harmA hlo
  have hcofsupply : S16CofactorSupply_LH_gk h (KlevF A) Cq (regimeEnlargeX R hx') (flatDoorM A) :=
    hcofR (KlevF A) Cq (regimeEnlargeX R hx') (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate
      hKvtcush
  have hxceil : Real.log (((regimeEnlargeX R hx').x : ℕ) : ℝ)
      ≤ 31 / (((regimeEnlargeX R hx').eps : ℚ) : ℝ)
        * (((regimeEnlargeX R hx').Hhi : ℕ) : ℝ) := by
    simp only [regimeEnlargeX_x, regimeEnlargeX_eps, regimeEnlargeX_Hhi]
    rw [hReps]; exact hxc
  exact hfire2 x' hx' hadvd hxc hcofsupply
    (s16_baseScaleCap96_LH_at_klevF_b9 (R := regimeEnlargeX R hx') hh hh9 hA26
      (flatDoorM_one_le hA26) heps500 hxceil hwin)

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
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, hεpin, -, -, -, hA162, hA₀A, hbody⟩ :=
    flat_chain_generic_h_g12b_band h hh hh9 Xi harcXi (MRTDoorReceiptSetG_g12b h Xi)
      (flat_door_head_xceil_h_g12b_band h hh hh9 Xi hcount) A₀
  -- ⟦THE ε-PIN EQUALITY⟧ read off `P R₀` at the TRIVIAL instantiation `x' := R₀.x`
  have hεeq : ε = 1 / (500 * (h : ℚ)) := by
    obtain ⟨R0, hR0eps, -, -, -, hR0ceilLoose, -, -, -, -, -, hR0Pband⟩ :=
      hbody (flatDesignBase A) 1 (fun _ _ => 0) le_rfl (flatDesignBase_loglog_le hA162)
        le_rfl (by norm_num) (xceilRiderStrict_zero ε)
    have hP0 := hR0Pband R0.x (le_refl R0.x) (one_dvd _) hR0ceilLoose
    rw [regimeEnlargeX_self] at hP0
    rw [← hR0eps]
    exact hP0.1
  refine ⟨ε, A, hε, hεpin, hεeq, hA162, hA₀A, ?_⟩
  intro U1floor a g hU hUceil ha ha8103 hg
  obtain ⟨R, hReps, hHlo, hRg, hstride, hceilLoose, hceilOmega, hceilX, -, hdes, hwin, hPband⟩ :=
    hbody U1floor a g hU hUceil ha ha8103 hg
  have hP0 := hPband R.x (le_refl R.x) hstride.1 hceilLoose
  rw [regimeEnlargeX_self] at hP0
  obtain ⟨-, hcountR, -⟩ := hP0
  refine ⟨R, hReps, hHlo, hRg, hstride, hceilLoose, hceilOmega, hceilX, hdes, hwin, hcountR, ?_⟩
  intro x' hx' hdvd hlogx'
  obtain ⟨-, -, ρ, hρpos, hρle, hdoor⟩ := hPband x' hx' hdvd hlogx'
  exact ⟨ρ, hρpos, hρle, hdoor⟩

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
  have hkpos : 0 < a * h := Nat.mul_pos ha hh
  refine mrtUniformityXiL2Set_holds_flat_floor_g12b_band (a * h) hkpos hah9
    (fun eps H _ => bigXiAffD a b h eps H)
    (fun eps heps => nearRatTight_of_bigXiAffD bigXiArcTight_twelve heps ha hh) ?_ A₀
  obtain ⟨Cc, hCc, hCcb, H₀, hH₀2, hcard⟩ :=
    bigXiAff_bounded_ceiling_of_pin_b9 a b h ha hh hah9 _ rfl
  refine ⟨Cc, hCc, hCcb, H₀, hH₀2, ?_⟩
  intro H _ hH
  refine le_trans ?_ (hcard H hH)
  exact_mod_cast bigXiAffD_card_le a b h _ H

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
  have hapos : 0 < a := ha
  have hkpos : 0 < a * h := Nat.mul_pos ha hh
  have hah8103 : a * h ≤ 8103 :=
    Salt.Entropy.Chowla.h_le_8103_of_log_le_nine hkpos hah9
  have haah : a ≤ a * h := Nat.le_mul_of_pos_right a hh
  have ha8103 : a ≤ 8103 := le_trans haah hah8103
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
  have hloga9 : Real.log ((a : ℕ) : ℝ) ≤ 9 := by
    refine le_trans (Real.log_le_log haR (by exact_mod_cast haah)) hah9
  -- ⟦THE RECEIPT AT THE AFFINE SET, BANDED⟧ at the caller's floor `a · flatDesignBase A`
  obtain ⟨ε, A, hε, hεpin, hεeq, hA162, hA₀A, hbody⟩ :=
    mrtUniformityXiL2AffSet_holds_flat_floor_g12b_band a b h ha hh hah9 A₀
  have hU : flatDesignBase A ≤ a * flatDesignBase A := Nat.le_mul_of_pos_left _ hapos
  have hUceil := loglog_mul_flatDesignBase_le_b9 hA162 ha hloga9
  obtain ⟨Rd, hReps, hHlo, hRg, hstride, hceilLoose, hceilOmega, hceilX, hdes, hwin, hcountD,
      hband⟩ :=
    hbody (a * flatDesignBase A) a (fun _ _ => 0) hU hUceil ha ha8103
      (xceilRiderStrict_zero ε)
  obtain ⟨Kc, hKc0, hKcb, hKcount⟩ := hcountD
  have hahQ : ((a * h : ℕ) : ℚ) ≤ 8103 := by exact_mod_cast hah8103
  have hahQ1 : (1 : ℚ) ≤ ((a * h : ℕ) : ℚ) := by exact_mod_cast hkpos
  have heps500 : Rd.eps ≤ 1 / 500 := by
    rw [hReps, hεeq]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have heps4051500 : (1 : ℚ) / 4051500 ≤ Rd.eps := by
    rw [hReps, hεeq]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hdiv : a ∣ Rd.a * Rd.Hlo := by
    rw [hHlo]
    exact (dvd_mul_right a (flatDesignBase A)).mul_left Rd.a
  have hquot : Rd.a * Rd.Hlo / a = Rd.a * flatDesignBase A := by
    rw [hHlo, show Rd.a * (a * flatDesignBase A) = a * (Rd.a * flatDesignBase A) by ring]
    exact Nat.mul_div_cancel_left _ hapos
  have hBle : flatDesignBase A ≤ Rd.a * Rd.Hlo / a := by
    rw [hquot]
    exact Nat.le_mul_of_pos_left _ Rd.ha
  obtain ⟨hf1, hf2⟩ := flatDesignBase_clears_stride_floors_b9 hA162 heps4051500
  have hlo4 : 4 * ⌈(1 / Rd.eps : ℚ)⌉₊ ^ 4 ≤ Rd.a * Rd.Hlo / a := le_trans hf1 hBle
  have hloM : 4000000 ≤ Rd.a * Rd.Hlo / a := le_trans hf2 hBle
  have hb0 : b ≤ Rd.a * Rd.Hlo / a := by omega
  have hepsR0 : (0 : ℝ) < (Rd.eps : ℝ) := by exact_mod_cast Rd.heps
  have heps500R : (Rd.eps : ℝ) ≤ 1 / 500 := by
    have hq := (Rat.cast_le (K := ℝ)).mpr heps500
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at hq
    exact hq
  have hcop : (2 : ℝ) ≤ (Rd.eps : ℝ) ^ 2 * ((Rd.Hlo : ℕ) : ℝ) := by
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
  -- ⟦THE BAND'S OWN BOTTOM⟧ x₀ := Rd.x / a, with the tight ceiling exported at `g ≡ 0`
  have hax0 : a * (Rd.x / a) = Rd.x := Nat.mul_div_cancel' hstride.1
  have hx0_2 : 2 ≤ Rd.x / a := hstride.2.1
  have hRdHhi4M : 4000000 ≤ Rd.Hhi := le_trans Rd.hHlo_floor Rd.hHlohi
  have hRdxarm : Real.log ((Rd.x : ℕ) : ℝ) ≤ xTightCeilArm ε Rd.Hhi := by
    have hle := hceilX
    simp only [Nat.mul_zero, Nat.cast_zero, Real.log_zero] at hle
    rwa [max_eq_left (xTightCeilArm_nonneg ε hε Rd.Hhi hRdHhi4M)] at hle
  have hx0_le_Rdx : Rd.x / a ≤ Rd.x := Nat.div_le_self Rd.x a
  have hx0pos : 0 < Rd.x / a := by omega
  have hx0tight : Real.log ((Rd.x / a : ℕ) : ℝ) ≤ xTightCeilArm ε Rd.Hhi :=
    le_trans (Real.log_le_log (by exact_mod_cast hx0pos) (by exact_mod_cast hx0_le_Rdx)) hRdxarm
  refine ⟨ε, A, hε, hεpin, hεeq, hA162, hA₀A, Rd.x / a, Rd.ω, Rd.Hhi, hx0_2, hω8, hRdHhi4M,
    hceilOmega, hx0tight, by rw [hax0]; exact hceilLoose, ?_⟩
  intro y hy hlogy
  have hx' : Rd.x ≤ a * y := by rw [← hax0]; exact Nat.mul_le_mul_left a hy
  have hdvd' : a ∣ a * y := dvd_mul_right a y
  obtain ⟨ρ, hρpos, hρle, hdoorRe⟩ := hband (a * y) hx' hdvd' hlogy
  have hstrideRe : StrideScale a (regimeEnlargeX Rd hx') :=
    strideScale_regimeEnlargeX a Rd hx' hdvd' hstride
  have hbRe : b ≤ (regimeShrinkX_stride_b9 (regimeEnlargeX Rd hx') a ha ha8103 heps500
      hstrideRe hdiv hlo4 hloM).Hlo := by
    rw [regimeShrinkX_stride_Hlo_b9]
    exact hb0
  have htrans := mrtUniformityXiL2AffW_of_set_b9 h (regimeEnlargeX Rd hx') a b ha ha8103
    heps500 hstrideRe hdiv hlo4 hloM hbRe hω8 Kc ρ hKcount hdoorRe
  have hx2' : 2 ≤ (regimeEnlargeX Rd hx').x / a := hstrideRe.2.1
  have hωx2' : (regimeEnlargeX Rd hx').ω ≤ (regimeEnlargeX Rd hx').x / a := hstrideRe.2.2.1
  have hlogωRe : (101 : ℝ) ≤ Real.log (((regimeEnlargeX Rd hx').ω : ℕ) : ℝ) := by
    simp only [regimeEnlargeX_omega]; linarith
  have hratio := strideZRatio_le (regimeEnlargeX Rd hx').x
    ((regimeEnlargeX Rd hx').x / a) (regimeEnlargeX Rd hx').ω (regimeEnlargeX Rd hx').hx
    hx2' (by simp only [regimeEnlargeX_omega]; exact hω2N) (regimeEnlargeX Rd hx').hωx hωx2'
    hlogωRe
  have hZlo := (harmonic_window_bounds hx2'
    (by simp only [regimeEnlargeX_omega]; exact hω2N) hωx2').1
  have hDpos : (0 : ℝ) < (a : ℝ) * (((regimeEnlargeX Rd hx').x / a / (regimeEnlargeX Rd hx').ω
      : ℕ) : ℝ) + 1 := by positivity
  have hLpos : (0 : ℝ) < Real.log (((regimeEnlargeX Rd hx').ω : ℕ) : ℝ) - 1 := by
    simp only [regimeEnlargeX_omega]; linarith
  have hlog2Re : (2 : ℝ) ≤ Real.log (((regimeEnlargeX Rd hx').ω : ℕ) : ℝ) := by linarith
  have hEnd0 := strideEndpoint_le Kc (a : ℝ)
    (∑ n ∈ Finset.Ioc ((regimeEnlargeX Rd hx').x / a / (regimeEnlargeX Rd hx').ω)
        ((regimeEnlargeX Rd hx').x / a), (n : ℝ)⁻¹)
    ((regimeEnlargeX Rd hx').x / a / (regimeEnlargeX Rd hx').ω) (regimeEnlargeX Rd hx').ω
    hKc0.le (Nat.cast_nonneg a) hlog2Re hZlo
  have hnum : Kc * (a : ℝ) ≤ 2 ^ 539 * (a : ℝ) :=
    mul_le_mul_of_nonneg_right hKcb (Nat.cast_nonneg a)
  have hEnd1 : Kc * (a : ℝ)
        / (((a : ℝ) * (((regimeEnlargeX Rd hx').x / a / (regimeEnlargeX Rd hx').ω : ℕ) : ℝ) + 1)
            * (Real.log (((regimeEnlargeX Rd hx').ω : ℕ) : ℝ) - 1))
      ≤ 2 ^ 539 * (a : ℝ)
        / (((a : ℝ) * (((regimeEnlargeX Rd hx').x / a / (regimeEnlargeX Rd hx').ω : ℕ) : ℝ) + 1)
            * (Real.log (((regimeEnlargeX Rd hx').ω : ℕ) : ℝ) - 1)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (mul_pos hDpos hLpos).le)
  have hyeq : (regimeEnlargeX Rd hx').x / a = y := Nat.mul_div_cancel_left y hapos
  refine ⟨ChowlaRegimeAff.ofRegime
      (regimeShrinkX_stride_b9 (regimeEnlargeX Rd hx') a ha ha8103 heps500 hstrideRe hdiv
        hlo4 hloM) b hbRe,
    rfl, rfl, hReps, hyeq, rfl, rfl, ?_, ?_, ρ, 1.02,
    2 ^ 539 * (a : ℝ)
      / (((a : ℝ) * (((regimeEnlargeX Rd hx').x / a / (regimeEnlargeX Rd hx').ω : ℕ) : ℝ) + 1)
          * (Real.log (((regimeEnlargeX Rd hx').ω : ℕ) : ℝ) - 1)),
    hρpos, hρle, by norm_num, by norm_num, by positivity, le_rfl, ?_⟩
  · exact hBle
  · have hDge : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
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
  · refine mrtUniformityXiL2AffW_mono h _ htrans ?_
    have hρ0 : (0 : ℝ) ≤ ρ := hρpos.le
    have hratmul : (a : ℝ)
        * ((∑ n ∈ Finset.Ioc ((regimeEnlargeX Rd hx').x / (regimeEnlargeX Rd hx').ω)
              (regimeEnlargeX Rd hx').x, (n : ℝ)⁻¹)
            / (∑ n ∈ Finset.Ioc ((regimeEnlargeX Rd hx').x / a / (regimeEnlargeX Rd hx').ω)
                  ((regimeEnlargeX Rd hx').x / a), (n : ℝ)⁻¹)) * ρ
        ≤ (a : ℝ) * 1.02 * ρ := by
      have hmul := mul_le_mul_of_nonneg_left hratio haR.le
      exact mul_le_mul_of_nonneg_right hmul hρ0
    linarith [hratmul, hEnd0, hEnd1]

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
