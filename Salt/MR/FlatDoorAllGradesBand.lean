/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FlatDoorAllGrades
import Salt.MR.TierSBand
import Mathlib

-- Needed to transcribe §4's band head and §5's socket hop: the two names rung 2 itself
-- opens for the identical purpose (`FlatDoorEpsRung2.lean:25-26`).  MEASURED, not assumed:
-- `#check @uniformCap_shuffle` and `#check @uniformCap_arc` both fail without this line
-- (`Unknown identifier`), and `regimeFlatEnlargeX` needs no such line — it is public in
-- `Salt.Entropy.Chowla`, which is opened below.
open private uniformCap_arc uniformCap_shuffle from Salt.MR.S16Uniform

/-!
# ⟦TIER S — ROAD F, THE REGIME AXIS: THE FLAT DOOR ON THE BAND (ARM R)⟧
(`FlatDoorAllGradesBand`)

**HONEST LABEL, FIRST LINE — HALF 1 OF TWO, AND THE THEOREM IS NOT IN IT.  NOTHING HERE BEARS ON
TWIN PRIMES, AND ARM R HAS NO KERNEL READER.**  Landed W-δ (`FlatDoorAllGradesW`,
`FlatDoorAllGrades.lean:50`) is the `L²` MRT door on the flat family at every grade `ρ > 0`.  ARM
R states the same door at EVERY outer scale `x'` of a LONG band above the built regime, which is
the corpus's own idiom for moving the crown's regime quantifier (`∃ H₀ ∀ R` against W-δ's
`∀ A₀ ∃ R`).  The crown `MRTDoorAllGrades` still has no producer; R does not reach it, it does not
buy the class road's residual (`x` large against `exp H₊`), it does not buy the `ε`-range
`(1/500, 1/2]`, and it does not buy a rate.

⛔ **WHAT THIS FILE OWES.  HALF 2 IS NOT WRITTEN**, and in particular the theorem
`: FlatDoorAllGradesBandW` DOES NOT EXIST YET: the statement of record below is a named `Prop`
with no inhabitant in this file, never a theorem with an unproved body.  Half 2 owes the
conditional hop, Kswin, V7, the chain, the shrink's band twin, W-δ on the band, the long-band
numeric lemma at the arm ceiling, the zero level
`FlatDoorAllGradesBandW → FlatDoorAllGradesW`, and the
registration under `#audit_axioms` in `Salt/MR/All.lean`.  Until then nothing in this file is a
new unconditional theorem: §1's `def` is a statement, §2's eight `def`s are statements, and
§3–§5's six theorems are the landed rung-2 chain replayed at the enlarged regime.

## §2's RULE — the eight band forms are GENERATED, never typed
ONE RULE turns each of rung 2's eight forms (`FlatDoorEpsRung2.lean:4478 · 4499 · 4529 · 4554 ·
4590 · 4684 · 4709 · 4738`) into its `_band` twin, everything else the source's byte for byte.
⚠️ Rung 2 has NO STRIDE, so the landed S-1 rule (`TierSBand.lean:35–54`) loses `a` throughout:
the rider is `g`, never `a * g`; there is no `a ∣ x'`, no `1 ≤ a → a ≤ 8103`, no `StrideScale`.

  (i-ω)    after the loose ceiling `Real.log R.x ≤ 31/ε · R.Hhi ∧` INSERT the rider-free tight
           ceiling on the width, `Real.log R.ω ≤ xTightCeil ε R.Hhi`; `ω` is untouched by the
           enlargement and by every hop;
  (i-x)    then the export-only tight bound on `x` in the MAX shape, in TWO TIERS because the
           conditional hop instantiates its source at the INFLATED rider and a rider-relative
           bound cannot cross it —
             tier A (head · socket · doorL2 · road · capstone; the rider `g` passes verbatim):
               `Real.log R.x ≤ max (xTightCeil ε R.Hhi) (Real.log (g R.Hhi R.ω))`
             tier B (conditional · Kswin):
               `Real.log R.x ≤ max (xTightCeilArm ε R.Hhi) (Real.log (2 · g R.Hhi R.ω))`;
  (i-gate) in the FIVE tier-A forms ONLY, after (i-x), the gate fact the builder twin B2′ proves
           and exports, `50 + Real.log c ≤ Real.log (Real.log R.Hhi)` — the conditional hop of
           HALF 2 is what spends it.  It reads `Hhi` only, so the enlargement does not touch it;
  (i′)     `V7RatedFormEpsW` carries NO ceiling and binds NO rider: after
           `R.eps = ε ∧ R.Hlo = flatDesignBase A ∧` INSERT the loose ceiling, then (i-ω), then
           the COLLAPSED tier-B bound `Real.log R.x ≤ xTightCeilArm ε R.Hhi` — there is no `g`
           to put in a `max`, and the crown side reads it directly in HALF 2;
  (ii)     PREFIX the antecedent block — the form's LAST conjunct — with the band quantifier
             `∀ (x' : ℕ) (hx' : R.x ≤ x'), Real.log x' ≤ 31/ε · R.Hhi →`
           and REPLACE every occurrence of the regime `R` inside that block by
           `regimeEnlargeX R hx'`;
  (iii)    wrap every line to ≤ 100 columns, by the generator itself.

WHY THE BAND IS THREADED THROUGH EVERY FORM: each hop passes ONE regime through and the
statements export nothing tying the output regime to the input regime, so a band that is not in
the form cannot be recovered from the chain's conclusion.  WHY THE LOOSE ceiling in the band and
the tight one only as an export: the tight reading gives floor and ceiling the same leading
coefficient.  WHY THE MAX shape: the builder enlarges `x` to `max x (g Hhi ω)`, so the caller's
own `g` is part of the answer; at `g ≡ 0` the MAX collapses to the tight arm (`Real.log 0 = 0`),
which is what HALF 2's exhibited caller spends.

**DIRECTION IS THE WHOLE REASON THIS IS A TRANSCRIPTION AND NOT A TRANSPORT:** every read of `x`
on rung 2's chain is a LOWER bound, monotone under `x ↦ x'`, except V7's one ceiling — which the
band hypothesis IS at `x'`.  The door at `R` does not imply the door at `regimeEnlargeX R hx'`,
so the chain is RE-RUN at the enlarged regime rather than transported, and re-running it costs
the transcription and nothing else.  The four hops of §5 spend the regime's own fields, which are
`(regimeEnlargeX R hx')`'s own fields, and `eps`, `Hlo`, `Hhi` reduce by the six `@[simp]`
projections of `RegimeHead.lean:137`.

## WHAT IS IN THIS FILE
* §1 `FlatDoorAllGradesBandW` — the statement of record;
* §2 `FlatHeadFormEpsW_band`, `FlatSocketFormEpsW_band`, `FlatDoorL2FormEpsW_band`,
  `FlatRoadFormEpsW_band`, `FlatCapstoneFormEpsW_band`, `FlatConditionalFormEpsW_band`,
  `FlatKswinFormEpsW_band`, `V7RatedFormEpsW_band` — the eight generated band forms;
* §3 `chowlaRegimeFlat_exists_param_head_xceil_at_tight` — the builder twin B2′;
* §4 `flat_head_uniform_xceil_epsW_band` — the band head at the trivial payload;
* §5 `flat_socket_generic_epsW_band`, `flat_doorL2_generic_epsW_band`,
  `flat_road_generic_epsW_band`, `flat_capstone_generic_epsW_band` — the four pass-through hops.
-/

noncomputable section

open scoped BigOperators
open Salt.Entropy.Chowla

set_option exponentiation.threshold 4000

namespace Salt.MR

/-! ## §1 — ARM R, THE STATEMENT OF RECORD -/

/-- **⟦ARM R — W-δ ON THE BAND⟧** (`FlatDoorAllGradesBandW`) — W-δ (`FlatDoorAllGradesW`) with one
more export: the built regime carries the door at EVERY outer scale `x'` from its own `R.x` up to
the flat ceiling `log x' ≤ (31/ε)·R.Hhi` (the landed band idiom, `regimeEnlargeX`), and the band
is LONG (`2·log R.x ≤ (31/ε)·R.Hhi`: it reaches `R.x²`), so the clause is not inert.  Its
zero level is landed W-δ (HALF 2); it has no kernel reader; nothing here bears on twin primes. -/
def FlatDoorAllGradesBandW : Prop :=
  ∀ (ε : ℚ), 0 < ε → ε ≤ 1 / 500 → ∀ ρ : ℝ, 0 < ρ → ∀ A₀ : ℝ,
    ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        2 * Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
        ∀ (x' : ℕ) (hx' : R.x ≤ x'),
          Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
          MRTUniformityXiL2 (regimeEnlargeX R hx') ρ

/-! ## §2 — the eight band forms, by rules (i-ω) (i-x) (i-gate) (i′) (ii) of the header.
GENERATED from rung 2's eight `def`s, not typed: everything but the five inserted lines and the
`(regimeEnlargeX R hx')` substitution is the source's byte for byte, which is why they carry no
per-declaration docstring — the rule above is their specification, exactly as `TierSBand.lean:99`
does for the six landed band forms. -/

def FlatHeadFormEpsW_band (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧ 0 < δ₀ ∧
      1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 26 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap = max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            XCeilRiderAt (50 + Real.log (c : ℝ)) ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
            Real.log ((R.x : ℕ) : ℝ)
              ≤ max (xTightCeil ε R.Hhi) (Real.log ((g R.Hhi R.ω : ℕ) : ℝ)) ∧
            50 + Real.log (c : ℝ) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ∧
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((bigXi R.eps H).card : ℝ) ≤ K) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            R.Hlo ≤ max Hcap (max extraFloor U1floor) ∧
            ∀ (x' : ℕ) (hx' : R.x ≤ x'),
              Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
              ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 (regimeEnlargeX R hx') ρ →
                P (regimeEnlargeX R hx')

def FlatSocketFormEpsW_band (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧ 0 < δ₀ ∧
      1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRiderAt (50 + Real.log (c : ℝ)) ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
              Real.log ((R.x : ℕ) : ℝ)
                ≤ max (xTightCeil ε R.Hhi) (Real.log ((g R.Hhi R.ω : ℕ) : ℝ)) ∧
              50 + Real.log (c : ℝ) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (x' : ℕ) (hx' : R.x ≤ x'),
                Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
                (∀ (a e : ℕ → ℂ) (Bsieve : ℕ → ℝ) (Binsert : ℝ),
                  (∀ m, lamCoeff m = a m + e m) →
                  (∀ H : ℕ, 0 ≤ Bsieve H) →
                  (∀ H : ℕ, ∀ [NeZero H], (regimeEnlargeX R hx').Hlo ≤ H →
                    H ≤ (regimeEnlargeX R hx').Hhi → ∀ α : ℝ,
                    NearRatTight (arcDen 12 H) H α →
                      (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure (regimeEnlargeX R hx').x
                        (regimeEnlargeX R hx').ω))
                        ≤ Bsieve H * (H : ℝ) ^ 2) →
                  (∀ H : ℕ, ∀ [NeZero H], (regimeEnlargeX R hx').Hlo ≤ H →
                    H ≤ (regimeEnlargeX R hx').Hhi →
                    (∑ ξ ∈ bigXi (regimeEnlargeX R hx').eps H, (1 / (H : ℝ) ^ 2) *
                      ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                        ∂(logMeasure (regimeEnlargeX R hx').x (regimeEnlargeX R hx').ω)) ≤ Binsert)
                          →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    K * (2 * Bsieve H) + 2 * Binsert ≤ δ₀) →
                  P (regimeEnlargeX R hx'))

def FlatDoorL2FormEpsW_band (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg : ℝ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧ 0 < δ₀ ∧
      1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧
      (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRiderAt (50 + Real.log (c : ℝ)) ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
              Real.log ((R.x : ℕ) : ℝ)
                ≤ max (xTightCeil ε R.Hhi) (Real.log ((g R.Hhi R.ω : ℕ) : ℝ)) ∧
              50 + Real.log (c : ℝ) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (x' : ℕ) (hx' : R.x ≤ x'),
                Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
                ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
                  M4DoorGates_L_gk K Cg (regimeEnlargeX R hx') M k δ →
                  (∀ H : ℕ, 0 ≤ Braw H) →
                  M4SievedDoorSq_L_gk K (regimeEnlargeX R hx') M Braw →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    Braw H ≤ Bceil) →
                  2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / ((regimeEnlargeX R hx').x : ℝ) ≤ δ₀ →
                    P (regimeEnlargeX R hx')

def FlatRoadFormEpsW_band (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg : ℝ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧ 0 < δ₀ ∧
      1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧
      (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRiderAt (50 + Real.log (c : ℝ)) ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
              Real.log ((R.x : ℕ) : ℝ)
                ≤ max (xTightCeil ε R.Hhi) (Real.log ((g R.Hhi R.ω : ℕ) : ℝ)) ∧
              50 + Real.log (c : ℝ) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (x' : ℕ) (hx' : R.x ≤ x'),
                Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
                ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
                  M4DoorGates_L_gk K Cg (regimeEnlargeX R hx') M k δ → 1 ≤ M →
                  (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
                  (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    arcDen 12 H ^ 7 ≤ RStr H) →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                        * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                      ≤ Braw H) →
                  (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                    Braw H ≤ Bceil) →
                  2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / ((regimeEnlargeX R hx').x : ℝ) ≤ δ₀ →
                  M4ChiSummedFreeRow_L_gk K (regimeEnlargeX R hx') M RS →
                    P (regimeEnlargeX R hx')

def FlatCapstoneFormEpsW_band (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ) : Prop :=
    ∃ (Cg : ℝ) (Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      Kc ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRiderAt (50 + Real.log (c : ℝ)) ε g →
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
                Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
                Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
                Real.log ((R.x : ℕ) : ℝ)
                  ≤ max (xTightCeil ε R.Hhi) (Real.log ((g R.Hhi R.ω : ℕ) : ℝ)) ∧
                50 + Real.log (c : ℝ) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (x' : ℕ) (hx' : R.x ≤ x'),
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
                          4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                        (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                          arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                        (∀ H : ℕ, (regimeEnlargeX R hx').Hlo ≤ H → H ≤ (regimeEnlargeX R hx').Hhi →
                          m4SmallGradeFits (doorRowFloorL M)
                            (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                            (fun H => 2 * rStrWitness H) H) →
                        -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                        (∀ H L q j A s : ℕ, SocketBaseL (regimeEnlargeX R hx') M H L q j A s →
                          DoorBaseFrame (A + s) j) →
                        (∀ H L q j A s : ℕ, SocketBaseL (regimeEnlargeX R hx') M H L q j A s →
                          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                            ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc))
                              (regimeEnlargeX R hx').Hhi) →
                        (∀ H L q j A s : ℕ, SocketBaseL (regimeEnlargeX R hx') M H L q j A s →
                          GRowsZeroGate'''_L_gk K M (A + s) Cp
                            (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc))
                              (regimeEnlargeX R hx').Hhi)) →
                        (∀ H L q j A s : ℕ, SocketBaseL (regimeEnlargeX R hx') M H L q j A s →
                          14 * Real.log (Real.log (((regimeEnlargeX R hx').Hhi : ℕ) : ℝ)) +
                            Real.log 376266
                              + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                            ≤ (theta293 - epsrf (A + s))
                                * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                        (∀ H L q j A s : ℕ, SocketBaseL (regimeEnlargeX R hx') M H L q j A s →
                          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                            ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc))
                              (regimeEnlargeX R hx').Hhi) →
                        (∀ H L q j A s : ℕ, SocketBaseL (regimeEnlargeX R hx') M H L q j A s →
                          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                            * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc))
                              (regimeEnlargeX R hx').Hhi) →
                        -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                        (∀ H L q j A s : ℕ, SocketBaseL (regimeEnlargeX R hx') M H L q j A s →
                          0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                        (∀ H L q j A s : ℕ, SocketBaseL (regimeEnlargeX R hx') M H L q j A s →
                          calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                                ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                            (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                            (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                        -- ⟦B4 RAW⟧ the crossing bound, carried
                        (∀ H L q j A s : ℕ, SocketBaseL (regimeEnlargeX R hx') M H L q j A s →
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
                        (∀ H L q j A s : ℕ, SocketBaseL (regimeEnlargeX R hx') M H L q j A s →
                          DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                        (∀ H L q j A s : ℕ, SocketBaseL (regimeEnlargeX R hx') M H L q j A s →
                          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                            (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                          P (regimeEnlargeX R hx')

def FlatConditionalFormEpsW_band (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ) : Prop :=
    ∃ (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      Kc ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRiderStrictAt (50 + Real.log (c : ℝ)) ε g →
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
              Real.log ((R.x : ℕ) : ℝ)
                ≤ max (xTightCeilArm ε R.Hhi) (Real.log ((2 * g R.Hhi R.ω : ℕ) : ℝ)) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ (x' : ℕ) (hx' : R.x ≤ x'),
                Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
                ∀ M : ℕ,
                  S15Sel''_L_gk_T K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl
                    (regimeEnlargeX R hx') M →
                   K ≤ 170000000 * M →
                  S15CrossingBound_L_gk K (regimeEnlargeX R hx') M → P (regimeEnlargeX R hx')

def FlatKswinFormEpsW_band (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ) : Prop :=
    ∃ (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧
        ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
          K ≤ 170000000 * flatDoorM A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          T₀ ≤ Real.exp (Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ) / 2) →
          Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 →
          ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrictAt (50 + Real.log (c : ℝ)) ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
            Real.log ((R.x : ℕ) : ℝ)
              ≤ max (xTightCeilArm ε R.Hhi) (Real.log ((2 * g R.Hhi R.ω : ℕ) : ℝ)) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            ∀ (x' : ℕ) (hx' : R.x ≤ x'),
              Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
              (S16CofactorSupply_L_gk K Cq (regimeEnlargeX R hx') (flatDoorM A) →
                S16BaseScaleCap96_L_gk K (regimeEnlargeX R hx') (flatDoorM A) →
                  P (regimeEnlargeX R hx')))

def V7RatedFormEpsW_band (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (A₀ : ℝ) : Prop :=
    ∃ (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧ Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧
      (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      Mfl ≤ flatDoorM A ∧ 0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
        Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil ε R.Hhi ∧
        Real.log ((R.x : ℕ) : ℝ) ≤ xTightCeilArm ε R.Hhi ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        ∀ (x' : ℕ) (hx' : R.x ≤ x'),
          Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
          P (regimeEnlargeX R hx')

/-! ## §3 — the builder twin B2′: B1's tight bound and the gate fact, both EXPORTED -/

/-- **⟦ARM R B2′ — THE BUILDER TWIN ON B1 AT STRIDE 1⟧**
(`chowlaRegimeFlat_exists_param_head_xceil_at_tight`) — rung 2's
`chowlaRegimeFlat_exists_param_head_xceil_at` (`FlatDoorEpsRung2.lean:2900`, body 90 lines) with
its first `obtain` taken from the landed S-1 builder B1
(`chowlaRegimeFlat_exists_param_gen_ceiling_mul_b9_tight`, `TierSBand.lean:420`) at stride
`a := 1` — `strideScale_one` makes that a flat regime — instead of from
`chowlaRegimeFlat_exists_param_gen_ceiling`.  Everything else is the source's body byte for byte;
THREE conjuncts move, and they are the whole reason this twin exists:

* B1's conclusion has NINE conjuncts where the source's builder has six.  Its FOURTH,
  `StrideScale 1 R.toChowlaRegime`, is DROPPED with `-`; its LAST TWO are what is harvested.
* `hRωtight` (`log R.ω ≤ xTightCeil eps R.Hhi`) is EXPORTED unchanged — `ω` is carried verbatim
  by the enlargement — and `hRxtight` (`log R.x ≤ xTightCeil eps R.Hhi`) is carried through the
  enlargement `x ↦ max x (g Hhi ω)` into the MAX shape by the two `rcases` on `le_total`, exactly
  as the landed B2 does it (`TierSBand.lean:615`), minus the stride's division by `a`.
* `hll` (`lam0 ≤ log (log R.Hhi)`, the source's own `:2917`) is EXPORTED as the last conjunct
  instead of being spent silently at the rider gate.  The five tier-A band forms of §2 carry it
  and HALF 2's conditional hop spends it; it reads `Hhi` only, so the enlargement does not move
  it.  At `lam0 = 50` the hypothesis `hlamA` is `50 ≤ 3.2·A`, which `hA : 26 ≤ A` already gives
  (`3.2 · 26 = 83.2`), so this twin is not weaker than its source at the source's own floor.

Nothing here bears on twin primes. -/
theorem chowlaRegimeFlat_exists_param_head_xceil_at_tight (lam0 A : ℝ) (hA : 26 ≤ A)
    (hlamA : lam0 ≤ 3.2 * A) (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ)
    (g : ℕ → ℕ → ℕ) (hg : XCeilRiderAt lam0 eps g) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      g R.Hhi R.ω ≤ R.x ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
      Real.log ((R.ω : ℕ) : ℝ) ≤ xTightCeil eps R.Hhi ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ max (xTightCeil eps R.Hhi) (Real.log ((g R.Hhi R.ω : ℕ) : ℝ)) ∧
      lam0 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) := by
  obtain ⟨R, hReps, hRA, hRHlo, -, hRcap, hRwid, hRx, hRωtight, hRxtight⟩ :=
    chowlaRegimeFlat_exists_param_gen_ceiling_mul_b9_tight 1 le_rfl (by norm_num) A hA eps heps
      heps1 Hlo₀
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
  have hgx : Real.log ((g R.Hhi R.ω : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) :=
    hg R.Hhi R.ω ⟨hHhi4, hll, hωgate⟩
  refine ⟨regimeFlatEnlargeX R (le_max_left R.x (g R.Hhi R.ω)), hReps, hRA, hRHlo,
    le_max_right _ _, hRcap, hRwid, ?_, ?_, ?_, ?_⟩
  · simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_Hhi]
    rcases le_total R.x (g R.Hhi R.ω) with h | h
    · rw [max_eq_right h]; exact hgx
    · rw [max_eq_left h]; exact hRx
  · simp only [regimeFlatEnlargeX_omega, regimeFlatEnlargeX_Hhi]
    exact hRωtight
  · simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_omega, regimeFlatEnlargeX_Hhi]
    rcases le_total R.x (g R.Hhi R.ω) with h | h
    · rw [max_eq_right h]; exact le_max_right _ _
    · rw [max_eq_left h]; exact le_trans hRxtight (le_max_left _ _)
  · simp only [regimeFlatEnlargeX_Hhi]
    exact hll

/-! ## §4 — the band head at the trivial payload -/

/-- **⟦ARM R H0 — THE BAND HEAD AT THE TRIVIAL PAYLOAD⟧**
(`flat_head_uniform_xceil_epsW_band`) — rung 2's `flat_head_uniform_xceil_epsW`
(`FlatDoorEpsRung2.lean:4783`, body 169 lines) at the band form, at `P := fun _ => True`.

**THE PAYLOAD IS DROPPED, BINDER AND ALL.**  The landed head takes a four-clause `hP` and spends
it in a SLOT that runs the door-head's spine at the regime it built; this twin takes no `hP`, and
its last conjunct is `fun x' hx' hxc ρ _ _ _ => trivial`.  That is cell (3) of the road-F freeze
of ARM R, and it is what keeps K10 out of this wave: the slot's spine is never run at the
enlarged regime, so NO `toChowlaRegime`/`regimeEnlargeX` compatibility lemma is needed.  It is
also the landed idiom rather than a new one — `flatDoorAllGradesW_holds`
(`FlatDoorAllGrades.lean:110`) already calls the landed head at `P := fun _ => True` and swaps
the payload in afterwards by the shrink.

WHAT SURVIVES, AND WHY: every `obtain`/`have` the FORM's conjuncts read — the count `K` through
`bigXi_bounded_ceiling_eps`, the mint `δ₀ = cD3/(16·C)·ε/4` with its pin `1/(838400·c) ≤ δ₀`,
`β`, `Hopq`, `Hcap`'s equation, the builder call (now B2′ of §3 at `lam0 := 50 + log c`, with
`hlamA` paid exactly as the landed head pays it), the tower conjunct and the cap conjunct.  The
count conjunct is stated at `R`, not at the enlarged regime, exactly as the landed band head does
it (`TierSBand.lean:115`) — it reads `Hlo`, `Hhi`, `eps` only.  THE THREE NEW EXPORTS come
straight from B2′'s conclusion: `hRωtight`, `hRxtight` in the MAX shape, and `hll`, at the
positions rules (i-ω) (i-x) (i-gate) put them.

WHAT WAS DROPPED, MEASURED BY A `clear`-PROBE ON A SCRATCH COPY rather than by reading: the full
transcription with every landed step present elaborates (`EXIT=0`), and so does this one with the
whole set below absent — so each member is individually unnecessary, not merely jointly.  The set
is `hreduce_holds_final_bounded`'s five names, `primeWindow_sum_inv_ge_bounded`'s five, the
circle-method estimate's four, `hcD3ge`, `hCle`, `hεle`, `hεcE`, `hε_half_lt`, `hε_D3`,
`hε_D3C`, `hbudHlo`, `hredHlo`, and the ~45-line slot itself.  `Hopq` is then witnessed by
`H₀xi` alone, since the two floors the landed head maxes into it came from the first two dropped
`obtain`s.  Nothing here bears on twin primes. -/
theorem flat_head_uniform_xceil_epsW_band (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
    {c : ℕ} (hc1 : 1 ≤ c) (hcε : (1 : ℚ) / (500 * (c : ℚ)) ≤ ε) :
    FlatHeadFormEpsW_band ε c (fun _ => True) := by
  classical
  unfold FlatHeadFormEpsW_band
  -- ⟦THE LEAF NUMERALS, PINNED⟧ `log 4 = 2·log 2`, both `d9` bounds on `log 2`
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  -- ⟦THE LEAVES' WITNESSES, PINNED⟧ the door-head's device (`DoorReceipt.lean:1012–1021`)
  obtain ⟨cD3, hcD3def⟩ : ∃ c : ℝ, c = 1 / 4 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ c : ℝ, c = 1 + 2 * (2 * Real.log 4) := ⟨_, rfl⟩
  have hcD3 : 0 < cD3 := by rw [hcD3def]; norm_num
  have hC : 0 < C := by rw [hCdef]; positivity
  have hCnum : C ≤ 655 / 100 := by rw [hCdef, hlog4eq]; linarith
  -- ⟦THE `ε` BOUNDS⟧ only the two the FORM reads survive here
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  have hεQ1 : ε ≤ 1 / 2 := by
    have h2 : (1 : ℚ) / 500 ≤ 1 / 2 := by norm_num
    linarith
  -- ⟦THE MINT⟧ the head's `δ₀` at the pinned witnesses IS the frozen file's term, exactly
  have hmint : cD3 / (16 * C) * (ε : ℝ) / 4 = (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) := by
    rw [hcD3def, hCdef]
    have hne : (1 : ℝ) + 2 * (2 * Real.log 4) ≠ 0 := by positivity
    field_simp
    ring
  -- ⟦THE MINT AGAINST THE PIN, AT THE CHARGE⟧ the source's `hqcap`/`hcapR`/`hδnum` at `c`
  have hcQ : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcQ0 : (0 : ℚ) < 500 * (c : ℚ) := by linarith
  have hqcap : (1 : ℚ) ≤ 500 * (c : ℚ) * ε := by
    rw [div_le_iff₀ hcQ0] at hcε; linarith
  have hcapR : (1 : ℝ) ≤ 500 * (c : ℝ) * (ε : ℝ) := by exact_mod_cast hqcap
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hδnum : (1 : ℝ) / (838400 * (c : ℝ)) ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    rw [hmint, div_le_div_iff₀ (by linarith) (by positivity), hlog4eq]
    linarith
  -- ⟦THE COUNT HOOK AT THE CAP⟧ §2, in place of the pinned hook
  obtain ⟨K, hK, hKb, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded_ceiling_eps ε hε0 hε hc1 hcε
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = cD3 * (ε : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hcD3 hεR0) (by positivity)
  obtain ⟨Hopq, hOpqdef⟩ : ∃ n : ℕ, n = H₀xi := ⟨_, rfl⟩
  refine ⟨K, cD3 / (16 * C) * (ε : ℝ) / 4, β, Hopq, hε0, hK, hKb,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num),
    hc1, hcε, hδnum, hβpos, ?_⟩
  -- ⟦THE HOIST⟧ the landed proof chose `A := max A₀ (budgetAFlat ε β)` HERE
  intro A hA26 hAge hAL
  -- ⟦THE TOWER FLOOR THE NINTH ARM PAYS⟧ `50 + Lc ≤ 45 + A/2 ≤ 3.2·A` at `A ≥ 26`
  have hlamA : 50 + Real.log (c : ℝ) ≤ 3.2 * A := by linarith
  obtain ⟨F, hFdef⟩ : ∃ n : ℕ, n = max Hopq (budgetFloorFlat (ε : ℝ) β A) := ⟨_, rfl⟩
  refine ⟨max (flatDesignFloor A) (max F (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), by rw [hFdef], ?_⟩
  intro extraFloor U1floor g₅ hg₅
  obtain ⟨Rf, hReps, hRA, hRHlo, hRg, _hRcapEq, hRwid, hRx, hRωtight, hRxtight, hll⟩ :=
    chowlaRegimeFlat_exists_param_head_xceil_at_tight (50 + Real.log (c : ℝ)) A hA26 hlamA ε hε0
      hεQ1 (max F (max extraFloor U1floor)) g₅ hg₅
  have hFlo : F ≤ Rf.Hlo := le_trans (le_max_left _ _) hRHlo
  have hxiHlo : H₀xi ≤ Rf.Hlo := by
    rw [hFdef, hOpqdef] at hFlo
    exact le_trans (le_max_left _ _) hFlo
  refine ⟨Rf.toChowlaRegime, hReps,
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, hRx,
    hRωtight, hRxtight, hll, ?_, fun _ => hRwid, ?_, ?_⟩
  · -- ⟦THE EXPORTED COUNT GATE⟧ the road's `hXi`, at this head's own `ε`
    intro H' _ hlo' _
    rw [hReps]
    exact hxi H' (le_trans hxiHlo hlo')
  · -- ⟦THE CAP⟧ the flat base equation, shuffled onto the consumer's floors
    rw [_hRcapEq]
    exact uniformCap_shuffle _ _ _ _ _
  · -- ⟦THE DOOR, HANDED OUT INSTEAD OF SPENT⟧ at the trivial payload
    exact fun x' hx' hxc ρ _ _ _ => trivial

end Salt.MR

end
