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

/-! ## §5 — the four pass-through hops, at the enlarged regime

Rung 2's four PASS-THROUGH hops (`FlatDoorEpsRung2.lean:4952 · 4978 · 5023 · 5086`) at the band
forms.  In each one the source's tuple gains the THREE new export conjuncts of rules (i-ω) (i-x)
(i-gate) — `hRωtight`, `hRxtight`, `hll` — which are passed straight through, and the source's
antecedent block gains `intro x' hx' hxc` in front and is then RUN AT `R' := regimeEnlargeX R hx'`
rather than at `R`.  That is legal for the same reason the whole arm is: the regime's fields these
bodies spend (`R.hx`, `R.hω`, `R.hωx`, `R.hheadroom`, `R.hHlo_floor`) are `R'`'s own fields, and
`R'.eps`, `R'.Hlo`, `R'.Hhi` are `R`'s verbatim.  MEASURED over all four bodies: not one of them
bounds `x` from ABOVE anywhere — every read of `x` is a lower bound and so survives `x ↦ x'` — so
the band hypothesis `hxc` is consumed by nothing here but the next form's own block.  The worked
precedent is the landed road-exit band hop (`TierSBand.lean:844`), which merges rung 2's three
into one; these are three separate hops making the same moves, plus the capstone. -/

/-- **⟦ARM R H0→H1⟧** (`flat_socket_generic_epsW_band`) — rung 2's `flat_socket_generic_epsW`
(`:4952`) at the band forms.  The head's one estimate is re-fired at the enlarged regime: `hReps`
and the `H₀` floor are transported by the `@[simp]` projections (`regimeEnlargeX_eps`,
`regimeEnlargeX_Hlo`), and the COUNT hypothesis passes verbatim — it reads `Hlo`, `Hhi` and `eps`
only, all carried by the enlargement. -/
theorem flat_socket_generic_epsW_band (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatHeadFormEpsW_band ε c P) :
    FlatSocketFormEpsW_band ε c P := by
  unfold FlatSocketFormEpsW_band
  obtain ⟨K, δ₀, β, Hopq, hε, hK, hKb, hδ₀, hc1, hεpin, hδpin, hβ, hhead⟩ :=
    h
  obtain ⟨H₀, hH₀⟩ := sum_bigXi_norm_windowExpSum_sq_le_twelve ε hε
  refine ⟨K, δ₀, β, max Hopq H₀, hε, hK, hKb, hδ₀, hc1, hεpin, hδpin, hβ, ?_⟩
  intro A hA162 hAge hAL
  obtain ⟨Hcap, hCapEq, hhd⟩ := hhead A (by linarith) hAge hAL
  refine ⟨max Hcap H₀, by rw [hCapEq]; exact uniformCap_arc _ _ _ _ _, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, _, hRU1, hRg, hRx, hRωtight, hRxtight, hll, hcount, hRtow, hRcap, hR⟩ :=
    hhd 0 (max U1floor H₀) g hg
  have hU1 : U1floor ≤ R.Hlo := le_trans (le_max_left _ _) hRU1
  have harc : H₀ ≤ R.Hlo := le_trans (le_max_right _ _) hRU1
  refine ⟨R, hReps, hU1, hRg, hRx, hRωtight, hRxtight, hll, hRtow,
    le_trans hRcap (by omega), ?_⟩
  intro x' hx' hxc a e Bsieve Binsert hsplit hB0 hsock hins hρ
  have hReps' : (regimeEnlargeX R hx').eps = ε := by
    simp only [regimeEnlargeX_eps]; exact hReps
  have harc' : H₀ ≤ (regimeEnlargeX R hx').Hlo := by
    simp only [regimeEnlargeX_Hlo]; exact harc
  refine hR x' hx' hxc δ₀ hδ₀ le_rfl ?_
  intro H _ hlo hhi
  exact le_trans (hH₀ (regimeEnlargeX R hx') hReps' harc' a e Bsieve K Binsert hsplit hB0 hsock
    hcount hins H hlo hhi) (hρ H hlo hhi)

/-- **⟦ARM R H1→H2⟧** (`flat_doorL2_generic_epsW_band`) — rung 2's `flat_doorL2_generic_epsW`
(`:4978`) at the band forms.  This is the hop whose body reads the REGIME'S OWN FIELDS (`:4995`):
`R.hω`, `R.hheadroom`, `R.hx`, `R.hωx` feed `hHx` and the Parseval insert estimate.  All four are
`R'`'s own fields — the enlargement weakens none of them, since every `x`-constraint of
`ChowlaRegime` is a LOWER bound on `x` (`RegimeHead.lean:104`) — so the body runs at `R'`
unchanged.  The insert budget's `8·2^k/R.x` term likewise only gets smaller at `x' ≥ R.x`. -/
theorem flat_doorL2_generic_epsW_band (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatSocketFormEpsW_band ε c P) :
    FlatDoorL2FormEpsW_band ε c P := by
  unfold FlatDoorL2FormEpsW_band
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  obtain ⟨Kb, δ₀, β, Hopq, hε, hKb, hKbb, hδ₀, hc1, hεpin, hδpin, hβ, hsk⟩ :=
    h
  refine ⟨Cg, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hc1, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge hAL
  obtain ⟨Hcap, hCapLe, hexit⟩ := hsk A hA162 hAge hAL
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRωtight, hRxtight, hll, hRtow, hRcap, hR⟩ :=
    hexit U1floor g hg
  refine ⟨R, hReps, hU1, hRg, hRx, hRωtight, hRxtight, hll, hRtow, hRcap, ?_⟩
  intro x' hx' hxc Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  set R' : ChowlaRegime := regimeEnlargeX R hx' with hR'def
  have hA : 1 ≤ AdoorL M := one_le_AdoorL hgates.hM
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : ∀ H : ℕ, H ≤ R'.Hhi → H + 1 ≤ R'.x := by
    intro H hhi
    have hdiv : R'.x / R'.ω ≤ R'.x / 2 := Nat.div_le_div_left R'.hω (by norm_num)
    have hle : H ≤ R'.x / 2 := le_trans (le_trans hhi R'.hheadroom) hdiv
    have h2 : 2 ≤ R'.x := R'.hx
    omega
  refine hR x' hx' hxc
    (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2
      liouvilleC)
    (fun m => lamCoeff m - memSCoeff (calP (AdoorL M) (s13GK K M))
      (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC m)
    Braw (δ / 4 + 4 * 2 ^ k / (R'.x : ℝ)) (fun m => by ring) hBraw0
    (hsock m4_bandTransport) ?_ ?_
  · intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R'
      (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (AdoorL M) (s13GK K M) M 2 R'.x R'.ω H k liouvilleC δ (bigXi R'.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R'.hx R'.hω R'.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · intro H hlo hhi
    rw [l2_budget_line Kb (Braw H) δ (R'.x : ℝ) k]
    have hmono : 2 * Kb * Braw H ≤ 2 * Kb * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

/-- **⟦ARM R H2→H3⟧** (`flat_road_generic_epsW_band`) — rung 2's `flat_road_generic_epsW`
(`:5023`) at the band forms.  The body reads no field of the regime directly; its regime-relative
steps (`one_le_arcDen_of_regime`, `blockLen_narrow`, `blockLen_drift`) take `R'` as their named
regime argument and are supplied the `R'`-relative floors the band block hands them. -/
theorem flat_road_generic_epsW_band (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatDoorL2FormEpsW_band ε c P) :
    FlatRoadFormEpsW_band ε c P := by
  unfold FlatRoadFormEpsW_band
  obtain ⟨Cg, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hc1, hεpin, hδpin, hβ, hdoor⟩ :=
    h
  refine ⟨Cg, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hc1, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge hAL
  obtain ⟨Hcap, hCapLe, hmain⟩ := hdoor K A hA162 hAge hAL
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRωtight, hRxtight, hll, hRtow, hRcap, hR⟩ :=
    hmain U1floor g hg
  refine ⟨R, hReps, hU1, hRg, hRx, hRωtight, hRxtight, hll, hRtow, hRcap, ?_⟩
  intro x' hx' hxc δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2
    harc3 hdgate hdrift hceil hbudget hrow
  set R' : ChowlaRegime := regimeEnlargeX R hx' with hR'def
  have harc8 : ∀ H : ℕ, R'.Hlo ≤ H → H ≤ R'.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R') hlo
    nlinarith [h1, harc1]
  have harc : ∀ H : ℕ, R'.Hlo ≤ H → H ≤ R'.Hhi → 128 * arcDen 12 H ^ 2 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R') hlo
    nlinarith [h1, harc1]
  have hchi : M4ChiSummedBlockMeanSqN_L_gk K R' M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied_L_gk K j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummed_L_gk K (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  have hcov := m4_cover_assembly_blk2_L_gk K hgates hBblk0 hblk2
  refine hR x' hx' hxc Braw Bceil δ M k hgates hBraw0 ?_ hceil hbudget
  refine m4_sievedDoorSq_of_blk2_L_gk K (ℓ := blockLen)
    (fun H => by have := hBblk0 H; positivity)
    (fun H q _ _ _ _ => one_le_blockLen H q) ?_ ?_ ?_ ?_ hcov
  · intro H q hlo hhi _ _
    have h1 := harc H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R') hlo
    have hH1 : 1 ≤ H := by
      have : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
      exact_mod_cast this
    exact blockLen_le H q hH1
  · intro H q hlo hhi _ _
    exact blockLen_narrow (R := R') hlo (harc H hlo hhi)
  · intro H q hlo hhi hq _
    exact blockLen_drift (R := R') hlo hq (harc H hlo hhi)
  · intro H hlo hhi
    have h := hdrift H hlo hhi
    have hres0 : (0 : ℝ) ≤ strataResidual H :=
      strataResidual_nonneg (one_le_arcDen_of_regime (R := R') hlo)
    have hB := hBcl0 H
    nlinarith [h]

/-- **⟦ARM R H3→H4⟧** (`flat_capstone_generic_epsW_band`) — rung 2's
`flat_capstone_generic_epsW` (`:5086`) at the band forms.  `Awin` and `hband` are unchanged; the
whole spine — the constant-pool fuse, the row bundle, the share table and the four gates — runs
at `R'`.  ONE step is not the source's token for token, and it is an instrument difference rather
than a mathematical one: the source closes `0 < H` by `have := R.hHlo_floor; omega`, and with the
enlarged regime bound by `set` that projection is no longer an omega atom, so the bound is taken
to `H` itself first (`le_trans R'.hHlo_floor hlo`) and omega is handed a fact about `H` alone.
Same two facts, one `le_trans` apart. -/
theorem flat_capstone_generic_epsW_band (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatRoadFormEpsW_band ε c P) (Awin : ℝ) (hband : S16BandLaneCBoundedL_winU Awin) :
    FlatCapstoneFormEpsW_band ε c P Awin := by
  unfold FlatCapstoneFormEpsW_band
  obtain ⟨Cg, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hKcb, hδ₀, hc1, hεpin, hδpin, hβ, hroadU⟩ :=
    h
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  refine ⟨Cg, Kc, δ₀, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, s11GradeFloor_one_le _, hCgle,
    hc1, hεpin, hδpin, hKcb,
    (fun A hA162 hAw => flatDoorM_gradeFloor_win hA162 hCband0 (by linarith)),
    hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_L_gk_ceiling_kwide K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge hAL
  obtain ⟨Hcap, hCapLe, hroad⟩ := hroadU K A hA26 hAge hAL
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRωtight, hRxtight, hll, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g hg
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRx, hRωtight, hRxtight, hll,
    hRtow, by omega, ?_⟩
  intro x' hx' hxc M hMfloor hKw
  set R' : ChowlaRegime := regimeEnlargeX R hx' with hR'def
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit K M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R'.Hlo ≤ H → H ≤ R'.Hhi →
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
  have hbase : ∀ H L q j A s : ℕ, SocketBaseL R' M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_L_gk K R' M
      (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R' M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R' C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho_L M ρ
  have hceilconj : ∀ H : ℕ, R'.Hlo ≤ H → H ≤ R'.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR x' hx' hxc δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R') hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      -- `set`-bound `R'` is not an omega atom the way the source's `R` is: give omega the
      -- bound on `H` itself rather than on `R'.Hlo`.  Same two facts, one `le_trans` apart.
      have h4 : 4000000 ≤ H := le_trans R'.hHlo_floor hlo
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R') hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
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


/-! ## §6 — the conditional hop, and the ONE export block: tier A → tier B

Rung 2's conditional hop (`FlatDoorEpsRung2.lean:5250`) at the band forms.  It is the only hop
of this file that does arithmetic rather than pass a conjunct through, and the arithmetic is
forced by rule (i-x)'s TWO TIERS: this hop instantiates its source at the INFLATED rider
`g' = s15Arm δ₀ ρ + g`, so the tier-A bound it receives is stated at `g'` and the tier-B bound it
must export is stated at `2 · g`.  The block below is that conversion. -/

/-- **⟦ARM R H4→H5⟧** (`flat_conditional_generic_epsW_band`) — rung 2's
`flat_conditional_generic_epsW` (`FlatDoorEpsRung2.lean:5250`) at the band forms.

THREE THINGS HAPPEN HERE, and only the third is new work:
* the source's `hg'` (the substituted rider `s15Arm δ₀ ρ + g` still obeys the builder-side gate,
  through `xCeilRiderAt_arm_add`) and the whole fire are the source's, token for token, with the
  regime read as `regimeEnlargeX R hx'` inside the band block and the arm's demotion discharged
  at `x'` rather than at `R.x` (`hRarm' := le_trans hRarm hx'`);
* the (i-ω) export `hRωtight` passes through unchanged — `ω` is untouched by the enlargement and
  by the rider — and so does the tower conjunct;
* ⟦S-1 (i-x) TIER A → TIER B⟧ the rider inflation, paid at the arm's own slack.  The capstone
  band form hands us `log R.x ≤ max (xTightCeil ε R.Hhi) (log (g' R.Hhi R.ω))` at `g' = arm + g`;
  the conditional band form demands `log R.x ≤ max (xTightCeilArm ε R.Hhi) (log (2 · g R.Hhi
  R.ω))`.  `xTightCeilArm = xTightCeil + 18 + log 2 + H₊/10²⁰` (`TierSBand.lean:95`), and at
  stride 1 this hop spends only `log 2 + H₊/10²⁰` of that — the `18` is the landed definition's
  slack for the stride lane's two `log (·) ≤ 9` shifts, which do not exist here.  The case split
  is on which summand of `g'` is the larger: at the arm, `log (arm + g) ≤ log 2 + log arm ≤
  log 2 + log ω + H₊/10²⁰ ≤ xTightCeilArm` by `s15Arm_log_le_L_cut20` and the (i-ω) export; at
  `g`, `arm + g ≤ 2 · g` in ℕ and the `max`'s right arm takes it.  The gate hypothesis
  `50 + log c ≤ loglog R.Hhi` that the arm lemma needs is the (i-gate) conjunct the builder twin
  B2′ of §3 exports and the five tier-A forms carry; THIS hop is what spends it, and `log c` does
  NOT reach the conclusion — it is consumed entirely inside the arm's own cut.

The landed precedent is the stride lane's conditional band hop (`TierSBand.lean:1149`, the block
opening ⟦S-1 (i-x) TIER A → TIER B⟧); this transcription drops that block's `a` multiplier
throughout (no `Real.log_mul`, no zero-product case) and its `log h` term, and reads the arm
through `s15Arm_log_le_L_cut20` instead of `s15ArmH_log_le_g12b`.

⚠️ ONE STEP IS NOT THE SOURCE'S TOKEN FOR TOKEN, and it is the instrument difference half 1 paid
twice: the two `MSelect'`-derived gates are fired at the enlarged regime, whose `Hhi` projection
is not the same ATOM as `R.Hhi`, so each `by linarith` gains a `simp only [regimeEnlargeX_Hhi]`
in front.  Same two facts, one rewrite apart.  Nothing here bears on twin primes. -/
theorem flat_conditional_generic_epsW_band (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ)
    (h : FlatCapstoneFormEpsW_band ε c P Awin) :
    FlatConditionalFormEpsW_band ε c P Awin := by
  unfold FlatConditionalFormEpsW_band
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hCg, hε, hKc, hδ₀, hMfl,
    hCgle, hc1, hεpin, hδpin, hKcb, hMflb, hβ, hcapU⟩ :=
    h
  refine ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl,
    hCgle, hc1, hεpin, hδpin, hKcb, hMflb, hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcapK⟩ := hcapU K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge hAL
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapK A hA26 hAge hAL
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  have hLc0 : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast hc1)
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hg' : XCeilRiderAt (50 + Real.log (c : ℝ)) ε
      (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω) :=
    xCeilRiderAt_arm_add hc1 hεpin hLc0 le_rfl hδ₀ hδpin hKc
      (epsRung2_one_le_Kb hc1) hKcb (epsRung2_log_Kb_le hc1) hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRωtight, hRxtight, hgate, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω) hg'
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRx, hRωtight, ?_, hRtow, ?_⟩
  · -- the tier A to tier B export
    have hH4R : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
    have harmR : Real.log ((s15Arm δ₀ ρ R.Hhi R.ω : ℕ) : ℝ)
        ≤ Real.log ((R.ω : ℕ) : ℝ) + ((R.Hhi : ℕ) : ℝ) / 10 ^ 20 := by
      rw [hρdef, hδsdef]
      exact s15Arm_log_le_L_cut20 (c := ((c : ℕ) : ℝ)) hcR1 hLc0 le_rfl hδ₀ hδpin hKc
        (epsRung2_one_le_Kb hc1) hKcb (epsRung2_log_Kb_le hc1) hH4R hgate
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
    · rcases le_total (g R.Hhi R.ω) (s15Arm δ₀ ρ R.Hhi R.ω) with hge | hgg
      · refine le_trans hB (le_trans ?_ (le_max_left _ _))
        have hsum : Real.log (((s15Arm δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω : ℕ)) : ℝ)
            ≤ Real.log 2 + Real.log ((s15Arm δ₀ ρ R.Hhi R.ω : ℕ) : ℝ) :=
          xt_log_add_le le_rfl (hlogmono hge)
        unfold xTightCeilArm
        linarith [hRωtight]
      · refine le_trans hB (le_trans ?_ (le_max_right _ _))
        refine hlogmono ?_
        omega
  intro x' hx' hxc M hsel hKw
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire x' hx' hxc M hsel.mfloor hKw
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hRarm' : s15Arm δ₀ ρ R.Hhi R.ω ≤ x' := le_trans hRarm hx'
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ x' :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm'
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ ((x' : ℕ) : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm')
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  have harith := s15_doorArithFrameRho_L_family'' (R := regimeEnlargeX R hx')
    (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1 hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ
      (regimeEnlargeX R hx') M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by simp only [regimeEnlargeX_Hhi]; linarith))
  have hbgate : S13BandGate'_L_gk K (regimeEnlargeX R hx') M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_L_gk_T K hfl hsel hgrade
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 (regimeEnlargeX R hx') ρ (fun _ => (1 : ℝ)))
    (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount (regimeEnlargeX R hx').ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_gen le_rfl (s13_g2_jfloor_of_MSelect'_L_gk K
      (by simp only [regimeEnlargeX_Hhi]; linarith) hS))
    (s13_gate8_L_gk le_rfl (s13_gate8_of_MSelect'_L_gk K
      (by simp only [regimeEnlargeX_Hhi]; linarith) hS))
    (s13_smallGradeFits_of_MSelect'_L_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket_L hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorL_gk_T K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat_T hfl (socketBase_of_socketBaseL hsel.hM hb) hlam50 htow
        hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flat_T hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flat_T hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM (hbgate.block H L q j A s hb)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_L_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hbgate)
    harith


end Salt.MR

end
