/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FlatDoorAllGrades
import Salt.MR.TierSBand
import Mathlib

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

end Salt.MR

end
