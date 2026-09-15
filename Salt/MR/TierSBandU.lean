/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TierSBand
import Mathlib

/-!
# ⟦TIER S — S-3⟧ THE CROWN BAND WITH THE CLASS QUANTIFIER MOVED INWARD (`TierSBandU`)

**STATEMENT-ONLY FREEZE (S-3, salt QUEUE P3 item 11; council 2026-09-14 afternoon ⑩).  HONEST
LABEL, FIRST LINE: NO NEW UNCONDITIONAL THEOREM.**  S-3 restates S-1's crown band
`mrtUniformityXiL2AffW_holds_flat_stride_g12b_band` (`TierSBand.lean:1619`) with the margin `ε`,
the design constant `A` AND the band `(x₀, ω₀, Hhi₀)` bound ABOVE the class quantifier `∀ b < a`.
It exports a uniformity that is already TRUE of every landed witness and STATED by no landed
theorem.  At fixed `z` Tier S is a SECOND PROOF of a terminal that already lands; E2 is
conditional on `MRTDoorAllGrades`, which has no producer; the `∃ε` tripwire is untouched.
Nothing here bears on twin primes.

Every `sorry` below is a FROZEN STATEMENT awaiting the non-author refuter's verdict (council ⑩:
no proof attempt until the statement survives).  The one PROVED declaration is the conservativity
control K, which reads no `sorry`: the class-uniform crown band implies S-1's crown band at every
class, so the re-statement is conservative over what is landed.

WHY THE BAND AND NOT ONLY `A` (the charter's letter names `A`): the full-range consumer D10
(`TwinParityAtomClasses.lean:635`) demands `∀ N ∈ S, ∀ r ∈ admClasses P, AffFullRangeAt P r 2 ε A
((N − r)/P)` — ONE scale `N` for EVERY class at once.  A per-class `A` is absorbed by a finite
`max` over `admClasses P`; a per-class BAND `[x₀(b), exp(31·Hhi₀(b)/ε)/a]` is not — nothing bounds
`Hhi₀(b)` above, so two classes' bands need not overlap and no common `N` is guaranteed.  The
witness that makes `A` `b`-free (the design-constant census, desk MF) is the SAME regime that makes
the band `b`-free, so the statement hoists all five and the consumer's load-bearing one is the band.

THE ROUTE (priced, NOT fired): the landed crown band runs the whole `_g12b` chain at the
`b`-dependent family `bigXiAffD a b h`; the hoist runs it ONCE at the class-UNION family
`bigXiAffU a h` (U0), whose count gate (U2) and arc-tightness (U3) are the per-class ones summed,
and reads each class's door off the union's by subset monotonicity (U1, U4).  No landed file moves.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla

set_option exponentiation.threshold 4000

namespace Salt.MR

/-! ## §0 — the class-union family and its four class-A gates (the route's owed names) -/

/-- **⟦S-3 U0⟧ (def) — THE CLASS-UNION FAMILY.**  At stride `a` and shift `h`, the union over the
classes `b < a` of the grid-restricted affine sets `bigXiAffD a b h` (`StridePair.lean:306`).
`b`-free by construction; each class's set is a subset (U1).  Off the grid (`¬ a ∣ H`) every
member is `∅`, so the union is `∅` there too, as the road's `∀ H ∈ [Hlo, Hhi]` door needs. -/
def bigXiAffU (a h : ℕ) : XiFamily :=
  fun eps H _ => (Finset.range a).biUnion (fun b => bigXiAffD a b h eps H)

/-- **⟦S-3 U1⟧ (class A).**  Each class's set sits inside the union: `Finset.subset_biUnion_of_mem`
at `b ∈ Finset.range a` (`Finset.mem_range.mpr hb`). -/
theorem bigXiAffD_subset_bigXiAffU (a b h : ℕ) (hb : b < a) (eps : ℚ) (H : ℕ) [NeZero H] :
    bigXiAffD a b h eps H ⊆ bigXiAffU a h eps H := by
  sorry

/-- **⟦S-3 U2⟧ (class A) — THE UNION'S COUNT GATE AT THE PIN.**
`bigXiAff_bounded_ceiling_of_pin_b9` (`StrideFork.lean:807`) with `a` copies:
`Finset.card_biUnion_le` + `Finset.sum_le_card_nsmul` over `range a`, each class at
`bigXiAffD_card_le` + `bigXiAff_card_le_mul` (the per-class bound is `a·h·|bigXi|`, `b`-FREE), so
the witness is `a ·` the landed one and `H₀ = 2` again.  The numeral:
`8103 · 32·2^70·500^10·3^40·8103^15 ≤ 2^539` (`2^435.9`, 103 bits spare) — `norm_num`. -/
theorem bigXiAffU_bounded_ceiling_of_pin_b9 (a h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9)
    (ε : ℚ) (hε : ε = 1 / (500 * ((a * h : ℕ) : ℚ))) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 539 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((bigXiAffU a h ε H).card : ℝ) ≤ C := by
  sorry

/-- **⟦S-3 U3⟧ (class A/B) — THE UNION IS ARC-TIGHT.**  `nearRatTight_of_bigXiAffD`
(`StridePairReceipt.lean:605`) at every class, with ONE threshold: its `H₀` is
`nearRatTight_of_bigXiArcTight harc heps`'s (`:520-522`), read at the PLAIN set and `b`-FREE, so
either take `Finset.sup` over `range a` of the per-class thresholds (`Classical.choose` +
`Finset.le_sup`, ~15 lines) or transcribe `nearRatTight_of_bigXiAffArcTight` with `intro b` moved
inside `∃ H₀` (~60 lines, one line moved).  A member of the union is a member of SOME class's set
(`Finset.mem_biUnion`). -/
theorem nearRatTight_of_bigXiAffU {B₅ : ℝ} (harc : BigXiArcTight B₅)
    {eps : ℚ} (heps : 0 < eps) {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXiAffU a h eps H,
      NearRatTight (((a * h : ℕ) : ℝ) * arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)) := by
  sorry

/-- **⟦S-3 U4⟧ (class A) — THE SET DOOR IS MONOTONE UNDER A POINTWISE-SUBSET FAMILY.**  Each
summand of `MRTUniformityXiL2Set` (`StridePair.lean:337`) is `(1/H²)·∫‖…‖²`, non-negative
(`integral_nonneg`, `sq_nonneg`, `norm_nonneg`), so `Finset.sum_le_sum_of_subset_of_nonneg` (the
corpus's own move at `:497`) bounds the sub-family's sum by the family's, at every `H`. -/
theorem mrtUniformityXiL2Set_of_subset (Xi Xi' : XiFamily)
    (hsub : ∀ (eps : ℚ) (H : ℕ) [NeZero H], Xi eps H ⊆ Xi' eps H) (R : ChowlaRegime) (ρ : ℝ)
    (hd : MRTUniformityXiL2Set Xi' R ρ) : MRTUniformityXiL2Set Xi R ρ := by
  sorry

/-! ## §1 — the C2 band at the union (the route's fifth owed name) -/

/-- **⟦S-3 U5⟧ (class A) — C2 AT THE UNION.**  `mrtUniformityXiL2AffSet_holds_flat_floor_g12b_band`
(`TierSBand.lean:1578`) with `bigXiAffD a b h ↦ bigXiAffU a h`: C1's band
(`mrtUniformityXiL2Set_holds_flat_floor_g12b_band`, `:1524`) at shift `a·h`, `harcXi` from U3 at
`bigXiArcTight_twelve`, `hcount` from U2.  BODY: C2's, with the two per-class suppliers swapped for
U2/U3.  No class quantifier anywhere — this is the statement that has `b` nowhere in it. -/
theorem mrtUniformityXiL2AffSet_holds_flat_floor_g12b_band_U (a h : ℕ) (ha : 0 < a) (hh : 0 < h)
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
          ((bigXiAffU a h R.eps H).card : ℝ) ≤ K) ∧
        ∀ (x' : ℕ) (hx' : R.x ≤ x'), a' ∣ x' →
          Real.log ((x' : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
          ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 12 * ((a * h : ℕ) : ℝ) ^ 2) ∧
            MRTUniformityXiL2Set (bigXiAffU a h) (regimeEnlargeX R hx') ρ := by
  sorry

/-! ## §2 — THE STATEMENT: the crown band with `∀ b < a` moved inward -/

/-- **⟦S-3⟧ THE CLASS-UNIFORM CROWN BAND** — `mrtUniformityXiL2AffW_holds_flat_stride_g12b_band`
(`TierSBand.lean:1619`) with `∃ ε A` and `∃ x₀ ω₀ Hhi₀` (and the three exported ceilings on
them) placed ABOVE `∀ b, b < a →`; below that line the statement is the landed one, byte for byte
(`Ra.b = b` included).  What it says that no landed statement says: ONE margin, ONE design constant
and ONE band `[x₀, exp(31·Hhi₀/ε)/a]` at width `ω₀` serve EVERY class `b < a` — which is what D12
(`abs_sum_Icc_le_of_windows`, one `(x₀, ω₀)`) needs per class and D10 needs ACROSS classes (one
scale `N` for all `r ∈ admClasses P`).

Route (`TierSBandU` header; not fired): C2 at the union (U5) in place of C2 at the class, the
crown band's body verbatim to the band witnesses `⟨ε, A, …, Rd.x / a, Rd.ω, Rd.Hhi, …⟩`, then
`intro b hba` and the per-class transport `mrtUniformityXiL2AffW_of_set_b9` (`StridePair.lean:1079`)
with its `hK` from the union's count gate through U1 (`Finset.card_le_card`) and its `hdoor` from
the union's door through U4 ∘ U1.  Everything else in the crown band's proof is `b`-free or
`b`-local (`hb0`, `hbRe`).  The witnesses `ε, A, x₀, ω₀, Hhi₀` are the crown band's own, read at
the union: unchanged in value, chosen once. -/
theorem mrtUniformityXiL2AffW_holds_flat_stride_g12b_band_bU (a h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
      ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ (x₀ ω₀ Hhi₀ : ℕ), 2 ≤ x₀ ∧ 8 ≤ ω₀ ∧ 4000000 ≤ Hhi₀ ∧
        Real.log ((ω₀ : ℕ) : ℝ) ≤ xTightCeil ε Hhi₀ ∧
        Real.log ((x₀ : ℕ) : ℝ) ≤ xTightCeilArm ε Hhi₀ ∧
        Real.log ((a * x₀ : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ) ∧
        ∀ b : ℕ, b < a →
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

/-! ## §3 — the conservativity control K (PROVED; reads no `sorry`) -/

/-- **⟦S-3 K⟧ (class A, PROVED) — CONSERVATIVITY.**  The class-uniform crown band's CONCLUSION,
taken as a hypothesis, implies S-1's crown band's conclusion at every class `b < a`
(`mrtUniformityXiL2AffW_holds_flat_stride_g12b_band`'s, byte for byte): instantiate the inner
`∀ b` at `b` and re-pack.  Stated with the hypothesis spelled out rather than through the `sorry`
above, so its axiom audit is the kernel's three and not `sorryAx`. -/
theorem mrtUniformityXiL2AffW_holds_flat_stride_g12b_band_of_bU (a b h : ℕ) (_ha : 0 < a)
    (_hh : 0 < h) (hba : b < a) (_hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9) (A₀ : ℝ)
    (hU : ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
      ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ (x₀ ω₀ Hhi₀ : ℕ), 2 ≤ x₀ ∧ 8 ≤ ω₀ ∧ 4000000 ≤ Hhi₀ ∧
        Real.log ((ω₀ : ℕ) : ℝ) ≤ xTightCeil ε Hhi₀ ∧
        Real.log ((x₀ : ℕ) : ℝ) ≤ xTightCeilArm ε Hhi₀ ∧
        Real.log ((a * x₀ : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ) ∧
        ∀ b : ℕ, b < a →
        ∀ y : ℕ, x₀ ≤ y → Real.log ((a * y : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ) →
          ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
            Ra.x = y ∧ Ra.ω = ω₀ ∧ Ra.Hhi = Hhi₀ ∧
            flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
            ∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 12 * ((a * h : ℕ) : ℝ) ^ 2) ∧
              1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
              E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
                  * (Real.log (Ra.ω : ℝ) - 1)) ∧
              MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E)) :
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
  obtain ⟨ε, A, hε, hεpin, hεeq, hA162, hA₀A, x₀, ω₀, Hhi₀, hx₀2, hω8, hH4M, hωt, hx₀t, hloose,
    hband⟩ := hU
  exact ⟨ε, A, hε, hεpin, hεeq, hA162, hA₀A, x₀, ω₀, Hhi₀, hx₀2, hω8, hH4M, hωt, hx₀t, hloose,
    hband b hba⟩

end Salt.MR

end
