import Salt.MR.M4Gauss
import Salt.MR.M4BridgePhase

/-!
# The door's road, COMPOSED across its first seam

The door's chain was walked link-by-link and every link was found to have producers
(`MRTPropA3.lean`, the "five links deep" section).  What was **not** measured there is whether
the links **compose** — and that is precisely the gap a green build cannot see: *the kernel
checks theorems, not that they compose.*

This file closes that gap for the first seam, in the kernel rather than in prose.  It joins

* `norm_absWindowSum_le_drift_tight` (`M4BridgePhase`) — phase drift from an arbitrary `α`
  at a tight major arc down to a rational `b/q`, landing on `subWindowSup`, and
* `subWindowSup_sq_le_strata` (`M4Gauss`) — the Gauss/strata bound at `doorSievedCoeff M`,

into one statement about `absWindowSum` directly.  The seam that had to line up is the
modulus cap: `drift_tight` **produces** `(q : ℝ) ≤ arcDen B₅ H`, and `strata` **consumes**
`(q : ℝ) ≤ W`.  Instantiating `W := arcDen B₅ H` makes the produced fact *be* the consumed
one — so the two arcs' denominators are the same object, not merely similarly named.

That is the whole content of a composition check, and it is the kind of thing that stays
invisible until someone writes the composed statement down.
-/

namespace Salt.MR

/-- **THE FIRST SEAM OF THE DOOR'S ROAD, KERNEL-CHECKED.**  At a tight major arc, the door's
sieved window sum is bounded — squared — by the weighted stratum budgets, with the drift
constant carried through.  The arc's own witness denominator `q` is shared by both halves:
`drift_tight` hands out `(q : ℝ) ≤ arcDen B₅ H` and `strata` takes it in at `W := arcDen B₅ H`.

⭐ **The numerator `b` is deliberately NOT in the conclusion.**  The first draft carried
`∃ (b : ℤ) (q : ℕ), …` and the unused-variable linter flagged `b` as unreferenced — which is a
statement-level fact, not a style nit: the stratum budgets are summed over ALL residues, so the
bound depends only on the arc's DENOMINATOR.  Carrying `∃ b` would have implied the estimate is
tied to a particular rational approximant when it is not. -/
theorem door_absWindowSum_sq_le_strata {M n H : ℕ} {B₅ α : ℝ}
    (hM : 1 ≤ M) (hH : 0 < H)
    (hW : arcDen B₅ H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
    (hα : NearRatTight (arcDen B₅ H) H α) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ arcDen B₅ H ∧
      ‖absWindowSum (doorSievedCoeff M) H n α‖ ^ 2
        ≤ (1 + 2 * Real.pi * (arcDen B₅ H / (q : ℝ))) ^ 2
          * ((∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
              * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm M q H d n) := by
  obtain ⟨b, q, hq, hqA, hbound⟩ :=
    norm_absWindowSum_le_drift_tight (B₅ := B₅) (H := H) (n := n) hH hα (doorSievedCoeff M)
  refine ⟨q, hq, hqA, ?_⟩
  -- ⟦THE SEAM⟧ `strata` is instantiated at `W := arcDen B₅ H`, so `hqA` IS its `hqW`.
  have hstrata := subWindowSup_sq_le_strata (M := M) (n := n) (q := q) (L := H)
    (W := arcDen B₅ H) hM hq hqA hW b
  calc ‖absWindowSum (doorSievedCoeff M) H n α‖ ^ 2
      ≤ ((1 + 2 * Real.pi * (arcDen B₅ H / (q : ℝ)))
            * subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = (1 + 2 * Real.pi * (arcDen B₅ H / (q : ℝ))) ^ 2
          * (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2 := by ring
    _ ≤ (1 + 2 * Real.pi * (arcDen B₅ H / (q : ℝ))) ^ 2
          * ((∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
              * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm M q H d n) :=
        mul_le_mul_of_nonneg_left hstrata (sq_nonneg _)

end Salt.MR
