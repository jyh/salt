/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.Capstone105
import Salt.MaynardK.Slack105
import Salt.MaynardK.Tuple600

/-!
# Bounded gaps between primes with gap at most 600 (C1 · B5)

Maynard's Theorem 1.3 (arXiv:1311.4600v3, p. 3), gap at most 600: the same k = 105 run as
`Gaps636`, with Engelsma's admissible 105-tuple of diameter 600 (`Cert105.H600`, the `k = 105`
entry of Sutherland's table of narrow admissible tuples; its admissibility is checked by the
kernel) in place of the first 105 primes greater than 105. The chain is generic in the tuple
(`TupleChoice`); here it is instantiated at `engelsmaTuple` (`Tuple600`), whose entries are
`≤ 600 ≤ 743` and whose diameter is `≤ 600`.

* `maynard_105_tuple600` — infinitely many `n` with at least two primes among `n + h`, `h` in
  Engelsma's tuple;
* `gaps_le_600` — infinitely many pairs of distinct primes at distance at most 600.

Both carry no hypotheses: `windowPNT_holds` and `hasLevel_half_of_siegelWalfisz
siegelWalfisz_holds` are discharged inside, as for `gaps_le_636`.
Nothing here bears on twin primes.
-/

namespace Salt.MaynardK

open Salt.Maynard

/-- **Maynard, k = 105, on Engelsma's tuple (tuple form).** -/
theorem maynard_105_tuple600 : ∀ N : ℕ, ∃ n : ℕ, N < n ∧
    2 ≤ (Finset.univ.filter (fun i : Fin 105 => (n + h600 i).Prime)).card := by
  have h := @maynard_105_of_slack engelsmaTuple
    (@winSlackM105_ev engelsmaTuple hSeq_engelsma_le_743) hSeq_engelsma_le_743
  simpa only [hSeq_engelsma_105] using h

/-- **Bounded gaps between primes: gap at most 600** (Maynard's Theorem 1.3). -/
theorem gaps_le_600 : ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
    (q : ℤ) - (p : ℤ) ∈ Set.Icc (-600 : ℤ) 600 :=
  @gaps_le_of_slack engelsmaTuple (@winSlackM105_ev engelsmaTuple hSeq_engelsma_le_743)
    hSeq_engelsma_le_743 600 hSeq_engelsma_diam_le_600

end Salt.MaynardK
