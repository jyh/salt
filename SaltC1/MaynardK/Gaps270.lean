/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.MaynardK.Capstone54
import SaltC1.MaynardK.Slack54
import SaltC1.MaynardK.Tuple54

/-!
# Bounded gaps between primes with gap at most 270 (C1 · A4)

H₁ ≤ 270 via DHL[54, 2]: Polymath 8b (arXiv:1407.4897v4) Thm 3.9(vii) (M₅₄ > 4.00238, p. 14) with
the Bombieri–Vinogradov theorem (p. 14), and H(54) = 270 (Figure 3, p. 75). Here it is the k = 54
run of Maynard's argument (`Capstone54`, `Slack54`, over the certificate `M₅₄ > 4.0015`,
`ratio_cert_54` — the kernel's own bound, which exceeds the 4 that DHL[54, 2] needs), instantiated
at `polymath54Tuple` (`Tuple54`), whose `54`-tuple is `H270`, the `k = 54` entry of Sutherland's
table of narrow admissible tuples and the paper's Figure 3 tuple (p. 75; its admissibility is
checked by the kernel), with entries `≤ 270` and diameter `≤ 270`.

* `maynard_54_tuple270` — infinitely many `n` with at least two primes among `n + h`, `h` in
  `H270`;
* `gaps_le_270` — infinitely many pairs of distinct primes at distance at most 270.

Both carry no hypotheses: `windowPNT_holds` and `hasLevel_half_of_siegelWalfisz
siegelWalfisz_holds` are discharged inside `gaps_le_of_slack` / `maynard_54_of_slack`.
Nothing here bears on twin primes.
-/

namespace SaltC1.MaynardK

open Salt.Maynard

/-- **Maynard at k = 54 on the diameter-270 tuple (tuple form).** -/
theorem maynard_54_tuple270 : ∀ N : ℕ, ∃ n : ℕ, N < n ∧
    2 ≤ (Finset.univ.filter (fun i : Fin 54 => (n + h270 i).Prime)).card := by
  have h := @maynard_54_of_slack polymath54Tuple
    (@winSlackM54_ev polymath54Tuple hSeq_polymath_le_270) hSeq_polymath_le_270
  simpa only [hSeq_polymath_54] using h

/-- **Bounded gaps between primes: gap at most 270.** H₁ ≤ 270 via DHL[54, 2]: Polymath 8b
(arXiv:1407.4897v4) Thm 3.9(vii) (M₅₄ > 4.00238, p. 14) with the Bombieri–Vinogradov theorem
(p. 14), and H(54) = 270 (Figure 3, p. 75). -/
theorem gaps_le_270 : ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
    (q : ℤ) - (p : ℤ) ∈ Set.Icc (-270 : ℤ) 270 :=
  @gaps_le_of_slack polymath54Tuple (@winSlackM54_ev polymath54Tuple hSeq_polymath_le_270)
    hSeq_polymath_le_270 270 hSeq_polymath_diam_le_270

end SaltC1.MaynardK
