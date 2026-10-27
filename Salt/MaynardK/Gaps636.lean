/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.Capstone105
import Salt.MaynardK.Slack105
import Salt.MaynardK.Tuple105

/-!
# Bounded gaps between primes with gap at most 636 (C1)

Maynard's proof of Theorem 1.3 (arXiv:1311.4600v3, p. 3; Prop. 4.2 and Prop. 4.3(2),
`M₁₀₅ > 4`) run at k = 105 with the admissible tuple of the first 105 primes greater than 105
(his p. 7 choice), diameter 636, in place of Engelsma's tuple; Theorem 1.3's own bound 600 is
not proved here. Here `hSeq 105 = {107, …, 743}`.

* `maynard_105` — infinitely many `n` with at least two primes among `n + hSeq 105 i`;
* `gaps_le_636` — infinitely many pairs of distinct primes at distance at most 636;
* `gaps_le_636_of_level` — the interface form, from `WindowPNT` and level `1/2`.

The first two carry no hypotheses: `windowPNT_holds` and
`hasLevel_half_of_siegelWalfisz siegelWalfisz_holds` are discharged inside. The engines
(`Slack105`, `Capstone105`, `WinCore105`, `Frontier105`) are generic in the tuple (`TupleChoice`);
this module instantiates them at `stdTuple` with `Tuple105`'s facts (`hSeq_105_le_743`,
`hSeq_diam_le_636`), so every statement here is the standard tuple's, byte for byte.
Nothing here bears on twin primes.
-/

namespace Salt.MaynardK

open Salt.Maynard

/-- **Maynard, k = 105 (tuple form).** -/
theorem maynard_105 : ∀ N : ℕ, ∃ n : ℕ, N < n ∧
    2 ≤ (Finset.univ.filter (fun i : Fin 105 => (n + hSeq 105 i).Prime)).card :=
  maynard_105_of_slack (winSlackM105_ev hSeq_105_le_743) hSeq_105_le_743

/-- **Bounded gaps between primes: gap at most 636.** -/
theorem gaps_le_636 : ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
    (q : ℤ) - (p : ℤ) ∈ Set.Icc (-636 : ℤ) 636 :=
  gaps_le_of_slack (winSlackM105_ev hSeq_105_le_743) hSeq_105_le_743 636 hSeq_diam_le_636

/-- The interface form: gaps at most 636 from `WindowPNT` and level `1/2`. -/
theorem gaps_le_636_of_level (hPNT : WindowPNT) (hLoD : HasLevel (1 / 2)) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-636 : ℤ) 636 :=
  gaps_le_of_level_of_slack (winSlackM105_ev hSeq_105_le_743) hSeq_105_le_743 636
    hSeq_diam_le_636 hPNT hLoD

end Salt.MaynardK
