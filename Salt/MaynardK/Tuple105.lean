/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.Tuple

/-!
# C1 · B4.0a — the chain's own 105-tuple: `hSeq 105 = {107, …, 743}`, diameter 636

`hSeq 105 i = Nat.nth Nat.Prime (27 + i)` (the first 105 primes above 105). Two kernel counts
(`Nat.count Nat.Prime 107 = 27`, `Nat.count Nat.Prime 743 = 131`) and the monotonicity of `Nat.nth`
pin every entry to `[107, 743]`; the diameter bound `636 = 743 − 107` follows by `omega`.
-/

namespace Salt.MaynardK

open Salt.Maynard

lemma count_prime_107 : Nat.count Nat.Prime 107 = 27 := by decide +kernel
lemma count_prime_743 : Nat.count Nat.Prime 743 = 131 := by decide +kernel

lemma firstIdxAboveK_105 : firstIdxAboveK 105 = 27 := by
  unfold firstIdxAboveK; decide +kernel

lemma nth_prime_27 : Nat.nth Nat.Prime 27 = 107 := by
  rw [← count_prime_107]; exact Nat.nth_count (by norm_num)

lemma nth_prime_131 : Nat.nth Nat.Prime 131 = 743 := by
  rw [← count_prime_743]; exact Nat.nth_count (by norm_num)

theorem hSeq_105_bounds (i : Fin 105) : 107 ≤ hSeq 105 i ∧ hSeq 105 i ≤ 743 := by
  have hmono := Nat.nth_strictMono Nat.infinite_setOf_prime
  rw [hSeq_std, firstIdxAboveK_105]
  constructor
  · rw [← nth_prime_27]; exact hmono.monotone (Nat.le_add_right 27 i)
  · rw [← nth_prime_131]; exact hmono.monotone (by omega)

theorem hSeq_105_eq : hSeq 105 ⟨0, by omega⟩ = 107 ∧ hSeq 105 ⟨104, by omega⟩ = 743 := by
  -- `rw [hSeq_std]` rewrites one `i` at a time (the two conjuncts differ in `i`), so pin each side.
  exact ⟨by rw [hSeq_std, firstIdxAboveK_105]; exact nth_prime_27,
         by rw [hSeq_std, firstIdxAboveK_105]; show Nat.nth Nat.Prime (27 + 104) = 743; exact nth_prime_131⟩

theorem hSeq_diam_le_636 (i j : Fin 105) :
    (hSeq 105 j : ℤ) - (hSeq 105 i : ℤ) ∈ Set.Icc (-636 : ℤ) 636 := by
  have hi := hSeq_105_bounds i
  have hj := hSeq_105_bounds j
  rw [Set.mem_Icc]; omega

theorem hSeq_105_lt_D {D : ℕ} (hD : 744 ≤ D) (i : Fin 105) : hSeq 105 i < D := by
  have := hSeq_105_bounds i; omega

end Salt.MaynardK
