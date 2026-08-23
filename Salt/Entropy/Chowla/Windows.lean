/-
Copyright (c) 2026 The Salt project contributors.
Released under the Apache License, Version 2.0.

The Liouville window pattern for the Tao (arXiv:1509.05422v2) §3 entropy-decrement spine
(sprint-3 wave I, node S3-A2-D-b). This file introduces the window random
variable, its finite-range / measurability infrastructure, the window entropy
ceiling (the (3.8) Liouville form), and the pointwise block-splitting identity
that Wave II's concatenation step consumes.
-/
import Mathlib
import Salt.Entropy.Basic
import Salt.Entropy.Measure

/-!
# Liouville window patterns (Chowla / entropy-decrement spine)

`liouvilleWindow H n = (λ(n+1), …, λ(n+H))` is the length-`H` window of Liouville
values starting just above `n`, viewed as a random variable in `n`.  Its range
sits inside `{-1, 1}^H` (Liouville is `±1`-valued on positive arguments), giving
the entropy ceiling `H[X_H ; μ] ≤ H · log 2`.
-/

open MeasureTheory ProbabilityTheory Real

/-- The Liouville window pattern: `liouvilleWindow H n i = λ(n + i + 1)`. -/
def liouvilleWindow (H : ℕ) (n : ℕ) : Fin H → ℤ :=
  fun i => ArithmeticFunction.liouville (n + i + 1)

@[simp] lemma liouvilleWindow_apply (H n : ℕ) (i : Fin H) :
    liouvilleWindow H n i = ArithmeticFunction.liouville (n + i + 1) := rfl

/-- Every Liouville value on a positive argument lies in `{-1, 1}`. -/
lemma liouville_mem_pm_one {m : ℕ} (hm : m ≠ 0) :
    ArithmeticFunction.liouville m ∈ ({-1, 1} : Finset ℤ) := by
  rw [ArithmeticFunction.liouville_apply hm]
  rcases Nat.even_or_odd (ArithmeticFunction.cardFactors m) with he | ho
  · rw [he.neg_one_pow]; simp
  · rw [ho.neg_one_pow]; simp

/-- The window pattern lands in the product Finset of `{-1, 1}`-valued tuples. -/
lemma liouvilleWindow_mem_piFinset (H n : ℕ) :
    liouvilleWindow H n ∈ Fintype.piFinset (fun _ : Fin H => ({-1, 1} : Finset ℤ)) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [liouvilleWindow_apply]
  exact liouville_mem_pm_one (by omega)

/-- The Liouville window has finite range (contained in `{-1, 1}^H`). -/
instance instFiniteRangeLiouvilleWindow (H : ℕ) : FiniteRange (liouvilleWindow H) :=
  finiteRange_of_finset (liouvilleWindow H)
    (Fintype.piFinset (fun _ : Fin H => ({-1, 1} : Finset ℤ)))
    (liouvilleWindow_mem_piFinset H)

/-- The Liouville window is measurable (its domain `ℕ` is discrete/countable). -/
lemma measurable_liouvilleWindow (H : ℕ) : Measurable (liouvilleWindow H) :=
  measurable_of_countable _

/-- **The window entropy ceiling (Tao (3.8), Liouville form).**
For any measure `μ` on `ℕ`, the Liouville window `X_H` has entropy at most
`H · log 2`, since its range has at most `2 ^ H` points. -/
lemma entropy_liouvilleWindow_le (H : ℕ) (μ : Measure ℕ) :
    H[liouvilleWindow H ; μ] ≤ (H : ℝ) * Real.log 2 := by
  have hA : (μ.map (liouvilleWindow H))
      ((Fintype.piFinset (fun _ : Fin H => ({-1, 1} : Finset ℤ)) : Set (Fin H → ℤ)))ᶜ = 0 := by
    have hpre : (liouvilleWindow H) ⁻¹'
        ((Fintype.piFinset (fun _ : Fin H => ({-1, 1} : Finset ℤ)) : Set (Fin H → ℤ)))ᶜ = ∅ := by
      ext n
      simp only [Set.mem_preimage, Set.mem_compl_iff, Finset.mem_coe, Set.mem_empty_iff_false,
        iff_false, not_not]
      exact liouvilleWindow_mem_piFinset H n
    rw [Measure.map_apply (measurable_liouvilleWindow H) (Finset.measurableSet _).compl, hpre,
      measure_empty]
  rw [entropy_def]
  have h2 : (({-1, 1} : Finset ℤ)).card = 2 := Finset.card_pair_eq_two_iff.mpr (by norm_num)
  calc Hm[μ.map (liouvilleWindow H)]
      ≤ Real.log ((Fintype.piFinset (fun _ : Fin H => ({-1, 1} : Finset ℤ))).card : ℝ) :=
        measureEntropy_le_log_card_of_mem (μ.map (liouvilleWindow H)) hA
    _ = (H : ℝ) * Real.log 2 := by
        have hcard : (Fintype.piFinset (fun _ : Fin H => ({-1, 1} : Finset ℤ))).card = 2 ^ H := by
          rw [Fintype.card_piFinset_const, h2]
        rw [hcard]; push_cast; rw [Real.log_pow]

/-- **Block-splitting identity (Wave II concatenation keystone).**
The `k·H`-window at base `n`, reindexed by `Fin k × Fin H ≃ Fin (k*H)` via
`finProdFinEquiv`, is the `H`-window at the shifted base `n + b·H`. -/
lemma liouvilleWindow_block (k H n : ℕ) (b : Fin k) (j : Fin H) :
    liouvilleWindow (k * H) n (finProdFinEquiv (b, j)) = liouvilleWindow H (n + b * H) j := by
  simp only [liouvilleWindow_apply]
  congr 1
  have hval : ((finProdFinEquiv (b, j) : Fin (k * H)) : ℕ) = (j : ℕ) + H * (b : ℕ) := rfl
  rw [hval]; ring
