/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.SiegelTwin

/-!
# OpenAI's real-zero gap statement, restated, and what it gives `NoSiegelZeros` (dated 2026-10-23)

`DirichletRealZeroGap` restates, at this repository's mathlib, the statement of OpenAI's theorem
`OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap` (file
`lean/OAI/NumberTheory/SiegelZeros/Conclusions/Theorem.lean` of `github.com/openai/math` at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, the revision of 2026-10-08 the statement was read at).
This repository does not import OpenAI's proof, so nothing here depends on it:
`DirichletRealZeroGap` is a hypothesis in this file, and the theorem below is an implication.

The body of the `def` is the text of OpenAI's statement, copied word for word. The `def` stands
before any `open`, so its names resolve as a reader of the source file resolves them, all to
mathlib's: `DirichletCharacter`, `DirichletCharacter.IsPrimitive`, `DirichletCharacter.LFunction`,
`ZMod`, `Complex.im`, `Real.log`, `NeZero`.

`noSiegelZeros_of_realZeroGap` proves that the statement implies `NoSiegelZeros`, with the
constant `min c (log 2)` for OpenAI's `c`. The two statements differ in three binders, and the
proof pays each:
* `3 ≤ q` there against `1 < q` here. The one extra modulus is `q = 2`, where every Dirichlet
  character is trivial, so `χ ≠ 1` has no instance (`eq_one_of_modulus_two`).
* `∀ a, (χ a).im = 0` there against `χ ^ 2 = 1` here. A quadratic character takes the values
  `1` and `-1` on units and `0` elsewhere, all real (`im_eq_zero_of_sq_eq_one`).
* `0 < β` there against no lower bound on `β` here. For `β ≤ 0` the bound `β ≤ 1 − c'/log q`
  is immediate once `c' ≤ log 2 ≤ log q`, which is why the constant is `min c (log 2)`.

OpenAI's theorem is over mathlib `d13f23b7` and this file is over this repository's mathlib
(`360da6fa`). The definitions the statement names directly are the same text at the two versions:
`DirichletCharacter.LFunction` (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:61`),
`DirichletCharacter.IsPrimitive` and `DirichletCharacter.conductor`
(`Mathlib/NumberTheory/DirichletCharacter/Basic.lean:292` and `:246`), read at both pins on
2026-10-09 and again on 2026-10-23. Below them, from `ZMod.LFunction` down, the two versions are
not checked to agree, so OpenAI's theorem does not discharge `DirichletRealZeroGap` here. Whether
Lean's kernel accepts OpenAI's proof of the statement is a separate question about their
repository and is not part of this file. The mathematics is classical, and nothing here claims
priority.
-/

namespace Salt.TwinBar

/-- OpenAI's real-zero gap statement (`exists_absolute_real_zero_gap`, see the module docstring
for the pin), its text word for word: a uniform `c > 0` with `c ≤ (1 − β) log q` at every real
zero `β ∈ (0, 1)` of the `L`-function of a primitive, nontrivial, real-valued character mod
`q ≥ 3`. -/
def DirichletRealZeroGap : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q], 3 ≤ q →
    ∀ χ : DirichletCharacter ℂ q,
      χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
      ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
        c ≤ (1 - β) * Real.log (q : ℝ)

open Complex DirichletCharacter

/-- A quadratic Dirichlet character is real-valued: on a unit its value squares to `1`, so it is
`1` or `-1`; off the units it is `0`. -/
theorem im_eq_zero_of_sq_eq_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) :
    ∀ a : ZMod q, (χ a).im = 0 := by
  intro a
  have h2 : (χ ^ 2) a = χ a ^ 2 := MulChar.pow_apply' χ two_ne_zero a
  rw [hsq] at h2
  by_cases ha : IsUnit a
  · rcases ha with ⟨u, rfl⟩
    rw [MulChar.one_apply_coe] at h2
    have h3 : χ (u : ZMod q) * χ (u : ZMod q) = 1 := by rw [← pow_two]; exact h2.symm
    rcases mul_self_eq_one_iff.mp h3 with h | h <;> simp [h]
  · rw [MulChar.map_nonunit χ ha]; simp

/-- Every Dirichlet character mod `2` is trivial: the unit group of `ZMod 2` has one element
(`φ 2 = 1`). -/
theorem eq_one_of_modulus_two (χ : DirichletCharacter ℂ 2) : χ = 1 := by
  have h1 : Fintype.card (ZMod 2)ˣ = 1 := by
    rw [ZMod.card_units_eq_totient]; decide
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp h1
  apply MulChar.ext
  intro a
  have ha : a = 1 := (hx a).trans (hx 1).symm
  rw [ha]; simp

/-- **The real-zero gap statement implies `NoSiegelZeros`**, with the constant `min c (log 2)`.
For `β ≤ 0` the bound is immediate; for `q = 2` there is no nontrivial character; otherwise
`3 ≤ q` and `0 < β < 1`, and OpenAI's gap transfers, the real-valuedness supplied by
`im_eq_zero_of_sq_eq_one`. -/
theorem noSiegelZeros_of_realZeroGap (h : DirichletRealZeroGap) : NoSiegelZeros := by
  obtain ⟨c, hc, H⟩ := h
  refine ⟨min c (Real.log 2), lt_min hc (Real.log_pos (by norm_num)), ?_⟩
  intro q _ χ hq hprim hsq hne β hL hβ1
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hlog2 : Real.log 2 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) hq2
  by_cases hβ0 : β ≤ 0
  · -- β ≤ 0: the gap is free, since min c (log 2) ≤ log 2 ≤ log q
    have h3 : min c (Real.log 2) / Real.log (q : ℝ) ≤ 1 := by
      rw [div_le_one hlogq]; exact (min_le_right _ _).trans hlog2
    linarith
  · have hβ0 : 0 < β := lt_of_not_ge hβ0
    rcases Nat.lt_or_ge q 3 with hq3 | hq3
    · -- q = 2: no nontrivial character exists
      exfalso
      have hq2' : q = 2 := by omega
      subst hq2'
      exact hne (eq_one_of_modulus_two χ)
    · -- 3 ≤ q and 0 < β < 1: OpenAI's gap, with the real-valuedness supplied
      have key := H q hq3 χ hprim hne (im_eq_zero_of_sq_eq_one χ hsq) β hβ0 hβ1 hL
      have h4 : min c (Real.log 2) / Real.log (q : ℝ) ≤ 1 - β := by
        rw [div_le_iff₀ hlogq]
        calc min c (Real.log 2) ≤ c := min_le_left _ _
          _ ≤ (1 - β) * Real.log (q : ℝ) := key
      linarith

end Salt.TwinBar
