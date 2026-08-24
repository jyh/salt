/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MRTProp24

/-!
# A pointwise floor transports to `mrtQuality`

`mrtQuality g X Q` (`Salt/MR/MRTProp24.lean:187-189`) is the infimum of
`pretDistSq g (chiTwist χ t) X` over the **triple** `(t, q, χ)` cut out by
`|t| ≤ X ∧ 1 ≤ q ∧ (q : ℝ) ≤ Q`.  This file records the `le_csInf` half of that
transport: a floor holding **pointwise, uniformly over the whole index set** is a
floor on the infimum.

⛔ **Both guards are load-bearing.**  `hX : 0 ≤ X` and `hQ : (1 : ℝ) ≤ Q` are what
make the index set nonempty, via the triple `(t, q, χ) = (0, 1, 1)`: `hX` is spent
on `|0| ≤ X` and `hQ` on `((1 : ℕ) : ℝ) ≤ Q`.  Drop either one and the set can be
empty; `Real.sInf ∅ = 0` in mathlib, so the pointwise hypothesis becomes vacuous and
**any `c > 0` refutes the conclusion** — the statement would be FALSE, not merely
unproved.  The witness character is mathlib's `(1 : DirichletCharacter ℂ 1)`; it is
**not** `chiPrin` (`Salt/MR/ChiFloor.lean:188`), which is `ℕ → ℂ` — the character
already applied and coerced — and cannot inhabit the `χ` binder.

The corpus's own landed instance of exactly this move is `mrtM_nonneg`
(`Salt/MR/MRTPropA3.lean:2595`), which likewise spends its `hX` on the nonemptiness
witness; this proof is modelled on it.

⚠️ **Scope.**  This closes the `le_csInf` half only.  The **index-uniformity** half is
untouched: the landed twisted floors — e.g. `chi_floor_all_unconditional_twisted`
(`Salt/MR/ChiLLower.lean:720-729`) — carry `((2 * orderOf χ : ℕ) : ℝ) ^ 2` in a
denominator and a `primeDivSum q X` term, so they are **not** uniform in the
`(t, q, χ)` this lemma quantifies over.  The lemma is therefore **true but inert**
until a floor uniform in that index exists to feed its hypothesis.
-/

namespace Salt.MR

/-- **A pointwise floor over the whole index set is a floor on `mrtQuality`.**
`c ≤ pretDistSq g (chiTwist χ t) X` for every admissible triple `(t, q, χ)` gives
`c ≤ mrtQuality g X Q`, by `le_csInf` with the `(0, 1, 1)` nonemptiness witness.
`hX` and `hQ` are exactly what that witness costs — see the module docstring. -/
theorem mrtQuality_lower_of_pointwise {g : ℕ → ℂ} {X Q c : ℝ}
    (hX : 0 ≤ X) (hQ : (1 : ℝ) ≤ Q)
    (h : ∀ (t : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q),
        |t| ≤ X → 1 ≤ q → (q : ℝ) ≤ Q → c ≤ pretDistSq g (chiTwist χ t) X) :
    c ≤ mrtQuality g X Q := by
  unfold mrtQuality
  refine le_csInf ⟨pretDistSq g (chiTwist (1 : DirichletCharacter ℂ 1) 0) X,
    ⟨0, 1, (1 : DirichletCharacter ℂ 1), by simpa using hX, le_refl 1,
      by simpa using hQ, rfl⟩⟩ ?_
  rintro b ⟨t, q, χ, ht, hq, hqQ, rfl⟩
  exact h t q χ ht hq hqQ

end Salt.MR
