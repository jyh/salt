/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.Defs

/-!
# Large sieve track, nodes L7.1 + L7.2: the Gauss-sum machinery

Blueprint: `docs/blueprints/largesieve.md` (W4, character form).

Work over a primitive Dirichlet character `χ : DirichletCharacter ℂ q` (`q ≥ 1`,
composite allowed) and the standard primitive additive character
`ψ = ZMod.stdAddChar : AddChar (ZMod q) ℂ`, `ψ j = exp (2πi j / q)`.

* **L7.2** (`gaussSum_normSq_of_primitive`, specialised as `gaussSum_normSq`):
  `‖gaussSum χ ψ‖² = q` for **all** `q` (not just prime). mathlib's
  `gaussSum_mul_gaussSum_eq_card` is `[Field R]`-only, so we take the
  Parseval-over-residues route that works at composite moduli. Compute
  `T := ∑_{n : ZMod q} ‖gaussSum χ (ψ.mulShift n)‖²` two ways:
  - via `gaussSum_mulShift_of_isPrimitive`, `gaussSum χ (ψ.mulShift n) = χ⁻¹ n · τ`,
    so `T = (∑_a ‖χ a‖²) · ‖τ‖²`;
  - expanding the square and using additive-character orthogonality
    (`AddChar.sum_mulShift`), `∑_n ψ(n·(a−b)) = q·δ_{a,b}`, so `T = q · ∑_a ‖χ a‖²`.
  Equate and cancel the positive factor `∑_a ‖χ a‖²` (its `a = 1` term is `1`).
  The argument never computes `φ(q)` and holds for any primitive additive
  character.

* **L7.1** (`dirichlet_inversion`, `dirichlet_inversion'`): the Gauss-sum
  inversion `∑_a χ⁻¹ a · ψ(n·a) = χ n · gaussSum χ⁻¹ ψ`, i.e.
  `gaussSum_mulShift_of_isPrimitive` at the primitive character `χ⁻¹`
  (`conductor_inv` gives primitivity of the inverse). Solving for `χ n` uses
  `gaussSum χ⁻¹ ψ ≠ 0` (`gaussSum_ne_zero`, itself from L7.2 and `q ≥ 1`).

* **The `e`-bridge** (`stdAddChar_eq_e`): `ψ a = e (a.val / q)`, connecting
  mathlib's `stdAddChar`/`toCircle` plumbing to the track carrier
  `e x = exp (2πi x)`. This lets L7.3 rewrite `∑_a χ⁻¹ a · ψ(n·a)` as an
  `expSum`-style evaluation at the Farey point `n/q`.
-/

namespace Salt.LS

open scoped BigOperators
open AddChar DirichletCharacter ComplexConjugate

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-! ### L7.2 — `‖gaussSum χ ψ‖² = q` for primitive `χ`, all `q` -/

/-- **L7.2 (general additive character).** For a primitive Dirichlet character `χ`
and *any* primitive additive character `ψ` on `ZMod q`, `‖gaussSum χ ψ‖² = q`
(with `q` arbitrary — composite included). -/
theorem gaussSum_normSq_of_primitive (hχ : χ.IsPrimitive)
    {ψ : AddChar (ZMod q) ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (q : ℝ) := by
  -- `conj (ψ x) = ψ (-x)`, from primitivity/roots-of-unity.
  have hR : 0 < ringChar (ZMod q) := by
    rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne q)
  have hψconj : ∀ x : ZMod q, conj (ψ x) = ψ (-x) := fun x => by
    rw [AddChar.starComp_apply hR, AddChar.inv_apply]
  -- `conj (χ n) = χ⁻¹ n` and the norm-symmetry `χ⁻¹ n · conj (χ⁻¹ n) = χ n · conj (χ n)`.
  have hconj : ∀ n : ZMod q, conj (χ n) = χ⁻¹ n := fun n => by
    rw [starRingEnd_apply, MulChar.star_apply']
  have hnn : ∀ n : ZMod q, χ⁻¹ n * conj (χ⁻¹ n) = χ n * conj (χ n) := fun n => by
    rw [← hconj n, Complex.conj_conj]; ring
  -- shift relation `gaussSum χ (ψ.mulShift n) = χ⁻¹ n · gaussSum χ ψ`.
  have hG : ∀ n : ZMod q, gaussSum χ (ψ.mulShift n) = χ⁻¹ n * gaussSum χ ψ :=
    fun n => gaussSum_mulShift_of_isPrimitive ψ hχ n
  -- `gaussSum χ (ψ.mulShift n)` expands definitionally.
  have hexp : ∀ n : ZMod q,
      gaussSum χ (ψ.mulShift n) = ∑ a : ZMod q, χ a * ψ (n * a) := fun _ => rfl
  -- expansion of `‖gaussSum χ (ψ.mulShift n)‖²` as a double sum.
  have Gn_conj : ∀ n : ZMod q,
      gaussSum χ (ψ.mulShift n) * conj (gaussSum χ (ψ.mulShift n))
        = ∑ a : ZMod q, ∑ b : ZMod q, χ a * conj (χ b) * ψ (n * (a - b)) := by
    intro n
    rw [hexp n, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul (starRingEnd ℂ), hψconj (n * b)]
    have hcomb : ψ (n * a) * ψ (-(n * b)) = ψ (n * (a - b)) := by
      rw [← AddChar.map_add_eq_mul, show n * a + -(n * b) = n * (a - b) from by ring]
    calc χ a * ψ (n * a) * (conj (χ b) * ψ (-(n * b)))
        = χ a * conj (χ b) * (ψ (n * a) * ψ (-(n * b))) := by ring
      _ = χ a * conj (χ b) * ψ (n * (a - b)) := by rw [hcomb]
  -- Way 2: `T = q · ∑_a χ a · conj (χ a)` (additive orthogonality).
  have hI : ∑ n : ZMod q, gaussSum χ (ψ.mulShift n) * conj (gaussSum χ (ψ.mulShift n))
      = (q : ℂ) * ∑ a : ZMod q, χ a * conj (χ a) := by
    simp_rw [Gn_conj]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    -- collapse the inner `∑_n` via additive orthogonality
    have hstep : ∀ b : ZMod q,
        ∑ n : ZMod q, χ a * conj (χ b) * ψ (n * (a - b))
          = χ a * conj (χ b) * (if a = b then (q : ℂ) else 0) := fun b => by
      rw [← Finset.mul_sum, AddChar.sum_mulShift (a - b) hψ, ZMod.card]
      congr 1
      simp only [Nat.cast_ite, Nat.cast_zero, sub_eq_zero]
    simp_rw [hstep, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ a (fun b => χ a * conj (χ b) * (q : ℂ))]
    rw [if_pos (Finset.mem_univ a)]
    ring
  -- Way 1: `T = (∑_a χ a · conj (χ a)) · (gaussSum χ ψ · conj (gaussSum χ ψ))`.
  have hII : ∑ n : ZMod q, gaussSum χ (ψ.mulShift n) * conj (gaussSum χ (ψ.mulShift n))
      = (∑ a : ZMod q, χ a * conj (χ a)) * (gaussSum χ ψ * conj (gaussSum χ ψ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hG n, map_mul, ← hnn n]
    ring
  -- Equate the two computations.
  have key : (∑ a : ZMod q, χ a * conj (χ a)) * (gaussSum χ ψ * conj (gaussSum χ ψ))
      = (q : ℂ) * ∑ a : ZMod q, χ a * conj (χ a) := by rw [← hII, hI]
  -- Descend to `ℝ`: both `∑_a χ a conj (χ a)` and `τ conj τ` are real casts.
  have hSumCast : (∑ a : ZMod q, χ a * conj (χ a))
      = ((∑ a : ZMod q, ‖χ a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_conj']; norm_cast
  have hτ : gaussSum χ ψ * conj (gaussSum χ ψ) = ((‖gaussSum χ ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; norm_cast
  rw [hSumCast, hτ] at key
  have keyR : (∑ a : ZMod q, ‖χ a‖ ^ 2) * ‖gaussSum χ ψ‖ ^ 2
      = (q : ℝ) * ∑ a : ZMod q, ‖χ a‖ ^ 2 := by exact_mod_cast key
  -- `∑_a ‖χ a‖² > 0` (the `a = 1` term is `1`), so we may cancel it.
  have hS : (∑ a : ZMod q, ‖χ a‖ ^ 2) ≠ 0 := by
    have hpos : 0 < ∑ a : ZMod q, ‖χ a‖ ^ 2 := by
      apply Finset.sum_pos'
      · intro a _; positivity
      · refine ⟨1, Finset.mem_univ 1, ?_⟩
        rw [MulChar.map_one, norm_one]; norm_num
    exact ne_of_gt hpos
  have hcancel : (∑ a : ZMod q, ‖χ a‖ ^ 2) * ‖gaussSum χ ψ‖ ^ 2
      = (∑ a : ZMod q, ‖χ a‖ ^ 2) * (q : ℝ) := by rw [keyR]; ring
  exact mul_left_cancel₀ hS hcancel

/-- **L7.2.** For a primitive Dirichlet character `χ` mod `q` and the standard
additive character, `‖gaussSum χ ψ‖² = q`, for all `q ≥ 1` (composite included). -/
theorem gaussSum_normSq (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)‖ ^ 2 = (q : ℝ) :=
  gaussSum_normSq_of_primitive χ hχ (ZMod.isPrimitive_stdAddChar q)

/-- For primitive `χ`, the Gauss sum with the standard additive character is
nonzero (immediate from L7.2 and `q ≥ 1`). -/
theorem gaussSum_ne_zero (hχ : χ.IsPrimitive) :
    gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) ≠ 0 := by
  have hnorm := gaussSum_normSq χ hχ
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  intro h
  rw [h, norm_zero] at hnorm
  have hq0 : (q : ℝ) = 0 := by rw [← hnorm]; norm_num
  linarith

/-! ### L7.1 — Gauss-sum inversion for primitive `χ` -/

omit [NeZero q] in
/-- `χ⁻¹` is primitive when `χ` is (`conductor_inv`). -/
theorem isPrimitive_inv (hχ : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  have h : χ⁻¹.conductor = q := by rw [DirichletCharacter.conductor_inv]; exact hχ
  exact h

/-- **L7.1 (inversion, sum form).** For primitive `χ` and every `n : ZMod q`
(units and non-units alike),
`∑ a, χ⁻¹ a · ψ (n·a) = χ n · gaussSum χ⁻¹ ψ`. -/
theorem dirichlet_inversion (hχ : χ.IsPrimitive) (n : ZMod q) :
    ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (n * a)
      = χ n * gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
  have hχ' : χ⁻¹.IsPrimitive := isPrimitive_inv χ hχ
  calc ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (n * a)
      = gaussSum χ⁻¹ ((ZMod.stdAddChar : AddChar (ZMod q) ℂ).mulShift n) := by
        simp only [gaussSum, AddChar.mulShift_apply]
    _ = χ n * gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
        rw [gaussSum_mulShift_of_isPrimitive _ hχ', inv_inv]

/-- **L7.1 (inversion, solved for `χ`).** For primitive `χ`,
`χ n = (gaussSum χ⁻¹ ψ)⁻¹ · ∑ a, χ⁻¹ a · ψ (n·a)`. This is the character
LS-expansion form consumed by L7.3. -/
theorem dirichlet_inversion' (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ n = (gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ))⁻¹
        * ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (n * a) := by
  have hχ' : χ⁻¹.IsPrimitive := isPrimitive_inv χ hχ
  rw [dirichlet_inversion χ hχ n, mul_comm (χ n),
    ← mul_assoc, inv_mul_cancel₀ (gaussSum_ne_zero χ⁻¹ hχ'), one_mul]

/-! ### The `e`-bridge -/

/-- **The `e`-bridge (deliverable 3).** mathlib's standard additive character
`ZMod.stdAddChar` on `ZMod q` is the track carrier `e` at the Farey point:
`ψ a = e (a.val / q)`. -/
theorem stdAddChar_eq_e (a : ZMod q) :
    (ZMod.stdAddChar a : ℂ) = e ((a.val : ℝ) / q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp]
  unfold e
  congr 1
  push_cast
  ring

end Salt.LS
