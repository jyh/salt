/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.Moments
import Mathlib

/-!
# Weil track, node W2T6 (wave 1) — the η character and Theorem 5 (the a_d values)

Blueprint: `docs/exploration/w2t6-design.md` (§3 the η definition, §4 the Theorem 5 ladder).
This is the first wave of the full Thm 6 apparatus: the completely-multiplicative character
`η` on `𝔽_p[X]` (Harcos Def 4, coefficient form) and the coefficient sums `a_d` of its
L-function (Harcos Thm 5).

* **η** (`eta`): `η(k) = e_p(-a·nextCoeff k)·e_p(-b·(coeff₁ k / coeff₀ k))` for `k` with nonzero
  constant term, else `0`. Basic facts: `eta_one`, `eta_mul` (complete multiplicativity, both
  factors monic), `eta_pow`.

* **The `a_d` values** (`aCoeff`): `a_d = ∑_{k monic, deg=d} η(k)`, summed over the coefficient
  tuple `Fin d → ZMod p`. Theorem 5:
  `a₀ = 1` (`T5_a0`), `a₁ = S(a,b;p)` (`T5_a1`), `a₂ = p` (`T5_a2`, needs `a≠0`, `b≠0`),
  `a_d = 0` for `d ≥ 3` (`T5_ad`, needs `a≠0`).
-/

namespace Salt.Weil

open scoped BigOperators
open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-! ### The η character (Harcos Def 4, coefficient form) -/

/-- Harcos Def 4, coefficient form. `nextCoeff k = coeff (natDegree − 1)` for degree `≥ 1` and
`0` for constants, so the constant case collapses to `1`. Correct for monic `k`. `X ∣ k`
(equivalently `coeff 0 = 0`) forces `η = 0`. -/
noncomputable def eta (a b : ZMod p) (k : (ZMod p)[X]) : ℂ :=
  if k.coeff 0 = 0 then 0
  else ZMod.stdAddChar (-(a * k.nextCoeff)) * ZMod.stdAddChar (-(b * (k.coeff 1 / k.coeff 0)))

theorem eta_of_coeff_zero (a b : ZMod p) {k : (ZMod p)[X]} (h : k.coeff 0 = 0) :
    eta a b k = 0 := by unfold eta; exact if_pos h

theorem eta_one (a b : ZMod p) : eta a b 1 = 1 := by
  have hc0 : (1 : (ZMod p)[X]).coeff 0 = 1 := by simp
  have hc1 : (1 : (ZMod p)[X]).coeff 1 = 0 := by simp [coeff_one]
  have hnc : (1 : (ZMod p)[X]).nextCoeff = 0 := by rw [← C_1]; exact nextCoeff_C_eq_zero 1
  unfold eta
  rw [if_neg (by rw [hc0]; exact one_ne_zero), hnc, hc1]
  simp [AddChar.map_zero_eq_one]

/-- **Complete multiplicativity (Harcos Lemma 6).** Both arguments monic. -/
theorem eta_mul (a b : ZMod p) {k₁ k₂ : (ZMod p)[X]} (h₁ : k₁.Monic) (h₂ : k₂.Monic) :
    eta a b (k₁ * k₂) = eta a b k₁ * eta a b k₂ := by
  by_cases hz1 : k₁.coeff 0 = 0
  · have h12 : (k₁ * k₂).coeff 0 = 0 := by rw [mul_coeff_zero, hz1, zero_mul]
    rw [eta_of_coeff_zero a b h12, eta_of_coeff_zero a b hz1, zero_mul]
  · by_cases hz2 : k₂.coeff 0 = 0
    · have h12 : (k₁ * k₂).coeff 0 = 0 := by rw [mul_coeff_zero, hz2, mul_zero]
      rw [eta_of_coeff_zero a b h12, eta_of_coeff_zero a b hz2, mul_zero]
    · have h12 : (k₁ * k₂).coeff 0 ≠ 0 := by rw [mul_coeff_zero]; exact mul_ne_zero hz1 hz2
      unfold eta
      rw [if_neg h12, if_neg hz1, if_neg hz2, Monic.nextCoeff_mul h₁ h₂, mul_coeff_zero,
        mul_coeff_one]
      have hd : (k₁.coeff 0 * k₂.coeff 1 + k₁.coeff 1 * k₂.coeff 0) / (k₁.coeff 0 * k₂.coeff 0)
          = k₁.coeff 1 / k₁.coeff 0 + k₂.coeff 1 / k₂.coeff 0 := by
        field_simp
        ring
      rw [hd, show -(a * (k₁.nextCoeff + k₂.nextCoeff))
            = -(a * k₁.nextCoeff) + -(a * k₂.nextCoeff) by ring,
        show -(b * (k₁.coeff 1 / k₁.coeff 0 + k₂.coeff 1 / k₂.coeff 0))
            = -(b * (k₁.coeff 1 / k₁.coeff 0)) + -(b * (k₂.coeff 1 / k₂.coeff 0)) by ring,
        AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
      ring

/-- η is completely multiplicative on powers of a monic (bonus lever for H3/Newton). -/
theorem eta_pow (a b : ZMod p) {k : (ZMod p)[X]} (h : k.Monic) (r : ℕ) :
    eta a b (k ^ r) = eta a b k ^ r := by
  induction r with
  | zero => simp [eta_one]
  | succ n ih => rw [pow_succ, eta_mul a b (h.pow n) h, ih, pow_succ]

/-! ### The coefficient sums `a_d` (Harcos Thm 5) -/

/-- `a_d = ∑_{k monic, deg=d} η(k)`, summed over the non-leading coefficient tuple
`Fin d → ZMod p` (avoiding the missing `Finite {k // Monic ∧ natDegree = d}`). -/
noncomputable def aCoeff (a b : ZMod p) (d : ℕ) : ℂ :=
  ∑ c : Fin d → ZMod p, eta a b (X ^ d + ∑ i : Fin d, C (c i) * X ^ (i : ℕ))

/-- The monic degree-`d` polynomial associated to a coefficient tuple. -/
noncomputable def tuplePoly {d : ℕ} (c : Fin d → ZMod p) : (ZMod p)[X] :=
  X ^ d + ∑ i : Fin d, C (c i) * X ^ (i : ℕ)

theorem aCoeff_eq (a b : ZMod p) (d : ℕ) :
    aCoeff a b d = ∑ c : Fin d → ZMod p, eta a b (tuplePoly c) := rfl

private theorem sum_CX_degree_lt {d : ℕ} (c : Fin d → ZMod p) :
    degree (∑ i : Fin d, C (c i) * X ^ (i : ℕ)) < (d : WithBot ℕ) := by
  refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr ?_)
  intro i _
  exact (degree_C_mul_X_pow_le _ (c i)).trans_lt (WithBot.coe_lt_coe.mpr i.isLt)

theorem tuplePoly_coeff {d : ℕ} (c : Fin d → ZMod p) {j : ℕ} (hj : j < d) :
    (tuplePoly c).coeff j = c ⟨j, hj⟩ := by
  rw [tuplePoly, coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt hj), zero_add, finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin d)]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro i _ hij
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => hij (Fin.ext h.symm)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem tuplePoly_monic {d : ℕ} (c : Fin d → ZMod p) : (tuplePoly c).Monic :=
  monic_X_pow_add (sum_CX_degree_lt c)

theorem tuplePoly_natDegree {d : ℕ} (c : Fin d → ZMod p) : (tuplePoly c).natDegree = d := by
  have hdeg : degree (tuplePoly c) = (d : WithBot ℕ) := by
    rw [tuplePoly, degree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact sum_CX_degree_lt c),
      degree_X_pow]
  exact natDegree_eq_of_degree_eq_some hdeg

theorem tuplePoly_nextCoeff {d : ℕ} (c : Fin d → ZMod p) (hd : 0 < d) :
    (tuplePoly c).nextCoeff = c ⟨d - 1, by omega⟩ := by
  rw [nextCoeff_of_natDegree_pos (by rw [tuplePoly_natDegree]; exact hd), tuplePoly_natDegree]
  exact tuplePoly_coeff c (by omega)

/-- **Theorem 5, `d = 0`.** `a₀ = η(1) = 1`. -/
theorem T5_a0 (a b : ZMod p) : aCoeff a b 0 = 1 := by
  rw [aCoeff_eq, Fintype.sum_unique]
  simp only [tuplePoly, pow_zero, Fin.sum_univ_zero, add_zero]
  exact eta_one a b

/-- A field sum over `ZMod p` whose value at `0` vanishes reindexes to a sum over the units. -/
private theorem sum_units_eq_sum_field {M : Type*} [AddCommMonoid M]
    (F : ZMod p → M) (h0 : F 0 = 0) :
    ∑ x : ZMod p, F x = ∑ t : (ZMod p)ˣ, F (t : ZMod p) := by
  rw [← Finset.sum_erase Finset.univ h0]
  refine (Finset.sum_bij (fun (t : (ZMod p)ˣ) _ => (t : ZMod p)) ?_ ?_ ?_ ?_).symm
  · intro t _
    exact Finset.mem_erase.mpr ⟨Units.ne_zero t, Finset.mem_univ _⟩
  · intro t₁ _ t₂ _ h
    exact Units.ext h
  · intro x hx
    exact ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
  · intro t _
    rfl

/-- η evaluated on a monic linear polynomial `X + C x`. -/
theorem eta_X_add_C (a b : ZMod p) (x : ZMod p) :
    eta a b (X + C x)
      = if x = 0 then 0 else ZMod.stdAddChar (-(a * x)) * ZMod.stdAddChar (-(b * (1 / x))) := by
  have hc0 : (X + C x).coeff 0 = x := by simp
  have hc1 : (X + C x).coeff 1 = 1 := by simp
  have hnc : (X + C x).nextCoeff = x := nextCoeff_X_add_C x
  unfold eta
  rw [hc0, hc1, hnc]

/-- **Theorem 5, `d = 1`.** `a₁ = S(a, b; p)`, the ordinary Kloosterman sum. -/
theorem T5_a1 (a b : ZMod p) : aCoeff a b 1 = kloosterman a b := by
  rw [aCoeff_eq]
  have hp1 : ∀ c : Fin 1 → ZMod p, tuplePoly c = X + C (c 0) := by
    intro c; rw [tuplePoly]; simp
  simp_rw [hp1]
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ZMod p))
      (fun c => eta a b (X + C (c 0))) (fun x => eta a b (X + C x)) (fun c => rfl)]
  rw [sum_units_eq_sum_field (fun x => eta a b (X + C x))
      (by change eta a b (X + C (0 : ZMod p)) = 0; rw [eta_X_add_C, if_pos rfl])]
  change ∑ t : (ZMod p)ˣ, eta a b (X + C (t : ZMod p)) = kloosterman a b
  have hsum : ∀ t : (ZMod p)ˣ, eta a b (X + C (t : ZMod p))
      = ZMod.stdAddChar (-(a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p))) := by
    intro t
    rw [eta_X_add_C, if_neg (Units.ne_zero t), ← AddChar.map_add_eq_mul]
    congr 1
    rw [one_div, ← Units.val_inv_eq_inv_val]
    ring
  rw [Finset.sum_congr rfl (fun t _ => hsum t), kloosterman,
    ← Equiv.sum_comp (Equiv.neg (ZMod p)ˣ) (fun t : (ZMod p)ˣ =>
      ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)))]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [Equiv.neg_apply]
  have hinv : ((-t : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) = -t⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
  rw [hinv]
  simp only [Units.val_neg]
  congr 1
  ring

/-- η on a monic degree-`d` polynomial (`d ≥ 2`) in terms of its coefficient tuple. -/
theorem eta_tuplePoly (a b : ZMod p) {d : ℕ} (hd : 2 ≤ d) (c : Fin d → ZMod p) :
    eta a b (tuplePoly c)
      = if c ⟨0, by omega⟩ = 0 then 0
        else ZMod.stdAddChar (-(a * c ⟨d - 1, by omega⟩))
           * ZMod.stdAddChar (-(b * (c ⟨1, by omega⟩ / c ⟨0, by omega⟩))) := by
  unfold eta
  rw [tuplePoly_coeff c (show 1 < d by omega), tuplePoly_coeff c (show 0 < d by omega),
    tuplePoly_nextCoeff c (show 0 < d by omega)]

/-- Additive orthogonality: `∑_v ψ(-(a·v)) = 0` for `a ≠ 0` (the free-coefficient kill). -/
private theorem sum_stdAddChar_neg_mul (a : ZMod p) (ha : a ≠ 0) :
    ∑ v : ZMod p, ZMod.stdAddChar (-(a * v)) = 0 := by
  have h : ∀ v : ZMod p, -(a * v) = v * (-a) := fun v => by ring
  simp_rw [h]
  rw [AddChar.sum_mulShift (-a) (ZMod.isPrimitive_stdAddChar p)]
  simp [ha]

/-- **Theorem 5, `d ≥ 3`.** The two middle coefficients are independent, and summing over the
free `X^{d-1}` coefficient kills the sum by orthogonality (`a ≠ 0`). -/
theorem T5_ad (a b : ZMod p) (ha : a ≠ 0) {d : ℕ} (hd : 3 ≤ d) : aCoeff a b d = 0 := by
  rw [aCoeff_eq]
  set i : Fin d := ⟨d - 1, by omega⟩ with hi
  rw [← Equiv.sum_comp (Equiv.funSplitAt i (ZMod p)).symm (fun c => eta a b (tuplePoly c)),
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_eq_zero (fun rest _ => ?_)
  have hi0 : (⟨0, by omega⟩ : Fin d) ≠ i := by rw [hi]; simp only [ne_eq, Fin.mk.injEq]; omega
  have hi1 : (⟨1, by omega⟩ : Fin d) ≠ i := by rw [hi]; simp only [ne_eq, Fin.mk.injEq]; omega
  have ec_dm1 : ∀ v : ZMod p,
      (Equiv.funSplitAt i (ZMod p)).symm (v, rest) ⟨d - 1, by omega⟩ = v := fun v => by simp [hi]
  have ec_0 : ∀ v : ZMod p,
      (Equiv.funSplitAt i (ZMod p)).symm (v, rest) ⟨0, by omega⟩ = rest ⟨⟨0, by omega⟩, hi0⟩ :=
    fun v => by simp [hi0]
  have ec_1 : ∀ v : ZMod p,
      (Equiv.funSplitAt i (ZMod p)).symm (v, rest) ⟨1, by omega⟩ = rest ⟨⟨1, by omega⟩, hi1⟩ :=
    fun v => by simp [hi1]
  simp_rw [eta_tuplePoly a b (show 2 ≤ d by omega), ec_dm1, ec_0, ec_1]
  by_cases hC0 : rest ⟨⟨0, by omega⟩, hi0⟩ = 0
  · simp [hC0]
  · simp only [if_neg hC0]
    rw [← Finset.sum_mul, sum_stdAddChar_neg_mul a ha, zero_mul]

/-- The inner `c₁`-orthogonality for `a₂`: completing the square collapses the double character
into a single multiplicative shift by `-(a + b/c₀)`. -/
private theorem sum_c1 (a b c₀ : ZMod p) (hc0 : c₀ ≠ 0) :
    (∑ c₁ : ZMod p, ZMod.stdAddChar (-(a * c₁)) * ZMod.stdAddChar (-(b * (c₁ / c₀))))
      = if a + b / c₀ = 0 then (p : ℂ) else 0 := by
  have h : ∀ c₁ : ZMod p,
      ZMod.stdAddChar (-(a * c₁)) * ZMod.stdAddChar (-(b * (c₁ / c₀)))
        = ZMod.stdAddChar (c₁ * (-(a + b / c₀))) := by
    intro c₁
    rw [← AddChar.map_add_eq_mul]
    congr 1
    field_simp
    ring
  simp_rw [h]
  rw [AddChar.sum_mulShift (-(a + b / c₀)) (ZMod.isPrimitive_stdAddChar p)]
  by_cases hz : a + b / c₀ = 0
  · rw [if_pos hz, if_pos (show -(a + b / c₀) = 0 by rw [hz]; ring)]
    simp [ZMod.card]
  · rw [if_neg hz, if_neg (neg_ne_zero.mpr hz)]
    simp

/-- **Theorem 5, `d = 2`.** `a₂ = p`. Needs both `a ≠ 0` and `b ≠ 0`: the single free coefficient
`c₁` (equal to both middle coefficients when `d = 2`) contributes `p` at the unique `c₀ = -b/a`. -/
theorem T5_a2 (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) : aCoeff a b 2 = (p : ℂ) := by
  rw [aCoeff_eq,
    ← Equiv.sum_comp (finTwoArrowEquiv (ZMod p)).symm (fun c => eta a b (tuplePoly c)),
    Fintype.sum_prod_type]
  have hred : ∀ c₀ c₁ : ZMod p,
      eta a b (tuplePoly ((finTwoArrowEquiv (ZMod p)).symm (c₀, c₁)))
        = if c₀ = 0 then (0 : ℂ)
          else ZMod.stdAddChar (-(a * c₁)) * ZMod.stdAddChar (-(b * (c₁ / c₀))) := by
    intro c₀ c₁
    rw [show (finTwoArrowEquiv (ZMod p)).symm (c₀, c₁) = ![c₀, c₁] by simp [finTwoArrowEquiv],
      eta_tuplePoly a b (le_refl 2)]
    simp
  simp_rw [hred]
  have hpull : ∀ c₀ : ZMod p,
      (∑ c₁ : ZMod p, if c₀ = 0 then (0 : ℂ)
          else ZMod.stdAddChar (-(a * c₁)) * ZMod.stdAddChar (-(b * (c₁ / c₀))))
        = if c₀ = -b / a then (p : ℂ) else 0 := by
    intro c₀
    by_cases hc0 : c₀ = 0
    · subst hc0
      rw [if_neg (show (0 : ZMod p) ≠ -b / a from
        fun h => (div_ne_zero (neg_ne_zero.mpr hb) ha) h.symm)]
      simp
    · have hiff : (a + b / c₀ = 0) ↔ (c₀ = -b / a) := by
        constructor
        · intro h; field_simp at h ⊢; linear_combination h
        · intro h; field_simp at h ⊢; linear_combination h
      simp only [if_neg hc0]
      rw [sum_c1 a b c₀ hc0]
      simp only [hiff]
  simp_rw [hpull]
  rw [Finset.sum_ite_eq']
  simp

end Salt.Weil
