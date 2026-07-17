/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.PointCount
import Mathlib

/-!
# Weil track, the φ-bundling and the one-sided Stepanov bound (W5B)

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder), following Harcos §5,
equations (20)–(23) and Theorem 7. This is the last node before Theorem 7 assembles: it
bundles the Harcos (22) constraint system into a single `F`-linear map `stepanovConstraint`
feeding `stepanov_dimension_count`, produces a nonzero degree-bounded solution `(r, s)` of
(22), and composes the landed pieces (`stepanovAux_ne_zero`, `stepanov_locus_card_le`,
`stepanovAux_natDegree_le`) into the one-sided count bound `ℓ·|T| ≤ deg h_a` on the locus
`N₀ ∪ N_a`.

* **the Hasse-derivative quotient** (`hasseQuot`): the honest linearity route. The map
  `g ↦ hasseDeriv k (g·f^p) / f^{p-k}` is `F`-linear — realised as a bundled `LinearMap`
  via the divisibility `pow_dvd_hasseDeriv_mul_pow` (no conditional-division constructor;
  additivity and homogeneity come from left-cancelling `f^{p-k} ≠ 0`).

* **the constraint map** (`stepanovConstraint`): for each `k < ℓ`, the `a`-form (22)
  polynomial `∑_j (r_j^{(k)} + a·s_j^{(k)}) X^j`, packaged with `LinearMap.pi` +
  `codRestrict` into `Fin ℓ → degreeLT F D`. Its kernel elements solve (22) on `N_a`.

* **the solution** (`stepanov_solution_exists`): `stepanov_dimension_count` applied to
  `stepanovConstraint` at the (Harcos + 1)-bumped parameters yields a nonzero `(r, s)`.

* **the one-sided bound** (`stepanov_one_sided_card_le`): `ℓ·|T| ≤ deg h_a` for any finite
  `T ⊆ N₀ ∪ N_a`, the shape Theorem 7's assembly consumes.
-/

namespace Salt.Weil

open Polynomial Module
open scoped BigOperators

variable {F : Type*} [Field F]

/-! ### Degree ↔ `degreeLT` membership bridges -/

/-- `natDegree p < n` implies `p ∈ degreeLT F n` (handles `p = 0` uniformly). -/
theorem mem_degreeLT_of_natDegree_lt {p : F[X]} {n : ℕ} (h : p.natDegree < n) :
    p ∈ degreeLT F n := by
  rw [mem_degreeLT]
  calc p.degree ≤ (p.natDegree : WithBot ℕ) := degree_le_natDegree
    _ < (n : WithBot ℕ) := by exact_mod_cast h

/-- `p ∈ degreeLT F n` gives `natDegree p ≤ n - 1` (valid for every `n`, including `0`). -/
theorem natDegree_le_sub_one_of_mem_degreeLT {p : F[X]} {n : ℕ}
    (h : p ∈ degreeLT F n) : p.natDegree ≤ n - 1 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [mem_degreeLT, degree_eq_natDegree hp] at h
    have : p.natDegree < n := by exact_mod_cast h
    omega

/-- `p ∈ degreeLT F n` with `1 ≤ n` gives `natDegree p < n`. -/
theorem natDegree_lt_of_mem_degreeLT {p : F[X]} {n : ℕ} (hn : 1 ≤ n)
    (h : p ∈ degreeLT F n) : p.natDegree < n := by
  have := natDegree_le_sub_one_of_mem_degreeLT h; omega

/-! ### The Hasse-derivative quotient as a bundled linear map -/

/-- **The Hasse-derivative quotient** (Harcos (20)/(21)). The map
`g ↦ hasseDeriv k (g·f^p) / f^{p-k}` (the quotient guaranteed by the tight-degree bridge) is
`F`-linear. The underlying function is `Classical.choose` of the divisibility witness; additivity
and homogeneity follow by left-cancelling the nonzero factor `f^{p-k}`. -/
noncomputable def hasseQuot (f : F[X]) (hf : f ≠ 0) (hm : 1 ≤ f.natDegree) (p k : ℕ)
    (hk : k ≤ p) : F[X] →ₗ[F] F[X] where
  toFun g := Classical.choose (exists_quotient_hasseDeriv_mul_pow f g hf hm p k hk)
  map_add' g₁ g₂ := by
    have s1 := (Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f g₁ hf hm p k hk)).1
    have s2 := (Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f g₂ hf hm p k hk)).1
    have s12 :=
      (Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f (g₁ + g₂) hf hm p k hk)).1
    refine mul_left_cancel₀ (pow_ne_zero (p - k) hf) ?_
    rw [mul_add, ← s1, ← s2, ← s12, add_mul, map_add]
  map_smul' c g := by
    have sg := (Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f g hf hm p k hk)).1
    have scg :=
      (Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f (c • g) hf hm p k hk)).1
    simp only [RingHom.id_apply]
    refine mul_left_cancel₀ (pow_ne_zero (p - k) hf) ?_
    rw [mul_smul_comm, ← sg, ← scg, smul_mul_assoc, map_smul]

/-- Defining relation of `hasseQuot`: `f^{p-k} · (g^{(k)}) = hasseDeriv k (g·f^p)`. -/
theorem hasseQuot_mul (f : F[X]) (hf : f ≠ 0) (hm : 1 ≤ f.natDegree) (p k : ℕ)
    (hk : k ≤ p) (g : F[X]) :
    f ^ (p - k) * hasseQuot f hf hm p k hk g = hasseDeriv k (g * f ^ p) :=
  ((Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f g hf hm p k hk)).1).symm

/-- The tight-degree bound (Harcos (21)) for `hasseQuot`. -/
theorem hasseQuot_natDegree_le (f : F[X]) (hf : f ≠ 0) (hm : 1 ≤ f.natDegree) (p k : ℕ)
    (hk : k ≤ p) (g : F[X]) :
    (hasseQuot f hf hm p k hk g).natDegree ≤ g.natDegree + k * (f.natDegree - 1) :=
  (Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f g hf hm p k hk)).2

/-! ### The bundled constraint map (Harcos (22)) -/

/-- **The `a`-form constraint map** (Harcos (22)). For each `k < ℓ` it returns the
`a`-combination `∑_j (r_j^{(k)} + C a · s_j^{(k)}) X^j` of the Hasse-derivative quotients, a
degree-`< D` polynomial (`D := B + (ℓ-1)(m-1) + J`). Bundled as an `F`-linear map into
`Fin ℓ → degreeLT F D` — the exact domain/codomain of `stepanov_dimension_count`. -/
noncomputable def stepanovConstraint [Fintype F] (f : F[X]) (hf : f ≠ 0)
    (hm : 1 ≤ f.natDegree) (a : F) (ℓ J B : ℕ) :
    ((Fin J → degreeLT F B) × (Fin J → degreeLT F B)) →ₗ[F]
      (Fin ℓ → degreeLT F (B + (ℓ - 1) * (f.natDegree - 1) + J)) :=
  LinearMap.pi fun k =>
    LinearMap.codRestrict _
      (∑ j : Fin J,
        (LinearMap.mulRight F (X ^ (j : ℕ))).comp
          ((hasseQuot f hf hm ℓ (k : ℕ) (le_of_lt k.isLt)).comp
              ((degreeLT F B).subtype.comp ((LinearMap.proj j).comp (LinearMap.fst F _ _)))
            + (LinearMap.mulLeft F (C a)).comp
                ((hasseQuot f hf hm (ℓ + (Fintype.card F - 1) / 2) (k : ℕ)
                    ((le_of_lt k.isLt).trans (Nat.le_add_right ℓ _))).comp
                  ((degreeLT F B).subtype.comp ((LinearMap.proj j).comp (LinearMap.snd F _ _))))))
      (by
        intro v
        rw [LinearMap.sum_apply]
        refine Submodule.sum_mem _ fun j _ => ?_
        simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
          LinearMap.mulLeft_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.proj_apply,
          Submodule.coe_subtype]
        apply mem_degreeLT_of_natDegree_lt
        have hj1 := j.isLt
        have hqr := hasseQuot_natDegree_le f hf hm ℓ (k : ℕ) (le_of_lt k.isLt) (v.1 j).val
        have hqs := hasseQuot_natDegree_le f hf hm (ℓ + (Fintype.card F - 1) / 2) (k : ℕ)
          ((le_of_lt k.isLt).trans (Nat.le_add_right ℓ _)) (v.2 j).val
        have hdrB : (v.1 j).val.natDegree ≤ B - 1 :=
          natDegree_le_sub_one_of_mem_degreeLT (v.1 j).2
        have hdsB : (v.2 j).val.natDegree ≤ B - 1 :=
          natDegree_le_sub_one_of_mem_degreeLT (v.2 j).2
        have hk1 := k.isLt
        set m := f.natDegree with hm_def
        have hkm : (k : ℕ) * (m - 1) ≤ (ℓ - 1) * (m - 1) := by gcongr; omega
        refine lt_of_le_of_lt (natDegree_mul_le) ?_
        rw [natDegree_X_pow]
        refine lt_of_le_of_lt
          (Nat.add_le_add_right (?_ : _ ≤ B - 1 + (k : ℕ) * (m - 1)) (j : ℕ)) ?_
        · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
          · exact hqr.trans (by omega)
          · exact (natDegree_C_mul_le _ _).trans (hqs.trans (by omega))
        · omega)

/-- The coefficient form of `stepanovConstraint`: its `k`-th component, coerced to `F[X]`, is the
`a`-combination `∑_j (r_j^{(k)} + C a · s_j^{(k)}) X^j`. -/
theorem stepanovConstraint_apply_coe [Fintype F] {ℓ J B : ℕ} (f : F[X]) (hf : f ≠ 0)
    (hm : 1 ≤ f.natDegree) (a : F)
    (v : (Fin J → degreeLT F B) × (Fin J → degreeLT F B)) (k : Fin ℓ) :
    ((stepanovConstraint f hf hm a ℓ J B v k : degreeLT F _) : F[X])
      = ∑ j : Fin J, (hasseQuot f hf hm ℓ (k : ℕ) (le_of_lt k.isLt) (v.1 j).val
          + C a * hasseQuot f hf hm (ℓ + (Fintype.card F - 1) / 2) (k : ℕ)
              ((le_of_lt k.isLt).trans (Nat.le_add_right ℓ _)) (v.2 j).val) * X ^ (j : ℕ) := by
  simp only [stepanovConstraint, LinearMap.pi_apply, LinearMap.codRestrict_apply,
    LinearMap.coe_sum, Finset.sum_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    LinearMap.proj_apply, Submodule.coe_subtype]

/-! ### The kernel bridge (Harcos (22) ⇒ the vanishing hypothesis) -/

/-- **The kernel bridge.** If the `a`-form constraint polynomial (the `k`-th component of
`stepanovConstraint`) is the zero polynomial, then the reduced polynomial `Q_k` vanishes at
every point `x` of the locus `N_a` (`f(x)^{(q-1)/2} = a`). This is the per-point specialisation
used to feed `stepanov_locus_card_le`: at such `x`, `Q_k(x) = f(x)^{ℓ-k}·(constraint)(x) = 0`. -/
theorem reducedPoly_eval_zero_of_constraint [Fintype F] {J : ℕ} (f : F[X]) (hf : f ≠ 0)
    (hm : 1 ≤ f.natDegree) (ℓ : ℕ) (r s : Fin J → F[X]) (a : F) {k : ℕ} (hk : k < ℓ)
    (x : F)
    (hx : (f.eval x) ^ ((Fintype.card F - 1) / 2) = a)
    (hcon : ∑ j : Fin J,
        (hasseQuot f hf hm ℓ k (le_of_lt hk) (r j)
          + C a * hasseQuot f hf hm (ℓ + (Fintype.card F - 1) / 2) k
              ((le_of_lt hk).trans (Nat.le_add_right ℓ _)) (s j)) * X ^ (j : ℕ) = 0) :
    (reducedPoly f ℓ r s k).eval x = 0 := by
  rw [reducedPoly_eval]
  set e := (Fintype.card F - 1) / 2 with he
  have hconx : ∑ j : Fin J,
      ((hasseQuot f hf hm ℓ k (le_of_lt hk) (r j)).eval x
        + a * (hasseQuot f hf hm (ℓ + e) k ((le_of_lt hk).trans (Nat.le_add_right ℓ _))
            (s j)).eval x) * x ^ (j : ℕ) = 0 := by
    have h := congrArg (Polynomial.eval x) hcon
    simpa only [eval_finsetSum, eval_mul, eval_add, eval_C, eval_pow, eval_X, eval_zero] using h
  have key : ∀ j : Fin J,
      (hasseDeriv k (r j * f ^ ℓ + s j * f ^ (ℓ + e))).eval x
        = (f.eval x) ^ (ℓ - k) * ((hasseQuot f hf hm ℓ k (le_of_lt hk) (r j)).eval x
            + a * (hasseQuot f hf hm (ℓ + e) k ((le_of_lt hk).trans (Nat.le_add_right ℓ _))
                (s j)).eval x) := by
    intro j
    have hr := hasseQuot_mul f hf hm ℓ k (le_of_lt hk) (r j)
    have hs := hasseQuot_mul f hf hm (ℓ + e) k
      ((le_of_lt hk).trans (Nat.le_add_right ℓ _)) (s j)
    rw [map_add, ← hr, ← hs, eval_add, eval_mul, eval_mul, eval_pow, eval_pow]
    have hpow : (f.eval x) ^ ((ℓ + e) - k) = (f.eval x) ^ (ℓ - k) * a := by
      rw [← hx, ← pow_add]; congr 1; omega
    rw [hpow]; ring
  have hstep : ∑ j : Fin J,
        (hasseDeriv k (r j * f ^ ℓ + s j * f ^ (ℓ + e))).eval x * x ^ (j : ℕ)
      = (f.eval x) ^ (ℓ - k) * ∑ j : Fin J,
          ((hasseQuot f hf hm ℓ k (le_of_lt hk) (r j)).eval x
            + a * (hasseQuot f hf hm (ℓ + e) k ((le_of_lt hk).trans (Nat.le_add_right ℓ _))
                (s j)).eval x) * x ^ (j : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [key j]; ring
  rw [hstep, hconx, mul_zero]

/-! ### The nonzero degree-bounded solution of (22) -/

/-- **The Stepanov solution** (Harcos p. 12). At the (Harcos + 1)-bumped parameters — the count
`ℓ·D < 2·J·B` with `D = B + (ℓ-1)(m-1) + J` — there is a nonzero degree-`< B` coefficient
vector `(r, s)` solving the (22) system on `N_a` for every `k < ℓ`: the reduced polynomials
vanish on the locus. Obtained by feeding `stepanovConstraint` to `stepanov_dimension_count`. -/
theorem stepanov_solution_exists [Fintype F] {ℓ J B : ℕ} (f : F[X]) (hf : f ≠ 0)
    (hm : 1 ≤ f.natDegree) (a : F)
    (hcount : ℓ * (B + (ℓ - 1) * (f.natDegree - 1) + J) < 2 * (J * B)) :
    ∃ r s : Fin J → F[X], (∃ j, r j ≠ 0 ∨ s j ≠ 0)
      ∧ (∀ j, (r j).natDegree ≤ B - 1) ∧ (∀ j, (s j).natDegree ≤ B - 1)
      ∧ ∀ k, k < ℓ → ∀ x : F, (f.eval x) ^ ((Fintype.card F - 1) / 2) = a
          → (reducedPoly f ℓ r s k).eval x = 0 := by
  obtain ⟨v, hv_ne, hv_ker⟩ :=
    stepanov_dimension_count (stepanovConstraint f hf hm a ℓ J B) hcount
  refine ⟨fun j => (v.1 j).val, fun j => (v.2 j).val, ?_, ?_, ?_, ?_⟩
  · by_contra hc
    apply hv_ne
    have hj : ∀ j, (v.1 j).val = 0 ∧ (v.2 j).val = 0 := by
      intro j
      have hnj := not_exists.mp hc j
      rw [not_or, not_ne_iff, not_ne_iff] at hnj
      exact hnj
    have h1 : v.1 = 0 := funext fun j => Subtype.ext (by simpa using (hj j).1)
    have h2 : v.2 = 0 := funext fun j => Subtype.ext (by simpa using (hj j).2)
    exact Prod.ext h1 h2
  · intro j; exact natDegree_le_sub_one_of_mem_degreeLT (v.1 j).2
  · intro j; exact natDegree_le_sub_one_of_mem_degreeLT (v.2 j).2
  · intro k hk x hx
    refine reducedPoly_eval_zero_of_constraint f hf hm ℓ _ _ a hk x hx ?_
    have hc : ((stepanovConstraint f hf hm a ℓ J B v ⟨k, hk⟩ : degreeLT F _) : F[X]) = 0 := by
      have hz := congrFun hv_ker ⟨k, hk⟩
      rw [hz]; simp
    rw [stepanovConstraint_apply_coe] at hc
    exact hc

/-! ### The one-sided Stepanov count bound (Harcos (13)) -/

/-- **The one-sided bound** (Harcos (13), the numerator half). For `q` odd, `f` a non-square with
`f(0) ≠ 0` and `deg f = m ≥ 1`, and parameters satisfying the (Harcos + 1) dimension count, any
finite locus `T ⊆ N₀ ∪ N_a` (each point either a root of `f` or on `f(x)^{(q-1)/2} = a`) obeys
`ℓ·|T| ≤ deg h_a`, with the explicit degree bound of `stepanovAux_natDegree_le` on the right.
This is the shape Theorem 7's assembly consumes for `a = ±1` (with `2·bound/ℓ − q < O_m(√q)`). -/
theorem stepanov_one_sided_card_le [Fintype F] {ℓ J B : ℕ} (f : F[X]) (hf : f ≠ 0)
    (hm : 1 ≤ f.natDegree) (a : F) (hB1 : 1 ≤ B) (hℓq : ℓ ≤ Fintype.card F)
    (hqodd : Odd (Fintype.card F)) (hf0 : f.coeff 0 ≠ 0)
    (hB : B ≤ (Fintype.card F - f.natDegree) / 2)
    (hns : ¬ ∃ g : (AlgebraicClosure F)[X],
      f.map (algebraMap F (AlgebraicClosure F)) = g ^ 2)
    (hcount : ℓ * (B + (ℓ - 1) * (f.natDegree - 1) + J) < 2 * (J * B))
    (T : Finset F)
    (hT : ∀ x ∈ T, f.eval x = 0 ∨ (f.eval x) ^ ((Fintype.card F - 1) / 2) = a) :
    ℓ * T.card ≤ ℓ * f.natDegree
        + (B + (Fintype.card F - 1) / 2 * f.natDegree + (J - 1) * Fintype.card F) := by
  obtain ⟨r, s, hnz, hrd, hsd, hvanish⟩ := stepanov_solution_exists f hf hm a hcount
  have hne : stepanovAux f ℓ r s ≠ 0 :=
    stepanovAux_ne_zero f ℓ r s hqodd hf0
      (fun j => lt_of_le_of_lt (hrd j) (by omega)) (fun j => lt_of_le_of_lt (hsd j) (by omega))
      hns hnz
  have hcard : ℓ * T.card ≤ (stepanovAux f ℓ r s).natDegree := by
    refine stepanov_locus_card_le f ℓ r s hℓq hne T (fun k hk x hxT hfx => ?_)
    rcases hT x hxT with h0 | ha
    · exact absurd h0 hfx
    · exact hvanish k hk x ha
  exact hcard.trans
    (stepanovAux_natDegree_le f ℓ r s (fun j => (hrd j).trans (Nat.sub_le B 1))
      (fun j => (hsd j).trans (Nat.sub_le B 1)))

end Salt.Weil
