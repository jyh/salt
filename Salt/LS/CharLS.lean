/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.GaussSum
import Salt.LS.ArithmeticLS

/-!
# Large sieve track, node L7.3: the character-form large sieve

Blueprint: `docs/blueprints/largesieve.md` (W4, character form).

For `2 ≤ Q` and any coefficient sequence `c : ℕ → ℂ`,
```
∑ q ∈ Icc 1 Q, (q / φ q) * ∑ χ primitive mod q, ‖∑ n < N, c n · χ n‖²
  ≤ (Q² + 13 N) · ∑ n < N, ‖c n‖².
```

The proof reduces the character form to the arithmetic large sieve `arithmetic_LS`
(L6.2) one modulus at a time (`char_LS_perQ`), via Gauss-sum inversion.

## The per-`q` argument

Fix `q ≥ 1` and write `ψ = ZMod.stdAddChar`. For `a : ZMod q` set
`S a = ∑ n < N, c n · ψ (n·a)`, and for a Dirichlet character `χ` set
`T χ = ∑ a, χ⁻¹ a · S a` (effectively a sum over units, since `χ⁻¹` vanishes off
units).

* **Per-`χ` identity (primitive `χ`).** Swapping the `a`- and `n`-sums and applying
  the Gauss-sum inversion `dirichlet_inversion` (L7.1) gives
  `T χ = (∑ n, c n · χ n) · gaussSum χ⁻¹ ψ`, whence
  `‖T χ‖² = ‖∑ n, c n · χ n‖² · q` using `‖gaussSum χ⁻¹ ψ‖² = q` (L7.2, `gaussSum_normSq`
  on `χ⁻¹` via `isPrimitive_inv`).

* **Plancherel over *all* `χ` (the budget).** Expanding `∑_χ ‖T χ‖²` and collapsing
  the character sum by the second orthogonality relation
  `DirichletCharacter.sum_characters_eq` yields
  `∑_χ ‖T χ‖² = φ(q) · ∑_{a unit} ‖S a‖²`. Restricting the left sum to primitive `χ`
  (each term `≥ 0`) and inserting the per-`χ` identity gives
  `q · ∑_{χ prim} ‖∑ c χ‖² ≤ φ(q) · ∑_{a unit} ‖S a‖²`, i.e.
  `(q/φ q) · ∑_{χ prim} ‖∑ c χ‖² ≤ ∑_{a unit} ‖S a‖²`. Summing the per-`χ` inequality
  *directly* would over-count the `a`-sum once per `χ`; going through all `χ` and
  orthogonality is what keeps the budget honest.

* **The bridge to Farey points.** `stdAddChar_eq_e` and `e`-power identities give
  `S a = expSum N c (a.val / q)`, and the unit-`a` sum reindexes (`a ↦ a.val`,
  `ZMod.isUnit_iff_coprime`) to `∑ a ∈ (range q).filter (Nat.Coprime q)`. The arithmetic
  large sieve `arithmetic_LS` (L6.2) then closes the `q`-sum.

Only `[propext, Classical.choice, Quot.sound]` are used. `Classical` is opened so the
primitive-character sum can be written as a `Finset.univ.filter` over the (noncomputable)
`Fintype (DirichletCharacter ℂ q)` instance.
-/

namespace Salt.LS

open scoped BigOperators
open ComplexConjugate

/-- `e (n·x) = (e x)^n` for a natural power. -/
lemma e_natCast_mul (n : ℕ) (x : ℝ) : e ((n : ℝ) * x) = e x ^ n := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

open Classical in
/-- **L7.3, per modulus.** For `q ≥ 1` and primitive characters mod `q`,
`(q/φ q) · ∑_{χ prim} ‖∑ n, c n · χ n‖² ≤ ∑ a ∈ (range q).filter (Coprime q),
‖expSum N c (a/q)‖²`. This is the heart of the character large sieve; summing it over
`q ∈ Icc 1 Q` and applying `arithmetic_LS` gives `char_LS`. -/
theorem char_LS_perQ {N : ℕ} (q : ℕ) [NeZero q] (c : ℕ → ℂ) :
    ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2
      ≤ ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), ‖expSum N c ((a : ℝ) / q)‖ ^ 2 := by
  classical
  -- The additive-character "twist" `S a = ∑ n, c n · ψ (n·a)` and its dual pairing
  -- `T χ = ∑ a, χ⁻¹ a · S a`.
  set S : ZMod q → ℂ :=
    fun a => ∑ n ∈ Finset.range N, c n * ZMod.stdAddChar ((n : ZMod q) * a) with hS_def
  set T : DirichletCharacter ℂ q → ℂ := fun χ => ∑ a : ZMod q, χ⁻¹ a * S a with hT_def
  have hSval : ∀ a, S a = ∑ n ∈ Finset.range N, c n * ZMod.stdAddChar ((n : ZMod q) * a) :=
    fun a => by rw [hS_def]
  have hTval : ∀ χ, T χ = ∑ a : ZMod q, χ⁻¹ a * S a := fun χ => by rw [hT_def]
  -- `conj (χ⁻¹ b) = χ b`.
  have hconjInv : ∀ (χ : DirichletCharacter ℂ q) (b : ZMod q),
      (starRingEnd ℂ) (χ⁻¹ b) = χ b := by
    intro χ b
    rw [starRingEnd_apply, MulChar.star_apply', inv_inv]
  -- Second orthogonality: `∑_χ χ⁻¹ a · χ b = φ(q)·δ_{a,b}` for `a` a unit.
  have horth : ∀ (a b : ZMod q), IsUnit a →
      (∑ χ : DirichletCharacter ℂ q, χ⁻¹ a * χ b) = if a = b then (q.totient : ℂ) else 0 := by
    intro a b ha
    have hterm : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ a * χ b = χ (Ring.inverse a * b) := by
      intro χ; rw [MulChar.inv_apply, ← map_mul]
    simp_rw [hterm]
    rw [DirichletCharacter.sum_characters_eq]
    have hiff : (Ring.inverse a * b = 1) ↔ (a = b) := by
      constructor
      · intro h
        have h2 : a * (Ring.inverse a * b) = a * 1 := by rw [h]
        rwa [← mul_assoc, Ring.mul_inverse_cancel a ha, one_mul, mul_one, eq_comm] at h2
      · rintro rfl
        exact Ring.inverse_mul_cancel a ha
    exact if_congr hiff rfl rfl
  -- Expand `‖T χ‖²` (as `T χ · conj (T χ)`) into a double sum over `ZMod q`.
  have expand : ∀ χ : DirichletCharacter ℂ q,
      T χ * (starRingEnd ℂ) (T χ)
        = ∑ a : ZMod q, ∑ b : ZMod q, (χ⁻¹ a * χ b) * (S a * (starRingEnd ℂ) (S b)) := by
    intro χ
    have hTc : (starRingEnd ℂ) (T χ) = ∑ b : ZMod q, χ b * (starRingEnd ℂ) (S b) := by
      rw [hTval χ, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, hconjInv χ b]
    rw [hTval χ, hTc, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  -- Collapse the character sum against the twist products, one `a` at a time.
  have hcollapse : ∀ a : ZMod q,
      (∑ χ : DirichletCharacter ℂ q, ∑ b : ZMod q,
          (χ⁻¹ a * χ b) * (S a * (starRingEnd ℂ) (S b)))
        = (if IsUnit a then (q.totient : ℂ) * (S a * (starRingEnd ℂ) (S a)) else 0) := by
    intro a
    rw [Finset.sum_comm]
    by_cases ha : IsUnit a
    · rw [if_pos ha]
      have step : ∀ b : ZMod q,
          (∑ χ : DirichletCharacter ℂ q, (χ⁻¹ a * χ b) * (S a * (starRingEnd ℂ) (S b)))
            = (if a = b then (q.totient : ℂ) else 0) * (S a * (starRingEnd ℂ) (S b)) := by
        intro b
        rw [← Finset.sum_mul, horth a b ha]
      rw [Finset.sum_congr rfl fun b _ => step b]
      simp_rw [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq Finset.univ a fun b => (q.totient : ℂ) * (S a * (starRingEnd ℂ) (S b))]
      rw [if_pos (Finset.mem_univ a)]
    · rw [if_neg ha]
      refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun χ _ => ?_
      rw [MulChar.map_nonunit χ⁻¹ ha, zero_mul, zero_mul]
  -- Plancherel over ALL characters (complex form).
  have hplancherel : (∑ χ : DirichletCharacter ℂ q, T χ * (starRingEnd ℂ) (T χ))
      = (q.totient : ℂ) * ∑ a : ZMod q, (if IsUnit a then S a * (starRingEnd ℂ) (S a) else 0) := by
    calc (∑ χ : DirichletCharacter ℂ q, T χ * (starRingEnd ℂ) (T χ))
        = ∑ χ : DirichletCharacter ℂ q, ∑ a : ZMod q, ∑ b : ZMod q,
            (χ⁻¹ a * χ b) * (S a * (starRingEnd ℂ) (S b)) :=
          Finset.sum_congr rfl fun χ _ => expand χ
      _ = ∑ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, ∑ b : ZMod q,
            (χ⁻¹ a * χ b) * (S a * (starRingEnd ℂ) (S b)) := Finset.sum_comm
      _ = ∑ a : ZMod q, (if IsUnit a then (q.totient : ℂ) * (S a * (starRingEnd ℂ) (S a)) else 0) :=
          Finset.sum_congr rfl fun a _ => hcollapse a
      _ = (q.totient : ℂ) *
            ∑ a : ZMod q, (if IsUnit a then S a * (starRingEnd ℂ) (S a) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          split_ifs <;> ring
  -- Descend the two sides to `ℝ`.
  have descend_lhs : (∑ χ : DirichletCharacter ℂ q, T χ * (starRingEnd ℂ) (T χ))
      = ((∑ χ : DirichletCharacter ℂ q, ‖T χ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Complex.mul_conj']; norm_cast
  have descend_rhs : (∑ a : ZMod q, (if IsUnit a then S a * (starRingEnd ℂ) (S a) else 0))
      = ((∑ a : ZMod q, (if IsUnit a then ‖S a‖ ^ 2 else 0) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with ha
    · rw [Complex.mul_conj']; norm_cast
    · norm_num
  have hplancherelR : (∑ χ : DirichletCharacter ℂ q, ‖T χ‖ ^ 2)
      = (q.totient : ℝ) * ∑ a : ZMod q, (if IsUnit a then ‖S a‖ ^ 2 else 0) := by
    have h := hplancherel
    rw [descend_lhs, descend_rhs] at h
    have hcast : (↑(∑ χ : DirichletCharacter ℂ q, ‖T χ‖ ^ 2) : ℂ)
        = ↑((q.totient : ℝ) * ∑ a : ZMod q, (if IsUnit a then ‖S a‖ ^ 2 else 0)) := by
      rw [h]; push_cast; ring
    exact_mod_cast hcast
  -- Per-`χ` identity for primitive `χ`.
  have hP1 : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ‖T χ‖ ^ 2 = ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2 * (q : ℝ) := by
    intro χ hχ
    have hTeq : T χ = (∑ n ∈ Finset.range N, c n * χ (n : ZMod q)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
      rw [hTval χ]
      calc ∑ a : ZMod q, χ⁻¹ a * S a
          = ∑ a : ZMod q, χ⁻¹ a *
              ∑ n ∈ Finset.range N, c n * ZMod.stdAddChar ((n : ZMod q) * a) := by
            refine Finset.sum_congr rfl fun a _ => by rw [hSval a]
        _ = ∑ a : ZMod q, ∑ n ∈ Finset.range N,
              χ⁻¹ a * (c n * ZMod.stdAddChar ((n : ZMod q) * a)) :=
            Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _
        _ = ∑ n ∈ Finset.range N, ∑ a : ZMod q,
              χ⁻¹ a * (c n * ZMod.stdAddChar ((n : ZMod q) * a)) := Finset.sum_comm
        _ = ∑ n ∈ Finset.range N, c n *
              ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar ((n : ZMod q) * a) := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => by ring
        _ = ∑ n ∈ Finset.range N, c n *
              (χ (n : ZMod q) * gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)) := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [dirichlet_inversion χ hχ (n : ZMod q)]
        _ = (∑ n ∈ Finset.range N, c n * χ (n : ZMod q)) *
              gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun n _ => by ring
    rw [hTeq, norm_mul, mul_pow, gaussSum_normSq χ⁻¹ (isPrimitive_inv χ hχ)]
  -- The twist `S a` is the exponential sum at the Farey point `a.val / q`.
  have hSbridge : ∀ a : ZMod q, S a = expSum N c ((a.val : ℝ) / q) := by
    intro a
    rw [hSval a]
    unfold expSum
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    rw [show ((n : ZMod q) * a) = n • a from by rw [nsmul_eq_mul]]
    rw [AddChar.map_nsmul_eq_pow, stdAddChar_eq_e, e_natCast_mul]
  -- Reindex the unit-`a` sum to the reduced-residue Farey filter.
  have hBunit : (∑ a : ZMod q, (if IsUnit a then ‖S a‖ ^ 2 else 0))
      = ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), ‖expSum N c ((a : ℝ) / q)‖ ^ 2 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (fun a : ZMod q => a.val) (fun m : ℕ => (m : ZMod q)) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at ha ⊢
      refine ⟨ZMod.val_lt a, ?_⟩
      have h := ZMod.val_coe_unit_coprime ha.unit
      rw [IsUnit.unit_spec] at h
      exact h.symm
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hm ⊢
      exact (ZMod.isUnit_iff_coprime m q).mpr hm.2.symm
    · intro a _
      exact ZMod.natCast_zmod_val a
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      exact ZMod.val_natCast_of_lt hm.1
    · intro a _
      rw [hSbridge a]
  -- Assemble: `q · (charSum) ≤ φ(q) · (fareySum)`, then divide.
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hrestrict :
      (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive), ‖T χ‖ ^ 2)
        ≤ ∑ χ : DirichletCharacter ℂ q, ‖T χ‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro χ _ _
    positivity
  have hkey :
      (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2) * (q : ℝ)
        ≤ (q.totient : ℝ) *
            ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), ‖expSum N c ((a : ℝ) / q)‖ ^ 2 := by
    calc (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2) * (q : ℝ)
        = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ‖T χ‖ ^ 2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun χ hχ => (hP1 χ (Finset.mem_filter.mp hχ).2).symm
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖T χ‖ ^ 2 := hrestrict
      _ = (q.totient : ℝ) * ∑ a : ZMod q, (if IsUnit a then ‖S a‖ ^ 2 else 0) := hplancherelR
      _ = (q.totient : ℝ) *
            ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), ‖expSum N c ((a : ℝ) / q)‖ ^ 2 := by
          rw [hBunit]
  rw [div_mul_eq_mul_div, div_le_iff₀ hφpos]
  nlinarith [hkey]

open Classical in
/-- **L7.3 — the character-form large sieve (FROZEN).** For `2 ≤ Q` and any coefficient
sequence `c : ℕ → ℂ`,
```
∑ q ∈ Icc 1 Q, (q / φ q) · ∑ χ primitive mod q, ‖∑ n < N, c n · χ n‖²
  ≤ (Q² + 13 N) · ∑ n < N, ‖c n‖².
```
The primitive-character sum is indexed by `Finset.univ.filter (·.IsPrimitive)` over the
`Fintype (DirichletCharacter ℂ q)` instance (with `Classical` decidability), and `χ n`
means `χ (n : ZMod q)`. Proof: `char_LS_perQ` for each modulus, then `arithmetic_LS`. -/
theorem char_LS {N Q : ℕ} (hQ : 2 ≤ Q) (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  classical
  calc ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
              ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2
      ≤ ∑ q ∈ Finset.Icc 1 Q,
          ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), ‖expSum N c ((a : ℝ) / q)‖ ^ 2 := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        haveI : NeZero q := ⟨Nat.one_le_iff_ne_zero.mp hq1⟩
        exact char_LS_perQ q c
    _ ≤ ((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := arithmetic_LS hQ c

end Salt.LS
