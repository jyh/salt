/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.SeriesM
import Mathlib.Data.Nat.Choose.Multinomial

open Finset Nat Salt.Twelve

namespace Salt.MaynardK

/-!
# C1 glue at general `M` — the basis `(1 − P₁)^a · Π_m P_{2(m+1)}^{C m}` as a budget polynomial

The `M`-variable generalisation of `Basis` (`basisPoly`, `eval_basisPoly`,
`simplexInt_basisPoly`): `basisPolyM M k a C` is the multinomial expansion of
`(1 − P₁)^a · Π_m P_{2(m+1)}^{C m}` on `k` coordinates, `eval_basisPolyM` says it evaluates to that
product, and `simplexInt_basisPolyM` gives its Dirichlet integral in closed form from
`symCollectM`. At `M = 1` these are `basisPoly`, `eval_basisPoly` and `simplexInt_basisPoly`
(controls in `ControlsSeriesM`). Pure polynomial algebra: nothing here bears on twin primes.
-/

/-- `(1 − P₁)^a · Π_m P_{2(m+1)}^{C m}` on `k` coordinates, as a budget polynomial: the
concatenation, over the assignment tuples `e` (one antidiagonal of `C m` per `m`), of the monomial
`Π_i t_i^{Σ_m 2(m+1)·e m i} · (1 − Σt)^a` with coefficient `Π_m multinomial (e m)`. -/
noncomputable def basisPolyM (M k a : ℕ) (C : Fin M → ℕ) : BPoly k :=
  (Fintype.piFinset fun m => piAntidiag (univ : Finset (Fin k)) (C m)).toList.map
    fun e => ((fun i => ∑ m : Fin M, 2 * ((m : ℕ) + 1) * e m i), a,
      ((∏ m, Nat.multinomial univ (e m) : ℕ) : ℚ))

/-- **G1 at general `M`:** the budget polynomial IS `(1 − Σt)^a · Π_m (Σ_i t_i^{2(m+1)})^{C m}`. -/
theorem eval_basisPolyM (M k a : ℕ) (C : Fin M → ℕ) (t : Fin k → ℝ) :
    eval (basisPolyM M k a C) t
      = (1 - ∑ i, t i) ^ a * ∏ m : Fin M, (∑ i, t i ^ (2 * ((m : ℕ) + 1))) ^ (C m) := by
  unfold eval basisPolyM
  rw [List.map_map, Finset.sum_map_toList]
  have hfac : ∀ m : Fin M, (∑ i, t i ^ (2 * ((m : ℕ) + 1))) ^ (C m)
      = ∑ e ∈ piAntidiag (univ : Finset (Fin k)) (C m),
          (Nat.multinomial univ e : ℝ) * ∏ i, (t i ^ (2 * ((m : ℕ) + 1))) ^ e i :=
    fun m => sum_pow_eq_sum_piAntidiag _ _ _
  rw [Finset.prod_congr rfl fun m _ => hfac m, Finset.prod_univ_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hmono : ∏ i, t i ^ (∑ m : Fin M, 2 * ((m : ℕ) + 1) * e m i)
      = ∏ m : Fin M, ∏ i, (t i ^ (2 * ((m : ℕ) + 1))) ^ e m i := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [pow_mul]
  simp only [Function.comp_apply]
  push_cast
  rw [Finset.prod_mul_distrib, hmono]
  ring

/-- **G2 at general `M`:** its Dirichlet integral is the closed form
`a!·Π_m (C m)!·[x^C] GM^k / (k + a + weight C)!`. -/
theorem simplexInt_basisPolyM (M k a : ℕ) (C : Fin M → ℕ) :
    simplexInt (basisPolyM M k a C)
      = ((a ! : ℕ) : ℚ) * (∏ m, (((C m)! : ℕ) : ℚ)) *
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm C) (GM M ^ k)
          / (((k + a + weight C)! : ℕ) : ℚ) := by
  rw [← symCollectM]
  unfold simplexInt basisPolyM
  rw [List.map_map, Finset.sum_map_toList]
  refine Finset.sum_nbij' (fun e m => Finsupp.equivFunOnFinite.symm (e m)) (fun e m => ⇑(e m))
    ?_ ?_ ?_ ?_ ?_
  · intro e he
    rw [Fintype.mem_piFinset] at he ⊢
    intro m
    rw [mem_finsuppAntidiag]
    exact ⟨(mem_piAntidiag.mp (he m)).1, subset_univ _⟩
  · intro e he
    rw [Fintype.mem_piFinset] at he ⊢
    intro m
    rw [mem_piAntidiag]
    exact ⟨(mem_finsuppAntidiag.mp (he m)).1, fun i _ => mem_univ i⟩
  · intro e _
    rfl
  · intro e _
    funext m
    exact Finsupp.equivFunOnFinite_symm_coe _
  · intro e he
    rw [Fintype.mem_piFinset] at he
    have hm : ∀ m, ((Nat.multinomial univ (e m) : ℕ) : ℚ)
        = (((C m)! : ℕ) : ℚ) / ∏ i, (((e m i)! : ℕ) : ℚ) := by
      intro m
      have hem := (mem_piAntidiag.mp (he m)).1
      have h := Nat.multinomial_spec (univ : Finset (Fin k)) (e m)
      rw [hem] at h
      have hpos : (∏ i, (((e m i)! : ℕ) : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
      rw [eq_div_iff hpos, mul_comm]
      exact_mod_cast h
    simp only [Function.comp_apply]
    rw [Nat.cast_prod, Finset.prod_congr rfl fun m _ => hm m]
    rfl

end Salt.MaynardK
