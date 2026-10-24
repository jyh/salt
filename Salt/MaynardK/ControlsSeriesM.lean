/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.Basis
import Salt.MaynardK.BasisM

/-!
# Controls: the general-`M` series and basis recover the landed `M = 1` statements

Each control below is a NEW theorem whose statement is a landed `M = 1` result of `Series` or
`Basis`, restated by `type_of%` (so it cannot drift from the original by a binder), and proved
from its general-`M` generalisation in `SeriesM`/`BasisM` at `M = 1` — never from the original.
They are checks on the generalisations, not inputs to `gaps_le_636`: none of them is in its
dependency closure. Pure polynomial and series algebra: nothing here bears on twin primes.

The `M = 1` reindexing: `Fin 1 → ℕ ≅ ℕ` (`fun _ => c ↔ c`), `weight (fun _ => c) = 2·c`, and
`[x^{(c)}] GM 1^k = [x^c] G^k` (`coeff_GM_one_pow`, by induction on `k` through
`Finsupp.antidiagonal_single`).
-/

open Finset Nat Salt.Twelve

namespace Salt.MaynardK

/-- At `M = 1` the weight of the constant tuple is `2c`: `weight (fun _ : Fin 1 => c) = 2 * c`
(`weight j = Σₘ 2(m+1)·jₘ`).
-/
lemma weight_one (c : ℕ) : weight (fun _ : Fin 1 => c) = 2 * c := by
  simp [weight]

/-- The `M = 1` reindexing on the `Finsupp` side: `Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 =>
c) = Finsupp.single 0 c`.
-/
lemma equivFunOnFinite_symm_fin_one (c : ℕ) :
    Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => c) = Finsupp.single 0 c :=
  Finsupp.ext fun m => by rw [Fin.fin_one_eq_zero m]; simp

/-- `GM 1` is `G` read in one variable: `[x^{(c)}] GM 1^k = [x^c] G^k`. -/
lemma coeff_GM_one_pow (k : ℕ) : ∀ c : ℕ,
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) c) (GM 1 ^ k)
      = PowerSeries.coeff c (G ^ k) := by
  induction k with
  | zero =>
    intro c
    rw [pow_zero, pow_zero, MvPowerSeries.coeff_one, PowerSeries.coeff_one]
    simp [Finsupp.single_eq_zero]
  | succ k ih =>
    intro c
    rw [pow_succ, pow_succ, MvPowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finsupp.antidiagonal_single, Finset.sum_map]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_fst,
      Prod.map_snd]
    rw [ih, coeff_GM]
    congr 1
    simp [G, PowerSeries.coeff_mk, weight]

/-- `(T k)[n] = TM 1 k 22 [enc (n)]` for `n ≤ 11` (the two tables run the same convolution). -/
lemma T_eq_TM_one (k : ℕ) : ∀ n, n < 12 →
    (T k).getD n 0 = ((TM 1 k 22).lookup (enc fun _ : Fin 1 => n)).getD 0 := by
  induction k with
  | zero =>
    intro n hn
    rw [TM_zero_lookup (by norm_num) (by rw [weight_one]; omega), Option.getD_some]
    simp only [T, Function.iterate_zero, id]
    have h0 : ((fun _ : Fin 1 => n) = 0) ↔ n = 0 :=
      ⟨fun h => congrFun h 0, fun h => by subst h; rfl⟩
    simp only [h0]
    interval_cases n <;> rfl
  | succ k ih =>
    intro n hn
    rw [TM_succ_lookup (by norm_num) (by rw [weight_one]; omega), Option.getD_some]
    have hT : T (k + 1) = pmul (T k) := by simp only [T, Function.iterate_succ_apply']
    rw [hT]
    unfold pmul
    rw [getD_map_range _ _ _ _ hn, list_sum_range]
    unfold tstep boxM
    symm
    refine Finset.sum_nbij' (fun A => A 0) (fun i _ => i) ?_ ?_ ?_ ?_ ?_
    · intro A hA
      exact (Fintype.mem_piFinset.mp hA) 0
    · intro i hi
      rw [Fintype.mem_piFinset]
      intro _
      exact hi
    · intro A _
      funext m
      simp only [Fin.fin_one_eq_zero m]
    · intro i _
      rfl
    · intro A hA
      have hA0 : A 0 < n + 1 := Finset.mem_range.mp ((Fintype.mem_piFinset.mp hA) 0)
      obtain ⟨i, rfl⟩ : ∃ i, A = fun _ => i :=
        ⟨A 0, funext fun m => by simp only [Fin.fin_one_eq_zero m]⟩
      dsimp only at hA0 ⊢
      rw [ih i (by omega)]
      congr 1
      have hsub : ((fun _ : Fin 1 => n) - fun _ => i) = fun _ => n - i := rfl
      rw [hsub]
      unfold g
      rw [getD_map_range _ _ _ _ (by omega)]
      simp [gN, weight]

/-- CONTROL: `symCollect`, restated by `type_of%`, from `symCollectM 1`. -/
theorem symCollect' : type_of% @symCollect := by
  intro k b c
  refine Eq.trans ?_ ((symCollectM 1 k b (fun _ => c)).trans ?_)
  · refine Finset.sum_nbij' (fun e _ => e) (fun e => e 0) ?_ ?_ ?_ ?_ ?_
    · intro e he
      rw [Fintype.mem_piFinset]
      intro _
      exact he
    · intro e he
      exact (Fintype.mem_piFinset.mp he) 0
    · intro e _
      rfl
    · intro e _
      funext m
      simp only [Fin.fin_one_eq_zero m]
    · intro e _
      simp
  · rw [equivFunOnFinite_symm_fin_one, coeff_GM_one_pow, weight_one, Fin.prod_univ_one]

/-- CONTROL: `T_eq_coeff`, restated by `type_of%`, from `T_eq_coeffM 1 k 22` and the landed `T`'s
definition (`weight (fun _ => n) = 2n ≤ 22` covers exactly `n ≤ 11`). -/
theorem T_eq_coeff' : type_of% @T_eq_coeff := by
  intro k n hn
  rw [T_eq_TM_one k n hn,
    T_eq_coeffM_getD 1 k 22 (by norm_num) _ (by rw [weight_one]; omega),
    equivFunOnFinite_symm_fin_one, coeff_GM_one_pow]

/-- `basisPoly k b c` and `basisPolyM 1 k b (fun _ => c)` have the same Dirichlet integral (the
same monomials, indexed by `piAntidiag` and by its `Fin 1`-tuples). -/
lemma simplexInt_basisPoly_eq_M (k b c : ℕ) :
    simplexInt (basisPoly k b c) = simplexInt (basisPolyM 1 k b fun _ => c) := by
  unfold simplexInt basisPoly basisPolyM
  rw [List.map_map, List.map_map, Finset.sum_map_toList, Finset.sum_map_toList]
  refine Finset.sum_nbij' (fun e _ => e) (fun e => e 0) ?_ ?_ ?_ ?_ ?_
  · intro e he
    rw [Fintype.mem_piFinset]
    intro _
    exact he
  · intro e he
    exact (Fintype.mem_piFinset.mp he) 0
  · intro e _
    rfl
  · intro e _
    funext m
    simp only [Fin.fin_one_eq_zero m]
  · intro e _
    simp

/-- CONTROL: `simplexInt_basisPoly`, restated by `type_of%`, from
`simplexInt_basisPolyM 1 k b (fun _ => c)`. -/
theorem simplexInt_basisPoly' : type_of% @simplexInt_basisPoly := by
  intro k b c
  rw [simplexInt_basisPoly_eq_M, simplexInt_basisPolyM, equivFunOnFinite_symm_fin_one,
    coeff_GM_one_pow, weight_one, Fin.prod_univ_one]

end Salt.MaynardK
