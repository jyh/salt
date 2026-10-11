/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.BudgetPoly
import Salt.MaynardK.Cert105
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Antidiag.Finsupp

open Finset Nat Salt.Twelve PowerSeries

namespace Salt.MaynardK

/-!
# C1 bridge B1 — the certificate's table is the Dirichlet main term of the basis

`symCollect`: the Dirichlet main term (`DInt'`) of `(1 − P₁)^b · P₂^c` summed over its multinomial
expansion is
`b!·c!·[x^c]G^k/(k+b+2c)!`; `T_eq_coeff`: the certificate's list table `T k` (`Cert105`) is
`[xⁿ]G^k` for `n ≤ 11`.
-/

/-- `G = Σ_j (2j)!/j! · Xʲ`. -/
noncomputable def G : PowerSeries ℚ :=
  PowerSeries.mk fun j => (((2 * j)! : ℕ) : ℚ) / ((j ! : ℕ) : ℚ)

/-- **B1(a′)** over `finsuppAntidiag`: the Dirichlet main term of `(1 − P₁)^b · P₂^c` summed over
its multinomial
expansion equals `b!·c!·[x^c]G^k / (k+b+2c)!`. -/
theorem symCollect (k b c : ℕ) :
    ∑ e ∈ finsuppAntidiag (univ : Finset (Fin k)) c,
        (((c ! : ℕ) : ℚ) / ∏ i, ((e i)! : ℕ)) * DInt' (fun i => 2 * e i) b
      = ((b ! : ℕ) : ℚ) * (c ! : ℕ) * coeff c (G ^ k) / ((k + b + 2 * c)! : ℕ) := by
  have hG : G ^ k = ∏ _i : Fin k, G := by rw [Finset.prod_const, Finset.card_fin]
  rw [hG, coeff_prod]
  unfold DInt'
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [mem_finsuppAntidiag] at he
  have hs : ∑ i, 2 * e i = 2 * c := by rw [← Finset.mul_sum, he.1]
  rw [hs]
  simp only [G, coeff_mk]
  have hpos : ∀ i, (((e i)! : ℕ) : ℚ) ≠ 0 := fun i => by exact_mod_cast (Nat.factorial_pos _).ne'
  push_cast
  rw [Finset.prod_div_distrib]
  field_simp

/-! ## B1(b): the C1 certificate's list table IS `[x^n] G^k` (n ≤ 11) -/

lemma getD_map_range {β : Type*} (f : ℕ → β) (m n : ℕ) (d : β) (h : n < m) :
    ((List.range m).map f).getD n d = f n := by
  simp [List.getD_eq_getElem?_getD, h]

lemma list_sum_range (f : ℕ → ℕ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]

lemma g_getD (j : ℕ) (h : j < 12) :
    ((g.getD j 0 : ℕ) : ℚ) = (((2 * j)! : ℕ) : ℚ) / ((j ! : ℕ) : ℚ) := by
  unfold g
  rw [getD_map_range _ _ _ _ h, Nat.cast_div (Nat.factorial_dvd_factorial (by omega))
    (by exact_mod_cast (Nat.factorial_pos _).ne')]

theorem T_eq_coeff (k : ℕ) : ∀ n, n < 12 → (((T k).getD n 0 : ℕ) : ℚ) = coeff n (G ^ k) := by
  induction k with
  | zero =>
    intro n hn
    simp only [T, Function.iterate_zero, id, pow_zero, coeff_one]
    interval_cases n <;> simp
  | succ k ih =>
    intro n hn
    have hT : T (k + 1) = pmul (T k) := by simp only [T, Function.iterate_succ_apply']
    rw [hT, pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    unfold pmul
    rw [getD_map_range _ _ _ _ hn, list_sum_range]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [ih i (by omega), g_getD (n - i) (by omega)]
    simp [G, coeff_mk]

end Salt.MaynardK


