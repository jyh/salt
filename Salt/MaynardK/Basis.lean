/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.BudgetPoly
import Salt.MaynardK.Series
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Data.Nat.Choose.Multinomial

open Finset Nat Salt.Twelve PowerSeries

namespace Salt.MaynardK

/-!
# C1 glue — Maynard's basis as a symbolic budget polynomial at general `k`
-/

/-- `(1 − P₁)^b · P₂^c` on `k` coordinates, as a budget polynomial: its multinomial expansion. -/
noncomputable def basisPoly (k b c : ℕ) : BPoly k :=
  (piAntidiag (univ : Finset (Fin k)) c).toList.map
    fun e => ((fun i => 2 * e i), b, ((Nat.multinomial univ e : ℕ) : ℚ))

/-- **G1:** the budget polynomial IS `(1 − Σt)^b · (Σ tᵢ²)^c`. -/
theorem eval_basisPoly (k b c : ℕ) (t : Fin k → ℝ) :
    eval (basisPoly k b c) t = (1 - ∑ i, t i) ^ b * (∑ i, t i ^ 2) ^ c := by
  unfold eval basisPoly
  rw [List.map_map, Finset.sum_map_toList, sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Function.comp_apply, pow_mul]
  push_cast
  ring

/-- **G2:** its Dirichlet integral is the closed form `b!·c!·[x^c]G^k / (k+b+2c)!`. -/
theorem simplexInt_basisPoly (k b c : ℕ) :
    simplexInt (basisPoly k b c)
      = ((b ! : ℕ) : ℚ) * (c ! : ℕ) * coeff c (G ^ k) / ((k + b + 2 * c)! : ℕ) := by
  have hG : G ^ k = ∏ _i : Fin k, G := by rw [Finset.prod_const, Finset.card_fin]
  have hconv : ∑ l ∈ finsuppAntidiag (univ : Finset (Fin k)) c, ∏ i ∈ univ, coeff (l i) G
      = ∑ e ∈ piAntidiag (univ : Finset (Fin k)) c, ∏ i, coeff (e i) G := by
    rw [finsuppAntidiag, Finset.sum_map, ← Finset.sum_attach (piAntidiag univ c)]; rfl
  rw [hG, coeff_prod, hconv]
  unfold simplexInt basisPoly DInt'
  rw [List.map_map, Finset.sum_map_toList, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [mem_piAntidiag] at he
  have hs : ∑ i, 2 * e i = 2 * c := by rw [← Finset.mul_sum, he.1]
  have hm : ((Nat.multinomial univ e : ℕ) : ℚ) = ((c ! : ℕ) : ℚ) / ∏ i, (((e i)! : ℕ) : ℚ) := by
    have h := Nat.multinomial_spec (univ : Finset (Fin k)) e
    rw [he.1] at h
    have hpos : (∏ i, (((e i)! : ℕ) : ℚ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [eq_div_iff hpos, mul_comm]; exact_mod_cast h
  simp only [Function.comp_apply, hs, hm, G, coeff_mk]
  have hpos : ∀ i, (((e i)! : ℕ) : ℚ) ≠ 0 := fun i => by exact_mod_cast (Nat.factorial_pos _).ne'
  push_cast
  rw [Finset.prod_div_distrib]
  field_simp

end Salt.MaynardK


