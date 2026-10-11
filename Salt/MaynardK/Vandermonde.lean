/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Multivariate Vandermonde: `Σ_{e ⊨ a} ∏ᵢ C(gᵢ, eᵢ) = C(Σ g, a)`

The coefficient of `Xᵃ` in `∏ᵢ (1 + X)^{gᵢ} = (1 + X)^{Σ g}`. Used to collect a product of two
multinomial expansions (the J side of C1, `simplexInt (sq (contractB m P))`).
-/

open Finset PowerSeries

namespace Salt.MaynardK

theorem vandermonde_pi {k : ℕ} (g : Fin k → ℕ) (a : ℕ) :
    ∑ e ∈ piAntidiag (univ : Finset (Fin k)) a, ∏ i, (g i).choose (e i) = (∑ i, g i).choose a := by
  classical
  set f : Fin k → PowerSeries ℕ := fun i => ((Polynomial.X + 1) ^ g i : Polynomial ℕ)
  have h1 : (((∏ i, (Polynomial.X + 1) ^ g i : Polynomial ℕ)) : PowerSeries ℕ) = ∏ i, f i := by
    exact map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℕ))
      (fun i => (Polynomial.X + 1) ^ g i) univ
  have hprod : ∏ i, f i = ((Polynomial.X + 1) ^ (∑ i, g i) : Polynomial ℕ) := by
    rw [← h1, Finset.prod_pow_eq_pow_sum]
  have hc := coeff_prod f a univ
  rw [hprod, Polynomial.coeff_coe, Polynomial.coeff_X_add_one_pow, Nat.cast_id] at hc
  rw [hc]
  have hconv : ∑ l ∈ finsuppAntidiag (univ : Finset (Fin k)) a, ∏ i ∈ univ, coeff (l i) (f i)
      = ∑ e ∈ piAntidiag (univ : Finset (Fin k)) a, ∏ i, coeff (e i) (f i) := by
    rw [finsuppAntidiag, Finset.sum_map, ← Finset.sum_attach (piAntidiag univ a)]; rfl
  rw [hconv]
  refine Finset.sum_congr rfl fun e _ => Finset.prod_congr rfl fun i _ => ?_
  simp only [f, Polynomial.coeff_coe, Polynomial.coeff_X_add_one_pow, Nat.cast_id]

end Salt.MaynardK
