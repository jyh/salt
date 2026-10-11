/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Multivariate Vandermonde: `Σ_{e ⊨ a} ∏ᵢ C(gᵢ, eᵢ) = C(Σ g, a)`

The coefficient of `Xᵃ` in `∏ᵢ (1 + X)^{gᵢ} = (1 + X)^{Σ g}`. Used to collect a product of two
multinomial expansions (the J side of C1, `simplexInt (sq (contractB m P))`).
-/

open Finset PowerSeries
open scoped Nat

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

/-- the multinomial coefficient of `e`, as a rational: `(Σ e)! / ∏ eᵢ!`. -/
lemma multinomial_cast {k : ℕ} (e : Fin k → ℕ) :
    ((Nat.multinomial univ e : ℕ) : ℚ) = (((∑ i, e i)! : ℕ) : ℚ) / ∏ i, (((e i)! : ℕ) : ℚ) := by
  have h := Nat.multinomial_spec (univ : Finset (Fin k)) e
  have hpos : (∏ i, (((e i)! : ℕ) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [eq_div_iff hpos, mul_comm]; exact_mod_cast h

/-- one fiber of the convolution: `Σ_{e + f = h, e ⊨ a, f ⊨ b} mult e · mult f = mult h`. -/
lemma mult_fiber {k : ℕ} (a b : ℕ) (h : Fin k → ℕ) (hh : ∑ i, h i = a + b) :
    ∑ e ∈ (piAntidiag (univ : Finset (Fin k)) a).filter (fun e => ∀ i, e i ≤ h i),
        ((Nat.multinomial univ e : ℕ) : ℚ) * (Nat.multinomial univ (h - e) : ℕ)
      = (Nat.multinomial univ h : ℕ) := by
  classical
  have hfact : ∀ i, (((h i)! : ℕ) : ℚ) ≠ 0 := fun i => by exact_mod_cast (Nat.factorial_pos _).ne'
  have key : ∀ e ∈ (piAntidiag (univ : Finset (Fin k)) a).filter (fun e => ∀ i, e i ≤ h i),
      ((Nat.multinomial univ e : ℕ) : ℚ) * (Nat.multinomial univ (h - e) : ℕ)
        = ((a ! * b ! : ℕ) : ℚ) / (∏ i, (((h i)! : ℕ) : ℚ))
            * ∏ i, (((h i).choose (e i) : ℕ) : ℚ) := by
    intro e he
    rw [Finset.mem_filter, mem_piAntidiag] at he
    obtain ⟨⟨hea0, -⟩, hle⟩ := he
    have hea : ∑ i, e i = a := hea0
    have hsub : ∑ i, (h - e) i = b := by
      have : ∑ i, (h - e) i + ∑ i, e i = ∑ i, h i := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by
          simp only [Pi.sub_apply]; exact Nat.sub_add_cancel (hle i)
      omega
    rw [multinomial_cast, multinomial_cast, hea, hsub]
    have hc : ∀ i, (((h i).choose (e i) : ℕ) : ℚ)
        = (((h i)! : ℕ) : ℚ) / ((((e i)! : ℕ) : ℚ) * (((h i - e i)! : ℕ) : ℚ)) := by
      intro i
      have := Nat.choose_mul_factorial_mul_factorial (hle i)
      have h1 : (((e i)! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      have h2 : (((h i - e i)! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      rw [eq_div_iff (mul_ne_zero h1 h2), ← mul_assoc]; exact_mod_cast this
    simp only [hc, Pi.sub_apply, Finset.prod_div_distrib, Finset.prod_mul_distrib]
    have he0 : (∏ i, (((e i)! : ℕ) : ℚ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
    have hs0 : (∏ i, (((h i - e i)! : ℕ) : ℚ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
    have hh0 : (∏ i, (((h i)! : ℕ) : ℚ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hfact i
    push_cast
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  have hext : ∑ e ∈ (piAntidiag (univ : Finset (Fin k)) a).filter (fun e => ∀ i, e i ≤ h i),
      ∏ i, (((h i).choose (e i) : ℕ) : ℚ)
      = ∑ e ∈ piAntidiag (univ : Finset (Fin k)) a, ∏ i, (((h i).choose (e i) : ℕ) : ℚ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs with hle
    · rfl
    · simp only [not_forall, not_le] at hle
      obtain ⟨i, hi⟩ := hle
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Nat.choose_eq_zero_of_lt hi]; simp)
  rw [hext]
  have hv := vandermonde_pi h a
  rw [hh] at hv
  have hv' : ∑ e ∈ piAntidiag (univ : Finset (Fin k)) a, ∏ i, (((h i).choose (e i) : ℕ) : ℚ)
      = (((a + b).choose a : ℕ) : ℚ) := by rw [← hv]; push_cast; rfl
  rw [hv', multinomial_cast, hh]
  have hab := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rw [Nat.add_sub_cancel_left] at hab
  have hh0 : (∏ i, (((h i)! : ℕ) : ℚ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hfact i
  rw [← hab]; push_cast; field_simp

/-- **The multinomial convolution:** `Σ_{e ⊨ a} Σ_{f ⊨ b} mult e · mult f · φ(e + f)
    = Σ_{h ⊨ a+b} mult h · φ h`. -/
theorem mult_conv {k : ℕ} (a b : ℕ) (φ : (Fin k → ℕ) → ℚ) :
    ∑ e ∈ piAntidiag (univ : Finset (Fin k)) a, ∑ f ∈ piAntidiag (univ : Finset (Fin k)) b,
        ((Nat.multinomial univ e : ℕ) : ℚ) * (Nat.multinomial univ f : ℕ) * φ (e + f)
      = ∑ h ∈ piAntidiag (univ : Finset (Fin k)) (a + b)
          , ((Nat.multinomial univ h : ℕ) : ℚ) * φ h := by
  classical
  rw [← Finset.sum_product']
  have hmaps : ∀ p ∈ piAntidiag (univ : Finset (Fin k)) a ×ˢ piAntidiag (univ : Finset (Fin k)) b,
      p.1 + p.2 ∈ piAntidiag (univ : Finset (Fin k)) (a + b) := by
    intro p hp
    rw [Finset.mem_product, mem_piAntidiag, mem_piAntidiag] at hp
    rw [mem_piAntidiag]
    refine ⟨by simp [Finset.sum_add_distrib, hp.1.1, hp.2.1], fun i _ => Finset.mem_univ i⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [mem_piAntidiag] at hh
  have hφ : ∀ p ∈ (piAntidiag (univ : Finset (Fin k)) a
      ×ˢ piAntidiag (univ : Finset (Fin k)) b).filter
      (fun p => p.1 + p.2 = h),
      ((Nat.multinomial univ p.1 : ℕ) : ℚ) * (Nat.multinomial univ p.2 : ℕ) * φ (p.1 + p.2)
        = ((Nat.multinomial univ p.1 : ℕ) : ℚ) * (Nat.multinomial univ p.2 : ℕ) * φ h := by
    intro p hp; rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl hφ, ← Finset.sum_mul, ← mult_fiber a b h hh.1]
  congr 1
  refine Finset.sum_nbij' (fun p => p.1) (fun e => (e, h - e)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    rw [Finset.mem_filter]
    refine ⟨hp.1.1, fun i => ?_⟩
    rw [← hp.2]; simp
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨hea0, hle⟩ := he
    rw [mem_piAntidiag] at hea0
    have hea : ∑ i, e i = a := hea0.1
    have hh' : ∑ i, h i = a + b := hh.1
    rw [Finset.mem_filter, Finset.mem_product, mem_piAntidiag, mem_piAntidiag]
    have hsum : ∑ i, (h - e) i = b := by
      have : ∑ i, (h - e) i + ∑ i, e i = ∑ i, h i := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by
          simp only [Pi.sub_apply]; exact Nat.sub_add_cancel (hle i)
      omega
    refine ⟨⟨hea0, ⟨hsum, fun i _ => Finset.mem_univ i⟩⟩, ?_⟩
    funext i; simp only [Pi.add_apply, Pi.sub_apply]; exact Nat.add_sub_cancel' (hle i)
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨p1, p2⟩ := p
    have h2 : p1 + p2 = h := hp.2
    rw [← h2]
    ext i <;> simp
  · intro e _; rfl
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨p1, p2⟩ := p
    have h2 : p1 + p2 = h := hp.2
    subst h2
    have e : p1 + p2 - p1 = p2 := by funext i; simp
    simp [e]

end Salt.MaynardK
