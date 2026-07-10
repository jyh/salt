/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Diagonal
import Salt.Maynard.DiagonalS2
import Salt.Maynard.S2DiagLam

/-!
# The `dₘ = eₘ = 1`-restricted S₂ diagonalisation (Maynard)

This file proves the `m`-coordinate-pinned analog of `s2_diag_lam`
(`S2DiagLam.lean`).  Restricting the S₂ quadratic form to the sub-lattice
`{(d,e) : dₘ = eₘ = 1}` diagonalises it to `∑_{u : uₘ=1} (∏ g(uᵢ))·Vₘ(u)²`,
where the `m`-restricted contraction

  `Vₘ(u) = lamPhiContractM u = ∑_{d∈𝒟, dₘ=1, uᵢ∣dᵢ} lam_d / ∏φ(dᵢ)`

carries the `dₘ = 1` filter throughout.  The pin `dₘ = 1` (resp. `eₘ = 1`) is a
`Finset.filter` on the outer `d`- (resp. `e`-) sum; it commutes with the whole
`s2_diag_lam` argument.  The `u`-sum's pin `uₘ = 1` is *forced*: on the support
`uₘ ∣ dₘ = 1`, so any `u` with `uₘ ≠ 1` contributes zero (its `lamPhiContractM`
vanishes term-by-term), and the `u`-sum over `𝒟` collapses onto the `uₘ = 1`
filter.

The proof mirrors `s2_diag_lam` step for step with the `dₘ=1`/`eₘ=1` filters
threaded through, reusing the exported ingredients `prod_totient_gcd_expand`,
`totient_gcd_mul_totient_lcm` and the `mul_ite_zero` normal form.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-- Move the innermost of three nested sums to the front (local copy; `private`
in the `S2DiagLam` file). -/
private theorem sum_move3R {α β γ δ : Type*} [AddCommMonoid δ]
    (A : Finset α) (B : Finset β) (C : Finset γ) (F : α → β → γ → δ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c)
      = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, F a b c := by
  rw [← Finset.sum_product']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  exact Finset.sum_product' A B (fun a b => F a b c)

/-- **The `m`-restricted contraction `Vₘ(u)`.** The `lam`-weighted `φ`-density
sum restricted to the sub-lattice `dₘ = 1` and to multiples of `u`.  This is the
`dₘ = 1`-filtered analog of `wsum_lam_phi`'s left-hand side. -/
noncomputable def lamPhiContractM (k R W : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (u : Fin k → ℕ) : ℝ :=
  ∑ d ∈ (kSieveIndex k R W).filter (fun d => d m = 1),
    (if (∀ i, u i ∣ d i) then lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ) else 0)

/-- **The `dₘ = eₘ = 1`-restricted S₂ diagonalisation.** With the *actual* sieve
weight `lam`, the S₂ quadratic form over the pinned sub-lattice
`{(d,e) : dₘ = eₘ = 1}` with denominator `∏ᵢ φ(lcm(dᵢ,eᵢ))` diagonalises to
`∑_{u : uₘ=1} (∏ᵢ g(uᵢ))·Vₘ(u)²`, where `Vₘ(u) = lamPhiContractM u`. -/
theorem s2_diag_lam_restricted (k R W : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) :
    ∑ d ∈ (kSieveIndex k R W).filter (fun d => d m = 1),
      ∑ e ∈ (kSieveIndex k R W).filter (fun e => e m = 1),
        lam k R W y d * lam k R W y e / ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)
      = ∑ u ∈ (kSieveIndex k R W).filter (fun u => u m = 1),
          (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R W m y u) ^ 2 := by
  -- (stepA) per-`(d,e)` in `𝒟`: split off `∏ φ(gcd)` from `1/∏ φ(lcm)`.
  have stepA : ∀ d ∈ kSieveIndex k R W, ∀ e ∈ kSieveIndex k R W,
      lam k R W y d * lam k R W y e / ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)
        = (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ))
          * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
          * ∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ) := by
    intro d hd e he
    have hdsq : ∀ i, Squarefree (d i) := fun i => ((mem_kSieveIndex_iff d).mp hd).1 i
    have hesq : ∀ i, Squarefree (e i) := fun i => ((mem_kSieveIndex_iff e).mp he).1 i
    have hφd : (∏ i, (Nat.totient (d i) : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro i _
      exact_mod_cast (Nat.totient_pos.mpr (kSieveIndex_coord_pos hd i)).ne'
    have hφe : (∏ i, (Nat.totient (e i) : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro i _
      exact_mod_cast (Nat.totient_pos.mpr (kSieveIndex_coord_pos he i)).ne'
    have hφlcm : (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro i _
      have : 0 < Nat.totient (Nat.lcm (d i) (e i)) := Nat.totient_pos.mpr
        (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (kSieveIndex_coord_pos hd i).ne'
          (kSieveIndex_coord_pos he i).ne'))
      exact_mod_cast this.ne'
    have hkey : (∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))
          * (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))
        = (∏ i, (Nat.totient (d i) : ℝ)) * (∏ i, (Nat.totient (e i) : ℝ)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      exact totient_gcd_mul_totient_lcm (hdsq i) (hesq i)
    rw [div_eq_iff hφlcm]
    rw [show (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ))
            * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
            * (∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))
            * (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))
          = (lam k R W y d * lam k R W y e)
            / ((∏ i, (Nat.totient (d i) : ℝ)) * (∏ i, (Nat.totient (e i) : ℝ)))
            * ((∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))
              * (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))) from by ring]
    rw [hkey, div_mul_cancel₀ _ (mul_ne_zero hφd hφe)]
  -- (hMain) rewrite each summand as a `∑_{u∈𝒟}` via `stepA` + `prod_totient_gcd_expand`.
  have hMain : ∀ d ∈ kSieveIndex k R W, ∀ e ∈ kSieveIndex k R W,
      lam k R W y d * lam k R W y e / ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)
        = ∑ u ∈ kSieveIndex k R W,
            (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ))
              * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
              * (if (∀ i, u i ∣ d i ∧ u i ∣ e i) then ∏ i, (gMult (u i) : ℝ) else 0) := by
    intro d hd e he
    rw [stepA d hd e he, prod_totient_gcd_expand hd, Finset.mul_sum]
  -- (hInner) per-`u∈𝒟` collapse to `∏ g(uᵢ)·Vₘ(u)²`.
  have hInner : ∀ u ∈ kSieveIndex k R W,
      (∑ d ∈ (kSieveIndex k R W).filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R W).filter (fun e => e m = 1),
        (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ))
          * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
          * (if (∀ i, u i ∣ d i ∧ u i ∣ e i) then ∏ i, (gMult (u i) : ℝ) else 0))
        = (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R W m y u) ^ 2 := by
    intro u _
    have he2 : (∑ e ∈ (kSieveIndex k R W).filter (fun e => e m = 1),
          (if (∀ i, u i ∣ e i) then
            (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ)) * ∏ i, (gMult (u i) : ℝ) else 0))
        = (∏ i, (gMult (u i) : ℝ)) * lamPhiContractM k R W m y u := by
      rw [lamPhiContractM, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro e _
      rw [mul_ite_zero]; split_ifs with h
      · ring
      · rfl
    have he1 : (∑ d ∈ (kSieveIndex k R W).filter (fun d => d m = 1),
          (if (∀ i, u i ∣ d i) then lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ) else 0))
        = lamPhiContractM k R W m y u := rfl
    calc (∑ d ∈ (kSieveIndex k R W).filter (fun d => d m = 1),
          ∑ e ∈ (kSieveIndex k R W).filter (fun e => e m = 1),
          (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ))
            * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
            * (if (∀ i, u i ∣ d i ∧ u i ∣ e i) then ∏ i, (gMult (u i) : ℝ) else 0))
        = (∑ d ∈ (kSieveIndex k R W).filter (fun d => d m = 1),
              (if (∀ i, u i ∣ d i) then lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ) else 0))
          * (∑ e ∈ (kSieveIndex k R W).filter (fun e => e m = 1),
              (if (∀ i, u i ∣ e i) then
                (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
                  * ∏ i, (gMult (u i) : ℝ)
                else 0)) := by
          rw [Finset.sum_mul_sum]
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro e _
          by_cases hP : ∀ i, u i ∣ d i <;> by_cases hQ : ∀ i, u i ∣ e i
          · rw [if_pos (forall_and.mpr ⟨hP, hQ⟩), if_pos hP, if_pos hQ]; ring
          · rw [if_neg (fun h => hQ (forall_and.mp h).2), if_pos hP, if_neg hQ]; ring
          · rw [if_neg (fun h => hP (forall_and.mp h).1), if_neg hP, if_pos hQ]; ring
          · rw [if_neg (fun h => hP (forall_and.mp h).1), if_neg hP, if_neg hQ]; ring
      _ = lamPhiContractM k R W m y u
            * ((∏ i, (gMult (u i) : ℝ)) * lamPhiContractM k R W m y u) := by
          rw [he1, he2]
      _ = (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R W m y u) ^ 2 := by ring
  -- (hzero) the `u`-pin `uₘ = 1` is forced: any `u` with `uₘ ≠ 1` contributes zero.
  have hzero : ∀ u ∈ kSieveIndex k R W, ¬ (u m = 1) →
      (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R W m y u) ^ 2 = 0 := by
    intro u _ hum
    have hV : lamPhiContractM k R W m y u = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [Finset.mem_filter] at hd
      rw [if_neg]
      intro hall
      exact hum (Nat.dvd_one.mp (hd.2 ▸ hall m))
    rw [hV]; ring
  -- assemble: rewrite the LHS, swap the forced `u`-sum to the front, collapse per `u`,
  -- then restrict the `u`-sum onto the `uₘ = 1` filter (killing the `uₘ ≠ 1` terms).
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he =>
    hMain d (Finset.mem_filter.mp hd).1 e (Finset.mem_filter.mp he).1))]
  rw [sum_move3R]
  rw [Finset.sum_congr rfl (fun u hu => hInner u hu)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro u hu
  split_ifs with h
  · rfl
  · exact hzero u hu h

end Salt.Maynard
