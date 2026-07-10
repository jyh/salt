/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.KSieve
import Salt.Brun.SelbergPort

/-!
# The k-dimensional S₁ diagonalisation (blueprint N2.2 + N2.4)

This is the k-dimensional Selberg diagonalisation: the linchpin of the
Maynard M4/M5 spine. It generalises the 1-dim Möbius inversion
(`Salt.SelbergPort.moebius_inv_dvd_lower_bound`) to `k` coordinates via a
coordinate tensor built with `Finset.prod_univ_sum`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-! ## Small reindexing helper -/

/-- Move the innermost of three nested sums to the front. -/
private theorem sum_move3 {α β γ δ : Type*} [AddCommMonoid δ]
    (A : Finset α) (B : Finset β) (C : Finset γ) (F : α → β → γ → δ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c)
      = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, F a b c := by
  rw [← Finset.sum_product']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  exact Finset.sum_product' A B (fun a b => F a b c)

/-- Move the outer pair of four nested sums (over one common set) to the back. -/
private theorem sum_move4 {α δ : Type*} [AddCommMonoid δ] (A : Finset α)
    (F : α → α → α → α → δ) :
    (∑ d ∈ A, ∑ e ∈ A, ∑ r ∈ A, ∑ s ∈ A, F d e r s)
      = ∑ r ∈ A, ∑ s ∈ A, ∑ d ∈ A, ∑ e ∈ A, F d e r s := by
  calc (∑ d ∈ A, ∑ e ∈ A, ∑ r ∈ A, ∑ s ∈ A, F d e r s)
      = ∑ p ∈ A ×ˢ A, ∑ q ∈ A ×ˢ A, F p.1 p.2 q.1 q.2 := by
        rw [← Finset.sum_product']
        apply Finset.sum_congr rfl; intro p _
        rw [← Finset.sum_product']
    _ = ∑ q ∈ A ×ˢ A, ∑ p ∈ A ×ˢ A, F p.1 p.2 q.1 q.2 := Finset.sum_comm
    _ = ∑ r ∈ A, ∑ s ∈ A, ∑ d ∈ A, ∑ e ∈ A, F d e r s := by
        rw [Finset.sum_product' A A (fun a b => ∑ p ∈ A ×ˢ A, F p.1 p.2 a b)]
        apply Finset.sum_congr rfl; intro r _
        apply Finset.sum_congr rfl; intro s _
        exact Finset.sum_product' A A (fun d e => F d e r s)

/-! ## The two hard standalone Finset lemmas (P3 + P6) -/

/-- **1-dim Möbius–gcd kernel (the fused P2/P3/P6 core).** For squarefree
`r, s`, the twisted double divisor sum collapses to a Kronecker delta times
the totient. This is the coordinate building block of the whole
diagonalisation. -/
theorem kernel1 {r s : ℕ} (hr : Squarefree r) (hs : Squarefree s) :
    (∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
        ((μ d : ℤ) : ℝ) * ((μ e : ℤ) : ℝ) * (Nat.gcd d e : ℝ))
      = if r = s then (Nat.totient r : ℝ) else 0 := by
  have hr0 : r ≠ 0 := hr.ne_zero
  have hs0 : s ≠ 0 := hs.ne_zero
  -- (P2) gcd d e as a totient sum over `r.divisors`, guarded by `u ∣ d ∧ u ∣ e`.
  have hgcd : ∀ d ∈ r.divisors, ∀ e ∈ s.divisors,
      (Nat.gcd d e : ℝ)
        = ∑ u ∈ r.divisors, if u ∣ d ∧ u ∣ e then (Nat.totient u : ℝ) else 0 := by
    intro d hd e _
    have hdr : d ∣ r := Nat.dvd_of_mem_divisors hd
    have hgr : Nat.gcd d e ∣ r := (Nat.gcd_dvd_left d e).trans hdr
    have hsum : (∑ u ∈ (Nat.gcd d e).divisors, (Nat.totient u : ℝ)) = (Nat.gcd d e : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast Nat.sum_totient _
    rw [← hsum, Salt.SelbergPort.sum_over_dvd_ite hr0 hgr]
    apply Finset.sum_congr rfl
    intro u _
    simp only [Nat.dvd_gcd_iff]
  -- (P2 substitution) rewrite each `gcd` as the guarded totient sum
  have hsub : (∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
          ((μ d : ℤ) : ℝ) * ((μ e : ℤ) : ℝ) * (Nat.gcd d e : ℝ))
        = ∑ d ∈ r.divisors, ∑ e ∈ s.divisors, ∑ u ∈ r.divisors,
            if u ∣ d ∧ u ∣ e then
              ((μ d : ℤ) : ℝ) * ((μ e : ℤ) : ℝ) * (Nat.totient u : ℝ) else 0 := by
    apply Finset.sum_congr rfl; intro d hd
    apply Finset.sum_congr rfl; intro e he
    rw [hgcd d hd e he, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _
    rw [mul_ite_zero]
  calc
    (∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
          ((μ d : ℤ) : ℝ) * ((μ e : ℤ) : ℝ) * (Nat.gcd d e : ℝ))
        = ∑ u ∈ r.divisors, ∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
            if u ∣ d ∧ u ∣ e then
              ((μ d : ℤ) : ℝ) * ((μ e : ℤ) : ℝ) * (Nat.totient u : ℝ) else 0 := by
        rw [hsub, sum_move3]
    _ = ∑ u ∈ r.divisors,
          (Nat.totient u : ℝ)
            * (∑ d ∈ r.divisors, if u ∣ d then ((μ d : ℤ) : ℝ) else 0)
            * (∑ e ∈ s.divisors, if u ∣ e then ((μ e : ℤ) : ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro u _
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _
        rw [ite_zero_mul_ite_zero, mul_ite_zero]
        split_ifs with h <;> ring
    _ = ∑ u ∈ r.divisors,
          (Nat.totient u : ℝ)
            * (if u = r then ((μ u : ℤ) : ℝ) else 0)
            * (if u = s then ((μ u : ℤ) : ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro u _
        have h1 : (∑ d ∈ r.divisors, if u ∣ d then ((μ d : ℤ) : ℝ) else 0)
            = if u = r then ((μ u : ℤ) : ℝ) else 0 := by
          exact_mod_cast Salt.SelbergPort.moebius_inv_dvd_lower_bound u r hr
        have h2 : (∑ e ∈ s.divisors, if u ∣ e then ((μ e : ℤ) : ℝ) else 0)
            = if u = s then ((μ u : ℤ) : ℝ) else 0 := by
          exact_mod_cast Salt.SelbergPort.moebius_inv_dvd_lower_bound u s hs
        rw [h1, h2]
    _ = if r = s then (Nat.totient r : ℝ) else 0 := by
        by_cases hrs : r = s
        · subst hrs
          rw [if_pos rfl]
          rw [Finset.sum_eq_single r]
          · rw [if_pos rfl]
            have hμ : ((μ r : ℤ) : ℝ) * ((μ r : ℤ) : ℝ) = 1 := by
              have : ((μ r : ℤ) : ℝ) ^ 2 = 1 := by
                rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hr,
                  Int.cast_one]
              nlinarith [this]
            rw [show (Nat.totient r : ℝ) * ((μ r : ℤ) : ℝ) * ((μ r : ℤ) : ℝ)
                  = (Nat.totient r : ℝ) * (((μ r : ℤ) : ℝ) * ((μ r : ℤ) : ℝ)) from by ring,
              hμ, mul_one]
          · intro u _ hur
            simp [hur]
          · intro hr'
            exact absurd (Nat.mem_divisors_self r hr0) hr'
        · rw [if_neg hrs]
          apply Finset.sum_eq_zero
          intro u _
          rcases eq_or_ne u r with hur | hur
          · subst hur; simp [hrs]
          · simp [hur]

/-- **k-dim Möbius–gcd kernel (P3 tensor of `kernel1`).** The coordinate
building block, tensored over `Fin k` by `Finset.prod_univ_sum`. -/
theorem kernelK {k : ℕ} {r s : Fin k → ℕ}
    (hr : ∀ i, Squarefree (r i)) (hs : ∀ i, Squarefree (s i)) :
    (∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
        ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
          ∏ i, ((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ))
      = if r = s then ∏ i, (Nat.totient (r i) : ℝ) else 0 := by
  calc
    (∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
        ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
          ∏ i, ((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ))
        = ∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
            ∏ i, ∑ e_i ∈ (s i).divisors,
              ((μ (d i) : ℤ) : ℝ) * ((μ e_i : ℤ) : ℝ) * (Nat.gcd (d i) e_i : ℝ) := by
        apply Finset.sum_congr rfl; intro d _
        exact (Finset.prod_univ_sum (fun i => (s i).divisors)
          (fun i e_i => ((μ (d i) : ℤ) : ℝ) * ((μ e_i : ℤ) : ℝ) * (Nat.gcd (d i) e_i : ℝ))).symm
    _ = ∏ i, ∑ d_i ∈ (r i).divisors, ∑ e_i ∈ (s i).divisors,
          ((μ d_i : ℤ) : ℝ) * ((μ e_i : ℤ) : ℝ) * (Nat.gcd d_i e_i : ℝ) := by
        exact (Finset.prod_univ_sum (fun i => (r i).divisors)
          (fun i d_i => ∑ e_i ∈ (s i).divisors,
            ((μ d_i : ℤ) : ℝ) * ((μ e_i : ℤ) : ℝ) * (Nat.gcd d_i e_i : ℝ))).symm
    _ = ∏ i, (if r i = s i then (Nat.totient (r i) : ℝ) else 0) := by
        apply Finset.prod_congr rfl; intro i _
        exact kernel1 (hr i) (hs i)
    _ = if r = s then ∏ i, (Nat.totient (r i) : ℝ) else 0 := by
        by_cases hrs : r = s
        · rw [if_pos hrs]
          apply Finset.prod_congr rfl; intro i _
          rw [if_pos (congrFun hrs i)]
        · rw [if_neg hrs]
          obtain ⟨i, hi⟩ := Function.ne_iff.mp hrs
          exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-! ## Support/reindexing: `𝒟`-sums restrict to divisor-tuple sums -/

/-- **The support invariant.** Summing a guarded quantity `[∀ i, dᵢ ∣ rᵢ]·F d`
over the sieve index set `𝒟` is the same as summing `F` over the tuple of
divisor sets `∏ᵢ (rᵢ).divisors`: every such `d` lies in `𝒟` precisely because
`r ∈ 𝒟` (each `dᵢ ∣ rᵢ` inherits squarefreeness, pairwise coprimality,
coprimality to `W`, and `∏ dᵢ ∣ ∏ rᵢ < R`). -/
theorem sum_ksieve_guarded_eq {k R W : ℕ} {r : Fin k → ℕ}
    (hr : r ∈ kSieveIndex k R W) (F : (Fin k → ℕ) → ℝ) :
    (∑ d ∈ kSieveIndex k R W, if ∀ i, d i ∣ r i then F d else 0)
      = ∑ d ∈ Fintype.piFinset (fun i => (r i).divisors), F d := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  obtain ⟨hrsq, hrcop, hrcopW, hrprod⟩ := (mem_kSieveIndex_iff r).mp hr
  ext d
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors]
  constructor
  · rintro ⟨-, hdvd⟩ i
    exact ⟨hdvd i, (kSieveIndex_coord_pos hr i).ne'⟩
  · intro h
    refine ⟨?_, fun i => (h i).1⟩
    rw [mem_kSieveIndex_iff]
    refine ⟨fun i => (hrsq i).squarefree_of_dvd (h i).1, ?_, ?_, ?_⟩
    · intro i j hij
      exact ((hrcop i j hij).coprime_dvd_left (h i).1).coprime_dvd_right (h j).1
    · intro i
      exact (hrcopW i).coprime_dvd_left (h i).1
    · have hdvd : (∏ i, d i) ∣ ∏ i, r i :=
        Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => (h i).1)
      have hpos : 0 < ∏ i, r i := Finset.prod_pos (fun i _ => kSieveIndex_coord_pos hr i)
      exact lt_of_le_of_lt (Nat.le_of_dvd hpos hdvd) hrprod

/-! ## The weights `λ` (N2.2) and the diagonalisation (N2.4) -/

/-- The "divisor-shifted" inner sum over the sieve support. -/
noncomputable def wSum (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) (u : Fin k → ℕ) : ℝ :=
  ∑ r ∈ kSieveIndex k R W,
    (if ∀ i, u i ∣ r i then y r / ∏ i, (Nat.totient (r i) : ℝ) else 0)

/-- **N2.2.** The Maynard weights `λ` obtained from `y` by the inverse change
of variables. -/
noncomputable def lam (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) (d : Fin k → ℕ) : ℝ :=
  (∏ i, ((μ (d i) : ℤ) : ℝ) * (d i : ℝ)) * wSum k R W y d

/-- **N2.4 — the k-dimensional S₁ diagonalisation.** With `λ` chosen from `y`
by `lam`, the Selberg quadratic form over `𝒟 × 𝒟` diagonalises to
`∑_r y(r)² / ∏ᵢ φ(rᵢ)`. -/
theorem s1_diagonalisation (k R W : ℕ) (y : (Fin k → ℕ) → ℝ)
    (_hy : ∀ r, r ∉ kSieveIndex k R W → y r = 0) :
    ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        lam k R W y d * lam k R W y e / ∏ i, (Nat.lcm (d i) (e i) : ℝ)
      = ∑ r ∈ kSieveIndex k R W, (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
  -- Positivity of the totient products on the support.
  have hΦpos : ∀ {v : Fin k → ℕ}, v ∈ kSieveIndex k R W →
      (0 : ℝ) < ∏ i, (Nat.totient (v i) : ℝ) := by
    intro v hv
    apply Finset.prod_pos; intro i _
    exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos hv i)
  -- (P1) Per-`(d,e)` summand: split `lam`, turn `1/lcm` into `gcd`.
  have stepA : ∀ d ∈ kSieveIndex k R W, ∀ e ∈ kSieveIndex k R W,
      lam k R W y d * lam k R W y e / ∏ i, (Nat.lcm (d i) (e i) : ℝ)
        = wSum k R W y d * wSum k R W y e *
            ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ)) := by
    intro d hd e he
    have hlcmprod : (∏ i, (Nat.lcm (d i) (e i) : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro i _
      have hpos : 0 < Nat.lcm (d i) (e i) :=
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero (kSieveIndex_coord_pos hd i).ne'
          (kSieveIndex_coord_pos he i).ne')
      exact_mod_cast hpos.ne'
    have hcoord : (∏ i, ((μ (d i) : ℤ) : ℝ) * (d i : ℝ))
          * (∏ i, ((μ (e i) : ℤ) : ℝ) * (e i : ℝ))
        = (∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ)))
          * (∏ i, (Nat.lcm (d i) (e i) : ℝ)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      have hgl : (Nat.gcd (d i) (e i) : ℝ) * (Nat.lcm (d i) (e i) : ℝ)
          = (d i : ℝ) * (e i : ℝ) := by
        rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.gcd_mul_lcm]
      calc ((μ (d i) : ℤ) : ℝ) * (d i : ℝ) * (((μ (e i) : ℤ) : ℝ) * (e i : ℝ))
          = ((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * ((d i : ℝ) * (e i : ℝ)) := by ring
        _ = ((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
              * ((Nat.gcd (d i) (e i) : ℝ) * (Nat.lcm (d i) (e i) : ℝ)) := by rw [hgl]
        _ = ((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ)
              * (Nat.lcm (d i) (e i) : ℝ) := by ring
    rw [lam, lam, div_eq_iff hlcmprod]
    rw [show (∏ i, ((μ (d i) : ℤ) : ℝ) * (d i : ℝ)) * wSum k R W y d
            * ((∏ i, ((μ (e i) : ℤ) : ℝ) * (e i : ℝ)) * wSum k R W y e)
          = wSum k R W y d * wSum k R W y e
            * ((∏ i, ((μ (d i) : ℤ) : ℝ) * (d i : ℝ))
               * (∏ i, ((μ (e i) : ℤ) : ℝ) * (e i : ℝ))) from by ring]
    rw [hcoord]; ring
  have hL : (∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        lam k R W y d * lam k R W y e / ∏ i, (Nat.lcm (d i) (e i) : ℝ))
      = ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
          wSum k R W y d * wSum k R W y e *
            ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ)) := by
    apply Finset.sum_congr rfl; intro d hd
    apply Finset.sum_congr rfl; intro e he
    exact stepA d hd e he
  -- (P4) Expand `wSum`, factor into a quadruple sum.
  have hExpand : (∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        wSum k R W y d * wSum k R W y e *
          ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ)))
      = ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
          ∑ r ∈ kSieveIndex k R W, ∑ s ∈ kSieveIndex k R W,
            (if ∀ i, d i ∣ r i then y r / ∏ i, (Nat.totient (r i) : ℝ) else 0)
            * (if ∀ i, e i ∣ s i then y s / ∏ i, (Nat.totient (s i) : ℝ) else 0)
            * ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ)) := by
    apply Finset.sum_congr rfl; intro d _; apply Finset.sum_congr rfl; intro e _
    rw [wSum, wSum, Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.sum_mul]
  -- (P5+P6) Collapse the inner `(d,e)` double sum for fixed `(r,s)`.
  have hInner : ∀ r ∈ kSieveIndex k R W, ∀ s ∈ kSieveIndex k R W,
      (∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        (if ∀ i, d i ∣ r i then y r / ∏ i, (Nat.totient (r i) : ℝ) else 0)
        * (if ∀ i, e i ∣ s i then y s / ∏ i, (Nat.totient (s i) : ℝ) else 0)
        * ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ)))
        = (y r / ∏ i, (Nat.totient (r i) : ℝ)) * (y s / ∏ i, (Nat.totient (s i) : ℝ))
            * (if r = s then ∏ i, (Nat.totient (r i) : ℝ) else 0) := by
    intro r hr s hs
    have hrsq : ∀ i, Squarefree (r i) := fun i => ((mem_kSieveIndex_iff r).mp hr).1 i
    have hssq : ∀ i, Squarefree (s i) := fun i => ((mem_kSieveIndex_iff s).mp hs).1 i
    calc
      (∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        (if ∀ i, d i ∣ r i then y r / ∏ i, (Nat.totient (r i) : ℝ) else 0)
        * (if ∀ i, e i ∣ s i then y s / ∏ i, (Nat.totient (s i) : ℝ) else 0)
        * ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ)))
          = ∑ d ∈ kSieveIndex k R W,
              (if ∀ i, d i ∣ r i then y r / ∏ i, (Nat.totient (r i) : ℝ) else 0) *
                ((y s / ∏ i, (Nat.totient (s i) : ℝ)) *
                  ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
                    ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
                      * (Nat.gcd (d i) (e i) : ℝ))) := by
            apply Finset.sum_congr rfl; intro d _
            have hin : (∑ e ∈ kSieveIndex k R W,
                  (if ∀ i, e i ∣ s i then y s / ∏ i, (Nat.totient (s i) : ℝ) else 0)
                  * ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ)))
                = (y s / ∏ i, (Nat.totient (s i) : ℝ)) *
                    ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
                      ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
                        * (Nat.gcd (d i) (e i) : ℝ)) := by
              rw [← sum_ksieve_guarded_eq hs (fun e =>
                ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ)))]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro e _
              split_ifs with h <;> ring
            rw [← hin, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro e _
            ring
      _ = (y s / ∏ i, (Nat.totient (s i) : ℝ)) *
            ∑ d ∈ kSieveIndex k R W,
              (if ∀ i, d i ∣ r i then y r / ∏ i, (Nat.totient (r i) : ℝ) else 0) *
                ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
                  ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
                    * (Nat.gcd (d i) (e i) : ℝ)) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring
      _ = (y s / ∏ i, (Nat.totient (s i) : ℝ)) *
            ((y r / ∏ i, (Nat.totient (r i) : ℝ)) *
              ∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
                ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
                  ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
                    * (Nat.gcd (d i) (e i) : ℝ))) := by
            congr 1
            rw [← sum_ksieve_guarded_eq hr (fun d =>
              ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
                ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ)))]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro d _
            split_ifs with h <;> ring
      _ = (y r / ∏ i, (Nat.totient (r i) : ℝ)) * (y s / ∏ i, (Nat.totient (s i) : ℝ))
            * (if r = s then ∏ i, (Nat.totient (r i) : ℝ) else 0) := by
            rw [kernelK hrsq hssq]; ring
  -- Assemble: swap `(d,e)` with `(r,s)`, collapse the delta.
  rw [hL, hExpand, sum_move4]
  have hRS : (∑ r ∈ kSieveIndex k R W, ∑ s ∈ kSieveIndex k R W,
        ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
          (if ∀ i, d i ∣ r i then y r / ∏ i, (Nat.totient (r i) : ℝ) else 0)
          * (if ∀ i, e i ∣ s i then y s / ∏ i, (Nat.totient (s i) : ℝ) else 0)
          * ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ) * (Nat.gcd (d i) (e i) : ℝ)))
      = ∑ r ∈ kSieveIndex k R W, ∑ s ∈ kSieveIndex k R W,
          (y r / ∏ i, (Nat.totient (r i) : ℝ)) * (y s / ∏ i, (Nat.totient (s i) : ℝ))
            * (if r = s then ∏ i, (Nat.totient (r i) : ℝ) else 0) := by
    apply Finset.sum_congr rfl; intro r hr
    apply Finset.sum_congr rfl; intro s hs
    exact hInner r hr s hs
  rw [hRS]
  -- (P7) Collapse `s = r`.
  apply Finset.sum_congr rfl; intro r hr
  have hΦr : (∏ i, (Nat.totient (r i) : ℝ)) ≠ 0 := (hΦpos hr).ne'
  have hcollapse : (∑ s ∈ kSieveIndex k R W,
        (y r / ∏ i, (Nat.totient (r i) : ℝ)) * (y s / ∏ i, (Nat.totient (s i) : ℝ))
          * (if r = s then ∏ i, (Nat.totient (r i) : ℝ) else 0))
      = ∑ s ∈ kSieveIndex k R W, if r = s then
          (y r / ∏ i, (Nat.totient (r i) : ℝ)) * (y s / ∏ i, (Nat.totient (s i) : ℝ))
            * (∏ i, (Nat.totient (r i) : ℝ)) else 0 := by
    apply Finset.sum_congr rfl; intro s _; rw [mul_ite_zero]
  rw [hcollapse, Finset.sum_ite_eq, if_pos hr]
  field_simp

end Salt.Maynard
