/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Diagonal
import Salt.Maynard.GFunction

/-!
# The k-dimensional S₂ diagonalisation (blueprint N2.5)

This MIRRORS `Salt.Maynard.Diagonal` (the S₁ diagonalisation, N2.4) with the
denominator changed from `∏ᵢ lcm(dᵢ, eᵢ)` to `∏ᵢ φ(lcm(dᵢ, eᵢ))` and the
diagonal weight from `∏ᵢ φ(rᵢ)` to `∏ᵢ g(rᵢ)`, where `g = gMult` (N2.6).

The coordinate building block is the *g-analog of the `gcd = Σφ` identity*:
for squarefree `n`,
`sum_gMult_eq_totient : ∑_{u ∣ n} g(u) = φ(n)`
(the Möbius relation `φ = 1 ∗ g`, `g(p) = p − 2`), which combines with
`totient_gcd_mul_totient_lcm : φ(gcd d e)·φ(lcm d e) = φ(d)·φ(e)` to give the
per-coordinate collapse `φ(d)φ(e)/φ(lcm(d,e)) = φ(gcd(d,e)) = Σ_{u ∣ gcd} g(u)`.

Everything downstream (`kernelG`, `kernelKG`, `wSumG`, `lamG`,
`s2_diagonalisation`) is the exact structural mirror of the S₁ file with
`φ`→`g` in the diagonal weight and `gcd`→`φ(gcd)` in the coordinate factor.
The S₂ diagonal weight `∏ g(rᵢ)` may vanish (a coordinate `rᵢ` divisible by
`2` gives `g(2) = 0`), so — unlike S₁ — the final collapse is done by an
explicit case split rather than `field_simp`, and the identity
`(y/G)·(y/G)·G = y²/G` is used in the form that also holds at `G = 0`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-! ## Small reindexing helpers (copied from the S₁ file; `private` there) -/

/-- Move the innermost of three nested sums to the front. -/
private theorem sum_move3' {α β γ δ : Type*} [AddCommMonoid δ]
    (A : Finset α) (B : Finset β) (C : Finset γ) (F : α → β → γ → δ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c)
      = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, F a b c := by
  rw [← Finset.sum_product']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  exact Finset.sum_product' A B (fun a b => F a b c)

/-- Move the outer pair of four nested sums (over one common set) to the back. -/
private theorem sum_move4' {α δ : Type*} [AddCommMonoid δ] (A : Finset α)
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

/-! ## The key g-identity: `∑_{u ∣ n} g(u) = φ(n)` on squarefree `n` -/

/-- **The g-analog of `gcd = Σφ` (the arithmetic heart of S₂).** For squarefree
`n`, `∑_{u ∈ n.divisors} gMult u = φ(n)`. Möbius relation `φ = 1 ∗ g` with
`g(p) = p − 2`: over squarefree `n` the divisor sum is `∑_{t ⊆ primeFactors n}
∏_{p ∈ t}(p−2) = ∏_{p ∣ n}(1 + (p−2)) = ∏_{p ∣ n}(p−1) = φ(n)`. -/
theorem sum_gMult_eq_totient {n : ℕ} (hn : Squarefree n) :
    ∑ u ∈ n.divisors, gMult u = Nat.totient n := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hbridge :
      (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
    rw [Nat.factors_eq, List.toFinset_coe, Nat.primeFactors]
  calc ∑ u ∈ n.divisors, gMult u
      = ∑ u ∈ {d ∈ n.divisors | Squarefree d}, gMult u := by
        rw [Nat.divisors_filter_squarefree_of_squarefree hn]
    _ = ∑ i ∈ (UniqueFactorizationMonoid.normalizedFactors n).toFinset.powerset,
          gMult i.val.prod := Nat.sum_divisors_filter_squarefree hn0
    _ = ∑ i ∈ n.primeFactors.powerset, ∏ p ∈ i, (p - 2) := by
        rw [hbridge]
        apply Finset.sum_congr rfl
        intro i hi
        have hip : ∀ p ∈ i, p.Prime := fun p hp =>
          Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hi hp)
        have hprod : (∏ p ∈ i, p) = i.val.prod := by
          rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
        rw [← hprod, gMult, Nat.primeFactors_prod hip]
    _ = ∏ p ∈ n.primeFactors, ((p - 2) + 1) := by
        rw [Finset.prod_add (fun p => p - 2) (fun _ => 1) n.primeFactors]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.prod_const_one, mul_one]
    _ = ∏ p ∈ n.primeFactors, (p - 1) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
        omega
    _ = Nat.totient n := (totient_squarefree hn).symm

/-- The `φ(gcd)·φ(lcm) = φ·φ` product identity on squarefree arguments, over `ℝ`.
Prime-factor product form: `gcd`-primeFactors are the intersection, `lcm`-primeFactors
the union, and `Finset.prod_union_inter` closes it. -/
private theorem primeFactors_lcm {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    (Nat.lcm d e).primeFactors = d.primeFactors ∪ e.primeFactors := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_union, ne_eq]
  constructor
  · rintro ⟨hp, hpl, _⟩
    rcases (hp.prime.dvd_lcm).mp hpl with h | h
    · exact Or.inl ⟨hp, h, hd⟩
    · exact Or.inr ⟨hp, h, he⟩
  · rintro (⟨hp, hpd, _⟩ | ⟨hp, hpe, _⟩)
    · exact ⟨hp, (hp.prime.dvd_lcm).mpr (Or.inl hpd), Nat.lcm_ne_zero hd he⟩
    · exact ⟨hp, (hp.prime.dvd_lcm).mpr (Or.inr hpe), Nat.lcm_ne_zero hd he⟩

/-- `φ(gcd d e)·φ(lcm d e) = φ(d)·φ(e)` over `ℝ`, for squarefree `d, e`. -/
theorem totient_gcd_mul_totient_lcm {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    (Nat.totient (Nat.gcd d e) : ℝ) * (Nat.totient (Nat.lcm d e) : ℝ)
      = (Nat.totient d : ℝ) * (Nat.totient e : ℝ) := by
  have hd0 := hd.ne_zero
  have he0 := he.ne_zero
  have hgcd_sf : Squarefree (Nat.gcd d e) := hd.squarefree_of_dvd (Nat.gcd_dvd_left d e)
  have hlcm_sf : Squarefree (Nat.lcm d e) := by
    apply Nat.squarefree_of_factorization_le_one (Nat.lcm_ne_zero hd0 he0)
    intro p
    rw [Nat.factorization_lcm hd0 he0, Finsupp.sup_apply]
    exact sup_le (hd.natFactorization_le_one p) (he.natFactorization_le_one p)
  rw [totient_squarefree_cast hd, totient_squarefree_cast he,
    totient_squarefree_cast hgcd_sf, totient_squarefree_cast hlcm_sf,
    Nat.primeFactors_gcd hd0 he0, primeFactors_lcm hd0 he0, mul_comm]
  exact Finset.prod_union_inter

/-! ## The g-kernels (mirror `kernel1` / `kernelK`) -/

/-- **1-dim g-kernel (mirror of `kernel1`).** For squarefree `r, s`, the twisted
double divisor sum with coordinate factor `φ(gcd d e)` collapses to a Kronecker
delta times `g(r)`. Proof structure identical to `kernel1`, with `φ(gcd)` (rewritten
via `sum_gMult_eq_totient` as `Σ_{u ∣ gcd} g(u)`) in place of `gcd`, and `g(r)` in
place of `φ(r)`. -/
theorem kernelG {r s : ℕ} (hr : Squarefree r) (hs : Squarefree s) :
    (∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
        ((μ d : ℤ) : ℝ) * ((μ e : ℤ) : ℝ) * (Nat.totient (Nat.gcd d e) : ℝ))
      = if r = s then (gMult r : ℝ) else 0 := by
  have hr0 : r ≠ 0 := hr.ne_zero
  have hs0 : s ≠ 0 := hs.ne_zero
  -- `φ(gcd d e) = ∑_{u ∈ r.divisors} [u ∣ d ∧ u ∣ e] g(u)`.
  have hgcd : ∀ d ∈ r.divisors, ∀ e ∈ s.divisors,
      (Nat.totient (Nat.gcd d e) : ℝ)
        = ∑ u ∈ r.divisors, if u ∣ d ∧ u ∣ e then (gMult u : ℝ) else 0 := by
    intro d hd e _
    have hdr : d ∣ r := Nat.dvd_of_mem_divisors hd
    have hgr : Nat.gcd d e ∣ r := (Nat.gcd_dvd_left d e).trans hdr
    have hgsf : Squarefree (Nat.gcd d e) := hr.squarefree_of_dvd hgr
    have hsum : (∑ u ∈ (Nat.gcd d e).divisors, (gMult u : ℝ))
        = (Nat.totient (Nat.gcd d e) : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast sum_gMult_eq_totient hgsf
    rw [← hsum, Salt.SelbergPort.sum_over_dvd_ite hr0 hgr]
    apply Finset.sum_congr rfl
    intro u _
    simp only [Nat.dvd_gcd_iff]
  have hsub : (∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
          ((μ d : ℤ) : ℝ) * ((μ e : ℤ) : ℝ) * (Nat.totient (Nat.gcd d e) : ℝ))
        = ∑ d ∈ r.divisors, ∑ e ∈ s.divisors, ∑ u ∈ r.divisors,
            if u ∣ d ∧ u ∣ e then
              ((μ d : ℤ) : ℝ) * ((μ e : ℤ) : ℝ) * (gMult u : ℝ) else 0 := by
    apply Finset.sum_congr rfl; intro d hd
    apply Finset.sum_congr rfl; intro e he
    rw [hgcd d hd e he, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _
    rw [mul_ite_zero]
  calc
    (∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
          ((μ d : ℤ) : ℝ) * ((μ e : ℤ) : ℝ) * (Nat.totient (Nat.gcd d e) : ℝ))
        = ∑ u ∈ r.divisors, ∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
            if u ∣ d ∧ u ∣ e then
              ((μ d : ℤ) : ℝ) * ((μ e : ℤ) : ℝ) * (gMult u : ℝ) else 0 := by
        rw [hsub, sum_move3']
    _ = ∑ u ∈ r.divisors,
          (gMult u : ℝ)
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
          (gMult u : ℝ)
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
    _ = if r = s then (gMult r : ℝ) else 0 := by
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
            rw [show (gMult r : ℝ) * ((μ r : ℤ) : ℝ) * ((μ r : ℤ) : ℝ)
                  = (gMult r : ℝ) * (((μ r : ℤ) : ℝ) * ((μ r : ℤ) : ℝ)) from by ring,
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

/-- **k-dim g-kernel (mirror of `kernelK`).** Tensor of `kernelG` over `Fin k`. -/
theorem kernelKG {k : ℕ} {r s : Fin k → ℕ}
    (hr : ∀ i, Squarefree (r i)) (hs : ∀ i, Squarefree (s i)) :
    (∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
        ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
          ∏ i, ((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
            * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))
      = if r = s then ∏ i, (gMult (r i) : ℝ) else 0 := by
  calc
    (∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
        ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
          ∏ i, ((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
            * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))
        = ∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
            ∏ i, ∑ e_i ∈ (s i).divisors,
              ((μ (d i) : ℤ) : ℝ) * ((μ e_i : ℤ) : ℝ)
                * (Nat.totient (Nat.gcd (d i) e_i) : ℝ) := by
        apply Finset.sum_congr rfl; intro d _
        exact (Finset.prod_univ_sum (fun i => (s i).divisors)
          (fun i e_i => ((μ (d i) : ℤ) : ℝ) * ((μ e_i : ℤ) : ℝ)
            * (Nat.totient (Nat.gcd (d i) e_i) : ℝ))).symm
    _ = ∏ i, ∑ d_i ∈ (r i).divisors, ∑ e_i ∈ (s i).divisors,
          ((μ d_i : ℤ) : ℝ) * ((μ e_i : ℤ) : ℝ)
            * (Nat.totient (Nat.gcd d_i e_i) : ℝ) := by
        exact (Finset.prod_univ_sum (fun i => (r i).divisors)
          (fun i d_i => ∑ e_i ∈ (s i).divisors,
            ((μ d_i : ℤ) : ℝ) * ((μ e_i : ℤ) : ℝ)
              * (Nat.totient (Nat.gcd d_i e_i) : ℝ))).symm
    _ = ∏ i, (if r i = s i then (gMult (r i) : ℝ) else 0) := by
        apply Finset.prod_congr rfl; intro i _
        exact kernelG (hr i) (hs i)
    _ = if r = s then ∏ i, (gMult (r i) : ℝ) else 0 := by
        by_cases hrs : r = s
        · rw [if_pos hrs]
          apply Finset.prod_congr rfl; intro i _
          rw [if_pos (congrFun hrs i)]
        · rw [if_neg hrs]
          obtain ⟨i, hi⟩ := Function.ne_iff.mp hrs
          exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-! ## The S₂ weights `λ` and the diagonalisation (mirror of N2.4) -/

/-- The g-weighted "divisor-shifted" inner sum over the sieve support (S₂ analog
of `wSum`, with `g(rᵢ)` in place of `φ(rᵢ)`). -/
noncomputable def wSumG (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) (u : Fin k → ℕ) : ℝ :=
  ∑ r ∈ kSieveIndex k R W,
    (if ∀ i, u i ∣ r i then y r / ∏ i, (gMult (r i) : ℝ) else 0)

/-- The S₂ Maynard weights `λ`, with per-coordinate multiplier `μ(dᵢ)·φ(dᵢ)`
(instead of S₁'s `μ(dᵢ)·dᵢ`), matched to the `φ(lcm)` denominator. -/
noncomputable def lamG (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) (d : Fin k → ℕ) : ℝ :=
  (∏ i, ((μ (d i) : ℤ) : ℝ) * (Nat.totient (d i) : ℝ)) * wSumG k R W y d

/-- **N2.5 — the k-dimensional S₂ diagonalisation.** With `λ` chosen from `y`
by `lamG`, the S₂ quadratic form over `𝒟 × 𝒟` — with denominator
`∏ᵢ φ(lcm(dᵢ,eᵢ))` — diagonalises to `∑_r y(r)² / ∏ᵢ g(rᵢ)`. This is the exact
g-analog of `s1_diagonalisation`. -/
theorem s2_diagonalisation (k R W : ℕ) (y : (Fin k → ℕ) → ℝ)
    (_hy : ∀ r, r ∉ kSieveIndex k R W → y r = 0) :
    ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        lamG k R W y d * lamG k R W y e / ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)
      = ∑ r ∈ kSieveIndex k R W, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ) := by
  -- (P1) Per-`(d,e)` summand: split `lamG`, turn `1/φ(lcm)` into `φ(gcd)`.
  have stepA : ∀ d ∈ kSieveIndex k R W, ∀ e ∈ kSieveIndex k R W,
      lamG k R W y d * lamG k R W y e / ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)
        = wSumG k R W y d * wSumG k R W y e *
            ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
              * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)) := by
    intro d hd e he
    have hdsq : ∀ i, Squarefree (d i) := fun i => ((mem_kSieveIndex_iff d).mp hd).1 i
    have hesq : ∀ i, Squarefree (e i) := fun i => ((mem_kSieveIndex_iff e).mp he).1 i
    have hφlcmprod : (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro i _
      have hpos : 0 < Nat.totient (Nat.lcm (d i) (e i)) := by
        apply Nat.totient_pos.mpr
        exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (kSieveIndex_coord_pos hd i).ne'
          (kSieveIndex_coord_pos he i).ne')
      exact_mod_cast hpos.ne'
    have hcoord : (∏ i, ((μ (d i) : ℤ) : ℝ) * (Nat.totient (d i) : ℝ))
          * (∏ i, ((μ (e i) : ℤ) : ℝ) * (Nat.totient (e i) : ℝ))
        = (∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
              * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)))
          * (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      have hgl : (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)
            * (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)
          = (Nat.totient (d i) : ℝ) * (Nat.totient (e i) : ℝ) :=
        totient_gcd_mul_totient_lcm (hdsq i) (hesq i)
      calc ((μ (d i) : ℤ) : ℝ) * (Nat.totient (d i) : ℝ)
              * (((μ (e i) : ℤ) : ℝ) * (Nat.totient (e i) : ℝ))
          = ((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
              * ((Nat.totient (d i) : ℝ) * (Nat.totient (e i) : ℝ)) := by ring
        _ = ((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
              * ((Nat.totient (Nat.gcd (d i) (e i)) : ℝ)
                  * (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)) := by rw [hgl]
        _ = ((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
              * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)
              * (Nat.totient (Nat.lcm (d i) (e i)) : ℝ) := by ring
    rw [lamG, lamG, div_eq_iff hφlcmprod]
    rw [show (∏ i, ((μ (d i) : ℤ) : ℝ) * (Nat.totient (d i) : ℝ)) * wSumG k R W y d
            * ((∏ i, ((μ (e i) : ℤ) : ℝ) * (Nat.totient (e i) : ℝ)) * wSumG k R W y e)
          = wSumG k R W y d * wSumG k R W y e
            * ((∏ i, ((μ (d i) : ℤ) : ℝ) * (Nat.totient (d i) : ℝ))
               * (∏ i, ((μ (e i) : ℤ) : ℝ) * (Nat.totient (e i) : ℝ))) from by ring]
    rw [hcoord]; ring
  have hL : (∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        lamG k R W y d * lamG k R W y e / ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))
      = ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
          wSumG k R W y d * wSumG k R W y e *
            ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
              * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)) := by
    apply Finset.sum_congr rfl; intro d hd
    apply Finset.sum_congr rfl; intro e he
    exact stepA d hd e he
  -- (P4) Expand `wSumG`, factor into a quadruple sum.
  have hExpand : (∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        wSumG k R W y d * wSumG k R W y e *
          ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
            * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)))
      = ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
          ∑ r ∈ kSieveIndex k R W, ∑ s ∈ kSieveIndex k R W,
            (if ∀ i, d i ∣ r i then y r / ∏ i, (gMult (r i) : ℝ) else 0)
            * (if ∀ i, e i ∣ s i then y s / ∏ i, (gMult (s i) : ℝ) else 0)
            * ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
              * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)) := by
    apply Finset.sum_congr rfl; intro d _; apply Finset.sum_congr rfl; intro e _
    rw [wSumG, wSumG, Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.sum_mul]
  -- (P5+P6) Collapse the inner `(d,e)` double sum for fixed `(r,s)`.
  have hInner : ∀ r ∈ kSieveIndex k R W, ∀ s ∈ kSieveIndex k R W,
      (∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        (if ∀ i, d i ∣ r i then y r / ∏ i, (gMult (r i) : ℝ) else 0)
        * (if ∀ i, e i ∣ s i then y s / ∏ i, (gMult (s i) : ℝ) else 0)
        * ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
          * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)))
        = (y r / ∏ i, (gMult (r i) : ℝ)) * (y s / ∏ i, (gMult (s i) : ℝ))
            * (if r = s then ∏ i, (gMult (r i) : ℝ) else 0) := by
    intro r hr s hs
    have hrsq : ∀ i, Squarefree (r i) := fun i => ((mem_kSieveIndex_iff r).mp hr).1 i
    have hssq : ∀ i, Squarefree (s i) := fun i => ((mem_kSieveIndex_iff s).mp hs).1 i
    calc
      (∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        (if ∀ i, d i ∣ r i then y r / ∏ i, (gMult (r i) : ℝ) else 0)
        * (if ∀ i, e i ∣ s i then y s / ∏ i, (gMult (s i) : ℝ) else 0)
        * ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
          * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)))
          = ∑ d ∈ kSieveIndex k R W,
              (if ∀ i, d i ∣ r i then y r / ∏ i, (gMult (r i) : ℝ) else 0) *
                ((y s / ∏ i, (gMult (s i) : ℝ)) *
                  ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
                    ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
                      * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))) := by
            apply Finset.sum_congr rfl; intro d _
            have hin : (∑ e ∈ kSieveIndex k R W,
                  (if ∀ i, e i ∣ s i then y s / ∏ i, (gMult (s i) : ℝ) else 0)
                  * ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
                    * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)))
                = (y s / ∏ i, (gMult (s i) : ℝ)) *
                    ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
                      ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
                        * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)) := by
              rw [← sum_ksieve_guarded_eq hs (fun e =>
                ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
                  * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)))]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro e _
              split_ifs with h <;> ring
            rw [← hin, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro e _
            ring
      _ = (y s / ∏ i, (gMult (s i) : ℝ)) *
            ∑ d ∈ kSieveIndex k R W,
              (if ∀ i, d i ∣ r i then y r / ∏ i, (gMult (r i) : ℝ) else 0) *
                ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
                  ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
                    * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring
      _ = (y s / ∏ i, (gMult (s i) : ℝ)) *
            ((y r / ∏ i, (gMult (r i) : ℝ)) *
              ∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
                ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
                  ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
                    * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))) := by
            congr 1
            rw [← sum_ksieve_guarded_eq hr (fun d =>
              ∑ e ∈ Fintype.piFinset (fun i => (s i).divisors),
                ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
                  * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)))]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro d _
            split_ifs with h <;> ring
      _ = (y r / ∏ i, (gMult (r i) : ℝ)) * (y s / ∏ i, (gMult (s i) : ℝ))
            * (if r = s then ∏ i, (gMult (r i) : ℝ) else 0) := by
            rw [kernelKG hrsq hssq]; ring
  -- Assemble: swap `(d,e)` with `(r,s)`, collapse the delta.
  rw [hL, hExpand, sum_move4']
  have hRS : (∑ r ∈ kSieveIndex k R W, ∑ s ∈ kSieveIndex k R W,
        ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
          (if ∀ i, d i ∣ r i then y r / ∏ i, (gMult (r i) : ℝ) else 0)
          * (if ∀ i, e i ∣ s i then y s / ∏ i, (gMult (s i) : ℝ) else 0)
          * ∏ i, (((μ (d i) : ℤ) : ℝ) * ((μ (e i) : ℤ) : ℝ)
            * (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)))
      = ∑ r ∈ kSieveIndex k R W, ∑ s ∈ kSieveIndex k R W,
          (y r / ∏ i, (gMult (r i) : ℝ)) * (y s / ∏ i, (gMult (s i) : ℝ))
            * (if r = s then ∏ i, (gMult (r i) : ℝ) else 0) := by
    apply Finset.sum_congr rfl; intro r hr
    apply Finset.sum_congr rfl; intro s hs
    exact hInner r hr s hs
  rw [hRS]
  -- (P7) Collapse `s = r`.
  apply Finset.sum_congr rfl; intro r hr
  have hcollapse : (∑ s ∈ kSieveIndex k R W,
        (y r / ∏ i, (gMult (r i) : ℝ)) * (y s / ∏ i, (gMult (s i) : ℝ))
          * (if r = s then ∏ i, (gMult (r i) : ℝ) else 0))
      = ∑ s ∈ kSieveIndex k R W, if r = s then
          (y r / ∏ i, (gMult (r i) : ℝ)) * (y s / ∏ i, (gMult (s i) : ℝ))
            * (∏ i, (gMult (r i) : ℝ)) else 0 := by
    apply Finset.sum_congr rfl; intro s _; rw [mul_ite_zero]
  rw [hcollapse, Finset.sum_ite_eq, if_pos hr]
  -- `(y/G)·(y/G)·G = y²/G`, valid even when `G = ∏ g(rᵢ) = 0`.
  by_cases hG : (∏ i, (gMult (r i) : ℝ)) = 0
  · rw [hG]; simp
  · field_simp

end Salt.Maynard
