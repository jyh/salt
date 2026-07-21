/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.LargeValues

/-!
# MR track, P-lane: large-value counting (Lemma 8, the k-th-power amplification)

Source: MR arXiv v4 `1501.04585v4` Lemma 8 (pp. 16, proof following).  Frozen
shape (S8 MR-CORE freeze v2, P3): for `P(s) = ∑_{P≤p≤2P} a_p p^{-s}` with
`|a_p| ≤ 1` and a well-spaced `𝒯 ⊂ [−T,T]` with `|P(1+it)| ≥ V⁻¹`,
`|𝒯| ≪ T^{2 log V / log P}·V²·exp(2 (log T/log P) loglog T)`, via `P(s)^k` at
`k = ⌈log T / log P⌉` fed into Lemma 7 (`wellspaced_l2`).

The proof's three pieces (P3 resistance map):

* **(a) the product-of-dpolys identity** — `dpoly_mul`: the pointwise product of
  two Dirichlet polynomials is a single Dirichlet polynomial whose coefficients are
  the *restricted Dirichlet convolution* `dconv`.  The antidiagonal reindex
  `n = n₁·n₂` via `Finset.sum_fiberwise_of_maps_to` (corpus precedent:
  `RamareWindows`, `ShiuMoment`).  **This file: `dconv`, `dpoly_mul`.**
* **(b) the k-fold coefficient L²/L¹ control** — the divisor-bound counting
  (`|b(n)| ≤ k!`, support `⊆ [P^k, (2P)^k]`, `Σ|b(n)|² ≤ k!·(#tuples)`).  Heavy
  combinatorial core (unique factorization of the prime multiset).
* **(c) the transcendental packaging** — feed `wellspaced_l2` at `N=(2P)^k`, then
  the `k = ⌈log T/log P⌉` instantiation + log-of-arithmetic to the frozen shape.

Zeno note: (a) is a standalone reusable stone (any large-value amplification needs
the product identity); (b)/(c) are the residual heavy pieces.
-/

namespace Salt.MR

open scoped BigOperators
open Complex Finset

/-- **Restricted Dirichlet convolution.** The coefficient of `n^{-s}` in the product
`(∑_{n≤N} aₙ n^{-s})·(∑_{m≤M} bₘ m^{-s})`: the sum of `a_{n₁}·b_{n₂}` over all
factorizations `n = n₁·n₂` with `n₁ ∈ [1,N]`, `n₂ ∈ [1,M]`. -/
noncomputable def dconv (N M : ℕ) (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ q ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 M).filter (fun q => q.1 * q.2 = n), a q.1 * b q.2

/-- **(a) The product-of-dpolys identity (V1).** The pointwise product of two
Dirichlet polynomials is the Dirichlet polynomial of degree `N·M` with the
restricted-convolution coefficients `dconv`.  This is the antidiagonal reindex
`n = n₁·n₂`; the frequencies add (`log n₁ + log n₂ = log(n₁ n₂)`) so the fibre over
each product collapses cleanly. -/
theorem dpoly_mul (N M : ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    dpoly N a t * dpoly M b t = dpoly (N * M) (dconv N M a b) t := by
  -- Step 1: the product as a single sum over the pair-Finset, frequencies combined.
  have hLHS : dpoly N a t * dpoly M b t
      = ∑ q ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 M,
          a q.1 * b q.2
            * Complex.exp (Complex.I * (t : ℂ) * (Real.log (q.1 * q.2 : ℕ) : ℂ)) := by
    unfold dpoly
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hn, hm⟩ := Finset.mem_product.mp hq
    have h1 : 1 ≤ q.1 := (Finset.mem_Icc.mp hn).1
    have h2 : 1 ≤ q.2 := (Finset.mem_Icc.mp hm).1
    have hne1 : ((q.1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hne2 : ((q.2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hexp :
        Complex.exp (Complex.I * (t : ℂ) * (Real.log (q.1 : ℕ) : ℂ))
            * Complex.exp (Complex.I * (t : ℂ) * (Real.log (q.2 : ℕ) : ℂ))
          = Complex.exp (Complex.I * (t : ℂ) * (Real.log (q.1 * q.2 : ℕ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      have hlog : Real.log ((q.1 * q.2 : ℕ) : ℝ)
          = Real.log (q.1 : ℕ) + Real.log (q.2 : ℕ) := by
        rw [Nat.cast_mul, Real.log_mul hne1 hne2]
      rw [hlog, Complex.ofReal_add]; ring
    rw [show
        (a q.1 * Complex.exp (Complex.I * (t : ℂ) * (Real.log (q.1 : ℕ) : ℂ)))
          * (b q.2 * Complex.exp (Complex.I * (t : ℂ) * (Real.log (q.2 : ℕ) : ℂ)))
        = a q.1 * b q.2
            * (Complex.exp (Complex.I * (t : ℂ) * (Real.log (q.1 : ℕ) : ℂ))
                * Complex.exp (Complex.I * (t : ℂ) * (Real.log (q.2 : ℕ) : ℂ)))
        from by ring, hexp]
  -- Step 2: fibre the pair-Finset over the product map `q ↦ q.1·q.2 ∈ [1, N·M]`.
  have hmaps : ∀ q ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 M,
      q.1 * q.2 ∈ Finset.Icc 1 (N * M) := by
    intro q hq
    obtain ⟨hn, hm⟩ := Finset.mem_product.mp hq
    rw [Finset.mem_Icc] at hn hm ⊢
    exact ⟨by simpa using Nat.mul_le_mul hn.1 hm.1, Nat.mul_le_mul hn.2 hm.2⟩
  rw [hLHS, dpoly, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [dconv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_filter] at hq
  rw [hq.2]

/-- **The k-fold restricted convolution.** The coefficients of `(∑_{n≤N} aₙ n^{-s})^k`
as a Dirichlet polynomial of degree `N^k`; built by iterating `dconv`.  Base case is
the coefficient sequence of the constant polynomial `1` (supported at `n = 1`). -/
noncomputable def kconv (N : ℕ) (a : ℕ → ℂ) : ℕ → (ℕ → ℂ)
  | 0 => fun n => if n = 1 then 1 else 0
  | (k + 1) => dconv N (N ^ k) a (kconv N a k)

/-- **(a, k-fold) The `k`-th power identity (V1′).** `P(s)^k` is a single Dirichlet
polynomial of degree `N^k` with the iterated-convolution coefficients `kconv`.  This
is the exact object Lemma 8 feeds into Lemma 7 (`wellspaced_l2`) at `N = (2P)^k`. -/
theorem dpoly_pow (N : ℕ) (a : ℕ → ℂ) (t : ℝ) (k : ℕ) :
    (dpoly N a t) ^ k = dpoly (N ^ k) (kconv N a k) t := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero, kconv, dpoly, Finset.Icc_self]
      simp
  | succ k ih =>
      rw [pow_succ', ih, dpoly_mul, pow_succ']
      rfl

/-- **(c-bridge) Lemma 7 applied to `P^k` (V3a).** The `2k`-th power moment of a
Dirichlet polynomial over a well-spaced set is Lemma 7 for its `k`-th power: the
`k`-fold convolution coefficients at degree `N^k`.  Fully unconditional — combines
`dpoly_pow` with the landed keystone `wellspaced_l2`. -/
theorem wellspaced_l2_pow (N k : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : 0 ≤ T) (𝒯 : Finset ℝ)
    (hws : WellSpaced 𝒯) (hsub𝒯 : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) :
    ∑ t ∈ 𝒯, ‖dpoly N a t‖ ^ (2 * k)
      ≤ 84 * (T + ((N ^ k : ℕ) : ℝ)) * Real.log (2 * ((N ^ k : ℕ) : ℝ))
          * ∑ n ∈ Finset.Icc 1 (N ^ k), ‖kconv N a k n‖ ^ 2 := by
  have hkey : ∀ t : ℝ, ‖dpoly N a t‖ ^ (2 * k) = ‖dpoly (N ^ k) (kconv N a k) t‖ ^ 2 := by
    intro t; rw [← dpoly_pow, norm_pow, ← pow_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun t _ => hkey t)]
  exact wellspaced_l2 (N ^ k) (kconv N a k) T hT 𝒯 hws hsub𝒯

/-- **(c-bridge) The card lower bound (V3b).** If `|P(1+it)| ≥ V⁻¹` on the whole
well-spaced set, the `2k`-th power moment is at least `|𝒯|·(V⁻¹)^{2k}` — the step
that turns the moment bound into a *counting* bound. -/
theorem card_mul_pow_le (N k : ℕ) (a : ℕ → ℂ) (V : ℝ) (hV : 0 < V) (𝒯 : Finset ℝ)
    (hlb : ∀ t ∈ 𝒯, V⁻¹ ≤ ‖dpoly N a t‖) :
    (𝒯.card : ℝ) * (V⁻¹) ^ (2 * k) ≤ ∑ t ∈ 𝒯, ‖dpoly N a t‖ ^ (2 * k) := by
  have h := Finset.card_nsmul_le_sum 𝒯 (fun t => ‖dpoly N a t‖ ^ (2 * k)) ((V⁻¹) ^ (2 * k))
    (fun t ht => pow_le_pow_left₀ (by positivity) (hlb t ht) (2 * k))
  simpa [nsmul_eq_mul] using h

/-- **The single-amplification inequality (V3).** Feeding the `k`-th power of
`P(s)` into Lemma 7 and using the pointwise lower bound gives the master counting
inequality, *modulo* the coefficient `L²` bound on `kconv` (the residual heavy piece
(b)) and the `k = ⌈log T/log P⌉` instantiation (piece (c)).  This is the frozen
`|𝒯|·V^{−2k} ≤ (Lemma 7 at N=(2P)^k)·(coeff mass)` step, coefficient-agnostic. -/
theorem large_value_count_pre (N k : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : 0 ≤ T) (V : ℝ)
    (hV : 0 < V) (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯)
    (hsub𝒯 : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) (hlb : ∀ t ∈ 𝒯, V⁻¹ ≤ ‖dpoly N a t‖) :
    (𝒯.card : ℝ) * (V⁻¹) ^ (2 * k)
      ≤ 84 * (T + ((N ^ k : ℕ) : ℝ)) * Real.log (2 * ((N ^ k : ℕ) : ℝ))
          * ∑ n ∈ Finset.Icc 1 (N ^ k), ‖kconv N a k n‖ ^ 2 :=
  le_trans (card_mul_pow_le N k a V hV 𝒯 hlb)
    (wellspaced_l2_pow N k a T hT 𝒯 hws hsub𝒯)

/-- **(b, L¹) Submultiplicativity of the convolution mass.** The total `L¹` mass of
`dconv` is at most the product of the masses — the triangle inequality inside each
fibre plus the antidiagonal reindex. -/
lemma dconv_l1_le (N M : ℕ) (a b : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 (N * M), ‖dconv N M a b n‖
      ≤ (∑ m ∈ Finset.Icc 1 N, ‖a m‖) * ∑ m ∈ Finset.Icc 1 M, ‖b m‖ := by
  have hmaps : ∀ q ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 M,
      q.1 * q.2 ∈ Finset.Icc 1 (N * M) := by
    intro q hq
    obtain ⟨hn, hm⟩ := Finset.mem_product.mp hq
    rw [Finset.mem_Icc] at hn hm ⊢
    exact ⟨by simpa using Nat.mul_le_mul hn.1 hm.1, Nat.mul_le_mul hn.2 hm.2⟩
  calc ∑ n ∈ Finset.Icc 1 (N * M), ‖dconv N M a b n‖
      ≤ ∑ n ∈ Finset.Icc 1 (N * M),
          ∑ q ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 M).filter (fun q => q.1 * q.2 = n),
            ‖a q.1‖ * ‖b q.2‖ := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [dconv]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
        rw [norm_mul]
    _ = ∑ q ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 M, ‖a q.1‖ * ‖b q.2‖ :=
        Finset.sum_fiberwise_of_maps_to hmaps _
    _ = (∑ m ∈ Finset.Icc 1 N, ‖a m‖) * ∑ m ∈ Finset.Icc 1 M, ‖b m‖ := by
        rw [Finset.sum_mul_sum, ← Finset.sum_product']

/-- **(b, L¹) The k-fold convolution mass bound (V2a).** `∑ₙ ‖kconv‖ ≤ (∑ₘ ‖aₘ‖)^k`.
Reusable stone: with `|a_p| ≤ 1` on the prime window this is `≤ (π(2P)−π(P))^k`, the
`#tuples` count entering the source's `Σ|b(n)|² ≤ k!·#tuples` chain. -/
lemma kconv_l1_le (N : ℕ) (a : ℕ → ℂ) (k : ℕ) :
    ∑ n ∈ Finset.Icc 1 (N ^ k), ‖kconv N a k n‖ ≤ (∑ m ∈ Finset.Icc 1 N, ‖a m‖) ^ k := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero, Finset.Icc_self]
      simp [kconv]
  | succ k ih =>
      have hdeg : N ^ (k + 1) = N * N ^ k := pow_succ' N k
      rw [kconv, hdeg]
      refine le_trans (dconv_l1_le N (N ^ k) a (kconv N a k)) ?_
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left ih (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- **(b, support floor) The `k`-fold convolution is supported on `[P^k, ∞)`.** If the
base coefficients vanish below `P`, the `k`-fold convolution vanishes below `P^k`.  This
is the source's "`n ≥ P^k`" fact — it turns each `1/n` in the coefficient chain into
`≤ 1/P^k` (the `1/P^k` factor of `Σ|b(n)/n|² ≤ k!(1/P^k)(Σ1/p)^k`). -/
lemma kconv_supp_lower (N P : ℕ) (a : ℕ → ℂ) (ha : ∀ m, a m ≠ 0 → P ≤ m) (k : ℕ) :
    ∀ n, kconv N a k n ≠ 0 → P ^ k ≤ n := by
  induction k with
  | zero =>
      intro n hn
      rw [pow_zero]; rw [kconv] at hn
      by_cases hn1 : n = 1
      · omega
      · simp [hn1] at hn
  | succ k ih =>
      intro n hn
      rw [kconv, dconv] at hn
      obtain ⟨q, hqmem, hqne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
      rw [Finset.mem_filter] at hqmem
      have ha1 : a q.1 ≠ 0 := fun h => hqne (by rw [h, zero_mul])
      have hb2 : kconv N a k q.2 ≠ 0 := fun h => hqne (by rw [h, mul_zero])
      calc P ^ (k + 1) = P * P ^ k := pow_succ' P k
        _ ≤ q.1 * q.2 := Nat.mul_le_mul (ha q.1 ha1) (ih q.2 hb2)
        _ = n := hqmem.2

/-- **(b, ω-count) The distinct-prime-factor bound.** If the base coefficients are
supported on primes, every `n` in the support of the `k`-fold convolution has at most
`k` distinct prime factors.  This is the *unique-factorization* content, entering not
through a flat `k`-tuple reindex but through `Nat.primeFactors_mul` on the nested
antidiagonal: `primeFactors (q₁·q₂) = {q₁} ∪ primeFactors q₂`, so the distinct-prime
count grows by at most one per convolution.  The engine of the `k!` sup bound. -/
lemma kconv_primeFactors_card_le (N : ℕ) (c : ℕ → ℂ)
    (hc : ∀ m, c m ≠ 0 → m.Prime) (k : ℕ) :
    ∀ n, kconv N c k n ≠ 0 → n.primeFactors.card ≤ k := by
  induction k with
  | zero =>
      intro n hn
      rw [kconv] at hn
      by_cases hn1 : n = 1
      · subst hn1; simp
      · simp [hn1] at hn
  | succ k ih =>
      intro n hn
      rw [kconv, dconv] at hn
      obtain ⟨q, hqmem, hqne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
      rw [Finset.mem_filter] at hqmem
      have ha1 : c q.1 ≠ 0 := fun h => hqne (by rw [h, zero_mul])
      have hb2 : kconv N c k q.2 ≠ 0 := fun h => hqne (by rw [h, mul_zero])
      have hp1 : q.1.Prime := hc q.1 ha1
      obtain ⟨hn1, hn2⟩ := Finset.mem_product.mp hqmem.1
      have hq1pos : 1 ≤ q.1 := (Finset.mem_Icc.mp hn1).1
      have hq2pos : 1 ≤ q.2 := (Finset.mem_Icc.mp hn2).1
      have hq1ne : q.1 ≠ 0 := by omega
      have hq2ne : q.2 ≠ 0 := by omega
      have hnfac : n = q.1 * q.2 := hqmem.2.symm
      rw [hnfac, Nat.primeFactors_mul hq1ne hq2ne, hp1.primeFactors]
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_singleton]
      have := ih q.2 hb2
      omega

/-- **(b, L∞) The `k!`-sup bound (V2b) — the residual heavy piece, dissolved.** With a
uniform coefficient bound `‖cₘ‖ ≤ B` and prime support, every coefficient of `P(s)^k`
obeys `‖kconv‖ ≤ k!·Bᵏ`.  The source's `#{ordered k-tuples of primes with product n} ≤
k!`, proved by induction on the nested antidiagonal: the convolution step's fibre injects
(first coordinate) into `n.primeFactors`, whose card is `≤ k+1` by
`kconv_primeFactors_card_le`, giving the recursion `f(k+1) ≤ (k+1)·f(k)`, `f(0) = 1`. -/
lemma kconv_sup_le (N : ℕ) (c : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ m, c m ≠ 0 → m.Prime) (hbound : ∀ m, ‖c m‖ ≤ B) (k : ℕ) :
    ∀ n, ‖kconv N c k n‖ ≤ (Nat.factorial k : ℝ) * B ^ k := by
  induction k with
  | zero =>
      intro n
      rw [kconv]
      by_cases hn1 : n = 1
      · subst hn1; simp
      · simp [hn1]
  | succ k ih =>
      classical
      intro n
      rw [kconv, dconv]
      set F := (Finset.Icc 1 N ×ˢ Finset.Icc 1 (N ^ k)).filter (fun q => q.1 * q.2 = n)
        with hFdef
      -- the "good" pairs: both factors contribute nonzero
      set good : ℕ × ℕ → Prop := fun q => c q.1 ≠ 0 ∧ kconv N c k q.2 ≠ 0 with hgood
      have hp : ∀ q ∈ F, ‖c q.1‖ * ‖kconv N c k q.2‖ ≠ 0 → good q := by
        intro q _ hne
        rw [mul_ne_zero_iff] at hne
        exact ⟨norm_ne_zero_iff.mp hne.1, norm_ne_zero_iff.mp hne.2⟩
      -- card bound: at most k+1 good pairs (distinct primes dividing n)
      have hmaps : Set.MapsTo (fun q : ℕ × ℕ => q.1)
          ↑(F.filter good) ↑n.primeFactors := by
        intro q hq
        rw [Finset.mem_coe, Finset.mem_filter, hFdef, Finset.mem_filter] at hq
        obtain ⟨⟨hmemprod, hprod⟩, hg⟩ := hq
        obtain ⟨hm1, hm2⟩ := Finset.mem_product.mp hmemprod
        have h1 : 1 ≤ q.1 := (Finset.mem_Icc.mp hm1).1
        have h2 : 1 ≤ q.2 := (Finset.mem_Icc.mp hm2).1
        rw [Finset.mem_coe, Nat.mem_primeFactors]
        refine ⟨hc q.1 hg.1, ⟨q.2, hprod.symm⟩, ?_⟩
        rw [← hprod]; exact Nat.mul_ne_zero (by omega) (by omega)
      have hinj : Set.InjOn (fun q : ℕ × ℕ => q.1) ↑(F.filter good) := by
        intro q hq q' hq' heq
        simp only at heq
        rw [Finset.mem_coe, Finset.mem_filter, hFdef, Finset.mem_filter] at hq hq'
        have hprodq : q.1 * q.2 = n := hq.1.2
        have hprodq' : q'.1 * q'.2 = n := hq'.1.2
        obtain ⟨hm1, _⟩ := Finset.mem_product.mp hq.1.1
        have hq1pos : 0 < q.1 := (Finset.mem_Icc.mp hm1).1
        have hcast : q.1 * q.2 = q.1 * q'.2 := by
          rw [hprodq, heq, hprodq']
        have h22 : q.2 = q'.2 := Nat.eq_of_mul_eq_mul_left hq1pos hcast
        exact Prod.ext heq h22
      have hcard : (F.filter good).card ≤ k + 1 := by
        rcases (F.filter good).eq_empty_or_nonempty with he | ⟨q0, hq0⟩
        · simp [he]
        · refine le_trans (Finset.card_le_card_of_injOn _ hmaps hinj) ?_
          rw [Finset.mem_filter, hFdef, Finset.mem_filter] at hq0
          obtain ⟨⟨hmemprod, hprod⟩, hg⟩ := hq0
          obtain ⟨hm1, hm2⟩ := Finset.mem_product.mp hmemprod
          have hq1pos : 1 ≤ q0.1 := (Finset.mem_Icc.mp hm1).1
          have hq2pos : 1 ≤ q0.2 := (Finset.mem_Icc.mp hm2).1
          have hq1ne : q0.1 ≠ 0 := by omega
          have hq2ne : q0.2 ≠ 0 := by omega
          have hnf : n = q0.1 * q0.2 := hprod.symm
          rw [hnf, Nat.primeFactors_mul hq1ne hq2ne, (hc q0.1 hg.1).primeFactors]
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [Finset.card_singleton]
          have := kconv_primeFactors_card_le N c hc k q0.2 hg.2
          omega
      -- assemble: triangle → restrict to good → constant bound → card ≤ k+1
      calc ‖∑ q ∈ F, c q.1 * kconv N c k q.2‖
          ≤ ∑ q ∈ F, ‖c q.1 * kconv N c k q.2‖ := norm_sum_le _ _
        _ = ∑ q ∈ F, ‖c q.1‖ * ‖kconv N c k q.2‖ := by simp_rw [norm_mul]
        _ = ∑ q ∈ F.filter good, ‖c q.1‖ * ‖kconv N c k q.2‖ :=
              (Finset.sum_filter_of_ne hp).symm
        _ ≤ ∑ q ∈ F.filter good, B * ((Nat.factorial k : ℝ) * B ^ k) := by
              refine Finset.sum_le_sum fun q _ => ?_
              exact mul_le_mul (hbound q.1) (ih q.2) (norm_nonneg _) hB
        _ = ((F.filter good).card : ℝ) * (B * ((Nat.factorial k : ℝ) * B ^ k)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((k : ℝ) + 1) * (B * ((Nat.factorial k : ℝ) * B ^ k)) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact_mod_cast hcard
        _ = (Nat.factorial (k + 1) : ℝ) * B ^ (k + 1) := by
              rw [Nat.factorial_succ, pow_succ]; push_cast; ring

/-- **(b, L∞ window) The `k!/Pᵏ` sup bound.** The exact frozen coefficient input: for
`c` supported on primes in the window with `‖c_p‖ ≤ 1/p`, every coefficient of the
`k`-th power is `≤ k!/Pᵏ`.  This is the source's `‖b(n)/n‖ ≤ k!/Pᵏ` with `c_p = a_p/p`
pre-folded (CATCH #A): the uniform bound `‖c_m‖ ≤ 1/P` follows from `1/m ≤ 1/P` on the
window, then `kconv_sup_le` at `B = 1/P` and `k!·(1/P)ᵏ = k!/Pᵏ`. -/
lemma kconv_sup_le_window (N P : ℕ) (c : ℕ → ℂ) (hP : 1 ≤ P)
    (hsupp : ∀ m, c m ≠ 0 → m.Prime ∧ P ≤ m)
    (hcoeff : ∀ m, c m ≠ 0 → ‖c m‖ ≤ (m : ℝ)⁻¹) (k : ℕ) (n : ℕ) :
    ‖kconv N c k n‖ ≤ (Nat.factorial k : ℝ) / (P : ℝ) ^ k := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hbound : ∀ m, ‖c m‖ ≤ (P : ℝ)⁻¹ := by
    intro m
    by_cases hm : c m = 0
    · rw [hm, norm_zero]; positivity
    · refine le_trans (hcoeff m hm) ?_
      have hPm : (P : ℝ) ≤ m := by exact_mod_cast (hsupp m hm).2
      exact inv_anti₀ hPpos hPm
  have h := kconv_sup_le N c ((P : ℝ)⁻¹) (by positivity)
    (fun m hm => (hsupp m hm).1) hbound k n
  rwa [inv_pow, ← div_eq_mul_inv] at h

/-- **(b, L²) The complete coefficient input (V2c).** The `L²` mass of the `k`-fold
convolution — exactly the quantity `wellspaced_l2_pow` feeds on — is bounded by
`(k!/Pᵏ)·(∑ₘ ‖cₘ‖)ᵏ`, the source's `k!·P^{−k}·(∑1/p)ᵏ`.  Pure `L∞·L¹` packaging:
`∑‖x‖² ≤ (supₙ‖x‖)·∑‖x‖`, then the sup from `kconv_sup_le_window` and the `L¹` mass
from the landed `kconv_l1_le`.  This closes piece (b): with `wellspaced_l2_pow` +
`large_value_count_pre`, only the `k = ⌈log T/log P⌉` instantiation (piece (c)) remains. -/
lemma kconv_l2_le_window (N P : ℕ) (c : ℕ → ℂ) (hP : 1 ≤ P)
    (hsupp : ∀ m, c m ≠ 0 → m.Prime ∧ P ≤ m)
    (hcoeff : ∀ m, c m ≠ 0 → ‖c m‖ ≤ (m : ℝ)⁻¹) (k : ℕ) :
    ∑ n ∈ Finset.Icc 1 (N ^ k), ‖kconv N c k n‖ ^ 2
      ≤ (Nat.factorial k : ℝ) / (P : ℝ) ^ k
          * (∑ m ∈ Finset.Icc 1 N, ‖c m‖) ^ k := by
  have hsup : ∀ n, ‖kconv N c k n‖ ≤ (Nat.factorial k : ℝ) / (P : ℝ) ^ k :=
    fun n => kconv_sup_le_window N P c hP hsupp hcoeff k n
  have hsupnn : (0 : ℝ) ≤ (Nat.factorial k : ℝ) / (P : ℝ) ^ k := by positivity
  calc ∑ n ∈ Finset.Icc 1 (N ^ k), ‖kconv N c k n‖ ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 (N ^ k),
          (Nat.factorial k : ℝ) / (P : ℝ) ^ k * ‖kconv N c k n‖ := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hsup n) (norm_nonneg _)
    _ = (Nat.factorial k : ℝ) / (P : ℝ) ^ k
          * ∑ n ∈ Finset.Icc 1 (N ^ k), ‖kconv N c k n‖ := by rw [Finset.mul_sum]
    _ ≤ (Nat.factorial k : ℝ) / (P : ℝ) ^ k
          * (∑ m ∈ Finset.Icc 1 N, ‖c m‖) ^ k :=
        mul_le_mul_of_nonneg_left (kconv_l1_le N c k) hsupnn

/-- **(c, csum) The window `L¹` coefficient mass is `≤ 2`.** With `‖c_m‖ ≤ 1/m` on a
prime support `≥ P`, the total mass over `[1, 2P]` is at most `(2P)·(1/P) = 2` — the
crude Mertens surrogate (each of the `≤ 2P` terms is `≤ 1/P`).  Feeds the `(∑1/p)^k ≤ 2^k`
leg of the transcendental packaging. -/
lemma csum_window_le (P : ℕ) (c : ℕ → ℂ) (hP : 1 ≤ P)
    (hsupp : ∀ m, c m ≠ 0 → m.Prime ∧ P ≤ m)
    (hcoeff : ∀ m, c m ≠ 0 → ‖c m‖ ≤ (m : ℝ)⁻¹) :
    (∑ m ∈ Finset.Icc 1 (2 * P), ‖c m‖) ≤ 2 := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hPne : (P : ℝ) ≠ 0 := ne_of_gt hPpos
  have hbound : ∀ m, ‖c m‖ ≤ (P : ℝ)⁻¹ := by
    intro m
    by_cases hm : c m = 0
    · rw [hm, norm_zero]; positivity
    · refine le_trans (hcoeff m hm) ?_
      have hPm : (P : ℝ) ≤ m := by exact_mod_cast (hsupp m hm).2
      exact inv_anti₀ hPpos hPm
  calc ∑ m ∈ Finset.Icc 1 (2 * P), ‖c m‖
      ≤ ∑ _m ∈ Finset.Icc 1 (2 * P), (P : ℝ)⁻¹ :=
        Finset.sum_le_sum fun m _ => hbound m
    _ = ((Finset.Icc 1 (2 * P)).card : ℝ) * (P : ℝ)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 := by
        rw [Nat.card_Icc, show 2 * P + 1 - 1 = 2 * P from by omega, Nat.cast_mul,
          mul_assoc, mul_inv_cancel₀ hPne, mul_one]
        norm_num

/-- **(c, algebraic) The combined counting inequality.** Plugging the window coefficient
inputs (`kconv_l2_le_window`, `csum_window_le`) into the amplification inequality
`large_value_count_pre`: for `c` supported on primes in `[P, 2P]` with `‖c_m‖ ≤ 1/m`
(CATCH #A: `c_p = a_p/p` pre-folded), a well-spaced `𝒯 ⊂ [−T,T]` with `V⁻¹ ≤ ‖dpoly (2P) c t‖`,
`|𝒯|·V^{−2k} ≤ 84·(T+(2P)^k)·log(2(2P)^k)·(k!/P^k)·2^k`.  Coefficient-closed; only the
`k = ⌈log T/log P⌉` transcendental packaging remains (`pow_V_le` + the exp leg). -/
theorem large_value_count_combined (P : ℕ) (c : ℕ → ℂ) (T : ℝ) (hT : 0 ≤ T) (V : ℝ)
    (hV : 0 < V) (hP : 1 ≤ P) (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯)
    (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hsupp : ∀ m, c m ≠ 0 → m.Prime ∧ P ≤ m)
    (hcoeff : ∀ m, c m ≠ 0 → ‖c m‖ ≤ (m : ℝ)⁻¹) (k : ℕ)
    (hlb : ∀ t ∈ 𝒯, V⁻¹ ≤ ‖dpoly (2 * P) c t‖) :
    (𝒯.card : ℝ) * (V⁻¹) ^ (2 * k)
      ≤ 84 * (T + (((2 * P) ^ k : ℕ) : ℝ)) * Real.log (2 * (((2 * P) ^ k : ℕ) : ℝ))
          * ((Nat.factorial k : ℝ) / (P : ℝ) ^ k * 2 ^ k) := by
  have hpre := large_value_count_pre (2 * P) k c T hT V hV 𝒯 hws hsub hlb
  refine le_trans hpre ?_
  have hprod_ge : (1 : ℝ) ≤ 2 * (((2 * P) ^ k : ℕ) : ℝ) := by
    have h1 : (1 : ℕ) ≤ (2 * P) ^ k := Nat.one_le_pow _ _ (by omega)
    have h2 : (1 : ℝ) ≤ (((2 * P) ^ k : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hlog_nn : 0 ≤ Real.log (2 * (((2 * P) ^ k : ℕ) : ℝ)) := Real.log_nonneg hprod_ge
  have hpf : 0 ≤ 84 * (T + (((2 * P) ^ k : ℕ) : ℝ))
      * Real.log (2 * (((2 * P) ^ k : ℕ) : ℝ)) := by
    have hTX : 0 ≤ T + (((2 * P) ^ k : ℕ) : ℝ) := add_nonneg hT (by positivity)
    exact mul_nonneg (mul_nonneg (by norm_num) hTX) hlog_nn
  refine mul_le_mul_of_nonneg_left ?_ hpf
  have hl2 := kconv_l2_le_window (2 * P) P c hP hsupp hcoeff k
  refine le_trans hl2 ?_
  have hfac_nn : (0 : ℝ) ≤ (Nat.factorial k : ℝ) / (P : ℝ) ^ k := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hfac_nn
  have hcsum := csum_window_le P c hP hsupp hcoeff
  have hcsum_nn : (0 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 (2 * P), ‖c m‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  exact pow_le_pow_left₀ hcsum_nn hcsum k

/-- **(c, V-power leg) The `V^{2k}` transcendental stone.** For `V ≥ 1` and `k` obeying
the ceiling relation `k ≤ 1 + log T/log P`, the `2k`-th power of `V` is dominated by
`V²·T^{2 log V/log P}` — the leg producing the frozen `T^{2 log V/log P}·V²` factor.  Pure
`exp/log` monotonicity: `V^{2k} = exp(2k·log V)`, `V²·T^{…} = exp(2 log V·(1+κ))`, and
`k ≤ 1+κ` with `log V ≥ 0`.  A standalone reusable stone. -/
lemma pow_V_le (V T P : ℝ) (hV : 1 ≤ V) (hT : 0 < T) (hLP : 0 < Real.log P) (k : ℕ)
    (hk : (k : ℝ) ≤ 1 + Real.log T / Real.log P) :
    V ^ (2 * k) ≤ V ^ 2 * T ^ (2 * Real.log V / Real.log P) := by
  have hVpos : (0 : ℝ) < V := lt_of_lt_of_le one_pos hV
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hV
  have e1 : V ^ (2 * k) = Real.exp (Real.log V * ((2 * k : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast V (2 * k), Real.rpow_def_of_pos hVpos]
  have e2 : V ^ 2 = Real.exp (Real.log V * 2) := by
    rw [← Real.rpow_natCast V 2, Real.rpow_def_of_pos hVpos]; norm_num
  have e3 : T ^ (2 * Real.log V / Real.log P)
      = Real.exp (Real.log T * (2 * Real.log V / Real.log P)) :=
    Real.rpow_def_of_pos hT _
  rw [e1, e2, e3, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
  rw [hcast]
  have hkey : Real.log T * (2 * Real.log V / Real.log P)
      = 2 * Real.log V * (Real.log T / Real.log P) := by
    field_simp
  rw [hkey]
  have hmul : 2 * Real.log V * (k : ℝ)
      ≤ 2 * Real.log V * (1 + Real.log T / Real.log P) :=
    mul_le_mul_of_nonneg_left hk (by positivity)
  nlinarith [hmul]

/-- **(c, exp leg — the transcendental heart) The exponent inequality.** The pure
real-analysis core of the exp packaging: for `k` in the ceiling window `κ ≤ k ≤ κ+1`
(with `κ = log T/log P`, `LL = loglog T`) and the "sufficiently large" thresholds
`κ ≥ 30`, `LL ≥ 5`, `log κ ≤ LL` (all discharged from `T` large, `P ≥ 3`),
`k·(log 4 + log k) + LL ≤ 2κ·LL` — the statement that `4^k·k! ·(log poly)` fits under
`exp(2κ loglog T)`.  Proved via the crude `log x ≤ x−1` atom bounds (log-of-arithmetic
law: `log 4`, `log 2` set-abstracted and bounded by constants) and one `(κ−2)·LL ≥ 5(κ−2)`
product hint. -/
lemma pack_exp_core (κ LL : ℝ) (hκ : 30 ≤ κ) (hLL5 : 5 ≤ LL) (hLLlogk : Real.log κ ≤ LL)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : (k : ℝ) ≤ κ + 1) :
    (k : ℝ) * (Real.log 4 + Real.log (k : ℝ)) + LL ≤ 2 * κ * LL := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hκpos : (0 : ℝ) < κ := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4); linarith
  have hlogk : Real.log (k : ℝ) ≤ Real.log 2 + LL := by
    have h1 : (k : ℝ) ≤ 2 * κ := by nlinarith
    have h2 : Real.log (k : ℝ) ≤ Real.log (2 * κ) := Real.log_le_log hkpos h1
    have h3 : Real.log (2 * κ) = Real.log 2 + Real.log κ :=
      Real.log_mul (by norm_num) (ne_of_gt hκpos)
    rw [h3] at h2
    linarith [hLLlogk]
  have hfac : Real.log 4 + Real.log (k : ℝ) ≤ 4 + LL := by linarith
  have hfac_nn : (0:ℝ) ≤ 4 + LL := by linarith
  have step1 : (k : ℝ) * (Real.log 4 + Real.log (k : ℝ)) ≤ (κ + 1) * (4 + LL) :=
    le_trans (mul_le_mul_of_nonneg_left hfac (le_of_lt hkpos))
      (mul_le_mul_of_nonneg_right hk2 hfac_nn)
  have hprod : (κ - 2) * 5 ≤ (κ - 2) * LL :=
    mul_le_mul_of_nonneg_left hLL5 (by linarith)
  nlinarith [step1, hprod, hκ, hLL5]

/-- **(c, exp leg — the packaging) `B ≤ 840·exp(2κ loglog T)`.** Wires the concrete
coefficient block onto `pack_exp_core`: the `T+(2P)^k ≤ 2(2P)^k` domination (`T ≤ (2P)^k`
at `k = ⌈κ⌉`), `(2P)^k = 2^k·P^k` so the `2^k/P^k` collapses to `4^k = exp(k log 4)`,
`k! ≤ k^k = exp(k log k)`, and the log-factor `log(2(2P)^k) ≤ 5 log T = 5·exp(loglog T)`.
The three exp factors multiply to `exp(k(log4+log k)+loglog T)`, capped by `pack_exp_core`
at `exp(2κ loglog T)`; the constant is `84·2·5 = 840`.  Thresholds: `T` large enough that
`loglog T ≥ 5`, `log T/log P ≥ 30`, and `3 ≤ P ≤ T` with `log P ≥ 1`. -/
lemma pack_exp_le (P : ℕ) (T : ℝ) (hP3 : 3 ≤ P) (hT : 1 < T)
    (hlogP1 : 1 ≤ Real.log P) (hPT : (P : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log P) (hLL5 : 5 ≤ Real.log (Real.log T)) (k : ℕ)
    (hk1 : 1 ≤ k) (hkub : (k : ℝ) ≤ Real.log T / Real.log P + 1)
    (hTk : T ≤ (((2 * P) ^ k : ℕ) : ℝ)) :
    84 * (T + (((2 * P) ^ k : ℕ) : ℝ)) * Real.log (2 * (((2 * P) ^ k : ℕ) : ℝ))
        * ((Nat.factorial k : ℝ) / (P : ℝ) ^ k * 2 ^ k)
      ≤ 840 * Real.exp (2 * (Real.log T / Real.log P) * Real.log (Real.log T)) := by
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogT0 : 0 < Real.log T := Real.log_pos hT
  have hPpos : (0 : ℝ) < P := by
    have : (3 : ℝ) ≤ P := by exact_mod_cast hP3
    linarith
  have hlogPpos : 0 < Real.log P := by linarith
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hPkpos : (0 : ℝ) < (P : ℝ) ^ k := by positivity
  set κ := Real.log T / Real.log P with hκdef
  set LL := Real.log (Real.log T) with hLLdef
  have hκpos : 0 < κ := by rw [hκdef]; positivity
  have hκlogP : κ * Real.log P = Real.log T := by rw [hκdef]; field_simp
  have hκlogT : κ ≤ Real.log T := by
    nlinarith [hκlogP, mul_nonneg (le_of_lt hκpos) (by linarith : (0:ℝ) ≤ Real.log P - 1)]
  have hLLlogk : Real.log κ ≤ LL := by rw [hLLdef]; exact Real.log_le_log hκpos hκlogT
  have hexpLL : Real.exp LL = Real.log T := by rw [hLLdef, Real.exp_log hlogT0]
  set L := Real.log (2 * (((2 * P) ^ k : ℕ) : ℝ)) with hLdef
  set fac := (Nat.factorial k : ℝ) with hfacdef
  -- exp representations
  have h4exp : (4 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 4) := by
    rw [← Real.exp_log (show (0:ℝ) < (4:ℝ)^k by positivity), Real.log_pow]
  have hfacexp : fac ≤ Real.exp ((k : ℝ) * Real.log (k : ℝ)) := by
    have h1 : fac ≤ (k : ℝ) ^ k := by rw [hfacdef]; exact_mod_cast Nat.factorial_le_pow k
    have h2 : (k : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log (k : ℝ)) := by
      rw [← Real.exp_log (show (0:ℝ) < (k:ℝ)^k by positivity), Real.log_pow]
    rw [h2] at h1; exact h1
  -- log-factor bound: L ≤ 5 log T
  have hlogTge6 : 6 ≤ Real.log T := by
    have h1 : Real.exp 5 ≤ Real.exp LL := Real.exp_le_exp.mpr hLL5
    have h2 : (6 : ℝ) ≤ Real.exp 5 := by
      have := Real.add_one_le_exp (5 : ℝ); linarith
    rw [hexpLL] at h1; linarith
  have hlogfac : L ≤ 5 * Real.log T := by
    have hcast : (((2 * P) ^ k : ℕ) : ℝ) = (2 * (P : ℝ)) ^ k := by push_cast; ring
    rw [hLdef, hcast, Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      Real.log_mul (by norm_num) (ne_of_gt hPpos)]
    have hlog2le1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    have hlog2leP : Real.log 2 ≤ Real.log P :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : (2:ℕ) ≤ P))
    have hlogPleT : Real.log P ≤ Real.log T := Real.log_le_log hPpos hPT
    have hklogP : (k : ℝ) * Real.log P ≤ 2 * Real.log T := by
      have h1 : (k : ℝ) * Real.log P ≤ (κ + 1) * Real.log P :=
        mul_le_mul_of_nonneg_right hkub (le_of_lt hlogPpos)
      nlinarith [h1, hκlogP, hlogPleT]
    nlinarith [hlog2le1, hlog2leP, hlogPleT, hklogP, hlogTge6,
      mul_nonneg (le_of_lt hkpos) (by linarith : (0:ℝ) ≤ Real.log P - Real.log 2)]
  -- domination + collapse: Y := (T+(2P)^k)·2^k/P^k ≤ 2·4^k
  have hdom : T + (((2 * P) ^ k : ℕ) : ℝ) ≤ 2 * (((2 * P) ^ k : ℕ) : ℝ) := by linarith [hTk]
  have hXval : (((2 * P) ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k * (P : ℝ) ^ k := by
    push_cast; rw [mul_pow]
  have hYle : (T + (((2 * P) ^ k : ℕ) : ℝ)) * (2 : ℝ) ^ k / (P : ℝ) ^ k ≤ 2 * (4 : ℝ) ^ k := by
    rw [div_le_iff₀ hPkpos]
    have h2k4k : (2 : ℝ) ^ k * (2 : ℝ) ^ k = (4 : ℝ) ^ k := by rw [← mul_pow]; norm_num
    calc (T + (((2 * P) ^ k : ℕ) : ℝ)) * (2 : ℝ) ^ k
        ≤ (2 * (((2 * P) ^ k : ℕ) : ℝ)) * (2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right hdom (by positivity)
      _ = 2 * ((2 : ℝ) ^ k * (P : ℝ) ^ k) * (2 : ℝ) ^ k := by rw [hXval]
      _ = 2 * (4 : ℝ) ^ k * (P : ℝ) ^ k := by rw [← h2k4k]; ring
  -- assemble the multiplicative chain
  have hLnn : 0 ≤ L := by
    rw [hLdef]; apply Real.log_nonneg
    have : (1 : ℕ) ≤ (2 * P) ^ k := Nat.one_le_pow _ _ (by omega)
    have h2 : (1 : ℝ) ≤ (((2 * P) ^ k : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have h84Lfac_nn : 0 ≤ 84 * L * fac := by
    have hfacnn : 0 ≤ fac := by rw [hfacdef]; positivity
    positivity
  have hLHSeq : 84 * (T + (((2 * P) ^ k : ℕ) : ℝ)) * L * (fac / (P : ℝ) ^ k * (2 : ℝ) ^ k)
      = 84 * L * fac * ((T + (((2 * P) ^ k : ℕ) : ℝ)) * (2 : ℝ) ^ k / (P : ℝ) ^ k) := by
    ring
  rw [hLHSeq]
  refine le_trans (mul_le_mul_of_nonneg_left hYle h84Lfac_nn) ?_
  have hcore := pack_exp_core κ LL hκ30 hLL5 hLLlogk k hk1 hkub
  calc 84 * L * fac * (2 * (4 : ℝ) ^ k)
      = 168 * (L * (fac * (4 : ℝ) ^ k)) := by ring
    _ ≤ 168 * ((5 * Real.log T)
          * (Real.exp ((k : ℝ) * Real.log (k : ℝ)) * Real.exp ((k : ℝ) * Real.log 4))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        refine mul_le_mul hlogfac ?_ (by positivity) (by positivity)
        exact mul_le_mul hfacexp (le_of_eq h4exp) (by positivity) (by positivity)
    _ = 840 * (Real.exp LL
          * (Real.exp ((k : ℝ) * Real.log (k : ℝ)) * Real.exp ((k : ℝ) * Real.log 4))) := by
        rw [← hexpLL]; ring
    _ = 840 * Real.exp ((k : ℝ) * (Real.log 4 + Real.log (k : ℝ)) + LL) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
    _ ≤ 840 * Real.exp (2 * κ * LL) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.exp_le_exp.mpr hcore

/-- **(c) Lemma 8 — the `k`-th-power amplification, packaged (frozen shape).** For a
Dirichlet polynomial `dpoly (2P) c` with prime-window coefficients `‖c_m‖ ≤ 1/m` on
`[P, 2P]` (CATCH #A: `c_p = a_p/p` pre-folded) and a well-spaced `𝒯 ⊂ [−T,T]` on which
`V⁻¹ ≤ ‖dpoly (2P) c t‖`,
`|𝒯| ≤ 840·T^{2 log V/log P}·V²·exp(2·(log T/log P)·loglog T)`,
via `P(s)^k` at `k = ⌈log T/log P⌉` fed into Lemma 7.  Assembled from
`large_value_count_combined` (algebraic spine), `pow_V_le` (the `V^{2k}` leg), and
`pack_exp_le` (the exp leg).  CATCH #B (sign convention `dpoly = P(1−it)`): a caller with
`|P(1+it)| ≥ V⁻¹` supplies `hlb` at the negated ordinate set `−𝒯` (well-spaced and in
`[−T,T]` iff `𝒯` is), leaving `|𝒯|` unchanged.  Thresholds (`T` sufficiently large, `P`
in range): `3 ≤ P ≤ T`, `1 < T`, `log T/log P ≥ 30`, `loglog T ≥ 5`, `1 ≤ V`. -/
theorem large_value_count (P : ℕ) (c : ℕ → ℂ) (T V : ℝ) (hP3 : 3 ≤ P) (hT : 1 < T)
    (hPT : (P : ℝ) ≤ T) (hV : 1 ≤ V) (hκ30 : 30 ≤ Real.log T / Real.log P)
    (hLL5 : 5 ≤ Real.log (Real.log T)) (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯)
    (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hsupp : ∀ m, c m ≠ 0 → m.Prime ∧ P ≤ m)
    (hcoeff : ∀ m, c m ≠ 0 → ‖c m‖ ≤ (m : ℝ)⁻¹)
    (hlb : ∀ t ∈ 𝒯, V⁻¹ ≤ ‖dpoly (2 * P) c t‖) :
    (𝒯.card : ℝ)
      ≤ 840 * T ^ (2 * Real.log V / Real.log P) * V ^ 2
          * Real.exp (2 * (Real.log T / Real.log P) * Real.log (Real.log T)) := by
  have hTpos : (0 : ℝ) < T := by linarith
  have hTnn : (0 : ℝ) ≤ T := le_of_lt hTpos
  have hlogT0 : 0 < Real.log T := Real.log_pos hT
  have hVpos : (0 : ℝ) < V := by linarith
  have hP1 : 1 ≤ P := by omega
  have hPpos : (0 : ℝ) < P := by
    have : (3 : ℝ) ≤ P := by exact_mod_cast hP3
    linarith
  have hlogP1 : 1 ≤ Real.log P := by
    have h1 : Real.exp 1 < (P : ℝ) := by
      have h2 := Real.exp_one_lt_d9
      have h3 : (3 : ℝ) ≤ P := by exact_mod_cast hP3
      linarith
    have := Real.log_lt_log (Real.exp_pos 1) h1
    rw [Real.log_exp] at this; linarith
  have hlogPpos : 0 < Real.log P := by linarith
  set k := ⌈Real.log T / Real.log P⌉₊ with hkdef
  have hκlek : Real.log T / Real.log P ≤ (k : ℝ) := Nat.le_ceil _
  have hkub : (k : ℝ) ≤ Real.log T / Real.log P + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Real.log T / Real.log P))
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  -- domination premise: T ≤ (2P)^k
  have hTk : T ≤ (((2 * P) ^ k : ℕ) : ℝ) := by
    have hP2kpos : (0 : ℝ) < (((2 * P) ^ k : ℕ) : ℝ) := by
      have h0 : (1 : ℕ) ≤ (2 * P) ^ k := Nat.one_le_pow _ _ (by omega)
      have h1 : (1 : ℝ) ≤ (((2 * P) ^ k : ℕ) : ℝ) := by exact_mod_cast h0
      linarith
    have hκlogP : Real.log T / Real.log P * Real.log P = Real.log T :=
      div_mul_cancel₀ _ (ne_of_gt hlogPpos)
    have hstep : Real.log T ≤ (k : ℝ) * Real.log P := by
      have h := mul_le_mul_of_nonneg_right hκlek (le_of_lt hlogPpos)
      rwa [hκlogP] at h
    have hlogle : Real.log T ≤ Real.log (((2 * P) ^ k : ℕ) : ℝ) := by
      have hcast : (((2 * P) ^ k : ℕ) : ℝ) = ((2 : ℝ) * P) ^ k := by push_cast; ring
      have hle2P : Real.log P ≤ Real.log (2 * (P : ℝ)) := Real.log_le_log hPpos (by linarith)
      have h1 : (k : ℝ) * Real.log P ≤ Real.log (((2 * P) ^ k : ℕ) : ℝ) := by
        rw [hcast, Real.log_pow]
        exact mul_le_mul_of_nonneg_left hle2P (le_of_lt hkpos)
      linarith
    calc T = Real.exp (Real.log T) := (Real.exp_log hTpos).symm
      _ ≤ Real.exp (Real.log (((2 * P) ^ k : ℕ) : ℝ)) := Real.exp_le_exp.mpr hlogle
      _ = (((2 * P) ^ k : ℕ) : ℝ) := Real.exp_log hP2kpos
  -- the three pieces
  have hcomb := large_value_count_combined P c T hTnn V hVpos hP1 𝒯 hws hsub hsupp hcoeff k hlb
  have hpack := pack_exp_le P T hP3 hT hlogP1 hPT hκ30 hLL5 k hk1 hkub hTk
  have hpowV := pow_V_le V T P hV hTpos hlogPpos k (by linarith)
  set B := 84 * (T + (((2 * P) ^ k : ℕ) : ℝ)) * Real.log (2 * (((2 * P) ^ k : ℕ) : ℝ))
      * ((Nat.factorial k : ℝ) / (P : ℝ) ^ k * 2 ^ k) with hBdef
  have hBnn : (0 : ℝ) ≤ B := by
    have hlogge : (1 : ℝ) ≤ 2 * (((2 * P) ^ k : ℕ) : ℝ) := by
      have h0 : (1 : ℕ) ≤ (2 * P) ^ k := Nat.one_le_pow _ _ (by omega)
      have h1 : (1 : ℝ) ≤ (((2 * P) ^ k : ℕ) : ℝ) := by exact_mod_cast h0
      linarith
    have hlognn : 0 ≤ Real.log (2 * (((2 * P) ^ k : ℕ) : ℝ)) := Real.log_nonneg hlogge
    have hTXnn : 0 ≤ T + (((2 * P) ^ k : ℕ) : ℝ) := add_nonneg hTnn (by positivity)
    rw [hBdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hTXnn) hlognn) (by positivity)
  -- invert the V^{-2k}: card ≤ B · V^{2k}
  have hVk : (0 : ℝ) < V ^ (2 * k) := by positivity
  rw [inv_pow, ← div_eq_mul_inv] at hcomb
  have hcard : (𝒯.card : ℝ) ≤ B * V ^ (2 * k) := (div_le_iff₀ hVk).mp hcomb
  have hVTnn : (0 : ℝ) ≤ V ^ 2 * T ^ (2 * Real.log V / Real.log P) := by positivity
  calc (𝒯.card : ℝ)
      ≤ B * V ^ (2 * k) := hcard
    _ ≤ B * (V ^ 2 * T ^ (2 * Real.log V / Real.log P)) :=
        mul_le_mul_of_nonneg_left hpowV hBnn
    _ ≤ (840 * Real.exp (2 * (Real.log T / Real.log P) * Real.log (Real.log T)))
          * (V ^ 2 * T ^ (2 * Real.log V / Real.log P)) :=
        mul_le_mul_of_nonneg_right hpack hVTnn
    _ = 840 * T ^ (2 * Real.log V / Real.log P) * V ^ 2
          * Real.exp (2 * (Real.log T / Real.log P) * Real.log (Real.log T)) := by ring

end Salt.MR
