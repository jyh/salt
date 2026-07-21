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

end Salt.MR
