/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HalaszSeam
import Salt.MR.Dist
import Salt.Mertens.Third

/-!
# A2-5 ROUTE III, the core layer — the smooth part `sPart` (stones R1–R4)

The coefficient-level dissection ruled in ⟦AMENDMENT C⟧ of the S8 rescope freeze
(`docs/exploration/s8-freeze-0727.md`).  For a seam datum `𝔉` (typically
`seamCoeff F (fun _ => 1) t₀` at a `1`-bounded multiplicative `F`) the freeze's
factorization

  `𝔉 = sPart ⍟ ellLin (𝔉 restricted to primes)`

is `HalaszLambda.smoothPart_factorization` read at the cutoff `y = 1`: at that
cutoff `restrictAbove 1` is the identity on primes (`restrictAbove_one_prime`),
so the "smoothing" datum is the *whole* prime datum and the residual factor
`sPart := 𝔉 ⍟ ellLinInv 𝔉` is SQUAREFULL-supported.  This file lands the four
core stones:

* **R1** `sPart_apply_prime` (`sPart(p) = 0`, the telescope `𝔉(p) + (−𝔉(p))`),
  `sPart_prime_pow_norm_le` (`‖sPart(p^k)‖ ≤ k+1`), `sPart_isMultiplicative`,
  and `sPart_eq_zero_of_not_squarefull` (the support).  `Squarefull 0` is `True`
  (`HalaszSeam.squarefull_zero`), so the support statement says nothing at `0`;
  `sPart_zero` forces the value there explicitly.
* **R2** `sPart_dirichlet_bound` : `∑_{d ≤ N} ‖sPart d‖·d^{−σ} ≤ cSq` for every
  `σ ∈ [3/4, 1]` with `cSq = 20736` EXPLICIT, and `sPart_tail_bound` : the
  `D^{−1/4}` tail.  Plus the completely-multiplicative corollaries
  (`sPart_cm_square_support`, `sPart_cm_norm_le_one`, `sPart_cm_dirichlet_bound`
  at the constant `3`), which certify the fallback narrowing that the general
  bound makes unnecessary.
* **R3** `conv_partial_sum_dissect` : the hyperbola dissection of a partial sum
  of a Dirichlet convolution against a completely multiplicative weight `w`.
* **R4** `pretDistSq_scale_gap` : `𝔻²(f,g;u) ≥ 𝔻²(f,g;X) − 2(S(X) − S(u))`, plus
  the Mertens gap `mertens_gap_le` and the dilated form
  `pretDistSq_scale_gap_dilate` at `u = X/D`.

The final section instantiates R1/R2 at the seam datum `seamCoeff F 1 t₀` itself
(`seamCoeff_isMultiplicative`, `sPart_seamCoeff_factorization`,
`sPart_seamCoeff_dirichlet_bound`) — the hand-off surface for the station stones.

TRAP (the wave's highest priority): this file works at the COEFFICIENT level.
`BallSup`'s `LSeries (ellLin (seamCoeff (ellLin g) …))` statements are about the
`ellLin` datum, where `sPart = δ`; at a general `F` they are a different object
and are NOT touched here.  The `M`-object is untouched too: it is prime-only
(`pretDistSq_congr_primes`), and R4 only compares two cutoffs of the SAME
`pretDistSq`.
-/

namespace Salt.MR

open scoped BigOperators LSeries.notation
open ArithmeticFunction

/-! ## The `y = 1` convention and the definition of `sPart` -/

/-- **The Route-III smooth part.**  `sPart F := F ⍟ ℓ⁻¹(F)`: the freeze's
`sPart := 𝔉 ⍟ ellLinInv(𝔉|primes)` at the trivial cutoff `y = 1`. -/
noncomputable def sPart (F : ℕ → ℂ) : ℕ → ℂ := F ⍟ ellLinInv F

/-- `restrictAbove 1` is the identity at every prime: the `y = 1` convention. -/
theorem restrictAbove_one_prime (F : ℕ → ℂ) {p : ℕ} (hp : p.Prime) :
    restrictAbove 1 F p = F p := by
  have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  simp only [restrictAbove, if_pos this]

/-- `ellLinInv` only reads its datum at primes. -/
theorem ellLinInv_congr_primes {d d' : ℕ → ℂ} (h : ∀ p : ℕ, p.Prime → d p = d' p) :
    ellLinInv d = ellLinInv d' := by
  funext n
  simp only [ellLinInv]
  split_ifs with hn
  · rfl
  · exact Finset.prod_congr rfl fun p hp => by
      rw [h p (Nat.prime_of_mem_primeFactors hp)]

/-- `ellLin` only reads its datum at primes. -/
theorem ellLin_congr_primes {d d' : ℕ → ℂ} (h : ∀ p : ℕ, p.Prime → d p = d' p) :
    ellLin d = ellLin d' := by
  funext n
  simp only [ellLin]
  split_ifs with hn hsq
  · rfl
  · exact Finset.prod_congr rfl fun p hp => h p (Nat.prime_of_mem_primeFactors hp)
  · rfl

/-- **The `y`-convention verified.**  The freeze's `smoothPart` at the cutoff
`y = 1` IS `sPart`. -/
theorem smoothPart_one_eq_sPart (F : ℕ → ℂ) : smoothPart 1 F F = sPart F := by
  rw [smoothPart, sPart,
    ellLinInv_congr_primes (fun p hp => restrictAbove_one_prime F hp)]

/-- **The factorization backbone at `y = 1`.**  `sPart F ⍟ ellLin F = F`. -/
theorem sPart_factorization {F : ℕ → ℂ} (hF0 : F 0 = 0) : sPart F ⍟ ellLin F = F :=
  conv_ellLinInv_ellLin hF0

/-- The same identity in the freeze's own `smoothPart`/`restrictAbove` spelling. -/
theorem sPart_factorization_smoothPart {F : ℕ → ℂ} (hF0 : F 0 = 0) :
    smoothPart 1 F F ⍟ ellLin (restrictAbove 1 F) = F :=
  smoothPart_factorization F 1 hF0

/-! ## R1 — support, prime-power values and bounds -/

/-- **The banked `Squarefull 0` trap, disarmed.**  `sPart F 0 = 0` explicitly
(the support statement is vacuous at `0` because `Squarefull 0` holds). -/
@[simp] theorem sPart_zero (F : ℕ → ℂ) : sPart F 0 = 0 := by
  simp [sPart]

/-- The pointwise unfolding of `sPart` as a divisor sum. -/
theorem sPart_apply (F : ℕ → ℂ) (n : ℕ) :
    sPart F n = ∑ q ∈ n.divisorsAntidiagonal, F q.1 * ellLinInv F q.2 := by
  rw [sPart, LSeries.convolution_def]

/-- `sPart F 1 = 1` when `F 1 = 1`. -/
@[simp] theorem sPart_one {F : ℕ → ℂ} (hF1 : F 1 = 1) : sPart F 1 = 1 := by
  rw [sPart_apply]
  simp [hF1, ellLinInv_one]

/-- **The Euler-factor telescope.**  `sPart F (p^i) = ∑_{j ≤ i} F(p^j)·(−F(p))^{i−j}`
(the `ellLin_mul_inv` pattern, via `convAF_prime_pow` and `ellLinInv_prime_pow`). -/
theorem sPart_prime_pow (F : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    sPart F (p ^ i) = ∑ j ∈ Finset.range (i + 1), F (p ^ j) * (-(F p)) ^ (i - j) := by
  have hconv : sPart F (p ^ i)
      = ∑ j ∈ Finset.range (i + 1), F (p ^ j) * ellLinInv F (p ^ (i - j)) :=
    convAF_prime_pow F (ellLinInv F) hp i
  rw [hconv]
  exact Finset.sum_congr rfl fun j _ => by rw [ellLinInv_prime_pow F hp]

/-- **R1 — the telescape.**  `sPart F p = 0` at every prime: the two surviving
terms are `F(1)·(−F(p))` and `F(p)·1`. -/
theorem sPart_apply_prime {F : ℕ → ℂ} (hF1 : F 1 = 1) {p : ℕ} (hp : p.Prime) :
    sPart F p = 0 := by
  have h := sPart_prime_pow F hp 1
  rw [pow_one] at h
  rw [h, Finset.sum_range_succ, Finset.sum_range_one]
  simp [hF1]

/-- **R1 — the prime-power bound.**  `‖sPart F (p^k)‖ ≤ k + 1` at every
`1`-bounded `F`. -/
theorem sPart_prime_pow_norm_le {F : ℕ → ℂ} (hFb : ∀ n, ‖F n‖ ≤ 1) {p : ℕ}
    (hp : p.Prime) (k : ℕ) : ‖sPart F (p ^ k)‖ ≤ (k : ℝ) + 1 := by
  rw [sPart_prime_pow F hp k]
  calc ‖∑ j ∈ Finset.range (k + 1), F (p ^ j) * (-(F p)) ^ (k - j)‖
      ≤ ∑ j ∈ Finset.range (k + 1), ‖F (p ^ j) * (-(F p)) ^ (k - j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (k + 1), (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_pow, norm_neg]
        exact mul_le_one₀ (hFb _) (by positivity)
          (pow_le_one₀ (norm_nonneg _) (hFb p))
    _ = (k : ℝ) + 1 := by simp

/-- `sPart` is multiplicative: a Dirichlet convolution of two multiplicatives. -/
theorem sPart_isMultiplicative {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) :
    (toArithmeticFunction (sPart F)).IsMultiplicative := by
  have hEq : toArithmeticFunction (sPart F)
      = toArithmeticFunction F * toArithmeticFunction (ellLinInv F) := by
    rw [sPart, LSeries.convolution]
    exact ArithmeticFunction.toArithmeticFunction_eq_self _
  rw [hEq]
  exact hFm.mul (isMult_ellLinInv F)

/-- **R1 — the squarefull support.**  If `n` is NOT squarefull then `sPart F n = 0`.
(`Squarefull 0` is `True`, so this never fires at `0`; `sPart_zero` covers that.) -/
theorem sPart_eq_zero_of_not_squarefull {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) (hF1 : F 1 = 1) {n : ℕ}
    (hn : ¬ Squarefull n) : sPart F n = 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn squarefull_zero
  obtain ⟨p, hp1⟩ : ∃ p : ℕ, n.factorization p = 1 := by
    by_contra hcon
    exact hn ((squarefull_iff_factorization hn0).mpr fun p hp => hcon ⟨p, hp⟩)
  have hpsupp : p ∈ n.factorization.support := by
    simp only [Finsupp.mem_support_iff, hp1]
    norm_num
  have hAF : toArithmeticFunction (sPart F) n
      = n.factorization.prod fun q k => toArithmeticFunction (sPart F) (q ^ k) :=
    (sPart_isMultiplicative hFm).multiplicative_factorization _ hn0
  have hppr : p.Prime := Nat.prime_of_mem_primeFactors (by
    rwa [Nat.support_factorization] at hpsupp)
  have hzero : toArithmeticFunction (sPart F) (p ^ n.factorization p) = 0 := by
    rw [hp1, pow_one]
    simp only [toAF_apply, if_neg hppr.pos.ne']
    exact sPart_apply_prime hF1 hppr
  have : toArithmeticFunction (sPart F) n = 0 := by
    rw [hAF, Finsupp.prod]
    exact Finset.prod_eq_zero hpsupp hzero
  rwa [toAF_apply, if_neg hn0] at this

/-- Contrapositive form of the support: `sPart` lives on the squarefull numbers. -/
theorem squarefull_of_sPart_ne_zero {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) (hF1 : F 1 = 1) {n : ℕ}
    (hn : sPart F n ≠ 0) : Squarefull n := by
  by_contra h
  exact hn (sPart_eq_zero_of_not_squarefull hFm hF1 h)

/-! ## The hyperbola engine (shared by R2 and R3)

The exact reindexing `⋃_{n ≤ N} {(d,m) : dm = n} = {(d,m) : d,m ≤ N, dm ≤ N}`.
It is the R3 dissection's combinatorial core AND the divisor-sum engine of R2. -/

/-- **The hyperbola reindexing (exact).**  Summing a function of the convolution
antidiagonal over `n ∈ [1, N]` is the same as summing it over the hyperbola
`{(d,m) : 1 ≤ d, m ≤ N, d·m ≤ N}`. -/
theorem sum_Icc_divisorsAntidiagonal {M : Type*} [AddCommMonoid M] (N : ℕ)
    (φ : ℕ × ℕ → M) :
    ∑ n ∈ Finset.Icc 1 N, ∑ q ∈ n.divisorsAntidiagonal, φ q
      = ∑ q ∈ {q ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N | q.1 * q.2 ≤ N}, φ q := by
  have hdisj : (↑(Finset.Icc 1 N) : Set ℕ).PairwiseDisjoint
      (fun n => n.divisorsAntidiagonal) := by
    intro n₁ _ n₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    rw [Nat.mem_divisorsAntidiagonal] at hq1 hq2
    exact hne (hq1.1.symm.trans hq2.1)
  rw [← Finset.sum_biUnion hdisj]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext q
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal,
    Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨n, ⟨hn1, hnN⟩, hq, -⟩
    subst hq
    have h1 : 1 ≤ q.1 := Nat.one_le_iff_ne_zero.mpr fun h => by simp [h] at hn1
    have h2 : 1 ≤ q.2 := Nat.one_le_iff_ne_zero.mpr fun h => by simp [h] at hn1
    exact ⟨⟨⟨h1, le_trans (Nat.le_mul_of_pos_right _ h2) hnN⟩,
      h2, le_trans (Nat.le_mul_of_pos_left _ h1) hnN⟩, hnN⟩
  · rintro ⟨⟨⟨h1, -⟩, h2, -⟩, hle⟩
    exact ⟨q.1 * q.2, ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
      hle⟩, rfl, Nat.mul_ne_zero (by omega) (by omega)⟩

/-- The hyperbola set, cut by the first coordinate: for `1 ≤ d`,
`{m ∈ [1,N] : d·m ≤ N} = [1, ⌊N/d⌋]`. -/
theorem filter_mul_le_eq_Icc_div {N d : ℕ} (hd : 1 ≤ d) :
    {m ∈ Finset.Icc 1 N | d * m ≤ N} = Finset.Icc 1 (N / d) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hm1, -⟩, hdm⟩
    exact ⟨hm1, (Nat.le_div_iff_mul_le hd).mpr (by rwa [Nat.mul_comm] at hdm)⟩
  · rintro ⟨hm1, hm2⟩
    have hdm : m * d ≤ N := (Nat.le_div_iff_mul_le hd).mp hm2
    exact ⟨⟨hm1, le_trans (Nat.le_mul_of_pos_right _ hd) hdm⟩, by rwa [Nat.mul_comm]⟩

/-- The hyperbola sum as an iterated sum over `d ≤ N` and `m ≤ ⌊N/d⌋`. -/
theorem sum_hyperbola_eq_nested {M : Type*} [AddCommMonoid M] (N : ℕ) (φ : ℕ × ℕ → M) :
    ∑ q ∈ {q ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N | q.1 * q.2 ≤ N}, φ q
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), φ (d, m) := by
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  rw [← filter_mul_le_eq_Icc_div hd1, Finset.sum_filter]

/-! ## R3 — the partial-sum dissection -/

/-- **R3 — `conv_partial_sum_dissect`.**  For a COMPLETELY MULTIPLICATIVE weight
`w` (the twist `n ↦ n^{−it₀}e(−t₁ log n)` is one) the partial sum of a Dirichlet
convolution dissects along the hyperbola:

`∑_{n ≤ k} (s ⍟ ℓ)(n)·w(n) = ∑_{d ≤ k} s(d)w(d)·∑_{m ≤ ⌊k/d⌋} ℓ(m)w(m)`.

The inner cutoff is the Nat-division floor `⌊k/d⌋`. -/
theorem conv_partial_sum_dissect {s ℓ w : ℕ → ℂ}
    (hw : ∀ {u v : ℕ}, u ≠ 0 → v ≠ 0 → w (u * v) = w u * w v) (k : ℕ) :
    ∑ n ∈ Finset.Icc 1 k, (s ⍟ ℓ) n * w n
      = ∑ d ∈ Finset.Icc 1 k, s d * w d * ∑ m ∈ Finset.Icc 1 (k / d), ℓ m * w m := by
  have hLHS : ∑ n ∈ Finset.Icc 1 k, (s ⍟ ℓ) n * w n
      = ∑ n ∈ Finset.Icc 1 k, ∑ q ∈ n.divisorsAntidiagonal,
          (s q.1 * w q.1) * (ℓ q.2 * w q.2) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [LSeries.convolution_def, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hq
    have h1 : q.1 ≠ 0 := fun h => hn0 (by rw [← hprod, h, zero_mul])
    have h2 : q.2 ≠ 0 := fun h => hn0 (by rw [← hprod, h, mul_zero])
    rw [← hprod, hw h1 h2]
    ring
  rw [hLHS, sum_Icc_divisorsAntidiagonal, sum_hyperbola_eq_nested]
  exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]

/-- **R3, the `range` form.**  Same identity with the outer sum over
`Finset.range (k+1)` (the `n = 0` term vanishes: `(s ⍟ ℓ) 0 = 0`). -/
theorem conv_partial_sum_dissect_range {s ℓ w : ℕ → ℂ}
    (hw : ∀ {u v : ℕ}, u ≠ 0 → v ≠ 0 → w (u * v) = w u * w v) (k : ℕ) :
    ∑ n ∈ Finset.range (k + 1), (s ⍟ ℓ) n * w n
      = ∑ d ∈ Finset.Icc 1 k, s d * w d * ∑ m ∈ Finset.Icc 1 (k / d), ℓ m * w m := by
  rw [← conv_partial_sum_dissect (s := s) (ℓ := ℓ) hw k]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro n hn
    rw [Finset.mem_Icc] at hn
    exact Finset.mem_range.mpr (by omega)
  · intro n hn hn'
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc] at hn'
    have : n = 0 := by omega
    subst this
    simp

/-! ## R4 — the scale gap of the pretentious distance -/

/-- **R4 — `pretDistSq_scale_gap`.**  Shrinking the cutoff from `X` to `u ≤ X`
costs at most twice the reciprocal mass of the primes in `(u, X]`:

`𝔻²(f,g;X) − 2·(S(X) − S(u)) ≤ 𝔻²(f,g;u)`.

Each prime in the gap contributes `(1 − Re(f·conj g))/p ≤ 2/p` (`1`-boundedness). -/
theorem pretDistSq_scale_gap {f g : ℕ → ℂ} (hf : ∀ p, ‖f p‖ ≤ 1) (hg : ∀ p, ‖g p‖ ≤ 1)
    {u X : ℝ} (huX : u ≤ X) :
    pretDistSq f g X - 2 * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial u)
      ≤ pretDistSq f g u := by
  have hsub : {p ∈ Finset.range (⌊u⌋₊ + 1) | Nat.Prime p}
      ⊆ {p ∈ Finset.range (⌊X⌋₊ + 1) | Nat.Prime p} := by
    refine Finset.filter_subset_filter _ ?_
    intro n hn
    have : ⌊u⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono huX
    rw [Finset.mem_range] at hn ⊢
    omega
  have hdecomp : pretDistSq f g X
      = (∑ p ∈ {p ∈ Finset.range (⌊X⌋₊ + 1) | Nat.Prime p}
            \ {p ∈ Finset.range (⌊u⌋₊ + 1) | Nat.Prime p},
          (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ))
        + pretDistSq f g u := by
    simp only [pretDistSq]
    exact (Finset.sum_sdiff hsub).symm
  have h1mass : (∑ p ∈ {p ∈ Finset.range (⌊X⌋₊ + 1) | Nat.Prime p}
        \ {p ∈ Finset.range (⌊u⌋₊ + 1) | Nat.Prime p}, (1 : ℝ) / (p : ℝ))
      = Salt.Mertens.SPartial X - Salt.Mertens.SPartial u := by
    have hss := Finset.sum_sdiff (f := fun p : ℕ => (1 : ℝ) / (p : ℝ)) hsub
    have hSX : Salt.Mertens.SPartial X
        = ∑ p ∈ {p ∈ Finset.range (⌊X⌋₊ + 1) | Nat.Prime p}, (1 : ℝ) / (p : ℝ) := rfl
    have hSu : Salt.Mertens.SPartial u
        = ∑ p ∈ {p ∈ Finset.range (⌊u⌋₊ + 1) | Nat.Prime p}, (1 : ℝ) / (p : ℝ) := rfl
    rw [hSX, hSu]; linarith [hss]
  have hgap : (∑ p ∈ {p ∈ Finset.range (⌊X⌋₊ + 1) | Nat.Prime p}
        \ {p ∈ Finset.range (⌊u⌋₊ + 1) | Nat.Prime p},
        (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ))
      ≤ 2 * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial u) := by
    calc (∑ p ∈ {p ∈ Finset.range (⌊X⌋₊ + 1) | Nat.Prime p}
            \ {p ∈ Finset.range (⌊u⌋₊ + 1) | Nat.Prime p},
            (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ))
        ≤ ∑ p ∈ {p ∈ Finset.range (⌊X⌋₊ + 1) | Nat.Prime p}
            \ {p ∈ Finset.range (⌊u⌋₊ + 1) | Nat.Prime p}, (2 : ℝ) / (p : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hnorm : ‖f p * (starRingEnd ℂ) (g p)‖ ≤ 1 := by
            rw [norm_mul, Complex.norm_conj]
            nlinarith [hf p, hg p, norm_nonneg (f p), norm_nonneg (g p)]
          have hre : -1 ≤ (f p * (starRingEnd ℂ) (g p)).re := by
            have h := (abs_le.mp (Complex.abs_re_le_norm (f p * (starRingEnd ℂ) (g p)))).1
            linarith
          have hppos : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
          gcongr
          linarith
      _ = 2 * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial u) := by
          rw [← h1mass, Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by rw [mul_one_div]
  rw [hdecomp]; linarith

/-- **R4 — the Mertens gap.**  For `2 ≤ u ≤ X`,
`S(X) − S(u) ≤ (log X − log u)/log u + 24/log u`.  Sharp Mertens-2 at both scales
(the Meissel constant cancels) plus `log t ≤ t − 1` at `t = log X/log u`. -/
theorem mertens_gap_le {u X : ℝ} (hu : 2 ≤ u) (huX : u ≤ X) :
    Salt.Mertens.SPartial X - Salt.Mertens.SPartial u
      ≤ (Real.log X - Real.log u) / Real.log u + 24 / Real.log u := by
  have hX2 : (2 : ℝ) ≤ X := le_trans hu huX
  have hlu : (0 : ℝ) < Real.log u := Real.log_pos (by linarith)
  have hlX : (0 : ℝ) < Real.log X := Real.log_pos (by linarith)
  have hlle : Real.log u ≤ Real.log X := Real.log_le_log (by linarith) huX
  have hstep : Real.log (Real.log X) - Real.log (Real.log u)
      ≤ (Real.log X - Real.log u) / Real.log u := by
    have hq : (0 : ℝ) < Real.log X / Real.log u := div_pos hlX hlu
    have h := Real.log_le_sub_one_of_pos hq
    rw [Real.log_div hlX.ne' hlu.ne'] at h
    have heq : Real.log X / Real.log u - 1 = (Real.log X - Real.log u) / Real.log u := by
      field_simp
    linarith [heq ▸ h]
  have h12 : (12 : ℝ) / Real.log X ≤ 12 / Real.log u :=
    div_le_div_of_nonneg_left (by norm_num) hlu hlle
  have hMX := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hX2)
  have hMu := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hu)
  have e24 : (24 : ℝ) / Real.log u = 12 / Real.log u + 12 / Real.log u := by ring
  rw [e24]
  linarith [hMX.1, hMX.2, hMu.1, hMu.2]

/-- **R4 — the dilated scale gap.**  At `u = X/D` with `D ≥ 1` and `X/D ≥ 2`,
the distance loses at most `2·(log D/log(X/D) + 24/log(X/D))`. -/
theorem pretDistSq_scale_gap_dilate {f g : ℕ → ℂ} (hf : ∀ p, ‖f p‖ ≤ 1)
    (hg : ∀ p, ‖g p‖ ≤ 1) {X D : ℝ} (hD : 1 ≤ D) (hu : 2 ≤ X / D) :
    pretDistSq f g X
        - 2 * (Real.log D / Real.log (X / D) + 24 / Real.log (X / D))
      ≤ pretDistSq f g (X / D) := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hXd : X / D * D = X := div_mul_cancel₀ X hD0.ne'
  have hX0 : (0 : ℝ) < X := by nlinarith
  have huX : X / D ≤ X := by
    rw [div_le_iff₀ hD0]; nlinarith
  have hlogsplit : Real.log X - Real.log (X / D) = Real.log D := by
    rw [Real.log_div hX0.ne' hD0.ne']; ring
  have hgap := mertens_gap_le hu huX
  rw [hlogsplit] at hgap
  have hmain := pretDistSq_scale_gap hf hg (u := X / D) (X := X) huX
  linarith

/-! ## R2, part 1 — the divisor majorant and the hyperbola weight engine -/

/-- `‖ℓ⁻¹(F)(n)‖ ≤ 1` at every `1`-bounded `F` (a product of `‖F(p)‖`-powers). -/
theorem norm_ellLinInv_le_one {F : ℕ → ℂ} (hFb : ∀ n, ‖F n‖ ≤ 1) (n : ℕ) :
    ‖ellLinInv F n‖ ≤ 1 := by
  simp only [ellLinInv]
  split_ifs with hn
  · simp
  · rw [norm_prod]
    refine Finset.prod_le_one (fun p _ => norm_nonneg _) (fun p _ => ?_)
    rw [norm_pow, norm_neg]
    exact pow_le_one₀ (norm_nonneg _) (hFb p)

/-- **The divisor majorant.**  `‖sPart F n‖ ≤ τ(n)`: both convolution legs are
`1`-bounded, so the antidiagonal contributes at most `1` per divisor. -/
theorem norm_sPart_le_card_divisors {F : ℕ → ℂ} (hFb : ∀ n, ‖F n‖ ≤ 1) (n : ℕ) :
    ‖sPart F n‖ ≤ (n.divisors.card : ℝ) := by
  rw [sPart_apply]
  calc ‖∑ q ∈ n.divisorsAntidiagonal, F q.1 * ellLinInv F q.2‖
      ≤ ∑ q ∈ n.divisorsAntidiagonal, ‖F q.1 * ellLinInv F q.2‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [norm_mul]
        exact mul_le_one₀ (hFb _) (norm_nonneg _) (norm_ellLinInv_le_one hFb _)
    _ = ((n.divisorsAntidiagonal.card : ℕ) : ℝ) := by simp
    _ = (n.divisors.card : ℝ) := by rw [← Nat.map_div_right_divisors, Finset.card_map]

/-- `τ` is submultiplicative: `τ(mn) ≤ τ(m)·τ(n)` (from `Nat.divisors_mul` and
`Finset.card_mul_le`; no coprimality needed). -/
theorem card_divisors_mul_le_real (m n : ℕ) :
    (((m * n).divisors.card : ℕ) : ℝ) ≤ (m.divisors.card : ℝ) * (n.divisors.card : ℝ) := by
  have h : (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
    rw [Nat.divisors_mul]; exact Finset.card_mul_le
  exact_mod_cast h

/-- **The hyperbola weight engine.**  For a nonnegative submultiplicative `g` and the
completely multiplicative weight `n ↦ n^{−s}`,
`∑_{n ≤ N} g(n)τ(n)n^{−s} ≤ (∑_{u ≤ N} g(u)u^{−s})²`. -/
theorem sum_tau_weight_le {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n)
    (hgm : ∀ u v : ℕ, g (u * v) ≤ g u * g v) (s : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, g n * (n.divisors.card : ℝ) * (n : ℝ) ^ (-s)
      ≤ (∑ u ∈ Finset.Icc 1 N, g u * (u : ℝ) ^ (-s)) ^ 2 := by
  have hterm : ∀ q : ℕ × ℕ, 0 ≤ (g q.1 * (q.1 : ℝ) ^ (-s)) * (g q.2 * (q.2 : ℝ) ^ (-s)) :=
    fun q => mul_nonneg (mul_nonneg (hg0 _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (mul_nonneg (hg0 _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hstep : ∀ n ∈ Finset.Icc 1 N, g n * (n.divisors.card : ℝ) * (n : ℝ) ^ (-s)
      ≤ ∑ q ∈ n.divisorsAntidiagonal,
          (g q.1 * (q.1 : ℝ) ^ (-s)) * (g q.2 * (q.2 : ℝ) ^ (-s)) := by
    intro n _
    have hcard : (n.divisors.card : ℝ) = ((n.divisorsAntidiagonal.card : ℕ) : ℝ) := by
      rw [← Nat.map_div_right_divisors, Finset.card_map]
    have hconst : g n * (n.divisors.card : ℝ) * (n : ℝ) ^ (-s)
        = ∑ _q ∈ n.divisorsAntidiagonal, g n * (n : ℝ) ^ (-s) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
    rw [hconst]
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hq
    have hw : (n : ℝ) ^ (-s) = (q.1 : ℝ) ^ (-s) * (q.2 : ℝ) ^ (-s) := by
      rw [← hprod]
      push_cast
      exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hgle : g n ≤ g q.1 * g q.2 := by rw [← hprod]; exact hgm _ _
    rw [hw]
    calc g n * ((q.1 : ℝ) ^ (-s) * (q.2 : ℝ) ^ (-s))
        ≤ (g q.1 * g q.2) * ((q.1 : ℝ) ^ (-s) * (q.2 : ℝ) ^ (-s)) := by
          refine mul_le_mul_of_nonneg_right hgle ?_
          exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (g q.1 * (q.1 : ℝ) ^ (-s)) * (g q.2 * (q.2 : ℝ) ^ (-s)) := by ring
  calc ∑ n ∈ Finset.Icc 1 N, g n * (n.divisors.card : ℝ) * (n : ℝ) ^ (-s)
      ≤ ∑ n ∈ Finset.Icc 1 N, ∑ q ∈ n.divisorsAntidiagonal,
          (g q.1 * (q.1 : ℝ) ^ (-s)) * (g q.2 * (q.2 : ℝ) ^ (-s)) := Finset.sum_le_sum hstep
    _ = ∑ q ∈ {q ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N | q.1 * q.2 ≤ N},
          (g q.1 * (q.1 : ℝ) ^ (-s)) * (g q.2 * (q.2 : ℝ) ^ (-s)) :=
        sum_Icc_divisorsAntidiagonal _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
          (g q.1 * (q.1 : ℝ) ^ (-s)) * (g q.2 * (q.2 : ℝ) ^ (-s)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun q _ _ => hterm q)
    _ = (∑ u ∈ Finset.Icc 1 N, g u * (u : ℝ) ^ (-s)) ^ 2 := by
        rw [Finset.sum_product, sq, Finset.sum_mul_sum]

/-- `∑_{n ≤ N} τ(n)·n^{−s} ≤ (∑_{u ≤ N} u^{−s})²`. -/
theorem sum_tau_le (s : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * (n : ℝ) ^ (-s)
      ≤ (∑ u ∈ Finset.Icc 1 N, (u : ℝ) ^ (-s)) ^ 2 := by
  have h := sum_tau_weight_le (g := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    (fun _ _ => by norm_num) s N
  simpa using h

/-- `∑_{n ≤ N} τ(n)²·n^{−s} ≤ (∑_{u ≤ N} u^{−s})⁴`. -/
theorem sum_tau_sq_le (s : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-s)
      ≤ (∑ u ∈ Finset.Icc 1 N, (u : ℝ) ^ (-s)) ^ 4 := by
  have hbase : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * (n : ℝ) ^ (-s) :=
    Finset.sum_nonneg fun n _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h := sum_tau_weight_le (g := fun n => (n.divisors.card : ℝ))
    (fun n => Nat.cast_nonneg _) card_divisors_mul_le_real s N
  have h2 : (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * (n : ℝ) ^ (-s)) ^ 2
      ≤ ((∑ u ∈ Finset.Icc 1 N, (u : ℝ) ^ (-s)) ^ 2) ^ 2 :=
    pow_le_pow_left₀ hbase (sum_tau_le s N) 2
  calc ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-s)
      = ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * (n.divisors.card : ℝ)
          * (n : ℝ) ^ (-s) := by
        exact Finset.sum_congr rfl fun n _ => by ring
    _ ≤ (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * (n : ℝ) ^ (-s)) ^ 2 := h
    _ ≤ ((∑ u ∈ Finset.Icc 1 N, (u : ℝ) ^ (-s)) ^ 2) ^ 2 := h2
    _ = (∑ u ∈ Finset.Icc 1 N, (u : ℝ) ^ (-s)) ^ 4 := by ring

/-- `∑_{n ≤ N} τ(n)³·n^{−s} ≤ (∑_{u ≤ N} u^{−s})⁸`. -/
theorem sum_tau_cube_le (s : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 3 * (n : ℝ) ^ (-s)
      ≤ (∑ u ∈ Finset.Icc 1 N, (u : ℝ) ^ (-s)) ^ 8 := by
  have hbase : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-s) :=
    Finset.sum_nonneg fun n _ =>
      mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hsub : ∀ u v : ℕ, ((u * v).divisors.card : ℝ) ^ 2
      ≤ (u.divisors.card : ℝ) ^ 2 * (v.divisors.card : ℝ) ^ 2 := by
    intro u v
    have h := card_divisors_mul_le_real u v
    nlinarith [Nat.cast_nonneg (α := ℝ) ((u * v).divisors.card),
      Nat.cast_nonneg (α := ℝ) u.divisors.card, Nat.cast_nonneg (α := ℝ) v.divisors.card]
  have h := sum_tau_weight_le (g := fun n => (n.divisors.card : ℝ) ^ 2)
    (fun n => by positivity) hsub s N
  have h2 : (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-s)) ^ 2
      ≤ ((∑ u ∈ Finset.Icc 1 N, (u : ℝ) ^ (-s)) ^ 4) ^ 2 :=
    pow_le_pow_left₀ hbase (sum_tau_sq_le s N) 2
  calc ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 3 * (n : ℝ) ^ (-s)
      = ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n.divisors.card : ℝ)
          * (n : ℝ) ^ (-s) := by
        exact Finset.sum_congr rfl fun n _ => by ring
    _ ≤ (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-s)) ^ 2 := h
    _ ≤ ((∑ u ∈ Finset.Icc 1 N, (u : ℝ) ^ (-s)) ^ 4) ^ 2 := h2
    _ = (∑ u ∈ Finset.Icc 1 N, (u : ℝ) ^ (-s)) ^ 8 := by ring

/-! ## R2, part 2 — the two explicit `p`-series partial sums -/

/-- `x^{−3/2} = 1/(√x)³`. -/
theorem rpow_neg_three_halves {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(3 / 2 : ℝ)) = 1 / Real.sqrt x ^ 3 := by
  rw [Real.rpow_neg hx, Real.sqrt_eq_rpow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 2)) 3,
    ← Real.rpow_mul hx]
  norm_num

/-- `x^{−2} = 1/x²`. -/
theorem rpow_neg_two {x : ℝ} (hx : 0 ≤ x) : x ^ (-(2 : ℝ)) = 1 / x ^ 2 := by
  have h2 : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast x 2]; norm_num
  rw [Real.rpow_neg hx, h2, one_div]

/-- The telescoping step at exponent `3/2`: `(x+1)^{−3/2} ≤ 2/√x − 2/√(x+1)`. -/
theorem step_three_halves {x : ℝ} (hx : 1 ≤ x) :
    (x + 1) ^ (-(3 / 2 : ℝ)) ≤ 2 / Real.sqrt x - 2 / Real.sqrt (x + 1) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  set A := Real.sqrt x with hAdef
  set B := Real.sqrt (x + 1) with hBdef
  have hA0 : 0 < A := Real.sqrt_pos.mpr hx0
  have hB0 : 0 < B := Real.sqrt_pos.mpr hx1
  have hA2 : A ^ 2 = x := Real.sq_sqrt hx0.le
  have hB2 : B ^ 2 = x + 1 := Real.sq_sqrt hx1.le
  have hAB : A ≤ B := Real.sqrt_le_sqrt (by linarith)
  have hprod : (B - A) * (B + A) = 1 := by nlinarith [hA2, hB2]
  have hABm : A * B ≤ B ^ 2 := by nlinarith [hAB, hA0, hB0]
  have hmul : (2 * (B - A) * B ^ 2 - A) * (B + A) ≥ 0 := by nlinarith [hprod, hABm, hA2, hB2]
  have hkey : A ≤ 2 * (B - A) * B ^ 2 := by nlinarith [hmul, hA0, hB0]
  have hid : 2 / A - 2 / B - 1 / B ^ 3 = (2 * (B - A) * B ^ 2 - A) / (A * B ^ 3) := by
    field_simp
  have hnn : 0 ≤ 2 / A - 2 / B - 1 / B ^ 3 := by
    rw [hid]
    exact div_nonneg (by linarith) (by positivity)
  rw [rpow_neg_three_halves hx1.le, ← hBdef]
  linarith

/-- The telescoping step at exponent `2`: `(x+1)^{−2} ≤ 1/x − 1/(x+1)`. -/
theorem step_two {x : ℝ} (hx : 1 ≤ x) :
    (x + 1) ^ (-(2 : ℝ)) ≤ 1 / x - 1 / (x + 1) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  rw [rpow_neg_two hx1.le]
  have heq : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by field_simp; ring
  rw [heq]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-- The `Icc`-to-`range` bridge for a summand vanishing at `0`. -/
theorem sum_Icc_eq_sum_range_of_zero {f : ℕ → ℝ} (hf : f 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ n ∈ Finset.range (N + 1), f n := by
  refine Finset.sum_subset ?_ ?_
  · intro n hn
    rw [Finset.mem_Icc] at hn
    exact Finset.mem_range.mpr (by omega)
  · intro n hn hn'
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc] at hn'
    have : n = 0 := by omega
    rw [this, hf]

/-- `∑_{n ≤ M} n^{−3/2} ≤ 3 − 2/√M` for `M ≥ 1` (telescoping). -/
theorem sum_range_three_halves_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ n ∈ Finset.range (M + 1), (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 3 - 2 / Real.sqrt M := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [Finset.sum_range_succ]
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hstep := step_three_halves hM1
    push_cast
    linarith

/-- `∑_{n ≤ M} n^{−2} ≤ 2 − 1/M` for `M ≥ 1` (telescoping). -/
theorem sum_range_two_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ n ∈ Finset.range (M + 1), (n : ℝ) ^ (-(2 : ℝ)) ≤ 2 - 1 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [Finset.sum_range_succ]
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hstep := step_two hM1
    push_cast
    linarith

/-- **The explicit `ζ(3/2)` majorant.**  `∑_{1 ≤ n ≤ N} n^{−3/2} ≤ 3`. -/
theorem sum_Icc_three_halves_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 3 := by
  have hz : ((0 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
  rw [sum_Icc_eq_sum_range_of_zero hz N]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · norm_num
  · have h := sum_range_three_halves_le hN
    have : (0 : ℝ) ≤ 2 / Real.sqrt N := by positivity
    linarith

/-- **The explicit `ζ(2)` majorant.**  `∑_{1 ≤ n ≤ N} n^{−2} ≤ 2`. -/
theorem sum_Icc_two_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 : ℝ)) ≤ 2 := by
  have hz : ((0 : ℕ) : ℝ) ^ (-(2 : ℝ)) = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
  rw [sum_Icc_eq_sum_range_of_zero hz N]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · norm_num
  · have h := sum_range_two_le hN
    have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    linarith

/-! ## R2, part 3 — the `a²b³` parametrization of the squarefull numbers -/

/-- The square part of the `a²b³` representation of a squarefull number. -/
noncomputable def sqPartOf (n : ℕ) : ℕ :=
  n.factorization.prod fun p k => p ^ ((k - 3 * (k % 2)) / 2)

/-- The cube part of the `a²b³` representation of a squarefull number. -/
noncomputable def cubePartOf (n : ℕ) : ℕ :=
  n.factorization.prod fun p k => p ^ (k % 2)

/-- Every member of `n.factorization.support` is prime. -/
theorem prime_of_mem_factorization_support {n p : ℕ} (hp : p ∈ n.factorization.support) :
    p.Prime :=
  Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)

theorem one_le_sqPartOf (n : ℕ) : 1 ≤ sqPartOf n := by
  rw [sqPartOf, Finsupp.prod]
  exact Finset.one_le_prod' fun p hp =>
    Nat.one_le_pow _ _ (prime_of_mem_factorization_support hp).pos

theorem one_le_cubePartOf (n : ℕ) : 1 ≤ cubePartOf n := by
  rw [cubePartOf, Finsupp.prod]
  exact Finset.one_le_prod' fun p hp =>
    Nat.one_le_pow _ _ (prime_of_mem_factorization_support hp).pos

/-- **The `a²b³` representation.**  Every nonzero squarefull `n` is `a²b³` with
`a = sqPartOf n ≥ 1` and `b = cubePartOf n ≥ 1`: an exponent `k ≠ 1` is either
even (`k = 2·(k/2)`) or odd and `≥ 3` (`k = 2·((k−3)/2) + 3`). -/
theorem sqPartOf_sq_mul_cubePartOf_cube {n : ℕ} (hn0 : n ≠ 0) (hsf : Squarefull n) :
    sqPartOf n ^ 2 * cubePartOf n ^ 3 = n := by
  have hstep : ∀ p ∈ n.factorization.support,
      (p ^ ((n.factorization p - 3 * (n.factorization p % 2)) / 2)) ^ 2
          * (p ^ (n.factorization p % 2)) ^ 3
        = p ^ n.factorization p := by
    intro p _
    have hne1 : n.factorization p ≠ 1 := (squarefull_iff_factorization hn0).mp hsf p
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  calc sqPartOf n ^ 2 * cubePartOf n ^ 3
      = ∏ p ∈ n.factorization.support,
          ((p ^ ((n.factorization p - 3 * (n.factorization p % 2)) / 2)) ^ 2
            * (p ^ (n.factorization p % 2)) ^ 3) := by
        rw [sqPartOf, cubePartOf, Finsupp.prod, Finsupp.prod, ← Finset.prod_pow,
          ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    _ = ∏ p ∈ n.factorization.support, p ^ n.factorization p :=
        Finset.prod_congr rfl hstep
    _ = n := by
        have h := Nat.prod_factorization_pow_eq_self hn0
        rw [Finsupp.prod] at h
        exact h

theorem sqPartOf_le {n : ℕ} (hn0 : n ≠ 0) (hsf : Squarefull n) : sqPartOf n ≤ n := by
  have h := sqPartOf_sq_mul_cubePartOf_cube hn0 hsf
  have hb : 0 < cubePartOf n := one_le_cubePartOf n
  calc sqPartOf n ≤ sqPartOf n ^ 2 := Nat.le_self_pow two_ne_zero _
    _ ≤ sqPartOf n ^ 2 * cubePartOf n ^ 3 :=
        Nat.le_mul_of_pos_right _ (pow_pos hb 3)
    _ = n := h

theorem cubePartOf_le {n : ℕ} (hn0 : n ≠ 0) (hsf : Squarefull n) : cubePartOf n ≤ n := by
  have h := sqPartOf_sq_mul_cubePartOf_cube hn0 hsf
  have ha : 0 < sqPartOf n := one_le_sqPartOf n
  calc cubePartOf n ≤ cubePartOf n ^ 3 := Nat.le_self_pow three_ne_zero _
    _ ≤ sqPartOf n ^ 2 * cubePartOf n ^ 3 :=
        Nat.le_mul_of_pos_left _ (pow_pos ha 2)
    _ = n := h

/-! ## R2 — the explicit squarefull constant and the Dirichlet bound -/

/-- **The explicit squarefull constant** `C_sq = 20736 = 3⁴·2⁸`: the product of the
`a`-sum majorant `(∑ a^{−3/2})⁴ ≤ 3⁴ = 81` and the `b`-sum majorant
`(∑ b^{−2})⁸ ≤ 2⁸ = 256`.  Nothing is `O(1)`-absorbed (law #253). -/
def cSq : ℝ := 20736

/-- The `a²b³` weight bound: `(a²b³)^{−3/4} = a^{−3/2}·b^{−9/4} ≤ a^{−3/2}·b^{−2}`. -/
theorem rpow_sq_cube_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((a ^ 2 * b ^ 3 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ))
      ≤ (a : ℝ) ^ (-(3 / 2 : ℝ)) * (b : ℝ) ^ (-(2 : ℝ)) := by
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := by linarith
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := by linarith
  have hcast : ((a ^ 2 * b ^ 3 : ℕ) : ℝ) = (a : ℝ) ^ 2 * (b : ℝ) ^ 3 := by push_cast; ring
  have hA : ((a : ℝ) ^ 2) ^ (-(3 / 4 : ℝ)) = (a : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast (a : ℝ) 2, ← Real.rpow_mul ha0]
    norm_num
  have hB : ((b : ℝ) ^ 3) ^ (-(3 / 4 : ℝ)) = (b : ℝ) ^ (-(9 / 4 : ℝ)) := by
    rw [← Real.rpow_natCast (b : ℝ) 3, ← Real.rpow_mul hb0]
    norm_num
  have hBle : (b : ℝ) ^ (-(9 / 4 : ℝ)) ≤ (b : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
  rw [hcast, Real.mul_rpow (by positivity) (by positivity), hA, hB]
  exact mul_le_mul_of_nonneg_left hBle (Real.rpow_nonneg ha0 _)

/-- **R2 — the squarefull Dirichlet bound at `σ = 3/4`.**  `∑_{d ≤ N} ‖sPart d‖·d^{−3/4}
≤ cSq` at every `1`-bounded multiplicative `F`.  Route: `sPart` is squarefull-supported
(R1) with `‖sPart d‖ ≤ τ(d)`; parametrize `d = a²b³`; `τ(a²b³) ≤ τ(a)²τ(b)³`
(`Nat.divisors_mul`); and the two `p`-series majorants close the double sum. -/
theorem sPart_dirichlet_bound_three_quarters {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) (hF1 : F 1 = 1)
    (hFb : ∀ n, ‖F n‖ ≤ 1) (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ)) ≤ cSq := by
  classical
  set G : ℕ × ℕ → ℝ := fun q =>
    ((q.1.divisors.card : ℝ) ^ 2 * (q.1 : ℝ) ^ (-(3 / 2 : ℝ)))
      * ((q.2.divisors.card : ℝ) ^ 3 * (q.2 : ℝ) ^ (-(2 : ℝ))) with hG
  have hGnn : ∀ q : ℕ × ℕ, 0 ≤ G q := fun q => by
    rw [hG]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  set S : Finset ℕ := {d ∈ Finset.Icc 1 N | Squarefull d} with hSdef
  have hSmem : ∀ d ∈ S, 1 ≤ d ∧ d ≤ N ∧ Squarefull d := by
    intro d hd
    have h := Finset.mem_filter.mp hd
    have h2 := Finset.mem_Icc.mp h.1
    exact ⟨h2.1, h2.2, h.2⟩
  -- Step 1: only the squarefull terms survive.
  have h1 : ∑ d ∈ Finset.Icc 1 N, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ))
      = ∑ d ∈ S, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ)) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro d hd hdS
    have hnsf : ¬ Squarefull d := fun h => hdS (Finset.mem_filter.mpr ⟨hd, h⟩)
    rw [sPart_eq_zero_of_not_squarefull hFm hF1 hnsf, norm_zero, zero_mul]
  -- Step 2: termwise domination by `G ∘ φ`.
  have h2 : ∀ d ∈ S, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ))
      ≤ G (sqPartOf d, cubePartOf d) := by
    intro d hd
    obtain ⟨hd1, _, hdsf⟩ := hSmem d hd
    have hd0 : d ≠ 0 := by omega
    set a := sqPartOf d with hadef
    set b := cubePartOf d with hbdef
    have hrep : a ^ 2 * b ^ 3 = d := sqPartOf_sq_mul_cubePartOf_cube hd0 hdsf
    have ha1 : 1 ≤ a := one_le_sqPartOf d
    have hb1 : 1 ≤ b := one_le_cubePartOf d
    have htau : ‖sPart F d‖ ≤ (a.divisors.card : ℝ) ^ 2 * (b.divisors.card : ℝ) ^ 3 := by
      refine le_trans (norm_sPart_le_card_divisors hFb d) ?_
      rw [← hrep]
      calc (((a ^ 2 * b ^ 3 : ℕ)).divisors.card : ℝ)
          ≤ ((a ^ 2 : ℕ).divisors.card : ℝ) * ((b ^ 3 : ℕ).divisors.card : ℝ) :=
            card_divisors_mul_le_real _ _
        _ ≤ ((a.divisors.card : ℝ) * (a.divisors.card : ℝ))
              * ((b.divisors.card : ℝ) * ((b.divisors.card : ℝ) * (b.divisors.card : ℝ))) := by
            have hA : ((a ^ 2 : ℕ).divisors.card : ℝ)
                ≤ (a.divisors.card : ℝ) * (a.divisors.card : ℝ) := by
              have := card_divisors_mul_le_real a a
              rwa [show a * a = a ^ 2 from by ring] at this
            have hB : ((b ^ 3 : ℕ).divisors.card : ℝ)
                ≤ (b.divisors.card : ℝ) * ((b.divisors.card : ℝ) * (b.divisors.card : ℝ)) := by
              have h1' := card_divisors_mul_le_real b (b * b)
              have h2' := card_divisors_mul_le_real b b
              have hbb : b * (b * b) = b ^ 3 := by ring
              rw [hbb] at h1'
              nlinarith [Nat.cast_nonneg (α := ℝ) b.divisors.card,
                Nat.cast_nonneg (α := ℝ) (b * b).divisors.card]
            exact mul_le_mul hA hB (Nat.cast_nonneg _) (by positivity)
        _ = (a.divisors.card : ℝ) ^ 2 * (b.divisors.card : ℝ) ^ 3 := by ring
    have hwt : (d : ℝ) ^ (-(3 / 4 : ℝ))
        ≤ (a : ℝ) ^ (-(3 / 2 : ℝ)) * (b : ℝ) ^ (-(2 : ℝ)) := by
      rw [← hrep]; exact rpow_sq_cube_le ha1 hb1
    have hnn1 : (0 : ℝ) ≤ (d : ℝ) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hnn2 : (0 : ℝ) ≤ (a.divisors.card : ℝ) ^ 2 * (b.divisors.card : ℝ) ^ 3 := by
      positivity
    calc ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ))
        ≤ ((a.divisors.card : ℝ) ^ 2 * (b.divisors.card : ℝ) ^ 3)
            * ((a : ℝ) ^ (-(3 / 2 : ℝ)) * (b : ℝ) ^ (-(2 : ℝ))) :=
          mul_le_mul htau hwt hnn1 hnn2
      _ = G (a, b) := by rw [hG]; ring
  -- Step 3: the map `d ↦ (sqPartOf d, cubePartOf d)` is injective on `S`.
  have hinj : ∀ d ∈ S, ∀ d' ∈ S,
      (sqPartOf d, cubePartOf d) = (sqPartOf d', cubePartOf d') → d = d' := by
    intro d hd d' hd' heq
    obtain ⟨hd1, _, hdsf⟩ := hSmem d hd
    obtain ⟨hd1', _, hdsf'⟩ := hSmem d' hd'
    have hr := sqPartOf_sq_mul_cubePartOf_cube (n := d) (by omega) hdsf
    have hr' := sqPartOf_sq_mul_cubePartOf_cube (n := d') (by omega) hdsf'
    rw [Prod.mk.injEq] at heq
    rw [← hr, ← hr', heq.1, heq.2]
  -- Step 4: the image sits in the box, and the box factorizes.
  have himg : S.image (fun d => (sqPartOf d, cubePartOf d))
      ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hd1, hdN, hdsf⟩ := hSmem d hd
    have hd0 : d ≠ 0 := by omega
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨one_le_sqPartOf d, le_trans (sqPartOf_le hd0 hdsf) hdN⟩,
      one_le_cubePartOf d, le_trans (cubePartOf_le hd0 hdsf) hdN⟩
  have hbox : ∑ q ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, G q
      = (∑ a ∈ Finset.Icc 1 N, (a.divisors.card : ℝ) ^ 2 * (a : ℝ) ^ (-(3 / 2 : ℝ)))
        * (∑ b ∈ Finset.Icc 1 N, (b.divisors.card : ℝ) ^ 3 * (b : ℝ) ^ (-(2 : ℝ))) := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
  -- Step 5: assemble.
  have hAsum : (∑ a ∈ Finset.Icc 1 N, (a.divisors.card : ℝ) ^ 2 * (a : ℝ) ^ (-(3 / 2 : ℝ)))
      ≤ 81 := by
    refine le_trans (sum_tau_sq_le (3 / 2) N) ?_
    have h := sum_Icc_three_halves_le N
    have hnn : (0 : ℝ) ≤ ∑ u ∈ Finset.Icc 1 N, (u : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Finset.sum_nonneg fun u _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc (∑ u ∈ Finset.Icc 1 N, (u : ℝ) ^ (-(3 / 2 : ℝ))) ^ 4 ≤ (3 : ℝ) ^ 4 :=
          pow_le_pow_left₀ hnn h 4
      _ = 81 := by norm_num
  have hBsum : (∑ b ∈ Finset.Icc 1 N, (b.divisors.card : ℝ) ^ 3 * (b : ℝ) ^ (-(2 : ℝ)))
      ≤ 256 := by
    refine le_trans (sum_tau_cube_le 2 N) ?_
    have h := sum_Icc_two_le N
    have hnn : (0 : ℝ) ≤ ∑ u ∈ Finset.Icc 1 N, (u : ℝ) ^ (-(2 : ℝ)) :=
      Finset.sum_nonneg fun u _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc (∑ u ∈ Finset.Icc 1 N, (u : ℝ) ^ (-(2 : ℝ))) ^ 8 ≤ (2 : ℝ) ^ 8 :=
          pow_le_pow_left₀ hnn h 8
      _ = 256 := by norm_num
  have hAnn : (0 : ℝ) ≤ ∑ a ∈ Finset.Icc 1 N,
      (a.divisors.card : ℝ) ^ 2 * (a : ℝ) ^ (-(3 / 2 : ℝ)) :=
    Finset.sum_nonneg fun a _ =>
      mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hBnn : (0 : ℝ) ≤ ∑ b ∈ Finset.Icc 1 N,
      (b.divisors.card : ℝ) ^ 3 * (b : ℝ) ^ (-(2 : ℝ)) :=
    Finset.sum_nonneg fun b _ =>
      mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc ∑ d ∈ Finset.Icc 1 N, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ))
      = ∑ d ∈ S, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ)) := h1
    _ ≤ ∑ d ∈ S, G (sqPartOf d, cubePartOf d) := Finset.sum_le_sum h2
    _ = ∑ q ∈ S.image (fun d => (sqPartOf d, cubePartOf d)), G q :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ q ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, G q :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun q _ _ => hGnn q)
    _ = (∑ a ∈ Finset.Icc 1 N, (a.divisors.card : ℝ) ^ 2 * (a : ℝ) ^ (-(3 / 2 : ℝ)))
          * (∑ b ∈ Finset.Icc 1 N, (b.divisors.card : ℝ) ^ 3 * (b : ℝ) ^ (-(2 : ℝ))) := hbox
    _ ≤ 81 * 256 := mul_le_mul hAsum hBsum hBnn (by norm_num)
    _ = cSq := by rw [cSq]; norm_num

/-- **R2 — `sPart_dirichlet_bound`.**  The bound at every `σ ∈ [3/4, 1]` (indeed at
every `σ ≥ 3/4`): the weight only decreases as `σ` grows. -/
theorem sPart_dirichlet_bound {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) (hF1 : F 1 = 1)
    (hFb : ∀ n, ‖F n‖ ≤ 1) {σ : ℝ} (hσ : 3 / 4 ≤ σ) (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, ‖sPart F d‖ * (d : ℝ) ^ (-σ) ≤ cSq := by
  refine le_trans (Finset.sum_le_sum ?_) (sPart_dirichlet_bound_three_quarters hFm hF1 hFb N)
  intro d hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    have := (Finset.mem_Icc.mp hd).1
    exact_mod_cast this
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)

/-- **R2 — the tail bound.**  `∑_{D < d ≤ N} ‖sPart d‖/d ≤ cSq·D^{−1/4}`: the
`σ = 3/4` vs `σ = 1` interpolation. -/
theorem sPart_tail_bound {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) (hF1 : F 1 = 1)
    (hFb : ∀ n, ‖F n‖ ≤ 1) {D : ℕ} (hD : 1 ≤ D) (N : ℕ) :
    ∑ d ∈ Finset.Icc (D + 1) N, ‖sPart F d‖ / (d : ℝ)
      ≤ cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hstep : ∀ d ∈ Finset.Icc (D + 1) N, ‖sPart F d‖ / (d : ℝ)
      ≤ (‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ))) * (D : ℝ) ^ (-(1 / 4 : ℝ)) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hdD : (D : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : D ≤ d)
    have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
    have hsplit : (d : ℝ) ^ (-(1 : ℝ))
        = (d : ℝ) ^ (-(3 / 4 : ℝ)) * (d : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_add hd0]; norm_num
    have hmono : (d : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (D : ℝ) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hD0 hdD (by norm_num)
    have hdiv : ‖sPart F d‖ / (d : ℝ) = ‖sPart F d‖ * (d : ℝ) ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one, div_eq_mul_inv]
    rw [hdiv, hsplit]
    have hnn : (0 : ℝ) ≤ ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ)) :=
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hd0.le _)
    calc ‖sPart F d‖ * ((d : ℝ) ^ (-(3 / 4 : ℝ)) * (d : ℝ) ^ (-(1 / 4 : ℝ)))
        = (‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ))) * (d : ℝ) ^ (-(1 / 4 : ℝ)) := by ring
      _ ≤ (‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ))) * (D : ℝ) ^ (-(1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hmono hnn
  have hsubset : Finset.Icc (D + 1) N ⊆ Finset.Icc 1 N := by
    intro d hd
    rw [Finset.mem_Icc] at hd ⊢
    omega
  have hDnn : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hD0.le _
  calc ∑ d ∈ Finset.Icc (D + 1) N, ‖sPart F d‖ / (d : ℝ)
      ≤ ∑ d ∈ Finset.Icc (D + 1) N,
          (‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ))) * (D : ℝ) ^ (-(1 / 4 : ℝ)) :=
        Finset.sum_le_sum hstep
    _ = (∑ d ∈ Finset.Icc (D + 1) N, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ)))
          * (D : ℝ) ^ (-(1 / 4 : ℝ)) := by rw [Finset.sum_mul]
    _ ≤ (∑ d ∈ Finset.Icc 1 N, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ)))
          * (D : ℝ) ^ (-(1 / 4 : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ hDnn
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ => ?_)
        exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right (sPart_dirichlet_bound_three_quarters hFm hF1 hFb N) hDnn

/-! ## R2 — the completely multiplicative corollary (the fallback narrowing)

At a completely multiplicative `F` — the consumer's actual datum `λχ̄·g_𝒥` is one —
`sPart(p^k) = F(p)^k·[k even]`, so `sPart` lives on the SQUARES with `‖sPart‖ ≤ 1`
and the `C_sq` page collapses to `∑_m m^{−3/2} ≤ 3`.  Recorded for the record: it
certifies the narrowing that the general R2 above makes unnecessary. -/

/-- Complete multiplicativity gives `F(p^k) = F(p)^k`. -/
theorem cm_pow {F : ℕ → ℂ} (hF1 : F 1 = 1)
    (hcm : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → F (m * n) = F m * F n) {p : ℕ} (hp : p ≠ 0)
    (k : ℕ) : F (p ^ k) = F p ^ k := by
  induction k with
  | zero => simpa using hF1
  | succ k ih => rw [pow_succ, hcm (pow_ne_zero k hp) hp, ih, pow_succ]

/-- A completely multiplicative datum is in particular multiplicative. -/
theorem cm_isMultiplicative {F : ℕ → ℂ} (hF1 : F 1 = 1)
    (hcm : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → F (m * n) = F m * F n) :
    (toArithmeticFunction F).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [toAF_apply, hF1], fun {m n} hm hn _ => ?_⟩
  simp only [toAF_apply, if_neg (Nat.mul_ne_zero hm hn), if_neg hm, if_neg hn]
  exact hcm hm hn

/-- The alternating telescope `∑_{j ≤ k} (−1)^{k−j} = [k even]`. -/
theorem alt_sum_shift (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ (k - j) = if Even k then 1 else 0 := by
  have h := Finset.sum_range_reflect (fun i => (-1 : ℂ) ^ i) (k + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [h, neg_one_geom_sum]
  by_cases hk : Even k
  · rw [if_neg (by simp [Nat.even_add_one, hk]), if_pos hk]
  · rw [if_pos (by simp [Nat.even_add_one, hk]), if_neg hk]

/-- **The CM Euler factor.**  `sPart F (p^k) = [k even]·F(p)^k`. -/
theorem sPart_cm_prime_pow {F : ℕ → ℂ} (hF1 : F 1 = 1)
    (hcm : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → F (m * n) = F m * F n) {p : ℕ} (hp : p.Prime)
    (k : ℕ) : sPart F (p ^ k) = (if Even k then (1 : ℂ) else 0) * F p ^ k := by
  rw [sPart_prime_pow F hp k, ← alt_sum_shift k, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  calc F (p ^ j) * (-(F p)) ^ (k - j)
      = F p ^ j * ((-1 : ℂ) ^ (k - j) * F p ^ (k - j)) := by
        rw [cm_pow hF1 hcm hp.pos.ne' j, neg_pow]
    _ = (-1 : ℂ) ^ (k - j) * F p ^ (j + (k - j)) := by rw [pow_add]; ring
    _ = (-1 : ℂ) ^ (k - j) * F p ^ k := by rw [show j + (k - j) = k from by omega]

/-- At a CM datum the Euler factors are `1`-bounded. -/
theorem sPart_cm_prime_pow_norm_le_one {F : ℕ → ℂ} (hF1 : F 1 = 1)
    (hcm : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → F (m * n) = F m * F n) (hFb : ∀ n, ‖F n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : ‖sPart F (p ^ k)‖ ≤ 1 := by
  rw [sPart_cm_prime_pow hF1 hcm hp k, norm_mul, norm_pow]
  refine mul_le_one₀ ?_ (by positivity) (pow_le_one₀ (norm_nonneg _) (hFb p))
  by_cases hk : Even k <;> simp [hk]

/-- The prime-power factorization of `sPart` at a nonzero argument. -/
theorem sPart_factorization_prod {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) {n : ℕ} (hn0 : n ≠ 0) :
    sPart F n = ∏ p ∈ n.factorization.support, sPart F (p ^ n.factorization p) := by
  have hAF := (sPart_isMultiplicative hFm).multiplicative_factorization _ hn0
  have hL : toArithmeticFunction (sPart F) n = sPart F n := by
    rw [toAF_apply, if_neg hn0]
  have hR : (n.factorization.prod fun p k => toArithmeticFunction (sPart F) (p ^ k))
      = ∏ p ∈ n.factorization.support, sPart F (p ^ n.factorization p) := by
    rw [Finsupp.prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp := prime_of_mem_factorization_support hp
    rw [toAF_apply, if_neg (pow_ne_zero _ hpp.pos.ne')]
  rw [hL, hR] at hAF
  exact hAF

/-- **CM — the `1`-bound.**  `‖sPart F n‖ ≤ 1` at every CM `1`-bounded `F`. -/
theorem sPart_cm_norm_le_one {F : ℕ → ℂ} (hF1 : F 1 = 1)
    (hcm : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → F (m * n) = F m * F n) (hFb : ∀ n, ‖F n‖ ≤ 1)
    (n : ℕ) : ‖sPart F n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rw [sPart_factorization_prod (cm_isMultiplicative hF1 hcm) hn0, norm_prod]
  refine Finset.prod_le_one (fun p _ => norm_nonneg _) (fun p hp => ?_)
  exact sPart_cm_prime_pow_norm_le_one hF1 hcm hFb
    (prime_of_mem_factorization_support hp) _

/-- **CM — the even-exponent forcing.**  If `sPart F n ≠ 0` then every exponent in the
factorization of `n` is even (the odd Euler factors vanish). -/
theorem sPart_cm_factorization_even {F : ℕ → ℂ} (hF1 : F 1 = 1)
    (hcm : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → F (m * n) = F m * F n) {n : ℕ}
    (hne : sPart F n ≠ 0) (p : ℕ) : Even (n.factorization p) := by
  by_contra hodd
  have hn0 : n ≠ 0 := by rintro rfl; exact hne (sPart_zero F)
  have hk0 : n.factorization p ≠ 0 := by
    intro h
    rw [h] at hodd
    exact hodd ⟨0, rfl⟩
  have hpsupp : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hk0
  have hpp := prime_of_mem_factorization_support hpsupp
  have hzero : sPart F (p ^ n.factorization p) = 0 := by
    rw [sPart_cm_prime_pow hF1 hcm hpp, if_neg hodd, zero_mul]
  exact hne (by
    rw [sPart_factorization_prod (cm_isMultiplicative hF1 hcm) hn0]
    exact Finset.prod_eq_zero hpsupp hzero)

/-- **CM — `sPart_cm_square_support`.**  At a completely multiplicative `F` the smooth
part is supported on the SQUARES: `sPart F n ≠ 0` forces `n = (sqPartOf n)²` with
`sqPartOf n ≥ 1`, and `‖sPart F n‖ ≤ 1` everywhere (`sPart_cm_norm_le_one`).  This is
the fallback narrowing of ⟦AMENDMENT C⟧, recorded but not needed: the general
`sPart_dirichlet_bound` above closes at `cSq`. -/
theorem sPart_cm_square_support {F : ℕ → ℂ} (hF1 : F 1 = 1)
    (hcm : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → F (m * n) = F m * F n) {n : ℕ}
    (hne : sPart F n ≠ 0) : 1 ≤ sqPartOf n ∧ n = sqPartOf n ^ 2 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hne (sPart_zero F)
  have heven := sPart_cm_factorization_even hF1 hcm hne
  have hsf : Squarefull n := by
    refine (squarefull_iff_factorization hn0).mpr fun p hp1 => ?_
    have := heven p
    rw [hp1] at this
    simp at this
  have hcube : cubePartOf n = 1 := by
    rw [cubePartOf, Finsupp.prod]
    refine Finset.prod_eq_one fun p _ => ?_
    have hmod : n.factorization p % 2 = 0 := Nat.even_iff.mp (heven p)
    rw [hmod, pow_zero]
  have hrep := sqPartOf_sq_mul_cubePartOf_cube hn0 hsf
  rw [hcube, one_pow, mul_one] at hrep
  exact ⟨one_le_sqPartOf n, hrep.symm⟩

/-- `(a²)^{−3/4} = a^{−3/2}`. -/
theorem rpow_sq_neg_three_quarters {a : ℕ} :
    ((a ^ 2 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) = (a : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hcast : ((a ^ 2 : ℕ) : ℝ) = (a : ℝ) ^ 2 := by push_cast; ring
  rw [hcast, ← Real.rpow_natCast (a : ℝ) 2, ← Real.rpow_mul ha0]
  norm_num

/-- **CM — the `ζ(3/2)` Dirichlet bound.**  At a CM `1`-bounded `F`,
`∑_{d ≤ N} ‖sPart d‖·d^{−3/4} ≤ 3`: the support is the squares and each value is
`1`-bounded, so the sum injects into `∑_m m^{−3/2}`. -/
theorem sPart_cm_dirichlet_bound {F : ℕ → ℂ} (hF1 : F 1 = 1)
    (hcm : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → F (m * n) = F m * F n) (hFb : ∀ n, ‖F n‖ ≤ 1)
    (N : ℕ) : ∑ d ∈ Finset.Icc 1 N, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 3 := by
  classical
  set S : Finset ℕ := {d ∈ Finset.Icc 1 N | sPart F d ≠ 0} with hSdef
  have hSmem : ∀ d ∈ S, (1 ≤ d ∧ d ≤ N) ∧ sPart F d ≠ 0 := by
    intro d hd
    have h := Finset.mem_filter.mp hd
    exact ⟨Finset.mem_Icc.mp h.1, h.2⟩
  have h1 : ∑ d ∈ Finset.Icc 1 N, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ))
      = ∑ d ∈ S, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ)) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro d hd hdS
    have hz : sPart F d = 0 := by
      by_contra hz
      exact hdS (Finset.mem_filter.mpr ⟨hd, hz⟩)
    rw [hz, norm_zero, zero_mul]
  have h2 : ∀ d ∈ S, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ))
      ≤ (sqPartOf d : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro d hd
    obtain ⟨-, hne⟩ := hSmem d hd
    obtain ⟨-, hrep⟩ := sPart_cm_square_support hF1 hcm hne
    have hw : (d : ℝ) ^ (-(3 / 4 : ℝ)) = (sqPartOf d : ℝ) ^ (-(3 / 2 : ℝ)) := by
      conv_lhs => rw [hrep]
      exact rpow_sq_neg_three_quarters
    rw [hw]
    have hnn : (0 : ℝ) ≤ (sqPartOf d : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc ‖sPart F d‖ * (sqPartOf d : ℝ) ^ (-(3 / 2 : ℝ))
        ≤ 1 * (sqPartOf d : ℝ) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (sPart_cm_norm_le_one hF1 hcm hFb d) hnn
      _ = (sqPartOf d : ℝ) ^ (-(3 / 2 : ℝ)) := one_mul _
  have hinj : ∀ d ∈ S, ∀ d' ∈ S, sqPartOf d = sqPartOf d' → d = d' := by
    intro d hd d' hd' heq
    obtain ⟨-, hne⟩ := hSmem d hd
    obtain ⟨-, hne'⟩ := hSmem d' hd'
    obtain ⟨-, hrep⟩ := sPart_cm_square_support hF1 hcm hne
    obtain ⟨-, hrep'⟩ := sPart_cm_square_support hF1 hcm hne'
    rw [hrep, hrep', heq]
  have himg : S.image sqPartOf ⊆ Finset.Icc 1 N := by
    intro m hm
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨⟨hd1, hdN⟩, hne⟩ := hSmem d hd
    obtain ⟨hm1, hrep⟩ := sPart_cm_square_support hF1 hcm hne
    have hle : sqPartOf d ≤ d := by
      calc sqPartOf d ≤ sqPartOf d ^ 2 := Nat.le_self_pow two_ne_zero _
        _ = d := hrep.symm
    exact Finset.mem_Icc.mpr ⟨hm1, le_trans hle hdN⟩
  calc ∑ d ∈ Finset.Icc 1 N, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ))
      = ∑ d ∈ S, ‖sPart F d‖ * (d : ℝ) ^ (-(3 / 4 : ℝ)) := h1
    _ ≤ ∑ d ∈ S, (sqPartOf d : ℝ) ^ (-(3 / 2 : ℝ)) := Finset.sum_le_sum h2
    _ = ∑ m ∈ S.image sqPartOf, (m : ℝ) ^ (-(3 / 2 : ℝ)) :=
        (Finset.sum_image (f := fun m : ℕ => (m : ℝ) ^ (-(3 / 2 : ℝ))) hinj).symm
    _ ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(3 / 2 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg himg
          (fun m _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ 3 := sum_Icc_three_halves_le N

/-! ## The seam-datum instantiation (the hand-off to the station stones)

`𝔉 := seamCoeff F (fun _ => 1) t₀ = F(n)·n^{−it₀}` is `1`-bounded, multiplicative
whenever `F` is (the centre twist is completely multiplicative), and vanishes at `0`
by construction — so R1/R2 apply to it verbatim. -/

/-- `𝔉(1) = 1`. -/
theorem seamCoeff_one_eq_one {F : ℕ → ℂ} (hF1 : F 1 = 1) (t₀ : ℝ) :
    seamCoeff F (fun _ => 1) t₀ 1 = 1 := by
  simp [seamCoeff, hF1]

/-- **The seam datum is multiplicative.**  The centre twist `n ↦ n^{−it₀}` is
completely multiplicative, so `𝔉 = F·(·)^{−it₀}` inherits `F`'s multiplicativity. -/
theorem seamCoeff_isMultiplicative {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) (t₀ : ℝ) :
    (toArithmeticFunction (seamCoeff F (fun _ => 1) t₀)).IsMultiplicative := by
  have hF1 : F 1 = 1 := by
    have h := hFm.map_one
    rwa [toAF_apply, if_neg one_ne_zero] at h
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [toAF_apply, seamCoeff_one_eq_one hF1], fun {m n} hm hn hco => ?_⟩
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  have hF : F (m * n) = F m * F n := by
    have h := hFm.map_mul_of_coprime hco
    rwa [toAF_apply, toAF_apply, toAF_apply, if_neg hmn, if_neg hm, if_neg hn] at h
  have htw : ((m * n : ℕ) : ℂ) ^ (-(t₀ : ℂ) * Complex.I)
      = (m : ℂ) ^ (-(t₀ : ℂ) * Complex.I) * (n : ℂ) ^ (-(t₀ : ℂ) * Complex.I) := by
    push_cast
    exact Complex.natCast_mul_natCast_cpow m n _
  simp only [toAF_apply, if_neg hmn, if_neg hm, if_neg hn, seamCoeff]
  rw [hF, htw]
  ring

/-- The seam datum is `1`-bounded. -/
theorem norm_seamCoeff_trivial_le {F : ℕ → ℂ} (hFb : ∀ n, ‖F n‖ ≤ 1) (t₀ : ℝ) (n : ℕ) :
    ‖seamCoeff F (fun _ => 1) t₀ n‖ ≤ 1 :=
  norm_seamCoeff_le hFb (fun _ => le_of_eq norm_one) t₀ n

/-- **The Route-III factorization at the seam datum** (⟦AMENDMENT C⟧'s
`𝔉 = sPart ⍟ ellLin(𝔉|primes)`). -/
theorem sPart_seamCoeff_factorization (F : ℕ → ℂ) (t₀ : ℝ) :
    sPart (seamCoeff F (fun _ => 1) t₀) ⍟ ellLin (seamCoeff F (fun _ => 1) t₀)
      = seamCoeff F (fun _ => 1) t₀ :=
  sPart_factorization (seamCoeff_zero F (fun _ => 1) t₀)

/-- **R2 at the seam datum.**  `∑_{d ≤ N} ‖sPart 𝔉 d‖·d^{−σ} ≤ cSq` for `σ ≥ 3/4`. -/
theorem sPart_seamCoeff_dirichlet_bound {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) (hFb : ∀ n, ‖F n‖ ≤ 1)
    (t₀ : ℝ) {σ : ℝ} (hσ : 3 / 4 ≤ σ) (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, ‖sPart (seamCoeff F (fun _ => 1) t₀) d‖ * (d : ℝ) ^ (-σ)
      ≤ cSq := by
  have hF1 : F 1 = 1 := by
    have h := hFm.map_one
    rwa [toAF_apply, if_neg one_ne_zero] at h
  exact sPart_dirichlet_bound (seamCoeff_isMultiplicative hFm t₀)
    (seamCoeff_one_eq_one hF1 t₀) (norm_seamCoeff_trivial_le hFb t₀) hσ N

/-- **R2's tail at the seam datum.** -/
theorem sPart_seamCoeff_tail_bound {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) (hFb : ∀ n, ‖F n‖ ≤ 1)
    (t₀ : ℝ) {D : ℕ} (hD : 1 ≤ D) (N : ℕ) :
    ∑ d ∈ Finset.Icc (D + 1) N, ‖sPart (seamCoeff F (fun _ => 1) t₀) d‖ / (d : ℝ)
      ≤ cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hF1 : F 1 = 1 := by
    have h := hFm.map_one
    rwa [toAF_apply, if_neg one_ne_zero] at h
  exact sPart_tail_bound (seamCoeff_isMultiplicative hFm t₀)
    (seamCoeff_one_eq_one hF1 t₀) (norm_seamCoeff_trivial_le hFb t₀) hD N

end Salt.MR
