/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Factorization.PrimePow
import Salt.MR.HalaszCore

/-!
# HALASZ-INFRA wave I-1, FILE B — the squarefree-linearized `Λ_ℓ` seam (`HalaszLambda`)

The `κ = 1` disarmament of the Granville–Harper–Soundararajan Halász engine: the
Dirichlet-series bookkeeping is carried by a *squarefree-linearized* twist `ℓ`
of a prime-values datum `g : ℕ → ℂ` (only `g(p)` matters), whose companion
"generalized von Mangoldt" `λ_lin` is dominated by the true `Λ` at *every* `n`
(hypothesis `‖g(p)‖ ≤ 1`).  This is the load-bearing simplification: no `2^{k+1}`
budget, and — crucially — the whole ladder is a *product form*
`−(d/ds) L(ℓ) = L(λ_lin)·L(ℓ)`, so the zero set of the completed `L`-function
never enters (no division by any `L`-series anywhere).

Rungs (freeze `docs/exploration/halasz-infra-freeze.md`, FILE B):
* `L0'` `ellLin`/`ellLinInv`, `ellLin_mul_inv : ellLin g ⍟ ellLinInv g = δ` — the
  per-Euler-factor telescope (`ℓ * ℓ⁻¹ = 1` on prime powers).
* `L1'` `lambdaLin`, `lambdaLin_norm_le : ‖λ_lin(n)‖ ≤ Λ(n)` for ALL `n`.
* `L2'` `lambdaLin_convolution : log · ℓ = λ_lin ⍟ ℓ` — unconditional identity.
* `L4'` `ellLin_lseries_deriv : −(d/ds) L(ℓ) = L(λ_lin)·L(ℓ)` on `1 < re s`.
* `L3'` the smooth-part split (C-rung; the `C_sq` squarefull constant carried
  in-statement), composing with `HalaszCore.halasz_cosh_ineq_complex`.

`⍟` is `LSeries.convolution`, `δ` is `LSeries.delta` (`LSeries.notation`).
-/

namespace Salt.MR

open scoped BigOperators LSeries.notation
open ArithmeticFunction

/-- **L0' datum.** The squarefree-linearized twist `ℓ` of `g`: the multiplicative
function supported on squarefree `n` with `ℓ(n) = ∏_{p ∣ n} g(p)`.  (`ℓ(p) = g(p)`,
`ℓ(p^k) = 0` for `k ≥ 2`.) -/
noncomputable def ellLin (g : ℕ → ℂ) : ℕ → ℂ := fun n =>
  if n = 0 then 0 else if Squarefree n then ∏ p ∈ n.primeFactors, g p else 0

/-- **L0' datum.** The Dirichlet inverse of `ellLin g`: multiplicative with
`ℓ⁻¹(p^k) = (−g(p))^k`. -/
noncomputable def ellLinInv (g : ℕ → ℂ) : ℕ → ℂ := fun n =>
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, (-(g p)) ^ (n.factorization p)

/-- **L1' datum.** The generalized von Mangoldt of the linearized twist:
`λ_lin(p^k) = (−1)^{k−1} g(p)^k log p`, supported on prime powers. -/
noncomputable def lambdaLin (g : ℕ → ℂ) : ℕ → ℂ := fun n =>
  if IsPrimePow n then
    (-1) ^ (n.factorization n.minFac - 1) * g n.minFac ^ (n.factorization n.minFac)
      * (Real.log n.minFac : ℂ)
  else 0

variable (g : ℕ → ℂ)

/-! ## L1' — the `κ = 1` domination `‖λ_lin(n)‖ ≤ Λ(n)` at every `n` -/

/-- **L1' (freeze FILE B).**  With `‖g(p)‖ ≤ 1` at every prime, the linearized
generalized von Mangoldt is dominated by the true von Mangoldt at EVERY `n`.
This is the design's `κ = 1` disarmament: no `2^{k+1}` budget is ever carried. -/
theorem lambdaLin_norm_le (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (n : ℕ) :
    ‖lambdaLin g n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · have hp : (n.minFac).Prime :=
      Nat.minFac_prime (by rintro rfl; exact not_isPrimePow_one hn)
    have hlog : (0 : ℝ) ≤ Real.log (n.minFac) :=
      Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have hpow : ‖g n.minFac‖ ^ (n.factorization n.minFac) ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (hg _ hp)
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hn]
    have hneg : ‖(-1 : ℂ)‖ = 1 := by simp
    have hval : ‖lambdaLin g n‖
        = ‖g n.minFac‖ ^ (n.factorization n.minFac) * Real.log (n.minFac) := by
      simp only [lambdaLin, if_pos hn]
      rw [norm_mul, norm_mul, norm_pow, norm_pow, hneg, one_pow, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hlog]
    rw [hval]
    exact mul_le_of_le_one_left hlog hpow
  · simp only [lambdaLin, if_neg hn, norm_zero]
    exact ArithmeticFunction.vonMangoldt_nonneg

/-! ## L0' — multiplicativity toolkit for `ellLin`/`ellLinInv`

`ellLin g` and `ellLinInv g` are multiplicative; on prime powers they telescope so
their Dirichlet convolution is the identity `δ`.  We route through `ArithmeticFunction`
so the standard `eq_iff_eq_on_prime_powers` machinery applies. -/

/-- Pointwise value of `toArithmeticFunction`. -/
lemma toAF_apply (f : ℕ → ℂ) (k : ℕ) :
    toArithmeticFunction f k = if k = 0 then 0 else f k := rfl

@[local simp] lemma ellLin_one : ellLin g 1 = 1 := by
  simp [ellLin, Nat.primeFactors_one]

@[local simp] lemma ellLinInv_one : ellLinInv g 1 = 1 := by
  simp [ellLinInv, Nat.primeFactors_one]

/-- `ℓ(p) = g(p)` at a prime. -/
lemma ellLin_apply_prime {p : ℕ} (hp : p.Prime) : ellLin g p = g p := by
  simp only [ellLin, if_neg hp.pos.ne', if_pos hp.squarefree, hp.primeFactors,
    Finset.prod_singleton]

/-- `ℓ(p^k) = 0` for `k ≥ 2` (support in squarefree). -/
lemma ellLin_prime_pow_ge_two {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 2 ≤ m) :
    ellLin g (p ^ m) = 0 := by
  have hpm : p ^ m ≠ 0 := pow_ne_zero m hp.pos.ne'
  have hnsq : ¬ Squarefree (p ^ m) := by
    intro hsq
    have hdvd : p * p ∣ p ^ m := by rw [← pow_two]; exact pow_dvd_pow p hm
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p hdvd))
  simp only [ellLin, if_neg hpm, if_neg hnsq]

/-- `ℓ⁻¹(p^m) = (−g(p))^m` at all `m`. -/
lemma ellLinInv_prime_pow {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ellLinInv g (p ^ m) = (-(g p)) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [ellLinInv]
  · have hpm : p ^ m ≠ 0 := pow_ne_zero m hp.pos.ne'
    simp only [ellLinInv, if_neg hpm, Nat.primeFactors_prime_pow hm.ne' hp,
      Finset.prod_singleton]
    congr 1
    rw [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]

/-- Multiplicativity of `ellLin` on coprime nonzero arguments. -/
lemma ellLin_mul_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hco : m.Coprime n) :
    ellLin g (m * n) = ellLin g m * ellLin g n := by
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  simp only [ellLin, if_neg hm, if_neg hn, if_neg hmn]
  by_cases hsq : Squarefree (m * n)
  · obtain ⟨hsm, hsn⟩ := (Nat.squarefree_mul hco).mp hsq
    rw [if_pos hsq, if_pos hsm, if_pos hsn, Nat.Coprime.primeFactors_mul hco,
      Finset.prod_union hco.disjoint_primeFactors]
  · rw [if_neg hsq, Nat.squarefree_mul hco] at *
    rcases not_and_or.mp hsq with h | h
    · rw [if_neg h, zero_mul]
    · rw [if_neg h, mul_zero]

/-- Multiplicativity of `ellLinInv` on coprime nonzero arguments. -/
lemma ellLinInv_mul_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hco : m.Coprime n) :
    ellLinInv g (m * n) = ellLinInv g m * ellLinInv g n := by
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  have hfac : (m * n).factorization = m.factorization + n.factorization :=
    Nat.factorization_mul hm hn
  simp only [ellLinInv, if_neg hm, if_neg hn, if_neg hmn]
  rw [Nat.Coprime.primeFactors_mul hco, Finset.prod_union hco.disjoint_primeFactors]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hzero : n.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      exact fun hd => (Finset.disjoint_left.mp hco.disjoint_primeFactors hp)
        (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hd, hn⟩)
    rw [show (m * n).factorization p = m.factorization p by
      rw [hfac, Finsupp.add_apply, hzero, add_zero]]
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hzero : m.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      exact fun hd => (Finset.disjoint_right.mp hco.disjoint_primeFactors hp)
        (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hd, hm⟩)
    rw [show (m * n).factorization p = n.factorization p by
      rw [hfac, Finsupp.add_apply, hzero, zero_add]]

lemma isMult_ellLin : (toArithmeticFunction (ellLin g)).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [toAF_apply], fun {m n} hm hn hco => ?_⟩
  simp only [toAF_apply, if_neg (Nat.mul_ne_zero hm hn), if_neg hm, if_neg hn]
  exact ellLin_mul_coprime g hm hn hco

lemma isMult_ellLinInv : (toArithmeticFunction (ellLinInv g)).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [toAF_apply], fun {m n} hm hn hco => ?_⟩
  simp only [toAF_apply, if_neg (Nat.mul_ne_zero hm hn), if_neg hm, if_neg hn]
  exact ellLinInv_mul_coprime g hm hn hco

/-- The Dirichlet convolution of `toArithmeticFunction`s at a prime power collapses to a
finite range sum — the per-Euler-factor local picture. -/
lemma convAF_prime_pow (F G : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (toArithmeticFunction F * toArithmeticFunction G) (p ^ i)
      = ∑ j ∈ Finset.range (i + 1), F (p ^ j) * G (p ^ (i - j)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal fun d e =>
        toArithmeticFunction F d * toArithmeticFunction G e, Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Nat.pow_div hji hp.pos, toAF_apply, toAF_apply, if_neg (pow_ne_zero j hp.pos.ne'),
    if_neg (pow_ne_zero (i - j) hp.pos.ne')]

/-! ## L0' — the per-Euler-factor telescope `ℓ ⍟ ℓ⁻¹ = δ` -/

/-- **L0' (freeze FILE B).**  The Dirichlet-inverse identity: the squarefree-linearized
twist convolved with its companion is the multiplicative identity `δ`.  Per Euler factor
`p`, the local convolution telescopes — for `k ≥ 1`,
`∑_{a+b=k} ℓ(p^a) ℓ⁻¹(p^b) = ℓ⁻¹(p^k) + g(p)·ℓ⁻¹(p^{k−1}) = (−g(p))^k + g(p)(−g(p))^{k−1} = 0`
(only `a = 0, 1` survive, since `ℓ(p^a) = 0` for `a ≥ 2`).  A pure product-form fact:
no `L`-series and no division enters. -/
theorem ellLin_mul_inv : ellLin g ⍟ ellLinInv g = δ := by
  have key : toArithmeticFunction (ellLin g) * toArithmeticFunction (ellLinInv g) = 1 := by
    rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
        ((isMult_ellLin g).mul (isMult_ellLinInv g)) _ ArithmeticFunction.isMultiplicative_one]
    intro p i hp
    rw [convAF_prime_pow _ _ hp, ArithmeticFunction.one_apply]
    rcases i with _ | i'
    · simp
    · rw [if_neg (Nat.one_lt_pow (Nat.succ_ne_zero i') hp.one_lt).ne']
      have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (i' + 1 + 1) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
      have hzero : ∀ j ∈ Finset.range (i' + 1 + 1), j ∉ ({0, 1} : Finset ℕ) →
          ellLin g (p ^ j) * ellLinInv g (p ^ (i' + 1 - j)) = 0 := by
        intro j _ hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        obtain ⟨hj0, hj1⟩ := not_or.mp hj
        rw [ellLin_prime_pow_ge_two g hp (by omega : 2 ≤ j), zero_mul]
      rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1),
        ellLinInv_prime_pow g hp, ellLinInv_prime_pow g hp, pow_zero, ellLin_one, pow_one,
        ellLin_apply_prime g hp, one_mul, Nat.sub_zero, Nat.add_sub_cancel, pow_succ]
      ring
  change (⇑(toArithmeticFunction (ellLin g) * toArithmeticFunction (ellLinInv g)) : ℕ → ℂ) = δ
  rw [key]
  exact ArithmeticFunction.one_eq_delta

/-! ## L2' — the unconditional algebraic identity `log · ℓ = λ_lin ⍟ ℓ` -/

/-- `λ_lin(1) = 0`: `1` is not a prime power. -/
lemma lambdaLin_one : lambdaLin g 1 = 0 := by
  simp only [lambdaLin, if_neg not_isPrimePow_one]

/-- The prime-power value of `λ_lin`: `λ_lin(p^k) = (−1)^{k−1} g(p)^k log p` for `k ≥ 1`. -/
lemma lambdaLin_prime_pow_pos {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    lambdaLin g (p ^ k) = (-1) ^ (k - 1) * g p ^ k * (Real.log p : ℂ) := by
  have hpp : IsPrimePow (p ^ k) := hp.isPrimePow.pow hk
  have hmin : (p ^ k).minFac = p := hp.pow_minFac hk
  have hfac : (p ^ k).factorization p = k := by
    rw [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
  simp only [lambdaLin, if_pos hpp, hmin, hfac]

/-- **The derivation split.**  The Dirichlet convolution of a prime-power-supported `F` with a
multiplicative `G` obeys the Leibniz rule across coprime arguments.  This is the mechanism (the
generalization of `ArithmeticFunction.vonMangoldt_sum`) by which the `log`-weighted identity
`log · ℓ = λ_lin ⍟ ℓ` glues over the coprime factorization. -/
lemma conv_deriv_coprime (F G : ℕ → ℂ) (hF : ∀ n, ¬ IsPrimePow n → F n = 0)
    (hGmul : ∀ {c d : ℕ}, c ≠ 0 → d ≠ 0 → c.Coprime d → G (c * d) = G c * G d)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hco : a.Coprime b) :
    (F ⍟ G) (a * b) = (F ⍟ G) a * G b + G a * (F ⍟ G) b := by
  have expand : ∀ n : ℕ, (F ⍟ G) n
      = ∑ d ∈ n.divisors.filter IsPrimePow, F d * G (n / d) := by
    intro n
    simp only [LSeries.convolution_def]
    rw [Nat.sum_divisorsAntidiagonal fun d e => F d * G e]
    refine (Finset.sum_filter_of_ne fun d _ hne => ?_).symm
    by_contra hpp
    exact hne (by rw [hF d hpp, zero_mul])
  rw [expand (a * b), expand a, expand b, Nat.mul_divisors_filter_prime_pow hco,
    Finset.filter_union, Finset.sum_union (Nat.disjoint_divisors_filter_isPrimePow hco),
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hda, hane⟩, _⟩ := hd
    have hadd : a / d ≠ 0 := fun h => hane (by rw [← Nat.div_mul_cancel hda, h, zero_mul])
    have hdiv : a * b / d = a / d * b := by
      rw [Nat.mul_comm a b, Nat.mul_div_assoc b hda, Nat.mul_comm b (a / d)]
    rw [hdiv, hGmul hadd hb (hco.coprime_dvd_left ⟨d, (Nat.div_mul_cancel hda).symm⟩)]
    ring
  · refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdb, hbne⟩, _⟩ := hd
    have hbdd : b / d ≠ 0 := fun h => hbne (by rw [← Nat.div_mul_cancel hdb, h, zero_mul])
    have hcop : a.Coprime (b / d) := hco.coprime_dvd_right ⟨d, (Nat.div_mul_cancel hdb).symm⟩
    rw [Nat.mul_div_assoc a hdb, hGmul ha hbdd hcop]
    ring

/-- **L2' (freeze FILE B).**  The unconditional algebraic identity `log · ℓ = λ_lin ⍟ ℓ`.
`log` is completely additive and `ℓ` is multiplicative, so both sides obey the same Leibniz
rule across coprime factors (`recOnPrimeCoprime`); on prime powers the two-term telescope
`λ_lin ⍟ ℓ (p^k) = λ_lin(p^k) + g(p) λ_lin(p^{k−1}) [k≥2] = 0` matches `log(p^k)·ℓ(p^k)`. -/
theorem lambdaLin_convolution (n : ℕ) :
    (Real.log n : ℂ) * ellLin g n = ((lambdaLin g) ⍟ (ellLin g)) n := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp [ellLin]
  | prime_pow p k hp =>
    have hconv : (lambdaLin g ⍟ ellLin g) (p ^ k)
        = ∑ j ∈ Finset.range (k + 1), lambdaLin g (p ^ j) * ellLin g (p ^ (k - j)) :=
      convAF_prime_pow (lambdaLin g) (ellLin g) hp k
    rw [hconv]
    rcases k with _ | _ | k''
    · simp [lambdaLin, not_isPrimePow_one]
    · rw [Finset.sum_range_succ, Finset.sum_range_one, lambdaLin_prime_pow_pos g hp one_ne_zero]
      simp only [pow_zero, pow_one, Nat.sub_zero, Nat.sub_self, lambdaLin_one, ellLin_one,
        ellLin_apply_prime g hp, zero_mul, zero_add, mul_one]
      ring
    · rw [ellLin_prime_pow_ge_two g hp (by omega : 2 ≤ k'' + 1 + 1), mul_zero]
      symm
      have hsub : ({k'' + 1, k'' + 1 + 1} : Finset ℕ) ⊆ Finset.range (k'' + 1 + 1 + 1) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
      have hzero : ∀ j ∈ Finset.range (k'' + 1 + 1 + 1),
          j ∉ ({k'' + 1, k'' + 1 + 1} : Finset ℕ) →
          lambdaLin g (p ^ j) * ellLin g (p ^ (k'' + 1 + 1 - j)) = 0 := by
        intro j hj hj'
        simp only [Finset.mem_range] at hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj'
        obtain ⟨h1, h2⟩ := not_or.mp hj'
        rw [ellLin_prime_pow_ge_two g hp (by omega : 2 ≤ k'' + 1 + 1 - j), mul_zero]
      rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by omega : k'' + 1 ≠ k'' + 1 + 1),
        lambdaLin_prime_pow_pos g hp (by omega : k'' + 1 ≠ 0),
        lambdaLin_prime_pow_pos g hp (by omega : k'' + 1 + 1 ≠ 0)]
      rw [show k'' + 1 + 1 - (k'' + 1) = 1 by omega, show k'' + 1 + 1 - (k'' + 1 + 1) = 0 by omega,
        pow_one, pow_zero, ellLin_apply_prime g hp, ellLin_one, mul_one,
        show k'' + 1 - 1 = k'' by omega, show k'' + 1 + 1 - 1 = k'' + 1 by omega]
      ring
  | coprime a b ha hb hco iha ihb =>
    have hae : a ≠ 0 := by omega
    have hbe : b ≠ 0 := by omega
    have hN : (lambdaLin g ⍟ ellLin g) (a * b)
        = (lambdaLin g ⍟ ellLin g) a * ellLin g b + ellLin g a * (lambdaLin g ⍟ ellLin g) b :=
      conv_deriv_coprime (lambdaLin g) (ellLin g)
        (fun n hn => by simp only [lambdaLin, if_neg hn])
        (fun {c d} hc hd hcd => ellLin_mul_coprime g hc hd hcd) hae hbe hco
    rw [hN, ← iha, ← ihb, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr hae) (Nat.cast_ne_zero.mpr hbe),
      ellLin_mul_coprime g hae hbe hco]
    push_cast
    ring

/-! ## L4' — the product-form derivative `−(d/ds) L(ℓ) = L(λ_lin)·L(ℓ)` -/

/-- With `‖g(p)‖ ≤ 1` at every prime, `ℓ` is bounded by `1` everywhere (empty/singleton or
squarefree product of unit-bounded factors). -/
lemma ellLin_norm_le_one (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (n : ℕ) : ‖ellLin g n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [ellLin]
  · by_cases hsq : Squarefree n
    · simp only [ellLin, if_neg hn, if_pos hsq]
      calc ‖∏ p ∈ n.primeFactors, g p‖ = ∏ p ∈ n.primeFactors, ‖g p‖ := norm_prod _ _
        _ ≤ 1 := Finset.prod_le_one (fun p _ => norm_nonneg _)
                  (fun p hp => hg p (Nat.prime_of_mem_primeFactors hp))
    · rw [show ellLin g n = 0 by simp only [ellLin, if_neg hn, if_neg hsq], norm_zero]
      exact zero_le_one

/-- **L4' (freeze FILE B).**  The product-form logarithmic-derivative identity on `1 < re s`:
`−(d/ds) L(ℓ, s) = L(λ_lin, s)·L(ℓ, s)`.  Route: mathlib's `LSeries_deriv` (abscissa `≤ 1`
from `‖ℓ‖ ≤ 1`) turns the derivative into `L(log·ℓ)`, `L2'` rewrites `log·ℓ = λ_lin ⍟ ℓ`,
and `LSeries_convolution'` (with `λ_lin` dominated by `Λ`) factors the convolution.
**No division by any `L`-series occurs**: the `F`-zero-set problem never enters. -/
theorem ellLin_lseries_deriv (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    -deriv (LSeries (ellLin g)) s = LSeries (lambdaLin g) s * LSeries (ellLin g) s := by
  have hbound : ∀ n, ‖ellLin g n‖ ≤ 1 := ellLin_norm_le_one g hg
  have habs : LSeries.abscissaOfAbsConv (ellLin g) < s.re :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => hbound n⟩)
      (by exact_mod_cast hs)
  have hfun : LSeries.logMul (ellLin g) = lambdaLin g ⍟ ellLin g := by
    funext n
    rw [← lambdaLin_convolution g n]
    change Complex.log ↑n * ellLin g n = (Real.log n : ℂ) * ellLin g n
    rw [Complex.natCast_log]
  have hsumEll : LSeriesSummable (ellLin g) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hbound n) hs
  have hsumLam : LSeriesSummable (lambdaLin g) s := by
    have hΛ : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
      LSeriesSummable_vonMangoldt hs
    rw [LSeriesSummable, ← summable_norm_iff] at hΛ ⊢
    refine hΛ.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => LSeries.norm_term_le s ?_)
    calc ‖lambdaLin g n‖ ≤ ArithmeticFunction.vonMangoldt n := lambdaLin_norm_le g hg n
      _ = ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [LSeries_deriv habs, neg_neg, hfun, LSeries_convolution' hsumLam hsumEll]

/-! ## L3' — the smooth-part split (partial: the frozen factorization backbone)

The frozen OUTPUT contract of L3' is `fg_J = sPart ⍟ ellLin(g·1_{p>y})` with
`sPart := fg_J ⍟ ellLinInv(g·1_{p>y})`, plus the analytic Euler-form bound
`‖LSeries sPart (σ+it)‖ ≤ (A.11 form)·C_sq` (with `C_sq` the explicit squarefull
`O(1)`) composing with `HalaszCore.halasz_cosh_ineq_complex`.  The **factorization
backbone** below — the load-bearing algebraic shape — is a clean corollary of `L0'`
and is fully self-contained.  The analytic Euler-form/support half is seam-coupled
(it depends on the concrete `fg_J` support of the GHS window decomposition, WAVE I-2);
see the executor NOTE. -/

/-- The `L0'` identity at the `ArithmeticFunction` level (the Dirichlet-ring unit form). -/
lemma ellLin_toAF_mul_inv :
    toArithmeticFunction (ellLin g) * toArithmeticFunction (ellLinInv g) = 1 := by
  apply DFunLike.coe_injective
  change ellLin g ⍟ ellLinInv g = ⇑(1 : ArithmeticFunction ℂ)
  rw [ellLin_mul_inv g]
  exact ArithmeticFunction.one_eq_delta.symm

/-- The prime datum restricted to primes above the smoothness cutoff `y`
(the `g·1_{p>y}` of the freeze). -/
noncomputable def restrictAbove (y : ℝ) (g : ℕ → ℂ) : ℕ → ℂ :=
  fun p => if y < (p : ℝ) then g p else 0

/-- The smooth part `sPart := fg_J ⍟ ℓ⁻¹(g·1_{p>y})` of the freeze. -/
noncomputable def smoothPart (y : ℝ) (g fg : ℕ → ℂ) : ℕ → ℂ :=
  fg ⍟ ellLinInv (restrictAbove y g)

/-- Backbone of the factorization: any Dirichlet coefficient function `fg` (with `fg 0 = 0`)
convolved with `ℓ⁻¹(d)` and then `ℓ(d)` returns `fg`, since `ℓ⁻¹(d) ⍟ ℓ(d) = δ` (`L0'`). -/
lemma conv_ellLinInv_ellLin {d fg : ℕ → ℂ} (hfg : fg 0 = 0) :
    (fg ⍟ ellLinInv d) ⍟ ellLin d = fg := by
  change ⇑(toArithmeticFunction (fg ⍟ ellLinInv d) * toArithmeticFunction (ellLin d)) = fg
  rw [show toArithmeticFunction (fg ⍟ ellLinInv d)
        = toArithmeticFunction fg * toArithmeticFunction (ellLinInv d) from
      ArithmeticFunction.toArithmeticFunction_eq_self _, mul_assoc,
    mul_comm (toArithmeticFunction (ellLinInv d)) (toArithmeticFunction (ellLin d)),
    ellLin_toAF_mul_inv, mul_one]
  funext n
  rw [toAF_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_pos rfl, hfg]
  · rw [if_neg hn]

/-- **L3' (freeze FILE B, factorization backbone).**  The frozen smooth-part shape
`fg_J = sPart ⍟ ℓ(g·1_{p>y})` with `sPart := fg_J ⍟ ℓ⁻¹(g·1_{p>y})`: the seam's
smoothing convolution is exactly inverted by `ℓ` above the cutoff, so it recovers `fg_J`.
A direct corollary of `L0'` (`ellLin_mul_inv`).  The analytic half of the contract (the
Euler-form `LSeries` bound with the explicit squarefull `C_sq`) is seam-coupled — see NOTE. -/
theorem smoothPart_factorization (y : ℝ) {fg : ℕ → ℂ} (hfg : fg 0 = 0) :
    smoothPart y g fg ⍟ ellLin (restrictAbove y g) = fg :=
  conv_ellLinInv_ellLin hfg

/-- **L3' — the explicit squarefull `C_sq` corner.**  The `p = 2`, `k → ∞` corner of the
squarefull Euler tail, `Σ_{k≥0} (k+1)·2^{−k c₀}`, is summable (an `O(1)` constant, value
`(1 − 2^{−c₀})^{−2}`) for every `c₀ > 0`.  This is the explicit constant the freeze
requires be carried, never silently absorbed. -/
theorem cSq_corner_summable {c₀ : ℝ} (hc : 0 < c₀) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * ((2 : ℝ) ^ (-c₀)) ^ k) := by
  have hr1 : ‖(2 : ℝ) ^ (-c₀)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1 : Summable (fun k : ℕ => (k : ℝ) * ((2 : ℝ) ^ (-c₀)) ^ k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr1
  have h2 : Summable (fun k : ℕ => ((2 : ℝ) ^ (-c₀)) ^ k) :=
    summable_geometric_of_norm_lt_one hr1
  simpa [add_mul, one_mul] using h1.add h2

end Salt.MR
