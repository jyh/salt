/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cCore

/-!
# The generic sign-function transfer chain (WALL-3, wave 1, node SignChain)

The sign-function re-typing of the Heath-Brown χ-twisted transfer surface: every
object of `Salt.HB.TwistChain`/`TwistChainC`/`Transfer`/`L2cCore` built from a real
quadratic Dirichlet character `χ` (`χ² = 1`, read through `chiRe`) is re-derived from
an arbitrary **real sign function** `f : ℕ → ℝ` carrying only the packet
`IsSignFunction f` — `f(1) = 1`, `f` totally multiplicative, `|f| ≤ 1`, and `f(p) = ±1`
at every prime.  No modulus `q` and no coprimality hypothesis appear: the sole consumer
of `(p, q) = 1` in the character chain was `chiRe_eq_one_or_neg_one`, replaced here
hypothesis-free by `IsSignFunction.prime_pm`.

The generic chain is the formal footing of the exchange-rate wall; `Salt.HB.SignLiouville`
instantiates it at the Liouville function `λ` (recovering `Λ̃_λ = Λ` exactly), and
`Salt.HB.SignRate` states the neutrality rate against it.

Single-writer file; it touches no landed file and is not yet in the `Salt.HB.All`
manifest.  It builds standalone via `Salt.HB.L2cCore`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace Salt.HB

variable {f : ℕ → ℝ} {n m p : ℕ}

/-! ## §0 — the sign-function packet -/

/-- W1 PACKET: replaces `χ : DirichletCharacter ℂ q` + `hsq : χ^2 = 1`; records
    `ℱ = f² = 1` at EVERY prime, with NO modulus. -/
structure IsSignFunction (f : ℕ → ℝ) : Prop where
  map_one    : f 1 = 1
  map_mul    : ∀ a b : ℕ, f (a * b) = f a * f b
  abs_le_one : ∀ n : ℕ, |f n| ≤ 1
  prime_pm   : ∀ p : ℕ, p.Prime → f p = 1 ∨ f p = -1

/-! ## §1 — the objects (generic mirrors of the paper §2–§3 defs) -/

/-- `f-sum` `∑_{d ∣ n} μ²(d)·f(d)` — mirror of `fChiSum` (TC:94). -/
noncomputable def fGenSum (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ d ∈ n.divisors, (μ d : ℝ) ^ 2 * f d

/-- `Λ̃_f(n) = ∑_{d ∣ n} μ²(d)·f(d)·log(n/d)` — mirror of `LamTilde` (TC:98-99); the
    `n / d` is ℕ-division cast to `ℝ`. -/
noncomputable def LamTildeGen (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (μ d : ℝ) ^ 2 * f d * Real.log ((n / d : ℕ) : ℝ)

/-- `μ²·f` as an `ArithmeticFunction ℝ` — mirror of `gChi` (TC:118). -/
noncomputable def gGen (f : ℕ → ℝ) : ArithmeticFunction ℝ := ⟨fun n => (μ n : ℝ) ^ 2 * f n, by simp⟩

@[simp] lemma gGen_apply (f : ℕ → ℝ) (n : ℕ) : gGen f n = (μ n : ℝ) ^ 2 * f n := rfl

/-- `f = ζ ∗ (μ²f)` — mirror of `fChiArith` (TC:136). -/
noncomputable def fGenArith (f : ℕ → ℝ) : ArithmeticFunction ℝ := ζ * gGen f

lemma fGenArith_apply (f : ℕ → ℝ) (n : ℕ) :
    fGenArith f n = ∑ d ∈ n.divisors, gGen f d := by rw [fGenArith, coe_zeta_mul_apply]

lemma fGenArith_eq_fGenSum (f : ℕ → ℝ) (n : ℕ) : fGenArith f n = fGenSum f n := by
  rw [fGenArith_apply]; rfl

open Classical in
/-- `n₊ = ∏_{p ∣ n, f(p) = 1} p^{v_p(n)}` — mirror of `nPlus` (TC:388). -/
noncomputable def nPlusGen (f : ℕ → ℝ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => f p = 1), p ^ (n.factorization p)

open Classical in
/-- `n₋ = ∏_{p ∣ n, f(p) = −1} p^{v_p(n)}` — mirror of `nMinus` (TC:393). -/
noncomputable def nMinusGen (f : ℕ → ℝ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => f p = -1), p ^ (n.factorization p)

/-- `S⁽²⁾_f = ∑_{n ∈ A} Λ̃_f(n)·Λ̃_f(n+2)` — mirror of `S2` (TR:179). -/
noncomputable def S2Gen (f : ℕ → ℝ) (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, LamTildeGen f n * LamTildeGen f (n + 2)

/-- The exact per-term transfer difference — mirror of `overshootExact` (LC:68). -/
noncomputable def overshootExactGen (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (LamTildeGen f n - Λ n) * LamTildeGen f (n + 2) + Λ n * (LamTildeGen f (n + 2) - Λ (n + 2))

open Classical in
/-- The pretense sum `∑_{p ≤ N, f(p) = 1} log p / p` — mirror of `PretenseSum` (TF:183-185). -/
noncomputable def PretenseSumGen (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ f p = 1), Real.log (p : ℝ) / p

open Classical in
/-- The honest small-prime modulus `∏_{p < z prime, f(p) ≠ −1} p` — mirror of
    `excPrimorial` (SW:72); the `q`-part is gone (no modulus exists). -/
noncomputable def excPrimorialGen (f : ℕ → ℝ) (z : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range z).filter (fun p => p.Prime ∧ f p ≠ -1), p

/-- The honest window `{n ∈ (x,2x] : (n(n+2), excPrimorialGen f z) = 1}` — mirror of
    `l2cWindow` (LC:159) with the `q`-part dropped. -/
noncomputable def l2cWindowGen (f : ℕ → ℝ) (z x : ℕ) : Finset ℕ :=
  (Finset.Ioc x (2 * x)).filter (fun n => Nat.Coprime (n * (n + 2)) (excPrimorialGen f z))

/-! ## §2 — multiplicativity and nonnegativity of `f`, `fGenArith` -/

/-- `f` is completely multiplicative on powers — mirror of `chiRe_pow` (TC:55). -/
lemma fGen_pow (hf : IsSignFunction f) (a k : ℕ) : f (a ^ k) = f a ^ k := by
  induction k with
  | zero => simp [hf.map_one]
  | succ k ih => rw [pow_succ, hf.map_mul, ih, pow_succ]

/-- `μ²·f` is multiplicative — mirror of `gChi_mult` (TC:181). -/
lemma gGen_mult (hf : IsSignFunction f) : (gGen f).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [hf.map_one], ?_⟩
  intro m n hm hn hmn
  have hmu : (μ (m * n) : ℤ) = μ m * μ n := isMultiplicative_moebius.map_mul_of_coprime hmn
  simp only [gGen_apply]
  rw [hf.map_mul, hmu]
  push_cast
  ring

/-- `f = ζ ∗ (μ²f)` is multiplicative — mirror of `fChiArith_mult` (TC:211). -/
lemma fGenArith_mult (hf : IsSignFunction f) : (fGenArith f).IsMultiplicative := by
  unfold fGenArith
  exact ArithmeticFunction.isMultiplicative_zeta.natCast.mul (gGen_mult hf)

/-- `f`'s local factor: `f(p^k) = [k < 2]·f(p)^k` — mirror of `gChi_primePow` (TC:239). -/
lemma gGen_primePow {p : ℕ} (hp : p.Prime) (hf : IsSignFunction f) (k : ℕ) :
    gGen f (p ^ k) = if k < 2 then (f p) ^ k else 0 := by
  rw [gGen_apply, moebius_sq_primePow hp, fGen_pow hf]
  by_cases h : k < 2 <;> simp [h]

/-- `fGenArith f (p^e) ≥ 0` — mirror of `fChiArith_primePow_nonneg` (TC:244). -/
lemma fGenArith_primePow_nonneg {p : ℕ} (hp : p.Prime) (hf : IsSignFunction f) (e : ℕ) :
    0 ≤ fGenArith f (p ^ e) := by
  rw [fGenArith_apply, Nat.sum_divisors_prime_pow hp]
  simp_rw [gGen_primePow hp hf]
  exact sum_ite_lt_pow_nonneg (hf.abs_le_one p) (e + 1) 2

/-- `fGenArith f ≥ 0` on all of `ℕ` — mirror of `fChiArith_nonneg` (TC:251). -/
lemma fGenArith_nonneg (hf : IsSignFunction f) (n : ℕ) : 0 ≤ fGenArith f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [(fGenArith_mult hf).multiplicative_factorization (fGenArith f) hn, Finsupp.prod]
    apply Finset.prod_nonneg
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)
    exact fGenArith_primePow_nonneg hpp hf _

/-! ## §3 — Lemma 1(a),(b) via the convolution identities -/

/-- `Λ̃_f` as the Dirichlet convolution `(μ²f) ∗ log` — mirror of `LamTilde_eq_conv`
    (TC:324).  Packet-free. -/
lemma LamTildeGen_eq_conv (f : ℕ → ℝ) (n : ℕ) :
    LamTildeGen f n = (gGen f * ArithmeticFunction.log) n := by
  rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => gGen f a * ArithmeticFunction.log b), LamTildeGen]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [gGen_apply, ArithmeticFunction.log_apply, mul_assoc]

/-- `(μ²f) ∗ log = fGenArith f ∗ Λ` — mirror of `gChi_mul_log` (TC:341). -/
lemma gGen_mul_log (f : ℕ → ℝ) :
    gGen f * ArithmeticFunction.log = fGenArith f * Λ := by
  rw [fGenArith, ← zeta_mul_vonMangoldt]; ring

/-- `Λ̃_f = fGenArith f ∗ Λ` at every argument — mirror of `LamTilde_eq_fChi_conv` (TC:351). -/
lemma LamTildeGen_eq_fGen_conv (f : ℕ → ℝ) (n : ℕ) :
    LamTildeGen f n = (fGenArith f * Λ) n := by rw [LamTildeGen_eq_conv, gGen_mul_log]

/-- **Lemma 1(b).** `Λ n ≤ Λ̃_f n` for every `n` — mirror of `vonMangoldt_le_LamTilde` (TC:368). -/
theorem vonMangoldt_le_LamTildeGen (hf : IsSignFunction f) (n : ℕ) : Λ n ≤ LamTildeGen f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LamTildeGen]
  · rw [LamTildeGen_eq_fGen_conv, ArithmeticFunction.mul_apply]
    have hmem : (1, n) ∈ n.divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, hn⟩
    have h1 : fGenArith f 1 = 1 := (fGenArith_mult hf).map_one
    calc Λ n = fGenArith f (1, n).1 * Λ (1, n).2 := by simp [h1]
      _ ≤ ∑ x ∈ n.divisorsAntidiagonal, fGenArith f x.1 * Λ x.2 :=
          Finset.single_le_sum
            (fun x _ => mul_nonneg (fGenArith_nonneg hf x.1) vonMangoldt_nonneg) hmem

/-! ## §4 — the `±` factorization -/

/-- **The `±` factorization.** For `n ≠ 0`, `n = n₊·n₋` — mirror of `eq_nPlus_mul_nMinus`
    (TC:408) with the coprimality hypothesis dropped: `prime_pm` supplies `f(p) = ±1` at
    every prime factor directly. -/
theorem eq_nPlusGen_mul_nMinusGen (hf : IsSignFunction f) (hn : n ≠ 0) :
    n = nPlusGen f n * nMinusGen f n := by
  classical
  have hself : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
  have hfeq : n.primeFactors.filter (fun p => ¬ f p = 1)
            = n.primeFactors.filter (fun p => f p = -1) := by
    apply Finset.filter_congr
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rcases hf.prime_pm p hpp with h1 | h1 <;> rw [h1] <;> norm_num
  rw [nPlusGen, nMinusGen, ← hfeq, Finset.prod_filter_mul_prod_filter_not, ← hself]

/-- **`n₊` and `n₋` are coprime** — mirror of `coprime_nPlus_nMinus` (TC:424).  Packet-free. -/
theorem coprime_nPlusGen_nMinusGen (f : ℕ → ℝ) (n : ℕ) :
    Nat.Coprime (nPlusGen f n) (nMinusGen f n) := by
  classical
  rw [nPlusGen, nMinusGen]
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro r hr
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hr)
  have hpr : p ≠ r := by
    rintro rfl
    have h1 : f p = 1 := (Finset.mem_filter.mp hp).2
    have h2 : f p = -1 := (Finset.mem_filter.mp hr).2
    rw [h1] at h2; norm_num at h2
  exact ((Nat.coprime_primes hpp hrp).mpr hpr).pow _ _

/-! ## §5 — the Lemma 1(c) helper block (TCC:43-221 mirrors) -/

/-- `fGenArith f (p^e) = 1 + f p` for `e ≥ 1` — mirror of `fChiArith_primePow_pos` (TCC:43). -/
lemma fGenArith_primePow_pos {p : ℕ} (hp : p.Prime) (hf : IsSignFunction f) {e : ℕ} (he : e ≠ 0) :
    fGenArith f (p ^ e) = 1 + f p := by
  rw [fGenArith_apply, Nat.sum_divisors_prime_pow hp]
  simp_rw [gGen_primePow hp hf]
  rw [← Finset.sum_filter]
  have hfilter : (range (e + 1)).filter (· < 2) = range 2 := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfilter, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]

/-- A prime `p` with `f(p) = −1` dividing `a ≠ 0` kills `fGenArith f a` — mirror of
    `fChiArith_eq_zero_of_dvd_neg` (TCC:55). -/
lemma fGenArith_eq_zero_of_dvd_neg {p a : ℕ} (hp : p.Prime) (hf : IsSignFunction f)
    (hneg : f p = -1) (hpa : p ∣ a) (ha : a ≠ 0) : fGenArith f a = 0 := by
  rw [(fGenArith_mult hf).multiplicative_factorization (fGenArith f) ha, Finsupp.prod]
  apply Finset.prod_eq_zero (i := p)
  · rw [Nat.support_factorization]; exact Nat.mem_primeFactors.mpr ⟨hp, hpa, ha⟩
  · have hvp : a.factorization p ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd hp ha hpa).ne'
    rw [fGenArith_primePow_pos hp hf hvp, hneg]; norm_num

/-- On an all-`f = 1` number, `fGenArith f = 2^ω` — mirror of `fChiArith_eq_two_pow` (TCC:67). -/
lemma fGenArith_eq_two_pow (hf : IsSignFunction f) (hn : n ≠ 0)
    (hall : ∀ p ∈ n.primeFactors, f p = 1) :
    fGenArith f n = (2 : ℝ) ^ n.primeFactors.card := by
  rw [(fGenArith_mult hf).multiplicative_factorization (fGenArith f) hn, Finsupp.prod]
  have hval : ∀ p ∈ n.factorization.support,
      fGenArith f (p ^ n.factorization p) = (2 : ℝ) := by
    intro p hps
    have hpf : p ∈ n.primeFactors := by rwa [Nat.support_factorization] at hps
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpf
    have hvp : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hps
    rw [fGenArith_primePow_pos hpp hf hvp, hall p hpf]; norm_num
  rw [Finset.prod_congr rfl hval, Finset.prod_const, Nat.support_factorization]

/-- The convolution reindexed over divisors — mirror of `LamTilde_eq_sum_div` (TCC:81). -/
lemma LamTildeGen_eq_sum_div (f : ℕ → ℝ) (n : ℕ) :
    LamTildeGen f n = ∑ a ∈ n.divisors, fGenArith f a * Λ (n / a) := by
  rw [LamTildeGen_eq_fGen_conv, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => fGenArith f a * Λ b)]

/-- Every prime dividing `n₊` has `f(p) = 1` — mirror of `nPlus_dvd_sign` (TCC:89). -/
lemma nPlusGen_dvd_sign {f : ℕ → ℝ} {n r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ nPlusGen f n) : f r = 1 := by
  classical
  rw [nPlusGen] at hdvd
  obtain ⟨p, hpf, hrp⟩ := (hr.prime.dvd_finsetProd_iff _).mp hdvd
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hpf)
  have hrpp : r = p := (Nat.prime_dvd_prime_iff_eq hr hpp).mp (hr.dvd_of_dvd_pow hrp)
  subst hrpp
  exact (Finset.mem_filter.mp hpf).2

/-- Every prime dividing `n₋` has `f(p) = −1` — mirror of `nMinus_dvd_sign` (TCC:100). -/
lemma nMinusGen_dvd_sign {f : ℕ → ℝ} {n r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ nMinusGen f n) : f r = -1 := by
  classical
  rw [nMinusGen] at hdvd
  obtain ⟨p, hpf, hrp⟩ := (hr.prime.dvd_finsetProd_iff _).mp hdvd
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hpf)
  have hrpp : r = p := (Nat.prime_dvd_prime_iff_eq hr hpp).mp (hr.dvd_of_dvd_pow hrp)
  subst hrpp
  exact (Finset.mem_filter.mp hpf).2

/-- The prime factors of `n₊` all have `f = 1` — mirror of `nPlus_sign` (TCC:111). -/
lemma nPlusGen_sign {f : ℕ → ℝ} {n p : ℕ} (hp : p ∈ (nPlusGen f n).primeFactors) :
    f p = 1 :=
  nPlusGen_dvd_sign (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-- `n₊` is positive — mirror of `nPlus_pos` (TCC:155). -/
lemma nPlusGen_pos (f : ℕ → ℝ) (n : ℕ) : 0 < nPlusGen f n := by
  classical
  rw [nPlusGen]; refine Finset.prod_pos fun p hp => ?_
  exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)).pos _

/-- `n₋` is positive — mirror of `nMinus_pos` (TCC:161). -/
lemma nMinusGen_pos (f : ℕ → ℝ) (n : ℕ) : 0 < nMinusGen f n := by
  classical
  rw [nMinusGen]; refine Finset.prod_pos fun p hp => ?_
  exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)).pos _

/-- **Reduction.** `Λ̃_f(n) = ∑_{a ∣ n₊} fGenArith f a·Λ(n/a)` — mirror of
    `LamTilde_eq_sum_nPlus` (TCC:121); coprimality dropped, `prime_pm` used hypothesis-free. -/
lemma LamTildeGen_eq_sum_nPlus (hf : IsSignFunction f) {n : ℕ} (hn : n ≠ 0) :
    LamTildeGen f n = ∑ a ∈ (nPlusGen f n).divisors, fGenArith f a * Λ (n / a) := by
  classical
  have hfact := eq_nPlusGen_mul_nMinusGen hf hn
  have hnp : nPlusGen f n ≠ 0 := by rintro h; rw [h, zero_mul] at hfact; exact hn hfact
  have hsub : (nPlusGen f n).divisors ⊆ n.divisors :=
    Nat.divisors_subset_of_dvd hn ⟨nMinusGen f n, hfact⟩
  rw [LamTildeGen_eq_sum_div]
  refine (Finset.sum_subset hsub ?_).symm
  intro a ha hanp
  suffices h0 : fGenArith f a = 0 by rw [h0, zero_mul]
  have han : a ∣ n := Nat.dvd_of_mem_divisors ha
  by_contra hne
  apply hanp
  have hsign : ∀ p, p.Prime → p ∣ a → f p = 1 := by
    intro p hp hpa
    rcases hf.prime_pm p hp with h1 | h1
    · exact h1
    · exact absurd (fGenArith_eq_zero_of_dvd_neg hp hf h1 hpa
        (Nat.pos_of_mem_divisors ha).ne') hne
  have hcopa : Nat.Coprime a (nMinusGen f n) := by
    by_contra hnc
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hnc
    have h1 := hsign p hp (hpg.trans (Nat.gcd_dvd_left _ _))
    have h2 := nMinusGen_dvd_sign hp (hpg.trans (Nat.gcd_dvd_right _ _))
    rw [h1] at h2; norm_num at h2
  have hdvd : a ∣ nPlusGen f n := hcopa.dvd_of_dvd_mul_right (hfact ▸ han)
  exact Nat.mem_divisors.mpr ⟨hdvd, hnp⟩

/-- For `a ∣ n₊`, `n / a = (n₊ / a)·n₋` — mirror of `nDiv_eq` (TCC:167), coprimality dropped. -/
lemma nDivGen_eq (hf : IsSignFunction f) {n : ℕ} (hn : n ≠ 0) {a : ℕ} (ha : a ∣ nPlusGen f n) :
    n / a = nPlusGen f n / a * nMinusGen f n := by
  have hfact := eq_nPlusGen_mul_nMinusGen hf hn
  have ha0 : a ≠ 0 := fun h => (nPlusGen_pos f n).ne' (Nat.eq_zero_of_zero_dvd (h ▸ ha))
  have hmul : n = nPlusGen f n / a * nMinusGen f n * a := by
    rw [mul_right_comm, Nat.div_mul_cancel ha]; exact hfact
  exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero ha0) hmul

/-- `n₋ ≠ 1` forces `fGenSum f n = 0` — mirror of `fChiSum_n_eq_zero` (TCC:184), coprimality
    dropped. -/
lemma fGenSum_n_eq_zero (hf : IsSignFunction f) (hn : n ≠ 0) (hM : nMinusGen f n ≠ 1) :
    fGenSum f n = 0 := by
  obtain ⟨p, hp, hpM⟩ := Nat.exists_prime_and_dvd hM
  have hMn : nMinusGen f n ∣ n :=
    ⟨nPlusGen f n, by rw [mul_comm]; exact eq_nPlusGen_mul_nMinusGen hf hn⟩
  rw [← fGenArith_eq_fGenSum]
  exact fGenArith_eq_zero_of_dvd_neg hp hf (nMinusGen_dvd_sign hp hpM) (hpM.trans hMn) hn

/-- `1 ≤ fGenSum f n₊` — mirror of `one_le_fChiSum_nPlus` (TCC:193). -/
lemma one_le_fGenSum_nPlus (hf : IsSignFunction f) (n : ℕ) : 1 ≤ fGenSum f (nPlusGen f n) := by
  rw [← fGenArith_eq_fGenSum,
      fGenArith_eq_two_pow hf (nPlusGen_pos f n).ne' (fun p hp => nPlusGen_sign hp)]
  exact one_le_pow₀ (by norm_num)

/-- `n₊ ≠ 1` forces `2 ≤ fGenSum f n₊` — mirror of `two_le_fChiSum_nPlus` (TCC:200). -/
lemma two_le_fGenSum_nPlus (hf : IsSignFunction f) {n : ℕ} (hP : nPlusGen f n ≠ 1) :
    2 ≤ fGenSum f (nPlusGen f n) := by
  rw [← fGenArith_eq_fGenSum,
      fGenArith_eq_two_pow hf (nPlusGen_pos f n).ne' (fun p hp => nPlusGen_sign hp)]
  have hcard : 1 ≤ (nPlusGen f n).primeFactors.card := by
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
    intro h; rcases Nat.primeFactors_eq_empty.mp h with h0 | h1
    · exact (nPlusGen_pos f n).ne' h0
    · exact hP h1
  calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (nPlusGen f n).primeFactors.card := pow_le_pow_right₀ (by norm_num) hcard

/-- Divisor-monotonicity of `fGenArith` on `f = 1` numbers — mirror of
    `fChiArith_le_of_dvd_nPlus` (TCC:213). -/
lemma fGenArith_le_of_dvd_nPlus (hf : IsSignFunction f) {n a : ℕ}
    (ha : a ∣ nPlusGen f n) : fGenArith f a ≤ fGenArith f (nPlusGen f n) := by
  have ha0 : a ≠ 0 := fun h => (nPlusGen_pos f n).ne' (Nat.eq_zero_of_zero_dvd (h ▸ ha))
  rw [fGenArith_eq_two_pow hf ha0 (fun p hp =>
        nPlusGen_dvd_sign (Nat.prime_of_mem_primeFactors hp)
          ((Nat.dvd_of_mem_primeFactors hp).trans ha)),
      fGenArith_eq_two_pow hf (nPlusGen_pos f n).ne' (fun p hp => nPlusGen_sign hp)]
  exact pow_le_pow_right₀ (by norm_num)
    (Finset.card_le_card (Nat.primeFactors_mono ha (nPlusGen_pos f n).ne'))

/-! ## §6 — the three cases on `ω(n₋)` and Lemma 1(c) (TCC:252-364 mirrors) -/

/-- **Case `ω(n₋) ≥ 2`.** `Λ̃_f(n) = 0` — mirror of `LamTilde_eq_zero_of_two_le_card`
    (TCC:252), coprimality dropped. -/
lemma LamTildeGen_eq_zero_of_two_le_card (hf : IsSignFunction f) (hn : n ≠ 0)
    (hM : 2 ≤ (nMinusGen f n).primeFactors.card) : LamTildeGen f n = 0 := by
  rw [LamTildeGen_eq_sum_nPlus hf hn]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hadvd : a ∣ nPlusGen f n := Nat.dvd_of_mem_divisors ha
  have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos hadvd (nPlusGen_pos f n)
  have hna : n / a = nPlusGen f n / a * nMinusGen f n := nDivGen_eq hf hn hadvd
  have hPa_pos : 0 < nPlusGen f n / a := Nat.div_pos (Nat.le_of_dvd (nPlusGen_pos f n) hadvd) ha_pos
  have hna0 : n / a ≠ 0 := by rw [hna]; exact Nat.mul_ne_zero hPa_pos.ne' (nMinusGen_pos f n).ne'
  have hMdvd : nMinusGen f n ∣ n / a := by rw [hna]; exact dvd_mul_left _ _
  have hnp : ¬ IsPrimePow (n / a) := not_isPrimePow_of_two_le_card hna0 hMdvd hM
  rw [vonMangoldt_eq_zero_iff.mpr hnp, mul_zero]

/-- **Case `ω(n₋) = 1`.** `Λ̃_f(n) = fGenSum f n₊·Λ(n₋)` — mirror of
    `LamTilde_eq_single_of_card_one` (TCC:268), coprimality dropped. -/
lemma LamTildeGen_eq_single_of_card_one (hf : IsSignFunction f) (hn : n ≠ 0)
    (hM : IsPrimePow (nMinusGen f n)) :
    LamTildeGen f n = fGenSum f (nPlusGen f n) * Λ (nMinusGen f n) := by
  rw [LamTildeGen_eq_sum_nPlus hf hn,
      Finset.sum_eq_single_of_mem (nPlusGen f n)
        (Nat.mem_divisors_self _ (nPlusGen_pos f n).ne') ?_]
  · rw [fGenArith_eq_fGenSum, nDivGen_eq hf hn dvd_rfl, Nat.div_self (nPlusGen_pos f n), one_mul]
  · intro a ha hane
    have hadvd : a ∣ nPlusGen f n := Nat.dvd_of_mem_divisors ha
    have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos hadvd (nPlusGen_pos f n)
    have hPa_pos : 0 < nPlusGen f n / a :=
      Nat.div_pos (Nat.le_of_dvd (nPlusGen_pos f n) hadvd) ha_pos
    have hPa1 : nPlusGen f n / a ≠ 1 := by
      intro h; apply hane
      have hh := Nat.mul_div_cancel' hadvd
      rw [h, mul_one] at hh; exact hh
    have hcopPaM : Nat.Coprime (nPlusGen f n / a) (nMinusGen f n) :=
      Nat.Coprime.coprime_dvd_left ⟨a, (Nat.div_mul_cancel hadvd).symm⟩
        (coprime_nPlusGen_nMinusGen f n)
    have hnp : ¬ IsPrimePow (n / a) := by
      rw [nDivGen_eq hf hn hadvd]
      exact not_isPrimePow_mul_coprime hcopPaM hPa1
        (fun h => not_isPrimePow_one (h ▸ hM)) hPa_pos.ne' (nMinusGen_pos f n).ne'
    rw [vonMangoldt_eq_zero_iff.mpr hnp, mul_zero]

/-- **Case `ω(n₋) = 0`.** The crude divisor-monotone bound `Λ̃_f(n) ≤ fGenSum f n·log n` —
    mirror of `LamTilde_le_of_nMinus_one` (TCC:293), coprimality dropped. -/
lemma LamTildeGen_le_of_nMinus_one (hf : IsSignFunction f) (hn : n ≠ 0)
    (hM : nMinusGen f n = 1) : LamTildeGen f n ≤ fGenSum f n * Real.log n := by
  have hPn : nPlusGen f n = n := by
    have h := eq_nPlusGen_mul_nMinusGen hf hn; rw [hM, mul_one] at h; exact h.symm
  rw [LamTildeGen_eq_sum_nPlus hf hn]
  calc ∑ a ∈ (nPlusGen f n).divisors, fGenArith f a * Λ (n / a)
      ≤ ∑ a ∈ (nPlusGen f n).divisors, fGenArith f (nPlusGen f n) * Λ (n / a) := by
        refine Finset.sum_le_sum fun a ha => ?_
        exact mul_le_mul_of_nonneg_right
          (fGenArith_le_of_dvd_nPlus hf (Nat.dvd_of_mem_divisors ha)) vonMangoldt_nonneg
    _ = fGenSum f n * Real.log n := by
        rw [← Finset.mul_sum, fGenArith_eq_fGenSum, hPn,
            Nat.sum_div_divisors n (fun d => Λ d), vonMangoldt_sum]

/-- **Lemma 1(c).** `Λ̃_f(n) − Λ(n) ≤ 2·(fGenSum f n·log n + (fGenSum f n₊ − 1)·Λ(n₋))` —
    mirror of `LamTilde_sub_vonMangoldt_le` (TCC:317), coprimality dropped. -/
theorem LamTildeGen_sub_vonMangoldt_le (hf : IsSignFunction f) (hn : n ≠ 0) :
    LamTildeGen f n - Λ n ≤
      2 * (fGenSum f n * Real.log n + (fGenSum f (nPlusGen f n) - 1) * Λ (nMinusGen f n)) := by
  have hlogn : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hFn_nonneg : 0 ≤ fGenSum f n := by
    rw [← fGenArith_eq_fGenSum]; exact fGenArith_nonneg hf n
  have hLM_nonneg : 0 ≤ Λ (nMinusGen f n) := vonMangoldt_nonneg
  have hLn_nonneg : 0 ≤ Λ n := vonMangoldt_nonneg
  have hFP1 : 0 ≤ fGenSum f (nPlusGen f n) - 1 := by linarith [one_le_fGenSum_nPlus hf n]
  have hR_nonneg : 0 ≤ 2 * (fGenSum f n * Real.log n
      + (fGenSum f (nPlusGen f n) - 1) * Λ (nMinusGen f n)) :=
    mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg hFn_nonneg hlogn) (mul_nonneg hFP1 hLM_nonneg))
  rcases lt_trichotomy (nMinusGen f n).primeFactors.card 1 with hc | hc | hc
  · have hcard0 : (nMinusGen f n).primeFactors.card = 0 := by omega
    have hM1 : nMinusGen f n = 1 := by
      rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hcard0) with h | h
      · exact absurd h (nMinusGen_pos f n).ne'
      · exact h
    rw [hM1, vonMangoldt_apply_one, mul_zero, add_zero]
    linarith [LamTildeGen_le_of_nMinus_one hf hn hM1, mul_nonneg hFn_nonneg hlogn]
  · have hM1 : IsPrimePow (nMinusGen f n) := isPrimePow_iff_card_primeFactors_eq_one.mpr hc
    have hMne1 : nMinusGen f n ≠ 1 := by intro h; rw [h] at hc; simp at hc
    have hLT := LamTildeGen_eq_single_of_card_one hf hn hM1
    by_cases hP1 : nPlusGen f n = 1
    · have hFP1' : fGenSum f (nPlusGen f n) = 1 := by
        rw [hP1, ← fGenArith_eq_fGenSum]; exact (fGenArith_mult hf).map_one
      have hnM : n = nMinusGen f n := by
        have h := eq_nPlusGen_mul_nMinusGen hf hn; rw [hP1, one_mul] at h; exact h
      have hLn : Λ n = Λ (nMinusGen f n) := by rw [← hnM]
      have hFn0 : fGenSum f n = 0 := fGenSum_n_eq_zero hf hn hMne1
      rw [hLT, hFP1', hLn, hFn0]
      exact le_of_eq (by ring)
    · have hFn0 : fGenSum f n = 0 := fGenSum_n_eq_zero hf hn hMne1
      have hLn0 : Λ n = 0 := by
        rw [vonMangoldt_eq_zero_iff, eq_nPlusGen_mul_nMinusGen hf hn]
        exact not_isPrimePow_mul_coprime (coprime_nPlusGen_nMinusGen f n) hP1 hMne1
          (nPlusGen_pos f n).ne' (nMinusGen_pos f n).ne'
      rw [hLT, hLn0, sub_zero, hFn0, zero_mul, zero_add]
      nlinarith [mul_nonneg (sub_nonneg.mpr (two_le_fGenSum_nPlus hf hP1)) hLM_nonneg,
        hLM_nonneg]
  · rw [LamTildeGen_eq_zero_of_two_le_card hf hn hc]
    linarith [hR_nonneg, hLn_nonneg]

/-! ## §7 — the transfer inequality `S⁽¹⁾ ≤ S⁽²⁾` (TR:143-192 mirrors) -/

/-- `Λ̃_f ≥ 0` everywhere — mirror of `LamTilde_nonneg` (TR:106). -/
lemma LamTildeGen_nonneg (hf : IsSignFunction f) (n : ℕ) : 0 ≤ LamTildeGen f n :=
  le_trans vonMangoldt_nonneg (vonMangoldt_le_LamTildeGen hf n)

/-- **Termwise nonnegativity** `Λ(n)Λ(n+2) ≤ Λ̃_f(n)Λ̃_f(n+2)` — mirror of
    `twin_termwise_nonneg` (TR:143). -/
lemma twin_termwise_nonnegGen (hf : IsSignFunction f) (n : ℕ) :
    Λ n * Λ (n + 2) ≤ LamTildeGen f n * LamTildeGen f (n + 2) := by
  have hid : LamTildeGen f n * LamTildeGen f (n + 2) - Λ n * Λ (n + 2)
      = (LamTildeGen f n - Λ n) * LamTildeGen f (n + 2)
        + Λ n * (LamTildeGen f (n + 2) - Λ (n + 2)) := by ring
  have h1 : 0 ≤ (LamTildeGen f n - Λ n) * LamTildeGen f (n + 2) :=
    mul_nonneg (by linarith [vonMangoldt_le_LamTildeGen hf n]) (LamTildeGen_nonneg hf (n + 2))
  have h2 : 0 ≤ Λ n * (LamTildeGen f (n + 2) - Λ (n + 2)) :=
    mul_nonneg vonMangoldt_nonneg (by linarith [vonMangoldt_le_LamTildeGen hf (n + 2)])
  linarith [hid, h1, h2]

/-- **Lemma 2, lower half.** `S⁽¹⁾ ≤ S⁽²⁾_f` — mirror of `S1_le_S2` (TR:189); `S1` (TR:176)
    is reused verbatim. -/
theorem S1_le_S2Gen (hf : IsSignFunction f) (A : Finset ℕ) : S1 A ≤ S2Gen f A := by
  unfold S1 S2Gen
  exact Finset.sum_le_sum fun n _ => twin_termwise_nonnegGen hf n

/-! ## §8 — the exact overshoot identity and vanishing/classification (LC:76-152 mirrors) -/

/-- **The exact ring identity.** `S⁽²⁾_f − S⁽¹⁾ = ∑_{n∈A} overshootExactGen f n` — mirror of
    `S2_sub_S1_eq` (LC:76).  Packet-free. -/
theorem S2Gen_sub_S1_eq (f : ℕ → ℝ) (A : Finset ℕ) :
    S2Gen f A - S1 A = ∑ n ∈ A, overshootExactGen f n := by
  unfold S2Gen S1 overshootExactGen
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Vanishing at primes** — mirror of `lamTilde_sub_vonMangoldt_eq_zero_of_prime` (LC:89). -/
lemma lamTildeGen_sub_eq_zero_of_prime (hf : IsSignFunction f) {p : ℕ} (hp : p.Prime) :
    LamTildeGen f p - Λ p = 0 := by
  have h1 : LamTildeGen f p = Λ p := by
    rw [LamTildeGen_eq_sum_div, hp.divisors, Finset.sum_pair hp.one_lt.ne,
        Nat.div_one, Nat.div_self hp.pos, vonMangoldt_apply_one, mul_zero, add_zero,
        (fGenArith_mult hf).map_one, one_mul]
  rw [h1, sub_self]

/-- **Vanishing at `1`** — mirror of `lamTilde_sub_vonMangoldt_eq_zero_of_one` (LC:98).
    Packet-free. -/
lemma lamTildeGen_sub_eq_zero_of_one (f : ℕ → ℝ) : LamTildeGen f 1 - Λ 1 = 0 := by
  have h1 : LamTildeGen f 1 = 0 := by
    rw [LamTildeGen_eq_sum_div, Nat.divisors_one, Finset.sum_singleton, Nat.div_one,
        vonMangoldt_apply_one, mul_zero]
  rw [h1, vonMangoldt_apply_one, sub_self]

/-- **Vanishing on the pure `f = −1` part** — mirror of
    `lamTilde_sub_vonMangoldt_eq_zero_of_pure_minus` (LC:107), coprimality dropped. -/
lemma lamTildeGen_sub_eq_zero_of_pure_minus (hf : IsSignFunction f) (hn : n ≠ 0)
    (hP1 : nPlusGen f n = 1) (hM : IsPrimePow (nMinusGen f n)) : LamTildeGen f n - Λ n = 0 := by
  have hnM : n = nMinusGen f n := by
    have h := eq_nPlusGen_mul_nMinusGen hf hn; rw [hP1, one_mul] at h; exact h
  have hf1 : fGenSum f (nPlusGen f n) = 1 := by
    rw [hP1, ← fGenArith_eq_fGenSum]; exact (fGenArith_mult hf).map_one
  rw [LamTildeGen_eq_single_of_card_one hf hn hM, hf1, one_mul, ← hnM, sub_self]

/-- **Vanishing when `ω(n₋) ≥ 2`** — mirror of
    `lamTilde_sub_vonMangoldt_eq_zero_of_two_le_card` (LC:118), coprimality dropped. -/
lemma lamTildeGen_sub_eq_zero_of_two_le_card (hf : IsSignFunction f) (hn : n ≠ 0)
    (hM : 2 ≤ (nMinusGen f n).primeFactors.card) : LamTildeGen f n - Λ n = 0 := by
  have hLt : LamTildeGen f n = 0 := LamTildeGen_eq_zero_of_two_le_card hf hn hM
  have hMdvd : nMinusGen f n ∣ n :=
    ⟨nPlusGen f n, by rw [mul_comm]; exact eq_nPlusGen_mul_nMinusGen hf hn⟩
  have hnp : ¬ IsPrimePow n := not_isPrimePow_of_two_le_card hn hMdvd hM
  rw [hLt, vonMangoldt_eq_zero_iff.mpr hnp, sub_self]

/-- **Support classification of `Λ̃_f − Λ`** — mirror of `lamTilde_sub_support_classification`
    (LC:130), coprimality dropped. -/
lemma lamTildeGen_sub_support_classification (hf : IsSignFunction f) (hn : n ≠ 0)
    (hne : LamTildeGen f n - Λ n ≠ 0) :
    ¬ n.Prime ∧ n ≠ 1 ∧
      (nMinusGen f n = 1 ∨ (IsPrimePow (nMinusGen f n) ∧ 1 < nPlusGen f n)) := by
  refine ⟨fun hp => hne (lamTildeGen_sub_eq_zero_of_prime hf hp), ?_, ?_⟩
  · rintro rfl; exact hne (lamTildeGen_sub_eq_zero_of_one f)
  · by_contra hcon
    have hM1 : nMinusGen f n ≠ 1 := fun h => hcon (Or.inl h)
    have hcon2 : IsPrimePow (nMinusGen f n) → nPlusGen f n ≤ 1 := fun hpp => by
      by_contra hlt; exact hcon (Or.inr ⟨hpp, by omega⟩)
    by_cases hpp : IsPrimePow (nMinusGen f n)
    · have hle := hcon2 hpp
      have hP1 : nPlusGen f n = 1 := by have := nPlusGen_pos f n; omega
      exact hne (lamTildeGen_sub_eq_zero_of_pure_minus hf hn hP1 hpp)
    · have hcard : 2 ≤ (nMinusGen f n).primeFactors.card := by
        rcases Nat.lt_trichotomy (nMinusGen f n).primeFactors.card 1 with h | h | h
        · have hc0 : (nMinusGen f n).primeFactors.card = 0 := by omega
          rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hc0) with h0 | h1
          · exact absurd h0 (nMinusGen_pos f n).ne'
          · exact absurd h1 hM1
        · exact absurd (isPrimePow_iff_card_primeFactors_eq_one.mpr h) hpp
        · omega
      exact hne (lamTildeGen_sub_eq_zero_of_two_le_card hf hn hcard)

/-! ## §9 — the honest window roughness and the caps (LC:180-271 mirrors) -/

/-- **Window roughness.** Every `f ≠ −1` prime of `n(n+2)` for `n` in the window is `≥ z`
    — mirror of `l2cWindow_roughness` (LC:180); `q` dropped, so the `excPrimorialGen`
    coprimality is read directly off window membership.  Packet-free. -/
lemma l2cWindowGen_roughness {z x : ℕ} (hn : n ∈ l2cWindowGen f z x) (hp : p.Prime)
    (hpd : p ∣ n * (n + 2)) (hf1 : f p ≠ -1) : z ≤ p := by
  by_contra hlt
  have hpz : p < z := not_le.mp hlt
  simp only [l2cWindowGen, Finset.mem_filter] at hn
  have hcop : Nat.Coprime (n * (n + 2)) (excPrimorialGen f z) := hn.2
  have hmem : p ∈ (Finset.range z).filter (fun p => p.Prime ∧ f p ≠ -1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpz, hp, hf1⟩
  have hdvdP : p ∣ excPrimorialGen f z := Finset.dvd_prod_of_mem _ hmem
  have hgcd : p ∣ Nat.gcd (n * (n + 2)) (excPrimorialGen f z) := Nat.dvd_gcd hpd hdvdP
  have hc1 : Nat.gcd (n * (n + 2)) (excPrimorialGen f z) = 1 := hcop
  rw [hc1] at hgcd
  exact hp.ne_one (Nat.dvd_one.mp hgcd)

/-- **The `ω(m₊)` cap.** `2^{ω(m₊)} ≤ e^{(log 2)·z₀}` — mirror of `omega_cap` (LC:196),
    coprimality dropped. -/
lemma omega_capGen (hf : IsSignFunction f) (z x : ℕ) (hz2 : 2 ≤ z) (hm0 : m ≠ 0)
    (hmle : m ≤ 2 * x + 2) (hrough : ∀ p ∈ (nPlusGen f m).primeFactors, z ≤ p) :
    (2 : ℝ) ^ (nPlusGen f m).primeFactors.card ≤ Real.exp (Real.log 2 * z0 z x) := by
  have hzR : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hlogz : 0 < Real.log z := Real.log_pos hzR
  have hmP_dvd : nPlusGen f m ∣ m := ⟨nMinusGen f m, eq_nPlusGen_mul_nMinusGen hf hm0⟩
  have hmP_le : nPlusGen f m ≤ 2 * x + 2 :=
    le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hmP_dvd) hmle
  have hrad_le : (∏ p ∈ (nPlusGen f m).primeFactors, p) ≤ nPlusGen f m :=
    Nat.le_of_dvd (nPlusGen_pos f m) (Nat.prod_primeFactors_dvd _)
  have hzc_pos : (0 : ℝ) < (z : ℝ) ^ (nPlusGen f m).primeFactors.card :=
    pow_pos (by exact_mod_cast (by omega : 0 < z)) _
  have hzc_le : (z : ℝ) ^ (nPlusGen f m).primeFactors.card ≤ 2 * (x : ℝ) + 2 := by
    calc (z : ℝ) ^ (nPlusGen f m).primeFactors.card
        = ∏ _p ∈ (nPlusGen f m).primeFactors, (z : ℝ) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ (nPlusGen f m).primeFactors, (p : ℝ) :=
          Finset.prod_le_prod (fun p _ => by positivity)
            (fun p hp => by exact_mod_cast hrough p hp)
      _ ≤ 2 * (x : ℝ) + 2 := by rw [← Nat.cast_prod]; exact_mod_cast le_trans hrad_le hmP_le
  have hc_le : ((nPlusGen f m).primeFactors.card : ℝ) ≤ z0 z x := by
    rw [z0, le_div_iff₀ hlogz, Lwin, ← Real.log_pow]
    exact Real.log_le_log hzc_pos hzc_le
  rw [show (2 : ℝ) ^ (nPlusGen f m).primeFactors.card
      = Real.exp (((nPlusGen f m).primeFactors.card : ℝ) * Real.log 2) from by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]]
  refine Real.exp_le_exp.mpr ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left hc_le (Real.log_nonneg (by norm_num))

/-- **The `Λ̃_f` cap.** On a window element `m`, `Λ̃_f(m) ≤ e^{(log 2)·z₀}·L'` — mirror of
    `lamTilde_cap` (LC:227), coprimality dropped. -/
lemma lamTildeGen_cap (hf : IsSignFunction f) (z x : ℕ) (hz2 : 2 ≤ z) (hm0 : m ≠ 0)
    (hmle : m ≤ 2 * x + 2) (hrough : ∀ p, p.Prime → p ∣ m → f p ≠ -1 → z ≤ p) :
    LamTildeGen f m ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x := by
  have hmP_dvd : nPlusGen f m ∣ m := ⟨nMinusGen f m, eq_nPlusGen_mul_nMinusGen hf hm0⟩
  have hroughP : ∀ p ∈ (nPlusGen f m).primeFactors, z ≤ p := fun p hp =>
    hrough p (Nat.prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hmP_dvd) (by rw [nPlusGen_sign hp]; norm_num)
  have hcap := omega_capGen hf z x hz2 hm0 hmle hroughP
  have hexp0 : 0 ≤ Real.exp (Real.log 2 * z0 z x) := (Real.exp_pos _).le
  have hfP : fGenSum f (nPlusGen f m) = (2 : ℝ) ^ (nPlusGen f m).primeFactors.card := by
    rw [← fGenArith_eq_fGenSum]
    exact fGenArith_eq_two_pow hf (nPlusGen_pos f m).ne' (fun p hp => nPlusGen_sign hp)
  have hlogm_le : Real.log m ≤ Lwin x := by
    rw [Lwin]
    exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hm0) (by exact_mod_cast hmle)
  rcases lt_trichotomy (nMinusGen f m).primeFactors.card 1 with hc | hc | hc
  · have hM1 : nMinusGen f m = 1 := by
      have hc0 : (nMinusGen f m).primeFactors.card = 0 := by omega
      rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hc0) with h0 | h1
      · exact absurd h0 (nMinusGen_pos f m).ne'
      · exact h1
    have hPm : nPlusGen f m = m := by
      have h := eq_nPlusGen_mul_nMinusGen hf hm0; rw [hM1, mul_one] at h; exact h.symm
    calc LamTildeGen f m ≤ fGenSum f m * Real.log m := LamTildeGen_le_of_nMinus_one hf hm0 hM1
      _ = fGenSum f (nPlusGen f m) * Real.log m := by rw [hPm]
      _ = (2 : ℝ) ^ (nPlusGen f m).primeFactors.card * Real.log m := by rw [hfP]
      _ ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x := mul_le_mul hcap hlogm_le
          (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0)) hexp0
  · have hM1 : IsPrimePow (nMinusGen f m) := isPrimePow_iff_card_primeFactors_eq_one.mpr hc
    have hMdvd : nMinusGen f m ∣ m :=
      ⟨nPlusGen f m, by rw [mul_comm]; exact eq_nPlusGen_mul_nMinusGen hf hm0⟩
    have hMle : nMinusGen f m ≤ 2 * x + 2 :=
      le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hMdvd) hmle
    have hLamM : Λ (nMinusGen f m) ≤ Lwin x := by
      rw [Lwin]
      exact le_trans vonMangoldt_le_log
        (Real.log_le_log (by exact_mod_cast nMinusGen_pos f m) (by exact_mod_cast hMle))
    calc LamTildeGen f m = fGenSum f (nPlusGen f m) * Λ (nMinusGen f m) :=
          LamTildeGen_eq_single_of_card_one hf hm0 hM1
      _ = (2 : ℝ) ^ (nPlusGen f m).primeFactors.card * Λ (nMinusGen f m) := by rw [hfP]
      _ ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x :=
          mul_le_mul hcap hLamM vonMangoldt_nonneg hexp0
  · rw [LamTildeGen_eq_zero_of_two_le_card hf hm0 hc]
    exact mul_nonneg hexp0 (Lwin_nonneg x)

/-! ## §10 — the `f = 1` prime counters (LC:372-434 mirrors, packet-free) -/

/-- **The `PretenseSum` conversion.** `∑_{z≤p≤N, f=1} 1/p ≤ PretenseSumGen f N / log z` —
    mirror of `sum_inv_plusprime_le_pretense` (LC:372).  Packet-free. -/
lemma sum_inv_plusprime_le_pretenseGen (f : ℕ → ℝ) (z N : ℕ) (hz : 1 < z) :
    (∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ f p = 1 ∧ z ≤ p),
        (1 : ℝ) / p)
      ≤ PretenseSumGen f N / Real.log z := by
  have hlogz : 0 < Real.log z := Real.log_pos (by exact_mod_cast hz)
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  rw [le_div_iff₀ hlogz, Finset.sum_mul, PretenseSumGen]
  refine le_trans (Finset.sum_le_sum ?_) (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨_, hpp, _, hzp⟩ := hp
    have hlogzp : Real.log z ≤ Real.log p := Real.log_le_log hz0 (by exact_mod_cast hzp)
    calc (1 : ℝ) / p * Real.log z = Real.log z * (1 / p) := by ring
      _ ≤ Real.log p * (1 / p) := mul_le_mul_of_nonneg_right hlogzp (by positivity)
      _ = Real.log p / p := by ring
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  · intro p hp _
    rw [Finset.mem_filter] at hp
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)) (by positivity)

/-- **The Chebyshev-`f` count.** `#{p ∈ (a,b], prime, f=1} ≤ (b/log a)·PretenseSumGen f N` —
    mirror of `chebyshev_chi_count` (LC:396).  Packet-free. -/
lemma chebyshev_chi_countGen (f : ℕ → ℝ) {a b N : ℕ} (ha : 1 < a) (hbN : b ≤ N) :
    (((Finset.Ioc a b).filter (fun p => Nat.Prime p ∧ f p = 1)).card : ℝ)
      ≤ ((b : ℝ) / Real.log a) * PretenseSumGen f N := by
  have hloga : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha)
  have hcard : (((Finset.Ioc a b).filter (fun p => Nat.Prime p ∧ f p = 1)).card : ℝ)
      = ∑ _p ∈ (Finset.Ioc a b).filter (fun p => Nat.Prime p ∧ f p = 1), (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard]
  calc (∑ _p ∈ (Finset.Ioc a b).filter (fun p => Nat.Prime p ∧ f p = 1), (1 : ℝ))
      ≤ ∑ p ∈ (Finset.Ioc a b).filter (fun p => Nat.Prime p ∧ f p = 1),
          ((b : ℝ) / Real.log a) * (Real.log p / p) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter, Finset.mem_Ioc] at hp
        obtain ⟨⟨hap, hpb⟩, hpp, _⟩ := hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hap' : (a : ℝ) ≤ p := by exact_mod_cast (by omega : a ≤ p)
        have hlogap : Real.log a ≤ Real.log p :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < a)) hap'
        have e1 : (1 : ℝ) ≤ Real.log p / Real.log a := (one_le_div hloga).mpr hlogap
        have e2 : (1 : ℝ) ≤ (b : ℝ) / p := (one_le_div hp0).mpr (by exact_mod_cast hpb)
        calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ (b : ℝ) / p * (Real.log p / Real.log a) :=
              mul_le_mul e2 e1 (by norm_num) (by positivity)
          _ = (b : ℝ) / Real.log a * (Real.log p / p) := by ring
    _ = ((b : ℝ) / Real.log a) * ∑ p ∈ (Finset.Ioc a b).filter
          (fun p => Nat.Prime p ∧ f p = 1), (Real.log p / p) := by rw [Finset.mul_sum]
    _ ≤ ((b : ℝ) / Real.log a) * PretenseSumGen f N := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (Nat.cast_nonneg b) hloga.le)
        rw [PretenseSumGen]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_filter, Finset.mem_Ioc] at hp
          rw [Finset.mem_filter, Finset.mem_range]
          obtain ⟨⟨hap, hpb⟩, hpp, hchi⟩ := hp
          exact ⟨by omega, hpp, hchi⟩
        · intro p hp _
          rw [Finset.mem_filter] at hp
          exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)) (by positivity)

end Salt.HB
