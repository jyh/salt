/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.PseudoChar

/-!
# B2 W4 — Jutila's Lemma 1 (L1′): the twisted Euler product and the detection identity (2.2)

For `Re s > 1`, a square-free level `t` and a multiplicative `f`,
`Σ_n χ(n) f_t(n) n^{−s} = L(s,χ)·∏_{p ∣ t}(1 + (f(p) − 1)χ(p)p^{−s})` (the local factor
`jutilaLocal`), and with it Lemma 1's (2.2), p.48:
`L(s,χ)·M(s,χ,f_r) = Σ_n (Σ_{d∣n} ξ_d) χ(n) f_r(n) n^{−s}`, where `M` (`jutilaM`) is (2.1) with
`ξ` supported on `[1, Z]` — a FINITE Dirichlet polynomial. Both are `LSeries` identities;
`LFunction χ s = LSeries (χ ·) s` on `Re s > 1` is mathlib's `LFunction_eq_LSeries`. The
`r`-summed form of (2.2) over a finite set of square-free levels, with the per-level
summability it needs, is what Lemma 6 (W7) consumes directly.

## The honest label

Every row here is an INPUT to Lemma 6, which is NOT in this file: nothing below bears on twin
primes or on the crown's conditions. The coefficients are ℝ-valued (`pseudoChar`, `selbergPsi`)
and cast to ℂ once, at the point of use — the corpus's idiom, and the reason every row carries
its casts explicitly. Two things Lemma 6 also needs are its OWN and are NOT here: the bound
`|bvWeight z₁ z₂ d| ≤ 1` on the mollifier weight, and the contour node (the removable
singularity at `w = 0`, Cauchy–Goursat on the whole integrand, integrability on
`Re w = 1/2 − β`). Mathlib's Euler product for Dirichlet L-series is NOT consumed: the twisted
product is proved by a prime-peeling induction over `t.primeFactors`, so no infinite product
and no convergence of one ever enters.

## Why `Squarefree t` is load-bearing on the twisted product

At `t = 4` the identity is FALSE, and not marginally: `f_4(n) = ψ(gcd(4, n))` takes the value
`ψ(4) = 0` on `4 ∣ n`, which the local factor `1 + (ψ(2) − 1)χ(2)2^{−s}` cannot see (it would
need a `p²` term). Measured at `s = 2 + 0.6i` for a character mod 5: the series is
`0.8326 − 0.2842i` against `L·(1 + (ψ(2) − 1)χ(2)2^{−s}) = 0.8830 − 0.3235i` — the two differ
in the SECOND significant digit, `|diff| = 6.4e−2`. The square-freeness enters through
`pseudoChar_mul_of_squarefree` and through `Nat.prod_primeFactors_of_squarefree`.

## The measured receipts behind these statements

For a character mod 5 with `χ(2) = i`, at `s = 2 + 0.6i`, sums to `2·10⁵`: the twisted product
at `t = 6` gives `1.148503 − 0.156896i` on both sides to 6 digits; (2.2) at `r = 6`,
`ξ = bvWeight 4 16`, `Z = 16` gives `0.993775 + 0.013490i` on both sides to 6 digits; and the
`r`-summed form over `S = {1, 2, 3, 6}` agrees to `3.9e−11`. The coefficient values seen at the
object are `a(1) = 1`, `a(2) = a(3) = a(4) = 0` (W6a's two divisor identities), `a(5) = 0.1610`.
-/

open ArithmeticFunction DirichletCharacter

noncomputable section
namespace Salt.SW

variable {q : ℕ}

/-- The local factor of (2.1): `∏_{p ∣ t} (1 + (f(p) − 1) χ(p) p^{−s})`. -/
def jutilaLocal (f : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) (t : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ t.primeFactors, (1 + (((f p : ℝ) : ℂ) - 1) * χ p * (p : ℂ) ^ (-s))

/-- The mollifier (2.1) with coefficients `ξ` supported on `[1, Z]`:
`M(s,χ,f_r) = Σ_{d ≤ Z} ξ_d χ(d) f_r(d) d^{−s} ∏_{p ∣ r/(r,d)} (1 + (f(p) − 1)χ(p)p^{−s})`. -/
def jutilaM (ξ : ℕ → ℝ) (Z : ℕ) (f : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q)
    (r : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Z, ((ξ d : ℝ) : ℂ) * χ d * ((pseudoChar f r d : ℝ) : ℂ) * (d : ℂ) ^ (-s)
    * jutilaLocal f χ (r / Nat.gcd r d) s

variable {f : ArithmeticFunction ℝ} (χ : DirichletCharacter ℂ q)

theorem jutilaLocal_one (f : ArithmeticFunction ℝ) (s : ℂ) : jutilaLocal f χ 1 s = 1 := by
  simp only [jutilaLocal, Nat.primeFactors_one, Finset.prod_empty]

theorem jutilaLocal_prime (f : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    jutilaLocal f χ p s = 1 + (((f p : ℝ) : ℂ) - 1) * χ p * (p : ℂ) ^ (-s) := by
  simp only [jutilaLocal, hp.primeFactors, Finset.prod_singleton]

theorem jutilaLocal_mul_of_coprime (f : ArithmeticFunction ℝ) {t₁ t₂ : ℕ}
    (h : Nat.Coprime t₁ t₂) (s : ℂ) :
    jutilaLocal f χ (t₁ * t₂) s = jutilaLocal f χ t₁ s * jutilaLocal f χ t₂ s := by
  simp only [jutilaLocal, h.primeFactors_mul]
  exact Finset.prod_union h.disjoint_primeFactors

theorem norm_jutilaLocal_le (f : ArithmeticFunction ℝ) (t : ℕ) (s : ℂ) :
    ‖jutilaLocal f χ t s‖ ≤ ∏ p ∈ t.primeFactors, (1 + |f p - 1| * (p : ℝ) ^ (-s.re)) := by
  rw [jutilaLocal, Complex.norm_prod]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) (fun p hp => ?_)
  have hppos : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
  have hcast : ((f p : ℝ) : ℂ) - 1 = ((f p - 1 : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hppos, Complex.neg_re]
  have hchi : ‖χ (p : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hrpow : (0 : ℝ) ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg hp0.le _
  calc ‖1 + (((f p : ℝ) : ℂ) - 1) * χ p * (p : ℂ) ^ (-s)‖
      ≤ ‖(1 : ℂ)‖ + ‖(((f p : ℝ) : ℂ) - 1) * χ p * (p : ℂ) ^ (-s)‖ := norm_add_le _ _
    _ = 1 + |f p - 1| * ‖χ (p : ZMod q)‖ * (p : ℝ) ^ (-s.re) := by
          rw [norm_one, norm_mul, norm_mul, hcast, Complex.norm_real, Real.norm_eq_abs, hnorm]
    _ ≤ 1 + |f p - 1| * (p : ℝ) ^ (-s.re) := by
          have hkey : |f p - 1| * (p : ℝ) ^ (-s.re) * (1 - ‖χ (p : ZMod q)‖) ≥ 0 :=
            mul_nonneg (mul_nonneg (abs_nonneg _) hrpow) (by linarith)
          nlinarith [hkey]

theorem LSeries_dvd_mul_eq (a : ℕ → ℂ) {d : ℕ} (hd : d ≠ 0) (s : ℂ) :
    LSeries (fun n => if d ∣ n then a n else 0) s
      = (d : ℂ) ^ (-s) * LSeries (fun m => a (d * m)) s := by
  have hinj : Function.Injective (fun m : ℕ => d * m) := fun x y hxy =>
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) hxy
  have hsupp : Function.support (LSeries.term (fun n => if d ∣ n then a n else 0) s)
      ⊆ Set.range (fun m : ℕ => d * m) := by
    refine Function.support_subset_iff'.mpr (fun n hn => ?_)
    rcases eq_or_ne n 0 with rfl | hn0
    · exact LSeries.term_zero _ _
    · have hnd : ¬ d ∣ n := fun hdvd => hn ⟨n / d, Nat.mul_div_cancel' hdvd⟩
      rw [LSeries.term_of_ne_zero hn0, if_neg hnd, zero_div]
  have hstep : ∀ m : ℕ, LSeries.term (fun n => if d ∣ n then a n else 0) s (d * m)
      = (d : ℂ) ^ (-s) * LSeries.term (fun m => a (d * m)) s m := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm0
    · rw [Nat.mul_zero, LSeries.term_zero, LSeries.term_zero, mul_zero]
    · have hdm : d * m ≠ 0 := Nat.mul_ne_zero hd hm0
      rw [LSeries.term_of_ne_zero hdm, LSeries.term_of_ne_zero hm0, if_pos (dvd_mul_right d m),
        Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      simp only [Complex.cpow_neg, div_eq_mul_inv, mul_inv]
      ring
  calc LSeries (fun n => if d ∣ n then a n else 0) s
      = ∑' n : ℕ, LSeries.term (fun n => if d ∣ n then a n else 0) s n := rfl
    _ = ∑' m : ℕ, LSeries.term (fun n => if d ∣ n then a n else 0) s (d * m) :=
        (hinj.tsum_eq hsupp).symm
    _ = ∑' m : ℕ, (d : ℂ) ^ (-s) * LSeries.term (fun m => a (d * m)) s m := tsum_congr hstep
    _ = (d : ℂ) ^ (-s) * ∑' m : ℕ, LSeries.term (fun m => a (d * m)) s m := tsum_mul_left
    _ = (d : ℂ) ^ (-s) * LSeries (fun m => a (d * m)) s := rfl

/-- The pointwise size of a twisted pseudocharacter coefficient: `‖χ(n)·f_t(n)‖ ≤ |f_t(n)|`,
since `‖χ(n)‖ ≤ 1`. The one input both summability rows below share. -/
private theorem norm_pseudoChar_twist_le (f : ArithmeticFunction ℝ) (t n : ℕ) :
    ‖(χ n : ℂ) * ((pseudoChar f t n : ℝ) : ℂ)‖ ≤ |pseudoChar f t n| := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖χ (n : ZMod q)‖ * |pseudoChar f t n|
      ≤ 1 * |pseudoChar f t n| :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (abs_nonneg _)
    _ = |pseudoChar f t n| := one_mul _

theorem LSeriesSummable_pseudoChar_twist (f : ArithmeticFunction ℝ) {t : ℕ} (ht : t ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => χ n * ((pseudoChar f t n : ℝ) : ℂ)) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := ∑ e ∈ t.divisors, |f e|)
    (fun n _ => (norm_pseudoChar_twist_le χ f t n).trans
      (abs_pseudoChar_le_sum_divisors ht n)) hs

/-- The same series with the coefficient killed off the multiples of `d`: still summable, by
the same bound (the discarded terms are `0`). -/
private theorem LSeriesSummable_pseudoChar_twist_dvd (f : ArithmeticFunction ℝ) {t : ℕ}
    (ht : t ≠ 0) (d : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (fun n => if d ∣ n then (χ n : ℂ) * ((pseudoChar f t n : ℝ) : ℂ) else 0) s := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := ∑ e ∈ t.divisors, |f e|)
    (fun n _ => ?_) hs
  by_cases hdn : d ∣ n
  · rw [if_pos hdn]
    exact (norm_pseudoChar_twist_le χ f t n).trans (abs_pseudoChar_le_sum_divisors ht n)
  · rw [if_neg hdn, norm_zero]
    exact Finset.sum_nonneg (fun e _ => abs_nonneg _)

/-- **The prime-peeling induction** behind `LSeries_pseudoChar_twist_eq`, staged as its own
lemma over a `Finset` of primes (the freeze's route: the level is `∏ p ∈ S, p`, and one prime
is peeled at each step through `pseudoChar_mul_left_of_coprime` and `pseudoChar_prime_left`).
The reindex `Σ_{p ∣ n} = p^{−s}·Σ_m` is the single helper `LSeries_dvd_mul_eq`. -/
private theorem LSeries_pseudoChar_prod_eq [NeZero q] (hf : f.IsMultiplicative) {s : ℂ}
    (hs : 1 < s.re) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    LSeries (fun n => (χ n : ℂ) * ((pseudoChar f (∏ p ∈ S, p) n : ℝ) : ℂ)) s
      = LFunction χ s * ∏ p ∈ S, (1 + (((f p : ℝ) : ℂ) - 1) * χ p * (p : ℂ) ^ (-s)) := by
  induction S using Finset.induction_on with
  | empty =>
      have hfun : (fun n : ℕ => (χ n : ℂ)
            * ((pseudoChar f (∏ p ∈ (∅ : Finset ℕ), p) n : ℝ) : ℂ))
          = fun n : ℕ => (χ n : ℂ) := by
        funext n
        rw [Finset.prod_empty, pseudoChar_one_left hf n]
        push_cast
        ring
      rw [hfun, Finset.prod_empty, mul_one, LFunction_eq_LSeries χ hs]
  | @insert p S hpS ih =>
      have hp : p.Prime := hS p (Finset.mem_insert_self p S)
      have hSp : ∀ x ∈ S, x.Prime := fun x hx => hS x (Finset.mem_insert_of_mem hx)
      have hcop : Nat.Coprime p (∏ x ∈ S, x) :=
        Nat.coprime_prod_right_iff.mpr (fun x hx =>
          (Nat.coprime_primes hp (hSp x hx)).mpr (fun hpx => hpS (by rw [hpx]; exact hx)))
      have hTne : (∏ x ∈ S, x) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun x hx => (hSp x hx).ne_zero)
      have hfun : (fun n : ℕ => (χ n : ℂ)
            * ((pseudoChar f (∏ x ∈ insert p S, x) n : ℝ) : ℂ))
          = (fun n : ℕ => (χ n : ℂ) * ((pseudoChar f (∏ x ∈ S, x) n : ℝ) : ℂ))
            + (((f p : ℝ) : ℂ) - 1) •
              (fun n : ℕ => if p ∣ n then (χ n : ℂ)
                * ((pseudoChar f (∏ x ∈ S, x) n : ℝ) : ℂ) else 0) := by
        funext n
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.prod_insert hpS,
          pseudoChar_mul_left_of_coprime hf hcop n, pseudoChar_prime_left hf hp n]
        by_cases hpn : p ∣ n
        · rw [if_pos hpn, if_pos hpn]
          push_cast
          ring
        · rw [if_neg hpn, if_neg hpn]
          push_cast
          ring
      have hsumF : LSeriesSummable
          (fun n : ℕ => (χ n : ℂ) * ((pseudoChar f (∏ x ∈ S, x) n : ℝ) : ℂ)) s :=
        LSeriesSummable_pseudoChar_twist χ f hTne hs
      have hsumG : LSeriesSummable
          (fun n : ℕ => if p ∣ n then (χ n : ℂ)
            * ((pseudoChar f (∏ x ∈ S, x) n : ℝ) : ℂ) else 0) s :=
        LSeriesSummable_pseudoChar_twist_dvd χ f hTne p hs
      have hG : LSeries (fun n : ℕ => if p ∣ n then (χ n : ℂ)
            * ((pseudoChar f (∏ x ∈ S, x) n : ℝ) : ℂ) else 0) s
          = (p : ℂ) ^ (-s) * ((χ p : ℂ) * LSeries
              (fun n : ℕ => (χ n : ℂ) * ((pseudoChar f (∏ x ∈ S, x) n : ℝ) : ℂ)) s) := by
        rw [LSeries_dvd_mul_eq (fun n : ℕ => (χ n : ℂ)
          * ((pseudoChar f (∏ x ∈ S, x) n : ℝ) : ℂ)) hp.ne_zero s]
        congr 1
        rw [← LSeries_smul]
        congr 1
        funext m
        simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, map_mul, pseudoChar]
        rw [Nat.Coprime.gcd_mul_left_cancel_right m hcop]
        ring
      rw [hfun, LSeries_add hsumF (hsumG.smul (((f p : ℝ) : ℂ) - 1)), LSeries_smul, hG,
        ih hSp, Finset.prod_insert hpS]
      ring

theorem LSeries_pseudoChar_twist_eq [NeZero q] (hf : f.IsMultiplicative) {t : ℕ}
    (ht : Squarefree t) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => χ n * ((pseudoChar f t n : ℝ) : ℂ)) s
      = LFunction χ s * jutilaLocal f χ t s := by
  have key := LSeries_pseudoChar_prod_eq χ hf hs t.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [Nat.prod_primeFactors_of_squarefree ht] at key
  rw [key, jutilaLocal]

/-- The divisor sum of a `[1, Z]`-supported `ξ`, written as a sum over the FIXED range
`Icc 1 Z` with a divisibility detector — the step that turns (2.2)'s coefficient into a finite
Dirichlet polynomial. -/
private theorem sum_divisors_eq_sum_Icc_ite (ξ : ℕ → ℝ) (Z : ℕ) (hξ : ∀ d, Z < d → ξ d = 0)
    {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, ξ d = ∑ d ∈ Finset.Icc 1 Z, if d ∣ n then ξ d else 0 := by
  rw [← Finset.sum_filter]
  refine (Finset.sum_subset (fun d hd => ?_) (fun d hd hd' => ?_)).symm
  · have hd' := Finset.mem_filter.mp hd
    exact Nat.mem_divisors.mpr ⟨hd'.2, hn⟩
  · have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hZ : Z < d := by
      by_contra hcon
      exact hd' (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, not_lt.mp hcon⟩, hdvd⟩)
    exact hξ d hZ

theorem LSeries_jutila_coeff_eq [NeZero q] (hf : f.IsMultiplicative) {r : ℕ} (hr : Squarefree r)
    (ξ : ℕ → ℝ) (Z : ℕ) (hξ : ∀ d, Z < d → ξ d = 0) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((∑ d ∈ n.divisors, ξ d : ℝ) : ℂ) * χ n * ((pseudoChar f r n : ℝ) : ℂ)) s
      = LFunction χ s * jutilaM ξ Z f χ r s := by
  have hcong : LSeries (fun n => ((∑ d ∈ n.divisors, ξ d : ℝ) : ℂ) * χ n
        * ((pseudoChar f r n : ℝ) : ℂ)) s
      = LSeries (∑ d ∈ Finset.Icc 1 Z, fun n : ℕ =>
          if d ∣ n then ((ξ d : ℝ) : ℂ) * χ n * ((pseudoChar f r n : ℝ) : ℂ) else 0) s := by
    refine LSeries_congr (fun {n} hn => ?_) s
    have hs1 : ((∑ d ∈ n.divisors, ξ d : ℝ) : ℂ)
        = ∑ d ∈ Finset.Icc 1 Z, (if d ∣ n then ((ξ d : ℝ) : ℂ) else 0) := by
      rw [sum_divisors_eq_sum_Icc_ite ξ Z hξ hn, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      by_cases hdn : d ∣ n
      · simp only [if_pos hdn]
      · simp only [if_neg hdn, Complex.ofReal_zero]
    rw [Finset.sum_apply, hs1, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases hdn : d ∣ n
    · simp only [if_pos hdn]
    · simp only [if_neg hdn, zero_mul]
  have hsummable : ∀ d ∈ Finset.Icc 1 Z, LSeriesSummable
      (fun n : ℕ => if d ∣ n then ((ξ d : ℝ) : ℂ) * χ n
        * ((pseudoChar f r n : ℝ) : ℂ) else 0) s := by
    intro d _
    refine LSeriesSummable_of_bounded_of_one_lt_re
      (m := |ξ d| * ∑ e ∈ r.divisors, |f e|) (fun n _ => ?_) hs
    by_cases hdn : d ∣ n
    · rw [if_pos hdn, mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        ((norm_pseudoChar_twist_le χ f r n).trans
          (abs_pseudoChar_le_sum_divisors hr.ne_zero n)) (abs_nonneg _)
    · rw [if_neg hdn, norm_zero]
      exact mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun e _ => abs_nonneg _))
  rw [hcong, LSeries_sum hsummable, jutilaM, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hd0 : d ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hd).1
  have hsq : Squarefree (r / Nat.gcd r d) :=
    Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r d)) hr
  rw [LSeries_dvd_mul_eq (fun n : ℕ => ((ξ d : ℝ) : ℂ) * χ n
    * ((pseudoChar f r n : ℝ) : ℂ)) hd0 s]
  have hshift : (fun m : ℕ => ((ξ d : ℝ) : ℂ) * χ ((d * m : ℕ))
        * ((pseudoChar f r (d * m) : ℝ) : ℂ))
      = (((ξ d : ℝ) : ℂ) * χ d * ((pseudoChar f r d : ℝ) : ℂ)) •
        (fun m : ℕ => (χ m : ℂ) * ((pseudoChar f (r / Nat.gcd r d) m : ℝ) : ℂ)) := by
    funext m
    simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, map_mul,
      pseudoChar_mul_of_squarefree hf hr d m]
    push_cast
    ring
  rw [hshift, LSeries_smul, LSeries_pseudoChar_twist_eq χ hf hsq hs]
  ring

/-- **The W4 exit row**, (2.2) at `r = 1`: the pseudocharacter is identically `1`
(`pseudoChar_one_left`) and every local factor collapses (`jutilaLocal_one`), so `M` is the bare
Dirichlet polynomial `Σ_{d ≤ Z} ξ_d χ(d) d^{−s}`. Measured: the coefficient values `a(1) = 1`,
`a(2) = a(3) = a(4) = 0` for `ξ = bvWeight 4 16`. -/
example [NeZero q] (hf : f.IsMultiplicative) (ξ : ℕ → ℝ) (Z : ℕ)
    (hξ : ∀ d, Z < d → ξ d = 0) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((∑ d ∈ n.divisors, ξ d : ℝ) : ℂ) * χ n) s
      = LFunction χ s * ∑ d ∈ Finset.Icc 1 Z, ((ξ d : ℝ) : ℂ) * χ d * (d : ℂ) ^ (-s) := by
  simpa [pseudoChar_one_left hf, jutilaM, jutilaLocal_one] using
    LSeries_jutila_coeff_eq χ hf (r := 1) squarefree_one ξ Z hξ hs

/-- `|Σ_{d ∣ n} ξ_d| ≤ Σ_{d ≤ Z} |ξ_d|` for `n ≠ 0`: the uniform bound behind
`LSeriesSummable_jutila_coeff`. -/
private theorem abs_sum_divisors_le (ξ : ℕ → ℝ) (Z : ℕ) (hξ : ∀ d, Z < d → ξ d = 0)
    {n : ℕ} (hn : n ≠ 0) :
    |∑ d ∈ n.divisors, ξ d| ≤ ∑ d ∈ Finset.Icc 1 Z, |ξ d| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [sum_divisors_eq_sum_Icc_ite (fun d => |ξ d|) Z (fun d hd => by rw [hξ d hd, abs_zero]) hn]
  refine Finset.sum_le_sum (fun d _ => ?_)
  by_cases hdn : d ∣ n
  · rw [if_pos hdn]
  · rw [if_neg hdn]
    exact abs_nonneg _

theorem LSeriesSummable_jutila_coeff (f : ArithmeticFunction ℝ) {r : ℕ} (hr : r ≠ 0)
    (ξ : ℕ → ℝ) (Z : ℕ) (hξ : ∀ d, Z < d → ξ d = 0) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (fun n => ((∑ d ∈ n.divisors, ξ d : ℝ) : ℂ) * χ n * ((pseudoChar f r n : ℝ) : ℂ)) s := by
  refine LSeriesSummable_of_bounded_of_one_lt_re
    (m := (∑ d ∈ Finset.Icc 1 Z, |ξ d|) * ∑ e ∈ r.divisors, |f e|) (fun n hn => ?_) hs
  rw [mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (abs_sum_divisors_le ξ Z hξ hn)
    ((norm_pseudoChar_twist_le χ f r n).trans (abs_pseudoChar_le_sum_divisors hr n))
    (norm_nonneg _) (Finset.sum_nonneg (fun d _ => abs_nonneg _))

theorem LSeries_jutila_coeff_sum_eq [NeZero q] (hf : f.IsMultiplicative) (S : Finset ℕ)
    (hS : ∀ r ∈ S, Squarefree r) (ξ : ℕ → ℝ) (Z : ℕ) (hξ : ∀ d, Z < d → ξ d = 0) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n => ((∑ d ∈ n.divisors, ξ d : ℝ) : ℂ) * χ n
        * ((∑ r ∈ S, (r : ℝ)⁻¹ * pseudoChar f r n : ℝ) : ℂ)) s
      = LFunction χ s * ∑ r ∈ S, ((r : ℝ)⁻¹ : ℂ) * jutilaM ξ Z f χ r s := by
  have hfun : (fun n : ℕ => ((∑ d ∈ n.divisors, ξ d : ℝ) : ℂ) * χ n
        * ((∑ r ∈ S, (r : ℝ)⁻¹ * pseudoChar f r n : ℝ) : ℂ))
      = ∑ r ∈ S, ((r : ℝ)⁻¹ : ℂ) •
          (fun n : ℕ => ((∑ d ∈ n.divisors, ξ d : ℝ) : ℂ) * χ n
            * ((pseudoChar f r n : ℝ) : ℂ)) := by
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  have hsum : ∀ r ∈ S, LSeriesSummable
      (((r : ℝ)⁻¹ : ℂ) •
        (fun n : ℕ => ((∑ d ∈ n.divisors, ξ d : ℝ) : ℂ) * χ n
          * ((pseudoChar f r n : ℝ) : ℂ))) s :=
    fun r hr =>
      (LSeriesSummable_jutila_coeff χ f (hS r hr).ne_zero ξ Z hξ hs).smul (((r : ℝ)⁻¹ : ℂ))
  rw [hfun, LSeries_sum hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [LSeries_smul, LSeries_jutila_coeff_eq χ hf (hS r hr) ξ Z hξ hs]
  ring

end Salt.SW
