/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHBal2

/-!
# The Selberg-weight re-founding (`T-BAL` R0) — the weight-generic detector family

Design: the JYH-ratified **T-BAL S₀ synthesis freeze**
(`docs/exploration/tbal-s0-freeze.md`, the 5th design — support-native with the
Selberg-optimal weights). This module re-founds the DH product detector on a
GENERIC real weight `λ : ℕ → ℝ` (the `*W` family), beside the retained
`grahamTheta`/`dhCoeff` (both kept for existing consumers — no removals), and
supplies the exact Selberg local factors `h`, `g`, `H` and the Selberg-optimal
weight `selWeight` (Benli–Goel–Twiss–Zaman (4.8), `arXiv:2410.06082`).

## The `*W` family (generic weight `λ`)

* `dhWeightSqW λ n = (Σ_{d ∣ n} λ d)²`     — the squared divisor-collected weight;
* `gcW λ m = lambdaSquared λ m`            — its lcm-collected pair coefficient
  (mathlib's Selberg `Λ²`), and
* `dhCoeffW χ λ n = dhA χ n · dhWeightSqW λ n` — the generic detector coefficient.

## The six generic-`λ` ports (kernel-verified here)

* **floor** `dhWeightSqW_one`, `dhCoeffW_one` — the `n = 1` seam `(λ 1)²`;
* **regroup** `dhWeightSqW_eq_sum_gcW` — `(Σ_{d∣n} λ_d)² = Σ_{m∣n} gcW λ m`
  (the classical Selberg `λ²`-regroup, ported from `grahamW_eq_sum_grahamGc`);
* **`|gcW| ≤ 3^ω`** `abs_gcW_le` — the lcm-pair count bound (`Nat.card_pair_lcm_eq`),
  for a squarefree-supported `λ` with `|λ_d| ≤ 1`;
* **the `k = 12` moment** `sum_abs_gcW_sigmaSq_div_le` — `Σ |gcW|·σ₀²/m ≤ (1+log M)¹²`
  (`|gcW|·σ₀² ≤ 3^ω·4^ω = 12^ω`, via the landed `tau6W_le`);
* **cpow-reality** `norm_dhCoeffW_term` — the per-term norm identity (`n^{-ρ}` twist
  contributes only `n^{-Re ρ}`), ported from `norm_dhDetectorShift_term`;
* **`dhCoeff_nonneg`** `dhCoeffW_nonneg` — `0 ≤ dhCoeffW` for real `χ`.

## The Selberg local factors and `selWeight` (defs; properties are R4/R5)

* `selH χ p = 1 + χ_ℝ(p) − χ_ℝ(p)/p ∈ (0,2]` (the exact local residue density,
  `selH_pos`/`selH_le_two`/`selH_lt_of_prime`);
* `selG χ p = selH χ p / (p − selH χ p) > 0` (`selG_pos`) and its multiplicative
  extension `selGmul`, `selHmul`;
* `selHSum χ z = Σ_{r ≤ z, sqfree} g(r)` (the freeze's `H(z) = Σ μ²·g`); and
* `selWeight χ z d` (Benli (4.8) in the freeze `g`-convention, `g = 1/g_Benli`):
  `μ(d)·h(d)·g(d)/H(z)·Σ_{r ≤ z/d, (r,d)=1, sqfree} g(r)`, validated by
  `selWeight_apply_one = 1`. The optimality (`selberg_opt_eq`), `selweight_abs_le_one`
  and the mean lower bound `H_lower` are R4/R5 (wave 2) — this module only DEFINES
  the weight and proves the `h`-range.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open Complex

noncomputable section

namespace Salt.SW

open Finset BoundingSieve
open ArithmeticFunction
open scoped ArithmeticFunction.omega

/-! ## §1 — the generic `*W` weight family -/

/-- **The generic squared divisor-sum weight** `w_λ(n) = (Σ_{d ∣ n} λ_d)²`. The support
structure lives entirely in `λ`; `grahamTheta`'s `dhWeightSq` is the case `λ = grahamTheta z`. -/
def dhWeightSqW (lam : ℕ → ℝ) (n : ℕ) : ℝ := (∑ d ∈ n.divisors, lam d) ^ 2

@[simp] lemma dhWeightSqW_nonneg (lam : ℕ → ℝ) (n : ℕ) : 0 ≤ dhWeightSqW lam n := sq_nonneg _

/-- **Floor port (weight side).** `w_λ(1) = (λ 1)²` (the divisors of `1` are `{1}`). -/
lemma dhWeightSqW_one (lam : ℕ → ℝ) : dhWeightSqW lam 1 = (lam 1) ^ 2 := by
  rw [dhWeightSqW, Nat.divisors_one, Finset.sum_singleton]

/-- **The lcm-collected pair coefficient** `gc_λ(m) = Σ_{lcm(d,e)=m} λ_d λ_e`, i.e. mathlib's
Selberg `Λ²` coefficient of the weight `λ`. `grahamGc z = gcW (grahamTheta z)`. -/
def gcW (lam : ℕ → ℝ) (m : ℕ) : ℝ := lambdaSquared lam m

/-- Unfolded form of `gcW` as the guarded lcm pair-sum over `m.divisors`. -/
lemma gcW_eq (lam : ℕ → ℝ) (m : ℕ) :
    gcW lam m = ∑ d1 ∈ m.divisors, ∑ d2 ∈ m.divisors,
      if m = Nat.lcm d1 d2 then lam d1 * lam d2 else 0 := by
  simp only [gcW, lambdaSquared]

/-- **The generic detector coefficient** `a_λ(n) = dhA χ n · w_λ(n)`. `dhCoeff χ z = dhCoeffW χ
(grahamTheta z)`; the retained `dhCoeff` stays for existing consumers. -/
def dhCoeffW {q : ℕ} (χ : DirichletCharacter ℂ q) (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  dhA χ n * dhWeightSqW lam n

/-- **Floor port (coefficient side).** `a_λ(1) = (λ 1)²` (`dhA χ 1 = 1`). -/
lemma dhCoeffW_one {q : ℕ} (χ : DirichletCharacter ℂ q) (lam : ℕ → ℝ) :
    dhCoeffW χ lam 1 = (lam 1) ^ 2 := by
  rw [dhCoeffW, dhA_one, dhWeightSqW_one, one_mul]

/-- **`dhCoeff_nonneg` port.** For real `χ` (`χ² = 1`) and `n ≠ 0`, `0 ≤ a_λ(n)`
(`dhA ≥ 0`, `w_λ ≥ 0`). -/
lemma dhCoeffW_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (lam : ℕ → ℝ)
    {n : ℕ} (hn : n ≠ 0) : 0 ≤ dhCoeffW χ lam n :=
  mul_nonneg (dhA_nonneg χ hsq hn) (dhWeightSqW_nonneg lam n)

/-! ## §2 — the regroup port `w_λ(n) = Σ_{m ∣ n} gcW λ m` -/

/-- **Regroup port.** For every `n`, `(Σ_{d ∣ n} λ_d)² = Σ_{m ∣ n} gcW λ m` — the classical
Selberg `λ²`-regroup by `m = lcm(d,e)`. Ported from `grahamW_eq_sum_grahamGc`. -/
theorem dhWeightSqW_eq_sum_gcW (lam : ℕ → ℝ) (n : ℕ) :
    dhWeightSqW lam n = ∑ m ∈ n.divisors, gcW lam m := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [dhWeightSqW, gcW, lambdaSquared]
  have hexpand_m : ∀ m ∈ n.divisors, gcW lam m
      = ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
          if m = Nat.lcm d1 d2 then lam d1 * lam d2 else 0 := by
    intro m hm
    have hmn : m ∣ n := Nat.dvd_of_mem_divisors hm
    have hm0 : m ≠ 0 := (Nat.pos_of_mem_divisors hm).ne'
    have hsub : m.divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd hn hmn
    have hinner : ∀ d1 : ℕ,
        (∑ d2 ∈ m.divisors, if m = Nat.lcm d1 d2 then lam d1 * lam d2 else 0)
          = ∑ d2 ∈ n.divisors, if m = Nat.lcm d1 d2 then lam d1 * lam d2 else 0 := by
      intro d1
      refine Finset.sum_subset hsub (fun d2 _ hd2m => ?_)
      rw [if_neg]
      intro heq
      exact hd2m (Nat.mem_divisors.mpr ⟨by rw [heq]; exact Nat.dvd_lcm_right d1 d2, hm0⟩)
    rw [gcW_eq]
    trans (∑ d1 ∈ m.divisors, ∑ d2 ∈ n.divisors,
        if m = Nat.lcm d1 d2 then lam d1 * lam d2 else 0)
    · exact Finset.sum_congr rfl (fun d1 _ => hinner d1)
    · refine Finset.sum_subset hsub (fun d1 _ hd1m => ?_)
      refine Finset.sum_eq_zero (fun d2 _ => ?_)
      rw [if_neg]
      intro heq
      exact hd1m (Nat.mem_divisors.mpr ⟨by rw [heq]; exact Nat.dvd_lcm_left d1 d2, hm0⟩)
  have key : ∑ m ∈ n.divisors, gcW lam m
      = ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, lam d1 * lam d2 := by
    calc ∑ m ∈ n.divisors, gcW lam m
        = ∑ m ∈ n.divisors, ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
            if m = Nat.lcm d1 d2 then lam d1 * lam d2 else 0 :=
          Finset.sum_congr rfl hexpand_m
      _ = ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, ∑ m ∈ n.divisors,
            if m = Nat.lcm d1 d2 then lam d1 * lam d2 else 0 := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun d1 _ => Finset.sum_comm)
      _ = ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, lam d1 * lam d2 := by
          refine Finset.sum_congr rfl (fun d1 hd1 => Finset.sum_congr rfl (fun d2 hd2 => ?_))
          rw [Finset.sum_ite_eq', if_pos]
          exact Nat.mem_divisors.mpr
            ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd1) (Nat.dvd_of_mem_divisors hd2), hn⟩
  rw [dhWeightSqW, sq, Finset.sum_mul_sum, key]

/-! ## §3 — the coefficient bounds `|gcW| ≤ 3^ω` and the `k = 12` moment -/

/-- `gcW λ m = 0` off squarefree `m`, when `λ` is squarefree-supported (`λ_d ≠ 0 ⟹ d` sqfree).
Every nonzero pair `λ_d λ_e` forces `d, e` squarefree, whence `lcm(d,e) = m` is squarefree. -/
theorem gcW_eq_zero_of_not_squarefree {lam : ℕ → ℝ}
    (hlamsf : ∀ d, lam d ≠ 0 → Squarefree d) {m : ℕ} (hm : ¬ Squarefree m) :
    gcW lam m = 0 := by
  rw [gcW_eq]
  refine Finset.sum_eq_zero (fun d1 _ => Finset.sum_eq_zero (fun d2 _ => ?_))
  split_ifs with heq
  · by_contra hne
    have h1 : lam d1 ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have h2 : lam d2 ≠ 0 := fun h => hne (by rw [h, mul_zero])
    exact hm (by rw [heq]; exact squarefree_lcm (hlamsf d1 h1) (hlamsf d2 h2))
  · rfl

/-- **`|gcW| ≤ 3^ω` port.** For a squarefree-supported `λ` with `|λ_d| ≤ 1`,
`|gcW λ m| ≤ 3^ω(m)`: bound each `|λ_d λ_e| ≤ 1` and count the lcm-pairs
(`Nat.card_pair_lcm_eq`); off squarefree `m`, `gcW = 0`. Ported from `abs_grahamGc_le`. -/
theorem abs_gcW_le {lam : ℕ → ℝ} (hlam1 : ∀ d, |lam d| ≤ 1)
    (hlamsf : ∀ d, lam d ≠ 0 → Squarefree d) (m : ℕ) :
    |gcW lam m| ≤ (3 : ℝ) ^ ω m := by
  by_cases hsf : Squarefree m
  · rw [gcW_eq]
    calc |∑ d1 ∈ m.divisors, ∑ d2 ∈ m.divisors,
            if m = Nat.lcm d1 d2 then lam d1 * lam d2 else 0|
        ≤ ∑ d1 ∈ m.divisors, |∑ d2 ∈ m.divisors,
            if m = Nat.lcm d1 d2 then lam d1 * lam d2 else 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d1 ∈ m.divisors, ∑ d2 ∈ m.divisors,
            |if m = Nat.lcm d1 d2 then lam d1 * lam d2 else 0| := by
          gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d1 ∈ m.divisors, ∑ d2 ∈ m.divisors, if m = Nat.lcm d1 d2 then (1 : ℝ) else 0 := by
          gcongr with d1 _ d2 _
          rw [apply_ite abs, abs_zero]
          split_ifs with h
          · rw [abs_mul]
            exact mul_le_one₀ (hlam1 d1) (abs_nonneg _) (hlam1 d2)
          · exact le_rfl
      _ = ∑ p ∈ m.divisors ×ˢ m.divisors, if m = Nat.lcm p.1 p.2 then (1 : ℝ) else 0 := by
          rw [← Finset.sum_product']
      _ = (((m.divisors ×ˢ m.divisors).filter fun p : ℕ × ℕ => m = Nat.lcm p.1 p.2).card : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const, Nat.smul_one_eq_cast]
      _ = (((m.divisors ×ˢ m.divisors).filter fun p : ℕ × ℕ => p.1.lcm p.2 = m).card : ℝ) := by
          norm_cast; congr 1; ext p; simp only [Finset.mem_filter, eq_comm]
      _ = (3 : ℝ) ^ ω m := by rw [Nat.card_pair_lcm_eq hsf]; push_cast; ring
  · rw [gcW_eq_zero_of_not_squarefree hlamsf hsf, abs_zero]; positivity

/-- **The `k = 12` moment port.** For a squarefree-supported `λ` with `|λ_d| ≤ 1`,
`Σ_{m ≤ M} |gcW λ m|·σ₀(m)²/m ≤ (1 + log M)¹²`. On the squarefree support
`|gcW|·σ₀² ≤ 3^ω·4^ω = 12^ω`; apply the landed `tau6W_le` at `k = 12`.
Ported from `sum_abs_grahamGc_sigmaSq_div_le`. -/
lemma sum_abs_gcW_sigmaSq_div_le {lam : ℕ → ℝ} (hlam1 : ∀ d, |lam d| ≤ 1)
    (hlamsf : ∀ d, lam d ≠ 0 → Squarefree d) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, |gcW lam m| * ((m.divisors.card : ℝ) ^ 2) / (m : ℝ)
      ≤ (1 + Real.log M) ^ 12 := by
  have hcond : ∀ m ∈ Finset.Icc 1 M,
      |gcW lam m| * ((m.divisors.card : ℝ) ^ 2) / (m : ℝ) ≠ 0 → Squarefree m := by
    intro m _ hne
    by_contra hnsf
    exact hne (by rw [gcW_eq_zero_of_not_squarefree hlamsf hnsf, abs_zero, zero_mul, zero_div])
  have key : ∑ m ∈ Finset.Icc 1 M, |gcW lam m| * ((m.divisors.card : ℝ) ^ 2) / (m : ℝ)
      ≤ ∑ d ∈ (Finset.Icc 1 M).filter Squarefree,
          ((12 : ℕ) : ℝ) ^ (d.primeFactors.card) / (d : ℝ) := by
    rw [← Finset.sum_filter_of_ne hcond]
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, _⟩, hsf⟩ := hm
    have hω : ω m = m.primeFactors.card := by
      rw [ArithmeticFunction.cardDistinctFactors_apply]; exact (List.card_toFinset _).symm
    have hgc : |gcW lam m| ≤ (3 : ℝ) ^ (m.primeFactors.card) := by
      have h := abs_gcW_le hlam1 hlamsf m; rwa [hω] at h
    have hcard : ((m.divisors.card : ℝ) ^ 2) = (4 : ℝ) ^ (m.primeFactors.card) := by
      rw [sqfree_card_divisors hsf]; push_cast; rw [pow_two, ← mul_pow]; norm_num
    have hbd : |gcW lam m| * ((m.divisors.card : ℝ) ^ 2)
        ≤ ((12 : ℕ) : ℝ) ^ (m.primeFactors.card) := by
      calc |gcW lam m| * ((m.divisors.card : ℝ) ^ 2)
          ≤ (3 : ℝ) ^ (m.primeFactors.card) * (4 : ℝ) ^ (m.primeFactors.card) :=
            mul_le_mul hgc (le_of_eq hcard) (by positivity) (by positivity)
        _ = ((12 : ℕ) : ℝ) ^ (m.primeFactors.card) := by rw [← mul_pow]; norm_num
    exact div_le_div_of_nonneg_right hbd (by positivity : (0 : ℝ) ≤ (m : ℝ))
  exact le_trans key (Salt.HardyLittlewood.tau6W_le M 12)

/-! ## §4 — the cpow-reality port -/

/-- **cpow-reality port.** On `Re ρ > 0` and `n ≥ 1`, the shifted `*W`-detector's `n`-th summand
has norm `|a_λ(n)|·n^{−Re ρ}·(1−n/x)₊`: the `n^{−ρ}` twist contributes only `n^{−Re ρ}` (real),
and the coefficient/kernel are real-cast. Ported from `norm_dhDetectorShift_term`. -/
lemma norm_dhCoeffW_term {q : ℕ} (χ : DirichletCharacter ℂ q) (lam : ℕ → ℝ)
    (x : ℝ) {ρ : ℂ} (hρ : 0 < ρ.re) {n : ℕ} (_hn : 1 ≤ n) :
    ‖(dhCoeffW χ lam n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)‖
      = |dhCoeffW χ lam n| * (n : ℝ) ^ (-ρ.re) * dhKernR ((n : ℝ) / x) := by
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, norm_natCast_cpow_neg hρ n,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (dhKernR_nonneg _)]

/-! ## §5 — the Selberg local factors `h`, `g` and the `h`-range

The exact local residue density `h(p) = 1 + χ_ℝ(p) − χ_ℝ(p)/p` (Benli §4) and its Selberg
reciprocal `g = h/(p−h)`. For real `χ` and `p` prime, `h(p) ∈ {2−1/p, 1, 1/p}` (per
`χ_ℝ(p) ∈ {1,0,−1}`) — all in `(0,2]` with `h(p) < p`, so `g(p) > 0` (no degeneracy). These are
DEFS with the range proven here; the optimality algebra (`selberg_opt_eq`, `selweight_abs_le_one`,
the mean lower bound `H_lower`) is R4/R5 (wave 2). -/

/-- **The exact local residue density** `h(p) = 1 + χ_ℝ(p) − χ_ℝ(p)/p`. -/
def selH {q : ℕ} (χ : DirichletCharacter ℂ q) (p : ℕ) : ℝ := 1 + chiRe χ p - chiRe χ p / p

/-- `0 < h(p)` for real `χ`, `p ≥ 2`. -/
lemma selH_pos {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {p : ℕ} (hp : 2 ≤ p) :
    0 < selH χ p := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rcases chiRe_values χ hsq p with h | h | h <;> rw [selH, h]
  · rw [zero_div]; norm_num
  · have h1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; linarith
    linarith
  · have h1 : 0 < 1 / (p : ℝ) := by positivity
    rw [neg_div]; linarith

/-- `h(p) ≤ 2` for real `χ`, `p ≥ 2`. -/
lemma selH_le_two {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {p : ℕ} (hp : 2 ≤ p) :
    selH χ p ≤ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rcases chiRe_values χ hsq p with h | h | h <;> rw [selH, h]
  · rw [zero_div]; norm_num
  · have h1 : 0 ≤ 1 / (p : ℝ) := by positivity
    linarith
  · have h1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; linarith
    rw [neg_div]; linarith

/-- `h(p) < p` for real `χ`, `p ≥ 2` (the `g`-denominator positivity). -/
lemma selH_lt_of_prime {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {p : ℕ}
    (hp : 2 ≤ p) : selH χ p < (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rcases chiRe_values χ hsq p with h | h | h <;> rw [selH, h]
  · rw [zero_div]; linarith
  · have h1 : 0 < 1 / (p : ℝ) := by positivity
    linarith
  · have h1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; linarith
    rw [neg_div]; linarith

/-- **The Selberg local factor** `g(p) = h(p)/(p − h(p))` (the freeze convention `g = 1/g_Benli`,
so `H = Σ μ²·g`). -/
def selG {q : ℕ} (χ : DirichletCharacter ℂ q) (p : ℕ) : ℝ := selH χ p / ((p : ℝ) - selH χ p)

/-- `0 < g(p)` for real `χ`, `p ≥ 2`. -/
lemma selG_pos {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {p : ℕ} (hp : 2 ≤ p) :
    0 < selG χ p :=
  div_pos (selH_pos χ hsq hp) (by linarith [selH_lt_of_prime χ hsq hp])

/-- The multiplicative extension `g(d) = ∏_{p ∣ d} g(p)` (over the prime factors of `d`). -/
def selGmul {q : ℕ} (χ : DirichletCharacter ℂ q) (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors, selG χ p

/-- The multiplicative extension `h(d) = ∏_{p ∣ d} h(p)`. -/
def selHmul {q : ℕ} (χ : DirichletCharacter ℂ q) (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors, selH χ p

/-- `0 < g(d)` for real `χ` (a product of positive prime factors). -/
lemma selGmul_pos {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (d : ℕ) :
    0 < selGmul χ d :=
  Finset.prod_pos (fun _p hp => selG_pos χ hsq (Nat.prime_of_mem_primeFactors hp).two_le)

/-- **The freeze's `H(z) = Σ_{r ≤ z, sqfree} μ²(r)·g(r)`** (`μ² = 1` on the squarefree support). -/
def selHSum {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter Squarefree, selGmul χ r

/-- `0 < H(z)` for `z ≥ 1` (nonempty — the `r = 1` term — sum of positive `g(r)`). -/
lemma selHSum_pos {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 1 ≤ z) :
    0 < selHSum χ z := by
  rw [selHSum]
  refine Finset.sum_pos (fun r _ => selGmul_pos χ hsq r) ⟨1, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨le_refl 1, hz⟩, squarefree_one⟩

/-! ## §6 — the Selberg-optimal weight `selWeight` (Benli (4.8)) -/

/-- **The Selberg-optimal weight** `θ_d` (Benli–Goel–Twiss–Zaman (4.8), freeze `g`-convention):
`θ_d = μ(d)·(d/h(d))·g(d)/H(z)·Σ_{r ≤ z/d, (r,d)=1, sqfree} g(r)` for squarefree `d ≤ z`,
else `0`.

HOUSE CORRECTION (2026-07-18, catch #163/W3b-#158): wave 1 shipped the local factor as
`h(d)`; the Selberg optimizer needs `1/ν(d) = d/h(d)` there. The two agree at `d = 1`
(`h(1) = 1`), which is why `selWeight_apply_one = 1` did not catch it; W3b certified the
inverted form makes `selberg_opt_eq` and `selweight_abs_le_one` FALSE (V = 0.514 vs 1/H =
0.308; max|θ| = 1.1217) and the corrected form exact to 3.3e-16 over 200 random (z, χ).
A weight def is not validated by its value at 1.

A DEF (properties `selweight_one`/`selweight_abs_le_one`/optimality are R4). -/
def selWeight {q : ℕ} (χ : DirichletCharacter ℂ q) (z d : ℕ) : ℝ :=
  if d ≤ z ∧ Squarefree d then
    (moebius d : ℝ) * ((d : ℝ) / selHmul χ d) * selGmul χ d / selHSum χ z
      * ∑ r ∈ (Finset.Icc 1 (z / d)).filter (fun r => Squarefree r ∧ Nat.Coprime r d),
          selGmul χ r
  else 0

/-- **`selWeight` validation.** `θ_1 = 1` for `z ≥ 1`: the guard holds, `μ(1)=h(1)=g(1)=1`, the
coprime inner sum over `r ≤ z` collapses to `H(z)`, and `H(z)/H(z) = 1`. -/
lemma selWeight_apply_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ}
    (hz : 1 ≤ z) : selWeight χ z 1 = 1 := by
  have hH : selHSum χ z ≠ 0 := (selHSum_pos χ hsq hz).ne'
  rw [selWeight, if_pos ⟨hz, squarefree_one⟩]
  have hμ : ((moebius 1 : ℤ) : ℝ) = 1 := by rw [moebius_apply_one]; norm_num
  have hHmul : selHmul χ 1 = 1 := by rw [selHmul, Nat.primeFactors_one, Finset.prod_empty]
  have hGmul : selGmul χ 1 = 1 := by rw [selGmul, Nat.primeFactors_one, Finset.prod_empty]
  have hinner :
      (∑ r ∈ (Finset.Icc 1 (z / 1)).filter (fun r => Squarefree r ∧ Nat.Coprime r 1), selGmul χ r)
        = selHSum χ z := by
    rw [Nat.div_one, selHSum]
    congr 1
    apply Finset.filter_congr
    intro r _
    simp
  rw [hμ, hHmul, hGmul, hinner, Nat.cast_one]
  field_simp

/-! ## §7 — R1: the exact termwise shift to the real zero (`tail_shift_to_beta0`)

The T-BAL-UNORDERED deviation, carried and named. The tail sum `S₀` at the complex-zero
abscissa `σ = Re ρ` is bounded by `N^{β₀−σ}` times the real-zero detector `D₀` with its `n = 1`
floor `(1−1/x)` removed: from `n^{−σ} ≤ n^{−β₀}·N^{β₀−σ}` on `2 ≤ n ≤ N` (valid because
`σ ≤ β₀`, so `β₀−σ ≥ 0`) and the coefficient nonnegativity `c n ≥ 0`. EXACT — no square-root
error mechanism (there is no Abel-vs-mass step on this route). -/

/-- **R1 — the termwise shift to `β₀`.** For a nonnegative coefficient sequence `c` with `c 1 = 1`,
`x ≥ 1`, `N ≥ 1`, and `σ ≤ β₀`,
`Σ_{2≤n≤N} c n·n^{−σ}·(1−n/x)₊ ≤ N^{β₀−σ}·(Σ_{1≤n≤N} c n·n^{−β₀}·(1−n/x)₊ − (1−1/x))`.
The `*W`-detector instantiates `c = dhCoeffW χ λ` (`dhCoeffW_nonneg`, `dhCoeffW_one` at `λ 1 = 1`).
-/
theorem tail_shift_to_beta0 {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (hc1 : c 1 = 1)
    {x : ℝ} (hx : 1 ≤ x) {N : ℕ} (hN : 1 ≤ N) {σ β₀ : ℝ} (hσβ : σ ≤ β₀) :
    ∑ n ∈ Finset.Icc 2 N, c n * (n : ℝ) ^ (-σ) * dhKernR ((n : ℝ) / x)
      ≤ (N : ℝ) ^ (β₀ - σ)
        * ((∑ n ∈ Finset.Icc 1 N, c n * (n : ℝ) ^ (-β₀) * dhKernR ((n : ℝ) / x))
            - (1 - 1 / x)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hexp : (0 : ℝ) ≤ β₀ - σ := by linarith
  have hins : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1 : (1 : ℕ) ∉ Finset.Icc 2 N := by simp only [Finset.mem_Icc]; omega
  -- the `n = 1` term of the `β₀`-detector is `1 − 1/x`, so `D₀ − (1−1/x)` is the tail.
  have hsplit :
      (∑ n ∈ Finset.Icc 1 N, c n * (n : ℝ) ^ (-β₀) * dhKernR ((n : ℝ) / x)) - (1 - 1 / x)
        = ∑ n ∈ Finset.Icc 2 N, c n * (n : ℝ) ^ (-β₀) * dhKernR ((n : ℝ) / x) := by
    rw [hins, Finset.sum_insert h1]
    have hterm : c 1 * ((1 : ℕ) : ℝ) ^ (-β₀) * dhKernR (((1 : ℕ) : ℝ) / x) = 1 - 1 / x := by
      rw [hc1, Nat.cast_one, Real.one_rpow, one_mul, one_mul,
        dhKernR_eq ((div_le_one hx0).mpr hx)]
    rw [hterm]; ring
  rw [hsplit, Finset.mul_sum]
  refine Finset.sum_le_sum (fun n hn => ?_)
  rw [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnNR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
  have hrpow : (n : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (β₀ - σ) * (n : ℝ) ^ (-β₀) := by
    have heq : (n : ℝ) ^ (-σ) = (n : ℝ) ^ (-β₀) * (n : ℝ) ^ (β₀ - σ) := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    rw [heq]
    calc (n : ℝ) ^ (-β₀) * (n : ℝ) ^ (β₀ - σ)
        ≤ (n : ℝ) ^ (-β₀) * (N : ℝ) ^ (β₀ - σ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hnNR hexp)
            (Real.rpow_nonneg hn0.le _)
      _ = (N : ℝ) ^ (β₀ - σ) * (n : ℝ) ^ (-β₀) := by ring
  calc c n * (n : ℝ) ^ (-σ) * dhKernR ((n : ℝ) / x)
      ≤ c n * ((N : ℝ) ^ (β₀ - σ) * (n : ℝ) ^ (-β₀)) * dhKernR ((n : ℝ) / x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow (hc n)) (dhKernR_nonneg _)
    _ = (N : ℝ) ^ (β₀ - σ) * (c n * (n : ℝ) ^ (-β₀) * dhKernR ((n : ℝ) / x)) := by ring

end Salt.SW

end
