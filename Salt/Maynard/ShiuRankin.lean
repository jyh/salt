/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Mertens.Third

/-!
# ShiuRankin — the smooth Euler-product bound (Rankin engine, first half)

For `v ≥ 2` and a real exponent `σ ∈ (1/2, 1]` we bound the `v`-smooth divisor sum
`Σ_{c ≤ N, c v-smooth} τ(c)/c^σ` by the finite Euler product `∏_{p ≤ v} (1 − p^{−σ})^{−2}`.
Here `c^σ` and `p^{−σ}` are real powers (`Real.rpow`).

The classical route (τ = 1∗1, the Euler square):

* each `v`-smooth `c` factors as `∏_{p ≤ v} p^{e_p}`, with `τ(c) = ∏(e_p+1)` and
  `c^{−σ} = ∏ (p^{−σ})^{e_p}`, so the summand is multiplicative;
* `f c := τ(c)/c^σ` is multiplicative on coprime arguments, `f 1 = 1`, and each local
  series `Σ_e f(p^e) = Σ_e (e+1)(p^{−σ})^e = (1 − p^{−σ})^{−2}` converges because
  `p^{−σ} ≤ 2^{−σ} < 1` for `p ≥ 2`, `σ > 1/2`;
* mathlib's **partial** Euler product
  `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum` (which requires
  only *per-prime* summability, NOT global summability — crucial, since the full sum
  `Σ_n τ(n)/n^σ = ζ(σ)²` diverges for `σ ≤ 1`) gives
  `HasSum (f ↾ (v+1)-smooth) (∏_{p < v+1} Σ_e f(p^e))`;
* the finite `c ≤ N` sum is a sub-sum of that nonnegative total, so `≤` the product.

The smoothness predicate is `∀ p ∈ c.primeFactors, p ≤ v` (decidable; equal to
"every prime factor of `c` is `≤ v`", i.e. `c ∈ (v+1).smoothNumbers` for `c ≥ 1`).

Class B/C (blueprint SHIU-G): the finite→infinite comparison plus rpow/geometric
bookkeeping; the heavy multiplicative-function machinery is reused from mathlib.
-/

open Nat Finset

namespace Salt.Maynard

/-- The multiplicative summand `τ(c)/c^σ` with a real exponent `σ` (`c^σ = Real.rpow`). -/
noncomputable def tauDivRpow (σ : ℝ) (c : ℕ) : ℝ := (c.divisors.card : ℝ) / (c : ℝ) ^ σ

/-- `τ(c)/c^σ ≥ 0`. -/
lemma tauDivRpow_nonneg (σ : ℝ) (c : ℕ) : 0 ≤ tauDivRpow σ c := by
  unfold tauDivRpow
  exact div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- `f 1 = 1`. -/
lemma tauDivRpow_one (σ : ℝ) : tauDivRpow σ 1 = 1 := by
  simp [tauDivRpow, Nat.divisors_one]

/-- `f` is multiplicative on coprime arguments. -/
lemma tauDivRpow_mul (σ : ℝ) {m n : ℕ} (h : Nat.Coprime m n) :
    tauDivRpow σ (m * n) = tauDivRpow σ m * tauDivRpow σ n := by
  unfold tauDivRpow
  rw [Nat.Coprime.card_divisors_mul h]
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity)]
  ring

/-- The local value at a prime power: `f(p^n) = (n+1)·(p^{−σ})^n`. -/
lemma tauDivRpow_prime_pow {p : ℕ} (hp : p.Prime) (σ : ℝ) (n : ℕ) :
    tauDivRpow σ (p ^ n) = ((n : ℝ) + 1) * ((p : ℝ) ^ (-σ)) ^ n := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hcard : ((p ^ n).divisors.card : ℝ) = (n : ℝ) + 1 := by
    rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]; push_cast; ring
  have e1 : ((p : ℝ) ^ (-σ)) ^ n = (p : ℝ) ^ (-σ * (n : ℝ)) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) n, ← Real.rpow_mul hp0]
  have e2 : ((p : ℝ) ^ n) ^ σ = (p : ℝ) ^ ((n : ℝ) * σ) := by
    rw [← Real.rpow_natCast (p : ℝ) n, ← Real.rpow_mul hp0]
  have hx : ((p : ℝ) ^ (-σ)) ^ n = (((p : ℝ) ^ n) ^ σ)⁻¹ := by
    rw [e1, e2, ← Real.rpow_neg hp0, show -σ * (n : ℝ) = -((n : ℝ) * σ) by ring]
  unfold tauDivRpow
  rw [hcard, Nat.cast_pow, hx, div_eq_mul_inv]

/-- The local Euler factor: `Σ_n f(p^n) = (1 − p^{−σ})^{−2}` when `‖p^{−σ}‖ < 1`. -/
lemma perPrime_hasSum {p : ℕ} (hp : p.Prime) (σ : ℝ)
    (hr : ‖((p : ℝ) ^ (-σ))‖ < 1) :
    HasSum (fun n : ℕ => tauDivRpow σ (p ^ n)) ((1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2) := by
  have hfun : (fun n : ℕ => tauDivRpow σ (p ^ n))
      = (fun n : ℕ => ((n + 1).choose 1 : ℝ) * ((p : ℝ) ^ (-σ)) ^ n) := by
    funext n
    rw [Nat.choose_one_right, tauDivRpow_prime_pow hp]
    push_cast; ring
  rw [hfun]
  have h := hasSum_choose_mul_geometric_of_norm_lt_one 1 hr
  rwa [show (1 : ℝ) / (1 - (p : ℝ) ^ (-σ)) ^ (1 + 1) = (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 by
    rw [one_div, inv_pow]] at h

/-- Per-prime norm summability, the sole hypothesis of the partial Euler product. -/
lemma perPrime_summable_norm {p : ℕ} (hp : p.Prime) (σ : ℝ)
    (hr : ‖((p : ℝ) ^ (-σ))‖ < 1) :
    Summable (fun n : ℕ => ‖tauDivRpow σ (p ^ n)‖) := by
  have h : (fun n : ℕ => ‖tauDivRpow σ (p ^ n)‖) = (fun n : ℕ => tauDivRpow σ (p ^ n)) := by
    funext n; rw [Real.norm_eq_abs, abs_of_nonneg (tauDivRpow_nonneg σ (p ^ n))]
  rw [h]; exact (perPrime_hasSum hp σ hr).summable

/-- For a prime `q` and `σ > 0`, `‖q^{−σ}‖ < 1`. -/
lemma norm_rpow_neg_prime_lt_one {q : ℕ} (hq : q.Prime) {σ : ℝ} (hσ : 0 < σ) :
    ‖((q : ℝ) ^ (-σ))‖ < 1 := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq.one_lt
  have hpos : (0 : ℝ) < (q : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _
  have hlt : (q : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  rw [Real.norm_eq_abs, abs_of_pos hpos]; exact hlt

/-- **The smooth Euler-product bound.** For `v ≥ 2` and `σ ∈ (1/2, 1]`,
`Σ_{1 ≤ c ≤ N, c v-smooth} τ(c)/c^σ ≤ ∏_{p ≤ v} (1 − p^{−σ})^{−2}`
(real exponent `σ`; `c v-smooth` = `∀ p ∈ c.primeFactors, p ≤ v`).
The hypotheses `2 ≤ v` and `σ ≤ 1` are carried for the consumer interface; the proof
uses only `1/2 < σ`. -/
theorem sum_tau_smooth_rpow_le (N v : ℕ) (σ : ℝ) (_hv : 2 ≤ v) (hσ : 1 / 2 < σ) (_hσ1 : σ ≤ 1) :
    ∑ c ∈ (Finset.Icc 1 N).filter (fun c => ∀ p ∈ c.primeFactors, p ≤ v),
        (c.divisors.card : ℝ) / (c : ℝ) ^ σ
      ≤ ∏ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  letI : DecidablePred (· ∈ (v + 1).smoothNumbers) := Classical.decPred _
  set myfin := (Finset.Icc 1 N).filter (fun c => ∀ p ∈ c.primeFactors, p ≤ v) with hmyfin
  -- The Euler product as a `HasSum` over `(v+1)`-smooth numbers.
  have hSum := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := tauDivRpow σ) (tauDivRpow_one σ) (fun {m n} h => tauDivRpow_mul σ h)
      (fun {q} hq => perPrime_summable_norm hq σ (norm_rpow_neg_prime_lt_one hq hσ0)) (v + 1)).2
  -- Evaluate the per-prime local factors inside the product.
  have hprodval : (∏ p ∈ (v + 1).primesBelow, ∑' n : ℕ, tauDivRpow σ (p ^ n))
      = ∏ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 :=
    Finset.prod_congr rfl (fun p hp => by
      have hpp : p.Prime := by rw [Finset.mem_filter] at hp; exact hp.2
      exact (perPrime_hasSum hpp σ (norm_rpow_neg_prime_lt_one hpp hσ0)).tsum_eq)
  -- Every filtered `c` is `(v+1)`-smooth.
  have hmem : ∀ c ∈ myfin, c ∈ (v + 1).smoothNumbers := by
    intro c hc
    rw [hmyfin, Finset.mem_filter, Finset.mem_Icc] at hc
    obtain ⟨⟨hc1, _⟩, hcp⟩ := hc
    rw [Nat.mem_smoothNumbers']
    intro p hp hpc
    have hc0 : c ≠ 0 := by omega
    have hpmem : p ∈ c.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpc, hc0⟩
    have := hcp p hpmem
    omega
  -- Assemble: finite sum = subtype sum ≤ tsum (= product).
  calc ∑ c ∈ myfin, (c.divisors.card : ℝ) / (c : ℝ) ^ σ
      = ∑ m ∈ myfin.subtype (· ∈ (v + 1).smoothNumbers), tauDivRpow σ ↑m :=
        (Finset.sum_subtype_of_mem (tauDivRpow σ) hmem).symm
    _ ≤ ∏ p ∈ (v + 1).primesBelow, ∑' n : ℕ, tauDivRpow σ (p ^ n) :=
        sum_le_hasSum _ (fun i _ => tauDivRpow_nonneg σ _) hSum
    _ = ∏ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 := hprodval

/-- **Consumer form at `σ = 1`.** For `v ≥ 2`,
`Σ_{1 ≤ c ≤ N, c v-smooth} τ(c)/c ≤ ∏_{p ≤ v} (1 − 1/p)^{−2}`.
(This is `sum_tau_smooth_rpow_le` with the real powers collapsed: `c^1 = c`,
`p^{−1} = p⁻¹`.) The RHS is `∏_{p ≤ v}(1 − 1/p)^{−2}`, which `mertens_third` grades
as `(C·log v)²`; that exponentiation is the separate S4-I bridge. -/
theorem sum_tau_smooth_div_le (N v : ℕ) (hv : 2 ≤ v) :
    ∑ c ∈ (Finset.Icc 1 N).filter (fun c => ∀ p ∈ c.primeFactors, p ≤ v),
        (c.divisors.card : ℝ) / (c : ℝ)
      ≤ ∏ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹ ^ 2 := by
  have h := sum_tau_smooth_rpow_le N v 1 hv (by norm_num) le_rfl
  simpa only [Real.rpow_one, Real.rpow_neg_one] using h

/-- **Mertens exponentiation.** `∏_{p ≤ v} (1 − 1/p)^{−2} ≤ (C·log v)²` for `v` large.
Derived from `mertens_third` (the two-sided estimate `|∏(1−1/p)·log v − e^{−γ}| ≤ C₀/log v`):
past the threshold the lower tail forces `∏(1−1/p) ≥ e^{−γ}/(2 log v)`, whose inverse-square
is `≤ (2e^{γ}·log v)²`. The constant is `C = 2/e^{−γ} = 2e^{γ}`; the threshold `v₀`
absorbs the `C₀/log v` slack. -/
theorem prod_one_sub_inv_sq_le :
    ∃ (C : ℝ) (v₀ : ℕ), 0 < C ∧ ∀ v : ℕ, v₀ ≤ v →
      ∏ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹ ^ 2
        ≤ (C * Real.log v) ^ 2 := by
  obtain ⟨C₀, hC₀, hmt⟩ := Salt.Mertens.mertens_third
  set g := Real.eulerMascheroniConstant with hg
  have hEpos : (0 : ℝ) < Real.exp (-g) := Real.exp_pos _
  refine ⟨2 / Real.exp (-g), ⌈Real.exp (2 * C₀ / Real.exp (-g))⌉₊ + 3, by positivity, ?_⟩
  intro v hv
  have hv3 : 3 ≤ v := by omega
  have hv1 : 1 < v := by omega
  have hvpos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (by omega : 0 < v)
  have hlogv : 0 < Real.log v := Real.log_pos (by exact_mod_cast hv1)
  have hceil : Real.exp (2 * C₀ / Real.exp (-g)) ≤ (⌈Real.exp (2 * C₀ / Real.exp (-g))⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hlt : (⌈Real.exp (2 * C₀ / Real.exp (-g))⌉₊ : ℝ) < (v : ℝ) := by
    have : ⌈Real.exp (2 * C₀ / Real.exp (-g))⌉₊ < v := by omega
    exact_mod_cast this
  have hexp_lt : Real.exp (2 * C₀ / Real.exp (-g)) < (v : ℝ) := lt_of_le_of_lt hceil hlt
  have hlogv_gt : 2 * C₀ / Real.exp (-g) < Real.log v :=
    (Real.lt_log_iff_exp_lt hvpos).mpr hexp_lt
  have hEv : 2 * C₀ < Real.log v * Real.exp (-g) := (div_lt_iff₀ hEpos).mp hlogv_gt
  have hstep : C₀ / Real.log v ≤ Real.exp (-g) / 2 := by
    rw [div_le_div_iff₀ hlogv (by norm_num : (0:ℝ) < 2)]
    nlinarith [hEv]
  set P := ∏ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) with hPdef
  have hsplit := abs_le.mp (hmt v hv3)
  have hPlogv : Real.exp (-g) / 2 ≤ P * Real.log v := by linarith [hsplit.1, hstep]
  have hPlb : Real.exp (-g) / (2 * Real.log v) ≤ P := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [hPlogv]
  have hPpos : 0 < P := lt_of_lt_of_le (by positivity) hPlb
  have hPinv : P⁻¹ ≤ 2 / Real.exp (-g) * Real.log v := by
    have h := inv_anti₀ (show (0:ℝ) < Real.exp (-g) / (2 * Real.log v) by positivity) hPlb
    rw [inv_div, mul_div_right_comm] at h
    exact h
  have hprodP :
      (∏ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹ ^ 2) = (P⁻¹) ^ 2 := by
    rw [hPdef, Finset.prod_pow, Finset.prod_inv_distrib]; simp only [one_div]
  rw [hprodP]
  exact pow_le_pow_left₀ (inv_pos.mpr hPpos).le hPinv 2

/-- **The composed consumer form (S4-I).** For `v` past a threshold and any `N`,
`Σ_{1 ≤ c ≤ N, c v-smooth} τ(c)/c ≤ (C·log v)²`. Composes `sum_tau_smooth_div_le`
with `prod_one_sub_inv_sq_le`. -/
theorem sum_tau_smooth_div_log_le :
    ∃ (C : ℝ) (v₀ : ℕ), 0 < C ∧ ∀ (N v : ℕ), v₀ ≤ v →
      ∑ c ∈ (Finset.Icc 1 N).filter (fun c => ∀ p ∈ c.primeFactors, p ≤ v),
          (c.divisors.card : ℝ) / (c : ℝ)
        ≤ (C * Real.log v) ^ 2 := by
  obtain ⟨C, v₀, hC, hbound⟩ := prod_one_sub_inv_sq_le
  refine ⟨C, max v₀ 2, hC, fun N v hv => ?_⟩
  have hv2 : 2 ≤ v := le_trans (le_max_right _ _) hv
  have hv0 : v₀ ≤ v := le_trans (le_max_left _ _) hv
  exact le_trans (sum_tau_smooth_div_le N v hv2) (hbound v hv0)

end Salt.Maynard
