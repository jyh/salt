/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.Growth
import Salt.SW.EulerBridge
import Salt.SW.FourFold
import Salt.SW.Siegel
import Salt.SW.SiegelFinal
import Salt.SW.Page
import Salt.BrunLower.MertensWindow

/-!
# The SW rung, node S4b⁗ — the Siegel closer

Design: `docs/blueprints/sw.md`, wave S4; flags `SW S4b‴`/`S4b‴ adjudication`. This module lands
the two deferred analytic inputs of the ε-quantified Siegel theorem — the near-line log-power
growth bounds (i) and the Euler-correction log bound (ii) — and assembles them into the closer.

## (i) Near-line log-power bounds (truncated Dirichlet series)

For a primitive `χ` mod `f ≥ 2`, the truncated split of `L = growthSum` at index `f` (trivial
`‖Sχ(i+1)‖ ≤ i+1` for the `i < f` head, Pólya–Vinogradov `‖Sχ‖ ≤ √f(1+log f)` for the tail with the
crucial `(i+f)^{-σ-1} ≤ f^{1/2-σ}(i+f)^{-3/2}` decay) gives `‖L(s,χ)‖ ≤ 5e·(1+log f)·‖s‖` on the
near-line region `Re s ≥ 1 − 1/(1+log f)`, `Re s ≥ 1/2` — a log-power replacement for the uniform
`√f log f` growth of `Growth.LFunction_growth`.

## (ii) The Euler-correction log bound (PM1 Mertens)

`‖∏_{p|N}(1 − a(p)p^{-1})‖ ≤ C₉·(1+log N)` (`‖a p‖ ≤ 1`) via `∏(1+1/p) ≤ exp(∑_{p|N}1/p)` and the
double-log windowed Mertens bound `Salt.BrunLower.sum_inv_le_of_prime_window` (`w = 2`, `z = N+1`).
-/

namespace Salt.SW

open Complex Metric Filter Finset MeasureTheory DirichletCharacter
open scoped LSeries.notation Topology ComplexOrder

/-! ## (ii) The Euler-correction log bound -/

/-- The constant in the Euler-correction bound (ii): `exp(19/log 2)/log 2`. -/
noncomputable def eulerC : ℝ := Real.exp (19 / Real.log 2) / Real.log 2

lemma eulerC_pos : 0 < eulerC := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold eulerC; positivity

/-- **The Euler-correction log bound (ii), core form.** For `N ≥ 2` and coefficients `a` with
`‖a p‖ ≤ 1`, `‖∏_{p|N}(1 − a(p)·p^{-1})‖ ≤ eulerC·(1 + log N)`. Route: per-factor
`‖1 − a(p)/p‖ ≤ 1 + 1/p`, then `∏(1+1/p) ≤ ∏ exp(1/p) = exp(∑_{p|N}1/p)`, and the double-log
windowed Mertens bound `∑_{p|N}1/p ≤ log(log(N+1)/log 2) + 19/log 2`. -/
theorem prod_norm_one_sub_le {N : ℕ} (hN : 2 ≤ N) (a : ℕ → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) :
    ‖∏ p ∈ N.primeFactors, (1 - a p * (p : ℂ) ^ (-(1 : ℂ)))‖ ≤ eulerC * (1 + Real.log N) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by linarith
  -- per-factor norm bound `‖1 − a(p)/p‖ ≤ 1 + 1/p`
  have hterm : ∀ p ∈ N.primeFactors, ‖(1 : ℂ) - a p * (p : ℂ) ^ (-(1 : ℂ))‖ ≤ 1 + 1 / (p : ℝ) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hP0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hcpow : ‖(p : ℂ) ^ (-(1 : ℂ))‖ = 1 / (p : ℝ) := by
      rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hP0]
      rw [show ((-(1 : ℂ)).re) = (-1 : ℝ) by simp, Real.rpow_neg_one, one_div]
    calc ‖(1 : ℂ) - a p * (p : ℂ) ^ (-(1 : ℂ))‖
        ≤ ‖(1 : ℂ)‖ + ‖a p * (p : ℂ) ^ (-(1 : ℂ))‖ := norm_sub_le _ _
      _ = 1 + ‖a p‖ * (1 / (p : ℝ)) := by rw [norm_one, norm_mul, hcpow]
      _ ≤ 1 + 1 * (1 / (p : ℝ)) := by
          have : ‖a p‖ * (1 / (p : ℝ)) ≤ 1 * (1 / (p : ℝ)) :=
            mul_le_mul_of_nonneg_right (ha p) (by positivity)
          linarith
      _ = 1 + 1 / (p : ℝ) := by ring
  -- `∏ ‖·‖ ≤ ∏ (1 + 1/p)`
  have hstep1 : ‖∏ p ∈ N.primeFactors, ((1 : ℂ) - a p * (p : ℂ) ^ (-(1 : ℂ)))‖
      ≤ ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℝ)) := by
    rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hterm
  -- `∏ (1 + 1/p) ≤ exp (∑ 1/p)`
  have hstep2 : ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℝ))
      ≤ Real.exp (∑ p ∈ N.primeFactors, 1 / (p : ℝ)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp; have := Nat.prime_of_mem_primeFactors hp; positivity
    · intro p _
      have h := Real.add_one_le_exp (1 / (p : ℝ))
      linarith
  -- Mertens: `∑_{p|N} 1/p ≤ log(log(N+1)/log 2) + 19/log 2`
  have hmertens : ∑ p ∈ N.primeFactors, 1 / (p : ℝ)
      ≤ Real.log (Real.log ((N : ℝ) + 1) / Real.log 2) + 19 / Real.log 2 := by
    apply Salt.BrunLower.sum_inv_le_of_prime_window (w := 2) (z := (N : ℝ) + 1) (by norm_num)
      (by linarith)
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp
    have hpleN : p ≤ N := Nat.le_of_dvd (by omega) hpN
    refine ⟨hpp, ?_, ?_⟩
    · exact_mod_cast hpp.two_le
    · have : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpleN
      linarith
  -- assemble
  have hXpos : (0 : ℝ) < Real.log ((N : ℝ) + 1) / Real.log 2 := by
    apply div_pos _ hlog2
    apply Real.log_pos; linarith
  have hexpmono : Real.exp (∑ p ∈ N.primeFactors, 1 / (p : ℝ))
      ≤ Real.exp (Real.log (Real.log ((N : ℝ) + 1) / Real.log 2)) * Real.exp (19 / Real.log 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hmertens
  have hexplog : Real.exp (Real.log (Real.log ((N : ℝ) + 1) / Real.log 2))
      = Real.log ((N : ℝ) + 1) / Real.log 2 := Real.exp_log hXpos
  -- `log(N+1) ≤ 1 + log N`
  have hlogN1 : Real.log ((N : ℝ) + 1) ≤ 1 + Real.log N := by
    have h1 : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N := by
      rw [Real.log_mul (by norm_num) (by linarith)]
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hlogNnn : 0 ≤ Real.log N := Real.log_nonneg hN1R
  calc ‖∏ p ∈ N.primeFactors, ((1 : ℂ) - a p * (p : ℂ) ^ (-(1 : ℂ)))‖
      ≤ ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℝ)) := hstep1
    _ ≤ Real.exp (∑ p ∈ N.primeFactors, 1 / (p : ℝ)) := hstep2
    _ ≤ Real.log ((N : ℝ) + 1) / Real.log 2 * Real.exp (19 / Real.log 2) := by
        rw [hexplog] at hexpmono; exact hexpmono
    _ ≤ (1 + Real.log N) / Real.log 2 * Real.exp (19 / Real.log 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        gcongr
    _ = eulerC * (1 + Real.log N) := by unfold eulerC; ring

/-- **The Euler-correction log bound (ii).** For `χ` mod `q ≥ 2`,
`‖eulerCorr χ 1‖ ≤ eulerC·(1 + log q)`. The Euler correction (`EulerBridge.eulerCorr`) is the finite
product `∏_{p|q}(1 − χ_prim(p)p^{-1})`; `prod_norm_one_sub_le` with `‖χ_prim(p)‖ ≤ 1`. -/
theorem norm_eulerCorr_one_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) :
    ‖eulerCorr χ 1‖ ≤ eulerC * (1 + Real.log q) := by
  have heq : eulerCorr χ 1
      = ∏ p ∈ q.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-(1 : ℂ))) := by
    rw [eulerCorr]; apply Finset.prod_congr rfl; intro p _; rfl
  rw [heq]
  exact prod_norm_one_sub_le hq (fun p => χ.primitiveCharacter p)
    (fun p => χ.primitiveCharacter.norm_le_one _)

/-! ## (i) Near-line log-power growth bounds (truncated Dirichlet series)

The uniform growth bound `Growth.LFunction_growth` is `≪ √f·log f`; here we run the truncated split
of `L = growthSum` (`Growth.LFunction_eq_growthSum`) at index `f` to get a log-power bound valid on
the near-line region. -/

/-- `∑_{i < f} (i:ℝ)⁻¹ ≤ 1 + log f` (the harmonic bound). -/
lemma sum_range_inv_le {f : ℕ} (hf : 1 ≤ f) :
    ∑ i ∈ Finset.range f, (i : ℝ)⁻¹ ≤ 1 + Real.log f := by
  have hIco : ∑ i ∈ Finset.range f, (i : ℝ)⁻¹ = ∑ i ∈ Finset.Ico 1 f, (i : ℝ)⁻¹ := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive (fun i => (i : ℝ)⁻¹) (Nat.zero_le 1) hf,
      show (Finset.Ico 0 1 : Finset ℕ) = {0} by decide, Finset.sum_singleton]
    simp
  rw [hIco]
  have hIcc : Finset.Ico 1 f = Finset.Icc 1 (f - 1) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  have hEq : ((harmonic (f - 1) : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 (f - 1), (k : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  rw [hIcc, ← hEq]
  calc ((harmonic (f - 1) : ℚ) : ℝ) ≤ 1 + Real.log ((f - 1 : ℕ) : ℝ) :=
        harmonic_le_one_add_log (f - 1)
    _ ≤ 1 + Real.log f := by
        have hle : ((f - 1 : ℕ) : ℝ) ≤ (f : ℝ) := by exact_mod_cast Nat.sub_le f 1
        rcases Nat.eq_zero_or_pos (f - 1) with h0 | h0
        · rw [h0, Nat.cast_zero, Real.log_zero]
          have : (0 : ℝ) ≤ Real.log f := Real.log_nonneg (by exact_mod_cast hf)
          linarith
        · have h01 : (0 : ℝ) < ((f - 1 : ℕ) : ℝ) := by exact_mod_cast h0
          linarith [Real.log_le_log h01 hle]

/-- The near-line head sum bound: `∑_{i < f} i^{-σ} ≤ e·(1 + log f)` for `σ ≥ 1 − 1/(1+log f)`. -/
lemma head_sum_le {f : ℕ} (hf : 2 ≤ f) {σ : ℝ} (hσ : 1 - 1 / (1 + Real.log f) ≤ σ) :
    ∑ i ∈ Finset.range f, (i : ℝ) ^ (-σ) ≤ Real.exp 1 * (1 + Real.log f) := by
  have hlogfpos : (0 : ℝ) < Real.log f := Real.log_pos (by exact_mod_cast hf)
  have h1logf : (1 : ℝ) < 1 + Real.log f := by linarith
  have hσ0 : 0 < σ := by
    have : 1 / (1 + Real.log f) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hexpbnd : (1 - σ) * Real.log f ≤ 1 := by
    have h1 : 1 - σ ≤ 1 / (1 + Real.log f) := by linarith
    calc (1 - σ) * Real.log f ≤ (1 / (1 + Real.log f)) * Real.log f :=
          mul_le_mul_of_nonneg_right h1 hlogfpos.le
      _ = Real.log f / (1 + Real.log f) := by rw [div_mul_eq_mul_div, one_mul]
      _ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hterm : ∀ i ∈ Finset.range f, (i : ℝ) ^ (-σ) ≤ Real.exp 1 * (i : ℝ)⁻¹ := by
    intro i hi
    rw [Finset.mem_range] at hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [Nat.cast_zero, Real.zero_rpow (by linarith), inv_zero, mul_zero]
    · have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hpos
      have hi0 : (0 : ℝ) < (i : ℝ) := by linarith
      have hlogi0 : 0 ≤ Real.log i := Real.log_nonneg hiR
      have hle1 : (1 - σ) * Real.log i ≤ 1 := by
        rcases le_total σ 1 with hs1 | hs1
        · have hlogi : Real.log i ≤ Real.log f :=
            Real.log_le_log hi0 (by exact_mod_cast (by omega : i ≤ f))
          calc (1 - σ) * Real.log i ≤ (1 - σ) * Real.log f :=
                mul_le_mul_of_nonneg_left hlogi (by linarith)
            _ ≤ 1 := hexpbnd
        · have : (1 - σ) * Real.log i ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (by linarith) hlogi0
          linarith
      have hpow : (i : ℝ) ^ (1 - σ) ≤ Real.exp 1 := by
        calc (i : ℝ) ^ (1 - σ) = Real.exp (Real.log i * (1 - σ)) := Real.rpow_def_of_pos hi0 _
          _ = Real.exp ((1 - σ) * Real.log i) := by rw [mul_comm]
          _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hle1
      have hsplit : (i : ℝ) ^ (-σ) = (i : ℝ) ^ (1 - σ) * (i : ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one (i : ℝ), ← Real.rpow_add hi0]; ring_nf
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right hpow (by positivity)
  calc ∑ i ∈ Finset.range f, (i : ℝ) ^ (-σ)
      ≤ ∑ i ∈ Finset.range f, Real.exp 1 * (i : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = Real.exp 1 * ∑ i ∈ Finset.range f, (i : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ Real.exp 1 * (1 + Real.log f) :=
        mul_le_mul_of_nonneg_left (sum_range_inv_le (by omega)) (Real.exp_pos _).le

/-- The trivial per-term bound `‖growthTerm χ s i‖ ≤ 2·‖s‖·i^{-σ}` (using `‖Sχ(i+1)‖ ≤ i+1`), the
head-friendly bound with no `√f` factor. -/
lemma growthTerm_norm_le_triv {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f) (hf : 2 ≤ f) (s : ℂ)
    (hσ : 0 < s.re) (i : ℕ) :
    ‖growthTerm χ s i‖ ≤ 2 * ‖s‖ * (i : ℝ) ^ (-s.re) := by
  haveI : Fact (1 < f) := ⟨by omega⟩
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have hchi0 : χ (0 : ZMod f) = 0 := MulChar.map_nonunit χ not_isUnit_zero
    have h0sum : (∑ k ∈ Finset.range (0 + 1), χ (k : ZMod f)) = 0 := by simp [hchi0]
    rw [growthTerm, h0sum, zero_mul, norm_zero]
    positivity
  · have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hpos
    have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hpos
    have hS : ‖∑ k ∈ Finset.range (i + 1), χ (k : ZMod f)‖ ≤ (i : ℝ) + 1 := by
      calc ‖∑ k ∈ Finset.range (i + 1), χ (k : ZMod f)‖
          ≤ ∑ k ∈ Finset.range (i + 1), ‖χ (k : ZMod f)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range (i + 1), (1 : ℝ) := Finset.sum_le_sum (fun k _ => χ.norm_le_one _)
        _ = (i : ℝ) + 1 := by rw [Finset.sum_const, Finset.card_range]; ring
    have hdiff := cpow_diff_bound s hσ hpos
    have hrw : (i : ℝ) ^ (-(s.re + 1)) = (i : ℝ) ^ (-s.re) * (i : ℝ)⁻¹ := by
      rw [show -(s.re + 1) = -s.re + (-1) by ring, Real.rpow_add hi0, Real.rpow_neg_one]
    have hinv : ((i : ℝ) + 1) * (i : ℝ)⁻¹ ≤ 2 := by
      rw [add_mul, mul_inv_cancel₀ hi0.ne', one_mul]
      have hle1 : (i : ℝ)⁻¹ ≤ 1 := by
        have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hiR
        simpa using this
      linarith
    rw [growthTerm, norm_mul]
    calc ‖∑ k ∈ Finset.range (i + 1), χ (k : ZMod f)‖ * ‖(i : ℂ) ^ (-s) - ((i : ℂ) + 1) ^ (-s)‖
        ≤ ((i : ℝ) + 1) * (‖s‖ * (i : ℝ) ^ (-(s.re + 1))) :=
          mul_le_mul hS hdiff (norm_nonneg _) (by positivity)
      _ = (‖s‖ * (i : ℝ) ^ (-s.re)) * (((i : ℝ) + 1) * (i : ℝ)⁻¹) := by rw [hrw]; ring
      _ ≤ (‖s‖ * (i : ℝ) ^ (-s.re)) * 2 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * ‖s‖ * (i : ℝ) ^ (-s.re) := by ring

/-- `∑' i, ((i+f):ℝ)^{-3/2} ≤ 3` (tail of the `3/2`-series), then scaled: the tail-decay bound
`∑' i, ((i+f):ℝ)^{-(σ+1)} ≤ f^{1/2-σ}·3` for `σ ≥ 1/2`. -/
lemma tsum_tail_le {f : ℕ} (hf : 1 ≤ f) {σ : ℝ} (hσ : (1 : ℝ) / 2 ≤ σ) :
    ∑' i : ℕ, ((i + f : ℕ) : ℝ) ^ (-(σ + 1)) ≤ (f : ℝ) ^ ((1 : ℝ) / 2 - σ) * 3 := by
  have hf0 : (0 : ℝ) < f := by exact_mod_cast hf
  have hgsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hS3 : ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 3 := by
    have hds := dser_tsum_le ((1 / 2 : ℝ) : ℂ) (by rw [Complex.ofReal_re]; norm_num)
    rw [Complex.ofReal_re] at hds
    have he : ∀ i : ℕ, (i : ℝ) ^ (-((1 : ℝ) / 2 + 1)) = (i : ℝ) ^ (-(3 / 2 : ℝ)) := fun i => by
      rw [show -((1 : ℝ) / 2 + 1) = -(3 / 2 : ℝ) by norm_num]
    rw [tsum_congr he] at hds
    refine le_trans hds ?_; norm_num
  -- tail summability
  have htailsum32 : Summable (fun i : ℕ => ((i + f : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (summable_nat_add_iff f).mpr hgsum
  have htailsumσ : Summable (fun i : ℕ => ((i + f : ℕ) : ℝ) ^ (-(σ + 1))) :=
    (summable_nat_add_iff f).mpr (Real.summable_nat_rpow.mpr (by linarith))
  -- `∑' i, ((i+f):ℝ)^{-3/2} ≤ 3`
  have htail3 : ∑' i : ℕ, ((i + f : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 3 := by
    have hshift := hgsum.sum_add_tsum_nat_add f
    have hnn : 0 ≤ ∑ i ∈ Finset.range f, (i : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
    linarith [hS3, hnn, hshift]
  -- termwise `((i+f):ℝ)^{-(σ+1)} ≤ f^{1/2-σ}·((i+f):ℝ)^{-3/2}`
  have hterm : ∀ i : ℕ, ((i + f : ℕ) : ℝ) ^ (-(σ + 1))
      ≤ (f : ℝ) ^ ((1 : ℝ) / 2 - σ) * ((i + f : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro i
    have hb : (0 : ℝ) < ((i + f : ℕ) : ℝ) := by
      have : 0 < i + f := by omega
      exact_mod_cast this
    have hfle : (f : ℝ) ≤ ((i + f : ℕ) : ℝ) := by
      have : f ≤ i + f := by omega
      exact_mod_cast this
    have hbase : ((i + f : ℕ) : ℝ) ^ ((1 : ℝ) / 2 - σ) ≤ (f : ℝ) ^ ((1 : ℝ) / 2 - σ) :=
      Real.rpow_le_rpow_of_nonpos hf0 hfle (by linarith)
    have hsplit : ((i + f : ℕ) : ℝ) ^ (-(σ + 1))
        = ((i + f : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * ((i + f : ℕ) : ℝ) ^ ((1 : ℝ) / 2 - σ) := by
      rw [← Real.rpow_add hb]; congr 1; ring
    rw [hsplit]
    calc ((i + f : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * ((i + f : ℕ) : ℝ) ^ ((1 : ℝ) / 2 - σ)
        ≤ ((i + f : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * (f : ℝ) ^ ((1 : ℝ) / 2 - σ) :=
          mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hb.le _)
      _ = (f : ℝ) ^ ((1 : ℝ) / 2 - σ) * ((i + f : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by ring
  calc ∑' i : ℕ, ((i + f : ℕ) : ℝ) ^ (-(σ + 1))
      ≤ ∑' i : ℕ, (f : ℝ) ^ ((1 : ℝ) / 2 - σ) * ((i + f : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
        htailsumσ.tsum_le_tsum hterm (htailsum32.mul_left _)
    _ = (f : ℝ) ^ ((1 : ℝ) / 2 - σ) * ∑' i : ℕ, ((i + f : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := tsum_mul_left
    _ ≤ (f : ℝ) ^ ((1 : ℝ) / 2 - σ) * 3 :=
        mul_le_mul_of_nonneg_left htail3 (Real.rpow_nonneg hf0.le _)

/-- **(i) The near-line log-power growth bound (strip form).** For a primitive `χ` mod `f ≥ 2` and
`s` in the near-line region `Re s ≥ 1 − 1/(1+log f)` and `Re s ≥ 1/2`,
`‖L(s,χ)‖ ≤ 5e·(1 + log f)·‖s‖` — a log-power replacement for the uniform `√f log f` growth. Route:
`L = growthSum` split at index `f`; head `∑_{i<f} ‖gt i‖ ≤ 2‖s‖·e(1+log f)` (trivial `‖Sχ‖ ≤ i+1`),
tail `∑'_i ‖gt(i+f)‖ ≤ 3e(1+log f)‖s‖` (Pólya–Vinogradov + the `f^{1/2-σ}` decay `tsum_tail_le`). -/
theorem LFunction_norm_le_near_one {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {s : ℂ}
    (hσlo : 1 - 1 / (1 + Real.log f) ≤ s.re) (hσhalf : (1 : ℝ) / 2 ≤ s.re) :
    ‖LFunction χ s‖ ≤ 5 * Real.exp 1 * (1 + Real.log f) * ‖s‖ := by
  have hσ : 0 < s.re := by linarith
  have hf0 : (0 : ℝ) < f := by exact_mod_cast (by omega : 0 < f)
  have hlog0 : (0 : ℝ) ≤ Real.log f := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ f))
  have hlogfpos : (0 : ℝ) < Real.log f := Real.log_pos (by exact_mod_cast hf)
  rw [LFunction_eq_growthSum χ hχ hf s hσ]
  -- summability of `‖growthTerm‖`
  have hdom : Summable
      (fun i : ℕ => Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖s‖ * (i : ℝ) ^ (-(s.re + 1))) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  have hns : Summable (fun i => ‖growthTerm χ s i‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => growthTerm_norm_le χ hχ hf s hσ i) hdom
  have hstep0 : ‖∑' i, growthTerm χ s i‖ ≤ ∑' i, ‖growthTerm χ s i‖ := norm_tsum_le_tsum_norm hns
  have hsplit := hns.sum_add_tsum_nat_add f
  -- head
  have hhead : ∑ i ∈ Finset.range f, ‖growthTerm χ s i‖
      ≤ 2 * ‖s‖ * (Real.exp 1 * (1 + Real.log f)) := by
    calc ∑ i ∈ Finset.range f, ‖growthTerm χ s i‖
        ≤ ∑ i ∈ Finset.range f, 2 * ‖s‖ * (i : ℝ) ^ (-s.re) :=
          Finset.sum_le_sum (fun i _ => growthTerm_norm_le_triv χ hf s hσ i)
      _ = 2 * ‖s‖ * ∑ i ∈ Finset.range f, (i : ℝ) ^ (-s.re) := by rw [← Finset.mul_sum]
      _ ≤ 2 * ‖s‖ * (Real.exp 1 * (1 + Real.log f)) :=
          mul_le_mul_of_nonneg_left (head_sum_le hf hσlo) (by positivity)
  -- `√f·f^{1/2-σ} ≤ e`
  have hexpb : (1 - s.re) * Real.log f ≤ 1 := by
    have h1 : 1 - s.re ≤ 1 / (1 + Real.log f) := by linarith
    calc (1 - s.re) * Real.log f ≤ (1 / (1 + Real.log f)) * Real.log f :=
          mul_le_mul_of_nonneg_right h1 hlog0
      _ = Real.log f / (1 + Real.log f) := by rw [div_mul_eq_mul_div, one_mul]
      _ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hfe : Real.sqrt f * (f : ℝ) ^ ((1 : ℝ) / 2 - s.re) ≤ Real.exp 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hf0,
      show (1 : ℝ) / 2 + ((1 : ℝ) / 2 - s.re) = 1 - s.re by ring]
    calc (f : ℝ) ^ (1 - s.re) = Real.exp (Real.log f * (1 - s.re)) := Real.rpow_def_of_pos hf0 _
      _ = Real.exp ((1 - s.re) * Real.log f) := by rw [mul_comm]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hexpb
  -- tail
  have htail : ∑' i, ‖growthTerm χ s (i + f)‖ ≤ 3 * Real.exp 1 * (1 + Real.log f) * ‖s‖ := by
    have htbnd : ∀ i, ‖growthTerm χ s (i + f)‖
        ≤ Real.sqrt f * (1 + Real.log f) * ‖s‖ * ((i + f : ℕ) : ℝ) ^ (-(s.re + 1)) :=
      fun i => growthTerm_norm_le χ hχ hf s hσ (i + f)
    have htsum1 : Summable
        (fun i => Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖s‖ * ((i + f : ℕ) : ℝ) ^ (-(s.re + 1))) :=
      ((summable_nat_add_iff f).mpr (Real.summable_nat_rpow.mpr (by linarith))).mul_left _
    have htail_sum : Summable (fun i => ‖growthTerm χ s (i + f)‖) :=
      (summable_nat_add_iff f).mpr hns
    have hSFnn : (0 : ℝ) ≤ Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖s‖ := by
      apply mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) (norm_nonneg s)
    have h3nn : (0 : ℝ) ≤ 3 * (1 + Real.log f) * ‖s‖ :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (norm_nonneg s)
    calc ∑' i, ‖growthTerm χ s (i + f)‖
        ≤ ∑' i, Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖s‖ * ((i + f : ℕ) : ℝ) ^ (-(s.re + 1)) :=
          htail_sum.tsum_le_tsum htbnd htsum1
      _ = Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖s‖ * ∑' i, ((i + f : ℕ) : ℝ) ^ (-(s.re + 1)) :=
          tsum_mul_left
      _ ≤ Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖s‖ * ((f : ℝ) ^ ((1 : ℝ) / 2 - s.re) * 3) :=
          mul_le_mul_of_nonneg_left (tsum_tail_le (by omega) hσhalf) hSFnn
      _ = (Real.sqrt (f : ℝ) * (f : ℝ) ^ ((1 : ℝ) / 2 - s.re)) * (3 * (1 + Real.log f) * ‖s‖) := by
          ring
      _ ≤ Real.exp 1 * (3 * (1 + Real.log f) * ‖s‖) := mul_le_mul_of_nonneg_right hfe h3nn
      _ = 3 * Real.exp 1 * (1 + Real.log f) * ‖s‖ := by ring
  calc ‖∑' i, growthTerm χ s i‖
      ≤ ∑' i, ‖growthTerm χ s i‖ := hstep0
    _ = ∑ i ∈ Finset.range f, ‖growthTerm χ s i‖ + ∑' i, ‖growthTerm χ s (i + f)‖ := hsplit.symm
    _ ≤ 2 * ‖s‖ * (Real.exp 1 * (1 + Real.log f)) + 3 * Real.exp 1 * (1 + Real.log f) * ‖s‖ :=
        add_le_add hhead htail
    _ = 5 * Real.exp 1 * (1 + Real.log f) * ‖s‖ := by ring

/-- **(i) The `L(1)` log-power bound.** For a primitive `χ` mod `f ≥ 2`,
`‖L(1,χ)‖ ≤ 5e·(1 + log f)`. The `s = 1` case of `LFunction_norm_le_near_one`. -/
theorem LFunction_apply_one_norm_le {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) :
    ‖LFunction χ 1‖ ≤ 5 * Real.exp 1 * (1 + Real.log f) := by
  have hlog0 : (0 : ℝ) ≤ Real.log f := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ f))
  have h1logf : (0 : ℝ) < 1 + Real.log f := by linarith
  have hre : ((1 : ℂ)).re = 1 := Complex.one_re
  have hσlo : 1 - 1 / (1 + Real.log f) ≤ ((1 : ℂ)).re := by
    rw [hre]; linarith [le_of_lt (div_pos one_pos h1logf)]
  have hσhalf : (1 : ℝ) / 2 ≤ ((1 : ℂ)).re := by rw [hre]; norm_num
  have h := LFunction_norm_le_near_one χ hχ hf (s := (1 : ℂ)) hσlo hσhalf
  rwa [norm_one, mul_one] at h

/-- **(i) The near-line derivative log-power bound.** For a primitive `χ` mod `f ≥ 2` and real
`σ ∈ [1 − 1/(4(1+log f)), 1]`, `‖L'(σ,χ)‖ ≤ 25e·(1 + log f)²`. Cauchy on the radius-`1/(4(1+log f))`
disk (whose sphere stays in the near-line strip, `Re z ≥ 1 − 1/(2(1+log f))`, `‖z‖ ≤ 5/4`), where
`LFunction_norm_le_near_one` bounds `‖L(z,χ)‖ ≤ 5e(1+log f)·(5/4)`; the Cauchy factor is
`1/r = 4(1+log f)`. -/
theorem norm_deriv_LFunction_near_one {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {σ : ℝ}
    (hσlo : 1 - 1 / (4 * (1 + Real.log f)) ≤ σ) (hσhi : σ ≤ 1) :
    ‖deriv (LFunction χ) (σ : ℂ)‖ ≤ 25 * Real.exp 1 * (1 + Real.log f) ^ 2 := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  have hlog0 : (0 : ℝ) ≤ Real.log f := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ f))
  have h1logf : (0 : ℝ) < 1 + Real.log f := by linarith
  have hden : (0 : ℝ) < 4 * (1 + Real.log f) := by linarith
  have hne : (1 + Real.log f) ≠ 0 := ne_of_gt h1logf
  set r : ℝ := 1 / (4 * (1 + Real.log f)) with hr
  have hrpos : 0 < r := by rw [hr]; exact div_pos one_pos hden
  have hrle : r ≤ 1 / 4 := by
    rw [hr]; exact one_div_le_one_div_of_le (by norm_num) (by nlinarith [hlog0])
  have hσlo' : 1 - r ≤ σ := by rw [hr]; exact hσlo
  have h2r_eq : 2 * r = 1 / (2 * (1 + Real.log f)) := by rw [hr]; field_simp; ring
  have h2rlog : 2 * r ≤ 1 / (1 + Real.log f) := by
    rw [h2r_eq]; exact one_div_le_one_div_of_le h1logf (by linarith)
  set C : ℝ := 5 * Real.exp 1 * (1 + Real.log f) * (5 / 4) with hCdef
  have hCcoef : (0 : ℝ) ≤ 5 * Real.exp 1 * (1 + Real.log f) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le) (by linarith)
  have hsphere : ∀ z ∈ sphere (σ : ℂ) r, ‖LFunction χ z‖ ≤ C := by
    intro z hz
    rw [mem_sphere, Complex.dist_eq] at hz
    have hzsub : |z.re - σ| ≤ r := by
      have h := Complex.abs_re_le_norm (z - (σ : ℂ))
      rw [Complex.sub_re, Complex.ofReal_re, hz] at h; exact h
    have hzre : σ - r ≤ z.re := by have := abs_le.mp hzsub; linarith [this.1]
    have hσ0 : (0 : ℝ) ≤ σ := by linarith [hσlo', hrle]
    have hznorm : ‖z‖ ≤ σ + r := by
      calc ‖z‖ = ‖(σ : ℂ) + (z - (σ : ℂ))‖ := by ring_nf
        _ ≤ ‖(σ : ℂ)‖ + ‖z - (σ : ℂ)‖ := norm_add_le _ _
        _ ≤ σ + r := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ0, hz]
    have hzlo : 1 - 1 / (1 + Real.log f) ≤ z.re := by linarith [hzre, hσlo', h2rlog]
    have hzhalf : (1 : ℝ) / 2 ≤ z.re := by linarith [hzre, hσlo', hrle]
    have hg := LFunction_norm_le_near_one χ hχ hf hzlo hzhalf
    calc ‖LFunction χ z‖ ≤ 5 * Real.exp 1 * (1 + Real.log f) * ‖z‖ := hg
      _ ≤ 5 * Real.exp 1 * (1 + Real.log f) * (5 / 4) :=
          mul_le_mul_of_nonneg_left (by linarith [hznorm, hσhi, hrle]) hCcoef
      _ = C := by rw [hCdef]
  have hdcc : DiffContOnCl ℂ (LFunction χ) (ball (σ : ℂ) r) :=
    (differentiable_LFunction hχ1).diffContOnCl
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hdcc hsphere
  have hCr : C / r = 25 * Real.exp 1 * (1 + Real.log f) ^ 2 := by
    rw [hCdef, hr]; field_simp; ring
  calc ‖deriv (LFunction χ) (σ : ℂ)‖ ≤ C / r := hcauchy
    _ = 25 * Real.exp 1 * (1 + Real.log f) ^ 2 := hCr

/-- **(i) The sharp derivative mean-value step.** For a primitive `χ` mod `f ≥ 2` with a real zero
`β ∈ [1 − 1/(4(1+log f)), 1)` of `L(·,χ)`, `(L(1,χ)).re ≤ (1−β)·25e·(1 + log f)²`. Same FTC route as
`SiegelFinal.LFunction_one_re_le_mvt`, using the sharp near-line derivative bound
`norm_deriv_LFunction_near_one` (log-power, not `√f`). -/
theorem LFunction_one_re_le_mvt_sharp {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {β : ℝ} (hzero : LFunction χ (β : ℂ) = 0)
    (hβlo : 1 - 1 / (4 * (1 + Real.log f)) ≤ β) (hβhi : β < 1) :
    (LFunction χ 1).re ≤ (1 - β) * (25 * Real.exp 1 * (1 + Real.log f) ^ 2) := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  set K : ℝ := 25 * Real.exp 1 * (1 + Real.log f) ^ 2 with hKdef
  set F' : ℝ → ℂ := fun σ => deriv (LFunction χ) (σ : ℂ) with hF'def
  have hderiv : ∀ σ ∈ Set.uIcc β (1 : ℝ),
      HasDerivAt (fun t : ℝ => LFunction χ (t : ℂ)) (F' σ) σ :=
    fun σ _ => (differentiable_LFunction hχ1 (σ : ℂ)).hasDerivAt.comp_ofReal
  have hana : AnalyticOnNhd ℂ (LFunction χ) Set.univ :=
    (differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ
  have hcontF' : Continuous F' :=
    (continuousOn_univ.mp hana.deriv.continuousOn).comp Complex.continuous_ofReal
  have hint : IntervalIntegrable F' volume β 1 := hcontF'.intervalIntegrable _ _
  have hFTC : (∫ σ in β..(1 : ℝ), F' σ) = LFunction χ 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
      show ((1 : ℝ) : ℂ) = (1 : ℂ) by norm_num, hzero, sub_zero]
  have hnorm_int : ‖(∫ σ in β..(1 : ℝ), F' σ)‖ ≤ (1 - β) * K := by
    have hbnd : ∀ σ ∈ Set.uIoc β (1 : ℝ), ‖F' σ‖ ≤ K := by
      intro σ hσ
      rw [Set.uIoc_of_le hβhi.le, Set.mem_Ioc] at hσ
      exact norm_deriv_LFunction_near_one χ hχ hf (by linarith [hσ.1]) hσ.2
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - β), mul_comm] at h
  calc (LFunction χ 1).re ≤ ‖LFunction χ 1‖ := Complex.re_le_norm _
    _ = ‖(∫ σ in β..(1 : ℝ), F' σ)‖ := by rw [hFTC]
    _ ≤ (1 - β) * K := hnorm_int

/-! ## (iii) The assembly: `siegel_theorem` -/

/-- **Sublinear log bound.** `log x ≤ x^δ/δ` for `x > 0`, `δ > 0` (log grows slower than any
positive power) — the tool that dissolves the polylog factors into `q^{o(1)}`. -/
lemma log_le_rpow_div {x : ℝ} (hx : 0 < x) {d : ℝ} (hd : 0 < d) : Real.log x ≤ x ^ d / d := by
  have h1 : d * Real.log x ≤ x ^ d - 1 := by
    rw [← Real.log_rpow hx]; exact Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx d)
  rw [le_div_iff₀ hd, mul_comm]
  linarith [Real.rpow_pos_of_pos hx d]

/-- `log x ≤ 2√x` for `x > 0`. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hsx
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  linarith

/-- **`diskConst N ≤ 81/2·N²`** (`SiegelFinal.diskConst = 27/2·√N(1+log N)N`), the universal
polynomial bound feeding the `M^{−3(1−β₁)}` exponent arithmetic. Via `1+log N ≤ 3√N`. -/
lemma diskConst_le {N : ℕ} (hN : 1 ≤ N) : diskConst N ≤ 81 / 2 * (N : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN1
  have h3sqrt : 1 + Real.log N ≤ 3 * Real.sqrt N := by linarith [log_le_two_sqrt hN0, hsqrt1]
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  unfold diskConst
  calc 27 / 2 * Real.sqrt N * (1 + Real.log N) * N
      ≤ 27 / 2 * Real.sqrt N * (3 * Real.sqrt N) * N := by
        apply mul_le_mul_of_nonneg_right _ hN0.le
        exact mul_le_mul_of_nonneg_left h3sqrt (by positivity)
    _ = 81 / 2 * (Real.sqrt N * Real.sqrt N) * N := by ring
    _ = 81 / 2 * (N : ℝ) * N := by rw [hsq]
    _ = 81 / 2 * (N : ℝ) ^ 2 := by ring

/-- **Improved imprimitive `L(1)` bound.** For `ψ ≠ 1` mod `N ≥ 2`,
`‖L(ψ,1)‖ ≤ 5e(1+log N)·eulerC(1+log N)` — a log-power one-point bound (`(i)` on the primitive
factor `≤ 5e(1+log N)`, `(ii)` on the Euler correction `≤ eulerC(1+log N)`), replacing the crude
`≪ N` bound `SiegelFinal.norm_LFunction_ball_le` at `s = 1`. -/
theorem norm_LFunction_one_imprim_le {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hN : 2 ≤ N)
    (hψ1 : ψ ≠ 1) :
    ‖LFunction ψ 1‖ ≤ 5 * Real.exp 1 * (1 + Real.log N) * (eulerC * (1 + Real.log N)) := by
  have hlogNnn : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hsplit : LFunction ψ 1 = LFunction ψ.primitiveCharacter 1 * eulerCorr ψ 1 :=
    LFunction_eq_primitive_mul ψ (Or.inl hψ1)
  have hprim1 : ψ.primitiveCharacter ≠ 1 := fun h =>
    hψ1 (by rw [← changeLevel_primitiveCharacter ψ, h, changeLevel_one])
  have hcond2 : 2 ≤ ψ.conductor := by
    have hc1 : ψ.conductor ≠ 1 := fun h => hψ1 (eq_one_iff_conductor_eq_one.mpr h)
    have := ψ.conductor_ne_zero; omega
  have hcondN : ψ.conductor ≤ N :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) (conductor_dvd_level ψ)
  have hgprim : ‖LFunction ψ.primitiveCharacter 1‖ ≤ 5 * Real.exp 1 * (1 + Real.log ψ.conductor) :=
    LFunction_apply_one_norm_le ψ.primitiveCharacter (primitiveCharacter_isPrimitive ψ) hcond2
  have hcorr : ‖eulerCorr ψ 1‖ ≤ eulerC * (1 + Real.log N) := norm_eulerCorr_one_le ψ hN
  have hcondR : (ψ.conductor : ℝ) ≤ N := by exact_mod_cast hcondN
  have hcond1R : (1 : ℝ) ≤ (ψ.conductor : ℝ) := by exact_mod_cast (by omega : 1 ≤ ψ.conductor)
  have hlog : Real.log ψ.conductor ≤ Real.log N := Real.log_le_log (by linarith) hcondR
  have hgprim' : ‖LFunction ψ.primitiveCharacter 1‖ ≤ 5 * Real.exp 1 * (1 + Real.log N) :=
    le_trans hgprim (mul_le_mul_of_nonneg_left (by linarith)
      (by positivity))
  have h5eNnn : (0 : ℝ) ≤ 5 * Real.exp 1 * (1 + Real.log N) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le) (by linarith)
  rw [hsplit, norm_mul]
  exact mul_le_mul hgprim' hcorr (norm_nonneg _) h5eNnn

/-- `changeLevel` of a nontrivial primitive character is nontrivial (re-derivation of the private
`SiegelFinal.changeLevel_ne_one`). -/
private lemma changeLevel_ne_one' {q N : ℕ} [NeZero q] [NeZero N] (hqN : q ∣ N)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    changeLevel hqN χ ≠ 1 := by
  intro he
  have hc : (changeLevel hqN χ).conductor = χ.conductor := conductor_changeLevel χ hqN
  rw [he, conductor_one, (hprim : χ.conductor = q)] at hc
  have hq2 : 2 ≤ q := by
    have hc1 : χ.conductor ≠ 1 := fun h => hχ1 (eq_one_iff_conductor_eq_one.mpr h)
    rw [(hprim : χ.conductor = q)] at hc1; have := NeZero.ne q; omega
  omega

/-- The improved one-point bound constant `B(N) = 5e(1+log N)·eulerC(1+log N)` (log-power). -/
noncomputable def oneB (N : ℕ) : ℝ :=
  5 * Real.exp 1 * (1 + Real.log N) * (eulerC * (1 + Real.log N))

lemma oneB_pos {N : ℕ} (hN : 1 ≤ N) : 0 < oneB N := by
  have : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  unfold oneB; have := eulerC_pos; positivity

/-- **The near-zero Goldfeld `L(1,χ)` lower bound (target level `q`), log-power denominators.** For
the fixed exceptional `χ₁` mod `q₁` (real zero `β₁ ∈ [19/20,1)`) and a *distinct* target `χ` mod `q`
(both primitive real quadratic `≠ 1`), with `N = q₁·q`,
`(1−β₁)/4·(diskConst N³)^{−3(1−β₁)}/(oneB N · oneB N)/(eulerC(1+log N)) ≤ (L(1,χ)).re`.
This re-runs `goldfeld_L_one_lower` with the **log-power** one-point bounds `B = oneB N`
(`norm_LFunction_one_imprim_le`, replacing the crude `≪ N` bounds), then extracts `L(1,χ)` from the
lifted `L(1,χ')` via `LFunction_changeLevel` (`L(χ',1) = L(χ,1)·∏(1−χ(p)p^{-1})`, correction
`≤ eulerC(1+log N)` by `prod_norm_one_sub_le`). -/
theorem siegel_L_one_lower_near {q₁ q : ℕ} [NeZero q₁] [NeZero q]
    (χ₁ : DirichletCharacter ℂ q₁) (χ : DirichletCharacter ℂ q)
    (hp₁ : χ₁.IsPrimitive) (hpχ : χ.IsPrimitive)
    (hsq₁ : χ₁ ^ 2 = 1) (hsqχ : χ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ1 : χ ≠ 1)
    (hdist : ∀ (h : q₁ = q), (h ▸ χ₁) ≠ χ)
    {β₁ : ℝ} (hz₁ : LFunction χ₁ (β₁ : ℂ) = 0) (hβlo : (19 / 20 : ℝ) ≤ β₁) (hβhi : β₁ < 1) :
    (1 - β₁) / 4 * (diskConst (q₁ * q) ^ 3) ^ (-(3 * (1 - β₁)))
        / (oneB (q₁ * q) * oneB (q₁ * q)) / (eulerC * (1 + Real.log ((q₁ * q : ℕ) : ℝ)))
      ≤ (LFunction χ 1).re := by
  set N : ℕ := q₁ * q with hNdef
  haveI : NeZero N := ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩
  have hq₁2 : 2 ≤ q₁ := by
    have hc1 : χ₁.conductor ≠ 1 := fun h => hχ₁1 (eq_one_iff_conductor_eq_one.mpr h)
    rw [(hp₁ : χ₁.conductor = q₁)] at hc1; have := NeZero.ne q₁; omega
  have hN2 : 2 ≤ N := by
    rw [hNdef]; calc 2 ≤ q₁ := hq₁2
      _ = q₁ * 1 := (mul_one _).symm
      _ ≤ q₁ * q := by
          apply Nat.mul_le_mul_left; exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h₁dvd : q₁ ∣ N := dvd_mul_right q₁ q
  have hdvd : q ∣ N := dvd_mul_left q q₁
  set χ₁' : DirichletCharacter ℂ N := changeLevel h₁dvd χ₁ with hχ₁'
  set χ' : DirichletCharacter ℂ N := changeLevel hdvd χ with hχ'
  have hsq1' : χ₁' ^ 2 = 1 := changeLevel_quadratic h₁dvd hsq₁
  have hsq2' : χ' ^ 2 = 1 := changeLevel_quadratic hdvd hsqχ
  have h1 : χ₁' ≠ 1 := changeLevel_ne_one' h₁dvd hp₁ hχ₁1
  have h2 : χ' ≠ 1 := changeLevel_ne_one' hdvd hpχ hχ1
  have hp' : χ₁' * χ' ≠ 1 := product_ne_one h₁dvd hdvd hp₁ hpχ hsqχ hdist
  have hzero' : LFunction χ₁' (β₁ : ℂ) = 0 := by
    rw [hχ₁', LFunction_changeLevel h₁dvd χ₁ (Or.inl hχ₁1), hz₁, zero_mul]
  set D : ℝ := diskConst N with hDdef
  have hD1 : (1 : ℝ) ≤ D := one_le_diskConst
  have hM : (1 : ℝ) ≤ D ^ 3 := by
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ D ^ 3 := by gcongr
  have hMbnd : ∀ z ∈ ball (2 : ℂ) (3 / 2),
      ‖LFunction χ₁' z * LFunction χ' z * LFunction (χ₁' * χ') z‖ ≤ D ^ 3 :=
    fun z hz => fourfold_disk_bound χ₁' χ' h1 h2 hp' hz
  have hBpos : 0 < oneB N := oneB_pos (by omega)
  have hB₁ : (LFunction χ₁' 1).re ≤ oneB N :=
    le_trans (Complex.re_le_norm _) (norm_LFunction_one_imprim_le χ₁' hN2 h1)
  have hB₂ : (LFunction (χ₁' * χ') 1).re ≤ oneB N :=
    le_trans (Complex.re_le_norm _) (norm_LFunction_one_imprim_le (χ₁' * χ') hN2 hp')
  have hgold := goldfeld_L_one_lower estermannPositivity χ₁' χ' hsq1' hsq2' h1 h2 hp' hM hMbnd
    hB₁ hB₂ hBpos hBpos hβlo hβhi hzero'
  -- `hgold : (1-β₁)/4·(D³)^{-3(1-β₁)}/(oneB N · oneB N) ≤ (L χ' 1).re`
  -- extract L(χ,1)
  have hPrel : LFunction χ' 1
      = LFunction χ 1 * ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-(1 : ℂ))) := by
    rw [hχ']; exact LFunction_changeLevel hdvd χ (Or.inl hχ1)
  have hPbnd : ‖∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-(1 : ℂ)))‖
      ≤ eulerC * (1 + Real.log N) :=
    prod_norm_one_sub_le hN2 (fun p => χ p) (fun p => χ.norm_le_one _)
  have hlogNnn : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hEpos : (0 : ℝ) < eulerC * (1 + Real.log N) := by have := eulerC_pos; positivity
  have hLχ1pos : (0 : ℂ) < LFunction χ 1 := LFunction_apply_one_pos hχ1 hsqχ
  obtain ⟨hLχ1re, hLχ1im⟩ := Complex.pos_iff.mp hLχ1pos
  set P : ℂ := ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-(1 : ℂ))) with hP
  have hre : (LFunction χ' 1).re = (LFunction χ 1).re * P.re := by
    rw [hPrel, Complex.mul_re, ← hLχ1im]; ring
  have hPre : P.re ≤ eulerC * (1 + Real.log N) := le_trans (Complex.re_le_norm P) hPbnd
  have hup : (LFunction χ' 1).re ≤ (LFunction χ 1).re * (eulerC * (1 + Real.log N)) := by
    rw [hre]; exact mul_le_mul_of_nonneg_left hPre hLχ1re.le
  have hchain : (1 - β₁) / 4 * (D ^ 3) ^ (-(3 * (1 - β₁))) / (oneB N * oneB N)
      ≤ (LFunction χ 1).re * (eulerC * (1 + Real.log N)) := le_trans hgold hup
  exact (div_le_iff₀ hEpos).mpr hchain

/-! ### The ε-arithmetic -/

/-- Cube-and-rpow lower bound: `((81/2)N²)^{−9t} ≤ (diskConst N³)^{−3t}` (from
`diskConst N ≤ 81/2 N²` and the negative exponent), the polynomial control on the
`M^{−3(1−β₁)}` factor. -/
lemma diskConst_cube_rpow_lower {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    ((81 / 2 : ℝ) * (N : ℝ) ^ 2) ^ (-(9 * t)) ≤ (diskConst N ^ 3) ^ (-(3 * t)) := by
  haveI : NeZero N := ⟨by omega⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : 0 < diskConst N := lt_of_lt_of_le zero_lt_one one_le_diskConst
  have hY0 : (0 : ℝ) < (81 / 2) * (N : ℝ) ^ 2 := by positivity
  have hle : diskConst N ≤ (81 / 2) * (N : ℝ) ^ 2 := diskConst_le hN
  have hcube : (diskConst N) ^ 3 ≤ ((81 / 2) * (N : ℝ) ^ 2) ^ 3 := by
    apply pow_le_pow_left₀ hd0.le hle
  have hYcube_eq : (((81 / 2 : ℝ) * (N : ℝ) ^ 2) ^ 3) ^ (-(3 * t))
      = ((81 / 2 : ℝ) * (N : ℝ) ^ 2) ^ (-(9 * t)) := by
    rw [← Real.rpow_natCast ((81 / 2 : ℝ) * (N : ℝ) ^ 2) 3, ← Real.rpow_mul hY0.le]
    congr 1; push_cast; ring
  rw [← hYcube_eq]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hcube (by linarith)

/-- The polynomial `M^{−3(1−β₁)}` factor is `≥ (const)·q₁^{−ε/2}·q^{−ε/2}` when `18(1−β₁) ≤ ε/2`. -/
lemma poly_lower {q₁ q : ℕ} (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {t ε : ℝ} (ht : 0 < t) (_hε : 0 < ε)
    (htε : 18 * t ≤ ε / 2) :
    (81 / 2 : ℝ) ^ (-(9 * t)) * (q₁ : ℝ) ^ (-(ε / 2)) * (q : ℝ) ^ (-(ε / 2))
      ≤ (diskConst (q₁ * q) ^ 3) ^ (-(3 * t)) := by
  have hN1 : 1 ≤ q₁ * q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hN0 : (0 : ℝ) < ((q₁ * q : ℕ) : ℝ) := by exact_mod_cast hN1
  have hlow := diskConst_cube_rpow_lower (N := q₁ * q) hN1 ht.le
  refine le_trans ?_ hlow
  have hsplit : ((81 / 2 : ℝ) * ((q₁ * q : ℕ) : ℝ) ^ 2) ^ (-(9 * t))
      = (81 / 2 : ℝ) ^ (-(9 * t)) * ((q₁ * q : ℕ) : ℝ) ^ (-(18 * t)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (((q₁ * q : ℕ) : ℝ)) 2, ← Real.rpow_mul hN0.le]
    congr 1; push_cast; ring
  rw [hsplit]
  have hNexp : ((q₁ * q : ℕ) : ℝ) ^ (-(ε / 2)) ≤ ((q₁ * q : ℕ) : ℝ) ^ (-(18 * t)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
  have hNsplit : ((q₁ * q : ℕ) : ℝ) ^ (-(ε / 2))
      = (q₁ : ℝ) ^ (-(ε / 2)) * (q : ℝ) ^ (-(ε / 2)) := by
    rw [show ((q₁ * q : ℕ) : ℝ) = (q₁ : ℝ) * (q : ℝ) by push_cast; ring,
      Real.mul_rpow (by positivity) (by positivity)]
  calc (81 / 2 : ℝ) ^ (-(9 * t)) * (q₁ : ℝ) ^ (-(ε / 2)) * (q : ℝ) ^ (-(ε / 2))
      = (81 / 2 : ℝ) ^ (-(9 * t)) * ((q₁ : ℝ) ^ (-(ε / 2)) * (q : ℝ) ^ (-(ε / 2))) := by ring
    _ = (81 / 2 : ℝ) ^ (-(9 * t)) * ((q₁ * q : ℕ) : ℝ) ^ (-(ε / 2)) := by rw [← hNsplit]
    _ ≤ (81 / 2 : ℝ) ^ (-(9 * t)) * ((q₁ * q : ℕ) : ℝ) ^ (-(18 * t)) :=
        mul_le_mul_of_nonneg_left hNexp (Real.rpow_nonneg (by norm_num) _)

/-- `1 + log x ≤ (1 + 1/d)·x^d` for `x ≥ 1`, `d > 0` — the polylog→power bound. -/
lemma one_add_log_le_rpow {x : ℝ} (hx : 1 ≤ x) {d : ℝ} (hd : 0 < d) :
    1 + Real.log x ≤ (1 + 1 / d) * x ^ d := by
  have hx0 : 0 < x := by linarith
  have h1 : Real.log x ≤ x ^ d / d := log_le_rpow_div hx0 hd
  have hxd1 : 1 ≤ x ^ d := Real.one_le_rpow hx hd.le
  have heq : (1 + 1 / d) * x ^ d = x ^ d + x ^ d / d := by ring
  rw [heq]; linarith

/-- **The ε-arithmetic core.** For the fixed exceptional data `(q₁ ≥ 2, β₁)` and `ε` with the window
condition `18(1−β₁) ≤ ε/2`, the target `L(1,χ)` lower bound `LB(q)` (from `siegel_L_one_lower_near`)
divided by the sharp-MVT denominator `25e(1+log q)²` is `≥ C·q^{−ε}` uniformly in `q`, for an
ineffective `C > 0`. The `M^{−3(1−β₁)}` factor supplies `q^{−ε/2}` (`poly_lower`), the polylog
denominator absorbs `q^{ε/2}` (`one_add_log_le_rpow`); the fixed data folds into `C`. -/
lemma LB_ratio_lower {q₁ : ℕ} (hq₁ : 2 ≤ q₁) {β₁ ε : ℝ} (hβ₁lo : (19 / 20 : ℝ) ≤ β₁)
    (hβ₁hi : β₁ < 1) (hε : 0 < ε) (htε : 18 * (1 - β₁) ≤ ε / 2) :
    ∃ C > 0, ∀ (q : ℕ), 2 ≤ q →
      C * (q : ℝ) ^ (-ε) ≤
        (1 - β₁) / 4 * (diskConst (q₁ * q) ^ 3) ^ (-(3 * (1 - β₁)))
          / (oneB (q₁ * q) * oneB (q₁ * q)) / (eulerC * (1 + Real.log ((q₁ * q : ℕ) : ℝ)))
          / (25 * Real.exp 1 * (1 + Real.log q) ^ 2) := by
  set t : ℝ := 1 - β₁ with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  have hlogq₁nn : (0 : ℝ) ≤ Real.log q₁ := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q₁))
  have heC : 0 < eulerC := eulerC_pos
  have hε14 : (0 : ℝ) < ε / 14 := by positivity
  have h14inv : (1 : ℝ) + 1 / (ε / 14) = 1 + 14 / ε := by rw [one_div_div]
  set A₀ : ℝ := (81 / 2 : ℝ) ^ (-(9 * t)) * (q₁ : ℝ) ^ (-(ε / 2)) with hA₀
  have hA₀pos : 0 < A₀ := by
    rw [hA₀]
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < q₁)) _)
  set A₁ : ℝ :=
    625 * Real.exp 1 ^ 3 * eulerC ^ 3 * (1 + Real.log q₁) ^ 5 * (1 + 14 / ε) ^ 7 with hA₁
  have h1logq₁ : (0 : ℝ) < 1 + Real.log q₁ := by linarith
  have h114ε : (0 : ℝ) < 1 + 14 / ε := by
    have : 0 < 14 / ε := by positivity
    linarith
  have hA₁pos : 0 < A₁ := by
    rw [hA₁]
    have h1 : (0 : ℝ) < 625 * Real.exp 1 ^ 3 * eulerC ^ 3 * (1 + Real.log q₁) ^ 5 :=
      mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos (Real.exp_pos 1) 3)) (pow_pos heC 3))
        (pow_pos h1logq₁ 5)
    exact mul_pos h1 (pow_pos h114ε 7)
  refine ⟨t / 4 * A₀ / A₁, div_pos (mul_pos (by linarith) hA₀pos) hA₁pos, ?_⟩
  intro q hq
  have hq1 : 1 ≤ q := by omega
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < q := by linarith
  have hlogqnn : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hqR
  have h1logq : (0 : ℝ) < 1 + Real.log q := by linarith
  have hlogN : Real.log ((q₁ * q : ℕ) : ℝ) = Real.log q₁ + Real.log q := by
    rw [Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))]
  -- poly lower bound
  have hpoly : A₀ * (q : ℝ) ^ (-(ε / 2)) ≤ (diskConst (q₁ * q) ^ 3) ^ (-(3 * t)) := by
    rw [hA₀]; exact poly_lower (by omega) hq1 ht0 hε htε
  -- denominator identity and upper bound
  have hden_eq : oneB (q₁ * q) * oneB (q₁ * q) * (eulerC * (1 + Real.log ((q₁ * q : ℕ) : ℝ)))
      * (25 * Real.exp 1 * (1 + Real.log q) ^ 2)
      = 625 * Real.exp 1 ^ 3 * eulerC ^ 3 * (1 + Real.log ((q₁ * q : ℕ) : ℝ)) ^ 5
          * (1 + Real.log q) ^ 2 := by
    unfold oneB; ring
  have hlogNle : 1 + Real.log ((q₁ * q : ℕ) : ℝ) ≤ (1 + Real.log q₁) * (1 + Real.log q) := by
    rw [hlogN]; nlinarith [mul_nonneg hlogq₁nn hlogqnn]
  have hlogNnn : (0 : ℝ) ≤ 1 + Real.log ((q₁ * q : ℕ) : ℝ) := by rw [hlogN]; linarith
  have hlogN5 : (1 + Real.log ((q₁ * q : ℕ) : ℝ)) ^ 5
      ≤ ((1 + Real.log q₁) * (1 + Real.log q)) ^ 5 :=
    pow_le_pow_left₀ hlogNnn hlogNle 5
  have hu7 : (1 + Real.log q) ^ 7 ≤ (1 + 14 / ε) ^ 7 * (q : ℝ) ^ (ε / 2) := by
    have h1 := one_add_log_le_rpow hqR hε14
    rw [h14inv] at h1
    calc (1 + Real.log q) ^ 7 ≤ ((1 + 14 / ε) * (q : ℝ) ^ (ε / 14)) ^ 7 :=
          pow_le_pow_left₀ (by linarith) h1 7
      _ = (1 + 14 / ε) ^ 7 * ((q : ℝ) ^ (ε / 14)) ^ (7 : ℕ) := by rw [mul_pow]
      _ = (1 + 14 / ε) ^ 7 * (q : ℝ) ^ (ε / 2) := by
          congr 1
          rw [← Real.rpow_natCast ((q : ℝ) ^ (ε / 14)) 7, ← Real.rpow_mul hqpos.le,
            show (ε / 14) * ((7 : ℕ) : ℝ) = ε / 2 by push_cast; ring]
  have hden_le : oneB (q₁ * q) * oneB (q₁ * q) * (eulerC * (1 + Real.log ((q₁ * q : ℕ) : ℝ)))
      * (25 * Real.exp 1 * (1 + Real.log q) ^ 2) ≤ A₁ * (q : ℝ) ^ (ε / 2) := by
    rw [hden_eq, hA₁]
    have hconst : (0 : ℝ) ≤ 625 * Real.exp 1 ^ 3 * eulerC ^ 3 := by positivity
    calc 625 * Real.exp 1 ^ 3 * eulerC ^ 3 * (1 + Real.log ((q₁ * q : ℕ) : ℝ)) ^ 5
            * (1 + Real.log q) ^ 2
        ≤ 625 * Real.exp 1 ^ 3 * eulerC ^ 3 * ((1 + Real.log q₁) * (1 + Real.log q)) ^ 5
            * (1 + Real.log q) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hlogN5 hconst
      _ = 625 * Real.exp 1 ^ 3 * eulerC ^ 3 * (1 + Real.log q₁) ^ 5 * (1 + Real.log q) ^ 7 := by
          ring
      _ ≤ 625 * Real.exp 1 ^ 3 * eulerC ^ 3 * (1 + Real.log q₁) ^ 5
            * ((1 + 14 / ε) ^ 7 * (q : ℝ) ^ (ε / 2)) := by
          apply mul_le_mul_of_nonneg_left hu7 (by positivity)
      _ = 625 * Real.exp 1 ^ 3 * eulerC ^ 3 * (1 + Real.log q₁) ^ 5 * (1 + 14 / ε) ^ 7
            * (q : ℝ) ^ (ε / 2) := by
          ring
  have hN1 : 1 ≤ q₁ * q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hden_pos : (0 : ℝ) < oneB (q₁ * q) * oneB (q₁ * q)
      * (eulerC * (1 + Real.log ((q₁ * q : ℕ) : ℝ)))
      * (25 * Real.exp 1 * (1 + Real.log q) ^ 2) := by
    have hb : 0 < oneB (q₁ * q) := oneB_pos hN1
    have hEp : (0 : ℝ) < 1 + Real.log ((q₁ * q : ℕ) : ℝ) := by rw [hlogN]; linarith
    have hMv : (0 : ℝ) < 25 * Real.exp 1 * (1 + Real.log q) ^ 2 := by positivity
    exact mul_pos (mul_pos (mul_pos hb hb) (mul_pos heC hEp)) hMv
  -- rewrite the nested-division target as a single fraction over `den`
  rw [div_div]
  rw [div_div]
  rw [show oneB (q₁ * q) * oneB (q₁ * q)
        * (eulerC * (1 + Real.log ((q₁ * q : ℕ) : ℝ)) * (25 * Real.exp 1 * (1 + Real.log q) ^ 2))
      = oneB (q₁ * q) * oneB (q₁ * q) * (eulerC * (1 + Real.log ((q₁ * q : ℕ) : ℝ)))
        * (25 * Real.exp 1 * (1 + Real.log q) ^ 2) by ring]
  rw [le_div_iff₀ hden_pos]
  -- goal: `(t/4·A₀/A₁·q^{-ε})·den ≤ t/4·poly`
  have hCpos : 0 < t / 4 * A₀ / A₁ := div_pos (mul_pos (by linarith) hA₀pos) hA₁pos
  have hCqnn : 0 ≤ t / 4 * A₀ / A₁ * (q : ℝ) ^ (-ε) :=
    mul_nonneg hCpos.le (Real.rpow_nonneg hqpos.le _)
  have hqcomb : (q : ℝ) ^ (-ε) * (q : ℝ) ^ (ε / 2) = (q : ℝ) ^ (-(ε / 2)) := by
    rw [← Real.rpow_add hqpos]; congr 1; ring
  calc t / 4 * A₀ / A₁ * (q : ℝ) ^ (-ε)
        * (oneB (q₁ * q) * oneB (q₁ * q) * (eulerC * (1 + Real.log ((q₁ * q : ℕ) : ℝ)))
          * (25 * Real.exp 1 * (1 + Real.log q) ^ 2))
      ≤ t / 4 * A₀ / A₁ * (q : ℝ) ^ (-ε) * (A₁ * (q : ℝ) ^ (ε / 2)) :=
        mul_le_mul_of_nonneg_left hden_le hCqnn
    _ = t / 4 * (A₀ * ((q : ℝ) ^ (-ε) * (q : ℝ) ^ (ε / 2))) := by
        field_simp
    _ = t / 4 * (A₀ * (q : ℝ) ^ (-(ε / 2))) := by rw [hqcomb]
    _ ≤ t / 4 * (diskConst (q₁ * q) ^ 3) ^ (-(3 * t)) :=
        mul_le_mul_of_nonneg_left hpoly (by linarith)

/-! ### The closer -/

/-- **Siegel's theorem (zero-free form), unconditional and ε-quantified.** For every `ε > 0`
there is an (ineffective) `C > 0` such that every real primitive quadratic `χ ≠ 1` mod `q`
has no real zero
`β ∈ [1 − C/q^ε, 1)`: `L(β,χ) = 0`, `β < 1 ⟹ β ≤ 1 − C/q^ε`.
Route (Goldfeld dichotomy at window `δ = min(ε/36, 1/20)`): the no-exceptional-zero branch is
effective (`C = δ`); the exceptional branch fixes `χ₁, β₁` and case-splits the target `χ` — the
distinct near case runs Estermann→Goldfeld→`L(1)`-lower (`siegel_L_one_lower_near`) against
the sharp
MVT (`LFunction_one_re_le_mvt_sharp`), the `ε`-arithmetic (`LB_ratio_lower`) absorbing the fixed
data; the distinct far case is trivial (`1 − β > 1/(4(1+log q)) ≥ C_far/q^ε`); the `χ = χ₁` case
uses the continuity gap of `L(·,χ₁)` at `1` (`L(1,χ₁) ≠ 0`). -/
theorem siegel_theorem : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
      ∀ {β : ℝ}, LFunction χ (β : ℂ) = 0 → β < 1 → β ≤ 1 - C / (q : ℝ) ^ ε := by
  intro ε hε
  set dl : ℝ := min (ε / 36) (1 / 20) with hdldef
  have hdlpos : 0 < dl := by rw [hdldef]; exact lt_min (by positivity) (by norm_num)
  have hdl20 : dl ≤ 1 / 20 := min_le_right _ _
  have hdlε : dl ≤ ε / 36 := min_le_left _ _
  rcases siegel_dichotomy dl with hno | ⟨q₁, hq₁ne, χ₁, β₁, hp₁, hsq₁, hχ₁1, hz₁, hβ₁lo, hβ₁hi⟩
  · -- easy (effective) branch: `C = dl`
    refine ⟨dl, hdlpos, ?_⟩
    intro q _ χ hprim hsq hne β hzero hβ1
    have hnot := hno q χ hprim hsq hne hzero
    have hβlt : β < 1 - dl := by by_contra hc; exact hnot ⟨not_lt.mp hc, hβ1⟩
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hqε : (1 : ℝ) ≤ (q : ℝ) ^ ε := Real.one_le_rpow hq1 hε.le
    have hle : dl / (q : ℝ) ^ ε ≤ dl := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hqε, hdlpos.le]
    linarith [hβlt, hle]
  · -- exceptional branch
    haveI : NeZero q₁ := hq₁ne
    have hq₁2 : 2 ≤ q₁ := by
      have hc1 : χ₁.conductor ≠ 1 := fun h => hχ₁1 (eq_one_iff_conductor_eq_one.mpr h)
      rw [(hp₁ : χ₁.conductor = q₁)] at hc1; have := NeZero.ne q₁; omega
    have hβ₁19 : (19 / 20 : ℝ) ≤ β₁ := by linarith [hβ₁lo, hdl20]
    have h18 : 18 * (1 - β₁) ≤ ε / 2 := by linarith [hβ₁lo, hdlε]
    obtain ⟨Cnear, hCnearpos, hCnear⟩ := LB_ratio_lower hq₁2 hβ₁19 hβ₁hi hε h18
    -- continuity gap for `χ₁` at `s = 1`
    have hL1ne : LFunction χ₁ 1 ≠ 0 := LFunction_apply_one_ne_zero hχ₁1
    have hcont : ContinuousAt (fun t : ℝ => LFunction χ₁ (t : ℂ)) 1 :=
      ((differentiable_LFunction hχ₁1).continuous.comp Complex.continuous_ofReal).continuousAt
    have hf1 : (fun t : ℝ => LFunction χ₁ (t : ℂ)) 1 ≠ 0 := by
      simp only; rw [show ((1 : ℝ) : ℂ) = 1 by norm_num]; exact hL1ne
    have hev := hcont.eventually_ne hf1
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨r, hrpos, hgap⟩ := hev
    -- the far-case constant
    set Cfar : ℝ := 1 / (4 * (1 + 1 / ε)) with hCfardef
    have h1e : (0 : ℝ) < 1 + 1 / ε := by
      have hpos : 0 < 1 / ε := by positivity
      linarith
    have hCfarpos : 0 < Cfar := by rw [hCfardef]; positivity
    set C : ℝ := min Cnear (min Cfar (r * (q₁ : ℝ) ^ ε)) with hCdef
    have hCq₁pos : 0 < r * (q₁ : ℝ) ^ ε :=
      mul_pos hrpos (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < q₁)) _)
    have hCpos : 0 < C := by rw [hCdef]; exact lt_min hCnearpos (lt_min hCfarpos hCq₁pos)
    have hCle_near : C ≤ Cnear := by rw [hCdef]; exact min_le_left _ _
    have hCle_far : C ≤ Cfar := le_trans (by rw [hCdef]; exact min_le_right _ _) (min_le_left _ _)
    have hCle_q₁ : C ≤ r * (q₁ : ℝ) ^ ε :=
      le_trans (by rw [hCdef]; exact min_le_right _ _) (min_le_right _ _)
    refine ⟨C, hCpos, ?_⟩
    intro q _ χ hprim hsq hne β hzero hβ1
    have hq2 : 2 ≤ q := by
      have hc1 : χ.conductor ≠ 1 := fun h => hne (eq_one_iff_conductor_eq_one.mpr h)
      rw [(hprim : χ.conductor = q)] at hc1; have := NeZero.ne q; omega
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have hqpos : (0 : ℝ) < q := by linarith
    have hqεpos : (0 : ℝ) < (q : ℝ) ^ ε := Real.rpow_pos_of_pos hqpos _
    have hqneg : (q : ℝ) ^ (-ε) = ((q : ℝ) ^ ε)⁻¹ := Real.rpow_neg hqpos.le ε
    by_cases hdist : ∀ (h : q₁ = q), (h ▸ χ₁) ≠ χ
    · -- distinct target
      by_cases hβnear : 1 - 1 / (4 * (1 + Real.log q)) ≤ β
      · -- near zero: Goldfeld + sharp MVT
        have hLB := siegel_L_one_lower_near χ₁ χ hp₁ hprim hsq₁ hsq hχ₁1 hne hdist hz₁ hβ₁19 hβ₁hi
        have hMVT := LFunction_one_re_le_mvt_sharp χ hprim hq2 hzero hβnear hβ1
        have hmvtpos : (0 : ℝ) < 25 * Real.exp 1 * (1 + Real.log q) ^ 2 := by
          have : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hqR; positivity
        have hcomb : (1 - β₁) / 4 * (diskConst (q₁ * q) ^ 3) ^ (-(3 * (1 - β₁)))
            / (oneB (q₁ * q) * oneB (q₁ * q)) / (eulerC * (1 + Real.log ((q₁ * q : ℕ) : ℝ)))
            ≤ (1 - β) * (25 * Real.exp 1 * (1 + Real.log q) ^ 2) := le_trans hLB hMVT
        have hdivle : (1 - β₁) / 4 * (diskConst (q₁ * q) ^ 3) ^ (-(3 * (1 - β₁)))
            / (oneB (q₁ * q) * oneB (q₁ * q)) / (eulerC * (1 + Real.log ((q₁ * q : ℕ) : ℝ)))
            / (25 * Real.exp 1 * (1 + Real.log q) ^ 2) ≤ 1 - β :=
          (div_le_iff₀ hmvtpos).mpr hcomb
        have hCn := le_trans (hCnear q hq2) hdivle
        -- `Cnear·q^{-ε} ≤ 1 - β`, so `C/q^ε ≤ Cnear/q^ε = Cnear·q^{-ε} ≤ 1 - β`
        have hstep : C / (q : ℝ) ^ ε ≤ Cnear * (q : ℝ) ^ (-ε) := by
          rw [hqneg, ← div_eq_mul_inv]
          exact div_le_div_of_nonneg_right hCle_near hqεpos.le
        linarith [hCn, hstep]
      · -- far zero: `1 − β > 1/(4(1+log q)) ≥ C_far/q^ε`
        replace hβnear := not_le.mp hβnear
        have hlogbound : 1 + Real.log q ≤ (1 + 1 / ε) * (q : ℝ) ^ ε :=
          one_add_log_le_rpow hqR hε
        have hfar : Cfar / (q : ℝ) ^ ε ≤ 1 / (4 * (1 + Real.log q)) := by
          have h4log : (0 : ℝ) < 4 * (1 + Real.log q) := by
            have : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hqR; positivity
          rw [div_le_div_iff₀ hqεpos h4log]
          have heq : Cfar * (4 * (1 + Real.log q)) = (1 + Real.log q) / (1 + 1 / ε) := by
            rw [hCfardef]; field_simp
          rw [one_mul, heq, div_le_iff₀ h1e]; nlinarith [hlogbound]
        have hCfle : C / (q : ℝ) ^ ε ≤ Cfar / (q : ℝ) ^ ε :=
          div_le_div_of_nonneg_right hCle_far hqεpos.le
        linarith [hβnear, hfar, hCfle]
    · -- `χ = χ₁` (same character): the continuity gap
      simp only [not_forall, not_not] at hdist
      obtain ⟨hqeq, hχeq⟩ := hdist
      subst hqeq
      rw [← hχeq] at hzero
      -- `β` is a real zero of `L(·,χ₁)`; the gap forces `1 − β ≥ r`
      have hnotgap : ¬ dist β (1 : ℝ) < r := fun hlt => hgap hlt hzero
      have hdist_ge : r ≤ dist β 1 := not_lt.mp hnotgap
      have hβr : β ≤ 1 - r := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith : β - 1 ≤ 0)] at hdist_ge
        linarith
      -- `C ≤ r·q₁^ε`, so `C/q₁^ε ≤ r`, giving `β ≤ 1 − r ≤ 1 − C/q₁^ε`
      have hq₁εpos : (0 : ℝ) < (q₁ : ℝ) ^ ε :=
        Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < q₁)) _
      have hCr : C / (q₁ : ℝ) ^ ε ≤ r := by
        rw [div_le_iff₀ hq₁εpos]; linarith [hCle_q₁]
      linarith [hβr, hCr]

end Salt.SW
