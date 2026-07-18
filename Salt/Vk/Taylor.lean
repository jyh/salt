/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.ZetaBlock
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# VMVT-VK rung R1 — the block Taylor expansion of the ζ-phase (`VK-TAYLOR`)

On a block `n = N₀ + m` (`0 ≤ m ≤ P + Y < N₀`) the ζ-phase
`φ(n) = −(t/2π)·log n` is the degree-`k` polynomial
`φ(N₀) + ∑_{j=1}^k c_j·m^j`, `c_j = −(t/2π)(−1)^{j−1}/(j·N₀^j)`, up to a
Lagrange-strength remainder `≤ 2·(t/2π)·((P+Y)/N₀)^{k+1}`.

The core is the sharp truncated-log bound
`|log(1+u) − ∑_{j=1}^k (−1)^{j−1}u^j/j| ≤ u^{k+1}/(k+1)` for `u ≥ 0`, proved by
the FTC: the remainder is `∫₀ᵘ (−1)^k sᵏ/(1+s) ds`, whose integrand has absolute
value `≤ sᵏ`.  This is stronger than mathlib's
`Real.abs_log_sub_add_sum_range_le` (which carries a `1/(1−u)` factor and so
fails at the block boundary `m → N₀`).
-/

namespace Salt.Vk

open Finset Real MeasureTheory
open scoped BigOperators

/-- The block Taylor coefficient `c_j = −(t/2π)·(−1)^{j−1}/(j·N₀^j)` (real form). -/
noncomputable def vkCoef (t N₀ : ℝ) (j : ℕ) : ℝ :=
  -(t / (2 * π)) * (-1 : ℝ) ^ (j - 1) / ((j : ℝ) * N₀ ^ j)

/-! ## The sharp truncated-log remainder -/

/-- The truncated-log series derivative bound: `|(1+s)⁻¹ − ∑_{j=1}^k (−1)^{j−1}s^{j−1}|
≤ sᵏ` for `s ≥ 0`.  The bracket equals `(−1)^k sᵏ/(1+s)`, whose modulus is
`sᵏ/(1+s) ≤ sᵏ`. -/
lemma log_series_deriv_bound (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |(1 + s)⁻¹ - ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * s ^ (j - 1)| ≤ s ^ k := by
  have h1s : (0 : ℝ) < 1 + s := by linarith
  -- reindex the Icc sum to a geometric sum in `(-s)`
  have hreindex : ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * s ^ (j - 1)
      = ∑ i ∈ Finset.range k, (-s) ^ i := by
    induction k with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n), Finset.sum_range_succ, ih]
        congr 1
        have hn : n + 1 - 1 = n := by omega
        rw [hn]; exact (neg_pow s n).symm
  -- geometric identity: `(∑_{i<k} (-s)^i)·(1+s) = 1 − (−1)^k sᵏ`
  have hgeom : (∑ i ∈ Finset.range k, (-s) ^ i) * (1 + s) = 1 - (-1 : ℝ) ^ k * s ^ k := by
    have hg := geom_sum_mul (-s) k
    have h1 : (-s) - 1 = -(1 + s) := by ring
    have h2 : (-s) ^ k = (-1 : ℝ) ^ k * s ^ k := by rw [neg_pow]
    rw [h1, h2] at hg
    -- hg : (∑ (-s)^i) * (-(1+s)) = (-1)^k s^k - 1
    linear_combination -hg
  -- identify the bracket with `(−1)^k sᵏ/(1+s)`
  have hbracket : (1 + s)⁻¹ - ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * s ^ (j - 1)
      = (-1 : ℝ) ^ k * s ^ k / (1 + s) := by
    rw [hreindex]
    rw [eq_div_iff h1s.ne', sub_mul, inv_mul_cancel₀ h1s.ne', hgeom]
    ring
  rw [hbracket, abs_div, abs_mul]
  rw [abs_of_pos h1s]
  have hsk : |s ^ k| = s ^ k := abs_of_nonneg (by positivity)
  have hneg : |(-1 : ℝ) ^ k| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [hsk, hneg, one_mul]
  rw [div_le_iff₀ h1s]
  nlinarith [pow_nonneg hs k]

/-- **The sharp truncated-log remainder.**  For `u ≥ 0`,
`|log(1+u) − ∑_{j=1}^k (−1)^{j−1}u^j/j| ≤ u^{k+1}/(k+1)`. -/
lemma log_series_remainder (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |Real.log (1 + u) - ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * u ^ j / (j : ℝ)|
      ≤ u ^ (k + 1) / (k + 1) := by
  set F : ℝ → ℝ :=
    fun s => Real.log (1 + s) - ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * s ^ j / (j : ℝ)
    with hFdef
  set f : ℝ → ℝ :=
    fun s => (1 + s)⁻¹ - ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * s ^ (j - 1)
    with hfdef
  -- derivative of the antiderivative
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) u, HasDerivAt F (f x) x := by
    intro x hx
    rw [Set.uIcc_of_le hu, Set.mem_Icc] at hx
    have hxpos : (0 : ℝ) < 1 + x := by linarith [hx.1]
    have hlog : HasDerivAt (fun s => Real.log (1 + s)) ((1 + x)⁻¹) x := by
      have hg : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
      have h := hg.log hxpos.ne'
      simpa using h
    have hterm : ∀ j ∈ Finset.Icc 1 k,
        HasDerivAt (fun s => (-1 : ℝ) ^ (j - 1) * s ^ j / (j : ℝ))
          ((-1 : ℝ) ^ (j - 1) * x ^ (j - 1)) x := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjne : (j : ℝ) ≠ 0 := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mp hj1
      have h := ((hasDerivAt_pow j x).const_mul ((-1 : ℝ) ^ (j - 1))).div_const (j : ℝ)
      have heq : (-1 : ℝ) ^ (j - 1) * ((j : ℝ) * x ^ (j - 1)) / (j : ℝ)
          = (-1 : ℝ) ^ (j - 1) * x ^ (j - 1) := by
        field_simp
      rwa [heq] at h
    have hsum0 := HasDerivAt.sum hterm
    have hfun : (∑ j ∈ Finset.Icc 1 k, fun s : ℝ => (-1 : ℝ) ^ (j - 1) * s ^ j / (j : ℝ))
        = fun s : ℝ => ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * s ^ j / (j : ℝ) := by
      funext s; simp only [Finset.sum_apply]
    rw [hfun] at hsum0
    exact hlog.sub hsum0
  -- integrability of the derivative on the interval
  have hcont : ContinuousOn f (Set.uIcc (0 : ℝ) u) := by
    rw [Set.uIcc_of_le hu]
    apply ContinuousOn.sub
    · apply ContinuousOn.inv₀ (by fun_prop)
      intro s hs; rw [Set.mem_Icc] at hs; nlinarith [hs.1]
    · exact (continuous_finsetSum _ (fun j _ => by fun_prop)).continuousOn
  have hint : IntervalIntegrable f volume 0 u := hcont.intervalIntegrable
  -- F 0 = 0
  have hF0 : F 0 = 0 := by
    simp only [hFdef, add_zero, Real.log_one]
    rw [Finset.sum_eq_zero]
    · ring
    · intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      rw [zero_pow (by omega : j ≠ 0)]; ring
  -- FTC
  have hFTC : ∫ s in (0 : ℝ)..u, f s = F u - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hF0, sub_zero] at hFTC
  -- |F u| = |∫ f| ≤ ∫ |f| ≤ ∫ s^k = u^{k+1}/(k+1)
  have hgoal : |F u| ≤ u ^ (k + 1) / (k + 1) := by
    rw [← hFTC]
    have hstep1 : |∫ s in (0 : ℝ)..u, f s| ≤ ∫ s in (0 : ℝ)..u, |f s| :=
      intervalIntegral.abs_integral_le_integral_abs hu
    have hintabs : IntervalIntegrable (fun s => |f s|) volume 0 u := hint.abs
    have hintpow : IntervalIntegrable (fun s => s ^ k) volume 0 u :=
      (continuous_pow k).intervalIntegrable 0 u
    have hstep2 : ∫ s in (0 : ℝ)..u, |f s| ≤ ∫ s in (0 : ℝ)..u, s ^ k := by
      apply intervalIntegral.integral_mono_on hu hintabs hintpow
      intro s hs
      rw [Set.mem_Icc] at hs
      exact log_series_deriv_bound k hs.1
    have hstep3 : ∫ s in (0 : ℝ)..u, s ^ k = u ^ (k + 1) / (k + 1) := by
      rw [integral_pow]; simp
    calc |∫ s in (0 : ℝ)..u, f s|
        ≤ ∫ s in (0 : ℝ)..u, |f s| := hstep1
      _ ≤ ∫ s in (0 : ℝ)..u, s ^ k := hstep2
      _ = u ^ (k + 1) / (k + 1) := hstep3
  -- rewrite the goal LHS as `F u`
  have : Real.log (1 + u) - ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * u ^ j / (j : ℝ) = F u := by
    rw [hFdef]
  rw [this]
  exact hgoal

/-! ## The block Taylor bound for the ζ-phase -/

/-- **VK-TAYLOR (real core).**  On the block `x ↦ −(t/2π)·log(N₀+m)`,
the degree-`k` Taylor polynomial `−(t/2π)·log N₀ + ∑_{j=1}^k c_j m^j`
(`c_j = vkCoef t N₀ j`) approximates with remainder
`≤ (|t|/2π)·(m/N₀)^{k+1}` for `0 ≤ m`, `0 < N₀`. -/
theorem phi_taylor_block (t N₀ m : ℝ) (hN : 0 < N₀) (hm : 0 ≤ m) (k : ℕ) :
    |(-(t / (2 * π)) * Real.log (N₀ + m)) - (-(t / (2 * π)) * Real.log N₀)
        - ∑ j ∈ Finset.Icc 1 k, vkCoef t N₀ j * m ^ j|
      ≤ (|t| / (2 * π)) * (m / N₀) ^ (k + 1) := by
  set u : ℝ := m / N₀ with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  -- log difference
  have hlogdiff : Real.log (N₀ + m) - Real.log N₀ = Real.log (1 + u) := by
    rw [hu, ← Real.log_div (by positivity) hN.ne']
    congr 1
    field_simp
  -- the coefficient sum equals `−(t/2π)·∑ (−1)^{j−1} u^j / j`
  have hcoefsum : ∑ j ∈ Finset.Icc 1 k, vkCoef t N₀ j * m ^ j
      = -(t / (2 * π)) * ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * u ^ j / (j : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl (fun j hj => ?_)
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hupow : u ^ j = m ^ j / N₀ ^ j := by rw [hu, div_pow]
    rw [vkCoef, hupow]
    field_simp
  -- assemble the bracket as `−(t/2π)·remainder`
  have hbr : (-(t / (2 * π)) * Real.log (N₀ + m)) - (-(t / (2 * π)) * Real.log N₀)
        - ∑ j ∈ Finset.Icc 1 k, vkCoef t N₀ j * m ^ j
      = -(t / (2 * π)) * (Real.log (1 + u)
          - ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * u ^ j / (j : ℝ)) := by
    rw [hcoefsum]
    have : (-(t / (2 * π)) * Real.log (N₀ + m)) - (-(t / (2 * π)) * Real.log N₀)
        = -(t / (2 * π)) * (Real.log (N₀ + m) - Real.log N₀) := by ring
    rw [this, hlogdiff]; ring
  rw [hbr, abs_mul]
  have hcoef : |-(t / (2 * π))| = |t| / (2 * π) := by
    rw [abs_neg, abs_div]
    congr 1
    rw [abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  rw [hcoef]
  have hrem := log_series_remainder k hu0
  calc |t| / (2 * π) * |Real.log (1 + u)
          - ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * u ^ j / (j : ℝ)|
      ≤ |t| / (2 * π) * (u ^ (k + 1) / (k + 1)) := by
        apply mul_le_mul_of_nonneg_left hrem (by positivity)
    _ ≤ |t| / (2 * π) * u ^ (k + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ) + 1)]
        nlinarith [pow_nonneg hu0 (k + 1)]

/-- **VK-TAYLOR (freeze form).**  With integer radii `P, Y` and `0 ≤ t`, the block
remainder is `≤ 2·(t/2π)·((P+Y)/N₀)^{k+1}` for `0 ≤ m ≤ P+Y < N₀`. -/
theorem phi_taylor_block_PY (t : ℝ) (ht : 0 ≤ t) (N₀ P Y : ℕ) (m : ℝ)
    (hN : 0 < (N₀ : ℝ)) (hm : 0 ≤ m) (hmPY : m ≤ (P : ℝ) + Y) (k : ℕ) :
    |(-(t / (2 * π)) * Real.log ((N₀ : ℝ) + m)) - (-(t / (2 * π)) * Real.log N₀)
        - ∑ j ∈ Finset.Icc 1 k, vkCoef t N₀ j * m ^ j|
      ≤ 2 * (t / (2 * π)) * (((P : ℝ) + Y) / N₀) ^ (k + 1) := by
  have hbase := phi_taylor_block t N₀ m hN hm k
  have habs : |t| = t := abs_of_nonneg ht
  rw [habs] at hbase
  refine hbase.trans ?_
  have hbasePos : 0 ≤ t / (2 * π) := by positivity
  have hdiv : m / N₀ ≤ ((P : ℝ) + Y) / N₀ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hmPY (by positivity)
  have hmono : (m / N₀) ^ (k + 1) ≤ (((P : ℝ) + Y) / N₀) ^ (k + 1) :=
    pow_le_pow_left₀ (by positivity) hdiv (k + 1)
  have hPYnn : (0 : ℝ) ≤ (((P : ℝ) + Y) / N₀) ^ (k + 1) := by positivity
  calc t / (2 * π) * (m / N₀) ^ (k + 1)
      ≤ t / (2 * π) * (((P : ℝ) + Y) / N₀) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left hmono hbasePos
    _ ≤ 2 * (t / (2 * π)) * (((P : ℝ) + Y) / N₀) ^ (k + 1) := by nlinarith [hbasePos, hPYnn]

end Salt.Vk
