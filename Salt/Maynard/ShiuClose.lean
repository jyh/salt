/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.ShiuTuned
import Salt.Maynard.ShiuClasses
import Salt.Maynard.ShiuGraded
import Salt.Maynard.ShiuBlocks

/-!
# ShiuClose — the S4-III/IV assemblies + S5: closing `ShiuCore` (wave W4)

This file closes the `N-SHIU-CORE` rung.  All analytic stones landed in earlier
waves (`ShiuTuned`, `ShiuClasses`, `ShiuGraded`, `ShiuSieve`, `ShiuBlocks`); this
file is the **composition**.

## W4-1 — the r-sum convergence stone (`rsum_tuned_summable` / `rsum_tuned_le`)

The per-bin class-IV product carries the tuned-Rankin decay
`exp(−(1/8)·r·log r + r^{1/4}·(log r/2 + C₀))` (from NEW-1), multiplied by an
abstract geometric factor `A^r` (the `τ(d) ≤ A^r`-grade weight, `A` a fixed
astronomically-large constant, **never evaluated**).  The factorial-scale decay
`exp(−(1/8) r log r)` dominates every geometric `A^r`, so the r-sum
`Σ_{r} A^r·exp(−(1/8) r log r + r^{1/4}(log r/2 + C₀))` converges to a
`z`-independent constant.  Route: an eventual domination `term(r) ≤ 2^{−r}`
(subpolynomial `r^{1/4} log r = o(r log r)` via `log t ≤ 2√t`, and
`A^r = exp(r log A) = exp(o(r log r))`), a geometric comparison for `Summable`,
then `Summable.sum_le_tsum`.
-/

open Finset

namespace Salt.Maynard

/-! ## W4-1 — the r-sum convergence stone -/

/-- The per-bin tuned-Rankin term, with an abstract geometric weight `A^r`. -/
noncomputable def rsumTerm (A C₀ : ℝ) (r : ℕ) : ℝ :=
  A ^ r * Real.exp (-((r : ℝ) * Real.log r) / 8
    + (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2 + C₀))

lemma rsumTerm_nonneg {A C₀ : ℝ} (hA : 0 ≤ A) (r : ℕ) : 0 ≤ rsumTerm A C₀ r := by
  unfold rsumTerm
  exact mul_nonneg (pow_nonneg hA r) (Real.exp_nonneg _)

/-- `log t ≤ 2·t^{1/2}` for `t > 0` (via `log √t ≤ √t − 1`). -/
lemma log_le_two_rpow_half {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * t ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hst
  have h2 : Real.log t = 2 * Real.log (Real.sqrt t) := by rw [Real.log_sqrt ht.le]; ring
  linarith

/-- **The eventual geometric domination.**  For `A ≥ 1`, `C₀ ≥ 0`, there is a
threshold `R` past which `rsumTerm A C₀ r ≤ (1/2)^r`. -/
lemma rsumTerm_le_geom {A C₀ : ℝ} (hA : 1 ≤ A) (hC₀ : 0 ≤ C₀) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → rsumTerm A C₀ r ≤ (1 / 2 : ℝ) ^ r := by
  have hApos : (0 : ℝ) < A := by linarith
  set M : ℝ := 8 * (Real.log A + Real.log 2 + 2) with hMdef
  refine ⟨max (max 16 (⌈C₀ ^ 4⌉₊ + 1)) (⌈Real.exp M⌉₊ + 1), fun r hr => ?_⟩
  have hr16 : 16 ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr
  have hrC : (⌈C₀ ^ 4⌉₊ + 1 : ℕ) ≤ r :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr
  have hrM : (⌈Real.exp M⌉₊ + 1 : ℕ) ≤ r := le_trans (le_max_right _ _) hr
  set t : ℝ := (r : ℝ) with htdef
  have ht1 : (1 : ℝ) ≤ t := by rw [htdef]; exact_mod_cast (by omega : 1 ≤ r)
  have ht0 : (0 : ℝ) < t := by linarith
  -- log t ≥ M
  have hlogt : M ≤ Real.log t := by
    have hexp : Real.exp M ≤ t := by
      have h1 : Real.exp M ≤ (⌈Real.exp M⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈Real.exp M⌉₊ + 1 : ℕ) : ℝ) ≤ t := by rw [htdef]; exact_mod_cast hrM
      push_cast at h2; linarith
    calc M = Real.log (Real.exp M) := (Real.log_exp M).symm
      _ ≤ Real.log t := Real.log_le_log (Real.exp_pos M) hexp
  -- C₀ ≤ t^{1/4}
  have hC0t : C₀ ≤ t ^ (1 / 4 : ℝ) := by
    have hle : C₀ ^ 4 ≤ t := by
      have h1 : (C₀ ^ 4 : ℝ) ≤ (⌈C₀ ^ 4⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈C₀ ^ 4⌉₊ + 1 : ℕ) : ℝ) ≤ t := by rw [htdef]; exact_mod_cast hrC
      push_cast at h2; linarith
    calc C₀ = (C₀ ^ 4) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_natCast C₀ 4, ← Real.rpow_mul hC₀]
            norm_num
      _ ≤ t ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hle (by norm_num)
  -- rpow monotonicity facts
  have h12_34 : t ^ (1 / 2 : ℝ) ≤ t ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have h34_1 : t ^ (3 / 4 : ℝ) ≤ t := by
    calc t ^ (3 / 4 : ℝ) ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
      _ = t := Real.rpow_one t
  have h14_pos : (0 : ℝ) < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have h14_12 : t ^ (1 / 4 : ℝ) * t ^ (1 / 2 : ℝ) = t ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add ht0]; norm_num
  have h14_14 : t ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ) = t ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add ht0]; norm_num
  -- P := t^{1/4}(log t/2 + C₀) ≤ 2 t^{3/4}
  have hP : t ^ (1 / 4 : ℝ) * (Real.log t / 2 + C₀) ≤ 2 * t ^ (3 / 4 : ℝ) := by
    have hlog : Real.log t / 2 + C₀ ≤ t ^ (1 / 2 : ℝ) + C₀ := by
      have := log_le_two_rpow_half ht0; linarith
    calc t ^ (1 / 4 : ℝ) * (Real.log t / 2 + C₀)
        ≤ t ^ (1 / 4 : ℝ) * (t ^ (1 / 2 : ℝ) + C₀) :=
          mul_le_mul_of_nonneg_left hlog h14_pos.le
      _ = t ^ (1 / 4 : ℝ) * t ^ (1 / 2 : ℝ) + C₀ * t ^ (1 / 4 : ℝ) := by ring
      _ ≤ t ^ (3 / 4 : ℝ) + t ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ) := by
          rw [h14_12]
          have : C₀ * t ^ (1 / 4 : ℝ) ≤ t ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ) := by
            rw [mul_comm C₀]; exact mul_le_mul_of_nonneg_left hC0t h14_pos.le
          linarith
      _ = t ^ (3 / 4 : ℝ) + t ^ (1 / 2 : ℝ) := by rw [h14_14]
      _ ≤ 2 * t ^ (3 / 4 : ℝ) := by linarith [h12_34]
  -- hmain : t log A + t log 2 + 2 t^{3/4} ≤ (t log t)/8
  have hmain : t * Real.log A + t * Real.log 2 + 2 * t ^ (3 / 4 : ℝ) ≤ t * Real.log t / 8 := by
    have hstep : Real.log A + Real.log 2 + 2 ≤ Real.log t / 8 := by
      rw [hMdef] at hlogt; linarith
    have hb : t * (Real.log A + Real.log 2 + 2) ≤ t * (Real.log t / 8) :=
      mul_le_mul_of_nonneg_left hstep ht0.le
    have h2t : 2 * t ^ (3 / 4 : ℝ) ≤ 2 * t := by linarith [h34_1]
    nlinarith [hb, h2t]
  -- A^r = exp(r log A);  (1/2)^r = exp(-r log 2)
  have hApow : A ^ r = Real.exp (t * Real.log A) := by
    rw [← Real.rpow_natCast A r, Real.rpow_def_of_pos hApos, htdef]; ring_nf
  have hHalf : (1 / 2 : ℝ) ^ r = Real.exp (-(t * Real.log 2)) := by
    rw [← Real.rpow_natCast (1 / 2 : ℝ) r, Real.rpow_def_of_pos (by norm_num), htdef]
    rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]; ring_nf
  -- assemble
  unfold rsumTerm
  rw [hApow, hHalf, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [htdef]
  have : t * Real.log A + (-((t) * Real.log t) / 8 + t ^ (1 / 4 : ℝ) * (Real.log t / 2 + C₀))
      ≤ -(t * Real.log 2) := by
    have hgoal := hP
    have hgoal2 := hmain
    nlinarith [hP, hmain]
  -- align the cast of r inside logs with t
  simpa [htdef] using this

/-- **W4-1 — the tuned r-sum is summable.** -/
lemma rsumTerm_summable {A C₀ : ℝ} (hA : 1 ≤ A) (hC₀ : 0 ≤ C₀) :
    Summable (rsumTerm A C₀) := by
  obtain ⟨R, hR⟩ := rsumTerm_le_geom hA hC₀
  have hgeo : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + R)) := by
    simpa [pow_add] using summable_geometric_two.mul_right ((1 / 2 : ℝ) ^ R)
  have hshift : Summable (fun k : ℕ => rsumTerm A C₀ (k + R)) := by
    apply Summable.of_nonneg_of_le (fun k => rsumTerm_nonneg (by linarith) (k + R)) _ hgeo
    intro k
    exact hR (k + R) (by omega)
  exact (summable_nat_add_iff R).mp hshift

/-- **W4-1 (consumer form).** The partial sums of the tuned r-term are bounded by a
`z`-independent constant `B = Σ' rsumTerm`, uniformly in the upper limit. -/
lemma rsum_tuned_le {A C₀ : ℝ} (hA : 1 ≤ A) (hC₀ : 0 ≤ C₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r₀ : ℕ,
      ∑ r ∈ Finset.Icc 2 r₀, rsumTerm A C₀ r ≤ B := by
  refine ⟨∑' r, rsumTerm A C₀ r, ?_, fun r₀ => ?_⟩
  · exact tsum_nonneg (fun r => rsumTerm_nonneg (by linarith) r)
  · exact Summable.sum_le_tsum _ (fun i _ => rsumTerm_nonneg (by linarith) i)
      (rsumTerm_summable hA hC₀)

/-! ## The class-II → capped-power structural reduction (S5 ingredient) -/

/-- **The class-II → capped-power reduction (verified verdict, catch #70 resolved).**
With budget `w ≥ W²` and secondary cut `W ≥ 2`, every class-II integer `n`
(`ρ = d.minFac ≤ W`, `c = shiuC w n ≤ W`) is divisible by `cappedPow W ρ` — the
minimal `ρ`-power exceeding `W`.  Greediness (`shiuC_mul_minFac_pow_gt`) gives
`w < c·ρ^{e_ρ} ≤ W·ρ^{e_ρ}`, so `W² ≤ w < W·ρ^{e_ρ}` forces `ρ^{e_ρ} > W`; hence
`e_ρ ≥ u_ρ` and `cappedPow W ρ = ρ^{u_ρ} ∣ ρ^{e_ρ} ∣ n`.

This is the honest reduction at threshold `W` (NOT `w`).  Catch #70's squarefree
counterexample fails here: squarefree `n` has `e_ρ = 1`, so `ρ^{e_ρ} = ρ > W`
forces `ρ > W`, contradicting class II's `ρ ≤ W` — the squarefree case simply is
not class II at this threshold. -/
theorem classII_dvd_cappedPow {n w W : ℕ} (hn : n ≠ 0) (hW : 2 ≤ W) (hwW : W ^ 2 ≤ w)
    (hcls : shiuClassII w W n) :
    cappedPow W ((shiuD w n).minFac) ∣ n := by
  obtain ⟨hd1, _hρW, hcW⟩ := hcls
  set ρ := (shiuD w n).minFac with hρ
  set e := n.factorization ρ with he
  have hρp : ρ.Prime := Nat.minFac_prime (by omega)
  have hρ2 : 2 ≤ ρ := hρp.two_le
  -- greediness: `w < c · ρ^e`, and `c ≤ W`
  have hgreedy : w < shiuC w n * ρ ^ e := shiuC_mul_minFac_pow_gt hn hd1
  have hstep : w < W * ρ ^ e := by
    calc w < shiuC w n * ρ ^ e := hgreedy
      _ ≤ W * ρ ^ e := Nat.mul_le_mul_right _ hcW
  -- `W² ≤ w < W·ρ^e` ⟹ `W < ρ^e`
  have hWlt : W < ρ ^ e := by
    have hmul : W * W < W * ρ ^ e := by
      calc W * W = W ^ 2 := by ring
        _ ≤ w := hwW
        _ < W * ρ ^ e := hstep
    exact lt_of_mul_lt_mul_left hmul (Nat.zero_le W)
  -- `e ≥ u_ρ = Nat.log ρ W + 1`
  have hlogle : ρ ^ (Nat.log ρ W) ≤ W := Nat.pow_log_le_self ρ (by omega)
  have hlt : ρ ^ (Nat.log ρ W) < ρ ^ e := lt_of_le_of_lt hlogle hWlt
  have huρ : Nat.log ρ W + 1 ≤ e := (Nat.pow_lt_pow_iff_right hρ2).mp hlt
  calc cappedPow W ρ = ρ ^ (Nat.log ρ W + 1) := rfl
    _ ∣ ρ ^ e := pow_dvd_pow ρ huρ
    _ ∣ n := he ▸ Nat.ordProj_dvd n ρ

/-! ## The degenerate class (`d = 1`, fully `w`-smooth) — the crude bound (S5 ingredient) -/

/-- **The degenerate-class bound.**  Every fully `w`-smooth `n` (`d = 1`, so
`n = c ≤ w`) lies in `[1, w]`, so its τ-mass in any residue class is at most the full
divisor-summatory `w·(1 + log w)` (`Salt.BV.sum_card_divisors_le`).  At the skeleton
scale `w = z^{α/3}` this is `z^{α/3}·log z`-junk, absorbed by the target's
`(z/φ(q))·log z ≥ z^{α}·log z`. -/
theorem classDeg_tau_le {w : ℕ} (hw : 1 ≤ w) (z q a : ℕ) :
    ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassDeg w n),
        (n.divisors.card : ℝ)
      ≤ (w : ℝ) * (1 + Real.log w) := by
  have hsub : (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassDeg w n)
      ⊆ Finset.Icc 1 w := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, _⟩, _, hdeg⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hdeg' : shiuD w n = 1 := hdeg
    have hcn : shiuC w n = n := by
      have h := shiuC_mul_shiuD hn0 w
      rw [hdeg', mul_one] at h; exact h
    rw [Finset.mem_Icc]
    exact ⟨hn1, hcn ▸ shiuC_le hw n⟩
  calc ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassDeg w n),
          (n.divisors.card : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 w, (n.divisors.card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ ≤ (w : ℝ) * (1 + Real.log w) := Salt.BV.sum_card_divisors_le w hw

end Salt.Maynard
