/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHMollified
import Salt.SW.DHFinal
import Salt.SW.DHTrunc
import Salt.SW.DHBalance
import Salt.SW.ZeroFreeReal
import Salt.SW.Siegel

/-!
# The DH balance capstone (`T-BAL`) — the mollified main-term balance

This module assembles WP2's analytic-core balance, closing the shifted-detector
repulsion `dh_repulsion` (contract at `DHRepulsion.lean:262`). The design is the
JYH-ratified "T-BAL FREEZE" (`docs/exploration/s3-hb3-design.md`), the survivor
of a 3-angle adversarial panel with the refuters' repairs applied.

Frozen witnesses: `b := 40`, `k := 9`, `c := 2⁻²⁶`.
Parameters: `T := |ρ.im|+2`; `X := qT`; `L := log X + 2`; `z := ⌈X⌉`;
`x := X^40`; `N := ⌈x⌉`; `P := 3√q(1+log q)(1+‖ρ‖/ρ.re)`; `c₀ := 1/126848`.

## Rungs (Zeno stones)

* R1 `norm_bsum_kernel_zero_decay` [B] — the sharp inner Abel (DH-TRUNC-A
  instantiation): the character partial sums damped by the antitone kernel.
* R6 `zfr_harvest` [B] — the zero-free-region harvest wiring `zero_free_region_all`
  to the contract hypotheses.

Later rungs (R2–R5, R7, R8) are the multi-session analytic bulk; the wall is
recorded in `docs/blueprints/flags.md` (node `T-BAL`).

## Honesty (HB-ENGINE, R4)

NO twin claim. `dh_repulsion` is one input to WP2, itself gated behind R4
(beyond-level-½ / Kloosterman — the documented death rung).
-/

open Complex

noncomputable section

namespace Salt.SW

open Finset

/-! ## R6 — the zero-free-region harvest (`zfr_harvest`) -/

/-- **R6 — the ZFR harvest.** For a real primitive character `χ ≠ 1` mod `q` and a
non-real zero `ρ` of `L(·,χ)` with `9/10 ≤ Re ρ < 1`, the landed
`zero_free_region_all` (`c₀ = 1/126848`) harvests the balance's three geometric
facts at one constant `c₀`:
* the width lower bound `c₀/log(q(|Im ρ|+2)) ≤ 1 − Re ρ` (the `x^{1−ρ.re}` damping's
  ZFR floor — poison for `‖1−ρ‖`);
* the pole-distance bound `1/‖1−ρ‖ ≤ log(q(|Im ρ|+2))/c₀` (polylog, absorbed in `k`);
* the shifted-pole bound `1 ≤ ‖2−ρ‖`.
No new ZFR work — pure wiring of the landed region to the contract shape (K1). -/
theorem zfr_harvest {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (him : ρ.im ≠ 0)
    (hlo : 9 / 10 ≤ ρ.re) (hhi : ρ.re < 1) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ 1 - ρ.re ∧
      1 / ‖1 - ρ‖ ≤ Real.log ((q : ℝ) * (|ρ.im| + 2)) / c₀ ∧
      1 ≤ ‖2 - ρ‖ := by
  obtain ⟨c₀, hc₀, hregion⟩ := zero_free_region_all
  refine ⟨c₀, hc₀, ?_, ?_, ?_⟩
  · -- the width floor from the region, at the disjunct `ρ.im ≠ 0`
    have hre : (1 : ℝ) / 2 ≤ ρ.re := by linarith
    have hb := hregion q χ hχ hne hzero hre (Or.inr him)
    linarith
  · -- pole distance: `‖1 − ρ‖ ≥ 1 − ρ.re ≥ c₀/log X > 0`
    have hre : (1 : ℝ) / 2 ≤ ρ.re := by linarith
    have hb := hregion q χ hχ hne hzero hre (Or.inr him)
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hLpos : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
      apply Real.log_pos; nlinarith [abs_nonneg ρ.im, hq1]
    have hwidth : 0 < 1 - ρ.re := by
      have : 0 < c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := div_pos hc₀ hLpos
      linarith
    have hdist : 1 - ρ.re ≤ ‖1 - ρ‖ := by
      have h := Complex.abs_re_le_norm (1 - ρ)
      simp only [Complex.sub_re, Complex.one_re] at h
      calc 1 - ρ.re ≤ |1 - ρ.re| := le_abs_self _
        _ ≤ ‖1 - ρ‖ := h
    have hnpos : 0 < ‖1 - ρ‖ := lt_of_lt_of_le hwidth hdist
    -- `c₀/log X ≤ 1 - ρ.re ≤ ‖1-ρ‖` gives `1/‖1-ρ‖ ≤ log X / c₀`
    rw [div_le_div_iff₀ hnpos hc₀]
    have hcross : c₀ ≤ ‖1 - ρ‖ * Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
      have hb' : c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ 1 - ρ.re := by linarith [hb]
      have hle : c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ ‖1 - ρ‖ := le_trans hb' hdist
      rw [div_le_iff₀ hLpos] at hle
      linarith
    linarith [hcross]
  · -- `‖2 − ρ‖ ≥ Re(2−ρ) = 2 − ρ.re ≥ 1`
    have h := Complex.abs_re_le_norm (2 - ρ)
    simp only [Complex.sub_re] at h
    have h2re : ((2 : ℂ).re) = 2 := by norm_num
    rw [h2re] at h
    calc (1 : ℝ) ≤ 2 - ρ.re := by linarith
      _ ≤ |2 - ρ.re| := le_abs_self _
      _ ≤ ‖2 - ρ‖ := h

/-! ## R1 — the sharp inner Abel (`norm_bsum_kernel_zero_decay`, DH-TRUNC-A) -/

/-- **R1 — DH-TRUNC-A (the sharp inner Abel).** Instantiates the ranged summation-by-parts
primitive `norm_sum_smul_antitone_ranged_le` with the DECAYING partial-sum bound
`Q(n) = P·(n−1)^{−ρ.re}` (from `partial_sum_at_zero_small`, `P := 3√q(1+log q)(1+‖ρ‖/ρ.re)`)
and the antitone linear-kernel weights `w_b = (1 − a·b/x)₊`. For a real character's zero `ρ`
(`0 < Re ρ ≤ 1`) and any outer index `a ≥ 1`, `x > 0`, the kernel-damped character partial sum
decays: the two explicit terms carry the `(N/a)^{−ρ.re}` inner grade the extraction consumes. -/
theorem norm_bsum_kernel_zero_decay {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re ≤ 1)
    {a : ℕ} (_ha : 1 ≤ a) {x : ℝ} (hx : 0 < x) (B : ℕ) :
    ‖∑ b ∈ Finset.Icc 1 B,
        χ (b : ZMod q) * (b : ℂ) ^ (-ρ) * ((dhKernR (((a * b : ℕ) : ℝ) / x)) : ℂ)‖
      ≤ dhKernR (((a * B : ℕ) : ℝ) / x)
          * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) * (B : ℝ) ^ (-ρ.re))
        + ∑ i ∈ Finset.range B,
            (dhKernR (((a * i : ℕ) : ℝ) / x) - dhKernR (((a * (i + 1) : ℕ) : ℝ) / x))
              * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) * (i : ℝ) ^ (-ρ.re)) := by
  set P := 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) with hP
  set c : ℕ → ℂ := fun i => χ (i : ZMod q) * (i : ℂ) ^ (-ρ) with hc
  set w : ℕ → ℝ := fun i => dhKernR (((a * i : ℕ) : ℝ) / x) with hw
  set Q : ℕ → ℝ := fun n => P * (((n - 1 : ℕ)) : ℝ) ^ (-ρ.re) with hQ
  have hlogq : (0 : ℝ) ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hPnn : 0 ≤ P := by
    rw [hP]
    have h1 : (0 : ℝ) ≤ 1 + Real.log q := by linarith
    have h2 : (0 : ℝ) ≤ 1 + ‖ρ‖ / ρ.re := by positivity
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) h1)) h2
  have hρne : ρ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hc0 : c 0 = 0 := by
    rw [hc]; simp only [Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hρne), mul_zero]
  -- generic drop-of-index-0 reindex `range n ↔ Icc 1 (n−1)` when the 0-term vanishes.
  have hdrop : ∀ (g : ℕ → ℂ), g 0 = 0 →
      ∀ n, ∑ i ∈ Finset.range n, g i = ∑ i ∈ Finset.Icc 1 (n - 1), g i := by
    intro g hg0 n
    cases n with
    | zero => simp
    | succ m =>
      rw [Finset.sum_range_succ', hg0, add_zero, Nat.succ_sub_one,
          show Finset.Icc 1 m = Finset.Ico 1 (m + 1) from by
            ext k; simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff],
          Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm i 1])
  -- the ranged partial-sum bound (the decaying `Q`).
  have hpartial : ∀ n, ‖∑ i ∈ Finset.range n, c i‖ ≤ Q n := by
    intro n
    rw [hdrop c hc0 n]
    rcases Nat.eq_zero_or_pos (n - 1) with h0 | hpos
    · rw [h0, show Finset.Icc 1 (0 : ℕ) = ∅ from Finset.Icc_eq_empty (by omega),
        Finset.sum_empty, norm_zero, hQ]
      exact mul_nonneg hPnn (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · have hkey := partial_sum_at_zero_small χ hχ hq hzero hρ0 hρ1 hpos
      simp only [hc, hQ, hP]
      exact hkey
  -- the antitone nonneg kernel weights.
  have hanti : Antitone w := by
    intro i j hij
    simp only [hw, dhKernR]
    refine max_le_max (le_refl 0) ?_
    have hnat : ((a * i : ℕ) : ℝ) ≤ ((a * j : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul (le_refl a) hij
    have hle : ((a * i : ℕ) : ℝ) / x ≤ ((a * j : ℕ) : ℝ) / x :=
      (div_le_div_iff_of_pos_right hx).mpr hnat
    linarith
  have hw0 : ∀ i, 0 ≤ w i := fun i => dhKernR_nonneg _
  -- rewrite the goal's LHS as the `range (B+1)` smul-sum.
  have hwc0 : (fun i => w i • c i) 0 = 0 := by change w 0 • c 0 = 0; rw [hc0, smul_zero]
  have hLHS : ∑ b ∈ Finset.Icc 1 B,
        χ (b : ZMod q) * (b : ℂ) ^ (-ρ) * ((dhKernR (((a * b : ℕ) : ℝ) / x)) : ℂ)
      = ∑ i ∈ Finset.range (B + 1), w i • c i := by
    rw [hdrop (fun i => w i • c i) hwc0 (B + 1), Nat.add_sub_cancel]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [hw, hc, Complex.real_smul]
    ring
  rw [hLHS]
  refine le_trans (norm_sum_smul_antitone_ranged_le hpartial hanti hw0 (B + 1)) (le_of_eq ?_)
  rw [Nat.add_sub_cancel]
  simp only [hw, hQ, Nat.add_sub_cancel]

end Salt.SW

end
