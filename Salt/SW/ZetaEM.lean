/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.ZetaApprox
import Salt.SW.DHContour

/-!
# Sharp ζ partial Euler–Maclaurin on the strip (T-BAL supplier, node R2)

Supplies T-BAL's R2 need: the sharp complex Euler–Maclaurin bound for the ζ-partials on the
closed critical strip `[1/2, 1)` with bounded height `|t| ≤ 1`.  The crude corpus lemma
`norm_sum_Icc_cpow_neg_le` (DHTrunc) carries no `ζ(s)` constant; this file delivers the sharp
form with the analytic-continuation constant identified.

## Route (reuse of the landed `Salt.ExpSum` Hardy–Littlewood apparatus)

`Salt.ExpSum.norm_zeta_sub_approx_le` already proves the exact shape
`‖ζ(s) − ∑_{n≤N} n^{−s} − N^{1−s}/(s−1)‖ ≤ ‖s‖·N^{−σ}/σ`, but only on the *upper* region
`{0 < Re s, 0 < Im s}` (its identity `zetaApprox` was continued into the upper half-plane only).
Our regime `|t| ≤ 1` straddles the real axis (`Im s ≤ 0` included).  We extend the underlying
identity across the real axis by re-running the identity theorem on the **convex open critical
strip** `{0 < Re s < 1}` (which avoids the pole `s = 1` and is convex ⟹ preconnected), seeded
from the landed upper-region `zetaApprox` at `1/2 + i` — one shot covers `Im s ≤ 0` too.

## Main results

* `zetaApprox_strip` — the Hardy–Littlewood identity on the whole open strip `0 < Re s < 1`.
* `norm_zeta_sub_approx_le_strip` — its bound form (the `‖s‖·N^{−σ}/σ` shape, no `Im s` gate).
* `zeta_partial_em` — the T-BAL R2 target, sharp form:
  `‖∑_{a≤y} a^{−s} − (y^{1−s}/(1−s) + ζ(s))‖ ≤ 8(1+‖s‖)·y^{−Re s}` for `1/2 ≤ Re s < 1`.
* `zetaHol_bound` — compactness bound on `zetaHol` over the strip rectangle (R2').
-/

namespace Salt.SW

open Complex Filter Finset MeasureTheory
open scoped Topology
open Salt.ExpSum

/-! ## The Hardy–Littlewood identity on the open critical strip `{0 < Re s < 1}` -/

/-- **The approximate identity on the open strip.**  For `0 < Re s < 1` and `N ≥ 1`,
`ζ(s) − ∑_{n≤N} n^{−s} − N^{1−s}/(s−1) = −s·∫_N^∞ {u} u^{−s−1} du`.  Extends the landed
`Salt.ExpSum.zetaApprox` (upper half-plane) across the real axis by the identity theorem on the
convex strip, seeded from the upper-region identity at `1/2 + i`. -/
lemma zetaApprox_strip {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re < 1) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (s - 1)
      = -s * zetaFracInt N s := by
  set S : Set ℂ := {z | 0 < z.re ∧ z.re < 1} with hSdef
  set P : ℂ → ℂ := fun z => riemannZeta z - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z))
    - (N : ℂ) ^ (1 - z) / (z - 1) with hP
  set Q : ℂ → ℂ := fun z => -z * zetaFracInt N z with hQ
  have hzne1 : ∀ z ∈ S, z ≠ 1 := by
    rintro z ⟨_, hz2⟩ rfl; simp only [Complex.one_re] at hz2; linarith
  have hopen : IsOpen S :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hconv : Convex ℝ S :=
    (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  have hterm_diff : ∀ z ∈ S, DifferentiableAt ℂ (fun z => (N : ℂ) ^ (1 - z) / (z - 1)) z := by
    intro z hz
    have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine DifferentiableAt.div ?_ (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr (hzne1 z hz))
    exact (differentiableAt_const (1 : ℂ) |>.sub differentiableAt_id).const_cpow (Or.inl hNne)
  have hsum_diff : ∀ z : ℂ,
      DifferentiableAt ℂ (fun z => ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z)) z := by
    intro z
    have hrw : (fun z : ℂ => ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z))
        = ∑ n ∈ Finset.Icc 1 N, (fun z : ℂ => (n : ℂ) ^ (-z)) := by
      funext w; rw [Finset.sum_apply]
    rw [hrw]
    apply DifferentiableAt.sum
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      rw [Finset.mem_Icc] at hn; exact Nat.cast_ne_zero.mpr (by omega)
    exact (differentiableAt_id.neg).const_cpow (Or.inl hn0)
  have hPana : AnalyticOnNhd ℂ P S := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen
    exact (((differentiableAt_riemannZeta (hzne1 z hz)).sub (hsum_diff z)).sub
      (hterm_diff z hz)).differentiableWithinAt
  have hQana : AnalyticOnNhd ℂ Q S := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen
    exact ((differentiableAt_id.neg).mul
      (zetaFracInt_differentiableAt N hN hz.1)).differentiableWithinAt
  have hz0 : (((1 / 2 : ℝ) : ℂ) + Complex.I) ∈ S := by
    refine ⟨?_, ?_⟩ <;>
      simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero] <;> norm_num
  have hfreq : ∃ᶠ z in 𝓝[≠] (((1 / 2 : ℝ) : ℂ) + Complex.I), P z = Q z := by
    have hev : ∀ᶠ z in 𝓝 (((1 / 2 : ℝ) : ℂ) + Complex.I), P z = Q z := by
      have hopenW : IsOpen {z : ℂ | 0 < z.re ∧ 0 < z.im} :=
        (isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt continuous_const Complex.continuous_im)
      have hmem : (((1 / 2 : ℝ) : ℂ) + Complex.I) ∈ {z : ℂ | 0 < z.re ∧ 0 < z.im} := by
        refine ⟨?_, ?_⟩ <;>
          simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, add_zero, zero_add] <;> norm_num
      filter_upwards [hopenW.mem_nhds hmem] with z hz
      exact zetaApprox hz.1 hz.2 hN
    exact (hev.filter_mono nhdsWithin_le_nhds).frequently
  exact hPana.eqOn_of_preconnected_of_frequently_eq hQana hconv.isPreconnected hz0 hfreq
    ⟨hσ, hσ1⟩

/-- **The bound form on the open strip.**  For `0 < Re s < 1` and `N ≥ 1`,
`‖ζ(s) − ∑_{n≤N} n^{−s} − N^{1−s}/(s−1)‖ ≤ ‖s‖·N^{−σ}/σ` (no `Im s` gate — the strip
identity holds across the real axis). -/
lemma norm_zeta_sub_approx_le_strip {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re < 1) {N : ℕ}
    (hN : 1 ≤ N) :
    ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (s - 1)‖
      ≤ ‖s‖ * (N : ℝ) ^ (-s.re) / s.re := by
  rw [zetaApprox_strip hσ hσ1 hN, norm_mul, norm_neg, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (zetaFracInt_bound hσ hN) (norm_nonneg s)

/-! ## The T-BAL R2 target: the sharp `8(1+‖s‖)·y^{−σ}` form -/

/-- **T-BAL R2, `zeta_partial_em` — the sharp ζ partial Euler–Maclaurin bound.**  For
`1/2 ≤ Re s < 1`, `|Im s| ≤ 1` (the DH-chain height grade) and `y ≥ 1`,
`‖∑_{a≤y} a^{−s} − (y^{1−s}/(1−s) + ζ(s))‖ ≤ 8·(1+‖s‖)·y^{−Re s}`.  Reduces to
`norm_zeta_sub_approx_le_strip` after the algebraic identity
`y^{1−s}/(s−1) = −y^{1−s}/(1−s)`, then `‖s‖/σ ≤ 2‖s‖ ≤ 8(1+‖s‖)` via `σ ≥ 1/2`. -/
lemma zeta_partial_em {s : ℂ} (hσ : 1 / 2 ≤ s.re) (hσ1 : s.re < 1) (_him : |s.im| ≤ 1)
    {y : ℕ} (hy : 1 ≤ y) :
    ‖(∑ a ∈ Finset.Icc 1 y, (a : ℂ) ^ (-s))
        - ((y : ℂ) ^ (1 - s) / (1 - s) + riemannZeta s)‖
      ≤ 8 * (1 + ‖s‖) * (y : ℝ) ^ (-s.re) := by
  have hσ0 : 0 < s.re := by linarith
  have hneg : (∑ a ∈ Finset.Icc 1 y, (a : ℂ) ^ (-s))
        - ((y : ℂ) ^ (1 - s) / (1 - s) + riemannZeta s)
      = -(riemannZeta s - (∑ a ∈ Finset.Icc 1 y, (a : ℂ) ^ (-s))
          - (y : ℂ) ^ (1 - s) / (s - 1)) := by
    rw [show (s - 1 : ℂ) = -(1 - s) from by ring, div_neg]; ring
  rw [hneg, norm_neg]
  refine le_trans (norm_zeta_sub_approx_le_strip hσ0 hσ1 hy) ?_
  have hyp : (0 : ℝ) ≤ (y : ℝ) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
  have hσinv : ‖s‖ / s.re ≤ 8 * (1 + ‖s‖) := by
    rw [div_le_iff₀ hσ0]
    nlinarith [norm_nonneg s, hσ,
      mul_nonneg (add_nonneg zero_le_one (norm_nonneg s)) (sub_nonneg.mpr hσ)]
  calc ‖s‖ * (y : ℝ) ^ (-s.re) / s.re
      = (‖s‖ / s.re) * (y : ℝ) ^ (-s.re) := by ring
    _ ≤ (8 * (1 + ‖s‖)) * (y : ℝ) ^ (-s.re) := mul_le_mul_of_nonneg_right hσinv hyp
    _ = 8 * (1 + ‖s‖) * (y : ℝ) ^ (-s.re) := by ring

/-! ## R2' — the compactness bound on `zetaHol` over the strip rectangle -/

/-- **R2', `zetaHol_bound`.**  `zetaHol` (the entire holomorphic part `ζ(s) − 1/(s−1)`,
`Salt.SW.DHContour`) is bounded on the compact rectangle `[1/2,1] × [−1,1]`.  Pure compactness:
`zetaHol` is entire hence continuous, the rectangle is closed and bounded in the proper space
`ℂ`, and a continuous function on a compact set is bounded. -/
lemma zetaHol_bound : ∃ Z₀ : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 →
    ‖zetaHol s‖ ≤ Z₀ := by
  set K : Set ℂ := {z | 1 / 2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ 1} with hKdef
  have hclosed : IsClosed K := by
    have h1 : IsClosed {z : ℂ | 1 / 2 ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {z : ℂ | z.re ≤ 1} := isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {z : ℂ | |z.im| ≤ 1} :=
      isClosed_le Complex.continuous_im.abs continuous_const
    have hEq : K = {z : ℂ | 1 / 2 ≤ z.re} ∩ ({z : ℂ | z.re ≤ 1} ∩ {z : ℂ | |z.im| ≤ 1}) := by
      ext z; simp only [hKdef, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [hEq]; exact h1.inter (h2.inter h3)
  have hsub : K ⊆ Metric.closedBall 0 2 := by
    intro z hz
    obtain ⟨hz1, hz2, hz3⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + 1 := add_le_add (by rw [abs_of_nonneg (by linarith)]; exact hz2) hz3
      _ = 2 := by norm_num
  have hbdd : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hsub
  have hcompact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hcont : ContinuousOn zetaHol K := zetaHol_differentiable.continuous.continuousOn
  obtain ⟨Z₀, hZ₀⟩ := hcompact.exists_bound_of_continuousOn hcont
  exact ⟨Z₀, fun s h1 h2 h3 => hZ₀ s ⟨h1, h2, h3⟩⟩

end Salt.SW
