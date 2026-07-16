/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.MobiusRate
import Salt.TwinBar.LambdaRate

/-!
# THE TROPHY — the effective Möbius summatory rate `mmuRate_holds : MmuRate`

This module lands the frozen Prop `Salt.TwinBar.MmuRate`
(`∀ A > 0, ∃ C x₀, ∀ y ≥ x₀, |M_μ(y)| ≤ C·y/(log y)^A`, `M_μ(y) = ∑_{n ≤ y} μ(n)`)
from the `1/ζ` smoothed-Perron contour spine landed in `Salt/SW/MobiusRate.lean`.

## Route (three phases, mirroring the ψ contour arc)

1. **EDGES** (`mmu1_contour_shift`). The smoothed Riesz mean
   `M₁_μ(x) = ∑_{n ≤ x} μ(n)(1 − n/x)` has the Perron representation `mmu1_eq_integral`. The
   contour `Re s = c = 1 + 1/log x` is shifted onto the shallow box `[σ₀, c] × [−T, T]`. Because
   `1/ζ` is analytic through the removable pole `s = 1` (`mmuG`), the rectangle boundary integral
   VANISHES with NO residue (`rectBI_right_split` on the differentiable `mmuG` integrand). The
   three box edges (`Re = σ₀`, `Im = ±T`) carry the constant bound `‖1/ζ‖ ≤ B_box` (from
   `zeta_inv_shallow`, `log⁷(|t|+2) ≤ log⁷(T+2)` on the box), while the truncation tail `|t| > T`
   on `Re = c` carries the constant bound `‖1/ζ(c+it)‖ ≤ ∑_n ‖μ(n)‖·n^{−c} ≤ 1 + 1/(c−1) = 1+log x`
   (`norm_zeta_inv_cline_le`, the Dirichlet-series bound — this eliminates the log⁷ tail-integral
   friction: on the c-line the bound is a CONSTANT in `t`, exactly like the ψ case).

2. **BUDGET** (`E_shape_bound_mmu`, `mmuRate_smoothed`). Parameters `L := log x`, `s := L^{1/10}`,
   `T := e^s = exp((log x)^{1/10})`, `σ₀ := 1 − c₄/log⁹(T+2)`, discharged against `zeta_inv_shallow`
   (edge bound) and `zeta_zero_free_region` (box non-vanishing). The saving is
   `x^{σ₀−1} = e^{−c₄·L/log⁹(T+2)} ≤ e^{−(c₄/512)·L^{1/10}}` since `log(T+2) ≤ 2s` ⇒
   `log⁹(T+2) ≤ 512 s⁹` and `L/s⁹ = s`. Each edge term `≤ K·x·(poly s)·e^{−γs}`, absorbed by
   `pow_le_C_exp` to `≤ K·x·e^{−(γ/2)s}`, which beats `x/(log x)^A` for every `A`.

3. **DE-SMOOTH** (`mmuRate_of_smoothed`, `mmuRate_holds`). `M₁_μ` is the Riesz mean; the sharp
   `M_μ` is recovered by the two-point de-smoothing `y·M₁(y) − x·M₁(x) = (y−x)·M_μ(⌊x⌋) + R`,
   `|R| ≤ (y−x+1)²`, choosing the width `h = x/(log x)^{A+1}`.

## III.3″ numeric sanity (mpmath / symbolic)

At `x = 10⁶`: `|M_μ(10⁶)| = 212` (known). `log(10⁶) = 13.8155`. For `A = 5`,
`x/log⁵x = 1.99`, so `C ≥ 212/1.99 ≈ 106.5` (the asymptotic saving has not dominated at 10⁶ — the
branch-max `C` is expected). Budget arithmetic at `log x = 100`, `A = 5`: `s = 100^{1/10} = 1.585`,
saving `x^{σ₀−1} = e^{−(c₄/512)·1.585}`; `L/log⁹(T+2) ≥ L^{1/10}/512` beats every fixed
`A·log log x` crossover at a finite (astronomically large) `x₀` absorbed by the existential.

All results axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no new
axioms.
-/

open MeasureTheory Complex Set ArithmeticFunction Filter
open scoped LSeries.notation ArithmeticFunction.Moebius Topology BigOperators

noncomputable section
namespace Salt.SW

/-! ## Phase 1a — the c-line Dirichlet-series bound `‖1/ζ(σ+it)‖ ≤ 1 + 1/(σ−1)` -/

/-- `∑'_{n≥1} n^{−σ} ≤ 1 + 1/(σ−1)` for `σ > 1` (the `n = 1` term plus the integral comparison
`∑_{n≥2} n^{−σ} ≤ ∫_1^∞ t^{−σ} dt = 1/(σ−1)`). -/
lemma tsum_rpow_neg_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, (n : ℝ) ^ (-σ) ≤ 1 + 1 / (σ - 1) := by
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  -- the shifted tail is bounded by the integral `1/(σ−1)`
  have htail : ∑' i : ℕ, ((i + 2 : ℕ) : ℝ) ^ (-σ) ≤ 1 / (σ - 1) := by
    apply Real.tsum_le_of_sum_range_le (fun i => Real.rpow_nonneg (by positivity) _)
    intro N
    -- antitone integral comparison on `[1, 1+N]`
    have hanti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Icc (1 : ℝ) (1 + (N : ℝ))) := by
      intro a ha b _ hab
      exact Real.rpow_le_rpow_of_nonpos (by simp only [mem_Icc] at ha; linarith [ha.1]) hab
        (by linarith)
    have hsi := AntitoneOn.sum_le_integral (x₀ := (1 : ℝ)) (a := N)
      (f := fun t : ℝ => t ^ (-σ)) hanti
    have hlhs : ∑ i ∈ Finset.range N, ((i + 2 : ℕ) : ℝ) ^ (-σ)
        = ∑ i ∈ Finset.range N, (fun t : ℝ => t ^ (-σ)) ((1 : ℝ) + ↑(i + 1)) := by
      apply Finset.sum_congr rfl; intro i _; congr 1; push_cast; ring
    have h1le : (1 : ℝ) ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
    have h0notmem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + (N : ℝ)) := by
      rw [Set.uIcc_of_le h1le]; intro hmem; linarith [hmem.1]
    have hint : ∫ t in (1 : ℝ)..(1 + (N : ℝ)), t ^ (-σ) ≤ 1 / (σ - 1) := by
      rw [integral_rpow (Or.inr ⟨by linarith, h0notmem⟩), Real.one_rpow,
        show ((-σ) + 1) = -(σ - 1) by ring]
      set u : ℝ := (1 + (N : ℝ)) ^ (-(σ - 1)) with hu
      have hupos : (0 : ℝ) ≤ u := Real.rpow_nonneg (by positivity) _
      have hule : u ≤ 1 := by
        rw [hu]; exact Real.rpow_le_one_of_one_le_of_nonpos h1le (by linarith)
      have e1 : (u - 1) / (-(σ - 1)) = (1 - u) * (σ - 1)⁻¹ := by
        rw [div_neg, ← neg_div, neg_sub, div_eq_mul_inv]
      rw [e1]
      calc (1 - u) * (σ - 1)⁻¹ ≤ 1 * (σ - 1)⁻¹ :=
            mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr (by linarith))
        _ = 1 / (σ - 1) := by rw [one_mul, one_div]
    calc ∑ i ∈ Finset.range N, ((i + 2 : ℕ) : ℝ) ^ (-σ)
        = ∑ i ∈ Finset.range N, (fun t : ℝ => t ^ (-σ)) ((1 : ℝ) + ↑(i + 1)) := hlhs
      _ ≤ ∫ t in (1 : ℝ)..(1 + (N : ℝ)), t ^ (-σ) := hsi
      _ ≤ 1 / (σ - 1) := hint
  -- reassemble `∑' n = (n=0) + (n=1) + tail`
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have h0 : ((0 : ℕ) : ℝ) ^ (-σ) = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
  have h1 : ((1 : ℕ) : ℝ) ^ (-σ) = 1 := by rw [Nat.cast_one, Real.one_rpow]
  rw [← hsplit]
  have hrange : ∑ i ∈ Finset.range 2, ((i : ℕ) : ℝ) ^ (-σ) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1]; ring
  rw [hrange]
  linarith [htail]

/-- **The c-line bound.** For `σ > 1` and any `t`, `‖(ζ(σ+it))⁻¹‖ ≤ 1 + 1/(σ−1)`, via the
Dirichlet series `1/ζ = ∑ μ(n) n^{−s}` majorized by `∑ n^{−σ} ≤ 1 + 1/(σ−1)`. -/
lemma norm_zeta_inv_cline_le {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ 1 + 1 / (σ - 1) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hsdef
  have hre : s.re = σ := by rw [hsdef]; simp
  have hs : 1 < s.re := by rw [hre]; exact hσ
  rw [← LSeries_moebius_eq_zeta_inv hs]
  have hsummable : Summable (fun n : ℕ => ‖LSeries.term ↗μ s n‖) :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hcomp : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := Real.summable_nat_rpow.mpr (by linarith)
  have hterm : ∀ n : ℕ, ‖LSeries.term ↗μ s n‖ ≤ (n : ℝ) ^ (-σ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.norm_term_eq, if_pos rfl]
      exact Real.rpow_nonneg (Nat.cast_nonneg 0) _
    · rw [LSeries.norm_term_eq, if_neg hn, hre, Real.rpow_neg (Nat.cast_nonneg n)]
      have hμ : ‖(↗μ : ℕ → ℂ) n‖ ≤ 1 := by
        have hcast : (↗μ : ℕ → ℂ) n = (((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℂ) := by
          push_cast; ring
        rw [hcast, Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hpow : (0 : ℝ) < (n : ℝ) ^ σ :=
        Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ
      rw [div_le_iff₀ hpow, inv_mul_cancel₀ hpow.ne']
      exact hμ
  calc ‖LSeries ↗μ s‖
      ≤ ∑' n : ℕ, ‖LSeries.term ↗μ s n‖ := norm_tsum_le_tsum_norm hsummable
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) := hsummable.tsum_le_tsum hterm hcomp
    _ ≤ 1 + 1 / (σ - 1) := tsum_rpow_neg_le hσ

/-! ## Phase 1b — the `mmuG` c-line integrability -/

/-- `Zc` is nonvanishing on the `c`-line `Re s = c > 1` (both `s − 1 ≠ 0` and `ζ ≠ 0`). -/
lemma Zc_cline_ne {c : ℝ} (hc : 1 < c) (v : ℝ) : Zc ((c : ℂ) + (v : ℂ) * I) ≠ 0 := by
  have hre : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
  have hne1 : (c : ℂ) + (v : ℂ) * I ≠ 1 := by
    intro h; rw [h] at hre; simp at hre; linarith
  rw [Zc_eq_of_ne hne1]
  exact mul_ne_zero (sub_ne_zero.mpr hne1)
    (riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; exact hc))

/-- The `M_μ` contour integrand `x^s/(s(s+1))·mmuG s` is integrable on the `c`-line
(`1 < c`): dominated by `(1 + 1/(c−1))·x^c·(c²+v²)⁻¹` (kernel `1/|s|²`-decay × the c-line
Dirichlet bound `‖1/ζ‖ ≤ 1 + 1/(c−1)`). -/
lemma mmu_contour_integrable {x : ℝ} (hx : 1 ≤ x) {c : ℝ} (hc1 : 1 < c) :
    Integrable (fun v : ℝ =>
      (x : ℂ) ^ ((c : ℂ) + v * I) / (((c : ℂ) + v * I) * ((c : ℂ) + v * I + 1))
        * mmuG ((c : ℂ) + v * I)) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
  have hcpos : (0 : ℝ) < c := by linarith
  have hdenne : ∀ v : ℝ, ((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1) ≠ 0 := fun v =>
    mul_ne_zero (s_ne_zero hcpos v) (s1_ne_zero hcpos v)
  -- continuity: kernel × `mmuG = (s−1)/Zc` on the line
  have hline : Continuous (fun v : ℝ => (c : ℂ) + v * I) := by fun_prop
  have hmmuGcont : Continuous (fun v : ℝ => mmuG ((c : ℂ) + v * I)) := by
    have hrw : (fun v : ℝ => mmuG ((c : ℂ) + v * I))
        = fun v : ℝ => (((c : ℂ) + v * I) - 1) / Zc ((c : ℂ) + v * I) := by
      funext v; rw [mmuG]
    rw [hrw]
    exact ((by fun_prop : Continuous fun v : ℝ => ((c : ℂ) + v * I) - 1).div
      (Zc_differentiable.continuous.comp hline) (fun v => Zc_cline_ne hc1 v))
  have hFcont : Continuous (fun v : ℝ =>
      (x : ℂ) ^ ((c : ℂ) + v * I) / (((c : ℂ) + v * I) * ((c : ℂ) + v * I + 1))
        * mmuG ((c : ℂ) + v * I)) := by
    apply Continuous.mul
    · apply Continuous.div
      · exact (by fun_prop : Continuous fun v : ℝ => (c : ℂ) + v * I).const_cpow (Or.inl hxC)
      · fun_prop
      · exact hdenne
    · exact hmmuGcont
  refine (Integrable.mono'
    ((integrable_inv_c_sq_add_sq hcpos).const_mul (x ^ c * (1 + 1 / (c - 1))))
    hFcont.aestronglyMeasurable ?_)
  filter_upwards with v
  have hre : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
  have hne1 : (c : ℂ) + (v : ℂ) * I ≠ 1 := by
    intro h; rw [h] at hre; simp at hre; linarith
  have hζ : riemannZeta ((c : ℂ) + (v : ℂ) * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; exact hc1)
  have h1 : ‖(x : ℂ) ^ ((c : ℂ) + v * I)‖ = x ^ c := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hre]
  have h2 : ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖ ≤ (c ^ 2 + v ^ 2)⁻¹ :=
    norm_inv_denom_le hcpos v
  have h3 : ‖mmuG ((c : ℂ) + v * I)‖ ≤ 1 + 1 / (c - 1) := by
    rw [mmuG_eq_zeta_inv hne1 hζ]; exact norm_zeta_inv_cline_le hc1 v
  have h3nn : (0 : ℝ) ≤ 1 + 1 / (c - 1) := by positivity
  have hxcnn : (0 : ℝ) ≤ x ^ c := by positivity
  calc ‖(x : ℂ) ^ ((c : ℂ) + v * I) / (((c : ℂ) + v * I) * ((c : ℂ) + v * I + 1))
          * mmuG ((c : ℂ) + v * I)‖
      = ‖(x : ℂ) ^ ((c : ℂ) + v * I)‖ * ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖
          * ‖mmuG ((c : ℂ) + v * I)‖ := by
        rw [norm_mul, norm_div, norm_inv, div_eq_mul_inv]
    _ ≤ x ^ c * (c ^ 2 + v ^ 2)⁻¹ * (1 + 1 / (c - 1)) := by rw [h1]; gcongr
    _ = x ^ c * (1 + 1 / (c - 1)) * (c ^ 2 + v ^ 2)⁻¹ := by ring

/-! ## Phase 1c — the residue-free contour-shift bound `mmu1_contour_shift` -/

set_option maxHeartbeats 1600000 in
-- The assembly threads the Perron identity, the Goursat split and four edge/tail integral
-- estimates through one `set`-heavy proof term; the elaborator needs headroom past the default.
/-- **Phase 1 — the residue-free contour-shift bound.** For `x ≥ 3`, a truncation height `T ≥ 2`,
a shallow abscissa `9/10 ≤ σ₀ < 1`, an edge bound `‖1/ζ‖ ≤ B_box` on the box (`hbox`), and no
zeros of `ζ` in the box (`hzf`), the smoothed Möbius mean satisfies the explicit contour bound.
The three box edges carry the constant `B_box`; the truncation tail carries the c-line Dirichlet
constant `1 + 1/(c−1) = 1 + log x`. NO residue term (the whole point of the `1/ζ` route). -/
theorem mmu1_contour_shift {x : ℝ} (hx : 3 ≤ x) {T σ₀ Bbox : ℝ}
    (hT : 2 ≤ T) (hσ₀lo : 9 / 10 ≤ σ₀) (hσ₀1 : σ₀ < 1) (hBbox : 0 ≤ Bbox)
    (hzf : ∀ ρ : ℂ, riemannZeta ρ = 0 → σ₀ ≤ ρ.re → ρ.re ≤ 1 + 1 / Real.log x →
        |ρ.im| ≤ T → False)
    (hbox : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 1 + 1 / Real.log x → |s.im| ≤ T → s ≠ 1 →
        riemannZeta s ≠ 0 → ‖(riemannZeta s)⁻¹‖ ≤ Bbox) :
    ‖Mmu1 x‖ ≤ (1 / (2 * Real.pi)) *
      (2 * ((1 + 1 / Real.log x) - σ₀) * Bbox * x ^ (1 + 1 / Real.log x) / T ^ 2
        + Bbox * x ^ σ₀ * (Real.pi / σ₀)
        + (Real.log x + 1) * x ^ (1 + 1 / Real.log x) * (2 / T)) := by
  classical
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
  have hlogx1 : (1 : ℝ) < Real.log x := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log x := Real.log_lt_log (Real.exp_pos 1)
          (lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hx)
  have hlogxpos : (0 : ℝ) < Real.log x := by linarith
  set c : ℝ := 1 + 1 / Real.log x with hcdef
  have hc1 : 1 < c := by
    have h : (0 : ℝ) < 1 / Real.log x := by positivity
    rw [hcdef]; linarith
  have hc2 : c < 2 := by
    have h : 1 / Real.log x < 1 := by rw [div_lt_one hlogxpos]; linarith
    rw [hcdef]; linarith
  have hcpos : (0 : ℝ) < c := by linarith
  have hc_sub : c - 1 = 1 / Real.log x := by rw [hcdef]; ring
  have hσ₀gt : (9 : ℝ) / 10 < σ₀ ∨ (9 : ℝ) / 10 = σ₀ := lt_or_eq_of_le hσ₀lo
  have hσ₀pos : (0 : ℝ) < σ₀ := by linarith
  have hσ₀c : σ₀ < c := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  -- the c-line Dirichlet bound `‖mmuG(c+vI)‖ ≤ log x + 1`
  have hcline_eq : 1 + 1 / (c - 1) = Real.log x + 1 := by rw [hc_sub, one_div_one_div]; ring
  have hcline : ∀ v : ℝ, ‖mmuG ((c : ℂ) + v * I)‖ ≤ Real.log x + 1 := by
    intro v
    have hre : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
    have hne1 : (c : ℂ) + (v : ℂ) * I ≠ 1 := by intro h; rw [h] at hre; simp at hre; linarith
    have hζ : riemannZeta ((c : ℂ) + (v : ℂ) * I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; exact hc1)
    rw [mmuG_eq_zeta_inv hne1 hζ, ← hcline_eq]; exact norm_zeta_inv_cline_le hc1 v
  -- the box bound `‖mmuG s‖ ≤ Bbox`
  have hmmuGbox : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ c → |s.im| ≤ T → s ≠ 1 → ‖mmuG s‖ ≤ Bbox := by
    intro s hsl hsu hsi hs1
    have hζ : riemannZeta s ≠ 0 := fun h0 => hzf s h0 hsl hsu hsi
    rw [mmuG_eq_zeta_inv hs1 hζ]; exact hbox s hsl hsu hsi hs1 hζ
  -- the integrand and its norm
  set F : ℂ → ℂ := fun s => (x : ℂ) ^ s / (s * (s + 1)) * mmuG s with hF
  have hFnorm : ∀ s : ℂ, ‖F s‖ = x ^ s.re * ‖(s * (s + 1))⁻¹‖ * ‖mmuG s‖ := by
    intro s
    simp only [hF]
    rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hxpos, div_eq_mul_inv, ← norm_inv]
  -- the rectangle
  set zc : ℂ := (σ₀ : ℂ) - (T : ℂ) * I with hzc
  set wc : ℂ := (c : ℂ) + (T : ℂ) * I with hwc
  have hzc_re : zc.re = σ₀ := by rw [hzc]; simp
  have hzc_im : zc.im = -T := by rw [hzc]; simp
  have hwc_re : wc.re = c := by rw [hwc]; simp
  have hwc_im : wc.im = T := by rw [hwc]; simp
  have hFana : DifferentiableOn ℂ F (closedRect zc wc) := by
    intro s hs
    rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, mem_reProdIm] at hs
    rw [Set.uIcc_of_le hσ₀c.le] at hs
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at hs
    obtain ⟨hsre, hsim⟩ := hs
    simp only [Set.mem_Icc] at hsre hsim
    have hsim' : |s.im| ≤ T := abs_le.mpr ⟨hsim.1, hsim.2⟩
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre; linarith [hsre.1]
    have hs1 : s + 1 ≠ 0 := fun h => by
      have : (s + 1).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.one_re] at this; linarith [hsre.1]
    have hZc : Zc s ≠ 0 := by
      by_cases he : s = 1
      · rw [he, Zc_one]; exact one_ne_zero
      · rw [Zc_eq_of_ne he]
        exact mul_ne_zero (sub_ne_zero.mpr he) (fun hζ => hzf s hζ hsre.1 hsre.2 hsim')
    have hker : DifferentiableAt ℂ (fun z => (x : ℂ) ^ z / (z * (z + 1))) s := by
      apply DifferentiableAt.div
      · exact differentiableAt_id.const_cpow (Or.inl hxC)
      · exact differentiableAt_id.mul (differentiableAt_id.add_const 1)
      · exact mul_ne_zero hs0 hs1
    have hFs : DifferentiableAt ℂ F s := by rw [hF]; exact hker.mul (mmuG_differentiableAt hZc)
    exact hFs.differentiableWithinAt
  -- Goursat rearrangement
  have hgour := rectBI_right_split hFana
  rw [hzc_re, hzc_im, hwc_re, hwc_im] at hgour
  set RIGHT : ℂ := ∫ v in (-T)..T, F ((c : ℂ) + v * I) with hRIGHT
  set TOPI : ℂ := ∫ u in σ₀..c, F ((u : ℂ) + (T : ℂ) * I) with hTOPI
  set BOTI : ℂ := ∫ u in σ₀..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I) with hBOTI
  set LEFT : ℂ := ∫ v in (-T)..T, F ((σ₀ : ℂ) + v * I) with hLEFT
  have hRnorm : ‖RIGHT‖ ≤ ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖ := by
    have heq : ‖RIGHT‖ = ‖TOPI - BOTI + I * LEFT‖ := by
      rw [← hgour, norm_mul, Complex.norm_I, one_mul]
    rw [heq]
    calc ‖TOPI - BOTI + I * LEFT‖
        ≤ ‖TOPI - BOTI‖ + ‖I * LEFT‖ := norm_add_le _ _
      _ ≤ ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]; linarith [norm_sub_le TOPI BOTI]
  -- integrability and Perron bridge
  have hFint : Integrable (fun v : ℝ => F ((c : ℂ) + v * I)) := by
    simp only [hF]; exact mmu_contour_integrable hx1 hc1
  have hbridge : Mmu1 x = (1 / (2 * Real.pi)) • ∫ v : ℝ, F ((c : ℂ) + v * I) := by
    rw [mmu1_eq_integral hx1 hc1]
    refine congrArg (fun z : ℂ => (1 / (2 * Real.pi)) • z) ?_
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp only [hF]
    have hrev : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
    have hne1v : (c : ℂ) + (v : ℂ) * I ≠ 1 := by intro h; rw [h] at hrev; simp at hrev; linarith
    have hζv : riemannZeta ((c : ℂ) + (v : ℂ) * I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by rw [hrev]; exact hc1)
    rw [mmuG_eq_zeta_inv hne1v hζv]
  -- truncation split
  have htrunc : (∫ v : ℝ, F ((c : ℂ) + v * I))
      = RIGHT + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I) := by
    rw [hRIGHT, intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T),
      integral_add_compl measurableSet_Ioc hFint]
  set Cbnd : ℝ := x ^ c * Bbox / T ^ 2 with hCbnd
  have hxcpos : (0 : ℝ) < x ^ c := by positivity
  have hCbnd_nn : (0 : ℝ) ≤ Cbnd := by rw [hCbnd]; positivity
  -- pointwise F-norm bound on a horizontal edge (Im = ±T)
  have hhoriz : ∀ (τ : ℝ), |τ| = T → ∀ u ∈ Set.uIoc σ₀ c, ‖F ((u : ℂ) + (τ : ℂ) * I)‖ ≤ Cbnd := by
    intro τ hτ u hu
    rw [Set.uIoc_of_le hσ₀c.le, Set.mem_Ioc] at hu
    have hsre : ((u : ℂ) + (τ : ℂ) * I).re = u := by simp
    have hsim : ((u : ℂ) + (τ : ℂ) * I).im = τ := by simp
    have hupos : (0 : ℝ) < u := by linarith [hu.1, hσ₀pos]
    have hne1 : (u : ℂ) + (τ : ℂ) * I ≠ 1 := by
      intro h
      have hτ0 : τ = 0 := by have h2 := congrArg Complex.im h; simpa using h2
      rw [hτ0, abs_zero] at hτ; linarith
    have hlogb : ‖mmuG ((u : ℂ) + (τ : ℂ) * I)‖ ≤ Bbox :=
      hmmuGbox _ (by rw [hsre]; linarith [hu.1]) (by rw [hsre]; linarith [hu.2])
        (by rw [hsim, hτ]) hne1
    have hden : ‖(((u : ℂ) + (τ : ℂ) * I) * (((u : ℂ) + (τ : ℂ) * I) + 1))⁻¹‖ ≤ (u ^ 2 + τ ^ 2)⁻¹ :=
      norm_inv_denom_le hupos τ
    have hττ : τ ^ 2 = T ^ 2 := by rw [← sq_abs, hτ]
    have hxexp : x ^ u ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hu.2])
    have hinvle : (u ^ 2 + τ ^ 2)⁻¹ ≤ (T ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr (by nlinarith [sq_nonneg u])
    rw [hFnorm, hsre]
    calc x ^ u * ‖(((u : ℂ) + (τ : ℂ) * I) * (((u : ℂ) + (τ : ℂ) * I) + 1))⁻¹‖
            * ‖mmuG ((u : ℂ) + (τ : ℂ) * I)‖
        ≤ x ^ u * (u ^ 2 + τ ^ 2)⁻¹ * Bbox :=
          mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
            (norm_nonneg _) (by positivity)
      _ ≤ x ^ c * (T ^ 2)⁻¹ * Bbox :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hxexp hinvle (by positivity) (by positivity)) hBbox
      _ = Cbnd := by rw [hCbnd]; ring
  -- horizontal integral bounds
  have hTOPb : ‖TOPI‖ ≤ (c - σ₀) * Cbnd := by
    rw [hTOPI]
    calc ‖∫ u in σ₀..c, F ((u : ℂ) + (T : ℂ) * I)‖
        ≤ Cbnd * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hhoriz T (abs_of_pos hTpos))
      _ = (c - σ₀) * Cbnd := by rw [abs_of_nonneg (by linarith)]; ring
  have hBOTb : ‖BOTI‖ ≤ (c - σ₀) * Cbnd := by
    rw [hBOTI]
    have hnegT : |(-T : ℝ)| = T := by rw [abs_neg, abs_of_pos hTpos]
    calc ‖∫ u in σ₀..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖
        ≤ Cbnd * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hhoriz (-T) hnegT)
      _ = (c - σ₀) * Cbnd := by rw [abs_of_nonneg (by linarith)]; ring
  -- left edge bound
  have hLEFTb : ‖LEFT‖ ≤ Bbox * x ^ σ₀ * (Real.pi / σ₀) := by
    rw [hLEFT]
    have hg_int : Integrable (fun v : ℝ => Bbox * x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹) :=
      (integrable_inv_c_sq_add_sq hσ₀pos).const_mul _
    have hre : ∀ v : ℝ, ((σ₀ : ℂ) + v * I).re = σ₀ := fun v => by simp
    have him : ∀ v : ℝ, ((σ₀ : ℂ) + v * I).im = v := fun v => by simp
    have hmapsto : Set.MapsTo (fun v : ℝ => (σ₀ : ℂ) + v * I) (Set.uIcc (-T) T)
        (closedRect zc wc) := by
      intro v hv
      rw [Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T), Set.mem_Icc] at hv
      rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, mem_reProdIm,
        Set.uIcc_of_le hσ₀c.le, Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)]
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Icc, hre v]; exact ⟨le_refl σ₀, hσ₀c.le⟩
      · rw [Set.mem_Icc, him v]; exact hv
    have hFleft_ii : IntervalIntegrable (fun v : ℝ => F ((σ₀ : ℂ) + v * I)) volume (-T) T :=
      (hFana.continuousOn.comp
        ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn)
        hmapsto).intervalIntegrable
    have hgnn : ∀ v : ℝ, (0 : ℝ) ≤ Bbox * x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
      fun v => mul_nonneg (mul_nonneg hBbox (by positivity)) (by positivity)
    have hpt : ∀ v ∈ Set.Icc (-T) T,
        ‖F ((σ₀ : ℂ) + v * I)‖ ≤ Bbox * x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
      intro v hv
      simp only [Set.mem_Icc] at hv
      have hvT : |v| ≤ T := abs_le.mpr ⟨hv.1, hv.2⟩
      have hsre : ((σ₀ : ℂ) + v * I).re = σ₀ := by simp
      have hsim : ((σ₀ : ℂ) + v * I).im = v := by simp
      have hne1 : (σ₀ : ℂ) + v * I ≠ 1 := by
        intro h; rw [h] at hsre; simp at hsre; linarith
      have hlogb : ‖mmuG ((σ₀ : ℂ) + v * I)‖ ≤ Bbox :=
        hmmuGbox _ (by rw [hsre]) (by rw [hsre]; linarith) (by rw [hsim]; exact hvT) hne1
      have hden : ‖(((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1))⁻¹‖ ≤ (σ₀ ^ 2 + v ^ 2)⁻¹ :=
        norm_inv_denom_le hσ₀pos v
      rw [hFnorm, hsre]
      calc x ^ σ₀ * ‖(((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1))⁻¹‖
              * ‖mmuG ((σ₀ : ℂ) + v * I)‖
          ≤ x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ * Bbox :=
            mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
              (norm_nonneg _) (by positivity)
        _ = Bbox * x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ := by ring
    calc ‖∫ v in (-T)..T, F ((σ₀ : ℂ) + v * I)‖
        ≤ ∫ v in (-T)..T, ‖F ((σ₀ : ℂ) + v * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ v in (-T)..T, Bbox * x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
          intervalIntegral.integral_mono_on (by linarith)
            hFleft_ii.norm hg_int.intervalIntegrable hpt
      _ ≤ ∫ v : ℝ, Bbox * x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
          rw [intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T)]
          exact setIntegral_le_integral hg_int (Filter.Eventually.of_forall hgnn)
      _ = Bbox * x ^ σ₀ * (Real.pi / σ₀) := by
          rw [integral_const_mul, integral_inv_sq_add hσ₀pos]
  -- tail bound on the vertical `Re = c` line
  have hcompl_meas : MeasurableSet (Set.Ioc (-T) T)ᶜ := measurableSet_Ioc.compl
  have hTAILb : ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖
      ≤ (Real.log x + 1) * x ^ c * (2 / T) := by
    have hFint_on : IntegrableOn (fun v : ℝ => F ((c : ℂ) + v * I)) (Set.Ioc (-T) T)ᶜ :=
      hFint.integrableOn
    have hg_int : IntegrableOn
        (fun v : ℝ => (Real.log x + 1) * x ^ c * (c ^ 2 + v ^ 2)⁻¹) (Set.Ioc (-T) T)ᶜ :=
      ((integrable_inv_c_sq_add_sq hcpos).const_mul _).integrableOn
    calc ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖
        ≤ ∫ v in (Set.Ioc (-T) T)ᶜ, ‖F ((c : ℂ) + v * I)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v in (Set.Ioc (-T) T)ᶜ, (Real.log x + 1) * x ^ c * (c ^ 2 + v ^ 2)⁻¹ := by
          refine setIntegral_mono_on hFint_on.norm hg_int hcompl_meas ?_
          intro v _
          have hsre : ((c : ℂ) + v * I).re = c := by simp
          have hlogb : ‖mmuG ((c : ℂ) + v * I)‖ ≤ Real.log x + 1 := hcline v
          have hden : ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖ ≤ (c ^ 2 + v ^ 2)⁻¹ :=
            norm_inv_denom_le hcpos v
          rw [hFnorm, hsre]
          calc x ^ c * ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖
                  * ‖mmuG ((c : ℂ) + v * I)‖
              ≤ x ^ c * (c ^ 2 + v ^ 2)⁻¹ * (Real.log x + 1) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
                  (norm_nonneg _) (by positivity)
            _ = (Real.log x + 1) * x ^ c * (c ^ 2 + v ^ 2)⁻¹ := by ring
      _ = (Real.log x + 1) * x ^ c * ∫ v in (Set.Ioc (-T) T)ᶜ, (c ^ 2 + v ^ 2)⁻¹ := by
          rw [integral_const_mul]
      _ ≤ (Real.log x + 1) * x ^ c * (2 / T) :=
          mul_le_mul_of_nonneg_left (tail_lorentzian_le hcpos hTpos) (by positivity)
  -- assemble
  have hcombine : ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
      ≤ 2 * (c - σ₀) * Bbox * x ^ c / T ^ 2 + Bbox * x ^ σ₀ * (Real.pi / σ₀) := by
    have hstep : ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
        ≤ (c - σ₀) * Cbnd + (c - σ₀) * Cbnd + Bbox * x ^ σ₀ * (Real.pi / σ₀) := by
      linarith [hTOPb, hBOTb, hLEFTb]
    calc ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
        ≤ (c - σ₀) * Cbnd + (c - σ₀) * Cbnd + Bbox * x ^ σ₀ * (Real.pi / σ₀) := hstep
      _ = 2 * (c - σ₀) * Bbox * x ^ c / T ^ 2 + Bbox * x ^ σ₀ * (Real.pi / σ₀) := by
          rw [hCbnd]; ring
  rw [hbridge, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [htrunc]
  calc ‖RIGHT + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖
      ≤ ‖RIGHT‖ + ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖ := norm_add_le _ _
    _ ≤ (2 * (c - σ₀) * Bbox * x ^ c / T ^ 2 + Bbox * x ^ σ₀ * (Real.pi / σ₀))
          + (Real.log x + 1) * x ^ c * (2 / T) := by
        have h1 : ‖RIGHT‖
            ≤ 2 * (c - σ₀) * Bbox * x ^ c / T ^ 2 + Bbox * x ^ σ₀ * (Real.pi / σ₀) :=
          le_trans hRnorm hcombine
        linarith [h1, hTAILb]
    _ = 2 * (c - σ₀) * Bbox * x ^ c / T ^ 2 + Bbox * x ^ σ₀ * (Real.pi / σ₀)
          + (Real.log x + 1) * x ^ c * (2 / T) := by ring

/-! ## Phase 2a — the polynomial-vs-exponential absorption -/

/-- **Absorption.** For `s ≥ 0`, `β > 0`, `k ≥ 1`, `s^k ≤ (k/β)^k·exp(β s)`. Route:
`exp(βs/k) ≥ 1 + βs/k ≥ βs/k` ⇒ `exp(βs) = (exp(βs/k))^k ≥ (βs/k)^k = β^k s^k/k^k`. -/
lemma pow_le_C_exp (k : ℕ) (hk : 1 ≤ k) {β : ℝ} (hβ : 0 < β) {s : ℝ} (hs : 0 ≤ s) :
    s ^ k ≤ ((k : ℝ) / β) ^ k * Real.exp (β * s) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hbase : β * s / k ≤ Real.exp (β * s / k) := by
    have := Real.add_one_le_exp (β * s / k); linarith
  have hbnn : 0 ≤ β * s / k := by positivity
  have hpow : (β * s / k) ^ k ≤ Real.exp (β * s) := by
    calc (β * s / k) ^ k ≤ (Real.exp (β * s / k)) ^ k := pow_le_pow_left₀ hbnn hbase k
      _ = Real.exp (β * s) := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  have hlhs : (β * s / k) ^ k = β ^ k * s ^ k / (k : ℝ) ^ k := by rw [div_pow, mul_pow]
  rw [hlhs, div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ k)] at hpow
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < β ^ k)]
  nlinarith [hpow]

/-- The `sq_le_C_exp`-style absorption used in the budget: for `s ≥ 1`, `0 < a ≤ γ`,
`s^k·exp(−γs) ≤ (2k/a)^k·exp(−(a/2)s)` — a poly factor absorbed into a slightly weaker exp decay. -/
lemma pow_exp_absorb (k : ℕ) (hk : 1 ≤ k) {a : ℝ} (ha : 0 < a) {s : ℝ} (hs : 1 ≤ s)
    {γ : ℝ} (hγ : a ≤ γ) :
    s ^ k * Real.exp (-(γ * s)) ≤ ((k : ℝ) / (a / 2)) ^ k * Real.exp (-(a / 2 * s)) := by
  have hs0 : 0 ≤ s := by linarith
  have hpow : s ^ k ≤ ((k : ℝ) / (a / 2)) ^ k * Real.exp (a / 2 * s) :=
    pow_le_C_exp k hk (β := a / 2) (by positivity) hs0
  calc s ^ k * Real.exp (-(γ * s))
      ≤ (((k : ℝ) / (a / 2)) ^ k * Real.exp (a / 2 * s)) * Real.exp (-(γ * s)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = ((k : ℝ) / (a / 2)) ^ k * Real.exp (a / 2 * s - γ * s) := by
        rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]
    _ ≤ ((k : ℝ) / (a / 2)) ^ k * Real.exp (-(a / 2 * s)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ γ - a) hs0])

/-! ## Phase 2b — the shifted-contour decay and the smoothed rate -/

set_option maxHeartbeats 4000000 in
-- The decay threads the contour-shift bound, the shallow-window discharge against
-- `zeta_inv_shallow` / `zeta_zero_free_region`, and three edge-term absorptions through one
-- `set`-heavy proof term; the elaborator needs headroom past the default.
/-- **Phase 2 — the smoothed-contour decay.** There are `dd, K > 0` and a threshold with
`‖M₁_μ(x)‖ ≤ K·x·exp(−dd·(log x)^{1/10})` for all large `x`. Parameters `s = (log x)^{1/10}`,
`T = e^s`, `σ₀ = 1 − c₄'/log⁹(T+2)` with `c₄' = min c₄ c₃`; the saving
`x^{σ₀−1} ≤ e^{−(c₄'/512)s}` (from `log⁹(T+2) ≤ 512·s⁹` and `L/s⁹ = s`) beats every log-power. -/
theorem mmu1_shift_decay :
    ∃ (dd K X₀ : ℝ), 0 < dd ∧ 0 < K ∧ ∀ x : ℝ, X₀ ≤ x →
      ‖Mmu1 x‖ ≤ K * x * Real.exp (-(dd * (Real.log x) ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c₄, hc₄pos, C, hCpos, Hinv⟩ := zeta_inv_shallow
  obtain ⟨c₃, hc₃pos, Hzfr⟩ := zeta_zero_free_region
  set c₄' : ℝ := min c₄ c₃ with hc₄'def
  have hc₄'pos : 0 < c₄' := lt_min hc₄pos hc₃pos
  have hc₄'c₄ : c₄' ≤ c₄ := min_le_left _ _
  have hc₄'c₃ : c₄' ≤ c₃ := min_le_right _ _
  set γ : ℝ := c₄' / 512 with hγdef
  have hγpos : 0 < γ := by rw [hγdef]; positivity
  set a : ℝ := min γ 1 with hadef
  have hapos : 0 < a := lt_min hγpos (by norm_num)
  have haγ : a ≤ γ := min_le_left _ _
  have ha1 : a ≤ 1 := min_le_right _ _
  have hCnn : (0 : ℝ) ≤ C := hCpos.le
  set A7 : ℝ := (((7 : ℕ) : ℝ) / (a / 2)) ^ 7 with hA7
  set A10 : ℝ := (((10 : ℕ) : ℝ) / (a / 2)) ^ 10 with hA10
  have hA7pos : 0 < A7 := by rw [hA7]; positivity
  have hA10pos : 0 < A10 := by rw [hA10]; positivity
  set K : ℝ := (1 / (2 * Real.pi)) *
      (2 * (11 / 10) * (128 * C) * Real.exp 1 * A7
        + (128 * C) * (10 * Real.pi / 9) * A7
        + 4 * Real.exp 1 * A10) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have he1 := Real.exp_pos 1
    have hpi := Real.pi_pos
    positivity
  suffices h : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Mmu1 x‖ ≤ K * x * Real.exp (-(a / 2 * (Real.log x) ^ ((1 : ℝ) / 10))) by
    rw [Filter.eventually_atTop] at h
    obtain ⟨X₀, hX₀⟩ := h
    exact ⟨a / 2, K, X₀, by positivity, hKpos, hX₀⟩
  have htend : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ ((9 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp Real.tendsto_log_atTop
  have hcond9ev : ∀ᶠ x : ℝ in Filter.atTop, 10 * c₄' ≤ (Real.log x) ^ ((9 : ℝ) / 10) :=
    htend.eventually (Filter.eventually_ge_atTop (10 * c₄'))
  filter_upwards [Filter.eventually_ge_atTop (3 : ℝ), hcond9ev] with x hx3 hcond9
  have hxpos : (0 : ℝ) < x := by linarith
  set Lg : ℝ := Real.log x with hLdef
  have hL1 : 1 < Lg := by
    rw [hLdef]; calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log x := Real.log_lt_log (Real.exp_pos 1)
          (lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hx3)
  have hLpos : 0 < Lg := by linarith
  set sg : ℝ := Lg ^ ((1 : ℝ) / 10) with hsdef
  have hs1 : 1 ≤ sg := by
    rw [hsdef]; calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 10) := (Real.one_rpow _).symm
      _ ≤ Lg ^ ((1 : ℝ) / 10) := Real.rpow_le_rpow (by norm_num) hL1.le (by norm_num)
  have hspos : 0 < sg := by linarith
  have hs10 : sg ^ (10 : ℕ) = Lg := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le,
      show ((1 : ℝ) / 10) * ((10 : ℕ) : ℝ) = 1 by push_cast; ring, Real.rpow_one]
  have hs9 : sg ^ (9 : ℕ) = Lg ^ ((9 : ℝ) / 10) := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; congr 1; push_cast; ring
  have hcond9' : 10 * c₄' ≤ sg ^ (9 : ℕ) := by rw [hs9]; exact hcond9
  set Tg : ℝ := Real.exp sg with hTdef
  have hTpos : 0 < Tg := by rw [hTdef]; exact Real.exp_pos _
  have h2es : (2 : ℝ) ≤ Real.exp sg :=
    le_trans (le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)) (Real.exp_le_exp.mpr hs1)
  have hTge2 : (2 : ℝ) ≤ Tg := by rw [hTdef]; exact h2es
  set lg : ℝ := Real.log (Tg + 2) with hℓdef
  have hℓpos : 0 < lg := by rw [hℓdef]; exact Real.log_pos (by linarith)
  have hℓgts : sg < lg := by
    rw [hℓdef, hTdef]
    calc sg = Real.log (Real.exp sg) := (Real.log_exp sg).symm
      _ < Real.log (Real.exp sg + 2) := Real.log_lt_log (Real.exp_pos sg) (by linarith)
  have hℓ1 : 1 < lg := lt_of_le_of_lt hs1 hℓgts
  have hℓle : lg ≤ 2 * sg := by
    rw [hℓdef, hTdef]
    calc Real.log (Real.exp sg + 2) ≤ Real.log (2 * Real.exp sg) :=
          Real.log_le_log (by positivity) (by linarith [h2es])
      _ = Real.log 2 + sg := by rw [Real.log_mul (by norm_num) (Real.exp_pos sg).ne', Real.log_exp]
      _ ≤ 2 * sg := by
          have h2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num); linarith
  have hℓ9pos : 0 < lg ^ 9 := by positivity
  have hℓ9ge : sg ^ 9 ≤ lg ^ 9 := pow_le_pow_left₀ hspos.le hℓgts.le 9
  have hℓ9le : lg ^ 9 ≤ (2 * sg) ^ 9 := pow_le_pow_left₀ hℓpos.le hℓle 9
  have hℓ7le : lg ^ 7 ≤ (2 * sg) ^ 7 := pow_le_pow_left₀ hℓpos.le hℓle 7
  set σ₀ : ℝ := 1 - c₄' / lg ^ 9 with hσ₀def
  have hσ₀frac : c₄' / lg ^ 9 ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hℓ9pos (by norm_num)]
    calc c₄' * 10 = 10 * c₄' := by ring
      _ ≤ sg ^ 9 := hcond9'
      _ ≤ lg ^ 9 := hℓ9ge
      _ = 1 * lg ^ 9 := by ring
  have hσ₀pos : 0 < σ₀ := by rw [hσ₀def]; linarith
  have hσ₀lo : (9 : ℝ) / 10 ≤ σ₀ := by rw [hσ₀def]; linarith
  have hσ₀1 : σ₀ < 1 := by
    rw [hσ₀def]
    have hpp : 0 < c₄' / lg ^ 9 := by positivity
    linarith
  set Bbox : ℝ := C * lg ^ 7 with hBboxdef
  have hBboxnn : 0 ≤ Bbox := by rw [hBboxdef]; positivity
  have hBbox_le : Bbox ≤ 128 * C * sg ^ 7 := by
    rw [hBboxdef]
    calc C * lg ^ 7 ≤ C * (2 * sg) ^ 7 := by apply mul_le_mul_of_nonneg_left hℓ7le hCnn
      _ = 128 * C * sg ^ 7 := by ring
  -- discharge hbox
  have hbox : ∀ w : ℂ, σ₀ ≤ w.re → w.re ≤ 1 + 1 / Real.log x → |w.im| ≤ Tg → w ≠ 1 →
      riemannZeta w ≠ 0 → ‖(riemannZeta w)⁻¹‖ ≤ Bbox := by
    intro w hwl hwu hwi hw1 hwζ
    have hlogwpos : 0 < Real.log (|w.im| + 2) := Real.log_pos (by linarith [abs_nonneg w.im])
    have hlogwle : Real.log (|w.im| + 2) ≤ lg := by
      rw [hℓdef]; exact Real.log_le_log (by positivity) (by linarith [hwi])
    have hlogw9pos : 0 < Real.log (|w.im| + 2) ^ 9 := by positivity
    have hcond : 1 - c₄ / Real.log (|w.im| + 2) ^ 9 ≤ w.re := by
      have hd9 : Real.log (|w.im| + 2) ^ 9 ≤ lg ^ 9 := pow_le_pow_left₀ hlogwpos.le hlogwle 9
      have hbig : c₄' / lg ^ 9 ≤ c₄ / Real.log (|w.im| + 2) ^ 9 := by
        rw [div_le_div_iff₀ hℓ9pos hlogw9pos]
        exact mul_le_mul hc₄'c₄ hd9 (by positivity) hc₄pos.le
      have hh : σ₀ ≤ w.re := hwl
      rw [hσ₀def] at hh
      linarith [hbig]
    have hne : (w.re : ℂ) + (w.im : ℂ) * I ≠ 1 := by rw [Complex.re_add_im]; exact hw1
    have hb := Hinv w.re w.im hcond hne
    rw [Complex.re_add_im] at hb
    calc ‖(riemannZeta w)⁻¹‖ ≤ C * Real.log (|w.im| + 2) ^ 7 := hb
      _ ≤ C * lg ^ 7 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogwpos.le hlogwle 7) hCnn
      _ = Bbox := by rw [hBboxdef]
  -- discharge hzf
  have hzf : ∀ ρ : ℂ, riemannZeta ρ = 0 → σ₀ ≤ ρ.re → ρ.re ≤ 1 + 1 / Real.log x →
      |ρ.im| ≤ Tg → False := by
    intro ρ hρ0 hρl hρu hρi
    have hρhalf : (1 : ℝ) / 2 ≤ ρ.re := by linarith [hρl, hσ₀lo]
    have hreg := Hzfr hρ0 hρhalf
    have hlogρpos : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith [abs_nonneg ρ.im])
    have hlogρle : Real.log (|ρ.im| + 2) ≤ lg := by
      rw [hℓdef]; exact Real.log_le_log (by positivity) (by linarith [hρi])
    have h1 : c₃ / lg ≤ c₃ / Real.log (|ρ.im| + 2) :=
      div_le_div_of_nonneg_left hc₃pos.le hlogρpos hlogρle
    have h2 : σ₀ ≤ 1 - c₃ / lg := by
      have hh : ρ.re ≤ 1 - c₃ / lg := by linarith [hreg, h1]
      linarith [hρl]
    have hkey : c₃ / lg ≤ c₄' / lg ^ 9 := by rw [hσ₀def] at h2; linarith
    rw [div_le_div_iff₀ hℓpos hℓ9pos] at hkey
    have hℓ9eq : lg ^ 9 = lg ^ 8 * lg := by ring
    rw [hℓ9eq] at hkey
    have hℓ8gt1 : 1 < lg ^ 8 := one_lt_pow₀ hℓ1 (by norm_num)
    nlinarith [hkey, hc₄'c₃,
      mul_pos (mul_pos hc₃pos hℓpos) (show (0 : ℝ) < lg ^ 8 - 1 by linarith)]
  -- apply the contour shift
  have hEshift := mmu1_contour_shift hx3 hTge2 hσ₀lo hσ₀1 hBboxnn hzf hbox
  rw [← hLdef] at hEshift
  refine le_trans hEshift ?_
  -- saving facts
  have hxc : x ^ (1 + 1 / Lg) = Real.exp 1 * x := by
    have hxinvL : x ^ (1 / Lg) = Real.exp 1 := by
      rw [Real.rpow_def_of_pos hxpos, ← hLdef, mul_one_div, div_self hLpos.ne']
    rw [Real.rpow_add hxpos, Real.rpow_one, hxinvL]; ring
  have hT2 : Tg ^ 2 = Real.exp (2 * sg) := by rw [hTdef, sq, ← Real.exp_add]; congr 1; ring
  have hTinv : (2 : ℝ) / Tg = 2 * Real.exp (-sg) := by
    rw [hTdef, div_eq_mul_inv, ← Real.exp_neg]
  have hkeysav : sg * lg ^ 9 ≤ 512 * Lg := by
    have h1 : lg ^ 9 ≤ 512 * sg ^ 9 := by
      calc lg ^ 9 ≤ (2 * sg) ^ 9 := hℓ9le
        _ = 512 * sg ^ 9 := by ring
    calc sg * lg ^ 9 ≤ sg * (512 * sg ^ 9) := by apply mul_le_mul_of_nonneg_left h1 hspos.le
      _ = 512 * sg ^ 10 := by ring
      _ = 512 * Lg := by rw [hs10]
  have hσ₀m1 : σ₀ - 1 = -(c₄' / lg ^ 9) := by rw [hσ₀def]; ring
  have hle : Lg * (σ₀ - 1) ≤ -(γ * sg) := by
    have expand : Lg * (σ₀ - 1) = -(c₄' * Lg / lg ^ 9) := by rw [hσ₀m1]; ring
    rw [expand, hγdef, neg_le_neg_iff, div_mul_eq_mul_div,
      div_le_div_iff₀ (by norm_num : (0 : ℝ) < 512) hℓ9pos]
    nlinarith [mul_le_mul_of_nonneg_left hkeysav hc₄'pos.le]
  have hxσ : x ^ σ₀ ≤ Real.exp (-(γ * sg)) * x := by
    have hxeq : x = Real.exp Lg := by rw [hLdef]; exact (Real.exp_log hxpos).symm
    have hxσeq : x ^ σ₀ = Real.exp (Lg * σ₀) := by rw [Real.rpow_def_of_pos hxpos, ← hLdef]
    rw [hxσeq, show Real.exp (-(γ * sg)) * x = Real.exp (Lg - γ * sg) by
      rw [hxeq, ← Real.exp_add]; ring_nf]
    apply Real.exp_le_exp.mpr
    linarith [hle, show Lg * (σ₀ - 1) = Lg * σ₀ - Lg from by ring]
  -- absorption facts
  have hpe7a : sg ^ 7 * Real.exp (-(2 * sg)) ≤ A7 * Real.exp (-(a / 2 * sg)) :=
    pow_exp_absorb 7 (by norm_num) hapos hs1 (by linarith [ha1])
  have hpe7b : sg ^ 7 * Real.exp (-(γ * sg)) ≤ A7 * Real.exp (-(a / 2 * sg)) :=
    pow_exp_absorb 7 (by norm_num) hapos hs1 haγ
  have hpe10 : sg ^ 10 * Real.exp (-sg) ≤ A10 * Real.exp (-(a / 2 * sg)) := by
    rw [show (-sg : ℝ) = -(1 * sg) by ring]
    exact pow_exp_absorb 10 (by norm_num) hapos hs1 (by linarith [ha1])
  set W : ℝ := x * Real.exp (-(a / 2 * sg)) with hWdef
  have hcm : 0 ≤ (1 + 1 / Lg) - σ₀ := by
    have : 0 < 1 / Lg := by positivity
    linarith [hσ₀1]
  have hcM : (1 + 1 / Lg) - σ₀ ≤ 11 / 10 := by
    have h1Lg : 1 / Lg ≤ 1 := by rw [div_le_one hLpos]; linarith
    linarith [hσ₀lo, h1Lg]
  have hπσ : Real.pi / σ₀ ≤ 10 * Real.pi / 9 := by
    rw [div_le_div_iff₀ hσ₀pos (by norm_num)]; nlinarith [Real.pi_pos, hσ₀lo]
  have hLp1 : Lg + 1 ≤ 2 * sg ^ 10 := by rw [hs10]; linarith [hL1]
  -- the three term bounds
  have hP1 : 2 * ((1 + 1 / Lg) - σ₀) * Bbox * x ^ (1 + 1 / Lg) / Tg ^ 2
      ≤ 2 * (11 / 10) * (128 * C) * Real.exp 1 * A7 * W := by
    rw [hxc, hT2, div_eq_mul_inv, ← Real.exp_neg]
    have hfac : 2 * ((1 + 1 / Lg) - σ₀) * Bbox ≤ 2 * (11 / 10) * (128 * C * sg ^ 7) := by
      nlinarith [mul_le_mul hcM hBbox_le hBboxnn (by norm_num : (0 : ℝ) ≤ 11 / 10),
        hcm, hBboxnn, hBbox_le, mul_nonneg hcm hBboxnn]
    calc 2 * ((1 + 1 / Lg) - σ₀) * Bbox * (Real.exp 1 * x) * Real.exp (-(2 * sg))
        ≤ 2 * (11 / 10) * (128 * C * sg ^ 7) * (Real.exp 1 * x) * Real.exp (-(2 * sg)) := by
          apply mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hfac (by positivity)) (Real.exp_pos _).le
      _ = (2 * (11 / 10) * (128 * C) * Real.exp 1) * x * (sg ^ 7 * Real.exp (-(2 * sg))) := by ring
      _ ≤ (2 * (11 / 10) * (128 * C) * Real.exp 1) * x * (A7 * Real.exp (-(a / 2 * sg))) := by
          apply mul_le_mul_of_nonneg_left hpe7a (by positivity)
      _ = 2 * (11 / 10) * (128 * C) * Real.exp 1 * A7 * W := by rw [hWdef]; ring
  have hP2 : Bbox * x ^ σ₀ * (Real.pi / σ₀) ≤ (128 * C) * (10 * Real.pi / 9) * A7 * W := by
    have h1 : Bbox * x ^ σ₀ * (Real.pi / σ₀)
        ≤ (128 * C * sg ^ 7) * (Real.exp (-(γ * sg)) * x) * (10 * Real.pi / 9) := by
      apply mul_le_mul
      · exact mul_le_mul hBbox_le hxσ (Real.rpow_nonneg hxpos.le σ₀) (by positivity)
      · exact hπσ
      · exact div_nonneg Real.pi_pos.le (by linarith [hσ₀lo])
      · positivity
    calc Bbox * x ^ σ₀ * (Real.pi / σ₀)
        ≤ (128 * C * sg ^ 7) * (Real.exp (-(γ * sg)) * x) * (10 * Real.pi / 9) := h1
      _ = ((128 * C) * (10 * Real.pi / 9)) * x * (sg ^ 7 * Real.exp (-(γ * sg))) := by ring
      _ ≤ ((128 * C) * (10 * Real.pi / 9)) * x * (A7 * Real.exp (-(a / 2 * sg))) := by
          apply mul_le_mul_of_nonneg_left hpe7b (by positivity)
      _ = (128 * C) * (10 * Real.pi / 9) * A7 * W := by rw [hWdef]; ring
  have hP3 : (Lg + 1) * x ^ (1 + 1 / Lg) * (2 / Tg) ≤ 4 * Real.exp 1 * A10 * W := by
    rw [hxc, hTinv]
    have h1 : (Lg + 1) * (Real.exp 1 * x) * (2 * Real.exp (-sg))
        ≤ (2 * sg ^ 10) * (Real.exp 1 * x) * (2 * Real.exp (-sg)) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLp1 (by positivity))
        (by positivity)
    calc (Lg + 1) * (Real.exp 1 * x) * (2 * Real.exp (-sg))
        ≤ (2 * sg ^ 10) * (Real.exp 1 * x) * (2 * Real.exp (-sg)) := h1
      _ = (4 * Real.exp 1) * x * (sg ^ 10 * Real.exp (-sg)) := by ring
      _ ≤ (4 * Real.exp 1) * x * (A10 * Real.exp (-(a / 2 * sg))) := by
          apply mul_le_mul_of_nonneg_left hpe10 (by positivity)
      _ = 4 * Real.exp 1 * A10 * W := by rw [hWdef]; ring
  -- combine
  rw [hKdef]
  have hsum := add_le_add (add_le_add hP1 hP2) hP3
  calc (1 / (2 * Real.pi)) *
        (2 * ((1 + 1 / Lg) - σ₀) * Bbox * x ^ (1 + 1 / Lg) / Tg ^ 2
          + Bbox * x ^ σ₀ * (Real.pi / σ₀) + (Lg + 1) * x ^ (1 + 1 / Lg) * (2 / Tg))
      ≤ (1 / (2 * Real.pi)) *
          (2 * (11 / 10) * (128 * C) * Real.exp 1 * A7 * W
            + (128 * C) * (10 * Real.pi / 9) * A7 * W + 4 * Real.exp 1 * A10 * W) := by
        apply mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1 / (2 * Real.pi)) * (2 * (11 / 10) * (128 * C) * Real.exp 1 * A7
          + (128 * C) * (10 * Real.pi / 9) * A7 + 4 * Real.exp 1 * A10) * x
          * Real.exp (-(a / 2 * sg)) := by rw [hWdef]; ring

/-- **The smoothed rate** (the sanctioned PB-floor form): for every saving `A > 0`,
`‖M₁_μ(x)‖ ≤ C·x/(log x)^A` for `x` large. The exponential saving of `mmu1_shift_decay`
beats every fixed log-power (`u^{10A}·e^{−dd·u} → 0` at `u = (log x)^{1/10} → ∞`). -/
theorem mmuRate_smoothed : ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (x₀ : ℝ), 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
    ‖Mmu1 x‖ ≤ C * x / (Real.log x) ^ A := by
  obtain ⟨dd, K, X₀, hddpos, hKpos, hbound⟩ := mmu1_shift_decay
  intro A hA
  have htendv : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp Real.tendsto_log_atTop
  have htend0 : Filter.Tendsto
      (fun x : ℝ => (Real.log x) ^ A * Real.exp (-(dd * (Real.log x) ^ ((1 : ℝ) / 10))))
      atTop (𝓝 0) := by
    have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * A) dd hddpos).comp htendv
    refine hbase.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul hlog0, show (1 : ℝ) / 10 * (10 * A) = A by ring, neg_mul]
  have hev1 : ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ A * Real.exp (-(dd * (Real.log x) ^ ((1 : ℝ) / 10))) ≤ 1 := by
    filter_upwards [htend0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx
    exact hx
  have hev : ∀ᶠ x : ℝ in atTop, ‖Mmu1 x‖ ≤ K * x / (Real.log x) ^ A := by
    filter_upwards [hev1, Filter.eventually_ge_atTop X₀, Filter.eventually_ge_atTop (Real.exp 1)]
      with x hx1 hxX0 hxe
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
    have hLge1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hxe
    have hLApos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos (by linarith) A
    have hb := hbound x hxX0
    have hexple : Real.exp (-(dd * (Real.log x) ^ ((1 : ℝ) / 10))) ≤ 1 / (Real.log x) ^ A :=
      (le_div_iff₀ hLApos).mpr (by rw [mul_comm]; exact hx1)
    calc ‖Mmu1 x‖ ≤ K * x * Real.exp (-(dd * (Real.log x) ^ ((1 : ℝ) / 10))) := hb
      _ ≤ K * x * (1 / (Real.log x) ^ A) :=
          mul_le_mul_of_nonneg_left hexple (mul_nonneg hKpos.le hxpos.le)
      _ = K * x / (Real.log x) ^ A := by ring
  rw [Filter.eventually_atTop] at hev
  obtain ⟨x₀, hx₀⟩ := hev
  exact ⟨K, x₀, hKpos, hx₀⟩

/-! ## Phase 3 — de-smoothing `M₁_μ → M_μ` -/

/-- Real Riesz mean `∑_{n ≤ x} μ(n)(1 − n/x)` (the real value of `Mmu1`). -/
noncomputable def R1 (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (1 - (n : ℝ) / x)

/-- Weighted Möbius sum `∑_{n≤N} μ(n)·n`. -/
noncomputable def Tsum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (n : ℝ)

/-- The bridge: `Mmu1` is the real Riesz mean cast to `ℂ`. -/
lemma Mmu1_eq_ofReal (x : ℝ) (_hx : x ≠ 0) : Mmu1 x = ((R1 x : ℝ) : ℂ) := by
  rw [Mmu1, R1, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  push_cast
  ring

lemma norm_Mmu1_eq (x : ℝ) (hx : x ≠ 0) : ‖Mmu1 x‖ = |R1 x| := by
  rw [Mmu1_eq_ofReal x hx, Complex.norm_real, Real.norm_eq_abs]

/-- `x · R1 x = x · Mmu ⌊x⌋₊ − Tsum ⌊x⌋₊`. -/
lemma x_mul_R1 (x : ℝ) (hx : x ≠ 0) :
    x * R1 x = x * Salt.TwinBar.Mmu ⌊x⌋₊ - Tsum ⌊x⌋₊ := by
  rw [R1, Salt.TwinBar.Mmu, Tsum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  field_simp

/-- `Finset.Icc 1 N = Finset.Ioc 0 N` over ℕ. -/
lemma Icc_one_eq_Ioc_zero (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- Split of `Mmu` at `M ≤ N`. -/
lemma Mmu_split {M N : ℕ} (h : M ≤ N) :
    Salt.TwinBar.Mmu N
      = Salt.TwinBar.Mmu M + ∑ n ∈ Finset.Ioc M N, ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
  rw [Salt.TwinBar.Mmu, Salt.TwinBar.Mmu, Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) h]

/-- Split of `Tsum` at `M ≤ N`. -/
lemma Tsum_split {M N : ℕ} (h : M ≤ N) :
    Tsum N = Tsum M + ∑ n ∈ Finset.Ioc M N, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (n : ℝ) := by
  rw [Tsum, Tsum, Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) h]

/-- **The de-smoothing identity.** For `1 ≤ x ≤ y`,
`y·R1 y − x·R1 x = (y−x)·Mmu ⌊x⌋₊ + ∑_{⌊x⌋<n≤⌊y⌋} μ(n)(y−n)`. -/
lemma desmooth_identity {x y : ℝ} (hx : (1 : ℝ) ≤ x) (hxy : x ≤ y) :
    y * R1 y - x * R1 x
      = (y - x) * Salt.TwinBar.Mmu ⌊x⌋₊
        + ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (y - (n : ℝ)) := by
  have hx0 : x ≠ 0 := by linarith
  have hy0 : y ≠ 0 := by linarith
  have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hsum : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (y - (n : ℝ))
      = y * (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ))
        - (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (n : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [x_mul_R1 x hx0, x_mul_R1 y hy0, Mmu_split hfl, Tsum_split hfl, hsum]
  ring

/-- **The remainder bound.** For `1 ≤ x ≤ y`,
`|∑_{⌊x⌋<n≤⌊y⌋} μ(n)(y−n)| ≤ (y−x+1)²`. -/
lemma remainder_bound {x y : ℝ} (hx : (1 : ℝ) ≤ x) (hxy : x ≤ y) :
    |∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (y - (n : ℝ))| ≤ (y - x + 1) ^ 2 := by
  have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  set d := (y - x + 1) with hd
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  have hterm : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      |((ArithmeticFunction.moebius n : ℤ) : ℝ) * (y - (n : ℝ))| ≤ d := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hnle : (n : ℝ) ≤ y := le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by linarith))
    have hyn : 0 ≤ y - (n : ℝ) := by linarith
    have hμ : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hxfl : x - 1 < (⌊x⌋₊ : ℝ) := by have := Nat.lt_floor_add_one x; linarith
    have hnlb : (⌊x⌋₊ : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have hyd : y - (n : ℝ) ≤ d := by rw [hd]; linarith
    rw [abs_mul]
    calc |((ArithmeticFunction.moebius n : ℤ) : ℝ)| * |y - (n : ℝ)|
        ≤ 1 * |y - (n : ℝ)| := mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
      _ = y - (n : ℝ) := by rw [one_mul, abs_of_nonneg hyn]
      _ ≤ d := hyd
  calc |∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (y - (n : ℝ))|
      ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
          |((ArithmeticFunction.moebius n : ℤ) : ℝ) * (y - (n : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, d := Finset.sum_le_sum hterm
    _ = (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).card • d := by rw [Finset.sum_const]
    _ = ((⌊y⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) * d := by rw [Nat.card_Ioc, nsmul_eq_mul]
    _ ≤ d * d := by
        apply mul_le_mul_of_nonneg_right _ hd0
        rw [Nat.cast_sub hfl]
        have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
        have h2 : x - 1 < (⌊x⌋₊ : ℝ) := by have := Nat.lt_floor_add_one x; linarith
        rw [hd]; linarith
    _ = d ^ 2 := by ring

/-- **The trophy de-smoothing.** The smoothed Riesz-mean rate (real `x`) implies `MmuRate`. -/
theorem mmuRate_of_smoothed
    (hsm : ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (x₀ : ℝ), 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
        ‖Mmu1 x‖ ≤ C * x / (Real.log x) ^ A) :
    Salt.TwinBar.MmuRate := by
  intro A hA
  obtain ⟨C', x₀', hC'pos, hb0⟩ := hsm (2 * A + 2) (by linarith)
  have hbound : ∀ x : ℝ, 1 ≤ x → x₀' ≤ x →
      |R1 x| ≤ C' * x / (Real.log x) ^ (2 * A + 2) := by
    intro x hx1 hx0
    rw [← norm_Mmu1_eq x (by linarith)]
    exact hb0 x hx0
  have hev_e : ∀ᶠ z : ℝ in Filter.atTop, Real.exp 1 ≤ z := Filter.eventually_ge_atTop _
  have hev_x0 : ∀ᶠ z : ℝ in Filter.atTop, x₀' ≤ z := Filter.eventually_ge_atTop _
  have hev_3P : ∀ᶠ z : ℝ in Filter.atTop, 3 * (Real.log z) ^ (A + 1) ≤ z := by
    have hlo := isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) (A + 1) (by norm_num)
    filter_upwards [hlo.def (by norm_num : (0 : ℝ) < 1 / 3), Filter.eventually_ge_atTop (1 : ℝ)]
      with z hz hz1
    have hzpos : (0 : ℝ) < z := by linarith
    rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hzpos,
        abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hz1) _)] at hz
    linarith
  have key : ∀ᶠ (y : ℕ) in Filter.atTop,
      |Salt.TwinBar.Mmu y| ≤ (5 * C' + 2) * (y : ℝ) / (Real.log y) ^ A := by
    have E1 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev_e
    have E2 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev_x0
    have E3 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev_3P
    filter_upwards [E1, E2, E3] with y he hx0 h3P
    set Y : ℝ := (y : ℝ) with hY
    set Lg : ℝ := Real.log Y with hLdef
    set Q : ℝ := Lg ^ A with hQdef
    set P : ℝ := Lg ^ (A + 1) with hPdef
    have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le (Real.exp_pos 1) he
    have hY1 : (1 : ℝ) ≤ Y := le_trans (Real.one_le_exp (by norm_num)) he
    have hL1 : (1 : ℝ) ≤ Lg := by
      rw [hLdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
    have hLpos : (0 : ℝ) < Lg := by linarith
    have hPpos : (0 : ℝ) < P := by rw [hPdef]; exact Real.rpow_pos_of_pos hLpos _
    have hQpos : (0 : ℝ) < Q := by rw [hQdef]; exact Real.rpow_pos_of_pos hLpos _
    have hP1 : (1 : ℝ) ≤ P := by
      rw [hPdef]; calc (1 : ℝ) = (1 : ℝ) ^ (A + 1) := (Real.one_rpow _).symm
        _ ≤ Lg ^ (A + 1) := Real.rpow_le_rpow (by norm_num) hL1 (by linarith)
    have h3P' : 3 * P ≤ Y := h3P
    have hPY : P ≤ Y := by linarith
    set h : ℝ := Y / P with hh
    have hhpos : (0 : ℝ) < h := by rw [hh]; positivity
    have hhle : h ≤ Y := by rw [hh, div_le_iff₀ hPpos]; nlinarith [hP1, hYpos]
    have hYhle : Y ≤ Y + h := by linarith
    have hYh2 : Y + h ≤ 2 * Y := by linarith
    have hfloorY : ⌊Y⌋₊ = y := by rw [hY]; exact Nat.floor_natCast y
    have hPeq : P = Q * Lg := by
      rw [hPdef, hQdef, Real.rpow_add hLpos, Real.rpow_one]
    have hP2 : Lg ^ (2 * A + 2) = P * P := by
      rw [hPdef, show (2 * A + 2 : ℝ) = (A + 1) + (A + 1) by ring, Real.rpow_add hLpos]
    have hR1Y : |R1 Y| ≤ C' * Y / Lg ^ (2 * A + 2) := by
      have := hbound Y hY1 hx0; rwa [← hLdef] at this
    have hR1Yh : |R1 (Y + h)| ≤ C' * (Y + h) / (Real.log (Y + h)) ^ (2 * A + 2) :=
      hbound (Y + h) (by linarith) (by linarith)
    have hlogYh : Lg ≤ Real.log (Y + h) := by
      rw [hLdef]; exact Real.log_le_log hYpos hYhle
    have h2A2 : (0 : ℝ) ≤ 2 * A + 2 := by linarith
    have hden : Lg ^ (2 * A + 2) ≤ (Real.log (Y + h)) ^ (2 * A + 2) :=
      Real.rpow_le_rpow (by linarith) hlogYh h2A2
    have hT1 : (Y + h) * |R1 (Y + h)| ≤ 4 * C' * Y ^ 2 / Lg ^ (2 * A + 2) := by
      have hstep1 : (Y + h) * |R1 (Y + h)|
          ≤ (Y + h) * (C' * (Y + h) / (Real.log (Y + h)) ^ (2 * A + 2)) :=
        mul_le_mul_of_nonneg_left hR1Yh (by linarith)
      have hnum : C' * (Y + h) ^ 2 ≤ 4 * C' * Y ^ 2 := by
        nlinarith [mul_nonneg hC'pos.le (mul_nonneg (by linarith : (0 : ℝ) ≤ Y - h)
          (by linarith : (0 : ℝ) ≤ 3 * Y + h))]
      have hstep2 : (Y + h) * (C' * (Y + h) / (Real.log (Y + h)) ^ (2 * A + 2))
          ≤ 4 * C' * Y ^ 2 / Lg ^ (2 * A + 2) := by
        rw [show (Y + h) * (C' * (Y + h) / (Real.log (Y + h)) ^ (2 * A + 2))
              = C' * (Y + h) ^ 2 / (Real.log (Y + h)) ^ (2 * A + 2) by ring]
        exact div_le_div₀ (by positivity) hnum (by positivity) hden
      linarith
    have hT2 : Y * |R1 Y| ≤ C' * Y ^ 2 / Lg ^ (2 * A + 2) := by
      have := mul_le_mul_of_nonneg_left hR1Y (le_of_lt hYpos)
      rw [show Y * (C' * Y / Lg ^ (2 * A + 2)) = C' * Y ^ 2 / Lg ^ (2 * A + 2) by ring] at this
      exact this
    have hid := desmooth_identity hY1 hYhle
    rw [hfloorY] at hid
    set S : ℝ := ∑ n ∈ Finset.Ioc y ⌊Y + h⌋₊,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (Y + h - (n : ℝ)) with hSdef
    have hSbd : |S| ≤ (h + 1) ^ 2 := by
      have hr := remainder_bound hY1 hYhle
      rw [hfloorY] at hr
      rw [show Y + h - Y + 1 = h + 1 by ring] at hr
      exact hr
    have hMeq : h * Salt.TwinBar.Mmu y = (Y + h) * R1 (Y + h) - Y * R1 Y - S := by
      rw [show Y + h - Y = h by ring] at hid
      linarith [hid]
    have hcore : h * |Salt.TwinBar.Mmu y| ≤ 5 * C' * Y ^ 2 / Lg ^ (2 * A + 2) + (h + 1) ^ 2 := by
      have habs : h * |Salt.TwinBar.Mmu y| = |(Y + h) * R1 (Y + h) - Y * R1 Y - S| := by
        rw [← hMeq, abs_mul, abs_of_pos hhpos]
      rw [habs]
      calc |(Y + h) * R1 (Y + h) - Y * R1 Y - S|
          ≤ |(Y + h) * R1 (Y + h)| + |Y * R1 Y| + |S| := by
            calc |(Y + h) * R1 (Y + h) - Y * R1 Y - S|
                ≤ |(Y + h) * R1 (Y + h) - Y * R1 Y| + |S| := abs_sub _ _
              _ ≤ |(Y + h) * R1 (Y + h)| + |Y * R1 Y| + |S| := by
                  linarith [abs_sub ((Y + h) * R1 (Y + h)) (Y * R1 Y)]
        _ = (Y + h) * |R1 (Y + h)| + Y * |R1 Y| + |S| := by
            rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Y + h), abs_of_pos hYpos]
        _ ≤ 4 * C' * Y ^ 2 / Lg ^ (2 * A + 2) + C' * Y ^ 2 / Lg ^ (2 * A + 2) + (h + 1) ^ 2 := by
            linarith [hT1, hT2, hSbd]
        _ = 5 * C' * Y ^ 2 / Lg ^ (2 * A + 2) + (h + 1) ^ 2 := by ring
    have hclean : 5 * C' * Y ^ 2 + (Y + P) ^ 2 ≤ (5 * C' + 2) * Y ^ 2 * Lg := by
      nlinarith [mul_nonneg (mul_nonneg hC'pos.le (sq_nonneg Y)) (by linarith : (0 : ℝ) ≤ Lg - 1),
        mul_nonneg (sq_nonneg Y) (by linarith : (0 : ℝ) ≤ Lg - 1),
        mul_nonneg (by linarith : (0 : ℝ) ≤ Y - 3 * P) (by linarith : (0 : ℝ) ≤ Y + P),
        sq_nonneg P]
    have key2 : 5 * C' * Y ^ 2 / (P * P) + (Y / P + 1) ^ 2 ≤ (5 * C' + 2) * Y ^ 2 / (P * Q) := by
      have e1 : (Y / P + 1) ^ 2 = (Y + P) ^ 2 / (P * P) := by field_simp
      rw [e1, ← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
      calc (5 * C' * Y ^ 2 + (Y + P) ^ 2) * (P * Q)
          ≤ ((5 * C' + 2) * Y ^ 2 * Lg) * (P * Q) :=
            mul_le_mul_of_nonneg_right hclean (by positivity)
        _ = (5 * C' + 2) * Y ^ 2 * (P * P) := by rw [hPeq]; ring
    refine le_of_mul_le_mul_left ?_ hhpos
    calc h * |Salt.TwinBar.Mmu y|
        ≤ 5 * C' * Y ^ 2 / Lg ^ (2 * A + 2) + (h + 1) ^ 2 := hcore
      _ = 5 * C' * Y ^ 2 / (P * P) + (Y / P + 1) ^ 2 := by rw [hP2, hh]
      _ ≤ (5 * C' + 2) * Y ^ 2 / (P * Q) := key2
      _ = h * ((5 * C' + 2) * Y / Q) := by rw [hh]; field_simp
  rw [Filter.eventually_atTop] at key
  obtain ⟨N, hN⟩ := key
  exact ⟨5 * C' + 2, N, by positivity, hN⟩

/-! ## THE TROPHY -/

/-- **THE TROPHY — the effective Möbius summatory rate.** `Salt.TwinBar.MmuRate` holds:
for every `A > 0` there are `C > 0` and `x₀` with `|M_μ(y)| ≤ C·y/(log y)^A` for all `y ≥ x₀`.
The `1/ζ` smoothed-Perron contour (`mmu1_contour_shift`, residue-free), the shallow-window
budget (`mmu1_shift_decay`, `T = exp((log x)^{1/10})`), and the two-point Riesz de-smoothing
(`mmuRate_of_smoothed`) compose. On this landing `parity_wall` goes UNCONDITIONAL. -/
theorem mmuRate_holds : Salt.TwinBar.MmuRate :=
  mmuRate_of_smoothed mmuRate_smoothed

end Salt.SW
end
