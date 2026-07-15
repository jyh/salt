/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.Estermann
import Salt.SW.ZetaPartialFractions

/-!
# The SW rung, node S4b″ — discharging `EstermannInterface`

Design: `docs/blueprints/sw.md`, wave S4; the flags `SW S4b` / `SW S4b′` / `SW S4b″` in
`docs/blueprints/flags.md`. This module supplies the analytic plumbing that S4b′ deferred:
the pole-subtracted Taylor data `(a, B)` of `F = ζ·f` at `s = 2`, its Cauchy bound, the
ψ-series identity, and the sign `ζ(σ) ≤ 0`.

## CRITICAL FINDING — `EstermannInterface` (as landed in `Estermann.lean`) is FALSE

The `Prop` `Salt.SW.EstermannInterface` quantifies over all `f, r` with `ζ·f = LSeries r`
on `Re > 1`, `r ≥ 0`, `r 1 = 1` — but the tsum-based `LSeries` equality does **not** force
`r` to be summable. Take `f ≡ 0` and `r n = 2^(n-1)` (nonneg, `r 1 = 1`, and non-summable at
every `Re s > 1`, so `LSeries r s = 0 = ζ(s)·0` holds). All interface hypotheses are met, yet
no `(a, B)` can satisfy the conclusion: the Cauchy bound forces `∑ a k (2−σ)^k` to converge to
`≥ a 0 ≥ 1`, while the ψ-identity forces it to equal `0`. See `no_estermann_data_for_zero`
(machine-checked kernel) and the flag `SW S4b″`.

The correct statement needs a summability hypothesis (`abscissaOfAbsConv r < 2`, satisfied by
every real application via `LSeriesSummable_fourfoldCoeff`). We prove the corrected interface
`EstermannInterface'` in FULL below.

## What is proven here (sorry-free, axiom-clean)

* `no_estermann_data_for_zero` — the machine-checked kernel of the falseness of the ORIGINAL
  interface: no `(a, B)` data exists once `L = 0` and the ψ-identity forces the series to `0`.
* `zeta_nonpos` — **obligation 3**: `ζ(σ) ≤ 0` on `[19/20, 1)`, via the pole factorisation
  `ζ = Zc/(s−1)` and `Zc(σ) > 0` from the landed `Zc_eq_series` / `norm_R_le`.
* `estermann_data` — **obligations 1, 2, 4**: for admissible `f, r` with the ADDED summability
  input `abscissaOfAbsConv r < 2`, the full `(a, B)` package (nonnegativity, `a 0 ≥ 1`, the
  Cauchy bound on `ψ = ζf − f(1)/(s−1)`, and the ψ-series identity).
* `estermannInterface' : EstermannInterface'` — the corrected interface.
-/

open scoped BigOperators ComplexOrder Nat
open Complex

namespace Salt.SW

/-! ## 0. The falseness kernel of the original `EstermannInterface` -/

/-- **The falseness kernel.** If `L = 0` and the ψ-series is forced to `0`, then no admissible
Taylor data `(a, B)` exists: the Cauchy bound `|a k| ≤ B (2/3)^k` makes `∑ a k y^k` converge to
`≥ a 0 ≥ 1`, contradicting `∑ a k y^k = 0`. This is exactly the contradiction reached by feeding
`f ≡ 0` (with a non-summable `r`, e.g. `r n = 2^(n-1)`) to `EstermannInterface`, whence
`¬ EstermannInterface`. -/
theorem no_estermann_data_for_zero {a : ℕ → ℝ} {B σ : ℝ}
    (hσ1 : 1 < 2 - σ) (hσ2 : 2 - σ ≤ 21 / 20)
    (ha : ∀ k, 0 ≤ a k) (ha0 : 1 ≤ a 0)
    (hcauchy : ∀ k, |a k| ≤ B * (2 / 3) ^ k)
    (hid : ∑' k, a k * (2 - σ) ^ k = 0) : False := by
  set y : ℝ := 2 - σ with hy
  have hy0 : 0 < y := by linarith
  set q : ℝ := 2 * y / 3 with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q < 1 := by rw [hq]; linarith [hσ2]
  have hBpos : 0 < B := by
    have := hcauchy 0; simp only [pow_zero, mul_one] at this
    have h0 : 0 ≤ |a 0| := abs_nonneg _
    have : 1 ≤ |a 0| := by rw [abs_of_nonneg (ha 0)]; exact ha0
    linarith [this, hcauchy 0]
  have hbound : ∀ k, a k * y ^ k ≤ B * q ^ k := by
    intro k
    have hyk : (0 : ℝ) ≤ y ^ k := by positivity
    calc a k * y ^ k ≤ |a k| * y ^ k := mul_le_mul_of_nonneg_right (le_abs_self (a k)) hyk
      _ ≤ B * (2 / 3) ^ k * y ^ k := mul_le_mul_of_nonneg_right (hcauchy k) hyk
      _ = B * q ^ k := by rw [hq, show (2 * y / 3 : ℝ) = 2 / 3 * y from by ring, mul_pow]; ring
  have hgeom : Summable (fun k => B * q ^ k) := (summable_geometric_of_lt_one hq0 hq1).mul_left B
  have hterm_nn : ∀ k, 0 ≤ a k * y ^ k := fun k => mul_nonneg (ha k) (by positivity)
  have hsummable : Summable (fun k => a k * y ^ k) :=
    Summable.of_nonneg_of_le hterm_nn hbound hgeom
  have hge : 1 ≤ ∑' k, a k * y ^ k := by
    calc (1 : ℝ) ≤ a 0 * y ^ 0 := by rw [pow_zero, mul_one]; exact ha0
      _ ≤ ∑' k, a k * y ^ k := hsummable.le_tsum 0 (fun i _ => hterm_nn i)
  rw [hid] at hge
  linarith

/-! ## 1. Obligation 3 — the sign `ζ(σ) ≤ 0` on `[19/20, 1)`

Route (b) of the S4b′ flag: the pole factorisation `Zc s = (s−1)·ζ(s)` gives `ζ(σ) = Zc(σ)/(σ−1)`,
and `Zc(σ) > 0` (a positive real) follows from the landed Abel identity `Zc s = 1 + (s−1)·∑ dTerm`
(`Zc_eq_series`) with the tail bound `‖∑ dTerm‖ ≤ ‖s‖(1 + 1/Re s)` (`norm_R_le`). Since `σ − 1 < 0`,
`ζ(σ)` is a negative real. -/

/-- The Abel term `dTerm (σ) m` is real for real `σ` and `m ≥ 1` (the integrand is `↑(m^{-σ} −
u^{-σ})`). -/
lemma dTerm_im (σ : ℝ) {m : ℕ} (hm : 1 ≤ m) : (dTerm (σ : ℂ) m).im = 0 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hcoe : dTerm (σ : ℂ) m
      = (((∫ u in (m : ℝ)..(m : ℝ) + 1, ((m : ℝ) ^ (-σ) - u ^ (-σ))) : ℝ) : ℂ) := by
    rw [dTerm, ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le (by linarith) (Set.mem_Icc.mp hu).1
    change (m : ℂ) ^ (-(σ : ℂ)) - (u : ℂ) ^ (-(σ : ℂ))
        = (((m : ℝ) ^ (-σ) - u ^ (-σ) : ℝ) : ℂ)
    rw [Complex.ofReal_sub, Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ (m : ℝ)) (-σ),
        Complex.ofReal_cpow hu0.le (-σ), Complex.ofReal_neg, Complex.ofReal_natCast]
  rw [hcoe, Complex.ofReal_im]

/-- **Obligation 3.** `ζ(σ) ≤ 0` (a nonpositive real, in `ComplexOrder`) for `σ ∈ [19/20, 1)`. -/
theorem zeta_nonpos {σ : ℝ} (h1 : (19 : ℝ) / 20 ≤ σ) (h2 : σ < 1) :
    riemannZeta (σ : ℂ) ≤ 0 := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hσC : 0 < ((σ : ℂ)).re := by rw [Complex.ofReal_re]; exact hσ0
  set R : ℂ := ∑' n : ℕ, dTerm (σ : ℂ) (n + 1) with hR
  have hZc : Zc (σ : ℂ) = 1 + ((σ : ℂ) - 1) * R := Zc_eq_series (σ : ℂ) hσC
  -- `R` is real
  have hRim : R.im = 0 := by
    have hhs := (dTerm_summable_shift (σ : ℂ) hσC).hasSum
    have heq : (fun n : ℕ => (dTerm (σ : ℂ) (n + 1)).im) = fun _ => (0 : ℝ) :=
      funext (fun n => dTerm_im σ (Nat.le_add_left 1 n))
    have hz : HasSum (fun n : ℕ => (dTerm (σ : ℂ) (n + 1)).im) 0 := by rw [heq]; exact hasSum_zero
    exact (Complex.hasSum_im hhs).unique hz
  -- the tail norm bound `‖(σ−1)·R‖ ≤ 1/10`
  have hnorm : ‖((σ : ℂ) - 1) * R‖ ≤ 1 / 10 := by
    rw [norm_mul]
    have hR_le : ‖R‖ ≤ σ + 1 := by
      have hbase := norm_R_le (σ : ℂ) hσC
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ0, Complex.ofReal_re] at hbase
      calc ‖R‖ ≤ σ * (1 + 1 / σ) := hbase
        _ = σ + 1 := by rw [mul_add, mul_one, mul_one_div, div_self (ne_of_gt hσ0)]
    have hσ1_norm : ‖(σ : ℂ) - 1‖ = 1 - σ := by
      have hrw : (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hrw, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : σ - 1 < 0)]; ring
    rw [hσ1_norm]
    nlinarith [hR_le, h1, h2, norm_nonneg R, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - σ)
      (by linarith [hR_le] : (0 : ℝ) ≤ σ + 1 - ‖R‖)]
  -- `Re(Zc σ) ≥ 9/10 > 0`
  have hZcpos : 0 < (Zc (σ : ℂ)).re := by
    rw [hZc, Complex.add_re, Complex.one_re]
    have hh := abs_le.mp (le_trans (Complex.abs_re_le_norm (((σ : ℂ) - 1) * R)) hnorm)
    linarith [hh.1]
  -- `(Zc σ).im = 0`
  have hZcim : (Zc (σ : ℂ)).im = 0 := by
    rw [hZc, Complex.add_im, Complex.one_im, zero_add, Complex.mul_im]
    have h1' : ((σ : ℂ) - 1).im = 0 := by
      rw [Complex.sub_im, Complex.ofReal_im, Complex.one_im]; ring
    rw [h1', hRim]; ring
  -- unpack `ζσ = Zc σ / (σ−1)`
  have hσne : (σ : ℂ) ≠ 1 := by
    intro h; rw [Complex.ext_iff, Complex.ofReal_re, Complex.one_re] at h; linarith [h.1]
  have hZceq : Zc (σ : ℂ) = ((σ : ℂ) - 1) * riemannZeta (σ : ℂ) := Zc_eq_of_ne hσne
  have hd : ((σ : ℂ) - 1).re = σ - 1 := by rw [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  have hd' : ((σ : ℂ) - 1).im = 0 := by rw [Complex.sub_im, Complex.ofReal_im, Complex.one_im]; ring
  have hre_eq : (Zc (σ : ℂ)).re = (σ - 1) * (riemannZeta (σ : ℂ)).re := by
    rw [hZceq, Complex.mul_re, hd, hd']; ring
  have him_eq : (Zc (σ : ℂ)).im = (σ - 1) * (riemannZeta (σ : ℂ)).im := by
    rw [hZceq, Complex.mul_im, hd, hd']; ring
  have hζim : (riemannZeta (σ : ℂ)).im = 0 := by
    have hz : (σ - 1) * (riemannZeta (σ : ℂ)).im = 0 := by rw [← him_eq]; exact hZcim
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_lt (by linarith : σ - 1 < 0))
  have hζre : (riemannZeta (σ : ℂ)).re < 0 := by
    have hpos : 0 < (σ - 1) * (riemannZeta (σ : ℂ)).re := hre_eq ▸ hZcpos
    by_contra hc
    have hc' : 0 ≤ (riemannZeta (σ : ℂ)).re := not_lt.mp hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : σ - 1 ≤ 0) hc']
  refine Complex.le_def.mpr ⟨?_, ?_⟩
  · rw [Complex.zero_re]; linarith [hζre]
  · rw [Complex.zero_im]; exact hζim

/-! ## 2. The pole-term iterated derivative

`ψ = ζf − f(1)/(s−1)` differs from `F = ζf` near `s = 2` by the pole term `f(1)·(s−1)⁻¹`, whose
`k`-th derivative at `2` is `f(1)·(−1)^k·k!`. This is the bridge that turns `ψ`'s Cauchy
coefficients into `F`'s (sign-alternating, nonnegative) Taylor data. -/

private lemma iteratedDeriv_pole (k : ℕ) :
    iteratedDeriv k (fun s : ℂ => (s - 1)⁻¹) 2 = (-1) ^ k * (k ! : ℂ) := by
  have key : ∀ n, Set.EqOn (iteratedDeriv n (fun s : ℂ => (s - 1)⁻¹))
      (fun s => (-1) ^ n * (n ! : ℂ) * ((s - 1)⁻¹) ^ (n + 1)) {s : ℂ | s ≠ 1} := by
    intro n
    induction n with
    | zero => intro s _; simp
    | succ m ih =>
      intro s hs
      have hsne : (s : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hs
      have hmem : {s : ℂ | s ≠ 1} ∈ nhds s := isOpen_ne.mem_nhds hs
      rw [iteratedDeriv_succ]
      have hcongr : deriv (iteratedDeriv m (fun s : ℂ => (s - 1)⁻¹)) s
          = deriv (fun s => (-1) ^ m * (m ! : ℂ) * ((s - 1)⁻¹) ^ (m + 1)) s := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [hmem] with t ht using ih ht
      rw [hcongr]
      have h1 : HasDerivAt (fun t : ℂ => t - 1) 1 s := (hasDerivAt_id s).sub_const 1
      have hp : HasDerivAt (fun t : ℂ => (t - 1)⁻¹) (-1 / (s - 1) ^ 2) s := h1.inv hsne
      have hfull := (hp.pow (m + 1)).const_mul ((-1 : ℂ) ^ m * (m ! : ℂ))
      simp only [Pi.pow_apply] at hfull
      rw [hfull.deriv, Nat.factorial_succ]
      have hexp : m + 1 - 1 = m := by omega
      rw [hexp]
      have hinv2 : (-1 / (((s : ℂ) - 1)) ^ 2) = -(((s - 1)⁻¹) ^ 2) := by
        rw [inv_pow]; ring
      rw [hinv2]; push_cast; ring
  have hmem2 : (2 : ℂ) ∈ {s : ℂ | s ≠ 1} := by norm_num
  have h2 := key k hmem2
  rw [h2]; norm_num

/-! ## 3. The corrected interface and its full discharge

The original `EstermannInterface` (`Estermann.lean`) is FALSE (see `no_estermann_data_for_zero`).
`EstermannInterface'` adds the missing summability input `abscissaOfAbsConv r < 2` — satisfied by
every real application (`LSeriesSummable_fourfoldCoeff`) — and is proven in full. -/

/-- **The corrected Estermann interface.** `EstermannInterface` plus the summability hypothesis
`abscissaOfAbsConv r < 2`, without which the `∃`-package cannot exist. -/
def EstermannInterface' : Prop :=
  ∀ (f : ℂ → ℂ) (r : ℕ → ℂ) (M : ℝ), 1 ≤ M → Differentiable ℂ f →
    (∀ z ∈ Metric.ball (2 : ℂ) (3 / 2), ‖f z‖ ≤ M) →
    (0 ≤ r) → r 1 = 1 → LSeries.abscissaOfAbsConv r < 2 →
    (∀ s : ℂ, 1 < s.re → riemannZeta s * f s = LSeries r s) →
    ∀ {σ : ℝ}, (19 / 20 : ℝ) ≤ σ → σ < 1 → (0 : ℂ) ≤ f (σ : ℂ) →
      ∃ (a : ℕ → ℝ) (B : ℝ), (∀ k, 0 ≤ a k) ∧ 1 ≤ a 0 ∧ 2 ≤ B ∧ B ≤ 29 / 2 * M ∧
        (∀ k, |a k - (f 1).re| ≤ B * (2 / 3) ^ k) ∧ riemannZeta (σ : ℂ) ≤ 0 ∧
        ∑' k, (a k - (f 1).re) * (2 - σ) ^ k
          = (riemannZeta (σ : ℂ) * f (σ : ℂ)).re + (f 1).re / (1 - σ)

/-- **The full discharge of the corrected interface** — obligations 1 (nonnegative Taylor data),
2 (Cauchy bound on `ψ = ζf − f(1)/(s−1)`), 4 (assembly), plus the ψ-series identity, together with
obligation 3 (`ζ(σ) ≤ 0`, via `zeta_nonpos`). -/
theorem estermannInterface' : EstermannInterface' := by
  intro f r M hM hf hfM hr0 hr1 habsc hζf σ hσlo hσhi hfσ
  have hζneg : riemannZeta (σ : ℂ) ≤ 0 := zeta_nonpos hσlo hσhi
  -- the entire pole-subtracted function `ψ`
  set F : ℂ → ℂ := fun s => riemannZeta s * f s with hFdef
  set g : ℂ → ℂ := fun s => Zc s * f s - f 1 with hgdef
  set ψ : ℂ → ℂ := dslope g 1 with hψdef
  have hg1 : g 1 = 0 := by rw [hgdef]; simp [Zc_one]
  have hgdiff : Differentiable ℂ g := (Zc_differentiable.mul hf).sub_const (f 1)
  have hψdiff : Differentiable ℂ ψ :=
    differentiableOn_univ.mp
      ((differentiableOn_dslope (c := (1 : ℂ)) Filter.univ_mem).mpr hgdiff.differentiableOn)
  have hψ_eq : ∀ {s : ℂ}, s ≠ 1 → ψ s = F s - f 1 * (s - 1)⁻¹ := by
    intro s hs
    have hs1 : (s : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hs
    rw [hψdef, dslope_of_ne g hs, slope_def_field, hg1, sub_zero]
    simp only [hgdef, hFdef]
    rw [Zc_eq_of_ne hs]
    field_simp
  set c : ℕ → ℂ := fun k => iteratedDeriv k ψ 2 / (k ! : ℂ) with hcdef
  set a : ℕ → ℝ := fun k => (-1) ^ k * (c k).re + (f 1).re with hadef
  have hσne : (σ : ℂ) ≠ 1 := by
    intro h; rw [Complex.ext_iff, Complex.ofReal_re, Complex.one_re] at h; linarith [h.1]
  -- ContDiff facts and the derivative bridge (`ψ`'s coefficients versus `F`'s Taylor data)
  have hζana : AnalyticAt ℂ riemannZeta 2 := by
    have hdon : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
      fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact hdon.analyticOnNhd isOpen_ne 2 (by norm_num)
  have hfana : AnalyticAt ℂ f 2 :=
    (hf.differentiableOn.analyticOnNhd isOpen_univ) 2 (Set.mem_univ _)
  have hFcd : ∀ k : ℕ, ContDiffAt ℂ k F 2 := fun k => (hζana.contDiffAt).mul hfana.contDiffAt
  have hinvcd : ∀ k : ℕ, ContDiffAt ℂ k (fun s : ℂ => (s - 1)⁻¹) 2 := by
    intro k
    have h1 : ContDiffAt ℂ k (fun s : ℂ => s - 1) 2 := contDiffAt_id.sub contDiffAt_const
    exact h1.inv (by norm_num)
  have hhcd : ∀ k : ℕ, ContDiffAt ℂ k (fun s : ℂ => f 1 * (s - 1)⁻¹) 2 :=
    fun k => contDiffAt_const.mul (hinvcd k)
  have hbridge : ∀ k, iteratedDeriv k ψ 2 = iteratedDeriv k F 2 - f 1 * ((-1) ^ k * (k ! : ℂ)) := by
    intro k
    have hev : ψ =ᶠ[nhds (2 : ℂ)] (fun s => F s - f 1 * (s - 1)⁻¹) := by
      filter_upwards [isOpen_ne.mem_nhds (show (2 : ℂ) ≠ 1 by norm_num)] with s hs
      exact hψ_eq hs
    rw [Filter.EventuallyEq.iteratedDeriv_eq k hev, iteratedDeriv_fun_sub (hFcd k) (hhcd k),
        iteratedDeriv_const_mul_field (f 1) (fun s => (s - 1)⁻¹)]
    rw [iteratedDeriv_pole k]
  have hFLS : ∀ k, iteratedDeriv k F 2 = iteratedDeriv k (LSeries r) 2 := by
    intro k
    have hev : F =ᶠ[nhds (2 : ℂ)] LSeries r := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by rw [Complex.re_ofNat]; norm_num)] with s hs
      exact hζf s hs
    exact Filter.EventuallyEq.iteratedDeriv_eq k hev
  -- the analytic value `a k = ((−1)^k · (k-th LSeries derivative)/k!).re`
  have hak : ∀ k, a k = ((-1 : ℂ) ^ k * iteratedDeriv k (LSeries r) 2 / (k ! : ℂ)).re := by
    intro k
    have hkf : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hneg1 : (-1 : ℂ) ^ k = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; ring
    have hsq : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    have hck : c k = iteratedDeriv k (LSeries r) 2 / (k ! : ℂ) - (-1) ^ k * f 1 := by
      simp only [hcdef]; rw [hbridge k, hFLS k]; field_simp
    simp only [hadef]
    rw [hck, Complex.sub_re, hneg1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, mul_div_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    linear_combination (-(f 1).re) * hsq
  -- obligation 1a: nonnegativity
  have habsc2 : LSeries.abscissaOfAbsConv r < ((2 : ℝ) : EReal) := by exact_mod_cast habsc
  have hnonneg : ∀ k, 0 ≤ a k := by
    intro k
    have hD : (0 : ℂ) ≤ (-1) ^ k * iteratedDeriv k (LSeries r) 2 := by
      have h := LSeries.iteratedDeriv_alternating hr0 habsc2 k
      rwa [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num] at h
    obtain ⟨hwre, hwim⟩ := Complex.le_def.mp hD
    simp only [Complex.zero_re, Complex.zero_im] at hwre hwim
    have hkinv : (k ! : ℂ)⁻¹ = (((k ! : ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [hak k, div_eq_mul_inv, hkinv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
    exact mul_nonneg hwre (by positivity)
  -- obligation 1b: `a 0 ≥ 1`
  have ha0 : 1 ≤ a 0 := by
    have hs : LSeriesSummable r 2 := by
      apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
      rw [Complex.re_ofNat]; exact_mod_cast habsc
    have hnn : ∀ n, 0 ≤ (LSeries.term r 2 n).re := by
      intro n
      have h := LSeries.term_nonneg (hr0 n) (2 : ℝ)
      rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num] at h
      simpa using (Complex.le_def.mp h).1
    have hsum_re : Summable (fun n => (LSeries.term r 2 n).re) :=
      (Complex.hasSum_re hs.hasSum).summable
    have h1term : (LSeries.term r 2 1).re = 1 := by
      rw [LSeries.term_of_ne_zero one_ne_zero, hr1]; simp
    have hle : 1 ≤ (LSeries r 2).re := by
      have hval : (LSeries r 2).re = ∑' n, (LSeries.term r 2 n).re :=
        (Complex.hasSum_re hs.hasSum).tsum_eq.symm
      rw [hval, ← h1term]
      exact hsum_re.le_tsum 1 (fun j _ => hnn j)
    have h00 : a 0 = (LSeries r 2).re := by
      rw [hak 0]; simp [iteratedDeriv_zero]
    rw [h00]; exact hle
  -- obligation 2: the Cauchy bound (with `B = 29/2 · M`)
  have hf1M : ‖f 1‖ ≤ M := hfM 1 (by
    rw [Metric.mem_ball, Complex.dist_eq, show (1 : ℂ) - 2 = -1 by ring, norm_neg, norm_one]
    norm_num)
  have hfcb : ∀ z ∈ Metric.closedBall (2 : ℂ) (3 / 2), ‖f z‖ ≤ M := by
    have hcl : IsClosed {z : ℂ | ‖f z‖ ≤ M} := isClosed_le hf.continuous.norm continuous_const
    have hsub : Metric.closedBall (2 : ℂ) (3 / 2) ⊆ {z | ‖f z‖ ≤ M} := by
      rw [← closure_ball (2 : ℂ) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
      exact closure_minimal hfM hcl
    exact hsub
  have hn2 : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]; norm_num
  have hψ_sphere : ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖ψ z‖ ≤ 29 / 2 * M := by
    intro z hz
    rw [Metric.mem_sphere, Complex.dist_eq] at hz
    have hz1lo : (1 : ℝ) / 2 ≤ ‖z - 1‖ := by
      have h := norm_sub_norm_le (z - 2) (-1 : ℂ)
      rw [show (z - 2) - (-1) = z - 1 by ring, norm_neg, norm_one, hz] at h
      linarith
    have hzne1 : z ≠ 1 := by
      intro h; rw [h] at hz1lo; simp only [sub_self, norm_zero] at hz1lo; linarith
    have hRe : (1 : ℝ) / 2 ≤ z.re := by
      have h := Complex.abs_re_le_norm (z - 2)
      rw [Complex.sub_re, Complex.re_ofNat, hz] at h
      have := abs_le.mp h; linarith [this.1]
    have hRePos : 0 < z.re := by linarith
    have hzn : ‖z‖ ≤ 7 / 2 := by
      calc ‖z‖ = ‖(z - 2) + 2‖ := by ring_nf
        _ ≤ ‖z - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
        _ = 3 / 2 + 2 := by rw [hz, hn2]
        _ = 7 / 2 := by norm_num
    have hfz : ‖f z‖ ≤ M := hfcb z (by
      rw [Metric.mem_closedBall, Complex.dist_eq]; exact le_of_eq hz)
    have hzne1' : (z : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hzne1
    have hd : (0 : ℝ) < ‖z - 1‖ := by linarith
    have hinv2 : ‖z - 1‖⁻¹ ≤ 2 := by
      have := inv_anti₀ (show (0 : ℝ) < 1 / 2 by norm_num) hz1lo
      rwa [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num] at this
    have hzre2 : 1 / z.re ≤ 2 := by rw [div_le_iff₀ hRePos]; linarith
    have hζz : riemannZeta z = Zc z * (z - 1)⁻¹ := by
      rw [Zc_eq_of_ne hzne1, mul_comm ((z : ℂ) - 1), mul_assoc, mul_inv_cancel₀ hzne1', mul_one]
    have hζznorm : ‖riemannZeta z‖ ≤ 25 / 2 := by
      rw [hζz, norm_mul, norm_inv]
      have hZcz := Zc_growth hRePos
      have e2 : (1 + ‖z - 1‖ * (‖z‖ * (1 + 1 / z.re))) * ‖z - 1‖⁻¹
          = ‖z - 1‖⁻¹ + ‖z‖ * (1 + 1 / z.re) := by field_simp
      have e3 : ‖z‖ * (1 + 1 / z.re) ≤ 21 / 2 := by
        have h1z : (0 : ℝ) ≤ 1 / z.re := by positivity
        calc ‖z‖ * (1 + 1 / z.re) ≤ (7 / 2) * (1 + 2) :=
              mul_le_mul hzn (by linarith) (by linarith) (by norm_num)
          _ = 21 / 2 := by norm_num
      calc ‖Zc z‖ * ‖z - 1‖⁻¹ ≤ (1 + ‖z - 1‖ * (‖z‖ * (1 + 1 / z.re))) * ‖z - 1‖⁻¹ :=
            mul_le_mul_of_nonneg_right hZcz (by positivity)
        _ = ‖z - 1‖⁻¹ + ‖z‖ * (1 + 1 / z.re) := e2
        _ ≤ 2 + 21 / 2 := by linarith
        _ = 25 / 2 := by norm_num
    have hψz : ψ z = riemannZeta z * f z - f 1 * (z - 1)⁻¹ := by
      have := hψ_eq hzne1; rwa [hFdef] at this
    calc ‖ψ z‖ = ‖riemannZeta z * f z - f 1 * (z - 1)⁻¹‖ := by rw [hψz]
      _ ≤ ‖riemannZeta z * f z‖ + ‖f 1 * (z - 1)⁻¹‖ := norm_sub_le _ _
      _ = ‖riemannZeta z‖ * ‖f z‖ + ‖f 1‖ * ‖z - 1‖⁻¹ := by rw [norm_mul, norm_mul, norm_inv]
      _ ≤ 25 / 2 * M + M * 2 := by
          have hA : ‖riemannZeta z‖ * ‖f z‖ ≤ 25 / 2 * M :=
            mul_le_mul hζznorm hfz (norm_nonneg _) (by norm_num)
          have hB : ‖f 1‖ * ‖z - 1‖⁻¹ ≤ M * 2 :=
            mul_le_mul hf1M hinv2 (by positivity) (by linarith)
          linarith
      _ = 29 / 2 * M := by ring
  have hc_bound : ∀ k, ‖c k‖ ≤ 29 / 2 * M * (2 / 3) ^ k := by
    intro k
    have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
      (by norm_num : (0 : ℝ) < 3 / 2) hψdiff.diffContOnCl hψ_sphere
    have hkfac : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    simp only [hcdef, norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ hkfac]
    calc ‖iteratedDeriv k ψ 2‖ ≤ (k ! : ℝ) * (29 / 2 * M) / (3 / 2) ^ k := hb
      _ = 29 / 2 * M * (2 / 3) ^ k * (k ! : ℝ) := by
          rw [div_eq_mul_inv, ← inv_pow, show ((3 : ℝ) / 2)⁻¹ = 2 / 3 by norm_num]; ring
  have hcauchy : ∀ k, |a k - (f 1).re| ≤ 29 / 2 * M * (2 / 3) ^ k := by
    intro k
    have haL : a k - (f 1).re = (-1) ^ k * (c k).re := by simp only [hadef]; ring
    rw [haL]
    calc |(-1) ^ k * (c k).re| = |(c k).re| := by
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ ≤ ‖c k‖ := Complex.abs_re_le_norm (c k)
      _ ≤ 29 / 2 * M * (2 / 3) ^ k := hc_bound k
  -- the ψ-series identity
  have htaylor : HasSum (fun k => c k * ((σ : ℂ) - 2) ^ k) (ψ (σ : ℂ)) := by
    have h := Complex.hasSum_taylorSeries_of_entire hψdiff 2 (σ : ℂ)
    have heq : (fun k => (k ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ k • iteratedDeriv k ψ 2)
        = (fun k => c k * ((σ : ℂ) - 2) ^ k) := by
      funext k; simp only [hcdef, smul_eq_mul]; ring
    rwa [heq] at h
  have hterm_eq : ∀ k, (c k * ((σ : ℂ) - 2) ^ k).re = (a k - (f 1).re) * (2 - σ) ^ k := by
    intro k
    have hw : ((σ : ℂ) - 2) ^ k = (((σ - 2) ^ k : ℝ) : ℂ) := by
      rw [show (σ : ℂ) - 2 = ((σ - 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_pow]
    have haL : a k - (f 1).re = (-1) ^ k * (c k).re := by simp only [hadef]; ring
    have h2σ : (2 - σ : ℝ) ^ k = (-1) ^ k * (σ - 2) ^ k := by
      rw [show (2 - σ : ℝ) = -(σ - 2) by ring, neg_pow]
    have hsq : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    rw [hw, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, haL, h2σ]
    linear_combination (-(c k).re * (σ - 2) ^ k) * hsq
  have hseries : ∑' k, (a k - (f 1).re) * (2 - σ) ^ k
      = (riemannZeta (σ : ℂ) * f (σ : ℂ)).re + (f 1).re / (1 - σ) := by
    have hhs : HasSum (fun k => (a k - (f 1).re) * (2 - σ) ^ k) (ψ (σ : ℂ)).re := by
      have heq : (fun k => (a k - (f 1).re) * (2 - σ) ^ k)
          = (fun k => (c k * ((σ : ℂ) - 2) ^ k).re) := funext (fun k => (hterm_eq k).symm)
      rw [heq]; exact Complex.hasSum_re htaylor
    rw [hhs.tsum_eq]
    have hψσ : ψ (σ : ℂ) = riemannZeta (σ : ℂ) * f (σ : ℂ) - f 1 * ((σ : ℂ) - 1)⁻¹ := by
      have := hψ_eq hσne; rwa [hFdef] at this
    have hinv : ((σ : ℂ) - 1)⁻¹ = (((σ - 1)⁻¹ : ℝ) : ℂ) := by
      rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_inv]
    have hii : ((σ : ℝ) - 1)⁻¹ = -(1 - σ)⁻¹ := by rw [neg_inv]; congr 1; ring
    have hpole_re : (f 1 * ((σ : ℂ) - 1)⁻¹).re = -((f 1).re / (1 - σ)) := by
      rw [hinv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hii,
          div_eq_mul_inv]; ring
    rw [hψσ, Complex.sub_re, hpole_re]; ring
  exact ⟨a, 29 / 2 * M, hnonneg, ha0, by nlinarith [hM], le_refl _, hcauchy, hζneg, hseries⟩



/-! ## The payoff: Estermann's lemma and Siegel's engine, unconditional

With the abscissa hypothesis folded into `EstermannInterface`/`EstermannPositivity`
(the catch-#26 amendment), the corrected interface *is* the interface, and
Estermann's positivity lemma holds unconditionally. -/

/-- The (amended) `EstermannInterface` holds — `EstermannInterface'` is definitionally
that statement. -/
theorem estermannInterface : EstermannInterface := estermannInterface'

/-- **Estermann's positivity lemma, unconditional** (MV Lemma 11.13). Completes the
analytic core of the Goldfeld–Siegel cluster: `Siegel.lean`'s `estermann_fourfold` and
everything downstream may now consume this instead of a hypothesis. -/
theorem estermannPositivity : EstermannPositivity :=
  estermannPositivity_of_interface estermannInterface

end Salt.SW
