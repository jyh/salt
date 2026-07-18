/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.RegionGrowth

/-!
# VMVT-VK — the power zero-free region (`σ ≥ 1 − c/((log t)^{3/4}(log log t)^3)`)

THE POWER REGION.  The Vinogradov–Korobov strip growth `zeta_growth_pow`
(`‖ζ(σ+it)‖ ≤ K·log t` on `σ ≥ 1 − vkTheta t`, `vkTheta t = (1/1000)/((log t)^{3/4}(log log t)^2)`),
fed through the growth-to-region bridge `region_of_uniform_growth` at `Θ = vkTheta(3γ)`, produces a
zero-free region of power shape `θ = 3/4 < 1` — strictly wider than de la Vallée Poussin's `1/log t`
AND than the Littlewood `log log t/log t`, and (crucially) the first region with the **power** shape
the Montgomery–Renyi (MR) gate consumes.

This file is the *emission*: given `zeta_growth_pow` (R6, produced from the machine-checked
Vinogradov mean value theorem via the block ladder R5b), the region follows.  The emission is
growth-agnostic in the same sense as `Salt/Vk/Littlewood.lean`: the power region and the Littlewood
sibling share the bridge `region_of_uniform_growth`; only the growth input and the `(Θ, Lq, dd)`
selection differ.  Unlike Littlewood there is no free degree `k` to balance — the `k(t)`-schedule is
already baked into `zeta_growth_pow`, so the emission is a single strip-wrapping, not a bracket.
-/

namespace Salt.Vk

open Complex
open scoped Topology

/-! ## The power half-width `vkTheta` and its monotonicity -/

/-- **The VK power half-width** `vkTheta t = (1/1000)/((log t)^{3/4}(log log t)^2)` (freeze MID
TARGET).  The strip `σ ≥ 1 − vkTheta t` on which the `K·log t` growth holds. -/
noncomputable def vkTheta (t : ℝ) : ℝ :=
  (1 / 1000) / ((Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (2 : ℕ))

/-- `vkTheta` is antitone above `e`: for `e < t₁ ≤ t₂`, `vkTheta t₂ ≤ vkTheta t₁`.  Both log/loglog
factors are nonnegative and monotone once `log t > 1`, so the denominator grows. -/
lemma vkTheta_anti {t₁ t₂ : ℝ} (h1 : Real.exp 1 < t₁) (h12 : t₁ ≤ t₂) :
    vkTheta t₂ ≤ vkTheta t₁ := by
  have ht1pos : 0 < t₁ := lt_trans (Real.exp_pos 1) h1
  have hlog1 : 1 < Real.log t₁ := by
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) h1
  have hlog12 : Real.log t₁ ≤ Real.log t₂ := Real.log_le_log ht1pos h12
  have hlog2 : 1 < Real.log t₂ := lt_of_lt_of_le hlog1 hlog12
  have hll1 : 0 < Real.log (Real.log t₁) := Real.log_pos hlog1
  have hll12 : Real.log (Real.log t₁) ≤ Real.log (Real.log t₂) :=
    Real.log_le_log (by linarith) hlog12
  -- denominators
  have hd1 : 0 < (Real.log t₁) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t₁)) ^ (2 : ℕ) := by
    apply mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    positivity
  have hbase : (Real.log t₁) ^ ((3 : ℝ) / 4) ≤ (Real.log t₂) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow (by linarith) hlog12 (by norm_num)
  have hll2 : (Real.log (Real.log t₁)) ^ (2 : ℕ) ≤ (Real.log (Real.log t₂)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hll1.le hll12 2
  have hdmono : (Real.log t₁) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t₁)) ^ (2 : ℕ)
      ≤ (Real.log t₂) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t₂)) ^ (2 : ℕ) := by
    apply mul_le_mul hbase hll2 (by positivity)
    exact Real.rpow_nonneg (by linarith) _
  rw [vkTheta, vkTheta]
  exact div_le_div_of_nonneg_left (by norm_num) hd1 hdmono

/-- `0 < vkTheta t` when `log t > 1`. -/
lemma vkTheta_pos {t : ℝ} (ht : 1 < Real.log t) : 0 < vkTheta t := by
  rw [vkTheta]
  have : 0 < Real.log (Real.log t) := Real.log_pos ht
  apply div_pos (by norm_num)
  apply mul_pos (Real.rpow_pos_of_pos (by linarith) _)
  positivity

/-! ## The growth statement (R6 output) as a `Prop` -/

/-- **`ZetaGrowthPow`** — the freeze MID TARGET `zeta_growth_pow`.  There exist `K ≥ 1`, `t₀ ≥ 3`
such that on the power strip `σ ≥ 1 − vkTheta t`, `σ ≤ 3`, `t ≥ t₀`, the ζ growth is `K·log t`.
This is the Vinogradov–Korobov strip bound produced by rung R6 from the block ladder. -/
def ZetaGrowthPow : Prop :=
  ∃ K t₀ : ℝ, 1 ≤ K ∧ 3 ≤ t₀ ∧ ∀ σ t : ℝ, t₀ ≤ t →
    1 - vkTheta t ≤ σ → σ ≤ 3 →
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K * Real.log t

/-! ## Uniform box growth from `zeta_growth_pow` -/

/-- **Uniform box growth from `zeta_growth_pow`.**  For a height `γ` with `e < γ − 1` and
`t₀ ≤ γ − 1`, the strip bound gives the single uniform bound `‖ζ z‖ ≤ K·log(3γ)` over the whole box
`Re z ∈ [1 − vkTheta(3γ), 2]`, `Im z ∈ [γ − 1, 3γ]` — the box containing every keep/drop sphere.
`vkTheta(3γ)` is the minimum of `vkTheta` on the box (antitone), so the strip hypothesis
`1 − vkTheta(z.im) ≤ z.re` follows from `1 − vkTheta(3γ) ≤ z.re`; `log z.im ≤ log 3γ` gives the
uniform ceiling.  This is the exact `hgrowth` shape `region_of_uniform_growth` consumes at
`Θ = vkTheta(3γ)`, `Mζ = K·log(3γ)`. -/
lemma pow_uniform_growth {K t₀ : ℝ} (hK : 1 ≤ K) (ht₀ : 3 ≤ t₀)
    (hg : ∀ σ t : ℝ, t₀ ≤ t → 1 - vkTheta t ≤ σ → σ ≤ 3 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K * Real.log t)
    {γ : ℝ} (hγe : Real.exp 1 < γ - 1) (hγt₀ : t₀ ≤ γ - 1) :
    ∀ z : ℂ, 1 - vkTheta (3 * γ) ≤ z.re → z.re ≤ 2 → γ - 1 ≤ z.im → z.im ≤ 3 * γ →
      ‖riemannZeta z‖ ≤ K * Real.log (3 * γ) := by
  intro z hre1 hre2 him1 him2
  have hzimpos : 0 < z.im := by linarith [him1, lt_trans (Real.exp_pos 1) hγe]
  have h3γ : 3 * γ ≤ 3 * γ := le_refl _
  -- z.im is above e (since z.im ≥ γ−1 > e)
  have hzime : Real.exp 1 < z.im := lt_of_lt_of_le hγe him1
  -- strip hypothesis: 1 − vkTheta(z.im) ≤ z.re
  have hθz : vkTheta (3 * γ) ≤ vkTheta z.im := vkTheta_anti hzime him2
  have hstrip : 1 - vkTheta z.im ≤ z.re := by linarith [hre1, hθz]
  have ht₀z : t₀ ≤ z.im := le_trans hγt₀ him1
  have hz3 : z.re ≤ 3 := by linarith [hre2]
  -- rewrite z as z.re + z.im * I and apply the growth
  have hzrw : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := Complex.re_add_im z
  have hfz := hg z.re z.im ht₀z hstrip hz3
  rw [hzrw] at hfz
  -- log z.im ≤ log 3γ
  have hlogle : Real.log z.im ≤ Real.log (3 * γ) := Real.log_le_log hzimpos him2
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  calc ‖riemannZeta z‖ ≤ K * Real.log z.im := hfz
    _ ≤ K * Real.log (3 * γ) := mul_le_mul_of_nonneg_left hlogle hKpos.le

/-! ## Analytic thresholds (copies of the Littlewood helpers) -/

/-- `log x ≤ 2√x` for `x > 0`. -/
private lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h
  linarith [Real.sqrt_nonneg x]

/-- `x³/27 ≤ exp x` for `0 ≤ x`. -/
private lemma cube_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 3 / 27 ≤ Real.exp x := by
  have hcube : Real.exp x = (Real.exp (x / 3)) ^ 3 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hb : 1 + x / 3 ≤ Real.exp (x / 3) := by
    have := Real.add_one_le_exp (x / 3); linarith
  rw [hcube]
  have hb0 : 0 ≤ 1 + x / 3 := by linarith
  calc x ^ 3 / 27 ≤ (1 + x / 3) ^ 3 := by
        have hexp : (1 + x / 3) ^ 3 = 1 + x + x ^ 2 / 3 + x ^ 3 / 27 := by ring
        rw [hexp]; nlinarith [hx, sq_nonneg x]
    _ ≤ (Real.exp (x / 3)) ^ 3 := pow_le_pow_left₀ hb0 hb 3

/-! ## The abstract-height core — gates + power-width algebra -/

set_option maxHeartbeats 1600000 in
-- The core threads the region bridge, the three gate discharges and the power-width bound
-- (Lq ≤ 1.91e7·L^{3/4}·ℓ³) through one declaration.
/-- **Power region at abstract height** (`zeta_growth_pow`-fed core).  A positive-height ζ-zero `ρ`
(`ρ.im ≥ 2`, `ρ.re < 1`) above the height thresholds, with the box growth from `zeta_growth_pow`,
obeys the power bound `ρ.re ≤ 1 − (1/10⁹)·1/((log ρ.im)^{3/4}(log log ρ.im)³)`.

Feeds `pow_uniform_growth` through `region_of_uniform_growth` at `Θ = vkTheta(3ρ.im)`, `dd = 1/2`,
`Lq = 8 + 700·Pinv·log(20·Pinv·Mζ)` with `Pinv = 1/Θ = 1000·(log 3γ)^{3/4}(log log 3γ)²`,
`Mζ = K·log 3γ`; the three gates reduce to `Pinv ≤ Lq` (`hchainC` by DEFN of Lq, equality), and the
width `dd/(7Lq) = 1/(14 Lq)` is bounded below via `Lq ≤ 1.91e7·L^{3/4}·ℓ³` (`L = log ρ.im`,
`ℓ = log L`), using `log(20 Pinv Mζ) ≤ 2·log log 3γ`, `log 3γ ≤ 2L`, `log log 3γ ≤ 2ℓ`. -/
theorem zeta_zero_free_pow_core {K t₀ : ℝ} (hK : 1 ≤ K) (ht₀ : 3 ≤ t₀)
    (hg : ∀ σ t : ℝ, t₀ ≤ t → 1 - vkTheta t ≤ σ → σ ≤ 3 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K * Real.log t)
    {ρ : ℂ} (hρ0 : riemannZeta ρ = 0) (hβ1 : ρ.re < 1) (hγ2 : 2 ≤ ρ.im)
    (hγe : Real.exp 1 < ρ.im - 1) (hγt₀ : t₀ ≤ ρ.im - 1)
    (hL3 : 3 ≤ Real.log ρ.im)
    (hℓK : 8 * Real.log (20000 * K) + 1100 ≤ Real.log (Real.log ρ.im)) :
    ρ.re ≤ 1 - (1 / 10 ^ 9) * (1 / ((Real.log ρ.im) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log ρ.im)) ^ (3 : ℕ))) := by
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  have hγpos : 0 < ρ.im := by linarith [hγ2]
  set L : ℝ := Real.log ρ.im with hLdef
  set ℓ : ℝ := Real.log L with hℓdef
  have hL0 : 0 < L := by linarith [hL3]
  have hℓ0 : 0 < ℓ := by rw [hℓdef]; exact Real.log_pos (by linarith [hL3])
  have hℓ1100 : 1100 ≤ ℓ := by
    have : (0 : ℝ) ≤ 8 * Real.log (20000 * K) :=
      mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [hK]))
    linarith [hℓK]
  -- log 3γ facts: L3 := log 3γ ∈ [L, 2L]; ℓ3 := log L3 ∈ [ℓ, 2ℓ]
  set L3 : ℝ := Real.log (3 * ρ.im) with hL3def
  have hlog3le2 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)]
  have hL3eq : L3 = Real.log 3 + L := by rw [hL3def, Real.log_mul (by norm_num) hγpos.ne']
  have hL3lb : L ≤ L3 := by rw [hL3eq]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]
  have hL3ub : L3 ≤ 2 * L := by rw [hL3eq]; linarith [hlog3le2, hL3]
  have hL30 : 0 < L3 := by linarith [hL3lb, hL0]
  set ℓ3 : ℝ := Real.log L3 with hℓ3def
  have hℓ3lb : ℓ ≤ ℓ3 := by rw [hℓ3def, hℓdef]; exact Real.log_le_log hL0 hL3lb
  have hlog2le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
  have hℓ3ub : ℓ3 ≤ 2 * ℓ := by
    rw [hℓ3def]
    calc Real.log L3 ≤ Real.log (2 * L) := Real.log_le_log hL30 hL3ub
      _ = Real.log 2 + ℓ := by rw [Real.log_mul (by norm_num) hL0.ne', ← hℓdef]
      _ ≤ 2 * ℓ := by linarith [hlog2le1, hℓ1100]
  have hℓ30 : 0 < ℓ3 := by linarith [hℓ3lb, hℓ0]
  have hℓ31100 : 1100 ≤ ℓ3 := by linarith [hℓ3lb, hℓ1100]
  -- region parameters
  set Θ : ℝ := vkTheta (3 * ρ.im) with hΘdef
  set Pinv : ℝ := 1000 * L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ) with hPinvdef
  have hL34pos : 0 < L3 ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL30 _
  have hPinvpos : 0 < Pinv := by rw [hPinvdef]; positivity
  have hΘval : Θ = 1 / 1000 / (L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ)) := by
    rw [hΘdef, vkTheta, ← hL3def, ← hℓ3def]
  have hΘPinv : Θ = 1 / Pinv := by
    rw [eq_div_iff (ne_of_gt hPinvpos), hΘval, hPinvdef]
    field_simp [ne_of_gt hL34pos, ne_of_gt hℓ30]
  have hΘ0 : 0 < Θ := by rw [hΘPinv]; positivity
  set Mζ : ℝ := K * L3 with hMζdef
  have hMζpos : 0 < Mζ := by rw [hMζdef]; positivity
  have hMζ1 : 1 ≤ Mζ := by
    rw [hMζdef]; nlinarith [hK, hL3lb, hL3]
  -- Pinv ≥ 2 (so Θ ≤ 1/2)
  have hPinv2 : 2 ≤ Pinv := by
    rw [hPinvdef]
    have h1 : (1 : ℝ) ≤ L3 ^ ((3 : ℝ) / 4) := Real.one_le_rpow (by linarith [hL3lb, hL3]) (by norm_num)
    have h2 : (1 : ℝ) ≤ ℓ3 ^ (2 : ℕ) := one_le_pow₀ (by linarith [hℓ31100])
    nlinarith [h1, h2]
  have hΘ12 : Θ ≤ 1 / 2 := by
    rw [hΘPinv]; rw [div_le_div_iff₀ hPinvpos (by norm_num)]; linarith [hPinv2]
  -- the box growth
  have hgrowth : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
      ‖riemannZeta z‖ ≤ Mζ := by
    intro z h1 h2 h3 h4
    rw [hΘdef] at h1; rw [hMζdef]
    exact pow_uniform_growth hK ht₀ hg hγe hγt₀ z h1 h2 h3 h4
  -- Lq and the log-argument bound
  set W : ℝ := Real.log (20 * Pinv * Mζ) with hWdef
  set Lq : ℝ := 8 + 700 * Pinv * W with hLqdef
  -- W = log(20000 K) + (7/4) ℓ3 + 2 log ℓ3
  have hℓ3log : 0 ≤ Real.log ℓ3 := Real.log_nonneg (by linarith [hℓ31100])
  have hWeq : W = Real.log (20000 * K) + (7 / 4) * ℓ3 + 2 * Real.log ℓ3 := by
    have hPinvne : Pinv ≠ 0 := ne_of_gt hPinvpos
    have hL3ne : L3 ≠ 0 := ne_of_gt hL30
    have hℓ3ne : ℓ3 ≠ 0 := ne_of_gt hℓ30
    have h20000 : Real.log (20000 * K) = Real.log 20 + Real.log 1000 + Real.log K := by
      rw [show (20000 : ℝ) * K = 20 * 1000 * K by ring, Real.log_mul (by norm_num) hKpos.ne',
        Real.log_mul (by norm_num) (by norm_num)]
    rw [hWdef, Real.log_mul (by positivity) (ne_of_gt hMζpos),
      Real.log_mul (by norm_num) hPinvne, hMζdef, Real.log_mul hKpos.ne' hL3ne,
      hPinvdef, Real.log_mul (by positivity) (pow_ne_zero 2 hℓ3ne),
      Real.log_mul (by norm_num) (ne_of_gt hL34pos), Real.log_rpow hL30, Real.log_pow,
      ← hℓ3def, h20000]
    push_cast; ring
  -- W ≤ 2 ℓ3  (log-power bound)
  have hlogℓ3 : Real.log ℓ3 ≤ 2 * Real.sqrt ℓ3 := log_le_two_sqrt hℓ30
  have hsqℓ3 : (32 : ℝ) ≤ Real.sqrt ℓ3 := by
    have h := Real.sqrt_le_sqrt (show (1024 : ℝ) ≤ ℓ3 by linarith [hℓ31100])
    rwa [show (1024 : ℝ) = 32 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 32)] at h
  have hsqℓ3sq : Real.sqrt ℓ3 ^ 2 = ℓ3 := Real.sq_sqrt hℓ30.le
  have hlog20K : Real.log (20000 * K) ≤ ℓ3 / 8 := by
    have : Real.log (20000 * K) ≤ ℓ / 8 := by linarith [hℓK]
    linarith [hℓ3lb, this]
  have hWub : W ≤ 2 * ℓ3 := by
    rw [hWeq]
    have h2logℓ3 : 2 * Real.log ℓ3 ≤ ℓ3 / 8 := by
      nlinarith [hlogℓ3, hsqℓ3, hsqℓ3sq, Real.sqrt_nonneg ℓ3]
    linarith [hlog20K, h2logℓ3]
  have hW1 : (1 : ℝ) ≤ W := by
    have h40 : (40 : ℝ) ≤ 20 * Pinv * Mζ := by nlinarith [hPinv2, hMζ1, hPinvpos]
    have he40 : Real.exp 1 ≤ 20 * Pinv * Mζ :=
      le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) h40
    rw [hWdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he40
  have hLqgeP : Pinv ≤ Lq := by
    rw [hLqdef]
    have hkey : 700 * Pinv * 1 ≤ 700 * Pinv * W := by
      apply mul_le_mul_of_nonneg_left hW1 (by positivity)
    nlinarith [hkey, hPinvpos]
  have hLq0 : 0 < Lq := lt_of_lt_of_le hPinvpos hLqgeP
  -- the three gates
  have hσΘ : (1 : ℝ) / 2 / Lq ≤ Θ / 2 := by
    rw [hΘPinv, div_div, div_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [hLqgeP])
  have hwΘ : (1 : ℝ) / 2 / (7 * Lq) ≤ 11 / 14 * Θ := by
    rw [hΘPinv, mul_one_div, div_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hLqgeP, hPinvpos, hLq0]
  have hchainC : 8 + 5 * ((120 / (6 * Θ / 7)) * Real.log (4 * (5 * Mζ / Θ)))
      ≤ Lq / (2 * (1 / 2)) := by
    have h1 : (120 : ℝ) / (6 * Θ / 7) = 140 * Pinv := by
      rw [hΘPinv]; field_simp [ne_of_gt hPinvpos]; ring
    have h2 : (4 : ℝ) * (5 * Mζ / Θ) = 20 * Pinv * Mζ := by
      rw [hΘPinv]; field_simp [ne_of_gt hPinvpos]; ring
    rw [h1, h2, ← hWdef, show (2 : ℝ) * (1 / 2) = 1 by norm_num, div_one, hLqdef]
    exact le_of_eq (by ring)
  -- run the bridge
  have hreg := region_of_uniform_growth hρ0 hβ1 (Θ := Θ) (Mζ := Mζ) (Lq := Lq) (dd := 1 / 2)
    hΘ0 hΘ12 hγ2 hMζ1 (by norm_num) (by norm_num) hLq0 hσΘ hwΘ hchainC hgrowth
  -- the width bound: 14 Lq ≤ 2.674e8 · L^{3/4} · ℓ³
  -- first: Pinv ≤ 6800 · L^{3/4} · ℓ²  (via L3 ≤ 2L, ℓ3 ≤ 2ℓ)
  have hL34le : L3 ^ ((3 : ℝ) / 4) ≤ 2 * L ^ ((3 : ℝ) / 4) := by
    have h1 : L3 ^ ((3 : ℝ) / 4) ≤ (2 * L) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hL30.le hL3ub (by norm_num)
    have h2 : (2 * L) ^ ((3 : ℝ) / 4) = 2 ^ ((3 : ℝ) / 4) * L ^ ((3 : ℝ) / 4) :=
      Real.mul_rpow (by norm_num) hL0.le
    have h3 : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
      calc (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hL34nn : 0 ≤ L ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hL0.le _
    rw [h2] at h1; nlinarith [h1, h3, hL34nn]
  have hL34nn : 0 ≤ L ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hL0.le _
  have hℓ3sqle : ℓ3 ^ (2 : ℕ) ≤ 4 * ℓ ^ (2 : ℕ) := by
    have := pow_le_pow_left₀ hℓ30.le hℓ3ub 2
    calc ℓ3 ^ (2 : ℕ) ≤ (2 * ℓ) ^ (2 : ℕ) := this
      _ = 4 * ℓ ^ (2 : ℕ) := by ring
  have hPinvle : Pinv ≤ 8000 * (L ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ)) := by
    have hℓ3nn : (0 : ℝ) ≤ ℓ3 ^ (2 : ℕ) := by positivity
    have hprod := mul_le_mul hL34le hℓ3sqle hℓ3nn (by positivity : (0:ℝ) ≤ 2 * L ^ ((3:ℝ)/4))
    calc Pinv = 1000 * (L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ)) := by rw [hPinvdef]; ring
      _ ≤ 1000 * ((2 * L ^ ((3 : ℝ) / 4)) * (4 * ℓ ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 8000 * (L ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ)) := by ring
  -- Lq ≤ 1.91e7 · L^{3/4} · ℓ³
  have hDpos : 0 < L ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ) := by positivity
  have hD1 : (1 : ℝ) ≤ L ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ) := by
    have h1 : (1 : ℝ) ≤ L ^ ((3 : ℝ) / 4) := Real.one_le_rpow (by linarith [hL3]) (by norm_num)
    have h2 : (1 : ℝ) ≤ ℓ ^ (3 : ℕ) := one_le_pow₀ (by linarith [hℓ1100])
    nlinarith [h1, h2]
  have hLqbnd : Lq ≤ 22500000 * (L ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)) := by
    rw [hLqdef]
    -- 700 · Pinv · W ≤ 700 · (8000 L^{3/4} ℓ²) · (4 ℓ)  = 2.24e7 · L^{3/4} ℓ³
    have hWnn : 0 ≤ W := by linarith [hW1]
    have hPWle : Pinv * W ≤ 8000 * (L ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ)) * (4 * ℓ) := by
      have hW4ℓ : W ≤ 4 * ℓ := by linarith [hWub, hℓ3ub]
      calc Pinv * W ≤ (8000 * (L ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ))) * W :=
            mul_le_mul_of_nonneg_right hPinvle hWnn
        _ ≤ (8000 * (L ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ))) * (4 * ℓ) :=
            mul_le_mul_of_nonneg_left hW4ℓ (by positivity)
    have hℓ23 : ℓ ^ (2 : ℕ) * ℓ = ℓ ^ (3 : ℕ) := by ring
    have hbound : 700 * Pinv * W ≤ 22400000 * (L ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)) := by
      have hh : 700 * (Pinv * W) ≤ 700 * (8000 * (L ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ)) * (4 * ℓ)) :=
        mul_le_mul_of_nonneg_left hPWle (by norm_num)
      nlinarith [hh, hℓ23, hL34nn]
    nlinarith [hbound, hD1]
  -- convert width: 1/(14 Lq) ≥ (1/10⁹)/(L^{3/4} ℓ³)
  have h14Lq : 14 * Lq ≤ 315000000 * (L ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)) := by nlinarith [hLqbnd]
  have hwidth : (1 / 10 ^ 9) * (1 / (L ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))) ≤ 1 / 2 / (7 * Lq) := by
    rw [show (1 : ℝ) / 2 / (7 * Lq) = 1 / (14 * Lq) by ring,
      show (1 / 10 ^ 9) * (1 / (L ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)))
        = 1 / (10 ^ 9 * (L ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))) by ring]
    refine one_div_le_one_div_of_le (by linarith [hLq0]) ?_
    nlinarith [h14Lq, hDpos]
  -- assemble
  have hfin : (1 / 10 ^ 9) * (1 / (L ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))) ≤ 1 - ρ.re :=
    le_trans hwidth (by linarith [hreg])
  linarith [hfin]

/-! ## THE POWER ZERO-FREE REGION (conditional on the VK growth `zeta_growth_pow`) -/

/-- **The power zero-free region, emitted from the VK growth.**  GIVEN the Vinogradov–Korobov strip
growth `zeta_growth_pow` (`ZetaGrowthPow`), there is an explicit `c > 0` and threshold `T₀` such that
every ζ-zero `ρ` of height `|Im ρ| ≥ T₀` satisfies
`Re ρ ≤ 1 − c/((log|Im ρ|)^{3/4}(log log|Im ρ|)³)` — the **power** shape `θ = 3/4 < 1`.

This is the *emission*: the whole content of the power region modulo the growth input.  The growth
`zeta_growth_pow` (rung R6) is what the block ladder R5b feeds; this theorem shows the region follows.
`c = 1/10⁹`, `T₀ = exp(exp(8·log(20000K) + 1100)) + t₀ + 3` are design-grade and astronomically lazy;
only the width SHAPE `1/((log t)^{3/4}(log log t)³)` (`θ = 3/4`) is the content — and that shape is
what the Montgomery–Renyi gate consumes.  Negative-height zeros via `riemannZeta_conj_zero`. -/
theorem zeta_zero_free_region_pow_of_growth (hgrow : ZetaGrowthPow) :
    ∃ c T₀ : ℝ, 0 < c ∧ 3 ≤ T₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 → T₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - c / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ)) := by
  obtain ⟨K, t₀, hK, ht₀, hg⟩ := hgrow
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  set A : ℝ := 8 * Real.log (20000 * K) + 1100 with hAdef
  have hA1100 : 1100 ≤ A := by
    have : (0 : ℝ) ≤ Real.log (20000 * K) := Real.log_nonneg (by nlinarith [hK])
    rw [hAdef]; linarith
  have hEpos : 0 < Real.exp (Real.exp A) := Real.exp_pos _
  refine ⟨1 / 10 ^ 9, Real.exp (Real.exp A) + t₀ + 3, by norm_num, by linarith [hEpos, ht₀], ?_⟩
  -- the positive-height core (then conjugation for negative heights)
  have hpos : ∀ σ : ℂ, riemannZeta σ = 0 → Real.exp (Real.exp A) + t₀ + 3 ≤ σ.im →
      σ.re ≤ 1 - (1 / 10 ^ 9) / ((Real.log σ.im) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log σ.im)) ^ (3 : ℕ)) := by
    intro σ hσ0 hσim
    have hβ1 : σ.re < 1 := by
      by_contra h; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hσ0
    -- discharge the core thresholds
    have hσimE : Real.exp (Real.exp A) ≤ σ.im := by linarith [ht₀, hσim]
    have hγ2 : 2 ≤ σ.im := by linarith [hEpos, ht₀, hσim]
    have hexpA1 : 1 < Real.exp A := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith [hA1100])
    have hEe : Real.exp 1 < Real.exp (Real.exp A) := Real.exp_lt_exp.mpr hexpA1
    have hγe : Real.exp 1 < σ.im - 1 := by linarith [hEe, hσim, ht₀, hEpos]
    have hγt₀ : t₀ ≤ σ.im - 1 := by linarith [hEpos, hσim]
    have hlogE : Real.log (Real.exp (Real.exp A)) = Real.exp A := Real.log_exp _
    have hlogσE : Real.exp A ≤ Real.log σ.im := by
      rw [← hlogE]; exact Real.log_le_log hEpos hσimE
    have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have hexpA3 : (3 : ℝ) ≤ Real.exp A :=
      le_trans hexp2 (Real.exp_le_exp.mpr (by linarith [hA1100]))
    have hL3 : 3 ≤ Real.log σ.im := le_trans hexpA3 hlogσE
    have hℓK : 8 * Real.log (20000 * K) + 1100 ≤ Real.log (Real.log σ.im) := by
      rw [← hAdef]
      calc A = Real.log (Real.exp A) := (Real.log_exp A).symm
        _ ≤ Real.log (Real.log σ.im) := Real.log_le_log (Real.exp_pos A) hlogσE
    have hcore := zeta_zero_free_pow_core hK ht₀ hg hσ0 hβ1 hγ2 hγe hγt₀ hL3 hℓK
    rwa [mul_one_div] at hcore
  intro ρ hρ0 hγ
  by_cases hsign : 0 ≤ ρ.im
  · rw [abs_of_nonneg hsign] at hγ ⊢; exact hpos ρ hρ0 hγ
  · rw [abs_of_neg (not_le.mp hsign)] at hγ ⊢
    have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hsign; simp at hsign
    have hconj0 : riemannZeta ((starRingEnd ℂ) ρ) = 0 := riemannZeta_conj_zero hρ1 hρ0
    have h := hpos ((starRingEnd ℂ) ρ) hconj0 (by rw [Complex.conj_im]; exact hγ)
    rwa [Complex.conj_im, Complex.conj_re] at h

end Salt.Vk
