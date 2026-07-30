/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.VkTwistStrip
import Salt.MR.VkTwistRegionProbe

/-!
# STONE B — the χ-VK ZERO-FREE REGION, UNCONDITIONAL (`χ² ≠ 1`)

The B-probe (`Salt/MR/VkTwistRegionProbe.lean`) built the growth→region bridge for `L(·,χ)` at VK
width and left ONE hypothesis open: the strip growth (`hgrowth`, `hgrowth2`).  Stone A
(`Salt/MR/VkTwistStrip.lean`, `vk_char_box_growth`) discharges it.  This file composes the two and
lands the **unconditional** VK-width zero-free region for `L(·,χ)`, `χ² ≠ 1`:

  `Re ρ ≤ 1 − c(A) / ((log|Im ρ|)^{3/4}·(log log|Im ρ|)³)`,  `c(A) = 1/(10⁸(A+7))`,

for every zero `ρ` of height `|Im ρ| ≥ exp(exp 100) + 1`, under the `q`-scale gate

  `log(20000·vkStripConst q) ≤ A·log log|Im ρ|`,  `vkStripConst q = 5000 q`.

**This is the port's ONE missing analytic stone** (⟦SPECTRUM-SCOPE⟧): the `3/4` exponent — the
power shape the §8.3 pins need and the classical `1/log(q(|t|+2))` width cannot give.

## The `q`-gate, and why KR-2 is benign

The gate is `log(20000·5000·q) ≤ A·loglog|Im ρ|`, i.e. `log(10⁸) + log q ≤ A·loglog|Im ρ|`.  At the
port's parameters (`q ≤ (log H)^12`, heights polynomial in `H`) it holds with `A` a small absolute
constant — `A ≈ 18` covers `log q ≤ 12·loglog H` with room.  The growth constant reaches the width
only through `log M` (the width law `Θ/(14(8Θ + 700 log(20M/Θ)))`), so the level cost is ADDITIVE
inside a logarithm and never touches the `3/4`.  KR-2 confirmed benign, twice over: stone A's
`Cq` came out LINEAR in `q` (the crude level bound beats Pólya–Vinogradov at truncation length
`t²`), not `q^{3/2}(1+log q)`.

## The height floor, re-tuned

The probe's `vk_width_shape` demanded `1100 ≤ loglog|Im ρ|` (a crude `log x ≤ 2√x` step at
`6 log ℓ₃ ≤ ℓ₃`).  Stone A's coarser growth needs only `2 log ℓ₃ ≤ ℓ₃`, so the floor drops to
`100 ≤ loglog|Im ρ|` — which is EXACTLY what the landed height floor `exp(exp 100)` already
supplies (gap-4 of the probe's list, discharged: no extra height demand).

## The growth SHAPE deviation (favourable), and the width arithmetic

Stone A delivers `M = Cq·(1 + log 3γ)` on the FULL strip `Θ = vkTheta(3γ)`, where the freeze
expected `Cq·(log)^{3/4}(loglog)⁴` — the sharper profile is a near-1-line phenomenon (it needs
`σ ≥ 1 − Θ/2`, i.e. half the strip).  Keeping the full strip is worth about `2×` in the final
constant, and the shape loss is `(1/4)·loglog` INSIDE a logarithm.  `vk_strip_width_shape` below
is the resulting arithmetic: `log(20M/Θ) ≤ (A+6)·ℓ` and `Pinv ≤ 8000·Lg^{3/4}ℓ²`, giving the
`10⁸(A+7)` constant.

## The negative-height half (the probe's gap-3)

`LFunction_inv_conj`: `L(χ⁻¹, conj s) = conj(L(χ,s))` for any `χ ≠ 1` — the general-character twin
of `Salt.SW.LFunction_conj` (which is real-character only, `χ² = 1`), proved the same way (the
series on `Re s > 1` plus the identity theorem), with `conj(χ(n)) = χ⁻¹(n)`
(`MulChar.star_apply'`) in place of the real-coefficient step.  A zero at negative height
transports to `χ⁻¹` at positive height, and `χ⁻¹` satisfies the same two hypotheses
(`χ⁻¹ ≠ 1`, `(χ⁻¹)² ≠ 1`) at the same level, hence the same gate.

## Traps observed

* no `set L := …` (the banked `LSeries`-notation collision — this file opens the notation);
* `χ²` lives mod `q`, NOT mod `q²`, so `vkStripConst q` serves both instances;
* the width law's `Θ` is the strip half-width at the DOUBLED-height box top, `vkTheta (3 Im ρ)`;
* the four log scales: everything here is `log|Im ρ|`, never `log X` or `loglog H`.
-/

noncomputable section

namespace Salt.MR

open Complex DirichletCharacter Salt.Vk
open scoped LSeries.notation

/-! ## §1 — the width arithmetic at stone A's growth shape -/

set_option maxHeartbeats 1600000 in
-- Pure real-analysis arithmetic: staged rpow/log comparisons through `nlinarith`, as in the
-- probe's own `vk_width_shape`.
/-- **The width arithmetic** (no L-function content).  At the landed `q`-free half-width
`Θ = vkTheta t` (`t = 3γ`, so `L3 = log 3γ ∈ [Lg, 2Lg]`, `ℓ3 = log L3 ∈ [ℓ, 2ℓ]`) and stone A's
growth `M = Cq·(1 + L3)`, the width law's denominator obeys

  `log(20M/Θ) = log(20000 Cq) + log(1 + L3) + (3/4)ℓ3 + 2 log ℓ3 ≤ (A + 6)·ℓ`

under the `q`-scale gate `log(20000 Cq) ≤ A·ℓ` and the height floor `ℓ ≥ 100`, whence

  `Θ / (14(8Θ + 700 log(20M/Θ))) ≥ (1/(10⁸(A+7)))·1/(Lg^{3/4}ℓ³)`.

The `3/4` exponent comes entirely from `Θ`; `M` enters only through `log M`. -/
private lemma vk_strip_width_shape {Lg ℓ L3 ℓ3 Θ M Cq A : ℝ}
    (hLg3 : 3 ≤ Lg) (hℓ100 : 100 ≤ ℓ)
    (hL3lb : Lg ≤ L3) (hL3ub : L3 ≤ 2 * Lg) (hℓ3def : ℓ3 = Real.log L3)
    (hℓ3lb : ℓ ≤ ℓ3) (hℓ3ub : ℓ3 ≤ 2 * ℓ)
    (hCq : 1 ≤ Cq) (hA1 : 1 ≤ A) (hgate : Real.log (20000 * Cq) ≤ A * ℓ)
    (hΘval : Θ = 1 / 1000 / (L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ)))
    (hMval : M = Cq * (1 + L3)) :
    0 < Θ ∧ Θ ≤ 1 / 2 ∧ 1 ≤ M ∧
      (1 / (10 ^ 8 * (A + 7))) * (1 / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)))
        ≤ Θ / (14 * (8 * Θ + 700 * Real.log (20 * M / Θ))) := by
  have hLg0 : 0 < Lg := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hL30 : 0 < L3 := by linarith
  have hL31' : (1 : ℝ) ≤ L3 := by linarith
  have hℓ3100 : 100 ≤ ℓ3 := by linarith
  have hℓ30 : 0 < ℓ3 := by linarith
  have hCqpos : (0 : ℝ) < Cq := by linarith
  have h20000Cq : (0 : ℝ) < 20000 * Cq := by linarith
  have hL34pos : 0 < L3 ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL30 _
  have hL31 : (1 : ℝ) ≤ L3 ^ ((3 : ℝ) / 4) := Real.one_le_rpow (by linarith) (by norm_num)
  have hℓ3sq1 : (1 : ℝ) ≤ ℓ3 ^ (2 : ℕ) := one_le_pow₀ (by linarith)
  have hLg34nn : 0 ≤ Lg ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hLg0.le _
  -- `Θ = 1/Pinv`, `Pinv = 1000 L3^{3/4} ℓ3²`
  set Pinv : ℝ := 1000 * L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ) with hPinvdef
  have hPinvpos : 0 < Pinv := by rw [hPinvdef]; positivity
  have hΘPinv : Θ = 1 / Pinv := by
    rw [eq_div_iff (ne_of_gt hPinvpos), hΘval, hPinvdef]
    field_simp [ne_of_gt hL34pos, ne_of_gt hℓ30]
  have hΘ0 : 0 < Θ := by rw [hΘPinv]; positivity
  have hPinv2 : 2 ≤ Pinv := by rw [hPinvdef]; nlinarith [hL31, hℓ3sq1]
  have hΘ12 : Θ ≤ 1 / 2 := by
    rw [hΘPinv, div_le_div_iff₀ hPinvpos (by norm_num)]; linarith
  have hM1 : 1 ≤ M := by rw [hMval]; nlinarith [hCq, hL31']
  refine ⟨hΘ0, hΘ12, hM1, ?_⟩
  -- the logarithm
  set W : ℝ := Real.log (20 * M / Θ) with hWdef
  have hWeq : W = Real.log (20000 * Cq) + Real.log (1 + L3)
      + (3 / 4) * ℓ3 + 2 * Real.log ℓ3 := by
    have h20M : 20 * M / Θ
        = 20000 * Cq * (1 + L3) * L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ) := by
      rw [hMval, hΘval]
      field_simp [ne_of_gt hL34pos, ne_of_gt hℓ30]
      ring
    rw [hWdef, h20M,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hL30, Real.log_pow, ← hℓ3def]
    push_cast; ring
  have hlog2le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  -- `log(1 + L3) ≤ log 2 + ℓ3`
  have hlog1L3 : Real.log (1 + L3) ≤ 1 + ℓ3 := by
    have h1 : Real.log (1 + L3) ≤ Real.log (2 * L3) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt hL30), ← hℓ3def] at h1
    linarith
  -- `2 log ℓ3 ≤ ℓ3`
  have hlogℓ3le : 2 * Real.log ℓ3 ≤ ℓ3 := by
    have h1 : Real.log ℓ3 ≤ 2 * Real.sqrt ℓ3 := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hℓ30)
      rw [Real.log_sqrt hℓ30.le] at h
      linarith [Real.sqrt_nonneg ℓ3]
    have h2 : (10 : ℝ) ≤ Real.sqrt ℓ3 := by
      have h := Real.sqrt_le_sqrt (show (100 : ℝ) ≤ ℓ3 by linarith)
      rwa [show (100 : ℝ) = 10 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 10)] at h
    have h3 : Real.sqrt ℓ3 ^ 2 = ℓ3 := Real.sq_sqrt hℓ30.le
    nlinarith [h1, h2, h3, Real.sqrt_nonneg ℓ3]
  have hWub : W ≤ (A + 6) * ℓ := by
    rw [hWeq]
    nlinarith [hgate, hlog1L3, hlogℓ3le, hℓ3ub, hℓ0, hℓ100]
  have hW1 : (1 : ℝ) ≤ W := by
    have h20 : (40 : ℝ) ≤ 20 * M / Θ := by
      rw [le_div_iff₀ hΘ0]; nlinarith [hM1, hΘ12]
    have he : Real.exp 1 ≤ 20 * M / Θ :=
      le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) h20
    rw [hWdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
  -- `Pinv ≤ 8000 Lg^{3/4}ℓ²` and `8Θ + 700 W ≤ 704(A+6)ℓ`
  have hL34le : L3 ^ ((3 : ℝ) / 4) ≤ 2 * Lg ^ ((3 : ℝ) / 4) := by
    have h1 : L3 ^ ((3 : ℝ) / 4) ≤ (2 * Lg) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hL30.le hL3ub (by norm_num)
    have h2 : (2 * Lg) ^ ((3 : ℝ) / 4) = 2 ^ ((3 : ℝ) / 4) * Lg ^ ((3 : ℝ) / 4) :=
      Real.mul_rpow (by norm_num) hLg0.le
    have h3 : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
      calc (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    rw [h2] at h1; nlinarith [h1, h3, hLg34nn]
  have hℓ3sqle : ℓ3 ^ (2 : ℕ) ≤ 4 * ℓ ^ (2 : ℕ) := by
    calc ℓ3 ^ (2 : ℕ) ≤ (2 * ℓ) ^ (2 : ℕ) := pow_le_pow_left₀ hℓ30.le hℓ3ub 2
      _ = 4 * ℓ ^ (2 : ℕ) := by ring
  have hPinvle : Pinv ≤ 8000 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ)) := by
    have hℓ3nn : (0 : ℝ) ≤ ℓ3 ^ (2 : ℕ) := by positivity
    have hprod := mul_le_mul hL34le hℓ3sqle hℓ3nn
      (by positivity : (0:ℝ) ≤ 2 * Lg ^ ((3:ℝ)/4))
    calc Pinv = 1000 * (L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ)) := by rw [hPinvdef]; ring
      _ ≤ 1000 * ((2 * Lg ^ ((3 : ℝ) / 4)) * (4 * ℓ ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 8000 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ)) := by ring
  set den : ℝ := 8 * Θ + 700 * W with hdendef
  have hden0 : 0 < den := by rw [hdendef]; nlinarith [hΘ0, hW1]
  have hdenub : den ≤ 704 * ((A + 6) * ℓ) := by
    rw [hdendef]; nlinarith [hΘ12, hW1, hWub, hA1, hℓ100]
  -- the final comparison
  set D : ℝ := Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hℓ3' : ℓ ^ (2 : ℕ) * ℓ = ℓ ^ (3 : ℕ) := by ring
  have step : 14 * den * Pinv ≤ 10 ^ 8 * (A + 7) * D := by
    calc 14 * den * Pinv
        ≤ 14 * (704 * ((A + 6) * ℓ)) * (8000 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ))) := by
          apply mul_le_mul (by linarith [hdenub]) hPinvle hPinvpos.le (by positivity)
      _ = 78848000 * (A + 6) * (Lg ^ ((3 : ℝ) / 4) * (ℓ ^ (2 : ℕ) * ℓ)) := by ring
      _ = 78848000 * (A + 6) * D := by rw [hℓ3', hDdef]
      _ ≤ 10 ^ 8 * (A + 7) * D := by nlinarith [hDpos, hA1]
  have hΘPinv1 : Θ * Pinv = 1 := by rw [hΘPinv]; field_simp
  have hcmp : (1 : ℝ) / (10 ^ 8 * (A + 7) * D) ≤ Θ / (14 * den) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Θ * (14 * den * Pinv) = 14 * den := by
      rw [show Θ * (14 * den * Pinv) = (14 * den) * (Θ * Pinv) from by ring, hΘPinv1, mul_one]
    rw [one_mul, ← h1]
    exact mul_le_mul_of_nonneg_left step hΘ0.le
  have heq : (1 / (10 ^ 8 * (A + 7))) * (1 / D) = 1 / (10 ^ 8 * (A + 7) * D) := by
    rw [div_mul_div_comm, one_mul]
  rw [heq]
  exact hcmp

/-! ## §2 — THE REGION at positive height -/

set_option maxHeartbeats 800000 in
-- The log-scale bookkeeping (`L3 ∈ [Lg, 2Lg]`, `ℓ3 ∈ [ℓ, 2ℓ]`) plus the width-law call.
/-- **STONE B — the χ-VK ZERO-FREE REGION, positive height, UNCONDITIONAL.**  For `χ mod q` with
`χ ≠ 1` and `χ² ≠ 1`, every zero `ρ` of `L(·,χ)` with `Re ρ < 1` and `Im ρ ≥ exp(exp 100) + 1`
obeys, under the `q`-scale gate `log(20000·vkStripConst q) ≤ A·log log Im ρ`,

  `Re ρ ≤ 1 − (1/(10⁸(A+7)))·1/((log Im ρ)^{3/4}(log log Im ρ)³)`.

The probe's bridge (`LFunction_zero_free_width_law`) at stone A's box growth
(`vk_char_box_growth`, for `χ` AND `χ²`), with the width arithmetic `vk_strip_width_shape`.
Nothing is hypothetical: the only inputs are `hχ1`, `hχ2`, the height floor and the gate. -/
theorem LFunction_zero_free_region_vk_pos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) {A : ℝ} (hA1 : 1 ≤ A)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hβ1 : ρ.re < 1)
    (hheight : Real.exp (Real.exp 100) + 1 ≤ ρ.im)
    (hgate : Real.log (20000 * vkStripConst q) ≤ A * Real.log (Real.log ρ.im)) :
    ρ.re ≤ 1 - (1 / (10 ^ 8 * (A + 7)))
      * (1 / ((Real.log ρ.im) ^ ((3 : ℝ) / 4) * (Real.log (Real.log ρ.im)) ^ (3 : ℕ))) := by
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hγfloor : Real.exp (Real.exp 100) ≤ ρ.im - 1 := by linarith
  have hγpos : 0 < ρ.im := by linarith [Real.exp_pos (Real.exp 100)]
  have hγ2 : (2 : ℝ) ≤ ρ.im := by linarith
  -- the four log scales
  set Lg : ℝ := Real.log ρ.im with hLgdef
  set ell : ℝ := Real.log Lg with helldef
  set L3 : ℝ := Real.log (3 * ρ.im) with hL3def
  set ell3 : ℝ := Real.log L3 with hell3def
  have hLgbig : Real.exp 100 ≤ Lg := by
    rw [hLgdef, ← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLg3 : (3 : ℝ) ≤ Lg := by linarith [hLgbig, hexp100]
  have hLg0 : 0 < Lg := by linarith
  have hell100 : (100 : ℝ) ≤ ell := by
    rw [helldef, ← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLgbig
  have hell0 : 0 < ell := by linarith
  -- `L3 = log 3 + Lg ∈ [Lg, 2Lg]`, `ell3 ∈ [ell, 2 ell]`
  have hlog3le2 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)]
  have hL3eq : L3 = Real.log 3 + Lg := by
    rw [hL3def, Real.log_mul (by norm_num) hγpos.ne', hLgdef]
  have hL3lb : Lg ≤ L3 := by
    rw [hL3eq]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]
  have hL3ub : L3 ≤ 2 * Lg := by rw [hL3eq]; linarith
  have hL30 : 0 < L3 := by linarith
  have hell3lb : ell ≤ ell3 := by
    rw [hell3def, helldef]; exact Real.log_le_log hLg0 hL3lb
  have hlog2le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
  have hell3ub : ell3 ≤ 2 * ell := by
    rw [hell3def]
    calc Real.log L3 ≤ Real.log (2 * Lg) := Real.log_le_log hL30 hL3ub
      _ = Real.log 2 + ell := by rw [Real.log_mul (by norm_num) hLg0.ne', ← helldef]
      _ ≤ 2 * ell := by linarith
  -- the half-width and the growth ceiling
  set Θ : ℝ := vkTheta (3 * ρ.im) with hΘdef
  have hΘval : Θ = 1 / 1000 / (L3 ^ ((3 : ℝ) / 4) * ell3 ^ (2 : ℕ)) := by
    rw [hΘdef, vkTheta, ← hL3def, ← hell3def]
  set M : ℝ := vkStripConst q * (1 + L3) with hMdef
  obtain ⟨hΘ0, hΘ12, hM1, hshape⟩ := vk_strip_width_shape hLg3 hell100 hL3lb hL3ub hell3def
    hell3lb hell3ub (one_le_vkStripConst (q := q)) hA1 hgate hΘval hMdef
  -- stone A's box growth, at `χ` and at `χ²`
  have hgrowth : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
      ‖LFunction χ z‖ ≤ M := by
    intro z h1 h2 h3 h4
    rw [hMdef, hL3def]
    exact vk_char_box_growth χ hχ1 hγfloor z (by rw [← hΘdef]; exact h1) h2 h3 h4
  have hgrowth2 : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
      ‖LFunction (χ ^ 2) z‖ ≤ M := by
    intro z h1 h2 h3 h4
    rw [hMdef, hL3def]
    exact vk_char_box_growth (χ ^ 2) hχ2 hγfloor z (by rw [← hΘdef]; exact h1) h2 h3 h4
  have hwl := LFunction_zero_free_width_law hχ1 hχ2 hρ0 hβ1 hΘ0 hΘ12 hγ2 hM1 hgrowth hgrowth2
  linarith [hwl, hshape]

/-! ## §3 — the conjugation lemma (the probe's gap-3) and the two-sided region -/

/-- **The conjugation functional equation, general character.**  `L(χ⁻¹, conj s) = conj(L(χ,s))`
for every `χ ≠ 1`.  The general-character twin of `Salt.SW.LFunction_conj` (which needs `χ² = 1`):
the Dirichlet coefficients conjugate to `χ⁻¹`'s (`MulChar.star_apply'`), so
`conj ∘ L(χ) ∘ conj` agrees with `L(χ⁻¹)` on `Re s > 1`; both are entire
(`differentiable_LFunction`), and the identity theorem extends the agreement to `ℂ`. -/
lemma LFunction_inv_conj {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) (s : ℂ) :
    LFunction χ⁻¹ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (LFunction χ s) := by
  have hinv1 : χ⁻¹ ≠ 1 := by
    intro h; exact hχ1 (by rw [← inv_inv χ, h, inv_one])
  have hLdiff : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ1
  have hLdiff' : Differentiable ℂ (LFunction χ⁻¹) := differentiable_LFunction hinv1
  -- the composed conjugate is entire
  have hFdiff : Differentiable ℂ
      (fun z => (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) z))) := by
    intro z
    have h1 : DifferentiableAt ℂ (LFunction χ) ((starRingEnd ℂ) z) := hLdiff _
    have h2 := h1.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2
  -- agreement on the series half-plane
  have hser : ∀ z : ℂ, 1 < z.re →
      (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) z)) = LFunction χ⁻¹ z := by
    intro z hz
    have hzc : 1 < ((starRingEnd ℂ) z).re := by rwa [Complex.conj_re]
    have hterm : ∀ n : ℕ, (starRingEnd ℂ) (LSeries.term ↗χ ((starRingEnd ℂ) z) n)
        = LSeries.term ↗(χ⁻¹) z n := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
          Salt.SW.conj_natCast_cpow]
        congr 1
        rw [starRingEnd_apply, MulChar.star_apply']
    rw [LFunction_eq_LSeries χ hzc, LFunction_eq_LSeries χ⁻¹ hz]
    calc (starRingEnd ℂ) (LSeries ↗χ ((starRingEnd ℂ) z))
        = ∑' n, (starRingEnd ℂ) (LSeries.term ↗χ ((starRingEnd ℂ) z) n) := by
          rw [show LSeries ↗χ ((starRingEnd ℂ) z)
              = ∑' n, LSeries.term ↗χ ((starRingEnd ℂ) z) n from rfl, Complex.conj_tsum]
      _ = ∑' n, LSeries.term ↗(χ⁻¹) z n := tsum_congr hterm
      _ = LSeries ↗(χ⁻¹) z := rfl
  -- the identity theorem on `ℂ`
  have hana_F : AnalyticOnNhd ℂ
      (fun z => (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) z))) Set.univ :=
    hFdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hana_L : AnalyticOnNhd ℂ (LFunction χ⁻¹) Set.univ :=
    hLdiff'.differentiableOn.analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ z in nhdsWithin (2 : ℂ) {(2 : ℂ)}ᶜ,
      (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) z)) = LFunction χ⁻¹ z := by
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2' : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      simp only [Set.mem_setOf_eq, Complex.re_ofNat]; norm_num
    have hgt : ∀ᶠ z in nhds (2 : ℂ),
        (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) z)) = LFunction χ⁻¹ z := by
      filter_upwards [hopen1.mem_nhds h2'] with z hz
      exact hser z hz
    exact (hgt.filter_mono nhdsWithin_le_nhds).frequently
  have heqOn := hana_F.eqOn_of_preconnected_of_frequently_eq hana_L
    isPreconnected_univ (Set.mem_univ (2 : ℂ)) hfreq
  have hFs : (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) ((starRingEnd ℂ) s)))
      = LFunction χ⁻¹ ((starRingEnd ℂ) s) := heqOn (Set.mem_univ _)
  rw [Complex.conj_conj] at hFs
  exact hFs.symm

/-- Zeros transport to the conjugate character at the mirrored height. -/
lemma LFunction_inv_conj_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    {ρ : ℂ} (hρ : LFunction χ ρ = 0) : LFunction χ⁻¹ ((starRingEnd ℂ) ρ) = 0 := by
  rw [LFunction_inv_conj hχ1 ρ, hρ, map_zero]

/-- **STONE B's EXIT — THE χ-VK ZERO-FREE REGION, both heights.**  For `χ mod q` with `χ ≠ 1`,
`χ² ≠ 1`, every zero `ρ` of `L(·,χ)` with `Re ρ < 1` and `|Im ρ| ≥ exp(exp 100) + 1` obeys, under
the `q`-scale gate `log(20000·vkStripConst q) ≤ A·log log|Im ρ|`,

  `Re ρ ≤ 1 − (1/(10⁸(A+7)))·1/((log|Im ρ|)^{3/4}(log log|Im ρ|)³)`.

The negative-height half is the positive half at `χ⁻¹` and `conj ρ` (`LFunction_inv_conj_zero`);
`χ⁻¹` has the same level, so the SAME gate and the SAME constant serve. -/
theorem LFunction_zero_free_region_vk {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) {A : ℝ} (hA1 : 1 ≤ A)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hβ1 : ρ.re < 1)
    (hheight : Real.exp (Real.exp 100) + 1 ≤ |ρ.im|)
    (hgate : Real.log (20000 * vkStripConst q) ≤ A * Real.log (Real.log |ρ.im|)) :
    ρ.re ≤ 1 - (1 / (10 ^ 8 * (A + 7)))
      * (1 / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ))) := by
  have hEpos : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  rcases le_or_gt 0 ρ.im with hpos | hneg
  · rw [abs_of_nonneg hpos] at hheight hgate ⊢
    exact LFunction_zero_free_region_vk_pos hχ1 hχ2 hA1 hρ0 hβ1 hheight hgate
  · rw [abs_of_neg hneg] at hheight hgate ⊢
    -- transport to `χ⁻¹` at the mirrored height
    have hinv1 : χ⁻¹ ≠ 1 := by
      intro h; exact hχ1 (by rw [← inv_inv χ, h, inv_one])
    have hinv2 : (χ⁻¹) ^ 2 ≠ 1 := by
      intro h
      refine hχ2 ?_
      rw [inv_pow] at h
      rw [← inv_inv (χ ^ 2), h, inv_one]
    have hzero := LFunction_inv_conj_zero hχ1 hρ0
    have hre : ((starRingEnd ℂ) ρ).re = ρ.re := Complex.conj_re ρ
    have him : ((starRingEnd ℂ) ρ).im = -ρ.im := Complex.conj_im ρ
    have hmain := LFunction_zero_free_region_vk_pos hinv1 hinv2 hA1 hzero
      (by rw [hre]; exact hβ1) (by rw [him]; exact hheight) (by rw [him]; exact hgate)
    rw [hre, him] at hmain
    exact hmain

end Salt.MR

end
