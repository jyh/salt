/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.RegionGrowth
import Salt.ExpSum.Strip

/-!
# VMVT-VK — the Littlewood zero-free region (`σ ≥ 1 − c·log log t / log t`)

The historic checkpoint.  The landed sub-Weyl growth `Salt.ExpSum.zeta_strip_family`
(`‖ζ(σ+it)‖ ≤ C·t^{1/(2^{k+2}(k−1))}·(1+log t)` on `σ ≥ 1 − 2^{−(k+2)}`, `t ≥ 4(k!)^6`), fed
through the growth-to-region bridge `region_of_uniform_growth` at the balanced short-interval
degree `k ≈ log₂ log t`, produces a zero-free region strictly wider than de la Vallée Poussin:
`ρ.re ≤ 1 − c·log log|γ| / log|γ|`.
-/

namespace Salt.Vk

open Complex
open scoped Topology

/-! ## Analytic thresholds -/

/-- `log x ≤ 2√x` for `x > 0` (via `log √x ≤ √x − 1`). -/
private lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h
  linarith [Real.sqrt_nonneg x]

/-- `x³/27 ≤ exp x` for `0 ≤ x` (cube of `1 + x/3 ≤ exp(x/3)`). -/
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

/-! ## The growth discharge — `zeta_strip_family` at fixed `k` over the sphere box -/

/-- **Uniform box growth from `zeta_strip_family`.**  For a fixed degree `k ≥ 4` and a height
`γ ≥ 2` above the factorial threshold (`4(k!)^6 ≤ γ − 1`), the sub-Weyl family bound gives the
single uniform bound `‖ζ z‖ ≤ C·(3γ)^e·(1+log 3γ)` (`e = 1/(2^{k+2}(k−1))`) over the whole box
`Re z ∈ [1 − 2^{−(k+2)}, 2]`, `Im z ∈ [γ−1, 3γ]` — the box containing every keep/drop sphere.
This is the exact `hgrowth` shape `region_of_uniform_growth` consumes at `Θ = 2^{−(k+2)}`. -/
lemma littlewood_uniform_growth {C : ℝ} (hC : 1 ≤ C)
    (hfam : ∀ k : ℕ, 4 ≤ k → ∀ σ t : ℝ,
      1 - 1 / (2 : ℝ) ^ (k + 2) ≤ σ → σ ≤ 2 → 4 * (k.factorial : ℝ) ^ 6 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * t ^ (1 / ((2 : ℝ) ^ (k + 2) * ((k : ℝ) - 1))) * (1 + Real.log t))
    {k : ℕ} (hk : 4 ≤ k) {γ : ℝ} (hγ2 : 2 ≤ γ) (hthr : 4 * (k.factorial : ℝ) ^ 6 ≤ γ - 1) :
    ∀ z : ℂ, 1 - 1 / (2 : ℝ) ^ (k + 2) ≤ z.re → z.re ≤ 2 → γ - 1 ≤ z.im → z.im ≤ 3 * γ →
      ‖riemannZeta z‖
        ≤ C * (3 * γ) ^ (1 / ((2 : ℝ) ^ (k + 2) * ((k : ℝ) - 1))) * (1 + Real.log (3 * γ)) := by
  intro z hre1 hre2 him1 him2
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  set e : ℝ := 1 / ((2 : ℝ) ^ (k + 2) * ((k : ℝ) - 1)) with he
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hzimpos : 0 < z.im := by linarith [him1, hγ2]
  have h3γpos : 0 < 3 * γ := by linarith [hγ2]
  -- apply the family at σ = z.re, t = z.im
  have hthr' : 4 * (k.factorial : ℝ) ^ 6 ≤ z.im := le_trans hthr (by linarith [him1])
  have hzrw : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := Complex.re_add_im z
  have hfz := hfam k hk z.re z.im hre1 hre2 hthr'
  rw [hzrw] at hfz
  -- monotone in base and in log
  have hbase : z.im ^ e ≤ (3 * γ) ^ e :=
    Real.rpow_le_rpow (le_of_lt hzimpos) him2 he0
  have hlog : 1 + Real.log z.im ≤ 1 + Real.log (3 * γ) := by
    have := Real.log_le_log hzimpos him2; linarith
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC
  have hstep : C * z.im ^ e * (1 + Real.log z.im)
      ≤ C * (3 * γ) ^ e * (1 + Real.log (3 * γ)) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hbase hCpos.le
    · exact hlog
    · have : 0 ≤ Real.log z.im := Real.log_nonneg (by linarith [him1, hγ2])
      linarith
    · positivity
  exact le_trans hfz hstep

/-! ## The abstract-`k` core — gates + width algebra at a balanced degree -/

set_option maxHeartbeats 1600000 in
-- The core threads the region bridge, the three gate discharges and the four-term width bound
-- (Lq ≤ 6301·L/ℓ) through one declaration with many `nlinarith`/`field_simp` steps.
/-- **Littlewood region at a balanced degree `k`** (abstract-`k` core).  A positive-height ζ-zero
`ρ` (`ρ.im ≥ 2`, `ρ.re < 1`) with a degree `k ≥ 4` satisfying the balance bracket
`2^{k+2} ≤ L/ℓ²`, `k+2 ≤ 2ℓ`, `(1/2)ℓ ≤ k−1` (`L = log ρ.im`, `ℓ = log L = log log ρ.im`), the
factorial threshold `4(k!)^6 ≤ ρ.im − 1`, and the height thresholds `3 ≤ L`,
`log 20 + log C + 4 ≤ ℓ`, `8 ≤ L/ℓ` obeys the Littlewood bound
`ρ.re ≤ 1 − (1/88214)·log log ρ.im / log ρ.im`.

Feeds `littlewood_uniform_growth` through `region_of_uniform_growth` at `Θ = 2^{−(k+2)}`,
`dd = 1/2`, `Lq = 8 + 700·2^{k+2}·log(20·2^{k+2}·Mζ)`; the three gates reduce to `2^{k+2} ≤ Lq`
and the width `dd/(7Lq) = 1/(14 Lq)` is bounded below via `Lq ≤ 6301·L/ℓ`. -/
theorem zeta_zero_free_littlewood_core {C : ℝ} (hC : 1 ≤ C)
    (hfam : ∀ k : ℕ, 4 ≤ k → ∀ σ t : ℝ,
      1 - 1 / (2 : ℝ) ^ (k + 2) ≤ σ → σ ≤ 2 → 4 * (k.factorial : ℝ) ^ 6 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * t ^ (1 / ((2 : ℝ) ^ (k + 2) * ((k : ℝ) - 1))) * (1 + Real.log t))
    {ρ : ℂ} (hρ0 : riemannZeta ρ = 0) (hβ1 : ρ.re < 1) {k : ℕ} (hk : 4 ≤ k)
    (hγ2 : 2 ≤ ρ.im) (hthr : 4 * (k.factorial : ℝ) ^ 6 ≤ ρ.im - 1)
    (hL3 : 3 ≤ Real.log ρ.im)
    (hℓbig : Real.log 20 + Real.log C + 4 ≤ Real.log (Real.log ρ.im))
    (hP : (2 : ℝ) ^ (k + 2) ≤ Real.log ρ.im / (Real.log (Real.log ρ.im)) ^ 2)
    (hk2 : (k : ℝ) + 2 ≤ 2 * Real.log (Real.log ρ.im))
    (hkm1 : (1 / 2) * Real.log (Real.log ρ.im) ≤ (k : ℝ) - 1)
    (h8 : 8 ≤ Real.log ρ.im / Real.log (Real.log ρ.im)) :
    ρ.re ≤ 1 - (1 / 88214) * (Real.log (Real.log ρ.im) / Real.log ρ.im) := by
  set L : ℝ := Real.log ρ.im with hLdef
  set ℓ : ℝ := Real.log L with hℓdef
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC
  have hγpos : 0 < ρ.im := by linarith [hγ2]
  have hℓ0 : 0 < ℓ := by
    rw [hℓdef]; exact Real.log_pos (by linarith [hL3])
  have hL0 : 0 < L := by linarith [hL3]
  have hP0 : (0 : ℝ) < (2 : ℝ) ^ (k + 2) := by positivity
  have hP1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := one_le_pow₀ (by norm_num)
  have hP2 : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hk4R : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  -- exponent, growth constant
  set e : ℝ := 1 / ((2 : ℝ) ^ (k + 2) * ((k : ℝ) - 1)) with hedef
  have he0 : 0 ≤ e := by rw [hedef]; positivity
  have h3γ0 : (0 : ℝ) < 3 * ρ.im := by linarith [hγ2]
  set Mζ : ℝ := C * (3 * ρ.im) ^ e * (1 + Real.log (3 * ρ.im)) with hMζdef
  have hl3γpos : 0 < 1 + Real.log (3 * ρ.im) := by
    have : 0 ≤ Real.log (3 * ρ.im) := Real.log_nonneg (by linarith [hγ2]); linarith
  have hrpow0 : 0 < (3 * ρ.im) ^ e := Real.rpow_pos_of_pos h3γ0 e
  have hMζpos : 0 < Mζ := by rw [hMζdef]; positivity
  have hb : (1 : ℝ) ≤ (3 * ρ.im) ^ e := Real.one_le_rpow (by linarith [hγ2]) he0
  have hl : (1 : ℝ) ≤ 1 + Real.log (3 * ρ.im) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 3 * ρ.im by linarith [hγ2]); linarith
  have hMζ1 : 1 ≤ Mζ := by
    rw [hMζdef]
    have hCb : (1 : ℝ) ≤ C * (3 * ρ.im) ^ e := by nlinarith [hC, hb, hCpos]
    nlinarith [hCb, hl]
  -- basic log facts
  have hlog2le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
  have hlog3le2 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)]
  have hl3γeq : Real.log (3 * ρ.im) = Real.log 3 + L := by rw [Real.log_mul (by norm_num) hγpos.ne']
  have hl3γ_lb : L ≤ Real.log (3 * ρ.im) := by
    rw [hl3γeq]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]
  have hl3γ_ub : Real.log (3 * ρ.im) ≤ 2 * L := by rw [hl3γeq]; nlinarith [hL3, hlog3le2]
  have hl1_ub : Real.log (1 + Real.log (3 * ρ.im)) ≤ 2 * ℓ := by
    have harg : 1 + Real.log (3 * ρ.im) ≤ L ^ 2 := by nlinarith [hl3γ_ub, hL3]
    calc Real.log (1 + Real.log (3 * ρ.im))
          ≤ Real.log (L ^ 2) := Real.log_le_log (by linarith [hl3γ_lb, hL3]) harg
      _ = 2 * ℓ := by rw [Real.log_pow, ← hℓdef]; norm_num
  -- the four grouped term bounds (units of L/ℓ)
  have hab : (2 : ℝ) ^ (k + 2) * (Real.log 20 + Real.log C) ≤ L / ℓ := by
    have h1 : Real.log 20 + Real.log C ≤ ℓ := by linarith [hℓbig]
    calc (2 : ℝ) ^ (k + 2) * (Real.log 20 + Real.log C)
          ≤ (L / ℓ ^ 2) * ℓ := by
            exact le_trans (mul_le_mul_of_nonneg_left h1 hP0.le)
              (mul_le_mul_of_nonneg_right hP hℓ0.le)
      _ = L / ℓ := by field_simp [hℓ0.ne']
  have hc : (2 : ℝ) ^ (k + 2) * (((k : ℝ) + 2) * Real.log 2) ≤ 2 * (L / ℓ) := by
    have hkl : ((k : ℝ) + 2) * Real.log 2 ≤ 2 * ℓ := by
      nlinarith [hk2, hlog2le1, Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num), hℓ0.le, hk4R]
    calc (2 : ℝ) ^ (k + 2) * (((k : ℝ) + 2) * Real.log 2)
          ≤ (L / ℓ ^ 2) * (2 * ℓ) := by
            refine mul_le_mul hP hkl ?_ (by positivity)
            positivity
      _ = 2 * (L / ℓ) := by field_simp [hℓ0.ne']
  have hd : Real.log (3 * ρ.im) / ((k : ℝ) - 1) ≤ 4 * (L / ℓ) := by
    rw [div_le_iff₀ hk1]
    have h4 : 2 * L ≤ 4 * (L / ℓ) * ((k : ℝ) - 1) := by
      have hstep : 4 * (L / ℓ) * ((1 / 2) * ℓ) ≤ 4 * (L / ℓ) * ((k : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hkm1 (by positivity)
      have heq2 : 4 * (L / ℓ) * ((1 / 2) * ℓ) = 2 * L := by field_simp [hℓ0.ne']; ring
      linarith [hstep, heq2]
    linarith [hl3γ_ub, h4]
  have he : (2 : ℝ) ^ (k + 2) * Real.log (1 + Real.log (3 * ρ.im)) ≤ 2 * (L / ℓ) := by
    calc (2 : ℝ) ^ (k + 2) * Real.log (1 + Real.log (3 * ρ.im))
          ≤ (L / ℓ ^ 2) * (2 * ℓ) := by
            refine mul_le_mul hP hl1_ub ?_ (by positivity)
            exact Real.log_nonneg (by linarith [hl3γ_lb, hL3])
      _ = 2 * (L / ℓ) := by field_simp [hℓ0.ne']
  -- log-split and the P·W bound
  have hkne : (k : ℝ) - 1 ≠ 0 := ne_of_gt hk1
  have hlogMζ : Real.log Mζ
      = Real.log C + e * Real.log (3 * ρ.im) + Real.log (1 + Real.log (3 * ρ.im)) := by
    rw [hMζdef, Real.log_mul (by positivity) (ne_of_gt hl3γpos),
      Real.log_mul (ne_of_gt hCpos) (ne_of_gt hrpow0), Real.log_rpow h3γ0]
  have hW : Real.log (20 * (2 : ℝ) ^ (k + 2) * Mζ)
      = Real.log 20 + ((k : ℝ) + 2) * Real.log 2 + Real.log Mζ := by
    rw [Real.log_mul (by positivity) (ne_of_gt hMζpos), Real.log_mul (by norm_num) (ne_of_gt hP0),
      Real.log_pow]; push_cast; ring
  have hPWeq : (2 : ℝ) ^ (k + 2) * Real.log (20 * (2 : ℝ) ^ (k + 2) * Mζ)
      = (2 : ℝ) ^ (k + 2) * (Real.log 20 + Real.log C)
        + (2 : ℝ) ^ (k + 2) * (((k : ℝ) + 2) * Real.log 2)
        + Real.log (3 * ρ.im) / ((k : ℝ) - 1)
        + (2 : ℝ) ^ (k + 2) * Real.log (1 + Real.log (3 * ρ.im)) := by
    rw [hW, hlogMζ, hedef]; field_simp; ring
  have hPWbound : (2 : ℝ) ^ (k + 2) * Real.log (20 * (2 : ℝ) ^ (k + 2) * Mζ) ≤ 9 * (L / ℓ) := by
    rw [hPWeq]; linarith [hab, hc, hd, he]
  -- region parameters and the three gates
  set Θ : ℝ := 1 / (2 : ℝ) ^ (k + 2) with hΘdef
  have hΘ0 : 0 < Θ := by rw [hΘdef]; positivity
  have hΘ12 : Θ ≤ 1 / 2 := by rw [hΘdef]; exact one_div_le_one_div_of_le (by norm_num) hP2
  set Lq : ℝ := 8 + 700 * (2 : ℝ) ^ (k + 2) * Real.log (20 * (2 : ℝ) ^ (k + 2) * Mζ) with hLqdef
  have hW1 : (1 : ℝ) ≤ Real.log (20 * (2 : ℝ) ^ (k + 2) * Mζ) := by
    have h20 : (20 : ℝ) ≤ 20 * (2 : ℝ) ^ (k + 2) * Mζ := by nlinarith [hP1, hMζ1]
    have he20 : Real.exp 1 ≤ 20 * (2 : ℝ) ^ (k + 2) * Mζ :=
      le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) h20
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he20
  have hLqgeP : (2 : ℝ) ^ (k + 2) ≤ Lq := by
    rw [hLqdef]
    have hkey : 700 * (2 : ℝ) ^ (k + 2) * 1
        ≤ 700 * (2 : ℝ) ^ (k + 2) * Real.log (20 * (2 : ℝ) ^ (k + 2) * Mζ) :=
      mul_le_mul_of_nonneg_left hW1 (by positivity)
    nlinarith [hkey, hP0]
  have hLq0 : 0 < Lq := lt_of_lt_of_le hP0 hLqgeP
  have hgrowth : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
      ‖riemannZeta z‖ ≤ Mζ := by
    intro z h1 h2 h3 h4
    rw [hΘdef] at h1
    rw [hMζdef]
    exact littlewood_uniform_growth hC hfam hk hγ2 hthr z h1 h2 h3 h4
  have hσΘ : (1 : ℝ) / 2 / Lq ≤ Θ / 2 := by
    rw [hΘdef, div_div, div_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [hLqgeP])
  have hwΘ : (1 : ℝ) / 2 / (7 * Lq) ≤ 11 / 14 * Θ := by
    rw [hΘdef, mul_one_div, div_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hLqgeP, hP0, hLq0]
  have hchainC : 8 + 5 * ((120 / (6 * Θ / 7)) * Real.log (4 * (5 * Mζ / Θ)))
      ≤ Lq / (2 * (1 / 2)) := by
    have h1 : (120 : ℝ) / (6 * Θ / 7) = 140 * (2 : ℝ) ^ (k + 2) := by
      rw [hΘdef]; field_simp; ring
    have h2 : (4 : ℝ) * (5 * Mζ / Θ) = 20 * (2 : ℝ) ^ (k + 2) * Mζ := by
      rw [hΘdef]; field_simp; ring
    rw [h1, h2, show (2 : ℝ) * (1 / 2) = 1 by norm_num, div_one, hLqdef]
    exact le_of_eq (by ring)
  -- run the bridge, then the width bound
  have hreg := region_of_uniform_growth hρ0 hβ1 (Θ := Θ) (Mζ := Mζ) (Lq := Lq) (dd := 1 / 2)
    hΘ0 hΘ12 hγ2 hMζ1 (by norm_num) (by norm_num) hLq0 hσΘ hwΘ hchainC hgrowth
  have hLqbnd : Lq ≤ 6301 * (L / ℓ) := by
    rw [hLqdef]
    have hmul : 700 * ((2 : ℝ) ^ (k + 2) * Real.log (20 * (2 : ℝ) ^ (k + 2) * Mζ))
        ≤ 700 * (9 * (L / ℓ)) := mul_le_mul_of_nonneg_left hPWbound (by norm_num)
    nlinarith [hmul, h8]
  have h7Lq : 7 * Lq ≤ 44107 * (L / ℓ) := by nlinarith [hLqbnd]
  have hstep : (1 / 2) / (44107 * (L / ℓ)) ≤ (1 / 2) / (7 * Lq) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) h7Lq
  have heq : (1 : ℝ) / 2 / (44107 * (L / ℓ)) = 1 / 88214 * (ℓ / L) := by
    field_simp [hL0.ne', hℓ0.ne']; ring
  rw [heq] at hstep
  linarith [hreg, hstep]

/-! ## The degree construction — `k = ⌊log log γ⌋` discharges the bracket -/

set_option maxHeartbeats 1000000 in
-- The bracket bundles the transcendental upper bound, the factorial threshold and the height
-- thresholds into one declaration; the log/exp/sqrt reasoning needs headroom.
/-- **Balanced-degree construction.**  For a height `γ` above the (astronomical, `C`-dependent)
threshold `exp(exp(log C + 400))`, the degree `k = ⌊log log γ⌋` satisfies every hypothesis of
`zeta_zero_free_littlewood_core`: `k ≥ 4`, the factorial threshold `4(k!)^6 ≤ γ − 1`, the balance
bracket `2^{k+2} ≤ L/ℓ²`, `k+2 ≤ 2ℓ`, `(1/2)ℓ ≤ k−1`, and the height thresholds
(`L = log γ`, `ℓ = log L`).  The single transcendental step is `2^{k+2} ≤ L/ℓ²`, proved via
`log 2 < 0.7` and `log ℓ ≤ 2√ℓ`; the factorial via `k! ≤ k^k` and `ℓ³/27 ≤ exp ℓ = L`. -/
theorem littlewood_bracket {C : ℝ} (hC : 1 ≤ C) {γ : ℝ}
    (hγ : Real.exp (Real.exp (Real.log C + 400)) ≤ γ) :
    ∃ k : ℕ, 4 ≤ k ∧ 2 ≤ γ ∧ 4 * (k.factorial : ℝ) ^ 6 ≤ γ - 1 ∧ 3 ≤ Real.log γ
      ∧ Real.log 20 + Real.log C + 4 ≤ Real.log (Real.log γ)
      ∧ (2 : ℝ) ^ (k + 2) ≤ Real.log γ / (Real.log (Real.log γ)) ^ 2
      ∧ (k : ℝ) + 2 ≤ 2 * Real.log (Real.log γ)
      ∧ (1 / 2) * Real.log (Real.log γ) ≤ (k : ℝ) - 1
      ∧ 8 ≤ Real.log γ / Real.log (Real.log γ) := by
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC
  have hlogC0 : 0 ≤ Real.log C := Real.log_nonneg hC
  set A : ℝ := Real.log C + 400 with hAdef
  have hApos : 0 < A := by rw [hAdef]; linarith
  have hγpos : 0 < γ := lt_of_lt_of_le (Real.exp_pos _) hγ
  set L : ℝ := Real.log γ with hLdef
  have hLA : Real.exp A ≤ L := by
    rw [hLdef, ← Real.log_exp (Real.exp A)]; exact Real.log_le_log (Real.exp_pos _) hγ
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hLA
  set ℓ : ℝ := Real.log L with hℓdef
  have hℓA : A ≤ ℓ := by
    rw [hℓdef, ← Real.log_exp A]; exact Real.log_le_log (Real.exp_pos _) hLA
  have hℓ400 : 400 ≤ ℓ := by rw [hAdef] at hℓA; linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hLexpℓ : Real.exp ℓ = L := Real.exp_log hL0
  have hLcube : ℓ ^ 3 / 27 ≤ L := by rw [← hLexpℓ]; exact cube_le_exp (by linarith)
  have hℓ2 : (160000 : ℝ) ≤ ℓ ^ 2 := by nlinarith [hℓ400]
  have hℓ3ℓ : 216 * ℓ ≤ ℓ ^ 3 := by nlinarith [hℓ2, hℓ0.le]
  have hℓ3ℓ2 : 378 * ℓ ^ 2 ≤ ℓ ^ 3 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ ℓ - 378 by linarith [hℓ400]) (sq_nonneg ℓ)]
  have hLbig : (2000000 : ℝ) ≤ L := by nlinarith [hLcube, hℓ3ℓ2, hℓ2]
  -- the degree
  set k : ℕ := ⌊ℓ⌋₊ with hkdef
  have hk_le : (k : ℝ) ≤ ℓ := Nat.floor_le hℓ0.le
  have hk_ge : ℓ - 1 ≤ (k : ℝ) := by
    have := Nat.lt_floor_add_one ℓ; rw [← hkdef] at this; linarith
  have hk4 : 4 ≤ k := Nat.le_floor (by push_cast; linarith [hℓ400])
  have hk4R : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
  have hkR1 : (1 : ℝ) ≤ (k : ℝ) := by linarith
  -- 2 ≤ γ
  have hγ2 : 2 ≤ γ := by
    have h1 : (1 : ℝ) ≤ Real.exp A := Real.one_le_exp hApos.le
    have h2 : (2 : ℝ) ≤ Real.exp (Real.exp A) :=
      le_trans (by linarith [Real.exp_one_gt_d9]) (Real.exp_le_exp.mpr h1)
    linarith [le_trans h2 hγ]
  -- height thresholds
  have hL3 : 3 ≤ L := by linarith [hLbig]
  have hℓbig : Real.log 20 + Real.log C + 4 ≤ ℓ := by
    have hlog20 : Real.log 20 ≤ 19 := by
      linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 20 by norm_num)]
    rw [hAdef] at hℓA; linarith
  have h8 : 8 ≤ L / ℓ := by
    rw [le_div_iff₀ hℓ0]; linarith [hLcube, hℓ3ℓ]
  -- (A') and (C): easy floor bounds
  have hk2 : (k : ℝ) + 2 ≤ 2 * ℓ := by linarith [hk_le, hℓ400]
  have hkm1 : (1 / 2) * ℓ ≤ (k : ℝ) - 1 := by linarith [hk_ge, hℓ400]
  -- (A): the transcendental upper bracket
  have hA6 : (2 : ℝ) ^ (k + 2) ≤ L / ℓ ^ 2 := by
    have hstep1 : (2 : ℝ) ^ (k + 2) ≤ (2 : ℝ) ^ (ℓ + 2) := by
      rw [← Real.rpow_natCast (2 : ℝ) (k + 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast; linarith [hk_le]
    have hlog2 : Real.log 2 ≤ 7 / 10 := le_of_lt (by linarith [Real.log_two_lt_d9])
    have hlogℓ : Real.log ℓ ≤ 2 * Real.sqrt ℓ := log_le_two_sqrt hℓ0
    have hsq : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ0.le
    have hsqge : 15 ≤ Real.sqrt ℓ := by
      have h := Real.sqrt_le_sqrt (show (225 : ℝ) ≤ ℓ by linarith [hℓ400])
      rwa [show (225 : ℝ) = 15 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 15)] at h
    have htrans : (ℓ + 2) * Real.log 2 ≤ ℓ - 2 * Real.log ℓ := by
      have hp : (ℓ + 2) * Real.log 2 ≤ (ℓ + 2) * (7 / 10) :=
        mul_le_mul_of_nonneg_left hlog2 (by linarith)
      nlinarith [hp, hlogℓ, hsq, hsqge, Real.sqrt_nonneg ℓ]
    have hlogstep : Real.log ((2 : ℝ) ^ (ℓ + 2)) ≤ Real.log (L / ℓ ^ 2) := by
      rw [Real.log_rpow (by norm_num), Real.log_div hL0.ne' (by positivity), Real.log_pow,
        ← hℓdef]
      push_cast; linarith [htrans]
    have hstep2 : (2 : ℝ) ^ (ℓ + 2) ≤ L / ℓ ^ 2 := by
      calc (2 : ℝ) ^ (ℓ + 2) = Real.exp (Real.log ((2 : ℝ) ^ (ℓ + 2))) :=
            (Real.exp_log (Real.rpow_pos_of_pos (by norm_num) _)).symm
        _ ≤ Real.exp (Real.log (L / ℓ ^ 2)) := Real.exp_le_exp.mpr hlogstep
        _ = L / ℓ ^ 2 := Real.exp_log (by positivity)
    linarith [hstep1, hstep2]
  -- the factorial threshold
  have hLℓ2 : 14 * ℓ ^ 2 ≤ L := by linarith [hLcube, hℓ3ℓ2]
  have hγ1pos : 0 < γ - 1 := by linarith [hγ2]
  have hlogγ1 : L / 2 ≤ Real.log (γ - 1) := by
    have h1 : Real.log (γ / 2) ≤ Real.log (γ - 1) :=
      Real.log_le_log (by linarith [hγ2]) (by linarith)
    have h2 : Real.log (γ / 2) = L - Real.log 2 := by
      rw [Real.log_div hγpos.ne' (by norm_num), ← hLdef]
    have hlog2le1 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
    rw [h2] at h1; linarith [h1, hlog2le1, hLbig]
  have hfk : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  have hkfacpos : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hlogkfac : Real.log (k.factorial : ℝ) ≤ (k : ℝ) * Real.log (k : ℝ) := by
    have := Real.log_le_log hkfacpos hfk; rwa [Real.log_pow] at this
  have hlogk0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hkR1
  have h6klogk : 6 * ((k : ℝ) * Real.log (k : ℝ)) ≤ 6 * ℓ ^ 2 := by
    have hklk : (k : ℝ) * Real.log (k : ℝ) ≤ ℓ * ℓ := by
      refine mul_le_mul hk_le ?_ hlogk0 (by linarith [hℓ0])
      exact le_trans (Real.log_le_log (by linarith [hkR1]) hk_le)
        (by linarith [Real.log_le_sub_one_of_pos hℓ0])
    nlinarith [hklk]
  have hlog4 : Real.log 4 ≤ ℓ ^ 2 := by
    have : Real.log 4 ≤ 3 := by
      linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)]
    nlinarith [this, hℓ400]
  have hlogexpr : Real.log (4 * (k.factorial : ℝ) ^ 6) ≤ 7 * ℓ ^ 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; linarith [hlogkfac, h6klogk, hlog4]
  have hfact : 4 * (k.factorial : ℝ) ^ 6 ≤ γ - 1 := by
    have hposL : (0 : ℝ) < 4 * (k.factorial : ℝ) ^ 6 := by positivity
    have hle : Real.log (4 * (k.factorial : ℝ) ^ 6) ≤ Real.log (γ - 1) := by
      calc Real.log (4 * (k.factorial : ℝ) ^ 6) ≤ 7 * ℓ ^ 2 := hlogexpr
        _ ≤ L / 2 := by linarith [hLℓ2]
        _ ≤ Real.log (γ - 1) := hlogγ1
    calc 4 * (k.factorial : ℝ) ^ 6
          = Real.exp (Real.log (4 * (k.factorial : ℝ) ^ 6)) := (Real.exp_log hposL).symm
      _ ≤ Real.exp (Real.log (γ - 1)) := Real.exp_le_exp.mpr hle
      _ = γ - 1 := Real.exp_log hγ1pos
  exact ⟨k, hk4, hγ2, hfact, hL3, hℓbig, hA6, hk2, hkm1, h8⟩

/-! ## THE LITTLEWOOD ZERO-FREE REGION -/

/-- **The Littlewood zero-free region** (`σ ≥ 1 − c·log log t / log t`).  There is an explicit
`c > 0` and a threshold `T₀` such that every ζ-zero `ρ` of height `|Im ρ| ≥ T₀` satisfies
`Re ρ ≤ 1 − c·log log|Im ρ| / log|Im ρ|` — strictly wider than de la Vallée Poussin's `1/log t`.

The historic checkpoint: the first machine-checked Littlewood-strength zero-free region, obtained
from the sub-Weyl growth `Salt.ExpSum.zeta_strip_family` at the balanced degree `k ≈ log log t`
(`littlewood_bracket`) fed through the 3-4-1 disc assembly (`zeta_zero_free_littlewood_core`).
Negative-height zeros are handled by the conjugation shim `riemannZeta_conj_zero`.  Both `c`
(`= 1/88214`) and `T₀` (`= exp(exp(log C + 400))`, `C` the sub-Weyl constant) are design-grade and
astronomically lazy; only the width SHAPE `log log t / log t` is the content. -/
theorem zeta_zero_free_region_littlewood :
    ∃ c T₀ : ℝ, 0 < c ∧ 3 ≤ T₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 → T₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - c * (Real.log (Real.log |ρ.im|) / Real.log |ρ.im|) := by
  obtain ⟨C, hC, hfam⟩ := Salt.ExpSum.zeta_strip_family
  refine ⟨1 / 88214, Real.exp (Real.exp (Real.log C + 400)), by norm_num, ?_, ?_⟩
  · -- 3 ≤ T₀
    have h1 : (401 : ℝ) ≤ Real.exp (Real.log C + 400) := by
      linarith [Real.add_one_le_exp (Real.log C + 400), Real.log_nonneg hC]
    have h2 : Real.exp 2 ≤ Real.exp (Real.exp (Real.log C + 400)) :=
      Real.exp_le_exp.mpr (by linarith [h1])
    linarith [h2, Real.add_one_le_exp (2 : ℝ)]
  · -- the positive-height core, then conjugation for negative heights
    have hpos : ∀ σ : ℂ, riemannZeta σ = 0 →
        Real.exp (Real.exp (Real.log C + 400)) ≤ σ.im →
        σ.re ≤ 1 - 1 / 88214 * (Real.log (Real.log σ.im) / Real.log σ.im) := by
      intro σ hσ0 hσim
      obtain ⟨k, hk4, hγ2, hthr, hL3, hℓbig, hP, hk2, hkm1, h8⟩ := littlewood_bracket hC hσim
      have hβ1 : σ.re < 1 := by
        by_contra h; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hσ0
      exact zeta_zero_free_littlewood_core hC hfam hσ0 hβ1 hk4 hγ2 hthr hL3 hℓbig hP hk2 hkm1 h8
    intro ρ hρ0 hγ
    by_cases hsign : 0 ≤ ρ.im
    · rw [abs_of_nonneg hsign] at hγ ⊢; exact hpos ρ hρ0 hγ
    · rw [abs_of_neg (not_le.mp hsign)] at hγ ⊢
      have hρ1 : ρ ≠ 1 := by
        intro h; rw [h] at hsign; simp at hsign
      have hconj0 : riemannZeta ((starRingEnd ℂ) ρ) = 0 := riemannZeta_conj_zero hρ1 hρ0
      have h := hpos ((starRingEnd ℂ) ρ) hconj0 (by rw [Complex.conj_im]; exact hγ)
      rwa [Complex.conj_im, Complex.conj_re] at h

end Salt.Vk
