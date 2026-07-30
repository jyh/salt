/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.VkTwistRegion

/-!
# STONE B, THE `χ² = 1` ARM — the VK-width region for REAL characters' complex zeros

`Salt/MR/VkTwistRegion.lean` lands the χ-VK region for `χ² ≠ 1`, where all three legs of the
3-4-1 device are entire.  For a REAL non-principal `χ` (`χ² = 1`, `χ ≠ 1`) the third leg
degenerates to the PRINCIPAL character mod `q`,

  `L(s, χ²) = L(s, χ₀) = ζ(s)·∏_{p∣q}(1 − p^{−s})`,

which has ζ's pole at `s = 1`, so `VkTwistRegionProbe.LFunction_drop_all_disc` (which needs
`differentiable_LFunction`) does not apply.  This file supplies the replacement leg and lands the
region for real characters' zeros at VK width.

## The three moves (the probe's gap-2, discharged)

1. **The drop-all leg is ζ's own, at the doubled height.**  `Salt.Vk.zeta_drop_all_disc` (the
   landed `Zc`-normalized drop-all) gives
   `Re(−ζ′/ζ(σ+2iγ)) ≤ Re(1/(s₂−1)) + (120/λ)·log(4M₀)`; its sphere hypotheses come from
   `Salt.Vk.Zc_ratio_sphere_bound` (gate `1 ≤ |2γ|`, free at `γ ≥ 2`) fed by ζ's OWN VK strip
   growth, which this file re-derives with EXPLICIT constants (`zeta_strip_growth_explicit`,
   `‖ζ‖ ≤ 8104·log t`) so that no existential leaks into the statements.
2. **The finite-Euler debit is one numeral: `log q`.**  `neg_re_logDeriv_trivChar_le_zeta`:
   `Re(−L′/L(s,χ₀)) ≤ Re(−ζ′/ζ(s)) + log q` for `Re s > 1`, by the multiplicative split
   `L(·,χ₀) = P·ζ` (`LFunctionTrivChar_eq_mul_riemannZeta`) and `‖logDeriv P‖ ≤ ∑_{p∣q} log p ≤
   log q` — the same per-factor route as `Salt.SW.neg_re_logDeriv_trivChar_complex_le`, but WITHOUT
   that lemma's classical `1080·log(|γ|+2)` ζ-term (which is `≫ (log γ)^{3/4}(loglog γ)³` and would
   destroy the VK width — the one place the classical arm cannot be reused).
3. **The pole correction is `≤ 1/4`.**  At the doubled height `Re(1/(s₂−1)) = (σ−1)/((σ−1)²+4γ²)
   ≤ 1/16`: the conjugate-zero apparatus of `Salt.SW.zero_free_region_real` is UNNECESSARY at VK
   width (the probe's finding — `σ−1` is tiny against `|γ| ≥ 2`).

So the Davenport chain reads `4/(σ−β) ≤ 3/(σ−1) + (8 + log q + 5·Cnum)`: exactly the probe's
`χ² ≠ 1` chain with `8 ⟹ 8 + log q`, i.e. the predicted `Lq = 8 + log q + 700·Pinv·W` shape.  The
`log q` is absorbed by the SAME `q`-scale gate that the growth constant needs
(`log q ≤ log(20000·Cq) ≤ A·loglog|Im ρ|`), so the region's constant is unchanged: `1/(10⁸(A+7))`.

## What is NOT built here (P-7's, per the brief)

The `∃ H₀` Siegel fold: real characters may have an EXCEPTIONAL real zero, and this file says
nothing about zeros with `Im ρ = 0` — they are excluded by the height floor `|Im ρ| ≥
exp(exp 100)+1`, exactly as `Salt.SW.zero_free_region_all` excludes them via its
`(χ² ≠ 1 ∨ Im ρ ≠ 0)` carve-out.  The consumer's dispatch is: complex zeros of real `χ` ⟹ this
file; the exceptional real zero ⟹ `Salt.SW.siegel_zero_free_exceptional` (the KMT `1_{χ∈{χ₀,ξ₁}}`
row); low heights ⟹ the classical `Salt.SW.zero_free_region_all'`.
-/

noncomputable section

namespace Salt.MR

open Complex DirichletCharacter Metric Set Salt.SW Salt.Vk
open scoped LSeries.notation Topology

/-! ## §1 — ζ's VK strip growth with EXPLICIT constants -/

/-- **ζ's VK strip growth, explicit.**  `‖ζ(σ+it)‖ ≤ 8104·log t` on the strip
`1 − vkTheta t ≤ σ ≤ 3` past `t ≥ exp(exp 100)`.  This is `Salt.Vk.zeta_growth_pow`'s body with
its witnesses (`K = 8104`, `t₀ = exp(exp 100)`) made explicit, so the real arm's constants stay
numerals: front end `Salt.Vk.zeta_sub_dirichlet_bound` (`≤ 4`) plus the dyadic ladder
`Salt.Vk.vk_dirichlet_sum_le` (`≤ 4050(1+log t)`). -/
theorem zeta_strip_growth_explicit {σ t : ℝ} (ht : Real.exp (Real.exp 100) ≤ t)
    (hσlo : 1 - vkTheta t ≤ σ) (hσ3 : σ ≤ 3) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 8104 * Real.log t := by
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht
  have hL100 : Real.exp 100 ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos _) ht
    rwa [Real.log_exp] at h
  have hexp101 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hlogt1 : (1 : ℝ) ≤ Real.log t := by linarith
  have hℓ1 : (1 : ℝ) ≤ Real.log (Real.log t) := by
    have h100 : (100 : ℝ) ≤ Real.log (Real.log t) := by
      rw [← Real.log_exp 100]; exact Real.log_le_log (Real.exp_pos _) hL100
    linarith
  have ht100 : (100 : ℝ) ≤ t := by
    have h1 : (100 : ℝ) ≤ Real.exp (Real.exp 100) := by
      have := Real.add_one_le_exp (Real.exp 100); linarith [hexp101]
    linarith
  have hΘsmall : vkTheta t ≤ 1 / 1000 := vkTheta_le_thousandth hlogt1 hℓ1
  have hσ34 : (3 : ℝ) / 4 ≤ σ := by linarith
  have hfront := zeta_sub_dirichlet_bound hσ34 hσ3 ht100
  have hdir := vk_dirichlet_sum_le ht0 hL100 hσlo hσ3
  have h := norm_le_norm_add_norm_sub' (riemannZeta ((σ : ℂ) + (t : ℂ) * I))
    (∑ n ∈ Finset.Icc 1 ⌈t ^ 2⌉₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)))
  have hcomb : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 4050 * (1 + Real.log t) + 4 := by
    linarith [h, hfront, hdir]
  linarith [hcomb, hlogt1]

/-- **ζ's VK BOX growth, explicit** — the `hgrowth` shape at the doubled-height box, twin of
`Salt.MR.vk_char_box_growth` and of `Salt.Vk.pow_uniform_growth` with the constant made a
numeral. -/
theorem zeta_box_growth_explicit {γ : ℝ} (hγfloor : Real.exp (Real.exp 100) ≤ γ - 1) :
    ∀ z : ℂ, 1 - vkTheta (3 * γ) ≤ z.re → z.re ≤ 2 → γ - 1 ≤ z.im → z.im ≤ 3 * γ →
      ‖riemannZeta z‖ ≤ 8104 * Real.log (3 * γ) := by
  intro z hre1 hre2 him1 him2
  have hexp1 : Real.exp 1 < Real.exp (Real.exp 100) := by
    apply Real.exp_lt_exp.mpr
    linarith [Real.add_one_le_exp (100 : ℝ)]
  have hzim : Real.exp (Real.exp 100) ≤ z.im := le_trans hγfloor him1
  have hzimpos : 0 < z.im := lt_of_lt_of_le (Real.exp_pos _) hzim
  have hzime : Real.exp 1 < z.im := lt_of_lt_of_le hexp1 hzim
  have hθz : vkTheta (3 * γ) ≤ vkTheta z.im := vkTheta_anti hzime him2
  have hstrip : 1 - vkTheta z.im ≤ z.re := by linarith [hre1, hθz]
  have hgrow := zeta_strip_growth_explicit (σ := z.re) (t := z.im) hzim hstrip (by linarith)
  rw [Complex.re_add_im z] at hgrow
  have hlogle : Real.log z.im ≤ Real.log (3 * γ) := Real.log_le_log hzimpos him2
  calc ‖riemannZeta z‖ ≤ 8104 * Real.log z.im := hgrow
    _ ≤ 8104 * Real.log (3 * γ) := by linarith

/-! ## §2 — the finite-Euler debit: the principal character against ζ -/

/-- **The finite-Euler debit, `log q`.**  For `Re s > 1`,
`Re(−L′/L(s,χ₀)) ≤ Re(−ζ′/ζ(s)) + log q`, where `χ₀ = (1 : DirichletCharacter ℂ q)`.

The multiplicative split `L(·,χ₀) = P·ζ` with `P z = ∏_{p∣q}(1 − p^{−z})`
(`LFunctionTrivChar_eq_mul_riemannZeta`), then `logDeriv_mul` and the per-factor bound
`‖logDeriv(1 − p^{−s})‖ ≤ log p` (`Salt.SW.norm_logDeriv_eulerFactor_le` at the mod-1
`eulerFactor`), summing to `∑_{p∣q} log p = log(rad q) ≤ log q`.

This is the `Re s > 1` core of `Salt.SW.neg_re_logDeriv_trivChar_complex_le` with the ζ-leg left
OPEN — which is the whole point: the classical ζ-leg (`zeta_neg_re_logDeriv_le`, `1080·log(|γ|+2)`)
is `≫ (log γ)^{3/4}(loglog γ)³` and would destroy the VK width, so the real arm feeds the ζ-leg
from `Salt.Vk.zeta_drop_all_disc` instead. -/
lemma neg_re_logDeriv_trivChar_le_zeta (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s).re
      ≤ (-logDeriv riemannZeta s).re + Real.log (q : ℝ) := by
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; norm_num at hs
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hspos : (0 : ℝ) < s.re := by linarith
  have hfac_ne : ∀ p ∈ q.primeFactors, (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
    intro p hp
    have h := eulerFactor_ne_zero (1 : DirichletCharacter ℂ 1)
      (Nat.prime_of_mem_primeFactors hp) hspos
    rwa [eulerFactor_one_eq p] at h
  have hfac_diff : ∀ p ∈ q.primeFactors,
      DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s := by
    intro p hp
    have h := differentiableAt_eulerFactor (1 : DirichletCharacter ℂ 1)
      (Nat.prime_of_mem_primeFactors hp) s
    rwa [eulerFactor_one_eq p] at h
  set P : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z)) with hPdef
  have hP0 : P s ≠ 0 := Finset.prod_ne_zero_iff.mpr hfac_ne
  have hPdiff : DifferentiableAt ℂ P s := DifferentiableAt.fun_finsetProd hfac_diff
  have hζdiff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hLmul : logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s
      = logDeriv P s + logDeriv riemannZeta s := by
    have hEq : LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s]
        fun z => P z * riemannZeta z := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
      rw [hPdef]
      exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (by simpa using hz)
    have hcong : logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s
        = logDeriv (fun z => P z * riemannZeta z) s := by
      simp only [logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds]
    rw [hcong, logDeriv_mul s hP0 hζ0 hPdiff hζdiff]
  have hPsum : logDeriv P s
      = ∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s := by
    rw [hPdef]
    exact logDeriv_prod hfac_ne hfac_diff
  have hPbound : ‖logDeriv P s‖ ≤ Real.log (q : ℝ) := by
    rw [hPsum]
    calc ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖
        ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ :=
          norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, Real.log p := by
          apply Finset.sum_le_sum
          intro p hp
          have h := norm_logDeriv_eulerFactor_le (1 : DirichletCharacter ℂ 1)
            (Nat.prime_of_mem_primeFactors hp) (le_of_lt hs)
          rwa [eulerFactor_one_eq p] at h
      _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos.ne'
      _ ≤ Real.log (q : ℝ) := by
          apply Real.log_le_log
          · apply Finset.prod_pos
            exact fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
          · rw [← Nat.cast_prod]
            exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
              (Nat.prod_primeFactors_dvd q)
  have hPre : (-logDeriv P s).re ≤ Real.log (q : ℝ) := by
    have h := (Complex.abs_re_le_norm (logDeriv P s)).trans hPbound
    rw [Complex.neg_re]
    linarith [(abs_le.mp h).1]
  have hsplit : (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s).re
      = (-logDeriv riemannZeta s).re + (-logDeriv P s).re := by
    rw [hLmul, neg_add, Complex.add_re, Complex.neg_re, Complex.neg_re]
    ring
  rw [hsplit]
  linarith [hPre]

/-! ## §3 — the 3-4-1 assembly for a real character at the near-1-line disc -/

set_option maxHeartbeats 1600000 in
-- The Davenport chain with the two extra numerals (`log q`, the pole `1/4`) plus the geometry.
/-- **The VK-width 3-4-1 assembly for `L(·,χ)`, `χ² = 1`.**  The real-character twin of
`VkTwistRegionProbe.LFunction_zero_free_of_disc`: same gates `(hσΘ, hwΘ)`, and `hchainC` with
`8 ⟹ 8 + log q`.  The three legs: `ζ(σ)³`'s pole at real `σ`
(`neg_logDeriv_LFunction_trivChar_le`), `L(σ+iγ,χ)⁴`'s keep-one
(`VkTwistRegionProbe.LFunction_keep_one_disc`), and the principal character's drop-all at the
doubled height — ζ's own `Salt.Vk.zeta_drop_all_disc` plus the `log q` Euler debit
(`neg_re_logDeriv_trivChar_le_zeta`) plus the pole correction `Re(1/(s₂−1)) ≤ 1/16`. -/
theorem LFunction_real_zero_free_of_disc {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (hχsq : χ ^ 2 = 1)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hβ1 : ρ.re < 1) (hγ2 : 2 ≤ ρ.im)
    {Θ M₀ Lq dd : ℝ} (hΘ0 : 0 < Θ) (hΘ2 : Θ ≤ 2) (hM₀ : 1 ≤ M₀)
    (hdd : 0 < dd) (hddlt : dd < 1) (hLq0 : 0 < Lq) (hσΘ : dd / Lq ≤ Θ / 2)
    (hwΘ : dd / (7 * Lq) ≤ 11 / 14 * Θ)
    (hchainC : 8 + Real.log (q : ℝ) + 5 * ((120 / (6 * Θ / 7)) * Real.log (4 * M₀))
      ≤ Lq / (2 * dd))
    (hkeep74 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I) (7 / 4 * (6 * Θ / 7)),
        ‖LFunction χ z / LFunction χ (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I)‖ ≤ M₀)
    (hkeep32 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I) (3 / 2 * (6 * Θ / 7)),
        ‖LFunction χ z / LFunction χ (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I)‖ ≤ M₀)
    (hdrop74 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)
        (7 / 4 * (6 * Θ / 7)),
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)‖ ≤ M₀)
    (hdrop32 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)
        (3 / 2 * (6 * Θ / 7)),
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)‖ ≤ M₀) :
    ρ.re ≤ 1 - dd / (7 * Lq) := by
  have h6Θ : (0 : ℝ) < 6 * Θ / 7 := by linarith [hΘ0]
  set Cnum : ℝ := (120 / (6 * Θ / 7)) * Real.log (4 * M₀) with hCnum
  have hCnum0 : 0 ≤ Cnum := by
    rw [hCnum]
    exact mul_nonneg (le_of_lt (div_pos (by norm_num) h6Θ)) (Real.log_nonneg (by nlinarith [hM₀]))
  have hlogq0 : 0 ≤ Real.log (q : ℝ) := by
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    exact Real.log_nonneg hq1
  have hddL : 0 < dd / Lq := div_pos hdd hLq0
  set σ : ℝ := 1 + dd / Lq with hσdef
  have hσ1 : 1 < σ := by rw [hσdef]; linarith [hddL]
  have hσ2le : σ ≤ 2 := by rw [hσdef]; linarith [hσΘ, hΘ2]
  have hσc : |σ - 1 - Θ / 2| ≤ 69 / 70 * Θ := by
    rw [hσdef, abs_of_nonpos (by nlinarith [hσΘ, hddL] : (1 + dd / Lq) - 1 - Θ / 2 ≤ 0)]
    nlinarith [hσΘ, hΘ0, hddL]
  rcases le_or_gt ρ.re (1 - 11 / 14 * Θ) with hout | hin
  · linarith [hwΘ, hout]
  · -- the three legs
    have hA1 := LFunction_keep_one_disc hχ1 hρ0 hβ1 hΘ0 hM₀ hσ1 hσc hin hkeep74 hkeep32
    have hA2ζ := zeta_drop_all_disc (Θ := Θ) (σ := σ) (M₀ := M₀) (τ := 2 * ρ.im)
      hΘ0 hM₀ hσ1 hσc hdrop74 hdrop32
    have hA0 : (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((σ : ℝ) : ℂ)).re
        ≤ 1 / (σ - 1) + 1 := neg_logDeriv_LFunction_trivChar_le q hσ1 hσ2le
    have h341 := three_four_one_logDeriv χ hσ1 ρ.im
    set s1 : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hs1def
    set s2 : ℂ := (σ : ℂ) + 2 * (ρ.im : ℂ) * I with hs2def
    have hσ0C : (1 : ℝ) < ((σ : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact hσ1
    have hσ1C : (1 : ℝ) < s1.re := by rw [hs1def]; simpa using hσ1
    have hσ2C : (1 : ℝ) < s2.re := by rw [hs2def]; simpa using hσ1
    rw [neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ q) hσ0C,
        neg_logDeriv_LSeries_eq χ hσ1C,
        neg_logDeriv_LSeries_eq (χ ^ 2) hσ2C, hχsq] at h341
    -- the principal-character drop-all leg at `s2`
    have hs2align : (σ : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I = s2 := by rw [hs2def]; push_cast; ring
    rw [hs2align] at hA2ζ
    have hdebit := neg_re_logDeriv_trivChar_le_zeta q hσ2C
    -- the pole correction at the doubled height
    have hpole : (1 / (s2 - 1)).re ≤ 1 / 16 := by
      have hzeq : s2 - 1 = (((σ - 1 : ℝ)) : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I := by
        rw [hs2def]; push_cast; ring
      have hre : (s2 - 1).re = σ - 1 := by rw [hzeq]; simp
      have him : (s2 - 1).im = 2 * ρ.im := by rw [hzeq]; simp
      have hns : Complex.normSq (s2 - 1) = (σ - 1) ^ 2 + (2 * ρ.im) ^ 2 := by
        rw [Complex.normSq_apply, hre, him]; ring
      have hden : (16 : ℝ) ≤ (σ - 1) ^ 2 + (2 * ρ.im) ^ 2 := by nlinarith [hγ2, hσ1]
      have hnum : σ - 1 ≤ 1 := by linarith [hσ2le]
      rw [one_div, Complex.inv_re, hre, hns]
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith [hnum, hden, hσ1]
    -- the Davenport chain
    have key : 4 * (1 / (σ - ρ.re)) ≤ 3 * (1 / (σ - 1))
        + (8 + Real.log (q : ℝ) + 5 * Cnum) := by
      rw [← hCnum] at hA1 hA2ζ
      linarith [h341, hA0, hA1, hA2ζ, hdebit, hpole, hCnum0]
    have hchain' : 4 / (dd / Lq + (1 - ρ.re)) ≤ 3 / (dd / Lq) + (1 / (2 * dd)) * Lq := by
      rw [mul_one_div, mul_one_div] at key
      have e1 : σ - ρ.re = dd / Lq + (1 - ρ.re) := by rw [hσdef]; ring
      have e2 : σ - 1 = dd / Lq := by rw [hσdef]; ring
      rw [e1, e2] at key
      have hCLq : (8 : ℝ) + Real.log (q : ℝ) + 5 * Cnum ≤ (1 / (2 * dd)) * Lq := by
        rw [div_mul_eq_mul_div, one_mul]; linarith [hchainC]
      linarith [key, hCLq]
    have hCdd : (1 / (2 * dd)) * dd = 1 / 2 := by field_simp
    have hext := zero_free_extraction hLq0 hdd hCdd hβ1 hchain'
    linarith [hext]

/-! ## §4 — the box-growth discharge for the real arm -/

set_option maxHeartbeats 1600000 in
-- The four sphere discharges (two `L`-ratios, two `Zc`-ratios) plus the radius bookkeeping.
/-- **The growth-to-region bridge, `χ² = 1`.**  Uniform growth `M` on the box
`Re z ∈ [1−Θ, 2]`, `Im z ∈ [Im ρ − 1, 3 Im ρ]` for BOTH `L(·,χ)` and `ζ` yields
`Re ρ ≤ 1 − dd/(7 Lq)` under the same three gates as the `χ² ≠ 1` arm, with `log q` added to
`hchainC`.  The `χ` spheres go through `VkTwistRegionProbe.LFunction_ratio_bound`, the `Zc`
spheres through `Salt.Vk.Zc_ratio_sphere_bound` (whose `1 ≤ |τ|` gate is free at `τ = 2 Im ρ`,
`Im ρ ≥ 2`). -/
theorem LFunction_real_region_of_growth {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (hχsq : χ ^ 2 = 1)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hβ1 : ρ.re < 1)
    {Θ M Lq dd : ℝ} (hΘ0 : 0 < Θ) (hΘ12 : Θ ≤ 1 / 2) (hγ2 : 2 ≤ ρ.im)
    (hM : 1 ≤ M) (hdd : 0 < dd) (hddlt : dd < 1) (hLq0 : 0 < Lq)
    (hσΘ : dd / Lq ≤ Θ / 2) (hwΘ : dd / (7 * Lq) ≤ 11 / 14 * Θ)
    (hchainC : 8 + Real.log (q : ℝ)
      + 5 * ((120 / (6 * Θ / 7)) * Real.log (4 * (5 * M / Θ))) ≤ Lq / (2 * dd))
    (hgrowthχ : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
        ‖LFunction χ z‖ ≤ M)
    (hgrowthζ : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
        ‖riemannZeta z‖ ≤ M) :
    ρ.re ≤ 1 - dd / (7 * Lq) := by
  have hM₀ : (1 : ℝ) ≤ 5 * M / Θ := by
    rw [le_div_iff₀ hΘ0]; nlinarith [hM, hΘ12, hΘ0]
  -- the sphere geometry (shared)
  have box : ∀ (τ R : ℝ), 0 ≤ R → R ≤ 3 / 2 * Θ → ρ.im - 1 + R ≤ τ → τ + R ≤ 3 * ρ.im →
      ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I) R,
        (1 - Θ ≤ z.re ∧ z.re ≤ 2) ∧ (ρ.im - 1 ≤ z.im ∧ z.im ≤ 3 * ρ.im) := by
    intro τ R hR0 hR hτlo hτhi z hz
    have hzc : ‖z - (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ = R := by
      rw [← dist_eq_norm, ← mem_sphere]; exact hz
    have hcre : (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I).re = 1 + Θ / 2 := by simp
    have hcim : (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I).im = τ := by simp
    have hreb : |z.re - (1 + Θ / 2)| ≤ R := by
      have h := Complex.abs_re_le_norm (z - (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I))
      rw [Complex.sub_re, hcre, hzc] at h; exact h
    have himb : |z.im - τ| ≤ R := by
      have h := Complex.abs_im_le_norm (z - (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I))
      rw [Complex.sub_im, hcim, hzc] at h; exact h
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have := (abs_le.mp hreb).1; nlinarith [hR, hΘ12]
    · have := (abs_le.mp hreb).2; nlinarith [hR, hΘ12]
    · have := (abs_le.mp himb).1; linarith [hτlo]
    · have := (abs_le.mp himb).2; linarith [hτhi]
  have hR74 : (7 : ℝ) / 4 * (6 * Θ / 7) ≤ 3 / 2 * Θ := by nlinarith [hΘ0]
  have hR32 : (3 : ℝ) / 2 * (6 * Θ / 7) ≤ 3 / 2 * Θ := by nlinarith [hΘ0]
  have hR74' : (0 : ℝ) ≤ 7 / 4 * (6 * Θ / 7) := by positivity
  have hR32' : (0 : ℝ) ≤ 3 / 2 * (6 * Θ / 7) := by positivity
  have hτ2 : (1 : ℝ) ≤ |2 * ρ.im| := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * ρ.im)]; linarith
  refine LFunction_real_zero_free_of_disc hχ1 hχsq hρ0 hβ1 hγ2 hΘ0 (by linarith [hΘ12]) hM₀
    hdd hddlt hLq0 hσΘ hwΘ hchainC ?_ ?_ ?_ ?_
  · intro z hz
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := box ρ.im _ hR74' hR74 (by nlinarith [hΘ12])
      (by nlinarith [hΘ12, hγ2]) z hz
    exact LFunction_ratio_bound χ hΘ0 hΘ12 hM (hgrowthχ z h1 h2 h3 h4)
  · intro z hz
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := box ρ.im _ hR32' hR32 (by nlinarith [hΘ12])
      (by nlinarith [hΘ12, hγ2]) z hz
    exact LFunction_ratio_bound χ hΘ0 hΘ12 hM (hgrowthχ z h1 h2 h3 h4)
  · intro z hz
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := box (2 * ρ.im) _ hR74' hR74 (by nlinarith [hΘ12, hγ2])
      (by nlinarith [hΘ12, hγ2]) z hz
    exact Zc_ratio_sphere_bound hΘ0 hΘ12 hτ2 hM hR74' hR74 hz (hgrowthζ z h1 h2 h3 h4)
  · intro z hz
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := box (2 * ρ.im) _ hR32' hR32 (by nlinarith [hΘ12, hγ2])
      (by nlinarith [hΘ12, hγ2]) z hz
    exact Zc_ratio_sphere_bound hΘ0 hΘ12 hτ2 hM hR32' hR32 hz (hgrowthζ z h1 h2 h3 h4)

/-! ## §5 — the width law, the shape, and THE REAL ARM'S REGION -/

set_option maxHeartbeats 1600000 in
-- Pure real-analysis arithmetic (the `χ² = 1` twin of `VkTwistRegion`'s own shape lemma, with the
-- extra `log q` on `Lq`), staged through `nlinarith`.
/-- **The width arithmetic with the Euler debit.**  Same as the `χ² ≠ 1` arm's shape lemma, with
`Lq = 8 + lq + 700·Pinv·W` for an extra additive `lq ≤ A·ℓ` (the `log q` debit).  The constant is
UNCHANGED at `10⁸(A+7)`: the debit is dominated by the growth term because `Pinv ≥ 10⁷`. -/
private lemma real_width_shape {Lg ℓ L3 ℓ3 Θ M Cq A lq : ℝ}
    (hLg3 : 3 ≤ Lg) (hℓ100 : 100 ≤ ℓ)
    (hL3lb : Lg ≤ L3) (hL3ub : L3 ≤ 2 * Lg) (hℓ3def : ℓ3 = Real.log L3)
    (hℓ3lb : ℓ ≤ ℓ3) (hℓ3ub : ℓ3 ≤ 2 * ℓ)
    (hCq : 1 ≤ Cq) (hA1 : 1 ≤ A) (hgate : Real.log (20000 * Cq) ≤ A * ℓ)
    (hlq0 : 0 ≤ lq) (hlqle : lq ≤ A * ℓ)
    (hΘval : Θ = 1 / 1000 / (L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ)))
    (hMval : M = Cq * (1 + L3)) :
    0 < Θ ∧ Θ ≤ 1 / 2 ∧ 1 ≤ M ∧
      (1 / (10 ^ 8 * (A + 7))) * (1 / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)))
        ≤ 1 / (14 * (8 + lq + 700 * (1 / Θ) * Real.log (20 * M / Θ))) := by
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
  set Pinv : ℝ := 1000 * L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ) with hPinvdef
  have hPinvpos : 0 < Pinv := by rw [hPinvdef]; positivity
  have hΘPinv : Θ = 1 / Pinv := by
    rw [eq_div_iff (ne_of_gt hPinvpos), hΘval, hPinvdef]
    field_simp [ne_of_gt hL34pos, ne_of_gt hℓ30]
  have hΘ0 : 0 < Θ := by rw [hΘPinv]; positivity
  have hPinvbig : (10 : ℝ) ^ 7 ≤ Pinv := by
    rw [hPinvdef]
    have h1 : (10000 : ℝ) ≤ ℓ3 ^ (2 : ℕ) := by nlinarith [hℓ3100]
    nlinarith [hL31, h1]
  have hΘ12 : Θ ≤ 1 / 2 := by
    rw [hΘPinv, div_le_div_iff₀ hPinvpos (by norm_num)]; linarith [hPinvbig]
  have hM1 : 1 ≤ M := by rw [hMval]; nlinarith [hCq, hL31']
  have hPinvΘ : 1 / Θ = Pinv := by rw [hΘPinv, one_div_one_div]
  refine ⟨hΘ0, hΘ12, hM1, ?_⟩
  rw [hPinvΘ]
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
  have hlog1L3 : Real.log (1 + L3) ≤ 1 + ℓ3 := by
    have h1 : Real.log (1 + L3) ≤ Real.log (2 * L3) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt hL30), ← hℓ3def] at h1
    linarith
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
  -- `Pinv ≤ 8000 Lg^{3/4}ℓ²`
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
  -- the final comparison
  set D : ℝ := Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ) with hDdef
  have hLg341 : (1 : ℝ) ≤ Lg ^ ((3 : ℝ) / 4) := Real.one_le_rpow (by linarith) (by norm_num)
  have hℓcube : (10 : ℝ) ^ 6 ≤ ℓ ^ (3 : ℕ) := by nlinarith [hℓ100, hℓ0]
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hDbig : (10 : ℝ) ^ 6 ≤ D := by
    rw [hDdef]; nlinarith [hLg341, hℓcube]
  have hℓD : ℓ ≤ D := by
    rw [hDdef]
    have h1 : ℓ ≤ ℓ ^ (3 : ℕ) := by nlinarith [hℓ100, hℓ0]
    nlinarith [h1, hLg341, hℓcube]
  have hℓ3' : ℓ ^ (2 : ℕ) * ℓ = ℓ ^ (3 : ℕ) := by ring
  have hden0 : 0 < 14 * (8 + lq + 700 * Pinv * W) := by
    nlinarith [hPinvpos, hW1, hlq0]
  have step : 14 * (8 + lq + 700 * Pinv * W) ≤ 10 ^ 8 * (A + 7) * D := by
    have hgrow : 700 * Pinv * W ≤ 700 * (8000 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ)))
        * ((A + 6) * ℓ) := by
      apply mul_le_mul (by linarith [hPinvle]) hWub (by linarith [hW1])
        (by positivity)
    have hgrow' : 700 * Pinv * W ≤ 5600000 * (A + 6) * D := by
      calc 700 * Pinv * W
          ≤ 700 * (8000 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ))) * ((A + 6) * ℓ) := hgrow
        _ = 5600000 * (A + 6) * (Lg ^ ((3 : ℝ) / 4) * (ℓ ^ (2 : ℕ) * ℓ)) := by ring
        _ = 5600000 * (A + 6) * D := by rw [hℓ3', hDdef]
    have hlqD : lq ≤ A * D := by
      calc lq ≤ A * ℓ := hlqle
        _ ≤ A * D := mul_le_mul_of_nonneg_left hℓD (by linarith)
    nlinarith [hgrow', hlqD, hDbig, hA1, hDpos]
  have hcmp : (1 : ℝ) / (10 ^ 8 * (A + 7) * D)
      ≤ 1 / (14 * (8 + lq + 700 * Pinv * W)) := by
    apply one_div_le_one_div_of_le hden0 step
  have heq : (1 / (10 ^ 8 * (A + 7))) * (1 / D) = 1 / (10 ^ 8 * (A + 7) * D) := by
    rw [div_mul_div_comm, one_mul]
  rw [heq]
  exact hcmp

set_option maxHeartbeats 1600000 in
-- The log-scale bookkeeping plus the width-law gates at `dd = 1/2`.
/-- **THE REAL ARM'S REGION, positive height.**  For a REAL non-principal `χ mod q` (`χ² = 1`),
every zero `ρ` of `L(·,χ)` with `Re ρ < 1` and `Im ρ ≥ exp(exp 100) + 1` obeys, under the
`q`-scale gate `log(20000·(vkStripConst q + 8104)) ≤ A·log log Im ρ`,

  `Re ρ ≤ 1 − (1/(10⁸(A+7)))·1/((log Im ρ)^{3/4}(log log Im ρ)³)`

— the SAME width and the SAME constant as the `χ² ≠ 1` arm.  The growth ceiling is the common
`M = (vkStripConst q + 8104)·(1 + log 3 Im ρ)`, dominating stone A's `L(·,χ)` box growth AND ζ's
own (`zeta_box_growth_explicit`); the Euler debit `log q` rides inside the gate. -/
theorem LFunction_real_zero_free_region_vk_pos {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) (hχsq : χ ^ 2 = 1) {A : ℝ} (hA1 : 1 ≤ A)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hβ1 : ρ.re < 1)
    (hheight : Real.exp (Real.exp 100) + 1 ≤ ρ.im)
    (hgate : Real.log (20000 * (vkStripConst q + 8104))
      ≤ A * Real.log (Real.log ρ.im)) :
    ρ.re ≤ 1 - (1 / (10 ^ 8 * (A + 7)))
      * (1 / ((Real.log ρ.im) ^ ((3 : ℝ) / 4) * (Real.log (Real.log ρ.im)) ^ (3 : ℕ))) := by
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hγfloor : Real.exp (Real.exp 100) ≤ ρ.im - 1 := by linarith
  have hγpos : 0 < ρ.im := by linarith [Real.exp_pos (Real.exp 100)]
  have hγ2 : (2 : ℝ) ≤ ρ.im := by linarith
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
  -- the common growth ceiling
  set Cq : ℝ := vkStripConst q + 8104 with hCqdef
  have hCq1 : (1 : ℝ) ≤ Cq := by
    have := one_le_vkStripConst (q := q); rw [hCqdef]; linarith
  set Θ : ℝ := vkTheta (3 * ρ.im) with hΘdef
  have hΘval : Θ = 1 / 1000 / (L3 ^ ((3 : ℝ) / 4) * ell3 ^ (2 : ℕ)) := by
    rw [hΘdef, vkTheta, ← hL3def, ← hell3def]
  set M : ℝ := Cq * (1 + L3) with hMdef
  -- the `log q` debit rides inside the gate
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq0 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1R
  have hlogqle : Real.log (q : ℝ) ≤ A * ell := by
    refine le_trans ?_ hgate
    apply Real.log_le_log (by linarith)
    rw [hCqdef, vkStripConst]
    nlinarith [hq1R]
  obtain ⟨hΘ0, hΘ12, hM1, hshape⟩ := real_width_shape hLg3 hell100 hL3lb hL3ub hell3def
    hell3lb hell3ub hCq1 hA1 hgate hlogq0 hlogqle hΘval hMdef
  -- the two growths, against the common `M`
  have hC0 : (0 : ℝ) ≤ vkStripConst q := by
    have := one_le_vkStripConst (q := q); linarith
  have hL3nn : (0 : ℝ) ≤ 1 + L3 := by linarith
  have hgrowthχ : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
      ‖LFunction χ z‖ ≤ M := by
    intro z h1 h2 h3 h4
    have h := vk_char_box_growth χ hχ1 hγfloor z (by rw [← hΘdef]; exact h1) h2 h3 h4
    rw [← hL3def] at h
    rw [hMdef, hCqdef]
    nlinarith [h, hL3nn]
  have hgrowthζ : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
      ‖riemannZeta z‖ ≤ M := by
    intro z h1 h2 h3 h4
    have h := zeta_box_growth_explicit hγfloor z (by rw [← hΘdef]; exact h1) h2 h3 h4
    rw [← hL3def] at h
    rw [hMdef, hCqdef]
    nlinarith [h, hL3nn, hC0, hL30]
  -- the width law at `dd = 1/2`, `Lq = 8 + log q + 700·Pinv·W`
  set Pinv : ℝ := 1 / Θ with hPinvdef
  have hPinvpos : 0 < Pinv := by rw [hPinvdef]; positivity
  have hPinv2 : 2 ≤ Pinv := by
    rw [hPinvdef, le_div_iff₀ hΘ0]; linarith [hΘ12]
  set W : ℝ := Real.log (20 * M / Θ) with hWdef
  have hW1 : (1 : ℝ) ≤ W := by
    have h20 : (40 : ℝ) ≤ 20 * M / Θ := by
      rw [le_div_iff₀ hΘ0]; nlinarith [hM1, hΘ12]
    have he : Real.exp 1 ≤ 20 * M / Θ :=
      le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) h20
    rw [hWdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
  set Lq : ℝ := 8 + Real.log (q : ℝ) + 700 * Pinv * W with hLqdef
  have hLqgeP : Pinv ≤ Lq := by
    rw [hLqdef]
    have hkey : 700 * Pinv * 1 ≤ 700 * Pinv * W :=
      mul_le_mul_of_nonneg_left hW1 (by positivity)
    nlinarith [hkey, hPinvpos, hlogq0]
  have hLq0 : 0 < Lq := lt_of_lt_of_le hPinvpos hLqgeP
  have hΘPinv : Θ = 1 / Pinv := by rw [hPinvdef, one_div_one_div]
  have hσΘ : (1 : ℝ) / 2 / Lq ≤ Θ / 2 := by
    rw [hΘPinv, div_div, div_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [hLqgeP])
  have hwΘ : (1 : ℝ) / 2 / (7 * Lq) ≤ 11 / 14 * Θ := by
    rw [hΘPinv, mul_one_div, div_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hLqgeP, hPinvpos, hLq0]
  have hchainC : 8 + Real.log (q : ℝ)
      + 5 * ((120 / (6 * Θ / 7)) * Real.log (4 * (5 * M / Θ))) ≤ Lq / (2 * (1 / 2)) := by
    have h1 : (120 : ℝ) / (6 * Θ / 7) = 140 * Pinv := by
      rw [hΘPinv]; field_simp; ring
    have h2 : (4 : ℝ) * (5 * M / Θ) = 20 * M / Θ := by ring
    rw [h1, h2, ← hWdef, show (2 : ℝ) * (1 / 2) = 1 by norm_num, div_one, hLqdef]
    exact le_of_eq (by ring)
  have hreg := LFunction_real_region_of_growth hχ1 hχsq hρ0 hβ1 (Θ := Θ) (M := M) (Lq := Lq)
    (dd := 1 / 2) hΘ0 hΘ12 hγ2 hM1 (by norm_num) (by norm_num) hLq0 hσΘ hwΘ hchainC
    hgrowthχ hgrowthζ
  -- the width, in shape
  have hEq : (1 : ℝ) / 2 / (7 * Lq) = 1 / (14 * (8 + Real.log (q : ℝ) + 700 * Pinv * W)) := by
    rw [hLqdef]
    rw [div_div, show (2 : ℝ) * (7 * (8 + Real.log (q : ℝ) + 700 * Pinv * W))
      = 14 * (8 + Real.log (q : ℝ) + 700 * Pinv * W) from by ring]
  rw [hEq] at hreg
  rw [hPinvdef, hWdef] at hreg
  linarith [hreg, hshape]

/-- **THE REAL ARM'S EXIT — both heights.**  As `LFunction_real_zero_free_region_vk_pos`, with the
negative-height half folded in.  For a real `χ` the conjugate character IS `χ`
(`χ⁻¹ = χ` when `χ² = 1`), so the fold is `Salt.SW.LFunction_conj_zero` — no new hypothesis. -/
theorem LFunction_real_zero_free_region_vk {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) (hχsq : χ ^ 2 = 1) {A : ℝ} (hA1 : 1 ≤ A)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hβ1 : ρ.re < 1)
    (hheight : Real.exp (Real.exp 100) + 1 ≤ |ρ.im|)
    (hgate : Real.log (20000 * (vkStripConst q + 8104))
      ≤ A * Real.log (Real.log |ρ.im|)) :
    ρ.re ≤ 1 - (1 / (10 ^ 8 * (A + 7)))
      * (1 / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ))) := by
  rcases le_or_gt 0 ρ.im with hpos | hneg
  · rw [abs_of_nonneg hpos] at hheight hgate ⊢
    exact LFunction_real_zero_free_region_vk_pos hχ1 hχsq hA1 hρ0 hβ1 hheight hgate
  · rw [abs_of_neg hneg] at hheight hgate ⊢
    have hzero := LFunction_conj_zero hχ1 hχsq hρ0
    have hre : ((starRingEnd ℂ) ρ).re = ρ.re := Complex.conj_re ρ
    have him : ((starRingEnd ℂ) ρ).im = -ρ.im := Complex.conj_im ρ
    have hmain := LFunction_real_zero_free_region_vk_pos hχ1 hχsq hA1 hzero
      (by rw [hre]; exact hβ1) (by rw [him]; exact hheight) (by rw [him]; exact hgate)
    rw [hre, him] at hmain
    exact hmain

end Salt.MR

end
