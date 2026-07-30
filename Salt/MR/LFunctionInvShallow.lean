/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MobiusChiRate
import Salt.MR.ChiLLower
import Salt.Vk.Landau

/-!
# ⟦THE SHALLOW SLOT⟧ — the χ-VK inverse bound `‖1/L(σ+it,χ)‖` just inside the region

The closing stone of `Salt/MR/MobiusChiRate.lean` §6: the `L(·,χ)` analogue of the landed
`Salt.SW.zeta_inv_shallow`, moved from the classical width to the VK width.

## What lands here, and the one correction it forces

`norm_LFunction_inv_shallow_of_ball` (§1) is the analytic core, and it is CHEAPER than the
banked route: **no Jensen zero count is needed.**  P-5's §6 named "a Jensen zero count
`∑m ≲ log 4M₀` on the ball" as the one missing input.  It is missing because it is
unnecessary — the Landau/Borel–Carathéodory ball can be taken ENTIRELY INSIDE the zero-free
region, and then the factorization's zero set is EMPTY (`Z = ∅`), so the whole product factor
and its count disappear.  What is left is one transport of `log‖L‖` along a horizontal
segment against `‖logDeriv h‖ ≤ (120/λ)·log(4M₀)`, anchored at the landed reference
`‖L((1+W)+it,χ)‖ ≥ W/32` (`Salt.MR.LFunction_near_one_lower`, unconditional, every `χ`).

The price of that simplification is the geometry: the ball has radius `≍ η` (the region's
own width), the transport runs from `1 + W` down to `1 − W`, and the Borel–Carathéodory cost
is `(120/λ)·log(4M₀)` PER UNIT LENGTH.  So the loss is
`exp(240·W·log(4M₀)/λ)`, and it is `O(1)` **iff**

  `W ≲ η / log(4 M₀)`,   `log(4M₀) ≍ log q + log log H`.

**That inequality is the finding.**  The slot as stated in `MobiusChiRate.lean`
(`LFunctionInvShallowVk`, width `vkShallowWidth c₄ q H = c₄/((log q+1)(log H)^{3/4}(loglog H)³)`)
puts the shallow line at a CONSTANT multiple of `η = boxWidth/2` — i.e. at `W ≍ η`, not at
`W ≍ η/log(4M₀)` — so no constant `c₄` can satisfy it: the requirement is
`c₄ · (log q + log log H) ≲ log log H`, which fails for every `c₄ > 0` as `q` or `H` grows.
The repair is exactly one factor of `(log q + 1)` and one factor of `log log H`:

  `vkShallowWidthSharp c₄ q H = c₄ / ((log q + 1)² · (log H)^{3/4} · (log log H)⁴)`

and it is the SAME correction the landed `q = 1` twin already pays: `Salt.MR.zeta_pow_lower`
cuts at `w = η/ℓ = c·L^{-3/4}·ℓ^{-4}` — "the loglog power `4 = 3 (region) + 1 (the `w = η/ℓ`
cut)" (that file's own header).  The `q`-factor is the χ-half of the same price, because the
ball's Borel–Carathéodory constant reads `log(4M₀) ≍ log q + loglog H` where ζ's reads
`loglog t`.  §4 proves `LFunctionInvShallowVkSharp` — `LFunctionInvShallowVk` verbatim EXCEPT
for the width — and §5 records what the amendment costs downstream: **nothing.**  The
consumer's budget (`MobiusChiRate.lean` §6) reads the saving `exp(−W·log x)` at
`q ≤ (log x)^12`, `log H ≤ 2 log x`, so the corrected `W` gives
`exp(−c(log x)^{1/4}/(log log x)^6)` in place of `exp(−c(log x)^{1/4}/(log log x)^4)` — still
a quasi-power, still `o((log x)^{−A})` for every fixed `A`, and the `o(1)` budget still
clears with the whole `0.29` unspent (only the finite `x₀` inside `MmuChiRate`'s `∃x₀` moves).

## The second deviation: the carve-out needs a MARGIN

`LFunctionInvShallowVk` carries the ξ₁ carve-out as
`∀ρ, L χ ρ = 0 → ρ.im = 0 → ρ.re < 1 − vkShallowWidth c₄ q H`, i.e. STRICTLY left of the
shallow line and no further.  That cannot support any bound of the stated form: a real zero at
`β = 1 − W − ε` satisfies the hypothesis for every `ε > 0`, while `‖1/L((1−W)+i0,χ)‖ ≥ c/ε`.
The carve-out must exclude real zeros from a NEIGHBOURHOOD of the line, and the natural
neighbourhood is the region's own: §4 states it at `vkShallowWidth (10⁻⁶) q H`, which
dominates `boxWidth` (the corpus's own region width, `MobiusChiRate.lean` §5) for every `q`
and every admissible `H`.  This is what wave P-7's Siegel fold has to deliver anyway — the
ξ₁ row is a `1/√q`-genre or `q^{-ε}`-genre statement, worlds wider than either width.

## The route, and the dead end that stays dead

* the anchor-plus-Cauchy transport (P-5's banked dead end) is confirmed dead: it needs
  `W ≲ Θ⁴/M⁵`, and the landed strip growth `M = vkStripConst q·(1+log 3γ) = 5000q(…)` puts
  `q⁵` in the denominator;
* the Borel–Carathéodory route below never touches `M` polynomially: `M` enters ONLY through
  `log(4M₀)`, which is why `5000q` costs one `log q` and nothing more.

Growth is supplied on two arms, matching §5's region split: above the VK floor the landed
`vk_char_strip_growth` (`M ≍ 5000q·log H`), below it the landed
`Salt.MR.LFunction_norm_le_level` (Pólya–Vinogradov, `M ≍ q^{3/2}(1+‖z‖)(1+log q)`, whose
`‖z‖ ≤ exp(exp 100) + 4` is a CONSTANT there).  The `χ₀` / `q = 1` row is NOT covered — the
slot's own statement excludes `χ = 1` — and it needs the `Zc`-normalized twin of §1 plus the
compact pole patch, exactly as P-5 recorded.
-/

noncomputable section

namespace Salt.MR

open Complex Metric Set DirichletCharacter
open Salt.SW Salt.Vk
open scoped LSeries.notation

/-! ## §1 — THE CORE: a zero-free Landau ball forces the inverse bound

Everything analytic happens here.  The hypotheses are geometric and quantitative; §2–§3
discharge them from the landed region and growth. -/

/-- **THE SHALLOW CORE.**  Let `c = (1+W) + it` be the reference point at depth `W` to the
RIGHT of the 1-line.  If

* `‖L(·,χ)‖ ≤ M` on the closed ball of radius `7λ/4` about `c` (growth),
* `L(·,χ)` has NO zero in the open ball of radius `3λ/2` about `c` (the region),
* `2W ≤ 23λ/20` (the segment `[1−W, 1+W] + it` sits inside Landau's inner ball), and
* `240·W·log(4·32M/W) ≤ λ` (the budget),

then `‖L(σ+it,χ)⁻¹‖ ≤ 88/W` throughout `1 − W ≤ σ ≤ 1 + W`.

Route: `Salt.Vk.entire_norm_logDeriv_sub_sum_scaled` at `G = L/L(c)` (entire for `χ ≠ 1`,
`G c = 1`), whose zero set `Z` is EMPTY by the second hypothesis, so its numeric conjunct is
the bare `‖logDeriv L‖ ≤ (120/λ)·log(4M₀)` on the inner ball; the mean-value inequality then
transports `log‖L‖` from `c` to `σ+it` at cost `≤ 1`, and the reference floor
`‖L(c)‖ ≥ W/32` (`LFunction_near_one_lower`) closes it.  `88 ≥ 32·e`. -/
theorem norm_LFunction_inv_shallow_of_ball {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) {t W lam M : ℝ}
    (hW0 : 0 < W) (hW1 : W ≤ 1) (hlam0 : 0 < lam) (hM1 : 1 ≤ M)
    (hreach : 2 * W ≤ 23 / 20 * lam)
    (hgrow : ∀ z : ℂ, ‖z - (((1 + W : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ 7 / 4 * lam →
        ‖LFunction χ z‖ ≤ M)
    (hzf : ∀ z : ℂ, ‖z - (((1 + W : ℝ) : ℂ) + (t : ℂ) * I)‖ < 3 / 2 * lam →
        LFunction χ z ≠ 0)
    (hbudget : 240 * W * Real.log (4 * (32 * M / W)) ≤ lam)
    {σ : ℝ} (hσlo : 1 - W ≤ σ) (hσhi : σ ≤ 1 + W) :
    ‖(LFunction χ ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ 88 / W := by
  classical
  set c : ℂ := ((1 + W : ℝ) : ℂ) + (t : ℂ) * I with hcdef
  -- the reference floor at the center
  have href : (1 / 32 : ℝ) * W ≤ ‖LFunction χ c‖ := LFunction_near_one_lower χ hW0 hW1
  have hLcpos : 0 < ‖LFunction χ c‖ := lt_of_lt_of_le (by positivity) href
  have hLc : LFunction χ c ≠ 0 := by
    rw [← norm_pos_iff]; exact hLcpos
  set M₀ : ℝ := 32 * M / W with hM₀def
  have hM₀ : 1 ≤ M₀ := by
    rw [hM₀def, le_div_iff₀ hW0]; nlinarith
  have hM₀pos : 0 < M₀ := lt_of_lt_of_le zero_lt_one hM₀
  have hlog4 : 0 < Real.log (4 * M₀) := Real.log_pos (by nlinarith)
  -- the normalized function and its log-derivative
  have hLdiff : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ1
  have hG_diff : Differentiable ℂ (fun z => LFunction χ z / LFunction χ c) :=
    fun z => (hLdiff z).div_const _
  have hGc_floor : (1 : ℝ) / 4 ≤ ‖LFunction χ c / LFunction χ c‖ := by
    rw [div_self hLc, norm_one]; norm_num
  have hLDG : ∀ z, logDeriv (fun w => LFunction χ w / LFunction χ c) z
      = logDeriv (LFunction χ) z := by
    intro z
    have hGeq : (fun w => LFunction χ w / LFunction χ c)
        = fun w => (LFunction χ c)⁻¹ * LFunction χ w := by funext w; ring
    rw [hGeq, logDeriv_const_mul z (LFunction χ c)⁻¹ (inv_ne_zero hLc)]
  -- the two sphere bounds
  have hsph : ∀ r : ℝ, r ≤ 7 / 4 * lam → ∀ z ∈ sphere c r,
      ‖LFunction χ z / LFunction χ c‖ ≤ M₀ := by
    intro r hr z hz
    have hzc : ‖z - c‖ = r := by rw [mem_sphere_iff_norm] at hz; exact hz
    have hzM := hgrow z (by rw [hzc]; exact hr)
    rw [norm_div, hM₀def, div_le_div_iff₀ hLcpos hW0]
    nlinarith [href, norm_nonneg (LFunction χ z), hM1]
  obtain ⟨Z, m, _hh, hmemb, -, -, -, -, hnum⟩ :=
    entire_norm_logDeriv_sub_sum_scaled hG_diff hlam0 hM₀ hGc_floor
      (hsph _ le_rfl) (hsph _ (by linarith))
  -- THE ZERO SET IS EMPTY (this is what replaces the Jensen count)
  have hZempty : Z = ∅ := by
    refine Finset.eq_empty_of_forall_notMem (fun ρ hρ => ?_)
    obtain ⟨hball, hzero⟩ := hmemb ρ hρ
    have hLρ : LFunction χ ρ = 0 := (div_eq_zero_iff.mp hzero).resolve_right hLc
    rw [mem_ball, dist_eq_norm] at hball
    exact hzf ρ hball hLρ
  set K : ℝ := 120 / lam * Real.log (4 * M₀) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  -- the numeric bound, with the empty product
  have hnumbd : ∀ u : ℝ, |u - (1 + W)| ≤ 2 * W →
      ‖logDeriv (LFunction χ) ((u : ℂ) + (t : ℂ) * I)‖ ≤ K := by
    intro u hu
    have hsub : ((u : ℂ) + (t : ℂ) * I) - c = ((u - (1 + W) : ℝ) : ℂ) := by
      rw [hcdef]; push_cast; ring
    have hdist : ‖((u : ℂ) + (t : ℂ) * I) - c‖ ≤ 23 / 20 * lam := by
      rw [hsub, Complex.norm_real, Real.norm_eq_abs]; linarith [hu, hreach]
    have hne : LFunction χ ((u : ℂ) + (t : ℂ) * I) / LFunction χ c ≠ 0 := by
      refine div_ne_zero (hzf _ ?_) hLc
      calc ‖((u : ℂ) + (t : ℂ) * I) - c‖ ≤ 23 / 20 * lam := hdist
        _ < 3 / 2 * lam := by nlinarith
    have hres := hnum ((u : ℂ) + (t : ℂ) * I) hdist hne
    rw [hLDG, hZempty] at hres
    simpa [hKdef] using hres
  -- the horizontal transport of `log‖L‖`
  have hmemIcc : ∀ v ∈ Set.Icc (1 - W) (1 + W), |v - (1 + W)| ≤ 2 * W := by
    intro v hv
    rw [abs_le]
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hLne : ∀ v ∈ Set.Icc (1 - W) (1 + W), LFunction χ ((v : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro v hv
    refine hzf _ ?_
    have hsub : ((v : ℂ) + (t : ℂ) * I) - c = ((v - (1 + W) : ℝ) : ℂ) := by
      rw [hcdef]; push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs]
    have hvb := hmemIcc v hv
    linarith [hreach]
  have hderiv : ∀ v ∈ Set.Icc (1 - W) (1 + W),
      HasDerivWithinAt (fun w : ℝ => Real.log ‖LFunction χ ((w : ℂ) + (t : ℂ) * I)‖)
        ((logDeriv (LFunction χ) ((v : ℂ) + (t : ℂ) * I)).re) (Set.Icc (1 - W) (1 + W)) v := by
    intro v hv
    exact (hasDerivAt_log_norm_horiz (hLdiff _) (hLne v hv)).hasDerivWithinAt
  have hbnd : ∀ v ∈ Set.Icc (1 - W) (1 + W),
      ‖(logDeriv (LFunction χ) ((v : ℂ) + (t : ℂ) * I)).re‖ ≤ K := by
    intro v hv
    calc ‖(logDeriv (LFunction χ) ((v : ℂ) + (t : ℂ) * I)).re‖
        ≤ ‖logDeriv (LFunction χ) ((v : ℂ) + (t : ℂ) * I)‖ := by
          rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
      _ ≤ K := hnumbd v (hmemIcc v hv)
  have hmvt := (convex_Icc (1 - W) (1 + W)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbnd (Set.right_mem_Icc.mpr (by linarith)) (Set.mem_Icc.mpr ⟨hσlo, hσhi⟩)
  -- the transported floor
  have hstep : |σ - (1 + W)| ≤ 2 * W := hmemIcc σ (Set.mem_Icc.mpr ⟨hσlo, hσhi⟩)
  have hloss : K * ‖σ - (1 + W)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    have h1 : K * |σ - (1 + W)| ≤ K * (2 * W) :=
      mul_le_mul_of_nonneg_left hstep hKpos.le
    have h2 : K * (2 * W) ≤ 1 := by
      rw [hKdef, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_one hlam0]
      linarith [hbudget]
    linarith
  have hφlow : Real.log ((1 / 32 : ℝ) * W) - 1
      ≤ Real.log ‖LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ := by
    have hkey : |Real.log ‖LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖
        - Real.log ‖LFunction χ (((1 + W : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤ 1 := by
      rw [← Real.norm_eq_abs]
      exact le_trans hmvt hloss
    have h2 := (abs_le.mp hkey).1
    have h3 : Real.log ((1 / 32 : ℝ) * W)
        ≤ Real.log ‖LFunction χ (((1 + W : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
      rw [show (((1 + W : ℝ) : ℂ) + (t : ℂ) * I) = c from rfl]
      exact Real.log_le_log (by positivity) href
    linarith
  -- exponentiate
  have hLσpos : 0 < ‖LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ := by
    rw [norm_pos_iff]
    exact hLne σ (Set.mem_Icc.mpr ⟨hσlo, hσhi⟩)
  have hexp : Real.exp (Real.log ((1 / 32 : ℝ) * W) - 1)
      ≤ ‖LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ := by
    rw [← Real.exp_log hLσpos]
    exact Real.exp_le_exp.mpr hφlow
  have hval : (1 / 88 : ℝ) * W ≤ ‖LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ := by
    refine le_trans ?_ hexp
    rw [Real.exp_sub, Real.exp_log (by positivity : (0:ℝ) < (1/32 : ℝ) * W)]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hepos : 0 < Real.exp 1 := Real.exp_pos 1
    rw [le_div_iff₀ hepos]
    nlinarith [hW0]
  rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ hLσpos hW0]
  nlinarith [hval]

/-! ## §2 — the two geometric hypotheses, discharged from the LANDED region and growth -/

/-- **The zero-free ball.**  §5's box discharge (`LFunction_no_zero_in_box`, at the box height
`H + 1` so that the ball's own heights are covered) says no zero has
`Re ρ ≥ 1 − boxWidth/2`; the ball of radius `η + W` about `(1+W)+it` with
`η = boxWidth c₀ A q (H+1)/2` reaches only down to `Re = 1 − η`, so it is zero-free. -/
theorem LFunction_ne_zero_of_shallow_ball {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) {A c₀ H t W : ℝ} (hA1 : 1 ≤ A) (hc₀pos : 0 < c₀)
    (hH : Real.exp (Real.exp 100) + 1 ≤ H) (ht : |t| ≤ H)
    (hgate : Real.log (20000 * (vkStripConst q + 8104)) ≤ 100 * A)
    (hcl : ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re →
        (χ.primitiveCharacter ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)))
    (hcarve : ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ.im = 0 →
        ρ.re ≤ 1 - boxWidth c₀ A q (H + 1))
    (hW0 : 0 < W) (hW : W ≤ 1 / 4)
    {z : ℂ} (hz : ‖z - (((1 + W : ℝ) : ℂ) + (t : ℂ) * I)‖
        < boxWidth c₀ A q (H + 1) / 2 + W) :
    LFunction χ z ≠ 0 := by
  intro hz0
  have hH1 : Real.exp (Real.exp 100) + 1 ≤ H + 1 := by linarith
  have hbw : boxWidth c₀ A q (H + 1) ≤ 1 / 2 := boxWidth_le_half c₀ A q (H + 1)
  have hbwpos : 0 < boxWidth c₀ A q (H + 1) := boxWidth_pos hA1 hc₀pos hH1
  set c : ℂ := ((1 + W : ℝ) : ℂ) + (t : ℂ) * I with hcdef
  have hcre : c.re = 1 + W := by rw [hcdef]; simp
  have hcim : c.im = t := by rw [hcdef]; simp
  have hre : |z.re - (1 + W)| ≤ ‖z - c‖ := by
    have h := Complex.abs_re_le_norm (z - c)
    rwa [Complex.sub_re, hcre] at h
  have him : |z.im - t| ≤ ‖z - c‖ := by
    have h := Complex.abs_im_le_norm (z - c)
    rwa [Complex.sub_im, hcim] at h
  have hβ : 1 - boxWidth c₀ A q (H + 1) / 2 ≤ z.re := by
    have h1 := (abs_le.mp hre).1
    linarith [hz]
  have hIm : |z.im| ≤ H + 1 := by
    have h2 := (abs_le.mp him).2
    have h3 := (abs_le.mp him).1
    have h4 := (abs_le.mp ht).1
    have h5 := (abs_le.mp ht).2
    rw [abs_le]
    constructor <;> linarith [hz]
  exact LFunction_no_zero_in_box hχ1 hA1 hc₀pos hH1 hgate hcl hcarve hz0 hβ hIm

/-- The uniform growth ceiling on the shallow ball: `5000·q³·(e^{e^100}+5)·(1+log(H+1))`.
Crude by design — `M` enters the closing bound ONLY through `log(4M₀)`, so a `q³` costs three
`log q` and nothing more.  The `q³` and the `e^{e^100}` are the two arms' prices: the
Pólya–Vinogradov arm below the VK floor carries `q^{3/2}(1+log q)(1+‖z‖)` with `‖z‖` bounded
by the floor itself. -/
def shallowGrowth (q : ℕ) (H : ℝ) : ℝ :=
  5000 * (q : ℝ) ^ 3 * (Real.exp (Real.exp 100) + 5) * (1 + Real.log (H + 1))

lemma one_le_shallowGrowth {q : ℕ} [NeZero q] {H : ℝ}
    (hH : Real.exp (Real.exp 100) + 1 ≤ H) : 1 ≤ shallowGrowth q H := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hE : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  have hHpos : (0 : ℝ) < H + 1 := by linarith
  have hlog : (0 : ℝ) ≤ Real.log (H + 1) := Real.log_nonneg (by linarith)
  have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq1
  have hC : (1 : ℝ) ≤ 1 + Real.log (H + 1) := by linarith
  have hE5 : (1 : ℝ) ≤ Real.exp (Real.exp 100) + 5 := by linarith
  have h1 : (1 : ℝ) ≤ 5000 * (q : ℝ) ^ 3 := by nlinarith
  have h2 : (1 : ℝ) ≤ 5000 * (q : ℝ) ^ 3 * (Real.exp (Real.exp 100) + 5) := by nlinarith
  rw [shallowGrowth]
  nlinarith

/-- **The growth on the shallow ball, both arms.**  For `‖z − ((1+W)+it)‖ ≤ r` with
`r ≤ min (1/8) (vkTheta (H+1))`:

* `|t|` above the VK floor — the landed `vk_char_strip_growth` (the ball stays inside the VK
  strip because `r ≤ vkTheta(H+1) ≤ vkTheta|Im z|`, `vkTheta` being antitone);
* `|t|` below it — the landed `LFunction_norm_le_level` (Pólya–Vinogradov at level `q`), where
  `‖z‖ ≤ e^{e^100} + 4` is a constant.

Both are majorized by `shallowGrowth q H`. -/
theorem norm_LFunction_le_shallowGrowth {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) {H t W r : ℝ} (hH : Real.exp (Real.exp 100) + 1 ≤ H) (ht : |t| ≤ H)
    (hW0 : 0 < W) (hW : W ≤ 1 / 8) (hr : r ≤ 1 / 8)
    (hrΘ : r ≤ vkTheta (H + 1))
    {z : ℂ} (hz : ‖z - (((1 + W : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ r) :
    ‖LFunction χ z‖ ≤ shallowGrowth q H := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hlogH : (0 : ℝ) ≤ Real.log (H + 1) := Real.log_nonneg (by linarith)
  set c : ℂ := ((1 + W : ℝ) : ℂ) + (t : ℂ) * I with hcdef
  have hcre : c.re = 1 + W := by rw [hcdef]; simp
  have hcim : c.im = t := by rw [hcdef]; simp
  have hre : |z.re - (1 + W)| ≤ r := by
    have h := Complex.abs_re_le_norm (z - c)
    rw [Complex.sub_re, hcre] at h; linarith
  have him : |z.im - t| ≤ r := by
    have h := Complex.abs_im_le_norm (z - c)
    rw [Complex.sub_im, hcim] at h; linarith
  have hrelo : 1 / 2 ≤ z.re := by linarith [(abs_le.mp hre).1]
  have hrehi : z.re ≤ 2 := by linarith [(abs_le.mp hre).2]
  have himhi : |z.im| ≤ H + 1 := by
    have h2 := (abs_le.mp him).2
    have h3 := (abs_le.mp him).1
    have h4 := (abs_le.mp ht).1
    have h5 := (abs_le.mp ht).2
    rw [abs_le]; constructor <;> linarith
  by_cases hcase : Real.exp (Real.exp 100) + 1 ≤ |t|
  · -- ARM 1: above the VK floor, the landed strip growth
    have himlo : Real.exp (Real.exp 100) ≤ |z.im| := by
      have h2 := (abs_le.mp him).2
      have h3 := (abs_le.mp him).1
      rcases le_or_gt 0 t with htpos | htneg
      · rw [abs_of_nonneg htpos] at hcase
        rw [abs_le] at him
        have : Real.exp (Real.exp 100) ≤ z.im := by linarith [him.1]
        calc Real.exp (Real.exp 100) ≤ z.im := this
          _ ≤ |z.im| := le_abs_self _
      · rw [abs_of_neg htneg] at hcase
        rw [abs_le] at him
        have : z.im ≤ -Real.exp (Real.exp 100) := by linarith [him.2]
        calc Real.exp (Real.exp 100) = -(-Real.exp (Real.exp 100)) := by ring
          _ ≤ -z.im := by linarith
          _ ≤ |z.im| := neg_le_abs _
    have himpos : (0 : ℝ) < |z.im| := lt_of_lt_of_le (Real.exp_pos _) himlo
    have hime : Real.exp 1 < |z.im| := by
      have h1 : Real.exp 1 < Real.exp (Real.exp 100) := Real.exp_lt_exp.mpr (by linarith)
      linarith
    have hΘmono : vkTheta (H + 1) ≤ vkTheta |z.im| := vkTheta_anti hime himhi
    have hstrip : 1 - vkTheta |z.im| ≤ z.re := by
      have := (abs_le.mp hre).1
      linarith
    have hgrow := vk_char_strip_growth χ hχ1 (σ := z.re) (T := z.im) himlo hstrip hrehi
    rw [Complex.re_add_im z] at hgrow
    have hloglt : Real.log |z.im| ≤ Real.log (H + 1) :=
      Real.log_le_log himpos himhi
    have hq3 : (q : ℝ) ≤ (q : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (q : ℝ) by positivity)
        (show (0 : ℝ) ≤ (q : ℝ) - 1 by linarith)) (show (0 : ℝ) ≤ (q : ℝ) + 1 by linarith)]
    have hE5 : (1 : ℝ) ≤ Real.exp (Real.exp 100) + 5 := by linarith
    have hlogim : (0 : ℝ) ≤ Real.log |z.im| := Real.log_nonneg (by linarith)
    have h1 : 5000 * (q : ℝ) ≤ 5000 * (q : ℝ) ^ 3 * (Real.exp (Real.exp 100) + 5) := by
      have hstep2 : 5000 * (q : ℝ) ^ 3 * 1
          ≤ 5000 * (q : ℝ) ^ 3 * (Real.exp (Real.exp 100) + 5) :=
        mul_le_mul_of_nonneg_left hE5 (by positivity)
      nlinarith [hq3, hstep2]
    calc ‖LFunction χ z‖ ≤ vkStripConst q * (1 + Real.log |z.im|) := hgrow
      _ ≤ 5000 * (q : ℝ) ^ 3 * (Real.exp (Real.exp 100) + 5) * (1 + Real.log (H + 1)) := by
          rw [vkStripConst]
          exact mul_le_mul h1 (by linarith) (by linarith) (by positivity)
      _ = shallowGrowth q H := by rw [shallowGrowth]
  · -- ARM 2: below the VK floor, Pólya–Vinogradov at level `q`
    rw [not_le] at hcase
    have hznorm : ‖z‖ ≤ Real.exp (Real.exp 100) + 4 := by
      have h := Complex.norm_le_abs_re_add_abs_im z
      have h1 : |z.re| ≤ 2 := by
        rw [abs_le]; exact ⟨by linarith [hrelo], hrehi⟩
      have h2 : |z.im| ≤ Real.exp (Real.exp 100) + 2 := by
        have h3 := (abs_le.mp him).2
        have h4 := (abs_le.mp him).1
        have h5 := (abs_le.mp (le_of_lt hcase)).1
        have h6 := (abs_le.mp (le_of_lt hcase)).2
        rw [abs_le]; constructor <;> linarith
      linarith
    have hlvl := LFunction_norm_le_level χ hχ1 hrelo (by linarith : z.re ≤ 4)
    have hsq : Real.sqrt (q : ℝ) ≤ (q : ℝ) := by
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (q : ℝ)),
        Real.sqrt_nonneg ((q : ℝ)), hq1]
    have hlq : 1 + Real.log (q : ℝ) ≤ (q : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (q : ℝ))
      linarith
    have hstep : (q : ℝ) * (3 * (1 + ‖z‖) * Real.sqrt q * (1 + Real.log q))
        ≤ shallowGrowth q H := by
      have hPnn : (0 : ℝ) ≤ 3 * (1 + ‖z‖) := by positivity
      have hP' : 3 * (1 + ‖z‖) ≤ 3 * (Real.exp (Real.exp 100) + 5) := by linarith
      have hlognn : (0 : ℝ) ≤ 1 + Real.log (q : ℝ) := by
        linarith [Real.log_nonneg hq1]
      have hqnn : (0 : ℝ) ≤ (q : ℝ) := by positivity
      -- replace `√q → q`, then `1+log q → q`, then `1+‖z‖ → e^{e^100}+5`
      have hA : 3 * (1 + ‖z‖) * Real.sqrt q * (1 + Real.log (q : ℝ))
          ≤ 3 * (1 + ‖z‖) * (q : ℝ) * (1 + Real.log (q : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hPnn) hlognn
      have hB : 3 * (1 + ‖z‖) * (q : ℝ) * (1 + Real.log (q : ℝ))
          ≤ 3 * (1 + ‖z‖) * (q : ℝ) * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hlq (by positivity)
      have hC : 3 * (1 + ‖z‖) * (q : ℝ) * (q : ℝ)
          ≤ 3 * (Real.exp (Real.exp 100) + 5) * (q : ℝ) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP' hqnn) hqnn
      have hD : (q : ℝ) * (3 * (1 + ‖z‖) * Real.sqrt q * (1 + Real.log (q : ℝ)))
          ≤ (q : ℝ) * (3 * (Real.exp (Real.exp 100) + 5) * (q : ℝ) * (q : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hqnn
      have hE : (q : ℝ) * (3 * (Real.exp (Real.exp 100) + 5) * (q : ℝ) * (q : ℝ))
          = 3 * (q : ℝ) ^ 3 * (Real.exp (Real.exp 100) + 5) := by ring
      have hF : 3 * (q : ℝ) ^ 3 * (Real.exp (Real.exp 100) + 5) ≤ shallowGrowth q H := by
        rw [shallowGrowth]
        have hX : (0 : ℝ) ≤ (q : ℝ) ^ 3 * (Real.exp (Real.exp 100) + 5) := by positivity
        have hY : 5000 * ((q : ℝ) ^ 3 * (Real.exp (Real.exp 100) + 5)) * 1
            ≤ 5000 * ((q : ℝ) ^ 3 * (Real.exp (Real.exp 100) + 5)) * (1 + Real.log (H + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        nlinarith [hX, hY]
      linarith [hD, hE, hF]
    linarith [hlvl, hstep]

/-! ## §3 — the corrected width, the gate base, and the box's own lower bound -/

/-- **THE CORRECTED SHALLOW WIDTH.**  `vkShallowWidth` with the ball zero-count's price paid:
one extra `(log q + 1)` and one extra `log log H`.  The `(log log H)⁴` is the landed `q = 1`
twin's own exponent (`Salt.MR.zeta_pow_lower`'s cut `w = η/ℓ`); the second `(log q + 1)` is
the χ-half of the same price, the Borel–Carathéodory constant `log(4M₀) ≍ log q + log log H`. -/
def vkShallowWidthSharp (c₄ : ℝ) (q : ℕ) (H : ℝ) : ℝ :=
  c₄ / ((Real.log (q : ℝ) + 1) ^ 2 * Real.log H ^ ((3 : ℝ) / 4)
          * Real.log (Real.log H) ^ (4 : ℕ))

/-- The corrected width is BELOW the slot's stated width — the amendment only narrows the
shallow strip (it never asks the region for more than P-5's own `boxWidth` gives). -/
lemma vkShallowWidthSharp_le {c₄ : ℝ} (hc₄ : 0 < c₄) {q : ℕ} {H : ℝ}
    (hH : Real.exp (Real.exp 100) + 1 ≤ H) :
    vkShallowWidthSharp c₄ q H ≤ vkShallowWidth c₄ q H := by
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hLg : Real.exp 100 ≤ Real.log H := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLg0 : (0 : ℝ) < Real.log H := by linarith
  have hℓ : (100 : ℝ) ≤ Real.log (Real.log H) := by
    rw [← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLg
  have hR : (0 : ℝ) < Real.log H ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hLg0 _
  have hq0 : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  have hℓ3 : (0 : ℝ) < Real.log (Real.log H) ^ (3 : ℕ) := by positivity
  rw [vkShallowWidthSharp, vkShallowWidth]
  apply div_le_div_of_nonneg_left hc₄.le (by positivity)
  have h1 : (Real.log (q : ℝ) + 1) ≤ (Real.log (q : ℝ) + 1) ^ 2 := by nlinarith
  have h2 : Real.log (Real.log H) ^ (3 : ℕ) ≤ Real.log (Real.log H) ^ (4 : ℕ) := by
    have := pow_le_pow_right₀ (show (1 : ℝ) ≤ Real.log (Real.log H) by linarith)
      (show 3 ≤ 4 by norm_num)
    exact this
  calc (Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (3 : ℕ)
      ≤ (Real.log (q : ℝ) + 1) ^ 2 * Real.log H ^ ((3 : ℝ) / 4)
          * Real.log (Real.log H) ^ (3 : ℕ) := by
        apply mul_le_mul_of_nonneg_right _ hℓ3.le
        exact mul_le_mul_of_nonneg_right h1 hR.le
    _ ≤ (Real.log (q : ℝ) + 1) ^ 2 * Real.log H ^ ((3 : ℝ) / 4)
          * Real.log (Real.log H) ^ (4 : ℕ) := by
        apply mul_le_mul_of_nonneg_left h2
        positivity

/-- The canonical gate base: the smallest `A` that the collapsed two-arm gate of
`LFunction_no_zero_in_box` admits, plus the slack that makes `1 ≤ A` free. -/
def shallowA (q : ℕ) : ℝ := 1 + Real.log (20000 * (vkStripConst q + 8104)) / 100

lemma one_le_shallowA {q : ℕ} [NeZero q] : 1 ≤ shallowA q := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h1 : (1 : ℝ) ≤ 20000 * (vkStripConst q + 8104) := by rw [vkStripConst]; nlinarith
  have h2 := Real.log_nonneg h1
  rw [shallowA]; linarith

lemma shallowA_gate {q : ℕ} [NeZero q] :
    Real.log (20000 * (vkStripConst q + 8104)) ≤ 100 * shallowA q := by
  rw [shallowA]
  have h : (100 : ℝ) * (1 + Real.log (20000 * (vkStripConst q + 8104)) / 100)
      = 100 + Real.log (20000 * (vkStripConst q + 8104)) := by ring
  rw [h]
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  linarith

lemma shallowA_lb {q : ℕ} [NeZero q] : 1 + Real.log (q : ℝ) / 100 ≤ shallowA q := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h : (q : ℝ) ≤ 20000 * (vkStripConst q + 8104) := by rw [vkStripConst]; nlinarith
  have h2 := Real.log_le_log (by linarith) h
  rw [shallowA]; linarith

lemma shallowA_ub {q : ℕ} [NeZero q] : shallowA q + 7 ≤ 9 * (Real.log (q : ℝ) + 1) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have h1 : 20000 * (vkStripConst q + 8104) ≤ 2 ^ 28 * (q : ℝ) := by
    rw [vkStripConst]; nlinarith
  have h2 : Real.log (20000 * (vkStripConst q + 8104)) ≤ 28 * Real.log 2 + Real.log (q : ℝ) := by
    calc Real.log (20000 * (vkStripConst q + 8104)) ≤ Real.log (2 ^ 28 * (q : ℝ)) := by
          refine Real.log_le_log ?_ h1
          rw [vkStripConst]; nlinarith
      _ = 28 * Real.log 2 + Real.log (q : ℝ) := by
          rw [Real.log_mul (by norm_num) (by linarith), Real.log_pow]; push_cast; ring
  have h3 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [shallowA]; linarith

/-- **A clean lower bound for the corpus's own box width.**  `boxWidth` is a `min` of three
arms; this single expression sits below all three, in the shape the budget consumes.  The only
non-numeric input is `log(H+1)^{3/4} ≥ exp 75`, which is what lets the `exp 100` of the
classical arm's denominator be paid. -/
lemma boxWidth_shallow_lower {q : ℕ} [NeZero q] {c₀ H : ℝ} (hc₀pos : 0 < c₀) (hc₀1 : c₀ ≤ 1)
    (hH : Real.exp (Real.exp 100) + 1 ≤ H) :
    c₀ / (10 ^ 20 * ((Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4)
        * Real.log (Real.log (H + 1)) ^ (3 : ℕ)))
      ≤ boxWidth c₀ (shallowA q) q (H + 1) := by
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hH1pos : (0 : ℝ) < H + 1 := by linarith
  have hLg : Real.exp 100 ≤ Real.log (H + 1) := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLg0 : (0 : ℝ) < Real.log (H + 1) := by linarith
  have hℓ : (100 : ℝ) ≤ Real.log (Real.log (H + 1)) := by
    rw [← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLg
  have hR75 : Real.exp 75 ≤ Real.log (H + 1) ^ ((3 : ℝ) / 4) := by
    have h1 : Real.exp 100 ^ ((3 : ℝ) / 4) ≤ Real.log (H + 1) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (Real.exp_pos _).le hLg (by norm_num)
    rw [Real.rpow_def_of_pos (Real.exp_pos 100), Real.log_exp] at h1
    rw [show (75 : ℝ) = 100 * (3 / 4) by norm_num]
    exact h1
  have hR1 : (1 : ℝ) ≤ Real.log (H + 1) ^ ((3 : ℝ) / 4) := by
    have : (1 : ℝ) ≤ Real.exp 75 := by linarith [Real.add_one_le_exp (75 : ℝ)]
    linarith [hR75]
  have hℓ3 : (10 : ℝ) ^ 6 ≤ Real.log (Real.log (H + 1)) ^ (3 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hℓ 3
    calc (10 : ℝ) ^ 6 = (100 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ Real.log (Real.log (H + 1)) ^ (3 : ℕ) := this
  have hD0 : (0 : ℝ) < (Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4)
      * Real.log (Real.log (H + 1)) ^ (3 : ℕ) := by positivity
  have hDbig : (10 : ℝ) ^ 6 ≤ (Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4)
      * Real.log (Real.log (H + 1)) ^ (3 : ℕ) := by
    have h1 : (1 : ℝ) * 1 * ((10 : ℝ) ^ 6)
        ≤ (Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4)
            * Real.log (Real.log (H + 1)) ^ (3 : ℕ) := by
      refine mul_le_mul (mul_le_mul (by linarith) hR1 (by norm_num) (by linarith)) hℓ3
        (by norm_num) (by positivity)
    linarith
  have hden0 : (0 : ℝ) < 10 ^ 20 * ((Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4)
      * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) := by positivity
  rw [boxWidth]
  refine le_min ?_ (le_min ?_ ?_)
  · -- the `1/2` cap
    rw [div_le_iff₀ hden0]
    nlinarith [hDbig, hc₀1, hc₀pos]
  · -- the VK arm
    rw [vkBoxWidth]
    have hA7 : (0 : ℝ) < shallowA q + 7 := by linarith [one_le_shallowA (q := q)]
    have hform : (1 / (10 ^ 8 * (shallowA q + 7)))
        * (1 / (Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ)))
        = 1 / (10 ^ 8 * (shallowA q + 7)
            * (Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ))) := by
      rw [div_mul_div_comm, one_mul]
    rw [hform, div_le_div_iff₀ hden0 (by positivity)]
    have hAub := shallowA_ub (q := q)
    have hP0 : (0 : ℝ) < Real.log (H + 1) ^ ((3 : ℝ) / 4)
        * Real.log (Real.log (H + 1)) ^ (3 : ℕ) := by positivity
    -- `c₀·10^8(A+7)·P ≤ 10^20·(log q+1)·P` since `10^8·9(log q+1) ≤ 10^20(log q+1)`
    have hkey : c₀ * (10 ^ 8 * (shallowA q + 7)) ≤ 10 ^ 20 * (Real.log (q : ℝ) + 1) := by
      nlinarith [hAub, hc₀1, hc₀pos, hlogq]
    calc c₀ * (10 ^ 8 * (shallowA q + 7)
            * (Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ)))
        = (c₀ * (10 ^ 8 * (shallowA q + 7)))
            * (Real.log (H + 1) ^ ((3 : ℝ) / 4)
              * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) := by ring
      _ ≤ (10 ^ 20 * (Real.log (q : ℝ) + 1))
            * (Real.log (H + 1) ^ ((3 : ℝ) / 4)
              * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) := mul_le_mul_of_nonneg_right hkey hP0.le
      _ = 1 * (10 ^ 20 * ((Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4)
            * Real.log (Real.log (H + 1)) ^ (3 : ℕ))) := by ring
  · -- the classical arm: this is where `exp 75` pays for `exp 100`
    rw [clBoxWidth, div_le_div_iff₀ hden0 (by nlinarith [hlogq, hexp100] :
      (0 : ℝ) < Real.log (q : ℝ) + Real.exp 100 + 1)]
    -- `log q + e^100 + 1 ≤ (e^100+1)(log q+1)` and `e^100 ≤ 10^26·e^75 ≤ 10^26·P`
    have hexp25 : Real.exp 25 ≤ 10 ^ 20 := by
      have he1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have he2 : Real.exp 2 ≤ 10 := by
        have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        rw [hsq]; nlinarith [Real.exp_pos (1 : ℝ)]
      have hlog10 : (2 : ℝ) ≤ Real.log 10 := by
        rw [show (2 : ℝ) = Real.log (Real.exp 2) from (Real.log_exp 2).symm]
        exact Real.log_le_log (Real.exp_pos 2) he2
      rw [show ((10 : ℝ) ^ 20) = Real.exp (Real.log ((10 : ℝ) ^ 20)) from
        (Real.exp_log (by positivity)).symm]
      refine Real.exp_le_exp.mpr ?_
      rw [Real.log_pow]
      push_cast
      nlinarith [hlog10]
    have h100 : Real.exp 100 ≤ 10 ^ 20 * Real.exp 75 := by
      have hsplit : Real.exp 100 = Real.exp 75 * Real.exp 25 := by
        rw [← Real.exp_add]; norm_num
      rw [hsplit]
      nlinarith [Real.exp_pos (75 : ℝ), hexp25]
    have hstep1 : Real.log (q : ℝ) + Real.exp 100 + 1
        ≤ (Real.exp 100 + 1) * (Real.log (q : ℝ) + 1) := by
      nlinarith [hlogq, hexp100]
    have hstep2 : (Real.exp 100 + 1) ≤ 10 ^ 20 * Real.log (H + 1) ^ ((3 : ℝ) / 4) + 1 := by
      nlinarith [hR75, h100]
    -- assemble, with `P = (log q + 1)·log(H+1)^{3/4}` factored out
    have hP0 : (0 : ℝ) ≤ (Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4) := by
      positivity
    have hPge : Real.log (q : ℝ) + 1
        ≤ (Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4) := by
      nlinarith [hR1, hlogq]
    have hfin : (Real.log (q : ℝ) + Real.exp 100 + 1)
        ≤ 10 ^ 20 * ((Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4)
            * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) := by
      have hA : (Real.exp 100 + 1) * (Real.log (q : ℝ) + 1)
          ≤ (10 ^ 20 * Real.log (H + 1) ^ ((3 : ℝ) / 4) + 1) * (Real.log (q : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hstep2 (by linarith)
      have hstep3 : (10 ^ 20 * Real.log (H + 1) ^ ((3 : ℝ) / 4) + 1) * (Real.log (q : ℝ) + 1)
          ≤ (10 ^ 20 + 1) * ((Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4)) := by
        nlinarith [hPge, hP0]
      have hstep4 : (10 ^ 20 + 1) * ((Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4))
          ≤ 10 ^ 20 * ((Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4)
              * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) := by
        nlinarith [mul_le_mul_of_nonneg_left hℓ3 hP0, hP0]
      linarith [hstep1, hA, hstep3, hstep4]
    exact mul_le_mul_of_nonneg_left hfin hc₀pos.le

/-! ## §4 — the budget: the Borel–Carathéodory cost is `≍ (log q + log log H)`, nothing more -/

/-- **The budget's log term, bounded.**  `log(128·M/W) ≤ (e^100 + 717 + log(1/c₄))·(log q+1)·
log log H / 100`.  This is where the SHAPE of the correction is decided: the growth `M` and the
reference `W` contribute `3 log q` and `2 log q + (3/4)log log H` respectively, so the whole
Borel–Carathéodory constant is `O(log q + log log H)` — and it is that factor, multiplying the
transport length, that the corrected width has to divide out. -/
lemma log_budget_bound {q : ℕ} [NeZero q] {c₄ H : ℝ} (hc₄0 : 0 < c₄) (hc₄1 : c₄ ≤ 1)
    (hH : Real.exp (Real.exp 100) + 1 ≤ H) :
    Real.log (128 * shallowGrowth q H / vkShallowWidthSharp c₄ q H)
      ≤ (Real.exp 100 + 717 + Real.log (1 / c₄)) * (Real.log (q : ℝ) + 1)
          * Real.log (Real.log H) / 100 := by
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hHpos : (0 : ℝ) < H := by linarith
  have hLg : Real.exp 100 ≤ Real.log H := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLg0 : (0 : ℝ) < Real.log H := by linarith
  have hℓ : (100 : ℝ) ≤ Real.log (Real.log H) := by
    rw [← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLg
  have hℓ0 : (0 : ℝ) < Real.log (Real.log H) := by linarith
  -- the `H+1` scales
  have hLgp : Real.log H ≤ Real.log (H + 1) := Real.log_le_log hHpos (by linarith)
  have hLgp2 : Real.log (H + 1) ≤ 2 * Real.log H := by
    have h1 : H + 1 ≤ H * H := by nlinarith [hEbig]
    have h2 : Real.log (H + 1) ≤ Real.log (H * H) := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by linarith) (by linarith)] at h2
    linarith
  have hℓp : Real.log (Real.log (H + 1)) ≤ 2 * Real.log (Real.log H) := by
    have h1 : Real.log (Real.log (H + 1)) ≤ Real.log (2 * Real.log H) :=
      Real.log_le_log (by linarith) hLgp2
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    linarith
  -- the two log-splittings
  set Dw : ℝ := (Real.log (q : ℝ) + 1) ^ 2 * Real.log H ^ ((3 : ℝ) / 4)
    * Real.log (Real.log H) ^ (4 : ℕ) with hDwdef
  have hR0 : (0 : ℝ) < Real.log H ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hLg0 _
  have hDw0 : (0 : ℝ) < Dw := by rw [hDwdef]; positivity
  have hMpos : (0 : ℝ) < shallowGrowth q H := by
    have := one_le_shallowGrowth (q := q) (H := H) hH; linarith
  have hWeq : 128 * shallowGrowth q H / vkShallowWidthSharp c₄ q H
      = 128 * shallowGrowth q H * Dw / c₄ := by
    rw [vkShallowWidthSharp, ← hDwdef]
    field_simp
  rw [hWeq]
  rw [Real.log_div (by positivity) (ne_of_gt hc₄0)]
  have hlogc₄ : Real.log (1 / c₄) = -Real.log c₄ := by
    rw [one_div, Real.log_inv]
  -- `log(128·M·Dw) = log 128 + log M + log Dw`
  have hsplit : Real.log (128 * shallowGrowth q H * Dw)
      = Real.log 128 + Real.log (shallowGrowth q H) + Real.log Dw := by
    rw [Real.log_mul (by positivity) (ne_of_gt hDw0), Real.log_mul (by norm_num) (ne_of_gt hMpos)]
  rw [hsplit]
  -- the four pieces
  have hlog128 : Real.log 128 ≤ 5 := by
    have h1 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; push_cast; ring
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    rw [h1]; linarith
  have hlogM : Real.log (shallowGrowth q H)
      ≤ 10 + 3 * Real.log (q : ℝ) + (Real.exp 100 + 1) + (1 + 2 * Real.log (Real.log H)) := by
    rw [shallowGrowth]
    have hE0 : (0 : ℝ) < Real.exp (Real.exp 100) + 5 := by positivity
    have hL1 : (0 : ℝ) < 1 + Real.log (H + 1) := by linarith [hLgp, hLg]
    have hs1 : Real.log (5000 * (q : ℝ) ^ 3 * (Real.exp (Real.exp 100) + 5)
          * (1 + Real.log (H + 1)))
        = Real.log (5000 * (q : ℝ) ^ 3) + Real.log (Real.exp (Real.exp 100) + 5)
          + Real.log (1 + Real.log (H + 1)) := by
      rw [Real.log_mul (by positivity) (ne_of_gt hL1),
        Real.log_mul (by positivity) (ne_of_gt hE0)]
    rw [hs1]
    have h5000 : Real.log (5000 * (q : ℝ) ^ 3) ≤ 10 + 3 * Real.log (q : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      have h1 : Real.log (5000 : ℝ) ≤ 13 * Real.log 2 := by
        have h2 : Real.log (5000 : ℝ) ≤ Real.log (2 ^ 13 : ℝ) :=
          Real.log_le_log (by norm_num) (by norm_num)
        rw [Real.log_pow] at h2; push_cast at h2; linarith
      have h3 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      push_cast; linarith
    have hEterm : Real.log (Real.exp (Real.exp 100) + 5) ≤ Real.exp 100 + 1 := by
      have h1 : Real.exp (Real.exp 100) + 5 ≤ 2 * Real.exp (Real.exp 100) := by linarith
      have h2 : Real.log (Real.exp (Real.exp 100) + 5)
          ≤ Real.log (2 * Real.exp (Real.exp 100)) := Real.log_le_log (by positivity) h1
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp] at h2
      have h3 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      linarith
    have hLterm : Real.log (1 + Real.log (H + 1)) ≤ 1 + 2 * Real.log (Real.log H) := by
      have h1 : 1 + Real.log (H + 1) ≤ 2 * Real.log (H + 1) := by linarith [hLgp, hLg]
      have h2 : Real.log (1 + Real.log (H + 1)) ≤ Real.log (2 * Real.log (H + 1)) :=
        Real.log_le_log (by linarith) h1
      rw [Real.log_mul (by norm_num) (by linarith [hLgp, hLg])] at h2
      have h3 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      linarith [hℓp]
    linarith
  have hlogDw : Real.log Dw ≤ 2 * Real.log (q : ℝ) + 5 * Real.log (Real.log H) := by
    rw [hDwdef]
    have h1 : Real.log ((Real.log (q : ℝ) + 1) ^ 2 * Real.log H ^ ((3 : ℝ) / 4)
          * Real.log (Real.log H) ^ (4 : ℕ))
        = 2 * Real.log (Real.log (q : ℝ) + 1) + (3 : ℝ) / 4 * Real.log (Real.log H)
          + 4 * Real.log (Real.log (Real.log H)) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (ne_of_gt hR0), Real.log_pow, Real.log_pow,
        Real.log_rpow hLg0]
      push_cast; ring
    rw [h1]
    have h2 : Real.log (Real.log (q : ℝ) + 1) ≤ Real.log (q : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.log (q : ℝ) + 1 by linarith)
      linarith
    have h3 : Real.log (Real.log (Real.log H)) ≤ Real.log (Real.log H) := by
      have := Real.log_le_sub_one_of_pos hℓ0
      linarith
    linarith
  -- assemble
  have hSnn : (0 : ℝ) ≤ Real.log (1 / c₄) := by
    rw [hlogc₄]
    have : Real.log c₄ ≤ 0 := Real.log_nonpos (by linarith) hc₄1
    linarith
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 100)]
  -- the numeric closing: `S + 17 + 5·log q + 7·ℓ ≤ (S+717)(log q+1)·ℓ/100`
  have hint1 : (Real.exp 100 + Real.log (1 / c₄)) * 100
      ≤ (Real.exp 100 + Real.log (1 / c₄))
        * ((Real.log (q : ℝ) + 1) * Real.log (Real.log H)) := by
    have hprod : (100 : ℝ) ≤ (Real.log (q : ℝ) + 1) * Real.log (Real.log H) := by
      nlinarith [hlogq, hℓ]
    nlinarith [hprod, hSnn, hexp100]
  have hint2 : 100 * Real.log (q : ℝ) ≤ Real.log (q : ℝ) * Real.log (Real.log H) := by
    nlinarith [hlogq, hℓ]
  nlinarith [hlog128, hlogM, hlogDw, hint1, hint2, hℓ, hlogq, hSnn, hexp100, hlogc₄]

/-- The carve-out width `vkShallowWidth (10⁻⁶) q H` dominates the region's own `boxWidth` at
the canonical gate base — so the ξ₁ hypothesis stated at the former feeds §5's box discharge. -/
lemma boxWidth_le_carve {q : ℕ} [NeZero q] {c₀ H : ℝ}
    (hH : Real.exp (Real.exp 100) + 1 ≤ H) :
    boxWidth c₀ (shallowA q) q (H + 1) ≤ vkShallowWidth (1 / 10 ^ 6) q H := by
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hHpos : (0 : ℝ) < H := by linarith
  have hLg : Real.exp 100 ≤ Real.log H := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLg0 : (0 : ℝ) < Real.log H := by linarith
  have hℓ : (100 : ℝ) ≤ Real.log (Real.log H) := by
    rw [← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLg
  have hLgp : Real.log H ≤ Real.log (H + 1) := Real.log_le_log hHpos (by linarith)
  have hLgp0 : (0 : ℝ) < Real.log (H + 1) := by linarith
  have hℓp : Real.log (Real.log H) ≤ Real.log (Real.log (H + 1)) :=
    Real.log_le_log hLg0 hLgp
  have hR0 : (0 : ℝ) < Real.log H ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hLg0 _
  have hR'0 : (0 : ℝ) < Real.log (H + 1) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hLgp0 _
  have hRR' : Real.log H ^ ((3 : ℝ) / 4) ≤ Real.log (H + 1) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow hLg0.le hLgp (by norm_num)
  have hmm' : Real.log (Real.log H) ^ (3 : ℕ) ≤ Real.log (Real.log (H + 1)) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by linarith) hℓp 3
  have hA1 : 1 ≤ shallowA q := one_le_shallowA
  have hAlb : 1 + Real.log (q : ℝ) / 100 ≤ shallowA q := shallowA_lb
  refine le_trans (boxWidth_le_vk c₀ (shallowA q) q (H + 1)) ?_
  rw [vkBoxWidth, vkShallowWidth]
  have hform : (1 / (10 ^ 8 * (shallowA q + 7)))
      * (1 / (Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ)))
      = 1 / (10 ^ 8 * (shallowA q + 7)
          * (Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ))) := by
    rw [div_mul_div_comm, one_mul]
  have hℓ0 : (0 : ℝ) < Real.log (Real.log H) := by linarith
  have hℓp0 : (0 : ℝ) < Real.log (Real.log (H + 1)) := by linarith
  have hden1 : (0 : ℝ) < 10 ^ 8 * (shallowA q + 7)
      * (Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) :=
    mul_pos (mul_pos (by norm_num) (by linarith)) (mul_pos hR'0 (pow_pos hℓp0 3))
  have hden2 : (0 : ℝ) < (Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4)
      * Real.log (Real.log H) ^ (3 : ℕ) :=
    mul_pos (mul_pos (by linarith) hR0) (pow_pos hℓ0 3)
  rw [hform, div_le_div_iff₀ hden1 hden2]
  have hPq : Real.log (q : ℝ) + 1 ≤ 100 * (shallowA q + 7) := by linarith
  have hstep : (Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4)
        * Real.log (Real.log H) ^ (3 : ℕ)
      ≤ 100 * (shallowA q + 7) * (Real.log (H + 1) ^ ((3 : ℝ) / 4)
        * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) := by
    have h1 : (Real.log (q : ℝ) + 1) * (Real.log H ^ ((3 : ℝ) / 4)
          * Real.log (Real.log H) ^ (3 : ℕ))
        ≤ 100 * (shallowA q + 7) * (Real.log (H + 1) ^ ((3 : ℝ) / 4)
          * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) := by
      refine mul_le_mul hPq (mul_le_mul hRR' hmm' (by positivity) hR'0.le) (by positivity)
        (by linarith)
    calc (Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4)
          * Real.log (Real.log H) ^ (3 : ℕ)
        = (Real.log (q : ℝ) + 1) * (Real.log H ^ ((3 : ℝ) / 4)
            * Real.log (Real.log H) ^ (3 : ℕ)) := by ring
      _ ≤ _ := h1
  nlinarith [hstep, hR'0, hA1]

set_option maxHeartbeats 4000000 in
-- The assembly threads FOUR nested scale ladders (the `H` vs `H+1` log pair, the rpow `3/4`
-- factor, the region's min-of-three width and the budget's `log(4M₀)`) through one `calc` with
-- degree-6 products; the elaborator needs headroom well past the default, exactly as
-- `MobiusChiRate.LFunction_no_zero_in_box`'s own three-way height split does.
/-- **⟦THE SHALLOW SLOT, DISCHARGED⟧ — at the corrected width.**  For every `χ ≠ 1` mod `q`,
every `H ≥ exp(exp 100)+1`, every `|t| ≤ H` and every `σ ≥ 1 − vkShallowWidthSharp c₄ q H`:

  `‖L(σ+it,χ)⁻¹‖ ≤ 88 / vkShallowWidthSharp c₄ q H`.

Inputs: §1's core, §2's two geometric discharges, §3's box lower bound and §4's budget.  The
`c₄`-gate is the honest smallness condition; `exists_shallowConst` supplies a witness. -/
theorem norm_LFunction_inv_shallow_sharp {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) {c₀ c₄ H σ t : ℝ}
    (hc₀pos : 0 < c₀) (hc₀1 : c₀ ≤ 1) (hc₄0 : 0 < c₄) (hc₄1 : c₄ ≤ 1)
    (hgate4 : c₄ * (Real.exp 100 + 717 + Real.log (1 / c₄)) ≤ c₀ / 10 ^ 30)
    (hH : Real.exp (Real.exp 100) + 1 ≤ H)
    (hcl : ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re →
        (χ.primitiveCharacter ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)))
    (hcarve : ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ.im = 0 →
        ρ.re ≤ 1 - vkShallowWidth (1 / 10 ^ 6) q H)
    (ht : |t| ≤ H) (hσ : 1 - vkShallowWidthSharp c₄ q H ≤ σ) :
    ‖(LFunction χ ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ 88 / vkShallowWidthSharp c₄ q H := by
  -- the standing scales
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hHpos : (0 : ℝ) < H := by linarith
  have hLg : Real.exp 100 ≤ Real.log H := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLg0 : (0 : ℝ) < Real.log H := by linarith
  have hℓ : (100 : ℝ) ≤ Real.log (Real.log H) := by
    rw [← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLg
  have hLgp : Real.log H ≤ Real.log (H + 1) := Real.log_le_log hHpos (by linarith)
  have hLgp0 : (0 : ℝ) < Real.log (H + 1) := by linarith
  have hℓpge : Real.log (Real.log H) ≤ Real.log (Real.log (H + 1)) :=
    Real.log_le_log hLg0 hLgp
  have hLgp2 : Real.log (H + 1) ≤ 2 * Real.log H := by
    have h1 : H + 1 ≤ H * H := by nlinarith [hEbig]
    have h2 : Real.log (H + 1) ≤ Real.log (H * H) := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by linarith) (by linarith)] at h2
    linarith
  have hℓp2 : Real.log (Real.log (H + 1)) ≤ 2 * Real.log (Real.log H) := by
    have h1 : Real.log (Real.log (H + 1)) ≤ Real.log (2 * Real.log H) :=
      Real.log_le_log (by linarith) hLgp2
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    linarith
  have hR0 : (0 : ℝ) < Real.log H ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hLg0 _
  have hR'0 : (0 : ℝ) < Real.log (H + 1) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hLgp0 _
  have hR1 : (1 : ℝ) ≤ Real.log H ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hℓ0 : (0 : ℝ) < Real.log (Real.log H) := by linarith
  have hℓp0 : (0 : ℝ) < Real.log (Real.log (H + 1)) := by linarith [hℓpge]
  have hR'1 : (1 : ℝ) ≤ Real.log (H + 1) ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hRR' : Real.log (H + 1) ^ ((3 : ℝ) / 4) ≤ 2 * Real.log H ^ ((3 : ℝ) / 4) := by
    have h1 : Real.log (H + 1) ^ ((3 : ℝ) / 4) ≤ (2 * Real.log H) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hLgp0.le hLgp2 (by norm_num)
    have h2 : (2 * Real.log H) ^ ((3 : ℝ) / 4)
        = (2 : ℝ) ^ ((3 : ℝ) / 4) * Real.log H ^ ((3 : ℝ) / 4) :=
      Real.mul_rpow (by norm_num) hLg0.le
    have h3 : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (3 : ℝ) / 4 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    rw [h2] at h1
    nlinarith [h1, h3, hR0]
  -- the budget's log bound, folded before the abbreviation
  have hlogbud := log_budget_bound (q := q) (c₄ := c₄) (H := H) hc₄0 hc₄1 hH
  have hbwlow := boxWidth_shallow_lower (q := q) (c₀ := c₀) (H := H) hc₀pos hc₀1 hH
  have hbwcarve := boxWidth_le_carve (q := q) (c₀ := c₀) (H := H) hH
  set W : ℝ := vkShallowWidthSharp c₄ q H with hWdef
  set bw : ℝ := boxWidth c₀ (shallowA q) q (H + 1) with hbwdef
  have hA1 : (1 : ℝ) ≤ shallowA q := one_le_shallowA
  have hbw0 : 0 < bw := by
    rw [hbwdef]; exact boxWidth_pos hA1 hc₀pos (by linarith)
  have hbwvk : bw ≤ vkBoxWidth (shallowA q) (H + 1) := by
    rw [hbwdef]; exact boxWidth_le_vk _ _ _ _
  -- `W` is positive and tiny
  have hℓ4 : (10 : ℝ) ^ 8 ≤ Real.log (Real.log H) ^ (4 : ℕ) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hℓ 4
    calc (10 : ℝ) ^ 8 = (100 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ _ := h
  have hDw0 : (0 : ℝ) < (Real.log (q : ℝ) + 1) ^ 2 * Real.log H ^ ((3 : ℝ) / 4)
      * Real.log (Real.log H) ^ (4 : ℕ) := by positivity
  have hDwbig : (10 : ℝ) ^ 8 ≤ (Real.log (q : ℝ) + 1) ^ 2 * Real.log H ^ ((3 : ℝ) / 4)
      * Real.log (Real.log H) ^ (4 : ℕ) := by
    have h1 : (1 : ℝ) * 1 * ((10 : ℝ) ^ 8)
        ≤ (Real.log (q : ℝ) + 1) ^ 2 * Real.log H ^ ((3 : ℝ) / 4)
            * Real.log (Real.log H) ^ (4 : ℕ) := by
      refine mul_le_mul (mul_le_mul (by nlinarith) hR1 (by norm_num) (by nlinarith)) hℓ4
        (by norm_num) (by positivity)
    linarith
  have hW0 : 0 < W := by
    rw [hWdef, vkShallowWidthSharp]; positivity
  have hWsmall : W ≤ 1 / 10 ^ 8 := by
    rw [hWdef, vkShallowWidthSharp, div_le_div_iff₀ hDw0 (by norm_num)]
    nlinarith [hDwbig, hc₄1, hc₄0]
  -- THE KEY BUDGET INEQUALITY
  have hBge : (717 : ℝ) ≤ Real.exp 100 + 717 + Real.log (1 / c₄) := by
    have hS : (0 : ℝ) ≤ Real.log (1 / c₄) := by
      rw [one_div, Real.log_inv]
      have : Real.log c₄ ≤ 0 := Real.log_nonpos (by linarith) hc₄1
      linarith
    linarith [Real.exp_pos (100 : ℝ)]
  have hkey : 7.2 * (Real.exp 100 + 717 + Real.log (1 / c₄)) * (Real.log (q : ℝ) + 1)
      * Real.log (Real.log H) * W ≤ bw := by
    refine le_trans ?_ (le_trans hbwlow (le_of_eq rfl))
    rw [hWdef, vkShallowWidthSharp]
    have hform : 7.2 * (Real.exp 100 + 717 + Real.log (1 / c₄)) * (Real.log (q : ℝ) + 1)
        * Real.log (Real.log H)
        * (c₄ / ((Real.log (q : ℝ) + 1) ^ 2 * Real.log H ^ ((3 : ℝ) / 4)
            * Real.log (Real.log H) ^ (4 : ℕ)))
        = (7.2 * ((Real.exp 100 + 717 + Real.log (1 / c₄)) * c₄)
            * ((Real.log (q : ℝ) + 1) * Real.log (Real.log H)))
          / ((Real.log (q : ℝ) + 1) ^ 2 * Real.log H ^ ((3 : ℝ) / 4)
            * Real.log (Real.log H) ^ (4 : ℕ)) := by
      field_simp
    have hden3 : (0 : ℝ) < 10 ^ 20 * ((Real.log (q : ℝ) + 1)
        * Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) :=
      mul_pos (by norm_num) (mul_pos (mul_pos (by linarith) hR'0) (pow_pos hℓp0 3))
    rw [hform, div_le_div_iff₀ hDw0 hden3]
    have hgate' : (Real.exp 100 + 717 + Real.log (1 / c₄)) * c₄ ≤ c₀ / 10 ^ 30 := by
      rw [mul_comm]; exact hgate4
    have hPℓ0 : (0 : ℝ) ≤ (Real.log (q : ℝ) + 1) * Real.log (Real.log H) := by
      have : (0 : ℝ) < Real.log (q : ℝ) + 1 := by linarith
      positivity
    have hstep1 : 7.2 * ((Real.exp 100 + 717 + Real.log (1 / c₄)) * c₄)
          * ((Real.log (q : ℝ) + 1) * Real.log (Real.log H))
        ≤ 7.2 * (c₀ / 10 ^ 30) * ((Real.log (q : ℝ) + 1) * Real.log (Real.log H)) := by
      have := mul_le_mul_of_nonneg_left hgate' (by norm_num : (0 : ℝ) ≤ 7.2)
      exact mul_le_mul_of_nonneg_right this hPℓ0
    have hmm' : Real.log (Real.log (H + 1)) ^ (3 : ℕ)
        ≤ 8 * Real.log (Real.log H) ^ (3 : ℕ) := by
      have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ Real.log (Real.log (H + 1)))
        hℓp2 3
      calc Real.log (Real.log (H + 1)) ^ (3 : ℕ)
          ≤ (2 * Real.log (Real.log H)) ^ (3 : ℕ) := h
        _ = 8 * Real.log (Real.log H) ^ (3 : ℕ) := by ring
    have hprod : Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ)
        ≤ 16 * (Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (3 : ℕ)) := by
      have h := mul_le_mul hRR' hmm' (pow_pos hℓp0 3).le (by nlinarith [hR0])
      calc Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ)
          ≤ 2 * Real.log H ^ ((3 : ℝ) / 4) * (8 * Real.log (Real.log H) ^ (3 : ℕ)) := h
        _ = 16 * (Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (3 : ℕ)) := by ring
    -- the final product comparison
    calc 7.2 * ((Real.exp 100 + 717 + Real.log (1 / c₄)) * c₄)
            * ((Real.log (q : ℝ) + 1) * Real.log (Real.log H))
          * (10 ^ 20 * ((Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4)
              * Real.log (Real.log (H + 1)) ^ (3 : ℕ)))
        ≤ 7.2 * (c₀ / 10 ^ 30) * ((Real.log (q : ℝ) + 1) * Real.log (Real.log H))
          * (10 ^ 20 * ((Real.log (q : ℝ) + 1) * Real.log (H + 1) ^ ((3 : ℝ) / 4)
              * Real.log (Real.log (H + 1)) ^ (3 : ℕ))) := by
          exact mul_le_mul_of_nonneg_right hstep1 hden3.le
      _ = (7.2 / 10 ^ 10) * c₀ * ((Real.log (q : ℝ) + 1) ^ 2 * Real.log (Real.log H))
            * (Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) := by
          ring
      _ ≤ (7.2 / 10 ^ 10) * c₀ * ((Real.log (q : ℝ) + 1) ^ 2 * Real.log (Real.log H))
            * (16 * (Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (3 : ℕ))) := by
          refine mul_le_mul_of_nonneg_left hprod ?_
          have h1 : (0 : ℝ) ≤ (Real.log (q : ℝ) + 1) ^ 2 * Real.log (Real.log H) := by
            have : (0 : ℝ) ≤ (Real.log (q : ℝ) + 1) ^ 2 := sq_nonneg _
            nlinarith [hℓ0]
          nlinarith [h1, hc₀pos]
      _ = (115.2 / 10 ^ 10) * (c₀ * ((Real.log (q : ℝ) + 1) ^ 2
            * Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (4 : ℕ))) := by
          ring
      _ ≤ 1 * (c₀ * ((Real.log (q : ℝ) + 1) ^ 2 * Real.log H ^ ((3 : ℝ) / 4)
            * Real.log (Real.log H) ^ (4 : ℕ))) := by
          refine mul_le_mul_of_nonneg_right (by norm_num) ?_
          have := hDw0
          nlinarith [hDw0, hc₀pos]
      _ = c₀ * ((Real.log (q : ℝ) + 1) ^ 2 * Real.log H ^ ((3 : ℝ) / 4)
            * Real.log (Real.log H) ^ (4 : ℕ)) := by ring
  -- consequences of the key inequality
  have hWbw : W ≤ bw / 4 := by
    have h1 : (4 : ℝ) * W ≤ 7.2 * (Real.exp 100 + 717 + Real.log (1 / c₄))
        * (Real.log (q : ℝ) + 1) * Real.log (Real.log H) * W := by
      have h2 : (4 : ℝ) ≤ 7.2 * (Real.exp 100 + 717 + Real.log (1 / c₄))
          * (Real.log (q : ℝ) + 1) * Real.log (Real.log H) := by
        have hb : 7.2 * (717 : ℝ) ≤ 7.2 * (Real.exp 100 + 717 + Real.log (1 / c₄)) := by
          linarith [hBge]
        have hstep : 7.2 * (717 : ℝ) * 1 * 100
            ≤ 7.2 * (Real.exp 100 + 717 + Real.log (1 / c₄))
              * (Real.log (q : ℝ) + 1) * Real.log (Real.log H) := by
          refine mul_le_mul (mul_le_mul hb (by linarith) (by norm_num) (by linarith [hBge])) hℓ
            (by norm_num) ?_
          nlinarith [hBge, hlogq]
        linarith [hstep]
      nlinarith [h2, hW0]
    linarith [hkey, h1]
  set lam : ℝ := 2 / 3 * (bw / 2 + W) with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  have hreach : 2 * W ≤ 23 / 20 * lam := by rw [hlamdef]; nlinarith [hWbw, hbw0]
  -- the growth radius sits inside the VK strip
  have hradius : 7 / 4 * lam ≤ bw := by rw [hlamdef]; nlinarith [hWbw, hbw0]
  have hvkform : vkBoxWidth (shallowA q) (H + 1)
      = 1 / (10 ^ 8 * (shallowA q + 7)
          * (Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ))) := by
    rw [vkBoxWidth, div_mul_div_comm, one_mul]
  have hℓp100 : (100 : ℝ) ≤ Real.log (Real.log (H + 1)) := by linarith [hℓpge]
  have hℓp3 : (10 : ℝ) ^ 6 ≤ Real.log (Real.log (H + 1)) ^ (3 : ℕ) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hℓp100 3
    calc (10 : ℝ) ^ 6 = (100 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ _ := h
  have hBIG0 : (0 : ℝ) < 10 ^ 8 * (shallowA q + 7)
      * (Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) :=
    mul_pos (mul_pos (by norm_num) (by linarith)) (mul_pos hR'0 (pow_pos hℓp0 3))
  -- the multiplicative form of `bw ≤ vkBoxWidth`, from which both ceilings follow
  have hbwmul : bw * (10 ^ 8 * (shallowA q + 7)
      * (Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ))) ≤ 1 := by
    have h := le_trans hbwvk (le_of_eq hvkform)
    rwa [le_div_iff₀ hBIG0] at h
  have hbwtiny : bw ≤ 1 / 8 := by
    have hprod1 : (1 : ℝ) ≤ Real.log (H + 1) ^ ((3 : ℝ) / 4)
        * Real.log (Real.log (H + 1)) ^ (3 : ℕ) := by
      nlinarith [hR'1, hℓp3]
    have hBIGge : (8 : ℝ) ≤ 10 ^ 8 * (shallowA q + 7)
        * (Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) := by
      have h2 : (8 : ℝ) ≤ 10 ^ 8 * (shallowA q + 7) := by nlinarith [hA1]
      nlinarith [hprod1, h2]
    nlinarith [hbwmul, hBIGge, hbw0]
  have hbwΘ : bw ≤ vkTheta (H + 1) := by
    rw [vkTheta, le_div_iff₀ (mul_pos hR'0 (pow_pos hℓp0 2))]
    have hfac : (1000 : ℝ) ≤ 10 ^ 8 * (shallowA q + 7) * Real.log (Real.log (H + 1)) := by
      have h1 : (8 : ℝ) * 100 ≤ (shallowA q + 7) * Real.log (Real.log (H + 1)) :=
        mul_le_mul (by linarith) hℓp100 (by norm_num) (by linarith)
      calc (1000 : ℝ) ≤ 10 ^ 8 * ((8 : ℝ) * 100) := by norm_num
        _ ≤ 10 ^ 8 * ((shallowA q + 7) * Real.log (Real.log (H + 1))) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 10 ^ 8 * (shallowA q + 7) * Real.log (Real.log (H + 1)) := by ring
    have hXnn : (0 : ℝ) ≤ bw * (Real.log (H + 1) ^ ((3 : ℝ) / 4)
        * Real.log (Real.log (H + 1)) ^ (2 : ℕ)) :=
      mul_nonneg hbw0.le (mul_pos hR'0 (pow_pos hℓp0 2)).le
    have hXF : bw * (Real.log (H + 1) ^ ((3 : ℝ) / 4)
        * Real.log (Real.log (H + 1)) ^ (2 : ℕ)) * 1000 ≤ 1 := by
      calc bw * (Real.log (H + 1) ^ ((3 : ℝ) / 4)
              * Real.log (Real.log (H + 1)) ^ (2 : ℕ)) * 1000
          ≤ bw * (Real.log (H + 1) ^ ((3 : ℝ) / 4)
              * Real.log (Real.log (H + 1)) ^ (2 : ℕ))
            * (10 ^ 8 * (shallowA q + 7) * Real.log (Real.log (H + 1))) :=
            mul_le_mul_of_nonneg_left hfac hXnn
        _ = bw * (10 ^ 8 * (shallowA q + 7)
            * (Real.log (H + 1) ^ ((3 : ℝ) / 4)
              * Real.log (Real.log (H + 1)) ^ (3 : ℕ))) := by ring
        _ ≤ 1 := hbwmul
    linarith [hXF]
  -- the two geometric discharges
  have hgrow : ∀ z : ℂ, ‖z - (((1 + W : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ 7 / 4 * lam →
      ‖LFunction χ z‖ ≤ shallowGrowth q H := by
    intro z hz
    exact norm_LFunction_le_shallowGrowth hχ1 hH ht hW0 (by linarith [hWsmall])
      (by linarith [hradius, hbwtiny]) (by linarith [hradius, hbwΘ]) hz
  have hzf : ∀ z : ℂ, ‖z - (((1 + W : ℝ) : ℂ) + (t : ℂ) * I)‖ < 3 / 2 * lam →
      LFunction χ z ≠ 0 := by
    intro z hz
    refine LFunction_ne_zero_of_shallow_ball hχ1 hA1 hc₀pos hH ht shallowA_gate hcl ?_ hW0
      (by linarith [hWsmall]) (z := z) ?_
    · intro ρ hρ0 hρim
      exact le_trans (hcarve ρ hρ0 hρim) (by linarith [hbwcarve])
    · rw [← hbwdef]
      calc ‖z - (((1 + W : ℝ) : ℂ) + (t : ℂ) * I)‖ < 3 / 2 * lam := hz
        _ = bw / 2 + W := by rw [hlamdef]; ring
  -- the budget in the core's shape
  have hbudget : 240 * W * Real.log (4 * (32 * shallowGrowth q H / W)) ≤ lam := by
    have heq : (4 : ℝ) * (32 * shallowGrowth q H / W) = 128 * shallowGrowth q H / W := by
      ring
    rw [heq]
    have h1 : Real.log (128 * shallowGrowth q H / W)
        ≤ (Real.exp 100 + 717 + Real.log (1 / c₄)) * (Real.log (q : ℝ) + 1)
            * Real.log (Real.log H) / 100 := hlogbud
    have h2 : 240 * W * Real.log (128 * shallowGrowth q H / W)
        ≤ 240 * W * ((Real.exp 100 + 717 + Real.log (1 / c₄)) * (Real.log (q : ℝ) + 1)
            * Real.log (Real.log H) / 100) :=
      mul_le_mul_of_nonneg_left h1 (by linarith [hW0] : (0 : ℝ) ≤ 240 * W)
    have h3 : 240 * W * ((Real.exp 100 + 717 + Real.log (1 / c₄)) * (Real.log (q : ℝ) + 1)
          * Real.log (Real.log H) / 100)
        = (1 / 3) * (7.2 * (Real.exp 100 + 717 + Real.log (1 / c₄)) * (Real.log (q : ℝ) + 1)
          * Real.log (Real.log H) * W) := by ring
    rw [hlamdef]
    linarith [h2, h3, hkey, hW0]
  -- split on the two σ ranges
  rcases le_or_gt σ (1 + W) with hσhi | hσhi
  · exact norm_LFunction_inv_shallow_of_ball hχ1 hW0 (by linarith [hWsmall]) hlam0
      (one_le_shallowGrowth hH) hreach hgrow hzf hbudget (by linarith [hσ]) hσhi
  · have h1 : (1 : ℝ) < σ := by linarith [hW0]
    have hcline := norm_LFunction_inv_cline_le χ h1 t
    have h2 : (1 : ℝ) / (σ - 1) ≤ 1 / W := by
      apply one_div_le_one_div_of_le hW0
      linarith
    have h3 : (1 : ℝ) + 1 / W ≤ 88 / W := by
      rw [le_div_iff₀ hW0]
      have hexp : (1 + 1 / W) * W = W + 1 := by field_simp
      rw [hexp]
      linarith [hWsmall]
    linarith [hcline, h2, h3]

/-! ## §5 — the slot's `Prop`, at the corrected width, and its discharge -/

/-- `(x²/16)·(1 + log(16/x²)) ≤ x` for `0 < x ≤ 1` — the elementary step that makes the
`c₄`-gate satisfiable (`c·log(1/c) → 0`), with an explicit witness rather than a limit. -/
lemma sq_div_sixteen_log_le {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) :
    x ^ 2 / 16 * (1 + Real.log (1 / (x ^ 2 / 16))) ≤ x := by
  have hu : (0 : ℝ) ≤ Real.log (1 / x) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ h0]; linarith
  have hxu : x * Real.exp (Real.log (1 / x)) = 1 := by
    rw [Real.exp_log (by positivity)]; field_simp
  have hexp : Real.log (1 / x) + 1 ≤ Real.exp (Real.log (1 / x)) :=
    Real.add_one_le_exp _
  have hxu1 : x * Real.log (1 / x) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hexp h0.le]
  have hform : (1 : ℝ) / (x ^ 2 / 16) = 16 * (1 / x) ^ 2 := by
    field_simp
  rw [hform, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hlog16 : Real.log 16 ≤ 3 := by
    have h2 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
    have h3 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    rw [h2]; linarith
  push_cast
  nlinarith [hxu1, hlog16, hu, mul_nonneg (sub_nonneg.mpr h1) h0.le,
    mul_nonneg h0.le hu]

/-- The `c₄`-gate of `norm_LFunction_inv_shallow_sharp` is satisfiable for every positive
`c₀ ≤ 1`. -/
lemma exists_shallowConst {c₀ : ℝ} (h0 : 0 < c₀) (h1 : c₀ ≤ 1) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ c₄ ≤ 1 ∧
      c₄ * (Real.exp 100 + 717 + Real.log (1 / c₄)) ≤ c₀ / 10 ^ 30 := by
  have hB1 : (1 : ℝ) ≤ Real.exp 100 + 717 := by
    linarith [Real.exp_pos (100 : ℝ)]
  set x : ℝ := c₀ / 10 ^ 30 / (Real.exp 100 + 717) with hxdef
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hx1 : x ≤ 1 := by
    rw [hxdef, div_le_one (by linarith)]
    have : c₀ / 10 ^ 30 ≤ 1 := by
      rw [div_le_one (by norm_num)]; linarith
    linarith
  refine ⟨x ^ 2 / 16, by positivity, by nlinarith [hx0, hx1], ?_⟩
  have hS : (0 : ℝ) ≤ Real.log (1 / (x ^ 2 / 16)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hx0, hx1]
  have hkey := sq_div_sixteen_log_le hx0 hx1
  have hsplit : x ^ 2 / 16 * (Real.exp 100 + 717 + Real.log (1 / (x ^ 2 / 16)))
      ≤ (Real.exp 100 + 717) * (x ^ 2 / 16 * (1 + Real.log (1 / (x ^ 2 / 16)))) := by
    have hc : (0 : ℝ) ≤ x ^ 2 / 16 := by positivity
    nlinarith [hS, hB1, hc, mul_nonneg hc hS]
  have hfin : (Real.exp 100 + 717) * (x ^ 2 / 16 * (1 + Real.log (1 / (x ^ 2 / 16))))
      ≤ (Real.exp 100 + 717) * x := by
    exact mul_le_mul_of_nonneg_left hkey (by linarith)
  have hval : (Real.exp 100 + 717) * x = c₀ / 10 ^ 30 := by
    rw [hxdef]; field_simp
  linarith [hsplit, hfin, hval]

/-- **⟦THE SLOT, CORRECTED⟧** — `Salt.MR.LFunctionInvShallowVk` verbatim, with TWO changes,
both forced (see the header):

* the width is `vkShallowWidthSharp` — the stated `vkShallowWidth` is too wide by the ball's
  own Borel–Carathéodory constant `log(4M₀) ≍ log q + log log H`;
* the ξ₁ carve-out carries a MARGIN (it is stated at the region-scale width
  `vkShallowWidth (10⁻⁶) q H`, which dominates `boxWidth`): with the carve-out at the shallow
  line itself, a real zero may sit arbitrarily close to that line and NO bound of this form
  can hold.

The edge bound's SHAPE — `K·((log q+1)·log H)^m` — is unchanged, so the consumer
(`MmuChiRate_residue`'s mirror) sees the same interface. -/
def LFunctionInvShallowVkSharp : Prop :=
  ∃ (c₄ K : ℝ) (m : ℕ), 0 < c₄ ∧ 0 < K ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ H : ℝ,
      Real.exp (Real.exp 100) + 1 ≤ H →
      (∀ ρ : ℂ, LFunction χ ρ = 0 → ρ.im = 0 →
          ρ.re ≤ 1 - vkShallowWidth (1 / 10 ^ 6) q H) →
      ∀ σ t : ℝ, 1 - vkShallowWidthSharp c₄ q H ≤ σ → σ ≤ 2 → |t| ≤ H →
        ‖(LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖
          ≤ K * ((Real.log (q : ℝ) + 1) * Real.log H) ^ m

set_option maxHeartbeats 1600000 in
-- The `Prop`-level discharge re-establishes the log/rpow scale facts and then converts the
-- width into the `((log q+1)·log H)²` shape through the `ℓ⁴ ≤ 256 log H` rpow step; the two
-- together exceed the default budget.
/-- **THE DISCHARGE.**  `LFunctionInvShallowVkSharp` holds, with `m = 2`: everything is
assembled from the landed χ-VK region (`LFunction_no_zero_in_box`), the landed strip growth
(`vk_char_strip_growth` / `LFunction_norm_le_level`), the landed reference floor
(`LFunction_near_one_lower`) and the landed scaled Landau core
(`Salt.Vk.entire_norm_logDeriv_sub_sum_scaled`).  No new axioms, no `sorry`, and — in
particular — NO Jensen zero count. -/
theorem lFunctionInvShallowVkSharp_holds : LFunctionInvShallowVkSharp := by
  obtain ⟨c₀', hc₀'pos, hcl'⟩ := Salt.SW.zero_free_region_all'
  set c₀ : ℝ := min c₀' 1 with hc₀def
  have hc₀pos : 0 < c₀ := lt_min hc₀'pos zero_lt_one
  have hc₀1 : c₀ ≤ 1 := min_le_right _ _
  have hc₀le : c₀ ≤ c₀' := min_le_left _ _
  obtain ⟨c₄, hc₄0, hc₄1, hgate4⟩ := exists_shallowConst hc₀pos hc₀1
  refine ⟨c₄, 22528 / c₄, 2, hc₄0, by positivity, ?_⟩
  intro q hq χ hχ1 H hH hcarve σ t hσ _hσ2 ht
  -- the classical region at the truncated constant
  have hcl : ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re →
      (χ.primitiveCharacter ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
      ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
    intro ρ hρ0 hρre hor
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hlogpos : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
      apply Real.log_pos
      nlinarith [abs_nonneg ρ.im]
    have hmono : c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2))
        ≤ c₀' / Real.log ((q : ℝ) * (|ρ.im| + 2)) :=
      (div_le_div_iff_of_pos_right hlogpos).mpr hc₀le
    linarith [hcl' q χ hχ1 hρ0 hρre hor, hmono]
  have hmain := norm_LFunction_inv_shallow_sharp hχ1 hc₀pos hc₀1 hc₄0 hc₄1 hgate4 hH hcl
    hcarve ht hσ
  -- the output shape: `88/W ≤ (22528/c₄)·((log q+1)·log H)²`
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hLg : Real.exp 100 ≤ Real.log H := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLg0 : (0 : ℝ) < Real.log H := by linarith
  have hℓ : (100 : ℝ) ≤ Real.log (Real.log H) := by
    rw [← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLg
  have hℓ0 : (0 : ℝ) < Real.log (Real.log H) := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hR0 : (0 : ℝ) < Real.log H ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hLg0 _
  have hRle : Real.log H ^ ((3 : ℝ) / 4) ≤ Real.log H := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ Real.log H by linarith)
      (show (3 : ℝ) / 4 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  -- `ℓ⁴ ≤ 256·log H`
  have hquart : (0 : ℝ) < Real.log H ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hLg0 _
  have hlogq4 : Real.log (Real.log H ^ ((1 : ℝ) / 4)) = 1 / 4 * Real.log (Real.log H) :=
    Real.log_rpow hLg0 _
  have hℓle : Real.log (Real.log H) ≤ 4 * Real.log H ^ ((1 : ℝ) / 4) := by
    have h := Real.log_le_sub_one_of_pos hquart
    rw [hlogq4] at h
    linarith
  have hpow4 : (Real.log H ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = Real.log H := by
    rw [← Real.rpow_natCast (Real.log H ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hLg0.le]
    norm_num
  have hℓ4 : Real.log (Real.log H) ^ (4 : ℕ) ≤ 256 * Real.log H := by
    have h1 : Real.log (Real.log H) ^ (4 : ℕ) ≤ (4 * Real.log H ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) :=
      pow_le_pow_left₀ (by linarith) hℓle 4
    calc Real.log (Real.log H) ^ (4 : ℕ) ≤ (4 * Real.log H ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := h1
      _ = 256 * (Real.log H ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := by ring
      _ = 256 * Real.log H := by rw [hpow4]
  -- assemble the shape
  have hW0 : 0 < vkShallowWidthSharp c₄ q H := by
    rw [vkShallowWidthSharp]
    have h1 : (0 : ℝ) < (Real.log (q : ℝ) + 1) ^ 2 * Real.log H ^ ((3 : ℝ) / 4)
        * Real.log (Real.log H) ^ (4 : ℕ) := by positivity
    positivity
  have hshape : 88 / vkShallowWidthSharp c₄ q H
      ≤ 22528 / c₄ * ((Real.log (q : ℝ) + 1) * Real.log H) ^ 2 := by
    rw [vkShallowWidthSharp, div_div_eq_mul_div, div_le_iff₀ hc₄0]
    have hcancel : 22528 / c₄ * ((Real.log (q : ℝ) + 1) * Real.log H) ^ 2 * c₄
        = 22528 * ((Real.log (q : ℝ) + 1) * Real.log H) ^ 2 := by
      field_simp
    rw [hcancel]
    have hP2 : (0 : ℝ) ≤ (Real.log (q : ℝ) + 1) ^ 2 := sq_nonneg _
    have hstep : Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (4 : ℕ)
        ≤ 256 * (Real.log H * Real.log H) := by
      calc Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (4 : ℕ)
          ≤ Real.log H * Real.log (Real.log H) ^ (4 : ℕ) := by
            refine mul_le_mul_of_nonneg_right hRle ?_
            positivity
        _ ≤ Real.log H * (256 * Real.log H) := by
            refine mul_le_mul_of_nonneg_left hℓ4 hLg0.le
        _ = 256 * (Real.log H * Real.log H) := by ring
    have hfin : 88 * ((Real.log (q : ℝ) + 1) ^ 2
          * (Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (4 : ℕ)))
        ≤ 22528 * ((Real.log (q : ℝ) + 1) ^ 2 * (Real.log H * Real.log H)) := by
      have h1 := mul_le_mul_of_nonneg_left hstep hP2
      nlinarith [h1]
    nlinarith [hfin, hP2]
  linarith [hmain, hshape]

/-! ## §6 — the interface: what the consumer must now supply, and the STOP on the literal slot

### The carve-out composes with the residue's own fold

`MmuChiRate_residue`'s second hypothesis is the STRONG ξ₁ statement (`Re ρ < 1/2` for every
real zero of `L(·,χ⁻¹)`), which is what wave P-7's Siegel fold is built to deliver.  It implies
the margin form §5 needs, at every admissible `H` — so the amendment costs the consumer
nothing on that side either. -/

/-- The strong ξ₁ form implies §5's margin carve-out (the width is `≤ 10⁻⁶ < 1/2`). -/
lemma carve_of_half {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {H : ℝ}
    (hH : Real.exp (Real.exp 100) + 1 ≤ H)
    (hhalf : ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ.im = 0 → ρ.re < 1 / 2) :
    ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ.im = 0 →
      ρ.re ≤ 1 - vkShallowWidth (1 / 10 ^ 6) q H := by
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hLg : Real.exp 100 ≤ Real.log H := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLg0 : (0 : ℝ) < Real.log H := by linarith
  have hℓ : (100 : ℝ) ≤ Real.log (Real.log H) := by
    rw [← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLg
  have hR1 : (1 : ℝ) ≤ Real.log H ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hℓ3 : (10 : ℝ) ^ 6 ≤ Real.log (Real.log H) ^ (3 : ℕ) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hℓ 3
    calc (10 : ℝ) ^ 6 = (100 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ _ := h
  have hDen : (1 : ℝ) ≤ (Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4)
      * Real.log (Real.log H) ^ (3 : ℕ) := by
    have h1 : (1 : ℝ) * 1 * 1 ≤ (Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4)
        * Real.log (Real.log H) ^ (3 : ℕ) := by
      refine mul_le_mul (mul_le_mul (by linarith) hR1 (by norm_num) (by linarith))
        (by linarith [hℓ3]) (by norm_num) (by nlinarith [hR1, hlogq])
    linarith
  have hwidth : vkShallowWidth (1 / 10 ^ 6) q H ≤ 1 / 2 := by
    rw [vkShallowWidth, div_le_iff₀ (by linarith : (0 : ℝ) < (Real.log (q : ℝ) + 1)
      * Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (3 : ℕ))]
    nlinarith [hDen]
  intro ρ hρ0 hρim
  linarith [hhalf ρ hρ0 hρim, hwidth]

/-- **The residue after this wave.**  `MmuChiRate` now needs only (i) the ξ₁/Siegel fold — the
SAME hypothesis `MmuChiRate_residue` already carries — and (ii) the mechanical mirror of
`Salt.SW.MobiusRateClose` (contour shift + budget + de-smoothing) read at
`vkShallowWidthSharp` instead of `vkShallowWidth`.  The ANALYTIC input is landed
(`lFunctionInvShallowVkSharp_holds`); `LFunctionInvShallowVk` itself is NOT provable — see the
STOP below. -/
def MmuChiRate_residue_sharp : Prop :=
  (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ ρ : ℂ, LFunction χ⁻¹ ρ = 0 → ρ.im = 0 → ρ.re < 1 / 2) →
    MmuChiRate

/-! ### ⟦THE STOP⟧ — `LFunctionInvShallowVk` as stated is NOT provable, and here is the line

Two independent obstructions, both of which the corrected slot clears:

**(1) The width.**  Every route to a shallow lower bound for `‖L‖` transports the reference
value at `Re = 1 + W` down to `Re = 1 − W` against a derivative/Borel–Carathéodory bound on a
ball that must stay inside the zero-free region.  The ball's radius is therefore `≍ η`
(`η = boxWidth/2`, the region's own half-width) and the BC cost is `(120/λ)·log(4M₀)` per unit
length, so the loss over the transport distance `2W` is
`exp(240·W·log(4M₀)/λ) ≍ exp(C·W·log(4M₀)/η)`.  With `log(4M₀) ≍ log q + log log H` — the
growth `M = vkStripConst q·(1+log H)` contributing `log q`, the reference `W` contributing
`log(1/W) ≍ log log H` — the loss is `O(1)` **iff**

  `W ≤ η / (C·(log q + log log H))`.

`vkShallowWidth c₄ q H` is a CONSTANT multiple of `η` (both are
`≍ 1/((log q+1)(log H)^{3/4}(log log H)³)`; §3's `boxWidth_shallow_lower` pins the comparison),
so the requirement reads

  `c₄ · (log q + log log H) ≤ C′`,   `C′` absolute,

which FAILS for every `c₄ > 0` as soon as `q` or `H` grows.  **The failing inequality, in the
file's own constants:** `norm_LFunction_inv_shallow_sharp` needs
`7.2·(e^100 + 717 + log(1/c₄))·(log q + 1)·log log H · W ≤ boxWidth c₀ (shallowA q) q (H+1)`,
and at `W = vkShallowWidth c₄ q H` the left side exceeds the right by the factor
`≍ (log q + log log H)`.  The repair is `vkShallowWidthSharp` (§3): one extra `(log q+1)`, one
extra `log log H`.  It is not a defect of the route — the landed `q = 1` twin
`Salt.MR.zeta_pow_lower` pays the same price (`ℓ⁴ = ℓ³·ℓ`, its own header's "4 = 3 + 1").

**(2) The carve-out.**  `LFunctionInvShallowVk`'s ξ₁ hypothesis is
`ρ.re < 1 − vkShallowWidth c₄ q H` — strict, but with no margin.  A real zero at
`β = 1 − W − ε` satisfies it for every `ε > 0`, while `‖L((1−W)+i·0,χ)⁻¹‖ ≥ c/ε → ∞`.  So no
bound of the stated form can follow from it; the hypothesis must exclude real zeros from a
NEIGHBOURHOOD of the line.  §5 states it at the region-scale `vkShallowWidth (10⁻⁶) q H` and
`carve_of_half` shows P-7's own `Re < 1/2` fold covers that.

**What the amendment costs downstream: nothing.**  The consumer's budget (`MobiusChiRate.lean`
§6) reads the saving `exp(−W·log x)` at `T = exp((log x)^{1/10})`, `|t| ≤ x`,
`q ≤ (log x)^{12}`, `log H ≤ 2 log x`.  With the corrected width,

  `W ≍ 1/((log q+1)²(log H)^{3/4}(log log H)⁴) ≍ 1/((log x)^{3/4}(log log x)⁶)`,

so the saving is `exp(−c(log x)^{1/4}/(log log x)⁶)` in place of
`exp(−c(log x)^{1/4}/(log log x)⁴)` — still a quasi-power of `log x`, hence still
`o((log x)^{−A})` for EVERY fixed `A`, so the `∀A` form and the whole `0.29` of the `o(1)`
budget survive unchanged.  Only the finite crossover moves (P-5's III.3″ witness `L ≈ 10^{77}`
at `A_target = 5` becomes `L ≈ 10^{90}`-genre), and `MmuChiRate`'s `∃x₀` absorbs it — nothing
in the cascade reads `x₀`.

**Still open, and named:** the `χ₀`/`q = 1` row (`L(·,1)` has a pole, so §1's entire-`F`
factorization needs the `Zc` normalization plus a compact patch near `s = 1`; the slot's own
statement excludes `χ = 1`, so this is the same gap P-5 recorded, unchanged), and the
mechanical `MobiusRateClose` mirror. -/

end Salt.MR

end
