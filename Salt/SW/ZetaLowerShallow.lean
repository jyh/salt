/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
/-
# The shallow-contour ζ lower bound (`T-lo′`)

`zeta_lower_shallow` : `∃ c₄ > 0, ∃ c > 0, ∀ σ t, 2 ≤ |t| →`
`1 − c₄/log(|t|+2)⁹ ≤ σ → c/log(|t|+2)⁷ ≤ ‖ζ(σ+it)‖`.

The route (the S2 fork's numerically-verified shallow contour):

1. **Anchor** at `σ₀ = 1 + a/L⁹` (`L = log(|t|+2)`) via the multiplicative 3-4-1
   (`DirichletCharacter.norm_LFunction_product_ge_one`, mod 1 → ζ via
   `LFunction_modOne_eq`): `|ζ(σ₀)|³·|ζ(σ₀+it)|⁴·|ζ(σ₀+2it)| ≥ 1`, with the sharp
   real pole bound `|ζ(σ')| ≤ 1 + 1/(σ'−1)` (`zeta_real_upper`, valid for every
   `σ' > 1` — so the anchor also handles large σ directly) and the landed
   `zeta_log_bound` for `|ζ(σ₀+2it)| ≤ 36·log(2|t|+2) ≤ 72L`, giving
   `|ζ(σ'+it)| ≥ a^{3/4}/(2C₁·L⁷)` for all `σ' ≥ σ₀`.
2. **Derivative** via Cauchy's estimate (`norm_deriv_le_of_forall_mem_sphere_norm_le`)
   on the disk of radius `r = 1/(3L)`; the sphere-sup `≤ 2C₁L + 18` splits on
   `|t| ≥ 3` (`zeta_log_bound`, disk stays in `|Im| ≥ 2`) vs `|t| < 3` (the `Zc`
   growth bound `zeta_norm_le_zc`, a constant near the pole): `‖ζ′‖ ≤ 6C₁L² + 54L`.
3. **Transport** (additive, Titchmarsh 3.11 — transport ζ, never log ζ) via the
   complex MVT `norm_image_sub_le_of_norm_deriv_le` along the horizontal segment:
   `‖ζ(σ₀+it) − ζ(σ+it)‖ ≤ (6C₁L²+54L)·(σ₀−σ) ≤ 2b⁴P/L⁷`.
4. **Close**: `‖ζ(σ+it)‖ ≥ anchor − transport ≥ c/L⁷`.

III.3″ witness (mpmath, dps 40; `C₁ = 36` = the landed `zeta_log_bound` constant):
`P = 270`, `b = 1/77760`, `a = c₄ = b⁴ ≈ 2.7·10⁻²⁰`, `c = b³/144 ≈ 1.5·10⁻¹⁷`.
At `t = 10⁶/10⁹/10¹²` (and the delicate `t = 2`) all of: `3-4-1 ≥ 1`, the pole
bound, `zeta_log_bound`, `D ≤ |ζ(σ₀+it)|`, and `D − T ≥ c/L⁷` hold with strictly
positive margin.  Constants are free (only the log-powers `9, 7` are load-bearing);
a worse honest power would still serve.  Reuses the landed `zeta_log_bound`,
`Zc_growth`/`Zc_eq_of_ne`, `tail_psum_le`.
-/
import Salt.SW.ZetaLogBound

namespace Salt.SW

open Complex Metric Filter

/-- **The `Zc` growth bound, transferred to ζ.**  For `w ≠ 1` with `Re w > 0`,
`‖ζ(w)‖ ≤ 1/‖w−1‖ + ‖w‖·(1 + 1/Re w)`.  (The near-pole fallback used when the disk
dips below `|Im| = 2`; from `Zc_eq_of_ne` + `Zc_growth`.) -/
lemma zeta_norm_le_zc {w : ℂ} (hw1 : w ≠ 1) (hwre : 0 < w.re) :
    ‖riemannZeta w‖ ≤ 1 / ‖w - 1‖ + ‖w‖ * (1 + 1 / w.re) := by
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hnw : 0 < ‖w - 1‖ := norm_pos_iff.mpr hw1'
  have hZc : Zc w = (w - 1) * riemannZeta w := Zc_eq_of_ne hw1
  have hnorm : ‖Zc w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := by rw [hZc, norm_mul]
  have hgrow : ‖Zc w‖ ≤ 1 + ‖w - 1‖ * (‖w‖ * (1 + 1 / w.re)) := Zc_growth hwre
  rw [hnorm] at hgrow
  rw [div_add' _ _ _ (ne_of_gt hnw), le_div_iff₀ hnw]
  nlinarith [hgrow]

/-- **The sharp real ζ upper bound.**  For real `x > 1`,
`‖ζ(x)‖ ≤ 1 + 1/(x−1)` (`ζ(x) = 1 + Σ_{n≥2} n^{-x} ≤ 1 + ∫₁^∞`).  Valid for *all*
`x > 1`, so the anchor's pole factor is controlled even for large σ.  From
`zeta_eq_tsum_one_div_nat_add_one_cpow` + the landed `tail_psum_le`. -/
lemma zeta_real_upper {x : ℝ} (hx : 1 < x) :
    ‖riemannZeta (x : ℂ)‖ ≤ 1 + 1 / (x - 1) := by
  have hxc : 1 < (x : ℂ).re := by simpa using hx
  have hx0 : (0 : ℝ) < x - 1 := by linarith
  have hterm : ∀ n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 1) ^ (x : ℂ)‖ = ((n : ℝ) + 1) ^ (-x) := by
    intro n
    rw [norm_div, norm_one, show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      norm_natCast_cpow_of_pos (Nat.succ_pos n), Complex.ofReal_re]
    rw [Real.rpow_neg (by positivity)]
    push_cast
    rw [one_div]
  have hsumR : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-x)) := by
    have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (-x)) := by
      have := (Real.summable_one_div_nat_rpow (p := x)).mpr hx
      refine this.congr (fun n => ?_)
      rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
    have := (summable_nat_add_iff 1).mpr h0
    refine this.congr (fun n => ?_)
    push_cast; ring_nf
  have hsumN : Summable (fun n : ℕ => ‖(1 : ℂ) / ((n : ℂ) + 1) ^ (x : ℂ)‖) :=
    hsumR.congr (fun n => (hterm n).symm)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hxc]
  calc ‖∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (x : ℂ)‖
      ≤ ∑' n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 1) ^ (x : ℂ)‖ := norm_tsum_le_tsum_norm hsumN
    _ = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-x) := tsum_congr hterm
    _ = 1 + ∑' n : ℕ, ((n : ℝ) + 2) ^ (-x) := by
        rw [hsumR.tsum_eq_zero_add]
        congr 1
        · rw [Nat.cast_zero, zero_add, Real.one_rpow]
        · exact tsum_congr (fun n => by push_cast; ring_nf)
    _ ≤ 1 + 1 / (x - 1) := by
        have htail := tail_psum_le (σ := x - 1) hx0 (N := 1) le_rfl
        rw [Nat.cast_one, Real.one_rpow] at htail
        have hcast : (∑' n : ℕ, ((n : ℝ) + 2) ^ (-x))
            = ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-((x - 1) + 1)) := by
          refine tsum_congr (fun n => ?_)
          rw [show (-((x - 1) + 1)) = -x by ring]; push_cast; ring_nf
        rw [hcast]; linarith [htail]

/-- **The 3-4-1 anchor.**  For `σ' ≥ σ₀ = 1 + a/L⁹` (`L = log(|t|+2)`, `|t| ≥ 2`,
`0 < a ≤ 1`), the multiplicative 3-4-1 gives `‖ζ(σ'+it)‖⁴ ≥ a³/(16·C₁·L²⁸)`,
where `C₁ ≥ 1` is (an upper bound for) the `zeta_log_bound` constant.  Uniform in
`σ' ≥ σ₀` including large σ, via the sharp `zeta_real_upper` pole factor. -/
lemma zeta_anchor {t : ℝ} (ht : 2 ≤ |t|) {C₁ : ℝ} (hC₁ : 1 ≤ C₁)
    (hlog : ∀ σ s : ℝ, 1 - 1 / Real.log (|s| + 2) ≤ σ → 2 ≤ |s| →
        ‖riemannZeta ((σ : ℂ) + (s : ℂ) * I)‖ ≤ C₁ * Real.log (|s| + 2))
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {σ' : ℝ}
    (hσ' : 1 + a / Real.log (|t| + 2) ^ 9 ≤ σ') :
    a ^ 3 / (16 * C₁ * Real.log (|t| + 2) ^ 28)
      ≤ ‖riemannZeta ((σ' : ℂ) + (t : ℂ) * I)‖ ^ 4 := by
  set L := Real.log (|t| + 2) with hL
  have hLgt : (4 : ℝ) / 3 < L := by
    rw [hL]
    have h4 : Real.log 4 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by linarith)
    have h2 := Real.log_two_gt_d9
    have : (4 : ℝ) / 3 < Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; nlinarith [h2]
    linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL9 : (0 : ℝ) < L ^ 9 := by positivity
  -- σ' > 1
  have haL9 : (0 : ℝ) < a / L ^ 9 := div_pos ha hL9
  have hσ'1 : 1 < σ' := by linarith
  have hx' : (0 : ℝ) < σ' - 1 := by linarith
  -- the multiplicative 3-4-1, reduced to ζ (mod-1 character → riemannZeta)
  have h341 := DirichletCharacter.norm_LFunction_product_ge_one
    (χ := (1 : DirichletCharacter ℂ 1)) hx' t
  simp only [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq,
    ge_iff_le] at h341
  -- the `1 + ↑(σ'-1) → ↑σ'` rewrite is a common subterm of all three points, so it fires
  -- everywhere; the remaining two atomic rewrites are then non-overlapping.
  rw [show (1 : ℂ) + ((σ' - 1 : ℝ) : ℂ) = (σ' : ℂ) by push_cast; ring] at h341
  rw [show I * (t : ℂ) = (t : ℂ) * I by ring,
    show (2 : ℂ) * I * (t : ℂ) = ((2 * t : ℝ) : ℂ) * I by push_cast; ring,
    norm_mul, norm_mul, norm_pow, norm_pow] at h341
  set A := ‖riemannZeta (σ' : ℂ)‖ with hA
  set B := ‖riemannZeta ((σ' : ℂ) + (t : ℂ) * I)‖ with hB
  set G := ‖riemannZeta ((σ' : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ with hG
  have hAn : 0 ≤ A := norm_nonneg _
  have hGn : 0 ≤ G := norm_nonneg _
  have hBn : 0 ≤ B := norm_nonneg _
  -- pole factor: A ≤ 2 L⁹/a
  have hA2 : A ≤ 2 * L ^ 9 / a := by
    have hup := zeta_real_upper hσ'1
    rw [← hA] at hup
    have hinv : 1 / (σ' - 1) ≤ L ^ 9 / a := by
      rw [div_le_div_iff₀ hx' ha]
      have : a / L ^ 9 ≤ σ' - 1 := by linarith
      rw [div_le_iff₀ hL9] at this; nlinarith [this]
    have h1le : (1 : ℝ) ≤ L ^ 9 / a := by
      rw [le_div_iff₀ ha]; nlinarith [one_le_pow₀ hL1 (n := 9), ha1]
    have : (2 : ℝ) * L ^ 9 / a = L ^ 9 / a + L ^ 9 / a := by ring
    linarith [hup, hinv, h1le]
  -- log factor: G ≤ 2 C₁ L
  have hG2 : G ≤ 2 * C₁ * L := by
    have h2t : (2 : ℝ) ≤ |2 * t| := by rw [abs_mul]; simp; linarith
    have hcond : 1 - 1 / Real.log (|2 * t| + 2) ≤ σ' := by
      have hlogpos : 0 < Real.log (|2 * t| + 2) :=
        Real.log_pos (by have := abs_nonneg (2 * t); linarith)
      have : 0 < 1 / Real.log (|2 * t| + 2) := by positivity
      linarith
    have hgl := hlog σ' (2 * t) hcond h2t
    rw [← hG] at hgl
    have hloglt : Real.log (|2 * t| + 2) ≤ 2 * L := by
      rw [hL, show (2 : ℝ) * Real.log (|t| + 2) = Real.log ((|t| + 2) ^ 2) by
        rw [Real.log_pow]; push_cast; ring]
      apply Real.log_le_log (by have := abs_nonneg (2 * t); linarith)
      have h2t' : |2 * t| = 2 * |t| := by rw [abs_mul]; norm_num
      rw [h2t']; nlinarith [abs_nonneg t, ht]
    nlinarith [hgl, hloglt, hC₁, hL0]
  -- combine: 1 ≤ A³·B⁴·G, so B⁴ ≥ a³/(16 C₁ L²⁸)
  have hAG : A ^ 3 * G ≤ (2 * L ^ 9 / a) ^ 3 * (2 * C₁ * L) := by
    apply mul_le_mul (pow_le_pow_left₀ hAn hA2 3) hG2 hGn (by positivity)
  have hAGpos : 0 < (2 * L ^ 9 / a) ^ 3 * (2 * C₁ * L) := by positivity
  have hkey : 1 ≤ (2 * L ^ 9 / a) ^ 3 * (2 * C₁ * L) * B ^ 4 := by
    calc (1 : ℝ) ≤ A ^ 3 * B ^ 4 * G := h341
      _ = A ^ 3 * G * B ^ 4 := by ring
      _ ≤ (2 * L ^ 9 / a) ^ 3 * (2 * C₁ * L) * B ^ 4 := by
          apply mul_le_mul_of_nonneg_right hAG (by positivity)
  have hsimp : (2 * L ^ 9 / a) ^ 3 * (2 * C₁ * L) = 16 * C₁ * L ^ 28 / a ^ 3 := by
    field_simp; ring
  have ha3 : (0 : ℝ) < a ^ 3 := by positivity
  rw [hsimp, div_mul_eq_mul_div, le_div_iff₀ ha3, one_mul] at hkey
  rw [div_le_iff₀ (show (0 : ℝ) < 16 * C₁ * L ^ 28 by positivity)]
  linarith [hkey, mul_comm (B ^ 4) (16 * C₁ * L ^ 28)]

/-- **The Cauchy derivative bound.**  For `z` on the shallow segment (`Im z = t`,
`|z.re − 1| ≤ a/L⁹`, `0 < a ≤ 1/2`), `‖ζ′(z)‖ ≤ 6C₁L² + 54L`, via Cauchy's estimate
on the disk `‖·−z‖ = 1/(3L)`.  The sphere-sup `≤ 2C₁L + 18` splits on `|t| ≥ 3`
(disk stays in `|Im| ≥ 2`, `zeta_log_bound`) vs `|t| < 3` (the near-pole `Zc` bound). -/
lemma zeta_deriv_bound {t : ℝ} (ht : 2 ≤ |t|) {C₁ : ℝ} (hC₁ : 1 ≤ C₁)
    (hlog : ∀ σ s : ℝ, 1 - 1 / Real.log (|s| + 2) ≤ σ → 2 ≤ |s| →
        ‖riemannZeta ((σ : ℂ) + (s : ℂ) * I)‖ ≤ C₁ * Real.log (|s| + 2))
    {a : ℝ} (ha : 0 < a) (ha_small : a ≤ 1 / 2) {z : ℂ} (hzim : z.im = t)
    (hzlo : 1 - a / Real.log (|t| + 2) ^ 9 ≤ z.re)
    (hzhi : z.re ≤ 1 + a / Real.log (|t| + 2) ^ 9) :
    ‖deriv riemannZeta z‖ ≤ 6 * C₁ * Real.log (|t| + 2) ^ 2 + 54 * Real.log (|t| + 2) := by
  set L := Real.log (|t| + 2) with hL
  have hLgt : (4 : ℝ) / 3 < L := by
    rw [hL]
    have h4 : Real.log 4 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by linarith)
    have h2 := Real.log_two_gt_d9
    have : (4 : ℝ) / 3 < Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; nlinarith [h2]
    linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL9 : (0 : ℝ) < L ^ 9 := by positivity
  set r : ℝ := 1 / (3 * L) with hr_def
  have hr : (0 : ℝ) < r := by rw [hr_def]; positivity
  have hr14 : r ≤ 1 / 4 := by rw [hr_def, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- the shift `a/L⁹ ≤ 1/(6L)`
  have haL9 : a / L ^ 9 ≤ 1 / (6 * L) := by
    have h3L8 : (3 : ℝ) ≤ L ^ 8 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4 / 3) (le_of_lt hLgt) 8
      nlinarith [this]
    rw [div_le_div_iff₀ hL9 (by positivity)]
    nlinarith [h3L8, hL0, ha_small, mul_pos hL0 hL9]
  -- differentiability on the closed ball (pole `1` is far: `|w−1| ≥ |Im| ≥ 7/4`)
  have hballne : ∀ w ∈ closedBall z r, w ≠ 1 := by
    intro w hw
    rw [mem_closedBall, Complex.dist_eq] at hw
    have him : |w.im - z.im| ≤ r := (abs_im_le_norm (w - z)).trans hw
    have hrev : |z.im| - |w.im| ≤ |w.im - z.im| := by
      rw [abs_sub_comm w.im z.im]; exact abs_sub_abs_le_abs_sub z.im w.im
    have h1 : |z.im| = |t| := by rw [hzim]
    have hwim74 : 7 / 4 ≤ |w.im| := by linarith [hrev, him, h1, ht, hr14]
    intro hw1
    rw [hw1] at hwim74
    simp only [Complex.one_im, abs_zero] at hwim74
    linarith
  have hdon : DifferentiableOn ℂ riemannZeta (closedBall z r) := fun w hw =>
    (differentiableAt_riemannZeta (hballne w hw)).differentiableWithinAt
  have hdcc : DiffContOnCl ℂ riemannZeta (ball z r) :=
    ⟨hdon.mono ball_subset_closedBall, by
      rw [closure_ball z (ne_of_gt hr)]; exact hdon.continuousOn⟩
  -- the sphere-sup bound `≤ 2 C₁ L + 18`
  have hsup : ∀ w ∈ sphere z r, ‖riemannZeta w‖ ≤ 2 * C₁ * L + 18 := by
    intro w hw
    rw [mem_sphere, Complex.dist_eq] at hw
    have hre : |w.re - z.re| ≤ r := (abs_re_le_norm (w - z)).trans (le_of_eq hw)
    have him : |w.im - z.im| ≤ r := (abs_im_le_norm (w - z)).trans (le_of_eq hw)
    have hwre_lo : 1 - a / L ^ 9 - r ≤ w.re := by
      have := abs_le.mp hre; linarith [this.1, hzlo]
    have hwre_hi : w.re ≤ 1 + a / L ^ 9 + r := by
      have := abs_le.mp hre; linarith [this.2, hzhi]
    have h1im : |z.im| = |t| := by rw [hzim]
    have hrev : |z.im| - |w.im| ≤ |w.im - z.im| := by
      rw [abs_sub_comm w.im z.im]; exact abs_sub_abs_le_abs_sub z.im w.im
    have hfwd : |w.im| - |z.im| ≤ |w.im - z.im| := abs_sub_abs_le_abs_sub w.im z.im
    have hwim_lo : |t| - r ≤ |w.im| := by linarith [hrev, him, h1im]
    have hwim_hi : |w.im| ≤ |t| + r := by linarith [hfwd, him, h1im]
    have hsmall2 : a / L ^ 9 + r ≤ 1 / (2 * L) := by
      rw [hr_def]; have h6 : 1 / (6 * L) + 1 / (3 * L) = 1 / (2 * L) := by field_simp; ring
      linarith [haL9, h6]
    have hsmall : a / L ^ 9 + r ≤ 1 / 2 := by
      have h2L : 1 / (2 * L) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith [hsmall2, h2L]
    have hwre_half : 1 / 2 ≤ w.re := by linarith [hwre_lo, hsmall]
    by_cases h3 : 3 ≤ |t|
    · -- `|Im w| ≥ 2`: use `zeta_log_bound`
      have hwim2 : 2 ≤ |w.im| := by linarith [hwim_lo, hr14]
      have hloglt : Real.log (|w.im| + 2) ≤ 2 * L := by
        rw [hL, show (2 : ℝ) * Real.log (|t| + 2) = Real.log ((|t| + 2) ^ 2) by
          rw [Real.log_pow]; push_cast; ring]
        apply Real.log_le_log (by linarith [abs_nonneg w.im])
        nlinarith [hwim_hi, hr14, abs_nonneg t, ht]
      have hcond : 1 - 1 / Real.log (|w.im| + 2) ≤ w.re := by
        have hlogpos : 0 < Real.log (|w.im| + 2) := Real.log_pos (by linarith [abs_nonneg w.im])
        have hinv : 1 / (2 * L) ≤ 1 / Real.log (|w.im| + 2) :=
          one_div_le_one_div_of_le hlogpos hloglt
        linarith [hwre_lo, hinv, hsmall2]
      have hzl := hlog w.re w.im hcond hwim2
      rw [Complex.re_add_im w] at hzl
      have : ‖riemannZeta w‖ ≤ C₁ * (2 * L) :=
        hzl.trans (mul_le_mul_of_nonneg_left hloglt (by linarith))
      nlinarith [this]
    · -- `|t| < 3`: near-pole `Zc` bound (a constant `≤ 18`)
      rw [not_le] at h3
      have hwrepos : 0 < w.re := by linarith [hwre_half]
      have hw1 : w ≠ 1 := by
        intro h
        have hcontra : 7 / 4 ≤ |w.im| := by linarith [hwim_lo, hr14, ht]
        rw [h] at hcontra; simp only [Complex.one_im, abs_zero] at hcontra; linarith
      have hzc := zeta_norm_le_zc hw1 hwrepos
      have hwm1 : 7 / 4 ≤ ‖w - 1‖ := by
        have hb : |w.im - (1 : ℂ).im| ≤ ‖w - 1‖ := abs_im_le_norm (w - 1)
        simp only [Complex.one_im, sub_zero] at hb
        linarith [hwim_lo, hr14, ht, hb]
      have h1inv : 1 / ‖w - 1‖ ≤ 1 := by
        rw [div_le_one (by linarith [hwm1])]; linarith [hwm1]
      have haL6 : a / L ^ 9 ≤ 1 / 6 := by
        have : 1 / (6 * L) ≤ 1 / 6 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        linarith [haL9, this]
      have hre32 : |w.re| ≤ 3 / 2 := by
        rw [abs_of_pos hwrepos]; linarith [hwre_hi, haL6, hr14]
      have him134 : |w.im| ≤ 13 / 4 := by linarith [hwim_hi, hr14, h3]
      have hwnorm : ‖w‖ ≤ 5 := by
        have := Complex.norm_le_abs_re_add_abs_im w; linarith [hre32, him134]
      have hrecip : 1 + 1 / w.re ≤ 3 := by
        have : 1 / w.re ≤ 2 := by rw [div_le_iff₀ hwrepos]; linarith [hwre_half]
        linarith
      have hrecip0 : (0 : ℝ) ≤ 1 + 1 / w.re := by
        have := one_div_pos.mpr hwrepos; linarith
      have hprod : ‖w‖ * (1 + 1 / w.re) ≤ 5 * 3 :=
        mul_le_mul hwnorm hrecip hrecip0 (by norm_num)
      have hzw : ‖riemannZeta w‖ ≤ 1 + 5 * 3 := hzc.trans (by linarith [h1inv, hprod])
      have hCL : (0 : ℝ) ≤ 2 * C₁ * L := mul_nonneg (by linarith [hC₁]) hL0.le
      linarith [hzw, hCL]
  -- Cauchy's estimate, and `(2C₁L+18)/r = 6C₁L² + 54L`
  have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hr hdcc hsup
  have hrval : (2 * C₁ * L + 18) / r = 6 * C₁ * L ^ 2 + 54 * L := by
    rw [hr_def]; field_simp; ring
  rw [hrval] at hcauchy
  exact hcauchy

set_option maxHeartbeats 800000 in
-- The many `set` constants (`C₁, P, b, L, σ₀, s`) threaded through the final transport
-- `calc` inflate elaboration; each individual tactic is cheap, so we raise the budget.
/-- **`T-lo′` — the shallow-contour ζ lower bound.**  There is a window width `c₄ > 0`
and a constant `c > 0` with `c/log(|t|+2)⁷ ≤ ‖ζ(σ+it)‖` on the shallow strip
`1 − c₄/log(|t|+2)⁹ ≤ σ`, for all `|t| ≥ 2`.  Anchor (3-4-1) for `σ ≥ σ₀`; anchor +
additive transport for `σ < σ₀`. -/
theorem zeta_lower_shallow :
    ∃ c₄ > 0, ∃ c > 0, ∀ (σ t : ℝ), 2 ≤ |t| →
      1 - c₄ / Real.log (|t| + 2) ^ 9 ≤ σ →
        c / Real.log (|t| + 2) ^ 7 ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ := by
  obtain ⟨C, hC⟩ := zeta_log_bound
  set C₁ : ℝ := max C 1 with hC₁def
  have hC₁ : 1 ≤ C₁ := le_max_right _ _
  have hCC₁ : C ≤ C₁ := le_max_left _ _
  have hlog : ∀ σ s : ℝ, 1 - 1 / Real.log (|s| + 2) ≤ σ → 2 ≤ |s| →
      ‖riemannZeta ((σ : ℂ) + (s : ℂ) * I)‖ ≤ C₁ * Real.log (|s| + 2) := fun σ s h1 h2 =>
    (hC σ s h1 h2).trans (mul_le_mul_of_nonneg_right hCC₁
      (Real.log_nonneg (by have := abs_nonneg s; linarith)))
  set P : ℝ := 6 * C₁ + 54 with hPdef
  set b : ℝ := 1 / (8 * C₁ * P) with hbdef
  have hPpos : 0 < P := by rw [hPdef]; linarith
  have h8CP : (0 : ℝ) < 8 * C₁ * P := by positivity
  have hbpos : 0 < b := by rw [hbdef]; positivity
  have hble : b ≤ 1 / 2 := by
    rw [hbdef, div_le_div_iff₀ h8CP (by norm_num), one_mul, hPdef]; nlinarith [hC₁]
  have hbrel : 8 * C₁ * P * b = 1 := by rw [hbdef]; field_simp
  have hbrel2 : 48 * C₁ ^ 2 * b + 432 * C₁ * b = 1 := by
    have h := hbrel; rw [hPdef] at h; linear_combination h
  have ha4half : b ^ 4 ≤ 1 / 2 := le_trans (pow_le_pow_left₀ hbpos.le hble 4) (by norm_num)
  have ha4one : b ^ 4 ≤ 1 := by linarith [ha4half]
  refine ⟨b ^ 4, by positivity, b ^ 3 / (4 * C₁), by positivity, ?_⟩
  intro σ t ht hσwin
  set L : ℝ := Real.log (|t| + 2) with hL
  have hLgt : (4 : ℝ) / 3 < L := by
    rw [hL]
    have h4 : Real.log 4 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by linarith)
    have h2 := Real.log_two_gt_d9
    have : (4 : ℝ) / 3 < Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; nlinarith [h2]
    linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL7 : (0 : ℝ) < L ^ 7 := by positivity
  set σ₀ : ℝ := 1 + b ^ 4 / L ^ 9 with hσ₀def
  have hre_pt : ∀ x : ℝ, ((x : ℂ) + (t : ℂ) * I).re = x := fun x => by simp
  have him_pt : ∀ x : ℝ, ((x : ℂ) + (t : ℂ) * I).im = t := fun x => by simp
  -- the anchor lower bound `b³/(2 C₁ L⁷) ≤ ‖ζ(σ'+it)‖` for `σ' ≥ σ₀`
  have anchor_lb : ∀ σ' : ℝ, σ₀ ≤ σ' →
      b ^ 3 / (2 * C₁ * L ^ 7) ≤ ‖riemannZeta ((σ' : ℂ) + (t : ℂ) * I)‖ := by
    intro σ' hσ'
    have han := zeta_anchor ht hC₁ hlog (by positivity) ha4one
      (show 1 + b ^ 4 / Real.log (|t| + 2) ^ 9 ≤ σ' by rw [← hL, ← hσ₀def]; exact hσ')
    rw [← hL] at han
    set Z := ‖riemannZeta ((σ' : ℂ) + (t : ℂ) * I)‖ with hZ
    have hCC : C₁ ≤ C₁ ^ 4 := by
      nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ C₁ by linarith [hC₁])
        (show (0:ℝ) ≤ C₁ - 1 by linarith [hC₁])) (show (0:ℝ) ≤ C₁ ^ 2 + C₁ + 1 by positivity)]
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (norm_nonneg _) ?_
    have hLHS : (b ^ 3 / (2 * C₁ * L ^ 7)) ^ 4 = b ^ 12 / (16 * C₁ ^ 4 * L ^ 28) := by
      rw [div_pow]; congr 1 <;> ring
    have hRHS : (b ^ 4) ^ 3 / (16 * C₁ * L ^ 28) = b ^ 12 / (16 * C₁ * L ^ 28) := by
      congr 1; ring
    rw [hLHS]
    refine le_trans ?_ (hRHS ▸ han)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [hCC, pow_pos hL0 28]
  -- window bounds and the small-shift facts
  have hshift : (0 : ℝ) < b ^ 4 / L ^ 9 := by positivity
  by_cases hσσ₀ : σ₀ ≤ σ
  · -- direct anchor at σ
    refine le_trans ?_ (anchor_lb σ hσσ₀)
    rw [div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [mul_nonneg (show (0:ℝ) ≤ C₁ by linarith [hC₁]) hL7.le]
  · -- transport from σ₀ down to σ
    rw [not_le] at hσσ₀
    have han0 := anchor_lb σ₀ le_rfl
    -- the transport set (a horizontal segment) and its convexity
    set s : Set ℂ := {w : ℂ | w.im = t ∧ σ ≤ w.re ∧ w.re ≤ σ₀} with hs_def
    have hs_conv : Convex ℝ s := by
      intro x hx y hy p q hp hq hpq
      obtain ⟨hxi, hxlo, hxhi⟩ := hx
      obtain ⟨hyi, hylo, hyhi⟩ := hy
      refine ⟨?_, ?_, ?_⟩
      · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, hxi, hyi]
        linear_combination t * hpq
      · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
        nlinarith [mul_nonneg hp (by linarith [hxlo] : (0:ℝ) ≤ x.re - σ),
          mul_nonneg hq (by linarith [hylo] : (0:ℝ) ≤ y.re - σ), hpq]
      · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
        nlinarith [mul_nonneg hp (by linarith [hxhi] : (0:ℝ) ≤ σ₀ - x.re),
          mul_nonneg hq (by linarith [hyhi] : (0:ℝ) ≤ σ₀ - y.re), hpq]
    have hxmem : (σ : ℂ) + (t : ℂ) * I ∈ s :=
      ⟨him_pt σ, (hre_pt σ).ge, by rw [hre_pt σ]; exact le_of_lt hσσ₀⟩
    have hymem : (σ₀ : ℂ) + (t : ℂ) * I ∈ s :=
      ⟨him_pt σ₀, by rw [hre_pt σ₀]; exact le_of_lt hσσ₀, (hre_pt σ₀).le⟩
    have htrans := Convex.norm_image_sub_le_of_norm_deriv_le (f := riemannZeta) (s := s)
      (C := 6 * C₁ * L ^ 2 + 54 * L)
      (fun w hw => differentiableAt_riemannZeta (fun h => by
        rw [h] at hw
        have hwi : (1 : ℂ).im = t := hw.1
        simp only [Complex.one_im] at hwi; rw [← hwi] at ht; norm_num at ht))
      (fun w hw => by
        obtain ⟨hwi, hwlo, hwhi⟩ := hw
        exact zeta_deriv_bound ht hC₁ hlog (by positivity) ha4half hwi
          (by rw [← hL]; linarith [hσwin, hwlo])
          (by rw [← hL, ← hσ₀def]; linarith [hwhi]))
      hs_conv hxmem hymem
    -- simplify the transport length to `σ₀ − σ`
    have hnormdiff : ‖(σ₀ : ℂ) + (t : ℂ) * I - ((σ : ℂ) + (t : ℂ) * I)‖ = σ₀ - σ := by
      rw [show (σ₀ : ℂ) + (t : ℂ) * I - ((σ : ℂ) + (t : ℂ) * I) = ((σ₀ - σ : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [hnormdiff] at htrans
    -- reverse triangle inequality
    have hrev_tri : ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I)‖ -
        ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) - riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ := by
      have h := norm_add_le (riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) -
        riemannZeta ((σ : ℂ) + (t : ℂ) * I)) (riemannZeta ((σ : ℂ) + (t : ℂ) * I))
      rw [sub_add_cancel] at h; linarith [h]
    -- the close: `c/L⁷ ≤ b³/(2C₁L⁷) − transport`
    refine le_trans ?_ (by linarith [hrev_tri, han0, htrans] :
      b ^ 3 / (2 * C₁ * L ^ 7) - (6 * C₁ * L ^ 2 + 54 * L) * (σ₀ - σ)
        ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖)
    -- `T ≤ b³/(4 C₁ L⁷)`, hence the gap covers `c/L⁷`
    have hred : 48 * b * C₁ ^ 2 * L + 432 * b * C₁ ≤ L := by
      have h432 : (0 : ℝ) ≤ 432 * C₁ * b * (L - 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith [hC₁])) hbpos.le)
          (by linarith [hL1])
      nlinarith [hbrel2, h432]
    have hTle : (6 * C₁ * L ^ 2 + 54 * L) * (σ₀ - σ) ≤ b ^ 3 / (4 * C₁ * L ^ 7) := by
      have hσ0σ : σ₀ - σ ≤ 2 * (b ^ 4 / L ^ 9) := by rw [hσ₀def]; linarith [hσwin]
      have hfac : (0 : ℝ) ≤ 6 * C₁ * L ^ 2 + 54 * L := by positivity
      calc (6 * C₁ * L ^ 2 + 54 * L) * (σ₀ - σ)
          ≤ (6 * C₁ * L ^ 2 + 54 * L) * (2 * (b ^ 4 / L ^ 9)) :=
            mul_le_mul_of_nonneg_left hσ0σ hfac
        _ ≤ b ^ 3 / (4 * C₁ * L ^ 7) := by
            rw [show (6 * C₁ * L ^ 2 + 54 * L) * (2 * (b ^ 4 / L ^ 9))
              = ((6 * C₁ * L ^ 2 + 54 * L) * (2 * b ^ 4)) / L ^ 9 by ring,
              div_le_div_iff₀ (by positivity) (by positivity)]
            have hex : (6 * C₁ * L ^ 2 + 54 * L) * (2 * b ^ 4) * (4 * C₁ * L ^ 7)
                = (48 * b * C₁ ^ 2 * L + 432 * b * C₁) * (b ^ 3 * L ^ 8) := by ring
            have hex2 : b ^ 3 * L ^ 9 = L * (b ^ 3 * L ^ 8) := by ring
            rw [hex, hex2]
            exact mul_le_mul_of_nonneg_right hred (by positivity)
    have hgap : b ^ 3 / (4 * C₁) / L ^ 7 = b ^ 3 / (2 * C₁ * L ^ 7) - b ^ 3 / (4 * C₁ * L ^ 7) := by
      rw [div_div]; field_simp; ring
    rw [hgap]; linarith [hTle]

end Salt.SW
