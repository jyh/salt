/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HalaszPrimesChi
import Salt.MR.VkMidSharp

/-!
# WAVE P-6-EDGE — THE TWISTED EDGE (`D1`)

Stone C (`HalaszPrimesChi.lean`) pinned the port's remaining analytic leg: an upper bound for
`‖L′/L(x + iγ, ψ)‖` on the near-1-line strip inside `twisted_rect_zero_free_split`'s rectangle,
for a NONPRINCIPAL `ψ mod q`.  This file lands it.

## The route (the `ζ`-twin's, minus the pole)

The `ζ`-side twin is `shifted_edge_disc_core_gen`/`shifted_edge_price_strip`
(`HalaszPrimesCore.lean`, ~900 lines).  Three structural savings transfer from the B-probe's
finding (`VkTwistRegionProbe.lean`):

* **no `Zc`, no pole correction.**  `L(·,ψ)` is entire for `ψ ≠ 1`
  (`DirichletCharacter.differentiable_LFunction`), so the whole `Zc = (·−1)ζ` normalization —
  and with it the `1/(z−1)` corrections in every leg — disappears.  The Borel–Carathéodory core is
  run on the entire `L(·,ψ)` directly: `near_norm_logDeriv_entire_le` below is the base-function
  generalization of `Salt.MR.near_norm_logDeriv_Zc_le`, and the reference-point floor is the
  probe's twisted Möbius bound `norm_LFunction_inv_cline_le` (through `LFunction_ratio_bound`),
  not the pole's neighbourhood;
* **one disc engine for both height regimes.**  `twisted_disc_engine` takes the scale `Θ`, a
  uniform growth ceiling `M` on the BC box, the strip datum and the zero-freeness margin, and
  returns `(140/Θ)·log(20M/Θ) + (log(20M/Θ)/log(7/6))/w`.  The high-height leg feeds it
  `Θ = vkTheta(3|γ|)`, `M = vkStripConst q·(1 + log 3|γ|)` (stone A's box growth, two-sided);
  the moderate-height leg feeds it `Θ = 1/2` and the **effective** crude ceiling
  `M = 1 + q(1 + 3‖z‖)` (one term of the twisted Dirichlet series plus
  `Salt.SW.norm_LFunction_sub_partial_le` at the level bound `q`).  **`ζ`'s below-floor leg used
  the non-effective compactness bound `logDeriv_Zc_compact_bound`; the twisted side does not need
  it** — the crude partial-sum ceiling is explicit in `q` and in the floor;
* **no conjugation leg.**  `ζ`'s glue reflected negative heights through `Zc_conj`; here the box
  growth is stated two-sidedly in `|γ|` (`vk_char_box_growth_abs`), so both signs run the same
  disc.  (Reflecting would have moved `ψ` to `ψ⁻¹` and needed a second region hypothesis.)

## THE ONE HONEST NEW GATE (the deviation from stone C's pin)

The price constant is absolute **only under a `q`-scale gate**

  `hqgate : 8·log(40000·vkStripConst q) ≤ loglog(5T+1)`,  `vkStripConst q = 5000 q`,

i.e. `log q ≲ loglog(5T+1)/8`.  It is the EXACT analogue of `ζ`'s own absorption — `ζ` hides it in
the height floor `γ ≥ exp(exp(8·log(20000·K) + 1100))`, where `K` is absolute and the floor is
therefore a numeral; with `K` replaced by the `q`-dependent `vkStripConst q` the same absorption
becomes a `q`-vs-`T` gate, and it cannot be absorbed into a constant (the depth `D₄` and the price
`D₅` differ by exactly ONE `loglog`, which is precisely the budget `log q` must fit into).

This is the gate stone C's §4 docstring already predicted for the region's `A`-absorption
(`log q ≤ K·loglog(q(5T+1))`, `K ≈ 19` at the port's parameters: `12·loglog H ≤ K·loglog X`); the
edge consumes the same one.  Consequently `TwistedWindowPrice` as pinned (constants outermost, no
`q`-dependence, `hreg` the only hypothesis) is **not** dischargeable as literally stated —
`TwistedWindowPriceGated` (`§4`) is, and it is `TwistedWindowPrice`'s body plus this single gate.

## Scales and conventions (the banked traps)

* `D₄(5T+1) = (log(5T+1))^{3/4}(loglog(5T+1))⁴` is the region DEPTH (stone C's split), the shifted
  abscissa is `σ₀ = 1 − (c_vk/2)/D₄(5T+1)`, and the EDGE price is one `loglog` coarser,
  `D₅(5T+1) = (log(5T+1))^{3/4}(loglog(5T+1))⁵` — exactly as `ζ`'s `D₄` price sits above its `D₃`
  depth;
* the height floor is stone C's exact `exp(exp 100) + 1`, and the split's TWO GATES ride as
  hypotheses (instantiate, never restate);
* no `set L := …` (the `LSeries`-notation collision);
* `Cq = vkStripConst q = 5000·q` rides through symbolically; the moderate-height constant
  `twistedEdgeLowConst` is `q`-free and absolute.
-/

noncomputable section

namespace Salt.MR

open Complex Metric Set MeromorphicOn Function DirichletCharacter MeasureTheory
open Salt.SW Salt.Vk
open scoped LSeries.notation

/-! ## §1 — the base-function Borel–Carathéodory core

`near_norm_logDeriv_Zc_le` (`ZetaPowLower.lean`) with `Zc` replaced by an arbitrary entire `F` and
the centre/radius made free.  Nothing about `ζ` is used: the normalized `G = F/F(c₀)` has
`G c₀ = 1`, so `Salt.Vk.entire_norm_logDeriv_sub_sum_scaled` applies, `Salt.SW.entire_zero_count_le`
supplies the Blaschke count, and the min-distance hypothesis converts the partial-fraction sum. -/

/-- **The entire-base near-1-line log-derivative bound.**  For entire `F` with `F c₀ ≠ 0`, a
normalized sup ceiling `M₀` on the two Borel–Carathéodory spheres about `c₀` (radii `7/4·lam`,
`3/2·lam`), a point `s` with `‖s − c₀‖ ≤ (23/20)·lam` and `F s ≠ 0`, and a min-distance `w` to every
zero of `F` in `ball c₀ (3/2·lam)`:

`‖logDeriv F s‖ ≤ (120/lam)·log(4M₀) + (log(4M₀)/log(7/6))/w`.

The base-function generalization of `near_norm_logDeriv_Zc_le`; `L(·,ψ)` for `ψ ≠ 1` is entire, so
no `Zc` normalization and no pole correction appear. -/
lemma near_norm_logDeriv_entire_le {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {M₀ w lam : ℝ} {c₀ s : ℂ}
    (hlam0 : 0 < lam) (hM₀ : 1 ≤ M₀) (hw : 0 < w)
    (hFc : F c₀ ≠ 0)
    (hsc : ‖s - c₀‖ ≤ 23 / 20 * lam)
    (hFs : F s ≠ 0)
    (hsphere74 : ∀ z ∈ sphere c₀ (7 / 4 * lam), ‖F z / F c₀‖ ≤ M₀)
    (hsphere32 : ∀ z ∈ sphere c₀ (3 / 2 * lam), ‖F z / F c₀‖ ≤ M₀)
    (hdist : ∀ ρ : ℂ, F ρ = 0 → ρ ∈ ball c₀ (3 / 2 * lam) → w ≤ ‖s - ρ‖) :
    ‖logDeriv F s‖ ≤ (120 / lam) * Real.log (4 * M₀)
        + (Real.log (4 * M₀) / Real.log (7 / 6)) / w := by
  classical
  have hG_diff : Differentiable ℂ (fun z => F z / F c₀) := fun z => (hF z).div_const _
  have hGc_floor : (1 : ℝ) / 4 ≤ ‖F c₀ / F c₀‖ := by rw [div_self hFc, norm_one]; norm_num
  have hLDG : ∀ z, logDeriv (fun w => F w / F c₀) z = logDeriv F z := by
    intro z
    have hGeq : (fun w => F w / F c₀) = fun w => (F c₀)⁻¹ * F w := by funext w; ring
    rw [hGeq, logDeriv_const_mul z (F c₀)⁻¹ (inv_ne_zero hFc)]
  obtain ⟨Z, m, hh, hmemb, hana_h, hne_h, hEqOn, -, hnum⟩ :=
    entire_norm_logDeriv_sub_sum_scaled hG_diff hlam0 hM₀ hGc_floor hsphere74 hsphere32
  have hGs0 : F s / F c₀ ≠ 0 := div_ne_zero hFs hFc
  have hnum' := hnum s hsc hGs0
  rw [hLDG s] at hnum'
  -- the Blaschke count `∑_{ρ∈Z} m_ρ ≤ log(4M₀)/log(7/6)`
  have hana_univ : AnalyticOnNhd ℂ (fun z => F z / F c₀) univ :=
    hG_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hana32 : AnalyticOnNhd ℂ (fun z => F z / F c₀) (ball c₀ (3 / 2 * lam)) :=
    hana_univ.mono (subset_univ _)
  have hana_cb : AnalyticOnNhd ℂ (fun z => F z / F c₀) (closedBall c₀ (3 / 2 * lam)) :=
    hana_univ.mono (subset_univ _)
  have hloc : ∀ ρ ∈ Z,
      (divisor (fun z => F z / F c₀) (ball c₀ (3 / 2 * lam))) ρ = (m ρ : ℤ) := by
    intro ρ hρ
    have hρball := (hmemb ρ hρ).1
    have horder : analyticOrderAt (fun z => F z / F c₀) ρ = (m ρ : ℕ∞) :=
      analyticOrderAt_eq_of_factorization hana_h hne_h hEqOn hρ hρball
    rw [hana32.divisor_apply hρball, horder]; simp
  have hsupp : (Function.support
      (fun u => divisor (fun z => F z / F c₀) (ball c₀ (3 / 2 * lam)) u)) ⊆ ↑Z := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    have hρball : ρ ∈ ball c₀ (3 / 2 * lam) := by
      by_contra hn
      exact hρ (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hn)
    have hρ0 : (fun z => F z / F c₀) ρ = 0 := by
      by_contra hne0
      apply hρ
      rw [hana32.divisor_apply hρball, (hana32 ρ hρball).analyticOrderAt_eq_zero.mpr hne0]; simp
    exact (mem_zeros_of_factorization_gen hne_h hEqOn hρball hρ0).1
  have hcount : (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ Real.log (4 * M₀) / Real.log (7 / 6) := by
    have e1 : (∑ ρ ∈ Z, (m ρ : ℤ))
        = ∑ ρ ∈ Z, divisor (fun z => F z / F c₀) (ball c₀ (3 / 2 * lam)) ρ := by
      apply Finset.sum_congr rfl; intro ρ hρ; rw [hloc ρ hρ]
    have e2 : (∑ ρ ∈ Z, divisor (fun z => F z / F c₀) (ball c₀ (3 / 2 * lam)) ρ)
        = ∑ᶠ u, divisor (fun z => F z / F c₀) (ball c₀ (3 / 2 * lam)) u :=
      (finsum_eq_finsetSum_of_support_subset _ hsupp).symm
    have hdle : ∀ u : ℂ, divisor (fun z => F z / F c₀) (ball c₀ (3 / 2 * lam)) u
        ≤ divisor (fun z => F z / F c₀) (closedBall c₀ (3 / 2 * lam)) u := by
      intro u
      by_cases hu : u ∈ ball c₀ (3 / 2 * lam)
      · exact le_of_eq
          (by rw [hana32.divisor_apply hu, hana_cb.divisor_apply (ball_subset_closedBall hu)])
      · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
        exact hana_cb.divisor_nonneg u
    have hfin_ball : (Function.support
        (fun u => divisor (fun z => F z / F c₀) (ball c₀ (3 / 2 * lam)) u)).Finite :=
      divisor_ball_support_finite hana_cb.meromorphicOn
    have hfin_cb : (Function.support
        (fun u => divisor (fun z => F z / F c₀) (closedBall c₀ (3 / 2 * lam)) u)).Finite :=
      (divisor (fun z => F z / F c₀) (closedBall c₀ (3 / 2 * lam))).finiteSupport
        (isCompact_closedBall _ _)
    have hmono : ∑ᶠ u, divisor (fun z => F z / F c₀) (ball c₀ (3 / 2 * lam)) u
        ≤ ∑ᶠ u, divisor (fun z => F z / F c₀) (closedBall c₀ (3 / 2 * lam)) u :=
      finsum_le_finsum' hfin_ball hfin_cb hdle
    have hcountJ := entire_zero_count_le hG_diff hGc_floor (r := 3 / 2 * lam)
      (R := 7 / 4 * lam) (M := M₀) (by linarith [hlam0]) (by linarith [hlam0]) hM₀ hsphere74
    calc (∑ ρ ∈ Z, (m ρ : ℝ))
        = ((∑ ρ ∈ Z, (m ρ : ℤ) : ℤ) : ℝ) := by push_cast; ring
      _ = ((∑ᶠ u, divisor (fun z => F z / F c₀) (ball c₀ (3 / 2 * lam)) u : ℤ) : ℝ) := by
          rw [e1, e2]
      _ ≤ ((∑ᶠ u, divisor (fun z => F z / F c₀) (closedBall c₀ (3 / 2 * lam)) u : ℤ) : ℝ) := by
          exact_mod_cast hmono
      _ ≤ Real.log (4 * M₀) / Real.log (7 / 4 * lam / (3 / 2 * lam)) := hcountJ
      _ = Real.log (4 * M₀) / Real.log (7 / 6) := by
          rw [show (7 : ℝ) / 4 * lam / (3 / 2 * lam) = 7 / 6 by
            rw [mul_div_mul_right _ _ (ne_of_gt hlam0)]; norm_num]
  -- the min-distance sum bound
  have hdist' : ∀ ρ ∈ Z, w ≤ ‖s - ρ‖ := by
    intro ρ hρ
    have h1 := hmemb ρ hρ
    have hFρ : F ρ = 0 := (div_eq_zero_iff.mp h1.2).resolve_right hFc
    exact hdist ρ hFρ h1.1
  have hSumNorm : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) / w := by
    calc ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / w := by
          apply Finset.sum_le_sum; intro ρ hρ
          rw [norm_div, Complex.norm_natCast]
          have hd := hdist' ρ hρ
          have hdpos : 0 < ‖s - ρ‖ := lt_of_lt_of_le hw hd
          rw [div_le_div_iff₀ hdpos hw]
          nlinarith [Nat.cast_nonneg (α := ℝ) (m ρ), hd]
      _ = (∑ ρ ∈ Z, (m ρ : ℝ)) / w := by rw [Finset.sum_div]
  have h76 : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hcount' : (∑ ρ ∈ Z, (m ρ : ℝ)) / w ≤ (Real.log (4 * M₀) / Real.log (7 / 6)) / w := by
    rw [div_le_div_iff_of_pos_right hw]; exact hcount
  have hsplit : ‖logDeriv F s‖
      ≤ ‖logDeriv F s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ + ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ := by
    calc ‖logDeriv F s‖
        = ‖(logDeriv F s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ := by
          rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  linarith [hsplit, hnum', hSumNorm, hcount']

/-! ## §2 — the two growth ceilings

The BC box the engine reads is `Re z ∈ [1 − Θ, 2]`, `|Im z − γ| ≤ 3/4`.  Two suppliers:

* high heights: stone A's box growth, made two-sided in `|γ|` (the sign symmetry is free — the
  strip bound `vk_char_strip_growth` already reads `|T|`);
* moderate heights: one term of the twisted series plus `Salt.SW.norm_LFunction_sub_partial_le` at
  the crude level bound `M = q` (`norm_char_partial_sum_le`) — EFFECTIVE, unlike `ζ`'s compactness
  argument. -/

/-- **Stone A's box growth, two-sided.**  The `|γ|`-form of `vk_char_box_growth`: for a
nonprincipal `χ mod q` and `|γ| ≥ exp(exp 100) + 1`,
`‖L(z,χ)‖ ≤ vkStripConst q·(1 + log 3|γ|)` on the box `Re z ∈ [1 − vkTheta(3|γ|), 2]`,
`|Im z| ∈ [|γ| − 1, 3|γ|]` — both height signs, no conjugation. -/
lemma vk_char_box_growth_abs {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {γ : ℝ} (hγfloor : Real.exp (Real.exp 100) + 1 ≤ |γ|) :
    ∀ z : ℂ, 1 - vkTheta (3 * |γ|) ≤ z.re → z.re ≤ 2 →
      |γ| - 1 ≤ |z.im| → |z.im| ≤ 3 * |γ| →
      ‖LFunction χ z‖ ≤ vkStripConst q * (1 + Real.log (3 * |γ|)) := by
  intro z hre1 hre2 him1 him2
  have hzim : Real.exp (Real.exp 100) ≤ |z.im| := by linarith
  have hzimpos : 0 < |z.im| := lt_of_lt_of_le (Real.exp_pos _) hzim
  have hexp1 : Real.exp 1 < Real.exp (Real.exp 100) :=
    Real.exp_lt_exp.mpr (by linarith [Real.add_one_le_exp (100 : ℝ)])
  have hzime : Real.exp 1 < |z.im| := lt_of_lt_of_le hexp1 hzim
  have hθz : vkTheta (3 * |γ|) ≤ vkTheta |z.im| := vkTheta_anti hzime him2
  have hstrip : 1 - vkTheta |z.im| ≤ z.re := by linarith
  have hgrow := vk_char_strip_growth χ hχ (σ := z.re) (T := z.im) hzim hstrip hre2
  rw [Complex.re_add_im z] at hgrow
  have hlogle : Real.log |z.im| ≤ Real.log (3 * |γ|) := Real.log_le_log hzimpos him2
  have hC0 : (0 : ℝ) ≤ vkStripConst q := by
    have := one_le_vkStripConst (q := q); linarith
  calc ‖LFunction χ z‖ ≤ vkStripConst q * (1 + Real.log |z.im|) := hgrow
    _ ≤ vkStripConst q * (1 + Real.log (3 * |γ|)) := by
        apply mul_le_mul_of_nonneg_left _ hC0; linarith

/-- **The crude effective ceiling.**  For a nonprincipal `χ mod q` and `Re z ≥ 1/2`,
`‖L(z,χ)‖ ≤ 1 + q·(1 + 3‖z‖)`: the `N = 1` truncation of the twisted series
(`Salt.SW.norm_LFunction_sub_partial_le` at the level bound `M = q`, `norm_char_partial_sum_le`)
plus the single head term `χ(1)·1^{−z} = 1`.  This is the moderate-height growth the disc engine
needs BELOW the VK floor, and it is explicit in `q` — no compactness. -/
lemma LFunction_crude_growth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {z : ℂ} (hz : (1 : ℝ) / 2 ≤ z.re) :
    ‖LFunction χ z‖ ≤ 1 + (q : ℝ) * (1 + 3 * ‖z‖) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with hlt | hge
    · exact absurd (χ.level_one' (by omega)) hχ
    · exact hge
  have hq1' : 1 ≤ q := hq0
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1'
  have hzre : 0 < z.re := by linarith
  have htrunc := Salt.SW.norm_LFunction_sub_partial_le χ hχ hq2 (norm_char_partial_sum_le χ hχ)
    (s := z) hzre (N := 1) (le_refl 1)
  have hhead : (∑ n ∈ Finset.Icc 1 1, χ ((n : ℕ) : ZMod q) * (n : ℂ) ^ (-z)) = 1 := by
    rw [Finset.Icc_self, Finset.sum_singleton]
    simp
  have hN1 : ((1 : ℕ) : ℝ) ^ (-z.re) = 1 := by
    rw [Nat.cast_one, Real.one_rpow]
  rw [hhead, hN1, mul_one] at htrunc
  have hinv : (1 : ℝ) + 1 / z.re ≤ 3 := by
    have h : 1 / z.re ≤ 2 := by rw [div_le_iff₀ hzre]; linarith
    linarith
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  have hfac : (1 : ℝ) + ‖z‖ * (1 + 1 / z.re) ≤ 1 + 3 * ‖z‖ := by nlinarith [hinv, hznn]
  have hstep : (q : ℝ) * (1 + ‖z‖ * (1 + 1 / z.re)) ≤ (q : ℝ) * (1 + 3 * ‖z‖) :=
    mul_le_mul_of_nonneg_left hfac (by linarith)
  calc ‖LFunction χ z‖ ≤ ‖(1 : ℂ)‖ + ‖LFunction χ z - 1‖ := by
        have h := norm_add_le (1 : ℂ) (LFunction χ z - 1)
        simpa using h
    _ ≤ 1 + (q : ℝ) * (1 + ‖z‖ * (1 + 1 / z.re)) := by
        rw [norm_one]; linarith [htrunc]
    _ ≤ 1 + (q : ℝ) * (1 + 3 * ‖z‖) := by linarith [hstep]

/-! ## §3 — the disc engine, and the two legs -/

/-- **THE TWISTED DISC ENGINE.**  At the near-1-line centre `c₀ = (1 + Θ/2) + iγ` of scale `Θ`, a
uniform growth ceiling `M` on the Borel–Carathéodory box, the strip datum `|x − 1| ≤ w` with
`w ≤ 17Θ/35`, and a zero-freeness margin pushing every nearby zero to `Re ρ ≤ x − w`:

`‖L′/L(x + iγ, ψ)‖ ≤ (140/Θ)·log(20M/Θ) + (log(20M/Θ)/log(7/6))/w`.

Rides `near_norm_logDeriv_entire_le` (`L(·,ψ)` entire) and the probe's reference floor through
`LFunction_ratio_bound`.  **No pole term, no `Zc`, no height hypothesis** — the whole `Θ`/height
bookkeeping is delegated to the two callers. -/
lemma twisted_disc_engine {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ1 : ψ ≠ 1)
    {Θ M w x γ : ℝ} (hΘ0 : 0 < Θ) (hΘ12 : Θ ≤ 1 / 2) (hM : 1 ≤ M) (hw0 : 0 < w)
    (hgrowth : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → |z.im - γ| ≤ 3 / 4 → ‖LFunction ψ z‖ ≤ M)
    (hx : |x - 1| ≤ w) (hwΘ : w ≤ 17 * Θ / 35)
    (hzfree : ∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im - γ| ≤ 3 / 4 → ρ.re ≤ x - w) :
    ‖logDeriv (LFunction ψ) ((x : ℂ) + (γ : ℂ) * I)‖
      ≤ (140 / Θ) * Real.log (20 * M / Θ)
        + (Real.log (20 * M / Θ) / Real.log (7 / 6)) / w := by
  set lam : ℝ := 6 * Θ / 7 with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  set c₀ : ℂ := (((1 + Θ / 2 : ℝ)) : ℂ) + (γ : ℂ) * I with hc₀def
  set s : ℂ := (x : ℂ) + (γ : ℂ) * I with hsdef
  have hc₀re : c₀.re = 1 + Θ / 2 := by rw [hc₀def]; simp
  have hc₀im : c₀.im = γ := by rw [hc₀def]; simp
  have hsre : s.re = x := by rw [hsdef]; simp
  have hsim : s.im = γ := by rw [hsdef]; simp
  have hLdiff : Differentiable ℂ (LFunction ψ) := differentiable_LFunction hψ1
  have hFc : LFunction ψ c₀ ≠ 0 :=
    LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (by rw [hc₀re]; linarith)
  -- the radius cap `3Θ/2 ≤ 3/4`
  have hradcap : 3 * Θ / 2 ≤ 3 / 4 := by linarith
  -- the sphere ceiling (both radii)
  have hsph : ∀ R : ℝ, 0 ≤ R → R ≤ 3 * Θ / 2 →
      ∀ z ∈ sphere c₀ R, ‖LFunction ψ z / LFunction ψ c₀‖ ≤ 5 * M / Θ := by
    intro R hR0 hR z hz
    have hzc : ‖z - c₀‖ = R := by rw [← dist_eq_norm, ← mem_sphere]; exact hz
    have hreb : |z.re - (1 + Θ / 2)| ≤ R := by
      have h := Complex.abs_re_le_norm (z - c₀)
      rw [Complex.sub_re, hc₀re, hzc] at h; exact h
    have himb : |z.im - γ| ≤ R := by
      have h := Complex.abs_im_le_norm (z - c₀)
      rw [Complex.sub_im, hc₀im, hzc] at h; exact h
    have hre1 : 1 - Θ ≤ z.re := by have := (abs_le.mp hreb).1; linarith
    have hre2 : z.re ≤ 2 := by have := (abs_le.mp hreb).2; linarith
    have him : |z.im - γ| ≤ 3 / 4 := le_trans himb (le_trans hR hradcap)
    have hgz := hgrowth z hre1 hre2 him
    exact LFunction_ratio_bound ψ hΘ0 hΘ12 hM hgz
  have hM₀1 : (1 : ℝ) ≤ 5 * M / Θ := by
    rw [le_div_iff₀ hΘ0]; nlinarith [hM, hΘ12, hΘ0]
  have hR74 : (7 : ℝ) / 4 * lam ≤ 3 * Θ / 2 := by rw [hlamdef]; linarith
  have hR32 : (3 : ℝ) / 2 * lam ≤ 3 * Θ / 2 := by rw [hlamdef]; linarith
  have hsphere74 := hsph (7 / 4 * lam) (by positivity) hR74
  have hsphere32 := hsph (3 / 2 * lam) (by positivity) hR32
  -- the centering
  have hsc : ‖s - c₀‖ ≤ 23 / 20 * lam := by
    have hsub : s - c₀ = (((x - (1 + Θ / 2) : ℝ)) : ℂ) := by
      rw [hsdef, hc₀def]; push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs]
    have hb := abs_le.mp hx
    rw [abs_le]
    constructor
    · rw [hlamdef]; nlinarith [hb.1, hwΘ, hΘ0]
    · rw [hlamdef]; nlinarith [hb.2, hwΘ, hΘ0]
  -- the min-distance and the point's own nonvanishing
  have hdistb : ∀ ρ : ℂ, LFunction ψ ρ = 0 → ρ ∈ ball c₀ (3 / 2 * lam) → w ≤ ‖s - ρ‖ := by
    intro ρ hρ0 hρball
    rw [mem_ball, dist_eq_norm] at hρball
    have himb : |ρ.im - γ| ≤ 3 / 4 := by
      have h := Complex.abs_im_le_norm (ρ - c₀)
      rw [Complex.sub_im, hc₀im] at h
      have h2 : (3 : ℝ) / 2 * lam ≤ 3 / 4 := le_trans hR32 hradcap
      linarith [h, hρball]
    have hzf := hzfree ρ hρ0 himb
    have hre : w ≤ s.re - ρ.re := by rw [hsre]; linarith
    have h := Complex.abs_re_le_norm (s - ρ)
    rw [Complex.sub_re] at h
    linarith [h, le_abs_self (s.re - ρ.re)]
  have hFs : LFunction ψ s ≠ 0 := by
    intro h0
    have := hzfree s h0 (by rw [hsim, sub_self, abs_zero]; norm_num)
    rw [hsre] at this; linarith
  have hkey := near_norm_logDeriv_entire_le hLdiff hlam0 hM₀1 hw0 hFc hsc hFs
    hsphere74 hsphere32 hdistb
  have h120 : (120 : ℝ) / lam = 140 / Θ := by
    rw [hlamdef]; field_simp; ring
  have h4M : (4 : ℝ) * (5 * M / Θ) = 20 * M / Θ := by ring
  rw [h120, h4M] at hkey
  exact hkey

/-- The `D₄`-depth region hypothesis pushes every zero near the height `γ` past the shifted
abscissa: the `hzfree` datum the engine reads.  (Pure arithmetic; both legs share it.) -/
lemma twisted_zfree_of_margin {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q}
    {c_vk T x γ D : ℝ} (hD : 0 < D) (hγT : |γ| ≤ 5 * T)
    (hxlb : 1 - (c_vk / 2) / D ≤ x)
    (hmargin : ∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im| ≤ 5 * T + 1 → ρ.re ≤ 1 - c_vk / D) :
    ∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im - γ| ≤ 3 / 4 → ρ.re ≤ x - (c_vk / 2) / D := by
  intro ρ hρ0 him
  have hb := abs_le.mp him
  have hρim : |ρ.im| ≤ 5 * T + 1 := by
    have h1 : |ρ.im| ≤ |γ| + 3 / 4 := by
      have h := abs_sub_abs_le_abs_sub ρ.im γ
      linarith [h, le_abs_self (ρ.im - γ), neg_abs_le (ρ.im - γ), him]
    linarith [hγT]
  have hmr := hmargin ρ hρ0 hρim
  have hhalf : c_vk / D = (c_vk / 2) / D + (c_vk / 2) / D := by field_simp; ring
  linarith [hmr, hxlb, hhalf]

/-! ### The high-height leg -/

set_option maxHeartbeats 3200000 in
-- The high-height leg threads the vkTheta region numerics, the constant chase and the closing
-- D₅ assembly through one declaration; the ζ twin `shifted_edge_disc_core_gen` needs 12.8M.
/-- **THE TWISTED EDGE, high heights.**  For a nonprincipal `ψ mod q`, at a height `|γ|` above
stone C's exact floor `exp(exp 100) + 1` and inside the contour box `|γ| ≤ 5T`, on the whole
near-1-line strip `|x − 1| ≤ (c_vk/2)/D₄(5T+1)`, under the split's region conclusion and the two
scale gates:

`‖L′/L(x + iγ, ψ)‖ ≤ (10⁸ + 200/c_vk)·(log(5T+1))^{3/4}(loglog(5T+1))⁵`.

The `ζ`-twin is `shifted_edge_disc_core_gen` at the SAME realized constant `10⁸ + 200/c_vk` — one
`loglog` coarser, because the twisted DEPTH is `D₄` where `ζ`'s is `D₃`. -/
lemma twisted_edge_disc_core {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ1 : ψ ≠ 1)
    {c_vk T x γ : ℝ} (hc_vk : 0 < c_vk)
    (hγfloor : Real.exp (Real.exp 100) + 1 ≤ |γ|) (hγT : |γ| ≤ 5 * T)
    (hsc_thr : 9000 * c_vk ≤ Real.log (Real.log (5 * T + 1)))
    (hqgate : 8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)))
    (hxlb : 1 - (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) ≤ x)
    (hxub : x ≤ 1 + (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)))
    (hmargin : ∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ))) :
    ‖logDeriv (LFunction ψ) ((x : ℂ) + (γ : ℂ) * I)‖
      ≤ (10 ^ 8 + 200 / c_vk) * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ)) := by
  -- === the `(5T+1)` scales ===
  set LT : ℝ := Real.log (5 * T + 1) with hLTdef
  set ℓT : ℝ := Real.log LT with hℓTdef
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hγ2 : (2 : ℝ) ≤ |γ| := by linarith
  have hE5T : Real.exp (Real.exp 100) ≤ 5 * T + 1 := by linarith [hγfloor, hγT]
  have hLT100 : Real.exp 100 ≤ LT := by
    rw [hLTdef, ← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) hE5T
  have hLT1 : (1 : ℝ) ≤ LT := by linarith
  have hLTpos : 0 < LT := by linarith
  have hℓT100 : (100 : ℝ) ≤ ℓT := by
    rw [hℓTdef, ← Real.log_exp (100 : ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hLT100
  have hℓT1 : (1 : ℝ) ≤ ℓT := by linarith
  have hℓTpos : 0 < ℓT := by linarith
  have hLT34 : (1 : ℝ) ≤ LT ^ ((3 : ℝ) / 4) := Real.one_le_rpow hLT1 (by norm_num)
  have hLT34pos : 0 < LT ^ ((3 : ℝ) / 4) := by linarith
  set D4 : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ) with hD4def
  set D5 : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (5 : ℕ) with hD5def
  have hD4pos : 0 < D4 := by rw [hD4def]; positivity
  have hD5pos : 0 < D5 := by rw [hD5def]; positivity
  have hD4ℓT : D4 * ℓT = D5 := by rw [hD4def, hD5def]; ring
  have hD4geℓT : ℓT ≤ D4 := by
    rw [hD4def]
    have h1 : ℓT ≤ ℓT ^ (4 : ℕ) := by
      have h3 : (1 : ℝ) ≤ ℓT ^ (3 : ℕ) := one_le_pow₀ hℓT1
      nlinarith [mul_le_mul_of_nonneg_left h3 hℓTpos.le]
    nlinarith [h1, pow_nonneg hℓTpos.le 4]
  set w : ℝ := (c_vk / 2) / D4 with hwdef
  have hw0 : 0 < w := by rw [hwdef]; positivity
  -- === the height-`γ` scales ===
  set Lg : ℝ := Real.log |γ| with hLgdef
  set ℓ : ℝ := Real.log Lg with hℓdef
  have hγpos : (0 : ℝ) < |γ| := by linarith
  have hLg100 : Real.exp 100 ≤ Lg := by
    rw [hLgdef, ← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLg1 : (1 : ℝ) ≤ Lg := by linarith
  have hLgpos : 0 < Lg := by linarith
  have hℓ100 : (100 : ℝ) ≤ ℓ := by
    rw [hℓdef, ← Real.log_exp (100 : ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hLg100
  have hℓpos : 0 < ℓ := by linarith
  set L3 : ℝ := Real.log (3 * |γ|) with hL3def
  set ℓ3 : ℝ := Real.log L3 with hℓ3def
  have hlog3nn : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog3le : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
  have hL3eq : L3 = Real.log 3 + Lg := by
    rw [hL3def, hLgdef, Real.log_mul (by norm_num) (ne_of_gt hγpos)]
  have hL3lb : Lg ≤ L3 := by rw [hL3eq]; linarith
  have hL3ub : L3 ≤ 2 * Lg := by rw [hL3eq]; linarith
  have hL3pos : 0 < L3 := by linarith
  have hL31 : (1 : ℝ) ≤ L3 := by linarith
  have hℓ3lb : ℓ ≤ ℓ3 := by rw [hℓ3def, hℓdef]; exact Real.log_le_log hLgpos hL3lb
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hℓ3ub : ℓ3 ≤ 2 * ℓ := by
    rw [hℓ3def]
    calc Real.log L3 ≤ Real.log (2 * Lg) := Real.log_le_log hL3pos hL3ub
      _ = Real.log 2 + ℓ := by rw [Real.log_mul (by norm_num) (ne_of_gt hLgpos), ← hℓdef]
      _ ≤ 2 * ℓ := by linarith
  have hℓ3pos : 0 < ℓ3 := by linarith
  -- monotonicity to the `(5T+1)` scale
  have hLgLT : Lg ≤ LT := by
    rw [hLgdef, hLTdef]; exact Real.log_le_log hγpos (by linarith)
  have hℓℓT : ℓ ≤ ℓT := by rw [hℓdef, hℓTdef]; exact Real.log_le_log hLgpos hLgLT
  have hTpos : 0 < T := by linarith
  have hL3_2LT : L3 ≤ 2 * LT := by
    have h1 : (3 : ℝ) * |γ| ≤ (5 * T + 1) ^ 2 := by
      nlinarith [hγT, hTpos, sq_nonneg (5 * T - 1)]
    calc L3 ≤ Real.log ((5 * T + 1) ^ 2) := by
          rw [hL3def]; exact Real.log_le_log (by positivity) h1
      _ = 2 * LT := by rw [Real.log_pow, ← hLTdef]; push_cast; ring
  have hℓ3_2ℓT : ℓ3 ≤ 2 * ℓT := by
    rw [hℓ3def]
    calc Real.log L3 ≤ Real.log (2 * LT) := Real.log_le_log hL3pos hL3_2LT
      _ = Real.log 2 + ℓT := by rw [Real.log_mul (by norm_num) (ne_of_gt hLTpos), ← hℓTdef]
      _ ≤ 2 * ℓT := by linarith
  -- === the region parameters ===
  set Θ : ℝ := vkTheta (3 * |γ|) with hΘdef
  set Pinv : ℝ := 1000 * L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ) with hPinvdef
  have hL334pos : 0 < L3 ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL3pos _
  have hPinvpos : 0 < Pinv := by rw [hPinvdef]; positivity
  have hΘPinv : Θ = 1 / Pinv := by
    rw [eq_div_iff (ne_of_gt hPinvpos), hΘdef, vkTheta, ← hL3def, ← hℓ3def, hPinvdef]
    field_simp [ne_of_gt hL334pos, ne_of_gt hℓ3pos]
  have hΘ0 : 0 < Θ := by rw [hΘPinv]; positivity
  have hPinv2 : (2 : ℝ) ≤ Pinv := by
    rw [hPinvdef]
    have h1 : (1 : ℝ) ≤ L3 ^ ((3 : ℝ) / 4) := Real.one_le_rpow hL31 (by norm_num)
    have h2 : (1 : ℝ) ≤ ℓ3 ^ (2 : ℕ) := one_le_pow₀ (by linarith)
    nlinarith [h1, h2]
  have hΘ12 : Θ ≤ 1 / 2 := by
    rw [hΘPinv, div_le_div_iff₀ hPinvpos (by norm_num)]; linarith
  have hPinv5 : Pinv ≤ 8000 * (LT ^ ((3 : ℝ) / 4) * ℓT ^ (2 : ℕ)) := by
    have hL34 : L3 ^ ((3 : ℝ) / 4) ≤ 2 * LT ^ ((3 : ℝ) / 4) := by
      calc L3 ^ ((3 : ℝ) / 4) ≤ (2 * LT) ^ ((3 : ℝ) / 4) :=
            Real.rpow_le_rpow hL3pos.le hL3_2LT (by norm_num)
        _ = 2 ^ ((3 : ℝ) / 4) * LT ^ ((3 : ℝ) / 4) := Real.mul_rpow (by norm_num) hLTpos.le
        _ ≤ 2 * LT ^ ((3 : ℝ) / 4) := by
            have h2 : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
              calc (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one 2
            nlinarith [h2, Real.rpow_nonneg hLTpos.le ((3 : ℝ) / 4)]
    have hℓ3sq : ℓ3 ^ (2 : ℕ) ≤ 4 * ℓT ^ (2 : ℕ) := by
      calc ℓ3 ^ (2 : ℕ) ≤ (2 * ℓT) ^ (2 : ℕ) := pow_le_pow_left₀ hℓ3pos.le hℓ3_2ℓT 2
        _ = 4 * ℓT ^ (2 : ℕ) := by ring
    calc Pinv = 1000 * (L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ)) := by rw [hPinvdef]; ring
      _ ≤ 1000 * ((2 * LT ^ ((3 : ℝ) / 4)) * (4 * ℓT ^ (2 : ℕ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hL34 hℓ3sq (by positivity) (by positivity)
      _ = 8000 * (LT ^ ((3 : ℝ) / 4) * ℓT ^ (2 : ℕ)) := by ring
  -- === the growth ceiling ===
  set Cq : ℝ := vkStripConst q with hCqdef
  have hCq1 : (1 : ℝ) ≤ Cq := by rw [hCqdef]; exact one_le_vkStripConst
  set M : ℝ := Cq * (1 + L3) with hMdef
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; nlinarith [hCq1, hL31]
  have hgrowth : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → |z.im - γ| ≤ 3 / 4 →
      ‖LFunction ψ z‖ ≤ M := by
    intro z hre1 hre2 him
    have hb := abs_le.mp him
    have h1 : |γ| - 1 ≤ |z.im| := by
      have h := abs_sub_abs_le_abs_sub γ z.im
      have h2 : |γ - z.im| = |z.im - γ| := abs_sub_comm γ z.im
      linarith [h, h2, him]
    have h2 : |z.im| ≤ 3 * |γ| := by
      have h := abs_sub_abs_le_abs_sub z.im γ
      linarith [h, him, hγ2]
    have hgz := vk_char_box_growth_abs ψ hψ1 hγfloor z hre1 hre2 h1 h2
    rw [hMdef, hCqdef, hL3def]; exact hgz
  -- === the constant chase: `w ≤ 17Θ/35` ===
  have hwPinv : w * Pinv ≤ 17 / 35 := by
    have hkey : w * Pinv ≤ 4000 * c_vk / ℓT ^ (2 : ℕ) := by
      have h1 : w * Pinv ≤ w * (8000 * (LT ^ ((3 : ℝ) / 4) * ℓT ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hPinv5 hw0.le
      have h2 : w * (8000 * (LT ^ ((3 : ℝ) / 4) * ℓT ^ (2 : ℕ))) = 4000 * c_vk / ℓT ^ (2 : ℕ) := by
        rw [hwdef, hD4def]
        have hA : LT ^ ((3 : ℝ) / 4) ≠ 0 := ne_of_gt hLT34pos
        have hB : ℓT ≠ 0 := ne_of_gt hℓTpos
        field_simp
        ring
      linarith [h1, h2]
    have hℓTsq : (0 : ℝ) < ℓT ^ (2 : ℕ) := by positivity
    have hstep : 4000 * c_vk / ℓT ^ (2 : ℕ) ≤ 17 / 35 := by
      rw [div_le_div_iff₀ hℓTsq (by norm_num : (0 : ℝ) < 35)]
      have hsq : ℓT ^ (2 : ℕ) = ℓT * ℓT := by ring
      nlinarith [hsc_thr, hℓT100, hc_vk, hsq]
    linarith [hkey, hstep]
  have hwΘ : w ≤ 17 * Θ / 35 := by
    rw [hΘPinv, show (17 : ℝ) * (1 / Pinv) / 35 = 17 / (35 * Pinv) by field_simp,
      le_div_iff₀ (by positivity)]
    nlinarith [hwPinv, hPinvpos]
  -- === the strip datum and the margin ===
  have hx : |x - 1| ≤ w := by
    rw [abs_le]; constructor <;> linarith [hxlb, hxub]
  have hxlb' : 1 - (c_vk / 2) / D4 ≤ x := by rw [← hwdef]; exact hxlb
  have hzfree : ∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im - γ| ≤ 3 / 4 → ρ.re ≤ x - w := by
    intro ρ hρ0 him
    have h := twisted_zfree_of_margin (D := D4) hD4pos hγT hxlb' hmargin ρ hρ0 him
    rw [hwdef]; exact h
  -- === run the engine ===
  have hkey := twisted_disc_engine ψ hψ1 hΘ0 hΘ12 hM1 hw0 hgrowth hx hwΘ hzfree
  -- === the price ===
  set W : ℝ := Real.log (20 * M / Θ) with hWdef
  have h140 : (140 : ℝ) / Θ = 140 * Pinv := by rw [hΘPinv]; field_simp
  have h20M : (20 : ℝ) * M / Θ = 20 * Pinv * M := by rw [hΘPinv]; field_simp
  rw [h140] at hkey
  -- `W ≤ 8·ℓT`
  have hWub : W ≤ 8 * ℓT := by
    have hbig : 20 * Pinv * M ≤ 40000 * Cq * L3 ^ ((7 : ℝ) / 4) * ℓ3 ^ (2 : ℕ) := by
      have hL374 : L3 ^ ((3 : ℝ) / 4) * L3 = L3 ^ ((7 : ℝ) / 4) := by
        rw [show (7 : ℝ) / 4 = (3 : ℝ) / 4 + 1 by norm_num, Real.rpow_add hL3pos,
          Real.rpow_one]
      have h1L3 : (1 : ℝ) + L3 ≤ 2 * L3 := by linarith
      calc 20 * Pinv * M
          = 20000 * (L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ)) * (Cq * (1 + L3)) := by
            rw [hPinvdef, hMdef]; ring
        _ ≤ 20000 * (L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ)) * (Cq * (2 * L3)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left h1L3 (by linarith)
        _ = 40000 * Cq * (L3 ^ ((3 : ℝ) / 4) * L3) * ℓ3 ^ (2 : ℕ) := by ring
        _ = 40000 * Cq * L3 ^ ((7 : ℝ) / 4) * ℓ3 ^ (2 : ℕ) := by rw [hL374]
    have hlogeq : Real.log (40000 * Cq * L3 ^ ((7 : ℝ) / 4) * ℓ3 ^ (2 : ℕ))
        = Real.log (40000 * Cq) + (7 / 4) * ℓ3 + 2 * Real.log ℓ3 := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_rpow hL3pos, Real.log_pow,
        ← hℓ3def]
      push_cast; ring
    have hlogmono : W ≤ Real.log (40000 * Cq * L3 ^ ((7 : ℝ) / 4) * ℓ3 ^ (2 : ℕ)) := by
      rw [hWdef, h20M]
      exact Real.log_le_log (by positivity) hbig
    have hlogℓ3 : Real.log ℓ3 ≤ ℓ3 := by
      linarith [Real.log_le_sub_one_of_pos hℓ3pos]
    have hgate' : Real.log (40000 * Cq) ≤ ℓT / 8 := by
      rw [hCqdef]; linarith [hqgate]
    linarith [hlogmono, hlogeq, hlogℓ3, hℓ3ub, hℓℓT, hgate']
  have hW0 : 0 ≤ W := by
    rw [hWdef, h20M]
    apply Real.log_nonneg
    nlinarith [hPinv2, hM1, hPinvpos]
  -- term 1
  have hterm1 : 140 * Pinv * W ≤ 10 ^ 8 * D5 := by
    have hPW : Pinv * W ≤ 8000 * (LT ^ ((3 : ℝ) / 4) * ℓT ^ (2 : ℕ)) * (8 * ℓT) :=
      mul_le_mul hPinv5 hWub hW0 (by positivity)
    have heq : 8000 * (LT ^ ((3 : ℝ) / 4) * ℓT ^ (2 : ℕ)) * (8 * ℓT)
        = 64000 * (LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ)) := by ring
    have hstep : LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) ≤ D5 := by
      rw [hD5def]
      refine mul_le_mul_of_nonneg_left ?_ hLT34pos.le
      exact pow_le_pow_right₀ hℓT1 (by norm_num)
    nlinarith [hPW, heq, hstep, hD5pos]
  -- term 2
  have hterm2 : (W / Real.log (7 / 6)) / w ≤ 200 / c_vk * D5 := by
    have h76pos : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
    have h76ge : (1 : ℝ) / 7 ≤ Real.log (7 / 6) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 / 7 by norm_num)
      rw [show (6 : ℝ) / 7 = (7 / 6)⁻¹ by norm_num, Real.log_inv] at h
      linarith
    have hWlog : W / Real.log (7 / 6) ≤ 56 * ℓT := by
      rw [div_le_iff₀ h76pos]
      nlinarith [hWub, mul_nonneg (by positivity : (0 : ℝ) ≤ 56 * ℓT) (sub_nonneg.mpr h76ge),
        hℓTpos, hW0]
    have h1w : (1 : ℝ) / w = 2 * D4 / c_vk := by rw [hwdef]; field_simp
    rw [div_eq_mul_one_div (W / Real.log (7 / 6)) w, h1w]
    have hstep : W / Real.log (7 / 6) * (2 * D4 / c_vk) ≤ 56 * ℓT * (2 * D4 / c_vk) :=
      mul_le_mul_of_nonneg_right hWlog (by positivity)
    refine le_trans hstep ?_
    have heq : 56 * ℓT * (2 * D4 / c_vk) = 112 * D5 * (1 / c_vk) := by
      rw [← hD4ℓT]; ring
    have heq2 : (200 : ℝ) / c_vk * D5 = 200 * D5 * (1 / c_vk) := by ring
    rw [heq, heq2]
    have hinv : (0 : ℝ) < 1 / c_vk := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith [hD5pos]) hinv.le
  calc ‖logDeriv (LFunction ψ) ((x : ℂ) + (γ : ℂ) * I)‖
      ≤ 140 * Pinv * W + (W / Real.log (7 / 6)) / w := hkey
    _ ≤ 10 ^ 8 * D5 + 200 / c_vk * D5 := by linarith [hterm1, hterm2]
    _ = (10 ^ 8 + 200 / c_vk) * D5 := by ring

/-! ### The moderate-height leg -/

/-- The `q`-free absolute constant of the moderate-height leg: `log(40·(2 + 3·(exp(exp 100)+4)))`,
the `log` of the crude ceiling at the VK floor.  (`ζ`'s counterpart is the NON-EFFECTIVE
`logDeriv_Zc_compact_bound` constant; this one is a closed form.) -/
def twistedEdgeLowConst : ℝ := Real.log (40 * (2 + 3 * (Real.exp (Real.exp 100) + 4)))

lemma twistedEdgeLowConst_pos : 0 < twistedEdgeLowConst := by
  rw [twistedEdgeLowConst]
  apply Real.log_pos
  nlinarith [Real.exp_pos (Real.exp 100)]

set_option maxHeartbeats 1600000 in
-- The moderate leg's closing arithmetic (the log q / loglog absorption at the fixed scale) needs
-- more than the default budget.
/-- **THE TWISTED EDGE, moderate heights.**  Below stone C's floor (`|γ| ≤ exp(exp 100) + 1`) the
disc engine runs at the FIXED scale `Θ = 1/2` on the crude effective ceiling
`LFunction_crude_growth`, giving

`‖L′/L(x + iγ, ψ)‖ ≤ 300·(twistedEdgeLowConst + 1)·(1 + 1/c_vk)·D₅(5T+1)`.

The `log q` produced by the ceiling is paid by the same `q`-scale gate the high leg uses; the rest
is absolute.  Effective throughout — no compactness. -/
lemma twisted_edge_moderate {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ1 : ψ ≠ 1)
    {c_vk T x γ : ℝ} (hc_vk : 0 < c_vk)
    (hγlow : |γ| ≤ Real.exp (Real.exp 100) + 1)
    (hT : Real.exp (Real.exp 100) ≤ T)
    (hsc_thr : 9000 * c_vk ≤ Real.log (Real.log (5 * T + 1)))
    (hqgate : 8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)))
    (hxlb : 1 - (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) ≤ x)
    (hxub : x ≤ 1 + (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)))
    (hmargin : ∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ))) :
    ‖logDeriv (LFunction ψ) ((x : ℂ) + (γ : ℂ) * I)‖
      ≤ 300 * (twistedEdgeLowConst + 1) * (1 + 1 / c_vk)
        * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ)) := by
  set LT : ℝ := Real.log (5 * T + 1) with hLTdef
  set ℓT : ℝ := Real.log LT with hℓTdef
  have hEpos : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hE5T : Real.exp (Real.exp 100) ≤ 5 * T + 1 := by linarith
  have hLT100 : Real.exp 100 ≤ LT := by
    rw [hLTdef, ← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log hEpos hE5T
  have hLT1 : (1 : ℝ) ≤ LT := by linarith
  have hLTpos : 0 < LT := by linarith
  have hℓT100 : (100 : ℝ) ≤ ℓT := by
    rw [hℓTdef, ← Real.log_exp (100 : ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hLT100
  have hℓT1 : (1 : ℝ) ≤ ℓT := by linarith
  have hℓTpos : 0 < ℓT := by linarith
  have hLT34 : (1 : ℝ) ≤ LT ^ ((3 : ℝ) / 4) := Real.one_le_rpow hLT1 (by norm_num)
  have hLT34pos : 0 < LT ^ ((3 : ℝ) / 4) := by linarith
  set D4 : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ) with hD4def
  set D5 : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (5 : ℕ) with hD5def
  have hD4pos : 0 < D4 := by rw [hD4def]; positivity
  have hD5pos : 0 < D5 := by rw [hD5def]; positivity
  have hD4ℓT : D4 * ℓT = D5 := by rw [hD4def, hD5def]; ring
  have hD4geℓT : ℓT ≤ D4 := by
    rw [hD4def]
    have h1 : ℓT ≤ ℓT ^ (4 : ℕ) := by
      have h3 : (1 : ℝ) ≤ ℓT ^ (3 : ℕ) := one_le_pow₀ hℓT1
      nlinarith [mul_le_mul_of_nonneg_left h3 hℓTpos.le]
    nlinarith [h1, pow_nonneg hℓTpos.le 4]
  have hD41 : (1 : ℝ) ≤ D4 := by linarith
  have hD5geℓT : ℓT ≤ D5 := by rw [← hD4ℓT]; nlinarith [hD41, hℓTpos]
  have hD51 : (1 : ℝ) ≤ D5 := by linarith
  have hD4D5 : 100 * D4 ≤ D5 := by rw [← hD4ℓT]; nlinarith [hD4pos, hℓT100]
  set w : ℝ := (c_vk / 2) / D4 with hwdef
  have hw0 : 0 < w := by rw [hwdef]; positivity
  have hwsmall : w ≤ 1 / 18000 := by
    rw [hwdef, div_le_div_iff₀ hD4pos (by norm_num : (0 : ℝ) < 18000)]
    nlinarith [hsc_thr, hD4geℓT, hc_vk]
  -- the fixed scale
  set Θ : ℝ := 1 / 2 with hΘdef
  have hΘ0 : 0 < Θ := by rw [hΘdef]; norm_num
  have hΘ12 : Θ ≤ 1 / 2 := by rw [hΘdef]
  -- the crude ceiling
  set Zb : ℝ := Real.exp (Real.exp 100) + 4 with hZbdef
  have hZb0 : 0 < Zb := by rw [hZbdef]; linarith
  set M : ℝ := 1 + (q : ℝ) * (1 + 3 * Zb) with hMdef
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne q); exact_mod_cast this
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; nlinarith [hq1, hZb0]
  have hgrowth : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → |z.im - γ| ≤ 3 / 4 →
      ‖LFunction ψ z‖ ≤ M := by
    intro z hre1 hre2 him
    have hzre : (1 : ℝ) / 2 ≤ z.re := by rw [hΘdef] at hre1; linarith
    have hzim : |z.im| ≤ Real.exp (Real.exp 100) + 2 := by
      have h := abs_sub_abs_le_abs_sub z.im γ
      linarith [h, him, hγlow]
    have hznorm : ‖z‖ ≤ Zb := by
      have h1 : ‖z‖ ≤ |z.re| + |z.im| := by
        have := Complex.norm_le_abs_re_add_abs_im z; linarith
      have h2 : |z.re| = z.re := abs_of_pos (by linarith)
      rw [hZbdef]; linarith [h1, h2, hzim]
    have hcr := LFunction_crude_growth ψ hψ1 hzre
    have hstep : (q : ℝ) * (1 + 3 * ‖z‖) ≤ (q : ℝ) * (1 + 3 * Zb) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    rw [hMdef]; linarith [hcr, hstep]
  -- the datum
  have hx : |x - 1| ≤ w := by
    rw [abs_le]; constructor <;> linarith [hxlb, hxub]
  have hwΘ : w ≤ 17 * Θ / 35 := by rw [hΘdef]; linarith [hwsmall]
  have hγT : |γ| ≤ 5 * T := by linarith
  have hxlb' : 1 - (c_vk / 2) / D4 ≤ x := by rw [← hwdef]; exact hxlb
  have hzfree : ∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im - γ| ≤ 3 / 4 → ρ.re ≤ x - w := by
    intro ρ hρ0 him
    have h := twisted_zfree_of_margin (D := D4) hD4pos hγT hxlb' hmargin ρ hρ0 him
    rw [hwdef]; exact h
  have hkey := twisted_disc_engine ψ hψ1 hΘ0 hΘ12 hM1 hw0 hgrowth hx hwΘ hzfree
  -- the price
  have h140 : (140 : ℝ) / Θ = 280 := by rw [hΘdef]; norm_num
  have h20M : (20 : ℝ) * M / Θ = 40 * M := by rw [hΘdef]; ring
  rw [h140, h20M] at hkey
  set W : ℝ := Real.log (40 * M) with hWdef
  -- `W ≤ log q + twistedEdgeLowConst`
  have hWub : W ≤ Real.log (q : ℝ) + twistedEdgeLowConst := by
    have hMle : M ≤ (q : ℝ) * (2 + 3 * Zb) := by rw [hMdef]; nlinarith [hq1, hZb0]
    have hstep : W ≤ Real.log (40 * ((q : ℝ) * (2 + 3 * Zb))) := by
      rw [hWdef]
      refine Real.log_le_log (by positivity) ?_
      linarith [hMle]
    have heq : Real.log (40 * ((q : ℝ) * (2 + 3 * Zb)))
        = Real.log (q : ℝ) + Real.log (40 * (2 + 3 * Zb)) := by
      rw [show (40 : ℝ) * ((q : ℝ) * (2 + 3 * Zb)) = (q : ℝ) * (40 * (2 + 3 * Zb)) by ring,
        Real.log_mul (by linarith) (by positivity)]
    rw [twistedEdgeLowConst, hZbdef] at *
    linarith [hstep, heq]
  have hW0 : 0 ≤ W := by
    rw [hWdef]; apply Real.log_nonneg; nlinarith [hM1]
  have hlogq : Real.log (q : ℝ) ≤ ℓT / 8 := by
    have h1 : Real.log (q : ℝ) ≤ Real.log (40000 * vkStripConst q) := by
      refine Real.log_le_log (by linarith) ?_
      rw [vkStripConst]; nlinarith [hq1]
    linarith [hqgate]
  set Cl : ℝ := twistedEdgeLowConst with hCldef
  have hCl0 : 0 < Cl := by rw [hCldef]; exact twistedEdgeLowConst_pos
  have hWfin : W ≤ ℓT / 8 + Cl := by rw [hCldef]; linarith [hWub, hlogq]
  -- term 1
  have hterm1 : 280 * W ≤ (280 * Cl + 35) * D5 := by
    have h1 : 280 * W ≤ 280 * (ℓT / 8 + Cl) := by linarith
    have h2 : 280 * (ℓT / 8 + Cl) = 35 * ℓT + 280 * Cl := by ring
    have h3 : 35 * ℓT ≤ 35 * D5 := by linarith [hD5geℓT]
    have h4 : 280 * Cl ≤ 280 * Cl * D5 := by nlinarith [hCl0, hD51]
    linarith [h1, h2, h3, h4]
  -- term 2
  have hterm2 : (W / Real.log (7 / 6)) / w ≤ (2 + Cl) * (1 / c_vk) * D5 := by
    have h76pos : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
    have h76ge : (1 : ℝ) / 7 ≤ Real.log (7 / 6) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 / 7 by norm_num)
      rw [show (6 : ℝ) / 7 = (7 / 6)⁻¹ by norm_num, Real.log_inv] at h
      linarith
    have hWlog : W / Real.log (7 / 6) ≤ 7 * W := by
      rw [div_le_iff₀ h76pos]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 7 * W) (sub_nonneg.mpr h76ge), hW0]
    have h1w : (1 : ℝ) / w = 2 * D4 / c_vk := by rw [hwdef]; field_simp
    rw [div_eq_mul_one_div (W / Real.log (7 / 6)) w, h1w]
    have hstep : W / Real.log (7 / 6) * (2 * D4 / c_vk) ≤ 7 * W * (2 * D4 / c_vk) :=
      mul_le_mul_of_nonneg_right hWlog (by positivity)
    refine le_trans hstep ?_
    have heq : 7 * W * (2 * D4 / c_vk) = (14 * W * D4) * (1 / c_vk) := by ring
    rw [heq]
    have hbnd : 14 * W * D4 ≤ (2 + Cl) * D5 := by
      have hA : 14 * W * D4 ≤ 14 * (ℓT / 8 + Cl) * D4 := by
        nlinarith [hWfin, hD4pos]
      have hB : 14 * (ℓT / 8 + Cl) * D4 = (7 / 4) * (D4 * ℓT) + 14 * Cl * D4 := by ring
      have hC : 14 * Cl * D4 ≤ Cl * D5 := by
        nlinarith [hD4D5, hCl0, hD4pos]
      rw [hD4ℓT] at hB
      linarith [hA, hB, hC, hD5pos]
    have hcinv : (0 : ℝ) < 1 / c_vk := by positivity
    calc (14 * W * D4) * (1 / c_vk) ≤ ((2 + Cl) * D5) * (1 / c_vk) :=
          mul_le_mul_of_nonneg_right hbnd hcinv.le
      _ = (2 + Cl) * (1 / c_vk) * D5 := by ring
  -- assemble
  have hfin : (280 * Cl + 35) * D5 + (2 + Cl) * (1 / c_vk) * D5
      ≤ 300 * (Cl + 1) * (1 + 1 / c_vk) * D5 := by
    have hexp : 300 * (Cl + 1) * (1 + 1 / c_vk)
        = (300 * Cl + 300) + (300 * Cl + 300) * (1 / c_vk) := by ring
    have hc1 : (0 : ℝ) < 1 / c_vk := by positivity
    have h1 : 280 * Cl + 35 ≤ 300 * Cl + 300 := by linarith
    have h2 : (2 + Cl) * (1 / c_vk) ≤ (300 * Cl + 300) * (1 / c_vk) := by
      apply mul_le_mul_of_nonneg_right _ hc1.le; linarith
    nlinarith [h1, h2, hD5pos]
  calc ‖logDeriv (LFunction ψ) ((x : ℂ) + (γ : ℂ) * I)‖
      ≤ 280 * W + (W / Real.log (7 / 6)) / w := hkey
    _ ≤ (280 * Cl + 35) * D5 + (2 + Cl) * (1 / c_vk) * D5 := by linarith [hterm1, hterm2]
    _ ≤ 300 * (Cl + 1) * (1 + 1 / c_vk) * D5 := hfin

/-! ## §4 — THE EDGE, glued: `twisted_edge_price_strip` -/

set_option maxHeartbeats 800000 in
-- The glue case-splits on |γ| against the floor after the exp/log threshold discharges; the
-- default budget is tight for the packaged split.
/-- **THE TWISTED EDGE (D1).**  There are `c_vk > 0`, `CE > 0`, `T₀ ≥ 3` such that for every
`q > 0`, every NONPRINCIPAL `ψ mod q`, every `T ≥ T₀` satisfying the `q`-scale gate, under the
region conclusion `twisted_rect_zero_free_split` supplies, the log-derivative of `L(·,ψ)` on the
whole near-1-line strip `|x − 1| ≤ (c_vk/2)/D₄(5T+1)` at any contour height `|γ| ≤ 5T` is
`D₅(5T+1)`-graded:

`‖L′/L(x + iγ, ψ)‖ ≤ CE·(log(5T+1))^{3/4}(loglog(5T+1))⁵`.

The `ζ`-twin is `shifted_edge_price_strip` (whose grade is `D₄` against a `D₃` depth).  The two
legs: `twisted_edge_disc_core` above stone C's floor `exp(exp 100) + 1`, `twisted_edge_moderate`
below it — no conjugation leg, no compactness constant. -/
theorem twisted_edge_price_strip :
    ∃ (c_vk CE T₀ : ℝ), 0 < c_vk ∧ c_vk ≤ 1 ∧ c_vk = 1 / 10 ^ 8 ∧
      0 < CE ∧ Real.exp (Real.exp 100) ≤ T₀ ∧
      ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q), ψ ≠ 1 →
      ∀ (T x γ : ℝ), T₀ ≤ T →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        (∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
            ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ))) →
        1 - (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) ≤ x →
        x ≤ 1 + (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
        |γ| ≤ 5 * T →
        ‖logDeriv (LFunction ψ) ((x : ℂ) + (γ : ℂ) * I)‖
          ≤ CE * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ)) := by
  refine ⟨1 / 10 ^ 8, (10 ^ 8 + 200 / (1 / 10 ^ 8 : ℝ))
      + 300 * (twistedEdgeLowConst + 1) * (1 + 1 / (1 / 10 ^ 8 : ℝ)),
    Real.exp (Real.exp 100), by norm_num, by norm_num, rfl, ?_, le_refl _, ?_⟩
  · have h := twistedEdgeLowConst_pos; positivity
  intro q hq ψ hψ1 T x γ hT hqgate hmargin hxlb hxub hγT
  have hCl0 : 0 < twistedEdgeLowConst := twistedEdgeLowConst_pos
  have hc_vk : (0 : ℝ) < 1 / 10 ^ 8 := by norm_num
  -- the `hsc_thr` threshold is free at this `c_vk`
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEpos : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  have hE5T : Real.exp (Real.exp 100) ≤ 5 * T + 1 := by
    have := hT; nlinarith [hEpos]
  have hLT100 : Real.exp 100 ≤ Real.log (5 * T + 1) := by
    rw [← Real.log_exp (Real.exp 100)]; exact Real.log_le_log hEpos hE5T
  have hℓT100 : (100 : ℝ) ≤ Real.log (Real.log (5 * T + 1)) := by
    rw [← Real.log_exp (100 : ℝ)]; exact Real.log_le_log (Real.exp_pos _) hLT100
  have hsc_thr : 9000 * (1 / 10 ^ 8 : ℝ) ≤ Real.log (Real.log (5 * T + 1)) := by
    norm_num; linarith [hℓT100]
  set D5 : ℝ := (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
    * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ) with hD5def
  have hD5pos : 0 < D5 := by
    rw [hD5def]
    have h1 : (0 : ℝ) < (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_pos_of_pos (by linarith) _
    have h2 : (0 : ℝ) < (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ) := by
      apply pow_pos; linarith
    exact mul_pos h1 h2
  by_cases hcase : Real.exp (Real.exp 100) + 1 ≤ |γ|
  · have h := twisted_edge_disc_core ψ hψ1 hc_vk hcase hγT hsc_thr hqgate hxlb hxub hmargin
    rw [← hD5def] at h
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_right ?_ hD5pos.le
    have hpos : (0 : ℝ) ≤ 300 * (twistedEdgeLowConst + 1) * (1 + 1 / (1 / 10 ^ 8 : ℝ)) := by
      positivity
    linarith
  · rw [not_le] at hcase
    have h := twisted_edge_moderate ψ hψ1 hc_vk (le_of_lt hcase) hT hsc_thr hqgate hxlb hxub
      hmargin
    rw [← hD5def] at h
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_right ?_ hD5pos.le
    have hpos : (0 : ℝ) ≤ 10 ^ 8 + 200 / (1 / 10 ^ 8 : ℝ) := by positivity
    linarith


/-! ## §5 — D2: THE PRICE DISCHARGE

`TwistedWindowPrice` (stone C, `HalaszPrimesChi.lean` §5) is `per_pair_contour` for the
`ψ`-twisted coefficient with the pole term DELETED.  Two structural notes:

* **RES/POLE-ROW have no twin.**  `L(·,ψ)` is entire for `ψ ≠ 1`, so the shifted rectangle carries
  NO interior pole: `pole_residue_term` is replaced by plain Cauchy–Goursat
  (`Salt.SW.rectBI_eq_zero_of_differentiableOn`) and the main term `windowKernel P 1 u` disappears
  from the statement — the twisted per-pair estimate is pure error.  The LEFT edge also loses its
  `1/w` pole price (`ζ`'s `Bσ = 1/w + CE·D₄` becomes `Bσ = CE·D₅`).
* **the representation layer is cited, not re-proved** (stone C's finding): `lambda_window_rep_chi`
  is REP-χ, `rep_truncated` is generic in the coefficient, `sum_vonMangoldt_cline_bound` and
  `truncKernel_const_le` are character-blind (`‖ψ(n)‖ ≤ 1`).

`TwistedWindowPriceGated` is `TwistedWindowPrice`'s body plus the ONE `q`-scale gate the edge needs
(see the module docstring).  For a FIXED `q` the gate is a `T`-floor, so P-7 discharges it exactly
where it discharges the split's own two gates. -/

/-- The `c`-line fold of the twisted coefficient: the Dirichlet series of `ψ(n)Λ(n)n^{iu}` at
`c + iv` is `−L′/L((c+iv) − iu, ψ)`.  The per-`v` core of `lambda_window_rep_chi`, extracted for
the truncation leg. -/
lemma twisted_dirichlet_cline {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {c u v : ℝ}
    (hc : 1 < c) :
    (∑' n : ℕ, ((χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))
          * (n : ℂ) ^ ((u : ℂ) * I))
        / (n : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
      = - logDeriv (LFunction χ) ((c : ℂ) + (v : ℂ) * I - (u : ℂ) * I) := by
  have hwre : (1 : ℝ) < ((c : ℂ) + (v : ℂ) * I - (u : ℂ) * I).re := by simp; linarith
  have hz0 : ((χ ((0 : ℕ) : ZMod q) * (ArithmeticFunction.vonMangoldt 0 : ℂ))
      * ((0 : ℕ) : ℂ) ^ ((u : ℂ) * I)) = 0 := by
    rw [show (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 by
      rw [ArithmeticFunction.map_zero]; norm_num]
    ring
  have hterm : ∀ n : ℕ, ((χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))
        * (n : ℂ) ^ ((u : ℂ) * I)) / (n : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)
      = LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt)
          ((c : ℂ) + (v : ℂ) * I - (u : ℂ) * I) n := by
    intro n
    rw [LSeries.term_def₀ (by simp) _ n]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hz0]; simp
    · have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [Pi.mul_apply]
      rw [mul_div_assoc]
      congr 1
      rw [div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hne]
      congr 1
      ring
  have hLS : (∑' n : ℕ, ((χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))
        * (n : ℂ) ^ ((u : ℂ) * I)) / (n : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
      = LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt)
          ((c : ℂ) + (v : ℂ) * I - (u : ℂ) * I) := tsum_congr hterm
  rw [hLS, ← Salt.SW.neg_logDeriv_LSeries_eq_LSeries_twist χ hwre,
    Salt.SW.neg_logDeriv_LSeries_eq χ hwre]

/-- **The twisted `c`-line bound.**  On a vertical line `Re = x > 1`, the twisted log-derivative is
dominated by the untwisted real Dirichlet sum: `‖L′/L(x+is,ψ)‖ ≤ ∑ Λ(n)/n^x` (`‖ψ(n)‖ ≤ 1`).  The
`χ`-twin of `norm_logDeriv_zeta_cline_le`; the sliver leg of the horizontals reads it. -/
lemma norm_logDeriv_LFunction_cline_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 1 < x) (s : ℝ) :
    ‖logDeriv (LFunction χ) ((x : ℂ) + (s : ℂ) * I)‖
      ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ x := by
  have hwre : (1 : ℝ) < ((x : ℂ) + (s : ℂ) * I).re := by simp; linarith
  have hnt : ∀ n : ℕ, ‖LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt)
        ((x : ℂ) + (s : ℂ) * I) n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ x := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg hn.ne']
      have hre : ((x : ℂ) + (s : ℂ) * I).re = x := by simp
      rw [hre]
      have hnum : ‖(↗χ * ↗ArithmeticFunction.vonMangoldt : ℕ → ℂ) n‖
          ≤ ArithmeticFunction.vonMangoldt n := by
        simp only [Pi.mul_apply, norm_mul]
        have h1 : ‖χ (n : ZMod q)‖ ≤ 1 := χ.norm_le_one _
        have h2 : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖
            = ArithmeticFunction.vonMangoldt n := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        rw [h2]
        nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n), norm_nonneg (χ (n : ZMod q))]
      have hpos : (0 : ℝ) < (n : ℝ) ^ x :=
        Real.rpow_pos_of_pos (by exact_mod_cast hn) x
      rw [div_le_div_iff_of_pos_right hpos]
      exact hnum
  have hsummN : Summable (fun n => ‖LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt)
      ((x : ℂ) + (s : ℂ) * I) n‖) :=
    summable_norm_iff.mpr (DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hwre))
  have hfold : - logDeriv (LFunction χ) ((x : ℂ) + (s : ℂ) * I)
      = LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) ((x : ℂ) + (s : ℂ) * I) := by
    rw [← Salt.SW.neg_logDeriv_LSeries_eq χ hwre,
      Salt.SW.neg_logDeriv_LSeries_eq_LSeries_twist χ hwre]
  have hnormeq : ‖logDeriv (LFunction χ) ((x : ℂ) + (s : ℂ) * I)‖
      = ‖LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) ((x : ℂ) + (s : ℂ) * I)‖ := by
    rw [← hfold, norm_neg]
  rw [hnormeq]
  calc ‖LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) ((x : ℂ) + (s : ℂ) * I)‖
      ≤ ∑' n, ‖LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt)
          ((x : ℂ) + (s : ℂ) * I) n‖ := norm_tsum_le_tsum_norm hsummN
    _ ≤ ∑' n, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ x :=
        hsummN.tsum_le_tsum hnt (summable_vonMangoldt_div_rpow hx)

/-- `s ↦ logDeriv (L(·,ψ)) (s − iu)` is differentiable on any set where the shifted argument is a
non-zero of `L(·,ψ)` — the twin of `logDeriv_Zc_shift_differentiableOn`, with the `Zc`
normalization gone (`L(·,ψ)` is entire for `ψ ≠ 1`). -/
lemma logDeriv_LFunction_shift_differentiableOn {q : ℕ} [NeZero q]
    {ψ : DirichletCharacter ℂ q} (hψ1 : ψ ≠ 1) {u : ℝ} {K : Set ℂ}
    (hK : ∀ s ∈ K, LFunction ψ (s - (u : ℂ) * I) ≠ 0) :
    DifferentiableOn ℂ (fun s => logDeriv (LFunction ψ) (s - (u : ℂ) * I)) K := by
  have hLana : AnalyticOnNhd ℂ (LFunction ψ) univ :=
    (differentiable_LFunction hψ1).differentiableOn.analyticOnNhd isOpen_univ
  have hdana : AnalyticOnNhd ℂ (deriv (LFunction ψ)) univ := hLana.deriv
  intro s hs
  have hne := hK s hs
  have h1 : AnalyticAt ℂ (logDeriv (LFunction ψ)) (s - (u : ℂ) * I) := by
    have h : AnalyticAt ℂ (fun z => deriv (LFunction ψ) z / LFunction ψ z) (s - (u : ℂ) * I) :=
      (hdana _ (mem_univ _)).div (hLana _ (mem_univ _)) hne
    rw [show logDeriv (LFunction ψ) = fun z => deriv (LFunction ψ) z / LFunction ψ z from rfl]
    exact h
  exact ((h1.differentiableAt).comp s (differentiableAt_id.sub_const _)).differentiableWithinAt

/-- **THE RESIDUE INTERFACE, GATED.**  `Salt.MR.TwistedWindowPrice`'s body plus the one `q`-scale
gate the twisted edge needs.  Everything else — the region hypothesis, the `D₄` depth, the `D₅`
price shape, the three terms, the constants' quantifier order — is byte-identical to stone C's
pin. -/
def TwistedWindowPriceGated (c_vk C₁ C₂ C₃ T₀ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q), ψ ≠ 1 →
  ∀ (T P u : ℝ), T₀ ≤ T → 2 ≤ P → |u| ≤ 2 * T →
    8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
    (∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ))) →
    ‖∑' n : ℕ, ((ψ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))
          * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ)‖
      ≤ C₁ * P * Real.exp (-(c_vk / 2) * Real.log P
              / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                  * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)))
            * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ))
        + C₂ * P * Real.log P / T
        + C₃ * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ)) * P / T ^ 2

/-- **The gate IS a `q`-dependent height floor.**  For a fixed `q`, the `q`-scale gate of
`TwistedWindowPriceGated` (and of `twisted_edge_price_strip`) holds at every
`T ≥ exp(exp(8·log(40000·vkStripConst q)))`.  So the deviation from stone C's pin costs P-7 exactly
one extra `T`-floor per modulus — the same shape the split's own two gates have. -/
lemma twisted_gate_of_height {q : ℕ} [NeZero q] {T : ℝ}
    (hT : Real.exp (Real.exp (8 * Real.log (40000 * vkStripConst q))) ≤ T) :
    8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) := by
  set A : ℝ := 8 * Real.log (40000 * vkStripConst q) with hAdef
  have hE : Real.exp (Real.exp A) ≤ 5 * T + 1 := by
    have h := Real.exp_pos (Real.exp A); linarith
  have h1 : Real.exp A ≤ Real.log (5 * T + 1) := by
    rw [← Real.log_exp (Real.exp A)]; exact Real.log_le_log (Real.exp_pos _) hE
  have h2 := Real.log_le_log (Real.exp_pos A) h1
  rwa [Real.log_exp] at h2

set_option maxHeartbeats 12800000 in
-- The full twisted contour assembly (Goursat + four sub-bounds + the orientation glue) runs in one
-- declaration; the ζ twin `per_pair_contour` needs the same 12.8M budget.
/-- **D2 — THE PRICE DISCHARGE.**  `TwistedWindowPriceGated` holds.  The `ζ` twin is
`per_pair_contour`; the pole row is gone (Cauchy–Goursat replaces the residue extraction, and
there is no main term). -/
theorem twisted_window_price_gated_holds :
    ∃ (C₁ C₂ C₃ T₀ : ℝ), 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ Real.exp (Real.exp 100) ≤ T₀ ∧
      TwistedWindowPriceGated (1 / 10 ^ 8) C₁ C₂ C₃ T₀ := by
  obtain ⟨c_vk, CE, T₀e, hc_vk0, hc_vk1, hc_vkval, hCE0, hT₀efloor, hedge⟩ :=
    twisted_edge_price_strip
  rw [← hc_vkval]
  obtain ⟨C₀, hC₀0, hcline⟩ := sum_vonMangoldt_cline_bound
  obtain ⟨δ₀, C₀z, hδ₀0, hcptZ⟩ :=
    logDeriv_Zc_compact_bound (M := 0) (c := 2) (le_refl 0) (by norm_num)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  set Kc : ℝ := (2 * 9 * (3 : ℝ) ^ ((Real.log 2)⁻¹) + 4) * Real.exp 1 with hKcdef
  have hKcpos : 0 < Kc := by rw [hKcdef]; positivity
  set Cζ : ℝ := 2 / c_vk + |C₀z| + CE with hCζdef
  have hCζpos : 0 < Cζ := by rw [hCζdef]; positivity
  set CL : ℝ := 44 * Real.pi * CE with hCLdef
  have hCLpos : 0 < CL := by rw [hCLdef]; positivity
  set CH : ℝ := Cζ * Kc * (1 / Real.log 2 + 1 / 2) / 9 with hCHdef
  have hCHpos : 0 < CH := by rw [hCHdef]; positivity
  set CT : ℝ := 2 / 3 * Kc * (1 + C₀ / Real.log 2) with hCTdef
  have hCTpos : 0 < CT := by rw [hCTdef]; positivity
  refine ⟨CL / (2 * Real.pi), CT / (2 * Real.pi), 2 * CH / (2 * Real.pi),
    T₀e, div_pos hCLpos (by positivity), div_pos hCTpos (by positivity),
    div_pos (by positivity) (by positivity), by linarith [hT₀efloor, hEbig], ?_⟩
  intro q hq ψ hψ1 T P u hT hP hu hqgate hmargin
  have hEfloor : Real.exp (Real.exp 100) ≤ T := le_trans hT₀efloor hT
  have hT3 : (3 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hP0 : (0 : ℝ) < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  -- the edge, pre-instantiated at this `(q, ψ, T)` so the abbreviations fold into it
  have hedgeT : ∀ x γ : ℝ,
      1 - (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) ≤ x →
      x ≤ 1 + (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      |γ| ≤ 5 * T →
      ‖logDeriv (LFunction ψ) ((x : ℂ) + (γ : ℂ) * I)‖
        ≤ CE * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ)) :=
    fun x γ h1 h2 h3 => hedge q ψ hψ1 T x γ hT hqgate hmargin h1 h2 h3
  -- === the scales ===
  set LT : ℝ := Real.log (5 * T + 1) with hLTdef
  set ℓT : ℝ := Real.log LT with hℓTdef
  have hE5T : Real.exp (Real.exp 100) ≤ 5 * T + 1 := by linarith
  have hLT100 : Real.exp 100 ≤ LT := by
    rw [hLTdef, ← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) hE5T
  have hLT1 : (1 : ℝ) ≤ LT := by linarith
  have hLTpos : 0 < LT := by linarith
  have hℓT100 : (100 : ℝ) ≤ ℓT := by
    rw [hℓTdef, ← Real.log_exp (100 : ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hLT100
  have hℓT1 : (1 : ℝ) ≤ ℓT := by linarith
  have hℓTpos : 0 < ℓT := by linarith
  have hLT34 : (1 : ℝ) ≤ LT ^ ((3 : ℝ) / 4) := Real.one_le_rpow hLT1 (by norm_num)
  have hLT34pos : 0 < LT ^ ((3 : ℝ) / 4) := by linarith
  set D4 : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ) with hD4def
  set D5 : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (5 : ℕ) with hD5def
  have hD4pos : 0 < D4 := by rw [hD4def]; positivity
  have hD5pos : 0 < D5 := by rw [hD5def]; positivity
  have hD41 : (1 : ℝ) ≤ D4 := by
    rw [hD4def]; nlinarith [hLT34, one_le_pow₀ hℓT1 (n := 4)]
  have hD4leD5 : D4 ≤ D5 := by
    rw [hD4def, hD5def]
    refine mul_le_mul_of_nonneg_left ?_ hLT34pos.le
    exact pow_le_pow_right₀ hℓT1 (by norm_num)
  have hD51 : (1 : ℝ) ≤ D5 := by linarith
  set w : ℝ := (c_vk / 2) / D4 with hwdef
  have hw0 : 0 < w := by rw [hwdef]; positivity
  have hwle : w ≤ 1 / 2 := by
    rw [hwdef, div_le_div_iff₀ hD4pos (by norm_num : (0 : ℝ) < 2)]; linarith
  set σ₀ : ℝ := 1 - w with hσ₀def
  have hσ₀half : (1 : ℝ) / 2 ≤ σ₀ := by rw [hσ₀def]; linarith
  have hσ₀0 : 0 < σ₀ := by linarith
  have hσ₀1 : σ₀ < 1 := by rw [hσ₀def]; linarith
  have hσ₀xlb : 1 - (c_vk / 2) / D4 ≤ σ₀ := by rw [hσ₀def, hwdef]
  have hσ₀xub : σ₀ ≤ 1 + (c_vk / 2) / D4 := by
    rw [hσ₀def, hwdef]; have : (0 : ℝ) < (c_vk / 2) / D4 := by positivity
    linarith
  set c : ℝ := 1 + (Real.log P)⁻¹ with hcdef
  have hc1 : 1 < c := by rw [hcdef]; have := inv_pos.mpr hlogP; linarith
  have hcpos : 0 < c := by linarith
  set Tp : ℝ := 3 * T with hTpdef
  have hTp0 : 0 < Tp := by rw [hTpdef]; linarith
  have huTp : |u| < Tp := by rw [hTpdef]; linarith [hu, abs_nonneg u]
  -- === the contour integrand and the rectangle ===
  set F : ℂ → ℂ := fun s => (- logDeriv (LFunction ψ) (s - (u : ℂ) * I)) * windowMellin P s
    with hFdef
  set zc : ℂ := (σ₀ : ℂ) + ((-Tp : ℝ) : ℂ) * I with hzc
  set wc : ℂ := (c : ℂ) + (Tp : ℂ) * I with hwc
  have hzc_re : zc.re = σ₀ := by rw [hzc]; simp
  have hzc_im : zc.im = -Tp := by rw [hzc]; simp
  have hwc_re : wc.re = c := by rw [hwc]; simp
  have hwc_im : wc.im = Tp := by rw [hwc]; simp
  -- zero-freeness of the shifted argument on the rectangle
  have hzf : ∀ s : ℂ, s ∈ closedRect zc wc → LFunction ψ (s - (u : ℂ) * I) ≠ 0 := by
    intro s hs
    rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm,
      Set.uIcc_of_le (by linarith : σ₀ ≤ c),
      Set.uIcc_of_le (by linarith : -Tp ≤ Tp)] at hs
    obtain ⟨hsre, hsim⟩ := hs
    simp only [Set.mem_Icc] at hsre hsim
    have hsre' : (s - (u : ℂ) * I).re = s.re := by simp
    have hshim : |(s - (u : ℂ) * I).im| ≤ 5 * T + 1 := by
      have him : (s - (u : ℂ) * I).im = s.im - u := by simp
      have hb := abs_le.mp hu
      rw [hTpdef] at hsim
      rw [him, abs_le]
      constructor <;> nlinarith [hsim.1, hsim.2, hb.1, hb.2]
    intro hz0
    by_cases h1 : (1 : ℝ) ≤ (s - (u : ℂ) * I).re
    · exact LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) h1 hz0
    · have hmr := hmargin (s - (u : ℂ) * I) hz0 hshim
      rw [hsre'] at hmr
      have hlt : (c_vk / 2) / D4 < c_vk / D4 := by
        rw [div_lt_div_iff₀ hD4pos hD4pos]; nlinarith [hc_vk0, hD4pos]
      have hσs : σ₀ ≤ s.re := hsre.1
      rw [hσ₀def, hwdef] at hσs
      linarith [hmr, hlt]
  -- Cauchy–Goursat: no pole, so the boundary integral vanishes
  have hFdiffOn : DifferentiableOn ℂ F (closedRect zc wc) := by
    have hlog := logDeriv_LFunction_shift_differentiableOn hψ1 (u := u) (K := closedRect zc wc) hzf
    have hwin : DifferentiableOn ℂ (windowMellin P) (closedRect zc wc) := by
      refine windowMellin_differentiableOn hP0 hσ₀0 (fun s hs => ?_)
      rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm,
        Set.uIcc_of_le (by linarith : σ₀ ≤ c),
        Set.uIcc_of_le (by linarith : -Tp ≤ Tp)] at hs
      exact hs.1.1
    rw [hFdef]
    exact (hlog.neg).mul hwin
  have hgour : rectBI zc wc F = 0 := rectBI_eq_zero_of_differentiableOn hFdiffOn
  -- the four edges
  set BOT : ℂ := ∫ x in σ₀..c, F ((x : ℂ) + ((-Tp : ℝ) : ℂ) * I) with hBOTdef
  set TOP : ℂ := ∫ x in σ₀..c, F ((x : ℂ) + (Tp : ℂ) * I) with hTOPdef
  set RIGHT : ℂ := ∫ v in (-Tp)..Tp, F ((c : ℂ) + (v : ℂ) * I) with hRIGHTdef
  set LEFT : ℂ := ∫ v in (-Tp)..Tp, F ((σ₀ : ℂ) + (v : ℂ) * I) with hLEFTdef
  have hunf : rectBI zc wc F = BOT - TOP + I * RIGHT - I * LEFT := by
    rw [rectBI, hzc_re, hzc_im, hwc_re, hwc_im, hBOTdef, hTOPdef, hRIGHTdef, hLEFTdef]
  rw [hunf] at hgour
  have hrearr : RIGHT = LEFT - I * (TOP - BOT) := by
    have key : I * RIGHT = I * (LEFT - I * (TOP - BOT)) := by
      have expand : I * (LEFT - I * (TOP - BOT)) = I * LEFT + (TOP - BOT) := by
        have hII : I * (I * (TOP - BOT)) = -(TOP - BOT) := by
          rw [← mul_assoc, Complex.I_mul_I]; ring
        rw [mul_sub, hII]; ring
      rw [expand]; linear_combination hgour
    exact mul_left_cancel₀ Complex.I_ne_zero key
  -- === the REP bridge and the truncation ===
  set a : ℕ → ℂ := fun n => (ψ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))
    * (n : ℂ) ^ ((u : ℂ) * I) with hadef
  have ha0 : a 0 = 0 := by
    rw [hadef]
    simp only
    rw [show (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 by
      rw [ArithmeticFunction.map_zero]; norm_num]
    ring
  have hnorm_a : ∀ n : ℕ, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n := fun n => by
    rw [hadef]; exact norm_chi_vonMangoldt_twist_le ψ u n
  have hsum : Summable (fun n => ‖a n‖ / (n : ℝ) ^ c) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (summable_vonMangoldt_div_rpow hc1)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ha0]; simp
    · have hpos : (0 : ℝ) < (n : ℝ) ^ c := Real.rpow_pos_of_pos (by exact_mod_cast hn) c
      rw [div_le_div_iff_of_pos_right hpos]
      exact hnorm_a n
  have hdir : ∀ v : ℝ, (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
      = - logDeriv (LFunction ψ) ((c : ℂ) + (v : ℂ) * I - (u : ℂ) * I) := by
    intro v; rw [hadef]; exact twisted_dirichlet_cline ψ hc1
  have hFdir : ∀ v : ℝ, F ((c : ℂ) + (v : ℂ) * I)
      = (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)) * windowKernel P c v := by
    intro v
    rw [hFdef]
    simp only
    rw [hdir v, windowKernel_eq_windowMellin]
  have hbridge : (∑' n : ℕ, ((ψ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))
        * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
      = (1 / (2 * Real.pi)) • ∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I) := by
    rw [show (∑' n : ℕ, ((ψ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))
          * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
        = ∑' n, a n * (primeWindow P n : ℂ) from rfl,
      primeWindow_contour_rep a ha0 hP hcpos hsum]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    exact (hFdir v).symm
  have htrunc := rep_truncated a ha0 hP hcpos hTp0 hsum
  have hI1 : (∫ t : ℝ, (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * windowKernel P c t)
      = ∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_)); exact (hFdir v).symm
  have hI2 : (∫ t in Set.Icc (-Tp) Tp,
        (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * windowKernel P c t) = RIGHT := by
    rw [hRIGHTdef, intervalIntegral.integral_of_le (by linarith : (-Tp : ℝ) ≤ Tp),
      ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc (fun v _ => ?_); exact (hFdir v).symm
  rw [hI1, hI2] at htrunc
  set TAILval : ℂ := (∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I)) - RIGHT with hTAILdef
  have hInt_split : (∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I)) = RIGHT + TAILval := by
    rw [hTAILdef]; ring
  have hTAILnorm : ‖TAILval‖ ≤ (∑' n, ‖a n‖ / (n : ℝ) ^ c)
      * (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2)) * (2 / Tp) := by
    rw [hTAILdef]; exact htrunc
  -- === rectangle membership and pointwise differentiability ===
  have hrectmem : ∀ x v : ℝ, σ₀ ≤ x → x ≤ c → -Tp ≤ v → v ≤ Tp →
      ((x : ℂ) + (v : ℂ) * I) ∈ closedRect zc wc := by
    intro x v h1 h2 h3 h4
    have hre : ((x : ℂ) + (v : ℂ) * I).re = x := by simp
    have him : ((x : ℂ) + (v : ℂ) * I).im = v := by simp
    rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm,
      Set.uIcc_of_le (by linarith : σ₀ ≤ c), Set.uIcc_of_le (by linarith : -Tp ≤ Tp)]
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Icc, hre]; exact ⟨h1, h2⟩
    · rw [Set.mem_Icc, him]; exact ⟨h3, h4⟩
  have hFdiffAt : ∀ s : ℂ, s ∈ closedRect zc wc → DifferentiableAt ℂ F s := by
    intro s hs
    have hne := hzf s hs
    have hLana : AnalyticOnNhd ℂ (LFunction ψ) univ :=
      (differentiable_LFunction hψ1).differentiableOn.analyticOnNhd isOpen_univ
    have hdana : AnalyticOnNhd ℂ (deriv (LFunction ψ)) univ := hLana.deriv
    have h1 : AnalyticAt ℂ (logDeriv (LFunction ψ)) (s - (u : ℂ) * I) := by
      have h : AnalyticAt ℂ (fun z => deriv (LFunction ψ) z / LFunction ψ z) (s - (u : ℂ) * I) :=
        (hdana _ (mem_univ _)).div (hLana _ (mem_univ _)) hne
      rw [show logDeriv (LFunction ψ) = fun z => deriv (LFunction ψ) z / LFunction ψ z from rfl]
      exact h
    have hld : DifferentiableAt ℂ (fun z => - logDeriv (LFunction ψ) (z - (u : ℂ) * I)) s :=
      ((h1.differentiableAt).comp s (differentiableAt_id.sub_const _)).neg
    have hsre : σ₀ ≤ s.re := by
      rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm,
        Set.uIcc_of_le (by linarith : σ₀ ≤ c),
        Set.uIcc_of_le (by linarith : -Tp ≤ Tp)] at hs
      exact hs.1.1
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre; linarith
    have hs1 : s + 1 ≠ 0 := fun h => by
      have hz : (s + 1).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.one_re] at hz; linarith
    have hWM : DifferentiableAt ℂ (windowMellin P) s := windowMellin_differentiableAt hP0 hs0 hs1
    rw [hFdef]; exact hld.mul hWM
  -- === LEFT edge ===
  have hLEFTb : ‖LEFT‖ ≤ CL * P * Real.exp (-(c_vk / 2) * Real.log P / D4) * D5 := by
    have hPσ0nn : (0 : ℝ) ≤ (P : ℝ) ^ σ₀ := Real.rpow_nonneg hP0.le σ₀
    have hPσ₀ : (P : ℝ) ^ σ₀ = P * Real.exp (-(c_vk / 2) * Real.log P / D4) := by
      rw [Real.rpow_def_of_pos hP0, hσ₀def, hwdef,
        show Real.log P * (1 - (c_vk / 2) / D4)
          = Real.log P + (-(c_vk / 2) * Real.log P / D4) by ring, Real.exp_add]
      congr 1; exact Real.exp_log hP0
    have hkerL : ∀ v : ℝ, ‖windowMellin P ((σ₀ : ℂ) + (v : ℂ) * I)‖
        ≤ 22 * (P : ℝ) ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
      intro v
      rw [← windowKernel_eq_windowMellin]
      refine le_trans (norm_windowKernel_le hP hσ₀0 v) ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h3Pσ : ((3 : ℝ) * P) ^ (σ₀ + 1) = (3 : ℝ) ^ (σ₀ + 1) * (P : ℝ) ^ (σ₀ + 1) :=
        Real.mul_rpow (by norm_num) hP0.le
      have hPσ1 : (P : ℝ) ^ (σ₀ + 1) = (P : ℝ) ^ σ₀ * P := by
        rw [Real.rpow_add hP0, Real.rpow_one]
      have e1 : 2 * (2 * P + P) ^ (σ₀ + 1) / P = 2 * (3 : ℝ) ^ (σ₀ + 1) * (P : ℝ) ^ σ₀ := by
        rw [show 2 * P + P = 3 * P by ring, h3Pσ, hPσ1]; field_simp
      have e2 : 2 * (P / 2 + P / 2) ^ (σ₀ + 1) / (P / 2) = 4 * (P : ℝ) ^ σ₀ := by
        rw [show P / 2 + P / 2 = P by ring, hPσ1]; field_simp; ring
      rw [e1, e2]
      have h3 : (3 : ℝ) ^ (σ₀ + 1) ≤ 9 := by
        rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hσ₀1])
      nlinarith [h3, hPσ0nn]
    have hLL : ∀ v : ℝ, v ∈ Set.Icc (-Tp) Tp →
        ‖(- logDeriv (LFunction ψ) (((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I))‖ ≤ CE * D5 := by
      intro v hv
      simp only [Set.mem_Icc] at hv
      have hs'eq : ((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I
          = (σ₀ : ℂ) + ((v - u : ℝ) : ℂ) * I := by push_cast; ring
      have hvu5T : |v - u| ≤ 5 * T := by
        have hb := abs_le.mp hu
        rw [hTpdef] at hv
        rw [abs_le]; constructor <;> nlinarith [hv.1, hv.2, hb.1, hb.2]
      rw [hs'eq, norm_neg]
      exact hedgeT σ₀ (v - u) hσ₀xlb hσ₀xub hvu5T
    have hBσ0 : (0 : ℝ) ≤ CE * D5 := by positivity
    have hg_int : Integrable (fun v : ℝ => (CE * D5) * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹) :=
      (Salt.SW.integrable_inv_c_sq_add_sq hσ₀0).const_mul _
    have hgnn : ∀ v : ℝ, (0 : ℝ) ≤ (CE * D5) * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
      fun v => by positivity
    have hpt : ∀ v ∈ Set.Icc (-Tp) Tp,
        ‖F ((σ₀ : ℂ) + (v : ℂ) * I)‖
          ≤ (CE * D5) * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
      intro v hv
      rw [hFdef]
      simp only
      rw [norm_mul]
      calc ‖(- logDeriv (LFunction ψ) (((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I))‖
              * ‖windowMellin P ((σ₀ : ℂ) + (v : ℂ) * I)‖
          ≤ (CE * D5) * (22 * (P : ℝ) ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹) :=
            mul_le_mul (hLL v hv) (hkerL v) (norm_nonneg _) hBσ0
        _ = (CE * D5) * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by ring
    have hFleft_ii : IntervalIntegrable (fun v : ℝ => F ((σ₀ : ℂ) + (v : ℂ) * I))
        volume (-Tp) Tp := by
      apply ContinuousOn.intervalIntegrable
      intro v hv
      rw [Set.uIcc_of_le (by linarith : (-Tp : ℝ) ≤ Tp), Set.mem_Icc] at hv
      have hmem := hrectmem σ₀ v (le_refl _) (by linarith) hv.1 hv.2
      have hFdiffC : DifferentiableAt ℂ F ((σ₀ : ℂ) + (v : ℂ) * I) := hFdiffAt _ hmem
      have hgdiff : DifferentiableAt ℝ (fun v : ℝ => (σ₀ : ℂ) + (v : ℂ) * I) v := by
        apply DifferentiableAt.const_add
        exact (Complex.ofRealCLM.differentiable.differentiableAt).mul_const I
      exact (((hFdiffC.restrictScalars ℝ).comp v hgdiff).continuousAt).continuousWithinAt
    calc ‖LEFT‖
        = ‖∫ v in (-Tp)..Tp, F ((σ₀ : ℂ) + (v : ℂ) * I)‖ := by rw [hLEFTdef]
      _ ≤ ∫ v in (-Tp)..Tp, ‖F ((σ₀ : ℂ) + (v : ℂ) * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ v in (-Tp)..Tp, (CE * D5) * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
          intervalIntegral.integral_mono_on (by linarith) hFleft_ii.norm
            hg_int.intervalIntegrable hpt
      _ ≤ ∫ v : ℝ, (CE * D5) * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
          rw [intervalIntegral.integral_of_le (by linarith : (-Tp : ℝ) ≤ Tp)]
          exact setIntegral_le_integral hg_int (Filter.Eventually.of_forall hgnn)
      _ = (CE * D5) * (22 * (P : ℝ) ^ σ₀) * (Real.pi / σ₀) := by
          rw [MeasureTheory.integral_const_mul, Salt.SW.integral_inv_sq_add hσ₀0]
      _ ≤ CL * P * Real.exp (-(c_vk / 2) * Real.log P / D4) * D5 := by
          have hπσ₀ : Real.pi / σ₀ ≤ 2 * Real.pi := by
            rw [div_le_iff₀ hσ₀0]; nlinarith [Real.pi_pos, hσ₀half]
          have hexpnn : (0 : ℝ) ≤ Real.exp (-(c_vk / 2) * Real.log P / D4) := (Real.exp_pos _).le
          rw [hPσ₀]
          have hfac_nn : (0 : ℝ) ≤ 22 * (P * Real.exp (-(c_vk / 2) * Real.log P / D4)) := by
            apply mul_nonneg (by norm_num); exact mul_nonneg hP0.le hexpnn
          calc (CE * D5) * (22 * (P * Real.exp (-(c_vk / 2) * Real.log P / D4)))
                  * (Real.pi / σ₀)
              ≤ (CE * D5) * (22 * (P * Real.exp (-(c_vk / 2) * Real.log P / D4)))
                  * (2 * Real.pi) := by
                refine mul_le_mul_of_nonneg_left hπσ₀ ?_
                exact mul_nonneg hBσ0 hfac_nn
            _ = CL * P * Real.exp (-(c_vk / 2) * Real.log P / D4) * D5 := by rw [hCLdef]; ring
  -- === HORIZONTALS ===
  have hTle : (1 : ℝ) ≤ T := by linarith
  have h1w_inv : (1 : ℝ) / w ≤ 2 / c_vk * D5 := by
    have he : (1 : ℝ) / w = 2 * D4 / c_vk := by rw [hwdef, one_div_div]; ring
    rw [he, show (2 : ℝ) / c_vk * D5 = 2 * D5 / c_vk by ring, div_le_div_iff₀ hc_vk0 hc_vk0]
    nlinarith [hD4leD5, hc_vk0]
  have hLhoriz : ∀ x τ : ℝ, σ₀ ≤ x → x ≤ c → |τ| = Tp →
      ‖(- logDeriv (LFunction ψ) (((x : ℂ) + (τ : ℂ) * I) - (u : ℂ) * I))‖ ≤ Cζ * D5 := by
    intro x τ hxl hxu hτ
    have hs'eq : ((x : ℂ) + (τ : ℂ) * I) - (u : ℂ) * I
        = (x : ℂ) + ((τ - u : ℝ) : ℂ) * I := by push_cast; ring
    have hτule : |τ - u| ≤ 5 * T := by
      have hb := abs_le.mp hu
      rw [abs_le]; rw [abs_eq (by linarith [hTp0] : (0 : ℝ) ≤ Tp)] at hτ
      rcases hτ with h | h <;> rw [hTpdef] at h <;> constructor <;> nlinarith [hb.1, hb.2]
    rw [hs'eq, norm_neg]
    by_cases hx1w : x ≤ 1 + w
    · have hedgeb := hedgeT x (τ - u) hxl hx1w hτule
      have hCζge : CE * D5 ≤ Cζ * D5 := by
        refine mul_le_mul_of_nonneg_right ?_ hD5pos.le
        rw [hCζdef]; have h1 : (0 : ℝ) < 2 / c_vk := by positivity
        linarith [abs_nonneg C₀z]
      linarith [hedgeb, hCζge]
    · rw [not_le] at hx1w
      have hx1 : (1 : ℝ) < x := by linarith [hw0]
      have h1w1 : (1 : ℝ) < 1 + w := by linarith [hw0]
      have hcl := norm_logDeriv_LFunction_cline_le ψ hx1 (τ - u)
      have hmono : (∑' n, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ x)
          ≤ ∑' n, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + w) := by
        refine (summable_vonMangoldt_div_rpow hx1).tsum_le_tsum (fun n => ?_)
          (summable_vonMangoldt_div_rpow h1w1)
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · have hle : (n : ℝ) ^ (1 + w) ≤ (n : ℝ) ^ x :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
          exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
            (Real.rpow_pos_of_pos (by exact_mod_cast hn) _) hle
      have hpole1w := sum_vonMangoldt_le_pole_add_Zc h1w1
      have hZc1w : ‖logDeriv Zc ((1 + w : ℝ) : ℂ)‖ ≤ |C₀z| := by
        refine le_trans (hcptZ ((1 + w : ℝ) : ℂ) ?_ ?_ ?_) (le_abs_self C₀z)
        · simp; linarith [hw0, hδ₀0]
        · simp; linarith [hwle]
        · simp
      have hpole1w2 : (1 : ℝ) / ((1 + w) - 1) = 1 / w := by ring_nf
      refine le_trans hcl ?_
      calc (∑' n, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ x)
          ≤ ∑' n, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + w) := hmono
        _ ≤ 1 / ((1 + w) - 1) + ‖logDeriv Zc ((1 + w : ℝ) : ℂ)‖ := hpole1w
        _ ≤ 1 / w + |C₀z| := by rw [hpole1w2]; linarith [hZc1w]
        _ ≤ 2 / c_vk * D5 + |C₀z| * D5 := by
            have h1 : |C₀z| ≤ |C₀z| * D5 := by nlinarith [abs_nonneg C₀z, hD51]
            linarith [h1w_inv, h1]
        _ ≤ Cζ * D5 := by rw [hCζdef]; nlinarith [hD5pos, hCE0]
  have hkerhoriz : ∀ x τ : ℝ, σ₀ ≤ x → x ≤ c → |τ| = Tp →
      ‖windowMellin P ((x : ℂ) + (τ : ℂ) * I)‖ ≤ Kc * P / (9 * T ^ 2) := by
    intro x τ hxl hxu hτ
    rw [← windowKernel_eq_windowMellin]
    have hx0 : 0 < x := by linarith [hσ₀0]
    refine le_trans (norm_windowKernel_le hP hx0 τ) ?_
    have hτ2 : τ ^ 2 = 9 * T ^ 2 := by
      have hsq : |τ| ^ 2 = τ ^ 2 := sq_abs τ
      rw [← hsq, hτ, hTpdef]; ring
    have hCkx : 2 * (2 * P + P) ^ (x + 1) / P + 2 * (P / 2 + P / 2) ^ (x + 1) / (P / 2)
        ≤ Kc * P := by
      have h3Px : ((3 : ℝ) * P) ^ (x + 1) = (3 : ℝ) ^ (x + 1) * (P : ℝ) ^ (x + 1) :=
        Real.mul_rpow (by norm_num) hP0.le
      have hPx1 : (P : ℝ) ^ (x + 1) = (P : ℝ) ^ x * P := by
        rw [Real.rpow_add hP0, Real.rpow_one]
      have e1 : 2 * (2 * P + P) ^ (x + 1) / P = 2 * (3 : ℝ) ^ (x + 1) * (P : ℝ) ^ x := by
        rw [show 2 * P + P = 3 * P by ring, h3Px, hPx1]; field_simp
      have e2 : 2 * (P / 2 + P / 2) ^ (x + 1) / (P / 2) = 4 * (P : ℝ) ^ x := by
        rw [show P / 2 + P / 2 = P by ring, hPx1]; field_simp; ring
      rw [e1, e2]
      have hlog2P : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
      have hxc : x + 1 ≤ 2 + (Real.log 2)⁻¹ := by
        have hh : (Real.log P)⁻¹ ≤ (Real.log 2)⁻¹ := inv_anti₀ hlog2 hlog2P
        rw [hcdef] at hxu; linarith
      have h3x : (3 : ℝ) ^ (x + 1) ≤ 9 * (3 : ℝ) ^ ((Real.log 2)⁻¹) := by
        rw [show (9 : ℝ) * (3 : ℝ) ^ ((Real.log 2)⁻¹) = (3 : ℝ) ^ (2 + (Real.log 2)⁻¹) by
          rw [Real.rpow_add (by norm_num),
            show (3 : ℝ) ^ (2 : ℝ) = 9 by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hxc
      have hPxc : (P : ℝ) ^ x ≤ Real.exp 1 * P := by
        have hPc : (P : ℝ) ^ c = Real.exp 1 * P := by
          rw [hcdef, Real.rpow_add hP0, Real.rpow_one, mul_comm]; congr 1
          rw [Real.rpow_def_of_pos hP0, mul_inv_cancel₀ hlogP.ne']
        calc (P : ℝ) ^ x ≤ (P : ℝ) ^ c := Real.rpow_le_rpow_of_exponent_le (by linarith [hP]) hxu
          _ = Real.exp 1 * P := hPc
      have hPxnn : (0 : ℝ) ≤ (P : ℝ) ^ x := Real.rpow_nonneg hP0.le x
      rw [hKcdef]
      nlinarith [h3x, hPxc, hPxnn, Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) ((Real.log 2)⁻¹),
        mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) ((Real.log 2)⁻¹)) hP0.le]
    have hinv : (x ^ 2 + τ ^ 2)⁻¹ ≤ (9 * T ^ 2)⁻¹ := by
      rw [hτ2]; apply inv_anti₀ (by positivity); nlinarith [sq_nonneg x]
    calc (2 * (2 * P + P) ^ (x + 1) / P + 2 * (P / 2 + P / 2) ^ (x + 1) / (P / 2))
            * (x ^ 2 + τ ^ 2)⁻¹
        ≤ (Kc * P) * (9 * T ^ 2)⁻¹ :=
          mul_le_mul hCkx hinv (by positivity) (by positivity)
      _ = Kc * P / (9 * T ^ 2) := by ring
  have hFhoriz : ∀ τ : ℝ, |τ| = Tp → ∀ x ∈ Set.uIoc σ₀ c,
      ‖F ((x : ℂ) + (τ : ℂ) * I)‖ ≤ Cζ * D5 * (Kc * P / (9 * T ^ 2)) := by
    intro τ hτ x hx
    rw [Set.uIoc_of_le (by linarith : σ₀ ≤ c), Set.mem_Ioc] at hx
    rw [hFdef]; simp only; rw [norm_mul]
    exact mul_le_mul (hLhoriz x τ (le_of_lt hx.1) hx.2 hτ) (hkerhoriz x τ (le_of_lt hx.1) hx.2 hτ)
      (norm_nonneg _) (by positivity)
  have hcσ₀w : c - σ₀ ≤ 1 / Real.log 2 + 1 / 2 := by
    have hlogPinv : (Real.log P)⁻¹ ≤ (Real.log 2)⁻¹ :=
      inv_anti₀ hlog2 (Real.log_le_log (by norm_num) hP)
    rw [hcdef, hσ₀def, one_div]; linarith [hlogPinv, hwle]
  have hCbnd_nn : (0 : ℝ) ≤ Cζ * D5 * (Kc * P / (9 * T ^ 2)) := by positivity
  have hTOPb : ‖TOP‖ ≤ CH * D5 * P / T ^ 2 := by
    rw [hTOPdef]
    have hτ : |Tp| = Tp := abs_of_pos hTp0
    calc ‖∫ x in σ₀..c, F ((x : ℂ) + (Tp : ℂ) * I)‖
        ≤ (Cζ * D5 * (Kc * P / (9 * T ^ 2))) * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hFhoriz Tp hτ)
      _ ≤ (Cζ * D5 * (Kc * P / (9 * T ^ 2))) * (1 / Real.log 2 + 1 / 2) := by
          apply mul_le_mul_of_nonneg_left _ hCbnd_nn
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c - σ₀)]; exact hcσ₀w
      _ = CH * D5 * P / T ^ 2 := by rw [hCHdef]; field_simp
  have hBOTb : ‖BOT‖ ≤ CH * D5 * P / T ^ 2 := by
    rw [hBOTdef]
    have hτ : |(-Tp : ℝ)| = Tp := by rw [abs_neg]; exact abs_of_pos hTp0
    calc ‖∫ x in σ₀..c, F ((x : ℂ) + ((-Tp : ℝ) : ℂ) * I)‖
        ≤ (Cζ * D5 * (Kc * P / (9 * T ^ 2))) * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hFhoriz (-Tp) hτ)
      _ ≤ (Cζ * D5 * (Kc * P / (9 * T ^ 2))) * (1 / Real.log 2 + 1 / 2) := by
          apply mul_le_mul_of_nonneg_left _ hCbnd_nn
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c - σ₀)]; exact hcσ₀w
      _ = CH * D5 * P / T ^ 2 := by rw [hCHdef]; field_simp
  have hTAILb : ‖TAILval‖ ≤ CT * P * Real.log P / T := by
    have hsuma : (∑' n, ‖a n‖ / (n : ℝ) ^ c) ≤ Real.log P + C₀ := by
      have hle : (∑' n, ‖a n‖ / (n : ℝ) ^ c)
          ≤ ∑' n, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c := by
        refine hsum.tsum_le_tsum (fun n => ?_) (summable_vonMangoldt_div_rpow hc1)
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [ha0]; simp
        · have hpos : (0 : ℝ) < (n : ℝ) ^ c := Real.rpow_pos_of_pos (by exact_mod_cast hn) c
          rw [div_le_div_iff_of_pos_right hpos]; exact hnorm_a n
      have hb : (∑' n, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) ≤ Real.log P + C₀ := by
        rw [hcdef]; exact hcline hP
      linarith
    have hsuma0 : (0 : ℝ) ≤ ∑' n, ‖a n‖ / (n : ℝ) ^ c := tsum_nonneg (fun n => by positivity)
    have hCk : (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2))
        ≤ Kc * P := by rw [hcdef, hKcdef]; exact truncKernel_const_le hP
    have hCk0 : (0 : ℝ) ≤ 2 * (2 * P + P) ^ (c + 1) / P
        + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2) := by
      have hPP : (0 : ℝ) < P := hP0; positivity
    have h2Tp : (2 : ℝ) / Tp = 2 / (3 * T) := by rw [hTpdef]
    have hstep : (∑' n, ‖a n‖ / (n : ℝ) ^ c)
          * (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2)) * (2 / Tp)
        ≤ (Real.log P + C₀) * (Kc * P) * (2 / (3 * T)) := by
      rw [h2Tp]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hsuma hCk hCk0 (by linarith [hlogP, hC₀0])) (by positivity)
    have hkeylog : Real.log P + C₀ ≤ (1 + C₀ / Real.log 2) * Real.log P := by
      have hlog2P : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
      have hh : C₀ * Real.log 2 ≤ C₀ * Real.log P := by nlinarith [hC₀0, hlog2P]
      rw [add_mul, one_mul, div_mul_eq_mul_div]
      have hkk : C₀ ≤ C₀ * Real.log P / Real.log 2 := by rw [le_div_iff₀ hlog2]; linarith [hh]
      linarith
    refine le_trans hTAILnorm (le_trans hstep ?_)
    calc (Real.log P + C₀) * (Kc * P) * (2 / (3 * T))
        ≤ ((1 + C₀ / Real.log 2) * Real.log P) * (Kc * P) * (2 / (3 * T)) := by
          apply mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hkeylog (by positivity)) (by positivity)
      _ = CT * P * Real.log P / T := by rw [hCTdef]; field_simp
  -- === assemble ===
  rw [hbridge, hInt_split, hrearr, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have htri : ‖LEFT - I * (TOP - BOT) + TAILval‖ ≤ ‖LEFT‖ + ‖TOP‖ + ‖BOT‖ + ‖TAILval‖ := by
    calc ‖LEFT - I * (TOP - BOT) + TAILval‖
        ≤ ‖LEFT - I * (TOP - BOT)‖ + ‖TAILval‖ := norm_add_le _ _
      _ ≤ (‖LEFT‖ + ‖I * (TOP - BOT)‖) + ‖TAILval‖ := by
          linarith [norm_sub_le LEFT (I * (TOP - BOT))]
      _ = ‖LEFT‖ + ‖TOP - BOT‖ + ‖TAILval‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ‖LEFT‖ + ‖TOP‖ + ‖BOT‖ + ‖TAILval‖ := by linarith [norm_sub_le TOP BOT]
  have hN : ‖LEFT - I * (TOP - BOT) + TAILval‖
      ≤ CL * P * Real.exp (-(c_vk / 2) * Real.log P / D4) * D5
        + CT * P * Real.log P / T + 2 * CH * D5 * P / T ^ 2 := by
    calc ‖LEFT - I * (TOP - BOT) + TAILval‖
        ≤ ‖LEFT‖ + ‖TOP‖ + ‖BOT‖ + ‖TAILval‖ := htri
      _ ≤ (CL * P * Real.exp (-(c_vk / 2) * Real.log P / D4) * D5)
            + (CH * D5 * P / T ^ 2) + (CH * D5 * P / T ^ 2) + (CT * P * Real.log P / T) := by
          linarith [hLEFTb, hTOPb, hBOTb, hTAILb]
      _ = CL * P * Real.exp (-(c_vk / 2) * Real.log P / D4) * D5
            + CT * P * Real.log P / T + 2 * CH * D5 * P / T ^ 2 := by ring
  calc (1 / (2 * Real.pi)) * ‖LEFT - I * (TOP - BOT) + TAILval‖
      ≤ (1 / (2 * Real.pi)) * (CL * P * Real.exp (-(c_vk / 2) * Real.log P / D4) * D5
          + CT * P * Real.log P / T + 2 * CH * D5 * P / T ^ 2) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ = CL / (2 * Real.pi) * P * Real.exp (-(c_vk / 2) * Real.log P / D4) * D5
          + CT / (2 * Real.pi) * P * Real.log P / T
          + 2 * CH / (2 * Real.pi) * D5 * P / T ^ 2 := by ring

end Salt.MR

end
