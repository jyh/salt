/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.MaxModulus

/-!
# The SW rung, node Z2ζ — the ζ partial-fraction / zero-theory mirror

Design: `docs/blueprints/sw.md`, wave S3 (the quantitative zero-free region), the flag
"SW S3d" in `docs/blueprints/flags.md`. This module supplies the ζ log-derivative bound at
complex `s = σ + 2iγ` that the real-character complex-zero case (S3d-b) of the zero-free region
consumes: the honest pole term with its complex real part, plus an `O(log(|γ|+2))` remainder.

The Dirichlet L-function pipeline (`Salt/SW/ZeroCount.lean` … `Salt/SW/MaxModulus.lean`) explicitly
excludes the trivial character (`χ ≠ 1`, because `ζ` has a pole at `1`). We recover the ζ case by
factoring out the pole: `Zc s := (s−1)·ζ(s)` is entire (removable singularity, value `1` at `s=1`),
and `logDeriv ζ = logDeriv Zc − 1/(s−1)` wherever `ζ ≠ 0`, `s ≠ 1`. The S2 machinery then applies to
`Zc` on balls centered `c = 2 + 2iγ`: zeros of `Zc` are zeros of `ζ` (with `Zc(1) = 1 ≠ 0`), all in
`Re < 1 < σ`, so their partial-fraction terms are `≥ 0` and drop for an upper bound, leaving the
`120·log(4M₀)` Borel–Carathéodory remainder.

## Mathlib consumed
* `riemannZeta_ne_zero_of_one_le_re` (ζ ≠ 0 on `Re ≥ 1`), `differentiableAt_riemannZeta`,
  `riemannZeta_residue_one` ((s−1)ζ → 1 at 1), the removable-singularity theorem
  `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` (entireness of `Zc`),
  and `LFunction_modOne_eq` (`ζ = LFunction 1 mod 1`, for the center bound).
* Reused corpus abstractions (generic in the base function): `norm_logDeriv_sub_sum_of_blaschke`,
  `reflectedFactor`/`norm_reflectedFactor_eq_on_sphere`, `norm_deriv_le_of_re_le`,
  `neg_re_logDeriv_le`, `logDeriv_prod_pow`, `LFunction_center_lower`.

Mathlib has **no** complex ζ growth bound on vertical strips; that (`Zc_growth`) is built here.
-/

namespace Salt.SW

open Complex Metric MeromorphicOn Function DirichletCharacter Set Filter
open scoped Topology

/-! ## 1. The entire function `Zc = (s−1)·ζ(s)` and the pole split -/

/-- `Zc s = (s−1)·ζ(s)`, extended entire by the removable singularity at `s = 1` (value `1`). -/
noncomputable def Zc : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1

lemma Zc_one : Zc 1 = 1 := Function.update_self 1 1 _

lemma Zc_eq_of_ne {s : ℂ} (hs : s ≠ 1) : Zc s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

lemma Zc_differentiableAt_of_ne {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ Zc s := by
  have hprod : DifferentiableAt ℂ (fun z => (z - 1) * riemannZeta z) s :=
    (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)
  have hloc : Zc =ᶠ[𝓝 s] (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
    exact Zc_eq_of_ne (by simpa using hz)
  exact hprod.congr_of_eventuallyEq hloc

lemma Zc_continuousAt_one : ContinuousAt Zc 1 := by
  rw [← continuousWithinAt_compl_self]
  have hEq : (fun s => (s - 1) * riemannZeta s) =ᶠ[𝓝[≠] 1] Zc := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (Zc_eq_of_ne hz).symm
  have : Tendsto Zc (𝓝[≠] 1) (𝓝 1) := riemannZeta_residue_one.congr' hEq
  simpa [ContinuousWithinAt, Zc_one] using this

lemma Zc_analyticAt_one : AnalyticAt ℂ Zc 1 := by
  apply analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ Zc_continuousAt_one
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact Zc_differentiableAt_of_ne hz

lemma Zc_differentiable : Differentiable ℂ Zc := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · exact Zc_analyticAt_one.differentiableAt
  · exact Zc_differentiableAt_of_ne hs

/-- The pole split: on `ζ s ≠ 0`, `s ≠ 1`, `logDeriv ζ = logDeriv Zc − 1/(s−1)`. -/
lemma logDeriv_zeta_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s = logDeriv Zc s - 1 / (s - 1) := by
  have hs1 : (s : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hloc : Zc =ᶠ[𝓝 s] (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz'
    exact Zc_eq_of_ne (by simpa using hz')
  have hlogZc : logDeriv Zc s = logDeriv (fun z => (z - 1) * riemannZeta z) s := by
    simp only [logDeriv_apply, hloc.deriv_eq, hloc.eq_of_nhds]
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := differentiableAt_id.sub_const 1
  have hd2 : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs
  have hmul : logDeriv (fun z => (z - 1) * riemannZeta z) s
      = logDeriv (fun z : ℂ => z - 1) s + logDeriv riemannZeta s :=
    logDeriv_mul s hs1 hz hd1 hd2
  have hlin : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply, deriv_sub_const]; simp
  rw [hlogZc, hmul, hlin]; ring

/-- The real-part form of the pole split, ready for S3d-b. -/
lemma neg_logDeriv_zeta_split {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    (-logDeriv riemannZeta s).re = (1 / (s - 1)).re + (-logDeriv Zc s).re := by
  rw [logDeriv_zeta_eq hs hz,
    show -(logDeriv Zc s - 1 / (s - 1)) = 1 / (s - 1) - logDeriv Zc s by ring,
    Complex.sub_re, Complex.neg_re]; ring

/-! ## 2. The center lower bound `‖Zc c‖ ≥ 1/4` at `c = 2 + 2iγ` -/

/-- `‖ζ(s)‖ ≥ 1/4` for `Re s ≥ 2`, obtained from the Dirichlet-character center lower bound
(`LFunction_center_lower`) via `LFunction 1 = riemannZeta` for the modulus-1 character. -/
lemma zeta_norm_ge {s : ℂ} (hs : 2 ≤ s.re) : (1 : ℝ) / 4 ≤ ‖riemannZeta s‖ := by
  have h := LFunction_center_lower (q := 1) (1 : DirichletCharacter ℂ 1) hs
  simpa only [LFunction_modOne_eq] using h

/-- **Center lower bound for `Zc`.** At `c = 2 + (t₀)i`, `‖Zc c‖ ≥ 1/4` (here `‖c−1‖ ≥ 1` and
`‖ζ(c)‖ ≥ 1/4`). -/
lemma Zc_center_lower (t₀ : ℝ) : (1 : ℝ) / 4 ≤ ‖Zc (2 + (t₀ : ℂ) * I)‖ := by
  set c : ℂ := 2 + (t₀ : ℂ) * I with hc
  have hcre : c.re = 2 := by rw [hc]; simp
  have hcne : c ≠ 1 := fun h => by rw [h, Complex.one_re] at hcre; norm_num at hcre
  have hZcc : Zc c = (c - 1) * riemannZeta c := Zc_eq_of_ne hcne
  have hz : (1 : ℝ) / 4 ≤ ‖riemannZeta c‖ := zeta_norm_ge (le_of_eq hcre.symm)
  have hc1 : (1 : ℝ) ≤ ‖c - 1‖ := by
    have h := Complex.abs_re_le_norm (c - 1)
    have hre : (c - 1).re = 1 := by rw [Complex.sub_re, hcre, Complex.one_re]; norm_num
    rw [hre] at h; simpa using h
  rw [hZcc, norm_mul]
  calc (1 : ℝ) / 4 = 1 * (1 / 4) := by ring
    _ ≤ ‖c - 1‖ * ‖riemannZeta c‖ := mul_le_mul hc1 hz (by norm_num) (by linarith [hc1])

/-! ## 3. The generic Jensen zero count (mirror of `LFunction_zero_count_le`, entire base) -/

/-- **Generic Jensen zero count.** For an entire `F` with `‖F c‖ ≥ 1/4`, if `‖F‖ ≤ M` (`M ≥ 1`) on
the sphere `|z − c| = R`, then the multiplicity-counted zeros of `F` in `closedBall c r`
(`0 < r < R`) number `≤ log(4M)/log(R/r)`. Route: the Nevanlinna keystone
`AnalyticOnNhd.sum_divisor_le`, center value folded into `4M`. Mirrors `LFunction_zero_count_le`. -/
theorem entire_zero_count_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c : ℂ}
    (hFc : (1 : ℝ) / 4 ≤ ‖F c‖) {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hbnd : ∀ z ∈ sphere c R, ‖F z‖ ≤ M) :
    ((∑ᶠ u, divisor F (closedBall c r) u : ℤ) : ℝ) ≤ Real.log (4 * M) / Real.log (R / r) := by
  have hRpos : 0 < R := hr.trans hrR
  have habsr : |r| = r := abs_of_pos hr
  have habsR : |R| = R := abs_of_pos hRpos
  have hcnorm : (0 : ℝ) < ‖F c‖ := by linarith
  have hcne : F c ≠ 0 := by intro h; rw [h, norm_zero] at hcnorm; exact lt_irrefl 0 hcnorm
  have hana : AnalyticOnNhd ℂ F (closedBall c |R|) :=
    (hF.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hjensen := hana.sum_divisor_le (by rw [habsr]; exact hr) (by rw [habsr, habsR]; exact hrR)
    hM hcne (by rw [habsR]; exact hbnd)
  rw [habsr] at hjensen
  refine le_trans hjensen ?_
  have hRr : 1 < R / r := (one_lt_div hr).mpr hrR
  have hlogpos : 0 < Real.log (R / r) := Real.log_pos hRr
  have hMpos : (0 : ℝ) < M := by linarith
  have hle1 : M / ‖F c‖ ≤ 4 * M := by rw [div_le_iff₀ hcnorm]; nlinarith [hFc, hMpos]
  have hlog : Real.log (M / ‖F c‖) ≤ Real.log (4 * M) :=
    Real.log_le_log (div_pos hMpos hcnorm) hle1
  rw [div_le_div_iff_of_pos_right hlogpos]
  exact hlog

/-! ## 4. The generic ungated `L'/L − ∑ 1/(s−ρ)` numeric (mirror of `MaxModulus`, entire base) -/

/-- **Generic ungated Landau numeric.** For an entire `F` with center lower bound `‖F c‖ ≥ 1/4` and
sphere sup bounds `‖F‖ ≤ M₀` (`M₀ ≥ 1`) on the spheres `|z−c| = 7/4` and `|z−c| = 3/2`, there is a
finite zero set `Z` (multiplicities `m`) and an analytic non-vanishing remainder `h` with the
partial-fraction invariants, and — unconditionally — the numeric bound
`‖F'/F(s) − ∑_ρ m_ρ/(s−ρ)‖ ≤ 120·log(4 M₀)` for `‖s−c‖ ≤ 23/20`, `F s ≠ 0`.

This is `Salt.SW.LFunction_norm_logDeriv_sub_sum'` with the Dirichlet L-function replaced by an
arbitrary entire base `F`: `differentiable_LFunction` becomes `hF`, `LFunction_center_lower` becomes
`hFc`, the growth sphere/ball bounds become `hsphere74`/`hsphere32`, and the Jensen count becomes
`entire_zero_count_le`. The Blaschke maximum-modulus argument (re-factoring at radius `8/5`) is
carried over verbatim. -/
theorem entire_norm_logDeriv_sub_sum' {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c : ℂ} {M₀ : ℝ}
    (hM₀ : 1 ≤ M₀) (hFc : (1 : ℝ) / 4 ≤ ‖F c‖)
    (hsphere74 : ∀ z ∈ sphere c (7 / 4), ‖F z‖ ≤ M₀)
    (hsphere32 : ∀ z ∈ sphere c (3 / 2), ‖F z‖ ≤ M₀) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ ρ ∈ Z, ρ ∈ ball c (3 / 2) ∧ F ρ = 0) ∧
      AnalyticOnNhd ℂ h (ball c (3 / 2)) ∧
      (∀ z ∈ ball c (3 / 2), h z ≠ 0) ∧
      Set.EqOn F (fun z => (∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) * h z) (ball c (3 / 2)) ∧
      (∀ s ∈ ball c (3 / 2), F s ≠ 0 →
        logDeriv F s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) = logDeriv h s) ∧
      (∀ s, ‖s - c‖ ≤ 23 / 20 → F s ≠ 0 →
        ‖logDeriv F s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ 120 * Real.log (4 * M₀)) := by
  classical
  have hFc0 : F c ≠ 0 := by intro h0; rw [h0, norm_zero] at hFc; linarith
  -- Inlined factorization at radius `8/5` (exposing `m₈ = divisor.toNat`)
  set U : Set ℂ := ball c (8 / 5) with hU
  have hUo : IsOpen U := isOpen_ball
  have hpre : IsPreconnected U := (convex_ball c (8 / 5)).isPreconnected
  have hcU : c ∈ U := mem_ball_self (by norm_num)
  have hana_univ : AnalyticOnNhd ℂ F univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  have hana : AnalyticOnNhd ℂ F U := hana_univ.mono (subset_univ _)
  have h₂f : ∀ u : U, meromorphicOrderAt F (u : ℂ) ≠ ⊤ := by
    intro u htop
    rw [meromorphicOrderAt_eq_top_iff] at htop
    have hfreq : ∃ᶠ z in 𝓝[≠] (u : ℂ), F z = 0 := htop.frequently
    have hz : Set.EqOn F 0 U :=
      hana.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre u.2 hfreq
    exact hFc0 (hz hcU)
  have h₃f : (divisor F U).support.Finite :=
    divisor_ball_support_finite (hana_univ.mono (subset_univ _)).meromorphicOn
  obtain ⟨g₈, hg₈_ana, hg₈_ne, hg₈_eq⟩ := hana.meromorphicOn.extract_zeros_poles h₂f h₃f
  set Z₈ : Finset ℂ := h₃f.toFinset with hZ₈
  set m₈ : ℂ → ℕ := fun ρ => ((divisor F U) ρ).toNat with hm₈
  have hdivnn : ∀ u, 0 ≤ (divisor F U) u := hana.divisor_nonneg
  set P₈ : ℂ → ℂ := fun z => ∏ ρ ∈ Z₈, (z - ρ) ^ (m₈ ρ) with hP₈
  have hsub : mulSupport (fun u : ℂ => ((· - u) ^ (divisor F U u) : ℂ → ℂ)) ⊆ ↑Z₈ := by
    intro u hu
    simp only [hZ₈, Finite.coe_toFinset, Function.mem_support]
    intro hd0; apply hu; simp [hd0]
  have hfun : (∏ᶠ u, ((· - u) ^ (divisor F U u) : ℂ → ℂ)) = P₈ := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    funext z; rw [hP₈]
    simp only [Finset.prod_apply, Pi.pow_apply]
    apply Finset.prod_congr rfl; intro u _
    rw [← Int.toNat_of_nonneg (hdivnn u), zpow_natCast]
  have hg_eq2 : F =ᶠ[codiscreteWithin U] (fun z => P₈ z * g₈ z) := by
    filter_upwards [hg₈_eq] with z hz
    rw [hz, hfun]; simp [Pi.smul_apply', smul_eq_mul]
  have hP₈_ana : AnalyticOnNhd ℂ P₈ U := by
    rw [hP₈]
    exact Finset.analyticOnNhd_fun_prod Z₈ (fun ρ _ => by
      apply AnalyticOnNhd.pow; exact (analyticOnNhd_id.sub analyticOnNhd_const))
  have hP₈g_ana : AnalyticOnNhd ℂ (fun z => P₈ z * g₈ z) U := hP₈_ana.mul hg₈_ana
  have hev : ∀ᶠ z in 𝓝[≠] c, F z = P₈ z * g₈ z := by
    have h1 : ({z | F z = P₈ z * g₈ z} ∪ Uᶜ) ∈ 𝓝[≠] c :=
      mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hg_eq2 c hcU
    have h2 : U ∈ 𝓝[≠] c := mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hcU)
    filter_upwards [h1, h2] with z hz hzU
    rcases hz with hz | hz
    · exact hz
    · exact absurd hzU hz
  have hEqOn₈ : Set.EqOn F (fun z => P₈ z * g₈ z) U :=
    hana.eqOn_of_preconnected_of_frequently_eq hP₈g_ana hpre hcU hev.frequently
  have hg₈_ne' : ∀ z ∈ U, g₈ z ≠ 0 := fun z hz => hg₈_ne ⟨z, hz⟩
  have hmemZ₈ : ∀ ρ ∈ Z₈, ρ ∈ U ∧ F ρ = 0 := by
    intro ρ hρ
    have hρsupp : (divisor F U) ρ ≠ 0 := by
      rw [hZ₈, Finite.mem_toFinset, Function.mem_support] at hρ; exact hρ
    have hρU : ρ ∈ U := by
      by_contra hnU
      exact hρsupp (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hnU)
    refine ⟨hρU, ?_⟩
    by_contra hne0
    apply hρsupp
    rw [hana.divisor_apply hρU, (hana ρ hρU).analyticOrderAt_eq_zero.mpr hne0]; simp
  -- Regrouping the zeros `Z₈ = Z' ⊔ Zout` and the witness `h' = g₈·Pout`
  set Z' : Finset ℂ := Z₈.filter (fun ρ => ρ ∈ ball c (3 / 2)) with hZ'
  set Zout : Finset ℂ := Z₈.filter (fun ρ => ρ ∉ ball c (3 / 2)) with hZout
  set Pout : ℂ → ℂ := fun z => ∏ ρ ∈ Zout, (z - ρ) ^ (m₈ ρ) with hPout
  set h' : ℂ → ℂ := fun z => g₈ z * Pout z with hh'
  have hZ'mem : ∀ ρ ∈ Z', ρ ∈ ball c (3 / 2) := fun ρ hρ => (Finset.mem_filter.mp hρ).2
  have hZ'sub : ∀ ρ ∈ Z', ρ ∈ Z₈ := fun ρ hρ => (Finset.mem_filter.mp hρ).1
  have hZoutmem : ∀ ρ ∈ Zout, ρ ∉ ball c (3 / 2) := fun ρ hρ => (Finset.mem_filter.mp hρ).2
  have hball32_U : ball c (3 / 2) ⊆ U := by rw [hU]; exact ball_subset_ball (by norm_num)
  have hcb32_U : closedBall c (3 / 2) ⊆ U := by rw [hU]; exact closedBall_subset_ball (by norm_num)
  have inv_memb : ∀ ρ ∈ Z', ρ ∈ ball c (3 / 2) ∧ F ρ = 0 :=
    fun ρ hρ => ⟨hZ'mem ρ hρ, (hmemZ₈ ρ (hZ'sub ρ hρ)).2⟩
  have hPout_ana : AnalyticOnNhd ℂ Pout U := by
    rw [hPout]
    exact Finset.analyticOnNhd_fun_prod Zout (fun ρ _ => by
      apply AnalyticOnNhd.pow; exact (analyticOnNhd_id.sub analyticOnNhd_const))
  have hh'_ana_U : AnalyticOnNhd ℂ h' U := by rw [hh']; exact hg₈_ana.mul hPout_ana
  have inv_ana : AnalyticOnNhd ℂ h' (ball c (3 / 2)) := hh'_ana_U.mono hball32_U
  have hPout_ne : ∀ z ∈ ball c (3 / 2), Pout z ≠ 0 := by
    intro z hz
    rw [hPout]; apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ; apply pow_ne_zero; rw [sub_ne_zero]
    intro heq; exact (hZoutmem ρ hρ) (heq ▸ hz)
  have inv_ne : ∀ z ∈ ball c (3 / 2), h' z ≠ 0 := by
    intro z hz; rw [hh']; exact mul_ne_zero (hg₈_ne' z (hball32_U hz)) (hPout_ne z hz)
  have hP'_ana : AnalyticOnNhd ℂ (fun z => ∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) U :=
    Finset.analyticOnNhd_fun_prod Z' (fun ρ _ => by
      apply AnalyticOnNhd.pow; exact (analyticOnNhd_id.sub analyticOnNhd_const))
  have hsplit_prod : ∀ z : ℂ, P₈ z = (∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) * Pout z := by
    intro z
    rw [hP₈, hPout, hZ', hZout]
    exact (Finset.prod_filter_mul_prod_filter_not Z₈ (fun ρ => ρ ∈ ball c (3 / 2))
      (fun ρ => (z - ρ) ^ (m₈ ρ))).symm
  have inv_eqon : Set.EqOn F (fun z => (∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) * h' z) (ball c (3 / 2)) := by
    intro z hz
    have hEz : F z = P₈ z * g₈ z := hEqOn₈ (hball32_U hz)
    rw [hEz, hsplit_prod z]
    change (∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) * Pout z * g₈ z
      = (∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) * (g₈ z * Pout z)
    ring
  have inv_ident : ∀ s ∈ ball c (3 / 2), F s ≠ 0 →
      logDeriv F s - ∑ ρ ∈ Z', (m₈ ρ : ℂ) / (s - ρ) = logDeriv h' s := by
    intro s hsU hsne
    have hsρ : ∀ ρ ∈ Z', s ≠ ρ := by
      intro ρ hρ hsρ; exact hsne (hsρ ▸ (hmemZ₈ ρ (hZ'sub ρ hρ)).2)
    have hP's : (∏ ρ ∈ Z', (s - ρ) ^ (m₈ ρ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hsρ ρ hρ))
    have hh's : h' s ≠ 0 := inv_ne s hsU
    have hlocal : F =ᶠ[𝓝 s] (fun z => (∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) * h' z) := by
      filter_upwards [(isOpen_ball (x := c) (ε := 3 / 2)).mem_nhds hsU] with z hz
      exact inv_eqon hz
    have hlogL : logDeriv F s
        = logDeriv (fun z => (∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) * h' z) s := by
      rw [logDeriv_apply, logDeriv_apply, hlocal.deriv_eq, hlocal.eq_of_nhds]
    have hlogmul : logDeriv (fun z => (∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) * h' z) s
        = logDeriv (fun z => ∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) s + logDeriv h' s :=
      logDeriv_mul s hP's hh's ((hP'_ana s (hball32_U hsU)).differentiableAt)
        ((hh'_ana_U s (hball32_U hsU)).differentiableAt)
    have hlogP' : logDeriv (fun z => ∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) s
        = ∑ ρ ∈ Z', (m₈ ρ : ℂ) / (s - ρ) := logDeriv_prod_pow Z' m₈ hsρ
    rw [hlogL, hlogmul, hlogP']; ring
  -- the zero count with the exact `log(7/6)` constant (divisor locality + Jensen)
  have hana32 : AnalyticOnNhd ℂ F (ball c (3 / 2)) := hana_univ.mono (subset_univ _)
  have hana_cb : AnalyticOnNhd ℂ F (closedBall c (3 / 2)) := hana_univ.mono (subset_univ _)
  have hloc : ∀ ρ ∈ Z', (divisor F U) ρ = (divisor F (ball c (3 / 2))) ρ := by
    intro ρ hρ
    rw [hana.meromorphicOn.divisor_apply (hball32_U (hZ'mem ρ hρ)),
        hana32.meromorphicOn.divisor_apply (hZ'mem ρ hρ)]
  have hsupp32 : (Function.support (fun u => divisor F (ball c (3 / 2)) u)) ⊆ ↑Z' := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    have hρ32 : ρ ∈ ball c (3 / 2) := by
      by_contra hn
      exact hρ (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hn)
    have hloc' : (divisor F U) ρ = (divisor F (ball c (3 / 2))) ρ := by
      rw [hana.meromorphicOn.divisor_apply (hball32_U hρ32),
          hana32.meromorphicOn.divisor_apply hρ32]
    have hUne : (divisor F U) ρ ≠ 0 := by rw [hloc']; exact hρ
    have hρZ₈ : ρ ∈ Z₈ := by rw [hZ₈, Finite.mem_toFinset, Function.mem_support]; exact hUne
    rw [hZ', Finset.coe_filter]; exact ⟨hρZ₈, hρ32⟩
  have hcount : (∑ ρ ∈ Z', (m₈ ρ : ℝ)) ≤ Real.log (4 * M₀) / Real.log (7 / 6) := by
    have e1 : (∑ ρ ∈ Z', (m₈ ρ : ℤ)) = ∑ ρ ∈ Z', divisor F (ball c (3 / 2)) ρ := by
      apply Finset.sum_congr rfl; intro ρ hρ
      have hcast : ((m₈ ρ : ℤ)) = divisor F U ρ := Int.toNat_of_nonneg (hdivnn ρ)
      rw [hcast, hloc ρ hρ]
    have e2 : (∑ ρ ∈ Z', divisor F (ball c (3 / 2)) ρ)
        = ∑ᶠ u, divisor F (ball c (3 / 2)) u :=
      (finsum_eq_finsetSum_of_support_subset _ hsupp32).symm
    have hdle : ∀ u : ℂ, divisor F (ball c (3 / 2)) u ≤ divisor F (closedBall c (3 / 2)) u := by
      intro u
      by_cases hu : u ∈ ball c (3 / 2)
      · exact le_of_eq (by rw [hana32.divisor_apply hu,
          hana_cb.divisor_apply (ball_subset_closedBall hu)])
      · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
        exact hana_cb.divisor_nonneg u
    have hfin_ball : (Function.support (fun u => divisor F (ball c (3 / 2)) u)).Finite :=
      divisor_ball_support_finite hana_cb.meromorphicOn
    have hfin_cb : (Function.support (fun u => divisor F (closedBall c (3 / 2)) u)).Finite :=
      (divisor F (closedBall c (3 / 2))).finiteSupport (isCompact_closedBall _ _)
    have hmono : ∑ᶠ u, divisor F (ball c (3 / 2)) u
        ≤ ∑ᶠ u, divisor F (closedBall c (3 / 2)) u :=
      finsum_le_finsum' hfin_ball hfin_cb hdle
    have hcountJ := entire_zero_count_le hF hFc (r := 3 / 2) (R := 7 / 4) (M := M₀)
      (by norm_num) (by norm_num) hM₀ hsphere74
    calc ∑ ρ ∈ Z', (m₈ ρ : ℝ)
        = ((∑ ρ ∈ Z', (m₈ ρ : ℤ) : ℤ) : ℝ) := by push_cast; ring
      _ = ((∑ᶠ u, divisor F (ball c (3 / 2)) u : ℤ) : ℝ) := by rw [e1, e2]
      _ ≤ ((∑ᶠ u, divisor F (closedBall c (3 / 2)) u : ℤ) : ℝ) := by exact_mod_cast hmono
      _ ≤ Real.log (4 * M₀) / Real.log (7 / 4 / (3 / 2)) := hcountJ
      _ = Real.log (4 * M₀) / Real.log (7 / 6) := by
          rw [show (7 : ℝ) / 4 / (3 / 2) = 7 / 6 by norm_num]
  -- `hsup` via the maximum-modulus principle
  have hsup : ∀ z ∈ ball c (3 / 2),
      ‖h' z * ∏ ρ ∈ Z', (reflectedFactor c ρ z) ^ (m₈ ρ)‖ ≤ M₀ := by
    set G : ℂ → ℂ := fun z => h' z * ∏ ρ ∈ Z', (reflectedFactor c ρ z) ^ (m₈ ρ) with hG
    have hrefl_ana : ∀ ρ, AnalyticOnNhd ℂ (reflectedFactor c ρ) U := by
      intro ρ
      have hden : AnalyticOnNhd ℂ (fun _ : ℂ => (3 : ℂ) / 2) U := analyticOnNhd_const
      have hnum : AnalyticOnNhd ℂ
          (fun z : ℂ => (9 : ℂ) / 4 - (starRingEnd ℂ) (ρ - c) * (z - c)) U :=
        analyticOnNhd_const.sub (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))
      exact hnum.div hden (fun z _ => by norm_num)
    have hrefprod_ana :
        AnalyticOnNhd ℂ (fun z => ∏ ρ ∈ Z', (reflectedFactor c ρ z) ^ (m₈ ρ)) U :=
      Finset.analyticOnNhd_fun_prod Z' (fun ρ _ => (hrefl_ana ρ).pow _)
    have hG_ana : AnalyticOnNhd ℂ G U := by rw [hG]; exact hh'_ana_U.mul hrefprod_ana
    have hdcc : DiffContOnCl ℂ G (ball c (3 / 2)) :=
      hG_ana.differentiableOn.diffContOnCl_ball hcb32_U
    have hbdry : ∀ w ∈ frontier (ball c (3 / 2)), ‖G w‖ ≤ M₀ := by
      intro w hw
      rw [frontier_ball c (by norm_num : (3 / 2 : ℝ) ≠ 0), mem_sphere, dist_eq_norm] at hw
      have hwU : w ∈ U := by rw [hU, mem_ball, dist_eq_norm, hw]; norm_num
      have hEw : F w = P₈ w * g₈ w := hEqOn₈ hwU
      have hnorm_refl : ‖∏ ρ ∈ Z', (reflectedFactor c ρ w) ^ (m₈ ρ)‖
          = ∏ ρ ∈ Z', ‖w - ρ‖ ^ (m₈ ρ) := by
        rw [norm_prod]; apply Finset.prod_congr rfl; intro ρ _
        rw [norm_pow, norm_reflectedFactor_eq_on_sphere c ρ hw]
      have hnorm_Pout : ‖Pout w‖ = ∏ ρ ∈ Zout, ‖w - ρ‖ ^ (m₈ ρ) := by
        change ‖∏ ρ ∈ Zout, (w - ρ) ^ (m₈ ρ)‖ = _
        rw [norm_prod]; apply Finset.prod_congr rfl; intro ρ _; rw [norm_pow]
      have hnorm_P₈ : ‖P₈ w‖ = ∏ ρ ∈ Z₈, ‖w - ρ‖ ^ (m₈ ρ) := by
        change ‖∏ ρ ∈ Z₈, (w - ρ) ^ (m₈ ρ)‖ = _
        rw [norm_prod]; apply Finset.prod_congr rfl; intro ρ _; rw [norm_pow]
      have hsplit_norm : (∏ ρ ∈ Z', ‖w - ρ‖ ^ (m₈ ρ)) * (∏ ρ ∈ Zout, ‖w - ρ‖ ^ (m₈ ρ))
          = ∏ ρ ∈ Z₈, ‖w - ρ‖ ^ (m₈ ρ) := by
        rw [hZ', hZout]
        exact Finset.prod_filter_mul_prod_filter_not Z₈ (fun ρ => ρ ∈ ball c (3 / 2)) _
      have hkey_norm : ‖Pout w * ∏ ρ ∈ Z', (reflectedFactor c ρ w) ^ (m₈ ρ)‖ = ‖P₈ w‖ := by
        rw [norm_mul, hnorm_Pout, hnorm_refl, hnorm_P₈, ← hsplit_norm]; ring
      have hGnorm : ‖G w‖ = ‖F w‖ := by
        have hGw : G w = g₈ w * (Pout w * ∏ ρ ∈ Z', (reflectedFactor c ρ w) ^ (m₈ ρ)) := by
          change h' w * (∏ ρ ∈ Z', (reflectedFactor c ρ w) ^ (m₈ ρ)) = _
          rw [show h' w = g₈ w * Pout w from rfl]; ring
        rw [hGw, norm_mul, hkey_norm, mul_comm, ← norm_mul, ← hEw]
      have hLw_bound : ‖F w‖ ≤ M₀ := hsphere32 w (by rw [mem_sphere, dist_eq_norm]; exact hw)
      calc ‖G w‖ = ‖F w‖ := hGnorm
        _ ≤ M₀ := hLw_bound
    intro z hz
    have hzcl : z ∈ closure (ball c (3 / 2)) := by
      rw [closure_ball c (by norm_num : (3 / 2 : ℝ) ≠ 0)]; exact ball_subset_closedBall hz
    exact norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdcc hbdry hzcl
  -- Assemble
  refine ⟨Z', m₈, h', inv_memb, inv_ana, inv_ne, inv_eqon, inv_ident, ?_⟩
  intro s hs hLs
  exact norm_logDeriv_sub_sum_of_blaschke hM₀ hFc (fun ρ hρ => (inv_memb ρ hρ).1) hcount
    inv_ana inv_ne inv_eqon inv_ident hsup hs hLs

/-! ## 5. The Abel growth bound `‖Zc s‖ ≤ 1 + ‖s−1‖·‖s‖·(1 + 1/Re s)` on `Re s > 0`

Mathlib has no complex-`s` growth bound for `ζ` on vertical strips; we build it via Abel summation
with the pole subtracted. The Abel term `dTerm s m = ∫_m^{m+1} (m^{−s} − u^{−s}) du` is kept as an
integral (entire in `s`; its closed form has a spurious `1/(1−s)` pole). On `Re s > 1` telescoping
gives `Zc s = 1 + (s−1)·∑'_{n} dTerm s (n+1)`; the sum is analytic on `Re s > 0` (differentiation
under the integral + locally uniform convergence), so the identity extends by the identity theorem,
and the termwise mean-value bound `‖dTerm s m‖ ≤ ‖s‖ m^{−(Re s+1)}` sums to the stated growth. -/

section ZcGrowth

open MeasureTheory intervalIntegral

/-- The Abel term: `∫_m^{m+1} (m^{-s} - u^{-s}) du`. -/
noncomputable def dTerm (s : ℂ) (m : ℕ) : ℂ :=
  ∫ u in (m : ℝ)..((m : ℝ) + 1), ((m : ℂ) ^ (-s) - (u : ℂ) ^ (-s))

/-- Pointwise mean-value bound: `‖m^{-s} - u^{-s}‖ ≤ ‖s‖·m^{-(Re s+1)}` for `m ≤ u ≤ m+1`. -/
lemma cpow_diff_pt (s : ℂ) (hσ : 0 < s.re) {m : ℕ} (hm : 1 ≤ m) {u : ℝ}
    (hu1 : (m : ℝ) ≤ u) (hu2 : u ≤ (m : ℝ) + 1) :
    ‖(m : ℂ) ^ (-s) - (u : ℂ) ^ (-s)‖ ≤ ‖s‖ * (m : ℝ) ^ (-(s.re + 1)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs0 : s ≠ 0 := fun h => by rw [h] at hσ; simp at hσ
  have hsne : (-s) ≠ 0 := neg_ne_zero.mpr hs0
  set φ : ℝ → ℂ := fun t => (t : ℂ) ^ (-s) with hφ
  have hderiv : ∀ t ∈ Set.Icc (m : ℝ) u,
      HasDerivWithinAt φ ((-s) * (t : ℂ) ^ (-s - 1)) (Set.Icc (m : ℝ) u) t := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hm0 (Set.mem_Icc.mp ht).1
    exact (hasDerivAt_ofReal_cpow_const htpos.ne' hsne).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc (m : ℝ) u,
      ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * (m : ℝ) ^ (-(s.re + 1)) := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hm0 (Set.mem_Icc.mp ht).1
    have hmt : (m : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    have hre : (-s - 1).re = -(s.re + 1) := by
      rw [Complex.sub_re, Complex.neg_re, Complex.one_re]; ring
    rw [hre]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
    exact Real.rpow_le_rpow_of_nonpos hm0 hmt (by linarith)
  have hmvt := (convex_Icc (m : ℝ) u).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.left_mem_Icc.mpr hu1) (Set.right_mem_Icc.mpr hu1)
  have e2 : φ (m : ℝ) = (m : ℂ) ^ (-s) := by
    change (((m : ℝ) : ℝ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s); rw [Complex.ofReal_natCast]
  have e1 : φ u = (u : ℂ) ^ (-s) := rfl
  rw [e1, e2] at hmvt
  rw [norm_sub_rev]
  have hum : ‖u - (m : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
  calc ‖(u : ℂ) ^ (-s) - (m : ℂ) ^ (-s)‖
      ≤ ‖s‖ * (m : ℝ) ^ (-(s.re + 1)) * ‖u - (m : ℝ)‖ := hmvt
    _ ≤ ‖s‖ * (m : ℝ) ^ (-(s.re + 1)) * 1 := by
        apply mul_le_mul_of_nonneg_left hum; positivity
    _ = ‖s‖ * (m : ℝ) ^ (-(s.re + 1)) := by ring

/-- Termwise bound on the Abel term. -/
lemma dTerm_norm_le (s : ℂ) (hσ : 0 < s.re) {m : ℕ} (hm : 1 ≤ m) :
    ‖dTerm s m‖ ≤ ‖s‖ * (m : ℝ) ^ (-(s.re + 1)) := by
  rw [dTerm]
  have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hC : ∀ u ∈ Set.uIoc (m : ℝ) ((m : ℝ) + 1),
      ‖(m : ℂ) ^ (-s) - (u : ℂ) ^ (-s)‖ ≤ ‖s‖ * (m : ℝ) ^ (-(s.re + 1)) := by
    intro u hu
    rw [Set.uIoc_of_le hle, Set.mem_Ioc] at hu
    exact cpow_diff_pt s hσ hm hu.1.le hu.2
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hC
  rw [show (m : ℝ) + 1 - (m : ℝ) = 1 by ring, abs_one, mul_one] at hb
  exact hb

/-- Reindexed tail: `∑'_n (n+1)^{-(σ+1)} = ∑'_i i^{-(σ+1)} ≤ 1+1/Re s`
(via the landed `Salt.SW.dser_tsum_le`). -/
lemma dser_shift_le (s : ℂ) (hσ : 0 < s.re) :
    ∑' (n : ℕ), ((n : ℝ) + 1) ^ (-(s.re + 1)) ≤ 1 + 1 / s.re := by
  have hexp : -(s.re + 1) < -1 := by linarith
  have hsummable : Summable (fun i : ℕ => (i : ℝ) ^ (-(s.re + 1))) :=
    Real.summable_nat_rpow.mpr hexp
  have hshift := hsummable.sum_add_tsum_nat_add 1
  have hr1 : (∑ i ∈ Finset.range 1, (i : ℝ) ^ (-(s.re + 1))) = 0 := by
    rw [Finset.sum_range_one, Nat.cast_zero, Real.zero_rpow (by linarith)]
  rw [hr1, zero_add] at hshift
  have hcong : (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(s.re + 1)))
      = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-(s.re + 1)) := by
    apply tsum_congr; intro n; congr 1; push_cast; ring
  rw [hcong, hshift]
  exact dser_tsum_le s hσ

/-- The dominating series `∑ ‖s‖ (n+1)^{-(σ+1)}` is summable. -/
lemma dom_summable (s : ℂ) (hσ : 0 < s.re) :
    Summable (fun n : ℕ => ‖s‖ * ((n : ℝ) + 1) ^ (-(s.re + 1))) := by
  have h1 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(s.re + 1))) := by
    have hbase : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(s.re + 1))) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -(s.re + 1) < -1))
    refine hbase.congr (fun n => ?_); push_cast; ring
  exact h1.mul_left _

lemma dTerm_norm_le' (s : ℂ) (hσ : 0 < s.re) (n : ℕ) :
    ‖dTerm s (n + 1)‖ ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-(s.re + 1)) := by
  have := dTerm_norm_le s hσ (m := n + 1) (by omega)
  rwa [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring] at this

lemma dTerm_norm_summable (s : ℂ) (hσ : 0 < s.re) :
    Summable (fun n : ℕ => ‖dTerm s (n + 1)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => dTerm_norm_le' s hσ n)
    (dom_summable s hσ)

lemma dTerm_summable_shift (s : ℂ) (hσ : 0 < s.re) : Summable (fun n : ℕ => dTerm s (n + 1)) :=
  (dTerm_norm_summable s hσ).of_norm

/-- `‖∑' n, dTerm s (n+1)‖ ≤ ‖s‖·(1 + 1/Re s)`. -/
lemma norm_R_le (s : ℂ) (hσ : 0 < s.re) :
    ‖∑' n : ℕ, dTerm s (n + 1)‖ ≤ ‖s‖ * (1 + 1 / s.re) := by
  calc ‖∑' n : ℕ, dTerm s (n + 1)‖
      ≤ ∑' n : ℕ, ‖dTerm s (n + 1)‖ := norm_tsum_le_tsum_norm (dTerm_norm_summable s hσ)
    _ ≤ ∑' n : ℕ, ‖s‖ * ((n : ℝ) + 1) ^ (-(s.re + 1)) :=
        (dTerm_norm_summable s hσ).tsum_le_tsum (fun n => dTerm_norm_le' s hσ n)
          (dom_summable s hσ)
    _ = ‖s‖ * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(s.re + 1)) := tsum_mul_left
    _ ≤ ‖s‖ * (1 + 1 / s.re) := mul_le_mul_of_nonneg_left (dser_shift_le s hσ) (norm_nonneg s)

/-- `u ↦ (u:ℂ)^(-y)` is continuous on `[m, m+1]` (`m ≥ 1`). -/
lemma cont_ucpow (y : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-y)) (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Set.uIcc_of_le (by linarith)]
  intro u hu
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le (by linarith) (Set.mem_Icc.mp hu).1
  exact (continuousAt_ofReal_cpow_const u (-y) (Or.inr hu0.ne')).continuousWithinAt

/-- `u ↦ Complex.log (u:ℂ)` is continuous on `[m, m+1]` (`m ≥ 1`). -/
lemma cont_ulog {m : ℕ} (hm : 1 ≤ m) :
    ContinuousOn (fun u : ℝ => Complex.log (u : ℂ)) (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Set.uIcc_of_le (by linarith)]
  intro u hu
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le (by linarith) (Set.mem_Icc.mp hu).1
  have hslit : (u : ℂ) ∈ Complex.slitPlane := Or.inl (by rw [Complex.ofReal_re]; exact hu0)
  exact ((continuousAt_clog hslit).comp Complex.continuous_ofReal.continuousAt).continuousWithinAt

/-- Per-term differentiability of the Abel term in `s` (differentiation under the integral). -/
lemma dTerm_differentiableAt {m : ℕ} (hm : 1 ≤ m) {x : ℂ} (hx : 0 < x.re) :
    DifferentiableAt ℂ (fun s => dTerm s m) x := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmc0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  set δ : ℝ := x.re / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set S : Set ℂ := Metric.ball x δ with hS
  have hSnhds : S ∈ 𝓝 x := Metric.ball_mem_nhds x hδpos
  have hReS : ∀ y ∈ S, 0 < y.re := by
    intro y hy
    rw [hS, Metric.mem_ball, Complex.dist_eq] at hy
    have h1 : |y.re - x.re| ≤ ‖y - x‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (y - x)
    have h2 : -‖y - x‖ ≤ y.re - x.re := neg_le_of_abs_le h1
    rw [hδ] at hy; linarith
  set F : ℂ → ℝ → ℂ := fun y u => (m : ℂ) ^ (-y) - (u : ℂ) ^ (-y) with hF
  set F' : ℂ → ℝ → ℂ := fun y u =>
    (m : ℂ) ^ (-y) * Complex.log (m : ℂ) * (-1) - (u : ℂ) ^ (-y) * Complex.log (u : ℂ) * (-1)
    with hF'
  -- continuity pieces
  have hcontF : ∀ y : ℂ, ContinuousOn (F y) (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := fun y =>
    continuousOn_const.sub (cont_ucpow y hm)
  have hcontF' : ContinuousOn (F' x) (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
    refine continuousOn_const.sub (ContinuousOn.mul (ContinuousOn.mul (cont_ucpow x hm) ?_) ?_)
    · exact cont_ulog hm
    · exact continuousOn_const
  -- the derivative bound `2 log(m+1)`
  have hbound : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.uIoc (m : ℝ) ((m : ℝ) + 1) →
      ∀ y ∈ S, ‖F' y u‖ ≤ 2 * Real.log ((m : ℝ) + 1) := by
    refine ae_of_all _ (fun u hu y hy => ?_)
    rw [Set.uIoc_of_le hle, Set.mem_Ioc] at hu
    have hu0 : (0 : ℝ) < u := by linarith
    have hyre : 0 < y.re := hReS y hy
    have hmn : ‖(m : ℂ) ^ (-y)‖ ≤ 1 := by
      rw [norm_natCast_cpow_of_pos (by omega : 0 < m)]
      rw [Complex.neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)
    have hun : ‖(u : ℂ) ^ (-y)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hlogm : ‖Complex.log (m : ℂ)‖ ≤ Real.log ((m : ℝ) + 1) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity), Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hm1)]
      exact Real.log_le_log (by linarith) (by linarith)
    have hlogu : ‖Complex.log (u : ℂ)‖ ≤ Real.log ((m : ℝ) + 1) := by
      rw [← Complex.ofReal_log hu0.le, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by linarith))]
      exact Real.log_le_log hu0 (by linarith)
    have ht1 : ‖(m : ℂ) ^ (-y) * Complex.log (m : ℂ) * (-1)‖ ≤ Real.log ((m : ℝ) + 1) := by
      rw [norm_mul, norm_mul, norm_neg, norm_one, mul_one]
      calc ‖(m : ℂ) ^ (-y)‖ * ‖Complex.log (m : ℂ)‖
          ≤ 1 * Real.log ((m : ℝ) + 1) :=
            mul_le_mul hmn hlogm (norm_nonneg _) (by norm_num)
        _ = Real.log ((m : ℝ) + 1) := by ring
    have ht2 : ‖(u : ℂ) ^ (-y) * Complex.log (u : ℂ) * (-1)‖ ≤ Real.log ((m : ℝ) + 1) := by
      rw [norm_mul, norm_mul, norm_neg, norm_one, mul_one]
      calc ‖(u : ℂ) ^ (-y)‖ * ‖Complex.log (u : ℂ)‖
          ≤ 1 * Real.log ((m : ℝ) + 1) :=
            mul_le_mul hun hlogu (norm_nonneg _) (by norm_num)
        _ = Real.log ((m : ℝ) + 1) := by ring
    calc ‖F' y u‖ ≤ ‖(m : ℂ) ^ (-y) * Complex.log (m : ℂ) * (-1)‖
          + ‖(u : ℂ) ^ (-y) * Complex.log (u : ℂ) * (-1)‖ := norm_sub_le _ _
      _ ≤ Real.log ((m : ℝ) + 1) + Real.log ((m : ℝ) + 1) := add_le_add ht1 ht2
      _ = 2 * Real.log ((m : ℝ) + 1) := by ring
  -- the pointwise derivative
  have hdiff : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.uIoc (m : ℝ) ((m : ℝ) + 1) →
      ∀ y ∈ S, HasDerivAt (fun y => F y u) (F' y u) y := by
    refine ae_of_all _ (fun u hu y hy => ?_)
    rw [Set.uIoc_of_le hle, Set.mem_Ioc] at hu
    have hu0 : (0 : ℝ) < u := by linarith
    have huc0 : (u : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_zero, Ne, Complex.ofReal_inj]; linarith
    have hd1 : HasDerivAt (fun y => (m : ℂ) ^ (-y))
        ((m : ℂ) ^ (-y) * Complex.log (m : ℂ) * (-1)) y :=
      ((hasDerivAt_id y).neg).const_cpow (Or.inl hmc0)
    have hd2 : HasDerivAt (fun y => (u : ℂ) ^ (-y))
        ((u : ℂ) ^ (-y) * Complex.log (u : ℂ) * (-1)) y :=
      ((hasDerivAt_id y).neg).const_cpow (Or.inl huc0)
    exact hd1.sub hd2
  have hHDA := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ => 2 * Real.log ((m : ℝ) + 1)) (F := F) (F' := F') hSnhds
    (Filter.Eventually.of_forall (fun y =>
      ((hcontF y).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc))
    ((hcontF x).intervalIntegrable)
    (((hcontF' ).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
    hbound (intervalIntegral.intervalIntegrable_const) hdiff).2
  exact hHDA.differentiableAt

/-- Analyticity of the Abel sum on the right half-plane. -/
lemma R_differentiableOn :
    DifferentiableOn ℂ (fun s => ∑' n : ℕ, dTerm s (n + 1)) {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hσ0 : 0 < s₀.re := hs₀
  set d := s₀.re / 2 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have hballsub : ∀ w ∈ Metric.ball s₀ d, d < w.re := by
    intro w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    have h1 : |w.re - s₀.re| ≤ ‖w - s₀‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - s₀)
    have h2 : -‖w - s₀‖ ≤ w.re - s₀.re := neg_le_of_abs_le h1
    rw [hd]; linarith
  have huniform : DifferentiableOn ℂ (fun s => ∑' n : ℕ, dTerm s (n + 1)) (Metric.ball s₀ d) := by
    apply differentiableOn_tsum_of_summable_norm
      (F := fun n w => dTerm w (n + 1))
      (u := fun n => (‖s₀‖ + d) * ((n : ℝ) + 1) ^ (-(d + 1)))
    · have h1 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(d + 1))) := by
        have hbase : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(d + 1))) :=
          (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -(d + 1) < -1))
        refine hbase.congr (fun n => ?_); push_cast; ring
      exact h1.mul_left _
    · intro n w hw
      exact (dTerm_differentiableAt (by omega)
        (lt_trans hdpos (hballsub w hw))).differentiableWithinAt
    · exact Metric.isOpen_ball
    · intro n w hw
      have hwre : d < w.re := hballsub w hw
      have hσw : 0 < w.re := lt_trans hdpos hwre
      have hwnorm : ‖w‖ ≤ ‖s₀‖ + d := by
        rw [Metric.mem_ball, Complex.dist_eq] at hw
        calc ‖w‖ = ‖s₀ + (w - s₀)‖ := by ring_nf
          _ ≤ ‖s₀‖ + ‖w - s₀‖ := norm_add_le _ _
          _ ≤ ‖s₀‖ + d := by linarith [hw.le]
      have hpow : ((n : ℝ) + 1) ^ (-(w.re + 1)) ≤ ((n : ℝ) + 1) ^ (-(d + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
      calc ‖dTerm w (n + 1)‖
          ≤ ‖w‖ * ((n : ℝ) + 1) ^ (-(w.re + 1)) := dTerm_norm_le' w hσw n
        _ ≤ (‖s₀‖ + d) * ((n : ℝ) + 1) ^ (-(d + 1)) := by
            apply mul_le_mul hwnorm hpow (Real.rpow_nonneg (by positivity) _)
            have : (0 : ℝ) ≤ ‖s₀‖ := norm_nonneg _; linarith
  exact (huniform.differentiableAt (Metric.ball_mem_nhds s₀ hdpos)).differentiableWithinAt

/-- `u ↦ (u:ℂ)^(-s)` is interval-integrable on any `[a,b]` with `a,b > 0`. -/
lemma intPow_ii (s : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (-s)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  have hu0 : 0 < u := by
    rcases le_total a b with hab | hab
    · rw [Set.uIcc_of_le hab] at hu; exact lt_of_lt_of_le ha (Set.mem_Icc.mp hu).1
    · rw [Set.uIcc_of_ge hab] at hu; exact lt_of_lt_of_le hb (Set.mem_Icc.mp hu).1
  exact (continuousAt_ofReal_cpow_const u (-s) (Or.inr hu0.ne')).continuousWithinAt

/-- Per-term split: `dTerm s m = m^{-s} - ∫_m^{m+1} u^{-s} du`. -/
lemma dTerm_split (s : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    dTerm s m = (m : ℂ) ^ (-s) - ∫ u in (m : ℝ)..((m : ℝ) + 1), (u : ℂ) ^ (-s) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hIc : IntervalIntegrable (fun _ : ℝ => (m : ℂ) ^ (-s)) volume (m : ℝ) ((m : ℝ) + 1) :=
    _root_.intervalIntegrable_const
  have hsub := intervalIntegral.integral_sub (μ := volume) (a := (m : ℝ)) (b := (m : ℝ) + 1)
    (f := fun _ : ℝ => (m : ℂ) ^ (-s)) (g := fun u : ℝ => (u : ℂ) ^ (-s))
    hIc (intPow_ii s hm0 (by positivity))
  rw [dTerm, hsub, intervalIntegral.integral_const,
    show (m : ℝ) + 1 - (m : ℝ) = 1 by ring, one_smul]

/-- FTC: `∫_1^X u^{-s} du = (X^{1-s} - 1)/(1-s)` for `s ≠ 1`, `1 ≤ X`. -/
lemma intPow_ftc (s : ℂ) (hs1 : s ≠ 1) {X : ℝ} (hX : 1 ≤ X) :
    ∫ u in (1 : ℝ)..X, (u : ℂ) ^ (-s) = ((X : ℂ) ^ (1 - s) - 1) / (1 - s) := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (fun h => hs1 h.symm)
  have hderiv : ∀ u ∈ Set.uIcc (1 : ℝ) X,
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ (1 - s) / (1 - s)) ((u : ℂ) ^ (-s)) u := by
    intro u hu
    rw [Set.uIcc_of_le hX] at hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos (Set.mem_Icc.mp hu).1
    have h := (hasDerivAt_ofReal_cpow_const hu0.ne' h1s).div_const (1 - s)
    have heq : (1 - s) * (u : ℂ) ^ (1 - s - 1) / (1 - s) = (u : ℂ) ^ (-s) := by
      rw [show (1 : ℂ) - s - 1 = -s by ring, mul_div_cancel_left₀ _ h1s]
    rw [heq] at h
    exact h
  have hint : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (-s)) volume 1 X :=
    intPow_ii s one_pos (by linarith)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [Complex.ofReal_one, Complex.one_cpow]
  ring

/-- The shifted zeta series equals `ζ` on `Re s > 1`. -/
lemma zeta_shift (s : ℂ) (hs1 : 1 < s.re) :
    ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) ^ (-s) = riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs1; linarith
  have hsummable : Summable (fun k : ℕ => (k : ℂ) ^ (-s)) := by
    have h : Summable (fun k : ℕ => 1 / (k : ℂ) ^ s) := Complex.summable_one_div_nat_cpow.mpr hs1
    refine h.congr (fun k => ?_); rw [Complex.cpow_neg, one_div]
  have hshift := hsummable.sum_add_tsum_nat_add 1
  have hr1 : (∑ k ∈ Finset.range 1, (k : ℂ) ^ (-s)) = 0 := by
    rw [Finset.sum_range_one, Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  rw [hr1, zero_add] at hshift
  rw [zeta_eq_tsum_one_div_nat_cpow hs1, hshift]
  exact tsum_congr (fun k => by rw [Complex.cpow_neg, one_div])

/-- The Abel identity `Zc s = 1 + (s-1)·∑' dTerm` on `Re s > 1`. -/
lemma Zc_eq_series_gt (s : ℂ) (hs1 : 1 < s.re) :
    Zc s = 1 + (s - 1) * ∑' n : ℕ, dTerm s (n + 1) := by
  have hs0 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs1; linarith
  have hs1ne : (s : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hs0
  have hσ0 : 0 < s.re := by linarith
  have hsummable : Summable (fun k : ℕ => (k : ℂ) ^ (-s)) := by
    have h : Summable (fun k : ℕ => 1 / (k : ℂ) ^ s) := Complex.summable_one_div_nat_cpow.mpr hs1
    refine h.congr (fun k => ?_); rw [Complex.cpow_neg, one_div]
  have hsum_shift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) :=
    (summable_nat_add_iff 1).mpr hsummable
  -- partial-sum identity
  have hPeq : ∀ N : ℕ, (∑ n ∈ Finset.range N, dTerm s (n + 1))
      = (∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-s))
        - ∫ u in (1 : ℝ)..((N : ℝ) + 1), (u : ℂ) ^ (-s) := by
    intro N
    rw [Finset.sum_congr rfl (fun n _ => dTerm_split s (Nat.le_add_left 1 n)),
      Finset.sum_sub_distrib]
    congr 1
    have hadj := intervalIntegral.sum_integral_adjacent_intervals (a := fun k => (k : ℝ) + 1)
      (f := fun u : ℝ => (u : ℂ) ^ (-s)) (n := N)
      (fun k _ => by exact intPow_ii s (by positivity) (by positivity))
    simp only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one] at hadj
    rw [← hadj]
    apply Finset.sum_congr rfl
    intro k _
    congr 1 <;> push_cast <;> ring
  -- the two limits of the partial sums
  have hzeta_partial : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-s))
      atTop (𝓝 (riemannZeta s)) := by
    have h := hsum_shift.hasSum.tendsto_sum_nat
    rw [zeta_shift s hs1] at h
    exact h
  have hint_lim : Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..((N : ℝ) + 1), (u : ℂ) ^ (-s))
      atTop (𝓝 (1 / (s - 1))) := by
    have hval : ∀ N : ℕ, (∫ u in (1 : ℝ)..((N : ℝ) + 1), (u : ℂ) ^ (-s))
        = (((N : ℝ) + 1 : ℂ) ^ (1 - s) - 1) / (1 - s) := by
      intro N
      rw [intPow_ftc s hs0 (by linarith [Nat.cast_nonneg (α := ℝ) N] : (1 : ℝ) ≤ (N : ℝ) + 1)]
      push_cast; ring
    have hpow0 : Tendsto (fun N : ℕ => (((N : ℝ) + 1 : ℂ) ^ (1 - s))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hnormeq : ∀ N : ℕ, ‖(((N : ℝ) + 1 : ℂ) ^ (1 - s))‖ = ((N : ℝ) + 1) ^ (-(s.re - 1)) := by
        intro N
        rw [show ((N : ℝ) + 1 : ℂ) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.sub_re, Complex.one_re,
          show (1 : ℝ) - s.re = -(s.re - 1) by ring]
      simp_rw [hnormeq]
      exact (tendsto_rpow_neg_atTop (show 0 < s.re - 1 by linarith)).comp
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    have hlim : Tendsto (fun N : ℕ => (((N : ℝ) + 1 : ℂ) ^ (1 - s) - 1) / (1 - s))
        atTop (𝓝 ((0 - 1) / (1 - s))) :=
      ((hpow0.sub_const 1).div_const (1 - s))
    have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs0)
    have heq : ((0 : ℂ) - 1) / (1 - s) = 1 / (s - 1) := by
      rw [zero_sub, div_eq_div_iff h1s hs1ne]; ring
    rw [heq] at hlim
    exact hlim.congr (fun N => (hval N).symm)
  have hPtends1 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, dTerm s (n + 1)) atTop
      (𝓝 (∑' n : ℕ, dTerm s (n + 1))) := (dTerm_summable_shift s hσ0).hasSum.tendsto_sum_nat
  have hPtends2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, dTerm s (n + 1)) atTop
      (𝓝 (riemannZeta s - 1 / (s - 1))) := by
    refine (hzeta_partial.sub hint_lim).congr (fun N => (hPeq N).symm)
  have hReq : ∑' n : ℕ, dTerm s (n + 1) = riemannZeta s - 1 / (s - 1) :=
    tendsto_nhds_unique hPtends1 hPtends2
  rw [hReq, Zc_eq_of_ne hs0]
  field_simp
  ring

/-- The Abel identity extended to the whole right half-plane by the identity theorem. -/
lemma Zc_eq_series (s : ℂ) (hσ : 0 < s.re) :
    Zc s = 1 + (s - 1) * ∑' n : ℕ, dTerm s (n + 1) := by
  set G : ℂ → ℂ := fun z => 1 + (z - 1) * ∑' n : ℕ, dTerm z (n + 1) with hG
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconv : Convex ℝ {z : ℂ | 0 < z.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.smul_re, smul_eq_mul] at hx hy ⊢
    have hm : (0 : ℝ) < min x.re y.re := lt_min hx hy
    calc (0 : ℝ) < min x.re y.re := hm
      _ = (a + b) * min x.re y.re := by rw [hab, one_mul]
      _ = a * min x.re y.re + b * min x.re y.re := by ring
      _ ≤ a * x.re + b * y.re := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (min_le_left _ _) ha
          · exact mul_le_mul_of_nonneg_left (min_le_right _ _) hb
  have hana_Z : AnalyticOnNhd ℂ Zc {z : ℂ | 0 < z.re} :=
    Zc_differentiable.differentiableOn.analyticOnNhd hopen
  have hana_G : AnalyticOnNhd ℂ G {z : ℂ | 0 < z.re} := by
    have hdiff : DifferentiableOn ℂ G {z : ℂ | 0 < z.re} := by
      apply DifferentiableOn.add (differentiableOn_const 1)
      exact (differentiableOn_id.sub (differentiableOn_const 1)).mul R_differentiableOn
    exact hdiff.analyticOnNhd hopen
  have h2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.re_ofNat]; norm_num
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), Zc z = G z := by
    have hgt : ∀ᶠ z in 𝓝 (2 : ℂ), Zc z = G z := by
      have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have h2' : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
        simp only [Set.mem_setOf_eq, Complex.re_ofNat]; norm_num
      filter_upwards [hopen1.mem_nhds h2'] with z hz
      exact Zc_eq_series_gt z hz
    exact (hgt.filter_mono nhdsWithin_le_nhds).frequently
  have heqOn := hana_Z.eqOn_of_preconnected_of_frequently_eq hana_G hconv.isPreconnected h2 hfreq
  exact heqOn hσ

/-- **The ζ growth bound.** For `Re s > 0`,
`‖Zc s‖ ≤ 1 + ‖s-1‖·(‖s‖·(1 + 1/Re s))`. -/
theorem Zc_growth {s : ℂ} (hs : 0 < s.re) :
    ‖Zc s‖ ≤ 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := by
  rw [Zc_eq_series s hs]
  calc ‖1 + (s - 1) * ∑' n : ℕ, dTerm s (n + 1)‖
      ≤ ‖(1 : ℂ)‖ + ‖(s - 1) * ∑' n : ℕ, dTerm s (n + 1)‖ := norm_add_le _ _
    _ = 1 + ‖s - 1‖ * ‖∑' n : ℕ, dTerm s (n + 1)‖ := by rw [norm_one, norm_mul]
    _ ≤ 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := by
        gcongr
        exact norm_R_le s hs

end ZcGrowth

/-! ## 6. The growth-sphere quantity `M₀ζ` and the S3d-b deliverable -/

/-- The ζ growth-sphere quantity at height `t₀`: `M₀ζ(t₀) = 1 + 5(19/4+|t₀|)(15/4+|t₀|)`, an
`O((|t₀|+2)²)` bound valid on both spheres `|z−c| ∈ {3/2, 7/4}` about `c = 2 + t₀i`. -/
noncomputable def M0zeta (t₀ : ℝ) : ℝ := 1 + 5 * (19 / 4 + |t₀|) * (15 / 4 + |t₀|)

lemma one_le_M0zeta (t₀ : ℝ) : 1 ≤ M0zeta t₀ := by
  have := abs_nonneg t₀; rw [M0zeta]; nlinarith [this]

/-- `log(4·M₀ζ(2γ)) ≤ 9·log(|γ|+2)` — the `O(log(|γ|+2))` collapse of the growth quantity
(`4 M₀ζ(2γ) ≤ 100(|γ|+2)²`, `log 100 ≤ 7 log 2 ≤ 7 log(|γ|+2)`). -/
lemma log_4M0zeta_le (γ : ℝ) :
    Real.log (4 * M0zeta (2 * γ)) ≤ 9 * Real.log (|γ| + 2) := by
  have hx : (0 : ℝ) ≤ |γ| := abs_nonneg γ
  have h2γ : |2 * γ| = 2 * |γ| := by rw [abs_mul]; norm_num
  have hbound4 : 4 * M0zeta (2 * γ) ≤ 100 * (|γ| + 2) ^ 2 := by
    rw [M0zeta, h2γ]; nlinarith [hx]
  have hM0pos : (0 : ℝ) < 4 * M0zeta (2 * γ) := by have := one_le_M0zeta (2 * γ); linarith
  have hlog2le : Real.log 2 ≤ Real.log (|γ| + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hlog100 : Real.log 100 ≤ 7 * Real.log (|γ| + 2) := by
    have h128 : Real.log 100 ≤ 7 * Real.log 2 := by
      rw [show (7 : ℝ) * Real.log 2 = Real.log (2 ^ (7 : ℕ)) by rw [Real.log_pow]; push_cast; ring]
      exact Real.log_le_log (by norm_num) (by norm_num)
    linarith
  calc Real.log (4 * M0zeta (2 * γ)) ≤ Real.log (100 * (|γ| + 2) ^ 2) :=
        Real.log_le_log hM0pos hbound4
    _ = Real.log 100 + 2 * Real.log (|γ| + 2) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    _ ≤ 9 * Real.log (|γ| + 2) := by linarith [hlog100]

/-- **The sphere growth bound for `Zc`.** On the sphere `|z − (2+t₀i)| = R` with `R ≤ 7/4`
(so `Re z ≥ 1/4`), `‖Zc z‖ ≤ M₀ζ(t₀)`; from `Zc_growth`. -/
lemma Zc_sphere_bound (t₀ : ℝ) {R : ℝ} (hR : R ≤ 7 / 4) {z : ℂ}
    (hz : ‖z - (2 + (t₀ : ℂ) * I)‖ = R) : ‖Zc z‖ ≤ M0zeta t₀ := by
  set c : ℂ := 2 + (t₀ : ℂ) * I with hc
  have hcre : c.re = 2 := by rw [hc]; simp
  have hzc_re : (2 : ℝ) - R ≤ z.re := by
    have h := Complex.abs_re_le_norm (z - c)
    rw [Complex.sub_re, hcre, hz] at h
    have := abs_le.mp h; linarith [this.1]
  have hre_pos : 0 < z.re := by linarith [hR]
  have hcnorm : ‖c‖ ≤ 2 + |t₀| := by
    rw [hc]
    calc ‖(2 : ℂ) + (t₀ : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(t₀ : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |t₀| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; norm_num
  have hznorm : ‖z‖ ≤ 15 / 4 + |t₀| := by
    calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
      _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ (2 + |t₀|) + R := by rw [hz]; linarith [hcnorm]
      _ ≤ 15 / 4 + |t₀| := by linarith [hR]
  have hz1norm : ‖z - 1‖ ≤ 19 / 4 + |t₀| := by
    calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖z‖ + 1 := by rw [norm_one]
      _ ≤ 19 / 4 + |t₀| := by linarith [hznorm]
  have h1re : (0 : ℝ) ≤ 1 / z.re := div_nonneg zero_le_one hre_pos.le
  have hinv : 1 + 1 / z.re ≤ 5 := by
    have h4 : 1 / z.re ≤ 4 := by rw [div_le_iff₀ hre_pos]; linarith [hzc_re, hR]
    linarith
  have habs : (0 : ℝ) ≤ |t₀| := abs_nonneg t₀
  have hA : ‖z‖ * (1 + 1 / z.re) ≤ (15 / 4 + |t₀|) * 5 :=
    mul_le_mul hznorm hinv (by linarith [h1re]) (by linarith [habs])
  have hAnn : (0 : ℝ) ≤ ‖z‖ * (1 + 1 / z.re) := mul_nonneg (norm_nonneg _) (by linarith [h1re])
  have hB : ‖z - 1‖ * (‖z‖ * (1 + 1 / z.re)) ≤ (19 / 4 + |t₀|) * ((15 / 4 + |t₀|) * 5) :=
    mul_le_mul hz1norm hA hAnn (by linarith [habs])
  rw [M0zeta]
  calc ‖Zc z‖ ≤ 1 + ‖z - 1‖ * (‖z‖ * (1 + 1 / z.re)) := Zc_growth hre_pos
    _ ≤ 1 + (19 / 4 + |t₀|) * ((15 / 4 + |t₀|) * 5) := by linarith [hB]
    _ = 1 + 5 * (19 / 4 + |t₀|) * (15 / 4 + |t₀|) := by ring

/-- **Z2ζ — the S3d-b deliverable.** The ζ log-derivative bound at `s = σ + 2iγ`, `σ ∈ (1,2]`:
`Re(−ζ'/ζ(s)) ≤ Re(1/(s−1)) + C₇·log(|γ|+2)` with **`C₇ = 1080`** — the honest complex pole term
`Re(1/(s−1)) = (σ−1)/((σ−1)²+4γ²)` plus an `O(log(|γ|+2))` zero-theory remainder, uniform in `γ`.

Route: the pole split `−ζ'/ζ = 1/(s−1) − Zc'/Zc` (`logDeriv_zeta_eq`); the entire-`Zc` numeric
`Re(−Zc'/Zc) ≤ 120·log(4M₀ζ)` from the generic S2 pipeline (`entire_norm_logDeriv_sub_sum'` at
`c = 2+2γi`, spheres bounded by `Zc_growth`), with all partial-fraction zero terms dropped — zeros
of `Zc` are zeros of `ζ` (`Zc(1) = 1 ≠ 0`), hence lie in `Re < 1 < σ` and contribute `≥ 0`; and
the collapse `120·log(4M₀ζ(2γ)) ≤ 1080·log(|γ|+2)` (`log_4M0zeta_le`). -/
theorem zeta_neg_re_logDeriv_le {σ γ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    (-logDeriv riemannZeta ((σ : ℂ) + 2 * (γ : ℂ) * I)).re
      ≤ (1 / (((σ : ℂ) + 2 * (γ : ℂ) * I) - 1)).re + 1080 * Real.log (|γ| + 2) := by
  set t₀ : ℝ := 2 * γ with ht₀
  set s : ℂ := (σ : ℂ) + 2 * (γ : ℂ) * I with hs
  set c : ℂ := 2 + (t₀ : ℂ) * I with hc
  have hsceq : s = (σ : ℂ) + (t₀ : ℂ) * I := by rw [hs, ht₀]; push_cast; ring
  have hsre : s.re = σ := by
    rw [hsceq]; simp [Complex.add_re, Complex.mul_re]
  have hσC : (1 : ℝ) < s.re := by rw [hsre]; exact h1
  have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hσC; norm_num at hσC
  have hζs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hσC)
  -- pole split
  have hsplit := neg_logDeriv_zeta_split hs_ne1 hζs
  -- the entire-`Zc` numeric via the generic pipeline
  have hsphere74 : ∀ z ∈ sphere c (7 / 4), ‖Zc z‖ ≤ M0zeta t₀ := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz
    exact Zc_sphere_bound t₀ (le_refl _) hz
  have hsphere32 : ∀ z ∈ sphere c (3 / 2), ‖Zc z‖ ≤ M0zeta t₀ := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz
    exact Zc_sphere_bound t₀ (by norm_num) hz
  obtain ⟨Z, m, h, hmemb, -, -, -, -, hnum⟩ :=
    entire_norm_logDeriv_sub_sum' Zc_differentiable (one_le_M0zeta t₀) (Zc_center_lower t₀)
      hsphere74 hsphere32
  -- evaluate the numeric bound at `s`
  have hscnorm : ‖s - c‖ ≤ 23 / 20 := by
    have hsub : s - c = ((σ - 2 : ℝ) : ℂ) := by rw [hsceq, hc]; push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    linarith
  have hZcs : Zc s ≠ 0 := by
    rw [Zc_eq_of_ne hs_ne1]
    exact mul_ne_zero (sub_ne_zero.mpr hs_ne1) hζs
  have hbound := hnum s hscnorm hZcs
  -- drop the (nonnegative) partial-fraction zero terms: zeros of `Zc` have `Re < 1 < σ`
  have hdrop : 0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (s - ρ)).re := by
    refine Finset.sum_nonneg (fun ρ hρ => ?_)
    have hρ0 : Zc ρ = 0 := (hmemb ρ hρ).2
    have hρ1 : ρ ≠ 1 := fun h => by rw [h, Zc_one] at hρ0; exact one_ne_zero hρ0
    have hζρ : riemannZeta ρ = 0 := by
      rw [Zc_eq_of_ne hρ1] at hρ0
      exact (mul_eq_zero.mp hρ0).resolve_left (sub_ne_zero.mpr hρ1)
    have hρre : ρ.re < 1 := by
      by_contra hcn; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcn) hζρ
    refine mul_nonneg (by positivity) ?_
    rw [one_div, Complex.inv_re]
    refine div_nonneg ?_ (Complex.normSq_nonneg _)
    rw [Complex.sub_re]; linarith [hσC, hρre]
  have hZcnum : (-logDeriv Zc s).re ≤ 120 * Real.log (4 * M0zeta t₀) := by
    have h := neg_re_logDeriv_le hbound
    linarith [h, hdrop]
  -- collapse `120·log(4M₀ζ(2γ)) ≤ 1080·log(|γ|+2)`
  have hlog : 120 * Real.log (4 * M0zeta t₀) ≤ 1080 * Real.log (|γ| + 2) := by
    have := log_4M0zeta_le γ; rw [ht₀]
    nlinarith [this]
  -- assemble
  rw [hsplit]
  linarith [hZcnum, hlog]

end Salt.SW
