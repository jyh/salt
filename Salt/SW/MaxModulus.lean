/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.BCBound

/-!
# The SW rung, node S2-Z3c — discharging `hsup`, the Blaschke maximum-modulus bound

Design: `docs/blueprints/sw.md`, wave S2. This module discharges the single analytic input
`hsup` that `Salt/SW/BCBound.lean` flagged (the hypothesis of
`norm_logDeriv_sub_sum_of_blaschke` / `LFunction_norm_logDeriv_sub_sum`), landing the **ungated**
endpoint `LFunction_norm_logDeriv_sub_sum'`.

## The obstruction and the route

`g := h · ∏_{ρ∈Z} reflectedFactor^{m_ρ}` is analytic on `ball c (3/2)`; `hsup` needs
`‖g‖ ≤ M₀` there. On the boundary sphere the Blaschke product has modulus one, so `‖g‖ = ‖L‖ ≤ M₀`,
and the maximum-modulus principle transfers the bound inside — *provided* `g` is continuous up to
the boundary. But `h` is only analytic on the **open** ball, so we re-factor `L` at the slightly
larger radius `R₈ = 8/5 > 3/2`: `LFunction_exists_factorization` (inlined here to expose the
divisor-based multiplicities) gives `L = (∏_{ρ∈Z₈}(·−ρ)^{m₈})·h₈` on `ball c (8/5)` with `h₈`
analytic non-vanishing there. Regrouping the zeros `Z₈ = Z' ⊔ Zout` (inside / annulus), we set
`h' := h₈·∏_{ρ∈Zout}(·−ρ)^{m₈}` (analytic on `ball c (8/5)`, non-vanishing on `ball c (3/2)`),
so `g' := h'·∏_{ρ∈Z'} reflectedFactor^{m₈}` is analytic on `ball c (8/5)`, hence continuous on
`closedBall c (3/2)`.

Two arithmetic facts make it work:

* **The sphere norm identity** (`norm_reflectedFactor_eq_on_sphere`): on `‖z−c‖ = 3/2`,
  `‖reflectedFactor c ρ z‖ = ‖z − ρ‖` for **any** `ρ` (the reflection factor `(9/4 −
  conj(ρ−c)(z−c))/(3/2)` equals `(z−c)·conj(z−ρ)/(3/2)` there). Hence `‖g'‖ = ‖L‖` on the sphere.
* **Divisor locality** (`meromorphicOrderAt` is a germ invariant, so `divisor L (ball c 8/5) ρ =
  divisor L (ball c 3/2) ρ` for `ρ ∈ ball c (3/2)`): the inside zero-count `∑_{Z'} m₈` equals the
  `ball c (3/2)` divisor mass, so the Jensen keystone (`LFunction_zero_count_le`, sphere `7/4`)
  bounds it by `log(4M₀)/log(7/6)` — the exact constant `norm_logDeriv_sub_sum_of_blaschke`
  consumes.

The growth-sphere bound `M₀ = 5(4+|t₀|)√f(1+log f)` is **not** enlarged: on `‖z−c‖ = 3/2` the real
parts lie in `[1/2, 7/2] ⊆ [1/2, 4]`, so `LFunction_growth` gives `‖L z‖ ≤ 3(1+‖z‖)√f(1+log f) ≤
M₀`.

## Main results

* `norm_reflectedFactor_eq_on_sphere` — the boundary modulus identity.
* `LFunction_norm_logDeriv_sub_sum'` — the ungated S2-Z3c endpoint: same `∃ Z m h` shape and
  invariants as the gated `LFunction_norm_logDeriv_sub_sum`, with the numeric bound
  `‖L'/L(s) − ∑_ρ m_ρ/(s−ρ)‖ ≤ 120·log(4 M₀)` now holding unconditionally for `‖s−c‖ ≤ 23/20`.
-/

namespace Salt.SW

open Complex Metric MeromorphicOn Function DirichletCharacter Set Filter
open scoped Topology

/-! ## 1. The boundary modulus identity for the reflected factor -/

/-- On the boundary sphere `‖z − c‖ = 3/2`, the reflected factor has modulus `‖z − ρ‖`, for **any**
`ρ`. This is the classical `|Blaschke| = 1` fact: `reflectedFactor c ρ z = (z−c)·conj(z−ρ)/(3/2)`
there, and `‖z − c‖ = 3/2`. -/
lemma norm_reflectedFactor_eq_on_sphere (c ρ : ℂ) {z : ℂ} (hz : ‖z - c‖ = 3 / 2) :
    ‖reflectedFactor c ρ z‖ = ‖z - ρ‖ := by
  have hns : (Complex.normSq (z - c) : ℂ) = 9 / 4 := by
    rw [Complex.normSq_eq_norm_sq, hz]; push_cast; norm_num
  have hmc : (z - c) * (starRingEnd ℂ) (z - c) = (9 : ℂ) / 4 := by
    rw [Complex.mul_conj]; exact hns
  have hkey : (9 : ℂ) / 4 - (starRingEnd ℂ) (ρ - c) * (z - c)
      = (z - c) * (starRingEnd ℂ) (z - ρ) := by
    have hconj : (starRingEnd ℂ) (z - ρ) = (starRingEnd ℂ) (z - c) - (starRingEnd ℂ) (ρ - c) := by
      rw [← map_sub]; congr 1; ring
    rw [hconj]
    conv_rhs => rw [mul_sub, hmc]
    ring
  rw [reflectedFactor, norm_div, hkey, norm_mul, Complex.norm_conj, hz]
  norm_num

/-! ## 2. The ungated endpoint -/

/-- **S2-Z3c — the ungated L'/L numeric near the 1-line.** For a primitive Dirichlet character `χ`
mod `f ≥ 2` and `t₀ ∈ ℝ`, on the disk `ball (2 + it₀) (3/2)` there is a finite set `Z` of zeros of
`L(·,χ)` (multiplicities `m`) and an analytic non-vanishing remainder `h` with the
`LFunction_partialFraction` invariants, and — **unconditionally** — the numeric bound
`‖L'/L(s) − ∑_ρ m_ρ/(s−ρ)‖ ≤ 120·log(4·M₀)` for `‖s − (2+it₀)‖ ≤ 23/20`, `L s ≠ 0`, with
`M₀ = 5(4+|t₀|)√f(1+log f)` the growth-sphere quantity. This discharges the `hsup` hypothesis of
`norm_logDeriv_sub_sum_of_blaschke` via the Blaschke maximum-modulus argument (re-factoring at
radius `8/5`; see the module docstring). -/
theorem LFunction_norm_logDeriv_sub_sum' {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (t₀ : ℝ) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ ρ ∈ Z, ρ ∈ ball (2 + (t₀ : ℂ) * I) (3 / 2) ∧ LFunction χ ρ = 0) ∧
      AnalyticOnNhd ℂ h (ball (2 + (t₀ : ℂ) * I) (3 / 2)) ∧
      (∀ z ∈ ball (2 + (t₀ : ℂ) * I) (3 / 2), h z ≠ 0) ∧
      Set.EqOn (LFunction χ) (fun z => (∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) * h z)
        (ball (2 + (t₀ : ℂ) * I) (3 / 2)) ∧
      (∀ s ∈ ball (2 + (t₀ : ℂ) * I) (3 / 2), LFunction χ s ≠ 0 →
        logDeriv (LFunction χ) s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) = logDeriv h s) ∧
      (∀ s, ‖s - (2 + (t₀ : ℂ) * I)‖ ≤ 23 / 20 → LFunction χ s ≠ 0 →
        ‖logDeriv (LFunction χ) s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖
          ≤ 120 * Real.log (4 * (5 * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f)))) := by
  classical
  set c : ℂ := 2 + (t₀ : ℂ) * I with hc
  set M₀ : ℝ := 5 * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f) with hM₀def
  have hne : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  have hcre : c.re = 2 := by rw [hc]; simp
  have hLc : (1 : ℝ) / 4 ≤ ‖LFunction χ c‖ := LFunction_center_lower χ (le_of_eq hcre.symm)
  have hc0 : LFunction χ c ≠ 0 := by intro h0; rw [h0, norm_zero] at hLc; linarith
  -- `1 ≤ M₀`
  have hlog2 : (0 : ℝ) ≤ Real.log f := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ f))
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt f := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt; exact_mod_cast (by omega : 1 ≤ f)
  have hM₀1 : 1 ≤ M₀ := by
    have ha : (4 : ℝ) ≤ 4 + |t₀| := by linarith [abs_nonneg t₀]
    have hp1nn : (0 : ℝ) ≤ 5 * (4 + |t₀|) := by linarith
    have p2 : (20 : ℝ) ≤ 5 * (4 + |t₀|) * Real.sqrt f := by
      nlinarith [mul_nonneg hp1nn (by linarith [hsqrt1] : (0 : ℝ) ≤ Real.sqrt f - 1)]
    have hp2nn : (0 : ℝ) ≤ 5 * (4 + |t₀|) * Real.sqrt f := by linarith
    have p3 : (20 : ℝ) ≤ 5 * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f) := by
      nlinarith [mul_nonneg hp2nn (by linarith [hlog2] : (0 : ℝ) ≤ (1 + Real.log f) - 1)]
    rw [hM₀def]; linarith [p3]
  -- ============================================================================
  -- Inlined `LFunction_exists_factorization` at radius `8/5` (exposing `m₈ = divisor.toNat`)
  -- ============================================================================
  set U : Set ℂ := ball c (8 / 5) with hU
  have hUo : IsOpen U := isOpen_ball
  have hpre : IsPreconnected U := (convex_ball c (8 / 5)).isPreconnected
  have hcU : c ∈ U := mem_ball_self (by norm_num)
  have hana_univ : AnalyticOnNhd ℂ (LFunction χ) univ :=
    (differentiable_LFunction hne).differentiableOn.analyticOnNhd isOpen_univ
  have hana : AnalyticOnNhd ℂ (LFunction χ) U := hana_univ.mono (subset_univ _)
  have h₂f : ∀ u : U, meromorphicOrderAt (LFunction χ) (u : ℂ) ≠ ⊤ := by
    intro u htop
    rw [meromorphicOrderAt_eq_top_iff] at htop
    have hfreq : ∃ᶠ z in 𝓝[≠] (u : ℂ), LFunction χ z = 0 := htop.frequently
    have hz : Set.EqOn (LFunction χ) 0 U :=
      hana.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre u.2 hfreq
    exact hc0 (hz hcU)
  have h₃f : (divisor (LFunction χ) U).support.Finite :=
    divisor_ball_support_finite (hana_univ.mono (subset_univ _)).meromorphicOn
  obtain ⟨g₈, hg₈_ana, hg₈_ne, hg₈_eq⟩ := hana.meromorphicOn.extract_zeros_poles h₂f h₃f
  set Z₈ : Finset ℂ := h₃f.toFinset with hZ₈
  set m₈ : ℂ → ℕ := fun ρ => ((divisor (LFunction χ) U) ρ).toNat with hm₈
  have hdivnn : ∀ u, 0 ≤ (divisor (LFunction χ) U) u := hana.divisor_nonneg
  set P₈ : ℂ → ℂ := fun z => ∏ ρ ∈ Z₈, (z - ρ) ^ (m₈ ρ) with hP₈
  have hsub : mulSupport (fun u : ℂ => ((· - u) ^ (divisor (LFunction χ) U u) : ℂ → ℂ)) ⊆ ↑Z₈ := by
    intro u hu
    simp only [hZ₈, Finite.coe_toFinset, Function.mem_support]
    intro hd0; apply hu; simp [hd0]
  have hfun : (∏ᶠ u, ((· - u) ^ (divisor (LFunction χ) U u) : ℂ → ℂ)) = P₈ := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    funext z; rw [hP₈]
    simp only [Finset.prod_apply, Pi.pow_apply]
    apply Finset.prod_congr rfl; intro u _
    rw [← Int.toNat_of_nonneg (hdivnn u), zpow_natCast]
  have hg_eq2 : LFunction χ =ᶠ[codiscreteWithin U] (fun z => P₈ z * g₈ z) := by
    filter_upwards [hg₈_eq] with z hz
    rw [hz, hfun]
    simp [Pi.smul_apply', smul_eq_mul]
  have hP₈_ana : AnalyticOnNhd ℂ P₈ U := by
    rw [hP₈]
    exact Finset.analyticOnNhd_fun_prod Z₈ (fun ρ _ => by
      apply AnalyticOnNhd.pow; exact (analyticOnNhd_id.sub analyticOnNhd_const))
  have hP₈g_ana : AnalyticOnNhd ℂ (fun z => P₈ z * g₈ z) U := hP₈_ana.mul hg₈_ana
  have hev : ∀ᶠ z in 𝓝[≠] c, LFunction χ z = P₈ z * g₈ z := by
    have h1 : ({z | LFunction χ z = P₈ z * g₈ z} ∪ Uᶜ) ∈ 𝓝[≠] c :=
      mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hg_eq2 c hcU
    have h2 : U ∈ 𝓝[≠] c := mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hcU)
    filter_upwards [h1, h2] with z hz hzU
    rcases hz with hz | hz
    · exact hz
    · exact absurd hzU hz
  have hEqOn₈ : Set.EqOn (LFunction χ) (fun z => P₈ z * g₈ z) U :=
    hana.eqOn_of_preconnected_of_frequently_eq hP₈g_ana hpre hcU hev.frequently
  have hg₈_ne' : ∀ z ∈ U, g₈ z ≠ 0 := fun z hz => hg₈_ne ⟨z, hz⟩
  have hmemZ₈ : ∀ ρ ∈ Z₈, ρ ∈ U ∧ LFunction χ ρ = 0 := by
    intro ρ hρ
    have hρsupp : (divisor (LFunction χ) U) ρ ≠ 0 := by
      rw [hZ₈, Finite.mem_toFinset, Function.mem_support] at hρ; exact hρ
    have hρU : ρ ∈ U := by
      by_contra hnU
      exact hρsupp (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hnU)
    refine ⟨hρU, ?_⟩
    by_contra hne0
    apply hρsupp
    rw [hana.divisor_apply hρU, (hana ρ hρU).analyticOrderAt_eq_zero.mpr hne0]; simp
  -- ============================================================================
  -- Regrouping the zeros `Z₈ = Z' ⊔ Zout` and the witness `h' = g₈·Pout`
  -- ============================================================================
  set Z' : Finset ℂ := Z₈.filter (fun ρ => ρ ∈ ball c (3 / 2)) with hZ'
  set Zout : Finset ℂ := Z₈.filter (fun ρ => ρ ∉ ball c (3 / 2)) with hZout
  set Pout : ℂ → ℂ := fun z => ∏ ρ ∈ Zout, (z - ρ) ^ (m₈ ρ) with hPout
  set h' : ℂ → ℂ := fun z => g₈ z * Pout z with hh'
  have hZ'mem : ∀ ρ ∈ Z', ρ ∈ ball c (3 / 2) := fun ρ hρ => (Finset.mem_filter.mp hρ).2
  have hZ'sub : ∀ ρ ∈ Z', ρ ∈ Z₈ := fun ρ hρ => (Finset.mem_filter.mp hρ).1
  have hZoutmem : ∀ ρ ∈ Zout, ρ ∉ ball c (3 / 2) := fun ρ hρ => (Finset.mem_filter.mp hρ).2
  have hball32_U : ball c (3 / 2) ⊆ U := by rw [hU]; exact ball_subset_ball (by norm_num)
  have hcb32_U : closedBall c (3 / 2) ⊆ U := by rw [hU]; exact closedBall_subset_ball (by norm_num)
  -- the invariants
  have inv_memb : ∀ ρ ∈ Z', ρ ∈ ball c (3 / 2) ∧ LFunction χ ρ = 0 :=
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
  have inv_eqon : Set.EqOn (LFunction χ) (fun z => (∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) * h' z)
      (ball c (3 / 2)) := by
    intro z hz
    have hEz : LFunction χ z = P₈ z * g₈ z := hEqOn₈ (hball32_U hz)
    rw [hEz, hsplit_prod z]
    change (∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) * Pout z * g₈ z
      = (∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) * (g₈ z * Pout z)
    ring
  -- the logarithmic-derivative identity
  have inv_ident : ∀ s ∈ ball c (3 / 2), LFunction χ s ≠ 0 →
      logDeriv (LFunction χ) s - ∑ ρ ∈ Z', (m₈ ρ : ℂ) / (s - ρ) = logDeriv h' s := by
    intro s hsU hsne
    have hsρ : ∀ ρ ∈ Z', s ≠ ρ := by
      intro ρ hρ hsρ; exact hsne (hsρ ▸ (hmemZ₈ ρ (hZ'sub ρ hρ)).2)
    have hP's : (∏ ρ ∈ Z', (s - ρ) ^ (m₈ ρ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hsρ ρ hρ))
    have hh's : h' s ≠ 0 := inv_ne s hsU
    have hlocal : LFunction χ =ᶠ[𝓝 s]
        (fun z => (∏ ρ ∈ Z', (z - ρ) ^ (m₈ ρ)) * h' z) := by
      filter_upwards [(isOpen_ball (x := c) (ε := 3 / 2)).mem_nhds hsU] with z hz
      exact inv_eqon hz
    have hlogL : logDeriv (LFunction χ) s
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
  have hana32 : AnalyticOnNhd ℂ (LFunction χ) (ball c (3 / 2)) := hana_univ.mono (subset_univ _)
  have hana_cb : AnalyticOnNhd ℂ (LFunction χ) (closedBall c (3 / 2)) :=
    hana_univ.mono (subset_univ _)
  have hloc : ∀ ρ ∈ Z',
      (divisor (LFunction χ) U) ρ = (divisor (LFunction χ) (ball c (3 / 2))) ρ := by
    intro ρ hρ
    rw [hana.meromorphicOn.divisor_apply (hball32_U (hZ'mem ρ hρ)),
        hana32.meromorphicOn.divisor_apply (hZ'mem ρ hρ)]
  have hsupp32 : (Function.support (fun u => divisor (LFunction χ) (ball c (3 / 2)) u)) ⊆ ↑Z' := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    have hρ32 : ρ ∈ ball c (3 / 2) := by
      by_contra hn
      exact hρ (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hn)
    have hloc' : (divisor (LFunction χ) U) ρ = (divisor (LFunction χ) (ball c (3 / 2))) ρ := by
      rw [hana.meromorphicOn.divisor_apply (hball32_U hρ32),
          hana32.meromorphicOn.divisor_apply hρ32]
    have hUne : (divisor (LFunction χ) U) ρ ≠ 0 := by rw [hloc']; exact hρ
    have hρZ₈ : ρ ∈ Z₈ := by rw [hZ₈, Finite.mem_toFinset, Function.mem_support]; exact hUne
    rw [hZ', Finset.coe_filter]; exact ⟨hρZ₈, hρ32⟩
  have hcount : (∑ ρ ∈ Z', (m₈ ρ : ℝ)) ≤ Real.log (4 * M₀) / Real.log (7 / 6) := by
    have e1 : (∑ ρ ∈ Z', (m₈ ρ : ℤ)) = ∑ ρ ∈ Z', divisor (LFunction χ) (ball c (3 / 2)) ρ := by
      apply Finset.sum_congr rfl; intro ρ hρ
      have hcast : ((m₈ ρ : ℤ)) = divisor (LFunction χ) U ρ := Int.toNat_of_nonneg (hdivnn ρ)
      rw [hcast, hloc ρ hρ]
    have e2 : (∑ ρ ∈ Z', divisor (LFunction χ) (ball c (3 / 2)) ρ)
        = ∑ᶠ u, divisor (LFunction χ) (ball c (3 / 2)) u :=
      (finsum_eq_finsetSum_of_support_subset _ hsupp32).symm
    have hdle : ∀ u : ℂ, divisor (LFunction χ) (ball c (3 / 2)) u
        ≤ divisor (LFunction χ) (closedBall c (3 / 2)) u := by
      intro u
      by_cases hu : u ∈ ball c (3 / 2)
      · exact le_of_eq (by rw [hana32.divisor_apply hu,
          hana_cb.divisor_apply (ball_subset_closedBall hu)])
      · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
        exact hana_cb.divisor_nonneg u
    have hfin_ball :
        (Function.support (fun u => divisor (LFunction χ) (ball c (3 / 2)) u)).Finite :=
      divisor_ball_support_finite hana_cb.meromorphicOn
    have hfin_cb :
        (Function.support (fun u => divisor (LFunction χ) (closedBall c (3 / 2)) u)).Finite :=
      (divisor (LFunction χ) (closedBall c (3 / 2))).finiteSupport (isCompact_closedBall _ _)
    have hmono : ∑ᶠ u, divisor (LFunction χ) (ball c (3 / 2)) u
        ≤ ∑ᶠ u, divisor (LFunction χ) (closedBall c (3 / 2)) u :=
      finsum_le_finsum' hfin_ball hfin_cb hdle
    have hsphere := LFunction_growth_sphere χ hχ hf t₀
    have hcountJ := LFunction_zero_count_le χ hne t₀ (r := 3 / 2) (R := 7 / 4) (M := M₀)
      (by norm_num) (by norm_num) hM₀1 hsphere
    calc ∑ ρ ∈ Z', (m₈ ρ : ℝ)
        = ((∑ ρ ∈ Z', (m₈ ρ : ℤ) : ℤ) : ℝ) := by push_cast; ring
      _ = ((∑ᶠ u, divisor (LFunction χ) (ball c (3 / 2)) u : ℤ) : ℝ) := by rw [e1, e2]
      _ ≤ ((∑ᶠ u, divisor (LFunction χ) (closedBall c (3 / 2)) u : ℤ) : ℝ) := by
          exact_mod_cast hmono
      _ ≤ Real.log (4 * M₀) / Real.log (7 / 4 / (3 / 2)) := hcountJ
      _ = Real.log (4 * M₀) / Real.log (7 / 6) := by
          rw [show (7 : ℝ) / 4 / (3 / 2) = 7 / 6 by norm_num]
  -- ============================================================================
  -- `hsup` via the maximum-modulus principle
  -- ============================================================================
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
      have hEw : LFunction χ w = P₈ w * g₈ w := hEqOn₈ hwU
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
      have hGnorm : ‖G w‖ = ‖LFunction χ w‖ := by
        have hGw : G w = g₈ w * (Pout w * ∏ ρ ∈ Z', (reflectedFactor c ρ w) ^ (m₈ ρ)) := by
          change h' w * (∏ ρ ∈ Z', (reflectedFactor c ρ w) ^ (m₈ ρ)) = _
          rw [show h' w = g₈ w * Pout w from rfl]; ring
        rw [hGw, norm_mul, hkey_norm, mul_comm, ← norm_mul, ← hEw]
      have hLw_bound : ‖LFunction χ w‖ ≤ M₀ := by
        have hzc : |w.re - 2| ≤ 3 / 2 := by
          have h := Complex.abs_re_le_norm (w - c)
          rw [Complex.sub_re, hcre, hw] at h; exact h
        have hre_lb : (1 : ℝ) / 2 ≤ w.re := by have := abs_le.mp hzc; linarith [this.1]
        have hre_ub : w.re ≤ 4 := by have := abs_le.mp hzc; linarith [this.2]
        have hgrow := LFunction_growth χ hχ hf hre_lb hre_ub
        have hcnorm : ‖c‖ ≤ 2 + |t₀| := by
          rw [hc]
          calc ‖(2 : ℂ) + (t₀ : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(t₀ : ℂ) * I‖ := norm_add_le _ _
            _ = 2 + |t₀| := by
                rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
                norm_num
        have hwnorm : ‖w‖ ≤ 7 / 2 + |t₀| := by
          calc ‖w‖ = ‖c + (w - c)‖ := by ring_nf
            _ ≤ ‖c‖ + ‖w - c‖ := norm_add_le _ _
            _ ≤ (2 + |t₀|) + 3 / 2 := by rw [hw]; linarith [hcnorm]
            _ = 7 / 2 + |t₀| := by ring
        have hPnn : (0 : ℝ) ≤ Real.sqrt f * (1 + Real.log f) := sqrtlog_nonneg hf
        have hfac : 3 * (1 + ‖w‖) ≤ 5 * (4 + |t₀|) := by linarith [hwnorm, abs_nonneg t₀]
        rw [hM₀def]
        calc ‖LFunction χ w‖ ≤ 3 * (1 + ‖w‖) * Real.sqrt f * (1 + Real.log f) := hgrow
          _ = (3 * (1 + ‖w‖)) * (Real.sqrt f * (1 + Real.log f)) := by ring
          _ ≤ (5 * (4 + |t₀|)) * (Real.sqrt f * (1 + Real.log f)) :=
              mul_le_mul_of_nonneg_right hfac hPnn
          _ = 5 * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f) := by ring
      calc ‖G w‖ = ‖LFunction χ w‖ := hGnorm
        _ ≤ M₀ := hLw_bound
    intro z hz
    have hzcl : z ∈ closure (ball c (3 / 2)) := by
      rw [closure_ball c (by norm_num : (3 / 2 : ℝ) ≠ 0)]; exact ball_subset_closedBall hz
    exact norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdcc hbdry hzcl
  -- ============================================================================
  -- Assemble
  -- ============================================================================
  refine ⟨Z', m₈, h', inv_memb, inv_ana, inv_ne, inv_eqon, inv_ident, ?_⟩
  intro s hs hLs
  exact norm_logDeriv_sub_sum_of_blaschke hM₀1 hLc (fun ρ hρ => (inv_memb ρ hρ).1) hcount
    inv_ana inv_ne inv_eqon inv_ident hsup hs hLs

end Salt.SW
