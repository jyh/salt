/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.ZeroCount
import Salt.SW.Growth

/-!
# The SW rung, node S2-Z3 — the L'/L partial-fraction expansion near the 1-line

Design: `docs/blueprints/sw.md`, wave S2 (the L'/L zero-counting cluster). This is the
classical Landau lemma (Davenport §16 shape) made explicit: on a disk about the comfortable
center `c = 2 + it₀`, the finitely many zeros `ρ` of the Dirichlet L-function are factored
out, leaving an analytic *non-vanishing* remainder `h`, and the logarithmic derivative splits
as `L'/L = Σ_ρ m_ρ/(s−ρ) + h'/h`.

## Route (the L-specific assembly the ZeroCount docstring flagged for Z3)

`L(·,χ)` is entire for `χ ≠ 1` (`differentiable_LFunction`) and non-vanishing at `c`
(`LFunction_center_lower`: `‖L(c,χ)‖ ≥ 1/4`), hence it is not locally constant zero on the
open ball `ball c (3/2)`. mathlib's `MeromorphicOn.extract_zeros_poles` supplies a factorization
`L =ᶠ[codiscreteWithin] (∏ᶠ ρ, (·−ρ)^(divisor L u)) • g` with `g` analytic and non-vanishing;
because `L` is entire the divisor is *non-negative* (`AnalyticOnNhd.divisor_nonneg`), so the
factorized-rational part is an honest polynomial `P = ∏_{ρ∈Z} (·−ρ)^{m_ρ}` (a `Finset` product,
`Z` the finite support of the divisor, `m_ρ` the multiplicities). Both `L` and `P·g` are analytic
on the connected `ball c (3/2)`, and they agree on the codiscrete set, so the **identity theorem**
(`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, fed from
`mem_codiscreteWithin_iff_forall_mem_nhdsNE` at the center) upgrades the codiscrete equality to a
*pointwise* one: `L = P·g` on the whole disk. The logarithmic-derivative algebra
(`logDeriv_mul`, `logDeriv_prod`, `logDeriv_fun_pow`) then gives, at every non-zero point,
`L'/L − Σ_{ρ∈Z} m_ρ/(s−ρ) = g'/g` (multiplicities respected in the sum). Finally the
zero count `Σ_{ρ∈Z} m_ρ` is bounded by the landed Jensen keystone `LFunction_zero_count_le`
(with the `LFunction_growth_sphere` sup on the 7/4-sphere) — uniform in the modulus.

## Main results

* `LFunction_exists_factorization` — the general factorization + logarithmic-derivative identity
  on any disk `ball c R` about a point where `L ≠ 0` (`χ ≠ 1`).
* `LFunction_partialFraction` — the S2-Z3 target, specialized to `c = 2 + it₀`, `R = 3/2`
  (nested inside the 7/4 growth sphere). Delivers the three frozen S3 consumables:
  the **membership/zero-hood** facts (`∀ ρ ∈ Z, ρ ∈ ball c (3/2) ∧ L ρ = 0`), the
  **cardinality-with-multiplicity** bound `Σ_{ρ∈Z} m_ρ ≤ log(4M₀)/log(7/6)` (with
  `M₀ = 5(4+|t₀|)√f(1+log f)`, the growth-sphere sup — `O(log(f(|t₀|+2)))`), and the
  **sum-minus-logDeriv identity** `L'/L − Σ_{ρ∈Z} m_ρ/(s−ρ) = h'/h` at every non-zero `s`
  in the disk (the region S3 evaluates in — including `Re s` slightly left of `1` — lies inside
  `ball c (3/2)`, so no clipping at the 1-line).
* `norm_logDeriv_sub_sum_le` — the hypothesis-parameterized transfer: once the `‖h'/h‖` estimate
  lands, the sum-minus-logDeriv *norm* bound `‖L'/L − Σ_ρ m_ρ/(s−ρ)‖ ≤ B` follows verbatim.

## Flag (the Borel–Carathéodory remainder, PB-floor boundary)

The one classical step **not** discharged here is the numeric estimate
`‖h'/h‖ ≤ C₁·log M₀` on an inner sub-disk, i.e. bounding `g'/g` for the non-vanishing factor `g`.
The reusable engine is landed — `Salt.SW.norm_deriv_le_of_re_le` (Borel–Carathéodory + Cauchy) —
and applies to `G := Complex.log (g/g(c))` (whose derivative is `g'/g`, whose real part is
`log(‖g‖/‖g(c)‖)`). Where the B–C application currently breaks: it needs an *upper* bound on
`Re G = log(‖g‖/‖g(c)‖)` on the mid-disk, i.e. `‖g‖ = ‖L‖/‖P‖` bounded above; `‖L‖ ≤ M₀` is in
hand (`LFunction_growth_sphere` + maximum modulus) but `‖P‖ = ∏‖·−ρ‖` has no uniform *lower*
bound near the zeros — the classical fix replaces the linear factors `(·−ρ)` by Blaschke
factors (modulus one on the boundary; mathlib's `Complex.canonicalFactor`,
`norm_canonicalFactor_eval_circle_eq_one`), whose logarithmic derivative differs from
`Σ m_ρ/(s−ρ)` by an `O(1/R)`-per-zero correction absorbed into `O(log M₀)`. Threading the
Blaschke normalization through `extract_zeros_poles`'s (linear) factorization + the
`Complex.log`-branch existence on the ball is the remaining Z3 plumbing; it consumes the identity
and h-non-vanishing landed here and closes `norm_logDeriv_sub_sum_le`'s hypothesis. Until then the
`‖h'/h‖` bound is the single stated hypothesis (of `norm_logDeriv_sub_sum_le`).
-/

namespace Salt.SW

open Complex Metric MeromorphicOn Function DirichletCharacter Set Filter
open scoped Topology

/-! ## 1. Logarithmic derivative of a finite product of linear powers -/

/-- The logarithmic derivative of `∏_{ρ∈Z} (·−ρ)^{m_ρ}` at a point `s` avoiding every `ρ ∈ Z`
is the partial-fraction sum `∑_{ρ∈Z} m_ρ/(s−ρ)` (multiplicities respected). -/
lemma logDeriv_prod_pow (Z : Finset ℂ) (m : ℂ → ℕ) {s : ℂ} (hs : ∀ ρ ∈ Z, s ≠ ρ) :
    logDeriv (fun z => ∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) s = ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) := by
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro ρ _
    have hd : DifferentiableAt ℂ (fun z : ℂ => z - ρ) s := by fun_prop
    rw [logDeriv_fun_pow hd]
    have hid : logDeriv (fun z : ℂ => z - ρ) s = 1 / (s - ρ) := by
      rw [logDeriv_apply, deriv_sub_const]; simp
    rw [hid]; ring
  · intro ρ hρ
    exact pow_ne_zero _ (sub_ne_zero.mpr (hs ρ hρ))
  · intro ρ _
    fun_prop

/-! ## 2. The factorization and the logarithmic-derivative identity (general disk) -/

/-- **The Landau factorization.** For a nontrivial Dirichlet character `χ`, a center `c` with
`L(c,χ) ≠ 0`, and any radius `R > 0`, the entire function `L(·,χ)` factors on `ball c R` as
`L = (∏_{ρ∈Z} (·−ρ)^{m_ρ}) · h` with:

* `Z` a finite set of genuine zeros of `L` in `ball c R`, `m_ρ` their multiplicities;
* `h` analytic and *non-vanishing* on `ball c R`;
* the cardinality-with-multiplicity `∑_{ρ∈Z} m_ρ` equal to the ball-divisor zero count
  `∑ᶠ u, divisor L (ball c R) u`;
* the **logarithmic-derivative partial-fraction identity**
  `L'/L(s) − ∑_{ρ∈Z} m_ρ/(s−ρ) = h'/h(s)` at every `s ∈ ball c R` with `L(s) ≠ 0`.

Route: `MeromorphicOn.extract_zeros_poles` (codiscrete factorization), upgraded to a pointwise
identity by the analytic identity theorem (both sides are analytic on the connected ball and agree
on a codiscrete set); then `logDeriv_mul`/`logDeriv_prod_pow`. -/
theorem LFunction_exists_factorization {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (c : ℂ) {R : ℝ} (hR : 0 < R) (hc : LFunction χ c ≠ 0) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ ρ ∈ Z, ρ ∈ ball c R ∧ LFunction χ ρ = 0) ∧
      AnalyticOnNhd ℂ h (ball c R) ∧ (∀ z ∈ ball c R, h z ≠ 0) ∧
      Set.EqOn (LFunction χ) (fun z => (∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) * h z) (ball c R) ∧
      ((∑ ρ ∈ Z, (m ρ : ℤ)) = ∑ᶠ u, divisor (LFunction χ) (ball c R) u) ∧
      (∀ s ∈ ball c R, LFunction χ s ≠ 0 →
        logDeriv (LFunction χ) s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) = logDeriv h s) := by
  set U : Set ℂ := ball c R with hU
  have hUo : IsOpen U := isOpen_ball
  have hpre : IsPreconnected U := (convex_ball c R).isPreconnected
  have hcU : c ∈ U := mem_ball_self hR
  have hana_univ : AnalyticOnNhd ℂ (LFunction χ) univ :=
    (differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ
  have hana : AnalyticOnNhd ℂ (LFunction χ) U := hana_univ.mono (subset_univ _)
  -- order finiteness: `L` is not locally zero anywhere (else `L ≡ 0`, contradicting `L c ≠ 0`)
  have h₂f : ∀ u : U, meromorphicOrderAt (LFunction χ) (u : ℂ) ≠ ⊤ := by
    intro u htop
    rw [meromorphicOrderAt_eq_top_iff] at htop
    have hfreq : ∃ᶠ z in 𝓝[≠] (u : ℂ), LFunction χ z = 0 := htop.frequently
    have hz : Set.EqOn (LFunction χ) 0 U :=
      hana.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre u.2 hfreq
    exact hc (hz hcU)
  have h₃f : (divisor (LFunction χ) U).support.Finite :=
    divisor_ball_support_finite (hana_univ.mono (subset_univ _)).meromorphicOn
  obtain ⟨g, hg_ana, hg_ne, hg_eq⟩ := hana.meromorphicOn.extract_zeros_poles h₂f h₃f
  set Zfin : Finset ℂ := h₃f.toFinset with hZfin
  set m : ℂ → ℕ := fun ρ => ((divisor (LFunction χ) U) ρ).toNat with hm
  set P : ℂ → ℂ := fun z => ∏ ρ ∈ Zfin, (z - ρ) ^ (m ρ) with hP
  have hdivnn : ∀ u, 0 ≤ (divisor (LFunction χ) U) u := hana.divisor_nonneg
  -- bridge the codiscrete finprod factor to the honest polynomial `P`
  have hsub : mulSupport (fun u : ℂ => ((· - u) ^ (divisor (LFunction χ) U u) : ℂ → ℂ))
      ⊆ ↑Zfin := by
    intro u hu
    simp only [hZfin, Finite.coe_toFinset, Function.mem_support]
    intro hd0
    apply hu
    simp [hd0]
  have hfun : (∏ᶠ u, ((· - u) ^ (divisor (LFunction χ) U u) : ℂ → ℂ)) = P := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    funext z
    rw [hP]
    simp only [Finset.prod_apply, Pi.pow_apply]
    apply Finset.prod_congr rfl
    intro u _
    rw [← Int.toNat_of_nonneg (hdivnn u), zpow_natCast]
  have hg_eq2 : LFunction χ =ᶠ[codiscreteWithin U] (fun z => P z * g z) := by
    filter_upwards [hg_eq] with z hz
    rw [hz, hfun]
    simp [Pi.smul_apply', smul_eq_mul]
  have hP_ana : AnalyticOnNhd ℂ P U := by
    rw [hP]
    exact Finset.analyticOnNhd_fun_prod Zfin (fun ρ _ => by
      apply AnalyticOnNhd.pow
      exact (analyticOnNhd_id.sub analyticOnNhd_const))
  have hPg_ana : AnalyticOnNhd ℂ (fun z => P z * g z) U := hP_ana.mul hg_ana
  -- upgrade codiscrete equality to pointwise equality via the identity theorem
  have hev : ∀ᶠ z in 𝓝[≠] c, LFunction χ z = P z * g z := by
    have h1 : ({z | LFunction χ z = P z * g z} ∪ Uᶜ) ∈ 𝓝[≠] c :=
      mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hg_eq2 c hcU
    have h2 : U ∈ 𝓝[≠] c := mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hcU)
    filter_upwards [h1, h2] with z hz hzU
    rcases hz with hz | hz
    · exact hz
    · exact absurd hzU hz
  have hEqOn : Set.EqOn (LFunction χ) (fun z => P z * g z) U :=
    hana.eqOn_of_preconnected_of_frequently_eq hPg_ana hpre hcU hev.frequently
  have hg_ne' : ∀ z ∈ U, g z ≠ 0 := fun z hz => hg_ne ⟨z, hz⟩
  -- membership / zero-hood of the elements of `Zfin`
  have hmem : ∀ ρ ∈ Zfin, (divisor (LFunction χ) U) ρ ≠ 0 ∧ ρ ∈ U := by
    intro ρ hρ
    have hρsupp : (divisor (LFunction χ) U) ρ ≠ 0 := by
      rw [hZfin, Finite.mem_toFinset, Function.mem_support] at hρ; exact hρ
    have hρU : ρ ∈ U := by
      by_contra hnU
      exact hρsupp (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hnU)
    exact ⟨hρsupp, hρU⟩
  have hmemZ : ∀ ρ ∈ Zfin, ρ ∈ U ∧ LFunction χ ρ = 0 := by
    intro ρ hρ
    obtain ⟨hρsupp, hρU⟩ := hmem ρ hρ
    refine ⟨hρU, ?_⟩
    by_contra hne0
    apply hρsupp
    rw [hana.divisor_apply hρU, (hana ρ hρU).analyticOrderAt_eq_zero.mpr hne0]
    simp
  have hmZ : ∀ ρ ∈ Zfin, (m ρ : ℤ) = divisor (LFunction χ) U ρ := by
    intro ρ _
    rw [hm]
    exact Int.toNat_of_nonneg (hdivnn ρ)
  have hsupp_sub : Function.support (fun u => (divisor (LFunction χ) U) u) ⊆ ↑Zfin := by
    rw [hZfin, Set.Finite.coe_toFinset]
  have hcard : (∑ ρ ∈ Zfin, (m ρ : ℤ)) = ∑ᶠ u, divisor (LFunction χ) U u := by
    rw [finsum_eq_finsetSum_of_support_subset _ hsupp_sub]
    exact Finset.sum_congr rfl fun ρ hρ => hmZ ρ hρ
  refine ⟨Zfin, m, g, hmemZ, hg_ana, hg_ne', hEqOn, hcard, ?_⟩
  -- the logarithmic-derivative partial-fraction identity at non-zero points
  intro s hsU hsne
  have hsρ : ∀ ρ ∈ Zfin, s ≠ ρ := by
    intro ρ hρ hsρ
    exact hsne (hsρ ▸ (hmemZ ρ hρ).2)
  have hPs : P s ≠ 0 := by
    rw [hP]
    exact Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hsρ ρ hρ))
  have hgs : g s ≠ 0 := hg_ne' s hsU
  have hlocal : LFunction χ =ᶠ[𝓝 s] (fun z => P z * g z) := by
    filter_upwards [hUo.mem_nhds hsU] with z hz; exact hEqOn hz
  have hPdiff : DifferentiableAt ℂ P s := (hP_ana s hsU).differentiableAt
  have hgdiff : DifferentiableAt ℂ g s := (hg_ana s hsU).differentiableAt
  have hlogL : logDeriv (LFunction χ) s = logDeriv (fun z => P z * g z) s := by
    rw [logDeriv_apply, logDeriv_apply, hlocal.deriv_eq, hlocal.eq_of_nhds]
  have hlogPg : logDeriv (fun z => P z * g z) s = logDeriv P s + logDeriv g s :=
    logDeriv_mul s hPs hgs hPdiff hgdiff
  have hlogP : logDeriv P s = ∑ ρ ∈ Zfin, (m ρ : ℂ) / (s - ρ) := by
    rw [hP]; exact logDeriv_prod_pow Zfin m hsρ
  rw [hlogL, hlogPg, hlogP]; ring

/-! ## 3. The S2-Z3 target on the disk about `c = 2 + it₀` -/

/-- **S2-Z3 — the L'/L partial-fraction expansion near the 1-line.** For a primitive Dirichlet
character `χ` mod `f ≥ 2` and `t₀ ∈ ℝ`, on the disk `ball (2 + it₀) (3/2)` (nested inside the 7/4
growth sphere) there is a finite set `Z` of zeros of `L(·,χ)` with multiplicities `m` and an
analytic non-vanishing remainder `h` such that:

* every `ρ ∈ Z` is a genuine zero of `L` in the disk (membership / zero-hood);
* `∑_{ρ∈Z} m_ρ ≤ log(4·M₀)/log(7/6)` with `M₀ = 5(4+|t₀|)√f(1+log f)` — the Jensen zero count
  (`O(log(f(|t₀|+2)))`, uniform in `f`) — cardinality with multiplicity;
* `L = (∏_{ρ∈Z} (·−ρ)^{m_ρ})·h` on the disk;
* `L'/L(s) − ∑_{ρ∈Z} m_ρ/(s−ρ) = h'/h(s)` at every `s` in the disk with `L(s) ≠ 0` — the
  sum-minus-logDeriv identity (the region S3 evaluates in, with `Re s` slightly left of `1`, lies
  inside `ball (2+it₀) (3/2)`).

The remaining `‖h'/h‖ ≤ C·log M₀` estimate (Borel–Carathéodory on the inner disk) closes the
numeric bound via `norm_logDeriv_sub_sum_le`; see the module flag. -/
theorem LFunction_partialFraction {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (t₀ : ℝ) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ ρ ∈ Z, ρ ∈ ball (2 + (t₀ : ℂ) * I) (3 / 2) ∧ LFunction χ ρ = 0) ∧
      ((∑ ρ ∈ Z, (m ρ : ℝ)) ≤
        Real.log (4 * (5 * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f))) / Real.log (7 / 6)) ∧
      AnalyticOnNhd ℂ h (ball (2 + (t₀ : ℂ) * I) (3 / 2)) ∧
      (∀ z ∈ ball (2 + (t₀ : ℂ) * I) (3 / 2), h z ≠ 0) ∧
      Set.EqOn (LFunction χ) (fun z => (∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) * h z)
        (ball (2 + (t₀ : ℂ) * I) (3 / 2)) ∧
      (∀ s ∈ ball (2 + (t₀ : ℂ) * I) (3 / 2), LFunction χ s ≠ 0 →
        logDeriv (LFunction χ) s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) = logDeriv h s) := by
  have hne : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  set c : ℂ := 2 + (t₀ : ℂ) * I with hc
  have hcre : c.re = 2 := by rw [hc]; simp
  have hc0 : LFunction χ c ≠ 0 := by
    have hcl := LFunction_center_lower χ (le_of_eq hcre.symm)
    intro h0; rw [h0, norm_zero] at hcl; linarith
  obtain ⟨Z, m, h, hmemZ, hana_h, hne_h, hEqOn, hcard, hident⟩ :=
    LFunction_exists_factorization χ hne c (R := 3 / 2) (by norm_num) hc0
  refine ⟨Z, m, h, hmemZ, ?_, hana_h, hne_h, hEqOn, hident⟩
  -- cardinality with multiplicity ≤ Jensen count
  set M₀ : ℝ := 5 * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f) with hM₀
  have hlog2 : (0 : ℝ) ≤ Real.log f := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ f))
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt f := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt; exact_mod_cast (by omega : 1 ≤ f)
  have hM₀1 : 1 ≤ M₀ := by
    have ha : (4 : ℝ) ≤ 4 + |t₀| := by linarith [abs_nonneg t₀]
    have hll : (1 : ℝ) ≤ 1 + Real.log f := by linarith [hlog2]
    have p1 : (20 : ℝ) ≤ 5 * (4 + |t₀|) := by linarith
    have hp1nn : (0 : ℝ) ≤ 5 * (4 + |t₀|) := by linarith
    have p2 : (20 : ℝ) ≤ 5 * (4 + |t₀|) * Real.sqrt f := by
      nlinarith [mul_nonneg hp1nn (by linarith [hsqrt1] : (0 : ℝ) ≤ Real.sqrt f - 1), p1]
    have hp2nn : (0 : ℝ) ≤ 5 * (4 + |t₀|) * Real.sqrt f := by linarith
    have p3 : (20 : ℝ) ≤ 5 * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f) := by
      nlinarith [mul_nonneg hp2nn (by linarith [hll] : (0 : ℝ) ≤ (1 + Real.log f) - 1), p2]
    rw [hM₀]; linarith [p3]
  have hsphere := LFunction_growth_sphere χ hχ hf t₀
  have hcount := LFunction_zero_count_le χ hne t₀ (r := 3 / 2) (R := 7 / 4) (M := M₀)
    (by norm_num) (by norm_num) hM₀1 hsphere
  have hana_ball : AnalyticOnNhd ℂ (LFunction χ) (ball c (3 / 2)) :=
    ((differentiable_LFunction hne).differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  have hana_cb : AnalyticOnNhd ℂ (LFunction χ) (closedBall c (3 / 2)) :=
    ((differentiable_LFunction hne).differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  -- the ball-divisor count is ≤ the closedBall-divisor count (extra sphere zeros only help)
  have hdle : ∀ u : ℂ, divisor (LFunction χ) (ball c (3 / 2)) u
      ≤ divisor (LFunction χ) (closedBall c (3 / 2)) u := by
    intro u
    by_cases hu : u ∈ ball c (3 / 2)
    · exact le_of_eq (by rw [hana_ball.divisor_apply hu,
        hana_cb.divisor_apply (ball_subset_closedBall hu)])
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      exact hana_cb.divisor_nonneg u
  have hfin_ball : (Function.support (fun u => divisor (LFunction χ) (ball c (3 / 2)) u)).Finite :=
    divisor_ball_support_finite hana_cb.meromorphicOn
  have hfin_cb :
      (Function.support (fun u => divisor (LFunction χ) (closedBall c (3 / 2)) u)).Finite :=
    (divisor (LFunction χ) (closedBall c (3 / 2))).finiteSupport (isCompact_closedBall _ _)
  have hmono : ∑ᶠ u, divisor (LFunction χ) (ball c (3 / 2)) u
      ≤ ∑ᶠ u, divisor (LFunction χ) (closedBall c (3 / 2)) u :=
    finsum_le_finsum' hfin_ball hfin_cb hdle
  have key : (∑ ρ ∈ Z, (m ρ : ℤ)) ≤ ∑ᶠ u, divisor (LFunction χ) (closedBall c (3 / 2)) u :=
    hcard ▸ hmono
  calc ∑ ρ ∈ Z, (m ρ : ℝ) = ((∑ ρ ∈ Z, (m ρ : ℤ) : ℤ) : ℝ) := by push_cast; ring
    _ ≤ ((∑ᶠ u, divisor (LFunction χ) (closedBall c (3 / 2)) u : ℤ) : ℝ) := by exact_mod_cast key
    _ ≤ Real.log (4 * M₀) / Real.log (7 / 4 / (3 / 2)) := hcount
    _ = Real.log (4 * M₀) / Real.log (7 / 6) := by
        rw [show (7 : ℝ) / 4 / (3 / 2) = 7 / 6 by norm_num]

/-! ## 4. The hypothesis-parameterized transfer to the numeric bound -/

/-- **The S3 transfer** (the single stated hypothesis of the Landau lemma). Given the
sum-minus-logDeriv *identity* `L'/L(s) − ∑_ρ m_ρ/(s−ρ) = h'/h(s)` (from `LFunction_partialFraction`)
and any bound `‖h'/h(s)‖ ≤ B` (the Borel–Carathéodory estimate, the flagged remainder), the
sum-minus-logDeriv *norm* bound `‖L'/L(s) − ∑_ρ m_ρ/(s−ρ)‖ ≤ B` follows verbatim. -/
theorem norm_logDeriv_sub_sum_le {L h : ℂ → ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {s : ℂ} {B : ℝ}
    (hident : logDeriv L s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) = logDeriv h s)
    (hbound : ‖logDeriv h s‖ ≤ B) :
    ‖logDeriv L s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ B := by
  rw [hident]; exact hbound

end Salt.SW
