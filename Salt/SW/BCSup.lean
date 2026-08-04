/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.MaxModulus
import Salt.SW.EFSharpMult

/-!
# The SW rung, node S2-Z3d — the partial fraction's remainder **difference** (Davenport ch. 12 (17))

Design: `docs/blueprints/sw.md`, wave S2; consumed by the fulcrum campaign's node N4a
(`Salt/HB/TwistedMertens.lean`).

## The `hsup` verdict (recorded here, loudly)

The fulcrum road carried `hrem` as "blocked behind `hsup`, the PB-floor flag of
`Salt/SW/BCBound.lean`".  **`hsup` is not a blocker: it was discharged months earlier by
`Salt/SW/MaxModulus.lean`** (`LFunction_norm_logDeriv_sub_sum'`, the ungated S2-Z3c endpoint,
via the radius-`8/5` re-factorization + the boundary modulus identity + max-modulus).  The
module flag at the head of `BCBound.lean` describes the *gated* lemma in that file and was read
as a live obligation; the ungated endpoint one file over supersedes it.  So the only thing the
`O(a)`-size remainder *difference* ever needed was the Cauchy/Schwarz step below.

## What this file lands

Write `A := L'/L − ∑_ρ m_ρ/(s−ρ)`.  On `ball c (3/2)` the partial fraction identifies `A` with
`logDeriv h`, `h` analytic and non-vanishing — so `A` is **analytic on the whole disk**, and the
S2-Z3c endpoint bounds it by `B := 120·log(4M₀)` on `‖s−c‖ ≤ 23/20`.  A uniform `O(L)` bound on a
disk plus analyticity is exactly the hypothesis of a Cauchy estimate, and the derivative bound
converts to an `O(L)·|σ−σ'|` **difference** bound by the mean value theorem.  At HB's operating
points `σ = 1+L^{−1}`, `σ' = 1+aL^{−1}` this is `O(a)` — Davenport ch. 12 (17), in the only shape
the differencing consumes.

Three steps, all unconditional:

* `norm_logDeriv_le_of_bound_off_zeros` — the S2-Z3c bound is stated only where `L s ≠ 0`
  (the partial-fraction identity needs it), but `logDeriv h` is analytic *through* the zeros and
  they are finitely many, so the bound extends to the full disk by continuity along `𝓝[≠]`.
* `norm_sub_le_of_norm_le_on_ball` — Schwarz (`Complex.norm_deriv_le_div_of_mapsTo_ball`) on the
  radius-`3/20` disk around each point of `closedBall c 1` gives `‖A'‖ ≤ 2B/(3/20) = 40B/3`
  there, and `Convex.norm_image_sub_le_of_norm_deriv_le` turns that into the Lipschitz bound.
* `LFunction_partialFraction_remainder_diff` — the endpoint at `t₀ = 0` (HB's line is real):
  for `1 ≤ σ, σ' ≤ 2`,
  `‖A(σ) − A(σ')‖ ≤ 1600·log(80√f(1+log f))·|σ−σ'|`.

## The two export items, also landed here

`LFunction_partialFraction`'s `Z`/`m` are exported only as "`ρ ∈ Z ⟹ L ρ = 0`" with `m` opaque.
Both defects are closed **from the exported invariants alone**, no re-derivation:

* `mem_of_LFunction_eq_zero` — the converse: a zero of `L` in the disk *is* in `Z`, with
  `m ≥ 1` (from `L = P·h`, `h` non-vanishing).  This is N4a's `hβZ` + `hmβ`.
* `multiplicity_eq_zeroMult` — `m ρ = zeroMult χ ρ` on `Z` (the local factorization
  `L = (·−ρ)^{m_ρ}·G` with `G ρ ≠ 0` *is* the `analyticOrderNatAt` characterization).  This is
  N4a's `hmz`, at equality rather than `≤`.
-/

namespace Salt.SW

open Complex Metric MeromorphicOn Function DirichletCharacter Set Filter
open scoped Topology

/-! ## 1. The sup bound extends across the zeros -/

/-- **The bound crosses the zeros.**  A bound on `‖logDeriv h‖` valid only off the zero set of
`L = (∏(·−ρ)^{m_ρ})·h` extends to *all* of `ball c r`: `logDeriv h` is analytic there (`h` is
analytic and non-vanishing), and the zeros of `L` in the disk are the finitely many points of
`Z`, so every one of them is approached through points where the bound already holds. -/
lemma norm_logDeriv_le_of_bound_off_zeros {L h : ℂ → ℂ} {c : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ}
    {r B : ℝ} (hr : r ≤ 3 / 2)
    (hana_h : AnalyticOnNhd ℂ h (ball c (3 / 2)))
    (hne_h : ∀ z ∈ ball c (3 / 2), h z ≠ 0)
    (hEqOn : Set.EqOn L (fun z => (∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) * h z) (ball c (3 / 2)))
    (hbd : ∀ z ∈ ball c r, L z ≠ 0 → ‖logDeriv h z‖ ≤ B) :
    ∀ z ∈ ball c r, ‖logDeriv h z‖ ≤ B := by
  classical
  have hsub : ball c r ⊆ ball c (3 / 2) := ball_subset_ball hr
  have hFeq : logDeriv h = fun z => deriv h z / h z := funext (logDeriv_apply h)
  have hF_ana : AnalyticOnNhd ℂ (logDeriv h) (ball c (3 / 2)) := by
    rw [hFeq]; exact hana_h.deriv.div hana_h hne_h
  have hLne : ∀ w ∈ ball c (3 / 2), w ∉ Z → L w ≠ 0 := by
    intro w hw hwZ
    have hval : L w = (∏ ρ ∈ Z, (w - ρ) ^ (m ρ)) * h w := hEqOn hw
    rw [hval]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr ?_) (hne_h w hw)
    intro ρ hρ
    refine pow_ne_zero _ (sub_ne_zero.mpr ?_)
    rintro rfl
    exact hwZ hρ
  intro z hz
  by_cases hLz : L z = 0
  · have hzmem : z ∈ ball c r \ (↑(Z.erase z) : Set ℂ) := by
      refine ⟨hz, ?_⟩
      simp
    have hopen : IsOpen (ball c r \ (↑(Z.erase z) : Set ℂ)) :=
      isOpen_ball.sdiff (Z.erase z).finite_toSet.isClosed
    have hev : ∀ᶠ w in 𝓝[≠] z, ‖logDeriv h w‖ ≤ B := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hzmem), self_mem_nhdsWithin]
        with w hw hwne
      have hwne' : w ≠ z := by simpa using hwne
      have hwZ : w ∉ Z := by
        intro hcon
        exact hw.2 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hwne', hcon⟩))
      exact hbd w hw.1 (hLne w (hsub hw.1) hwZ)
    have hcont : ContinuousAt (fun w => ‖logDeriv h w‖) z :=
      ((hF_ana z (hsub hz)).continuousAt).norm
    exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
  · exact hbd z hz hLz

/-! ## 2. The Cauchy estimate and the Lipschitz difference bound -/

/-- **The difference bound from a sup bound.**  If `F` is analytic on `ball c (23/20)` and
`‖F‖ ≤ B` there, then `F` is `40B/3`-Lipschitz on `closedBall c 1`.  Route: Schwarz
(`Complex.norm_deriv_le_div_of_mapsTo_ball`) on the radius-`3/20` disk around each point — the
image lies in `closedBall (F u) (2B)`, so `‖F' u‖ ≤ 2B/(3/20)` — then the mean value theorem
on the convex set `closedBall c 1`. -/
lemma norm_sub_le_of_norm_le_on_ball {F : ℂ → ℂ} {c : ℂ} {B : ℝ} {z w : ℂ}
    (hana : AnalyticOnNhd ℂ F (ball c (23 / 20)))
    (hbd : ∀ u ∈ ball c (23 / 20), ‖F u‖ ≤ B)
    (hz : ‖z - c‖ ≤ 1) (hw : ‖w - c‖ ≤ 1) :
    ‖F z - F w‖ ≤ 40 / 3 * B * ‖z - w‖ := by
  have hcb : ∀ u : ℂ, ‖u - c‖ ≤ 1 → u ∈ ball c (23 / 20) := by
    intro u hu; rw [mem_ball, dist_eq_norm]; linarith
  have hmem : ∀ u : ℂ, u ∈ closedBall c 1 → ‖u - c‖ ≤ 1 := by
    intro u hu; rwa [mem_closedBall, dist_eq_norm] at hu
  have hconv : Convex ℝ (closedBall c 1) := convex_closedBall c 1
  have hdiff : ∀ u ∈ closedBall c 1, DifferentiableAt ℂ F u := fun u hu =>
    (hana u (hcb u (hmem u hu))).differentiableAt
  have hbound : ∀ u ∈ closedBall c 1, ‖deriv F u‖ ≤ 40 / 3 * B := by
    intro u hu
    have huc : ‖u - c‖ ≤ 1 := hmem u hu
    have hball : ball u (3 / 20) ⊆ ball c (23 / 20) := by
      intro v hv
      rw [mem_ball, dist_eq_norm] at hv ⊢
      have hvc : v - c = (v - u) + (u - c) := by ring
      rw [hvc]
      calc ‖(v - u) + (u - c)‖ ≤ ‖v - u‖ + ‖u - c‖ := norm_add_le _ _
        _ < 23 / 20 := by linarith
    have hd : DifferentiableOn ℂ F (ball u (3 / 20)) := (hana.mono hball).differentiableOn
    have hFu : ‖F u‖ ≤ B := hbd u (hcb u huc)
    have hmaps : MapsTo F (ball u (3 / 20)) (closedBall (F u) (2 * B)) := by
      intro v hv
      rw [mem_closedBall, dist_eq_norm]
      have h1 : ‖F v‖ ≤ B := hbd v (hball hv)
      calc ‖F v - F u‖ ≤ ‖F v‖ + ‖F u‖ := norm_sub_le _ _
        _ ≤ 2 * B := by linarith
    have hsch := Complex.norm_deriv_le_div_of_mapsTo_ball hd hmaps (by norm_num : (0 : ℝ) < 3 / 20)
    calc ‖deriv F u‖ ≤ 2 * B / (3 / 20) := hsch
      _ = 40 / 3 * B := by ring
  have hzs : z ∈ closedBall c 1 := by rw [mem_closedBall, dist_eq_norm]; exact hz
  have hws : w ∈ closedBall c 1 := by rw [mem_closedBall, dist_eq_norm]; exact hw
  exact hconv.norm_image_sub_le_of_norm_deriv_le hdiff hbound hws hzs

/-! ## 3. The two export items of `LFunction_partialFraction` -/

/-- **The converse membership (N4a's `hβZ` + `hmβ`).**  `LFunction_partialFraction` states only
`ρ ∈ Z ⟹ L ρ = 0`.  The converse follows from the factorization itself: `L z = P z · h z` with
`h` non-vanishing forces `P z = 0`, i.e. `z ∈ Z` with `m z ≥ 1`. -/
lemma mem_of_LFunction_eq_zero {L h : ℂ → ℂ} {c : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (hne_h : ∀ z ∈ ball c (3 / 2), h z ≠ 0)
    (hEqOn : Set.EqOn L (fun z => (∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) * h z) (ball c (3 / 2)))
    {z : ℂ} (hz : z ∈ ball c (3 / 2)) (hL : L z = 0) : z ∈ Z ∧ 1 ≤ m z := by
  classical
  have hval : L z = (∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) * h z := hEqOn hz
  have h1 : (∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) * h z = 0 := by rw [← hval]; exact hL
  have h2 : (∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) = 0 := by
    rcases mul_eq_zero.mp h1 with hp | hh
    · exact hp
    · exact absurd hh (hne_h z hz)
  obtain ⟨ρ, hρZ, hρ0⟩ := Finset.prod_eq_zero_iff.mp h2
  have hmne : m ρ ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hρ0
    exact one_ne_zero hρ0
  have hzρ : z = ρ := by
    have := pow_eq_zero_iff hmne |>.mp hρ0
    exact sub_eq_zero.mp this
  subst hzρ
  exact ⟨hρZ, Nat.one_le_iff_ne_zero.mpr hmne⟩

/-- **The multiplicity is the analytic order (N4a's `hmz`, at equality).**
`LFunction_partialFraction` hides `m` behind the existential, but the exported factorization
already pins it: near `ρ ∈ Z` we have `L = (·−ρ)^{m_ρ}·G` with `G` analytic and `G ρ ≠ 0`, which
is precisely `AnalyticAt.analyticOrderNatAt_eq_iff`.  Hence `m ρ = zeroMult χ ρ`. -/
lemma multiplicity_eq_zeroMult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    {c : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {h : ℂ → ℂ}
    (hana_h : AnalyticOnNhd ℂ h (ball c (3 / 2)))
    (hne_h : ∀ z ∈ ball c (3 / 2), h z ≠ 0)
    (hEqOn : Set.EqOn (LFunction χ) (fun z => (∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) * h z) (ball c (3 / 2)))
    {ρ : ℂ} (hρZ : ρ ∈ Z) (hρ : ρ ∈ ball c (3 / 2)) :
    m ρ = zeroMult χ ρ := by
  classical
  have hprod_ana : AnalyticOnNhd ℂ (fun z => ∏ ρ' ∈ Z.erase ρ, (z - ρ') ^ (m ρ'))
      (ball c (3 / 2)) :=
    Finset.analyticOnNhd_fun_prod _ (fun ρ' _ => (analyticOnNhd_id.sub analyticOnNhd_const).pow _)
  have hGana : AnalyticAt ℂ (fun z => (∏ ρ' ∈ Z.erase ρ, (z - ρ') ^ (m ρ')) * h z) ρ :=
    (hprod_ana ρ hρ).mul (hana_h ρ hρ)
  have hGne : (∏ ρ' ∈ Z.erase ρ, (ρ - ρ') ^ (m ρ')) * h ρ ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr ?_) (hne_h ρ hρ)
    intro ρ' hρ'
    exact pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ').symm)
  have hloc : ∀ᶠ z in 𝓝 ρ, LFunction χ z
      = (z - ρ) ^ (m ρ) • ((∏ ρ' ∈ Z.erase ρ, (z - ρ') ^ (m ρ')) * h z) := by
    filter_upwards [isOpen_ball.mem_nhds hρ] with z hz
    have hval : LFunction χ z = (∏ ρ' ∈ Z, (z - ρ') ^ (m ρ')) * h z := hEqOn hz
    rw [hval, smul_eq_mul, ← Finset.mul_prod_erase Z (fun ρ' => (z - ρ') ^ (m ρ')) hρZ]
    ring
  have hLana : AnalyticAt ℂ (LFunction χ) ρ :=
    ((differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ) ρ (mem_univ _)
  have hord := (hLana.analyticOrderNatAt_eq_iff (analyticOrderAt_LFunction_ne_top hχ1 ρ)).mpr
    ⟨fun z => (∏ ρ' ∈ Z.erase ρ, (z - ρ') ^ (m ρ')) * h z, hGana, hGne, hloc⟩
  simp only [zeroMult]
  exact hord.symm

/-! ## 4. The endpoint — the remainder difference at HB's real operating points -/

/-- **S2-Z3d — Davenport ch. 12 (17) in difference form.**  For a primitive `χ` mod `f ≥ 2`, on
the disk `ball 2 (3/2)` (the `t₀ = 0` partial fraction — HB's line is real) there is a finite set
`Z` of zeros with multiplicities `m` such that, writing `A(s) = L'/L(s) − ∑_ρ m_ρ/(s−ρ)`,

    ‖A(σ) − A(σ')‖ ≤ 1600·log(80√f(1+log f))·|σ − σ'|   for 1 ≤ σ, σ' ≤ 2.

At HB's operating points `σ = 1+L^{−1}`, `σ' = 1+aL^{−1}` the right side is
`1600·log(80√f(1+log f))·(a−1)/L = O(a)` — the `O(1)`-per-unit-`a` remainder the (4.1)/(4.2)
differencing consumes.  The exported `Z`, `m` come with the converse membership and
`m = zeroMult`, so N4a's `hβZ`, `hmβ`, `hmz` are all available from this one call. -/
theorem LFunction_partialFraction_remainder_diff {f : ℕ} [NeZero f]
    (χ : DirichletCharacter ℂ f) (hχ : χ.IsPrimitive) (hf : 2 ≤ f) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ Z, ρ ∈ ball (2 : ℂ) (3 / 2) ∧ LFunction χ ρ = 0) ∧
      (∀ z ∈ ball (2 : ℂ) (3 / 2), LFunction χ z = 0 → z ∈ Z ∧ 1 ≤ m z) ∧
      (∀ ρ ∈ Z, m ρ = zeroMult χ ρ) ∧
      (∀ σ σ' : ℝ, 1 ≤ σ → σ ≤ 2 → 1 ≤ σ' → σ' ≤ 2 →
        ‖(logDeriv (LFunction χ) (σ : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) - ρ))
          - (logDeriv (LFunction χ) (σ' : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ' : ℂ) - ρ))‖
          ≤ 1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f)) * |σ - σ'|) := by
  classical
  have hne1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  obtain ⟨Z, m, h, hmemZ, hana_h, hne_h, hEqOn, hident, hnum⟩ :=
    LFunction_norm_logDeriv_sub_sum' χ hχ hf 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hmemZ hana_h hne_h hEqOn hident hnum
  have hMval : (4 : ℝ) * (5 * (4 + |(0 : ℝ)|) * Real.sqrt f * (1 + Real.log f))
      = 80 * Real.sqrt f * (1 + Real.log f) := by rw [abs_zero]; ring
  rw [hMval] at hnum
  -- the sup bound on `logDeriv h`, valid through the zeros
  have hbd0 : ∀ z ∈ ball (2 : ℂ) (23 / 20), LFunction χ z ≠ 0 →
      ‖logDeriv h z‖ ≤ 120 * Real.log (80 * Real.sqrt f * (1 + Real.log f)) := by
    intro z hz hLz
    rw [mem_ball, dist_eq_norm] at hz
    have hz32 : z ∈ ball (2 : ℂ) (3 / 2) := by rw [mem_ball, dist_eq_norm]; linarith
    rw [← hident z hz32 hLz]
    exact hnum z (by linarith) hLz
  have hbd : ∀ z ∈ ball (2 : ℂ) (23 / 20),
      ‖logDeriv h z‖ ≤ 120 * Real.log (80 * Real.sqrt f * (1 + Real.log f)) :=
    norm_logDeriv_le_of_bound_off_zeros (by norm_num) hana_h hne_h hEqOn hbd0
  -- analyticity of `logDeriv h`
  have hFeq : logDeriv h = fun z => deriv h z / h z := funext (logDeriv_apply h)
  have hF_ana : AnalyticOnNhd ℂ (logDeriv h) (ball (2 : ℂ) (23 / 20)) := by
    rw [hFeq]
    exact (hana_h.deriv.div hana_h hne_h).mono (ball_subset_ball (by norm_num))
  refine ⟨Z, m, hmemZ, ?_, ?_, ?_⟩
  · intro z hz hLz
    exact mem_of_LFunction_eq_zero hne_h hEqOn hz hLz
  · intro ρ hρ
    exact multiplicity_eq_zeroMult hne1 hana_h hne_h hEqOn hρ (hmemZ ρ hρ).1
  · intro σ σ' hσ1 hσ2 hσ'1 hσ'2
    have hnorm_of : ∀ t : ℝ, 1 ≤ t → t ≤ 2 → ‖(t : ℂ) - 2‖ ≤ 1 := by
      intro t ht1 ht2
      have hcast : ((t : ℂ) - 2) = ((t - 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hball_of : ∀ t : ℝ, 1 ≤ t → t ≤ 2 → (t : ℂ) ∈ ball (2 : ℂ) (3 / 2) := by
      intro t ht1 ht2
      rw [mem_ball, dist_eq_norm]
      have := hnorm_of t ht1 ht2
      linarith
    have hLne_of : ∀ t : ℝ, 1 ≤ t → LFunction χ (t : ℂ) ≠ 0 := by
      intro t ht
      refine LFunction_ne_zero_of_one_le_re χ (Or.inl hne1) ?_
      simpa using ht
    rw [hident (σ : ℂ) (hball_of σ hσ1 hσ2) (hLne_of σ hσ1),
        hident (σ' : ℂ) (hball_of σ' hσ'1 hσ'2) (hLne_of σ' hσ'1)]
    have hlip := norm_sub_le_of_norm_le_on_ball (F := logDeriv h) (c := (2 : ℂ))
      (B := 120 * Real.log (80 * Real.sqrt f * (1 + Real.log f))) hF_ana hbd
      (hnorm_of σ hσ1 hσ2) (hnorm_of σ' hσ'1 hσ'2)
    have hdist : ‖(σ : ℂ) - (σ' : ℂ)‖ = |σ - σ'| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hdist] at hlip
    calc ‖logDeriv h (σ : ℂ) - logDeriv h (σ' : ℂ)‖
        ≤ 40 / 3 * (120 * Real.log (80 * Real.sqrt f * (1 + Real.log f))) * |σ - σ'| := hlip
      _ = 1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f)) * |σ - σ'| := by ring

end Salt.SW
