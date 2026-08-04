/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.ShiftVariants
import Salt.SW.EFSharp

/-!
# THE FULCRUM CAMPAIGN, node N1 — wave 2: **A1**, the enumerated contour shift

Wave 1 (`Salt/SW/EFSharp.lean`) reduced the sharp explicit formula
`psi_explicit_sharp_of_riesz_residues` to a single unmet hypothesis, named there **A1**:
the contour shift for the *smoothed* carrier `ψ₁` with the residues at an **enumerated
finite set of zeros** rather than at the corpus's single carved-out exceptional zero
(`Salt/SW/ShiftVariants.lean`, `psi1_contour_shift_exceptional`, whose `hzf` hypothesis says
"every zero in the box *is* `β₁`").

This module lands A1.

## What A1 says, and why the hypothesis has the shape it has

    ‖ψ₁(x,χ) + ∑_{ρ ∈ Z} x^{ρ+1}/(ρ(ρ+1))‖  ≤  E(x,T,σ₀,w,f)

with `E` **literally the landed `psi1_contour_shift_exceptional` bound** — no constant moves.
That is forced: the Goursat/edge/tail estimates of the landed argument are *zero-count
independent* (they bound `‖−L'/L‖` on the box edges by the Borel–Carathéodory/Jensen constant
`B = 120·L₄ + L₄/log(7/6)/w`, which already accounts for **all** zeros of the ball through the
partial-fraction count). Only the residue extraction iterates: `kernel_residue` is applied once
per enumerated zero and the results are summed (`rectBI_finsetSum` below).

The honest hypothesis shape. The contour identity produced by the argument is an **equality**:
`rectBI = 0` for the de-singularized integrand, so the boundary integral of the true integrand
equals `−2πi·∑_{ρ ∈ box} Res_ρ`. Hence `Z` must be **all** of the box's zeros — a `Z ⊆ zeros`
would leave uncancelled poles inside the contour and break Goursat. The hypotheses therefore are

* `hZall` — every zero of `L(·,χ)` in the *widened* region `σ₀ − w ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T + 2`
  lies in `Z` (the exact generalization of the landed `hzf`, which concluded `ρ = β₁`);
* `hZsep` — every `ρ ∈ Z` is `w`-separated from the left and horizontal edges
  (`σ₀ + w ≤ Re ρ`, `|Im ρ| + w ≤ T`); this is the generalization of the landed `hβsep`, and
  together with `hZall` it is the well-spacing statement the `∃T'`/`∃σ₀'` dodge discharges;
* `hZsimple` — every `ρ ∈ Z` is a **simple** zero (`analyticOrderAt L ρ = 1`), the generalization
  of the landed `hβ_simple`. (A multiplicity-carrying version would replace `1/(s−ρ)` by
  `m_ρ/(s−ρ)` throughout and scale each residue by `m_ρ`; nothing else changes. Left for the
  campaign to price when it needs it — see the flags entry.)

Finiteness of the zero set is *supplied*, not assumed: wave 1's `LFunction_halfbox_zero_count`
bounds the count in each unit window, and §3 below turns "the zeros in a compact box" into an
honest `Finset` (`boxZeros`).

## The residue mechanism, in one paragraph

Work with the de-singularized integrand `A(s) = ker(s)·G̃(s)`, `ker(s) = x^{s+1}/(s(s+1))`,
where `G̃ = −L'/L + ∑_{ρ ∈ Z} 1/(s−ρ)` off `Z` and, at each `ρ₀ ∈ Z`, takes the value
`−h'_{ρ₀}/h_{ρ₀}(ρ₀) + ∑_{ρ ∈ Z \ {ρ₀}} 1/(ρ₀−ρ)` from the local factorization
`L = (·−ρ₀)·h_{ρ₀}`. Each simple zero contributes exactly one removable singularity, so `A` is
differentiable on the whole box and Goursat gives `rectBI A = 0`; the true integrand is
`F = A − ∑_{ρ ∈ Z} ker/(·−ρ)` off `Z`, and `rectBI` of each subtracted term is `2πi·ker(ρ)` by
`kernel_residue`. The edge estimates are copied verbatim from the landed argument; the only
edge-level change is that the "points of the contour are not zeros" bookkeeping is now
`γ(t) ∉ Z` instead of `γ(t) ≠ β₁`.
-/

open Complex DirichletCharacter ArithmeticFunction Filter Set Metric MeromorphicOn Function
  MeasureTheory
open scoped LSeries.notation Topology

namespace Salt.SW

/-! ## 1. `rectBI` over a finite sum of integrands

The one genuinely new piece of contour plumbing: the rectangle boundary integral is additive
over a `Finset`-indexed family of edge-integrable integrands. This is what turns "one
`kernel_residue` application" into "one per enumerated zero, summed". -/

/-- **`rectBI` is `Finset`-additive.** If each member of a finite family is interval-integrable
on all four edges, the boundary integral of the sum is the sum of the boundary integrals. -/
lemma rectBI_finsetSum {ι : Type*} {z w : ℂ} (Z : Finset ι) (F : ι → ℂ → ℂ)
    (hbot : ∀ i ∈ Z, IntervalIntegrable (fun t : ℝ => F i (↑t + ↑z.im * I)) volume z.re w.re)
    (htop : ∀ i ∈ Z, IntervalIntegrable (fun t : ℝ => F i (↑t + ↑w.im * I)) volume z.re w.re)
    (hrgt : ∀ i ∈ Z, IntervalIntegrable (fun t : ℝ => F i (↑w.re + ↑t * I)) volume z.im w.im)
    (hlft : ∀ i ∈ Z, IntervalIntegrable (fun t : ℝ => F i (↑z.re + ↑t * I)) volume z.im w.im) :
    rectBI z w (fun s => ∑ i ∈ Z, F i s) = ∑ i ∈ Z, rectBI z w (F i) := by
  simp only [rectBI]
  rw [intervalIntegral.integral_finsetSum hbot, intervalIntegral.integral_finsetSum htop,
    intervalIntegral.integral_finsetSum hrgt, intervalIntegral.integral_finsetSum hlft,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]

/-! ## 2. A1 — THE ENUMERATED CONTOUR SHIFT -/

/-- **The contour-shift error budget `E(x)`** — literally the landed `psi1_contour_shift` /
`psi1_contour_shift_exceptional` right-hand side, named so the enumerated shift and the sharp
explicit formula can be stated without re-typing it. `B = 120·L₄ + L₄/log(7/6)/w` is the
Borel–Carathéodory/Jensen edge bound on `‖−L'/L‖`, `L₄ = log(4·M₀(T))`, and the three summands
are the horizontal edges (`≍ B·x^{c+1}/T²`), the left edge (`≍ B·x^{σ₀+1}·π/σ₀`) and the
truncation tail (`≍ x^{c+1}·log x/T`), all at `c = 1 + 1/log x`. -/
noncomputable def efShiftError (f : ℕ) (T σ₀ w x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (2 * ((1 + 1 / Real.log x) - σ₀)
        * (120 * Real.log (4 * (5 * (4 + T) * Real.sqrt f * (1 + Real.log f)))
           + Real.log (4 * (5 * (4 + T) * Real.sqrt f * (1 + Real.log f))) / Real.log (7 / 6) / w)
        * x ^ ((1 + 1 / Real.log x) + 1) / T ^ 2
      + (120 * Real.log (4 * (5 * (4 + T) * Real.sqrt f * (1 + Real.log f)))
           + Real.log (4 * (5 * (4 + T) * Real.sqrt f * (1 + Real.log f))) / Real.log (7 / 6) / w)
        * x ^ (σ₀ + 1) * (Real.pi / σ₀)
      + (Real.log x + 1) * x ^ ((1 + 1 / Real.log x) + 1) * (2 / T))

set_option maxHeartbeats 1600000 in
-- The enumerated assembly runs the S5c contour-shift argument on the de-singularized integrand
-- `A = ker·G̃` (Goursat-clean on the box after *all* the enumerated removable singularities are
-- filled) and re-attaches one `kernel_residue` per enumerated zero; the copied edge/tail
-- estimates plus the `E`-arithmetic need the same headroom the single-zero variant needed.
/-- **A1 — the contour-shift bound at an enumerated zero set** (the capstone's last unmet
hypothesis, `Salt/SW/EFSharp.lean` `psi_explicit_sharp_of_riesz_residues`).

Same box and hypotheses as the landed clean/exceptional shifts, but the box is allowed to
contain a **finite enumerated set `Z` of simple zeros** of `L(·,χ)`:

* `hZall` — `Z` contains *every* zero in the widened box region (the generalization of the
  landed `hzf`; the contour identity is an equality, so nothing may be left out);
* `hZsep` — every `ρ ∈ Z` is `w`-separated from the left and horizontal edges;
* `hZsimple` — every `ρ ∈ Z` is simple.

The shift then picks up **one residue per enumerated zero**, i.e. exactly wave 1's
`efRieszSum Z x = ∑_{ρ ∈ Z} x^{ρ+1}/(ρ(ρ+1))`:

    ‖ψ₁(x,χ) + efRieszSum Z x‖ ≤ E,

with `E` **identical** to the landed `psi1_contour_shift_exceptional` bound (the Goursat, edge
and tail estimates are zero-count independent — the Borel–Carathéodory/Jensen edge constant
`B` already prices all the zeros of the ball). -/
theorem psi1_contour_shift_finset {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {x : ℝ} (hx : 3 ≤ x) {T σ₀ w : ℝ} {Z : Finset ℂ}
    (hT : 2 ≤ T) (hw : 0 < w) (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1)
    (hZsep : ∀ ρ ∈ Z, σ₀ + w ≤ ρ.re ∧ |ρ.im| + w ≤ T)
    (hZsimple : ∀ ρ ∈ Z, analyticOrderAt (LFunction χ) ρ = 1)
    (hZall : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 → ρ ∈ Z) :
    ‖psi1Chi x χ + efRieszSum Z x‖ ≤ efShiftError f T σ₀ w x := by
  classical
  rw [efShiftError]
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
  have hlogx1 : (1 : ℝ) < Real.log x := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log x := Real.log_lt_log (Real.exp_pos 1)
          (lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hx)
  have hlogxpos : (0 : ℝ) < Real.log x := by linarith
  set c : ℝ := 1 + 1 / Real.log x with hcdef
  have hc1 : 1 < c := by
    have h : (0 : ℝ) < 1 / Real.log x := by positivity
    rw [hcdef]; linarith
  have hc2 : c < 2 := by
    have h : 1 / Real.log x < 1 := by rw [div_lt_one hlogxpos]; linarith
    rw [hcdef]; linarith
  have hcpos : (0 : ℝ) < c := by linarith
  have hc_sub : c - 1 = 1 / Real.log x := by rw [hcdef]; ring
  have hσ₀gt : (9 : ℝ) / 10 < σ₀ := by linarith
  have hσ₀pos : (0 : ℝ) < σ₀ := by linarith
  have hσ₀c : σ₀ < c := lt_trans hσ₀1 hc1
  set L4 : ℝ := Real.log (4 * (5 * (4 + T) * Real.sqrt f * (1 + Real.log f))) with hL4
  set B : ℝ := 120 * L4 + L4 / Real.log (7 / 6) / w with hBdef
  have hlogf : (0 : ℝ) ≤ Real.log f := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ f))
  have hsqrtf1 : (1 : ℝ) ≤ Real.sqrt f := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ f))
  have hM₀T1 : (1 : ℝ) ≤ 5 * (4 + T) * Real.sqrt f * (1 + Real.log f) := by
    have hp1 : (30 : ℝ) ≤ 5 * (4 + T) := by linarith
    have hp2 : (30 : ℝ) ≤ 5 * (4 + T) * Real.sqrt f := by
      calc (30 : ℝ) = 30 * 1 := by ring
        _ ≤ 5 * (4 + T) * Real.sqrt f := mul_le_mul hp1 hsqrtf1 (by norm_num) (by linarith)
    calc (1 : ℝ) ≤ 30 * 1 := by norm_num
      _ ≤ 5 * (4 + T) * Real.sqrt f * (1 + Real.log f) :=
          mul_le_mul hp2 (by linarith) (by norm_num) (by linarith)
  have hL4nn : (0 : ℝ) ≤ L4 := by rw [hL4]; exact Real.log_nonneg (by nlinarith [hM₀T1])
  have h76 : (0 : ℝ) < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hBnn : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  have hwT : w ≤ T := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  -- analyticity infrastructure
  have hana_univ : AnalyticOnNhd ℂ (LFunction χ) univ :=
    (differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ
  have hdL_diff : Differentiable ℂ (deriv (LFunction χ)) :=
    differentiableOn_univ.mp hana_univ.deriv.differentiableOn
  have hlogD_diff : ∀ s : ℂ, LFunction χ s ≠ 0 →
      DifferentiableAt ℂ (fun z => -logDeriv (LFunction χ) z) s := by
    intro s hs
    have hrw : (fun z => -logDeriv (LFunction χ) z)
        = fun z => -(deriv (LFunction χ) z / LFunction χ z) := by
      funext z; rw [logDeriv_apply]
    rw [hrw]
    exact (((hdL_diff s).div ((differentiable_LFunction hχ1) s) hs)).neg
  have hkerAt : ∀ s : ℂ, s ≠ 0 → s + 1 ≠ 0 →
      DifferentiableAt ℂ (fun z => (x : ℂ) ^ (z + 1) / (z * (z + 1))) s := by
    intro s hs0 hs1
    apply DifferentiableAt.div
    · exact (differentiableAt_id.add_const 1).const_cpow (Or.inl hxC)
    · exact differentiableAt_id.mul (differentiableAt_id.add_const 1)
    · exact mul_ne_zero hs0 hs1
  -- every member of `Z` is a zero, strictly inside the strip
  have hZzero : ∀ ρ ∈ Z, LFunction χ ρ = 0 := by
    intro ρ hρ
    by_contra h0
    have hord := hZsimple ρ hρ
    rw [(hana_univ ρ (mem_univ _)).analyticOrderAt_eq_zero.mpr h0] at hord
    exact absurd hord (by simp)
  have hZre1 : ∀ ρ ∈ Z, ρ.re < 1 := by
    intro ρ hρ
    by_contra hcon
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp hcon) (hZzero ρ hρ)
  -- the contour avoids `Z`
  have hZ_off_edge : ∀ a b : ℝ, (a ≤ σ₀ ∨ 1 ≤ a ∨ T ≤ |b|) → ((a : ℂ) + (b : ℂ) * I) ∉ Z := by
    intro a b hab hmem
    have hre : ((a : ℂ) + (b : ℂ) * I).re = a := by simp
    have him : ((a : ℂ) + (b : ℂ) * I).im = b := by simp
    obtain ⟨h1, h2⟩ := hZsep _ hmem
    rw [hre] at h1
    rw [him] at h2
    have h3 := hZre1 _ hmem
    rw [hre] at h3
    rcases hab with h | h | h
    · linarith
    · linarith
    · have := abs_nonneg b; linarith
  -- box non-vanishing away from `Z`
  have hLne_box : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ c → |s.im| ≤ T → s ∉ Z → LFunction χ s ≠ 0 := by
    intro s hsl hsu hsi hsZ hs0
    by_cases h1 : 1 ≤ s.re
    · exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) h1 hs0
    · exact hsZ (hZall s hs0 (by linarith) (not_le.mp h1).le (by linarith))
  -- the local factorizations at the enumerated simple zeros
  have hex : ∀ ρ : ℂ, ∃ gg : ℂ → ℂ, ρ ∈ Z →
      AnalyticAt ℂ gg ρ ∧ gg ρ ≠ 0 ∧ LFunction χ =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ 1 • gg z := by
    intro ρ
    by_cases hρ : ρ ∈ Z
    · obtain ⟨gg, h1, h2, h3⟩ :=
        ((hana_univ ρ (mem_univ _)).analyticOrderAt_eq_natCast (n := 1)).mp
          (by exact_mod_cast hZsimple ρ hρ)
      exact ⟨gg, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hρ⟩
  choose g hg using hex
  -- the de-singularized log-derivative
  obtain ⟨Gtrue, hGtrue⟩ : ∃ Gt : ℂ → ℂ, ∀ s : ℂ, Gt s =
      if s ∈ Z then -logDeriv (g s) s + ∑ ρ ∈ Z.erase s, 1 / (s - ρ)
      else -logDeriv (LFunction χ) s + ∑ ρ ∈ Z, 1 / (s - ρ) := ⟨_, fun _ => rfl⟩
  have hZclosed : IsOpen ((↑Z : Set ℂ)ᶜ) := Z.finite_toSet.isClosed.isOpen_compl
  -- differentiability of `Gtrue` at an enumerated zero (the removable singularity)
  have hGtrue_Z : ∀ ρ₀ ∈ Z, DifferentiableAt ℂ Gtrue ρ₀ := by
    intro ρ₀ hρ₀
    obtain ⟨hg_ana, hg_ne, hg_eq⟩ := hg ρ₀ hρ₀
    have hH_diff : DifferentiableAt ℂ
        (fun z => -logDeriv (g ρ₀) z + ∑ ρ ∈ Z.erase ρ₀, 1 / (z - ρ)) ρ₀ := by
      refine DifferentiableAt.add ?_ ?_
      · simp only [logDeriv_apply]
        exact ((hg_ana.deriv.differentiableAt).div hg_ana.differentiableAt hg_ne).neg
      · refine DifferentiableAt.fun_sum ?_
        intro ρ hρ
        have hne : ρ₀ - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hρ))
        exact (differentiableAt_const 1).div (differentiableAt_id.sub_const _) hne
    have hev : Gtrue =ᶠ[𝓝 ρ₀]
        (fun z => -logDeriv (g ρ₀) z + ∑ ρ ∈ Z.erase ρ₀, 1 / (z - ρ)) := by
      obtain ⟨U, hU_eq, hU_open, hρU⟩ := _root_.eventually_nhds_iff.mp hg_eq
      have hg_ne_nhds : ∀ᶠ z in 𝓝 ρ₀, g ρ₀ z ≠ 0 := hg_ana.continuousAt.eventually_ne hg_ne
      obtain ⟨V, hV_ne, hV_open, hρV⟩ := _root_.eventually_nhds_iff.mp hg_ne_nhds
      obtain ⟨W, hW_ana, hW_open, hρW⟩ :=
        _root_.eventually_nhds_iff.mp hg_ana.eventually_analyticAt
      have hEopen : IsOpen ((↑(Z.erase ρ₀) : Set ℂ)ᶜ) :=
        (Z.erase ρ₀).finite_toSet.isClosed.isOpen_compl
      have hρE : ρ₀ ∈ ((↑(Z.erase ρ₀) : Set ℂ)ᶜ) := by simp
      refine _root_.eventually_nhds_iff.mpr
        ⟨U ∩ V ∩ W ∩ (↑(Z.erase ρ₀) : Set ℂ)ᶜ, ?_,
          ((hU_open.inter hV_open).inter hW_open).inter hEopen, ⟨⟨⟨hρU, hρV⟩, hρW⟩, hρE⟩⟩
      intro z hz
      by_cases hzρ : z = ρ₀
      · subst hzρ; rw [hGtrue z, if_pos hρ₀]
      · have hzZ : z ∉ Z := by
          intro hmem
          exact hz.2 (by simpa using ⟨hmem, hzρ⟩)
        rw [hGtrue z, if_neg hzZ]
        have hz_ne : g ρ₀ z ≠ 0 := hV_ne z hz.1.1.2
        have hz_diff : DifferentiableAt ℂ (g ρ₀) z := (hW_ana z hz.1.2).differentiableAt
        have hzρ' : z - ρ₀ ≠ 0 := sub_ne_zero.mpr hzρ
        have hlocal : LFunction χ =ᶠ[𝓝 z] (fun u => (u - ρ₀) * g ρ₀ u) := by
          filter_upwards [(((hU_open.inter hV_open).inter hW_open).inter hEopen).mem_nhds hz]
            with u hu
          have heq := hU_eq u hu.1.1.1
          simp only [pow_one, smul_eq_mul] at heq
          exact heq
        have hlogL : logDeriv (LFunction χ) z = logDeriv (fun u => (u - ρ₀) * g ρ₀ u) z := by
          rw [logDeriv_apply, logDeriv_apply, hlocal.deriv_eq, hlocal.eq_of_nhds]
        have hd1 : DifferentiableAt ℂ (fun u : ℂ => u - ρ₀) z := differentiableAt_id.sub_const _
        have hmul : logDeriv (fun u => (u - ρ₀) * g ρ₀ u) z
            = logDeriv (fun u : ℂ => u - ρ₀) z + logDeriv (g ρ₀) z :=
          logDeriv_mul z hzρ' hz_ne hd1 hz_diff
        have hlin : logDeriv (fun u : ℂ => u - ρ₀) z = 1 / (z - ρ₀) := by
          rw [logDeriv_apply, deriv_sub_const]; simp
        have hsplit : ∑ ρ ∈ Z, 1 / (z - ρ) = 1 / (z - ρ₀) + ∑ ρ ∈ Z.erase ρ₀, 1 / (z - ρ) :=
          (Finset.add_sum_erase _ _ hρ₀).symm
        rw [hsplit, hlogL, hmul, hlin]
        ring
    exact hH_diff.congr_of_eventuallyEq hev
  -- differentiability of `Gtrue` on the whole box
  have hGtrue_diff : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ c → |s.im| ≤ T →
      DifferentiableAt ℂ Gtrue s := by
    intro s hsl hsu hsi
    by_cases hsZ : s ∈ Z
    · exact hGtrue_Z s hsZ
    · have hGeq : Gtrue =ᶠ[𝓝 s]
          (fun z => -logDeriv (LFunction χ) z + ∑ ρ ∈ Z, 1 / (z - ρ)) := by
        filter_upwards [hZclosed.mem_nhds (by simpa using hsZ)] with z hz
        rw [hGtrue z, if_neg (by simpa using hz)]
      have hLs : LFunction χ s ≠ 0 := hLne_box s hsl hsu hsi hsZ
      have hGd : DifferentiableAt ℂ
          (fun z => -logDeriv (LFunction χ) z + ∑ ρ ∈ Z, 1 / (z - ρ)) s := by
        refine (hlogD_diff s hLs).add ?_
        refine DifferentiableAt.fun_sum ?_
        intro ρ hρ
        have hne : s ≠ ρ := by rintro rfl; exact hsZ hρ
        exact (differentiableAt_const 1).div (differentiableAt_id.sub_const _)
          (sub_ne_zero.mpr hne)
      exact hGd.congr_of_eventuallyEq hGeq
  -- the integrands
  set F : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) * (-logDeriv (LFunction χ) s) with hF
  set A : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) * Gtrue s with hA
  set Bfun : ℂ → ℂ := fun s => ∑ ρ ∈ Z, (x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - ρ) with hBfun
  set κ : ℂ := efRieszSum Z x with hκ
  have hFnorm : ∀ s : ℂ, ‖F s‖
      = x ^ (s.re + 1) * ‖(s * (s + 1))⁻¹‖ * ‖logDeriv (LFunction χ) s‖ := by
    intro s
    simp only [hF]
    rw [norm_mul, norm_neg, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.add_re,
      Complex.one_re, div_eq_mul_inv, ← norm_inv]
  have hkermul : ∀ s : ℂ, (x : ℂ) ^ (s + 1) / (s * (s + 1)) * (∑ ρ ∈ Z, 1 / (s - ρ))
      = ∑ ρ ∈ Z, (x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - ρ) := by
    intro s
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ρ _ => mul_one_div _ _)
  -- pointwise splitting `F = A − Bfun` off `Z`
  have hAFB : ∀ s : ℂ, s ∉ Z → F s = A s - Bfun s := by
    intro s hsZ
    have hGt : Gtrue s = -logDeriv (LFunction χ) s + ∑ ρ ∈ Z, 1 / (s - ρ) := by
      rw [hGtrue s, if_neg hsZ]
    have h2 : (x : ℂ) ^ (s + 1) / (s * (s + 1)) * (-logDeriv (LFunction χ) s + ∑ ρ ∈ Z, 1 / (s - ρ))
        = (x : ℂ) ^ (s + 1) / (s * (s + 1)) * (-logDeriv (LFunction χ) s)
          + ∑ ρ ∈ Z, (x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - ρ) := by
      rw [← hkermul s]; ring
    simp only [hF, hA, hBfun, hGt]
    rw [h2]
    ring
  -- the rectangle
  set zc : ℂ := (σ₀ : ℂ) - (T : ℂ) * I with hzc
  set wc : ℂ := (c : ℂ) + (T : ℂ) * I with hwc
  have hzc_re : zc.re = σ₀ := by rw [hzc]; simp
  have hzc_im : zc.im = -T := by rw [hzc]; simp
  have hwc_re : wc.re = c := by rw [hwc]; simp
  have hwc_im : wc.im = T := by rw [hwc]; simp
  -- `A` is differentiable on the whole box
  have hA_diff : DifferentiableOn ℂ A (closedRect zc wc) := by
    intro s hs
    rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, mem_reProdIm] at hs
    rw [Set.uIcc_of_le hσ₀c.le] at hs
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at hs
    obtain ⟨hsre, hsim⟩ := hs
    simp only [Set.mem_Icc] at hsre hsim
    have hsim' : |s.im| ≤ T := by rw [abs_le]; exact ⟨hsim.1, hsim.2⟩
    have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hsre; linarith [hsre.1, hσ₀pos]
    have hs1 : s + 1 ≠ 0 := by
      intro h; have : (s + 1).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.one_re] at this; linarith [hsre.1, hσ₀pos]
    have hAs : DifferentiableAt ℂ A s := by
      rw [hA]; exact (hkerAt s hs0 hs1).mul (hGtrue_diff s hsre.1 hsre.2 hsim')
    exact hAs.differentiableWithinAt
  have hA0 : rectBI zc wc A = 0 := rectBI_eq_zero_of_differentiableOn hA_diff
  -- edge integrability, for `A`, for `Bfun`, and for each enumerated residue kernel
  have hedge_int : ∀ (γ : ℝ → ℂ) (a b : ℝ), Continuous γ →
      Set.MapsTo γ (Set.uIcc a b) (closedRect zc wc) →
      (∀ t ∈ Set.uIcc a b, γ t ∉ Z) →
      IntervalIntegrable (fun t => A (γ t)) volume a b ∧
        IntervalIntegrable (fun t => Bfun (γ t)) volume a b ∧
        ∀ ρ ∈ Z, IntervalIntegrable
          (fun t => (x : ℂ) ^ (γ t + 1) / (γ t * (γ t + 1)) / (γ t - ρ)) volume a b := by
    intro γ a b hγ hmaps hne
    have hden : ∀ t ∈ Set.uIcc a b, γ t ≠ 0 ∧ γ t + 1 ≠ 0 := by
      intro t ht
      have hmem := hmaps ht
      rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, mem_reProdIm, Set.uIcc_of_le hσ₀c.le,
          Set.uIcc_of_le (by linarith : -T ≤ T)] at hmem
      obtain ⟨hre, -⟩ := hmem
      simp only [Set.mem_Icc] at hre
      refine ⟨?_, ?_⟩
      · intro h; rw [h, Complex.zero_re] at hre; linarith [hre.1, hσ₀pos]
      · intro h; have h2 : (γ t + 1).re = 0 := by rw [h]; simp
        rw [Complex.add_re, Complex.one_re] at h2; linarith [hre.1, hσ₀pos]
    have hZne : ∀ ρ ∈ Z, ∀ t ∈ Set.uIcc a b, γ t - ρ ≠ 0 := by
      intro ρ hρ t ht
      refine sub_ne_zero.mpr ?_
      intro h
      exact hne t ht (by rw [h]; exact hρ)
    refine ⟨(hA_diff.continuousOn.comp hγ.continuousOn hmaps).intervalIntegrable, ?_, ?_⟩
    · apply ContinuousOn.intervalIntegrable
      intro t ht
      have hd : DifferentiableAt ℂ Bfun (γ t) := by
        rw [hBfun]
        refine DifferentiableAt.fun_sum ?_
        intro ρ hρ
        exact (hkerAt (γ t) (hden t ht).1 (hden t ht).2).div (differentiableAt_id.sub_const _)
          (hZne ρ hρ t ht)
      exact ((hd.continuousAt).comp hγ.continuousAt).continuousWithinAt
    · intro ρ hρ
      apply ContinuousOn.intervalIntegrable
      intro t ht
      have hd : DifferentiableAt ℂ
          (fun s : ℂ => (x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - ρ)) (γ t) :=
        (hkerAt (γ t) (hden t ht).1 (hden t ht).2).div (differentiableAt_id.sub_const _)
          (hZne ρ hρ t ht)
      exact ((hd.continuousAt).comp hγ.continuousAt).continuousWithinAt
  -- the four MapsTo (edges into the box)
  have hmaps_bot : Set.MapsTo (fun t : ℝ => (↑t + ↑zc.im * I : ℂ)) (Set.uIcc zc.re wc.re)
      (closedRect zc wc) := by
    intro u hu
    rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [show (↑u + ↑zc.im * I : ℂ).re = u by simp]; exact hu
    · rw [show (↑u + ↑zc.im * I : ℂ).im = zc.im by simp]; exact left_mem_uIcc
  have hmaps_top : Set.MapsTo (fun t : ℝ => (↑t + ↑wc.im * I : ℂ)) (Set.uIcc zc.re wc.re)
      (closedRect zc wc) := by
    intro u hu
    rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [show (↑u + ↑wc.im * I : ℂ).re = u by simp]; exact hu
    · rw [show (↑u + ↑wc.im * I : ℂ).im = wc.im by simp]; exact right_mem_uIcc
  have hmaps_rgt : Set.MapsTo (fun t : ℝ => (↑wc.re + ↑t * I : ℂ)) (Set.uIcc zc.im wc.im)
      (closedRect zc wc) := by
    intro v hv
    rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [show (↑wc.re + ↑v * I : ℂ).re = wc.re by simp]; exact right_mem_uIcc
    · rw [show (↑wc.re + ↑v * I : ℂ).im = v by simp]; exact hv
  have hmaps_lft : Set.MapsTo (fun t : ℝ => (↑zc.re + ↑t * I : ℂ)) (Set.uIcc zc.im wc.im)
      (closedRect zc wc) := by
    intro v hv
    rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [show (↑zc.re + ↑v * I : ℂ).re = zc.re by simp]; exact left_mem_uIcc
    · rw [show (↑zc.re + ↑v * I : ℂ).im = v by simp]; exact hv
  have hne_bot : ∀ t ∈ Set.uIcc zc.re wc.re, (↑t + ↑zc.im * I : ℂ) ∉ Z :=
    fun t _ => hZ_off_edge t zc.im (Or.inr (Or.inr (by rw [hzc_im, abs_neg, abs_of_pos hTpos])))
  have hne_top : ∀ t ∈ Set.uIcc zc.re wc.re, (↑t + ↑wc.im * I : ℂ) ∉ Z :=
    fun t _ => hZ_off_edge t wc.im (Or.inr (Or.inr (by rw [hwc_im, abs_of_pos hTpos])))
  have hne_rgt : ∀ t ∈ Set.uIcc zc.im wc.im, (↑wc.re + ↑t * I : ℂ) ∉ Z :=
    fun t _ => hZ_off_edge wc.re t (Or.inr (Or.inl (by rw [hwc_re]; linarith)))
  have hne_lft : ∀ t ∈ Set.uIcc zc.im wc.im, (↑zc.re + ↑t * I : ℂ) ∉ Z :=
    fun t _ => hZ_off_edge zc.re t (Or.inl (by rw [hzc_re]))
  obtain ⟨hA_bot, hB_bot, hK_bot⟩ :=
    hedge_int _ zc.re wc.re (by fun_prop) hmaps_bot hne_bot
  obtain ⟨hA_top, hB_top, hK_top⟩ :=
    hedge_int _ zc.re wc.re (by fun_prop) hmaps_top hne_top
  obtain ⟨hA_rgt, hB_rgt, hK_rgt⟩ :=
    hedge_int _ zc.im wc.im (by fun_prop) hmaps_rgt hne_rgt
  obtain ⟨hA_lft, hB_lft, hK_lft⟩ :=
    hedge_int _ zc.im wc.im (by fun_prop) hmaps_lft hne_lft
  -- THE RESIDUE EXTRACTION: one `kernel_residue` per enumerated zero, summed
  have hBsplit : rectBI zc wc Bfun
      = ∑ ρ ∈ Z, rectBI zc wc (fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - ρ)) := by
    rw [hBfun]
    exact rectBI_finsetSum Z (fun ρ s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - ρ))
      hK_bot hK_top hK_rgt hK_lft
  have hBres : rectBI zc wc Bfun = 2 * ↑Real.pi * I * κ := by
    rw [hBsplit, hκ, efRieszSum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    have him : |ρ.im| < T := by linarith [(hZsep ρ hρ).2]
    have him' := abs_lt.mp him
    exact kernel_residue hxpos (β := ρ) (by rw [hzc_re]; exact hσ₀pos)
      (by rw [hzc_re, hwc_re]; exact hσ₀c) (by rw [hzc_im, hwc_im]; linarith)
      ⟨by rw [hzc_re]; linarith [(hZsep ρ hρ).1],
        by rw [hwc_re]; linarith [hZre1 ρ hρ]⟩
      ⟨by rw [hzc_im]; linarith [him'.1], by rw [hwc_im]; linarith [him'.2]⟩
  have hlin : rectBI zc wc F = rectBI zc wc A - rectBI zc wc Bfun :=
    rectBI_sub_of_edge_eq hA_bot hA_top hA_rgt hA_lft hB_bot hB_top hB_rgt hB_lft
      (fun t ht => hAFB _ (hne_bot t ht)) (fun t ht => hAFB _ (hne_top t ht))
      (fun t ht => hAFB _ (hne_rgt t ht)) (fun t ht => hAFB _ (hne_lft t ht))
  have hrectF : rectBI zc wc F = -(2 * ↑Real.pi * I) * κ := by
    rw [hlin, hA0, hBres]; ring
  rw [rectBI, hzc_re, hzc_im, hwc_re, hwc_im] at hrectF
  set RIGHT : ℂ := ∫ v in (-T)..T, F ((c : ℂ) + v * I) with hRIGHT
  set TOPI : ℂ := ∫ u in σ₀..c, F ((u : ℂ) + (T : ℂ) * I) with hTOPI
  set BOTI : ℂ := ∫ u in σ₀..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I) with hBOTI
  set LEFT : ℂ := ∫ v in (-T)..T, F ((σ₀ : ℂ) + v * I) with hLEFT
  have hgour2 : I * (RIGHT + (2 * ↑Real.pi : ℂ) * κ) = TOPI - BOTI + I * LEFT := by
    linear_combination hrectF
  have hRnorm : ‖RIGHT + (2 * ↑Real.pi : ℂ) * κ‖ ≤ ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖ := by
    have heq : ‖RIGHT + (2 * ↑Real.pi : ℂ) * κ‖ = ‖TOPI - BOTI + I * LEFT‖ := by
      rw [← hgour2, norm_mul, Complex.norm_I, one_mul]
    rw [heq]
    calc ‖TOPI - BOTI + I * LEFT‖
        ≤ ‖TOPI - BOTI‖ + ‖I * LEFT‖ := norm_add_le _ _
      _ ≤ ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]; linarith [norm_sub_le TOPI BOTI]
  -- the c-line integrability and the Perron bridge
  have hFint : Integrable (fun v : ℝ => F ((c : ℂ) + v * I)) := by
    simp only [hF]; exact contour_integrand_integrable χ hχ1 hx1 hc1 hc2.le
  have hbridge : psi1Chi x χ = (1 / (2 * Real.pi)) • ∫ v : ℝ, F ((c : ℂ) + v * I) := by
    rw [psi1_eq_contour_integral χ hx1 hc1]
  have htrunc : (∫ v : ℝ, F ((c : ℂ) + v * I))
      = RIGHT + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I) := by
    rw [hRIGHT, intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T),
      integral_add_compl measurableSet_Ioc hFint]
  -- the distance argument on the edges (carving the enumerated zeros)
  have hdist_edge : ∀ (s : ℂ), (s.re = σ₀ ∨ |s.im| = T) → σ₀ ≤ s.re → |s.im| ≤ T →
      ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ ∈ Metric.ball (2 + (s.im : ℂ) * I) (3 / 2) →
        w ≤ ‖s - ρ‖ := by
    intro s hedge hsl hsi ρ hρ0 hρball
    have hρre1 : ρ.re < 1 := by
      by_contra hcon; exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp hcon) hρ0
    have hρim : |ρ.im| ≤ T + 2 := by
      have himdist : |ρ.im - s.im| ≤ 3 / 2 := by
        have h := Complex.abs_im_le_norm (ρ - (2 + (s.im : ℂ) * I))
        have hival : (ρ - (2 + (s.im : ℂ) * I)).im = ρ.im - s.im := by simp
        rw [hival] at h
        have hb : ‖ρ - (2 + (s.im : ℂ) * I)‖ < 3 / 2 := by rw [← dist_eq_norm]; exact hρball
        linarith
      have hh1 := abs_le.mp himdist
      have hh2 := abs_le.mp hsi
      rw [abs_le]; constructor <;> linarith
    by_cases hρZ : ρ ∈ Z
    · obtain ⟨hsep_re, hsep_im⟩ := hZsep ρ hρZ
      rcases hedge with hre | him
      · have h := Complex.abs_re_le_norm (s - ρ)
        rw [Complex.sub_re, hre] at h
        have hb : |σ₀ - ρ.re| = ρ.re - σ₀ := by rw [abs_of_nonpos (by linarith)]; ring
        rw [hb] at h; linarith
      · have h := Complex.abs_im_le_norm (s - ρ)
        rw [Complex.sub_im] at h
        have hb : |s.im| - |ρ.im| ≤ |s.im - ρ.im| := abs_sub_abs_le_abs_sub _ _
        rw [him] at hb
        linarith
    · have hρre2 : ρ.re ≤ σ₀ - w := by
        by_contra hcon
        exact hρZ (hZall ρ hρ0 (le_of_lt (not_le.mp hcon)) hρre1.le hρim)
      have hre := Complex.abs_re_le_norm (s - ρ)
      rw [Complex.sub_re] at hre
      calc w ≤ s.re - ρ.re := by linarith
        _ = |s.re - ρ.re| := (abs_of_nonneg (by linarith)).symm
        _ ≤ ‖s - ρ‖ := hre
  -- edge bound constant and the horizontal pointwise estimate
  set Cbnd : ℝ := x ^ (c + 1) * B / T ^ 2 with hCbnd
  have hxc1pos : (0 : ℝ) < x ^ (c + 1) := by positivity
  have hCbnd_nn : (0 : ℝ) ≤ Cbnd := by rw [hCbnd]; positivity
  have hhoriz : ∀ (τ : ℝ), |τ| = T → ∀ u ∈ Set.uIoc σ₀ c,
      ‖F ((u : ℂ) + (τ : ℂ) * I)‖ ≤ Cbnd := by
    intro τ hτ u hu
    rw [Set.uIoc_of_le hσ₀c.le, Set.mem_Ioc] at hu
    have hsre : ((u : ℂ) + (τ : ℂ) * I).re = u := by simp
    have hsim : ((u : ℂ) + (τ : ℂ) * I).im = τ := by simp
    have hupos : (0 : ℝ) < u := by linarith [hu.1, hσ₀gt]
    have hsZ : ((u : ℂ) + (τ : ℂ) * I) ∉ Z :=
      hZ_off_edge u τ (Or.inr (Or.inr (le_of_eq hτ.symm)))
    have hLs : LFunction χ ((u : ℂ) + (τ : ℂ) * I) ≠ 0 :=
      hLne_box _ (by rw [hsre]; linarith [hu.1]) (by rw [hsre]; linarith [hu.2])
        (by rw [hsim]; exact le_of_eq hτ) hsZ
    have hlogb : ‖logDeriv (LFunction χ) ((u : ℂ) + (τ : ℂ) * I)‖ ≤ B := by
      rw [hBdef, hL4]
      exact norm_logDeriv_le_of_ball_dist χ hχ hf hw hσ₀w
        (by rw [hsre]; linarith [hu.1]) (by rw [hsre]; linarith [hu.2])
        (by rw [hsim]; exact le_of_eq hτ) hLs
        (hdist_edge _ (Or.inr (by rw [hsim]; exact hτ)) (by rw [hsre]; linarith [hu.1])
          (by rw [hsim]; exact le_of_eq hτ))
    have hden : ‖(((u : ℂ) + (τ : ℂ) * I) * (((u : ℂ) + (τ : ℂ) * I) + 1))⁻¹‖
        ≤ (u ^ 2 + τ ^ 2)⁻¹ := norm_inv_denom_le hupos τ
    have hττ : τ ^ 2 = T ^ 2 := by rw [← sq_abs, hτ]
    have hxexp : x ^ (u + 1) ≤ x ^ (c + 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hu.2])
    have hinvle : (u ^ 2 + τ ^ 2)⁻¹ ≤ (T ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr (by nlinarith [sq_nonneg u])
    rw [hFnorm, hsre]
    calc x ^ (u + 1) * ‖(((u : ℂ) + (τ : ℂ) * I) * (((u : ℂ) + (τ : ℂ) * I) + 1))⁻¹‖
            * ‖logDeriv (LFunction χ) ((u : ℂ) + (τ : ℂ) * I)‖
        ≤ x ^ (u + 1) * (u ^ 2 + τ ^ 2)⁻¹ * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
            (norm_nonneg _) (by positivity)
      _ ≤ x ^ (c + 1) * (T ^ 2)⁻¹ * B :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hxexp hinvle (by positivity) (by positivity)) hBnn
      _ = Cbnd := by rw [hCbnd]; ring
  have hTOPb : ‖TOPI‖ ≤ (c - σ₀) * Cbnd := by
    rw [hTOPI]
    calc ‖∫ u in σ₀..c, F ((u : ℂ) + (T : ℂ) * I)‖
        ≤ Cbnd * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hhoriz T (abs_of_pos hTpos))
      _ = (c - σ₀) * Cbnd := by rw [abs_of_nonneg (by linarith)]; ring
  have hBOTb : ‖BOTI‖ ≤ (c - σ₀) * Cbnd := by
    rw [hBOTI]
    have hnegT : |(-T : ℝ)| = T := by rw [abs_neg, abs_of_pos hTpos]
    calc ‖∫ u in σ₀..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖
        ≤ Cbnd * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hhoriz (-T) hnegT)
      _ = (c - σ₀) * Cbnd := by rw [abs_of_nonneg (by linarith)]; ring
  have hLEFTb : ‖LEFT‖ ≤ B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
    rw [hLEFT]
    have hg_int : Integrable (fun v : ℝ => B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹) :=
      (integrable_inv_c_sq_add_sq hσ₀pos).const_mul _
    have hFleft_ii : IntervalIntegrable (fun v : ℝ => F ((σ₀ : ℂ) + v * I)) volume (-T) T := by
      simp only [hF]
      apply ContinuousOn.intervalIntegrable
      have hLcont : Continuous (LFunction χ) := (differentiable_LFunction hχ1).continuous
      have hdLcont : Continuous (deriv (LFunction χ)) := hdL_diff.continuous
      have hline : Continuous (fun v : ℝ => (σ₀ : ℂ) + v * I) := by fun_prop
      have hLne : ∀ v ∈ Set.uIcc (-T) T, LFunction χ ((σ₀ : ℂ) + v * I) ≠ 0 := by
        intro v hv
        rw [Set.uIcc_of_le (by linarith : -T ≤ T), Set.mem_Icc] at hv
        have hsre : ((σ₀ : ℂ) + v * I).re = σ₀ := by simp
        have hsim : ((σ₀ : ℂ) + v * I).im = v := by simp
        exact hLne_box _ hsre.ge (by rw [hsre]; linarith)
          (by rw [hsim, abs_le]; exact ⟨hv.1, hv.2⟩) (hZ_off_edge σ₀ v (Or.inl le_rfl))
      have hden : ∀ v ∈ Set.uIcc (-T) T,
          ((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1) ≠ 0 := by
        intro v _
        have hsre : ((σ₀ : ℂ) + v * I).re = σ₀ := by simp
        refine mul_ne_zero ?_ ?_
        · intro h; rw [h, Complex.zero_re] at hsre; linarith [hσ₀pos]
        · intro h; have : (((σ₀ : ℂ) + v * I) + 1).re = 0 := by rw [h]; simp
          rw [Complex.add_re, Complex.one_re, hsre] at this; linarith [hσ₀pos]
      apply ContinuousOn.mul
      · apply ContinuousOn.div
        · exact ((by fun_prop : Continuous fun v : ℝ => ((σ₀ : ℂ) + v * I) + 1).const_cpow
            (Or.inl hxC)).continuousOn
        · exact (by fun_prop :
            Continuous fun v : ℝ => ((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1)).continuousOn
        · exact hden
      · have hrw : (fun v : ℝ => -logDeriv (LFunction χ) ((σ₀ : ℂ) + v * I))
            = fun v : ℝ =>
              -(deriv (LFunction χ) ((σ₀ : ℂ) + v * I) / LFunction χ ((σ₀ : ℂ) + v * I)) := by
          funext v; rw [logDeriv_apply]
        rw [hrw]
        exact (((hdLcont.comp hline).continuousOn.div (hLcont.comp hline).continuousOn hLne)).neg
    have hgnn : ∀ v : ℝ, (0 : ℝ) ≤ B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
      fun v => mul_nonneg (mul_nonneg hBnn (by positivity)) (by positivity)
    have hpt : ∀ v ∈ Set.Icc (-T) T,
        ‖F ((σ₀ : ℂ) + v * I)‖ ≤ B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
      intro v hv
      simp only [Set.mem_Icc] at hv
      have hvT : |v| ≤ T := by rw [abs_le]; exact ⟨hv.1, hv.2⟩
      have hsre : ((σ₀ : ℂ) + v * I).re = σ₀ := by simp
      have hsim : ((σ₀ : ℂ) + v * I).im = v := by simp
      have hsZ : ((σ₀ : ℂ) + v * I) ∉ Z := hZ_off_edge σ₀ v (Or.inl le_rfl)
      have hLs : LFunction χ ((σ₀ : ℂ) + v * I) ≠ 0 :=
        hLne_box _ hsre.ge (by rw [hsre]; linarith) (by rw [hsim]; exact hvT) hsZ
      have hlogb : ‖logDeriv (LFunction χ) ((σ₀ : ℂ) + v * I)‖ ≤ B := by
        rw [hBdef, hL4]
        exact norm_logDeriv_le_of_ball_dist χ hχ hf hw hσ₀w hsre.ge (by rw [hsre]; linarith)
          (by rw [hsim]; exact hvT) hLs
          (hdist_edge _ (Or.inl hsre) hsre.ge (by rw [hsim]; exact hvT))
      have hden : ‖(((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1))⁻¹‖ ≤ (σ₀ ^ 2 + v ^ 2)⁻¹ :=
        norm_inv_denom_le hσ₀pos v
      rw [hFnorm, hsre]
      calc x ^ (σ₀ + 1) * ‖(((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1))⁻¹‖
              * ‖logDeriv (LFunction χ) ((σ₀ : ℂ) + v * I)‖
          ≤ x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ * B :=
            mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
              (norm_nonneg _) (by positivity)
        _ = B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by ring
    calc ‖∫ v in (-T)..T, F ((σ₀ : ℂ) + v * I)‖
        ≤ ∫ v in (-T)..T, ‖F ((σ₀ : ℂ) + v * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ v in (-T)..T, B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
          intervalIntegral.integral_mono_on (by linarith)
            hFleft_ii.norm hg_int.intervalIntegrable hpt
      _ ≤ ∫ v : ℝ, B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
          rw [intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T)]
          exact setIntegral_le_integral hg_int (Filter.Eventually.of_forall hgnn)
      _ = B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
          rw [integral_const_mul, integral_inv_sq_add hσ₀pos]
  have hcompl_meas : MeasurableSet (Set.Ioc (-T) T)ᶜ := measurableSet_Ioc.compl
  have hTAILb : ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖
      ≤ (Real.log x + 1) * x ^ (c + 1) * (2 / T) := by
    have hFint_on : IntegrableOn (fun v : ℝ => F ((c : ℂ) + v * I)) (Set.Ioc (-T) T)ᶜ :=
      hFint.integrableOn
    have hg_int : IntegrableOn
        (fun v : ℝ => (Real.log x + 1) * x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹) (Set.Ioc (-T) T)ᶜ :=
      ((integrable_inv_c_sq_add_sq hcpos).const_mul _).integrableOn
    calc ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖
        ≤ ∫ v in (Set.Ioc (-T) T)ᶜ, ‖F ((c : ℂ) + v * I)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v in (Set.Ioc (-T) T)ᶜ, (Real.log x + 1) * x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹ := by
          refine setIntegral_mono_on hFint_on.norm hg_int hcompl_meas ?_
          intro v _
          have hsre : ((c : ℂ) + v * I).re = c := by simp
          have hLs : LFunction χ ((c : ℂ) + v * I) ≠ 0 :=
            LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by rw [hsre]; linarith)
          have hlogb : ‖logDeriv (LFunction χ) ((c : ℂ) + v * I)‖ ≤ Real.log x + 1 := by
            have hle := norm_logDeriv_le_of_re χ (s := (c : ℂ) + v * I)
              (by rw [hsre]; exact hc1) (by rw [hsre]; linarith)
            rw [hsre, hc_sub, one_div_one_div] at hle
            exact hle
          have hden : ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖ ≤ (c ^ 2 + v ^ 2)⁻¹ :=
            norm_inv_denom_le hcpos v
          rw [hFnorm, hsre]
          calc x ^ (c + 1) * ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖
                  * ‖logDeriv (LFunction χ) ((c : ℂ) + v * I)‖
              ≤ x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹ * (Real.log x + 1) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
                  (norm_nonneg _) (by positivity)
            _ = (Real.log x + 1) * x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹ := by ring
      _ = (Real.log x + 1) * x ^ (c + 1) * ∫ v in (Set.Ioc (-T) T)ᶜ, (c ^ 2 + v ^ 2)⁻¹ := by
          rw [integral_const_mul]
      _ ≤ (Real.log x + 1) * x ^ (c + 1) * (2 / T) :=
          mul_le_mul_of_nonneg_left (tail_lorentzian_le hcpos hTpos)
            (by positivity)
  have hcombine : ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
      ≤ 2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
    have hstep : ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
        ≤ (c - σ₀) * Cbnd + (c - σ₀) * Cbnd + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
      linarith [hTOPb, hBOTb, hLEFTb]
    calc ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
        ≤ (c - σ₀) * Cbnd + (c - σ₀) * Cbnd + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := hstep
      _ = 2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
          rw [hCbnd]; ring
  -- final assembly (the enumerated residue sum absorbs the residues)
  have hπℂ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkappa : (1 / (2 * Real.pi) : ℝ) • ((2 * ↑Real.pi : ℂ) * κ) = κ := by
    rw [Complex.real_smul]; push_cast; field_simp
  have hcollect : psi1Chi x χ + κ
      = (1 / (2 * Real.pi)) • ((RIGHT + (2 * ↑Real.pi : ℂ) * κ)
          + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)) := by
    have e1 : (1 / (2 * Real.pi) : ℝ) • ((RIGHT + (2 * ↑Real.pi : ℂ) * κ)
          + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I))
        = (1 / (2 * Real.pi)) • (RIGHT + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I))
          + (1 / (2 * Real.pi)) • ((2 * ↑Real.pi : ℂ) * κ) := by
      simp only [Complex.real_smul]; ring
    rw [e1, hkappa, ← htrunc, ← hbridge]
  rw [hcollect, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖(RIGHT + (2 * ↑Real.pi : ℂ) * κ) + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖
      ≤ ‖RIGHT + (2 * ↑Real.pi : ℂ) * κ‖
          + ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖ := norm_add_le _ _
    _ ≤ (2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀))
          + (Real.log x + 1) * x ^ (c + 1) * (2 / T) := by
        have h1 : ‖RIGHT + (2 * ↑Real.pi : ℂ) * κ‖
            ≤ 2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) :=
          le_trans hRnorm hcombine
        linarith [h1, hTAILb]
    _ = 2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀)
          + (Real.log x + 1) * x ^ (c + 1) * (2 / T) := by ring

/-! ## 3. A2 — THE ZERO `Finset`

A1 consumes an honest `Finset` of zeros. This section builds it: the zeros of `L(·,χ)` in a
closed box of the critical strip are finite (they sit in the support of the analytic divisor on
a compact ball, which is finite), so `Set.Finite.toFinset` gives the enumeration, with an exact
membership spec.

**Disposition of the left half `Re ρ < 1/2`.** The `Finset` built here is the *whole* box's
zero set — there is no left/right asymmetry in the construction, and none is needed for A1
(which needs membership, not counting). The functional-equation reflection `ρ ↦ 1 − ρ̄` is
needed only to *bound the cardinality* on the left: wave 1's `LFunction_halfbox_zero_count`
runs the Jensen keystone in `closedBall (2+it₀) (37/20)`, whose reach is `Re ≥ 3/20`, so it
already covers the whole strip's unit window `0 ≤ Re ρ ≤ 1` **except** the sliver
`0 ≤ Re ρ < 3/20`; the growth input `LFunction_growth_sphere_wide` cannot be pushed further
left without the functional equation (mathlib `completedLFunction`), because `L` grows there.
So: the enumeration is unconditional; a *numeric* bound on `#boxZeros` is not landed here and
is the A3 batching job. -/

/-- **The zeros of `L(·,χ)` in a closed box are finite.** Route: they sit in the support of the
analytic divisor of `L(·,χ)` on a compact closed ball containing the box, which is finite
(`Function.locallyFinsuppWithin.finiteSupport`). The only global input is that `L(·,χ)` is not
identically zero — supplied by `L(2,χ) ≠ 0` through the identity theorem. -/
lemma boxZeroSet_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (a b T : ℝ) :
    {ρ : ℂ | LFunction χ ρ = 0 ∧ a ≤ ρ.re ∧ ρ.re ≤ b ∧ |ρ.im| ≤ T}.Finite := by
  have hana : AnalyticOnNhd ℂ (LFunction χ) univ :=
    (differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ
  set R : ℝ := |a| + |b| + |T| + 1 with hR
  set K : Set ℂ := Metric.closedBall (0 : ℂ) R with hK
  have hanaK : AnalyticOnNhd ℂ (LFunction χ) K := hana.mono (subset_univ _)
  have hfin : (Function.support (fun u => divisor (LFunction χ) K u)).Finite :=
    (divisor (LFunction χ) K).finiteSupport (by rw [hK]; exact isCompact_closedBall _ _)
  refine hfin.subset ?_
  intro ρ hρ
  obtain ⟨h0, hre1, hre2, him⟩ := hρ
  -- the box sits in the ball
  have hmem : ρ ∈ K := by
    rw [hK, Metric.mem_closedBall, dist_zero_right]
    have hre : |ρ.re| ≤ |a| + |b| := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le a, abs_nonneg b], by linarith [le_abs_self b, abs_nonneg a]⟩
    have hnorm := Complex.norm_le_abs_re_add_abs_im ρ
    have hTT : T ≤ |T| := le_abs_self T
    rw [hR]; linarith
  -- the order at a zero is neither `0` nor `⊤`
  have hordne0 : analyticOrderAt (LFunction χ) ρ ≠ 0 := fun hz =>
    ((hana ρ (mem_univ _)).analyticOrderAt_eq_zero.mp hz) h0
  have hordnetop : analyticOrderAt (LFunction χ) ρ ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have heq := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ ρ) (htop.mono fun _ hz => hz)
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1)
      (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re) (heq (mem_univ (2 : ℂ)))
  have hn : analyticOrderAt (LFunction χ) ρ = (analyticOrderNatAt (LFunction χ) ρ : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt hordnetop).symm
  have hn0 : analyticOrderNatAt (LFunction χ) ρ ≠ 0 := by
    intro h0'
    rw [h0'] at hn
    exact hordne0 (by simpa using hn)
  have hdiv : divisor (LFunction χ) K ρ = (analyticOrderNatAt (LFunction χ) ρ : ℤ) := by
    rw [hanaK.divisor_apply hmem, hn]; simp
  rw [Function.mem_support, hdiv]
  exact_mod_cast hn0

open Classical in
/-- **`boxZeros χ a b T`** — the enumerated zeros of `L(·,χ)` in the closed box
`{a ≤ Re ρ ≤ b, |Im ρ| ≤ T}`, as an honest `Finset ℂ` (the A2 deliverable). Total by `dite`;
the junk branch is unreachable for `χ ≠ 1` (`boxZeroSet_finite`). -/
noncomputable def boxZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b T : ℝ) :
    Finset ℂ :=
  if h : {ρ : ℂ | LFunction χ ρ = 0 ∧ a ≤ ρ.re ∧ ρ.re ≤ b ∧ |ρ.im| ≤ T}.Finite
  then h.toFinset else ∅

/-- **The membership spec of `boxZeros`** — exactly "is a zero, and lies in the box". -/
lemma mem_boxZeros {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) {a b T : ℝ}
    {ρ : ℂ} :
    ρ ∈ boxZeros χ a b T ↔ LFunction χ ρ = 0 ∧ a ≤ ρ.re ∧ ρ.re ≤ b ∧ |ρ.im| ≤ T := by
  rw [boxZeros, dif_pos (boxZeroSet_finite χ hχ1 a b T)]
  exact (boxZeroSet_finite χ hχ1 a b T).mem_toFinset

/-! ## 4. THE ASSEMBLY — the sharp explicit formula at the enumerated box zeros -/

/-- **THE SHARP EXPLICIT FORMULA WITH ENUMERATED ZEROS** (`psi_explicit_sharp`). Wave 1's
capstone `psi_explicit_sharp_of_riesz_residues` fired at `Z = boxZeros χ (σ₀−w) 1 (T+2)`, with
its only unmet hypothesis discharged by A1:

    ‖ψ(y,χ) + ∑_{ρ ∈ boxZeros} y^ρ/ρ‖
      ≤ (h+1)·log(y+h) + (E(y) + E(y+h))/h + #boxZeros · h,

`E = efShiftError` the landed contour-shift budget. At the campaign step `h = y/T` the last
term is `#Z·y/T`, and the first is `(y/T+1)·log(y+h)` — HB p.208's `O(yT^{−1}(log qy)²)` genre.

What remains hypothesis-carrying, named exactly:
* `hsep` — the **well-spacing** of the box zeros off the contour edges (the `∃T'`/`∃σ₀'` dodge;
  the landed single-zero shift carries the same thing as `hβsep`);
* `hsimple` — the box zeros are **simple**. This is the one genuinely open-shaped hypothesis:
  simplicity of Dirichlet `L`-zeros is not known. It enters only through the residue
  extraction, where a multiplicity `m_ρ` would multiply the `ρ`-th residue; the unconditional
  form therefore needs `efRieszSum`/`efZeroSum` re-based on a multiplicity-weighted sum, which
  changes wave 1's capstone interface. Flagged, not silently assumed. -/
theorem psi_explicit_sharp {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {y h T σ₀ w : ℝ}
    (hy : 3 ≤ y) (hh : 0 < h) (hT : 2 ≤ T) (hw : 0 < w)
    (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1)
    (hsep : ∀ ρ ∈ boxZeros χ (σ₀ - w) 1 (T + 2), σ₀ + w ≤ ρ.re ∧ |ρ.im| + w ≤ T)
    (hsimple : ∀ ρ ∈ boxZeros χ (σ₀ - w) 1 (T + 2), analyticOrderAt (LFunction χ) ρ = 1) :
    ‖psiChiR y χ + efZeroSum (boxZeros χ (σ₀ - w) 1 (T + 2)) y‖
      ≤ (h + 1) * Real.log (y + h)
        + (efShiftError f T σ₀ w y + efShiftError f T σ₀ w (y + h)) / h
        + ((boxZeros χ (σ₀ - w) 1 (T + 2)).card : ℝ) * h := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  set Z : Finset ℂ := boxZeros χ (σ₀ - w) 1 (T + 2) with hZ
  have hZall : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 → ρ ∈ Z :=
    fun ρ h1 h2 h3 h4 => by rw [hZ, mem_boxZeros hχ1]; exact ⟨h1, h2, h3, h4⟩
  have hZbox : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re ≤ 1 := by
    intro ρ hρ
    rw [hZ, mem_boxZeros hχ1] at hρ
    exact ⟨by linarith [hρ.2.1], hρ.2.2.1⟩
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hyh : (3 : ℝ) ≤ y + h := by linarith
  have h₁ := psi1_contour_shift_finset χ hχ hf hy hT hw hσ₀w hσ₀1 hsep hsimple hZall
  have h₂ := psi1_contour_shift_finset χ hχ hf hyh hT hw hσ₀w hσ₀1 hsep hsimple hZall
  have hmain := psi_explicit_sharp_of_riesz_residues (σ := 1) le_rfl hZbox hy1 hh χ h₁ h₂
  have hrw : y ^ ((1 : ℝ) - 1) = 1 := by
    rw [show (1 : ℝ) - 1 = 0 by ring, Real.rpow_zero]
  rw [hrw, mul_one] at hmain
  exact hmain

/-- **The sharp explicit formula at the ruled truncation height** `T = efHeight q = (log q+2)⁴`
(the ⟦N0 CLEAR⟧ ruling), differenced at the campaign step `h = y/T`. -/
theorem psi_sharp_at_efHeight {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {y σ₀ w : ℝ} (hy : 3 ≤ y) (hw : 0 < w)
    (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1)
    (hsep : ∀ ρ ∈ boxZeros χ (σ₀ - w) 1 (efHeight f + 2),
      σ₀ + w ≤ ρ.re ∧ |ρ.im| + w ≤ efHeight f)
    (hsimple : ∀ ρ ∈ boxZeros χ (σ₀ - w) 1 (efHeight f + 2),
      analyticOrderAt (LFunction χ) ρ = 1) :
    ‖psiChiR y χ + efZeroSum (boxZeros χ (σ₀ - w) 1 (efHeight f + 2)) y‖
      ≤ (y / efHeight f + 1) * Real.log (y + y / efHeight f)
        + (efShiftError f (efHeight f) σ₀ w y
            + efShiftError f (efHeight f) σ₀ w (y + y / efHeight f)) / (y / efHeight f)
        + ((boxZeros χ (σ₀ - w) 1 (efHeight f + 2)).card : ℝ) * (y / efHeight f) := by
  have hTpos : (0 : ℝ) < efHeight f := efHeight_pos (by omega)
  have hT2 : (2 : ℝ) ≤ efHeight f := le_trans (by norm_num) (sixteen_le_efHeight (by omega))
  exact psi_explicit_sharp χ hχ hf hy (by positivity) hT2 hw hσ₀w hσ₀1 hsep hsimple

end Salt.SW
