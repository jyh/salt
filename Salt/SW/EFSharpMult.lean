/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.EFSharpZeros

/-!
# THE FULCRUM CAMPAIGN, node N1 — wave 3: **the multiplicity-weighted re-base**

Wave 2 (`Salt/SW/EFSharpZeros.lean`) landed the sharp explicit formula with an *enumerated*
zero sum, but carried one open-shaped hypothesis all the way to the capstone:

    hsimple : ∀ ρ ∈ boxZeros …, analyticOrderAt (LFunction χ) ρ = 1

— i.e. *all the box zeros of `L(·,χ)` are simple*. That is **unknown mathematics** for Dirichlet
`L`-functions. This module removes it, by the route the flags entry ruled mandatory: re-base the
zero sums on **multiplicity-weighted** forms

    𝓡_M(x) = ∑_{ρ ∈ Z} m_ρ · x^{ρ+1}/(ρ(ρ+1)),   Σ_M(y) = ∑_{ρ ∈ Z} m_ρ · y^ρ/ρ,
    m_ρ = analyticOrderNatAt (LFunction χ) ρ  (`zeroMult`),

so the explicit formula carries multiplicities the way Heath-Brown's own p.208 argument
implicitly does (his `∑′` is a sum over zeros *with multiplicity*).

Everything here is **additive**: no declaration of wave 1 or wave 2 is touched, and the bridge
lemmas (`efRieszSumM_eq_of_simple`, `efZeroSumM_eq_of_simple`, `efMultTotal_eq_card_of_simple`)
show the weighted forms *collapse to wave 1's* at a simple zero set, so nothing landed is
orphaned.

## What changes in the argument, and what does not

* **The residue extraction** (§3) is the only place simplicity entered. At `ρ₀` of order `m` the
  local factorization `L = (·−ρ₀)^m · g` (`AnalyticAt.analyticOrderAt_ne_top`, `g ρ₀ ≠ 0`) gives
  `logDeriv L = m/(s−ρ₀) + logDeriv g` (mathlib `logDeriv_fun_pow`), so the de-singularized
  log-derivative is `G̃ = −L'/L + ∑_{ρ ∈ Z} m_ρ/(s−ρ)`, still analytic across every `ρ ∈ Z`, and
  the subtracted principal parts contribute `m_ρ·2πi·ker(ρ)` apiece.
* **`hZsimple` is deleted** and replaced by `hZzero : ∀ ρ ∈ Z, LFunction χ ρ = 0` — which wave 2
  *derived* from `hZsimple` and which the assembly gets for free from `mem_boxZeros`. So the
  hypothesis budget strictly *shrinks*.
* **`E` is unchanged** — literally wave 2's `efShiftError`. Verified by inspection at the bytes:
  the horizontal/left/tail estimates read only `hZsep` (edge separation) and `hZall` (nothing
  outside `Z` is a zero near the contour) through `hdist_edge`; the Borel–Carathéodory/Jensen
  edge constant `B` already prices **all** zeros of the ball *with multiplicity*
  (`norm_logDeriv_le_of_ball_dist` sits on the partial-fraction count). No estimate anywhere in
  the argument reads a zero's order.

## The multiplicity count (the wave-3 audit item)

Wave 1's half-box supply `LFunction_halfbox_zero_count` bounds

    ∑ᶠ u, divisor (LFunction χ) (closedBall (2+it₀) (37/20)) u  ≤  (7/log(39/37))·log(q(|t₀|+2)),

and `divisor` **is** the analytic-order divisor: `divisor f K ρ = analyticOrderNatAt f ρ` at every
`ρ ∈ K` (that is exactly how `boxZeroSet_finite` reads it). So the landed window count is already
a bound on `∑ m_ρ`, *not* on set-cardinality — the weighted de-smoothing's `∑_{ρ ∈ Z} m_ρ` term
(`efMultTotal`) needs **no new counting input**, and A3's batching consumes the same lemma it
would have consumed for `#Z`. Nothing is carried as an extra hypothesis on this account. §6 puts
that disposition in the kernel rather than in this prose: `efMultTotal_le_divisor` and
`efMultTotal_halfbox_le`.

## Status of the node

`psi_explicit_sharpM` / `psi_sharp_at_efHeightM` below are **N1 COMPLETE, UNCONDITIONAL IN
SIMPLICITY**: the surviving hypotheses are primitivity + the ranges + `hsep` (the well-spacing
`∃T'`/`∃σ₀'` dodge wave 2 already carried). What A3/A4 still owe downstream is unchanged by this
wave: **A3** — the numeric batching `∑_{|γ| ≤ T} m_ρ/|ρ| ≪ (log qT)²` (unit windows against
`LFunction_halfbox_zero_count`, now read with multiplicity, and `efMultTotal ≪ T log(qT)`);
**A4** — the `y^{β₀}/β₀` isolation of the exceptional zero out of `efZeroSumM` and the
`y^{1/4} log y` prime-power tail.
-/

open Complex DirichletCharacter ArithmeticFunction Filter Set Metric MeromorphicOn Function
  MeasureTheory
open scoped LSeries.notation Topology

namespace Salt.SW

/-! ## 1. The multiplicity, the weighted sums, and the collapse to wave 1 -/

/-- **The multiplicity of `ρ` as a zero of `L(·,χ)`** — the analytic order, read as a natural
number (`analyticOrderNatAt = (analyticOrderAt ·).toNat`). At a non-zero of `L` this is `0`, at a
simple zero `1`. This is the weight the explicit formula's zero sum must carry when simplicity is
not available. -/
noncomputable def zeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (LFunction χ) ρ

/-- For `χ ≠ 1` the `L`-function is not identically zero, so no analytic order is `⊤`. Route: the
identity theorem on the (preconnected) plane against `L(2,χ) ≠ 0`. -/
lemma analyticOrderAt_LFunction_ne_top {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (ρ : ℂ) : analyticOrderAt (LFunction χ) ρ ≠ ⊤ := by
  have hana : AnalyticOnNhd ℂ (LFunction χ) univ :=
    (differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have heq := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ ρ) (htop.mono fun _ hz => hz)
  exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1)
    (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re) (heq (mem_univ (2 : ℂ)))

/-- The order in `ℕ∞` is the `ℕ`-valued multiplicity, for `χ ≠ 1`. -/
lemma analyticOrderAt_LFunction_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (ρ : ℂ) : analyticOrderAt (LFunction χ) ρ = (zeroMult χ ρ : ℕ∞) :=
  (Nat.cast_analyticOrderNatAt (analyticOrderAt_LFunction_ne_top hχ1 ρ)).symm

/-- A simple zero has multiplicity `1` — the collapse hypothesis of wave 2. -/
lemma zeroMult_eq_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : analyticOrderAt (LFunction χ) ρ = 1) : zeroMult χ ρ = 1 := by
  rw [zeroMult, analyticOrderNatAt, h]
  rfl

/-- At a zero of `L(·,χ)` the multiplicity is at least `1`. -/
lemma one_le_zeroMult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) {ρ : ℂ}
    (hρ : LFunction χ ρ = 0) : 1 ≤ zeroMult χ ρ := by
  have hana : AnalyticOnNhd ℂ (LFunction χ) univ :=
    (differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ
  have hne : analyticOrderAt (LFunction χ) ρ ≠ 0 :=
    (hana ρ (mem_univ _)).analyticOrderAt_ne_zero.mpr hρ
  rcases Nat.eq_zero_or_pos (zeroMult χ ρ) with h0 | h
  · exact absurd (by rw [analyticOrderAt_LFunction_eq hχ1 ρ, h0]; rfl) hne
  · exact h

/-- **The local factorization at an arbitrary point**, at the honest multiplicity:
`L = (·−ρ)^{m_ρ} · g` near `ρ`, with `g` analytic and `g ρ ≠ 0`. This is the one input the
residue extraction needs, and it is available at *every* point (order `0` at a non-zero, order
`m ≥ 1` at a zero) — no simplicity anywhere. -/
lemma LFunction_local_factor {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    (ρ : ℂ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      LFunction χ =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ zeroMult χ ρ • g z := by
  have hana : AnalyticOnNhd ℂ (LFunction χ) univ :=
    (differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ
  simp only [zeroMult]
  exact (hana ρ (mem_univ _)).analyticOrderAt_ne_top.mp (analyticOrderAt_LFunction_ne_top hχ1 ρ)

/-- **The multiplicity-weighted sharp zero sum** `∑_{ρ ∈ Z} m_ρ·y^ρ/ρ` — the explicit formula's
zero term as HB p.208 writes it (`∑′` is over zeros *with multiplicity*). Collapses to wave 1's
`efZeroSum` at a simple zero set (`efZeroSumM_eq_of_simple`). -/
noncomputable def efZeroSumM {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Z : Finset ℂ)
    (y : ℝ) : ℂ :=
  ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) * (((y : ℝ) : ℂ) ^ ρ / ρ)

/-- **The multiplicity-weighted Riesz residue sum** `∑_{ρ ∈ Z} m_ρ·x^{ρ+1}/(ρ(ρ+1))` — what the
enumerated contour shift of the *smoothed* carrier `ψ₁` produces when the zeros are allowed to be
multiple. Collapses to wave 1's `efRieszSum` at a simple zero set. -/
noncomputable def efRieszSumM {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Z : Finset ℂ)
    (x : ℝ) : ℂ :=
  ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) * (((x : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))

/-- **The total multiplicity** `∑_{ρ ∈ Z} m_ρ` — the de-smoothing's counting weight, replacing
wave 1's `#Z`. Bounded by the *same* landed window count as `#Z` would be, because
`LFunction_halfbox_zero_count` counts the analytic divisor (module docstring). -/
noncomputable def efMultTotal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Z : Finset ℂ) :
    ℝ :=
  ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ)

lemma efMultTotal_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Z : Finset ℂ) :
    0 ≤ efMultTotal χ Z :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- **The collapse, Riesz side**: at a set of simple zeros the weighted sum *is* wave 1's. -/
lemma efRieszSumM_eq_of_simple {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {Z : Finset ℂ}
    (hsimple : ∀ ρ ∈ Z, analyticOrderAt (LFunction χ) ρ = 1) (x : ℝ) :
    efRieszSumM χ Z x = efRieszSum Z x := by
  rw [efRieszSumM, efRieszSum]
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  rw [zeroMult_eq_one (hsimple ρ hρ)]
  push_cast
  ring

/-- **The collapse, sharp side**: at a set of simple zeros the weighted sum *is* wave 1's. -/
lemma efZeroSumM_eq_of_simple {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {Z : Finset ℂ}
    (hsimple : ∀ ρ ∈ Z, analyticOrderAt (LFunction χ) ρ = 1) (y : ℝ) :
    efZeroSumM χ Z y = efZeroSum Z y := by
  rw [efZeroSumM, efZeroSum]
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  rw [zeroMult_eq_one (hsimple ρ hρ)]
  push_cast
  ring

/-- **The collapse, count side**: at a set of simple zeros the total multiplicity is `#Z`. -/
lemma efMultTotal_eq_card_of_simple {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {Z : Finset ℂ} (hsimple : ∀ ρ ∈ Z, analyticOrderAt (LFunction χ) ρ = 1) :
    efMultTotal χ Z = (Z.card : ℝ) := by
  rw [efMultTotal]
  rw [Finset.sum_congr rfl (fun ρ hρ => by rw [zeroMult_eq_one (hsimple ρ hρ)]; norm_num :
    ∀ ρ ∈ Z, ((zeroMult χ ρ : ℝ)) = 1)]
  simp

/-- **THE β₀ ERASE-SPLIT (N4b W0-i).** The exceptional zero's residue peeled off the weighted
zero sum:

    ∑_{ρ ∈ Z} m_ρ·y^ρ/ρ  =  m_{β₀}·y^{β₀}/β₀  +  ∑_{ρ ∈ Z∖{β₀}} m_ρ·y^ρ/ρ.

HB p.209 spends the first term against the Siegel-zero main term and prices the second by the
repulsion band; this is the split, at the bytes, via `Finset.add_sum_erase` (the corpus pattern
of `Salt.HB.neg_re_logDeriv_differenced`'s `hsplit`). -/
lemma efZeroSumM_erase_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {Z : Finset ℂ}
    {β₀ : ℂ} (hβZ : β₀ ∈ Z) (y : ℝ) :
    efZeroSumM χ Z y
      = (zeroMult χ β₀ : ℂ) * (((y : ℝ) : ℂ) ^ β₀ / β₀) + efZeroSumM χ (Z.erase β₀) y := by
  classical
  simp only [efZeroSumM]
  exact (Finset.add_sum_erase Z (fun ρ => (zeroMult χ ρ : ℂ) * (((y : ℝ) : ℂ) ^ ρ / ρ)) hβZ).symm

/-! ## 2. Two pieces of plumbing: `rectBI` scaling and the `m`-fold log-derivative -/

/-- **`rectBI` is homogeneous.** Scaling the integrand by a constant scales the rectangle boundary
integral — the step that turns "one residue per zero" into "`m_ρ` residues per zero". -/
lemma rectBI_const_mul (z w c : ℂ) (F : ℂ → ℂ) :
    rectBI z w (fun s => c * F s) = c * rectBI z w F := by
  simp only [rectBI, intervalIntegral.integral_const_mul]
  ring

/-- **The `m`-fold pole of the log-derivative.** `logDeriv ((·−ρ)^m) z = m/(z−ρ)` — the literal
statement wave 2's pricing note named ("`logDeriv((·−ρ)^m) = m/(·−ρ)`"). Unconditional: at `z = ρ`
both sides are the junk value `0`. -/
lemma logDeriv_sub_const_pow (ρ z : ℂ) (m : ℕ) :
    logDeriv (fun u : ℂ => (u - ρ) ^ m) z = (m : ℂ) / (z - ρ) := by
  have hd : DifferentiableAt ℂ (fun u : ℂ => u - ρ) z := differentiableAt_id.sub_const _
  have hlin : logDeriv (fun u : ℂ => u - ρ) z = 1 / (z - ρ) := by
    rw [logDeriv_apply, deriv_sub_const]; simp
  have h2 := logDeriv_fun_pow (f := fun u : ℂ => u - ρ) (x := z) hd m
  simp only [hlin, mul_one_div] at h2
  exact h2

/-! ## 3. THE MULTIPLICITY-WEIGHTED CONTOUR SHIFT — wave 2's A1 with `hsimple` deleted -/

set_option maxHeartbeats 2400000 in
-- The multiplicity-weighted assembly runs the S5c contour-shift argument on the de-singularized
-- integrand `A = ker·G̃`, `G̃ = −L'/L + ∑ m_ρ/(s−ρ)` (Goursat-clean on the box once *every*
-- enumerated removable singularity is filled, whatever the orders), and re-attaches `m_ρ`
-- `kernel_residue` applications per enumerated zero. The copied edge/tail estimates plus the
-- `E`-arithmetic need the same headroom the wave-2 variant needed, plus the scaling algebra.
/-- **A1-M — the contour-shift bound at an enumerated zero set, WITH MULTIPLICITY, AT THE GAP
HYPOTHESIS (N4B-W0.5).** Wave 2's `psi1_contour_shift_finset` with its `hZsimple` hypothesis
**deleted** and its `hZall` **weakened to the width-`w` gap form**:

* `hZsep` — every `ρ ∈ Z` is `w`-separated from the left and horizontal edges (unchanged);
* `hZzero` — every `ρ ∈ Z` **is a zero** (what wave 2 *derived* from `hZsimple`; free at
  `Z = boxZeros`);
* `hZall` — every zero in the widened box region is **either enumerated or `w`-above the
  contour's horizontal edges**: `ρ ∈ Z ∨ T + w ≤ |Im ρ|`.

The old hypothesis (`… → ρ ∈ Z`, demanding a *zero-free band of width 2* above the contour) is the
`Or.inl` specialization — `psi1_contour_shift_finsetM` below, statement untouched. The weakened
form is what makes the well-spacing binder `hsep` a **pigeonhole theorem** rather than an
assumption: only a width-`2w` band must be cleared, and `w` may be taken as small as the zero
count allows. Nothing in the estimates changes — `hZall` is read at exactly two sites (box
non-vanishing off `Z`, and the edge-distance argument `hdist_edge`), and at both the new right
disjunct closes the goal directly (`|Im| ≤ T` on the contour vs `T + w ≤ |Im ρ|`).

The shift picks up **`m_ρ` residues per enumerated zero**:

    ‖ψ₁(x,χ) + ∑_{ρ ∈ Z} m_ρ·x^{ρ+1}/(ρ(ρ+1))‖ ≤ E,

with `E = efShiftError f T σ₀ w x` **identical** to wave 2's, hence to the landed
`psi1_contour_shift_exceptional` bound: no estimate in the argument reads a zero's order. -/
theorem psi1_contour_shift_finsetM_gap {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {x : ℝ} (hx : 3 ≤ x) {T σ₀ w : ℝ} {Z : Finset ℂ}
    (hT : 2 ≤ T) (hw : 0 < w) (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1)
    (hZsep : ∀ ρ ∈ Z, σ₀ + w ≤ ρ.re ∧ |ρ.im| + w ≤ T)
    (hZzero : ∀ ρ ∈ Z, LFunction χ ρ = 0)
    (hZall : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 →
      ρ ∈ Z ∨ T + w ≤ |ρ.im|) :
    ‖psi1Chi x χ + efRieszSumM χ Z x‖ ≤ efShiftError f T σ₀ w x := by
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
  -- every member of `Z` sits strictly inside the strip
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
    · rcases hZall s hs0 (by linarith) (not_le.mp h1).le (by linarith) with hmem | hfar
      · exact hsZ hmem
      · linarith
  -- THE LOCAL FACTORIZATIONS, at the honest multiplicities (no simplicity)
  choose g hg_ana hg_ne hg_eq using LFunction_local_factor (χ := χ) hχ1
  -- the de-singularized log-derivative, multiplicity-weighted
  obtain ⟨Gtrue, hGtrue⟩ : ∃ Gt : ℂ → ℂ, ∀ s : ℂ, Gt s =
      if s ∈ Z then -logDeriv (g s) s + ∑ ρ ∈ Z.erase s, (zeroMult χ ρ : ℂ) / (s - ρ)
      else -logDeriv (LFunction χ) s + ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ) := ⟨_, fun _ => rfl⟩
  have hZclosed : IsOpen ((↑Z : Set ℂ)ᶜ) := Z.finite_toSet.isClosed.isOpen_compl
  -- differentiability of `Gtrue` at an enumerated zero (the removable singularity, order `m`)
  have hGtrue_Z : ∀ ρ₀ ∈ Z, DifferentiableAt ℂ Gtrue ρ₀ := by
    intro ρ₀ hρ₀
    have hH_diff : DifferentiableAt ℂ
        (fun z => -logDeriv (g ρ₀) z + ∑ ρ ∈ Z.erase ρ₀, (zeroMult χ ρ : ℂ) / (z - ρ)) ρ₀ := by
      refine DifferentiableAt.add ?_ ?_
      · simp only [logDeriv_apply]
        exact (((hg_ana ρ₀).deriv.differentiableAt).div (hg_ana ρ₀).differentiableAt
          (hg_ne ρ₀)).neg
      · refine DifferentiableAt.fun_sum ?_
        intro ρ hρ
        have hne : ρ₀ - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hρ))
        exact (differentiableAt_const _).div (differentiableAt_id.sub_const _) hne
    have hev : Gtrue =ᶠ[𝓝 ρ₀]
        (fun z => -logDeriv (g ρ₀) z + ∑ ρ ∈ Z.erase ρ₀, (zeroMult χ ρ : ℂ) / (z - ρ)) := by
      obtain ⟨U, hU_eq, hU_open, hρU⟩ := _root_.eventually_nhds_iff.mp (hg_eq ρ₀)
      have hg_ne_nhds : ∀ᶠ z in 𝓝 ρ₀, g ρ₀ z ≠ 0 :=
        (hg_ana ρ₀).continuousAt.eventually_ne (hg_ne ρ₀)
      obtain ⟨V, hV_ne, hV_open, hρV⟩ := _root_.eventually_nhds_iff.mp hg_ne_nhds
      obtain ⟨W, hW_ana, hW_open, hρW⟩ :=
        _root_.eventually_nhds_iff.mp (hg_ana ρ₀).eventually_analyticAt
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
        have hlocal : LFunction χ =ᶠ[𝓝 z]
            (fun u => (u - ρ₀) ^ zeroMult χ ρ₀ * g ρ₀ u) := by
          filter_upwards [(((hU_open.inter hV_open).inter hW_open).inter hEopen).mem_nhds hz]
            with u hu
          have heq := hU_eq u hu.1.1.1
          simp only [smul_eq_mul] at heq
          exact heq
        have hlogL : logDeriv (LFunction χ) z
            = logDeriv (fun u => (u - ρ₀) ^ zeroMult χ ρ₀ * g ρ₀ u) z := by
          rw [logDeriv_apply, logDeriv_apply, hlocal.deriv_eq, hlocal.eq_of_nhds]
        have hd1 : DifferentiableAt ℂ (fun u : ℂ => (u - ρ₀) ^ zeroMult χ ρ₀) z :=
          (differentiableAt_id.sub_const _).pow _
        have hpow_ne : (z - ρ₀) ^ zeroMult χ ρ₀ ≠ 0 := pow_ne_zero _ hzρ'
        have hmul : logDeriv (fun u => (u - ρ₀) ^ zeroMult χ ρ₀ * g ρ₀ u) z
            = logDeriv (fun u : ℂ => (u - ρ₀) ^ zeroMult χ ρ₀) z + logDeriv (g ρ₀) z :=
          logDeriv_mul z hpow_ne hz_ne hd1 hz_diff
        have hlin : logDeriv (fun u : ℂ => (u - ρ₀) ^ zeroMult χ ρ₀) z
            = (zeroMult χ ρ₀ : ℂ) / (z - ρ₀) := logDeriv_sub_const_pow _ _ _
        have hsplit : ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (z - ρ)
            = (zeroMult χ ρ₀ : ℂ) / (z - ρ₀)
              + ∑ ρ ∈ Z.erase ρ₀, (zeroMult χ ρ : ℂ) / (z - ρ) :=
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
          (fun z => -logDeriv (LFunction χ) z + ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (z - ρ)) := by
        filter_upwards [hZclosed.mem_nhds (by simpa using hsZ)] with z hz
        rw [hGtrue z, if_neg (by simpa using hz)]
      have hLs : LFunction χ s ≠ 0 := hLne_box s hsl hsu hsi hsZ
      have hGd : DifferentiableAt ℂ
          (fun z => -logDeriv (LFunction χ) z + ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (z - ρ)) s := by
        refine (hlogD_diff s hLs).add ?_
        refine DifferentiableAt.fun_sum ?_
        intro ρ hρ
        have hne : s ≠ ρ := by rintro rfl; exact hsZ hρ
        exact (differentiableAt_const _).div (differentiableAt_id.sub_const _)
          (sub_ne_zero.mpr hne)
      exact hGd.congr_of_eventuallyEq hGeq
  -- the integrands
  set F : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) * (-logDeriv (LFunction χ) s) with hF
  set A : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) * Gtrue s with hA
  set Bfun : ℂ → ℂ := fun s =>
    ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) * ((x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - ρ)) with hBfun
  set κ : ℂ := efRieszSumM χ Z x with hκ
  have hFnorm : ∀ s : ℂ, ‖F s‖
      = x ^ (s.re + 1) * ‖(s * (s + 1))⁻¹‖ * ‖logDeriv (LFunction χ) s‖ := by
    intro s
    simp only [hF]
    rw [norm_mul, norm_neg, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.add_re,
      Complex.one_re, div_eq_mul_inv, ← norm_inv]
  have hkermul : ∀ s : ℂ,
      (x : ℂ) ^ (s + 1) / (s * (s + 1)) * (∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ))
      = ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) * ((x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - ρ)) := by
    intro s
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ρ _ => by ring)
  -- pointwise splitting `F = A − Bfun` off `Z`
  have hAFB : ∀ s : ℂ, s ∉ Z → F s = A s - Bfun s := by
    intro s hsZ
    have hGt : Gtrue s = -logDeriv (LFunction χ) s + ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ) := by
      rw [hGtrue s, if_neg hsZ]
    have h2 : (x : ℂ) ^ (s + 1) / (s * (s + 1))
          * (-logDeriv (LFunction χ) s + ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ))
        = (x : ℂ) ^ (s + 1) / (s * (s + 1)) * (-logDeriv (LFunction χ) s)
          + ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) * ((x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - ρ)) := by
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
  -- edge integrability, for `A`, for `Bfun`, and for each weighted residue kernel
  have hedge_int : ∀ (γ : ℝ → ℂ) (a b : ℝ), Continuous γ →
      Set.MapsTo γ (Set.uIcc a b) (closedRect zc wc) →
      (∀ t ∈ Set.uIcc a b, γ t ∉ Z) →
      IntervalIntegrable (fun t => A (γ t)) volume a b ∧
        IntervalIntegrable (fun t => Bfun (γ t)) volume a b ∧
        ∀ ρ ∈ Z, IntervalIntegrable
          (fun t => (zeroMult χ ρ : ℂ)
            * ((x : ℂ) ^ (γ t + 1) / (γ t * (γ t + 1)) / (γ t - ρ))) volume a b := by
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
        exact (differentiableAt_const _).mul
          ((hkerAt (γ t) (hden t ht).1 (hden t ht).2).div (differentiableAt_id.sub_const _)
            (hZne ρ hρ t ht))
      exact ((hd.continuousAt).comp hγ.continuousAt).continuousWithinAt
    · intro ρ hρ
      apply ContinuousOn.intervalIntegrable
      intro t ht
      have hd : DifferentiableAt ℂ
          (fun s : ℂ => (zeroMult χ ρ : ℂ) * ((x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - ρ)))
          (γ t) :=
        (differentiableAt_const _).mul
          ((hkerAt (γ t) (hden t ht).1 (hden t ht).2).div (differentiableAt_id.sub_const _)
            (hZne ρ hρ t ht))
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
  -- THE RESIDUE EXTRACTION: `m_ρ` residues per enumerated zero, summed
  have hBsplit : rectBI zc wc Bfun
      = ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ)
          * rectBI zc wc (fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - ρ)) := by
    rw [hBfun,
      rectBI_finsetSum Z
        (fun ρ s => (zeroMult χ ρ : ℂ) * ((x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - ρ)))
        hK_bot hK_top hK_rgt hK_lft]
    exact Finset.sum_congr rfl (fun ρ _ => rectBI_const_mul _ _ _ _)
  have hBres : rectBI zc wc Bfun = 2 * ↑Real.pi * I * κ := by
    rw [hBsplit, hκ, efRieszSumM, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    have him : |ρ.im| < T := by linarith [(hZsep ρ hρ).2]
    have him' := abs_lt.mp him
    rw [kernel_residue hxpos (β := ρ) (by rw [hzc_re]; exact hσ₀pos)
      (by rw [hzc_re, hwc_re]; exact hσ₀c) (by rw [hzc_im, hwc_im]; linarith)
      ⟨by rw [hzc_re]; linarith [(hZsep ρ hρ).1],
        by rw [hwc_re]; linarith [hZre1 ρ hρ]⟩
      ⟨by rw [hzc_im]; linarith [him'.1], by rw [hwc_im]; linarith [him'.2]⟩]
    ring
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
    · by_cases hρre2 : ρ.re ≤ σ₀ - w
      · have hre := Complex.abs_re_le_norm (s - ρ)
        rw [Complex.sub_re] at hre
        calc w ≤ s.re - ρ.re := by linarith
          _ = |s.re - ρ.re| := (abs_of_nonneg (by linarith)).symm
          _ ≤ ‖s - ρ‖ := hre
      · -- the gap disjunct: `ρ` is not enumerated and sits inside the strip, so it is `w` above
        -- the horizontal edges, and the *imaginary* distance already exceeds `w`
        rcases hZall ρ hρ0 (le_of_lt (not_le.mp hρre2)) hρre1.le hρim with hmem | hfar
        · exact absurd hmem hρZ
        · have him := Complex.abs_im_le_norm (s - ρ)
          rw [Complex.sub_im] at him
          have hb : |ρ.im| - |s.im| ≤ |ρ.im - s.im| := abs_sub_abs_le_abs_sub _ _
          rw [abs_sub_comm] at hb
          linarith
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
  -- final assembly (the weighted residue sum absorbs the residues)
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

/-- **A1-M — the contour-shift bound at an enumerated zero set, WITH MULTIPLICITY.** Wave 2's
`psi1_contour_shift_finset` with its `hZsimple` hypothesis **deleted**:

* `hZsep` — every `ρ ∈ Z` is `w`-separated from the left and horizontal edges (unchanged);
* `hZzero` — every `ρ ∈ Z` **is a zero** (what wave 2 *derived* from `hZsimple`; free at
  `Z = boxZeros`);
* `hZall` — `Z` contains every zero in the widened box region (unchanged; the contour identity is
  an equality, so nothing may be left out).

The shift picks up **`m_ρ` residues per enumerated zero**:

    ‖ψ₁(x,χ) + ∑_{ρ ∈ Z} m_ρ·x^{ρ+1}/(ρ(ρ+1))‖ ≤ E,

with `E = efShiftError f T σ₀ w x` **identical** to wave 2's, hence to the landed
`psi1_contour_shift_exceptional` bound: no estimate in the argument reads a zero's order.

Statement unchanged since wave 3; the proof is now the `Or.inl` specialization of the gap form
`psi1_contour_shift_finsetM_gap`. -/
theorem psi1_contour_shift_finsetM {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {x : ℝ} (hx : 3 ≤ x) {T σ₀ w : ℝ} {Z : Finset ℂ}
    (hT : 2 ≤ T) (hw : 0 < w) (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1)
    (hZsep : ∀ ρ ∈ Z, σ₀ + w ≤ ρ.re ∧ |ρ.im| + w ≤ T)
    (hZzero : ∀ ρ ∈ Z, LFunction χ ρ = 0)
    (hZall : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 → ρ ∈ Z) :
    ‖psi1Chi x χ + efRieszSumM χ Z x‖ ≤ efShiftError f T σ₀ w x :=
  psi1_contour_shift_finsetM_gap χ hχ hf hx hT hw hσ₀w hσ₀1 hZsep hZzero
    (fun ρ h1 h2 h3 h4 => Or.inl (hZall ρ h1 h2 h3 h4))

/-! ## 4. The weighted de-smoothing and the weighted capstone

Wave 1's `cpow_riesz_residue_desmooth` is per-zero and order-blind, so the multiplicities ride
through the mean-value bound **linearly**: the `#Z·h·y^{σ−1}` of `efRieszSum_diff_sub_efZeroSum_le`
becomes `(∑_ρ m_ρ)·h·y^{σ−1}`, the total multiplicity. Per the module docstring, the landed
half-box supply already bounds *that* quantity (it counts the analytic divisor), so no new
counting hypothesis appears. -/

/-- **The residue de-smoothing at the multiplicity-weighted sums.** If every enumerated zero has
`0 < Re ρ ≤ σ ≤ 1`, then

    ‖h^{−1}(𝓡_M(y+h) − 𝓡_M(y)) − ∑_{ρ ∈ Z} m_ρ·y^ρ/ρ‖ ≤ (∑_{ρ ∈ Z} m_ρ) · h · y^{σ−1}.

At the campaign step `h = y/T` this is `efMultTotal·y^σ/T` — a full `1/T` below the weighted zero
sum's own size, exactly as in wave 1. -/
theorem efRieszSumM_diff_sub_efZeroSumM_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {Z : Finset ℂ} {σ : ℝ} (hσ : σ ≤ 1) (hZ : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re ≤ σ) {y h : ℝ}
    (hy : 1 ≤ y) (hh : 0 < h) :
    ‖(efRieszSumM χ Z (y + h) - efRieszSumM χ Z y) / (h : ℂ) - efZeroSumM χ Z y‖
      ≤ efMultTotal χ Z * (h * y ^ (σ - 1)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set D : ℂ → ℂ := fun ρ => (zeroMult χ ρ : ℂ) *
    (((y + h : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))
      - ((y : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) - (h : ℂ) * (((y : ℝ) : ℂ) ^ ρ / ρ)) with hD
  have hDsum : ∑ ρ ∈ Z, D ρ
      = (efRieszSumM χ Z (y + h) - efRieszSumM χ Z y) - (h : ℂ) * efZeroSumM χ Z y := by
    simp only [hD, efRieszSumM, efZeroSumM, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun ρ _ => by ring)
  have hid : (efRieszSumM χ Z (y + h) - efRieszSumM χ Z y) / (h : ℂ) - efZeroSumM χ Z y
      = (∑ ρ ∈ Z, D ρ) / (h : ℂ) := by
    rw [hDsum]; field_simp
  have hterm : ∀ ρ ∈ Z, ‖D ρ‖ ≤ (zeroMult χ ρ : ℝ) * (h ^ 2 * y ^ (σ - 1)) := by
    intro ρ hρ
    obtain ⟨hρ0, hρσ⟩ := hZ ρ hρ
    have hbase := cpow_riesz_residue_desmooth hρ0 (le_trans hρσ hσ) hy hh
    have hmono : y ^ (ρ.re - 1) ≤ y ^ (σ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hy (by linarith)
    have hinner : ‖((y + h : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))
        - ((y : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) - (h : ℂ) * (((y : ℝ) : ℂ) ^ ρ / ρ)‖
        ≤ h ^ 2 * y ^ (σ - 1) := by
      calc _ ≤ h ^ 2 * y ^ (ρ.re - 1) := hbase
        _ ≤ h ^ 2 * y ^ (σ - 1) := mul_le_mul_of_nonneg_left hmono (by positivity)
    rw [hD]
    simp only [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hinner (by positivity)
  have hsum : ‖∑ ρ ∈ Z, D ρ‖ ≤ efMultTotal χ Z * (h ^ 2 * y ^ (σ - 1)) := by
    calc ‖∑ ρ ∈ Z, D ρ‖ ≤ ∑ ρ ∈ Z, ‖D ρ‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) * (h ^ 2 * y ^ (σ - 1)) := Finset.sum_le_sum hterm
      _ = efMultTotal χ Z * (h ^ 2 * y ^ (σ - 1)) := by rw [efMultTotal, ← Finset.sum_mul]
  rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, div_le_iff₀ hh]
  calc ‖∑ ρ ∈ Z, D ρ‖ ≤ efMultTotal χ Z * (h ^ 2 * y ^ (σ - 1)) := hsum
    _ = efMultTotal χ Z * (h * y ^ (σ - 1)) * h := by ring

/-- **THE WEIGHTED CAPSTONE** — wave 1's `psi_explicit_sharp_of_riesz_residues` at the
multiplicity-weighted sums:

    ‖ψ₁(y,χ) + 𝓡_M(y)‖ ≤ E₁,  ‖ψ₁(y+h,χ) + 𝓡_M(y+h)‖ ≤ E₂
      ⟹ ‖ψ(y,χ) + ∑_{ρ ∈ Z} m_ρ·y^ρ/ρ‖
           ≤ (h+1)log(y+h) + (E₁+E₂)/h + (∑_ρ m_ρ)·h·y^{σ−1}.

The bridge (`psi_sharp_of_riesz_bounds`) is order-blind and reused verbatim. -/
theorem psi_explicit_sharpM_of_riesz_residues {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {Z : Finset ℂ} {σ : ℝ} (hσ : σ ≤ 1) (hZ : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re ≤ σ) {y h : ℝ}
    (hy : 1 ≤ y) (hh : 0 < h) {E₁ E₂ : ℝ}
    (h₁ : ‖psi1Chi y χ + efRieszSumM χ Z y‖ ≤ E₁)
    (h₂ : ‖psi1Chi (y + h) χ + efRieszSumM χ Z (y + h)‖ ≤ E₂) :
    ‖psiChiR y χ + efZeroSumM χ Z y‖
      ≤ (h + 1) * Real.log (y + h) + (E₁ + E₂) / h
        + efMultTotal χ Z * (h * y ^ (σ - 1)) := by
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hsock := psi_sharp_of_riesz_bounds (A₁ := -efRieszSumM χ Z y)
    (A₂ := -efRieszSumM χ Z (y + h)) hy hh χ (by simpa using h₁) (by simpa using h₂)
  have hdes := efRieszSumM_diff_sub_efZeroSumM_le χ hσ hZ hy hh
  have hsplit : psiChiR y χ + efZeroSumM χ Z y
      = (psiChiR y χ - (-efRieszSumM χ Z (y + h) - -efRieszSumM χ Z y) / (h : ℂ))
        - ((efRieszSumM χ Z (y + h) - efRieszSumM χ Z y) / (h : ℂ) - efZeroSumM χ Z y) := by
    field_simp
    ring
  rw [hsplit]
  calc ‖(psiChiR y χ - (-efRieszSumM χ Z (y + h) - -efRieszSumM χ Z y) / (h : ℂ))
        - ((efRieszSumM χ Z (y + h) - efRieszSumM χ Z y) / (h : ℂ) - efZeroSumM χ Z y)‖
      ≤ ‖psiChiR y χ - (-efRieszSumM χ Z (y + h) - -efRieszSumM χ Z y) / (h : ℂ)‖
        + ‖(efRieszSumM χ Z (y + h) - efRieszSumM χ Z y) / (h : ℂ) - efZeroSumM χ Z y‖ :=
        norm_sub_le _ _
    _ ≤ ((h + 1) * Real.log (y + h) + (E₁ + E₂) / h) + efMultTotal χ Z * (h * y ^ (σ - 1)) :=
        add_le_add hsock hdes
    _ = (h + 1) * Real.log (y + h) + (E₁ + E₂) / h
          + efMultTotal χ Z * (h * y ^ (σ - 1)) := by ring

/-! ## 5. THE UNCONDITIONAL ASSEMBLY — N1 without `hsimple` -/

/-- **THE SHARP EXPLICIT FORMULA, UNCONDITIONAL IN SIMPLICITY** (`psi_explicit_sharpM`). Wave 2's
`psi_explicit_sharp` with the `hsimple` hypothesis **gone**:

    ‖ψ(y,χ) + ∑_{ρ ∈ boxZeros} m_ρ·y^ρ/ρ‖
      ≤ (h+1)·log(y+h) + (E(y) + E(y+h))/h + (∑_{ρ ∈ boxZeros} m_ρ)·h,

`E = efShiftError` the landed contour-shift budget, `m_ρ = zeroMult χ ρ` the analytic order.

**Surviving hypotheses, exactly**: `hχ` (primitivity) and `hf : 2 ≤ f`; the ranges `3 ≤ y`,
`0 < h`, `2 ≤ T`, `0 < w`, `9/10 ≤ σ₀ − w`, `σ₀ < 1`; and `hsep`, the well-spacing of the box
zeros off the contour edges — the same `∃T'`/`∃σ₀'` dodge wave 2 carried and the landed
single-zero shift carries as `hβsep`. **No simplicity, no zero-density, no count hypothesis**: the
`∑ m_ρ` in the error is a *conclusion-side* quantity, priced by the landed
`LFunction_halfbox_zero_count` through §6's `efMultTotal_halfbox_le` (the window count is a count
of the analytic divisor, i.e. already with multiplicity).

At a set of simple zeros this specializes back to wave 2's statement through
`efZeroSumM_eq_of_simple` / `efMultTotal_eq_card_of_simple`.

**What A3/A4 still owe downstream**: A3 — the batching `∑_{|γ| ≤ T} m_ρ/|ρ| ≪ (log qT)²` and the
numeric `efMultTotal ≪ T log(qT)` from unit windows against the half-box count; A4 — the
`y^{β₀}/β₀` isolation of the exceptional zero out of `efZeroSumM` and the `y^{1/4} log y`
prime-power tail. Neither is affected by the re-base beyond reading the count with
multiplicity. -/
theorem psi_explicit_sharpM {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {y h T σ₀ w : ℝ}
    (hy : 3 ≤ y) (hh : 0 < h) (hT : 2 ≤ T) (hw : 0 < w)
    (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1)
    (hsep : ∀ ρ ∈ boxZeros χ (σ₀ - w) 1 (T + 2), σ₀ + w ≤ ρ.re ∧ |ρ.im| + w ≤ T) :
    ‖psiChiR y χ + efZeroSumM χ (boxZeros χ (σ₀ - w) 1 (T + 2)) y‖
      ≤ (h + 1) * Real.log (y + h)
        + (efShiftError f T σ₀ w y + efShiftError f T σ₀ w (y + h)) / h
        + efMultTotal χ (boxZeros χ (σ₀ - w) 1 (T + 2)) * h := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  set Z : Finset ℂ := boxZeros χ (σ₀ - w) 1 (T + 2) with hZ
  have hZall : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 → ρ ∈ Z :=
    fun ρ h1 h2 h3 h4 => by rw [hZ, mem_boxZeros hχ1]; exact ⟨h1, h2, h3, h4⟩
  have hZzero : ∀ ρ ∈ Z, LFunction χ ρ = 0 := by
    intro ρ hρ
    rw [hZ, mem_boxZeros hχ1] at hρ
    exact hρ.1
  have hZbox : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re ≤ 1 := by
    intro ρ hρ
    rw [hZ, mem_boxZeros hχ1] at hρ
    exact ⟨by linarith [hρ.2.1], hρ.2.2.1⟩
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hyh : (3 : ℝ) ≤ y + h := by linarith
  have h₁ := psi1_contour_shift_finsetM χ hχ hf hy hT hw hσ₀w hσ₀1 hsep hZzero hZall
  have h₂ := psi1_contour_shift_finsetM χ hχ hf hyh hT hw hσ₀w hσ₀1 hsep hZzero hZall
  have hmain := psi_explicit_sharpM_of_riesz_residues (σ := 1) χ le_rfl hZbox hy1 hh h₁ h₂
  have hrw : y ^ ((1 : ℝ) - 1) = 1 := by
    rw [show (1 : ℝ) - 1 = 0 by ring, Real.rpow_zero]
  rw [hrw, mul_one] at hmain
  exact hmain

/-- **The unconditional sharp explicit formula at the ruled truncation height**
`T = efHeight q = (log q+2)⁴` (the ⟦N0 CLEAR⟧ ruling), differenced at the campaign step
`h = y/T`. Wave 2's `psi_sharp_at_efHeight` with `hsimple` deleted — N1's deliverable to the
fulcrum campaign. -/
theorem psi_sharp_at_efHeightM {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {y σ₀ w : ℝ} (hy : 3 ≤ y) (hw : 0 < w)
    (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1)
    (hsep : ∀ ρ ∈ boxZeros χ (σ₀ - w) 1 (efHeight f + 2),
      σ₀ + w ≤ ρ.re ∧ |ρ.im| + w ≤ efHeight f) :
    ‖psiChiR y χ + efZeroSumM χ (boxZeros χ (σ₀ - w) 1 (efHeight f + 2)) y‖
      ≤ (y / efHeight f + 1) * Real.log (y + y / efHeight f)
        + (efShiftError f (efHeight f) σ₀ w y
            + efShiftError f (efHeight f) σ₀ w (y + y / efHeight f)) / (y / efHeight f)
        + efMultTotal χ (boxZeros χ (σ₀ - w) 1 (efHeight f + 2)) * (y / efHeight f) := by
  have hTpos : (0 : ℝ) < efHeight f := efHeight_pos (by omega)
  have hT2 : (2 : ℝ) ≤ efHeight f := le_trans (by norm_num) (sixteen_le_efHeight (by omega))
  exact psi_explicit_sharpM χ hχ hf hy (by positivity) hT2 hw hσ₀w hσ₀1 hsep

/-! ## 6. THE MULTIPLICITY COUNT — the landed supply already counts with multiplicity

The wave-3 audit item, discharged in the kernel rather than in prose: wave 1's half-box supply
bounds the **analytic divisor's mass** over the ball, and the divisor of an analytic function *is*
the multiplicity function (`AnalyticOnNhd.divisor_apply`). So `efMultTotal` — the weighted
de-smoothing's counting weight — is bounded by exactly the landed count, with no new input. -/

/-- **The total multiplicity of an enumerated zero set is at most the divisor's mass.** For `Z` a
finite set of zeros of `L(·,χ)` inside a compact `K`,

    ∑_{ρ ∈ Z} m_ρ  ≤  ∑ᶠ u, divisor (L(·,χ)) K u.

Route: `divisor f K ρ = m_ρ` at every `ρ ∈ K` for analytic `f`, the divisor is nonnegative
(`AnalyticOnNhd.divisor_nonneg`), and `Z` sits inside its (finite) support because every `ρ ∈ Z`
has `m_ρ ≥ 1`. -/
lemma efMultTotal_le_divisor {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    {Z : Finset ℂ} {K : Set ℂ} (hK : IsCompact K) (hZK : ∀ ρ ∈ Z, ρ ∈ K)
    (hZ0 : ∀ ρ ∈ Z, LFunction χ ρ = 0) :
    efMultTotal χ Z ≤ ((∑ᶠ u, divisor (LFunction χ) K u : ℤ) : ℝ) := by
  classical
  have hana : AnalyticOnNhd ℂ (LFunction χ) univ :=
    (differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ
  have hanaK : AnalyticOnNhd ℂ (LFunction χ) K := hana.mono (subset_univ _)
  have hfin : (Function.support fun u => divisor (LFunction χ) K u).Finite :=
    (divisor (LFunction χ) K).finiteSupport hK
  have hdiv_eq : ∀ ρ ∈ K, divisor (LFunction χ) K ρ = (zeroMult χ ρ : ℤ) := by
    intro ρ hρ
    rw [hanaK.divisor_apply hρ, analyticOrderAt_LFunction_eq hχ1 ρ]
    simp
  have hnn : ∀ u : ℂ, 0 ≤ divisor (LFunction χ) K u := by
    intro u; simpa using hanaK.divisor_nonneg u
  have hZsub : Z ⊆ hfin.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset, Function.mem_support, hdiv_eq ρ (hZK ρ hρ)]
    exact_mod_cast Nat.one_le_iff_ne_zero.mp (one_le_zeroMult hχ1 (hZ0 ρ hρ))
  have hsum : (∑ᶠ u, divisor (LFunction χ) K u)
      = ∑ u ∈ hfin.toFinset, divisor (LFunction χ) K u :=
    finsum_eq_finsetSum_of_support_subset _ (by simp)
  have hstep : (∑ ρ ∈ Z, (zeroMult χ ρ : ℤ))
      ≤ ∑ u ∈ hfin.toFinset, divisor (LFunction χ) K u := by
    calc (∑ ρ ∈ Z, (zeroMult χ ρ : ℤ)) = ∑ ρ ∈ Z, divisor (LFunction χ) K ρ :=
          Finset.sum_congr rfl (fun ρ hρ => (hdiv_eq ρ (hZK ρ hρ)).symm)
      _ ≤ ∑ u ∈ hfin.toFinset, divisor (LFunction χ) K u :=
          Finset.sum_le_sum_of_subset_of_nonneg hZsub (fun i _ _ => hnn i)
  rw [efMultTotal, hsum]
  have hcast : (∑ ρ ∈ Z, (zeroMult χ ρ : ℝ)) = ((∑ ρ ∈ Z, (zeroMult χ ρ : ℤ) : ℤ) : ℝ) := by
    push_cast; ring
  rw [hcast]
  exact_mod_cast hstep

/-- **THE DISPOSITION, in the kernel.** Wave 1's half-box supply `LFunction_halfbox_zero_count`
bounds the total multiplicity of the zeros in a unit window, not merely their number:

    ∑_{ρ ∈ Z} m_ρ ≤ (7/log(39/37))·log(q(|t₀|+2))   for `Z` ⊆ closedBall (2+it₀) (37/20)`.

Hence the weighted de-smoothing's `efMultTotal` term is priced by the *same* landed lemma that
would have priced wave 1's `#Z`, and the multiplicity re-base costs the campaign **no new
counting input** — A3's batching consumes this. -/
lemma efMultTotal_halfbox_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (t₀ : ℝ) {Z : Finset ℂ}
    (hZK : ∀ ρ ∈ Z, ρ ∈ Metric.closedBall (2 + (t₀ : ℂ) * I) (37 / 20))
    (hZ0 : ∀ ρ ∈ Z, LFunction χ ρ = 0) :
    efMultTotal χ Z ≤ (7 / Real.log (39 / 37)) * Real.log ((q : ℝ) * (|t₀| + 2)) :=
  le_trans
    (efMultTotal_le_divisor (ne_one_of_isPrimitive χ hχ hq) (isCompact_closedBall _ _) hZK hZ0)
    (LFunction_halfbox_zero_count χ hχ hq t₀)

/-- **The plain cardinality is under the weighted count** — every zero carries `m_ρ ≥ 1`, so any
bound on `efMultTotal` is a bound on `#Z`. The bridge the N4B-W0.5 pigeonhole crosses: the landed
supplies count *with multiplicity*, the midpoint argument needs only the number of obstructions. -/
lemma card_le_efMultTotal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    {Z : Finset ℂ} (hZ0 : ∀ ρ ∈ Z, LFunction χ ρ = 0) :
    (Z.card : ℝ) ≤ efMultTotal χ Z := by
  rw [efMultTotal]
  calc (Z.card : ℝ) = ∑ _ρ ∈ Z, (1 : ℝ) := by simp
    _ ≤ ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) :=
        Finset.sum_le_sum fun ρ hρ => by
          exact_mod_cast one_le_zeroMult hχ1 (hZ0 ρ hρ)

/-! ## 7. THE UN-COLLAPSED VARIANTS — the per-zero shapes N4b's EF socket consumes

§4's de-smoothing and §5's capstone both end by *collapsing* the per-zero spend
`∑_ρ m_ρ·h·y^{Re ρ−1}` into `efMultTotal χ Z · h · y^{σ−1}` at the sup exponent. That collapse
is exactly what makes `psi_explicit_sharpM` vacuous at the N4b operating point: the collapsed
count is `T`-free and `h`-free, so no choice of `(T,h)` makes the de-smoothing term small. The
variants below stop one `Finset.sum_le_sum` earlier, keeping the `1/‖ρ‖`- and `y^{Re ρ}`-graded
per-zero weights that A3's harmonic batching (`Salt.SW.efMultHarmonic_box_le`) then prices.
Everything here is **additive**: the collapsed forms of §4/§5 are untouched. -/

/-- **The de-smoothing, UN-COLLAPSED (N4b W0-vi).** `efRieszSumM_diff_sub_efZeroSumM_le` with
its final `Finset.sum_le_sum` removed:

    ‖h^{−1}(𝓡_M(y+h) − 𝓡_M(y)) − Σ_M(y)‖ ≤ ∑_{ρ ∈ Z} m_ρ·h·y^{Re ρ−1}.

The per-zero estimate is the same landed `cpow_riesz_residue_desmooth`; only the sup-exponent
collapse `y^{Re ρ−1} ≤ y^{σ−1}` is not taken. -/
theorem efRieszSumM_diff_sub_efZeroSumM_le_perZero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {Z : Finset ℂ} {σ : ℝ} (hσ : σ ≤ 1)
    (hZ : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re ≤ σ) {y h : ℝ} (hy : 1 ≤ y) (hh : 0 < h) :
    ‖(efRieszSumM χ Z (y + h) - efRieszSumM χ Z y) / (h : ℂ) - efZeroSumM χ Z y‖
      ≤ ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) * (h * y ^ (ρ.re - 1)) := by
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set D : ℂ → ℂ := fun ρ => (zeroMult χ ρ : ℂ) *
    (((y + h : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))
      - ((y : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) - (h : ℂ) * (((y : ℝ) : ℂ) ^ ρ / ρ)) with hD
  have hDsum : ∑ ρ ∈ Z, D ρ
      = (efRieszSumM χ Z (y + h) - efRieszSumM χ Z y) - (h : ℂ) * efZeroSumM χ Z y := by
    simp only [hD, efRieszSumM, efZeroSumM, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun ρ _ => by ring)
  have hid : (efRieszSumM χ Z (y + h) - efRieszSumM χ Z y) / (h : ℂ) - efZeroSumM χ Z y
      = (∑ ρ ∈ Z, D ρ) / (h : ℂ) := by
    rw [hDsum]; field_simp
  have hterm : ∀ ρ ∈ Z, ‖D ρ‖ ≤ (zeroMult χ ρ : ℝ) * (h ^ 2 * y ^ (ρ.re - 1)) := by
    intro ρ hρ
    obtain ⟨hρ0, hρσ⟩ := hZ ρ hρ
    have hbase := cpow_riesz_residue_desmooth hρ0 (le_trans hρσ hσ) hy hh
    rw [hD]
    simp only [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hbase (by positivity)
  have hsum : ‖∑ ρ ∈ Z, D ρ‖ ≤ ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) * (h ^ 2 * y ^ (ρ.re - 1)) :=
    le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
  rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, div_le_iff₀ hh]
  calc ‖∑ ρ ∈ Z, D ρ‖ ≤ ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) * (h ^ 2 * y ^ (ρ.re - 1)) := hsum
    _ = (∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) * (h * y ^ (ρ.re - 1))) * h := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun ρ _ => by ring)

/-- **The weighted capstone, UN-COLLAPSED (N4b W0-vi).** `psi_explicit_sharpM_of_riesz_residues`
carrying the per-zero de-smoothing spend. -/
theorem psi_explicit_sharpM_of_riesz_residues_perZero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {Z : Finset ℂ} {σ : ℝ} (hσ : σ ≤ 1)
    (hZ : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re ≤ σ) {y h : ℝ} (hy : 1 ≤ y) (hh : 0 < h) {E₁ E₂ : ℝ}
    (h₁ : ‖psi1Chi y χ + efRieszSumM χ Z y‖ ≤ E₁)
    (h₂ : ‖psi1Chi (y + h) χ + efRieszSumM χ Z (y + h)‖ ≤ E₂) :
    ‖psiChiR y χ + efZeroSumM χ Z y‖
      ≤ (h + 1) * Real.log (y + h) + (E₁ + E₂) / h
        + ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) * (h * y ^ (ρ.re - 1)) := by
  have hsock := psi_sharp_of_riesz_bounds (A₁ := -efRieszSumM χ Z y)
    (A₂ := -efRieszSumM χ Z (y + h)) hy hh χ (by simpa using h₁) (by simpa using h₂)
  have hdes := efRieszSumM_diff_sub_efZeroSumM_le_perZero χ hσ hZ hy hh
  have hsplit : psiChiR y χ + efZeroSumM χ Z y
      = (psiChiR y χ - (-efRieszSumM χ Z (y + h) - -efRieszSumM χ Z y) / (h : ℂ))
        - ((efRieszSumM χ Z (y + h) - efRieszSumM χ Z y) / (h : ℂ) - efZeroSumM χ Z y) := by
    field_simp
    ring
  rw [hsplit]
  calc ‖(psiChiR y χ - (-efRieszSumM χ Z (y + h) - -efRieszSumM χ Z y) / (h : ℂ))
        - ((efRieszSumM χ Z (y + h) - efRieszSumM χ Z y) / (h : ℂ) - efZeroSumM χ Z y)‖
      ≤ ‖psiChiR y χ - (-efRieszSumM χ Z (y + h) - -efRieszSumM χ Z y) / (h : ℂ)‖
        + ‖(efRieszSumM χ Z (y + h) - efRieszSumM χ Z y) / (h : ℂ) - efZeroSumM χ Z y‖ :=
        norm_sub_le _ _
    _ ≤ ((h + 1) * Real.log (y + h) + (E₁ + E₂) / h)
          + ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) * (h * y ^ (ρ.re - 1)) := add_le_add hsock hdes
    _ = (h + 1) * Real.log (y + h) + (E₁ + E₂) / h
          + ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) * (h * y ^ (ρ.re - 1)) := by ring

/-- **THE SHARP EXPLICIT FORMULA, UN-COLLAPSED (N4b W0-vi).** `psi_explicit_sharpM` with its
de-smoothing term left per-zero:

    ‖ψ(y,χ) + ∑_{ρ ∈ boxZeros} m_ρ·y^ρ/ρ‖
      ≤ (h+1)·log(y+h) + (E(y) + E(y+h))/h + ∑_{ρ ∈ boxZeros} m_ρ·h·y^{Re ρ−1}.

Hypotheses identical to `psi_explicit_sharpM`'s; only the last summand differs. -/
theorem psi_explicit_sharpM_perZero {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {y h T σ₀ w : ℝ}
    (hy : 3 ≤ y) (hh : 0 < h) (hT : 2 ≤ T) (hw : 0 < w)
    (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1)
    (hsep : ∀ ρ ∈ boxZeros χ (σ₀ - w) 1 (T + 2), σ₀ + w ≤ ρ.re ∧ |ρ.im| + w ≤ T) :
    ‖psiChiR y χ + efZeroSumM χ (boxZeros χ (σ₀ - w) 1 (T + 2)) y‖
      ≤ (h + 1) * Real.log (y + h)
        + (efShiftError f T σ₀ w y + efShiftError f T σ₀ w (y + h)) / h
        + ∑ ρ ∈ boxZeros χ (σ₀ - w) 1 (T + 2), (zeroMult χ ρ : ℝ) * (h * y ^ (ρ.re - 1)) := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  set Z : Finset ℂ := boxZeros χ (σ₀ - w) 1 (T + 2) with hZ
  have hZall : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 → ρ ∈ Z :=
    fun ρ h1 h2 h3 h4 => by rw [hZ, mem_boxZeros hχ1]; exact ⟨h1, h2, h3, h4⟩
  have hZzero : ∀ ρ ∈ Z, LFunction χ ρ = 0 := by
    intro ρ hρ
    rw [hZ, mem_boxZeros hχ1] at hρ
    exact hρ.1
  have hZbox : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re ≤ 1 := by
    intro ρ hρ
    rw [hZ, mem_boxZeros hχ1] at hρ
    exact ⟨by linarith [hρ.2.1], hρ.2.2.1⟩
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hyh : (3 : ℝ) ≤ y + h := by linarith
  have h₁ := psi1_contour_shift_finsetM χ hχ hf hy hT hw hσ₀w hσ₀1 hsep hZzero hZall
  have h₂ := psi1_contour_shift_finsetM χ hχ hf hyh hT hw hσ₀w hσ₀1 hsep hZzero hZall
  exact psi_explicit_sharpM_of_riesz_residues_perZero (σ := 1) χ le_rfl hZbox hy1 hh h₁ h₂

/-- **The Riesz residue's first difference, per zero (N4b W0-vii).** For `0 < Re ρ`, `y ≥ 1`,
`h > 0`,

    ‖(y+h)^{ρ+1}/(ρ(ρ+1)) − y^{ρ+1}/(ρ(ρ+1))‖ ≤ h·(y+h)^{Re ρ}/‖ρ‖.

Route: the *elementary* mean-value bound (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`)
on `φ(u) = u^{ρ+1}/(ρ(ρ+1))`, whose derivative is `u^ρ/ρ` with norm `u^{Re ρ}/‖ρ‖ ≤
(y+h)^{Re ρ}/‖ρ‖` throughout `[y, y+h]` — the same route `cpow_riesz_residue_desmooth` takes,
and it delivers exactly the grade the `∫_y^{y+h}(ρ+1)t^ρ dt` identity would (the identity is not
needed: the segment sup of `‖t^ρ‖` is what both routes spend). -/
theorem cpow_riesz_diff_norm_le {ρ : ℂ} (hρ0 : 0 < ρ.re) {y h : ℝ} (hy : 1 ≤ y) (hh : 0 < h) :
    ‖((y + h : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) - ((y : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖
      ≤ h * ((y + h) ^ ρ.re / ‖ρ‖) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hρne : ρ ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hρ1ne : ρ + 1 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hρnorm : (0 : ℝ) < ‖ρ‖ := norm_pos_iff.mpr hρne
  set S : Set ℝ := Set.Icc y (y + h) with hSdef
  have hconv : Convex ℝ S := convex_Icc _ _
  set φ : ℝ → ℂ := fun u => (u : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) with hφ
  have hderiv : ∀ u ∈ S, HasDerivWithinAt φ ((u : ℂ) ^ ρ / ρ) S u := by
    intro u hu
    rw [hSdef, Set.mem_Icc] at hu
    have hu0 : u ≠ 0 := by have : (0 : ℝ) < u := lt_of_lt_of_le hy0 hu.1; linarith
    have h1 : HasDerivAt (fun v : ℝ => (v : ℂ) ^ (ρ + 1)) ((ρ + 1) * (u : ℂ) ^ (ρ + 1 - 1)) u :=
      hasDerivAt_ofReal_cpow_const hu0 hρ1ne
    have h3 : HasDerivAt φ ((ρ + 1) * (u : ℂ) ^ (ρ + 1 - 1) / (ρ * (ρ + 1))) u := h1.div_const _
    have heq : (ρ + 1) * (u : ℂ) ^ (ρ + 1 - 1) / (ρ * (ρ + 1)) = (u : ℂ) ^ ρ / ρ := by
      rw [show ρ + 1 - 1 = ρ from by ring]
      field_simp
    rw [heq] at h3
    exact h3.hasDerivWithinAt
  have hbound : ∀ u ∈ S, ‖(u : ℂ) ^ ρ / ρ‖ ≤ (y + h) ^ ρ.re / ‖ρ‖ := by
    intro u hu
    rw [hSdef, Set.mem_Icc] at hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hy0 hu.1
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow hu0.le hu.2 hρ0.le) hρnorm.le
  have hyS : y ∈ S := by rw [hSdef, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
  have hyhS : y + h ∈ S := by rw [hSdef, Set.mem_Icc]; exact ⟨by linarith, le_refl _⟩
  have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hyS hyhS
  refine le_trans hmvt (le_of_eq ?_)
  rw [Real.norm_eq_abs, show y + h - y = h from by ring, abs_of_pos hh]
  ring

/-- **THE DIRECT `𝓡_M` DIFFERENCE-QUOTIENT BOUND (N4b W0-vii).** Summing
`cpow_riesz_diff_norm_le` with multiplicities, at a uniform real-part ceiling `β̄`:

    ‖𝓡_M(y+h) − 𝓡_M(y)‖ ≤ (y+h)^{β̄}·h·∑_{ρ ∈ Z} m_ρ/‖ρ‖.

The right factor is exactly A3's harmonic weight (`Salt.SW.efMultHarmonic_box_le`), so this is
the term the N4b EF socket prices at `log(qT)·log T` grade — **no** collapsed, `T`-free count
appears. -/
theorem efRieszSumM_diff_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {Z : Finset ℂ}
    {y h β : ℝ} (hy : 1 ≤ y) (hh : 0 < h) (hZ : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re ≤ β) :
    ‖efRieszSumM χ Z (y + h) - efRieszSumM χ Z y‖
      ≤ (y + h) ^ β * (h * ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) / ‖ρ‖) := by
  have hyh1 : (1 : ℝ) ≤ y + h := by linarith
  have hdiff : efRieszSumM χ Z (y + h) - efRieszSumM χ Z y
      = ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) *
          (((y + h : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))
            - ((y : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))) := by
    simp only [efRieszSumM, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun ρ _ => by ring)
  have hrhs : (y + h) ^ β * (h * ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) / ‖ρ‖)
      = ∑ ρ ∈ Z, (y + h) ^ β * (h * ((zeroMult χ ρ : ℝ) / ‖ρ‖)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hdiff, hrhs]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun ρ hρ => ?_)
  obtain ⟨hρ0, hρβ⟩ := hZ ρ hρ
  have hρnorm : (0 : ℝ) < ‖ρ‖ := by
    refine norm_pos_iff.mpr ?_
    intro h0; rw [h0, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hbase := cpow_riesz_diff_norm_le (ρ := ρ) hρ0 hy hh
  have hmono : (y + h) ^ ρ.re ≤ (y + h) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hyh1 hρβ
  rw [norm_mul, Complex.norm_natCast]
  calc (zeroMult χ ρ : ℝ) * ‖((y + h : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))
          - ((y : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖
      ≤ (zeroMult χ ρ : ℝ) * (h * ((y + h) ^ ρ.re / ‖ρ‖)) :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ (zeroMult χ ρ : ℝ) * (h * ((y + h) ^ β / ‖ρ‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hmono hρnorm.le) hh.le
    _ = (y + h) ^ β * (h * ((zeroMult χ ρ : ℝ) / ‖ρ‖)) := by ring

/-- The same, as a **difference quotient** — the shape `psi_sharp_of_riesz_bounds` consumes
after the `A_i := −𝓡_M` substitution: `‖(𝓡_M(y+h) − 𝓡_M(y))/h‖ ≤ (y+h)^{β̄}·∑ m_ρ/‖ρ‖`, the
`h` having cancelled. -/
theorem efRieszSumM_diff_quotient_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {Z : Finset ℂ} {y h β : ℝ} (hy : 1 ≤ y) (hh : 0 < h) (hZ : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re ≤ β) :
    ‖(efRieszSumM χ Z (y + h) - efRieszSumM χ Z y) / (h : ℂ)‖
      ≤ (y + h) ^ β * ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) / ‖ρ‖ := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, div_le_iff₀ hh]
  refine le_trans (efRieszSumM_diff_norm_le χ hy hh hZ) (le_of_eq ?_)
  ring

/-! ## 8. THE BOX-EXACT VARIANTS (N4B-W0.5) — the zero sum cut at the contour height

`psi_explicit_sharpM` and its un-collapsed twin enumerate at `boxZeros χ (σ₀−w) 1 (T+2)`: the
*widened* box, forced by the old `hZall`, which demanded a zero-free band of width `2` above the
contour. With the gap socket `psi1_contour_shift_finsetM_gap` the enumeration is **box-exact** —
`Z = boxZeros χ (σ₀−w) 1 T`, the zeros the contour actually encircles — and the residual demand
is the width-`w` band

    hgap : no zero of the strip has `T < |Im ρ| < T + w`,

which is a **pigeonhole conclusion** off the landed counts (`Salt.SW.exists_contour_params`), not
a hypothesis. Downstream this also drops the ceiling base from `q(T+4)` to `q(T+2)`. -/

/-- **THE SHARP EXPLICIT FORMULA, UN-COLLAPSED AND BOX-EXACT (N4B-W0.5).**
`psi_explicit_sharpM_perZero` at `Z = boxZeros χ (σ₀−w) 1 T` — the zeros of the contour box
itself, no `+2` widening:

    ‖ψ(y,χ) + ∑_{ρ ∈ boxZeros …T} m_ρ·y^ρ/ρ‖
      ≤ (h+1)·log(y+h) + (E(y) + E(y+h))/h + ∑_{ρ ∈ boxZeros …T} m_ρ·h·y^{Re ρ−1}.

`hsep` is the old well-spacing (now at the exact box); `hgap` replaces the width-2 zero-free band
by the width-`w` one. Both are discharged together by `Salt.SW.exists_contour_params`. -/
theorem psi_explicit_sharpM_perZero_box {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {y h T σ₀ w : ℝ}
    (hy : 3 ≤ y) (hh : 0 < h) (hT : 2 ≤ T) (hw : 0 < w)
    (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1)
    (hsep : ∀ ρ ∈ boxZeros χ (σ₀ - w) 1 T, σ₀ + w ≤ ρ.re ∧ |ρ.im| + w ≤ T)
    (hgap : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → T < |ρ.im| →
      T + w ≤ |ρ.im|) :
    ‖psiChiR y χ + efZeroSumM χ (boxZeros χ (σ₀ - w) 1 T) y‖
      ≤ (h + 1) * Real.log (y + h)
        + (efShiftError f T σ₀ w y + efShiftError f T σ₀ w (y + h)) / h
        + ∑ ρ ∈ boxZeros χ (σ₀ - w) 1 T, (zeroMult χ ρ : ℝ) * (h * y ^ (ρ.re - 1)) := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  set Z : Finset ℂ := boxZeros χ (σ₀ - w) 1 T with hZ
  have hZall : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 →
      ρ ∈ Z ∨ T + w ≤ |ρ.im| := by
    intro ρ h1 h2 h3 _
    by_cases him : |ρ.im| ≤ T
    · exact Or.inl (by rw [hZ, mem_boxZeros hχ1]; exact ⟨h1, h2, h3, him⟩)
    · exact Or.inr (hgap ρ h1 h2 h3 (not_le.mp him))
  have hZzero : ∀ ρ ∈ Z, LFunction χ ρ = 0 := by
    intro ρ hρ
    rw [hZ, mem_boxZeros hχ1] at hρ
    exact hρ.1
  have hZbox : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re ≤ 1 := by
    intro ρ hρ
    rw [hZ, mem_boxZeros hχ1] at hρ
    exact ⟨by linarith [hρ.2.1], hρ.2.2.1⟩
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hyh : (3 : ℝ) ≤ y + h := by linarith
  have h₁ := psi1_contour_shift_finsetM_gap χ hχ hf hy hT hw hσ₀w hσ₀1 hsep hZzero hZall
  have h₂ := psi1_contour_shift_finsetM_gap χ hχ hf hyh hT hw hσ₀w hσ₀1 hsep hZzero hZall
  exact psi_explicit_sharpM_of_riesz_residues_perZero (σ := 1) χ le_rfl hZbox hy1 hh h₁ h₂

/-- **THE SHARP EXPLICIT FORMULA, BOX-EXACT (N4B-W0.5).** `psi_explicit_sharpM` with the
enumeration cut at the contour height `T` rather than `T+2`, at the width-`w` gap hypothesis.
The collapsed de-smoothing spend `efMultTotal · h` is unchanged in shape; only the enumerated set
shrinks. -/
theorem psi_explicit_sharpM_box {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {y h T σ₀ w : ℝ}
    (hy : 3 ≤ y) (hh : 0 < h) (hT : 2 ≤ T) (hw : 0 < w)
    (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1)
    (hsep : ∀ ρ ∈ boxZeros χ (σ₀ - w) 1 T, σ₀ + w ≤ ρ.re ∧ |ρ.im| + w ≤ T)
    (hgap : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → T < |ρ.im| →
      T + w ≤ |ρ.im|) :
    ‖psiChiR y χ + efZeroSumM χ (boxZeros χ (σ₀ - w) 1 T) y‖
      ≤ (h + 1) * Real.log (y + h)
        + (efShiftError f T σ₀ w y + efShiftError f T σ₀ w (y + h)) / h
        + efMultTotal χ (boxZeros χ (σ₀ - w) 1 T) * h := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  set Z : Finset ℂ := boxZeros χ (σ₀ - w) 1 T with hZ
  have hZall : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 →
      ρ ∈ Z ∨ T + w ≤ |ρ.im| := by
    intro ρ h1 h2 h3 _
    by_cases him : |ρ.im| ≤ T
    · exact Or.inl (by rw [hZ, mem_boxZeros hχ1]; exact ⟨h1, h2, h3, him⟩)
    · exact Or.inr (hgap ρ h1 h2 h3 (not_le.mp him))
  have hZzero : ∀ ρ ∈ Z, LFunction χ ρ = 0 := by
    intro ρ hρ
    rw [hZ, mem_boxZeros hχ1] at hρ
    exact hρ.1
  have hZbox : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re ≤ 1 := by
    intro ρ hρ
    rw [hZ, mem_boxZeros hχ1] at hρ
    exact ⟨by linarith [hρ.2.1], hρ.2.2.1⟩
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hyh : (3 : ℝ) ≤ y + h := by linarith
  have h₁ := psi1_contour_shift_finsetM_gap χ hχ hf hy hT hw hσ₀w hσ₀1 hsep hZzero hZall
  have h₂ := psi1_contour_shift_finsetM_gap χ hχ hf hyh hT hw hσ₀w hσ₀1 hsep hZzero hZall
  have hmain := psi_explicit_sharpM_of_riesz_residues (σ := 1) χ le_rfl hZbox hy1 hh h₁ h₂
  have hrw : y ^ ((1 : ℝ) - 1) = 1 := by
    rw [show (1 : ℝ) - 1 = 0 by ring, Real.rpow_zero]
  rw [hrw, mul_one] at hmain
  exact hmain

end Salt.SW
