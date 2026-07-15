/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.Peeling

/-!
⚠ 58c DEPRECATION NOTE (2026-07-15, from the H4C disposition): the abstract-σ `h4` rows in
this file (`∀ s' …, Vlow ≤ (3K/σ)·W`-shaped) are landed TRUE theorems whose hypothesis
bundles `{hσ1, hσ3, h4}` are jointly uninstantiable at σ = logRatio (catch #66's genre —
via hσ3 alone).  They are OFF the headline's dependency path: the live chain routes through
the H4C-CONDITIONED slots (WindowedStep/P/C + H4Cond.h4_cond_of_base).  Kept as landed
mathematics; do not build new consumers on the abstract-σ rows.
-/
/-!
# C1c⁵ — discharging `hbase`, the `hBJS` functional integral bound, and the τ interface

This file supplies the pieces C1c⁗ (`Peeling.lean`) named as the two remaining named
hypotheses of the Buchstab induction skeleton — the base bound `hbase` (BJS (39)) and the
analytic ingredient (the `hBJS` self-integral bound) that a future `hstep` (BJS (34)–(38))
consumes.

## What is proved (sorry-free, axiom-clean)

* **The `hBJS` functional integral bound** (`hBJS_funcbound`): for `s ≥ 2` and any upper
  limit `c`, `∫_{s-1}^c h(u) du ≤ s·h(s)` — the `κ = 1` analogue of Tail's `hbar_funcbound`,
  proved region-by-region against the elementary exponential majorant `h(u) ≤ e^{-u}`
  (`u ≥ 2`) with the tight `[2,3]` panel closed by the Padé upper bound
  `(2-x)eˣ ≤ 2+x` (`exp_pade_upper`).  This is BJS's `H(s) ≤ κ₃·s·h(s)` (their (24)/(26)),
  the ingredient the (35)–(38) `h`-slack ledger of `hstep` integrates.

  **FINDING (κ = 1 is the elementary floor; the frozen τ-close needs κ₃ < 1).**  The
  constant `κ = 1` is *tight at `s = 2`* (equality: `∫_1^∞ h = 2·h(2)` for the majorant),
  and it is the best an *elementary* majorant yields — the true `∫_1^∞ h ≈ 0.26 < 2e^{-2}`
  requires the `3u⁻¹e^{-u}` tail's exponential integral `E₁`, which is not elementary in
  mathlib.  Since BJS's τ-recursion contracts only with `β = Kκ₃ + (K−1)γ₃ < 1`, and `κ = 1`
  gives `β ≥ 1`, the numeric frozen row `C₁ = 106, C₂ = 108` is **NOT** reproducible from
  elementary `hBJS` constants; it stays the named `htau` hypothesis (C0-ledger doctrine).
  See `docs/blueprints/flags.md`.

* **The base bound `hbase`** (`hbase_of`, both sides FULL): the depth-1 slot of
  `Peeling.hmain_upper_of_step` / `hmain_lower_of_step`, discharged from the primitive
  inputs — hypothesis (4) in the base V-ratio form (`h4`, `Vlow ≤ (3K/s)W`), the σ-window
  `σ ∈ [1,3]`, and `τ₁ = 3`.  Upper side is `Lemma11.hlevel_one_upper`; the even/lower side
  is `T s 2 D 1 = 0` (`T_two_one_zero`) against a nonnegative bound.

* **The payoff** (`bjs_theorem6_upper` / `bjs_theorem6_lower`, and the `_sifted` forms):
  `Peeling.hmain_*_of_step` with `hbase` discharged, leaving only the per-step comparison
  `hstep` (BJS (34)–(38), still a named hypothesis — see the flag on the σ/z architecture),
  the parametric τ-close `htau`, and the hypothesis-(4) family.

## The deferred piece (precise flag in `docs/blueprints/flags.md`)

`hstep` — the discrete-to-integral partial summation (BJS (35)–(38)) — remains the one named
hypothesis.  The obstruction is architectural: `Peeling`'s `σ : BoundingSieve → ℕ → ℝ`
cannot recover the sub-sieve's cutoff `p` from `sieveBelow s p` (whose `prodPrimes = ∏_{q<p} q`
forgets `p`), so the change of variables `t = log D/log p ↦ s'_p = t − 1` that turns the
`p`-sum into the `fseq` recursion integral cannot be stated through `σ` alone.  See the flag.
-/

open Finset MeasureTheory intervalIntegral Set

namespace Salt.Chen

/-! ## Part A — the `hBJS` functional integral bound `∫_{s-1}^c h ≤ s·h(s)` (κ = 1) -/

/-- `h(u) = e^{-2}` on `u ≤ 2`. -/
theorem hBJS_le2 {u : ℝ} (h : u ≤ 2) : hBJS u = Real.exp (-2) := by
  unfold hBJS; rw [if_pos h]

/-- `h(s) = e^{-s}` on the middle window `[2,3]`. -/
theorem hBJS_mid {s : ℝ} (h2 : 2 ≤ s) (h3 : s ≤ 3) : hBJS s = Real.exp (-s) := by
  rcases eq_or_lt_of_le h2 with rfl | h2'
  · rw [hBJS_le2 le_rfl]
  · unfold hBJS; rw [if_neg (by linarith), if_pos h3]

/-- `h(s) = 3·s⁻¹·e^{-s}` on the tail `s ≥ 3` (the second and third branches agree at 3). -/
theorem hBJS_ge3 {s : ℝ} (h3 : 3 ≤ s) : hBJS s = 3 * s⁻¹ * Real.exp (-s) := by
  unfold hBJS
  rcases eq_or_lt_of_le h3 with rfl | h3'
  · rw [if_neg (by norm_num), if_pos le_rfl]; norm_num
  · rw [if_neg (by linarith), if_neg (by linarith)]

/-- `h(u) ≤ e^{-u}` for `u ≥ 2` (the elementary exponential majorant). -/
theorem hBJS_le_exp_of_ge {u : ℝ} (h : 2 ≤ u) : hBJS u ≤ Real.exp (-u) := by
  rcases le_total u 3 with h3 | h3
  · rw [hBJS_mid h h3]
  · rw [hBJS_ge3 h3]
    have hu0 : 0 < u := by linarith
    have h1 : 3 * u⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hu0]; linarith
    calc 3 * u⁻¹ * Real.exp (-u) ≤ 1 * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-u) := one_mul _

/-- `h(u) ≤ e^{-2}` globally (all three branches are `≤ e^{-2}`). -/
theorem hBJS_le_exp2 (u : ℝ) : hBJS u ≤ Real.exp (-2) := by
  rcases le_total u 2 with h2 | h2
  · rw [hBJS_le2 h2]
  · exact (hBJS_le_exp_of_ge h2).trans (Real.exp_le_exp.mpr (by linarith))

theorem hBJS_measurable : Measurable hBJS := by
  unfold hBJS
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_le measurable_id measurable_const)
    (Real.measurable_exp.comp measurable_neg) ?_
  exact (measurable_const.mul measurable_inv).mul (Real.measurable_exp.comp measurable_neg)

/-- `h` is interval integrable on every interval (measurable and globally bounded by `e^{-2}`). -/
theorem hBJS_intervalIntegrable (a b : ℝ) : IntervalIntegrable hBJS volume a b := by
  rw [intervalIntegrable_iff]
  apply MeasureTheory.Measure.integrableOn_of_bounded (M := Real.exp (-2)) _
    hBJS_measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs, abs_of_pos (hBJS_pos s)]; exact hBJS_le_exp2 s))
  rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top

/-- `∫_a^c e^{-u} du = e^{-a} − e^{-c}`. -/
theorem integral_exp_neg (a c : ℝ) :
    ∫ u in a..c, Real.exp (-u) = Real.exp (-a) - Real.exp (-c) := by
  have hderiv : ∀ u ∈ uIcc a c, HasDerivAt (fun x => -Real.exp (-x)) (Real.exp (-u)) u := by
    intro u _
    have h0 : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) u := (hasDerivAt_id u).neg
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-u) * (-1)) u :=
      (Real.hasDerivAt_exp (-u)).comp u h0
    have h2 : HasDerivAt (fun x : ℝ => -Real.exp (-x)) (-(Real.exp (-u) * (-1))) u := h1.neg
    simpa using h2
  rw [integral_eq_sub_of_hasDerivAt hderiv
    ((Real.continuous_exp.comp continuous_neg).intervalIntegrable _ _)]
  ring

/-- For `a ≥ 2` (inside the decay branch), `∫_a^c h ≤ e^{-a}`. -/
theorem hBJS_intbound_hi (a c : ℝ) (ha : 2 ≤ a) : (∫ u in a..c, hBJS u) ≤ Real.exp (-a) := by
  rcases le_total a c with hac | hac
  · have hmono : (∫ u in a..c, hBJS u) ≤ ∫ u in a..c, Real.exp (-u) := by
      apply integral_mono_on hac (hBJS_intervalIntegrable a c)
        ((Real.continuous_exp.comp continuous_neg).intervalIntegrable a c)
      intro u hu
      exact hBJS_le_exp_of_ge (le_trans ha hu.1)
    calc (∫ u in a..c, hBJS u) ≤ ∫ u in a..c, Real.exp (-u) := hmono
      _ = Real.exp (-a) - Real.exp (-c) := integral_exp_neg a c
      _ ≤ Real.exp (-a) := by linarith [Real.exp_pos (-c)]
  · rw [intervalIntegral.integral_symm]
    have h1 : 0 ≤ ∫ u in c..a, hBJS u := integral_nonneg hac (fun u _ => (hBJS_pos u).le)
    linarith [Real.exp_pos (-a)]

/-- For `a ≤ 2` (crossing the junction), `∫_a^c h ≤ e^{-2}·(3 − a)`. -/
theorem hBJS_intbound_cross (a c : ℝ) (ha : a ≤ 2) :
    (∫ u in a..c, hBJS u) ≤ Real.exp (-2) * (3 - a) := by
  have hsplit : (∫ u in a..c, hBJS u)
      = (∫ u in a..(2:ℝ), hBJS u) + ∫ u in (2:ℝ)..c, hBJS u :=
    (integral_add_adjacent_intervals (hBJS_intervalIntegrable a 2)
      (hBJS_intervalIntegrable 2 c)).symm
  rw [hsplit]
  have hflat : (∫ u in a..(2:ℝ), hBJS u) = Real.exp (-2) * (2 - a) := by
    have hcongr : (∫ u in a..(2:ℝ), hBJS u) = ∫ _u in a..(2:ℝ), Real.exp (-2) := by
      apply integral_congr
      intro u hu
      rw [uIcc_of_le ha] at hu
      exact hBJS_le2 hu.2
    rw [hcongr, intervalIntegral.integral_const]; simp; ring
  rw [hflat]
  have hhi : (∫ u in (2:ℝ)..c, hBJS u) ≤ Real.exp (-2) := hBJS_intbound_hi 2 c le_rfl
  have hrw : Real.exp (-2) * (3 - a) = Real.exp (-2) * (2 - a) + Real.exp (-2) := by ring
  rw [hrw]; linarith [hhi]

/-- **The Padé upper bound** `(2 − x)·eˣ ≤ 2 + x` on `[0,1]` (the tight `[2,3]` panel of
`hBJS_funcbound`).  From `Real.exp_bound` at `n = 4`: `eˣ ≤ 1+x+x²/2+x³/6 + 5x⁴/96`, then
`(2−x)·(that) − (2+x) = −x³/6 − x⁴/16 ≤ 0`. -/
theorem exp_pade_upper {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (2 - x) * Real.exp x ≤ 2 + x := by
  have h := Real.exp_bound (x := x) (by rw [abs_le]; constructor <;> linarith) (n := 4)
    (by norm_num)
  rw [abs_le] at h
  have h2 := h.2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  rw [abs_of_nonneg hx0] at h2
  norm_num at h2
  nlinarith [h2, Real.exp_pos x, pow_nonneg hx0 3, pow_nonneg hx0 4, hx0, hx1,
    mul_nonneg hx0 hx0, mul_nonneg (mul_nonneg hx0 hx0) hx0]

/-- **The `hBJS` functional integral bound** (BJS `H(s) ≤ κ₃·s·h(s)`, at the elementary
`κ₃ = 1`).  For `s ≥ 2` and any upper limit `c`, `∫_{s-1}^c h(u) du ≤ s·h(s)`.  Region-split:
the tail `s ≥ 3` uses `∫ ≤ e^{-(s-1)} = e·e^{-s} ≤ 3e^{-s} = s·h(s)`; the band `2 ≤ s ≤ 3`
uses the crossing bound `e^{-2}(4−s)` and the Padé panel `(4−s)e^{s-2} ≤ s`. -/
theorem hBJS_funcbound (s c : ℝ) (hs : 2 ≤ s) : (∫ u in (s - 1)..c, hBJS u) ≤ s * hBJS s := by
  rcases le_total s 3 with h3 | h3
  · -- 2 ≤ s ≤ 3
    have hcross := hBJS_intbound_cross (s - 1) c (by linarith)
    rw [hBJS_mid hs h3]
    have hconv : (4 - s) * Real.exp (s - 2) ≤ s := by
      have hp := exp_pade_upper (x := s - 2) (by linarith) (by linarith)
      have e1 : (2 - (s - 2)) = 4 - s := by ring
      have e2 : 2 + (s - 2) = s := by ring
      rw [e1, e2] at hp; exact hp
    have hkey : Real.exp (-2) * (4 - s) ≤ s * Real.exp (-s) := by
      have hexpid : Real.exp (-2) = Real.exp (s - 2) * Real.exp (-s) := by
        rw [← Real.exp_add]; congr 1; ring
      have hid : Real.exp (-2) * (4 - s) = (4 - s) * Real.exp (s - 2) * Real.exp (-s) := by
        rw [hexpid]; ring
      rw [hid]
      exact mul_le_mul_of_nonneg_right hconv (Real.exp_pos _).le
    calc (∫ u in (s - 1)..c, hBJS u) ≤ Real.exp (-2) * (3 - (s - 1)) := hcross
      _ = Real.exp (-2) * (4 - s) := by ring
      _ ≤ s * Real.exp (-s) := hkey
  · -- s ≥ 3
    have hhi := hBJS_intbound_hi (s - 1) c (by linarith)
    rw [hBJS_ge3 h3]
    have hs0 : s ≠ 0 := by positivity
    have hval : s * (3 * s⁻¹ * Real.exp (-s)) = 3 * Real.exp (-s) := by
      field_simp
    rw [hval]
    calc (∫ u in (s - 1)..c, hBJS u) ≤ Real.exp (-(s - 1)) := hhi
      _ = Real.exp 1 * Real.exp (-s) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ 3 * Real.exp (-s) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have := Real.exp_one_lt_d9; linarith

/-! ## Part B — the τ-close dischargers (parametric, `htau`-shaped)

BJS Lemma 12 sums the (31) τ-recursion to the finite `Στ_{2n−1} = C₁`, `Στ_{2n} = C₂`
(Table 1: `ε = 1/10000 → C₁ = 106, C₂ = 108`).  `Lemma11.tau_sum_le_of_recursion` closes the
*full* partial sum for a contracting geometric recursion `τₙ₊₁ ≤ a·rⁿ + β·τₙ`; here we drop
that onto the odd/even filters `hmain_*_of_step`'s `htau` uses (each sub-sum is `≤` the full
sum, `τ ≥ 0`).

**FINDING (the contraction does not close at elementary constants).**  BJS's `β = Kκ₃ + (K−1)γ₃`
contracts (`β < 1`) only because `κ₃ < 1` in their `H(s) ≤ κ₃·s·h(s)`.  Our elementary
`hBJS_funcbound` gives `κ₃ = 1` (tight at `s = 2`; the true `κ₃ ≈ 0.96` needs the `E₁`
exponential integral of the `3u⁻¹e^{-u}` tail — not elementary in mathlib), so `β ≥ Kκ₃ ≥ 1`
and no *concrete* contracting τ with BJS's actual `(31)` coefficients is elementarily
derivable.  Hence the numeric `C₁ = 106, C₂ = 108` stay the named `htau` hypotheses; these
dischargers are the parametric tool that instantiates them once BJS's `(31)` constants
(page-image `γ₃, κ₃, cₙ`) are available.  See `docs/blueprints/flags.md`. -/

/-- **`htau` (odd), from a contracting geometric τ-recursion.**  Any τ with `τₙ₊₁ ≤ a·rⁿ + β·τₙ`
(`0 ≤ r,β < 1`, `a,τ ≥ 0`) has odd-filtered partial sums bounded by the same finite `C₁`. -/
theorem tauSum_odd_le (tau : ℕ → ℝ) (a r β : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (ha : 0 ≤ a) (hnn : ∀ n, 0 ≤ tau n)
    (hrec : ∀ n, tau (n + 1) ≤ a * r ^ n + β * tau n) (M : ℕ) :
    ∑ n ∈ (Finset.range M).filter (fun n => Odd n), tau n ≤ (tau 0 + a / (1 - r)) / (1 - β) :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => hnn i))
    (tau_sum_le_of_recursion tau a r β hr0 hr1 hβ0 hβ1 ha hnn hrec M)

/-- **`htau` (even), from a contracting geometric τ-recursion.**  The even-filtered dual. -/
theorem tauSum_even_le (tau : ℕ → ℝ) (a r β : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (ha : 0 ≤ a) (hnn : ∀ n, 0 ≤ tau n)
    (hrec : ∀ n, tau (n + 1) ≤ a * r ^ n + β * tau n) (M : ℕ) :
    ∑ n ∈ (Finset.range M).filter (fun n => Even n), tau n ≤ (tau 0 + a / (1 - r)) / (1 - β) :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => hnn i))
    (tau_sum_le_of_recursion tau a r β hr0 hr1 hβ0 hβ1 ha hnn hrec M)

/-! ## Part C — the base bound `hbase` (BJS (39)), both sides FULL

The depth-1 slot of `Peeling.hmain_*_of_step`, discharged from the primitive inputs:
hypothesis (4) in the base V-ratio form (`h4 : Vlow ≤ (3K/σ)W`, at `u = D^{1/3}`), the
σ-window `σ ∈ [1,3]`, and `τ₁ = 3`.  Upper (odd) side is `Lemma11.hlevel_one_upper`; the
even/lower side is `T s 2 D 1 = 0` (`T_two_one_zero`) against a nonnegative bound. -/

/-- **`hbase`** (BJS (39), both sides).  Discharges the base hypothesis of
`hmain_upper_of_step` / `hmain_lower_of_step` for the `fseqBound σ ε tau` target family, from
the σ-window, hypothesis (4), `0 ≤ ε`, `K ≤ 1+ε`, `τ₁ = 3`. -/
theorem hbase_of (σ : BoundingSieve → ℕ → ℝ) (ε K : ℝ) (tau : ℕ → ℝ)
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3)
    (hσ1 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' → 1 ≤ σ s' D')
    (hσ3 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' → σ s' D' ≤ 3)
    (h4 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / σ s' D') * Salt.BrunLower.W s') :
    ∀ (s' : BoundingSieve) (side' D' : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' →
      T s' side' D' 1 ≤ fseqBound σ ε tau s' side' D' 1 := by
  intro s' side' D' hside hD'
  rcases hside with h1 | h2
  · subst h1
    have h := hlevel_one_upper s' D' (σ s' D') ε K (hσ1 s' D' hD') (hσ3 s' D' hD') hε hKe
      (h4 s' D' hD')
    simp only [fseqBound, htau1]
    exact h
  · subst h2
    rw [T_two_one_zero]
    simp only [fseqBound, htau1]
    have hW := Salt.BrunLower.W_pos s'
    have hnn : 0 ≤ fseq 1 (σ s' D') + ε * 3 * Real.exp 2 * hBJS (σ s' D') := by
      have hf := fseq_nonneg 1 (σ s' D')
      have hh : 0 ≤ ε * 3 * Real.exp 2 * hBJS (σ s' D') :=
        mul_nonneg (mul_nonneg (mul_nonneg hε (by norm_num)) (Real.exp_pos 2).le)
          (hBJS_pos _).le
      linarith
    exact mul_nonneg hW.le hnn

/-! ## Part D — the per-step comparison `hstep` (BJS (34)–(38))  ⚠️ DEFERRED

`hstep` is the discrete-to-integral partial summation, the genuine real-analysis heart.  It
remains the one named hypothesis of the payoff below.  The obstruction is architectural, not
just laborious: `Peeling`'s `σ : BoundingSieve → ℕ → ℝ` cannot recover the sub-sieve cutoff
`p` from `sieveBelow s p` (its `prodPrimes = ∏_{q<p} q` forgets `p`), so BJS's change of
variables `t = log D/log p ↦ s'_p = t − 1`, which turns `Σ_p ν(p)V(p)·fₙ(s'_p)` into the
`fseq` recursion integral `(1/S)∫_S^∞ fₙ(t−1) dt`, is not statable through `σ` alone.  A
future session either threads `p` into the operating-point map (extend `σ`/`hstep`) or carries
`z` explicitly in `T`.  `hBJS_funcbound` (Part A) is the `h`-slack ingredient it will consume.
See `docs/blueprints/flags.md`. -/

/-! ## Part E — the payoff: BJS Theorem 6 (5)/(6), modulo `hstep` + `htau` + hyp (4)

`hmain_*_of_step` with `hbase` discharged (`hbase_of`).  The remaining named hypotheses are the
per-step comparison `hstep`, the parametric τ-close `htau`, and the hypothesis-(4) family
(`h4`, the σ-window). -/

/-- **BJS Theorem 6 (5), main-term form** (upper), with `hbase` discharged. -/
theorem bjs_theorem6_upper (s : BoundingSieve) (D : ℕ) (hD : 1 ≤ D)
    (σ : BoundingSieve → ℕ → ℝ) (ε K C₁ : ℝ) (tau : ℕ → ℝ)
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3)
    (hσ1 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' → 1 ≤ σ s' D')
    (hσ3 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' → σ s' D' ≤ 3)
    (h4 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / σ s' D') * Salt.BrunLower.W s')
    (hstep : ∀ (s' : BoundingSieve) (side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * fseqBound σ ε tau (sieveBelow s' p) (3 - side') (cdiv D' p) n)
          ≤ fseqBound σ ε tau s' side' D' (n + 1))
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), tau n ≤ C₁) :
    s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      ≤ Salt.BrunLower.W s *
        (Fchain (maxDepth s) (σ s D) + ε * C₁ * Real.exp 2 * hBJS (σ s D)) :=
  hmain_upper_of_step s D hD σ ε C₁ tau hε
    (hbase_of σ ε K tau hε hKe htau1 hσ1 hσ3 h4) hstep htau

/-- **BJS Theorem 6 (6), main-term form** (lower), with `hbase` discharged. -/
theorem bjs_theorem6_lower (s : BoundingSieve) (D : ℕ) (hD : 1 ≤ D)
    (σ : BoundingSieve → ℕ → ℝ) (ε K C₂ : ℝ) (tau : ℕ → ℝ)
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau0 : 0 ≤ tau 0) (htau1 : tau 1 = 3)
    (hσ1 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' → 1 ≤ σ s' D')
    (hσ3 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' → σ s' D' ≤ 3)
    (h4 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / σ s' D') * Salt.BrunLower.W s')
    (hstep : ∀ (s' : BoundingSieve) (side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * fseqBound σ ε tau (sieveBelow s' p) (3 - side') (cdiv D' p) n)
          ≤ fseqBound σ ε tau s' side' D' (n + 1))
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), tau n ≤ C₂) :
    Salt.BrunLower.W s * (fchain (maxDepth s) (σ s D) - ε * C₂ * Real.exp 2 * hBJS (σ s D))
      ≤ s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam :=
  hmain_lower_of_step s D hD σ ε C₂ tau hε htau0
    (hbase_of σ ε K tau hε hKe htau1 hσ1 hσ3 h4) hstep htau

/-- **BJS Theorem 6 (5), sifted-sum form** (upper), with `hbase` discharged: the full explicit
upper linear sieve modulo `hstep`, `htau`, and the hypothesis-(4) family. -/
theorem bjs_theorem6_upper_sifted (s : BoundingSieve) (D : ℕ) (hD : 2 ≤ D)
    (htm : 0 ≤ s.totalMass) (σ : BoundingSieve → ℕ → ℝ) (ε K C₁ Q : ℝ) (hQ : 1 ≤ Q)
    (tau : ℕ → ℝ) (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3)
    (hσ1 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' → 1 ≤ σ s' D')
    (hσ3 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' → σ s' D' ≤ 3)
    (h4 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / σ s' D') * Salt.BrunLower.W s')
    (hstep : ∀ (s' : BoundingSieve) (side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * fseqBound σ ε tau (sieveBelow s' p) (3 - side') (cdiv D' p) n)
          ≤ fseqBound σ ε tau s' side' D' (n + 1))
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), tau n ≤ C₁) :
    s.siftedSum
      ≤ s.totalMass * (Salt.BrunLower.W s *
          (Fchain (maxDepth s) (σ s D) + ε * C₁ * Real.exp 2 * hBJS (σ s D)))
        + rosserRemainder s (Q * D) :=
  linear_sieve_upper_rosser_assembled_final s D hD htm (σ s D) ε C₁ Q hQ hε tau
    (hlevel_upper_of_step s D (by omega) σ ε tau
      (hbase_of σ ε K tau hε hKe htau1 hσ1 hσ3 h4) hstep) htau

/-- **BJS Theorem 6 (6), sifted-sum form** (lower), with `hbase` discharged. -/
theorem bjs_theorem6_lower_sifted (s : BoundingSieve) (D z : ℕ) (hz2 : 2 ≤ z) (hzD : z ≤ D)
    (hz : ∀ p ∈ s.prodPrimes.primeFactors, p < z) (htm : 0 ≤ s.totalMass)
    (σ : BoundingSieve → ℕ → ℝ) (ε K C₂ Q : ℝ) (hQ : 1 ≤ Q)
    (tau : ℕ → ℝ) (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau0 : 0 ≤ tau 0) (htau1 : tau 1 = 3)
    (hσ1 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' → 1 ≤ σ s' D')
    (hσ3 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' → σ s' D' ≤ 3)
    (h4 : ∀ (s' : BoundingSieve) (D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / σ s' D') * Salt.BrunLower.W s')
    (hstep : ∀ (s' : BoundingSieve) (side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * fseqBound σ ε tau (sieveBelow s' p) (3 - side') (cdiv D' p) n)
          ≤ fseqBound σ ε tau s' side' D' (n + 1))
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), tau n ≤ C₂) :
    s.totalMass * (Salt.BrunLower.W s *
        (fchain (maxDepth s) (σ s D) - ε * C₂ * Real.exp 2 * hBJS (σ s D)))
      - rosserRemainder s (Q * D) ≤ s.siftedSum :=
  linear_sieve_lower_rosser_assembled_final s D z hz2 hzD hz htm (σ s D) ε C₂ Q hQ hε tau
    (hlevel_lower_of_step s D (by omega) σ ε tau hε htau0
      (hbase_of σ ε K tau hε hKe htau1 hσ1 hσ3 h4) hstep) htau

end Salt.Chen
