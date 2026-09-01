/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey
-/
import Mathlib
import Salt.MR.ZetaPowLower
import Salt.MR.PrimeTail
import Salt.MR.DistHalasz
import Salt.SW.ZetaLowerShallow

/-!
# A4F H3 — FTC and the harmonic-sum assembly, all regimes named

The mid-range route needs two-sided `O(·)` control of the prime harmonic sums
`S(t) = Σ_{Y<p≤X} cos(t·log p)/p`.  This file supplies it, regime by regime:

* the FINSET INDEX IDENTITY (`prime_sum_filter_gt_sub`): `Σ_{Y<p≤X} = Σ_{p≤X} − Σ_{p≤Y}` at
  the `⌊·⌋₊`-indexed sets — a real sub-item, not a footnote;
* the Euler-oscillation bridge (`euler_osc_bridge_unconditional`, landed) converts each side
  to `log‖ζ(1+1/log x + ti)‖` at cost `K`, twice;
* the MIRROR of the landed one-sided FTC bridge (`zeta_near_bridge_lower` below — the same
  `integral_mono_on` argument reversed, on the derivative stone `hasDerivAt_log_norm_zeta`,
  which is cited, never re-derived);
* `2 ≤ |t| ≤ T`: BOTH endpoint logs are absolutely bounded — upper by the bounded-height
  closed form (`log_zeta_small_b_le`), lower by the shallow-strip bound
  (`zeta_lower_shallow`, whose `σ`-hypothesis is free at `σ = 1+1/log x > 1`); the sup over
  a FIXED height range is an absolute constant, so no per-harmonic `log` leaks
  (the no-slack invariant);
* `|t| > T₀`: the landed VK-window bound `zeta_near_logDeriv_bound` through the bridge PAIR
  gives the DIFFERENCE form `(1/log Y)·400·(log|t|)^{3/4}(loglog|t|)^4/cR` — a per-point
  endpoint bound here would inject `logloglog X` per harmonic and is FATAL, which is exactly
  why the FTC difference is used.

**THE REGIME TABLE, complete (classifier-arity: three states, not two).**  In the H4
assembly the top-level branch is on `u`:
* `|u| < 2` — then the `u`-floor `(log X)^{1/16}/2 ≤ |u|` forces `log X < 2^{32}`: a BOUNDED
  `X`-range, and the whole target inequality is absorbed into its constant.  This branch also
  contains the entire `|t| ∈ [1/2, 2)` regime (reachable only through the `u`-floor at small
  `X`; neither small-height stone reaches it) — NAMED here so the classifier is three-state,
  and absorbed top-level, never silently assumed empty.
* `|u| ≥ 2` — every harmonic `t = m·u` (`m ≥ 1`) has `|t| ≥ 2`, and this file's two lemmas
  cover `2 ≤ |t| ≤ T₀` and `T₀ ≤ |t|` (their union is everything the assembly meets).
* `Y > X` (`ε ≥ 1/3` makes `log Y > log X`) — the demand is `≤ 0` and the sifted sum is
  `≥ 0`: trivial, handled in H4, listed here so the table is whole.
-/

namespace Salt.MR

open Complex (I)
open Set MeasureTheory intervalIntegral

/-! ## The Finset index identity -/

/-- `Σ_{Y<p≤X} f p = Σ_{p≤X} f p − Σ_{p≤Y} f p` at the `⌊·⌋₊`-indexed prime Finsets:
the `(Y,X]` window is the range-filter difference.  Needs `0 ≤ Y ≤ X`. -/
lemma prime_sum_filter_gt_sub (f : ℕ → ℝ) {X Y : ℝ} (hY0 : 0 ≤ Y) (hYX : Y ≤ X) :
    ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ)), f p
      = (∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime, f p)
        - ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1)).filter Nat.Prime, f p := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime) (fun p : ℕ => Y < (p : ℝ)) f
  have hEq : ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p : ℕ => ¬ Y < (p : ℝ))
      = (Finset.range (⌊Y⌋₊ + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, not_lt]
    constructor
    · rintro ⟨⟨-, hp⟩, hle⟩
      have hfloor : p ≤ ⌊Y⌋₊ := Nat.le_floor hle
      exact ⟨by omega, hp⟩
    · rintro ⟨hpY, hp⟩
      have hple : (p : ℝ) ≤ Y := by
        have hpf : p ≤ ⌊Y⌋₊ := by omega
        calc (p : ℝ) ≤ (⌊Y⌋₊ : ℝ) := Nat.cast_le.mpr hpf
          _ ≤ Y := Nat.floor_le hY0
      have hpX : p ≤ ⌊X⌋₊ := Nat.le_floor (le_trans hple hYX)
      exact ⟨⟨by omega, hp⟩, hple⟩
  rw [hEq] at hsplit
  linarith [hsplit]

/-! ## The FTC bridge, mirrored -/

/-- **The lower FTC bridge** — the mirror of the landed `zeta_near_bridge`: integrating the
derivative stone `hasDerivAt_log_norm_zeta` over `[a,b]` at height `t` (`|t| ≥ 3`, `a ≥ 1`),
a uniform bound `Bnd` on `‖logDeriv ζ(v+it)‖` gives
`−(b−a)·Bnd ≤ log‖ζ(b+it)‖ − log‖ζ(a+it)‖` — the same `integral_mono_on` argument with the
constant on the LEFT. -/
lemma zeta_near_bridge_lower {t a b Bnd : ℝ} (hab : a ≤ b) (h1a : 1 ≤ a) (ht : 3 ≤ |t|)
    (hnear : ∀ v : ℝ, a ≤ v → v ≤ b →
        ‖logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)‖ ≤ Bnd) :
    -((b - a) * Bnd) ≤ Real.log ‖riemannZeta ((b : ℝ) + (t : ℂ) * I)‖
        - Real.log ‖riemannZeta ((a : ℝ) + (t : ℂ) * I)‖ := by
  have htne : (t : ℝ) ≠ 0 := by
    intro h; rw [h, abs_zero] at ht; linarith
  have hzne0 : ∀ v : ℝ, v ∈ uIcc a b → riemannZeta ((v : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro v hv
    rw [uIcc_of_le hab] at hv
    exact riemannZeta_ne_zero_of_one_le_re (by simp only [Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]; nlinarith [hv.1, h1a])
  have hzne1 : ∀ v : ℝ, ((v : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro v h
    have him : ((v : ℂ) + (t : ℂ) * I).im = (1 : ℂ).im := by rw [h]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, Complex.one_im] at him
    norm_num at him
    exact htne him
  have hpt : ∀ v : ℝ, v ∈ uIcc a b →
      HasDerivAt (fun w : ℝ => Real.log ‖riemannZeta ((w : ℂ) + (t : ℂ) * I)‖)
        ((logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)).re) v :=
    fun v hv => hasDerivAt_log_norm_zeta (hzne0 v hv) (hzne1 v)
  have hUopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hζdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hζana : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := hζdiff.analyticOnNhd hUopen
  have hline : Continuous (fun v : ℝ => (v : ℂ) + (t : ℂ) * I) := by fun_prop
  have hmaps : ∀ v : ℝ, ((v : ℂ) + (t : ℂ) * I) ∈ {s : ℂ | s ≠ 1} := fun v => hzne1 v
  have hdc : ContinuousOn (fun v : ℝ => deriv riemannZeta ((v : ℂ) + (t : ℂ) * I)) (uIcc a b) :=
    (hζana.deriv.continuousOn).comp hline.continuousOn (fun v _ => hmaps v)
  have hζc : ContinuousOn (fun v : ℝ => riemannZeta ((v : ℂ) + (t : ℂ) * I)) (uIcc a b) :=
    (hζana.continuousOn).comp hline.continuousOn (fun v _ => hmaps v)
  have hcontD : ContinuousOn (fun v : ℝ => (logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)).re)
      (uIcc a b) := by
    have hLD : ContinuousOn (fun v : ℝ => logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I))
        (uIcc a b) := by
      simp only [logDeriv_apply]
      exact hdc.div hζc (fun v hv => hzne0 v hv)
    exact Complex.continuous_re.comp_continuousOn hLD
  have hint : IntervalIntegrable
      (fun v : ℝ => (logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)).re)
      MeasureTheory.volume a b :=
    hcontD.intervalIntegrable
  have hFTC : ∫ v in a..b, (logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)).re
      = Real.log ‖riemannZeta ((b : ℝ) + (t : ℂ) * I)‖
        - Real.log ‖riemannZeta ((a : ℝ) + (t : ℂ) * I)‖ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hpt hint
  have hbnd : ∀ v ∈ Icc a b, -Bnd ≤ (logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)).re := by
    intro v hv
    have habs : |(logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)).re| ≤ Bnd :=
      le_trans (Complex.abs_re_le_norm _) (hnear v hv.1 hv.2)
    linarith [(abs_le.mp habs).1]
  have hmono := intervalIntegral.integral_mono_on hab
    (_root_.intervalIntegrable_const) hint hbnd
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  rw [← hFTC]
  calc -((b - a) * Bnd) = (b - a) * -Bnd := by ring
    _ ≤ _ := hmono

/-! ## Bounded height: both endpoint logs are absolute -/

/-- On any FIXED height range `2 ≤ |t| ≤ T`, `|log‖ζ(1+1/log x + ti)‖|` is bounded by an
absolute constant `B(T)` — upper by the bounded-height closed form, lower by the shallow
strip (its `σ`-window hypothesis is free at `σ = 1+1/log x > 1`).  The sup over a fixed
range is a CONSTANT: this is what keeps the small-height regime from leaking a `log` per
harmonic (the no-slack invariant). -/
theorem abs_log_zeta_near_one_bounded_height {T : ℝ} (hT : 2 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (x t : ℝ), Real.exp 1 ≤ x → 2 ≤ |t| → |t| ≤ T →
      |Real.log ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖| ≤ B := by
  obtain ⟨c₄, hc₄pos, c, hcpos, hshallow⟩ := Salt.SW.zeta_lower_shallow
  refine ⟨max (Real.log (5 + 2 * T)) (7 * Real.log (Real.log (T + 2)) - Real.log c),
    le_trans (Real.log_nonneg (by linarith)) (le_max_left _ _), ?_⟩
  intro x t hx h2t htT
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hup : Real.log ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖
      ≤ Real.log (5 + 2 * T) :=
    log_zeta_small_b_le (by linarith : (1 : ℝ) ≤ T) hx (by linarith) htT
  have hltpos : (0 : ℝ) < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
  have hσwin : 1 - c₄ / Real.log (|t| + 2) ^ 9 ≤ 1 + 1 / Real.log x := by
    have h9 : (0 : ℝ) < Real.log (|t| + 2) ^ 9 := by positivity
    have hdiv : (0 : ℝ) ≤ c₄ / Real.log (|t| + 2) ^ 9 := div_nonneg hc₄pos.le h9.le
    have h1x : (0 : ℝ) ≤ 1 / Real.log x := by positivity
    linarith
  have hsh := hshallow (1 + 1 / Real.log x) t h2t hσwin
  have hclogpos : (0 : ℝ) < c / Real.log (|t| + 2) ^ 7 := by positivity
  have hlo : Real.log c - 7 * Real.log (Real.log (T + 2))
      ≤ Real.log ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ := by
    have hstep := Real.log_le_log hclogpos hsh
    rw [Real.log_div (ne_of_gt hcpos) (by positivity), Real.log_pow,
      show ((7 : ℕ) : ℝ) = (7 : ℝ) by norm_num] at hstep
    have hmono : Real.log (Real.log (|t| + 2)) ≤ Real.log (Real.log (T + 2)) := by
      refine Real.log_le_log hltpos ?_
      exact Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
    linarith
  rw [abs_le]
  refine ⟨?_, le_trans hup (le_max_left _ _)⟩
  calc -(max (Real.log (5 + 2 * T)) (7 * Real.log (Real.log (T + 2)) - Real.log c))
      ≤ -(7 * Real.log (Real.log (T + 2)) - Real.log c) := neg_le_neg (le_max_right _ _)
    _ = Real.log c - 7 * Real.log (Real.log (T + 2)) := by ring
    _ ≤ _ := hlo

/-! ## The harmonic prime sums, two regimes -/

/-- **The bounded-height harmonic sum bound.**  For every fixed `T ≥ 2` there is an absolute
`B` with `|Σ_{Y<p≤X} cos(t·log p)/p| ≤ B` for all `e ≤ Y ≤ X` and `2 ≤ |t| ≤ T`: the index
identity, the Euler bridge at both endpoints (cost `2|K|`), and the two endpoint logs each
absolutely bounded on the fixed height range. -/
theorem harmonic_prime_sum_abs_le_bounded_height {T : ℝ} (hT : 2 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (X Y t : ℝ), Real.exp 1 ≤ Y → Y ≤ X → 2 ≤ |t| → |t| ≤ T →
      |∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ)),
          Real.cos (t * Real.log p) / (p : ℝ)| ≤ B := by
  obtain ⟨K, hK⟩ := euler_osc_bridge_unconditional
  obtain ⟨B₀, hB₀0, hB₀⟩ := abs_log_zeta_near_one_bounded_height hT
  refine ⟨2 * |K| + 2 * B₀, by positivity, ?_⟩
  intro X Y t heY hYX h2t htT
  have heX : Real.exp 1 ≤ X := le_trans heY hYX
  have hY0 : (0 : ℝ) ≤ Y := le_trans (Real.exp_pos 1).le heY
  rw [prime_sum_filter_gt_sub _ hY0 hYX]
  have hbX := abs_le.mp (hK X t heX)
  have hbY := abs_le.mp (hK Y t heY)
  have hzX := abs_le.mp (hB₀ X t heX h2t htT)
  have hzY := abs_le.mp (hB₀ Y t heY h2t htT)
  have hKabs : K ≤ |K| := le_abs_self K
  rw [abs_le]
  constructor <;> linarith [hbX.1, hbX.2, hbY.1, hbY.2, hzX.1, hzX.2, hzY.1, hzY.2]

/-- **The VK-window harmonic sum bound.**  Above the VK threshold `T₀`, with the integration
window inside the VK strip (`1/log Y ≤ cR/D(t)`, `D(t) = (log|t|)^{3/4}(loglog|t|)^4`), the
bridge PAIR (`zeta_near_bridge` + its mirror above) gives the DIFFERENCE form
`|Σ_{Y<p≤X} cos(t·log p)/p| ≤ 2|K| + (1/log Y)·(400·D(t)/cR)` — the term that vanishes
against `log Y ≥ (log X)^{2/3}` in the mid range. -/
theorem harmonic_prime_sum_abs_le_vk :
    ∃ (K₂ cR T₀ : ℝ), 0 ≤ K₂ ∧ 0 < cR ∧ cR ≤ 1 ∧ 3 ≤ T₀ ∧ ∀ (X Y t : ℝ),
      Real.exp 1 ≤ Y → Y ≤ X → T₀ ≤ |t| →
      1 / Real.log Y
          ≤ cR / ((Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ)) →
      |∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ)),
          Real.cos (t * Real.log p) / (p : ℝ)|
        ≤ K₂ + 1 / Real.log Y
            * (400 * ((Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ))
                / cR) := by
  obtain ⟨K, hK⟩ := euler_osc_bridge_unconditional
  obtain ⟨cR, T₀, hcR0, hcR1, hT₀3, hℓ1, hnear⟩ := zeta_near_logDeriv_bound
  refine ⟨2 * |K|, cR, T₀, by positivity, hcR0, hcR1, hT₀3, ?_⟩
  intro X Y t heY hYX hTt hwin
  have heX : Real.exp 1 ≤ X := le_trans heY hYX
  have hY0 : (0 : ℝ) ≤ Y := le_trans (Real.exp_pos 1).le heY
  have hlogY1 : (1 : ℝ) ≤ Real.log Y := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) heY
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) heX
  have hlogYX : Real.log Y ≤ Real.log X := Real.log_le_log (by linarith [Real.exp_pos 1]) hYX
  set D : ℝ := (Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ) with hD
  have habs3 : (3 : ℝ) ≤ |t| := le_trans hT₀3 hTt
  have hLt1 : (1 : ℝ) < Real.log |t| := by
    have hexp1lt3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hexp1lt3
      _ ≤ Real.log |t| := Real.log_le_log (by norm_num) habs3
  have hℓ1' : (1 : ℝ) ≤ Real.log (Real.log |t|) := hℓ1 t hTt
  have hD0 : 0 < D := by
    rw [hD]
    have h34 : (0 : ℝ) < (Real.log |t|) ^ ((3 : ℝ) / 4) :=
      Real.rpow_pos_of_pos (by linarith) _
    positivity
  set a : ℝ := 1 + 1 / Real.log X with ha
  set b : ℝ := 1 + 1 / Real.log Y with hb
  have hab : a ≤ b := by
    rw [ha, hb]
    have := one_div_le_one_div_of_le (by linarith) hlogYX
    linarith
  have h1a : (1 : ℝ) ≤ a := by
    rw [ha]; have : (0 : ℝ) ≤ 1 / Real.log X := by positivity
    linarith
  have hnear' : ∀ v : ℝ, a ≤ v → v ≤ b →
      ‖logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)‖ ≤ 400 * D / cR := by
    intro v hv1 hv2
    have hv1' : 1 ≤ v := le_trans h1a hv1
    have hv2' : v ≤ 1 + cR / D := by
      have hbwin : b ≤ 1 + cR / D := by rw [hb]; linarith [hwin]
      linarith
    rw [hD] at hv2'
    have hbnd := hnear t v hTt hv1' hv2'
    rw [hD]
    exact hbnd
  have hup := zeta_near_bridge (t := t) (a := a) (b := b) (Bnd := 400 * D / cR)
    hab h1a habs3 hnear'
  have hlo := zeta_near_bridge_lower (t := t) (a := a) (b := b) (Bnd := 400 * D / cR)
    hab h1a habs3 hnear'
  have hlen : (b - a) * (400 * D / cR) ≤ 1 / Real.log Y * (400 * D / cR) := by
    have hba : b - a ≤ 1 / Real.log Y := by
      rw [ha, hb]
      have : (0 : ℝ) ≤ 1 / Real.log X := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right hba (by positivity)
  have hbX := abs_le.mp (hK X t heX)
  have hbY := abs_le.mp (hK Y t heY)
  rw [prime_sum_filter_gt_sub _ hY0 hYX]
  -- the bridge endpoints: `a = 1+1/log X` is the `X`-side, `b = 1+1/log Y` the `Y`-side
  have hida : ((a : ℝ) : ℂ) + (t : ℂ) * I
      = ((1 + 1 / Real.log X : ℝ) : ℂ) + (t : ℝ) * Complex.I := by rw [ha]
  have hidb : ((b : ℝ) : ℂ) + (t : ℂ) * I
      = ((1 + 1 / Real.log Y : ℝ) : ℂ) + (t : ℝ) * Complex.I := by rw [hb]
  rw [hida, hidb] at hup hlo
  have hKabs : K ≤ |K| := le_abs_self K
  rw [abs_le]
  constructor <;> linarith [hbX.1, hbX.2, hbY.1, hbY.2, hup, hlo, hlen]

end Salt.MR
