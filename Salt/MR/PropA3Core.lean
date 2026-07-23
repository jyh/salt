/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.DistSplit
import Salt.MR.DistHalasz
import Salt.MR.HalaszCore

/-!
# MR wave-3 rung H3 — the numeral/branch completion of R3.1 + R3.2/R3.3/R3.4 (`PropA3Core`)

This file lands the *numeral* layer on top of the abstract `𝔻`-split algebra that
`DistSplit.lean` landed (`dist_split_A4`, `dist_split_A4_recentered`,
`dist_split_fgJ`, `dist_recenter_sq`).  The frozen numerals are BINDING
(`s8-freeze.md:33`, N2): threshold `(1/16)·loglog X`, `f`-floor `(1/16)·loglog`,
halved conclusion `(1/32)·loglog X`; and the `−5·logloglog(2X+16)` correction is
carried IN-STATEMENT (S5 law — never absorbed into `C`).

## R3.1 completion — the two-branch dispatch (`s8-freeze.md:33`)

* **Branch a** (`M ≥ (1/16)·loglog X`): the `f`-floor holds directly at the twist
  `costwist t`; the landed `dist_split_fgJ` halves it to `(1/32)·loglog X`
  (`dist_split_fgJ_branch_a`).
* **Branch b** (`|t − t₁| > (log X)^{1/16}/2`): recenter with `L = (1/4)·loglog X`
  (from `DistHalasz.dist_one_floor_pow`, the H1.0-grounded floor) and center cap
  `S = (1/16)·loglog X`, then halve.  The recentering sqrt-algebra
  `(√L − √S)² ≥ (1/16)·loglog X − δ` is `recenter_sq_floor`; the composed branch is
  `dist_split_fgJ_branch_b`.
* **The frozen stone** `dist_split_A4_frozen` dispatches `a ∨ b` into the frozen
  conclusion `𝔻(fg_J, n^{it}; X)² ≥ (1/32)·loglog X − 5·logloglog(2X+16) − C − W`,
  with the window-loss `W = 𝔻(f, fg_J)²` carried as the named hypothesis `hloss`
  (the MULT-SHIU seam — NOT discharged here).

## Posture

Center-`t₀` recentering only (I-3 gate-check verdict — NO GS[10] Lipschitz import);
all analytic conditionality (window loss, S1'/K4' seam of `halasz_ball_decay`) carried
as NAMED hypotheses; the campaign house reconciles at the end.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## R3.1 — the recentering sqrt-algebra (branch b core) -/

/-- **The recentering sqrt floor** (branch b, the `(√L − √S)²` numeral).  For
`S = (1/16)·ℓ` and an `f = 1`-floor value `L ≥ (1/4)·ℓ − δ` (`δ ≥ 0` the honest
correction, `L ≥ 0`), the reverse-triangle recentering obeys
`(√L − √S)² ≥ (1/16)·ℓ − δ`.  With `L = (1/4)ℓ`, `δ = 0` this is exactly
`(√((1/4)ℓ) − √((1/16)ℓ))² = ((1/2 − 1/4)√ℓ)² = (1/16)ℓ`.

SOS certificate (with `u = √L`, `v = √S`):
`u² − 2uv + δ = ½(L + δ − 4S) + ½(u − 2v)² + δ/2`, all three terms `≥ 0`
(`L + δ − 4S = L + δ − (1/4)ℓ ≥ 0` from the floor `L ≥ (1/4)ℓ − δ`). -/
theorem recenter_sq_floor {L S ℓ δ : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 ≤ δ)
    (hS : S = (1 / 16) * ℓ) (hL0 : 0 ≤ L) (hLlb : (1 / 4) * ℓ - δ ≤ L) :
    (1 / 16) * ℓ - δ ≤ (Real.sqrt L - Real.sqrt S) ^ 2 := by
  have hSnn : 0 ≤ S := by rw [hS]; linarith
  have hu2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0
  have hv2 : Real.sqrt S ^ 2 = S := Real.sq_sqrt hSnn
  have hu : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hv : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
  nlinarith [sq_nonneg (Real.sqrt L - 2 * Real.sqrt S), hu2, hv2, hLlb, hδ, hS,
    hu, hv, mul_nonneg hu hv]

/-! ## R3.1 — the two branch numerals on `fg_J` -/

/-- **R3.1 branch a — the direct-floor numeral.**  When the `f`-side distance floor
`(1/16)·loglog X ≤ 𝔻(f, n^{it}; X)²` holds at the twist directly, the landed
`dist_split_fgJ` halving gives `𝔻(fg_J, n^{it}; X)² ≥ (1/32)·loglog X − W`, with `W`
the window loss (`hloss`, the MULT-SHIU seam). -/
theorem dist_split_fgJ_branch_a {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t₀ y Y : ℝ)
    {t X W : ℝ}
    (hbranchA : (1 / 16) * Real.log (Real.log X) ≤ pretDistSq f (costwist t) X)
    (hloss : pretDistSq f (fgJ f t₀ y Y) X ≤ W) :
    (1 / 32) * Real.log (Real.log X) - W
      ≤ pretDistSq (fgJ f t₀ y Y) (costwist t) X := by
  have h := dist_split_fgJ hf t₀ y Y hbranchA hloss
  linarith [h]

/-- **R3.1 branch b — the recenter-then-halve numeral.**  With the `f = 1`-floor
value `L ≥ (1/4)·loglog X − δ` at the shifted frequency `t − t₁` (`dist_one_floor_pow`),
the center cap `S = (1/16)·loglog X` (`hS_cap`) and the regime `S ≤ L` (`hSL`), the
recentering `recenter_sq_floor` yields the `(1/16)·loglog X − δ` `f`-floor which
`dist_split_A4_recentered` halves onto `fg_J`:
`𝔻(fg_J, n^{it}; X)² ≥ (1/32)·loglog X − δ/2 − W`.  `δ` is the honest correction
(o(loglog X)); `W` the window loss. -/
theorem dist_split_fgJ_branch_b {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t₀ y Y : ℝ)
    {t t₁ X W L δ : ℝ}
    (hℓnn : 0 ≤ Real.log (Real.log X)) (hδ : 0 ≤ δ) (hL0 : 0 ≤ L)
    (hL_floor : L ≤ pretDistSq (fun _ => 1) (costwist (t - t₁)) X)
    (hL_lb : (1 / 4) * Real.log (Real.log X) - δ ≤ L)
    (hS_cap : pretDistSq f (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X))
    (hSL : (1 / 16) * Real.log (Real.log X) ≤ L)
    (hloss : pretDistSq f (fgJ f t₀ y Y) X ≤ W) :
    (1 / 32) * Real.log (Real.log X) - δ / 2 - W
      ≤ pretDistSq (fgJ f t₀ y Y) (costwist t) X := by
  have hrec := dist_split_A4_recentered hf (norm_fgJ_le hf t₀ y Y) hL_floor hS_cap hSL hloss
  have hfloor := recenter_sq_floor (L := L) (S := (1 / 16) * Real.log (Real.log X))
    (ℓ := Real.log (Real.log X)) (δ := δ) hℓnn hδ rfl hL0 hL_lb
  linarith [hrec, hfloor]

/-! ## R3.1 frozen stone — numeric log-of-log bookkeeping helpers -/

/-- The numeric anchor `e^e ≤ 2X + 16` for `X ≥ e`: since `X ≥ e > 2.718`,
`2X + 16 > 21.4`, while `e^e ≤ e³ = e^1³ < 2.7183³ < 21`. -/
private lemma expexp_le_two_X {X : ℝ} (hX : Real.exp 1 ≤ X) :
    Real.exp (Real.exp 1) ≤ 2 * X + 16 := by
  have he1u : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he1l : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hX' : (2.7182818283 : ℝ) < X := lt_of_lt_of_le he1l hX
  have hexp3eq : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]; ring
  have hexp3lt : Real.exp 3 < 2.7182818286 ^ 3 := by rw [hexp3eq]; gcongr
  have hee : Real.exp (Real.exp 1) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by linarith)
  have hpow : (2.7182818286 : ℝ) ^ 3 < 21 := by norm_num
  linarith [hee, hexp3lt, hpow, hX']

/-- `logloglog(2X+16) ≥ 0` for `X ≥ e`: `2X+16 ≥ e^e`, so `loglog(2X+16) ≥ 1`,
so `logloglog(2X+16) ≥ 0`.  Needed so the frozen `−5·logloglog(2X+16)` term
(and its `(5/2)→5` halving slack) is a genuine downward correction. -/
private lemma logloglog_two_X_nonneg {X : ℝ} (hX : Real.exp 1 ≤ X) :
    0 ≤ Real.log (Real.log (Real.log (2 * X + 16))) := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogpos : 0 < Real.log (2 * X + 16) := Real.log_pos (by linarith)
  have h1 : Real.exp 1 ≤ Real.log (2 * X + 16) :=
    (Real.le_log_iff_exp_le (by linarith)).mpr (expexp_le_two_X hX)
  have h2 : (1 : ℝ) ≤ Real.log (Real.log (2 * X + 16)) :=
    (Real.le_log_iff_exp_le hlogpos).mpr h1
  exact Real.log_nonneg h2

/-- Monotonicity of the triple log: `logloglog(b+16) ≤ logloglog(2X+16)` for
`0 ≤ b ≤ X` (all inner arguments stay `> e`, so each `Real.log` is monotone). -/
private lemma logloglog_mono_of_le {b X : ℝ} (hb : 0 ≤ b) (hbX : b ≤ X) :
    Real.log (Real.log (Real.log (b + 16)))
      ≤ Real.log (Real.log (Real.log (2 * X + 16))) := by
  have hX0 : 0 ≤ X := le_trans hb hbX
  have hb16 : (0 : ℝ) < b + 16 := by linarith
  have h2X : b + 16 ≤ 2 * X + 16 := by linarith
  have hlog1 : Real.log (b + 16) ≤ Real.log (2 * X + 16) := Real.log_le_log hb16 h2X
  have hlogb_gt1 : (1 : ℝ) < Real.log (b + 16) := by
    have hexp : Real.exp 1 < b + 16 := by have := Real.exp_one_lt_d9; linarith
    exact (Real.lt_log_iff_exp_lt (by linarith)).mpr hexp
  have hll1 : Real.log (Real.log (b + 16)) ≤ Real.log (Real.log (2 * X + 16)) :=
    Real.log_le_log (by linarith) hlog1
  exact Real.log_le_log (Real.log_pos hlogb_gt1) hll1

/-! ## R3.1 frozen stone — the two-branch dispatch to the frozen conclusion -/

/-- **R3.1 — the frozen conclusion (`dist_split_A4_frozen`).**  The numeral completion
of the landed abstract split: there are constants `Cfloor` (the `dist_one_floor_pow`
floor constant) and `C ≥ 0` such that, for `X ≥ e`, the window loss `W = 𝔻(f, fg_J)²`
(hypothesis `hloss`), and EITHER

* branch a: the direct `f`-floor `(1/16)·loglog X ≤ 𝔻(f, n^{it}; X)²`, OR
* branch b: a center `t₁` with `1 ≤ |t − t₁| ≤ X`, center cap
  `𝔻(f, n^{it₁}; X)² ≤ (1/16)·loglog X`, and the regime `S ≤ L`
  (`(1/16)·loglog X ≤` the `dist_one_floor_pow` floor at `t − t₁`),

the FROZEN conclusion holds:

  `𝔻(fg_J, n^{it}; X)² ≥ (1/32)·loglog X − 5·logloglog(2X+16) − C − W`.

The `−5·logloglog(2X+16)` term is IN-STATEMENT (S5 law — never absorbed into `C`);
`W` is the MULT-SHIU window mass (carried, NOT discharged).  Branch a is the stronger
`(1/32)·loglog X − W` bound weakened into the frozen shape (`logloglog(2X+16) ≥ 0`,
`C ≥ 0`); branch b composes `dist_one_floor_pow`, `recenter_sq_floor` and the halving,
with the honest `(3/4)(loglog(|t−t₁|+3) − loglog X) + 5·logloglog + Cfloor` correction
absorbed into `C` via `loglog_height_le` and the triple-log monotonicity. -/
theorem dist_split_A4_frozen :
    ∃ Cfloor C : ℝ, 0 ≤ C ∧
      ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ (t₀ y Y t t₁ X W : ℝ),
        Real.exp 1 ≤ X →
        pretDistSq f (fgJ f t₀ y Y) X ≤ W →
        ((1 / 16) * Real.log (Real.log X) ≤ pretDistSq f (costwist t) X ∨
          (1 ≤ |t - t₁| ∧ |t - t₁| ≤ X ∧
            pretDistSq f (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) ∧
            (1 / 16) * Real.log (Real.log X) ≤
              Real.log (Real.log X) - (3 / 4) * Real.log (Real.log (|t - t₁| + 3)) -
                5 * Real.log (Real.log (Real.log (|t - t₁| + 16))) - Cfloor)) →
        (1 / 32) * Real.log (Real.log X) -
              5 * Real.log (Real.log (Real.log (2 * X + 16))) - C - W ≤
            pretDistSq (fgJ f t₀ y Y) (costwist t) X := by
  obtain ⟨Cfloor, hCfloor⟩ := dist_one_floor_pow
  refine ⟨Cfloor, (3 / 8) * Real.log (1 + Real.log (1 + 3)) + max Cfloor 0 + 1, ?_, ?_⟩
  · show (0 : ℝ) ≤ (3 / 8) * Real.log (1 + Real.log (1 + 3)) + max Cfloor 0 + 1
    have hκnn : 0 ≤ Real.log (1 + Real.log (1 + 3)) :=
      Real.log_nonneg (by nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 1 + 3 by norm_num)])
    have hm : (0 : ℝ) ≤ max Cfloor 0 := le_max_right _ _
    have hs : (0 : ℝ) ≤ (3 / 8) * Real.log (1 + Real.log (1 + 3)) :=
      mul_nonneg (by norm_num) hκnn
    linarith [hs, hm]
  · intro f hf t₀ y Y t t₁ X W hX hloss hbranch
    have hlogX1 : (1 : ℝ) ≤ Real.log X := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
    have hℓnn : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hlogX1
    have hL3nn : 0 ≤ Real.log (Real.log (Real.log (2 * X + 16))) := logloglog_two_X_nonneg hX
    have hκnn : 0 ≤ Real.log (1 + Real.log (1 + 3)) :=
      Real.log_nonneg (by nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 1 + 3 by norm_num)])
    have hCmax : (0 : ℝ) ≤ max Cfloor 0 := le_max_right _ _
    have hCflmax : Cfloor ≤ max Cfloor 0 := le_max_left _ _
    rcases hbranch with ha | ⟨hb1, hbX, hcap, hreg⟩
    · -- branch a: the direct floor, weakened into the frozen shape
      have hba := dist_split_fgJ_branch_a hf t₀ y Y ha hloss
      set ℓ := Real.log (Real.log X)
      set L3 := Real.log (Real.log (Real.log (2 * X + 16)))
      set κ := Real.log (1 + Real.log (1 + 3))
      linarith [hba, hL3nn, hκnn, hCmax]
    · -- branch b: recenter (via `dist_one_floor_pow`) then halve
      have hLfl := hCfloor X (t - t₁) hX hb1
      have hbX0 : (0 : ℝ) ≤ |t - t₁| := abs_nonneg _
      have hκ := loglog_height_le (Q := 1) (by norm_num) hX
        (show |t - t₁| ≤ 1 * X by rw [one_mul]; exact hbX)
      have hmono3 := logloglog_mono_of_le hbX0 hbX
      -- fold every "log-of-arithmetic" atom to a plain variable so `linarith` can do
      -- the coefficient arithmetic (`(3/8)·κ`, `(3/4)·A`, …) reliably
      set ℓ := Real.log (Real.log X) with hℓdef
      set L3 := Real.log (Real.log (Real.log (2 * X + 16))) with hL3def
      set κ := Real.log (1 + Real.log (1 + 3)) with hκdef
      set A := Real.log (Real.log (|t - t₁| + 3)) with hAdef
      set B := Real.log (Real.log (Real.log (|t - t₁| + 16))) with hBdef
      have hL0 : 0 ≤ ℓ - (3 / 4) * A - 5 * B - Cfloor := by linarith [hreg, hℓnn]
      set δ := max ((3 / 4) * κ + 5 * L3 + Cfloor) 0 with hδdef
      have hδnn : 0 ≤ δ := by rw [hδdef]; exact le_max_right _ _
      have hPδ : (3 / 4) * κ + 5 * L3 + Cfloor ≤ δ := by rw [hδdef]; exact le_max_left _ _
      have hL_lb : (1 / 4) * ℓ - δ ≤ ℓ - (3 / 4) * A - 5 * B - Cfloor := by
        linarith [hκ, hmono3, hPδ]
      have hrec := dist_split_A4_recentered hf (norm_fgJ_le hf t₀ y Y) hLfl hcap hreg hloss
      have hfloor := recenter_sq_floor (L := ℓ - (3 / 4) * A - 5 * B - Cfloor)
        (S := (1 / 16) * ℓ) (ℓ := ℓ) (δ := δ) hℓnn hδnn rfl hL0 hL_lb
      have hδbound : δ ≤ 2 * (5 * L3 + ((3 / 8) * κ + max Cfloor 0 + 1)) := by
        rw [hδdef]
        apply max_le
        · linarith [hL3nn, hCflmax, hCmax]
        · linarith [hL3nn, hκnn, hCmax]
      linarith [hrec, hfloor, hδbound]

/-! ## R3.2 — the `T1` pointwise/mass decay (`s8-freeze.md:34`, N3) -/

/-- **The `exp(-M/2)` decay at the R3.1 floor.**  If the center distance obeys the
R3.1 floor `M ≥ (1/32)·loglog X`, then `exp(-M/2) ≤ (log X)^{-1/64}` — the grade
`exp(-(1/2)·(1/32)·loglog X)`.  This is the pointwise engine of the frozen T1 bound
`T1 ≪ X·(log X)^{-1/64+o(1)}`. -/
theorem expEM_le_of_floor {X M : ℝ} (hX : Real.exp 1 ≤ X)
    (hM : (1 / 32) * Real.log (Real.log X) ≤ M) :
    Real.exp (-M / 2) ≤ (Real.log X) ^ (-(1 : ℝ) / 64) := by
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hstep : -M / 2 ≤ Real.log (Real.log X) * (-(1 : ℝ) / 64) := by
    set ℓ := Real.log (Real.log X); linarith [hM]
  calc Real.exp (-M / 2)
      ≤ Real.exp (Real.log (Real.log X) * (-(1 : ℝ) / 64)) := Real.exp_le_exp.mpr hstep
    _ = (Real.log X) ^ (-(1 : ℝ) / 64) := (Real.rpow_def_of_pos hlogXpos _).symm

/-- **R3.2 — the integrated `T1` mass floor (`s8-freeze.md:34`, N3).**  For
`M ≤ (1/16)·loglog X` (the T1 regime — the centers where Halász decay is weak), the mass floor
`(log X)^{-1/32} ≤ exp(-M/2)` holds (`C = 1`; the tie at the threshold `M = (1/16)loglog`
is exactly `exp(-(1/32)loglog X) = (log X)^{-1/32}`).  Absorbed by the `≪`-constant and
existential `c₀` downstream. -/
theorem T1_mass_floor {X M : ℝ} (hX : Real.exp 1 ≤ X)
    (hM : M ≤ (1 / 16) * Real.log (Real.log X)) :
    (Real.log X) ^ (-(1 : ℝ) / 32) ≤ Real.exp (-M / 2) := by
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hstep : Real.log (Real.log X) * (-(1 : ℝ) / 32) ≤ -M / 2 := by
    set ℓ := Real.log (Real.log X); linarith [hM]
  calc (Real.log X) ^ (-(1 : ℝ) / 32)
      = Real.exp (Real.log (Real.log X) * (-(1 : ℝ) / 32)) := Real.rpow_def_of_pos hlogXpos _
    _ ≤ Real.exp (-M / 2) := Real.exp_le_exp.mpr hstep

/-- **R3.2 — `T1_pointwise_decay` (`s8-freeze.md:34`, N3).**  The per-center T1 mass bound:
composing the exit stone `halasz_ball_decay` with the R3.1 floor `M ≥ (1/32)·loglog X`
(`expEM_le_of_floor`) gives

  `U ≤ (2·C₁ + C₂)·X·((log X)^{-1/64} + (log X)^{-1/2+ε})`

(the `≪ X·(log X)^{-1/64+o(1)}` grade).

The S1'/MULT-SHIU conditionality of `halasz_ball_decay` is carried through EXPLICITLY as the
named hypotheses `hsplit` (the S1' head/tail split of `U`), `hhead` (the S2' centered head,
K4'-conditional) and `htail` (the S2' tail ledger) — NOT discharged here.

**AMENDMENT J0 (JYH-ratified 2026-07-23).**  `M = M_range f X T` is GHS Lemma 1's
range-minimum squared-distance (the `sInf` over the offset window), NOT the center value
`pretDistSq f g X`.  The center-M deviation was the drift problem's source; `M_range`
never drifts below the landed floor (`Mrange_one_floor`) and restores the frozen
`prop_A3'` semantics.  The floor `hfloor` is now `(1/32)loglog X ≤ M_range f X T`
(`Mrange_one_floor`-supplied), and `expEM_le_of_floor` (generic in `M`) threads
unchanged. -/
theorem T1_pointwise_decay {f g : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hg : ∀ n, ‖g n‖ ≤ 1) {X ε U Uhead Utail C₁ C₂ T : ℝ}
    (hX : Real.exp 1 ≤ X) (hε : 0 ≤ ε) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : U = Uhead + Utail)
    (hhead : Uhead ≤ C₁ * X * ((1 + M_range f X T) * Real.exp (-(M_range f X T))))
    (htail : Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2))
    (hfloor : (1 / 32) * Real.log (Real.log X) ≤ M_range f X T) :
    U ≤ (2 * C₁ + C₂) * X *
        ((Real.log X) ^ (-(1 : ℝ) / 64) + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  have hdecay := halasz_ball_decay hf hg hX hε hC₁ hC₂ hsplit hhead htail
  have hexp := expEM_le_of_floor hX hfloor
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hcoef : (0 : ℝ) ≤ (2 * C₁ + C₂) * X := mul_nonneg (by linarith) hXpos.le
  refine hdecay.trans (mul_le_mul_of_nonneg_left ?_ hcoef)
  linarith [hexp]

end Salt.MR
