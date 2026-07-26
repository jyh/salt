/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetResiduals

/-!
# Transfer34 — the `q = 3/4` transfer twin (⟦V6b⟧'s **R3**)

`docs/exploration/hsup-design.md`, ⟦V6b⟧: the GS-7.1 transfer as built converts the CASE-B
pocket's own cap to the CRUDE Mertens-mass convention `𝔻² ≤ P(x)/8`
(`CofactorSupply.pocket_transport`:320 via `SmallStones.sixteenth_loglog_le_SPartial_div_eight`),
and the resulting certificate `√(2P)·√(P/8) = P/2` (`BallSup.budget_le_half`) prices the
transfer error at a `√(log x)` denominator, `q = 1/2`.  **The pocket's real cap is
`(1/32 − θ)·loglog X`, and it is thrown away as-built.**  This file restores it.

## The arithmetic, in four lines

* the pocket cap `(1/32 − θ)loglog X` converts to `𝔻² ≤ P(x)/32` — NOT `P(x)/8` — as soon as
  `32·(1/32 − θ)·loglog X ≤ P(x)`.  With the corpus's crude Meissel–Mertens floor
  (`SmallStones.mertensM_ge_neg_seventeen`, `−17 ≤ M₂`) and `12/log X ≤ 1` this reads
  `(1 − 32θ)loglog X ≤ loglog X − 18`, i.e. **`32θ·loglog X ≥ 18`**; at the §8.3 pin
  `θ = θ₂₉₃ = 1/(32(3e+1))` that is `loglog X ≥ 18(3e+1) = 164.787…`, so the threshold is
  `exp(exp 165)` (`ballQuarterThreshold`) — FREE against the collision tower.
* Cauchy–Schwarz then certifies `√(2P)·√(P/32) = √(P²/16) = P/4`: `budget_le_quarter`.
* Mertens-2 turns `exp(P(x)/4)` into `(log x)^{1/4}·e^{M₂/4+3}` (`exp_budget_le_34`), and
  GS 7.1's `x/log x` prefactor collapses with it to `x/(log x)^{3/4}`: the `q = 3/4`
  denominator (`ballErr34`, `transfer_at_scale_34`).
* the CASE-B far transfer is re-run at that denominator (`farErr34`, `farSupS34`,
  `far_transfer_sup_34`), and the ambient-gate consumers of `USetResiduals` follow
  (`farErr34_le_of_ambient_gate`, `Rbd34_grade_priced(_of_ambient)`).

## What this buys (and what it does not)

`farErr` at `q = 1/2` is bounded BELOW by the absolute constant `120·ballSupC` under
`USetPins.TannGate` (`USetResiduals.farErr_TannGate_floor`) — the repair window is empty.
At `q = 3/4` that particular collision **dissolves**: at the `TannGate` floor
`log Rmax ≍ 30√(log X)` the twin reads `farErr34 ≲ 256·ballSupC34·(log X)^{−1/4}`
(`farErr34_at_TannGate_floor`) — a DECAYING bound where the `q = 1/2` page has an absolute
floor.  (Comparing it to the demanded `(log X)^{−ρ₂₉₃}` is then a matter of an explicit `X₀`,
since `ρ₂₉₃ ≈ 0.0102 < 1/4`; that comparison is NOT proved here.)  ⟦V6b⟧'s
verdict stands nonetheless: at the LIVE row height `Tann ≍ X/log X` the numerator is
`≍ log X` and the twin still diverges (`4·ballSupC34·(log X)^{1/4}`).  R3 is the certificate
half of the pair; **R1** (the localized dichotomy, `Rmax → T*`) and **R2** (the `y` re-pin)
are what make the numerator small enough for the `3/4` denominator to close.

## Iron rule 1 — twins, never edits

Nothing here edits `BallSup`, `SmallStones`, `CofactorBall`, `CofactorSupply` or
`USetResiduals`: every statement below is a NEW twin of a landed one, at the `α = 1/32`
budget.  The landed `q = 1/2` chain stays exactly as it is.

Law #253: every threshold (`exp(exp 165)`), every gate (`32θ·loglog X ≥ 18`, the loglog
descent gap, the ambient radius gate) is IN-STATEMENT, never absorbed.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 (T-1) — the pocket's cap, converted at `α = 1/32`

`SmallStones`:152 converts the A.4 ball convention `(1/16)loglog X` to `P(x)/8` at the
threshold `exp(exp 40)`.  The twin converts the POCKET's cap `(1/32 − θ)loglog X` to the
FOUR-TIMES-SHARPER `P(x)/32`, at the threshold `exp(exp 165)`.  The `θ`-slack is what makes
it work: `(1/32)loglog X ≤ P(x)/32` is FALSE with the corpus's crude `−17 ≤ M₂`, and
`(1/32 − θ)loglog X ≤ P(x)/32` is true exactly when `32θ·loglog X ≥ 18`. -/

/-- **The `q = 3/4` threshold**: `exp(exp 165)` (so `loglog X ≥ 165`).  Past it the conversion
of the pocket's cap `(1/32 − θ)loglog X` into the Mertens-mass convention `P(x)/32` closes at
the §8.3 pin `θ = θ₂₉₃` — the gate is `18(3e+1) = 164.787… ≤ loglog X`.  (Compare
`SmallStones.ballMertensThreshold = exp(exp 40)`, the crude `P(x)/8` conversion's threshold.) -/
noncomputable def ballQuarterThreshold : ℝ := Real.exp (Real.exp 165)

lemma exp_oneSixtyFive_ge : (166 : ℝ) ≤ Real.exp 165 := by
  have := Real.add_one_le_exp (165 : ℝ); linarith

/-- The threshold clears every positivity floor the consumers use (`3 ≤ X`). -/
theorem three_le_ballQuarterThreshold : (3 : ℝ) ≤ ballQuarterThreshold := by
  have h1 : (167 : ℝ) ≤ Real.exp 166 := by have := Real.add_one_le_exp (166 : ℝ); linarith
  have h2 : Real.exp 166 ≤ Real.exp (Real.exp 165) := Real.exp_le_exp.mpr exp_oneSixtyFive_ge
  rw [ballQuarterThreshold]; linarith

/-- Past the threshold, `log X ≥ exp 165` and `loglog X ≥ 165`. -/
lemma loglog_ge_oneSixtyFive {X : ℝ} (hX : ballQuarterThreshold ≤ X) :
    Real.exp 165 ≤ Real.log X ∧ (165 : ℝ) ≤ Real.log (Real.log X) := by
  have h1 : Real.log ballQuarterThreshold ≤ Real.log X :=
    Real.log_le_log (by rw [ballQuarterThreshold]; exact Real.exp_pos _) hX
  rw [ballQuarterThreshold, Real.log_exp] at h1
  refine ⟨h1, ?_⟩
  have h2 : Real.log (Real.exp 165) ≤ Real.log (Real.log X) :=
    Real.log_le_log (Real.exp_pos 165) h1
  rwa [Real.log_exp] at h2

/-- **The Mertens mass past the threshold**: `P(y) ≥ loglog y − 18`.  The `18` is
`17 + 1`: `−17 ≤ M₂` (`SmallStones.mertensM_ge_neg_seventeen`) and `12/log y ≤ 1`, the
latter because `log y ≥ exp 165 ≥ 166`. -/
theorem SPartial_ge_loglog_sub_eighteen {y : ℝ} (hy : ballQuarterThreshold ≤ y) :
    Real.log (Real.log y) - 18 ≤ Salt.Mertens.SPartial y := by
  obtain ⟨h1, _h2⟩ := loglog_ge_oneSixtyFive hy
  have hpos : (0 : ℝ) < Real.log y := lt_of_lt_of_le (by linarith [exp_oneSixtyFive_ge]) h1
  have hy2 : (2 : ℝ) ≤ y := le_trans (by linarith [three_le_ballQuarterThreshold]) hy
  have hsharp := (abs_le.mp (Salt.Mertens.mertens_second_sharp_real hy2)).1
  have hsmall : 12 / Real.log y ≤ 1 := by
    rw [div_le_one hpos]; linarith [exp_oneSixtyFive_ge]
  linarith [mertensM_ge_neg_seventeen]

/-- **T-1 (the core) — the pocket's cap in the `P/32` convention, WITH the loglog descent
priced.**  The cap lives at the GLOBAL scale `X`; the transfer reads it at a window scale `y`
(`k₀ ≤ y ≤ M ≤ X`), where the Mertens mass is SMALLER.  The gap `loglog X − loglog y` is
therefore charged in the gate — law #253, never absorbed:

  `18 + (loglog X − loglog y) ≤ 32θ·loglog X  ⟹  (1/32 − θ)loglog X ≤ P(y)/32`.

(The crude `P/8` conversion of `SmallStones`:152 hides this gap inside its factor-2 slack
`(1/32)loglog X ≤ (1/16)loglog k₀`; at `P/32` there is no slack left to hide it in.) -/
theorem thirtysecond_cap_to_SPartial {X y θ : ℝ} (hy : ballQuarterThreshold ≤ y)
    (hgate : 18 + Real.log (Real.log X) - Real.log (Real.log y)
      ≤ 32 * θ * Real.log (Real.log X)) :
    (1 / 32 - θ) * Real.log (Real.log X) ≤ Salt.Mertens.SPartial y / 32 := by
  have hS := SPartial_ge_loglog_sub_eighteen hy
  linarith

/-- **T-1 — the conversion in `SmallStones`:152's own binder shape** (`X` past the threshold,
`x ≥ X`): the descent gap is `≤ 0` here, so the gate is the bare `32θ·loglog X ≥ 18`.

  `(1/32 − θ)·loglog X ≤ P(x)/32`.

This is the `α = 1/32` twin of `sixteenth_loglog_le_SPartial_div_eight`. -/
theorem thirtysecond_loglog_le_SPartial_div_32 {X x θ : ℝ}
    (hX : ballQuarterThreshold ≤ X) (hx : X ≤ x)
    (hgate : 18 ≤ 32 * θ * Real.log (Real.log X)) :
    (1 / 32 - θ) * Real.log (Real.log X) ≤ Salt.Mertens.SPartial x / 32 := by
  obtain ⟨h1, _h2⟩ := loglog_ge_oneSixtyFive hX
  have hX0 : (0 : ℝ) < X := by linarith [three_le_ballQuarterThreshold]
  have hlogXpos : (0 : ℝ) < Real.log X := lt_of_lt_of_le (by linarith [exp_oneSixtyFive_ge]) h1
  have hmono : Real.log X ≤ Real.log x := Real.log_le_log hX0 hx
  have hll : Real.log (Real.log X) ≤ Real.log (Real.log x) := Real.log_le_log hlogXpos hmono
  exact thirtysecond_cap_to_SPartial (le_trans hX hx) (by linarith)

/-- `32·θ₂₉₃ = 1/(3e+1)` — the §8.3 pin's own conversion factor. -/
lemma thirtytwo_theta293 : 32 * theta293 = 1 / (3 * Real.exp 1 + 1) := by
  have hne : (3 * Real.exp 1 + 1) ≠ 0 := by positivity
  rw [theta293]
  field_simp

/-- **T-1, at the §8.3 pin `θ = θ₂₉₃`.**  The gate `32θ₂₉₃·loglog X ≥ 18` is
`18(3e+1) ≤ loglog X`, i.e. `164.787… ≤ loglog X` — discharged by the threshold
`exp(exp 165)` with margin `0.21`. -/
theorem thirtysecond_cap_to_SPartial_293 {X x : ℝ}
    (hX : ballQuarterThreshold ≤ X) (hx : X ≤ x) :
    (1 / 32 - theta293) * Real.log (Real.log X) ≤ Salt.Mertens.SPartial x / 32 := by
  obtain ⟨_h1, h2⟩ := loglog_ge_oneSixtyFive hX
  refine thirtysecond_loglog_le_SPartial_div_32 hX hx ?_
  have hpos : (0 : ℝ) < 3 * Real.exp 1 + 1 := by positivity
  rw [thirtytwo_theta293, one_div, inv_mul_eq_div, le_div_iff₀ hpos]
  linarith [Real.exp_one_lt_d9]

/-- **T-1, at the pin, WITH the descent.**  The window's loglog gap is allowed to be as large
as `1/100`; the live descent gate `(1 − 1/loglog X)log X ≤ log k₀` delivers a gap of at most
`≈ 1/(loglog X − 1) ≤ 1/164`, so the margin is a factor `~4`.  The numeric obligation is
`(18 + 1/100)(3e+1) = 164.97… ≤ 165 ≤ loglog X`. -/
theorem thirtysecond_cap_to_SPartial_293_descent {X y : ℝ}
    (hy : ballQuarterThreshold ≤ y)
    (hdesc : Real.log (Real.log X) - Real.log (Real.log y) ≤ 1 / 100)
    (hL : (165 : ℝ) ≤ Real.log (Real.log X)) :
    (1 / 32 - theta293) * Real.log (Real.log X) ≤ Salt.Mertens.SPartial y / 32 := by
  refine thirtysecond_cap_to_SPartial hy ?_
  have hpos : (0 : ℝ) < 3 * Real.exp 1 + 1 := by positivity
  have hkey : (18 + 1 / 100) * (3 * Real.exp 1 + 1) ≤ Real.log (Real.log X) := by
    linarith [Real.exp_one_lt_d9]
  have h1 : (18 + Real.log (Real.log X) - Real.log (Real.log y)) * (3 * Real.exp 1 + 1)
      ≤ (18 + 1 / 100) * (3 * Real.exp 1 + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hpos.le
  rw [thirtytwo_theta293, one_div, inv_mul_eq_div, le_div_iff₀ hpos]
  linarith

/-! ## §2 (T-2) — the budget page at `α = 1/32`: `√(2P)·√(P/32) = P/4`

`BallSup`:120/144/165 at the sharper cap.  ONE numeral changes through the chain
(`8 → 32`, `2 → 4`, `1/2 → 1/4`, `M₂/2+6 → M₂/4+3`); nothing else moves. -/

/-- **The Cauchy–Schwarz quarter-cut, abstract** (the `α = 1/32` twin of
`BallSup.budget_le_half_abstract`).  On any finite set of positive integers, a 1-bounded `u`
whose distance mass is at most a THIRTY-SECOND of the Mertens mass has
`∑ ‖1 − u(p)‖/p ≤ (1/4)·∑ 1/p`.

The certificate is exact: `√(2P)·√(P/32) = √(P²/16) = P/4`. -/
lemma budget_le_quarter_abstract {S : Finset ℕ} {u : ℕ → ℂ}
    (hS : ∀ p ∈ S, 0 < p) (hu : ∀ p ∈ S, ‖u p‖ ≤ 1)
    (hM : ∑ p ∈ S, (1 - (u p).re) / (p : ℝ) ≤ (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) / 32) :
    ∑ p ∈ S, ‖1 - u p‖ / (p : ℝ) ≤ (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) / 4 := by
  have hP0 : (0 : ℝ) ≤ ∑ p ∈ S, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hM0 : (0 : ℝ) ≤ ∑ p ∈ S, (1 - (u p).re) / (p : ℝ) :=
    Finset.sum_nonneg fun p hp =>
      div_nonneg (by linarith [le_trans (Complex.re_le_norm (u p)) (hu p hp)])
        (Nat.cast_nonneg p)
  have hCS := sum_norm_one_sub_div_le S u hS hu
  have h2 : (∑ p ∈ S, (2 : ℝ) / (p : ℝ)) = 2 * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [h2] at hCS
  refine hCS.trans ?_
  rw [← Real.sqrt_mul (by positivity)]
  calc Real.sqrt (2 * (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) * ∑ p ∈ S, (1 - (u p).re) / (p : ℝ))
      ≤ Real.sqrt (((∑ p ∈ S, (1 : ℝ) / (p : ℝ)) / 4) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) / 4 := Real.sqrt_sq (by linarith)

/-- **The budget's quarter-cut at the primes `≤ x`** — the pocket's cap in the Mertens-mass
convention `P(x)/32`, delivered in `renormalise`'s own `(Icc 1 ⌊x⌋₊).filter Prime` shape.
(The `α = 1/32` twin of `BallSup.budget_le_half`.) -/
lemma budget_le_quarter {u : ℕ → ℂ} {x : ℝ} (hu : ∀ p, ‖u p‖ ≤ 1)
    (hM : pretDistSq u (fun _ => 1) x ≤ Salt.Mertens.SPartial x / 32) :
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - u p‖ / (p : ℝ)
      ≤ Salt.Mertens.SPartial x / 4 := by
  have hMeq : pretDistSq u (fun _ => 1) x
      = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 - (u p).re) / (p : ℝ) := by
    unfold pretDistSq
    exact Finset.sum_congr rfl fun p _ => by rw [map_one, mul_one]
  rw [hMeq] at hM
  unfold Salt.Mertens.SPartial at hM ⊢
  rw [primes_Icc_eq_range]
  exact budget_le_quarter_abstract (fun p hp => (Finset.mem_filter.mp hp).2.pos)
    (fun p _ => hu p) hM

/-- **The exponentiated budget at `α = 1/32` (the T-2 headline).**  Under the pocket's cap in
Mertens-mass form the GS 7.1 error factor is `(log x)^{1/4}`-grade:

  `exp(∑_{p≤x} ‖1 − u(p)‖/p) ≤ (log x)^{1/4}·exp(M₂/4 + 3)`,

`M₂` the Meissel–Mertens constant.  Composed with GS 7.1's `x/log x` prefactor this is the
`q = 3/4` denominator — the whole content of R3.  (Twin of `BallSup.exp_budget_le`, whose
`(log x)^{1/2}·e^{M₂/2+6}` is the `q = 1/2` grade.) -/
lemma exp_budget_le_34 {u : ℕ → ℂ} {x : ℝ} (hx : 3 ≤ x) (hu : ∀ p, ‖u p‖ ≤ 1)
    (hM : pretDistSq u (fun _ => 1) x ≤ Salt.Mertens.SPartial x / 32) :
    Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - u p‖ / (p : ℝ))
      ≤ (Real.log x) ^ ((1 : ℝ) / 4) * Real.exp (Salt.Mertens.mertensM / 4 + 3) := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hE : Real.exp 1 ≤ x := by
    have := Real.exp_one_lt_d9
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hE
  have hmert := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hx2)
  have h12 : 12 / Real.log x ≤ 12 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hb := budget_le_quarter hu hM
  have hstep : (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - u p‖ / (p : ℝ))
      ≤ Real.log (Real.log x) / 4 + (Salt.Mertens.mertensM / 4 + 3) := by
    linarith [hmert.2]
  have hquarter : Real.exp (Real.log (Real.log x) / 4) = (Real.log x) ^ ((1 : ℝ) / 4) := by
    rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < Real.log x)]
    congr 1
    ring
  calc Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - u p‖ / (p : ℝ))
      ≤ Real.exp (Real.log (Real.log x) / 4 + (Salt.Mertens.mertensM / 4 + 3)) :=
        Real.exp_le_exp.mpr hstep
    _ = Real.exp (Real.log (Real.log x) / 4) * Real.exp (Salt.Mertens.mertensM / 4 + 3) :=
        Real.exp_add _ _
    _ = (Real.log x) ^ ((1 : ℝ) / 4) * Real.exp (Salt.Mertens.mertensM / 4 + 3) := by
        rw [hquarter]

/-! ## §3 (T-3) — the transfer at the `3/4` denominator -/

/-- The `α = 1/32` error constant: GS 7.1's `C` times the sharper Mertens exponential.
(Twin of `BallSup.ballSupC = renormaliseConst·e^{M₂/2+6}`.) -/
noncomputable def ballSupC34 : ℝ := renormaliseConst * Real.exp (Salt.Mertens.mertensM / 4 + 3)

lemma ballSupC34_pos : 0 < ballSupC34 := by
  have h28 : (28 : ℝ) ≤ renormaliseConst := by
    rw [renormaliseConst_eq]
    nlinarith [one_le_exp_eight, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  exact mul_pos (by linarith) (Real.exp_pos _)

/-- **The error majorant at `q = 3/4`.**
`ballErr34 x r = C₃₄·(x/(log x)^{3/4})·(1 + log(3 + r(1+log x)))` — GS 7.1's error with the
`(log x)^{1/4}` budget already substituted (`exp_budget_le_34`) and the
`x/log x · (log x)^{1/4} = x/(log x)^{3/4}` collapse performed.  (Twin of `BallSup.ballErr`,
whose denominator is `√(log x)`.) -/
noncomputable def ballErr34 (x r : ℝ) : ℝ :=
  ballSupC34 * (x / (Real.log x) ^ ((3 : ℝ) / 4)) * (1 + Real.log (3 + r * (1 + Real.log x)))

/-- `x/L·L^{1/4} = x/L^{3/4}` — the collapse that turns GS 7.1's `x/log x` prefactor and the
`(log x)^{1/4}` budget into the `q = 3/4` grade.  (Twin of `BallSup.div_log_mul_sqrt`.) -/
lemma div_log_mul_rpow_quarter (x : ℝ) {L : ℝ} (hL : 0 < L) :
    x / L * L ^ ((1 : ℝ) / 4) = x / L ^ ((3 : ℝ) / 4) := by
  have h34 : (0 : ℝ) < L ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL _
  have hsum : L ^ ((1 : ℝ) / 4) * L ^ ((3 : ℝ) / 4) = L := by
    rw [← Real.rpow_add hL, show (1 : ℝ) / 4 + (3 : ℝ) / 4 = 1 by norm_num, Real.rpow_one]
  rw [div_mul_eq_mul_div, div_eq_div_iff (ne_of_gt hL) (ne_of_gt h34), mul_assoc, hsum]

/-- **T-3 — the transfer at one scale, with the error already in `ballErr34` form.**  The
consumable one-scale statement at the POCKET's own cap: under `𝔻² ≤ P(x)/32` at scale `x`,
the whole GS 7.1 error is `≤ ballErr34 x |t−t₁|`, i.e. `≪ x/(log x)^{3/4}` up to the
`log(3 + |t−t₁|(1+log x))` factor.  (Twin of `BallSup.transfer_at_scale`, which pays
`x/√(log x)`.) -/
theorem transfer_at_scale_34 {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b)
    (hfle : ∀ n, ‖f n‖ ≤ 1) {t t₁ x : ℝ} (hx : 3 ≤ x)
    (hM : pretDistSq (fun n => f n * eIu (-t₁) n) (fun _ => 1) x
      ≤ Salt.Mertens.SPartial x / 32) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * eIu (-t) n‖
      ≤ Real.sqrt 2 / (1 + |t - t₁|) * ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * eIu (-t₁) n‖
        + ballErr34 x |t - t₁| := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hE : Real.exp 1 ≤ x := by
    have := Real.exp_one_lt_d9
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hE
  have hu : ∀ p, ‖f p * eIu (-t₁) p‖ ≤ 1 := by
    intro p
    rw [norm_mul, norm_eIu, mul_one]
    exact hfle p
  have hbud := exp_budget_le_34 hx hu hM
  refine (center_to_ball_transfer hf1 hfmul hfle t t₁ hx2).trans ?_
  have hpre : (0 : ℝ) ≤ renormaliseConst * (x / Real.log x)
      * (1 + Real.log (3 + |t - t₁| * (1 + Real.log x))) := by
    have h28 : (28 : ℝ) ≤ renormaliseConst := by
      rw [renormaliseConst_eq]
      nlinarith [one_le_exp_eight, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
    have hL : (1 : ℝ) ≤ 3 + |t - t₁| * (1 + Real.log x) := by
      nlinarith [abs_nonneg (t - t₁)]
    have := Real.log_nonneg hL
    have hxl : (0 : ℝ) ≤ x / Real.log x := by positivity
    have : (0 : ℝ) ≤ 1 + Real.log (3 + |t - t₁| * (1 + Real.log x)) := by linarith
    positivity
  have hkey : renormaliseConst * (x / Real.log x)
        * (1 + Real.log (3 + |t - t₁| * (1 + Real.log x)))
        * Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ‖1 - f p * eIu (-t₁) p‖ / p)
      ≤ ballErr34 x |t - t₁| := by
    refine (mul_le_mul_of_nonneg_left hbud hpre).trans (le_of_eq ?_)
    unfold ballErr34 ballSupC34
    rw [← div_log_mul_rpow_quarter x (by linarith : (0 : ℝ) < Real.log x)]
    ring
  linarith

/-! ## §4 (T-4) — the CASE-B far transfer at the `3/4` denominator

`CofactorBall`:175/:217, re-run at `ballErr34`.  The far arm pays the GS 7.1 error
ADDITIVELY (never multiplied by the weight), so the whole gain of R3 lands directly on the
exit constant: `farErr34` has `(log W)^{3/4}` where `farErr` has `√(log W)`. -/

/-- **The additively-paid GS 7.1 error at `q = 3/4`.**  `farErr34 W Y Rmax` majorises the SUM
of the two transfer errors (at the two endpoints of the window `[W, Y]`), divided by the
length: it is `4·ballSupC34·(1 + log(3 + Rmax(1+log Y)))/(log W)^{3/4}`, of grade
`(log W)^{−3/4}·log(Rmax·log Y)`.  (Twin of `CofactorBall.farErr`, whose denominator is
`√(log W)`.) -/
noncomputable def farErr34 (W Y Rmax : ℝ) : ℝ :=
  4 * ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log Y))) / (Real.log W) ^ ((3 : ℝ) / 4)

/-- **The CASE-B exit constant at `q = 3/4`.**  `farSupS34 W Y Rmax R = 2√2/R + farErr34`:
the trivial centre bound `S₀ = 1` transferred at radius `≥ R` (main term, UNCHANGED by R3),
plus the additive GS 7.1 error at the sharper denominator. -/
noncomputable def farSupS34 (W Y Rmax R : ℝ) : ℝ := 2 * Real.sqrt 2 / R + farErr34 W Y Rmax

/-- Nonnegativity.  Unlike `farErr_nonneg` this needs `0 ≤ log W`: the denominator is an
`rpow`, not a `sqrt`, so its own sign is not free. -/
lemma farErr34_nonneg {W Y Rmax : ℝ} (hW : 0 < Real.log W) (hY : 0 ≤ Real.log Y)
    (hRmax : 0 ≤ Rmax) : 0 ≤ farErr34 W Y Rmax := by
  have h1 : (1 : ℝ) ≤ 3 + Rmax * (1 + Real.log Y) := by nlinarith
  have h2 : 0 ≤ Real.log (3 + Rmax * (1 + Real.log Y)) := Real.log_nonneg h1
  have h3 := ballSupC34_pos
  have h4 : (0 : ℝ) < (Real.log W) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hW _
  unfold farErr34
  positivity

lemma farSupS34_nonneg {W Y Rmax R : ℝ} (hR : 0 < R) (hW : 0 < Real.log W)
    (hY : 0 ≤ Real.log Y) (hRmax : 0 ≤ Rmax) : 0 ≤ farSupS34 W Y Rmax R := by
  have h1 := farErr34_nonneg (W := W) hW hY hRmax
  have h2 : (0 : ℝ) ≤ 2 * Real.sqrt 2 / R := by positivity
  unfold farSupS34
  linarith

/-- **T-4 — THE RADIUS TRANSFER at `q = 3/4`.**  A window datum `a` (supported in `(k₀, M]`,
where it agrees with a 1-bounded multiplicative `f`) whose centre `t₁'` satisfies the
POCKET's cap in Mertens-mass form `𝔻² ≤ P(y)/32` on the whole window has

  `‖A_t(m)‖ ≤ farSupS34 k₀ M Rmax R · m`   for all `m ≤ M`,

whenever `R ≤ 1 + |t − t₁'|` and `|t − t₁'| ≤ Rmax`.  The centre input is again the TRIVIAL
bound (`center_trivial_bound`, `S₀ = 1`).  Twin of `CofactorBall.far_transfer_sup`; the ONLY
changes are `P/8 ↝ P/32`, `ballErr ↝ ballErr34`, `√(log k₀) ↝ (log k₀)^{3/4}`. -/
theorem far_transfer_sup_34 {M k₀ : ℕ} {a f : ℕ → ℂ} {t t₁' Rmax R : ℝ}
    (hk₀ : 3 ≤ k₀) (hMk : (M : ℝ) ≤ 2 * (k₀ : ℝ))
    (hf1 : f 1 = 1) (hfmul : ∀ p q : ℕ, Nat.Coprime p q → f (p * q) = f p * f q)
    (hfle : ∀ n, ‖f n‖ ≤ 1)
    (hsupp : ∀ n : ℕ, n ≤ k₀ → a n = 0)
    (hDatum : ∀ n : ℕ, k₀ < n → n ≤ M → a n = f n)
    (hMball : ∀ y : ℝ, (k₀ : ℝ) ≤ y → y ≤ (M : ℝ) →
      pretDistSq (fun n => f n * eIu (-t₁') n) (fun _ => 1) y
        ≤ Salt.Mertens.SPartial y / 32)
    (hR0 : 0 < R) (hRle : R ≤ 1 + |t - t₁'|) (hRmax : |t - t₁'| ≤ Rmax) :
    ∀ m : ℕ, m ≤ M → ‖spolyA a t m‖ ≤ farSupS34 (k₀ : ℝ) (M : ℝ) Rmax R * (m : ℝ) := by
  intro m hm
  have hk₀R : (3 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
  have hr0 : (0 : ℝ) ≤ |t - t₁'| := abs_nonneg _
  have hRmax0 : (0 : ℝ) ≤ Rmax := le_trans hr0 hRmax
  have hMR : (0 : ℝ) ≤ Real.log (M : ℝ) := log_natCast_nonneg M
  have hlogk : (0 : ℝ) < Real.log (k₀ : ℝ) := Real.log_pos (by linarith)
  have hSnn : 0 ≤ farSupS34 (k₀ : ℝ) (M : ℝ) Rmax R := farSupS34_nonneg hR0 hlogk hMR hRmax0
  rcases le_or_gt m k₀ with hcase | hcase
  · -- below the window the polynomial is empty
    have hz : spolyA a t m = 0 := by
      unfold spolyA
      refine Finset.sum_eq_zero fun n hn => ?_
      have hnm : n ≤ m := (Finset.mem_Icc.mp hn).2
      rw [hsupp n (le_trans hnm hcase), zero_div]
    rw [hz, norm_zero]
    positivity
  · -- the live range `k₀ < m ≤ M ≤ 2k₀`
    have hkm : k₀ ≤ m := hcase.le
    have hmR : (k₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    have hmM : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm
    have hm3 : (3 : ℝ) ≤ (m : ℝ) := le_trans hk₀R hmR
    have hM2m : (M : ℝ) ≤ 2 * (m : ℝ) := le_trans hMk (by linarith)
    have hd : (0 : ℝ) < 1 + |t - t₁'| := by positivity
    have hsk : (0 : ℝ) < (Real.log (k₀ : ℝ)) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hlogk _
    -- the datum split
    have hsplit := spolyA_window_split hsupp hDatum t hkm hm
    -- the transfer at scale `m`
    have hAm : ‖∑ n ∈ Finset.Icc 1 m, f n * eIu (-t) n‖
        ≤ Real.sqrt 2 / (1 + |t - t₁'|) * (1 * (m : ℝ)) + ballErr34 (m : ℝ) |t - t₁'| := by
      have h := transfer_at_scale_34 hf1 hfmul hfle (t := t) (t₁ := t₁') (x := (m : ℝ)) hm3
        (hMball (m : ℝ) hmR hmM)
      rw [Nat.floor_natCast] at h
      refine h.trans ?_
      have hq : (0 : ℝ) ≤ Real.sqrt 2 / (1 + |t - t₁'|) := by positivity
      have := mul_le_mul_of_nonneg_left (center_trivial_bound hfle t₁' m) hq
      linarith
    -- the transfer at scale `k₀`
    have hAk : ‖∑ n ∈ Finset.Icc 1 k₀, f n * eIu (-t) n‖
        ≤ Real.sqrt 2 / (1 + |t - t₁'|) * (1 * (m : ℝ)) + ballErr34 (k₀ : ℝ) |t - t₁'| := by
      have h := transfer_at_scale_34 hf1 hfmul hfle (t := t) (t₁ := t₁') (x := (k₀ : ℝ)) hk₀R
        (hMball (k₀ : ℝ) le_rfl (le_trans hmR hmM))
      rw [Nat.floor_natCast] at h
      refine h.trans ?_
      have hq : (0 : ℝ) ≤ Real.sqrt 2 / (1 + |t - t₁'|) := by positivity
      have hc := center_trivial_bound hfle t₁' k₀
      have hmono : 1 * (k₀ : ℝ) ≤ 1 * (m : ℝ) := by linarith
      have := mul_le_mul_of_nonneg_left (le_trans hc hmono) hq
      linarith
    -- the error majorant, uniform on the window
    have herr : ∀ y : ℝ, (k₀ : ℝ) ≤ y → y ≤ (M : ℝ) →
        ballErr34 y |t - t₁'|
          ≤ ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))))
              / (Real.log (k₀ : ℝ)) ^ ((3 : ℝ) / 4) * (M : ℝ) := by
      intro y hy1 hy2
      have hy0 : (0 : ℝ) < y := by linarith
      have hlogy : (0 : ℝ) < Real.log y :=
        lt_of_lt_of_le hlogk (Real.log_le_log (by linarith) hy1)
      have hsy : (Real.log (k₀ : ℝ)) ^ ((3 : ℝ) / 4) ≤ (Real.log y) ^ ((3 : ℝ) / 4) :=
        Real.rpow_le_rpow hlogk.le (Real.log_le_log (by linarith) hy1) (by norm_num)
      have hlogM : Real.log y ≤ Real.log (M : ℝ) := Real.log_le_log hy0 hy2
      -- (i) the `y/(log y)^{3/4}` factor
      have hq : y / (Real.log y) ^ ((3 : ℝ) / 4)
          ≤ (M : ℝ) / (Real.log (k₀ : ℝ)) ^ ((3 : ℝ) / 4) := by
        rw [div_le_div_iff₀ (lt_of_lt_of_le hsk hsy) hsk]
        have ha : y * (Real.log (k₀ : ℝ)) ^ ((3 : ℝ) / 4)
            ≤ (M : ℝ) * (Real.log (k₀ : ℝ)) ^ ((3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right hy2 hsk.le
        have hb : (M : ℝ) * (Real.log (k₀ : ℝ)) ^ ((3 : ℝ) / 4)
            ≤ (M : ℝ) * (Real.log y) ^ ((3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left hsy (by linarith)
        linarith
      -- (ii) the log factor
      have hprod0 : (0 : ℝ) ≤ |t - t₁'| * (1 + Real.log y) :=
        mul_nonneg hr0 (by linarith)
      have hin1 : (0 : ℝ) < 3 + |t - t₁'| * (1 + Real.log y) := by linarith
      have hin2 : 3 + |t - t₁'| * (1 + Real.log y)
          ≤ 3 + Rmax * (1 + Real.log (M : ℝ)) := by
        have := mul_le_mul hRmax (by linarith : 1 + Real.log y ≤ 1 + Real.log (M : ℝ))
          (by linarith) hRmax0
        linarith
      have hlogfac : 1 + Real.log (3 + |t - t₁'| * (1 + Real.log y))
          ≤ 1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))) := by
        have := Real.log_le_log hin1 hin2
        linarith
      have hnn1 : (0 : ℝ) ≤ 1 + Real.log (3 + |t - t₁'| * (1 + Real.log y)) := by
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 3 + |t - t₁'| * (1 + Real.log y))
        linarith
      have hq0 : (0 : ℝ) ≤ y / (Real.log y) ^ ((3 : ℝ) / 4) := by positivity
      have hC := ballSupC34_pos
      calc ballErr34 y |t - t₁'|
          = ballSupC34 * (y / (Real.log y) ^ ((3 : ℝ) / 4))
              * (1 + Real.log (3 + |t - t₁'| * (1 + Real.log y))) := rfl
        _ ≤ ballSupC34 * ((M : ℝ) / (Real.log (k₀ : ℝ)) ^ ((3 : ℝ) / 4))
              * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ)))) := by gcongr
        _ = ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))))
              / (Real.log (k₀ : ℝ)) ^ ((3 : ℝ) / 4) * (M : ℝ) := by ring
    -- assemble
    have hEm := herr (m : ℝ) hmR hmM
    have hEk := herr (k₀ : ℝ) le_rfl (le_trans hmR hmM)
    have hnorm : ‖spolyA a t m‖
        ≤ ‖∑ n ∈ Finset.Icc 1 m, f n * eIu (-t) n‖
          + ‖∑ n ∈ Finset.Icc 1 k₀, f n * eIu (-t) n‖ := by
      rw [hsplit]
      exact norm_sub_le _ _
    -- the main term: `1/(1+|t−t₁'|) ≤ 1/R`
    have hwt : Real.sqrt 2 / (1 + |t - t₁'|) ≤ Real.sqrt 2 / R := by
      have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      exact div_le_div_of_nonneg_left h2 hR0 hRle
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := by linarith
    have hmain : Real.sqrt 2 / (1 + |t - t₁'|) * (1 * (m : ℝ))
        ≤ Real.sqrt 2 / R * (m : ℝ) := by
      have := mul_le_mul_of_nonneg_right hwt hmnn
      linarith
    -- the error term: `M ≤ 2m`
    have hAnn : (0 : ℝ) ≤ ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))))
        / (Real.log (k₀ : ℝ)) ^ ((3 : ℝ) / 4) := by
      have hC := ballSupC34_pos
      have h1 : (1 : ℝ) ≤ 3 + Rmax * (1 + Real.log (M : ℝ)) := by nlinarith
      have := Real.log_nonneg h1
      positivity
    have herr2 : ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))))
          / (Real.log (k₀ : ℝ)) ^ ((3 : ℝ) / 4) * (M : ℝ)
        ≤ ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))))
          / (Real.log (k₀ : ℝ)) ^ ((3 : ℝ) / 4) * (2 * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hM2m hAnn
    have hexp : farSupS34 (k₀ : ℝ) (M : ℝ) Rmax R * (m : ℝ)
        = 2 * (Real.sqrt 2 / R * (m : ℝ))
          + 2 * (ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))))
              / (Real.log (k₀ : ℝ)) ^ ((3 : ℝ) / 4) * (2 * (m : ℝ))) := by
      unfold farSupS34 farErr34
      ring
    linarith

/-- **T-4, THE BINDER THAT CONSUMES THE POCKET'S CAP DIRECTLY.**  `far_transfer_sup_34` with
its `hMball` discharged FROM the pocket's own datum `𝔻²(f, p^{it₁'}; X) ≤ (1/32 − θ)loglog X`
— the cap `CofactorSupply.pocket_transport`'s CASE-B branch actually produces, and which the
landed route immediately throws away into `P(y)/8`.

Three moves, exactly the ones `pocket_transport` makes: the twist slot
(`CenterSupply.pretDistSq_twist_slot`), the FREE scale descent (`pretDistSq_mono_scale`,
`y ≤ M ≤ X`), and the conversion (`thirtysecond_cap_to_SPartial`) — the last at the SHARP
`P/32` convention rather than the crude `P/8`.

Both gates are in-statement (law #253): the threshold `exp(exp 165) ≤ k₀` and the conversion
gate `18 + (loglog X − loglog k₀) ≤ 32θ·loglog X`, the second charging the window's own loglog
descent.  At `θ = θ₂₉₃` the gate is `(18 + gap)(3e+1) ≤ loglog X`, discharged by
`thirtysecond_cap_to_SPartial_293_descent`. -/
theorem far_transfer_sup_34_of_pocket_cap {M k₀ : ℕ} {a f : ℕ → ℂ} {t t₁' Rmax R X θ : ℝ}
    (hMk : (M : ℝ) ≤ 2 * (k₀ : ℝ))
    (hf1 : f 1 = 1) (hfmul : ∀ p q : ℕ, Nat.Coprime p q → f (p * q) = f p * f q)
    (hfle : ∀ n, ‖f n‖ ≤ 1)
    (hsupp : ∀ n : ℕ, n ≤ k₀ → a n = 0)
    (hDatum : ∀ n : ℕ, k₀ < n → n ≤ M → a n = f n)
    (hk₀th : ballQuarterThreshold ≤ (k₀ : ℝ)) (hMX : (M : ℝ) ≤ X)
    (hgate : 18 + Real.log (Real.log X) - Real.log (Real.log (k₀ : ℝ))
      ≤ 32 * θ * Real.log (Real.log X))
    (hcap : pretDistSq f (costwist t₁') X ≤ (1 / 32 - θ) * Real.log (Real.log X))
    (hR0 : 0 < R) (hRle : R ≤ 1 + |t - t₁'|) (hRmax : |t - t₁'| ≤ Rmax) :
    ∀ m : ℕ, m ≤ M → ‖spolyA a t m‖ ≤ farSupS34 (k₀ : ℝ) (M : ℝ) Rmax R * (m : ℝ) := by
  have hk₀R : (3 : ℝ) ≤ (k₀ : ℝ) := le_trans three_le_ballQuarterThreshold hk₀th
  have hk₀ : 3 ≤ k₀ := by exact_mod_cast hk₀R
  have hlogk : (0 : ℝ) < Real.log (k₀ : ℝ) := Real.log_pos (by linarith)
  refine far_transfer_sup_34 hk₀ hMk hf1 hfmul hfle hsupp hDatum ?_ hR0 hRle hRmax
  intro y hy1 hy2
  have hcw : ∀ n : ℕ, ‖costwist t₁' n‖ ≤ 1 := fun n => le_of_eq (costwist_norm t₁' n)
  have hyth : ballQuarterThreshold ≤ y := le_trans hk₀th hy1
  have hlogy : Real.log (k₀ : ℝ) ≤ Real.log y := Real.log_le_log (by linarith) hy1
  have hlly : Real.log (Real.log (k₀ : ℝ)) ≤ Real.log (Real.log y) :=
    Real.log_le_log hlogk hlogy
  have hmono : pretDistSq f (costwist t₁') y ≤ pretDistSq f (costwist t₁') X :=
    pretDistSq_mono_scale hfle hcw (le_trans hy2 hMX)
  have hconv := thirtysecond_cap_to_SPartial (X := X) (y := y) (θ := θ) hyth (by linarith)
  rw [← pretDistSq_twist_slot]
  linarith

/-! ## §5 (T-5) — the ambient-gate consumers at the `3/4` denominator

`USetResiduals`:515/:570, re-run at `farErr34`.  These are the shapes ⟦V6b⟧ names as the live
route after R1+R2: the far arm's gate is a bound on the ROW HEIGHT's logarithm against
`(log X)^{3/4}` instead of `(log X)^{1/2}`. -/

/-- **THE REPAIR TARGET at `q = 3/4`.**  The far arm's GS-7.1 error meets the exit grade
whenever the AMBIENT radius obeys

  `8·ballSupC34·(1 + log(3 + Rmax(1+log Y))) ≤ (log X)^{3/4 − ρ₂₉₃}  ⟹  farErr34 ≤ (log X)^{−ρ₂₉₃}`,

using only `log kmin ≥ (1/2)log X` (the descent gate's own consequence).  The front constant
is still `8` because `(1/2)^{3/4} ≥ 1/2`.  Twin of `USetResiduals.farErr_le_of_ambient_gate`,
whose right-hand exponent is `1/2 − ρ₂₉₃` — **this is exactly the quarter-power of room R3
buys.** -/
theorem farErr34_le_of_ambient_gate {X kmin Ymax Dmax : ℝ}
    (hL1 : 1 ≤ Real.log X) (hk1 : 1 < kmin) (hD0 : 0 ≤ Dmax) (hY1 : 1 ≤ Ymax)
    (hhalf : 1 / 2 * Real.log X ≤ Real.log kmin)
    (hamb : 8 * ballSupC34 * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax)))
      ≤ (Real.log X) ^ ((3 : ℝ) / 4 - rho293)) :
    farErr34 kmin Ymax (Dmax + 1) ≤ (Real.log X) ^ (-rho293) := by
  have hC0 : (0 : ℝ) < ballSupC34 := ballSupC34_pos
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hk0 : (0 : ℝ) < Real.log kmin := Real.log_pos hk1
  have hs0 : (0 : ℝ) < (Real.log X) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
  have hhalf0 : (0 : ℝ) < 1 / 2 * (Real.log X) ^ ((3 : ℝ) / 4) := by linarith
  -- `(log kmin)^{3/4} ≥ (1/2)·(log X)^{3/4}`, because `(1/2)^{3/4} ≥ 1/2`
  have hden : 1 / 2 * (Real.log X) ^ ((3 : ℝ) / 4) ≤ (Real.log kmin) ^ ((3 : ℝ) / 4) := by
    have hhalf34 : (1 : ℝ) / 2 ≤ ((1 : ℝ) / 2) ^ ((3 : ℝ) / 4) := by
      have h := Real.rpow_le_rpow_of_exponent_ge (x := (1 : ℝ) / 2) (by norm_num) (by norm_num)
        (show (3 : ℝ) / 4 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    have hmulr : ((1 : ℝ) / 2 * Real.log X) ^ ((3 : ℝ) / 4)
        = ((1 : ℝ) / 2) ^ ((3 : ℝ) / 4) * (Real.log X) ^ ((3 : ℝ) / 4) :=
      Real.mul_rpow (by norm_num) hL0.le
    calc 1 / 2 * (Real.log X) ^ ((3 : ℝ) / 4)
        ≤ ((1 : ℝ) / 2) ^ ((3 : ℝ) / 4) * (Real.log X) ^ ((3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right hhalf34 hs0.le
      _ = ((1 : ℝ) / 2 * Real.log X) ^ ((3 : ℝ) / 4) := hmulr.symm
      _ ≤ (Real.log kmin) ^ ((3 : ℝ) / 4) :=
          Real.rpow_le_rpow (by positivity) hhalf (by norm_num)
  -- the numerator's non-negativity
  have hY0 : (0 : ℝ) ≤ Real.log Ymax := Real.log_nonneg hY1
  have hargpos : (1 : ℝ) ≤ 3 + (Dmax + 1) * (1 + Real.log Ymax) := by nlinarith
  have hlognn : (0 : ℝ) ≤ Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax)) :=
    Real.log_nonneg hargpos
  have hnum0 : (0 : ℝ)
      ≤ 4 * ballSupC34 * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax))) := by
    positivity
  have hstep : farErr34 kmin Ymax (Dmax + 1)
      ≤ 4 * ballSupC34 * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax)))
        / (1 / 2 * (Real.log X) ^ ((3 : ℝ) / 4)) := by
    rw [farErr34]
    exact div_le_div_of_nonneg_left hnum0 hhalf0 hden
  have hform : 4 * ballSupC34 * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax)))
        / (1 / 2 * (Real.log X) ^ ((3 : ℝ) / 4))
      = (8 * ballSupC34 * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax))))
        * ((Real.log X) ^ ((3 : ℝ) / 4))⁻¹ := by
    field_simp
    ring
  have hinv0 : (0 : ℝ) ≤ ((Real.log X) ^ ((3 : ℝ) / 4))⁻¹ := by positivity
  have hlast : (Real.log X) ^ ((3 : ℝ) / 4 - rho293) * ((Real.log X) ^ ((3 : ℝ) / 4))⁻¹
      = (Real.log X) ^ (-rho293) := by
    rw [← Real.rpow_neg hL0.le, ← Real.rpow_add hL0]
    congr 1
    ring
  calc farErr34 kmin Ymax (Dmax + 1)
      ≤ (8 * ballSupC34 * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax))))
        * ((Real.log X) ^ ((3 : ℝ) / 4))⁻¹ := by rw [← hform]; exact hstep
    _ ≤ (Real.log X) ^ ((3 : ℝ) / 4 - rho293) * ((Real.log X) ^ ((3 : ℝ) / 4))⁻¹ :=
        mul_le_mul_of_nonneg_right hamb hinv0
    _ = (Real.log X) ^ (-rho293) := hlast

/-- **The fused `Rbd` at `q = 3/4`** — `CofactorSupply.cofactorRbd` with the far arm's exit
constant replaced by its `3/4` twin.  (A NEW definition, not an edit: the landed `cofactorRbd`
is untouched.) -/
noncomputable def cofactorRbd34 (c Cb X θ W Y Rmax R : ℝ) : ℝ :=
  3 * max (2 * caseAS c Cb (cofactorMfl X θ W) W) (farSupS34 W Y Rmax R)

/-- **R-1 at `q = 3/4`** — `R̄₃₄ ≤ C_R·(log X)^{−ρ₂₉₃}` at the pin `c = 1/e`, with the SAME
explicit constant `gradeCR Cb`: the CASE-A arm is untouched (`caseAS_arm_priced`), the far
arm's main term is untouched (`farMain_priced`), and only the GS-7.1 error moves — it enters
through the stated gate `hfar34`.  Twin of `USetResiduals.Rbd_grade_priced`. -/
theorem Rbd34_grade_priced {X Cb kmin Ymax Dmax Rrad : ℝ}
    (hCb0 : 0 ≤ Cb) (hk2 : 2 ≤ kmin) (hkX : kmin ≤ X)
    (hlX : Real.exp 2 ≤ Real.log X)
    (hgate : (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin)
    (hRlow : seamRad X ≤ Rrad)
    (hfar34 : farErr34 kmin Ymax (Dmax + 1) ≤ (Real.log X) ^ (-rho293)) :
    cofactorRbd34 (1 / Real.exp 1) Cb X theta293 kmin Ymax (Dmax + 1) Rrad
      ≤ gradeCR Cb * (Real.log X) ^ (-rho293) := by
  have he3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hL3 : (3 : ℝ) ≤ Real.log X := le_trans he3 hlX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hpow0 : (0 : ℝ) ≤ (Real.log X) ^ (-rho293) := Real.rpow_nonneg hL0.le _
  have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  set CA := gradeAbsConstC (1 / Real.exp 1) Cb * Real.exp 13 + 2 * farCStar + 8 with hCA
  have hCA0 : (0 : ℝ) ≤ CA := by
    have h1 : (0 : ℝ) ≤ gradeAbsConstC (1 / Real.exp 1) Cb := gradeAbsConstC_nonneg hc1 hCb0
    have h2 : (0 : ℝ) ≤ farCStar := farCStar_nonneg
    have h3 : (0 : ℝ) < Real.exp 13 := Real.exp_pos _
    rw [hCA]; nlinarith
  have hA := caseAS_arm_priced (X := X) (W := kmin) (Cb := Cb) hCb0 hk2 hkX hlX hgate
  have hB : farSupS34 kmin Ymax (Dmax + 1) Rrad ≤ 4 * (Real.log X) ^ (-rho293) := by
    have hm := farMain_priced (X := X) (Rrad := Rrad) hL1 hRlow
    unfold farSupS34
    linarith
  have hmax : max (2 * caseAS (1 / Real.exp 1) Cb (cofactorMfl X theta293 kmin) kmin)
      (farSupS34 kmin Ymax (Dmax + 1) Rrad) ≤ (2 * CA + 4) * (Real.log X) ^ (-rho293) := by
    refine max_le ?_ ?_
    · nlinarith [hA]
    · nlinarith [hB]
  have hCRval : gradeCR Cb = 3 * (2 * CA + 4) := by rw [gradeCR, hCA]; ring
  unfold cofactorRbd34
  rw [hCRval]
  nlinarith [hmax]

/-- **R-1 at `q = 3/4`, END-TO-END, IN A QUASI-POLYLOG-AMBIENT REGIME.**  `Rbd34_grade_priced`
with its far gate discharged from the ambient gate — the `3/4` twin of
`USetResiduals.Rbd_grade_priced_of_ambient`, and the shape ⟦V6b⟧ names as the live route once
R1 (the localized dichotomy) and R2 (the `y` re-pin) shrink `log Rmax` below `(log X)^{3/4−ρ}`. -/
theorem Rbd34_grade_priced_of_ambient {X Cb kmin Ymax Dmax Rrad : ℝ}
    (hCb0 : 0 ≤ Cb) (hk2 : 2 ≤ kmin) (hkX : kmin ≤ X) (hD0 : 0 ≤ Dmax) (hY1 : 1 ≤ Ymax)
    (hlX : Real.exp 2 ≤ Real.log X)
    (hgate : (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin)
    (hRlow : seamRad X ≤ Rrad)
    (hamb : 8 * ballSupC34 * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax)))
      ≤ (Real.log X) ^ ((3 : ℝ) / 4 - rho293)) :
    cofactorRbd34 (1 / Real.exp 1) Cb X theta293 kmin Ymax (Dmax + 1) Rrad
      ≤ gradeCR Cb * (Real.log X) ^ (-rho293) := by
  have he3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hL3 : (3 : ℝ) ≤ Real.log X := le_trans he3 hlX
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hL2 : (2 : ℝ) ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log (Real.exp_pos 2) hlX
    rwa [Real.log_exp] at h
  have hhalf : 1 / 2 * Real.log X ≤ Real.log kmin := by
    have h1 : (1 : ℝ) / Real.log (Real.log X) ≤ 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL2
    nlinarith
  exact Rbd34_grade_priced hCb0 hk2 hkX hlX hgate hRlow
    (farErr34_le_of_ambient_gate hL1 (by linarith) hD0 hY1 hhalf hamb)

/-! ### §5b — what the `3/4` denominator does to the `TannGate` collision

`USetResiduals.farErr_TannGate_floor` shows the `q = 1/2` far error is bounded BELOW by the
absolute constant `120·ballSupC` under `USetPins.TannGate` (`Tann ≥ exp(30(log X)^{1/2})`),
so `USetResiduals.ambient_cap_below_TannGate_floor` empties the repair window.  At `q = 3/4`
that collision DISSOLVES: the same numerator `≍ 30(log X)^{1/2}` against the denominator
`(log X)^{3/4}` decays like `(log X)^{−1/4}`. -/

/-- **THE COLLISION DISSOLVES AT `q = 3/4`.**  If the ambient radius is capped at the
`TannGate` FLOOR — `log(3 + Rmax(1+log Y)) ≤ 31(log X)^{1/2}`, one unit of slack above the
gate's own `30(log X)^{1/2}` — then

  `farErr34 W Y Rmax ≤ 256·ballSupC34·(log X)^{−1/4}`,

a DECAYING bound.  The `q = 1/2` twin has an absolute FLOOR of `120·ballSupC` in exactly this
regime (`USetResiduals.farErr_TannGate_floor`) — that is the whole of R3's gain, in one
inequality.  (Beating the demanded `(log X)^{−ρ₂₉₃}` from here is a matter of an explicit
`X₀`, `ρ₂₉₃ ≈ 0.0102 < 1/4`; that comparison is NOT proved here.)

It does NOT close the far arm: at the LIVE row height
`Tann ≍ X/log X` the numerator is `≍ log X`, not `≍ √(log X)`, and the twin still diverges at
`4·ballSupC34·(log X)^{1/4}`.  R1 + R2 are what shrink the numerator.) -/
theorem farErr34_at_TannGate_floor {X W Y Rmax : ℝ}
    (hL1 : 1 ≤ Real.log X) (hW : 1 < W) (hhalf : 1 / 2 * Real.log X ≤ Real.log W)
    (hY1 : 1 ≤ Y) (hRmax0 : 0 ≤ Rmax)
    (hR : Real.log (3 + Rmax * (1 + Real.log Y)) ≤ 31 * (Real.log X) ^ ((1 : ℝ) / 2)) :
    farErr34 W Y Rmax ≤ 256 * ballSupC34 * (Real.log X) ^ (-(1 : ℝ) / 4) := by
  have hC0 : (0 : ℝ) < ballSupC34 := ballSupC34_pos
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hW0 : (0 : ℝ) < Real.log W := Real.log_pos hW
  have hs0 : (0 : ℝ) < (Real.log X) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
  have hhalf0 : (0 : ℝ) < 1 / 2 * (Real.log X) ^ ((3 : ℝ) / 4) := by linarith
  have hroot1 : (1 : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hL1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [Real.one_rpow] at h
  have hden : 1 / 2 * (Real.log X) ^ ((3 : ℝ) / 4) ≤ (Real.log W) ^ ((3 : ℝ) / 4) := by
    have hhalf34 : (1 : ℝ) / 2 ≤ ((1 : ℝ) / 2) ^ ((3 : ℝ) / 4) := by
      have h := Real.rpow_le_rpow_of_exponent_ge (x := (1 : ℝ) / 2) (by norm_num) (by norm_num)
        (show (3 : ℝ) / 4 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    have hmulr : ((1 : ℝ) / 2 * Real.log X) ^ ((3 : ℝ) / 4)
        = ((1 : ℝ) / 2) ^ ((3 : ℝ) / 4) * (Real.log X) ^ ((3 : ℝ) / 4) :=
      Real.mul_rpow (by norm_num) hL0.le
    calc 1 / 2 * (Real.log X) ^ ((3 : ℝ) / 4)
        ≤ ((1 : ℝ) / 2) ^ ((3 : ℝ) / 4) * (Real.log X) ^ ((3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right hhalf34 hs0.le
      _ = ((1 : ℝ) / 2 * Real.log X) ^ ((3 : ℝ) / 4) := hmulr.symm
      _ ≤ (Real.log W) ^ ((3 : ℝ) / 4) :=
          Real.rpow_le_rpow (by positivity) hhalf (by norm_num)
  have hY0 : (0 : ℝ) ≤ Real.log Y := Real.log_nonneg hY1
  have hargpos : (1 : ℝ) ≤ 3 + Rmax * (1 + Real.log Y) := by nlinarith
  have hlognn : (0 : ℝ) ≤ Real.log (3 + Rmax * (1 + Real.log Y)) := Real.log_nonneg hargpos
  have hnum0 : (0 : ℝ) ≤ 4 * ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log Y))) := by
    positivity
  have hstep : farErr34 W Y Rmax
      ≤ 4 * ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log Y)))
        / (1 / 2 * (Real.log X) ^ ((3 : ℝ) / 4)) := by
    rw [farErr34]
    exact div_le_div_of_nonneg_left hnum0 hhalf0 hden
  have hform : 4 * ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log Y)))
        / (1 / 2 * (Real.log X) ^ ((3 : ℝ) / 4))
      = (8 * ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log Y))))
        * ((Real.log X) ^ ((3 : ℝ) / 4))⁻¹ := by
    field_simp
    ring
  have hinv0 : (0 : ℝ) ≤ ((Real.log X) ^ ((3 : ℝ) / 4))⁻¹ := by positivity
  have hnum : 8 * ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log Y)))
      ≤ 256 * ballSupC34 * (Real.log X) ^ ((1 : ℝ) / 2) := by
    have h1 : ballSupC34 * Real.log (3 + Rmax * (1 + Real.log Y))
        ≤ ballSupC34 * (31 * (Real.log X) ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hR hC0.le
    have h2 : ballSupC34 * 1 ≤ ballSupC34 * (Real.log X) ^ ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hroot1 hC0.le
    nlinarith
  have hid : (Real.log X) ^ ((1 : ℝ) / 2) * ((Real.log X) ^ ((3 : ℝ) / 4))⁻¹
      = (Real.log X) ^ (-(1 : ℝ) / 4) := by
    rw [← Real.rpow_neg hL0.le, ← Real.rpow_add hL0]
    congr 1
    ring
  calc farErr34 W Y Rmax
      ≤ (8 * ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log Y))))
        * ((Real.log X) ^ ((3 : ℝ) / 4))⁻¹ := by rw [← hform]; exact hstep
    _ ≤ (256 * ballSupC34 * (Real.log X) ^ ((1 : ℝ) / 2))
        * ((Real.log X) ^ ((3 : ℝ) / 4))⁻¹ := mul_le_mul_of_nonneg_right hnum hinv0
    _ = 256 * ballSupC34 * (Real.log X) ^ (-(1 : ℝ) / 4) := by rw [mul_assoc, hid]

end Salt.MR
