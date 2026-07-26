/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RHSGradeC
import Salt.MR.SupClose
import Salt.MR.JointPlumb

/-!
# The `c`-GENERIC grade CLOSE — the window-floor exit (`GradeWindowC`)

`RHSGradeC` (W4-1/2/3) frees the exponent `c` in the two `c`-carrying suppliers of the
joint-head grade.  This file closes the `c`-generic supplier: the grade AT SCALE in
**window-floor form**, the `c`-generic integrability bundle, and the grade-abstract centre
supply.  Together they are the CASE-A route's whole analytic input at a free `c`.

## §1 (W4-5) — `JointIntegrableAtC` and its discharge

`RHSGrade.JointIntegrableAt` at `rhsFboundC c` in place of `rhsFbound`.  **The `c`-slot
touches components 1 and 3 only**: components 2 and 4 (the `prop21RHS` legs) mention neither
`M` nor the majorant, so they are the LANDED bundle's own, taken verbatim.  Components 1/3
go by `JointPlumb`'s continuity route against the PUBLIC `continuousAt_crossKer`, so the
measurability page (`measurable_jointIntegrandC` & co., `private` there) is never re-derived.

**FINDING (no `c`-gate).**  The two continuity legs hold at EVERY real `c`: on the pin's box
`σ = β + 1/L` is bounded away from `0`, and `rhsFboundC c M L σ` is continuous there whatever
the sign of the exponent.  `jointIntegrableAtC_pin_free` therefore carries the scale gate
`e^{64} ≤ k` and nothing else — no `hc0`, no `M`, no minimality.

## §2 (W4-4) — `rhs_grade_at_scale_windowC`

`GradeConst.rhs_grade_at_scale_const` (the `∀ t : ℝ` floor `hMt`) and `SupClose`'s truncated
form (`hmin` on `|v| ≤ R` + the recentring gate `hgate`) merge into ONE binder at a free `c`:

  `hMwin : ∀ t : ℝ, |t − t₀'| ≤ T → M ≤ 𝔻²(ellLin (damped datum), costwist (t − t₀'); k)`,

which is EXACTLY what the chain consumes — `SupClose.joint_supF_pin_trunc` (:248) spends the
floor only at truncated contour points `|t − t₀'| ≤ T`, one point at a time, and
`center_dist_floor_recentred` (:224) is precisely the seam-shaped SUPPLIER of that binder.
Stating the consumption directly drops `hXk`, `hgate`, `hmin`, `R`, `t₀`, `t₁` and `X` from
the statement: no seam geometry survives into the `c`-generic supplier, and the CASE-A
consumer may discharge `hMwin` however its own window page prefers.

The far arm rides ADDITIVELY (`joint_cs_factoring_trunc`'s own `Ffar`/`Kfar` binders,
threaded verbatim, never absorbed) — the consumer prices it.  The amplitude side is `c`-free
and is CITED, not cloned (`crossKer_width_pin_const`, `widthKamp`, `pin_width_gates`,
`bridge_adapter`, `alpha_rpow_integral_le`, `rhsAgradeConst_le`).

## §3 (W4-6) — `center_halasz_supply_B`

`CenterSupply.center_halasz_supply` with the grade factor ABSTRACTED: the numeral exponent
`C₁·e^{−(1/(2e))·𝔻²}` is replaced by an opaque nonneg `B` and the `hRHS` binder becomes
`‖prop21RHS …‖ ≤ B·k`.  The landed proof never inspects the exponent, so the clone is
`c`-FREE FOREVER after — CASE A feeds it `B := gradeAbsConstC c Cb · e^{−c·M} + (far)` and
the ball arm's `B := C₁·e^{−M/(2e)}` recovers the original.  The uniform form
(`center_halasz_supply_B_uniform`, `∃ X₀` hoisted over the centre `t₁` as in
`SupStation` §2) is the one proved; the `CenterSupply`-shaped face follows in three lines.

`CenterSupply`'s `center_error_grade` + `rpow_neg_half_eq` + `two_log_le_self` +
`twentyfive_le_exp_eight` are `private` there, and `SupStation`'s `_st` re-derivations are
`private` too, so they are re-derived here VERBATIM under a `_B` suffix; `SupClose`'s /
`GradeConst`'s pin arithmetic likewise under a `W` suffix (the house's re-derivation
convention).

**LIVE GUARD (inherited).**  Nothing here commits to a route: `hc0`/`hce`/`hc1` are the whole
`c`-contract of §1, and §2/§3 carry no exponent at all.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped Topology

/-! ## §1 (W4-5) — the `c`-generic integrability bundle

`RHSGrade.JointIntegrableAt` mentions its majorant in components 1 and 3 ONLY; components 2
and 4 are statements about the `prop21RHS` integrand alone.  So the `c`-generic bundle needs
exactly two new legs, and both go by `JointPlumb`'s CONTINUITY route — the measurability page
(`private` there) is never touched. -/

/-- `σ ↦ rhsFboundC c M L σ` at `σ = b w + 1/L` is continuous where `σ > 0`, at ANY `c`.
Re-derivation of `JointPlumb`'s private `continuousAt_rhsFbound_shiftP` at the freed
exponent (the exponent's leading factor is a constant in `w` either way). -/
private lemma continuousAt_rhsFboundC_shift {Ω : Type*} [TopologicalSpace Ω] {c M L : ℝ}
    {b : Ω → ℝ} {w₀ : Ω} (hL0 : 0 < L) (hb : ContinuousAt b w₀) (hσ : 0 < b w₀ + 1 / L) :
    ContinuousAt (fun w : Ω => rhsFboundC c M L (b w + 1 / L)) w₀ := by
  simp only [rhsFboundC]
  have hσc : ContinuousAt (fun w : Ω => b w + 1 / L) w₀ := hb.add continuousAt_const
  refine ContinuousAt.mul (continuousAt_const.mul
    (continuousAt_const.div hσc (ne_of_gt hσ))) ?_
  refine Real.continuous_exp.continuousAt.comp ?_
  refine continuousAt_const.mul ((continuousAt_const.sub ?_).sub continuousAt_const)
  exact continuousAt_const.mul (ContinuousAt.log (hσc.mul continuousAt_const)
    (ne_of_gt (mul_pos hσ hL0)))

/-- The `c`-generic `hIβ`/`hIα` integrand is continuous wherever `0 ≤ β`, `0 < c₀ − α − β`
and `0 < L` — `JointPlumb.continuousAt_fbound_mul_crossKer` at `rhsFboundC c`, against the
PUBLIC `continuousAt_crossKer` (which is `c`-free plumbing). -/
lemma continuousAt_fboundC_mul_crossKer {Ω : Type*} [TopologicalSpace Ω]
    [FirstCountableTopology Ω] {g : ℕ → ℂ} {c M L X h y c₀ t₀ : ℝ} {a b : Ω → ℝ} {w₀ : Ω}
    (hX : 1 ≤ X) (hh : 0 < h) (hL0 : 0 < L) (ha : ContinuousAt a w₀) (hb : ContinuousAt b w₀)
    (hβ0 : 0 ≤ b w₀) (hc : 0 < c₀ - a w₀ - b w₀) :
    ContinuousAt (fun w : Ω =>
      rhsFboundC c M L (b w + 1 / L) * crossKer g X h y c₀ t₀ (a w) (b w)) w₀ := by
  have hLi : (0 : ℝ) < 1 / L := by positivity
  exact (continuousAt_rhsFboundC_shift hL0 hb (by linarith)).mul
    (continuousAt_crossKer hX hh ha hb hβ0 hc)

/-- **SOCKET 1 at a FREE `c` (`hIβ`).**  `JointPlumb.intervalIntegrable_beta_leg` at
`rhsFboundC c`. -/
theorem intervalIntegrable_beta_legC {g : ℕ → ℂ} {c M L X h y c₀ t₀ η α : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hL0 : 0 < L) (hη0 : 0 ≤ η) (hc2η : 0 < c₀ - 2 * η)
    (hα : α ∈ Icc (0 : ℝ) η) :
    IntervalIntegrable (fun β => rhsFboundC c M L (β + 1 / L) * crossKer g X h y c₀ t₀ α β)
      volume 0 η := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hη0]
  rintro β ⟨hβ0, hβη⟩
  have hαη : α ≤ η := hα.2
  refine ContinuousAt.continuousWithinAt ?_
  exact continuousAt_fboundC_mul_crossKer (Ω := ℝ) (a := fun _ => α) (b := fun x => x)
    (w₀ := β) hX hh hL0 continuousAt_const continuousAt_id hβ0
    (by linarith)

/-- The `(α, β)`-box sup of the `c`-generic `hIβ` integrand, on a box slightly ENLARGED in
`α`.  Re-derivation of `JointPlumb`'s private `exists_box_bound`. -/
private lemma exists_box_boundC {g : ℕ → ℂ} {c M L X h y c₀ t₀ η : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hL0 : 0 < L) (hc2η : 0 < c₀ - 2 * η) :
    ∃ C : ℝ, ∀ α ∈ Icc (-1 : ℝ) (η + (c₀ - 2 * η) / 2), ∀ β ∈ Icc (0 : ℝ) η,
      ‖rhsFboundC c M L (β + 1 / L) * crossKer g X h y c₀ t₀ α β‖ ≤ C := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => rhsFboundC c M L (p.2 + 1 / L) * crossKer g X h y c₀ t₀ p.1 p.2)
      (Icc (-1 : ℝ) (η + (c₀ - 2 * η) / 2) ×ˢ Icc (0 : ℝ) η) := by
    rintro ⟨u, v⟩ ⟨⟨hu1, hu2⟩, hv1, hv2⟩
    refine ContinuousAt.continuousWithinAt ?_
    exact continuousAt_fboundC_mul_crossKer (a := Prod.fst) (b := Prod.snd) hX hh hL0
      continuousAt_fst continuousAt_snd hv1 (by change (0 : ℝ) < c₀ - u - v; linarith)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  exact ⟨C, fun α hα β hβ => hC (α, β) ⟨hα, hβ⟩⟩

/-- **SOCKET 3 at a FREE `c` (`hIα`).**  `JointPlumb.intervalIntegrable_alpha_leg` at
`rhsFboundC c`: the same dominated-convergence pass with the constant box bound. -/
theorem intervalIntegrable_alpha_legC {g : ℕ → ℂ} {c M L X h y c₀ t₀ η : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hL0 : 0 < L) (hη0 : 0 ≤ η) (hc2η : 0 < c₀ - 2 * η) :
    IntervalIntegrable (fun α => ∫ β in (0 : ℝ)..η,
      rhsFboundC c M L (β + 1 / L) * crossKer g X h y c₀ t₀ α β) volume 0 η := by
  obtain ⟨C, hC⟩ := exists_box_boundC (g := g) (c := c) (M := M) (L := L) (X := X) (h := h)
    (y := y) (c₀ := c₀) (t₀ := t₀) (η := η) hX hh hL0 hc2η
  have hδ0 : (0 : ℝ) < (c₀ - 2 * η) / 2 := by linarith
  have hIoc : Set.uIoc (0 : ℝ) η = Ioc 0 η := uIoc_of_le hη0
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hη0]
  rintro α₀ ⟨hα₀0, hα₀η⟩
  refine ContinuousAt.continuousWithinAt ?_
  have hρ0 : (0 : ℝ) < min 1 ((c₀ - 2 * η) / 2) := lt_min one_pos hδ0
  have hnb : Ioo (α₀ - min 1 ((c₀ - 2 * η) / 2)) (α₀ + min 1 ((c₀ - 2 * η) / 2)) ∈ 𝓝 α₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hbox : ∀ α ∈ Ioo (α₀ - min 1 ((c₀ - 2 * η) / 2)) (α₀ + min 1 ((c₀ - 2 * η) / 2)),
      α ∈ Icc (-1 : ℝ) (η + (c₀ - 2 * η) / 2) := by
    rintro α ⟨h1, h2⟩
    have hm1 : min 1 ((c₀ - 2 * η) / 2) ≤ 1 := min_le_left _ _
    have hm2 : min 1 ((c₀ - 2 * η) / 2) ≤ (c₀ - 2 * η) / 2 := min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => C) ?_ ?_ intervalIntegrable_const ?_
  · refine Filter.eventually_of_mem hnb (fun α hα => ?_)
    obtain ⟨hα1, hα2⟩ := hbox α hα
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    rw [hIoc]
    rintro β ⟨hβ0, hβη⟩
    refine ContinuousAt.continuousWithinAt ?_
    exact continuousAt_fboundC_mul_crossKer (Ω := ℝ) (a := fun _ => α) (b := fun x => x)
      (w₀ := β) hX hh hL0 continuousAt_const continuousAt_id hβ0.le
      (by linarith)
  · refine Filter.eventually_of_mem hnb (fun α hα => ?_)
    refine Filter.Eventually.of_forall (fun β hβ => ?_)
    rw [hIoc] at hβ
    exact hC α (hbox α hα) β ⟨hβ.1.le, hβ.2⟩
  · refine Filter.Eventually.of_forall (fun β hβ => ?_)
    rw [hIoc] at hβ
    obtain ⟨hβ0, hβη⟩ := hβ
    exact continuousAt_fboundC_mul_crossKer (Ω := ℝ) (a := fun x => x) (b := fun _ => β)
      (w₀ := α₀) hX hh hL0 continuousAt_id continuousAt_const hβ0.le
      (by linarith)

/-- **THE `c`-GENERIC INTEGRABILITY BUNDLE** (`JointIntegrableAtC`).
`RHSGrade.JointIntegrableAt` with the majorant freed: `rhsFboundC c` in place of
`rhsFbound`.  Components 2 and 4 are byte-identical to the landed ones — the `prop21RHS`
legs mention neither the majorant nor `M`. -/
def JointIntegrableAtC (c : ℝ) (d : ℕ → ℂ) (t₀' M k L c₀ y η h : ℝ) : Prop :=
  (∀ α ∈ Icc (0 : ℝ) η, IntervalIntegrable
      (fun β => rhsFboundC c M L (β + 1 / L) * crossKer d k h y c₀ t₀' α β) volume 0 η)
  ∧ (∀ α ∈ Icc (0 : ℝ) η, IntervalIntegrable
      (fun β => ‖(1 / (2 * Real.pi) : ℝ) • ∫ t, jointIntegrand d t₀' k h c₀ y α β t‖)
      volume 0 η)
  ∧ IntervalIntegrable (fun α => ∫ β in (0 : ℝ)..η,
      rhsFboundC c M L (β + 1 / L) * crossKer d k h y c₀ t₀' α β) volume 0 η
  ∧ IntervalIntegrable (fun α => ‖∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) •
      ∫ t, jointIntegrand d t₀' k h c₀ y α β t‖) volume 0 η

/-- **THE PIN IDENTITY (bundle).**  The landed ball-arm bundle IS the `c`-generic one at
`c = 1/(2e)` — `Iff.rfl`, as for `rhsFbound_eq_rhsFboundC`. -/
lemma jointIntegrableAt_iff_C (d : ℕ → ℂ) (t₀' M k L c₀ y η h : ℝ) :
    JointIntegrableAt d t₀' M k L c₀ y η h
      ↔ JointIntegrableAtC (1 / (2 * Real.exp 1)) d t₀' M k L c₀ y η h := Iff.rfl

/-- **THE GENERAL EXIT AT A FREE `c`** (`jointIntegrableAtC_of_gates`).  The two majorant
legs from the five geometric gates (`1 ≤ k`, `0 < h`, `0 < L`, `0 ≤ η`, `0 < c₀ − 2η`); the
two `prop21RHS` legs taken from the LANDED bundle at `M = 0`, where they are already
hypothesis-free (`JointPlumb.jointIntegrableAt_pin`).

**No `c`-gate.**  On `[0, η]` the σ-slot `β + 1/L` is bounded away from `0`, so the legs are
continuous whatever the sign of the exponent — `c` is entirely free here. -/
theorem jointIntegrableAtC_of_gates {c : ℝ} {d : ℕ → ℂ} {t₀' M k L c₀ y η h : ℝ}
    (hk : 1 ≤ k) (hh : 0 < h) (hL0 : 0 < L) (hη0 : 0 ≤ η) (hc2η : 0 < c₀ - 2 * η)
    (h24 : JointIntegrableAt d t₀' 0 k L c₀ y η h) :
    JointIntegrableAtC c d t₀' M k L c₀ y η h :=
  ⟨fun _ hα => intervalIntegrable_beta_legC hk hh hL0 hη0 hc2η hα,
   h24.2.1,
   intervalIntegrable_alpha_legC hk hh hL0 hη0 hc2η,
   h24.2.2.2⟩

/-- **W4-5 — THE `c`-GENERIC BUNDLE, DISCHARGED** (`jointIntegrableAtC_pin_free`).
`SupStation.jointIntegrableAt_pin_free`'s twin at a free exponent: at the corpus pin the four
sockets cost exactly the scale gate `e^{64} ≤ k` — no minimality, no `M`, no `c`-gate.

The `M`-freedom is `RHSGradeC.rhsFboundC_eq_exp_mul`'s content on the landed side and is not
even needed here: components 1/3 are proved outright at the caller's `M`, and components 2/4
do not mention `M` at all, so `JointPlumb.jointIntegrableAt_pin` at `M := 0` (whose floor is
`pretDistSq_nonneg`) supplies them for every `M`. -/
theorem jointIntegrableAtC_pin_free {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (c t₀' M : ℝ) {k : ℕ} (hk64 : Real.exp 64 ≤ (k : ℝ)) :
    JointIntegrableAtC c (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' M (k : ℝ)
      (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
      (1 / Real.log (Real.log (k : ℝ) ^ 4)) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 64) hk64
  have hL64 : (64 : ℝ) ≤ Real.log (k : ℝ) := by
    rw [← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk64
  have hL0 : (0 : ℝ) < Real.log (k : ℝ) := by linarith
  have hLinv0 : (0 : ℝ) < 1 / Real.log (k : ℝ) := by positivity
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by linarith [Real.add_one_le_exp (64 : ℝ)]
  have hh : (0 : ℝ) < (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by
    have : (0 : ℝ) < Real.sqrt (Real.log (k : ℝ)) := Real.sqrt_pos.mpr hL0
    positivity
  have hlogy : Real.log (Real.log (k : ℝ) ^ 4) = 4 * Real.log (Real.log (k : ℝ)) := by
    rw [Real.log_pow]; norm_num
  have he2 : Real.exp 2 ≤ 64 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hlogL2 : (2 : ℝ) ≤ Real.log (Real.log (k : ℝ)) := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) (by linarith)
  have hlogy0 : (0 : ℝ) < Real.log (Real.log (k : ℝ) ^ 4) := by rw [hlogy]; linarith
  have hη0 : (0 : ℝ) ≤ 1 / Real.log (Real.log (k : ℝ) ^ 4) := by positivity
  have hη8 : 1 / Real.log (Real.log (k : ℝ) ^ 4) ≤ 1 / 8 := by
    rw [hlogy, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 8)]
    linarith
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  refine jointIntegrableAtC_of_gates hk1 hh hL0 hη0 (by linarith)
    (jointIntegrableAt_pin hg hk64 (fun t => ?_))
  exact pretDistSq_nonneg _ _ _ (fun n => ellLin_norm_le_one _ hgtw n)
    (fun n => le_of_eq (costwist_norm _ n))

/-! ## §2 (W4-4) — the grade at scale in WINDOW-FLOOR form, at a FREE `c`

`GradeConst`'s / `SupClose`'s pin arithmetic, re-derived verbatim under a `W` suffix (both
files keep it `private`). -/

/-- `4·log L ≤ L` for `L ≥ 64`.  Re-derivation of `GradeConst`'s private
`four_log_le_selfC`. -/
private lemma four_log_le_selfW {L : ℝ} (h : 64 ≤ L) : 4 * Real.log L ≤ L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt h
  have hlog : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 := Real.log_le_sub_one_of_pos hs0
  have hhalf : Real.log (Real.sqrt L) = Real.log L / 2 := Real.log_sqrt hL0.le
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  nlinarith

/-- The pin's elementary arithmetic at the `e^{64}` gate.  Re-derivation of `GradeConst`'s
private `pin_basic64`. -/
private lemma pin_basic64W {k L y η : ℝ} (hk : Real.exp 64 ≤ k) (hL : L = Real.log k)
    (hy : y = L ^ 4) (hη : η = 1 / Real.log y) :
    0 < k ∧ 64 ≤ L ∧ (131072 : ℝ) ≤ y ∧ 0 < Real.log y ∧ 0 < η ∧ η ≤ 1 / 8
      ∧ 1 / L ≤ η ∧ L ^ 4 ≤ k := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 64) hk
  have hL64 : (64 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hy131072 : (131072 : ℝ) ≤ y := by
    rw [hy]
    have h4 : (64 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL64 4
    norm_num at h4
    linarith
  have hlogy : Real.log y = 4 * Real.log L := by rw [hy, Real.log_pow]; norm_num
  have he2 : Real.exp 2 ≤ 64 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hlogL2 : (2 : ℝ) ≤ Real.log L := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) (by linarith)
  have hlogy0 : (0 : ℝ) < Real.log y := by rw [hlogy]; linarith
  refine ⟨hk0, hL64, hy131072, hlogy0, by rw [hη]; positivity, ?_, ?_, ?_⟩
  · rw [hη, hlogy, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 8)]
    linarith
  · rw [hη, hlogy, div_le_div_iff₀ hL0 (by linarith)]
    linarith [four_log_le_selfW hL64]
  · have h1 : Real.log (L ^ 4) ≤ Real.log k := by
      rw [Real.log_pow, ← hL]; push_cast; linarith [four_log_le_selfW hL64]
    have h2 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by positivity), Real.exp_log hk0] at h2

/-- Continuity of `α ↦ a^{−α}`.  Re-derivation of `GradeConst`'s private
`continuous_rpow_negC`. -/
private lemma continuous_rpow_negW {a : ℝ} (ha : 0 < a) :
    Continuous (fun α : ℝ => a ^ (-α)) := by
  have hrw : (fun α : ℝ => a ^ (-α)) = fun α : ℝ => Real.exp (Real.log a * (-α)) := by
    funext α; rw [Real.rpow_def_of_pos ha]
  rw [hrw]
  exact Real.continuous_exp.comp (by fun_prop)

/-- The width amplitude is nonnegative.  Re-derivation of `GradeConst`'s private
`widthKamp_nonneg`. -/
private lemma widthKamp_nonnegW {Cb X h y c₀ : ℝ} (hCb0 : 0 ≤ Cb) (hX0 : 0 < X) (hh : 0 < h)
    (hy0 : 0 < y) : 0 ≤ widthKamp Cb X h y c₀ := by
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hy2 : (0 : ℝ) < y / 2 := by linarith
  have hA0 : (0 : ℝ) < (y / 2) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hy2 _
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold widthKamp widthKampBr
  have hrp : (0 : ℝ) ≤ (X + h) ^ c₀ := Real.rpow_nonneg hXh0.le _
  positivity

/-! ### The window floor and the truncated factoring at a free `c` -/

/-- **W4-4a — the pointwise pin `supF` at a FREE `c`** (`joint_supF_pin_atC`).
`RHSGradeC.joint_supF_pinC` with its floor binder taken at the ONE contour point where the
proof uses it (as `SupClose.joint_supF_pin_at` is to `RHSGrade.joint_supF_pin`): the `∀ t`
form is consumed only as `hMt t`, so the per-`t` form is a strict weakening proved by the
same page.

**The `c`-gates, in-statement (law #253):** `0 < c` and `c ≤ 1/e` — `supF_pret_pointwise`'s
own two, no more. -/
theorem joint_supF_pin_atC {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀' M k L c₀ y η : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hk : Real.exp 3 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀eq : c₀ = 1 + 1 / L)
    {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαη : α ≤ η) (hβη : β ≤ η) (t : ℝ)
    (hMt : M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k) :
    ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
          (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
          (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ rhsFboundC c M L (β + 1 / L) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 3) hk
  have hL3 : (3 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 3]; exact Real.log_le_log (Real.exp_pos 3) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hLinv3 : 1 / L ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hL0 (by norm_num : (0 : ℝ) < 3)]; linarith
  have hσ0 : (0 : ℝ) < β + 1 / L := by linarith
  -- the `y`-gates
  have hy0 : (0 : ℝ) < y := by rw [hy]; positivity
  have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hylo : Real.exp 1 ≤ y := by
    rw [hy]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL3 4]
  have hlogy : Real.log y = 4 * Real.log L := by rw [hy, Real.log_pow]; norm_num
  have hlogL1 : (1 : ℝ) ≤ Real.log L := by
    have h3 : Real.log 3 ≤ Real.log L := Real.log_le_log (by norm_num) hL3
    have h1 : (1 : ℝ) ≤ Real.log 3 := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
    linarith
  have hlogy0 : (0 : ℝ) < Real.log y := by rw [hlogy]; linarith
  have hη4 : η ≤ 1 / 4 := by
    rw [hη, hlogy]
    rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 4)]
    linarith
  -- the twisted datum is 1-bounded at primes
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  -- the scale condition `e^{1/σ} ≤ k` on `σ ≥ 1/L`
  have hσL : 1 / (β + 1 / L) ≤ L := by
    rw [div_le_iff₀ hσ0]
    have h1 : L * (1 / L) = 1 := by field_simp
    nlinarith
  have hYX : Real.exp (1 / (c₀ - 1 + β)) ≤ k := by
    rw [show c₀ - 1 + β = β + 1 / L from by rw [hc₀eq]; ring]
    calc Real.exp (1 / (β + 1 / L)) ≤ Real.exp L := Real.exp_le_exp.mpr hσL
      _ = k := by rw [hL, Real.exp_log hk0]
  have hP := supF_pret_pointwise (g := fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) (y := y)
    hgtw (c := c) (t₀ := t₀') (t := t) (X := k) (c₀ := c₀)
    (α := α) (β := β) hc0 hce
    hylo (by rw [hc₀eq]; linarith) hα0 hβ0
    (by rw [← hη]; exact hαη) (by rw [← hη]; exact hβη)
    (by rw [hc₀eq]; linarith) hYX
  rw [show c₀ - 1 + β = β + 1 / L from by rw [hc₀eq]; ring, ← hL] at hP
  refine hP.trans ?_
  unfold rhsFboundC rhsCSF
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ?_
  · nlinarith [mul_le_mul_of_nonneg_left hMt hc0.le]
  · have : (0 : ℝ) ≤ 1 / (β + 1 / L) := by positivity
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) this

/-- **W4-4b — THE WINDOW-FLOOR `hsupF` BINDER at a FREE `c`** (`joint_supF_pin_windowC`).
`TruncFactor.joint_cs_factoring_trunc`'s `hsupF` binder byte-for-byte, discharged from the
SINGLE window binder

  `hMwin : ∀ t, |t − t₀'| ≤ T → M ≤ 𝔻²(ellLin (damped datum), costwist (t − t₀'); k)`.

This is the whole content of the window-floor form: `SupClose`'s route reaches the same place
through `center_dist_floor_recentred` (`|t₁| + T ≤ R` against an on-`|v| ≤ R` minimality),
which is one SUPPLIER of `hMwin`; the chain itself needs nothing else, so nothing else is
asked.  No `t₀`, no `t₁`, no `R`, no `X`, no `⌊·⌋₊` — the seam geometry stays with the
consumer. -/
theorem joint_supF_pin_windowC {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀' M k L c₀ y η T : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hk : Real.exp 3 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀eq : c₀ = 1 + 1 / L)
    (hMwin : ∀ t : ℝ, |t - t₀'| ≤ T →
      M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k) :
    ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ, |t - t₀'| ≤ T →
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖
        ≤ rhsFboundC c M L (β + 1 / L) := by
  intro α hα β hβ t ht
  exact joint_supF_pin_atC hg hc0 hce hk hL hy hη hc₀eq hα.1 hβ.1 hα.2 hβ.2 t (hMwin t ht)

/-- **W4-4c — the TRUNCATED joint factoring at the pin, at a FREE `c`** (`joint_cs_trunc_pinC`).
`SupClose.joint_cs_trunc_pin` with the exponent freed and the window binder in place of
`hXk`/`hgate`/`hmin`.  The far arm (`Ffar`, `Kfar`, `hFar`, `hKfar`) is
`joint_cs_factoring_trunc`'s own — threaded verbatim, NOT discharged and NEVER absorbed. -/
theorem joint_cs_trunc_pinC {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀' M k L c₀ y η h T Ffar Kfar : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀eq : c₀ = 1 + 1 / L) (hh0 : 0 < h)
    (hMwin : ∀ t : ℝ, |t - t₀'| ≤ T →
      M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k)
    (hFfar0 : 0 ≤ Ffar)
    (hFar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Ffar)
    (hKfar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β T ≤ Kfar)
    (hInt : JointIntegrableAtC c (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
      t₀' M k L c₀ y η h) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' k h c₀ y η‖
      ≤ (1 / Real.pi) * (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
            rhsFboundC c M L (β + 1 / L)
              * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β)
        + (1 / Real.pi) * (η ^ 2 * (Ffar * Kfar)) := by
  obtain ⟨hIβ, hIβ', hIα, hIα'⟩ := hInt
  obtain ⟨hk0, hL64, -, -, hη0, hη8, -, -⟩ := pin_basic64W hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hk1 : (1 : ℝ) ≤ k := by
    have h65 : (65 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (64 : ℝ)]
    linarith
  have hk3 : Real.exp 3 ≤ k := by
    have h3 : Real.exp 3 ≤ Real.exp 64 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  refine joint_cs_factoring_trunc hk1 hh0 hη0.le ?_ hFfar0 ?_
    (joint_supF_pin_windowC hg hc0 hce hk3 hL hy hη hc₀eq hMwin) hFar hKfar hIβ hIβ' hIα hIα'
  · rw [hc₀eq]; linarith
  · exact fun _ _ β hβ => rhsFboundC_nonneg _ _ _ (by linarith [hβ.1])

/-! ### The `c`-generic amplitude -/

/-- **The `c`-GENERIC assembled grade** — `GradeConst.rhsAgradeConst` with the exponent
freed: `Agrade_C = (1/π)·C_S·C_F·(e^{48c}/(1−2c))·widthKamp`. -/
def rhsAgradeConstC (c Cb X h y c₀ : ℝ) : ℝ :=
  (1 / Real.pi) * rhsCSF * (Real.exp (c * 48) / (1 - 2 * c)) * widthKamp Cb X h y c₀

/-- **The `c`-GENERIC absolute grade constant** — `GradeConst.gradeAbsConst` with the
exponent freed: `C₁(c) = (1/π)·C_S·C_F·(e^{48c}/(1−2c))·1580544·(1+Cb)`.  Absolute: no `k`,
no `X`, no `L`. -/
def gradeAbsConstC (c Cb : ℝ) : ℝ :=
  (1 / Real.pi) * rhsCSF * (Real.exp (c * 48) / (1 - 2 * c)) * (1580544 * (1 + Cb))

lemma gradeAbsConstC_nonneg {c Cb : ℝ} (hc1 : 2 * c < 1) (hCb0 : 0 ≤ Cb) :
    0 ≤ gradeAbsConstC c Cb := by
  have hd : (0 : ℝ) < 1 - 2 * c := by linarith
  have hCSF : (0 : ℝ) < rhsCSF := rhsCSF_pos
  unfold gradeAbsConstC
  positivity

/-- The `c`-FREE content of `GradeConst.rhsAgradeConst_le`: at the corpus pin the width
amplitude itself obeys `widthKamp ≤ 1580544·(1+Cb)·k`.  Recovered from the landed statement
by cancelling its (positive, `c = 1/(2e)`) front factor — the `pin_rpow_scale` page is
`private` there and is NOT re-derived. -/
private lemma widthKamp_pin_le {Cb k L y h c₀ : ℝ} (hCb0 : 0 ≤ Cb) (hk : Real.exp 64 ≤ k)
    (hL : L = Real.log k) (hy : y = L ^ 4) (hh : h = k / Real.sqrt L) (hc₀ : c₀ = 1 + 1 / L) :
    widthKamp Cb k h y c₀ ≤ 1580544 * (1 + Cb) * k := by
  have hd : (0 : ℝ) < 1 - 2 * (1 / (2 * Real.exp 1)) := by
    rw [show 2 * (1 / (2 * Real.exp 1)) = 1 / Real.exp 1 from by ring]
    have h1 : 1 / Real.exp 1 < 1 := by
      rw [div_lt_one (Real.exp_pos 1)]; linarith [Real.exp_one_gt_d9]
    linarith
  have hCSF : (0 : ℝ) < rhsCSF := rhsCSF_pos
  have hF0 : (0 : ℝ) < (1 / Real.pi) * rhsCSF
      * (Real.exp (1 / (2 * Real.exp 1) * 48) / (1 - 2 * (1 / (2 * Real.exp 1)))) := by
    have hπ : (0 : ℝ) < 1 / Real.pi := by positivity
    positivity
  refine le_of_mul_le_mul_left ?_ hF0
  calc (1 / Real.pi) * rhsCSF
        * (Real.exp (1 / (2 * Real.exp 1) * 48) / (1 - 2 * (1 / (2 * Real.exp 1))))
        * widthKamp Cb k h y c₀
      = rhsAgradeConst Cb k h y c₀ := by unfold rhsAgradeConst; ring
    _ ≤ gradeAbsConst Cb * k := rhsAgradeConst_le hCb0 hk hL hy hh hc₀
    _ = (1 / Real.pi) * rhsCSF
        * (Real.exp (1 / (2 * Real.exp 1) * 48) / (1 - 2 * (1 / (2 * Real.exp 1))))
        * (1580544 * (1 + Cb) * k) := by unfold gradeAbsConst; ring

/-- **THE GRADE SOCKET AT A FREE `c`** (`rhsAgradeConstC_le`).  `GradeConst.rhsAgradeConst_le`
with the exponent freed: at the corpus pin,
`rhsAgradeConstC c Cb k h y c₀ ≤ gradeAbsConstC c Cb · k`, with `gradeAbsConstC c Cb` free of
`k`.  The `c`-gate is `2c < 1` alone (the σ-cutoff's own convergence boundary), since the
amplitude side is `c`-free. -/
theorem rhsAgradeConstC_le {c Cb k L y h c₀ : ℝ} (hc1 : 2 * c < 1) (hCb0 : 0 ≤ Cb)
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hh : h = k / Real.sqrt L)
    (hc₀ : c₀ = 1 + 1 / L) :
    rhsAgradeConstC c Cb k h y c₀ ≤ gradeAbsConstC c Cb * k := by
  have hd : (0 : ℝ) < 1 - 2 * c := by linarith
  have hCSF : (0 : ℝ) < rhsCSF := rhsCSF_pos
  have hF0 : (0 : ℝ) ≤ (1 / Real.pi) * rhsCSF * (Real.exp (c * 48) / (1 - 2 * c)) := by
    have hπ : (0 : ℝ) < 1 / Real.pi := by positivity
    positivity
  unfold rhsAgradeConstC gradeAbsConstC
  calc (1 / Real.pi) * rhsCSF * (Real.exp (c * 48) / (1 - 2 * c)) * widthKamp Cb k h y c₀
      ≤ (1 / Real.pi) * rhsCSF * (Real.exp (c * 48) / (1 - 2 * c))
          * (1580544 * (1 + Cb) * k) :=
        mul_le_mul_of_nonneg_left (widthKamp_pin_le hCb0 hk hL hy hh hc₀) hF0
    _ = (1 / Real.pi) * rhsCSF * (Real.exp (c * 48) / (1 - 2 * c)) * (1580544 * (1 + Cb))
          * k := by ring

/-! ### The exit -/

/-- **W4-4 — THE GRADE AT SCALE, WINDOW-FLOOR FORM, AT A FREE `c`**
(`rhs_grade_at_scale_windowC`).  `GradeConst.rhs_grade_at_scale_const` (:1089) and
`SupClose.rhs_grade_at_scale_trunc` (:334) merged and freed:

  `‖prop21RHS (damped datum) t₀' k h c₀ y η‖
     ≤ gradeAbsConstC c Cb · k · e^{−c·M} + (1/π)·η²·(Ffar·Kfar)`.

**The floor binder is the window one alone** — `hMt`/`hmin`/`hgate` are gone:

  `hMwin : ∀ t, |t − t₀'| ≤ T → M ≤ 𝔻²(ellLin (damped datum), costwist (t − t₀'); k)`,

which is EXACTLY the chain's consumption (`joint_supF_pin_windowC`), stated at the contour's
own centre `t₀'`.  `M` is a free real: the consumer names it.

**The `c`-gates, in-statement (law #253):** `0 < c`, `c ≤ 1/e` (`supF_pret_pointwise`) and
`2c < 1` (`sigma_cutoff_pretentious_gen`, the σ-cutoff's honest convergence boundary).  At
the CASE-A exponent `c = 1/e` all three hold; at `c = 1/(2e)` this is the ball arm's own
statement with `hMwin` in place of `hmin`.

**The far arm rides ADDITIVELY.**  `Ffar`/`Kfar` and their two binders are
`TruncFactor.joint_cs_factoring_trunc`'s, threaded verbatim; the remainder
`(1/π)·η²·(Ffar·Kfar)` is NOT absorbed into the main term (absorption needs the numerals —
`hFar` at the free `M = 0` majorant, `crossKerFar_pin_le` at `T := L⁴` — and the live-band
cap on `M`; that is the consumer's rung, as in `SupClose` §4). -/
theorem rhs_grade_at_scale_windowC {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c Cb t₀' M k L c₀ y η h T Ffar Kfar : ℝ}
    (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1) (hc1 : 2 * c < 1)
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L) (hM0 : 0 ≤ M)
    (hMwin : ∀ t : ℝ, |t - t₀'| ≤ T →
      M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k)
    (hFfar0 : 0 ≤ Ffar)
    (hFar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Ffar)
    (hKfar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β T ≤ Kfar)
    (hInt : JointIntegrableAtC c (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
      t₀' M k L c₀ y η h) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' k h c₀ y η‖
      ≤ gradeAbsConstC c Cb * k * Real.exp (-c * M)
        + (1 / Real.pi) * (η ^ 2 * (Ffar * Kfar)) := by
  obtain ⟨hIβ, hIβ', hIα, hIα'⟩ := hInt
  obtain ⟨hk0, hL64, -, -, hη0, -, -, hyk⟩ := pin_basic64W hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨hh0, -, -, -⟩ := pin_width_gates hL64 hk0 hh hy
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hk65 : (65 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (64 : ℝ)]
  have hy0 : (0 : ℝ) < y := by rw [hy]; positivity
  have hyk' : y ≤ k := by rw [hy]; exact hyk
  have hd : (0 : ℝ) < 1 - 2 * c := by linarith
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  have hKamp0 : (0 : ℝ) ≤ widthKamp Cb k h y c₀ := widthKamp_nonnegW hCb0 hk0 hh0 hy0
  have hG0 : (0 : ℝ) ≤ rhsSigmaGC c M L := by
    unfold rhsSigmaGC
    have hE : (0 : ℝ) ≤ Real.exp (c * 48) / (1 - 2 * c) := by positivity
    exact mul_nonneg rhsCSF_pos.le (by positivity)
  -- the truncated factoring at a free `c`, with the window floor as the only frequency input
  have hJ1 := joint_cs_trunc_pinC hg hc0 hce hk hL hy hη hc₀ hh0 hMwin hFfar0 hFar hKfar
    ⟨hIβ, hIβ', hIα, hIα'⟩
  -- the MAIN term: `beta_integral_pin_constC`'s page, unchanged
  have hper : ∀ α ∈ Icc (0 : ℝ) η,
      (∫ β in (0 : ℝ)..η, rhsFboundC c M L (β + 1 / L)
          * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β)
        ≤ (widthKamp Cb k h y c₀ * (k + h) ^ (-α)) * rhsSigmaGC c M L :=
    fun α hα => beta_integral_pin_constC _ hgtw hc0 hc1 hCb0 hCbound hk hL hy hη hc₀ hh hyk'
      hM0 hα.1 hα.2 (hIβ α hα)
  have hKcont : Continuous
      (fun α : ℝ => (widthKamp Cb k h y c₀ * (k + h) ^ (-α)) * rhsSigmaGC c M L) :=
    ((continuous_rpow_negW hkh0).const_mul _).mul continuous_const
  have hmono := intervalIntegral.integral_mono_on hη0.le hIα
    (hKcont.intervalIntegrable 0 η) hper
  have hfe : ∀ α : ℝ, (widthKamp Cb k h y c₀ * (k + h) ^ (-α)) * rhsSigmaGC c M L
      = (widthKamp Cb k h y c₀ * rhsSigmaGC c M L) * ((k + h) ^ (-α)) := fun α => by ring
  have hpull : (∫ α in (0 : ℝ)..η, (widthKamp Cb k h y c₀ * (k + h) ^ (-α)) * rhsSigmaGC c M L)
      = (widthKamp Cb k h y c₀ * rhsSigmaGC c M L) * ∫ α in (0 : ℝ)..η, (k + h) ^ (-α) := by
    simp only [hfe]
    exact intervalIntegral.integral_const_mul _ _
  have hint_le : (∫ α in (0 : ℝ)..η, (k + h) ^ (-α)) ≤ 1 / L := by
    have h1 : (∫ α in (0 : ℝ)..η, (k + h) ^ (-α)) ≤ 1 / Real.log (k + h) :=
      alpha_rpow_integral_le (by linarith) hη0.le
    have h2 : L ≤ Real.log (k + h) := by
      rw [hL]; exact Real.log_le_log hk0 (by linarith)
    have h3 : (0 : ℝ) < Real.log (k + h) := by linarith
    have h4 : 1 / Real.log (k + h) ≤ 1 / L := by
      rw [div_le_div_iff₀ h3 hL0]; linarith
    linarith
  have hstep : (1 / Real.pi) * ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
        rhsFboundC c M L (β + 1 / L)
          * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β
      ≤ (1 / Real.pi) * ((widthKamp Cb k h y c₀ * rhsSigmaGC c M L) * (1 / L)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η, rhsFboundC c M L (β + 1 / L)
              * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β)
        ≤ ∫ α in (0 : ℝ)..η, (widthKamp Cb k h y c₀ * (k + h) ^ (-α))
            * rhsSigmaGC c M L := hmono
      _ = (widthKamp Cb k h y c₀ * rhsSigmaGC c M L)
            * ∫ α in (0 : ℝ)..η, (k + h) ^ (-α) := hpull
      _ ≤ (widthKamp Cb k h y c₀ * rhsSigmaGC c M L) * (1 / L) :=
          mul_le_mul_of_nonneg_left hint_le (mul_nonneg hKamp0 hG0)
  have hmaineq : (1 / Real.pi) * ((widthKamp Cb k h y c₀ * rhsSigmaGC c M L) * (1 / L))
      = rhsAgradeConstC c Cb k h y c₀ * Real.exp (-c * M) := by
    have hexpeq : Real.exp (-(c * M)) = Real.exp (-c * M) := by rw [neg_mul]
    have hπne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hLne : L ≠ 0 := ne_of_gt hL0
    have hdne : (1 : ℝ) - 2 * c ≠ 0 := ne_of_gt hd
    unfold rhsAgradeConstC rhsSigmaGC
    rw [← hexpeq]
    field_simp
  -- the amplitude at the absolute constant
  have habs : rhsAgradeConstC c Cb k h y c₀ * Real.exp (-c * M)
      ≤ gradeAbsConstC c Cb * k * Real.exp (-c * M) :=
    mul_le_mul_of_nonneg_right (rhsAgradeConstC_le hc1 hCb0 hk hL hy hh hc₀)
      (Real.exp_nonneg _)
  have hmain := hstep.trans (le_of_eq hmaineq)
  linarith

/-! ## §3 (W4-6) — the centre supply at an ABSTRACT grade factor

`CenterSupply`'s four arithmetic privates, re-derived verbatim under a `_B` suffix (they are
`private` both there and in `SupStation`'s `_st` re-derivation). -/

/-- `L^{−1/2} = 1/√L`. -/
private lemma rpow_neg_half_eq_B {L : ℝ} (hL : 0 < L) :
    L ^ (-(1 : ℝ) / 2) = (Real.sqrt L)⁻¹ := by
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) from by norm_num, Real.rpow_neg hL.le,
    Real.sqrt_eq_rpow]

/-- `2·log X ≤ X` for `X ≥ 16` (the `√X`-route: `log X = 2 log √X ≤ 2(√X−1)`, then
`4√X − 4 ≤ X` is `(√X−2)² ≥ 0`). -/
private lemma two_log_le_self_B {X : ℝ} (hX : 16 ≤ X) : 2 * Real.log X ≤ X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hs4 : (4 : ℝ) ≤ Real.sqrt X := by
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h16]
    exact Real.sqrt_le_sqrt hX
  have hlog : Real.log (Real.sqrt X) ≤ Real.sqrt X - 1 := Real.log_le_sub_one_of_pos hs0
  have hhalf : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hX0.le
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  nlinarith [hs4, hlog, hsq, hhalf]

/-- `25 ≤ exp 8` (used only to place the threshold above `16`). -/
private lemma twentyfive_le_exp_eight_B : (25 : ℝ) ≤ Real.exp 8 := by
  have h4 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hpos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  rw [show (8 : ℝ) = 4 + 4 from by norm_num, Real.exp_add]
  nlinarith

/-- **THE GRADE PAGE (`center_error_grade_B`).**  The two error legs of the centre
composition — the desmooth cost `h+1 = k/√(log k) + 1` and the S1′ `E`-error, already
reduced to `D·k·loglog k/log k` — are converted into the SINGLE `X`-scale term
`4·k·(log X)^{−1/2+1/1000}`, uniformly over the dyadic window `X−1 < k ≤ 2X`.

The three conversions, each elementary: `log k ∈ [L/2, 2L]` (the window, `L := log X`);
`loglog k / log k ≤ 4·loglog X / log X`, absorbed by `hB` (A-6 at the pinned `ε = 1/1000`);
`1/√(log k) ≤ 2/√L` and `1 ≤ k/√L` (the latter from `2·log X ≤ X`, `two_log_le_self_B`). -/
private lemma center_error_grade_B {D X : ℝ} {k : ℕ} (hD0 : 0 ≤ D)
    (hX8 : Real.exp 8 ≤ X) (hk1 : X - 1 < (k : ℝ)) (hk2 : (k : ℝ) ≤ 2 * X)
    (hB : 4 * D * Real.log (Real.log X) * Real.log X ^ (-(1 : ℝ))
        ≤ Real.log X ^ (-(1 : ℝ) + 1 / 1000)) :
    D * ((k : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)))
        + ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)) + 1)
      ≤ 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight_B hX8
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hkX2 : X / 2 ≤ (k : ℝ) := by linarith
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  set L := Real.log X with hLdef
  have hL8 : (8 : ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 8]
    exact Real.log_le_log (Real.exp_pos 8) hX8
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  set Lk := Real.log (k : ℝ) with hLkdef
  have hLklo : L - Real.log 2 ≤ Lk := by
    have h1 : Real.log (X / 2) ≤ Lk := Real.log_le_log (by linarith) hkX2
    rwa [Real.log_div (by linarith) (by norm_num)] at h1
  have hLkhi : Lk ≤ L + Real.log 2 := by
    have h1 : Lk ≤ Real.log (2 * X) := Real.log_le_log hk0 hk2
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have hLk1 : (1 : ℝ) ≤ Lk := by linarith
  have hLk0 : (0 : ℝ) < Lk := by linarith
  have hLkhalf : L / 2 ≤ Lk := by linarith
  have hLk2L : Lk ≤ 2 * L := by linarith
  have hlogLk0 : (0 : ℝ) ≤ Real.log Lk := Real.log_nonneg hLk1
  have hlogL0 : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL1
  -- STEP A/B/C — `loglog k / log k ≤ 4·loglog X / log X`
  have hlogLk : Real.log Lk ≤ 2 * Real.log L := by
    have h1 : Real.log Lk ≤ Real.log (2 * L) := Real.log_le_log hLk0 hLk2L
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log L := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hstepC : Real.log Lk / Lk ≤ 4 * (Real.log L / L) := by
    have hq0 : (0 : ℝ) ≤ 4 * (Real.log L / L) := by positivity
    have h1 : 4 * (Real.log L / L) * (L / 2) ≤ 4 * (Real.log L / L) * Lk :=
      mul_le_mul_of_nonneg_left hLkhalf hq0
    have h2 : 4 * (Real.log L / L) * (L / 2) = 2 * Real.log L := by
      field_simp
      ring
    rw [div_le_iff₀ hLk0]
    linarith
  -- STEP D — the A-6 absorption at the pin
  have hLinv : L ^ (-(1 : ℝ)) = 1 / L := by rw [Real.rpow_neg_one, one_div]
  have hPmono : L ^ (-(1 : ℝ) + 1 / 1000) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hstepD : D * (Real.log Lk / Lk) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h1 : D * (Real.log Lk / Lk) ≤ D * (4 * (Real.log L / L)) :=
      mul_le_mul_of_nonneg_left hstepC hD0
    have h2 : D * (4 * (Real.log L / L)) = 4 * D * Real.log L * L ^ (-(1 : ℝ)) := by
      rw [hLinv]; field_simp
    linarith
  -- STEP E — the desmooth leg
  have hsqL0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsqL2 : Real.sqrt L / 2 ≤ Real.sqrt Lk := by
    have hq : Real.sqrt (L / 4) = Real.sqrt L / 2 := by
      rw [show L / 4 = L * (1 / 2) ^ 2 from by ring, Real.sqrt_mul hL0.le,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    calc Real.sqrt L / 2 = Real.sqrt (L / 4) := hq.symm
      _ ≤ Real.sqrt Lk := Real.sqrt_le_sqrt (by linarith)
  have hsqL20 : (0 : ℝ) < Real.sqrt L / 2 := by linarith
  have hdes : (k : ℝ) / Real.sqrt Lk ≤ 2 * ((k : ℝ) * L ^ (-(1 : ℝ) / 2)) := by
    have h1 : (k : ℝ) / Real.sqrt Lk ≤ (k : ℝ) / (Real.sqrt L / 2) :=
      div_le_div_of_nonneg_left hk0.le hsqL20 hsqL2
    have h2 : (k : ℝ) / (Real.sqrt L / 2) = 2 * ((k : ℝ) * L ^ (-(1 : ℝ) / 2)) := by
      rw [rpow_neg_half_eq_B hL0]
      field_simp
    linarith
  -- STEP F — `1 ≤ k·L^{−1/2}`
  have hone : (1 : ℝ) ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2) := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt L := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hL1
    have hsL : Real.sqrt L ≤ L := by nlinarith [Real.mul_self_sqrt hL0.le, hsq1]
    have h2L : 2 * L ≤ X := by rw [hLdef]; exact two_log_le_self_B (by linarith)
    have hsk : Real.sqrt L ≤ (k : ℝ) := by linarith
    rw [rpow_neg_half_eq_B hL0, ← div_eq_mul_inv, le_div_iff₀ hsqL0]
    linarith
  -- STEP G — assemble
  have hPnn : (0 : ℝ) ≤ L ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hL0.le _
  have hGmono : L ^ (-(1 : ℝ) / 2) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hterm1 : D * ((k : ℝ) * (Real.log Lk / Lk))
      ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h := mul_le_mul_of_nonneg_left hstepD hk0.le
    calc D * ((k : ℝ) * (Real.log Lk / Lk)) = (k : ℝ) * (D * (Real.log Lk / Lk)) := by ring
      _ ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) := h
  have hterm2 : (k : ℝ) * L ^ (-(1 : ℝ) / 2)
      ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    mul_le_mul_of_nonneg_left hGmono hk0.le
  linarith

/-- **W4-6 — THE CENTRE SUPPLY AT AN ABSTRACT GRADE FACTOR, UNIFORM IN THE CENTRE**
(`center_halasz_supply_B_uniform`).  `CenterSupply.center_halasz_supply` (:296) with the
grade factor `C₁·e^{−(1/(2e))·𝔻²(f, p^{it₁}; X)}` replaced by an OPAQUE nonneg `B`:

  `hRHS : ∀ k ∈ [⌊X⌋₊, N],  ‖prop21RHS (damped datum) (t₀+t₁) k h c₀ y η‖ ≤ B·k`
  ⟹  `∀ k ∈ [⌊X⌋₊, N],  ‖∑_{n≤k} f n·e^{−it₁ log n}‖ ≤ (B + 4·(log X)^{−1/2+1/1000})·k`.

The landed proof never inspects the exponent — the grade leg enters once, as `hR`, and is
carried to the closing `linarith` — so the abstraction is free and this face is `c`-FREE
FOREVER: the CASE-A route instantiates `B` at the `c`-generic grade, the ball arm at
`C₁·e^{−M/(2e)}`, and neither costs a new page.

The `∃ X₀` is quantified BEFORE the centre `t₁` (`SupStation` §2's hoisting: the witness
`max (max (XA+1) XB) (e⁸)` mentions neither `g`, `t₀` nor `t₁`), so a consumer that picks its
centre per-`X` — as the CASE-A window does — can still consume it. -/
theorem center_halasz_supply_B_uniform {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (t₀ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (t₁ X : ℝ) (N : ℕ) (B : ℝ), X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ B →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
              ≤ B * (k : ℝ)) →
      ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n‖
          ≤ (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ) := by
  obtain ⟨XA, C_E, C_R, hCE0, hCR0, hrep⟩ := prop21_uniform_at_scale_absC
  obtain ⟨XB, _hXB0, hB⟩ :=
    loglog_absorb_pow_pin (C := 4 * (8 * C_E + 4 * C_R)) (by positivity) 1
  refine ⟨max (max (XA + 1) XB) (Real.exp 8),
    lt_of_lt_of_le (Real.exp_pos 8) (le_max_right _ _), ?_⟩
  intro t₁ X N B hXlb hXN hN2 hB0 hRHS k hkfl hkN
  -- the threshold split
  have hX8 : Real.exp 8 ≤ X := le_trans (le_max_right _ _) hXlb
  have hXA1 : XA + 1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXlb
  have hXB : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXlb
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight_B hX8
  have hX0 : (0 : ℝ) < X := by linarith
  -- the dyadic `k`-window
  have hfl : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  have hk1 : X - 1 < (k : ℝ) := by
    have h : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hkfl
    linarith
  have hk2 : (k : ℝ) ≤ 2 * X := le_trans (Nat.cast_le.mpr hkN) hN2
  have hkXA : XA ≤ (k : ℝ) := by linarith
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk1le : (1 : ℝ) ≤ (k : ℝ) := by linarith
  -- `log k ≥ 1` (the window: `log k ≥ log X − log 2 ≥ 8 − 0.7`)
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL8 : (8 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8]; exact Real.log_le_log (Real.exp_pos 8) hX8
  have hLklo : Real.log X - Real.log 2 ≤ Real.log (k : ℝ) := by
    have h1 : Real.log (X / 2) ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by linarith) (by linarith)
    rwa [Real.log_div (by linarith) (by norm_num)] at h1
  have hLk1 : (1 : ℝ) ≤ Real.log (k : ℝ) := by linarith
  have hLk0 : (0 : ℝ) < Real.log (k : ℝ) := by linarith
  have hsqLk1 : (1 : ℝ) ≤ Real.sqrt (Real.log (k : ℝ)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hLk1
  have hsqLk0 : (0 : ℝ) < Real.sqrt (Real.log (k : ℝ)) := by linarith
  have hh0 : (0 : ℝ) < (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by positivity
  have hhX : (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) ≤ (k : ℝ) := by
    rw [div_le_iff₀ hsqLk0]; nlinarith
  -- the two landed legs, at scale `k`
  have hdes := prop21_desmooth_reduction (f := ellLin g) (gJ := fun _ => 1) (t₀ + t₁)
    (fun n => ellLin_norm_le_one g hg n) (fun _ => by simp)
    (X := (k : ℝ)) (h := (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) hk1le hh0 hhX
  rw [Nat.floor_natCast] at hdes
  have hr := hrep g hg (t₀ + t₁) (k : ℝ) hkXA
  have hR := hRHS k hkfl hkN
  -- the twist combine
  have hsum : (∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n)
      = ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n :=
    Finset.sum_congr rfl (fun n _ => seamCoeff_twist_combine _ _ t₀ t₁ n)
  rw [hsum]
  -- the triangle chain
  set A := ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n with hAdef
  set Bs := ∑' n, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n
    * (hatK (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) n : ℂ) with hBsdef
  set R := prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
    (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
    (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4)) with hRdef
  have hid : A = (A - Bs) + ((Bs - R) + R) := by ring
  have htri : ‖A‖ ≤ ‖A - Bs‖ + (‖Bs - R‖ + ‖R‖) := by
    calc ‖A‖ = ‖(A - Bs) + ((Bs - R) + R)‖ := by rw [← hid]
      _ ≤ ‖A - Bs‖ + ‖(Bs - R) + R‖ := norm_add_le _ _
      _ ≤ ‖A - Bs‖ + (‖Bs - R‖ + ‖R‖) := by
          linarith [norm_add_le (Bs - R) R]
  -- the `E`-error, reduced to the `D·k·loglog k/log k` shape
  have hlogpow : Real.log (Real.log (k : ℝ) ^ 4) = 4 * Real.log (Real.log (k : ℝ)) := by
    rw [Real.log_pow]; norm_num
  have hlogLk0 : (0 : ℝ) ≤ Real.log (Real.log (k : ℝ)) := Real.log_nonneg hLk1
  have hu0 : (0 : ℝ) < (k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by linarith
  have hulogb : Real.log (k : ℝ) ≤ Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) :=
    Real.log_le_log hk0 (by linarith)
  have huq : ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
        / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
      ≤ 2 * (k : ℝ) / Real.log (k : ℝ) := by
    rw [div_le_div_iff₀ (by linarith) hLk0]
    nlinarith
  have hEle : C_E * (((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
          / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))))
        * Real.log (Real.log (k : ℝ) ^ 4)
      + C_R * ((k : ℝ) / Real.log (k : ℝ)) * Real.log (Real.log (k : ℝ) ^ 4)
      ≤ (8 * C_E + 4 * C_R)
          * ((k : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))) := by
    rw [hlogpow]
    have h1 : C_E * (((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
            / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))))
          * (4 * Real.log (Real.log (k : ℝ)))
        ≤ C_E * (2 * (k : ℝ) / Real.log (k : ℝ)) * (4 * Real.log (Real.log (k : ℝ))) := by
      have hq : (0 : ℝ) ≤ 4 * Real.log (Real.log (k : ℝ)) := by linarith
      have := mul_le_mul_of_nonneg_left huq hCE0
      exact mul_le_mul_of_nonneg_right this hq
    have h2 : C_E * (2 * (k : ℝ) / Real.log (k : ℝ)) * (4 * Real.log (Real.log (k : ℝ)))
          + C_R * ((k : ℝ) / Real.log (k : ℝ)) * (4 * Real.log (Real.log (k : ℝ)))
        = (8 * C_E + 4 * C_R)
            * ((k : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))) := by
      field_simp
      ring
    linarith
  -- the grade page
  have hgrade := center_error_grade_B (D := 8 * C_E + 4 * C_R) (X := X) (k := k)
    (by positivity) hX8 hk1 hk2 (hB X hXB)
  have hexpand : (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ)
      = B * (k : ℝ) + 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by ring
  rw [hexpand]
  linarith
/-- **W4-6 face — the `CenterSupply` binder shape** (`center_halasz_supply_B`).
`center_halasz_supply_B_uniform` at a fixed centre: `CenterSupply.center_halasz_supply`
(:296) byte-for-byte with the grade factor abstracted to `B`. -/
theorem center_halasz_supply_B {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t₁ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (B : ℝ), X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ B →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
              ≤ B * (k : ℝ)) →
      ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n‖
          ≤ (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ) := by
  obtain ⟨X₀, hX₀0, hsupply⟩ := center_halasz_supply_B_uniform hg t₀
  exact ⟨X₀, hX₀0, fun X N B hXlb hXN hN2 hB0 hRHS => hsupply t₁ X N B hXlb hXN hN2 hB0 hRHS⟩

end Salt.MR
