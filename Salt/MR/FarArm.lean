/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.AnnHead
import Salt.MR.CofactorSupply
import Salt.MR.SeamBallWeighted
import Salt.MR.SeamGate

/-!
# FAR-ARM — the A-10 cap-FAILS exit of the seam row (`FarArm`)

**W-1 of ⟦V6⟧ (`docs/exploration/hsup-design.md`).**  The seam row's ball leg fires under the
A-10 cap

  `hMcap : ∀ x ∈ [X, 2X],  𝔻²(seamCoeff (ellLin g) 1 t₀, p^{it₁}; x) ≤ (1/16)·loglog X`

(`CenterSupply.ball_sup_supplied`, `FarStar.ball_sup_closed_star`).  This file lands the OTHER
arm: what the row does when that cap FAILS.  It is MR(T) §A.3's own far arm — there the
`M ≥ (1/8)loglog` branch takes `𝒯₁ = [−T, T]` WHOLE and pays the U-bound everywhere, no ball
removal at all.  Ours does the same, in the landed vocabulary: **cap fails ⟹ the R3.1 floor
holds ⟹ the annular head/tail chain runs on the whole annulus at the `(log X)^{−1/(32e)}`
grade** (`AnnHead.T1_decay_annular_T_polylog`, whose LAST abstract socket is exactly that
floor).

## The honest page (the scale question, worked)

The cap is a `∀ x ∈ [X, 2X]` statement; its negation supplies ONE `x*` with the floor **at
scale `x*`**, and `pretDistSq` GROWS with the scale (`RHSGrade.pretDistSq_mono_scale`), so the
floor does **not** descend to `X` for free.  It descends for a PRICE, and the price is `o(1)`:

* `CofactorSupply.pretDistSq_tail_le` (the landed priced ascent) charges the descent by
  `2·(S(x*) − S(X))`, `S` the Mertens partial sum;
* on the row's own dyadic window that charge is `≤ 50/log X` (`dyadic_SPartial_charge` below:
  sharp Mertens-2 twice, `log u ≤ u − 1` at `u = log x*/log X`, `log 2 ≤ 1`);
* and `50/log X ≤ (1/32)·loglog X` past `farArmThreshold` — so the `(1/16) → (1/32)` halving
  the frozen numerals already carry absorbs the whole descent, with no numeral shift and no
  statement change (Iron rule 1 never engages).

So the cap-fails floor lands at the row's OWN scale `X`, halved: `cap_fails_floor`.

## From the centre to `M_range` (why the minimiser is what carries it)

The consumers do not want a floor at `t₁`; they want `(1/32)·loglog X ≤ M_range f X T`, the
infimum over the offset window.  `t₁` is the COMPACT MINIMISER
(`SeamGate.exists_min_gate` / `seam_gate_package`, at radius `seamGateR X T`;
`FarStar.ball_sup_closed_star`, at `seamGateRstar X T`), and `M_range`'s window
`{|t| ∈ [(logX)^{1/15}, T + (logX)^{1/16}], |t| ≤ X}` sits inside BOTH — each radius is
`T + seamRad X + (something ≥ 0) + 1`, and `seamRad X = (logX)^{1/16}` is `M_range`'s own
widening.  So the stones below take the radius as a FREE parameter with the single hypothesis
`T + seamRad X ≤ R`, and the floor at the minimiser propagates to every frequency the infimum
sees: `Mrange_floor_of_center_floor_radius`.  The window's nonemptiness is
`Mrange_one_floor`'s own witness `t = (logX)^{1/15}`, under the same hypothesis
`(logX)^{1/15} ≤ T`.

## What is here

* `dyadic_SPartial_charge` (§1) — the `50/log X` dyadic Mertens charge.
* `farArmThreshold` + `farArm_charge_le` (§2) — the explicit threshold at which the charge is
  swallowed by the halving (law #253: every constant explicit).
* `cap_fails_floor` (F-1, §2) — cap fails ⟹ `(1/32)·loglog X ≤ 𝔻²(f, p^{it₁}; X)`.
* `Mrange_floor_of_center_floor_radius` / `_of_center_floor` (F-2a, §3) — the minimiser's floor
  ⟹ the `M_range` floor, at a FREE minimality radius (so `seamGateR` and `seamGateRstar` are
  both instances and one centre serves both arms).
* `far_arm_row` / `far_arm_row_tailed` / `far_arm_row_polyT` (F-2b, §4) — the far arm's ROW:
  the whole-annulus head/tail grade with `hfloor` DISCHARGED from the cap's failure.  Two
  flavours: general `T` (no gate, so the seam's `T_ann ≈ X` regime is covered, at the honest
  `(logX)²` inflation of `T1_decay_annular_T_polylog`) and polylog `T` (the clean, un-inflated
  grade).  **Residual, stated not hidden:** the un-inflated GENERAL-`T` row
  (`T1_decay_annular_T_of_floor`) wants the strong floor `2e·loglog X ≤ M_range`, and the A-10
  cap's threshold `(1/16)·loglog X` cannot reach it (`1/16 ≪ 2e`).  Closing that is a SOCKET
  question — a sharper `annHead` measure page at `T ≍ X` — never a floor question, and never a
  numeral change (Iron rule 1).
* `seam_row_of_inter_empty` (§5) — the third arm, at the row level: the weighted seam row with
  `hSup` discharged from the EMPTY intersection, at any `S`.
* `seam_row_both_arms` / `seam_row_three_arms` (F-3, §5) — the packaged case split the seam
  terminal consumes: the cap as a FREE dichotomy, and the full A-10 tree
  (empty / near / far).

**Nothing existing is touched** (Iron rule 5): every statement below is new, every landed stone
is hit through its existing binders, and the frozen `PropA3Core` numerals are used only in the
direction they were frozen for.
-/

noncomputable section

namespace Salt.MR

open Set

/-! ## §1 — the dyadic Mertens charge

The one genuinely new piece of arithmetic in this file: how much a floor pays when it is
carried DOWN from a scale `x ∈ [X, 2X]` to the row's own scale `X`. -/

/-- **The dyadic scale charge (`dyadic_SPartial_charge`).**  On the row's dyadic window the
Mertens partial sum moves by `O(1/log X)`:

  `2·(S(x) − S(X)) ≤ 50/log X`  for `2 ≤ X ≤ x ≤ 2X`.

Page: sharp Mertens-2 (`Salt.Mertens.mertens_second_sharp_real`, the explicit `12/log t`) at
both ends leaves `2·(loglog x − loglog X) + 24/log x + 24/log X`; and

  `loglog x − loglog X = log(log x / log X) ≤ (log x − log X)/log X ≤ log 2/log X ≤ 1/log X`

by `Real.log_le_sub_one_of_pos` at `u = log x/log X` and `log x ≤ log 2 + log X`.  The `50` is
deliberately crude (`2·log 2 + 48 < 49.4`); every constant is explicit (law #253). -/
lemma dyadic_SPartial_charge {X x : ℝ} (hX : 2 ≤ X) (hxX : X ≤ x) (hx2X : x ≤ 2 * X) :
    2 * (Salt.Mertens.SPartial x - Salt.Mertens.SPartial X) ≤ 50 / Real.log X := by
  have hXpos : (0 : ℝ) < X := by linarith
  have hx2 : (2 : ℝ) ≤ x := le_trans hX hxX
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos (by linarith)
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hmono : Real.log X ≤ Real.log x := Real.log_le_log hXpos hxX
  have hsx := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hx2)
  have hsX := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hX)
  -- the `loglog` gap across the dyadic window
  have hll : Real.log (Real.log x) - Real.log (Real.log X) ≤ 1 / Real.log X := by
    have hq : (0 : ℝ) < Real.log x / Real.log X := by positivity
    have h := Real.log_le_sub_one_of_pos hq
    rw [Real.log_div (ne_of_gt hlogx) (ne_of_gt hlogX)] at h
    have heq : Real.log x / Real.log X - 1 = (Real.log x - Real.log X) / Real.log X := by
      field_simp
    rw [heq] at h
    have hlx : Real.log x - Real.log X ≤ 1 := by
      have h2X : Real.log x ≤ Real.log (2 * X) := Real.log_le_log (by linarith) hx2X
      rw [Real.log_mul (by norm_num) (ne_of_gt hXpos)] at h2X
      have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      linarith
    have hdiv : (Real.log x - Real.log X) / Real.log X ≤ 1 / Real.log X := by gcongr
    linarith
  -- the two sharp-Mertens error terms
  have h12 : 12 / Real.log x ≤ 12 / Real.log X := by gcongr
  have hcollect : (1 : ℝ) / Real.log X + 12 / Real.log X + 12 / Real.log X
      = 25 / Real.log X := by ring
  have hfin : 2 * (25 / Real.log X) = 50 / Real.log X := by ring
  linarith [hsx.2, hsX.1]

/-! ## §2 — F-1: the cap-fails floor

The threshold is explicit and generous: `farArmThreshold = exp(exp 1600)` gives
`log X ≥ 1601` and `loglog X ≥ 1600`, so the dyadic charge `50/log X < 1` sits far below the
halving slack `(1/32)·loglog X ≥ 50`.  (The campaign's standing `X₀` tower — `⟦V5c⟧`'s
`exp(exp(2·10⁴⁵))` — dwarfs it; nothing here is the binding gate.) -/

/-- **The far arm's explicit threshold.**  `exp(exp 1600)`: the scale past which the dyadic
descent charge `50/log X` is swallowed by the frozen `(1/16) → (1/32)` halving slack. -/
def farArmThreshold : ℝ := Real.exp (Real.exp 1600)

/-- `1601 ≤ log X` past the threshold (`exp t ≥ t + 1` once). -/
lemma farArm_log_lb {X : ℝ} (hX : farArmThreshold ≤ X) : (1601 : ℝ) ≤ Real.log X := by
  have hXpos : (0 : ℝ) < X :=
    lt_of_lt_of_le (Real.exp_pos (Real.exp 1600)) (by rwa [farArmThreshold] at hX)
  have hlog : Real.exp 1600 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).mpr (by rwa [farArmThreshold] at hX)
  have h1601 : (1601 : ℝ) ≤ Real.exp 1600 := by linarith [Real.add_one_le_exp (1600 : ℝ)]
  linarith

/-- `1600 ≤ loglog X` past the threshold. -/
lemma farArm_loglog_lb {X : ℝ} (hX : farArmThreshold ≤ X) :
    (1600 : ℝ) ≤ Real.log (Real.log X) := by
  have hXpos : (0 : ℝ) < X :=
    lt_of_lt_of_le (Real.exp_pos (Real.exp 1600)) (by rwa [farArmThreshold] at hX)
  have hlog : Real.exp 1600 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).mpr (by rwa [farArmThreshold] at hX)
  have h := Real.log_le_log (Real.exp_pos 1600) hlog
  rwa [Real.log_exp] at h

/-- `2 ≤ X` past the threshold (`exp t ≥ t + 1` twice). -/
lemma farArm_two_le {X : ℝ} (hX : farArmThreshold ≤ X) : (2 : ℝ) ≤ X := by
  have e1 : (1601 : ℝ) ≤ Real.exp 1600 := by linarith [Real.add_one_le_exp (1600 : ℝ)]
  have e2 : Real.exp 1600 + 1 ≤ Real.exp (Real.exp 1600) := Real.add_one_le_exp _
  rw [farArmThreshold] at hX
  linarith

/-- `e ≤ X` past the threshold — the gate every landed chain opens with. -/
lemma farArm_exp_one_le {X : ℝ} (hX : farArmThreshold ≤ X) : Real.exp 1 ≤ X := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) (farArm_two_le hX)
  exact (Real.le_log_iff_exp_le hXpos).mp (by linarith [farArm_log_lb hX])

/-- **The charge is swallowed.**  Past the threshold the dyadic descent charge is below the
halving slack: `50/log X ≤ (1/32)·loglog X`.  (`50/1601 < 1 ≤ 50 = (1/32)·1600`.) -/
lemma farArm_charge_le {X : ℝ} (hX : farArmThreshold ≤ X) :
    50 / Real.log X ≤ (1 / 32) * Real.log (Real.log X) := by
  have hlog := farArm_log_lb hX
  have hll := farArm_loglog_lb hX
  have h1 : (50 : ℝ) / Real.log X ≤ 50 / 1601 := by gcongr
  linarith

/-- **F-1 — THE CAP-FAILS FLOOR (`cap_fails_floor`).**  If the A-10 ball cap fails anywhere on
the row's dyadic window, the R3.1 floor holds at the centre, at the row's OWN scale:

  `¬(∀ x ∈ [X,2X], 𝔻²(f, p^{it₁}; x) ≤ (1/16)·loglog X)`
    `⟹  (1/32)·loglog X ≤ 𝔻²(f, p^{it₁}; X)`.

The `(1/16) → (1/32)` gap is exactly what pays the honest scale descent: the negation gives
the floor at some `x* ∈ [X, 2X]` only, `pretDistSq` grows with the scale, and
`CofactorSupply.pretDistSq_tail_le` charges the descent by `2(S(x*) − S(X)) ≤ 50/log X`
(`dyadic_SPartial_charge`), which `farArm_charge_le` puts below `(1/32)·loglog X`.  **No
numeral is shifted and no frozen statement is touched** — the halving the freeze already
carries absorbs the whole charge. -/
theorem cap_fails_floor {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {X t₁ : ℝ}
    (hX : farArmThreshold ≤ X)
    (hcap : ¬ ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq f (costwist t₁) x ≤ (1 / 16) * Real.log (Real.log X)) :
    (1 / 32) * Real.log (Real.log X) ≤ pretDistSq f (costwist t₁) X := by
  push Not at hcap
  obtain ⟨x, hx1, hx2, hx3⟩ := hcap
  have hdesc := pretDistSq_tail_le hf (norm_costwist_le t₁) (Nat.floor_mono hx1)
  have hchg := dyadic_SPartial_charge (farArm_two_le hX) hx1 hx2
  have hgate := farArm_charge_le hX
  linarith

/-! ## §3 — F-2a: the centre floor becomes the `M_range` floor

`M_range f X T` is the infimum over the OFFSET WINDOW, so a floor at one frequency says
nothing — unless that frequency is the MINIMISER over a set containing the window.  It is:
`SeamGate.exists_min_gate` produces exactly that, at radius `seamGateR X T`, and the window
`|t| ≤ T + (logX)^{1/16} = T + seamRad X` sits inside it with `(log 2X)⁴ + 1` to spare. -/

/-- **F-2a — the `M_range` floor from the minimiser (`Mrange_floor_of_center_floor`).**  With
`t₁` the compact minimiser at radius `seamGateR X T` (`SeamGate.exists_min_gate`), the R3.1
floor at `t₁` propagates to the whole offset window:

  `(1/32)·loglog X ≤ 𝔻²(f, p^{it₁}; X)  ⟹  (1/32)·loglog X ≤ M_range f X T`.

Two ingredients, both geometric: (i) every `t` the infimum sees obeys
`|t| ≤ T + (logX)^{1/16} = T + seamRad X ≤ R`, so `hmin` applies to it; (ii) the
window is nonempty (`t = (logX)^{1/15}`, `Mrange_one_floor`'s own witness) under the same
hypothesis `(logX)^{1/15} ≤ T` that stone carries — which is what lets `le_csInf` fire (an
`sInf` over `∅` is `0` in `ℝ` and would make the claim false).

**The radius is FREE** (`hR : T + seamRad X ≤ R`), deliberately: the near arm's supplier
`FarStar.ball_sup_closed_star` minimises at `seamGateRstar X T` while `SeamGate.exists_min_gate`
minimises at `seamGateR X T`, and both radii clear `T + seamRad X` by inspection (each is
`T + seamRad X + (something ≥ 0) + 1`).  So ONE centre serves both arms with no
`Tstar`-versus-`log⁴` comparison anywhere.  `Mrange_floor_of_center_floor` below is the
`seamGateR` instance. -/
theorem Mrange_floor_of_center_floor_radius {f : ℕ → ℂ} {X T R t₁ : ℝ}
    (hXe : Real.exp 1 ≤ X) (hT15 : (Real.log X) ^ (1 / 15 : ℝ) ≤ T)
    (hR : T + seamRad X ≤ R)
    (hmin : ∀ v : ℝ, |v| ≤ R →
      pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist v) X)
    (hfloor : (1 / 32) * Real.log (Real.log X) ≤ pretDistSq f (costwist t₁) X) :
    (1 / 32) * Real.log (Real.log X) ≤ M_range f X T := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hXe
  have hLnn : (0 : ℝ) ≤ Real.log X := by linarith
  have hr15 : (0 : ℝ) ≤ (Real.log X) ^ (1 / 15 : ℝ) := Real.rpow_nonneg hLnn _
  have hr16 : (0 : ℝ) ≤ (Real.log X) ^ (1 / 16 : ℝ) := Real.rpow_nonneg hLnn _
  have habs : |(Real.log X) ^ (1 / 15 : ℝ)| = (Real.log X) ^ (1 / 15 : ℝ) := abs_of_nonneg hr15
  -- (i) the offset window sits inside the minimality ball
  have hin : ∀ t : ℝ, |t| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) → |t| ≤ R := by
    intro t ht
    have hrad : seamRad X = (Real.log X) ^ (1 / 16 : ℝ) := rfl
    rw [hrad] at hR
    linarith
  -- (ii) the window is nonempty
  have hmem : (Real.log X) ^ (1 / 15 : ℝ) ∈
      {t : ℝ | (Real.log X) ^ (1 / 15 : ℝ) ≤ |t|
        ∧ |t| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t| ≤ X} := by
    refine ⟨le_of_eq habs.symm, ?_, ?_⟩
    · rw [habs]; linarith
    · rw [habs]
      calc (Real.log X) ^ (1 / 15 : ℝ) ≤ (Real.log X) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = Real.log X := Real.rpow_one _
        _ ≤ X := by linarith [Real.log_le_sub_one_of_pos hXpos]
  unfold M_range
  refine le_csInf ⟨_, ⟨(Real.log X) ^ (1 / 15 : ℝ), hmem, rfl⟩⟩ ?_
  rintro b ⟨t, ht, rfl⟩
  exact hfloor.trans (hmin t (hin t ht.2.1))

/-- The `seamGateR` instance of `Mrange_floor_of_center_floor_radius` — the radius
`SeamGate.exists_min_gate` / `seam_gate_package` actually hand over.  The radius hypothesis is
discharged by inspection: `seamGateR X T = T + seamRad X + (log 2X)⁴ + 1`. -/
theorem Mrange_floor_of_center_floor {f : ℕ → ℂ} {X T t₁ : ℝ}
    (hXe : Real.exp 1 ≤ X) (hT15 : (Real.log X) ^ (1 / 15 : ℝ) ≤ T)
    (hmin : ∀ v : ℝ, |v| ≤ seamGateR X T →
      pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist v) X)
    (hfloor : (1 / 32) * Real.log (Real.log X) ≤ pretDistSq f (costwist t₁) X) :
    (1 / 32) * Real.log (Real.log X) ≤ M_range f X T := by
  refine Mrange_floor_of_center_floor_radius hXe hT15 ?_ hmin hfloor
  have h4 : (0 : ℝ) ≤ Real.log (2 * X) ^ 4 := by positivity
  unfold seamGateR
  linarith

/-! ## §4 — F-2b: THE FAR-ARM ROW

The cap's failure discharges the LAST abstract socket of the annular head/tail chain.  The
flavour chosen is `AnnHead.T1_decay_annular_T_polylog` — the one with **no `T`-gate at all**,
because the seam's annulus runs to `T_ann ≈ X` (the L14 regime) where the polylog-gated rows
do not reach.  Its price is visible in the grade (the `(logX)²` factor, the honest residue of
the crude measure×sup at `T ≍ X`); it is carried, not hidden. -/

/-- **F-2b — THE FAR-ARM ROW (`far_arm_row`).**  The cap-FAILS exit of the seam row: with

* `hmin` — `t₁` the compact minimiser at ANY radius `R ≥ T + seamRad X` (`hR`); both
  `SeamGate.exists_min_gate` (`seamGateR`) and `FarStar.ball_sup_closed_star`
  (`seamGateRstar`) clear that by inspection, so one centre serves both arms,
* `hT15` — the offset window nonempty (`(logX)^{1/15} ≤ T`; free in the seam's `T_ann ≈ X`),
* `hcap` — the A-10 ball cap FAILING somewhere on `[X, 2X]`,

the whole-annulus head/tail leg obeys the frozen `(log X)^{−1/(32e)}` grade:

  `annHead + Utail ≤ (C₁·(T/X + 1)·(logX)² + C₂)·X·((logX)^{−1/(32e)} + (logX)^{−1/2+ε})`.

No ball is removed and no `hSup` binder appears — this is MR(T) §A.3's `𝒯₁ = [−T,T]` WHOLE
treatment of the far branch, in the landed vocabulary.  Route: `cap_fails_floor` (F-1) →
`Mrange_floor_of_center_floor` (F-2a) → `AnnHead.T1_decay_annular_T_polylog`'s `hfloor`.
`X₀ = max (the chain's own) farArmThreshold`. -/
theorem far_arm_row (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t t₁ : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Utail C₂ T R : ℝ),
      X₀ ≤ X → 0 ≤ ε → 0 ≤ C₂ →
      (Real.log X) ^ (1 / 15 : ℝ) ≤ T → T + seamRad X ≤ R →
      Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2) →
      (∀ v : ℝ, |v| ≤ R →
        pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
          ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) →
      (¬ ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
        pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
          ≤ (1 / 16) * Real.log (Real.log X)) →
      annHead g t₀ X T (1 / Real.log X) + Utail
        ≤ (C₁ * (T / X + 1) * (Real.log X) ^ 2 + C₂) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  obtain ⟨C₁, X₀, hC₁, hchain⟩ := T1_decay_annular_T_polylog g hg t₀ t
  refine ⟨C₁, max X₀ farArmThreshold, hC₁, ?_⟩
  intro X ε Utail C₂ T R hX hε hC₂ hT15 hR htail hmin hcap
  have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXfar : farArmThreshold ≤ X := le_trans (le_max_right _ _) hX
  have hXe : Real.exp 1 ≤ X := farArm_exp_one_le hXfar
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hLnn : (0 : ℝ) ≤ Real.log X := by
    linarith [farArm_log_lb hXfar]
  have hTnn : (0 : ℝ) ≤ T := le_trans (Real.rpow_nonneg hLnn _) hT15
  have hf : ∀ n, ‖seamCoeff (ellLin g) (fun _ => 1) t₀ n‖ ≤ 1 :=
    fun n => norm_seamCoeff_le (ellLin_norm_le_one g hg) (fun _ => le_of_eq norm_one) t₀ n
  have hfloor := Mrange_floor_of_center_floor_radius hXe hT15 hR hmin
    (cap_fails_floor hf hXfar hcap)
  exact hchain X ε Utail C₂ T hX0 hTnn hε hC₂ htail hfloor

/-- **F-2b, tail wired (`far_arm_row_tailed`).**  `far_arm_row` with the abstract `Utail`
binder DISCHARGED at the concrete landed S2′ tail ledger object
`(Csup·L³)·(√L·X·(L⁴)⁻¹)` (`HalaszHead.head_prep_utail` ⟸ `HalaszSeam.s2_tail_ledger`), exactly
as `AnnHead.T1_decay_annular_tailed_polyT` does it on the near side.  The ledger's strict gate
`1 < log X` is free past `farArmThreshold` (`log X ≥ 1601`), so no threshold moves.  After this
stone the far arm's head AND tail are both concrete objects and the only remaining inputs are
the two geometric facts about `t₁` (`hmin`, `hcap`). -/
theorem far_arm_row_tailed (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t t₁ : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Csup T R : ℝ),
      X₀ ≤ X → 0 ≤ ε → 0 ≤ Csup →
      (Real.log X) ^ (1 / 15 : ℝ) ≤ T → T + seamRad X ≤ R →
      (∀ v : ℝ, |v| ≤ R →
        pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
          ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) →
      (¬ ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
        pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
          ≤ (1 / 16) * Real.log (Real.log X)) →
      annHead g t₀ X T (1 / Real.log X)
          + (Csup * (Real.log X) ^ 3)
              * (Real.sqrt (Real.log X) * X * ((Real.log X) ^ 4)⁻¹)
        ≤ (C₁ * (T / X + 1) * (Real.log X) ^ 2 + Csup) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  obtain ⟨C₁, X₀, hC₁, hrow⟩ := far_arm_row g hg t₀ t t₁
  refine ⟨C₁, max X₀ farArmThreshold, hC₁, ?_⟩
  intro X ε Csup T R hX hε hCsup hT15 hR hmin hcap
  have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXfar : farArmThreshold ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) (farArm_two_le hXfar)
  have hL1 : (1 : ℝ) < Real.log X := by linarith [farArm_log_lb hXfar]
  have htail := head_prep_utail hL1 hXpos.le hCsup
  exact hrow X ε _ Csup T R hX0 hε hCsup hT15 hR htail hmin hcap

/-- **F-2b, the CLEAN flavour (`far_arm_row_polyT`).**  `far_arm_row` at the polylog gate
`T ≤ (logX)^A` (`A : ℕ`, `A ≥ 1`), where `AnnHead.T1_decay_annular_polyT` runs at the SAME
standing `(1/32)·loglog X` floor with **no grade inflation at all**:

  `annHead + Utail ≤ (C₁ + C₂)·X·((logX)^{−1/(32e)} + (logX)^{−1/2+ε})`.

This is the far arm's winning form.  The general-`T` `far_arm_row` above is TRUE for every
`T ≥ 0`, but at `T ≍ X` its `(logX)²` factor (the honest residue of `annHead_le_socket_T`'s
crude measure×sup, AnnHead's own T-RESHAPE note) swamps the decay; the un-inflated general-`T`
row `T1_decay_annular_T_of_floor` demands the STRONG floor `2e·loglog X ≤ M_range`, which the
A-10 cap CANNOT supply — its threshold is `(1/16)·loglog X`, and `1/16 ≪ 2e`.  So: the far arm
is sharp exactly on the polylog-`T` range, and the `T ≍ X` sharpening is a socket question, not
a floor question (see the module header's residual note). -/
theorem far_arm_row_polyT (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t t₁ : ℝ)
    (A : ℕ) (hA : 1 ≤ A) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Utail C₂ T R : ℝ),
      X₀ ≤ X → 0 ≤ ε → 0 ≤ C₂ →
      (Real.log X) ^ (1 / 15 : ℝ) ≤ T → T ≤ (Real.log X) ^ A → T + seamRad X ≤ R →
      Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2) →
      (∀ v : ℝ, |v| ≤ R →
        pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
          ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) →
      (¬ ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
        pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
          ≤ (1 / 16) * Real.log (Real.log X)) →
      annHead g t₀ X T (1 / Real.log X) + Utail
        ≤ (C₁ + C₂) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  obtain ⟨C₁, X₀, hC₁, hchain⟩ := T1_decay_annular_polyT g hg t₀ t A hA
  refine ⟨C₁, max X₀ farArmThreshold, hC₁, ?_⟩
  intro X ε Utail C₂ T R hX hε hC₂ hT15 hTA hR htail hmin hcap
  have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXfar : farArmThreshold ≤ X := le_trans (le_max_right _ _) hX
  have hXe : Real.exp 1 ≤ X := farArm_exp_one_le hXfar
  have hLnn : (0 : ℝ) ≤ Real.log X := by linarith [farArm_log_lb hXfar]
  have hTnn : (0 : ℝ) ≤ T := le_trans (Real.rpow_nonneg hLnn _) hT15
  have hf : ∀ n, ‖seamCoeff (ellLin g) (fun _ => 1) t₀ n‖ ≤ 1 :=
    fun n => norm_seamCoeff_le (ellLin_norm_le_one g hg) (fun _ => le_of_eq norm_one) t₀ n
  have hfloor := Mrange_floor_of_center_floor_radius hXe hT15 hR hmin
    (cap_fails_floor hf hXfar hcap)
  exact hchain X ε Utail C₂ T hX0 hTnn hTA hε hC₂ htail hfloor

/-! ## §5 — F-3: the case tree

`SeamGate.ball_center_dichotomy_two_sided` (⟸ `CenterCore.ball_center_dichotomy`, A-10) splits
the row on the ball leg's own domain; the cap splits the live branch again.  Three arms, all
landed:

* **EMPTY** — `seamAnn ∩ seamBall = ∅`: the ball leg is `0` at ANY `S`
  (`SeamGate.ball_leg_of_inter_empty`), and the row's `hSup` binder is vacuous
  (`SeamGate.seam_sup_binder_of_inter_empty`).  `seam_row_of_inter_empty` below is that arm
  at the ROW level.
* **NEAR** — nonempty and the cap HOLDS: `FarStar.ball_sup_closed_star` supplies `hSup` and the
  weighted `8S²` leg fires (the near arm; not this file's business).
* **FAR** — the cap FAILS: `far_arm_row`, the whole-annulus grade.

The two packaging stones state the tree so the terminal can consume it with no analysis of its
own. -/

/-- **The EMPTY arm at the row level (`seam_row_of_inter_empty`).**  The weighted seam row
`SeamBallWeighted.prop_A3_T1_row_split_weighted` with its `hSup` binder discharged from the
EMPTINESS of the ball leg's domain (`SeamGate.seam_sup_binder_of_inter_empty`) — so it holds
for EVERY `S`, with no Halász supply, no cap and no minimality.  This is the arm the A-10
dichotomy hands over when the centre is small. -/
theorem seam_row_of_inter_empty
    (a : ℕ → ℂ) (N : ℕ)
    (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (Jb : ℕ)
    (X T t₁ S U : ℝ)
    (hL : 0 ≤ Real.log X) (hT : 0 ≤ T)
    (hX : 0 < X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hE : seamAnn X T ∩ seamBall X t₁ = ∅)
    (hU : (∫ t in (seamAnn X T \ seamBall X t₁) ∩ Uset fb Pseq Qseq δ Jb,
        ‖spoly N a t‖ ^ 2) ≤ U) :
    (∫ t in seamAnn X T, ‖spoly N a t‖ ^ 2)
      ≤ 8 * S ^ 2
        + (∫ t in (seamAnn X T \ seamBall X t₁) ∩ seamTtot fb Pseq Qseq δ Jb,
            ‖spoly N a t‖ ^ 2) + U :=
  prop_A3_T1_row_split_weighted a N fb Pseq Qseq δ Jb X T t₁ S U hL hT hX hXN hN2 hsupp
    (seam_sup_binder_of_inter_empty hE) hU

/-- **F-3 — THE TWO ARMS (`seam_row_both_arms`).**  The cap as a FREE case split: whatever
conclusion `B` the seam terminal wants, it suffices to prove it from the cap (the near arm,
cited abstractly) and from the `M_range` floor (the far arm, `far_arm_row`'s hypothesis).  The
cap's failure is converted for the consumer here — F-1 then F-2a — so the terminal never sees
the scale-descent page. -/
theorem seam_row_both_arms {B : Prop} {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {X T R t₁ : ℝ}
    (hXfar : farArmThreshold ≤ X) (hT15 : (Real.log X) ^ (1 / 15 : ℝ) ≤ T)
    (hR : T + seamRad X ≤ R)
    (hmin : ∀ v : ℝ, |v| ≤ R →
      pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist v) X)
    (hnear : (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
        pretDistSq f (costwist t₁) x ≤ (1 / 16) * Real.log (Real.log X)) → B)
    (hfar : (1 / 32) * Real.log (Real.log X) ≤ M_range f X T → B) : B := by
  by_cases hcap : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq f (costwist t₁) x ≤ (1 / 16) * Real.log (Real.log X)
  · exact hnear hcap
  · exact hfar (Mrange_floor_of_center_floor_radius (farArm_exp_one_le hXfar) hT15 hR hmin
      (cap_fails_floor hf hXfar hcap))

/-- **F-3 — THE FULL A-10 TREE (`seam_row_three_arms`).**  `seam_row_both_arms` with the
ball-centre dichotomy prefixed: the three arms of the seam row, packaged.  The NEAR arm
receives the two geometric facts the live branch carries — the ball leg's domain is nonempty
(`FarStar.ball_sup_closed_star`'s `hne`) and the centre sits in the annular shell thickened by
the ball radius (`SeamGate.ball_center_dichotomy_two_sided`) — so it can open
`ball_sup_closed_star` directly.  The EMPTY arm needs nothing at all
(`seam_row_of_inter_empty`).  The FAR arm receives the `M_range` floor (`far_arm_row`). -/
theorem seam_row_three_arms {B : Prop} {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {X T R t₁ : ℝ}
    (hXfar : farArmThreshold ≤ X) (hT15 : (Real.log X) ^ (1 / 15 : ℝ) ≤ T)
    (hR : T + seamRad X ≤ R)
    (hmin : ∀ v : ℝ, |v| ≤ R →
      pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist v) X)
    (hempty : seamAnn X T ∩ seamBall X t₁ = ∅ → B)
    (hnear : (seamAnn X T ∩ seamBall X t₁).Nonempty →
      seamT0 X - seamRad X ≤ |t₁| → |t₁| ≤ T + seamRad X →
      (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
        pretDistSq f (costwist t₁) x ≤ (1 / 16) * Real.log (Real.log X)) → B)
    (hfar : (1 / 32) * Real.log (Real.log X) ≤ M_range f X T → B) : B := by
  rcases Set.eq_empty_or_nonempty (seamAnn X T ∩ seamBall X t₁) with hE | hne
  · exact hempty hE
  · obtain ⟨hlo, hhi⟩ : seamT0 X - seamRad X ≤ |t₁| ∧ |t₁| ≤ T + seamRad X := by
      rcases ball_center_dichotomy_two_sided X T t₁ with hE | hband
      · exact absurd hE (Set.nonempty_iff_ne_empty.mp hne)
      · exact hband
    exact seam_row_both_arms hf hXfar hT15 hR hmin (hnear hne hlo hhi) hfar

end Salt.MR
