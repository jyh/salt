/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SPartCore
import Salt.MR.SupplyGeneric
import Salt.MR.SupStation
import Salt.MR.GradeWindowC

/-!
# A2-5 ROUTE III, the station layer — stones R5–R7 (`SPartStation`)

⟦AMENDMENT C⟧ of the S8 rescope freeze (`docs/exploration/s8-freeze-0727.md`) rules the
COEFFICIENT-LEVEL DISSECTION: for the seam datum `𝔉 := seamCoeff F 1 t₀` at a `1`-bounded
multiplicative `F`, `SPartCore`'s factorization `𝔉 = sPart 𝔉 ⍟ ellLin 𝔉` dissects the
partial sum against a completely multiplicative weight `w`,

  `∑_{n ≤ k} 𝔉(n)w(n) = ∑_{d ≤ k} sPart(d)w(d) · ∑_{m ≤ ⌊k/d⌋} ℓ(m)w(m)`,

and the split at `D` sends the head (`d ≤ D`) to the LANDED `y`-generic centre supply at the
DILATED scales `⌊k/d⌋`, the tail (`d > D`) to the trivial bound `k·cSq·D^{−1/4}`.

## The three stones

* **R6** `center_halasz_supply_wide` (§1) — the centre supply re-cut at the WIDE window
  `Xw ≤ k ≤ 2X` at a FREE floor `Xw ≥ √X` (the range the dissection's head walks: `⌊k/d⌋`
  for `d ≤ D` leaves the dyadic block `[X, 2X]` immediately; the consumer takes
  `Xw := Xd`, the dilated scale).  Its private grade page is `centerErrorGradeWide` — **THE
  SIXTH private clone of `CenterSupply.center_error_grade`**; the other five live at
  `CenterSupply` :407 (the original), `SupStation` :183 (`_st`), `SupplyGeneric` :114
  (`_Y`, the base this one is re-cut from), `GradeWindowC` :724 (`_B`) and
  `CofactorGrade` (`_A`).  The re-cut is exactly one hypothesis: `X − 1 < k` becomes
  `√X ≤ k`, whence `log k ≥ (log X)/2` in place of `log k ≥ log X − log 2`; the constant `4`
  survives because the page only ever needs `√(log X)/2 ≤ √(log k)`.  (The `k ≤ 2X` gate is
  carried for the consumer alone — the page never uses an upper bound on `k`.)
* **R5** `dilated_scale_grade` (§2) — the per-scale grade at the dilated scale, composed
  from the LANDED FREE-`M` face `GradeWindowC.rhs_grade_at_scale_windowC` (whose floor
  binder is the window one `hMwin` ALONE — `hmin`/`hgate`/`hMt` are gone and `M` is a free
  real) at `M := M₀ − dilGap X Xd`, plus the star far arm
  (`FarClose.far_supF_bound` / `FarStar.far_kernel_bound_star` / `FarStar.hfar_star`) read at
  the scale's OWN currency `k`.  The floor transport is `SPartCore`'s R4
  (`pretDistSq_scale_gap` + `mertens_gap_le`, i.e. `pretDistSq_scale_gap_dilate` at
  `Xd = X/D`): the `M₀` floor at scale `X` descends to `M₀ − dilGap X Xd` at every scale
  `≥ Xd`.
* **R7** `hCenter_dissected` (§3) — the assembled centre bound at GENERAL `F`:
  `‖∑_{n ≤ k} 𝔉(n)·w(n)‖ ≤ (cSq·S + cSq·D^{−1/4})·k` from a per-`d` inner bound `S` on
  `[1, D]`; and the AS-twin `seam_ball_leg_station_M_gen` (§4), which feeds that supply to
  `BallSup.ball_sup_of_center` — whose `hCenter` interface is DATUM-FREE (see below) — and
  lands `SupStation.seam_ball_leg_station_M`'s exit shape with the datum generalized from
  `seamCoeff (ellLin g) 1 t₀` to `seamCoeff F 1 t₀`.

## THE DOUBLE-LINEARIZATION TRAP (the wave's highest priority), audited

`BallSup` :614/:641 carry `LSeries (ellLin (seamCoeff (ellLin g) …))` statements — the
identity `ellLin ∘ ellLin = ellLin` at the `ellLin` datum, where `sPart = δ`.  At a general
`F` those are DIFFERENT OBJECTS and are NEVER touched here.  What IS consumed is
`BallSup.ball_sup_of_center` (:473), whose hypothesis list is
`hf1`/`hfmul`/`hfle`/`hsupp`/`hDatum`/`hCenter`/`hMball` — every one of them a property of
the ABSTRACT datum `f`, with no `ellLin` and no `seamCoeff` anywhere in the statement.  The
interface is datum-free; §4 instantiates it at `f := seamCoeff F 1 t₀` with no adapter.

The bridge that makes the dissection's inner sums land in the LANDED supply's own shape is
`ellLin_seamCoeff` (§0): `ellLin (seamCoeff F 1 t₀) = seamCoeff (ellLin F) 1 t₀` — the twist
`n ↦ n^{−it₀}` is completely multiplicative, so it commutes with the squarefree
linearization.  No new `M`-object is created: the `M` slot stays `pretDistSq (seamCoeff
(ellLin F) 1 t₀) (costwist ·) X`, and `pretDistSq` is prime-only
(`RHSGrade.pretDistSq_congr_primes`).

## THE DILATED-SCALES COUPLING (⟦AMENDMENT C⟧ trap 7), audited

Every hypothesis this file cites at a dilated scale is `X`-free or is cited at the dilated
scale itself: `rhs_grade_at_scale_windowC` (scale gate `e^{64} ≤ k` only), `hfar_star` (at
its own scale, `X := k`), `far_supF_bound`, `far_kernel_bound_star`,
`jointIntegrableAtC_pin_free` (all `e^{64} ≤ k`), and `prop21_unconditional_uniform_absC`
(threshold on the SCALE).  The ONE genuinely `X`-anchored object is the distance floor
`M₀ ≤ 𝔻²(…; X)`, and it is transported to the dilated scale EXPLICITLY by R4 at the price
`dilGap X Xd`, which is stated in every conclusion.  No cap-shaped hypothesis (`hrow`,
`hMcap`) is consumed anywhere in this file — the free-`M` face has none, and ⟦AMENDMENT E⟧'s
cap-free arm is verified `X`-free.

## The `D`-parameter

`D` is left FREE with its gates in-statement: `1 ≤ D` and `D ≤ k` at §3; at §4 additionally
`√X ≤ Xd ≤ X` and `D·(Xd+1) ≤ X−1`, the window arithmetic that puts every `⌊k/d⌋`
(`k ≥ ⌊X⌋₊`, `d ≤ D`) above the dilated scale `Xd`.  The consumer pins `D ≈ W^{1.1}` and
`Xd ≈ X/D` later; nothing here depends on the choice.

**LIVE GUARD** (inherited from the ball chain): the exponent `c` is free in §2, but the
consumer's is the BALL arm's halved `c = 1/(2e)`; a §8.3 consumer citing §4 is a STOP.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators LSeries.notation

/-! ## §0 — the two algebra bridges

The linearization commutes with the centre twist, and the weight `n ↦ n^{−it₁}` is
completely multiplicative on `ℕ_{>0}` — the two facts that let `SPartCore`'s coefficient-level
dissection meet the landed centre supply's statement. -/

/-- `∏ p ∈ S` of natural casts commutes with `cpow`: `(∏ p)^s = ∏ p^s`.  No positivity
hypothesis — `Complex.natCast_mul_natCast_cpow` is unconditional on natural casts. -/
private lemma natCast_prod_cpow_sp (s : ℂ) (S : Finset ℕ) :
    (((∏ p ∈ S, p : ℕ) : ℕ) : ℂ) ^ s = ∏ p ∈ S, (p : ℂ) ^ s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow]

/-- **THE LINEARIZATION/TWIST BRIDGE (`ellLin_seamCoeff`).**
`ellLin (seamCoeff F 1 t₀) = seamCoeff (ellLin F) 1 t₀`.

`ellLin` reads its datum at primes and multiplies over the (squarefree) prime factorization;
the centre twist `n ↦ n^{−it₀}` is completely multiplicative, so it factors out of the
product and reassembles as `n^{−it₀}` via `Nat.prod_primeFactors_of_squarefree`.

This is what puts the dissection's inner sum `∑_{m ≤ u} (ellLin 𝔉)(m)·w(m)` into
`SupplyGeneric.center_halasz_supply_Y`'s conclusion shape at `g := F`, with NO new datum and
NO new `M`-object. -/
theorem ellLin_seamCoeff (F : ℕ → ℂ) (t₀ : ℝ) :
    ellLin (seamCoeff F (fun _ => 1) t₀) = seamCoeff (ellLin F) (fun _ => 1) t₀ := by
  funext n
  by_cases hn : n = 0
  · simp [hn, ellLin, seamCoeff]
  · by_cases hsf : Squarefree n
    · have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsf
      have hfac : ∀ p ∈ n.primeFactors,
          (if p = 0 then (0 : ℂ) else F p * (p : ℂ) ^ (-(t₀ : ℂ) * I))
            = F p * (p : ℂ) ^ (-(t₀ : ℂ) * I) := by
        intro p hp
        exact if_neg (Nat.prime_of_mem_primeFactors hp).ne_zero
      simp only [ellLin, if_neg hn, if_pos hsf, seamCoeff, mul_one]
      rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib,
        ← natCast_prod_cpow_sp (-(t₀ : ℂ) * I) n.primeFactors, hprod]
    · simp only [ellLin, if_neg hn, if_neg hsf, seamCoeff, zero_mul]

/-- The centre weight `n ↦ n^{−it₁}` is completely multiplicative on the nonzero naturals —
`conv_partial_sum_dissect`'s `hw` binder. -/
theorem eIu_natCast_mul (t₁ : ℝ) {u v : ℕ} (hu : u ≠ 0) (hv : v ≠ 0) :
    eIu t₁ ((u * v : ℕ) : ℝ) = eIu t₁ ((u : ℕ) : ℝ) * eIu t₁ ((v : ℕ) : ℝ) := by
  have hu0 : (0 : ℝ) < (u : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hu
  have hv0 : (0 : ℝ) < (v : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hv
  rw [Nat.cast_mul, eIu_mul t₁ hu0 hv0]

/-! ## §1 (R6) — THE WIDE-WINDOW GRADE PAGE AND CENTRE SUPPLY -/

/-- `L^{−1/2} = 1/√L` for `L > 0` (`CenterSupply.rpow_neg_half_eq`, re-derived — it is
`private` there and at all five clone sites). -/
private lemma rpow_neg_half_eq_sp {Lv : ℝ} (hL : 0 < Lv) :
    Lv ^ (-(1 : ℝ) / 2) = (Real.sqrt Lv)⁻¹ := by
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) from by norm_num, Real.rpow_neg hL.le,
    Real.sqrt_eq_rpow]

/-- `25 ≤ exp 8` (`CenterSupply.twentyfive_le_exp_eight`, re-derived). -/
private lemma twentyfive_le_exp_eight_sp : (25 : ℝ) ≤ Real.exp 8 := by
  have h4 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hpos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  rw [show (8 : ℝ) = 4 + 4 from by norm_num, Real.exp_add]
  nlinarith

/-- `exp 2 < 10` — the numeral behind the `S1′` gate `0 < c₀ − 2η` at a free `Y`. -/
private lemma exp_two_lt_ten_sp : Real.exp 2 < 10 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith

/-- **THE WIDE-WINDOW GRADE PAGE (`centerErrorGradeWide`) — THE SIXTH PRIVATE CLONE.**

The other five homes of `CenterSupply.center_error_grade`'s page: `CenterSupply` :407 (the
original, at the pin's `loglog k`), `SupStation` :183 (`center_error_grade_st`),
`SupplyGeneric` :114 (`center_error_grade_Y`, at a free weight `W` — the base re-cut here),
`GradeWindowC` :724 (`center_error_grade_B`) and `CofactorGrade` (`_A`).  Each is at ITS OWN
window; this one is at the WIDE window `√X ≤ k`, which is what the Route-III dissection's
head needs (the inner scales `⌊k/d⌋`, `d ≤ D`, leave the dyadic block `[X, 2X]` at once).

  `C·k·(W/log k) + (k/√(log k) + 1) ≤ 4·k·(log X)^{−1/2+1/1000}`.

The re-cut versus `_Y` is ONE hypothesis.  `_Y` reads `X − 1 < k` and gets
`log k ≥ log X − log 2`; here `√X ≤ k` gives `log k ≥ (log X)/2` — weaker, and still enough:
the page only ever consumes `√(log X)/2 ≤ √(log k)` (from `(log X)/4 ≤ log k`) and
`√(log X) ≤ k` (here from `√(log X) ≤ √X ≤ k`, where `_Y` used `2 log X ≤ X`).  The
constant `4` is therefore unchanged, and no upper bound on `k` is used at either window. -/
private lemma centerErrorGradeWide {C W X : ℝ} {k : ℕ} (hC0 : 0 ≤ C)
    (hX8 : Real.exp 8 ≤ X) (hkw : Real.sqrt X ≤ (k : ℝ))
    (hWcap : W ≤ Real.sqrt (Real.log (k : ℝ)))
    (hB : 2 * C * Real.log (Real.log X) * Real.log X ^ (-((1 : ℝ) / 2))
        ≤ Real.log X ^ (-((1 : ℝ) / 2) + 1 / 1000)) :
    C * ((k : ℝ) * (W / Real.log (k : ℝ)))
        + ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)) + 1)
      ≤ 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
  rw [show (-((1 : ℝ) / 2) : ℝ) = -(1 : ℝ) / 2 from by norm_num] at hB
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight_sp hX8
  have hX0 : (0 : ℝ) < X := by linarith
  set Lx := Real.log X with hLdef
  have hL8 : (8 : ℝ) ≤ Lx := by
    rw [hLdef, ← Real.log_exp 8]
    exact Real.log_le_log (Real.exp_pos 8) hX8
  have hL0 : (0 : ℝ) < Lx := by linarith
  have hL1 : (1 : ℝ) ≤ Lx := by linarith
  have hsqX0 : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le hsqX0 hkw
  set Lk := Real.log (k : ℝ) with hLkdef
  -- the WIDE window: `log k ≥ Lx/2`
  have hLkhalf : Lx / 2 ≤ Lk := by
    have h1 : Real.log (Real.sqrt X) ≤ Lk := Real.log_le_log hsqX0 hkw
    rwa [Real.log_sqrt hX0.le] at h1
  have hLk1 : (1 : ℝ) ≤ Lk := by linarith
  have hLk0 : (0 : ℝ) < Lk := by linarith
  have hsqLk0 : (0 : ℝ) < Real.sqrt Lk := Real.sqrt_pos.mpr hLk0
  -- STEP A — the cap: `W/log k ≤ 1/√(log k)`
  have hsqk : Real.sqrt Lk * Real.sqrt Lk = Lk := Real.mul_self_sqrt hLk0.le
  have hcap : W / Lk ≤ 1 / Real.sqrt Lk := by
    rw [div_le_div_iff₀ hLk0 hsqLk0]
    have h1 : W * Real.sqrt Lk ≤ Real.sqrt Lk * Real.sqrt Lk :=
      mul_le_mul_of_nonneg_right hWcap hsqLk0.le
    rw [hsqk] at h1
    linarith
  have hEshape : (k : ℝ) * (W / Lk) ≤ (k : ℝ) / Real.sqrt Lk := by
    have h1 : (k : ℝ) * (W / Lk) ≤ (k : ℝ) * (1 / Real.sqrt Lk) :=
      mul_le_mul_of_nonneg_left hcap hk0.le
    rwa [mul_one_div] at h1
  -- STEP B — the window: `k/√(log k) ≤ 2·k·Lx^{−1/2}` and `1 ≤ k·Lx^{−1/2}`
  have hsqL0 : (0 : ℝ) < Real.sqrt Lx := Real.sqrt_pos.mpr hL0
  have hsqL2 : Real.sqrt Lx / 2 ≤ Real.sqrt Lk := by
    have hq : Real.sqrt (Lx / 4) = Real.sqrt Lx / 2 := by
      rw [show Lx / 4 = Lx * (1 / 2) ^ 2 from by ring, Real.sqrt_mul hL0.le,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    calc Real.sqrt Lx / 2 = Real.sqrt (Lx / 4) := hq.symm
      _ ≤ Real.sqrt Lk := Real.sqrt_le_sqrt (by linarith)
  have hsqL20 : (0 : ℝ) < Real.sqrt Lx / 2 := by linarith
  have hdes : (k : ℝ) / Real.sqrt Lk ≤ 2 * ((k : ℝ) * Lx ^ (-(1 : ℝ) / 2)) := by
    have h1 : (k : ℝ) / Real.sqrt Lk ≤ (k : ℝ) / (Real.sqrt Lx / 2) :=
      div_le_div_of_nonneg_left hk0.le hsqL20 hsqL2
    have h2 : (k : ℝ) / (Real.sqrt Lx / 2) = 2 * ((k : ℝ) * Lx ^ (-(1 : ℝ) / 2)) := by
      rw [rpow_neg_half_eq_sp hL0]
      field_simp
    linarith
  have hone : (1 : ℝ) ≤ (k : ℝ) * Lx ^ (-(1 : ℝ) / 2) := by
    have hLX : Lx ≤ X := by
      rw [hLdef]; linarith [Real.log_le_sub_one_of_pos hX0]
    have hsk : Real.sqrt Lx ≤ (k : ℝ) := le_trans (Real.sqrt_le_sqrt hLX) hkw
    rw [rpow_neg_half_eq_sp hL0, ← div_eq_mul_inv, le_div_iff₀ hsqL0]
    linarith
  -- STEP C — the absorption `2C·Lx^{−1/2} ≤ Lx^{−1/2+1/1000}` (`loglog X ≥ 1`)
  have hPnn : (0 : ℝ) ≤ Lx ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hL0.le _
  have hlogL1 : (1 : ℝ) ≤ Real.log Lx := by
    have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h8 : Real.log 8 ≤ Real.log Lx := Real.log_le_log (by norm_num) hL8
    have h83 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have habs : 2 * C * Lx ^ (-(1 : ℝ) / 2) ≤ Lx ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have hCP : (0 : ℝ) ≤ C * Lx ^ (-(1 : ℝ) / 2) := mul_nonneg hC0 hPnn
    have hprod : (0 : ℝ) ≤ C * Lx ^ (-(1 : ℝ) / 2) * (Real.log Lx - 1) :=
      mul_nonneg hCP (by linarith)
    linarith
  -- STEP D — assemble
  have hGmono : Lx ^ (-(1 : ℝ) / 2) ≤ Lx ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hterm1 : C * ((k : ℝ) * (W / Lk)) ≤ (k : ℝ) * Lx ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h1 : C * ((k : ℝ) * (W / Lk)) ≤ C * ((k : ℝ) / Real.sqrt Lk) :=
      mul_le_mul_of_nonneg_left hEshape hC0
    have h2 : C * ((k : ℝ) / Real.sqrt Lk) ≤ C * (2 * ((k : ℝ) * Lx ^ (-(1 : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left hdes hC0
    have h3 : C * (2 * ((k : ℝ) * Lx ^ (-(1 : ℝ) / 2)))
        = (k : ℝ) * (2 * C * Lx ^ (-(1 : ℝ) / 2)) := by ring
    have h4 : (k : ℝ) * (2 * C * Lx ^ (-(1 : ℝ) / 2))
        ≤ (k : ℝ) * Lx ^ (-(1 : ℝ) / 2 + 1 / 1000) := mul_le_mul_of_nonneg_left habs hk0.le
    linarith
  have hterm2 : (k : ℝ) * Lx ^ (-(1 : ℝ) / 2) ≤ (k : ℝ) * Lx ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    mul_le_mul_of_nonneg_left hGmono hk0.le
  linarith

/-- **R6 — THE WIDE-WINDOW CENTRE SUPPLY (`center_halasz_supply_wide`).**
`SupplyGeneric.center_halasz_supply_Y` (:257) re-cut from the DYADIC window
`⌊X⌋₊ ≤ k ≤ N ≤ 2X` to the WIDE window `√X ≤ k` — the range Route III's dissection head
actually walks (`⌊k/d⌋` for `d ≤ D`, `k ∈ [X, 2X]`).

  `hRHS : ∀ k ≥ √X, ‖prop21RHS (damped datum) (t₀+t₁) k h c₀ (Y k) (1/log (Y k))‖ ≤ B·k`
  ⟹  `∀ k ≥ √X, ‖∑_{n≤k} 𝔉(n)·e^{−it₁ log n}‖ ≤ (B + 4·(log X)^{−1/2+1/1000})·k`,

at `h = k/√(log k)`, `c₀ = 1 + 1/log k`, and with the SAME grade constant `4` (the page's
own re-cut is `centerErrorGradeWide`).  The `Y`-gates are `_Y`'s four, restated on the wide
range; the scale gate is `X₀ ≤ √X` (i.e. `X ≥ X₀²`), which is what the `S1′` threshold needs
at the SMALLEST scale in the window.

Everything else is `_Y`'s proof verbatim: `prop21_unconditional_uniform_absC` at the scale
`k`, `prop21_desmooth_reduction`, the twist combine, the triangle.  **LIVE GUARD**:
`c = 1/(2e)` is the BALL arm's halved constant; a §8.3 consumer citing this head is a STOP. -/
theorem center_halasz_supply_wide {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ)
    (Y : ℝ → ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (t₁ X Xw B : ℝ), X₀ ≤ Real.sqrt X → Real.sqrt X ≤ Xw → 0 ≤ B →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → 10 ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
              ≤ B * (k : ℝ)) →
      ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
        ‖∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n‖
          ≤ (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ) := by
  obtain ⟨XA, C_E, C_R, hCE0, hCR0, hrep⟩ := prop21_unconditional_uniform_absC
  obtain ⟨XB, _hXB0, hBabs⟩ :=
    loglog_absorb_pow_pin (C := 2 * (2 * C_E + C_R)) (by positivity) ((1 : ℝ) / 2)
  refine ⟨max (max (XA + 1) XB) (Real.exp 8),
    lt_of_lt_of_le (Real.exp_pos 8) (le_max_right _ _), ?_⟩
  intro t₁ X Xw B hXlb hXw hB0 hY10 hYsq hYlow hYlog hRHS k hkXw hkup
  have hkw : Real.sqrt X ≤ (k : ℝ) := le_trans hXw hkXw
  -- the scale page at the wide window's floor `√X`
  have hsq8 : Real.exp 8 ≤ Real.sqrt X := le_trans (le_max_right _ _) hXlb
  have hsqXA1 : XA + 1 ≤ Real.sqrt X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXlb
  have hsqXB : XB ≤ Real.sqrt X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXlb
  have hsq0 : (0 : ℝ) < Real.sqrt X := lt_of_lt_of_le (Real.exp_pos 8) hsq8
  have hX0 : (0 : ℝ) < X := Real.sqrt_pos.mp hsq0
  have hsqsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hsq25 : (25 : ℝ) ≤ Real.sqrt X := le_trans twentyfive_le_exp_eight_sp hsq8
  have hsqX : Real.sqrt X ≤ X := by nlinarith
  have hX8 : Real.exp 8 ≤ X := le_trans hsq8 hsqX
  have hXB : XB ≤ X := le_trans hsqXB hsqX
  have hkXA : XA ≤ (k : ℝ) := by linarith [le_trans hsqXA1 hkw]
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le hsq0 hkw
  have hk1le : (1 : ℝ) ≤ (k : ℝ) := by linarith [le_trans hsq25 hkw]
  -- the wide window's log floor: `log k ≥ (log X)/2 ≥ 4`
  have hLX8 : (8 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8]; exact Real.log_le_log (Real.exp_pos 8) hX8
  have hLklo : Real.log X / 2 ≤ Real.log (k : ℝ) := by
    have h1 : Real.log (Real.sqrt X) ≤ Real.log (k : ℝ) := Real.log_le_log hsq0 hkw
    rwa [Real.log_sqrt hX0.le] at h1
  have hLk1 : (1 : ℝ) ≤ Real.log (k : ℝ) := by linarith
  have hLk0 : (0 : ℝ) < Real.log (k : ℝ) := by linarith
  have hsqLk1 : (1 : ℝ) ≤ Real.sqrt (Real.log (k : ℝ)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hLk1
  have hsqLk0 : (0 : ℝ) < Real.sqrt (Real.log (k : ℝ)) := by linarith
  have hh0 : (0 : ℝ) < (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by positivity
  have hhX : (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) ≤ (k : ℝ) := by
    rw [div_le_iff₀ hsqLk0]; nlinarith
  -- THE `Y`-PAGE at this scale
  have hY10k : (10 : ℝ) ≤ Y (k : ℝ) := hY10 k hkXw hkup
  have hlogY2 : (2 : ℝ) ≤ Real.log (Y (k : ℝ)) := by
    have h1 : Real.log (Real.exp 2) ≤ Real.log (Y (k : ℝ)) :=
      Real.log_le_log (Real.exp_pos 2) (le_trans exp_two_lt_ten_sp.le hY10k)
    rwa [Real.log_exp] at h1
  have hlogY0 : (0 : ℝ) < Real.log (Y (k : ℝ)) := by linarith
  have hc₀ : (1 : ℝ) < 1 + 1 / Real.log (k : ℝ) := by
    have hpos : (0 : ℝ) < 1 / Real.log (k : ℝ) := by positivity
    linarith
  have hc' : (0 : ℝ) < 1 + 1 / Real.log (k : ℝ) - 2 * (1 / Real.log (Y (k : ℝ))) := by
    have hpos : (0 : ℝ) < 1 / Real.log (k : ℝ) := by positivity
    have hhalf : 2 * (1 / Real.log (Y (k : ℝ))) ≤ 1 := by
      rw [mul_one_div, div_le_one hlogY0]
      linarith
    linarith
  -- the two landed legs, at scale `k`
  have hdes := prop21_desmooth_reduction (f := ellLin g) (gJ := fun _ => 1) (t₀ + t₁)
    (fun n => ellLin_norm_le_one g hg n) (fun _ => by simp)
    (X := (k : ℝ)) (h := (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) hk1le hh0 hhX
  rw [Nat.floor_natCast] at hdes
  have hr := hrep g hg (t₀ + t₁) (X := (k : ℝ))
    (h := (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (c₀ := 1 + 1 / Real.log (k : ℝ))
    (y := Y (k : ℝ)) (η := 1 / Real.log (Y (k : ℝ)))
    hkXA rfl hc₀ rfl hc' hY10k (hYsq k hkXw hkup) (hYlow k hkXw hkup)
  have hR := hRHS k hkXw hkup
  -- the twist combine
  have hsum : (∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n)
      = ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n :=
    Finset.sum_congr rfl (fun n _ => seamCoeff_twist_combine _ _ t₀ t₁ n)
  rw [hsum]
  -- the triangle chain
  set A := ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n with hAdef
  set Bs := ∑' n, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n
    * (hatK (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) n : ℂ) with hBsdef
  set Rr := prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
    (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
    (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ))) with hRdef
  have hid : A = (A - Bs) + ((Bs - Rr) + Rr) := by ring
  have htri : ‖A‖ ≤ ‖A - Bs‖ + (‖Bs - Rr‖ + ‖Rr‖) := by
    calc ‖A‖ = ‖(A - Bs) + ((Bs - Rr) + Rr)‖ := by rw [← hid]
      _ ≤ ‖A - Bs‖ + ‖(Bs - Rr) + Rr‖ := norm_add_le _ _
      _ ≤ ‖A - Bs‖ + (‖Bs - Rr‖ + ‖Rr‖) := by
          linarith [norm_add_le (Bs - Rr) Rr]
  -- the `E`-error, reduced to the `C·k·log (Y k)/log k` shape
  have hu0 : (0 : ℝ) < (k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by linarith
  have hulogb : Real.log (k : ℝ)
      ≤ Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) :=
    Real.log_le_log hk0 (by linarith)
  have huq : ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
        / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
      ≤ 2 * (k : ℝ) / Real.log (k : ℝ) := by
    rw [div_le_div_iff₀ (by linarith) hLk0]
    nlinarith
  have hEle : C_E * (((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
          / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))))
        * Real.log (Y (k : ℝ))
      + C_R * ((k : ℝ) / Real.log (k : ℝ)) * Real.log (Y (k : ℝ))
      ≤ (2 * C_E + C_R) * ((k : ℝ) * (Real.log (Y (k : ℝ)) / Real.log (k : ℝ))) := by
    have h1 : C_E * (((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
            / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))))
          * Real.log (Y (k : ℝ))
        ≤ C_E * (2 * (k : ℝ) / Real.log (k : ℝ)) * Real.log (Y (k : ℝ)) := by
      have := mul_le_mul_of_nonneg_left huq hCE0
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have h2 : C_E * (2 * (k : ℝ) / Real.log (k : ℝ)) * Real.log (Y (k : ℝ))
          + C_R * ((k : ℝ) / Real.log (k : ℝ)) * Real.log (Y (k : ℝ))
        = (2 * C_E + C_R) * ((k : ℝ) * (Real.log (Y (k : ℝ)) / Real.log (k : ℝ))) := by
      ring
    linarith
  -- the WIDE grade page
  have hgrade := centerErrorGradeWide (C := 2 * C_E + C_R) (W := Real.log (Y (k : ℝ)))
    (X := X) (k := k) (by positivity) hX8 hkw (hYlog k hkXw hkup) (hBabs X hXB)
  have hexpand : (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ)
      = B * (k : ℝ) + 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by ring
  rw [hexpand]
  linarith


/-! ## §2 (R5) — THE GRADE AT THE DILATED SCALE -/

/-- **The scale-descent price (`dilGap`).**  Shrinking the pretentious distance's cutoff from
`X` down to `Xd ≤ X` costs at most

  `dilGap X Xd := 2·((log X − log Xd)/log Xd + 24/log Xd)`,

which is twice the Mertens mass of the primes in `(Xd, X]` (`SPartCore`'s R4:
`pretDistSq_scale_gap` composed with `mertens_gap_le`).  At the freeze's dilation
`Xd = X/D` this is EXACTLY ⟦AMENDMENT C⟧'s `ε_D` (see `dilGap_div`), and at
`D ≤ (log X)^{0.001}` it is `O(loglog X/log X) → 0`. -/
def dilGap (X Xd : ℝ) : ℝ :=
  2 * ((Real.log X - Real.log Xd) / Real.log Xd + 24 / Real.log Xd)

/-- `dilGap X (X/D) = ε_D` — ⟦AMENDMENT C⟧'s price in its own notation
(`pretDistSq_scale_gap_dilate`'s). -/
theorem dilGap_div {X D : ℝ} (hX : 0 < X) (hD : 0 < D) :
    dilGap X (X / D)
      = 2 * (Real.log D / Real.log (X / D) + 24 / Real.log (X / D)) := by
  have h : Real.log X - Real.log (X / D) = Real.log D := by
    rw [Real.log_div hX.ne' hD.ne']; ring
  unfold dilGap
  rw [h]

/-- **R5's floor transport.**  A floor `M₀` for `𝔻²(f, gg; X)` descends, at the price
`dilGap X Xd`, to a floor at EVERY scale `z ≥ Xd`: R4's scale gap down to `Xd`, then
`RHSGrade.pretDistSq_mono_scale` back up (the free direction).  This is the ONLY place in
the file where an `X`-anchored hypothesis is moved to a dilated scale, and the price is
carried in the statement. -/
theorem pretDistSq_floor_dilate {f gg : ℕ → ℂ} (hf : ∀ p, ‖f p‖ ≤ 1) (hgg : ∀ p, ‖gg p‖ ≤ 1)
    {M₀ X Xd z : ℝ} (hXd2 : 2 ≤ Xd) (hXdX : Xd ≤ X) (hz : Xd ≤ z)
    (hM₀ : M₀ ≤ pretDistSq f gg X) :
    M₀ - dilGap X Xd ≤ pretDistSq f gg z := by
  have h1 := pretDistSq_scale_gap hf hgg (u := Xd) (X := X) hXdX
  have h2 := mertens_gap_le hXd2 hXdX
  have h3 : pretDistSq f gg Xd ≤ pretDistSq f gg z := pretDistSq_mono_scale hf hgg hz
  unfold dilGap
  linarith

set_option maxHeartbeats 800000 in
-- As at `FarStar.rhs_grade_at_scale_closed_star`: the free-`M` face's binder block is
-- instantiated wholesale (five pin expressions per socket, plus the far pair), and the
-- unification exceeds the default budget.
/-- **R5 — THE DILATED-SCALE GRADE (`dilated_scale_grade`).**  The per-scale grade the
Route-III head needs at each dilated scale `k`, with the `X`-anchored distance floor
transported explicitly:

  `‖prop21RHS (damped datum) (t₀+t₁) k h c₀ y η‖
     ≤ gradeAbsConstC c Cb·k·e^{−c(M₀ − dilGap X Xd)} + farCStar·k·(log k)^{−1/(32e)}`

at the corpus pin `y = (log k)^4`, `η = 1/log y`, `h = k/√(log k)`, `c₀ = 1 + 1/log k`.

**What is consumed, and where.**  The main term is `GradeWindowC.rhs_grade_at_scale_windowC`
(:582) — the LANDED FREE-`M` face, whose floor binder is the WINDOW one `hMwin` alone
(`hmin`, `hgate`, `hMt` are gone; `M` is a free real named by the consumer) — at
`M := max 0 (M₀ − dilGap X Xd)` (the `max` discharges its `0 ≤ M` gate for free and only
strengthens the exit, since `c > 0`).  The far arm rides additively and is closed by the
STAR chain at the scale's OWN currency: `FarClose.far_supF_bound` (`hFar`),
`FarStar.far_kernel_bound_star` (`hKfar` at `T := T*(k, log k)`) and `FarStar.hfar_star`
read at `X := k` — legal because `hfar_star`'s two scale hypotheses `e ≤ X`, `X ≤ 2k` are
then `e ≤ k` and `k ≤ 2k`.  Integrability is `GradeWindowC.jointIntegrableAtC_pin_free`
(gate `e^{64} ≤ k`, no minimality, no `M`).

**The dilated-scales coupling (⟦AMENDMENT C⟧ trap 7).**  Every hypothesis above is `X`-free
(scale gate `e^{64} ≤ k` only).  The floor `hM₀` is the sole `X`-anchored input; it is moved
to scale `k` by `pretDistSq_floor_dilate`, whose price appears in the conclusion.  NO
cap-shaped hypothesis is used: the free-`M` face carries neither `hrow` nor `hMcap`.

`hgate` is the recentring geometry (`FarStar.seam_gate_star_of_nonempty` supplies it at
`Rad := seamGateRstar X Tann`); it is what turns the `hM₀` radius into the `hMwin` window. -/
theorem dilated_scale_grade {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c Cb t₀ t₁ X Xd M₀ Rad : ℝ} {k : ℕ}
    (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1) (hc1 : 2 * c < 1)
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk64 : Real.exp 64 ≤ (k : ℝ))
    (hXd2 : 2 ≤ Xd) (hXdX : Xd ≤ X) (hkXd : Xd ≤ (k : ℝ))
    (hgate : |t₁| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ Rad)
    (hM₀ : ∀ v : ℝ, |v| ≤ Rad →
      M₀ ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
        (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
        (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
      ≤ gradeAbsConstC c Cb * (k : ℝ) * Real.exp (-c * (M₀ - dilGap X Xd))
        + farCStar * (k : ℝ) * Real.log (k : ℝ) ^ (-(1 / (32 * Real.exp 1))) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 64) hk64
  have hLk64 : (64 : ℝ) ≤ Real.log (k : ℝ) := by
    rw [← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk64
  have hLk0 : (0 : ℝ) < Real.log (k : ℝ) := by linarith
  have hke : Real.exp 1 ≤ (k : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by linarith [Real.exp_one_lt_d9])) hk64
  have hk3 : Real.exp 3 ≤ (k : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hk64
  have hgtw : ∀ p, p.Prime →
      ‖(fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist (t₀ + t₁) hp.one_lt.le, mul_one]
    exact hg p hp
  have hEll : ∀ n : ℕ, ‖ellLin g n‖ ≤ 1 := ellLin_norm_le_one g hg
  set M : ℝ := max 0 (M₀ - dilGap X Xd) with hMdef
  have hM0 : (0 : ℝ) ≤ M := le_max_left _ _
  have hMlb : M₀ - dilGap X Xd ≤ M := le_max_right _ _
  -- THE WINDOW FLOOR at the dilated scale
  have hMwin : ∀ t : ℝ, |t - (t₀ + t₁)| ≤ Tstar (k : ℝ) (Real.log (k : ℝ)) →
      M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)))
        (costwist (t - (t₀ + t₁))) (k : ℝ) := by
    intro t ht
    have hshift := twisted_datum_dist_eq g (t₀ + t₁) (t - (t₀ + t₁)) (k : ℝ)
    rw [show t - (t₀ + t₁) + (t₀ + t₁) = t from by ring] at hshift
    rw [hshift]
    refine max_le (pretDistSq_nonneg _ _ _ hEll (fun n => le_of_eq (costwist_norm t n))) ?_
    -- the `X`-anchored floor at the frequency `t`
    have habs : |t - t₀| ≤ Rad := by
      have h1 : |t - t₀| ≤ |t - (t₀ + t₁)| + |t₁| := by
        have : t - t₀ = (t - (t₀ + t₁)) + t₁ := by ring
        rw [this]
        exact abs_add_le _ _
      linarith
    have hfl := hM₀ (t - t₀) habs
    rw [seamCoeff_trivial_dist_eq, show t - t₀ + t₀ = t from by ring] at hfl
    exact pretDistSq_floor_dilate hEll (fun n => le_of_eq (costwist_norm t n))
      hXd2 hXdX hkXd hfl
  -- the far arm, at the scale's own currency
  have hFfar0 : (0 : ℝ) ≤ farFbound (Real.log (k : ℝ)) := farFbound_nonneg hLk0.le
  have hFar := far_supF_bound hg (t₀' := t₀ + t₁) hk3 (rfl : Real.log (k : ℝ) = _)
    (rfl : Real.log (k : ℝ) ^ 4 = _) (rfl : 1 / Real.log (Real.log (k : ℝ) ^ 4) = _)
    (rfl : 1 + 1 / Real.log (k : ℝ) = _)
  have hKfar := far_kernel_bound_star
    (d := fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀' := t₀ + t₁)
    hk64 (rfl : Real.log (k : ℝ) = _) (rfl : Real.log (k : ℝ) ^ 4 = _)
    (rfl : 1 / Real.log (Real.log (k : ℝ) ^ 4) = _) (rfl : 1 + 1 / Real.log (k : ℝ) = _)
  have hInt := jointIntegrableAtC_pin_free hg c (t₀ + t₁) M hk64
  have hmain := rhs_grade_at_scale_windowC hg hc0 hce hc1 hCb0 hCbound hk64
    (rfl : Real.log (k : ℝ) = _) (rfl : Real.log (k : ℝ) ^ 4 = _)
    (rfl : 1 / Real.log (Real.log (k : ℝ) ^ 4) = _) (rfl : 1 + 1 / Real.log (k : ℝ) = _)
    (rfl : (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) = _) hM0 hMwin hFfar0 hFar hKfar hInt
  have hfar := hfar_star hgtw hk64 (rfl : Real.log (k : ℝ) = _)
    (rfl : Real.log (k : ℝ) ^ 4 = _) (rfl : 1 / Real.log (Real.log (k : ℝ) ^ 4) = _)
    (X := (k : ℝ)) hke (by linarith)
  -- the exponent: the `max` only strengthens
  have hexp : Real.exp (-c * M) ≤ Real.exp (-c * (M₀ - dilGap X Xd)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hC0 : (0 : ℝ) ≤ gradeAbsConstC c Cb * (k : ℝ) :=
    mul_nonneg (gradeAbsConstC_nonneg hc1 hCb0) hk0.le
  have hstep : gradeAbsConstC c Cb * (k : ℝ) * Real.exp (-c * M)
      ≤ gradeAbsConstC c Cb * (k : ℝ) * Real.exp (-c * (M₀ - dilGap X Xd)) :=
    mul_le_mul_of_nonneg_left hexp hC0
  linarith


/-! ## §3 (R7, head) — THE DISSECTED CENTRE BOUND AT GENERAL `F` -/

/-- **R7 (head) — `hCenter_dissected`.**  The Route-III centre bound at a GENERAL `1`-bounded
multiplicative `F`, assembled from `SPartCore`'s dissection and its two `cSq` pages:

  `‖∑_{n ≤ k} 𝔉(n)·n^{−it₁}‖ ≤ (cSq·S + cSq·D^{−1/4})·k`,   `𝔉 = seamCoeff F 1 t₀`,

where `S` is ANY common grade for the dilated inner sums on the head `1 ≤ d ≤ D`:

  `‖∑_{m ≤ ⌊k/d⌋} (ellLin 𝔉)(m)·m^{−it₁}‖ ≤ S·⌊k/d⌋`.

**The two halves.**  The head (`d ≤ D`) pays `∑_{d ≤ D} ‖sPart 𝔉(d)‖/d ≤ cSq`
(`sPart_seamCoeff_dirichlet_bound` at `σ = 1`) against `S·k/d` per `d`; the tail (`d > D`)
pays the TRIVIAL inner bound `⌊k/d⌋ ≤ k/d` (every `ellLin` value is `1`-bounded) against
`∑_{d > D} ‖sPart 𝔉(d)‖/d ≤ cSq·D^{−1/4}` (`sPart_seamCoeff_tail_bound`).  `cSq = 20736`
is EXPLICIT; the whole cost is the interface's absolute `C₁`, exactly as ⟦AMENDMENT C⟧
prices it.

The inner sums are stated at `seamCoeff (ellLin F) 1 t₀` — i.e. in the LANDED supply's own
datum — via `ellLin_seamCoeff`.  `D` is free: its only gates are `1 ≤ D` and `D ≤ k`. -/
theorem hCenter_dissected {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) (hFb : ∀ n, ‖F n‖ ≤ 1)
    (t₀ t₁ : ℝ) {D k : ℕ} (hD : 1 ≤ D) (hDk : D ≤ k) {S : ℝ} (hS : 0 ≤ S)
    (hInner : ∀ d : ℕ, 1 ≤ d → d ≤ D →
      ‖∑ m ∈ Finset.Icc 1 (k / d), seamCoeff (ellLin F) (fun _ => 1) t₀ m * eIu (-t₁) m‖
        ≤ S * ((k / d : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.Icc 1 k, seamCoeff F (fun _ => 1) t₀ n * eIu (-t₁) n‖
      ≤ (cSq * S + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) * (k : ℝ) := by
  classical
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hEllOne : ∀ m : ℕ, ‖ellLin (seamCoeff F (fun _ => 1) t₀) m‖ ≤ 1 :=
    fun m => ellLin_norm_le_one _ (fun p _ => norm_seamCoeff_trivial_le hFb t₀ p) m
  -- the inner sums, in the landed supply's own datum
  have hInner' : ∀ d : ℕ, 1 ≤ d → d ≤ D →
      ‖∑ m ∈ Finset.Icc 1 (k / d),
          ellLin (seamCoeff F (fun _ => 1) t₀) m * eIu (-t₁) (m : ℝ)‖
        ≤ S * ((k / d : ℕ) : ℝ) := by
    intro d h1 h2
    rw [ellLin_seamCoeff F t₀]
    exact hInner d h1 h2
  -- the trivial inner bound (every `ellLin` value is `1`-bounded)
  have hTriv : ∀ d : ℕ,
      ‖∑ m ∈ Finset.Icc 1 (k / d),
          ellLin (seamCoeff F (fun _ => 1) t₀) m * eIu (-t₁) (m : ℝ)‖
        ≤ ((k / d : ℕ) : ℝ) := by
    intro d
    calc ‖∑ m ∈ Finset.Icc 1 (k / d),
            ellLin (seamCoeff F (fun _ => 1) t₀) m * eIu (-t₁) (m : ℝ)‖
        ≤ ∑ m ∈ Finset.Icc 1 (k / d),
            ‖ellLin (seamCoeff F (fun _ => 1) t₀) m * eIu (-t₁) (m : ℝ)‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc 1 (k / d), (1 : ℝ) := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [norm_mul, norm_eIu, mul_one]
          exact hEllOne m
      _ = ((k / d : ℕ) : ℝ) := by simp
  -- THE DISSECTION (`SPartCore` R3 at the completely multiplicative weight `n ↦ n^{−it₁}`)
  have hdis : ∑ n ∈ Finset.Icc 1 k, seamCoeff F (fun _ => 1) t₀ n * eIu (-t₁) (n : ℝ)
      = ∑ d ∈ Finset.Icc 1 k, sPart (seamCoeff F (fun _ => 1) t₀) d * eIu (-t₁) (d : ℝ)
          * ∑ m ∈ Finset.Icc 1 (k / d),
              ellLin (seamCoeff F (fun _ => 1) t₀) m * eIu (-t₁) (m : ℝ) := by
    have h := conv_partial_sum_dissect (s := sPart (seamCoeff F (fun _ => 1) t₀))
      (ℓ := ellLin (seamCoeff F (fun _ => 1) t₀))
      (w := fun n : ℕ => eIu (-t₁) (n : ℝ))
      (fun {u v} hu hv => eIu_natCast_mul (-t₁) hu hv) k
    rw [sPart_seamCoeff_factorization F t₀] at h
    exact h
  -- the head/tail split at `D`
  have hsplit : Finset.Icc 1 k = Finset.Icc 1 D ∪ Finset.Icc (D + 1) k := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 D) (Finset.Icc (D + 1) k) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    rw [Finset.mem_Icc] at hd hd'
    omega
  -- THE HEAD
  have hhead : ‖∑ d ∈ Finset.Icc 1 D,
        sPart (seamCoeff F (fun _ => 1) t₀) d * eIu (-t₁) (d : ℝ)
          * ∑ m ∈ Finset.Icc 1 (k / d),
              ellLin (seamCoeff F (fun _ => 1) t₀) m * eIu (-t₁) (m : ℝ)‖
      ≤ cSq * S * (k : ℝ) := by
    calc ‖∑ d ∈ Finset.Icc 1 D,
            sPart (seamCoeff F (fun _ => 1) t₀) d * eIu (-t₁) (d : ℝ)
              * ∑ m ∈ Finset.Icc 1 (k / d),
                  ellLin (seamCoeff F (fun _ => 1) t₀) m * eIu (-t₁) (m : ℝ)‖
        ≤ ∑ d ∈ Finset.Icc 1 D,
            ‖sPart (seamCoeff F (fun _ => 1) t₀) d * eIu (-t₁) (d : ℝ)
              * ∑ m ∈ Finset.Icc 1 (k / d),
                  ellLin (seamCoeff F (fun _ => 1) t₀) m * eIu (-t₁) (m : ℝ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 D,
            (‖sPart (seamCoeff F (fun _ => 1) t₀) d‖ * (d : ℝ) ^ (-(1 : ℝ)))
              * (S * (k : ℝ)) := by
          refine Finset.sum_le_sum fun d hd => ?_
          obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
          have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
          have hkd : ((k / d : ℕ) : ℝ) ≤ (k : ℝ) / (d : ℝ) := Nat.cast_div_le
          have hT := hInner' d hd1 hdD
          have hT' : ‖∑ m ∈ Finset.Icc 1 (k / d),
              ellLin (seamCoeff F (fun _ => 1) t₀) m * eIu (-t₁) (m : ℝ)‖
                ≤ S * ((k : ℝ) / (d : ℝ)) := by
            refine le_trans hT ?_
            exact mul_le_mul_of_nonneg_left hkd hS
          rw [norm_mul, norm_mul, norm_eIu, mul_one, Real.rpow_neg_one]
          have hprod : (‖sPart (seamCoeff F (fun _ => 1) t₀) d‖ * (d : ℝ)⁻¹) * (S * (k : ℝ))
              = ‖sPart (seamCoeff F (fun _ => 1) t₀) d‖ * (S * ((k : ℝ) / (d : ℝ))) := by
            field_simp
          rw [hprod]
          exact mul_le_mul_of_nonneg_left hT' (norm_nonneg _)
      _ = (∑ d ∈ Finset.Icc 1 D,
            ‖sPart (seamCoeff F (fun _ => 1) t₀) d‖ * (d : ℝ) ^ (-(1 : ℝ)))
              * (S * (k : ℝ)) := by rw [Finset.sum_mul]
      _ ≤ cSq * (S * (k : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hS hk0)
          exact sPart_seamCoeff_dirichlet_bound hFm hFb t₀ (σ := 1) (by norm_num) D
      _ = cSq * S * (k : ℝ) := by ring
  -- THE TAIL
  have htail : ‖∑ d ∈ Finset.Icc (D + 1) k,
        sPart (seamCoeff F (fun _ => 1) t₀) d * eIu (-t₁) (d : ℝ)
          * ∑ m ∈ Finset.Icc 1 (k / d),
              ellLin (seamCoeff F (fun _ => 1) t₀) m * eIu (-t₁) (m : ℝ)‖
      ≤ cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) * (k : ℝ) := by
    calc ‖∑ d ∈ Finset.Icc (D + 1) k,
            sPart (seamCoeff F (fun _ => 1) t₀) d * eIu (-t₁) (d : ℝ)
              * ∑ m ∈ Finset.Icc 1 (k / d),
                  ellLin (seamCoeff F (fun _ => 1) t₀) m * eIu (-t₁) (m : ℝ)‖
        ≤ ∑ d ∈ Finset.Icc (D + 1) k,
            ‖sPart (seamCoeff F (fun _ => 1) t₀) d * eIu (-t₁) (d : ℝ)
              * ∑ m ∈ Finset.Icc 1 (k / d),
                  ellLin (seamCoeff F (fun _ => 1) t₀) m * eIu (-t₁) (m : ℝ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.Icc (D + 1) k,
            (‖sPart (seamCoeff F (fun _ => 1) t₀) d‖ / (d : ℝ)) * (k : ℝ) := by
          refine Finset.sum_le_sum fun d hd => ?_
          obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
          have hd0 : (0 : ℝ) < (d : ℝ) := by
            have : 1 ≤ d := by omega
            exact_mod_cast this
          have hkd : ((k / d : ℕ) : ℝ) ≤ (k : ℝ) / (d : ℝ) := Nat.cast_div_le
          have hT : ‖∑ m ∈ Finset.Icc 1 (k / d),
              ellLin (seamCoeff F (fun _ => 1) t₀) m * eIu (-t₁) (m : ℝ)‖
                ≤ (k : ℝ) / (d : ℝ) := le_trans (hTriv d) hkd
          rw [norm_mul, norm_mul, norm_eIu, mul_one]
          have hprod : (‖sPart (seamCoeff F (fun _ => 1) t₀) d‖ / (d : ℝ)) * (k : ℝ)
              = ‖sPart (seamCoeff F (fun _ => 1) t₀) d‖ * ((k : ℝ) / (d : ℝ)) := by
            field_simp
          rw [hprod]
          exact mul_le_mul_of_nonneg_left hT (norm_nonneg _)
      _ = (∑ d ∈ Finset.Icc (D + 1) k,
            ‖sPart (seamCoeff F (fun _ => 1) t₀) d‖ / (d : ℝ)) * (k : ℝ) := by
          rw [Finset.sum_mul]
      _ ≤ (cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) * (k : ℝ) :=
          mul_le_mul_of_nonneg_right (sPart_seamCoeff_tail_bound hFm hFb t₀ hD k) hk0
      _ = cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) * (k : ℝ) := by ring
  -- assemble
  rw [hdis, hsplit, Finset.sum_union hdisj]
  refine le_trans (norm_add_le _ _) ?_
  have hring : (cSq * S + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) * (k : ℝ)
      = cSq * S * (k : ℝ) + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) * (k : ℝ) := by ring
  rw [hring]
  linarith


/-! ## §4 (R7, the AS-twin) — THE STATION EXIT AT GENERAL `F`

`BallSup.ball_sup_of_center`'s hypothesis list is DATUM-FREE (see the module docstring's
audit), so §3's supply plugs straight in at `f := seamCoeff F 1 t₀`.  The four `Y`-gates are
discharged at the CORPUS PIN `Y x = (log x)^4` from a single scale gate `e^{4096} ≤ k` — the
binding one being `4 log L ≤ √L`, i.e. `8 log s ≤ s` at `s = √L ≥ 64`. -/

/-- `8·log L ≤ L` for `L ≥ 64` (`FarStar.eight_log_le_selfT`, re-derived — `private` there). -/
private lemma eight_log_le_self_sp {Lv : ℝ} (h : 64 ≤ Lv) : 8 * Real.log Lv ≤ Lv := by
  have hL0 : (0 : ℝ) < Lv := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt Lv := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt Lv := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt h
  have hsq : Real.sqrt Lv * Real.sqrt Lv = Lv := Real.mul_self_sqrt hL0.le
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hlog : Real.log (Real.sqrt Lv) ≤ Real.sqrt Lv / Real.exp 1 := by
    have h1 : Real.log (Real.sqrt Lv / Real.exp 1) ≤ Real.sqrt Lv / Real.exp 1 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hs0.ne' (Real.exp_ne_zero 1), Real.log_exp] at h1
    linarith
  have hhalf : Real.log (Real.sqrt Lv) = Real.log Lv / 2 := Real.log_sqrt hL0.le
  have hdiv : Real.sqrt Lv / Real.exp 1 ≤ Real.sqrt Lv / 2 :=
    div_le_div_of_nonneg_left hs0.le (by norm_num) he2
  rw [hhalf] at hlog
  nlinarith

/-- **The four `Y`-gates at the corpus pin `Y x = (log x)^4`**, from the single scale gate
`e^{4096} ≤ k`.  The binding one is the fourth, `log (Y k) = 4 log L ≤ √L`, which is
`8 log s ≤ s` at `s = √L`; it needs `√L ≥ 64`, i.e. `L ≥ 4096`.  (`SupplyGeneric`'s
`ypin2_gates_Y` is the same page at the OTHER pin `y₂ = exp(L^{2/5})`, where the gate is
`2/5 < 1/2`.) -/
private lemma ypin4_gates_sp {k : ℝ} (hk : Real.exp 4096 ≤ k) :
    10 ≤ Real.log k ^ 4 ∧ Real.log k ^ 4 ≤ Real.sqrt k
      ∧ Real.sqrt (Real.log k) ≤ Real.log k ^ 4
      ∧ Real.log (Real.log k ^ 4) ≤ Real.sqrt (Real.log k) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos _) hk
  have hL : (4096 : ℝ) ≤ Real.log k := by
    rw [← Real.log_exp 4096]; exact Real.log_le_log (Real.exp_pos _) hk
  have hL0 : (0 : ℝ) < Real.log k := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log k := by linarith
  have hL4 : Real.log k ≤ Real.log k ^ 4 := le_self_pow₀ hL1 (by norm_num)
  have hsqL0 : (0 : ℝ) < Real.sqrt (Real.log k) := Real.sqrt_pos.mpr hL0
  have hsqLsq : Real.sqrt (Real.log k) * Real.sqrt (Real.log k) = Real.log k :=
    Real.mul_self_sqrt hL0.le
  have hsqL64 : (64 : ℝ) ≤ Real.sqrt (Real.log k) := by
    have h64 : Real.sqrt 4096 = 64 := by
      rw [show (4096 : ℝ) = 64 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt hL
  have hsqLle : Real.sqrt (Real.log k) ≤ Real.log k := by nlinarith
  -- the log-power identity
  have hlogpow : Real.log (Real.log k ^ 4) = 4 * Real.log (Real.log k) := by
    rw [Real.log_pow]; push_cast; ring
  -- the binding gate: `4 log L ≤ √L`
  have hbind : 4 * Real.log (Real.log k) ≤ Real.sqrt (Real.log k) := by
    have h8 := eight_log_le_self_sp hsqL64
    have hhalf : Real.log (Real.sqrt (Real.log k)) = Real.log (Real.log k) / 2 :=
      Real.log_sqrt hL0.le
    rw [hhalf] at h8
    linarith
  -- gate 2: `L^4 ≤ √k`
  have hg2 : Real.log k ^ 4 ≤ Real.sqrt k := by
    have hsk : Real.sqrt k = Real.exp (Real.log k * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hk0]
    have hp4 : Real.log k ^ 4 = Real.exp (4 * Real.log (Real.log k)) := by
      rw [← hlogpow]
      exact (Real.exp_log (by positivity)).symm
    rw [hsk, hp4]
    refine Real.exp_le_exp.mpr ?_
    have h8 := eight_log_le_self_sp (le_trans (by norm_num) hL)
    linarith
  refine ⟨by nlinarith, hg2, le_trans hsqLle hL4, ?_⟩
  rw [hlogpow]
  exact hbind

/-- The floor of a real quotient dominates any `z` one unit below it: if `z + 1 ≤ k/d` then
`z ≤ ⌊k/d⌋` (Nat division).  The dissection's window arithmetic. -/
private lemma le_natDiv_of_le {k d : ℕ} {z : ℝ} (hd : 1 ≤ d)
    (h : z + 1 ≤ (k : ℝ) / (d : ℝ)) : z ≤ ((k / d : ℕ) : ℝ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmod : (d : ℝ) * ((k / d : ℕ) : ℝ) + ((k % d : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast Nat.div_add_mod k d
  have hlt : ((k % d : ℕ) : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.mod_lt k (show 0 < d by omega)
  have h2 : (k : ℝ) / (d : ℝ) - 1 < ((k / d : ℕ) : ℝ) := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hd0]
    nlinarith
  linarith


set_option maxHeartbeats 1000000 in
-- As at `SupStation.seam_ball_leg_station_M`: the crown's binder block is instantiated
-- wholesale and the `S`-slot carries the assembled grade expression twice.
/-- **R7 (the AS-twin) — THE STATION EXIT AT GENERAL `F` (`seam_ball_leg_station_M_gen`).**
`SupStation.seam_ball_leg_station_M` (:717) with the DATUM GENERALIZED from
`seamCoeff (ellLin g) 1 t₀` to `seamCoeff F 1 t₀` at any `1`-bounded multiplicative `F`:

  `‖A_t(m)‖ ≤ ballSupS X S₀ · m/(1+|t−t₁|)`,
  `S₀ = cSq·(C₁(c,Cb)·e^{−(1/(2e))(M₀ − dilGap X Xd)} + farCStar·(log X/2)^{−1/(32e)}
        + 4(log X)^{−1/2+1/1000}) + cSq·D^{−1/4}`,

with `C₁(c,Cb) = gradeAbsConstC (1/(2e)) Cb` EXPLICIT and `cSq = 20736`.  This is the shape
`SeamBallWeighted.ball_leg_of_sup_weighted` / `prop_A3_T1_row_split_weighted` consume in
their `hSup` slot (the ball leg then lands as `8S₀²`).

**How the datum generality is bought.**  §3's `hCenter_dissected` supplies
`BallSup.ball_sup_of_center`'s `hCenter` binder at the general datum; every OTHER hypothesis
of that stone is datum-free and is discharged here at `f := seamCoeff F 1 t₀`
(`SPartCore.seamCoeff_one_eq_one`, `seamCoeff_isMultiplicative`,
`norm_seamCoeff_trivial_le`, and `SmallStones.hMball_of_A4_cap` through
`CenterSupply.pretDistSq_twist_slot`).  The inner sums at the dilated scales `⌊k/d⌋` ride
§1's wide supply at the corpus pin `Y x = (log x)^4` (gates by `ypin4_gates_sp`) with §2's
`hRHS`; the far currency is majorised from the scale's own `log k` to `log X/2` (legal on
the window `√X ≤ Xd ≤ ⌊k/d⌋`).

**Carried hypotheses, enumerated.**  (1) `F` `1`-bounded multiplicative; (2) the scale frame
`X₀ ≤ √X`, `X ≤ N ≤ 2X`; (3) `0 ≤ Cb` + `ShortIntervalDatum Cb`; (4) the dissection gates
`1 ≤ D`, `√X ≤ Xd ≤ X`, `D·(Xd+1) ≤ X−1` (which is what puts every `⌊k/d⌋` above `Xd`);
(5) the recentring gate `|t₁| + T*(2X, log 2X) ≤ Rad` (`Tstar_mono` carries it to every
dilated scale) and the DISTANCE FLOOR `M₀` on `|v| ≤ Rad` — the ONE `X`-anchored input,
transported at the stated price `dilGap X Xd`; (6) `a`'s two coefficient equations; (7)
`hMcap`, the A-10 ball cap at the general datum, on `[X, 2X]`.  **No row cap, no produced
centre, no minimality** — `t₁` is FREE (⟦AMENDMENT A⟧'s option-W reading), which is what
lets the consumer choose the ball's centre. -/
theorem seam_ball_leg_station_M_gen {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) (hFb : ∀ n, ‖F n‖ ≤ 1) (t₀ t₁ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N D : ℕ) (Cb Xd M₀ Rad T : ℝ) (a : ℕ → ℂ),
        X₀ ≤ Real.sqrt X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X →
        0 ≤ Cb → ShortIntervalDatum Cb →
        1 ≤ D → Real.sqrt X ≤ Xd → Xd ≤ X → (D : ℝ) * (Xd + 1) ≤ X - 1 →
        |t₁| + Tstar (2 * X) (Real.log (2 * X)) ≤ Rad →
        (∀ v : ℝ, |v| ≤ Rad →
          M₀ ≤ pretDistSq (seamCoeff (ellLin F) (fun _ => 1) t₀) (costwist v) X) →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff F (fun _ => 1) t₀ n) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
          pretDistSq (seamCoeff F (fun _ => 1) t₀) (costwist t₁) x
            ≤ 1 / 16 * Real.log (Real.log X)) →
        ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N →
            ‖spolyA a t m‖
              ≤ ballSupS X (cSq * (gradeAbsConstC (1 / (2 * Real.exp 1)) Cb
                      * Real.exp (-(1 / (2 * Real.exp 1)) * (M₀ - dilGap X Xd))
                    + farCStar * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1)))
                    + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
                  + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) * m / (1 + |t - t₁|) := by
  have hgF : ∀ p : ℕ, p.Prime → ‖F p‖ ≤ 1 := fun p _ => hFb p
  have hF1 : F 1 = 1 := by
    have h := hFm.map_one
    rwa [toAF_apply, if_neg one_ne_zero] at h
  obtain ⟨X₁, hX₁0, hsupply⟩ :=
    center_halasz_supply_wide hgF t₀ (fun x => Real.log x ^ 4)
  refine ⟨max (max X₁ ballMertensThreshold) (Real.exp 4096),
    lt_of_lt_of_le (Real.exp_pos 4096) (le_max_right _ _), ?_⟩
  intro X N D Cb Xd M₀ Rad T a hXlb hXN hN2 hCb0 hCbound hD hsqXd hXdX hDgate hRad hM₀
    hsupp hDatum hMcap
  set c : ℝ := 1 / (2 * Real.exp 1) with hcdef
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc0 : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hc1 : 2 * c < 1 := by
    rw [hcdef, mul_one_div, div_lt_one (by positivity)]
    linarith
  have hce : c ≤ 1 / Real.exp 1 := by
    rw [hcdef, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [Real.exp_pos (1 : ℝ)]
  -- the scale page
  have hX1lb : X₁ ≤ Real.sqrt X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXlb
  have hthlb : ballMertensThreshold ≤ Real.sqrt X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXlb
  have hsq4096 : Real.exp 4096 ≤ Real.sqrt X := le_trans (le_max_right _ _) hXlb
  have hexp4097 : (4097 : ℝ) ≤ Real.exp 4096 := by linarith [Real.add_one_le_exp (4096 : ℝ)]
  have hsq0 : (0 : ℝ) < Real.sqrt X := lt_of_lt_of_le (Real.exp_pos _) hsq4096
  have hX0 : (0 : ℝ) < X := Real.sqrt_pos.mp hsq0
  have hsqsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hsq1 : (1 : ℝ) ≤ Real.sqrt X := by linarith
  have hsqX : Real.sqrt X ≤ X := by nlinarith
  have hXth : ballMertensThreshold ≤ X := le_trans hthlb hsqX
  have hX3 : (3 : ℝ) ≤ X := le_trans three_le_ballMertensThreshold hXth
  have hXexp : Real.exp 8192 ≤ X := by
    have hsplit : Real.exp 8192 = Real.exp 4096 * Real.exp 4096 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (4096 : ℝ)]
  have hLX : (8192 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8192]; exact Real.log_le_log (Real.exp_pos _) hXexp
  have hLhalf0 : (0 : ℝ) < Real.log X / 2 := by linarith
  have hXd2 : (2 : ℝ) ≤ Xd := by linarith [le_trans hsq4096 hsqXd]
  -- the datum facts (all datum-free interfaces of `ball_sup_of_center`)
  have hfle : ∀ n : ℕ, ‖seamCoeff F (fun _ => 1) t₀ n‖ ≤ 1 := norm_seamCoeff_trivial_le hFb t₀
  have hf1 : seamCoeff F (fun _ => 1) t₀ 1 = 1 := seamCoeff_one_eq_one hF1 t₀
  have hfmul : ∀ p q : ℕ, Nat.Coprime p q →
      seamCoeff F (fun _ => 1) t₀ (p * q)
        = seamCoeff F (fun _ => 1) t₀ p * seamCoeff F (fun _ => 1) t₀ q := by
    intro p q hpq
    by_cases hp : p = 0
    · subst hp
      have hq1 : q = 1 := Nat.coprime_zero_left q |>.mp hpq
      subst hq1
      simp [seamCoeff]
    · by_cases hq : q = 0
      · subst hq
        have hp1 : p = 1 := Nat.coprime_zero_right p |>.mp hpq
        subst hp1
        simp [seamCoeff]
      · have hmul := (seamCoeff_isMultiplicative hFm t₀).map_mul_of_coprime hpq
        have hpq0 : p * q ≠ 0 := Nat.mul_ne_zero hp hq
        rwa [toAF_apply, toAF_apply, toAF_apply, if_neg hpq0, if_neg hp, if_neg hq] at hmul
  have hMball : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (fun n => seamCoeff F (fun _ => 1) t₀ n * eIu (-t₁) n) (fun _ => 1) x
        ≤ Salt.Mertens.SPartial x / 8 := by
    refine hMball_of_A4_cap hXth ?_
    intro x h1 h2
    rw [← pretDistSq_twist_slot]
    exact hMcap x h1 h2
  -- the grade constant at the dilated scales
  set B : ℝ := gradeAbsConstC c Cb * Real.exp (-c * (M₀ - dilGap X Xd))
      + farCStar * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) with hBdef
  have hgc0 : (0 : ℝ) ≤ gradeAbsConstC c Cb := gradeAbsConstC_nonneg hc1 hCb0
  have hrp0 : (0 : ℝ) ≤ (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) :=
    Real.rpow_nonneg hLhalf0.le _
  have hB0 : (0 : ℝ) ≤ B := by
    have h1 := mul_nonneg hgc0 (Real.exp_nonneg (-c * (M₀ - dilGap X Xd)))
    have h2 := mul_nonneg farCStar_nonneg hrp0
    rw [hBdef]; linarith
  -- the window's scale gate
  have hk4096 : ∀ k : ℕ, Xd ≤ (k : ℝ) → Real.exp 4096 ≤ (k : ℝ) :=
    fun k h => le_trans (le_trans hsq4096 hsqXd) h
  have hLklo : ∀ k : ℕ, Xd ≤ (k : ℝ) → Real.log X / 2 ≤ Real.log (k : ℝ) := by
    intro k h
    have h1 : Real.log (Real.sqrt X) ≤ Real.log (k : ℝ) :=
      Real.log_le_log hsq0 (le_trans hsqXd h)
    rwa [Real.log_sqrt hX0.le] at h1
  -- §2 AT EVERY DILATED SCALE — the wide supply's `hRHS` binder
  have hRHSb : ∀ k : ℕ, Xd ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
      ‖prop21RHS (fun p => F p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
          (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
          ((fun x => Real.log x ^ 4) (k : ℝ))
          (1 / Real.log ((fun x => Real.log x ^ 4) (k : ℝ)))‖
        ≤ B * (k : ℝ) := by
    intro k hk1 hk2
    have hkA := hk4096 k hk1
    have hk64 : Real.exp 64 ≤ (k : ℝ) :=
      le_trans (Real.exp_le_exp.mpr (by norm_num)) hkA
    have hkee : Real.exp (Real.exp 1) ≤ (k : ℝ) :=
      le_trans (Real.exp_le_exp.mpr (by linarith [Real.exp_one_lt_d9])) hkA
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hgate : |t₁| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ Rad := by
      have hmono := Tstar_mono hkee hk2
      linarith
    have hmain := dilated_scale_grade hgF (c := c) (Cb := Cb) (t₀ := t₀) (t₁ := t₁)
      (X := X) (Xd := Xd) (M₀ := M₀) (Rad := Rad) (k := k)
      hc0 hce hc1 hCb0 hCbound hk64 hXd2 hXdX hk1 hgate hM₀
    refine le_trans hmain ?_
    have hfarmono : Real.log (k : ℝ) ^ (-(1 / (32 * Real.exp 1)))
        ≤ (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) :=
      Real.rpow_le_rpow_of_nonpos hLhalf0 (hLklo k hk1)
        (neg_nonpos.mpr (by positivity))
    have hfk : farCStar * (k : ℝ) * Real.log (k : ℝ) ^ (-(1 / (32 * Real.exp 1)))
        ≤ farCStar * (k : ℝ) * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) :=
      mul_le_mul_of_nonneg_left hfarmono (mul_nonneg farCStar_nonneg hk0)
    have hring : B * (k : ℝ)
        = gradeAbsConstC c Cb * (k : ℝ) * Real.exp (-c * (M₀ - dilGap X Xd))
          + farCStar * (k : ℝ) * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) := by
      rw [hBdef]; ring
    rw [hring]
    linarith
  -- §1 AT EVERY DILATED SCALE
  have hSupplyAt := hsupply t₁ X Xd B hX1lb hsqXd hB0
    (fun k h _ => (ypin4_gates_sp (hk4096 k h)).1)
    (fun k h _ => (ypin4_gates_sp (hk4096 k h)).2.1)
    (fun k h _ => (ypin4_gates_sp (hk4096 k h)).2.2.1)
    (fun k h _ => (ypin4_gates_sp (hk4096 k h)).2.2.2)
    hRHSb
  -- §3: the dissected centre bound, i.e. `ball_sup_of_center`'s `hCenter`
  set S : ℝ := B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) with hSdef
  have hS0 : (0 : ℝ) ≤ S := by
    have h1 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
      Real.rpow_nonneg (by linarith) _
    rw [hSdef]; linarith
  have hDR : (D : ℝ) ≤ X - 1 := by
    have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    nlinarith
  have hCenter : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ‖∑ n ∈ Finset.Icc 1 k, seamCoeff F (fun _ => 1) t₀ n * eIu (-t₁) n‖
        ≤ (cSq * S + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) * (k : ℝ) := by
    intro k hk1 hk2
    have hkX : X - 1 < (k : ℝ) := by
      have h1 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
      have h2 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk1
      linarith
    have hkN : (k : ℝ) ≤ 2 * X := le_trans (Nat.cast_le.mpr hk2) hN2
    have hDk : D ≤ k := by
      have hlt : (D : ℝ) < (k : ℝ) := by linarith
      exact_mod_cast le_of_lt hlt
    refine hCenter_dissected hFm hFb t₀ t₁ hD hDk hS0 ?_
    intro d hd1 hdD
    have hdD' : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hdD
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hulow : Xd ≤ ((k / d : ℕ) : ℝ) := by
      refine le_natDiv_of_le hd1 ?_
      rw [le_div_iff₀ hd0]
      have h1 : (Xd + 1) * (d : ℝ) ≤ (Xd + 1) * (D : ℝ) :=
        mul_le_mul_of_nonneg_left hdD' (by linarith)
      have h2 : (Xd + 1) * (D : ℝ) = (D : ℝ) * (Xd + 1) := by ring
      linarith
    have huup : ((k / d : ℕ) : ℝ) ≤ 2 * X := by
      have h1 : ((k / d : ℕ) : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Nat.div_le_self k d
      linarith
    exact hSupplyAt (k / d) hulow huup
  have hS₀ : (0 : ℝ) ≤ cSq * S + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have hcS : (0 : ℝ) ≤ cSq := by rw [cSq]; norm_num
    have h1 : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg D) _
    have := mul_nonneg hcS hS0
    have := mul_nonneg hcS h1
    linarith
  exact ball_sup_of_center hX3 hXN hN2 hf1 hfmul hfle hS₀ hsupp hDatum hCenter hMball


end Salt.MR
