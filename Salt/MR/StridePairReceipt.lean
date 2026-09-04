/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# λ-BV wave 2-S, step F3 — THE REGIME PAIRING (MR half): the `h`-lane door RECEIPT with the
# caller's floor and the scale multiplier EXPOSED, at a generic frequency-set family

`Salt/Entropy/Chowla/StridePair.lean` shrinks a door regime to the affine regime and transports the
plain `L²` door over the affine set to the affine door at Tao's range.  What it needs is a door
regime `R` carrying (i) `R.Hlo = U1floor` for a CALLER-CHOSEN floor `U1floor ≥ flatDesignBase A`
(so that `a ∣ R.Hlo`), (ii) `StrideScale a R` (the outer scale divisible by `a` with the six
`x`-floors met at `x/a`), and (iii) the plain `L²` door over the AFFINE set
`bigXiAffD a b h` at a closed numeral grade.  None of the three is exported by the landed
`h`-lane headline (`logChowla2_v7_rated_h`, V7RatedH.lean:1063): it exports `R.Hlo =
flatDesignBase A` (the floor slot is instantiated at H6/H7), `g R.Hhi R.ω ≤ R.x` at `g ≡ 0` (the
scale slot is spent), and `¬ logChowlaFails` (the door is SPENT at the head's tail, minted over
`bigXiH h`).  This file is `DoorReceipt.lean`'s generator (`FlatHeadForm … V7RatedForm`, the seven
replays, the door-head, the chain, the receipt) ported to the `h` lane's compose chain
(`S16ComposeLH.lean`, `V7RatedH.lean`), with FOUR deltas, each named at the form that carries it:

  Δ1 THE SET IS A PARAMETER.  Every form takes `Xi : XiFamily` in place of `bigXiH h`: the road's
     door-L2 supply (`m4_doorL2_supply_H_L_gk_khoist`, S16ComposeLH:1072) reads the set only
     through the arc bridge `harc`, the count `hXi` and the fused insert budget `hins` —
     `parseval_insert_budget_door` (M4ParsevalStone:341) takes `Xi` as a binder — so the road is
     replayed ONCE at `Xi` with the bridge as a HYPOTHESIS
     (`m4_second_road_L2_Set_gk_flatRoot_L_khoist`).
     At `Xi := bigXiH h` the bridge is `nearRatTight_of_bigXiArcTight_H` and the receipt is the
     plain `h`-door (the anti-drift instance); at `Xi := bigXiAffD a b h` it is
     `nearRatTight_of_bigXiAffD` (§2) at cap `(a·h)·arcDen`, so the road runs at PARAMETER
     `k := a·h` — the freeze §2 number's own parameter.
  Δ2 THE MULTIPLIER IS THREADED, NOT RIDDEN.  The price brief (M-R2) proposed absorbing a factor
     `a` on `x` through the outer-scale rider at `a·g`.  That is FALSE for the `hPHheadroom` floor:
     the rider is quantified over the gate `XCeilGate`, whose only ceiling on `ω` is
     `log ω + ε²·H₊ ≤ 31/ε·H₊`, and `8·(4^⌊ε²H₊⌋)²·ω` has `log ≥ 2.77·ε²H₊ + log ω` — over the
     rider's budget by `1.77·ε²·H₊` at the gate's largest `ω`, for EVERY `a ≥ 1`.  So the factor
     enters at the BUILDER (`chowlaRegimeFlat_exists_param_gen_ceiling_mul`: `x := a·x₀`, the
     floors at `x₀` are the builder's own, the ceiling `log(a·x₀) ≤ 31/ε·H₊` re-derived from
     `regime_outer_param_ceiling`'s tighter form with `log a ≤ 7` absorbed) and is carried INERT
     through every hop as `a ∣ R.x ∧ StrideScale a R` (no hop reads `R.x` except through the
     regime's fields and the ceiling; H5 substitutes `g' = s15ArmH + g` and proves the rider at
     `a·g'`, the extra `log a ≤ 7` paid by the numeral twin `xceil_arm_split_mul_h` — v2, refuter
     verdict A1: the landed `xceil_arm_split_h` is an EQUALITY-tight budget line with no residual
     slack, so the `+ 7` needs its own class-A numeral, not "the same margin").
  Δ3 THE FLOOR IS EXPOSED TO THE END.  H5 already carries `R.Hlo = U1floor` for any `U1floor ≥
     max Hcap (arcFloor36, loglogFloor50)`; H6 instantiates `U1floor := flatWitFloor` and H7 pins
     `flatDesignBase A`.  Here H6/H7 keep `∀ U1floor ≥ flatWitFloor` with ONE caller hypothesis,
     `loglog U1floor ≤ 3.2·A + log 2` — the single place the chain reads `Hlo` from ABOVE
     (`hbaseceil` → `flat_L_width_priced`, S16FlatTerminalLinear:1570); every other read is a
     floor and is monotone.  The caller discharges it at `U1floor := a·flatDesignBase A` by
     `loglog_mul_flatDesignBase_le` (StridePair, F3-P19).
  Δ4 THE DOOR IS HANDED OUT.  The forms end in `P R`; the door-head `flat_door_head_xceil_h`
     hands `⟨ρ, 0 < ρ, ρ ≤ 1/(837782·h²), door⟩` out at the head's own `δ₀ = cD3/(16C)·ε/4` with
     the leaves PINNED (`cD3 = 1/4`, `C = h·(1 + 4·log 4)`, `ε = 1/(500h)`), exactly as
     `DoorReceipt.flat_door_head_xceil` does at `h = 1` (refuter R6: a grade bounded only from
     below is not a grade).

THE CROWN (§7): `mrtUniformityXiL2AffW_holds_flat_stride` — for every `(a, b, h)` with `b < a`,
`0 < h`, `log(a·h) ≤ 7`, and every `A₀`, an affine regime `Ra` with `Ra.a = a`, `Ra.b = b`,
`flatDesignBase A ≤ Ra.Hlo`, carrying the affine `L²` door AT TAO'S RANGE at grade
**`≤ 1.02·a·ρ + E`** with `ρ ≤ 1/(837782·(a·h)²)` and `E` a named nonnegative endpoint bounded
against `2^539` — the freeze §2 supply line `1.02·a·δ₀(a·h)`, stated at the regime it lives at.
The statement spells the grade `a·Zr·ρ + E` with `Zr` a SLACK BINDER (`1 ≤ Zr ≤ 1.02`; the
executor takes `Zr := 1.02`), NOT the normaliser ratio `Z/Z'` — that ratio is bounded above by
`1.02` (F3-P17) but is NOT `≥ 1` in general (v2, refuter verdict A7: `Z(10,3)/Z(5,3) = 0.854`);
the door lands at the binder's grade from the transport's literal grade by
`mrtUniformityXiL2AffW_mono` (F3-P10a).  UNCONDITIONAL once landed.

HONEST LABEL.  The door's grade is the road's at parameter `a·h` times `1.02·a`; the affine DEMAND
(`δ₀_aff = δ₀(a·h)`, freeze §2) is NOT met here — that miss (`214` at `(210, 2)`) is F5's numeral
re-cut.  Nothing here bears on twin primes.  Statement-only at the freeze; NO executor fires
before the helm's refuter verdict.  ⛔ MERGE FENCE (iron rule 2) as in `StridePair.lean`.

Degenerate values: `a = 0` is excluded by `1 ≤ a` at every form; `h = 0` by `0 < h`; at
`a = 1`, `Xi := bigXiH h` the forms are the landed hops' statements with the conclusion slot
(the anti-drift instance `mrtUniformityXiL2H_holds_flat`, §5); `K = 0` makes the count
hypotheses trivial and the door's grade `2·Binsert` — consistent.
-/
import Salt.Entropy.Chowla.StridePair
import Salt.MR.DoorReceipt
import Salt.MR.S16ComposeLH
import Salt.MR.V7RatedH
import Salt.MR.HDoorArc
import Mathlib

-- The head reaches `flatCapH_shuffle` (the `h` head's own cap shuffle) by `open private`, the
-- corpus's sanctioned device (`DoorReceipt.lean:64` does the same for `uniformCap_shuffle`).
open private flatCapH_shuffle from Salt.Entropy.Chowla.HloExportFlatH
-- v2 (refuter R1): two "body verbatim" replays call `private` lemmas of their source modules —
-- the multiplier builder (F3-Q2) copies `chowlaRegimeFlat_exists_param_gen_ceiling`'s body,
-- which invokes `xceil_flat_P` / `xceil_flat_step` (XCeil.lean:144, :135), and the road-exit
-- replay (F3-Q8) copies S16ComposeLH.lean:1869-1891, whose cap line is `flatRootCapH_arc_k`
-- (S16ComposeLH.lean:1063).  Opened here so the copies elaborate; nothing landed moves.
open private xceil_flat_P xceil_flat_step from Salt.MR.XCeil
open private flatRootCapH_arc_k from Salt.MR.S16ComposeLH

noncomputable section

open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla

set_option exponentiation.threshold 4000

namespace Salt.MR

/-- **F3-Q0 (abbrev).**  A frequency-set family: one finite set of frequencies on the `1/H` grid
per `(ε, H)`.  The landed instances are `fun eps H _ => bigXiH h eps H` and
`fun eps H _ => bigXiAffD a b h eps H`. -/
abbrev XiFamily := ∀ (_eps : ℚ) (H : ℕ) [NeZero H], Finset (ZMod H)

/-! ## §1 — the multiplier: a factor `a` on the outer scale, carried by the BUILDER -/

/-- **F3-Q1 (class A) — the rider at a multiple.**  `XCeilRiderStrict ε g → XCeilRider ε (a·g)` at
`a ≤ 1096` and `1/548000 ≤ ε`: on the gate `50 ≤ loglog H₊`, so `H₊ ≥ exp(exp 50)` and
`ε²·H₊ ≥ exp(exp 50)/548000² ≥ 7 ≥ log a` (`log_le_log` on `a ≤ 1096`, `Real.log 1096 < 7`
by `Real.exp_one_gt_d9`… or `h_le_1096_of_log_le_seven`'s converse numeral); `Real.log_mul`
(cases `g Hhi ω = 0`: `Real.log_zero`, `log a ≤ 7 ≤ ε²H₊`).  The corpus's `exp(exp 50)` floor:
`regime_Hfloor_of_loglogFloor50`-style numerals (S12Compose:195) or `Real.add_one_le_exp` twice
after `exp 50 ≥ 2^72` (`Real.exp_one_gt_d9`, `Real.exp_nat_mul`).  Used by the crown's caller
at `g := 0` (trivial) and by the H5 replay at `g' := s15ArmH + g` (§4). -/
theorem xceilRider_mul_of_strict {ε : ℚ} (heps : 1 / 548000 ≤ ε) {a : ℕ} (ha1096 : a ≤ 1096)
    {g : ℕ → ℕ → ℕ} (hg : XCeilRiderStrict ε g) :
    XCeilRider ε (fun Hhi ω => a * g Hhi ω) := by
  sorry

/-- **F3-Q2 (class B) — THE MULTIPLIER BUILDER.**  `chowlaRegimeFlat_exists_param_gen_ceiling`
(XCeil.lean:386) with `x := a * x₀`: the same construction (`regime_outer_param_ceiling` at
`(ε, H₊, P := 4^⌊ε²H₊⌋)`, XCeil.lean:185, gives `(x₀, ω)` with the eight floors and the ceiling
`log x₀ ≤ (30/ε)·log H₊ + 2·log(P+1)`), the regime record at `x := a * x₀` (each `x`-field at
`a·x₀ ≥ x₀` by `Nat.le_mul_of_pos_left`/monotonicity, exactly `regimeFlatEnlargeX`'s six lines),
`StrideScale a R` from `Nat.mul_div_cancel_left x₀ ha` (`R.x / a = x₀`) and the floors at `x₀`
VERBATIM, and the ceiling `log(a·x₀) ≤ log a + (30/ε)·log H₊ + 2·log(P+1) ≤ 31/ε·H₊`: the landed
collapse (XCeil.lean:~440-470: `2·log(P+1) ≤ 1.39 + 0.694·H₊` at `ε ≤ 1/2`, `(30/ε)·log H₊ ≤
(30/ε)·H₊/…`) with `+ 7` absorbed by the margin `(31/ε − 0.694)·H₊ − (30/ε)·log H₊ ≥ 61·H₊ −
(30/ε)·log H₊ ≥ 2.4·10⁸` at `H₊ ≥ 4·10⁶`, `1/ε ≥ 2` — the executor copies the ~90-line body and
edits the record's `x` and the last `linarith`.  The body calls `xceil_flat_P` and
`xceil_flat_step`, `private` to `XCeil.lean` and opened at this file's head (v2, refuter R1);
the `+ 7` enters at `xceil_flat_step`'s use, whose margin `(u − 0.694)·H₊ − 1.39 ≥ 5.2·10⁶`
grows in both `H₊` and `u = 1/ε`.  The flat fields (`A`, `hflat`, `Jf`, `hfitF`, `hJconF`) are
untouched.  `log a ≤ 7` in the form `a ≤ 1096`. -/
theorem chowlaRegimeFlat_exists_param_gen_ceiling_mul (a : ℕ) (ha : 1 ≤ a) (ha1096 : a ≤ 1096)
    (A : ℝ) (hA : 26 ≤ A) (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      StrideScale a R.toChowlaRegime ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
  sorry

/-- **F3-Q3 (class B) — the head-shaped multiplier builder.**
`chowlaRegimeFlat_exists_param_head_xceil`
(XThread.lean:~95) off F3-Q2: push the scale to `a * max (R.x / a) (g R.Hhi R.ω)` by
`regimeFlatEnlargeX` (legal: `a * max (x/a) g ≥ a * (x/a) = x` by `Nat.mul_div_cancel'` from
`a ∣ x`); then `a * g ≤ a * max _ _` (`Nat.mul_le_mul_left`, `le_max_right`); `StrideScale a`
at the new scale: `a ∣ a * m` and `(a * m) / a = m ≥ x/a` (`Nat.mul_div_cancel_left`), each floor
monotone in the scale (`le_trans` with F3-Q2's conjunct; `Nat.div_le_div_right` for the two
`/ ω` corners, `Nat.cast_le` for the real ones); the ceiling on `max`: `log(a * max m g) = max
(log(a*m)) (log(a*g))` via `Nat.mul_max_mul_left`… or `le_max_iff` + `Real.log_le_log`; the
`a*g` arm is the rider `hg` on the gate `XCeilGate eps R.Hhi R.ω`, discharged from the regime's
own fields exactly as XThread does (`hHhi4`, `hll50` off `hflat` at `A ≥ 26`, `hωgate` off
`hPHheadroom` against the ceiling — with the ceiling now on `x = a·x₀` the same `log 8 + 2 log P
+ log ω ≤ log x` argument runs, and `x ≥ x₀ ≥ 8P²ω` still); the `a*x₀` arm is F3-Q2's ceiling. -/
theorem chowlaRegimeFlat_exists_param_head_xceil_mul (a : ℕ) (ha : 1 ≤ a) (ha1096 : a ≤ 1096)
    (A : ℝ) (hA : 26 ≤ A) (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ)
    (g : ℕ → ℕ → ℕ) (hg : XCeilRider eps (fun Hhi ω => a * g Hhi ω)) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      a * g R.Hhi R.ω ≤ R.x ∧ StrideScale a R.toChowlaRegime ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
  sorry

/-! ## §2 — the affine arc bridge (M2's first object, at cap `(a·h)·arcDen`) -/

/-- **F3-Q4 (class B/C) — THE AFFINE ARC BRIDGE.**  Every affine frequency is `NearRatTight` at
cap `(a·h)·arcDen B₅ H`, on the grid `a ∣ H`.  The twin of `nearRatTight_of_bigXiArcTight_H`
(HDoorArc.lean:139): `ξ ∈ bigXiAff` gives `η < a` with `ζ := affOffset a b h H η + h·ξ ∈ bigXi`
(`mem_bigXiAff_iff`), so `NearRatTight (arcDen B₅ H) H (−ζ.val/H)` by the base bridge
(`nearRatTight_of_bigXiArcTight harc heps`, at its own `H₀`); `ζ.val ≡ c + h·ξ.val (mod H)` with
`c = affOffset … .val` and, on the grid, `c·a ≡ (b+h)·η·H (mod H·a)` (`affOffset_spec`, F1-X4), i.e.
`c/H = (b+h)η/a − (an integer)` — a rational with denominator `a`; so `−h·ξ.val/H` is within
`arcDen/(qH)` of `p/q + r/a + m`, a rational with denominator `≤ a·q ≤ a·arcDen`; then N2's
division by `h` (`HDoorArc.lean:139`'s own script: the shift `k = (h·ξ.val)/H` stripped by
`Nat.div_add_mod`, THE CAST SEAM ADDITIVE, never subtractive) puts `−ξ.val/H` within
`(a·h)·arcDen/(q'·H)` of a rational with denominator `q' ≤ a·h·arcDen`.  ⛔ The B/C half is the
denominator bookkeeping through `NearRatTight`'s tight radius `Q/(q·H)` (BigXiArc:566): the witness
denominator after the two scalings is `q·a·h`, and the radius must be shown `≤ (ahQ)/((qah)·H)
= Q/(qH)` — EQUAL, so the tight form survives both scalings with no loss; the executor writes it
as one `refine ⟨_, q * a * h, _, _, _⟩` with `abs_sub_le` chains.  M2's measurement: the claim
is that Tao's `(b+h)η/a` offset (textdump:1296-1300, :1360) costs exactly the factor `a` in the
cap, nothing in the radius. -/
theorem nearRatTight_of_bigXiAffArcTight {B₅ : ℝ} (harc : BigXiArcTight B₅)
    {eps : ℚ} (heps : 0 < eps) {a b h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → a ∣ H → ∀ ξ ∈ bigXiAff a b h eps H,
      NearRatTight (((a * h : ℕ) : ℝ) * arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)) := by
  sorry

/-- **F3-Q4a (class A).**  The bridge at the grid-restricted family, for EVERY `H`: on the grid
`bigXiAffD_of_dvd` rewrites to F3-Q4; off it the set is `∅` (`bigXiAffD`'s `if_neg`) and the
statement is vacuous (`Finset.not_mem_empty`).  This is the `harc` the road replay consumes. -/
theorem nearRatTight_of_bigXiAffD {B₅ : ℝ} (harc : BigXiArcTight B₅)
    {eps : ℚ} (heps : 0 < eps) {a b h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXiAffD a b h eps H,
      NearRatTight (((a * h : ℕ) : ℝ) * arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)) := by
  sorry

/-! ## §3 — the road at a generic set family (Δ1) -/

/-- **F3-Q5 (class B) — N4c at a generic set.**  `sum_bigXiH_norm_windowExpSum_sq_le_parseval`
(HDoorArc.lean:328) with `bigXiH h R.eps H` replaced by `Xi R.eps H` and the cap `(h : ℝ) * arcDen
B₅ H` by an arbitrary `Q H`: the proof (`sum_bigXiH_norm_windowExpSum_sq_le_sub` ← N4a,
HDoorArc.lean:211-293) reads the set ONLY through `harc`, `hXi`, `hins` and is copied with the
set renamed — no `mem_bigXiH_iff` is used anywhere in it.  `hins` in the parseval spelling
(`(1/H²) * ∑ ‖λ-sum − a-sum‖²`), the spelling lemma `sum_bigXi_insert_spelling_eq`
(M4DoorL2.lean:545) being set-generic in its proof (`absWindowSum_add_coeff` + `Finset.mul_sum`)
— the executor states its `Xi` twin inline as a `have`. -/
theorem sum_Xi_norm_windowExpSum_sq_le_parseval (Xi : XiFamily) (Q : ℕ → ℝ) (R : ChowlaRegime)
    (a : ℕ → ℂ) (Bsieve : ℕ → ℝ) (K Binsert : ℝ) {H₀ : ℕ}
    (hfloor : H₀ ≤ R.Hlo)
    (harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ Xi R.eps H,
      NearRatTight (Q H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (hB0 : ∀ H : ℕ, 0 ≤ Bsieve H)
    (hsock : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (Q H) H α →
        (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
          ≤ Bsieve H * (H : ℝ) ^ 2)
    (hXi : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      ((Xi R.eps H).card : ℝ) ≤ K)
    (hins : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ Xi R.eps H,
        ∫ n, ‖absWindowSum lamCoeff H n (-(ξ.val : ℝ) / (H : ℝ))
            - absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω) ≤ Binsert) :
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (∑ ξ ∈ Xi R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
        ≤ K * (2 * Bsieve H) + 2 * Binsert := by
  sorry

/-- **F3-Q6 (class B) — the door-L2 supply at a generic set.**  `m4_doorL2_supply_H_L_gk_khoist`
(S16ComposeLH.lean:1072) with the set `Xi` and the arc bridge `harcXi` a HYPOTHESIS (at the
landed set it is `nearRatTight_of_bigXiArcTight_H bigXiArcTight_twelve`, the one line the landed
body spends on the set).  Body verbatim otherwise: `parseval_insert_budget_door_bounded`, the
`H₀` from `harcXi eps heps`, `harc` transported to the regime's `ε` by `rw [hReps]`, the four
scale lines, `hins` via `hpars … (Xi R.eps H)` (parseval is set-generic), then F3-Q5 in place of
N4c and the budget line `l2_budget_line`.  The socket stays `M4SievedDoorSqH_L_gk h` — the cap
`(h : ℝ) * arcDen 12 H` is the road's PARAMETER, and the affine instance runs at `h := a·h`. -/
theorem m4_doorL2_supply_Set_gk_khoist (h : ℕ) (hh : 0 < h) (Xi : XiFamily)
    (harcXi : ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
      ∀ ξ ∈ Xi eps H, NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ))) :
    ∃ Cg : ℝ, 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      ∀ (eps : ℚ), 0 < eps → ∃ H₀ : ℕ,
        ∀ (K : ℕ) (R : ChowlaRegime), R.eps = eps → H₀ ≤ R.Hlo →
          ∀ (Braw : ℕ → ℝ) (Kc Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSqH_L_gk h K R M Braw →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((Xi R.eps H).card : ℝ) ≤ Kc) →
            0 ≤ Kc →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
              MRTUniformityXiL2Set Xi R (2 * Kc * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ)) := by
  sorry

/-- **F3-Q7 (class B) — the road at a generic set.**  `m4_second_road_L2_H_gk_flatRoot_L_khoist`
(S16ComposeLH.lean:1138) with F3-Q6 in place of its first `obtain` (`m4_doorL2_supply_H_L_gk_khoist
h hh`); body verbatim (the block-mean cover, the sieved-door socket from `blk2H`, the five cap
reads are all set-free — the set enters only at the last `refine hH₀ …`). -/
theorem m4_second_road_L2_Set_gk_flatRoot_L_khoist (h : ℕ) (hh : 0 < h) (Xi : XiFamily)
    (harcXi : ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
      ∀ ξ ∈ Xi eps H, NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ))) :
    ∃ Cg : ℝ, 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      ∀ (eps : ℚ), 0 < eps → ∃ H₀ : ℕ,
        ∀ (K : ℕ) (R : ChowlaRegime), R.eps = eps → H₀ ≤ R.Hlo →
          ∀ (δ Bceil Kc : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
            M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ((h : ℝ) * arcDen 12 H) ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * ((h : ℝ) * arcDen 12 H) ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              (h : ℝ) * arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((Xi R.eps H).card : ℝ) ≤ Kc) →
            0 ≤ Kc →
            M4ChiSummedFreeRowH_L_gk h K R M RS →
              MRTUniformityXiL2Set Xi R (2 * Kc * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ)) := by
  sorry

/-! ## §4 — THE FORMS: each `h`-lane hop's statement, once, with the conclusion slot `P R`, the
set `Xi`, the multiplier `a` (Δ2) and — at H6/H7 — the exposed floor (Δ3).  Each form is the
landed statement (cited) with EXACTLY the edits Δ1–Δ4 name; a refuter diffs them against the
citations. -/

/-- **⟦H0 FORM⟧** `flat_head_uniform_xceil_h`'s statement (S16ComposeLH.lean:1670) with: the count
at `Xi`; the door slot `MRTUniformityXiL2Set Xi R ρ`; the scale slot `a * g R.Hhi R.ω ≤ R.x ∧
StrideScale a R` under `1 ≤ a → a ≤ 1096 → XCeilRider ε (a·g)`; the conclusion `P R`. -/
def FlatHeadFormH (h : ℕ) (Xi : XiFamily) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (ε : ℚ) (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 539 ∧ 0 < δ₀ ∧
      1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 26 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap = max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (a extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → a ≤ 1096 →
            XCeilRider ε (fun Hhi ω => a * g Hhi ω) → ∃ R : ChowlaRegime,
            R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ a * g R.Hhi R.ω ≤ R.x ∧
            StrideScale a R ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((Xi R.eps H).card : ℝ) ≤ K) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            R.Hlo ≤ max Hcap (max extraFloor U1floor) ∧
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2Set Xi R ρ →
              P R

/-- **⟦H1 FORM⟧** `m4_second_road_L2_H_gk_flatRoot_L_exit_uniform_xceil_khoist`'s statement
(S16ComposeLH.lean:1833) with the scale slot and `P R`.  (`extraFloor` is instantiated at `H₀`
inside the replay, as landed; the set does not appear in this statement — it was spent at the
door-L2 supply.) -/
def FlatRoadExitFormH (h : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 539 ∧ 0 < δ₀ ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧
      1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (a U1floor : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → a ≤ 1096 →
            XCeilRider ε (fun Hhi ω => a * g Hhi ω) →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ a * g R.Hhi R.ω ≤ R.x ∧
              StrideScale a R ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
                M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
                (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
                (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ((h : ℝ) * arcDen 12 H) ^ 7 ≤ RStr H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  44 * RSan H + 87 * ((h : ℝ) * arcDen 12 H) ≤ (4 / 3 : ℝ) ^ j₀) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  128 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  (h : ℝ) * arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
                      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                    ≤ Braw H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                M4ChiSummedFreeRowH_L_gk h K R M RS →
                  P R

/-- **⟦H2 FORM⟧** `flat_capstone_uniform_win_xceil_kwide_khoist_h`'s statement
(S16ComposeLH.lean:1892) with the scale slot and `P R`; `Awin` and `hband` are the form's
parameters as in `DoorReceipt.FlatCapstoneForm`. -/
def FlatCapstoneFormH (h : ℕ) (Awin : ℝ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (a U1floor : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → a ≤ 1096 →
            XCeilRider ε (fun Hhi ω => a * g Hhi ω) →
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ a * g R.Hhi R.ω ≤ R.x ∧
              StrideScale a R ∧
                Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (M : ℕ), Mfl ≤ M → K ≤ 170000000 * M →
                  ∃ C' : ℝ, 0 < C' ∧
                    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                        ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                    ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                      -- ⟦A⟧ THE SPINE ARITHMETIC
                      M4DoorGates_L_gk K Cg R M k δ₀ →
                      8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        4 * Real.log (263 * (h : ℝ) * max 1 (arcDen 12 H))
                          ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        (h : ℝ) * arcDen 12 H
                          < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRhoH (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) h H)
                          (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                          (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                          5 ≤ Real.log (Real.log (2 * T)) →
                          (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                            ≤ 8 * (0 : ℝ) ^ 2
                              + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                    \ seamBall (((A + s : ℕ)) : ℝ) 0)
                                  ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                      (calP (AdoorL M) (s13GK K M))
                                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                      (mrAlpha (1 / 12)) 2,
                                  ‖spoly (2 * (A + s))
                                    (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                              + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                                  * (Real.log (((A + s : ℕ)) : ℝ))
                                      ^ (-theta293 + epsrf (A + s)))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        P R

/-- **⟦H3 FORM⟧** `flat_conditional_uniform_win_xceil_kwide_khoist_h`'s statement
(S16ComposeLH.lean:2143) with the scale slot under the STRICT rider and `P R`. -/
def FlatConditionalFormH (h : ℕ) (Awin : ℝ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (ε : ℚ) (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (a U1floor : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → a ≤ 1096 → XCeilRiderStrict ε g →
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ a * g R.Hhi R.ω ≤ R.x ∧
              StrideScale a R ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ M : ℕ, K ≤ 170000000 * M →
                S15Sel''_L_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                S15CrossingBound_LH_gk h K R M → P R

/-- **⟦H4 FORM⟧** `logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin_h`'s
statement (S16ComposeLH.lean:3338) with Δ3 — `∀ U1floor ≥ flatWitFloor ε β A Hopq` under the ONE
ceiling `loglog U1floor ≤ 3.2·A + log 2`, `R.Hlo = U1floor` — the scale slot, and `P R`.  The
`T₀` arm stays stated at `flatWitFloor` (the replay lifts it to `U1floor` by monotonicity of
`√` and `exp`). -/
def FlatKswinFormH (h : ℕ) (Awin : ℝ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (ε : ℚ) (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧
        ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
          K ≤ 170000000 * flatDoorM A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          T₀ ≤ Real.exp (Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ) / 2) →
          Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 →
          ∀ (U1floor : ℕ), flatWitFloor ε β A Hopq ≤ U1floor →
            Real.log (Real.log ((U1floor : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 →
          ∀ (a : ℕ) (g : ℕ → ℕ → ℕ), 1 ≤ a → a ≤ 1096 → XCeilRiderStrict ε g →
            ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = U1floor ∧ a * g R.Hhi R.ω ≤ R.x ∧ StrideScale a R ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            (S16CofactorSupply_LH_gk h K Cq R (flatDoorM A) →
              S16BaseScaleCap96_LH_gk h K R (flatDoorM A) →
                P R))

/-- **⟦H5 FORM⟧** `logChowla2_v7_rated_h`'s statement (V7RatedH.lean:1063) with Δ3 — `∀ U1floor ≥
flatDesignBase A` under `loglog U1floor ≤ 3.2·A + log 2`, `R.Hlo = U1floor` in place of `R.Hlo =
flatDesignBase A` — the scale slot, and `P R`.  At `U1floor := flatDesignBase A`, `a := 1`,
`g := 0`, `P := (¬ logChowlaFails h · · ·)` this is the landed headline's statement. -/
def V7RatedFormH (h : ℕ) (P : ChowlaRegime → Prop) (A₀ : ℝ) : Prop :=
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧ Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧
      1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Mfl ≤ flatDoorM A ∧ 0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∀ (U1floor a : ℕ) (g : ℕ → ℕ → ℕ), flatDesignBase A ≤ U1floor →
        Real.log (Real.log ((U1floor : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 →
        1 ≤ a → a ≤ 1096 → XCeilRiderStrict ε g →
      ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = U1floor ∧ a * g R.Hhi R.ω ≤ R.x ∧ StrideScale a R ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        P R

/-! ## §5 — THE REPLAYS, generic in `P` (and in `Xi` where the set is still visible) -/

/-- **⟦H0→H1 REPLAY⟧ (class B).**  The road exit (S16ComposeLH.lean:1869-1891) from a generic head:
the landed body with `flat_head_uniform_xceil_h h hh hh7` replaced by the hypothesis `hhead` and
`m4_second_road_L2_H_gk_flatRoot_L_khoist h hh` by F3-Q7 at `Xi` with `harcXi`; the `a`-binders
are introduced beside `U1floor g hg` and forwarded (`hhd H₀ a U1floor g ha ha1096 hg`); the
new conjunct `StrideScale a R` is forwarded verbatim; the cap line `flatRootCapH_arc_k` is
`private` to `S16ComposeLH.lean` and opened at this file's head (v2, refuter R1); the last line
`hR δ₀ hδ₀ le_rfl (mrtUniformityXiL2Set_mono …)` — `mrtUniformityXiL2H_mono`'s set-generic twin,
a one-line `intro H _ hlo hhi; exact le_trans (hdoor H hlo hhi) hbudget` the executor states
inline. -/
theorem flat_roadExit_generic_h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    (Xi : XiFamily)
    (harcXi : ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
      ∀ ξ ∈ Xi eps H, NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (P : ChowlaRegime → Prop) (hhead : FlatHeadFormH h Xi P) :
    FlatRoadExitFormH h P := by
  sorry

/-- **⟦H1→H2 REPLAY⟧ (class B).**  The capstone (S16ComposeLH.lean:2060-2142) from a generic road
exit: body verbatim (the capstone forwards the road's regime and the caller's `g` untouched, so
it forwards the multiplier and `StrideScale` untouched too); `hroadU` is the hypothesis. -/
theorem flat_capstone_generic_h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) (Awin : ℝ)
    (hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hroad : FlatRoadExitFormH h P) :
    FlatCapstoneFormH h Awin P := by
  sorry

/-- **⟦A1 — THE `+ 7` NUMERAL TWIN⟧ (class A, v2).**  `xceil_arm_split_h` (XThread.lean:1153)
with `+ 7` on the left: `log 2 + log h + 7 ≤ H₊/(250000·h²) − H₊/10²⁰`.  The landed lemma is an
EQUALITY-tight budget line (the conditional's `hg'` block closes at ZERO slack on `31/ε·H₊`), so
the H2→H3 replay's extra `log a ≤ 7` cannot ride it — refuter verdict A1.  Same body as the
landed proof (`h ≤ 1096` from `h_le_1096_of_log_le_seven`, `H₊ ≥ 36·10²⁰` from `loglog H₊ ≥ 50`
through `xt_exp25`, the `h²` widening `hr1`, then `linarith` against `14.694` instead of
`7.694`); slack `1.2·10¹⁰` from `hHbig` at `h = 1096`. -/
theorem xceil_arm_split_mul_h {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {Hhi : ℕ}
    (hH4 : 4000000 ≤ Hhi) (hll : 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log 2 + Real.log (h : ℝ) + 7
      ≤ ((Hhi : ℕ) : ℝ) / (250000 * (h : ℝ) ^ 2) - ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
  sorry

/-- **⟦H2→H3 REPLAY⟧ (class B).**  The conditional (S16ComposeLH.lean:2170-2325) from a generic
capstone — the one hop that MOVES `g` (`g' := s15ArmH h δ₀ ρ + g`) and now proves the rider at
`a·g'`: the landed `hg'` block (S16ComposeLH.lean:2198-2240) with the budget `B := 31/ε·H₊ −
log 2 − 7` in place of `31/ε·H₊ − log 2` — `harm' : log arm ≤ B` from `harm`, the gate's
`hωw : log ω + ε²H₊ ≤ 31/ε·H₊`, `hεsq` and `xceil_arm_split_mul_h hh hh7 hH4 hll` (v2, A1: the
`+ 7` numeral twin above, in place of `xceil_arm_split_h`); `hgb' : log g ≤ B` from the STRICT
rider `hg` (its `ε²H₊` margin against the same numeral); `xt_log_add_le harm' hgb'` gives
`log(arm + g) ≤ 31/ε·H₊ − 7`; then `Real.log (a * (arm + g)) = log a + log(arm + g)`
(`Real.log_mul`, `a ≥ 1`, `arm + g ≥ 1` — `s15ArmH` is `≥ 1`; else the `= 0` case) and
`log a ≤ log 1096 < 7` (`Real.log_le_log`, `Real.log 1096 < 7` by `Real.exp_one_gt_d9`… or the
converse of `h_le_1096_of_log_le_seven`) close `≤ 31/ε·H₊`.  Then `hmain 0 le_rfl a U1floor g'
ha ha1096 hg'`, `hRarm`/`hRgg` by `omega` from `a * (arm + g) ≤ R.x` (`Nat.mul_add`, `a ≥ 1`),
`StrideScale` forwarded, the rest verbatim. -/
theorem flat_conditional_generic_h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    (Awin : ℝ) (hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hcap : FlatCapstoneFormH h Awin P) :
    FlatConditionalFormH h Awin P := by
  sorry

/-- **⟦H3→H4 REPLAY⟧ (class B).**  The kswin terminal (S16ComposeLH.lean:3370-3420 region; the
`h = 1` generic twin is `DoorReceipt.flat_kswin_generic`, :775) from a generic conditional, with
Δ3: `intro U1floor hU hUceil a g ha ha1096 hg` in place of `intro g hg`; `hbody U1floor g hg
(le_trans (flatCap_le_flatWitFloor hCapLe) hU)` in place of `hbody (flatWitFloor …) g hg
(flatCap_le_flatWitFloor hCapLe)`; `hdes` from `flatWitFloor_design` and `hU` by `Real.log_le_log`
twice (monotone); `hbaseceil := hUceil` (the caller's ceiling — the landed `rw [hHlo,
flat_witFloor_eq_designBase …]; exact flatDesignBase_loglog_le` is REPLACED, the only body line
that read `Hlo` from above); `hfl`, `hlo`, `hKswR`, `hT₀` (`by rw [hHlo]; exact le_trans hT₀
(exp_le_exp.mpr (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (Nat.cast_le.mpr hU)) …))`) by
monotonicity from `hU`; the rest verbatim. -/
theorem flat_kswin_generic_h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) (Awin : ℝ)
    (hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hcond : FlatConditionalFormH h Awin P) :
    FlatKswinFormH h Awin P := by
  sorry

/-- **⟦H4→H5 REPLAY⟧ (class B).**  The rated terminal (V7RatedH.lean:1090-1200) from a generic
kswin, with Δ3: after the eight-arm design constant, `intro U1floor a g hU hUceil ha ha1096 hg`
and `hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKswin U1floor (by rw [hbase hopq];
exact hU) hUceil a g ha ha1096 hg` in place of the landed `g ≡ 0` exhibit (`xceilRiderStrict_zero`
is no longer needed here; the CROWN's caller supplies `g := 0`); `hfl`, `hlo`, `hthrgate`,
`hKvtcush` (`cofkR_cushion_of_armVt R hKvt0 harmA hlo`) by monotonicity from `hU`; the
base-scale cap `s16_baseScaleCap96_LH_at_klevF … hxceil hwin` unchanged; the terminal `hfireR :
P R` where the parent has `¬ logChowlaFails`. -/
theorem flat_v7_generic_h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    (P : ChowlaRegime → Prop)
    (hk : ∀ Awin : ℝ, S16BandLaneCBoundedLH_winU h Awin → FlatKswinFormH h Awin P) (A₀ : ℝ) :
    V7RatedFormH h P A₀ := by
  sorry

/-! ## §6 — the door-head, the chain, the receipts -/

/-- **⟦THE RECEIPT PREDICATE AT `h` — THE P-SLOT, WIDENED (v2)⟧** the `L²` door over `Xi` at
the closed numeral `1/(837782·h²)` — `DoorReceipt.MRTDoorReceipt` (DoorReceipt.lean:84) with the
set family and the `h²` — carrying TWO facts the head holds and the chain does not forward:
(i) the head's ε-PIN as an EQUALITY, `R.eps = 1/(500·h)` (refuter verdict A4: the six forms and
the receipts export only the LOWER pin `1/(500h) ≤ ε`, while `regimeShrinkX_stride` and the
transport need `ε ≤ 1/500`; the regime's own `heps1 : ε ≤ 1/2` gives `2/ε² ≥ 8`, which fails
`hcoprime` at `a = 210`); (ii) the COUNT, `∃ K ≤ 2^539, ∀ H ∈ [Hlo, Hhi], |Xi R.eps H| ≤ K`
(refuter verdict A2/A6: the head form exports it, the road exit SPENDS it, no later form
re-exports it, and the crown's `hK` has no source).  Both ride the P-slot because `P` is
OPAQUE to the six forms and the five replays (Q8–Q12 are generic in `P`): the door-head
(F3-Q14) discharges both at the head, where `R.eps = ε`, `ε = 1/(500h)` (`hεdef`) and the count
conjunct are all in hand — ZERO forms or replays move.  The alternative (thread the equality and
the count through the six forms as conjuncts) was an 11-site edit across landed-text-derived
statements; refused. -/
def MRTDoorReceiptSet (h : ℕ) (Xi : XiFamily) (R : ChowlaRegime) : Prop :=
  R.eps = 1 / (500 * (h : ℚ)) ∧
  (∃ K : ℝ, 0 < K ∧ K ≤ 2 ^ 539 ∧ ∀ (H : ℕ) [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
    ((Xi R.eps H).card : ℝ) ≤ K) ∧
  ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / (837782 * (h : ℝ) ^ 2) ∧ MRTUniformityXiL2Set Xi R ρ

/-- **⟦THE DOOR-HEAD AT `h`, AT A GENERIC SET⟧ (class B).**  `DoorReceipt.flat_door_head_xceil`
(DoorReceipt.lean:1001) ported to the `h` head (`flat_head_uniform_xceil_h`, S16ComposeLH.lean:
1670-1830): the leaves PINNED — `cD3 := 1/4`, `C := h·(1 + 2·(2·log 4))`, `ε := 1/(500·h)` —
so `δ₀ := cD3/(16·C)·ε/4 = 1/(128000·h²·(1 + 8·log 2))` closes BOTH `1/(838400·h²) ≤ δ₀`
(`hδ₀ge`, the landed script at `h`) and `δ₀ ≤ 1/(837782·h²)` (`hδ₀le`, `C > 6.5451718·h` by
`Real.log_two_gt_d9`); the count hook is the HYPOTHESIS `hcount` (at `Xi := bigXiH h` it is
`bigXiH_bounded_ceiling_of_pin h hh hh7 ε rfl`; at `bigXiAffD a b h` with `h := a·h` it is
`bigXiAff_bounded_ceiling_of_pin` through `bigXiAffD_card_le`); `β := cD3·ε/(144·log 4)`;
`Hopq := H₀xi`; the hoist `intro A hA26 hAge`; the regime from F3-Q3 at `max F (max extraFloor
U1floor)` and the caller's `a`, `g`, `hg`; the cap by `flatCapH_shuffle`; the `P R` slot
(`MRTDoorReceiptSet`, v2) discharged as the triple `⟨hReps ▸ hεdef, ⟨C, hC, hCb, hcountR⟩,
ρ, hρpos, le_trans hρ hδ₀le, hdoor⟩` — the pin from `hεdef : ε = 1/(500h)` and `R.eps = ε`, the
count from the head's own count conjunct (`hcountR : ∀ H ∈ [R.Hlo, R.Hhi], |Xi R.eps H| ≤ C`,
which the head form ALSO exports beside `P R`), the door HANDED OUT.  The `h`-head's tail
(`entropy_decrementFlat`, `spine_False_core_xi_sq_flat_h`) is NOT replayed — the door-head has
no tail. -/
theorem flat_door_head_xceil_h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    (Xi : XiFamily)
    (hcount : ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 539 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((Xi (1 / (500 * (h : ℚ))) H).card : ℝ) ≤ C) :
    FlatHeadFormH h Xi (MRTDoorReceiptSet h Xi) := by
  sorry

/-- **⟦THE CHAIN⟧ (class A).**  H0 ∘ … ∘ H5 at `h`, generic in `P` and `Xi`:
`flat_v7_generic_h h hh hh7 P (fun Awin hband => flat_kswin_generic_h … (flat_conditional_generic_h
… (flat_capstone_generic_h … (flat_roadExit_generic_h h hh hh7 Xi harcXi P hhead)))) A₀`. -/
theorem flat_chain_generic_h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) (Xi : XiFamily)
    (harcXi : ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
      ∀ ξ ∈ Xi eps H, NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (P : ChowlaRegime → Prop) (hhead : FlatHeadFormH h Xi P) (A₀ : ℝ) :
    V7RatedFormH h P A₀ := by
  sorry

/-- **⟦THE RECEIPT AT `h`, GENERIC SET, FLOOR AND SCALE EXPOSED⟧ (class A).**  The chain at
`P := MRTDoorReceiptSet h Xi` fed the door-head, unpacked to the payload the pairing reads:
`obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, …, hεpin, …, hA162, hA₀A,
hbody⟩ := flat_chain_generic_h … (flat_door_head_xceil_h …) A₀`.  v2 (A4/A2): the payload's
`P R` is now the triple `⟨hRpin, ⟨K, hK, hKb, hcountR⟩, ρ, …⟩`; the two new conjuncts are
(i) the top-level ε-PIN EQUALITY `ε = 1/(500h)` — read off `P R` at the TRIVIAL instantiation
`hbody (flatDesignBase A) 1 (fun _ _ => 0) le_rfl (flatDesignBase_loglog_le hA162) le_rfl
(by norm_num) xceilRiderStrict_zero` (the same five arguments F3-Q17 uses): `hReps ▸ hRpin`;
(ii) the count conjunct in the payload, forwarded from `P R` verbatim.  Then `⟨ε, A, hε, hεpin,
hεeq, hA162, hA₀A, fun U1floor a g hU hUceil ha ha1096 hg => …⟩` with the payload re-packed. -/
theorem mrtUniformityXiL2Set_holds_flat_floor (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    (Xi : XiFamily)
    (harcXi : ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
      ∀ ξ ∈ Xi eps H, NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (hcount : ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 539 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((Xi (1 / (500 * (h : ℚ))) H).card : ℝ) ≤ C)
    (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ ε = 1 / (500 * (h : ℚ)) ∧
      162 ≤ A ∧ A₀ ≤ A ∧
      ∀ (U1floor a : ℕ) (g : ℕ → ℕ → ℕ), flatDesignBase A ≤ U1floor →
        Real.log (Real.log ((U1floor : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 →
        1 ≤ a → a ≤ 1096 → XCeilRiderStrict ε g →
      ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = U1floor ∧ a * g R.Hhi R.ω ≤ R.x ∧ StrideScale a R ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        (∃ K : ℝ, 0 < K ∧ K ≤ 2 ^ 539 ∧ ∀ (H : ℕ) [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
          ((Xi R.eps H).card : ℝ) ≤ K) ∧
        ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / (837782 * (h : ℝ) ^ 2) ∧ MRTUniformityXiL2Set Xi R ρ := by
  sorry

/-- **⟦THE ANTI-DRIFT INSTANCE — THE PLAIN `h`-DOOR, NAMED⟧ (class A).**  At `Xi := bigXiH h`,
`a := 1`, `g := 0`, `U1floor := flatDesignBase A`: the `h`-lane's `L²` door on the flat family at
`ρ ≤ 1/(837782·h²)` — the EM bank's "`_h` twin receipt, a later wave" (2026-09-02 §4), landing
here as the conservativity control of the generator.  `harcXi := fun eps heps =>
nearRatTight_of_bigXiArcTight_H bigXiArcTight_twelve heps hh`; `hcount :=
bigXiH_bounded_ceiling_of_pin h hh hh7 _ rfl`; `hUceil := flatDesignBase_loglog_le hA162`;
`xceilRiderStrict_zero`; `strideScale_one`; the door by `mrtUniformityXiL2Set_bigXiH_eq ▸`. -/
theorem mrtUniformityXiL2H_holds_flat (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / (837782 * (h : ℝ) ^ 2) ∧ MRTUniformityXiL2H h R ρ := by
  sorry

/-- **⟦THE AFFINE-SET INSTANCE⟧ (class A).**  At parameter `k := a·h`, `Xi := bigXiAffD a b h`:
`harcXi := fun eps heps => nearRatTight_of_bigXiAffD bigXiArcTight_twelve heps ha hh` (the cap
`((a*h : ℕ) : ℝ) * arcDen` matches the road's `(k : ℝ) * arcDen` at `k = a*h` by
`Nat.cast_mul`… — state the road at `h := a * h` and `push_cast`); `hcount` from
`bigXiAff_bounded_ceiling_of_pin a b h ha hh hah7 _ rfl` through `bigXiAffD_card_le`
(`Nat.cast_le.mpr`).  The pin `1/(500·(a·h))` is F1-C5's.  v2 (A4/A2): the ε-pin EQUALITY
`ε = 1/(500·(a·h))` and the count conjunct at `bigXiAffD` are F3-Q16's own at `h := a*h`, `Xi :=
bigXiAffD a b h` — nothing to prove here beyond the instance (`Nat.cast_mul` on the pin's
denominator if the road is stated at `(a*h : ℕ)`). -/
theorem mrtUniformityXiL2AffSet_holds_flat_floor (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
      ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∀ (U1floor a' : ℕ) (g : ℕ → ℕ → ℕ), flatDesignBase A ≤ U1floor →
        Real.log (Real.log ((U1floor : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 →
        1 ≤ a' → a' ≤ 1096 → XCeilRiderStrict ε g →
      ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = U1floor ∧ a' * g R.Hhi R.ω ≤ R.x ∧ StrideScale a' R ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        (∃ K : ℝ, 0 < K ∧ K ≤ 2 ^ 539 ∧ ∀ (H : ℕ) [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
          ((bigXiAffD a b h R.eps H).card : ℝ) ≤ K) ∧
        ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / (837782 * ((a * h : ℕ) : ℝ) ^ 2) ∧
          MRTUniformityXiL2Set (fun eps H _ => bigXiAffD a b h eps H) R ρ := by
  sorry

/-! ## §7 — THE CROWN: the affine door at Tao's range, at a regime that shares the tower -/

/-- **⟦THE CROWN⟧ (class B) — `mrtUniformityXiL2AffW_holds_flat_stride`.**  For every `(a, b, h)`
with `b < a`, `0 < h`, `log(a·h) ≤ 7` and every `A₀`: an affine regime `Ra` at stride `a`, offset
`b`, whose `Hlo` is `Rd.a · flatDesignBase A` for the door regime `Rd` (`= flatDesignBase A` when
the builder's stride is `1`, which it is but does not export — hence the product form, and the
floor `flatDesignBase A ≤ Ra.Hlo` exported beside it), carrying the affine `L²` door AT TAO'S
RANGE at grade **`≤ 1.02·a·ρ + E`** with `ρ ≤ 1/(837782·(ah)²)` and `E` a NAMED nonnegative
endpoint `≤ 2^539·a/((a·(Ra.x/ω)+1)·(log ω − 1))`.  The statement spells the grade `a·Zr·ρ + E`
with `Zr` a SLACK BINDER — `1 ≤ Zr ≤ 1.02` — NOT the normaliser ratio `Z/Z'` (v2, refuter verdict
A7: the ratio is `≤ 1.02` by F3-P17 but not `≥ 1` in general; `Z(10,3)/Z(5,3) = 0.854`).  The
executor takes `Zr := 1.02`, `E := 2^539·a/(…)` (the bound's own right side) and lands the door
by `mrtUniformityXiL2AffW_mono` (F3-P10a) from the transport's literal grade `a·(Z/Z')·ρ +
K·a/((…)·Z')`: `Z/Z' ≤ 1.02` (F3-P17 at `log ω ≥ 101`), `K·a/((…)·Z') ≤ 2^539·a/((…)·(log ω − 1))`
(F3-P18 at `Z' ≥ log ω − 1` from `harmonic_window_bounds`, `K ≤ 2^539`).
Assembly: `mrtUniformityXiL2AffSet_holds_flat_floor a b h ha hh hah7 A₀` at `U1floor := a *
flatDesignBase A` (`hU : flatDesignBase A ≤ a * B` by `Nat.le_mul_of_pos_left`; `hUceil :=
loglog_mul_flatDesignBase_le hA162 ha (log a ≤ log(ah) ≤ 7)`), `a' := a`, `g := 0`
(`xceilRiderStrict_zero`) — giving `Rd` with `Rd.Hlo = a * B`, `StrideScale a Rd`, the count
`hcountD : ∃ K ≤ 2^539, ∀ H ∈ [Rd.Hlo, Rd.Hhi], |bigXiAffD a b h Rd.eps H| ≤ K` (v2, A2: the
receipt's own conjunct, sourced from the widened P-slot — F3-P16's `hK` is stated at
`bigXiAffD`, so it is fed VERBATIM), and the door over `bigXiAffD`; then `regimeShrinkX_stride
Rd a ha ha1096 heps500 hs hdiv hlo4 hloM` with `hdiv : a ∣ Rd.a * (a * B)` (`Dvd.intro_left`),
`hlo4`/`hloM` from `flatDesignBase_clears_stride_floors hA162 (heps : 1/548000 ≤ ε)` and
`Rd.a * (a*B) / a = Rd.a * B ≥ B` (`Nat.mul_div_cancel`… with `Nat.le_mul_of_pos_left`),
`heps500 : Rd.eps ≤ 1/500` from the receipt's ε-PIN EQUALITY `hεeq : ε = 1/(500·(a·h))` and
`Rd.eps = ε` (v2, A4: `1/(500·(ah)) ≤ 1/500` at `a·h ≥ 1`, `one_div_le_one_div_of_le`; v1's
"read `ε ≤ 1/2` off the regime" route was bogus — `hcoprime` needs `2/ε² ≥ a`, i.e. `ε ≤ 1/24`
at `a ≤ 1096`); `hb : b ≤ Ra.Hlo` from `b < a ≤ 1096 ≤ 4·10⁶ ≤ Ra.Hlo`; `hω : 8 ≤ Rd.ω` from
`Rd.hωbig` (`log ω ≥ 64·500`); finally `mrtUniformityXiL2AffW_of_set`, the projections, and the
mono step above.  The top-level pin `ε = 1/(500·(a·h))` is the receipt's, forwarded. -/
theorem mrtUniformityXiL2AffW_holds_flat_stride (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hba : b < a) (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
      ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
        flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
        ∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * ((a * h : ℕ) : ℝ) ^ 2) ∧
          1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
          E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
              * (Real.log (Ra.ω : ℝ) - 1)) ∧
          MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E) := by
  sorry

end Salt.MR
