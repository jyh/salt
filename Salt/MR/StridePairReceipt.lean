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
  intro Hhi ω hgate
  obtain ⟨hH4, hll, hωg⟩ := hgate
  have hepsQ : (0 : ℚ) < ε := lt_of_lt_of_le (by norm_num) heps
  have hepsR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hepsQ
  have hepsR' : (1 / 548000 : ℝ) ≤ (ε : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr heps
    push_cast at hc
    linarith
  have hHR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hH4
  have hHpos : (0 : ℝ) < ((Hhi : ℕ) : ℝ) := by linarith
  -- ⟦THE TOWER⟧ `loglog H₊ ≥ 50` ⟹ `log H₊ ≥ e^50 ≥ 3.6·10^21` ⟹ `H₊ ≥ 3.6·10^21`
  have hL0 : (0 : ℝ) ≤ Real.log ((Hhi : ℕ) : ℝ) := Real.log_nonneg (by linarith)
  have hL1 : (1 : ℝ) < Real.log ((Hhi : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hL0 (by norm_num : (0 : ℝ) < 50) hll
  have hexp25 : (6e10 : ℝ) ≤ Real.exp 25 := by
    have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have hh25 : Real.exp (25 : ℝ) = (Real.exp 1) ^ (25 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hh25]
    have hc : (2.7 : ℝ) ^ (25 : ℕ) ≤ (Real.exp 1) ^ (25 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he1.le 25
    have hn : (6e10 : ℝ) ≤ (2.7 : ℝ) ^ (25 : ℕ) := by norm_num
    linarith
  have hexp50 : (36 * 10 ^ 20 : ℝ) ≤ Real.exp 50 := by
    have hsq : Real.exp 25 * Real.exp 25 = Real.exp 50 := by
      rw [← Real.exp_add]; norm_num
    rw [← hsq]
    nlinarith [hexp25, (Real.exp_pos 25).le]
  have hLexp : Real.exp 50 ≤ Real.log ((Hhi : ℕ) : ℝ) := by
    have h1 := Real.exp_le_exp.mpr hll
    rwa [Real.exp_log (by linarith : (0 : ℝ) < Real.log ((Hhi : ℕ) : ℝ))] at h1
  have hLbig : (36 * 10 ^ 20 : ℝ) ≤ Real.log ((Hhi : ℕ) : ℝ) := by linarith
  have hHbig : (36 * 10 ^ 20 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by
    have := Real.log_le_sub_one_of_pos hHpos
    linarith
  -- ⟦THE MARGIN⟧ `ε²·H₊ ≥ 1.19·10^10 ≥ 1095 ≥ log a`
  have hsqe : (1 / 300304000000 : ℝ) ≤ (ε : ℝ) ^ 2 := by nlinarith [hepsR']
  have hmargin : (1095 : ℝ) ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := by
    nlinarith [hsqe, hHbig, hHpos, hepsR]
  have hgstrict := hg Hhi ω ⟨hH4, hll, hωg⟩
  have hgoal : Real.log (((a * g Hhi ω : ℕ) : ℝ))
      ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (a * g Hhi ω) with hz | hp
    · rw [hz]
      simp only [Nat.cast_zero, Real.log_zero]
      have : (0 : ℝ) < 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) := by positivity
      linarith
    · have hmul : a * g Hhi ω ≠ 0 := hp.ne'
      have hap : 0 < a := Nat.pos_of_ne_zero (fun hc => hmul (by rw [hc, Nat.zero_mul]))
      have hgp : 0 < g Hhi ω := Nat.pos_of_ne_zero (fun hc => hmul (by rw [hc, Nat.mul_zero]))
      have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hap
      have hgR : (1 : ℝ) ≤ ((g Hhi ω : ℕ) : ℝ) := by exact_mod_cast hgp
      have hcast : (((a * g Hhi ω : ℕ)) : ℝ) = (a : ℝ) * ((g Hhi ω : ℕ) : ℝ) := by push_cast; ring
      rw [hcast, Real.log_mul (by linarith) (by linarith)]
      have hloga : Real.log ((a : ℕ) : ℝ) ≤ 1095 := by
        have h1 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (a : ℝ))
        have h2 : (a : ℝ) ≤ 1096 := by exact_mod_cast ha1096
        linarith
      linarith
  exact hgoal

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
  classical
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  -- the scale `m ≥ 1/ε`
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈(1 / eps : ℚ)⌉₊ := ⟨_, rfl⟩
  have hm_ge : (1 / eps : ℚ) ≤ (m : ℚ) := by rw [hmdef]; exact Nat.le_ceil _
  have hem : (1 : ℚ) ≤ eps * (m : ℚ) := by
    have h := mul_le_mul_of_nonneg_left hm_ge (le_of_lt heps)
    rwa [mul_one_div, div_self (ne_of_gt heps)] at h
  have hm1N : 1 ≤ m := by rw [hmdef]; exact Nat.ceil_pos.mpr (div_pos one_pos heps)
  have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm1N
  have hemR : (1 : ℝ) ≤ (eps : ℝ) * (m : ℝ) := by exact_mod_cast hem
  -- ⟦THE RE-BASED BASE⟧
  obtain ⟨Hlo, hHlodef⟩ : ∃ Hlo : ℕ,
      Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * m ^ 4)) := ⟨_, rfl⟩
  have hHloDF : flatDesignFloor A ≤ Hlo := by rw [hHlodef]; exact le_max_left _ _
  have hHlo_floor : 4000000 ≤ Hlo := le_trans (flatDesignFloor_house A) hHloDF
  have hHlo0 : Hlo₀ ≤ Hlo := by
    rw [hHlodef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hHlo4 : 4 * m ^ 4 ≤ Hlo := by
    rw [hHlodef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hHlo4Q : (4 : ℚ) * (m : ℚ) ^ 4 ≤ (Hlo : ℚ) := by exact_mod_cast hHlo4
  have hHlo4R : (4 : ℝ) * (m : ℝ) ^ 4 ≤ (Hlo : ℝ) := by exact_mod_cast hHlo4
  have hHlocap : Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) := by
    rw [hHlodef, hmdef]
  -- ⟦THE DESIGN LAW⟧ and the two floors it and `flatBase` supply
  have hflat : 3.2 * A ≤ Real.log (Real.log (Hlo : ℝ)) := flatDesignFloor_design hHloDF
  have hfl : 100 * (flatC A + Real.log (Real.log (Hlo : ℝ))) ≤ Real.log (Hlo : ℝ) :=
    flatFloor_of_design hA hHlo_floor hflat
  have h50 : (50 : ℝ) ≤ Real.log (Real.log (Hlo : ℝ)) := by linarith
  -- `hcoprime : 1 ≤ ε²·Hlo/2`
  have hcop : ((1 : ℕ) : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) / 2 := by
    have hprod : (1 : ℚ) ≤ (eps * (m : ℚ)) ^ 2 * (m : ℚ) ^ 2 := by
      have h1 : (1 : ℚ) ≤ (eps * (m : ℚ)) ^ 2 := by nlinarith [hem, sq_nonneg (eps * (m : ℚ) - 1)]
      have h2 : (1 : ℚ) ≤ (m : ℚ) ^ 2 := by nlinarith [hm1, sq_nonneg ((m : ℚ) - 1)]
      exact le_trans h1 (le_mul_of_one_le_right (sq_nonneg _) h2)
    have heq : (eps * (m : ℚ)) ^ 2 * (m : ℚ) ^ 2 = eps ^ 2 * (m : ℚ) ^ 4 := by ring
    have h4le : (4 : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) := by
      have hmul : eps ^ 2 * (4 * (m : ℚ) ^ 4) ≤ eps ^ 2 * (Hlo : ℚ) :=
        mul_le_mul_of_nonneg_left hHlo4Q (sq_nonneg eps)
      nlinarith [hmul, hprod, heq]
    rw [Nat.cast_one]; linarith
  -- `hPNTwindow : √Hlo ≤ ε²·Hlo/2`
  have hPNT : Real.sqrt (Hlo : ℝ) ≤ (eps : ℝ) ^ 2 * (Hlo : ℝ) / 2 := by
    have hsqrtHlo : (2 : ℝ) * (m : ℝ) ^ 2 ≤ Real.sqrt (Hlo : ℝ) := by
      have heq : Real.sqrt (4 * (m : ℝ) ^ 4) = 2 * (m : ℝ) ^ 2 := by
        rw [show (4 : ℝ) * (m : ℝ) ^ 4 = (2 * (m : ℝ) ^ 2) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
      calc (2 : ℝ) * (m : ℝ) ^ 2 = Real.sqrt (4 * (m : ℝ) ^ 4) := heq.symm
        _ ≤ Real.sqrt (Hlo : ℝ) := Real.sqrt_le_sqrt hHlo4R
    have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (Hlo : ℝ) := Real.sqrt_nonneg _
    have hHloeq : Real.sqrt (Hlo : ℝ) * Real.sqrt (Hlo : ℝ) = (Hlo : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have h2 : (2 : ℝ) ≤ (eps : ℝ) ^ 2 * Real.sqrt (Hlo : ℝ) := by
      have hstep : (eps : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2) ≤ (eps : ℝ) ^ 2 * Real.sqrt (Hlo : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrtHlo (sq_nonneg _)
      nlinarith [hstep, hemR, sq_nonneg ((eps : ℝ) * (m : ℝ) - 1)]
    have h3 : 2 * Real.sqrt (Hlo : ℝ) ≤ (eps : ℝ) ^ 2 * (Hlo : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right h2 hsqrtnn
      rw [mul_assoc, hHloeq] at hh
      linarith [hh]
    linarith [h3]
  -- ⟦THE TWO TOWERS⟧ at their minimal crossings, and the endpoint that hosts both
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = towerJmin 2 1 Hlo := ⟨_, rfl⟩
  obtain ⟨Jf, hJfdef⟩ : ∃ Jf : ℕ, Jf = towerFlatJmin A 1 Hlo := ⟨_, rfl⟩
  have hJ : Real.log 2 < towerDropSum 2 1 Hlo J := by
    rw [hJdef]; exact towerJmin_spec hHlo_floor
  have hJf : Real.log 2 < towerDropSumFlat A 1 Hlo Jf := by
    rw [hJfdef]; exact towerFlatJmin_spec hA1 hHlo_floor hfl
  obtain ⟨Hhi, hHhidef⟩ : ∃ Hhi : ℕ,
      Hhi = max (chowlaTower 2 1 Hlo J) (chowlaTowerFlat A 1 Hlo Jf) := ⟨_, rfl⟩
  have hfitL : chowlaTower 2 1 Hlo J ≤ Hhi := by rw [hHhidef]; exact le_max_left _ _
  have hfitFl : chowlaTowerFlat A 1 Hlo Jf ≤ Hhi := by rw [hHhidef]; exact le_max_right _ _
  have hHlohi : Hlo ≤ Hhi := le_trans (chowlaTower_base_ge hHlo_floor J) hfitL
  have hHhi_floor : 4000000 ≤ Hhi := le_trans hHlo_floor hHlohi
  -- ⟦THE WIDTH EXPORT⟧ at the flat shape, on both arms of the endpoint
  have hwidth : Real.log (Real.log (Hhi : ℝ))
      ≤ Real.exp (Real.log (Real.log (Hlo : ℝ)) / 2) := by
    rw [hHhidef, hJdef, hJfdef]
    rcases le_total (chowlaTower 2 1 Hlo (towerJmin 2 1 Hlo))
        (chowlaTowerFlat A 1 Hlo (towerFlatJmin A 1 Hlo)) with h | h
    · rw [max_eq_right h]
      exact towerFlat_width_export hA hHlo_floor hflat
    · rw [max_eq_left h]
      exact le_trans (tower_loglog_le_45 hHlo_floor h50) (pow_nine_halves_le_exp_half h50)
  -- the outer scale at this `ε` and endpoint, WITH THE CEILING
  obtain ⟨x, ω, hx2, hω2, hωx, hhead, hhead', hPH, homega, hxb, hxceil⟩ :=
    regime_outer_param_ceiling eps heps heps1 Hhi (4 ^ ⌊eps ^ 2 * (Hhi : ℚ)⌋₊) hHhi_floor
  -- ⟦THE CEILING AT THE BUILDER'S OWN `P`⟧
  have h2q : (2 : ℚ) * eps ≤ 1 := by linarith
  have h2r : (2 : ℝ) * (eps : ℝ) ≤ 1 := by exact_mod_cast h2q
  have hepsHalf : (eps : ℝ) ≤ 1 / 2 := by linarith
  have hHhiR : (4000000 : ℝ) ≤ (Hhi : ℝ) := by exact_mod_cast hHhi_floor
  have hHhipos : (0 : ℝ) < (Hhi : ℝ) := by linarith
  -- ⟦THE MULTIPLIER⟧ `log a ≤ 7` at `a ≤ 1096`
  have hapos : 0 < a := ha
  have haR0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
  have hlogA : Real.log ((a : ℕ) : ℝ) ≤ 7 := by
    have haR : ((a : ℕ) : ℝ) ≤ 1096 := by exact_mod_cast ha1096
    have he7 : (1096 : ℝ) ≤ Real.exp 7 := by
      have h3 : Real.exp 7 = (Real.exp 1) ^ (7 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have h4 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h5 : (2.7182818283 : ℝ) ^ (7 : ℕ) ≤ (Real.exp 1) ^ (7 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) h4.le 7
      have h6 : (1096 : ℝ) ≤ (2.7182818283 : ℝ) ^ (7 : ℕ) := by norm_num
      rw [h3]; linarith
    calc Real.log ((a : ℕ) : ℝ) ≤ Real.log (Real.exp 7) := Real.log_le_log haR0 (by linarith)
      _ = 7 := Real.log_exp 7
  -- ⟦THE CEILING AT `a·x`⟧ the landed collapse with the `+ 7` absorbed into `l`
  have hxceil' : Real.log (((a * x : ℕ)) : ℝ) ≤ 31 / (eps : ℝ) * (Hhi : ℝ) := by
    obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = 1 / (eps : ℝ) := ⟨_, rfl⟩
    have hu2 : (2 : ℝ) ≤ u := by rw [hudef, le_div_iff₀ hepsR]; linarith
    have hupos : (0 : ℝ) < u := by linarith
    have hbr30 : (30 : ℝ) / (eps : ℝ) * Real.log (Hhi : ℝ)
        = 30 * (u * Real.log (Hhi : ℝ)) := by rw [hudef]; ring
    have hbr31 : (31 : ℝ) / (eps : ℝ) * (Hhi : ℝ) = 31 * (u * (Hhi : ℝ)) := by
      rw [hudef]; ring
    have hx0R : (0 : ℝ) < ((x : ℕ) : ℝ) := by
      have hx2R : (2 : ℝ) ≤ ((x : ℕ) : ℝ) := by exact_mod_cast hx2
      linarith
    have hsplit : Real.log (((a * x : ℕ)) : ℝ)
        = Real.log ((a : ℕ) : ℝ) + Real.log ((x : ℕ) : ℝ) := by
      push_cast
      exact Real.log_mul (by positivity) (by positivity)
    have hxu : Real.log (((a * x : ℕ)) : ℝ)
        ≤ 30 * (u * (Real.log (Hhi : ℝ) + 7 / (30 * u)))
          + 2 * Real.log (((4 ^ ⌊eps ^ 2 * (Hhi : ℚ)⌋₊ : ℕ) : ℝ) + 1) := by
      have hcancel : 30 * (u * (Real.log (Hhi : ℝ) + 7 / (30 * u)))
          = 30 * (u * Real.log (Hhi : ℝ)) + 7 := by
        field_simp
      rw [hsplit, hcancel]
      linarith [hxceil, hbr30, hlogA]
    have hPterm := xceil_flat_P heps hepsHalf hepsR hHhiR
    have hlogself : Real.log (Hhi : ℝ) + 7 / (30 * u) ≤ (Hhi : ℝ) := by
      have h1 : Real.log (Hhi : ℝ) ≤ (Hhi : ℝ) - 1 := Real.log_le_sub_one_of_pos hHhipos
      have h2 : 7 / (30 * u) ≤ 7 / 60 := by
        have h60 : (60 : ℝ) ≤ 30 * u := by linarith
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h60
      linarith
    have hfin := xceil_flat_step hu2 hHhiR hlogself hxu hPterm
    linarith [hfin, hbr31]
  have hxle : x ≤ a * x := Nat.le_mul_of_pos_left x hapos
  have hdivc : (a * x) / a = x := Nat.mul_div_cancel_left x hapos
  refine ⟨regimeFlatEnlargeX
      { x := x, ω := ω, a := 1, eps := eps, Hlo := Hlo, Hhi := Hhi, C0 := 2, J := J,
        hx := hx2, hω := hω2, hωx := hωx, ha := le_refl 1, heps := heps, heps1 := heps1,
        hHlo := le_trans (by norm_num) hHlo_floor, hHlohi := hHlohi, hC0 := le_refl 2,
        hHlo_floor := hHlo_floor, hheadroom := hhead, hcoprime := hcop, hfit := hfitL,
        hJcon := hJ, hheadroom' := hhead', hPHheadroom := hPH, hPNTwindow := hPNT,
        hωbig := homega, hxbig := hxb,
        A := A, hA := hA, hflat := hflat, Jf := Jf,
        hfitF := by simpa using hfitFl, hJconF := by simpa using hJf } hxle,
    rfl, rfl, hHlo0, ?_, hHlocap, hwidth, ?_⟩
  · refine ⟨dvd_mul_right a x, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_omega, regimeFlatEnlargeX_Hhi,
        regimeFlatEnlargeX_eps, hdivc]
    · exact hx2
    · exact hωx
    · exact hhead
    · exact hhead'
    · exact hPH
    · exact hxb
  · simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_Hhi]
    exact hxceil'

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
  obtain ⟨R, hReps, hRA, hRHlo, hstride, hRcap, hRwid, hRx⟩ :=
    chowlaRegimeFlat_exists_param_gen_ceiling_mul a ha ha1096 A hA eps heps heps1 Hlo₀
  have hapos : 0 < a := ha
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  -- ⟦THE ENDPOINT FLOOR⟧
  have hHhi4 : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
  have hHhiR : (4000000 : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast hHhi4
  have hHlo4 : (4000000 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast R.hHlo_floor
  -- ⟦THE `loglog` FLOOR⟧ off the design law `3.2·A ≤ loglog H₋` at `A ≥ 26`
  have hll50 : (50 : ℝ) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) := by
    have hflat : 3.2 * R.A ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) := R.hflat
    have hA26 : (26 : ℝ) ≤ R.A := R.hA
    have hlogpos : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
      Real.log_pos (by linarith)
    have hmono : Real.log ((R.Hlo : ℕ) : ℝ) ≤ Real.log ((R.Hhi : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      exact_mod_cast R.hHlohi
    have := Real.log_le_log hlogpos hmono
    linarith
  -- ⟦THE WIDTH WINDOW⟧ the majorant field read against the ceiling
  have hωgate : Real.log ((R.ω : ℕ) : ℝ) + (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ)
      ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    set P : ℕ := 4 ^ ⌊R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)⌋₊ with hPdef
    set n : ℕ := ⌊R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)⌋₊ with hndef
    have hPH : 8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ) ≤ ((R.x : ℕ) : ℝ) := R.hPHheadroom
    have hP1 : (1 : ℝ) ≤ ((P : ℕ) : ℝ) := by
      rw [hPdef]
      have : (1 : ℕ) ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
      exact_mod_cast this
    have hω1 : (1 : ℝ) ≤ ((R.ω : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ R.ω := le_trans (by norm_num) R.hω
      exact_mod_cast this
    -- `log 8 + 2·log P + log ω ≤ log x`
    have hpos : (0 : ℝ) < 8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ) := by positivity
    have hlogle : Real.log (8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ))
        ≤ Real.log ((R.x : ℕ) : ℝ) := Real.log_le_log hpos hPH
    have hsplit : Real.log (8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ))
        = Real.log 8 + 2 * Real.log ((P : ℕ) : ℝ) + Real.log ((R.ω : ℕ) : ℝ) := by
      rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow]
      push_cast
      ring
    -- `log P = n·log 4 ≥ (ε²H₊ − 1)·log 4`
    have hlogP : Real.log ((P : ℕ) : ℝ) = (n : ℝ) * Real.log 4 := by
      rw [hPdef]
      have h4 : ((4 ^ n : ℕ) : ℝ) = (4 : ℝ) ^ n := by push_cast; ring
      rw [h4, Real.log_pow]
    have hnge : (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) - 1 ≤ (n : ℝ) := by
      have hQ : R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ) < (n : ℚ) + 1 := by
        rw [hndef]; exact Nat.lt_floor_add_one _
      have hR : (R.eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) < (n : ℝ) + 1 := by exact_mod_cast hQ
      rw [hReps] at hR
      linarith
    have hlog4 : (1.3862 : ℝ) ≤ Real.log 4 := by
      have h : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      rw [h]; linarith [Real.log_two_gt_d9]
    have hlog8 : (2.0794 : ℝ) ≤ Real.log 8 := by
      have h : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      rw [h]; linarith [Real.log_two_gt_d9]
    -- ⟦THE COPRIMALITY FLOOR⟧ `ε²·H₊ ≥ 2`
    have hcop : (2 : ℝ) ≤ (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) := by
      have hQ : ((R.a : ℕ) : ℚ) ≤ R.eps ^ 2 * ((R.Hlo : ℕ) : ℚ) / 2 := R.hcoprime
      have ha1 : (1 : ℚ) ≤ ((R.a : ℕ) : ℚ) := by exact_mod_cast R.ha
      have hQ2 : (2 : ℚ) ≤ R.eps ^ 2 * ((R.Hlo : ℕ) : ℚ) := by linarith
      have hR2 : (2 : ℝ) ≤ (R.eps : ℝ) ^ 2 * ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast hQ2
      rw [hReps] at hR2
      have hmono : (eps : ℝ) ^ 2 * ((R.Hlo : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast R.hHlohi) (sq_nonneg _)
      linarith
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith [hlogle, hsplit, hlogP, hnge, hlog4, hlog8, hRx, hcop, hnn]
  have hgx : Real.log (((a * g R.Hhi R.ω : ℕ)) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) :=
    hg R.Hhi R.ω ⟨hHhi4, hll50, hωgate⟩
  -- ⟦THE PUSH⟧ the scale to `a * max (R.x / a) (g R.Hhi R.ω)`
  have hxa : a * (R.x / a) = R.x := Nat.mul_div_cancel' hstride.1
  have hxle : R.x ≤ a * max (R.x / a) (g R.Hhi R.ω) := by
    calc R.x = a * (R.x / a) := hxa.symm
      _ ≤ a * max (R.x / a) (g R.Hhi R.ω) := Nat.mul_le_mul_left a (le_max_left _ _)
  have hdivc : (a * max (R.x / a) (g R.Hhi R.ω)) / a = max (R.x / a) (g R.Hhi R.ω) :=
    Nat.mul_div_cancel_left _ hapos
  have hmle : R.x / a ≤ max (R.x / a) (g R.Hhi R.ω) := le_max_left _ _
  have hmleR : ((R.x / a : ℕ) : ℝ) ≤ ((max (R.x / a) (g R.Hhi R.ω) : ℕ) : ℝ) := by
    exact_mod_cast hmle
  have hmdiv : R.x / a / R.ω ≤ max (R.x / a) (g R.Hhi R.ω) / R.ω :=
    Nat.div_le_div_right hmle
  have hmdivR : ((R.x / a / R.ω : ℕ) : ℝ)
      ≤ ((max (R.x / a) (g R.Hhi R.ω) / R.ω : ℕ) : ℝ) := by exact_mod_cast hmdiv
  refine ⟨regimeFlatEnlargeX R hxle, hReps, hRA, hRHlo, ?_, ?_, hRcap, hRwid, ?_⟩
  · simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_omega, regimeFlatEnlargeX_Hhi]
    exact Nat.mul_le_mul_left a (le_max_right _ _)
  · refine ⟨dvd_mul_right _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_omega, regimeFlatEnlargeX_Hhi,
        regimeFlatEnlargeX_eps, hdivc]
    · exact le_trans hstride.2.1 hmle
    · exact le_trans hstride.2.2.1 hmle
    · exact le_trans hstride.2.2.2.1 hmdiv
    · exact le_trans hstride.2.2.2.2.1 hmdivR
    · exact le_trans hstride.2.2.2.2.2.1 hmleR
    · exact le_trans hstride.2.2.2.2.2.2 hmleR
  · simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_Hhi]
    rcases le_total (R.x / a) (g R.Hhi R.ω) with hc | hc
    · rw [max_eq_right hc]; exact hgx
    · rw [max_eq_left hc, hxa]; exact hRx

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
  obtain ⟨H₀, hH₀⟩ := nearRatTight_of_bigXiArcTight harc heps
  refine ⟨H₀, ?_⟩
  intro H _ hH hdvd ξ hξ
  have hHpos : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hHpos
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  obtain ⟨η, _hη, hmem⟩ := mem_bigXiAff_iff.mp hξ
  have hbase := hH₀ H hH _ hmem
  -- ⟦THE VALUE IDENTITY⟧ `ζ.val = N % H` at `N := (b+h)·η·(H/a) + h·ξ.val`
  obtain ⟨N, hNdef⟩ : ∃ n : ℕ, n = (b + h) * η * (H / a) + h * ξ.val := ⟨_, rfl⟩
  have hcv : (affOffset a b h H η).val = ((b + h) * η * (H / a)) % H := by
    unfold affOffset
    rw [ZMod.val_natCast]
  have htv : ((h : ZMod H) * ξ).val = (h * ξ.val) % H := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  have hzv : (affOffset a b h H η + (h : ZMod H) * ξ).val = N % H := by
    rw [ZMod.val_add, hcv, htv, ← Nat.add_mod, hNdef]
  have hdm : H * (N / H) + N % H = N := Nat.div_add_mod N H
  have hcast : (H : ℝ) * ((N / H : ℕ) : ℝ) + ((N % H : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hdm
  have hdivR : ((H / a : ℕ) : ℝ) = (H : ℝ) / (a : ℝ) :=
    Nat.cast_div hdvd (ne_of_gt haR)
  have hNR : (N : ℝ) = (((b + h) * η : ℕ) : ℝ) * ((H : ℝ) / (a : ℝ))
      + (h : ℝ) * (ξ.val : ℝ) := by
    rw [hNdef]
    push_cast [hdivR]
    ring
  -- ⟦THE FREQUENCY IDENTITY⟧ THE CAST SEAM ADDITIVE, never subtractive
  have hfreq : -(((affOffset a b h H η + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ)
      = ((h : ℝ) * (-(ξ.val : ℝ) / (H : ℝ)) - (((b + h) * η : ℕ) : ℝ) / (a : ℝ))
        + ((((N / H : ℕ)) : ℤ) : ℝ) := by
    rw [hzv]
    have hkz : ((((N / H : ℕ)) : ℤ) : ℝ) = ((N / H : ℕ) : ℝ) := Int.cast_natCast _
    rw [hkz]
    have key : -((N % H : ℕ) : ℝ)
        = (h : ℝ) * (-(ξ.val : ℝ)) - (((b + h) * η : ℕ) : ℝ) * ((H : ℝ) / (a : ℝ))
          + ((N / H : ℕ) : ℝ) * (H : ℝ) := by linarith [hcast, hNR]
    calc -((N % H : ℕ) : ℝ) / (H : ℝ)
        = ((h : ℝ) * (-(ξ.val : ℝ)) - (((b + h) * η : ℕ) : ℝ) * ((H : ℝ) / (a : ℝ))
            + ((N / H : ℕ) : ℝ) * (H : ℝ)) / (H : ℝ) := by rw [key]
      _ = ((h : ℝ) * (-(ξ.val : ℝ) / (H : ℝ)) - (((b + h) * η : ℕ) : ℝ) / (a : ℝ))
            + ((N / H : ℕ) : ℝ) := by
          field_simp
  rw [hfreq] at hbase
  -- ⟦THE OFFSET, A RATIONAL WITH DENOMINATOR `a`⟧ the cap pays `a`, the radius pays nothing
  have hstep2 : NearRatTight ((a : ℝ) * arcDen B₅ H) H
      ((h : ℝ) * (-(ξ.val : ℝ) / (H : ℝ))) := by
    obtain ⟨A₁, q, hq, hqQ, hd⟩ := (nearRatTight_intCast_add _).mp hbase
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    refine ⟨A₁ * (a : ℤ) + (((b + h) * η : ℕ) : ℤ) * (q : ℤ), q * a,
      Nat.mul_pos hq ha, ?_, ?_⟩
    · have hle : (q : ℝ) * (a : ℝ) ≤ arcDen B₅ H * (a : ℝ) :=
        mul_le_mul_of_nonneg_right hqQ haR.le
      push_cast
      linarith [hle]
    · have hrw : (h : ℝ) * (-(ξ.val : ℝ) / (H : ℝ))
          - ((A₁ * (a : ℤ) + (((b + h) * η : ℕ) : ℤ) * (q : ℤ) : ℤ) : ℝ)
              / (((q * a : ℕ)) : ℝ)
          = ((h : ℝ) * (-(ξ.val : ℝ) / (H : ℝ)) - (((b + h) * η : ℕ) : ℝ) / (a : ℝ))
            - (A₁ : ℝ) / (q : ℝ) := by
        push_cast
        field_simp
        ring
      have hrad : (a : ℝ) * arcDen B₅ H / ((((q * a : ℕ)) : ℝ) * (H : ℝ))
          = arcDen B₅ H / ((q : ℝ) * (H : ℝ)) := by
        push_cast
        field_simp
      rw [hrw, hrad]
      exact hd
  -- ⟦N2⟧ dividing the frequency by `h`, the cap paying exactly `h` more
  have hfinal := nearRatTight_div_nat hh hstep2
  have hQeq : ((a * h : ℕ) : ℝ) * arcDen B₅ H = (h : ℝ) * ((a : ℝ) * arcDen B₅ H) := by
    push_cast
    ring
  rw [hQeq]
  exact hfinal

/-- **F3-Q4a (class A).**  The bridge at the grid-restricted family, for EVERY `H`: on the grid
`bigXiAffD_of_dvd` rewrites to F3-Q4; off it the set is `∅` (`bigXiAffD`'s `if_neg`) and the
statement is vacuous (`Finset.not_mem_empty`).  This is the `harc` the road replay consumes. -/
theorem nearRatTight_of_bigXiAffD {B₅ : ℝ} (harc : BigXiArcTight B₅)
    {eps : ℚ} (heps : 0 < eps) {a b h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXiAffD a b h eps H,
      NearRatTight (((a * h : ℕ) : ℝ) * arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)) := by
  obtain ⟨H₀, hH₀⟩ := nearRatTight_of_bigXiAffArcTight harc heps ha hh
  refine ⟨H₀, ?_⟩
  intro H _ hH ξ hξ
  by_cases hdvd : a ∣ H
  · exact hH₀ H hH hdvd ξ (by rwa [bigXiAffD_of_dvd hdvd] at hξ)
  · exfalso
    simp only [bigXiAffD, if_neg hdvd] at hξ
    simp at hξ

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
  intro H _ hlo hhi
  have hH0 : H ≠ 0 := NeZero.ne H
  have hHpos : (0 : ℝ) < (H : ℝ) := by positivity
  have hinvpos : (0 : ℝ) < 1 / (H : ℝ) ^ 2 := by positivity
  -- ⟦N4a AT `Xi`⟧ the landed body (HDoorArc.lean:211-293) with the set renamed
  have N4a : ∀ e : ℕ → ℂ, (∀ m, lamCoeff m = a m + e m) →
      (∑ ξ ∈ Xi R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω)) ≤ Binsert →
      (∑ ξ ∈ Xi R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
        ≤ K * (2 * Bsieve H) + 2 * Binsert := by
    intro e hsplit hI
    have hfun : lamCoeff = fun m => a m + e m := funext hsplit
    have hterm : ∀ ξ ∈ Xi R.eps H,
        (1 / (H : ℝ) ^ 2) * (∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
            ∂(logMeasure R.x R.ω))
          ≤ 2 * Bsieve H + 2 * ((1 / (H : ℝ) ^ 2) *
              ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                ∂(logMeasure R.x R.ω)) := by
      intro ξ hξ
      have harcξ := harc H (le_trans hfloor hlo) ξ hξ
      have hrw : (∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
            ∂(logMeasure R.x R.ω))
          = ∫ n, ‖absWindowSum (fun m => a m + e m) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
        simp only [norm_windowExpSum_eq_absWindowSum, hfun]
      rw [hrw]
      have hspl := integral_norm_absWindowSum_sq_split R.x R.ω H a e (-(ξ.val : ℝ) / (H : ℝ))
      have hs := hsock H hlo hhi (-(ξ.val : ℝ) / (H : ℝ)) harcξ
      have hA : (1 / (H : ℝ) ^ 2) * (∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω)) ≤ Bsieve H := by
        have hm := mul_le_mul_of_nonneg_left hs hinvpos.le
        have heq : (1 / (H : ℝ) ^ 2) * (Bsieve H * (H : ℝ) ^ 2) = Bsieve H := by
          field_simp
        linarith [hm, heq.le, heq.ge]
      have hmul := mul_le_mul_of_nonneg_left hspl hinvpos.le
      have hexp : (1 / (H : ℝ) ^ 2) *
          (2 * (∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                ∂(logMeasure R.x R.ω))
            + 2 * ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                ∂(logMeasure R.x R.ω))
          = 2 * ((1 / (H : ℝ) ^ 2) * ∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                ∂(logMeasure R.x R.ω))
            + 2 * ((1 / (H : ℝ) ^ 2) * ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                ∂(logMeasure R.x R.ω)) := by ring
      rw [hexp] at hmul
      linarith
    have hcard := hXi H hlo hhi
    have h2B : (0 : ℝ) ≤ 2 * Bsieve H := by have := hB0 H; linarith
    have hKB := mul_le_mul_of_nonneg_right hcard h2B
    calc (∑ ξ ∈ Xi R.eps H, (1 / (H : ℝ) ^ 2) *
            ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure R.x R.ω))
        ≤ ∑ _ξ ∈ Xi R.eps H, (2 * Bsieve H + 2 * ((1 / (H : ℝ) ^ 2) *
            ∫ n, ‖absWindowSum e H n (-(_ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω))) := Finset.sum_le_sum hterm
      _ = ((Xi R.eps H).card : ℝ) * (2 * Bsieve H)
            + 2 * ∑ ξ ∈ Xi R.eps H, (1 / (H : ℝ) ^ 2) *
                ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                  ∂(logMeasure R.x R.ω) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      _ ≤ K * (2 * Bsieve H) + 2 * Binsert := by linarith
  -- ⟦THE PARSEVAL SPELLING⟧ HDoorArc.lean:353-376 with the set renamed
  have hsub : ∀ (n : ℕ) (α : ℝ),
      absWindowSum (fun m => lamCoeff m - a m) H n α
        = absWindowSum lamCoeff H n α - absWindowSum a H n α := by
    intro n α
    have hA := absWindowSum_add_coeff a (fun m => lamCoeff m - a m) H n α
    have hf : (fun m => a m + (lamCoeff m - a m)) = lamCoeff := funext fun m => by ring
    rw [hf] at hA
    rw [hA]
    ring
  refine N4a (fun m => lamCoeff m - a m) (fun m => by ring) ?_
  have hcongr : (∑ ξ ∈ Xi R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖absWindowSum (fun m => lamCoeff m - a m) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
      = (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ Xi R.eps H,
        ∫ n, ‖absWindowSum lamCoeff H n (-(ξ.val : ℝ) / (H : ℝ))
            - absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
    simp only [hsub]
  rw [hcongr]
  exact hins H hlo hhi

/-- **F3-Q6 (class B) — the door-L2 supply at a generic set.**  `m4_doorL2_supply_H_L_gk_khoist`
(S16ComposeLH.lean:1072) with the set `Xi` and the arc bridge `harcXi` a HYPOTHESIS (at the
landed set it is `nearRatTight_of_bigXiArcTight_H bigXiArcTight_twelve`, the one line the landed
body spends on the set).  Body verbatim otherwise: `parseval_insert_budget_door_bounded`, the
`H₀` from `harcXi eps heps`, `harc` transported to the regime's `ε` by `rw [hReps]`, the four
scale lines, `hins` via `hpars … (Xi R.eps H)` (parseval is set-generic), then F3-Q5 in place of
N4c and the budget line `l2_budget_line`.  The socket stays `M4SievedDoorSqH_L_gk h` — the cap
`(h : ℝ) * arcDen 12 H` is the road's PARAMETER, and the affine instance runs at `h := a·h`. -/
theorem m4_doorL2_supply_Set_gk_khoist (h : ℕ) (_hh : 0 < h) (Xi : XiFamily)
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
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  refine ⟨Cg, hCg, hCgle, ?_⟩
  intro eps heps
  obtain ⟨H₀, hH₀⟩ := harcXi eps heps
  refine ⟨H₀, ?_⟩
  intro K R hReps hfloor Braw Kc Bceil δ M k hgates hBraw0 hsock hXi hK0 hceil
  -- ⟦the arc supply at the PARAMETER set, transported to the regime's own `ε`⟧
  have harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ Xi R.eps H,
      NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)) := by
    intro H _ hH ξ hξ
    rw [hReps] at hξ
    exact hH₀ H hH ξ hξ
  -- ⟦the door's own scales, off the regime — the lane's four lines⟧
  have hA : 1 ≤ AdoorL M := one_le_AdoorL hgates.hM
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
    intro H hhi
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  -- ⟦THE FUSE⟧ the adapter's `hins`, fired at `Xi R.eps H` (parseval is set-generic).
  have hins : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ Xi R.eps H,
        ∫ n, ‖absWindowSum lamCoeff H n (-(ξ.val : ℝ) / (H : ℝ))
            - absWindowSum (memSCoeff (calP (AdoorL M) (s13GK K M))
                (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω)
        ≤ δ / 4 + 4 * 2 ^ k / (R.x : ℝ) := by
    intro H _ hlo hhi
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (AdoorL M) (s13GK K M) M 2 R.x R.ω H k liouvilleC δ (Xi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  -- ⟦the adapter⟧ F3-Q5 at the cap `Q H := h·arcDen 12 H`.
  have hkey := sum_Xi_norm_windowExpSum_sq_le_parseval Xi (fun H => (h : ℝ) * arcDen 12 H) R
    (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC)
    Braw Kc (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) hfloor harc hBraw0 (hsock m4_bandTransport)
    hXi hins
  -- ⟦the budget line⟧ and the `H`-uniform ceiling on the socket leg.
  intro H _ hlo hhi
  have hb := hkey H hlo hhi
  rw [l2_budget_line Kc (Braw H) δ (R.x : ℝ) k] at hb
  have hmono : 2 * Kc * Braw H ≤ 2 * Kc * Bceil :=
    mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
  linarith

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
  obtain ⟨Cg, hCg, hCgle, hmint⟩ := m4_doorL2_supply_Set_gk_khoist h hh Xi harcXi
  refine ⟨Cg, hCg, hCgle, ?_⟩
  intro eps heps
  obtain ⟨H₀, hH₀⟩ := hmint eps heps
  refine ⟨H₀, ?_⟩
  intro K R hReps hfloor δ Bceil Kc RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han
    hG1 hG2 harc3 hdgate hdrift hceil hXi hKc0 hrow
  have hh1 : 1 ≤ h := hh
  have harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh1 hlo
    nlinarith [h1, harc1]
  have harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * ((h : ℝ) * arcDen 12 H) ^ 2 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh1 hlo
    nlinarith [h1, harc1]
  have hchi : M4ChiSummedBlockMeanSqNH_L_gk h K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_suppliedH_L_gk h K j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummedH_L_gk h K (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidualH h H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  have hcov := m4_cover_assembly_blk2H_L_gk h K hgates hBblk0 hblk2
  refine hH₀ K R hReps hfloor Braw Kc Bceil δ M k hgates hBraw0 ?_ hXi hKc0 hceil
  refine m4_sievedDoorSq_of_blk2H_L_gk h K (ℓ := blockLenH h)
    (fun H => by have := hBblk0 H; positivity)
    (fun H q _ _ _ _ => one_le_blockLenH h H q) ?_ ?_ ?_ ?_ hcov
  · intro H q hlo hhi _ _
    have h1 := harc H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh1 hlo
    have hH1 : 1 ≤ H := by
      have : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
      exact_mod_cast this
    exact blockLenH_le h H q hH1
  · intro H q hlo hhi _ _
    exact blockLenH_narrow (R := R) hh1 hlo (harc H hlo hhi)
  · intro H q hlo hhi hq _
    exact blockLenH_drift (R := R) hh1 hlo hq (harc H hlo hhi)
  · intro H hlo hhi
    have hdr := hdrift H hlo hhi
    have hres0 : (0 : ℝ) ≤ strataResidualH h H :=
      strataResidualH_nonneg (one_le_hArcDen_of_regime hh1 hlo)
    have hB := hBcl0 H
    nlinarith [hdr]

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
theorem flat_roadExit_generic_h (h : ℕ) (hh : 0 < h) (_hh7 : Real.log (h : ℝ) ≤ 7)
    (Xi : XiFamily)
    (harcXi : ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
      ∀ ξ ∈ Xi eps H, NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (P : ChowlaRegime → Prop) (hhead : FlatHeadFormH h Xi P) :
    FlatRoadExitFormH h P := by
  obtain ⟨Cg, hCg, hCgle, hreg⟩ := m4_second_road_L2_Set_gk_flatRoot_L_khoist h hh Xi harcXi
  obtain ⟨ε, Kb, δ₀, β, Hopq, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, hhd0⟩ := hhead
  obtain ⟨H₀, hH₀⟩ := hreg ε hε
  refine ⟨Cg, ε, Kb, δ₀, β, max Hopq H₀, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge
  obtain ⟨Hcap, hCapEq, hhd⟩ := hhd0 A (by linarith) hAge
  refine ⟨max Hcap H₀, by rw [hCapEq]; exact flatRootCapH_arc_k _ _ _ _ _, ?_⟩
  intro a U1floor g ha ha1096 hg
  obtain ⟨R, hReps, hRextra, hRU1, hRg, hstride, hRx, hcount, hRtow, hRcap, hR⟩ :=
    hhd a H₀ U1floor g ha ha1096 hg
  refine ⟨R, hReps, hRU1, hRg, hstride, hRx, hRtow, le_trans hRcap (by omega), ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  have hdoor := hH₀ K R hReps hRextra δ Bceil Kb RS RSan RStr Braw M k j₀ hgates hM hRSan0
    hRStr0 hBraw0 han hG1 hG2 harc3 hdgate hdrift hceil hcount hKb.le hrow
  refine hR δ₀ hδ₀ le_rfl ?_
  intro H _ hlo hhi
  exact le_trans (hdoor H hlo hhi) hbudget

/-- **⟦H1→H2 REPLAY⟧ (class B).**  The capstone (S16ComposeLH.lean:2060-2142) from a generic road
exit: body verbatim (the capstone forwards the road's regime and the caller's `g` untouched, so
it forwards the multiplier and `StrideScale` untouched too); `hroadU` is the hypothesis. -/
theorem flat_capstone_generic_h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) (Awin : ℝ)
    (hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hroad : FlatRoadExitFormH h P) :
    FlatCapstoneFormH h Awin P := by
  obtain ⟨Cg, ε, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hKcb, hδ₀, hεpin, hδpin, hβ, hroadU⟩ :=
    hroad
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, hKcb,
    (fun A hA162 hAw => flatDoorM_gradeFloor_win hA162 hCband0 (by linarith)),
    hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hfuse⟩ :=
    m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling_kwide h hh hh7 K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hroad0⟩ := hroadU K A hA26 hAge
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp a U1floor g ha ha1096 hg
  obtain ⟨R, hReps, hU1, hRg, hstride, hRx, hRtow, hRcap, hR⟩ :=
    hroad0 a (max U1floor (max arcFloor36 loglogFloor50)) g ha ha1096 hg
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hstride, hRx, hRtow, by omega, ?_⟩
  intro M hMfloor hKw
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit K M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the absorbed floor⟧ ⭐ at `h` only `loglogFloor50` is read: `arc36_of_regime_h` routes
  -- gate 7 off the tower floor, because `arcFloor36` clears `h = 1` by 1.14× and FAILS at `h ≥ 2`.
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRowH_L_gk h K R M
      (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H) j H ≤ RSanDoorRhoH ρ h H :=
    m4_arith_gate4_rhoH_L h M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 * (108 / 5 * RSanDoorRhoH ρ h H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_deltaH hh hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) (RSanDoorRhoH ρ h)
    (fun H => (h : ℝ) ^ 7 * rStrWitness H)
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
          (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRhoH_nonneg hρpos.le h H)
    (fun H => rStrWitness_mul_nonneg h H) ?_ hgate4 (fun H _ _ => rStrWitness_G1_h h H) ?_
    (arc36_of_regime_h hh hh7 hllfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRhoH ρ h H)
      (Ftr := fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) (H := H)
      (by have := RSanDoorRhoH_nonneg hρpos.le h H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRhoH ρ h H))
      (by have := rStrWitness_mul_nonneg h H
          simpa using (by linarith : (0:ℝ) ≤ 2 * ((h : ℝ) ^ 7 * rStrWitness H)))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh hlo
    have hSR1 : (1 : ℝ) ≤ strataResidualH h H := one_le_strataResidualH harc1
    have hSRsq : (1 : ℝ) ≤ strataResidualH h H ^ 2 := by nlinarith
    have hRSle : RSanDoorRhoH ρ h H ≤ rSanWitness H := by
      have h1 : RSanDoorRhoH ρ h H ≤ 1 := by
        unfold RSanDoorRhoH
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor_h h hh H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRhoH ρ h H)
      (Ftr := fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
            (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRhoH ρ h H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRhoH ρ h H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
            * (108 / 5 * RSanDoorRhoH ρ h H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
        * (108 / 5 * RSanDoorRhoH ρ h H)) ≤ 2 * δs ^ 2 := by linarith
    have hKcpos : (0 : ℝ) < 16 * Kc := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

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
  have hx0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hx1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have h1096 : (h : ℝ) ≤ 1096 := by
    exact_mod_cast Salt.Entropy.Chowla.h_le_1096_of_log_le_seven hh hh7
  have hsqb : (h : ℝ) ^ 2 ≤ 1201216 := by nlinarith [hx1, h1096]
  have hHR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hH4
  have hHpos : (0 : ℝ) < ((Hhi : ℕ) : ℝ) := by linarith
  -- ⟦THE TOWER⟧ `loglog H₊ ≥ 50` ⟹ `log H₊ ≥ e^50 ≥ 3.6·10^21` ⟹ `H₊ ≥ 3.6·10^21`
  have hL0 : (0 : ℝ) ≤ Real.log ((Hhi : ℕ) : ℝ) := Real.log_nonneg (by linarith)
  have hL1 : (1 : ℝ) < Real.log ((Hhi : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hL0 (by norm_num : (0 : ℝ) < 50) hll
  have hexp25 : (6e10 : ℝ) ≤ Real.exp 25 := by
    have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have hh25 : Real.exp (25 : ℝ) = (Real.exp 1) ^ (25 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hh25]
    have hc : (2.7 : ℝ) ^ (25 : ℕ) ≤ (Real.exp 1) ^ (25 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he1.le 25
    have hn : (6e10 : ℝ) ≤ (2.7 : ℝ) ^ (25 : ℕ) := by norm_num
    linarith
  have hexp50 : (36 * 10 ^ 20 : ℝ) ≤ Real.exp 50 := by
    have hsq : Real.exp 25 * Real.exp 25 = Real.exp 50 := by
      rw [← Real.exp_add]; norm_num
    rw [← hsq]
    nlinarith [hexp25, (Real.exp_pos 25).le]
  have hLexp : Real.exp 50 ≤ Real.log ((Hhi : ℕ) : ℝ) := by
    have h1 := Real.exp_le_exp.mpr hll
    rwa [Real.exp_log (by linarith : (0 : ℝ) < Real.log ((Hhi : ℕ) : ℝ))] at h1
  have hLbig : (36 * 10 ^ 20 : ℝ) ≤ Real.log ((Hhi : ℕ) : ℝ) := by linarith
  have hHbig : (36 * 10 ^ 20 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by
    have := Real.log_le_sub_one_of_pos hHpos
    linarith
  -- ⟦THE SLACK⟧ the `h²` widening of the denominator, then a linear comparison
  have hr1 : ((Hhi : ℕ) : ℝ) / (250000 * 1201216)
      ≤ ((Hhi : ℕ) : ℝ) / (250000 * (h : ℝ) ^ 2) := by
    have hpos : (0 : ℝ) < 250000 * (h : ℝ) ^ 2 := by positivity
    have hle : 250000 * (h : ℝ) ^ 2 ≤ 250000 * 1201216 := by nlinarith [hsqb]
    gcongr
  have e1 : ((Hhi : ℕ) : ℝ) / (250000 * 1201216)
      = ((Hhi : ℕ) : ℝ) * (1 / 300304000000) := by ring
  have e2 : ((Hhi : ℕ) : ℝ) / (10 : ℝ) ^ 20
      = ((Hhi : ℕ) : ℝ) * (1 / 100000000000000000000) := by norm_num; ring
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hkey : Real.log 2 + Real.log (h : ℝ) + 7
      ≤ ((Hhi : ℕ) : ℝ) / (250000 * 1201216) - ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
    rw [e1, e2]; linarith [hHbig, hlog2, hh7]
  linarith [hkey, hr1]

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
    (Awin : ℝ) (_hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hcap : FlatCapstoneFormH h Awin P) :
    FlatConditionalFormH h Awin P := by
  obtain ⟨Cg, ε, Kc, δ₀, β, x₀, Hopq, Mfl, hCg, hε, hKc,
    hδ₀, hMfl, hCgle, hεpin, hδpin, hKcb, hMflb,
    hβ, hcapU⟩ := hcap
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcapK⟩ := hcapU K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapK A hA26 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro a U1floor g ha ha1096 hg hU
  have hapos : 0 < a := ha
  have haR0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
  have hlogA : Real.log ((a : ℕ) : ℝ) ≤ 7 := by
    have he7 : (1096 : ℝ) ≤ Real.exp 7 := by
      have h3 : Real.exp 7 = (Real.exp 1) ^ (7 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have h4 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h5 : (2.7182818283 : ℝ) ^ (7 : ℕ) ≤ (Real.exp 1) ^ (7 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) h4.le 7
      have h6 : (1096 : ℝ) ≤ (2.7182818283 : ℝ) ^ (7 : ℕ) := by norm_num
      rw [h3]; linarith
    have haR : ((a : ℕ) : ℝ) ≤ 1096 := by exact_mod_cast ha1096
    calc Real.log ((a : ℕ) : ℝ) ≤ Real.log (Real.exp 7) := Real.log_le_log haR0 (by linarith)
      _ = 7 := Real.log_exp 7
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦THE ONE GENUINE ESTIMATE, SPENT AT SHIFT `h`⟧ the substituted
  -- `g' = s15ArmH h δ₀ ρ + g` still obeys the builder-side rider.  H1's re-cut prices the arm at
  -- `log ω + log h + H₊/10^20` (`s15ArmH_log_le`), the caller's own `ε²·H₊` margin is
  -- `≥ H₊/(250000·h²)` at `ε ≥ 1/(500·h)`, and H2a word 4's `xceil_arm_split_h` is exactly the
  -- statement that the margin pays for BOTH the arm's `log h` and the sum split's `log 2`.
  have hh1R : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hεR : (1 : ℝ) / (500 * (h : ℝ)) ≤ (ε : ℝ) := by
    have hq := (Rat.cast_le (K := ℝ)).mpr hεpin
    rwa [show (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) by
      push_cast; ring] at hq
  have hεpos : (0 : ℝ) < (ε : ℝ) := by
    have hb : (0 : ℝ) < 1 / (500 * (h : ℝ)) := by positivity
    linarith
  have hg' : XCeilRider ε
      (fun Hhi ω => a * (s15ArmH h δ₀ ρ Hhi ω + g Hhi ω)) := by
    intro Hhi ω hgate
    obtain ⟨hH4, hll, hωw⟩ := hgate
    have hHhiR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hH4
    -- ⟦THE MARGIN⟧ `ε ≥ 1/(500h) > 0` ⟹ `ε² ≥ 1/(250000h²)`
    have hε2 : (1 : ℝ) / (250000 * (h : ℝ) ^ 2) ≤ (ε : ℝ) ^ 2 := by
      have hsq : (1 : ℝ) / (500 * (h : ℝ)) * (1 / (500 * (h : ℝ))) ≤ (ε : ℝ) * (ε : ℝ) :=
        mul_le_mul hεR hεR (by positivity) (le_of_lt hεpos)
      have he : (1 : ℝ) / (500 * (h : ℝ)) * (1 / (500 * (h : ℝ)))
          = 1 / (250000 * (h : ℝ) ^ 2) := by
        have hne : (h : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      nlinarith [hsq, he.le, he.ge]
    have hεsq : ((Hhi : ℕ) : ℝ) / (250000 * (h : ℝ) ^ 2)
        ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := by
      have hH0 : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by positivity
      have hm := mul_le_mul_of_nonneg_right hε2 hH0
      calc ((Hhi : ℕ) : ℝ) / (250000 * (h : ℝ) ^ 2)
          = 1 / (250000 * (h : ℝ) ^ 2) * ((Hhi : ℕ) : ℝ) := by ring
        _ ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := hm
    -- ⟦THE ARM⟧ wave H1's re-cut, at the `h` lane's own `δ₀` pin
    have harm : Real.log ((s15ArmH h δ₀ ρ Hhi ω : ℕ) : ℝ)
        ≤ Real.log ((ω : ℕ) : ℝ) + Real.log (h : ℝ) + ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
      rw [hρdef, hδsdef]
      exact s15ArmH_log_le hh hh7 hδ₀ hδpin hKc hKcb hH4 hll
    -- ⟦H2a WORD 4⟧ the split, whose room is a tower against a constant
    have hsplit := xceil_arm_split_mul_h hh hh7 hH4 hll
    have hgb := hg Hhi ω ⟨hH4, hll, hωw⟩
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have harm' : Real.log ((s15ArmH h δ₀ ρ Hhi ω : ℕ) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - Real.log 2 - 7 := by linarith
    have hgb' : Real.log ((g Hhi ω : ℕ) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - Real.log 2 - 7 := by
      have hlogh : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_natCast_nonneg h
      have hH20 : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by positivity
      linarith
    have hsum : Real.log (((s15ArmH h δ₀ ρ Hhi ω + g Hhi ω : ℕ)) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - 7 :=
      le_trans (xt_log_add_le harm' hgb') (by linarith)
    -- ⟦THE MULTIPLIER⟧ `log(a·(arm + g)) = log a + log(arm + g) ≤ 7 + (31/ε·H₊ − 7)`
    have hprod : Real.log (((a * (s15ArmH h δ₀ ρ Hhi ω + g Hhi ω) : ℕ)) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos (a * (s15ArmH h δ₀ ρ Hhi ω + g Hhi ω)) with hz | hp
      · rw [hz]
        simp only [Nat.cast_zero, Real.log_zero]
        have hbig : (0 : ℝ) < 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) := by
          have : (0 : ℝ) < ((Hhi : ℕ) : ℝ) := by linarith
          positivity
        linarith
      · have hne : a * (s15ArmH h δ₀ ρ Hhi ω + g Hhi ω) ≠ 0 := hp.ne'
        have hsne : (0 : ℝ) < ((s15ArmH h δ₀ ρ Hhi ω + g Hhi ω : ℕ) : ℝ) := by
          have hs0 : 0 < s15ArmH h δ₀ ρ Hhi ω + g Hhi ω :=
            Nat.pos_of_ne_zero (fun hc => hne (by rw [hc, Nat.mul_zero]))
          exact_mod_cast hs0
        have hcast : (((a * (s15ArmH h δ₀ ρ Hhi ω + g Hhi ω) : ℕ)) : ℝ)
            = ((a : ℕ) : ℝ) * ((s15ArmH h δ₀ ρ Hhi ω + g Hhi ω : ℕ) : ℝ) := by
          push_cast; ring
        rw [hcast, Real.log_mul (ne_of_gt haR0) (ne_of_gt hsne)]
        linarith
    exact hprod
  obtain ⟨R, hReps, hU1, hRg, hstride, hRx, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl a U1floor (fun Hhi ω => s15ArmH h δ₀ ρ Hhi ω + g Hhi ω) ha ha1096 hg'
  have hRarm : s15ArmH h δ₀ ρ R.Hhi R.ω ≤ R.x := by
    have hstep : s15ArmH h δ₀ ρ R.Hhi R.ω
        ≤ a * (s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω) := by
      have h1 : s15ArmH h δ₀ ρ R.Hhi R.ω
          ≤ 1 * (s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω) := by omega
      exact le_trans h1 (Nat.mul_le_mul_right _ ha)
    omega
  have hRgg : a * g R.Hhi R.ω ≤ R.x := by
    have hstep : a * g R.Hhi R.ω
        ≤ a * (s15ArmH h δ₀ ρ R.Hhi R.ω + g R.Hhi R.ω) :=
      Nat.mul_le_mul_left a (by omega)
    omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hstride, hRx, hRtow, ?_⟩
  intro M hKw hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor hKw
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15ArmH_demoted h δ₀ ρ R.Hhi R.ω) hRarm
  have hhω : (0 : ℝ) ≤ (h : ℝ) * (R.ω : ℝ) := by positivity
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 ((h : ℝ) * (R.ω : ℝ)) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hhω ?_ hhi) (s15ArmH_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family at the inflated socket, arm read at `h·ω`
  have harith := s15_doorArithFrameRho_L_familyH'' (C₁ := fun _ : ℕ => (1 : ℝ)) hh hsel.hM
    hρ0 hρ1 hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧ — the register and its bridges are SOCKET-BLIND
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦slot 3⟧ H2a word 6's OUTER step, over the `h`-free family, with the `28` in the gate
  have hj0raw : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * max 1 (arcDen 12 H)) + 28 ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    have hgate := s13_g2_jfloor_of_MSelect'_L_gk_shift28 K (by linarith) hS
    have hbase := s13_g2_jfloor_gen (R := R)
      (F := ((doorRowFloorL M : ℕ) : ℝ) - 28) le_rfl (by linarith)
    intro H hlo hhi
    linarith [hbase H hlo hhi]
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_of_MSelect'_L_gk_h hh hh7 hj0raw)
    (s13_gate8_L_gk_h hh hh7 le_rfl (by linarith) hsel.gRows)
    (s13_smallGradeFits_of_halfWindow_L_gk_h hh hh7 hρ0 hρ1 hfl hsel.half)
    (fun H L q j A s hb => doorBaseFrame_at_socket_LH hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorLH_gk K hh hh7 hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flatH hh hh7 hfl hb hlam50 htow hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flatH hh hh7 hfl hb hρ0 hlam50 htow hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flatH hh hh7 hfl hb hρ0 hlam50 htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM
        (s15_block_at_socketH_L_gk K hh hh7 hb (hHreg H hb.1 hb.2.1) hsel.blk)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'H_L_gk K hh hh7 hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (s15ArmH_rho hRarm) harith hsel.x0M (fun _ => le_rfl) hgrade
      (fun H L q j A s hb =>
        s15_block_at_socketH_L_gk K hh hh7 hb (hHreg H hb.1 hb.2.1) hsel.blk))
    harith

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
    (_hband : S16BandLaneCBoundedLH_winU h Awin) (P : ChowlaRegime → Prop)
    (hcond : FlatConditionalFormH h Awin P) :
    FlatKswinFormH h Awin P := by
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, hcondU⟩ := hcond
  obtain ⟨_Ct0, -, -, hcond0⟩ := hcondU 0
  -- ⟦THE CROSSING CONSTANTS, HOISTED ABOVE THE LEVER⟧ — §11.4's windowed twin
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40,
    hsupplyU⟩ := s15_crossing_supplied_LH_gk_ceiling_sharpT0_khoist_csfree_kswin hh hh7
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond0 (max 162 (budgetAFlat (ε : ℝ) β)) (le_max_left _ _) (le_max_right _ _)
  -- the `ε`-probe's own `g ≡ 0` obeys the strict rider trivially (`log 0 = 0`, and the gate's
  -- width window already carries the `ε²·H₊` margin)
  have hzero : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := by
    intro Hhi ω hgate
    obtain ⟨-, -, hωw⟩ := hgate
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [Real.log_natCast_nonneg ω]
  obtain ⟨R0, hR0eps, -, -, -, -, -, -⟩ :=
    hbody0 1 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) le_rfl (by norm_num)
      hzero le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have hεR : (1 : ℝ) / (500 * (h : ℝ)) ≤ (ε : ℝ) := by
    have hq := (Rat.cast_le (K := ℝ)).mpr hεpin
    rwa [show (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) by
      push_cast; ring] at hq
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  have hsupply := hsupplyU K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA26 hAwin hAge hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge
  refine ⟨fun hopq => flat_witFloor_eq_designBase_h hh hh7 hA26 hβ hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hx0win hopq hT₀ hKsw U1floor hU hUceil a g ha ha1096 hg
  -- ⟦Δ3⟧ the caller's floor, and the three monotone lifts off `hU`
  have hWpos : (0 : ℝ) < Real.log ((flatWitFloor ε β A Hopq : ℕ) : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos _) (flatWitFloor_log_ge hA26)
  have hWposN : (0 : ℝ) < ((flatWitFloor ε β A Hopq : ℕ) : ℝ) := by
    rcases (Nat.cast_nonneg (flatWitFloor ε β A Hopq) : (0 : ℝ) ≤ _).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [← heq] at hWpos
      simp at hWpos
  have hUR : ((flatWitFloor ε β A Hopq : ℕ) : ℝ) ≤ ((U1floor : ℕ) : ℝ) := by exact_mod_cast hU
  have hUlog : Real.log ((flatWitFloor ε β A Hopq : ℕ) : ℝ)
      ≤ Real.log ((U1floor : ℕ) : ℝ) := Real.log_le_log hWposN hUR
  have hUll : Real.log (Real.log ((flatWitFloor ε β A Hopq : ℕ) : ℝ))
      ≤ Real.log (Real.log ((U1floor : ℕ) : ℝ)) := Real.log_le_log hWpos hUlog
  obtain ⟨R, hReps, hHlo, hRg, hstride, hRx, hRtow, hfire⟩ :=
    hbody a U1floor g ha ha1096 hg (le_trans (flatCap_le_flatWitFloor hCapLe) hU)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]
    exact le_trans (flatWitFloor_design ε β A Hopq) hUll
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo]; exact hUceil
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hstride, hRx, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  -- ⟦THE REGISTER, SUPPLIED⟧ at the flat design modulus
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have hhQ : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  have heps : (1 : ℚ) / (2 ^ 9 * (h : ℚ)) ≤ R.eps := by
    rw [hReps]
    have hle : (1 : ℚ) / (2 ^ 9 * (h : ℚ)) ≤ 1 / (500 * (h : ℚ)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [hhQ]
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact le_trans (flatWitFloor_log_ge hA26) hUlog
  -- ⟦THE BRIDGE⟧ the `A`-scoped window becomes §11.4's regime-scoped one at the flat floor
  have hKswR : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16 := by linarith
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win_h hA26 K hKw hh hh7 hδ₀ hδpin
    hKc hKcb hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win heps hlo hwin
  -- ⟦THE CROSSING, SUPPLIED⟧ the block floor off the register's own `blk` line
  have hfl : loglogFloor50 ≤ R.Hlo := by
    rw [hHlo]; exact le_trans (flatWitFloor_ll _ _ _ _) hU
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseLH h R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socketH_L_gk K hh hh7 hb
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hKw hsel
    (hsupply hKqb R (flatDoorM A) hM1 hfl hKswR
      (by
        rw [hHlo]
        refine le_trans hT₀ (Real.exp_le_exp.mpr ?_)
        have hs : Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ)
            ≤ Real.sqrt ((U1floor : ℕ) : ℝ) := Real.sqrt_le_sqrt hUR
        linarith)
      hblk hcof hcapsc)

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
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ :=
    cofkR_cofactorSupply_L_gk_rated_h h hh hh7
  obtain ⟨Awin, -, hband⟩ := s16_bandLaneWinLH_holdsU h hh
  -- ⟦THE cs-FREE, Ks-WINDOWED FLAT TERMINAL⟧ V7Ks §5
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ := hk Awin hband
  -- ⟦THE DESIGN CONSTANT, EIGHT ARMS⟧ the seven landed arms verbatim (`A'`), the eighth
  -- (`armVt Kvt`) outermost — every constant still minted BEFORE the lever: `Kvt` arrives at
  -- the supply obtain above, before the mint.
  obtain ⟨A', hA'def⟩ : ∃ a : ℝ, a = max (16 * Real.log (1 / Ks) / 3) (max T₀
      (max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
        (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))))) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (armVt Kvt) A' := ⟨_, rfl⟩
  have harmA : armVt Kvt ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hlift : A' ≤ A := by rw [hAdef]; exact le_max_right _ _
  have hKsA : 16 * Real.log (1 / Ks) / 3 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]; exact le_max_left _ _
  have hT₀A : T₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hA162 : (162 : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hA₀A : A₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAwinA : Awin ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_right (max (max A₀ 162) Awin)
      (cofkRThr Cq Cb Xsk Y0)) (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _)
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  -- ⟦THE `Ks` WINDOW, AT THE SEVENTH ARM⟧ as in the parent
  have hKswin : Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 := by linarith
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
    have h2 : Real.exp (3.2 * A) / 10 + 1 ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
      Real.add_one_le_exp _
    linarith
  have hopq : Hopq ≤ flatDesignBase A := by
    have h2 : Real.exp (3.2 * A) + 1 ≤ Real.exp (Real.exp (3.2 * A)) := Real.add_one_le_exp _
    have hR : ((Hopq : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by linarith
    have hceil := le_trans hR (Nat.le_ceil (Real.exp (Real.exp (3.2 * A))))
    rw [flatDesignBase]; exact_mod_cast hceil
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, hCt, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hKw
  -- ⟦THE `T₀` ARM⟧ V7-C's discharge, as in the parent
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A, ?_⟩
  -- ⟦Δ3⟧ the caller's floor and ceiling, forwarded into the kswin form
  intro U1floor a g hU hUceil ha ha1096 hg
  obtain ⟨R, hReps, hHlo, hRg, hstride, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKswin U1floor
      (by rw [hbase hopq]; exact hU) hUceil a g ha ha1096 hg
  -- ⟦THE BASE-SCALE CAP⟧ at `K = KlevF A`, as in the parent
  have heps500 : (1 : ℚ) / (500 * (h : ℚ)) ≤ R.eps := by rw [hReps]; exact hεpin
  have hxceil : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [hReps]; exact hRx
  -- ⟦THE RATED SUPPLY, WITH THE CUSHION PAID BY THE EIGHTH ARM⟧
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA26
  have heps500R : (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ) := by
    rw [hReps]
    have hq := (Rat.cast_le (K := ℝ)).mpr hεpin
    rwa [show (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) by
      push_cast; ring] at hq
  have h518 : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by nlinarith [hdes, hA162]
  have hfl : loglogFloor50 ≤ R.Hlo := by
    rw [hHlo]
    refine le_trans ?_ hU
    have hw := flatWitFloor_ll ε β A Hopq
    rwa [hbase hopq] at hw
  have hllreg := regime_Hfloor_of_loglogFloor50 hfl
  have hlogpos : (1 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hllreg.1 (by norm_num : (0 : ℝ) < 50) hllreg.2
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    have h1 := Real.exp_le_exp.mpr hdes
    rwa [Real.exp_log (by linarith)] at h1
  have hthrgate : cofkRThr Cq Cb Xsk Y0 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    linarith [hthrA, hlo, hexp1]
  have hKvtcush : 32 * Kvt
      + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
      ≤ Real.log (R.Hhi : ℝ) / 4 :=
    cofkR_cushion_of_armVt R hKvt0 harmA hlo
  have hcofsupply : S16CofactorSupply_LH_gk h (KlevF A) Cq R (flatDoorM A) :=
    hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush
  have hfireR : P R :=
    hfire2 hcofsupply
      (s16_baseScaleCap96_LH_at_klevF hh hh7 hA26 (flatDoorM_one_le hA26) heps500 hxceil hwin)
  exact ⟨R, hReps, hHlo, hRg, hstride, hRtow, hdes, hwin, hfireR⟩

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
theorem flat_door_head_xceil_h (h : ℕ) (hh : 0 < h) (_hh7 : Real.log (h : ℝ) ≤ 7)
    (Xi : XiFamily)
    (hcount : ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 539 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((Xi (1 / (500 * (h : ℚ))) H).card : ℝ) ≤ C) :
    FlatHeadFormH h Xi (MRTDoorReceiptSet h Xi) := by
  classical
  unfold FlatHeadFormH
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hhne : (h : ℝ) ≠ 0 := ne_of_gt hhR
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- ⟦THE LEAF NUMERALS, PINNED⟧ `log 4 = 2·log 2`, both `d9` bounds on `log 2`
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  obtain ⟨cD3, hcD3def⟩ : ∃ c : ℝ, c = 1 / 4 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ c : ℝ, c = (h : ℝ) * (1 + 2 * (2 * Real.log 4)) := ⟨_, rfl⟩
  have hcD3 : 0 < cD3 := by rw [hcD3def]; norm_num
  have hLpos : (0 : ℝ) < 1 + 8 * Real.log 2 := by linarith
  have hLne : (1 : ℝ) + 8 * Real.log 2 ≠ 0 := ne_of_gt hLpos
  have hCval : C = (h : ℝ) * (1 + 8 * Real.log 2) := by rw [hCdef, hlog4eq]; ring
  have hC : 0 < C := by rw [hCval]; positivity
  -- ⟦THE PIN⟧ `ε := 1/(500·h)`
  obtain ⟨ε, hεdef⟩ : ∃ e : ℚ, e = 1 / (500 * (h : ℚ)) := ⟨_, rfl⟩
  have hεR : ((ε : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) := by rw [hεdef]; push_cast; ring
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by rw [hεR]; positivity
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεQ1 : ε ≤ 1 / 2 := by
    have hhQ : (1 : ℚ) ≤ (h : ℚ) := by exact_mod_cast hh
    rw [hεdef]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  -- ⟦THE MINT, READ BOTH WAYS⟧ `δ₀ = 1/(128000·h²·(1 + 8·log 2))`
  have hval : cD3 / (16 * C) * (ε : ℝ) / 4
      = 1 / (128000 * (h : ℝ) ^ 2 * (1 + 8 * Real.log 2)) := by
    rw [hcD3def, hCval, hεR]
    field_simp
    ring
  have hsq0 : (0 : ℝ) ≤ (h : ℝ) ^ 2 := sq_nonneg _
  have hδ₀ge : (1 : ℝ) / (838400 * (h : ℝ) ^ 2) ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    rw [hval]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hnum : 128000 * (1 + 8 * Real.log 2) ≤ 838400 := by linarith
    nlinarith [hnum, hsq0]
  have hδ₀le : cD3 / (16 * C) * (ε : ℝ) / 4 ≤ 1 / (837782 * (h : ℝ) ^ 2) := by
    rw [hval]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hnum : (837782 : ℝ) ≤ 128000 * (1 + 8 * Real.log 2) := by linarith
    nlinarith [hnum, hsq0]
  -- ⟦THE COUNT HOOK AT THE PIN⟧ carrying `K ≤ 2^539`
  obtain ⟨K, hK, hKb, H₀xi, _hH₀xi2, hxi⟩ := hcount
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = cD3 * (ε : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hcD3 hεR0) (by positivity)
  -- ⟦THE HEAD'S OWN FLOOR⟧ the count hook's alone — the door-head has no tail
  obtain ⟨Hopq, hOpqdef⟩ : ∃ n : ℕ, n = H₀xi := ⟨_, rfl⟩
  refine ⟨ε, K, cD3 / (16 * C) * (ε : ℝ) / 4, β, Hopq, hεQpos, hK, hKb,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num),
    hεdef.ge, hδ₀ge, hβpos, ?_⟩
  -- ⟦THE HOIST⟧ as in the head
  intro A hA26 _hAge
  obtain ⟨F, hFdef⟩ : ∃ n : ℕ, n = max Hopq (budgetFloorFlat (ε : ℝ) β A) := ⟨_, rfl⟩
  refine ⟨max (flatDesignFloor A) (max F (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), by rw [hFdef], ?_⟩
  intro a extraFloor U1floor g₅ ha ha1096 hg₅
  obtain ⟨Rf, hReps, _hRA, hRHlo, hRg, hstride, _hRcapEq, hRwid, hRx⟩ :=
    chowlaRegimeFlat_exists_param_head_xceil_mul a ha ha1096 A hA26 ε hεQpos hεQ1
      (max F (max extraFloor U1floor)) g₅ hg₅
  have hFlo : F ≤ Rf.Hlo := le_trans (le_max_left _ _) hRHlo
  have hxiHlo : H₀xi ≤ Rf.Hlo := by
    rw [hFdef, hOpqdef] at hFlo
    exact le_trans (le_max_left _ _) hFlo
  -- ⟦THE COUNT GATE⟧ at this head's own `ε`, reused for the receipt's own conjunct
  have hcountR : ∀ (H' : ℕ) [NeZero H'], Rf.Hlo ≤ H' → H' ≤ Rf.Hhi →
      ((Xi Rf.eps H').card : ℝ) ≤ K := by
    intro H' _ hlo' _
    rw [hReps, hεdef]
    exact hxi H' (le_trans hxiHlo hlo')
  refine ⟨Rf.toChowlaRegime, hReps,
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, hstride, hRx,
    hcountR, fun _ => hRwid, ?_, ?_⟩
  · -- ⟦THE CAP⟧ the flat base equation, shuffled onto the consumer's floors
    rw [_hRcapEq]
    exact flatCapH_shuffle _ _ _ _ _
  · -- ⟦THE DOOR, HANDED OUT INSTEAD OF SPENT⟧ with the pin and the count beside it
    intro ρ hρpos hρ hdoor
    exact ⟨by rw [hReps, hεdef], ⟨K, hK, hKb, hcountR⟩, ρ, hρpos,
      le_trans hρ hδ₀le, hdoor⟩

/-- **⟦THE CHAIN⟧ (class A).**  H0 ∘ … ∘ H5 at `h`, generic in `P` and `Xi`:
`flat_v7_generic_h h hh hh7 P (fun Awin hband => flat_kswin_generic_h … (flat_conditional_generic_h
… (flat_capstone_generic_h … (flat_roadExit_generic_h h hh hh7 Xi harcXi P hhead)))) A₀`. -/
theorem flat_chain_generic_h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) (Xi : XiFamily)
    (harcXi : ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
      ∀ ξ ∈ Xi eps H, NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (P : ChowlaRegime → Prop) (hhead : FlatHeadFormH h Xi P) (A₀ : ℝ) :
    V7RatedFormH h P A₀ := by
  exact flat_v7_generic_h h hh hh7 P
    (fun Awin hband => flat_kswin_generic_h h hh hh7 Awin hband P
      (flat_conditional_generic_h h hh hh7 Awin hband P
        (flat_capstone_generic_h h hh hh7 Awin hband P
          (flat_roadExit_generic_h h hh hh7 Xi harcXi P hhead)))) A₀

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
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hεpin, -, -, -, hA162, hA₀A, hbody⟩ :=
    flat_chain_generic_h h hh hh7 Xi harcXi (MRTDoorReceiptSet h Xi)
      (flat_door_head_xceil_h h hh hh7 Xi hcount) A₀
  -- ⟦THE ε-PIN EQUALITY⟧ read off `P R` at the TRIVIAL instantiation
  have hεeq : ε = 1 / (500 * (h : ℚ)) := by
    obtain ⟨R0, hR0eps, -, -, -, -, -, -, hP0⟩ :=
      hbody (flatDesignBase A) 1 (fun _ _ => 0) le_rfl (flatDesignBase_loglog_le hA162)
        le_rfl (by norm_num) (xceilRiderStrict_zero ε)
    rw [← hR0eps]
    exact hP0.1
  refine ⟨ε, A, hε, hεpin, hεeq, hA162, hA₀A, ?_⟩
  intro U1floor a g hU hUceil ha ha1096 hg
  obtain ⟨R, hReps, hHlo, hRg, hstride, -, hdes, hwin, hP⟩ :=
    hbody U1floor a g hU hUceil ha ha1096 hg
  obtain ⟨-, hcountR, ρ, hρpos, hρle, hdoor⟩ := hP
  exact ⟨R, hReps, hHlo, hRg, hstride, hdes, hwin, hcountR, ρ, hρpos, hρle, hdoor⟩

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
  obtain ⟨ε, A, hε, hεpin, -, hA162, hA₀A, hbody⟩ :=
    mrtUniformityXiL2Set_holds_flat_floor h hh hh7 (fun eps H _ => bigXiH h eps H)
      (fun eps heps => nearRatTight_of_bigXiArcTight_H bigXiArcTight_twelve heps hh)
      (bigXiH_bounded_ceiling_of_pin h hh hh7 _ rfl) A₀
  obtain ⟨R, hReps, hHlo, -, -, hdes, -, -, ρ, hρpos, hρle, hdoor⟩ :=
    hbody (flatDesignBase A) 1 (fun _ _ => 0) le_rfl (flatDesignBase_loglog_le hA162) le_rfl
      (by norm_num) (xceilRiderStrict_zero ε)
  refine ⟨ε, A, hε, hεpin, hA162, hA₀A, R, hReps, hHlo, hdes, ρ, hρpos, hρle, ?_⟩
  rw [← mrtUniformityXiL2Set_bigXiH_eq h R ρ]
  exact hdoor

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
  have hkpos : 0 < a * h := Nat.mul_pos ha hh
  refine mrtUniformityXiL2Set_holds_flat_floor (a * h) hkpos hah7
    (fun eps H _ => bigXiAffD a b h eps H)
    (fun eps heps => nearRatTight_of_bigXiAffD bigXiArcTight_twelve heps ha hh) ?_ A₀
  obtain ⟨Cc, hCc, hCcb, H₀, hH₀2, hcard⟩ :=
    bigXiAff_bounded_ceiling_of_pin a b h ha hh hah7 _ rfl
  refine ⟨Cc, hCc, hCcb, H₀, hH₀2, ?_⟩
  intro H _ hH
  refine le_trans ?_ (hcard H hH)
  exact_mod_cast bigXiAffD_card_le a b h _ H

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
  have hapos : 0 < a := ha
  have hkpos : 0 < a * h := Nat.mul_pos ha hh
  have hah1096 : a * h ≤ 1096 :=
    Salt.Entropy.Chowla.h_le_1096_of_log_le_seven hkpos hah7
  have haah : a ≤ a * h := Nat.le_mul_of_pos_right a hh
  have ha1096 : a ≤ 1096 := le_trans haah hah1096
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
  have hloga7 : Real.log ((a : ℕ) : ℝ) ≤ 7 := by
    refine le_trans (Real.log_le_log haR (by exact_mod_cast haah)) hah7
  -- ⟦THE RECEIPT AT THE AFFINE SET⟧ at the caller's floor `a · flatDesignBase A`
  obtain ⟨ε, A, hε, hεpin, hεeq, hA162, hA₀A, hbody⟩ :=
    mrtUniformityXiL2AffSet_holds_flat_floor a b h ha hh hah7 A₀
  have hU : flatDesignBase A ≤ a * flatDesignBase A := Nat.le_mul_of_pos_left _ hapos
  have hUceil := loglog_mul_flatDesignBase_le hA162 ha hloga7
  obtain ⟨Rd, hReps, hHlo, -, hstride, -, -, hcountD, ρ, hρpos, hρle, hdoor⟩ :=
    hbody (a * flatDesignBase A) a (fun _ _ => 0) hU hUceil ha ha1096
      (xceilRiderStrict_zero ε)
  obtain ⟨Kc, hKc0, hKcb, hKcount⟩ := hcountD
  -- ⟦THE ε PINS⟧ the receipt's own EQUALITY, read both ways
  have hahQ : ((a * h : ℕ) : ℚ) ≤ 1096 := by exact_mod_cast hah1096
  have hahQ1 : (1 : ℚ) ≤ ((a * h : ℕ) : ℚ) := by exact_mod_cast hkpos
  have heps500 : Rd.eps ≤ 1 / 500 := by
    rw [hReps, hεeq]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have heps548 : (1 : ℚ) / 548000 ≤ Rd.eps := by
    rw [hReps, hεeq]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  -- ⟦THE SHRINK'S THREE FLOORS⟧ off `flatDesignBase_clears_stride_floors`
  have hdiv : a ∣ Rd.a * Rd.Hlo := by
    rw [hHlo]
    exact (dvd_mul_right a (flatDesignBase A)).mul_left Rd.a
  have hquot : Rd.a * Rd.Hlo / a = Rd.a * flatDesignBase A := by
    rw [hHlo, show Rd.a * (a * flatDesignBase A) = a * (Rd.a * flatDesignBase A) by ring]
    exact Nat.mul_div_cancel_left _ hapos
  have hBle : flatDesignBase A ≤ Rd.a * Rd.Hlo / a := by
    rw [hquot]
    exact Nat.le_mul_of_pos_left _ Rd.ha
  obtain ⟨hf1, hf2⟩ := flatDesignBase_clears_stride_floors hA162 heps548
  have hlo4 : 4 * ⌈(1 / Rd.eps : ℚ)⌉₊ ^ 4 ≤ Rd.a * Rd.Hlo / a := le_trans hf1 hBle
  have hloM : 4000000 ≤ Rd.a * Rd.Hlo / a := le_trans hf2 hBle
  have hb : b ≤ (regimeShrinkX_stride Rd a ha ha1096 heps500 hstride hdiv hlo4 hloM).Hlo := by
    rw [regimeShrinkX_stride_Hlo]
    omega
  -- ⟦THE WIDTH NUMERAL⟧ `log ω ≥ 32001` off `hωbig` at `ε ≤ 1/500`
  have hepsR0 : (0 : ℝ) < (Rd.eps : ℝ) := by exact_mod_cast Rd.heps
  have heps500R : (Rd.eps : ℝ) ≤ 1 / 500 := by
    have hq := (Rat.cast_le (K := ℝ)).mpr heps500
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at hq
    exact hq
  have hcop : (2 : ℝ) ≤ (Rd.eps : ℝ) ^ 2 * ((Rd.Hlo : ℕ) : ℝ) := by
    have hQ : ((Rd.a : ℕ) : ℚ) ≤ Rd.eps ^ 2 * ((Rd.Hlo : ℕ) : ℚ) / 2 := Rd.hcoprime
    have ha1 : (1 : ℚ) ≤ ((Rd.a : ℕ) : ℚ) := by exact_mod_cast Rd.ha
    have hQ2 : (2 : ℚ) ≤ Rd.eps ^ 2 * ((Rd.Hlo : ℕ) : ℚ) := by linarith
    exact_mod_cast hQ2
  have hHmono : (Rd.eps : ℝ) ^ 2 * ((Rd.Hlo : ℕ) : ℝ)
      ≤ (Rd.eps : ℝ) ^ 2 * ((Rd.Hhi : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast Rd.hHlohi) (sq_nonneg _)
  have hlognn : (0 : ℝ) ≤ Real.log ((Rd.eps : ℝ) ^ 2 * ((Rd.Hhi : ℕ) : ℝ)) :=
    Real.log_nonneg (by linarith)
  have h16 : (0 : ℝ) ≤ 16 / (Rd.eps : ℝ) := by positivity
  have h64 : (32000 : ℝ) ≤ 64 / (Rd.eps : ℝ) := by
    rw [le_div_iff₀ hepsR0]; linarith
  have hlogω : (32001 : ℝ) ≤ Real.log ((Rd.ω : ℕ) : ℝ) := by
    have hb2 := Rd.hωbig
    nlinarith [mul_nonneg h16 hlognn]
  have hω2N : 2 ≤ Rd.ω := Rd.hω
  have hωR : (0 : ℝ) < ((Rd.ω : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((Rd.ω : ℕ) : ℝ) := by exact_mod_cast hω2N
    linarith
  have hω8 : 8 ≤ Rd.ω := by
    have hsub := Real.log_le_sub_one_of_pos hωR
    have h8 : (8 : ℝ) ≤ ((Rd.ω : ℕ) : ℝ) := by linarith
    exact_mod_cast h8
  -- ⟦THE TRANSPORT⟧ F3-P16 at the shrunk regime
  have htrans := mrtUniformityXiL2AffW_of_set h Rd a b ha ha1096 heps500 hstride hdiv hlo4
    hloM hb hω8 Kc ρ hKcount hdoor
  -- ⟦THE TWO MEASUREMENTS⟧ F3-P17 on the ratio, F3-P18 on the endpoint
  have hx2 : 2 ≤ Rd.x / a := hstride.2.1
  have hωx2 : Rd.ω ≤ Rd.x / a := hstride.2.2.1
  have hratio := strideZRatio_le Rd.x (Rd.x / a) Rd.ω Rd.hx hx2 hω2N Rd.hωx hωx2
    (by linarith)
  have hZlo := (harmonic_window_bounds hx2 hω2N hωx2).1
  have hDpos : (0 : ℝ) < (a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1 := by positivity
  have hLpos : (0 : ℝ) < Real.log ((Rd.ω : ℕ) : ℝ) - 1 := by linarith
  have hEnd0 := strideEndpoint_le Kc (a : ℝ)
    (∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹) (Rd.x / a / Rd.ω) Rd.ω
    hKc0.le (Nat.cast_nonneg a) (by linarith) hZlo
  have hnum : Kc * (a : ℝ) ≤ 2 ^ 539 * (a : ℝ) :=
    mul_le_mul_of_nonneg_right hKcb (Nat.cast_nonneg a)
  have hEnd1 : Kc * (a : ℝ)
        / (((a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1) * (Real.log ((Rd.ω : ℕ) : ℝ) - 1))
      ≤ 2 ^ 539 * (a : ℝ)
        / (((a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1) * (Real.log ((Rd.ω : ℕ) : ℝ) - 1)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (mul_pos hDpos hLpos).le)
  -- ⟦THE PACKAGE⟧ the grade at the slack binder, the endpoint NAMED
  refine ⟨ε, A, hε, hεpin, hεeq, hA162, hA₀A,
    ChowlaRegimeAff.ofRegime
      (regimeShrinkX_stride Rd a ha ha1096 heps500 hstride hdiv hlo4 hloM) b hb,
    rfl, rfl, hReps, ?_, ?_, ρ, 1.02,
    2 ^ 539 * (a : ℝ)
      / (((a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1) * (Real.log ((Rd.ω : ℕ) : ℝ) - 1)),
    hρpos, hρle, by norm_num, by norm_num, by positivity, le_rfl, ?_⟩
  · exact hBle
  · -- ⟦THE DESIGN LAW AT THE SHRUNK BASE⟧ off `flatDesignBase`'s own ceiling
    have hDge : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
      rw [flatDesignBase]; exact Nat.le_ceil _
    have hRaR : ((flatDesignBase A : ℕ) : ℝ) ≤ ((Rd.a * Rd.Hlo / a : ℕ) : ℝ) := by
      exact_mod_cast hBle
    have h1 : Real.exp (Real.exp (3.2 * A)) ≤ ((Rd.a * Rd.Hlo / a : ℕ) : ℝ) :=
      le_trans hDge hRaR
    have h2 : Real.exp (3.2 * A) ≤ Real.log ((Rd.a * Rd.Hlo / a : ℕ) : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h
    have h3 : 3.2 * A ≤ Real.log (Real.log ((Rd.a * Rd.Hlo / a : ℕ) : ℝ)) := by
      have h := Real.log_le_log (Real.exp_pos _) h2
      rwa [Real.log_exp] at h
    exact h3
  · -- ⟦THE GRADE⟧ the transport's literal grade, monotone up to the binder's
    refine mrtUniformityXiL2AffW_mono h _ htrans ?_
    have hρ0 : (0 : ℝ) ≤ ρ := hρpos.le
    have hratmul : (a : ℝ)
        * ((∑ n ∈ Finset.Ioc (Rd.x / Rd.ω) Rd.x, (n : ℝ)⁻¹)
            / (∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹)) * ρ
        ≤ (a : ℝ) * 1.02 * ρ := by
      have hmul := mul_le_mul_of_nonneg_left hratio haR.le
      nlinarith [hmul, hρ0, haR]
    linarith [hratmul, hEnd0, hEnd1]

end Salt.MR
