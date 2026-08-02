/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16BudgetFlat
import Salt.MR.HloExportMRFlatRoot

/-!
# THE FLAT TERMINAL — the third face at HEIGHT 2, and the price of the last step

⟦WHAT THIS FILE SETTLES⟧  After `S16Budget.logChowla2_witnessed_scale_final'_v3`
exactly one numeral rider of the terminal was still false at the chain's own
witness: `Hcap ≤ s15WitFloor2`, the wall's THIRD FACE, whose landed value is the
HEIGHT-3 tower `budgetFloor ε β = ⌈e^{e^{e^{X}}}⌉₊`.  The ratified flat road
(FLAT-REF, built by W0–W3) replaces that road's head by
`HloExportFlat.log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat`, whose
cap is

```
Hcap = max (flatDesignFloor A) (max (max Hopq (budgetFloorFlat ε β A)) (4·⌈1/ε⌉₊⁴))
```

`budgetFloorFlat` is HEIGHT 1 (`⌈e^{max (4X) (2 log A + 2)}⌉₊`) — that arm of the
wall is gone.  What survives is `flatDesignFloor A`, whose binding arm is
`flatDesignBase A = ⌈e^{e^{3.2·A}}⌉₊`: the price of the flat regime's own DESIGN
LAW `3.2·A ≤ loglog H₋`.  So the third face drops from height 3 to **height 2**,
and the residue is no longer a missing exponential but a NUMBER — the design
constant `A`.

⟦§1 — THE PRICE, EXACT⟧  `s15WitFloor2 = ⌈e^{2^{400}}⌉₊` is height 1, so
`flatDesignFloor A ≤ s15WitFloor2` holds **iff** `3.2·A ≲ 400·log 2 = 277.26`
(`flat_design_window_necessary` is the converse of the landed
`flatDesignFloor_le_s15WitFloor2`).  The flat head must take
`A ≥ budgetAFlat ε β = 2304·log 4/(ε⁶β²)` (`budget_factsFlat` (iv)), and its own
`β` is the AM–GM shell split `β = cD3·ε/(144·log 4)`
(`SpineFlat.hbudget1_witness_flatKappa`), so the window is a demand on the LEAF
CONSTANTS alone.  `flat_window_forces_cD3` prices it: the flat cap clears
`s15WitFloor2` only if the Mertens leaf constant satisfies `cD3 ≥ 19000`.
`HeadPinLeaves.primeWindow_sum_inv_ge_bounded` supplies `cD3 = 1/4`.  **So the
rider is still false at the chain's own witness — by a factor `7.7·10⁴` in `cD3`,
i.e. `A ≈ 8·10³⁰` against the window's `86.6` — and NOT by a missing
exponential.**  That is the whole content of the flat road's arrival, stated so
the kernel checks it.

⟦§2 — WHAT THE FLAT ROAD DOES DISCHARGE⟧  The rider was never intrinsic: it
exists because the LANDED register pins the base at `s15WitFloor2`.  Pinned at
its OWN cap the flat road needs no rider at all: `flatWitFloor` is the road's cap
joined with the two register floors, and `flatCap_le_flatWitFloor` discharges the
base pin unconditionally.  `flatWitFloor_design` is the non-vacuity — the design
law survives the join, so the pinned base is a legal flat base.

⟦§3 — THE REGISTER, AND WHY IT IS THE NEXT WALL⟧  Pinning at `flatWitFloor`
costs the S15 register: it reads `λ₋ ≤ 277.2589` (`s15WitFloor2_loglog_le`) and
the flat base has `λ₋ ≥ 3.2·A`.  `flat_base_breaks_s15_window` is that collision,
in one line.  So `S15Sel''_gk` cannot be PRODUCED on the flat road at the landed
frame constants; it is CARRIED by the flat terminal instead, and named.

**PURELY ADDITIVE.**  No landed declaration is touched.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE PRICE OF THE THIRD FACE ON THE FLAT ROAD -/

/-- **THE FLAT DESIGN CONSTANT'S SPEND, AS AN IDENTITY.**  `budget_factsFlat`'s
fact (iv) is `2304·log 4 ≤ A·β²·ε⁶`, and `budgetAFlat` is by definition the least
`A` clearing it — so the product is exactly the demand. -/
theorem budgetAFlat_spend {ε β : ℝ} (hε : ε ≠ 0) (hβ : β ≠ 0) :
    budgetAFlat ε β * (ε ^ 6 * β ^ 2) = 2304 * Real.log 4 := by
  rw [budgetAFlat]
  field_simp

/-- **THE DESIGN WINDOW, AS A DEMAND ON THE BUDGET PAIR.**  If the flat design
constant fits under the compose's witness exponent (`3.2·A ≤ 400·log 2 + 1`), the
budget pair `ε⁶β²` must exceed `36`.  The demand is scale-free: no floor, no
tower, no `H` — just the two spine constants. -/
theorem flat_design_window_demand {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β)
    (h : 3.2 * budgetAFlat ε β ≤ 400 * Real.log 2 + 1) :
    36 ≤ ε ^ 6 * β ^ 2 := by
  have hP : (0 : ℝ) < ε ^ 6 * β ^ 2 := by positivity
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hid : budgetAFlat ε β * (ε ^ 6 * β ^ 2) = 2304 * Real.log 4 :=
    budgetAFlat_spend (ne_of_gt hε) (ne_of_gt hβ)
  have hmul : 3.2 * budgetAFlat ε β * (ε ^ 6 * β ^ 2)
      ≤ (400 * Real.log 2 + 1) * (ε ^ 6 * β ^ 2) :=
    mul_le_mul_of_nonneg_right h hP.le
  have hlhs : 3.2 * budgetAFlat ε β * (ε ^ 6 * β ^ 2) = 3.2 * (2304 * Real.log 4) := by
    rw [← hid]; ring
  rw [hlhs, hl4] at hmul
  nlinarith [hmul, hl2lo, hl2hi, hP]

/-- **THE HEAD'S OWN BUDGET PAIR.**  The flat head does not choose `β` freely:
`SpineFlat.hbudget1_witness_flatKappa` fixes it at the AM–GM shell split
`β = cD3·ε/(144·log 4)`, so the pair is `cD3²·ε⁸/(144·log 4)²`. -/
theorem flatHead_budget_pair {ε cD3 : ℝ} (h4 : Real.log 4 ≠ 0) :
    ε ^ 6 * (cD3 * ε / (144 * Real.log 4)) ^ 2
      = cD3 ^ 2 * ε ^ 8 / (144 * Real.log 4) ^ 2 := by
  field_simp

/-- **⟦THE PRICE⟧ THE FLAT DESIGN WINDOW FORCES A MERTENS CONSTANT THE CHAIN DOES
NOT HAVE.**  At the head's own `β` and any spine `ε ≤ 1/2`, `3.2·A ≤ 400·log 2 + 1`
forces `cD3 ≥ 19000`.  `HeadPinLeaves.primeWindow_sum_inv_ge_bounded` supplies
`cD3 = 1/4`: the gap is a factor `7.7·10⁴` in `cD3`, equivalently `A ≈ 8·10³⁰`
against the window's `86.6`.

⟦WHY THIS IS THE HONEST STATEMENT⟧ `cD3` is an OPAQUE existential constant of the
chain (only `1/4 ≤ cD3` is exported), so "the rider is false" is not a kernel
theorem — it is a statement about the chain's own witness, exactly like the three
riders `REPAIRS-LANE` re-cut.  What IS a kernel theorem is the price: this. -/
theorem flat_window_forces_cD3 {ε cD3 : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hc : 0 < cD3)
    (h : 3.2 * budgetAFlat ε (cD3 * ε / (144 * Real.log 4)) ≤ 400 * Real.log 2 + 1) :
    19000 ≤ cD3 := by
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hl4pos : (0 : ℝ) < Real.log 4 := by rw [hl4]; linarith
  have hβ : (0 : ℝ) < cD3 * ε / (144 * Real.log 4) := by positivity
  have hP := flat_design_window_demand hε hβ h
  rw [flatHead_budget_pair (ne_of_gt hl4pos)] at hP
  have hD : (0 : ℝ) < (144 * Real.log 4) ^ 2 := by positivity
  have hP' : 36 * (144 * Real.log 4) ^ 2 ≤ cD3 ^ 2 * ε ^ 8 := by
    rw [le_div_iff₀ hD] at hP; linarith
  -- `ε^8 ≤ 1/256`
  have hε8 : ε ^ 8 ≤ 1 / 256 := by
    have h2 : ε ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [sq_nonneg ε, sq_nonneg (ε ^ 2), sq_nonneg (ε ^ 4), pow_nonneg hε.le 4,
      pow_nonneg hε.le 6]
  -- `(144·log 4)^2 ≥ 39850`
  have hD' : (39850 : ℝ) ≤ (144 * Real.log 4) ^ 2 := by
    have : (199.62 : ℝ) ≤ 144 * Real.log 4 := by rw [hl4]; linarith
    nlinarith [this]
  have hsq : (367264000 : ℝ) ≤ cD3 ^ 2 := by
    have hstep : 36 * (39850 : ℝ) ≤ cD3 ^ 2 * ε ^ 8 := by linarith [hP', hD']
    nlinarith [hstep, hε8, sq_nonneg cD3, pow_nonneg hε.le 8]
  nlinarith [hsq, hc]

set_option exponentiation.threshold 4000 in
/-- **THE DESIGN WINDOW IS NECESSARY** — the converse of the landed
`flatDesignFloor_le_s15WitFloor2`.  `s15WitFloor2 = ⌈e^{2^{400}}⌉₊` is a SINGLE
exponential and `flatDesignBase A = ⌈e^{e^{3.2A}}⌉₊` is a double one, so the only
way the flat cap fits under the witness floor is for `e^{3.2A}` to fit under the
witness EXPONENT. -/
theorem flat_design_window_necessary {A : ℝ} (h : flatDesignBase A ≤ s15WitFloor2) :
    3.2 * A ≤ 400 * Real.log 2 + 1 := by
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h1 : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    rw [flatDesignBase]; exact Nat.le_ceil _
  have h2 : ((flatDesignBase A : ℕ) : ℝ) ≤ ((s15WitFloor2 : ℕ) : ℝ) := by exact_mod_cast h
  have hpos : (0 : ℝ) < ((s15WitFloor2 : ℕ) : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos _) (le_trans h1 h2)
  have h3 : Real.exp (Real.exp (3.2 * A)) ≤ Real.exp ((2 : ℝ) ^ 400 + 1) := by
    calc Real.exp (Real.exp (3.2 * A)) ≤ ((s15WitFloor2 : ℕ) : ℝ) := le_trans h1 h2
      _ = Real.exp (Real.log ((s15WitFloor2 : ℕ) : ℝ)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp ((2 : ℝ) ^ 400 + 1) := Real.exp_le_exp.mpr s15WitFloor2_log_le
  have h4 : Real.exp (3.2 * A) ≤ (2 : ℝ) ^ 400 + 1 := Real.exp_le_exp.mp h3
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (400 : ℕ) := one_le_pow₀ (by norm_num)
  have hpow : (2 : ℝ) ^ (401 : ℕ) = Real.exp (401 * Real.log 2) := by
    rw [show (401 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ (401 : ℕ)) by
      rw [Real.log_pow]; norm_num]
    exact (Real.exp_log (by positivity)).symm
  have hsplit : (2 : ℝ) ^ (401 : ℕ) = 2 * (2 : ℝ) ^ (400 : ℕ) := by
    rw [show (401 : ℕ) = 400 + 1 by norm_num, pow_succ]; ring
  have h6 : Real.exp (3.2 * A) ≤ Real.exp (401 * Real.log 2) := by
    rw [← hpow, hsplit]; linarith
  have h7 : 3.2 * A ≤ 401 * Real.log 2 := Real.exp_le_exp.mp h6
  linarith

/-- **⟦THE THIRD FACE, PRICED⟧** — the flat road's cap clears the compose's
witness floor ONLY IF the Mertens leaf constant is `≥ 19000`.  Composition of
`flat_design_window_necessary` (the height-2 arm against the height-1 target) with
`flat_window_forces_cD3` (the leaf-constant price).

This is the exact statement of what the flat tower bought and what it did not:
the wall's third face is no longer an extra exponential, it is the number
`3.2·A ≈ 2.5·10³¹` against the register's `277.26`. -/
theorem flatCap_le_s15WitFloor2_forces_cD3 {ε cD3 A : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hc : 0 < cD3) (hA : budgetAFlat ε (cD3 * ε / (144 * Real.log 4)) ≤ A)
    (h : flatDesignFloor A ≤ s15WitFloor2) : 19000 ≤ cD3 := by
  have hbase : flatDesignBase A ≤ s15WitFloor2 :=
    le_trans (flatDesignBase_le_flatDesignFloor A) h
  have hwin : 3.2 * A ≤ 400 * Real.log 2 + 1 := flat_design_window_necessary hbase
  exact flat_window_forces_cD3 hε hε2 hc (by linarith [hA, hwin])

/-! ## §2 — THE FLAT WITNESS FLOOR: the base pin the flat road CAN take -/

/-- **THE FLAT WITNESS FLOOR** — the flat road's own cap joined with the two
register floors `arcFloor36` and `loglogFloor50`.  This is `s15WitFloor2`'s role
played by the flat data itself: pinned here, the road needs NO cap rider. -/
def flatWitFloor (ε : ℚ) (β A : ℝ) (Hopq : ℕ) : ℕ :=
  max (max (flatDesignFloor A)
      (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)))
    (max arcFloor36 loglogFloor50)

theorem flatWitFloor_arc (ε : ℚ) (β A : ℝ) (Hopq : ℕ) :
    arcFloor36 ≤ flatWitFloor ε β A Hopq :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem flatWitFloor_ll (ε : ℚ) (β A : ℝ) (Hopq : ℕ) :
    loglogFloor50 ≤ flatWitFloor ε β A Hopq :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-- **⟦THE CAP DISCHARGE — THE POINT OF THE FLAT ROAD⟧** the witness floor clears
the flat head's floor, UNCONDITIONALLY.  This is the `Hcap ≤ s15WitFloor2` rider's
replacement: on the flat road it is a theorem, not a hypothesis, because the base
pin is taken at the road's own cap. -/
theorem flatCap_le_flatWitFloor {ε : ℚ} {β A : ℝ} {Hcap Hopq : ℕ}
    (h : Hcap ≤ max (flatDesignFloor A)
      (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4))) :
    max Hcap (max arcFloor36 loglogFloor50) ≤ flatWitFloor ε β A Hopq :=
  max_le (le_trans h (le_max_left _ _)) (le_max_right _ _)

/-- **THE NON-VACUITY** — the flat design law survives the join, so the pinned
base is a legal flat base (`flatDesignFloor_design_max` twice through the
`max`-lattice).  `A` is symbolic throughout. -/
theorem flatWitFloor_design (ε : ℚ) (β A : ℝ) (Hopq : ℕ) :
    3.2 * A ≤ Real.log (Real.log ((flatWitFloor ε β A Hopq : ℕ) : ℝ)) := by
  have hle : flatDesignFloor A ≤ flatWitFloor ε β A Hopq :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hEq : max (flatDesignFloor A) (flatWitFloor ε β A Hopq) = flatWitFloor ε β A Hopq :=
    max_eq_right hle
  have h := flatDesignFloor_design_max A (flatWitFloor ε β A Hopq)
  rwa [hEq] at h

/-- **THE HEIGHT-2 ENVELOPE.**  Every named arm of the flat witness floor is a
`⌈e^·⌉₊` whose exponent is either a constant, a single `exp`, or the height-1
budget exponent — so the whole floor sits under `⌈e^T⌉₊` joined with the road's
opaque arm and the two register floors.  The landed `budgetFloor ε β =
⌈e^{e^{e^{X}}}⌉₊` admits no such statement at any finite `T`: THAT is the height
collapse, in one comparison. -/
theorem flatWitFloor_le_ceil_exp {ε : ℚ} {β A T : ℝ} {Hopq : ℕ} (hA : 1 ≤ A)
    (hbase : 200 * flatC A + 10000 ≤ T) (hdes : Real.exp (3.2 * A) ≤ T)
    (hbud : max (4 * budgetXFlat (ε : ℝ) β) (2 * Real.log A + 2) ≤ T)
    (heps : 4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4 ≤ ⌈Real.exp T⌉₊) :
    flatWitFloor ε β A Hopq
      ≤ max (max Hopq (max arcFloor36 loglogFloor50)) ⌈Real.exp T⌉₊ := by
  have h1 : flatDesignFloor A ≤ ⌈Real.exp T⌉₊ := flatDesignFloor_le_ceil_exp hA hbase hdes
  have h2 : budgetFloorFlat (ε : ℝ) β A ≤ ⌈Real.exp T⌉₊ := by
    rw [budgetFloorFlat]; exact Nat.ceil_le_ceil (Real.exp_le_exp.mpr hbud)
  rw [flatWitFloor]
  refine max_le (max_le (le_trans h1 (le_max_right _ _))
    (max_le (max_le ?_ (le_trans h2 (le_max_right _ _)))
      (le_trans heps (le_max_right _ _)))) ?_
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)

/-! ## §3 — THE REGISTER WINDOW: why the flat base cannot be `s15WitFloor2` -/

/-- **⟦THE COLLISION⟧** — the S15 register reads its base through
`s15WitFloor2_loglog_le` (`λ₋ ≤ 277.2589`, the exact ceiling the `anchor` and
`lvl` lines tolerate at `M = 2^355`), while every flat base carries
`λ₋ ≥ 3.2·A`.  So a flat base sits inside the register's window only for
`A ≤ 86.6` — the SAME window as §1's cap comparison, arrived at from the register
side.  Stated as: a flat base that clears the register's ceiling clears the cap
window too. -/
theorem flat_base_in_s15_window {A : ℝ} {B : ℕ} (hB : flatDesignFloor A ≤ B)
    (hwin : Real.log (Real.log ((B : ℕ) : ℝ)) ≤ 2772589 / 10000) :
    3.2 * A ≤ 2772589 / 10000 :=
  le_trans (flatDesignFloor_design hB) hwin

/-- **THE REGISTER WINDOW IS THE CAP WINDOW.**  `400·log 2 = 277.2589…`, so §1's
cap demand and §3's register demand are the same inequality on `A` to within the
witness floor's own rounding. -/
theorem s15_window_eq_cap_window :
    (2772589 : ℝ) / 10000 ≤ 400 * Real.log 2 + 1 := by
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  linarith


/-! ## §4 — THE CAPSTONE AT THE FLAT ROOT (HOP 3) -/

/-- The cap's `max`-lattice join with a consumer floor: the floor is absorbed into
the road's OPAQUE arm, so the cap keeps its three-arm shape and the height claim
survives the hop. -/
theorem flatCap_join_floor {ε : ℚ} {β A : ℝ} {Hcap Hopq h : ℕ}
    (hc : Hcap ≤ max (flatDesignFloor A)
      (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4))) :
    max Hcap h ≤ max (flatDesignFloor A)
      (max (max (max Hopq h) (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) := by
  omega

set_option maxHeartbeats 1000000 in
-- Same cause as the landed HOP 3: the ~120-line residue re-elaborates against the re-cut
-- prefix, which here gains three items and five conjuncts.
/-- **⟦HOP 3, AT THE FLAT ROOT⟧** (`logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot`)
— `S16Budget.logChowla2_capstone_final_const'_graded_gk_pinned_Mfl` (:1429) with its road
`obtain` re-pointed at `HloExportMRFlatRoot.m4_second_road_L2_gk_flatRoot`.

Against `S16BudgetFlat`'s HOP-3 twin (which is the LANDED road plus one shape rewrite) this
one is rooted in the FLAT head: no triple-exponential `budgetFloor` occurs anywhere beneath
it, and the `∃`-prefix carries the three flat items `A`, `β`, `Hopq` plus the FLAT CAP BOUND.
The proof body is the landed one, verbatim; only the first `obtain` and the `refine`'s prefix
move. -/
theorem logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot (K : ℕ)
    (hK : K ≤ 170000000) (hband : S16BandLaneCBounded K) (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks A β : ℝ) (x₀ Hcap Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
      Hcap ≤ max (flatDesignFloor A)
        (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
        ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
          ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            R.Hlo ≤ max Hcap U1floor ∧
            ∀ (M : ℕ), Mfl ≤ M →
              ∃ C' : ℝ, 0 < C' ∧
                8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
                    ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                  -- ⟦A⟧ THE SPINE ARITHMETIC
                  M4DoorGates_gk K Cg R M k δ₀ →
                  8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloor M : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    arcDen 12 H < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    m4SmallGradeFits (doorRowFloor M)
                      (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                      (fun H => 2 * rStrWitness H) H) →
                  -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    GRowsZeroGate'''_gk K M (A + s) Cp
                      (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                        + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                      ≤ (theta293 - epsrf (A + s))
                          * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                      * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    calQK (Adoor M) (s13GK K M) M 2 ≤ A + s ∧
                      Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
                          ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                      ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                  -- ⟦B4 RAW⟧ the crossing bound, carried
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                      (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                      5 ≤ Real.log (Real.log (2 * T)) →
                      (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                          ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                        ≤ 8 * (0 : ℝ) ^ 2
                          + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                \ seamBall (((A + s : ℕ)) : ℝ) 0)
                              ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                  (calP (Adoor M) (s13GK K M))
                                  (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                                  (mrAlpha (1 / 12)) 2,
                              ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                          + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                              * (Real.log (((A + s : ℕ)) : ℝ))
                                  ^ (-theta293 + epsrf (A + s)))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorBandBase_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hKc, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, hCapLe, hroad⟩ := m4_second_road_L2_gk_flatRoot K A₀ hA₀
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_gk K hK
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cband, hCband0, hCband40, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, A, β, x₀,
    max Hcap (max arcFloor36 loglogFloor50),
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, s11_grade_floor_hoistCb_prod_le Cband hCband0 hCband40,
    hβ, hA26, hA₀A, hAge, flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hMfloor
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, s11_grade_absorption' _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
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
  have hbase : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorRowZeroBase_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (Adoor M) (s13GK K M))
          (calQK (Adoor M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (Adoor M) (s13GK K M))
        (calQK (Adoor M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hρpos (fun i m => norm_doorPunctCoeffU_le_one_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloor M ≤ j →
      m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloor M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloor M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloor M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloor M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
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

/-! ## §5 — THE ROAD AT THE FLAT ROOT, PINNED (HOP 4) -/

set_option maxHeartbeats 1000000 in
-- Same cause as the landed HOP 4: the residue re-elaborates against the prefix.
/-- **⟦HOP 4, AT THE FLAT ROOT⟧** (`logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot`)
— `S16BudgetFlat.logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flat` on §4, so the four
flat socket consumers of `Salt.MR.FlatConsumers` are spent against a road that is FLAT ALL
THE WAY DOWN.  The `∃`-prefix carries `A`, `β`, `Hopq` and the flat cap bound; the body is
`S16BudgetFlat`'s, verbatim. -/
theorem logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot (K : ℕ)
    (hK : K ≤ 170000000) (hband : S16BandLaneCBounded K) (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (x₀ Hcap Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
      Hcap ≤ max (flatDesignFloor A)
        (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
        ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          ∀ M : ℕ, S15Sel''_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
            S15CrossingBound_gk K R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, A, β, x₀, Hcap, Hopq, Mfl, hCg, hε, hKc,
    hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hMflb, hβ, hA26, hA₀A,
    hAge, hCapLe, hmain⟩ :=
    logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot K hK hband A₀ hA₀
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hcap, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCgle, hεpin, hδpin, hMflb, hβ, hA26, hA₀A, hAge, hCapLe, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  -- ⟦THE BASE PIN⟧ `R.Hlo = U1floor`
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor
  intro hcap
  -- ⟦the two scale floors⟧
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  -- ⟦the arm, both halves⟧
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the RESTORED anchor
  have harith := s15_doorArithFrameRho_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_of_halfWindow_gk K hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register, at the RESTORED `x0_le`⟧
  have hgate : S13BandGate'_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_gk K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor le_rfl (s13_g2_jfloor_of_MSelect'_gk K hsel.hM (by linarith) hS))
    (s15_gate8_gk K le_rfl (s13_gate8_of_MSelect'_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gk K hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_gk_flat K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat hfl hb hlam50 htow hsel.rho le_rfl)
    (fun H L q j A s hb => s15_heps293_at_socket_flat hfl hb hρ0 hlam50 htow hsel.rho)
    (fun H L q j A s hb => s15_hband4096_at_socket_flat hfl hb hρ0 hlam50 htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_gk K hsel.hM (hgate.block H L q j A s hb) hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith

/-! ## §6 — ⟦THE FLAT TERMINAL⟧ -/

set_option maxHeartbeats 1000000 in
-- the seventeen-binder prefix re-elaborates beside the crossing supply's six constants
/-- **⟦THE FLAT TERMINAL⟧** (`logChowla2_witnessed_scale_flat`) — the flat road's counterpart
of `S16Budget.logChowla2_witnessed_scale_final'_v3`, pinned at the road's OWN cap.

⟦WHAT LEFT THE RIDER LIST, REMOVED-BECAUSE-PROVEN⟧

* **`Hcap ≤ s15WitFloor2` — THE WALL'S THIRD FACE — IS GONE.**  `v3` had to ask for it
  because the LANDED register pins the base at `s15WitFloor2`.  Here the base is pinned at
  `flatWitFloor ε β A Hopq` — the flat head's own cap, joined with `arcFloor36` and
  `loglogFloor50` — and `flatCap_le_flatWitFloor` (§2) discharges the pin outright.  The pin
  is legal: `flatWitFloor_design` (§2) is the design law at the pinned base, so the flat
  regime exists there; `flatWitFloor_le_ceil_exp` is its HEIGHT-2 envelope, against the
  landed `budgetFloor`'s height 3.
* `(x₀ : ℝ) ≤ e^{e^{275}}`, `Kc ≤ 2^539`, `Ct ≤ 2^23` — the Siegel item and the two WIDE
  constant-pool riders.  They were spent only inside `s15_sel''_witness_wide` to PRODUCE the
  register; the register is carried here (see below), so they do not appear.

⟦THE HYPOTHESIS LIST, EXACT AND COMPLETE⟧  the theorem's own arguments are
`hband : S16BandLaneCBounded 32000000` (the band-lane `C`) and the design floor
`A₀` with `162 ≤ A₀` (⟦LADDER-L G4⟧'s floor bump: `FlatFloorBump` kernelizes the two
`flatDoorM` demands the flat re-fire owes, and `162` is the least integer clearing both).
The inner implication asks for, in order:

* `e^{-100} ≤ cs` — the honest floor (`REPAIRS-LANE` ITEM 2), unchanged;
* `T₀ ≤ e^{e^{100}}` — the fuse's forced-equality opaque, unchanged;
* `Kq ≤ e^{100}` — TRUE with 46 orders spare, unchanged;
* `e^{-100} ≤ Ks` — the second Siegel item, unchanged.

and the payload then carries three predicates per `M`:

* `S15Sel''_gk 32000000 …` — ⛔ **THE REGISTER, THE NEW NAMED DEBT.**  On the landed road
  this is PRODUCED by `s15_sel''_witness_wide` at `M = 2^355`; that witness reads the base
  through `λ₋ ≤ 277.2589` and the tower through the `9/2` law.  The flat base has
  `λ₋ ≥ 3.2·A` (`flatWitFloor_design`), so it is outside the register's window whenever
  `3.2·A > 277.26` — §1/§3's single inequality, from the register side.  Producing it is the
  REGISTER/DOOR cone (`FlatConsumers` §4 prices the `lvl` line; the `anchor` line
  `14·λ₊ + log(1/ρ) + 33 ≤ 3.9·10⁹·(log₂M+1)` is the second, door-independent break);
* `S16CofactorSupply_gk 32000000 Cq R M` — ⟦RULING 9⟧'s shelved `Rbd`/`Cq` debt, carried;
* `S16BaseScaleCap96_gk 32000000 R M` — ⟦ITEM 3⟧'s base-scale cap at the divisor `9.60000096`.

⟦WHAT IS EXPORTED ABOUT THE DESIGN CONSTANT⟧ `0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat ε β ≤ A`
— `A` is SYMBOLIC (FLAT-REF §4: no numeral anywhere), above the caller's `A₀`, and the head's
own budget demand is exported so §1's price is readable at the terminal itself. -/
theorem logChowla2_witnessed_scale_flat (hband : S16BandLaneCBounded 32000000)
    (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Real.log C ≤ 40 ∧
      Mfl ≤ 2 ^ 355 ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
      (Real.exp (-100) ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          ∀ M : ℕ,
            S15Sel''_gk 32000000 Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
            S16CofactorSupply_gk 32000000 Cq R M → S16BaseScaleCap96_gk 32000000 R M →
              ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hcap, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hA26, hA₀A, hAge, hCapLe, hbody⟩ :=
    logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot 32000000 (by norm_num) hband
      A₀ hA₀
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40, hsupply⟩ :=
    s15_crossing_supplied_wide_gk 32000000
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0,
    hCgle, hεpin, hδpin, hC40, hMflb, hβ, hA26, hA₀A, hAge, ?_⟩
  intro hcs hT₀ hKq hKs g
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g (flatCap_le_flatWitFloor hCapLe)
  refine ⟨R, hReps, hHlo, hRg, hRtow, ?_⟩
  intro M hsel hcof hcap
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Ax s : ℕ, SocketBase R M H L q j Ax s →
      s13BlockFloor_gk 32000000 M ≤ Ax + s := by
    intro H L q j Ax s hb
    exact s15_block_at_socket_gk 32000000 hb
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire M hsel (hsupply hcs hT₀ hKq hKs R M hsel.hM hfl hblk hcof hcap)

/-! ## §7 — THE INHABITATION, and the register break priced on both sides -/

/-- **THE FLAT DESIGN POINT, AS A DEFINITION** (FLAT-REF §4: symbolic in `A`, no numeral
anywhere).  `flatWitA` is the least legal design constant at a given budget pair: the house
floor `162` (⟦LADDER-L G4⟧'s bump) joined with the head's own budget demand `budgetAFlat`. -/
def flatWitA (ε β : ℝ) : ℝ := max 162 (budgetAFlat ε β)

theorem flatWitA_ge (ε β : ℝ) : 162 ≤ flatWitA ε β := le_max_left _ _

theorem flatWitA_budget (ε β : ℝ) : budgetAFlat ε β ≤ flatWitA ε β := le_max_right _ _

/-- **⟦THE NON-VACUITY⟧** — a flat regime EXISTS at the flat witness floor, at any design
constant `A ≥ 26`: the floor discharges the design law `hflat` by construction
(`flatWitFloor_design`), and the builder's own base equation then sits above it.  So the
terminal's pinned base is inhabited, not merely well-formed. -/
theorem flatWitFloor_regime_exists {ε : ℚ} (heps : 0 < ε) (heps1 : ε ≤ 1 / 2) (β A : ℝ)
    (hA : 26 ≤ A) (Hopq : ℕ) (g : ℕ → ℕ → ℕ) :
    ∃ R : ChowlaRegimeFlat, R.eps = ε ∧ R.A = A ∧ flatWitFloor ε β A Hopq ≤ R.Hlo ∧
      g R.Hhi R.ω ≤ R.x ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) := by
  obtain ⟨R, hReps, hRA, hRHlo, hRg, _hRcap, hRwid⟩ :=
    chowlaRegimeFlat_exists_param_head A hA ε heps heps1 (flatWitFloor ε β A Hopq) g
  exact ⟨R, hReps, hRA, hRHlo, hRg, hRwid⟩

/-- **THE REGISTER'S `anchor` LINE AT THE LANDED CEILING** — `M = 2^355`,
`λ₊ ≤ 9.87·10¹⁰`, the `ρ`-charge at `43`: the line closes with `0.48 %` of margin.  This is
the number the whole `s15WitFloor2` calibration is pinned to. -/
theorem s15w2_anchor_landed_margin :
    14 * (987 * 10 ^ 8 : ℝ) + 43 + 33 ≤ 39 * 10 ^ 8 * 356 := by norm_num

/-- **⟦THE SECOND BREAK — THE `anchor` LINE AT THE FLAT CEILING⟧**  At the flat window
ceiling `λ₊ ≤ 3·10⁶⁰` (`FlatConsumers.s15w2_tower_bound_flat`) the same line FAILS at
`M = 2^355`, by 49 orders of magnitude.  Unlike `lvl`, `gRows` and `gP1`, the `anchor`
line's right side `3.9·10⁹·(log₂M+1)` is a FRAME constant
(`M4ArithRho.DoorArithFrameRho.anchor`), not a door constant: the `Adoor`-linear re-cut of
`Salt.MR.DoorLinear` does not touch it.  Raising `M` instead is blocked by the register's
`half` line (`0.7·doorRowFloor M ≤ log H₋/2`), which caps `log₂M` at the base's own scale.
So the register break is NOT the `lvl` line alone; it is `anchor` too, and that is the
frontier this wave stops at. -/
theorem s15w2_anchor_flat_break :
    ¬ (14 * (3 * 10 ^ 60 : ℝ) + 33 ≤ 39 * 10 ^ 8 * 356) := by norm_num

/-- **THE `gRows` LINE, BOTH SIDES.**  At the flat ceiling the landed door fails, and S3's
LINEAR door `AdoorL (2^355) = 2^391` (`FlatConsumers.adoorL_pow355`) clears by 55 orders —
the same verdict `FlatConsumers.s15w2_lvl_num_flat_doorL` records for `lvl`. -/
theorem s15w2_gRows_flat_break :
    ¬ (242 * (3 * 10 ^ 60 : ℝ) ≤ 24464133718016) := by norm_num

set_option exponentiation.threshold 4000 in
theorem s15w2_gRows_flat_doorL : 242 * (3 * 10 ^ 60 : ℝ) ≤ (2 : ℝ) ^ (391 : ℕ) := by
  norm_num

end Salt.MR

end
