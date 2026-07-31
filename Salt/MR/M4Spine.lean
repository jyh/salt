/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4BaseNarrow

/-!
# `M4Spine` — the S11 spine at ⟦THE FINAL REGISTER⟧, and the three walls it meets

`M4BaseNarrow.m4_wave_collapsed` is the M4/S9 road's terminal form: eighteen gates, every one
of them declared "regime-absorbable or witnessed", zero analytic arms.  The S11 spine's job
was to *fire* it — instantiate `(C, U1floor, g)`, then `(δ, Braw, MS, MSan, MStr, M, k)` at the
regime the exit builds, discharge the eighteen gates, and land

  `m4_door_closed : … → ¬ logChowla2Fails R.eps R.x R.ω`,   UNCONDITIONAL.

**It does not fire.**  This file records why — in the kernel where the obstruction is
arithmetic — and banks the two reusable stones the attempt produced.  Three walls, in order of
severity.

## ⟦WALL A — THE BUDGET COLLISION⟧ (§3, kernel-checked)

The register's arithmetic gates are **jointly inconsistent** at every window length any regime
can carry.  The collision is a four-line budget and needs no regime at all:

* ⟦gate 8⟧ `δ/4 + 4·2^k/x ≤ mrtDeliveredGrade (C/2) H` pins the door grade at the DECAYING MRT
  grade — `δ ≤ 4·(C/2)·(log H)^{−11/4}·loglog H`, so `δ ≲ C/(log H)²`;
* ⟦`M4Close.M4DoorGates.hMδ`⟧ `24·Cg/δ ≤ M` then forces `M ≳ (log H)²/C`, hence the graded
  floor `j₀ = doorRowFloor M = M·Adoor M ≥ 2^18·M ≳ 2^18·(log H)²/C`;
* ⟦gate 6⟧'s drift line carries the small-length summand `(9/2)(3/2)^{log₂H}(4/3)^{j₀}/H` of
  `m4BclGraded` (⟦LEVER 1′⟧'s weighted head, read at `(3/2)^{log₂H} ≥ 1`) against
  an envelope `MStr H` that ⟦G1⟧ (gate 15) pins from BELOW by `arcDen 12 H ≥ 1`, and ⟦gate 7⟧
  caps the whole budget by `mrtDeliveredGrade (C/2) H ≤ C`.  So `(4/3)^{j₀} ≤ C²·H`, i.e.
  `j₀·log(4/3) ≤ 2·log C + log H ≤ 2C + log H`, and `log(4/3) ≥ 1/4` gives
  `j₀ ≤ 8C + 4·log H`.

Multiplying the two by `C > 0`, `9·2^18·(log H)² ≤ 2^18·M·C ≤ (8C + 4·log H)·C`, i.e. after
dividing by `4`:

  **`589824·(log H)² ≤ 2C² + (log H)·C`**   (`m4_spine_budget_necessary`).

Since every regime has `log H ≥ 15` (`ChowlaRegime.hHlo_floor`: `H ≥ 4·10^6`), this forces
`log H ≤ C` (`m4_budget_forces_C`) — the MRT constant must exceed the log of every window
length in the range.  That is already unmeetable from outside: `C` is fixed BEFORE `R`, and
nothing bounds `R.Hhi` above (⟦WALL C⟧).  Worse, it is outright CONTRADICTORY along the
construction: `M4Exit.m4_exit_socket` builds `R` with `H0scale C = ⌈exp(C²)⌉₊ ≤ R.Hlo` (its
proof's `hscale`; the statement does not export it, which is why the collision below carries
`C² ≤ log H` as a hypothesis), i.e. `C² ≤ log H` at every admissible `H` — and `C² ≤ log H ≤ C`
at `log H ≥ 15` is FALSE (`m4_budget_collision`, `m4_spine_budget_collision`).  The `C`-lever
is self-defeating: raising `C` to buy room in the drift line raises the regime floor
quadratically faster than it buys.

⟦WHAT THIS MEANS⟧ `m4_wave_collapsed` is TRUE but VACUOUS — its hypothesis list cannot be met,
so no spine closes it.  The repair is a statement-level ruling, not an executor's page.  The
two candidate rulings: (i) an `M`-free small-length term (the `(4/3)^{j₀}(3/2)^{log₂H}/H`
factor is `m4BclGraded`'s, from the graded split's `j < j₀` half — it is what `M4Maximal`'s
⟦THE CONSUMPTION NOTE⟧ already flagged as "not free"; ⟦LEVER 1′⟧ HALVED its exponent — the
demand is `H ≳ 2^{j₀}` where it was `4^{j₀}` — and the wall survived the halving, which is
itself the measure of how far ruling (i) must go); or (ii) a per-`H` door grade `δ H` in place
of the single pinned `δ`, which is what decouples `M` from the TOP of the window range.

**(ii) is REFUTED** (`m4_spine_budget_collision_perH_at_Hlo`, 2026-07-29): the collision needs
only ONE window length, and `H := R.Hlo` is in every regime's range with both of its `H`-side
hypotheses free there (`ChowlaRegime.hHlo_floor` gives `log R.Hlo ≥ 15`; the exit's own
`H0scale C ≤ R.Hlo` gives `C² ≤ log R.Hlo`).  A per-`H` grade is contradictory through its own
bottom instance `δ R.Hlo`.  Ruling (i) is the survivor.

## ⟦WALL B — THE ENDPOINT, ∀-QUANTIFIED⟧ (§4, kernel-checked)

`DoorRowCarriedT0`'s conjunct `hend : doorChiCoeff χ M X_d = 0` is discharged exactly when
`X_d ∉ 𝒮` (`M4Band.memSCoeff_eq_zero_of_not_memS`), and `M4DoorClose`'s ⟦THE ENDPOINT
CONVENTION⟧ says a consumer "discharges it by choosing `s`".  **That freedom is already spent.**
The register's per-instance line quantifies `∀ s ≤ ⌊H/d⌋ + 1`, so at `d = 1` it demands

  `doorChiCoeff χ M (doorLadder R.x H (i+1) − 1 + s) = 0`   for EVERY `s ≤ H + 1`

(`m4_register_forces_endpoint_interval`) — the sieved datum must vanish on a full interval of
`H + 2` consecutive integers at the bottom of every ladder block, at every `H` in the window
range, and (taking `q = 1`, admissible since `1 ≤ arcDen 12 H`) with no character zero to hide
behind.  `𝒮 = MemS 𝒫 𝒬K 2` is the Ramaré sieve at `𝒬K_j = 𝒫_j^{j²M}`, designed so that ALMOST
EVERY integer has a prime factor in each block; a length-`(H+2)` interval free of `𝒮` is not
something a consumer can arrange, and `H ≥ 4·10^6`.  The `∀s` is not optional:
`M4Maximal.M4ChiDyadicRowMeanSq` needs the row datum at every shift, because
`m4_chiShiftBlock_of_dyadicRow` decomposes the ladder block into shifted pieces.

## ⟦WALL C — THE `H`-UPPER GATES AGAINST AN UNBOUNDED `R.Hhi`⟧ — **REPAIRED** (2026-07-29)

As found, two register gates were UPPER bounds on the window length: ⟦gate 9⟧
`arcDen 12 H ≤ Qm`, with `Qm` the theorem's own parameter fixed BEFORE the regime, and
⟦gate 12⟧ `log H ≤ 2^{21845}`, a numeral.  The exit (`M4Exit.m4_exit_socket`, off
`log_chowla_two_budget_head_g`) exposes only LOWER control — `U1floor ≤ R.Hlo`,
`g R.Hhi R.ω ≤ R.x` — and `ChowlaRegime` carries no upper bound on `Hhi` at all (`hfit` forces
it UP, above the `J`-step tower), so neither gate was dischargeable from outside.  Both are
now re-cut, and both repairs are mechanical:

* ⟦gate 12⟧ is `M`-RELATIVE: `arcDen 12 H < calP (Adoor M) (3072M) 1 = 2^{Adoor M}`
  (`M4Residue.door_dilation_gate'`).  The dilation never needed a numeral — it needs
  `d₀ ≤ q ≤ W < P₁`, and `P₁` is the door's own bottom block, which `M` (witnessed, chosen
  after `R`) controls.  The old numeral route survives as `door_dilation_gate`.
* ⟦gate 9⟧ is discharged by a QUANTIFIER REORDER: `Qm` moved from the leading parameters into
  the witnessed group beside `M`, `k`, which is legitimate because the three `Qm`-taking
  suppliers are Skolemised — `Kfl`, `Kcf`, `Kbox`, `X₀w` are now choice FUNCTIONS `ℕ → ℝ`.
  `M4BaseNarrow.m4_modulusCap_discharged` then closes the gate at
  `Qm := ⌈arcDen 12 R.Hhi⌉₊`.

⟦WALL A⟧ and ⟦WALL B⟧ are of a different order and STAND: the register is now honest and
`Hhi`-safe, and still unfulfillable.

## ⟦WHAT LANDS HERE⟧

* §1 `m4ArcFloor`, `eight_arcDen_le_of_arcFloor`, `two_arcDen_le_of_arcFloor` — the brief's
  ⟦S-4⟧ page (`c·(log H)^{12} ≤ H` past an explicit floor): ⟦gates 13/14⟧ discharged for ANY
  repaired register.  Route: `log t ≤ 24·t^{1/24}` raised to the twelfth power, then the floor
  `8·24^{12} ≤ √H`.
* §2 `mrtDeliveredGrade_le_inv_sq` — the delivered grade against a clean `1/(log H)²`; the
  arithmetic both halves of ⟦WALL A⟧ run on, and the transfer any repaired budget will reuse.
* §3 ⟦WALL A⟧: `m4_spine_budget_necessary`, `m4_budget_forces_C`, `m4_budget_collision`,
  `m4_spine_budget_collision`, and the two floor-read corollaries
  `m4_spine_budget_collision_at_Hlo` / `m4_spine_budget_collision_perH_at_Hlo` — the second
  banks the refutation of the council's C2(ii) repair (a per-`H` door grade `δ H`): the
  collision is arithmetic at ONE window length, and `R.Hlo` is in every regime's range.
* §4 ⟦WALL B⟧: `doorRowCarriedT0_endpoint`, `m4_register_forces_endpoint_interval`.

Nothing here moves a landed statement; the file is purely additive.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE ARC FLOOR: `8·arcDen 12 H ≤ H` past an explicit threshold

⟦gates 13/14⟧ of ⟦THE FINAL REGISTER⟧ are `2·arcDen 12 H ≤ H` and `8·arcDen 12 H ≤ H`, i.e.
`c·(log H)^{12} ≤ H`.  The brief named this the spine's ONE hard new page; it is the
`log_scale_threshold` genre run at a twelfth power: `log t ≤ 24·t^{1/24}` (one application of
`log u ≤ u − 1` at `u = t^{1/24}`), raised to the twelfth power, gives
`(log t)^{12} ≤ 24^{12}·√t`, and the floor is where `8·24^{12} ≤ √t`. -/

/-- **THE ARC FLOOR** — `10^36`, the window length past which `8·(log H)^{12} ≤ H`.  SHAPE, not
a claim of optimality: `(8·24^{12})² ≈ 8.54·10^{34}` is what the route costs, and `10^36`
clears it with a factor `11`. -/
def m4ArcFloor : ℕ := 10 ^ 36

/-- One application of `log u ≤ u − 1` at `u = t^{1/24}`: `log t ≤ 24·t^{1/24}`. -/
private lemma log_le_rpow_inv_24 {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ 24 * t ^ ((1 : ℝ) / 24) := by
  have hp : (0 : ℝ) < t ^ ((1 : ℝ) / 24) := Real.rpow_pos_of_pos ht _
  have h1 : Real.log (t ^ ((1 : ℝ) / 24)) ≤ t ^ ((1 : ℝ) / 24) - 1 :=
    Real.log_le_sub_one_of_pos hp
  rw [Real.log_rpow ht] at h1
  linarith

/-- `arcDen 12 H` read as an honest twelfth power — the only shape the estimates below use. -/
theorem arcDen_twelve_eq_pow (H : ℕ) : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
  unfold arcDen
  rw [show ((12 : ℝ)) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **THE ARC GATE, AT THE FLOOR** (`eight_arcDen_le_of_arcFloor`) — ⟦gate 14⟧, the register's
⟦regime fact⟧, for every window length past `m4ArcFloor`. -/
theorem eight_arcDen_le_of_arcFloor {H : ℕ} (hH : m4ArcFloor ≤ H) :
    8 * arcDen 12 H ≤ (H : ℝ) := by
  have hHR : ((10 : ℝ) ^ (36 : ℕ)) ≤ (H : ℝ) := by
    have h : (10 : ℕ) ^ (36 : ℕ) ≤ H := hH
    exact_mod_cast h
  have h10 : (0 : ℝ) < (10 : ℝ) ^ (36 : ℕ) := by positivity
  have ht : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le h10 hHR
  have ht1 : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
  have hL0 : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg ht1
  have hstep : Real.log (H : ℝ) ≤ 24 * (H : ℝ) ^ ((1 : ℝ) / 24) := log_le_rpow_inv_24 ht
  have hhalf : ((H : ℝ) ^ ((1 : ℝ) / 24)) ^ (12 : ℕ) = Real.sqrt (H : ℝ) := by
    rw [← Real.rpow_natCast ((H : ℝ) ^ ((1 : ℝ) / 24)) 12, ← Real.rpow_mul ht.le,
      Real.sqrt_eq_rpow]
    norm_num
  have hA : Real.log (H : ℝ) ^ (12 : ℕ) ≤ 24 ^ (12 : ℕ) * Real.sqrt (H : ℝ) := by
    calc Real.log (H : ℝ) ^ (12 : ℕ) ≤ (24 * (H : ℝ) ^ ((1 : ℝ) / 24)) ^ (12 : ℕ) := by
          gcongr
      _ = 24 ^ (12 : ℕ) * ((H : ℝ) ^ ((1 : ℝ) / 24)) ^ (12 : ℕ) := by rw [mul_pow]
      _ = 24 ^ (12 : ℕ) * Real.sqrt (H : ℝ) := by rw [hhalf]
  have hsq : Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ) = (H : ℝ) := Real.mul_self_sqrt ht.le
  have hs0 : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have hbig : (8 : ℝ) * 24 ^ (12 : ℕ) ≤ Real.sqrt (H : ℝ) := by
    have hval : (8 : ℝ) * 24 ^ (12 : ℕ) = 292162779488452608 := by norm_num
    rw [hval]
    have hle : (292162779488452608 : ℝ) ^ (2 : ℕ) ≤ (H : ℝ) := by
      refine le_trans ?_ hHR
      norm_num
    calc (292162779488452608 : ℝ)
        = Real.sqrt ((292162779488452608 : ℝ) ^ (2 : ℕ)) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (H : ℝ) := Real.sqrt_le_sqrt hle
  rw [arcDen_twelve_eq_pow]
  nlinarith [hA, hbig, hsq, hs0]

/-- ⟦gate 13⟧, from ⟦gate 14⟧. -/
theorem two_arcDen_le_of_arcFloor {H : ℕ} (hH : m4ArcFloor ≤ H) :
    2 * arcDen 12 H ≤ (H : ℝ) := by
  have h := eight_arcDen_le_of_arcFloor hH
  have h0 : 0 ≤ arcDen 12 H := by
    rw [arcDen_twelve_eq_pow]; positivity
  linarith

/-! ## §2 — THE DELIVERED GRADE AGAINST `1/(log H)²`

`mrtDeliveredGrade C H = C·(log H)^{−11/4}·loglog H`.  Both halves of ⟦WALL A⟧ read it against
a clean power: `loglog H ≤ (4/3)(log H)^{3/4}` (one application of `log u ≤ u − 1` at
`u = (log H)^{3/4}`) turns the exponent `−11/4 + 3/4` into `−2`. -/

set_option maxHeartbeats 800000 in
-- the `rpow` bookkeeping (`−11/4 + 3/4 = −2`) plus the closing `field_simp` on a
-- three-factor product; no tactic search happens
/-- **THE DELIVERED GRADE, CAPPED** (`mrtDeliveredGrade_le_inv_sq`). -/
theorem mrtDeliveredGrade_le_inv_sq {C : ℝ} (hC : 0 ≤ C) {H : ℕ}
    (hL : 15 ≤ Real.log (H : ℝ)) :
    mrtDeliveredGrade C H ≤ 4 * C / (3 * Real.log (H : ℝ) ^ (2 : ℕ)) := by
  set L := Real.log (H : ℝ) with hLdef
  have hL0 : (0 : ℝ) < L := by linarith
  have hlogL : Real.log L ≤ 4 / 3 * L ^ ((3 : ℝ) / 4) := by
    have hp : (0 : ℝ) < L ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
    have h1 := Real.log_le_sub_one_of_pos hp
    rw [Real.log_rpow hL0] at h1
    linarith
  have hrn : (0 : ℝ) ≤ L ^ (-(11 / 4 : ℝ)) := (Real.rpow_pos_of_pos hL0 _).le
  have hcomb : L ^ (-(11 / 4 : ℝ)) * L ^ ((3 : ℝ) / 4) = (L ^ (2 : ℕ))⁻¹ := by
    rw [← Real.rpow_add hL0,
      show (-(11 / 4 : ℝ)) + (3 : ℝ) / 4 = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hL0.le, Real.rpow_natCast]
  have hkey : L ^ (-(11 / 4 : ℝ)) * Real.log L ≤ 4 / 3 * (L ^ (2 : ℕ))⁻¹ := by
    calc L ^ (-(11 / 4 : ℝ)) * Real.log L
        ≤ L ^ (-(11 / 4 : ℝ)) * (4 / 3 * L ^ ((3 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hlogL hrn
      _ = 4 / 3 * (L ^ (-(11 / 4 : ℝ)) * L ^ ((3 : ℝ) / 4)) := by ring
      _ = 4 / 3 * (L ^ (2 : ℕ))⁻¹ := by rw [hcomb]
  have hshape : mrtDeliveredGrade C H = C * (L ^ (-(11 / 4 : ℝ)) * Real.log L) := by
    unfold mrtDeliveredGrade
    rw [← hLdef, mul_assoc]
  have hL2 : (0 : ℝ) < L ^ (2 : ℕ) := by positivity
  rw [hshape]
  calc C * (L ^ (-(11 / 4 : ℝ)) * Real.log L) ≤ C * (4 / 3 * (L ^ (2 : ℕ))⁻¹) :=
        mul_le_mul_of_nonneg_left hkey hC
    _ = 4 * C / (3 * L ^ (2 : ℕ)) := by field_simp

/-! ## §3 — ⟦WALL A⟧: THE BUDGET COLLISION

The hypotheses below are, verbatim, ⟦THE FINAL REGISTER⟧'s lines 4, 6, 7, 8, 15 together with
`M4Close.M4DoorGates`' `hM`, `hδ`, `hMδ`, all read at ONE window length `H`.  No regime appears
— the collision is arithmetic, so it applies to whatever regime the exit produces.

The one non-mechanical step is the passage from the drift line to `(4/3)^{j₀} ≤ C²·H`: the
drift LHS dominates its own SMALL-LENGTH summand, which carries `9·(4/3)^{j₀}/H` against
`Ftr H = 2·MStr H ≥ 2·arcDen 12 H ≥ 2` (⟦G1⟧ plus `1 ≤ (log H)^{12}`), and ⟦gate 7⟧ caps the
whole thing by `mrtDeliveredGrade (C/2) H ≤ C`. -/

set_option maxHeartbeats 2000000 in
-- the budget runs five `nlinarith` calls over the same six atoms (`log H`, `C`, `M`,
-- `(4/3)^{j₀}/H`, `MStr H`, `Braw H`); the cost is the arithmetic, not a search
/-- **THE NECESSARY CONDITION** (`m4_spine_budget_necessary`).  ANY instantiation of ⟦THE FINAL
REGISTER⟧'s arithmetic gates at a window length `H` with `log H ≥ 15` (every regime:
`hHlo_floor` gives `H ≥ 4·10^6`, so `log H ≥ 15.2`) satisfies

  `589824·(log H)² ≤ 2C² + (log H)·C`.

`589824 = 9·2^18/4` — the `9` from the `δ`-to-`M` step, the `2^18` from `Adoor`, and the
`1/4` from ⟦LEVER 1′⟧: the drift line's small-length summand now carries `(4/3)^{j₀}` in place
of `4^{j₀}`, so the log step reads `j₀·log(4/3) ≤ 2C + log H` and `log(4/3) ≥ 1/4` (the
uniform route had `log 4 ≥ 1`).  The wall STANDS at the weighted head — the geometric weights
cost it exactly a factor `4` in the collision constant, and `589824 ≫ 3` is what
`m4_budget_forces_C` needs. -/
theorem m4_spine_budget_necessary
    {Cg C δ : ℝ} {Braw MSan MStr : ℕ → ℝ} {M H : ℕ}
    (hCg : 1 ≤ Cg) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hL : 15 ≤ Real.log (H : ℝ))
    (hMδ : 24 * Cg / δ ≤ (M : ℝ))
    (hMSan0 : 0 ≤ MSan H) (hMStr0 : 0 ≤ MStr H)
    (hdrift : ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
          * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloor M)
              (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H)
    (hdel : Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H)
    (hrest : δ / 4 ≤ mrtDeliveredGrade (C / 2) H)
    (hG1 : arcDen 12 H ≤ MStr H) :
    589824 * Real.log (H : ℝ) ^ (2 : ℕ) ≤ 2 * C ^ (2 : ℕ) + Real.log (H : ℝ) * C := by
  have hL0 : (0 : ℝ) < Real.log (H : ℝ) := by linarith
  have hL2 : (0 : ℝ) < Real.log (H : ℝ) ^ (2 : ℕ) := by positivity
  have hL2big : (225 : ℝ) ≤ Real.log (H : ℝ) ^ (2 : ℕ) := by nlinarith
  -- ⟦`H` is a genuine window length⟧
  have hH1 : 1 ≤ H := by
    rcases Nat.eq_zero_or_pos H with rfl | h
    · exfalso; norm_num at hL
    · exact h
  have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  -- ⟦`arcDen` as an honest twelfth power⟧
  have hL1 : (1 : ℝ) ≤ Real.log (H : ℝ) := by linarith
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := by
    rw [arcDen_twelve_eq_pow]
    calc (1 : ℝ) = 1 ^ (12 : ℕ) := by norm_num
      _ ≤ Real.log (H : ℝ) ^ (12 : ℕ) := by gcongr
  have harc0 : (0 : ℝ) ≤ arcDen 12 H := by linarith
  -- ⟦the delivered grade, capped⟧
  have hCh : (0 : ℝ) ≤ C / 2 := by linarith
  have hmr := mrtDeliveredGrade_le_inv_sq hCh hL
  have hmr' : mrtDeliveredGrade (C / 2) H ≤ 2 * C / (3 * Real.log (H : ℝ) ^ (2 : ℕ)) := by
    have he : 4 * (C / 2) = 2 * C := by ring
    rwa [he] at hmr
  -- ⟦`δ ≲ C/(log H)²`⟧
  have hδle : δ ≤ 8 * C / (3 * Real.log (H : ℝ) ^ (2 : ℕ)) := by
    have h := le_trans hrest hmr'
    calc δ = 4 * (δ / 4) := by ring
      _ ≤ 4 * (2 * C / (3 * Real.log (H : ℝ) ^ (2 : ℕ))) := by linarith
      _ = 8 * C / (3 * Real.log (H : ℝ) ^ (2 : ℕ)) := by ring
  -- ⟦a zero grade cannot carry a positive `δ`⟧
  have hC0 : (0 : ℝ) < C := by
    rcases lt_or_eq_of_le hC with h | h
    · exact h
    · exfalso
      rw [← h] at hδle
      simp at hδle
      linarith
  -- ⟦the `δ`-to-`M` step: `9·(log H)² ≤ M·C`⟧
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hinv : (0 : ℝ) < 1 / δ := by positivity
  have h24 : 24 / δ ≤ (M : ℝ) := by
    have h1 : (24 : ℝ) * (1 / δ) ≤ (24 * Cg) * (1 / δ) :=
      mul_le_mul_of_nonneg_right (by linarith) hinv.le
    have e1 : (24 : ℝ) / δ = 24 * (1 / δ) := by ring
    have e2 : (24 : ℝ) * Cg / δ = (24 * Cg) * (1 / δ) := by ring
    rw [e1]
    rw [e2] at hMδ
    linarith
  have hMδ2 : (24 : ℝ) ≤ (M : ℝ) * δ := (div_le_iff₀ hδ).mp h24
  have hMC : 9 * Real.log (H : ℝ) ^ (2 : ℕ) ≤ (M : ℝ) * C := by
    have hpos : (0 : ℝ) < 3 * Real.log (H : ℝ) ^ (2 : ℕ) := by linarith
    have hstep : (M : ℝ) * δ ≤ (M : ℝ) * (8 * C / (3 * Real.log (H : ℝ) ^ (2 : ℕ))) :=
      mul_le_mul_of_nonneg_left hδle hM0
    have h1 : (24 : ℝ) ≤ (M : ℝ) * (8 * C) / (3 * Real.log (H : ℝ) ^ (2 : ℕ)) := by
      calc (24 : ℝ) ≤ (M : ℝ) * δ := hMδ2
        _ ≤ (M : ℝ) * (8 * C / (3 * Real.log (H : ℝ) ^ (2 : ℕ))) := hstep
        _ = (M : ℝ) * (8 * C) / (3 * Real.log (H : ℝ) ^ (2 : ℕ)) := by ring
    have h2 := (le_div_iff₀ hpos).mp h1
    nlinarith [h2]
  -- ⟦the drift line's small-length summand⟧
  have hdr := hdrift 1 (by norm_num) (by simpa using harc1)
  have hdr1 : (1 + 2 * Real.pi * arcDen 12 H) ^ 2
      * (3 * m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H)
          (fun H => 2 * MStr H) H) ≤ Braw H := by
    simpa using hdr
  have hu0 : (0 : ℝ) ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ (doorRowFloor M)
      / (H : ℝ) := by positivity
  have ha1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ (Nat.log 2 H) := one_le_pow₀ (by norm_num)
  have hFtr : (2 : ℝ) ≤ 2 * MStr H := by
    have := le_trans harc1 hG1
    linarith
  have hbcl : 9 * (4 / 3 : ℝ) ^ (doorRowFloor M) / (H : ℝ)
      ≤ m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H) H := by
    have hfirst : (0 : ℝ) ≤ m4Cmax H * (2 * MSan H) :=
      mul_nonneg (m4Cmax_nonneg H) (by linarith)
    have hsnd0 : (0 : ℝ) ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H)
        * (8 / 3 : ℝ) ^ (doorRowFloor M) / (H : ℝ) ^ 2 * (2 * MStr H) := by
      have : (0 : ℝ) ≤ 2 * MStr H := by linarith
      positivity
    have hpow43 : (0 : ℝ) < (4 / 3 : ℝ) ^ (doorRowFloor M) := by positivity
    have hkey : 9 * (4 / 3 : ℝ) ^ (doorRowFloor M) / (H : ℝ)
        ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ (doorRowFloor M) / (H : ℝ)
            * (2 * MStr H) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hH0]
      have h1 : 9 * (4 / 3 : ℝ) ^ (doorRowFloor M)
          ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ (doorRowFloor M) * 2 := by
        nlinarith [mul_le_mul_of_nonneg_left ha1 (by positivity :
          (0 : ℝ) ≤ 9 * (4 / 3 : ℝ) ^ (doorRowFloor M))]
      nlinarith [h1, hFtr, mul_le_mul_of_nonneg_left hFtr
        (by positivity : (0 : ℝ) ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H)
          * (4 / 3 : ℝ) ^ (doorRowFloor M))]
    have hexp : m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
        = m4Cmax H * (2 * MSan H)
          + 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ (doorRowFloor M) / (H : ℝ)
              * (2 * MStr H)
          + 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ (doorRowFloor M)
              / (H : ℝ) ^ 2 * (2 * MStr H) := by
      unfold m4BclGraded
      ring
    rw [hexp]
    linarith
  have hBraw_ge : 27 * (4 / 3 : ℝ) ^ (doorRowFloor M) / (H : ℝ) ≤ Braw H := by
    set G := m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
      with hGdef
    set A := (1 + 2 * Real.pi * arcDen 12 H) ^ 2 with hAdef
    have h2 : 27 * (4 / 3 : ℝ) ^ (doorRowFloor M) / (H : ℝ) ≤ 3 * G := by
      calc 27 * (4 / 3 : ℝ) ^ (doorRowFloor M) / (H : ℝ)
          = 3 * (9 * (4 / 3 : ℝ) ^ (doorRowFloor M) / (H : ℝ)) := by ring
        _ ≤ 3 * G := by linarith [hbcl]
    have hX0 : (0 : ℝ) ≤ 3 * G := by
      have h0 : (0 : ℝ) ≤ 27 * (4 / 3 : ℝ) ^ (doorRowFloor M) / (H : ℝ) := by positivity
      linarith
    have hA1 : (1 : ℝ) ≤ A := by
      have hbase : (1 : ℝ) ≤ 1 + 2 * Real.pi * arcDen 12 H := by
        nlinarith [Real.pi_pos, harc0]
      rw [hAdef]
      nlinarith [hbase]
    have h1 : (3 : ℝ) * G ≤ A * (3 * G) := by nlinarith [hX0, hA1]
    linarith [hdr1]
  have hBraw0 : (0 : ℝ) ≤ Braw H := by
    have h0 : (0 : ℝ) ≤ 27 * (4 / 3 : ℝ) ^ (doorRowFloor M) / (H : ℝ) := by positivity
    linarith [hBraw_ge]
  -- ⟦gate 7 caps the budget by `C`⟧
  have hmrC : mrtDeliveredGrade (C / 2) H ≤ C := by
    refine le_trans hmr' ?_
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 3 * Real.log (H : ℝ) ^ (2 : ℕ))]
    nlinarith [hL2big, hC0]
  have hBrawC : Braw H ≤ C ^ (2 : ℕ) := by
    have h1 : Real.sqrt (Braw H) ≤ C := le_trans hdel hmrC
    have h2 : Real.sqrt (Braw H) ^ (2 : ℕ) = Braw H := Real.sq_sqrt hBraw0
    nlinarith [h1, Real.sqrt_nonneg (Braw H)]
  -- ⟦`(4/3)^{j₀} ≤ C²·H`, hence `j₀ ≤ 8C + 4·log H`⟧
  have hpow0 : (0 : ℝ) < (4 / 3 : ℝ) ^ (doorRowFloor M) := by positivity
  have h4j : (4 / 3 : ℝ) ^ (doorRowFloor M) ≤ C ^ (2 : ℕ) * (H : ℝ) := by
    have h1 : 27 * (4 / 3 : ℝ) ^ (doorRowFloor M) / (H : ℝ) ≤ C ^ (2 : ℕ) :=
      le_trans hBraw_ge hBrawC
    rw [div_le_iff₀ hH0] at h1
    linarith [hpow0]
  -- `log(4/3) ≥ 1/4` because `(4/3)^4 = 256/81 = 3.16… > e`
  have hlog43 : (1 : ℝ) / 4 ≤ Real.log (4 / 3) := by
    have h : (1 : ℝ) ≤ Real.log ((4 / 3 : ℝ) ^ (4 : ℕ)) := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < (4 / 3 : ℝ) ^ (4 : ℕ))]
      have := Real.exp_one_lt_d9
      norm_num
      linarith
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hj0le : ((doorRowFloor M : ℕ) : ℝ) ≤ 8 * C + 4 * Real.log (H : ℝ) := by
    have hmono := Real.log_le_log hpow0 h4j
    rw [Real.log_pow] at hmono
    have hsplit : Real.log (C ^ (2 : ℕ) * (H : ℝ)) = 2 * Real.log C + Real.log (H : ℝ) := by
      rw [Real.log_mul (by positivity) (by linarith), Real.log_pow]
      norm_num
    rw [hsplit] at hmono
    have hlogC : Real.log C ≤ C := by
      have := Real.log_le_sub_one_of_pos hC0
      linarith
    have hj0nn : (0 : ℝ) ≤ ((doorRowFloor M : ℕ) : ℝ) := Nat.cast_nonneg _
    have hq := mul_le_mul_of_nonneg_left hlog43 hj0nn
    linarith [hmono, hq, hlogC]
  -- ⟦`Adoor ≥ 2^18`⟧ (the pre-re-pin bound: true-and-weaker at the `2^36` anchor)
  have hAdoor : (262144 : ℝ) * (M : ℝ) ≤ ((doorRowFloor M : ℕ) : ℝ) := by
    have hnat : 2 ^ 18 * M ≤ doorRowFloor M := by
      unfold doorRowFloor
      calc 2 ^ 18 * M = M * 2 ^ 18 := by ring
        _ ≤ M * Adoor M := Nat.mul_le_mul_left _ (Adoor_ge_old M)
    have h := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at h
    linarith
  -- ⟦the collision⟧
  have h1 : (262144 : ℝ) * (M : ℝ) * C ≤ ((doorRowFloor M : ℕ) : ℝ) * C :=
    mul_le_mul_of_nonneg_right hAdoor hC0.le
  have h2 : ((doorRowFloor M : ℕ) : ℝ) * C ≤ (8 * C + 4 * Real.log (H : ℝ)) * C :=
    mul_le_mul_of_nonneg_right hj0le hC0.le
  nlinarith [hMC, h1, h2]

/-- **THE FORCED CONSTANT** (`m4_budget_forces_C`).  The necessary condition, read as a lower
bound on the MRT constant: the register can only be met if `C` exceeds `log H`. -/
theorem m4_budget_forces_C {C L : ℝ} (hC : 0 ≤ C) (hL : 15 ≤ L)
    (hb : 589824 * L ^ (2 : ℕ) ≤ 2 * C ^ (2 : ℕ) + L * C) : L ≤ C := by
  by_contra hcon
  have h : C < L := not_le.mp hcon
  nlinarith [hb, h, hL, hC]

/-- **THE COLLISION** (`m4_budget_collision`).  Against the exit's own floor demand
`H0scale C ≤ R.Hlo`, i.e. `C² ≤ log H` (`M4Exit.sq_le_log_of_H0scale_le`), the forced constant
is impossible. -/
theorem m4_budget_collision {C L : ℝ} (hC : 0 ≤ C) (hL : 15 ≤ L)
    (hb : 589824 * L ^ (2 : ℕ) ≤ 2 * C ^ (2 : ℕ) + L * C) (hscale : C ^ (2 : ℕ) ≤ L) :
    False := by
  have hLC := m4_budget_forces_C hC hL hb
  nlinarith [hLC, hscale, hL, hC]

/-- **⟦WALL A⟧, ASSEMBLED** (`m4_spine_budget_collision`).  ⟦THE FINAL REGISTER⟧'s arithmetic
gates, at one window length of one regime, together with the exit's own scale floor
(`C² ≤ log H`, which `M4Exit.m4_exit_socket` guarantees at every admissible `H` through
`H0scale C ≤ R.Hlo`), are CONTRADICTORY.  Hence `m4_wave_collapsed`'s hypothesis list is
unfulfillable and no S11 spine closes it. -/
theorem m4_spine_budget_collision
    {Cg C δ : ℝ} {Braw MSan MStr : ℕ → ℝ} {M H : ℕ}
    (hCg : 1 ≤ Cg) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hL : 15 ≤ Real.log (H : ℝ))
    (hscale : C ^ (2 : ℕ) ≤ Real.log (H : ℝ))
    (hMδ : 24 * Cg / δ ≤ (M : ℝ))
    (hMSan0 : 0 ≤ MSan H) (hMStr0 : 0 ≤ MStr H)
    (hdrift : ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
          * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloor M)
              (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H)
    (hdel : Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H)
    (hrest : δ / 4 ≤ mrtDeliveredGrade (C / 2) H)
    (hG1 : arcDen 12 H ≤ MStr H) :
    False :=
  m4_budget_collision hC hL
    (m4_spine_budget_necessary hCg hC hδ hL hMδ hMSan0 hMStr0 hdrift hdel hrest hG1) hscale

/-- **⟦WALL A⟧ AT THE REGIME'S OWN FLOOR** (`m4_spine_budget_collision_at_Hlo`).  The
collision, with its two `H`-side hypotheses DISCHARGED at `H := R.Hlo`: `log R.Hlo ≥ 15` is
`ChowlaRegime.hHlo_floor` (`4·10⁶ ≤ R.Hlo`, `Salt.Entropy.Chowla.tower_log_bounds`) and
`C² ≤ log R.Hlo` is the exit's own scale floor `H0scale C ≤ R.Hlo`
(`M4Exit.sq_le_log_of_H0scale_le`, which `M4Exit.m4_exit_socket`'s `hscale` supplies).  So the
register's arithmetic gates need only be read at ONE window length — the BOTTOM of the range —
to be contradictory. -/
theorem m4_spine_budget_collision_at_Hlo {R : ChowlaRegime} {Cg C δ : ℝ}
    {Braw MSan MStr : ℕ → ℝ} {M : ℕ}
    (hCg : 1 ≤ Cg) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hscale : H0scale C ≤ R.Hlo)
    (hMδ : 24 * Cg / δ ≤ (M : ℝ))
    (hMSan0 : 0 ≤ MSan R.Hlo) (hMStr0 : 0 ≤ MStr R.Hlo)
    (hdrift : ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 R.Hlo →
      (1 + 2 * Real.pi * (arcDen 12 R.Hlo / (q : ℝ))) ^ 2
          * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloor M)
              (fun H => 2 * MSan H) (fun H => 2 * MStr H) R.Hlo)) ≤ Braw R.Hlo)
    (hdel : Real.sqrt (Braw R.Hlo) ≤ mrtDeliveredGrade (C / 2) R.Hlo)
    (hrest : δ / 4 ≤ mrtDeliveredGrade (C / 2) R.Hlo)
    (hG1 : arcDen 12 R.Hlo ≤ MStr R.Hlo) :
    False :=
  m4_spine_budget_collision hCg hC hδ (tower_log_bounds R.hHlo_floor).1
    (sq_le_log_of_H0scale_le hscale) hMδ hMSan0 hMStr0 hdrift hdel hrest hG1

/-- **⟦WALL A⟧ SURVIVES THE PER-`H` DOOR GRADE** (`m4_spine_budget_collision_perH_at_Hlo`) —
the council's C2(ii) repair, REFUTED, permanently.  Replacing the register's single pinned `δ`
by a per-window-length grade `δ : ℕ → ℝ` changes nothing: the collision is arithmetic at ONE
`H`, and `H := R.Hlo` is in every regime's range, so the repaired register is contradictory
through its own bottom instance `δ R.Hlo`.  (What C2(ii) buys is decoupling `M` from the TOP
of the range — and the collision never used the top.) -/
theorem m4_spine_budget_collision_perH_at_Hlo {R : ChowlaRegime} {Cg C : ℝ}
    {δ Braw MSan MStr : ℕ → ℝ} {M : ℕ}
    (hCg : 1 ≤ Cg) (hC : 0 ≤ C) (hδ : 0 < δ R.Hlo)
    (hscale : H0scale C ≤ R.Hlo)
    (hMδ : 24 * Cg / δ R.Hlo ≤ (M : ℝ))
    (hMSan0 : 0 ≤ MSan R.Hlo) (hMStr0 : 0 ≤ MStr R.Hlo)
    (hdrift : ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 R.Hlo →
      (1 + 2 * Real.pi * (arcDen 12 R.Hlo / (q : ℝ))) ^ 2
          * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloor M)
              (fun H => 2 * MSan H) (fun H => 2 * MStr H) R.Hlo)) ≤ Braw R.Hlo)
    (hdel : Real.sqrt (Braw R.Hlo) ≤ mrtDeliveredGrade (C / 2) R.Hlo)
    (hrest : δ R.Hlo / 4 ≤ mrtDeliveredGrade (C / 2) R.Hlo)
    (hG1 : arcDen 12 R.Hlo ≤ MStr R.Hlo) :
    False :=
  m4_spine_budget_collision_at_Hlo (δ := δ R.Hlo) hCg hC hδ hscale hMδ hMSan0 hMStr0
    hdrift hdel hrest hG1

/-! ## §4 — ⟦WALL B⟧: THE ENDPOINT, ∀-QUANTIFIED OVER THE SHIFT

`M4DoorClose`'s ⟦THE ENDPOINT CONVENTION⟧ records `hend` as the ONE conjunct a consumer
discharges "by choosing `s`".  The register does not choose: it quantifies `∀ s ≤ ⌊H/d⌋ + 1`.
The two lemmas below make that demand explicit in the kernel. -/

set_option maxHeartbeats 1600000 in
-- the register is a 24-fold existential over a ~98-conjunct chain; the projection is a
-- straight-line search down the right spine of the `∧`-tree, no tactic search
/-- **THE ENDPOINT PROJECTION** (`doorRowCarriedT0_endpoint`).  Every instance of the
per-instance register asserts that the door's sieved χ-twisted datum VANISHES at the block
bottom `X_d`.  Its only discharge route is `X_d ∉ 𝒮`
(`M4Band.memSCoeff_eq_zero_of_not_memS`). -/
theorem doorRowCarriedT0_endpoint {Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ}
    {q : ℕ} {χ : DirichletCharacter ℂ q} {M Xd j : ℕ} {B : ℝ}
    (hreg : DoorRowCarriedT0 Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B) :
    doorChiCoeff χ M Xd = 0 := by
  obtain ⟨P, Q, Ddis, Mt, kk, Dd, Xa, X, hwin, δ', V, VJ, L, Cb, kmin, Ymax, εw, Xw, cqS,
    cgS, cW, SW, Rbar0, Dmask, hc⟩ := hreg
  repeat (first | exact hc.1 | replace hc := hc.2)

/-- **⟦WALL B⟧** (`m4_register_forces_endpoint_interval`).  ⟦THE FINAL REGISTER⟧'s per-instance
line — gate 11, at the `d = 1` instance — forces the sieved χ-twisted datum to vanish on a FULL
interval of `H + 2` consecutive integers at the bottom of every ladder block, at every window
length in range.  With `q = 1` (admissible: `1 ≤ arcDen 12 H`) there is no character zero
available, so the demand is `X_d ∉ 𝒮` for every one of those `H + 2` integers — while `𝒮` is
the Ramaré sieve, which keeps almost every integer.  The `s`-freedom `M4DoorClose`'s ⟦ENDPOINT
CONVENTION⟧ points at was spent by `M4Maximal.M4ChiDyadicRowMeanSq`'s own `∀ s`. -/
theorem m4_register_forces_endpoint_interval
    {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    {Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ}
    (hcar : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
        doorRowFloor M ≤ j → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H →
          ∀ s ≤ H / d + 1,
            DoorRowCarriedT0 Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
              (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H))
    {H : ℕ} (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi) {q : ℕ} (hq : 0 < q)
    (hqQ : (q : ℝ) ≤ arcDen 12 H) (χ : DirichletCharacter ℂ q) {i : ℕ} (hik : i < k)
    {j : ℕ} (hjL : j ≤ Nat.log 2 H) (hj0 : doorRowFloor M ≤ j) :
    ∀ s ≤ H + 1, doorChiCoeff χ M (doorLadder R.x H (i + 1) - 1 + s) = 0 := by
  intro s hs
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hd1 : ((1 : ℕ) : ℝ) ≤ arcDen 12 H := by
    have : (1 : ℝ) ≤ arcDen 12 H := le_trans hq1 hqQ
    simpa using this
  have hreg := hcar H hlo hhi q hq hqQ i hik χ j hjL hj0 1 (by norm_num) hd1 s
    (by simpa using hs)
  have hz := doorRowCarriedT0_endpoint hreg
  simpa using hz

/-! ## §GK — the G-lever twin (BLOCKED, no declarations)

Both of this file's `G`-reading declarations — `doorRowCarriedT0_endpoint` (:563) and
`m4_register_forces_endpoint_interval` (:578) — are stated at
`M4T0Discharge.DoorRowCarriedT0` and conclude about `M4WaveClosed.doorChiCoeff χ M`.  The
datum side has its twin (`doorChiCoeff_gk`, `M4WaveClosed` §GK); the REGISTER side does not:
`DoorRowCarriedT0` lives in `M4T0Discharge`, a file owned by another group, and carries no
`_gk` sibling yet.

So `doorRowCarriedT0_endpoint_gk` and `m4_register_forces_endpoint_interval_gk` cannot even
be STATED here.  They are flagged, not attempted; both proofs are pure projection/α-transport
and will transfer byte-for-byte once `DoorRowCarriedT0_gk` lands.

-- #audit (temporary)
-/

end Salt.MR
