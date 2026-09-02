/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16ComposeV4

/-!
# `XThread` — ⟦THE `x`-CEILING, THREADED⟧ AND `logChowla2_ineffective_v5`

⟦WHAT `v4` LEFT OPEN⟧  `S16ComposeV4.logChowla2_ineffective_v4` discharges the base-scale cap
at the raised lever `KlevF A`, but `KLever.s16_baseScaleCap96_L_at_klevF` wants the flat
builder's own OUTER-SCALE CEILING `log R.x ≤ (31/ε)·R.H₊` as an input, and the uniform lane does
not export it: `XCeil` landed it AT THE BUILDER
(`chowlaRegimeFlat_exists_param_gen_ceiling`) and banked the threading.  `v4` therefore carries
the ceiling as a conclusion-side ANTECEDENT.  This file spends the banked wave: the ceiling is
carried down every uniform hop (head → socket → doorL2 → road → capstone → conditional →
terminal), and `v5` is `v4` with that antecedent PROVEN INSIDE.

⟦THE PRICE, NAMED⟧ the ceiling is not free for an arbitrary caller: the builder's outer scale is
ENLARGED to `x ↦ max x (g H₊ ω)`, so a caller who asks for an astronomical `g` gets an
astronomical `x` and no export can prevent it.  The threading therefore trades the
conclusion-side ask for a hypothesis on the CALLER's own `g` — `XCeilRiderStrict` below.  That
is a strictly better bargain: the ask was about the regime the theorem PRODUCES (unverifiable by
the consumer), the rider is about the function the consumer SUPPLIES.

⟦THE GATE⟧ the rider cannot be a bare `∀ H₊ ω` bound, because the conditional hop substitutes
`g' := s15Arm δ₀ ρ + g` and `s15Arm` reads `ω` linearly — at an unconstrained `ω` no bound
survives.  `XCeilGate` is the constraint the builder's own regime satisfies and the rider is
allowed to assume: `H₊ ≥ 4·10^6`, `loglog H₊ ≥ 50`, and the width window
`log ω + ε²·H₊ ≤ (31/ε)·H₊`.  The last is a THEOREM about the produced regime — it is the
regime's own `hPHheadroom` (`8·(4^⌊ε²H₊⌋)²·ω ≤ x`) read against the ceiling, and the `ε²·H₊`
margin is precisely the `2·log(4^⌊ε²H₊⌋)` the majorant field spends.

⟦THE ONE GENUINE ESTIMATE⟧ §2's `s15Arm_log_le`: the compose's own arm satisfies
`log (s15Arm δ₀ ρ H₊ ω) ≤ log ω + H₊/10^6` on the gate.  The arm's binding summand is
`gArmDoorRho`'s `exp(exp(7000·loglog H + 500·log(1/ρ) + 6600))`, i.e. `(log H)^{7000}·ρ^{-500}
·e^{6600}` — the arithmetic heart is `7000·λ + C ≤ e^λ` at `λ = loglog H ≥ 50`, where
`e^{50} ≥ 3.6·10^{21}` against `7000·50 + 2.1·10^5 ≈ 5.6·10^5`: **fifteen orders of margin**.
The `ρ`-cost is bounded once and for all by the register's own constants
(`δ₀ ≥ 1/838400`, `Kc ≤ 2^539` give `1/ρ ≤ 2^580`, `log(1/ρ) ≤ 403`).

**PURELY ADDITIVE.**  Every statement and proof below is the landed one plus the rider
hypothesis and the ceiling conjunct; no landed declaration is touched.
-/

-- The head twin's core and the two cap-shuffle helpers are `private` in `S16Uniform`; they are
-- reached by `open private` (Batteries), the corpus's sanctioned device (`S16Compose` §1 does
-- the same) — no landed file gains a declaration.
open private spine_False_core_xi_sq_uniform uniformCap_arc uniformCap_shuffle from
  Salt.MR.S16Uniform

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.Entropy.Chowla

/-! ## §0 — ⟦THE GATE AND THE RIDER⟧ -/

/-- **⟦THE WIDTH GATE⟧** (`XCeilGate`) — the constraint on `(H₊, ω)` that the flat builder's own
regime satisfies, and that the caller's `g`-rider is therefore allowed to assume.

The third conjunct is the regime's `hPHheadroom` read against the outer-scale ceiling:
`8·(4^⌊ε²H₊⌋)²·ω ≤ x` and `log x ≤ (31/ε)·H₊` give
`log ω ≤ (31/ε)·H₊ − 2·⌊ε²H₊⌋·log 4 − log 8 ≤ (31/ε)·H₊ − ε²·H₊`. -/
def XCeilGate (eps : ℚ) (Hhi ω : ℕ) : Prop :=
  4000000 ≤ Hhi ∧ 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ)) ∧
    Real.log ((ω : ℕ) : ℝ) + (eps : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ)
      ≤ 31 / (eps : ℝ) * ((Hhi : ℕ) : ℝ)

/-- **⟦THE BUILDER-SIDE RIDER⟧** (`XCeilRider`) — what the flat builder needs of a caller's `g`
in order to EXPORT the outer-scale ceiling: on the gate, `g` itself sits inside the budget. -/
def XCeilRider (eps : ℚ) (g : ℕ → ℕ → ℕ) : Prop :=
  ∀ Hhi ω : ℕ, XCeilGate eps Hhi ω →
    Real.log ((g Hhi ω : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((Hhi : ℕ) : ℝ)

/-- **⟦THE CALLER-SIDE RIDER⟧** (`XCeilRiderStrict`) — the same bound with the `ε²·H₊` margin
kept in hand.  This is what `v5` asks of its caller, and the margin is exactly what pays for the
compose's own arm (§2) and the two `log 2`s of the sum splits. -/
def XCeilRiderStrict (eps : ℚ) (g : ℕ → ℕ → ℕ) : Prop :=
  ∀ Hhi ω : ℕ, XCeilGate eps Hhi ω →
    Real.log ((g Hhi ω : ℕ) : ℝ) + (eps : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ)
      ≤ 31 / (eps : ℝ) * ((Hhi : ℕ) : ℝ)

/-! ## §1 — ⟦THE FLAT BUILDER, EXPORTING THE CEILING⟧ -/

/-- **⟦THE HEAD-SHAPED FLAT BUILDER WITH THE CEILING EXPORTED⟧**
(`chowlaRegimeFlat_exists_param_head_xceil`) — `XCeil.chowlaRegimeFlat_exists_param_head_ceiling`
with the `max` COLLAPSED at the builder's own endpoint and width, off the caller's rider.

Unlike `KLever.chowlaRegimeFlat_exists_param_head_gceil` (which asks the rider at EVERY
`(H₊, ω)`), the rider here is asked only on `XCeilGate` — and the gate is discharged from the
regime's own fields, so no generality is lost and the `ω`-linear arm of §2 survives. -/
theorem chowlaRegimeFlat_exists_param_head_xceil (A : ℝ) (hA : 26 ≤ A) (eps : ℚ)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ) (g : ℕ → ℕ → ℕ)
    (hg : XCeilRider eps g) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      g R.Hhi R.ω ≤ R.x ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
  obtain ⟨R, hReps, hRA, hRHlo, hRcap, hRwid, hRx⟩ :=
    chowlaRegimeFlat_exists_param_gen_ceiling A hA eps heps heps1 Hlo₀
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
  have hgx : Real.log ((g R.Hhi R.ω : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) :=
    hg R.Hhi R.ω ⟨hHhi4, hll50, hωgate⟩
  refine ⟨regimeFlatEnlargeX R (le_max_left R.x (g R.Hhi R.ω)), hReps, hRA, hRHlo,
    le_max_right _ _, hRcap, hRwid, ?_⟩
  simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_Hhi]
  rcases le_total R.x (g R.Hhi R.ω) with h | h
  · rw [max_eq_right h]; exact hgx
  · rw [max_eq_left h]; exact hRx

end Salt.Entropy.Chowla

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §2 — ⟦THE ONE GENUINE ESTIMATE⟧ THE COMPOSE'S ARM, PRICED -/

/-- `6·10^{10} ≤ e^{25}` — the numeral `TowerFlatExport.flat_lambda_core` uses, re-derived
here so this file leans on no private helper. -/
private lemma xt_exp25 : (6e10 : ℝ) ≤ Real.exp 25 := by
  have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h : Real.exp (25 : ℝ) = (Real.exp 1) ^ (25 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have hc : (2.7 : ℝ) ^ (25 : ℕ) ≤ (Real.exp 1) ^ (25 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) he1.le 25
  have hn : (6e10 : ℝ) ≤ (2.7 : ℝ) ^ (25 : ℕ) := by norm_num
  linarith

set_option exponentiation.threshold 4000 in
/-- **⟦THE `ρ`-COST, BOUNDED ONCE⟧** (`xt_log_inv_rho_le`) — at the register's own constants
(`δ₀ ≥ 1/838400`, `0 < Kc ≤ 2^539`) the compose's `ρ = doorRhoOfDelta (s12DeltaSock δ₀ Kc)`
obeys `1/ρ ≤ 2^580`, hence `log (1/ρ) ≤ 403`.

The accounting: `ρ = min 1 (δ₀/(16·Kc·110525))` and
`δ₀/(16·Kc·110525) ≥ 1/(838400·16·110525·2^539) = 1/(1.4827·10^{12}·2^539) ≥ 2^{-580}`. -/
theorem xt_log_inv_rho_le {δ₀ Kc : ℝ} (hδ₀ : 0 < δ₀) (hδpin : 1 / 838400 ≤ δ₀)
    (hKc : 0 < Kc) (hKcb : Kc ≤ 2 ^ 539) :
    Real.log (1 / doorRhoOfDelta (s12DeltaSock δ₀ Kc)) ≤ 403 := by
  have hδs : 0 < s12DeltaSock δ₀ Kc := s12DeltaSock_pos hδ₀ hKc
  have hρpos : 0 < doorRhoOfDelta (s12DeltaSock δ₀ Kc) := doorRhoOfDelta_pos hδs.ne'
  have hp580 : (0 : ℝ) < 2 ^ (580 : ℕ) := by positivity
  have hp539 : (0 : ℝ) < 2 ^ (539 : ℕ) := by positivity
  have hsplit : (2 : ℝ) ^ (580 : ℕ) = 2 ^ (41 : ℕ) * 2 ^ (539 : ℕ) := by
    rw [← pow_add]
  have hlo : (1 : ℝ) / 2 ^ (580 : ℕ) ≤ doorRhoOfDelta (s12DeltaSock δ₀ Kc) := by
    rw [doorRhoOfDelta]
    refine le_min ?_ ?_
    · rw [div_le_one hp580]
      exact one_le_pow₀ (by norm_num)
    rw [s12DeltaSock_sq hδ₀ hKc, le_div_iff₀ (by norm_num : (0 : ℝ) < 110525),
      le_div_iff₀ (by positivity : (0 : ℝ) < 16 * Kc)]
    have hstep : 1 / (2 : ℝ) ^ (580 : ℕ) * 110525 * (16 * Kc)
        ≤ 1 / (2 : ℝ) ^ (580 : ℕ) * 110525 * (16 * 2 ^ (539 : ℕ)) := by
      have hc : (0 : ℝ) < 1 / (2 : ℝ) ^ (580 : ℕ) * 110525 * 16 := by positivity
      nlinarith [hKcb, hc]
    have hval : 1 / (2 : ℝ) ^ (580 : ℕ) * 110525 * (16 * 2 ^ (539 : ℕ))
        = 1768400 / 2 ^ (41 : ℕ) := by
      rw [hsplit]
      field_simp
      ring
    have hnum : (1768400 : ℝ) / 2 ^ (41 : ℕ) ≤ 1 / 838400 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 838400)]
      norm_num
    linarith
  have h1 : (1 : ℝ) / doorRhoOfDelta (s12DeltaSock δ₀ Kc) ≤ 2 ^ (580 : ℕ) := by
    rw [div_le_iff₀ hρpos]
    calc (1 : ℝ) = 2 ^ (580 : ℕ) * (1 / 2 ^ (580 : ℕ)) := by field_simp
      _ ≤ 2 ^ (580 : ℕ) * doorRhoOfDelta (s12DeltaSock δ₀ Kc) :=
        mul_le_mul_of_nonneg_left hlo hp580.le
  have h2 : Real.log (1 / doorRhoOfDelta (s12DeltaSock δ₀ Kc)) ≤ Real.log ((2 : ℝ) ^ (580 : ℕ)) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  push_cast at h2
  linarith [Real.log_two_lt_d9]

/-- **⟦THE `ρ`-CHARGE AT A SCALED `δ₀` PIN⟧** (`xt_log_inv_rho_le_scaled`) —
`xt_log_inv_rho_le` with the pin relaxed by a factor `c ≥ 1`.  The floor drops by exactly `c`,
so the charge rises by exactly `log c`: `ρ ≥ 1/(2^580·c)`, hence
`log(1/ρ) ≤ 580·log 2 + log c = 402.03 + log c`.

At the `h` lane's own pin (`c = h²`, wave X's exported `1/(838400·h²) ≤ δ₀`) and under the
`h`-family's binder `hh7 : log h ≤ 7`, `log c = 2·log h ≤ 14`, so the charge is at most `417`.
⛔ It is `2·log h` and NOT `4·log h`: the compose pins `doorRhoOfDelta (s12DeltaSock δ₀ Kc)`, and
`s12DeltaSock`'s square root (`S12Compose.lean:216`) exactly cancels `doorRhoOfDelta`'s square
(`M4ArithRho.lean:578`). -/
theorem xt_log_inv_rho_le_scaled {c δ₀ Kc : ℝ} (hc1 : 1 ≤ c) (hδ₀ : 0 < δ₀)
    (hδpin : 1 / (838400 * c) ≤ δ₀) (hKc : 0 < Kc) (hKcb : Kc ≤ 2 ^ 539) :
    Real.log (1 / doorRhoOfDelta (s12DeltaSock δ₀ Kc)) ≤ 403 + Real.log c := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hδs : 0 < s12DeltaSock δ₀ Kc := s12DeltaSock_pos hδ₀ hKc
  have hρpos : 0 < doorRhoOfDelta (s12DeltaSock δ₀ Kc) := doorRhoOfDelta_pos hδs.ne'
  have hp580 : (0 : ℝ) < 2 ^ (580 : ℕ) := by positivity
  have hp580one : (1 : ℝ) ≤ 2 ^ (580 : ℕ) := one_le_pow₀ (by norm_num)
  have hsplit : (2 : ℝ) ^ (580 : ℕ) = 2 ^ (41 : ℕ) * 2 ^ (539 : ℕ) := by rw [← pow_add]
  have hlo : (1 : ℝ) / (2 ^ (580 : ℕ) * c) ≤ doorRhoOfDelta (s12DeltaSock δ₀ Kc) := by
    rw [doorRhoOfDelta]
    refine le_min ?_ ?_
    · rw [div_le_one (by positivity)]
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 2 ^ (580 : ℕ) * c := mul_le_mul hp580one hc1 (by norm_num) (by positivity)
    rw [s12DeltaSock_sq hδ₀ hKc, le_div_iff₀ (by norm_num : (0 : ℝ) < 110525),
      le_div_iff₀ (by positivity : (0 : ℝ) < 16 * Kc)]
    have hstep : 1 / ((2 : ℝ) ^ (580 : ℕ) * c) * 110525 * (16 * Kc)
        ≤ 1 / ((2 : ℝ) ^ (580 : ℕ) * c) * 110525 * (16 * 2 ^ (539 : ℕ)) := by
      have hcpos : (0 : ℝ) < 1 / ((2 : ℝ) ^ (580 : ℕ) * c) * 110525 * 16 := by positivity
      nlinarith [hKcb, hcpos]
    have hval : 1 / ((2 : ℝ) ^ (580 : ℕ) * c) * 110525 * (16 * 2 ^ (539 : ℕ))
        = 1768400 / (2 ^ (41 : ℕ) * c) := by
      rw [hsplit]; field_simp; ring
    have hnum : (1768400 : ℝ) / (2 ^ (41 : ℕ) * c) ≤ 1 / (838400 * c) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hc0]
    linarith [hδpin]
  have h1 : (1 : ℝ) / doorRhoOfDelta (s12DeltaSock δ₀ Kc) ≤ 2 ^ (580 : ℕ) * c := by
    rw [div_le_iff₀ hρpos]
    calc (1 : ℝ) = (2 ^ (580 : ℕ) * c) * (1 / (2 ^ (580 : ℕ) * c)) := by field_simp
      _ ≤ (2 ^ (580 : ℕ) * c) * doorRhoOfDelta (s12DeltaSock δ₀ Kc) :=
        mul_le_mul_of_nonneg_left hlo (by positivity)
  have h2 : Real.log (1 / doorRhoOfDelta (s12DeltaSock δ₀ Kc))
      ≤ Real.log ((2 : ℝ) ^ (580 : ℕ) * c) := Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h2
  push_cast at h2
  linarith [Real.log_two_lt_d9]

/-- **⟦THE SUM SPLIT⟧** (`xt_log_add_le`) — `log (m + n) ≤ log 2 + B` whenever both summands are
under `B`, at natural arguments (`log 0 = 0` is handled, not assumed away). -/
theorem xt_log_add_le {m n : ℕ} {B : ℝ}
    (hm : Real.log ((m : ℕ) : ℝ) ≤ B) (hn : Real.log ((n : ℕ) : ℝ) ≤ B) :
    Real.log (((m + n : ℕ)) : ℝ) ≤ Real.log 2 + B := by
  have hB0 : (0 : ℝ) ≤ B := le_trans (Real.log_natCast_nonneg m) hm
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos (m + n) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    linarith
  · have hposR : (0 : ℝ) < ((m + n : ℕ) : ℝ) := by exact_mod_cast hpos
    rcases le_total ((m : ℕ) : ℝ) ((n : ℕ) : ℝ) with h | h
    · have hmn : m ≤ n := by exact_mod_cast h
      have hn0 : 0 < n := by omega
      have hn0R : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast hn0
      have hle : ((m + n : ℕ) : ℝ) ≤ 2 * ((n : ℕ) : ℝ) := by push_cast; linarith
      have hlog := Real.log_le_log hposR hle
      rw [Real.log_mul (by norm_num) hn0R.ne'] at hlog
      · linarith
    · have hmn : n ≤ m := by exact_mod_cast h
      have hm0 : 0 < m := by omega
      have hm0R : (0 : ℝ) < ((m : ℕ) : ℝ) := by exact_mod_cast hm0
      have hle : ((m + n : ℕ) : ℝ) ≤ 2 * ((m : ℕ) : ℝ) := by push_cast; linarith
      have hlog := Real.log_le_log hposR hle
      rw [Real.log_mul (by norm_num) hm0R.ne'] at hlog
      · linarith

set_option maxHeartbeats 2000000 in
-- the arm's four summands, the double exponential's collapse and the closing budget elaborate
-- in one block; the 2026-09-01 re-cut to `H₊/10^20` adds the tower step `u ≥ 8·10^41`, whose
-- constants are large enough that the block no longer fits the previous 1000000
/-- **⟦THE ARM, PRICED, AT A SCALED `δ₀` PIN⟧** (`s15Arm_log_le_scaled`) — the compose's own
`g`-arm costs, in logs, no more than `log ω + H₊/10^20` on the gate, at any pin
`1/(838400·c) ≤ δ₀` with `1 ≤ c ≤ 1201216` and `log c ≤ 14`.  `c = 1` is the landed lane
(`s15Arm_log_le`, below); `c = h²` is the `h` lane's, at `h ≤ e^7 = 1096`.

⟦THE ARITHMETIC HEART⟧ the binding summand is `gArmDoorRho`'s
`16·ω·(log H₊)^{12}·exp(exp(7000·loglog H₊ + 500·log(1/ρ) + 6600))`, whose log is
`log(16ω) + 12·loglog H₊ + (log H₊)^{7000}·ρ^{-500}·e^{6600}`.  With `λ := loglog H₊ ≥ 50` and
`log(1/ρ) ≤ 403` the exponent obeys `7000·λ + 207600 ≤ e^{λ}/2 = (log H₊)/2`, i.e. the whole
double exponential is at most `√H₊` — against a budget of `H₊/10^6`.  The margin at the floor is
`e^{50}/2 = 2.6·10^{21}` against `5.6·10^5`: **fifteen orders**. -/
theorem s15Arm_log_le_scaled {c δ₀ Kc : ℝ} (hc1 : 1 ≤ c) (hcb : c ≤ 1201216)
    (hlogc : Real.log c ≤ 14) (hδ₀ : 0 < δ₀) (hδpin : 1 / (838400 * c) ≤ δ₀)
    (hKc : 0 < Kc) (hKcb : Kc ≤ 2 ^ 539) {Hhi ω : ℕ} (hHhi : 4000000 ≤ Hhi)
    (hΛ : 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ Real.log ((ω : ℕ) : ℝ) + ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
  have hc0 : (0 : ℝ) < c := by linarith
  set ρ : ℝ := doorRhoOfDelta (s12DeltaSock δ₀ Kc) with hρdef
  have hδs : 0 < s12DeltaSock δ₀ Kc := s12DeltaSock_pos hδ₀ hKc
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρlog : Real.log (1 / ρ) ≤ 417 :=
    le_trans (xt_log_inv_rho_le_scaled hc1 hδ₀ hδpin hKc hKcb) (by linarith)
  -- ⟦THE SCALES⟧ `L = log H₊`, `Λ = loglog H₊`, and their two exponential witnesses
  set L : ℝ := Real.log ((Hhi : ℕ) : ℝ) with hLdef
  set Λ : ℝ := Real.log L with hΛdef
  have hHhiR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hHhi
  have hHhipos : (0 : ℝ) < ((Hhi : ℕ) : ℝ) := by linarith
  have hL0 : (0 : ℝ) ≤ L := Real.log_nonneg (by linarith)
  have hL1 : (1 : ℝ) < L := one_lt_log_of_loglog_ge hL0 (by norm_num : (0 : ℝ) < 50) hΛ
  have hΛ0 : (0 : ℝ) ≤ Λ := Real.log_nonneg hL1.le
  -- `v := e^{Λ/2}`, so `v² = L` and `v ≥ 6·10^{10}`
  set v : ℝ := Real.exp (Λ / 2) with hvdef
  have hvv : v * v = L := by
    rw [hvdef, ← Real.exp_add, show Λ / 2 + Λ / 2 = Λ by ring, hΛdef]
    exact Real.exp_log (by linarith)
  have hv : (6e10 : ℝ) ≤ v := by
    refine le_trans xt_exp25 ?_
    rw [hvdef]
    exact Real.exp_le_exp.mpr (by linarith)
  have hΛv : Λ ≤ 2 * (v - 1) := by
    have := Real.add_one_le_exp (Λ / 2)
    rw [← hvdef] at this
    linarith
  have hLbig : (3.6e21 : ℝ) ≤ L := by nlinarith [hvv, hv]
  -- `u := e^{L/2}`, so `u² = H₊`
  set u : ℝ := Real.exp (L / 2) with hudef
  have huu : u * u = ((Hhi : ℕ) : ℝ) := by
    rw [hudef, ← Real.exp_add, show L / 2 + L / 2 = L by ring, hLdef]
    exact Real.exp_log hHhipos
  have hLu : L ≤ 2 * (u - 1) := by
    have := Real.add_one_le_exp (L / 2)
    rw [← hudef] at this
    linarith
  have hu : (1.8e21 : ℝ) ≤ u := by linarith
  -- ⟦THE EXPONENT⟧ `E ≤ L/2`
  set E : ℝ := 7000 * Λ + 500 * Real.log (1 / ρ) + 6600 + 36 * 0 with hEdef
  have hE : E ≤ L / 2 := by
    rw [hEdef]
    nlinarith [hρlog, hΛv, hvv, hv]
  have hexpE : Real.exp E ≤ u := by
    rw [hudef]; exact Real.exp_le_exp.mpr hE
  -- ⟦THE ARM, BOUNDED⟧
  have hωnn : (0 : ℝ) ≤ ((ω : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlogωnn : (0 : ℝ) ≤ Real.log ((ω : ℕ) : ℝ) := Real.log_natCast_nonneg ω
  -- the `ρ`-arm's closed form
  have harc : arcDen 12 Hhi = Real.exp (12 * Λ) := by
    rw [arcDen, ← hLdef, Real.rpow_def_of_pos (by linarith), hΛdef]
    congr 1
    ring
  have hG : gArmDoorRho 0 0 ((ω : ℕ) : ℝ) ρ Hhi
      = 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by
    have hsplit : Real.exp (12 * Λ + Real.exp E)
        = Real.exp (12 * Λ) * Real.exp (Real.exp E) := Real.exp_add _ _
    have hnn : (0 : ℝ) ≤ 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ) * Real.exp (Real.exp E) := by
      positivity
    rw [gArmDoorRho, harc, ← hLdef, ← hΛdef, ← hEdef, max_eq_right hnn, hsplit]
    ring
  -- the sum, cast
  have hcast : ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
      = 2 * ((ω : ℕ) : ℝ) * (((Hhi : ℕ) : ℝ) + 2) + 8 * ((ω : ℕ) : ℝ)
        + ((⌈128 * ((ω : ℕ) : ℝ) / δ₀⌉₊ : ℕ) : ℝ)
        + ((⌈gArmDoorRho 0 0 ((ω : ℕ) : ℝ) ρ Hhi⌉₊ : ℕ) : ℝ) := by
    rw [s15Arm, s13GArm']
    push_cast
    ring
  have hceil1 : ((⌈128 * ((ω : ℕ) : ℝ) / δ₀⌉₊ : ℕ) : ℝ)
      ≤ 128 * 838400 * 1201216 * ((ω : ℕ) : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ 128 * ((ω : ℕ) : ℝ) / δ₀ := by positivity
    have hlt : ((⌈128 * ((ω : ℕ) : ℝ) / δ₀⌉₊ : ℕ) : ℝ) < 128 * ((ω : ℕ) : ℝ) / δ₀ + 1 :=
      Nat.ceil_lt_add_one h0
    have hdiv : 128 * ((ω : ℕ) : ℝ) / δ₀ ≤ 128 * 838400 * 1201216 * ((ω : ℕ) : ℝ) := by
      rw [div_le_iff₀ hδ₀]
      have hpin' : 1 / (838400 * 1201216 : ℝ) ≤ δ₀ := by
        refine le_trans ?_ hδpin
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [hcb, hc0]
      nlinarith [hωnn, hpin']
    linarith
  have hceil2 : ((⌈gArmDoorRho 0 0 ((ω : ℕ) : ℝ) ρ Hhi⌉₊ : ℕ) : ℝ)
      ≤ 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) + 1 := by
    rw [hG]
    have h0 : (0 : ℝ) ≤ 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by positivity
    linarith [Nat.ceil_lt_add_one h0]
  -- ⟦THE ENVELOPE⟧ `S ≤ (ω+1)·e^Y` at `Y = L + 12λ + e^E + 6`
  have hX1 : (1 : ℝ) ≤ Real.exp (12 * Λ + Real.exp E) :=
    Real.one_le_exp (by positivity)
  have hHhibig : (13 * 10 ^ 13 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by nlinarith [huu, hu]
  have he6 : (19 : ℝ) ≤ Real.exp 6 := by
    have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h : Real.exp (6 : ℝ) = (Real.exp 1) ^ (6 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    have hc : (2.7 : ℝ) ^ (6 : ℕ) ≤ (Real.exp 1) ^ (6 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he1.le 6
    have hn : (19 : ℝ) ≤ (2.7 : ℝ) ^ (6 : ℕ) := by norm_num
    linarith
  have hYeq : Real.exp (L + (12 * Λ + Real.exp E) + 6)
      = ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) * Real.exp 6 := by
    rw [Real.exp_add, Real.exp_add, hLdef, Real.exp_log hHhipos]
  have henv : ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
      ≤ (((ω : ℕ) : ℝ) + 1) * Real.exp (L + (12 * Λ + Real.exp E) + 6) := by
    rw [hcast, hYeq]
    have hfac : 2 * ((Hhi : ℕ) : ℝ) + 13 * 10 ^ 13
          + 16 * Real.exp (12 * Λ + Real.exp E)
        ≤ ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) * Real.exp 6 := by
      have h1 : 2 * ((Hhi : ℕ) : ℝ)
          ≤ 2 * (((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E)) := by
        nlinarith [hX1, hHhiR]
      have h2 : (13 * 10 ^ 13 : ℝ)
          ≤ ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by
        nlinarith [hX1, hHhibig]
      have h3 : 16 * Real.exp (12 * Λ + Real.exp E)
          ≤ 16 * (((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E)) := by
        nlinarith [hX1, hHhiR, Real.exp_pos (12 * Λ + Real.exp E)]
      have hprodnn : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by positivity
      nlinarith [h1, h2, h3, he6, hprodnn]
    have hstep : 2 * ((ω : ℕ) : ℝ) * (((Hhi : ℕ) : ℝ) + 2) + 8 * ((ω : ℕ) : ℝ)
        + (128 * 838400 * 1201216 * ((ω : ℕ) : ℝ) + 1)
        + (16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) + 1)
        ≤ (((ω : ℕ) : ℝ) + 1) * (2 * ((Hhi : ℕ) : ℝ) + 13 * 10 ^ 13
            + 16 * Real.exp (12 * Λ + Real.exp E)) := by
      nlinarith [hωnn, hX1, hHhiR, Real.exp_pos (12 * Λ + Real.exp E)]
    have hmul : (((ω : ℕ) : ℝ) + 1) * (2 * ((Hhi : ℕ) : ℝ) + 13 * 10 ^ 13
          + 16 * Real.exp (12 * Λ + Real.exp E))
        ≤ (((ω : ℕ) : ℝ) + 1)
          * (((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) * Real.exp 6) :=
      mul_le_mul_of_nonneg_left hfac (by linarith)
    linarith [hceil1, hceil2, hstep, hmul]
  -- ⟦THE LOG⟧
  rcases Nat.eq_zero_or_pos (s15Arm δ₀ ρ Hhi ω) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    have : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by positivity
    linarith
  · have hSpos : (0 : ℝ) < ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ) := by exact_mod_cast hpos
    have hlog := Real.log_le_log hSpos henv
    have hprod : Real.log ((((ω : ℕ) : ℝ) + 1) * Real.exp (L + (12 * Λ + Real.exp E) + 6))
        = Real.log (((ω : ℕ) : ℝ) + 1) + (L + (12 * Λ + Real.exp E) + 6) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
    -- `log(ω+1) ≤ log ω + log 2`
    have hω1 : Real.log (((ω : ℕ) : ℝ) + 1) ≤ Real.log ((ω : ℕ) : ℝ) + Real.log 2 := by
      rcases Nat.eq_zero_or_pos ω with hz | hz
      · rw [hz]
        simp only [Nat.cast_zero, Real.log_zero, zero_add, Real.log_one]
        linarith [Real.log_two_gt_d9]
      · have hω1R : (1 : ℝ) ≤ ((ω : ℕ) : ℝ) := by exact_mod_cast hz
        have hle : ((ω : ℕ) : ℝ) + 1 ≤ 2 * ((ω : ℕ) : ℝ) := by linarith
        have h := Real.log_le_log (by linarith : (0 : ℝ) < ((ω : ℕ) : ℝ) + 1) hle
        rwa [Real.log_mul (by norm_num) (by linarith), add_comm (Real.log 2)] at h
    -- the closing budget
    have hΛL : Λ ≤ L := by nlinarith [hΛv, hvv, hv]
    have hclose : Real.log 2 + (L + (12 * Λ + Real.exp E) + 6)
        ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
      -- ⟦THE TOWER STEP⟧ `u = e^{L/2} = (e^{L/4})² ≥ (1 + L/4)²`, so with `L ≥ 3.6·10^21`
      -- the linear witness `u ≥ 1.8·10^21` is upgraded to `u ≥ 8.1·10^41` — which is what
      -- buys the deeper cut `H₊/10^20` in place of `H₊/10^6`.  The headroom here is a TOWER
      -- (`XCeilGate` carries `50 ≤ loglog H₊`), so the extra fourteen orders are free.
      have hq := Real.add_one_le_exp (L / 4)
      have hq0 : (0 : ℝ) ≤ Real.exp (L / 4) := (Real.exp_pos _).le
      have hqL : (9 * 10 ^ 20 : ℝ) ≤ Real.exp (L / 4) := by linarith only [hq, hLbig]
      have hsq : Real.exp (L / 4) * Real.exp (L / 4) = u := by
        rw [← Real.exp_add, show L / 4 + L / 4 = L / 2 by ring, hudef]
      have hu41 : (8 * 10 ^ 41 : ℝ) ≤ u := by
        rw [← hsq]
        calc (8 * 10 ^ 41 : ℝ) ≤ (9 * 10 ^ 20) * (9 * 10 ^ 20) := by norm_num
          _ ≤ Real.exp (L / 4) * Real.exp (L / 4) :=
              mul_le_mul hqL hqL (by norm_num) hq0
      -- keep every step LINEAR in `u`: the one product is isolated in `hsquare`.
      have hupos : (0 : ℝ) < u := by linarith only [hu41]
      have hlin : L + 12 * Λ + Real.exp E + 6.7 ≤ 27 * u := by
        linarith only [hexpE, hΛL, hLu]
      have h27 : (27 : ℝ) * 10 ^ 20 ≤ u := by linarith only [hu41]
      have hsquare : 27 * u * 10 ^ 20 ≤ u * u := by
        have hm := mul_le_mul_of_nonneg_right h27 hupos.le
        linarith only [hm]
      have hstep : L + 12 * Λ + Real.exp E + 6.7 ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
        rw [← huu, le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 20)]
        linarith only [hlin, hsquare]
      linarith [Real.log_two_lt_d9]
    linarith [hlog, hprod, hω1, hclose]


/-- **⟦THE ARM, PRICED, AT THE LANDED PIN⟧** (`s15Arm_log_le`) — `s15Arm_log_le_scaled` at
`c = 1`.  ⭐ **RE-CUT 2026-09-01 (wave H1 word 2): the conclusion is now `H₊/10^20`, not
`H₊/10^6`.**  The estimate always had tower headroom (`XCeilGate` carries `50 ≤ loglog H₊`, so
`H₊ ≥ e^{e^{50}}` while the proof only ever spent `u ≥ 1.8·10^21`); the fourteen extra orders
are what let the `h` lane's relaxed `δ₀` pin `1/(838400·h²) ≤ δ₀` reach the same consumers.
Strictly stronger than the landed form — every `h = 1` consumer reaches it by `linarith`. -/
theorem s15Arm_log_le {δ₀ Kc : ℝ} (hδ₀ : 0 < δ₀) (hδpin : 1 / 838400 ≤ δ₀)
    (hKc : 0 < Kc) (hKcb : Kc ≤ 2 ^ 539) {Hhi ω : ℕ} (hHhi : 4000000 ≤ Hhi)
    (hΛ : 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ Real.log ((ω : ℕ) : ℝ) + ((Hhi : ℕ) : ℝ) / 10 ^ 20 :=
  s15Arm_log_le_scaled le_rfl (by norm_num) (by simp) hδ₀ (by simpa using hδpin) hKc hKcb hHhi hΛ

/-! ## §3 — ⟦THE FLAT HEAD, EXPORTING THE CEILING⟧ -/

/-- **⟦THE `A`-UNIFORM FLAT HEAD, `x`-CEILINGED⟧** (`flat_head_uniform_xceil`) —
`S16Compose.flat_head_uniform_ceiling` with the caller's rider as a hypothesis and the builder's
outer-scale ceiling as an exported conjunct.  The only proof edit is the builder hop:
`chowlaRegimeFlat_exists_param_head_xceil` in place of `chowlaRegimeFlat_exists_param_head`. -/
theorem flat_head_uniform_xceil :
    ∃ (ε : ℚ) (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 539 ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 26 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap = max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((bigXi R.eps H).card : ℝ) ≤ K) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            R.Hlo ≤ max Hcap (max extraFloor U1floor) ∧
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨cE, hcE, hcEge, H₀red, hred⟩ := hreduce_holds_final_bounded
  obtain ⟨cD3, hcD3, hcD3ge, H₀D3, hD3⟩ := primeWindow_sum_inv_ge_bounded
  obtain ⟨C, hC, hCcap, hcm⟩ := circle_method_estimate_sq_bounded (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- ⟦THE LEAF NUMERALS⟧ `log 4 = 2·log 2 < 1.3863`, hence `C ≤ 6.55`
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hCnum : C ≤ 655 / 100 := by
    rw [hlog4eq] at hCcap; linarith
  -- ⟦THE PIN⟧ `ε := 1/500`
  obtain ⟨ε, hεdef⟩ : ∃ e : ℚ, e = 1 / 500 := ⟨_, rfl⟩
  have hεR : ((ε : ℚ) : ℝ) = 1 / 500 := by rw [hεdef]; norm_num
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by rw [hεR]; norm_num
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := by
    rw [hεR, le_div_iff₀ (by positivity), hlog4eq]
    linarith
  have hε_half_lt : (ε : ℝ) < 1 / 2 := by rw [hεR]; norm_num
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := by
    rw [hεR, le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]; linarith
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := by
    rw [hεR, le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
  have hεQ1 : ε ≤ 1 / 2 := by rw [hεdef]; norm_num
  -- ⟦THE `δ₀` FLOOR⟧ the binding arm at its worst case
  have hδ₀ge : (1 : ℝ) / 838400 ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    have hkey : (5 : ℝ) / 2096 ≤ cD3 / (16 * C) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
    rw [hεR]; linarith
  -- ⟦THE ONE EDIT⟧ the count hook at the pin, carrying `Kc ≤ 2^539`
  obtain ⟨K, hK, hKb, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded_ceiling_of_pin ε hεdef
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = cD3 * (ε : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hcD3 hεR0) (by positivity)
  -- ⟦THE HEAD'S OWN FOUR-ARM FLOOR⟧ (flat) — `A`-FREE, which is the whole point
  obtain ⟨Hopq, hOpqdef⟩ : ∃ n : ℕ, n = max (max H₀red H₀D3) H₀xi := ⟨_, rfl⟩
  refine ⟨ε, K, cD3 / (16 * C) * (ε : ℝ) / 4, β, Hopq, hεQpos, hK, hKb,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num),
    hεdef.ge, hδ₀ge, hβpos, ?_⟩
  -- ⟦THE HOIST⟧ the landed proof chose `A := max A₀ (budgetAFlat ε β)` HERE
  intro A hA26 hAge
  obtain ⟨F, hFdef⟩ : ∃ n : ℕ, n = max Hopq (budgetFloorFlat (ε : ℝ) β A) := ⟨_, rfl⟩
  refine ⟨max (flatDesignFloor A) (max F (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), by rw [hFdef], ?_⟩
  intro extraFloor U1floor g₅ hg₅
  obtain ⟨Rf, hReps, hRA, hRHlo, hRg, _hRcapEq, hRwid, hRx⟩ :=
    chowlaRegimeFlat_exists_param_head_xceil A hA26 ε hεQpos hεQ1
      (max F (max extraFloor U1floor)) g₅ hg₅
  have hFlo : F ≤ Rf.Hlo := le_trans (le_max_left _ _) hRHlo
  have hxiHlo : H₀xi ≤ Rf.Hlo := by
    rw [hFdef, hOpqdef] at hFlo
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hFlo
  have hbudHlo : budgetFloorFlat (ε : ℝ) β A ≤ Rf.Hlo := by
    rw [hFdef] at hFlo; exact le_trans (le_max_right _ _) hFlo
  have hredHlo : max H₀red H₀D3 ≤ Rf.Hlo := by
    rw [hFdef, hOpqdef] at hFlo
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hFlo
  refine ⟨Rf.toChowlaRegime, hReps,
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, hRx, ?_,
    fun _ => hRwid, ?_, ?_⟩
  · -- ⟦THE EXPORTED COUNT GATE⟧ the road's `hXi`, at this head's own `ε`
    intro H' _ hlo' _
    rw [hReps]
    exact hxi H' (le_trans hxiHlo hlo')
  · -- ⟦THE CAP⟧ the flat base equation, shuffled onto the consumer's floors
    rw [_hRcapEq]
    exact uniformCap_shuffle _ _ _ _ _
  intro ρ _hρpos hρ hdoor hfail
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrementFlat Rf
  have hH4 : 4000000 ≤ H := le_trans Rf.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow Rf.eps H : liouvilleWindow H ; logMeasure Rf.x Rf.ω]
      ≤ (H : ℝ) / (Rf.A * Real.log H) := by
    rw [mutualInfo_window_comm_flat]; exact hMI
  have hepsc : (Rf.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max H₀red H₀D3 ≤ H := le_trans hredHlo hlo
  have hβR : cD3 * (Rf.eps : ℝ) / (144 * Real.log 4) = β := by rw [hReps, hβdef]
  have hAgeR : budgetAFlat (Rf.eps : ℝ) (cD3 * (Rf.eps : ℝ) / (144 * Real.log 4)) ≤ Rf.A := by
    rw [hβR, hReps, hRA]; exact hAge
  have hfloorH : budgetFloorFlat (Rf.eps : ℝ)
      (cD3 * (Rf.eps : ℝ) / (144 * Real.log 4)) Rf.A ≤ H := by
    rw [hβR, hReps, hRA]
    exact le_trans hbudHlo hlo
  obtain ⟨t, g, ht, hg, hgle, hbudget1⟩ :=
    hbudget1_witnessFlat Rf H cD3 C hcD3 hC
      (by rw [hReps]; exact le_of_lt hε_half_lt)
      (by rw [hReps]; exact hε_D3)
      (by rw [hReps]; exact hε_D3C) hhi hAgeR hfloorH
  -- ⟦THE K-FREE hbudget2⟧ `ρ ≤ c₀ε/4 < c₀ε`
  have hbudget2 : ρ < cD3 / (16 * C) * (Rf.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hρ, hpos]
  -- ⟦THE CORE⟧ at the FLAT threshold `κ = H/(A·log H)`
  exact spine_False_core_xi_sq_uniform Rf.toChowlaRegime hdoor cE hcE H₀red hred cD3 hcD3
    H₀D3 hD3 C hC hcm H hlo hhi hH₀ hepsc t g
    ((H : ℝ) / (Rf.A * Real.log H)) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail

/-! ## §4 — ⟦THE ROAD-FORM SOCKET, `x`-CEILINGED⟧ -/

/-- **⟦THE `A`-UNIFORM SPLIT SOCKET, `x`-CEILINGED⟧** (`flat_socket_uniform_xceil`) —
`S16Compose.flat_socket_uniform_ceiling` on §3's twin.  Body verbatim: the socket forwards the
head's regime, hence its ceiling, untouched. -/
theorem flat_socket_uniform_xceil :
    ∃ (ε : ℚ) (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 539 ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              (∀ (a e : ℕ → ℂ) (Bsieve : ℕ → ℝ) (Binsert : ℝ),
                (∀ m, lamCoeff m = a m + e m) →
                (∀ H : ℕ, 0 ≤ Bsieve H) →
                (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
                  NearRatTight (arcDen 12 H) H α →
                    (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                      ≤ Bsieve H * (H : ℝ) ^ 2) →
                (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
                  (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
                    ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                      ∂(logMeasure R.x R.ω)) ≤ Binsert) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  K * (2 * Bsieve H) + 2 * Binsert ≤ δ₀) →
                ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨ε, K, δ₀, β, Hopq, hε, hK, hKb, hδ₀, hεpin, hδpin, hβ, hhead⟩ :=
    flat_head_uniform_xceil
  obtain ⟨H₀, hH₀⟩ := sum_bigXi_norm_windowExpSum_sq_le_twelve ε hε
  refine ⟨ε, K, δ₀, β, max Hopq H₀, hε, hK, hKb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro A hA162 hAge
  obtain ⟨Hcap, hCapEq, hhd⟩ := hhead A (by linarith) hAge
  refine ⟨max Hcap H₀, by rw [hCapEq]; exact uniformCap_arc _ _ _ _ _, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, _, hRU1, hRg, hRx, hcount, hRtow, hRcap, hR⟩ :=
    hhd 0 (max U1floor H₀) g hg
  have hU1 : U1floor ≤ R.Hlo := le_trans (le_max_left _ _) hRU1
  have harc : H₀ ≤ R.Hlo := le_trans (le_max_right _ _) hRU1
  refine ⟨R, hReps, hU1, hRg, hRx, hRtow, le_trans hRcap (by omega), ?_⟩
  intro a e Bsieve Binsert hsplit hB0 hsock hins hρ
  refine hR δ₀ hδ₀ le_rfl ?_
  intro H _ hlo hhi
  exact le_trans (hH₀ R hReps harc a e Bsieve K Binsert hsplit hB0 hsock hcount hins
    H hlo hhi) (hρ H hlo hhi)

/-! ## §5 — ⟦THE CLOSED LOOP, `K`-HOISTED AND `x`-CEILINGED⟧ -/

/-- **⟦THE `A`-UNIFORM CLOSED LOOP, `K`-HOISTED, `x`-CEILINGED⟧**
(`flat_doorL2_uniform_xceil_khoist`) — `S16ComposeV4.flat_doorL2_uniform_ceiling_khoist` on §4's
twin.  Body verbatim. -/
theorem flat_doorL2_uniform_xceil_khoist :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 539 ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
                M4DoorGates_L_gk K Cg R M k δ →
                (∀ H : ℕ, 0 ≤ Braw H) →
                M4SievedDoorSq_L_gk K R M Braw →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                  ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  obtain ⟨ε, Kb, δ₀, β, Hopq, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, hsk⟩ :=
    flat_socket_uniform_xceil
  refine ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge
  obtain ⟨Hcap, hCapLe, hexit⟩ := hsk A hA162 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hR⟩ := hexit U1floor g hg
  refine ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, ?_⟩
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  have hA : 1 ≤ AdoorL M := one_le_AdoorL hgates.hM
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
    intro H hhi
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  refine hR (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2
      liouvilleC)
    (fun m => lamCoeff m - memSCoeff (calP (AdoorL M) (s13GK K M))
      (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC m)
    Braw (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) (fun m => by ring) hBraw0
    (hsock m4_bandTransport) ?_ ?_
  · intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (AdoorL M) (s13GK K M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · intro H hlo hhi
    rw [l2_budget_line Kb (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * Kb * Braw H ≤ 2 * Kb * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

/-! ## §6 — ⟦THE TERMINAL REGISTER, `K`-HOISTED AND `x`-CEILINGED⟧ -/

/-- **⟦THE `A`-UNIFORM TERMINAL REGISTER, `K`-HOISTED, `x`-CEILINGED⟧**
(`flat_road_uniform_xceil_khoist`) — `S16ComposeV4.flat_road_uniform_ceiling_khoist` on §5's
twin.  Body verbatim. -/
theorem flat_road_uniform_xceil_khoist :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 539 ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
                M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
                (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
                (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                    ≤ Braw H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                M4ChiSummedFreeRow_L_gk K R M RS →
                  ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, hdoor⟩ :=
    flat_doorL2_uniform_xceil_khoist
  refine ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hdoor K A hA162 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hR⟩ := hmain U1floor g hg
  refine ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  have harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    nlinarith [h1, harc1]
  have harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 2 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    nlinarith [h1, harc1]
  have hchi : M4ChiSummedBlockMeanSqN_L_gk K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied_L_gk K j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummed_L_gk K (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  have hcov := m4_cover_assembly_blk2_L_gk K hgates hBblk0 hblk2
  refine hR Braw Bceil δ M k hgates hBraw0 ?_ hceil hbudget
  refine m4_sievedDoorSq_of_blk2_L_gk K (ℓ := blockLen)
    (fun H => by have := hBblk0 H; positivity)
    (fun H q _ _ _ _ => one_le_blockLen H q) ?_ ?_ ?_ ?_ hcov
  · intro H q hlo hhi _ _
    have h1 := harc H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hH1 : 1 ≤ H := by
      have : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
      exact_mod_cast this
    exact blockLen_le H q hH1
  · intro H q hlo hhi _ _
    exact blockLen_narrow (R := R) hlo (harc H hlo hhi)
  · intro H q hlo hhi hq _
    exact blockLen_drift (R := R) hlo hq (harc H hlo hhi)
  · intro H hlo hhi
    have h := hdrift H hlo hhi
    have hres0 : (0 : ℝ) ≤ strataResidual H :=
      strataResidual_nonneg (one_le_arcDen_of_regime (R := R) hlo)
    have hB := hBcl0 H
    nlinarith [h]


/-! ## §7 — ⟦THE CAPSTONE, `K`-HOISTED AND `x`-CEILINGED⟧ -/

set_option maxHeartbeats 1600000 in
-- Same cause as the landed original: the ~90-line conclusion re-elaborates under the extra
-- `∀ K`/`∃ Ct` bracket.
/-- **⟦THE `A`-UNIFORM CAPSTONE, WINDOWED, WIDE-CEILINGED, `K`-HOISTED, `x`-CEILINGED⟧**
(`flat_capstone_uniform_win_xceil_kwide_khoist`) —
`S16ComposeV4.flat_capstone_uniform_win_ceiling_kwide_khoist` on §6's twin.  Body verbatim: the
capstone forwards the road's regime and the caller's `g` untouched, so it forwards the ceiling
and the rider untouched too. -/
theorem flat_capstone_uniform_win_xceil_kwide_khoist (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_winU Awin) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g →
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
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
                        4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                          (fun H => 2 * rStrWitness H) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
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
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hKcb, hδ₀, hεpin, hδpin, hβ, hroadU⟩ :=
    flat_road_uniform_xceil_khoist
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
  obtain ⟨Ct, hCt, hCtb, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_L_gk_ceiling_kwide K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hroad⟩ := hroadU K A hA26 hAge
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g hg
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRx, hRtow, by omega, ?_⟩
  intro M hMfloor hKw
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit K M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
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
  have hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_L_gk K R M
      (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho_L M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
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
    have hG := g2_of_j0_floor H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
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


/-! ## §8 — ⟦THE CONDITIONAL, `K`-HOISTED AND `x`-CEILINGED⟧ THE ESTIMATE, SPENT -/

set_option maxHeartbeats 1600000 in
-- Same cause as the landed original: the capstone's monster body is consumed under one more
-- binder layer.
/-- **⟦THE FLAT CONDITIONAL, WINDOWED, WIDE-CEILINGED, `K`-HOISTED, `x`-CEILINGED⟧**
(`flat_conditional_uniform_win_xceil_kwide_khoist`) — §7 under
`S16ComposeV4.flat_conditional_uniform_win_ceiling_kwide_khoist`'s body.

**THIS IS THE ONLY HOP THAT MOVES `g`**: the compose substitutes
`g' := fun H₊ ω => s15Arm δ₀ ρ H₊ ω + g H₊ ω`, so it is here that the caller's STRICT rider is
spent and the builder-side rider re-established.  §2's `s15Arm_log_le` prices the arm at
`log ω + H₊/10^6`; the gate's own width window supplies `log ω ≤ (31/ε)·H₊ − ε²·H₊`; and
`ε ≥ 1/500` makes the margin `ε²·H₊ ≥ 4·H₊/10^6` — enough for the arm, the sum split's `log 2`,
and `3·H₊/10^6 ≥ 12` to spare.  Everything else is the landed body. -/
theorem flat_conditional_uniform_win_xceil_kwide_khoist (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_winU Awin) :
    ∃ (ε : ℚ) (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRiderStrict ε g →
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ M : ℕ,
                S15Sel''_L_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                 K ≤ 170000000 * M →
                S15CrossingBound_L_gk K R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, β, x₀, Hopq, Mfl, hCg, hε, hKc, hδ₀, hMfl,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, hcapU⟩ :=
    flat_capstone_uniform_win_xceil_kwide_khoist Awin hband
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcapK⟩ := hcapU K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapK A hA26 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦THE ONE GENUINE ESTIMATE, SPENT⟧ the substituted `g' = s15Arm δ₀ ρ + g` still obeys the
  -- builder-side rider: §2 prices the arm at `log ω + H₊/10^6` and the caller's own `ε²·H₊`
  -- margin (`≥ 4·H₊/10^6` at `ε ≥ 1/500`) pays for it AND for the sum split's `log 2`
  have hεR : (1 : ℝ) / 500 ≤ (ε : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hεpin
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
    exact h
  have hg' : XCeilRider ε (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω) := by
    intro Hhi ω hgate
    obtain ⟨hH4, hll, hωw⟩ := hgate
    have hHhiR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hH4
    have hε2 : (1 : ℝ) / 250000 ≤ (ε : ℝ) ^ 2 := by
      nlinarith [hεR, sq_nonneg ((ε : ℝ) - 1 / 500)]
    have hεsq : 4 * ((Hhi : ℕ) : ℝ) / 1000000 ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hε2 (le_trans (by norm_num) hHhiR)
      linarith
    have harm : Real.log ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
        ≤ Real.log ((ω : ℕ) : ℝ) + ((Hhi : ℕ) : ℝ) / 1000000 := by
      rw [hρdef, hδsdef]
      -- the re-cut estimate is STRICTLY STRONGER; this consumer still spends only `H₊/10^6`
      refine le_trans (s15Arm_log_le hδ₀ hδpin hKc hKcb hH4 hll) ?_
      have : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by positivity
      linarith
    have hgb := hg Hhi ω ⟨hH4, hll, hωw⟩
    have hlog2 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
    have harm' : Real.log ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - 3 * ((Hhi : ℕ) : ℝ) / 1000000 := by linarith
    have hgb' : Real.log ((g Hhi ω : ℕ) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - 3 * ((Hhi : ℕ) : ℝ) / 1000000 := by linarith
    have hsum := xt_log_add_le harm' hgb'
    have hslack : Real.log 2 ≤ 3 * ((Hhi : ℕ) : ℝ) / 1000000 := by linarith
    exact le_trans hsum (by linarith)
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω) hg'
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
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
  refine ⟨R, hReps, hHlo, hRgg, hRx, hRtow, ?_⟩
  intro M hsel hKw
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
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the LINEAR anchor
  have harith := s15_doorArithFrameRho_L_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register⟧
  have hgate : S13BandGate'_L_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_L_gk K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_gen le_rfl (s13_g2_jfloor_of_MSelect'_L_gk K (by linarith) hS))
    (s13_gate8_L_gk le_rfl (s13_gate8_of_MSelect'_L_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_L_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket_L hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorL_gk K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hlam50 htow
        hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM (hgate.block H L q j A s hb)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_L_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith


/-! ## §9 — ⟦THE FLAT LINEAR TERMINAL `v2`, `K`-HOISTED AND `x`-CEILINGED⟧ -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 1600000 in
-- Same cause as the landed original: the hoisted prefix plus the three window discharges
-- re-elaborate the terminal's conclusion.
/-- **⟦THE FLAT LINEAR TERMINAL `v2`, `A`-UNIFORM, WINDOWED, PRICED, `K`-HOISTED, `x`-CEILINGED⟧**
(`logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_khoist`) —
`S16ComposeV4.logChowla2_witnessed_scale_flat_L_v2_uniform_win_ceiling_khoist` on §8's twin.  The
regime it hands out now carries the flat builder's own outer-scale ceiling, which is exactly the
input `KLever.s16_baseScaleCap96_L_at_klevF` was missing.  Body verbatim. -/
theorem logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_khoist (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_winU Awin) :
    ∃ (ε : ℚ) (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ (Ct Cq cs T₀ Kq Ks C : ℝ),
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
        ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
          K ≤ 170000000 * flatDoorM A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          Real.exp (-100) ≤ cs →
          T₀ ≤ Real.exp (Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ) / 2) →
          Real.exp (-100) ≤ Ks →
          ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            (S16CofactorSupply_L_gk K Cq R (flatDoorM A) →
              S16BaseScaleCap96_L_gk K R (flatDoorM A) →
                ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, hcondU⟩ :=
    flat_conditional_uniform_win_xceil_kwide_khoist Awin hband
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  obtain ⟨_Ct0, -, -, hcond0⟩ := hcondU 0
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond0 (max 162 (budgetAFlat (ε : ℝ) β)) (le_max_left _ _) (le_max_right _ _)
  -- the `ε`-probe's own `g ≡ 0` obeys the strict rider trivially (`log 0 = 0`, and the gate's
  -- width window already carries the `ε²·H₊` margin)
  have hzero : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := by
    intro Hhi ω hgate
    obtain ⟨-, -, hωw⟩ := hgate
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [Real.log_natCast_nonneg ω]
  obtain ⟨R0, hR0eps, -, -, -, -, -⟩ :=
    hbody0 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) hzero le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have hεR : (1 : ℝ) / 500 ≤ (ε : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hεpin
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
    exact h
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKqb, hKs0, hC0, hC40, hsupply⟩ :=
    s15_crossing_supplied_L_gk_ceiling_sharpT0 K
  refine ⟨Ct, Cq, cs, T₀, Kq, Ks, C, hCt, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro A hA26 hAwin hAge hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge
  refine ⟨fun hopq => flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hx0win hopq hcs hT₀ hKs g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g hg (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  -- ⟦THE REGISTER, SUPPLIED⟧ at the flat design modulus, at the CALLER's lever
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by
    rw [hReps]
    have : (1 : ℚ) / 2 ^ 9 ≤ 1 / 500 := by norm_num
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win (c := 1) hA26 K hKw (by norm_num) (by norm_num) (by simp) hδ₀ (by simpa using hδpin) hKc hKcb
    hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win (by simpa using heps) hlo hwin
  -- ⟦THE CROSSING, SUPPLIED⟧ the block floor off the register's own `blk` line
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk K (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel hKw
    (hsupply hcs hKqb hKs R (flatDoorM A) hM1 hfl (by rw [hHlo]; exact hT₀) hblk hcof hcapsc)


/-! ## §10 — ⟦THE INEFFECTIVE LIMIT, `v5`⟧ THE `x`-CEILING IS A THEOREM -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 800000 in
-- Same cause as `v4`: the `∃`-prefix and the four window discharges re-elaborate the
-- conclusion under the raised lever.
/-- **⟦THE INEFFECTIVE LIMIT, `v5`⟧** (`logChowla2_ineffective_v5`) — `v4` with the outer-scale
ceiling **PROVEN INSIDE** instead of asked for.

⟦WHAT `v5` IS⟧ for every depth `A₀` there are a design constant `A ≥ max(162, A₀)` and a Chowla
regime whose window base is `⌈e^{e^{3.2A}}⌉` — depth unbounded — such that, granted three
numeric facts about three constants the theorem itself produces and ONE property of the caller's
own outer-scale request `g`, the log-averaged two-point Chowla correlation does not fail at the
witnessed scale unless the co-factor register is empty.  No Siegel window, no `x₀` arm, no
`Hopq` arm, no band-lane rider, no `Kc`/`Ct`/`Kq` numeral, **no base-scale cap**, and **no
outer-scale ask**.

⟦WHAT CHANGED FROM `v4`⟧ `v4` carried
`Real.log R.x ≤ (31/R.eps)·R.H₊` as a CONCLUSION-SIDE antecedent, because the uniform lane did
not export the flat builder's own ceiling — X-CEIL landed it at the builder and banked the
threading.  §§1–9 above spend that wave: the ceiling is carried down every hop and `v5`
discharges `KLever.s16_baseScaleCap96_L_at_klevF`'s fourth input from the terminal's own EXPORT.
The antecedent is GONE from the statement.

⟦WHAT IT COST, NAMED⟧ one hypothesis on the CALLER's `g`: `XCeilRiderStrict ε g`, i.e. on the
gate (`H₊ ≥ 4·10^6`, `loglog H₊ ≥ 50`, and the builder's own width window
`log ω + ε²·H₊ ≤ (31/ε)·H₊`) the request obeys `log (g H₊ ω) + ε²·H₊ ≤ (31/ε)·H₊`.  This is not
a weakening in disguise: the flat builder ENLARGES its outer scale to `max x (g H₊ ω)`, so a
caller asking for an astronomical `g` really does get an astronomical `x`, and no theorem can
export a ceiling without constraining it.  The trade is strictly favourable — `v4` asked for a
property of the regime it PRODUCES (which its consumer cannot check), `v5` asks for a property
of the function its consumer SUPPLIES.  The budget `(31/ε)·H₊ ≥ 15500·H₊` is enormous: the
builder's own scale sits at `log x ≈ 1.386·ε²·H₊`, nine orders inside it.

⟦THE SURVIVING LIST, EXACT AND COMPLETE⟧ **outer: NOTHING** (the caller supplies only `A₀`).
Inner: three numeral riders on constants this theorem produces, plus the caller's own `g`-rider —

* `e^{-100} ≤ cs` — **satisfied at the corpus's own witness**: `cs = 3.716·10^{-11}` against
  `e^{-100} = 3.72·10^{-44}`, 33 orders, kernel-pinned at
  `RiderTrace.cs_closed_form_ge_exp_neg_hundred`.  Carried, not discharged.
* `T₀ ≤ exp(√(flatDesignBase A)/2)` — the RESHAPED rider (COMPOSE-2's 8/02 second repair), the
  sole consumer's TRUE tolerance.  Satisfiable at the corpus's own witness by two exponential
  levels (`e^{½·e^{6.4·10^{224}}}` allowed against `T₀ ≈ e^{e^{1251}}`).
* `e^{-100} ≤ Ks` — the Siegel-genre remnant, the field's own caveat.
* `XCeilRiderStrict ε g` — the caller's outer-scale request, discussed above.  It is met by
  every `g` the corpus's own consumers use (`g ≡ 0`, and the compose's own arm, which §8 proves
  fits with `3·H₊/10^6` to spare).

Conclusion-side, at the RAISED lever, exactly ONE item survives:

* `S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A)` — the co-factor debt, carried exactly as
  in `v3`/`v4` but now alone.  COFACTOR-BULK instantiated it end-to-end from a named 17-conjunct
  register (`cofkL_cofactorSupply_L_gk_of_bulk`, `K`-parametric, so the `KlevF A` instance is
  immediate); what is NOT closed is that register's inhabitation at the flat scale and its
  symbolic-`K_vt` cushion, so nothing is gained by trading one named predicate for two.

⟦THE THREE 8/02 REPAIRS, ALL LANDED⟧ the base-scale cap (a theorem at the raised lever, predicate
deleted), the mis-sized `T₀` numeral (replaced by the consumer's tolerance), and now the
outer-scale ceiling (threaded, ask deleted).  What remains conditional is ONE named predicate and
four riders, and every one of them is either satisfied at the corpus's own witness or an open
debt the ledger already carries. -/
theorem logChowla2_ineffective_v5 (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      (Real.exp (-100) ≤ cs →
        T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) →
        Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  -- ⟦RIDER 0, DISCHARGED⟧ the band lane's own constant, at its own window — ONE witness for
  -- EVERY lever, which is what lets the design constant be chosen before the lever is
  obtain ⟨Awin, -, hband⟩ := s16_bandLaneWinL_holdsU
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hmainU⟩ :=
    logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_khoist Awin hband
  -- ⟦THE CLASSICAL LIMIT⟧ the design constant, chosen ABOVE all four fixed constants — and
  -- BEFORE the lever, which is legal exactly because `ε`, `β`, `x₀`, `Hopq`, `Awin` are `K`-free
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (max (max A₀ 162) Awin)
      (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))) := ⟨_, rfl⟩
  have hA162 : (162 : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hA₀A : A₀ ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hAwinA : Awin ≤ A := by
    rw [hAdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    rw [hAdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  -- ⟦RIDER 3, DISCHARGED⟧ the `x₀` window
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
    have h2 : Real.exp (3.2 * A) / 10 + 1 ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
      Real.add_one_le_exp _
    linarith
  -- ⟦RIDER 4, DISCHARGED⟧ the arm census
  have hopq : Hopq ≤ flatDesignBase A := by
    have h2 : Real.exp (3.2 * A) + 1 ≤ Real.exp (Real.exp (3.2 * A)) := Real.add_one_le_exp _
    have hR : ((Hopq : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by linarith
    have hceil := le_trans hR (Nat.le_ceil (Real.exp (Real.exp (3.2 * A))))
    rw [flatDesignBase]; exact_mod_cast hceil
  -- ⟦THE RAISED LEVER⟧ chosen AFTER `A`, admissible inside the register's own wide ceiling
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, Cq, cs, T₀, Kq, Ks, C, hCt, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40, hmain⟩ :=
    hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hKw
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A, ?_⟩
  intro hcs hT₀ hKs g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq hcs (by rw [hbase hopq]; exact hT₀) hKs g hg
  refine ⟨R, hReps, by rw [hHlo]; exact hbase hopq, hRg, hRtow, hdes, hwin, ?_⟩
  intro hcof
  -- ⟦ITEM 3, DISCHARGED⟧ the base-scale cap at `K = KlevF A`, a THEOREM off the builder's two
  -- exported ceilings — and the `x`-ceiling is now the terminal's own EXPORT, not an ask
  have heps500 : (1 : ℚ) / 500 ≤ R.eps := by rw [hReps]; exact hεpin
  have hxceil : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [hReps]; exact hRx
  exact hfire2 hcof
    (s16_baseScaleCap96_L_at_klevF hA26 (flatDoorM_one_le hA26) heps500 hxceil hwin)

end Salt.MR

end
