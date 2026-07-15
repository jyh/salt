/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.AssembleA3
import Salt.Chen.AssembleA3b
import Salt.Chen.AggSum
import Salt.Chen.AggCE
import Salt.Chen.AggDiag
import Salt.Chen.PriceClose
import Salt.Chen.PDiag
import Salt.Chen.SwitchW
import Salt.Chen.HeadlineW2
import Salt.Chen.GlueNormalized
import Salt.Chen.RazorClose
import Salt.Chen.CountW
import Salt.Chen.WLower
import Salt.Chen.Assembly
import Salt.Chen.GlueFinal
import Salt.Chen.H4Cond

/-!
# fin8c — THE COMPOSITION → `chen_headline`

Design: `docs/blueprints/flags.md` (the `fin8b`/`fin8c` entries, the SYMLOW input inventory).
This file composes the landed operating-point suppliers into the Chen headline:

  `chen_headline : {p : ℕ | p.Prime ∧ IsP2 2 (p + 2)}.Infinite`.

The plan (per the fin8c mandate):
1. `op_floors` — the mechanical rpow floors at the operating values (from `opf_tower`).
2. `hBVblocksW_at_op` → `a12_hA3` — the block-remainder discharge fed through the
   `mainA3_of_block_remainders_W` route.
3. the ledger via `normalized_package` / `hledger_at_certs`.
4. the 12 conjuncts → `chen_of_hypotheses_W` → `chen_headline`.

Only `[propext, Classical.choice, Quot.sound]`; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## Step 1 — the `op_floors` bundle (the mechanical rpow floors at the operating values)

The conductor `D := opQ · opDlev x` and the band floor `opZ x · opY x`, framed for the
`box_price_at_op`/`sym_price_at_op`/`low_price_at_op` conductor range
(`x^{11/24}/8 ≤ D ≤ x^{499/1000}`) and the band `F`-floor (`x^{11/24}/8 ≤ opZ·opY`,
`2 ≤ opZ·opY`), plus the window floor `x^{1/3}/8 ≤ opY x`.  Derived from `opf_tower`
(`opDlev x ≥ x^{496/1000}`, `opQ ≤ log x`, `opZ·opY ≥ x^{11/24}/4` via `zy_floor_ge`) and the
polylog-beats-power threshold `log x ≤ x^{1/500}` (`a12_logpow_le_rpow`) for the `D`-upper bound
`opQ · opDlev x ≤ log x · x^{497/1000} ≤ x^{499/1000}`. -/
theorem op_floors : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((opQ * opDlev x : ℕ) : ℝ)
      ∧ ((opQ * opDlev x : ℕ) : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000)
      ∧ (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((opZ x * opY x : ℕ) : ℝ)
      ∧ 2 ≤ opZ x * opY x
      ∧ (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (opY x : ℝ) := by
  obtain ⟨xt, _hxt8, htower⟩ := opf_tower
  obtain ⟨xl, hxl⟩ := a12_logpow_le_rpow 1 (1 / 500) (by norm_num) (by norm_num)
  refine ⟨max (max (max xt xl) (10 ^ 48)) ⌈Real.exp 200⌉₊, fun x hx => ?_⟩
  have hxt' : xt ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxl' : xl ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx48 : 10 ^ 48 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hexp200 : Real.exp 200 ≤ (x : ℝ) := by
    have h1 : ⌈Real.exp 200⌉₊ ≤ x := le_trans (le_max_right _ _) hx
    calc Real.exp 200 ≤ (⌈Real.exp 200⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (x : ℝ) := by exact_mod_cast h1
  have hxR : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hxR
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hxR
  obtain ⟨hQlog, _hwz, _hw'z, hz3, _hzD, _hD1, hzy, _hyx2, _hyx, _hStop1, _hStop3, _hDlev2,
    _hDx, hDlev496, _hA3mem, _hDlevx2, _hx4⟩ := htower x hxt'
  have hlogx : Real.log x ≤ (x : ℝ) ^ ((1 : ℝ) / 500) := by
    have := hxl x hxl'; rwa [Real.rpow_one] at this
  have hQ1R : (1 : ℝ) ≤ (opQ : ℝ) := by exact_mod_cast opf_Q_pos
  -- the two `D`-floor rows for `D = opQ · opDlev x`
  have hDcast : ((opQ * opDlev x : ℕ) : ℝ) = (opQ : ℝ) * (opDlev x : ℝ) := by
    push_cast; ring
  have hDlevub : (opDlev x : ℝ) ≤ (x : ℝ) ^ ((497 : ℝ) / 1000) := by
    rw [opDlev]; exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
  have hDlow : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((opQ * opDlev x : ℕ) : ℝ) := by
    rw [hDcast]
    have h1 : (x : ℝ) ^ ((11 : ℝ) / 24) ≤ (x : ℝ) ^ ((496 : ℝ) / 1000) :=
      Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num)
    have h2 : (x : ℝ) ^ ((496 : ℝ) / 1000) ≤ (opDlev x : ℝ) := hDlev496
    have h3 : (0 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) := Real.rpow_nonneg hxpos.le _
    have h4 : (opDlev x : ℝ) ≤ (opQ : ℝ) * (opDlev x : ℝ) :=
      le_mul_of_one_le_left (Nat.cast_nonneg _) hQ1R
    have h5 : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (x : ℝ) ^ ((11 : ℝ) / 24) :=
      div_le_self h3 (by norm_num)
    linarith [h1, h2, h4, h5]
  have hDhi : ((opQ * opDlev x : ℕ) : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000) := by
    rw [hDcast]
    -- opQ ≤ log x ≤ x^{1/500}
    have hQx : (opQ : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 500) := le_trans hQlog hlogx
    have hDnn : (0 : ℝ) ≤ (opDlev x : ℝ) := Nat.cast_nonneg _
    have hstep : (opQ : ℝ) * (opDlev x : ℝ)
        ≤ (x : ℝ) ^ ((1 : ℝ) / 500) * (x : ℝ) ^ ((497 : ℝ) / 1000) :=
      mul_le_mul hQx hDlevub hDnn (Real.rpow_nonneg hxpos.le _)
    have hcomb : (x : ℝ) ^ ((1 : ℝ) / 500) * (x : ℝ) ^ ((497 : ℝ) / 1000)
        = (x : ℝ) ^ ((499 : ℝ) / 1000) := by
      rw [← Real.rpow_add hxpos, show (1 : ℝ) / 500 + (497 : ℝ) / 1000 = (499 : ℝ) / 1000 by
        norm_num]
    linarith [hstep, hcomb.le]
  -- the band `F`-floor for `opZ x · opY x`
  have hzyfloor : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((opZ x * opY x : ℕ) : ℝ) := by
    have hzy := zy_floor_ge (x := x) hexp200
    have hzyc : (x : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((opZ x * opY x : ℕ) : ℝ) := by
      simpa [opZ, opY] using hzy
    have hnn : (0 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) := Real.rpow_nonneg hxpos.le _
    have : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (x : ℝ) ^ ((11 : ℝ) / 24) / 4 := by
      apply div_le_div_of_nonneg_left hnn (by norm_num) (by norm_num)
    linarith [hzyc]
  have hzy2 : 2 ≤ opZ x * opY x := by
    have hopZ1 : 1 ≤ opZ x := by omega
    calc 2 ≤ opY x := by omega
      _ ≤ opZ x * opY x := Nat.le_mul_of_pos_left _ hopZ1
  -- the window floor for `opY x`
  have hyfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (opY x : ℝ) := by
    have htfl : (x : ℝ) ^ ((1 : ℝ) / 3) < (opY x : ℝ) + 1 := by
      rw [opY]; exact Nat.lt_floor_add_one _
    have h3le : (3 : ℝ) ≤ (opY x : ℝ) := by
      exact_mod_cast (by omega : 3 ≤ opY x)
    -- `x^{1/3} < opY + 1` and `opY ≥ 3` give `x^{1/3}/8 ≤ opY` (since `1 − 7·opY < 0`).
    linarith [htfl, h3le]
  exact ⟨hDlow, hDhi, hzyfloor, hzy2, hyfloor⟩

end Salt.Chen
