/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.CountAtOp
import Salt.Chen.ChenRows2

/-!
# HCOUNT-2 — the three count sub-rows: Lval + CORR + SLACK

Design: `docs/blueprints/flags.md`, the `2026-07-15 HCOUNT` entry (the enumerated sub-rows) and
`Salt/Chen/CountAtOp.lean`'s module tail (the `(★)` premise and the deferred sub-node list).

`CountAtOp.hcount_at_op` closes the GlueNormalized `hcount` SLOT **modulo** the premise (★)

  `log x · tripleSumW opQ opA x (opZ x)(opY x) ≤ (cbar + ecountOp C x)·massLo x Kmass / φ(opQ)`.

Discharging (★) means applying the count keystone `CountW.tripleSum_le_cbar_final_W` at the op
witnesses (its geometry/AP rows are `hcount_op_geometry`/`hcount_op_AP3`) and folding the RHS —
the `LF·WF·(c̄/2)(x/log x)` main plus the `CORR`/`E_SW` errors — into `(cbar + ecountOp C x)`.
This module supplies the three enumerated sub-rows and their composition.

## The three deliverables

* **HCOUNT-Lval** (`Lval_op_ge`, `hcount_Lval_rows`) — the `Lval` rows at op:
  `3 ≤ Lval x (opY x)`, `N₀ ≤ Lval x (opY x)`, `4 ≤ log (Lval x (opY x))`,
  `(opQ:ℝ) ≤ (log (Lval x (opY x)))^(2:ℝ)`.  Route: `Lval x (opY x) = x/(2·opY x·√x) ≥ x^{1/6}/4`
  (nat-division + floor + `Nat.sqrt`), so `log Lval ≥ log x/6 − 2·log 2`; with `opQ ≤ log x`
  (`opf_tower`) the `C = 2` range row is `log x ≤ (log x/6 − 2 log 2)^2`, past `log x ≥ 96`.
* **HCOUNT-CORR** — the `o(x/log x)` bound on the keystone's `CORR` sum (three pieces).
* **HCOUNT-SLACK** — the multiplicative-slack collapse `LF·WF − 1 ≤ (6K + 4 log 2)/L₀`
  (pure algebra) + the `E_SW` polylog-beats-power fold.

## What is closed here (8 decls, all `[propext, Classical.choice, Quot.sound]`)

* **Deliverable 1 (HCOUNT-Lval) — FULLY CLOSED.**  `Lval_op_ge`, `logLval_op_ge`,
  `hcount_Lval_rows` (all four keystone `Lval` rows at op, `N₀` threaded as a parameter).
* **Deliverable 2 (HCOUNT-CORR) — the three analytic building blocks.**  `Ifun_op_le`,
  `hbjs_sqrt_eq`, `hbjs_sqrt_le`, `S1set_mertens`.  These are exactly the three pieces
  `flags.md` / `CountAtOp.lean`'s deferred note flagged as having *no landed infrastructure*
  ((i) `Ifun` upper bound, (ii) boundary `hbjs`, (iii) `S1set` windowed Mertens).
* **Deliverable 3 (HCOUNT-SLACK) — the pure-algebra collapse.**  `slack_collapse`.

## Honest constants (catch #76 — design value vs. landed value)

* `Ifun_op_le` : landed `(3/2)·log 2/log N`; design note `(3/2)·log(13/8)/log N`.  The uniform
  `β = log u/log N ∈ [0, 1/3]` bound `log(2−3β) ≤ log 2` is safe (the design's `log(13/8)` assumes
  `β ≥ 1/8`, but `zN`'s `β` can dip below `1/8`).  Both are `O(1/log N)`.
* `hbjs_sqrt_le` : landed `≤ 3/log N` (`= 2/(log N − log p)`, `log p ≤ log N/3`); design `2/log x`
  (its `+`-sign was a slip — `hbjs_sqrt_eq` proves the exact value is `2/(log N − log p)`).
* `slack_collapse` : landed `LF·WF − 1 ≤ (6K + 4 log 2)/L₀`; design note `(3K + 24 log 2)/L₀`.
  The honest expansion `a + b + a·b` with `a = 3K/L₀`, `b = 4 log 2/M₀ ≤ 1`, `b ≤ 4 log 2/L₀`
  gives `6K + 4 log 2`.  Still `O(1/L₀)`, still `≪ 0.01` at the tower.

## What remains (the follow-up integration — building blocks now in place)

* **HCOUNT-CORR sum assembly** — bound the whole `CORR` sum `≤ C_CORR/(log x)^2` by combining
  the four lemmas above: the `(21/log zR)·Ifun x yR zR` and `Σ(1/p₁)(21/log yR)·hbjs√` terms are
  the dominant `O(1/(log x)^2)`; the `Ifun/zN`, `Ifun/yN`, and floor-`hbjs`/`⌊√⌋` terms are
  `x^{−poly}·polylog` (the floor term needs `⌊√(x/p₁)⌋ ≥ x^{1/3}−1`, then `a12_logpow_le_rpow`).
* **HCOUNT-SLACK `E_SW` fold** — `φ·log x·E_SW = O(x/(log x)^{11})` via `φ ≤ opQ ≤ log x`
  (`opf_tower`), `log Lval ≥ log x/6` (`logLval_op_ge`), `sum_inv_pairSet_le`/`pairSet_card_le`
  (landed), `a12_logpow_le_rpow` (landed); `A = 13` gives `(log x)^{13−2} = (log x)^{11}`.
* **The (★) composition `hcount_star_at_op`** — apply `tripleSum_le_cbar_final_W` at the op
  witnesses (rows: `hcount_op_geometry`, `hcount_op_AP3`, `hcount_Lval_rows`), fold the RHS via
  `slack_collapse` + the CORR sum + the `E_SW` fold, and match to `(cbar + ecountOp C x)·massLo`
  with the honest `C = cbar·(11K + 12 log 2)/4`.  A large but now-unblocked inequality chain.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace Salt.Chen

/-! ## Deliverable 1 — HCOUNT-Lval: the `Lval` rows at the operating point -/

/-- **`Lval_op_ge` — the `x^{1/6}/4` floor on `Lval` at op.**  `Lval x (opY x) = x/(2·opY x·√x)`
(nat division).  Bounding the denominator by its real value `2·x^{1/3}·x^{1/2} = 2·x^{5/6}` and
losing at most `1` to the nat floor gives `(Lval x (opY x) : ℝ) ≥ x^{1/6}/2 − 1 ≥ x^{1/6}/4` past
`x ≥ 10^48` (there `x^{1/6} ≥ 10^8 ≥ 4`). -/
theorem Lval_op_ge {x : ℕ} (hx : (10 : ℝ) ^ 48 ≤ (x : ℝ)) :
    (x : ℝ) ^ ((1 : ℝ) / 6) / 4 ≤ (Lval x (opY x) : ℝ) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx
  have hx1N : 1 ≤ x := by
    have : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hx
    exact_mod_cast this
  -- `opY x ≤ x^{1/3}` and `Nat.sqrt x ≤ x^{1/2}`
  have hopY_le : (opY x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [opY]; exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
  have hsqrt_le : (Nat.sqrt x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    have h2 : (Nat.sqrt x : ℝ) ^ 2 ≤ (x : ℝ) := by exact_mod_cast Nat.sqrt_le' x
    rw [← Real.sqrt_eq_rpow]
    calc (Nat.sqrt x : ℝ) = Real.sqrt ((Nat.sqrt x : ℝ) ^ 2) :=
          (Real.sqrt_sq (Nat.cast_nonneg _)).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt h2
  -- the denominator `D = 2·opY x·√x` and its real upper bound `2·x^{5/6}`
  set D : ℕ := 2 * opY x * Nat.sqrt x with hDdef
  have hopYpos : 1 ≤ opY x := by
    rw [opY]; refine Nat.le_floor ?_
    rw [Nat.cast_one]; exact Real.one_le_rpow (le_trans (by norm_num) hx) (by norm_num)
  have hsqrtpos : 1 ≤ Nat.sqrt x := Nat.le_sqrt.mpr (by omega)
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hDposR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hx56 : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 2) = (x : ℝ) ^ ((5 : ℝ) / 6) := by
    rw [← Real.rpow_add hxpos]; norm_num
  have hD_le : (D : ℝ) ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 6) := by
    have hnn3 : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hxpos.le _
    calc (D : ℝ) = 2 * (opY x : ℝ) * (Nat.sqrt x : ℝ) := by rw [hDdef]; push_cast; ring
      _ ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 2) := by
          gcongr
      _ = 2 * (x : ℝ) ^ ((5 : ℝ) / 6) := by rw [mul_assoc, hx56]
  -- nat-division lower bound: `(Lval : ℝ) ≥ (x:ℝ)/D − 1`
  have hLvalEq : Lval x (opY x) = x / D := by simp only [Lval, hDdef]
  have hkey : (x : ℝ) ≤ (Lval x (opY x) : ℝ) * (D : ℝ) + (D : ℝ) := by
    have h := Nat.div_add_mod x D
    have hlt := Nat.mod_lt x hDpos
    have hcast : (x : ℝ) = (D : ℝ) * (Lval x (opY x) : ℝ) + ((x % D : ℕ) : ℝ) := by
      rw [hLvalEq]; exact_mod_cast h.symm
    have hltR : ((x % D : ℕ) : ℝ) < (D : ℝ) := by exact_mod_cast hlt
    nlinarith [hcast, hltR]
  have hLval_ge : (x : ℝ) / (D : ℝ) - 1 ≤ (Lval x (opY x) : ℝ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ hDposR]
    nlinarith [hkey]
  -- `x/D ≥ x/(2 x^{5/6}) = x^{1/6}/2`
  have hx56pos : (0 : ℝ) < (x : ℝ) ^ ((5 : ℝ) / 6) := Real.rpow_pos_of_pos hxpos _
  have hxD_ge : (x : ℝ) ^ ((1 : ℝ) / 6) / 2 ≤ (x : ℝ) / (D : ℝ) := by
    have hstep : (x : ℝ) / (2 * (x : ℝ) ^ ((5 : ℝ) / 6)) ≤ (x : ℝ) / (D : ℝ) := by
      apply div_le_div_of_nonneg_left hxpos.le hDposR hD_le
    have heq : (x : ℝ) / (2 * (x : ℝ) ^ ((5 : ℝ) / 6)) = (x : ℝ) ^ ((1 : ℝ) / 6) / 2 := by
      rw [div_eq_div_iff (by positivity : (2 * (x : ℝ) ^ ((5 : ℝ) / 6)) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
      have hcollapse : (x : ℝ) ^ ((1 : ℝ) / 6) * (2 * (x : ℝ) ^ ((5 : ℝ) / 6))
          = 2 * (x : ℝ) ^ ((1 : ℝ) / 6 + 5 / 6) := by rw [Real.rpow_add hxpos]; ring
      rw [hcollapse, show (1 : ℝ) / 6 + 5 / 6 = 1 by norm_num, Real.rpow_one]; ring
    rwa [heq] at hstep
  -- `x^{1/6} ≥ 10^8 ≥ 4`, so `x^{1/6}/2 − 1 ≥ x^{1/6}/4`
  have hx16_ge : (10 : ℝ) ^ 8 ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := by
    calc (10 : ℝ) ^ 8 = ((10 : ℝ) ^ 48) ^ ((1 : ℝ) / 6) := by
          rw [← Real.rpow_natCast (10 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10),
            show ((48 : ℕ) : ℝ) * (1 / 6) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have hx16_ge4 : (4 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := le_trans (by norm_num) hx16_ge
  -- assemble
  calc (x : ℝ) ^ ((1 : ℝ) / 6) / 4 ≤ (x : ℝ) ^ ((1 : ℝ) / 6) / 2 - 1 := by nlinarith [hx16_ge4]
    _ ≤ (x : ℝ) / (D : ℝ) - 1 := by linarith [hxD_ge]
    _ ≤ (Lval x (opY x) : ℝ) := hLval_ge

/-- **`logLval_op_ge` — the `log Lval ≥ log x/6 − 2 log 2` floor at op.**  Logging `Lval_op_ge`:
`log (Lval x (opY x)) ≥ log (x^{1/6}/4) = (1/6) log x − log 4 = (1/6) log x − 2 log 2`. -/
theorem logLval_op_ge {x : ℕ} (hx : (10 : ℝ) ^ 48 ≤ (x : ℝ)) :
    Real.log x / 6 - 2 * Real.log 2 ≤ Real.log (Lval x (opY x)) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx
  have h16pos : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 6) / 4 := by positivity
  have hlog := Real.log_le_log h16pos (Lval_op_ge hx)
  rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hxpos,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- **HCOUNT-Lval — the four `Lval` rows at the operating point.**  For any keystone threshold
`N₀`, past a threshold in `x`: `3 ≤ Lval x (opY x)`, `N₀ ≤ Lval x (opY x)`,
`4 ≤ log (Lval x (opY x))`, and `(opQ : ℝ) ≤ (log (Lval x (opY x)))^(2:ℝ)` (the `C = 2` range row).
The first three use `log Lval ≥ log x/6 − 2 log 2` at `log x ≥ 96`; the `N₀` row needs
`x ≥ (4 N₀)^6` (so `x^{1/6} ≥ 4 N₀`); the range row uses `opQ ≤ log x` (`opf_tower`) and
`log x ≤ (log x/6 − 2 log 2)^2` past `log x ≥ 96`. -/
theorem hcount_Lval_rows (N₀ : ℕ) :
    ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
      3 ≤ Lval x (opY x) ∧ N₀ ≤ Lval x (opY x)
        ∧ 4 ≤ Real.log (Lval x (opY x))
        ∧ (opQ : ℝ) ≤ (Real.log (Lval x (opY x))) ^ (2 : ℝ) := by
  obtain ⟨xt, _, htower⟩ := opf_tower
  refine ⟨max xt (max (10 ^ 48) ((4 * N₀) ^ 6)), fun x hx => ?_⟩
  have hxt : xt ≤ x := le_trans (le_max_left _ _) hx
  have hx48N : 10 ^ 48 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxN6 : (4 * N₀) ^ 6 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx48 : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48N
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx48
  have hL96 : (96 : ℝ) ≤ Real.log (x : ℝ) := opf_log_ge_96 x hx48
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlogLval := logLval_op_ge hx48
  have hLval_ge := Lval_op_ge hx48
  -- `4 ≤ log Lval`
  have h4 : 4 ≤ Real.log (Lval x (opY x)) := by nlinarith [hlogLval, hL96, hlog2]
  -- `x^{1/6} ≥ 10^8`
  have hx16 : (10 : ℝ) ^ 8 ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := by
    calc (10 : ℝ) ^ 8 = ((10 : ℝ) ^ 48) ^ ((1 : ℝ) / 6) := by
          rw [← Real.rpow_natCast (10 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10),
            show ((48 : ℕ) : ℝ) * (1 / 6) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_le_rpow (by positivity) hx48 (by norm_num)
  -- `3 ≤ Lval` (nat): `Lval ≥ x^{1/6}/4 ≥ 10^8/4 ≥ 3`
  have h3 : 3 ≤ Lval x (opY x) := by
    have : (3 : ℝ) ≤ (Lval x (opY x) : ℝ) := by nlinarith [hLval_ge, hx16]
    exact_mod_cast this
  -- `N₀ ≤ Lval` (nat): `x ≥ (4 N₀)^6 ⇒ x^{1/6} ≥ 4 N₀ ⇒ Lval ≥ x^{1/6}/4 ≥ N₀`
  have hN₀ : N₀ ≤ Lval x (opY x) := by
    have hbase : ((4 * N₀ : ℕ) : ℝ) ^ 6 ≤ (x : ℝ) := by
      have : (((4 * N₀) ^ 6 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxN6
      push_cast at this ⊢; linarith
    have h4N₀ : ((4 * N₀ : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := by
      have hnn : (0 : ℝ) ≤ ((4 * N₀ : ℕ) : ℝ) := by positivity
      calc ((4 * N₀ : ℕ) : ℝ) = (((4 * N₀ : ℕ) : ℝ) ^ 6) ^ ((1 : ℝ) / 6) := by
            rw [← Real.rpow_natCast (((4 * N₀ : ℕ) : ℝ)) 6, ← Real.rpow_mul hnn,
              show ((6 : ℕ) : ℝ) * (1 / 6) = 1 by norm_num, Real.rpow_one]
        _ ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_le_rpow (by positivity) hbase (by norm_num)
    have : (N₀ : ℝ) ≤ (Lval x (opY x) : ℝ) := by
      have : (4 * N₀ : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := by push_cast at h4N₀; linarith
      nlinarith [hLval_ge, this]
    exact_mod_cast this
  -- the `C = 2` range row: `opQ ≤ log x ≤ (log x/6 − 2 log 2)^2 ≤ (log Lval)^2`
  have hQlogx : (opQ : ℝ) ≤ Real.log x := (htower x hxt).1
  have hrange : (opQ : ℝ) ≤ (Real.log (Lval x (opY x))) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hLvalpos : 0 < Real.log (Lval x (opY x)) := by linarith
    have hsq : Real.log x ≤ (Real.log (Lval x (opY x))) ^ 2 := by
      have hstep : Real.log x ≤ (Real.log x / 6 - 2 * Real.log 2) ^ 2 := by
        nlinarith [hL96, hlog2, Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
      nlinarith [hstep, hlogLval, hLvalpos]
    linarith [hQlogx, hsq]
  exact ⟨h3, hN₀, h4, hrange⟩

/-! ## Deliverable 2 — HCOUNT-CORR: the Abel-error / boundary-prime pieces

The keystone's `CORR` sum (`CountW.lean:700`) is

  `CORR = Ifun x yR zN/zN + Ifun x yR yN/yN + (21/log zR)·Ifun x yR zR
        + Σ_{p₁∈S1set} (1/p₁)·(hbjs x p₁ ⌊√(x/p₁)⌋/⌊√(x/p₁)⌋ + (21/log yR)·hbjs x p₁ √(x/p₁))`.

The three analytic pieces flagged as missing infrastructure are landed here as reusable lemmas:
(i) the `Ifun` upper bound `Ifun_op_le`; (ii) the boundary `hbjs` bounds
`hbjs_sqrt_eq`/`hbjs_sqrt_le`;
(iii) the `S1set` windowed-Mertens bound `S1set_mertens` (a corollary of the landed
`sum_inv_le_of_prime_window`). -/

/-- **HCOUNT-CORR (i) — the `Ifun` upper bound `(3/2)·log 2/log N`.**  On the keystone's `Ifun`
arguments (`u ≥ 1`, `log u ≤ log N/3`), the closed form gives `Ifun N yR u =
log(2 − 3 log u/log N)/(log N − log u)`; the numerator `∈ [0, log 2]` (`2 − 3β ∈ [1, 2]` for
`β = log u/log N ∈ [0, 1/3]`) and the denominator `≥ (2/3) log N`, so `Ifun N yR u ≤
(3/2)·log 2/log N`.  (The design note's `(3/2)·log(13/8)` uses `β ≥ 1/8`; the uniform `β ≥ 0`
bound `log 2` is safe since `zN`'s `β` can dip below `1/8` — DOCUMENTED, catch #76.) -/
theorem Ifun_op_le {N yR u : ℝ} (hN : 1 < N) (hyR0 : 0 < yR)
    (hyR : Real.log yR = Real.log N / 3) (hu1 : 1 ≤ u) (hu_hi : Real.log u ≤ Real.log N / 3) :
    Ifun N yR u ≤ 3 / 2 * Real.log 2 / Real.log N := by
  have hLN : 0 < Real.log N := Real.log_pos hN
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu1
  have hlogu_nn : 0 ≤ Real.log u := Real.log_nonneg hu1
  have htM : Real.log u < 2 / 3 * Real.log N := by linarith
  rw [Ifun_closed_form hN hyR0 hyR hu0 htM, Ifun_cf]
  have hIarg_le2 : IargA N u ≤ 2 := by
    rw [IargA]; have : 0 ≤ 3 * Real.log u / Real.log N := by positivity
    linarith
  have hIarg_ge1 : 1 ≤ IargA N u := by
    rw [IargA]
    have : 3 * Real.log u / Real.log N ≤ 1 := by rw [div_le_iff₀ hLN]; linarith
    linarith
  have hIarg_pos : 0 < IargA N u := lt_of_lt_of_le one_pos hIarg_ge1
  have hnum_le : Real.log (IargA N u) ≤ Real.log 2 := Real.log_le_log hIarg_pos hIarg_le2
  have hnum_nn : 0 ≤ Real.log (IargA N u) := Real.log_nonneg hIarg_ge1
  have hden_ge : 2 / 3 * Real.log N ≤ IdenA N u := by rw [IdenA]; linarith
  calc Real.log (IargA N u) / IdenA N u
      ≤ Real.log (IargA N u) / (2 / 3 * Real.log N) :=
        div_le_div_of_nonneg_left hnum_nn (by positivity) hden_ge
    _ ≤ Real.log 2 / (2 / 3 * Real.log N) := by gcongr
    _ = 3 / 2 * Real.log 2 / Real.log N := by field_simp

/-- **HCOUNT-CORR (ii-eq) — the boundary `hbjs` value.**  `hbjs N p √(N/p) = 2/(log N − log p)`:
`p·√(N/p) = √(pN)`, so `N/(p·√(N/p)) = √(N/p)` and `log √(N/p) = (log N − log p)/2`. -/
theorem hbjs_sqrt_eq {N p : ℝ} (hN : 0 < N) (hp : 0 < p) :
    hbjs N p (Real.sqrt (N / p)) = 2 / (Real.log N - Real.log p) := by
  have hNp : (0 : ℝ) < N / p := div_pos hN hp
  have hs : 0 < Real.sqrt (N / p) := Real.sqrt_pos.mpr hNp
  have hden0 : (0 : ℝ) < p * Real.sqrt (N / p) := by positivity
  rw [hbjs, Real.log_div hN.ne' hden0.ne', Real.log_mul hp.ne' hs.ne', Real.log_sqrt hNp.le,
    Real.log_div hN.ne' hp.ne',
    show Real.log N - (Real.log p + (Real.log N - Real.log p) / 2)
        = (Real.log N - Real.log p) / 2 by ring, inv_div]

/-- **HCOUNT-CORR (ii) — the boundary `hbjs` bound `hbjs N p √(N/p) ≤ 3/log N`.**  For
`p ≤ N^{1/3}` (`log p ≤ log N/3`), `log N − log p ≥ (2/3) log N`, so `2/(log N − log p) ≤ 3/log N`.
(The design note wrote `2/log x`; the honest value is `≤ 3/log N` — DOCUMENTED, catch #76.) -/
theorem hbjs_sqrt_le {N p : ℝ} (hN : 1 < N) (hp1 : 1 ≤ p) (hp_hi : Real.log p ≤ Real.log N / 3) :
    hbjs N p (Real.sqrt (N / p)) ≤ 3 / Real.log N := by
  have hN0 : 0 < N := by linarith
  have hp0 : 0 < p := by linarith
  have hLN : 0 < Real.log N := Real.log_pos hN
  rw [hbjs_sqrt_eq hN0 hp0]
  have hden : 2 / 3 * Real.log N ≤ Real.log N - Real.log p := by linarith
  calc 2 / (Real.log N - Real.log p) ≤ 2 / (2 / 3 * Real.log N) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = 3 / Real.log N := by field_simp

/-- **HCOUNT-CORR (iii) — the `S1set` windowed-Mertens bound.**  The `p₁`-window `S1set x z y`
is a set of primes in `[z, y] ⊆ [z, y+1)`, so the landed `sum_inv_le_of_prime_window` (`C₃ = 19`)
gives `Σ_{p₁∈S1set} 1/p₁ ≤ log(log(y+1)/log z) + 19/log z`.  At op `log z = log x/8`,
`log(y+1) ≈ log x/3`, this is `log(8/3) + O(1/log z)`. -/
theorem S1set_mertens {x z y : ℕ} (hz2 : (2 : ℝ) ≤ (z : ℝ)) (hzy1 : (z : ℝ) ≤ (y : ℝ) + 1) :
    ∑ p ∈ S1set x z y, (1 : ℝ) / p
      ≤ Real.log (Real.log ((y : ℝ) + 1) / Real.log z) + 19 / Real.log z := by
  apply Salt.BrunLower.sum_inv_le_of_prime_window hz2 hzy1
  intro p hp
  rw [S1set, Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨_, hzp, hpy, hpp⟩ := hp
  refine ⟨hpp, by exact_mod_cast hzp, ?_⟩
  have : (p : ℝ) ≤ (y : ℝ) := by exact_mod_cast hpy
  linarith

/-! ## Deliverable 3 (algebra half) — HCOUNT-SLACK: the multiplicative-slack collapse

The keystone's leading factor is `LF·WF·(c̄/2)(x/log x)` with `LF = 1 + 3K/L₀`,
`WF = 1 + 4 log 2/log(2·Lval)`, `L₀ = log Lval`.  The multiplicative slack over the bare
`(c̄/2)(x/log x)` main is `(LF·WF − 1)·(c̄/2)·x`; `slack_collapse` shows `LF·WF − 1 ≤
(6K + 4 log 2)/L₀`, an honest `O(1/log Lval)`.  (The in-file design note claimed
`(3K + 24 log 2)/L₀`; the honest algebra yields `6K + 4 log 2` — DOCUMENTED, catch #76.) -/

/-- **`slack_collapse` — the `LF·WF − 1 ≤ (6K + 4 log 2)/L₀` collapse (pure algebra).**  With
`L₀ = log Lval ≥ 4`, `M₀ = log(2·Lval) ≥ L₀`, `K ≥ 0`, writing `a = 3K/L₀ ≥ 0`,
`b = 4 log 2/M₀ ≤ 1` (as `M₀ ≥ 4`), one has `LF·WF − 1 = a + b + a·b ≤ a + 4 log 2/L₀ + a =
(6K + 4 log 2)/L₀` (using `b ≤ 4 log 2/L₀` and `a·b ≤ a`). -/
theorem slack_collapse {K L₀ M₀ : ℝ} (hK : 0 ≤ K) (hL₀ : 4 ≤ L₀) (hM₀ : L₀ ≤ M₀) :
    (1 + 3 * K / L₀) * (1 + 4 * Real.log 2 / M₀) - 1 ≤ (6 * K + 4 * Real.log 2) / L₀ := by
  have hL₀0 : 0 < L₀ := by linarith
  have hM₀0 : 0 < M₀ := by linarith
  have hM₀4 : 4 ≤ M₀ := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have ha : 0 ≤ 3 * K / L₀ := by positivity
  -- `b = 4 log 2/M₀ ≤ 1` and `b ≤ 4 log 2/L₀`
  have hb1 : 4 * Real.log 2 / M₀ ≤ 1 := by
    have h1 : 4 * Real.log 2 / M₀ ≤ 4 * Real.log 2 / 4 := by
      gcongr
    have h2 : 4 * Real.log 2 / 4 = Real.log 2 := by ring
    linarith [h1, h2 ▸ hlog2lt]
  have hb_le : 4 * Real.log 2 / M₀ ≤ 4 * Real.log 2 / L₀ := by
    gcongr
  have key : (1 + 3 * K / L₀) * (1 + 4 * Real.log 2 / M₀) - 1
      = 3 * K / L₀ + 4 * Real.log 2 / M₀ + (3 * K / L₀) * (4 * Real.log 2 / M₀) := by ring
  rw [key]
  have hab : (3 * K / L₀) * (4 * Real.log 2 / M₀) ≤ 3 * K / L₀ := by
    calc (3 * K / L₀) * (4 * Real.log 2 / M₀)
        ≤ (3 * K / L₀) * 1 := mul_le_mul_of_nonneg_left hb1 ha
      _ = 3 * K / L₀ := mul_one _
  have hsum : 3 * K / L₀ + 4 * Real.log 2 / L₀ + 3 * K / L₀ = (6 * K + 4 * Real.log 2) / L₀ := by
    field_simp; ring
  linarith [hab, hb_le, hsum]

/-- **`ESW_main_fold` — the `E_SW` main-term polylog-beats-power collapse.**  With `L = log x`,
`φ ≤ L`, `logLval ≥ L/6` and `A ≥ 2`, the `E_SW` main term `φ·L·(Ksw·x/logLval^A·M)` collapses to
`Ksw·M·6^A·x·L^(2−A)` — i.e. `O(x/(log x)^{A−2})`.  At the keystone's `A = 13` this is
`O(x/(log x)^{11})`, the strip the `HCOUNT-SLACK` `E_SW` fold needs.  Route: `logLval^A ≥
(L/6)^A = L^A/6^A` (`Real.div_rpow`), so `1/logLval^A ≤ 6^A/L^A`; then `φ·L ≤ L·L = L^2` and
`L^2/L^A = L^{2−A}`. -/
theorem ESW_main_fold {A φ x logLval M Ksw : ℝ}
    (hA : 2 ≤ A) (_hφ : 0 ≤ φ) (hφx : φ ≤ Real.log x) (hlogx : 0 < Real.log x)
    (hLval : Real.log x / 6 ≤ logLval) (hM : 0 ≤ M) (hKsw : 0 ≤ Ksw) (hx : 0 ≤ x) :
    φ * Real.log x * (Ksw * x / logLval ^ A * M)
      ≤ Ksw * M * (6 : ℝ) ^ A * x * (Real.log x) ^ (2 - A) := by
  set L := Real.log x with hLdef
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hlogLval0 : 0 < logLval := by linarith
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hlogx A
  have h6A : 0 < (6 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have hlogLvalA : 0 < logLval ^ A := Real.rpow_pos_of_pos hlogLval0 A
  -- `logLval^A ≥ L^A/6^A`
  have h3 : L ^ A / (6 : ℝ) ^ A ≤ logLval ^ A := by
    rw [← Real.div_rpow hlogx.le (by norm_num) A]
    exact Real.rpow_le_rpow (by positivity) hLval hA0
  -- `1/logLval^A ≤ 6^A/L^A`
  have hinv : (1 : ℝ) / logLval ^ A ≤ (6 : ℝ) ^ A / L ^ A := by
    rw [div_le_div_iff₀ hlogLvalA hLA, one_mul, mul_comm]
    have hm := mul_le_mul_of_nonneg_right h3 h6A.le
    have hc : L ^ A / (6 : ℝ) ^ A * (6 : ℝ) ^ A = L ^ A := by field_simp
    linarith [hm, hc]
  -- `L^2/L^A = L^(2-A)`
  have hLL : L * L / L ^ A = L ^ (2 - A) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hlogx.le,
      show L * L = L ^ (2 : ℝ) by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add hlogx, Real.rpow_one],
      ← Real.rpow_add hlogx]
    congr 1
  -- assemble
  have hchain : Ksw * x / logLval ^ A * M ≤ Ksw * x * M * ((6 : ℝ) ^ A / L ^ A) := by
    have h := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ Ksw * x * M)
    calc Ksw * x / logLval ^ A * M = Ksw * x * M * (1 / logLval ^ A) := by ring
      _ ≤ Ksw * x * M * ((6 : ℝ) ^ A / L ^ A) := h
  calc φ * L * (Ksw * x / logLval ^ A * M)
      ≤ L * L * (Ksw * x * M * ((6 : ℝ) ^ A / L ^ A)) := by
        apply mul_le_mul _ hchain (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hφx hlogx.le
    _ = Ksw * M * (6 : ℝ) ^ A * x * (L * L / L ^ A) := by ring
    _ = Ksw * M * (6 : ℝ) ^ A * x * (L ^ (2 - A)) := by rw [hLL]

end Salt.Chen
