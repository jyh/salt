/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ArithPool
import Salt.MR.M4ArithPrime
import Salt.MR.M4RowsChiZeroPrime

/-!
# ⟦R5 — THE CLOSURE REPAIRS⟧ (`M4ClosureRepair`)

Design provenance: `docs/blueprints/flags.md` 2026-07-30 18:46, ⟦THE CLOSURE EXAMINER RULES⟧.
The examiner ruled the ⟦KNOT-2 CLOSURE⟧ **terminal CONFIRMED, closure DEFECT**, with four
night-executable repairs.  This file is all four, as ADDITIVE TWINS: not one landed
declaration is touched, not one frozen definition is edited.

## ⟦D1 — THE POOL PINCH⟧

`M4ArithPrime.doorFuseFrame_pool'_of_gates` asks `hone : 1 ≤ π₀`, and
`M4ArithPool.m4_arith_henv_rho_pool` asks `188133·π₀·e^{14λ} ≤ ρ/2`.  For `ρ ≤ 2` and
`λ ≥ 0` those are JOINTLY UNSATISFIABLE (the examiner's kernel probe `pool_pinch`), so
`m4_chiSummedFreeRow_of_doorAssembly_join` is uninstantiable as landed.

§1 mints the twin at the DECAYING pool `π₀ := (log X_d)^{−θ₂₉₃}` and `ε ≤ 0`, where

* `eps_pool` is an EQUALITY (`(log X_d)^{−θ₂₉₃+ε} ≤ (log X_d)^{−θ₂₉₃}` at `ε ≤ 0`);
* `band_pool` follows from the base-LOWER threshold
  `4096 ≤ (log X_d)^{1−1/500−θ₂₉₃}` — note the exponent: `1 − 1/500 − θ₂₉₃`, **not** the
  landed `1 − 1/250`, which is what the pinch's repair actually needs;
* the price `188133·(log X_d)^{−θ₂₉₃}·e^{14λ} ≤ ρ/2` is DISCHARGED by
  `DoorArithFrameRho.arm` alone (`7000λ + 500·log(1/ρ) + 6600 ≤ loglog X_d`): the demand is
  `θ₂₉₃·loglog X_d ≥ 14λ + log(376266/ρ)`, and `7000·θ₂₉₃ = 23.89` against the `14` needed —
  a `1.707×` margin in the `λ`-coefficient.

So `gU` and `gBand` are jointly satisfiable and the price is free: the pinch is gone.

## ⟦D3 — THE `C_p` PINNING⟧

`M4ArithPrime.GRowsZeroGate''` splits the pool THREE ways and `gRows_zero_of_gate''` proves
only the `C_p = 0` conclusion `5760·(a2RowsSum' + 0·(2/M)) ≤ π₀`; both R4 exits
(`M4RowsChiEndPrime`'s `∃ Cp, 0 < Cp` and `M4RowsChiZeroPrime`'s `∀ Cp, 0 < Cp →`) demand a
frame at a POSITIVE `C_p`.  §2 mints `GRowsZeroGate'''` — the same three slots plus the
density slot `5760·C_cc·(2/M) ≤ π₀/4`, the pool re-split FOUR ways (each share `π₀/4`
instead of `π₀/3`) — and carries it through the frame and the join exit at free `C_cc`.

## ⟦D4 — THE UNGATED `henv`⟧

`M4AssemblyPrime.m4_chiSummedFreeRow_of_doorAssembly_pool'` reads

  `henv : ∀ H j A s, doorRowFloor M ≤ j → arcDen 12 H · a2DoorGrade_pool … ≤ RSbig j H`

with `A`, `s` UNIVERSALLY quantified and no socket gate.  At `RSbig := RSanDoorRho ρ` the
left side grows like `(log H)^{12}` and the right decays, so that binder is unsatisfiable;
the only supplier, `m4_arith_henv_rho_pool`, is `SocketBase`-GATED.  R2's own exit
`m4_chiSummedFreeRow_of_doorArithRho_pool` routes through
`m4_chiSummedFreeRowBig_of_doorGradeGated_pool` and gets this right; the join/end'/zero'
exits regressed.  §3 mints the gated twins on exactly R2's route.

## ⟦D7 — THE `E_ge` LINE⟧

`DoorArithFrameRho` is FROZEN, so the `arm`'s `7000λ` is not touched.  §4 mints the `E_ge`
line as a STANDALONE gate: from the `EP2` gate and the `φ`-row, `49920·φ(q) ≤ (log X_d)^{εr}`;
and the sufficiency form, a base-LOWER demand on `loglog X_d`.

## Contents

* §1 ⟦D1⟧ `decayPool`, the three decay stones, `doorFuseFrame_pool'_of_gates_decay`,
  `price_at_decayPool` + the per-base socket wrapper;
* §2 ⟦D3⟧ `GRowsZeroGate'''`, `gRows_zero_of_gate'''`, `doorFuseFrame_pool'_of_gates_cc`
  (and its decay twin), `m4_chiSummedFreeRow_of_doorAssembly_join_cc`;
* §3 ⟦D4⟧ `m4_chiSummedFreeRow_of_doorAssembly_pool'_gated` and the `end'`/`zero'` twins,
  then the `ρ`-spliced exits;
* §4 ⟦D7⟧ `ege_line_gate`, `ege_line_of_loglog`;
* §5 **THE FUSE** — `m4_closure_fuse_end'` / `m4_closure_fuse_zero'`: ⟦item 11⟧ at
  `RSanDoorRho ρ`, from the gates alone, at the decaying pool, with NO `hone` and NO
  `hprice`;
* §6 ⟦R5b⟧ **THE CONSTANT POOL** — `constPool`, its price, its socket wrapper and its frame
  supplier: the base-UPPER-cap-free alternative to §1's decaying pool.

Additive: no landed declaration is touched.
-/

set_option maxRecDepth 40000

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — ⟦D1⟧ THE DECAYING POOL

The pinch's repair.  Everything in this section is stated at `π₀ := (log X_d)^{−θ₂₉₃}`. -/

/-- **⟦THE DECAYING POOL⟧** (`decayPool`) — the pool value at which `DoorFuseFrame_pool'`'s
two pool-side fields and `m4_arith_henv_rho_pool`'s price are JOINTLY satisfiable.  The
landed `hone : 1 ≤ π₀` picks the other side of the pinch and is unsatisfiable against the
price. -/
def decayPool (A : ℕ) : ℝ := (Real.log ((A : ℕ) : ℝ)) ^ (-theta293)

theorem decayPool_def (A : ℕ) : decayPool A = (Real.log ((A : ℕ) : ℝ)) ^ (-theta293) := rfl

/-- The decaying pool is nonnegative at EVERY natural base — no threshold needed, since
`log` of a natural cast is nonnegative and `rpow` preserves that. -/
theorem decayPool_nonneg (A : ℕ) : 0 ≤ decayPool A :=
  Real.rpow_nonneg (log_natCast_nonneg' A) _

/-- `3 ≤ X_d` gives `1 ≤ log X_d`. -/
private lemma r5_one_le_log_of_three_le {Xd : ℕ} (h : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ)) :
    (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
  have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) h
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ (3 : ℝ))
    rwa [Real.log_exp] at this
  linarith

/-- **⟦STONE 1 — `eps_pool` AT THE DECAYING POOL⟧** (`eps_pool_at_decayPool`).  At `ε ≤ 0`
the `𝒰`-leg field is the rpow monotonicity in the exponent, i.e. an equality at `ε = 0`.
Kernel-certified by the closure examiner (probe `P4`). -/
theorem eps_pool_at_decayPool {Xd : ℕ} {ε : ℝ}
    (hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ)) (hε : ε ≤ 0) :
    (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ decayPool Xd :=
  Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)

/-- **⟦STONE 2 — `band_pool` AT THE DECAYING POOL⟧** (`band_pool_at_decayPool`).  From a
base-LOWER threshold at the exponent `1 − 1/500 − θ₂₉₃`, **not** the landed `1 − 1/250`:
the landed absorption routed through `(log X_d)^{−1/500} ≤ 1`, which is exactly the step
`hone` paid for.  Kernel-certified (probe `P4`). -/
theorem band_pool_at_decayPool {Xd : ℕ} (h : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ))
    (hL : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) :
    4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ decayPool Xd := by
  have hsplit : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293)
      = (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)
        * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) := by
    rw [← Real.rpow_add h]; ring_nf
  rw [decayPool_def, hsplit]
  exact mul_le_mul_of_nonneg_right hL (Real.rpow_pos_of_pos h _).le

/-- **⟦STONE 3 — THE PRICE AT THE DECAYING POOL⟧** (`price_at_decayPool`).  The summand-3
price `188133·π₀·e^{14λ} ≤ ρ/2` at `π₀ := (log X_d)^{−θ₂₉₃}` reduces to

  `θ₂₉₃·loglog X_d ≥ 14λ + log(376266/ρ)` ,

which `DoorArithFrameRho.arm`'s `7000λ + 500·log(1/ρ) + 6600 ≤ loglog X_d` implies with a
`1.707×` margin in the `λ`-coefficient (`7000·θ₂₉₃ = 23.89` against the `14` needed) and a
`500 ≫ 1/θ₂₉₃ = 293` margin in the `log(1/ρ)` coefficient.  Kernel-certified (probe `P4`).

⟦THE READING⟧ the frozen `arm` PAYS FOR the decaying pool.  No new frame field, no
restatement of `DoorArithFrameRho`. -/
theorem price_at_decayPool {Xd : ℕ} {ρ lam : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hlam : 0 ≤ lam)
    (hL : (1 : ℝ) < Real.log ((Xd : ℕ) : ℝ))
    (harm : 7000 * lam + 500 * Real.log (1 / ρ) + 6600
      ≤ Real.log (Real.log ((Xd : ℕ) : ℝ))) :
    188133 * decayPool Xd * Real.exp (14 * lam) ≤ ρ / 2 := by
  have hθlo : (34 : ℝ) / 10000 ≤ theta293 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have he : Real.exp 1 < 2.7182818286 := by have := Real.exp_one_lt_d9; linarith
    have hden : (0 : ℝ) < 32 * (3 * Real.exp 1 + 1) := by nlinarith
    have hval : theta293 = 1 / (32 * (3 * Real.exp 1 + 1)) := rfl
    rw [hval, le_div_iff₀ hden]; nlinarith
  have hLL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hlogrho : (0 : ℝ) ≤ Real.log (1 / ρ) := by
    rw [one_div, Real.log_inv]
    have := Real.log_nonpos hρ0.le hρ1
    linarith
  have hrw : decayPool Xd
      = Real.exp (-theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ))) := by
    rw [decayPool_def, Real.rpow_def_of_pos hLL0]; ring_nf
  rw [hrw]
  have hkey : 14 * lam + Real.log (376266 / ρ)
      ≤ theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)) := by
    have hsplit : Real.log (376266 / ρ) = Real.log 376266 + Real.log (1 / ρ) := by
      rw [Real.log_div (by norm_num) hρ0.ne', one_div, Real.log_inv]; ring
    have h376 : Real.log 376266 ≤ 13 := by
      have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have he13 : (376266 : ℝ) ≤ Real.exp 13 := by
        have hh : Real.exp 13 = (Real.exp 1) ^ (13 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
        rw [hh]
        have hc : (2.7182818283 : ℝ) ^ (13 : ℕ) ≤ (Real.exp 1) ^ (13 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) h1.le 13
        have : (376266 : ℝ) ≤ (2.7182818283 : ℝ) ^ (13 : ℕ) := by norm_num
        linarith
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 376266) he13
      rwa [Real.log_exp] at this
    rw [hsplit]
    nlinarith [harm, hθlo, hlam, hlogrho]
  have hexp : 188133 * Real.exp (-theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)))
      * Real.exp (14 * lam)
      = 188133 * Real.exp (14 * lam - theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ))) := by
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [hexp]
  have hlt : 14 * lam - theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ))
      ≤ - Real.log (376266 / ρ) := by linarith
  have hmono := Real.exp_le_exp.mpr hlt
  have hval : Real.exp (- Real.log (376266 / ρ)) = ρ / 376266 := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [hval] at hmono
  nlinarith [hmono, hρ0,
    Real.exp_pos (14 * lam - theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)))]

/-- **⟦THE PRICE WRAPPER, PER SOCKET BASE⟧** (`price_at_decayPool_socket`) — exactly the
`hprice` binder of `M4ArithPool.m4_arith_henv_rho_pool` at `π₀ := decayPool`, DISCHARGED from
`DoorArithFrameRho` alone.  Nothing else is asked: `ρ > 0`, `ρ ≤ 1`, `λ ≥ 0` and `1 < log X_d`
are all frame fields (`rho_pos`, `rho_le_one`, `Hfloor`, `one_lt_logX`). -/
theorem price_at_decayPool_socket {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {K ρ : ℝ}
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      188133 * decayPool (A + s) * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2 := by
  intro H L q j A s hb
  have hfr := harith H L q j A s hb
  have hlam : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by
    have := hfr.Hfloor; linarith
  exact price_at_decayPool hfr.rho_pos hfr.rho_le_one hlam hfr.one_lt_logX hfr.armWeak

/-- **⟦D1 — THE FRAME AT THE DECAYING POOL⟧** (`doorFuseFrame_pool'_of_gates_decay`) — the
twin of `M4ArithPrime.doorFuseFrame_pool'_of_gates` at `π₀ := decayPool X_d`, with
`hone : 1 ≤ π₀` GONE.  What replaces it:

* `hε : ε ≤ 0` — the `𝒰`-leg exponent, pinned at or below `0` (the examiner's `ε := 0` is the
  intended instance);
* `hL4096 : 4096 ≤ (log X_d)^{1−1/500−θ₂₉₃}` — a base-LOWER threshold, at the CORRECTED
  exponent.

Every remaining demand is base-free or base-LOWER; no field caps the base and no field is
in tension with the summand-3 price. -/
theorem doorFuseFrame_pool'_of_gates_decay {M Xd j : ℕ} {Cs ε : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ decayPool Xd)
    (hg : GRowsZeroGate'' M Xd (decayPool Xd))
    (hε : ε ≤ 0)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) :
    DoorFuseFrame_pool' M Xd j Cs 0 ε (decayPool Xd) where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate'' hM hXd hg
  eps_pool := eps_pool_at_decayPool (r5_one_le_log_of_three_le hb.X_three) hε
  band_pool := band_pool_at_decayPool
    (by have := r5_one_le_log_of_three_le hb.X_three; linarith) hL4096

/-! ## §2 — ⟦D3⟧ THE FOUR-SLOT RE-SPLIT

`GRowsZeroGate''` splits the pool three ways and pins `C_p = 0`.  Both R4 exits
(`M4RowsChiEndPrime.m4_chiSummedFreeRow_of_doorAssembly_pool_end'` and
`M4RowsChiZeroPrime.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'`) hand out a POSITIVE
`Cp` and demand `DoorFuseFrame_pool' M (A+s) j Ct Cp …`, whose `gRows` field carries the
density debit `5760·Cp·(2/M)`.  The re-split below adds that debit as a FOURTH slot and
shrinks the three landed shares from `π₀/3` to `π₀/4`. -/

/-- **⟦THE `gRows` GATE AT FREE DENSITY⟧** (`GRowsZeroGate'''`) — `GRowsZeroGate''`'s three
slots at `π₀/4` plus the density slot.  Three of the four are BASE-FREE; `endpt` is the one
base-reading slot and it reads the base only from BELOW (`1/X_d → 0`).

| slot | statement | reads the base? |
|---|---|---|
| `level1` | `14400·e²·a2Level1 M ≤ π₀/4` | **no** |
| `endpt` | `5760·(2e+2)/X_d ≤ π₀/4` | yes — a base-LOWER demand |
| `p2` | `138240·(1/𝒫₁ + 1/𝒫₂) ≤ π₀/4` | **no** |
| `dens` | `5760·C_cc·(2/M) ≤ π₀/4` | **no** — an `M`-axis demand |

⟦THE ARITHMETIC OF THE RE-SPLIT⟧ `4 · (π₀/4) = π₀`, and the four summands of
`a2RowsSum'_door_decomp` (weighted by `5760`) plus the density debit are exactly the four
left-hand sides.  Nothing is absorbed. -/
structure GRowsZeroGate''' (M Xd : ℕ) (Ccc π₀ : ℝ) : Prop where
  /-- ⟦THE LEVEL-1 SLOT⟧ base-free. -/
  level1 : 14400 * Real.exp 1 ^ 2 * a2Level1 M ≤ 1 / 4 * π₀
  /-- ⟦THE ENDPOINT SLOT⟧ the only base-reading slot, and base-LOWER. -/
  endpt : 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ)) ≤ 1 / 4 * π₀
  /-- ⟦THE `p²` SLOT, R1⟧ `X_d`-FREE. -/
  p2 : 138240 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
        + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ))
      ≤ 1 / 4 * π₀
  /-- **⟦THE DENSITY SLOT — D3⟧** the debit `GRowsZeroGate''` pinned to `0`. -/
  dens : 5760 * Ccc * (2 / (M : ℝ)) ≤ 1 / 4 * π₀

/-- At `C_cc = 0` and a nonnegative pool the four-way gate is STRICTLY stronger than the
landed three-way one — the shares only shrank. -/
theorem gRowsZeroGate''_of_gate''' {M Xd : ℕ} {π₀ : ℝ} (hπ : 0 ≤ π₀)
    (hg : GRowsZeroGate''' M Xd 0 π₀) : GRowsZeroGate'' M Xd π₀ where
  level1 := by have := hg.level1; linarith
  endpt := by have := hg.endpt; linarith
  p2 := by have := hg.p2; linarith

/-- **⟦THE RESIDUAL AT FREE DENSITY⟧** (`gRows_zero_of_gate'''`):

  `5760·(a2RowsSum' M X_d + C_cc·(2/M)) ≤ π₀`

from `GRowsZeroGate'''` alone.  `M4ArithPrime.gRows_zero_of_gate''`'s proof with the fourth
summand carried instead of killed. -/
theorem gRows_zero_of_gate''' {M Xd : ℕ} {Ccc π₀ : ℝ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hg : GRowsZeroGate''' M Xd Ccc π₀) :
    5760 * (a2RowsSum' M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ := by
  rw [a2RowsSum'_door_decomp hM hXd]
  have hid : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1 M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 24 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ))
        + Ccc * (2 / (M : ℝ)))
      = 14400 * Real.exp 1 ^ 2 * a2Level1 M
        + 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ))
        + 138240 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ))
        + 5760 * Ccc * (2 / (M : ℝ)) := by ring
  rw [hid]
  linarith [hg.level1, hg.endpt, hg.p2, hg.dens]

/-- **⟦D3 — THE FRAME AT FREE DENSITY⟧** (`doorFuseFrame_pool'_of_gates_cc`) —
`M4ArithPrime.doorFuseFrame_pool'_of_gates` with `C_cc` free instead of pinned at `0`.  The
pool-side fields are unchanged (`hone` + `hL4096` at the landed exponent). -/
theorem doorFuseFrame_pool'_of_gates_cc {M Xd j : ℕ} {Cs Ccc ε π₀ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hg : GRowsZeroGate''' M Xd Ccc π₀)
    (hone : (1 : ℝ) ≤ π₀)
    (hε : ε ≤ theta293)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)) :
    DoorFuseFrame_pool' M Xd j Cs Ccc ε π₀ where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate''' hM hXd hg
  eps_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := r5_one_le_log_of_three_le hb.X_three
    have hle : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      simpa using this
    linarith
  band_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := r5_one_le_log_of_three_le hb.X_three
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
    have habs : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) := by
      have hsp : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          = (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)
            * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) := by
        rw [← Real.rpow_add hL0]; norm_num
      rw [hsp]
      exact mul_le_mul_of_nonneg_right hL4096 (le_of_lt (Real.rpow_pos_of_pos hL0 _))
    have hone' : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      simpa using this
    linarith

/-- **⟦D1 × D3 — THE FRAME AT FREE DENSITY AND THE DECAYING POOL⟧**
(`doorFuseFrame_pool'_of_gates_cc_decay`) — the two repairs composed: `C_cc` free (so both R4
exits can consume it) AND `π₀ := decayPool X_d` (so the summand-3 price is payable).  This is
the frame supplier §5's fuse actually uses. -/
theorem doorFuseFrame_pool'_of_gates_cc_decay {M Xd j : ℕ} {Cs Ccc ε : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ decayPool Xd)
    (hg : GRowsZeroGate''' M Xd Ccc (decayPool Xd))
    (hε : ε ≤ 0)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) :
    DoorFuseFrame_pool' M Xd j Cs Ccc ε (decayPool Xd) where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate''' hM hXd hg
  eps_pool := eps_pool_at_decayPool (r5_one_le_log_of_three_le hb.X_three) hε
  band_pool := band_pool_at_decayPool
    (by have := r5_one_le_log_of_three_le hb.X_three; linarith) hL4096

/-- **⟦D3 — THE JOIN EXIT AT FREE DENSITY⟧** (`m4_chiSummedFreeRow_of_doorAssembly_join_cc`) —
`M4ArithPrime.m4_chiSummedFreeRow_of_doorAssembly_join` with the density constant FREE.  The
`hrows` binder correspondingly reads `a2Mrow' (Cs …) (Ccc …)` rather than `a2Mrow' (Cs …) 0`,
which is what both R4 `hrows` suppliers actually produce. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_join_cc {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hbase : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j)
    (hgP1 : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      374784 * Cs (A + s) * Real.exp 3
          * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀ (A + s))
    (hgRows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      GRowsZeroGate''' M (A + s) (Ccc (A + s)) (π₀ (A + s)))
    (hone : ∀ A : ℕ, (1 : ℝ) ≤ π₀ A)
    (heps : ∀ A : ℕ, ε A ≤ theta293)
    (hL4096 : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 250))
    (hrows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
          ≤ a2Mrow' (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorAssembly_pool' (Cs := Cs) (Ccc := Ccc) (C₁ := C₁)
    (M₀ := M₀) (ε := ε) (π₀ := π₀) hM ?_ hrows hband (fun A => le_trans zero_le_one (hone A))
    henv
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_cc (hbase H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (hone (A + s)) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-! ## §3 — ⟦D4⟧ THE GATED TWINS

`M4AssemblyPrime.m4_chiSummedFreeRow_of_doorAssembly_pool'` routes through
`M4AssemblyPool.m4_chiSummedFreeRow_of_doorGrade_pool`, whose `henv` binder is UNGATED: `A`,
`s` are universally quantified with only `doorRowFloor M ≤ j` in front.  At
`RSbig := RSanDoorRho ρ` that binder demands `(log H)^{12}·(grade) ≤ ρ/(1+12λ)²` at bases the
socket never reaches, and it is unsatisfiable.

R2's own exit routes through `M4ArithPool.m4_chiSummedFreeRowBig_of_doorGradeGated_pool`,
whose `henv` carries the `SocketBase` gate.  Everything below is that route, at the PRIMED
fuse. -/

/-- **⟦D4 — THE ASSEMBLY, GATED⟧** (`m4_chiSummedFreeRow_of_doorAssembly_pool'_gated`) —
`M4AssemblyPrime.m4_chiSummedFreeRow_of_doorAssembly_pool'` with the `henv` binder
`SocketBase`-GATED.  Proof template:
`M4ArithPool.m4_chiSummedFreeRow_of_doorArithRho_pool`, with the primed fuse
`m4_chiFreeRowSq_sum_at_door_pool'` in place of the landed one. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool'_gated {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorFuseFrame_pool' M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
          ≤ a2Mrow' (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (henv : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) := by
  refine m4_chiSummedFreeRow_of_big
    (m4_chiSummedFreeRowBig_of_doorGradeGated_pool (C₁ := C₁) (M₀ := M₀) (π₀ := π₀) hpool ?_
      henv)
  intro H L q j A s hb
  obtain ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  haveI : NeZero q := ⟨hq.ne'⟩
  have hbb : SocketBase R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hbb
  exact m4_chiFreeRowSq_sum_at_door_pool' hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hbb) (hband H L q j A s hbb) hF.gP1 hF.gRows hF.eps_pool
    hF.band_pool

/-- **⟦D4 — ITEM 11 AT THE `end'` CHAIN, GATED⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated`) — the twin of
`M4RowsChiEndPrime.m4_chiSummedFreeRow_of_doorAssembly_pool_end'` whose `henv` binder is
`SocketBase`-gated, so that `M4ArithPool.m4_arith_henv_rho_pool` can fill it.  Every other
binder is that exit's VERBATIM. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame_pool' M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowEndBase M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          arcDen 12 H * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end'
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_gated (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv

/-- **⟦D4 — ITEM 11 AT THE `zero'` CHAIN, GATED⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated`) — the twin of
`M4RowsChiZeroPrime.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'` at the gated `henv`. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame_pool' M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          arcDen 12 H * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_gated (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot Cp hCp.le R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv

/-! ## §4 — ⟦D7⟧ THE `E_ge` LINE, STANDALONE

`DoorArithFrameRho` is FROZEN: its `arm` field stays at `7000λ`.  The `E_ge` line is minted
here as a standalone gate the assembly can consume, plus a sufficiency form that turns it
into a base-LOWER demand on `loglog X_d`. -/

/-- **⟦THE `E_ge` LINE⟧** (`ege_line_gate`) — the `EP2` gate and the `φ`-row FORCE

  `49920·φ(q) ≤ (log X_d)^{εr}` .

Kernel-certified by the closure examiner (probe `P5`).  Nothing here reads a frame: it is a
two-hypothesis implication between the two inequalities the assembly already carries. -/
theorem ege_line_gate {Nd q : ℕ} {EP2 epsr : ℝ}
    (hL : (0 : ℝ) < Real.log ((Nd : ℕ) : ℝ))
    (hgate : 12 * EP2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293 + epsr))
    (hphi : 4160 * (q.totient : ℝ) * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293) ≤ EP2) :
    49920 * (q.totient : ℝ) ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ epsr := by
  have hpow : (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293 + epsr)
      = (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293) * (Real.log ((Nd : ℕ) : ℝ)) ^ epsr := by
    rw [← Real.rpow_add hL]
  have hp0 : (0 : ℝ) < (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293) := Real.rpow_pos_of_pos hL _
  have h1 : 49920 * (q.totient : ℝ) * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293)
      ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293) * (Real.log ((Nd : ℕ) : ℝ)) ^ epsr := by
    rw [← hpow]; nlinarith [hphi, hgate]
  nlinarith [h1, hp0]

/-- `θ₂₉₃ − 1/500 ≥ 1413/10⁶` — the exponent room the sufficiency form spends.  (`θ₂₉₃ =
1/(32(3e+1)) = 0.00341349…`, so `θ₂₉₃ − 1/500 = 0.00141349…`.) -/
theorem theta293_sub_lower : (1413 : ℝ) / 1000000 ≤ theta293 - 1 / 500 := by
  have he : Real.exp 1 < 2.7182818286 := by have := Real.exp_one_lt_d9; linarith
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hden : (0 : ℝ) < 32 * (3 * Real.exp 1 + 1) := by nlinarith
  have hval : theta293 = 1 / (32 * (3 * Real.exp 1 + 1)) := rfl
  have hkey : (1413 : ℝ) / 1000000 + 1 / 500 ≤ 1 / (32 * (3 * Real.exp 1 + 1)) := by
    rw [le_div_iff₀ hden]; nlinarith
  rw [hval]; linarith

/-- **⟦THE `E_ge` LINE AS A BASE-LOWER DEMAND⟧** (`ege_line_of_loglog`) — at
`εr := θ₂₉₃ − 1/500` and `q ≤ arcDen 12 H = (log H)^{12}` (the `SocketBase` field `q_arcDen`),
the gate `49920·φ(q) ≤ (log X_d)^{εr}` holds as soon as

  `loglog X_d ≥ 8500·loglog H + 7800` .

The examiner's exact worst case is `8489.6·λ + 7653.5`; the constants here are that, rounded
UP to integers with the `log 49920 ≤ 11` slack the kernel proof spends (`e^{11} = 59874 ≥
49920`).  The demand is `1.21×` the frozen `arm`'s `7000λ`, which is why it is stated
STANDALONE rather than folded into `DoorArithFrameRho` — and it is met with astronomic slack
at the socket's x-scale. -/
theorem ege_line_of_loglog {Nd H q : ℕ}
    (hH0 : (0 : ℝ) < Real.log (H : ℝ))
    (hlam : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)))
    (hLNd : (0 : ℝ) < Real.log ((Nd : ℕ) : ℝ))
    (hq : (q : ℝ) ≤ arcDen 12 H)
    (hbase : 8500 * Real.log (Real.log (H : ℝ)) + 7800
      ≤ Real.log (Real.log ((Nd : ℕ) : ℝ))) :
    49920 * (q.totient : ℝ) ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (theta293 - 1 / 500) := by
  have hδ := theta293_sub_lower
  -- `log 49920 ≤ 11`
  have h499 : Real.log 49920 ≤ 11 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have he11 : (49920 : ℝ) ≤ Real.exp 11 := by
      have hh : Real.exp 11 = (Real.exp 1) ^ (11 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      rw [hh]
      have hc : (2.7182818283 : ℝ) ^ (11 : ℕ) ≤ (Real.exp 1) ^ (11 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) h1.le 11
      have : (49920 : ℝ) ≤ (2.7182818283 : ℝ) ^ (11 : ℕ) := by norm_num
      linarith
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 49920) he11
    rwa [Real.log_exp] at this
  -- the arc denominator in exponential form
  have harc : arcDen 12 H = Real.exp (12 * Real.log (Real.log (H : ℝ))) := by
    rw [arcDen, Real.rpow_def_of_pos hH0]; ring_nf
  have hrw : (Real.log ((Nd : ℕ) : ℝ)) ^ (theta293 - 1 / 500)
      = Real.exp ((theta293 - 1 / 500) * Real.log (Real.log ((Nd : ℕ) : ℝ))) := by
    rw [Real.rpow_def_of_pos hLNd]; ring_nf
  rw [hrw]
  -- the exponent budget
  have hbud : Real.log 49920 + 12 * Real.log (Real.log (H : ℝ))
      ≤ (theta293 - 1 / 500) * Real.log (Real.log ((Nd : ℕ) : ℝ)) := by
    have hll : (0 : ℝ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ)) := by linarith
    nlinarith [hδ, hbase, hlam, h499, hll]
  have hφ : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hstep : 49920 * (q.totient : ℝ)
      ≤ Real.exp (Real.log 49920 + 12 * Real.log (Real.log (H : ℝ))) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 49920), ← harc]
    have h0 : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
    nlinarith [hφ, hq, h0]
  exact le_trans hstep (Real.exp_le_exp.mpr hbud)

/-! ## §5 — THE FUSE

The four repairs composed.  ⟦Item 11⟧ of `m4_second_road` at the door's `ρ`-envelope
`RSanDoorRho ρ H`, from the gates alone:

* the pool is `decayPool` (⟦D1⟧), so `hone` is GONE and the summand-3 price is DISCHARGED by
  `DoorArithFrameRho.arm` — no `hprice` binder survives;
* the density constant is the R4 exits' own positive `Cp` (⟦D3⟧), so the `hrows` supplier's
  output type matches the frame's `gRows` field;
* the `henv` binder is `SocketBase`-gated (⟦D4⟧) and is filled by
  `M4ArithPool.m4_arith_henv_rho_pool`.

Both R4 chains are covered: `end'` (the seven-field `DoorRowEndBase`) and `zero'` (the
six-field `DoorRowZeroBase`, at a free positive `C_p`). -/

/-- **⟦THE FUSE, `end'` CHAIN⟧** (`m4_closure_fuse_end'`) — ⟦item 11⟧ at `RSanDoorRho ρ`,
from: the six base-side frame fields, the `𝒯`-leg gate, the FOUR-slot `gRows` gate, the
`ε ≤ 0` pin, the corrected `4096`-threshold, the `end'` chain's per-base bundle, the A3
capstone family, the band supplier, and the `ρ`-arithmetic frame.

**NO `hone`.  NO `hprice`.**  The pool is `decayPool` and the ARM pays. -/
theorem m4_closure_fuse_end' :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (K ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
            ≤ decayPool (A + s)) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          GRowsZeroGate''' M (A + s) Cp (decayPool (A + s))) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowEndBase M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hexit⟩ := m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε K ρ cU bU t₁ hM hb1 hc1 hbf hgP1 hgRows heps hL4096 hbase hcap hband harith
  refine hexit R M C₁ M₀ ε decayPool (fun _ H => RSanDoorRho ρ H) cU bU t₁ hM hb1 hc1
    ?_ hbase hcap hband decayPool_nonneg
    (m4_arith_henv_rho_pool decayPool_nonneg harith (price_at_decayPool_socket harith))
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_cc_decay (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-- **⟦THE FUSE, `zero'` CHAIN⟧** (`m4_closure_fuse_zero'`) — the same, at
`M4RowsChiZeroPrime`'s density-free chain: `C_p` is a FREE positive parameter and the
per-base bundle is the six-field `DoorRowZeroBase`. -/
theorem m4_closure_fuse_zero' :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (K ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
            ≤ decayPool (A + s)) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          GRowsZeroGate''' M (A + s) Cp (decayPool (A + s))) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hexit⟩ := m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε K ρ cU bU t₁ hM hb1 hc1 hbf hgP1 hgRows heps hL4096 hbase hcap
    hband harith
  refine hexit Cp hCp R M C₁ M₀ ε decayPool (fun _ H => RSanDoorRho ρ H) cU bU t₁ hM hb1 hc1
    ?_ hbase hcap hband decayPool_nonneg
    (m4_arith_henv_rho_pool decayPool_nonneg harith (price_at_decayPool_socket harith))
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_cc_decay (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-! ## §6 — ⟦R5b⟧ THE CONSTANT POOL

⟦THE FINDING R5-REPAIR BANKED⟧ §1's `decayPool` pays the summand-3 price out of the frozen
ARM, but it re-introduces base UPPER caps: `gP1`, `GRowsZeroGate'''`'s `level1`/`p2`/`dens`
slots all read `π₀ = (log X_d)^{−θ₂₉₃}` on the RIGHT, and that side DECAYS in `X_d`.  Each of
those four gates therefore caps the base from above.

This section mints the alternative the pinch also admits: the pool is a CONSTANT in the base,

  `constPool ρ H₊ := ρ / (376266 · e^{14·loglog H₊})` ,

so **no gate has `X_d` on the right anywhere**.  The trade, field by field:

| field | at `decayPool` | at `constPool` |
|---|---|---|
| `gP1` | base UPPER cap | **base-free** — a pure constant inequality |
| `gRows.level1`/`.p2`/`.dens` | base UPPER cap | **base-free** |
| `gRows.endpt` | base-LOWER | base-LOWER (`1/X_d → 0`) |
| `eps_pool` | equality at `ε = 0` | base-LOWER (`heps293` below) |
| `band_pool` | base-LOWER (`hL4096`) | base-LOWER (`hband4096` below) |
| the price | the ARM, per base | `H ≤ H₊` monotonicity, EXACT at `H = H₊` |

The two surviving base-side demands are LOWER, so the socket's `A ≤ 2·R.x` cap is not spent
on them.  `376266 = 2·188133` is chosen so the price closes with equality at `H = H₊`: it is
the largest constant pool the summand-3 slot admits over the regime's whole `H`-window. -/

/-- **⟦THE CONSTANT POOL⟧** (`constPool`) — `ρ/(376266·e^{14·loglog H₊})`, the pool value the
summand-3 slot admits UNIFORMLY over the regime's `H`-window `[H₋, H₊]`.  Base-free: the
argument is the regime's UPPER `H`-endpoint, never `X_d`. -/
def constPool (ρ : ℝ) (Hhi : ℕ) : ℝ :=
  ρ / (376266 * Real.exp (14 * Real.log (Real.log (Hhi : ℝ))))

theorem constPool_def (ρ : ℝ) (Hhi : ℕ) :
    constPool ρ Hhi = ρ / (376266 * Real.exp (14 * Real.log (Real.log (Hhi : ℝ)))) := rfl

/-- The constant pool is positive at a positive clearing parameter. -/
theorem constPool_pos {ρ : ℝ} {Hhi : ℕ} (hρ : 0 < ρ) : 0 < constPool ρ Hhi :=
  div_pos hρ (by positivity)

/-- The constant pool is nonnegative — the form `m4_arith_henv_rho_pool`'s `hpool` binder and
`DoorFuseFrame_pool'` both want. -/
theorem constPool_nonneg {ρ : ℝ} {Hhi : ℕ} (hρ : 0 ≤ ρ) : 0 ≤ constPool ρ Hhi :=
  div_nonneg hρ (by positivity)

/-- `loglog` is monotone on the regime's `H`-window: `H ≤ H₊` with `log H > 0` gives
`loglog H ≤ loglog H₊`.  This is the ONLY analytic input the constant pool's price needs. -/
theorem loglog_le_of_le {H Hhi : ℕ} (hHpos : 0 < H) (hlogH : 0 < Real.log (H : ℝ))
    (hle : H ≤ Hhi) :
    Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log (Hhi : ℝ)) := by
  have hcast : ((H : ℕ) : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hle
  have h1 : Real.log (H : ℝ) ≤ Real.log (Hhi : ℝ) :=
    Real.log_le_log (by exact_mod_cast hHpos) hcast
  exact Real.log_le_log hlogH h1

/-- **⟦THE PRICE AT THE CONSTANT POOL⟧** (`price_at_constPool`) — the summand-3 price
`188133·π₀·e^{14·loglog H} ≤ ρ/2` at `π₀ := constPool ρ H₊`, from `loglog H ≤ loglog H₊`
ALONE.  No frame field, no ARM, no base: the `376266 = 2·188133` normalisation makes the
inequality an EQUALITY at `H = H₊` and monotone below it. -/
theorem price_at_constPool {H Hhi : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (hmono : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log (Hhi : ℝ))) :
    188133 * constPool ρ Hhi * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2 := by
  have hEne : Real.exp (14 * Real.log (Real.log (Hhi : ℝ))) ≠ 0 := (Real.exp_pos _).ne'
  have hle : Real.exp (14 * Real.log (Real.log (H : ℝ)))
      ≤ Real.exp (14 * Real.log (Real.log (Hhi : ℝ))) := Real.exp_le_exp.mpr (by linarith)
  have hc0 : (0 : ℝ)
      ≤ 188133 * (ρ / (376266 * Real.exp (14 * Real.log (Real.log (Hhi : ℝ))))) :=
    mul_nonneg (by norm_num) (div_nonneg hρ.le (by positivity))
  rw [constPool_def]
  calc 188133 * (ρ / (376266 * Real.exp (14 * Real.log (Real.log (Hhi : ℝ)))))
        * Real.exp (14 * Real.log (Real.log (H : ℝ)))
      ≤ 188133 * (ρ / (376266 * Real.exp (14 * Real.log (Real.log (Hhi : ℝ)))))
        * Real.exp (14 * Real.log (Real.log (Hhi : ℝ))) := mul_le_mul_of_nonneg_left hle hc0
    _ = ρ / 2 := by field_simp; ring

/-- **⟦THE PRICE WRAPPER, PER SOCKET BASE⟧** (`price_at_constPool_socket`) — the twin of
`price_at_decayPool_socket`: exactly the `hprice` binder of `M4ArithPool.m4_arith_henv_rho_pool`
at `π₀ := fun _ => constPool ρ R.Hhi`.  What discharges it is NOT the ARM but the socket's own
window field `H ≤ R.Hhi` (plus `R.Hlo ≤ H` and the regime's `hHlo_floor` for positivity, and
`DoorArithFrameRho.rho_pos`/`.one_lt_logH` for the two scalar side conditions). -/
theorem price_at_constPool_socket {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {K ρ : ℝ}
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      188133 * constPool ρ R.Hhi * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2 := by
  intro H L q j A s hb
  have hfr := harith H L q j A s hb
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  have hHpos : 0 < H := by have := R.hHlo_floor; omega
  have hlogH : (0 : ℝ) < Real.log (H : ℝ) := by have := hfr.one_lt_logH; linarith
  exact price_at_constPool hfr.rho_pos (loglog_le_of_le hHpos hlogH hhi)

/-- **⟦THE ARITHMETIC GATE AT THE CONSTANT POOL⟧** (`m4_arith_henv_constPool`) — the composed
witness that the wrapper fills `m4_arith_henv_rho_pool` verbatim: `henv` at
`RSbig j H := RSanDoorRho ρ H`, with the pool a CONSTANT in the base. -/
theorem m4_arith_henv_constPool {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {K ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (constPool ρ R.Hhi)
        ≤ RSanDoorRho ρ H :=
  m4_arith_henv_rho_pool (π₀ := fun _ => constPool ρ R.Hhi)
    (fun _ => constPool_nonneg hρ) harith (price_at_constPool_socket harith)

/-- **⟦`eps_pool` FROM A BASE-LOWER THRESHOLD⟧** (`eps_pool_of_threshold`) — pool-generic: at
`ε ≤ 0` the `𝒰`-leg field follows from `(log X_d)^{−θ₂₉₃} ≤ π₀`, a demand that WEAKENS as the
base grows.  At `π₀ := constPool ρ H₊` it reads
`θ₂₉₃·loglog X_d ≥ 14·loglog H₊ + log(376266/ρ)`, i.e.
`loglog X_d ≥ 4102·loglog H₊ + 293·log(376266/ρ)` — the same genre as the frozen ARM's
`7000·loglog H`, and a SMALLER `λ`-coefficient, but read at the window's upper endpoint. -/
theorem eps_pool_of_threshold {Xd : ℕ} {ε π₀ : ℝ}
    (hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ)) (hε : ε ≤ 0)
    (hthr : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293) ≤ π₀) :
    (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀ :=
  le_trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hthr

/-- **⟦`band_pool` FROM A BASE-LOWER THRESHOLD⟧** (`band_pool_of_threshold`) — pool-generic:
`4096 ≤ (log X_d)^{1−1/500}·π₀` gives the band field exactly (the two rpow exponents sum to
`0`).  At `π₀ := (log X_d)^{−θ₂₉₃}` this IS §1's `hL4096`; at `π₀ := constPool ρ H₊` it is a
base-LOWER threshold with no `X_d` on the right. -/
theorem band_pool_of_threshold {Xd : ℕ} {π₀ : ℝ} (h : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ))
    (hL : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500) * π₀) :
    4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ := by
  have hid : (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500)
      * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) = 1 := by
    rw [← Real.rpow_add h]; norm_num
  have hstep := mul_le_mul_of_nonneg_right hL
    (Real.rpow_pos_of_pos h (-(1 : ℝ) + 1 / 500)).le
  have heq : (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500) * π₀
      * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) = π₀ := by
    calc (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500) * π₀
          * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500)
        = π₀ * ((Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500)) := by ring
      _ = π₀ := by rw [hid, mul_one]
  linarith [hstep, heq]

/-- **⟦R5b — THE FRAME AT THE CONSTANT POOL⟧** (`doorFuseFrame_pool'_of_gates_const`) — the
twin of `doorFuseFrame_pool'_of_gates_decay` (and of its `C_cc`-free composition
`doorFuseFrame_pool'_of_gates_cc_decay`, whose four-slot `gRows` gate it carries) at
`π₀ := constPool ρ H₊`.

⟦THE HYPOTHESIS SET, AGAINST THE DECAY TWIN'S⟧ field for field the same SHAPE — `hb`, `hgP1`,
`hg`, `hε`, `hM`, `hXd` and one `4096`-threshold — with two differences, both in the same
direction:

* `hgP1` and `hg` are now BASE-FREE on the right (`constPool` carries no `X_d`), where the
  decay twin's were base UPPER caps;
* the single decay threshold `hL4096 : 4096 ≤ (log X_d)^{1−1/500−θ₂₉₃}` splits into TWO
  base-LOWER thresholds, `heps293` and `hband4096`, because at a constant pool the `𝒰`-leg no
  longer discharges by rpow-exponent monotonicity into `π₀` itself.

Nothing else changes; `ε ≤ 0` is reused verbatim. -/
theorem doorFuseFrame_pool'_of_gates_const {M Xd j Hhi : ℕ} {Cs Ccc ε ρ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ constPool ρ Hhi)
    (hg : GRowsZeroGate''' M Xd Ccc (constPool ρ Hhi))
    (hε : ε ≤ 0)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (heps293 : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293) ≤ constPool ρ Hhi)
    (hband4096 : (4096 : ℝ)
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500) * constPool ρ Hhi) :
    DoorFuseFrame_pool' M Xd j Cs Ccc ε (constPool ρ Hhi) where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate''' hM hXd hg
  eps_pool := eps_pool_of_threshold (r5_one_le_log_of_three_le hb.X_three) hε heps293
  band_pool := band_pool_of_threshold
    (by have := r5_one_le_log_of_three_le hb.X_three; linarith) hband4096

/-! ## §7 — ⟦R5c⟧ THE FUSE AT THE CONSTANT POOL

§5 fused the four repairs at `π₀ := decayPool`; §6 minted the constant pool and its frame
`doorFuseFrame_pool'_of_gates_const`.  This section closes the parity: the SAME two ⟦item 11⟧
exits (`..._pool_end'_gated` / `..._pool_zero'_gated`), now instantiated at
`π₀ := fun _ => constPool ρ R.Hhi`.

⟦THE BINDER DELTA AGAINST §5⟧, per fuse, and nothing else:

* `hρ : 0 ≤ ρ` is NEW — at the decay pool the `hpool` binder was `decayPool_nonneg`, a closed
  fact; at the constant pool nonnegativity is inherited from the clearing parameter;
* the single decay threshold `hL4096` SPLITS into `heps293` and `hband4096`, exactly as
  `doorFuseFrame_pool'_of_gates_const` demands (§6's table);
* `gP1` and the four-slot `gRows` gate are read at `constPool ρ R.Hhi`, so they carry NO `X_d`
  on the right — base-free where §5's were base UPPER caps;
* the price is paid by `m4_arith_henv_constPool` (the socket's own `H ≤ R.Hhi` window field),
  not by `price_at_decayPool_socket`'s ARM.

**NO `hone`.  NO `hprice`.**  As in §5. -/

/-- **⟦THE FUSE AT `constPool`, `end'` CHAIN⟧** (`m4_closure_fuse_end'_const`) — ⟦item 11⟧ at
`RSanDoorRho ρ`, at the CONSTANT pool `π₀ := fun _ => constPool ρ R.Hhi`.  The twin of
`m4_closure_fuse_end'`, binder for binder, with `hρ` added and `hL4096` split into the two
base-LOWER thresholds `heps293`/`hband4096`. -/
theorem m4_closure_fuse_end'_const :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (K ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 ≤ ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          GRowsZeroGate''' M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowEndBase M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hexit⟩ := m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε K ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows heps heps293 hband4096 hbase
    hcap hband harith
  refine hexit R M C₁ M₀ ε (fun _ => constPool ρ R.Hhi) (fun _ H => RSanDoorRho ρ H) cU bU t₁
    hM hb1 hc1 ?_ hbase hcap hband (fun _ => constPool_nonneg hρ)
    (m4_arith_henv_constPool hρ harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (heps293 H L q j A s hb)
    (hband4096 H L q j A s hb)

/-- **⟦THE FUSE AT `constPool`, `zero'` CHAIN⟧** (`m4_closure_fuse_zero'_const`) — the same at
`M4RowsChiZeroPrime`'s density-free chain: `C_p` is a FREE positive parameter and the per-base
bundle is the six-field `DoorRowZeroBase`. -/
theorem m4_closure_fuse_zero'_const :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (K ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 ≤ ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          GRowsZeroGate''' M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hexit⟩ := m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε K ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows heps heps293 hband4096
    hbase hcap hband harith
  refine hexit Cp hCp R M C₁ M₀ ε (fun _ => constPool ρ R.Hhi) (fun _ H => RSanDoorRho ρ H)
    cU bU t₁ hM hb1 hc1 ?_ hbase hcap hband (fun _ => constPool_nonneg hρ)
    (m4_arith_henv_constPool hρ harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (heps293 H L q j A s hb)
    (hband4096 H L q j A s hb)

/-! ## §GK — the G-lever twin

The closure repairs at `G := s13GK K M` (`GLever`), `(K : ℕ)` first.

⟦K-INVARIANT, KEEPS ITS LANDED NAME⟧ §1's `decayPool`, `eps_pool_at_decayPool`,
`band_pool_at_decayPool`, `price_at_decayPool{,_socket}`; §4's whole `E_ge` page
(`ege_line_gate`, `theta293_sub_lower`, `ege_line_of_loglog`); §6's `constPool` and its five
lemmas, `loglog_le_of_le`, `price_at_constPool{,_socket}`, `eps_pool_of_threshold`,
`band_pool_of_threshold`; and `M4ArithPrime.DoorBaseFrame`.  Not one of them reads the door
ladder: they speak `log X_d`, `loglog H`, `θ₂₉₃` and `ρ` only.  `a2Level1 M` (in
`GRowsZeroGate'''.level1`) is LEVEL 1, so that field does not move either — only the `p²`
field, which reads `𝒫₁`/`𝒫₂` directly.

⚠ ⟦THE BINDER SHADOW⟧ §5's and §7's four fuses bind a REAL `K` — ⟦C3⟧'s margined-floor
constant inside `DoorArithFrameRho`.  It is ALPHA-RENAMED to `Kar` so the lever's `(K : ℕ)`
can go first.  Those four, and the two gated ⟦item 11⟧ exits they consume, also carry
`hK : K ≤ 1.7·10⁸` — the side condition of the R4 row slots
(`M4RowsChiEndPrime.m4_hrowsSlot_at_door_end'_gk`,
`M4RowsChiZeroPrime.m4_hrowsSlot_at_door_zero'_gk`). -/

/-- `doorFuseFrame_pool'_of_gates_decay` (:234), at the lever. -/
theorem doorFuseFrame_pool'_of_gates_decay_gk (K : ℕ) {M Xd j : ℕ} {Cs ε : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ decayPool Xd)
    (hg : GRowsZeroGate''_gk K M Xd (decayPool Xd))
    (hε : ε ≤ 0)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) :
    DoorFuseFrame_pool'_gk K M Xd j Cs 0 ε (decayPool Xd) where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate''_gk K hM hXd hg
  eps_pool := eps_pool_at_decayPool (r5_one_le_log_of_three_le hb.X_three) hε
  band_pool := band_pool_at_decayPool
    (by have := r5_one_le_log_of_three_le hb.X_three; linarith) hL4096

/-- `GRowsZeroGate'''` (:278), at the lever.  Only the `p²` field moves. -/
structure GRowsZeroGate'''_gk (K : ℕ) (M Xd : ℕ) (Ccc π₀ : ℝ) : Prop where
  /-- ⟦THE LEVEL-1 SLOT⟧ base-free. -/
  level1 : 14400 * Real.exp 1 ^ 2 * a2Level1 M ≤ 1 / 4 * π₀
  /-- ⟦THE ENDPOINT SLOT⟧ the only base-reading slot, and base-LOWER. -/
  endpt : 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ)) ≤ 1 / 4 * π₀
  /-- ⟦THE `p²` SLOT, R1⟧ `X_d`-FREE, at the levered ladder. -/
  p2 : 138240 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)
        + 1 / ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ))
      ≤ 1 / 4 * π₀
  /-- **⟦THE DENSITY SLOT — D3⟧** the debit `GRowsZeroGate''_gk` pinned to `0`. -/
  dens : 5760 * Ccc * (2 / (M : ℝ)) ≤ 1 / 4 * π₀

/-- `gRowsZeroGate''_of_gate'''` (:292), at the lever. -/
theorem gRowsZeroGate''_of_gate'''_gk {K M Xd : ℕ} {π₀ : ℝ} (hπ : 0 ≤ π₀)
    (hg : GRowsZeroGate'''_gk K M Xd 0 π₀) : GRowsZeroGate''_gk K M Xd π₀ where
  level1 := by have := hg.level1; linarith
  endpt := by have := hg.endpt; linarith
  p2 := by have := hg.p2; linarith

/-- `gRows_zero_of_gate'''` (:304), at the lever. -/
theorem gRows_zero_of_gate'''_gk (K : ℕ) {M Xd : ℕ} {Ccc π₀ : ℝ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hg : GRowsZeroGate'''_gk K M Xd Ccc π₀) :
    5760 * (a2RowsSum'_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ := by
  rw [a2RowsSum'_door_decomp_gk K hM hXd]
  have hid : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1 M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 24 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)
              + 1 / ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ))
        + Ccc * (2 / (M : ℝ)))
      = 14400 * Real.exp 1 ^ 2 * a2Level1 M
        + 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ))
        + 138240 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)
              + 1 / ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ))
        + 5760 * Ccc * (2 / (M : ℝ)) := by ring
  rw [hid]
  linarith [hg.level1, hg.endpt, hg.p2, hg.dens]

/-- `doorFuseFrame_pool'_of_gates_cc` (:324), at the lever. -/
theorem doorFuseFrame_pool'_of_gates_cc_gk (K : ℕ) {M Xd j : ℕ} {Cs Ccc ε π₀ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hg : GRowsZeroGate'''_gk K M Xd Ccc π₀)
    (hone : (1 : ℝ) ≤ π₀)
    (hε : ε ≤ theta293)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)) :
    DoorFuseFrame_pool'_gk K M Xd j Cs Ccc ε π₀ where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate'''_gk K hM hXd hg
  eps_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := r5_one_le_log_of_three_le hb.X_three
    have hle : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      simpa using this
    linarith
  band_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := r5_one_le_log_of_three_le hb.X_three
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
    have habs : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) := by
      have hsp : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          = (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)
            * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) := by
        rw [← Real.rpow_add hL0]; norm_num
      rw [hsp]
      exact mul_le_mul_of_nonneg_right hL4096 (le_of_lt (Real.rpow_pos_of_pos hL0 _))
    have hone' : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      simpa using this
    linarith

/-- `doorFuseFrame_pool'_of_gates_cc_decay` (:371), at the lever. -/
theorem doorFuseFrame_pool'_of_gates_cc_decay_gk (K : ℕ) {M Xd j : ℕ} {Cs Ccc ε : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ decayPool Xd)
    (hg : GRowsZeroGate'''_gk K M Xd Ccc (decayPool Xd))
    (hε : ε ≤ 0)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) :
    DoorFuseFrame_pool'_gk K M Xd j Cs Ccc ε (decayPool Xd) where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate'''_gk K hM hXd hg
  eps_pool := eps_pool_at_decayPool (r5_one_le_log_of_three_le hb.X_three) hε
  band_pool := band_pool_at_decayPool
    (by have := r5_one_le_log_of_three_le hb.X_three; linarith) hL4096

/-- `m4_chiSummedFreeRow_of_doorAssembly_join_cc` (:396), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_join_cc_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hbase : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j)
    (hgP1 : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      374784 * Cs (A + s) * Real.exp 3
          * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ (A + s))
    (hgRows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      GRowsZeroGate'''_gk K M (A + s) (Ccc (A + s)) (π₀ (A + s)))
    (hone : ∀ A : ℕ, (1 : ℝ) ≤ π₀ A)
    (heps : ∀ A : ℕ, ε A ≤ theta293)
    (hL4096 : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 250))
    (hrows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow'_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_gk K (Cs := Cs) (Ccc := Ccc) (C₁ := C₁)
    (M₀ := M₀) (ε := ε) (π₀ := π₀) hM ?_ hrows hband
    (fun A => le_trans zero_le_one (hone A)) henv
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_cc_gk K (hbase H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (hone (A + s)) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-- `m4_chiSummedFreeRow_of_doorAssembly_pool'_gated` (:455), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorFuseFrame_pool'_gk K M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow'_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (henv : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M RSbig) := by
  refine m4_chiSummedFreeRow_of_big_gk K
    (m4_chiSummedFreeRowBig_of_doorGradeGated_pool_gk K (C₁ := C₁) (M₀ := M₀) (π₀ := π₀)
      hpool ?_ henv)
  intro H L q j A s hb
  obtain ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  haveI : NeZero q := ⟨hq.ne'⟩
  have hbb : SocketBase R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hbb
  exact m4_chiFreeRowSq_sum_at_door_pool'_gk K hM hF.X_exp hF.X_three hF.h_four hF.h_window
    hF.tann hF.ceil5 (hrows H L q j A s hbb) (hband H L q j A s hbb) hF.gP1 hF.gRows
    hF.eps_pool hF.band_pool

/-- `m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated` (:498), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated_gk (K : ℕ)
    (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame_pool'_gk K M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorRowEndBase_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          arcDen 12 H * a2DoorGrade_pool_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M RSbig) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end'_gk K hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_gk K (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv

/-- `m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated` (:544), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_gk (K : ℕ)
    (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame_pool'_gk K M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorRowZeroBase_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          arcDen 12 H * a2DoorGrade_pool_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M RSbig) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_gk K (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot Cp hCp.le R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv

/-- `m4_closure_fuse_end'` (:698), at the lever. -/
theorem m4_closure_fuse_end'_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kar ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ decayPool (A + s)) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          GRowsZeroGate'''_gk K M (A + s) Cp (decayPool (A + s))) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorRowEndBase_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) →
        M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hexit⟩ :=
    m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated_gk K hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε Kar ρ cU bU t₁ hM hb1 hc1 hbf hgP1 hgRows heps hL4096 hbase hcap hband
    harith
  refine hexit R M C₁ M₀ ε decayPool (fun _ H => RSanDoorRho ρ H) cU bU t₁ hM hb1 hc1
    ?_ hbase hcap hband decayPool_nonneg
    (m4_arith_henv_rho_pool_gk K decayPool_nonneg harith (price_at_decayPool_socket harith))
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_cc_decay_gk K (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-- `m4_closure_fuse_zero'` (:754), at the lever. -/
theorem m4_closure_fuse_zero'_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kar ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ decayPool (A + s)) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          GRowsZeroGate'''_gk K M (A + s) Cp (decayPool (A + s))) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorRowZeroBase_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) →
        M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hexit⟩ := m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε Kar ρ cU bU t₁ hM hb1 hc1 hbf hgP1 hgRows heps hL4096 hbase hcap
    hband harith
  refine hexit Cp hCp R M C₁ M₀ ε decayPool (fun _ H => RSanDoorRho ρ H) cU bU t₁ hM hb1 hc1
    ?_ hbase hcap hband decayPool_nonneg
    (m4_arith_henv_rho_pool_gk K decayPool_nonneg harith (price_at_decayPool_socket harith))
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_cc_decay_gk K (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-- `m4_arith_henv_constPool` (:904), at the lever. -/
theorem m4_arith_henv_constPool_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ}
    {Kar ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (constPool ρ R.Hhi)
        ≤ RSanDoorRho ρ H :=
  m4_arith_henv_rho_pool_gk K (π₀ := fun _ => constPool ρ R.Hhi)
    (fun _ => constPool_nonneg hρ) harith (price_at_constPool_socket harith)

/-- `doorFuseFrame_pool'_of_gates_const` (:964), at the lever. -/
theorem doorFuseFrame_pool'_of_gates_const_gk (K : ℕ) {M Xd j Hhi : ℕ} {Cs Ccc ε ρ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ constPool ρ Hhi)
    (hg : GRowsZeroGate'''_gk K M Xd Ccc (constPool ρ Hhi))
    (hε : ε ≤ 0)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (heps293 : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293) ≤ constPool ρ Hhi)
    (hband4096 : (4096 : ℝ)
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500) * constPool ρ Hhi) :
    DoorFuseFrame_pool'_gk K M Xd j Cs Ccc ε (constPool ρ Hhi) where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate'''_gk K hM hXd hg
  eps_pool := eps_pool_of_threshold (r5_one_le_log_of_three_le hb.X_three) hε heps293
  band_pool := band_pool_of_threshold
    (by have := r5_one_le_log_of_three_le hb.X_three; linarith) hband4096

/-- `m4_closure_fuse_end'_const` (:1011), at the lever. -/
theorem m4_closure_fuse_end'_const_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kar ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 ≤ ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          GRowsZeroGate'''_gk K M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorRowEndBase_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) →
        M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hexit⟩ :=
    m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated_gk K hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε Kar ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows heps heps293 hband4096 hbase
    hcap hband harith
  refine hexit R M C₁ M₀ ε (fun _ => constPool ρ R.Hhi) (fun _ H => RSanDoorRho ρ H) cU bU t₁
    hM hb1 hc1 ?_ hbase hcap hband (fun _ => constPool_nonneg hρ)
    (m4_arith_henv_constPool_gk K hρ harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_gk K (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (heps293 H L q j A s hb)
    (hband4096 H L q j A s hb)

/-- `m4_closure_fuse_zero'_const` (:1072), at the lever. -/
theorem m4_closure_fuse_zero'_const_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kar ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 ≤ ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          GRowsZeroGate'''_gk K M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorRowZeroBase_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) →
        M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hexit⟩ := m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε Kar ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows heps heps293 hband4096
    hbase hcap hband harith
  refine hexit Cp hCp R M C₁ M₀ ε (fun _ => constPool ρ R.Hhi) (fun _ H => RSanDoorRho ρ H)
    cU bU t₁ hM hb1 hc1 ?_ hbase hcap hband (fun _ => constPool_nonneg hρ)
    (m4_arith_henv_constPool_gk K hρ harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_gk K (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (heps293 H L q j A s hb)
    (hband4096 H L q j A s hb)

end Salt.MR

-- #audit (temporary)
