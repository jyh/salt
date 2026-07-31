/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S14Compose
import Salt.MR.S11HoistGrade

/-!
# ⟦S12-CONST⟧ — THE CAPSTONE TWIN AT THE CONSTANT POOL, WITH `εr` FREED POSITIVE

⟦THE GRANT⟧ CONST-VERDICT + maestro ruling 8 (`docs/blueprints/flags.md`, 2026-07-30 21:49):
the decay road is dead (`S14Compose.s14_gRows_kill`), the raw-`B4` road is dead (the `4320×`
seam shortfall), and the ONE surviving road is `constPool` at `Cp := 0` with the crossing
exponent `εr` freed POSITIVE.  This file is that road's statement layer.

Everything here is PURELY ADDITIVE: no landed declaration is edited anywhere.

## §0 — the ported numeric engine

`s12c_lambda_core` is the CONST-VERDICT λ-engine at the coefficient this file needs
(`14·λ^{9/2} + 10^{15} ≤ 2·10^{−4}·e^λ` for `λ ≥ 50`; the verdict's own certificate is stated
at `1.7·10^{−3}`, which is `8.5×` too weak for the `500×` threshold of §1).  `s12c_llX_ge`
is the socket's x-scale figure `½·e^λ ≤ loglog X_d`, re-derived from
`S14Compose.s14_loglogX_ge_of_socket`.

## §1 — ⟦PIECE 1⟧ THE POSITIVE-`ε` STONE

`eps_pool_const_pos`: the `𝒰`-leg field `(log X_d)^{−θ₂₉₃+ε} ≤ constPool ρ H₊` at ANY `ε`,
from ONE budget line

  `14·loglog H₊ + log 376266 + log(1/ρ) ≤ (θ₂₉₃ − ε)·loglog X_d`.

Since `−θ₂₉₃ + ε < 0` for `ε < θ₂₉₃`, the left side DECAYS in `X_d` and the budget is a
base-LOWER threshold — which is exactly what `constPool` admits and `decayPool` does not
(`M4ClosureRepair.eps_pool_at_decayPool` needs `ε ≤ 0`; that pin is what pinned `εr ≡ 0` and
killed `DoorCapBasePerBlock.abs8640`).  At the target instantiation `ε := θ₂₉₃ − 1/500` the
divisor is `1/500`, so the demand is `loglog X_d ≥ 500·(14·loglog H₊ + log(376266/ρ))`;
`s12c_eps_threshold_at_socket` discharges it at every socket base — the direction check is
`500·(14λ^{9/2} + 10^{15}) ≤ 0.1·e^λ` against the socket's `loglog X_d ≥ 0.5·e^λ`, a `5×`
margin on top of the λ-engine's own ~`700×`.

## §2 — ⟦PIECE 2⟧ THE FRAME TWIN AT POSITIVE `ε`

`doorFuseFrame_pool'_of_gates_const_pos` is `M4ClosureRepair.doorFuseFrame_pool'_of_gates_const`
with the `hε : ε ≤ 0` binder replaced by `hρ : 0 < ρ` and §1's threshold.  Every other field is
that theorem's, verbatim.

⚠ The landed const frame's `heps293` binder is NOT carried here: its ONLY consumer in that
theorem is the `eps_pool` field, which §1's threshold now supplies at every `ε` (and the
threshold IMPLIES `heps293` whenever `0 ≤ ε`).  Carrying it would leave a named binder unused.
It IS carried, unchanged, by §3 and §4 — where the residue list is a specification and the
verdict's certificate `constv_heps293_at_socket` discharges it directly.

## §3 — ⟦PIECE 3⟧ THE FUSE AT `constPool`, `0 ≤ Cp`, POSITIVE `ε`

`m4_closure_fuse_zero'_const_nonneg` = `M4ClosureRepair.m4_closure_fuse_zero'_const` with

* `0 < Cp` relaxed to `0 ≤ Cp` (the byte model is `S12FuseCompose.m4_closure_fuse_zero'_nonneg`:
  route through `m4_chiSummedFreeRow_of_doorAssembly_pool'_gated` + `m4_hrowsSlot_at_door_zero'`
  instead of through `..._pool_zero'_gated`'s strict wrapper) — ruling 8 enters the road at
  `Cp := 0`, where the verdict's `constv_dens_at_zero` makes the `dens` slot FREE;
* `0 ≤ ρ` strengthened to `0 < ρ` (§1's stone reads the pool in exponential form);
* the pool pin `∀ A, ε A ≤ 0` replaced by §1's per-socket-base threshold.

## §4 — ⟦PIECE 4⟧ THE CAPSTONE TWIN

`logChowla2_capstone_final_const'` is `S12FuseCompose.logChowla2_capstone_final_rawcap'` with
the ⟦B1'⟧ block re-cut to the constant pool.  Prefix, conclusion, ⟦A⟧-group, ⟦B2⟧'s window,
⟦B3⟧, ⟦B4⟧, ⟦B5⟧, ⟦B6⟧ and the EDGE-5 `Hcap` carry are byte-identical.

⟦THE DELTA⟧ OUT (3): the decay `gP1`, the decay `GRowsZeroGate'''`, the decay `4096`
threshold.  IN (4): `gP1` at `constPool ρ R.Hhi`, `GRowsZeroGate'''` at `constPool ρ R.Hhi`,
`heps293` (`(log X_d)^{−θ₂₉₃} ≤ constPool ρ R.Hhi`) and `hband4096`
(`4096 ≤ (log X_d)^{1−1/500}·constPool ρ R.Hhi`), all at
`ρ := doorRhoOfDelta (s12DeltaSock δ₀ K)`.  PLUS: the pool pin `∀ A, epsrf A ≤ 0` — the binder
that forced `epsrf ≡ 0` against ⟦B2⟧'s `0 ≤ epsrf` and so made `abs8640` read `8640 ≤ 1` — is
REPLACED by §1's threshold.  ⟦B2⟧'s window `0 ≤ epsrf ≤ θ₂₉₃ − 1/500` is kept exactly as
landed, and is now SATISFIABLE at its upper endpoint.  That is the whole point of the road.

⚠ `heps293` is carried per the ruling's four-slot residue list and is INERT in the proof
(written `_heps293`, the `_epsf` precedent): §1's threshold subsumes it at every `0 ≤ epsrf`.
It is kept so the twin's residue list matches the four slots CONST-VERDICT certified.

Nothing is fired here; the compose comes after CAPGATE.

## §5 — ⟦PIECE 5⟧ THE TWIN AT THE GRADED BAND WIRE

`logChowla2_capstone_final_const'_graded` is §4's twin with the UNGRADED band wire replaced by
`S12FuseCompose.m4_fuse_hband_of_bandBase_graded` (⟦B5-HOIST⟧).  The graded wire carries the
`M`-slope `C' ≤ Cb·M^{2.1}` with `Cb` in the top constant block, so
`S11HoistGrade.s11_grade_absorption` pays `S13BandGate.grade` at an explicit `M`-floor `Mfl`
instead of leaving it a naked hypothesis on the consumer.  The delta against §4 is two lines:
`Mfl` joins the top block (`1 ≤ Mfl`, and `1 ≤ M` becomes `Mfl ≤ M` — the selection genre),
and the payload delivers `8·C' ≤ (log 2 · doorRowFloor M)^{s13Aexp − 1/2 + 1/1000}`.  All
sixteen residue binders are §4's, byte for byte.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — THE PORTED NUMERIC ENGINE -/

/-- `3 ≤ X_d` gives `1 ≤ log X_d` (the private helper of `M4ClosureRepair` §1, re-derived). -/
private lemma s12c_one_le_log_of_three_le {Xd : ℕ} (h : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ)) :
    (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
  have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) h
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ (3 : ℝ))
    rwa [Real.log_exp] at this
  linarith

private lemma s12c_exp45 : (25000000000000000000 : ℝ) ≤ Real.exp 45 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h : Real.exp 45 = (Real.exp 1) ^ (45 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : (2.7 : ℝ) ^ (45 : ℕ) ≤ (Real.exp 1) ^ (45 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h1.le 45
  have hn : (25000000000000000000 : ℝ) ≤ (2.7 : ℝ) ^ (45 : ℕ) := by norm_num
  rw [h]; linarith

private lemma s12c_exp5 : (143 : ℝ) ≤ Real.exp 5 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h : Real.exp 5 = (Real.exp 1) ^ (5 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : (2.7 : ℝ) ^ (5 : ℕ) ≤ (Real.exp 1) ^ (5 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h1.le 5
  have hn : (143 : ℝ) ≤ (2.7 : ℝ) ^ (5 : ℕ) := by norm_num
  rw [h]; linarith

/-- `log 376266 ≤ 13` — the additive constant of `constPool`'s divisor. -/
theorem s12c_log376266 : Real.log 376266 ≤ 13 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h : Real.exp 13 = (Real.exp 1) ^ (13 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : (2.7 : ℝ) ^ (13 : ℕ) ≤ (Real.exp 1) ^ (13 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h1.le 13
  have hn : (376266 : ℝ) ≤ (2.7 : ℝ) ^ (13 : ℕ) := by norm_num
  have hle : (376266 : ℝ) ≤ Real.exp 13 := by rw [h]; linarith
  have := Real.log_le_log (by norm_num : (0 : ℝ) < 376266) hle
  rwa [Real.log_exp] at this

/-- **⟦THE λ-ENGINE, AT THE `500×` COEFFICIENT⟧** (`s12c_lambda_core`) — for `λ ≥ 50`,
`14·λ^{9/2} + 10^{15} ≤ 2·10^{−4}·e^λ`.

CONST-VERDICT's `constv_lambda_core` is the same statement at `1.7·10^{−3}`; §1's threshold
carries a `500×` coefficient against the socket's `½·e^λ`, so it needs the right side below
`10^{−3}`.  The proof is the verdict's, verbatim — `e^λ ≥ e^{45}·e^5·W` with
`W := e^{λ/10−5} ≥ (λ/50)^5`, i.e. `e^λ ≥ 3.575·10^{21}·W` against a left side of at most
`(4.375·10^9 + 10^{15})·W` — so the true margin at `2·10^{−4}` is still a factor `715`. -/
theorem s12c_lambda_core {lam : ℝ} (hlam : 50 ≤ lam) :
    14 * lam ^ ((9 : ℝ) / 2) + 1000000000000000 ≤ 0.0002 * Real.exp lam := by
  have hlam1 : (1 : ℝ) ≤ lam := by linarith
  have hpow45 : lam ^ ((9 : ℝ) / 2) ≤ lam ^ (5 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hlam1 (by norm_num : (9 : ℝ) / 2 ≤ (5 : ℝ))
    rwa [show ((5 : ℝ)) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  set W : ℝ := Real.exp (lam / 10 - 5) with hW
  have hWpos : (0 : ℝ) < W := Real.exp_pos _
  have hW1 : (1 : ℝ) ≤ W := by
    rw [hW]
    have : (0 : ℝ) ≤ lam / 10 - 5 := by linarith
    calc (1 : ℝ) = Real.exp 0 := by simp
      _ ≤ Real.exp (lam / 10 - 5) := Real.exp_le_exp.mpr this
  have hstep : lam / 50 ≤ Real.exp (lam / 50 - 1) := by
    have := Real.add_one_le_exp (lam / 50 - 1); linarith
  have hfifth : (lam / 50) ^ (5 : ℕ) ≤ W := by
    have h5 : (lam / 50) ^ (5 : ℕ) ≤ (Real.exp (lam / 50 - 1)) ^ (5 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hstep 5
    have hid : (Real.exp (lam / 50 - 1)) ^ (5 : ℕ) = W := by
      rw [hW, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    linarith [h5, hid.ge, hid.le]
  have hlam5 : lam ^ (5 : ℕ) ≤ 312500000 * W := by
    have hid : lam ^ (5 : ℕ) = 312500000 * (lam / 50) ^ (5 : ℕ) := by ring
    rw [hid]; nlinarith [hfifth]
  have hexpsplit : Real.exp 45 * (Real.exp 5 * W) ≤ Real.exp lam := by
    have hid : Real.exp 45 * (Real.exp 5 * W) = Real.exp (45 + 5 + (lam / 10 - 5)) := by
      rw [hW, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [hid]
    exact Real.exp_le_exp.mpr (by linarith)
  have hbig : 3575000000000000000000 * W ≤ Real.exp lam := by
    have hA : (25000000000000000000 : ℝ) * 143 ≤ Real.exp 45 * Real.exp 5 := by
      nlinarith [s12c_exp45, s12c_exp5, Real.exp_pos (45 : ℝ), Real.exp_pos (5 : ℝ)]
    have h1 : (25000000000000000000 : ℝ) * 143 * W ≤ Real.exp 45 * Real.exp 5 * W :=
      mul_le_mul_of_nonneg_right hA hWpos.le
    have h2 : Real.exp 45 * Real.exp 5 * W = Real.exp 45 * (Real.exp 5 * W) := by ring
    nlinarith [h1, h2.le, h2.ge, hexpsplit]
  nlinarith [hpow45, hlam5, hbig, hW1, hWpos]

/-- **⟦THE SOCKET'S `loglog X_d`, AGAINST `e^λ`⟧** (`s12c_llX_ge`) — `½·e^{loglog H₋} ≤
loglog X_d` at every socket base of a regime carrying the capstone's absorbed
`loglogFloor50`.  CONST-VERDICT's `constv_llX_ge`, re-derived from
`S14Compose.s14_loglogX_ge_of_socket`. -/
theorem s12c_llX_ge {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) / 2
      ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ R.Hlo := R.hHlo_floor
  have hHR : (4000000 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast hH4
  have hlogHlopos : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hcast : ((R.Hlo : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo
  have hmono : Real.log ((R.Hlo : ℕ) : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hcast
  have hsharp := s14_loglogX_ge_of_socket hfl hb
  rw [Real.exp_log hlogHlopos]
  linarith

/-! ## §1 — ⟦PIECE 1⟧ THE POSITIVE-`ε` STONE -/

/-- **⟦`eps_pool` AT `constPool`, AT ANY `ε`⟧** (`eps_pool_const_pos`).

The `𝒰`-leg field of `DoorFuseFrame_pool'` at the CONSTANT pool, from one budget line.  No
sign condition on `ε` is needed: the budget's coefficient `θ₂₉₃ − ε` carries the whole
dependence, so the stone covers the landed `ε ≤ 0` regime and the road's target
`ε := θ₂₉₃ − 1/500` alike.  At `ε < θ₂₉₃` the exponent `−θ₂₉₃ + ε` is NEGATIVE, so the left
side decays in `X_d` and the budget is a base-LOWER threshold — the property `constPool` has
and `decayPool` (whose right side decays at the same rate) has not. -/
theorem eps_pool_const_pos {Xd Hhi : ℕ} {ε ρ : ℝ}
    (hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ)) (hρ : 0 < ρ)
    (hthr : 14 * Real.log (Real.log ((Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
      ≤ (theta293 - ε) * Real.log (Real.log ((Xd : ℕ) : ℝ))) :
    (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ constPool ρ Hhi := by
  have hX0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hpool : constPool ρ Hhi
      = Real.exp (Real.log ρ - Real.log 376266
        - 14 * Real.log (Real.log ((Hhi : ℕ) : ℝ))) := by
    rw [constPool_def, Real.exp_sub, Real.exp_sub, Real.exp_log hρ,
      Real.exp_log (by norm_num : (0 : ℝ) < 376266), div_div]
  have hlhs : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε)
      = Real.exp ((-theta293 + ε) * Real.log (Real.log ((Xd : ℕ) : ℝ))) := by
    rw [Real.rpow_def_of_pos hX0]; congr 1; ring
  rw [hlhs, hpool]
  refine Real.exp_le_exp.mpr ?_
  have hflip : (-theta293 + ε) * Real.log (Real.log ((Xd : ℕ) : ℝ))
      = -((theta293 - ε) * Real.log (Real.log ((Xd : ℕ) : ℝ))) := by ring
  rw [hflip]
  linarith

/-- **⟦THE THRESHOLD, DISCHARGED AT EVERY SOCKET BASE⟧** (`s12c_eps_threshold_at_socket`) —
§1's budget line at any `ε ≤ θ₂₉₃ − 1/500`, from the twin's OWN payload (the `9/2` tower
`Λ ≤ λ^{9/2}` and the absorbed `loglogFloor50`) plus a clearing charge `log(1/ρ) ≤ 10^{14}`
(`doorRhoOfDelta` gives `ρ ≤ 1`, so the charge is the only ρ-side demand).

⟦THE DIRECTION⟧ `θ₂₉₃ − ε ≥ 1/500`, so the demand is
`500·(14Λ + log 376266 + log(1/ρ)) ≤ loglog X_d`.  The λ-engine caps the bracket by
`2·10^{−4}·e^λ`, i.e. the demand by `0.1·e^λ`; the socket delivers `loglog X_d ≥ 0.5·e^λ`. -/
theorem s12c_eps_threshold_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ ε : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) ^ ((9 : ℝ) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000)
    (hε : ε ≤ theta293 - 1 / 500) :
    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
      ≤ (theta293 - ε) * Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hll := s12c_llX_ge hfl hb
  have hcore := s12c_lambda_core hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by linarith
  have hcoef : (1 : ℝ) / 500 ≤ theta293 - ε := by linarith
  have hprod : (1 : ℝ) / 500 * ll ≤ (theta293 - ε) * ll :=
    mul_le_mul_of_nonneg_right hcoef hll0
  have h1 : 14 * Λ ≤ 14 * lam ^ ((9 : ℝ) / 2) := by linarith
  linarith

/-- **⟦THE `𝒰`-LEG FIELD AT `constPool`, AT THE SOCKET, AT POSITIVE `ε`⟧**
(`eps_pool_const_pos_at_socket`) — §1's stone composed with its socket discharge.  This is
the form a compose consumes: the frame field itself, at every `ε ≤ θ₂₉₃ − 1/500` and in
particular at the road's fire point `ε := θ₂₉₃ − 1/500 > 0`. -/
theorem eps_pool_const_pos_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ ε : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hρ : 0 < ρ)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) ^ ((9 : ℝ) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000)
    (hε : ε ≤ theta293 - 1 / 500) :
    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε) ≤ constPool ρ R.Hhi := by
  refine eps_pool_const_pos ?_ hρ (s12c_eps_threshold_at_socket hfl hb hlam htow hrho hε)
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
  have := Real.log_le_log hA0 hAX
  linarith

/-! ## §2 — ⟦PIECE 2⟧ THE FRAME TWIN AT POSITIVE `ε` -/

/-- **⟦R5b-POS — THE FRAME AT THE CONSTANT POOL, `ε` UNPINNED⟧**
(`doorFuseFrame_pool'_of_gates_const_pos`) — `M4ClosureRepair.doorFuseFrame_pool'_of_gates_const`
with the `hε : ε ≤ 0` binder REPLACED by `hρ : 0 < ρ` together with §1's threshold, and the
`eps_pool` field discharged from `eps_pool_const_pos` instead of from the `ε ≤ 0` collapse.
`hb`, `hgP1`, `hg`, `hM`, `hXd` and `hband4096` are that theorem's, byte for byte, and every
field but `eps_pool` is filled by the same term.

⚠ the landed const frame's `heps293` binder is NOT among the hypotheses: its only consumer
there is `eps_pool`, and §1's threshold supplies that field at every `ε` (indeed the threshold
IMPLIES `heps293` at every `0 ≤ ε`).  §3 and §4 carry `heps293` unchanged. -/
theorem doorFuseFrame_pool'_of_gates_const_pos {M Xd j Hhi : ℕ} {Cs Ccc ε ρ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ constPool ρ Hhi)
    (hg : GRowsZeroGate''' M Xd Ccc (constPool ρ Hhi))
    (hρ : 0 < ρ)
    (hthr : 14 * Real.log (Real.log ((Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
      ≤ (theta293 - ε) * Real.log (Real.log ((Xd : ℕ) : ℝ)))
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
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
  eps_pool := eps_pool_const_pos (s12c_one_le_log_of_three_le hb.X_three) hρ hthr
  band_pool := band_pool_of_threshold
    (by have := s12c_one_le_log_of_three_le hb.X_three; linarith) hband4096

/-! ## §3 — ⟦PIECE 3⟧ THE FUSE AT `constPool`, `0 ≤ C_p`, POSITIVE `ε` -/

/-- **⟦THE FUSE AT `constPool`, `zero'` CHAIN, AT `0 ≤ C_p` AND POSITIVE `ε`⟧**
(`m4_closure_fuse_zero'_const_nonneg`).

`M4ClosureRepair.m4_closure_fuse_zero'_const` with three binder changes and nothing else:

* `0 < Cp` → `0 ≤ Cp`.  Nothing below the fuse uses the strictness (the density constant
  enters only through `GRowsZeroGate'''.dens`, which the caller supplies, and through
  `M4RowsChiZeroPrime.m4_hrowsSlot_at_door_zero'`, whose own binder is `0 ≤ Cp`).  The proof is
  `S12FuseCompose.m4_closure_fuse_zero'_nonneg`'s: apply
  `m4_chiSummedFreeRow_of_doorAssembly_pool'_gated` directly rather than through
  `..._pool_zero'_gated`'s strict wrapper.  Ruling 8 enters the road at `Cp := 0`.
* `0 ≤ ρ` → `0 < ρ` (§1's stone reads `constPool` in exponential form); the `hpool` and price
  binders still take `constPool_nonneg`/`m4_arith_henv_constPool` at `hρ.le`.
* the pool pin `∀ A, ε A ≤ 0` → §1's per-socket-base threshold, so the fuse's ONE `ε` — the
  same one its `hcap` binder reads — is free to be POSITIVE.

`heps293` is carried in place, unchanged; it is inert on this route (§1's threshold subsumes
it at every `0 ≤ ε`) and kept so the demand list matches CONST-VERDICT's four certified slots. -/
theorem m4_closure_fuse_zero'_const_nonneg :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (K ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 < ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          GRowsZeroGate''' M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
            ≤ (theta293 - ε (A + s)) * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
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
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε K ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows hthr _heps293 hband4096
    hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_gated (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := fun _ => constPool ρ R.Hhi)
    (RSbig := fun _ H => RSanDoorRho ρ H) hM ?_
    (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband
    (fun _ => constPool_nonneg hρ.le) (m4_arith_henv_constPool hρ.le harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_pos (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) hρ (hthr H L q j A s hb) hM hXd (hband4096 H L q j A s hb)

/-! ## §4 — ⟦PIECE 4⟧ THE CAPSTONE TWIN AT THE CONSTANT POOL -/

set_option maxHeartbeats 1000000 in
-- Same cause as `S12FuseCompose` §4/§5: the statement re-elaborates the full residue against
-- the re-cut prefix.
/-- **⟦THE CAPSTONE TWIN AT THE CONSTANT POOL⟧** (`logChowla2_capstone_final_const'`).

`S12FuseCompose.logChowla2_capstone_final_rawcap'` with the ⟦B1'⟧ block re-cut to
`constPool ρ R.Hhi` at `ρ := doorRhoOfDelta (s12DeltaSock δ₀ K)`.  UNCHANGED, byte for byte:
the prefix (the eleven constants, `x₀` and `Hcap` in the top block, `∀ Cp ≥ 0`, `R` before
`M`, `C'` after `M`), the EDGE-5 payload conjunct `R.Hlo ≤ max Hcap U1floor`, the conclusion
`¬ logChowla2Fails R.eps R.x R.ω`, the ⟦A⟧-group spine arithmetic, ⟦B2⟧'s `epsrf` window,
⟦B3⟧'s five-field per-base bundle, ⟦B4⟧'s RAW crossing bound, ⟦B5⟧ (`DoorBandBase`) and
⟦B6⟧ (`DoorArithFrameRho`).

⟦THE DELTA⟧ three demands OUT, four IN, plus one replacement:

* OUT — the decay `gP1`, the decay `GRowsZeroGate''' M (A+s) Cp (decayPool (A+s))` (FALSE at
  every socket base the road reaches: `S14Compose.s14_gRows_kill`), and the decay band
  threshold `4096 ≤ (log X_d)^{1−1/500−θ₂₉₃}`;
* IN — `gP1` and the four-slot `GRowsZeroGate'''` at `constPool ρ R.Hhi` (base-FREE on the
  right, and CONST-VERDICT's `constv_gate_base_transfer` makes the gate monotone UPWARD in the
  base, which is the whole difference from the decay pool), `heps293` and `hband4096` — the
  two base-LOWER thresholds `constv_heps293_at_socket`/`constv_hband4096_at_socket` certify at
  every socket base;
* REPLACED — the pool pin `∀ A, epsrf A ≤ 0` becomes §1's threshold
  `14·loglog R.Hhi + log 376266 + log(1/ρ) ≤ (θ₂₉₃ − epsrf X_d)·loglog X_d`.

⟦WHY THE REPLACEMENT IS THE ROAD⟧ the landed twins' pool pin and ⟦B2⟧'s `0 ≤ epsrf` together
force `epsrf ≡ 0`, where `DoorCapBasePerBlock.abs8640` reads `8640 ≤ (log X_d)^0 = 1`.  §1's
threshold releases the pin without touching ⟦B2⟧, so the fire point `epsrf ≡ θ₂₉₃ − 1/500`
— ⟦B2⟧'s own upper endpoint — is now admissible, and `abs8640` becomes honest.

⚠ `heps293` is INERT here (`_heps293`): §1's threshold subsumes it at every `0 ≤ epsrf`, which
⟦B2⟧ supplies.  It is carried so the residue list matches CONST-VERDICT's four certified
`constPool` slots.  Nothing is fired: the compose comes after CAPGATE. -/
theorem logChowla2_capstone_final_const' (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ Ct Cq cs T₀ Kq Ks : ℝ) (x₀ Hcap : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
        ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
          ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
            R.Hlo ≤ max Hcap U1floor ∧
            ∀ (M : ℕ), 1 ≤ M →
              ∃ C' : ℝ, 0 < C' ∧
                ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                  -- ⟦A⟧ THE SPINE ARITHMETIC
                  M4DoorGates Cg R M k δ₀ →
                  8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloor M : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    m4SmallGradeFits (doorRowFloor M)
                      (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ K)) H)
                      (fun H => 2 * rStrWitness H) H) →
                  -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ K)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    GRowsZeroGate''' M (A + s) Cp
                      (constPool (doorRhoOfDelta (s12DeltaSock δ₀ K)) R.Hhi)) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                        + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)))
                      ≤ (theta293 - epsrf (A + s))
                          * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ K)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                      * constPool (doorRhoOfDelta (s12DeltaSock δ₀ K)) R.Hhi) →
                  -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    calQK (Adoor M) (3072 * M) M 2 ≤ A + s ∧
                      Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
                          ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                      ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                  -- ⟦B4 RAW⟧ the crossing bound, carried
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                      (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                      5 ≤ Real.log (Real.log (2 * T)) →
                      (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                          ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                        ≤ 8 * (0 : ℝ) ^ 2
                          + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                \ seamBall (((A + s : ℕ)) : ℝ) 0)
                              ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                  (calP (Adoor M) (3072 * M))
                                  (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                                  (mrAlpha (1 / 12)) 2,
                              ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                          + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                              * (Real.log (((A + s : ℕ)) : ℝ))
                                  ^ (-theta293 + epsrf (A + s)))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ K))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, Hcap, hCg, hε, hK, hδ₀, hroad⟩ := m4_second_road_L2_hloCap
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS
  obtain ⟨x₀, hbandsplit⟩ := m4_fuse_hband_of_bandBase mmuChiRate_holds_gated Aexp hAexp
  refine ⟨Cg, ε, K, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀,
    max Hcap (max arcFloor36 loglogFloor50), hCg, hε, hK, hδ₀, hCt, hCq, hcs, hT₀, hKq,
    hKs, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hM
  obtain ⟨C', hC'pos, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, ?_⟩
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
  set δs : ℝ := s12DeltaSock δ₀ K with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hK
  have hδssq : δs ^ 2 = δ₀ / (16 * K) := s12DeltaSock_sq hδ₀ hK
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorRowZeroBase M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hρpos (fun i m => norm_doorPunctCoeffU_le_one M i m)
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
  refine hR δ₀ (δ₀ / (8 * K))
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
    have hKpos : (0 : ℝ) < 16 * K := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * K) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * K * (δ₀ / (8 * K)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

/-! ## §5 — ⟦PIECE 5⟧ THE TWIN AT THE GRADED BAND WIRE (⟦B5 `grade`⟧ PAID) -/

set_option maxHeartbeats 1000000 in
-- Same cause as §4: the statement re-elaborates the full residue against the re-cut prefix.
/-- **⟦THE CAPSTONE TWIN AT THE GRADED BAND WIRE⟧**
(`logChowla2_capstone_final_const'_graded`).

§4's twin with ONE wire swapped: `S12FuseCompose.m4_fuse_hband_of_bandBase` (UNGRADED) OUT,
`S12FuseCompose.m4_fuse_hband_of_bandBase_graded` (⟦B5-HOIST⟧, §6 there) IN.  Everything else
is §4's, byte for byte: the eleven constants, `x₀` and `Hcap` in the top block, `∀ Cp ≥ 0`, `R`
before `M`, the EDGE-5 payload conjunct `R.Hlo ≤ max Hcap U1floor`, the conclusion
`¬ logChowla2Fails R.eps R.x R.ω`, and ALL SIXTEEN residue binders (⟦A⟧, ⟦B1'⟧ at
`constPool`, ⟦B2⟧'s `epsrf` window, ⟦B3⟧, ⟦B4⟧ RAW, ⟦B5⟧ `DoorBandBase`, ⟦B6⟧).

⟦THE DELTA⟧ exactly two lines:

* the top constant block gains `Mfl : ℕ` with `1 ≤ Mfl` — the EXPLICIT `M`-floor
  `⌈(max 1 (8·Cb))^{5/2}⌉₊ + 1` of `S11HoistGrade.s11_grade_absorption`, read off the graded
  wire's `Aexp`-only constant `Cb`.  The `M`-binder `1 ≤ M` becomes `Mfl ≤ M`; since
  `1 ≤ Mfl`, nothing is lost.  The floor lands in the SELECTION genre, beside
  `S15Compose.S15Sel.x0M`: both are plain `ℕ`-floors on `M` against a constant revealed
  BEFORE `M` is chosen;
* the payload `∃ C' : ℝ, 0 < C' ∧ …` gains the conjunct
  `8·C' ≤ (log 2 · doorRowFloor M)^{s13Aexp − 1/2 + 1/1000}` — `S13BandGate.grade`, now
  DELIVERED rather than assumed.

⟦WHAT THIS BUYS⟧ `grade` is the ONE line of `S13BandGate` the landed twin could not absorb:
`C'` is revealed AFTER `M`, so a consumer that fixes `M` first had to carry it as a naked
hypothesis (or, at `S15Compose.S15Supply`, quantify over EVERY `C' > 0`).  The graded wire's
cap `C' ≤ Cb·M^{2.1}` against the gate's `M^{2.501}` right side closes it with `M^{0.401}` of
headroom, so the consumer pays an ORDINARY `M`-floor instead of an analytic hypothesis.

⚠ Nothing else moves.  `DoorBandBase` remains a hypothesis (⟦B5⟧) and the RAW crossing bound
remains a hypothesis (⟦B4⟧); this file's §4 twin is untouched and still exported. -/
theorem logChowla2_capstone_final_const'_graded (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ Ct Cq cs T₀ Kq Ks : ℝ) (x₀ Hcap Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
        ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
          ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
            R.Hlo ≤ max Hcap U1floor ∧
            ∀ (M : ℕ), Mfl ≤ M →
              ∃ C' : ℝ, 0 < C' ∧
                8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
                    ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                  -- ⟦A⟧ THE SPINE ARITHMETIC
                  M4DoorGates Cg R M k δ₀ →
                  8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloor M : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    m4SmallGradeFits (doorRowFloor M)
                      (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ K)) H)
                      (fun H => 2 * rStrWitness H) H) →
                  -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ K)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    GRowsZeroGate''' M (A + s) Cp
                      (constPool (doorRhoOfDelta (s12DeltaSock δ₀ K)) R.Hhi)) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                        + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)))
                      ≤ (theta293 - epsrf (A + s))
                          * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ K)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                      * constPool (doorRhoOfDelta (s12DeltaSock δ₀ K)) R.Hhi) →
                  -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    calQK (Adoor M) (3072 * M) M 2 ≤ A + s ∧
                      Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
                          ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                      ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                  -- ⟦B4 RAW⟧ the crossing bound, carried
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                      (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                      5 ≤ Real.log (Real.log (2 * T)) →
                      (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                          ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                        ≤ 8 * (0 : ℝ) ^ 2
                          + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                \ seamBall (((A + s : ℕ)) : ℝ) 0)
                              ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                  (calP (Adoor M) (3072 * M))
                                  (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                                  (mrAlpha (1 / 12)) 2,
                              ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                          + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                              * (Real.log (((A + s : ℕ)) : ℝ))
                                  ^ (-theta293 + epsrf (A + s)))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ K))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, Hcap, hCg, hε, hK, hδ₀, hroad⟩ := m4_second_road_L2_hloCap
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS
  obtain ⟨x₀, Cb, hCb, hbandsplit⟩ :=
    m4_fuse_hband_of_bandBase_graded mmuChiRate_holds_gated Aexp hAexp
  obtain ⟨Mfl, hMfl, habs⟩ := s11_grade_absorption Cb hCb
  refine ⟨Cg, ε, K, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀,
    max Hcap (max arcFloor36 loglogFloor50), Mfl, hCg, hε, hK, hδ₀, hCt, hCq, hcs, hT₀,
    hKq, hKs, hMfl, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hMfloor
  have hM : 1 ≤ M := le_trans hMfl hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, habs M hMfloor C' hC'le, ?_⟩
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
  set δs : ℝ := s12DeltaSock δ₀ K with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hK
  have hδssq : δs ^ 2 = δ₀ / (16 * K) := s12DeltaSock_sq hδ₀ hK
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorRowZeroBase M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hρpos (fun i m => norm_doorPunctCoeffU_le_one M i m)
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
  refine hR δ₀ (δ₀ / (8 * K))
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
    have hKpos : (0 : ℝ) < 16 * K := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * K) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * K * (δ₀ / (8 * K)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

/-! ## §GK — the G-lever twin -/

/-- `doorFuseFrame_pool'_of_gates_const_pos (:307)` at the lever. -/
theorem doorFuseFrame_pool'_of_gates_const_pos_gk (K : ℕ) {M Xd j Hhi : ℕ} {Cs Ccc ε ρ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ constPool ρ Hhi)
    (hg : GRowsZeroGate'''_gk K M Xd Ccc (constPool ρ Hhi))
    (hρ : 0 < ρ)
    (hthr : 14 * Real.log (Real.log ((Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
      ≤ (theta293 - ε) * Real.log (Real.log ((Xd : ℕ) : ℝ)))
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
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
  eps_pool := eps_pool_const_pos (s12c_one_le_log_of_three_le hb.X_three) hρ hthr
  band_pool := band_pool_of_threshold
    (by have := s12c_one_le_log_of_three_le hb.X_three; linarith) hband4096

/-! ## §3 — ⟦PIECE 3⟧ THE FUSE AT `constPool`, `0 ≤ C_p`, POSITIVE `ε` -/

/-- `m4_closure_fuse_zero'_const_nonneg (:351)` at the lever. -/
theorem m4_closure_fuse_zero'_const_nonneg_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kc ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 < ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          GRowsZeroGate'''_gk K M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
            ≤ (theta293 - ε (A + s)) * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase_gk K M (A + s) j cU bU) →
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
          DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kc ρ) →
        M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε Kc ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows hthr _heps293 hband4096
    hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_gk K (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := fun _ => constPool ρ R.Hhi)
    (RSbig := fun _ H => RSanDoorRho ρ H) hM ?_
    (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband
    (fun _ => constPool_nonneg hρ.le) (m4_arith_henv_constPool_gk K hρ.le harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_pos_gk K (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) hρ (hthr H L q j A s hb) hM hXd (hband4096 H L q j A s hb)

/-! ## §4 — ⟦PIECE 4⟧ THE CAPSTONE TWIN AT THE CONSTANT POOL -/

set_option maxHeartbeats 1000000 in
-- Same cause as `S12FuseCompose` §4/§5: the statement re-elaborates the full residue against
-- the re-cut prefix.
/-- `logChowla2_capstone_final_const' (:449)` at the lever. -/
theorem logChowla2_capstone_final_const'_gk (K : ℕ) (hK : K ≤ 170000000)
    (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks : ℝ) (x₀ Hcap : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
        ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
          ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
            R.Hlo ≤ max Hcap U1floor ∧
            ∀ (M : ℕ), 1 ≤ M →
              ∃ C' : ℝ, 0 < C' ∧
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
                    DoorBandBase_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Hcap, hCg, hε, hKc, hδ₀, hroad⟩ := m4_second_road_L2_hloCap_gk K
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_gk K hK
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, hbandsplit⟩ := m4_fuse_hband_of_bandBase_gk K mmuChiRate_holds_gated Aexp hAexp
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀,
    max Hcap (max arcFloor36 loglogFloor50), hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq,
    hKs, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hM
  obtain ⟨C', hC'pos, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, ?_⟩
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

/-! ## §5 — ⟦PIECE 5⟧ THE TWIN AT THE GRADED BAND WIRE (⟦B5 `grade`⟧ PAID) -/

set_option maxHeartbeats 1000000 in
-- Same cause as §4: the statement re-elaborates the full residue against the re-cut prefix.
/-- `logChowla2_capstone_final_const'_graded (:691)` at the lever.  THE LAST
K-UNIFORM STATEMENT: no numeral in `K` anywhere below the pin. -/
theorem logChowla2_capstone_final_const'_graded_gk (K : ℕ) (hK : K ≤ 170000000)
    (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks : ℝ) (x₀ Hcap Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
        ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
          ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
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
                    DoorBandBase_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Hcap, hCg, hε, hKc, hδ₀, hroad⟩ := m4_second_road_L2_hloCap_gk K
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_gk K hK
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cb, hCb, hbandsplit⟩ :=
    m4_fuse_hband_of_bandBase_graded_gk K mmuChiRate_holds_gated Aexp hAexp
  obtain ⟨Mfl, hMfl, habs⟩ := s11_grade_absorption Cb hCb
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀,
    max Hcap (max arcFloor36 loglogFloor50), Mfl, hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀,
    hKq, hKs, hMfl, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hMfloor
  have hM : 1 ≤ M := le_trans hMfl hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, habs M hMfloor C' hC'le, ?_⟩
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

/-! ## §GK-PINNED — ⟦REF-REPAIR (b) + THE `Mfl` WIRE⟧ THE GRADED CAPSTONE ON THE **PINNED**
ROAD

⟦WHY⟧ `REF-FINAL-SAT` (flags 2026-07-31) proved the summit terminal VACUOUS as landed: its
`1/2^10 ≤ δ₀` rider is FALSE at the object's own constants (`s13Delta0 ≈ 2^{-19.68}`, 673×
short) and unreachable at ANY admissible `ε`.  The repair is to consume the road that
already CARRIES its constants: `HloExportMR.m4_second_road_L2_hloCap_pinned_gk` (EPSPIN,
landed) delivers three extra conjuncts — `Cg ≤ 2·10^{12}`, `1/500 ≤ ε`, `1/838400 ≤ δ₀` —
which this twin hands up the chain, where they DISCHARGE the `ε`/`δ₀`/`Cg` riders instead of
carrying them.

⟦THE SECOND CHANGE — THE `Mfl` WIRE⟧ §5 (:1217) fires `S11HoistGrade.s11_grade_absorption`,
whose floor throws the gate's own `(4·10^{10})^{2.501}` away.  `SEL-RECUT` restored that
numeral (`s11_grade_absorption'` at `s11GradeFloor`) and the restoration was never wired.
This twin wires it: the exported `Mfl` is `s11GradeFloor Cb`, smaller than §5's by the full
`(4·10^{10})^{2.5·2.501} ≈ 2^{221}`.

⟦WHAT IS **NOT** CLAIMED⟧ `Cb` is the LEVERED band constant
`C·4^{Aexp}·(exp 26.25·(49152·2^K)^{1.05}) + 1` (`S11Hoist.m4_hband_at_door_slot_split_
graded_gk`), so `Mfl` still grows like `2^{2.63K}`; the wire shrinks it, it does not bound it.
See the REF-REPAIR report for the `Mfl`-vs-`K` conflict this exposes.

**PURELY ADDITIVE.**  §5 and every declaration it feeds are untouched. -/

set_option maxHeartbeats 1000000 in
-- Same cause as §5: the statement re-elaborates the full residue against the re-cut prefix.
/-- `logChowla2_capstone_final_const'_graded_gk (:1217)` on the PINNED road, with the grade
absorption at the restored floor.  Statement = §GK's, plus the three EPSPIN conjuncts
`Cg ≤ 2·10^{12}`, `1/500 ≤ ε`, `1/838400 ≤ δ₀` at the END of the `∃`-prefix. -/
theorem logChowla2_capstone_final_const'_graded_gk_pinned (K : ℕ) (hK : K ≤ 170000000)
    (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks : ℝ) (x₀ Hcap Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
        ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
          ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
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
                    DoorBandBase_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Hcap, hCg, hCgle, hε, hKc, hδ₀, hεpin, hδpin, hroad⟩ :=
    m4_second_road_L2_hloCap_pinned_gk K
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_gk K hK
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cb, hCb, hbandsplit⟩ :=
    m4_fuse_hband_of_bandBase_graded_gk K mmuChiRate_holds_gated Aexp hAexp
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀,
    max Hcap (max arcFloor36 loglogFloor50), s11GradeFloor Cb, hCg, hε, hKc, hδ₀, hCt, hCq,
    hcs, hT₀, hKq, hKs, s11GradeFloor_one_le Cb, hCgle, hεpin, hδpin, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hMfloor
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le Cb) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, s11_grade_absorption' Cb M hMfloor C' hC'le, ?_⟩
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

