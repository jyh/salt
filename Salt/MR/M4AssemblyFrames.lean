/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ClosureRepair
import Salt.MR.M4SocketDischarge
import Salt.MR.S13FramesA
import Salt.MR.S13FramesB

/-!
# ⟦THE FRAME INSTANTIATION PAGES, AT THE DECAY POOL⟧ (`M4AssemblyFrames`)

Design provenance: `docs/blueprints/flags.md` 2026-07-30 18:46 ⟦THE CLOSURE EXAMINER RULES⟧,
19:00 ⟦R5-REPAIR⟧, and the Captain's ⟦D2 FREEZE CORRECTION⟧ ruling (the certified working
point `m = 66`, `s13M`, `λ ∈ [74.198, 83.667]` SURVIVES; `MSelect.winFloor`/`.absorb` are
write-only; `abs8640` is a BASE-lower discharged at `SocketBase`'s x-scale).  **THE DECAY POOL
road is the Captain's choice**, so every page below is stated at `M4ClosureRepair.decayPool`.

`M4ClosureRepair` §5 fused ⟦item 11⟧ from the gates alone — `m4_closure_fuse_end'` and
`m4_closure_fuse_zero'`.  This file discharges those fuses' hypothesis binders from the
corpus's landed tables, `M4Assembly.SocketBase` and the regime, one page per binder.

## The binder ledger of `m4_closure_fuse_end'` / `m4_closure_fuse_zero'`

| binder | page | status here |
|---|---|---|
| `hbf` — `DoorBaseFrame (A+s) j` | §2 | **DISCHARGED** from `SocketBase` + the `ρ`-frame |
| `hgP1` — the `𝒯`-leg gate at `decayPool` | §3 | **ABSORBED** to ONE top instance at `3·R.x` |
| `hgRows` — `GRowsZeroGate'''` at `decayPool` | §4 | three slots absorbed, `endpt` DISCHARGED |
| `heps` — `ε ≤ 0` | — | free at the intended `ε := 0` |
| `hL4096` — the corrected band threshold | §5 | **DISCHARGED** from the ARM |
| `hbase` — `DoorRowEndBase`/`DoorRowZeroBase` | §8 | five of the fields DISCHARGED |
| `hcap`, `hband` | — | spine-witnessed; carried (`M4SocketDischarge`'s ledger) |
| `harith` — `DoorArithFrameRho` | §6 | **DISCHARGED** from the `g`-arm + the anchor |

## ⟦THE TWO GENRES, NAMED⟧

Every base-side demand of the decay pool falls into exactly one of two genres, and the file is
organised by them:

* **base UPPER caps** — `gP1` and three of `GRowsZeroGate'''`'s four slots read
  `π₀ = (log X_d)^{−θ₂₉₃}` on the RIGHT, which DECAYS.  These are absorbed exactly as
  `M4SocketDischarge` §5 absorbs the landed `(log X_d)^{−1/500}` cap: the socket's base cap
  `A ≤ 2·R.x` bounds the range (`socketBase_base_le_three_x`), the right-hand side is antitone
  in the base, so the `∀`-binder collapses to its TOP instance at `X_d = 3·R.x`
  (`decayPool_ge_top`).  What survives is ONE finite `M`-side inequality per slot — the
  `Adoor M`-genre demand `M4ArithZero`'s header prices, ⟦REF-SOCKET-2⟧-corrected.
* **base LOWER demands** — `endpt`, `hL4096`, `X_exp`/`X_three`, the window/annulus fields.
  These are met by the ARM's own floor `loglog X_d ≥ 356600`
  (`DoorArithFrameRho.loglogX_ge`), with margins of many orders.  §1 is the stone that turns
  that floor into the usable numeral `log X_d ≥ 10¹⁰`.

⟦THE DECAY-SPECIFIC COST, HONESTLY⟧ against the constant pool (`M4ClosureRepair` §6) the
four upper caps here are `≈ 1.7×` tighter in the log-exponent (`θ₂₉₃ = 0.003413` against
`1/500 = 0.002`) — a constant-factor tightening of the same `Adoor M` demand, on the same
axis, absorbed by the same machinery.  No slot of the decay road jams on the base cap.

## Contents

* §1 the scale stones (`frames_quarter_sq_le_exp`, `frames_logX_ge`, `frames_base_ge`);
* §2 ⟦ITEM (a)⟧ `doorBaseFrame_at_socket` — the six-field base page;
* §3 ⟦ITEM (b)⟧ `decayPool_ge_top`, `gP1_at_socketBase_decay`;
* §4 ⟦ITEM (c)⟧ `endpt_at_decayPool`, `gRowsZeroGate'''_at_socket`;
* §5 ⟦ITEM (d)⟧ `hL4096_of_frame`;
* §6 ⟦ITEM (e)⟧ `doorArithFrameRho_at_socket` / `doorArithFrameRho_family`;
* §7 ⟦ITEM (f)⟧ the `E_ge` line threaded: `gArmEge`, `ege_line_at_socket`,
  `ege_line_of_capGatePerBlock`;
* §8 ⟦ITEM (g)⟧ `doorRowZeroBase_at_socket`/`_family`, `doorRowEndBase_at_socket`/`_family`;
* §9 the composite: `m4_closure_fuse_end'_at_socket` / `m4_closure_fuse_zero'_at_socket`.

⟦PURELY ADDITIVE⟧ no landed declaration is touched; every statement below is new.
-/

set_option maxRecDepth 40000

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE SCALE STONES

The ARM gives `loglog X_d ≥ 356600`; every base-LOWER demand below is met through the single
numeral `log X_d ≥ 10¹⁰` this section extracts from it. -/

/-- `t²/4 ≤ e^t` at `t ≥ 0` — the one convexity step that turns a `loglog` floor into a `log`
floor without leaving `linarith`'s reach.  (`e^t = (e^{t/2})² ≥ (1 + t/2)² ≥ t²/4`.) -/
theorem frames_quarter_sq_le_exp {t : ℝ} (ht : 0 ≤ t) : t ^ 2 / 4 ≤ Real.exp t := by
  have h := Real.add_one_le_exp (t / 2)
  have hsplit : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hpos : (0 : ℝ) < Real.exp (t / 2) := Real.exp_pos _
  rw [hsplit]
  nlinarith [h, hpos, ht]

/-- `t ≤ e^t` — the shadow of the same step, used for `loglog X ≤ log X`. -/
theorem frames_le_exp (t : ℝ) : t ≤ Real.exp t := by
  have := Real.add_one_le_exp t; linarith

/-- **⟦THE ARM'S FLOOR AS A `log`-NUMERAL⟧** (`frames_logX_ge`) — `DoorArithFrameRho`'s own
`loglogX_ge` (`356600 ≤ loglog X`) gives `log X ≥ 10¹⁰`, with `3.17×` to spare
(`356600²/4 = 3.179·10¹⁰`).  Every base-LOWER demand of the decay road is met at this
numeral. -/
theorem frames_logX_ge {M H j : ℕ} {X C₁ M₀ K ρ : ℝ}
    (hfr : DoorArithFrameRho M H j X C₁ M₀ K ρ) : (10 : ℝ) ^ 10 ≤ Real.log X := by
  have hmu : (356600 : ℝ) ≤ Real.log (Real.log X) := hfr.loglogX_ge
  have hL1 : (1 : ℝ) < Real.log X := hfr.one_lt_logX
  have hstep : Real.exp (356600 : ℝ) ≤ Real.log X := by
    have := Real.exp_le_exp.mpr hmu
    rwa [Real.exp_log (by linarith : (0 : ℝ) < Real.log X)] at this
  have hq : (356600 : ℝ) ^ 2 / 4 ≤ Real.exp (356600 : ℝ) :=
    frames_quarter_sq_le_exp (by norm_num)
  have : (10 : ℝ) ^ 10 ≤ (356600 : ℝ) ^ 2 / 4 := by norm_num
  linarith

/-- **⟦THE BASE ITSELF IS HUGE⟧** (`frames_base_ge`) — at a POSITIVE natural base the `log`
floor lifts to the base: `X = e^{log X} ≥ 1 + log X`. -/
theorem frames_base_ge {Xd : ℕ} (hpos : 0 < Xd) {c : ℝ} (h : c ≤ Real.log ((Xd : ℕ) : ℝ)) :
    1 + c ≤ ((Xd : ℕ) : ℝ) := by
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := by exact_mod_cast hpos
  have := Real.add_one_le_exp (Real.log ((Xd : ℕ) : ℝ))
  rw [Real.exp_log hX0] at this
  linarith

/-- `0 ≤ θ₂₉₃` — the exponent's sign, needed for every antitone step below. -/
theorem frames_theta293_nonneg : (0 : ℝ) ≤ theta293 :=
  le_of_lt theta293_pos_le_one.1

/-- `θ₂₉₃ ≤ 1/100`: `θ₂₉₃ = 1/(32(3e+1)) ≤ 1/(32·9.15)`. -/
theorem frames_theta293_le : theta293 ≤ 1 / 100 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hden : (0 : ℝ) < 32 * (3 * Real.exp 1 + 1) := by nlinarith
  have hval : theta293 = 1 / (32 * (3 * Real.exp 1 + 1)) := rfl
  have h100 : (100 : ℝ) ≤ 32 * (3 * Real.exp 1 + 1) := by nlinarith
  rw [hval]
  exact one_div_le_one_div_of_le (by norm_num) h100

/-! ## §2 — ⟦ITEM (a)⟧ THE `DoorBaseFrame` PAGE

The six grade-blind fields of `M4ArithPrime.DoorBaseFrame`, discharged at every base the
socket reaches from `SocketBase` and the `ρ`-frame at that base.  Nothing else is used: no
`M`-side numeral, no register cap.

⟦THE ARITHMETIC, IN ONE LINE PER FIELD⟧

| field | source | margin |
|---|---|---|
| `X_exp`, `X_three` | `log X_d ≥ 10¹⁰` (§1) | `X_d ≥ 10¹⁰` |
| `h_four` | the `ρ`-frame's `jfloor` (`j ≥ 21·50 + 28 = 1078`) | `2^{1078}` vs `4` |
| `h_window` | `2^j ≤ H` and `log X_d ≥ e·log H` | `0.57·log X_d` vs `log X_d` |
| `tann` | the same, plus `30√L ≤ L/2` at `L ≥ 3600` | `0.87·L` vs `L` |
| `ceil5` | the same, plus `e⁵ ≤ 1000` | `6.3·10⁹` vs `148.4` |

The `H`-versus-`X_d` step is the ARM's own `loglog X_d ≥ 7000·loglog H + 6600`, spent at its
WEAKEST reading `loglog X_d ≥ loglog H + 1`, i.e. `log X_d ≥ e·log H`. -/

/-- **⟦ITEM (a) — THE SIX-FIELD BASE PAGE, AT THE SOCKET⟧** (`doorBaseFrame_at_socket`).
`M4ArithPrime.DoorBaseFrame (A+s) j` from `SocketBase` and `DoorArithFrameRho` at that base.

This is the `hbf` binder of `M4ClosureRepair.m4_closure_fuse_end'` /
`m4_closure_fuse_zero'`, per base; §9 threads the family form. -/
theorem doorBaseFrame_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ} {C₁ M₀ K ρ : ℝ}
    (hb : SocketBase R M H L q j A s)
    (hfr : DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) C₁ M₀ K ρ) :
    DoorBaseFrame (A + s) j := by
  obtain ⟨hlo, hhi, hLH, hqp, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  have hAs : 0 < A + s := by omega
  have hX0 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hLX : (10 : ℝ) ^ 10 ≤ Real.log (((A + s : ℕ)) : ℝ) := frames_logX_ge hfr
  have hLXn : (10000000000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    le_trans (by norm_num) hLX
  have hLX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  -- ⟦the `H`-side scales⟧
  have hH1 : (1 : ℝ) < Real.log (H : ℝ) := hfr.one_lt_logH
  have hH0 : (0 : ℝ) < Real.log (H : ℝ) := by linarith
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    rcases lt_or_ge 0 (H : ℝ) with h | h
    · exact h
    · exfalso
      have hz : (H : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg H)
      rw [hz, Real.log_zero] at hH1; linarith
  have hlam : (50 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := hfr.Hfloor
  have hlr : (0 : ℝ) ≤ Real.log (1 / ρ) := hfr.logInvRho_nonneg
  -- ⟦the window index⟧
  have hjR : (1078 : ℝ) ≤ (j : ℝ) := by have := hfr.jfloor; linarith
  have hjN : 1078 ≤ j := by exact_mod_cast hjR
  have hLne : L ≠ 0 := by
    rintro rfl
    rw [Nat.log_zero_right] at hjL
    omega
  have h2jH : 2 ^ j ≤ H :=
    le_trans (le_trans (Nat.pow_le_pow_right (by norm_num) hjL)
      (Nat.pow_log_le_self 2 hLne)) hLH
  have h2jHR : ((2 ^ j : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h2jH
  have h2jpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  -- ⟦the ARM, at its weakest reading: `log X_d ≥ e·log H`⟧
  have hstep : Real.log (Real.log (H : ℝ)) + 1 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
    have := hfr.armWeak; linarith
  have hEH : Real.log (H : ℝ) * Real.exp 1 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h1 := Real.exp_le_exp.mpr hstep
    rwa [Real.exp_add, Real.exp_log hH0, Real.exp_log hLX0] at h1
  have hHX : 2.7 * Real.log (H : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have he27 : (2.7 : ℝ) < Real.exp 1 := exp_one_gt_27
    nlinarith [hEH, he27, hH0]
  have hllX : Real.log (Real.log (((A + s : ℕ)) : ℝ)) ≤ Real.log (((A + s : ℕ)) : ℝ) - 1 := by
    have := Real.add_one_le_exp (Real.log (Real.log (((A + s : ℕ)) : ℝ)))
    rw [Real.exp_log hLX0] at this; linarith
  -- ⟦the shared lower bound on the annulus height `2·X_d/2^j`⟧
  have hXH : Real.exp (Real.log (((A + s : ℕ)) : ℝ) - Real.log (H : ℝ))
      = (((A + s : ℕ)) : ℝ) / (H : ℝ) := by
    rw [Real.exp_sub, Real.exp_log hX0, Real.exp_log hHpos]
  have hdiv : (((A + s : ℕ)) : ℝ) / (H : ℝ)
      ≤ 2 * ((((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ)) := by
    have hd : (((A + s : ℕ)) : ℝ) / (H : ℝ)
        ≤ (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) := by gcongr
    have hpos : (0 : ℝ) ≤ (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) := by positivity
    linarith
  have hann : Real.exp (Real.log (((A + s : ℕ)) : ℝ) - Real.log (H : ℝ))
      ≤ 2 * ((((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ)) := by rw [hXH]; exact hdiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ⟦`X_exp`⟧
    have h := Real.exp_le_exp.mpr (by linarith : (1 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ))
    rwa [Real.exp_log hX0] at h
  · -- ⟦`X_three`⟧
    have h := frames_base_ge hAs hLX
    have h3 : (3 : ℝ) ≤ 1 + (10 : ℝ) ^ 10 := by norm_num
    linarith
  · -- ⟦`h_four`⟧
    have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hR : ((2 ^ 2 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast h4
    simpa using hR
  · -- ⟦`h_window`⟧
    have hprod : (((A + s : ℕ)) : ℝ) * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-(1 / 5 : ℝ))
        = Real.exp (Real.log (((A + s : ℕ)) : ℝ)
            + Real.log (Real.log (((A + s : ℕ)) : ℝ)) * (-(1 / 5 : ℝ))) := by
      rw [Real.rpow_def_of_pos hLX0, Real.exp_add, Real.exp_log hX0]
    rw [hprod]
    calc ((2 ^ j : ℕ) : ℝ) ≤ (H : ℝ) := h2jHR
      _ = Real.exp (Real.log (H : ℝ)) := (Real.exp_log hHpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · -- ⟦`tann`⟧
    rw [TannGate]
    have hsq : Real.sqrt (Real.log (((A + s : ℕ)) : ℝ))
        ≤ Real.log (((A + s : ℕ)) : ℝ) / 60 := by
      have hnn : (0 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) / 60 := by positivity
      have hle : Real.log (((A + s : ℕ)) : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ) / 60) ^ 2 := by
        nlinarith [hLXn, hLX0]
      calc Real.sqrt (Real.log (((A + s : ℕ)) : ℝ))
          ≤ Real.sqrt ((Real.log (((A + s : ℕ)) : ℝ) / 60) ^ 2) := Real.sqrt_le_sqrt hle
        _ = Real.log (((A + s : ℕ)) : ℝ) / 60 := Real.sqrt_sq hnn
    rw [← Real.sqrt_eq_rpow]
    refine le_trans (Real.exp_le_exp.mpr ?_) hann
    linarith
  · -- ⟦`ceil5`⟧
    have he5 : Real.exp 5 ≤ 1000 := by
      have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have hh : Real.exp 5 = (Real.exp 1) ^ (5 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      rw [hh]
      have hc : (Real.exp 1) ^ (5 : ℕ) ≤ (2.7182818286 : ℝ) ^ (5 : ℕ) :=
        pow_le_pow_left₀ hpos.le he.le 5
      have hn : (2.7182818286 : ℝ) ^ (5 : ℕ) ≤ 1000 := by norm_num
      linarith
    have hlog : Real.exp 5
        ≤ Real.log (2 * ((((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ))) := by
      have h1 : Real.log (((A + s : ℕ)) : ℝ) - Real.log (H : ℝ)
          ≤ Real.log (2 * ((((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ))) := by
        have h2 := Real.log_le_log (Real.exp_pos _) hann
        rwa [Real.log_exp] at h2
      linarith
    have := Real.log_le_log (Real.exp_pos 5) hlog
    rwa [Real.log_exp] at this

/-! ## §3 — ⟦ITEM (b)⟧ THE `𝒯`-LEG GATE AT THE DECAY POOL

`M4SocketDischarge` §5's absorption, re-run at the decay exponent.  `decayPool X_d =
(log X_d)^{−θ₂₉₃}` is ANTITONE in the base exactly as the landed `(log X_d)^{−1/500}` is, so
the socket's base cap `A ≤ 2·R.x` collapses the `∀`-binder to its TOP instance at
`X_d = 3·R.x`. -/

/-- **⟦THE DECAY POOL AT THE TOP OF THE CAPPED RANGE⟧** (`decayPool_ge_top`) — the pool's
value at `X_d = 3·R.x` is a LOWER bound for its value at every base the socket reaches.  So
any cap met at the top is met everywhere: the `∀` is one inequality.

This is the decay road's whole answer to ⟦THE FINDING⟧ R5-REPAIR banked (the decay pool
re-introduces base UPPER caps): they are absorbed by the same (α) base-cap machinery the
landed `1/500` caps use, at a `1.7×` tighter exponent. -/
theorem decayPool_ge_top {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBase R M H L q j A s) (hX1 : (1 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ)) :
    Real.log (3 * (R.x : ℝ)) ^ (-theta293) ≤ decayPool (A + s) := by
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hX0 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by
    have : 0 < A + s := by omega
    exact_mod_cast this
  rw [decayPool_def]
  exact Real.rpow_le_rpow_of_nonpos (by linarith)
    (Real.log_le_log hX0 (socketBase_base_le_three_x hb))
    (neg_nonpos.mpr frames_theta293_nonneg)

/-- **⟦ITEM (b) — `gP1` AT THE DECAY POOL, ABSORBED⟧** (`gP1_at_socketBase_decay`) — the
`hgP1` binder of `M4ClosureRepair.m4_closure_fuse_end'`/`_zero'` at ONE base, from the single
top instance.  The surviving obligation is the `M`-side numeral

  `loglog(3·R.x)·θ₂₉₃ + log(374784·C_t·e³) ≤ (log 2)·Adoor M` ,

`M4SocketDischarge`'s ⟦THE ARITHMETIC OF THAT ONE INEQUALITY⟧ with `1/500 ↦ θ₂₉₃`. -/
theorem gP1_at_socketBase_decay {R : ChowlaRegime} {M H L q j A s : ℕ} {Cs : ℝ}
    (hb : SocketBase R M H L q j A s) (hX1 : (1 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ))
    (htop : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ Real.log (3 * (R.x : ℝ)) ^ (-theta293)) :
    374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ decayPool (A + s) :=
  le_trans htop (decayPool_ge_top hb hX1)

/-! ## §4 — ⟦ITEM (c)⟧ `GRowsZeroGate'''` AT THE DECAY POOL

Four slots.  `level1`, `p2` and `dens` are base UPPER caps and go through §3's top instance;
`endpt` reads the base on BOTH sides (`1/X_d` against `(log X_d)^{−θ₂₉₃}/4`) and is a
base-LOWER demand, discharged outright from the ARM's floor. -/

/-- **⟦THE `endpt` SLOT, DISCHARGED⟧** (`endpt_at_decayPool`) — `5760·(2e+2)/X_d ≤ π₀/4` at
`π₀ = (log X_d)^{−θ₂₉₃}`.  The demand is `23040·(2e+2)·(log X_d)^{θ₂₉₃} ≤ X_d`; since
`(log X_d)^{θ₂₉₃} ≤ log X_d` and `X_d ≥ (log X_d)²/4`, it holds as soon as
`log X_d ≥ 685672` — met by the ARM's `log X_d ≥ 10¹⁰` with four orders to spare.

⟦THE READING⟧ this is the ONE slot of the decay road whose two sides both move with the base,
and it moves the RIGHT way: the left decays like `1/X_d`, the right only like
`(log X_d)^{−θ₂₉₃}`. -/
theorem endpt_at_decayPool {Xd : ℕ} (hpos : 0 < Xd)
    (hL : (10000000000 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ)) :
    5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ)) ≤ 1 / 4 * decayPool Xd := by
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := by exact_mod_cast hpos
  have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hXge : (Real.log ((Xd : ℕ) : ℝ)) ^ 2 / 4 ≤ ((Xd : ℕ) : ℝ) := by
    have h := frames_quarter_sq_le_exp hL0.le
    rwa [Real.exp_log hX0] at h
  have hpowpos : (0 : ℝ) < (Real.log ((Xd : ℕ) : ℝ)) ^ theta293 :=
    Real.rpow_pos_of_pos hL0 _
  have hpow : (Real.log ((Xd : ℕ) : ℝ)) ^ theta293 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by linarith
    have h2 := Real.rpow_le_rpow_of_exponent_le h1
      (le_trans frames_theta293_le (by norm_num) : theta293 ≤ (1 : ℝ))
    rwa [Real.rpow_one] at h2
  have hinv : decayPool Xd = ((Real.log ((Xd : ℕ) : ℝ)) ^ theta293)⁻¹ := by
    rw [decayPool_def, Real.rpow_neg hL0.le]
  have he2 : 2 * Real.exp 1 + 2 ≤ 7.44 := by have := Real.exp_one_lt_d9; linarith
  have hLsq : 2742688 * Real.log ((Xd : ℕ) : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ 2 := by
    nlinarith [hL, hL0]
  have hA1 : 5760 * (2 * Real.exp 1 + 2) * (4 * (Real.log ((Xd : ℕ) : ℝ)) ^ theta293)
      ≤ 171418 * (Real.log ((Xd : ℕ) : ℝ)) ^ theta293 := by nlinarith [he2, hpowpos]
  have hA2 : 171418 * (Real.log ((Xd : ℕ) : ℝ)) ^ theta293
      ≤ 171418 * Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hA3 : 171418 * Real.log ((Xd : ℕ) : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ 2 / 4 := by
    linarith
  have hkey : 5760 * (2 * Real.exp 1 + 2) * (4 * (Real.log ((Xd : ℕ) : ℝ)) ^ theta293)
      ≤ ((Xd : ℕ) : ℝ) := le_trans (le_trans hA1 hA2) (le_trans hA3 hXge)
  rw [hinv, show 5760 * ((2 * Real.exp 1 + 2) / ((Xd : ℕ) : ℝ))
      = (5760 * (2 * Real.exp 1 + 2)) / ((Xd : ℕ) : ℝ) by ring,
    show (1 : ℝ) / 4 * ((Real.log ((Xd : ℕ) : ℝ)) ^ theta293)⁻¹
      = 1 / (4 * (Real.log ((Xd : ℕ) : ℝ)) ^ theta293) by field_simp,
    div_le_div_iff₀ hX0 (by positivity)]
  linarith

/-- **⟦ITEM (c) — THE FOUR-SLOT GATE AT THE DECAY POOL⟧** (`gRowsZeroGate'''_at_socket`) —
the `hgRows` binder at ONE base.  Three top instances (`level1`, `p2`, `dens` — the `M`-side
`Adoor M` demands, ⟦REF-SOCKET-2⟧'s genre) plus the discharged `endpt`. -/
theorem gRowsZeroGate'''_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ} {Ccc : ℝ}
    (hb : SocketBase R M H L q j A s)
    (hL : (10000000000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ))
    (hlvl : 14400 * Real.exp 1 ^ 2 * a2Level1 M
      ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293))
    (hp2 : 138240 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
          + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ))
      ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293))
    (hdens : 5760 * Ccc * (2 / (M : ℝ))
      ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293)) :
    GRowsZeroGate''' M (A + s) Ccc (decayPool (A + s)) := by
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hAs : 0 < A + s := by omega
  have htop := decayPool_ge_top hb (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith
  · exact endpt_at_decayPool hAs hL
  · linarith
  · linarith

/-! ## §5 — ⟦ITEM (d)⟧ THE CORRECTED `4096`-THRESHOLD

`hL4096 : 4096 ≤ (log X_d)^{1−1/500−θ₂₉₃}`.  The exponent is POSITIVE (`≥ 0.9945`), so this
is a base-LOWER demand: taking logs it reads `12·log 2 ≤ (1−1/500−θ₂₉₃)·loglog X_d`, i.e.
`loglog X_d ≥ 8.37`.  The ARM delivers `356600`.  ⟦THE DIRECTION IS AS HOPED⟧ — the examiner's
corrected exponent does not flip the demand's sign. -/

/-- **⟦ITEM (d) — THE BAND THRESHOLD, DISCHARGED FROM THE ARM⟧** (`hL4096_of_frame`).  The
margin is `356600` against the `8.37` needed: `4.3·10⁴×` in the `loglog` scale. -/
theorem hL4096_of_frame {M H j : ℕ} {X C₁ M₀ K ρ : ℝ}
    (hfr : DoorArithFrameRho M H j X C₁ M₀ K ρ) :
    (4096 : ℝ) ≤ (Real.log X) ^ (1 - (1 : ℝ) / 500 - theta293) := by
  have hL1 : (1 : ℝ) < Real.log X := hfr.one_lt_logX
  have hmu : (356600 : ℝ) ≤ Real.log (Real.log X) := hfr.loglogX_ge
  have hθ : theta293 ≤ 1 / 100 := frames_theta293_le
  have hθ0 : (0 : ℝ) ≤ theta293 := frames_theta293_nonneg
  have ha : (98 : ℝ) / 100 ≤ 1 - (1 : ℝ) / 500 - theta293 := by linarith
  have hrw : (Real.log X) ^ (1 - (1 : ℝ) / 500 - theta293)
      = Real.exp (Real.log (Real.log X) * (1 - (1 : ℝ) / 500 - theta293)) :=
    Real.rpow_def_of_pos (by linarith) _
  have h9 : (4096 : ℝ) ≤ Real.exp 9 := by
    have h := pow_27_le_exp 9
    norm_num at h
    linarith
  have hmul : (356600 : ℝ) * (98 / 100)
      ≤ Real.log (Real.log X) * (1 - (1 : ℝ) / 500 - theta293) :=
    mul_le_mul hmu ha (by norm_num) (by linarith)
  rw [hrw]
  exact le_trans h9 (Real.exp_le_exp.mpr (by linarith))

/-! ## §6 — ⟦ITEM (e)⟧ THE `ρ`-FRAME AT THE SOCKET

`M4ArithRho` §7 minted every field supplier of `DoorArithFrameRho`; this section assembles
them at ONE socket base.  Nothing new is proved about the register — the `g`-arm floor, the
⟦C1⟧ anchor and the `M₀` window's readable endpoint are the landed objects, consumed. -/

/-- **⟦ITEM (e) — THE THIRTEEN-FIELD `ρ`-FRAME, AT ONE SOCKET BASE⟧**
(`doorArithFrameRho_at_socket`).  The `harith` binder of `M4ClosureRepair`'s fuses, per base.

⟦THE SUPPLIERS, FIELD BY FIELD⟧ `Mpos`/`Knonneg`/`rho_pos`/`rho_le_one`/`C1_nonneg` are the
carried scalars; `logX_nonneg` is free at a natural base; `logH_nonneg`/`Hfloor` are the
register's own `H`-floor; `arm` is `m4_arith_arm_of_gArmRho` at `A` shifted to `A+s` by
`m4_arith_arm_of_shift`; `anchor` is `m4_arith_anchor_of_C1_rho`; `M0_window` is
`m4_arith_M0_window_lower_rho` at its readable endpoint; `jfloor` is
`m4_arith_jfloor_of_anchor_rho` off the socket's own door floor `doorRowFloor M ≤ j`.

⟦THE ONE REGISTER DEMAND⟧ `hg : gArmDoorRho x₀ K ω ρ H ≤ R.x` — the `∀g ∃R` mechanism of
`m4_exit_socket_split`, where `g` is chosen BEFORE `R`.  It is the only place the register
enters, and it is where the `399`-in-`1.25·10⁵` clearance of ⟦ASSEMBLY-ARITH⟧ is spent. -/
theorem doorArithFrameRho_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ}
    {C₁ M₀ : ℕ → ℝ} {x₀ K ρ : ℝ}
    (hM : 1 ≤ M) (hK : 0 ≤ K) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hanchor : 2484 ≤ Nat.log 2 M + 1)
    (hHcap : Real.log (Real.log (H : ℝ)) ≤ 10 ^ 11)
    (hρcap : Real.log (1 / ρ) ≤ 10 ^ 11)
    (hHreg : 0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho x₀ K (R.ω : ℝ) ρ H ≤ (R.x : ℝ))
    (hC1 : 0 ≤ C₁ (A + s))
    (hM0 : 0.062 * Real.log (Real.log (((A + s : ℕ)) : ℝ))
        + 40 * Real.log (Real.log (H : ℝ)) + 6 * Real.log (C₁ (A + s) + 1)
        + 3 * Real.log (1 / ρ) + 33 ≤ M₀ (A + s))
    (hb : SocketBase R M H L q j A s) :
    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ := by
  obtain ⟨hlo, hhi, hLH, hqp, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  have hω : (0 : ℝ) < (R.ω : ℝ) := by
    have := R.hω
    have : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
    linarith
  have hlrho : (0 : ℝ) ≤ Real.log (1 / ρ) := log_one_div_nonneg hρ0 hρ1
  have harmA := m4_arith_arm_of_gArmRho hω hHreg.1 hHreg.2 hg hAx
  have hmuA : (356600 : ℝ) ≤ Real.log (Real.log (A : ℝ)) := by
    have := hHreg.2; linarith
  have hlogA : (1 : ℝ) < Real.log (A : ℝ) :=
    one_lt_log_of_loglog_ge (log_natCast_nonneg' A) (by norm_num) hmuA
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have harm := m4_arith_arm_of_shift hApos (by linarith) hAX harmA
  have hmu : (0 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
    have := hHreg.2; linarith
  exact
    { Mpos := hM
      logX_nonneg := log_natCast_nonneg' (A + s)
      logH_nonneg := hHreg.1
      Hfloor := hHreg.2
      Knonneg := hK
      rho_pos := hρ0
      rho_le_one := hρ1
      arm := harm
      anchor := m4_arith_anchor_of_C1_rho hanchor hHcap hρcap
      C1_nonneg := hC1
      M0_window := m4_arith_M0_window_lower_rho (by linarith [hHreg.2]) hmu
        (Real.log_nonneg (by linarith)) hlrho hM0
      jfloor := m4_arith_jfloor_of_anchor_rho hanchor hjfl hHcap hρcap }

/-- **⟦THE `ρ`-FRAME AS THE FUSE'S FAMILY BINDER⟧** (`doorArithFrameRho_family`) — the same,
quantified exactly as `M4ClosureRepair`'s `harith` demands. -/
theorem doorArithFrameRho_family {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {x₀ K ρ : ℝ}
    (hM : 1 ≤ M) (hK : 0 ≤ K) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hanchor : 2484 ≤ Nat.log 2 M + 1)
    (hρcap : Real.log (1 / ρ) ≤ 10 ^ 11)
    (hHcap : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.log (Real.log (H : ℝ)) ≤ 10 ^ 11)
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → gArmDoorRho x₀ K (R.ω : ℝ) ρ H ≤ (R.x : ℝ))
    (hC1 : ∀ n : ℕ, 0 ≤ C₁ n)
    (hM0 : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      0.062 * Real.log (Real.log (((A + s : ℕ)) : ℝ))
        + 40 * Real.log (Real.log (H : ℝ)) + 6 * Real.log (C₁ (A + s) + 1)
        + 3 * Real.log (1 / ρ) + 33 ≤ M₀ (A + s)) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ := by
  intro H L q j A s hb
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  exact doorArithFrameRho_at_socket hM hK hρ0 hρ1 hanchor (hHcap H hlo hhi) hρcap
    (hHreg H hlo hhi) (hg H hlo hhi) (hC1 (A + s)) (hM0 H L q j A s hb) hb

/-! ## §7 — ⟦ITEM (f)⟧ THE `E_ge` LINE, THREADED

`M4ClosureRepair` §4 minted the line in both directions: `ege_line_gate` shows the cap
bundle's own two fields (`EP2_gate` and `phi_row`) FORCE `49920·φ(q) ≤ (log X_d)^{εr}`, and
`ege_line_of_loglog` shows a `loglog X_d ≥ 8500·loglog H + 7800` floor SUPPLIES it at
`εr := θ₂₉₃ − 1/500`.  This section wires both ends to the socket.

⟦THE HONEST FENCE⟧ the demand `8500·λ` is `1.21×` the frozen `DoorArithFrameRho.arm`'s
`7000·λ`, so it does **not** follow from the `ρ`-frame.  It rides where the frame's own arm
rides — on the register's `g`-floor, which is chosen BEFORE `R` — and `gArmEge` below is that
floor, written.  No frozen field is touched. -/

/-- **⟦THE `E_ge` ARM, WRITTEN⟧** (`gArmEge x₀ ω H`) — the `g`-floor at the `E_ge` line's own
coefficient pair:

  `g H ω = max x₀ (16·ω·(log H)¹²·exp(exp(8500·loglog H + 7800)))` .

`M4ArithRho.gArmDoorRho`'s shape at `(8500, 7800)` in place of `(7000, 500·log(1/ρ) + 6600 +
36K)`.  A consumer that wants both takes the `max` of the two `g`'s — both are chosen before
the register. -/
def gArmEge (x₀ ω : ℝ) (H : ℕ) : ℝ :=
  max x₀ (16 * ω * arcDen 12 H
    * Real.exp (Real.exp (8500 * Real.log (Real.log (H : ℝ)) + 7800)))

/-- **⟦THE `E_ge` ARM, DERIVED FROM ITS `g`-FLOOR⟧** (`ege_arm_of_gArmEge`) —
`m4_arith_arm_of_gArmRho`'s argument at the `E_ge` coefficients. -/
theorem ege_arm_of_gArmEge {x₀ ω x : ℝ} {H A : ℕ}
    (hω : 0 < ω) (hL0 : 0 ≤ Real.log (H : ℝ))
    (hlam : 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmEge x₀ ω H ≤ x)
    (hsock : x ≤ 16 * ω * arcDen 12 H * (A : ℝ)) :
    8500 * Real.log (Real.log (H : ℝ)) + 7800 ≤ Real.log (Real.log (A : ℝ)) := by
  have hL1 : 1 < Real.log (H : ℝ) := one_lt_log_of_loglog_ge hL0 (by norm_num) hlam
  have harc : (0 : ℝ) < arcDen 12 H := by
    rw [arcDen]; exact Real.rpow_pos_of_pos (by linarith) _
  have hpre : (0 : ℝ) < 16 * ω * arcDen 12 H := by positivity
  set E : ℝ := 8500 * Real.log (Real.log (H : ℝ)) + 7800 with hE
  have h2 : 16 * ω * arcDen 12 H * Real.exp (Real.exp E) ≤ x :=
    le_trans (le_max_right _ _) hg
  have hAle : Real.exp (Real.exp E) ≤ (A : ℝ) := by
    have := le_trans h2 hsock
    exact le_of_mul_le_mul_left (by linarith [this]) hpre
  have hApos : (0 : ℝ) < (A : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hAle
  have hlogA : Real.exp E ≤ Real.log (A : ℝ) := by
    have := Real.log_le_log (Real.exp_pos (Real.exp E)) hAle
    rwa [Real.log_exp] at this
  have := Real.log_le_log (Real.exp_pos E) hlogA
  rwa [Real.log_exp] at this

/-- **⟦ITEM (f) — THE `E_ge` LINE, SUPPLIED AT THE SOCKET⟧** (`ege_line_at_socket`) — the
line at `εr := θ₂₉₃ − 1/500`, from the `E_ge` `g`-floor and `SocketBase`'s OWN modulus field
`q ≤ arcDen 12 H` (the `H`-side ledger the examiner named as the `φ(q)` row's honest home).

Nothing base-side is asked: `q_arcDen` is `SocketBase` field 5, verbatim. -/
theorem ege_line_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ} {x₀ : ℝ}
    (hb : SocketBase R M H L q j A s)
    (hHreg : 0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmEge x₀ (R.ω : ℝ) H ≤ (R.x : ℝ)) :
    49920 * (q.totient : ℝ)
      ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (theta293 - 1 / 500) := by
  obtain ⟨hlo, hhi, hLH, hqp, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  have hω : (0 : ℝ) < (R.ω : ℝ) := by
    have : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
    linarith
  have harmA := ege_arm_of_gArmEge hω hHreg.1 hHreg.2 hg hAx
  have hmuA : (7800 : ℝ) ≤ Real.log (Real.log (A : ℝ)) := by
    have := hHreg.2; linarith
  have hlogA : (1 : ℝ) < Real.log (A : ℝ) :=
    one_lt_log_of_loglog_ge (log_natCast_nonneg' A) (by norm_num) hmuA
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have harm := m4_arith_arm_of_shift hApos (by linarith) hAX harmA
  have hmu : (7800 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
    have := hHreg.2; linarith
  have hLNd : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) :=
    one_lt_log_of_loglog_ge (log_natCast_nonneg' (A + s)) (by norm_num) hmu
  have hH0 : (0 : ℝ) < Real.log (H : ℝ) := by
    have := one_lt_log_of_loglog_ge hHreg.1 (by norm_num : (0 : ℝ) < 50) hHreg.2
    linarith
  exact ege_line_of_loglog hH0 (by linarith [hHreg.2]) (by linarith) hqQ harm

/-- **⟦THE OTHER END: THE CAP BUNDLE FORCES THE SAME LINE⟧**
(`ege_line_of_capGatePerBlock`) — `S13FramesB.S13CapGatePerBlock`'s `EP2_gate` and `phi_row`
fields, read through `M4ClosureRepair.ege_line_gate`.  So `ege_line_at_socket` is not an extra
demand invented here: it is exactly what the landed per-block cap bundle already asks, at the
`εr` the bundle carries. -/
theorem ege_line_of_capGatePerBlock {Cq cs T₀ Kq Ks C : ℝ} {M Nd q P Q Hreg : ℕ}
    {Tann Rrad Rbd CR EP2 epsr : ℝ}
    (hg : S13CapGatePerBlock Cq cs T₀ Kq Ks C M Nd q P Q Hreg Tann Rrad Rbd CR EP2 epsr) :
    49920 * (q.totient : ℝ) ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ epsr :=
  ege_line_gate (by have := hg.logX_eight; linarith) hg.EP2_gate hg.phi_row

/-! ## §8 — ⟦ITEM (g)⟧ THE TWO PER-BASE ROW BUNDLES

`M4RowsChiEnd.DoorRowEndBase` (seven fields) and `M4RowsChiZero.DoorRowZeroBase` (six).
`S13FramesA.s13_doorRowZeroBase_five` already discharges FIVE of them — `Q2_le`, `reg`, `big`,
`h_four`, `Q1_le_h` — from the door's block-scale floor `s13BlockFloor M ≤ X_d` and the
socket's own `doorRowFloor M ≤ j`.  This section reads that discharge into the two bundles.

⟦WHAT IS NOT DISCHARGED, AND WHY⟧

* `coefWS` — ⟦THE STRICT RELATIVIZED PAIR LAW⟧ at the door's own blocks.  This is the
  SPINE-WITNESSED datum (`M4SocketDischarge`'s hypothesis ledger, group ⟦SPINE-WITNESSED⟧);
  no page proves it and none should.
* `dom` (the `end'` bundle only) — the per-level error-domination product.
  `M4RowsChiZero`'s own header records that it is the field imposing an `X_d ≳ (M·i²)⁸` floor
  on every socket base, and that the `zero'` chain exists precisely to be free of it.  It is
  carried here, named, exactly as `hcap` and `hband` are.

⟦THE `s13BlockFloor` THRESHOLD IS AN `M`-VERSUS-BASE DEMAND⟧ `s13BlockFloor M =
2^{400·(Adoor M·3072M·M)²}` is NOT implied by the socket's `2^{doorRowFloor M} ≤ A` (that
floor is linear in `Adoor M·M`, this one quadratic).  It is therefore carried as a named
binder of the same genre as ⟦gate 8⟧ and the `gP1` top instance — the consumer's arithmetic,
in the open. -/

/-- **⟦ITEM (g) — `DoorRowZeroBase`, FIVE OF SIX⟧** (`doorRowZeroBase_at_socket`). -/
theorem doorRowZeroBase_at_socket {M Xd j : ℕ} {cU : ℕ → ℂ} {bU : ℕ → ℕ → ℂ}
    (hM : 1 ≤ M) (hXd : s13BlockFloor M ≤ Xd) (hj : doorRowFloor M ≤ j)
    (hcoef : ∀ i ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (Adoor M) (3072 * M) i) (calQK (Adoor M) (3072 * M) M i)
        (winCutH Xd (doorCoeffU M)) (bU i) cU) :
    DoorRowZeroBase M Xd j cU bU := by
  obtain ⟨hQ2, hreg, hbig, hfour, hQ1⟩ := s13_doorRowZeroBase_five hM hXd hj
  exact ⟨hQ2, hcoef, hreg, hbig, hfour, hQ1⟩

/-- **⟦ITEM (g) — `DoorRowEndBase`, FIVE OF SEVEN⟧** (`doorRowEndBase_at_socket`) — the same,
with `coefWS` and `dom` carried. -/
theorem doorRowEndBase_at_socket {M Xd j : ℕ} {cU : ℕ → ℂ} {bU : ℕ → ℕ → ℂ}
    (hM : 1 ≤ M) (hXd : s13BlockFloor M ≤ Xd) (hj : doorRowFloor M ≤ j)
    (hcoef : ∀ i ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (Adoor M) (3072 * M) i) (calQK (Adoor M) (3072 * M) M i)
        (winCutH Xd (doorCoeffU M)) (bU i) cU)
    (hdom : ∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) i)
                (calQK (Adoor M) (3072 * M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) i : ℕ) : ℝ)
            / Real.log ((calQK (Adoor M) (3072 * M) M i : ℕ) : ℝ))) :
    DoorRowEndBase M Xd j cU bU := by
  obtain ⟨hQ2, hreg, hbig, hfour, hQ1⟩ := s13_doorRowZeroBase_five hM hXd hj
  exact ⟨hQ2, hcoef, hreg, hbig, hdom, hfour, hQ1⟩

/-- The `zero'` bundle as the fuse's family binder. -/
theorem doorRowZeroBase_family {R : ChowlaRegime} {M : ℕ} {cU : ℕ → ℂ} {bU : ℕ → ℕ → ℂ}
    (hM : 1 ≤ M)
    (hblock : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor M ≤ A + s)
    (hcoef : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ i ∈ Finset.Icc 1 2,
        SeamCoefWS (A + s) (calP (Adoor M) (3072 * M) i) (calQK (Adoor M) (3072 * M) M i)
          (winCutH (A + s) (doorCoeffU M)) (bU i) cU) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase M (A + s) j cU bU :=
  fun H L q j A s hb =>
    doorRowZeroBase_at_socket hM (hblock H L q j A s hb) hb.2.2.2.2.2.2.1
      (hcoef H L q j A s hb)

/-- The `end'` bundle as the fuse's family binder, with `dom` carried per base. -/
theorem doorRowEndBase_family {R : ChowlaRegime} {M : ℕ} {cU : ℕ → ℂ} {bU : ℕ → ℕ → ℂ}
    (hM : 1 ≤ M)
    (hblock : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor M ≤ A + s)
    (hcoef : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ i ∈ Finset.Icc 1 2,
        SeamCoefWS (A + s) (calP (Adoor M) (3072 * M) i) (calQK (Adoor M) (3072 * M) M i)
          (winCutH (A + s) (doorCoeffU M)) (bU i) cU)
    (hdom : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ i ∈ Finset.Icc 1 2,
        ((Nat.sqrt (A + s) : ℝ) + 1)
            * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) i)
                  (calQK (Adoor M) (3072 * M) M i), (1 + 3 / (p : ℝ))
          ≤ (((A + s : ℕ)) : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) i : ℕ) : ℝ)
              / Real.log ((calQK (Adoor M) (3072 * M) M i : ℕ) : ℝ))) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowEndBase M (A + s) j cU bU :=
  fun H L q j A s hb =>
    doorRowEndBase_at_socket hM (hblock H L q j A s hb) hb.2.2.2.2.2.2.1
      (hcoef H L q j A s hb) (hdom H L q j A s hb)

/-! ## §9 — THE COMPOSITE: THE FUSES, AT THE SOCKET

`M4ClosureRepair`'s two fuses with §2–§8 substituted for their frame-side binders.  What
remains is exactly three groups, and every member of each is named:

* ⟦REGISTER⟧ — `hHcap`, `hHreg`, `hg` (the `g`-arm floor: the `∀g ∃R` mechanism), and the
  carried scalars `hK`, `hρ0`, `hρ1`, `hanchor`, `hρcap`, `hC1`, `hM0`;
* ⟦`M`-SIDE, FOUR NUMERALS⟧ — the top instances at `X_d = 3·R.x` of `gP1` and of
  `GRowsZeroGate'''`'s `level1`/`p2`/`dens`.  Each is ONE finite inequality on `Adoor M`, met
  by taking `M` large (⟦REF-SOCKET-2⟧'s window `[14728, 1.44·10¹¹]` in `log₂M + 1`, at the
  `1.7×` tighter exponent);
* ⟦SPINE-WITNESSED⟧ — `hb1`, `hc1`, `hbase` (whose `coefWS` is the strict pair law), `hcap`
  (the A3 capstone family) and `hband` (the `T₀` band).

**GONE**: `hbf`, `hgP1`'s and `hgRows`'s `∀`-quantification, `hL4096`, `harith`, `hone`,
`hprice` — and no `sorry`, no new axiom, anywhere on the path. -/

/-- **⟦THE `end'` FUSE, AT THE SOCKET⟧** (`m4_closure_fuse_end'_at_socket`) — ⟦item 11⟧ at
`RSanDoorRho ρ`, with every frame-side binder of `M4ClosureRepair.m4_closure_fuse_end'`
discharged from `SocketBase`, the `ρ`-frame's own suppliers and four `M`-side numerals. -/
theorem m4_closure_fuse_end'_at_socket :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (x₀ K ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 ≤ K → 0 < ρ → ρ ≤ 1 → 2484 ≤ Nat.log 2 M + 1 →
        Real.log (1 / ρ) ≤ 10 ^ 11 →
        (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) → (∀ A : ℕ, ε A ≤ 0) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.log (Real.log (H : ℝ)) ≤ 10 ^ 11) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → gArmDoorRho x₀ K (R.ω : ℝ) ρ H ≤ (R.x : ℝ)) →
        (∀ n : ℕ, 0 ≤ C₁ n) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          0.062 * Real.log (Real.log (((A + s : ℕ)) : ℝ))
            + 40 * Real.log (Real.log (H : ℝ)) + 6 * Real.log (C₁ (A + s) + 1)
            + 3 * Real.log (1 / ρ) + 33 ≤ M₀ (A + s)) →
        374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
          ≤ Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
        14400 * Real.exp 1 ^ 2 * a2Level1 M
          ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
        138240 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
            + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ))
          ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
        5760 * Cp * (2 / (M : ℝ)) ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
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
        M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hfuse⟩ := m4_closure_fuse_end'
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε x₀ K ρ cU bU t₁ hM hK hρ0 hρ1 hanchor hρcap hb1 hc1 heps hHcap hHreg hg
    hC1 hM0 htopP1 htoplvl htopp2 htopdens hbase hcap hband
  have harith := doorArithFrameRho_family hM hK hρ0 hρ1 hanchor hρcap hHcap hHreg hg hC1 hM0
  refine hfuse R M C₁ M₀ ε K ρ cU bU t₁ hM hb1 hc1 ?_ ?_ ?_ heps ?_ hbase hcap hband harith
  · intro H L q j A s hb
    exact doorBaseFrame_at_socket hb (harith H L q j A s hb)
  · intro H L q j A s hb
    have hL := frames_logX_ge (harith H L q j A s hb)
    exact gP1_at_socketBase_decay hb (le_trans (by norm_num) hL) htopP1
  · intro H L q j A s hb
    have hL := frames_logX_ge (harith H L q j A s hb)
    exact gRowsZeroGate'''_at_socket hb (le_trans (by norm_num) hL) htoplvl htopp2 htopdens
  · intro H L q j A s hb
    exact hL4096_of_frame (harith H L q j A s hb)

/-- **⟦THE `zero'` FUSE, AT THE SOCKET⟧** (`m4_closure_fuse_zero'_at_socket`) — the same at
`M4RowsChiZeroPrime`'s density-free chain: `C_p` FREE and positive, the per-base bundle the
six-field `DoorRowZeroBase`. -/
theorem m4_closure_fuse_zero'_at_socket :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (x₀ K ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 ≤ K → 0 < ρ → ρ ≤ 1 → 2484 ≤ Nat.log 2 M + 1 →
        Real.log (1 / ρ) ≤ 10 ^ 11 →
        (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) → (∀ A : ℕ, ε A ≤ 0) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.log (Real.log (H : ℝ)) ≤ 10 ^ 11) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → gArmDoorRho x₀ K (R.ω : ℝ) ρ H ≤ (R.x : ℝ)) →
        (∀ n : ℕ, 0 ≤ C₁ n) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          0.062 * Real.log (Real.log (((A + s : ℕ)) : ℝ))
            + 40 * Real.log (Real.log (H : ℝ)) + 6 * Real.log (C₁ (A + s) + 1)
            + 3 * Real.log (1 / ρ) + 33 ≤ M₀ (A + s)) →
        374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
          ≤ Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
        14400 * Real.exp 1 ^ 2 * a2Level1 M
          ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
        138240 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
            + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ))
          ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
        5760 * Cp * (2 / (M : ℝ)) ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
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
        M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε x₀ K ρ cU bU t₁ hM hK hρ0 hρ1 hanchor hρcap hb1 hc1 heps hHcap
    hHreg hg hC1 hM0 htopP1 htoplvl htopp2 htopdens hbase hcap hband
  have harith := doorArithFrameRho_family hM hK hρ0 hρ1 hanchor hρcap hHcap hHreg hg hC1 hM0
  refine hfuse Cp hCp R M C₁ M₀ ε K ρ cU bU t₁ hM hb1 hc1 ?_ ?_ ?_ heps ?_ hbase hcap hband
    harith
  · intro H L q j A s hb
    exact doorBaseFrame_at_socket hb (harith H L q j A s hb)
  · intro H L q j A s hb
    have hL := frames_logX_ge (harith H L q j A s hb)
    exact gP1_at_socketBase_decay hb (le_trans (by norm_num) hL) htopP1
  · intro H L q j A s hb
    have hL := frames_logX_ge (harith H L q j A s hb)
    exact gRowsZeroGate'''_at_socket hb (le_trans (by norm_num) hL) htoplvl htopp2 htopdens
  · intro H L q j A s hb
    exact hL4096_of_frame (harith H L q j A s hb)

/-! ## §GK — the G-lever twin -/

/-- `gP1_at_socketBase_decay (:312)` at the lever. -/
theorem gP1_at_socketBase_decay_gk (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} {Cs : ℝ}
    (hb : SocketBase R M H L q j A s) (hX1 : (1 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ))
    (htop : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ Real.log (3 * (R.x : ℝ)) ^ (-theta293)) :
    374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ decayPool (A + s) :=
  le_trans htop (decayPool_ge_top hb hX1)

/-! ## §4 — ⟦ITEM (c)⟧ `GRowsZeroGate'''_gk K` AT THE DECAY POOL

Four slots.  `level1`, `p2` and `dens` are base UPPER caps and go through §3's top instance;
`endpt` reads the base on BOTH sides (`1/X_d` against `(log X_d)^{−θ₂₉₃}/4`) and is a
base-LOWER demand, discharged outright from the ARM's floor. -/

/-- `gRowsZeroGate'''_at_socket (:372)` at the lever. -/
theorem gRowsZeroGate'''_at_socket_gk (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} {Ccc : ℝ}
    (hb : SocketBase R M H L q j A s)
    (hL : (10000000000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ))
    (hlvl : 14400 * Real.exp 1 ^ 2 * a2Level1 M
      ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293))
    (hp2 : 138240 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)
          + 1 / ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ))
      ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293))
    (hdens : 5760 * Ccc * (2 / (M : ℝ))
      ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293)) :
    GRowsZeroGate'''_gk K M (A + s) Ccc (decayPool (A + s)) := by
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hAs : 0 < A + s := by omega
  have htop := decayPool_ge_top hb (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith
  · exact endpt_at_decayPool hAs hL
  · linarith
  · linarith

/-! ## §5 — ⟦ITEM (d)⟧ THE CORRECTED `4096`-THRESHOLD

`hL4096 : 4096 ≤ (log X_d)^{1−1/500−θ₂₉₃}`.  The exponent is POSITIVE (`≥ 0.9945`), so this
is a base-LOWER demand: taking logs it reads `12·log 2 ≤ (1−1/500−θ₂₉₃)·loglog X_d`, i.e.
`loglog X_d ≥ 8.37`.  The ARM delivers `356600`.  ⟦THE DIRECTION IS AS HOPED⟧ — the examiner's
corrected exponent does not flip the demand's sign. -/

/-- `ege_line_of_capGatePerBlock (:595)` at the lever. -/
theorem ege_line_of_capGatePerBlock_gk (K : ℕ) {Cq cs T₀ Kq Ks C : ℝ} {M Nd q P Q Hreg : ℕ}
    {Tann Rrad Rbd CR EP2 epsr : ℝ}
    (hg : S13CapGatePerBlock_gk K Cq cs T₀ Kq Ks C M Nd q P Q Hreg Tann Rrad Rbd CR EP2 epsr) :
    49920 * (q.totient : ℝ) ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ epsr :=
  ege_line_gate (by have := hg.logX_eight; linarith) hg.EP2_gate hg.phi_row

/-! ## §8 — ⟦ITEM (g)⟧ THE TWO PER-BASE ROW BUNDLES

`M4RowsChiEnd.DoorRowEndBase_gk K` (seven fields) and `M4RowsChiZero.DoorRowZeroBase_gk K` (six).
`S13FramesA.s13_doorRowZeroBase_five_gk K` already discharges FIVE of them — `Q2_le`, `reg`, `big`,
`h_four`, `Q1_le_h` — from the door's block-scale floor `s13BlockFloor_gk K M ≤ X_d` and the
socket's own `doorRowFloor M ≤ j`.  This section reads that discharge into the two bundles.

⟦WHAT IS NOT DISCHARGED, AND WHY⟧

* `coefWS` — ⟦THE STRICT RELATIVIZED PAIR LAW⟧ at the door's own blocks.  This is the
  SPINE-WITNESSED datum (`M4SocketDischarge`'s hypothesis ledger, group ⟦SPINE-WITNESSED⟧);
  no page proves it and none should.
* `dom` (the `end'` bundle only) — the per-level error-domination product.
  `M4RowsChiZero`'s own header records that it is the field imposing an `X_d ≳ (M·i²)⁸` floor
  on every socket base, and that the `zero'` chain exists precisely to be free of it.  It is
  carried here, named, exactly as `hcap` and `hband` are.

⟦THE `s13BlockFloor` THRESHOLD IS AN `M`-VERSUS-BASE DEMAND⟧ `s13BlockFloor_gk K M =
2^{400·(Adoor M·3072M·M)²}` is NOT implied by the socket's `2^{doorRowFloor M} ≤ A` (that
floor is linear in `Adoor M·M`, this one quadratic).  It is therefore carried as a named
binder of the same genre as ⟦gate 8⟧ and the `gP1` top instance — the consumer's arithmetic,
in the open. -/

/-- `doorRowZeroBase_at_socket (:625)` at the lever. -/
theorem doorRowZeroBase_at_socket_gk (K : ℕ) {M Xd j : ℕ} {cU : ℕ → ℂ} {bU : ℕ → ℕ → ℂ}
    (hM : 1 ≤ M) (hXd : s13BlockFloor_gk K M ≤ Xd) (hj : doorRowFloor M ≤ j)
    (hcoef : ∀ i ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (Adoor M) (s13GK K M) i) (calQK (Adoor M) (s13GK K M) M i)
        (winCutH Xd (doorCoeffU_gk K M)) (bU i) cU) :
    DoorRowZeroBase_gk K M Xd j cU bU := by
  obtain ⟨hQ2, hreg, hbig, hfour, hQ1⟩ := s13_doorRowZeroBase_five_gk K hM hXd hj
  exact ⟨hQ2, hcoef, hreg, hbig, hfour, hQ1⟩

/-- `doorRowEndBase_at_socket (:636)` at the lever. -/
theorem doorRowEndBase_at_socket_gk (K : ℕ) {M Xd j : ℕ} {cU : ℕ → ℂ} {bU : ℕ → ℕ → ℂ}
    (hM : 1 ≤ M) (hXd : s13BlockFloor_gk K M ≤ Xd) (hj : doorRowFloor M ≤ j)
    (hcoef : ∀ i ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (Adoor M) (s13GK K M) i) (calQK (Adoor M) (s13GK K M) M i)
        (winCutH Xd (doorCoeffU_gk K M)) (bU i) cU)
    (hdom : ∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (Adoor M) (s13GK K M) i)
                (calQK (Adoor M) (s13GK K M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (s13GK K M) i : ℕ) : ℝ)
            / Real.log ((calQK (Adoor M) (s13GK K M) M i : ℕ) : ℝ))) :
    DoorRowEndBase_gk K M Xd j cU bU := by
  obtain ⟨hQ2, hreg, hbig, hfour, hQ1⟩ := s13_doorRowZeroBase_five_gk K hM hXd hj
  exact ⟨hQ2, hcoef, hreg, hbig, hdom, hfour, hQ1⟩

/-- `doorRowZeroBase_family (:652)` at the lever. -/
theorem doorRowZeroBase_family_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {cU : ℕ → ℂ} {bU : ℕ → ℕ → ℂ}
    (hM : 1 ≤ M)
    (hblock : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor_gk K M ≤ A + s)
    (hcoef : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ i ∈ Finset.Icc 1 2,
        SeamCoefWS (A + s) (calP (Adoor M) (s13GK K M) i) (calQK (Adoor M) (s13GK K M) M i)
          (winCutH (A + s) (doorCoeffU_gk K M)) (bU i) cU) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase_gk K M (A + s) j cU bU :=
  fun H L q j A s hb =>
    doorRowZeroBase_at_socket_gk K hM (hblock H L q j A s hb) hb.2.2.2.2.2.2.1
      (hcoef H L q j A s hb)

/-- `doorRowEndBase_family (:665)` at the lever. -/
theorem doorRowEndBase_family_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {cU : ℕ → ℂ} {bU : ℕ → ℕ → ℂ}
    (hM : 1 ≤ M)
    (hblock : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor_gk K M ≤ A + s)
    (hcoef : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ i ∈ Finset.Icc 1 2,
        SeamCoefWS (A + s) (calP (Adoor M) (s13GK K M) i) (calQK (Adoor M) (s13GK K M) M i)
          (winCutH (A + s) (doorCoeffU_gk K M)) (bU i) cU)
    (hdom : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ i ∈ Finset.Icc 1 2,
        ((Nat.sqrt (A + s) : ℝ) + 1)
            * ∏ p ∈ primeBand (calP (Adoor M) (s13GK K M) i)
                  (calQK (Adoor M) (s13GK K M) M i), (1 + 3 / (p : ℝ))
          ≤ (((A + s : ℕ)) : ℝ) * (Real.log ((calP (Adoor M) (s13GK K M) i : ℕ) : ℝ)
              / Real.log ((calQK (Adoor M) (s13GK K M) M i : ℕ) : ℝ))) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowEndBase_gk K M (A + s) j cU bU :=
  fun H L q j A s hb =>
    doorRowEndBase_at_socket_gk K hM (hblock H L q j A s hb) hb.2.2.2.2.2.2.1
      (hcoef H L q j A s hb) (hdom H L q j A s hb)

/-! ## §9 — THE COMPOSITE: THE FUSES, AT THE SOCKET

`M4ClosureRepair`'s two fuses with §2–§8 substituted for their frame-side binders.  What
remains is exactly three groups, and every member of each is named:

* ⟦REGISTER⟧ — `hHcap`, `hHreg`, `hg` (the `g`-arm floor: the `∀g ∃R` mechanism), and the
  carried scalars `hKar`, `hρ0`, `hρ1`, `hanchor`, `hρcap`, `hC1`, `hM0`;
* ⟦`M`-SIDE, FOUR NUMERALS⟧ — the top instances at `X_d = 3·R.x` of `gP1` and of
  `GRowsZeroGate'''_gk K`'s `level1`/`p2`/`dens`.  Each is ONE finite inequality on `Adoor M`, met
  by taking `M` large (⟦REF-SOCKET-2⟧'s window `[14728, 1.44·10¹¹]` in `log₂M + 1`, at the
  `1.7×` tighter exponent);
* ⟦SPINE-WITNESSED⟧ — `hb1`, `hc1`, `hbase` (whose `coefWS` is the strict pair law), `hcap`
  (the A3 capstone family) and `hband` (the `T₀` band).

**GONE**: `hbf`, `hgP1`'s and `hgRows`'s `∀`-quantification, `hL4096`, `harith`, `hone`,
`hprice` — and no `sorry`, no new axiom, anywhere on the path. -/

/-- `m4_closure_fuse_end'_at_socket (:704)` at the lever. -/
theorem m4_closure_fuse_end'_at_socket_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (x₀ Kar ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 ≤ Kar → 0 < ρ → ρ ≤ 1 → 2484 ≤ Nat.log 2 M + 1 →
        Real.log (1 / ρ) ≤ 10 ^ 11 →
        (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) → (∀ A : ℕ, ε A ≤ 0) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.log (Real.log (H : ℝ)) ≤ 10 ^ 11) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → gArmDoorRho x₀ Kar (R.ω : ℝ) ρ H ≤ (R.x : ℝ)) →
        (∀ n : ℕ, 0 ≤ C₁ n) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          0.062 * Real.log (Real.log (((A + s : ℕ)) : ℝ))
            + 40 * Real.log (Real.log (H : ℝ)) + 6 * Real.log (C₁ (A + s) + 1)
            + 3 * Real.log (1 / ρ) + 33 ≤ M₀ (A + s)) →
        374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
          ≤ Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
        14400 * Real.exp 1 ^ 2 * a2Level1 M
          ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
        138240 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)
            + 1 / ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ))
          ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
        5760 * Cp * (2 / (M : ℝ)) ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowEndBase_gk K M (A + s) j cU bU) →
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
        M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hfuse⟩ := m4_closure_fuse_end'_gk K hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε x₀ Kar ρ cU bU t₁ hM hKar hρ0 hρ1 hanchor hρcap hb1 hc1 heps hHcap hHreg hg
    hC1 hM0 htopP1 htoplvl htopp2 htopdens hbase hcap hband
  have harith := doorArithFrameRho_family hM hKar hρ0 hρ1 hanchor hρcap hHcap hHreg hg hC1 hM0
  refine hfuse R M C₁ M₀ ε Kar ρ cU bU t₁ hM hb1 hc1 ?_ ?_ ?_ heps ?_ hbase hcap hband harith
  · intro H L q j A s hb
    exact doorBaseFrame_at_socket hb (harith H L q j A s hb)
  · intro H L q j A s hb
    have hL := frames_logX_ge (harith H L q j A s hb)
    exact gP1_at_socketBase_decay_gk K hb (le_trans (by norm_num) hL) htopP1
  · intro H L q j A s hb
    have hL := frames_logX_ge (harith H L q j A s hb)
    exact gRowsZeroGate'''_at_socket_gk K hb (le_trans (by norm_num) hL) htoplvl htopp2 htopdens
  · intro H L q j A s hb
    exact hL4096_of_frame (harith H L q j A s hb)

/-- `m4_closure_fuse_zero'_at_socket (:772)` at the lever. -/
theorem m4_closure_fuse_zero'_at_socket_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (x₀ Kar ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 ≤ Kar → 0 < ρ → ρ ≤ 1 → 2484 ≤ Nat.log 2 M + 1 →
        Real.log (1 / ρ) ≤ 10 ^ 11 →
        (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) → (∀ A : ℕ, ε A ≤ 0) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.log (Real.log (H : ℝ)) ≤ 10 ^ 11) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → gArmDoorRho x₀ Kar (R.ω : ℝ) ρ H ≤ (R.x : ℝ)) →
        (∀ n : ℕ, 0 ≤ C₁ n) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          0.062 * Real.log (Real.log (((A + s : ℕ)) : ℝ))
            + 40 * Real.log (Real.log (H : ℝ)) + 6 * Real.log (C₁ (A + s) + 1)
            + 3 * Real.log (1 / ρ) + 33 ≤ M₀ (A + s)) →
        374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
          ≤ Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
        14400 * Real.exp 1 ^ 2 * a2Level1 M
          ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
        138240 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)
            + 1 / ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ))
          ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
        5760 * Cp * (2 / (M : ℝ)) ≤ 1 / 4 * Real.log (3 * (R.x : ℝ)) ^ (-theta293) →
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
        M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε x₀ Kar ρ cU bU t₁ hM hKar hρ0 hρ1 hanchor hρcap hb1 hc1 heps hHcap
    hHreg hg hC1 hM0 htopP1 htoplvl htopp2 htopdens hbase hcap hband
  have harith := doorArithFrameRho_family hM hKar hρ0 hρ1 hanchor hρcap hHcap hHreg hg hC1 hM0
  refine hfuse Cp hCp R M C₁ M₀ ε Kar ρ cU bU t₁ hM hb1 hc1 ?_ ?_ ?_ heps ?_ hbase hcap hband
    harith
  · intro H L q j A s hb
    exact doorBaseFrame_at_socket hb (harith H L q j A s hb)
  · intro H L q j A s hb
    have hL := frames_logX_ge (harith H L q j A s hb)
    exact gP1_at_socketBase_decay_gk K hb (le_trans (by norm_num) hL) htopP1
  · intro H L q j A s hb
    have hL := frames_logX_ge (harith H L q j A s hb)
    exact gRowsZeroGate'''_at_socket_gk K hb (le_trans (by norm_num) hL) htoplvl htopp2 htopdens
  · intro H L q j A s hb
    exact hL4096_of_frame (harith H L q j A s hb)

-- #audit (temporary)

end Salt.MR
