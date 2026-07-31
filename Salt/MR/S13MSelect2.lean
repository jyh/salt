/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S13FramesA
import Salt.MR.M4Assembly

/-!
# ⟦MSELECT v2⟧ — THE `M`-SELECTION SYSTEM AFTER THE D2 FREEZE CORRECTION

PURELY ADDITIVE: no landed declaration is touched anywhere in this file.  `S13FramesA`'s
`MSelect` and all four of its landed consumers stay exactly as they are; this file mints the
corrected twin beside them.

## ⟦THE RULING THIS FILE IMPLEMENTS⟧

THE CLOSURE EXAMINER's ⟦D2⟧ (kernel-certified, `flags.md` 2026-07-30 18:46) showed that
`MSelect`'s fields ⟦2⟧ `winFloor` and ⟦4⟧ `absorb` TOGETHER force `loglog H₋ ≥ 6412.6`, which
contradicts the landed `λ`-table (`λ₋ ≤ 83.667`, §9's tightened `81.184`).  The examiner's
adjudication, RATIFIED by the Captain:

* **both offending fields are WRITE-ONLY.**  `s13_gate8_of_MSelect` and
  `s13_g2_jfloor_of_MSelect` read field ⟦3⟧ (`gRows`) alone; `s13_doorGates_of_MSelect` reads
  ⟦1⟧ (`bfloor`) and ⟦5⟧ (`blockCeil`) alone.  Nothing in the kernel reads ⟦2⟧ or ⟦4⟧.
* **⟦4⟧ `absorb` is not an `M`-lower at all.**  `abs8640` is a demand on the BASE `X_d`, and
  the socket base carries `SocketBase`'s x-scale field `x ≤ 16·ω·arcDen 12 H·A`, which against
  the regime's own `hPHheadroom` pins `A` at `2^{4⌊ε²H₊⌋₊}/(2·(log H)^{12})`.  §2 below turns
  that into `log A ≥ √H`, hence `loglog A ≥ ½·log H ≥ ½·e^{50} = 2.6·10²¹` — EIGHTEEN ORDERS
  above the `6412.6` the line asks for.  R3-B's banked finding ("`abs8640`'s honest home is
  `MSelect.absorb`, an `M`-lower") is refuted at the bytes.
* **⟦2⟧ `winFloor` was the wrong statement of the window gate** (the examiner's ⟦D5⟧).  The
  TRUE window gate is `s13_smallGradeFits`' `hfit` slot at `(7/10)·j₀ + 3·G ≤ log H` — a
  `7/10` coefficient (not `log 2 = 0.693`) plus the additive charge
  `G = log 9 + 84·loglog H + 2·log(strataResidual H) − log ρ`.  `winFloor` neither implies it
  nor is implied by it; §3's field `winFit` states the true gate directly.

So `MSelect'` has **four** fields — ⟦1⟧, ⟦3⟧, ⟦5⟧ verbatim from `MSelect`, and `winFit` in
place of `winFloor`; `absorb` is DELETED, and its content re-homed as §2's
`s13_abs8640_of_socketBase`.  The certified working point (`m = 66`, `s13M`,
`λ₋ ∈ [74.198, 83.667]`, §9's `81.184`) survives untouched.

## ⟦THE SECTIONS⟧

* §1 — the examiner's kernel-verified probes, ported verbatim (`P1`/`P4`).
* §2 — the tower arithmetic: `⌊ε²H₊⌋₊ ≥ 2√H − 1` from `hPNTwindow`, then `log A ≥ √H`, then
  `loglog A ≥ 6500`, then `abs8640` at the socket base and at every base above it.
* §3 — `MSelect'`, the four-field system.
* §4 — the consumer bridges, re-routed at `MSelect'`.
* §5 — the `winFit` discharge (the half-window floor) and the satisfaction theorems.
-/

open Salt.Entropy.Chowla

noncomputable section

namespace Salt.MR

/-! ## §1 — THE EXAMINER'S STONES, PORTED

Kernel-verified at `scratchpad/examiner/{P1,P4}.lean` during THE CLOSURE EXAMINER's sitting;
carried here verbatim so the closure owns them.  Nothing is re-derived. -/

/-- `θ₂₉₃ − 1/500 ≥ 1.4·10⁻³` (true value `1.41349·10⁻³`) — the crossing window's own
exponent, from below.  `θ₂₉₃ = 1/(32(3e+1))`. -/
theorem s13_theta293_margin_lo : (14 : ℝ) / 10000 ≤ theta293 - 1 / 500 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he : Real.exp 1 < 2.7182818286 := by have := Real.exp_one_lt_d9; linarith
  have hden : (0 : ℝ) < 32 * (3 * Real.exp 1 + 1) := by nlinarith
  have hval : theta293 = 1 / (32 * (3 * Real.exp 1 + 1)) := rfl
  rw [hval]
  have : (14 : ℝ) / 10000 + 1 / 500 ≤ 1 / (32 * (3 * Real.exp 1 + 1)) := by
    rw [le_div_iff₀ hden]; nlinarith
  linarith

/-- **⟦THE EXACT SHAPE OF `abs8640`'s DEMAND⟧** (`P4`, ported) — it is a `loglog X` floor of
size `log 8640/(θ₂₉₃ − 1/500) = 6412.6`, and NOTHING ELSE. -/
theorem s13_abs8640_of_loglog {X : ℝ} (hX : 1 < Real.log X)
    (h : (6500 : ℝ) ≤ Real.log (Real.log X)) :
    (8640 : ℝ) ≤ (Real.log X) ^ (theta293 - 1 / 500) := by
  have hθlo := s13_theta293_margin_lo
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hrw : (Real.log X) ^ (theta293 - 1 / 500)
      = Real.exp ((theta293 - 1 / 500) * Real.log (Real.log X)) := by
    rw [Real.rpow_def_of_pos hL0]; ring_nf
  rw [hrw]
  have hprod : (9.07 : ℝ) ≤ (theta293 - 1 / 500) * Real.log (Real.log X) := by
    nlinarith [hθlo, h]
  have h8640 : (8640 : ℝ) ≤ Real.exp 9.07 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have he9 : (8103 : ℝ) ≤ Real.exp 9 := by
      have hh : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      rw [hh]
      have hc : (2.7182818283 : ℝ) ^ (9 : ℕ) ≤ (Real.exp 1) ^ (9 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) h1.le 9
      have : (8103 : ℝ) ≤ (2.7182818283 : ℝ) ^ (9 : ℕ) := by norm_num
      linarith
    have he007 : (1.07 : ℝ) ≤ Real.exp 0.07 := by
      have := Real.add_one_le_exp (0.07 : ℝ); linarith
    have hmul : (8640 : ℝ) ≤ Real.exp 9 * Real.exp 0.07 := by
      nlinarith [Real.exp_pos (9 : ℝ), Real.exp_pos (0.07 : ℝ)]
    calc (8640 : ℝ) ≤ Real.exp 9 * Real.exp 0.07 := hmul
      _ = Real.exp 9.07 := by rw [← Real.exp_add]; norm_num
  exact le_trans h8640 (Real.exp_le_exp.mpr hprod)

/-- **⟦THE BASE IS PINNED BY `x`, NOT BY `2^{doorRowFloor M}`⟧** (`P4`, ported) — `SocketBase`'s
x-scale field plus the regime's `hPHheadroom` give `(4^{⌊ε²H₊⌋₊})² ≤ 2·arcDen 12 H·A`. -/
theorem s13_socketBase_xscale {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBase R M H L q j A s) :
    ((4 ^ ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) ^ 2 ≤ 2 * arcDen 12 H * (A : ℝ) := by
  have hx : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) := hb.2.2.2.2.2.2.2.2.2.2.1
  have hhead := R.hPHheadroom
  have hω : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
  nlinarith [hx, hhead, hω]

/-- **THE OTHER BASE FLOOR** (`P4`, ported) — the socket's `A` also carries the door floor
`2^{doorRowFloor M} ≤ A`, the bound `MSelect.absorb` used to charge.  Both are LOWER bounds on
the same object; §2 shows the x-scale one is astronomically the larger, which is exactly why
field ⟦4⟧ was never an `M`-lower. -/
theorem s13_socketBase_doorFloor {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBase R M H L q j A s) : 2 ^ (doorRowFloor M) ≤ A := by
  have hjfl : doorRowFloor M ≤ j := hb.2.2.2.2.2.2.1
  have h2j : 2 ^ j ≤ A := hb.2.2.2.2.2.2.2.2.1
  exact le_trans (Nat.pow_le_pow_right (by norm_num) hjfl) h2j

/-! ## §2 — THE TOWER ARITHMETIC: `abs8640` AT THE SOCKET BASE

The chain, in four steps.

1. `hPNTwindow` (`√H₋ ≤ ε²H₋/2`) plus `H₋ ≤ H₊` give `2·√H₊ ≤ ε²·H₊`, so the headroom
   exponent `m := ⌊ε²H₊⌋₊` clears `2·√H − 1` at every admissible `H`.
2. §1's x-scale, in logs: `4m·log 2 ≤ log 2 + 12·loglog H + log A`.
3. `loglog H ≤ 2(√(log H) − 1)` and `log H ≤ 2(√H − 1)` price the subtraction at the FOURTH
   root, which the `√H` of step 1 dominates: `log A ≥ √H`.
4. `loglog A ≥ log √H = ½·log H ≥ ½·e^{50} = 2.6·10²¹ ≥ 6500`, and §1's `abs8640` line fires.

Every constant is checked at the regime's own floors (`H ≥ 4·10⁶`, `loglog H ≥ 50` from the
capstone's absorbed `loglogFloor50`); nothing here reads `M`. -/

/-- `4·10⁶ ≤ e^{50}` — the one numeral the tower spends (`e^{20} ≥ 4.85·10⁸`). -/
theorem s13_four_million_le_exp50 : (4000000 : ℝ) ≤ Real.exp 50 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h20 : Real.exp 20 = (Real.exp 1) ^ (20 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : (2.7182818283 : ℝ) ^ (20 : ℕ) ≤ (Real.exp 1) ^ (20 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h1.le 20
  have hn : (4000000 : ℝ) ≤ (2.7182818283 : ℝ) ^ (20 : ℕ) := by norm_num
  have hm : Real.exp 20 ≤ Real.exp 50 := Real.exp_le_exp.mpr (by norm_num)
  rw [h20] at hm
  linarith

/-- **⟦THE HEADROOM EXPONENT'S FLOOR⟧** — `2·√H − 1 ≤ ⌊ε²H₊⌋₊` for every `H ≤ H₊`.  From
`hPNTwindow` alone: `√H₋ ≤ ε²H₋/2` reads `2 ≤ ε²·√H₋`, and `√H₋ ≤ √H₊` upgrades it to
`2·√H₊ ≤ ε²·H₊` (the `t ↦ t²/√H₋` comparison), which the nat floor loses at most `1` of. -/
theorem s13_socketBase_mFloor {R : ChowlaRegime} {H : ℕ} (hhi : H ≤ R.Hhi) :
    2 * Real.sqrt (H : ℝ) - 1 ≤ ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hlohi : (R.Hlo : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast R.hHlohi
  set a : ℝ := Real.sqrt (R.Hlo : ℝ) with ha
  set b : ℝ := Real.sqrt (R.Hhi : ℝ) with hb
  have ha2 : a ^ 2 = (R.Hlo : ℝ) := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = (R.Hhi : ℝ) := Real.sq_sqrt (by positivity)
  have ha0 : (0 : ℝ) < a := by rw [ha]; exact Real.sqrt_pos.mpr (by linarith)
  have hb0 : (0 : ℝ) ≤ b := Real.sqrt_nonneg _
  have hab : a ≤ b := Real.sqrt_le_sqrt hlohi
  have hpnt := R.hPNTwindow
  rw [← ha, ← ha2] at hpnt
  have hkey : (2 : ℝ) ≤ (R.eps : ℝ) ^ 2 * a := by
    have : 2 * a ≤ (R.eps : ℝ) ^ 2 * a ^ 2 := by linarith
    nlinarith [ha0]
  have heb : 2 * b ≤ (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) := by
    rw [← hb2]; nlinarith [hkey, hab, hb0, ha0]
  have hub : Real.sqrt (H : ℝ) ≤ b := Real.sqrt_le_sqrt (by exact_mod_cast hhi)
  have hfl : (R.eps ^ 2 * (R.Hhi : ℚ)) < (⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) + 1 :=
    Nat.lt_floor_add_one _
  have hflR : (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) < ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by exact_mod_cast hfl :
      ((R.eps ^ 2 * (R.Hhi : ℚ) : ℚ) : ℝ) < (((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℚ) : ℝ) + 1)
  linarith

/-- **⟦THE BASE IS `√H`-LARGE⟧** — `√H ≤ log A` at every socket base, from the x-scale and
the headroom exponent's floor.  This is the whole content of ⟦D2⟧'s refutation. -/
theorem s13_socketBase_logA_ge_sqrt {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    Real.sqrt (H : ℝ) ≤ Real.log (A : ℝ) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have hlogHbig : (4000000 : ℝ) ≤ Real.log (H : ℝ) := le_trans s13_four_million_le_exp50 hexp50
  set u : ℝ := Real.sqrt (H : ℝ) with hu
  set w : ℝ := Real.sqrt (Real.log (H : ℝ)) with hw
  have hu2 : u ^ 2 = (H : ℝ) := Real.sq_sqrt (by positivity)
  have hw2 : w ^ 2 = Real.log (H : ℝ) := Real.sq_sqrt hlogH0.le
  have hu0 : (0 : ℝ) < u := by rw [hu]; exact Real.sqrt_pos.mpr (by linarith)
  have hw0 : (0 : ℝ) < w := by rw [hw]; exact Real.sqrt_pos.mpr hlogH0
  have hu2000 : (2000 : ℝ) ≤ u := by nlinarith [hu2, hu0, hHR]
  have hw2000 : (2000 : ℝ) ≤ w := by nlinarith [hw2, hw0, hlogHbig]
  have hlogu : Real.log u = Real.log (H : ℝ) / 2 := by
    rw [hu]; exact Real.log_sqrt (by positivity)
  have hlogule : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu0
  have hHu : Real.log (H : ℝ) ≤ 2 * u - 2 := by rw [hlogu] at hlogule; linarith
  have hlogw : Real.log w = Real.log (Real.log (H : ℝ)) / 2 := by
    rw [hw]; exact Real.log_sqrt hlogH0.le
  have hlogwle : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hw0
  have hllH : Real.log (Real.log (H : ℝ)) ≤ 2 * w - 2 := by rw [hlogw] at hlogwle; linarith
  have hwu : w ^ 2 ≤ 2 * u := by rw [hw2]; linarith
  -- ⟦the x-scale, in logs⟧
  set m : ℕ := ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ with hm
  have hxs : ((4 ^ m : ℕ) : ℝ) ^ 2 ≤ 2 * arcDen 12 H * (A : ℝ) := s13_socketBase_xscale hb
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hAR : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hlhs0 : (0 : ℝ) < ((4 ^ m : ℕ) : ℝ) ^ 2 := by positivity
  have hlog := Real.log_le_log hlhs0 hxs
  have hL : Real.log (((4 ^ m : ℕ) : ℝ) ^ 2) = 4 * (m : ℝ) * Real.log 2 := by
    have h4 : ((4 ^ m : ℕ) : ℝ) = (4 : ℝ) ^ m := by push_cast; ring
    rw [h4, ← pow_mul, Real.log_pow, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hRR : Real.log (2 * arcDen 12 H * (A : ℝ))
      = Real.log 2 + 12 * Real.log (Real.log (H : ℝ)) + Real.log (A : ℝ) := by
    rw [harcpow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  rw [hL, hRR] at hlog
  have hmfl : 2 * u - 1 ≤ (m : ℝ) := by rw [hm, hu]; exact s13_socketBase_mFloor hhi
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  nlinarith [hlog, hmfl, hllH, hwu, hw2000, hu2000, hl2lo, hl2hi, hu0, hw0]

/-- **⟦THE SHARP `loglog` FIGURE⟧** — `loglog A ≥ ½·log H`.  This is the honest strength of
the x-scale discharge, and the number every exponent question should be priced against: at
the capstone's absorbed `loglogFloor50` it reads `loglog A ≥ ½·e^{50} = 2.59·10²¹`. -/
theorem s13_socketBase_loglogA_sharp {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    Real.log (H : ℝ) / 2 ≤ Real.log (Real.log (A : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  set u : ℝ := Real.sqrt (H : ℝ) with hu
  have hu0 : (0 : ℝ) < u := by rw [hu]; exact Real.sqrt_pos.mpr (by linarith)
  have hmain : u ≤ Real.log (A : ℝ) := s13_socketBase_logA_ge_sqrt hfl hb
  have hlogu : Real.log u = Real.log (H : ℝ) / 2 := by
    rw [hu]; exact Real.log_sqrt (by positivity)
  have hmono := Real.log_le_log hu0 hmain
  rw [hlogu] at hmono
  linarith

/-- **⟦THE `loglog` FIGURE⟧** — `loglog A ≥ ½·log H ≥ ½·e^{50} = 2.6·10²¹`, eighteen orders
above the `6412.6` `abs8640` asks for.  (Stated at the slack numeral `6500`.) -/
theorem s13_socketBase_loglogA {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    (2000 : ℝ) ≤ Real.log (A : ℝ) ∧ (6500 : ℝ) ≤ Real.log (Real.log (A : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have hlogHbig : (4000000 : ℝ) ≤ Real.log (H : ℝ) := le_trans s13_four_million_le_exp50 hexp50
  set u : ℝ := Real.sqrt (H : ℝ) with hu
  have hu2 : u ^ 2 = (H : ℝ) := Real.sq_sqrt (by positivity)
  have hu0 : (0 : ℝ) < u := by rw [hu]; exact Real.sqrt_pos.mpr (by linarith)
  have hu2000 : (2000 : ℝ) ≤ u := by nlinarith [hu2, hu0, hHR]
  have hmain : u ≤ Real.log (A : ℝ) := s13_socketBase_logA_ge_sqrt hfl hb
  exact ⟨le_trans hu2000 hmain, by have := s13_socketBase_loglogA_sharp hfl hb; linarith⟩

/-- **⟦`abs8640` AT THE SOCKET BASE — THE D2 CORRECTION, KERNELIZED⟧**
(`s13_abs8640_of_socketBase`).  `8640 ≤ (log A)^{θ₂₉₃ − 1/500}` from `SocketBase` and the
capstone's absorbed `loglogFloor50` alone.  NO `M`-lower is spent: the line is a BASE-lower,
discharged at `SocketBase`'s own x-scale field. -/
theorem s13_abs8640_of_socketBase {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    (8640 : ℝ) ≤ (Real.log (A : ℝ)) ^ (theta293 - 1 / 500) := by
  obtain ⟨h1, h2⟩ := s13_socketBase_loglogA hfl hb
  exact s13_abs8640_of_loglog (by linarith) h2

/-- The same line at any base ABOVE the socket's `A` — in particular at the wire's own
`X_d = A + s`, which is what `DoorCapErrWS`/`DoorCapBasePerBlock` read. -/
theorem s13_abs8640_at_base {R : ChowlaRegime} {M H L q j A s B : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAB : A ≤ B) :
    (8640 : ℝ) ≤ (Real.log (B : ℝ)) ^ (theta293 - 1 / 500) := by
  obtain ⟨h1, -⟩ := s13_socketBase_loglogA hfl hb
  have hcore := s13_abs8640_of_socketBase hfl hb
  have hABR : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
  have hA0 : (0 : ℝ) < (A : ℝ) := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    exact_mod_cast hA
  have hmono : Real.log (A : ℝ) ≤ Real.log (B : ℝ) := Real.log_le_log hA0 hABR
  have hθ : (0 : ℝ) ≤ theta293 - 1 / 500 := by have := s13_theta293_margin_lo; linarith
  exact le_trans hcore (Real.rpow_le_rpow (by linarith) hmono hθ)

/-- `abs8640` at the wire's base `X_d = A + s`. -/
theorem s13_abs8640_at_shift {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    (8640 : ℝ) ≤ (Real.log ((A + s : ℕ) : ℝ)) ^ (theta293 - 1 / 500) :=
  s13_abs8640_at_base hfl hb (Nat.le_add_right A s)

/-- **⟦`abs8640` AT A FREE EXPONENT⟧** (`s13_abs8640_at_exponent`) — the line is NOT
transportable down the `ε`-window for free (`t ↦ (log X)^t` is increasing, so a smaller `εr`
asks for a LARGER `loglog X`), so the honest form carries the exponent's own floor:
`2·log 8640 ≤ εr·log H`.  Against §2's sharp figure `loglog A ≥ ½·log H` this is exactly the
demand, and at the capstone's absorbed `loglogFloor50` (`log H ≥ e^{50} = 5.18·10²¹`) it is
met by every `εr ≥ 3.5·10⁻²¹` — the whole live `ε`-window bar its bottom. -/
theorem s13_abs8640_at_exponent {R : ChowlaRegime} {M H L q j A s B : ℕ} {εr : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAB : A ≤ B)
    (hεr : 2 * Real.log 8640 ≤ εr * Real.log (H : ℝ)) :
    (8640 : ℝ) ≤ (Real.log (B : ℝ)) ^ εr := by
  obtain ⟨h1, -⟩ := s13_socketBase_loglogA hfl hb
  have hsharp := s13_socketBase_loglogA_sharp hfl hb
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have h8640 : (0 : ℝ) < Real.log 8640 := Real.log_pos (by norm_num)
  have hA0 : (0 : ℝ) < (A : ℝ) := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    exact_mod_cast hA
  have hABR : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
  have hmono : Real.log (A : ℝ) ≤ Real.log (B : ℝ) := Real.log_le_log hA0 hABR
  have hlogB0 : (0 : ℝ) < Real.log (B : ℝ) := by linarith
  have hll : Real.log (Real.log (A : ℝ)) ≤ Real.log (Real.log (B : ℝ)) :=
    Real.log_le_log (by linarith) hmono
  have hε0 : (0 : ℝ) < εr := by nlinarith [hεr, hlogH0, h8640]
  have hkey : Real.log 8640 ≤ εr * Real.log (Real.log (B : ℝ)) := by nlinarith [hsharp, hll, hε0]
  rw [Real.rpow_def_of_pos hlogB0]
  calc (8640 : ℝ) = Real.exp (Real.log 8640) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (εr * Real.log (Real.log (B : ℝ))) := Real.exp_le_exp.mpr hkey
    _ = Real.exp (Real.log (Real.log (B : ℝ)) * εr) := by rw [mul_comm]

/-! ## §3 — `MSelect'`, THE FOUR-FIELD SYSTEM -/

/-- **⟦THE `M`-SELECTION SYSTEM, v2⟧** (`MSelect' Cg δ₀ Λ ρ R M`) — the FOUR conditions the
re-cut capstone's `M` must meet.

| # | field | direction | what it is | vs `MSelect` |
|---|---|---|---|---|
| 1 | `bfloor` | `M`-LOWER | `24·Cg/δ₀ ≤ M`, i.e. `M4DoorGates.hMδ` | ⟦1⟧ verbatim |
| 2 | `gRows` | `M`-LOWER | `242·Λ ≤ Adoor M` — K1's surviving `gRows` term | ⟦3⟧ verbatim |
| 3 | `blockCeil` | `M`-UPPER | the DEMOTED arm summand `4ω·s13BlockFloor M ≤ x` | ⟦5⟧ verbatim |
| 4 | `winFit` | `M`-UPPER | THE TRUE WINDOW GATE, at `s13_smallGradeFits`' shape | replaces ⟦2⟧ |

`MSelect.absorb` (⟦4⟧) is GONE — §2 discharges it at the socket base — and `MSelect.winFloor`
(⟦2⟧) is replaced, not weakened: `winFit` is the `hfit` slot of `s13_smallGradeFits` written
out, so the bridge in §4 is `fun H hlo hhi => s13_smallGradeFits _ _ hlo (hS.winFit H hlo hhi)`
with nothing in between.

⟦THE `ρ` PARAMETER⟧  The true gate carries the `ρ`-page's own `log(1/ρ)` charge inside `G`, so
the system is indexed by `ρ` as well.  At the capstone's call site `ρ` is
`doorRhoOfDelta (s12DeltaSock δ₀ K)` — determined by `δ₀` and `K`, both bound before `M`. -/
structure MSelect' (Cg δ₀ Λ ρ : ℝ) (R : ChowlaRegime) (M : ℕ) : Prop where
  /-- ⟦1⟧ the `b`-floor — `M4DoorGates.hMδ`.  (`MSelect.bfloor`, verbatim.) -/
  bfloor : 24 * Cg / δ₀ ≤ (M : ℝ)
  /-- ⟦2⟧ the surviving `gRows` demand, `Adoor M ≳ 242·λ₊`.  (`MSelect.gRows`, verbatim.) -/
  gRows : 242 * Λ ≤ (Adoor M : ℝ)
  /-- ⟦3⟧ the DEMOTED arm summand — the `400·(A·G·M)²` block ceiling against `x`.
  (`MSelect.blockCeil`, verbatim.) -/
  blockCeil : 4 * R.ω * s13BlockFloor M ≤ R.x
  /-- ⟦4⟧ **THE TRUE WINDOW GATE** — `s13_smallGradeFits`' `hfit` slot, at every admissible
  window length: `(7/10)·doorRowFloor M + 3·G ≤ log H` with
  `G = log 9 + 84·loglog H + 2·log(strataResidual H) − log ρ`. -/
  winFit : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
    (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ)
        + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
            + 2 * Real.log (strataResidual H) - Real.log ρ)
      ≤ Real.log (H : ℝ)

/-! ## §4 — THE CONSUMER BRIDGES, RE-ROUTED AT `MSelect'`

The three landed consumers read only `gRows`/`bfloor`/`blockCeil`, so each re-routes with its
landed proof unchanged.  The fourth bridge is new: it is what `winFit` was minted for. -/

/-- **⟦A-4 FROM `MSelect'`⟧** — `s13_gate8_of_MSelect` at the corrected system.  Reads field
⟦2⟧ (`gRows`) alone (`242·log 2 = 167.7 > 12`). -/
theorem s13_gate8_of_MSelect' {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ} (hΛ : 0 < Λ)
    (hS : MSelect' Cg δ₀ Λ ρ R M) : 12 * Λ < (Adoor M : ℝ) * Real.log 2 := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h := hS.gRows
  nlinarith [hΛ, h, hlog2]

/-- **⟦A-3 FROM `MSelect'`⟧** — `s13_g2_jfloor_of_MSelect` at the corrected system.  Reads
field ⟦2⟧ and `1 ≤ M` alone. -/
theorem s13_g2_jfloor_of_MSelect' {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    (hΛ : 1 ≤ Λ) (hS : MSelect' Cg δ₀ Λ ρ R M) :
    4 * Real.log 263 + 48 * Λ ≤ ((doorRowFloor M : ℕ) : ℝ) := by
  have hlog := s13_log263_le_six
  have hdr : (Adoor M : ℝ) ≤ ((doorRowFloor M : ℕ) : ℝ) := by
    have h : Adoor M ≤ doorRowFloor M := by
      rw [doorRowFloor]
      calc Adoor M = 1 * Adoor M := (one_mul _).symm
        _ ≤ M * Adoor M := Nat.mul_le_mul_right _ hM
    exact_mod_cast h
  have h := hS.gRows
  linarith

/-- **⟦THE (A) GROUP AT THE DEMOTED ARM AND `MSelect'`⟧** — `s13_doorGates_of_MSelect` at the
corrected system.  Reads fields ⟦1⟧ and ⟦3⟧ alone. -/
theorem s13_doorGates_of_MSelect' {Cg δ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) (hδ : 0 < δ) (hS : MSelect' Cg δ Λ ρ R M)
    (harm : s13GArm' δ R.Hhi R.ω ≤ R.x) :
    M4DoorGates Cg R M (doorCount R.ω) δ :=
  s13_doorGates_of_arm' hM hδ hS.bfloor harm hS.blockCeil

/-- **⟦A-5 FROM `MSelect'`⟧** (`s13_smallGradeFits_of_MSelect'`) — THE NEW BRIDGE.  Field ⟦4⟧
IS `s13_smallGradeFits`' gate, so the capstone's `hfit` slot

  `∀ H ∈ [H₋, H₊], m4SmallGradeFits (doorRowFloor M) (2·RSanDoorRho ρ) (2·rStrWitness) H`

comes out of `MSelect'` with nothing in between.  This is what `MSelect.winFloor` could NOT
do (the examiner's ⟦D5⟧: the `log 2` coefficient does not reach the `7/10` one, and `winFloor`
carries no `3·G` at all). -/
theorem s13_smallGradeFits_of_MSelect' {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hS : MSelect' Cg δ₀ Λ ρ R M) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      m4SmallGradeFits (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
        (fun H => 2 * rStrWitness H) H :=
  fun H hlo hhi => s13_smallGradeFits hρ0 hρ1 hlo (hS.winFit H hlo hhi)

/-! ## §5 — THE `winFit` DISCHARGE, AND THE SATISFACTION THEOREMS

The gate `(7/10)·j₀ + 3·G ≤ log H` is one inequality in `log H`, and `G` is `loglog`-genre:
at `λ := log H` it reads `252·log λ + 6·log(1 + 12·log λ) + 3·log 9 + 3·log(1/ρ)`.  So the
whole gate is bought by a HALF-window floor at the window's own lower endpoint

  `(7/10)·j₀ + 3·log(1/ρ) ≤ ½·log H₋` ,

whose leftover half pays `3·G` with room to spare: at `√λ ≥ 2000` (the `loglogFloor50`
absorption gives `λ ≥ e^{50}`) the `loglog` charge is under `648·√λ`, against `½λ = ½·(√λ)²`.
At the certified point `(7/10)·j₀ = 1.43·10³²` against `½·log H₋ = 9.5·10³⁴` — the floor
clears with 665× slack, and the `G`-side charge is `6.5·10³`.  Nothing here reads a numeral
the tables do not carry. -/

/-- **⟦THE TRUE WINDOW GATE, DISCHARGED⟧** (`s13_winFit_of_halfWindow`) — field ⟦4⟧ from the
HALF-window floor at `H₋` plus the capstone's absorbed `loglogFloor50`.  The `H`-propagation
is free: `log H₋ ≤ log H` and the `G`-side is priced at `√(log H)`. -/
theorem s13_winFit_of_halfWindow {R : ChowlaRegime} {M : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hhalf : (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
      ≤ Real.log (R.Hlo : ℝ) / 2) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ)
          + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
              + 2 * Real.log (strataResidual H) - Real.log ρ)
        ≤ Real.log (H : ℝ) := by
  intro H hlo _
  have hHlo4 : 4000000 ≤ R.Hlo := R.hHlo_floor
  have hH4 : 4000000 ≤ H := le_trans hHlo4 hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hHloR : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast hHlo4
  have hloR : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo
  have hlogmono : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hloR
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have hlogHbig : (4000000 : ℝ) ≤ Real.log (H : ℝ) := le_trans s13_four_million_le_exp50 hexp50
  set w : ℝ := Real.sqrt (Real.log (H : ℝ)) with hw
  have hw2 : w ^ 2 = Real.log (H : ℝ) := Real.sq_sqrt hlogH0.le
  have hw0 : (0 : ℝ) < w := by rw [hw]; exact Real.sqrt_pos.mpr hlogH0
  have hw2000 : (2000 : ℝ) ≤ w := by nlinarith [hw2, hw0, hlogHbig]
  have hlogw : Real.log w = Real.log (Real.log (H : ℝ)) / 2 := by
    rw [hw]; exact Real.log_sqrt hlogH0.le
  have hlogwle : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hw0
  have hllH : Real.log (Real.log (H : ℝ)) ≤ 2 * w - 2 := by rw [hlogw] at hlogwle; linarith
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hSval : strataResidual H = 1 + 12 * Real.log (Real.log (H : ℝ)) := by
    rw [strataResidual, harcpow, Real.log_pow]; push_cast; ring
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by linarith
  have hS1 : (1 : ℝ) ≤ strataResidual H := by rw [hSval]; linarith
  have hlogS : Real.log (strataResidual H) ≤ strataResidual H - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hSle : strataResidual H - 1 ≤ 24 * w - 24 := by rw [hSval]; linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hlog9 : Real.log 9 ≤ 4 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; linarith
  have hinv : Real.log (1 / ρ) = - Real.log ρ := by rw [one_div, Real.log_inv]
  rw [hinv] at hhalf
  nlinarith [hhalf, hlogmono, hllH, hlogS, hSle, hlog9, hw2, hw2000, hw0]

/-- `8·(4^m)² = 2^{4m+3}` — the headroom field's exponent, normalised. -/
private theorem s13_headroom_pow' (m : ℕ) : 8 * (4 ^ m) ^ 2 = 2 ^ (4 * m + 3) := by
  have h1 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
  have h2 : ((2 : ℕ) ^ (2 * m)) ^ 2 = 2 ^ (4 * m) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [h1, h2, pow_add]
  ring

/-- **⟦`MSelect'` IS NONEMPTY AT THE REGIME'S HEADROOM⟧** (`s13_MSelect'_of_headroom`) — the
mirror of `s13_MSelect_of_headroom`, MINUS the `absorb` discharge (§2 re-homes it at the
socket base).  The three demands that do not read the regime's scale ride as hypotheses; the
ONE structural condition, the demoted block ceiling, is discharged from `hPHheadroom` by the
landed exponent comparison, byte-for-byte. -/
theorem s13_MSelect'_of_headroom {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hbf : 24 * Cg / δ₀ ≤ (M : ℝ))
    (hgr : 242 * Λ ≤ (Adoor M : ℝ))
    (hwf : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ)
          + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
              + 2 * Real.log (strataResidual H) - Real.log ρ)
        ≤ Real.log (H : ℝ))
    (hhead : s13BlockExp M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1) :
    MSelect' Cg δ₀ Λ ρ R M := by
  refine ⟨hbf, hgr, ?_, hwf⟩
  have hfield := R.hPHheadroom
  set m : ℕ := ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ with hm
  have hnat : 4 * s13BlockFloor M ≤ 8 * (4 ^ m) ^ 2 := by
    have h1 : 4 * s13BlockFloor M = 2 ^ (s13BlockExp M + 2) := by
      rw [s13BlockFloor, pow_add]; ring
    rw [h1, s13_headroom_pow']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcast : ((4 * s13BlockFloor M : ℕ) : ℝ) ≤ ((8 * (4 ^ m) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hchain : ((4 * R.ω * s13BlockFloor M : ℕ) : ℝ) ≤ (R.x : ℝ) := by
    push_cast at hcast hfield ⊢
    nlinarith [hcast, hfield, hω0]
  exact_mod_cast hchain

/-- **⟦THE SYSTEM AT THE HALF-WINDOW FLOOR⟧** (`s13_MSelect'_of_halfWindow`) — the same, with
field ⟦4⟧ DISCHARGED from §5's half-window floor rather than carried.  This is the form the
final assembly instantiates: two `M`-lowers (`bfloor`, `gRows`), one `M`-upper stated at the
window's lower endpoint (`hhalf`), and the block ceiling off `hPHheadroom`. -/
theorem s13_MSelect'_of_halfWindow {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hbf : 24 * Cg / δ₀ ≤ (M : ℝ))
    (hgr : 242 * Λ ≤ (Adoor M : ℝ))
    (hhalf : (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
      ≤ Real.log (R.Hlo : ℝ) / 2)
    (hhead : s13BlockExp M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1) :
    MSelect' Cg δ₀ Λ ρ R M :=
  s13_MSelect'_of_headroom hbf hgr (s13_winFit_of_halfWindow hfl hhalf) hhead

/-! ## §GK — the G-lever twin -/

/-- `MSelect' (:359)` at the lever. Only `blockCeil` moves — to the levered block floor. -/
structure MSelect'_gk (K : ℕ) (Cg δ₀ Λ ρ : ℝ) (R : ChowlaRegime) (M : ℕ) : Prop where
  /-- ⟦1⟧ the `b`-floor — `M4DoorGates_gk K.hMδ`.  (`MSelect.bfloor`, verbatim.) -/
  bfloor : 24 * Cg / δ₀ ≤ (M : ℝ)
  /-- ⟦2⟧ the surviving `gRows` demand, `Adoor M ≳ 242·λ₊`.  (`MSelect.gRows`, verbatim.) -/
  gRows : 242 * Λ ≤ (Adoor M : ℝ)
  /-- ⟦3⟧ the DEMOTED arm summand — the `400·(A·G·M)²` block ceiling against `x`.
  (`MSelect.blockCeil`, verbatim.) -/
  blockCeil : 4 * R.ω * s13BlockFloor_gk K M ≤ R.x
  /-- ⟦4⟧ **THE TRUE WINDOW GATE** — `s13_smallGradeFits`' `hfit` slot, at every admissible
  window length: `(7/10)·doorRowFloor M + 3·G ≤ log H` with
  `G = log 9 + 84·loglog H + 2·log(strataResidual H) − log ρ`. -/
  winFit : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
    (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ)
        + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
            + 2 * Real.log (strataResidual H) - Real.log ρ)
      ≤ Real.log (H : ℝ)

/-! ## §4 — THE CONSUMER BRIDGES, RE-ROUTED AT `MSelect'_gk K`

The three landed consumers read only `gRows`/`bfloor`/`blockCeil`, so each re-routes with its
landed proof unchanged.  The fourth bridge is new: it is what `winFit` was minted for. -/

/-- `s13_gate8_of_MSelect' (:383)` at the lever. -/
theorem s13_gate8_of_MSelect'_gk (K : ℕ) {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ} (hΛ : 0 < Λ)
    (hS : MSelect'_gk K Cg δ₀ Λ ρ R M) : 12 * Λ < (Adoor M : ℝ) * Real.log 2 := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h := hS.gRows
  nlinarith [hΛ, h, hlog2]

/-- `s13_g2_jfloor_of_MSelect' (:391)` at the lever. -/
theorem s13_g2_jfloor_of_MSelect'_gk (K : ℕ) {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    (hΛ : 1 ≤ Λ) (hS : MSelect'_gk K Cg δ₀ Λ ρ R M) :
    4 * Real.log 263 + 48 * Λ ≤ ((doorRowFloor M : ℕ) : ℝ) := by
  have hlog := s13_log263_le_six
  have hdr : (Adoor M : ℝ) ≤ ((doorRowFloor M : ℕ) : ℝ) := by
    have h : Adoor M ≤ doorRowFloor M := by
      rw [doorRowFloor]
      calc Adoor M = 1 * Adoor M := (one_mul _).symm
        _ ≤ M * Adoor M := Nat.mul_le_mul_right _ hM
    exact_mod_cast h
  have h := hS.gRows
  linarith

/-- `s13_doorGates_of_MSelect' (:406)` at the lever. -/
theorem s13_doorGates_of_MSelect'_gk (K : ℕ) {Cg δ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) (hδ : 0 < δ) (hS : MSelect'_gk K Cg δ Λ ρ R M)
    (harm : s13GArm' δ R.Hhi R.ω ≤ R.x) :
    M4DoorGates_gk K Cg R M (doorCount R.ω) δ :=
  s13_doorGates_of_arm'_gk K hM hδ hS.bfloor harm hS.blockCeil

/-- `s13_smallGradeFits_of_MSelect' (:420)` at the lever. -/
theorem s13_smallGradeFits_of_MSelect'_gk (K : ℕ) {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hS : MSelect'_gk K Cg δ₀ Λ ρ R M) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      m4SmallGradeFits (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
        (fun H => 2 * rStrWitness H) H :=
  fun H hlo hhi => s13_smallGradeFits hρ0 hρ1 hlo (hS.winFit H hlo hhi)

/-! ## §5 — THE `winFit` DISCHARGE, AND THE SATISFACTION THEOREMS

The gate `(7/10)·j₀ + 3·G ≤ log H` is one inequality in `log H`, and `G` is `loglog`-genre:
at `λ := log H` it reads `252·log λ + 6·log(1 + 12·log λ) + 3·log 9 + 3·log(1/ρ)`.  So the
whole gate is bought by a HALF-window floor at the window's own lower endpoint

  `(7/10)·j₀ + 3·log(1/ρ) ≤ ½·log H₋` ,

whose leftover half pays `3·G` with room to spare: at `√λ ≥ 2000` (the `loglogFloor50`
absorption gives `λ ≥ e^{50}`) the `loglog` charge is under `648·√λ`, against `½λ = ½·(√λ)²`.
At the certified point `(7/10)·j₀ = 1.43·10³²` against `½·log H₋ = 9.5·10³⁴` — the floor
clears with 665× slack, and the `G`-side charge is `6.5·10³`.  Nothing here reads a numeral
the tables do not carry. -/

/-- `s13_MSelect'_of_headroom (:507)` at the lever. -/
theorem s13_MSelect'_of_headroom_gk (K : ℕ) {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hbf : 24 * Cg / δ₀ ≤ (M : ℝ))
    (hgr : 242 * Λ ≤ (Adoor M : ℝ))
    (hwf : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ)
          + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
              + 2 * Real.log (strataResidual H) - Real.log ρ)
        ≤ Real.log (H : ℝ))
    (hhead : s13BlockExp_gk K M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1) :
    MSelect'_gk K Cg δ₀ Λ ρ R M := by
  refine ⟨hbf, hgr, ?_, hwf⟩
  have hfield := R.hPHheadroom
  set m : ℕ := ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ with hm
  have hnat : 4 * s13BlockFloor_gk K M ≤ 8 * (4 ^ m) ^ 2 := by
    have h1 : 4 * s13BlockFloor_gk K M = 2 ^ (s13BlockExp_gk K M + 2) := by
      rw [s13BlockFloor_gk, pow_add]; ring
    rw [h1, s13_headroom_pow']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcast : ((4 * s13BlockFloor_gk K M : ℕ) : ℝ) ≤ ((8 * (4 ^ m) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hchain : ((4 * R.ω * s13BlockFloor_gk K M : ℕ) : ℝ) ≤ (R.x : ℝ) := by
    push_cast at hcast hfield ⊢
    nlinarith [hcast, hfield, hω0]
  exact_mod_cast hchain

/-- `s13_MSelect'_of_halfWindow (:537)` at the lever. -/
theorem s13_MSelect'_of_halfWindow_gk (K : ℕ) {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hbf : 24 * Cg / δ₀ ≤ (M : ℝ))
    (hgr : 242 * Λ ≤ (Adoor M : ℝ))
    (hhalf : (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
      ≤ Real.log (R.Hlo : ℝ) / 2)
    (hhead : s13BlockExp_gk K M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1) :
    MSelect'_gk K Cg δ₀ Λ ρ R M :=
  s13_MSelect'_of_headroom_gk K hbf hgr (s13_winFit_of_halfWindow hfl hhalf) hhead

-- #audit (temporary)

end Salt.MR
