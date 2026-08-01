/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S13FramesA
import Salt.MR.S13FramesB
import Salt.MR.S13MSelect2
import Salt.MR.M4AssemblyFrames
import Salt.MR.FrameWitness
import Salt.MR.USetPins
import Salt.MR.USetThinTL
import Salt.MR.CofactorDist
import Salt.MR.TypicalDensity

/-!
# ⟦CAPGATE — THE GRID WAVE⟧ `S13CapGatePerBlock`'s band/grid fields, supplied

PURELY ADDITIVE: no landed declaration is touched.  This file supplies EIGHTEEN of the
thirty-seven fields of `S13FramesB.S13CapGatePerBlock` — the scale floor, the band pins, the
seven grid rows, the `cs`-gate, and the tail band's two side conditions — at the socket's own
working point, and collects them in one bundling lemma `s13CapGrid_all`.

## ⟦THE WORKING POINT⟧

`SocketBase R M H L q j A s` together with the capstone's absorbed `loglogFloor50 ≤ R.Hlo`
gives (`S13MSelect2` §2)

  `μ := log X_d ≥ √H`  and  `Λ := loglog X_d ≥ ½·log H ≥ ½·e^{50} = 2.59·10²¹` ,

at the wire's own base `X_d = A + s`.  EVERY numeric field below closes on that pair; the
band pins are the canonical `P := ⌈P₈₃ X_d θ₂₉₃⌉₊`, `Q := ⌊Q₈₃ X_d⌋₊`.

## ⟦THE T-FLOOR — READ THIS BEFORE TOUCHING `kappa30`/`BT`/`BT10`⟧

`TannGate` is NOT the binding `T`-floor.  `SocketBase`'s `j ≤ Nat.log 2 L` and `L ≤ H` give
`2^j ≤ H` (§2's `s13CapGrid_twoj_le_H`), so the gate family's OWN lower binder
`hTlo : X_d/2^j ≤ T` forces

  `log T_ann ≥ μ − log H` ,   with `log H ≤ √H ≤ μ` and in fact `log H ≤ 2Λ` ,

which is what the `30·log Q_base` charge is priced against.  Reading the floor off `TannGate`
(`T_ann ≥ exp(30√μ)`) instead would KILL the `kappa30` row.

## ⟦THE SECTIONS⟧

* §0 — the numerals (`e^{50}`, `log x ≤ √x`, the `gate` polynomial, the `κ`-polynomial).
* §1 — the socket working point: `μ ≥ √H`, `Λ ≥ 10²¹`, `2^j ≤ H`, `log H ≤ μ`.
* §2 — the band pins `P`, `Q` and their five fields.
* §3 — the grid rows `Hj`, `B3`, `BT`, `kappa30`, `BT10`, `WL`.
* §4 — the `cs`-gate.
* §5 — the tail band's side conditions `Q_hundred` and `band_product`.
* §6 — the bundling lemma `s13CapGrid_all`.
-/

open Salt.Entropy.Chowla

noncomputable section

open scoped BigOperators

namespace Salt.MR

/-! ## §0 — THE NUMERALS -/

/-- `2·10²¹ ≤ e^{50}` (true value `5.1847·10²¹`).  The one numeral the whole file spends:
it is what turns `S13MSelect2`'s sharp `Λ ≥ ½·log H ≥ ½·e^{50}` into the working `Λ ≥ 10²¹`. -/
theorem capgrid_exp50_lo : (2 : ℝ) * 10 ^ (21 : ℕ) ≤ Real.exp 50 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h50 : Real.exp 50 = (Real.exp 1) ^ (50 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : (2.7182818283 : ℝ) ^ (50 : ℕ) ≤ (Real.exp 1) ^ (50 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h1.le 50
  have hn : (2 : ℝ) * 10 ^ (21 : ℕ) ≤ (2.7182818283 : ℝ) ^ (50 : ℕ) := by norm_num
  rw [h50]; linarith

/-- **⟦THE FOURTH-ROOT PRICING⟧** `log x ≤ √x` at every `x ≥ 1`.  `log x = 4·log x^{1/4} ≤
4(x^{1/4} − 1)` and `√x − 4x^{1/4} + 4 = (x^{1/4} − 2)² ≥ 0`. -/
theorem capgrid_log_le_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := by linarith
  set r : ℝ := Real.sqrt x with hr
  have hr2 : r ^ 2 = x := Real.sq_sqrt hx0.le
  have hr0 : (0 : ℝ) < r := by rw [hr]; exact Real.sqrt_pos.mpr hx0
  set w : ℝ := Real.sqrt r with hw
  have hw2 : w ^ 2 = r := Real.sq_sqrt hr0.le
  have hw0 : (0 : ℝ) < w := by rw [hw]; exact Real.sqrt_pos.mpr hr0
  have hlr : Real.log r = Real.log x / 2 := by rw [hr]; exact Real.log_sqrt hx0.le
  have hlw : Real.log w = Real.log r / 2 := by rw [hw]; exact Real.log_sqrt hr0.le
  have hwle : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hw0
  have : Real.log x ≤ 4 * w - 4 := by rw [hlr] at hlw; linarith
  nlinarith [hw2, sq_nonneg (w - 2)]

/-- **⟦P1c, PORTED⟧ THE `gate` NUMERIC** (`capgate_gate_numeric`) — the `Λ`-polynomial the
`gate` field carries is swallowed by the margin exponent already at `Λ ≥ 7800`.  Certified
margin at the floor: `~6600×`; at the socket base `Λ ≥ 2.6·10²¹`. -/
theorem capgrid_gate_numeric {Λ : ℝ} (hΛ : 7800 ≤ Λ) :
    420 * (11 / 10 * Λ) ^ 5 ≤ Real.exp (68 / 1000 * Λ) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  set y : ℝ := 68 / 1000 * Λ / 16 with hy
  have hy0 : (0 : ℝ) ≤ y := by rw [hy]; positivity
  have hye : y ≤ Real.exp y := by have := Real.add_one_le_exp y; linarith
  have hsplit : Real.exp (68 / 1000 * Λ) = (Real.exp y) ^ (16 : ℕ) := by
    rw [← Real.exp_nat_mul, hy]; ring_nf
  have hpow : y ^ (16 : ℕ) ≤ (Real.exp y) ^ (16 : ℕ) := pow_le_pow_left₀ hy0 hye 16
  rw [hsplit]
  refine le_trans ?_ hpow
  have hyv : y ^ (16 : ℕ) = ((17 : ℝ) / 4000) ^ (16 : ℕ) * (Λ ^ (11 : ℕ) * Λ ^ (5 : ℕ)) := by
    rw [hy]; ring
  have h11 : (7800 : ℝ) ^ (11 : ℕ) ≤ Λ ^ (11 : ℕ) := pow_le_pow_left₀ (by norm_num) hΛ 11
  have hc : 420 * ((11 : ℝ) / 10) ^ (5 : ℕ)
      ≤ ((17 : ℝ) / 4000) ^ (16 : ℕ) * (7800 : ℝ) ^ (11 : ℕ) := by norm_num
  have h5 : (0 : ℝ) < Λ ^ (5 : ℕ) := by positivity
  have hcpos : (0 : ℝ) < ((17 : ℝ) / 4000) ^ (16 : ℕ) := by positivity
  rw [hyv]
  have hstep : 420 * ((11 : ℝ) / 10) ^ (5 : ℕ)
      ≤ ((17 : ℝ) / 4000) ^ (16 : ℕ) * Λ ^ (11 : ℕ) :=
    le_trans hc (by nlinarith [h11, hcpos])
  calc 420 * (11 / 10 * Λ) ^ (5 : ℕ) = (420 * ((11 : ℝ) / 10) ^ (5 : ℕ)) * Λ ^ (5 : ℕ) := by
        ring
    _ ≤ (((17 : ℝ) / 4000) ^ (16 : ℕ) * Λ ^ (11 : ℕ)) * Λ ^ (5 : ℕ) :=
        mul_le_mul_of_nonneg_right hstep h5.le
    _ = ((17 : ℝ) / 4000) ^ (16 : ℕ) * (Λ ^ (11 : ℕ) * Λ ^ (5 : ℕ)) := by ring

/-- **⟦P3b, PORTED IN μ-FORM⟧ THE `κ`-POLYNOMIAL** — `30·(μ/Λ) + 2Λ ≤ μ` at `Λ = log μ ≥ 100`.
This is the `kappa30` row at the BAND TOP (`log Q ≤ μ/Λ`) against the `hTlo` floor
`log T_ann ≥ μ − 2Λ`.  At the socket base the true margin is `Λ/30`. -/
theorem capgrid_kappa_numeric {μ : ℝ} (hμ : 2000 ≤ μ) (hΛ : 100 ≤ Real.log μ) :
    30 * (μ / Real.log μ) + 2 * Real.log μ ≤ μ := by
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hsq : Real.log μ ≤ Real.sqrt μ := capgrid_log_le_sqrt (by linarith)
  have hs2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ0.le
  have hs0 : (0 : ℝ) < Real.sqrt μ := Real.sqrt_pos.mpr hμ0
  have hs40 : (40 : ℝ) ≤ Real.sqrt μ := by nlinarith [hs2, hs0]
  have hdiv : 30 * (μ / Real.log μ) ≤ (3 / 10) * μ := by
    rw [mul_div_assoc', div_le_iff₀ hΛ0]
    nlinarith [hμ0, hΛ]
  nlinarith [hdiv, hsq, hs2, hs40, hs0]

/-- `μ ≥ Λ²` at `Λ = log μ` — the `√`-pricing squared.  Used wherever a `Λ`-polynomial must be
swallowed by `μ` itself (the band-product page). -/
theorem capgrid_mu_ge_sq {μ : ℝ} (hμ : 1 ≤ μ) : (Real.log μ) ^ 2 ≤ μ := by
  have hs : Real.log μ ≤ Real.sqrt μ := capgrid_log_le_sqrt hμ
  have hs2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt (by linarith)
  have hl0 : (0 : ℝ) ≤ Real.log μ := Real.log_nonneg hμ
  nlinarith [hs, hs2, hl0]

/-! ## §1 — THE SOCKET WORKING POINT

`μ := log X_d ≥ √H`, `Λ := loglog X_d ≥ ½·log H ≥ 10²¹`, `log H ≤ μ`, and the `T`-floor
stone `2^j ≤ H`.  Everything downstream reads only these four lines. -/

/-- **⟦THE `T`-FLOOR STONE⟧** (`P3a`, ported) — `2^j ≤ H` from `SocketBase`'s window fields
`j ≤ Nat.log 2 L` and `L ≤ H`.  This is what turns the gate family's `hTlo` into
`T_ann ≥ X_d/H`, and it is the reason `TannGate` is NOT the binding `T`-floor. -/
theorem s13CapGrid_twoj_le_H {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBase R M H L q j A s) : 2 ^ j ≤ H := by
  have hjL : j ≤ Nat.log 2 L := hb.2.2.2.2.2.1
  have hLH : L ≤ H := hb.2.2.1
  have hH : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · subst hL0
    have hj : j = 0 := by simpa using hjL
    subst hj
    simpa using (by omega : 1 ≤ H)
  · exact le_trans (le_trans (Nat.pow_le_pow_right (by norm_num) hjL)
      (Nat.pow_log_le_self 2 (by omega))) hLH

/-- `√H ≤ μ` at the wire's base `X_d = A + s` — `S13MSelect2.s13_socketBase_logA_ge_sqrt`
transported up the shift. -/
theorem s13CapGrid_mu_lo {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    Real.sqrt (H : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hmono : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    Real.log_le_log hA0 (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) s])
  exact le_trans (s13_socketBase_logA_ge_sqrt hfl hb) hmono

/-- `2000 ≤ μ` — the crudest reading of `√H ≥ √(4·10⁶)`. -/
theorem s13CapGrid_mu_2000 {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hs2 : Real.sqrt (H : ℝ) ^ 2 = (H : ℝ) := Real.sq_sqrt (by positivity)
  have hs0 : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have : (2000 : ℝ) ≤ Real.sqrt (H : ℝ) := by nlinarith [hs2, hs0, hHR]
  exact le_trans this (s13CapGrid_mu_lo hfl hb)

/-- `log H ≤ μ` — §0's `log x ≤ √x` against `√H ≤ μ`.  This is what makes the socket's own
modulus ledger `q ≤ (log H)^{12}` a `μ`-side gate. -/
theorem s13CapGrid_logH_le_mu {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    Real.log (H : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  exact le_trans (capgrid_log_le_sqrt (by linarith)) (s13CapGrid_mu_lo hfl hb)

/-- `½·log H ≤ Λ` at the wire's base — `S13MSelect2.s13_socketBase_loglogA_sharp` transported
up the shift. -/
theorem s13CapGrid_Lambda_sharp {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    Real.log (H : ℝ) / 2 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hsq := s13_socketBase_logA_ge_sqrt hfl hb
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hs2 : Real.sqrt (H : ℝ) ^ 2 = (H : ℝ) := Real.sq_sqrt (by positivity)
  have hs0 : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have h2000 : (2000 : ℝ) ≤ Real.sqrt (H : ℝ) := by nlinarith [hs2, hs0, hHR]
  have hlogA0 : (0 : ℝ) < Real.log (A : ℝ) := by linarith
  have hmono : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    Real.log_le_log hA0 (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) s])
  exact le_trans (s13_socketBase_loglogA_sharp hfl hb) (Real.log_le_log hlogA0 hmono)

/-- **⟦THE `Λ`-FLOOR⟧** `Λ = loglog X_d ≥ 10²¹`.  From `Λ ≥ ½·log H` and the capstone's
absorbed `loglogFloor50` (`log H ≥ e^{50} = 5.18·10²¹`). -/
theorem s13CapGrid_Lambda_lo {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have := s13CapGrid_Lambda_sharp hfl hb
  linarith [capgrid_exp50_lo]

/-! ## §2 — THE BAND PINS AND THE FIVE PIN FIELDS

`P := ⌈P₈₃ X_d θ₂₉₃⌉₊`, `Q := ⌊Q₈₃ X_d⌋₊` — the §8.3 window's own endpoints, rounded the
way each of `P_low` (`P₈₃ ≤ P`) and `Q_high` (`Q ≤ Q₈₃`) needs.

⟦THE ONE DRIFT vs the brief⟧ `P_le_Q` is NOT `CofactorDist.pin_P83_le_Q83_293` wired
directly: `⌈a⌉₊ ≤ ⌊b⌋₊` needs a UNIT gap `a + 1 ≤ b`, not `a ≤ b`.  The gap is supplied at
the working point by `e^{θ₂₉₃Λ} ≥ 2Λ` (`capgrid_exp_theta_gap`) — sixteen orders of slack —
so the rounding costs nothing. -/

/-- The band's LOWER pin `P := ⌈P₈₃ X_d θ₂₉₃⌉₊`. -/
def s13BandP (Nd : ℕ) : ℕ := ⌈P83 ((Nd : ℕ) : ℝ) theta293⌉₊

/-- The band's UPPER pin `Q := ⌊Q₈₃ X_d⌋₊`. -/
def s13BandQ (Nd : ℕ) : ℕ := ⌊Q83 ((Nd : ℕ) : ℝ)⌋₊

/-- **⟦THE PIN SEPARATION⟧** `2Λ ≤ e^{θ₂₉₃·Λ}` at `Λ ≥ 10²¹`.  `θ₂₉₃Λ ≥ Λ/500 ≥ 2·10¹⁸` and
`e^x ≥ x²/4`, so the true margin is `10¹⁵×`. -/
theorem capgrid_exp_theta_gap {Λ : ℝ} (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Λ) :
    2 * Λ ≤ Real.exp (theta293 * Λ) := by
  have hθ : (1 : ℝ) / 500 ≤ theta293 := c0_le_theta293
  have hΛ0 : (0 : ℝ) < Λ := by
    have : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    linarith
  set x : ℝ := theta293 * Λ with hx
  have hxlo : Λ / 500 ≤ x := by rw [hx]; nlinarith
  have hxbig : (2 : ℝ) * 10 ^ (18 : ℕ) ≤ x := by
    have : (10 : ℝ) ^ (21 : ℕ) / 500 ≤ Λ / 500 := by linarith
    have h2 : (2 : ℝ) * 10 ^ (18 : ℕ) ≤ (10 : ℝ) ^ (21 : ℕ) / 500 := by norm_num
    linarith
  have hx0 : (0 : ℝ) ≤ x / 2 := by linarith
  have hhalf : x / 2 ≤ Real.exp (x / 2) := by linarith [Real.add_one_le_exp (x / 2)]
  have hsq : Real.exp x = (Real.exp (x / 2)) ^ (2 : ℕ) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hlow : x ^ 2 / 4 ≤ Real.exp x := by rw [hsq]; nlinarith [hhalf, hx0]
  have hfin : 2 * Λ ≤ x ^ 2 / 4 := by nlinarith [hxbig, hxlo, hΛ0]
  linarith

/-- `P₈₃ X_d θ₂₉₃ ≤ P` — ⟦FIELD `P_low`⟧, `Nat.le_ceil`. -/
theorem s13CapGrid_P_low (Nd : ℕ) :
    P83 ((Nd : ℕ) : ℝ) theta293 ≤ ((s13BandP Nd : ℕ) : ℝ) := Nat.le_ceil _

/-- `Q ≤ Q₈₃ X_d` — ⟦FIELD `Q_high`⟧, `Nat.floor_le`. -/
theorem s13CapGrid_Q_high (Nd : ℕ) :
    ((s13BandQ Nd : ℕ) : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ) :=
  Nat.floor_le (le_of_lt (Real.exp_pos _))

/-- `0 < Q` — ⟦FIELD `Q_pos`⟧: `Q₈₃ = e^{μ/Λ} ≥ 1`. -/
theorem s13CapGrid_Q_pos {Nd : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ)) :
    0 < s13BandQ Nd := by
  have hΛ0 : (0 : ℝ) < Real.log (Real.log ((Nd : ℕ) : ℝ)) :=
    Real.log_pos (by linarith)
  have h1 : (1 : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ) := by
    rw [Q83, show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_le_exp.mpr (by positivity)
  have : 1 ≤ s13BandQ Nd := Nat.le_floor (by exact_mod_cast h1)
  omega

/-- `μ^{1−θ₂₉₃} ≤ log P` — the lower pin in `log` form. -/
theorem s13CapGrid_logP_ge (Nd : ℕ) :
    (Real.log ((Nd : ℕ) : ℝ)) ^ (1 - theta293) ≤ Real.log ((s13BandP Nd : ℕ) : ℝ) := by
  have h := Real.log_le_log (Real.exp_pos ((Real.log ((Nd : ℕ) : ℝ)) ^ (1 - theta293)))
    (by simpa [P83] using s13CapGrid_P_low Nd)
  rwa [Real.log_exp] at h

/-- `log Q ≤ μ/Λ` — the upper pin in `log` form. -/
theorem s13CapGrid_logQ_le {Nd : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ)) :
    Real.log ((s13BandQ Nd : ℕ) : ℝ)
      ≤ Real.log ((Nd : ℕ) : ℝ) / Real.log (Real.log ((Nd : ℕ) : ℝ)) := by
  have hQ : 0 < s13BandQ Nd := s13CapGrid_Q_pos hμ
  have hQ0 : (0 : ℝ) < ((s13BandQ Nd : ℕ) : ℝ) := by exact_mod_cast hQ
  have h := Real.log_le_log hQ0 (s13CapGrid_Q_high Nd)
  rwa [Q83, Real.log_exp] at h

/-- **⟦FIELD `P_le_Q`⟧** `P ≤ Q`.  `P₈₃ + 1 ≤ Q₈₃` at the working point: `P₈₃ ≥ 1` so
`P₈₃ + 1 ≤ 2P₈₃`, and `log 2 + μ·e^{−θ₂₉₃Λ} ≤ μ/Λ` by the pin separation. -/
theorem s13CapGrid_P_le_Q {Nd : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ))) :
    s13BandP Nd ≤ s13BandQ Nd := by
  have hNd0 : (0 : ℝ) < ((Nd : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos Nd with h | h
    · exfalso; rw [h] at hμ; simp at hμ; linarith
    · exact_mod_cast h
  set μ : ℝ := Real.log ((Nd : ℕ) : ℝ) with hμdef
  set Λ : ℝ := Real.log μ with hΛdef
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Λ := by
    have : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    linarith
  have hexpμ : Real.exp Λ = μ := Real.exp_log hμ0
  -- `μ^{1−θ} = μ·e^{−θΛ}`
  have hsplit : μ ^ (1 - theta293) = μ * Real.exp (-(theta293 * Λ)) := by
    rw [Real.rpow_def_of_pos hμ0, ← hΛdef,
      show Λ * (1 - theta293) = Λ + -(theta293 * Λ) by ring, Real.exp_add, hexpμ]
  -- `e^{−θΛ} ≤ 1/(2Λ)`
  have hgap := capgrid_exp_theta_gap hΛ
  have hepos : (0 : ℝ) < Real.exp (theta293 * Λ) := Real.exp_pos _
  have hinv : Real.exp (-(theta293 * Λ)) ≤ 1 / (2 * Λ) := by
    rw [Real.exp_neg, inv_le_comm₀ hepos (by positivity)]
    rw [one_div, inv_inv] at *
    linarith [hgap]
  have hΛsq : Λ ≤ Real.sqrt μ := by
    rw [hΛdef]; exact capgrid_log_le_sqrt (by linarith)
  have hs2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ0.le
  have hs0 : (0 : ℝ) < Real.sqrt μ := Real.sqrt_pos.mpr hμ0
  have hs40 : (40 : ℝ) ≤ Real.sqrt μ := by nlinarith [hs2, hs0]
  have hμΛ : 4 * Λ ≤ μ := by nlinarith [hΛsq, hs2, hs40, hs0]
  -- the key real gap `log 2 + μ^{1−θ} ≤ μ/Λ`
  have hkey : Real.log 2 + μ ^ (1 - theta293) ≤ μ / Λ := by
    have h1 : μ * Real.exp (-(theta293 * Λ)) ≤ μ * (1 / (2 * Λ)) :=
      mul_le_mul_of_nonneg_left hinv hμ0.le
    have h2 : μ * (1 / (2 * Λ)) = (μ / Λ) / 2 := by field_simp
    have hl2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have h3 : (1 : ℝ) ≤ (μ / Λ) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_div_iff₀ hΛ0]; linarith
    rw [hsplit]
    linarith [h1, h2.le, h2.ge, h3]
  -- lift to `P₈₃ + 1 ≤ Q₈₃`
  have hP1 : (1 : ℝ) ≤ P83 ((Nd : ℕ) : ℝ) theta293 := by
    rw [P83, show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_le_exp.mpr (Real.rpow_nonneg hμ0.le _)
  have hPQ : P83 ((Nd : ℕ) : ℝ) theta293 + 1 ≤ Q83 ((Nd : ℕ) : ℝ) := by
    have h2P : P83 ((Nd : ℕ) : ℝ) theta293 + 1 ≤ 2 * P83 ((Nd : ℕ) : ℝ) theta293 := by
      linarith
    have hstep : 2 * P83 ((Nd : ℕ) : ℝ) theta293 ≤ Q83 ((Nd : ℕ) : ℝ) := by
      rw [P83, Q83, ← hμdef, ← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by rw [← hΛdef]; linarith [hkey])
    linarith
  refine Nat.le_floor ?_
  have hc : ((s13BandP Nd : ℕ) : ℝ) < P83 ((Nd : ℕ) : ℝ) theta293 + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  linarith

/-! ### §2b — the four scalar pin fields -/

/-- **⟦FIELD `logX_eight`⟧** `8 ≤ log X_d`. -/
theorem s13CapGrid_logX_eight {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    8 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  linarith [s13CapGrid_mu_2000 hfl hb]

/-- **⟦FIELD `H83_two`⟧** `2 ≤ H₈₃ X_d θ₂₉₃ = μ^{θ₂₉₃}`.  `θ₂₉₃Λ ≥ Λ/500 ≥ 2·10¹⁸`. -/
theorem s13CapGrid_H83_two {Nd : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ))) :
    2 ≤ H83 ((Nd : ℕ) : ℝ) theta293 := by
  set μ : ℝ := Real.log ((Nd : ℕ) : ℝ) with hμdef
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hθ : (1 : ℝ) / 500 ≤ theta293 := c0_le_theta293
  have hΛ0 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hone : (1 : ℝ) ≤ Real.log μ * theta293 := by nlinarith
  have := Real.add_one_le_exp (Real.log μ * theta293)
  rw [H83, ← hμdef, Real.rpow_def_of_pos hμ0]
  linarith

/-- **⟦FIELD `q_logX`⟧** `q ≤ (log X_d)^{12}`.  The socket's OWN modulus ledger
`q ≤ arcDen 12 H = (log H)^{12}`, against `log H ≤ μ`. -/
theorem s13CapGrid_q_logX {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    (q : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ 12 := by
  have hq := hb.2.2.2.2.1
  have harc : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg (by linarith)
  have hstep : Real.log (H : ℝ) ^ (12 : ℕ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (12 : ℕ) :=
    pow_le_pow_left₀ hlogH0 (s13CapGrid_logH_le_mu hfl hb) 12
  rw [harc] at hq
  linarith

/-- **⟦FIELD `logqT_L`⟧** `log(q·T_ann) ≤ Lr = μ^{11/10}`.  `log q ≤ 12Λ` off `q_logX`,
`log T_ann ≤ μ` off the family's own `2T ≤ X_d`, and `μ^{1/10} = e^{Λ/10} ≥ 2`. -/
theorem s13CapGrid_logqT_L {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T)
    (hThi : 2 * T ≤ (((A + s : ℕ)) : ℝ)) :
    Real.log ((q : ℝ) * (2 * T)) ≤ s13Lr (A + s) := by
  set Nd : ℕ := A + s with hNd
  set μ : ℝ := Real.log ((Nd : ℕ) : ℝ) with hμdef
  have hμ2000 : (2000 : ℝ) ≤ μ := s13CapGrid_mu_2000 hfl hb
  have hΛ21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log μ := s13CapGrid_Lambda_lo hfl hb
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hNd1 : 1 ≤ Nd := by omega
  have hNdR : (1 : ℝ) ≤ ((Nd : ℕ) : ℝ) := by exact_mod_cast hNd1
  have hq1 : 1 ≤ q := hb.2.2.2.1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hpow0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hT0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) := by positivity
    linarith
  -- `log q ≤ 12Λ`
  have hqlog : Real.log (q : ℝ) ≤ 12 * Real.log μ := by
    have hq12 : (q : ℝ) ≤ μ ^ (12 : ℕ) := s13CapGrid_q_logX hfl hb
    have := Real.log_le_log (by linarith) hq12
    rwa [Real.log_pow] at this
    -- `Real.log_pow : log (x ^ n) = n * log x`
  have hTlog : Real.log (2 * T) ≤ μ := Real.log_le_log hT0 hThi
  have hsum : Real.log ((q : ℝ) * (2 * T)) ≤ 12 * Real.log μ + μ := by
    rw [Real.log_mul (by linarith) (by linarith)]
    linarith
  -- `2μ ≤ μ^{11/10}`
  have hΛ0 : (0 : ℝ) < Real.log μ := by
    have : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    linarith
  have htwo : (2 : ℝ) ≤ μ ^ ((1 : ℝ) / 10) := by
    have hone : (1 : ℝ) ≤ Real.log μ * (1 / 10) := by nlinarith [hΛ21]
    have := Real.add_one_le_exp (Real.log μ * (1 / 10))
    rw [Real.rpow_def_of_pos hμ0]
    linarith
  have hLr : s13Lr Nd = μ * μ ^ ((1 : ℝ) / 10) := by
    rw [s13Lr, ← hμdef, ← Real.rpow_one_add' hμ0.le (by norm_num)]
    norm_num
  have h2μ : 2 * μ ≤ s13Lr Nd := by
    rw [hLr]; nlinarith [htwo, hμ0]
  -- `12Λ ≤ μ`
  have hΛsq : Real.log μ ≤ Real.sqrt μ := capgrid_log_le_sqrt (by linarith)
  have hs2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ0.le
  have hs0 : (0 : ℝ) < Real.sqrt μ := Real.sqrt_pos.mpr hμ0
  have hs40 : (40 : ℝ) ≤ Real.sqrt μ := by nlinarith [hs2, hs0]
  have h12 : 12 * Real.log μ ≤ μ := by nlinarith [hΛsq, hs2, hs40, hs0]
  linarith

/-! ## §3 — THE GRID ROWS

The six rows quantified over `i ∈ ramI (H₈₃ X_d θ₂₉₃) P Q`.  All six run through the
`FrameWitness` SANDWICH `P ≤ ramQbase ≤ Q`: `B3` transports UP from `P`, and
`BT`/`kappa30`/`BT10`/`WL` transport DOWN from `Q`. -/

/-- `2 ≤ μ^{1−θ₂₉₃}` — the exponent floor behind `log P ≥ 2` and `3 ≤ P`. -/
theorem s13CapGrid_pow_two {Nd : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ))) :
    2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (1 - theta293) := by
  set μ : ℝ := Real.log ((Nd : ℕ) : ℝ) with hμdef
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hθ : theta293 ≤ 1 / 100 := frames_theta293_le
  have hΛ0 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hone : (1 : ℝ) ≤ Real.log μ * (1 - theta293) := by nlinarith
  have := Real.add_one_le_exp (Real.log μ * (1 - theta293))
  rw [Real.rpow_def_of_pos hμ0]
  linarith

/-- `2 ≤ log P` at the lower pin. -/
theorem s13CapGrid_logP_two {Nd : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ))) :
    2 ≤ Real.log ((s13BandP Nd : ℕ) : ℝ) :=
  le_trans (s13CapGrid_pow_two hμ hΛ) (s13CapGrid_logP_ge Nd)

/-- `3 ≤ P` at the lower pin (`P ≥ P₈₃ ≥ e² > 7`). -/
theorem s13CapGrid_P_three {Nd : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ))) :
    3 ≤ s13BandP Nd := by
  have h2 := s13CapGrid_pow_two hμ hΛ
  have hexp : Real.exp 2 ≤ P83 ((Nd : ℕ) : ℝ) theta293 := by
    rw [P83]; exact Real.exp_le_exp.mpr h2
  have h7 : (7 : ℝ) ≤ Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have he : Real.exp 2 = (Real.exp 1) ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 : ℝ)]
  have hR : (3 : ℝ) ≤ ((s13BandP Nd : ℕ) : ℝ) := by
    have := s13CapGrid_P_low Nd; linarith
  exact_mod_cast hR

/-- **⟦THE `hTlo` FLOOR, IN LOGS⟧** `log T_ann ≥ μ − 2Λ`.  The family's own lower binder
`X_d/2^j ≤ T` against `2^j ≤ H` and `log H ≤ 2Λ`.  ⟦NOT `TannGate`⟧. -/
theorem s13CapGrid_logTann_lo {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    Real.log (((A + s : ℕ)) : ℝ) - 2 * Real.log (Real.log (((A + s : ℕ)) : ℝ))
      ≤ Real.log (2 * T) := by
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hNd1 : (1 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    have : 1 ≤ A + s := by omega
    exact_mod_cast this
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hpow0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have h2j : ((2 ^ j : ℕ) : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast s13CapGrid_twoj_le_H hb
  have hdiv : (((A + s : ℕ)) : ℝ) / (H : ℝ) ≤ (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left (by linarith) hpow0 h2j
  have hdiv0 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) / (H : ℝ) := by positivity
  have hle : (((A + s : ℕ)) : ℝ) / (H : ℝ) ≤ 2 * T := by linarith
  have hlog := Real.log_le_log hdiv0 hle
  rw [Real.log_div (by linarith) (by linarith)] at hlog
  have hLam := s13CapGrid_Lambda_sharp hfl hb
  linarith

/-- `1 < T_ann` at the working point (`log T_ann ≥ μ − 2Λ > 0`). -/
theorem s13CapGrid_Tann_one {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) : (1 : ℝ) < 2 * T := by
  set μ : ℝ := Real.log (((A + s : ℕ)) : ℝ) with hμdef
  have hμ2000 : (2000 : ℝ) ≤ μ := s13CapGrid_mu_2000 hfl hb
  have hΛ21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log μ := s13CapGrid_Lambda_lo hfl hb
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hsq : Real.log μ ≤ Real.sqrt μ := capgrid_log_le_sqrt (by linarith)
  have hs2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ0.le
  have hs0 : (0 : ℝ) < Real.sqrt μ := Real.sqrt_pos.mpr hμ0
  have hs40 : (40 : ℝ) ≤ Real.sqrt μ := by nlinarith [hs2, hs0]
  have h2Λ : 2 * Real.log μ ≤ μ / 2 := by nlinarith [hsq, hs2, hs40, hs0]
  have hlow := s13CapGrid_logTann_lo hfl hb hTlo
  have hlog0 : (0 : ℝ) < Real.log (2 * T) := by rw [← hμdef] at hlow; linarith
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hNd1 : (1 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    have : 1 ≤ A + s := by omega
    exact_mod_cast this
  have hT0 : (0 : ℝ) < 2 * T := by
    have h1 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) := by positivity
    linarith
  have := Real.exp_lt_exp.mpr hlog0
  rwa [Real.exp_zero, Real.exp_log hT0] at this

/-- The SANDWICH's top at the pins: `ramQbase ≤ Q` on the grid. -/
theorem s13CapGrid_base_le_Q {Nd i : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ)))
    (hi : i ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) (s13BandQ Nd)) :
    ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i ≤ s13BandQ Nd := by
  have hH2 : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293 := s13CapGrid_H83_two hμ hΛ
  exact ramQbase_le_top (by linarith) (s13CapGrid_Q_pos hμ) (s13CapGrid_P_le_Q hμ hΛ) hi

/-- **⟦FIELD `Hj`⟧** `H₈₃ ≤ i` on the grid — `FrameWitness.ramI_index_ge`. -/
theorem s13CapGrid_Hj {Nd : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ))) :
    ∀ i ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) (s13BandQ Nd),
      H83 ((Nd : ℕ) : ℝ) theta293 ≤ (i : ℝ) := by
  intro i hi
  have hH2 : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293 := s13CapGrid_H83_two hμ hΛ
  exact ramI_index_ge (by linarith) (s13CapGrid_logP_two hμ hΛ) hi

/-- **⟦FIELD `B3`⟧** `3 ≤ Q_base` on the grid — `FrameWitness.ramQbase_ge_bot` against
`3 ≤ P`. -/
theorem s13CapGrid_B3 {Nd : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ))) :
    ∀ i ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) (s13BandQ Nd),
      3 ≤ ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i := by
  intro i _
  exact le_trans (s13CapGrid_P_three hμ hΛ)
    (ramQbase_ge_bot (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i)

/-- `log Q_base ≤ μ/Λ` on the grid — the SANDWICH's top in `log` form. -/
theorem s13CapGrid_logBase_le {Nd i : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ)))
    (hi : i ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) (s13BandQ Nd)) :
    Real.log ((ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i : ℕ) : ℝ)
      ≤ Real.log ((Nd : ℕ) : ℝ) / Real.log (Real.log ((Nd : ℕ) : ℝ)) := by
  have hb3 := s13CapGrid_B3 hμ hΛ i hi
  have hb3R : (3 : ℝ) ≤ ((ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i : ℕ) : ℝ) := by
    exact_mod_cast hb3
  have hle : ((ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i : ℕ) : ℝ)
      ≤ ((s13BandQ Nd : ℕ) : ℝ) := by exact_mod_cast s13CapGrid_base_le_Q hμ hΛ hi
  exact le_trans (Real.log_le_log (by linarith) hle) (s13CapGrid_logQ_le hμ)

/-- **⟦THE `κ`-ROW AT `T_ann`⟧** `30 ≤ log T_ann / log Q_base` on the grid — the row the
`hTlo` floor pays for.  `log Q_base ≤ μ/Λ` and `log T_ann ≥ μ − 2Λ`, and
`30·(μ/Λ) + 2Λ ≤ μ` (§0). -/
theorem s13CapGrid_kappa_Tann {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    ∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
      30 ≤ Real.log (2 * T)
        / Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i) := by
  intro i hi
  set μ : ℝ := Real.log (((A + s : ℕ)) : ℝ) with hμdef
  have hμ2000 : (2000 : ℝ) ≤ μ := s13CapGrid_mu_2000 hfl hb
  have hΛ21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log μ := s13CapGrid_Lambda_lo hfl hb
  have hΛ100 : (100 : ℝ) ≤ Real.log μ := by
    have : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    nlinarith
  have hb3 := s13CapGrid_B3 (Nd := A + s) hμ2000 hΛ21 i hi
  have hb3R : (3 : ℝ)
      ≤ ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ) := by
    exact_mod_cast hb3
  have hlog0 : (0 : ℝ)
      < Real.log ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ) :=
    Real.log_pos (by linarith)
  have htop := s13CapGrid_logBase_le (Nd := A + s) hμ2000 hΛ21 hi
  have hlow := s13CapGrid_logTann_lo hfl hb hTlo
  have hnum := capgrid_kappa_numeric hμ2000 hΛ100
  rw [le_div_iff₀ hlog0]
  rw [← hμdef] at hlow
  nlinarith [htop, hlow, hnum]

/-- **⟦FIELD `kappa30`⟧** the `κ`-gate on the grid, at `q·T_ann` (`q ≥ 1` only helps). -/
theorem s13CapGrid_kappa30 {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    ∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
      30 ≤ Real.log ((q : ℝ) * (2 * T))
        / Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i) := by
  intro i hi
  have hq1 : 1 ≤ q := hb.2.2.2.1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hT1 : (1 : ℝ) < 2 * T := s13CapGrid_Tann_one hfl hb hTlo
  have hmul : Real.log (2 * T) ≤ Real.log ((q : ℝ) * (2 * T)) := by
    apply Real.log_le_log (by linarith)
    nlinarith
  have hb3 := s13CapGrid_B3 (Nd := A + s) (s13CapGrid_mu_2000 hfl hb)
    (s13CapGrid_Lambda_lo hfl hb) i hi
  have hb3R : (3 : ℝ)
      ≤ ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ) := by
    exact_mod_cast hb3
  have hlog0 : (0 : ℝ)
      < Real.log ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ) :=
    Real.log_pos (by linarith)
  have hbase := s13CapGrid_kappa_Tann hfl hb hTlo i hi
  rw [le_div_iff₀ hlog0] at hbase ⊢
  linarith

/-- **⟦FIELD `BT10`⟧** `Q_base ≤ T_ann^{10}` on the grid — `USetThinTL.ramQbase_le_pow_ten`
at the `T_ann`-version of the `κ`-row. -/
theorem s13CapGrid_BT10 {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    ∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
      ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
        ≤ (2 * T) ^ 10 := by
  intro i hi
  exact ramQbase_le_pow_ten (s13CapGrid_Tann_one hfl hb hTlo)
    (s13CapGrid_B3 (Nd := A + s) (s13CapGrid_mu_2000 hfl hb) (s13CapGrid_Lambda_lo hfl hb) i hi)
    (s13CapGrid_kappa_Tann hfl hb hTlo i hi)

/-- **⟦FIELD `BT`⟧** `Q_base ≤ q·T_ann` on the grid.  `Q_base ≤ Q ≤ Q₈₃ = e^{μ/Λ}` and
`μ/Λ ≤ log T_ann` off the same `κ`-arithmetic. -/
theorem s13CapGrid_BT {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    ∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
      ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
        ≤ (q : ℝ) * (2 * T) := by
  intro i hi
  set μ : ℝ := Real.log (((A + s : ℕ)) : ℝ) with hμdef
  have hμ2000 : (2000 : ℝ) ≤ μ := s13CapGrid_mu_2000 hfl hb
  have hΛ21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log μ := s13CapGrid_Lambda_lo hfl hb
  have hΛ100 : (100 : ℝ) ≤ Real.log μ := by
    have : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    nlinarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hb3 := s13CapGrid_B3 (Nd := A + s) hμ2000 hΛ21 i hi
  have hb3R : (3 : ℝ)
      ≤ ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ) := by
    exact_mod_cast hb3
  have hT1 : (1 : ℝ) < 2 * T := s13CapGrid_Tann_one hfl hb hTlo
  have hq1 : 1 ≤ q := hb.2.2.2.1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have htop := s13CapGrid_logBase_le (Nd := A + s) hμ2000 hΛ21 hi
  have hlow := s13CapGrid_logTann_lo hfl hb hTlo
  rw [← hμdef] at hlow
  have hnum := capgrid_kappa_numeric hμ2000 hΛ100
  have hstep : Real.log ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i
      : ℕ) : ℝ) ≤ Real.log (2 * T) := by
    have hdiv : (0 : ℝ) ≤ μ / Real.log μ := by positivity
    nlinarith [htop, hlow, hnum]
  have hmono := Real.exp_le_exp.mpr hstep
  rw [Real.exp_log (by linarith), Real.exp_log (by linarith)] at hmono
  nlinarith [hmono, hqR, hT1]

/-- **⟦FIELD `WL`⟧** `log Q_base ≤ Lr = μ^{11/10}` on the grid. -/
theorem s13CapGrid_WL {Nd : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ))) :
    ∀ i ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) (s13BandQ Nd),
      Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i) ≤ s13Lr Nd := by
  intro i hi
  set μ : ℝ := Real.log ((Nd : ℕ) : ℝ) with hμdef
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by
    have : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    linarith
  have htop := s13CapGrid_logBase_le hμ hΛ hi
  have hdiv : μ / Real.log μ ≤ μ := by
    rw [div_le_iff₀ hΛ0]; nlinarith
  have hone : μ ≤ s13Lr Nd := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := μ) (by linarith : (1 : ℝ) ≤ μ)
      (by norm_num : (1 : ℝ) ≤ (11 : ℝ) / 10)
    rw [Real.rpow_one] at h
    rw [s13Lr, ← hμdef]
    exact h
  rw [← hμdef] at htop
  linarith

/-! ## §4 — THE `cs`-GATE

`420·Lr^{7/4}·(log Lr)^5 ≤ cs·(log Q_base)²` at `Lr = μ^{11/10}` and
`log Q_base ≥ log P ≥ μ^{1−θ₂₉₃}`.  ⟦THE EXPONENT MARGIN⟧ the demand is
`420·((11/10)Λ)^5 ≤ μ^{3/40 − 2θ₂₉₃}` and the margin `3/40 − 2θ₂₉₃ ≥ 68/1000` is POSITIVE
(`exit_margin_293_sharp`); §0's numeric closes it already at `Λ ≥ 7800`, sixteen orders below
the socket base.  `1 ≤ cs` is carried as a named binder — the gate is a demand ON `cs`. -/

/-- **⟦THE `gate` EXPONENT MARGIN⟧** `68/1000 ≤ 3/40 − 2θ₂₉₃` (true value `0.068172`). -/
theorem capgrid_gate_margin : (68 : ℝ) / 1000 ≤ 3 / 40 - 2 * theta293 := by
  have := exit_margin_293_sharp; linarith

/-- **⟦FIELD `gate`⟧** the `cs`-gate on the grid. -/
theorem s13CapGrid_gate {Nd : ℕ} {cs : ℝ} (hcs : 1 ≤ cs)
    (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ))) :
    ∀ i ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) (s13BandQ Nd),
      420 * s13Lr Nd * (s13Lr Nd) ^ ((3 : ℝ) / 4) * (Real.log (s13Lr Nd)) ^ 5
        ≤ cs * (Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i)) ^ 2 := by
  intro i hi
  set μ : ℝ := Real.log ((Nd : ℕ) : ℝ) with hμdef
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by
    have : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    linarith
  have hΛ7800 : (7800 : ℝ) ≤ Real.log μ := by
    have : (7800 : ℝ) ≤ (10 : ℝ) ^ (21 : ℕ) := by norm_num
    linarith
  -- the `Lr` algebra
  have hL1 : s13Lr Nd * (s13Lr Nd) ^ ((3 : ℝ) / 4) = μ ^ ((77 : ℝ) / 40) := by
    rw [s13Lr, ← hμdef, ← Real.rpow_mul hμ0.le, ← Real.rpow_add hμ0]
    norm_num
  have hlogLr : Real.log (s13Lr Nd) = 11 / 10 * Real.log μ := by
    rw [s13Lr, ← hμdef, Real.log_rpow hμ0]
  -- the base side
  have hbase : μ ^ (1 - theta293)
      ≤ Real.log ((ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i : ℕ) : ℝ) := by
    refine le_trans (s13CapGrid_logP_ge Nd) (Real.log_le_log ?_ ?_)
    · have h3 := s13CapGrid_P_three hμ hΛ
      have : (3 : ℝ) ≤ ((s13BandP Nd : ℕ) : ℝ) := by exact_mod_cast h3
      linarith
    · exact_mod_cast ramQbase_ge_bot (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i
  have hpow2 : (μ ^ (1 - theta293)) ^ (2 : ℕ) = μ ^ ((2 : ℝ) - 2 * theta293) := by
    rw [← Real.rpow_natCast (μ ^ (1 - theta293)) 2, ← Real.rpow_mul hμ0.le]
    congr 1
    push_cast
    ring
  have hsplit : μ ^ ((2 : ℝ) - 2 * theta293)
      = μ ^ ((77 : ℝ) / 40) * μ ^ ((3 : ℝ) / 40 - 2 * theta293) := by
    rw [← Real.rpow_add hμ0]; congr 1; ring
  have hgate : 420 * (11 / 10 * Real.log μ) ^ 5 ≤ μ ^ ((3 : ℝ) / 40 - 2 * theta293) := by
    rw [Real.rpow_def_of_pos hμ0]
    refine le_trans (capgrid_gate_numeric hΛ7800) (Real.exp_le_exp.mpr ?_)
    nlinarith [capgrid_gate_margin, hΛ0]
  calc 420 * s13Lr Nd * (s13Lr Nd) ^ ((3 : ℝ) / 4) * (Real.log (s13Lr Nd)) ^ 5
      = μ ^ ((77 : ℝ) / 40) * (420 * (11 / 10 * Real.log μ) ^ 5) := by
        rw [hlogLr, ← hL1]; ring
    _ ≤ μ ^ ((77 : ℝ) / 40) * μ ^ ((3 : ℝ) / 40 - 2 * theta293) :=
        mul_le_mul_of_nonneg_left hgate (Real.rpow_nonneg hμ0.le _)
    _ = (μ ^ (1 - theta293)) ^ (2 : ℕ) := by rw [hpow2, hsplit]
    _ ≤ (Real.log ((ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i : ℕ) : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hμ0.le _) hbase 2
    _ ≤ cs * (Real.log ((ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i : ℕ) : ℝ))
          ^ 2 := by nlinarith [sq_nonneg (Real.log
            ((ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i : ℕ) : ℝ))]

/-! ## §5 — THE TAIL BAND'S TWO SIDE CONDITIONS

`Q_hundred` is `100·log Q ≤ μ`, immediate from `log Q ≤ μ/Λ` at `Λ ≥ 100`.

`band_product` is the ONE new analytic page of this wave: the Mertens/Rankin band product
`∏_{P ≤ p ≤ Q}(1 + 3/p)` against the sieve's `X_d·log P/log Q`.  The machinery is
`TypicalDensity.prod_one_add_three_div_le` (windowed Mertens); no exit existed, so this
section builds it.  ⟦THE ARITHMETIC⟧ the product is `≤ e^{3θ₂₉₃Λ + 57}` (the window ratio
`log Q/log P ≤ μ^{θ₂₉₃}/Λ`), the left factor is `≤ 2e^{μ/2}` and the right side is
`≥ e^{μ − θ₂₉₃Λ}` — so the demand is `4θ₂₉₃Λ + 58 ≤ μ/2`, and `μ ≥ Λ²` settles it with
twenty-one orders to spare. -/

/-- **⟦FIELD `Q_hundred`⟧** `100·log Q ≤ log X_d`. -/
theorem s13CapGrid_Q_hundred {Nd : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ))) :
    100 * Real.log ((s13BandQ Nd : ℕ) : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) := by
  set μ : ℝ := Real.log ((Nd : ℕ) : ℝ) with hμdef
  have hΛ100 : (100 : ℝ) ≤ Real.log μ := by
    have : (100 : ℝ) ≤ (10 : ℝ) ^ (21 : ℕ) := by norm_num
    linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have h := s13CapGrid_logQ_le hμ
  rw [← hμdef] at h
  have hdiv : 100 * (μ / Real.log μ) ≤ μ := by
    rw [mul_div_assoc', div_le_iff₀ hΛ0]; nlinarith
  linarith

/-- **⟦FIELD `band_product`⟧** `(√X_d + 1)·∏_{P ≤ p ≤ Q}(1 + 3/p) ≤ X_d·log P/log Q`. -/
theorem s13CapGrid_band_product {Nd : ℕ} (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ))) :
    ((Nat.sqrt Nd : ℝ) + 1) * ∏ p ∈ primeBand (s13BandP Nd) (s13BandQ Nd), (1 + 3 / (p : ℝ))
      ≤ ((Nd : ℕ) : ℝ)
        * (Real.log ((s13BandP Nd : ℕ) : ℝ) / Real.log ((s13BandQ Nd : ℕ) : ℝ)) := by
  have hNd0 : (0 : ℝ) < ((Nd : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos Nd with h | h
    · exfalso; rw [h] at hμ; simp at hμ; linarith
    · exact_mod_cast h
  set μ : ℝ := Real.log ((Nd : ℕ) : ℝ) with hμdef
  set Λ : ℝ := Real.log μ with hΛdef
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ100 : (100 : ℝ) ≤ Λ := by
    have : (100 : ℝ) ≤ (10 : ℝ) ^ (21 : ℕ) := by norm_num
    rw [hΛdef]; linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hθ0 : (0 : ℝ) < theta293 := theta293_pos
  have hθ1 : theta293 ≤ 1 / 100 := frames_theta293_le
  have hNdexp : Real.exp μ = ((Nd : ℕ) : ℝ) := by rw [hμdef]; exact Real.exp_log hNd0
  -- the pins
  have hP3 : 3 ≤ s13BandP Nd := s13CapGrid_P_three hμ hΛ
  have hPQ : s13BandP Nd ≤ s13BandQ Nd := s13CapGrid_P_le_Q hμ hΛ
  have hQ3 : 3 ≤ s13BandQ Nd := le_trans hP3 hPQ
  have hPR : (3 : ℝ) ≤ ((s13BandP Nd : ℕ) : ℝ) := by exact_mod_cast hP3
  have hQR : (3 : ℝ) ≤ ((s13BandQ Nd : ℕ) : ℝ) := by exact_mod_cast hQ3
  set a : ℝ := Real.log ((s13BandP Nd : ℕ) : ℝ) with hadef
  set b : ℝ := Real.log ((s13BandQ Nd : ℕ) : ℝ) with hbdef
  have ha2 : 2 ≤ a := s13CapGrid_logP_two hμ hΛ
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by rw [hbdef]; exact Real.log_pos (by linarith)
  have hbhi : b ≤ μ / Λ := by rw [hbdef, hΛdef, hμdef]; exact s13CapGrid_logQ_le hμ
  have hbmu : b ≤ μ := by
    have : μ / Λ ≤ μ := by rw [div_le_iff₀ hΛ0]; nlinarith
    linarith
  have halo : μ ^ (1 - theta293) ≤ a := by
    rw [hadef, hμdef]; exact s13CapGrid_logP_ge Nd
  -- `μ^{1−θ} = μ·e^{−θΛ}`
  have hsplit : μ ^ (1 - theta293) = μ * Real.exp (-(theta293 * Λ)) := by
    rw [Real.rpow_def_of_pos hμ0, ← hΛdef,
      show Λ * (1 - theta293) = Λ + -(theta293 * Λ) by ring, Real.exp_add, hΛdef,
      Real.exp_log hμ0]
  -- ⟦LEG 1⟧ the band product
  have hprodle : ∏ p ∈ primeBand (s13BandP Nd) (s13BandQ Nd), (1 + 3 / (p : ℝ))
      ≤ Real.exp (3 * theta293 * Λ + 57) := by
    refine le_trans (prod_one_add_three_div_le (by omega) hPQ) (Real.exp_le_exp.mpr ?_)
    have hnum0 : (0 : ℝ) < Real.log (((s13BandQ Nd : ℕ) : ℝ) + 1) :=
      Real.log_pos (by linarith)
    have hstep1 : Real.log (((s13BandQ Nd : ℕ) : ℝ) + 1) ≤ 1 + b := by
      have h2Q : ((s13BandQ Nd : ℕ) : ℝ) + 1 ≤ 2 * ((s13BandQ Nd : ℕ) : ℝ) := by linarith
      have := Real.log_le_log (by linarith) h2Q
      rw [Real.log_mul (by norm_num) (by linarith), ← hbdef] at this
      have hl2 : Real.log 2 ≤ 1 := by
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
      linarith
    have hstep2 : Real.log (Real.log (((s13BandQ Nd : ℕ) : ℝ) + 1) / a)
        ≤ Real.log ((1 + b) / a) := by
      refine Real.log_le_log (by positivity) ?_
      gcongr
    have hstep3 : Real.log ((1 + b) / a) = Real.log (1 + b) - Real.log a :=
      Real.log_div (by linarith) (by linarith)
    have hstep4 : Real.log (1 + b) ≤ Λ := by
      have h1b : 1 + b ≤ μ := by
        have : μ / Λ ≤ μ / 100 := by
          rw [div_le_div_iff₀ hΛ0 (by norm_num)]; nlinarith
        linarith
      rw [hΛdef]; exact Real.log_le_log (by linarith) h1b
    have hstep5 : (1 - theta293) * Λ ≤ Real.log a := by
      have hp0 : (0 : ℝ) < μ ^ (1 - theta293) := Real.rpow_pos_of_pos hμ0 _
      have := Real.log_le_log hp0 halo
      rwa [Real.log_rpow hμ0, ← hΛdef] at this
    have h19 : 19 / a ≤ 19 := by
      rw [div_le_iff₀ ha0]; nlinarith
    have hcore : Real.log (Real.log (((s13BandQ Nd : ℕ) : ℝ) + 1) / a) ≤ theta293 * Λ := by
      linarith
    linarith
  have hprod0 : (0 : ℝ)
      ≤ ∏ p ∈ primeBand (s13BandP Nd) (s13BandQ Nd), (1 + 3 / (p : ℝ)) := by
    refine Finset.prod_nonneg (fun p hp => ?_)
    have : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    positivity
  -- ⟦LEG 2⟧ the `√X_d` factor
  have hsqrt : ((Nat.sqrt Nd : ℕ) : ℝ) ≤ Real.exp (μ / 2) := by
    have hnat : (Nat.sqrt Nd) ^ 2 ≤ Nd := Nat.sqrt_le' Nd
    have hR : ((Nat.sqrt Nd : ℕ) : ℝ) ^ 2 ≤ ((Nd : ℕ) : ℝ) := by exact_mod_cast hnat
    have h2 : (Real.exp (μ / 2)) ^ (2 : ℕ) = ((Nd : ℕ) : ℝ) := by
      rw [← Real.exp_nat_mul]
      rw [show ((2 : ℕ) : ℝ) * (μ / 2) = μ by push_cast; ring]
      exact hNdexp
    have hc0 : (0 : ℝ) ≤ ((Nat.sqrt Nd : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [Real.exp_pos (μ / 2), hR, h2]
  have hleft : ((Nat.sqrt Nd : ℝ) + 1) ≤ 2 * Real.exp (μ / 2) := by
    have h1 : (1 : ℝ) ≤ Real.exp (μ / 2) := by
      rw [show (1 : ℝ) = Real.exp 0 by simp]
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  -- ⟦LEG 3⟧ the right-hand ratio
  have hratio : Real.exp (-(theta293 * Λ)) ≤ a / b := by
    rw [le_div_iff₀ hb0]
    have h1 : Real.exp (-(theta293 * Λ)) * b ≤ Real.exp (-(theta293 * Λ)) * μ :=
      mul_le_mul_of_nonneg_left hbmu (Real.exp_pos _).le
    have h2 : Real.exp (-(theta293 * Λ)) * μ = μ ^ (1 - theta293) := by rw [hsplit]; ring
    linarith
  -- ⟦THE CLOSE⟧ `4θΛ + 58 ≤ μ/2`
  have hmuΛ : Λ ^ 2 ≤ μ := by rw [hΛdef]; exact capgrid_mu_ge_sq (by linarith)
  have hclose : 1 + μ / 2 + (3 * theta293 * Λ + 57) ≤ μ + -(theta293 * Λ) := by
    nlinarith [hmuΛ, hΛ100, hθ0, hθ1]
  have hexp2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc ((Nat.sqrt Nd : ℝ) + 1)
        * ∏ p ∈ primeBand (s13BandP Nd) (s13BandQ Nd), (1 + 3 / (p : ℝ))
      ≤ (2 * Real.exp (μ / 2)) * Real.exp (3 * theta293 * Λ + 57) :=
        mul_le_mul hleft hprodle hprod0 (by positivity)
    _ ≤ Real.exp 1 * Real.exp (μ / 2) * Real.exp (3 * theta293 * Λ + 57) := by
        have hXY : (0 : ℝ) < Real.exp (μ / 2) * Real.exp (3 * theta293 * Λ + 57) := by
          positivity
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.exp 1 - 2) hXY.le]
    _ = Real.exp (1 + μ / 2 + (3 * theta293 * Λ + 57)) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (μ + -(theta293 * Λ)) := Real.exp_le_exp.mpr hclose
    _ = ((Nd : ℕ) : ℝ) * Real.exp (-(theta293 * Λ)) := by rw [Real.exp_add, hNdexp]
    _ ≤ ((Nd : ℕ) : ℝ) * (a / b) := mul_le_mul_of_nonneg_left hratio hNd0.le

/-! ## §6 — `Q2_reg` AND THE BUNDLING LEMMA -/

/-- **⟦FIELD `Q2_reg`⟧** `log 𝒬K₂ ≤ √(log X_d)` — `S13FramesA.s13_doorRowZeroBase_five`'s
second conjunct, byte-identical.  `s13BlockFloor M ≤ X_d` is the corpus's OWN named binder
for this genre (`M4AssemblyFrames.doorRowZeroBase_family`'s `hblock`), carried here
unchanged. -/
theorem s13CapGrid_Q2_reg {R : ChowlaRegime} {M H L q j A s : ℕ} (hM : 1 ≤ M)
    (hb : SocketBase R M H L q j A s) (hblock : s13BlockFloor M ≤ A + s) :
    Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) :=
  (s13_doorRowZeroBase_five hM hblock hb.2.2.2.2.2.2.1).2.1

/-- **⟦THE GRID WAVE, BUNDLED⟧** (`s13CapGrid_all`) — EIGHTEEN of `S13CapGatePerBlock`'s
thirty-seven fields, in structure order, at the socket's working point and the canonical band
pins `P = ⌈P₈₃ X_d θ₂₉₃⌉₊`, `Q = ⌊Q₈₃ X_d⌋₊`, with `X_d = A + s`, `T_ann = 2T`,
`H_reg = H`.

⟦THE HYPOTHESIS REGISTER⟧ — six binders, all of them the corpus's own:

* `hM : 1 ≤ M`, `hb : SocketBase R M H L q j A s`, `hfl : loglogFloor50 ≤ R.Hlo` — the
  socket triple every `S13`/`M4` page already carries;
* `hblock : s13BlockFloor M ≤ A + s` — the `M`-versus-base threshold, named exactly as in
  `M4AssemblyFrames.doorRowZeroBase_family`;
* `hTlo`/`hThi` — the gate FAMILY's own window binders
  (`doorCapBundle_family_perBlock`, verbatim);
* `hcs : 1 ≤ cs` — the `gate` field is a demand ON `cs`, so a floor on it is unavoidable.

NOT supplied here (other waves): `QTann`, `kappa30Q`, `T0_Tann`, `floor1`–`floor4`, `budget`,
`Rbd_nonneg`, `Rbd_grade`, `Cq_gate`, `Rbd_socket`, `epsr_nonneg`, `abs8640`, `EP2_gate`,
`q_arcDen`, `phi_row`, `p2_row`, `tail_row`. -/
theorem s13CapGrid_all {R : ChowlaRegime} {M H L q j A s : ℕ} {cs T : ℝ}
    (hM : 1 ≤ M) (hcs : 1 ≤ cs) (hfl : loglogFloor50 ≤ R.Hlo)
    (hb : SocketBase R M H L q j A s) (hblock : s13BlockFloor M ≤ A + s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T)
    (hThi : 2 * T ≤ (((A + s : ℕ)) : ℝ)) :
    -- ⟦logX_eight⟧
    8 ≤ Real.log (((A + s : ℕ)) : ℝ)
    -- ⟦H83_two⟧
    ∧ 2 ≤ H83 (((A + s : ℕ)) : ℝ) theta293
    -- ⟦q_logX⟧
    ∧ (q : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ 12
    -- ⟦logqT_L⟧
    ∧ Real.log ((q : ℝ) * (2 * T)) ≤ s13Lr (A + s)
    -- ⟦P_low⟧
    ∧ P83 (((A + s : ℕ)) : ℝ) theta293 ≤ ((s13BandP (A + s) : ℕ) : ℝ)
    -- ⟦Q2_reg⟧
    ∧ Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
        ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ))
    -- ⟦Q_pos⟧
    ∧ 0 < s13BandQ (A + s)
    -- ⟦Q_high⟧
    ∧ ((s13BandQ (A + s) : ℕ) : ℝ) ≤ Q83 (((A + s : ℕ)) : ℝ)
    -- ⟦P_le_Q⟧
    ∧ s13BandP (A + s) ≤ s13BandQ (A + s)
    -- ⟦Hj⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        H83 (((A + s : ℕ)) : ℝ) theta293 ≤ (i : ℝ))
    -- ⟦B3⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        3 ≤ ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i)
    -- ⟦BT⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
          ≤ (q : ℝ) * (2 * T))
    -- ⟦kappa30⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        30 ≤ Real.log ((q : ℝ) * (2 * T))
          / Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i))
    -- ⟦BT10⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
          ≤ (2 * T) ^ 10)
    -- ⟦WL⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i)
          ≤ s13Lr (A + s))
    -- ⟦gate⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        420 * s13Lr (A + s) * (s13Lr (A + s)) ^ ((3 : ℝ) / 4)
            * (Real.log (s13Lr (A + s))) ^ 5
          ≤ cs * (Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293)
              (s13BandP (A + s)) i)) ^ 2)
    -- ⟦Q_hundred⟧
    ∧ 100 * Real.log ((s13BandQ (A + s) : ℕ) : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ)
    -- ⟦band_product⟧
    ∧ ((Nat.sqrt (A + s) : ℝ) + 1)
          * ∏ p ∈ primeBand (s13BandP (A + s)) (s13BandQ (A + s)), (1 + 3 / (p : ℝ))
        ≤ (((A + s : ℕ)) : ℝ)
          * (Real.log ((s13BandP (A + s) : ℕ) : ℝ)
              / Real.log ((s13BandQ (A + s) : ℕ) : ℝ)) := by
  have hμ : (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := s13CapGrid_mu_2000 hfl hb
  have hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    s13CapGrid_Lambda_lo hfl hb
  exact ⟨s13CapGrid_logX_eight hfl hb, s13CapGrid_H83_two hμ hΛ, s13CapGrid_q_logX hfl hb,
    s13CapGrid_logqT_L hfl hb hTlo hThi, s13CapGrid_P_low (A + s),
    s13CapGrid_Q2_reg hM hb hblock, s13CapGrid_Q_pos hμ, s13CapGrid_Q_high (A + s),
    s13CapGrid_P_le_Q hμ hΛ, s13CapGrid_Hj hμ hΛ, s13CapGrid_B3 hμ hΛ,
    s13CapGrid_BT hfl hb hTlo, s13CapGrid_kappa30 hfl hb hTlo, s13CapGrid_BT10 hfl hb hTlo,
    s13CapGrid_WL hμ hΛ, s13CapGrid_gate hcs hμ hΛ, s13CapGrid_Q_hundred hμ hΛ,
    s13CapGrid_band_product hμ hΛ⟩

/-! ## §GK — the G-lever twin -/

/-- `s13CapGrid_Q2_reg (:935)` at the lever.  RE-RUN: `log 𝒬K₂` gains the lever's
`2^K`, and the levered block floor pays it —
the bound is `s13_doorRowZeroBase_five_gk`'s second conjunct, byte for byte. -/
theorem s13CapGrid_Q2_reg_gk (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} (hM : 1 ≤ M)
    (hb : SocketBase R M H L q j A s) (hblock : s13BlockFloor_gk K M ≤ A + s) :
    Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) :=
  (s13_doorRowZeroBase_five_gk K hM hblock hb.2.2.2.2.2.2.1).2.1

/-- `s13CapGrid_all (:959)` at the lever. -/
theorem s13CapGrid_all_gk (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} {cs T : ℝ}
    (hM : 1 ≤ M) (hcs : 1 ≤ cs) (hfl : loglogFloor50 ≤ R.Hlo)
    (hb : SocketBase R M H L q j A s) (hblock : s13BlockFloor_gk K M ≤ A + s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T)
    (hThi : 2 * T ≤ (((A + s : ℕ)) : ℝ)) :
    -- ⟦logX_eight⟧
    8 ≤ Real.log (((A + s : ℕ)) : ℝ)
    -- ⟦H83_two⟧
    ∧ 2 ≤ H83 (((A + s : ℕ)) : ℝ) theta293
    -- ⟦q_logX⟧
    ∧ (q : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ 12
    -- ⟦logqT_L⟧
    ∧ Real.log ((q : ℝ) * (2 * T)) ≤ s13Lr (A + s)
    -- ⟦P_low⟧
    ∧ P83 (((A + s : ℕ)) : ℝ) theta293 ≤ ((s13BandP (A + s) : ℕ) : ℝ)
    -- ⟦Q2_reg⟧
    ∧ Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
        ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ))
    -- ⟦Q_pos⟧
    ∧ 0 < s13BandQ (A + s)
    -- ⟦Q_high⟧
    ∧ ((s13BandQ (A + s) : ℕ) : ℝ) ≤ Q83 (((A + s : ℕ)) : ℝ)
    -- ⟦P_le_Q⟧
    ∧ s13BandP (A + s) ≤ s13BandQ (A + s)
    -- ⟦Hj⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        H83 (((A + s : ℕ)) : ℝ) theta293 ≤ (i : ℝ))
    -- ⟦B3⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        3 ≤ ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i)
    -- ⟦BT⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
          ≤ (q : ℝ) * (2 * T))
    -- ⟦kappa30⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        30 ≤ Real.log ((q : ℝ) * (2 * T))
          / Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i))
    -- ⟦BT10⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
          ≤ (2 * T) ^ 10)
    -- ⟦WL⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i)
          ≤ s13Lr (A + s))
    -- ⟦gate⟧
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        420 * s13Lr (A + s) * (s13Lr (A + s)) ^ ((3 : ℝ) / 4)
            * (Real.log (s13Lr (A + s))) ^ 5
          ≤ cs * (Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293)
              (s13BandP (A + s)) i)) ^ 2)
    -- ⟦Q_hundred⟧
    ∧ 100 * Real.log ((s13BandQ (A + s) : ℕ) : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ)
    -- ⟦band_product⟧
    ∧ ((Nat.sqrt (A + s) : ℝ) + 1)
          * ∏ p ∈ primeBand (s13BandP (A + s)) (s13BandQ (A + s)), (1 + 3 / (p : ℝ))
        ≤ (((A + s : ℕ)) : ℝ)
          * (Real.log ((s13BandP (A + s) : ℕ) : ℝ)
              / Real.log ((s13BandQ (A + s) : ℕ) : ℝ)) := by
  have hμ : (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := s13CapGrid_mu_2000 hfl hb
  have hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    s13CapGrid_Lambda_lo hfl hb
  exact ⟨s13CapGrid_logX_eight hfl hb, s13CapGrid_H83_two hμ hΛ, s13CapGrid_q_logX hfl hb,
    s13CapGrid_logqT_L hfl hb hTlo hThi, s13CapGrid_P_low (A + s),
    s13CapGrid_Q2_reg_gk K hM hb hblock, s13CapGrid_Q_pos hμ, s13CapGrid_Q_high (A + s),
    s13CapGrid_P_le_Q hμ hΛ, s13CapGrid_Hj hμ hΛ, s13CapGrid_B3 hμ hΛ,
    s13CapGrid_BT hfl hb hTlo, s13CapGrid_kappa30 hfl hb hTlo, s13CapGrid_BT10 hfl hb hTlo,
    s13CapGrid_WL hμ hΛ, s13CapGrid_gate hcs hμ hΛ, s13CapGrid_Q_hundred hμ hΛ,
    s13CapGrid_band_product hμ hΛ⟩


end Salt.MR

end
