/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S13CapEps
import Salt.MR.S13CapFloor
import Salt.MR.S13CapGateLinear
import Salt.MR.S16Compose
import Salt.MR.S16ProducersH
import Salt.MR.S16FlatTerminalLinearLH

/-!
# ⟦H2c⟧ — THE CROSSING SUPPLIER AT THE INFLATED SOCKET `SocketBaseLH h`

**PURELY ADDITIVE.**  No landed declaration is edited.  Every landed numeric stone whose
ceiling the `h` lane outgrows gets a SIBLING here with a wider ceiling; the landed stone
keeps its own consumers untouched.

## ⟦WHY THE PAGE EXISTS AT ALL⟧ — the assembler's `hbb`

`s16_capGate_supply_L_gk` (`S13CapGateLinear:955`) and `s13CapGrid_all_L_gk` (`:594`) build
`hbb : SocketBase` out of their `SocketBaseL` binder and feed `hbb` to the WHOLE floor and
eps pages.  `SocketBaseLH h → SocketBase` is FALSE at `h ≥ 2` — the modulus conjunct is
`q ≤ h·arcDen 12 H`, not `q ≤ arcDen 12 H` — and no non-linear inflated socket exists.  So
every `SocketBase`-typed leaf under that assembler is re-stated here at `SocketBaseLH h`.

## ⟦THE TWO CONJUNCTS THAT MOVE, AND WHERE THEY ARE READ⟧ (census, h2c step 0)

`SocketBaseLH` (`HDoorSupply:535`) is 13 conjuncts; exactly two differ from `SocketBaseL`:

* **conjunct 5**, `q ≤ h·arcDen 12 H` — read at exactly FIVE sites: `s13CapGrid_q_logX`
  (`S13CapGrid:393`), `capfloor_logq_le` (`S13CapFloor:284`), `capfloor_floor4` (`:459`),
  `s13_capEps_register` (`S13CapEps:476`), `s13CapEps_q_arcDen` (`:530`);
* **conjunct 11**, `x ≤ 16·ω·(h·arcDen 12 H)·A` — read at exactly ONE site,
  `s13_socketBase_xscale` (`S13MSelect2:111`), reaching this page only through
  `s13_socketBase_logA_ge_sqrt` (`:182`).

Conjunct 11 costs NOTHING new: its whole `_LH` substrate is already landed in
`S16ProducersH` (`xscale_LH :332`, `logA_ge_sqrt_LH :345`, `loglogA_sharp_LH :408`,
`loglogA_LH :425`).  On the grid page only `s13CapGrid_mu_lo` and `s13CapGrid_Lambda_sharp`
touch that substrate directly; the other twelve `11`-routed leaves inherit through them.

## ⟦§1 — THE SIX NUMERIC SIBLINGS⟧

These carry NO socket.  They exist because three landed stones sit at a ceiling that is an
author's convenience rather than a barrier, and the `+log h` line needs a few units more:
`log h ≤ 7` turns a spend of `49` into `56`, and `8` into `15`.

⭐ **THE CEILINGS WERE NEVER TIGHT, AND THE MARGIN IS NOT CLOSE.**  In `capeps_master` the
hypothesis `t ≤ 50` enters the proof in exactly one place — the closing `nlinarith`, and
linearly.  The goal is `t + 12·log u + log Λ ≤ (14/10000)·Λ` with `Λ ≥ u/2 ≥ 5·10²⁰`, so the
right side is `≥ 7·10¹⁷` against a left side of about `686`.  **The true admissible `t` is
~`7·10¹⁷`; `60` is the smallest round ceiling clearing the `56` the `h` lane spends, and it
is seventeen orders below the barrier.**  Likewise `capfloor_lam_core` pays `160 + 96·log v`
(~`4806`) against `v/4 ≥ 2.5·10²⁰`, so `160 → 216` costs `56` against twenty orders.

The siblings are therefore stated with the SAME proof certificates as the landed stones,
not with re-derived ones: if a certificate did not travel, the ceiling would have been a
barrier after all, and that is a finding rather than a repair.
-/

namespace Salt.MR

section NumericSiblings

/-- ⟦SIBLING of `capeps_master` (`S13CapEps:104`), ceiling `50 → 60`⟧ — the `εr`-budget
master line.  `ht` enters only the closing `nlinarith`, linearly, against `(14/10000)·Λ ≥
7·10¹⁷`; the certificate is the landed one, unchanged. -/
theorem capeps_master_60 {u Λ t : ℝ} (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hΛ : u / 2 ≤ Λ)
    (ht : t ≤ 60) : t + 12 * Real.log u + Real.log Λ ≤ 14 / 10000 * Λ := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hu2L : u ≤ 2 * Λ := by linarith
  have hlogu : Real.log u ≤ 1 + Real.log Λ := by
    have h1 : Real.log u ≤ Real.log (2 * Λ) := Real.log_le_log hu0 hu2L
    have h2 : Real.log (2 * Λ) = Real.log 2 + Real.log Λ :=
      Real.log_mul (by norm_num) (ne_of_gt hΛ0)
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith
  have hsq0 : (0 : ℝ) < Real.sqrt Λ := Real.sqrt_pos.mpr hΛ0
  have hsqrt : Real.log Λ ≤ 2 * Real.sqrt Λ := by
    have h := Real.log_le_sub_one_of_pos hsq0
    have hs : Real.log (Real.sqrt Λ) = Real.log Λ / 2 := Real.log_sqrt hΛ0.le
    rw [hs] at h; linarith
  have hsu : Real.sqrt Λ * Real.sqrt Λ = Λ := Real.mul_self_sqrt hΛ0.le
  have hLbig : (5 : ℝ) * 10 ^ (20 : ℕ) ≤ Λ := by
    have : (10 : ℝ) ^ (21 : ℕ) = 2 * (5 * 10 ^ (20 : ℕ)) := by norm_num
    linarith
  have hs10 : (2 : ℝ) * 10 ^ (10 : ℕ) ≤ Real.sqrt Λ := by
    nlinarith [hsu, hLbig, hsq0]
  nlinarith [hsqrt, hsu, hs10, hsq0, hlogu, ht]

/-- ⟦SIBLING of `capeps_expbound` (`S13CapEps:142`), ceiling `50 → 60`⟧. -/
theorem capeps_expbound_60 {u μ t : ℝ} (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (ht : t ≤ 60) :
    Real.exp t * u ^ (12 : ℕ) * Real.log μ ≤ μ ^ (theta293 - 1 / 500) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hmas := capeps_master_60 hu hΛ ht
  have hθ := s13_theta293_margin_lo
  have hlhs : Real.exp (t + 12 * Real.log u + Real.log (Real.log μ))
      = Real.exp t * u ^ (12 : ℕ) * Real.log μ := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hΛ0, ← capeps_pow12 hu0]
  rw [← hlhs, Real.rpow_def_of_pos hμ0]
  refine Real.exp_le_exp.mpr ?_
  have : 14 / 10000 * Real.log μ ≤ Real.log μ * (theta293 - 1 / 500) := by nlinarith
  linarith

/-- ⟦SIBLING of `capeps_bigexp` (`S13CapEps:161`), ceiling `50 → 60`⟧. -/
theorem capeps_bigexp_60 {u μ t : ℝ} (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (ht : t ≤ 60) :
    Real.exp t * u ^ (12 : ℕ) * μ ^ 2 ≤ Real.exp (μ - Real.log μ / 500) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hΛbig : (5 : ℝ) * 10 ^ (20 : ℕ) ≤ Real.log μ := by
    have : (10 : ℝ) ^ (21 : ℕ) = 2 * (5 * 10 ^ (20 : ℕ)) := by norm_num
    linarith
  have hmas := capeps_master_60 hu hΛ ht
  have hlogΛ : 0 ≤ Real.log (Real.log μ) := Real.log_nonneg (by linarith)
  have hsq : (Real.log μ) ^ 2 / 4 ≤ μ := by
    have h := capeps_sq_le_exp hΛ0.le
    rwa [Real.exp_log hμ0] at h
  have h3Λ : 3 * Real.log μ ≤ μ := by nlinarith [hsq, hΛbig, hΛ0]
  have hμ2 : μ ^ 2 = Real.exp (2 * Real.log μ) := by
    rw [show (2 : ℝ) * Real.log μ = ((2 : ℕ) : ℝ) * Real.log μ by norm_num,
      ← Real.log_pow, Real.exp_log (pow_pos hμ0 2)]
  have hlhs : Real.exp (t + 12 * Real.log u + 2 * Real.log μ)
      = Real.exp t * u ^ (12 : ℕ) * μ ^ 2 := by
    rw [Real.exp_add, Real.exp_add, ← capeps_pow12 hu0, ← hμ2]
  rw [← hlhs]
  exact Real.exp_le_exp.mpr (by linarith)

/-- ⟦SIBLING of `capeps_Pbig` (`S13CapEps:188`), constant `e¹¹ → e¹⁸⟧` — the `p²` row's
`1/P` leg at the `h`-inflated modulus. -/
theorem capeps_Pbig_h {u μ : ℝ} (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) :
    Real.exp 18 * u ^ (12 : ℕ) * μ * μ ^ ((1 : ℝ) / 500)
      ≤ Real.exp (μ ^ (1 - theta293)) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hΛbig : (5 : ℝ) * 10 ^ (20 : ℕ) ≤ Real.log μ := by
    have : (10 : ℝ) ^ (21 : ℕ) = 2 * (5 * 10 ^ (20 : ℕ)) := by norm_num
    linarith
  have hmas := capeps_master_60 hu hΛ (by norm_num : (18 : ℝ) ≤ 60)
  have hlogΛ : 0 ≤ Real.log (Real.log μ) := Real.log_nonneg (by linarith)
  have hθ32 : theta293 < 1 / 32 := theta293_lt_one_div_32
  have hθ0 : (0 : ℝ) < theta293 := theta293_pos
  have hrw : μ ^ (1 - theta293) = Real.exp ((1 - theta293) * Real.log μ) := by
    rw [Real.rpow_def_of_pos hμ0]; ring_nf
  have hhalf : Real.exp (Real.log μ / 2) ≤ μ ^ (1 - theta293) := by
    rw [hrw]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hsq : (Real.log μ / 2) ^ 2 / 4 ≤ Real.exp (Real.log μ / 2) :=
    capeps_sq_le_exp (by linarith)
  have hbig : 2 * Real.log μ ≤ μ ^ (1 - theta293) := by nlinarith [hsq, hhalf, hΛbig, hΛ0]
  have h500 : μ ^ ((1 : ℝ) / 500) = Real.exp (Real.log μ / 500) := by
    rw [Real.rpow_def_of_pos hμ0]; ring_nf
  have hlhs : Real.exp (18 + 12 * Real.log u + Real.log μ + Real.log μ / 500)
      = Real.exp 18 * u ^ (12 : ℕ) * μ * μ ^ ((1 : ℝ) / 500) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, ← capeps_pow12 hu0, Real.exp_log hμ0,
      ← h500]
  rw [← hlhs]
  exact Real.exp_le_exp.mpr (le_trans (by linarith) hbig)

/-- ⟦SIBLING of `capfloor_lam_core` (`S13CapFloor:268`), constant `160 → 216`⟧ — `floor1`'s
`Λ`-leg with the `+log h` room.  The landed left side is ~`4806` against `v/4 ≥ 2.5·10²⁰`;
`+56` is not visible at that scale, and the certificate is unchanged. -/
theorem capfloor_lam_core_h {v : ℝ} (hv : (10 : ℝ) ^ (21 : ℕ) ≤ v) :
    216 + 96 * Real.log v ≤ v / 4 := by
  have h := capfloor_logv_le hv
  norm_num at h ⊢
  linarith

/-- ⟦SIBLING of `capfloor_floor3_numeric` (`S13CapFloor:344`), slack `+1 → +8`⟧ — `floor3`'s
numeric leg, absorbing `log q ≤ log h + 12·loglog H` at `log h ≤ 7`. -/
theorem capfloor_floor3_numeric_h {v E W : ℝ} (hv : (10 : ℝ) ^ (21 : ℕ) ≤ v) (hE : 101 ≤ E)
    (hW : W ≤ 12 * Real.log v + E + 8) :
    E * W ≤ E ^ (3 : ℕ) * (v / 4) ^ (4 : ℕ) := by
  have hlv := capfloor_logv_le hv
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le h21 hv
  have hE0 : (0 : ℝ) < E := by linarith
  have hvbig : (1000000000000000000000 : ℝ) ≤ v := le_trans (by norm_num) hv
  have hlv' : Real.log v ≤ v / 10000000000 := le_trans hlv (by norm_num)
  have hWv : W ≤ v + E + 8 := by linarith
  have hvq : (v / 4) ^ (4 : ℕ) = v ^ (4 : ℕ) / 256 := by ring
  rw [hvq]
  have h1 : v + E + 8 ≤ v * E := by nlinarith [hvbig, hE]
  have hxx : (65536 : ℝ) ≤ v * v := by nlinarith [hvbig]
  have hv3 : (256 : ℝ) ≤ v ^ (3 : ℕ) := by
    have hid : v ^ (3 : ℕ) = v * (v * v) := by ring
    rw [hid]; nlinarith [hvbig, hxx]
  have hfac : (1 : ℝ) ≤ E * v ^ (3 : ℕ) / 256 := by nlinarith [hv3, hE]
  have hpos : (0 : ℝ) ≤ E * (v * E) := by positivity
  have h2 : E * (v * E) ≤ E ^ (3 : ℕ) * (v ^ (4 : ℕ) / 256) := by
    calc E * (v * E) = (E * (v * E)) * 1 := by ring
      _ ≤ (E * (v * E)) * (E * v ^ (3 : ℕ) / 256) := mul_le_mul_of_nonneg_left hfac hpos
      _ = E ^ (3 : ℕ) * (v ^ (4 : ℕ) / 256) := by ring
  have hA : E * W ≤ E * (v + E + 8) := mul_le_mul_of_nonneg_left hWv hE0.le
  have hB : E * (v + E + 8) ≤ E * (v * E) := mul_le_mul_of_nonneg_left h1 hE0.le
  linarith

end NumericSiblings

end Salt.MR
