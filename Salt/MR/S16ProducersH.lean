/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16FlatTerminalLinearH
import Salt.MR.XThread

/-!
# THE SOCKET'S PRODUCERS AT SHIFT `h` — wave P of the `_L_gk` h-family

⟦WHAT THIS FILE SETTLES⟧  `S16FlatTerminalLinearH` re-stated the second road's terminal
register at the `h`-inflated arc cap and left its socket `M4ChiSummedFreeRowH_L_gk h K R M RS`
with NO producer at `h ≥ 2`.  This file is the producer chain the terminal path reads — the
constant-pool fuse `m4_closure_fuse_zero'_const_nonneg_L_gk` (`S16FlatTerminalLinear.lean:109`)
and everything under it — re-quantified over the inflated framed base `HDoorSupply.SocketBaseLH h`
(`SocketBaseL` with conjuncts 5 and 11, the modulus cap and the x-scale floor, read at
`h · arcDen 12 H`).

⟦THE CAP, WHERE THE CHAIN READS IT⟧  Of the twenty-six `SocketBaseL`-framed hypothesis shapes
the producer population carries, THREE read the cap, and each has one repair here:

* **S12, the envelope price** — `arcDen 12 H · strataResidual H² ≤ e^{14·loglog H}` becomes
  `h · arcDen 12 H · strataResidualH h H² ≤ e^{14·loglog H}` (`hArcDen_mul_strataResidualH_sq_le`),
  paid under the family's landed `H`-free binder `hh7 : log h ≤ 7`; the envelope is
  `RSanDoorRhoH ρ h H := ρ / strataResidualH h H²`, whose cancel at the register's drift gate
  is EXACT and `h`-free (`m4_arith_rs_ceiling_met_rhoH`).
* **S2, the `ρ`-frame's x-floor** — `gArmDoorRho 0 0 (h·ω) ρ H` IS the inflated `g`-floor
  (`16·ω·(h·arcDen)·A = 16·(h·ω)·arcDen·A`), so the landed arm lemma applies at `ω ↦ h·ω`;
  the compose's arm is `s15ArmH h δ₀ ρ`.
* **S11, the band base's `q ≤ arcDen`** — `s13_band_qfit_h` pays the `log h` against the
  frame's `7000·loglog H` arm.

Every other shape is CAP-BLIND: its producer projects only conjuncts `{1,2,3,4,6,7,8,9}` or
carries no socket binder, and its `h`-twin is the landed proof with `SocketBaseL` read as
`SocketBaseLH h`.  ⚠️ The socket helpers under the bridge restatements (`s13_socketBase_xscale`
and its descendants, `s15_block_at_socket_gen`) read conjunct 11 and lose exactly `log h` in
the log; each is restated with `hh7` absorbing it against slack of `10²¹` and more.

⟦THE RECEIPT⟧  `m4_closure_fuse_zero'_const_nonneg_H_L_gk` concludes
`M4ChiSummedFreeRowH_L_gk h K R M (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H))` —
the socket the landed register is conditional on — and `m4_chiSummedN_supplied_of_rowH_L_gk`
shows the register's own consumer `m4_chiSummedN_suppliedH_L_gk` fires on it, with
`RStr := h⁷·rStrWitness` and the `j₀`-floor `g2_of_j0_floor_h` supplying ⟦G1⟧/⟦G2⟧.

⟦NOT IN THIS FILE⟧  The exit below the register (wave X: the `_bounded` h-wrappers, the budget
head's h-twin, the ¬Fails-form register) and the six hops above it (wave H).  No `SocketBaseH`
def, no `S13BandGate'H` structure, no `rStrWitnessH` def — each would be a statement act.

**PURELY ADDITIVE.**  No landed declaration is touched.  Nothing here bears on twin primes:
every object is conditional exactly where its `h = 1` twin is; the seven OPEN sockets
(`DoorRowZeroBase`, `DoorRowEndBase`, the `epsrf` split, the `calQK` window, …) cross to `h`
unchanged.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — the envelope at the inflated residual (word 1) -/

/-- **⟦THE DOOR'S ANALYTIC ENVELOPE, AT `ρ` AND SHIFT `h`⟧** (`RSanDoorRhoH ρ h H`) —
`RSanDoorRho` with the base residual replaced by the inflated one: `ρ / strataResidualH h H²`.
The register's drift gate reads `strataResidualH h H²` and the envelope divides by the same
square, so the cancel is EXACT at every `h`. -/
def RSanDoorRhoH (ρ : ℝ) (h H : ℕ) : ℝ := ρ / strataResidualH h H ^ 2

/-- At `h = 1` the inflated envelope is the landed one (the compat direction). -/
theorem RSanDoorRhoH_one (ρ : ℝ) (H : ℕ) : RSanDoorRhoH ρ 1 H = RSanDoorRho ρ H := by
  simp only [RSanDoorRhoH, RSanDoorRho, strataResidualH_one]

theorem RSanDoorRhoH_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (h H : ℕ) : 0 ≤ RSanDoorRhoH ρ h H :=
  div_nonneg hρ (sq_nonneg _)

/-- `1 ≤ strataResidualH h H` once the inflated cap is `≥ 1`. -/
theorem one_le_strataResidualH {h H : ℕ} (h1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H) :
    1 ≤ strataResidualH h H := by
  unfold strataResidualH
  have := Real.log_nonneg h1
  linarith

/-- `3 ≤ H` from `1 < log H`. -/
theorem three_le_of_one_lt_log {H : ℕ} (hL1 : 1 < Real.log (H : ℝ)) : 3 ≤ H := by
  by_contra hcon
  have hH2 : (H : ℝ) ≤ 2 := by exact_mod_cast (by omega : H ≤ 2)
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  have hlog : Real.log (H : ℝ) ≤ Real.log 2 := by
    rcases eq_or_lt_of_le hH0 with hz | hz
    · rw [← hz, Real.log_zero]; exact Real.log_nonneg (by norm_num)
    · exact Real.log_le_log hz hH2
  have := Real.log_two_lt_d9
  linarith

/-- `1 ≤ h · arcDen 12 H` at the ceiling's own floor `50 ≤ loglog H` and `0 < h`. -/
theorem one_le_hArcDen_of_loglog {h H : ℕ} (hh : 0 < h) (hL0 : 0 ≤ Real.log (H : ℝ))
    (hlam : 50 ≤ Real.log (Real.log (H : ℝ))) : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := by
  have hL1 : 1 < Real.log (H : ℝ) := one_lt_log_of_loglog_ge hL0 (by norm_num) hlam
  have harc : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen (by norm_num) (three_le_of_one_lt_log hL1)
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  nlinarith

/-- **⟦THE CEILING, MET AT `ρ` AND SHIFT `h`⟧** (`m4_arith_rs_ceiling_met_rhoH`) —
`m4_arith_rs_ceiling_met_rho` with the drift gate's residual at `strataResidualH h H` and the
envelope at `RSanDoorRhoH ρ h H`.  The square cancels EXACTLY, leaving the `h`-free
`96(1+2π)²·(108/5)·ρ = 109,994·ρ ≤ 110525·ρ ≤ δ₀²` — the SAME constant as at `h = 1`, for
every `h`.  (The `h = 2` ceiling `m4_arith_rs_ceiling_met_rhoH_two`, which kept the grades in
the base residual and paid `log 2` by a ratio, is RETAINED and now UNCONSUMED; this is its
successor.) -/
theorem m4_arith_rs_ceiling_met_rhoH {h : ℕ} (hh : 0 < h) {ρ δ₀ : ℝ} (hρ : 0 < ρ)
    (hρδ : 110525 * ρ ≤ δ₀ ^ 2)
    {H : ℕ} (hL0 : 0 ≤ Real.log (H : ℝ)) (hlam : 50 ≤ Real.log (Real.log (H : ℝ))) :
    96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 * (108 / 5 * RSanDoorRhoH ρ h H)
      ≤ δ₀ ^ 2 := by
  have hstrpos : (0 : ℝ) < strataResidualH h H := by
    have := one_le_strataResidualH (one_le_hArcDen_of_loglog hh hL0 hlam)
    linarith
  have hcancel : strataResidualH h H ^ 2 * (108 / 5 * RSanDoorRhoH ρ h H) = 108 / 5 * ρ := by
    rw [RSanDoorRhoH]
    field_simp
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq : (1 + 2 * Real.pi) ^ 2 ≤ 53.3 := by nlinarith
  have hrho0 : (0 : ℝ) ≤ 108 / 5 * ρ := by positivity
  calc 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 * (108 / 5 * RSanDoorRhoH ρ h H)
      = 96 * (1 + 2 * Real.pi) ^ 2
          * (strataResidualH h H ^ 2 * (108 / 5 * RSanDoorRhoH ρ h H)) := by ring
    _ = 96 * (1 + 2 * Real.pi) ^ 2 * (108 / 5 * ρ) := by rw [hcancel]
    _ ≤ 96 * 53.3 * (108 / 5 * ρ) := mul_le_mul_of_nonneg_right (by nlinarith) hrho0
    _ ≤ 110525 * ρ := by nlinarith
    _ ≤ δ₀ ^ 2 := hρδ

/-- **⟦THE CEILING, MET AT THE CONSUMER'S `ρ`, AT SHIFT `h`⟧** — `m4_arith_rs_ceiling_met_of_delta`
at the inflated residual: at `ρ := doorRhoOfDelta δ₀` the ceiling holds from `δ₀ ≠ 0` alone. -/
theorem m4_arith_rs_ceiling_met_of_deltaH {h : ℕ} (hh : 0 < h) {δ₀ : ℝ} (hδ : δ₀ ≠ 0)
    {H : ℕ} (hL0 : 0 ≤ Real.log (H : ℝ)) (hlam : 50 ≤ Real.log (Real.log (H : ℝ))) :
    96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
        * (108 / 5 * RSanDoorRhoH (doorRhoOfDelta δ₀) h H)
      ≤ δ₀ ^ 2 :=
  m4_arith_rs_ceiling_met_rhoH hh (doorRhoOfDelta_pos hδ) (doorRhoOfDelta_spec δ₀) hL0 hlam

/-! ## §1 — S12: the envelope price at the inflated cap (word 2) -/

/-- **⟦THE `H`-SIDE PRICE AT SHIFT `h`⟧** (`hArcDen_mul_strataResidualH_sq_le`) —
`h · arcDen 12 H · strataResidualH h H² ≤ e^{14·loglog H}` under `hh7 : log h ≤ 7`.

With `L := loglog H ≥ 50`: `arcDen = e^{12L}`, `strataResidualH = 1 + 12L + log h ≤ 8 + 12L ≤
2·e^{L−5}` (the landed `one_add_twelve_le_exp` at `l = L − 5 ≥ 44`), and `h ≤ e⁷`, so the
product is at most `e⁷·e^{12L}·4·e^{2L−10} = 4e^{−3}·e^{14L} < e^{14L}`.  The obligation
`√h·(1 + 12L + log h) ≤ e^L` has ~17 orders of room at `L = 50`. -/
theorem hArcDen_mul_strataResidualH_sq_le {h H : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    (hL0 : 0 ≤ Real.log (H : ℝ)) (hlam : 50 ≤ Real.log (Real.log (H : ℝ))) :
    (h : ℝ) * arcDen 12 H * strataResidualH h H ^ 2
      ≤ Real.exp (14 * Real.log (Real.log (H : ℝ))) := by
  set L : ℝ := Real.log (Real.log (H : ℝ)) with hLdef
  have hL1 : 1 < Real.log (H : ℝ) := one_lt_log_of_loglog_ge hL0 (by norm_num) hlam
  have hL : 0 < Real.log (H : ℝ) := by linarith
  have harc : arcDen 12 H = Real.exp (12 * L) := by
    rw [arcDen, Real.rpow_def_of_pos hL, ← hLdef]
    congr 1
    ring
  have hsH : strataResidualH h H = strataResidual H + Real.log (h : ℝ) :=
    strataResidualH_eq hh hL
  have hstr : strataResidual H = 1 + 12 * L := strataResidual_eq_of_pos hL
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hhle : (h : ℝ) ≤ Real.exp 7 := by
    rw [← Real.exp_log hh0]
    exact Real.exp_le_exp.mpr hh7
  have hlogh0 : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  -- `8 + 12L ≤ 2·e^{L−5}`
  have hb : 1 + 12 * (L - 5) ≤ Real.exp (L - 5) := one_add_twelve_le_exp (by linarith)
  have hres : strataResidualH h H ≤ 2 * Real.exp (L - 5) := by
    rw [hsH, hstr]; linarith
  have hres0 : 0 ≤ strataResidualH h H := by rw [hsH, hstr]; linarith
  have hsq : strataResidualH h H ^ 2 ≤ 4 * Real.exp (L - 5) ^ 2 := by
    have h2 := pow_le_pow_left₀ hres0 hres 2
    calc strataResidualH h H ^ 2 ≤ (2 * Real.exp (L - 5)) ^ 2 := h2
      _ = 4 * Real.exp (L - 5) ^ 2 := by ring
  have hE : Real.exp 7 * Real.exp (12 * L) * (4 * Real.exp (L - 5) ^ 2)
      = 4 * Real.exp (14 * L - 3) := by
    have hE' : Real.exp 7 * Real.exp (12 * L) * Real.exp (L - 5) ^ 2
        = Real.exp (14 * L - 3) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [← hE']
    ring
  have he3 : (4 : ℝ) ≤ Real.exp 3 := by
    have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h3 : Real.exp 3 = (Real.exp 1) ^ (3 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7 : ℝ) ^ (3 : ℕ) ≤ (Real.exp 1) ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) h1.le 3
    have hn : (4 : ℝ) ≤ (2.7 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [h3]; linarith
  have h4 : 4 * Real.exp (14 * L - 3) ≤ Real.exp (14 * L) := by
    rw [Real.exp_sub, mul_div_assoc']
    rw [div_le_iff₀ (Real.exp_pos 3)]
    have := Real.exp_pos (14 * L)
    nlinarith
  have harc0 : (0 : ℝ) ≤ arcDen 12 H := arcDen_nonneg 12 H
  have hsq0 : (0 : ℝ) ≤ strataResidualH h H ^ 2 := sq_nonneg _
  calc (h : ℝ) * arcDen 12 H * strataResidualH h H ^ 2
      ≤ Real.exp 7 * arcDen 12 H * strataResidualH h H ^ 2 := by
        gcongr
    _ = Real.exp 7 * Real.exp (12 * L) * strataResidualH h H ^ 2 := by rw [harc]
    _ ≤ Real.exp 7 * Real.exp (12 * L) * (4 * Real.exp (L - 5) ^ 2) := by
        gcongr
    _ = 4 * Real.exp (14 * L - 3) := hE
    _ ≤ Real.exp (14 * L) := h4

/-- **⟦THE PRICING AT THE POOL, AT `ρ`, AT THE LINEAR DOOR, AT SHIFT `h`⟧**
(`a2DoorGrade_pool_L_priced_rho` at the inflated cap).  Budget `ρ/2 + 4·(ρ/8) = ρ`, unchanged;
the `H`-side price is `hArcDen_mul_strataResidualH_sq_le`; the five summand prices read no cap. -/
theorem a2DoorGrade_pool_L_priced_rhoH {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {M H j : ℕ} {X C₁ M₀ K ρ π₀ : ℝ}
    (hfr : DoorArithFrameRho_L M H j X C₁ M₀ K ρ) (hpool : 0 ≤ π₀)
    (hprice : 188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2) :
    (h : ℝ) * arcDen 12 H * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
      ≤ RSanDoorRhoH ρ h H := by
  have hLX : 1 < Real.log X := hfr.one_lt_logX
  have hLrho : 0 ≤ Real.log (1 / ρ) := hfr.logInvRho_nonneg
  have hstrpos : (0 : ℝ) < strataResidualH h H := by
    have := one_le_strataResidualH (one_le_hArcDen_of_loglog hh hfr.logH_nonneg hfr.Hfloor)
    linarith
  have hgrade0 : (0 : ℝ) ≤ a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
    refine a2DoorGrade_pool_L_nonneg hfr.Mpos (by linarith) ?_ hpool
    have : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    push_cast
    exact this
  have hwt := hArcDen_mul_strataResidualH_sq_le hh hh7 hfr.logH_nonneg hfr.Hfloor
  rw [RSanDoorRhoH, le_div_iff₀ (pow_pos hstrpos 2)]
  have hkey : (h : ℝ) * arcDen 12 H * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
        * strataResidualH h H ^ 2
      ≤ Real.exp (14 * Real.log (Real.log (H : ℝ)))
          * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
    have hid : (h : ℝ) * arcDen 12 H * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
          * strataResidualH h H ^ 2
        = ((h : ℝ) * arcDen 12 H * strataResidualH h H ^ 2)
            * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right hwt hgrade0
  refine le_trans hkey ?_
  have h1 := doorGrade_summand1_priced_rho (H := H) hfr.rho_pos hfr.C1_nonneg hfr.logX_nonneg
    hLX hfr.M0_window
  have h2 := doorGrade_summand2_priced_rho_L (H := H) hfr.rho_pos hfr.Mpos hfr.anchor
  have h3 := doorGrade_summand3_priced_rho_pool (H := H) hprice
  have h4 := doorGrade_summand4_priced_rho (H := H) hfr.rho_pos hLrho hLX hfr.Hfloor
    hfr.armWeak
  have h5 := doorGrade_summand5_priced_rho (H := H) (j := j) hfr.rho_pos hLrho hfr.Hfloor
    hfr.jfloor
  rw [a2DoorGrade_pool_L]
  ring_nf
  ring_nf at h1 h2 h3 h4 h5
  linarith

/-- `a2DoorGrade_pool_L_priced_rhoH`, at the lever (`a2Level1_L` is K-invariant). -/
theorem a2DoorGrade_pool_L_priced_rhoH_gk (K : ℕ) {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {M H j : ℕ} {X C₁ M₀ Kar ρ π₀ : ℝ}
    (hfr : DoorArithFrameRho_L M H j X C₁ M₀ Kar ρ) (hpool : 0 ≤ π₀)
    (hprice : 188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2) :
    (h : ℝ) * arcDen 12 H * a2DoorGrade_pool_L_gk K M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
      ≤ RSanDoorRhoH ρ h H := by
  have heq : a2DoorGrade_pool_L_gk K M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
      = a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := rfl
  rw [heq]
  exact a2DoorGrade_pool_L_priced_rhoH hh hh7 hfr hpool hprice

/-- **⟦THE PRICE WRAPPER, PER INFLATED SOCKET BASE⟧** (`price_at_constPool_socket_L` at
`SocketBaseLH h`) — discharged by the socket's own window field `H ≤ R.Hhi` (conjuncts 1–2;
cap-blind). -/
theorem price_at_constPool_socketH_L {h : ℕ} {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ}
    {K ρ : ℝ}
    (harith : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) :
    ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      188133 * constPool ρ R.Hhi * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2 := by
  intro H L q j A s hb
  have hfr := harith H L q j A s hb
  have hhi : H ≤ R.Hhi := hb.2.1
  have hHpos : 0 < H := by
    have := R.hHlo_floor
    have := hb.1
    omega
  have hlogH : (0 : ℝ) < Real.log (H : ℝ) := by have := hfr.one_lt_logH; linarith
  exact price_at_constPool hfr.rho_pos (loglog_le_of_le hHpos hlogH hhi)

/-- `m4_arith_henv_rho_pool_L_gk` at the inflated socket: `henv` at the inflated cap and the
inflated envelope. -/
theorem m4_arith_henv_rho_poolH_L_gk (K : ℕ) {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {R : ChowlaRegime} {M : ℕ} {C₁ M₀ π₀ : ℕ → ℝ} {Kar ρ : ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (harith : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ)
    (hprice : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      188133 * π₀ (A + s) * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2) :
    ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      (h : ℝ) * arcDen 12 H
          * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
        ≤ RSanDoorRhoH ρ h H :=
  fun H L q j A s hb =>
    a2DoorGrade_pool_L_priced_rhoH_gk K hh hh7 (harith H L q j A s hb) (hpool (A + s))
      (hprice H L q j A s hb)

/-- **⟦THE ARITHMETIC GATE AT THE CONSTANT POOL, AT SHIFT `h`⟧**
(`m4_arith_henv_constPool_L_gk` at the inflated socket). -/
theorem m4_arith_henv_constPoolH_L_gk (K : ℕ) {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {Kar ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (harith : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) :
    ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      (h : ℝ) * arcDen 12 H
          * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
              (M₀ (A + s)) (constPool ρ R.Hhi)
        ≤ RSanDoorRhoH ρ h H :=
  m4_arith_henv_rho_poolH_L_gk K hh hh7 (π₀ := fun _ => constPool ρ R.Hhi)
    (fun _ => constPool_nonneg hρ) harith (price_at_constPool_socketH_L harith)


/-! ## §2 — the socket helpers at the inflated base

`SocketBase`'s x-scale field `x ≤ 16·ω·arcDen·A` is read by `s13_socketBase_xscale` and
everything above it; at `SocketBaseLH h` the field is `x ≤ 16·ω·(h·arcDen)·A`, so each
descendant loses exactly `log h ≤ 7` in the log against slack of `10²¹` and more.  Each is the
landed proof with the one extra term absorbed.  Conjuncts 1–4, 6–10, 12–13 read identically. -/

/-- `s13_socketBase_xscale` at the inflated socket: `(4^{⌊ε²H₊⌋₊})² ≤ 2·(h·arcDen 12 H)·A`. -/
theorem s13_socketBase_xscale_LH {h : ℕ} {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseLH h R M H L q j A s) :
    ((4 ^ ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) ^ 2 ≤ 2 * ((h : ℝ) * arcDen 12 H) * (A : ℝ) := by
  have hx : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * ((h : ℝ) * arcDen 12 H) * (A : ℝ) :=
    hb.2.2.2.2.2.2.2.2.2.2.1
  have hhead := R.hPHheadroom
  have hω : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
  set c : ℝ := (h : ℝ) * arcDen 12 H with hc
  have hc0 : (0 : ℝ) ≤ c := hArcDen_nonneg h H
  nlinarith [hx, hhead, hω, hc0]

/-- `s13_socketBase_logA_ge_sqrt` at the inflated socket — `√H ≤ log A`; the `log h ≤ 7` the
x-scale loses is absorbed by the `2000 ≤ √H` floor's margin. -/
theorem s13_socketBase_logA_ge_sqrt_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
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
  -- ⟦the x-scale, in logs, at the inflated cap⟧
  set m : ℕ := ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ with hm
  have hxs : ((4 ^ m : ℕ) : ℝ) ^ 2 ≤ 2 * ((h : ℝ) * arcDen 12 H) * (A : ℝ) :=
    s13_socketBase_xscale_LH hb
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hAR : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hL12 : (0 : ℝ) < Real.log (H : ℝ) ^ (12 : ℕ) := by positivity
  have hhl : (0 : ℝ) < (h : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ) := mul_pos hh0 hL12
  have hlhs0 : (0 : ℝ) < ((4 ^ m : ℕ) : ℝ) ^ 2 := by positivity
  have hlog := Real.log_le_log hlhs0 hxs
  have hL : Real.log (((4 ^ m : ℕ) : ℝ) ^ 2) = 4 * (m : ℝ) * Real.log 2 := by
    have h4 : ((4 ^ m : ℕ) : ℝ) = (4 : ℝ) ^ m := by push_cast; ring
    rw [h4, ← pow_mul, Real.log_pow, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hRR : Real.log (2 * ((h : ℝ) * arcDen 12 H) * (A : ℝ))
      = Real.log 2 + Real.log (h : ℝ) + 12 * Real.log (Real.log (H : ℝ)) + Real.log (A : ℝ) := by
    rw [harcpow, Real.log_mul (mul_pos two_pos hhl).ne' hAR.ne', Real.log_mul two_ne_zero hhl.ne',
      Real.log_mul hh0.ne' hL12.ne', Real.log_pow]
    push_cast; ring
  rw [hL, hRR] at hlog
  have hlog' : 4 * (m : ℝ) * Real.log 2
      ≤ Real.log 2 + 7 + 12 * Real.log (Real.log (H : ℝ)) + Real.log (A : ℝ) := by linarith
  have hmfl : 2 * u - 1 ≤ (m : ℝ) := by rw [hm, hu]; exact s13_socketBase_mFloor hhi
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  nlinarith [hlog', hmfl, hllH, hwu, hw2000, hu2000, hl2lo, hl2hi, hu0, hw0]

/-- `s13_socketBase_loglogA_sharp` at the inflated socket. -/
theorem s13_socketBase_loglogA_sharp_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    Real.log (H : ℝ) / 2 ≤ Real.log (Real.log (A : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  set u : ℝ := Real.sqrt (H : ℝ) with hu
  have hu0 : (0 : ℝ) < u := by rw [hu]; exact Real.sqrt_pos.mpr (by linarith)
  have hmain : u ≤ Real.log (A : ℝ) := s13_socketBase_logA_ge_sqrt_LH hh hh7 hfl hb
  have hlogu : Real.log u = Real.log (H : ℝ) / 2 := by
    rw [hu]; exact Real.log_sqrt (by positivity)
  have hmono := Real.log_le_log hu0 hmain
  rw [hlogu] at hmono
  linarith

/-- `s13_socketBase_loglogA` at the inflated socket. -/
theorem s13_socketBase_loglogA_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
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
  have hmain : u ≤ Real.log (A : ℝ) := s13_socketBase_logA_ge_sqrt_LH hh hh7 hfl hb
  exact ⟨le_trans hu2000 hmain,
    by have := s13_socketBase_loglogA_sharp_LH hh hh7 hfl hb; linarith⟩

/-- `s14_loglogX_ge_of_socket` at the inflated socket. -/
theorem s14_loglogX_ge_of_socket_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    Real.log (H : ℝ) / 2 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hsharp := s13_socketBase_loglogA_sharp_LH hh hh7 hfl hb
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA_LH hh hh7 hfl hb
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hmono : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := Real.log_le_log hA0 hAX
  have h := Real.log_le_log (by linarith : (0 : ℝ) < Real.log (A : ℝ)) hmono
  linarith

/-- `s12c_llX_ge` at the inflated socket. -/
theorem s12c_llX_ge_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) / 2
      ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ R.Hlo := R.hHlo_floor
  have hHR : (4000000 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast hH4
  have hlogHlopos : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hcast : ((R.Hlo : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo
  have hmono : Real.log ((R.Hlo : ℕ) : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hcast
  have hsharp := s14_loglogX_ge_of_socket_LH hh hh7 hfl hb
  rw [Real.exp_log hlogHlopos]
  linarith

/-- `s15_block_at_socket_gen` at the inflated socket: `2^E ≤ A + s`.  The `log h ≤ 7` is
absorbed by the `18·loglog H₊` against `12·loglog H` margin (`≥ 0.47·50 > 7`). -/
theorem s15_block_at_socket_gen_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {R : ChowlaRegime} {M H L q j A s E : ℕ}
    (hb : SocketBaseLH h R M H L q j A s)
    (hHreg : 0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hblk : ((E : ℕ) : ℝ) + 1 + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)) :
    2 ^ E ≤ A + s := by
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) :=
    lt_of_lt_of_le (by norm_num) (one_lt_log_of_loglog_ge hHreg.1 (by norm_num) hHreg.2).le
  have hllH : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) :=
    s13_loglog_le_of_range (R := R) hlo hhi
  set m : ℕ := ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ with hm
  have hxs : ((4 ^ m : ℕ) : ℝ) ^ 2 ≤ 2 * ((h : ℝ) * arcDen 12 H) * (A : ℝ) :=
    s13_socketBase_xscale_LH hb
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hL12 : (0 : ℝ) < Real.log (H : ℝ) ^ (12 : ℕ) := by positivity
  have hhl : (0 : ℝ) < (h : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ) := mul_pos hh0 hL12
  have hlhs0 : (0 : ℝ) < ((4 ^ m : ℕ) : ℝ) ^ 2 := by positivity
  have hlog := Real.log_le_log hlhs0 hxs
  have hLid : Real.log (((4 ^ m : ℕ) : ℝ) ^ 2) = 4 * (m : ℝ) * Real.log 2 := by
    have h4 : ((4 ^ m : ℕ) : ℝ) = (4 : ℝ) ^ m := by push_cast; ring
    rw [h4, ← pow_mul, Real.log_pow, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hRR : Real.log (2 * ((h : ℝ) * arcDen 12 H) * (A : ℝ))
      = Real.log 2 + Real.log (h : ℝ) + 12 * Real.log (Real.log (H : ℝ)) + Real.log (A : ℝ) := by
    rw [harcpow, Real.log_mul (mul_pos two_pos hhl).ne' hApos.ne', Real.log_mul two_ne_zero hhl.ne',
      Real.log_mul hh0.ne' hL12.ne', Real.log_pow]
    push_cast; ring
  rw [hLid, hRR] at hlog
  have hlog' : 4 * (m : ℝ) * Real.log 2
      ≤ Real.log 2 + 7 + 12 * Real.log (Real.log (H : ℝ)) + Real.log (A : ℝ) := by linarith
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hE : ((E : ℕ) : ℝ) * Real.log 2 ≤ Real.log (A : ℝ) := by
    nlinarith [hblk, hlog', hllH, hHreg.2, hl2lo, hl2hi]
  have hpow : ((2 : ℝ)) ^ E ≤ (A : ℝ) := by
    have hlt : Real.log (((2 : ℝ)) ^ E) ≤ Real.log (A : ℝ) := by
      rw [Real.log_pow]; linarith
    exact (Real.log_le_log_iff (by positivity) hApos).mp hlt
  have hcast : ((2 ^ E : ℕ) : ℝ) ≤ (A : ℝ) := by push_cast; exact hpow
  have hnat : (2 : ℕ) ^ E ≤ A := by exact_mod_cast hcast
  omega

/-- `s13_band_X400` at the inflated socket — conjuncts 7 and 9 only (cap-blind); the LINEAR row
floor `doorRowFloorL M = M·2^36·M ≥ 2^36 ≥ 2^9`. -/
theorem s13_band_X400_LH {h : ℕ} {R : ChowlaRegime} {M H L q j A s : ℕ} (hM : 1 ≤ M)
    (hb : SocketBaseLH h R M H L q j A s) : (400 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
  have hj : doorRowFloorL M ≤ j := hb.2.2.2.2.2.2.1
  have hAj : 2 ^ j ≤ A := hb.2.2.2.2.2.2.2.2.1
  have h9 : 9 ≤ j := by
    have h36 : 2 ^ 36 ≤ doorRowFloorL M := by
      rw [doorRowFloorL, AdoorL]
      calc (2 : ℕ) ^ 36 = 1 * (2 ^ 36 * 1) := by ring
        _ ≤ M * (2 ^ 36 * M) := Nat.mul_le_mul hM (Nat.mul_le_mul le_rfl hM)
    have h2 : (2 : ℕ) ^ 36 = 68719476736 := by norm_num
    omega
  have h512 : (512 : ℕ) ≤ A := by
    calc (512 : ℕ) = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h9
      _ ≤ A := hAj
  have : (512 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    have h : (512 : ℕ) ≤ A + s := by omega
    exact_mod_cast h
  linarith

/-- `s13_band_baseFloor_L` at the inflated socket — conjuncts 7 and 9 only (cap-blind). -/
theorem s13_band_baseFloor_LH {h : ℕ} {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseLH h R M H L q j A s) :
    Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have hj : doorRowFloorL M ≤ j := hb.2.2.2.2.2.2.1
  have hAj : 2 ^ j ≤ A := hb.2.2.2.2.2.2.2.2.1
  have hpow : (2 : ℕ) ^ doorRowFloorL M ≤ A + s := by
    have : (2 : ℕ) ^ doorRowFloorL M ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    omega
  have hR : ((2 : ℝ)) ^ (doorRowFloorL M) ≤ (((A + s : ℕ)) : ℝ) := by
    have h : ((2 ^ doorRowFloorL M : ℕ) : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by exact_mod_cast hpow
    simpa using h
  have h0 : (0 : ℝ) < ((2 : ℝ)) ^ (doorRowFloorL M) := by positivity
  have := Real.log_le_log h0 hR
  rwa [Real.log_pow, mul_comm] at this

/-! ## §3 — the four bridge restatements at the inflated socket (word 5)

At `h = 1` these are consumed THROUGH `socketBase_of_socketBaseL`; no `SocketBaseH` exists and
none can at `h ≥ 2`, so each is restated at `SocketBaseLH h` over the `_LH` helpers of §2. -/

/-- `s12c_eps_threshold_at_socket_flat` at the inflated socket. -/
theorem s12c_eps_threshold_at_socket_flatH {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ ε : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000)
    (hε : ε ≤ theta293 - 1 / 500) :
    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
      ≤ (theta293 - ε) * Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hll := s12c_llX_ge_LH hh hh7 hfl hb
  have hcore := flat_lambda_core hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by linarith
  have hcoef : (1 : ℝ) / 500 ≤ theta293 - ε := by linarith
  have hprod : (1 : ℝ) / 500 * ll ≤ (theta293 - ε) * ll :=
    mul_le_mul_of_nonneg_right hcoef hll0
  have h1 : 14 * Λ ≤ 14 * Real.exp (lam / 2) := by linarith
  linarith

/-- `s15_heps293_at_socket_flat` at the inflated socket. -/
theorem s15_heps293_at_socket_flatH {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hρ : 0 < ρ)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000) :
    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi := by
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA_LH hh hh7 hfl hb
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpool : constPool ρ R.Hhi = Real.exp (Real.log ρ - Real.log 376266 - 14 * Λ) := by
    rw [constPool_def, hLamdef, Real.exp_sub, Real.exp_sub, Real.exp_log hρ,
      Real.exp_log (by norm_num : (0 : ℝ) < 376266), div_div]
  have hlhs : (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) = Real.exp (-(theta293 * ll)) := by
    rw [Real.rpow_def_of_pos hX0, hlldef]; congr 1; ring
  rw [hlhs, hpool]
  refine Real.exp_le_exp.mpr ?_
  have hθ : (0.0034 : ℝ) ≤ theta293 := by have := s13_theta293_margin_lo; linarith
  have hll := s12c_llX_ge_LH hh hh7 hfl hb
  have hcore := flat_lambda_core_17 hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by
    have : (0 : ℝ) < Real.exp lam / 2 := by positivity
    linarith [hll]
  have hkey : 14 * Λ + 13 + (-Real.log ρ) ≤ theta293 * ll := by
    have h1 : 14 * Λ ≤ 14 * Real.exp (lam / 2) := by linarith [htow]
    have h2 : theta293 * ll ≥ 0.0034 * (Real.exp lam / 2) := by
      nlinarith [hθ, hll, hll0]
    nlinarith [h1, h2, hcore, hrho]
  linarith [hkey, hlog376]

/-- `s15_hband4096_at_socket_flat` at the inflated socket. -/
theorem s15_hband4096_at_socket_flatH {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hρ : 0 < ρ)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000) :
    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500) * constPool ρ R.Hhi := by
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA_LH hh hh7 hfl hb
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpool : constPool ρ R.Hhi = Real.exp (Real.log ρ - Real.log 376266 - 14 * Λ) := by
    rw [constPool_def, hLamdef, Real.exp_sub, Real.exp_sub, Real.exp_log hρ,
      Real.exp_log (by norm_num : (0 : ℝ) < 376266), div_div]
  have hlhs : (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
      = Real.exp ((1 - (1 : ℝ) / 500) * ll) := by
    rw [Real.rpow_def_of_pos hX0, hlldef]; congr 1; ring
  rw [hlhs, hpool, ← Real.exp_add]
  have h4096 : (4096 : ℝ) ≤ Real.exp 9 := by
    have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7 : ℝ) ^ (9 : ℕ) ≤ (Real.exp 1) ^ (9 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 9
    have hn : (4096 : ℝ) ≤ (2.7 : ℝ) ^ (9 : ℕ) := by norm_num
    rw [h]; linarith
  refine le_trans h4096 (Real.exp_le_exp.mpr ?_)
  have hll := s12c_llX_ge_LH hh hh7 hfl hb
  have hcore := flat_lambda_core_17 hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by
    have : (0 : ℝ) < Real.exp lam / 2 := by positivity
    linarith [hll]
  have h1 : 14 * Λ ≤ 14 * Real.exp (lam / 2) := by linarith [htow]
  have h2 : (1 - (1 : ℝ) / 500) * ll ≥ 0.0017 * Real.exp lam := by nlinarith [hll, hll0]
  nlinarith [h1, h2, hcore, hrho, hlog376]

/-- `s15_block_at_socket_L_gk` at the inflated socket. -/
theorem s15_block_at_socketH_L_gk (K : ℕ) {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseLH h R M H L q j A s)
    (hHreg : 0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hblk : ((s13BlockExp_L_gk K M : ℕ) : ℝ) + 1
        + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)) :
    s13BlockFloor_L_gk K M ≤ A + s := by
  rw [s13BlockFloor_L_gk]
  exact s15_block_at_socket_gen_LH hh hh7 hb hHreg hblk

/-! ## §4 — S2: the compose's arm and the `ρ`-frame at the inflated socket (word 3)

The register's free slot is `∀ g, ∃ R, … g R.Hhi R.ω ≤ R.x …` with `ω` the slot's SECOND
argument; the `ρ`-frame's arm at the inflated socket is `gArmDoorRho 0 0 (h·ω) ρ H`, because
`16·ω·(h·arcDen)·A = 16·(h·ω)·arcDen·A` — the inflated x-floor IS the landed `g`-floor at
`ω ↦ h·ω`, and `m4_arith_arm_of_gArmRho` applies verbatim there. -/

/-- **⟦THE COMPOSE'S `g`-ARM AT SHIFT `h`⟧** (`s15ArmH h δ₀ ρ`) — `s15Arm` with the `ρ`-summand
read at `h·ω`. -/
def s15ArmH (h : ℕ) (δ₀ ρ : ℝ) : ℕ → ℕ → ℕ := fun Hhi ω =>
  s13GArm' δ₀ Hhi ω + ⌈gArmDoorRho 0 0 ((h : ℝ) * (ω : ℝ)) ρ Hhi⌉₊

/-- At `h = 1` the inflated arm is the landed one. -/
theorem s15ArmH_one (δ₀ ρ : ℝ) : s15ArmH 1 δ₀ ρ = s15Arm δ₀ ρ := by
  funext Hhi ω
  simp only [s15ArmH, s15Arm, Nat.cast_one, one_mul]

/-- The demoted arm sits under `s15ArmH`. -/
theorem s15ArmH_demoted (h : ℕ) (δ₀ ρ : ℝ) (Hhi ω : ℕ) :
    s13GArm' δ₀ Hhi ω ≤ s15ArmH h δ₀ ρ Hhi ω := by
  rw [s15ArmH]; omega

/-- The `ρ`-frame's arm at `h·ω` sits under `s15ArmH`, in the reals (`s15Arm_rho` at `h`). -/
theorem s15ArmH_rho {h : ℕ} {δ₀ ρ : ℝ} {Hhi ω x : ℕ} (hx : s15ArmH h δ₀ ρ Hhi ω ≤ x) :
    gArmDoorRho 0 0 ((h : ℝ) * (ω : ℝ)) ρ Hhi ≤ (x : ℝ) := by
  have hc : ⌈gArmDoorRho 0 0 ((h : ℝ) * (ω : ℝ)) ρ Hhi⌉₊ ≤ x := by rw [s15ArmH] at hx; omega
  have hcR : ((⌈gArmDoorRho 0 0 ((h : ℝ) * (ω : ℝ)) ρ Hhi⌉₊ : ℕ) : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast hc
  exact le_trans (Nat.le_ceil _) hcR

/-- `gArmDoorRho 0 0 (h·ω) ρ H ≤ h · gArmDoorRho 0 0 ω ρ H` for `0 ≤ h` — the `ρ`-arm is
`h`-homogeneous at `x₀ = 0`. -/
theorem gArmDoorRho_zero_mul_le {h ω ρ : ℝ} (hh : 0 ≤ h) (H : ℕ) :
    gArmDoorRho 0 0 (h * ω) ρ H ≤ h * gArmDoorRho 0 0 ω ρ H := by
  rw [gArmDoorRho, gArmDoorRho]
  have harc0 : (0 : ℝ) ≤ arcDen 12 H := arcDen_nonneg 12 H
  refine max_le (by positivity) ?_
  have hmax := le_max_right (0 : ℝ) (16 * ω * arcDen 12 H
      * Real.exp (Real.exp (7000 * Real.log (Real.log (H : ℝ))
        + 500 * Real.log (1 / ρ) + 6600 + 36 * 0)))
  have hid : 16 * (h * ω) * arcDen 12 H
      * Real.exp (Real.exp (7000 * Real.log (Real.log (H : ℝ))
        + 500 * Real.log (1 / ρ) + 6600 + 36 * 0))
      = h * (16 * ω * arcDen 12 H
        * Real.exp (Real.exp (7000 * Real.log (Real.log (H : ℝ))
          + 500 * Real.log (1 / ρ) + 6600 + 36 * 0))) := by ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left hmax hh

/-- `s15ArmH h ≤ h · s15Arm` — the inflated arm is at most `h` times the landed one. -/
theorem s15ArmH_le_mul {h : ℕ} (hh : 0 < h) (δ₀ ρ : ℝ) (Hhi ω : ℕ) :
    s15ArmH h δ₀ ρ Hhi ω ≤ h * s15Arm δ₀ ρ Hhi ω := by
  have h1 : s13GArm' δ₀ Hhi ω ≤ h * s13GArm' δ₀ Hhi ω := Nat.le_mul_of_pos_left _ hh
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
  have h2 : ⌈gArmDoorRho 0 0 ((h : ℝ) * (ω : ℝ)) ρ Hhi⌉₊
      ≤ h * ⌈gArmDoorRho 0 0 (ω : ℝ) ρ Hhi⌉₊ := by
    rw [Nat.ceil_le]
    push_cast
    calc gArmDoorRho 0 0 ((h : ℝ) * (ω : ℝ)) ρ Hhi
        ≤ (h : ℝ) * gArmDoorRho 0 0 (ω : ℝ) ρ Hhi := gArmDoorRho_zero_mul_le hh0 Hhi
      _ ≤ (h : ℝ) * ((⌈gArmDoorRho 0 0 (ω : ℝ) ρ Hhi⌉₊ : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left (Nat.le_ceil _) hh0
  unfold s15ArmH s15Arm
  rw [Nat.mul_add]
  exact Nat.add_le_add h1 h2

/-- **⟦THE ARM'S LOG AT SHIFT `h`⟧** (`s15Arm_log_le` at `h`) — the landed bound plus `log h`,
off `s15ArmH_le_mul`. -/
theorem s15ArmH_log_le {h : ℕ} (hh : 0 < h) {δ₀ Kc : ℝ} (hδ₀ : 0 < δ₀)
    (hδpin : 1 / 838400 ≤ δ₀) (hKc : 0 < Kc) (hKcb : Kc ≤ 2 ^ 539) {Hhi ω : ℕ}
    (hHhi : 4000000 ≤ Hhi) (hΛ : 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ Real.log ((ω : ℕ) : ℝ) + Real.log (h : ℝ) + ((Hhi : ℕ) : ℝ) / 1000000 := by
  have hbase := s15Arm_log_le hδ₀ hδpin hKc hKcb (ω := ω) hHhi hΛ
  have hle := s15ArmH_le_mul hh δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω
  have hleR : ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ (h : ℝ) * ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hω0 : 0 ≤ Real.log ((ω : ℕ) : ℝ) := Real.log_natCast_nonneg ω
  have hh0 : 0 ≤ Real.log (h : ℝ) := Real.log_natCast_nonneg h
  have hHhi0 : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / 1000000 := by positivity
  rcases Nat.eq_zero_or_pos (s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω)
    with hz | hpos
  · rw [hz]; simp only [Nat.cast_zero, Real.log_zero]; linarith
  · have hposR : (0 : ℝ)
        < ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) := by
      exact_mod_cast hpos
    have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    have hbpos : (0 : ℝ)
        < ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) := by
      by_contra hcon
      have hb0 : ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) ≤ 0 :=
        not_lt.mp hcon
      nlinarith [hleR, hposR, hhR, hb0]
    have hlog := Real.log_le_log hposR hleR
    rw [Real.log_mul hhR.ne' hbpos.ne'] at hlog
    linarith

/-- **⟦THE `ρ`-FRAME AT THE INFLATED SOCKET⟧** (`s15_doorArithFrameRho_L_at_socket''` at
`SocketBaseLH h`) — the landed proof with the arm read at `ω ↦ h·ω`: the socket's
`x ≤ 16·ω·(h·arcDen)·A` is `x ≤ 16·(h·ω)·arcDen·A` by `ring`. -/
theorem s15_doorArithFrameRho_L_at_socketH'' {h : ℕ} (hh : 0 < h)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    {C₁ : ℕ → ℝ} (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hanchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33
      ≤ 39 * 10 ^ 8 * (M : ℝ))
    (hHreg : 0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho 0 0 ((h : ℝ) * (R.ω : ℝ)) ρ H ≤ (R.x : ℝ))
    (hC1 : 0 ≤ C₁ (A + s))
    (hb : SocketBaseLH h R M H L q j A s) :
    DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
      (s13BandM0 R ρ C₁ (A + s)) 0 ρ := by
  have hhi : H ≤ R.Hhi := hb.2.1
  have hjd : doorRowFloorL M ≤ j := hb.2.2.2.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hAx : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * ((h : ℝ) * arcDen 12 H) * (A : ℝ) :=
    hb.2.2.2.2.2.2.2.2.2.2.1
  have hAx' : (R.x : ℝ) ≤ 16 * ((h : ℝ) * (R.ω : ℝ)) * arcDen 12 H * (A : ℝ) := by
    have hid : 16 * (R.ω : ℝ) * ((h : ℝ) * arcDen 12 H) * (A : ℝ)
        = 16 * ((h : ℝ) * (R.ω : ℝ)) * arcDen 12 H * (A : ℝ) := by ring
    rw [hid] at hAx
    exact hAx
  have hω : (0 : ℝ) < (R.ω : ℝ) := by
    have : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
    linarith
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hω' : (0 : ℝ) < (h : ℝ) * (R.ω : ℝ) := mul_pos hh0 hω
  have hlrho : (0 : ℝ) ≤ Real.log (1 / ρ) := log_one_div_nonneg hρ0 hρ1
  have hllH : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) :=
    s13_loglog_le_of_range (R := R) hb.1 hhi
  have harmA := m4_arith_arm_of_gArmRho hω' hHreg.1 hHreg.2 hg hAx'
  have hmuA : (356600 : ℝ) ≤ Real.log (Real.log (A : ℝ)) := by
    have := hHreg.2; linarith
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hlogA : (1 : ℝ) < Real.log (A : ℝ) :=
    one_lt_log_of_loglog_ge (log_natCast_nonneg' A) (by norm_num) hmuA
  have harm := m4_arith_arm_of_shift hApos (by linarith) hAX harmA
  have hlogH0 : (0 : ℝ) < Real.log ((H : ℕ) : ℝ) :=
    lt_of_lt_of_le (by norm_num) (one_lt_log_of_loglog_ge hHreg.1 (by norm_num) hHreg.2).le
  have hjn : (68719476736 : ℝ) * (M : ℝ) ≤ (j : ℝ) := by
    have h1 : AdoorL M ≤ doorRowFloorL M := by
      rw [doorRowFloorL]; exact Nat.le_mul_of_pos_left _ hM
    have h2 : 2 ^ 36 * M ≤ j := le_trans h1 (le_trans (le_of_eq rfl) hjd)
    have h3 : ((2 ^ 36 * M : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast h2
    push_cast at h3 ⊢
    linarith
  have hn0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  exact
    { Mpos := hM
      logX_nonneg := log_natCast_nonneg' (A + s)
      logH_nonneg := hHreg.1
      Hfloor := hHreg.2
      Knonneg := le_rfl
      rho_pos := hρ0
      rho_le_one := hρ1
      arm := harm
      anchor := by linarith [hanchor, hllH]
      C1_nonneg := hC1
      M0_window := s13BandM0_window (R := R) (ρ := ρ) (C₁ := C₁) hhi hlogH0
      jfloor := by linarith [hanchor, hllH, hjn, hlrho, hn0, hHreg.2] }

/-- **⟦THE FAMILY FORM AT THE INFLATED SOCKET⟧** (`s15_doorArithFrameRho_L_family''` at `h`). -/
theorem s15_doorArithFrameRho_L_familyH'' {h : ℕ} (hh : 0 < h)
    {R : ChowlaRegime} {M : ℕ} {ρ : ℝ} {C₁ : ℕ → ℝ}
    (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hanchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33
      ≤ 39 * 10 ^ 8 * (M : ℝ))
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 ((h : ℝ) * (R.ω : ℝ)) ρ H ≤ (R.x : ℝ))
    (hC1 : ∀ n : ℕ, 0 ≤ C₁ n) :
    ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) 0 ρ := by
  intro H L q j A s hb
  exact s15_doorArithFrameRho_L_at_socketH'' hh hM hρ0 hρ1 hanchor (hHreg H hb.1 hb.2.1)
    (hg H hb.1 hb.2.1) (hC1 (A + s)) hb

/-! ## §5 — S11: the band base at the inflated socket (word 4) -/

/-- **⟦`qfit` AT SHIFT `h`⟧** (`s13_band_qfit_h`) — `q ≤ (log X_d)^{10}` from
`q ≤ h·(log H)^{12}` and the arm: `log h + 12·λ_H ≤ 7 + 12·λ_H ≤ 10·Λ` under `7000·λ_H ≤ Λ`
and `1 ≤ λ_H`. -/
theorem s13_band_qfit_h {h q H Xd : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    (hq : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H)
    (hH : (0 : ℝ) < Real.log ((H : ℕ) : ℝ)) (hX : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ))
    (hHfl : (1 : ℝ) ≤ Real.log (Real.log ((H : ℕ) : ℝ)))
    (harm : 7000 * Real.log (Real.log ((H : ℕ) : ℝ))
      ≤ Real.log (Real.log ((Xd : ℕ) : ℝ))) :
    (q : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (10 : ℕ) := by
  refine le_trans hq ?_
  have hA : arcDen 12 H = Real.exp (12 * Real.log (Real.log ((H : ℕ) : ℝ))) := by
    rw [arcDen, Real.rpow_def_of_pos hH]; ring_nf
  have hB : (Real.log ((Xd : ℕ) : ℝ)) ^ (10 : ℕ)
      = Real.exp (10 * Real.log (Real.log ((Xd : ℕ) : ℝ))) := by
    rw [← Real.rpow_natCast (Real.log ((Xd : ℕ) : ℝ)) 10, Real.rpow_def_of_pos hX]
    push_cast; ring_nf
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hhe : (h : ℝ) = Real.exp (Real.log (h : ℝ)) := (Real.exp_log hh0).symm
  rw [hA, hB, hhe, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- `s13_band_arm_at_top` at the inflated socket — the arm at `h·ω`. -/
theorem s13_band_arm_at_top_LH {h : ℕ} (hh : 0 < h)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho 0 0 ((h : ℝ) * (R.ω : ℝ)) ρ R.Hhi ≤ (R.x : ℝ))
    (hb : SocketBaseLH h R M H L q j A s) :
    7000 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + 500 * Real.log (1 / ρ) + 6600
      ≤ Real.log (Real.log ((A : ℕ) : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  have hAx : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * ((h : ℝ) * arcDen 12 H) * (A : ℝ) :=
    hb.2.2.2.2.2.2.2.2.2.2.1
  have hω : (0 : ℝ) < (R.ω : ℝ) := by
    have : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
    linarith
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hω' : (0 : ℝ) < (h : ℝ) * (R.ω : ℝ) := mul_pos hh0 hω
  obtain ⟨hlogH0, hlamH⟩ := hHreg H hlo hhi
  obtain ⟨hlogT0, hlamT⟩ := hHreg R.Hhi (le_trans hlo hhi) le_rfl
  have hHpos : (0 : ℝ) < Real.log ((H : ℕ) : ℝ) :=
    lt_of_lt_of_le (by norm_num) (one_lt_log_of_loglog_ge hlogH0 (by norm_num) hlamH).le
  have hH0 : (0 : ℝ) < ((H : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos H with hz | hz
    · rw [hz] at hHpos; norm_num at hHpos
    · exact_mod_cast hz
  have hcast : ((H : ℕ) : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast hhi
  have hlogmono : Real.log ((H : ℕ) : ℝ) ≤ Real.log ((R.Hhi : ℕ) : ℝ) :=
    Real.log_le_log hH0 hcast
  have harc : arcDen 12 H ≤ arcDen 12 R.Hhi := by
    rw [arcDen, arcDen]; exact Real.rpow_le_rpow hHpos.le hlogmono (by norm_num)
  have hApos : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  have hsock : (R.x : ℝ) ≤ 16 * ((h : ℝ) * (R.ω : ℝ)) * arcDen 12 R.Hhi * (A : ℝ) := by
    have hAx' : (R.x : ℝ) ≤ 16 * ((h : ℝ) * (R.ω : ℝ)) * arcDen 12 H * (A : ℝ) := by
      have hid : 16 * (R.ω : ℝ) * ((h : ℝ) * arcDen 12 H) * (A : ℝ)
          = 16 * ((h : ℝ) * (R.ω : ℝ)) * arcDen 12 H * (A : ℝ) := by ring
      rw [hid] at hAx
      exact hAx
    refine le_trans hAx' ?_
    have h1 : 16 * ((h : ℝ) * (R.ω : ℝ)) * arcDen 12 H
        ≤ 16 * ((h : ℝ) * (R.ω : ℝ)) * arcDen 12 R.Hhi := by
      nlinarith [harc, hω']
    nlinarith [h1, hApos]
  have := m4_arith_arm_of_gArmRho (x₀ := 0) (K := 0) hω' hlogT0 hlamT hg hsock
  linarith [this]

/-- `s13_band_err_free` at the inflated socket. -/
theorem s13_band_err_free_LH {h : ℕ} (hh : 0 < h)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ} {C₁ : ℕ → ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hC1lo : (1 : ℝ) ≤ C₁ (A + s)) (hC1hi : C₁ (A + s) ≤ 1)
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho 0 0 ((h : ℝ) * (R.ω : ℝ)) ρ R.Hhi ≤ (R.x : ℝ))
    (hb : SocketBaseLH h R M H L q j A s) :
    4 * Real.log (((A + s : ℕ)) : ℝ) ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.exp (-(1 / (2 * Real.exp 1)) * s13BandM0 R ρ C₁ (A + s)) := by
  have harm := s13_band_arm_at_top_LH hh hHreg hg hb
  obtain ⟨hlogT0, hlamT⟩ := hHreg R.Hhi (le_trans hb.1 hb.2.1) le_rfl
  have hlρ : (0 : ℝ) ≤ Real.log (1 / ρ) := by
    rw [one_div, Real.log_inv]
    have : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
    linarith
  have hA356 : (356600 : ℝ) ≤ Real.log (Real.log ((A : ℕ) : ℝ)) := by linarith
  have hlogA1 : (1 : ℝ) < Real.log ((A : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge (log_natCast_nonneg' A) (by norm_num) hA356
  have hApos : (0 : ℝ) < ((A : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos A with hz | hz
    · rw [hz] at hlogA1; norm_num at hlogA1
    · exact_mod_cast hz
  have hAX : ((A : ℕ) : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hshift := m4_arith_arm_of_shift hApos (by linarith) hAX harm
  have hΛ : (0 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by linarith
  have hμ : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) :=
    lt_trans (by norm_num)
      (one_lt_log_of_loglog_ge (log_natCast_nonneg' (A + s)) (show (0:ℝ) < 356600 by norm_num)
        (by linarith))
  refine s13_band_err_at_pin (R := R) (Xd := A + s) (ρ := ρ) (C₁ := C₁) hμ hΛ ?_
  have hc : Real.log (C₁ (A + s) + 1) ≤ 1 := by
    have h2 : Real.log (C₁ (A + s) + 1) ≤ Real.log 2 :=
      Real.log_le_log (by linarith) (by linarith)
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  set X : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hXdef
  set Y : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hYdef
  set L : ℝ := Real.log (1 / ρ) with hLdef
  set c : ℝ := Real.log (C₁ (A + s) + 1) with hcdef
  linarith [hshift, hlamT, hlρ, hc]

/-- **⟦THE BAND BASE FAMILY AT THE INFLATED SOCKET⟧** (`doorBandBase_family'_L_gk` at
`SocketBaseLH h`).  The band gate's four fields are taken as binders (a `S13BandGate'H`
structure would be a def); `qfit` is `s13_band_qfit_h`, `X400`/`grade` read conjuncts 7 and 9,
`err` reads the arm at `h·ω`. -/
theorem doorBandBase_family'H_L_gk (K : ℕ) {h : ℕ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    {R : ChowlaRegime} {M x₀ : ℕ} {C' Kar ρ : ℝ} {C₁ : ℕ → ℝ}
    (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hC1hi : ∀ n : ℕ, C₁ n ≤ 1)
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho 0 0 ((h : ℝ) * (R.ω : ℝ)) ρ R.Hhi ≤ (R.x : ℝ))
    (harith : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) Kar ρ)
    (hx0 : x₀ ≤ 2 ^ doorRowFloorL M)
    (hC1one : ∀ n : ℕ, (1 : ℝ) ≤ C₁ n)
    (hgrade : 8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
      ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)))
    (hblock : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      s13BlockFloor_L_gk K M ≤ A + s) :
    ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) := by
  intro H L q j A s hbL
  have hfr := harith H L q j A s hbL
  have hΛ : (356600 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := hfr.loglogX_ge
  have hμ : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := lt_trans (by norm_num) hfr.one_lt_logX
  obtain ⟨hbig, h48, h24⟩ := s13_band_floors hμ hΛ
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by linarith
  have hX2 : (2 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hjfl : doorRowFloorL M ≤ j := hbL.2.2.2.2.2.2.1
  have hfive := s13_doorRowZeroBase_five_L_gk K hM (hblock H L q j A s hbL) hjfl
  have hreg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) := hfive.2.1
  refine
    { X400 := s13_band_X400_LH hM hbL
      C₁_one := hC1one (A + s)
      x₀_le := ?_
      qfit := ?_
      gHalf := ?_
      gO1 := ?_
      gWin := ?_
      grade := ?_
      err := ?_ }
  · have hAj : 2 ^ j ≤ A := hbL.2.2.2.2.2.2.2.2.1
    have hpow : (2 : ℕ) ^ doorRowFloorL M ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjfl
    exact le_trans hx0 (le_trans hpow (le_trans hAj (Nat.le_add_right A s)))
  · refine s13_band_qfit_h hh hh7 hbL.2.2.2.2.1 (lt_trans (by norm_num) hfr.one_lt_logH) hμ
      ?_ ?_
    · linarith [hfr.Hfloor]
    · have := hfr.armWeak
      have := hfr.logInvRho_nonneg
      linarith
  · intro k hk1 hk2
    have h := s13_band_gHalf hX2 h48 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · intro k hk1 hk2
    have hQ0 : (0 : ℝ) ≤ Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) := by
      linarith [s13_band_log_calQK_two_ge_L_gk K hM]
    have h := s13_band_gO1 hX2 hQ0 hreg h24 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · intro k hk1 hk2
    have h := s13_band_gWin (by linarith) hX2 (s13_band_loglog_calP_one_L_gk K hM)
      (s13_band_log_calQK_two_ge_L_gk K hM) hreg k hk1 hk2
    simpa only [s13Aexp] using h
  · refine le_trans hgrade ?_
    refine Real.rpow_le_rpow (by positivity) (s13_band_baseFloor_LH hbL) ?_
    rw [s13Aexp]; norm_num
  · exact s13_band_err_free_LH hh hρ0 hρ1 (hC1one (A + s)) (hC1hi (A + s)) hHreg hg hbL

/-- **⟦THE `hband` SLOT, MET, AT THE INFLATED SOCKET⟧** (`m4_hband_at_door_slot_L_gk` at
`SocketBaseLH h`; conjunct 4 only — cap-blind). -/
theorem m4_hband_at_door_slotH_L_gk (h K : ℕ) (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp)
    (R : ChowlaRegime) (M : ℕ) (hM : 1 ≤ M) (C₁ M₀ : ℕ → ℝ) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      ((∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          DoorBandBase_L_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
        ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) := by
  obtain ⟨hP4, hPQ⟩ := door_window_bounds_L_gk K M hM
  obtain ⟨C', x₀, hC'pos, hband⟩ := m4_hT0band_at_door_discharged_L_gk K hMmu Aexp hAexp
    (calP (AdoorL M) (s13GK K M) 1) (calQK (AdoorL M) (s13GK K M) M 2) hP4 hPQ
  obtain ⟨hcovP, hcovQ⟩ := door_cover_L_gk K M hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro hgates H L q j A s hb χ
  have hq : 0 < q := hb.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hgates H L q j A s hb
  have h16 : 16 ≤ A + s := by
    have h400 : (400 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := hD.X400
    have : (16 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by linarith
    exact_mod_cast this
  exact hband q χ M (A + s) (2 * (A + s)) rfl hD.X400 (by omega) le_rfl hD.C₁_one
    hD.x₀_le h16 hD.qfit hcovP hcovQ hD.gHalf hD.gO1 hD.gWin hD.grade hD.err

/-! ## §6 — the consumer's two inflated demands (word 6) -/

/-- ⟦G1⟧ at the inflated cap: `(h·arcDen 12 H)^7 ≤ h^7·rStrWitness H` — no new witness def. -/
theorem rStrWitness_G1_h (h H : ℕ) :
    ((h : ℝ) * arcDen 12 H) ^ 7 ≤ (h : ℝ) ^ 7 * rStrWitness H := by
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (rStrWitness_G1 H) (by positivity)

theorem rStrWitness_mul_nonneg (h H : ℕ) : 0 ≤ (h : ℝ) ^ 7 * rStrWitness H :=
  mul_nonneg (by positivity) (rStrWitness_nonneg H)

/-- **⟦G2's `j₀` FLOOR AT SHIFT `h`⟧** (`g2_of_j0_floor_h`) — `44·rSanWitness H + 87·(h·arcDen)
≤ (4/3)^{j₀}` from `4·log(263·h·max 1 (arcDen 12 H)) ≤ j₀`; the `h` rides inside the log. -/
theorem g2_of_j0_floor_h (h : ℕ) (hh : 0 < h) (H : ℕ) {j₀ : ℕ}
    (hj : 4 * Real.log (263 * (h : ℝ) * max 1 (arcDen 12 H)) ≤ (j₀ : ℝ)) :
    44 * rSanWitness H + 87 * ((h : ℝ) * arcDen 12 H) ≤ (4 / 3 : ℝ) ^ j₀ := by
  set m := max (1 : ℝ) (arcDen 12 H) with hm
  have hm1 : (1 : ℝ) ≤ m := le_max_left _ _
  have harc : arcDen 12 H ≤ m := le_max_right _ _
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hRS : rSanWitness H ≤ 4 * m := by
    unfold rSanWitness
    exact max_le (by linarith) (by linarith)
  have hpos : (0 : ℝ) < 263 * (h : ℝ) * m := by positivity
  have hpow : (0 : ℝ) < (4 / 3 : ℝ) ^ j₀ := by positivity
  have hlog43 : (1 : ℝ) / 4 ≤ Real.log (4 / 3) := by
    have h : (1 : ℝ) ≤ Real.log ((4 / 3 : ℝ) ^ (4 : ℕ)) := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < (4 / 3 : ℝ) ^ (4 : ℕ))]
      have := Real.exp_one_lt_d9
      norm_num
      linarith
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hj0 : (0 : ℝ) ≤ (j₀ : ℝ) := Nat.cast_nonneg _
  have hlogle : Real.log (263 * (h : ℝ) * m) ≤ Real.log ((4 / 3 : ℝ) ^ j₀) := by
    rw [Real.log_pow]
    linarith [mul_le_mul_of_nonneg_left hlog43 hj0]
  have hfin : 263 * (h : ℝ) * m ≤ (4 / 3 : ℝ) ^ j₀ := by
    have hexp := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log hpos, Real.exp_log hpow] at hexp
  have harc0 : (0 : ℝ) ≤ arcDen 12 H := arcDen_nonneg 12 H
  nlinarith [hfin, hRS, harc, hm1, hh1, harc0]

/-- **⟦GATE 4, READ AT THE INFLATED ENVELOPE⟧** (`m4_arith_gate4_rho_L` at `h`): above the
linear floor the spliced grade IS `RSanDoorRhoH ρ h H`. -/
theorem m4_arith_gate4_rhoH_L (h M : ℕ) (ρ : ℝ) :
    ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H) j H ≤ RSanDoorRhoH ρ h H :=
  m4ChiRowGradedH_an_L (RSan := fun H => RSanDoorRhoH ρ h H) (fun _ _ _ => le_rfl)

/-! ## §7 — THE CHAIN: the `hrows` slot, the middle link, the TOP producer, the BOTTOM fuse

Each is the landed theorem with `SocketBaseL` read as `SocketBaseLH h`; the two cap reads
enter only through `henv` (§1) and the framed base's own conjunct 5 (the middle link's
`φ(q) ≤ q ≤ h·arcDen`). -/

set_option maxHeartbeats 1000000 in
-- the landed slot's own budget (`M4RowsChiPrimeLinear.lean:622`): the 40-line statement
-- re-elaborates the seam integrals at every socket base
/-- **⟦THE SLOT, MET, DENSITY-FREE, AT THE INFLATED SOCKET⟧** (`m4_hrowsSlot_at_door_zero'_L_gk`
at `SocketBaseLH h`; conjuncts 4 and 8 only — cap-blind). -/
theorem m4_hrowsSlot_at_door_zero'H_L_gk (h K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow'_L_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_door_zero'_L_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L_gk] using hslot

/-- **⟦THE MIDDLE LINK AT THE INFLATED SOCKET⟧**
(`m4_chiSummedFreeRowBig_of_doorGradeGated_pool_L_gk` at `SocketBaseLH h`):
`φ(q) ≤ q ≤ h·arcDen 12 H`, so `henv` is read at `h·arcDen`. -/
theorem m4_chiSummedFreeRowBig_of_doorGradeGated_poolH_L_gk (h K : ℕ) {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) {C₁ M₀ π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (hgrade : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s)
        ≤ (q.totient : ℝ)
            * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                (M₀ (A + s)) (π₀ (A + s)))
    (henv : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      (h : ℝ) * arcDen 12 H
          * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBigH_L_gk h K R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hb : SocketBaseLH h R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) (π₀ (A + s)) :=
    a2DoorGrade_pool_nonneg_L_gk K hM (log_natCast_nonneg' (A + s)) hh0 (hpool (A + s))
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ (h : ℝ) * arcDen 12 H := le_trans hφq hqQ
  refine le_trans (hgrade H L q j A s hb) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H L q j A s hb

/-- **⟦THE TOP PRODUCER AT THE INFLATED SOCKET⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_L_gk` at `SocketBaseLH h`) — concludes the
socket `M4ChiSummedFreeRowH_L_gk` at the spliced grade `m4ChiRowGradedH_L h M RSbig`.  Of its
six hypotheses only `henv` reads the cap. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool'_gatedH_L_gk (h K : ℕ) {R : ChowlaRegime}
    {M : ℕ} {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorFuseFrame_pool'_L_gk K M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow'_L_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (henv : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      (h : ℝ) * arcDen 12 H
          * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
              (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowH_L_gk h K R M (m4ChiRowGradedH_L h M RSbig) := by
  refine m4_chiSummedFreeRow_of_bigH_L_gk h K
    (m4_chiSummedFreeRowBig_of_doorGradeGated_poolH_L_gk h K hM (C₁ := C₁) (M₀ := M₀) (π₀ := π₀)
      hpool ?_ henv)
  intro H L q j A s hb
  obtain ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  haveI : NeZero q := ⟨hq.ne'⟩
  have hbb : SocketBaseLH h R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hbb
  exact m4_chiFreeRowSq_sum_at_door_pool'_L_gk K hM hF.X_exp hF.X_three hF.h_four hF.h_window
    hF.tann hF.ceil5 (hrows H L q j A s hbb) (hband H L q j A s hbb) hF.gP1 hF.gRows
    hF.eps_pool hF.band_pool

set_option maxHeartbeats 1000000 in
-- the landed fuse's own budget (`S16FlatTerminalLinear.lean:106`): sixteen socket-framed
-- hypotheses re-elaborate against the re-cut prefix
/-- **⟦THE CONSTANT-POOL FUSE AT THE INFLATED SOCKET⟧** (`m4_closure_fuse_zero'_const_nonneg_L_gk`
at `SocketBaseLH h`) — THE BOTTOM of the terminal chain: sixteen hypotheses, every one cap-blind
in statement, concluding the socket `M4ChiSummedFreeRowH_L_gk h K R M` at the spliced grade
`m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)`.  `hh7 : log h ≤ 7` is stated ONCE,
here, outside every `∀ H`; it pays the envelope's `h` (§1). -/
theorem m4_closure_fuse_zero'_const_nonneg_H_L_gk (h : ℕ) (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kc ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 < ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          GRowsZeroGate'''_L_gk K M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
            ≤ (theta293 - ε (A + s)) * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kc ρ) →
        M4ChiSummedFreeRowH_L_gk h K R M
          (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'H_L_gk h K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε Kc ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows hthr _heps293
    hband4096 hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_gatedH_L_gk h K (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := fun _ => constPool ρ R.Hhi)
    (RSbig := fun _ H => RSanDoorRhoH ρ h H) hM ?_
    (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband
    (fun _ => constPool_nonneg hρ.le) (m4_arith_henv_constPoolH_L_gk K hh hh7 hρ.le harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_pos_L_gk K (hbf H L q j A s hb)
    (hgP1 H L q j A s hb) (hgRows H L q j A s hb) hρ (hthr H L q j A s hb) hM hXd
    (hband4096 H L q j A s hb)

/-! ## §8 — THE RECEIPT: the register's consumer fires on the fuse's output -/

/-- **⟦THE RECEIPT⟧** (`m4_chiSummedN_supplied_of_rowH_L_gk`) — the register's own consumer
`m4_chiSummedN_suppliedH_L_gk` (fired at `S16FlatTerminalLinearH.lean:1607` inside the register)
applied to the socket in the SHAPE the fuse produces, with ⟦G1⟧ at `RStr := h⁷·rStrWitness`
(`rStrWitness_G1_h`), ⟦G2⟧ at the `j₀`-floor (`g2_of_j0_floor_h`, via
`RSanDoorRhoH ρ h H ≤ 1 ≤ rSanWitness H`), and `han` at gate 4.  This is the `h`-twin of the
capstone's ⟦ITEM 11⟧ → ⟦gate 6⟧ wiring (`S16FlatTerminalLinear.lean:490-518`). -/
theorem m4_chiSummedN_supplied_of_rowH_L_gk (h K : ℕ) (hh : 0 < h) {R : ChowlaRegime} {M : ℕ}
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hj0 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * (h : ℝ) * max 1 (arcDen 12 H)) ≤ ((doorRowFloorL M : ℕ) : ℝ))
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ))
    (hrow : M4ChiSummedFreeRowH_L_gk h K R M
      (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H))) :
    M4ChiSummedBlockMeanSqNH_L_gk h K R M
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
        (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H))) := by
  refine m4_chiSummedN_suppliedH_L_gk h K (doorRowFloorL M)
    (fun H => RSanDoorRhoH_nonneg hρ0.le h H) (fun H => rStrWitness_mul_nonneg h H)
    (m4_arith_gate4_rhoH_L h M ρ) (fun H _ _ => rStrWitness_G1_h h H) ?_ harc8 hrow
  intro H hlo hhi
  have hh1 : 1 ≤ h := hh
  have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh1 hlo
  have hSR1 : (1 : ℝ) ≤ strataResidualH h H := one_le_strataResidualH harc1
  have hSRsq : (1 : ℝ) ≤ strataResidualH h H ^ 2 := by nlinarith
  have hRSle : RSanDoorRhoH ρ h H ≤ rSanWitness H := by
    have h1 : RSanDoorRhoH ρ h H ≤ 1 := by
      unfold RSanDoorRhoH
      rw [div_le_one (by nlinarith)]
      linarith
    exact le_trans h1 (le_max_left _ _)
  have hG := g2_of_j0_floor_h h hh H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
  linarith

/-! ## §9 — the `h = 1` twin law, spot-checked -/

example (ρ : ℝ) (H : ℕ) : RSanDoorRhoH ρ 1 H = RSanDoorRho ρ H := RSanDoorRhoH_one ρ H

example (δ₀ ρ : ℝ) : s15ArmH 1 δ₀ ρ = s15Arm δ₀ ρ := s15ArmH_one δ₀ ρ

/-- At `h = 1` the S12 price is the landed `arcDen_mul_strataResidual_sq_le`. -/
example {H : ℕ} (hL0 : 0 ≤ Real.log (H : ℝ)) (hlam : 50 ≤ Real.log (Real.log (H : ℝ))) :
    ((1 : ℕ) : ℝ) * arcDen 12 H * strataResidualH 1 H ^ 2
      ≤ Real.exp (14 * Real.log (Real.log (H : ℝ))) := by
  simpa [strataResidualH_one] using arcDen_mul_strataResidual_sq_le hL0 hlam

end Salt.MR
