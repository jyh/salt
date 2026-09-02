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

open Salt.Entropy.Chowla

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

/-! ## ⟦§2 — THE TWO SUPPLY DEFS AT THE INFLATED SOCKET, AND THEIR `h = 1` TWIN LAWS⟧

Both are pure binder swaps: `SocketBaseL R M …` becomes `SocketBaseLH h R M …` and nothing
else moves.  In BOTH the socket sits in HYPOTHESIS position under a `∀`, so a drifted
definition would still elaborate at every consumer and no build anywhere could see the
drift — the same blindness that let the P/X seam ship green in H1.  The `_one_iff` pair
below is the only instrument that looks at it, which is why each is a THEOREM and not a
docstring claim. -/

/-- ⟦ITEM 3⟧'s base-scale cap at the INFLATED socket (`S13CapGateLinear:891` re-quantified). -/
def S16BaseScaleCap96_LH_gk (h K : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
    Real.log (Real.log (((A + s : ℕ)) : ℝ))
      ≤ Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) / 9.60000096

/-- ⟦RULING 9⟧'s co-factor block at the INFLATED socket (`S13CapGateLinear:897`
re-quantified). -/
def S16CofactorSupply_LH_gk (h K : ℕ) (Cq : ℝ) (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
    ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
      ∃ Rrad Rbd CR : ℝ,
        0 ≤ Rbd
        ∧ Rbd ≤ CR * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-rho293)
        ∧ 1728 * Cq * CR ^ 2 ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (2 * theta293)
        ∧ (∀ (t₁ : ℝ) (χ : DirichletCharacter ℂ q),
            CofactorSocket (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) (A + s)
              (s13BandP (A + s)) (s13BandQ (A + s)) (2 * T) Rrad t₁ Rbd
              (doorCofactor0 χ (calP (AdoorL M) (s13GK K M))
                (calQK (AdoorL M) (s13GK K M) M) 2 1))

/-- ⭐ **THE ANTI-DRIFT GATE** — `S16BaseScaleCap96_LH_gk 1 = S16BaseScaleCap96_L_gk`. -/
theorem s16BaseScaleCap96LH_gk_one_iff (K : ℕ) (R : ChowlaRegime) (M : ℕ) :
    S16BaseScaleCap96_LH_gk 1 K R M ↔ S16BaseScaleCap96_L_gk K R M := by
  unfold S16BaseScaleCap96_LH_gk S16BaseScaleCap96_L_gk
  simp only [socketBaseLH_one_iff]

/-- ⭐ **THE ANTI-DRIFT GATE** — `S16CofactorSupply_LH_gk 1 = S16CofactorSupply_L_gk`. -/
theorem s16CofactorSupplyLH_gk_one_iff (K : ℕ) (Cq : ℝ) (R : ChowlaRegime) (M : ℕ) :
    S16CofactorSupply_LH_gk 1 K Cq R M ↔ S16CofactorSupply_L_gk K Cq R M := by
  unfold S16CofactorSupply_LH_gk S16CofactorSupply_L_gk
  simp only [socketBaseLH_one_iff]

/-! ## ⟦§3 — THE SUBSTRATE-TOUCHING LEAVES AND THE GRID PAGE⟧

Conjunct 11 enters this page at exactly two places — `s13CapGrid_mu_lo` and
`s13CapGrid_Lambda_sharp`, each a single call to `S16ProducersH`'s landed `_LH` substrate.
Every other `11`-routed grid leaf inherits through those two, so its port is the landed
proof with `(hh) (hh7)` threaded and the conclusion untouched. -/

theorem s13_abs8640_of_socketBase_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    (8640 : ℝ) ≤ (Real.log (A : ℝ)) ^ (theta293 - 1 / 500) := by
  obtain ⟨h1, h2⟩ := s13_socketBase_loglogA_LH hh hh7 hfl hb
  exact s13_abs8640_of_loglog (by linarith) h2

theorem s13_abs8640_at_base_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s B : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hAB : A ≤ B) :
    (8640 : ℝ) ≤ (Real.log (B : ℝ)) ^ (theta293 - 1 / 500) := by
  obtain ⟨h1, -⟩ := s13_socketBase_loglogA_LH hh hh7 hfl hb
  have hcore := s13_abs8640_of_socketBase_LH hh hh7 hfl hb
  have hABR : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
  have hA0 : (0 : ℝ) < (A : ℝ) := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    exact_mod_cast hA
  have hmono : Real.log (A : ℝ) ≤ Real.log (B : ℝ) := Real.log_le_log hA0 hABR
  have hθ : (0 : ℝ) ≤ theta293 - 1 / 500 := by have := s13_theta293_margin_lo; linarith
  exact le_trans hcore (Real.rpow_le_rpow (by linarith) hmono hθ)

theorem s13_abs8640_at_shift_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    (8640 : ℝ) ≤ (Real.log ((A + s : ℕ) : ℝ)) ^ (theta293 - 1 / 500) :=
  s13_abs8640_at_base_LH hh hh7 hfl hb (Nat.le_add_right A s)

theorem s13CapGrid_twoj_le_H_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseLH h R M H L q j A s) : 2 ^ j ≤ H := by
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

theorem s13CapGrid_mu_lo_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    Real.sqrt (H : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hmono : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    Real.log_le_log hA0 (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) s])
  exact le_trans (s13_socketBase_logA_ge_sqrt_LH hh hh7 hfl hb) hmono

theorem s13CapGrid_mu_2000_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hs2 : Real.sqrt (H : ℝ) ^ 2 = (H : ℝ) := Real.sq_sqrt (by positivity)
  have hs0 : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have : (2000 : ℝ) ≤ Real.sqrt (H : ℝ) := by nlinarith [hs2, hs0, hHR]
  exact le_trans this (s13CapGrid_mu_lo_LH hh hh7 hfl hb)

theorem s13CapGrid_logH_le_mu_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    Real.log (H : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  exact le_trans (capgrid_log_le_sqrt (by linarith)) (s13CapGrid_mu_lo_LH hh hh7 hfl hb)

theorem s13CapGrid_Lambda_sharp_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    Real.log (H : ℝ) / 2 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hsq := s13_socketBase_logA_ge_sqrt_LH hh hh7 hfl hb
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hs2 : Real.sqrt (H : ℝ) ^ 2 = (H : ℝ) := Real.sq_sqrt (by positivity)
  have hs0 : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have h2000 : (2000 : ℝ) ≤ Real.sqrt (H : ℝ) := by nlinarith [hs2, hs0, hHR]
  have hlogA0 : (0 : ℝ) < Real.log (A : ℝ) := by linarith
  have hmono : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    Real.log_le_log hA0 (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) s])
  exact le_trans (s13_socketBase_loglogA_sharp_LH hh hh7 hfl hb) (Real.log_le_log hlogA0 hmono)

theorem s13CapGrid_Lambda_lo_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have := s13CapGrid_Lambda_sharp_LH hh hh7 hfl hb
  linarith [capgrid_exp50_lo]

theorem s13CapGrid_logX_eight_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    8 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  linarith [s13CapGrid_mu_2000_LH hh hh7 hfl hb]

/-- **⟦FIELD `q_logX` AT THE INFLATED SOCKET⟧** — the ONE grid leaf that spends conjunct 5,
and the conclusion is nevertheless UNCHANGED: `q ≤ (log X_d)^12`.

The landed proof reads `q ≤ (log H)^12 ≤ μ^12` off `log H ≤ μ`.  At `SocketBaseLH h` the
ledger is `q ≤ h·(log H)^12`, so `log H ≤ μ` alone no longer closes it.  The repair does not
touch the conclusion and does not put a numeral at a floor: `capfloor_logH_le_half_sqrt`
gives `log H ≤ √H/2` at `H ≥ 4·10⁶`, and `√H ≤ μ` is `mu_lo`, so `log H ≤ μ/2` **uniformly**
— a factor `2^12 = 4096` of room, against `h ≤ 1096` from `log h ≤ 7`.  Margin `3.7×`. -/
theorem s13CapGrid_q_logX_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    (q : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ 12 := by
  have hq := hb.2.2.2.2.1
  have harc : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg (by linarith)
  have hhalf : Real.log (H : ℝ) ≤ Real.sqrt (H : ℝ) / 2 := capfloor_logH_le_half_sqrt hHR
  have hmulo : Real.sqrt (H : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    s13CapGrid_mu_lo_LH hh hh7 hfl hb
  have hhalfmu : Real.log (H : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) / 2 := by linarith
  have hmu0 : (0 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpow : Real.log (H : ℝ) ^ (12 : ℕ)
      ≤ (Real.log (((A + s : ℕ)) : ℝ) / 2) ^ (12 : ℕ) :=
    pow_le_pow_left₀ hlogH0 hhalfmu 12
  have hsplit : (Real.log (((A + s : ℕ)) : ℝ) / 2) ^ (12 : ℕ)
      = Real.log (((A + s : ℕ)) : ℝ) ^ (12 : ℕ) / 4096 := by ring
  have hmupow : (0 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) ^ (12 : ℕ) := by positivity
  have hh1096N : h ≤ 1096 := Salt.Entropy.Chowla.h_le_1096_of_log_le_seven hh hh7
  have hh1096 : (h : ℝ) ≤ 1096 := by exact_mod_cast hh1096N
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := by positivity
  rw [harc] at hq
  have hstep : (h : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ)
      ≤ 1096 * (Real.log (((A + s : ℕ)) : ℝ) ^ (12 : ℕ) / 4096) := by
    have h1 : (h : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ)
        ≤ (h : ℝ) * (Real.log (((A + s : ℕ)) : ℝ) ^ (12 : ℕ) / 4096) := by
      rw [← hsplit]; exact mul_le_mul_of_nonneg_left hpow hh0
    have h2 : (h : ℝ) * (Real.log (((A + s : ℕ)) : ℝ) ^ (12 : ℕ) / 4096)
        ≤ 1096 * (Real.log (((A + s : ℕ)) : ℝ) ^ (12 : ℕ) / 4096) :=
      mul_le_mul_of_nonneg_right hh1096 (by positivity)
    linarith
  have hfin : (1096 : ℝ) * (Real.log (((A + s : ℕ)) : ℝ) ^ (12 : ℕ) / 4096)
      ≤ Real.log (((A + s : ℕ)) : ℝ) ^ (12 : ℕ) := by nlinarith [hmupow]
  calc (q : ℝ) ≤ (h : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ) := hq
    _ ≤ 1096 * (Real.log (((A + s : ℕ)) : ℝ) ^ (12 : ℕ) / 4096) := hstep
    _ ≤ Real.log (((A + s : ℕ)) : ℝ) ^ (12 : ℕ) := hfin

theorem s13CapGrid_logqT_L_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T)
    (hThi : 2 * T ≤ (((A + s : ℕ)) : ℝ)) :
    Real.log ((q : ℝ) * (2 * T)) ≤ s13Lr (A + s) := by
  set Nd : ℕ := A + s with hNd
  set μ : ℝ := Real.log ((Nd : ℕ) : ℝ) with hμdef
  have hμ2000 : (2000 : ℝ) ≤ μ := s13CapGrid_mu_2000_LH hh hh7 hfl hb
  have hΛ21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log μ := s13CapGrid_Lambda_lo_LH hh hh7 hfl hb
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
    have hq12 : (q : ℝ) ≤ μ ^ (12 : ℕ) := s13CapGrid_q_logX_LH hh hh7 hfl hb
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

theorem s13CapGrid_logTann_lo_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
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
    exact_mod_cast s13CapGrid_twoj_le_H_LH hh hh7 hb
  have hdiv : (((A + s : ℕ)) : ℝ) / (H : ℝ) ≤ (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left (by linarith) hpow0 h2j
  have hdiv0 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) / (H : ℝ) := by positivity
  have hle : (((A + s : ℕ)) : ℝ) / (H : ℝ) ≤ 2 * T := by linarith
  have hlog := Real.log_le_log hdiv0 hle
  rw [Real.log_div (by linarith) (by linarith)] at hlog
  have hLam := s13CapGrid_Lambda_sharp_LH hh hh7 hfl hb
  linarith

theorem s13CapGrid_Tann_one_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) : (1 : ℝ) < 2 * T := by
  set μ : ℝ := Real.log (((A + s : ℕ)) : ℝ) with hμdef
  have hμ2000 : (2000 : ℝ) ≤ μ := s13CapGrid_mu_2000_LH hh hh7 hfl hb
  have hΛ21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log μ := s13CapGrid_Lambda_lo_LH hh hh7 hfl hb
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hsq : Real.log μ ≤ Real.sqrt μ := capgrid_log_le_sqrt (by linarith)
  have hs2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ0.le
  have hs0 : (0 : ℝ) < Real.sqrt μ := Real.sqrt_pos.mpr hμ0
  have hs40 : (40 : ℝ) ≤ Real.sqrt μ := by nlinarith [hs2, hs0]
  have h2Λ : 2 * Real.log μ ≤ μ / 2 := by nlinarith [hsq, hs2, hs40, hs0]
  have hlow := s13CapGrid_logTann_lo_LH hh hh7 hfl hb hTlo
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

theorem s13CapGrid_kappa_Tann_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    ∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
      30 ≤ Real.log (2 * T)
        / Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i) := by
  intro i hi
  set μ : ℝ := Real.log (((A + s : ℕ)) : ℝ) with hμdef
  have hμ2000 : (2000 : ℝ) ≤ μ := s13CapGrid_mu_2000_LH hh hh7 hfl hb
  have hΛ21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log μ := s13CapGrid_Lambda_lo_LH hh hh7 hfl hb
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
  have hlow := s13CapGrid_logTann_lo_LH hh hh7 hfl hb hTlo
  have hnum := capgrid_kappa_numeric hμ2000 hΛ100
  rw [le_div_iff₀ hlog0]
  rw [← hμdef] at hlow
  nlinarith [htop, hlow, hnum]

theorem s13CapGrid_kappa30_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    ∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
      30 ≤ Real.log ((q : ℝ) * (2 * T))
        / Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i) := by
  intro i hi
  have hq1 : 1 ≤ q := hb.2.2.2.1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hT1 : (1 : ℝ) < 2 * T := s13CapGrid_Tann_one_LH hh hh7 hfl hb hTlo
  have hmul : Real.log (2 * T) ≤ Real.log ((q : ℝ) * (2 * T)) := by
    apply Real.log_le_log (by linarith)
    nlinarith
  have hb3 := s13CapGrid_B3 (Nd := A + s) (s13CapGrid_mu_2000_LH hh hh7 hfl hb)
    (s13CapGrid_Lambda_lo_LH hh hh7 hfl hb) i hi
  have hb3R : (3 : ℝ)
      ≤ ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ) := by
    exact_mod_cast hb3
  have hlog0 : (0 : ℝ)
      < Real.log ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ) :=
    Real.log_pos (by linarith)
  have hbase := s13CapGrid_kappa_Tann_LH hh hh7 hfl hb hTlo i hi
  rw [le_div_iff₀ hlog0] at hbase ⊢
  linarith

theorem s13CapGrid_BT_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    ∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
      ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
        ≤ (q : ℝ) * (2 * T) := by
  intro i hi
  set μ : ℝ := Real.log (((A + s : ℕ)) : ℝ) with hμdef
  have hμ2000 : (2000 : ℝ) ≤ μ := s13CapGrid_mu_2000_LH hh hh7 hfl hb
  have hΛ21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log μ := s13CapGrid_Lambda_lo_LH hh hh7 hfl hb
  have hΛ100 : (100 : ℝ) ≤ Real.log μ := by
    have : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    nlinarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hb3 := s13CapGrid_B3 (Nd := A + s) hμ2000 hΛ21 i hi
  have hb3R : (3 : ℝ)
      ≤ ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ) := by
    exact_mod_cast hb3
  have hT1 : (1 : ℝ) < 2 * T := s13CapGrid_Tann_one_LH hh hh7 hfl hb hTlo
  have hq1 : 1 ≤ q := hb.2.2.2.1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have htop := s13CapGrid_logBase_le (Nd := A + s) hμ2000 hΛ21 hi
  have hlow := s13CapGrid_logTann_lo_LH hh hh7 hfl hb hTlo
  rw [← hμdef] at hlow
  have hnum := capgrid_kappa_numeric hμ2000 hΛ100
  have hstep : Real.log ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i
      : ℕ) : ℝ) ≤ Real.log (2 * T) := by
    have hdiv : (0 : ℝ) ≤ μ / Real.log μ := by positivity
    nlinarith [htop, hlow, hnum]
  have hmono := Real.exp_le_exp.mpr hstep
  rw [Real.exp_log (by linarith), Real.exp_log (by linarith)] at hmono
  nlinarith [hmono, hqR, hT1]

theorem s13CapGrid_BT10_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ} {T : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T) :
    ∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
      ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
        ≤ (2 * T) ^ 10 := by
  intro i hi
  exact ramQbase_le_pow_ten (s13CapGrid_Tann_one_LH hh hh7 hfl hb hTlo)
    (s13CapGrid_B3 (Nd := A + s) (s13CapGrid_mu_2000_LH hh hh7 hfl hb) (s13CapGrid_Lambda_lo_LH hh hh7 hfl hb) i hi)
    (s13CapGrid_kappa_Tann_LH hh hh7 hfl hb hTlo i hi)


/-! ## ⟦§4 — THE FLOOR PAGE⟧

Conjunct 5 is spent here at exactly one place, `capfloor_logq_le_LH`, and `floor1`/`floor3`
absorb it into the two numeric siblings.  `capfloor_tannGate` is NOT a spender despite
reaching `capfloor_logq_le`: it destructures `⟨-, hq1⟩` and keeps only `1 ≤ q`, using
`0 ≤ log q` in the favourable direction — so the whole `QTann`/`kappa30Q` razor pair below
is `+log h`-insensitive and ports mechanically. -/

/-- ⭐ **⟦THE `+log h` LINE⟧** — the one new inequality the floor page reads, and the only
place on it where conjunct 5's inflation is spent.  At `SocketBaseL` the modulus ledger gives
`log q ≤ 12·loglog H`; at `SocketBaseLH h` it gives `log q ≤ log h + 12·loglog H`, and `hh7`
turns that into `≤ 7 + 12·loglog H` wherever a numeral is wanted. -/
theorem capfloor_logq_le_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseLH h R M H L q j A s) :
    Real.log (q : ℝ) ≤ Real.log (h : ℝ) + 12 * Real.log (Real.log (H : ℝ))
      ∧ (1 : ℝ) ≤ (q : ℝ) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hqp : 0 < q := hb.2.2.2.1
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp
  have hqA : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H := hb.2.2.2.2.1
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [harcpow] at hqA
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hpow0 : (0 : ℝ) < Real.log (H : ℝ) ^ (12 : ℕ) := by positivity
  refine ⟨?_, hq1⟩
  have hstep := Real.log_le_log (by linarith : (0 : ℝ) < (q : ℝ)) hqA
  rw [Real.log_mul (ne_of_gt hh0) (ne_of_gt hpow0), Real.log_pow] at hstep
  push_cast at hstep
  linarith

theorem capfloor_twoj_le_H_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseLH h R M H L q j A s) : 2 ^ j ≤ H := by
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

theorem capfloor_core_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (H : ℝ) ∧ Real.sqrt (H : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) ∧
      0 < Tann ∧ Real.log ((Nd : ℕ) : ℝ) / 2 ≤ Real.log Tann := by
  have hlo : R.Hlo ≤ H := hb.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have hv : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (H : ℝ) :=
    le_trans capfloor_ten21_le_exp50 hexp50
  -- the base
  have hsqrtH : Real.sqrt (H : ℝ) ≤ Real.log (A : ℝ) := s13_socketBase_logA_ge_sqrt_LH hh hh7 hfl hb
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hANR : (A : ℝ) ≤ ((Nd : ℕ) : ℝ) := by exact_mod_cast hAN
  have hNd0 : (0 : ℝ) < ((Nd : ℕ) : ℝ) := lt_of_lt_of_le hA0 hANR
  have hm : Real.sqrt (H : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) :=
    le_trans hsqrtH (Real.log_le_log hA0 hANR)
  -- the height
  have h2j : 2 ^ j ≤ H := capfloor_twoj_le_H_LH hh hh7 hb
  have h2jR : ((2 ^ j : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h2j
  have h2j0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hTpos : 0 < Tann := lt_of_lt_of_le (div_pos hNd0 h2j0) hTlo
  have hlogdiv : Real.log ((Nd : ℕ) : ℝ) - Real.log ((2 ^ j : ℕ) : ℝ) ≤ Real.log Tann := by
    have hz := Real.log_le_log (div_pos hNd0 h2j0) hTlo
    rwa [Real.log_div (ne_of_gt hNd0) (ne_of_gt h2j0)] at hz
  have hlog2j : Real.log ((2 ^ j : ℕ) : ℝ) ≤ Real.log (H : ℝ) := Real.log_le_log h2j0 h2jR
  have hHhalf : Real.log (H : ℝ) ≤ Real.sqrt (H : ℝ) / 2 := capfloor_logH_le_half_sqrt hHR
  exact ⟨hv, hm, hTpos, by linarith⟩

theorem capfloor_muLambda_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    Real.exp (Real.log (H : ℝ) / 4) ≤ Real.log (5 * Tann + 1) ∧
      Real.log (H : ℝ) / 4 ≤ Real.log (Real.log (5 * Tann + 1)) := by
  obtain ⟨hv, hm, hTpos, hlogT⟩ := capfloor_core_LH hh hh7 hfl hb hAN hTlo
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  have hv0 : (0 : ℝ) < Real.log (H : ℝ) := by nlinarith [hv, (by positivity :
    (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ))]
  -- `√H = e^{v/2} = e^{v/4}·e^{v/4}`
  have hsq : Real.sqrt (H : ℝ) = Real.exp (Real.log (H : ℝ) / 2) := capfloor_sqrt_eq_exp hH0
  have hsplit : Real.exp (Real.log (H : ℝ) / 2)
      = Real.exp (Real.log (H : ℝ) / 4) * Real.exp (Real.log (H : ℝ) / 4) := by
    rw [← Real.exp_add]; ring_nf
  have hq0 : (0 : ℝ) < Real.exp (Real.log (H : ℝ) / 4) := Real.exp_pos _
  have hq2 : (2 : ℝ) ≤ Real.exp (Real.log (H : ℝ) / 4) := by
    have hz := Real.add_one_le_exp (Real.log (H : ℝ) / 4)
    have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    linarith
  -- `log T_ann ≥ ½ log Nd ≥ ½ √H = ½ e^{v/2} ≥ e^{v/4}`
  have hstep : Real.exp (Real.log (H : ℝ) / 4) ≤ Real.log Tann := by
    have h1 : Real.sqrt (H : ℝ) / 2 ≤ Real.log Tann := by linarith
    rw [hsq, hsplit] at h1
    nlinarith [h1, hq0, hq2]
  have hmono : Real.log Tann ≤ Real.log (5 * Tann + 1) :=
    Real.log_le_log hTpos (by linarith)
  refine ⟨le_trans hstep hmono, ?_⟩
  have hpos : (0 : ℝ) < Real.exp (Real.log (H : ℝ) / 4) := Real.exp_pos _
  have hz := Real.log_le_log hpos (le_trans hstep hmono)
  rwa [Real.log_exp] at hz

theorem capfloor_T0_Tann_sharp_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {T₀ Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hT₀ : T₀ ≤ Real.exp (Real.sqrt (H : ℝ) / 2)) : T₀ ≤ Tann := by
  obtain ⟨hv, hm, hTpos, hlogT⟩ := capfloor_core_LH hh hh7 hfl hb hAN hTlo
  have h1 : Real.sqrt (H : ℝ) / 2 ≤ Real.log Tann := by linarith
  have h2 : Real.exp (Real.sqrt (H : ℝ) / 2) ≤ Real.exp (Real.log Tann) :=
    Real.exp_le_exp.mpr h1
  rw [Real.exp_log hTpos] at h2
  linarith

theorem capfloor_T0_Tann_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {T₀ Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hT₀ : T₀ ≤ Real.exp (Real.exp 100)) : T₀ ≤ Tann := by
  obtain ⟨hv, hm, hTpos, hlogT⟩ := capfloor_core_LH hh hh7 hfl hb hAN hTlo
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  have hsq : Real.sqrt (H : ℝ) = Real.exp (Real.log (H : ℝ) / 2) := capfloor_sqrt_eq_exp hH0
  -- `e^{100} ≤ √H/2`
  have hE : Real.exp 100 ≤ Real.sqrt (H : ℝ) / 2 := by
    have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    have hmono : Real.exp 101 ≤ Real.exp (Real.log (H : ℝ) / 2) :=
      Real.exp_le_exp.mpr (by nlinarith [hv, h21])
    have hsplit : Real.exp 101 = Real.exp 100 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hp : (0 : ℝ) < Real.exp 100 := Real.exp_pos _
    rw [hsq]
    nlinarith [hmono, hsplit, he1, hp]
  exact capfloor_T0_Tann_sharp_LH hh hh7 hfl hb hAN hTlo (le_trans hT₀ (Real.exp_le_exp.mpr hE))

theorem capfloor_rhs_legs_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    Real.exp 300 * (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core_LH hh hh7 hfl hb hAN hTlo
  obtain ⟨hμ, hΛ⟩ := capfloor_muLambda_LH hh hh7 hfl hb hAN hTlo
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le h21 hv
  -- leg 1
  have hleg1 : Real.exp 300 ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4) := by
    have hstep : (Real.exp (Real.log (H : ℝ) / 4)) ^ ((3 : ℝ) / 4)
        ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (Real.exp_nonneg _) hμ (by norm_num)
    have heq : (Real.exp (Real.log (H : ℝ) / 4)) ^ ((3 : ℝ) / 4)
        = Real.exp (Real.log (H : ℝ) / 4 * (3 / 4)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [heq] at hstep
    refine le_trans (Real.exp_le_exp.mpr ?_) hstep
    nlinarith [hv, h21]
  -- leg 2
  have hleg2 : (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
      ≤ (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hΛ 4
  have hp1 : (0 : ℝ) < Real.exp 300 := Real.exp_pos _
  have hp2 : (0 : ℝ) ≤ (Real.log (H : ℝ) / 4) ^ (4 : ℕ) := by positivity
  exact mul_le_mul hleg1 hleg2 hp2 (le_trans hp1.le hleg1)

theorem capfloor_tannGate_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    TannGate ((Nd : ℕ) : ℝ) ((q : ℝ) * Tann) := by
  obtain ⟨hv, hm, hTpos, hlogT⟩ := capfloor_core_LH hh hh7 hfl hb hAN hTlo
  obtain ⟨-, hq1⟩ := capfloor_logq_le_LH hh hh7 hb
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le h21 hv
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  -- `log Nd ≥ √H = e^{v/2} ≥ (v/4)² = v²/16`
  have hsq : Real.sqrt (H : ℝ) = Real.exp (Real.log (H : ℝ) / 2) := capfloor_sqrt_eq_exp hH0
  have hexpsq : Real.exp (Real.log (H : ℝ) / 2)
      = Real.exp (Real.log (H : ℝ) / 4) * Real.exp (Real.log (H : ℝ) / 4) := by
    rw [← Real.exp_add]; ring_nf
  have hquart : Real.log (H : ℝ) / 4 ≤ Real.exp (Real.log (H : ℝ) / 4) := by
    have := Real.add_one_le_exp (Real.log (H : ℝ) / 4); linarith
  have hq0 : (0 : ℝ) ≤ Real.log (H : ℝ) / 4 := by linarith
  have hmsq : Real.log (H : ℝ) ^ (2 : ℕ) / 16 ≤ Real.log ((Nd : ℕ) : ℝ) := by
    have hz : (Real.log (H : ℝ) / 4) * (Real.log (H : ℝ) / 4) ≤ Real.sqrt (H : ℝ) := by
      rw [hsq, hexpsq]; nlinarith [hquart, hq0]
    nlinarith [hz, hm]
  have hm0 : (0 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) := by nlinarith [hmsq, hv0]
  set r : ℝ := Real.sqrt (Real.log ((Nd : ℕ) : ℝ)) with hr
  have hr2 : r * r = Real.log ((Nd : ℕ) : ℝ) := Real.mul_self_sqrt hm0
  have hr0 : (0 : ℝ) ≤ r := Real.sqrt_nonneg _
  have hnum : (10 : ℝ) ^ (21 : ℕ) = 1000000000000000000000 := by norm_num
  rw [hnum] at hv
  have hr60 : (60 : ℝ) ≤ r := by nlinarith [hr2, hmsq, hv, hr0, hv0]
  -- `log(q·T_ann) ≥ log T_ann ≥ ½·r² ≥ 30r`
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hqT : Real.log ((q : ℝ) * Tann) = Real.log (q : ℝ) + Real.log Tann :=
    Real.log_mul (by linarith) (ne_of_gt hTpos)
  have hkey : 30 * r ≤ Real.log ((q : ℝ) * Tann) := by
    rw [hqT]; nlinarith [hlogT, hr2, hr60, hr0, hlogq]
  have hqT0 : (0 : ℝ) < (q : ℝ) * Tann := by positivity
  unfold TannGate
  rw [rpow_half_eq_sqrt, ← hr]
  calc Real.exp (30 * r) ≤ Real.exp (Real.log ((q : ℝ) * Tann)) := Real.exp_le_exp.mpr hkey
    _ = (q : ℝ) * Tann := Real.exp_log hqT0

theorem capfloor_QTann_gen_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {A G M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j As s) (hAN : As ≤ Nd)
    (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK A G M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    ((calQK A G M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann := by
  have hgate := capfloor_tannGate_LH hh hh7 hfl hb hAN hTlo (q := q)
  unfold TannGate at hgate
  rw [rpow_half_eq_sqrt] at hgate
  have hQ1 : 1 < ((calQK A G M 2 : ℕ) : ℝ) := capfloor_one_lt_QK2_gen hA hG hM
  have hQ0 : (0 : ℝ) < ((calQK A G M 2 : ℕ) : ℝ) := by linarith
  have hr0 : (0 : ℝ) ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)) := Real.sqrt_nonneg _
  calc ((calQK A G M 2 : ℕ) : ℝ)
      = Real.exp (Real.log ((calQK A G M 2 : ℕ) : ℝ)) := (Real.exp_log hQ0).symm
    _ ≤ Real.exp (30 * Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ (q : ℝ) * Tann := hgate

theorem capfloor_kappa30Q_gen_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {A G M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j As s) (hAN : As ≤ Nd)
    (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK A G M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((calQK A G M 2 : ℕ) : ℝ) := by
  refine kappa30_of_TannGate ((Nd : ℕ) : ℝ) ((q : ℝ) * Tann) (calQK A G M 2)
    (capfloor_one_lt_QK2_gen hA hG hM) ?_ (capfloor_tannGate_LH hh hh7 hfl hb hAN hTlo)
  rw [rpow_half_eq_sqrt]; exact hQ2reg

theorem capfloor_QTann_LH_gk {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) (K : ℕ) {R : ChowlaRegime} {M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j As s) (hAN : As ≤ Nd)
    (hM : 1 ≤ M) (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann :=
  capfloor_QTann_gen_LH hh hh7 hfl hb hAN (one_le_AdoorL hM) (one_le_s13GK K hM) hM hTlo hQ2reg

theorem capfloor_kappa30Q_LH_gk {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) (K : ℕ) {R : ChowlaRegime} {M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j As s) (hAN : As ≤ Nd)
    (hM : 1 ≤ M) (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) :=
  capfloor_kappa30Q_gen_LH hh hh7 hfl hb hAN (one_le_AdoorL hM) (one_le_s13GK K hM) hM hTlo hQ2reg


/-- ⟦`floor1` at the inflated socket⟧ — the `8·log(40000·vkStripConst q)` leg.  The landed
proof spends `8·(20 + log q) ≤ 160 + 96·loglog H`, exactly `capfloor_lam_core`'s left side.
At `LH` the same spend is `8·(20 + 7 + 12·loglog H) = 216 + 96·loglog H`, exactly
`capfloor_lam_core_h`'s.  **The sibling's `216` is not a chosen constant — it is what this
line costs.** -/
theorem capfloor_floor1_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core_LH hh hh7 hfl hb hAN hTlo
  obtain ⟨-, hΛ⟩ := capfloor_muLambda_LH hh hh7 hfl hb hAN hTlo
  obtain ⟨hlq, hq1⟩ := capfloor_logq_le_LH hh hh7 hb
  have hvk : (40000 : ℝ) * vkStripConst q = 200000000 * (q : ℝ) := by
    rw [vkStripConst]; ring
  have hsplit : Real.log (200000000 * (q : ℝ))
      = Real.log 200000000 + Real.log (q : ℝ) :=
    Real.log_mul (by norm_num) (by linarith)
  have hnum : Real.log 200000000 ≤ 20 := by
    have hz := Real.log_le_log (by norm_num : (0 : ℝ) < 200000000)
      (le_trans (by norm_num : (200000000 : ℝ) ≤ 300000000) capfloor_twoE8_le_exp20)
    rwa [Real.log_exp] at hz
  have hcore := capfloor_lam_core_h hv
  rw [hvk, hsplit]
  linarith

/-- ⟦`floor2` at the inflated socket⟧ — the `+8104` companion.  `log q` enters divided by
`100`, so the whole `+log h` costs `0.07`. -/
theorem capfloor_floor2_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
      ≤ Real.log (Real.log (5 * Tann + 1)) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core_LH hh hh7 hfl hb hAN hTlo
  obtain ⟨-, hΛ⟩ := capfloor_muLambda_LH hh hh7 hfl hb hAN hTlo
  obtain ⟨hlq, hq1⟩ := capfloor_logq_le_LH hh hh7 hb
  have hvk : (20000 : ℝ) * (vkStripConst q + 8104) = 100000000 * (q : ℝ) + 162080000 := by
    rw [vkStripConst]; ring
  have hub : 100000000 * (q : ℝ) + 162080000 ≤ 300000000 * (q : ℝ) := by linarith
  have hlb : (0 : ℝ) < 100000000 * (q : ℝ) + 162080000 := by linarith
  have hmono := Real.log_le_log hlb hub
  have hsplit : Real.log (300000000 * (q : ℝ))
      = Real.log 300000000 + Real.log (q : ℝ) :=
    Real.log_mul (by norm_num) (by linarith)
  have hnum : Real.log 300000000 ≤ 20 := by
    have hz := Real.log_le_log (by norm_num : (0 : ℝ) < 300000000) capfloor_twoE8_le_exp20
    rwa [Real.log_exp] at hz
  have hcore := capfloor_lam_core_h hv
  have hlq0 : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  -- ⚠ at h = 1 this followed from `0 ≤ log q ≤ 12·loglog H`; at LH the `+log h` breaks that
  -- implication, so it is taken from the register's own `log H ≥ 10^21` instead.
  have hone : (1 : ℝ) ≤ Real.log (H : ℝ) := by
    have hnum : (1 : ℝ) ≤ (10 : ℝ) ^ (21 : ℕ) := by norm_num
    linarith
  have hlvl : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := Real.log_nonneg hone
  rw [hvk]
  rw [hsplit] at hmono
  linarith

/-- ⟦`floor3` at the inflated socket⟧ — the `Kq` arm.  `hW` picks up `log h ≤ 7`, so the
numeric leg is `capfloor_floor3_numeric_h`'s `+8` rather than the landed `+1`. -/
theorem capfloor_floor3_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Kq Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) (hKq : Kq ≤ Real.exp 100) :
    Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core_LH hh hh7 hfl hb hAN hTlo
  obtain ⟨hlq, hq1⟩ := capfloor_logq_le_LH hh hh7 hb
  have hlegs := capfloor_rhs_legs_LH hh hh7 hfl hb hAN hTlo
  set E : ℝ := Real.exp 100 with hEdef
  have hE : (101 : ℝ) ≤ E := by
    have := Real.add_one_le_exp (100 : ℝ); rw [hEdef]; linarith
  have hE0 : (0 : ℝ) < E := by linarith
  have hexpE : (3 : ℝ) ≤ Real.exp E := by
    have := Real.add_one_le_exp E; linarith
  have hbox : Real.exp E + 3 ≤ Real.exp (E + 1) := by
    rw [Real.exp_add]
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    nlinarith [Real.exp_pos E, hexpE, he1]
  have hbox0 : (0 : ℝ) < Real.exp E + 3 := by positivity
  have hboxlog : Real.log (Real.exp E + 3) ≤ E + 1 := by
    have hz := Real.log_le_log hbox0 hbox
    rwa [Real.log_exp] at hz
  have hWsplit : Real.log ((q : ℝ) * (Real.exp E + 3))
      = Real.log (q : ℝ) + Real.log (Real.exp E + 3) :=
    Real.log_mul (by linarith) (by linarith)
  have hW0 : (0 : ℝ) ≤ Real.log ((q : ℝ) * (Real.exp E + 3)) := by
    refine Real.log_nonneg ?_
    nlinarith [hq1, hexpE]
  have hW : Real.log ((q : ℝ) * (Real.exp E + 3))
      ≤ 12 * Real.log (Real.log (H : ℝ)) + E + 8 := by
    rw [hWsplit]; linarith
  have hstep : Kq * Real.log ((q : ℝ) * (Real.exp E + 3))
      ≤ E * Real.log ((q : ℝ) * (Real.exp E + 3)) :=
    mul_le_mul_of_nonneg_right hKq hW0
  have hnum := capfloor_floor3_numeric_h hv hE hW
  have hE3 : Real.exp 300 = E ^ (3 : ℕ) := by
    rw [hEdef, ← Real.exp_nat_mul]; norm_num
  rw [hE3] at hlegs
  linarith

set_option maxHeartbeats 400000 in
-- the `q ≤ (log H)^13` re-cut adds an rpow chain on top of the landed closing block
/-- ⟦`floor4` at the inflated socket⟧ — the `Ks` arm, and the one leaf whose LHS route is
genuinely re-cut.  The landed proof reads `q ≤ (log H)^12` and lands on `(log H)^{3/4}`.  At
`LH` the ledger is `q ≤ h·(log H)^12`, and rather than carry an `h^{1/16}` factor the cleanest
route absorbs `h` into the exponent: `h ≤ 1096 ≤ log H`, so `q ≤ (log H)^13` and
`q^{1/16} ≤ (log H)^{13/16} ≤ log H` — **the same conclusion, with no numeral at a floor**. -/
theorem capfloor_floor4_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) (hKs : Real.exp (-100) ≤ Ks) :
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core_LH hh hh7 hfl hb hAN hTlo
  obtain ⟨hlq, hq1⟩ := capfloor_logq_le_LH hh hh7 hb
  have hlegs := capfloor_rhs_legs_LH hh hh7 hfl hb hAN hTlo
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le h21 hv
  have hnum1 : (1 : ℝ) ≤ (10 : ℝ) ^ (21 : ℕ) := by norm_num
  have hv1 : (1 : ℝ) ≤ Real.log (H : ℝ) := by linarith
  -- `h ≤ 1096 ≤ 10^21 ≤ log H`, so the inflation is absorbed into the exponent
  have hh1096N : h ≤ 1096 := Salt.Entropy.Chowla.h_le_1096_of_log_le_seven hh hh7
  have hh1096 : (h : ℝ) ≤ 1096 := by exact_mod_cast hh1096N
  have hnum2 : (1096 : ℝ) ≤ (10 : ℝ) ^ (21 : ℕ) := by norm_num
  have hhle : (h : ℝ) ≤ Real.log (H : ℝ) := by linarith
  have hqA : (q : ℝ) ≤ Real.log (H : ℝ) ^ (13 : ℕ) := by
    have hz := hb.2.2.2.2.1
    have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
      rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [harcpow] at hz
    have hp12 : (0 : ℝ) ≤ Real.log (H : ℝ) ^ (12 : ℕ) := by positivity
    have hid : Real.log (H : ℝ) ^ (13 : ℕ)
        = Real.log (H : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ) := by ring
    calc (q : ℝ) ≤ (h : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ) := hz
      _ ≤ Real.log (H : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ) :=
          mul_le_mul_of_nonneg_right hhle hp12
      _ = Real.log (H : ℝ) ^ (13 : ℕ) := hid.symm
  have hstep1 : (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ (Real.log (H : ℝ) ^ (13 : ℕ)) ^ ((1 : ℝ) / 16) :=
    Real.rpow_le_rpow (Nat.cast_nonneg q) hqA (by norm_num)
  have hstep2 : (Real.log (H : ℝ) ^ (13 : ℕ)) ^ ((1 : ℝ) / 16)
      = Real.log (H : ℝ) ^ ((13 : ℝ) / 16) := by
    rw [← Real.rpow_natCast (Real.log (H : ℝ)) 13, ← Real.rpow_mul hv0.le]
    norm_num
  have hstep3 : Real.log (H : ℝ) ^ ((13 : ℝ) / 16) ≤ Real.log (H : ℝ) := by
    calc Real.log (H : ℝ) ^ ((13 : ℝ) / 16) ≤ Real.log (H : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
      _ = Real.log (H : ℝ) := Real.rpow_one _
  have hLHS : (q : ℝ) ^ ((1 : ℝ) / 16) ≤ Real.log (H : ℝ) := by
    rw [hstep2] at hstep1; linarith
  set E : ℝ := Real.exp 100 with hEdef
  have hE : (101 : ℝ) ≤ E := by
    have := Real.add_one_le_exp (100 : ℝ); rw [hEdef]; linarith
  have hE0 : (0 : ℝ) < E := by linarith
  have hE3 : Real.exp 300 = E ^ (3 : ℕ) := by
    rw [hEdef, ← Real.exp_nat_mul]; norm_num
  rw [hE3] at hlegs
  have hKsE : 1 / E ≤ Ks := by
    have hz : Real.exp (-100 : ℝ) = 1 / E := by
      rw [hEdef, Real.exp_neg]; simp
    rwa [hz] at hKs
  have hRpos : (0 : ℝ) ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) := by
    refine le_trans ?_ hlegs
    positivity
  have hmul : (1 / E) * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ))
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) :=
    mul_le_mul_of_nonneg_right hKsE hRpos
  refine le_trans ?_ hmul
  refine le_trans hLHS ?_
  -- the RHS is h-blind: the landed closing chain, verbatim
  have hinner : (1 / E) * (E ^ (3 : ℕ) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ))
      ≤ (1 / E) * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) :=
    mul_le_mul_of_nonneg_left hlegs (by positivity)
  refine le_trans ?_ hinner
  have hEq : (1 / E) * (E ^ (3 : ℕ) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ))
      = E ^ (2 : ℕ) * (Real.log (H : ℝ) ^ (4 : ℕ) / 256) := by
    field_simp; ring
  rw [hEq]
  have h256 : (256 : ℝ) ≤ Real.log (H : ℝ) := by
    refine le_trans (by norm_num) hv
  have hxx : (65536 : ℝ) ≤ Real.log (H : ℝ) * Real.log (H : ℝ) := by nlinarith [h256]
  have hv3 : (256 : ℝ) ≤ Real.log (H : ℝ) ^ (3 : ℕ) := by
    have hid : Real.log (H : ℝ) ^ (3 : ℕ)
        = Real.log (H : ℝ) * (Real.log (H : ℝ) * Real.log (H : ℝ)) := by ring
    rw [hid]; nlinarith [h256, hxx]
  have hE2 : (1 : ℝ) ≤ E ^ (2 : ℕ) := by nlinarith [hE]
  have hfac : (1 : ℝ) ≤ E ^ (2 : ℕ) * (Real.log (H : ℝ) ^ (3 : ℕ) / 256) := by
    have h1 : (1 : ℝ) ≤ Real.log (H : ℝ) ^ (3 : ℕ) / 256 := by linarith
    nlinarith [hE2, h1]
  have hid2 : E ^ (2 : ℕ) * (Real.log (H : ℝ) ^ (4 : ℕ) / 256)
      = Real.log (H : ℝ) * (E ^ (2 : ℕ) * (Real.log (H : ℝ) ^ (3 : ℕ) / 256)) := by ring
  rw [hid2]
  nlinarith [hfac, hv0]


theorem s13CapFloor_all_LH_gk {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) (K : ℕ) {R : ChowlaRegime} {M H L q j As s Nd : ℕ}
    {T₀ Kq Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j As s) (hM : 1 ≤ M)
    (hAN : As ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)))
    (hT₀ : T₀ ≤ Real.exp (Real.exp 100)) (hKq : Kq ≤ Real.exp 100)
    (hKs : Real.exp (-100) ≤ Ks) :
    ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann ∧
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ∧
    T₀ ≤ Tann ∧
    8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) ∧
    8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
      ≤ Real.log (Real.log (5 * Tann + 1)) ∧
    Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) ∧
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) ∧
    Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)) :=
  ⟨capfloor_QTann_LH_gk hh hh7 K hfl hb hAN hM hTlo hQ2reg,
   capfloor_kappa30Q_LH_gk hh hh7 K hfl hb hAN hM hTlo hQ2reg,
   capfloor_T0_Tann_LH hh hh7 hfl hb hAN hTlo hT₀,
   capfloor_floor1_LH hh hh7 hfl hb hAN hTlo,
   capfloor_floor2_LH hh hh7 hfl hb hAN hTlo,
   capfloor_floor3_LH hh hh7 hfl hb hAN hTlo hKq,
   capfloor_floor4_LH hh hh7 hfl hb hAN hTlo hKs,
   hQ2reg⟩



/-! ## ⟦§5 — THE THREE `EP₂` ROWS AT THE INFLATED MODULUS⟧

The register's fourth output is `φ(q) ≤ (log H)^12` at `SocketBaseL` and `φ(q) ≤ h·(log H)^12`
at `SocketBaseLH h`, because `φ(q) ≤ q` and conjunct 5 now carries the `h`.  That single
factor is what the six numeric siblings of §1 were minted for, and each row spends it as an
extra `log h ≤ 7` in one exponential:

| row | landed stone, at | sibling, at |
|---|---|---|
| `capeps_row_phi` | `expbound`, `t = 11` | `expbound_60`, `t = 18` |
| `capeps_row_tail` leg 1 | `expbound`, `t = 49` | `expbound_60`, `t = 56` |
| `capeps_row_tail` leg 2 | `bigexp`, `t = 8` | `bigexp_60`, `t = 15` |
| `capeps_row_p2` leg 1 | `Pbig`, `e^11` | `Pbig_h`, `e^18` |
| `capeps_row_p2` leg 2 | `bigexp`, `t = 11` | `bigexp_60`, `t = 18` |

**Every one of the six siblings is consumed here, and nowhere else** — which is the check that
§1's ceilings were priced from the real demand rather than chosen. -/

section RowsH

variable {u μ X W C r β Pr φ : ℝ}

/-- `h ≤ e^7` — the one fact about the shift these rows use. -/
theorem h_le_exp_seven {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) :
    (h : ℝ) ≤ Real.exp 7 := by
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hz := Real.exp_le_exp.mpr hh7
  rwa [Real.exp_log hh0] at hz

/-- ⟦SIBLING of `capeps_row_phi` (`S13CapEps:242`) at `φ ≤ h·u¹²`⟧ — `11 → 18`. -/
theorem capeps_row_phi_h {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (hφ0 : 0 ≤ φ) (hφ : φ ≤ (h : ℝ) * u ^ (12 : ℕ)) :
    12 * (4160 * φ * μ ^ (-theta293)) ≤ μ ^ (-(1 / 500) : ℝ) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Real.log μ := by linarith
  have hp12 : (0 : ℝ) < u ^ (12 : ℕ) := pow_pos hu0 12
  have hexp7 := h_le_exp_seven hh hh7
  have he11 : (49920 : ℝ) ≤ Real.exp 11 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hz : Real.exp 11 = (Real.exp 1) ^ (11 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7182818283 : ℝ) ^ (11 : ℕ) ≤ (Real.exp 1) ^ (11 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 11
    have : (49920 : ℝ) ≤ (2.7182818283 : ℝ) ^ (11 : ℕ) := by norm_num
    rw [hz]; linarith
  have he18 : (49920 : ℝ) * (h : ℝ) ≤ Real.exp 18 := by
    have hsum : Real.exp 18 = Real.exp 11 * Real.exp 7 := by rw [← Real.exp_add]; norm_num
    rw [hsum]
    exact mul_le_mul he11 hexp7 (by positivity) (Real.exp_pos 11).le
  have hstone := capeps_expbound_60 hu hμ hΛ (by norm_num : (18 : ℝ) ≤ 60)
  have hkey : 49920 * φ ≤ μ ^ (theta293 - 1 / 500) := by
    have hchain : 49920 * φ ≤ (49920 * (h : ℝ)) * u ^ (12 : ℕ) := by nlinarith [hφ, hp12]
    have h1 : 49920 * φ ≤ Real.exp 18 * u ^ (12 : ℕ) :=
      le_trans hchain (mul_le_mul_of_nonneg_right he18 hp12.le)
    have h2 : Real.exp 18 * u ^ (12 : ℕ)
        ≤ Real.exp 18 * u ^ (12 : ℕ) * Real.log μ := by
      nlinarith [Real.exp_pos (18 : ℝ)]
    linarith
  have hT0 : (0 : ℝ) < μ ^ (-theta293) := Real.rpow_pos_of_pos hμ0 _
  have hsplit : μ ^ (-theta293) * μ ^ (theta293 - 1 / 500) = μ ^ (-(1 / 500) : ℝ) := by
    rw [← Real.rpow_add hμ0]; congr 1; ring
  calc 12 * (4160 * φ * μ ^ (-theta293)) = (49920 * φ) * μ ^ (-theta293) := by ring
    _ ≤ μ ^ (theta293 - 1 / 500) * μ ^ (-theta293) :=
        mul_le_mul_of_nonneg_right hkey hT0.le
    _ = μ ^ (-theta293) * μ ^ (theta293 - 1 / 500) := by ring
    _ = μ ^ (-(1 / 500) : ℝ) := hsplit

set_option maxHeartbeats 1000000 in
-- the `(h:ℝ)·u¹²` factor doubles the monomial count in both legs' linarith tableaux
/-- ⟦SIBLING of `capeps_row_tail` (`S13CapEps:277`) at `W ≤ 64·h·u¹²·X`⟧ — `49 → 56`, `8 → 15`. -/
theorem capeps_row_tail_h {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (hX0 : 0 < X) (hXlog : Real.log X = μ)
    (hW0 : 0 ≤ W) (hW : W ≤ 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X) (hC0 : 0 < C)
    (hC : Real.log C ≤ 40) (hr : r ≤ 2 * (Real.log μ * μ ^ (-theta293))) :
    12 * (W * (C * r / X + 1 / X ^ 2)) ≤ μ ^ (-(1 / 500) : ℝ) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Real.log μ := by linarith
  have hp12 : (0 : ℝ) < u ^ (12 : ℕ) := pow_pos hu0 12
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hph : (0 : ℝ) < (h : ℝ) * u ^ (12 : ℕ) := by positivity
  have hexp7 := h_le_exp_seven hh hh7
  have hT0 : (0 : ℝ) < μ ^ (-theta293) := Real.rpow_pos_of_pos hμ0 _
  have hXne : X ≠ 0 := ne_of_gt hX0
  have hinv : (0 : ℝ) ≤ X⁻¹ := by positivity
  have hstep : C * r / X + 1 / X ^ 2
      ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2 := by
    have h1 : C * r ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) :=
      mul_le_mul_of_nonneg_left hr hC0.le
    have h2 : C * r / X ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) / X := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h1 hinv
    linarith
  have hS0 : (0 : ℝ) ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2 := by
    have : (0 : ℝ) ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) / X := by positivity
    have h2 : (0 : ℝ) ≤ 1 / X ^ 2 := by positivity
    linarith
  have hprod : W * (C * r / X + 1 / X ^ 2)
      ≤ 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X
        * (C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2) :=
    le_trans (mul_le_mul_of_nonneg_left hstep hW0) (mul_le_mul_of_nonneg_right hW hS0)
  have hval : 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X
        * (C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2)
      = 128 * C * ((h : ℝ) * u ^ (12 : ℕ)) * Real.log μ * μ ^ (-theta293)
        + 64 * ((h : ℝ) * u ^ (12 : ℕ)) / X := by
    field_simp
    ring
  have hCle : C ≤ Real.exp 40 := by
    have := Real.exp_le_exp.mpr hC
    rwa [Real.exp_log hC0] at this
  have h3072 : (3072 : ℝ) ≤ Real.exp 9 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hz : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7182818283 : ℝ) ^ (9 : ℕ) ≤ (Real.exp 1) ^ (9 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 9
    have : (3072 : ℝ) ≤ (2.7182818283 : ℝ) ^ (9 : ℕ) := by norm_num
    rw [hz]; linarith
  have h56 : (3072 : ℝ) * C * (h : ℝ) ≤ Real.exp 56 := by
    have hsum : Real.exp 56 = Real.exp 9 * Real.exp 40 * Real.exp 7 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [hsum]
    have hCh : (3072 : ℝ) * C ≤ Real.exp 9 * Real.exp 40 :=
      mul_le_mul h3072 hCle hC0.le (Real.exp_pos 9).le
    exact mul_le_mul hCh hexp7 (by positivity) (by positivity)
  have hlegA : 1536 * C * ((h : ℝ) * u ^ (12 : ℕ)) * Real.log μ * μ ^ (-theta293)
      ≤ μ ^ (-(1 / 500) : ℝ) / 2 := by
    have hstone := capeps_expbound_60 hu hμ hΛ (by norm_num : (56 : ℝ) ≤ 60)
    have hmul : (3072 * C * (h : ℝ)) * (u ^ (12 : ℕ) * Real.log μ)
        ≤ Real.exp 56 * (u ^ (12 : ℕ) * Real.log μ) :=
      mul_le_mul_of_nonneg_right h56 (by positivity)
    have h1 : 3072 * C * ((h : ℝ) * u ^ (12 : ℕ)) * Real.log μ
        ≤ μ ^ (theta293 - 1 / 500) := by nlinarith [hmul, hstone]
    have h2 : 3072 * C * ((h : ℝ) * u ^ (12 : ℕ)) * Real.log μ * μ ^ (-theta293)
        ≤ μ ^ (theta293 - 1 / 500) * μ ^ (-theta293) :=
      mul_le_mul_of_nonneg_right h1 hT0.le
    have hsplit : μ ^ (theta293 - 1 / 500) * μ ^ (-theta293) = μ ^ (-(1 / 500) : ℝ) := by
      rw [← Real.rpow_add hμ0]; congr 1; ring
    rw [hsplit] at h2
    linarith
  have hlegB : 64 * ((h : ℝ) * u ^ (12 : ℕ)) / X ≤ μ ^ (-(1 / 500) : ℝ) / 24 := by
    have hstone := capeps_bigexp_60 hu hμ hΛ (by norm_num : (15 : ℝ) ≤ 60)
    have he8 : (1536 : ℝ) ≤ Real.exp 8 := by
      have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have hz : Real.exp 8 = (Real.exp 1) ^ (8 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have hc : (2.7182818283 : ℝ) ^ (8 : ℕ) ≤ (Real.exp 1) ^ (8 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) h1.le 8
      have : (1536 : ℝ) ≤ (2.7182818283 : ℝ) ^ (8 : ℕ) := by norm_num
      rw [hz]; linarith
    have he15 : (1536 : ℝ) * (h : ℝ) ≤ Real.exp 15 := by
      have hsum : Real.exp 15 = Real.exp 8 * Real.exp 7 := by rw [← Real.exp_add]; norm_num
      rw [hsum]
      exact mul_le_mul he8 hexp7 (by positivity) (Real.exp_pos 8).le
    have hμ2 : (1 : ℝ) ≤ μ ^ 2 := by nlinarith
    have ha : 1536 * ((h : ℝ) * u ^ (12 : ℕ)) ≤ Real.exp 15 * u ^ (12 : ℕ) := by
      have := mul_le_mul_of_nonneg_right he15 hp12.le
      nlinarith [this]
    have hbb : Real.exp 15 * u ^ (12 : ℕ) ≤ Real.exp 15 * u ^ (12 : ℕ) * μ ^ 2 :=
      le_mul_of_one_le_right (by positivity) hμ2
    have h1 : 1536 * ((h : ℝ) * u ^ (12 : ℕ)) ≤ Real.exp 15 * u ^ (12 : ℕ) * μ ^ 2 := by
      linarith
    have h2 : 1536 * ((h : ℝ) * u ^ (12 : ℕ)) ≤ X * μ ^ (-(1 / 500) : ℝ) := by
      rw [capeps_Xmu hX0 hXlog hμ0]; linarith
    rw [div_le_div_iff₀ hX0 (by norm_num : (0 : ℝ) < 24)]
    nlinarith [h2]
  calc 12 * (W * (C * r / X + 1 / X ^ 2))
      ≤ 12 * (64 * ((h : ℝ) * u ^ (12 : ℕ)) * X
          * (C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2)) := by linarith
    _ = 12 * (128 * C * ((h : ℝ) * u ^ (12 : ℕ)) * Real.log μ * μ ^ (-theta293)
          + 64 * ((h : ℝ) * u ^ (12 : ℕ)) / X) := by rw [hval]
    _ ≤ μ ^ (-(1 / 500) : ℝ) := by linarith

set_option maxHeartbeats 1000000 in
-- same cause: `(h:ℝ)·u¹²` where the landed row carries `u¹²` alone
/-- ⟦SIBLING of `capeps_row_p2` (`S13CapEps:371`) at `W ≤ 64·h·u¹²·X`⟧ — `e^11 → e^18`
(leg 1, through `capeps_Pbig_h`) and `11 → 18` (leg 2). -/
theorem capeps_row_p2_h {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (hX0 : 0 < X) (hXlog : Real.log X = μ)
    (hW0 : 0 ≤ W) (hW : W ≤ 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 2 * μ) (hPr : Real.exp (μ ^ (1 - theta293)) ≤ Pr) :
    12 * (W * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2)) ≤ μ ^ (-(1 / 500) : ℝ) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Real.log μ := by linarith
  have hp12 : (0 : ℝ) < u ^ (12 : ℕ) := pow_pos hu0 12
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hexp7 := h_le_exp_seven hh hh7
  have hPr0 : (0 : ℝ) < Pr := lt_of_lt_of_le (Real.exp_pos _) hPr
  have hXne : X ≠ 0 := ne_of_gt hX0
  have hPne : Pr ≠ 0 := ne_of_gt hPr0
  have hK0 : (0 : ℝ) < μ ^ (-(1 / 500) : ℝ) := Real.rpow_pos_of_pos hμ0 _
  have hS0 : (0 : ℝ) ≤ 16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2 := by
    have h1 : (0 : ℝ) ≤ 16 * β / (X * Pr) := by positivity
    have h2 : (0 : ℝ) ≤ 4 * β ^ 2 / X ^ 2 := by positivity
    linarith
  have hprod : W * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2)
      ≤ 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2) :=
    mul_le_mul_of_nonneg_right hW hS0
  have hval : 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2)
      = 1024 * ((h : ℝ) * u ^ (12 : ℕ)) * β / Pr
        + 256 * ((h : ℝ) * u ^ (12 : ℕ)) * β ^ 2 / X := by
    field_simp
    ring
  have he11 : (49152 : ℝ) ≤ Real.exp 11 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hz : Real.exp 11 = (Real.exp 1) ^ (11 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7182818283 : ℝ) ^ (11 : ℕ) ≤ (Real.exp 1) ^ (11 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 11
    have : (49152 : ℝ) ≤ (2.7182818283 : ℝ) ^ (11 : ℕ) := by norm_num
    rw [hz]; linarith
  have he18 : (49152 : ℝ) * (h : ℝ) ≤ Real.exp 18 := by
    have hsum : Real.exp 18 = Real.exp 11 * Real.exp 7 := by rw [← Real.exp_add]; norm_num
    rw [hsum]
    exact mul_le_mul he11 hexp7 (by positivity) (Real.exp_pos 11).le
  have hlegA : 12 * (1024 * ((h : ℝ) * u ^ (12 : ℕ)) * β / Pr)
      ≤ μ ^ (-(1 / 500) : ℝ) / 2 := by
    have hstone := capeps_Pbig_h hu hμ hΛ
    have h500 : (0 : ℝ) < μ ^ ((1 : ℝ) / 500) := Real.rpow_pos_of_pos hμ0 _
    have hPb : 49152 * ((h : ℝ) * u ^ (12 : ℕ)) * μ * μ ^ ((1 : ℝ) / 500) ≤ Pr := by
      have h1 : (49152 * (h : ℝ)) * (u ^ (12 : ℕ) * μ * μ ^ ((1 : ℝ) / 500))
          ≤ Real.exp 18 * (u ^ (12 : ℕ) * μ * μ ^ ((1 : ℝ) / 500)) :=
        mul_le_mul_of_nonneg_right he18 (by positivity)
      nlinarith [h1, hstone]
    have hmul : 49152 * ((h : ℝ) * u ^ (12 : ℕ)) * μ
          * (μ ^ ((1 : ℝ) / 500) * μ ^ (-(1 / 500) : ℝ))
        ≤ Pr * μ ^ (-(1 / 500) : ℝ) := by
      have := mul_le_mul_of_nonneg_right hPb hK0.le
      nlinarith [this]
    have hone : μ ^ ((1 : ℝ) / 500) * μ ^ (-(1 / 500) : ℝ) = 1 := by
      rw [← Real.rpow_add hμ0, show (1 : ℝ) / 500 + -(1 / 500) = 0 by ring, Real.rpow_zero]
    rw [hone, mul_one] at hmul
    have hβμ : 12 * (1024 * ((h : ℝ) * u ^ (12 : ℕ)) * β)
        ≤ 24576 * ((h : ℝ) * u ^ (12 : ℕ)) * μ := by nlinarith [hp12, hh0]
    rw [mul_div_assoc', div_le_iff₀ hPr0]
    linarith [hmul, hβμ]
  have hlegB : 12 * (256 * ((h : ℝ) * u ^ (12 : ℕ)) * β ^ 2 / X)
      ≤ μ ^ (-(1 / 500) : ℝ) / 2 := by
    have hstone := capeps_bigexp_60 hu hμ hΛ (by norm_num : (18 : ℝ) ≤ 60)
    have he18b : (24576 : ℝ) * (h : ℝ) ≤ Real.exp 18 := by
      have hsum : Real.exp 18 = Real.exp 11 * Real.exp 7 := by rw [← Real.exp_add]; norm_num
      rw [hsum]
      exact mul_le_mul (by linarith : (24576 : ℝ) ≤ Real.exp 11) hexp7 (by positivity)
        (Real.exp_pos 11).le
    have h1 : 24576 * ((h : ℝ) * u ^ (12 : ℕ)) * μ ^ 2 ≤ X * μ ^ (-(1 / 500) : ℝ) := by
      rw [capeps_Xmu hX0 hXlog hμ0]
      have hmul : (24576 * (h : ℝ)) * (u ^ (12 : ℕ) * μ ^ 2)
          ≤ Real.exp 18 * (u ^ (12 : ℕ) * μ ^ 2) :=
        mul_le_mul_of_nonneg_right he18b (by positivity)
      nlinarith [hmul, hstone]
    have hβsq : β ^ 2 ≤ 4 * μ ^ 2 := by nlinarith
    have h2 : 12 * (256 * ((h : ℝ) * u ^ (12 : ℕ)) * β ^ 2)
        ≤ 12288 * ((h : ℝ) * u ^ (12 : ℕ)) * μ ^ 2 := by
      nlinarith [hp12, hh0, hβsq]
    rw [mul_div_assoc', div_le_div_iff₀ hX0 (by norm_num : (0 : ℝ) < 2)]
    linarith [h1, h2]
  calc 12 * (W * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2))
      ≤ 12 * (64 * ((h : ℝ) * u ^ (12 : ℕ)) * X
          * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2)) := by linarith
    _ = 12 * (1024 * ((h : ℝ) * u ^ (12 : ℕ)) * β / Pr)
          + 12 * (256 * ((h : ℝ) * u ^ (12 : ℕ)) * β ^ 2 / X) := by rw [hval]; ring
    _ ≤ μ ^ (-(1 / 500) : ℝ) := by linarith

end RowsH


/-! ## ⟦§6 — THE `εr` PAGE, AND ⟦R KILL 1⟧⟧

The register's fourth output carries the `h`; the three rows above absorb it.  The one place
the inflation cannot be absorbed is `s13CapEps_all`'s FOURTH CONJUNCT, `q ≤ arcDen 12 Hreg`,
which is **false at `SocketBaseLH h`** with `Hreg := H` — only `q ≤ h·arcDen 12 H` is
available.  ⟦R KILL 1⟧'s repair, taken here: state it at **`Hreg := A + s`** instead, where
`arcDen 12 (A+s) = (log (A+s))^12` is exactly the `q_logX` field the grid page already proves
at `LH` with its conclusion unchanged.  The structure field it lands in
(`S13CapGatePerBlock_L_gk.q_arcDen`, `S13CapGateLinear:187`) is **read nowhere in the corpus**
— three declarations, five `:= e4` assignments, docstrings, zero reads — and `Hreg` occurs in
that structure only there, so no landed object changes and nothing downstream can observe the
move. -/

/-- ⟦THE REGISTER AT THE INFLATED SOCKET⟧ — first three outputs byte-identical, the fourth
carrying the `h` that conjunct 5 now supplies. -/
theorem s13_capEps_register_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (H : ℝ)
      ∧ (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ)
      ∧ Real.log (H : ℝ) / 2 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ))
      ∧ (q.totient : ℝ) ≤ (h : ℝ) * (Real.log (H : ℝ)) ^ (12 : ℕ) := by
  have hlo : R.Hlo ≤ H := hb.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have hz := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at hz
  have hu21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (H : ℝ) :=
    le_trans capeps_ten21_le_exp50 hexp50
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA_LH hh hh7 hfl hb
  have hsharp := s13_socketBase_loglogA_sharp_LH hh hh7 hfl hb
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hmono : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := Real.log_le_log hA0 hAX
  have hll : Real.log (Real.log (A : ℝ)) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    Real.log_le_log (by linarith) hmono
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hqQ : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H := hb.2.2.2.2.1
  rw [harcpow] at hqQ
  have htot : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  exact ⟨hu21, by linarith, by linarith, by linarith⟩

/-- ⟦`abs8640` at the inflated socket⟧ — COPY on the `_LH` substrate. -/
theorem s13CapEps_abs8640_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ} {εr : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hεr : theta293 - 1 / 500 ≤ εr) :
    (8640 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ εr := by
  obtain ⟨-, hμ, -, -⟩ := s13_capEps_register_LH hh hh7 hfl hb
  exact le_trans (s13_abs8640_at_shift_LH hh hh7 hfl hb)
    (Real.rpow_le_rpow_of_exponent_le (by linarith) hεr)

/-- ⭐ ⟦R KILL 1⟧ **`q_arcDen` RE-BASED TO `Hreg := A + s`** — the landed statement
`q ≤ arcDen 12 H` is FALSE at `SocketBaseLH h`; at the wire's own base `A + s` it is exactly
the grid page's `q_logX`, whose `LH` conclusion is unchanged. -/
theorem s13CapEps_q_arcDen_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    (q : ℝ) ≤ arcDen 12 (A + s) := by
  have harcpow : arcDen 12 (A + s) = Real.log (((A + s : ℕ)) : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [harcpow]
  exact s13CapGrid_q_logX_LH hh hh7 hfl hb

/-- ⟦`EP2_gate` at the inflated socket⟧ — the whole `EP₂` group, through the three `_h` rows. -/
theorem s13CapEps_EP2_gate_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {M H L q j A s P Q : ℕ} {C Tann εr : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hεr : theta293 - 1 / 500 ≤ εr) (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hT0 : 0 ≤ Tann) (hTX : Tann ≤ (((A + s : ℕ)) : ℝ))
    (hP83 : P83 (((A + s : ℕ)) : ℝ) theta293 ≤ (P : ℝ))
    (hgrade : Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log (((A + s : ℕ)) : ℝ))
              * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293))) :
    12 * s13CapEP2 C q (A + s) P Q Tann
      ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + εr) := by
  obtain ⟨hu, hμ, hΛ, hφ⟩ := s13_capEps_register_LH hh hh7 hfl hb
  set u : ℝ := Real.log (H : ℝ) with hudef
  set X : ℝ := (((A + s : ℕ)) : ℝ) with hXdef
  set μ : ℝ := Real.log X with hμdef
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hX1 : (1 : ℝ) < X := by
    rcases lt_or_ge 1 X with hc | hc
    · exact hc
    · have hnp : Real.log X ≤ 0 := Real.log_nonpos (by positivity) hc
      rw [← hμdef] at hnp
      linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hp12 : (0 : ℝ) < u ^ (12 : ℕ) := pow_pos hu0 12
  have hu121 : (1 : ℝ) ≤ u ^ (12 : ℕ) := one_le_pow₀ (by linarith)
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hhu121 : (1 : ℝ) ≤ (h : ℝ) * u ^ (12 : ℕ) := by nlinarith
  have hhu0 : (0 : ℝ) < (h : ℝ) * u ^ (12 : ℕ) := by linarith
  have hφ0 : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  have hq : 0 < q := hb.2.2.2.1
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have htot : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hWval : s13CapEpsW q (A + s) Tann
      = 4 * (2 * (q.totient : ℝ) * Tann + 7 * (q.totient : ℝ) * (2 * X) / q) := by
    simp only [s13CapEpsW, hXdef]
    push_cast
    ring
  have hW0 : 0 ≤ s13CapEpsW q (A + s) Tann := by
    rw [hWval]
    have h1 : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * Tann := by positivity
    have h2 : (0 : ℝ) ≤ 7 * (q.totient : ℝ) * (2 * X) / q := by positivity
    linarith
  have hW : s13CapEpsW q (A + s) Tann ≤ 64 * ((h : ℝ) * u ^ (12 : ℕ)) * X := by
    rw [hWval]
    have h1 : 2 * (q.totient : ℝ) * Tann ≤ 2 * ((h : ℝ) * u ^ (12 : ℕ)) * X := by nlinarith
    have hfrac : 7 * (q.totient : ℝ) * (2 * X) / q ≤ 14 * X := by
      rw [div_le_iff₀ hqR]
      nlinarith
    nlinarith
  have hrow1 : 12 * (4160 * (q.totient : ℝ) * μ ^ (-theta293)) ≤ μ ^ (-(1 / 500) : ℝ) :=
    capeps_row_phi_h hh hh7 hu hμ hΛ hφ0 hφ
  have hrow3 : 12 * (s13CapEpsW q (A + s) Tann * s13MtailBand C (A + s) P Q)
      ≤ μ ^ (-(1 / 500) : ℝ) := by
    rw [s13MtailBand]
    exact capeps_row_tail_h hh hh7 hu hμ hΛ hX0 rfl hW0 hW hC0 hC hgrade
  have hrow2 : 12 * (s13CapEpsW q (A + s) Tann
      * (16 * Real.logb 2 (2 * X) / (X * (P : ℝ)) + endMass (A + s)))
      ≤ μ ^ (-(1 / 500) : ℝ) := by
    have hend : endMass (A + s) = 4 * (Real.logb 2 (2 * X)) ^ 2 / X ^ 2 := by
      rw [endMass]
    have hβ0 : (0 : ℝ) ≤ Real.logb 2 (2 * X) :=
      Real.logb_nonneg (by norm_num) (by linarith)
    have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hβ : Real.logb 2 (2 * X) ≤ 2 * μ := by
      have hlog : Real.log (2 * X) = Real.log 2 + μ := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hX0)]
      rw [Real.logb, hlog, div_le_iff₀ (by linarith)]
      nlinarith
    have hPr : Real.exp (μ ^ (1 - theta293)) ≤ (P : ℝ) := by
      have hz : P83 X theta293 = Real.exp (μ ^ (1 - theta293)) := by rw [P83]
      rw [← hz]; exact hP83
    rw [hend]
    exact capeps_row_p2_h hh hh7 hu hμ hΛ hX0 rfl hW0 hW hβ0 hβ hPr
  have hmax : s13CapEP2 C q (A + s) P Q Tann ≤ μ ^ (-(1 / 500) : ℝ) / 12 := by
    rw [s13CapEP2]
    refine max_le (by linarith) (max_le ?_ (by linarith))
    have := hrow2
    linarith
  have hmono : μ ^ (-(1 / 500) : ℝ) ≤ μ ^ (-theta293 + εr) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  linarith

/-- ⟦THE `εr` GROUP AT THE INFLATED SOCKET⟧ — the seven fields in structure order, with the
fourth stated at `Hreg := A + s` per ⟦R KILL 1⟧.  Fields 1, 5, 6, 7 are socket-blind and
reuse the LANDED lemmas verbatim: `s13CapEps_epsr_nonneg`, `_phi_row`, `_p2_row`,
`_tail_row` take no socket binder at all, so the wave does not owe them twins. -/
theorem s13CapEps_all_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {M H L q j A s P Q : ℕ} {C Tann εr : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hεr : theta293 - 1 / 500 ≤ εr) (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hT0 : 0 ≤ Tann) (hTX : Tann ≤ (((A + s : ℕ)) : ℝ))
    (hP83 : P83 (((A + s : ℕ)) : ℝ) theta293 ≤ (P : ℝ))
    (hgrade : Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log (((A + s : ℕ)) : ℝ))
              * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293))) :
    0 ≤ εr
      ∧ (8640 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ εr
      ∧ 12 * s13CapEP2 C q (A + s) P Q Tann
          ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + εr)
      ∧ (q : ℝ) ≤ arcDen 12 (A + s)
      ∧ 4160 * (q.totient : ℝ) * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
          ≤ s13CapEP2 C q (A + s) P Q Tann
      ∧ 4 * (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * (A + s) : ℕ)) : ℝ) / q)
          * (16 * Real.logb 2 (2 * (((A + s : ℕ)) : ℝ))
              / ((((A + s : ℕ)) : ℝ) * (P : ℝ)) + endMass (A + s))
          ≤ s13CapEP2 C q (A + s) P Q Tann
      ∧ 4 * (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * (A + s) : ℕ)) : ℝ) / q)
          * s13MtailBand C (A + s) P Q
          ≤ s13CapEP2 C q (A + s) P Q Tann :=
  ⟨s13CapEps_epsr_nonneg hεr, s13CapEps_abs8640_LH hh hh7 hfl hb hεr,
    s13CapEps_EP2_gate_LH hh hh7 hfl hb hεr hC0 hC hT0 hTX hP83 hgrade,
    s13CapEps_q_arcDen_LH hh hh7 hfl hb, s13CapEps_phi_row C q (A + s) P Q Tann,
    s13CapEps_p2_row C q (A + s) P Q Tann, s13CapEps_tail_row C q (A + s) P Q Tann⟩

/-- ⟦THE PINS' TWO SIDE FACTS at the inflated socket⟧ — COPY: it reads only the register's
first three outputs, and those are byte-identical at `LH`. -/
theorem s13CapEps_pin_floors_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    (4 : ℝ) ≤ Real.log (P83 (((A + s : ℕ)) : ℝ) theta293)
      ∧ (4 : ℝ) ≤ Real.log (Q83 (((A + s : ℕ)) : ℝ)) := by
  obtain ⟨hu, hμ, hΛ, -⟩ := s13_capEps_register_LH hh hh7 hfl hb
  set X : ℝ := (((A + s : ℕ)) : ℝ) with hXdef
  set μ : ℝ := Real.log X with hμdef
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛbig : (5 : ℝ) * 10 ^ (20 : ℕ) ≤ Real.log μ := by
    have : (10 : ℝ) ^ (21 : ℕ) = 2 * (5 * 10 ^ (20 : ℕ)) := by norm_num
    linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hθ32 : theta293 < 1 / 32 := theta293_lt_one_div_32
  have hθ0 : (0 : ℝ) < theta293 := theta293_pos
  constructor
  · rw [P83, Real.log_exp]
    have hrw : μ ^ (1 - theta293) = Real.exp ((1 - theta293) * Real.log μ) := by
      rw [Real.rpow_def_of_pos hμ0]; ring_nf
    have hhalf : Real.exp (Real.log μ / 2) ≤ μ ^ (1 - theta293) := by
      rw [hrw]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hlin : Real.log μ / 2 + 1 ≤ Real.exp (Real.log μ / 2) :=
      Real.add_one_le_exp _
    linarith
  · rw [Q83, Real.log_exp, le_div_iff₀ hΛ0]
    have hsq : (Real.log μ) ^ 2 / 4 ≤ μ := by
      have hz := capeps_sq_le_exp hΛ0.le
      rwa [Real.exp_log hμ0] at hz
    nlinarith [hsq, hΛbig, hΛ0]

/-- ⟦THE PINS SUPPLY at the inflated socket⟧ — COPY, same reason. -/
theorem s13CapEps_pins_supply_LH {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) :
    P83 (((A + s : ℕ)) : ℝ) theta293
        ≤ ((⌈P83 (((A + s : ℕ)) : ℝ) theta293⌉₊ : ℕ) : ℝ)
      ∧ Real.log ((⌈P83 (((A + s : ℕ)) : ℝ) theta293⌉₊ : ℕ) : ℝ)
            / Real.log ((⌊Q83 (((A + s : ℕ)) : ℝ)⌋₊ : ℕ) : ℝ)
          ≤ 2 * (Real.log (Real.log (((A + s : ℕ)) : ℝ))
                  * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)) := by
  obtain ⟨hu, hμ, hΛ, -⟩ := s13_capEps_register_LH hh hh7 hfl hb
  obtain ⟨hP4, hQ4⟩ := s13CapEps_pin_floors_LH hh hh7 hfl hb
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  refine ⟨Nat.le_ceil _, m4_tail_grade_rounded (by linarith) (by linarith) hP4 hQ4⟩


/-! ## ⟦§7 — THE GRID ASSEMBLER AT THE INFLATED SOCKET⟧

The landed `s13CapGrid_all_L_gk` opens with `have hbb : SocketBase := socketBase_of_socketBaseL
hM hb` and feeds `hbb` to every grid leaf.  **That line is the whole reason this wave exists**:
`SocketBaseLH h → SocketBase` is false at `h ≥ 2`, so it simply disappears here and each leaf
takes the `LH` binder directly. -/

theorem s13CapGrid_Q2_reg_LH_gk {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} (hM : 1 ≤ M)
    (hb : SocketBaseLH h R M H L q j A s) (hblock : s13BlockFloor_L_gk K M ≤ A + s) :
    Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) :=
  (s13_doorRowZeroBase_five_L_gk K hM hblock hb.2.2.2.2.2.2.1).2.1

theorem s13CapGrid_all_LH_gk {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} {cs T : ℝ}
    (hM : 1 ≤ M) (hcs : 1 ≤ cs) (hfl : loglogFloor50 ≤ R.Hlo)
    (hb : SocketBaseLH h R M H L q j A s) (hblock : s13BlockFloor_L_gk K M ≤ A + s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T)
    (hThi : 2 * T ≤ (((A + s : ℕ)) : ℝ)) :
    8 ≤ Real.log (((A + s : ℕ)) : ℝ)
    ∧ 2 ≤ H83 (((A + s : ℕ)) : ℝ) theta293
    ∧ (q : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ 12
    ∧ Real.log ((q : ℝ) * (2 * T)) ≤ s13Lr (A + s)
    ∧ P83 (((A + s : ℕ)) : ℝ) theta293 ≤ ((s13BandP (A + s) : ℕ) : ℝ)
    ∧ Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
        ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ))
    ∧ 0 < s13BandQ (A + s)
    ∧ ((s13BandQ (A + s) : ℕ) : ℝ) ≤ Q83 (((A + s : ℕ)) : ℝ)
    ∧ s13BandP (A + s) ≤ s13BandQ (A + s)
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        H83 (((A + s : ℕ)) : ℝ) theta293 ≤ (i : ℝ))
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        3 ≤ ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i)
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
          ≤ (q : ℝ) * (2 * T))
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        30 ≤ Real.log ((q : ℝ) * (2 * T))
          / Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i))
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
          ≤ (2 * T) ^ 10)
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i)
          ≤ s13Lr (A + s))
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        420 * s13Lr (A + s) * (s13Lr (A + s)) ^ ((3 : ℝ) / 4)
            * (Real.log (s13Lr (A + s))) ^ 5
          ≤ cs * (Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293)
              (s13BandP (A + s)) i)) ^ 2)
    ∧ 100 * Real.log ((s13BandQ (A + s) : ℕ) : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ)
    ∧ ((Nat.sqrt (A + s) : ℝ) + 1)
          * ∏ p ∈ primeBand (s13BandP (A + s)) (s13BandQ (A + s)), (1 + 3 / (p : ℝ))
        ≤ (((A + s : ℕ)) : ℝ)
          * (Real.log ((s13BandP (A + s) : ℕ) : ℝ)
              / Real.log ((s13BandQ (A + s) : ℕ) : ℝ)) := by
  have hμ : (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := s13CapGrid_mu_2000_LH hh hh7 hfl hb
  have hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    s13CapGrid_Lambda_lo_LH hh hh7 hfl hb
  exact ⟨s13CapGrid_logX_eight_LH hh hh7 hfl hb, s13CapGrid_H83_two hμ hΛ, s13CapGrid_q_logX_LH hh hh7 hfl hb,
    s13CapGrid_logqT_L_LH hh hh7 hfl hb hTlo hThi, s13CapGrid_P_low (A + s),
    s13CapGrid_Q2_reg_LH_gk hh hh7 K hM hb hblock, s13CapGrid_Q_pos hμ, s13CapGrid_Q_high (A + s),
    s13CapGrid_P_le_Q hμ hΛ, s13CapGrid_Hj hμ hΛ, s13CapGrid_B3 hμ hΛ,
    s13CapGrid_BT_LH hh hh7 hfl hb hTlo, s13CapGrid_kappa30_LH hh hh7 hfl hb hTlo, s13CapGrid_BT10_LH hh hh7 hfl hb hTlo,
    s13CapGrid_WL hμ hΛ, s13CapGrid_gate hcs hμ hΛ, s13CapGrid_Q_hundred hμ hΛ,
    s13CapGrid_band_product hμ hΛ⟩

end Salt.MR
