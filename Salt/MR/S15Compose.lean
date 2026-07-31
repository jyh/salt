/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S12ConstCompose
import Salt.MR.S11HoistGrade

/-!
# ⟦S15-COMPOSE⟧ — THE CONST CAPSTONE, FIRED

PURELY ADDITIVE: no landed declaration is touched anywhere in this file.

⟦THE MISSION⟧ (maestro ruling 11, `docs/blueprints/flags.md` 2026-07-30 22:50) — fire
`S12ConstCompose.logChowla2_capstone_final_const'` at a working point and discharge as many of
its SIXTEEN residue binders as the landed supply allows, naming every survivor exactly.

## §A — THE INSTANTIATION

| slot | choice | source |
|---|---|---|
| `Aexp` | `s13Aexp = 3` | ⟦F1⟧, `S13BandBase.lean:71` — forced by `doorBandBase_family` |
| `Cp` | `0` | ruling 8; `dens` is FREE there (`s15_dens_at_zero`) |
| `C₁` | `fun _ => 1` | `S13BandGate.C1_one` free, `DoorArithFrameRho.C1_nonneg` free |
| `M₀` | `s13BandM0 R ρ C₁` | ⟦F2⟧, the shared pin — the band and the arith frame agree |
| `_epsf` | `fun _ => 0` | inert |
| `epsrf` | `fun _ => θ₂₉₃ − 1/500` | ruling 8's honest endpoint; ⟦B2⟧'s UPPER end |
| `Kf` | `0` | `DoorArithFrameRho.Knonneg` |
| `k` | `doorCount R.ω` | `s13_doorGates_of_MSelect'` |
| `ρ` | `doorRhoOfDelta (s12DeltaSock δ₀ K)` | the twin's own |
| `U1floor` | `≥ Hcap` | the EDGE-5 base pin: `R.Hlo` is PINNED to `U1floor` |
| `g` | `s15Arm δ₀ ρ` | the demoted arm + the `ρ`-frame's own arm, in one `max` |
| `M` | the caller's, under `S15Sel` | every `M`-floor/`M`-upper written out |

## §B — THE COMPOSE LEDGER: sixteen binders, discharge source, survivor

| # | binder | discharged from | where |
|---|---|---|---|
| 1 | `hgates` | `s13_doorGates_of_MSelect'` + `S15Sel` | `S13MSelect2.lean:406` |
| 2 | `hend` | `s13_endpoint_of_arm'` (the demoted arm) | `S13FramesA.lean:892` |
| 3 | `hj0` | `s13_g2_jfloor` at `Λ := loglog H₊` | `S13FramesA.lean:500` |
| 4 | `hdgate` | `s13_gate8` at `Λ := loglog H₊` | `S13FramesA.lean:528` |
| 5 | `hfit` | `s13_smallGradeFits_of_MSelect'` | `S13MSelect2.lean:420` |
| 6 | `hbf` | `doorBaseFrame_at_socket` | `M4AssemblyFrames.lean:167` |
| 7 | `hgP1` | `s15_gP1_of_budget` (CONST-VERDICT §C) | §1 below |
| 8 | `hgRows` | `s15_gRows_const_at_socket` (CONST-VERDICT §H) | §1 below |
| 9 | `hthr` | `s12c_eps_threshold_at_socket` | `S12ConstCompose.lean:239` |
| 10 | `_heps293` | `s15_heps293_at_socket` (CONST-VERDICT §F) | §1 below |
| 11 | `hband4096` | `s15_hband4096_at_socket` (CONST-VERDICT §F) | §1 below |
| 12 | `_hepsr` | `s13_theta293_margin_lo` + `le_rfl` | `S13MSelect2.lean:66` |
| 13 | `hbase5` | `s13_doorRowZeroBase_five` + `s15_block_at_socket` | `S13FramesA.lean:760` |
| 14 | `hcapraw` | **THE SURVIVOR** — see §C | — |
| 15 | `hbandbase` | `doorBandBase_family` + `s15_bandGate_of_grade` | `S13BandBase.lean:509` |
| 16 | `harith` | `s15_doorArithFrameRho_family` | §2 below |

## §C — THE ONE SURVIVOR, AND THE CARRIED REGISTER

⟦THE SURVIVOR⟧ `hcapraw` — the ⟦B4⟧ RAW CROSSING BOUND.  WIDTH-SCOPE (flags, 2026-07-30
22:50) proves in the kernel that its only landed route — the cap bundle's `budget` field —
demands a regime window of width `λ₊ − λ₋ ≤ 7.1448`, while `probe_regime_width_forced` shows
EVERY `ChowlaRegime` has `λ₊ ≥ λ₋³`.  Deficit `5·10³×`.  So the crossing bound is carried here
as a hypothesis, honestly named, and its re-supply is the Captain's design question.

⟦THE CARRIED REGISTER⟧ the fifteen discharges above are not free: each spends numeric
conditions on the OPAQUE constants of the road (`Cg`, `δ₀`, `K`, `Ct`, `x₀`, `C'`) and on the
regime scales `λ₋ := loglog H₋`, `Λ := loglog H₊`.  Those conditions are collected, written
out, in TWO named bundles and nowhere else:

* `S15Sel` (§4) — the `M`-selection system: eleven explicit inequalities (three `M`-lowers,
  two `M`-uppers, the clearing charge and four budget lines, plus `1 ≤ M`).  Nothing opaque is
  hidden inside any field.
* ONE line of `S13BandGate` (`S13BandBase.lean:481`), carried beside the crossing bound:
  `grade`, `8·C' ≤ (log 2·doorRowFloor M)^{2.501}`.  This is the ⟦B5⟧ item `S14Compose`'s
  frontier names — the twin reveals `C'` AFTER `M`, so `S11HoistGrade.s11_grade_absorption`
  (which closes it at the GRADED wire `m4_fuse_hband_of_bandBase_graded`, `C' ≤ Cb·M^{2.1}`
  with `Cb` in the top constant block) cannot be spent at the UNGRADED wire the landed const
  twin consumes.  The other four band lines ARE discharged: `x0_le` by the `M`-floor
  `x₀ ≤ M` (§3b), `C1_one` free at `C₁ ≡ 1`, `err_res` by `S15Sel.err`, `block` (⟦F3⟧) by
  `s15_block_at_socket` off the regime's own `hPHheadroom` (§3b).

⚠ **THE REGISTER IS CARRIED, NOT PROVED.**  `S15Sel`'s `half` field (`winFit`, an `M`-UPPER
of size `log H₋`) and its `gRows` field (an `M`-LOWER of size `Λ`) are jointly satisfiable
only when `Λ ≲ 4·10⁸·λ₋` — CONST-VERDICT's `M`-window — and the twin's payload bounds `Λ`
only by the `9/2` tower `Λ ≤ λ₋^{9/2}`.  This file does NOT claim the window is nonempty at
every regime; it claims exactly what it proves: **given the register and the crossing bound,
the capstone fires**.

## §D — CONTENTS

* §1 the CONST-VERDICT certificates, ported (`scratchpad/constv/ConstVerdictAll.lean`);
* §2 the arith frame at the socket, at the WEAK anchor (no `2^{2483}` `M`-floor);
* §3 the arm `s15Arm` and its monotonicity;
* §3b ⟦F3⟧'s block floor and the opaque threshold, both paid;
* §4 `S15Sel`, the `M`-selection register;
* §5 ⟦THE COMPOSE⟧ `logChowla2_conditional`;
* §6 the witnessed-scale corollary;
* §7 the inhabitation certificate (the vacuity fence);
* §8 ⟦GRADE-RECUT⟧ the same compose at the GRADED twin (`S12ConstCompose` §5): `grade` PAID
  inside the twin, so the carried list is `S15Sel` + `S15CrossingBound` + one `ℕ`-floor.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE CONST-VERDICT CERTIFICATES, PORTED

`scratchpad/constv/ConstVerdictAll.lean`, kernel-verified at the CONST-VERDICT sitting
(2026-07-30 21:49), carried here verbatim so the compose owns them.  The λ-engine and the
socket's `loglog X_d` figure are NOT re-derived: `S12ConstCompose.s12c_lambda_core` (at the
`500×` coefficient, hence strictly stronger than the verdict's) and `s12c_llX_ge` are used. -/

/-- `2.1673·10¹⁰ ≤ e²⁴`. -/
theorem s15_exp24 : (21672921600 : ℝ) ≤ Real.exp 24 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h : Real.exp 24 = (Real.exp 1) ^ (24 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : (2.7 : ℝ) ^ (24 : ℕ) ≤ (Real.exp 1) ^ (24 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h1.le 24
  have hn : (21672921600 : ℝ) ≤ (2.7 : ℝ) ^ (24 : ℕ) := by norm_num
  rw [h]; linarith

/-- `1.4102·10¹¹ ≤ e²⁶`. -/
theorem s15_exp26 : (141018476544 : ℝ) ≤ Real.exp 26 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h : Real.exp 26 = (Real.exp 1) ^ (26 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : (2.7 : ℝ) ^ (26 : ℕ) ≤ (Real.exp 1) ^ (26 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h1.le 26
  have hn : (141018476544 : ℝ) ≤ (2.7 : ℝ) ^ (26 : ℕ) := by norm_num
  rw [h]; linarith

/-- `4.1612·10¹¹ ≤ e²⁷`. -/
theorem s15_exp27 : (416120094720 : ℝ) ≤ Real.exp 27 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h : Real.exp 27 = (Real.exp 1) ^ (27 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : (2.7 : ℝ) ^ (27 : ℕ) ≤ (Real.exp 1) ^ (27 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h1.le 27
  have hn : (416120094720 : ℝ) ≤ (2.7 : ℝ) ^ (27 : ℕ) := by norm_num
  rw [h]; linarith

/-- `𝒫₁ ≤ 𝒫₂` at the door family. -/
theorem s15_calP_one_le_two {M : ℕ} (hM : 1 ≤ M) :
    (calP (Adoor M) (3072 * M) 1) ≤ (calP (Adoor M) (3072 * M) 2) := by
  have hE : calE (Adoor M) (3072 * M) 1 ≤ calE (Adoor M) (3072 * M) 2 := by
    have h1 : calE (Adoor M) (3072 * M) 1 = Adoor M := calE_one _ _
    have h2 : calE (Adoor M) (3072 * M) 2 = Adoor M * (3072 * M) * 4 := by
      simp [calE, Nat.factorial]
    rw [h1, h2]
    calc Adoor M = Adoor M * 1 * 1 := by ring
      _ ≤ Adoor M * (3072 * M) * 4 := by
          have : 1 ≤ 3072 * M := by omega
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ this) (by omega)
  rw [calP, calP]
  exact Nat.pow_le_pow_right (by norm_num) hE

/-- `log 𝒬₁ = doorRowFloor M · log 2` at the door family. -/
theorem s15_log_calQK_one (M : ℕ) :
    Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)
      = ((doorRowFloor M : ℕ) : ℝ) * Real.log 2 := by
  rw [log_calQK, calE_one, doorRowFloor]
  push_cast; ring

/-- `2^36 ≤ doorRowFloor M`. -/
theorem s15_doorRowFloor_ge {M : ℕ} (hM : 1 ≤ M) : (2 : ℕ) ^ 36 ≤ doorRowFloor M := by
  rw [doorRowFloor]
  calc (2 : ℕ) ^ 36 ≤ Adoor M := Adoor_ge M
    _ = 1 * Adoor M := (one_mul _).symm
    _ ≤ M * Adoor M := Nat.mul_le_mul_right _ hM

theorem s15_log_calQK_one_pos {M : ℕ} (hM : 1 ≤ M) :
    (0 : ℝ) < Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := by
  rw [s15_log_calQK_one]
  have h1 : (1 : ℕ) ≤ doorRowFloor M := le_trans (by norm_num) (s15_doorRowFloor_ge hM)
  have h1R : (1 : ℝ) ≤ ((doorRowFloor M : ℕ) : ℝ) := by exact_mod_cast h1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

theorem s15_loglogQ1_nonneg {M : ℕ} (hM : 1 ≤ M) :
    (0 : ℝ) ≤ Real.log (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) := by
  refine Real.log_nonneg ?_
  rw [s15_log_calQK_one]
  have h : (2 : ℕ) ^ 36 ≤ doorRowFloor M := s15_doorRowFloor_ge hM
  have hR : (2 : ℝ) ^ 36 ≤ ((doorRowFloor M : ℕ) : ℝ) := by exact_mod_cast h
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  nlinarith

/-- **⟦`a2Level1` IN CLOSED FORM⟧** — `a2Level1 M = exp(⅓·loglog 𝒬₁ − (1/12)·Adoor M·log 2)`. -/
theorem s15_a2Level1_exp {M : ℕ} (hM : 1 ≤ M) :
    a2Level1 M = Real.exp ((1 / 3) * Real.log (Real.log
        ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ))
      - (1 / 12) * ((Adoor M : ℕ) : ℝ) * Real.log 2) := by
  have hP1pos : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    have h : 0 < calP (Adoor M) (3072 * M) 1 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast h
  have hLQ := s15_log_calQK_one_pos hM
  rw [a2Level1, Real.rpow_def_of_pos hLQ, Real.rpow_def_of_pos hP1pos,
    s13_band_log_calP_one M, ← Real.exp_sub]
  ring_nf

/-- **⟦THE `p²` SLOT AT `constPool`, MET⟧** — one linear budget line, `X_d`-free on BOTH sides:
`27 + 14·loglog H₊ ≤ Adoor M·log 2 + log ρ`. -/
theorem s15_p2_of_budget {M Hhi : ℕ} {ρ : ℝ} (hM : 1 ≤ M) (hρ : 0 < ρ)
    (hbudget : 27 + 14 * Real.log (Real.log (Hhi : ℝ))
      ≤ ((Adoor M : ℕ) : ℝ) * Real.log 2 + Real.log ρ) :
    138240 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
        + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ))
      ≤ 1 / 4 * constPool ρ (Hhi) := by
  have hP1pos : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    have h : 0 < calP (Adoor M) (3072 * M) 1 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast h
  have hP2pos : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ) := by
    have h : 0 < calP (Adoor M) (3072 * M) 2 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast h
  have hP12 : ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
      ≤ ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ) := by
    exact_mod_cast s15_calP_one_le_two hM
  have hinv : 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ)
      ≤ 1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hP1pos hP12
  set E : ℝ := Real.exp (14 * Real.log (Real.log (Hhi : ℝ))) with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hpool : (1 : ℝ) / 4 * constPool ρ Hhi = ρ / (1505064 * E) := by
    rw [constPool_def, hE]; field_simp; ring
  have hkey : 416120094720 * E ≤ ρ * ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    have hmul : ρ * ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
        = Real.exp (Real.log ρ + Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) := by
      rw [Real.exp_add, Real.exp_log hρ, Real.exp_log hP1pos]
    calc 416120094720 * E ≤ Real.exp 27 * E := by nlinarith [s15_exp27, hEpos]
      _ = Real.exp (27 + 14 * Real.log (Real.log (Hhi : ℝ))) := by rw [hE, ← Real.exp_add]
      _ ≤ Real.exp (Real.log ρ + Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) := by
          refine Real.exp_le_exp.mpr ?_
          rw [s13_band_log_calP_one M]; linarith
      _ = ρ * ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := hmul.symm
  have hhalf : 276480 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ 1 / 4 * constPool ρ Hhi := by
    rw [hpool, show (276480 : ℝ) * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
        = 276480 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) by ring,
      div_le_div_iff₀ hP1pos (by positivity)]
    nlinarith [hkey]
  nlinarith [hinv, hhalf, hP1pos]

/-- **⟦THE `level1` SLOT AT `constPool`, MET⟧** — budget form. -/
theorem s15_level1_of_budget {M Hhi : ℕ} {ρ : ℝ} (hM : 1 ≤ M) (hρ : 0 < ρ)
    (hbudget : 26 + 14 * Real.log (Real.log (Hhi : ℝ))
        + (1 / 3) * Real.log (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ))
      ≤ (1 / 12) * ((Adoor M : ℕ) : ℝ) * Real.log 2 + Real.log ρ) :
    14400 * Real.exp 1 ^ 2 * a2Level1 M ≤ 1 / 4 * constPool ρ Hhi := by
  set L : ℝ := Real.log (Real.log (Hhi : ℝ)) with hL
  set Q : ℝ := Real.log (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) with hQ
  set D : ℝ := (1 / 12) * ((Adoor M : ℕ) : ℝ) * Real.log 2 with hD
  set E : ℝ := Real.exp (14 * L) with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hpool : (1 : ℝ) / 4 * constPool ρ Hhi = ρ / (1505064 * E) := by
    rw [constPool_def, hE, hL]; field_simp; ring
  rw [s15_a2Level1_exp hM, hpool, le_div_iff₀ (by positivity)]
  have hid : 14400 * Real.exp 1 ^ 2 * Real.exp ((1 / 3) * Q - D) * (1505064 * E)
      = 21672921600 * Real.exp (2 + (1 / 3) * Q - D + 14 * L) := by
    rw [hE, show Real.exp 1 ^ 2 = Real.exp 2 by rw [← Real.exp_nat_mul]; norm_num]
    rw [show (2 : ℝ) + (1 / 3) * Q - D + 14 * L = 2 + ((1 / 3) * Q - D) + 14 * L by ring,
      Real.exp_add, Real.exp_add]
    ring
  rw [hid]
  have hρexp : ρ = Real.exp (Real.log ρ) := (Real.exp_log hρ).symm
  calc 21672921600 * Real.exp (2 + (1 / 3) * Q - D + 14 * L)
      ≤ Real.exp 24 * Real.exp (2 + (1 / 3) * Q - D + 14 * L) := by
        nlinarith [s15_exp24, Real.exp_pos (2 + (1 / 3) * Q - D + 14 * L)]
    _ = Real.exp (26 + (1 / 3) * Q - D + 14 * L) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (Real.log ρ) := Real.exp_le_exp.mpr (by linarith)
    _ = ρ := hρexp.symm

/-- **⟦THE `𝒯`-LEG GATE AT `constPool`, MET⟧** — `X_d`-free budget line
`29 + log Cs + 14·loglog H₊ ≤ Adoor M·log 2 + log ρ`. -/
theorem s15_gP1_of_budget {M Hhi : ℕ} {Cs ρ : ℝ} (hCs : 0 < Cs) (hρ : 0 < ρ)
    (hbudget : 29 + Real.log Cs + 14 * Real.log (Real.log (Hhi : ℝ))
      ≤ ((Adoor M : ℕ) : ℝ) * Real.log 2 + Real.log ρ) :
    374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ constPool ρ Hhi := by
  have hP1pos : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    have h : 0 < calP (Adoor M) (3072 * M) 1 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast h
  set L : ℝ := Real.log (Real.log (Hhi : ℝ)) with hL
  set E : ℝ := Real.exp (14 * L) with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hpool : constPool ρ Hhi = ρ / (376266 * E) := by
    rw [constPool_def, hE, hL]
  rw [hpool, show (374784 : ℝ) * Cs * Real.exp 3
      * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      = (374784 * Cs * Real.exp 3) / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) by ring,
    div_le_div_iff₀ hP1pos (by positivity)]
  have hP1exp : ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
      = Real.exp (((Adoor M : ℕ) : ℝ) * Real.log 2) := by
    rw [← s13_band_log_calP_one M, Real.exp_log hP1pos]
  have hρexp : ρ = Real.exp (Real.log ρ) := (Real.exp_log hρ).symm
  have hprod : Real.exp (29 + Real.log Cs + 14 * L) = Real.exp 26 * Real.exp 3 * Cs * E := by
    rw [hE, show (29 : ℝ) + Real.log Cs + 14 * L = 26 + (3 + (Real.log Cs + 14 * L)) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hCs]
    ring
  calc 374784 * Cs * Real.exp 3 * (376266 * E)
      = 141018476544 * Real.exp 3 * Cs * E := by ring
    _ ≤ Real.exp 26 * Real.exp 3 * Cs * E := by
        have := s15_exp26
        have hp : (0 : ℝ) < Real.exp 3 * Cs * E := by positivity
        nlinarith
    _ = Real.exp (29 + Real.log Cs + 14 * L) := hprod.symm
    _ ≤ Real.exp (Real.log ρ + ((Adoor M : ℕ) : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = ρ * ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
        rw [Real.exp_add, hP1exp, ← hρexp]

/-- **⟦`dens` IS FREE AT `Cp = 0`⟧**. -/
theorem s15_dens_at_zero {M Hhi : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    5760 * (0 : ℝ) * (2 / (M : ℝ)) ≤ 1 / 4 * constPool ρ Hhi := by
  have := constPool_nonneg (ρ := ρ) (Hhi := Hhi) hρ
  simp only [mul_zero, zero_mul]
  linarith

/-- **⟦THE `endpt` SLOT AT `constPool`⟧** — the only base-READING slot, and it reads the base
from BELOW: `log X_d ≥ 26 + 14·loglog H₊ + log(1/ρ)`. -/
theorem s15_endpt_at_constPool {Xd Hhi : ℕ} {ρ : ℝ} (hXd : 0 < Xd) (hρ : 0 < ρ)
    (hbudget : 26 + 14 * Real.log (Real.log ((Hhi : ℕ) : ℝ)) + (-Real.log ρ)
      ≤ Real.log ((Xd : ℕ) : ℝ)) :
    5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ)) ≤ 1 / 4 * constPool ρ Hhi := by
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := by exact_mod_cast hXd
  set L : ℝ := Real.log (Real.log ((Hhi : ℕ) : ℝ)) with hL
  set E : ℝ := Real.exp (14 * L) with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hpool : (1 : ℝ) / 4 * constPool ρ Hhi = ρ / (1505064 * E) := by
    rw [constPool_def, hE, hL]; field_simp; ring
  rw [hpool, show (5760 : ℝ) * ((2 * Real.exp 1 + 2) / ((Xd : ℕ) : ℝ))
      = (5760 * (2 * Real.exp 1 + 2)) / ((Xd : ℕ) : ℝ) by ring,
    div_le_div_iff₀ hX0 (by positivity)]
  have he : 2 * Real.exp 1 + 2 ≤ 7.44 := by have := Real.exp_one_lt_d9; linarith
  have hXexp : ((Xd : ℕ) : ℝ) = Real.exp (Real.log ((Xd : ℕ) : ℝ)) := (Real.exp_log hX0).symm
  have hρexp : ρ = Real.exp (Real.log ρ) := (Real.exp_log hρ).symm
  calc 5760 * (2 * Real.exp 1 + 2) * (1505064 * E)
      ≤ 5760 * 7.44 * (1505064 * E) := by nlinarith [he, hEpos]
    _ ≤ Real.exp 26 * E := by
        have := s15_exp26
        nlinarith [hEpos]
    _ = Real.exp (26 + 14 * L) := by rw [hE, ← Real.exp_add]
    _ ≤ Real.exp (Real.log ρ + Real.log ((Xd : ℕ) : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = ρ * ((Xd : ℕ) : ℝ) := by rw [Real.exp_add, ← hXexp, ← hρexp]

/-- The λ-engine at the verdict's own coefficient, from `S12ConstCompose`'s stronger one. -/
theorem s15_lambda_core17 {lam : ℝ} (hlam : 50 ≤ lam) :
    14 * lam ^ ((9 : ℝ) / 2) + 1000000000000000 ≤ 0.0017 * Real.exp lam := by
  have h := s12c_lambda_core hlam
  have hp := Real.exp_pos lam
  linarith

/-- **⟦`heps293` AT THE SOCKET⟧** — `(log X_d)^{−θ₂₉₃} ≤ constPool ρ H₊` at every socket base,
from the tower `Λ ≤ λ^{9/2}`, `λ ≥ 50`, and the clearing charge `log(1/ρ) ≤ 10^{14}`. -/
theorem s15_heps293_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hρ : 0 < ρ)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) ^ ((9 : ℝ) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000) :
    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi := by
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
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
  have hll := s12c_llX_ge hfl hb
  have hcore := s15_lambda_core17 hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by
    have : (0 : ℝ) < Real.exp lam / 2 := by positivity
    linarith [hll]
  have hkey : 14 * Λ + 13 + (-Real.log ρ) ≤ theta293 * ll := by
    have h1 : 14 * Λ ≤ 14 * lam ^ ((9 : ℝ) / 2) := by linarith [htow]
    have h2 : theta293 * ll ≥ 0.0034 * (Real.exp lam / 2) := by
      nlinarith [hθ, hll, hll0]
    nlinarith [h1, h2, hcore, hrho]
  linarith [hkey, hlog376]

/-- **⟦`hband4096` AT THE SOCKET⟧** — `4096 ≤ (log X_d)^{1−1/500}·constPool ρ H₊`. -/
theorem s15_hband4096_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hρ : 0 < ρ)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) ^ ((9 : ℝ) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000) :
    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500) * constPool ρ R.Hhi := by
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
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
  have hll := s12c_llX_ge hfl hb
  have hcore := s15_lambda_core17 hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by
    have : (0 : ℝ) < Real.exp lam / 2 := by positivity
    linarith [hll]
  have h1 : 14 * Λ ≤ 14 * lam ^ ((9 : ℝ) / 2) := by linarith [htow]
  have h2 : (1 - (1 : ℝ) / 500) * ll ≥ 0.0017 * Real.exp lam := by nlinarith [hll, hll0]
  linarith [h1, h2, hcore, hrho, hlog376]

/-- **⟦THE ⟦B1'-3⟧ BINDER AT THE CONSTANT POOL, AT EVERY SOCKET BASE⟧**
(`s15_gRows_const_at_socket`) — the exact counterpart of `S14Compose.s14_gRows_kill`, with the
opposite verdict.  ONE `M`-side budget line, `X_d`-FREE, does all four slots. -/
theorem s15_gRows_const_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hM : 1 ≤ M)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) ^ ((9 : ℝ) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000)
    (hbud : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        + (1 / 3) * Real.log (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ))
        + (-Real.log ρ)
      ≤ (1 / 12) * ((Adoor M : ℕ) : ℝ) * Real.log 2) :
    GRowsZeroGate''' M (A + s) 0 (constPool ρ R.Hhi) := by
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  have hQ0 := s15_loglogQ1_nonneg hM
  obtain ⟨-, hL50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hAs : 0 < A + s := by omega
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hllle : Real.log (Real.log (((A + s : ℕ)) : ℝ)) ≤ Real.log (((A + s : ℕ)) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hll := s12c_llX_ge hfl hb
  have hcore := s15_lambda_core17 hlam50
  have hexp0 : (0 : ℝ) < Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) := Real.exp_pos _
  have hendbud : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + (-Real.log ρ)
      ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h1 : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        ≤ 14 * (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) ^ ((9 : ℝ) / 2) := by linarith
    linarith [hcore, hll, hllle, hrho, h1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact s15_level1_of_budget hM hρ0 (by linarith)
  · exact s15_endpt_at_constPool hAs hρ0 hendbud
  · refine s15_p2_of_budget hM hρ0 ?_
    linarith [hbud, hQ0, hL50, hlogρ]
  · exact s15_dens_at_zero hρ0.le

/-! ## §2 — THE ARITHMETIC FRAME AT THE SOCKET, AT THE **WEAK** ANCHOR

`M4AssemblyFrames.doorArithFrameRho_at_socket` discharges `DoorArithFrameRho`'s `anchor` and
`jfloor` fields through `M4ArithRho.m4_arith_anchor_of_C1_rho`, whose hypothesis is the
council's blanket `2484 ≤ log₂M + 1` — an `M`-LOWER of size `2^{2483}`.  Against
`MSelect'.winFit`'s `M`-UPPER `(7/10)·M·Adoor M ≤ log H₋` that floor alone would demand
`λ₋ ≥ 1753`, and the `9/2` tower then puts `Λ` out of reach of every `M`-lower below.

So this section re-assembles the same frame with both fields taken at their OWN statements:

* `anchor` — `14·loglog H + log(1/ρ) + 33 ≤ 3.9·10⁹·(log₂M + 1)`, met at `log₂M + 1 ≥ 1` from
  the register line `14·Λ + log(1/ρ) + 33 ≤ 3.9·10⁹`;
* `jfloor` — `21·loglog H + 2·log(1/ρ) + 28 ≤ j`, met from `j ≥ doorRowFloor M ≥ 2^36` and
  the SAME register line (`3.9·10⁹` bounds the anchor's own bracket, and `1.5×` of it sits
  under `2^36`) — so the window-index floor costs no second line.

Everything else is `doorArithFrameRho_at_socket`'s, term for term, except `M0_window`, which
is taken at ⟦F2⟧'s pin directly (`S13BandBase.s13BandM0_window`) rather than through the
`0.062`-form — the pin's `e/45 = 0.0604` sits BELOW `0.062`, so the readable form is not
available at the pin and the exact one is. -/

/-- **⟦THE `ρ`-FRAME AT ONE SOCKET BASE, AT THE WEAK ANCHOR⟧**
(`s15_doorArithFrameRho_at_socket`) — `K := 0`, `M₀ := s13BandM0 R ρ C₁`, the `g`-arm at
`x₀ := 0`. -/
theorem s15_doorArithFrameRho_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    {C₁ : ℕ → ℝ} (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hanchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33
      ≤ 39 * 10 ^ 8)
    (hHreg : 0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ))
    (hC1 : 0 ≤ C₁ (A + s))
    (hb : SocketBase R M H L q j A s) :
    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
      (s13BandM0 R ρ C₁ (A + s)) 0 ρ := by
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  have hjd : doorRowFloor M ≤ j := hb.2.2.2.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hAx : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) := hb.2.2.2.2.2.2.2.2.2.2.1
  have hω : (0 : ℝ) < (R.ω : ℝ) := by
    have : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
    linarith
  have hlrho : (0 : ℝ) ≤ Real.log (1 / ρ) := log_one_div_nonneg hρ0 hρ1
  have hllH : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) :=
    s13_loglog_le_of_range (R := R) hlo hhi
  have harmA := m4_arith_arm_of_gArmRho hω hHreg.1 hHreg.2 hg hAx
  have hmuA : (356600 : ℝ) ≤ Real.log (Real.log (A : ℝ)) := by
    have := hHreg.2; linarith
  have hlogA : (1 : ℝ) < Real.log (A : ℝ) :=
    one_lt_log_of_loglog_ge (log_natCast_nonneg' A) (by norm_num) hmuA
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have harm := m4_arith_arm_of_shift hApos (by linarith) hAX harmA
  have hlogH0 : (0 : ℝ) < Real.log ((H : ℕ) : ℝ) :=
    lt_of_lt_of_le (by norm_num) (one_lt_log_of_loglog_ge hHreg.1 (by norm_num) hHreg.2).le
  -- ⟦the `j`-floor, off the door's own row floor⟧
  have hj36 : (68719476736 : ℝ) ≤ (j : ℝ) := by
    have h1 : (2 : ℕ) ^ 36 ≤ j := le_trans (s15_doorRowFloor_ge hM) hjd
    have h2 : (68719476736 : ℕ) ≤ j := by
      have : (2 : ℕ) ^ 36 = 68719476736 := by norm_num
      omega
    exact_mod_cast h2
  -- ⟦the anchor, at `log₂M + 1 ≥ 1`⟧
  have hn1 : (1 : ℝ) ≤ ((Nat.log 2 M + 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ Nat.log 2 M + 1 := by omega
    exact_mod_cast this
  exact
    { Mpos := hM
      logX_nonneg := log_natCast_nonneg' (A + s)
      logH_nonneg := hHreg.1
      Hfloor := hHreg.2
      Knonneg := le_rfl
      rho_pos := hρ0
      rho_le_one := hρ1
      arm := harm
      anchor := by nlinarith [hanchor, hllH, hn1]
      C1_nonneg := hC1
      M0_window := s13BandM0_window (R := R) (ρ := ρ) (C₁ := C₁) hhi hlogH0
      jfloor := by linarith [hanchor, hllH, hj36, hlrho] }

/-- **⟦THE FAMILY FORM⟧** (`s15_doorArithFrameRho_family`) — the `harith` binder of the
capstone twin, at `Kf := 0` and the ⟦F2⟧ pin. -/
theorem s15_doorArithFrameRho_family {R : ChowlaRegime} {M : ℕ} {ρ : ℝ} {C₁ : ℕ → ℝ}
    (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hanchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33
      ≤ 39 * 10 ^ 8)
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ))
    (hC1 : ∀ n : ℕ, 0 ≤ C₁ n) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) 0 ρ := by
  intro H L q j A s hb
  exact s15_doorArithFrameRho_at_socket hM hρ0 hρ1 hanchor (hHreg H hb.1 hb.2.1)
    (hg H hb.1 hb.2.1) (hC1 (A + s)) hb

/-! ## §3 — THE ARM

The capstone's `∀ g ∃ R` slot is entered BEFORE `R` and before `M`, so the arm may read only
objects fixed by then: `δ₀`, `K` (hence `ρ`), and the window's own top `H₊` with the register
width `ω`.  `s15Arm` is the sum of the two arms the compose needs — `S13FramesA.s13GArm'` (the
`M`-free demoted arm: ⟦A-1⟧'s door gates and ⟦A-2⟧'s endpoint share) and `M4ArithRho`'s own
`gArmDoorRho` at `x₀ := 0`, `K := 0` (the `ρ`-frame's `arm` field). -/

/-- **⟦THE COMPOSE'S `g`-ARM⟧** (`s15Arm`) — read at `(H₊, ω)`; both summands are `M`-free. -/
def s15Arm (δ₀ ρ : ℝ) : ℕ → ℕ → ℕ := fun Hhi ω =>
  s13GArm' δ₀ Hhi ω + ⌈gArmDoorRho 0 0 (ω : ℝ) ρ Hhi⌉₊

/-- The demoted arm sits under `s15Arm`. -/
theorem s15Arm_demoted (δ₀ ρ : ℝ) (Hhi ω : ℕ) : s13GArm' δ₀ Hhi ω ≤ s15Arm δ₀ ρ Hhi ω := by
  rw [s15Arm]; omega

/-- The `ρ`-frame's arm sits under `s15Arm`, in the reals. -/
theorem s15Arm_rho {δ₀ ρ : ℝ} {Hhi ω x : ℕ} (h : s15Arm δ₀ ρ Hhi ω ≤ x) :
    gArmDoorRho 0 0 (ω : ℝ) ρ Hhi ≤ (x : ℝ) := by
  have hc : ⌈gArmDoorRho 0 0 (ω : ℝ) ρ Hhi⌉₊ ≤ x := by rw [s15Arm] at h; omega
  have hcR : ((⌈gArmDoorRho 0 0 (ω : ℝ) ρ Hhi⌉₊ : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hc
  exact le_trans (Nat.le_ceil _) hcR

/-- **⟦THE `ρ`-ARM IS MONOTONE IN THE WIDTH⟧** (`s15_gArmDoorRho_mono`) — so a floor met at
the window's TOP `H₊` is met at every admissible `H`.  Both `arcDen 12 H = (log H)^{12}` and
`exp(exp(7000·loglog H + …))` increase with `H`. -/
theorem s15_gArmDoorRho_mono {ω ρ : ℝ} {H H' : ℕ} (hω : 0 ≤ ω)
    (hH : 0 < Real.log ((H : ℕ) : ℝ)) (hHH : H ≤ H') :
    gArmDoorRho 0 0 ω ρ H ≤ gArmDoorRho 0 0 ω ρ H' := by
  have hH0 : (0 : ℝ) < ((H : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos H with hz | hz
    · rw [hz] at hH; norm_num at hH
    · exact_mod_cast hz
  have hcast : ((H : ℕ) : ℝ) ≤ ((H' : ℕ) : ℝ) := by exact_mod_cast hHH
  have hlog : Real.log ((H : ℕ) : ℝ) ≤ Real.log ((H' : ℕ) : ℝ) := Real.log_le_log hH0 hcast
  have hll : Real.log (Real.log ((H : ℕ) : ℝ)) ≤ Real.log (Real.log ((H' : ℕ) : ℝ)) :=
    Real.log_le_log hH hlog
  have harc : arcDen 12 H ≤ arcDen 12 H' := by
    rw [arcDen, arcDen]
    exact Real.rpow_le_rpow hH.le hlog (by norm_num)
  have hE : Real.exp (Real.exp (7000 * Real.log (Real.log ((H : ℕ) : ℝ))
        + 500 * Real.log (1 / ρ) + 6600 + 36 * 0))
      ≤ Real.exp (Real.exp (7000 * Real.log (Real.log ((H' : ℕ) : ℝ))
        + 500 * Real.log (1 / ρ) + 6600 + 36 * 0)) :=
    Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith))
  have harc0 : (0 : ℝ) ≤ arcDen 12 H := by
    rw [arcDen]; positivity
  rw [gArmDoorRho, gArmDoorRho]
  refine max_le_max le_rfl ?_
  have h1 : 16 * ω * arcDen 12 H ≤ 16 * ω * arcDen 12 H' := by nlinarith [harc, hω]
  have h2 : (0 : ℝ) ≤ 16 * ω * arcDen 12 H := by positivity
  nlinarith [h1, h2, hE, Real.exp_pos (Real.exp (7000 * Real.log (Real.log ((H : ℕ) : ℝ))
    + 500 * Real.log (1 / ρ) + 6600 + 36 * 0))]

/-! ## §3b — ⟦F3⟧ THE BLOCK FLOOR AT THE SOCKET, AND THE OPAQUE THRESHOLD

`S13BandGate`'s `block` (`s13BlockFloor M ≤ X_d`) and `x0_le` (`x₀ ≤ 2^{doorRowFloor M}`) are
carried as gate lines in `S13BandBase` because the socket's own `j`-floor is LINEAR in
`M·Adoor M` while the block floor is QUADRATIC.  Both are nevertheless payable from data the
compose has: the regime's `hPHheadroom` (through `s13_socketBase_xscale`) pays `block` once
the `M`-upper is stated with `12·loglog H/log 2` of room, and `x₀ ≤ M` — a plain `ℕ`
inequality on a constant revealed BEFORE `M` — pays `x0_le`. -/

/-- **⟦F3, PAID⟧** (`s15_block_at_socket`) — `s13BlockFloor M ≤ A + s` at every socket base,
from `SocketBase`'s x-scale field and the `M`-upper `E + 1 + 18Λ ≤ 4⌊ε²H₊⌋₊`.

⟦THE ARITHMETIC⟧ the x-scale gives `2^{4m} ≤ 2·(log H)^{12}·A`, i.e.
`log A ≥ 4m·log 2 − log 2 − 12·loglog H`; the block floor asks `E·log 2 ≤ log A`, and
`12·loglog H ≤ 12Λ ≤ 18Λ·log 2` closes it.  The `18` is `12/log 2 = 17.31` rounded up. -/
theorem s15_block_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBase R M H L q j A s)
    (hHreg : 0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hblk : ((s13BlockExp M : ℕ) : ℝ) + 1
        + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)) :
    s13BlockFloor M ≤ A + s := by
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) :=
    lt_of_lt_of_le (by norm_num) (one_lt_log_of_loglog_ge hHreg.1 (by norm_num) hHreg.2).le
  have hllH : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) :=
    s13_loglog_le_of_range (R := R) hlo hhi
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by linarith [hHreg.2]
  set m : ℕ := ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ with hm
  have hxs : ((4 ^ m : ℕ) : ℝ) ^ 2 ≤ 2 * arcDen 12 H * (A : ℝ) := s13_socketBase_xscale hb
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlhs0 : (0 : ℝ) < ((4 ^ m : ℕ) : ℝ) ^ 2 := by positivity
  have hlog := Real.log_le_log hlhs0 hxs
  have hLid : Real.log (((4 ^ m : ℕ) : ℝ) ^ 2) = 4 * (m : ℝ) * Real.log 2 := by
    have h4 : ((4 ^ m : ℕ) : ℝ) = (4 : ℝ) ^ m := by push_cast; ring
    rw [h4, ← pow_mul, Real.log_pow, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hRR : Real.log (2 * arcDen 12 H * (A : ℝ))
      = Real.log 2 + 12 * Real.log (Real.log (H : ℝ)) + Real.log (A : ℝ) := by
    rw [harcpow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  rw [hLid, hRR] at hlog
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hE : ((s13BlockExp M : ℕ) : ℝ) * Real.log 2 ≤ Real.log (A : ℝ) := by
    nlinarith [hblk, hlog, hllH, hll0, hl2lo, hl2hi]
  have hpow : ((2 : ℝ)) ^ (s13BlockExp M) ≤ (A : ℝ) := by
    have hlt : Real.log (((2 : ℝ)) ^ (s13BlockExp M)) ≤ Real.log (A : ℝ) := by
      rw [Real.log_pow]; linarith
    exact (Real.log_le_log_iff (by positivity) hApos).mp hlt
  have hcast : ((2 ^ s13BlockExp M : ℕ) : ℝ) ≤ (A : ℝ) := by push_cast; exact hpow
  have hnat : (2 : ℕ) ^ s13BlockExp M ≤ A := by exact_mod_cast hcast
  rw [s13BlockFloor]; omega

/-- **⟦THE OPAQUE THRESHOLD, PAID BY AN `M`-FLOOR⟧** (`s15_x0_le`) — `S13BandGate.x0_le` from
the plain `ℕ` line `x₀ ≤ M`.  `x₀` sits in the twin's TOP constant block, so it is revealed
before `M` is chosen and this is an ordinary `M`-floor. -/
theorem s15_x0_le {x₀ M : ℕ} (h : x₀ ≤ M) : x₀ ≤ 2 ^ doorRowFloor M := by
  have h1 : M ≤ 2 ^ M := Nat.le_of_lt (Nat.lt_two_pow_self)
  have h2 : M ≤ doorRowFloor M := by
    rw [doorRowFloor]
    have := one_le_Adoor M
    calc M = M * 1 := (Nat.mul_one M).symm
      _ ≤ M * Adoor M := Nat.mul_le_mul_left _ this
  have h3 : (2 : ℕ) ^ M ≤ 2 ^ doorRowFloor M := Nat.pow_le_pow_right (by norm_num) h2
  omega

/-! ## §4 — `S15Sel`, THE `M`-SELECTION REGISTER

Eleven lines.  `hM` is `1 ≤ M`; three are `M`-LOWERS (`bfloor`, `gRows`, `x0M`), two are
`M`-UPPERS (`blk`, `half`), one is a charge on the clearing parameter (`rho`), and four are
budgets the const road's own slots cost (`anchor`, `gP1`, `err`, `lvl`).  Every field is ONE
inequality in the scales `λ₋ = loglog H₋`, `Λ = loglog H₊`, `Adoor M`, `doorRowFloor M`,
`log(1/ρ)`; nothing opaque is hidden inside any of them.

⚠ `S15Sel` IS CARRIED, NOT PROVED.  `half` and `gRows`/`lvl` pull in opposite directions and
are jointly satisfiable only inside CONST-VERDICT's `M`-window `Λ ≲ 4·10⁸·λ₋`; the twin's
payload bounds `Λ` only by the `9/2` tower.  Naming the window is the point of the bundle. -/

/-- **⟦THE `M`-SELECTION REGISTER⟧** (`S15Sel Cg δ₀ Ct ρ x₀ R M`). -/
structure S15Sel (Cg δ₀ Ct ρ : ℝ) (x₀ : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop where
  /-- the door's parameter is a modulus. -/
  hM : 1 ≤ M
  /-- ⟦`M`-LOWER 1⟧ `MSelect'.bfloor` = `M4DoorGates.hMδ`. -/
  bfloor : 24 * Cg / δ₀ ≤ (M : ℝ)
  /-- ⟦`M`-LOWER 2⟧ `MSelect'.gRows` — pays ⟦gate 8⟧ (`hdgate`) and ⟦G2⟧ (`hj0`). -/
  gRows : 242 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ ((Adoor M : ℕ) : ℝ)
  /-- ⟦`M`-LOWER 3⟧ the opaque threshold, as a plain `ℕ` floor (`S13BandGate.x0_le`). -/
  x0M : x₀ ≤ M
  /-- ⟦`M`-UPPER 1⟧ `MSelect'.blockCeil` AND ⟦F3⟧'s `block`, off `hPHheadroom` (`§3b`). -/
  blk : ((s13BlockExp M : ℕ) : ℝ) + 1 + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)
  /-- ⟦`M`-UPPER 2⟧ THE WINDOW GATE at the half-window floor (`s13_winFit_of_halfWindow`). -/
  half : (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
    ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 2
  /-- the clearing charge — `ρ ≥ e^{−10^{14}}`. -/
  rho : -Real.log ρ ≤ 100000000000000
  /-- the `ρ`-frame's ⟦C1⟧ anchor, at its OWN statement (no `2^{2483}` floor). -/
  anchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33 ≤ 39 * 10 ^ 8
  /-- the `𝒯`-leg budget at `constPool` (`s15_gP1_of_budget`). -/
  gP1 : 29 + Real.log Ct + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ ((Adoor M : ℕ) : ℝ) * Real.log 2 + Real.log ρ
  /-- the `T₀`-band residue line after the `e`-cancellation (`S13BandGate.err_res`). -/
  err : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 17 ≤ 347900
  /-- the `level1` budget — the BINDING const-pool line (`Adoor M ≳ 242.4·Λ`). -/
  lvl : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      + (1 / 3) * Real.log (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ))
      + (-Real.log ρ)
    ≤ (1 / 12) * ((Adoor M : ℕ) : ℝ) * Real.log 2

/-- `MSelect'.blockCeil`'s `ℕ`-form, read off the register's real-valued `M`-upper. -/
theorem S15Sel.head {Cg δ₀ Ct ρ : ℝ} {x₀ : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hsel : S15Sel Cg δ₀ Ct ρ x₀ R M) (hΛ : 0 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) :
    s13BlockExp M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1 := by
  have h := hsel.blk
  have hR : ((s13BlockExp M : ℕ) : ℝ) ≤ ((4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
    push_cast; linarith
  have : s13BlockExp M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ := by exact_mod_cast hR
  omega

/-- **⟦THE BAND REGISTER, FOUR OF FIVE⟧** (`s15_bandGate_of_grade`) — `S13BandGate` at
`C₁ ≡ 1` with only its `grade` line carried: `x0_le` is §3b's `M`-floor, `C1_one` is free at
the pin, `err_res` is `S15Sel.err` (`2·log 2 ≤ 2`), `block` is §3b's ⟦F3⟧ discharge. -/
theorem s15_bandGate_of_grade {Cg δ₀ Ct ρ : ℝ} {x₀ : ℕ} {R : ChowlaRegime} {M : ℕ} {C' : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hsel : S15Sel Cg δ₀ Ct ρ x₀ R M)
    (hgrade : 8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
      ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))) :
    S13BandGate R M x₀ C' ρ (fun _ => 1) where
  x0_le := s15_x0_le hsel.x0M
  C1_one := fun _ => le_rfl
  grade := hgrade
  err_res := fun n => by
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have h3 := hsel.err
    change 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + 2 * Real.log ((1 : ℝ) + 1)
      + Real.log (1 / ρ) + 15 ≤ 347900
    rw [show ((1 : ℝ) + 1) = 2 by norm_num]
    linarith
  block := by
    intro H L q j A s hb
    exact s15_block_at_socket hb (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk

/-- **⟦THE SURVIVOR, NAMED⟧** (`S15CrossingBound R M`) — the ⟦B4⟧ RAW CROSSING BOUND of
`S12ConstCompose.logChowla2_capstone_final_const'` (`S12ConstCompose.lean:492-509`), written
at the compose's own instantiation (`t₁ ≡ 0`, `cU := liouvilleC`,
`epsrf ≡ θ₂₉₃ − 1/500`), byte for byte.

⟦WHY IT SURVIVES⟧ its only landed route is the per-block cap bundle, whose `budget` field
carries the `thinBundle` tail `S^{2·loglog S/log 𝒫₂}` and so forces
`log H₊ ≤ 1280·log 2·doorRowFloor M`.  Against `MSelect'.winFit` that is a window-WIDTH law
`λ₊ ≤ λ₋ + 7.1448`, and WIDTH-SCOPE's `probe_regime_width_forced` shows every `ChowlaRegime`
(at `C0 = 2`, `a = 1`, `λ₋ ≥ 50`) has `λ₊ ≥ λ₋³` — the entropy budget's own `log 2` crossing
FORCES the tower.  The collision is `4999×` at the landed `K = 3`.  So no regime the spine can
build supplies this bound through `budget`, and it is carried here as a hypothesis. -/
def S15CrossingBound (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
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
              * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + (theta293 - 1 / 500)))

/-! ## §5 — ⟦THE COMPOSE⟧ -/

set_option maxHeartbeats 1000000 in
-- Same cause as `S12ConstCompose` §4: the twin's sixteen-binder residue re-elaborates against
-- the instantiated prefix.
/-- **⟦THE CAPSTONE, FIRED — MODULO ONE NAMED CROSSING BOUND⟧** (`logChowla2_conditional`).

`S12ConstCompose.logChowla2_capstone_final_const'` at
`Aexp := s13Aexp`, `Cp := 0`, `C₁ ≡ 1`, `M₀ := s13BandM0 R ρ C₁`,
`epsrf ≡ θ₂₉₃ − 1/500`, `Kf := 0`, `k := doorCount R.ω`,
`g := s15Arm δ₀ ρ`, `ρ := doorRhoOfDelta (s12DeltaSock δ₀ K)`,
with FIFTEEN of its sixteen residue binders DISCHARGED (the table in this file's header) and
the sixteenth — `S15CrossingBound` — carried, named, with its wall map.

⟦THE `g`-SLOT⟧ the caller's register arm `g` rides beside `s15Arm` in one sum, so the payload
keeps the road's own `g R.Hhi R.ω ≤ R.x` conjunct — which is what §6 needs.

⟦THE BASE PIN⟧ at `U1floor ≥ max Hcap (max arcFloor36 loglogFloor50)` the EDGE-5 conjunct
`R.Hlo ≤ max Hcap U1floor` pins `R.Hlo = U1floor` exactly, so every `λ₋`-reading line of
`S15Sel` is a statement about a scale the CALLER chose, not about an opaque one.

⟦WHAT IS CARRIED⟧ `S15Sel` (§4) and `S13BandGate` (`S13BandBase.lean:481`) — nine plus five
explicit inequalities — and `S15CrossingBound`.  Nothing else. -/
theorem logChowla2_conditional :
    ∃ (ε : ℚ) (Cg K δ₀ Ct : ℝ) (x₀ Hcap : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < K ∧ 0 < δ₀ ∧ 0 < Ct ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
        ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          ∀ M : ℕ, S15Sel Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ R M →
            ∃ C' : ℝ, 0 < C' ∧
              (8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
                  ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) →
                S15CrossingBound R M →
                  ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨Cg, ε, K, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀, Hcap, hCg, hε, hK, hδ₀, hCt, hCq, hcs,
    hT₀, hKq, hKs, hmain⟩ := logChowla2_capstone_final_const' s13Aexp s13Aexp_pos
  refine ⟨ε, Cg, K, δ₀, Ct, x₀, Hcap, hε, hCg, hK, hδ₀, hCt, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ K with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hK
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  -- ⟦THE BASE PIN⟧ `R.Hlo = U1floor`
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hsel
  obtain ⟨C', hC'pos, hgo⟩ := hfire M hsel.hM
  refine ⟨C', hC'pos, ?_⟩
  intro hgrade hcap
  -- ⟦the two scale floors⟧
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) ^ ((9 : ℝ) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  -- ⟦the arm, both halves⟧
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family
  have harith := s15_doorArithFrameRho_family (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect' Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_of_halfWindow hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register, four of five⟧
  have hgate : S13BandGate R M x₀ C' ρ (fun _ => 1) :=
    s15_bandGate_of_grade hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect' hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor le_rfl (s13_g2_jfloor_of_MSelect' hsel.hM (by linarith) hS))
    (s13_gate8 le_rfl (s13_gate8_of_MSelect' (by linarith) hS))
    (s13_smallGradeFits_of_MSelect' hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket hfl hb hsel.hM hρ0 hρ1 htow hsel.rho hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket hfl hb hlam50 htow hsel.rho le_rfl)
    (fun H L q j A s hb => s15_heps293_at_socket hfl hb hρ0 hlam50 htow hsel.rho)
    (fun H L q j A s hb => s15_hband4096_at_socket hfl hb hρ0 hlam50 htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five hsel.hM (hgate.block H L q j A s hb) hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family hsel.hM harith hgate)
    harith

/-! ## §6 — THE WITNESSED-SCALE STATEMENT, CONDITIONAL

`S14Compose.LogChowla2WitnessedScale` is `∃ε > 0, ∀ U1floor g, ∃ R` above the floor, past the
arm, at which `logChowla2Fails` FAILS.  §5's conclusion IS that payload, so the last mile is
one `∃`-repackaging — through `S14Compose.logChowla2_witnessed_scale_of_fired`, the bridge the
campaign recorded for exactly this moment. -/

/-- **⟦THE REGISTER SUPPLY, AS ONE NAMED PROP⟧** (`S15Supply`) — what a regime must carry for
§5 to fire there: an `M` inside the selection window, the crossing bound at that `M`, and the
band register at EVERY positive `C'`.

⚠ the `∀ C'` is not slack — it is the ⟦B5 `grade`⟧ wall stated precisely.  The twin reveals
`C'` AFTER `M` (`m4_fuse_hband_of_bandBase`'s prefix), so a supplier that fixes `M` first must
cover whatever `C'` the band wire then produces.  `S11HoistGrade.s11_grade_absorption` closes
exactly this at the GRADED wire (`m4_fuse_hband_of_bandBase_graded`, `C' ≤ Cb·M^{2.1}`, `Cb`
in the top block) — which the landed const twin does not consume.  A const twin re-cut at the
graded wire would remove this `∀ C'` and nothing else. -/
def S15Supply (Cg δ₀ Ct ρ : ℝ) (x₀ : ℕ) (R : ChowlaRegime) : Prop :=
  ∃ M : ℕ, S15Sel Cg δ₀ Ct ρ x₀ R M ∧ S15CrossingBound R M ∧
    ∀ C' : ℝ, 0 < C' → 8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
      ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))

/-- **⟦THE WITNESSED-SCALE STATEMENT, ON THE REGISTER⟧**
(`logChowla2_witnessed_scale_conditional`) — `LogChowla2WitnessedScale` follows from the
register supply alone, at the road's own constants. -/
theorem logChowla2_witnessed_scale_conditional :
    ∃ (Cg K δ₀ Ct : ℝ) (x₀ : ℕ), 1 ≤ Cg ∧ 0 < K ∧ 0 < δ₀ ∧ 0 < Ct ∧
      ((∀ R : ChowlaRegime, S15Supply Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ R) →
        LogChowla2WitnessedScale) := by
  obtain ⟨ε, Cg, K, δ₀, Ct, x₀, Hcap, hε, hCg, hK, hδ₀, hCt, hbody⟩ := logChowla2_conditional
  refine ⟨Cg, K, δ₀, Ct, x₀, hCg, hK, hδ₀, hCt, ?_⟩
  intro hsup
  refine logChowla2_witnessed_scale_of_fired ⟨ε, hε, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hHlo, hRg, -, hM⟩ :=
    hbody (max U1floor (max Hcap (max arcFloor36 loglogFloor50))) g (le_max_right _ _)
  obtain ⟨M, hsel, hcap, hgate⟩ := hsup R
  obtain ⟨C', hC'pos, hfin⟩ := hM M hsel
  exact ⟨R, hReps, by omega, hRg, hfin (hgate C' hC'pos) hcap⟩

/-! ## §7 — THE INHABITATION CERTIFICATE (THE VACUITY FENCE)

`S14Compose` §4's sharpest line, at the compose's own `(R, M)`: the socket family is NONEMPTY
there, so none of the sixteen residue binders — the survivor included — is vacuously true.
The tuple is `H = L = H₊`, `q = 1`, `j = doorRowFloor M`, `A = 2·x`, `s = 0`, and the ONE side
condition `2^{doorRowFloor M} ≤ H₊` is FORCED by `S15Sel.half` (the window gate), through
`s14_window_floor_of_winFit`. -/

/-- **⟦THE SOCKET FAMILY IS INHABITED AT THE COMPOSED TUPLE⟧** (`s15_socketBase_inhabited`). -/
theorem s15_socketBase_inhabited {Cg δ₀ Ct ρ : ℝ} {x₀ : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsel : S15Sel Cg δ₀ Ct ρ x₀ R M) :
    SocketBase R M R.Hhi R.Hhi 1 (doorRowFloor M) (2 * R.x) 0 := by
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have hS : MSelect' Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_of_halfWindow hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  have hwin : 2 ^ doorRowFloor M ≤ R.Hlo :=
    s14_window_floor_of_winFit hρ0 hρ1 (hS.winFit R.Hlo le_rfl R.hHlohi)
  exact s14_socketBase_witness (le_trans hwin R.hHlohi)

/-- **⟦THE FENCE, AT THE FIRED COMPOSE⟧** (`s15_compose_nonvacuous`) — the same, delivered
beside §5's own data: at every `U1floor` the compose admits and every `M` its register
accepts, the socket family at `(R, M)` is inhabited. -/
theorem s15_compose_nonvacuous :
    ∃ (ε : ℚ) (Cg K δ₀ Ct : ℝ) (x₀ Hcap : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < K ∧ 0 < δ₀ ∧ 0 < Ct ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
        ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ M : ℕ, S15Sel Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ R M →
            SocketBase R M R.Hhi R.Hhi 1 (doorRowFloor M) (2 * R.x) 0 := by
  obtain ⟨ε, Cg, K, δ₀, Ct, x₀, Hcap, hε, hCg, hK, hδ₀, hCt, hbody⟩ := logChowla2_conditional
  refine ⟨ε, Cg, K, δ₀, Ct, x₀, Hcap, hε, hCg, hK, hδ₀, hCt, ?_⟩
  intro U1floor g hU
  obtain ⟨R, hReps, hHlo, hRg, -, -⟩ := hbody U1floor g hU
  refine ⟨R, hReps, hHlo, hRg, ?_⟩
  intro M hsel
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  exact s15_socketBase_inhabited hfl (doorRhoOfDelta_pos (s12DeltaSock_pos hδ₀ hK).ne')
    (doorRhoOfDelta_le_one _) hsel


/-! ## §8 — ⟦GRADE-RECUT⟧ THE SAME COMPOSE AT THE GRADED TWIN

`S12ConstCompose` §5 re-cuts the const capstone twin onto the GRADED band wire
(`S12FuseCompose.m4_fuse_hband_of_bandBase_graded`, `C' ≤ Cb·M^{2.1}` with `Cb` in the top
constant block), so `S11HoistGrade.s11_grade_absorption` pays `S13BandGate.grade` INSIDE the
twin at an explicit `M`-floor `Mfl`.  This section fires that twin at §5's working point.

⟦THE DELTA AGAINST §5⟧ the naked `grade` hypothesis
`8·C' ≤ (log 2·doorRowFloor M)^{2.501}` is GONE from the compose's hypothesis list, and with
it the whole `∃ C' > 0` payload wrapper — `C'` is now internal to the twin.  In its place the
`M`-quantifier carries `Mfl ≤ M`, an ordinary `ℕ`-floor against a constant of the top block,
of the same genre as `S15Sel.x0M` (`x₀ ≤ M`) — when `S15Sel` is next re-cut this is one more
`M`-LOWER line, `mfloor : Mfl ≤ M`, and the survivor list is then `S15CrossingBound` +
`S15Sel` alone.  `s15_bandGate_of_grade` is unchanged: it consumes the DELIVERED grade exactly
as it consumed the assumed one, so the band bundle (`hbandbase`, ledger row 15) is discharged
with `grade` PAID.  Nothing else moves — ⟦B4⟧'s crossing bound is still the analytic survivor.
-/

set_option maxHeartbeats 1000000 in
-- Same cause as §5: the twin's residue re-elaborates against the instantiated prefix.
/-- **⟦THE CAPSTONE, FIRED AT THE GRADED TWIN⟧** (`logChowla2_conditional_graded`).

§5's `logChowla2_conditional` at `S12ConstCompose.logChowla2_capstone_final_const'_graded`.
Same instantiation (§A), same fifteen discharges (§B), same base pin.  Two changes and no
others:

* the `grade` hypothesis `8·C' ≤ (log 2·doorRowFloor M)^{s13Aexp − 1/2 + 1/1000}` is GONE —
  the twin delivers it — and so is the `∃ C' : ℝ, 0 < C' ∧ …` wrapper it was stated in;
* the top block gains `Mfl : ℕ` (`1 ≤ Mfl`) and the `M`-quantifier gains `Mfl ≤ M`.

⟦WHAT IS CARRIED⟧ `S15Sel` (§4), `S15CrossingBound` (§4), and the `M`-floor `Mfl ≤ M`.
Nothing else. -/
theorem logChowla2_conditional_graded :
    ∃ (ε : ℚ) (Cg K δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < K ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
        ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          ∀ M : ℕ, Mfl ≤ M →
            S15Sel Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ R M →
              S15CrossingBound R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀, Hcap, Mfl, hCg, hε, hK, hδ₀, hCt, hCq,
    hcs, hT₀, hKq, hKs, hMfl, hmain⟩ :=
    logChowla2_capstone_final_const'_graded s13Aexp s13Aexp_pos
  refine ⟨ε, Cg, K, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hK, hδ₀, hCt, hMfl, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ K with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hK
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  -- ⟦THE BASE PIN⟧ `R.Hlo = U1floor`
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hMfloor hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hMfloor
  intro hcap
  -- ⟦the two scale floors⟧
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) ^ ((9 : ℝ) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  -- ⟦the arm, both halves⟧
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family
  have harith := s15_doorArithFrameRho_family (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect' Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_of_halfWindow hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register, four of five⟧
  have hgate : S13BandGate R M x₀ C' ρ (fun _ => 1) :=
    s15_bandGate_of_grade hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect' hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor le_rfl (s13_g2_jfloor_of_MSelect' hsel.hM (by linarith) hS))
    (s13_gate8 le_rfl (s13_gate8_of_MSelect' (by linarith) hS))
    (s13_smallGradeFits_of_MSelect' hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket hfl hb hsel.hM hρ0 hρ1 htow hsel.rho hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket hfl hb hlam50 htow hsel.rho le_rfl)
    (fun H L q j A s hb => s15_heps293_at_socket hfl hb hρ0 hlam50 htow hsel.rho)
    (fun H L q j A s hb => s15_hband4096_at_socket hfl hb hρ0 hlam50 htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five hsel.hM (hgate.block H L q j A s hb) hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family hsel.hM harith hgate)
    harith

/-- **⟦THE REGISTER SUPPLY, GRADED⟧** (`S15SupplyGraded`) — §6's `S15Supply` with the `∀ C'`
clause DELETED and the `M`-floor in its place.  That `∀ C'` was the ⟦B5 `grade`⟧ wall stated
precisely (a supplier fixing `M` first had to cover whatever `C'` the band wire then produced);
the graded twin pays it internally, so what remains is the selection register, the crossing
bound, and one `ℕ`-floor. -/
def S15SupplyGraded (Cg δ₀ Ct ρ : ℝ) (x₀ Mfl : ℕ) (R : ChowlaRegime) : Prop :=
  ∃ M : ℕ, Mfl ≤ M ∧ S15Sel Cg δ₀ Ct ρ x₀ R M ∧ S15CrossingBound R M

/-- **⟦THE WITNESSED-SCALE STATEMENT, ON THE GRADED REGISTER⟧**
(`logChowla2_witnessed_scale_conditional_graded`) — §6's corollary at §8's compose. -/
theorem logChowla2_witnessed_scale_conditional_graded :
    ∃ (Cg K δ₀ Ct : ℝ) (x₀ Mfl : ℕ), 1 ≤ Cg ∧ 0 < K ∧ 0 < δ₀ ∧ 0 < Ct ∧
      ((∀ R : ChowlaRegime,
          S15SupplyGraded Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R) →
        LogChowla2WitnessedScale) := by
  obtain ⟨ε, Cg, K, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hK, hδ₀, hCt, hMfl, hbody⟩ :=
    logChowla2_conditional_graded
  refine ⟨Cg, K, δ₀, Ct, x₀, Mfl, hCg, hK, hδ₀, hCt, ?_⟩
  intro hsup
  refine logChowla2_witnessed_scale_of_fired ⟨ε, hε, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hHlo, hRg, -, hM⟩ :=
    hbody (max U1floor (max Hcap (max arcFloor36 loglogFloor50))) g (le_max_right _ _)
  obtain ⟨M, hMfloor, hsel, hcap⟩ := hsup R
  exact ⟨R, hReps, by omega, hRg, hM M hMfloor hsel hcap⟩

/-! ## §9 — ⟦ERR-REPAIR⟧ THE SHARP REGISTER, AND THE NON-VACUOUS CONDITIONAL

PURELY ADDITIVE: §4–§8 are untouched.

⟦WHAT WENT WRONG⟧ `S15Sel.err` (§4) is the numeral line `14·λ₊ + log(1/ρ) + 17 ≤ 347900`,
inherited from `S13BandGate.err_res`.  Read as a cap on the window top it is `λ₊ ≤ 24849`.
`ERR-REF`'s kernel probe (flags, 2026-07-30 23:38) put that against WIDTH-SCOPE's forced
tower `λ₊ ≥ λ₋³ ≥ 125000` (at `C0 = 2`, `a = 1`, `λ₋ ≥ 50`, which the compose's own base pin
supplies) and derived `False`: `S15Sel` IS EMPTY at every regime the spine can build, so
§5's and §8's conditionals — true, kernel-checked, unimpeachable — were VACUOUSLY true.  The
socket inhabitation certificate of §7 fenced SOCKET vacuity; this was REGISTER vacuity, one
level up.

⟦THE REPAIR⟧ no numeral can work — `λ₊` has no upper bound on the register — so the line is
DELETED, not re-numeraled.  `S13BandBase` §6 pays `DoorBandBase.err` from the `g`-arm read AT
THE WINDOW TOP (`s13_band_err_free`), which the compose already carries at `hgarm R.Hhi`, and
which imposes NO `λ₊` cap at all: the residue closes on the constant term `6439.62` against
`17`.  This section re-cuts the register accordingly and re-fires §8's compose on it.

⟦THE DELTA AGAINST §8⟧ exactly two statement changes in the register and one in the compose:

* `S15Sel.err` is GONE (`S15Sel'` has ten lines where `S15Sel` had eleven);
* `Mfl ≤ M` — §8's `M`-quantifier hypothesis, of the same genre as `x0M` — is FOLDED IN as
  the field `S15Sel'.mfloor`, so the compose's `M`-quantifier carries the register and
  nothing else;
* `doorBandBase_family'` + `S13BandGate'` replace `doorBandBase_family` + `S13BandGate`; the
  supplier's CONCLUSION is byte-identical, so the fire's argument list is unchanged.

⟦THE SURVIVOR LIST⟧ `S15CrossingBound` + `S15Sel'`.  Two objects.

⟦IS `S15Sel'` NONEMPTY?⟧  Not proved here, and not claimed.  What IS kernel-checked:
`s15_sel'_anchor_cap` — the next-tightest `λ₊`-cap left in the register (`anchor`,
`14λ₊ + log(1/ρ) + 33 ≤ 3.9·10⁹`, i.e. `λ₊ ≤ 2.7857·10⁸`) is against the same width law only
`λ₋ ≤ 654`, SATISFIED at the working point `λ₋ ≈ 50`, where `err`'s cap was `λ₋ ≤ 29.2` and
failed.  So the contradiction ERR-REF exhibited is gone and the register is not empty for the
reason it was empty before.  A full witness — an explicit `(R, M)` satisfying all ten lines
at once — additionally needs `blk`, `half`, `gRows`, `gP1`, `lvl` jointly satisfied against
the OPAQUE `Cg`, `δ₀`, `Ct`, `x₀`, `Mfl` that `logChowla2_capstone_final_const'_graded`
produces existentially, and no landed statement bounds those.  It is NOT attempted here; it
is the follow-up the `∃M` discharge was always going to be. -/

/-- **⟦THE `M`-SELECTION REGISTER, SHARP⟧** (`S15Sel' Cg δ₀ Ct ρ x₀ Mfl R M`) — §4's
`S15Sel` with `err` DELETED (the arm at the window top pays it, `S13BandBase` §6) and §8's
`M`-floor `Mfl ≤ M` FOLDED IN as `mfloor`.  Every other line is verbatim §4. -/
structure S15Sel' (Cg δ₀ Ct ρ : ℝ) (x₀ Mfl : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop where
  /-- the door's parameter is a modulus. -/
  hM : 1 ≤ M
  /-- ⟦`M`-LOWER 0⟧ the graded twin's own `ℕ`-floor (§8's quantifier hypothesis, folded in). -/
  mfloor : Mfl ≤ M
  /-- ⟦`M`-LOWER 1⟧ `MSelect'.bfloor` = `M4DoorGates.hMδ`. -/
  bfloor : 24 * Cg / δ₀ ≤ (M : ℝ)
  /-- ⟦`M`-LOWER 2⟧ `MSelect'.gRows` — pays ⟦gate 8⟧ (`hdgate`) and ⟦G2⟧ (`hj0`). -/
  gRows : 242 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ ((Adoor M : ℕ) : ℝ)
  /-- ⟦`M`-LOWER 3⟧ the opaque threshold, as a plain `ℕ` floor (`S13BandGate'.x0_le`). -/
  x0M : x₀ ≤ M
  /-- ⟦`M`-UPPER 1⟧ `MSelect'.blockCeil` AND ⟦F3⟧'s `block`, off `hPHheadroom` (`§3b`). -/
  blk : ((s13BlockExp M : ℕ) : ℝ) + 1 + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)
  /-- ⟦`M`-UPPER 2⟧ THE WINDOW GATE at the half-window floor (`s13_winFit_of_halfWindow`). -/
  half : (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
    ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 2
  /-- the clearing charge — `ρ ≥ e^{−10^{14}}`. -/
  rho : -Real.log ρ ≤ 100000000000000
  /-- the `ρ`-frame's ⟦C1⟧ anchor, at its OWN statement (no `2^{2483}` floor). -/
  anchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33 ≤ 39 * 10 ^ 8
  /-- the `𝒯`-leg budget at `constPool` (`s15_gP1_of_budget`). -/
  gP1 : 29 + Real.log Ct + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ ((Adoor M : ℕ) : ℝ) * Real.log 2 + Real.log ρ
  /-- the `level1` budget — the BINDING const-pool line (`Adoor M ≳ 242.4·Λ`). -/
  lvl : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      + (1 / 3) * Real.log (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ))
      + (-Real.log ρ)
    ≤ (1 / 12) * ((Adoor M : ℕ) : ℝ) * Real.log 2

/-- `MSelect'.blockCeil`'s `ℕ`-form, read off the sharp register's real-valued `M`-upper
(§4's `S15Sel.head`, verbatim). -/
theorem S15Sel'.head {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hsel : S15Sel' Cg δ₀ Ct ρ x₀ Mfl R M)
    (hΛ : 0 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) :
    s13BlockExp M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1 := by
  have h := hsel.blk
  have hR : ((s13BlockExp M : ℕ) : ℝ) ≤ ((4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
    push_cast; linarith
  have : s13BlockExp M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ := by exact_mod_cast hR
  omega

/-- **⟦THE SHARP BAND REGISTER, THREE OF FOUR⟧** (`s15_bandGate'_of_grade`) —
`S13BandGate'` at `C₁ ≡ 1` with only its `grade` line carried (delivered by the graded twin
at the fire).  `x0_le` is §3b's `M`-floor, `C1_one` is free at the pin, `block` is §3b's
⟦F3⟧ discharge — and there is no fourth line to pay: `err_res` is gone. -/
theorem s15_bandGate'_of_grade {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    {C' : ℝ} (hfl : loglogFloor50 ≤ R.Hlo) (hsel : S15Sel' Cg δ₀ Ct ρ x₀ Mfl R M)
    (hgrade : 8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
      ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))) :
    S13BandGate' R M x₀ C' (fun _ => 1) where
  x0_le := s15_x0_le hsel.x0M
  C1_one := fun _ => le_rfl
  grade := hgrade
  block := by
    intro H L q j A s hb
    exact s15_block_at_socket hb (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk

set_option maxHeartbeats 1000000 in
-- Same cause as §5 and §8: the twin's residue re-elaborates against the instantiated prefix.
/-- **⟦THE CAPSTONE, FIRED — SHARP AND NON-VACUOUS⟧** (`logChowla2_conditional_sharp`).

§8's `logChowla2_conditional_graded` on the SHARP register.  Same twin
(`logChowla2_capstone_final_const'_graded`), same instantiation, same base pin, same fifteen
discharges.  Two changes and no others:

* the band bundle is `S13BandGate'` and the supplier `doorBandBase_family'` — `err` paid by
  the arm at the window top (`S13BandBase` §6) instead of by the deleted numeral residue.
  The supplier's conclusion is byte-identical, so the fire's argument list does not move;
* the register is `S15Sel'`, which absorbs §8's `Mfl ≤ M` quantifier hypothesis.

⟦WHAT IS CARRIED⟧ `S15Sel'` (§9) and `S15CrossingBound` (§4).  Nothing else — and unlike §5
and §8 the hypothesis set is not known-contradictory: see `s15_sel'_anchor_cap`. -/
theorem logChowla2_conditional_sharp :
    ∃ (ε : ℚ) (Cg K δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < K ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
        ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          ∀ M : ℕ, S15Sel' Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R M →
            S15CrossingBound R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀, Hcap, Mfl, hCg, hε, hK, hδ₀, hCt, hCq,
    hcs, hT₀, hKq, hKs, hMfl, hmain⟩ :=
    logChowla2_capstone_final_const'_graded s13Aexp s13Aexp_pos
  refine ⟨ε, Cg, K, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hK, hδ₀, hCt, hMfl, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ K with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hK
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  -- ⟦THE BASE PIN⟧ `R.Hlo = U1floor`
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor
  intro hcap
  -- ⟦the two scale floors⟧
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) ^ ((9 : ℝ) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  -- ⟦the arm, both halves⟧
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family
  have harith := s15_doorArithFrameRho_family (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect' Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_of_halfWindow hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the sharp band register, three of four⟧
  have hgate : S13BandGate' R M x₀ C' (fun _ => 1) :=
    s15_bandGate'_of_grade hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect' hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor le_rfl (s13_g2_jfloor_of_MSelect' hsel.hM (by linarith) hS))
    (s13_gate8 le_rfl (s13_gate8_of_MSelect' (by linarith) hS))
    (s13_smallGradeFits_of_MSelect' hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket hfl hb hsel.hM hρ0 hρ1 htow hsel.rho hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket hfl hb hlam50 htow hsel.rho le_rfl)
    (fun H L q j A s hb => s15_heps293_at_socket hfl hb hρ0 hlam50 htow hsel.rho)
    (fun H L q j A s hb => s15_hband4096_at_socket hfl hb hρ0 hlam50 htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five hsel.hM (hgate.block H L q j A s hb) hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family' hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith

/-- **⟦THE SOCKET FENCE AT THE SHARP REGISTER⟧** (`s15_socketBase_inhabited'`) — §7's
certificate, re-read on `S15Sel'`: the socket family at `(R, M)` is still inhabited, so the
sixteen residue binders of the sharp fire are not vacuous either.  Only `bfloor`, `gRows`,
`half`, `blk` are spent — none of them the deleted line. -/
theorem s15_socketBase_inhabited' {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsel : S15Sel' Cg δ₀ Ct ρ x₀ Mfl R M) :
    SocketBase R M R.Hhi R.Hhi 1 (doorRowFloor M) (2 * R.x) 0 := by
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have hS : MSelect' Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_of_halfWindow hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  have hwin : 2 ^ doorRowFloor M ≤ R.Hlo :=
    s14_window_floor_of_winFit hρ0 hρ1 (hS.winFit R.Hlo le_rfl R.hHlohi)
  exact s14_socketBase_witness (le_trans hwin R.hHlohi)

/-- **⟦THE NEXT-TIGHTEST CAP, AFTER THE REPAIR⟧** (`s15_sel'_anchor_cap`) — ERR-REF's probe C
at the sharp register, with the width law taken as a hypothesis rather than re-derived (the
tower modules are not in this file's import closure; `WIDTH-SCOPE`'s
`probe_regime_width_forced` supplies it at `C0 = 2`, `a = 1`, `λ₋ ≥ 50`).

`S15Sel'.anchor` is now the tightest `λ₊`-cap the register carries: `λ₊ ≤ 2.7857·10⁸`, which
against `λ₊ ≥ λ₋³` reads `λ₋ ≤ 654` — SATISFIED at the working point `λ₋ ≈ 50`.  The deleted
`err` line read `λ₊ ≤ 24849`, i.e. `λ₋ ≤ 29.2`, and was NOT satisfiable there: that is the
whole difference between this conditional and §5's/§8's.

⟦THIS IS NOT A WITNESS⟧ it says the register is not empty FOR THE REASON it was empty; the
`∃M` discharge (`blk`/`half`/`gRows`/`gP1`/`lvl` against the twin's opaque constants) is a
separate piece of work and is not attempted. -/
theorem s15_sel'_anchor_cap {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (h50 : 50 ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hwidth : (Real.log (Real.log (R.Hlo : ℝ))) ^ 3 ≤ Real.log (Real.log (R.Hhi : ℝ)))
    (hsel : S15Sel' Cg δ₀ Ct ρ x₀ Mfl R M) :
    Real.log (Real.log (R.Hlo : ℝ)) ≤ 654 := by
  have hlρ : (0 : ℝ) ≤ Real.log (1 / ρ) := by
    rw [one_div, Real.log_inv]
    have : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
    linarith
  have hanc := hsel.anchor
  set u : ℝ := Real.log (Real.log (R.Hlo : ℝ)) with hudef
  by_contra hcon
  rw [not_le] at hcon
  have hsq : (654 : ℝ) ^ 2 ≤ u ^ 2 := by nlinarith [hcon, h50]
  have hcube : (279726264 : ℝ) ≤ u ^ 3 := by nlinarith [hsq, hcon, h50]
  norm_num at hanc hlρ ⊢
  linarith [hwidth, hcube, hanc, hlρ]

/-- **⟦THE REGISTER SUPPLY, SHARP⟧** (`S15SupplySharp`) — §8's `S15SupplyGraded` with the
`M`-floor absorbed into the register.  TWO conjuncts: the selection register and the crossing
bound. -/
def S15SupplySharp (Cg δ₀ Ct ρ : ℝ) (x₀ Mfl : ℕ) (R : ChowlaRegime) : Prop :=
  ∃ M : ℕ, S15Sel' Cg δ₀ Ct ρ x₀ Mfl R M ∧ S15CrossingBound R M

/-- **⟦THE WITNESSED-SCALE STATEMENT, SHARP⟧** (`logChowla2_witnessed_scale_sharp`) — §6's
corollary at §9's compose.  `LogChowla2WitnessedScale` follows from the sharp register supply
alone, at the road's own constants. -/
theorem logChowla2_witnessed_scale_sharp :
    ∃ (Cg K δ₀ Ct : ℝ) (x₀ Mfl : ℕ), 1 ≤ Cg ∧ 0 < K ∧ 0 < δ₀ ∧ 0 < Ct ∧
      ((∀ R : ChowlaRegime,
          S15SupplySharp Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R) →
        LogChowla2WitnessedScale) := by
  obtain ⟨ε, Cg, K, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hK, hδ₀, hCt, hMfl, hbody⟩ :=
    logChowla2_conditional_sharp
  refine ⟨Cg, K, δ₀, Ct, x₀, Mfl, hCg, hK, hδ₀, hCt, ?_⟩
  intro hsup
  refine logChowla2_witnessed_scale_of_fired ⟨ε, hε, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hHlo, hRg, -, hM⟩ :=
    hbody (max U1floor (max Hcap (max arcFloor36 loglogFloor50))) g (le_max_right _ _)
  obtain ⟨M, hsel, hcap⟩ := hsup R
  exact ⟨R, hReps, by omega, hRg, hM M hsel hcap⟩

/-! ## §10 — ⟦SEL-RECUT⟧ THE REGISTER AT ITS SUPPLIERS' OWN FORMS

PURELY ADDITIVE: §1–§9 are untouched, and `S15Sel'` / `logChowla2_conditional_sharp` stay
exactly as landed.

⟦THE DIAGNOSIS⟧ (`X0MFL-TRACE`, flags 2026-07-31) `S15Sel'` discards two factors its own
suppliers carry, and each discard is a wall:

* **`x0M`** reads `x₀ ≤ M` — a `2^{doorRowFloor M}`-fold strengthening of what
  `S13BandGate'.x0_le` actually asks (`x₀ ≤ 2^{doorRowFloor M}`, `S13BandBase.lean:727`).
  `s15_x0_le` (§3b) is the throwaway bridge between them.  The analytic chain's own `x₀` is
  `≥ exp (exp 100)`, so at the weak form no window admits it and at the tolerant form the
  room is `doorRowFloor M` DOUBLE-LOG units.
* **`anchor`** reads the `ρ`-frame's ⟦C1⟧ line at `log₂M + 1 ≥ 1` (§2's own note) — but
  `M4ArithRho.DoorArithFrameRho.anchor` carries the factor `(log₂M + 1)` (`M4ArithRho:194`).
  Restored, the register's `λ₊`-cap grows WITH `M` and the `M`-ceiling moves from `2^{66}`
  to `2^{356}`.

⟦THE RE-CUT⟧ `S15Sel''` is `S15Sel'` with those two lines stated at the SUPPLIER'S form and
every other line verbatim.  Both consumers take the restored line DIRECTLY: the band gate
asks exactly the tolerant `x0_le`, and the `ρ`-frame's own `anchor` field carries the
`(log₂M + 1)` factor — so `s15_x0_le` is no longer needed in this direction, and §2's
`hn1 : 1 ≤ log₂M + 1` step disappears.  The `jfloor` field, which §2 also paid off the weak
anchor, is repaid off `j ≥ doorRowFloor M ≥ 2^{36}·(log₂M + 1)` — the door's row floor is
itself linear in `log₂M + 1`, so the restored anchor costs the window index nothing.

⟦`mfloor`⟧ unchanged (`Mfl ≤ M`): `Mfl` is the graded twin's exported constant.  What moves
there is its SIZE — `S11HoistGrade` §4's `s11GradeFloor` keeps the `(4·10^{10})^{2.501}` the
landed absorption discards, and delivers `Mfl = 2` at the hoist's own band constant.

⟦THE SURVIVOR LIST⟧ unchanged: `S15CrossingBound` + the register.  -/

/-- **⟦THE `ρ`-FRAME AT ONE SOCKET BASE, AT THE FRAME'S OWN ANCHOR⟧**
(`s15_doorArithFrameRho_at_socket''`) — §2's lemma with `hanchor` taken at
`DoorArithFrameRho.anchor`'s own right side `3.9·10⁹·(log₂M + 1)`.  Two lines change:
`anchor` is now a DIRECT read (no `log₂M + 1 ≥ 1` step), and `jfloor` is paid off the row
floor's own `(log₂M + 1)` factor (`Adoor M = 2^{36}·(log₂M + 1) ≤ doorRowFloor M ≤ j`)
against `1.5 ×` the anchor bracket. -/
theorem s15_doorArithFrameRho_at_socket'' {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    {C₁ : ℕ → ℝ} (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hanchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33
      ≤ 39 * 10 ^ 8 * ((Nat.log 2 M + 1 : ℕ) : ℝ))
    (hHreg : 0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ))
    (hC1 : 0 ≤ C₁ (A + s))
    (hb : SocketBase R M H L q j A s) :
    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
      (s13BandM0 R ρ C₁ (A + s)) 0 ρ := by
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  have hjd : doorRowFloor M ≤ j := hb.2.2.2.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hAx : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) := hb.2.2.2.2.2.2.2.2.2.2.1
  have hω : (0 : ℝ) < (R.ω : ℝ) := by
    have : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
    linarith
  have hlrho : (0 : ℝ) ≤ Real.log (1 / ρ) := log_one_div_nonneg hρ0 hρ1
  have hllH : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) :=
    s13_loglog_le_of_range (R := R) hlo hhi
  have harmA := m4_arith_arm_of_gArmRho hω hHreg.1 hHreg.2 hg hAx
  have hmuA : (356600 : ℝ) ≤ Real.log (Real.log (A : ℝ)) := by
    have := hHreg.2; linarith
  have hlogA : (1 : ℝ) < Real.log (A : ℝ) :=
    one_lt_log_of_loglog_ge (log_natCast_nonneg' A) (by norm_num) hmuA
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have harm := m4_arith_arm_of_shift hApos (by linarith) hAX harmA
  have hlogH0 : (0 : ℝ) < Real.log ((H : ℕ) : ℝ) :=
    lt_of_lt_of_le (by norm_num) (one_lt_log_of_loglog_ge hHreg.1 (by norm_num) hHreg.2).le
  -- ⟦the window index floor, off the row floor's OWN `(log₂M + 1)` factor⟧
  have hjn : (68719476736 : ℝ) * ((Nat.log 2 M + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by
    have h1 : Adoor M ≤ doorRowFloor M := by
      rw [doorRowFloor]; exact Nat.le_mul_of_pos_left _ hM
    have h2 : 2 ^ 36 * (Nat.log 2 M + 1) ≤ j := le_trans h1 hjd
    have h3 : ((2 ^ 36 * (Nat.log 2 M + 1) : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast h2
    push_cast at h3 ⊢
    linarith
  have hn0 : (0 : ℝ) ≤ ((Nat.log 2 M + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
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

/-- **⟦THE FAMILY FORM, AT THE RESTORED ANCHOR⟧** (`s15_doorArithFrameRho_family''`). -/
theorem s15_doorArithFrameRho_family'' {R : ChowlaRegime} {M : ℕ} {ρ : ℝ} {C₁ : ℕ → ℝ}
    (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hanchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33
      ≤ 39 * 10 ^ 8 * ((Nat.log 2 M + 1 : ℕ) : ℝ))
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ))
    (hC1 : ∀ n : ℕ, 0 ≤ C₁ n) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) 0 ρ := by
  intro H L q j A s hb
  exact s15_doorArithFrameRho_at_socket'' hM hρ0 hρ1 hanchor (hHreg H hb.1 hb.2.1)
    (hg H hb.1 hb.2.1) (hC1 (A + s)) hb

/-- **⟦THE `M`-SELECTION REGISTER, RE-CUT⟧** (`S15Sel'' Cg δ₀ Ct ρ x₀ Mfl R M`) — §9's
`S15Sel'` with `x0M` and `anchor` restated at their suppliers' own forms.  Eleven lines; nine
are §9's byte for byte. -/
structure S15Sel'' (Cg δ₀ Ct ρ : ℝ) (x₀ Mfl : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop where
  /-- the door's parameter is a modulus. -/
  hM : 1 ≤ M
  /-- ⟦`M`-LOWER 0⟧ the graded twin's own `ℕ`-floor (`S11HoistGrade` §4: `Mfl = 2`). -/
  mfloor : Mfl ≤ M
  /-- ⟦`M`-LOWER 1⟧ `MSelect'.bfloor` = `M4DoorGates.hMδ`. -/
  bfloor : 24 * Cg / δ₀ ≤ (M : ℝ)
  /-- ⟦`M`-LOWER 2⟧ `MSelect'.gRows` — pays ⟦gate 8⟧ (`hdgate`) and ⟦G2⟧ (`hj0`). -/
  gRows : 242 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ ((Adoor M : ℕ) : ℝ)
  /-- ⟦RESTORED⟧ the opaque threshold at `S13BandGate'.x0_le`'s OWN form. -/
  x0M : x₀ ≤ 2 ^ doorRowFloor M
  /-- ⟦`M`-UPPER 1⟧ `MSelect'.blockCeil` AND ⟦F3⟧'s `block`, off `hPHheadroom` (`§3b`). -/
  blk : ((s13BlockExp M : ℕ) : ℝ) + 1 + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)
  /-- ⟦`M`-UPPER 2⟧ THE WINDOW GATE at the half-window floor (`s13_winFit_of_halfWindow`). -/
  half : (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
    ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 2
  /-- the clearing charge — `ρ ≥ e^{−10^{14}}`. -/
  rho : -Real.log ρ ≤ 100000000000000
  /-- ⟦RESTORED⟧ the `ρ`-frame's ⟦C1⟧ anchor at `DoorArithFrameRho.anchor`'s OWN right side. -/
  anchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33
    ≤ 39 * 10 ^ 8 * ((Nat.log 2 M + 1 : ℕ) : ℝ)
  /-- the `𝒯`-leg budget at `constPool` (`s15_gP1_of_budget`). -/
  gP1 : 29 + Real.log Ct + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ ((Adoor M : ℕ) : ℝ) * Real.log 2 + Real.log ρ
  /-- the `level1` budget — the BINDING const-pool line (`Adoor M ≳ 242.4·Λ`). -/
  lvl : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      + (1 / 3) * Real.log (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ))
      + (-Real.log ρ)
    ≤ (1 / 12) * ((Adoor M : ℕ) : ℝ) * Real.log 2

/-- `MSelect'.blockCeil`'s `ℕ`-form, read off the re-cut register's `M`-upper (§9 verbatim). -/
theorem S15Sel''.head {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hsel : S15Sel'' Cg δ₀ Ct ρ x₀ Mfl R M)
    (hΛ : 0 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) :
    s13BlockExp M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1 := by
  have h := hsel.blk
  have hR : ((s13BlockExp M : ℕ) : ℝ) ≤ ((4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
    push_cast; linarith
  have : s13BlockExp M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ := by exact_mod_cast hR
  omega

/-- **⟦THE SHARP BAND REGISTER, RE-CUT⟧** (`s15_bandGate''_of_grade`) — §9's
`s15_bandGate'_of_grade` with `x0_le` taken from the register DIRECTLY (`s15_x0_le` is not
consumed in this direction). -/
theorem s15_bandGate''_of_grade {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    {C' : ℝ} (hfl : loglogFloor50 ≤ R.Hlo) (hsel : S15Sel'' Cg δ₀ Ct ρ x₀ Mfl R M)
    (hgrade : 8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
      ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))) :
    S13BandGate' R M x₀ C' (fun _ => 1) where
  x0_le := hsel.x0M
  C1_one := fun _ => le_rfl
  grade := hgrade
  block := by
    intro H L q j A s hb
    exact s15_block_at_socket hb (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk

set_option maxHeartbeats 1000000 in
-- Same cause as §5, §8 and §9: the twin's residue re-elaborates against the instantiated
-- prefix.
/-- **⟦THE CAPSTONE, FIRED ON THE RE-CUT REGISTER⟧** (`logChowla2_conditional_sharp2`).

§9's `logChowla2_conditional_sharp` on `S15Sel''`.  Same twin
(`logChowla2_capstone_final_const'_graded`), same instantiation, same base pin, same fifteen
discharges, same survivor.  The only movement is inside two discharges:

* the arithmetic frame family is `s15_doorArithFrameRho_family''` — the anchor read at the
  frame's own `(log₂M + 1)` right side;
* the band bundle is `s15_bandGate''_of_grade` — `x0_le` read at the gate's own tolerant
  form.

⟦WHAT IS CARRIED⟧ `S15Sel''` (§10) and `S15CrossingBound` (§4).  Nothing else. -/
theorem logChowla2_conditional_sharp2 :
    ∃ (ε : ℚ) (Cg K δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < K ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
        ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          ∀ M : ℕ, S15Sel'' Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R M →
            S15CrossingBound R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀, Hcap, Mfl, hCg, hε, hK, hδ₀, hCt, hCq,
    hcs, hT₀, hKq, hKs, hMfl, hmain⟩ :=
    logChowla2_capstone_final_const'_graded s13Aexp s13Aexp_pos
  refine ⟨ε, Cg, K, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hK, hδ₀, hCt, hMfl, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ K with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hK
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  -- ⟦THE BASE PIN⟧ `R.Hlo = U1floor`
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor
  intro hcap
  -- ⟦the two scale floors⟧
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) ^ ((9 : ℝ) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  -- ⟦the arm, both halves⟧
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the RESTORED anchor
  have harith := s15_doorArithFrameRho_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect' Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_of_halfWindow hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register, at the RESTORED `x0_le`⟧
  have hgate : S13BandGate' R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect' hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor le_rfl (s13_g2_jfloor_of_MSelect' hsel.hM (by linarith) hS))
    (s13_gate8 le_rfl (s13_gate8_of_MSelect' (by linarith) hS))
    (s13_smallGradeFits_of_MSelect' hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket hfl hb hsel.hM hρ0 hρ1 htow hsel.rho hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket hfl hb hlam50 htow hsel.rho le_rfl)
    (fun H L q j A s hb => s15_heps293_at_socket hfl hb hρ0 hlam50 htow hsel.rho)
    (fun H L q j A s hb => s15_hband4096_at_socket hfl hb hρ0 hlam50 htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five hsel.hM (hgate.block H L q j A s hb) hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family' hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith

/-- **⟦THE SOCKET FENCE AT THE RE-CUT REGISTER⟧** (`s15_socketBase_inhabited''`) — §7's
certificate again: only `bfloor`, `gRows`, `half`, `blk` are spent, and none of those moved. -/
theorem s15_socketBase_inhabited'' {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsel : S15Sel'' Cg δ₀ Ct ρ x₀ Mfl R M) :
    SocketBase R M R.Hhi R.Hhi 1 (doorRowFloor M) (2 * R.x) 0 := by
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have hS : MSelect' Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_of_halfWindow hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  have hwin : 2 ^ doorRowFloor M ≤ R.Hlo :=
    s14_window_floor_of_winFit hρ0 hρ1 (hS.winFit R.Hlo le_rfl R.hHlohi)
  exact s14_socketBase_witness (le_trans hwin R.hHlohi)

