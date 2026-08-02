/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S15SelLinear
import Salt.MR.S16FlatTerminal

/-!
# `S15SelLinearWide` — THE ACCEPTANCE AT THE **WIDE** RIDERS, AND THE JOINT POINT

⟦COMPOSE-FLAT-2, the accounting half⟧  `S15SelLinear`'s acceptance theorem
(`s15_sel''_L_witness_flat`) was minted against the OLD NARROW riders — `1/2^10 ≤ δ₀`,
`Kc ≤ 2^20`, `Ct ≤ 2^20` — every one of which is FALSE at the terminal's own witness:
the pinned `δ₀` is `1/838400` (⟦S16Budget⟧ `hδpin`), `Kc`'s honest ceiling is `2^539`
(`KExpr_le`) and `Ct = 6·e^{14} > 2^20` (`s16_audit_Ct_over_pin`).  ⟦REPAIRS-LANE⟧ certified
the wide numerals in `S16Budget` §6.3/§6.6; this file SPENDS them at the linear door.

⟦§1 — THE FIVE `ρ`-LINES, CHARGE-GENERIC⟧  Exactly five of `S15Sel''_L`'s eleven lines read
the clearing charge (`half`, `rho`, `anchor`, `gP1`, `lvl`); the other six are `ρ`-free and
transport from the landed acceptance verbatim.  Each of the five is restated here with the
charge as a PARAMETER `c` and closed at `c ≤ 403` — the WIDE charge
(`s16_audit_neglog_rho_le_wide`), which is `11.2×` the narrow `36`.  The margins are
unaffected: the binding line is still `half`, at `4.1·10^{-4}·e^{3.2A}` of slack against a
`1209` spend.

⟦§2 — THE WIDE ACCEPTANCE⟧ `s15_sel''_L_witness_flat_wide` and its levered twin
`s15_sel''_L_gk_witness_flat_wide` — the register at the flat design point under
`1/2^20 ≤ δ₀`, `Kc ≤ 2^539`, `Ct ≤ 2^23`.  Still NO upper bound on `A`.

⟦§3 — THE JOINT POINT⟧ `flat_linear_joint_point` — the certificate the compose refuter's
mandate asks for: the three hunts (⟦H1-ANCHOR⟧, ⟦H2-CONSTANTS⟧, ⟦H3-SHAPE⟧) ran in parallel
and never met in one kernel statement.  Here they do, at `λ₋ = 3.2·A`, `M = flatDoorM A`,
`λ₊ = e^{1.6A}`, uniformly in `A ≥ 26`: the flat floor invariant, the Fannes ceiling, the
width law's OWN demand `4^{(20/21)A}` (`TowerFlat.towerFlat_width_ge`) against the supplied
width, the linear `anchor`/`gRows` pair, the `half` window, and the budget's height-1 floor
under the pinned base.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — the flat design point's five `ρ`-lines, with the charge as a parameter -/

/-- `19·y ≤ e^y` for `y ≥ 7` — the linear-vs-exponential step the width comparison needs
(`e^7 ≥ 2.718^7 ≥ 1095`, then `e^{y-7} ≥ 1 + (y-7)`). -/
theorem flat_exp_ge_lin {y : ℝ} (hy : 7 ≤ y) : 19 * y ≤ Real.exp y := by
  have he : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp : (2.718 : ℝ) ^ (7 : ℕ) ≤ (Real.exp 1) ^ (7 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) he.le 7
  have hE : (Real.exp 1) ^ (7 : ℕ) = Real.exp 7 := by rw [← Real.exp_nat_mul]; norm_num
  have hn : (1095 : ℝ) ≤ (2.718 : ℝ) ^ (7 : ℕ) := by norm_num
  rw [hE] at hp
  have he7 : (1095 : ℝ) ≤ Real.exp 7 := by linarith
  have hsplit : Real.exp 7 * Real.exp (y - 7) = Real.exp y := by
    rw [← Real.exp_add]; congr 1; ring
  have hlin : (y - 7) + 1 ≤ Real.exp (y - 7) := Real.add_one_le_exp (y - 7)
  have h1 : Real.exp 7 * ((y - 7) + 1) ≤ Real.exp 7 * Real.exp (y - 7) :=
    mul_le_mul_of_nonneg_left hlin (Real.exp_pos 7).le
  rw [hsplit] at h1
  nlinarith [he7, h1, mul_nonneg (by linarith : (0 : ℝ) ≤ Real.exp 7 - 1095)
    (by linarith : (0 : ℝ) ≤ y - 6)]

/-- ⟦`M`-LOWER 2⟧ **THE `gRows` LINE AT THE FLAT DESIGN POINT** — `242·λ₊ ≤ A_L(M)` at
`λ₊ ≤ e^{1.6A}` and `M = flatDoorM A`: `242·E` against `2.2146·10⁵·E`, `915×`.  Charge-free. -/
theorem flat_gRows_line {A : ℝ} (hA : 26 ≤ A) :
    242 * Real.exp (3.2 * A / 2) ≤ ((AdoorL (flatDoorM A) : ℕ) : ℝ) := by
  have hE17 := flat_exp_half_ge hA
  have hMge := flatDoorM_ge A
  rw [AdoorL_cast]
  linarith

/-- ⟦THE REPAIR⟧ **THE `anchor` LINE AT THE FLAT DESIGN POINT**, at ANY charge `c ≤ 403`:
`14·E + 436` against `1.2568·10⁴·E`, `898×`.  This is ⟦H1-ANCHOR⟧'s repair at the WIDE
charge — the eleven-order widening of `Kc` is invisible here. -/
theorem flat_anchor_line {A c : ℝ} (hA : 26 ≤ A) (hc : c ≤ 403) :
    14 * Real.exp (3.2 * A / 2) + c + 33 ≤ 39 * 10 ^ 8 * ((flatDoorM A : ℕ) : ℝ) := by
  have hE17 := flat_exp_half_ge hA
  have hMge := flatDoorM_ge A
  linarith

/-- **THE `anchor` LINE AT THE DOUBLED `Λ` SLOT** ⟦amended per REF-FLAT-SAT⟧ — the same line
at `Λ ≤ 2·E`, the width the road can actually export off a `Nat.ceil`-pinned base:
`28·E + 436` against `1.2568·10⁴·E`, `449×`.  Half the margin, still three orders. -/
theorem flat_anchor_line_wide {A c : ℝ} (hA : 26 ≤ A) (hc : c ≤ 403) :
    14 * (2 * Real.exp (3.2 * A / 2)) + c + 33
      ≤ 39 * 10 ^ 8 * ((flatDoorM A : ℕ) : ℝ) := by
  have hE17 := flat_exp_half_ge hA
  have hMge := flatDoorM_ge A
  linarith

/-- ⟦`M`-UPPER 2⟧ **THE WINDOW GATE AT THE FLAT DESIGN POINT**, at ANY charge `c ≤ 403`:
`0.49959·e^{3.2A} + 1209` against `e^{3.2A}/2`.  THE BINDING LINE — `M` sits at its ceiling
by design — and still `4.1·10^{-4}·e^{3.2A}` of slack pays the `1209`. -/
theorem flat_half_line {A c : ℝ} (hA : 26 ≤ A) (hc : c ≤ 403) :
    (7 / 10 : ℝ) * ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ) + 3 * c
      ≤ Real.exp (3.2 * A) / 2 := by
  have hE17 := flat_exp_half_ge hA
  have hE0 : (0 : ℝ) < Real.exp (3.2 * A / 2) := Real.exp_pos _
  have hMle := flatDoorM_le A
  have hM0 : (0 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := Nat.cast_nonneg _
  have hY := flat_exp_sq A
  have hrow : ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ)
      = 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 := by
    rw [doorRowFloorL, AdoorL]; push_cast; ring
  have h1 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 - ((flatDoorM A : ℕ) : ℝ) := by
    linarith
  have h2 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 + ((flatDoorM A : ℕ) : ℝ) := by
    positivity
  have hsq : ((flatDoorM A : ℕ) : ℝ) ^ 2
      ≤ Real.exp (3.2 * A / 2) ^ 2 / 96286710601 := by
    nlinarith [mul_nonneg h1 h2]
  have hE2 : (10 : ℝ) ^ 34 ≤ Real.exp (3.2 * A / 2) ^ 2 := by nlinarith [hE17, hE0]
  rw [hrow, ← hY]
  linarith [hsq, hE2, hc]

/-- **THE `𝒯`-LEG BUDGET AT THE FLAT DESIGN POINT**, at the WIDE `Ct ≤ 2^23` and ANY charge
`c ≥ -403`: at the amended `2E` slot (`Λ ≤ 2·e^{1.6A}`) it spends `28·E + 45` against
`1.53·10⁵·E`, `≈5.5·10³×`.  `Ct`'s `8×` widening costs `2.08` on a line with eleven orders
of slack. -/
theorem flat_gP1_line {A c Ct Λ : ℝ} (hA : 26 ≤ A) (hc : -403 ≤ c) (hCt : 0 < Ct)
    -- amended per REF-FLAT-SAT: the `Λ` slot carries the `Nat.ceil` overshoot factor `2`
    (hCtb : Ct ≤ 2 ^ 23) (hΛ : Λ ≤ 2 * Real.exp (3.2 * A / 2)) :
    29 + Real.log Ct + 14 * Λ ≤ ((AdoorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2 + c := by
  have hE17 := flat_exp_half_ge hA
  have hMge := flatDoorM_ge A
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hAdlo : 221460 * Real.exp (3.2 * A / 2) - 68719476737
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) := by linarith
  have hpos : (0 : ℝ) ≤ 221460 * Real.exp (3.2 * A / 2) - 68719476737 := by linarith
  have h1 : (221460 * Real.exp (3.2 * A / 2) - 68719476737) * Real.log 2
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hAdlo (by linarith)
  have hAdlog : 153000 * Real.exp (3.2 * A / 2)
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 := by
    nlinarith [hpos, hlog2lo, hE17]
  have hCtl : Real.log Ct ≤ 23 * Real.log 2 := by
    have h := Real.log_le_log hCt hCtb
    rwa [Real.log_pow] at h
  rw [AdoorL_cast]
  linarith

/-- **THE `level1` BUDGET AT THE FLAT DESIGN POINT**, at ANY charge `c ≤ 403`: at the amended
`2E` slot (`Λ ≤ 2·e^{1.6A}`) it spends `28·E + 429 + ⅔·log E` against `1.279·10⁴·E`,
`457×`. -/
theorem flat_lvl_line {A c Λ : ℝ} (hA : 26 ≤ A) (hc : c ≤ 403)
    -- amended per REF-FLAT-SAT: the `Λ` slot carries the `Nat.ceil` overshoot factor `2`
    (hΛ : Λ ≤ 2 * Real.exp (3.2 * A / 2)) :
    26 + 14 * Λ
        + (1 / 3) * Real.log (Real.log ((calQK (AdoorL (flatDoorM A))
            (3072 * flatDoorM A) (flatDoorM A) 1 : ℕ) : ℝ)) + c
      ≤ (1 / 12) * ((AdoorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2 := by
  have hE17 := flat_exp_half_ge hA
  have hE0 : (0 : ℝ) < Real.exp (3.2 * A / 2) := Real.exp_pos _
  have hMle := flatDoorM_le A
  have hMge := flatDoorM_ge A
  have hM0 : (0 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hrow : ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ)
      = 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 := by
    rw [doorRowFloorL, AdoorL]; push_cast; ring
  have hAdlo : 221460 * Real.exp (3.2 * A / 2) - 68719476737
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) := by linarith
  have hpos : (0 : ℝ) ≤ 221460 * Real.exp (3.2 * A / 2) - 68719476737 := by linarith
  have h1 : (221460 * Real.exp (3.2 * A / 2) - 68719476737) * Real.log 2
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hAdlo (by linarith)
  have hAdlog : 153000 * Real.exp (3.2 * A / 2)
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 := by
    nlinarith [hpos, hlog2lo, hE17]
  rw [AdoorL_cast, s15_log_calQK_L_one, hrow]
  have hQpos : (0 : ℝ) < 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 * Real.log 2 := by
    have hM1N : 1 ≤ flatDoorM A := flatDoorM_one_le hA
    have hM1 : (1 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := by exact_mod_cast hM1N
    have : (0 : ℝ) < Real.log 2 := by linarith
    positivity
  have hd1 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 - ((flatDoorM A : ℕ) : ℝ) := by
    linarith
  have hd2 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 + ((flatDoorM A : ℕ) : ℝ) := by
    positivity
  have hsq : ((flatDoorM A : ℕ) : ℝ) ^ 2
      ≤ Real.exp (3.2 * A / 2) ^ 2 / 96286710601 := by
    nlinarith [mul_nonneg hd1 hd2]
  have hQle : 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 * Real.log 2
      ≤ Real.exp (3.2 * A / 2) ^ 2 := by
    nlinarith [hsq, hlog2hi, sq_nonneg (Real.exp (3.2 * A / 2)), hM0,
      sq_nonneg ((flatDoorM A : ℕ) : ℝ)]
  have hlogQ : Real.log (68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 * Real.log 2)
      ≤ 2 * Real.log (Real.exp (3.2 * A / 2)) := by
    have h := Real.log_le_log hQpos hQle
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlogE : Real.log (Real.exp (3.2 * A / 2)) ≤ Real.exp (3.2 * A / 2) - 1 :=
    Real.log_le_sub_one_of_pos hE0
  have hbud : 12750 * Real.exp (3.2 * A / 2)
      ≤ 1 / 12 * (68719476736 * ((flatDoorM A : ℕ) : ℝ)) * Real.log 2 := by
    linarith [hAdlog]
  linarith [hΛ, hc, hlogQ, hlogE, hbud, hE17]

/-! ## §2 — ⟦THE WIDE ACCEPTANCE⟧ -/

/-- **⟦THE REGISTER AT THE FLAT DESIGN POINT, CHARGE-GENERIC⟧**
(`s15_sel''_L_witness_flat_charge`) — `s15_sel''_L_witness_flat` with the clearing charge
carried as a hypothesis `-log ρ ≤ 403` instead of being computed from narrow `δ₀`/`Kc`
ceilings, and with `Ct`'s ceiling at the honest `2^23`.

The six `ρ`-free lines (`hM`, `mfloor`, `bfloor`, `gRows`, `x0M`, `blk`) are the landed
acceptance's, read off at a dummy narrow instance — they do not mention `ρ`, `Ct`, `Cg` or
`δ₀`, so the instance is legal.  The five charge-spending lines are §1's. -/
theorem s15_sel''_L_witness_flat_charge {A : ℝ} (hA : 26 ≤ A) {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ}
    {R : ChowlaRegime}
    (hρlog : -Real.log ρ ≤ 403)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    -- amended per REF-FLAT-SAT: the `Λ` slot carries the `Nat.ceil` overshoot factor `2`
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L Cg δ₀ Ct ρ x₀ Mfl R (flatDoorM A) := by
  have hbase := s15_sel''_L_witness_flat (A := A) (Cg := 0) (δ₀ := 1 / 2 ^ 10) (Ct := 1)
    (K := 1) (x₀ := x₀) (Mfl := Mfl) (R := R) hA (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by simp) hMfl hx0win heps hlo hhi
  have hinv : Real.log (1 / ρ) = -Real.log ρ := by rw [one_div, Real.log_inv]
  refine
    { hM := hbase.hM
      mfloor := hMfl
      bfloor := hbfl
      gRows := hbase.gRows
      x0M := hbase.x0M
      blk := hbase.blk
      half := ?_
      rho := ?_
      anchor := ?_
      gP1 := ?_
      lvl := ?_ }
  · rw [hinv]
    exact le_trans (flat_half_line hA hρlog) (by linarith [hlo])
  · linarith [hρlog]
  · rw [hinv]
    -- amended per REF-FLAT-SAT: the wide anchor line, at the doubled `Λ` slot
    exact le_trans (by linarith [hhi]) (flat_anchor_line_wide hA hρlog)
  · exact flat_gP1_line hA (by linarith [hρlog]) hCt hCtb hhi
  · exact flat_lvl_line hA hρlog hhi

/-- **⟦THE WIDE ACCEPTANCE⟧** (`s15_sel''_L_witness_flat_wide`) — `S15SelLinear`'s acceptance
theorem at the riders that are TRUE at the terminal's own witness: `1/2^20 ≤ δ₀`
(the pinned `1/838400` clears it by `1.25×`), `Kc ≤ 2^539` (`KExpr_le`'s honest ceiling) and
`Ct ≤ 2^23` (`s16_audit_Ct_ceiling`, `14 %` of room).  The charge moves `36 → 403`
(`s16_audit_neglog_rho_le_wide`).

⟦WHAT DOES **NOT** APPEAR⟧ any upper bound on `A` — unchanged. -/
theorem s15_sel''_L_witness_flat_wide {A : ℝ} (hA : 26 ≤ A) {Cg δ₀ Ct K : ℝ} {x₀ Mfl : ℕ}
    {R : ChowlaRegime}
    (hδ : 0 < δ₀) (hδb : 1 / 2 ^ 20 ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 539)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    -- amended per REF-FLAT-SAT: the `Λ` slot carries the `Nat.ceil` overshoot factor `2`
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R (flatDoorM A) :=
  s15_sel''_L_witness_flat_charge hA (s16_audit_neglog_rho_le_wide hδ hK hδb hKb) hCt hCtb
    hbfl hMfl hx0win heps hlo hhi

/-- **THE LEVERED `blk` LINE AT THE FLAT DESIGN POINT** — charge-free and constant-free, so
it is read off the landed levered acceptance at a dummy narrow instance.  `4^K ≤ e^{760·E}`
against `e^{E²}` at `E ≥ 10^{17}`. -/
theorem flat_blk_line_gk {A : ℝ} (hA : 26 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {R : ChowlaRegime}
    (heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    -- amended per REF-FLAT-SAT: the `Λ` slot carries the `Nat.ceil` overshoot factor `2`
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    ((s13BlockExp_L_gk Klev (flatDoorM A) : ℕ) : ℝ) + 1
        + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) :=
  (s15_sel''_L_gk_witness_flat (A := A) (Cg := 0) (δ₀ := 1 / 2 ^ 10) (Ct := 1) (K := 1)
    (x₀ := 0) (Mfl := 0) hA Klev hKle (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by simp) (by simp)
    (by simpa using (Real.exp_pos (Real.exp (3.2 * A) / 10)).le) heps hlo hhi).blk

/-- **⟦THE LEVERED WIDE ACCEPTANCE⟧** (`s15_sel''_L_gk_witness_flat_wide`) — the wide
register at the `G`-lever, `Klev` at the linear door's own ceiling `1.7·10⁸·M`. -/
theorem s15_sel''_L_gk_witness_flat_wide {A : ℝ} (hA : 26 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {Cg δ₀ Ct K : ℝ} {x₀ Mfl : ℕ}
    {R : ChowlaRegime}
    (hδ : 0 < δ₀) (hδb : 1 / 2 ^ 20 ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 539)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    -- amended per REF-FLAT-SAT: the `Λ` slot carries the `Nat.ceil` overshoot factor `2`
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L_gk Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R
      (flatDoorM A) :=
  s15_sel''_L_gk_of_L Klev
    (s15_sel''_L_witness_flat_wide hA hδ hδb hK hKb hCt hCtb hbfl hMfl hx0win heps hlo hhi)
    (flat_blk_line_gk hA Klev hKle heps hlo hhi)

/-! ## §3 — ⟦THE JOINT POINT⟧ -/

/-- `flatC A = log(2A) ≤ 2A − 1`, and `flatC A ≥ 0` at `A ≥ 26`. -/
theorem flatC_bracket {A : ℝ} (hA : 26 ≤ A) : 0 ≤ flatC A ∧ flatC A ≤ 2 * A - 1 := by
  constructor
  · exact Real.log_nonneg (by linarith)
  · have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * A by linarith)
    exact this

/-- `4^{(20/21)·A} ≤ e^{1.3203·A}` — the master law's exponent in `e`-glyphs
(`(20/21)·log 4 = 1.32028…`). -/
theorem flat_rpow_four_le {A : ℝ} (hA : 26 ≤ A) :
    (4 : ℝ) ^ ((20 / 21 : ℝ) * A) ≤ Real.exp (1.3203 * A) := by
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hdef : (4 : ℝ) ^ ((20 / 21 : ℝ) * A) = Real.exp (Real.log 4 * ((20 / 21 : ℝ) * A)) :=
    Real.rpow_def_of_pos (by norm_num) _
  rw [hdef]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [hl4, hl2, hA]

/-- **⟦THE JOINT POINT EXISTS⟧** (`flat_linear_joint_point`) — the compose refuter's mandate,
in ONE kernel statement.  At `λ₋ = 3.2·A`, `L₋ = e^{3.2A}`, `λ₊ = e^{1.6A}`,
`M = flatDoorM A`, and UNIFORMLY IN `A ≥ 26`:

1. ⟦THE FLAT FLOOR⟧ `100·(c + λ₋) ≤ L₋` — `TowerFlat`'s tower invariant `hfl`, the one new
   hypothesis `MASTER-LAW-KERNEL` introduced.  Slack: `28` orders.
2. ⟦THE FANNES CEILING⟧ `φ ≤ L₋/(6·log 2)` at `φ ≡ A` — ⟦H3-SHAPE⟧'s upper bound on any
   admissible threshold.  Slack: `e^{3.2A}/A`.
3. ⟦THE WIDTH LAW'S DEMAND⟧ `(c + λ₋)·4^{(20/21)A} ≤ c + λ₊` — `towerFlat_width_ge`'s OWN
   conclusion, against the width the flat export SUPPLIES.  This is the face ⟦H3-SHAPE⟧
   proved is EXTREMAL: `4^{(20/21)A} = e^{1.3203A}` against `e^{1.6A}`, so the margin is an
   exponent gap of `0.2797·A` — the only conjunct here that is not astronomic.
4. ⟦THE LINEAR ANCHOR⟧ `14·λ₊ + 403 + 33 ≤ 3.9·10⁹·M` — ⟦H1-ANCHOR⟧'s repair, at the WIDE
   `ρ`-charge.  `449×` at the amended `2E` slot (`λ₊ ≤ 2·e^{1.6A}`).
5. ⟦`gRows`⟧ `242·λ₊ ≤ A_L(M)`.  `457×` at the same slot.
6. ⟦THE HALF WINDOW⟧ `0.7·doorRowFloorL M + 3·403 ≤ L₋/2` — the binding register line, `M`
   at its ceiling.
7. ⟦THE BUDGET'S HEIGHT-1 FLOOR⟧ `budgetFloorFlat ε β A ≤ flatWitFloor ε β A Hopq` for every
   `ε`, `β`, `Hopq` — the pinned base dominates the flat budget floor, which is HEIGHT 1
   (`⌈e^{max(4X, 2 log A + 2)}⌉₊`), not the landed height-3 `budgetFloor`.

⟦WHAT THIS SETTLES⟧ the three hunts ran in parallel and never met.  Conjuncts 3–6 are the
meeting: the width the tower DEMANDS (3) is below the width the export supplies, and that
supplied width is below what the linear door HOSTS (4,5) at an `M` the window still
admits (6).  No conjunct caps `A`. -/
theorem flat_linear_joint_point {A : ℝ} (hA : 26 ≤ A) :
    100 * (flatC A + 3.2 * A) ≤ Real.exp (3.2 * A) ∧
    A ≤ Real.exp (3.2 * A) / (6 * Real.log 2) ∧
    (flatC A + 3.2 * A) * (4 : ℝ) ^ ((20 / 21 : ℝ) * A)
      ≤ flatC A + Real.exp (3.2 * A / 2) ∧
    14 * Real.exp (3.2 * A / 2) + 403 + 33 ≤ 39 * 10 ^ 8 * ((flatDoorM A : ℕ) : ℝ) ∧
    242 * Real.exp (3.2 * A / 2) ≤ ((AdoorL (flatDoorM A) : ℕ) : ℝ) ∧
    (7 / 10 : ℝ) * ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ) + 3 * 403
      ≤ Real.exp (3.2 * A) / 2 ∧
    (∀ (ε : ℚ) (β : ℝ) (Hopq : ℕ),
      budgetFloorFlat (ε : ℝ) β A ≤ flatWitFloor ε β A Hopq) := by
  obtain ⟨hC0, hCle⟩ := flatC_bracket hA
  have hA0 : (0 : ℝ) < A := by linarith
  have hcube : (17576 : ℝ) ≤ A ^ 3 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 26 by norm_num) hA 3
    have h26 : ((26 : ℝ)) ^ (3 : ℕ) = 17576 := by norm_num
    rw [h26] at h
    exact h
  have hquart : (17576 : ℝ) * A ≤ A ^ 4 := by nlinarith [hcube, hA0]
  have hqe : (3.2 * A) ^ 4 / 256 ≤ Real.exp (3.2 * A) :=
    flat_exp_ge_quartic (by linarith)
  have hbig : (7199 : ℝ) * A ≤ Real.exp (3.2 * A) := by nlinarith [hqe, hquart, hA0]
  refine ⟨by linarith, ?_, ?_, flat_anchor_line hA le_rfl, flat_gRows_line hA,
    flat_half_line hA le_rfl, ?_⟩
  · -- ⟦2⟧ the Fannes ceiling
    have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hl2p : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [le_div_iff₀ (by linarith)]
    nlinarith [hbig, hA0, hl2]
  · -- ⟦3⟧ the width law's demand against the supplied width
    have h4 := flat_rpow_four_le hA
    have hs : (0 : ℝ) < flatC A + 3.2 * A := by linarith
    have hy : (7 : ℝ) ≤ 0.2797 * A := by linarith
    have hlin : 19 * (0.2797 * A) ≤ Real.exp (0.2797 * A) := flat_exp_ge_lin hy
    have hgap : flatC A + 3.2 * A ≤ Real.exp (0.2797 * A) := by nlinarith [hlin, hCle, hA]
    have hsplit : Real.exp (1.3203 * A) * Real.exp (0.2797 * A) = Real.exp (3.2 * A / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hstep : (flatC A + 3.2 * A) * (4 : ℝ) ^ ((20 / 21 : ℝ) * A)
        ≤ Real.exp (0.2797 * A) * Real.exp (1.3203 * A) := by
      have h1 : (flatC A + 3.2 * A) * (4 : ℝ) ^ ((20 / 21 : ℝ) * A)
          ≤ (flatC A + 3.2 * A) * Real.exp (1.3203 * A) :=
        mul_le_mul_of_nonneg_left h4 (by linarith)
      have h2 : (flatC A + 3.2 * A) * Real.exp (1.3203 * A)
          ≤ Real.exp (0.2797 * A) * Real.exp (1.3203 * A) :=
        mul_le_mul_of_nonneg_right hgap (Real.exp_pos _).le
      linarith
    have hid : Real.exp (0.2797 * A) * Real.exp (1.3203 * A) = Real.exp (3.2 * A / 2) := by
      rw [mul_comm]; exact hsplit
    linarith [hstep, hid.le, hid.ge, hC0]
  · -- ⟦7⟧ the budget's height-1 floor under the pinned base
    intro ε β Hopq
    rw [flatWitFloor]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_trans (le_max_right _ _) (le_max_left _ _))

/-! ## §4 — ⟦THE RESIDUE⟧ the transport ledger, the socket form, and the ROAD's break -/

/-- `s13BlockExp M ≤ s13BlockExp_L M` — the block exponent GROWS under the re-cut
(`Adoor_le_AdoorL`), so the linear `blk` line is the STRONGER of the two. -/
theorem s13BlockExp_le_L {M : ℕ} (hM : 1 ≤ M) : s13BlockExp M ≤ s13BlockExp_L M := by
  rw [s13BlockExp, s13BlockExp_L]
  have h : Adoor M * (3072 * M) * M ≤ AdoorL M * (3072 * M) * M :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Adoor_le_AdoorL hM))
  have h2 : (Adoor M * (3072 * M) * M) ^ 2 ≤ (AdoorL M * (3072 * M) * M) ^ 2 :=
    Nat.pow_le_pow_left h 2
  omega

/-- ⟦THE TRANSPORT LEDGER, `blk`⟧ the LINEAR register's block ceiling implies the LANDED
one.  With `mfloor`, `bfloor`, `rho` (identical) and `half` (below) these are the four lines
that survive the re-cut in the SUPPLY direction; `gRows`, `anchor`, `gP1`, `lvl` and `x0M`
do not — they are strictly weaker at the linear door, and that is exactly the price
⟦H1-ANCHOR⟧'s repair pays. -/
theorem s15_sel''_L_blk_landed {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hsel : S15Sel''_L Cg δ₀ Ct ρ x₀ Mfl R M) :
    ((s13BlockExp M : ℕ) : ℝ) + 1 + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
  have hle : ((s13BlockExp M : ℕ) : ℝ) ≤ ((s13BlockExp_L M : ℕ) : ℝ) := by
    exact_mod_cast s13BlockExp_le_L hsel.hM
  linarith [hsel.blk]

/-- ⟦THE TRANSPORT LEDGER, `half`⟧ the LINEAR window gate implies the LANDED one
(`doorRowFloor_le_doorRowFloorL`). -/
theorem s15_sel''_L_half_landed {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hsel : S15Sel''_L Cg δ₀ Ct ρ x₀ Mfl R M) :
    (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
      ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 2 := by
  have hle : ((doorRowFloor M : ℕ) : ℝ) ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    exact_mod_cast doorRowFloor_le_doorRowFloorL hsel.hM
  linarith [hsel.half]

/-- **⟦THE SOCKET FORM AT THE LINEAR DOOR⟧** (`s15_gRows_const_at_socket_flat_doorL`) —
`FlatConsumers.s15_gRows_const_at_socket_gk_flat`'s twin at `AdoorL`: the const-pool gate
`GRowsZeroGate'''_L` at every base the LINEAR socket reaches, from the register's own `lvl`
line and the `𝒫`-side weakening of `gP1`, with the endpoint slot paid off the FLAT tower
conjunct (`flat_lambda_core_17`) exactly as on the landed road. -/
theorem s15_gRows_const_at_socket_flat_doorL {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseL R M H L q j A s) (hM : 1 ≤ M)
    (hρ0 : 0 < ρ) (_hρ1 : ρ ≤ 1)
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000)
    (hlvl : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        + (1 / 3) * Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ))
        + (-Real.log ρ)
      ≤ (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2)
    (hp2 : 27 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ) :
    GRowsZeroGate'''_L M (A + s) 0 (constPool ρ R.Hhi) := by
  have hbb : SocketBase R M H L q j A s := socketBase_of_socketBaseL hM hb
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hA : 0 < A := hbb.2.2.2.2.2.2.2.1
  have hAs : 0 < A + s := by omega
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hbb
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hllle : Real.log (Real.log (((A + s : ℕ)) : ℝ)) ≤ Real.log (((A + s : ℕ)) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hll := s12c_llX_ge hfl hbb
  have hcore := flat_lambda_core_17 hlam50
  have hendbud : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + (-Real.log ρ)
      ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h1 : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        ≤ 14 * Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := by linarith
    linarith [hcore, hll, hllle, hrho, h1]
  exact gRowsZeroGate'''_L_of_budget hM hAs hρ0 (by linarith) hp2 hendbud

/-- `⌊log₂(flatDoorM A)⌋ ≤ 2.3084·A` — the landed anchor at the flat design point grows only
LOGARITHMICALLY in the door modulus, hence only LINEARLY in `A`. -/
theorem flatDoorM_natLog_le {A : ℝ} (hA : 26 ≤ A) :
    ((Nat.log 2 (flatDoorM A) : ℕ) : ℝ) ≤ 2.3084 * A := by
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA
  have hpow : 2 ^ (Nat.log 2 (flatDoorM A)) ≤ flatDoorM A :=
    Nat.pow_log_le_self 2 (by omega)
  have hpowR : ((2 : ℝ)) ^ (Nat.log 2 (flatDoorM A)) ≤ ((flatDoorM A : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hMle := flatDoorM_le A
  have hE0 : (0 : ℝ) < Real.exp (3.2 * A / 2) := Real.exp_pos _
  have hle : ((2 : ℝ)) ^ (Nat.log 2 (flatDoorM A)) ≤ Real.exp (3.2 * A / 2) := by
    linarith
  have hpos : (0 : ℝ) < ((2 : ℝ)) ^ (Nat.log 2 (flatDoorM A)) := by positivity
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_pow, Real.log_exp] at hlog
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hn0 : (0 : ℝ) ≤ ((Nat.log 2 (flatDoorM A) : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [hlog, hl2, hn0]

/-- **⟦THE ROAD'S OWN LADDER STILL READS THE LANDED ANCHOR⟧**
(`flat_landed_ladder_break`) — at the flat design point the LANDED budget line
`14·λ₊ + 33 ≤ Adoor M·log 2` is FALSE for every `A ≥ 26`, by seven orders at the floor and
growing.  `S15SelLinear`'s acceptance repairs the REGISTER's copy of this line
(`AdoorL M = 2^36·M` in place of `2^36·(⌊log₂M⌋+1)`); but the road and the fuse read the same
budget through `calP (Adoor M) (s13GK K M)` — `M4Close.M4DoorGates_gk.hblocks`,
`S15Compose.s15_gate8_gk`, `S12ConstCompose.m4_closure_fuse_zero'_const_nonneg_gk`'s `gP1`
slot, and `M4WaveClosed.doorChiCoeff_gk`'s coefficient sequence itself.  So the re-fire needs
the LADDER re-cut, not only the register: `doorChiCoeff` at `(AdoorL M, s13GK K M)` and the
`M4Arith*`/`M4Assembly*`/`M4Closure*`/`S12ConstCompose`/`HloExportMR*` twins above it. -/
theorem flat_landed_ladder_break {A : ℝ} (hA : 26 ≤ A) :
    ¬ (14 * Real.exp (3.2 * A / 2) + 33
        ≤ ((Adoor (flatDoorM A) : ℕ) : ℝ) * Real.log 2) := by
  intro hcon
  have hn := flatDoorM_natLog_le hA
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl2p : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hAd : ((Adoor (flatDoorM A) : ℕ) : ℝ)
      = 68719476736 * (((Nat.log 2 (flatDoorM A) : ℕ) : ℝ) + 1) := by
    rw [Adoor]; push_cast; ring
  have hn0 : (0 : ℝ) ≤ ((Nat.log 2 (flatDoorM A) : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the left side⟧ `E ≥ 10^{17}·(1.6A − 40.6)`
  have h41 : (10 : ℝ) ^ 17 ≤ Real.exp (41.6) := by
    have h := flat_exp_half_ge (A := 26) le_rfl
    have hid : (3.2 : ℝ) * 26 / 2 = 41.6 := by norm_num
    rwa [hid] at h
  have hsplit : Real.exp (41.6) * Real.exp (3.2 * A / 2 - 41.6) = Real.exp (3.2 * A / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hlin : (3.2 * A / 2 - 41.6) + 1 ≤ Real.exp (3.2 * A / 2 - 41.6) :=
    Real.add_one_le_exp _
  have hstep : Real.exp (41.6) * ((3.2 * A / 2 - 41.6) + 1)
      ≤ Real.exp (3.2 * A / 2) := by
    rw [← hsplit]
    exact mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le
  have hbig : (10 : ℝ) ^ 17 * (1.6 * A - 40.6) ≤ Real.exp (3.2 * A / 2) := by
    nlinarith [hstep, h41, hA]
  rw [hAd] at hcon
  nlinarith [hcon, hbig, hn, hl2, hn0, hA]

end Salt.MR

end
