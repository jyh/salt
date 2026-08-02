/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ArithRhoLinear

/-!
# ⟦LADDER-L G3 §2⟧ — `M4SocketDischarge` + `S11CoefWS` at the LINEAR anchor
(`M4SocketLinear`)

⟦COMPOSE-FLAT-2⟧'s ladder re-cut, at the FINAL FUSE.  This page carries the `_L` twin family
of `M4SocketDischarge` (the socket discharged in its honest conditional form, the `T₀`-band
slot, the (α) base-cap satisfiability lemmas) and of `S11CoefWS` (the untwisted puncture pair
law and its witness) at `AdoorL M = 2^36·M`.

PURELY ADDITIVE: no landed declaration moves.

## ⟦THE ONE NEW STONE — WHY THE LANDED ARITHMETIC FRAME NEEDS NO TWIN⟧

`M4ArithPage.DoorArithFrame` is DOOR-FREE (its `anchor` reads `⌊log₂M⌋+1`, never the ladder),
so the twins below carry it verbatim.  What DOES move is the grade it prices: the level-1
summand `a2Level1 M` becomes `a2Level1_L M`.  §0 closes that gap once and for all with

  `a2Level1_L M ≤ a2Level1 M`   (`a2Level1_L_le_a2Level1`, `1 ≤ M`),

whose content is the re-cut's own trade, read as an inequality: raising the anchor from
`2^36·(⌊log₂M⌋+1)` to `2^36·M` multiplies the LOG of the numerator by `M/(⌊log₂M⌋+1)` — a
cost of `(1/3)·log(M/m)` — while the denominator's budget grows by `(1/12)·2^36·(M−m)·log 2`.
The second beats the first by eleven orders (`log(M/m) ≤ M−m` and `1/3 ≤ 2^36·log 2/12`).
Hence `a2DoorGrade_L ≤ a2DoorGrade` pointwise, and EVERY landed pricing transports down.

## ⟦THE SOCKET BASE⟧

The linear twins quantify over `ArithPageLinear.SocketBaseL` — the landed `SocketBase` with
the window-index floor at `doorRowFloorL M = 2^36·M²` — matching the linear suppliers.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — THE LEVEL-1 GRADE AT THE LINEAR ANCHOR IS SMALLER

The one stone the whole non-`ρ` arithmetic layer needs: the linear door's grade sits UNDER
the landed door's, so every landed pricing transports down with no new hypothesis. -/

/-- **THE `a2Level1` COMPARISON, AT ABSTRACT SCALES** (`level1_exp_step`) — the arithmetic core
of `a2Level1_L_le_a2Level1`, stated over plain reals so no ladder numeral enters the algebra:
`⅓·log(m·b·l) − (1/12)·b·l ≤ ⅓·log(m·a·l) − (1/12)·a·l` whenever `1 ≤ m`, `l > 0.693`,
`2^36 ≤ a ≤ b`. -/
theorem level1_exp_step {m a b l : ℝ} (hm : 1 ≤ m) (hl : (0.6931471803 : ℝ) < l)
    (ha : (68719476736 : ℝ) ≤ a) (hab : a ≤ b) :
    (1 / 3) * Real.log (m * b * l) - (1 / 12) * b * l
      ≤ (1 / 3) * Real.log (m * a * l) - (1 / 12) * a * l := by
  have hlpos : (0 : ℝ) < l := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  have hmpos : (0 : ℝ) < m := by linarith
  have hQpos : (0 : ℝ) < m * a * l := by positivity
  have hQLpos : (0 : ℝ) < m * b * l := by
    have hbpos : (0 : ℝ) < b := by linarith
    positivity
  have hratio : (m * b * l) / (m * a * l) - 1 = (b - a) / a := by
    field_simp
  have hdiv : Real.log (m * b * l) - Real.log (m * a * l) ≤ (b - a) / a := by
    have hsub : Real.log (m * b * l) - Real.log (m * a * l)
        = Real.log ((m * b * l) / (m * a * l)) := (Real.log_div hQLpos.ne' hQpos.ne').symm
    rw [hsub, ← hratio]
    exact Real.log_le_sub_one_of_pos (div_pos hQLpos hQpos)
  have hgap : (0 : ℝ) ≤ b - a := by linarith
  have hquot : (b - a) / a ≤ (b - a) / 68719476736 :=
    div_le_div_of_nonneg_left hgap (by norm_num) ha
  have hfinal : (1 / 3 : ℝ) * ((b - a) / 68719476736) ≤ (1 / 12 : ℝ) * (b - a) * l := by
    nlinarith [hgap, hl]
  linarith

/-- **⟦THE RE-CUT ONLY SHRINKS THE LEVEL-1 GRADE⟧** (`a2Level1_L_le_a2Level1`).

In closed form (`S15Compose.s15_a2Level1_exp`, `ArithPageLinear.s15_a2Level1_L_exp`) the two
grades are `exp(⅓·loglog 𝒬₁ − (1/12)·A·log 2)` at `A = Adoor M`, resp. `AdoorL M`.  Raising
the anchor costs `⅓·log(A_L/A) ≤ ⅓·(A_L − A)/2^36` in the numerator and buys
`(1/12)·(A_L − A)·log 2` in the denominator; the second beats the first by the factor
`2^36·log 2/4 ≈ 1.2·10¹⁰`. -/
theorem a2Level1_L_le_a2Level1 {M : ℕ} (hM : 1 ≤ M) : a2Level1_L M ≤ a2Level1 M := by
  rw [s15_a2Level1_L_exp hM, s15_a2Level1_exp hM]
  refine Real.exp_le_exp.mpr ?_
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have haR : (68719476736 : ℝ) ≤ ((Adoor M : ℕ) : ℝ) := by
    rw [Adoor_cast]
    have h0 : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) := Nat.cast_nonneg _
    linarith
  have hbaN : Adoor M ≤ AdoorL M := Adoor_le_AdoorL hM
  have hba : ((Adoor M : ℕ) : ℝ) ≤ ((AdoorL M : ℕ) : ℝ) := by exact_mod_cast hbaN
  have hLQ : Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)
      = (M : ℝ) * ((Adoor M : ℕ) : ℝ) * Real.log 2 := by
    rw [log_calQK, calE_one]; push_cast; ring
  have hLQL : Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)
      = (M : ℝ) * ((AdoorL M : ℕ) : ℝ) * Real.log 2 := log_calQK_doorL_one M
  rw [hLQ, hLQL]
  exact level1_exp_step hMR hlog2lo haR hba

/-- **⟦THE GRADE AT THE LINEAR DOOR SITS UNDER THE LANDED GRADE⟧** (`a2DoorGrade_L_le`).
Four of the five summands are byte-identical; the level-1 summand shrinks (§0). -/
theorem a2DoorGrade_L_le {M : ℕ} (hM : 1 ≤ M) (X h C₁ M₀ : ℝ) :
    a2DoorGrade_L M X h C₁ M₀ ≤ a2DoorGrade M X h C₁ M₀ := by
  rw [a2DoorGrade_L, a2DoorGrade]
  have := a2Level1_L_le_a2Level1 hM
  linarith

/-- **⟦THE LANDED PRICING, AT THE LINEAR DOOR⟧** (`a2DoorGrade_L_priced`) —
`M4ArithPage.a2DoorGrade_priced` transported through §0.  `DoorArithFrame` is DOOR-FREE, so
the hypothesis is the landed one verbatim. -/
theorem a2DoorGrade_L_priced {M H j : ℕ} {X C₁ M₀ K : ℝ}
    (hfr : DoorArithFrame M H j X C₁ M₀ K) :
    arcDen 12 H * a2DoorGrade_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ ≤ RSanDoor H := by
  have hL1 : 1 < Real.log (H : ℝ) := hfr.one_lt_logH
  have harc : (0 : ℝ) < arcDen 12 H := by
    rw [arcDen]; exact Real.rpow_pos_of_pos (by linarith) _
  refine le_trans (mul_le_mul_of_nonneg_left
    (a2DoorGrade_L_le hfr.Mpos X ((2 ^ j : ℕ) : ℝ) C₁ M₀) harc.le) ?_
  exact a2DoorGrade_priced hfr

/-- **⟦THE ARITHMETIC GATE, DISCHARGED AT THE LINEAR DOOR⟧** (`m4_arith_henv_L`) —
`M4ArithPage.m4_arith_henv` at `AdoorL`, over the LINEAR socket base. -/
theorem m4_arith_henv_L {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {K : ℝ}
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSanDoor H :=
  fun H L q j A s hb => a2DoorGrade_L_priced (harith H L q j A s hb)

/-- `m4_arith_henv_L`, at the lever (`a2DoorGrade_L_gk` is `a2DoorGrade_L`'s levered name). -/
theorem m4_arith_henv_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {Kar : ℝ}
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSanDoor H :=
  m4_arith_henv_L harith

/-! ## §1 — THE `_end` ASSEMBLY, AT THE GATED ARITHMETIC, AT THE LINEAR DOOR -/

/-- **⟦ITEM 11 AT THE DOOR'S ENVELOPE, `hrows`-FREE, AT THE LINEAR DOOR⟧**
(`m4_chiSummedFreeRow_of_doorArith_end_L`).  `M4SocketDischarge`'s §1 (:196) at `AdoorL`:
⟦D5⟧'s `_end` supplier composed with the GATED socket, exactly as landed. -/
theorem m4_chiSummedFreeRow_of_doorArith_end_L :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K : ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowEndBase_L M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                        (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end_L
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε cU bU t₁ K hM hb1 hc1 hframe hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_big_L
    (m4_chiSummedFreeRowBig_of_doorGradeGated_L hM (C₁ := C₁) (M₀ := M₀) ?_
      (m4_arith_henv_L harith))
  intro H L q j A s hb
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_L hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hslot R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb)
    (hband H L q j A s hb) hF.gP1 hF.gRows ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-! ## §2 — THE `T₀`-BAND SLOT, DISCHARGED, AT THE LINEAR DOOR -/

/-- **THE PER-BASE GATE BUNDLE OF THE `T₀`-BAND SUPPLIER, AT THE LINEAR DOOR**
(`DoorBandBase_L`).  Nine fields, names and order unchanged; only `gO1` and `gWin` read the
ladder, at `AdoorL`. -/
structure DoorBandBase_L (x₀ : ℕ) (C' Aexp : ℝ) (M Xd q : ℕ) (C₁ M₀ : ℝ) : Prop where
  /-- `400 ≤ X_d` — the supplier's base floor (it also gives `16 ≤ X_d`). -/
  X400 : (400 : ℝ) ≤ ((Xd : ℕ) : ℝ)
  /-- `1 ≤ C₁` — the band constant's normalisation. -/
  C₁_one : (1 : ℝ) ≤ C₁
  /-- `x₀ ≤ X_d` — the supplier's threshold, VISIBLE. -/
  x₀_le : x₀ ≤ Xd
  /-- `q ≤ (log X_d)^{10}` — the BASE-side conductor gate. -/
  qfit : (q : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (10 : ℕ)
  /-- The half-range mass gate, on `[X_d, 2X_d]`. -/
  gHalf : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    16 * Aexp * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)
  /-- The `O(1)`-range Rankin gate at the linear door's upper cutoff `Q₂`. -/
  gO1 : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    8 * Aexp * Real.log (Real.log (k : ℝ))
        * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.log (k : ℝ)
  /-- The covering-window gate at the linear `[P₁, Q₂]`. -/
  gWin : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    Real.exp (2 * Real.exp 1
        * (Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ))
            - Real.log (Real.log ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) + 25))
      ≤ (Real.log (k : ℝ)) ^ Aexp
  /-- The grade fit `8C' ≤ (log X_d)^{A − 1/2 + 1/1000}`. -/
  grade : 8 * C' ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
  /-- `cfb_t0band_supply_of_sup`'s own `hErr`. -/
  err : 4 * Real.log ((Xd : ℕ) : ℝ) ^ (-(1 : ℝ) / 2 + 1 / 1000)
    ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀)

/-- **⟦THE `hband` SLOT, MET, AT THE LINEAR DOOR⟧** (`m4_hband_at_door_slot_L`).
Composition: `door_window_bounds_L` ∘ `door_cover_L` ∘ `m4_hT0band_at_door_discharged_L`. -/
theorem m4_hband_at_door_slot_L (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp)
    (R : ChowlaRegime) (M : ℕ) (hM : 1 ≤ M) (C₁ M₀ : ℕ → ℝ) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      ((∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorBandBase_L x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) := by
  obtain ⟨hP4, hPQ⟩ := door_window_bounds_L M hM
  obtain ⟨C', x₀, hC'pos, hband⟩ := m4_hT0band_at_door_discharged_L hMmu Aexp hAexp
    (calP (AdoorL M) (3072 * M) 1) (calQK (AdoorL M) (3072 * M) M 2) hP4 hPQ
  obtain ⟨hcovP, hcovQ⟩ := door_cover_L M hM
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

/-! ## §3 — ⟦THE COMPOSITE⟧, AT THE LINEAR DOOR -/

/-- **⟦A4 — THE SOCKET, DISCHARGED IN ITS HONEST CONDITIONAL FORM, AT THE LINEAR DOOR⟧**
(`m4_socket_discharged_conditional_L`).  `M4SocketDischarge`'s §3 (:344) at `AdoorL`:
⟦item 11⟧, ⟦gate 4⟧ (at the LINEAR floor `doorRowFloorL M`) and the ceiling (door-FREE,
verbatim) at ONE hypothesis set. -/
theorem m4_socket_discharged_conditional_L :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
        1 ≤ M → 2 / 10 ^ 49 ≤ δ₀ →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
        (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowEndBase_L M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                        (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H))
          ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
              m4ChiRowGraded_L M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
          ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, Cp, hCt, hCp, hitem11⟩ := m4_chiSummedFreeRow_of_doorArith_end_L
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε cU bU t₁ K δ₀ hM hδ₀ hHreg hb1 hc1 hframe hbase hcap hband harith
  refine ⟨hitem11 R M C₁ M₀ ε cU bU t₁ K hM hb1 hc1 hframe hbase hcap hband harith,
    m4_arith_gate4_L M, ?_⟩
  intro H hlo hhi
  obtain ⟨hL0, hlam⟩ := hHreg H hlo hhi
  exact m4_arith_rs_ceiling_met hδ₀ hL0 hlam

/-! ## §4 — THE SAME, WITH THE `T₀`-BAND GONE, AT THE LINEAR DOOR -/

/-- **⟦A4 — THE SOCKET, DISCHARGED, `T₀`-BAND INCLUDED, AT THE LINEAR DOOR⟧**
(`m4_socket_discharged_bandfree_L`).  §3 with `hband` supplied by §2. -/
theorem m4_socket_discharged_bandfree_L (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
            2 / 10 ^ 49 ≤ δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowEndBase_L M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                            (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
            M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, Cp, hCt, hCp, hcomp⟩ := m4_socket_discharged_conditional_L
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ := m4_hband_at_door_slot_L hMmu Aexp hAexp R M hM C₁ M₀
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact hcomp R M C₁ M₀ ε cU bU t₁ K δ₀ hM hδ₀ hHreg hb1 hc1 hframe hbase hcap
    (hbandslot hbandbase) harith

/-! ## §5 — ⟦THE SATISFIABILITY OF `hframe`⟧ AT THE LINEAR DOOR

`socketBase_base_le_three_x` is door-FREE and applies verbatim through
`ArithPageLinear.socketBase_of_socketBaseL`. -/

/-- **⟦THE FRAME'S DECAYING CAP IS ANTITONE IN THE BASE, AT THE LINEAR DOOR⟧**
(`gP1_of_le_L`). -/
theorem gP1_of_le_L {M : ℕ} {Cs X Y : ℝ} (hX0 : 0 < X) (hX1 : (1 : ℝ) ≤ Real.log X)
    (hXY : X ≤ Y)
    (h : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ Real.log Y ^ (-(1 : ℝ) / 500)) :
    374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ Real.log X ^ (-(1 : ℝ) / 500) :=
  le_trans h
    (Real.rpow_le_rpow_of_nonpos (by linarith) (Real.log_le_log hX0 hXY) (by norm_num))

/-- **⟦`gP1` ON THE WHOLE CAPPED RANGE, FROM ONE INSTANCE, AT THE LINEAR DOOR⟧**
(`gP1_at_socketBase_L`).  The remaining obligation is
`loglog(3·R.x) + log(374784·C_s·e³) ≤ 500·A_L(M)·log 2` — an `M`-LOWER demand, now LINEAR in
`M` rather than logarithmic. -/
theorem gP1_at_socketBase_L {R : ChowlaRegime} {M H L q j A s : ℕ} {Cs : ℝ} (hM : 1 ≤ M)
    (hb : SocketBaseL R M H L q j A s)
    (hX1 : (1 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ))
    (htop : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ Real.log (3 * (R.x : ℝ)) ^ (-(1 : ℝ) / 500)) :
    374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ Real.log (((A + s : ℕ)) : ℝ) ^ (-(1 : ℝ) / 500) := by
  have hbb : SocketBase R M H L q j A s := socketBase_of_socketBaseL hM hb
  have hA : 0 < A := hbb.2.2.2.2.2.2.2.1
  have hX0 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by
    have hpos : 0 < A + s := by omega
    exact_mod_cast hpos
  exact gP1_of_le_L hX0 hX1 (socketBase_base_le_three_x hbb) htop

/-! ## §6 — `S11CoefWS` AT THE LINEAR DOOR

The UNTWISTED puncture pair law and its witness at `AdoorL`.
`memSCoeff_seamCoefWS_punct_gen_U` is `(Pseq, Qseq)`-GENERIC and is reused verbatim; only the
door instance moves. -/

/-- **`hcoefBand` AT THE LINEAR DOOR, UNTWISTED AND STRICT**
(`doorCoeffU_seamCoefWS_punct_H_L`) — `S11CoefWS.doorCoeffU_seamCoefWS_punct_H` (:80) at
`AdoorL`.  The separation is `DoorLinear.door_block_sep_at_L`. -/
theorem doorCoeffU_seamCoefWS_punct_H_L {M Xd : ℕ} {a : ℕ → ℂ} (hM : 1 ≤ M)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorCoeffU_L M n) :
    ∀ i ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (AdoorL M) (3072 * M) i) (calQK (AdoorL M) (3072 * M) M i) a
        (memSPunctCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 i
          liouvilleC) liouvilleC := by
  intro i hi
  exact memSCoeff_seamCoefWS_punct_gen_U (calP (AdoorL M) (3072 * M))
    (calQK (AdoorL M) (3072 * M) M) 2 i Xd a hi
    (fun p hp hlo hhi => door_block_sep_at_L hM hi hlo hhi) haH

/-- **⟦THE ONE WITNESSED-DATA FAMILY, WITNESSED, AT THE LINEAR DOOR⟧**
(`doorRowZeroBase_coefWS_witness_L`) — `M4RowsChiZero.DoorRowZeroBase`'s `coefWS` field at
`AdoorL`, `bU i := memSPunctCoeff 𝒫 𝒬K 2 i liouvilleC`, `cU := liouvilleC`, for EVERY `X_d`. -/
theorem doorRowZeroBase_coefWS_witness_L {M : ℕ} (Xd : ℕ) (hM : 1 ≤ M) :
    ∀ i ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (AdoorL M) (3072 * M) i) (calQK (AdoorL M) (3072 * M) M i)
        (winCutH Xd (doorCoeffU_L M))
        (memSPunctCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 i
          liouvilleC) liouvilleC :=
  doorCoeffU_seamCoefWS_punct_H_L hM (fun _ h1 h2 => winCutH_of_mem _ h1 h2)

/-- The linear witness's `b`-slot is `1`-bounded (`norm_doorPunctCoeffU_le_one_L`). -/
theorem norm_doorPunctCoeffU_le_one_L (M i n : ℕ) :
    ‖memSPunctCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 i
      liouvilleC n‖ ≤ 1 :=
  norm_memSPunctCoeff_le_one liouvilleC_norm_le_one _ _ 2 i n

/-! ## §GK — the `G`-lever twins -/

/-- **THE PER-BASE GATE BUNDLE OF THE `T₀`-BAND SUPPLIER, AT THE LINEAR DOOR AND THE LEVER**
(`DoorBandBase_L_gk`).  Nine fields; only `gO1`/`gWin` move, and both read level 2. -/
structure DoorBandBase_L_gk (K : ℕ) (x₀ : ℕ) (C' Aexp : ℝ) (M Xd q : ℕ) (C₁ M₀ : ℝ) :
    Prop where
  /-- `400 ≤ X_d` — the supplier's base floor. -/
  X400 : (400 : ℝ) ≤ ((Xd : ℕ) : ℝ)
  /-- `1 ≤ C₁` — the band constant's normalisation. -/
  C₁_one : (1 : ℝ) ≤ C₁
  /-- `x₀ ≤ X_d` — the supplier's threshold, VISIBLE. -/
  x₀_le : x₀ ≤ Xd
  /-- `q ≤ (log X_d)^{10}` — the BASE-side conductor gate. -/
  qfit : (q : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (10 : ℕ)
  /-- The half-range mass gate, on `[X_d, 2X_d]`. -/
  gHalf : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    16 * Aexp * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)
  /-- The `O(1)`-range Rankin gate at the levered linear cutoff `Q₂`. -/
  gO1 : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    8 * Aexp * Real.log (Real.log (k : ℝ))
        * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.log (k : ℝ)
  /-- The covering-window gate at the levered linear `[P₁, Q₂]`. -/
  gWin : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    Real.exp (2 * Real.exp 1
        * (Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ))
            - Real.log (Real.log ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) + 25))
      ≤ (Real.log (k : ℝ)) ^ Aexp
  /-- The grade fit `8C' ≤ (log X_d)^{A − 1/2 + 1/1000}`. -/
  grade : 8 * C' ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
  /-- `cfb_t0band_supply_of_sup`'s own `hErr`. -/
  err : 4 * Real.log ((Xd : ℕ) : ℝ) ^ (-(1 : ℝ) / 2 + 1 / 1000)
    ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀)

/-- **⟦THE `hband` SLOT, MET⟧ AT THE LINEAR DOOR AND THE LEVER**
(`m4_hband_at_door_slot_L_gk`). -/
theorem m4_hband_at_door_slot_L_gk (K : ℕ) (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp)
    (R : ChowlaRegime) (M : ℕ) (hM : 1 ≤ M) (C₁ M₀ : ℕ → ℝ) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      ((∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorBandBase_L_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
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

/-- `gP1_of_le_L` (:—), at the lever.  `𝒫₁` is LEVEL 1, hence K-INVARIANT. -/
theorem gP1_of_le_L_gk (K : ℕ) {M : ℕ} {Cs X Y : ℝ} (hX0 : 0 < X)
    (hX1 : (1 : ℝ) ≤ Real.log X) (hXY : X ≤ Y)
    (h : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ Real.log Y ^ (-(1 : ℝ) / 500)) :
    374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ Real.log X ^ (-(1 : ℝ) / 500) := by
  rw [calP_gk_one_eq] at h ⊢
  exact gP1_of_le_L hX0 hX1 hXY h

/-- `gP1_at_socketBase_L`, at the lever. -/
theorem gP1_at_socketBase_L_gk (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} {Cs : ℝ}
    (hM : 1 ≤ M) (hb : SocketBaseL R M H L q j A s)
    (hX1 : (1 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ))
    (htop : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ Real.log (3 * (R.x : ℝ)) ^ (-(1 : ℝ) / 500)) :
    374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ Real.log (((A + s : ℕ)) : ℝ) ^ (-(1 : ℝ) / 500) := by
  have hbb : SocketBase R M H L q j A s := socketBase_of_socketBaseL hM hb
  have hA : 0 < A := hbb.2.2.2.2.2.2.2.1
  have hX0 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by
    have hpos : 0 < A + s := by omega
    exact_mod_cast hpos
  exact gP1_of_le_L_gk K hX0 hX1 (socketBase_base_le_three_x hbb) htop

/-- `m4_chiSummedFreeRow_of_doorArith_end_L`, at the lever.  `hK : Klev ≤ 1.7·10⁸` is the
WIDE `K`-ceiling `m4_hrowsSlot_at_door_end_L_gk`'s frame side condition asks. -/
theorem m4_chiSummedFreeRow_of_doorArith_end_L_gk (Klev : ℕ) (hK : Klev ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K : ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L_gk Klev M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowEndBase_L_gk Klev M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK Klev M))
                        (calQK (AdoorL M) (s13GK Klev M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow_L_gk Klev R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end_L_gk Klev hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε cU bU t₁ K hM hb1 hc1 hframe hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_big_L_gk Klev
    (m4_chiSummedFreeRowBig_of_doorGradeGated_L_gk Klev hM (C₁ := C₁) (M₀ := M₀) ?_
      (m4_arith_henv_L_gk Klev harith))
  intro H L q j A s hb
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_L_gk Klev hM hF.X_exp hF.X_three hF.h_four hF.h_window
    hF.tann hF.ceil5 (hslot R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb)
    (hband H L q j A s hb) hF.gP1 hF.gRows ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-- `m4_socket_discharged_conditional_L`, at the lever. -/
theorem m4_socket_discharged_conditional_L_gk (Klev : ℕ) (hK : Klev ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
        1 ≤ M → 2 / 10 ^ 49 ≤ δ₀ →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
        (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L_gk Klev M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowEndBase_L_gk Klev M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK Klev M))
                        (calQK (AdoorL M) (s13GK Klev M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow_L_gk Klev R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H))
          ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
              m4ChiRowGraded_L M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
          ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, Cp, hCt, hCp, hitem11⟩ := m4_chiSummedFreeRow_of_doorArith_end_L_gk Klev hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε cU bU t₁ K δ₀ hM hδ₀ hHreg hb1 hc1 hframe hbase hcap hband harith
  refine ⟨hitem11 R M C₁ M₀ ε cU bU t₁ K hM hb1 hc1 hframe hbase hcap hband harith,
    m4_arith_gate4_L M, ?_⟩
  intro H hlo hhi
  obtain ⟨hL0, hlam⟩ := hHreg H hlo hhi
  exact m4_arith_rs_ceiling_met hδ₀ hL0 hlam

/-- `m4_socket_discharged_bandfree_L`, at the lever. -/
theorem m4_socket_discharged_bandfree_L_gk (Klev : ℕ) (hK : Klev ≤ 170000000)
    (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
            2 / 10 ^ 49 ≤ δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L_gk Klev M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowEndBase_L_gk Klev M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK Klev M))
                            (calQK (AdoorL M) (s13GK Klev M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s))
                          (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L_gk Klev x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
            M4ChiSummedFreeRow_L_gk Klev R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, Cp, hCt, hCp, hcomp⟩ := m4_socket_discharged_conditional_L_gk Klev hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ :=
    m4_hband_at_door_slot_L_gk Klev hMmu Aexp hAexp R M hM C₁ M₀
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact hcomp R M C₁ M₀ ε cU bU t₁ K δ₀ hM hδ₀ hHreg hb1 hc1 hframe hbase hcap
    (hbandslot hbandbase) harith

/-- `doorCoeffU_seamCoefWS_punct_H_L` (:—), at the lever. -/
theorem doorCoeffU_seamCoefWS_punct_H_L_gk (K : ℕ) {M Xd : ℕ} {a : ℕ → ℂ} (hM : 1 ≤ M)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorCoeffU_L_gk K M n) :
    ∀ i ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) i) (calQK (AdoorL M) (s13GK K M) M i) a
        (memSPunctCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 i
          liouvilleC) liouvilleC := by
  intro i hi
  exact memSCoeff_seamCoefWS_punct_gen_U (calP (AdoorL M) (s13GK K M))
    (calQK (AdoorL M) (s13GK K M) M) 2 i Xd a hi
    (fun p hp hlo hhi => door_block_sep_at_L_gk K hM hi hlo hhi) haH

/-- `doorRowZeroBase_coefWS_witness_L`, at the lever. -/
theorem doorRowZeroBase_coefWS_witness_L_gk (K : ℕ) {M : ℕ} (Xd : ℕ) (hM : 1 ≤ M) :
    ∀ i ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) i) (calQK (AdoorL M) (s13GK K M) M i)
        (winCutH Xd (doorCoeffU_L_gk K M))
        (memSPunctCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 i
          liouvilleC) liouvilleC :=
  doorCoeffU_seamCoefWS_punct_H_L_gk K hM (fun _ h1 h2 => winCutH_of_mem _ h1 h2)

/-- `norm_doorPunctCoeffU_le_one_L`, at the lever. -/
theorem norm_doorPunctCoeffU_le_one_L_gk (K : ℕ) (M i n : ℕ) :
    ‖memSPunctCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 i
      liouvilleC n‖ ≤ 1 :=
  norm_memSPunctCoeff_le_one liouvilleC_norm_le_one _ _ 2 i n

/-! ## §Xw — ⟦KWIDE-65⟧ THE WIDE-CEILING TWINS (this file)

Mechanical widening of the flat `hK` ceiling binders on the `L`-chain: the ceiling moves
INSIDE the internal `∀ M` as `≤ 170000000 * M`, so the raised lever `KlevF` can flow.
Statements and proofs are verbatim apart from that antecedent and the `_kwide` re-pointing.
The originals are untouched.
-/

/-- ⟦WIDE CEILING TWIN⟧ (`m4_chiSummedFreeRow_of_doorArith_end_L_gk_kwide`) —
`m4_chiSummedFreeRow_of_doorArith_end_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `Klev ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_chiSummedFreeRow_of_doorArith_end_L_gk_kwide (Klev : ℕ) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K : ℝ),
        1 ≤ M → Klev ≤ 170000000 * M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L_gk Klev M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowEndBase_L_gk Klev M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK Klev M))
                        (calQK (AdoorL M) (s13GK Klev M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow_L_gk Klev R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end_L_gk_kwide Klev
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε cU bU t₁ K hM hKw hb1 hc1 hframe hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_big_L_gk Klev
    (m4_chiSummedFreeRowBig_of_doorGradeGated_L_gk Klev hM (C₁ := C₁) (M₀ := M₀) ?_
      (m4_arith_henv_L_gk Klev harith))
  intro H L q j A s hb
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_L_gk Klev hM hF.X_exp hF.X_three hF.h_four hF.h_window
    hF.tann hF.ceil5 (hslot R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap H L q j A s hb)
    (hband H L q j A s hb) hF.gP1 hF.gRows ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-- ⟦WIDE CEILING TWIN⟧ (`m4_socket_discharged_conditional_L_gk_kwide`) —
`m4_socket_discharged_conditional_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `Klev ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_socket_discharged_conditional_L_gk_kwide (Klev : ℕ) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
        1 ≤ M → Klev ≤ 170000000 * M → 2 / 10 ^ 49 ≤ δ₀ →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
        (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L_gk Klev M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowEndBase_L_gk Klev M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK Klev M))
                        (calQK (AdoorL M) (s13GK Klev M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow_L_gk Klev R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H))
          ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
              m4ChiRowGraded_L M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
          ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, Cp, hCt, hCp, hitem11⟩ := m4_chiSummedFreeRow_of_doorArith_end_L_gk_kwide Klev
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε cU bU t₁ K δ₀ hM hKw hδ₀ hHreg hb1 hc1 hframe hbase hcap hband harith
  refine ⟨hitem11 R M C₁ M₀ ε cU bU t₁ K hM hKw hb1 hc1 hframe hbase hcap hband harith,
    m4_arith_gate4_L M, ?_⟩
  intro H hlo hhi
  obtain ⟨hL0, hlam⟩ := hHreg H hlo hhi
  exact m4_arith_rs_ceiling_met hδ₀ hL0 hlam

/-- ⟦WIDE CEILING TWIN⟧ (`m4_socket_discharged_bandfree_L_gk_kwide`) —
`m4_socket_discharged_bandfree_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `Klev ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_socket_discharged_bandfree_L_gk_kwide (Klev : ℕ)
    (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M → Klev ≤ 170000000 * M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
            2 / 10 ^ 49 ≤ δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L_gk Klev M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowEndBase_L_gk Klev M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK Klev M))
                            (calQK (AdoorL M) (s13GK Klev M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s))
                          (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L_gk Klev x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
            M4ChiSummedFreeRow_L_gk Klev R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, Cp, hCt, hCp, hcomp⟩ := m4_socket_discharged_conditional_L_gk_kwide Klev
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ hM hKw
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ :=
    m4_hband_at_door_slot_L_gk Klev hMmu Aexp hAexp R M hM C₁ M₀
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact hcomp R M C₁ M₀ ε cU bU t₁ K δ₀ hM hKw hδ₀ hHreg hb1 hc1 hframe hbase hcap
    (hbandslot hbandbase) harith

end Salt.MR

end
