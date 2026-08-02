/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4CapWireLinear

/-!
# ⟦LADDER-L G3 §6⟧ — `M4ClosureRepair` at the LINEAR anchor (`M4ClosureRepairLinear`)

⟦COMPOSE-FLAT-2⟧'s ladder re-cut, at the CLOSURE REPAIR.  The `_L` twin family of the four
repairs (⟦D1⟧ the decaying pool, ⟦D3⟧ the free density, ⟦D4⟧ the gated `henv`, ⟦R5b⟧ the
constant pool) and of both fuses, at `AdoorL M = 2^36·M`.

⟦WHAT KEEPS ITS LANDED NAME⟧ `decayPool`, `constPool` and their positivity/monotonicity
lemmas, `eps_pool_at_decayPool`, `band_pool_at_decayPool`, `price_at_decayPool`,
`price_at_constPool`, `eps_pool_of_threshold`, `band_pool_of_threshold`, `loglog_le_of_le`,
`ege_line_gate`, `theta293_sub_lower`, `ege_line_of_loglog` and `DoorBaseFrame` are ALL
door-FREE and are consumed verbatim — no new root definition is minted here.
The four-slot gate at the linear door and its budget discharge are `ArithPageLinear`'s,
already landed; only the `_gk` generation of that family is added below.

The socket base is `ArithPageLinear.SocketBaseL` throughout.

PURELY ADDITIVE: no landed declaration moves.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-- `M4ClosureRepair.r5_one_le_log_of_three_le` (:113), re-proved (the landed lemma is
`private`).  Ladder-BLIND. -/
private lemma r5L_one_le_log_of_three_le {Xd : ℕ} (h : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ)) :
    (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
  have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) h
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ (3 : ℝ))
    rwa [Real.log_exp] at this
  linarith


/-- **⟦THE PRICE WRAPPER, PER SOCKET BASE⟧** (`price_at_decayPool_socket_L`) — exactly the
`hprice` binder of `M4ArithPool.m4_arith_henv_rho_pool_L` at `π₀ := decayPool`, DISCHARGED from
`DoorArithFrameRho_L` alone.  Nothing else is asked: `ρ > 0`, `ρ ≤ 1`, `λ ≥ 0` and `1 < log X_d`
are all frame fields (`rho_pos`, `rho_le_one`, `Hfloor`, `one_lt_logX`). -/
theorem price_at_decayPool_socket_L {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {K ρ : ℝ}
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      188133 * decayPool (A + s) * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2 := by
  intro H L q j A s hb
  have hfr := harith H L q j A s hb
  have hlam : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by
    have := hfr.Hfloor; linarith
  exact price_at_decayPool hfr.rho_pos hfr.rho_le_one hlam hfr.one_lt_logX hfr.armWeak

/-- **⟦D1 — THE FRAME AT THE DECAYING POOL⟧** (`doorFuseFrame_pool'_of_gates_decay_L`) — the
twin of `M4ArithPrime.doorFuseFrame_pool'_of_gates` at `π₀ := decayPool X_d`, with
`hone : 1 ≤ π₀` GONE.  What replaces it:

* `hε : ε ≤ 0` — the `𝒰`-leg exponent, pinned at or below `0` (the examiner's `ε := 0` is the
  intended instance);
* `hL4096 : 4096 ≤ (log X_d)^{1−1/500−θ₂₉₃}` — a base-LOWER threshold, at the CORRECTED
  exponent.

Every remaining demand is base-free or base-LOWER; no field caps the base and no field is
in tension with the summand-3 price. -/
theorem doorFuseFrame_pool'_of_gates_decay_L {M Xd j : ℕ} {Cs ε : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ decayPool Xd)
    (hg : GRowsZeroGate''_L M Xd (decayPool Xd))
    (hε : ε ≤ 0)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) :
    DoorFuseFrame_pool'_L M Xd j Cs 0 ε (decayPool Xd) where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate''_L hM hXd hg
  eps_pool := eps_pool_at_decayPool (r5L_one_le_log_of_three_le hb.X_three) hε
  band_pool := band_pool_at_decayPool
    (by have := r5L_one_le_log_of_three_le hb.X_three; linarith) hL4096

/-- At `C_cc = 0` and a nonnegative pool the four-way gate is STRICTLY stronger than the
landed three-way one — the shares only shrank. -/
theorem gRowsZeroGate''_of_gate'''_L {M Xd : ℕ} {π₀ : ℝ} (hπ : 0 ≤ π₀)
    (hg : GRowsZeroGate'''_L M Xd 0 π₀) : GRowsZeroGate''_L M Xd π₀ where
  level1 := by have := hg.level1; linarith
  endpt := by have := hg.endpt; linarith
  p2 := by have := hg.p2; linarith

/-- **⟦THE RESIDUAL AT FREE DENSITY⟧** (`gRows_zero_of_gate'''_L`):

  `5760·(a2RowsSum'_L M X_d + C_cc·(2/M)) ≤ π₀`

from `GRowsZeroGate'''_L` alone.  `M4ArithPrime.gRows_zero_of_gate''_L`'s proof with the fourth
summand carried instead of killed. -/
theorem gRows_zero_of_gate'''_L {M Xd : ℕ} {Ccc π₀ : ℝ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hg : GRowsZeroGate'''_L M Xd Ccc π₀) :
    5760 * (a2RowsSum'_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ := by
  rw [a2RowsSum'_door_decomp_L hM hXd]
  have hid : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 24 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ))
        + Ccc * (2 / (M : ℝ)))
      = 14400 * Real.exp 1 ^ 2 * a2Level1_L M
        + 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ))
        + 138240 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ))
        + 5760 * Ccc * (2 / (M : ℝ)) := by ring
  rw [hid]
  linarith [hg.level1, hg.endpt, hg.p2, hg.dens]

/-- **⟦D3 — THE FRAME AT FREE DENSITY⟧** (`doorFuseFrame_pool'_of_gates_cc_L`) —
`M4ArithPrime.doorFuseFrame_pool'_of_gates` with `C_cc` free instead of pinned at `0`.  The
pool-side fields are unchanged (`hone` + `hL4096` at the landed exponent). -/
theorem doorFuseFrame_pool'_of_gates_cc_L {M Xd j : ℕ} {Cs Ccc ε π₀ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hg : GRowsZeroGate'''_L M Xd Ccc π₀)
    (hone : (1 : ℝ) ≤ π₀)
    (hε : ε ≤ theta293)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)) :
    DoorFuseFrame_pool'_L M Xd j Cs Ccc ε π₀ where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate'''_L hM hXd hg
  eps_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := r5L_one_le_log_of_three_le hb.X_three
    have hle : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      simpa using this
    linarith
  band_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := r5L_one_le_log_of_three_le hb.X_three
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
    have habs : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) := by
      have hsp : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          = (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)
            * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) := by
        rw [← Real.rpow_add hL0]; norm_num
      rw [hsp]
      exact mul_le_mul_of_nonneg_right hL4096 (le_of_lt (Real.rpow_pos_of_pos hL0 _))
    have hone' : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      simpa using this
    linarith

/-- **⟦D1 × D3 — THE FRAME AT FREE DENSITY AND THE DECAYING POOL⟧**
(`doorFuseFrame_pool'_of_gates_cc_decay_L`) — the two repairs composed: `C_cc` free (so both R4
exits can consume it) AND `π₀ := decayPool X_d` (so the summand-3 price is payable).  This is
the frame supplier §5's fuse actually uses. -/
theorem doorFuseFrame_pool'_of_gates_cc_decay_L {M Xd j : ℕ} {Cs Ccc ε : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ decayPool Xd)
    (hg : GRowsZeroGate'''_L M Xd Ccc (decayPool Xd))
    (hε : ε ≤ 0)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) :
    DoorFuseFrame_pool'_L M Xd j Cs Ccc ε (decayPool Xd) where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate'''_L hM hXd hg
  eps_pool := eps_pool_at_decayPool (r5L_one_le_log_of_three_le hb.X_three) hε
  band_pool := band_pool_at_decayPool
    (by have := r5L_one_le_log_of_three_le hb.X_three; linarith) hL4096

/-- **⟦D3 — THE JOIN EXIT AT FREE DENSITY⟧** (`m4_chiSummedFreeRow_of_doorAssembly_join_cc_L`) —
`M4ArithPrime.m4_chiSummedFreeRow_of_doorAssembly_join` with the density constant FREE.  The
`hrows` binder correspondingly reads `a2Mrow'_L (Cs …) (Ccc …)` rather than `a2Mrow'_L (Cs …) 0`,
which is what both R4 `hrows` suppliers actually produce. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_join_cc_L {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j)
    (hgP1 : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      374784 * Cs (A + s) * Real.exp 3
          * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀ (A + s))
    (hgRows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      GRowsZeroGate'''_L M (A + s) (Ccc (A + s)) (π₀ (A + s)))
    (hone : ∀ A : ℕ, (1 : ℝ) ≤ π₀ A)
    (heps : ∀ A : ℕ, ε A ≤ theta293)
    (hL4096 : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 250))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
          ≤ a2Mrow'_L (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_L (Cs := Cs) (Ccc := Ccc) (C₁ := C₁)
    (M₀ := M₀) (ε := ε) (π₀ := π₀) hM ?_ hrows hband (fun A => le_trans zero_le_one (hone A))
    henv
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_cc_L (hbase H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (hone (A + s)) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-- **⟦D4 — THE ASSEMBLY, GATED⟧** (`m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_L`) —
`M4AssemblyPrime.m4_chiSummedFreeRow_of_doorAssembly_pool'_L` with the `henv` binder
`SocketBaseL`-GATED.  Proof template:
`M4ArithPool.m4_chiSummedFreeRow_of_doorArithRho_pool`, with the primed fuse
`m4_chiFreeRowSq_sum_at_door_pool'_L` in place of the landed one. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_L {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_pool'_L M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
          ≤ a2Mrow'_L (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (henv : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) := by
  refine m4_chiSummedFreeRow_of_big_L
    (m4_chiSummedFreeRowBig_of_doorGradeGated_pool_L hM (C₁ := C₁) (M₀ := M₀) (π₀ := π₀) hpool ?_
      henv)
  intro H L q j A s hb
  obtain ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  haveI : NeZero q := ⟨hq.ne'⟩
  have hbb : SocketBaseL R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hbb
  exact m4_chiFreeRowSq_sum_at_door_pool'_L hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hbb) (hband H L q j A s hbb) hF.gP1 hF.gRows hF.eps_pool
    hF.band_pool

/-- **⟦D4 — ITEM 11 AT THE `end'` CHAIN, GATED⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated_L`) — the twin of
`M4RowsChiEndPrime.m4_chiSummedFreeRow_of_doorAssembly_pool_end'` whose `henv` binder is
`SocketBaseL`-gated, so that `M4ArithPool.m4_arith_henv_rho_pool_L` can fill it.  Every other
binder is that exit's VERBATIM. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated_L :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_pool'_L M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowEndBase_L M (A + s) j cU bU) →
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
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end'_L
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_L (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv

/-- **⟦D4 — ITEM 11 AT THE `zero'` CHAIN, GATED⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_L`) — the twin of
`M4RowsChiZeroPrime.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'` at the gated `henv`. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_L :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_pool'_L M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowZeroBase_L M (A + s) j cU bU) →
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
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'_L
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_L (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot Cp hCp.le R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv

/-- **⟦THE FUSE, `end'` CHAIN⟧** (`m4_closure_fuse_end'_L`) — ⟦item 11⟧ at `RSanDoorRho ρ`,
from: the six base-side frame fields, the `𝒯`-leg gate, the FOUR-slot `gRows` gate, the
`ε ≤ 0` pin, the corrected `4096`-threshold, the `end'` chain's per-base bundle, the A3
capstone family, the band supplier, and the `ρ`-arithmetic frame.

**NO `hone`.  NO `hprice`.**  The pool is `decayPool` and the ARM pays. -/
theorem m4_closure_fuse_end'_L :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (K ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
            ≤ decayPool (A + s)) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          GRowsZeroGate'''_L M (A + s) Cp (decayPool (A + s))) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowEndBase_L M (A + s) j cU bU) →
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
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hexit⟩ := m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated_L
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε K ρ cU bU t₁ hM hb1 hc1 hbf hgP1 hgRows heps hL4096 hbase hcap hband harith
  refine hexit R M C₁ M₀ ε decayPool (fun _ H => RSanDoorRho ρ H) cU bU t₁ hM hb1 hc1
    ?_ hbase hcap hband decayPool_nonneg
    (m4_arith_henv_rho_pool_L decayPool_nonneg harith (price_at_decayPool_socket_L harith))
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_cc_decay_L (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-- **⟦THE FUSE, `zero'` CHAIN⟧** (`m4_closure_fuse_zero'_L`) — the same, at
`M4RowsChiZeroPrime`'s density-free chain: `C_p` is a FREE positive parameter and the
per-base bundle is the six-field `DoorRowZeroBase_L`. -/
theorem m4_closure_fuse_zero'_L :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (K ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
            ≤ decayPool (A + s)) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          GRowsZeroGate'''_L M (A + s) Cp (decayPool (A + s))) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowZeroBase_L M (A + s) j cU bU) →
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
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hexit⟩ := m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_L
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε K ρ cU bU t₁ hM hb1 hc1 hbf hgP1 hgRows heps hL4096 hbase hcap
    hband harith
  refine hexit Cp hCp R M C₁ M₀ ε decayPool (fun _ H => RSanDoorRho ρ H) cU bU t₁ hM hb1 hc1
    ?_ hbase hcap hband decayPool_nonneg
    (m4_arith_henv_rho_pool_L decayPool_nonneg harith (price_at_decayPool_socket_L harith))
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_cc_decay_L (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-- **⟦THE PRICE WRAPPER, PER SOCKET BASE⟧** (`price_at_constPool_socket_L`) — the twin of
`price_at_decayPool_socket_L`: exactly the `hprice` binder of `M4ArithPool.m4_arith_henv_rho_pool_L`
at `π₀ := fun _ => constPool ρ R.Hhi`.  What discharges it is NOT the ARM but the socket's own
window field `H ≤ R.Hhi` (plus `R.Hlo ≤ H` and the regime's `hHlo_floor` for positivity, and
`DoorArithFrameRho_L.rho_pos`/`.one_lt_logH` for the two scalar side conditions). -/
theorem price_at_constPool_socket_L {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {K ρ : ℝ}
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      188133 * constPool ρ R.Hhi * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2 := by
  intro H L q j A s hb
  have hfr := harith H L q j A s hb
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  have hHpos : 0 < H := by have := R.hHlo_floor; omega
  have hlogH : (0 : ℝ) < Real.log (H : ℝ) := by have := hfr.one_lt_logH; linarith
  exact price_at_constPool hfr.rho_pos (loglog_le_of_le hHpos hlogH hhi)

/-- **⟦THE ARITHMETIC GATE AT THE CONSTANT POOL⟧** (`m4_arith_henv_constPool_L`) — the composed
witness that the wrapper fills `m4_arith_henv_rho_pool_L` verbatim: `henv` at
`RSbig j H := RSanDoorRho ρ H`, with the pool a CONSTANT in the base. -/
theorem m4_arith_henv_constPool_L {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {K ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (constPool ρ R.Hhi)
        ≤ RSanDoorRho ρ H :=
  m4_arith_henv_rho_pool_L (π₀ := fun _ => constPool ρ R.Hhi)
    (fun _ => constPool_nonneg hρ) harith (price_at_constPool_socket_L harith)

/-- **⟦R5b — THE FRAME AT THE CONSTANT POOL⟧** (`doorFuseFrame_pool'_of_gates_const_L`) — the
twin of `doorFuseFrame_pool'_of_gates_decay_L` (and of its `C_cc`-free composition
`doorFuseFrame_pool'_of_gates_cc_decay_L`, whose four-slot `gRows` gate it carries) at
`π₀ := constPool ρ H₊`.

⟦THE HYPOTHESIS SET, AGAINST THE DECAY TWIN'S⟧ field for field the same SHAPE — `hb`, `hgP1`,
`hg`, `hε`, `hM`, `hXd` and one `4096`-threshold — with two differences, both in the same
direction:

* `hgP1` and `hg` are now BASE-FREE on the right (`constPool` carries no `X_d`), where the
  decay twin's were base UPPER caps;
* the single decay threshold `hL4096 : 4096 ≤ (log X_d)^{1−1/500−θ₂₉₃}` splits into TWO
  base-LOWER thresholds, `heps293` and `hband4096`, because at a constant pool the `𝒰`-leg no
  longer discharges by rpow-exponent monotonicity into `π₀` itself.

Nothing else changes; `ε ≤ 0` is reused verbatim. -/
theorem doorFuseFrame_pool'_of_gates_const_L {M Xd j Hhi : ℕ} {Cs Ccc ε ρ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ constPool ρ Hhi)
    (hg : GRowsZeroGate'''_L M Xd Ccc (constPool ρ Hhi))
    (hε : ε ≤ 0)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (heps293 : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293) ≤ constPool ρ Hhi)
    (hband4096 : (4096 : ℝ)
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500) * constPool ρ Hhi) :
    DoorFuseFrame_pool'_L M Xd j Cs Ccc ε (constPool ρ Hhi) where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate'''_L hM hXd hg
  eps_pool := eps_pool_of_threshold (r5L_one_le_log_of_three_le hb.X_three) hε heps293
  band_pool := band_pool_of_threshold
    (by have := r5L_one_le_log_of_three_le hb.X_three; linarith) hband4096

/-- **⟦THE FUSE AT `constPool`, `end'` CHAIN⟧** (`m4_closure_fuse_end'_const_L`) — ⟦item 11⟧ at
`RSanDoorRho ρ`, at the CONSTANT pool `π₀ := fun _ => constPool ρ R.Hhi`.  The twin of
`m4_closure_fuse_end'_L`, binder for binder, with `hρ` added and `hL4096` split into the two
base-LOWER thresholds `heps293`/`hband4096`. -/
theorem m4_closure_fuse_end'_const_L :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (K ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 ≤ ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          GRowsZeroGate'''_L M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowEndBase_L M (A + s) j cU bU) →
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
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hexit⟩ := m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated_L
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε K ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows heps heps293 hband4096 hbase
    hcap hband harith
  refine hexit R M C₁ M₀ ε (fun _ => constPool ρ R.Hhi) (fun _ H => RSanDoorRho ρ H) cU bU t₁
    hM hb1 hc1 ?_ hbase hcap hband (fun _ => constPool_nonneg hρ)
    (m4_arith_henv_constPool_L hρ harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_L (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (heps293 H L q j A s hb)
    (hband4096 H L q j A s hb)

/-- **⟦THE FUSE AT `constPool`, `zero'` CHAIN⟧** (`m4_closure_fuse_zero'_const_L`) — the same at
`M4RowsChiZeroPrime`'s density-free chain: `C_p` is a FREE positive parameter and the per-base
bundle is the six-field `DoorRowZeroBase_L`. -/
theorem m4_closure_fuse_zero'_const_L :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (K ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 ≤ ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          GRowsZeroGate'''_L M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowZeroBase_L M (A + s) j cU bU) →
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
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hexit⟩ := m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_L
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε K ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows heps heps293 hband4096
    hbase hcap hband harith
  refine hexit Cp hCp R M C₁ M₀ ε (fun _ => constPool ρ R.Hhi) (fun _ H => RSanDoorRho ρ H)
    cU bU t₁ hM hb1 hc1 ?_ hbase hcap hband (fun _ => constPool_nonneg hρ)
    (m4_arith_henv_constPool_L hρ harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_L (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (heps293 H L q j A s hb)
    (hband4096 H L q j A s hb)

/-! ## §GK — the `G`-lever twins, at the LINEAR door -/

/-- `doorFuseFrame_pool'_of_gates_decay_L` (:234), at the lever. -/
theorem doorFuseFrame_pool'_of_gates_decay_L_gk (K : ℕ) {M Xd j : ℕ} {Cs ε : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ decayPool Xd)
    (hg : GRowsZeroGate''_L_gk K M Xd (decayPool Xd))
    (hε : ε ≤ 0)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) :
    DoorFuseFrame_pool'_L_gk K M Xd j Cs 0 ε (decayPool Xd) where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate''_L_gk K hM hXd hg
  eps_pool := eps_pool_at_decayPool (r5L_one_le_log_of_three_le hb.X_three) hε
  band_pool := band_pool_at_decayPool
    (by have := r5L_one_le_log_of_three_le hb.X_three; linarith) hL4096

/-- `GRowsZeroGate'''_L` (:278), at the lever.  Only the `p²` field moves. -/
structure GRowsZeroGate'''_L_gk (K : ℕ) (M Xd : ℕ) (Ccc π₀ : ℝ) : Prop where
  /-- ⟦THE LEVEL-1 SLOT⟧ base-free. -/
  level1 : 14400 * Real.exp 1 ^ 2 * a2Level1_L M ≤ 1 / 4 * π₀
  /-- ⟦THE ENDPOINT SLOT⟧ the only base-reading slot, and base-LOWER. -/
  endpt : 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ)) ≤ 1 / 4 * π₀
  /-- ⟦THE `p²` SLOT, R1⟧ `X_d`-FREE, at the levered ladder. -/
  p2 : 138240 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
        + 1 / ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ))
      ≤ 1 / 4 * π₀
  /-- **⟦THE DENSITY SLOT — D3⟧** the debit `GRowsZeroGate''_L_gk` pinned to `0`. -/
  dens : 5760 * Ccc * (2 / (M : ℝ)) ≤ 1 / 4 * π₀

/-- `gRowsZeroGate''_of_gate'''_L` (:292), at the lever. -/
theorem gRowsZeroGate''_of_gate'''_L_gk {K M Xd : ℕ} {π₀ : ℝ} (hπ : 0 ≤ π₀)
    (hg : GRowsZeroGate'''_L_gk K M Xd 0 π₀) : GRowsZeroGate''_L_gk K M Xd π₀ where
  level1 := by have := hg.level1; linarith
  endpt := by have := hg.endpt; linarith
  p2 := by have := hg.p2; linarith

/-- `gRows_zero_of_gate'''_L` (:304), at the lever. -/
theorem gRows_zero_of_gate'''_L_gk (K : ℕ) {M Xd : ℕ} {Ccc π₀ : ℝ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hg : GRowsZeroGate'''_L_gk K M Xd Ccc π₀) :
    5760 * (a2RowsSum'_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ := by
  rw [a2RowsSum'_door_decomp_L_gk K hM hXd]
  have hid : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 24 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ))
        + Ccc * (2 / (M : ℝ)))
      = 14400 * Real.exp 1 ^ 2 * a2Level1_L M
        + 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ))
        + 138240 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ))
        + 5760 * Ccc * (2 / (M : ℝ)) := by ring
  rw [hid]
  linarith [hg.level1, hg.endpt, hg.p2, hg.dens]

/-- `doorFuseFrame_pool'_of_gates_cc_L` (:324), at the lever. -/
theorem doorFuseFrame_pool'_of_gates_cc_L_gk (K : ℕ) {M Xd j : ℕ} {Cs Ccc ε π₀ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hg : GRowsZeroGate'''_L_gk K M Xd Ccc π₀)
    (hone : (1 : ℝ) ≤ π₀)
    (hε : ε ≤ theta293)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)) :
    DoorFuseFrame_pool'_L_gk K M Xd j Cs Ccc ε π₀ where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate'''_L_gk K hM hXd hg
  eps_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := r5L_one_le_log_of_three_le hb.X_three
    have hle : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      simpa using this
    linarith
  band_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := r5L_one_le_log_of_three_le hb.X_three
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
    have habs : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) := by
      have hsp : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          = (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)
            * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) := by
        rw [← Real.rpow_add hL0]; norm_num
      rw [hsp]
      exact mul_le_mul_of_nonneg_right hL4096 (le_of_lt (Real.rpow_pos_of_pos hL0 _))
    have hone' : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      simpa using this
    linarith

/-- `doorFuseFrame_pool'_of_gates_cc_decay_L` (:371), at the lever. -/
theorem doorFuseFrame_pool'_of_gates_cc_decay_L_gk (K : ℕ) {M Xd j : ℕ} {Cs Ccc ε : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ decayPool Xd)
    (hg : GRowsZeroGate'''_L_gk K M Xd Ccc (decayPool Xd))
    (hε : ε ≤ 0)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) :
    DoorFuseFrame_pool'_L_gk K M Xd j Cs Ccc ε (decayPool Xd) where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate'''_L_gk K hM hXd hg
  eps_pool := eps_pool_at_decayPool (r5L_one_le_log_of_three_le hb.X_three) hε
  band_pool := band_pool_at_decayPool
    (by have := r5L_one_le_log_of_three_le hb.X_three; linarith) hL4096

/-- `m4_chiSummedFreeRow_of_doorAssembly_join_cc_L` (:396), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_join_cc_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j)
    (hgP1 : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      374784 * Cs (A + s) * Real.exp 3
          * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ (A + s))
    (hgRows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      GRowsZeroGate'''_L_gk K M (A + s) (Ccc (A + s)) (π₀ (A + s)))
    (hone : ∀ A : ℕ, (1 : ℝ) ≤ π₀ A)
    (heps : ∀ A : ℕ, ε A ≤ theta293)
    (hL4096 : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 250))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow'_L_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_L_gk K (Cs := Cs) (Ccc := Ccc) (C₁ := C₁)
    (M₀ := M₀) (ε := ε) (π₀ := π₀) hM ?_ hrows hband
    (fun A => le_trans zero_le_one (hone A)) henv
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_cc_L_gk K (hbase H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (hone (A + s)) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-- `m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_L` (:455), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_pool'_L_gk K M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow'_L_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (henv : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  refine m4_chiSummedFreeRow_of_big_L_gk K
    (m4_chiSummedFreeRowBig_of_doorGradeGated_pool_L_gk K hM (C₁ := C₁) (M₀ := M₀) (π₀ := π₀)
      hpool ?_ henv)
  intro H L q j A s hb
  obtain ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  haveI : NeZero q := ⟨hq.ne'⟩
  have hbb : SocketBaseL R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hbb
  exact m4_chiFreeRowSq_sum_at_door_pool'_L_gk K hM hF.X_exp hF.X_three hF.h_four hF.h_window
    hF.tann hF.ceil5 (hrows H L q j A s hbb) (hband H L q j A s hbb) hF.gP1 hF.gRows
    hF.eps_pool hF.band_pool

/-- `m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated_L` (:498), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated_L_gk (K : ℕ)
    (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_pool'_L_gk K M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowEndBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
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
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end'_L_gk K hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_L_gk K (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv

/-- `m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_L` (:544), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_L_gk (K : ℕ)
    (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_pool'_L_gk K M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
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
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'_L_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_L_gk K (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot Cp hCp.le R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv

/-- `m4_closure_fuse_end'_L` (:698), at the lever. -/
theorem m4_closure_fuse_end'_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kar ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ decayPool (A + s)) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          GRowsZeroGate'''_L_gk K M (A + s) Cp (decayPool (A + s))) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowEndBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
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
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hexit⟩ :=
    m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated_L_gk K hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε Kar ρ cU bU t₁ hM hb1 hc1 hbf hgP1 hgRows heps hL4096 hbase hcap hband
    harith
  refine hexit R M C₁ M₀ ε decayPool (fun _ H => RSanDoorRho ρ H) cU bU t₁ hM hb1 hc1
    ?_ hbase hcap hband decayPool_nonneg
    (m4_arith_henv_rho_pool_L_gk K decayPool_nonneg harith (price_at_decayPool_socket_L harith))
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_cc_decay_L_gk K (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-- `m4_closure_fuse_zero'_L` (:754), at the lever. -/
theorem m4_closure_fuse_zero'_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kar ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ decayPool (A + s)) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          GRowsZeroGate'''_L_gk K M (A + s) Cp (decayPool (A + s))) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
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
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hexit⟩ := m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_L_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε Kar ρ cU bU t₁ hM hb1 hc1 hbf hgP1 hgRows heps hL4096 hbase hcap
    hband harith
  refine hexit Cp hCp R M C₁ M₀ ε decayPool (fun _ H => RSanDoorRho ρ H) cU bU t₁ hM hb1 hc1
    ?_ hbase hcap hband decayPool_nonneg
    (m4_arith_henv_rho_pool_L_gk K decayPool_nonneg harith (price_at_decayPool_socket_L harith))
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_cc_decay_L_gk K (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-- `m4_arith_henv_constPool_L` (:904), at the lever. -/
theorem m4_arith_henv_constPool_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ}
    {Kar ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (constPool ρ R.Hhi)
        ≤ RSanDoorRho ρ H :=
  m4_arith_henv_rho_pool_L_gk K (π₀ := fun _ => constPool ρ R.Hhi)
    (fun _ => constPool_nonneg hρ) harith (price_at_constPool_socket_L harith)

/-- `doorFuseFrame_pool'_of_gates_const_L` (:964), at the lever. -/
theorem doorFuseFrame_pool'_of_gates_const_L_gk (K : ℕ) {M Xd j Hhi : ℕ} {Cs Ccc ε ρ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ constPool ρ Hhi)
    (hg : GRowsZeroGate'''_L_gk K M Xd Ccc (constPool ρ Hhi))
    (hε : ε ≤ 0)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (heps293 : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293) ≤ constPool ρ Hhi)
    (hband4096 : (4096 : ℝ)
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500) * constPool ρ Hhi) :
    DoorFuseFrame_pool'_L_gk K M Xd j Cs Ccc ε (constPool ρ Hhi) where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate'''_L_gk K hM hXd hg
  eps_pool := eps_pool_of_threshold (r5L_one_le_log_of_three_le hb.X_three) hε heps293
  band_pool := band_pool_of_threshold
    (by have := r5L_one_le_log_of_three_le hb.X_three; linarith) hband4096

/-- `m4_closure_fuse_end'_const_L` (:1011), at the lever. -/
theorem m4_closure_fuse_end'_const_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kar ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 ≤ ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          GRowsZeroGate'''_L_gk K M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowEndBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
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
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hexit⟩ :=
    m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated_L_gk K hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε Kar ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows heps heps293 hband4096 hbase
    hcap hband harith
  refine hexit R M C₁ M₀ ε (fun _ => constPool ρ R.Hhi) (fun _ H => RSanDoorRho ρ H) cU bU t₁
    hM hb1 hc1 ?_ hbase hcap hband (fun _ => constPool_nonneg hρ)
    (m4_arith_henv_constPool_L_gk K hρ harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_L_gk K (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (heps293 H L q j A s hb)
    (hband4096 H L q j A s hb)

/-- `m4_closure_fuse_zero'_const_L` (:1072), at the lever. -/
theorem m4_closure_fuse_zero'_const_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kar ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 ≤ ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          GRowsZeroGate'''_L_gk K M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
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
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hexit⟩ := m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_L_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε Kar ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows heps heps293 hband4096
    hbase hcap hband harith
  refine hexit Cp hCp R M C₁ M₀ ε (fun _ => constPool ρ R.Hhi) (fun _ H => RSanDoorRho ρ H)
    cU bU t₁ hM hb1 hc1 ?_ hbase hcap hband (fun _ => constPool_nonneg hρ)
    (m4_arith_henv_constPool_L_gk K hρ harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_L_gk K (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (heps293 H L q j A s hb)
    (hband4096 H L q j A s hb)

end Salt.MR

end
