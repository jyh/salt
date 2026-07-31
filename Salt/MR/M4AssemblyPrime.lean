/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4AssemblyPool
import Salt.MR.ThmA2Prime

/-!
# ⟦R3-A — THE JOIN AT THE DOOR⟧ (`M4AssemblyPrime`)

`ThmA2Prime` joins ⟦R1⟧'s primed row sum to ⟦R2⟧'s free pool at the `q = 1` and `Σ_χ`
interfaces.  This file carries that join through the DOOR — the slot fuse, the frame twin,
and the socket composite — so that the joined crossing feeds `m4_second_road`'s ⟦item 11⟧.

## ⟦WHAT MOVES AND WHAT DOES NOT⟧

The GRADE does not move: `M4AssemblyPool.a2DoorGrade_pool` is already stated at the pool and
mentions no row sum, so `a2DoorGrade_pool_nonneg`, `m4_chiSummedFreeRowBig_of_doorGrade_pool`
and `m4_chiSummedFreeRow_of_doorGrade_pool` are reused VERBATIM — the R1 half of the join is
invisible to them.  Exactly two objects move, and both move to the SMALLER side:

* `DoorFuseFrame_pool'` — `DoorFuseFrame_pool` with `gRows` read at `ThmA2.a2RowsSum'`.  Ten
  fields, same names, one changed statement;
* `m4_chiFreeRowSq_sum_at_door_pool'` — the slot fuse over
  `ThmA2Prime.thm_a2'_of_rows_chiSummed_pool'`, whose `hrowsSum` binder reads `a2Mrow'`.

⚠ ⟦THE DIRECTION⟧ both are WEAKER hypotheses, so `m4_chiSummedFreeRow_of_doorAssembly_pool'`
is strictly stronger than its R2 sibling.  No landed-form frame discharges a primed slot;
the primed `hrows` supplier is `A3Middle.a2Rows_of_capfree3_end'` and there is no other.

## ⟦THE μ-LEDGER AT THIS LAYER⟧

`DoorFuseFrame_pool'`'s ten fields split by what they read of the base scale
`μ = loglog X_d`:

| field | reads `μ`? |
|---|---|
| `X_exp`, `X_three`, `h_four`, `h_window`, `tann`, `ceil5` | base-side frame, `μ`-LOWER only |
| `gP1` | **NO** — `374784·C_s·e³/𝒫₁ ≤ π₀`, both sides base-free |
| `gRows` | **NO** at `C_p = 0` — `GRowsZeroGate''`; its `(2e+2)/X_d` residue is base-LOWER |
| `eps_pool` | `(log X_d)^{−θ₂₉₃+ε} ≤ π₀` — base-LOWER at `ε ≤ θ₂₉₃` |
| `band_pool` | `4096·(log X_d)^{−1+1/500} ≤ π₀` — base-LOWER |

No field is a `μ`-CAP.  That is the whole content of R1 × R2 at the door: the pool retires
the decaying right-hand sides, and R1 retires the `log₂(2X_d)` numerator that made `gRows`
grow with the base.

## Contents

* §1 `DoorFuseFrame_pool'` + `pool_nonneg`;
* §2 `m4_chiFreeRowSq_sum_at_door_pool'` — the slot fuse at the JOIN;
* §3 `m4_chiSummedFreeRow_of_doorAssembly_pool'` — **THE EXIT**.

Additive: no landed declaration is touched.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE FRAME TWIN AT THE JOIN -/

/-- **THE FUSE FRAME AT ONE BASE, POOLED AND RE-PRICED** (`DoorFuseFrame_pool'`) —
`M4AssemblyPool.DoorFuseFrame_pool` with its `gRows` field at `ThmA2.a2RowsSum'`.

Ten fields, nine of them byte-identical to `DoorFuseFrame_pool`'s.  The one that moves is
`gRows`, and it moves to the WEAKER demand (`a2RowsSum' ≤ a2RowsSum`): its `p²` slot is now
the `X_d`-FREE `24·(1/𝒫₁ + 1/𝒫₂)`, so the field reads no `log₂(2X_d)` at all. -/
structure DoorFuseFrame_pool' (M Xd j : ℕ) (Cs Ccc ε π₀ : ℝ) : Prop where
  /-- `e ≤ X_d` — the frozen interface's lower scale pin. -/
  X_exp : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)
  /-- `3 ≤ X_d`. -/
  X_three : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ)
  /-- `4 ≤ 2^j` — the AS-2 MVT guard (NOT `3`). -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- Lemma 14's window frame `2^j ≤ X_d·(log X_d)^{−1/5}`. -/
  h_window : ((2 ^ j : ℕ) : ℝ)
    ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ))
  /-- `TannGate X_d (2X_d/2^j)` — the annulus gate at the family's bottom height. -/
  tann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))
  /-- `5 ≤ loglog(2X_d/2^j)` — the `h`-ceiling. -/
  ceil5 : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
  /-- The first GRADING gate, on the `𝒯`-leg constant `Cs`, AT THE POOL. -/
  gP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀
  /-- **THE SECOND GRADING GATE, AT THE POOL AND AT ⟦R1⟧'s ROW SUM** — the `p²` slot is the
  `X_d`-FREE constant `24/𝒫ⱼ`, so nothing in this field grows with the base. -/
  gRows : 5760 * (a2RowsSum' M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀
  /-- **THE `𝒰`-LEG, POOLED** — `ε` carries no exponent-room constraint. -/
  eps_pool : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀
  /-- **THE BAND ABSORPTION, POOLED**. -/
  band_pool : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀

namespace DoorFuseFrame_pool'

variable {M Xd j : ℕ} {Cs Ccc ε π₀ : ℝ}

/-- The pool is nonnegative — DERIVED from `band_pool` and `X_three`, exactly as in
`M4AssemblyPool.DoorFuseFrame_pool.pool_nonneg`. -/
theorem pool_nonneg (h : DoorFuseFrame_pool' M Xd j Cs Ccc ε π₀) : 0 ≤ π₀ := by
  have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by
    have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) h.X_three
    have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  have hrp : (0 : ℝ) < (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) :=
    Real.rpow_pos_of_pos hL0 _
  have := h.band_pool
  linarith

/-- **THE FIDELITY DIRECTION** (`toPool_of_le`): a primed frame is implied by the landed
pooled frame at `2 ≤ X_d` — `a2RowsSum' ≤ a2RowsSum` makes `gRows` weaker, and the nine other
fields are shared.  ⚠ ONLY this direction exists: a `DoorFuseFrame_pool` cannot be built from
a `DoorFuseFrame_pool'`. -/
theorem of_pool (h : DoorFuseFrame_pool M Xd j Cs Ccc ε π₀) (hXd : 2 ≤ Xd) :
    DoorFuseFrame_pool' M Xd j Cs Ccc ε π₀ where
  X_exp := h.X_exp
  X_three := h.X_three
  h_four := h.h_four
  h_window := h.h_window
  tann := h.tann
  ceil5 := h.ceil5
  gP1 := h.gP1
  gRows := by
    have hle := a2RowsSum'_le_a2RowsSum (M := M) (Xd := Xd) hXd
    have := h.gRows
    linarith
  eps_pool := h.eps_pool
  band_pool := h.band_pool

end DoorFuseFrame_pool'

/-! ## §2 — THE SLOT FUSE, AT THE JOIN -/

/-- **⟦THE SLOT FUSE AT THE JOIN⟧** (`m4_chiFreeRowSq_sum_at_door_pool'`).
`ThmA2Prime.thm_a2'_of_rows_chiSummed_pool'` instantiated at the door datum

  `N := 2X_d`,  `X := X_d`,  `h := 2^j`,  `a χ := winCutH X_d (doorChiCoeff χ M)`,

whose right-hand side collapses to `φ(q)·a2DoorGrade_pool M X_d 2^j C₁ M₀ π₀` — the SAME
grade `M4AssemblyPool.m4_chiFreeRowSq_sum_at_door_pool` lands in, because the pooled grade
mentions no row sum.

⟦THE GATE LIST AGAINST THE R2 SIBLING⟧ every gate is verbatim except two, both weaker:
`hrowsSum` reads `a2Mrow'` and `hgRows` reads `a2RowsSum'`.  `0 ≤ π₀` is still derived from
`hgBand` and `hX3`, not assumed. -/
theorem m4_chiFreeRowSq_sum_at_door_pool' {q : ℕ} [NeZero q] {M Xd j : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)) (hX3 : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ))
    (hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ))
    (hhX : ((2 ^ j : ℕ) : ℝ)
      ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ)))
    (hTann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
    (hceil : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ ((Xd : ℕ) : ℝ) →
      TannGate ((Xd : ℕ) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
          * (∫ t in seamAnn ((Xd : ℕ) : ℝ) (2 * T),
              ‖spoly (2 * Xd) (winCutH Xd (doorChiCoeff χ M)) t‖ ^ 2)
        ≤ a2Mrow' Cs Ccc M Xd ((Xd : ℕ) : ℝ) ε)
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 ((Xd : ℕ) : ℝ)))..(seamT0 ((Xd : ℕ) : ℝ)),
        ‖dpolyA (winCutH Xd (doorChiCoeff χ M)) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) t‖ ^ 2)
        ≤ t0BandB ((Xd : ℕ) : ℝ) (cfbC₁ ((Xd : ℕ) : ℝ) C₁) M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum' M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
    (hgU : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀)
    (hgBand : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j Xd
      ≤ (q.totient : ℝ)
          * a2DoorGrade_pool M ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
  have hpool : (0 : ℝ) ≤ π₀ := by
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by
      have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) hX3
      have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
      linarith
    have hrp : (0 : ℝ) < (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) :=
      Real.rpow_pos_of_pos hL0 _
    linarith
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hbase := thm_a2'_of_rows_chiSummed_pool' (q := q) (N := 2 * Xd) (M := M) (Xd := Xd)
    (a := fun χ => winCutH Xd (doorChiCoeff χ M)) (X := ((Xd : ℕ) : ℝ))
    (h := ((2 ^ j : ℕ) : ℝ)) (π₀ := π₀) (Cs := fun _ => Cs) (Ccc := fun _ => Ccc)
    (C₁' := fun _ => cfbC₁ ((Xd : ℕ) : ℝ) C₁) (M₀ := fun _ => M₀) (ε := fun _ => ε)
    hM hX hX3 hh4 hhX (fun χ n => doorRow_ha1 χ M Xd n)
    (fun χ n hn => doorRow_hsupp0 χ M Xd n hn) hN2 hTann hceil hrowsSum hT0bandSum
    hpool (fun _ => hgP1) (fun _ => hgRows) (fun _ => hgU) hgBand
  simp only [shortSum_winCutH_seamS0] at hbase
  refine le_trans hbase (le_of_eq ?_)
  rw [a2_sum_const_chars]
  unfold a2DoorGrade_pool
  ring

/-! ## §3 — THE EXIT: ⟦item 11⟧ from the joined chain

`M4AssemblyPool`'s §4 wires are grade-only and are reused verbatim; only the fuse in the
last step is the primed one. -/

/-- **⟦THE ASSEMBLY, AT THE R1×R2 JOIN⟧** (`m4_chiSummedFreeRow_of_doorAssembly_pool'`) —
**THE EXIT**: ⟦item 11⟧ of `m4_second_road` from the named gates alone, at the joined grade.

THE COMPLETE GATE LIST: `hM`; `hframe` — `DoorFuseFrame_pool'` (TEN fields) at every base
the socket reaches, with the base-indexed pool `π₀`; `hrows` — the row family at
`ThmA2Prime.a2Mrow'` (supplied by `A3Middle.a2Rows_of_capfree3_end'`, and by nothing else);
`hband` — `M4Assembly`'s own band supplier, BYTE FOR BYTE unchanged; `hpool` and `henv` —
verbatim from the R2 sibling, since the pooled grade never mentions a row sum.

⟦WHAT THIS DEMONSTRATES⟧ the joined chain feeds the frames: `a2Rows_of_capfree3_end'` lands
in `a2Mrow'`, `a2Mrow'` is what `thm_a2'_of_rows_pool'` consumes, and the pool is what the
door's constant target wants.  Every `X_d`-decaying right-hand side inside the frame is
gone; what remains are base-LOWER demands (see this module's μ-ledger). -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool' {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorFuseFrame_pool' M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
          ≤ a2Mrow' (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorGrade_pool (C₁ := C₁) (M₀ := M₀) (π₀ := π₀) hpool ?_ henv
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb : SocketBase R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_pool' hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows hF.eps_pool
    hF.band_pool

end Salt.MR
