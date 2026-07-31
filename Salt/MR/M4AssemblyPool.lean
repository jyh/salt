/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Assembly
import Salt.MR.ThmA2Pool

/-!
# ⟦R2 — THE CONSTANT POOL⟧ at the door grade and the socket (`M4AssemblyPool`)

Design provenance: `docs/exploration/knot2-closure-freeze-0730.md`, wave **R2**; the re-cut
inventory of KNOT2-SCOPE (`flags.md` 2026-07-30 15:50), fired by K4-CENSUS (16:42).
`ThmA2Pool` carries the interface half; this file carries the door half.

## ⟦WHAT THE POOL DOES TO THE DOOR GRADE⟧

`M4Assembly.a2DoorGrade`'s third summand is `188133·(log X)^{−1/500}` — the ONE summand that
decays in the base.  `a2DoorGrade_pool` replaces it by `188133·π₀` at a free `π₀ ≥ 0`; the
other four summands are byte-identical.  Setting `π₀ := (log X)^{−1/500}` recovers the landed
grade definitionally.

`DoorFuseFrame_pool` is the frame twin: ELEVEN fields become TEN.  `eps_lo`/`eps_hi` — the
`𝒰`-leg's exponent room `0 ≤ ε ≤ θ₂₉₃ − 1/500`, the pair that made `ε` a constrained
parameter — collapse to the single stated gate `eps_pool : (log X_d)^{−θ₂₉₃+ε} ≤ π₀`, and
`L4096` becomes `band_pool : 4096·(log X_d)^{−1+1/500} ≤ π₀`.  **`ε` is FREE.**  Nonnegativity
of the pool is NOT a field: `DoorFuseFrame_pool.pool_nonneg` derives it from `band_pool` and
`X_three`, which is why the field count drops by one rather than staying at eleven.

⚠ ⟦χ-FREEDOM⟧ `π₀` is `χ`-free at every base (it is indexed by the BASE `A + s`, exactly as
`C₁`/`M₀` are, never by the character): the ⟦φ(q) LEDGER⟧'s single payment depends on it.

## Contents

* §1 `a2DoorGrade_pool` + `a2DoorGrade_pool_nonneg`;
* §2 `m4_chiFreeRowSq_sum_at_door_pool` — the slot fuse at the pool;
* §3 `DoorFuseFrame_pool` — the ten-field frame twin;
* §4 the socket wires: `m4_chiSummedFreeRowBig_of_doorGrade_pool`,
  `m4_chiSummedFreeRow_of_doorGrade_pool`, `m4_chiSummedFreeRow_of_doorAssembly_pool`.

`SocketBase` is grade-blind and is reused verbatim.  Additive: no landed declaration is
touched.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE DOOR GRADE, POOLED -/

/-- **THE DOOR GRADE AT A FREE POOL** (`a2DoorGrade_pool M X h C₁ M₀ π₀`) — `M4Assembly`'s
`a2DoorGrade` with its third summand `188133·(log X)^{−1/500}` replaced by `188133·π₀`.

This is the whole of ⟦R2⟧ at the grade level: the door's constant target `δ₀/4` needs no
decay, so the one decaying summand is freed to a constant the consumer supplies. -/
def a2DoorGrade_pool (M : ℕ) (X h C₁ M₀ π₀ : ℝ) : ℝ :=
  8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
    + 1787702400 * a2Level1 M
    + 188133 * π₀
    + 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
    + 6315000 / h

/-- `a2DoorGrade_pool` at `π₀ := (log X)^{−1/500}` IS the landed `a2DoorGrade` — definitional,
recorded so the twin's fidelity is a checked object and not a claim. -/
theorem a2DoorGrade_pool_at_decay (M : ℕ) (X h C₁ M₀ : ℝ) :
    a2DoorGrade_pool M X h C₁ M₀ ((Real.log X) ^ (-(1 : ℝ) / 500))
      = a2DoorGrade M X h C₁ M₀ := rfl

/-- The pooled door grade is nonnegative — the `φ(q) ≤ arcDen 12 H` ledger step, at the pool.
The only new hypothesis against `M4Assembly.a2DoorGrade_nonneg` is `0 ≤ π₀`. -/
theorem a2DoorGrade_pool_nonneg (M : ℕ) {X h C₁ M₀ π₀ : ℝ} (hX : 0 ≤ Real.log X) (hh : 0 < h)
    (hπ : 0 ≤ π₀) : 0 ≤ a2DoorGrade_pool M X h C₁ M₀ π₀ := by
  have hQ1 : (1 : ℝ) ≤ ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := by
    exact_mod_cast one_le_calQK (Adoor M) (3072 * M) M 1
  have hP1 : (1 : ℝ) ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    have h : 1 ≤ calP (Adoor M) (3072 * M) 1 := by
      simp only [calP]; exact Nat.one_le_two_pow
    exact_mod_cast h
  have hlvl : (0 : ℝ) ≤ a2Level1 M := by
    unfold a2Level1
    have h1 : (0 : ℝ) ≤ (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (Real.log_nonneg hQ1) _
    have h2 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
      Real.rpow_pos_of_pos (by linarith) _
    exact div_nonneg h1 h2.le
  have h4345 : (0 : ℝ) ≤ (Real.log X) ^ (-(43 : ℝ) / 45) := Real.rpow_nonneg hX _
  have hband : (0 : ℝ) ≤ 8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀) := by
    positivity
  have hball : (0 : ℝ) ≤ 304128 * ballSupC ^ 2
      * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by
    have : (0 : ℝ) ≤ (Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2 :=
      mul_nonneg h4345 (sq_nonneg _)
    positivity
  have hh6 : (0 : ℝ) ≤ 6315000 / h := by positivity
  unfold a2DoorGrade_pool
  linarith

/-! ## §2 — THE SLOT FUSE, AT THE POOL -/

/-- **⟦THE SLOT FUSE AT THE POOL⟧** (`m4_chiFreeRowSq_sum_at_door_pool`).
`ThmA2Pool.thm_a2'_of_rows_chiSummed_pool` instantiated at the door datum

  `N := 2X_d`,  `X := X_d`,  `h := 2^j`,  `a χ := winCutH X_d (doorChiCoeff χ M)`,

whose right-hand side collapses to `φ(q)·a2DoorGrade_pool M X_d 2^j C₁ M₀ π₀`.

⟦THE GATE LIST AGAINST `M4Assembly.m4_chiFreeRowSq_sum_at_door`⟧ `hM`, `hX`, `hX3`, `hh4`,
`hhX`, `hTann`, `hceil`, `hrowsSum`, `hT0bandSum` are VERBATIM.  `hgP1`/`hgRows` read `≤ π₀`;
`hεwin` and `hL4096` are GONE, replaced by the two stated pool gates `hgU`/`hgBand`.  `0 ≤ π₀`
is derived from `hgBand` and `hX3`, not assumed. -/
theorem m4_chiFreeRowSq_sum_at_door_pool {q : ℕ} [NeZero q] {M Xd j : ℕ}
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
        ≤ a2Mrow Cs Ccc M Xd ((Xd : ℕ) : ℝ) ε)
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 ((Xd : ℕ) : ℝ)))..(seamT0 ((Xd : ℕ) : ℝ)),
        ‖dpolyA (winCutH Xd (doorChiCoeff χ M)) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) t‖ ^ 2)
        ≤ t0BandB ((Xd : ℕ) : ℝ) (cfbC₁ ((Xd : ℕ) : ℝ) C₁) M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
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
  have hbase := thm_a2'_of_rows_chiSummed_pool (q := q) (N := 2 * Xd) (M := M) (Xd := Xd)
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

/-! ## §3 — THE FRAME TWIN: ELEVEN FIELDS BECOME TEN -/

/-- **THE FUSE FRAME AT ONE BASE, POOLED** (`DoorFuseFrame_pool`) — the character-blind half
of `m4_chiFreeRowSq_sum_at_door_pool`'s gate list, field by field.

Against `M4Assembly.DoorFuseFrame`'s eleven fields: the six frame fields are verbatim; `gP1`
and `gRows` read `≤ π₀`; `eps_lo`/`eps_hi` are REPLACED by the single `eps_pool` (so `ε` is
otherwise free); `L4096` is REPLACED by `band_pool`.  **Ten fields.**  Nonnegativity of `π₀`
is a derived lemma (`pool_nonneg`), not a field. -/
structure DoorFuseFrame_pool (M Xd j : ℕ) (Cs Ccc ε π₀ : ℝ) : Prop where
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
  /-- The second GRADING gate, on the Lemma-12 row sum and `Ccc`, AT THE POOL. -/
  gRows : 5760 * (a2RowsSum M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀
  /-- **THE `𝒰`-LEG, POOLED** — replacing `eps_lo`/`eps_hi`: the leg's own value sits under
  the pool, so `ε` carries no exponent-room constraint. -/
  eps_pool : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀
  /-- **THE BAND ABSORPTION, POOLED** — replacing `L4096`. -/
  band_pool : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀

namespace DoorFuseFrame_pool

variable {M Xd j : ℕ} {Cs Ccc ε π₀ : ℝ}

/-- The pool is nonnegative — DERIVED from `band_pool` and `X_three`, which is why the frame
has ten fields and not eleven. -/
theorem pool_nonneg (h : DoorFuseFrame_pool M Xd j Cs Ccc ε π₀) : 0 ≤ π₀ := by
  have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by
    have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) h.X_three
    have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  have hrp : (0 : ℝ) < (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) :=
    Real.rpow_pos_of_pos hL0 _
  have := h.band_pool
  linarith

end DoorFuseFrame_pool

/-! ## §4 — THE SOCKET WIRES, AT THE POOLED GRADE

`SocketBase` is grade-blind and is reused verbatim.  The pool joins `C₁`/`M₀` as a
BASE-indexed family `π₀ : ℕ → ℝ` — never character-indexed. -/

/-- **⟦THE SOCKET AT THE POOLED DOOR GRADE⟧** (`m4_chiSummedFreeRowBig_of_doorGrade_pool`) —
`M4Assembly.m4_chiSummedFreeRowBig_of_doorGrade` with `a2DoorGrade_pool` in both slots.  The
⟦φ(q) LEDGER⟧ is paid identically: `φ(q) ≤ q ≤ arcDen 12 H`, explicit in `henv`. -/
theorem m4_chiSummedFreeRowBig_of_doorGrade_pool {R : ChowlaRegime} {M : ℕ}
    {C₁ M₀ π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloor M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)) (π₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) (π₀ (A + s)) :=
    a2DoorGrade_pool_nonneg M (log_natCast_nonneg' (A + s)) hh0 (hpool (A + s))
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans
    (hgrade H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H j A s hjfl

/-- **⟦ITEM 11, INHABITED AT THE POOLED DOOR GRADE⟧**
(`m4_chiSummedFreeRow_of_doorGrade_pool`) — §4 spliced through
`M4ChiSocketWire.m4_chiSummedFreeRow_of_big`, at the same `m4ChiRowGraded` shape. -/
theorem m4_chiSummedFreeRow_of_doorGrade_pool {R : ChowlaRegime} {M : ℕ}
    {C₁ M₀ π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloor M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)) (π₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) :=
  m4_chiSummedFreeRow_of_big (m4_chiSummedFreeRowBig_of_doorGrade_pool hpool hgrade henv)

/-- **⟦THE ASSEMBLY, POOLED⟧** (`m4_chiSummedFreeRow_of_doorAssembly_pool`) — ⟦item 11⟧ of
`m4_second_road` from the NAMED gates alone, at the pooled grade.

THE COMPLETE GATE LIST: `hM`; `hframe` — `DoorFuseFrame_pool` (TEN fields) at every base the
socket reaches, with the base-indexed pool `π₀`; `hrows` and `hband` — `M4Assembly`'s own two
suppliers, BYTE FOR BYTE unchanged (neither mentions the pool); `henv` — the arithmetic, now
against `a2DoorGrade_pool`. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorFuseFrame_pool M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
          ≤ a2Mrow (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
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
  exact m4_chiFreeRowSq_sum_at_door_pool hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows hF.eps_pool
    hF.band_pool

/-! ## §GK — the G-lever twin

The pooled door page at `G := s13GK K M` (`GLever`): `(K : ℕ)` as a new FIRST binder, the door
datum at `doorChiCoeff_gk`, the row number at `ThmA2.a2Mrow_gk` and the row sum at
`ThmA2.a2RowsSum_gk`.  `SocketBase` and `m4ChiRowGraded` are `G`-free and are reused VERBATIM;
`a2Level1 M` is level-1 and K-invariant, so `a2DoorGrade_pool_gk`'s body is byte-identical to
the landed one's (recorded as `a2DoorGrade_pool_gk_eq`). -/

set_option linter.unusedVariables false in
/-- `a2DoorGrade_pool` (:61), at the lever.  Body byte-identical (`a2Level1` is K-invariant);
the twin exists for uniformity of the family's shape. -/
def a2DoorGrade_pool_gk (K : ℕ) (M : ℕ) (X h C₁ M₀ π₀ : ℝ) : ℝ :=
  8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
    + 1787702400 * a2Level1 M
    + 188133 * π₀
    + 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
    + 6315000 / h

/-- The levered pooled grade IS the landed one (`a2Level1` is K-invariant). -/
theorem a2DoorGrade_pool_gk_eq (K : ℕ) (M : ℕ) (X h C₁ M₀ π₀ : ℝ) :
    a2DoorGrade_pool_gk K M X h C₁ M₀ π₀ = a2DoorGrade_pool M X h C₁ M₀ π₀ := rfl

/-- `a2DoorGrade_pool_at_decay` (:71), at the lever. -/
theorem a2DoorGrade_pool_at_decay_gk (K : ℕ) (M : ℕ) (X h C₁ M₀ : ℝ) :
    a2DoorGrade_pool_gk K M X h C₁ M₀ ((Real.log X) ^ (-(1 : ℝ) / 500))
      = a2DoorGrade_gk K M X h C₁ M₀ := rfl

/-- `a2DoorGrade_pool_nonneg` (:77), at the lever. -/
theorem a2DoorGrade_pool_nonneg_gk (K : ℕ) (M : ℕ) {X h C₁ M₀ π₀ : ℝ} (hX : 0 ≤ Real.log X)
    (hh : 0 < h) (hπ : 0 ≤ π₀) : 0 ≤ a2DoorGrade_pool_gk K M X h C₁ M₀ π₀ :=
  a2DoorGrade_pool_nonneg M hX hh hπ

/-- `m4_chiFreeRowSq_sum_at_door_pool` (:117), at the lever. -/
theorem m4_chiFreeRowSq_sum_at_door_pool_gk (K : ℕ) {q : ℕ} [NeZero q] {M Xd j : ℕ}
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
              ‖spoly (2 * Xd) (winCutH Xd (doorChiCoeff_gk K χ M)) t‖ ^ 2)
        ≤ a2Mrow_gk K Cs Ccc M Xd ((Xd : ℕ) : ℝ) ε)
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 ((Xd : ℕ) : ℝ)))..(seamT0 ((Xd : ℕ) : ℝ)),
        ‖dpolyA (winCutH Xd (doorChiCoeff_gk K χ M)) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) t‖ ^ 2)
        ≤ t0BandB ((Xd : ℕ) : ℝ) (cfbC₁ ((Xd : ℕ) : ℝ) C₁) M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
    (hgU : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀)
    (hgBand : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_gk K χ M j Xd
      ≤ (q.totient : ℝ)
          * a2DoorGrade_pool_gk K M ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
  have hpool : (0 : ℝ) ≤ π₀ := by
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by
      have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) hX3
      have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
      linarith
    have hrp : (0 : ℝ) < (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) :=
      Real.rpow_pos_of_pos hL0 _
    linarith
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hbase := thm_a2'_of_rows_chiSummed_pool_gk K (q := q) (N := 2 * Xd) (M := M) (Xd := Xd)
    (a := fun χ => winCutH Xd (doorChiCoeff_gk K χ M)) (X := ((Xd : ℕ) : ℝ))
    (h := ((2 ^ j : ℕ) : ℝ)) (π₀ := π₀) (Cs := fun _ => Cs) (Ccc := fun _ => Ccc)
    (C₁' := fun _ => cfbC₁ ((Xd : ℕ) : ℝ) C₁) (M₀ := fun _ => M₀) (ε := fun _ => ε)
    hM hX hX3 hh4 hhX (fun χ n => doorRow_ha1_gk K χ M Xd n)
    (fun χ n hn => doorRow_hsupp0_gk K χ M Xd n hn) hN2 hTann hceil hrowsSum hT0bandSum
    hpool (fun _ => hgP1) (fun _ => hgRows) (fun _ => hgU) hgBand
  simp only [shortSum_winCutH_seamS0] at hbase
  refine le_trans hbase (le_of_eq ?_)
  rw [a2_sum_const_chars]
  unfold a2DoorGrade_pool_gk
  ring

/-- `DoorFuseFrame_pool` (:175), at the lever.  Two of the ten fields move: `gP1`'s `𝒫₁` is
written at the levered base and `gRows` reads `ThmA2.a2RowsSum_gk`. -/
structure DoorFuseFrame_pool_gk (K : ℕ) (M Xd j : ℕ) (Cs Ccc ε π₀ : ℝ) : Prop where
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
  /-- The first GRADING gate, on the `𝒯`-leg constant `Cs`, AT THE POOL AND THE LEVER. -/
  gP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀
  /-- The second GRADING gate, at the levered row sum and `Ccc`, AT THE POOL. -/
  gRows : 5760 * (a2RowsSum_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀
  /-- **THE `𝒰`-LEG, POOLED** — `ε` carries no exponent-room constraint. -/
  eps_pool : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀
  /-- **THE BAND ABSORPTION, POOLED** — replacing `L4096`. -/
  band_pool : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀

namespace DoorFuseFrame_pool_gk

variable {K : ℕ} {M Xd j : ℕ} {Cs Ccc ε π₀ : ℝ}

/-- `DoorFuseFrame_pool.pool_nonneg` (:205), at the lever. -/
theorem pool_nonneg (h : DoorFuseFrame_pool_gk K M Xd j Cs Ccc ε π₀) : 0 ≤ π₀ := by
  have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by
    have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) h.X_three
    have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  have hrp : (0 : ℝ) < (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) :=
    Real.rpow_pos_of_pos hL0 _
  have := h.band_pool
  linarith

end DoorFuseFrame_pool_gk

/-- `m4_chiSummedFreeRowBig_of_doorGrade_pool` (:225), at the lever. -/
theorem m4_chiSummedFreeRowBig_of_doorGrade_pool_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {C₁ M₀ π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloor M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_gk K χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_pool_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)) (π₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig_gk K R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade_pool_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) (π₀ (A + s)) :=
    a2DoorGrade_pool_nonneg_gk K M (log_natCast_nonneg' (A + s)) hh0 (hpool (A + s))
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans
    (hgrade H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H j A s hjfl

/-- `m4_chiSummedFreeRow_of_doorGrade_pool` (:259), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorGrade_pool_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {C₁ M₀ π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloor M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_gk K χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_pool_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)) (π₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M RSbig) :=
  m4_chiSummedFreeRow_of_big_gk K
    (m4_chiSummedFreeRowBig_of_doorGrade_pool_gk K hpool hgrade henv)

/-- `m4_chiSummedFreeRow_of_doorAssembly_pool` (:285), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorFuseFrame_pool_gk K M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorGrade_pool_gk K (C₁ := C₁) (M₀ := M₀) (π₀ := π₀) hpool ?_
    henv
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb : SocketBase R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_pool_gk K hM hF.X_exp hF.X_three hF.h_four hF.h_window
    hF.tann hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows hF.eps_pool
    hF.band_pool

end Salt.MR

-- #audit (temporary)
