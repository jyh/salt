/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ThmA2Pool
import Salt.MR.ThmA2Rows

/-!
# ⟦R3-A — THE R1×R2 JOIN⟧ at the frozen interface (`ThmA2Prime`)

Design provenance: `docs/exploration/knot2-closure-freeze-0730.md`; the landing entries
`flags.md` 2026-07-30 17:24 (⟦R1⟧, ⟦R2⟧) and the R3 dispatch on the same entry.

`ThmA2.a2RowsSum'` (⟦R1⟧) re-prices the `p²` slot `16·log₂(2X_d)/𝒫ⱼ ↦ 24/𝒫ⱼ`, `X_d`-FREE.
`ThmA2Pool.thm_a2'_of_rows_pool` (⟦R2⟧) frees the three `X`-side sources into one constant
pool `π₀`.  This file is their JOIN: the crossing stated at BOTH the primed row sum AND the
free pool.

## ⚠ ⟦THE JOIN DIRECTION⟧ — R1's own finding, restated in the kernel

`a2RowsSum'_le_a2RowsSum` says the primed sum is SMALLER, so a hypothesis stated at
`a2RowsSum'` is WEAKER and a theorem carrying it is STRONGER.  The inequality therefore
runs the WRONG WAY for discharging: **no landed-form `gRows` gate discharges a primed
slot**, and the join must re-thread through the primed supplier at every step.  There is no
shortcut, and this file offers none: `a2Mrow'` is a NEW definition beside `a2Mrow`,
`a2Mrow'_le_a2Mrow` is recorded only as the fidelity fact (the primed row number is the
smaller one), and it is never used to prove a primed statement from a landed one.

## Contents

* §1 `a2Mrow'` — the flat row number at the primed row sum, and `a2Mrow'_le_a2Mrow`;
* §2 `thm_a2'_of_rows_pool'` — **THE JOIN**: the `q = 1` crossing at the primed sum and the
  free pool;
* §3 `thm_a2'_of_rows_chiSummed_pool'` — its `Σ_χ` wrapper (`π₀` a `χ`-free SCALAR, the
  ⟦φ(q) LEDGER⟧ unchanged);
* §4 `thm_a2'_of_rows'` — the primed crossing at the LANDED decaying right-hand side (the
  A3 middle's own exit: `π₀ := (log X)^{−1/500}`, with `hgU`/`hgBand` derived from `hεwin`
  and `hL4096` exactly as the landed proof derives them).

Additive: no landed declaration is touched.  `ThmA2.spine_scale` and
`ThmA2Pool.spine_scale_pool` are both module-private, so §2 carries its own copy.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

/-! ## §1 — THE FLAT ROW NUMBER AT THE PRIMED ROW SUM -/

/-- **THE FLAT ROW NUMBER — R1** (`a2Mrow'`).  `ThmA2.a2Mrow` with its Lemma-12 slot read at
the re-priced `ThmA2.a2RowsSum'`: the `p²` rows are the `X_d`-FREE constant `24/𝒫ⱼ`.  The
other three summands — the §8.1 level-1 term, the `Cs`-row and the `𝒰`-leg — are
`a2Mrow`'s, byte for byte, and the ⟦AMENDMENT G⟧ `×4` cover `5760` never moves. -/
def a2Mrow' (Cs C : ℝ) (M Xd : ℕ) (X ε : ℝ) : ℝ :=
  47520 * a2Level1 M
    + 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
    + 5760 * (a2RowsSum' M Xd + C * (2 / (M : ℝ)))
    + 3 * (Real.log X) ^ (-theta293 + ε)

/-- **THE PRIMED ROW NUMBER IS THE SMALLER ONE** (`a2Mrow'_le_a2Mrow`), at `2 ≤ X_d` — one
application of `ThmA2.a2RowsSum'_le_a2RowsSum` inside the third summand.

⚠ RECORDED AS FIDELITY, NEVER USED AS A BRIDGE: a `hrows` binder stated at `a2Mrow'` is
STRONGER than one stated at `a2Mrow`, so this inequality cannot supply a primed row family
from a landed one.  Every primed consumer below is fed by a primed supplier. -/
lemma a2Mrow'_le_a2Mrow {Cs C : ℝ} {M Xd : ℕ} {X ε : ℝ} (hXd : 2 ≤ Xd) :
    a2Mrow' Cs C M Xd X ε ≤ a2Mrow Cs C M Xd X ε := by
  have h := a2RowsSum'_le_a2RowsSum (M := M) (Xd := Xd) hXd
  unfold a2Mrow' a2Mrow
  linarith

/-! ## §2 — THE JOIN: the `q = 1` crossing at the primed sum AND the free pool -/

/-- The `π`-arithmetic of the spine's prefactor `1/(2π²)`, isolated (`ThmA2.spine_scale`'s
statement and proof; both the landed copy and `ThmA2Pool`'s are module-private):
`236365/(2π) ≤ 37620`, `205/(2π) ≤ 33`, `39674880/(2π) ≤ 6315000`. -/
private lemma spine_scale_prime {p Mr Bd w Eg eg : ℝ} (hp1 : 3.141592 < p)
    (hMr : 0 ≤ Mr) (hBd : 0 ≤ Bd) (hw : 0 ≤ w) (hEg : Eg ≤ 2 * p ^ 2 * eg) :
    1 / (2 * p ^ 2) * (236365 * p * Mr + 205 * p * Bd + 39674880 * p * w + Eg)
      ≤ 37620 * Mr + 33 * Bd + 6315000 * w + eg := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp2pos : (0 : ℝ) < 2 * p ^ 2 := by positivity
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hp2pos]
  have h1 : 236365 * p ≤ 75240 * p ^ 2 := by nlinarith
  have h2 : 205 * p ≤ 66 * p ^ 2 := by nlinarith
  have h3 : 39674880 * p ≤ 12630000 * p ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hMr, mul_le_mul_of_nonneg_right h2 hBd,
    mul_le_mul_of_nonneg_right h3 hw]

/-- **⟦THE R1×R2 JOIN⟧** (`thm_a2'_of_rows_pool'`) — `ThmA2Pool.thm_a2'_of_rows_pool` with
its row family at `a2Mrow'` and its second grading gate at `a2RowsSum'`:

  `(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
  `  ≤ 8448·C₁'²·exp(−M₀/e)`
  `   + 1787702400·(log Q₁)^{1/3}/P₁^{1/12}`
  `   + 188133·π₀`
  `   + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)²`
  `   + 6315000/h`.

⟦THE GATE LIST⟧ against `thm_a2'_of_rows_pool`: the frame (`hM`, `hX`, `hX3`, `hh4`, `hhX`,
`ha`, `hsupp`, `hN2`, `hTann`, `hceil`), the band supplier `hT0band` and the four pool gates
`hpool`/`hgP1`/`hgU`/`hgBand` are VERBATIM.  Exactly TWO slots move, in the same direction:
`hrows` reads `a2Mrow'` and `hgRows` reads `a2RowsSum'`.  Both are the primed — i.e.
SMALLER — objects, so both hypotheses are WEAKER and the conclusion is unchanged: this
theorem is strictly stronger than its R2 sibling, which is strictly stronger than the S8
summit's own `thm_a2'_of_rows`.

⟦WHY THE PROOF IS THE POOL TWIN'S, UNCHANGED⟧ `hgRows` enters through exactly one step —
the `linarith` behind `hMrowLe : a2Mrow' ≤ 47520·a2Level1 M + 5·π₀` — and it enters as a
bound on the row number's third summand, whichever sum sits inside it.  Nothing downstream
of `hMrowLe` mentions the rows at all. -/
theorem thm_a2'_of_rows_pool' {N M Xd : ℕ} {a : ℕ → ℂ} {X h Cs Ccc C₁' M₀ ε π₀ : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2) ≤ a2Mrow' Cs Ccc M Xd X ε)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ t0BandB X C₁' M₀)
    (hpool : 0 ≤ π₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum' M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
    (hgU : (Real.log X) ^ (-theta293 + ε) ≤ π₀)
    (hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
      ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1 M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hL1
  have hrp13 : (0 : ℝ) < (Real.log X) ^ (-(43 : ℝ) / 45) := Real.rpow_pos_of_pos hL0 _
  -- the level-1 grade is nonnegative
  have hlogQ1 := one_le_log_calQK_door_one hM
  have hP64 := calP_door_one_ge M
  have hlvl0 : (0 : ℝ) ≤ a2Level1 M := by
    unfold a2Level1
    have h1 : (0 : ℝ) ≤ (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by linarith) _
    have h2 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
      Real.rpow_pos_of_pos (by linarith) _
    exact div_nonneg h1 h2.le
  -- ⟦the PRIMED row number, graded AT THE POOL⟧ — three sources, `1 + 1 + 3` copies
  have hMrowLe : a2Mrow' Cs Ccc M Xd X ε ≤ 47520 * a2Level1 M + 5 * π₀ := by
    unfold a2Mrow'
    linarith
  have hMrow'0 : (0 : ℝ) ≤ 47520 * a2Level1 M + 5 * π₀ := by linarith
  -- ⟦the band, graded, with the `4096` summand absorbed INTO THE POOL⟧
  have hBandLe : t0BandB X C₁' M₀
      ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + π₀
        + 9216 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by
    have := t0BandB_grade (X := X) (C₁ := C₁') (M₀ := M₀) hX3
    linarith
  have hBand'0 : (0 : ℝ) ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + π₀
        + 9216 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by
    have h1 : (0 : ℝ) ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀) := by positivity
    have h2 : (0 : ℝ) ≤ 9216 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by positivity
    linarith
  -- ⟦the Perron defect, to the limit⟧
  refine le_of_forall_pos_le_add (fun eg heg => ?_)
  have hpi := Real.pi_gt_d6
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨K, δ, hδ0, hδ1, hEg⟩ :=
    egap_small (X := X) (h := h) hX3 hh4 (show (0 : ℝ) < 2 * Real.pi ^ 2 * eg by positivity)
  have hspine := thm_a2_spine (N := N) (a := a) (X := X) (h := h)
    (Mrow := a2Mrow' Cs Ccc M Xd X ε) (B₀ := t0BandB X C₁' M₀) (δ := δ) K
    hX hh4 hhX hδ0 hδ1 ha hsupp hN2 hTann hceil hrows hT0band
  refine hspine.trans ?_
  -- monotonicity in `Mrow` and `B₀`, then the `π`-arithmetic
  have hmono : 1 / (2 * Real.pi ^ 2)
        * (236365 * Real.pi * a2Mrow' Cs Ccc M Xd X ε
            + 205 * Real.pi * t0BandB X C₁' M₀ + 39674880 * Real.pi / h
            + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
              + 1152 * (12 * h / (2 ^ K * δ)
                  + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2))
      ≤ 1 / (2 * Real.pi ^ 2)
        * (236365 * Real.pi * (47520 * a2Level1 M + 5 * π₀)
            + 205 * Real.pi * (256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + π₀
                + 9216 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2))
            + 39674880 * Real.pi * (1 / h)
            + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
              + 1152 * (12 * h / (2 ^ K * δ)
                  + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2)) := by
    have hpre : (0 : ℝ) ≤ 1 / (2 * Real.pi ^ 2) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hpre
    have e1 : 236365 * Real.pi * a2Mrow' Cs Ccc M Xd X ε
        ≤ 236365 * Real.pi * (47520 * a2Level1 M + 5 * π₀) :=
      mul_le_mul_of_nonneg_left hMrowLe (by positivity)
    have e2 : 205 * Real.pi * t0BandB X C₁' M₀
        ≤ 205 * Real.pi * (256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
            + π₀
            + 9216 * ballSupC ^ 2
              * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hBandLe (by positivity)
    have e3 : 39674880 * Real.pi / h = 39674880 * Real.pi * (1 / h) := by ring
    rw [e3]
    linarith
  refine hmono.trans ?_
  have hscale := spine_scale_prime (p := Real.pi)
    (Mr := 47520 * a2Level1 M + 5 * π₀)
    (Bd := 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + π₀
        + 9216 * ballSupC ^ 2
          * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2))
    (w := 1 / h) (eg := eg) hpi hMrow'0 hBand'0 (by positivity) hEg
  refine hscale.trans ?_
  have hw : 6315000 * (1 / h) = 6315000 / h := by ring
  rw [hw]
  linarith

/-! ## §3 — THE `Σ_χ` WRAPPER, AT THE JOIN

`ThmA2Pool.thm_a2'_of_rows_chiSummed_pool`'s three moves, verbatim, with §2 in move 1.  The
pool is still a SCALAR and the ⟦φ(q) LEDGER⟧ is byte-identical: only the two row slots move
to their primed forms, and neither is `χ`-free (both are already per-character). -/

/-- **⟦THE R1×R2 JOIN, `Σ_χ`⟧** (`thm_a2'_of_rows_chiSummed_pool'`).  §2's character sum, at
a generic `χ`-indexed coefficient family, INDEXED constant families `Cs Ccc C₁' M₀ ε`, and a
`χ`-FREE pool `π₀`:

`∑_χ (1/X)∫_X^{2X} ‖(1/h)·S_χ(x)‖² dx`
`  ≤ ∑_χ 8448·C₁'(χ)²·exp(−M₀(χ)/e)`
`   + φ(q)·[ 1787702400·a2Level1 M + 188133·π₀`
`          + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)² + 6315000/h ]`.

⟦THE φ(q) LEDGER IS UNTOUCHED BY R1⟧ `a2RowsSum'` sits inside the per-character `hgRows`,
which was already on the `∀ χ` side; the pool stays global for exactly the reason
`ThmA2Pool` records (a per-`χ` pool would move the third summand onto the `∑_χ` side and
break the single `φ(q)` payment). -/
theorem thm_a2'_of_rows_chiSummed_pool' {q : ℕ} [NeZero q] {N M Xd : ℕ}
    {a : DirichletCharacter ℂ q → ℕ → ℂ} {X h π₀ : ℝ}
    {Cs Ccc C₁' M₀ ε : DirichletCharacter ℂ q → ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, ‖a χ n‖ ≤ 1)
    (hsupp : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, (n : ℝ) ≤ X → a χ n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
      TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (a χ) t‖ ^ 2)
        ≤ a2Mrow' (Cs χ) (Ccc χ) M Xd X (ε χ))
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA (a χ) (seamS0 N X) t‖ ^ 2)
        ≤ t0BandB X (C₁' χ) (M₀ χ))
    (hpool : 0 ≤ π₀)
    (hgP1 : ∀ χ : DirichletCharacter ℂ q,
      374784 * Cs χ * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : ∀ χ : DirichletCharacter ℂ q,
      5760 * (a2RowsSum' M Xd + Ccc χ * (2 / (M : ℝ))) ≤ π₀)
    (hgU : ∀ χ : DirichletCharacter ℂ q, (Real.log X) ^ (-theta293 + ε χ) ≤ π₀)
    (hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    ∑ χ : DirichletCharacter ℂ q,
        1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
      ≤ (∑ χ : DirichletCharacter ℂ q,
            8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ))
        + (q.totient : ℝ)
            * (1787702400 * a2Level1 M
              + 188133 * π₀
              + 304128 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
              + 6315000 / h) := by
  -- ⟦move 1⟧ §2 at each character's OWN datum and OWN constants, at the SHARED pool
  have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
        ≤ 8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ)
          + (1787702400 * a2Level1 M
            + 188133 * π₀
            + 304128 * ballSupC ^ 2
                * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
            + 6315000 / h) := by
    intro χ _
    have hrow := thm_a2'_of_rows_pool' (N := N) (M := M) (Xd := Xd) (a := a χ) (X := X) (h := h)
      (Cs := Cs χ) (Ccc := Ccc χ) (C₁' := C₁' χ) (M₀ := M₀ χ) (ε := ε χ) (π₀ := π₀)
      hM hX hX3 hh4 hhX (ha χ) (hsupp χ) hN2 hTann hceil (hrowsSum χ) (hT0bandSum χ)
      hpool (hgP1 χ) (hgRows χ) (hgU χ) hgBand
    refine le_trans hrow (le_of_eq ?_)
    ring
  -- ⟦move 2⟧ the character sum, then ⟦move 3⟧ the split: `φ(q)` on the four `χ`-free summands
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [a2_sum_head_split]

/-! ## §4 — THE A3 MIDDLE'S OWN EXIT: the primed crossing at the LANDED grade

⟦R1⟧'s fence names `thm_a2'_of_rows'` as the end of the primed thread — the frozen
five-summand statement, with `(log X)^{−1/500}` back in the third slot, carrying the WEAKER
`a2RowsSum'` gate.  It is §2 at `π₀ := (log X)^{−1/500}`, with the two pool gates supplied
by exactly the derivations the landed proof performs inline (`hεwin ⟹ hgU`,
`hL4096 ⟹ hgBand`).  Nothing here is a new estimate. -/

/-- **thm_A2′ AT THE PRIMED ROW SUM** (`thm_a2'_of_rows'`) — `ThmA2.thm_a2'_of_rows` with
`a2Mrow ↦ a2Mrow'` and `a2RowsSum ↦ a2RowsSum'`, the frozen conclusion BYTE-IDENTICAL.

⟦THE S8 SUMMIT BECOMES STRICTLY STRONGER⟧ — this is that sentence as a kernel object: the
hypothesis list differs from the landed one in exactly two slots, both of which name the
SMALLER (`a2RowsSum' ≤ a2RowsSum`, `a2Mrow' ≤ a2Mrow`) object, and the conclusion is the
frozen one unchanged. -/
theorem thm_a2'_of_rows' {N M Xd : ℕ} {a : ℕ → ℂ} {X h Cs Ccc C₁' M₀ ε : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2) ≤ a2Mrow' Cs Ccc M Xd X ε)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ t0BandB X C₁' M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hgRows : 5760 * (a2RowsSum' M Xd + Ccc * (2 / (M : ℝ)))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hεwin : 0 ≤ ε ∧ ε ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
      ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1 M
        + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h := by
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hrp500 : (0 : ℝ) < (Real.log X) ^ (-(1 : ℝ) / 500) := Real.rpow_pos_of_pos hL0 _
  -- ⟦the `𝒰`-leg gate⟧ the landed derivation from `hεwin`
  have hgU : (Real.log X) ^ (-theta293 + ε) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) := by
    have hθ : theta293 < 1 / 32 := theta293_lt_one_div_32
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [hεwin.1, hεwin.2])
  -- ⟦the band absorption⟧ the landed derivation from `hL4096`
  have hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500)
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500) := by
    have hsp : (Real.log X) ^ (-(1 : ℝ) / 500)
        = (Real.log X) ^ (1 - (1 : ℝ) / 250) * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [hsp]
    exact mul_le_mul_of_nonneg_right hL4096
      (le_of_lt (Real.rpow_pos_of_pos hL0 _))
  exact thm_a2'_of_rows_pool' hM hX hX3 hh4 hhX ha hsupp hN2 hTann hceil hrows hT0band
    hrp500.le hgP1 hgRows hgU hgBand

end Salt.MR
