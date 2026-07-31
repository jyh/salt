/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ThmA2ChiSummed

/-!
# ⟦R2 — THE CONSTANT POOL⟧, at the frozen interface (`ThmA2Pool`)

Design provenance: `docs/exploration/knot2-closure-freeze-0730.md`, wave **R2 — THE CONSTANT
POOL**, priced and mechanics-byte-verified by KNOT2-SCOPE (`flags.md` 2026-07-30 15:50, THE
POOL MECHANICS — VERIFIED) and fired by K4-CENSUS (`flags.md` 2026-07-30 16:42).

## ⟦THE RE-CUT⟧ — what changes, and what does not

`ThmA2.thm_a2'_of_rows` grades its three `X`-side sources against ONE decaying right-hand
side, `(log X)^{−1/500}`.  The pool twin replaces that right-hand side by a FREE real `π₀`:

* `hgP1`, `hgRows` — the two GRADING gates, restated at `≤ π₀`;
* `hgU : (log X)^{−θ₂₉₃+ε} ≤ π₀` — **NEW, STATED**, where the landed proof DERIVED
  `(log X)^{−θ₂₉₃+ε} ≤ (log X)^{−1/500}` from `hεwin`.  **`ε` becomes FREE**: the exponent
  room `0 ≤ ε ≤ θ₂₉₃ − 1/500` is no longer a hypothesis of the interface;
* `hgBand : 4096·(log X)^{−1+1/500} ≤ π₀` — **NEW, STATED**, where the landed proof DERIVED
  the same absorption from `hL4096 : 4096 ≤ (log X)^{1−1/250}`.  `hL4096` is DROPPED.

The conclusion's third summand becomes `188133·π₀` — the coefficient is LINEAR in the pool
(`37620·5 + 33`: five copies through the row number, one through the band), so the frozen
five-summand shape is otherwise byte-identical.  Every other summand is untouched.

⚠ ⟦THE χ-FREEDOM SIDE CONDITION⟧ `π₀` is a SCALAR, never a `χ`-indexed family: in
`thm_a2'_of_rows_chiSummed_pool` the pool sits on the `χ`-FREE side of the ⟦φ(q) LEDGER⟧, so
it pays exactly one `φ(q)` like the four other `χ`-free summands.  A per-`χ` pool would break
the single-`φ(q)` payment (KNOT2-SCOPE's note) and is deliberately not offered.

## Contents

* §1 `thm_a2'_of_rows_pool` — the `q = 1` crossing twin at a free pool;
* §2 `thm_a2'_of_rows_chiSummed_pool` — its `Σ_χ` wrapper.

Additive: no landed declaration is touched.  `ThmA2.spine_scale` is `private` to its module,
so §1 carries its own copy (`spine_scale_pool`, same statement, same proof).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

/-! ## §1 — THE `q = 1` INTERFACE, AT A FREE POOL -/

/-- The `π`-arithmetic of the spine's prefactor `1/(2π²)`, isolated (`ThmA2.spine_scale`'s
statement and proof, re-stated here because the original is module-private):
`236365/(2π) ≤ 37620`, `205/(2π) ≤ 33`, `39674880/(2π) ≤ 6315000`. -/
private lemma spine_scale_pool {p Mr Bd w Eg eg : ℝ} (hp1 : 3.141592 < p)
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

/-- **thm_A2′ AT A FREE CONSTANT POOL** (`thm_a2'_of_rows_pool`) — ⟦R2⟧'s crossing twin of
`ThmA2.thm_a2'_of_rows`.  The frozen five-summand interface with the three `X`-side sources
pooled into ONE free real `π₀ ≥ 0`:

  `(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
  `  ≤ 8448·C₁'²·exp(−M₀/e)`
  `   + 1787702400·(log Q₁)^{1/3}/P₁^{1/12}`
  `   + 188133·π₀`
  `   + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)²`
  `   + 6315000/h`.

⟦THE GATE LIST, AGAINST THE LANDED ONE⟧ the frame (`hM`, `hX`, `hX3`, `hh4`, `hhX`, `ha`,
`hsupp`, `hN2`, `hTann`, `hceil`) and the two suppliers (`hrows`, `hT0band`) are VERBATIM.
In place of the landed `hgP1`/`hgRows`/`hεwin`/`hL4096` stand FOUR pool gates:
`hpool : 0 ≤ π₀`, `hgP1`/`hgRows` at `≤ π₀`, and the two gates that were derivations —
`hgU : (log X)^{−θ₂₉₃+ε} ≤ π₀` (so `ε` is FREE: no exponent-room hypothesis survives) and
`hgBand : 4096·(log X)^{−1+1/500} ≤ π₀`.

⟦WHY THE COEFFICIENT IS `188133` AGAIN⟧ the pool enters the row number FIVE times
(`1 + 1 + 3`: `hgP1`, `hgRows`, and the `𝒰`-leg's `3·(log X)^{−θ₂₉₃+ε}`) and the band ONCE,
and the `π`-scaling pays `37620` and `33` for those two channels: `37620·5 + 33 = 188133`.
Setting `π₀ := (log X)^{−1/500}` recovers the landed statement exactly. -/
theorem thm_a2'_of_rows_pool {N M Xd : ℕ} {a : ℕ → ℂ} {X h Cs Ccc C₁' M₀ ε π₀ : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2) ≤ a2Mrow Cs Ccc M Xd X ε)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ t0BandB X C₁' M₀)
    (hpool : 0 ≤ π₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
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
  -- ⟦the row number, graded AT THE POOL⟧ — three sources, `1 + 1 + 3` copies
  have hMrowLe : a2Mrow Cs Ccc M Xd X ε ≤ 47520 * a2Level1 M + 5 * π₀ := by
    unfold a2Mrow
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
    (Mrow := a2Mrow Cs Ccc M Xd X ε) (B₀ := t0BandB X C₁' M₀) (δ := δ) K
    hX hh4 hhX hδ0 hδ1 ha hsupp hN2 hTann hceil hrows hT0band
  refine hspine.trans ?_
  -- monotonicity in `Mrow` and `B₀`, then the `π`-arithmetic
  have hmono : 1 / (2 * Real.pi ^ 2)
        * (236365 * Real.pi * a2Mrow Cs Ccc M Xd X ε
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
    have e1 : 236365 * Real.pi * a2Mrow Cs Ccc M Xd X ε
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
  have hscale := spine_scale_pool (p := Real.pi)
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

/-! ## §2 — THE `Σ_χ` WRAPPER, AT THE SAME POOL

`ThmA2ChiSummed.thm_a2'_of_rows_chiSummed`'s three moves, verbatim, with §1 in move 1.  The
pool is a SCALAR: it rides with the four `χ`-free summands and pays exactly one `φ(q)`. -/

/-- **⟦R2 — THE `Σ_χ` FROZEN INTERFACE AT A FREE POOL⟧** (`thm_a2'_of_rows_chiSummed_pool`).
The character sum of §1's five-summand bound, at a GENERIC `χ`-indexed coefficient family,
INDEXED constant families `Cs Ccc C₁' M₀ ε`, and a **`χ`-FREE pool `π₀`**:

`∑_χ (1/X)∫_X^{2X} ‖(1/h)·S_χ(x)‖² dx`
`  ≤ ∑_χ 8448·C₁'(χ)²·exp(−M₀(χ)/e)`
`   + φ(q)·[ 1787702400·a2Level1 M + 188133·π₀`
`          + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)² + 6315000/h ]`.

⟦THE φ(q) LEDGER — WHY THE POOL MUST NOT BE INDEXED⟧ the ledger's mechanism is
`a2_sum_const_chars`: a summand pays one `φ(q)` exactly when it is `χ`-free.  A per-`χ` pool
`π₀ χ` would land the third summand on the `∑_χ` side with the band head, and the single
`φ(q)` payment of KNOT2-SCOPE's accounting would break.  Hence `π₀ : ℝ`, global.

The per-character gates are `hgP1`/`hgRows` (`∀ χ`, at `≤ π₀`) and the two suppliers; the
frame, `hpool`, `hgU` and `hgBand` are character-blind and stay global — `hgU` reads the
`𝒰`-leg exponent at a `χ`-indexed `ε`, so it too is quantified `∀ χ`. -/
theorem thm_a2'_of_rows_chiSummed_pool {q : ℕ} [NeZero q] {N M Xd : ℕ}
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
        ≤ a2Mrow (Cs χ) (Ccc χ) M Xd X (ε χ))
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA (a χ) (seamS0 N X) t‖ ^ 2)
        ≤ t0BandB X (C₁' χ) (M₀ χ))
    (hpool : 0 ≤ π₀)
    (hgP1 : ∀ χ : DirichletCharacter ℂ q,
      374784 * Cs χ * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : ∀ χ : DirichletCharacter ℂ q,
      5760 * (a2RowsSum M Xd + Ccc χ * (2 / (M : ℝ))) ≤ π₀)
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
  -- ⟦move 1⟧ §1 at each character's OWN datum and OWN constants, at the SHARED pool
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
    have hrow := thm_a2'_of_rows_pool (N := N) (M := M) (Xd := Xd) (a := a χ) (X := X) (h := h)
      (Cs := Cs χ) (Ccc := Ccc χ) (C₁' := C₁' χ) (M₀ := M₀ χ) (ε := ε χ) (π₀ := π₀)
      hM hX hX3 hh4 hhX (ha χ) (hsupp χ) hN2 hTann hceil (hrowsSum χ) (hT0bandSum χ)
      hpool (hgP1 χ) (hgRows χ) (hgU χ) hgBand
    refine le_trans hrow (le_of_eq ?_)
    ring
  -- ⟦move 2⟧ the character sum, then ⟦move 3⟧ the split: `φ(q)` on the four `χ`-free summands
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [a2_sum_head_split]

/-! ## §GK — the G-lever twin

The pooled crossing (§1) and its `χ`-summed sibling (§2) at `G := s13GK K M`.  Conclusions
BYTE-IDENTICAL; the moved slots are `hrows`/`hrowsSum` (at `a2Mrow_gk`), `hgRows` (at
`a2RowsSum_gk`) and `hgP1`'s level-1 `𝒫₁`.  Both are ⟦THE `Ccc`-SHIFT⟧
(`ThmA2.a2Mrow_shift_gk`) applied to the landed theorem — no estimate is re-run. -/

/-- **thm_A2′ AT THE FREE POOL, AT THE G-LEVER** (`thm_a2'_of_rows_pool_gk`). -/
theorem thm_a2'_of_rows_pool_gk (K : ℕ) {N M Xd : ℕ} {a : ℕ → ℂ}
    {X h Cs Ccc C₁' M₀ ε π₀ : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
        ≤ a2Mrow_gk K Cs Ccc M Xd X ε)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ t0BandB X C₁' M₀)
    (hpool : 0 ≤ π₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
    (hgU : (Real.log X) ^ (-theta293 + ε) ≤ π₀)
    (hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
      ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1 M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h := by
  refine thm_a2'_of_rows_pool (Xd := Xd) (Cs := Cs)
    (Ccc := Ccc + (M : ℝ) / 2 * (a2RowsSum_gk K M Xd - a2RowsSum M Xd))
    hM hX hX3 hh4 hhX ha hsupp hN2 hTann hceil ?_ hT0band hpool ?_ ?_ hgU hgBand
  · intro T h1 h2 h3 h4
    exact (hrows T h1 h2 h3 h4).trans
      (le_of_eq (a2Mrow_shift_gk K Cs Ccc (M := M) Xd X ε hM).symm)
  · rw [← calP_door_one_gk (K := K)]
    exact hgP1
  · rw [a2RowsSum_shift_gk K Ccc (M := M) Xd hM]
    exact hgRows

/-- **thm_A2′ χ-SUMMED AT THE FREE POOL, AT THE G-LEVER**
(`thm_a2'_of_rows_chiSummed_pool_gk`). -/
theorem thm_a2'_of_rows_chiSummed_pool_gk (K : ℕ) {q : ℕ} [NeZero q] {N M Xd : ℕ}
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
        ≤ a2Mrow_gk K (Cs χ) (Ccc χ) M Xd X (ε χ))
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA (a χ) (seamS0 N X) t‖ ^ 2)
        ≤ t0BandB X (C₁' χ) (M₀ χ))
    (hpool : 0 ≤ π₀)
    (hgP1 : ∀ χ : DirichletCharacter ℂ q,
      374784 * Cs χ * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : ∀ χ : DirichletCharacter ℂ q,
      5760 * (a2RowsSum_gk K M Xd + Ccc χ * (2 / (M : ℝ))) ≤ π₀)
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
  refine thm_a2'_of_rows_chiSummed_pool (Xd := Xd) (Cs := Cs) (Ccc := fun χ =>
      Ccc χ + (M : ℝ) / 2 * (a2RowsSum_gk K M Xd - a2RowsSum M Xd))
    hM hX hX3 hh4 hhX ha hsupp hN2 hTann hceil ?_ hT0bandSum hpool ?_ ?_ hgU hgBand
  · intro χ T h1 h2 h3 h4
    exact (hrowsSum χ T h1 h2 h3 h4).trans
      (le_of_eq (a2Mrow_shift_gk K (Cs χ) (Ccc χ) (M := M) Xd X (ε χ) hM).symm)
  · intro χ
    rw [← calP_door_one_gk (K := K)]
    exact hgP1 χ
  · intro χ
    rw [a2RowsSum_shift_gk K (Ccc χ) (M := M) Xd hM]
    exact hgRows χ

-- #audit (temporary)

end Salt.MR
