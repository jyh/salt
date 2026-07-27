/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SeamCalibrationK

/-!
# `TypicalPriceK` — the `p²`-row K-copies: the seam row's `Σ_j lemma12Rows` FULLY priced

`TypicalPrice`'s pricing wire (`lemma12Rows_priced`, `lemma12Rows_priced_ratio`,
`sum_lemma12Rows_priced`) prices `TLegExit.lemma12Rows`' second row through
`TypicalPrice.ramP2mass_win_le` — the `Σf² ≤ (Σf)²` route, whose grade is `64/P²`.
⟦V9b⟧ finding (ii), recorded in `TypicalPrice`'s own header: **that grade is useless at the
seam's scales.**  `CalFrameK.Q_le_Xd` forces `X_d ≥ Q_{Jb} ≥ Q_j = P_j^{j²M}`, so against
`lemma12Rows`' prefactor `2T + 20N ≍ X_d(T/X_d+1)` the row contributes
`64·X_d/P_j²·(T/X_d+1) ≥ 64` at EVERY level — an `O(1)` row inside a bound whose entire
purpose is to be small.

`SeamCalibrationK.ramP2mass_direct` (K-2) repairs the grade: the direct route
`Σ_n f_n² ≤ (max_n f_n)(Σ_n f_n)` with `f_n := ‖coeff_n‖/n`, `max_n f_n ≤ 2log₂(2X_d)/X_d`
and `Σ_n f_n ≤ 8/P`, returning `16·log₂(2X_d)/(X_d·P)` — MR's own `1/P` grade with only a
logarithm lost.  **This file is the wire that consumes it.**

## The device: the verbatim transplant, ONE call swapped

Each theorem here is its `TypicalPrice` original with a single line changed —
`ramP2mass_win_le` becomes `ramP2mass_direct` — and the resulting number carried through
the same three regroupings.  Nothing else moves: the hypotheses are byte-identical (the
direct route assumes exactly what the window route assumed — `ramP2mass_direct`'s own
docstring: "Every hypothesis is `ramP2mass_win_le`'s own"), the density engine
(`blockfree_sum_le`) is untouched, and `TypicalPrice` itself is not modified (⟦V9b⟧'s
parallel-family ruling: the landed exits stay landed, at the landed grade).

`TypicalPrice`'s four private helpers (`card_dvd_window_le`, `winTerm_inner_row_le`,
`winTerm_dom_sum_le`, and the fiber ledger) are **not** needed here: they are already paid
for inside `SeamCalibrationK`'s own private re-derivations, and `ramP2mass_direct` is public.
The transplant is therefore at the STATEMENT layer only.

## The exits

* `lemma12Rows_pricedK` — the row as a number, `p²`-term `16·log₂(2X_d)/(X_d·P)`.
* `lemma12Rows_priced_ratioK` — the same at MR §8's `(T/X_d+1)` grade.  The `p²`-term is
  `X_d·16·log₂(2X_d)/(X_d·P) = 16·log₂(2X_d)/P`, so the row's `p²` contribution is

    `7680·log₂(2X_d)/P·(T/X_d + 1)`,

  in place of the landed `480·64·X_d/P²·(T/X_d+1)`.  At the K-ladder's `X_d ≥ P_j^{j²M}`
  the exchange is `≥ 64` for `≈ log₂(2X_d)/P_j` — MR's grade, per level.
* `sum_lemma12Rows_pricedK` — the `j`-collection at a GENERIC ladder (as in `TypicalPrice`,
  the ratio `Σ_j log P_j/log Q_j` is left symbolic on the right, so any re-pin plugs in).
* `sum_lemma12Rows_priced_calibratedK2` — **THE FULLY-PRICED NUMBER**: the `j`-collection at
  the K-family `(calP A G, calQK A G M, calH H1)`, with BOTH small grades in place —
  the density collection at `C·(2/M)` (`SeamCalibrationK.sum_ratioK_le`) and the `p²` row at
  `16·log₂(2X_d)/P_j`.  `SeamCalibrationK.sum_lemma12Rows_priced_calibratedK` is this same
  theorem at the OLD `p²` grade; that one is the K-ladder's density statement, this one is
  the K-ladder's whole seam row.

Law #253 throughout: every growing quantity (`T`, `N`, `X_d`, `log₂(2X_d)`, `Jb`, `M`) is
in-statement; no threshold is hidden, and no gate is added to `TypicalPrice`'s own list.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 p.6, §8.2 p.27, §9 p.31;
`docs/sources/mr_extract.md` §6.4, §6.6, §6.7; `docs/exploration/hsup-design.md` ⟦V9⟧,
⟦V9b⟧ finding (ii), ⟦V9c⟧ K-2/K-4.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the row as a number, at MR's `p²` grade -/

/-- **THE ROW, PRICED AT MR's `p²` GRADE** (`lemma12Rows_pricedK`).
`TypicalPrice.lemma12Rows_priced` with its `ramP2mass_win_le` call replaced by
`SeamCalibrationK.ramP2mass_direct`:

* row 1 (the window error) — `(2e·X_d/H + 1)(e/X_d²)`, carried verbatim;
* row 2 (the `p²` correction) — `16·log₂(2X_d)/(X_d·P)` (was `64/P²`);
* row 3 (the block-free mass) — `C(log P/log Q)/X_d + 1/X_d²` (`blockfree_sum_le`).

The hypothesis list is `lemma12Rows_priced`'s, unchanged: `ramP2mass_direct` assumes exactly
what `ramP2mass_win_le` assumed (`1 ≤ X_d`, `1 ≤ P`, the three `1`-bounds, the support of
`a` in `[X_d, 2X_d]`, and `hwin`), and the density gates are `blockfree_sum_le`'s own. -/
theorem lemma12Rows_pricedK :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q N Xd : ℕ) (H T : ℝ) (a b c : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd → 0 ≤ T →
      Real.log Q ≤ Real.sqrt (Real.log Xd) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      (∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      lemma12Rows N Xd P Q H T a b c
        ≤ 6 * (2 * T + 20 * (N : ℝ))
            * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
                + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))
                + (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)) := by
  obtain ⟨C, hC, hbf⟩ := blockfree_sum_le
  refine ⟨C, hC, ?_⟩
  intro P Q N Xd H T a b c hP hPQ hXd hT hreg hbig herr ha hb hc hasupp hwin
  -- `hwin` in ℕ shape, for `ramP2mass_direct`
  have hwinN : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      Xd ≤ p * m ∧ p * m ≤ 2 * Xd := by
    intro p m hp hP1 hQ1 hne
    obtain ⟨h1, h2⟩ := hwin p m hp hP1 hQ1 hne
    constructor
    · have h : (Xd : ℝ) ≤ ((p * m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
    · have h : ((p * m : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
  have hpre : (0 : ℝ) ≤ 2 * T + 20 * (N : ℝ) := by positivity
  -- ⟦THE ONE SWAPPED CALL⟧ `ramP2mass_direct` in place of `ramP2mass_win_le`
  have h2 := ramP2mass_direct N P Q Xd hXd (by omega) a b c ha hb hc hasupp hwinN
  have h3 := hbf P Q Xd N a hP hPQ hXd hreg hbig herr ha hasupp
  have e2 := mul_le_mul_of_nonneg_left h2 hpre
  have e3 := mul_le_mul_of_nonneg_left h3 hpre
  rw [lemma12Rows]
  nlinarith [e2, e3]

/-- **THE `(T/X_d + 1)` EXIT AT MR's `p²` GRADE** (`lemma12Rows_priced_ratioK`).
`TypicalPrice.lemma12Rows_priced_ratio`'s regrouping, run on `lemma12Rows_pricedK`: `N ≤ 4X_d`
turns `6(2T + 20N)` into `480·X_d·(T/X_d + 1)`, and the `X_d` distributes into the bracket.
The `p²` term becomes

  `X_d · 16·log₂(2X_d)/(X_d·P) = 16·log₂(2X_d)/P`,

so the row's `p²` contribution is `7680·log₂(2X_d)/P·(T/X_d+1)` — MR's own `(T/X+1)/P` grade
(one logarithm lost), in place of the landed `480·64·X_d/P²·(T/X_d+1)`, which the K-ladder's
`X_d ≥ P²` pins at `≥ 30720·(T/X_d+1)`. -/
theorem lemma12Rows_priced_ratioK :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q N Xd : ℕ) (H T : ℝ) (a b c : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd → 0 ≤ T → 0 < H → (N : ℝ) ≤ 4 * (Xd : ℝ) →
      Real.log Q ≤ Real.sqrt (Real.log Xd) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      (∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      lemma12Rows N Xd P Q H T a b c
        ≤ 480 * (T / (Xd : ℝ) + 1)
            * ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 16 * Real.logb 2 (2 * (Xd : ℝ)) / (P : ℝ)
                + C * (Real.log P / Real.log Q)
                + 1 / (Xd : ℝ)) := by
  obtain ⟨C, hC, hrow⟩ := lemma12Rows_pricedK
  refine ⟨C, hC, ?_⟩
  intro P Q N Xd H T a b c hP hPQ hXd hT hH hN4 hreg hbig herr ha hb hc hasupp hwin
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by linarith
  have hXdne : (Xd : ℝ) ≠ 0 := ne_of_gt hXd0
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have h : 0 < P := by omega
    exact_mod_cast h
  have hPne : (P : ℝ) ≠ 0 := ne_of_gt hP0
  have hlogP : (0 : ℝ) ≤ Real.log (P : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hP)
  have hlogQ : (0 : ℝ) < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by omega : 1 < P) hPQ)
  have hratio : (0 : ℝ) ≤ Real.log (P : ℝ) / Real.log (Q : ℝ) := by positivity
  -- the `log₂(2X_d)` atom is nonneg, but `positivity` has no `logb` extension: supply it
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hp2nn : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)) :=
    div_nonneg (by linarith) (by positivity)
  have hBnn : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
      + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))
      + (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2) := by
    have hb1 : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2) := by
      positivity
    have hb3 : (0 : ℝ) ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2 := by
      positivity
    linarith
  have hcoefle : 6 * (2 * T + 20 * (N : ℝ)) ≤ 480 * (Xd : ℝ) * (T / (Xd : ℝ) + 1) := by
    have hTid : (Xd : ℝ) * (T / (Xd : ℝ)) = T := by field_simp
    nlinarith [hN4, hT, hXd0]
  have hstep := hrow P Q N Xd H T a b c hP hPQ hXd hT hreg hbig herr ha hb hc hasupp hwin
  refine hstep.trans ?_
  have hmul := mul_le_mul_of_nonneg_right hcoefle hBnn
  refine hmul.trans (le_of_eq ?_)
  field_simp
  ring

/-! ## §2 — the `j`-collection, generic ladder -/

/-- **THE `j`-COLLECTION AT MR's `p²` GRADE** (`sum_lemma12Rows_pricedK`).
`TypicalPrice.sum_lemma12Rows_priced` run on `lemma12Rows_priced_ratioK`.  As there, the
ladder is GENERIC and the density collection `Σ_j log P_j/log Q_j` is left symbolic on the
right — so any re-pin (in particular `SeamCalibrationK`'s `calQK`) plugs straight in.  The
`p²` row is now `16·log₂(2X_d)/P_j` per level, inside the same `j`-sum. -/
theorem sum_lemma12Rows_pricedK :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ) (Jb N Xd : ℕ) (T : ℝ)
      (a b c : ℕ → ℂ),
      1 ≤ Xd → 0 ≤ T → (N : ℝ) ≤ 4 * (Xd : ℝ) →
      (∀ j ∈ Finset.Icc 1 Jb, 2 ≤ Pseq j ∧ Pseq j ≤ Qseq j ∧ 0 < Hseq j) →
      (∀ j ∈ Finset.Icc 1 Jb, Real.log (Qseq j : ℝ) ≤ Real.sqrt (Real.log Xd)) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      (∀ j ∈ Finset.Icc 1 Jb,
        ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand (Pseq j) (Qseq j), (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log (Pseq j : ℝ) / Real.log (Qseq j : ℝ))) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j → c p * b m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      ∑ j ∈ Finset.Icc 1 Jb, lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T a b c
        ≤ 480 * (T / (Xd : ℝ) + 1)
            * ((∑ j ∈ Finset.Icc 1 Jb,
                  ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1)
                      * (Real.exp 1 / (Xd : ℝ) ^ 2))
                    + 16 * Real.logb 2 (2 * (Xd : ℝ)) / (Pseq j : ℝ)
                    + 1 / (Xd : ℝ)))
              + C * ∑ j ∈ Finset.Icc 1 Jb,
                  Real.log (Pseq j : ℝ) / Real.log (Qseq j : ℝ)) := by
  obtain ⟨C, hC, hrow⟩ := lemma12Rows_priced_ratioK
  refine ⟨C, hC, ?_⟩
  intro Pseq Qseq Hseq Jb N Xd T a b c hXd hT hN4 hgates hreg hbig herr ha hb hc hasupp hwin
  have hlevel : ∀ j ∈ Finset.Icc 1 Jb,
      lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T a b c
        ≤ 480 * (T / (Xd : ℝ) + 1)
            * ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1)
                  * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 16 * Real.logb 2 (2 * (Xd : ℝ)) / (Pseq j : ℝ)
                + 1 / (Xd : ℝ)
                + C * (Real.log (Pseq j : ℝ) / Real.log (Qseq j : ℝ))) := by
    intro j hj
    obtain ⟨hP, hPQ, hH⟩ := hgates j hj
    exact (hrow (Pseq j) (Qseq j) N Xd (Hseq j) T a b c hP hPQ hXd hT hH hN4 (hreg j hj) hbig
      (herr j hj) ha hb hc hasupp (hwin j hj)).trans (le_of_eq (by ring))
  refine (Finset.sum_le_sum hlevel).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ## §3 — K-4 completed: the seam row's `Σ_j lemma12Rows` AS A FULLY-PRICED NUMBER -/

/-- **THE FULLY-PRICED SEAM ROW** (`sum_lemma12Rows_priced_calibratedK2`).

`sum_lemma12Rows_pricedK` at the K-family `P_j := calP A G j`, `Q_j := calQK A G M j`,
`H_j := calH H1 j`, with BOTH small grades in place:

* the density collection is `C·(2/M)` (`SeamCalibrationK.sum_ratioK_le`: `Σ_j 1/(j²M) ≤ 2/M`,
  uniform in the cutoff `Jb`) — this is what `eq28_clears_of_M` certifies against MR §9's
  demand;
* the `p²` row is `16·log₂(2X_d)/P_j` per level (`ramP2mass_direct`) — MR's `1/P` grade, in
  place of `64·X_d/P_j²`, which the frame's `Q_le_Xd` pins at `≥ 64` per level.

`SeamCalibrationK.sum_lemma12Rows_priced_calibratedK` is this theorem at the OLD `p²` grade:
it is the K-ladder's DENSITY statement.  This one is the K-ladder's WHOLE seam row — every
one of the three rows a number that goes to zero with the parameters. -/
theorem sum_lemma12Rows_priced_calibratedK2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (A G M Jb N Xd : ℕ) (H1 T : ℝ) (a b c : ℕ → ℂ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 1 ≤ Xd → 0 ≤ T → 0 < H1 → (N : ℝ) ≤ 4 * (Xd : ℝ) →
      (∀ j ∈ Finset.Icc 1 Jb,
        Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log Xd)) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      (∀ j ∈ Finset.Icc 1 Jb,
        ((Nat.sqrt Xd : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ)
            * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ))) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
        c p * b m ≠ 0 → (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      ∑ j ∈ Finset.Icc 1 Jb,
          lemma12Rows N Xd (calP A G j) (calQK A G M j) (calH H1 j) T a b c
        ≤ 480 * (T / (Xd : ℝ) + 1)
            * ((∑ j ∈ Finset.Icc 1 Jb,
                  ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                      * (Real.exp 1 / (Xd : ℝ) ^ 2))
                    + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                    + 1 / (Xd : ℝ)))
              + C * (2 / (M : ℝ))) := by
  obtain ⟨C, hC, hsum⟩ := sum_lemma12Rows_pricedK
  refine ⟨C, hC, ?_⟩
  intro A G M Jb N Xd H1 T a b c hA hG hM hXd hT hH1 hN4 hreg hbig herr ha hb hc hasupp hwin
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hgates : ∀ j ∈ Finset.Icc 1 Jb,
      2 ≤ calP A G j ∧ calP A G j ≤ calQK A G M j ∧ 0 < calH H1 j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hE : 0 < calE A G j := by
      rw [calE]
      exact Nat.mul_pos (Nat.mul_pos hA (pow_pos hG (j - 1)))
        (pow_pos (Nat.factorial_pos j) 2)
    refine ⟨?_, calP_le_calQK hM hj.1, ?_⟩
    · rw [calP]
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ calE A G j := Nat.pow_le_pow_right (by norm_num) hE
    · rw [calH]
      have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
      positivity
  have h := hsum (calP A G) (calQK A G M) (calH H1) Jb N Xd T a b c hXd hT hN4 hgates hreg
    hbig herr ha hb hc hasupp hwin
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · have hratio := sum_ratioK_le hA hG hM Jb
    have := mul_le_mul_of_nonneg_left hratio hC.le
    linarith
  · have hT0 : (0 : ℝ) ≤ T / (Xd : ℝ) := div_nonneg hT hXd0.le
    linarith

end Salt.MR
