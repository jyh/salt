/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SeamRowWindowed
import Salt.MR.M4P2MR

/-!
# `M4RowMR` — ⟦WALL 1⟧'s row: Lemma 12's FOUR rows, and their price, WITHOUT `hwin`

⟦WALL 1⟧ (`M4DoorRow` §6, `band_window_ratio_lock`).  The capstone's K-block binder pair

```
hcoefBand : … ∀ p m, p prime → 𝒫_j ≤ p ≤ 𝒬K_j → ¬p∣m → X_d ≤ pm ≤ 2X_d →
              a (p·m) = bfam j m · cf p
hwinBand  : … ∀ p m, p prime → 𝒫_j ≤ p ≤ 𝒬K_j → cf p · bfam j m ≠ 0 → X_d ≤ pm ≤ 2X_d
```

locks any two block primes at which the datum is live into a factor `2` of each other, and
the door's level-1 block spans `2^{(M−1)·2^18}`.  So `hwinBand` is UNINHABITABLE at the door
datum, and the repair is the one the pin chain already took (`M4MeanSq` §3″): **delete the
window law and price the rows through MR's own cofactor range**, where the window lives in
the INDEX SET (`RamareMR.ramHonMR`) instead of in a joint-support hypothesis.

## THE FOUR ROWS (§1–§2)

`SeamRowWindowed.ramErr_moment_split_mr_windowed` splits the SAME `ramErr` object at the
relativized pair `SeamCoefW` alone, into FOUR rows instead of three, at prefactor `4`
instead of `3`:

* the two seam windows `ramSeamLoPoly`/`ramSeamUpPoly` (MR p.20 pays the second one honestly
  — it is what `hwin` used to zero by fiat);
* the `p²` correction at MR's own domain (`ramP2coeffMR`), priced by `M4P2MR`'s
  `ramP2massMR_direct` — `16·log₂(2X_d)/(X_d·P)`, `hwin`-free;
* the coprime tail, priced by `TypicalDensity.blockfree_sum_le` — `hwin`-free already.

`lemma12RowsMR` names the four rows exactly as `TLegExit.lemma12Rows` names the three, and
`lemma12_meansq_on_subset_mr_windowed` is `USetThin.lemma12_meansq_on_subset`'s proof with
the windowed split in place of the unwindowed one.  It GAINS `hasupp` (MR's dyadic support,
which the split reads) and LOSES `hwin`.

## THE PRICE (§3–§5)

`TypicalPriceK`'s three-stage wire, run on the four rows.  The extra row costs a factor `2`
(`SeamRowWindowed.second_window_le_first_row`: the second window is at most twice the first)
and the split's `3 → 4` another `4/3`; against that, the first row LOSES a factor `e`
(the windowed split's row is `(2eX_d/H+1)/X_d²`, the unwindowed one
`(2eX_d/H+1)·(e/X_d²)`).  Net: `6 → 12` at the raw exit and

  `480 → 960`  at the `(T/X_d + 1)` exit,

which is HALF of ⟦AMENDMENT G⟧'s `×4` cover — `ThmA2.a2Mrow` prices the row summand at
`5760 = 4·1440`, and `960·3 = 2880 ≤ 5760`, so the interface numeral does not move.

## ⚠ THE TRAPS

* the four log scales — `Real.logb 2` is the `p²` row's own, `Real.log` the density ratio's;
* the windowed split needs `2 ≤ H` (the second-window comparison) where the unwindowed one
  needed only `0 < H`;
* `2X_d ≤ N` is now load-bearing at the ROW (it was only at the frame): both
  `ramP2massMR_direct` and `second_window_le_first_row` read it.
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §1 — LEMMA 12's FOUR ERROR ROWS, NAMED -/

/-- **Lemma 12's FOUR error rows at one level**, exactly as the windowed split emits them —
`TLegExit.lemma12Rows`' sibling at `SeamRowWindowed.ramErr_moment_split_mr_windowed`.  Two
changes: the second seam window is a row of its own (MR p.20, paid instead of assumed), and
the `p²` row is at MR's own coefficient `ramP2coeffMR`.  The def unfolds by `rfl`. -/
def lemma12RowsMR (N Xd P Q : ℕ) (H T : ℝ) (a b c : ℕ → ℂ) : ℝ :=
  2 * (4 * ((2 * T + 20 * (N : ℝ))
              * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2)
          + (2 * T + 80 * (Xd : ℝ))
              * ((4 * Real.exp 1 * (Xd : ℝ) / H + 1) / (2 * (Xd : ℝ)) ^ 2)
          + (2 * T + 20 * (N : ℝ))
              * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N Xd P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
          + (2 * T + 20 * (N : ℝ))
              * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
                  ‖a n‖ ^ 2 / (n : ℝ) ^ 2))

/-- The capstone carries its dyadic support pin in ℕ; the split reads it in ℝ. -/
theorem hasupp_real_of_nat {a : ℕ → ℂ} {Xd : ℕ}
    (h : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) :
    ∀ n : ℕ, a n ≠ 0 → (Xd : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (Xd : ℝ) := by
  intro n hn
  obtain ⟨h1, h2⟩ := h n hn
  constructor
  · exact_mod_cast h1
  · have : ((n : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this
    linarith

/-! ## §2 — THE ON-SUBSET MR ROW -/

/-- **THE ON-SUBSET MR ROW** (`lemma12_meansq_on_subset_mr_windowed`).
`USetThin.lemma12_meansq_on_subset`'s proof with `SeamRowWindowed`'s four-row windowed split
and its four moments in place of the three.  Against the landed row: `hwin` is GONE and
`hcoef` is the relativized `SeamCoefW`; `hasupp` (MR's dyadic support) is GAINED, and it is
a binder the S8 datum carries anyway. -/
theorem lemma12_meansq_on_subset_mr_windowed (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hP : 1 ≤ P) (a b c : ℕ → ℂ) (hcoefW : SeamCoefW X P Q a b c)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (T : ℝ) (hT : 0 ≤ T) (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T) :
    (∫ t in A, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in A, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + lemma12RowsMR N X P Q H T a b c := by
  rw [lemma12RowsMR]
  refine meansq_on_subset_of_decomp hT hAm hAsub
    (fun j _ => continuous_ramMain H N X P Q b c j) (continuous_ramErr H N X P Q a b c)
    (fun t => spoly_ram_decomp H N X P Q a b c t) ?_
  refine (ramErr_moment_split_mr_windowed H hH N X P Q hX hN hP a b c hcoefW hasupp T hT).trans
    ?_
  gcongr
  · exact ramSeamLoPoly_moment H hH N X P Q hX hN hP b c hb hc T hT
  · exact ramSeamUpPoly_moment H hH N X P Q hX hP b c hb hc T hT
  · exact ramP2corrMR_moment N X P Q hX hN a b c T
  · exact ramCopTail_moment N P Q a T

/-- **THE MR ROW ON `A_j`** (`lemma12_on_TsetG_mr_windowed`) — `TLegPreamble.lemma12_on_TsetG`'s
sibling: §2 at the level-`j` window set, in exactly the shape the graded `𝒯`-leg consumes. -/
theorem lemma12_on_TsetG_mr_windowed (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
    (Jb j : ℕ) (hH : 2 ≤ Hseq j) (N Xd : ℕ) (hX : 1 ≤ Xd) (hN : 2 * Xd ≤ N)
    (hP : 1 ≤ Pseq j) (a b c : ℕ → ℂ)
    (hcoefW : SeamCoefW Xd (Pseq j) (Qseq j) a b c)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (Xd : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (Xd : ℝ))
    (X T t₁ : ℝ) (hT : 0 ≤ T) :
    (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG fb Pseq Qseq Hseq αseq Jb j,
        ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
          * (∑ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
              ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG fb Pseq Qseq Hseq αseq Jb j,
                ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
        + lemma12RowsMR N Xd (Pseq j) (Qseq j) (Hseq j) T a b c :=
  lemma12_meansq_on_subset_mr_windowed (Hseq j) hH N Xd (Pseq j) (Qseq j) hX hN hP a b c
    hcoefW hb hc hasupp T hT _
    (measurableSet_annulus_TsetG fb Pseq Qseq Hseq αseq Jb j X T t₁)
    (annulus_TsetG_subset_Icc fb Pseq Qseq Hseq αseq Jb j X T t₁)

/-! ## §3 — THE ROW AS A NUMBER, AT MR's `p²` GRADE -/

/-- The four-row regrouping, as bare arithmetic: with the second window at most twice the
first (`h2`), the first at HALF the landed bracket (`h1` — the factor `e` the windowed split
saves), and the two mass rows priced, the whole row fits the single prefactor `12`. -/
private lemma four_rows_le {pre R1 R2 R3 R4 B1 B2 B3 : ℝ}
    (h2 : R2 ≤ 2 * R1) (h1 : 2 * R1 ≤ pre * B1)
    (h3 : R3 ≤ pre * B2) (h4 : R4 ≤ pre * B3)
    (_hR1 : 0 ≤ R1) (hR3 : 0 ≤ R3) (hR4 : 0 ≤ R4) :
    2 * (4 * (R1 + R2 + R3 + R4)) ≤ 12 * pre * (B1 + B2 + B3) := by
  linarith

/-- **THE MR ROW, PRICED** (`lemma12RowsMR_pricedK`).  `TypicalPriceK.lemma12Rows_pricedK`'s
transplant onto the four rows, with `hwin` GONE:

* rows 1+2 (the two seam windows) — `second_window_le_first_row` collapses the second onto
  twice the first, so `row₁ + row₂ ≤ 3·row₁`, and `row₁`'s bracket is a factor `e` BELOW the
  landed row's `(2e·X_d/H + 1)(e/X_d²)`;
* row 3 (the `p²` correction) — `M4P2MR.ramP2massMR_direct`, `16·log₂(2X_d)/(X_d·P)`;
* row 4 (the block-free mass) — `TypicalDensity.blockfree_sum_le`, unchanged.

`8·3/e ≤ 12` and `8 ≤ 12` give the single prefactor `12` (the landed row's is `6`). -/
theorem lemma12RowsMR_pricedK :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q N Xd : ℕ) (H T : ℝ) (a b c : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → 2 ≤ H →
      Real.log Q ≤ Real.sqrt (Real.log Xd) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      lemma12RowsMR N Xd P Q H T a b c
        ≤ 12 * (2 * T + 20 * (N : ℝ))
            * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
                + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))
                + (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)) := by
  obtain ⟨C, hC, hbf⟩ := blockfree_sum_le
  refine ⟨C, hC, ?_⟩
  intro P Q N Xd H T a b c hP hPQ hXd hN hT hH hreg hbig herr ha hb hc hasupp
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by linarith
  have hNR : 2 * (Xd : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpre : (0 : ℝ) ≤ 2 * T + 20 * (N : ℝ) := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    linarith
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hH0 : (0 : ℝ) < H := by linarith
  -- ⟦ROW 1 + ROW 2⟧ the second window costs at most twice the first
  have hwin2 := second_window_le_first_row (H := H) (T := T) (Nr := (N : ℝ)) (X := Xd)
    hH hXd hT hNR
  -- ⟦ROW 1⟧ the windowed bracket is a factor `e ≥ 2` below the landed one
  have hrow1nn : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2 := by positivity
  have hrow1 : 2 * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2)
      ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2) := by
    have hid : (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
        - 2 * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2)
        = (Real.exp 1 - 2) * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2) := by
      field_simp
    have hnn : (0 : ℝ)
        ≤ (Real.exp 1 - 2) * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2) :=
      mul_nonneg (by linarith) hrow1nn
    linarith [hid.le, hid.ge, hnn]
  -- ⟦ROW 3⟧ the `p²` mass, `hwin`-free
  have hp2 := ramP2massMR_direct N Xd P Q hXd hN (by omega) a b c ha hb hc
  have hp2nn : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N,
      ‖ramP2coeffMR N Xd P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun n _ => by positivity)
  -- ⟦ROW 4⟧ the block-free mass
  have hbfr := hbf P Q Xd N a hP hPQ hXd (densGate_of_sqrt (le_trans hP hPQ) hreg hbig)
    herr ha hasupp
  have hbfnn : (0 : ℝ) ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
      ‖a n‖ ^ 2 / (n : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun n _ => by positivity)
  -- the four rows, regrouped
  rw [lemma12RowsMR]
  refine four_rows_le hwin2 ?_ (mul_le_mul_of_nonneg_left hp2 hpre)
    (mul_le_mul_of_nonneg_left hbfr hpre) (mul_nonneg hpre hrow1nn) (mul_nonneg hpre hp2nn)
    (mul_nonneg hpre hbfnn)
  have h := mul_le_mul_of_nonneg_left hrow1 hpre
  linarith

/-- **THE `(T/X_d + 1)` EXIT** (`lemma12RowsMR_priced_ratioK`).
`TypicalPriceK.lemma12Rows_priced_ratioK`'s regrouping, run on §3: `N ≤ 4X_d` turns
`12(2T + 20N)` into `960·X_d·(T/X_d + 1)`, and the `X_d` distributes into the bracket. -/
theorem lemma12RowsMR_priced_ratioK :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q N Xd : ℕ) (H T : ℝ) (a b c : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → 2 ≤ H → (N : ℝ) ≤ 4 * (Xd : ℝ) →
      Real.log Q ≤ Real.sqrt (Real.log Xd) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      lemma12RowsMR N Xd P Q H T a b c
        ≤ 960 * (T / (Xd : ℝ) + 1)
            * ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 16 * Real.logb 2 (2 * (Xd : ℝ)) / (P : ℝ)
                + C * (Real.log P / Real.log Q)
                + 1 / (Xd : ℝ)) := by
  obtain ⟨C, hC, hrow⟩ := lemma12RowsMR_pricedK
  refine ⟨C, hC, ?_⟩
  intro P Q N Xd H T a b c hP hPQ hXd hN hT hH hN4 hreg hbig herr ha hb hc hasupp
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
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hp2nn : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)) :=
    div_nonneg (by linarith) (by positivity)
  have hBnn : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
      + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))
      + (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2) := by
    have hH0 : (0 : ℝ) < H := by linarith
    have hb1 : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2) := by
      positivity
    have hb3 : (0 : ℝ) ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2 := by
      positivity
    linarith
  have hcoefle : 12 * (2 * T + 20 * (N : ℝ)) ≤ 960 * (Xd : ℝ) * (T / (Xd : ℝ) + 1) := by
    have hTid : (Xd : ℝ) * (T / (Xd : ℝ)) = T := by field_simp
    nlinarith [hN4, hT, hXd0]
  have hstep := hrow P Q N Xd H T a b c hP hPQ hXd hN hT hH hreg hbig herr ha hb hc hasupp
  refine hstep.trans ?_
  have hmul := mul_le_mul_of_nonneg_right hcoefle hBnn
  refine hmul.trans (le_of_eq ?_)
  field_simp
  ring

/-! ## §3′ — ⟦THE ENDPOINT WALL⟧: the STRICT/FUSED row, and ⟦AMENDMENT 1⟧'s absorption

The row side of the endpoint repair.  `SeamRowWindowed` §3′ re-cuts the split at the STRICT
pair law `SeamCoefWS` and fuses the released endpoint cofactors into the `p²` row
(`ramP2coeffEndMR`); `M4P2MR.ramP2massEndMR_direct` prices that row at

  `16·log₂(2X_d)/(X_d·P) + 4·(log₂(2X_d))²/X_d²`.

⟦AMENDMENT 1 — WHERE THE CRUMB LANDS⟧.  It does NOT go to the register grading conjunct (that
conjunct is carried, never discharged — strengthening it costs no proof and pays nothing) and
it does NOT go to `ThmA2.a2Mrow`'s frozen five-summand interface.  It is absorbed HERE, at
`four_rows_le`'s own slack: the landed regrouping spends `8` of its `12` on the `B2` slot, an
exact `1.5×` unspent factor.  `four_rows_le_end` restates that slot as `R3 ≤ pre·(3/2)·B2`
(and `8·3/2 = 12` closes the `linarith` tight), and the endpoint mass fits inside the half —

  `4L²/X_d² ≤ (1/2)·16L/(X_d·P)`   ⟺   **`log₂(2X_d)·P ≤ 2·X_d`**,

which `logb_two_mul_P_le` derives from the row's EXISTING binders `hP`/`hPQ`/`hreg`/`hbig`:
`P ≤ e^{√u}`, `L ≤ (3/2)u`, and `(3/2)u·e^{√u} ≤ 2e^u` (one `Real.add_one_le_exp`).  So
`lemma12RowsMR_pricedK_end`'s right-hand side is `lemma12RowsMR_pricedK`'s BYTE FOR BYTE, and
every downstream bracket — `_priced_ratioK`, `_calibratedK2`, `ThmA2.a2RowsSum` — is
untouched. -/

/-- **Lemma 12's FOUR error rows at the STRICT pair** — `lemma12RowsMR` with the fused `p²`
coefficient.  Rows 1, 2 and 4 are byte-identical. -/
def lemma12RowsMR_end (N Xd P Q : ℕ) (H T : ℝ) (a b c : ℕ → ℂ) : ℝ :=
  2 * (4 * ((2 * T + 20 * (N : ℝ))
              * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2)
          + (2 * T + 80 * (Xd : ℝ))
              * ((4 * Real.exp 1 * (Xd : ℝ) / H + 1) / (2 * (Xd : ℝ)) ^ 2)
          + (2 * T + 20 * (N : ℝ))
              * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffEndMR N Xd P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
          + (2 * T + 20 * (N : ℝ))
              * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
                  ‖a n‖ ^ 2 / (n : ℝ) ^ 2))

/-- **THE ON-SUBSET MR ROW, STRICT/FUSED** (`lemma12_meansq_on_subset_mr_windowed_end`). -/
theorem lemma12_meansq_on_subset_mr_windowed_end (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ)
    (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoefWS : SeamCoefWS X P Q a b c)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (T : ℝ) (hT : 0 ≤ T) (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T) :
    (∫ t in A, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in A, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + lemma12RowsMR_end N X P Q H T a b c := by
  rw [lemma12RowsMR_end]
  refine meansq_on_subset_of_decomp hT hAm hAsub
    (fun j _ => continuous_ramMain H N X P Q b c j) (continuous_ramErr H N X P Q a b c)
    (fun t => spoly_ram_decomp H N X P Q a b c t) ?_
  refine (ramErr_moment_split_mr_windowed_end H hH N X P Q hX hN hP a b c hcoefWS hasupp
    T hT).trans ?_
  gcongr
  · exact ramSeamLoPoly_moment H hH N X P Q hX hN hP b c hb hc T hT
  · exact ramSeamUpPoly_moment H hH N X P Q hX hP b c hb hc T hT
  · exact ramP2corrEndMR_moment N X P Q hX hN a b c T
  · exact ramCopTail_moment N P Q a T

/-- **THE MR ROW ON `A_j`, STRICT/FUSED** (`lemma12_on_TsetG_mr_windowed_end`). -/
theorem lemma12_on_TsetG_mr_windowed_end (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
    (Jb j : ℕ) (hH : 2 ≤ Hseq j) (N Xd : ℕ) (hX : 1 ≤ Xd) (hN : 2 * Xd ≤ N)
    (hP : 1 ≤ Pseq j) (a b c : ℕ → ℂ)
    (hcoefWS : SeamCoefWS Xd (Pseq j) (Qseq j) a b c)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (Xd : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (Xd : ℝ))
    (X T t₁ : ℝ) (hT : 0 ≤ T) :
    (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG fb Pseq Qseq Hseq αseq Jb j,
        ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
          * (∑ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
              ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG fb Pseq Qseq Hseq αseq Jb j,
                ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
        + lemma12RowsMR_end N Xd (Pseq j) (Qseq j) (Hseq j) T a b c :=
  lemma12_meansq_on_subset_mr_windowed_end (Hseq j) hH N Xd (Pseq j) (Qseq j) hX hN hP a b c
    hcoefWS hb hc hasupp T hT _
    (measurableSet_annulus_TsetG fb Pseq Qseq Hseq αseq Jb j X T t₁)
    (annulus_TsetG_subset_Icc fb Pseq Qseq Hseq αseq Jb j X T t₁)

/-- ⟦AMENDMENT 1⟧'s regrouping: `four_rows_le` with the `B2` slot restated at `pre·(3/2)·B2`.
The landed lemma spends `8` of its `12` there; `8·(3/2) = 12` closes tight. -/
private lemma four_rows_le_end {pre R1 R2 R3 R4 B1 B2 B3 : ℝ}
    (h2 : R2 ≤ 2 * R1) (h1 : 2 * R1 ≤ pre * B1)
    (h3 : R3 ≤ pre * (3 / 2) * B2) (h4 : R4 ≤ pre * B3)
    (_hR1 : 0 ≤ R1) (_hR3 : 0 ≤ R3) (hR4 : 0 ≤ R4) :
    2 * (4 * (R1 + R2 + R3 + R4)) ≤ 12 * pre * (B1 + B2 + B3) := by
  linarith

/-- **⟦THE ABSORPTION GATE⟧** (`logb_two_mul_P_le`): `log₂(2X_d)·P ≤ 2·X_d`, from the row's
OWN binders — `P ≤ Q`, `log Q ≤ √(log X_d)` and `100 ≤ √(log X_d)`.  With `u := log X_d` and
`s := √u ≥ 100` (so `u = s² ≥ 10⁴`): `P ≤ e^s`, `log₂(2X_d) ≤ (3/2)u`, and
`(3/2)s²·e^s ≤ 2·e^{s²}` because `e^{s²−s} ≥ s² − s` and `2(s²−s) ≥ (3/2)s²` at `s ≥ 4`. -/
private lemma logb_two_mul_P_le {P Q Xd : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q) (hXd : 1 ≤ Xd)
    (hreg : Real.log Q ≤ Real.sqrt (Real.log Xd))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log Xd)) :
    Real.logb 2 (2 * (Xd : ℝ)) * (P : ℝ) ≤ 2 * (Xd : ℝ) := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    linarith
  have hPQR : (P : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hPQ
  -- `0 ≤ u` (else `√u = 0 < 100`), and then `u = s²`
  have hu0 : 0 ≤ Real.log (Xd : ℝ) := by
    by_contra hcon
    push Not at hcon
    rw [Real.sqrt_eq_zero'.mpr hcon.le] at hbig
    norm_num at hbig
  have hsq : Real.sqrt (Real.log (Xd : ℝ)) * Real.sqrt (Real.log (Xd : ℝ))
      = Real.log (Xd : ℝ) := Real.mul_self_sqrt hu0
  have hu4 : (10000 : ℝ) ≤ Real.log (Xd : ℝ) := by nlinarith
  -- `P ≤ e^s`
  have hPexp : (P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (Xd : ℝ))) := by
    have hlogP : Real.log (P : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) :=
      le_trans (Real.log_le_log hP0 hPQR) hreg
    calc (P : ℝ) = Real.exp (Real.log (P : ℝ)) := (Real.exp_log hP0).symm
      _ ≤ Real.exp (Real.sqrt (Real.log (Xd : ℝ))) := Real.exp_le_exp.mpr hlogP
  -- `log₂(2X_d) ≤ (3/2)·log X_d`
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLb : Real.logb 2 (2 * (Xd : ℝ)) ≤ 3 / 2 * Real.log (Xd : ℝ) := by
    have hgt2 := Real.log_two_gt_d9
    have hlt2 := Real.log_two_lt_d9
    have hprod : (0 : ℝ) ≤ (Real.log (Xd : ℝ) - 10000) * (Real.log 2 - 0.6931471803) :=
      mul_nonneg (by linarith) (by linarith)
    have hlogb : Real.logb 2 (2 * (Xd : ℝ))
        = (Real.log 2 + Real.log (Xd : ℝ)) / Real.log 2 := by
      rw [Real.logb, Real.log_mul (by norm_num) (ne_of_gt hXd0)]
    rw [hlogb, div_le_iff₀ hl2]
    linarith
  -- `(3/2)u ≤ 2·e^{u−s}`
  have hgap : 3 / 2 * Real.log (Xd : ℝ)
      ≤ 2 * Real.exp (Real.log (Xd : ℝ) - Real.sqrt (Real.log (Xd : ℝ))) := by
    have hexp := Real.add_one_le_exp
      (Real.log (Xd : ℝ) - Real.sqrt (Real.log (Xd : ℝ)))
    nlinarith [hsq, hbig, hexp]
  calc Real.logb 2 (2 * (Xd : ℝ)) * (P : ℝ)
      ≤ (3 / 2 * Real.log (Xd : ℝ)) * Real.exp (Real.sqrt (Real.log (Xd : ℝ))) :=
        mul_le_mul hLb hPexp hP0.le (by linarith)
    _ ≤ (2 * Real.exp (Real.log (Xd : ℝ) - Real.sqrt (Real.log (Xd : ℝ))))
          * Real.exp (Real.sqrt (Real.log (Xd : ℝ))) :=
        mul_le_mul_of_nonneg_right hgap (Real.exp_pos _).le
    _ = 2 * (Real.exp (Real.log (Xd : ℝ) - Real.sqrt (Real.log (Xd : ℝ)))
          * Real.exp (Real.sqrt (Real.log (Xd : ℝ)))) := by ring
    _ = 2 * Real.exp (Real.log (Xd : ℝ)) := by rw [← Real.exp_add]; congr 2; ring
    _ = 2 * (Xd : ℝ) := by rw [Real.exp_log hXd0]

/-- **THE MR ROW, PRICED — STRICT/FUSED** (`lemma12RowsMR_pricedK_end`).  The right-hand side
is `lemma12RowsMR_pricedK`'s BYTE FOR BYTE: the endpoint mass is absorbed inside the `B2`
slot's unspent `1.5×` (⟦AMENDMENT 1⟧), gated by `logb_two_mul_P_le`. -/
theorem lemma12RowsMR_pricedK_end :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q N Xd : ℕ) (H T : ℝ) (a b c : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → 2 ≤ H →
      Real.log Q ≤ Real.sqrt (Real.log Xd) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      lemma12RowsMR_end N Xd P Q H T a b c
        ≤ 12 * (2 * T + 20 * (N : ℝ))
            * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
                + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))
                + (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)) := by
  obtain ⟨C, hC, hbf⟩ := blockfree_sum_le
  refine ⟨C, hC, ?_⟩
  intro P Q N Xd H T a b c hP hPQ hXd hN hT hH hreg hbig herr ha hb hc hasupp
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    linarith
  have hNR : 2 * (Xd : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpre : (0 : ℝ) ≤ 2 * T + 20 * (N : ℝ) := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    linarith
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hH0 : (0 : ℝ) < H := by linarith
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  -- ⟦ROW 1 + ROW 2⟧ the second window costs at most twice the first
  have hwin2 := second_window_le_first_row (H := H) (T := T) (Nr := (N : ℝ)) (X := Xd)
    hH hXd hT hNR
  -- ⟦ROW 1⟧ the windowed bracket is a factor `e ≥ 2` below the landed one
  have hrow1nn : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2 := by positivity
  have hrow1 : 2 * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2)
      ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2) := by
    have hid : (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
        - 2 * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2)
        = (Real.exp 1 - 2) * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2) := by
      field_simp
    have hnn : (0 : ℝ)
        ≤ (Real.exp 1 - 2) * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2) :=
      mul_nonneg (by linarith) hrow1nn
    linarith [hid.le, hid.ge, hnn]
  -- ⟦ROW 3⟧ the FUSED `p²` mass, and ⟦AMENDMENT 1⟧'s absorption of its endpoint half
  have hp2 := ramP2massEndMR_direct N Xd P Q hXd hN (by omega) a b c ha hb hc
  have hgate := logb_two_mul_P_le (P := P) (Q := Q) (Xd := Xd) hP hPQ hXd hreg hbig
  have habs : 4 * (Real.logb 2 (2 * (Xd : ℝ))) ^ 2 / (Xd : ℝ) ^ 2
      ≤ 1 / 2 * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))) := by
    rw [show (1 : ℝ) / 2 * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))
        = 8 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * Real.logb 2 (2 * (Xd : ℝ)))
      hXd0.le) (by linarith : (0 : ℝ) ≤ 2 * (Xd : ℝ) - Real.logb 2 (2 * (Xd : ℝ)) * (P : ℝ))]
  have hp2' : (∑ n ∈ Finset.Icc 1 N,
        ‖ramP2coeffEndMR N Xd P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ 3 / 2 * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))) := by
    linarith
  have hp2nn : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N,
      ‖ramP2coeffEndMR N Xd P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun n _ => by positivity)
  have hrow3 : (2 * T + 20 * (N : ℝ)) * (∑ n ∈ Finset.Icc 1 N,
        ‖ramP2coeffEndMR N Xd P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * (3 / 2)
          * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))) := by
    have := mul_le_mul_of_nonneg_left hp2' hpre
    linarith
  -- ⟦ROW 4⟧ the block-free mass
  have hbfr := hbf P Q Xd N a hP hPQ hXd (densGate_of_sqrt (le_trans hP hPQ) hreg hbig)
    herr ha hasupp
  have hbfnn : (0 : ℝ) ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
      ‖a n‖ ^ 2 / (n : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun n _ => by positivity)
  -- the four rows, regrouped at the `3/2` slot
  rw [lemma12RowsMR_end]
  refine four_rows_le_end hwin2 ?_ hrow3
    (mul_le_mul_of_nonneg_left hbfr hpre) (mul_nonneg hpre hrow1nn) (mul_nonneg hpre hp2nn)
    (mul_nonneg hpre hbfnn)
  have h := mul_le_mul_of_nonneg_left hrow1 hpre
  linarith

/-- **THE `(T/X_d + 1)` EXIT, STRICT/FUSED** (`lemma12RowsMR_priced_ratioK_end`) — §3's
regrouping on §3′'s row; the bracket is the landed one, byte for byte. -/
theorem lemma12RowsMR_priced_ratioK_end :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q N Xd : ℕ) (H T : ℝ) (a b c : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → 2 ≤ H → (N : ℝ) ≤ 4 * (Xd : ℝ) →
      Real.log Q ≤ Real.sqrt (Real.log Xd) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      lemma12RowsMR_end N Xd P Q H T a b c
        ≤ 960 * (T / (Xd : ℝ) + 1)
            * ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 16 * Real.logb 2 (2 * (Xd : ℝ)) / (P : ℝ)
                + C * (Real.log P / Real.log Q)
                + 1 / (Xd : ℝ)) := by
  obtain ⟨C, hC, hrow⟩ := lemma12RowsMR_pricedK_end
  refine ⟨C, hC, ?_⟩
  intro P Q N Xd H T a b c hP hPQ hXd hN hT hH hN4 hreg hbig herr ha hb hc hasupp
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
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hp2nn : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)) :=
    div_nonneg (by linarith) (by positivity)
  have hBnn : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
      + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))
      + (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2) := by
    have hH0 : (0 : ℝ) < H := by linarith
    have hb1 : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2) := by
      positivity
    have hb3 : (0 : ℝ) ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2 := by
      positivity
    linarith
  have hcoefle : 12 * (2 * T + 20 * (N : ℝ)) ≤ 960 * (Xd : ℝ) * (T / (Xd : ℝ) + 1) := by
    have hTid : (Xd : ℝ) * (T / (Xd : ℝ)) = T := by field_simp
    nlinarith [hN4, hT, hXd0]
  have hstep := hrow P Q N Xd H T a b c hP hPQ hXd hN hT hH hreg hbig herr ha hb hc hasupp
  refine hstep.trans ?_
  have hmul := mul_le_mul_of_nonneg_right hcoefle hBnn
  refine hmul.trans (le_of_eq ?_)
  field_simp
  ring

/-- **THE `j`-COLLECTION, STRICT/FUSED** (`sum_lemma12RowsMR_pricedK_end`). -/
theorem sum_lemma12RowsMR_pricedK_end :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ) (Jb N Xd : ℕ) (T : ℝ)
      (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (c : ℕ → ℂ),
      1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → (N : ℝ) ≤ 4 * (Xd : ℝ) →
      (∀ j ∈ Finset.Icc 1 Jb, 2 ≤ Pseq j ∧ Pseq j ≤ Qseq j ∧ 2 ≤ Hseq j) →
      (∀ j ∈ Finset.Icc 1 Jb, Real.log (Qseq j : ℝ) ≤ Real.sqrt (Real.log Xd)) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      (∀ j ∈ Finset.Icc 1 Jb,
        ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand (Pseq j) (Qseq j), (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log (Pseq j : ℝ) / Real.log (Qseq j : ℝ))) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      ∑ j ∈ Finset.Icc 1 Jb, lemma12RowsMR_end N Xd (Pseq j) (Qseq j) (Hseq j) T a (b j) c
        ≤ 960 * (T / (Xd : ℝ) + 1)
            * ((∑ j ∈ Finset.Icc 1 Jb,
                  ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1)
                      * (Real.exp 1 / (Xd : ℝ) ^ 2))
                    + 16 * Real.logb 2 (2 * (Xd : ℝ)) / (Pseq j : ℝ)
                    + 1 / (Xd : ℝ)))
              + C * ∑ j ∈ Finset.Icc 1 Jb,
                  Real.log (Pseq j : ℝ) / Real.log (Qseq j : ℝ)) := by
  obtain ⟨C, hC, hrow⟩ := lemma12RowsMR_priced_ratioK_end
  refine ⟨C, hC, ?_⟩
  intro Pseq Qseq Hseq Jb N Xd T a b c hXd hN hT hN4 hgates hreg hbig herr ha hb hc hasupp
  have hlevel : ∀ j ∈ Finset.Icc 1 Jb,
      lemma12RowsMR_end N Xd (Pseq j) (Qseq j) (Hseq j) T a (b j) c
        ≤ 960 * (T / (Xd : ℝ) + 1)
            * ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1)
                  * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 16 * Real.logb 2 (2 * (Xd : ℝ)) / (Pseq j : ℝ)
                + 1 / (Xd : ℝ)
                + C * (Real.log (Pseq j : ℝ) / Real.log (Qseq j : ℝ))) := by
    intro j hj
    obtain ⟨hP, hPQ, hH⟩ := hgates j hj
    exact (hrow (Pseq j) (Qseq j) N Xd (Hseq j) T a (b j) c hP hPQ hXd hN hT hH hN4
      (hreg j hj) hbig (herr j hj) ha (hb j) hc hasupp).trans (le_of_eq (by ring))
  refine (Finset.sum_le_sum hlevel).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **THE FULLY-PRICED MR SEAM ROW, STRICT/FUSED**
(`sum_lemma12RowsMR_priced_calibratedK2_end`).  The right-hand side is the landed exit's, byte
for byte — `ThmA2.a2RowsSum` never moves. -/
theorem sum_lemma12RowsMR_priced_calibratedK2_end :
    ∃ C : ℝ, 0 < C ∧ ∀ (A G M Jb N Xd : ℕ) (H1 T : ℝ) (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ)
      (c : ℕ → ℂ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → 2 ≤ H1 →
      (N : ℝ) ≤ 4 * (Xd : ℝ) →
      (∀ j ∈ Finset.Icc 1 Jb,
        Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log Xd)) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      (∀ j ∈ Finset.Icc 1 Jb,
        ((Nat.sqrt Xd : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ)
            * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ))) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      ∑ j ∈ Finset.Icc 1 Jb,
          lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) T a (b j) c
        ≤ 960 * (T / (Xd : ℝ) + 1)
            * ((∑ j ∈ Finset.Icc 1 Jb,
                  ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                      * (Real.exp 1 / (Xd : ℝ) ^ 2))
                    + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                    + 1 / (Xd : ℝ)))
              + C * (2 / (M : ℝ))) := by
  obtain ⟨C, hC, hsum⟩ := sum_lemma12RowsMR_pricedK_end
  refine ⟨C, hC, ?_⟩
  intro A G M Jb N Xd H1 T a b c hA hG hM hXd hN hT hH1 hN4 hreg hbig herr ha hb hc hasupp
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hgates : ∀ j ∈ Finset.Icc 1 Jb,
      2 ≤ calP A G j ∧ calP A G j ≤ calQK A G M j ∧ 2 ≤ calH H1 j := by
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
      nlinarith
  have h := hsum (calP A G) (calQK A G M) (calH H1) Jb N Xd T a b c hXd hN hT hN4 hgates hreg
    hbig herr ha hb hc hasupp
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · have hratio := sum_ratioK_le hA hG hM Jb
    have := mul_le_mul_of_nonneg_left hratio hC.le
    linarith
  · have hT0 : (0 : ℝ) ≤ T / (Xd : ℝ) := div_nonneg hT hXd0.le
    linarith

/-! ## §4 — THE `j`-COLLECTION, GENERIC LADDER -/

/-- **THE `j`-COLLECTION AT THE MR ROW** (`sum_lemma12RowsMR_pricedK`).
`TypicalPriceK.sum_lemma12Rows_pricedK` run on §3's exit; the ladder is generic and the
density collection `Σ_j log P_j/log Q_j` is left symbolic on the right. -/
theorem sum_lemma12RowsMR_pricedK :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ) (Jb N Xd : ℕ) (T : ℝ)
      (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (c : ℕ → ℂ),
      1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → (N : ℝ) ≤ 4 * (Xd : ℝ) →
      (∀ j ∈ Finset.Icc 1 Jb, 2 ≤ Pseq j ∧ Pseq j ≤ Qseq j ∧ 2 ≤ Hseq j) →
      (∀ j ∈ Finset.Icc 1 Jb, Real.log (Qseq j : ℝ) ≤ Real.sqrt (Real.log Xd)) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      (∀ j ∈ Finset.Icc 1 Jb,
        ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand (Pseq j) (Qseq j), (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log (Pseq j : ℝ) / Real.log (Qseq j : ℝ))) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      ∑ j ∈ Finset.Icc 1 Jb, lemma12RowsMR N Xd (Pseq j) (Qseq j) (Hseq j) T a (b j) c
        ≤ 960 * (T / (Xd : ℝ) + 1)
            * ((∑ j ∈ Finset.Icc 1 Jb,
                  ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1)
                      * (Real.exp 1 / (Xd : ℝ) ^ 2))
                    + 16 * Real.logb 2 (2 * (Xd : ℝ)) / (Pseq j : ℝ)
                    + 1 / (Xd : ℝ)))
              + C * ∑ j ∈ Finset.Icc 1 Jb,
                  Real.log (Pseq j : ℝ) / Real.log (Qseq j : ℝ)) := by
  obtain ⟨C, hC, hrow⟩ := lemma12RowsMR_priced_ratioK
  refine ⟨C, hC, ?_⟩
  intro Pseq Qseq Hseq Jb N Xd T a b c hXd hN hT hN4 hgates hreg hbig herr ha hb hc hasupp
  have hlevel : ∀ j ∈ Finset.Icc 1 Jb,
      lemma12RowsMR N Xd (Pseq j) (Qseq j) (Hseq j) T a (b j) c
        ≤ 960 * (T / (Xd : ℝ) + 1)
            * ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1)
                  * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 16 * Real.logb 2 (2 * (Xd : ℝ)) / (Pseq j : ℝ)
                + 1 / (Xd : ℝ)
                + C * (Real.log (Pseq j : ℝ) / Real.log (Qseq j : ℝ))) := by
    intro j hj
    obtain ⟨hP, hPQ, hH⟩ := hgates j hj
    exact (hrow (Pseq j) (Qseq j) N Xd (Hseq j) T a (b j) c hP hPQ hXd hN hT hH hN4
      (hreg j hj) hbig (herr j hj) ha (hb j) hc hasupp).trans (le_of_eq (by ring))
  refine (Finset.sum_le_sum hlevel).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ## §5 — THE FULLY-PRICED MR SEAM ROW -/

/-- **THE FULLY-PRICED MR SEAM ROW** (`sum_lemma12RowsMR_priced_calibratedK2`).
`TypicalPriceK.sum_lemma12Rows_priced_calibratedK2`'s twin at the four rows: §4 at the
K-family `(calP A G, calQK A G M, calH H1)` with the density collection at `C·(2/M)`
(`SeamCalibrationK.sum_ratioK_le`).  The ONLY change against the landed exit is the
prefactor `480 → 960` — and `hwin` is gone from the hypothesis list. -/
theorem sum_lemma12RowsMR_priced_calibratedK2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (A G M Jb N Xd : ℕ) (H1 T : ℝ) (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ)
      (c : ℕ → ℂ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → 2 ≤ H1 →
      (N : ℝ) ≤ 4 * (Xd : ℝ) →
      (∀ j ∈ Finset.Icc 1 Jb,
        Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log Xd)) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      (∀ j ∈ Finset.Icc 1 Jb,
        ((Nat.sqrt Xd : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ)
            * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ))) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      ∑ j ∈ Finset.Icc 1 Jb,
          lemma12RowsMR N Xd (calP A G j) (calQK A G M j) (calH H1 j) T a (b j) c
        ≤ 960 * (T / (Xd : ℝ) + 1)
            * ((∑ j ∈ Finset.Icc 1 Jb,
                  ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                      * (Real.exp 1 / (Xd : ℝ) ^ 2))
                    + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                    + 1 / (Xd : ℝ)))
              + C * (2 / (M : ℝ))) := by
  obtain ⟨C, hC, hsum⟩ := sum_lemma12RowsMR_pricedK
  refine ⟨C, hC, ?_⟩
  intro A G M Jb N Xd H1 T a b c hA hG hM hXd hN hT hH1 hN4 hreg hbig herr ha hb hc hasupp
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hgates : ∀ j ∈ Finset.Icc 1 Jb,
      2 ≤ calP A G j ∧ calP A G j ≤ calQK A G M j ∧ 2 ≤ calH H1 j := by
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
      nlinarith
  have h := hsum (calP A G) (calQK A G M) (calH H1) Jb N Xd T a b c hXd hN hT hN4 hgates hreg
    hbig herr ha hb hc hasupp
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · have hratio := sum_ratioK_le hA hG hM Jb
    have := mul_le_mul_of_nonneg_left hratio hC.le
    linarith
  · have hT0 : (0 : ℝ) ≤ T / (Xd : ℝ) := div_nonneg hT hXd0.le
    linarith

end Salt.MR

end
