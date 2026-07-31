/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4RowsChiEnd

/-!
# ⟦THE SIEVE-VANISHING TWIN CHAIN⟧ (`M4RowsChiZero`)

Design provenance: `docs/blueprints/flags.md` ⟦DENSITY-SCOPE returns⟧ (2026-07-30 09:13) and
the council grant of 09:15 ("all granted").  This file is the FIRST of the granted repairs.

## The finding this file executes

Lemma 12's row `lemma12RowsMR_end` has FOUR rows.  Its fourth is the **block-free (coprime
tail) mass**

```
      Σ_{n ≤ N, ω(n; P_j, Q_j) = 0}  ‖aₙ‖²/n² ,
```

and the ONLY thing that ever prices it in the corpus is `TypicalPrice.blockfree_sum_le`,
which reads `‖a‖ ≤ 1` and nothing else and pays `C·(log P/log Q)/X_d + 1/X_d²`.  Collected
over the K-ladder (`SeamCalibrationK.sum_ratioK_le`) that is the density summand

```
      C_p · (2/M)
```

of `ThmA2.a2Mrow` — the one the ⟦SECOND HORN⟧ refutation rides.

**But the door's datum is `𝒮`-SUPPORTED.**  `M4Assembly.doorCoeffU M` is
`M4Sieve.memSCoeff` at the door's own two-level family, and `Sec9Glue.MemS` says: a prime
factor in EVERY block.  So off the sieve — exactly the index set the fourth row sums over —
the datum is **identically zero**, and the fourth row is `0`, not `C·(log P/log Q)/X_d`.

That is what this file proves and then carries the whole way up the `χ` chain.

## The shape of the twins — `C_p` becomes a FREE parameter

Every landed statement in the chain has the form `∃ C, 0 < C ∧ …`; the twin has

```
      ∀ C : ℝ, 0 ≤ C → …
```

with the SAME right-hand side, byte for byte.  Nothing is weakened: `∀ C ≥ 0` is strictly
stronger than `∃ C > 0` at a bound that is monotone in `C`, and the interface constant
`ThmA2.a2Mrow`'s `C` (`M4Assembly.DoorFuseFrame`'s `Ccc`) carries **no positivity
hypothesis** anywhere in the frozen statements.  In particular the consumer may take

```
      C_p := 0 ,
```

which is an INSTANTIATION of the frozen interface, not an edit of it: `a2Mrow Ct 0 M X_d X ε`
is the frozen definition read at `C = 0`, and `DoorFuseFrame M X_d j Ct 0 ε`'s `gRows` field
loses its density debit `5760·C_p·(2/M)` outright.

## Contents

* §1 the `𝒮`-support predicate `BlockLive`, its three transports, and the vanishing
  (`blockfree_row_zero`, `blockfree_row_memS_zero` — the scoper's ⟦PROBE 1⟧ in the repo);
* §2 the four-row price WITHOUT the density: `lemma12RowsMR_pricedK_end_zero` and the
  `(T/X_d + 1)` exit `lemma12RowsMR_priced_ratioK_end_zero`;
* §3 the `j`-collection and the K-calibrated exit — **`sum_ratioK_le` is never called**;
* §4 the twisted datum: `sum_lemma12RowsMR_priced_chi_end_zero`;
* §5 the per-`χ` seam row as a number, and the `hrowsSum` slot
  (`m4_rowChi_number_of_capstone_zero`, `m4_hrowsSum_chi_zero`);
* §6 the door instance, `DoorRowZeroBase`, and the slot `m4_hrowsSlot_at_door_zero`;
* §7 ⟦item 11⟧ at the zero density (`m4_chiSummedFreeRow_of_doorAssembly_zero`).

## ⟦WHAT THE TWIN DROPS — the `dom` bonus⟧

`M4RowsChiEnd.DoorRowEndBase`'s field `dom` (the per-level error-domination product
`(√X_d + 1)·∏_{p ∈ [P_j,Q_j]}(1 + 3/p) ≤ X_d·log P_j/log Q_j`) exists for exactly one
purpose: it is `blockfree_sum_le`'s own analytic gate.  With the fourth row identically zero
that gate has no consumer, and `DoorRowZeroBase` **omits it** — relaxing an `X_d ≳ (M j²)⁸`
floor on every socket base.  `doorRowZeroBase_of_doorRowEndBase` records that the twin asks
strictly less (iron rule 1: no statement is strengthened anywhere).

⟦WHAT THE TWIN KEEPS⟧  `reg` and `big` stay: they are ⟦AMENDMENT 1⟧'s absorption gate
(`logb_two_mul_P_le`, the `p²` row's endpoint half), not the density's.

## ⟦PURELY ADDITIVE⟧

No landed declaration is touched.  `M4RowsChiEnd.m4_rowChi_weighed_end`,
`M4RowsChiEnd.m4MrowChiEnd_le_a2Mrow` and `M4Assembly.m4_chiSummedFreeRow_of_doorAssembly` are
REUSED at `C_p := 0`, which is why §5–§7 are short: the weighting page and the door bridge are
already parametric in the density constant.

⟦THE FOUR LOG SCALES⟧ stay apart exactly as in `M4RowsChiEnd`: `log(qT_ann)`, `log(5T_ann+1)`,
`L ≥ log(qT_ann)`, `log X`; `√(log X_d)` is the FIFTH and is never identified with
`√(log X)`.  `arcDen 12 H` is never evaluated.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE `𝒮`-SUPPORT, AND THE VANISHING OF THE BLOCK-FREE ROW

The scoper's three kernel probes (`scratchpad/DensityProbe.lean`), ported and factored: one
predicate, three transports, one vanishing lemma. -/

/-- **⟦THE `𝒮`-SUPPORT PREDICATE⟧** (`BlockLive P Q a`).  The datum is supported on integers
carrying at least one prime factor in the block `[P, Q]`.  This is the ONE hypothesis the
whole twin chain adds, and at the door it is discharged definitionally (§6). -/
def BlockLive (P Q : ℕ) (a : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, a n ≠ 0 → blockOmega P Q n ≠ 0

/-- The sieved datum `1_𝒮·F` is block-live at EVERY level of its own family — this is
`Sec9Glue.MemS`'s content ("a prime factor in every block") read one level at a time. -/
theorem blockLive_memSCoeff (Pseq Qseq : ℕ → ℕ) (J : ℕ) (F : ℕ → ℂ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 J) : BlockLive (Pseq j) (Qseq j) (memSCoeff Pseq Qseq J F) := by
  intro n hn hz
  apply hn
  simp only [memSCoeff]
  rw [if_neg]
  intro hmem
  have h1 := hmem j hj
  omega

/-- Block-liveness survives the half-open dyadic cut (the cut only ever deletes terms). -/
theorem blockLive_winCutH {P Q Xd : ℕ} {F : ℕ → ℂ} (h : BlockLive P Q F) :
    BlockLive P Q (winCutH Xd F) := by
  intro n hn
  refine h n ?_
  intro hF
  apply hn
  simp only [winCutH, hF]
  split_ifs <;> rfl

/-- **Block-liveness survives the `χ̄`-twist** — the scoper's ⟦PROBE 3⟧.  The twist multiplies
pointwise, so it cannot create support. -/
theorem blockLive_chiBarCoeff {q : ℕ} (χ : DirichletCharacter ℂ q) {P Q : ℕ} {a : ℕ → ℂ}
    (h : BlockLive P Q a) : BlockLive P Q (chiBarCoeff q χ a) := by
  intro n hn
  refine h n ?_
  intro ha
  exact hn (by rw [chiBarCoeff_apply, ha, mul_zero])

/-- **⟦THE VANISHING⟧** (`blockfree_row_zero`).  Lemma 12's fourth row — the block-free
(coprime-tail) mass that `TypicalPrice.blockfree_sum_le` prices at `C(log P/log Q)/W + 1/W²`
— is **identically zero** at block-live data.  The index set of the sum and the support of
the datum are complementary by construction. -/
theorem blockfree_row_zero {P Q N : ℕ} {a : ℕ → ℂ} (h : BlockLive P Q a) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2 = 0 := by
  refine Finset.sum_eq_zero (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  have hz : a n = 0 := by
    by_contra hne
    exact h n hne hn.2
  rw [hz]
  simp

/-- **⟦PROBE 1, IN THE REPO⟧** (`blockfree_row_memS_zero`).  The block-free row vanishes at
`𝒮`-supported data, level by level — the statement the scoper kernel-checked in
`scratchpad/DensityProbe.lean`. -/
theorem blockfree_row_memS_zero (Pseq Qseq : ℕ → ℕ) (J N : ℕ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 J) (F : ℕ → ℂ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega (Pseq j) (Qseq j) n = 0),
        ‖memSCoeff Pseq Qseq J F n‖ ^ 2 / (n : ℝ) ^ 2 = 0 :=
  blockfree_row_zero (blockLive_memSCoeff Pseq Qseq J F hj)

/-- **⟦LEMMA 12'S FOURTH ROW, AS THE CHAIN READS IT⟧** (`lemma12RowsMR_end_row4_zero`) — the
fourth summand of `M4RowMR.lemma12RowsMR_end`, with its `(2T + 20N)` prefactor, is `0`. -/
theorem lemma12RowsMR_end_row4_zero {P Q N : ℕ} {a : ℕ → ℂ} (T Nr : ℝ)
    (h : BlockLive P Q a) :
    (2 * T + 20 * Nr)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
            ‖a n‖ ^ 2 / (n : ℝ) ^ 2 = 0 := by
  rw [blockfree_row_zero h, mul_zero]

/-! ## §2 — THE FOUR-ROW PRICE WITHOUT THE DENSITY

`M4RowMR.lemma12RowsMR_pricedK_end`'s twin.  Rows 1, 2 and 3 are priced exactly as there
(`SeamRowWindowed.second_window_le_first_row`, the factor-`e` windowed bracket, and
`M4P2MR.ramP2massEndMR_direct` with ⟦AMENDMENT 1⟧'s `3/2`-slot absorption); row 4 is §1's
zero.  The two private helpers of `M4RowMR` (`four_rows_le_end`, `logb_two_mul_P_le`) are
re-derived here at their own names — no content is re-proved that could have been imported. -/

/-- `M4RowMR.four_rows_le_end`'s twin with the fourth row KILLED and the third bracket slot
gone: `8·(3/2) = 12` still closes tight. -/
private lemma four_rows_le_zero {pre R1 R2 R3 R4 B1 B2 : ℝ}
    (h2 : R2 ≤ 2 * R1) (h1 : 2 * R1 ≤ pre * B1)
    (h3 : R3 ≤ pre * (3 / 2) * B2) (h4 : R4 = 0)
    (_hR1 : 0 ≤ R1) (_hR3 : 0 ≤ R3) :
    2 * (4 * (R1 + R2 + R3 + R4)) ≤ 12 * pre * (B1 + B2) := by
  subst h4
  linarith

/-- **⟦THE ABSORPTION GATE⟧** (`logb_two_mul_P_le_zero`) — `M4RowMR.logb_two_mul_P_le` at its
own name (that one is `private` to its file).  `log₂(2X_d)·P ≤ 2·X_d` from `P ≤ Q`,
`log Q ≤ √(log X_d)` and `100 ≤ √(log X_d)`.  This is the `p²` row's gate, NOT the density's,
which is why `reg`/`big` survive into `DoorRowZeroBase`. -/
private lemma logb_two_mul_P_le_zero {P Q Xd : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q) (hXd : 1 ≤ Xd)
    (hreg : Real.log Q ≤ Real.sqrt (Real.log Xd))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log Xd)) :
    Real.logb 2 (2 * (Xd : ℝ)) * (P : ℝ) ≤ 2 * (Xd : ℝ) := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    linarith
  have hPQR : (P : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hPQ
  have hu0 : 0 ≤ Real.log (Xd : ℝ) := by
    by_contra hcon
    rw [Real.sqrt_eq_zero'.mpr (not_le.mp hcon).le] at hbig
    norm_num at hbig
  have hsq : Real.sqrt (Real.log (Xd : ℝ)) * Real.sqrt (Real.log (Xd : ℝ))
      = Real.log (Xd : ℝ) := Real.mul_self_sqrt hu0
  have hu4 : (10000 : ℝ) ≤ Real.log (Xd : ℝ) := by nlinarith
  have hPexp : (P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (Xd : ℝ))) := by
    have hlogP : Real.log (P : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) :=
      le_trans (Real.log_le_log hP0 hPQR) hreg
    calc (P : ℝ) = Real.exp (Real.log (P : ℝ)) := (Real.exp_log hP0).symm
      _ ≤ Real.exp (Real.sqrt (Real.log (Xd : ℝ))) := Real.exp_le_exp.mpr hlogP
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

/-- **⟦THE MR ROW, PRICED, DENSITY-FREE⟧** (`lemma12RowsMR_pricedK_end_zero`).
`M4RowMR.lemma12RowsMR_pricedK_end` at a block-live datum: the third bracket slot
`C·(log P/log Q)/X_d + 1/X_d²` — the whole of `blockfree_sum_le`'s output — is GONE, because
the row it priced is `0`.

⟦WHAT LEFT THE HYPOTHESIS LIST⟧ the error-domination product `herr` (blockfree's own gate,
the `DoorRowEndBase.dom` bonus) and the dyadic support pin `hasupp` (read only by
blockfree).  ⟦WHAT STAYED⟧ `hreg`/`hbig` — ⟦AMENDMENT 1⟧'s absorption gate needs them. -/
theorem lemma12RowsMR_pricedK_end_zero (P Q N Xd : ℕ) (H T : ℝ) (a b c : ℕ → ℂ)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hXd : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hT : 0 ≤ T) (hH : 2 ≤ H)
    (hreg : Real.log Q ≤ Real.sqrt (Real.log Xd))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log Xd))
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hlive : BlockLive P Q a) :
    lemma12RowsMR_end N Xd P Q H T a b c
      ≤ 12 * (2 * T + 20 * (N : ℝ))
          * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
              + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))) := by
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
  have hgate := logb_two_mul_P_le_zero (P := P) (Q := Q) (Xd := Xd) hP hPQ hXd hreg hbig
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
  -- ⟦ROW 4⟧ ⟦THE VANISHING⟧ (`lemma12RowsMR_end_row4_zero`, inlined at the row's own shape)
  rw [lemma12RowsMR_end]
  refine four_rows_le_zero hwin2 ?_ hrow3 ?_ (mul_nonneg hpre hrow1nn)
    (mul_nonneg hpre hp2nn)
  · have h := mul_le_mul_of_nonneg_left hrow1 hpre
    linarith
  · rw [blockfree_row_zero hlive, mul_zero]

/-- **⟦THE `(T/X_d + 1)` EXIT, DENSITY-FREE⟧** (`lemma12RowsMR_priced_ratioK_end_zero`).
`M4RowMR.lemma12RowsMR_priced_ratioK_end`'s regrouping on §2: `N ≤ 4X_d` turns
`12(2T + 20N)` into `960·X_d·(T/X_d + 1)`, and the `X_d` distributes into the (now
two-slot) bracket. -/
theorem lemma12RowsMR_priced_ratioK_end_zero (P Q N Xd : ℕ) (H T : ℝ) (a b c : ℕ → ℂ)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hXd : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hT : 0 ≤ T) (hH : 2 ≤ H)
    (hN4 : (N : ℝ) ≤ 4 * (Xd : ℝ))
    (hreg : Real.log Q ≤ Real.sqrt (Real.log Xd))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log Xd))
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hlive : BlockLive P Q a) :
    lemma12RowsMR_end N Xd P Q H T a b c
      ≤ 960 * (T / (Xd : ℝ) + 1)
          * ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2))
              + 16 * Real.logb 2 (2 * (Xd : ℝ)) / (P : ℝ)) := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by linarith
  have hXdne : (Xd : ℝ) ≠ 0 := ne_of_gt hXd0
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have h : 0 < P := by omega
    exact_mod_cast h
  have hPne : (P : ℝ) ≠ 0 := ne_of_gt hP0
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hp2nn : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)) :=
    div_nonneg (by linarith) (by positivity)
  have hBnn : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
      + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)) := by
    have hH0 : (0 : ℝ) < H := by linarith
    have hb1 : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2) := by
      positivity
    linarith
  have hcoefle : 12 * (2 * T + 20 * (N : ℝ)) ≤ 960 * (Xd : ℝ) * (T / (Xd : ℝ) + 1) := by
    have hTid : (Xd : ℝ) * (T / (Xd : ℝ)) = T := by field_simp
    nlinarith [hN4, hT, hXd0]
  have hstep := lemma12RowsMR_pricedK_end_zero P Q N Xd H T a b c hP hPQ hXd hN hT hH
    hreg hbig ha hb hc hlive
  refine hstep.trans ?_
  have hmul := mul_le_mul_of_nonneg_right hcoefle hBnn
  refine hmul.trans (le_of_eq ?_)
  field_simp

/-! ## §3 — THE `j`-COLLECTION, AND THE K-CALIBRATED EXIT

⟦WHERE `sum_ratioK_le` DIES⟧  The landed chain collects `Σ_j log P_j/log Q_j` and pays it at
`2/M` (`SeamCalibrationK.sum_ratioK_le`) — that collection IS the density summand.  Here the
collection has nothing to collect, so the calibration step is never performed: the twin's
right-hand side is the landed one BYTE FOR BYTE only because the two absent quantities
(`Σ_j 1/X_d` and `C·(2/M)`) are re-added as nonnegative slack at the interface. -/

/-- **⟦THE `j`-COLLECTION, DENSITY-FREE⟧** (`sum_lemma12RowsMR_pricedK_end_zero`).  §2's exit
summed over a generic ladder; the right-hand side carries NO density collection at all. -/
theorem sum_lemma12RowsMR_pricedK_end_zero (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ)
    (Jb N Xd : ℕ) (T : ℝ) (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (c : ℕ → ℂ)
    (hXd : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hT : 0 ≤ T) (hN4 : (N : ℝ) ≤ 4 * (Xd : ℝ))
    (hgates : ∀ j ∈ Finset.Icc 1 Jb, 2 ≤ Pseq j ∧ Pseq j ≤ Qseq j ∧ 2 ≤ Hseq j)
    (hreg : ∀ j ∈ Finset.Icc 1 Jb, Real.log (Qseq j : ℝ) ≤ Real.sqrt (Real.log Xd))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log Xd))
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ j m, ‖b j m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hlive : ∀ j ∈ Finset.Icc 1 Jb, BlockLive (Pseq j) (Qseq j) a) :
    ∑ j ∈ Finset.Icc 1 Jb, lemma12RowsMR_end N Xd (Pseq j) (Qseq j) (Hseq j) T a (b j) c
      ≤ 960 * (T / (Xd : ℝ) + 1)
          * ∑ j ∈ Finset.Icc 1 Jb,
              ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1)
                  * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 16 * Real.logb 2 (2 * (Xd : ℝ)) / (Pseq j : ℝ)) := by
  have hlevel : ∀ j ∈ Finset.Icc 1 Jb,
      lemma12RowsMR_end N Xd (Pseq j) (Qseq j) (Hseq j) T a (b j) c
        ≤ 960 * (T / (Xd : ℝ) + 1)
            * ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1)
                  * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 16 * Real.logb 2 (2 * (Xd : ℝ)) / (Pseq j : ℝ)) := by
    intro j hj
    obtain ⟨hP, hPQ, hH⟩ := hgates j hj
    exact lemma12RowsMR_priced_ratioK_end_zero (Pseq j) (Qseq j) N Xd (Hseq j) T a (b j) c
      hP hPQ hXd hN hT hH hN4 (hreg j hj) hbig ha (hb j) hc (hlive j hj)
  refine (Finset.sum_le_sum hlevel).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]

/-- **⟦THE FULLY-PRICED MR SEAM ROW AT `C_p` FREE⟧**
(`sum_lemma12RowsMR_priced_calibratedK2_end_zero`).
`M4RowMR.sum_lemma12RowsMR_priced_calibratedK2_end`'s twin.  The right-hand side is that
theorem's BYTE FOR BYTE — including the `C·(2/M)` summand — but `C` is now a FREE nonnegative
real instead of an existential witness, because the row it used to pay for is `0`.
`SeamCalibrationK.sum_ratioK_le` is not called anywhere in the proof. -/
theorem sum_lemma12RowsMR_priced_calibratedK2_end_zero (C : ℝ) (hC : 0 ≤ C)
    (A G M Jb N Xd : ℕ) (H1 T : ℝ) (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (c : ℕ → ℂ)
    (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) (hXd : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hT : 0 ≤ T)
    (hH1 : 2 ≤ H1) (hN4 : (N : ℝ) ≤ 4 * (Xd : ℝ))
    (hreg : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log Xd))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log Xd))
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ j m, ‖b j m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hlive : ∀ j ∈ Finset.Icc 1 Jb, BlockLive (calP A G j) (calQK A G M j) a) :
    ∑ j ∈ Finset.Icc 1 Jb,
        lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) T a (b j) c
      ≤ 960 * (T / (Xd : ℝ) + 1)
          * ((∑ j ∈ Finset.Icc 1 Jb,
                ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                    * (Real.exp 1 / (Xd : ℝ) ^ 2))
                  + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                  + 1 / (Xd : ℝ)))
            + C * (2 / (M : ℝ))) := by
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
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
  have h := sum_lemma12RowsMR_pricedK_end_zero (calP A G) (calQK A G M) (calH H1) Jb N Xd T
    a b c hXd hN hT hN4 hgates hreg hbig ha hb hc hlive
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · have hstep : ∑ j ∈ Finset.Icc 1 Jb,
        ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
            * (Real.exp 1 / (Xd : ℝ) ^ 2))
          + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ))
        ≤ ∑ j ∈ Finset.Icc 1 Jb,
            ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                * (Real.exp 1 / (Xd : ℝ) ^ 2))
              + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
              + 1 / (Xd : ℝ)) := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      have : (0 : ℝ) ≤ 1 / (Xd : ℝ) := by positivity
      linarith
    have hCm : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith
  · have hT0 : (0 : ℝ) ≤ T / (Xd : ℝ) := div_nonneg hT hXd0.le
    linarith

/-! ## §4 — THE TWISTED DATUM

`M4RowsChiEnd.sum_lemma12RowsMR_priced_chi_end`'s twin.  The pricer is datum-generic, so the
lift is `TLegChi` §1's four coefficient transports plus §1's `blockLive_chiBarCoeff`. -/

/-- **⟦THE FOUR-ROW LEMMA-12 ROW SUM AT TWISTED DATA, DENSITY-FREE⟧**
(`sum_lemma12RowsMR_priced_chi_end_zero`).  The hypotheses are stated on the UNTWISTED
sequences (block-liveness included — §1's transport does the rest) and the bound is the
`q = 1` one VERBATIM at a FREE `C ≥ 0`. -/
theorem sum_lemma12RowsMR_priced_chi_end_zero (C : ℝ) (hC : 0 ≤ C)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (A G M Jb N Xd : ℕ) (H1 T : ℝ) (a c : ℕ → ℂ) (b : ℕ → ℕ → ℂ)
    (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) (hXd : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hT : 0 ≤ T)
    (hH1 : 2 ≤ H1) (hN4 : (N : ℝ) ≤ 4 * (Xd : ℝ))
    (hreg : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)))
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ j m, ‖b j m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hlive : ∀ j ∈ Finset.Icc 1 Jb, BlockLive (calP A G j) (calQK A G M j) a) :
    ∑ j ∈ Finset.Icc 1 Jb,
        lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) T
          (chiBarCoeff q χ a) (chiBarCoeff q χ (b j)) (chiBarCoeff q χ c)
      ≤ 960 * (T / (Xd : ℝ) + 1)
          * ((∑ j ∈ Finset.Icc 1 Jb,
                ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                    * (Real.exp 1 / (Xd : ℝ) ^ 2))
                  + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                  + 1 / (Xd : ℝ)))
            + C * (2 / (M : ℝ))) :=
  sum_lemma12RowsMR_priced_calibratedK2_end_zero C hC A G M Jb N Xd H1 T
    (chiBarCoeff q χ a) (fun j => chiBarCoeff q χ (b j)) (chiBarCoeff q χ c)
    hA hG hM hXd hN hT hH1 hN4 hreg hbig
    (norm_chiBarCoeff_le_one χ ha) (chiBarCoeff_bfam_le_one χ hb)
    (chiBarCoeff_cseq_le_one χ hc)
    (fun j hj => blockLive_chiBarCoeff χ (hlive j hj))

/-! ## §5 — THE PER-`χ` SEAM ROW AS A NUMBER, AND THE `hrowsSum` SLOT

`M4RowsChiEnd` §3 and §5 at the density-free pricer.  The composition is identical:
`TLegExit.TLeg_feeds_capstone_gen` with its row slot instantiated at the FOUR-row
strict/fused exit `M4RowMR.lemma12_on_TsetG_mr_windowed_end`, fused with §4.

⟦THE WEIGHTING PAGE IS REUSED, NOT RE-DERIVED⟧  `M4RowsChiEnd.m4_rowChi_weighed_end` is
already parametric in `Cp` and asks only `0 ≤ Cp`, so §5's weighing is one application at
`Cp := C`; the four weight numerals `9`, `244`, `3`, `3/2` are untouched. -/

set_option maxHeartbeats 1000000 in
-- Same cause as `M4RowsChiEnd.m4_rowChi_number_of_capstone_end`: the leg's exit and the
-- pricer's exit are elaborated against one another at full ladder width.
/-- **⟦THE PER-`χ` SEAM ROW AS A NUMBER, DENSITY-FREE⟧** (`m4_rowChi_number_of_capstone_zero`).
`M4RowsChiEnd.m4_rowChi_number_of_capstone_end` with `Cp` a FREE nonnegative real and the
error-domination binder `hdom` GONE from the hypothesis list — replaced by the datum's own
block-liveness, which the door supplies for free. -/
theorem m4_rowChi_number_of_capstone_zero :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd A G M Jb : ℕ) (H1 X Tann t₁ S η ε : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        0 ≤ Tann → 2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        -- ⟦THE STRICT RELATIVIZED PAIR LAW, UNTWISTED⟧
        (∀ j ∈ Finset.Icc 1 Jb,
          SeamCoefWS Xd (calP A G j) (calQK A G M j) a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        -- ⟦THE `𝒮`-SUPPORT⟧ in place of the density gate
        (∀ j ∈ Finset.Icc 1 Jb, BlockLive (calP A G j) (calQK A G M j) a) →
        -- ⟦THE RECONCILIATION GATES (R1), (R2)⟧ — (R4) is GONE
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        -- ⟦THE A3 CAPSTONE ROW, CARRIED⟧
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * S ^ 2
              + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1)
                      (mrAlpha η) Jb,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) →
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
                  * (Tann * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
                  * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                      + 60 * (calH H1 1 / mrAlpha η 1)
                          * Real.exp (4 * mrAlpha η 1 / calH H1 1))
                + 1536 * Ct * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
                    * (1 / ((calP A G 1 : ℕ) : ℝ))
                + 960 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + Cp * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Ct, hCt, hfeed⟩ := TLeg_feeds_capstone_gen
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ χ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X Tann t₁ S η ε hF hT0 hNXd hN4
    hcoefWS hasupp hlive hQXd hXdbig hcap
  -- ⟦THE FRAME'S OWN READS⟧
  have hη := hF.eta_pos
  have hη6 := hF.eta_lt
  have hJb1 := hF.one_le_Jb
  have hG1 := hF.one_le_G
  have hM1 := hF.one_le_M
  have hA1 : 1 ≤ A := le_trans (by norm_num) hF.A_floor
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hcalH1 : calH H1 1 = H1 := by simp [calH]
  have hH1two : (2 : ℝ) ≤ calH H1 1 := by rw [hcalH1]; exact hF.H1_two
  have hP1nat : 1 ≤ calP A G 1 := by simp only [calP]; exact Nat.one_le_two_pow
  have hP1pos : (0 : ℝ) < ((calP A G 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((calP A G 1 : ℕ) : ℝ) := by exact_mod_cast hP1nat
    linarith
  have hQ1Xd : calQK A G M 1 ≤ Xd := le_trans (calQK_mono A hG1 hJb1) hF.Q_le_Xd
  have hbot1 : ∀ v ∈ ramI (calH H1 1) (calP A G 1) (calQK A G M 1),
      1 ≤ ramRbot (calH H1 1) Xd v :=
    fun v hv => ramRbot_one_le_of_mem_ramI (by linarith) (one_le_calQK A G M 1) hQ1Xd hv
  have hHj : ∀ j ∈ Finset.Icc 1 Jb, (2 : ℝ) ≤ calH H1 j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    rw [calH]
    nlinarith [hF.H1_two]
  have hPj1 : ∀ j : ℕ, 1 ≤ calP A G j := fun j => by
    simp only [calP]; exact Nat.one_le_two_pow
  have hasuppχ := chiBarCoeff_dyadic_supp χ hasupp
  -- ⟦THE ROW SLOT, AT THE FOUR-ROW STRICT/FUSED EXIT⟧
  have hrowfam : ∀ j ∈ Finset.Icc 1 Jb,
      (∫ t in (seamAnn X Tann \ seamBall X t₁)
            ∩ TsetG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1) (mrAlpha η) Jb j,
          ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        ≤ 2 * ((ramI (calH H1 j) (calP A G j) (calQK A G M j)).card : ℝ)
            * (∑ v ∈ ramI (calH H1 j) (calP A G j) (calQK A G M j),
                ∫ t in (seamAnn X Tann \ seamBall X t₁)
                    ∩ TsetG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1)
                        (mrAlpha η) Jb j,
                  ‖ramMain (calH H1 j) N Xd (calP A G j) (calQK A G M j)
                    (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c) v t‖ ^ 2)
          + lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann
              (chiBarCoeff q χ a) (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c) := by
    intro j hj
    exact lemma12_on_TsetG_mr_windowed_end (chiBarCoeff q χ c) (calP A G) (calQK A G M)
      (calH H1) (mrAlpha η) Jb j (hHj j hj) N Xd hXd1 hNXd (hPj1 j)
      (chiBarCoeff q χ a) (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c)
      (chiBarCoeff_seamCoefWS χ (hcoefWS j hj)) (chiBarCoeff_bfam_le_one χ hb1 j)
      (chiBarCoeff_cseq_le_one χ hc1) (hasupp_real_of_nat hasuppχ) X Tann t₁ hT0
  have hleg := hfeed (chiBarCoeff q χ c) (chiBarCoeff q χ a)
    (fun j => chiBarCoeff q χ (bfam j)) (calP A G) (calQK A G M) (calH H1) η Jb N Xd
    (calP A G 1) X Tann t₁ S ε
    (fun j => lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann
      (chiBarCoeff q χ a) (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c))
    hη hη6 hJb1 hXd1 hT0 hP1pos (levelGates_calibratedK hF) hH1two hP1nat
    (calP_le_calQK hM1 le_rfl) hbot1 (chiBarCoeff_bfam_le_one χ hb1)
    (chiBarCoeff_cseq_le_one χ hc1) hrowfam hcap
  -- ⟦THE PRICE OF `Σ_j lemma12RowsMR_end`, AT THE TWISTED `𝒮`-SUPPORTED DATUM⟧
  have hreg : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine le_trans (Real.log_le_log ?_ ?_) hQXd
    · have h : (0 : ℕ) < calQK A G M j := lt_of_lt_of_le Nat.zero_lt_one (one_le_calQK A G M j)
      exact_mod_cast h
    · exact_mod_cast calQK_mono A hG1 hj.2
  have hK2 := sum_lemma12RowsMR_priced_chi_end_zero Cp hCp q χ A G M Jb N Xd H1 Tann a c bfam
    hA1 hG1 hM1 hXd1 hNXd hT0 hF.H1_two hN4 hreg hXdbig ha1 hb1 hc1 hlive
  exact hleg.trans
    (add_le_add (add_le_add le_rfl (add_le_add le_rfl hK2)) le_rfl)

set_option maxHeartbeats 400000 in
-- Same cause as `M4RowsChiEnd.m4_rowChi_weighed_end`: the number-row hypothesis is matched
-- summand by summand against `m4MrowChiEnd`, which costs more than the default budget in
-- elaboration alone.
/-- **⟦THE `hrowsSum` SLOT, DENSITY-FREE⟧** (`m4_hrowsSum_chi_zero`).
`M4RowsChiEnd.m4_hrowsSum_chi_end`'s twin: the `hrowsSum` binder of
`ThmA2ChiSummed.thm_a2_spine_chiSummed` at a FREE `Cp ≥ 0`, with (R4) gone from the gate list
and the datum's block-liveness in its place. -/
theorem m4_hrowsSum_chi_zero :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd A G M Jb : ℕ) (H1 X h η ε : ℝ)
        (t₁ S : DirichletCharacter ℂ q → ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 Jb,
          SeamCoefWS Xd (calP A G j) (calQK A G M j) a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        (∀ j ∈ Finset.Icc 1 Jb, BlockLive (calP A G j) (calQK A G M j) a) →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK A G M 1 : ℕ) : ℝ) ≤ h →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * S χ ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1)
                      (mrAlpha η) Jb,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ m4MrowChiEnd Ct Cp A G M Jb Xd H1 η X ε (S χ) := by
  obtain ⟨Ct, hCt, hnum⟩ := m4_rowChi_number_of_capstone_zero
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X h η ε t₁ S hF hNXd hN4 hcoefWS
    hasupp hlive hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hrow := hnum Cp hCp q χ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X (2 * T) (t₁ χ) (S χ) η ε
    hF (by linarith) hNXd hN4 hcoefWS hasupp hlive hQXd hXdbig
    (hcap χ T hT hTX2 hTgate hTll)
  exact m4_rowChi_weighed_end hXd1 hF.H1_two hF.eta_pos hF.eta_lt hCt.le hCp hF.one_le_M
    hh4 hX0 hL0 hX4Xd hQ1h hT hrow

/-! ## §6 — THE DOOR INSTANCE: THE `𝒮`-SUPPORT IS FREE

⟦THE STONE THE WHOLE CHAIN RESTS ON⟧  The door's row datum is
`M4DoorRow.winCutH X_d (M4Assembly.doorCoeffU M)`, and `doorCoeffU M` is
`M4Sieve.memSCoeff` at the door's own two-level family.  So §1's three lemmas compose into a
`rfl`-level discharge: the door never has to supply block-liveness, and never had to supply
`blockfree_sum_le`'s error-domination gate either. -/

/-- **⟦THE DOOR DATUM IS BLOCK-LIVE, AT EVERY DOOR LEVEL⟧** (`blockLive_winCutH_doorCoeffU`) —
the scoper's ⟦PROBE 2⟧, factored.  `doorCoeffU M = 1_𝒮·λ` at the family
`(calP (Adoor M) (3072M), calQK (Adoor M) (3072M) M)` with `J = 2`; `MemS` gives a prime
factor in the block at each `i ∈ [1, 2]`, and the half-open cut cannot create support. -/
theorem blockLive_winCutH_doorCoeffU (M Xd : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 2) :
    BlockLive (calP (Adoor M) (3072 * M) i) (calQK (Adoor M) (3072 * M) M i)
      (winCutH Xd (doorCoeffU M)) :=
  blockLive_winCutH (blockLive_memSCoeff _ _ 2 liouvilleC hi)

/-- **THE PER-BASE GATE BUNDLE, DENSITY-FREE** (`DoorRowZeroBase`) — `DoorRowEndBase` with
the field `dom` REMOVED.  Six fields:

1. `Q2_le` — the door's cutoff `Q₂ ≤ X_d` (also `CalFrameK`'s at the door family);
2. `coefWS` — the STRICT relativized pair law `SeamRowWindowed.SeamCoefWS`, level by level;
3. `reg` — (R1) `log Q₂ ≤ √(log X_d)`;
4. `big` — (R2) `100 ≤ √(log X_d)`;
5. `h_four` — the weighting frame's floor `4 ≤ 2^j`;
6. `Q1_le_h` — the weighting frame's `Q₁ ≤ 2^j`.

⟦THE BONUS⟧ `DoorRowEndBase.dom` — the per-level error-domination product
`(√X_d + 1)·∏_{p∈[P_i,Q_i]}(1 + 3/p) ≤ X_d·(log P_i/log Q_i)` — is GONE.  It existed only to
feed `TypicalPrice.blockfree_sum_le`, whose row is now identically zero, and it was the field
that imposed an `X_d ≳ (M i²)⁸` floor on every socket base.  `reg` and `big` are NOT dropped:
they gate ⟦AMENDMENT 1⟧'s endpoint absorption in the `p²` row, which survives. -/
structure DoorRowZeroBase (M Xd j : ℕ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) : Prop where
  /-- The door's cutoff `Q₂ ≤ X_d`. -/
  Q2_le : calQK (Adoor M) (3072 * M) M 2 ≤ Xd
  /-- ⟦THE REPAIR⟧ the STRICT relativized pair law, level by level. -/
  coefWS : ∀ i ∈ Finset.Icc 1 2,
    SeamCoefWS Xd (calP (Adoor M) (3072 * M) i) (calQK (Adoor M) (3072 * M) M i)
      (winCutH Xd (doorCoeffU M)) (bU i) cU
  /-- (R1) `log Q₂ ≤ √(log X_d)`. -/
  reg : Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- (R2) `100 ≤ √(log X_d)`. -/
  big : (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- The weighting frame's floor `4 ≤ 2^j`. -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- The weighting frame's `Q₁ ≤ h` at `h = 2^j`. -/
  Q1_le_h : ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)

/-- **⟦IRON RULE 1: THIS PAGE ASKS STRICTLY LESS⟧**
(`doorRowZeroBase_of_doorRowEndBase`).  Every model of `M4RowsChiEnd.DoorRowEndBase` is a
model of `DoorRowZeroBase` — the twin forgets one field and adds none. -/
theorem doorRowZeroBase_of_doorRowEndBase {M Xd j : ℕ} {cU : ℕ → ℂ} {bU : ℕ → ℕ → ℂ}
    (h : DoorRowEndBase M Xd j cU bU) : DoorRowZeroBase M Xd j cU bU :=
  ⟨h.Q2_le, h.coefWS, h.reg, h.big, h.h_four, h.Q1_le_h⟩

/-- **⟦THE `a2Mrow`-GENRE ROW FAMILY AT THE DOOR, DENSITY-FREE⟧**
(`m4_hrowsSum_chi_door_zero`).  §5 at the door family and the vacuous ball, landed inside the
FROZEN interface's row constant `ThmA2.a2Mrow` at a FREE `Cp ≥ 0`.  The datum is pinned to
`winCutH X_d (doorCoeffU M)`, which is what makes the block-liveness gate free. -/
theorem m4_hrowsSum_chi_door_zero :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (Adoor M) (3072 * M) j) (calQK (Adoor M) (3072 * M) M j)
            (winCutH Xd (doorCoeffU M)) (bfam j) c) →
        Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU M))) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (Adoor M) (3072 * M))
                      (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU M))) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU M))) t‖ ^ 2)
            ≤ a2Mrow Ct Cp M Xd X ε := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_zero
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ c bfam hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hQXd
    hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (3072 * M) M 2) hXdQ
  have ha1 : ∀ n : ℕ, ‖winCutH Xd (doorCoeffU M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  refine (hrows Cp hCp q c (winCutH Xd (doorCoeffU M)) bfam ha1 hb1 hc1 N Xd
    (Adoor M) (3072 * M) M 2 (H1door M) X h (1 / 12) ε t₁ (fun _ => 0)
    (calFrameK_doorH1_at M Xd hM hXdQ) hNXd hN4 hcoefWS (fun n hn => winCutH_asupp hn)
    (fun i hi => blockLive_winCutH_doorCoeffU M Xd hi) hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h
    hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd_le_a2Mrow hM hXd1 hCp

/-- **⟦THE SLOT, MET, DENSITY-FREE⟧** (`m4_hrowsSlot_at_door_zero`).  The statement below is
`M4Assembly.m4_chiSummedFreeRow_of_doorAssembly`'s `hrows` binder VERBATIM at `Cs ≡ Ct`,
`Ccc ≡ Cp` with `Cp` a free nonnegative real — in particular at `Cp := 0`.  Supplied by the
door page through the datum bridge `M4Assembly.chiBarCoeff_doorRowDatum`. -/
theorem m4_hrowsSlot_at_door_zero :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ a2Mrow Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_door_zero
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum] using hslot

/-! ## §7 — ⟦ITEM 11 AT THE ZERO DENSITY⟧

`M4Assembly.m4_chiSummedFreeRow_of_doorAssembly` is already parametric in `Ccc`, so the twin
is one application at the free constant.  The point of the statement is what its `hframe`
now READS: at `Cp := 0` the frame's `gRows` field is

  `5760 · (a2RowsSum M X_d + 0·(2/M))  ≤  (log X_d)^{−1/500}` ,

i.e. the density debit — the ⟦SECOND HORN⟧'s whole content — is gone from the gate. -/

/-- **⟦A4 — ITEM 11 AT A FREE DENSITY CONSTANT⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_zero`).  `M4RowsChiEnd`'s `_end` assembly with `Cp`
free: `M4ChiSummed.M4ChiSummedFreeRow` at the door grade from `hM`, `hb1`, `hc1`, `hframe`,
`hbase` (`DoorRowZeroBase` — `dom`-free), `hcap`, `hband`, `henv`.

⟦THE ONE THING THAT MOVES AGAINST `m4_chiSummedFreeRow_of_doorAssembly_end`⟧ the density
constant is quantified `∀ Cp ≥ 0` instead of `∃ Cp > 0`, so a consumer may take `Cp := 0`;
and `hbase` asks six fields where the `_end` form asks seven. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_zero :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H j A s : ℕ, doorRowFloor M ≤ j →
          arcDen 12 H * a2DoorGrade M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
              (M₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband henv
  exact m4_chiSummedFreeRow_of_doorAssembly (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) hM hframe
    (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband henv

/-! ## §GK — the G-lever twin

The density-free door row page at `G := s13GK K M`.  `doorCoeffU_gk` and
`chiBarCoeff_doorRowDatum_gk` come from `M4RowsChiEnd`'s `§GK`, where they are the CANONICAL
mints on `M4Assembly`'s behalf (the ⟦PROVISIONAL⟧ tag is discharged — `M4Assembly`'s own `§GK`
records why they stay there).

⟦THE BLOCK IS CLEARED⟧ `m4_chiSummedFreeRow_of_doorAssembly_zero` (:868) was banked BLOCKED
on `M4Assembly.m4_chiSummedFreeRow_of_doorAssembly_gk` (and its `DoorFuseFrame_gk` /
`m4_chiFreeRowSq_sum_at_door_gk`).  All three exist now, and the twin is landed in `§GK.wire`
below — one `exact`, as predicted. -/

/-- ⟦PROBE 2⟧ AT THE G-LEVER (`blockLive_winCutH_doorCoeffU_gk`). -/
theorem blockLive_winCutH_doorCoeffU_gk (K : ℕ) (M Xd : ℕ) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 2) :
    BlockLive (calP (Adoor M) (s13GK K M) i) (calQK (Adoor M) (s13GK K M) M i)
      (winCutH Xd (doorCoeffU_gk K M)) :=
  blockLive_winCutH (blockLive_memSCoeff _ _ 2 liouvilleC hi)

/-- **THE PER-BASE GATE BUNDLE, DENSITY-FREE, AT THE G-LEVER**
(`DoorRowZeroBase_gk`).  SIX fields, names UNCHANGED and in this order: `Q2_le`, `coefWS`,
`reg`, `big`, `h_four`, `Q1_le_h`.  `reg` is byte-identical to `S13CapGate`'s `Q2_reg` at the
levered symbol — that is the propagator the whole S13 supply reads. -/
structure DoorRowZeroBase_gk (K : ℕ) (M Xd j : ℕ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) : Prop where
  /-- The door's cutoff `Q₂ ≤ X_d`. -/
  Q2_le : calQK (Adoor M) (s13GK K M) M 2 ≤ Xd
  /-- ⟦THE REPAIR⟧ the STRICT relativized pair law, level by level. -/
  coefWS : ∀ i ∈ Finset.Icc 1 2,
    SeamCoefWS Xd (calP (Adoor M) (s13GK K M) i) (calQK (Adoor M) (s13GK K M) M i)
      (winCutH Xd (doorCoeffU_gk K M)) (bU i) cU
  /-- (R1) `log Q₂ ≤ √(log X_d)`. -/
  reg : Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- (R2) `100 ≤ √(log X_d)`. -/
  big : (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- The weighting frame's floor `4 ≤ 2^j`. -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- The weighting frame's `Q₁ ≤ h` at `h = 2^j`. -/
  Q1_le_h : ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)

/-- **⟦IRON RULE 1: THIS PAGE ASKS STRICTLY LESS⟧ AT THE
G-LEVER** (`doorRowZeroBase_of_doorRowEndBase_gk`). -/
theorem doorRowZeroBase_of_doorRowEndBase_gk (K : ℕ) {M Xd j : ℕ} {cU : ℕ → ℂ}
    {bU : ℕ → ℕ → ℂ}
    (h : DoorRowEndBase_gk K M Xd j cU bU) : DoorRowZeroBase_gk K M Xd j cU bU :=
  ⟨h.Q2_le, h.coefWS, h.reg, h.big, h.h_four, h.Q1_le_h⟩

/-- **⟦THE `a2Mrow`-GENRE ROW FAMILY AT THE DOOR, DENSITY-FREE⟧ AT THE
G-LEVER** (`m4_hrowsSum_chi_door_zero_gk`). -/
theorem m4_hrowsSum_chi_door_zero_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (Adoor M) (s13GK K M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (Adoor M) (s13GK K M) j) (calQK (Adoor M) (s13GK K M) M j)
            (winCutH Xd (doorCoeffU_gk K M)) (bfam j) c) →
        Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_gk K M))) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (Adoor M) (s13GK K M))
                      (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_gk K M))) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_gk K M))) t‖ ^ 2)
            ≤ a2Mrow_gk K Ct Cp M Xd X ε := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_zero
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ c bfam hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hQXd
    hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (s13GK K M) M 2) hXdQ
  have ha1 : ∀ n : ℕ, ‖winCutH Xd (doorCoeffU_gk K M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  refine (hrows Cp hCp q c (winCutH Xd (doorCoeffU_gk K M)) bfam ha1 hb1 hc1 N Xd
    (Adoor M) (s13GK K M) M 2 (H1door M) X h (1 / 12) ε t₁ (fun _ => 0)
    (calFrameK_doorH1_at_gk K M Xd hM hK hXdQ) hNXd hN4 hcoefWS (fun n hn => winCutH_asupp hn)
    (fun i hi => blockLive_winCutH_doorCoeffU_gk K M Xd hi) hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h
    hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd_le_a2Mrow_gk K hM hXd1 hCp

/-- **⟦THE SLOT, MET, DENSITY-FREE⟧ AT THE G-LEVER**
(`m4_hrowsSlot_at_door_zero_gk`). -/
theorem m4_hrowsSlot_at_door_zero_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase_gk K M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_door_zero_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_gk] using hslot

-- #audit (temporary)


/-! ### §GK.wire — THE BLOCKED ASSEMBLY WIRE, LANDED

⟦THE BLOCK ABOVE IS CLEARED⟧ `M4Assembly` / `M4AssemblyPrime` grew their own `§GK`
(`DoorFuseFrame_gk`, `DoorFuseFrame_pool'_gk`, `m4_chiFreeRowSq_sum_at_door_gk`,
`m4_chiSummedFreeRow_of_doorAssembly{,_pool'}_gk`), so the wire below is the landed proof
with those names substituted.  `hK : K ≤ 1.7·10⁸` is the slot supplier's frame side
condition, inherited. -/

/-- **⟦ITEM 11⟧ AT THE ASSEMBLY WIRE, DENSITY-FREE, AT THE LEVER** —
`m4_chiSummedFreeRow_of_doorAssembly_zero` (:868). -/
theorem m4_chiSummedFreeRow_of_doorAssembly_zero_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame_gk K M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H j A s : ℕ, doorRowFloor M ≤ j →
          arcDen 12 H * a2DoorGrade_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
              (M₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M RSbig) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband henv
  exact m4_chiSummedFreeRow_of_doorAssembly_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) hM hframe
    (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband henv

end Salt.MR
