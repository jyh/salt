/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ThmA2ChiSummed
import Salt.MR.ThmA2Rows
import Salt.MR.USetGChiTS
import Salt.MR.TLegChi
import Salt.MR.SeamNumber

/-!
# M4RowsChi — the per-`χ` SEAM ROW FAMILY feeding `hrowsSum` (wave ⟦D2-REDERIVE⟧)

`docs/blueprints/flags.md` ⟦C2-SCOPE lands⟧ §4.1 (the per-`χ` instantiation table),
⟦TLEG-FACT lands⟧ (the scope fence: "the twisted PRICING side does not exist yet"),
⟦RELIFT-B lands⟧ (the fibrewise graded A3), and THE 0730 COUNCIL's C5 wave plan.  This is the
second bank's **D2** item: the `Σ_χ` row family that discharges the `hrowsSum` slot of
`ThmA2ChiSummed.thm_a2_spine_chiSummed` and `thm_a2'_of_rows_chiSummed`.

## What this file is, and what it is not

Purely ADDITIVE.  Every rung is an INSTANTIATION or a `.trans` of a landed theorem: no
estimate is re-derived, no constant re-chosen, and no landed declaration is touched.  The
`q = 1` chain it mirrors is `CapFreeArm3` §6–§9 → `SeamNumber.seam_row_number` →
`ThmA2Rows.a2Rows_of_capfree3_end`; the mirror is possible because **every stone of that chain
is datum-generic** (C2-SCOPE §4.1), so the character enters only through the twisted datum
`χ̄a`, `χ̄c`, `χ̄(b j)`.

The four legs, and where each comes from:

* the **`𝒰`-leg** — LANDED `USetGChiTS.usetGChi_window_meansq_gated_family` (the C2
  deliverable), read fibrewise at §1's pair set and per-`χ` by nonnegativity (§3);
* the **`𝒯`-leg** — LANDED `TLegChi.TLeg_feeds_capstone_chi`, fused with its price (§7);
* the **`𝒯`-leg PRICING** — `TypicalPriceK.sum_lemma12Rows_priced_calibratedK2` at the
  twist (⟦ii-8c⟧, §6): the half TLEG-FACT's fence left open;
* the **ball leg** — **CARRIED** as the per-`χ` `hSup` binder of
  `SeamBallWeighted.ball_leg_of_sup_weighted` at the centre `t₁ χ` and sup `S χ`
  (supplier: the BALL-SUP leg; vacuous at `t₁ ≡ 0`, `S ≡ 0`);
* the **far tail** — the landed `2·(T_ann/X + 1)(log X)^{−θ₂₉₃+ε}` balance
  (`USetGradedBalance.hUG_balance`), reached through `USetPrice.balance_priced_main` and
  `rem_priced`.

## ⟦ii-8⟧ — the two pricing adapters this wave owed

* **§2, the block-price adapter.**  The fibrewise A3 exits at
  `4|I|·Σ_j (𝒯_S-grade + 81·Cs·Rbd²(H/j)²) + 2E`; the pricing ladder consumes
  `4|I|·(|I|·KS + 54·Cq·Rbd²H²/(⌊H log P⌋−1)) + 2E`.  The bridge is
  `USetBalance.block_sum_bound` at `Cq := 3·Cs/2`, since `54·(3/2) = 81` — the pair row's
  `81 = 3·27` against the `q = 1` row's `54 = 2·27`.  **The hybrid debit is carried in the
  constant, never absorbed.**
* **§6, the Lemma-12 pricing at the twist.**  Free: the pricer is `∀ a b c` and all four of
  its coefficient hypotheses lift (`TLegChi` §1's three lifts plus §4's dyadic pin).

## ⟦THE `Σ_χ` → PER-`χ` READ, and its price⟧

`usetGChi_window_meansq_gated_family` bounds a CHARACTER SUM of fibre integrals; `hrowsSum` is
per character.  §3 reconciles them by NONNEGATIVITY alone (`Finset.single_le_sum`), so the
resulting row constant is character-UNIFORM in everything but the carried ball sup `S χ`.  At
the spine that costs one `φ(q)` on `Σ_χ Mrow χ` — C2-SCOPE's finding K-2 ("a per-`χ` Rbd at
uniform grade is purchasable for ONE `φ(q)`"), read at the row and stated where it is paid.

## ⟦THE CARRIED HYPOTHESES — the full residue list (PORT-AUDIT law)⟧

The deliverables §9/§10/§11b are conditional on exactly these, all in-statement:

1. **the A3 capstone family** — `∀ χ, ∀ T`, the graded row at `T_ann = 2T`.  Its supplier is
   §5 (`m4_rowChi_capstone`) IN THIS FILE, and §5's own residue is: the graded razor's gates
   at `(q, 2T)` (the `𝒰`-package, the debit `q^{2α} ≤ X^ε`, the budget), the per-`(q,T)`
   socket floor `T₀ ≤ 2T` with G1–G4, the `𝒯_S` budget `KS` with its gate, Lemma 12's
   `χ`-summed error row `E` with its absorption, the `X`-side `H₈₃` pins, and items 2–3 below;
2. **the co-factor binder `Rbd`** — `‖ramR … (χ̄b) t‖ ≤ Rbd` on `Ann ∖ ball(t₁ χ)`, with its
   grade `Rbd ≤ C_R (log X)^{−ρ₂₉₃}` and the `C_q`-gate.  **Supplier LANDED**:
   `RbdSupply.rbd_binder_of_doorSocket_free` (the `∀χ` door socket at `Ps = 1` IS this
   binder); left as a binder here, as the wave brief directs;
3. **the ball binder `hSup`** — per-`χ` centre `t₁ χ`, sup `S χ`.  Supplier: the BALL-SUP leg
   (mid-flight at dispatch); vacuous at `t₁ ≡ 0`, `S ≡ 0` by
   `CapFreeArm.ball_leg_vacuous_at_zero`, which is the `q = 1` cap-free arm's own choice and
   the setting of §11b;
4. **the `𝒯`-side frame** — `CalFrameK η H₁ A G M Jb X_d` (LANDED at the door:
   `ThmA2.calFrameK_doorH1_at`), the Ramaré factorization with its two `1`-bounds and its
   dyadic window, `2X_d ≤ N`;
5. **the six reconciliation gates** (R1)–(R6) of `SeamNumber` — character-free, verbatim;
6. **the weighting frame** — `4 ≤ h`, `0 < X`, `0 ≤ log X`, `X ≤ 4X_d`, `Q₁ ≤ h`.

⟦THE ONE STATION-LEVEL FENCE, stated not hidden⟧  §7 carries the A3 capstone row as a
hypothesis for the same reason `TLegExit`'s H-4 and `TLegChi` §3 do: the `𝒯`-side gate family
(`CalFrameK` + the `X_d`-side reconciliation) and the `𝒰`-side gate family (the graded razor
at `(q,2T)` + the socket floor) are reconciled at the STATION.  What the kernel certifies here
is the shape fit, the price and the weighting — the simultaneous satisfiability of the two
families is recorded, not manufactured.  (RELIFT-B's ⟦K-5⟧ walk exhibits a regime where the
`𝒰`-side list holds; the `𝒯`-side is the landed door frame.)

## ⟦THE FOUR LOG SCALES⟧

Kept strictly apart, and none is ever substituted for another: `log(qT_ann)` (the graded
count, height and razor), `log(5T_ann+1)` (the socket's four gates G1–G4, and nothing else),
`L ≥ log(qT_ann)` (the `𝒯_L` kill), and `log X` (the `𝒯_S` level, the modulus gate
`q ≤ (log X)^{12}`, the grades and the balance).  `√(log X_d)` — the pricing side's own
cutoff base — is a FIFTH quantity and is never identified with `√(log X)`: `SeamNumber`'s law
#253 note explains why the bridge `X_d ≤ X` points the wrong way, and (R1) rides accordingly.

## Contents

* §1 the row's pair set and its fibre/measurability/containment trio;
* §2 ⟦ii-8a,b⟧ the block-price adapter (`81 = 54·(3/2)`);
* §3 the graded `𝒰`-leg, PER CHARACTER, at the `hUG_supplied` shape;
* §4 the twisted datum's two support lifts;
* §5 the per-`χ` A3 capstone row (the four legs assembled);
* §6 ⟦ii-8c⟧ the Lemma-12 row sum priced at twisted data;
* §7 the per-`χ` seam row AS A NUMBER (the `χ`-twin of `SeamNumber.seam_row_number`);
* §8 the weighting page — the `T`-family collapses to `m4MrowChi`;
* §9 **the deliverable**: `m4_hrowsSum_chi`, the `hrowsSum` slot per character;
* §10 the slot discharged into `thm_a2_spine_chiSummed`;
* §11 the door bridge `m4MrowChi ≤ a2Mrow`, and `m4_hrowsSum_chi_door` — the frozen
  interface's genre.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 eq (21), §8.1–§8.3 pp. 25–29, §9 p.31;
`docs/blueprints/flags.md` ⟦C2-SCOPE lands⟧ / ⟦TLEG-FACT lands⟧ / ⟦RELIFT-B lands⟧ /
THE 0730 COUNCIL (2026-07-30); `docs/exploration/a4-bridge-freeze-0730.md` v2.3.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

/-! ## §1 — the pair set the fibrewise `𝒰`-leg is read on -/

/-- **THE ROW'S PAIR SET.**  Fibre by fibre it is exactly the set the graded seam row's `hU`
binder integrates over (`SeamGraded.prop_A3_T1_row_split_weightedG`), at a PER-CHARACTER ball
centre `t₁ χ` (C2-SCOPE finding K-3) and the `χ̄`-twisted partition datum. -/
def rowPairSetG (q : ℕ) (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J : ℕ)
    (X Tann : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ) : Set (DirichletCharacter ℂ q × ℝ) :=
  {r | r.2 ∈ (seamAnn X Tann \ seamBall X (t₁ r.1))
        ∩ UsetG (chiBarCoeff q r.1 c) Pseq Qseq Hseq αseq J}

/-- The fibre of `rowPairSetG` at `χ` IS the graded row's `𝒰`-domain at that character. -/
lemma rowPairSetG_fibre (q : ℕ) (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J : ℕ)
    (X Tann : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ) (χ : DirichletCharacter ℂ q) :
    {t : ℝ | (χ, t) ∈ rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁}
      = (seamAnn X Tann \ seamBall X (t₁ χ))
          ∩ UsetG (chiBarCoeff q χ c) Pseq Qseq Hseq αseq J := rfl

/-- Every fibre is measurable (the row's own domain: an annulus minus a ball, cut by the
graded `𝒰`). -/
lemma measurableSet_rowPairSetG_fibre (q : ℕ) (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ)
    (Hseq αseq : ℕ → ℝ) (J : ℕ) (X Tann : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ)
    (χ : DirichletCharacter ℂ q) :
    MeasurableSet {t : ℝ | (χ, t) ∈ rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁} := by
  rw [rowPairSetG_fibre]
  exact ((measurableSet_seamAnn X Tann).diff (measurableSet_seamBall X (t₁ χ))).inter
    (measurableSet_UsetG _ Pseq Qseq Hseq αseq J)

/-- The ordinates lie in `[−Tann, Tann]` — the annulus' own containment. -/
lemma rowPairSetG_sub (q : ℕ) (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J : ℕ)
    (X Tann : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ) :
    ∀ r ∈ rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁, r.2 ∈ Set.Icc (-Tann) Tann :=
  fun _ hr => seamAnn_subset_Icc X Tann hr.1.1

/-- The pair set sits inside the graded pair `𝒰` — by `USetGChi.UsetGChi_fibre`, fibrewise. -/
lemma rowPairSetG_subset_UsetGChi (q : ℕ) (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ)
    (Hseq αseq : ℕ → ℝ) (J : ℕ) (X Tann : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ) :
    rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁ ⊆ UsetGChi q c Pseq Qseq Hseq αseq J :=
  fun _ hr => hr.2

/-! ## §2 — ⟦ii-8⟧ THE BLOCK-PRICE ADAPTER: the A3 shape into the `hUG_supplied` shape

`USetGChiTS.usetGChi_window_meansq_gated_family` exits at the A3 shape

  `4·|I|·Σ_{j∈I} (𝒯_S-grade j + 81·Cs·Rbd²·(H/j)²) + 2E`,

while the whole landed pricing ladder (`USetPrice.balance_priced_main`, and through it the
graded balance and the row) consumes the `hUG_supplied` shape

  `4·|I|·(|I|·KS + 54·Cq·Rbd²·H²/(⌊H log P⌋−1)) + 2E`.

The adapter is the landed `USetBalance.block_sum_bound` (the `Σ_j 1/j²` telescope) read at
`Cq := 3·Cs/2`, since `54·(3/2) = 81`: the `𝒯_L` debit `81 = 3·27` of the pair/hybrid row
against the `q = 1` row's `54 = 2·27` is EXACTLY the factor `3/2` this substitution names, and
it is carried in the constant, never absorbed. -/

/-- **⟦ii-8a⟧ THE `𝒯_L` BLOCK WEIGHT AT THE PAIR ROW'S DEBIT.**  `USetBalance.tL_block_weight`
at `Cq := 3·Cs/2`: the A3 exit's per-block `81·Cs·Rbd²·(H/j)²` is the `54·Cq·…` shape
`block_sum_bound` consumes. -/
lemma tL_block_weight_chi (Cs H Rbd : ℝ) (j : ℕ) (hCs : 0 ≤ Cs) (hRbd : 0 ≤ Rbd) :
    81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2
      ≤ 54 * (3 * Cs / 2) * Rbd ^ 2 * H ^ 2 * (1 / (j : ℝ) ^ 2) := by
  have h := tL_block_weight (3 * Cs / 2) H Rbd Rbd j (by linarith) hRbd le_rfl
  have heq : 54 * (3 * Cs / 2) * Rbd ^ 2 * (H / (j : ℝ)) ^ 2
      = 81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2 := by ring
  rw [heq] at h
  exact h

/-- **⟦ii-8b⟧ THE BLOCK-SUM ADAPTER.**  The A3 exit's `Σ_{j∈I}` priced at the `hUG_supplied`
shape, with the `𝒯_S` grade majorised uniformly by `KS` and the `𝒯_L` grade telescoped. -/
lemma usetGChi_block_price (H : ℝ) (N Xd P Q M : ℕ) (b : ℕ → ℂ) (X Tann KS Cs Rbd : ℝ)
    (hCs : 0 ≤ Cs) (hRbd : 0 ≤ Rbd) (hj₀ : 2 ≤ ⌊H * Real.log (P : ℝ)⌋₊)
    (hKS : ∀ j ∈ ramI H P Q,
      5128 * (Real.log X) ^ (-200 : ℝ) * (M : ℝ) * (1 + Real.log (2 * Tann))
          * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) ≤ KS) :
    (∑ j ∈ ramI H P Q,
        (5128 * (Real.log X) ^ (-200 : ℝ) * (M : ℝ) * (1 + Real.log (2 * Tann))
            * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
          + 81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2))
      ≤ ((ramI H P Q).card : ℝ) * KS
        + 54 * (3 * Cs / 2) * Rbd ^ 2 * H ^ 2 / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1) :=
  block_sum_bound H P Q _ _ KS (3 * Cs / 2) Rbd hKS (by linarith)
    (fun j _ => tL_block_weight_chi Cs H Rbd j hCs hRbd) hj₀

/-! ## §3 — THE PER-`χ` `𝒰`-LEG, at the `hUG_supplied` shape

`USetGChiTS.usetGChi_window_meansq_gated_family` is a `Σ_χ` statement; the `hrowsSum` slot is
PER character.  The two are reconciled by NONNEGATIVITY and nothing else: every summand of the
character sum is a set integral of `‖·‖²`, so each single fibre is bounded by the whole sum
(`Finset.single_le_sum`).  The price is honest and stated: the resulting `Mrow` is
character-UNIFORM, so `Σ_χ Mrow χ = φ(q)·Mrow` at the spine — C2-SCOPE's finding K-2 ("a
per-`χ` Rbd at uniform grade is purchasable for ONE `φ(q)`"), read at the row.

The conclusion is then adapted to the `hUG_supplied` shape by §2, so that the ENTIRE landed
pricing ladder (`balance_priced_main` → `hUG_balance` → the graded row) applies verbatim. -/

set_option maxHeartbeats 800000 in
-- Same cause as the landed family theorem it instantiates: the composition threads the
-- fibrewise pair set through a gate list of ~60 binders, and the unifier needs room for the
-- `UsetG (chiBarCoeff …)` fibre expressions.
/-- **THE GRADED `𝒰`-LEG, PER CHARACTER** (`usetGChi_row_exit_perChi`).  For each `χ`,

  `∫_{(Ann ∖ ball(t₁ χ)) ∩ 𝒰G(χ̄c)} ‖spoly N (χ̄a) t‖²`
    `≤ 4·|I|·(|I|·KS + 54·Cq·Rbd²·H²/(⌊H log P⌋−1)) + 2E`,

the shape `USetGradedBalance.hUG_supplied` exits at and `USetPrice.balance_priced_main`
consumes.  `Cq = 3·Cs/2` where `Cs` is the port's socket constant (§2's ⟦ii-8⟧ debit).

⟦THE BINDERS⟧ are `usetGChi_window_meansq_gated_family`'s, with THREE changes:
* the `𝔄`-package is replaced by the per-character ball centre `t₁ : χ ↦ t₁ χ` (the pair set
  is `rowPairSetG`, built here, so no set binder survives);
* `hR` is stated FIBREWISE on the annulus-minus-ball (strictly stronger than the pair form the
  family asks for, and the shape `RbdSupply.rbd_binder_of_doorSocket_free` supplies);
* the `𝒯_S` grade is majorised by the free `KS` (`hKS`), and `hj₀ : 2 ≤ ⌊H log P⌋` is added —
  both are `block_sum_bound`'s demands. -/
theorem usetGChi_row_exit_perChi :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (Tann VJ V L X : ℝ), 1 ≤ Tann → 1 < (q : ℝ) * Tann →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann →
        30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * Tann)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → Tann ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        -- ⟦THE PER-`(q,T)` FLOOR — the socket's discharge, verbatim⟧
        T₀ ≤ Tann →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * Tann + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * Tann) → Real.log ((q : ℝ) * Tann) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q M : ℕ) (a b cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 M) →
        thinBundleGChi ((q : ℝ) * Tann) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ (M : ℝ) →
        (∀ j ∈ ramI H P Q, H ≤ (j : ℝ)) →
        (∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * Tann) →
        (∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * Tann) / Real.log (ramQbase H P j)) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ Tann ^ 10) →
        (∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L) →
        (∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase H P j)) ^ 2) →
      ∀ Rbd : ℝ, 0 ≤ Rbd →
      ∀ t₁ : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ j ∈ ramI H P Q,
          ∀ t ∈ seamAnn X Tann \ seamBall X (t₁ χ),
            ‖ramR H N Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd) →
      ∀ E : ℝ, (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
          ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
      ∀ KS : ℝ,
        (∀ j ∈ ramI H P Q,
          5128 * (Real.log X) ^ (-200 : ℝ) * (M : ℝ) * (1 + Real.log (2 * Tann))
              * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
            ≤ KS) →
        2 ≤ ⌊H * Real.log (P : ℝ)⌋₊ →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (seamAnn X Tann \ seamBall X (t₁ χ))
            ∩ UsetG (chiBarCoeff q χ c) Pseq Qseq Hseq αseq J,
            ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (((ramI H P Q).card : ℝ) * KS
                  + 54 * Cq * Rbd ^ 2 * H ^ 2
                      / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E := by
  obtain ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hT₀, hKq, hKs, hfam⟩ :=
    usetGChi_window_meansq_gated_family
  refine ⟨3 * Cs / 2, cs, T₀, Kq, Ks, by linarith, hcs, hT₀, hKq, hKs, ?_⟩
  intro q _ c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X hT1 hqT hP3
    hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV H hH2 N Xd P Q M a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL
    hgate Rbd hRbd t₁ hR E herr KS hKS hj₀ χ
  -- ⟦the Σ_χ exit at the row's own pair set⟧
  have hsum := hfam q c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X
    hT1 hqT hP3 hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T
    hG1 hG2 hG3 hG4 hlogT1 hTL hLe hlogV H hH2 N Xd P Q M a b cf hcf1 hM hbudget hHj hB3
    hBT hκ30 hBT10 hWL hgate Rbd hRbd
    (rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁)
    (measurableSet_rowPairSetG_fibre q c Pseq Qseq Hseq αseq J X Tann t₁)
    (rowPairSetG_sub q c Pseq Qseq Hseq αseq J X Tann t₁)
    (rowPairSetG_subset_UsetGChi q c Pseq Qseq Hseq αseq J X Tann t₁)
    (fun j hj r hr => hR r.1 j hj r.2 hr.1) E herr
  -- ⟦the per-χ read: every fibre integral is nonnegative, so one is at most the sum⟧
  have hnn : ∀ χ' ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      (0 : ℝ) ≤ ∫ t in {t : ℝ | (χ', t) ∈ rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁},
        ‖spoly N (chiBarCoeff q χ' a) t‖ ^ 2 := by
    intro χ' _
    exact setIntegral_nonneg
      (measurableSet_rowPairSetG_fibre q c Pseq Qseq Hseq αseq J X Tann t₁ χ')
      (fun _ _ => by positivity)
  have hsingle := Finset.single_le_sum hnn (Finset.mem_univ χ)
  -- ⟦the ⟦ii-8⟧ block price⟧
  have hprice := usetGChi_block_price H N Xd P Q M b X Tann KS Cs Rbd hCs.le hRbd hj₀ hKS
  have hcard0 : (0 : ℝ) ≤ 4 * ((ramI H P Q).card : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hprice hcard0
  rw [rowPairSetG_fibre] at hsingle
  linarith

/-! ## §4 — the twisted datum's two support lifts

The `𝒯`-leg's three lifts are landed (`TLegChi` §1).  The ROW needs two more, both one-liners:
the seam support pin (`n ≤ X → aₙ = 0`) and the dyadic window pin the pricing side asks for
(`aₙ ≠ 0 → X_d ≤ n ≤ 2X_d`).  Both hold because the twist can only KILL coefficients. -/

/-- The seam support pin survives the twist. -/
lemma chiBarCoeff_seam_supp {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ℕ → ℂ} {X : ℝ}
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) :
    ∀ n : ℕ, (n : ℝ) ≤ X → chiBarCoeff q χ a n = 0 := by
  intro n hn
  simp [chiBarCoeff_apply, hsupp n hn]

/-- The dyadic window pin survives the twist (the twisted support is a SUBSET). -/
lemma chiBarCoeff_dyadic_supp {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ℕ → ℂ} {Xd : ℕ}
    (h : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) :
    ∀ n : ℕ, chiBarCoeff q χ a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd := by
  intro n hn
  refine h n (fun h0 => hn ?_)
  simp [chiBarCoeff_apply, h0]

/-! ## §5 — THE PER-`χ` CAPSTONE ROW

§3's `𝒰`-exit, priced by the landed ladder (`USetPrice.balance_priced_main` for the block leg,
`USetPrice.rem_priced` for Lemma 12's error leg, `USetGradedBalance.hUG_balance` for the
`θ₂₉₃` balance) and plugged into `SeamGraded.prop_A3_T1_row_split_weightedG` at the twisted
datum.  Every one of those four stones is CHARACTER-BLIND and datum-generic, so this section
adds no estimate: it is the q = 1 §7 of `CapFreeArm3` read at `(χ̄a, χ̄c)`.

The output is EXACTLY the hypothesis `TLegChi.TLeg_feeds_capstone_chi` carries — which is why
§6 is a `.trans` and nothing more. -/

set_option maxHeartbeats 1000000 in
-- Same cause as `CapFreeArm3` §7 (the `q = 1` twin): four landed prices are composed into one
-- row, each carrying its own gate family, at twisted data.
/-- **THE PER-`χ` CAPSTONE ROW** (`m4_rowChi_capstone`).  At `H := H₈₃ X θ₂₉₃`, for each `χ`:

  `∫_{Ann} ‖spoly N (χ̄a)‖² ≤ 8·S(χ)² + ∫_{(Ann∖ball(t₁ χ)) ∩ 𝒯totG(χ̄c)} ‖spoly N (χ̄a)‖²`
  `                            + 2·((Tann/X + 1)·(log X)^{−θ₂₉₃+ε_r})`.

⟦THE BALL LEG IS CARRIED⟧ `hSup` is the per-character binder of
`SeamBallWeighted.ball_leg_of_sup_weighted` at the centre `t₁ χ` and the sup constant `S χ`
(C2-SCOPE K-3: per-`χ` centres are the natural shape).  Its supplier is the BALL-SUP leg; at
`t₁ ≡ 0` the landed `CapFreeArm.ball_leg_vacuous_at_zero` discharges it at `S ≡ 0`.

⟦TWO EXPONENTS, KEPT APART⟧ `ε` is the CHARACTER DEBIT exponent (`q^{2α} ≤ X^ε`, spent inside
the razor's budget); `ε_r` is the REMAINDER absorption exponent (`8640 ≤ (log X)^{ε_r}`) of
`rem_priced`.  They are never identified. -/
theorem m4_rowChi_capstone :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (Tann VJ V L X : ℝ), 1 ≤ Tann → 1 < (q : ℝ) * Tann →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann →
        30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * Tann)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → Tann ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        T₀ ≤ Tann →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * Tann + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * Tann) → Real.log ((q : ℝ) * Tann) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
        -- ⟦THE `X`-SIDE FRAME⟧ (the `H₈₃` pins the landed pricing ladder reads)
        2 ≤ H83 X theta293 → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann →
      ∀ (N Xd P Q M : ℕ) (a b cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 M) →
        thinBundleGChi ((q : ℝ) * Tann) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ (M : ℝ) →
        (∀ j ∈ ramI (H83 X theta293) P Q, H83 X theta293 ≤ (j : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 3 ≤ ramQbase (H83 X theta293) P j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          (ramQbase (H83 X theta293) P j : ℝ) ≤ (q : ℝ) * Tann) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          30 ≤ Real.log ((q : ℝ) * Tann) / Real.log (ramQbase (H83 X theta293) P j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          (ramQbase (H83 X theta293) P j : ℝ) ≤ Tann ^ 10) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          Real.log (ramQbase (H83 X theta293) P j) ≤ L) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase (H83 X theta293) P j)) ^ 2) →
        -- ⟦THE CO-FACTOR BOUND AND ITS GRADE⟧ (`RbdSupply` closes the supply side)
      ∀ (Rbd CR : ℝ), 0 ≤ Rbd → Rbd ≤ CR * (Real.log X) ^ (-rho293) →
        1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
      ∀ t₁ : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ j ∈ ramI (H83 X theta293) P Q,
          ∀ t ∈ seamAnn X Tann \ seamBall X (t₁ χ),
            ‖ramR (H83 X theta293) N Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd) →
        -- ⟦THE `𝒯_S` GRADE BUDGET⟧
      ∀ KS : ℝ, 0 ≤ KS →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          5128 * (Real.log X) ^ (-200 : ℝ) * (M : ℝ) * (1 + Real.log (2 * Tann))
              * (∑ m ∈ Finset.Icc 1 M,
                  ‖ramRcoeff (H83 X theta293) N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
            ≤ KS) →
        32 * (Real.log X) ^ (2 + 2 * theta293) * KS ≤ (Real.log X) ^ (-theta293) →
        -- ⟦LEMMA 12's ERROR ROW, `χ`-SUMMED⟧ and its absorption
      ∀ (E EP2 εr : ℝ), 0 ≤ εr → 8640 ≤ (Real.log X) ^ εr →
        12 * EP2 ≤ (Real.log X) ^ (-theta293 + εr) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
          ‖ramErr (H83 X theta293) N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
        -- ⟦THE ROW FRAME AND THE CARRIED BALL LEG⟧
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
      ∀ S : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann →
          |t - t₁ χ| ≤ seamRad X → ∀ m : ℕ, m ≤ N →
            ‖spolyA (chiBarCoeff q χ a) t m‖ ≤ S χ * m / (1 + |t - t₁ χ|)) →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 8 * S χ ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X (t₁ χ))
                ∩ seamTtotG (chiBarCoeff q χ c) Pseq Qseq Hseq αseq J,
                ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + εr)) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, hexit⟩ := usetGChi_row_exit_perChi
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, ?_⟩
  intro q _ c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X hT1 hqT hP3
    hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV hH2 hLXe hL4 hTgate
    N Xd P Q M a b cf hcf1 hPlow hQ0 hQhigh hM hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate
    Rbd CR hRbd hRgrade hCqgate t₁ hR KS hKS0 hKS hKSgate E EP2 εr hεr habs hEP2 hErow herr
    hXN hN2 hsupp S hSup χ
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hH0 : (0 : ℝ) ≤ H83 X theta293 := by linarith
  have hHeq : H83 X theta293 = (Real.log X) ^ theta293 := by rw [H83]
  have hTann0 : (0 : ℝ) ≤ Tann := by linarith
  have hfl := floor_pin X P hL4 hPlow
  -- ⟦the per-χ `𝒰` exit⟧
  have hU := hexit q c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X
    hT1 hqT hP3 hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T
    hG1 hG2 hG3 hG4 hlogT1 hTL hLe hlogV (H83 X theta293) hH2 N Xd P Q M a b cf hcf1 hM
    hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate Rbd hRbd t₁ hR E herr KS hKS hfl.1 χ
  -- ⟦the block leg, priced at `θ₂₉₃`⟧
  have hmain := balance_priced_main X (H83 X theta293) Cq CR KS Rbd P Q hL0 hH0
    (ramI_card_le_pin X P Q hQ0 hQhigh hLXe) (le_of_eq hHeq) hfl.2
    hCq.le hKS0 hRbd hRgrade hKSgate hCqgate
  -- ⟦Lemma 12's error leg, absorbed⟧
  have hrem := rem_priced X Tann (H83 X theta293) εr EP2 E hL1 hX0 hTann0
    (le_of_eq hHeq.symm) habs hEP2 hErow
  -- ⟦the balance⟧
  have hbal := hUG_balance (chiBarCoeff q χ a) (chiBarCoeff q χ c) N Pseq Qseq Hseq αseq J
    X Tann (t₁ χ) εr _ _ hεr hL1 hX0 hTgate hU hmain hrem
  exact prop_A3_T1_row_split_weightedG (chiBarCoeff q χ a) N (chiBarCoeff q χ c) Pseq Qseq
    Hseq αseq J X Tann (t₁ χ) (S χ) _ hL0.le hTann0 hX0 hXN hN2
    (chiBarCoeff_seam_supp χ hsupp) (hSup χ) hbal

/-! ## §6 — ⟦ii-8c⟧ THE `𝒯`-LEG PRICING AT TWISTED DATA

⟦TLEG-FACT's FENCE, LIFTED⟧  The `TLegChi` page stopped at the leg's exit because "the
twisted pricing side does not exist yet".  It does now, and it costs one instantiation:
`TypicalPriceK.sum_lemma12Rows_priced_calibratedK2` is fully datum-generic
(`∀ a (b : ℕ → ℕ → ℂ) c`, four coefficient hypotheses and the `X_d`-side gates), and all four
coefficient hypotheses lift to the twist by the landed lifts of `TLegChi` §1 plus §4's dyadic
pin.  The PRICE — the `X_d`-side reconciliation gates (R1)–(R6) of `SeamNumber` — is
character-free and rides verbatim.

`C` is the same universal constant the `q = 1` pricing produces: character- and
modulus-uniform, bound outside `q` and outside `χ`. -/

/-- **⟦ii-8c⟧ THE LEMMA-12 ROW SUM, PRICED AT TWISTED DATA** (`sum_lemma12Rows_priced_chi`).
`TypicalPriceK.sum_lemma12Rows_priced_calibratedK2` at `(χ̄a, χ̄b, χ̄c)`; the hypotheses are
stated on the UNTWISTED sequences and the bound is the `q = 1` one VERBATIM — the twist
touches neither the `480·(T/X_d+1)` factor nor the `Σ_j` row nor the `C·(2/M)` density
collection. -/
theorem sum_lemma12Rows_priced_chi :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (A G M Jb N Xd : ℕ) (H1 T : ℝ) (a c : ℕ → ℂ) (b : ℕ → ℕ → ℂ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 1 ≤ Xd → 0 ≤ T → 0 < H1 → (N : ℝ) ≤ 4 * (Xd : ℝ) →
      (∀ j ∈ Finset.Icc 1 Jb,
        Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) →
      (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
      (∀ j ∈ Finset.Icc 1 Jb,
        ((Nat.sqrt Xd : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ)
            * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ))) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
        c p * b j m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      ∑ j ∈ Finset.Icc 1 Jb,
          lemma12Rows N Xd (calP A G j) (calQK A G M j) (calH H1 j) T
            (chiBarCoeff q χ a) (chiBarCoeff q χ (b j)) (chiBarCoeff q χ c)
        ≤ 480 * (T / (Xd : ℝ) + 1)
            * ((∑ j ∈ Finset.Icc 1 Jb,
                  ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                      * (Real.exp 1 / (Xd : ℝ) ^ 2))
                    + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                    + 1 / (Xd : ℝ)))
              + C * (2 / (M : ℝ))) := by
  obtain ⟨C, hC, hK2⟩ := sum_lemma12Rows_priced_calibratedK2
  refine ⟨C, hC, ?_⟩
  intro q _ χ A G M Jb N Xd H1 T a c b hA hG hM hXd hT hH1 hN4 hreg hbig hdom ha hb hc
    hasupp hwin
  exact hK2 A G M Jb N Xd H1 T (chiBarCoeff q χ a) (fun j => chiBarCoeff q χ (b j))
    (chiBarCoeff q χ c) hA hG hM hXd hT hH1 hN4 hreg hbig hdom
    (norm_chiBarCoeff_le_one χ ha) (chiBarCoeff_bfam_le_one χ hb)
    (chiBarCoeff_cseq_le_one χ hc) (chiBarCoeff_dyadic_supp χ hasupp)
    (chiBarCoeff_window q χ c b (calP A G) (calQK A G M) Jb Xd hwin)

/-! ## §7 — THE PER-`χ` SEAM ROW AS A NUMBER (the `𝒯`-leg fused with its price)

`TLegChi.TLeg_feeds_capstone_chi` composed with §6, at the K-calibrated family
`P_j = calP A G j`, `Q_j = calQK A G M j`, `H_j = calH H1 j`, `α = mrAlpha η` — i.e. the
`χ`-twin of `SeamNumber.seam_row_number`, and its proof is the same two-step `.trans`.

⟦THE CAPSTONE ROW IS CARRIED, exactly as at `q = 1`⟧  `TLeg_feeds_capstone_chi` takes the A3
row as a hypothesis because the `𝒯`-side gate family (`CalFrameK` + the `X_d`-side
reconciliation) and the `𝒰`-side gate family (the graded razor + the socket floor at `(q,T)`)
are reconciled at the STATION, not inside the leg.  §5 produces exactly this hypothesis; the
composition is the consumer's, and what the kernel certifies here is the shape fit and the
price.  (Same fence as `TLegExit`'s H-4 and `TLegChi` §3.)

⟦THE SIX RECONCILIATION GATES⟧ (R1) `log Q_Jb ≤ √(log X_d)`, (R2) `100 ≤ √(log X_d)`,
(R3) `N ≤ 4X_d`, (R4) the per-level error-domination product, (R5) `‖aₙ‖ ≤ 1`,
(R6) `aₙ ≠ 0 → X_d ≤ n ≤ 2X_d` — `SeamNumber`'s header states why each is `X_d`-side and
cannot be derived from the `X`-side frame.  They are character-FREE and ride verbatim. -/

set_option maxHeartbeats 1000000 in
-- Same cause as `SeamNumber.seam_row_number` (the `q = 1` twin): the fuse elaborates the
-- leg's exit and the pricer's exit against one another, both at full ladder width.
/-- **THE PER-`χ` SEAM ROW AS A NUMBER** (`m4_rowChi_number_of_capstone`).  Given the A3
capstone row at the character `χ` (§5's conclusion, at the K-calibrated partition), the whole
right-hand side becomes a formula in the parameters — no integral, no coefficient sum:

  `∫_{Ann} ‖spoly N (χ̄a)‖² ≤ 8S² + [level-1 term] + 1536·Ct·e³·(2T_ann/X_d+240)/P₁`
  `                                 + 480·(T_ann/X_d+1)·(Σ_j rows + Cp·2/M)`
  `                              + 2·(T_ann/X + 1)·(log X)^{−θ₂₉₃+ε}`.

`Ct` and `Cp` are the `q = 1` universal constants (`TLegExit.TLeg_bound`'s and
`TypicalPriceK`'s): bound outside `q` and outside `χ`, hence character- and
modulus-uniform. -/
theorem m4_rowChi_number_of_capstone :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd A G M Jb : ℕ) (H1 X Tann t₁ S η ε : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        0 ≤ Tann → 2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        -- ⟦THE RAMARÉ DATUM, UNTWISTED⟧
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → a (p * m) = bfam j m * c p) →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          c p * bfam j m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        -- ⟦THE RECONCILIATION GATES (R1), (R2), (R4)⟧
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (∀ j ∈ Finset.Icc 1 Jb,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
                / Real.log ((calQK A G M j : ℕ) : ℝ))) →
        -- ⟦THE A3 CAPSTONE ROW, CARRIED⟧ (§5 supplies it)
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
                + 480 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + Cp * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Ct, hCt, hfeed⟩ := TLeg_feeds_capstone_chi
  obtain ⟨Cp, hCp, hprice⟩ := sum_lemma12Rows_priced_chi
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ χ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X Tann t₁ S η ε hF hT0 hNXd hN4 hcoef
    hwin hasupp hQXd hXdbig hdom hcap
  -- ⟦THE FRAME'S OWN READS⟧ everything the leg and the pricer need, from `CalFrameK`
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hη := hF.eta_pos
  have hη6 := hF.eta_lt
  have hJb1 := hF.one_le_Jb
  have hG1 := hF.one_le_G
  have hM1 := hF.one_le_M
  have hA1 : 1 ≤ A := le_trans (by norm_num) hF.A_floor
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hcalH1 : calH H1 1 = H1 := by simp [calH]
  have hH1two : (2 : ℝ) ≤ calH H1 1 := by rw [hcalH1]; exact hF.H1_two
  have hH10 : (0 : ℝ) < H1 := by linarith [hF.H1_two]
  have hP1nat : 1 ≤ calP A G 1 := by simp only [calP]; exact Nat.one_le_two_pow
  have hP1pos : (0 : ℝ) < ((calP A G 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((calP A G 1 : ℕ) : ℝ) := by exact_mod_cast hP1nat
    linarith
  have hQ1Xd : calQK A G M 1 ≤ Xd := le_trans (calQK_mono A hG1 hJb1) hF.Q_le_Xd
  have hbot1 : ∀ v ∈ ramI (calH H1 1) (calP A G 1) (calQK A G M 1),
      1 ≤ ramRbot (calH H1 1) Xd v :=
    fun v hv => ramRbot_one_le_of_mem_ramI (by linarith) (one_le_calQK A G M 1) hQ1Xd hv
  -- ⟦THE 𝒯-LEG AT THE TWISTED DATUM⟧
  have hleg := hfeed q hq0 χ c a bfam (calP A G) (calQK A G M) (calH H1) η Jb N Xd
    (calP A G 1) X Tann t₁ S ε hη hη6 hJb1 hXd1 hNXd hT0 hP1pos (levelGates_calibratedK hF)
    hH1two hP1nat (calP_le_calQK hM1 le_rfl) hbot1 hcoef hb1 hc1 hwin hcap
  -- ⟦THE PRICE OF `Σ_j lemma12Rows`, AT THE TWISTED DATUM⟧
  have hK2 := hprice q χ A G M Jb N Xd H1 Tann a c bfam hA1 hG1 hM1 hXd1 hT0 hH10 hN4
    (fun j hj => le_trans (Real.log_le_log (by
        have h : (0 : ℕ) < calQK A G M j :=
          lt_of_lt_of_le Nat.zero_lt_one (one_le_calQK A G M j)
        exact_mod_cast h)
      (by exact_mod_cast calQK_mono A hG1 (Finset.mem_Icc.mp hj).2)) hQXd)
    hXdbig hdom ha1 hb1 hc1 hasupp hwin
  exact hleg.trans
    (add_le_add (add_le_add le_rfl (add_le_add le_rfl hK2)) le_rfl)

/-! ## §8 — THE WEIGHTING: the `T`-family collapses to ONE number

The `hrowsSum` slot demands a constant `Mrow χ` UNIFORM over the whole height family
`X/h ≤ T`, `2T ≤ X` (`ThmA2ChiSummed`'s ⟦A1⟧: `Mrow` is a scalar per character, never a
function of `T`).  §7's row is `T`-linear in four places, and the weight `w = (X/h)/T` kills
every one of them at the four numerals of `ThmA2Rows` §1 — `9`, `244`, `3`, `3/2` — which are
CHARACTER-BLIND arithmetic.  Those helpers are `private` to `ThmA2Rows`, so the page is
re-derived here at its own names; no content is re-proved (the arithmetic is
`(X/h)/X_d ≤ 4/h` and `w ≤ 1`, twice each).

⟦THE LEVEL-1 TERM IS LEFT AT THE GENERAL LADDER⟧  `ThmA2Rows` weighs it against
`DoorFrameH1.level1_term_door_decays`, which is pinned to the DOOR family
(`A = Adoor M`, `G = 3072M`, `H₁ = H1door M`, `η = 1/12`).  This page is stated at a FREE
`(A, G, H₁, η)`, so the `9`-gate is applied to the `T`-carrying factor alone and the rest of
the term rides into `m4MrowChi` unchanged.  A consumer at the door family may then bound it by
`47520·a2Level1 M` with the landed decay lemma — that step is the door instance's, not this
page's. -/

/-- **THE FOUR NUMERALS** (`m4_weight_gates`) — `ThmA2Rows.a2_weight_gates` at its own name
(that one is `private`).  With `w := (X/h)/T`: `0 ≤ w ≤ 1`, and the four `T`-linear factors of
the seam row weigh in at `9`, `244`, `3`, `3/2`. -/
private lemma m4_weight_gates {X h T Xd Q1 : ℝ} (hh4 : 4 ≤ h) (hX0 : 0 < X)
    (hT : X / h ≤ T) (hXd : X ≤ 4 * Xd) (hQ1 : Q1 ≤ h) (hQ10 : 0 ≤ Q1) :
    0 ≤ X / h / T ∧ X / h / T ≤ 1 ∧
      X / h / T * (2 * T * Q1 / Xd + 1) ≤ 9 ∧
      X / h / T * (2 * (2 * T) / Xd + 240) ≤ 244 ∧
      X / h / T * (2 * T / Xd + 1) ≤ 3 ∧
      X / h / T * (2 * T / X + 1) ≤ 3 / 2 := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hu0 : (0 : ℝ) < X / h := div_pos hX0 hh0
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le hu0 hT
  have hXd0 : (0 : ℝ) < Xd := by linarith
  have hw0 : (0 : ℝ) ≤ X / h / T := le_of_lt (div_pos hu0 hT0)
  have hw1 : X / h / T ≤ 1 := (div_le_one hT0).mpr hT
  have hratio : X / h / Xd ≤ 4 / h := by
    rw [div_div, div_le_div_iff₀ (by positivity) hh0]
    nlinarith
  refine ⟨hw0, hw1, ?_, ?_, ?_, ?_⟩
  · have hid : X / h / T * (2 * T * Q1 / Xd + 1) = 2 * Q1 * (X / h / Xd) + X / h / T := by
      field_simp
    have hstep : 2 * Q1 * (X / h / Xd) ≤ 2 * Q1 * (4 / h) :=
      mul_le_mul_of_nonneg_left hratio (by linarith)
    have hval : 2 * Q1 * (4 / h) ≤ 8 := by
      rw [show 2 * Q1 * (4 / h) = 8 * Q1 / h by ring, div_le_iff₀ hh0]
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * (2 * T) / Xd + 240)
        = 4 * (X / h / Xd) + 240 * (X / h / T) := by field_simp; ring
    have hstep : 4 * (X / h / Xd) ≤ 4 * (4 / h) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    have hval : 4 * (4 / h) ≤ 4 := by
      rw [show 4 * (4 / h) = 16 / h by ring, div_le_iff₀ hh0]
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * T / Xd + 1) = 2 * (X / h / Xd) + X / h / T := by field_simp
    have hstep : 2 * (X / h / Xd) ≤ 2 * (4 / h) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    have hval : 2 * (4 / h) ≤ 2 := by
      rw [show 2 * (4 / h) = 8 / h by ring, div_le_iff₀ hh0]
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * T / X + 1) = 2 / h + X / h / T := by field_simp
    have h2 : 2 / h ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hh0 (by norm_num)]
      linarith
    rw [hid]; linarith

/-- The row's five summands weigh independently. -/
private lemma m4_row_weigh {w Sq A B C D s a b c d : ℝ}
    (hS : w * Sq ≤ s) (hA : w * A ≤ a) (hB : w * B ≤ b) (hC : w * C ≤ c) (hD : w * D ≤ d) :
    w * (Sq + (A + B + C) + D) ≤ s + (a + b + c) + d := by
  have h : w * (Sq + (A + B + C) + D) = w * Sq + (w * A + w * B + w * C) + w * D := by ring
  rw [h]; linarith

/-- The level-1 summand: the weight meets the `T`-carrying factor at the `9`-gate; the rest of
the term is `T`-free and rides through. -/
private lemma m4_level1_weigh {w Hq Lq R Pq Br : ℝ}
    (hHL : 0 ≤ 2 * (Hq * Lq + 1)) (hPq : 0 ≤ Pq) (hBr : 0 ≤ Br) (hR9 : w * R ≤ 9) :
    w * (2 * (Hq * Lq + 1) * R * Pq * Br) ≤ 18 * (Hq * Lq + 1) * Pq * Br := by
  have hid : w * (2 * (Hq * Lq + 1) * R * Pq * Br)
      = (2 * (Hq * Lq + 1) * Pq * Br) * (w * R) := by ring
  have h0 : (0 : ℝ) ≤ 2 * (Hq * Lq + 1) * Pq * Br := by positivity
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_left hR9 h0]

/-- The `Ct`-summand, at the `244`-gate: `1536·244 = 374784`. -/
private lemma m4_term2_weigh {w Ct R Y : ℝ} (hCt : 0 ≤ Ct) (hY : 0 ≤ Y) (hR : w * R ≤ 244) :
    w * (1536 * Ct * Real.exp 3 * R * Y) ≤ 374784 * Ct * Real.exp 3 * Y := by
  have hid : w * (1536 * Ct * Real.exp 3 * R * Y)
      = 1536 * Ct * Real.exp 3 * Y * (w * R) := by ring
  have h0 : (0 : ℝ) ≤ 1536 * Ct * Real.exp 3 * Y := by positivity
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR h0]

/-- The Lemma-12 summand, at the `3`-gate: `480·3 = 1440`. -/
private lemma m4_term3_weigh {w R Z : ℝ} (hZ : 0 ≤ Z) (hR : w * R ≤ 3) :
    w * (480 * R * Z) ≤ 1440 * Z := by
  have hid : w * (480 * R * Z) = 480 * Z * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 480) hZ)]

/-- The `𝒰`-leg summand, at the `3/2`-gate: `2·(3/2) = 3`. -/
private lemma m4_term4_weigh {w R Z : ℝ} (hZ : 0 ≤ Z) (hR : w * R ≤ 3 / 2) :
    w * (2 * (R * Z)) ≤ 3 * Z := by
  have hid : w * (2 * (R * Z)) = 2 * Z * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (by linarith : (0 : ℝ) ≤ 2 * Z)]

/-- The ball leg passes the weighting untouched (`w ≤ 1`). -/
private lemma m4_ball_weigh {w S : ℝ} (hw1 : w ≤ 1) :
    w * (8 * S ^ 2) ≤ 8 * S ^ 2 := by nlinarith [sq_nonneg S]

/-- **THE PER-`χ` ROW NUMBER** (`m4MrowChi`).  The `T`-FREE bound the weighted seam row obeys
uniformly over the family `X/h ≤ T`, `2T ≤ X` — the value the `hrowsSum` slot's `Mrow χ`
takes.  Five summands: the carried ball leg `8S²`, the level-1 term at the `9`-gate, the
`Ct`-row at the `244`-gate, the Lemma-12 rows at the `3`-gate (`480·3 = 1440`), and the
`𝒰`-leg at the `3/2`-gate. -/
def m4MrowChi (Ct Cp : ℝ) (A G M Jb Xd : ℕ) (H1 η X ε S : ℝ) : ℝ :=
  8 * S ^ 2
    + (18 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
          * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
          * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
              + 60 * (calH H1 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / calH H1 1))
        + 374784 * Ct * Real.exp 3 * (1 / ((calP A G 1 : ℕ) : ℝ))
        + 1440 * ((∑ j ∈ Finset.Icc 1 Jb,
              ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                  * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                + 1 / (Xd : ℝ)))
            + Cp * (2 / (M : ℝ))))
    + 3 * (Real.log X) ^ (-theta293 + ε)

/-- The Lemma-12 row sum is a sum of nonnegative terms (`1 ≤ X_d`, `2 ≤ H₁`, `1 ≤ P_j`) —
`ThmA2Rows.a2RowsSum_nonneg` at the free ladder. -/
private lemma m4_rowsSum_nonneg {A G Jb Xd : ℕ} {H1 : ℝ} (hXd : 1 ≤ Xd) (hH1 : 2 ≤ H1) :
    (0 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 Jb,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
        + 1 / (Xd : ℝ)) := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have hcalH : (0 : ℝ) < calH H1 j := by rw [calH]; nlinarith
  have hP1 : (1 : ℝ) ≤ ((calP A G j : ℕ) : ℝ) := by
    have h : 1 ≤ calP A G j := by simp only [calP]; exact Nat.one_le_two_pow
    exact_mod_cast h
  have hlogb : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have h1 : (0 : ℝ) ≤ (Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
      * (Real.exp 1 / (Xd : ℝ) ^ 2)) := by
    have hq : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH H1 j :=
      div_nonneg (by positivity) hcalH.le
    have hr : (0 : ℝ) ≤ Real.exp 1 / (Xd : ℝ) ^ 2 := by positivity
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1) hr
    nlinarith
  have h2 : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ) :=
    div_nonneg (by linarith) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 / (Xd : ℝ) := by positivity
  linarith

set_option maxHeartbeats 400000 in
-- The `hrow` hypothesis is the full number-row; matching it summand by summand against
-- `m4MrowChi` costs more than the default budget in elaboration alone.
/-- **THE WEIGHTED ROW** (`m4_rowChi_weighed`).  §7's number-row at `T_ann = 2T`, weighted by
`(X/h)/T`, lands inside the `T`-FREE constant `m4MrowChi` — the `hrowsSum` slot's shape. -/
theorem m4_rowChi_weighed {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {a : ℕ → ℂ}
    {N Xd A G M Jb : ℕ} {H1 X h S η ε Ct Cp T : ℝ}
    (hXd1 : 1 ≤ Xd) (hH1 : 2 ≤ H1) (hη : 0 < η) (hη6 : η < 1 / 6)
    (hCt : 0 ≤ Ct) (hCp : 0 ≤ Cp) (hM1 : 1 ≤ M)
    (hh4 : 4 ≤ h) (hX0 : 0 < X) (hL0 : 0 ≤ Real.log X) (hX4Xd : X ≤ 4 * (Xd : ℝ))
    (hQ1h : ((calQK A G M 1 : ℕ) : ℝ) ≤ h)
    (hT : X / h ≤ T)
    (hrow : (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
      ≤ 8 * S ^ 2
        + (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
              * (2 * T * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
              * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
              * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                    * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                  + 60 * (calH H1 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / calH H1 1))
            + 1536 * Ct * Real.exp 3 * (2 * (2 * T) / (Xd : ℝ) + 240)
                * (1 / ((calP A G 1 : ℕ) : ℝ))
            + 480 * (2 * T / (Xd : ℝ) + 1)
                * ((∑ j ∈ Finset.Icc 1 Jb,
                      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                          * (Real.exp 1 / (Xd : ℝ) ^ 2))
                        + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                        + 1 / (Xd : ℝ)))
                  + Cp * (2 / (M : ℝ))))
        + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) :
    X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
      ≤ m4MrowChi Ct Cp A G M Jb Xd H1 η X ε S := by
  have hQ10 : (0 : ℝ) ≤ ((calQK A G M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨hw0, hw1, hg9, hg244, hg3, hg32⟩ :=
    m4_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK A G M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hrow hw0).trans ?_
  -- ⟦the level-1 term's `T`-free factors⟧
  have hcalH1 : calH H1 1 = H1 := by simp [calH]
  have hH1pos : (0 : ℝ) < calH H1 1 := by rw [hcalH1]; linarith
  have hα1 : 0 < mrAlpha η 1 := mrAlpha_pos η hη hη6 le_rfl
  have hα1' : mrAlpha η 1 ≤ 1 / 4 := by rw [mrAlpha]; nlinarith
  have hHL0 : (0 : ℝ) ≤ 2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1) := by
    have hQlog : (0 : ℝ) ≤ Real.log ((calQK A G M 1 : ℕ) : ℝ) := by
      have h : (1 : ℝ) ≤ ((calQK A G M 1 : ℕ) : ℝ) := by
        exact_mod_cast one_le_calQK A G M 1
      exact Real.log_nonneg h
    nlinarith
  have hPq0 : (0 : ℝ) ≤ ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hBr0 : (0 : ℝ) ≤ 4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
      * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
    + 60 * (calH H1 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / calH H1 1) := by
    have h1 : (0 : ℝ) < 1 - 2 * mrAlpha η 1 := by linarith
    have h2 : (0 : ℝ) ≤ calH H1 1 / (1 - 2 * mrAlpha η 1) := by positivity
    have h3 : (0 : ℝ) ≤ calH H1 1 / mrAlpha η 1 := by positivity
    have e1 : (0 : ℝ) < Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1) := Real.exp_pos _
    have e2 : (0 : ℝ) < Real.exp (4 * mrAlpha η 1 / calH H1 1) := Real.exp_pos _
    nlinarith
  have hY0 : (0 : ℝ) ≤ 1 / ((calP A G 1 : ℕ) : ℝ) := by positivity
  have hRS0 : (0 : ℝ) ≤ (∑ j ∈ Finset.Icc 1 Jb,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
        + 1 / (Xd : ℝ))) + Cp * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
    have h2 : (0 : ℝ) ≤ Cp * (2 / (M : ℝ)) := by positivity
    linarith [m4_rowsSum_nonneg (A := A) (G := G) (Jb := Jb) (Xd := Xd) (H1 := H1) hXd1 hH1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) := Real.rpow_nonneg hL0 _
  unfold m4MrowChi
  exact m4_row_weigh (m4_ball_weigh hw1)
    (m4_level1_weigh hHL0 hPq0 hBr0 hg9)
    (m4_term2_weigh hCt hY0 hg244) (m4_term3_weigh hRS0 hg3) (m4_term4_weigh hZ0 hg32)

/-! ## §9 — THE DELIVERABLE: the `hrowsSum` slot, per character

§7 at `T_ann = 2T` composed with §8, quantified over the height family.  The statement's
shape is `ThmA2ChiSummed.thm_a2_spine_chiSummed`'s `hrowsSum` binder BYTE FOR BYTE
(`∀ χ, ∀ T, X/h ≤ T → 2T ≤ X → TannGate X (2T) → 5 ≤ loglog(2T) → …`), at the datum
`a χ := chiBarCoeff q χ a` and the row constant `Mrow χ := m4MrowChi … (S χ)`.

⟦THE ONE CARRIED FAMILY⟧  The A3 capstone row is carried as a `∀ χ, ∀ T` hypothesis and §5
(`m4_rowChi_capstone`) is its supplier: instantiate §5 at `T_ann := 2T`, `Pseq := calP A G`,
`Qseq := calQK A G M`, `Hseq := calH H1`, `αseq := mrAlpha η`, `J := Jb`.  §5's own binder
list — the graded razor's gates at `(q, 2T)`, the socket floor `T₀ ≤ 2T` with G1–G4, the
`Rbd` binder, the `𝒯_S` budget `KS`, Lemma 12's `χ`-summed error row, and the carried ball
binder `hSup` — is stated there and NOT repeated here; what this page adds is the `𝒯`-side
frame, its price, and the weighting.  The two gate families meet at the station, which is
where the corpus has always reconciled them (`TLegExit` H-4, `TLegChi` §3, §7 above). -/

/-- **⟦THE D2 DELIVERABLE⟧ THE PER-`χ` ROW FAMILY** (`m4_hrowsSum_chi`).  For every character
and every height in the seam family,

  `(X/h)/T · ∫_{Ann(X,2T)} ‖spoly N (χ̄a) t‖² ≤ m4MrowChi Ct Cp A G M Jb X_d H₁ η X ε (S χ)`,

the `hrowsSum` slot of `thm_a2_spine_chiSummed` / `thm_a2'_of_rows_chiSummed`.

⟦THE RESIDUE, ENUMERATED⟧ (the PORT-AUDIT law: no under-counted list)
1. **the carried A3 capstone family** `hcap` — supplied by §5 at `T_ann = 2T`, whose own
   residue is §5's docstring: the graded razor's gates at `(q, 2T)`, the per-`(q,T)` socket
   floor `T₀ ≤ 2T` + G1–G4, the co-factor binder `Rbd` with its grade (supplier landed in
   `RbdSupply`), the `𝒯_S` budget `KS` with its gate, Lemma 12's `χ`-summed error row `E`,
   and the **carried ball binder** `hSup` at the per-`χ` centre `t₁ χ` and sup `S χ`
   (supplier: the BALL-SUP leg; vacuous at `t₁ ≡ 0`, `S ≡ 0` by
   `CapFreeArm.ball_leg_vacuous_at_zero`);
2. **the `𝒯`-side frame** — `CalFrameK η H₁ A G M Jb X_d`, the Ramaré factorization of `a`
   with its two `1`-bounds and its dyadic window, and `2X_d ≤ N`;
3. **the six reconciliation gates** (R1)–(R6) of `SeamNumber`, character-free;
4. **the weighting frame** — `4 ≤ h`, `0 < X`, `0 ≤ log X`, `X ≤ 4X_d`, `Q₁ ≤ h`.

`Ct`, `Cp` are the `q = 1` universal constants: character- and modulus-uniform.  Because they
are, `Mrow` is character-uniform up to `S χ`, so the spine's `Σ_χ Mrow χ` costs one `φ(q)` on
everything but the ball leg — C2-SCOPE's finding K-2, paid in the open. -/
theorem m4_hrowsSum_chi :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd A G M Jb : ℕ) (H1 X h η ε : ℝ)
        (t₁ S : DirichletCharacter ℂ q → ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → a (p * m) = bfam j m * c p) →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          c p * bfam j m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (∀ j ∈ Finset.Icc 1 Jb,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
                / Real.log ((calQK A G M j : ℕ) : ℝ))) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK A G M 1 : ℕ) : ℝ) ≤ h →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ (`m4_rowChi_capstone` supplies it, height by height)
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
            ≤ m4MrowChi Ct Cp A G M Jb Xd H1 η X ε (S χ) := by
  obtain ⟨Ct, Cp, hCt, hCp, hnum⟩ := m4_rowChi_number_of_capstone
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X h η ε t₁ S hF hNXd hN4 hcoef hwin
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hrow := hnum q χ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X (2 * T) (t₁ χ) (S χ) η ε
    hF (by linarith) hNXd hN4 hcoef hwin hasupp hQXd hXdbig hdom
    (hcap χ T hT hTX2 hTgate hTll)
  exact m4_rowChi_weighed hXd1 hF.H1_two hF.eta_pos hF.eta_lt hCt.le hCp.le hF.one_le_M
    hh4 hX0 hL0 hX4Xd hQ1h hT hrow

/-! ## §10 — THE SLOT, DISCHARGED: `thm_a2_spine_chiSummed` at the `χ`-row family

**The compile is the certificate** that §9 byte-fits the frozen `hrowsSum` binder: the datum
`a χ := chiBarCoeff q χ a`, the height quantification, the four gates and the direction of the
inequality are `ThmA2ChiSummed`'s, verbatim.  Nothing about the slot is restated or relaxed;
this theorem is `thm_a2_spine_chiSummed` with its row slot supplied. -/

set_option maxHeartbeats 400000 in
-- The spine's own statement is large (the five-summand right-hand side plus the `T`-family
-- row slot); instantiating it at the `χ̄`-twisted datum family exceeds the default budget.
/-- **THE `Σ_χ` COMPOSITION SPINE AT THE `χ`-ROW FAMILY** (`m4_a2_spine_of_rowsChi`).
`ThmA2ChiSummed.thm_a2_spine_chiSummed` with `Mrow χ := m4MrowChi … (S χ)` supplied by §9. -/
theorem m4_a2_spine_of_rowsChi :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd A G M Jb K : ℕ) (H1 X h δ η ε : ℝ)
        (t₁ S B₀ : DirichletCharacter ℂ q → ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → a (p * m) = bfam j m * c p) →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          c p * bfam j m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (∀ j ∈ Finset.Icc 1 Jb,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
                / Real.log ((calQK A G M j : ℕ) : ℝ))) →
        4 ≤ h → X ≤ 4 * (Xd : ℝ) → ((calQK A G M 1 : ℕ) : ℝ) ≤ h →
        -- ⟦THE SPINE'S OWN FRAME⟧ (character-blind, `ThmA2ChiSummed`'s verbatim)
        Real.exp 1 ≤ X → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) → 0 < δ → δ ≤ 1 →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) → (N : ℝ) ≤ 2 * X →
        TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
        (∀ χ : DirichletCharacter ℂ q,
          (∫ t in (-(seamT0 X))..(seamT0 X),
            ‖dpolyA (chiBarCoeff q χ a) (seamS0 N X) t‖ ^ 2) ≤ B₀ χ) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ (`m4_rowChi_capstone` supplies it)
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * S χ ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1)
                      (mrAlpha η) Jb,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∑ χ : DirichletCharacter ℂ q,
            1 / X * (∫ x in X..(2 * X),
              ‖((1 / h : ℝ) : ℂ) * shortSum (chiBarCoeff q χ a) (seamS0 N X) x h‖ ^ 2)
          ≤ 1 / (2 * Real.pi ^ 2)
              * (236365 * Real.pi
                    * (∑ χ : DirichletCharacter ℂ q,
                        m4MrowChi Ct Cp A G M Jb Xd H1 η X ε (S χ))
                + 205 * Real.pi * (∑ χ : DirichletCharacter ℂ q, B₀ χ)
                + (q.totient : ℝ)
                    * (39674880 * Real.pi / h
                      + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
                        + 1152 * (12 * h / (2 ^ K * δ)
                            + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2))) := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd A G M Jb K H1 X h δ η ε t₁ S B₀ hF hNXd hN4 hcoef hwin
    hasupp hQXd hXdbig hdom hh4 hX4Xd hQ1h hX hhX hδ0 hδ1 hsupp hN2 hTann hceil hT0band hcap
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL0 : (0 : ℝ) ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hX
    rw [Real.log_exp] at h
    linarith
  exact thm_a2_spine_chiSummed (a := fun χ => chiBarCoeff q χ a)
    (Mrow := fun χ => m4MrowChi Ct Cp A G M Jb Xd H1 η X ε (S χ)) (B₀ := B₀) K hX hh4 hhX
    hδ0 hδ1 (fun χ => norm_chiBarCoeff_le_one χ ha1)
    (fun χ => chiBarCoeff_seam_supp χ hsupp) hN2 hTann hceil
    (hrows q c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X h η ε t₁ S hF hNXd hN4 hcoef hwin
      hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap)
    hT0band

/-! ## §11 — THE DOOR INSTANCE: `m4MrowChi` INSIDE `a2Mrow`

`ThmA2.a2Mrow` is the FROZEN five-summand interface's row constant, and
`thm_a2'_of_rows_chiSummed` pins its `hrowsSum` slot to it.  At the door family
(`A = Adoor M`, `G = 3072M`, `Jb = 2`, `H₁ = H1door M`, `η = 1/12`) and the vacuous ball
(`t₁ ≡ 0`, `S ≡ 0` — `CapFreeArm.ball_leg_vacuous_at_zero`, the `q = 1` arm's own choice),
`m4MrowChi` sits inside `a2Mrow` summand by summand:

* the level-1 term at `R = 9` is `DoorFrameH1.level1_term_door_decays`' `5280·9 = 47520`;
* the `Ct`-row is `a2Mrow`'s second summand VERBATIM;
* the Lemma-12 rows are `a2RowsSum M X_d` definitionally (the `j`-sum at `Jb = 2` and the door
  sequences), weighed at `1440` against `a2Mrow`'s `5760` — ⟦AMENDMENT G⟧'s `×4` cover, spent
  nowhere here;
* the `𝒰`-leg summand is `a2Mrow`'s fourth VERBATIM.

So the D2 row family feeds the frozen interface as well as the composition spine. -/

/-- **THE DOOR BRIDGE** (`m4MrowChi_le_a2Mrow`).  At the door family and the vacuous ball,
the per-`χ` row number sits inside the frozen interface's `a2Mrow`. -/
theorem m4MrowChi_le_a2Mrow {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) {Ct Cp X ε : ℝ}
    (hCp : 0 ≤ Cp) :
    m4MrowChi Ct Cp (Adoor M) (3072 * M) M 2 Xd (H1door M) (1 / 12) X ε 0
      ≤ a2Mrow Ct Cp M Xd X ε := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlvl := level1_term_door_decays (M := M) hM (R := 9) (by norm_num)
  have hRS0 : (0 : ℝ) ≤ (∑ j ∈ Finset.Icc 1 2,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1door M) j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 16 * Real.logb 2 (2 * (Xd : ℝ))
            / ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
        + 1 / (Xd : ℝ))) + Cp * (2 / (M : ℝ)) := by
    have h2 : (0 : ℝ) ≤ Cp * (2 / (M : ℝ)) := by positivity
    linarith [m4_rowsSum_nonneg (A := Adoor M) (G := 3072 * M) (Jb := 2) (Xd := Xd)
      (H1 := H1door M) hXd (H1door_two hM)]
  unfold m4MrowChi a2Mrow a2Level1 a2RowsSum
  have hlvl' : 18 * (calH (H1door M) 1
        * Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) + 1)
      * ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
      * (4 * (calH (H1door M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
            * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1door M) 1)
          + 60 * (calH (H1door M) 1 / mrAlpha (1 / 12 : ℝ) 1)
              * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1door M) 1))
      ≤ 47520 * ((Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
          / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by
    calc 18 * (calH (H1door M) 1
            * Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) + 1)
          * ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
          * (4 * (calH (H1door M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
                * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1door M) 1)
              + 60 * (calH (H1door M) 1 / mrAlpha (1 / 12 : ℝ) 1)
                  * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1door M) 1))
        = 2 * (calH (H1door M) 1
              * Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) + 1) * 9
            * ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
            * (4 * (calH (H1door M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
                  * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1door M) 1)
                + 60 * (calH (H1door M) 1 / mrAlpha (1 / 12 : ℝ) 1)
                    * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1door M) 1)) := by ring
      _ ≤ 5280 * 9 * ((Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
            / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := hlvl
      _ = 47520 * ((Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
            / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by ring
  linarith

/-- **⟦THE D2 DELIVERABLE AT THE DOOR⟧ THE `a2Mrow`-GENRE ROW FAMILY**
(`m4_hrowsSum_chi_door`).  §9 at the door family and the vacuous ball, landed inside the
FROZEN interface's row constant: this is `thm_a2'_of_rows_chiSummed`'s `hrowsSum` slot at the
constant families `Cs χ := Ct`, `Ccc χ := Cp`, `ε χ := ε`.

The frame `CalFrameK (1/12) (H1door M) (Adoor M) (3072M) M 2 X_d` is the LANDED
`ThmA2.calFrameK_doorH1_at`, so only `1 ≤ M` and the cutoff `Q₂ ≤ X_d` are asked for. -/
theorem m4_hrowsSum_chi_door :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
          p ≤ calQK (Adoor M) (3072 * M) M j → ¬ p ∣ m → a (p * m) = bfam j m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
          p ≤ calQK (Adoor M) (3072 * M) M j → c p * bfam j m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
                    (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ))) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (Adoor M) (3072 * M))
                      (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ a2Mrow Ct Cp M Xd X ε := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoef hwin hasupp hQXd
    hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (3072 * M) M 2) hXdQ
  refine (hrows q c a bfam ha1 hb1 hc1 N Xd (Adoor M) (3072 * M) M 2 (H1door M) X h
    (1 / 12) ε t₁ (fun _ => 0) (calFrameK_doorH1_at M Xd hM hXdQ) hNXd hN4 hcoef hwin
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChi_le_a2Mrow hM hXd1 hCp.le

/-! ## §9 — ⟦KNOT-1 ARITY SURGERY⟧ the capstone chain at the PER-BLOCK co-factor length

`USetGChiTS` §5's per-block composes, carried through §2, §3 and §5 to the capstone.  The ONE
binder that moves is the graded `hbudget`, from a single statement to `∀ j ∈ ramI H P Q`; `hM`
and every `Σ_j` were per-block already.  **The capstone's CONCLUSION is `M`-free**, so this
whole section changes nothing downstream except the hypothesis list.

⟦THE ROOT (KNOT1-SCOPE, flags 2026-07-30)⟧ a scalar range cap serving all blocks forces
`Q ≤ 2P` — the ram-block band collapses to a point — directly out of `range`@bottom against
`Mr_sharp`@top.  At the family the two are read at the same `j` and the forcing evaporates.

**PURELY ADDITIVE.**  §2/§3/§5 stand; these are twins beside them. -/

/-- **⟦ii-8b, PER-BLOCK⟧ THE BLOCK-SUM ADAPTER at the co-factor length family.**
`usetGChi_block_price` with the scalar `M` replaced by `Ms : ℕ → ℕ`.  The RIGHT-hand side is
unchanged (it is `M`-free); only the `Σ_j` being priced moves. -/
lemma usetGChi_block_price_perBlock (H : ℝ) (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (b : ℕ → ℂ)
    (X Tann KS Cs Rbd : ℝ)
    (hCs : 0 ≤ Cs) (hRbd : 0 ≤ Rbd) (hj₀ : 2 ≤ ⌊H * Real.log (P : ℝ)⌋₊)
    (hKS : ∀ j ∈ ramI H P Q,
      5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
          * (∑ m ∈ Finset.Icc 1 (Ms j),
              ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) ≤ KS) :
    (∑ j ∈ ramI H P Q,
        (5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
            * (∑ m ∈ Finset.Icc 1 (Ms j),
                ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
          + 81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2))
      ≤ ((ramI H P Q).card : ℝ) * KS
        + 54 * (3 * Cs / 2) * Rbd ^ 2 * H ^ 2 / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1) :=
  block_sum_bound H P Q _ _ KS (3 * Cs / 2) Rbd hKS (by linarith)
    (fun j _ => tL_block_weight_chi Cs H Rbd j hCs hRbd) hj₀

set_option maxHeartbeats 800000 in
-- Same cause as §3.
/-- **THE GRADED `𝒰`-LEG, PER CHARACTER, PER-BLOCK** (`usetGChi_row_exit_perChi_perBlock`).
`usetGChi_row_exit_perChi` at the co-factor length family `Ms : ℕ → ℕ`.  The conclusion is
byte-identical to the landed one (it is `M`-free); the hypothesis list differs in exactly two
places — `hM` and `hKS` read `Ms j`, and `hbudget` is now per-block. -/
theorem usetGChi_row_exit_perChi_perBlock :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (Tann VJ V L X : ℝ), 1 ≤ Tann → 1 < (q : ℝ) * Tann →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann →
        30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * Tann)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → Tann ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        T₀ ≤ Tann →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * Tann + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * Tann) → Real.log ((q : ℝ) * Tann) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ),
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q,
          thinBundleGChi ((q : ℝ) * Tann) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, H ≤ (j : ℝ)) →
        (∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * Tann) →
        (∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * Tann) / Real.log (ramQbase H P j)) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ Tann ^ 10) →
        (∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L) →
        (∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase H P j)) ^ 2) →
      ∀ Rbd : ℝ, 0 ≤ Rbd →
      ∀ t₁ : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ j ∈ ramI H P Q,
          ∀ t ∈ seamAnn X Tann \ seamBall X (t₁ χ),
            ‖ramR H N Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd) →
      ∀ E : ℝ, (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
          ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
      ∀ KS : ℝ,
        (∀ j ∈ ramI H P Q,
          5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
              * (∑ m ∈ Finset.Icc 1 (Ms j),
                  ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
            ≤ KS) →
        2 ≤ ⌊H * Real.log (P : ℝ)⌋₊ →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (seamAnn X Tann \ seamBall X (t₁ χ))
            ∩ UsetG (chiBarCoeff q χ c) Pseq Qseq Hseq αseq J,
            ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (((ramI H P Q).card : ℝ) * KS
                  + 54 * Cq * Rbd ^ 2 * H ^ 2
                      / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E := by
  obtain ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hT₀, hKq, hKs, hfam⟩ :=
    usetGChi_window_meansq_gated_family_perBlock
  refine ⟨3 * Cs / 2, cs, T₀, Kq, Ks, by linarith, hcs, hT₀, hKq, hKs, ?_⟩
  intro q _ c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X hT1 hqT hP3
    hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL
    hgate Rbd hRbd t₁ hR E herr KS hKS hj₀ χ
  -- ⟦the Σ_χ exit at the row's own pair set⟧
  have hsum := hfam q c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X
    hT1 hqT hP3 hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T
    hG1 hG2 hG3 hG4 hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3
    hBT hκ30 hBT10 hWL hgate Rbd hRbd
    (rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁)
    (measurableSet_rowPairSetG_fibre q c Pseq Qseq Hseq αseq J X Tann t₁)
    (rowPairSetG_sub q c Pseq Qseq Hseq αseq J X Tann t₁)
    (rowPairSetG_subset_UsetGChi q c Pseq Qseq Hseq αseq J X Tann t₁)
    (fun j hj r hr => hR r.1 j hj r.2 hr.1) E herr
  -- ⟦the per-χ read: every fibre integral is nonnegative, so one is at most the sum⟧
  have hnn : ∀ χ' ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      (0 : ℝ) ≤ ∫ t in {t : ℝ | (χ', t) ∈ rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁},
        ‖spoly N (chiBarCoeff q χ' a) t‖ ^ 2 := by
    intro χ' _
    exact setIntegral_nonneg
      (measurableSet_rowPairSetG_fibre q c Pseq Qseq Hseq αseq J X Tann t₁ χ')
      (fun _ _ => by positivity)
  have hsingle := Finset.single_le_sum hnn (Finset.mem_univ χ)
  -- ⟦the ⟦ii-8⟧ block price, per block⟧
  have hprice := usetGChi_block_price_perBlock H N Xd P Q Ms b X Tann KS Cs Rbd hCs.le hRbd
    hj₀ hKS
  have hcard0 : (0 : ℝ) ≤ 4 * ((ramI H P Q).card : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hprice hcard0
  rw [rowPairSetG_fibre] at hsingle
  linarith

set_option maxHeartbeats 1000000 in
-- Same cause as §5.
/-- **THE PER-`χ` CAPSTONE ROW, PER-BLOCK** (`m4_rowChi_capstone_perBlock`).
`m4_rowChi_capstone` at the co-factor length family `Ms : ℕ → ℕ`.  The CONCLUSION is
byte-identical to the landed capstone's; the hypothesis list moves in exactly three places —
the range containment `hM`, the `𝒯_S` budget binder `hKS` (both already `∀ j`, now reading
`Ms j`) and the graded `hbudget`, which becomes `∀ j ∈ ramI (H₈₃ X θ₂₉₃) P Q`.

⟦IRON RULE 1⟧ this is an ADDITIVE twin: `m4_rowChi_capstone` is untouched and remains the
`Ms ≡ const` special case. -/
theorem m4_rowChi_capstone_perBlock :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (Tann VJ V L X : ℝ), 1 ≤ Tann → 1 < (q : ℝ) * Tann →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann →
        30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * Tann)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → Tann ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        T₀ ≤ Tann →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * Tann + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * Tann) → Real.log ((q : ℝ) * Tann) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
        -- ⟦THE `X`-SIDE FRAME⟧
        2 ≤ H83 X theta293 → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann →
      ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleGChi ((q : ℝ) * Tann) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, H83 X theta293 ≤ (j : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 3 ≤ ramQbase (H83 X theta293) P j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          (ramQbase (H83 X theta293) P j : ℝ) ≤ (q : ℝ) * Tann) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          30 ≤ Real.log ((q : ℝ) * Tann) / Real.log (ramQbase (H83 X theta293) P j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          (ramQbase (H83 X theta293) P j : ℝ) ≤ Tann ^ 10) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          Real.log (ramQbase (H83 X theta293) P j) ≤ L) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase (H83 X theta293) P j)) ^ 2) →
      ∀ (Rbd CR : ℝ), 0 ≤ Rbd → Rbd ≤ CR * (Real.log X) ^ (-rho293) →
        1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
      ∀ t₁ : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ j ∈ ramI (H83 X theta293) P Q,
          ∀ t ∈ seamAnn X Tann \ seamBall X (t₁ χ),
            ‖ramR (H83 X theta293) N Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd) →
      ∀ KS : ℝ, 0 ≤ KS →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
              * (∑ m ∈ Finset.Icc 1 (Ms j),
                  ‖ramRcoeff (H83 X theta293) N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
            ≤ KS) →
        32 * (Real.log X) ^ (2 + 2 * theta293) * KS ≤ (Real.log X) ^ (-theta293) →
      ∀ (E EP2 εr : ℝ), 0 ≤ εr → 8640 ≤ (Real.log X) ^ εr →
        12 * EP2 ≤ (Real.log X) ^ (-theta293 + εr) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
          ‖ramErr (H83 X theta293) N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
      ∀ S : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann →
          |t - t₁ χ| ≤ seamRad X → ∀ m : ℕ, m ≤ N →
            ‖spolyA (chiBarCoeff q χ a) t m‖ ≤ S χ * m / (1 + |t - t₁ χ|)) →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 8 * S χ ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X (t₁ χ))
                ∩ seamTtotG (chiBarCoeff q χ c) Pseq Qseq Hseq αseq J,
                ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + εr)) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, hexit⟩ :=
    usetGChi_row_exit_perChi_perBlock
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, ?_⟩
  intro q _ c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X hT1 hqT hP3
    hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV hH2 hLXe hL4 hTgate
    N Xd P Q Ms a b cf hcf1 hPlow hQ0 hQhigh hM hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate
    Rbd CR hRbd hRgrade hCqgate t₁ hR KS hKS0 hKS hKSgate E EP2 εr hεr habs hEP2 hErow herr
    hXN hN2 hsupp S hSup χ
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hH0 : (0 : ℝ) ≤ H83 X theta293 := by linarith
  have hHeq : H83 X theta293 = (Real.log X) ^ theta293 := by rw [H83]
  have hTann0 : (0 : ℝ) ≤ Tann := by linarith
  have hfl := floor_pin X P hL4 hPlow
  -- ⟦the per-χ `𝒰` exit, per block⟧
  have hU := hexit q c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X
    hT1 hqT hP3 hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T
    hG1 hG2 hG3 hG4 hlogT1 hTL hLe hlogV (H83 X theta293) hH2 N Xd P Q Ms a b cf hcf1 hM
    hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate Rbd hRbd t₁ hR E herr KS hKS hfl.1 χ
  -- ⟦the block leg, priced at `θ₂₉₃`⟧
  have hmain := balance_priced_main X (H83 X theta293) Cq CR KS Rbd P Q hL0 hH0
    (ramI_card_le_pin X P Q hQ0 hQhigh hLXe) (le_of_eq hHeq) hfl.2
    hCq.le hKS0 hRbd hRgrade hKSgate hCqgate
  -- ⟦Lemma 12's error leg, absorbed⟧
  have hrem := rem_priced X Tann (H83 X theta293) εr EP2 E hL1 hX0 hTann0
    (le_of_eq hHeq.symm) habs hEP2 hErow
  -- ⟦the balance⟧
  have hbal := hUG_balance (chiBarCoeff q χ a) (chiBarCoeff q χ c) N Pseq Qseq Hseq αseq J
    X Tann (t₁ χ) εr _ _ hεr hL1 hX0 hTgate hU hmain hrem
  exact prop_A3_T1_row_split_weightedG (chiBarCoeff q χ a) N (chiBarCoeff q χ c) Pseq Qseq
    Hseq αseq J X Tann (t₁ χ) (S χ) _ hL0.le hTann0 hX0 hXN hN2
    (chiBarCoeff_seam_supp χ hsupp) (hSup χ) hbal

end Salt.MR
