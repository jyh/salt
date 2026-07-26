/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetGradedThin
import Salt.MR.RamRAdapter
import Salt.Tactic.DyadicRec

/-!
# TLegPreamble — the §8 preamble on the graded `𝒯ⱼ` (ROUTE G, stone G2)

`docs/exploration/hsup-design.md` ⟦V6⟧'s Route-G ladder, node `G2` — the OPENER of the
`𝒯`-leg, on top of `G0` (`Salt.MR.SeamGraded`), `G1a` (`Salt.MR.USetGradedThin`) and `G1b`
(`Salt.MR.USetGradedBalance`/`USetGradedPrice`).  Everything here is **parallel and
additive**: no landed statement is touched.

MR §8 opens by putting the three §8.1/§8.2 estimates on a common footing.  This file lands
that footing, in four independent stones.

## The stones

* **G2a — the pointwise (21) bound on `𝒯ⱼ`** (`blockSmallG_of_mem_TsetG`,
  `ramQ_le_of_blockSmallG`, `ramQ_sq_le_of_blockSmallG`,
  `exists_mem_ramI_ramQ_le_of_mem_TsetG`).  Definitional at the graded predicate: `G0`
  quantifies `BlockSmallG` over the block index set `ramI (Hseq j) (Pseq j) (Qseq j)`
  itself, so "`t ∈ 𝒯ⱼ` ⟹ `‖Q_{v,H_j}(1+it)‖ ≤ e^{−α_j v/H_j}` for every `v ∈ I_j`" is
  projection, not analysis.  (The flat family's `BlockSmallAt` quantified over *arbitrary*
  sub-ranges, so its consumer had to manufacture a block first — the trap is designed out
  at `G0`.)  The squared form is the one §8 actually uses.

* **G2b — Lemma 12 on `A_j`** (`lemma12_on_TsetG`, `lemma12_on_TsetG_blockSupport`).  The
  byte-plug of `USetThin.lemma12_meansq_on_subset(_blockSupport)` at the graded window
  parameters `(Hseq j, Pseq j, Qseq j)` and the set
  `A_j := (Ann ∖ ball) ∩ 𝒯ⱼ`.  The two binders that file asks of its subset —
  `MeasurableSet A` and `A ⊆ [−T,T]` — are supplied by `G0`'s
  `measurableSet_TsetG` and by `SeamSplit.seamAnn_subset_Icc` through the two
  intersections; nothing else moves.

* **G2c — the sharp-length co-factor MVT** (`cofactor_mvt_of_subset`, `cofactor_mvt_sharp`,
  `cofactor_mvt_mass_of_subset`, `cofactor_mvt_sharp_exit`,
  `cofactor_mvt_sharp_exit_visible`, `cofactor_mvt_dyadic_lossy`).  `ramR` is a `σ = 1`
  Dirichlet polynomial of length `M` for **any** `M` containing the co-factor range
  (`USetThinTS.ramR_eq_spoly`), so `MomentsA2.moment_core_bound` prices it at
  `(2T + 20M)·Σ_m ‖r_m‖²/m²`.  ⟦V4a⟧'s **SHARP-`M` LAW** says the `M` to use is
  `M ≍ 2X_v = 2·Xd·e^{−v/H}` (`RamRAdapter.ramRbot` /
  `ramRrange_subset_Icc_sharp`), *not* the dyadic `N ≍ 2Xd`.  Both instantiations are
  landed here so the loss is kernel-visible:

  * sharp (`2X_v ≤ Ms ≤ 3X_v`):  `∫ ≤ 4T·e^{v/H}/Xd + 120`;
  * dyadic (`M := N`):           `∫ ≤ 4T·e^{v/H}/Xd + 40·N·e^{v/H}/Xd`,

  and at the row's `N ≍ 2Xd` the second term is `80·e^{v/H}` — the `20N` term is lossy by
  **exactly the factor `e^{v/H}`** that the sharp instantiation keeps.  That factor is the
  co-factor mass MR (23) has to pay, which is why the sharp `M` is the whole point.

* **G2d — the two geometric `v`-sums** (`sum_exp_neg_graded`, `sum_exp_neg_graded_rate`,
  `sum_exp_neg_graded_card`, `sum_exp_growth`, `sum_exp_growth_top`).  `ramI H P Q` is a
  `Finset.Icc` of block indices and `e^{cv/H} = (e^{c/H})^v`, so both `v`-sums are plain
  geometric series in the house `Salt.Tactic.geom_sum_le_bot_Icc` / `geom_sum_le_top_Icc`
  form.  **Both exit shapes are stated, honestly:**

  * decaying leg (`c = −2α`, ratio `e^{−2α/H} < 1`, gated `0 < α`): the geometric bound
    `e^{−2α v₀/H}/(1 − e^{−2α/H})`, the `H/(2α)`-shape
    `(H/2α)·e^{−2α(v₀−1)/H}` (the ratio is near `1` when `α/H → 0`, so the
    `1/(1−r)` must be read as `≈ H/2α`, never as `O(1)`), and the crude `|I_J|`-times-top
    bound — the consumer takes the min;
  * growing leg (`c = 1 − 2α`, ratio `e^{(1−2α)/H} > 1`, gated `2α < 1` **in-statement**):
    the top-dominated `e^{(1−2α)(v₁+1)/H}/(e^{(1−2α)/H} − 1)` and its closed form
    `(H/(1−2α))·e^{(1−2α)/H}·Q^{1−2α}`.

## Conventions and pins (law #253, byte-checked)

* **No negation.**  `G1a`'s posture is kept: every `t` here is the ordinate the seam row
  integrates over.  `BlockSmallG` is stated in the `+it` convention and quoted through
  `ramQ`; no `dpoly`, no `Finset.image (−·)`, no `−𝒯` bridge appears in this file.
* **The half-open `ramQblock` fiber** (`e^{v/H} ≤ p < e^{(v+1)/H}`) is inherited through
  `ramQ` and never re-derived, exactly as at `G0`.
* **The empty-block vacuity** (`G0`'s structural trap): `BlockSmallG` is a bounded `∀` over
  `ramI`, vacuous when `ramI = ∅`.  `exists_mem_ramI_ramQ_le_of_mem_TsetG` carries the
  `G0`/`G1a` non-degeneracy pins `0 ≤ Hseq j`, `1 ≤ Pseq j`, `Pseq j ≤ Qseq j` and
  certifies that the graded bound on `𝒯ⱼ` has at least one block to bite on.
* Every growing quantity rides the statement: `T`, `N`, `Xd`, `Ms`, `ramRbot H Xd v`, the
  block count `(ramI …).card`, `H`, `α`.  Nothing is absorbed into a numeral.
* `0 < α` is a gate of the **decaying** leg only; the growing leg needs `2α < 1` and
  nothing else, so `0 < α` is not carried there (an unused gate is a false pin).

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 eq (21), §6 (Lemma 12), §8 pp. 27–29;
`docs/exploration/hsup-design.md` ⟦V4a⟧ (the sharp-`M` law) and ⟦V6⟧ (the Route-G ladder).
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §1 — G2a: the pointwise MR (21) bound on the graded `𝒯ⱼ` -/

/-- **`t ∈ 𝒯ⱼ` carries the graded smallness at `j`.**  Pure projection out of `G0`'s
`TsetG`; recorded so no consumer has to unfold the set-builder. -/
lemma blockSmallG_of_mem_TsetG {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ}
    {J j : ℕ} {t : ℝ} (ht : t ∈ TsetG f Pseq Qseq Hseq αseq J j) :
    BlockSmallG f Pseq Qseq Hseq αseq j t := ht.2.2.1

/-- **G2a — MR eq (21) on `𝒯ⱼ`.**  For `t ∈ TsetG … J j` and *every* block index
`v ∈ I_j = ramI (Hseq j) (Pseq j) (Qseq j)`,

  `‖Q_{v,H_j}(1+it)‖ ≤ exp(−α_j·v/H_j)`.

This is definitional at the graded predicate: `G0`'s `BlockSmallG` quantifies over `I_j`
itself, so there is no block to manufacture and no sub-range to refine (the flat
`BlockSmallAt` trap is designed out). -/
lemma ramQ_le_of_blockSmallG {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ}
    {J j : ℕ} {t : ℝ} (ht : t ∈ TsetG f Pseq Qseq Hseq αseq J j)
    {v : ℕ} (hv : v ∈ ramI (Hseq j) (Pseq j) (Qseq j)) :
    ‖ramQ (Hseq j) (Pseq j) (Qseq j) v f t‖ ≤ Real.exp (-(αseq j) * (v : ℝ) / Hseq j) :=
  blockSmallG_of_mem_TsetG ht v hv

/-- **G2a (squared) — the form §8 consumes.**  `‖Q_{v,H_j}(1+it)‖² ≤ exp(−2α_j·v/H_j)` on
`𝒯ⱼ`.  The exponent `2α_j` is exactly the one `G1a`'s thinness is calibrated to, and the
one `G2d`'s decaying `v`-sum runs at. -/
lemma ramQ_sq_le_of_blockSmallG {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ}
    {J j : ℕ} {t : ℝ} (ht : t ∈ TsetG f Pseq Qseq Hseq αseq J j)
    {v : ℕ} (hv : v ∈ ramI (Hseq j) (Pseq j) (Qseq j)) :
    ‖ramQ (Hseq j) (Pseq j) (Qseq j) v f t‖ ^ 2
      ≤ Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j) := by
  have hb := ramQ_le_of_blockSmallG ht hv
  have h0 : (0 : ℝ) ≤ ‖ramQ (Hseq j) (Pseq j) (Qseq j) v f t‖ := norm_nonneg _
  have hexp : Real.exp (-(αseq j) * (v : ℝ) / Hseq j) ^ 2
      = Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  calc ‖ramQ (Hseq j) (Pseq j) (Qseq j) v f t‖ ^ 2
      ≤ Real.exp (-(αseq j) * (v : ℝ) / Hseq j) ^ 2 := by nlinarith [hb, h0]
    _ = Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j) := hexp

/-- **G2a (non-degeneracy) — the graded bound on `𝒯ⱼ` is not vacuous.**  `G0` banked the
structural trap: an EMPTY `ramI` makes `BlockSmallG` vacuously true.  Under the `G0`/`G1a`
pins `0 ≤ H_j`, `1 ≤ P_j`, `P_j ≤ Q_j` the block index set is nonempty
(`USetGradedThin.ramI_nonempty`), so membership in `𝒯ⱼ` really does bound at least one
block polynomial. -/
lemma exists_mem_ramI_ramQ_le_of_mem_TsetG {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ}
    {Hseq αseq : ℕ → ℝ} {J j : ℕ} {t : ℝ}
    (hH : 0 ≤ Hseq j) (hP1 : 1 ≤ Pseq j) (hPQ : Pseq j ≤ Qseq j)
    (ht : t ∈ TsetG f Pseq Qseq Hseq αseq J j) :
    ∃ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
      ‖ramQ (Hseq j) (Pseq j) (Qseq j) v f t‖ ≤ Real.exp (-(αseq j) * (v : ℝ) / Hseq j) := by
  obtain ⟨v, hv⟩ := ramI_nonempty hH hP1 hPQ
  exact ⟨v, hv, ramQ_le_of_blockSmallG ht hv⟩

/-! ## §2 — G2b: Lemma 12 on `A_j = (Ann ∖ ball) ∩ 𝒯ⱼ` -/

/-- The §8 window `A_j := (Ann ∖ ball) ∩ 𝒯ⱼ` is measurable (`G0`'s
`measurableSet_TsetG` against the landed seam sets). -/
lemma measurableSet_annulus_TsetG (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
    (Jb j : ℕ) (X T t₁ : ℝ) :
    MeasurableSet ((seamAnn X T \ seamBall X t₁) ∩ TsetG fb Pseq Qseq Hseq αseq Jb j) :=
  ((measurableSet_seamAnn X T).diff (measurableSet_seamBall X t₁)).inter
    (measurableSet_TsetG fb Pseq Qseq Hseq αseq Jb j)

/-- `A_j ⊆ [−T,T]` — the subset transport Lemma 12's set-restricted row asks for, through
the two intersections. -/
lemma annulus_TsetG_subset_Icc (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
    (Jb j : ℕ) (X T t₁ : ℝ) :
    (seamAnn X T \ seamBall X t₁) ∩ TsetG fb Pseq Qseq Hseq αseq Jb j ⊆ Set.Icc (-T) T :=
  fun _ ht => seamAnn_subset_Icc X T ht.1.1

/-- **G2b — Lemma 12 on the graded `A_j`.**  `USetThin.lemma12_meansq_on_subset` at the
graded window parameters `(Hseq j, Pseq j, Qseq j)` and `A := (Ann ∖ ball) ∩ 𝒯ⱼ`.  The main
term is restricted to `A_j` along with the left side (that is what §8 spends the graded
smallness on); the three error rows keep their full `[−T,T]` pricing. -/
theorem lemma12_on_TsetG (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (Jb j : ℕ)
    (hH : 2 ≤ Hseq j) (N Xd : ℕ) (hX : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hP : 1 ≤ Pseq j)
    (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → Pseq j ≤ p → p ≤ Qseq j → ¬ p ∣ m → a (p * m) = b m * c p)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hwin : ∀ p m : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j → c p * b m ≠ 0 →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ))
    (X T t₁ : ℝ) (hT : 0 ≤ T) :
    (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG fb Pseq Qseq Hseq αseq Jb j,
        ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
          * (∑ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
              ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG fb Pseq Qseq Hseq αseq Jb j,
                ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
        + 2 * (3 * ((2 * T + 20 * (N : ℝ))
                * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2))
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ Finset.Icc 1 N,
                    ‖ramP2coeff N (Pseq j) (Qseq j) a b c n‖ ^ 2 / (n : ℝ) ^ 2
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega (Pseq j) (Qseq j) n = 0),
                    ‖a n‖ ^ 2 / (n : ℝ) ^ 2)) :=
  lemma12_meansq_on_subset (Hseq j) hH N Xd (Pseq j) (Qseq j) hX hN hP a b c hcoef hb hc hwin
    T hT _ (measurableSet_annulus_TsetG fb Pseq Qseq Hseq αseq Jb j X T t₁)
    (annulus_TsetG_subset_Icc fb Pseq Qseq Hseq αseq Jb j X T t₁)

/-- **G2b (exit) — Lemma 12 on `A_j` under the §8.3 block-support pin (P-iii).**  With the
block-support condition on the coefficient support the coprime-tail row vanishes
identically, leaving the seam row and the `p²` row. -/
theorem lemma12_on_TsetG_blockSupport (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
    (Jb j : ℕ) (hH : 2 ≤ Hseq j) (N Xd : ℕ) (hX : 1 ≤ Xd) (hN : 2 * Xd ≤ N)
    (hP : 1 ≤ Pseq j) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → Pseq j ≤ p → p ≤ Qseq j → ¬ p ∣ m → a (p * m) = b m * c p)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hwin : ∀ p m : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j → c p * b m ≠ 0 →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ))
    (hsupp : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega (Pseq j) (Qseq j) n)
    (X T t₁ : ℝ) (hT : 0 ≤ T) :
    (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG fb Pseq Qseq Hseq αseq Jb j,
        ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
          * (∑ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
              ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG fb Pseq Qseq Hseq αseq Jb j,
                ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
        + 2 * (3 * ((2 * T + 20 * (N : ℝ))
                * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2))
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ Finset.Icc 1 N,
                    ‖ramP2coeff N (Pseq j) (Qseq j) a b c n‖ ^ 2 / (n : ℝ) ^ 2)) :=
  lemma12_meansq_on_subset_blockSupport (Hseq j) hH N Xd (Pseq j) (Qseq j) hX hN hP a b c
    hcoef hb hc hwin hsupp T hT _
    (measurableSet_annulus_TsetG fb Pseq Qseq Hseq αseq Jb j X T t₁)
    (annulus_TsetG_subset_Icc fb Pseq Qseq Hseq αseq Jb j X T t₁)

/-! ## §3 — G2c: the sharp-length co-factor MVT -/

/-- **The co-factor MVT at any admissible length.**  `ramR = spoly M (ramRcoeff)` for any
`M` containing the co-factor range (`USetThinTS.ramR_eq_spoly`), so the landed
Montgomery–Vaughan row `MomentsA2.moment_core_bound` applies verbatim at that `M`.  The
`M` is a free parameter — law #253: the *choice* of `M` is the content (see
`cofactor_mvt_sharp` vs `cofactor_mvt_dyadic_lossy`), so it may not be hidden. -/
theorem cofactor_mvt_of_subset (H : ℝ) (N Xd P Q v M : ℕ) (b : ℕ → ℂ) (T : ℝ)
    (hM : ramRrange H N Xd v ⊆ Finset.Icc 1 M) :
    (∫ t in (-T)..T, ‖ramR H N Xd P Q v b t‖ ^ 2)
      ≤ (2 * T + 20 * (M : ℝ))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q v b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  have hcongr : (∫ t in (-T)..T, ‖ramR H N Xd P Q v b t‖ ^ 2)
      = ∫ t in (-T)..T, ‖spoly M (ramRcoeff H N Xd P Q v b) t‖ ^ 2 :=
    intervalIntegral.integral_congr
      (fun t _ => by rw [ramR_eq_spoly H N Xd P Q v M b hM t])
  rw [hcongr]
  exact moment_core_bound M (ramRcoeff H N Xd P Q v b) T

/-- **G2c — the SHARP-`M` co-factor MVT** (⟦V4a⟧'s sharp-`M` law).  The length is
`Ms ≥ 2·ramRbot H Xd v = 2·Xd·e^{−v/H}` — the co-factor's own dyadic window — not the row's
`N ≍ 2Xd`. -/
theorem cofactor_mvt_sharp (H : ℝ) (N Xd P Q v Ms : ℕ) (b : ℕ → ℂ) (T : ℝ)
    (hMs : 2 * ramRbot H Xd v ≤ (Ms : ℝ)) :
    (∫ t in (-T)..T, ‖ramR H N Xd P Q v b t‖ ^ 2)
      ≤ (2 * T + 20 * (Ms : ℝ))
          * ∑ m ∈ Finset.Icc 1 Ms, ‖ramRcoeff H N Xd P Q v b m‖ ^ 2 / (m : ℝ) ^ 2 :=
  cofactor_mvt_of_subset H N Xd P Q v Ms b T (ramRrange_subset_Icc_sharp H N Xd v Ms hMs)

/-- The co-factor window has at most `2·X_v` integers (it sits in `[X_v, 2X_v]`). -/
lemma ramRrange_card_le (H : ℝ) (N Xd v : ℕ) :
    ((ramRrange H N Xd v).card : ℝ) ≤ 2 * ramRbot H Xd v := by
  have hb0 : (0 : ℝ) ≤ ramRbot H Xd v := ramRbot_nonneg H Xd v
  have hsub : ramRrange H N Xd v ⊆ Finset.Icc 1 ⌊2 * ramRbot H Xd v⌋₊ := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨ramRrange_one_le hm, Nat.le_floor (ramRrange_le_top hm)⟩
  have hcard : (ramRrange H N Xd v).card ≤ ⌊2 * ramRbot H Xd v⌋₊ := by
    have h := Finset.card_le_card hsub
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
  have hfloor : (⌊2 * ramRbot H Xd v⌋₊ : ℝ) ≤ 2 * ramRbot H Xd v :=
    Nat.floor_le (by positivity)
  exact le_trans (by exact_mod_cast hcard) hfloor

/-- **The co-factor's harmonic-square mass.**  `Σ_{m ∈ [X_v, 2X_v]} 1/m² ≤ 2/X_v`: at most
`2X_v` terms, each at most `1/X_v²`.  This is the `1/M`-shape that makes
`M·(mass) ≍ 1` at the sharp `M ≍ 2X_v` — at `Ms ≍ 2X_v` the bound `2/X_v` IS the
`4/Ms`-shape, and `Ms·(4/Ms) = 4` is the absolute constant the sharp law buys. -/
lemma ramRrange_mass_le (H : ℝ) (N Xd v : ℕ) (hbot : 0 < ramRbot H Xd v) :
    ∑ m ∈ ramRrange H N Xd v, 1 / (m : ℝ) ^ 2 ≤ 2 / ramRbot H Xd v := by
  have hterm : ∀ m ∈ ramRrange H N Xd v,
      1 / (m : ℝ) ^ 2 ≤ 1 / ramRbot H Xd v ^ 2 := by
    intro m hm
    have hmb : ramRbot H Xd v ≤ (m : ℝ) := ramRrange_bot_le hm
    have hm0 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hbot hmb
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  calc ∑ m ∈ ramRrange H N Xd v, 1 / (m : ℝ) ^ 2
      ≤ ∑ _m ∈ ramRrange H N Xd v, 1 / ramRbot H Xd v ^ 2 := Finset.sum_le_sum hterm
    _ = ((ramRrange H N Xd v).card : ℝ) * (1 / ramRbot H Xd v ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * ramRbot H Xd v) * (1 / ramRbot H Xd v ^ 2) :=
        mul_le_mul_of_nonneg_right (ramRrange_card_le H N Xd v) (by positivity)
    _ = 2 / ramRbot H Xd v := by field_simp

/-- The co-factor MVT with the coefficient mass discharged at `‖b‖ ≤ 1`
(`USetThinTS.ramRcoeff_mass_le`). -/
theorem cofactor_mvt_mass_of_subset (H : ℝ) (N Xd P Q v M : ℕ) (b : ℕ → ℂ)
    (hb : ∀ m, ‖b m‖ ≤ 1) (T : ℝ) (hT : 0 ≤ T)
    (hM : ramRrange H N Xd v ⊆ Finset.Icc 1 M) (hbot : 0 < ramRbot H Xd v) :
    (∫ t in (-T)..T, ‖ramR H N Xd P Q v b t‖ ^ 2)
      ≤ (2 * T + 20 * (M : ℝ)) * (2 / ramRbot H Xd v) := by
  have hpre : (0 : ℝ) ≤ 2 * T + 20 * (M : ℝ) := by positivity
  refine le_trans (cofactor_mvt_of_subset H N Xd P Q v M b T hM) ?_
  refine mul_le_mul_of_nonneg_left ?_ hpre
  exact le_trans (ramRcoeff_mass_le H N Xd P Q v M b hb hM) (ramRrange_mass_le H N Xd v hbot)

/-- **G2c (exit) — the sharp instantiation, in closed form.**  At any co-factor length
pinned to the window, `2·X_v ≤ Ms ≤ 3·X_v` (the consumer's rounding of `⌈2X_v⌉`),

  `∫_{−T}^{T} ‖R_{v,H}(1+it)‖² dt ≤ 4T/X_v + 120,   X_v = ramRbot H Xd v = Xd·e^{−v/H}`.

The `20M` term has collapsed to the **absolute constant `120`** — that is the whole content
of the sharp-`M` law (compare `cofactor_mvt_dyadic_lossy`). -/
theorem cofactor_mvt_sharp_exit (H : ℝ) (N Xd P Q v Ms : ℕ) (b : ℕ → ℂ)
    (hb : ∀ m, ‖b m‖ ≤ 1) (T : ℝ) (hT : 0 ≤ T) (hbot : 0 < ramRbot H Xd v)
    (hMs : 2 * ramRbot H Xd v ≤ (Ms : ℝ)) (hMs' : (Ms : ℝ) ≤ 3 * ramRbot H Xd v) :
    (∫ t in (-T)..T, ‖ramR H N Xd P Q v b t‖ ^ 2)
      ≤ 4 * T / ramRbot H Xd v + 120 := by
  refine le_trans (cofactor_mvt_mass_of_subset H N Xd P Q v Ms b hb T hT
    (ramRrange_subset_Icc_sharp H N Xd v Ms hMs) hbot) ?_
  have hinv : (0 : ℝ) < 2 / ramRbot H Xd v := by positivity
  have hstep : (2 * T + 20 * (Ms : ℝ)) * (2 / ramRbot H Xd v)
      ≤ (2 * T + 60 * ramRbot H Xd v) * (2 / ramRbot H Xd v) := by
    refine mul_le_mul_of_nonneg_right ?_ hinv.le
    linarith
  refine le_trans hstep (le_of_eq ?_)
  field_simp
  ring

/-- **The sharp-length gate is SATISFIABLE (no silent vacuity).**  Whenever the co-factor
window bottom clears `1` — the live regime, `X_v = Xd·e^{−v/H} ≥ 1` since `v ≤ ⌊H log Q⌋`
and `Q ≪ Xd` — the rounding `Ms := ⌈2X_v⌉` meets both gates of
`cofactor_mvt_sharp_exit`.  (Below `X_v = 1` the two-sided window `[2X_v, 3X_v]` can miss
every natural, so the gate would be vacuous; that is exactly why this witness is
recorded rather than assumed.) -/
lemma exists_sharp_length (H : ℝ) (Xd v : ℕ) (h1 : 1 ≤ ramRbot H Xd v) :
    ∃ Ms : ℕ, 2 * ramRbot H Xd v ≤ (Ms : ℝ) ∧ (Ms : ℝ) ≤ 3 * ramRbot H Xd v := by
  refine ⟨⌈2 * ramRbot H Xd v⌉₊, Nat.le_ceil _, ?_⟩
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * ramRbot H Xd v by linarith)
  linarith

/-- `1/X_v = e^{v/H}/Xd` — the identity that makes the saving visible. -/
lemma one_div_ramRbot (H : ℝ) {Xd : ℕ} (hXd : 0 < Xd) (v : ℕ) :
    1 / ramRbot H Xd v = Real.exp ((v : ℝ) / H) / (Xd : ℝ) := by
  have hX0 : ((Xd : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
    exact this.ne'
  have hE : Real.exp ((v : ℝ) / H) ≠ 0 := (Real.exp_pos _).ne'
  rw [ramRbot, neg_div, Real.exp_neg]
  field_simp

/-- **G2c (exit, `e^{v/H}` visible).**  The sharp exit with `1/X_v` expanded: the co-factor
mean square is `4T·e^{v/H}/Xd + 120`.  Only the `T`-leg carries the block factor; the
length leg is an absolute constant. -/
theorem cofactor_mvt_sharp_exit_visible (H : ℝ) (N Xd P Q v Ms : ℕ) (b : ℕ → ℂ)
    (hb : ∀ m, ‖b m‖ ≤ 1) (T : ℝ) (hT : 0 ≤ T) (hXd : 0 < Xd)
    (hbot : 0 < ramRbot H Xd v)
    (hMs : 2 * ramRbot H Xd v ≤ (Ms : ℝ)) (hMs' : (Ms : ℝ) ≤ 3 * ramRbot H Xd v) :
    (∫ t in (-T)..T, ‖ramR H N Xd P Q v b t‖ ^ 2)
      ≤ 4 * T * Real.exp ((v : ℝ) / H) / (Xd : ℝ) + 120 := by
  refine le_trans (cofactor_mvt_sharp_exit H N Xd P Q v Ms b hb T hT hbot hMs hMs') ?_
  have hone := one_div_ramRbot H hXd (v := v)
  have hrw : 4 * T / ramRbot H Xd v = 4 * T * Real.exp ((v : ℝ) / H) / (Xd : ℝ) := by
    rw [div_eq_mul_one_div, hone]
    ring
  rw [hrw]

/-- **G2c (the loss, kernel-certified) — the DYADIC instantiation.**  The same route at the
row's length `M := N` (`USetThinTS.ramRrange_subset_Icc`) gives

  `∫_{−T}^{T} ‖R_{v,H}(1+it)‖² dt ≤ 4T·e^{v/H}/Xd + 40·N·e^{v/H}/Xd`,

so at `N ≍ 2Xd` the length leg is `80·e^{v/H}` where the sharp instantiation gives `120`.
The `20N` term is lossy by **exactly `e^{v/H}`** — the co-factor mass MR (23) must pay.
This lemma exists so the comparison is a theorem, not a remark. -/
theorem cofactor_mvt_dyadic_lossy (H : ℝ) (N Xd P Q v : ℕ) (b : ℕ → ℂ)
    (hb : ∀ m, ‖b m‖ ≤ 1) (T : ℝ) (hT : 0 ≤ T) (hXd : 0 < Xd)
    (hbot : 0 < ramRbot H Xd v) :
    (∫ t in (-T)..T, ‖ramR H N Xd P Q v b t‖ ^ 2)
      ≤ 4 * T * Real.exp ((v : ℝ) / H) / (Xd : ℝ)
        + 40 * (N : ℝ) * Real.exp ((v : ℝ) / H) / (Xd : ℝ) := by
  refine le_trans (cofactor_mvt_mass_of_subset H N Xd P Q v N b hb T hT
    (ramRrange_subset_Icc H N Xd v) hbot) ?_
  have hone := one_div_ramRbot H hXd (v := v)
  have hexpand : (2 * T + 20 * (N : ℝ)) * (2 / ramRbot H Xd v)
      = (4 * T + 40 * (N : ℝ)) * (1 / ramRbot H Xd v) := by ring
  rw [hexpand, hone]
  exact le_of_eq (by ring)

/-! ## §4 — G2d: the two geometric `v`-sums over the block index set -/

/-- The block-index sum is a geometric series: `e^{c·v/H} = (e^{c/H})^v`. -/
private lemma exp_block_pow (c H : ℝ) (v : ℕ) :
    Real.exp (c * (v : ℝ) / H) = 1 * Real.exp (c / H) ^ v := by
  rw [one_mul, ← Real.exp_nat_mul]
  congr 1
  ring

/-- **G2d (decaying leg) — the geometric form.**  With `v₀ = ⌊H log P⌋` the bottom block
index,

  `Σ_{v ∈ I} e^{−2α v/H} ≤ e^{−2α v₀/H} / (1 − e^{−2α/H})`.

The ratio gate `e^{−2α/H} < 1` is exactly `0 < α` (with `0 < H`) and is carried
in-statement.  **Read the denominator honestly**: `α/H → 0` in the live regime, so
`1/(1 − e^{−2α/H}) ≈ H/(2α)` — never `O(1)`.  `sum_exp_neg_graded_rate` states that form;
`sum_exp_neg_graded_card` states the crude `|I|`-times-top alternative, and the consumer
takes the min. -/
theorem sum_exp_neg_graded (H α : ℝ) (hH : 0 < H) (hα : 0 < α) (P Q : ℕ) :
    ∑ v ∈ ramI H P Q, Real.exp (-(2 * α) * (v : ℝ) / H)
      ≤ Real.exp (-(2 * α) * (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) / H)
          / (1 - Real.exp (-(2 * α) / H)) := by
  have hneg : -(2 * α) / H < 0 := div_neg_of_neg_of_pos (by linarith) hH
  have hr0 : (0 : ℝ) ≤ Real.exp (-(2 * α) / H) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(2 * α) / H) < 1 := by
    have h := Real.exp_lt_exp.mpr hneg
    rwa [Real.exp_zero] at h
  rw [ramI]
  calc ∑ v ∈ Finset.Icc ⌊H * Real.log (P : ℝ)⌋₊ ⌊H * Real.log (Q : ℝ)⌋₊,
        Real.exp (-(2 * α) * (v : ℝ) / H)
      = ∑ v ∈ Finset.Icc ⌊H * Real.log (P : ℝ)⌋₊ ⌊H * Real.log (Q : ℝ)⌋₊,
          1 * Real.exp (-(2 * α) / H) ^ v :=
        Finset.sum_congr rfl (fun v _ => exp_block_pow (-(2 * α)) H v)
    _ ≤ 1 * Real.exp (-(2 * α) / H) ^ ⌊H * Real.log (P : ℝ)⌋₊
          / (1 - Real.exp (-(2 * α) / H)) :=
        Salt.Tactic.geom_sum_le_bot_Icc (by norm_num) hr0 hr1 _ _
    _ = Real.exp (-(2 * α) * (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) / H)
          / (1 - Real.exp (-(2 * α) / H)) := by
        rw [← exp_block_pow (-(2 * α)) H ⌊H * Real.log (P : ℝ)⌋₊]

/-- **G2d (decaying leg) — the `H/(2α)` form.**  `1/(1 − e^{−x}) ≤ e^x/x` (from
`x + 1 ≤ e^x`), so at `x = 2α/H`

  `Σ_{v ∈ I} e^{−2α v/H} ≤ (H/(2α))·e^{−2α(v₀−1)/H}`.

This is the shape the consumer must budget: the `v`-sum costs a factor `H/(2α)`, which
GROWS as the grading weakens.  Stating only the `1/(1−r)` form would hide it. -/
theorem sum_exp_neg_graded_rate (H α : ℝ) (hH : 0 < H) (hα : 0 < α) (P Q : ℕ) :
    ∑ v ∈ ramI H P Q, Real.exp (-(2 * α) * (v : ℝ) / H)
      ≤ H / (2 * α)
          * Real.exp (-(2 * α) * ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1) / H) := by
  have hx : (0 : ℝ) < 2 * α / H := by positivity
  have hneg : -(2 * α) / H < 0 := div_neg_of_neg_of_pos (by linarith) hH
  have hr1 : Real.exp (-(2 * α) / H) < 1 := by
    have h := Real.exp_lt_exp.mpr hneg
    rwa [Real.exp_zero] at h
  have hden : (0 : ℝ) < 1 - Real.exp (-(2 * α) / H) := by linarith
  have hsum0 : 2 * α / H + -(2 * α) / H = 0 := by ring
  have hinv : Real.exp (2 * α / H) * Real.exp (-(2 * α) / H) = 1 := by
    rw [← Real.exp_add, hsum0, Real.exp_zero]
  have hEr : Real.exp (2 * α / H) * (1 - Real.exp (-(2 * α) / H))
      = Real.exp (2 * α / H) - 1 := by
    rw [mul_sub, mul_one, hinv]
  have hEx : 2 * α / H + 1 ≤ Real.exp (2 * α / H) := Real.add_one_le_exp _
  have hkey : (1 : ℝ) / (1 - Real.exp (-(2 * α) / H))
      ≤ Real.exp (2 * α / H) / (2 * α / H) := by
    rw [div_le_div_iff₀ hden hx]
    rw [hEr]
    linarith
  have hEfac : Real.exp (2 * α / H) / (2 * α / H)
      = H / (2 * α) * Real.exp (2 * α / H) := by
    field_simp
  have hmerge : Real.exp (-(2 * α) * (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) / H)
        * Real.exp (2 * α / H)
      = Real.exp (-(2 * α) * ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1) / H) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have htop : (0 : ℝ) ≤ Real.exp (-(2 * α) * (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) / H) :=
    (Real.exp_pos _).le
  refine le_trans (sum_exp_neg_graded H α hH hα P Q) ?_
  calc Real.exp (-(2 * α) * (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) / H)
        / (1 - Real.exp (-(2 * α) / H))
      = Real.exp (-(2 * α) * (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) / H)
          * (1 / (1 - Real.exp (-(2 * α) / H))) := by ring
    _ ≤ Real.exp (-(2 * α) * (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) / H)
          * (Real.exp (2 * α / H) / (2 * α / H)) :=
        mul_le_mul_of_nonneg_left hkey htop
    _ = H / (2 * α)
          * (Real.exp (-(2 * α) * (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) / H)
              * Real.exp (2 * α / H)) := by rw [hEfac]; ring
    _ = H / (2 * α)
          * Real.exp (-(2 * α) * ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1) / H) := by
        rw [hmerge]

/-- **G2d (decaying leg) — the crude `|I|` form.**  Every term is at most the bottom one,
so the sum is at most `|I_J|·e^{−2α v₀/H}`.  When `α/H` is small this beats the geometric
form (whose `1/(1−r) ≈ H/(2α)` may exceed the block count); the consumer takes the min of
the two, which is why BOTH are stated. -/
theorem sum_exp_neg_graded_card (H α : ℝ) (hH : 0 < H) (hα : 0 ≤ α) (P Q : ℕ) :
    ∑ v ∈ ramI H P Q, Real.exp (-(2 * α) * (v : ℝ) / H)
      ≤ ((ramI H P Q).card : ℝ)
          * Real.exp (-(2 * α) * (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) / H) := by
  have hterm : ∀ v ∈ ramI H P Q,
      Real.exp (-(2 * α) * (v : ℝ) / H)
        ≤ Real.exp (-(2 * α) * (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) / H) := by
    intro v hv
    have hv0 : (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) ≤ (v : ℝ) := by
      rw [ramI, Finset.mem_Icc] at hv
      exact_mod_cast hv.1
    refine Real.exp_le_exp.mpr ?_
    rw [div_le_div_iff_of_pos_right hH]
    nlinarith [hv0, hα]
  calc ∑ v ∈ ramI H P Q, Real.exp (-(2 * α) * (v : ℝ) / H)
      ≤ ∑ _v ∈ ramI H P Q, Real.exp (-(2 * α) * (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) / H) :=
        Finset.sum_le_sum hterm
    _ = ((ramI H P Q).card : ℝ)
          * Real.exp (-(2 * α) * (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) / H) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **G2d (growing leg) — the top-dominated geometric form.**  With `v₁ = ⌊H log Q⌋` the top
block index,

  `Σ_{v ∈ I} e^{(1−2α) v/H} ≤ e^{(1−2α)(v₁+1)/H} / (e^{(1−2α)/H} − 1)`.

The ratio gate `1 < e^{(1−2α)/H}` is exactly `2α < 1` (with `0 < H`) and is carried
in-statement — the sum DIVERGES the other way, so the gate is load-bearing, not cosmetic.
(`0 < α` is not needed here and is therefore not carried: an unused gate is a false pin.) -/
theorem sum_exp_growth (H α : ℝ) (hH : 0 < H) (hα2 : 2 * α < 1) (P Q : ℕ) :
    ∑ v ∈ ramI H P Q, Real.exp ((1 - 2 * α) * (v : ℝ) / H)
      ≤ Real.exp ((1 - 2 * α) * ((⌊H * Real.log (Q : ℝ)⌋₊ : ℝ) + 1) / H)
          / (Real.exp ((1 - 2 * α) / H) - 1) := by
  have hpos : (0 : ℝ) < (1 - 2 * α) / H := by
    apply div_pos (by linarith) hH
  have hr1 : (1 : ℝ) < Real.exp ((1 - 2 * α) / H) := by
    have h := Real.exp_lt_exp.mpr hpos
    rwa [Real.exp_zero] at h
  rw [ramI]
  calc ∑ v ∈ Finset.Icc ⌊H * Real.log (P : ℝ)⌋₊ ⌊H * Real.log (Q : ℝ)⌋₊,
        Real.exp ((1 - 2 * α) * (v : ℝ) / H)
      = ∑ v ∈ Finset.Icc ⌊H * Real.log (P : ℝ)⌋₊ ⌊H * Real.log (Q : ℝ)⌋₊,
          1 * Real.exp ((1 - 2 * α) / H) ^ v :=
        Finset.sum_congr rfl (fun v _ => exp_block_pow (1 - 2 * α) H v)
    _ ≤ 1 * Real.exp ((1 - 2 * α) / H) ^ (⌊H * Real.log (Q : ℝ)⌋₊ + 1)
          / (Real.exp ((1 - 2 * α) / H) - 1) :=
        Salt.Tactic.geom_sum_le_top_Icc (by norm_num) hr1 _ _
    _ = Real.exp ((1 - 2 * α) * ((⌊H * Real.log (Q : ℝ)⌋₊ : ℝ) + 1) / H)
          / (Real.exp ((1 - 2 * α) / H) - 1) := by
        rw [← exp_block_pow (1 - 2 * α) H (⌊H * Real.log (Q : ℝ)⌋₊ + 1)]
        push_cast
        ring_nf

/-- **G2d (growing leg) — the closed `Q^{1−2α}` form.**  `e^y − 1 ≥ y` at
`y = (1−2α)/H` and `⌊H log Q⌋ ≤ H log Q` give

  `Σ_{v ∈ I} e^{(1−2α) v/H} ≤ (H/(1−2α))·e^{(1−2α)/H}·Q^{1−2α}`.

This is the shape §8.2 budgets against: the co-factor's `Q^{1−2α}` growth against the
graded threshold's decay, with the block-height factor `H/(1−2α)` explicit (law #253). -/
theorem sum_exp_growth_top (H α : ℝ) (hH : 0 < H) (hα2 : 2 * α < 1) (P Q : ℕ)
    (hQ : 1 ≤ Q) :
    ∑ v ∈ ramI H P Q, Real.exp ((1 - 2 * α) * (v : ℝ) / H)
      ≤ H / (1 - 2 * α) * Real.exp ((1 - 2 * α) / H) * (Q : ℝ) ^ (1 - 2 * α) := by
  have hy : (0 : ℝ) < (1 - 2 * α) / H := div_pos (by linarith) hH
  have hr1 : (1 : ℝ) < Real.exp ((1 - 2 * α) / H) := by
    have h := Real.exp_lt_exp.mpr hy
    rwa [Real.exp_zero] at h
  have hden : (0 : ℝ) < Real.exp ((1 - 2 * α) / H) - 1 := by linarith
  have hEy : (1 - 2 * α) / H ≤ Real.exp ((1 - 2 * α) / H) - 1 := by
    have h := Real.add_one_le_exp ((1 - 2 * α) / H)
    linarith
  -- the denominator: `1/(e^y − 1) ≤ H/(1−2α)`
  have hdenle : (1 : ℝ) / (Real.exp ((1 - 2 * α) / H) - 1) ≤ H / (1 - 2 * α) := by
    rw [div_le_div_iff₀ hden (by linarith)]
    rw [one_mul]
    rw [div_le_iff₀ hH] at hEy
    linarith
  -- the numerator: `e^{(1−2α)(v₁+1)/H} ≤ e^{(1−2α)/H}·Q^{1−2α}`
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hlogQ : (0 : ℝ) ≤ Real.log (Q : ℝ) := Real.log_nonneg (by exact_mod_cast hQ)
  have hfloor : (⌊H * Real.log (Q : ℝ)⌋₊ : ℝ) ≤ H * Real.log (Q : ℝ) :=
    Nat.floor_le (by positivity)
  have hQrpow : (Q : ℝ) ^ (1 - 2 * α) = Real.exp (Real.log (Q : ℝ) * (1 - 2 * α)) :=
    Real.rpow_def_of_pos hQ0 _
  have hnum : Real.exp ((1 - 2 * α) * ((⌊H * Real.log (Q : ℝ)⌋₊ : ℝ) + 1) / H)
      ≤ Real.exp ((1 - 2 * α) / H) * (Q : ℝ) ^ (1 - 2 * α) := by
    rw [hQrpow, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [div_add' _ _ _ (ne_of_gt hH), div_le_div_iff_of_pos_right hH]
    nlinarith [hfloor, hα2]
  have hnum0 : (0 : ℝ)
      ≤ Real.exp ((1 - 2 * α) * ((⌊H * Real.log (Q : ℝ)⌋₊ : ℝ) + 1) / H) :=
    (Real.exp_pos _).le
  have hQpow0 : (0 : ℝ) ≤ Real.exp ((1 - 2 * α) / H) * (Q : ℝ) ^ (1 - 2 * α) := by
    have : (0 : ℝ) ≤ (Q : ℝ) ^ (1 - 2 * α) := Real.rpow_nonneg hQ0.le _
    positivity
  refine le_trans (sum_exp_growth H α hH hα2 P Q) ?_
  calc Real.exp ((1 - 2 * α) * ((⌊H * Real.log (Q : ℝ)⌋₊ : ℝ) + 1) / H)
        / (Real.exp ((1 - 2 * α) / H) - 1)
      = Real.exp ((1 - 2 * α) * ((⌊H * Real.log (Q : ℝ)⌋₊ : ℝ) + 1) / H)
          * (1 / (Real.exp ((1 - 2 * α) / H) - 1)) := by ring
    _ ≤ (Real.exp ((1 - 2 * α) / H) * (Q : ℝ) ^ (1 - 2 * α)) * (H / (1 - 2 * α)) := by
        refine mul_le_mul hnum hdenle (by positivity) hQpow0
    _ = H / (1 - 2 * α) * Real.exp ((1 - 2 * α) / H) * (Q : ℝ) ^ (1 - 2 * α) := by ring

end Salt.MR
