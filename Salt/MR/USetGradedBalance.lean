/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetBalance
import Salt.MR.USetGradedThin
import Salt.MR.CofactorLocal

/-!
# USetGradedBalance — the GRADED serial balance (ROUTE G, stone G1b)

The graded twin of `USetBalance`: the `hU` chain of MR §8.3 replayed at the **graded**
partition (`SeamGraded.UsetG`, MR eq (21)) instead of the flat `Decomp.Uset`, with the
`𝒯_L` co-factor supply taken from the **repaired, localized** arm
(`CofactorLocal.tL_supply_discharged_local`).  The exit is the `hU` binder of
`SeamGraded.prop_A3_T1_row_split_weightedG`:

  `(∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset,
      ‖spoly N a t‖^2) ≤ U`.

⟦V6⟧ HELD this stone behind the far-arm repair so the ~1000-line replay would not be paid
twice against a broken arm; ⟦V7⟧'s `farErr34_local_closes` lifted the hold (R1 + R2 + R3).
Everything here is parallel and additive: no landed statement is touched.

## THE V-SPLIT (⟦V6⟧'s G1b note, as-built)

The flat chain used **one** `V` for two different jobs.  The graded chain separates them, and
carries both parameters honestly:

* **`VJ` — the THINNESS level** (`Vthin`).  It bounds the graded thresholds
  `exp(α_Jb·v/H_Jb)`, `v ∈ I_Jb`, through the uniformisation binder
  `hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb), exp(αseq Jb·v/Hseq Jb) ≤ VJ`
  (`USetGradedThin.usetG_thin`'s own binder; `usetG_thin_Q` supplies the concrete
  `VJ = Q_Jb^{α_Jb}` and `usetG_thin_pin` its `X^{ε}` pin form).  Its gates are
  `hVJ`, `0 ≤ α_Jb`, `α_Jb ≤ 1/4 − η`, `2η ≤ 1` and the co-factor budget
  `thinBundleG·X^{1−2η} ≤ Ms j`.
  **The flat `hVinv : V⁻¹ ≤ δ/K₀` and `hVα : log V ≤ α·log P_Jb` are GONE**: there is no
  flat `δ` to invert, and the Lemma-8 exponent is `2α_Jb` *exactly* (⟦V6⟧'s α-collapse,
  landed in `ramQ_graded_count`) — so the α-gate is asked of `αseq Jb` itself, with no
  `K₀`-inflation and no `η′ := η/2` correction.
* **`V` — the SPLIT level** (`Vsplit`), the `𝒯_S ∥ 𝒯_L` threshold at `δ'`.  Its gates are
  `1 ≤ V`, `V⁻¹ ≤ δ'`, `log V ≤ 100·log L` — the `≤ L^100` level that feeds the `𝒯_L` kill
  (`CofactorSupply`'s `tL_main_sumsq` window), and nothing else.

Conflating them would be a false byte-fit: `VJ` lives at the block's own graded base and
`V` at the branch threshold.

## What is reused VERBATIM (predicate-blind), and what has a graded twin

Reused: `USetBalance.uset_integral_to_branches` (an arbitrary measurable `A ⊆ [−T,T]` — the
`𝒰`-predicate never enters), `block_sum_bound`, `sum_inv_sq_Icc_le`, `tL_block_weight`,
`sum_TS_add_TL`, `USetThinTS.TS_branch_meansq` and `thin_sqrt_kill`, and the abstract
`hU_balance` / `hU_balance_beats_door`.  Twinned: the thinness feed (`thinBundleG`,
`usetG_thin_bundle`, `usetG_thin_sqrt_kill`, `usetG_TS_branch(_meanvalue)`, `TSG_feed_of_thin`
— the flat `uset_TS_branch` consumes `Uset_thin` internally, so it cannot be reused), the
`𝒯_L` feed at the localized supply (`TLBlockGatesLoc`, `TLG_feed_of_supply_local`), and the
assembly (`usetG_integral_to_branches`, `hUG_exit_of_branches`, `hUG_supplied`,
`hUG_balance`, `hUG_discharged`).

## THE LOCALIZED SUPPLY — what the repair removes from this file's hypotheses

`CofactorSupply.tL_supply_discharged` demands, per `𝒯_L` ordinate,
`R ≤ |t−t₁|` ∧ `|t−t₁| ≤ Dmax` ∧ `∀ k ∈ [k₀,M], |t| + T*(k, log k) ≤ 3X`, and prices the
transfer at `Rmax := Dmax + 1`.  `CofactorLocal.tL_supply_discharged_local` demands
`R ≤ |t−t₁|` ∧ `|t| + T*(M, log M) ≤ 3X` and prices it at `Rmax := T*(M, log M)`.  So the
whole `Dmax` layer — the ambient `hDmax : Tann + |t₁| ≤ Dmax` of the flat `hU_supplied`, the
`(Dmax + 1)` slot in `cofactorRbd`, and the `∀ k` box family — **does not occur in this
file**.  That is the ⟦V6a⟧ floor removed at the source, and it is why the graded `R̄` budget
is gradeable at all (⟦V7⟧: `farErr34_local_closes`).

## The gates that ride the exit in-statement (law #253)

`TannGate X Tann` (it supplies `hκ30` at the `J`-block through
`USetPins.kappa30_of_TannGate`; a polylog `Tann` refuses it, so dropping it is unsound);
MR Step 0's `Tann ≤ X`; the graded non-degeneracy pins `2 ≤ H_Jb`, `3 ≤ P_Jb ≤ Q_Jb`
(the `G0` empty-block trap — an empty `ramI` makes `BlockSmallG` vacuous), `1 ≤ Jb ≤ Jset`;
both `V`-parameters with their own gates (above); the sharp co-factor length `Ms`
(⟦V4a⟧ finding 1 — never the dyadic `N`); the per-block bundle `TLBlockGatesLoc`; the
localized contour box; and the two grade budgets `KS`, `R̄`.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 eq (21), pp. 19–20, 27–29 (§8.3);
`docs/exploration/hsup-design.md` ⟦V4a⟧/⟦V5d⟧/⟦V6⟧/⟦V6b⟧/⟦V7⟧.
-/

namespace Salt.MR

open scoped BigOperators
open Finset MeasureTheory

/-! ## §1 — GB-1: the graded `𝒰` integral → the two branch exits -/

/-- **GB-1 — THE COMPOSITION AT `UsetG`** (`usetG_integral_to_branches`).  The `4·|I|` page
of `USetBalance` :105, instantiated at the graded far set
`(seamAnn X Tann ∖ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset`:

  `∫_{(Ann∖ball)∩𝒰G} ‖spoly N a‖² ≤ 4·|I|·Σ_{j∈I} (Sb j + Lb j) + 2E`.

`uset_integral_to_branches` is **predicate-blind** — it asks only for a measurable
`A ⊆ [−Tann, Tann]` — so the whole eq-(16)/discretisation/`δ'`-split page is reused verbatim
and this stone's own content is exactly the graded measurability discharge
(`SeamGraded.measurableSet_UsetG`, a countable intersection of complements of the CLOSED
`BlockSmallG` sets) plus the annulus window.  The `2·|I|` is the eq-(16) Cauchy–Schwarz, the
extra `2` the parity halving of the well-spaced discretisation, `E` Lemma 12's error row. -/
theorem usetG_integral_to_branches
    (H : ℝ) (N Xd P Q : ℕ) (a b c : ℕ → ℂ)
    (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (Jset : ℕ)
    (X Tann t₁ E : ℝ) (hT : 0 ≤ Tann)
    (herr : (∫ t in (-Tann)..Tann, ‖ramErr H N Xd P Q a b c t‖ ^ 2) ≤ E)
    (δ' : ℝ) (Sb Lb : ℕ → ℝ)
    (hTS : ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 →
      (↑𝒯 : Set ℝ) ⊆ (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset →
      (∑ t ∈ TsetSmall H P Q j c δ' 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2) ≤ Sb j)
    (hTL : ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 →
      (↑𝒯 : Set ℝ) ⊆ (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset →
      (∑ t ∈ tLset H P Q j c δ' 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2) ≤ Lb j) :
    (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset,
        ‖spoly N a t‖ ^ 2)
      ≤ 4 * ((ramI H P Q).card : ℝ) * (∑ j ∈ ramI H P Q, (Sb j + Lb j)) + 2 * E := by
  have hRm : MeasurableSet (seamAnn X Tann \ seamBall X t₁) :=
    (measurableSet_seamAnn X Tann).diff (measurableSet_seamBall X t₁)
  have hAm : MeasurableSet ((seamAnn X Tann \ seamBall X t₁)
      ∩ UsetG fb Pseq Qseq Hseq αseq Jset) :=
    hRm.inter (measurableSet_UsetG fb Pseq Qseq Hseq αseq Jset)
  have hRsub : (seamAnn X Tann \ seamBall X t₁) ⊆ Set.Icc (-Tann) Tann :=
    fun _ ht => seamAnn_subset_Icc X Tann ht.1
  exact uset_integral_to_branches H N Xd P Q a b c Tann E hT herr _ hAm
    (fun _ ht => hRsub ht.1) δ' Sb Lb hTS hTL

/-- **THE `G0` EMPTY-BLOCK TRAP, DISCHARGED FOR THIS FILE'S GATE LIST.**  An empty
`ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)` would make `BlockSmallG` a bounded `∀` over `∅` — hence
vacuously true, `UsetG` empty, and every statement below silently vacuous.  The three pins
that every stone of this file carries in-statement (`2 ≤ H_Jb`, `3 ≤ P_Jb`, `P_Jb ≤ Q_Jb`)
already forbid that, by `USetGradedThin.ramI_nonempty`.  Recorded as a kernel fact so the
non-degeneracy is not merely asserted in prose. -/
lemma gradedPins_nondegenerate {Hseq : ℕ → ℝ} {Pseq Qseq : ℕ → ℕ} {Jb : ℕ}
    (hH2 : 2 ≤ Hseq Jb) (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb) :
    (ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).Nonempty :=
  ramI_nonempty (by linarith) (by omega) hPQ

/-! ## §2 — GB-2a: the `𝒯_S` feed at the GRADED thinness -/

/-- **The `X^{o(1)}` bundle of the GRADED thinness count** — the graded twin of
`USetThinTS.thinBundle`.  Two changes, both structural (⟦V6⟧'s G1a bullet):

* the union factor is MR's own block count `|I_J| = |ramI H_J P_J Q_J|` (priced at the pin by
  `USetPrice.ramI_card_le_pin`, `≤ 2(log X)^{1+θ}`), **not** `card (dyadicPairs P_J Q_J) ≤
  (Q_J+1)²` — the `ratioChain`/pigeonhole layer of the flat route is simply absent;
* the level is the graded `VJ` (the uniform bound on `exp(α_J v/H_J)`), with no `K₀`
  division.

The `T`-power leg `T^{2α_J}` is NOT in the bundle: it factors out, exactly as in the flat
`thinBundle`, so `thin_sqrt_kill` applies verbatim. -/
noncomputable def thinBundleG (T VJ Hj : ℝ) (Pj Qj : ℕ) : ℝ :=
  ((ramI Hj Pj Qj).card : ℝ)
    * (840 * VJ ^ 2 * Real.exp (2 * (Real.log T / Real.log Pj) * Real.log (Real.log T)))

lemma thinBundleG_nonneg (T VJ Hj : ℝ) (Pj Qj : ℕ) : 0 ≤ thinBundleG T VJ Hj Pj Qj := by
  rw [thinBundleG]
  have h := Real.exp_pos (2 * (Real.log T / Real.log Pj) * Real.log (Real.log T))
  positivity

/-- **The graded thinness in bundle form.**  `usetG_thin`'s exit, with the `T`-power leg
factored out: `|𝒯| ≤ thinBundleG · T^{2α_Jb}`.

**THE α-COLLAPSE IS THE POINT** (⟦V6⟧): the flat `Uset_thin_alpha` had to *inflate* Lemma
8's exponent `2·log V/log P_Jb` up to `2α` through the gate `log V ≤ α·log P_Jb` (at the flat
pin, `α = α_J + log K₀/log P_J`).  Here the exponent is already `2·αseq Jb` — the block base
carries the grading, so `log V_v / log base = α_J` exactly and there is nothing to inflate.
The only α-hypotheses in this file are `0 ≤ αseq Jb` and `αseq Jb ≤ 1/4 − η`. -/
theorem usetG_thin_bundle (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ : ℝ) (hT : 1 < T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb) (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log T))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hU : ∀ t ∈ 𝒯, t ∈ UsetG f Pseq Qseq Hseq αseq J) :
    (𝒯.card : ℝ)
      ≤ thinBundleG T VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * T ^ (2 * αseq Jb) := by
  refine (usetG_thin f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2 hα0 T VJ hT hP3 hPQ hQT
    hκ30 hLL5 hVJ 𝒯 hws hsub hU).trans (le_of_eq ?_)
  rw [thinBundleG]
  ring

/-- **The graded kill.**  `|𝒯|·√T ≤ thinBundleG·X^{1−2η}` — the graded thinness spent through
`USetThinTS.thin_sqrt_kill` (predicate-blind: it takes the count as a number).  The gate is
`αseq Jb ≤ 1/4 − η` **plus MR Step 0's `T ≤ X`**; nothing else is needed. -/
theorem usetG_thin_sqrt_kill (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ : ℝ) (hT : 1 < T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb) (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log T))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hU : ∀ t ∈ 𝒯, t ∈ UsetG f Pseq Qseq Hseq αseq J)
    (η X : ℝ) (hα : αseq Jb ≤ 1 / 4 - η) (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) :
    (𝒯.card : ℝ) * Real.sqrt T
      ≤ thinBundleG T VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η) :=
  thin_sqrt_kill T X (thinBundleG T VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)) (αseq Jb) η
    (𝒯.card : ℝ) (le_of_lt hT) hTX (thinBundleG_nonneg T VJ (Hseq Jb) (Pseq Jb) (Qseq Jb))
    hα hη2
    (usetG_thin_bundle f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2 hα0 T VJ hT hP3 hPQ hQT
      hκ30 hLL5 hVJ 𝒯 hws hsub hU)

/-- **GB-2a — THE GRADED `𝒯_S` BRANCH.**  `USetThinTS.uset_TS_branch` at the graded
thinness.  The Halász page (`TS_branch_meansq`: the pointwise `ε²` gain plus Lemma 9 on the
co-factor at the sharp length `M`) is **predicate-blind** and is reused verbatim; only the
`|𝒯|·√T` slot changes, from `thinBundle·X^{1−2η}` to `thinBundleG·X^{1−2η}`. -/
theorem usetG_TS_branch (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ : ℝ) (hT : 1 < T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb) (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log T))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hU : ∀ t ∈ 𝒯, t ∈ UsetG f Pseq Qseq Hseq αseq J)
    (η X : ℝ) (hα : αseq Jb ≤ 1 / 4 - η) (hη2 : 2 * η ≤ 1) (hTX : T ≤ X)
    (H : ℝ) (N Xd P Q j M : ℕ) (b c : ℕ → ℂ) (ε : ℝ)
    (hM : ramRrange H N Xd j ⊆ Finset.Icc 1 M) :
    ∑ t ∈ TsetSmall H P Q j c ε 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2
      ≤ ε ^ 2 * (2564 * ((M : ℝ)
            + thinBundleG T VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η))
          * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) := by
  refine (TS_branch_meansq H N Xd P Q j M b c hM ε T (le_of_lt hT) 𝒯 hws hsub).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ε)
  have hkill := usetG_thin_sqrt_kill f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2 hα0 T VJ
    hT hP3 hPQ hQT hκ30 hLL5 hVJ 𝒯 hws hsub hU η X hα hη2 hTX
  have hlog : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hmass : (0 : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun m _ => by positivity)
  nlinarith [mul_nonneg (sub_nonneg.mpr hkill) (mul_nonneg hlog hmass)]

/-- **GB-2a (exit) — the graded `𝒯_S` branch at the MEAN-VALUE grade.**  Once the graded
thinness budget clears the co-factor length (`thinBundleG·X^{1−2η} ≤ M`), Lemma 9 degenerates
to the mean value theorem and the branch is priced at the trivial grade times the pointwise
gain `ε²`.  The graded twin of `USetThinTS.uset_TS_branch_meanvalue`, byte-for-byte in its
exit shape (`5128 = 2·2564`). -/
theorem usetG_TS_branch_meanvalue (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ : ℝ) (hT : 1 < T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb) (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log T))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hU : ∀ t ∈ 𝒯, t ∈ UsetG f Pseq Qseq Hseq αseq J)
    (η X : ℝ) (hα : αseq Jb ≤ 1 / 4 - η) (hη2 : 2 * η ≤ 1) (hTX : T ≤ X)
    (H : ℝ) (N Xd P Q j M : ℕ) (b c : ℕ → ℂ) (ε : ℝ)
    (hM : ramRrange H N Xd j ⊆ Finset.Icc 1 M)
    (hbudget : thinBundleG T VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η) ≤ (M : ℝ)) :
    ∑ t ∈ TsetSmall H P Q j c ε 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2
      ≤ 5128 * ε ^ 2 * (M : ℝ) * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  refine (usetG_TS_branch f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2 hα0 T VJ hT hP3 hPQ
    hQT hκ30 hLL5 hVJ 𝒯 hws hsub hU η X hα hη2 hTX H N Xd P Q j M b c ε hM).trans ?_
  have hlog : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hmass : (0 : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun m _ => by positivity)
  have hε2 : (0 : ℝ) ≤ ε ^ 2 := sq_nonneg ε
  nlinarith [mul_nonneg hε2 (mul_nonneg (sub_nonneg.mpr hbudget) (mul_nonneg hlog hmass))]

/-- **GB-2a (feed) — the graded `𝒯_S` bound in the `∀ 𝒯 ⊆ A` shape** that `usetG_integral_
to_branches` consumes.  Exactly the flat `TS_feed_of_thin`'s shape, with the flat `𝒰`
replaced by `UsetG` and the `Vthin` gates as described in the header (`hVJ` + the direct
α-gate; no `hVinv`, no `hVα`).

⟦V4a⟧ finding 1 (THE SHARP `M`) is in-statement: the length `Ms j` is a per-block parameter
with `ramRrange H N Xd j ⊆ [1, Ms j]`; the consumer must feed the CO-FACTOR length
`≍ 2·Xd·e^{−j/H}`, never the dyadic `N`. -/
theorem TSG_feed_of_thin
    (fb : ℕ → ℂ) (hfb1 : ∀ n : ℕ, ‖fb n‖ ≤ 1) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
    (Jset Jb : ℕ) (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ Jset)
    (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ : ℝ) (hT : 1 < T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb) (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log T))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (η X : ℝ) (hα : αseq Jb ≤ 1 / 4 - η) (hη2 : 2 * η ≤ 1) (hTX : T ≤ X)
    (Rset : Set ℝ) (hRsub : Rset ⊆ Set.Icc (-T) T)
    (H : ℝ) (N Xd P Q : ℕ) (b c : ℕ → ℂ) (δ' : ℝ) (Ms : ℕ → ℕ)
    (hM : ∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j))
    (hbudget : ∀ j ∈ ramI H P Q,
      thinBundleG T VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
      ≤ ((Ms j : ℕ) : ℝ)) :
    ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 →
      (↑𝒯 : Set ℝ) ⊆ Rset ∩ UsetG fb Pseq Qseq Hseq αseq Jset →
      (∑ t ∈ TsetSmall H P Q j c δ' 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2)
        ≤ 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * T))
            * ∑ m ∈ Finset.Icc 1 (Ms j), ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  intro j hj 𝒯 hws hsubA
  exact usetG_TS_branch_meanvalue fb hfb1 Pseq Qseq Hseq αseq Jset Jb hJb1 hJbJ hH2 hα0
    T VJ hT hP3 hPQ hQT hκ30 hLL5 hVJ 𝒯 hws
    (fun t ht => hRsub (hsubA (Finset.mem_coe.mpr ht)).1)
    (fun t ht => (hsubA (Finset.mem_coe.mpr ht)).2) η X hα hη2 hTX
    H N Xd P Q j (Ms j) b c δ' (hM j hj) (hbudget j hj)

/-! ## §3 — GB-2b: the `𝒯_L` feed at the LOCALIZED co-factor supply -/

/-- **THE PER-BLOCK `𝒯_L` GATE BUNDLE, LOCALIZED** — `USetBalance.TLBlockGates` with the
ambient far radius `Dmax + 1` replaced by the localized transfer height
`T*(M_j, log M_j)` in the `Rbd` endpoint charge, per ⟦V6b⟧'s R1 and ⟦V7⟧'s certificate.
`Dmax` does not occur.  Every other conjunct is byte-identical to the flat bundle: the block
base, the `X₀` law `hκ30`, the kill gate, the descent anchor `k₀`, the two roundings of the
co-factor length, the loglog descent gate.

The two roundings stay separate parameters (`Mt` here, `Ms` in the `𝒯_S` feed): identifying
them would be a false byte-fit, exactly as in the flat file. -/
def TLBlockGatesLoc (cq X₀ H : ℝ) (P N Xn : ℕ) (Mt kk : ℕ → ℕ) (T L cg Cb Xg θ Rrad : ℝ)
    (j : ℕ) : Prop :=
  H ≤ (j : ℝ) ∧ 3 ≤ ramQbase H P j ∧ (ramQbase H P j : ℝ) ≤ T ∧
  30 ≤ Real.log T / Real.log (ramQbase H P j) ∧
  Real.log (ramQbase H P j) ≤ L ∧
  420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (ramQbase H P j)) ^ 2 ∧
  X₀ ≤ ((kk j : ℕ) : ℝ) ∧ Real.exp 64 ≤ ((kk j : ℕ) : ℝ) ∧
  ballMertensThreshold ≤ ((kk j : ℕ) : ℝ) ∧
  Mt j ≤ N ∧ ((kk j : ℕ) : ℝ) < ramRbot H Xn j ∧ ramRbot H Xn j ≤ ((kk j : ℕ) : ℝ) + 1 ∧
  1 < ramRbot H Xn j ∧ ramRbot H Xn j - 1 ≤ ((Mt j : ℕ) : ℝ) ∧
  ((Mt j : ℕ) : ℝ) ≤ 2 * (ramRbot H Xn j - 1) ∧ 2 * ramRbot H Xn j < ((Mt j : ℕ) : ℝ) + 3 ∧
  ((Mt j : ℕ) : ℝ) ≤ Xg ∧
  (1 / 32 - θ) * Real.log (Real.log Xg) ≤ (1 / 16) * Real.log (Real.log ((kk j : ℕ) : ℝ)) ∧
  0 ≤ cofactorMfl Xg θ ((kk j : ℕ) : ℝ) ∧
  2 / ramRbot H Xn j
    ≤ cofactorRbd cg Cb Xg θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
        (Tstar ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad / 3

/-- **GB-2b — the `𝒯_L` branch bound at the LOCALIZED supply**, uniformly over the
well-spaced witnesses: `CofactorLocal.tL_supply_discharged_local` re-shaped for `GB-1`'s
`∀ 𝒯 ⊆ A` binder.

**The `Dmax` layer is gone.**  The flat `TL_feed_of_supply` needed, on the ambient far leg,
`Rrad ≤ |t − t₁| ∧ |t − t₁| ≤ Dmax ∧ ∀ k ∈ [k₀,M_j], |t| + T*(k, log k) ≤ 3Xg`; here the
per-`t` bundle is `Rrad ≤ |t − t₁| ∧ |t| + T*(M_j, log M_j) ≤ 3Xg` — the middle conjunct
(the one that forced `Rmax ≥ Tann` into `farErr` and, by ⟦V6a⟧, refuted the grade) has no
consumer left, and the `∀ k` family collapses to its strongest member by `Tstar_mono`.

The `Vsplit` parameters (`1 ≤ V`, `V⁻¹ ≤ δ'`, `log V ≤ 100 log L`) are the ONLY `V`-data
this branch sees: the thinness level `VJ` does not appear on the `𝒯_L` side at all. -/
theorem TLG_feed_of_supply_local :
    ∃ Cq cq T₀ X₀ C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (H : ℝ), 2 ≤ H → ∀ (P Q N Xn : ℕ) (Mt kk : ℕ → ℕ) (cf : ℕ → ℂ),
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (T V L δ' : ℝ), T₀ ≤ T → 1 < T → 5 ≤ Real.log (Real.log T) → 1 ≤ V → V⁻¹ ≤ δ' →
        Real.log T ≤ L → 1 ≤ Real.log T → Real.exp 1 ≤ L → Real.log V ≤ 100 * Real.log L →
      ∀ (cg Cb Xg θ t₁ Rrad : ℝ),
        0 < cg → cg ≤ 1 / Real.exp 1 → 2 * cg < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        Real.exp 1 ≤ Xg → Real.exp 1 ≤ Real.log Xg → 0 < θ → θ ≤ 1 / 32 →
        P83 Xg θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 Xg → P ≤ Q → |t₁| ≤ Xg →
        pretDistSq (ellLin g) (costwist t₁) Xg ≤ (1 / 16) * Real.log (Real.log Xg) →
        collisionGate Xg 25 C → 0 < Rrad →
      ∀ (Rset : Set ℝ), Rset ⊆ Set.Icc (-T) T →
      ∀ j : ℕ, TLBlockGatesLoc cq X₀ H P N Xn Mt kk T L cg Cb Xg θ Rrad j →
        (∀ t ∈ Rset, Rrad ≤ |t - t₁| ∧
          |t| + Tstar ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * Xg) →
      ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 → (↑𝒯 : Set ℝ) ⊆ Rset →
        (∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N Xn P Q (ellLin g) cf j t‖ ^ 2)
          ≤ 54 * Cq * cofactorRbd cg Cb Xg θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
              (Tstar ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ^ 2
              * (H / (j : ℝ)) ^ 2 := by
  obtain ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, hmain⟩ := tL_supply_discharged_local
  refine ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, ?_⟩
  intro g hg H hH P Q N Xn Mt kk cf hcf1 T V L δ' hT₀T hT hLL5 hV1 hVδ hTL hlogT1 hLe hlogV
    cg Cb Xg θ t₁ Rrad hc0 hce hc1 hCb0 hCbound hX hLX hθ0 hθ32 hPlow hQhigh hPQ ht₁
    hrow hgate hR0 Rset hRsub j hblk hgeo 𝒯 hws h𝒯R
  obtain ⟨hHj, hB3, hBT, hκ30, hWL, hkill, hX₀k, hk₀64, hk₀th, hMN, hk₀lo, hk₀hi, hbot,
    hlow, hhigh, hMtop, hMX, hll, hMfl0, hend⟩ := hblk
  exact hmain g hg H hH P Q j N Xn (Mt j) (kk j) cf hcf1 hHj T V L δ' 𝒯 hws
    (fun t ht => hRsub (h𝒯R (Finset.mem_coe.mpr ht))) hT₀T hT hB3 hBT hκ30 hLL5 hV1 hVδ
    hTL hlogT1 hLe hWL hlogV hkill cg Cb Xg θ t₁ Rrad hc0 hce hc1 hCb0 hCbound hX₀k
    hk₀64 hk₀th hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hMX hll hX hLX hθ0 hθ32 hPlow hQhigh
    hPQ ht₁ hrow hgate hR0 hMfl0 hend
    (fun t ht => hgeo t (h𝒯R (Finset.mem_coe.mpr (tLset_subset H P Q j cf δ' 𝒯 ht))))

/-! ## §4 — GB-3: the graded exit `U`, and `hU` SUPPLIED -/

/-- **The graded exit `U`, explicit** (`hUG_exit_of_branches`).  `GB-1`'s composition at the
branch bounds of §2/§3, with the `j`-sum page (`USetBalance.block_sum_bound`, predicate-blind
— the `Σ_{j∈I} 1/j² ≤ 1/(⌊H log P⌋−1)` telescope) applied verbatim:

  `∫_{(Ann∖ball)∩𝒰G} ‖spoly‖² ≤ 4|I|·(|I|·KS + 54·C_q·R̄²·H²/(⌊H log P⌋−1)) + 2E`.

This is the `U` the graded row's `hU` binder takes. -/
theorem hUG_exit_of_branches
    (H : ℝ) (N Xd P Q : ℕ) (a b c : ℕ → ℂ)
    (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (Jset : ℕ)
    (X Tann t₁ E : ℝ) (hT : 0 ≤ Tann)
    (herr : (∫ t in (-Tann)..Tann, ‖ramErr H N Xd P Q a b c t‖ ^ 2) ≤ E)
    (δ' : ℝ) (Sb Lb : ℕ → ℝ) (KS Cq Rbar : ℝ) (hCq : 0 ≤ Cq)
    (hj₀ : 2 ≤ ⌊H * Real.log (P : ℝ)⌋₊)
    (hTS : ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 →
      (↑𝒯 : Set ℝ) ⊆ (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset →
      (∑ t ∈ TsetSmall H P Q j c δ' 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2) ≤ Sb j)
    (hTL : ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 →
      (↑𝒯 : Set ℝ) ⊆ (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset →
      (∑ t ∈ tLset H P Q j c δ' 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2) ≤ Lb j)
    (hKS : ∀ j ∈ ramI H P Q, Sb j ≤ KS)
    (hLbj : ∀ j ∈ ramI H P Q, Lb j ≤ 54 * Cq * Rbar ^ 2 * H ^ 2 * (1 / (j : ℝ) ^ 2)) :
    (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset,
        ‖spoly N a t‖ ^ 2)
      ≤ 4 * ((ramI H P Q).card : ℝ)
          * (((ramI H P Q).card : ℝ) * KS
              + 54 * Cq * Rbar ^ 2 * H ^ 2
                  / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E := by
  have hcomp := usetG_integral_to_branches H N Xd P Q a b c fb Pseq Qseq Hseq αseq Jset
    X Tann t₁ E hT herr δ' Sb Lb hTS hTL
  have hblk := block_sum_bound H P Q Sb Lb KS Cq Rbar hKS hCq hLbj hj₀
  have hcard0 : (0 : ℝ) ≤ 4 * ((ramI H P Q).card : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hblk hcard0
  linarith

/-- **GB-3 — THE GRADED `hU` SUPPLY** (`hUG_supplied`).  The graded row's `𝒰` integral,
bounded by `GB-1`'s composition fed by the two branch exits of §2 (graded thinness) and §3
(localized co-factor supply):

  `∫_{(Ann∖ball)∩𝒰G} ‖spoly N a‖² ≤ 4|I|·(|I|·KS + 54·C_q·R̄²·H²/(⌊H log P⌋−1)) + 2E`.

**THE `Tann` GATE RIDES IN-STATEMENT** (⟦V4⟧'s law): `TannGate X Tann` supplies the graded
thinness's `hκ30` at the `Jb`-block through `USetPins.kappa30_of_TannGate` at the pin
`log Q_Jb ≤ (log X)^{1/2}`.  A polylog `Tann` refuses the gate, and with it the whole
thinness row.

The gates, enumerated: MR Step 0 (`Tann ≤ X`); the graded non-degeneracy pins
(`1 ≤ Jb ≤ Jset`, `2 ≤ H_Jb`, `0 ≤ α_Jb`, `3 ≤ P_Jb ≤ Q_Jb`, `Q_Jb ≤ Tann` — the `G0`
empty-block trap); the **`Vthin`** data (`hVJ` uniformisation, `α_Jb ≤ 1/4 − η`, `2η ≤ 1`,
the sharp `Ms` with its budget); the **`Vsplit`** data (`1 ≤ V`, `V⁻¹ ≤ δ'`,
`log V ≤ 100 log L`); U-7's `t`-free gates (the `c`-generic window, the short-interval datum,
the `P83/Q83` pins, the ball datum, the collision gate); the per-block bundle
`TLBlockGatesLoc`; the LOCALIZED contour box; and the two grade budgets `KS`, `R̄`.

The far-leg geometry is DERIVED, not assumed: `Rrad ≤ seamRad X` plus `t ∉ ball` gives CASE
B's radius input — which is all that survives of the flat chain's geometry, since the
localized supply asks for no `Dmax` at all. -/
theorem hUG_supplied :
    ∃ Cq cq T₀ X₀ C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
      ∀ (g fb a cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖fb n‖ ≤ 1) →
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq Ms Mt kk : ℕ → ℕ)
        (Hseq αseq : ℕ → ℝ),
      ∀ (X Tann t₁ δ' V VJ L η cg Cb θ Rrad KS Rbar E : ℝ),
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        1 < (Qseq Jb : ℝ) → Real.log (Qseq Jb) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        -- the graded partition's non-degeneracy pins (the `G0` empty-block trap)
        1 ≤ Jb → Jb ≤ Jset → 2 ≤ Hseq Jb → 0 ≤ αseq Jb →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ Tann →
        -- `Vthin`: the graded thinness level and its α-gate (no `hVinv`, no `hVα`)
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
        αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q,
          thinBundleG Tann VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        -- `Vsplit`: the `𝒯_S ∥ 𝒯_L` level at `δ'`
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        -- U-7's `t`-free gates
        0 < cg → cg ≤ 1 / Real.exp 1 → 2 * cg < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        0 < θ → θ ≤ 1 / 32 → P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 C → 0 < Rrad → Rrad ≤ seamRad X →
        (∀ j ∈ ramI H P Q, TLBlockGatesLoc cq X₀ H P N Xd Mt kk Tann L cg Cb X θ Rrad j) →
        (∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X) →
        (∀ j ∈ ramI H P Q, 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
            * (∑ m ∈ Finset.Icc 1 (Ms j),
                ‖ramRcoeff H N Xd P Q j (ellLin g) m‖ ^ 2 / (m : ℝ) ^ 2) ≤ KS) →
        (∀ j ∈ ramI H P Q,
          cofactorRbd cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
            (Tstar ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ≤ Rbar) →
        2 ≤ ⌊H * Real.log (P : ℝ)⌋₊ →
        (∫ t in (-Tann)..Tann, ‖ramErr H N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset,
            ‖spoly N a t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (((ramI H P Q).card : ℝ) * KS
                  + 54 * Cq * Rbar ^ 2 * H ^ 2
                      / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E := by
  obtain ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, hTLfeed⟩ := TLG_feed_of_supply_local
  refine ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, ?_⟩
  intro g fb a cf hg hfb1 hcf1 H hH N Xd P Q Jset Jb Pseq Qseq Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η cg Cb θ Rrad KS Rbar E
    hX0 hXe hLXe hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hH2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hV1 hVδ hlogV
    hc0 hce hc1 hCb0 hCbound hθ0 hθ32 hPlow hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad
    hblk hbox hKS hRbdU hj₀ herr
  have hTann0 : (0 : ℝ) ≤ Tann := by linarith
  have hκ30 : 30 ≤ Real.log Tann / Real.log (Qseq Jb) :=
    kappa30_of_TannGate X Tann (Qseq Jb) hQ1 hQpin hTgate
  have hRsub : (seamAnn X Tann \ seamBall X t₁) ⊆ Set.Icc (-Tann) Tann :=
    fun _ ht => seamAnn_subset_Icc X Tann ht.1
  -- the `𝒯_S` feed at the GRADED thinness
  have hTSfeed := TSG_feed_of_thin fb hfb1 Pseq Qseq Hseq αseq Jset Jb hJb1 hJbJ hH2 hα0
    Tann VJ hT1 hP3 hPQ hQT hκ30 hLL5 hVJ η X hα hη2 hTX
    (seamAnn X Tann \ seamBall X t₁) hRsub H N Xd P Q (ellLin g) cf δ' Ms hMs hbudget
  -- the `𝒯_L` feed at the LOCALIZED supply; only the far-leg LOWER gate is derived
  have hTLj : ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 →
      (↑𝒯 : Set ℝ) ⊆ (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset →
      (∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N Xd P Q (ellLin g) cf j t‖ ^ 2)
        ≤ 54 * Cq * cofactorRbd cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
            (Tstar ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ^ 2
            * (H / (j : ℝ)) ^ 2 := by
    intro j hj 𝒯 hws h𝒯A
    refine hTLfeed g hg H hH P Q N Xd Mt kk cf hcf1 Tann V L δ' hT₀T hT1 hLL5 hV1 hVδ hTLle
      hlogT1 hLe hlogV cg Cb X θ t₁ Rrad hc0 hce hc1 hCb0 hCbound hXe hLXe hθ0 hθ32
      hPlow hQhigh hPQ83 ht₁ hrow hcoll hR0 (seamAnn X Tann \ seamBall X t₁) hRsub j
      (hblk j hj) ?_ 𝒯 hws (fun x hx => (h𝒯A hx).1)
    intro t ht
    have hTabs : |t| ≤ Tann := ht.1.2
    have hnot : ¬ (|t - t₁| ≤ seamRad X) := ht.2
    exact ⟨le_trans hRrad (le_of_lt (not_le.mp hnot)), hbox j hj t hTabs⟩
  refine hUG_exit_of_branches H N Xd P Q a (ellLin g) cf fb Pseq Qseq Hseq αseq Jset
    X Tann t₁ E hTann0 herr δ'
    (fun j => 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
      * ∑ m ∈ Finset.Icc 1 (Ms j), ‖ramRcoeff H N Xd P Q j (ellLin g) m‖ ^ 2 / (m : ℝ) ^ 2)
    (fun j => 54 * Cq * cofactorRbd cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
      (Tstar ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ^ 2 * (H / (j : ℝ)) ^ 2)
    KS Cq Rbar (le_of_lt hCq) hj₀ (fun j hj 𝒯 hws h𝒯A => hTSfeed j hj 𝒯 hws h𝒯A) hTLj hKS ?_
  intro j hj
  have hk64 := (hblk j hj).2.2.2.2.2.2.2.1
  have h65 : (65 : ℝ) ≤ ((kk j : ℕ) : ℝ) := by
    linarith [Real.add_one_le_exp (64 : ℝ), hk64]
  have hk1 : (1 : ℝ) ≤ ((kk j : ℕ) : ℝ) := by linarith
  exact tL_block_weight Cq H _ Rbar j (le_of_lt hCq)
    (cofactorRbd_nonneg hc1 hCb0 hk1) (hRbdU j hj)

/-! ## §5 — GB-3: the balance at the RATIFIED pin `θ₂₉₃` -/

/-- **GB-3 — THE GRADED BALANCE** (`hUG_balance`).  `USetBalance.hU_balance` is
predicate-blind (it is arithmetic on the two legs at the ratified `θ₂₉₃ = ρ₂₉₃/3` pin), so
the graded balance is that theorem read at the graded `𝒰`:

  `∫_{(Ann∖ball)∩𝒰G} ‖spoly‖² ≤ 2·(Tann/X + 1)·(log X)^{−θ₂₉₃+ε}`,

from the block leg at `(log X)^{5θ−2ρ}` and Lemma 12's error leg at
`(Tann/X+1)(log X)^{−θ+ε}`.  `TannGate X Tann` rides here too and is what makes `Tann`
positive, hence `0 ≤ Tann/X` — the only nonnegativity the balance needs. -/
theorem hUG_balance
    (a fb : ℕ → ℂ) (N : ℕ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (Jset : ℕ)
    (X Tann t₁ ε Umain Urem : ℝ) (hε : 0 ≤ ε) (hL : 1 ≤ Real.log X) (hX0 : 0 < X)
    (hTgate : TannGate X Tann)
    (hUint : (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset,
        ‖spoly N a t‖ ^ 2) ≤ Umain + Urem)
    (hmain : Umain ≤ (Real.log X) ^ (5 * theta293 - 2 * rho293))
    (hrem : Urem ≤ (Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) :
    (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset,
        ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) :=
  hU_balance X Tann ε Umain Urem _ hε hL hX0 hTgate hUint hmain hrem

/-- **The graded balanced exit CLEARS THE DOOR.**  At any `o(1)` with `ε ≤ 1/1000` the
exponent `−θ₂₉₃ + ε` is at most `−1/500` — the door's floor `c₀ ≥ 1/500`, cleared with the
ratified margin `1.7067×` (`CofactorDist.exit_margin_293`). -/
theorem hUG_balance_beats_door
    (a fb : ℕ → ℂ) (N : ℕ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (Jset : ℕ)
    (X Tann t₁ ε : ℝ) (hε : ε ≤ 1 / 1000) (hL : 1 ≤ Real.log X) (hX0 : 0 < X)
    (hTgate : TannGate X Tann)
    (hUint : (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset,
        ‖spoly N a t‖ ^ 2) ≤ 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε))) :
    (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset,
        ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((Tann / X + 1) * (Real.log X) ^ (-(1 : ℝ) / 500)) :=
  hU_balance_beats_door X Tann ε _ hε hL hX0 hTgate hUint

/-! ## §6 — GB-4: the graded row with `hU` GONE -/

/-- **GB-4 — THE GRADED `hU` DISCHARGED** (`hUG_discharged`).
`SeamGraded.prop_A3_T1_row_split_weightedG` with its `hU` binder supplied by §4: the graded
seam row now carries only the ball leg, the graded `𝒯`-leg (§8.1+§8.2 at the graded
partition — `G2`–`G5`, out of scope here) and the EXPLICIT `U`.

**The compile is the certificate** that §4's exit byte-fits the graded row's `hU` slot: the
set `(seamAnn X Tann ∖ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset`, the integrand
`‖spoly N a t‖^2`, and the direction of the inequality are the row's, verbatim.  As in the
flat chain the plug-point is the row at a FREE `t₁` (not a station that produces one): §4's
exit needs `t₁` as a parameter, since the far-leg radius `Rrad ≤ |t − t₁|` and the ball datum
`pretDistSq … (costwist t₁)` are stated about the same `t₁` the `𝒰` integral is centred on. -/
theorem hUG_discharged :
    ∃ Cq cq T₀ X₀ C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
      ∀ (g fb a cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖fb n‖ ≤ 1) →
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq Ms Mt kk : ℕ → ℕ)
        (Hseq αseq : ℕ → ℝ),
      ∀ (X Tann t₁ δ' V VJ L η cg Cb θ Rrad KS Rbar E S : ℝ),
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        1 < (Qseq Jb : ℝ) → Real.log (Qseq Jb) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        1 ≤ Jb → Jb ≤ Jset → 2 ≤ Hseq Jb → 0 ≤ αseq Jb →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ Tann →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
        αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q,
          thinBundleG Tann VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 < cg → cg ≤ 1 / Real.exp 1 → 2 * cg < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        0 < θ → θ ≤ 1 / 32 → P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 C → 0 < Rrad → Rrad ≤ seamRad X →
        (∀ j ∈ ramI H P Q, TLBlockGatesLoc cq X₀ H P N Xd Mt kk Tann L cg Cb X θ Rrad j) →
        (∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X) →
        (∀ j ∈ ramI H P Q, 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
            * (∑ m ∈ Finset.Icc 1 (Ms j),
                ‖ramRcoeff H N Xd P Q j (ellLin g) m‖ ^ 2 / (m : ℝ) ^ 2) ≤ KS) →
        (∀ j ∈ ramI H P Q,
          cofactorRbd cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
            (Tstar ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ≤ Rbar) →
        2 ≤ ⌊H * Real.log (P : ℝ)⌋₊ →
        (∫ t in (-Tann)..Tann, ‖ramErr H N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        -- the graded row's own frame (`SeamGraded`:315), `hU` ABSENT
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                ∩ seamTtotG fb Pseq Qseq Hseq αseq Jset, ‖spoly N a t‖ ^ 2)
            + (4 * ((ramI H P Q).card : ℝ)
                * (((ramI H P Q).card : ℝ) * KS
                    + 54 * Cq * Rbar ^ 2 * H ^ 2
                        / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E) := by
  obtain ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, hsup⟩ := hUG_supplied
  refine ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, ?_⟩
  intro g fb a cf hg hfb1 hcf1 H hH N Xd P Q Jset Jb Pseq Qseq Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η cg Cb θ Rrad KS Rbar E S
    hX0 hXe hLXe hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hH2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hV1 hVδ hlogV
    hc0 hce hc1 hCb0 hCbound hθ0 hθ32 hPlow hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad
    hblk hbox hKS hRbdU hj₀ herr hXN hN2 hsupp hSup
  have hU := hsup g fb a cf hg hfb1 hcf1 H hH N Xd P Q Jset Jb Pseq Qseq Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η cg Cb θ Rrad KS Rbar E
    hX0 hXe hLXe hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hH2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hV1 hVδ hlogV
    hc0 hce hc1 hCb0 hCbound hθ0 hθ32 hPlow hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad
    hblk hbox hKS hRbdU hj₀ herr
  have hLX : (0 : ℝ) ≤ Real.log X := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  exact prop_A3_T1_row_split_weightedG a N fb Pseq Qseq Hseq αseq Jset X Tann t₁ S _ hLX
    (by linarith) hX0 hXN hN2 hsupp hSup hU

end Salt.MR
