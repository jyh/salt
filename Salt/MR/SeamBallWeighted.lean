/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SeamSplit
import Salt.MR.SupF

/-!
# SeamBallWeighted — the WEIGHTED ball leg (`HSUP-REPAIR`)

The repair wave of `docs/exploration/hsup-design.md`'s ⟦SCOPE VERDICT + AMENDMENT V1⟧
(HSUP-SCOPE, 2026-07-24) and the flags entry *"ball_leg_of_sup divergence + the ball-centre
defect"*.  Everything here is ADDITIVE: the landed `SeamSplit` stones stay untouched as
heritage; this file supplies the honest replacements alongside them.

## The defect being repaired

`SeamSplit.ball_leg_of_sup` (:362) bounds the ball leg by `measure × sup²`, i.e.
`2r·(2S)²` with `r = seamRad X = (log X)^{1/46}`.  HSUP-SCOPE's numerics: at the live band
`1 ≤ M < (1/16)·loglog X` the `r`-factor DIVERGES against the `e^{−2cM}` gain (the exit is
`(log X)^{+0.0395}` at the top of the band).  MRT's Appendix A.7 never takes a sup: the
renormalisation factor `1/(1+|t−t₁|)` stays INSIDE the integral, and the ball leg is bounded
by an absolute multiple of `S²` with NO `r`-factor at all.

## What lands here

* `integral_ballWeight_le` [§1] — the honest Cauchy page:
  `∫_{−r}^{r} (1+|u|)^{−2} du ≤ 2` (two halves of `∫_0^∞ (1+u)^{−2} = 1`), PROPER interval
  integrals only (no improper/`Ioi` machinery): the half-line antiderivative is delivered by
  `integral_zpow` after the shift `v = 1+u`.  `integral_ballWeight_centred_le` is the
  translate `∫_{t₁−r}^{t₁+r} (1+|t−t₁|)^{−2} dt ≤ 2`.
* `ball_leg_of_sup_weighted` [W1] — THE REPAIR.  Under the WEIGHTED binder
  `hSup′ : ‖A_t(m)‖ ≤ S·m/(1+|t−t₁|)` (annulus-restricted per H-0: the two window
  hypotheses `seamT0 X ≤ |t|`, `|t| ≤ T` come free from the integration domain, so the
  binder is window-legal), the ball leg is
  `∫_{Ann ∩ ball} ‖spoly‖² ≤ 8·S²` — the honest constant of our page (MRT's grade is `16S²`;
  ours is a factor 2 better because the landed Abel exit is `2S`, not `3S`), with NO
  `r`-factor.  `spoly_abel_sup` is reused UNCHANGED: it is a per-`t` statement, so it is
  applied at each `t` with `S_t := S/(1+|t−t₁|)`.
* `prop_A3_T1_row_split_weighted` [W2] — the seam row rebuilt on the weighted leg, with the
  ball centre `t₁` a FREE parameter (defect #3: the honest centre is the GLOBAL minimizer of
  `M(f;X)` over `|t| ≤ X`, NOT the `M_range` near-minimizer the landed row produces; the
  centre semantics now live in the consumer, so no `∃t₁`/`M_range` clause appears here).
  All the partition machinery (`annulus_ball_far_split`, `seam_TU_split`) is landed and
  already `t₁`-free, so the repair is a re-assembly, not a re-proof.
* `sigma_cutoff_pretentious_gen` / `_half` / `_of_gen` [W3, H-2] — the σ-cutoff at a GENERAL
  exponent `c` with `2c < 1`.  `SupF.sigma_cutoff_pretentious` (:1005) is the `c = 1/e`
  instance; V1's defect #1 (the (A.13)/(A.14) square root halves the pointwise exponent)
  needs the `c = 1/(2e)` instance, which is `_half`.  Landing the general form (rather than
  the mechanical clone) means every future re-grade is one instantiation, not a new proof;
  `_of_gen` re-derives the landed `c = 1/e` statement from it as the cross-check.

## What is NOT repaired here

The named binder `hSup′` still has no landed supply — that is H-4 (GS[10] Lemma 7.1, the
campaign's one `D`-node, un-retracted by V1's defect #4) plus H-5/H-6/H-7.  `hU` is
unchanged (the §8.3 interior).  Nothing in this file claims a supply it has not exhibited.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2, §8; MRT v3 Appendix A.6/A.7.
-/

noncomputable section

namespace Salt.MR

open MeasureTheory

/-! ## §1 — the Cauchy weight `∫_ℝ (1+|u|)^{−2} du = 2`

The only analytic input the weighted ball leg needs.  Kept PROPER: the ball is compact, so
the whole page is two interval integrals over `[0,r]` and `[−r,0]`, each `≤ 1` uniformly in
`r` — no improper integral, no `Ioi` integrability side-condition. -/

/-- The Cauchy-type weight `u ↦ (1+|u|)^{−2}` is continuous: its denominator is `≥ 1`. -/
lemma continuous_ballWeight : Continuous fun u : ℝ => 1 / (1 + |u|) ^ 2 :=
  continuous_const.div ((continuous_const.add continuous_abs).pow 2) fun _ => by positivity

/-- The weight is nonnegative. -/
lemma ballWeight_nonneg (u : ℝ) : 0 ≤ 1 / (1 + |u|) ^ 2 := by positivity

/-- **The right half** — `∫_0^r (1+|u|)^{−2} du = 1 − (1+r)^{−1} ≤ 1`.  On `[0,r]` the weight
is `(1+u)^{−2}`; the shift `v = 1+u` (`integral_comp_add_left`) turns it into `∫_1^{1+r}
v^{−2}`, whose closed form is `integral_zpow`'s. -/
lemma integral_ballWeight_right_le {r : ℝ} (hr : 0 ≤ r) :
    (∫ u in (0 : ℝ)..r, 1 / (1 + |u|) ^ 2) ≤ 1 := by
  have hz2 : ∀ v : ℝ, v ^ (2 : ℤ) = v ^ 2 := fun v => by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from by norm_num, zpow_natCast]
  have heq : Set.EqOn (fun u : ℝ => 1 / (1 + |u|) ^ 2)
      (fun u : ℝ => (fun v : ℝ => v ^ (-2 : ℤ)) (1 + u)) (Set.uIcc 0 r) := by
    intro u hu
    rw [Set.uIcc_of_le hr, Set.mem_Icc] at hu
    simp only [abs_of_nonneg hu.1]
    rw [zpow_neg, hz2, one_div]
  rw [intervalIntegral.integral_congr heq,
    intervalIntegral.integral_comp_add_left (fun v : ℝ => v ^ (-2 : ℤ)) 1]
  have hnot : (0 : ℝ) ∉ Set.uIcc (1 + 0 : ℝ) (1 + r) := by
    rw [Set.uIcc_of_le (by linarith), Set.mem_Icc]
    rintro ⟨h1, -⟩
    linarith
  rw [integral_zpow (Or.inr ⟨by decide, hnot⟩)]
  have e1 : ((1 : ℝ) + r) ^ (-2 + 1 : ℤ) = (1 + r)⁻¹ := by norm_num
  have e2 : ((1 : ℝ) + 0) ^ (-2 + 1 : ℤ) = 1 := by norm_num
  rw [e1, e2, show (((-2 : ℤ) : ℝ)) + 1 = -1 from by norm_num, div_neg, div_one]
  have hinv : (0 : ℝ) ≤ (1 + r)⁻¹ := by positivity
  linarith

/-- **The left half** — the weight is even, so `∫_{−r}^0 = ∫_0^r ≤ 1`
(`integral_comp_neg` + `abs_neg`). -/
lemma integral_ballWeight_left_le {r : ℝ} (hr : 0 ≤ r) :
    (∫ u in (-r)..(0 : ℝ), 1 / (1 + |u|) ^ 2) ≤ 1 := by
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := r)
    (fun u : ℝ => 1 / (1 + |u|) ^ 2)
  simp only [abs_neg, neg_zero] at h
  rw [← h]
  exact integral_ballWeight_right_le hr

/-- **The Cauchy page** — `∫_{−r}^{r} (1+|u|)^{−2} du ≤ 2`, uniformly in `r ≥ 0`.  THIS is
what replaces the divergent `measure × sup²`: the `r`-factor of the crude leg is exactly the
mass the weight kills. -/
lemma integral_ballWeight_le {r : ℝ} (hr : 0 ≤ r) :
    (∫ u in (-r)..r, 1 / (1 + |u|) ^ 2) ≤ 2 := by
  have hsplit : (∫ u in (-r)..(0 : ℝ), 1 / (1 + |u|) ^ 2)
        + (∫ u in (0 : ℝ)..r, 1 / (1 + |u|) ^ 2)
      = ∫ u in (-r)..r, 1 / (1 + |u|) ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (continuous_ballWeight.intervalIntegrable _ _)
      (continuous_ballWeight.intervalIntegrable _ _)
  linarith [integral_ballWeight_left_le hr, integral_ballWeight_right_le hr]

/-- **The centred page** — the translate of `integral_ballWeight_le` to the ball about `t₁`:
`∫_{t₁−r}^{t₁+r} (1+|t−t₁|)^{−2} dt ≤ 2` (`integral_comp_sub_right`). -/
lemma integral_ballWeight_centred_le (t₁ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ t in (t₁ - r)..(t₁ + r), 1 / (1 + |t - t₁|) ^ 2) ≤ 2 := by
  have hcov : (∫ t in (t₁ - r)..(t₁ + r), 1 / (1 + |t - t₁|) ^ 2)
      = ∫ u in (-r)..r, 1 / (1 + |u|) ^ 2 := by
    have h := intervalIntegral.integral_comp_sub_right (a := t₁ - r) (b := t₁ + r)
      (fun u : ℝ => 1 / (1 + |u|) ^ 2) t₁
    rw [show t₁ - r - t₁ = -r from by ring, show t₁ + r - t₁ = r from by ring] at h
    exact h
  rw [hcov]
  exact integral_ballWeight_le hr

/-! ## §2 — W1: the WEIGHTED ball leg -/

/-- **W1 — the weighted ball leg (`ball_leg_of_sup_weighted`).**  The honest replacement for
`SeamSplit.ball_leg_of_sup`:

  `∫_{Ann ∩ ball} ‖spoly N a t‖² ≤ 8·S²`   — NO `r`-factor.

**The binder.**  `hSup` carries MRT A.7's renormalisation INSIDE:
`‖A_t(m)‖ ≤ S·m/(1+|t−t₁|)`, and it is restricted to the annulus (`seamT0 X ≤ |t|`,
`|t| ≤ T`) — HSUP-SCOPE's H-0 free win, since the integration domain `Ann ∩ ball` supplies
both hypotheses at every point where the binder is used, and the supply side (the pointwise
Halász bound) is only ever window-legal.

**The page.**  Per `t`, the landed `spoly_abel_sup` (UNCHANGED — it is a per-`t` statement,
so it is instantiated at `S_t := S/(1+|t−t₁|)`) gives `‖spoly N a t‖ ≤ 2S/(1+|t−t₁|)`, whence
`‖spoly N a t‖² ≤ (2S)²·(1+|t−t₁|)^{−2}`.  Monotonicity into the full ball and the Cauchy
page `∫ (1+|u|)^{−2} ≤ 2` then give `(2S)²·2 = 8S²`.  (MRT's A.7 grade is `16S²`; ours is
better by the factor 2 the landed Abel constant already bought.) -/
theorem ball_leg_of_sup_weighted {N : ℕ} {a : ℕ → ℂ} {X T t₁ S : ℝ}
    (hX : 0 < X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X) (hT : 0 ≤ T)
    (hL : 0 ≤ Real.log X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hSup : ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - t₁| ≤ seamRad X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) :
    (∫ t in seamAnn X T ∩ seamBall X t₁, ‖spoly N a t‖ ^ 2) ≤ 8 * S ^ 2 := by
  have hrad : (0 : ℝ) ≤ seamRad X := seamRad_nonneg hL
  have hcont : Continuous fun t : ℝ => ‖spoly N a t‖ ^ 2 :=
    (continuous_spoly N a).norm.pow 2
  have hgcont : Continuous fun t : ℝ => (2 * S) ^ 2 * (1 / (1 + |t - t₁|) ^ 2) := by
    refine continuous_const.mul (continuous_const.div ?_ fun _ => by positivity)
    exact (continuous_const.add (continuous_id.sub continuous_const).abs).pow 2
  have hmeas : MeasurableSet (seamAnn X T ∩ seamBall X t₁) :=
    (measurableSet_seamAnn X T).inter (measurableSet_seamBall X t₁)
  have hsub : seamAnn X T ∩ seamBall X t₁ ⊆ Set.Icc (-T) T :=
    fun _ ht => seamAnn_subset_Icc X T ht.1
  have hint : IntegrableOn (fun t : ℝ => ‖spoly N a t‖ ^ 2)
      (seamAnn X T ∩ seamBall X t₁) volume :=
    integrableOn_of_continuous_subset_Icc hcont hT hmeas hsub
  have hgint : IntegrableOn (fun t : ℝ => (2 * S) ^ 2 * (1 / (1 + |t - t₁|) ^ 2))
      (seamAnn X T ∩ seamBall X t₁) volume :=
    integrableOn_of_continuous_subset_Icc hgcont hT hmeas hsub
  have hgball : IntegrableOn (fun t : ℝ => (2 * S) ^ 2 * (1 / (1 + |t - t₁|) ^ 2))
      (seamBall X t₁) volume := by
    rw [seamBall_eq_Icc]
    exact hgcont.integrableOn_Icc
  -- the pointwise weighted bound, through the landed (per-`t`) Abel inequality
  have hdom : ∀ t ∈ seamAnn X T ∩ seamBall X t₁,
      ‖spoly N a t‖ ^ 2 ≤ (2 * S) ^ 2 * (1 / (1 + |t - t₁|) ^ 2) := by
    intro t ht
    have hd : (0 : ℝ) < 1 + |t - t₁| := by positivity
    have hd' : (1 : ℝ) + |t - t₁| ≠ 0 := ne_of_gt hd
    have hA : ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ (S / (1 + |t - t₁|)) * m := by
      intro m hm
      have h := hSup t ht.1.1 ht.1.2 ht.2 m hm
      rwa [div_mul_eq_mul_div]
    have hpt : ‖spoly N a t‖ ≤ 2 * (S / (1 + |t - t₁|)) :=
      spoly_abel_sup hX hXN hN2 hsupp hA
    calc ‖spoly N a t‖ ^ 2 ≤ (2 * (S / (1 + |t - t₁|))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hpt 2
      _ = (2 * S) ^ 2 * (1 / (1 + |t - t₁|) ^ 2) := by field_simp
  -- the ball integral of the majorant
  have hballint : (∫ t in seamBall X t₁, (2 * S) ^ 2 * (1 / (1 + |t - t₁|) ^ 2))
      ≤ 8 * S ^ 2 := by
    rw [seamBall_eq_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : t₁ - seamRad X ≤ t₁ + seamRad X),
      intervalIntegral.integral_const_mul]
    calc (2 * S) ^ 2 * ∫ t in (t₁ - seamRad X)..(t₁ + seamRad X), 1 / (1 + |t - t₁|) ^ 2
        ≤ (2 * S) ^ 2 * 2 :=
          mul_le_mul_of_nonneg_left (integral_ballWeight_centred_le t₁ hrad) (sq_nonneg _)
      _ = 8 * S ^ 2 := by ring
  calc (∫ t in seamAnn X T ∩ seamBall X t₁, ‖spoly N a t‖ ^ 2)
      ≤ ∫ t in seamAnn X T ∩ seamBall X t₁, (2 * S) ^ 2 * (1 / (1 + |t - t₁|) ^ 2) :=
        setIntegral_mono_on hint hgint hmeas hdom
    _ ≤ ∫ t in seamBall X t₁, (2 * S) ^ 2 * (1 / (1 + |t - t₁|) ^ 2) :=
        setIntegral_mono_set hgball
          (Filter.Eventually.of_forall fun t => by positivity)
          (HasSubset.Subset.eventuallyLE Set.inter_subset_right)
    _ ≤ 8 * S ^ 2 := hballint

/-! ## §3 — W2: the seam row on the weighted ball leg -/

/-- **W2 — THE REPAIRED SEAM ROW (`prop_A3_T1_row_split_weighted`).**  `SeamSplit`'s
`prop_A3_T1_row_split` with BOTH V1 defects repaired, additively:

  `∫_{Ann} ‖spoly N a t‖² ≤ 8·S² + ∫_{(Ann\ball) ∩ 𝒯tot} ‖spoly N a t‖² + U`.

**(i) the ball leg** is the weighted `8S²` (no `r`-factor: the landed row's `2r(2S)²` diverges
at every live `M` — flags 2026-07-24).

**(ii) the centre `t₁` is a FREE parameter.**  The landed row PRODUCES `t₁` as a near-minimizer
of `M_range`'s window infimum; defect #3 says that is the wrong centre (counterexample `f ≡ 1`:
`M_range ≈ loglog X` while the true bound is `(log X)^{−1/15}`-grade only — the honest centre is
the GLOBAL minimizer of `M(f;X)` over `|t| ≤ X`, which for `f ≡ 1` sits BELOW `T₀`, making
`Ann ∩ ball = ∅` and the ball leg zero, exactly MRT's architecture: `M(f;X)` on `𝒯₀`,
`M_range` on `𝒯₁`).  So the `∃t₁`/`pretDistSq < M_range + 1` clause is DROPPED here and the
centre semantics move to the consumer.  No window fact about `t₁` itself is needed: the
weighted leg never uses one.  Consequently the `g`/`t₀` seam datum does not appear at all.

**(iii) the binder `hSup` is annulus-restricted** (H-0), so it is window-legal: the two extra
hypotheses are supplied free by the integration domain.

The partition machinery is the landed one verbatim — `annulus_ball_far_split` and
`seam_TU_split` are already stated at a free `t₁` — so this is a re-assembly, not a re-proof.
`hU` is unchanged (the §8.3 interior); `hSup` remains the open frontier (H-4/H-5/H-6/H-7). -/
theorem prop_A3_T1_row_split_weighted
    (a : ℕ → ℂ) (N : ℕ)
    (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (Jb : ℕ)
    (X T t₁ S U : ℝ)
    (hL : 0 ≤ Real.log X) (hT : 0 ≤ T)
    (hX : 0 < X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hSup : ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - t₁| ≤ seamRad X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|))
    (hU : (∫ t in (seamAnn X T \ seamBall X t₁) ∩ Uset fb Pseq Qseq δ Jb,
        ‖spoly N a t‖ ^ 2) ≤ U) :
    (∫ t in seamAnn X T, ‖spoly N a t‖ ^ 2)
      ≤ 8 * S ^ 2
        + (∫ t in (seamAnn X T \ seamBall X t₁) ∩ seamTtot fb Pseq Qseq δ Jb,
            ‖spoly N a t‖ ^ 2) + U := by
  have hcont : Continuous fun t : ℝ => ‖spoly N a t‖ ^ 2 :=
    (continuous_spoly N a).norm.pow 2
  have hR : MeasurableSet (seamAnn X T \ seamBall X t₁) :=
    (measurableSet_seamAnn X T).diff (measurableSet_seamBall X t₁)
  have hRsub : seamAnn X T \ seamBall X t₁ ⊆ Set.Icc (-T) T :=
    fun _ ht => seamAnn_subset_Icc X T ht.1
  -- 1. the ball / far split (landed, `t₁`-free)
  have h1 := annulus_ball_far_split (F := fun t : ℝ => ‖spoly N a t‖ ^ 2) hcont X T t₁ hT
  -- 2. the WEIGHTED ball leg
  have h2 := ball_leg_of_sup_weighted hX hXN hN2 hT hL hsupp hSup
  -- 3. the `𝒯tot / 𝒰` split of the far part (landed, `t₁`-free)
  have h3 := seam_TU_split (f := fb) (Pseq := Pseq) (Qseq := Qseq) (δ := δ) (J := Jb)
    (F := fun t : ℝ => ‖spoly N a t‖ ^ 2) hcont hT hR hRsub
  linarith [h1, h2, h3, hU]

/-- **W2′ — the crude far leg (`prop_A3_T1_row_split_weighted_crude`).**  The weighted row with
the `𝒯`-leg collapsed by the landed `far_leg_collapse` (ONE monotonicity, never a `Σⱼ` of `J`
copies — catch #253).  Deliberately crude, as in the landed `_crude` clone: at that collapse
the statement no longer beats the trivial `Ann ⊆ [-T,T]` monotonicity; it is the freeze's
stated exit SHAPE, kept so a consumer can read the row's `T`-structure off one line. -/
theorem prop_A3_T1_row_split_weighted_crude
    (a : ℕ → ℂ) (N : ℕ)
    (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (Jb : ℕ)
    (X T t₁ S U : ℝ)
    (hL : 0 ≤ Real.log X) (hT : 0 ≤ T)
    (hX : 0 < X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hSup : ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - t₁| ≤ seamRad X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|))
    (hU : (∫ t in (seamAnn X T \ seamBall X t₁) ∩ Uset fb Pseq Qseq δ Jb,
        ‖spoly N a t‖ ^ 2) ≤ U) :
    (∫ t in seamAnn X T, ‖spoly N a t‖ ^ 2)
      ≤ 8 * S ^ 2 + (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2) + U := by
  have hcont : Continuous fun t : ℝ => ‖spoly N a t‖ ^ 2 :=
    (continuous_spoly N a).norm.pow 2
  have hRsub : seamAnn X T \ seamBall X t₁ ⊆ Set.Icc (-T) T :=
    fun _ ht => seamAnn_subset_Icc X T ht.1
  have hfar : (∫ t in (seamAnn X T \ seamBall X t₁) ∩ seamTtot fb Pseq Qseq δ Jb,
      ‖spoly N a t‖ ^ 2) ≤ ∫ t in (-T)..T, ‖spoly N a t‖ ^ 2 :=
    far_leg_collapse hcont (fun _ => sq_nonneg _) hT (fun _ ht => hRsub ht.1)
  have hrow := prop_A3_T1_row_split_weighted a N fb Pseq Qseq δ Jb X T t₁ S U
    hL hT hX hXN hN2 hsupp hSup hU
  linarith [hrow, hfar]

/-! ## §4 — W3 (H-2): the σ-cutoff at a general exponent -/

/-- **W3 — the flat-regime pretentious σ-cutoff at a GENERAL exponent `c`**
(`sigma_cutoff_pretentious_gen`).  For `0 < c` with `2c < 1`, `L ≥ 3`, `M, C ≥ 0` and any
upper limit `b ≥ 1/L`:

  `∫_{1/L}^{b} σ^{−2}·exp(−c(M − 2log(σL) − C)) dσ ≤ (e^{cC}/(1−2c))·e^{−cM}·L`.

The page is `SupF.sigma_cutoff_pretentious`'s, with the exponent freed: the integrand is
`K·σ^{2c−2}` with `K = e^{−cM}e^{cC}L^{2c}`, `integral_rpow` gives the closed antiderivative
(the hypothesis `2c ≠ 1` is exactly `2c − 2 ≠ −1`), and `2c − 1 < 0` both kills the
top-endpoint term and turns `L^{2c}·(1/L)^{2c−1}` into `L`.

**Why general.**  V1's defect #1: the (A.13)/(A.14) square root HALVES the pointwise exponent,
so the landed `c = 1/e` arm must be re-run at `c = 1/(2e)` (`_half` below).  Landing the
general form makes every future re-grade an instantiation rather than a new proof — the
convergence condition `2c < 1` is the honest boundary of the method (at `2c = 1` the σ-integral
diverges logarithmically). -/
theorem sigma_cutoff_pretentious_gen {c L M C b : ℝ} (hc0 : 0 < c) (hc1 : 2 * c < 1)
    (hL : 3 ≤ L) (_hM : 0 ≤ M) (_hC : 0 ≤ C) (hb : 1 / L ≤ b) :
    (∫ σ in (1 / L)..b, (1 / σ ^ 2) * Real.exp (-c * (M - 2 * Real.log (σ * L) - C)))
      ≤ (Real.exp (c * C) / (1 - 2 * c)) * Real.exp (-(c * M)) * L := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le hLinv0 hb
  have hsneg : (2 * c - 1 : ℝ) < 0 := by linarith
  have hσsq : ∀ σ : ℝ, σ ^ (2 : ℝ) = σ ^ 2 := fun σ => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  set K : ℝ := Real.exp (-(c * M)) * Real.exp (c * C) * L ^ (2 * c : ℝ) with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  -- pointwise integrand identity for `σ > 0`
  have hpoint0 : ∀ σ : ℝ, 0 < σ →
      (1 / σ ^ 2) * Real.exp (-c * (M - 2 * Real.log (σ * L) - C))
        = K * σ ^ (2 * c - 2 : ℝ) := by
    intro σ hσpos
    have hσL : 0 < σ * L := mul_pos hσpos hLpos
    rw [show -c * (M - 2 * Real.log (σ * L) - C)
          = -(c * M) + Real.log (σ * L) * (2 * c) + c * C from by ring,
      Real.exp_add, Real.exp_add, ← Real.rpow_def_of_pos hσL,
      Real.mul_rpow hσpos.le hLpos.le, hKdef,
      show σ ^ (2 * c - 2 : ℝ) = σ ^ (2 * c : ℝ) * (1 / σ ^ 2) from by
        rw [Real.rpow_sub hσpos, hσsq σ, div_eq_mul_one_div]]
    ring
  have hpoint : Set.EqOn
      (fun σ => (1 / σ ^ 2) * Real.exp (-c * (M - 2 * Real.log (σ * L) - C)))
      (fun σ => K * σ ^ (2 * c - 2 : ℝ)) (Set.uIcc (1 / L) b) := by
    intro σ hσ
    rw [Set.uIcc_of_le hb, Set.mem_Icc] at hσ
    exact hpoint0 σ (lt_of_lt_of_le hLinv0 hσ.1)
  -- integrate the rpow monomial
  rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by intro h; linarith, by
      rw [Set.uIcc_of_le hb, Set.mem_Icc]; rintro ⟨h1, -⟩; linarith⟩),
    show (2 * c - 2 : ℝ) + 1 = 2 * c - 1 from by ring]
  -- the closed-form bound
  have hbs : (0 : ℝ) < b ^ (2 * c - 1 : ℝ) := Real.rpow_pos_of_pos hbpos _
  have hLL : L ^ (2 * c : ℝ) * (1 / L) ^ (2 * c - 1 : ℝ) = L := by
    rw [one_div, Real.inv_rpow hLpos.le, ← Real.rpow_neg hLpos.le, ← Real.rpow_add hLpos,
      show (2 * c : ℝ) + -(2 * c - 1) = 1 from by ring, Real.rpow_one]
  have hKL : K * (1 / L) ^ (2 * c - 1 : ℝ)
      = Real.exp (-(c * M)) * Real.exp (c * C) * L := by
    rw [hKdef, mul_assoc, hLL]
  have hstep : (b ^ (2 * c - 1 : ℝ) - (1 / L) ^ (2 * c - 1 : ℝ)) / (2 * c - 1)
      ≤ (1 / L) ^ (2 * c - 1 : ℝ) / (1 - 2 * c) := by
    rw [show (1 : ℝ) - 2 * c = -(2 * c - 1) from by ring, div_neg, sub_div]
    have hAs : b ^ (2 * c - 1 : ℝ) / (2 * c - 1) ≤ 0 :=
      le_of_lt (div_neg_of_pos_of_neg hbs hsneg)
    linarith [hAs]
  calc K * ((b ^ (2 * c - 1 : ℝ) - (1 / L) ^ (2 * c - 1 : ℝ)) / (2 * c - 1))
      ≤ K * ((1 / L) ^ (2 * c - 1 : ℝ) / (1 - 2 * c)) :=
        mul_le_mul_of_nonneg_left hstep hKnn
    _ = (K * (1 / L) ^ (2 * c - 1 : ℝ)) / (1 - 2 * c) := by rw [mul_div_assoc]
    _ = (Real.exp (-(c * M)) * Real.exp (c * C) * L) / (1 - 2 * c) := by rw [hKL]
    _ = (Real.exp (c * C) / (1 - 2 * c)) * Real.exp (-(c * M)) * L := by ring

/-- **H-2 — the HALVED σ-cutoff (`sigma_cutoff_pretentious_half`).**  The `c = 1/(2e)`
instance of `sigma_cutoff_pretentious_gen`:

  `∫_{1/L}^{b} σ^{−2}·exp(−(1/(2e))(M − 2log(σL) − C)) dσ
      ≤ (e^{C/(2e)}/(1 − 1/e))·e^{−M/(2e)}·L`.

This is the arm V1's defect #1 forces: the (A.13)/(A.14) square root halves the B-ladder's
`c = 1/e` pointwise exponent, so the honest σ-cutoff runs at `1/(2e)` and the convergence
margin is `2c = 1/e < 1` (comfortable; the method's wall is `2c = 1`).  The landed
`SupF.sigma_cutoff_pretentious` stays untouched as heritage. -/
theorem sigma_cutoff_pretentious_half {L M C b : ℝ} (hL : 3 ≤ L) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hb : 1 / L ≤ b) :
    (∫ σ in (1 / L)..b,
        (1 / σ ^ 2) * Real.exp (-(1 / (2 * Real.exp 1)) * (M - 2 * Real.log (σ * L) - C)))
      ≤ (Real.exp (C / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1))
          * Real.exp (-(M / (2 * Real.exp 1))) * L := by
  have hEpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hE1 : (2 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h2c : 2 * (1 / (2 * Real.exp 1)) = 1 / Real.exp 1 := by
    field_simp
  have hc0 : (0 : ℝ) < 1 / (2 * Real.exp 1) := by positivity
  have hc1 : 2 * (1 / (2 * Real.exp 1)) < 1 := by
    rw [h2c, div_lt_one hEpos]
    linarith
  have h := sigma_cutoff_pretentious_gen (c := 1 / (2 * Real.exp 1)) hc0 hc1 hL hM hC hb
  have e1 : (1 / (2 * Real.exp 1)) * C = C / (2 * Real.exp 1) := by ring
  have e2 : (1 / (2 * Real.exp 1)) * M = M / (2 * Real.exp 1) := by ring
  rw [h2c, e1, e2] at h
  exact h

/-- **The cross-check (`sigma_cutoff_pretentious_of_gen`).**  The `c = 1/e` instance of
`sigma_cutoff_pretentious_gen` reproduces `SupF.sigma_cutoff_pretentious` (:1005) statement
for statement — the evidence that the general form really subsumes the landed one, so the
`_half` arm is an instantiation of the SAME page rather than a parallel proof. -/
theorem sigma_cutoff_pretentious_of_gen {L M C b : ℝ} (hL : 3 ≤ L) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hb : 1 / L ≤ b) :
    (∫ σ in (1 / L)..b,
        (1 / σ ^ 2) * Real.exp (-(1 / Real.exp 1) * (M - 2 * Real.log (σ * L) - C)))
      ≤ (Real.exp (C / Real.exp 1) / (1 - 2 / Real.exp 1))
          * Real.exp (-(M / Real.exp 1)) * L := by
  have hEpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hE1 : (2 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have h2c : 2 * (1 / Real.exp 1) = 2 / Real.exp 1 := by ring
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [h2c, div_lt_one hEpos]
    exact hE1
  have h := sigma_cutoff_pretentious_gen (c := 1 / Real.exp 1) hc0 hc1 hL hM hC hb
  have e1 : (1 / Real.exp 1) * C = C / Real.exp 1 := by ring
  have e2 : (1 / Real.exp 1) * M = M / Real.exp 1 := by ring
  rw [h2c, e1, e2] at h
  exact h

end Salt.MR
