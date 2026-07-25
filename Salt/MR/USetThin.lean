/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RamareErr
import Salt.MR.LargeValueCount
import Salt.MR.Decomp

/-!
# USetThin — the `𝒰`-interior stones of the `hU` ladder (U-1, U-3, U-4)

The §8.3 seam row's second binder `hU` needs three set-level devices; this file lands them.
Scope pins: `docs/exploration/hu-scope-0724.md`, `⟦THE PINS RATIFIED⟧` block.  The threshold
`δ` enters as a *hypothesis* with honest gates (`0 < δ`, and the level `V` with `1 ≤ V`,
`V⁻¹ ≤ δ/K₀`); the pin `δ := P_J^{−α_J}` — which is what makes `V = K₀/δ ≥ 1` available —
lives at the consumer.

* **U-1 `lemma12_meansq_on_subset`** — Lemma 12 (the SHARP window row of
  `Salt.MR.RamareErr`) restricted to a measurable `A ⊆ [−T,T]`.  The main term is restricted
  along with the left side (that is the whole point: §8.3 spends `𝒰`-thinness on the main
  term); the three error rows keep their full `[−T,T]` pricing, by monotonicity of the
  integral of a nonnegative integrand.  Generic core: `meansq_on_subset_of_decomp`.

* **U-3 `wellspaced_discretize`** — "an integral is dominated by a well-spaced sum".  For a
  continuous nonnegative `f` and measurable `A ⊆ [−T,T]` there is a well-spaced `𝒯 ⊆ A` with
  `∫_A f ≤ 2·Σ_{t∈𝒯} f t`.  Route (HU-SCOPE's recommendation): the **∃-above-average**
  argument — NO sup-attainment, since `𝒰` is open and no maximiser need exist.  Cut `[−T,T]`
  into the unit cells `[k, k+1)`; on each cell of positive measure the first-moment method
  (`MeasureTheory.exists_setAverage_le`) supplies a point of `A ∩ cell` at least the average,
  and `|A ∩ cell| ≤ 1` turns the average into a bound for the cell integral; the factor `2`
  is the even/odd split of the cell index, which is what buys the spacing `≥ 1`.

* **U-4 `Uset_thin`** — the thinness of `Ann ∩ 𝒰` measured on a well-spaced set, via Lemma 8
  (`large_value_count`) and the **D1 adapter**.  Two pieces:
  - `largeblock_count` — the `t`-free adapter: a *fixed* block `[p,q]` with `q ≤ 2p` is a
    Lemma-8 dyadic prime polynomial (`primeBlockPoly_eq_dpoly` is the `σ=1`/frequency-sign
    bridge, CATCH #B: `dpoly = P(1−it)`, so the counted set is `−𝒯`).
  - `primeBlockPoly_chain_split` / `Uset_thin` — the witness `[P,Q] ⊆ [P_J, Q_J]` of the
    `𝒰`-condition is split along the ratio-2 chain `P, 2P+1, 4P+3, …` into
    `K₀ = ⌊log₂(Q_J+1)⌋+1` pieces, one of which carries `δ/K₀` by pigeonhole; the union is
    over the candidate family `𝒫 = dyadicPairs = {(p,q) ∈ [P_J,Q_J]² : q ≤ 2p}`.

  **FINDING (D1's true cost).**  HU-SCOPE priced the D1 repair as "dyadic-refine + union
  bound"; the union factor is **not** `log₂ Q + 1`.  The pigeonholed piece of the witness is
  a sub-interval of a dyadic block *truncated at the witness endpoints*, i.e. it depends on
  `t`, so the union must run over a `t`-free family containing every ratio-≤2 sub-interval of
  `[P_J,Q_J]` — `card 𝒫 ≤ (Q_J+1)²`.  (Any `t`-free family able to cover all sub-intervals
  has `≳ Q_J` members, so this is not an artefact of the route.)  HU-SCOPE's *conclusion*
  survives — `Q_J = X^{o(1)}` makes `(Q_J+1)²` an `X^{o(1)}` factor, which is what the
  §8.3 arithmetic absorbs — but the consumer (U-9) must budget `Q_J²`, not a polylog.

The `𝒰`-side pins (`Qseq j < P_L12`, the block-support condition) are consumer-side and do
not appear here: no statement of this file is `hcoef`-adjacent, and the coprime tail enters
only through `lemma12_meansq_sharp`, whose own hypotheses are re-exported verbatim.

Source pins (D5): MR arXiv v4 (`1501.04585v4`) pp. 8 (`𝒰`, eq (6)), 16 (Lemma 8), 20
(Lemma 12).
-/

namespace Salt.MR

open scoped BigOperators
open Finset Complex MeasureTheory intervalIntegral

/-! ## U-1 — Lemma 12's mean square on a measurable subset of `[−T,T]` -/

/-- **The set-restricted mean-square split.**  The generic core of U-1: given the eq (16)
decomposition `spoly = Σ_{j∈I} mainPoly j + errPoly` and an error pricing `E` on the FULL
range `[−T,T]`, the mean square over any measurable `A ⊆ [−T,T]` splits with the main term
also restricted to `A`.  (Restricting the main term is the point: §8.3 spends the thinness of
`𝒰` there.  The error rows cannot be restricted — their pricing is a full-range mean value —
but they need not be: `∫_A ≤ ∫_{[−T,T]}` for a nonnegative integrand.) -/
theorem meansq_on_subset_of_decomp {N : ℕ} {a : ℕ → ℂ} {I : Finset ℕ}
    {mainPoly : ℕ → ℝ → ℂ} {errPoly : ℝ → ℂ} {E T : ℝ} {A : Set ℝ}
    (hT : 0 ≤ T) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T)
    (hmain_cont : ∀ j ∈ I, Continuous (mainPoly j))
    (herr_cont : Continuous errPoly)
    (hdecomp : ∀ t, spoly N a t = (∑ j ∈ I, mainPoly j t) + errPoly t)
    (herr : (∫ t in (-T)..T, ‖errPoly t‖ ^ 2) ≤ E) :
    (∫ t in A, ‖spoly N a t‖ ^ 2)
      ≤ 2 * (I.card : ℝ) * (∑ j ∈ I, ∫ t in A, ‖mainPoly j t‖ ^ 2) + 2 * E := by
  have hmc : Continuous (fun t => ∑ j ∈ I, mainPoly j t) := continuous_finsetSum I hmain_cont
  -- integrability on `A`, inherited from the compact `[−T,T]`
  have hIntA : ∀ g : ℝ → ℂ, Continuous g → IntegrableOn (fun t => ‖g t‖ ^ 2) A := by
    intro g hg
    exact ((hg.norm.pow 2).integrableOn_Icc (a := -T) (b := T)).mono_set hAsub
  have hInt_main : IntegrableOn (fun t => ‖∑ j ∈ I, mainPoly j t‖ ^ 2) A := hIntA _ hmc
  have hInt_err : IntegrableOn (fun t => ‖errPoly t‖ ^ 2) A := hIntA _ herr_cont
  have hInt_lhs : IntegrableOn (fun t => ‖(∑ j ∈ I, mainPoly j t) + errPoly t‖ ^ 2) A :=
    hIntA _ (hmc.add herr_cont)
  have hInt_j : ∀ j ∈ I, IntegrableOn (fun t => ‖mainPoly j t‖ ^ 2) A :=
    fun j hj => hIntA _ (hmain_cont j hj)
  have hInt_rhs : IntegrableOn
      (fun t => 2 * ‖∑ j ∈ I, mainPoly j t‖ ^ 2 + 2 * ‖errPoly t‖ ^ 2) A :=
    (hInt_main.const_mul 2).add (hInt_err.const_mul 2)
  -- the error row: monotonicity from `A` to `[−T,T]`
  have herrA : (∫ t in A, ‖errPoly t‖ ^ 2) ≤ E := by
    have hbig : IntegrableOn (fun t => ‖errPoly t‖ ^ 2) (Set.Icc (-T) T) :=
      (herr_cont.norm.pow 2).integrableOn_Icc
    have hmono : (∫ t in A, ‖errPoly t‖ ^ 2) ≤ ∫ t in Set.Icc (-T) T, ‖errPoly t‖ ^ 2 :=
      setIntegral_mono_set hbig
        (Filter.Eventually.of_forall (fun t => by positivity)) hAsub.eventuallyLE
    have hfull : (∫ t in Set.Icc (-T) T, ‖errPoly t‖ ^ 2)
        = ∫ t in (-T)..T, ‖errPoly t‖ ^ 2 := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T)]
    linarith [hmono, hfull ▸ hmono]
  -- the main row: Cauchy–Schwarz on the `j`-sum, then `∫_A Σ = Σ ∫_A`
  have hmainA : (∫ t in A, ‖∑ j ∈ I, mainPoly j t‖ ^ 2)
      ≤ (I.card : ℝ) * ∑ j ∈ I, ∫ t in A, ‖mainPoly j t‖ ^ 2 := by
    have hIntCS : IntegrableOn (fun t => (I.card : ℝ) * ∑ j ∈ I, ‖mainPoly j t‖ ^ 2) A :=
      (integrable_finsetSum I hInt_j).const_mul _
    calc (∫ t in A, ‖∑ j ∈ I, mainPoly j t‖ ^ 2)
        ≤ ∫ t in A, (I.card : ℝ) * ∑ j ∈ I, ‖mainPoly j t‖ ^ 2 := by
          refine setIntegral_mono_on hInt_main hIntCS hAm (fun t _ => ?_)
          exact cauchy_schwarz_sum_sq I (fun j => mainPoly j t)
      _ = (I.card : ℝ) * ∑ j ∈ I, ∫ t in A, ‖mainPoly j t‖ ^ 2 := by
          rw [MeasureTheory.integral_const_mul]
          congr 1
          exact MeasureTheory.integral_finsetSum I hInt_j
  calc (∫ t in A, ‖spoly N a t‖ ^ 2)
      = ∫ t in A, ‖(∑ j ∈ I, mainPoly j t) + errPoly t‖ ^ 2 := by
        simp only [hdecomp]
    _ ≤ ∫ t in A, (2 * ‖∑ j ∈ I, mainPoly j t‖ ^ 2 + 2 * ‖errPoly t‖ ^ 2) := by
        refine setIntegral_mono_on hInt_lhs hInt_rhs hAm (fun t _ => ?_)
        nlinarith [norm_add_le (∑ j ∈ I, mainPoly j t) (errPoly t),
          norm_nonneg (∑ j ∈ I, mainPoly j t), norm_nonneg (errPoly t),
          norm_nonneg ((∑ j ∈ I, mainPoly j t) + errPoly t),
          sq_nonneg (‖∑ j ∈ I, mainPoly j t‖ - ‖errPoly t‖)]
    _ = 2 * (∫ t in A, ‖∑ j ∈ I, mainPoly j t‖ ^ 2) + 2 * (∫ t in A, ‖errPoly t‖ ^ 2) := by
        rw [MeasureTheory.integral_add (hInt_main.const_mul 2) (hInt_err.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ 2 * (I.card : ℝ) * (∑ j ∈ I, ∫ t in A, ‖mainPoly j t‖ ^ 2) + 2 * E := by
        nlinarith [hmainA, herrA]

/-- **U-1 — Lemma 12's mean square on `A ⊆ [−T,T]` (the SHARP row).**  Exactly
`lemma12_meansq_sharp` with both the left side and the main term restricted to a measurable
`A ⊆ [−T,T]`; the three error rows are the full-range ones, unchanged.  This is the row the
§8.3 assembly consumes at `A = Ann ∩ 𝒰`. -/
theorem lemma12_meansq_on_subset (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      (X : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ))
    (T : ℝ) (hT : 0 ≤ T) (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T) :
    (∫ t in A, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in A, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + 2 * (3 * ((2 * T + 20 * (N : ℝ))
                * ((2 * Real.exp 1 * (X : ℝ) / H + 1) * (Real.exp 1 / (X : ℝ) ^ 2))
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
                    ‖a n‖ ^ 2 / (n : ℝ) ^ 2)) := by
  have hH0 : (0 : ℝ) < H := by linarith
  refine meansq_on_subset_of_decomp hT hAm hAsub
    (fun j _ => continuous_ramMain H N X P Q b c j) (continuous_ramErr H N X P Q a b c)
    (fun t => spoly_ram_decomp H N X P Q a b c t) ?_
  refine (ramErr_moment_split H hH0 N X P Q hP a b c hcoef T hT).trans ?_
  gcongr
  · exact ramWindowErr_moment_sharp H hH N X P Q hX hN hP b c hb hc hwin T hT
  · exact ramP2corr_moment N P Q a b c T
  · exact ramCopTail_moment N P Q a T

/-- **U-1 (exit) — Lemma 12 on `A ⊆ [−T,T]` under the §8.3 support pin (P-iii).**  With the
block-support condition on the coefficient support the coprime-tail row vanishes identically,
leaving the seam row and the `p²` row. -/
theorem lemma12_meansq_on_subset_blockSupport (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      (X : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ))
    (hsupp : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P Q n)
    (T : ℝ) (hT : 0 ≤ T) (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T) :
    (∫ t in A, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in A, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + 2 * (3 * ((2 * T + 20 * (N : ℝ))
                * ((2 * Real.exp 1 * (X : ℝ) / H + 1) * (Real.exp 1 / (X : ℝ) ^ 2))
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)) := by
  have hH0 : (0 : ℝ) < H := by linarith
  refine meansq_on_subset_of_decomp hT hAm hAsub
    (fun j _ => continuous_ramMain H N X P Q b c j) (continuous_ramErr H N X P Q a b c)
    (fun t => spoly_ram_decomp H N X P Q a b c t) ?_
  refine (ramErr_moment_split H hH0 N X P Q hP a b c hcoef T hT).trans ?_
  have h1 := ramWindowErr_moment_sharp H hH N X P Q hX hN hP b c hb hc hwin T hT
  have h2 := ramP2corr_moment N P Q a b c T
  have h3 := ramCopTail_moment_zero N P Q a hsupp T
  rw [h3]
  linarith

/-! ## U-3 — the well-spaced discretization of a set integral -/

/-- The unit cells `[k, k+1)`, `k ∈ ℤ`, are pairwise disjoint (each real lies in exactly the
cell of its floor). -/
lemma unitCell_disjoint {k k' : ℤ} (h : k ≠ k') :
    Disjoint (Set.Ico (k : ℝ) ((k : ℝ) + 1)) (Set.Ico (k' : ℝ) ((k' : ℝ) + 1)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 : ⌊x⌋ = k := Int.floor_eq_iff.mpr ⟨hx.1, hx.2⟩
  have h2 : ⌊x⌋ = k' := Int.floor_eq_iff.mpr ⟨hx'.1, hx'.2⟩
  exact h (h1.symm.trans h2)

/-- **The ∃-above-average device.**  On a measurable set of positive measure at most `1`, a
nonnegative integrable `f` attains, at some point OF THE SET, a value at least the whole set
integral: the average is at most some value of `f` (`exists_setAverage_le`, the first-moment
method), and `|S| ≤ 1` converts the average into the integral.  No supremum is attained and
none is needed — the point of the route, since `𝒰` is open. -/
lemma exists_mem_setIntegral_le {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t) {S : Set ℝ}
    (hSint : IntegrableOn f S) (hS0 : volume S ≠ 0) (hSle : volume S ≤ 1) :
    ∃ t ∈ S, (∫ s in S, f s) ≤ f t := by
  have hStop : volume S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hSle
  obtain ⟨t, htS, ht⟩ := exists_setAverage_le hS0 hStop hSint
  refine ⟨t, htS, ?_⟩
  have hsm : volume.real S • (⨍ x in S, f x) = ∫ x in S, f x :=
    measure_smul_setAverage (μ := volume) f hStop
  have hreal_le : volume.real S ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hSle
    simpa [MeasureTheory.measureReal_def] using h
  have hstep : volume.real S * (⨍ x in S, f x) ≤ volume.real S * f t :=
    mul_le_mul_of_nonneg_left ht measureReal_nonneg
  have hfin : volume.real S * f t ≤ f t := mul_le_of_le_one_left (hf0 t) hreal_le
  rw [← hsm, smul_eq_mul]
  linarith

/-- **U-3 — the well-spaced discretization.**  For a continuous nonnegative `f` and a
measurable `A ⊆ [−T,T]` there is a WELL-SPACED finite `𝒯 ⊆ A` with
`∫_A f ≤ 2 · Σ_{t∈𝒯} f t`.  This is the classical "an integral is dominated by a well-spaced
sum" device, in the shape `wellspaced_l2` / `large_value_count` consume (`𝒯 ⊆ A ⊆ [−T,T]`
supplies their `hsub𝒯`, `WellSpaced 𝒯` their `hws`).

Route (no sup-attainment): cut `[−T,T]` into the unit cells `[k,k+1)`; on each cell of
positive measure pick, by `exists_mem_setIntegral_le`, a point of `A ∩ cell` whose value is at
least the cell integral; the cells of measure zero contribute nothing.  Points from cells of
the SAME parity are `≥ 1` apart (their indices differ by `≥ 2`), and one of the two parity
classes carries at least half the sum — that halving is the factor `2`. -/
theorem wellspaced_discretize (T : ℝ) (f : ℝ → ℝ) (hfc : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T) :
    ∃ 𝒯 : Finset ℝ, (↑𝒯 : Set ℝ) ⊆ A ∧ WellSpaced 𝒯 ∧ (∫ t in A, f t) ≤ 2 * ∑ t ∈ 𝒯, f t := by
  classical
  have hSm : ∀ k : ℤ, MeasurableSet (A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1)) :=
    fun k => hAm.inter measurableSet_Ico
  have hIntA : IntegrableOn f (Set.Icc (-T) T) := hfc.integrableOn_Icc
  have hSint : ∀ k : ℤ, IntegrableOn f (A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1)) :=
    fun k => hIntA.mono_set (Set.inter_subset_left.trans hAsub)
  -- the cell cover of `A`
  have hcover : (⋃ k ∈ Finset.Icc (-⌈T⌉) ⌈T⌉, A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1)) = A := by
    refine Set.Subset.antisymm (Set.iUnion₂_subset (fun k _ => Set.inter_subset_left)) ?_
    intro x hx
    have hxI := Set.mem_Icc.mp (hAsub hx)
    have hmem : ⌊x⌋ ∈ Finset.Icc (-⌈T⌉) ⌈T⌉ := by
      rw [Finset.mem_Icc]
      refine ⟨?_, le_trans (Int.floor_le_floor hxI.2) (Int.floor_le_ceil T)⟩
      have h1 : ⌊(-T : ℝ)⌋ ≤ ⌊x⌋ := Int.floor_le_floor (by linarith [hxI.1])
      rwa [Int.floor_neg] at h1
    exact Set.mem_iUnion₂.mpr
      ⟨⌊x⌋, hmem, ⟨hx, ⟨Int.floor_le x, Int.lt_floor_add_one x⟩⟩⟩
  have hdisj : ((Finset.Icc (-⌈T⌉) ⌈T⌉ : Finset ℤ) : Set ℤ).PairwiseDisjoint
      (fun k : ℤ => A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1)) := by
    intro k _ k' _ hne
    simp only [Function.onFun]
    exact (unitCell_disjoint hne).mono Set.inter_subset_right Set.inter_subset_right
  have hsplit : (∫ t in A, f t)
      = ∑ k ∈ Finset.Icc (-⌈T⌉) ⌈T⌉, ∫ t in A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1), f t := by
    have h := integral_biUnion_finset (μ := volume) (f := f) (Finset.Icc (-⌈T⌉) ⌈T⌉)
      (fun k _ => hSm k) hdisj (fun k _ => hSint k)
    rwa [hcover] at h
  -- the per-cell above-average point
  have hex : ∀ k : ℤ, ∃ t : ℝ, volume (A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1)) ≠ 0 →
      (t ∈ A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1) ∧
        (∫ s in A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1), f s) ≤ f t) := by
    intro k
    by_cases hk : volume (A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1)) = 0
    · exact ⟨0, fun h => absurd hk h⟩
    · have hle : volume (A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1)) ≤ 1 := by
        calc volume (A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1))
            ≤ volume (Set.Ico (k : ℝ) ((k : ℝ) + 1)) := measure_mono Set.inter_subset_right
          _ = 1 := by rw [Real.volume_Ico]; norm_num
      obtain ⟨t, htS, ht⟩ := exists_mem_setIntegral_le hf0 (hSint k) hk hle
      exact ⟨t, fun _ => ⟨htS, ht⟩⟩
  choose g hg using hex
  set K : Finset ℤ := (Finset.Icc (-⌈T⌉) ⌈T⌉).filter
    (fun k : ℤ => volume (A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1)) ≠ 0) with hKdef
  have hgS : ∀ k ∈ K, g k ∈ A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1) := by
    intro k hk
    rw [hKdef, Finset.mem_filter] at hk
    exact (hg k hk.2).1
  -- `∫_A f ≤ Σ_{k∈K} f (g k)`
  have hsum : (∫ t in A, f t) ≤ ∑ k ∈ K, f (g k) := by
    have hfil : ∑ k ∈ K, (∫ t in A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1), f t)
        = ∑ k ∈ Finset.Icc (-⌈T⌉) ⌈T⌉, ∫ t in A ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1), f t := by
      rw [hKdef]
      refine Finset.sum_filter_of_ne (fun k _ hne => ?_)
      by_contra h
      exact hne (setIntegral_measure_zero f h)
    rw [hsplit, ← hfil]
    refine Finset.sum_le_sum (fun k hk => ?_)
    rw [hKdef, Finset.mem_filter] at hk
    exact (hg k hk.2).2
  -- each parity class of cell indices gives a well-spaced set
  have hbuild : ∀ r : ℤ, ∃ 𝒯 : Finset ℝ, (↑𝒯 : Set ℝ) ⊆ A ∧ WellSpaced 𝒯 ∧
      ∑ k ∈ K.filter (fun k : ℤ => k % 2 = r), f (g k) = ∑ t ∈ 𝒯, f t := by
    intro r
    have hsubK : K.filter (fun k : ℤ => k % 2 = r) ⊆ K := Finset.filter_subset _ _
    have hfloor : ∀ k ∈ K, ⌊g k⌋ = k := by
      intro k hk
      exact Int.floor_eq_iff.mpr ⟨(hgS k hk).2.1, (hgS k hk).2.2⟩
    have hinj : Set.InjOn g ↑(K.filter (fun k : ℤ => k % 2 = r)) := by
      intro k hk k' hk' heq
      have h1 := hfloor k (hsubK (Finset.mem_coe.mp hk))
      have h2 := hfloor k' (hsubK (Finset.mem_coe.mp hk'))
      rw [← h1, ← h2, heq]
    refine ⟨(K.filter (fun k : ℤ => k % 2 = r)).image g, ?_, ?_, (Finset.sum_image hinj).symm⟩
    · intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      exact (hgS k (hsubK hk)).1
    · intro t ht s hs hne
      simp only [Finset.mem_image] at ht hs
      obtain ⟨k, hk, rfl⟩ := ht
      obtain ⟨k', hk', rfl⟩ := hs
      have hkne : k ≠ k' := by rintro rfl; exact hne rfl
      have hkr := (Finset.mem_filter.mp hk).2
      have hk'r := (Finset.mem_filter.mp hk').2
      have hkg := hgS k (hsubK hk)
      have hk'g := hgS k' (hsubK hk')
      rcases lt_or_gt_of_ne hkne with hlt | hlt
      · have h2 : k + 2 ≤ k' := by omega
        have h2R : (k : ℝ) + 2 ≤ (k' : ℝ) := by exact_mod_cast h2
        refine le_abs.mpr (Or.inr ?_)
        have := hkg.2.2
        have := hk'g.2.1
        linarith
      · have h2 : k' + 2 ≤ k := by omega
        have h2R : (k' : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast h2
        refine le_abs.mpr (Or.inl ?_)
        have := hk'g.2.2
        have := hkg.2.1
        linarith
  obtain ⟨𝒯₀, h₀A, h₀ws, h₀sum⟩ := hbuild 0
  obtain ⟨𝒯₁, h₁A, h₁ws, h₁sum⟩ := hbuild 1
  have hKsplit : ∑ k ∈ K, f (g k)
      = (∑ k ∈ K.filter (fun k : ℤ => k % 2 = 0), f (g k))
        + ∑ k ∈ K.filter (fun k : ℤ => k % 2 = 1), f (g k) := by
    rw [← Finset.sum_filter_add_sum_filter_not K (fun k : ℤ => k % 2 = 0)]
    congr 2
    refine Finset.filter_congr (fun k _ => ?_)
    constructor
    · intro h; omega
    · intro h; omega
  rcases le_total (∑ k ∈ K.filter (fun k : ℤ => k % 2 = 1), f (g k))
      (∑ k ∈ K.filter (fun k : ℤ => k % 2 = 0), f (g k)) with hcase | hcase
  · exact ⟨𝒯₀, h₀A, h₀ws, by rw [← h₀sum]; linarith⟩
  · exact ⟨𝒯₁, h₁A, h₁ws, by rw [← h₁sum]; linarith⟩

/-! ## U-4 — the `D1` adapter: a fixed ratio-2 block is a Lemma-8 polynomial -/

/-- The Lemma-8 coefficient source of a prime block: `f` restricted to the primes of `[P,Q]`
(the `σ = 1` numerator; `blockCoeff = blockSrc / n` is what `dpoly` carries). -/
noncomputable def blockSrc (f : ℕ → ℂ) (P Q : ℕ) (n : ℕ) : ℂ :=
  if n.Prime ∧ P ≤ n ∧ n ≤ Q then f n else 0

/-- The prime block polynomial is the `σ = 1` polynomial of its own restricted coefficients. -/
lemma primeBlockPoly_eq_spoly (f : ℕ → ℂ) (P Q N : ℕ) (hP : 1 ≤ P) (hQN : Q ≤ N) (t : ℝ) :
    primeBlockPoly f P Q t = spoly N (blockSrc f P Q) t := by
  unfold primeBlockPoly spoly
  have h1 : ∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
        f p / (p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
      = ∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
          blockSrc f P Q p / (p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [blockSrc, if_pos ⟨hp.2, hp.1.1, hp.1.2⟩]
  rw [h1]
  refine Finset.sum_subset (fun p hp => ?_) (fun n _ hnot => ?_)
  · rw [Finset.mem_filter, Finset.mem_Icc] at hp
    exact Finset.mem_Icc.mpr ⟨le_trans hP hp.1.1, le_trans hp.1.2 hQN⟩
  · have hz : blockSrc f P Q n = 0 := by
      rw [blockSrc, if_neg]
      rintro ⟨hpr, h1', h2'⟩
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1', h2'⟩, hpr⟩)
    rw [hz, zero_div]

/-- **The D1 sign bridge (CATCH #B).**  `primeBlockPoly f P Q t = dpoly N (blockSrc/n) (−t)`:
Lemma 8's `dpoly` is `P(1−it)`, so a caller with `|P(1+it)|` large hands Lemma 8 the NEGATED
ordinate set. -/
lemma primeBlockPoly_eq_dpoly (f : ℕ → ℂ) (P Q N : ℕ) (hP : 1 ≤ P) (hQN : Q ≤ N) (t : ℝ) :
    primeBlockPoly f P Q t = dpoly N (fun n => blockSrc f P Q n / (n : ℂ)) (-t) := by
  rw [primeBlockPoly_eq_spoly f P Q N hP hQN t, spoly_eq_dpoly]

/-- A subset of a well-spaced set is well-spaced. -/
lemma wellSpaced_of_subset {𝒮 𝒯 : Finset ℝ} (h : 𝒮 ⊆ 𝒯) (hws : WellSpaced 𝒯) :
    WellSpaced 𝒮 := fun t ht r hr hne => hws t (h ht) r (h hr) hne

/-- **The `t`-free Lemma-8 adapter.**  A FIXED prime block `[p,q]` of ratio at most `2` on
which `‖primeBlockPoly f p q ·‖ ≥ V⁻¹` holds along a well-spaced `𝒯 ⊆ [−T,T]` is counted by
Lemma 8 (`large_value_count`) at the frozen constant `840`.  Gates carried verbatim from
Lemma 8: `3 ≤ p ≤ T`, `1 < T`, `log T/log p ≥ 30`, `loglog T ≥ 5`, `1 ≤ V`. -/
theorem largeblock_count (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (p q : ℕ) (T V : ℝ)
    (hp3 : 3 ≤ p) (hq2p : q ≤ 2 * p) (hT : 1 < T) (hpT : (p : ℝ) ≤ T) (hV : 1 ≤ V)
    (hκ30 : 30 ≤ Real.log T / Real.log p) (hLL5 : 5 ≤ Real.log (Real.log T))
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hlb : ∀ t ∈ 𝒯, V⁻¹ ≤ ‖primeBlockPoly f p q t‖) :
    (𝒯.card : ℝ) ≤ 840 * T ^ (2 * Real.log V / Real.log p) * V ^ 2
        * Real.exp (2 * (Real.log T / Real.log p) * Real.log (Real.log T)) := by
  classical
  have hp1 : 1 ≤ p := by omega
  have hcard : (𝒯.image (fun t => -t)).card = 𝒯.card :=
    Finset.card_image_of_injective _ neg_injective
  have hws' : WellSpaced (𝒯.image (fun t => -t)) := by
    intro s hs r hr hne
    rw [Finset.mem_image] at hs hr
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨u, hu, rfl⟩ := hr
    have htu : t ≠ u := fun h => hne (by rw [h])
    have h := hws t ht u hu htu
    rwa [show -t - -u = -(t - u) by ring, abs_neg]
  have hsub' : ∀ s ∈ 𝒯.image (fun t => -t), s ∈ Set.Icc (-T) T := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have h := Set.mem_Icc.mp (hsub t ht)
    exact Set.mem_Icc.mpr ⟨by linarith [h.2], by linarith [h.1]⟩
  have hsupp : ∀ m, (fun n => blockSrc f p q n / (n : ℂ)) m ≠ 0 → m.Prime ∧ p ≤ m := by
    intro m hm
    by_cases hcond : m.Prime ∧ p ≤ m ∧ m ≤ q
    · exact ⟨hcond.1, hcond.2.1⟩
    · exfalso; apply hm; simp only [blockSrc, if_neg hcond, zero_div]
  have hcoeff : ∀ m, (fun n => blockSrc f p q n / (n : ℂ)) m ≠ 0 →
      ‖(fun n => blockSrc f p q n / (n : ℂ)) m‖ ≤ (m : ℝ)⁻¹ := by
    intro m hm
    obtain ⟨hpr, hpm⟩ := hsupp m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hpr.pos
    by_cases hcond : m.Prime ∧ p ≤ m ∧ m ≤ q
    · simp only [blockSrc, if_pos hcond, norm_div, Complex.norm_natCast]
      rw [inv_eq_one_div]
      gcongr
      exact hf1 m
    · exfalso; apply hm; simp only [blockSrc, if_neg hcond, zero_div]
  have hlb' : ∀ s ∈ 𝒯.image (fun t => -t),
      V⁻¹ ≤ ‖dpoly (2 * p) (fun n => blockSrc f p q n / (n : ℂ)) s‖ := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [← primeBlockPoly_eq_dpoly f p q (2 * p) hp1 hq2p t]
    exact hlb t ht
  have h := large_value_count p (fun n => blockSrc f p q n / (n : ℂ)) T V hp3 hT hpT hV hκ30
    hLL5 (𝒯.image (fun t => -t)) hws' hsub' hsupp hcoeff hlb'
  rwa [hcard] at h

/-- Monotonicity of Lemma 8's bound in the block base: the bound at `p ≥ P` is at most the
bound at `P` (both exponents decrease in the base). -/
lemma largeblock_bound_mono (T V : ℝ) (hT : 1 < T) (hV : 1 ≤ V) (P p : ℕ) (hP3 : 3 ≤ P)
    (hPp : P ≤ p) (hLL : 0 ≤ Real.log (Real.log T)) :
    840 * T ^ (2 * Real.log V / Real.log p) * V ^ 2
        * Real.exp (2 * (Real.log T / Real.log p) * Real.log (Real.log T))
      ≤ 840 * T ^ (2 * Real.log V / Real.log P) * V ^ 2
        * Real.exp (2 * (Real.log T / Real.log P) * Real.log (Real.log T)) := by
  have hP1 : (1 : ℝ) < (P : ℝ) := by
    have : (3 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP3
    linarith
  have hlogP : 0 < Real.log P := Real.log_pos hP1
  have hlogp : Real.log P ≤ Real.log p := by
    refine Real.log_le_log (by linarith) ?_
    exact_mod_cast hPp
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hV
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have h1 : 2 * Real.log V / Real.log p ≤ 2 * Real.log V / Real.log P := by gcongr
  have h2 : Real.log T / Real.log p ≤ Real.log T / Real.log P := by gcongr
  have hA : T ^ (2 * Real.log V / Real.log p) ≤ T ^ (2 * Real.log V / Real.log P) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hT) h1
  have hB : Real.exp (2 * (Real.log T / Real.log p) * Real.log (Real.log T))
      ≤ Real.exp (2 * (Real.log T / Real.log P) * Real.log (Real.log T)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hApos : (0 : ℝ) < T ^ (2 * Real.log V / Real.log p) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hVpos : (0 : ℝ) < V ^ 2 := by nlinarith
  have hBpos : (0 : ℝ) < Real.exp (2 * (Real.log T / Real.log p) * Real.log (Real.log T)) :=
    Real.exp_pos _
  have hstep : 840 * T ^ (2 * Real.log V / Real.log p) * V ^ 2
      ≤ 840 * T ^ (2 * Real.log V / Real.log P) * V ^ 2 := by nlinarith
  have hRHSnn : (0 : ℝ) ≤ 840 * T ^ (2 * Real.log V / Real.log P) * V ^ 2 := by
    have h : (0 : ℝ) < T ^ (2 * Real.log V / Real.log P) :=
      Real.rpow_pos_of_pos (by linarith) _
    nlinarith
  exact mul_le_mul hstep hB (le_of_lt hBpos) hRHSnn

/-! ### The ratio-2 chain and the witness refinement -/

/-- **The ratio-2 chain from `P`**: `P, 2P+1, 4P+3, …`.  The `k`-th block
`[chain k, 2·chain k]` has ratio exactly `2`, and consecutive blocks abut exactly
(`chain (k+1) = 2·chain k + 1`), so the blocks tile `[P, ∞)` without overlap. -/
def ratioChain (P : ℕ) : ℕ → ℕ
  | 0 => P
  | k + 1 => 2 * ratioChain P k + 1

@[simp] lemma ratioChain_zero (P : ℕ) : ratioChain P 0 = P := rfl

lemma ratioChain_succ (P k : ℕ) : ratioChain P (k + 1) = 2 * ratioChain P k + 1 := rfl

lemma ratioChain_add_one_eq (P k : ℕ) : ratioChain P k + 1 = 2 ^ k * (P + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : ratioChain P (k + 1) + 1 = 2 * (ratioChain P k + 1) := by
      rw [ratioChain_succ]; ring
    rw [h, ih, pow_succ]; ring

lemma ratioChain_mono (P : ℕ) : Monotone (ratioChain P) := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  rw [ratioChain_succ]; omega

lemma ratioChain_ge (P k : ℕ) : P ≤ ratioChain P k := by
  have h := ratioChain_mono P (Nat.zero_le k)
  rwa [ratioChain_zero] at h

/-- `⌊log₂ (Q+1)⌋ + 1` chain steps always overshoot `Q`. -/
lemma lt_ratioChain_log (P Q : ℕ) : Q < ratioChain P (Nat.log 2 (Q + 1) + 1) := by
  have h := ratioChain_add_one_eq P (Nat.log 2 (Q + 1) + 1)
  have h2 : Q + 1 < 2 ^ (Nat.log 2 (Q + 1) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) (Q + 1)
  have h3 : 2 ^ (Nat.log 2 (Q + 1) + 1) ≤ 2 ^ (Nat.log 2 (Q + 1) + 1) * (P + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h4 : Q + 1 < ratioChain P (Nat.log 2 (Q + 1) + 1) + 1 := by
    rw [h]; exact lt_of_lt_of_le h2 h3
  omega

/-- **The chain tiling of `[P,Q]`.**  Once the chain overshoots `Q`, its first `K` blocks
(clipped at `Q`) partition `[P,Q]` exactly. -/
lemma Icc_eq_biUnion_ratioChain (P Q K : ℕ) (hK : Q < ratioChain P K) :
    Finset.Icc P Q = (Finset.range K).biUnion
      (fun k => Finset.Icc (ratioChain P k) (min (2 * ratioChain P k) Q)) := by
  ext n
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_Icc, le_min_iff]
  constructor
  · rintro ⟨hPn, hnQ⟩
    have hex : ∃ k, n < ratioChain P k := ⟨K, by omega⟩
    have hspec := Nat.find_spec hex
    have hjle : Nat.find hex ≤ K := Nat.find_min' hex (by omega)
    have hj0 : Nat.find hex ≠ 0 := by
      intro h0
      rw [h0, ratioChain_zero] at hspec
      omega
    have hkey : ratioChain P (Nat.find hex - 1) ≤ n := by
      have h := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
      omega
    have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    have hub : n < 2 * ratioChain P (Nat.find hex - 1) + 1 := by
      have h := hspec
      rwa [← hsucc, ratioChain_succ] at h
    exact ⟨Nat.find hex - 1, by omega, hkey, by omega, hnQ⟩
  · rintro ⟨k, _, hck, _, hnQ⟩
    exact ⟨le_trans (ratioChain_ge P k) hck, hnQ⟩

/-- The chain blocks are pairwise disjoint. -/
lemma ratioChain_pieces_disjoint (P Q K : ℕ) :
    ((Finset.range K : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun k => Finset.Icc (ratioChain P k) (min (2 * ratioChain P k) Q)) := by
  intro k _ k' _ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro n hn hn'
  rw [Finset.mem_Icc] at hn hn'
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : ratioChain P (k + 1) ≤ ratioChain P k' := ratioChain_mono P (by omega)
    rw [ratioChain_succ] at h1
    omega
  · have h1 : ratioChain P (k' + 1) ≤ ratioChain P k := ratioChain_mono P (by omega)
    rw [ratioChain_succ] at h1
    omega

/-- **The witness refinement.**  A prime block polynomial over `[P,Q]` is the sum of its
`K` chain pieces, each of ratio at most `2`. -/
lemma primeBlockPoly_chain_split (f : ℕ → ℂ) (P Q K : ℕ) (hK : Q < ratioChain P K) (t : ℝ) :
    primeBlockPoly f P Q t
      = ∑ k ∈ Finset.range K,
          primeBlockPoly f (ratioChain P k) (min (2 * ratioChain P k) Q) t := by
  unfold primeBlockPoly
  rw [Icc_eq_biUnion_ratioChain P Q K hK, Finset.filter_biUnion]
  exact Finset.sum_biUnion
    ((ratioChain_pieces_disjoint P Q K).mono (fun k => Finset.filter_subset _ _))

/-- Pigeonhole on a finite sum of complex numbers. -/
lemma exists_piece_large {K : ℕ} (hK : 0 < K) (z : ℕ → ℂ) {δ : ℝ}
    (h : δ < ‖∑ k ∈ Finset.range K, z k‖) : ∃ k ∈ Finset.range K, δ / (K : ℝ) < ‖z k‖ := by
  by_contra hcon
  have hall : ∀ k ∈ Finset.range K, ‖z k‖ ≤ δ / (K : ℝ) := by
    intro k hk
    rw [← not_lt]
    intro hlt
    exact hcon ⟨k, hk, hlt⟩
  have h1 : ‖∑ k ∈ Finset.range K, z k‖ ≤ ∑ k ∈ Finset.range K, ‖z k‖ := norm_sum_le _ _
  have h2 : ∑ k ∈ Finset.range K, ‖z k‖ ≤ (K : ℝ) * (δ / (K : ℝ)) := by
    calc ∑ k ∈ Finset.range K, ‖z k‖
        ≤ ∑ _k ∈ Finset.range K, δ / (K : ℝ) := Finset.sum_le_sum hall
      _ = (K : ℝ) * (δ / (K : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hK0 : (K : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    linarith
  have h3 : (K : ℝ) * (δ / (K : ℝ)) = δ := by field_simp
  linarith

/-- **The candidate block family** of `[P₀,Q₀]`: every sub-block of ratio at most `2`.  The
union bound of `Uset_thin` runs over this `t`-free family. -/
def dyadicPairs (P₀ Q₀ : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc P₀ Q₀) ×ˢ (Finset.Icc P₀ Q₀)).filter (fun pq => pq.2 ≤ 2 * pq.1)

lemma card_dyadicPairs_le (P₀ Q₀ : ℕ) : (dyadicPairs P₀ Q₀).card ≤ (Q₀ + 1) ^ 2 := by
  have h1 : (dyadicPairs P₀ Q₀).card ≤ ((Finset.Icc P₀ Q₀) ×ˢ (Finset.Icc P₀ Q₀)).card :=
    Finset.card_filter_le _ _
  rw [Finset.card_product, Nat.card_Icc] at h1
  calc (dyadicPairs P₀ Q₀).card ≤ (Q₀ + 1 - P₀) * (Q₀ + 1 - P₀) := h1
    _ ≤ (Q₀ + 1) ^ 2 := by
        have : Q₀ + 1 - P₀ ≤ Q₀ + 1 := by omega
        calc (Q₀ + 1 - P₀) * (Q₀ + 1 - P₀) ≤ (Q₀ + 1) * (Q₀ + 1) :=
              Nat.mul_le_mul this this
          _ = (Q₀ + 1) ^ 2 := by ring

/-- **U-4 — `𝒰` is thin on a well-spaced set.**  Every `t` of a well-spaced `𝒯 ⊆ [−T,T]∩𝒰`
carries, at the block index `Jb`, a sub-block of `[P_Jb, Q_Jb]` on which the prime polynomial
exceeds `δ`; refining that witness along the ratio-2 chain and pigeonholing over the
`K₀ = ⌊log₂(Q_Jb+1)⌋+1` pieces puts `t` into one of the `dyadicPairs` count sets, each of
which Lemma 8 bounds.  Hence the raw count bound below; the `T^{2α+η}` arithmetic is the
consumer's (U-9).

Honest gates, all carried: `3 ≤ P_Jb`, `Q_Jb ≤ T`, `1 < T`, `log T/log Q_Jb ≥ 30`,
`loglog T ≥ 5`, `0 < δ`, `‖f n‖ ≤ 1`, and `V` any level with `1 ≤ V` and `V⁻¹ ≤ δ/K₀`
(the ratified pin `δ := P_J^{−α_J} ≤ 1` is what supplies `V := K₀/δ ≥ 1` at the consumer).
`card 𝒫` is bounded by `card_dyadicPairs_le`. -/
theorem Uset_thin (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (Pseq Qseq : ℕ → ℕ) (δ : ℝ)
    (J Jb : ℕ) (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J) (hδ0 : 0 < δ)
    (T V : ℝ) (hT : 1 < T) (hV : 1 ≤ V)
    (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log (Qseq Jb)) (hLL5 : 5 ≤ Real.log (Real.log T))
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hU : ∀ t ∈ 𝒯, t ∈ Uset f Pseq Qseq δ J) :
    (𝒯.card : ℝ)
      ≤ ((dyadicPairs (Pseq Jb) (Qseq Jb)).card : ℝ)
        * (840 * T ^ (2 * Real.log V / Real.log (Pseq Jb)) * V ^ 2
            * Real.exp (2 * (Real.log T / Real.log (Pseq Jb)) * Real.log (Real.log T))) := by
  classical
  set K₀ : ℕ := Nat.log 2 (Qseq Jb + 1) + 1 with hK₀
  set B : ℝ := 840 * T ^ (2 * Real.log V / Real.log (Pseq Jb)) * V ^ 2
      * Real.exp (2 * (Real.log T / Real.log (Pseq Jb)) * Real.log (Real.log T)) with hB
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log T) := by linarith
  have hK₀pos : 0 < K₀ := by omega
  have hK₀R : (0 : ℝ) < (K₀ : ℝ) := by exact_mod_cast hK₀pos
  have hthr : (0 : ℝ) < δ / (K₀ : ℝ) := by positivity
  -- (i) each candidate block's count set is Lemma-8 bounded
  have hpair : ∀ pq ∈ dyadicPairs (Pseq Jb) (Qseq Jb),
      (((𝒯.filter (fun t => V⁻¹ ≤ ‖primeBlockPoly f pq.1 pq.2 t‖)).card : ℝ)) ≤ B := by
    intro pq hpq
    rw [dyadicPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_Icc] at hpq
    obtain ⟨⟨⟨hp1, hp2⟩, hq1, hq2⟩, hratio⟩ := hpq
    have hp3' : 3 ≤ pq.1 := le_trans hP3 hp1
    have hp1R : (1 : ℝ) < (pq.1 : ℝ) := by
      have : (3 : ℝ) ≤ (pq.1 : ℝ) := by exact_mod_cast hp3'
      linarith
    have hlogp : 0 < Real.log pq.1 := Real.log_pos hp1R
    have hlogQ : Real.log pq.1 ≤ Real.log (Qseq Jb) := by
      refine Real.log_le_log (by linarith) ?_
      exact_mod_cast hp2
    have hpT : (pq.1 : ℝ) ≤ T := by
      have : (pq.1 : ℝ) ≤ (Qseq Jb : ℝ) := by exact_mod_cast hp2
      linarith
    have hlogTnn : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (le_of_lt hT)
    have hκ : 30 ≤ Real.log T / Real.log pq.1 := by
      refine le_trans hκ30 ?_
      gcongr
    have hcount := largeblock_count f hf1 pq.1 pq.2 T V hp3' hratio hT hpT hV hκ hLL5
      (𝒯.filter (fun t => V⁻¹ ≤ ‖primeBlockPoly f pq.1 pq.2 t‖))
      (wellSpaced_of_subset (Finset.filter_subset _ _) hws)
      (fun t ht => hsub t (Finset.mem_filter.mp ht).1)
      (fun t ht => (Finset.mem_filter.mp ht).2)
    exact le_trans hcount
      (largeblock_bound_mono T V hT hV (Pseq Jb) pq.1 hP3 hp1 hLL0)
  -- (ii) the count sets cover `𝒯`
  have hcover : 𝒯 ⊆ (dyadicPairs (Pseq Jb) (Qseq Jb)).biUnion
      (fun pq => 𝒯.filter (fun t => V⁻¹ ≤ ‖primeBlockPoly f pq.1 pq.2 t‖)) := by
    intro t ht
    have hUt := hU t ht Jb hJb1 hJbJ
    obtain ⟨P, Q, hP, hQ, hlarge⟩ :
        ∃ P Q, Pseq Jb ≤ P ∧ Q ≤ Qseq Jb ∧ δ < ‖primeBlockPoly f P Q t‖ := by
      by_contra hcon
      refine hUt (fun P Q hP hQ => ?_)
      by_contra hcon2
      exact hcon ⟨P, Q, hP, hQ, not_le.mp hcon2⟩
    have hP1 : 1 ≤ P := le_trans (by omega) hP
    have hQK : Q < ratioChain P K₀ := by
      refine lt_of_lt_of_le (lt_ratioChain_log P Q) (ratioChain_mono P ?_)
      have h : Nat.log 2 (Q + 1) ≤ Nat.log 2 (Qseq Jb + 1) :=
        Nat.log_mono_right (by omega)
      omega
    rw [primeBlockPoly_chain_split f P Q K₀ hQK t] at hlarge
    obtain ⟨k, _, hbig⟩ := exists_piece_large hK₀pos
      (fun k => primeBlockPoly f (ratioChain P k) (min (2 * ratioChain P k) Q) t) hlarge
    have hnz : primeBlockPoly f (ratioChain P k) (min (2 * ratioChain P k) Q) t ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hbig
      linarith
    have hck : ratioChain P k ≤ Q := by
      by_contra hcon
      apply hnz
      unfold primeBlockPoly
      rw [Finset.Icc_eq_empty (by omega), Finset.filter_empty, Finset.sum_empty]
    have hkP : Pseq Jb ≤ ratioChain P k := le_trans hP (ratioChain_ge P k)
    refine Finset.mem_biUnion.mpr
      ⟨(ratioChain P k, min (2 * ratioChain P k) Q), ?_, ?_⟩
    · rw [dyadicPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨⟨hkP, by omega⟩, ⟨by omega, by omega⟩⟩, min_le_left _ _⟩
    · exact Finset.mem_filter.mpr ⟨ht, le_trans hVinv (le_of_lt hbig)⟩
  -- (iii) the union bound
  calc (𝒯.card : ℝ)
      ≤ (((dyadicPairs (Pseq Jb) (Qseq Jb)).biUnion
          (fun pq => 𝒯.filter (fun t => V⁻¹ ≤ ‖primeBlockPoly f pq.1 pq.2 t‖))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ pq ∈ dyadicPairs (Pseq Jb) (Qseq Jb),
          ((𝒯.filter (fun t => V⁻¹ ≤ ‖primeBlockPoly f pq.1 pq.2 t‖)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _pq ∈ dyadicPairs (Pseq Jb) (Qseq Jb), B := Finset.sum_le_sum hpair
    _ = ((dyadicPairs (Pseq Jb) (Qseq Jb)).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Salt.MR
