/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SeamBallWeighted

/-!
# SeamGraded — the GRADED `𝒯ⱼ / 𝒰` partition (ROUTE G, stone G0)

The graded partition core of Route G (`docs/exploration/hsup-design.md` ⟦V6⟧ +
⟦MORNING RATIFICATIONS (JYH 7/26)⟧: the Route-G SHAPE is ratified; `G1b`'s hU replay is
HELD behind the far-arm repair).  Everything here is **parallel and additive**: the landed
flat family (`Decomp.BlockSmallAt`/`Tset`/`Uset`, `SeamSplit.seamTtot`/`seam_TU_split`,
`SeamBallWeighted.prop_A3_T1_row_split_weighted`) is untouched heritage — this file supplies
the graded twin alongside it, in a new module, so iron rule 5 never engages.

## Why graded (the flat-δ wall)

⟦V6⟧'s TLEG-SCOPE verdict: the row's `𝒯`-leg is **impossible** at the flat threshold
`‖primeBlockPoly f P Q t‖ ≤ δ`.  The `𝒯`-side needs `δ ≲ Q_j^{−1/2}` (the co-factor mass
`e^{v/H}` at the top of `I_j`); the `𝒰`-side floor forces `δ ≥ K₀·P_J^{−1/4}` (Lemma 8's
thinness exponent).  Collision: `P_J^{1/4} ≲ 1`, contradictory for every `P_J > 1`,
independent of every pin.  MR's own threshold — eq (21), `|Q_{j,H}(1+it)| ≤ e^{−α_j v/H_j}`,
graded in the **block index `v`** — is load-bearing twice (it pays the co-factor mass in
(23) AND calibrates Lemma 8's exponent to `2α_j` at the block's own base).  Restoring it is
the whole point of Route G, and `BlockSmallG` is where it enters.

## The graded predicate (G0a)

`BlockSmallG f Pseq Qseq Hseq αseq j t` quantifies over the **finite** block index set
`ramI (Hseq j) (Pseq j) (Qseq j)` (`RamareWindows` :83, `Finset.Icc ⌊H log P⌋₊ ⌊H log Q⌋₊`)
rather than over an arbitrary sub-range `[P,Q] ⊆ [Pⱼ,Qⱼ]`, and asks the MR (21) bound of
each block polynomial `ramQ (Hseq j) (Pseq j) (Qseq j) v f` (`RamareWindows` :70).  Two
consequences, both structural:

* the threshold `exp(−(αseq j)·v / Hseq j)` DEPENDS ON `v` — the grading;
* the defining intersection is over a `Finset`, not an arbitrary family, so closedness and
  measurability are strictly easier than in the flat file (the same `isClosed_iInter`
  idiom, with the membership hypothesis as the inner binder).

**Convention pins (byte-checked against `RamareWindows`, no sign flip).**

* `ramQ H P Q v c t = Σ_{p ∈ ramQblock H P Q v} c p / p^{(1 : ℂ) + t·I}` — the `+it`
  convention, identical to `Decomp.primeBlockPoly`.  There is **no `−𝒯` flip** anywhere in
  this file: every `t` here is the same `t` the flat family and the seam row integrate over,
  and the graded sets are subsets of the same real line.
* `ramQblock H P Q v` is the **half-open** fiber `exp(v/H) ≤ p < exp((v+1)/H)`
  (`RamareWindows` :56–59) — the `⌊H log p⌋ = v` fiber, so the blocks partition the prime
  range.  `BlockSmallG` quotes it through `ramQ` and never re-derives an interval, so the
  half-open convention is inherited verbatim.
* `Hseq j` is the block's own `H_j` and `αseq j` its own `α_j`: both are per-`j` sequences,
  not global constants (MR's `H_j`/`α_j` vary with the block, which is exactly what the flat
  `δ : ℝ` could not express).

## The stones

* **G0a** — `BlockSmallG`, `TsetG`, `UsetG`, `seamTtotG`; `TsetG_unique`,
  `TsetG_disjoint`, `TsetG_UsetG_disjoint`, `exists_TsetG_or_mem_UsetG`.  Mirrors
  `Decomp` :219–276 at the graded predicate.
* **G0b** — `isClosed_blockSmallG`, `measurableSet_UsetG`, `measurableSet_TsetG`,
  `measurableSet_seamTtotG`, `sdiff_biUnion_TsetG`, `seam_T_additivityG`,
  `seam_TU_splitG`.  Mirrors `SeamSplit` :414–546.  `far_leg_collapse` (`SeamSplit` :559)
  is **predicate-free** and is reused verbatim — no graded twin is needed or wanted.
* **G0c** — `prop_A3_T1_row_split_weightedG` (+ the crude twin).  Mirrors
  `SeamBallWeighted` :248/:283.  `annulus_ball_far_split` and `ball_leg_of_sup_weighted` are
  predicate-free and are reused verbatim; ONLY the `Uset`/`seamTtot` slots move to the
  G-family.  The `hU` binder and the `hSup` binder are unchanged in shape.

## What is NOT here

`G1a` (graded thinness — cleaner than flat: the pigeonhole disappears, `log V / log base =
α_J` exactly) and `G1b` (the V-split hU replay, **HELD** behind the far-arm repair R1/R2/R3,
so the ~1,000-line replay is not paid twice), and all of `G2`–`G5` (§8's interior).  As in
the flat family, `hSup` and `hU` are named binders at the row.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 eq (21), §8; MRT v3 Appendix A.
-/

namespace Salt.MR

open MeasureTheory

/-! ## §1 — G0a: the graded predicate and the graded partition family -/

/-- **Graded block smallness at index `j`** (MR eq (21)).  Every block polynomial
`Q_{v,H_j}(1+it)` of the block-index range `I_j = ramI H_j P_j Q_j` obeys the
`v`-GRADED threshold `e^{−α_j v / H_j}`:

  `∀ v ∈ ramI (Hseq j) (Pseq j) (Qseq j), ‖ramQ (Hseq j) (Pseq j) (Qseq j) v f t‖`
  `  ≤ exp(−(αseq j)·v / Hseq j)`.

This is the honest replacement for `Decomp.BlockSmallAt`'s flat `δ`: the threshold decays
with the block's own base `e^{v/H_j}` (i.e. it is `≈ p^{−α_j}` on the block), which is what
pays the co-factor mass in MR (23) and calibrates the Lemma-8 exponent to `2α_j`.  The
quantifier ranges over a `Finset`, not an arbitrary subdivision family. -/
def BlockSmallG (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (j : ℕ)
    (t : ℝ) : Prop :=
  ∀ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
    ‖ramQ (Hseq j) (Pseq j) (Qseq j) v f t‖ ≤ Real.exp (-(αseq j) * (v : ℝ) / Hseq j)

/-- **`𝒯ⱼ` at the graded threshold**: `t ∈ TsetG … j` iff `j` is the *smallest* index in
`[1,J]` at which the graded bound (21) holds across the whole block range.  Same shape as
`Decomp.Tset`; only the smallness predicate is graded. -/
def TsetG (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J j : ℕ) : Set ℝ :=
  {t | 1 ≤ j ∧ j ≤ J ∧ BlockSmallG f Pseq Qseq Hseq αseq j t ∧
       ∀ i, 1 ≤ i → i < j → ¬ BlockSmallG f Pseq Qseq Hseq αseq i t}

/-- **`𝒰` at the graded threshold**: `t ∈ UsetG … J` iff *no* index `j ∈ [1,J]` carries the
graded bound (21).  Same shape as `Decomp.Uset`. -/
def UsetG (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J : ℕ) : Set ℝ :=
  {t | ∀ j, 1 ≤ j → j ≤ J → ¬ BlockSmallG f Pseq Qseq Hseq αseq j t}

section Structural

variable {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ} {J : ℕ}

/-- The graded `𝒯ⱼ` are determined by the *smallest* graded-small index, so `t` lies in at
most one of them. -/
lemma TsetG_unique {j j' : ℕ} {t : ℝ}
    (hj : t ∈ TsetG f Pseq Qseq Hseq αseq J j)
    (hj' : t ∈ TsetG f Pseq Qseq Hseq αseq J j') : j = j' := by
  obtain ⟨hj1, _, hjs, hjm⟩ := hj
  obtain ⟨hj'1, _, hj's, hj'm⟩ := hj'
  by_contra hne
  rcases Nat.lt_or_ge j j' with h | h
  · exact hj'm j hj1 h hjs
  · rcases Nat.lt_or_ge j' j with h' | h'
    · exact hjm j' hj'1 h' hj's
    · omega

/-- The graded `𝒯ⱼ` are pairwise disjoint. -/
lemma TsetG_disjoint {j j' : ℕ} (h : j ≠ j') :
    Disjoint (TsetG f Pseq Qseq Hseq αseq J j) (TsetG f Pseq Qseq Hseq αseq J j') := by
  rw [Set.disjoint_left]
  exact fun t ht ht' => h (TsetG_unique ht ht')

/-- Each graded `𝒯ⱼ` is disjoint from the graded `𝒰`. -/
lemma TsetG_UsetG_disjoint {j : ℕ} :
    Disjoint (TsetG f Pseq Qseq Hseq αseq J j) (UsetG f Pseq Qseq Hseq αseq J) := by
  rw [Set.disjoint_left]
  rintro t ⟨hj1, hjJ, hjs, _⟩ hU
  exact hU j hj1 hjJ hjs

/-- **Exhaustiveness of the graded split.**  Every real lies in some graded `𝒯ⱼ` or in the
graded `𝒰` — `Nat.find` on the graded predicate, exactly as in the flat family (the range
restriction of the seam annulus is imposed separately). -/
lemma exists_TsetG_or_mem_UsetG (t : ℝ) :
    (∃ j, t ∈ TsetG f Pseq Qseq Hseq αseq J j) ∨ t ∈ UsetG f Pseq Qseq Hseq αseq J := by
  classical
  by_cases h : ∃ j, 1 ≤ j ∧ j ≤ J ∧ BlockSmallG f Pseq Qseq Hseq αseq j t
  · left
    have hspec := Nat.find_spec h
    refine ⟨Nat.find h, hspec.1, hspec.2.1, hspec.2.2, ?_⟩
    intro i hi1 hij hsmall
    have hiJ : i ≤ J := by have := hspec.2.1; omega
    exact (Nat.find_min h hij) ⟨hi1, hiJ, hsmall⟩
  · right
    exact fun j hj1 hjJ hsmall => h ⟨j, hj1, hjJ, hsmall⟩

end Structural

/-! ## §2 — G0b: measurability and the graded `𝒯tot / 𝒰` splits -/

/-- **`BlockSmallG`'s set is CLOSED.**  It is an intersection — over the FINITE block index
set `ramI (Hseq j) (Pseq j) (Qseq j)` — of closed sublevel sets of the continuous
`‖ramQ …‖` (`continuous_ramQ`).  Finiteness is not even needed for closedness (the flat file
gets by with an arbitrary intersection); it is recorded here because it is what makes the
measurability step below cheaper than its flat counterpart. -/
lemma isClosed_blockSmallG (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (j : ℕ) :
    IsClosed {t : ℝ | BlockSmallG f Pseq Qseq Hseq αseq j t} := by
  have hset : {t : ℝ | BlockSmallG f Pseq Qseq Hseq αseq j t}
      = ⋂ v : ℕ, ⋂ (_ : v ∈ ramI (Hseq j) (Pseq j) (Qseq j)),
          {t : ℝ | ‖ramQ (Hseq j) (Pseq j) (Qseq j) v f t‖
            ≤ Real.exp (-(αseq j) * (v : ℝ) / Hseq j)} := by
    ext t
    simp only [BlockSmallG, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hset]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    isClosed_le (continuous_ramQ (Hseq j) (Pseq j) (Qseq j) v f).norm continuous_const

/-- The graded `𝒰` is measurable (a countable intersection — over `j ∈ [1,J]` — of the open
complements of the closed `BlockSmallG` sets). -/
lemma measurableSet_UsetG (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J : ℕ) :
    MeasurableSet (UsetG f Pseq Qseq Hseq αseq J) := by
  have hset : UsetG f Pseq Qseq Hseq αseq J
      = ⋂ j ∈ Set.Icc 1 J, {t : ℝ | BlockSmallG f Pseq Qseq Hseq αseq j t}ᶜ := by
    ext t
    simp only [UsetG, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff, Set.mem_Icc]
    exact ⟨fun h j hj => h j hj.1 hj.2, fun h j hj1 hj2 => h j ⟨hj1, hj2⟩⟩
  rw [hset]
  exact MeasurableSet.biInter (Set.to_countable _)
    (fun j _ => (isClosed_blockSmallG f Pseq Qseq Hseq αseq j).measurableSet.compl)

/-- The graded `𝒯ⱼ` is measurable: for `1 ≤ j ≤ J` it is the closed `BlockSmallG` set
intersected with the (countably many) open complements at the smaller indices `i < j`;
outside that range it is empty. -/
lemma measurableSet_TsetG (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J j : ℕ) :
    MeasurableSet (TsetG f Pseq Qseq Hseq αseq J j) := by
  by_cases hj : 1 ≤ j ∧ j ≤ J
  · have hset : TsetG f Pseq Qseq Hseq αseq J j
        = {t : ℝ | BlockSmallG f Pseq Qseq Hseq αseq j t}
          ∩ ⋂ i ∈ Set.Ico 1 j, {t : ℝ | BlockSmallG f Pseq Qseq Hseq αseq i t}ᶜ := by
      ext t
      simp only [TsetG, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Set.mem_Ico]
      constructor
      · rintro ⟨-, -, hs, hm⟩
        exact ⟨hs, fun i hi => hm i hi.1 hi.2⟩
      · rintro ⟨hs, hm⟩
        exact ⟨hj.1, hj.2, hs, fun i h1 h2 => hm i ⟨h1, h2⟩⟩
    rw [hset]
    exact (isClosed_blockSmallG f Pseq Qseq Hseq αseq j).measurableSet.inter
      (MeasurableSet.biInter (Set.to_countable _)
        (fun i _ => (isClosed_blockSmallG f Pseq Qseq Hseq αseq i).measurableSet.compl))
  · have hset : TsetG f Pseq Qseq Hseq αseq J j = ∅ := by
      ext t
      simp only [TsetG, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hj
    rw [hset]
    exact MeasurableSet.empty

/-- **`𝒯tot` at the graded threshold** — the union of the graded `𝒯ⱼ` over `j ∈ [1,J]`.  As
in the flat family the union is kept as ONE object: `J` grows with `X`, so a `J`-fold sum of
interval bounds would be a false economy (catch #253). -/
def seamTtotG (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J : ℕ) : Set ℝ :=
  ⋃ j ∈ Finset.Icc 1 J, TsetG f Pseq Qseq Hseq αseq J j

lemma measurableSet_seamTtotG (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J : ℕ) :
    MeasurableSet (seamTtotG f Pseq Qseq Hseq αseq J) :=
  Finset.measurableSet_biUnion _
    (fun j _ => measurableSet_TsetG f Pseq Qseq Hseq αseq J j)

/-- **The graded annulus-restricted exhaustiveness.**  Off the graded `𝒯tot`, every point
lies in the graded `𝒰`: `R \ 𝒯totG = R ∩ 𝒰G`, for an arbitrary `R`. -/
lemma sdiff_biUnion_TsetG (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J : ℕ)
    (R : Set ℝ) :
    R \ seamTtotG f Pseq Qseq Hseq αseq J = R ∩ UsetG f Pseq Qseq Hseq αseq J := by
  have hcover : ∀ t : ℝ, t ∉ seamTtotG f Pseq Qseq Hseq αseq J ↔
      t ∈ UsetG f Pseq Qseq Hseq αseq J := by
    intro t
    constructor
    · intro hnot
      rcases exists_TsetG_or_mem_UsetG (f := f) (Pseq := Pseq) (Qseq := Qseq) (Hseq := Hseq)
        (αseq := αseq) (J := J) t with ⟨j, hj⟩ | hU
      · exact absurd (Set.mem_biUnion (Finset.mem_Icc.mpr ⟨hj.1, hj.2.1⟩) hj) hnot
      · exact hU
    · intro hU hmem
      obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.mp hmem
      exact Set.disjoint_left.mp TsetG_UsetG_disjoint hj hU
  ext t
  constructor
  · rintro ⟨htR, hnot⟩
    exact ⟨htR, (hcover t).mp hnot⟩
  · rintro ⟨htR, htU⟩
    exact ⟨htR, (hcover t).mpr htU⟩

/-- **The disjoint additivity over the graded `𝒯ⱼ`** (`seam_T_additivityG`).  The granular
form, via `MeasureTheory.integral_biUnion_finset` fed by `TsetG_disjoint`.  The seam row
consumes the UNION form (`seam_TU_splitG`) instead, so no `J`-factor is ever created
(catch #253). -/
theorem seam_T_additivityG {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ} {J : ℕ}
    {F : ℝ → ℝ} (hF : Continuous F) {R : Set ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hR : MeasurableSet R) (hRsub : R ⊆ Set.Icc (-T) T) :
    (∫ t in R ∩ seamTtotG f Pseq Qseq Hseq αseq J, F t)
      = ∑ j ∈ Finset.Icc 1 J, ∫ t in R ∩ TsetG f Pseq Qseq Hseq αseq J j, F t := by
  rw [seamTtotG, Set.inter_iUnion₂]
  refine integral_biUnion_finset _
    (fun j _ => hR.inter (measurableSet_TsetG f Pseq Qseq Hseq αseq J j)) ?_
    (fun j _ => integrableOn_of_continuous_subset_Icc hF hT
      (hR.inter (measurableSet_TsetG f Pseq Qseq Hseq αseq J j))
      (fun _ ht => hRsub ht.1))
  intro i _ j _ hij
  exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right (TsetG_disjoint hij)

/-- **The two-set graded `𝒯tot / 𝒰` split of a bounded piece** (`seam_TU_splitG`).  For any
measurable `R ⊆ [-T,T]`,

  `∫_R F = ∫_{R ∩ 𝒯totG} F + ∫_{R ∩ 𝒰G} F`.

The union form is what the graded seam row consumes: the whole graded `𝒯`-side is bounded by
ONE monotonicity into `[-T,T]`, so no factor of `J` (which grows with `X`) appears. -/
theorem seam_TU_splitG {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ} {J : ℕ}
    {F : ℝ → ℝ} (hF : Continuous F) {R : Set ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hR : MeasurableSet R) (hRsub : R ⊆ Set.Icc (-T) T) :
    (∫ t in R, F t)
      = (∫ t in R ∩ seamTtotG f Pseq Qseq Hseq αseq J, F t)
        + ∫ t in R ∩ UsetG f Pseq Qseq Hseq αseq J, F t := by
  have hint : IntegrableOn F R volume :=
    integrableOn_of_continuous_subset_Icc hF hT hR hRsub
  have hsplit := integral_inter_add_sdiff (μ := volume) (f := F)
    (measurableSet_seamTtotG f Pseq Qseq Hseq αseq J) hint
  rw [sdiff_biUnion_TsetG f Pseq Qseq Hseq αseq J R] at hsplit
  exact hsplit.symm

/-! ## §3 — G0c: the seam row at the graded partition -/

/-- **G0c — THE GRADED SEAM ROW (`prop_A3_T1_row_split_weightedG`).**
`SeamBallWeighted.prop_A3_T1_row_split_weighted` with the flat `𝒯tot`/`𝒰` slots replaced by
the graded family:

  `∫_{Ann} ‖spoly N a t‖² ≤ 8·S² + ∫_{(Ann\ball) ∩ 𝒯totG} ‖spoly N a t‖² + U`.

**What moved and what did not.**  The ball machinery is PREDICATE-FREE and is reused
verbatim: `annulus_ball_far_split` (the two-set split, stated at a free `t₁`) and
`ball_leg_of_sup_weighted` (the weighted `8S²` leg — no `r`-factor, and no window fact about
`t₁`, which stays a free parameter with the centre semantics at the consumer).  ONLY the
partition slots changed: `Uset fb Pseq Qseq δ Jb ↝ UsetG fb Pseq Qseq Hseq αseq Jb` in the
`hU` binder and `seamTtot ↝ seamTtotG` in the conclusion, the flat `δ : ℝ` being replaced by
the pair of sequences `Hseq αseq : ℕ → ℝ` (MR (21)'s per-block `H_j`, `α_j`).

`hSup` is untouched (annulus-restricted, H-0 window-legal); `hU` is untouched in shape — its
graded supply is `G1a`/`G1b`, and `G1b` is HELD behind the far-arm repair. -/
theorem prop_A3_T1_row_split_weightedG
    (a : ℕ → ℂ) (N : ℕ)
    (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (Jb : ℕ)
    (X T t₁ S U : ℝ)
    (hL : 0 ≤ Real.log X) (hT : 0 ≤ T)
    (hX : 0 < X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hSup : ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - t₁| ≤ seamRad X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|))
    (hU : (∫ t in (seamAnn X T \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jb,
        ‖spoly N a t‖ ^ 2) ≤ U) :
    (∫ t in seamAnn X T, ‖spoly N a t‖ ^ 2)
      ≤ 8 * S ^ 2
        + (∫ t in (seamAnn X T \ seamBall X t₁) ∩ seamTtotG fb Pseq Qseq Hseq αseq Jb,
            ‖spoly N a t‖ ^ 2) + U := by
  have hcont : Continuous fun t : ℝ => ‖spoly N a t‖ ^ 2 :=
    (continuous_spoly N a).norm.pow 2
  have hR : MeasurableSet (seamAnn X T \ seamBall X t₁) :=
    (measurableSet_seamAnn X T).diff (measurableSet_seamBall X t₁)
  have hRsub : seamAnn X T \ seamBall X t₁ ⊆ Set.Icc (-T) T :=
    fun _ ht => seamAnn_subset_Icc X T ht.1
  -- 1. the ball / far split (landed, predicate-free, `t₁`-free)
  have h1 := annulus_ball_far_split (F := fun t : ℝ => ‖spoly N a t‖ ^ 2) hcont X T t₁ hT
  -- 2. the WEIGHTED ball leg (landed, predicate-free)
  have h2 := ball_leg_of_sup_weighted hX hXN hN2 hT hL hsupp hSup
  -- 3. the GRADED `𝒯tot / 𝒰` split of the far part
  have h3 := seam_TU_splitG (f := fb) (Pseq := Pseq) (Qseq := Qseq) (Hseq := Hseq)
    (αseq := αseq) (J := Jb) (F := fun t : ℝ => ‖spoly N a t‖ ^ 2) hcont hT hR hRsub
  linarith [h1, h2, h3, hU]

/-- **G0c′ — the crude graded far leg (`prop_A3_T1_row_split_weightedG_crude`).**  The graded
row with the `𝒯`-leg collapsed by the landed, predicate-free `far_leg_collapse` (ONE
monotonicity, never a `Σⱼ` of `J` copies — catch #253).  Deliberately crude, as in the flat
`_crude` clones: at that collapse the statement no longer beats the trivial
`Ann ⊆ [-T,T]` monotonicity, and it is kept only so a consumer can read the row's
`T`-structure off one line. -/
theorem prop_A3_T1_row_split_weightedG_crude
    (a : ℕ → ℂ) (N : ℕ)
    (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (Jb : ℕ)
    (X T t₁ S U : ℝ)
    (hL : 0 ≤ Real.log X) (hT : 0 ≤ T)
    (hX : 0 < X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hSup : ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - t₁| ≤ seamRad X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|))
    (hU : (∫ t in (seamAnn X T \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jb,
        ‖spoly N a t‖ ^ 2) ≤ U) :
    (∫ t in seamAnn X T, ‖spoly N a t‖ ^ 2)
      ≤ 8 * S ^ 2 + (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2) + U := by
  have hcont : Continuous fun t : ℝ => ‖spoly N a t‖ ^ 2 :=
    (continuous_spoly N a).norm.pow 2
  have hRsub : seamAnn X T \ seamBall X t₁ ⊆ Set.Icc (-T) T :=
    fun _ ht => seamAnn_subset_Icc X T ht.1
  have hfar : (∫ t in (seamAnn X T \ seamBall X t₁) ∩ seamTtotG fb Pseq Qseq Hseq αseq Jb,
      ‖spoly N a t‖ ^ 2) ≤ ∫ t in (-T)..T, ‖spoly N a t‖ ^ 2 :=
    far_leg_collapse hcont (fun _ => sq_nonneg _) hT (fun _ ht => hRsub ht.1)
  have hrow := prop_A3_T1_row_split_weightedG a N fb Pseq Qseq Hseq αseq Jb X T t₁ S U
    hL hT hX hXN hN2 hsupp hSup hU
  linarith [hrow, hfar]

end Salt.MR
