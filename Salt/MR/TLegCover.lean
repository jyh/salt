/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TLegPreamble

/-!
# TLegCover — MR §8.2's covering + the `ℓ`-th-power normalization (ROUTE G, `G4a`/`G4b`)

`docs/exploration/hsup-design.md` ⟦V6⟧'s Route-G ladder, nodes `G4a` (the covering /
pigeonhole) and `G4b` (the threshold normalization), on top of `G2`
(`Salt.MR.TLegPreamble`) and `G3` (`Salt.MR.TLegE1`).  Everything here is **parallel and
additive**: no landed statement is touched.

MR §8.2 (p.25–27) prices the level-`j` pieces of eq (24) for `2 ≤ j ≤ J`.  The device has
three moves; this file lands the first two (the third — the moment `Lemma 13` insertion — is
`G4c`/`G4d`, a sibling lane and NOT imported here):

1. **The level-`(j−1)` violation** (`G4a`-i).  `t ∈ 𝒯ⱼ` says graded smallness (21) HOLDS at
   `j` and FAILS at every level below.  In particular it fails at `j − 1`, which names a
   block index `r ∈ I_{j−1}` with

     `e^{−α_{j−1}·r/H_{j−1}} < ‖Q_{r,H_{j−1}}(1+it)‖`.

   This is `G1a`'s `not_blockSmallG_witness` read at the SHIFTED level; the uniqueness clause
   of `G0`'s `TsetG` (`∀ i, 1 ≤ i → i < j → ¬ BlockSmallG … i t`) is what supplies it, and it
   is available exactly when `2 ≤ j` (at `j = 1` there is no level below — that is §8.1,
   node `G3`).

2. **The covering** (`G4a`-ii).  `𝒯ⱼ ⊆ ⋃_{r ∈ I_{j−1}} 𝒯_{j,r}` with
   `𝒯_{j,r} := 𝒯ⱼ ∩ {t : the r-violation}` — MR's own pigeonhole onto ONE `(j,r)` pair.  The
   cells are **not** disjoint (a `t` may violate at several `r`), so the union cost is the
   honest `#I_{j−1}`: `∫_{A ∩ 𝒯ⱼ} F ≤ Σ_{r ∈ I_{j−1}} ∫_{A ∩ 𝒯_{j,r}} F ≤ #I_{j−1}·B`
   whenever every cell is priced by `B`.  `#I_{j−1} ≤ H_{j−1} log Q_{j−1} + 1`
   (`USetPrice.ramI_card_le`) is the consumer's conversion; nothing is absorbed into a
   numeral here (law #253).

3. **The normalization** (`G4b`).  On `𝒯_{j,r}` the violation is a strict `>`, so for ANY
   `ℓ : ℕ`

     `1 ≤ (‖Q_{r,H_{j−1}}(1+it)‖·e^{α_{j−1}r/H_{j−1}})^{2ℓ}
        = ‖Q_{r,H_{j−1}}(1+it)‖^{2ℓ}·e^{2ℓα_{j−1}r/H_{j−1}}`,

   the moment device's ENTRY TICKET: the factor `1` under `∫_{A}‖F(1+it)‖²` may be replaced
   by the `2ℓ`-th power of the block polynomial at the price of the explicit exponential.
   `ℓ` is free here — MR's `ℓ_{j,r} = ⌈(v/H_j)/(r/H_{j−1})⌉` is a CONSUMER pin (`G4d`), not
   a hypothesis of the entry ticket, so no arithmetic of `ℓ` rides these statements.

## The stones

* **C-1** — `TsetG_level_ge_two_witness` (+ `not_blockSmallG_pred_of_mem_TsetG`,
  `ramI_pred_nonempty_of_mem_TsetG`).
* **C-2** — `TsetGr` (the `(j,r)`-cell), `measurableSet_TsetGr`,
  `TsetG_subset_biUnion_TsetGr`, and the union cost in both forms
  (`integral_TsetG_le_sum_TsetGr`, `integral_TsetG_le_card_mul`), on the generic
  covering lemma `setIntegral_le_finset_sum_of_cover`.
* **C-3** — `one_le_normalized_of_mem_TsetGr`, `one_le_normalized_pow` (at any `ℓ`), and the
  split form `one_le_ramQ_pow_mul_exp` the integral step consumes.
* **C-4** — `cell_integral_normalized` (generic `A`) and `cell_integral_normalized_annulus`
  (at the row's own window `A = (Ann ∖ ball) ∩ 𝒯_{j,r}`).

## Conventions and pins (law #253, byte-checked)

* **The coefficient seam** (`G3`'s composition finding 1).  The graded set is instantiated at
  the SAME coefficient `c` the block polynomial carries — `TsetG c …` against
  `ramQ … r c t`.  The seam is closed IN THE STATEMENT, never left to the consumer; with any
  other datum neither the violation nor the normalization bites.
* **The shifted level is `j − 1` (ℕ-subtraction), gated by `2 ≤ j`.**  Every statement that
  needs the level below carries `hj : 2 ≤ j` explicitly; `TsetGr` itself is defined at `j − 1`
  unconditionally (at `j ≤ 1` it degenerates to a level-0 cell and no lemma here claims
  anything about it).
* **No negation.**  `G0`/`G1a`/`G2`/`G3`'s posture is kept: every `t` is the ordinate the seam
  row integrates over; no `dpoly`, no `Finset.image (−·)`, no `−𝒯` bridge appears.
* **Non-degeneracy is FREE here.**  `¬ BlockSmallG` at `j − 1` cannot hold over an empty block
  range, so membership in `𝒯ⱼ` at `2 ≤ j` certifies `I_{j−1} ≠ ∅` by itself
  (`ramI_pred_nonempty_of_mem_TsetG`) — the `G0` empty-block vacuity trap is discharged, not
  assumed.
* **The cells are not disjoint** — see move 2.  Disjointifying (taking the least violating
  `r`) would buy a factor `#I_{j−1}` but is NOT what MR does, and the graded page's exponent
  is calibrated to the union cost; the honest cost is stated.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 eq (21), §8.2 pp.25–27;
`docs/sources/mr_extract.md` §2.7; `docs/exploration/hsup-design.md` ⟦V6⟧ (the Route-G
ladder).
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §1 — C-1: the level-`(j−1)` violation witness -/

/-- **The uniqueness clause of `G0`'s `TsetG`, read at the level below.**  `t ∈ 𝒯ⱼ` carries
`∀ i, 1 ≤ i → i < j → ¬ BlockSmallG … i t`; at `2 ≤ j` the index `i = j − 1` is legal, so
graded smallness FAILS at `j − 1`.  Pure projection — no `push_neg`, no unfolding at the
consumer. -/
lemma not_blockSmallG_pred_of_mem_TsetG {c : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ}
    {J j : ℕ} (hj : 2 ≤ j) {t : ℝ} (ht : t ∈ TsetG c Pseq Qseq Hseq αseq J j) :
    ¬ BlockSmallG c Pseq Qseq Hseq αseq (j - 1) t :=
  ht.2.2.2 (j - 1) (by omega) (by omega)

/-- **C-1 — the level-`(j−1)` witness (MR §8.2's opening move).**  For `2 ≤ j`, every
`t ∈ 𝒯ⱼ` names a block index `r ∈ I_{j−1}` at which MR (21) is VIOLATED at the level below:

  `exp(−α_{j−1}·r/H_{j−1}) < ‖Q_{r,H_{j−1}}(1+it)‖`.

The graded set is instantiated at the coefficient `c` the block polynomial carries (the
coefficient seam, closed in-statement).  This is `G1a`'s `not_blockSmallG_witness` at the
shifted level; the shift is exactly what `TsetG`'s uniqueness clause supplies. -/
theorem TsetG_level_ge_two_witness {c : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ}
    {J j : ℕ} (hj : 2 ≤ j) {t : ℝ} (ht : t ∈ TsetG c Pseq Qseq Hseq αseq J j) :
    ∃ r ∈ ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)),
      Real.exp (-(αseq (j - 1)) * (r : ℝ) / Hseq (j - 1))
        < ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ :=
  not_blockSmallG_witness (not_blockSmallG_pred_of_mem_TsetG hj ht)

/-- **The non-degeneracy pin, FREE.**  A violated `BlockSmallG` cannot live over an empty
block range, so an ordinate of `𝒯ⱼ` (`2 ≤ j`) certifies `I_{j−1} ≠ ∅` all by itself — the
`G0` empty-block vacuity trap needs no geometric hypothesis at this node. -/
lemma ramI_pred_nonempty_of_mem_TsetG {c : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ}
    {J j : ℕ} (hj : 2 ≤ j) {t : ℝ} (ht : t ∈ TsetG c Pseq Qseq Hseq αseq J j) :
    (ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).Nonempty :=
  ramI_nonempty_of_not_blockSmallG (not_blockSmallG_pred_of_mem_TsetG hj ht)

/-! ## §2 — C-2: the `(j,r)`-cell and the covering -/

/-- **`𝒯_{j,r}` — the `(j,r)`-cell of MR §8.2.**  The ordinates of `𝒯ⱼ` whose level-`(j−1)`
violation is realised at the specific block index `r`:

  `𝒯_{j,r} := 𝒯ⱼ ∩ {t : exp(−α_{j−1}·r/H_{j−1}) < ‖Q_{r,H_{j−1}}(1+it)‖}`.

The coefficient of the block polynomial is the datum `c` of the graded set itself (the
coefficient seam).  Defined at `j − 1` unconditionally; the covering below carries `2 ≤ j`. -/
def TsetGr (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J j r : ℕ) : Set ℝ :=
  TsetG c Pseq Qseq Hseq αseq J j ∩
    {t : ℝ | Real.exp (-(αseq (j - 1)) * (r : ℝ) / Hseq (j - 1))
      < ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖}

section Cell

variable {c : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ} {J j r : ℕ}

/-- The cell sits inside its level: `𝒯_{j,r} ⊆ 𝒯ⱼ`. -/
lemma TsetGr_subset_TsetG :
    TsetGr c Pseq Qseq Hseq αseq J j r ⊆ TsetG c Pseq Qseq Hseq αseq J j :=
  Set.inter_subset_left

/-- The defining violation of the cell, projected out. -/
lemma ramQ_violation_of_mem_TsetGr {t : ℝ} (ht : t ∈ TsetGr c Pseq Qseq Hseq αseq J j r) :
    Real.exp (-(αseq (j - 1)) * (r : ℝ) / Hseq (j - 1))
      < ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ := ht.2

end Cell

/-- The violation set is OPEN — a strict sublevel set of the continuous `‖ramQ …‖`
(`RamareWindows.continuous_ramQ`).  This is the `G0b` idiom (`isClosed_blockSmallG`) with the
inequality reversed, and it is what makes the cells measurable. -/
lemma isOpen_ramQ_violation (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (j r : ℕ) :
    IsOpen {t : ℝ | Real.exp (-(αseq (j - 1)) * (r : ℝ) / Hseq (j - 1))
      < ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖} :=
  isOpen_lt continuous_const
    (continuous_ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c).norm

/-- Each `(j,r)`-cell is measurable: `G0b`'s `measurableSet_TsetG` intersected with the open
violation set. -/
lemma measurableSet_TsetGr (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J j r : ℕ) :
    MeasurableSet (TsetGr c Pseq Qseq Hseq αseq J j r) :=
  (measurableSet_TsetG c Pseq Qseq Hseq αseq J j).inter
    (isOpen_ramQ_violation c Pseq Qseq Hseq αseq j r).measurableSet

/-- **C-2 — THE COVERING (MR §8.2's pigeonhole).**  For `2 ≤ j`,

  `𝒯ⱼ ⊆ ⋃_{r ∈ I_{j−1}} 𝒯_{j,r}`,

i.e. every level-`j` ordinate is caught by ONE `(j,r)` pair, the index `r` ranging over the
level-`(j−1)` block range.  Immediate from `C-1`: the witness IS the covering index. -/
theorem TsetG_subset_biUnion_TsetGr (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
    (J j : ℕ) (hj : 2 ≤ j) :
    TsetG c Pseq Qseq Hseq αseq J j
      ⊆ ⋃ r ∈ ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)),
          TsetGr c Pseq Qseq Hseq αseq J j r := by
  intro t ht
  obtain ⟨r, hr, hviol⟩ := TsetG_level_ge_two_witness hj ht
  exact Set.mem_biUnion hr ⟨ht, hviol⟩

/-! ### The union cost

The cells are NOT disjoint, so the price of the covering is a genuine subadditivity: a finite
cover of a measurable piece costs the SUM of the pieces' integrals (and hence `#I_{j−1}`
times a uniform cell bound).  The generic step is proved once, by `Finset` induction on the
cover, splitting off one cell at a time with `integral_inter_add_sdiff` — the leftover
`E ∖ U a` is measurable, still inside `[−T,T]`, and covered by the rest. -/

/-- **The finite-cover subadditivity of a set integral** (nonnegative continuous integrand).
If `E ⊆ [−T,T]` is measurable and covered by `⋃_{r ∈ s} U r` with each `U r` measurable, then

  `∫_E F ≤ Σ_{r ∈ s} ∫_{E ∩ U r} F`.

No disjointness is asked (that is the point: `Finset.card_biUnion_le`'s posture, in the
measure-theoretic register).  Integrability comes from continuity on `[−T,T]`
(`SeamSplit.integrableOn_of_continuous_subset_Icc`), exactly as in the flat and graded seam
files. -/
lemma setIntegral_le_finset_sum_of_cover {F : ℝ → ℝ} (hF : Continuous F)
    (hF0 : ∀ t, 0 ≤ F t) {T : ℝ} (hT : 0 ≤ T) (U : ℕ → Set ℝ)
    (hU : ∀ r, MeasurableSet (U r)) :
    ∀ (s : Finset ℕ) (E : Set ℝ), MeasurableSet E → E ⊆ Set.Icc (-T) T →
      E ⊆ (⋃ r ∈ s, U r) → (∫ t in E, F t) ≤ ∑ r ∈ s, ∫ t in E ∩ U r, F t := by
  intro s
  induction s using Finset.induction with
  | empty =>
      intro E _ _ hcov
      have hE : E = ∅ := Set.subset_empty_iff.mp (by simpa using hcov)
      simp [hE]
  | insert a s ha ih =>
      intro E hEm hEsub hcov
      have hEint : IntegrableOn F E volume :=
        integrableOn_of_continuous_subset_Icc hF hT hEm hEsub
      have hsplit : (∫ t in E ∩ U a, F t) + (∫ t in E \ U a, F t) = ∫ t in E, F t :=
        integral_inter_add_sdiff (hU a) hEint
      have hDm : MeasurableSet (E \ U a) := hEm.diff (hU a)
      have hDsub : E \ U a ⊆ Set.Icc (-T) T := fun t ht => hEsub ht.1
      have hDcov : E \ U a ⊆ ⋃ r ∈ s, U r := by
        intro t ht
        obtain ⟨q, hqs, htq⟩ := Set.mem_iUnion₂.mp (hcov ht.1)
        rcases Finset.mem_insert.mp hqs with rfl | hqs'
        · exact absurd htq ht.2
        · exact Set.mem_biUnion hqs' htq
      have hIH := ih (E \ U a) hDm hDsub hDcov
      have hmono : ∀ q ∈ s, (∫ t in (E \ U a) ∩ U q, F t) ≤ ∫ t in E ∩ U q, F t := by
        intro q _
        have hbig : IntegrableOn F (E ∩ U q) volume :=
          integrableOn_of_continuous_subset_Icc hF hT (hEm.inter (hU q))
            (fun t ht => hEsub ht.1)
        have hsub : (E \ U a) ∩ U q ⊆ E ∩ U q := fun t ht => ⟨ht.1.1, ht.2⟩
        exact setIntegral_mono_set hbig (Filter.Eventually.of_forall (fun t => hF0 t))
          hsub.eventuallyLE
      have hsum := Finset.sum_le_sum hmono
      rw [Finset.sum_insert ha]
      linarith [hsplit, hIH, hsum]

/-- The cell already lies in its level, so intersecting a window with `𝒯ⱼ` first is free:
`(A ∩ 𝒯ⱼ) ∩ 𝒯_{j,r} = A ∩ 𝒯_{j,r}`. -/
lemma inter_TsetG_inter_TsetGr (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
    (J j r : ℕ) (A : Set ℝ) :
    (A ∩ TsetG c Pseq Qseq Hseq αseq J j) ∩ TsetGr c Pseq Qseq Hseq αseq J j r
      = A ∩ TsetGr c Pseq Qseq Hseq αseq J j r := by
  ext t
  constructor
  · rintro ⟨⟨hA, -⟩, hcell⟩
    exact ⟨hA, hcell⟩
  · rintro ⟨hA, hcell⟩
    exact ⟨⟨hA, TsetGr_subset_TsetG hcell⟩, hcell⟩

/-- **C-2 (the union cost, sum form).**  On any measurable window `A ⊆ [−T,T]` and for
`2 ≤ j`, the level-`j` integral of a nonnegative continuous `F` is at most the SUM of the
cell integrals:

  `∫_{A ∩ 𝒯ⱼ} F ≤ Σ_{r ∈ I_{j−1}} ∫_{A ∩ 𝒯_{j,r}} F`.

This is the honest §8.2 accounting: no disjointness is claimed or used. -/
theorem integral_TsetG_le_sum_TsetGr (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
    (J j : ℕ) (hj : 2 ≤ j) {F : ℝ → ℝ} (hF : Continuous F) (hF0 : ∀ t, 0 ≤ F t)
    {T : ℝ} (hT : 0 ≤ T) (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T) :
    (∫ t in A ∩ TsetG c Pseq Qseq Hseq αseq J j, F t)
      ≤ ∑ r ∈ ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)),
          ∫ t in A ∩ TsetGr c Pseq Qseq Hseq αseq J j r, F t := by
  have hEm : MeasurableSet (A ∩ TsetG c Pseq Qseq Hseq αseq J j) :=
    hAm.inter (measurableSet_TsetG c Pseq Qseq Hseq αseq J j)
  have hEsub : A ∩ TsetG c Pseq Qseq Hseq αseq J j ⊆ Set.Icc (-T) T := fun t ht => hAsub ht.1
  have hcov : A ∩ TsetG c Pseq Qseq Hseq αseq J j
      ⊆ ⋃ r ∈ ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)),
          TsetGr c Pseq Qseq Hseq αseq J j r :=
    fun t ht => TsetG_subset_biUnion_TsetGr c Pseq Qseq Hseq αseq J j hj ht.2
  have hstep := setIntegral_le_finset_sum_of_cover hF hF0 hT
    (fun r => TsetGr c Pseq Qseq Hseq αseq J j r)
    (fun r => measurableSet_TsetGr c Pseq Qseq Hseq αseq J j r)
    (ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)))
    (A ∩ TsetG c Pseq Qseq Hseq αseq J j) hEm hEsub hcov
  refine le_trans hstep (le_of_eq (Finset.sum_congr rfl (fun r _ => ?_)))
  rw [inter_TsetG_inter_TsetGr]

/-- **C-2 (the union cost, `#I_{j−1}` form) — the shape §8.2 consumes.**  A uniform cell
bound `B` on the level-`(j−1)` block range prices the whole level at `#I_{j−1}·B`:

  `(∀ r ∈ I_{j−1}, ∫_{A ∩ 𝒯_{j,r}} F ≤ B)  ⟹  ∫_{A ∩ 𝒯ⱼ} F ≤ #I_{j−1}·B`.

The block count is left as `#I_{j−1}` (law #253): `USetPrice.ramI_card_le` converts it to
`H_{j−1} log Q_{j−1} + 1` at the consumer, where the `H`-pins are known. -/
theorem integral_TsetG_le_card_mul (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
    (J j : ℕ) (hj : 2 ≤ j) {F : ℝ → ℝ} (hF : Continuous F) (hF0 : ∀ t, 0 ≤ F t)
    {T : ℝ} (hT : 0 ≤ T) (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T)
    (B : ℝ) (hcell : ∀ r ∈ ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)),
      (∫ t in A ∩ TsetGr c Pseq Qseq Hseq αseq J j r, F t) ≤ B) :
    (∫ t in A ∩ TsetG c Pseq Qseq Hseq αseq J j, F t)
      ≤ ((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ) * B := by
  refine le_trans
    (integral_TsetG_le_sum_TsetGr c Pseq Qseq Hseq αseq J j hj hF hF0 hT A hAm hAsub) ?_
  refine le_trans (Finset.sum_le_sum hcell) (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ## §3 — C-3: the `ℓ`-th-power normalization (the moment device's entry ticket) -/

/-- The threshold, normalized: on `𝒯_{j,r}` the product of the block polynomial with the
INVERSE threshold is at least `1`.  The whole content of `G4b`, before any power is taken:
the violation `e^{−α_{j−1}r/H_{j−1}} < ‖Q_{r,H_{j−1}}‖` multiplied by the positive
`e^{α_{j−1}r/H_{j−1}}`. -/
lemma one_le_normalized_of_mem_TsetGr {c : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ}
    {J j r : ℕ} {t : ℝ} (ht : t ∈ TsetGr c Pseq Qseq Hseq αseq J j r) :
    1 ≤ ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖
        * Real.exp (αseq (j - 1) * (r : ℝ) / Hseq (j - 1)) := by
  have hviol := ramQ_violation_of_mem_TsetGr ht
  have hpos : (0 : ℝ) < Real.exp (αseq (j - 1) * (r : ℝ) / Hseq (j - 1)) := Real.exp_pos _
  have hmul := mul_lt_mul_of_pos_right hviol hpos
  have heq : Real.exp (-(αseq (j - 1)) * (r : ℝ) / Hseq (j - 1))
      * Real.exp (αseq (j - 1) * (r : ℝ) / Hseq (j - 1)) = 1 := by
    rw [← Real.exp_add]
    have hz : -(αseq (j - 1)) * (r : ℝ) / Hseq (j - 1)
        + αseq (j - 1) * (r : ℝ) / Hseq (j - 1) = 0 := by ring
    rw [hz, Real.exp_zero]
  linarith [hmul, heq]

/-- **C-3 — the normalization at ANY `ℓ`.**  On `𝒯_{j,r}`,

  `1 ≤ (‖Q_{r,H_{j−1}}(1+it)‖·e^{α_{j−1}r/H_{j−1}})^{2ℓ}`  for every `ℓ : ℕ`.

`ℓ` is entirely free: MR's `ℓ_{j,r} = ⌈(v/H_j)/(r/H_{j−1})⌉` is a consumer pin (`G4d`), so no
arithmetic of `ℓ` rides this statement. -/
theorem one_le_normalized_pow {c : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ}
    {J j r : ℕ} {t : ℝ} (ht : t ∈ TsetGr c Pseq Qseq Hseq αseq J j r) (ℓ : ℕ) :
    1 ≤ (‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖
          * Real.exp (αseq (j - 1) * (r : ℝ) / Hseq (j - 1))) ^ (2 * ℓ) :=
  one_le_pow₀ (one_le_normalized_of_mem_TsetGr ht)

/-- `exp(z)^{2ℓ} = exp(2ℓ·z)` — the cast-first `Real.exp_nat_mul` idiom. -/
lemma exp_pow_two_mul (z : ℝ) (ℓ : ℕ) : Real.exp z ^ (2 * ℓ) = Real.exp (2 * (ℓ : ℝ) * z) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **C-3 (split form) — the entry ticket as the integral step consumes it.**  On `𝒯_{j,r}`,
for every `ℓ : ℕ`,

  `1 ≤ ‖Q_{r,H_{j−1}}(1+it)‖^{2ℓ}·e^{2ℓα_{j−1}r/H_{j−1}}`,

the power of the block polynomial and the (explicit, `t`-free) exponential separated. -/
theorem one_le_ramQ_pow_mul_exp {c : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ}
    {J j r : ℕ} {t : ℝ} (ht : t ∈ TsetGr c Pseq Qseq Hseq αseq J j r) (ℓ : ℕ) :
    1 ≤ ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
        * Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1)) := by
  have hpow := one_le_normalized_pow ht ℓ
  have hsplit : (‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖
        * Real.exp (αseq (j - 1) * (r : ℝ) / Hseq (j - 1))) ^ (2 * ℓ)
      = ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
        * Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1)) := by
    rw [mul_pow, exp_pow_two_mul]
    congr 2
    ring
  rw [hsplit] at hpow
  exact hpow

/-! ## §4 — C-4: the moment insertion on a cell -/

/-- **C-4 — THE MOMENT INSERTION.**  On any measurable window `A ⊆ [−T,T]` contained in the
cell `𝒯_{j,r}`, the `2ℓ`-th power of the level-`(j−1)` block polynomial may be inserted under
the mean square at the price of the explicit exponential:

  `∫_A ‖F(1+it)‖² dt ≤ e^{2ℓα_{j−1}r/H_{j−1}}·∫_A ‖Q_{r,H_{j−1}}(1+it)‖^{2ℓ}·‖F(1+it)‖² dt`.

This is the entry ticket for the moment stone (MR's Lemma 13, `G4c`/`G4d`, a sibling lane —
NOT consumed here): §8.2 spends the RIGHT side, which is exactly what Lemma 13's `Q^ℓ A`
shape prices.  `ℓ` is free; the exponential carries `α_{j−1}`, `r`, `H_{j−1}` in-statement
(law #253, nothing absorbed).  Measurability/integrability are DISCHARGED internally from
continuity of `spoly` and `ramQ` on `[−T,T]` — no socket binders are needed or carried. -/
theorem cell_integral_normalized (c a : ℕ → ℂ) (N : ℕ) (Pseq Qseq : ℕ → ℕ)
    (Hseq αseq : ℕ → ℝ) (J j r ℓ : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T)
    (hAT : A ⊆ TsetGr c Pseq Qseq Hseq αseq J j r) :
    (∫ t in A, ‖spoly N a t‖ ^ 2)
      ≤ Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
          * ∫ t in A, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
              * ‖spoly N a t‖ ^ 2 := by
  have hcontL : Continuous fun t : ℝ => ‖spoly N a t‖ ^ 2 :=
    (continuous_spoly N a).norm.pow 2
  have hcontG : Continuous fun t : ℝ =>
      ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
        * ‖spoly N a t‖ ^ 2 :=
    ((continuous_ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c).norm.pow (2 * ℓ)).mul
      ((continuous_spoly N a).norm.pow 2)
  have hcontR : Continuous fun t : ℝ =>
      Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
        * (‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
            * ‖spoly N a t‖ ^ 2) := continuous_const.mul hcontG
  have hIntL : IntegrableOn (fun t : ℝ => ‖spoly N a t‖ ^ 2) A volume :=
    integrableOn_of_continuous_subset_Icc hcontL hT hAm hAsub
  have hIntG : IntegrableOn (fun t : ℝ =>
      ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
        * ‖spoly N a t‖ ^ 2) A volume :=
    integrableOn_of_continuous_subset_Icc hcontG hT hAm hAsub
  have hIntR : IntegrableOn (fun t : ℝ =>
      Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
        * (‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
            * ‖spoly N a t‖ ^ 2)) A volume :=
    integrableOn_of_continuous_subset_Icc hcontR hT hAm hAsub
  have hpt : (∫ t in A, ‖spoly N a t‖ ^ 2)
      ≤ ∫ t in A, Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
          * (‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
              * ‖spoly N a t‖ ^ 2) := by
    refine setIntegral_mono_on hIntL hIntR hAm (fun t ht => ?_)
    have h1 := one_le_ramQ_pow_mul_exp (hAT ht) ℓ
    have h2 : (0 : ℝ) ≤ ‖spoly N a t‖ ^ 2 := sq_nonneg _
    nlinarith [h1, h2]
  have hconst : (∫ t in A, Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
        * (‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
            * ‖spoly N a t‖ ^ 2))
      = Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
        * ∫ t in A, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
            * ‖spoly N a t‖ ^ 2 :=
    MeasureTheory.integral_const_mul _ _
  rw [hconst] at hpt
  exact hpt

/-- The §8.2 cell window `A_{j,r} := (Ann ∖ ball) ∩ 𝒯_{j,r}` is measurable (`G2`'s idiom at
the cell). -/
lemma measurableSet_annulus_TsetGr (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
    (J j r : ℕ) (X T t₁ : ℝ) :
    MeasurableSet ((seamAnn X T \ seamBall X t₁) ∩ TsetGr c Pseq Qseq Hseq αseq J j r) :=
  ((measurableSet_seamAnn X T).diff (measurableSet_seamBall X t₁)).inter
    (measurableSet_TsetGr c Pseq Qseq Hseq αseq J j r)

/-- `A_{j,r} ⊆ [−T,T]` — the transport through the two intersections. -/
lemma annulus_TsetGr_subset_Icc (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
    (J j r : ℕ) (X T t₁ : ℝ) :
    (seamAnn X T \ seamBall X t₁) ∩ TsetGr c Pseq Qseq Hseq αseq J j r ⊆ Set.Icc (-T) T :=
  fun _ ht => seamAnn_subset_Icc X T ht.1.1

/-- **C-4 at the row's own window.**  `cell_integral_normalized` instantiated at
`A_{j,r} = (Ann ∖ ball) ∩ 𝒯_{j,r}` — the piece the graded seam row
(`SeamGraded.prop_A3_T1_row_split_weightedG`) hands §8.2 after `C-2`'s covering:

  `∫_{A_{j,r}}‖F(1+it)‖² ≤ e^{2ℓα_{j−1}r/H_{j−1}}·∫_{A_{j,r}}‖Q_{r,H_{j−1}}‖^{2ℓ}‖F(1+it)‖²`.
-/
theorem cell_integral_normalized_annulus (c a : ℕ → ℂ) (N : ℕ) (Pseq Qseq : ℕ → ℕ)
    (Hseq αseq : ℕ → ℝ) (J j r ℓ : ℕ) (X T t₁ : ℝ) (hT : 0 ≤ T) :
    (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetGr c Pseq Qseq Hseq αseq J j r,
        ‖spoly N a t‖ ^ 2)
      ≤ Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
          * ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetGr c Pseq Qseq Hseq αseq J j r,
              ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
                * ‖spoly N a t‖ ^ 2 :=
  cell_integral_normalized c a N Pseq Qseq Hseq αseq J j r ℓ hT _
    (measurableSet_annulus_TsetGr c Pseq Qseq Hseq αseq J j r X T t₁)
    (annulus_TsetGr_subset_Icc c Pseq Qseq Hseq αseq J j r X T t₁)
    Set.inter_subset_right

end Salt.MR
