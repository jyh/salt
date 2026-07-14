/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.BandSplit
import Salt.Chen.PieceDecomp

/-!
# BND2 — the three-piece band decomposition + `Plo_discharge` (catch #57's resolution)

Design: `docs/blueprints/flags.md`, the `2026-07-14 BND … ★ CATCH #57 ★` entry and the FABLE
ADJUDICATION paragraph (the frozen three-piece design), plus `Salt/Chen/BandSplit.lean` (the landed
`sum_symm_ordered_split` + `bandDiagCount_le`) and `Salt/Chen/PieceDecomp.lean` (the named band slot
`Plo` of `hBlock_of_window_prices`).

The band sub-box of piece `k` is `blockBoxHonestDisc x z y ε₀ j N M (min (z·N+1) (x+1)) (x+1) d`
(`N = pieceN k`, `M = pieceM k`).  Its triples are `(p₁, p₂, p₃)` with `z ≤ p₁ ≤ y < p₂ ≤ p₃`,
`N < p₃ ≤ M`, `min (z·N+1) (x+1) ≤ p₁p₂ < x+1`, `prod` in the window, block `j`, class `d`.

## The m-threshold finding (verified here)

* **Symmetric region `p₂ > N`.**  The band's `m`-lower-threshold `a ≤ p₁p₂` is **AUTOMATIC**: with
  `p₁ ≥ z ≥ 1` and `p₂ ≥ N+1` one has `p₁p₂ ≥ z(N+1) = zN+z ≥ zN+1 ≥ min (zN+1) (x+1) = a`; and the
  upper `p₁p₂ < x+1` is automatic since `p₁p₂ ≤ prod ≤ x` (`bandCard_split`'s redundancy).
* **Low region `p₂ ≤ N`.**  The threshold genuinely **CUTS** — for small `p₁` one may have
  `p₁p₂ < zN` — so the `α_low` rectangle carries the `m`-range `[a, x+1)` explicitly.

## The geometric three-piece cover

`band box = {p₂ > N (SYMMETRIC part)} ⊔ {p₂ ≤ N (α_low part)}` (partition on `N < p₂`,
`bandCard_split`).  The symmetric part is an ordered `(p₂, p₃)`-sum over the primes
`(max(y,N), M]`; `sum_symm_ordered_split` (landed) splits it as `½·(unordered rectangle) +
½·(diagonal)` (`symCard_two_mul`).  So the band's honest discrepancy decomposes as
`bandDisc = ½·symRectDisc + ½·diagDisc + lowDisc` (`bandDisc_eq_three`), whence the per-`d` triangle
`bandDisc_le_three_pieces`.  The diagonal is crude (`abs_diagDisc_le_bandDiagCount`, feeding the
landed `bandDiagCount_le`); the symmetric rectangle and the `α_low` rectangle are BV-priced
downstream (`general_BV_cutoff_final` at their own cutoffs).

## What this file lands

* the three-piece cover + the symmetry split at the count level (`bandCard_split`,
  `symCard_two_mul`);
* the honest-discrepancy decomposition + the per-`d` triangle (`bandDisc_eq_three`,
  `bandDisc_le_three_pieces`);
* the crude diagonal disc bound (`abs_diagDisc_le_bandDiagCount`);
* the composed `Plo_discharge`: the band slot of `hBlock_of_window_prices` bounded by
  `½·(sym rectangle price) + (α_low rectangle price) + (crude diagonal)`, with the `#check` chain
  into `hBlock_of_window_prices → hHDblocks_of_perBlock → hBVblocks_of_generalBV`.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the piece index sets and the class×window pair weight -/

/-- The block-`j` small-prime index set: primes `p₁ ∈ [1, x]` with `z ≤ p₁ ≤ y` and
`blockIdx z ε₀ p₁ = j` — the `p₁`-fibre folded into the symmetry-split weight. -/
noncomputable def bandP1Set (x z y : ℕ) (ε₀ : ℝ) (j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun p₁ => p₁.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ blockIdx z ε₀ p₁ = j)

/-- The large-prime index set of the symmetric part: primes in `(max(y, N), M] ∩ [1, x]`.  Both
large primes `p₂, p₃` of a symmetric band triple range over this SAME set (the reason the
`½`-symmetry applies). -/
noncomputable def bandLargeSet (x y N M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun p => p.Prime ∧ max y N < p ∧ p ≤ M)

/-- The class×window pair predicate on `(p₁, p, q)`: the product `p₁·p·q` meets the class `C` and
lies in the window `[x/2+2, x]`.  Symmetric in `p, q` (`cwin_comm`), the reason the symmetric part's
weight `∑_{p₁} [cwin]` is symmetric. -/
def cwin (x : ℕ) (C : ℕ → Prop) (p₁ p q : ℕ) : Prop :=
  C (p₁ * p * q) ∧ x / 2 + 2 ≤ p₁ * p * q ∧ p₁ * p * q ≤ x

lemma cwin_comm (x : ℕ) (C : ℕ → Prop) (p₁ a b : ℕ) :
    cwin x C p₁ a b = cwin x C p₁ b a := by
  unfold cwin; rw [mul_right_comm p₁ a b]

/-! ## Part B — the symmetric-part counts and the `½`-symmetry split -/

open Classical in
/-- The symmetric-part count at class `C`: block-`j` band triples with `p₂ > N`, `N < p₃ ≤ M` — the
ordered `(p₂, p₃)`-sum with both large primes in `(max(y,N), M]` (the `m`-range is redundant here,
see `bandCard_split`). -/
noncomputable def symCard (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (C : ℕ → Prop) : ℝ :=
  (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ C (prod3 t) ∧
      N < t.2.1 ∧ N < t.2.2 ∧ t.2.2 ≤ M)).card : ℝ)

open Classical in
/-- The UNORDERED rectangle count at class `C`: `∑_{p₁} ∑_{(p,q) ∈ S×S} [cwin]`, `S` the large
primes `(max(y,N), M]`.  The `½`-image of the symmetric part (`symCard_two_mul`); BV-priced
downstream by `general_BV_cutoff_final`. -/
noncomputable def symRectCount (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (C : ℕ → Prop) : ℝ :=
  ∑ p₁ ∈ bandP1Set x z y ε₀ j, ∑ q ∈ bandLargeSet x y N M ×ˢ bandLargeSet x y N M,
    (if cwin x C p₁ q.1 q.2 then (1 : ℝ) else 0)

open Classical in
/-- The diagonal count at class `C`: `∑_{p₁} ∑_{p ∈ S} [cwin p p]` (the `p₂ = p₃` triples).  The
other `½`-image of the symmetric part; crude (`abs_diagDisc_le_bandDiagCount`). -/
noncomputable def diagSum (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (C : ℕ → Prop) : ℝ :=
  ∑ p₁ ∈ bandP1Set x z y ε₀ j, ∑ p ∈ bandLargeSet x y N M,
    (if cwin x C p₁ p p then (1 : ℝ) else 0)

open Classical in
/-- **The symmetric-part reindex.**  `symCard` reindexes to the ordered `p₁`-then-`(p₂ ≤ p₃)`-pair
double sum: the block-`j` symmetric triples are exactly the triples `(p₁, p, q)` with `p₁ ∈`
`bandP1Set`, `(p, q) ∈ S×S` ordered `p ≤ q`, and `cwin`.  A `Finset.ext` (both sides are subsets of
`ℕ×ℕ×ℕ` — the identification `t = (t.1, t.2.1, t.2.2)` is definitional) + `sum_boole` +
`sum_product'`. -/
lemma symCard_eq_sum (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (C : ℕ → Prop) :
    symCard x z y ε₀ j N M C
      = ∑ p₁ ∈ bandP1Set x z y ε₀ j,
          ∑ q ∈ (bandLargeSet x y N M ×ˢ bandLargeSet x y N M).filter (fun q => q.1 ≤ q.2),
            (if cwin x C p₁ q.1 q.2 then (1 : ℝ) else 0) := by
  classical
  unfold symCard
  have hset : (tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ C (prod3 t) ∧
        N < t.2.1 ∧ N < t.2.2 ∧ t.2.2 ≤ M)
      = (bandP1Set x z y ε₀ j ×ˢ
          (bandLargeSet x y N M ×ˢ bandLargeSet x y N M).filter (fun q => q.1 ≤ q.2)).filter
          (fun w => cwin x C w.1 w.2.1 w.2.2) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_product, bandP1Set, bandLargeSet, tripleSet, cwin,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hp1i, hp2i, hp3i⟩, hz1, h1y, hy2, h23, hpr1, hpr2, hpr3, hwlo, hwhi⟩,
        hblk, hC, hN2, hN3, h3M⟩
      refine ⟨⟨⟨⟨hp1i.1, hp1i.2⟩, hpr1, hz1, h1y, hblk⟩,
        ⟨⟨⟨hp2i.1, hp2i.2⟩, hpr2, ?_, ?_⟩, ⟨⟨hp3i.1, hp3i.2⟩, hpr3, ?_, h3M⟩⟩, h23⟩,
        hC, hwlo, hwhi⟩
      · exact max_lt hy2 hN2
      · exact le_trans h23 h3M
      · exact max_lt (lt_of_lt_of_le hy2 h23) hN3
    · rintro ⟨⟨⟨⟨hp1i1, hp1i2⟩, hpr1, hz1, h1y, hblk⟩,
        ⟨⟨⟨hp2i1, hp2i2⟩, hpr2, h2max, h2M⟩, ⟨⟨hp3i1, hp3i2⟩, hpr3, h3max, h3M⟩⟩, h23⟩,
        hC, hwlo, hwhi⟩
      exact ⟨⟨⟨⟨hp1i1, hp1i2⟩, ⟨hp2i1, hp2i2⟩, ⟨hp3i1, hp3i2⟩⟩,
        hz1, h1y, lt_of_le_of_lt (le_max_left _ _) h2max, h23, hpr1, hpr2, hpr3, hwlo, hwhi⟩,
        hblk, hC, lt_of_le_of_lt (le_max_right _ _) h2max, lt_of_le_of_lt (le_max_right _ _) h3max,
        h3M⟩
  rw [hset, ← Finset.sum_boole, Finset.sum_product]

open Classical in
/-- **The `½`-symmetry split (FULL — consumes the landed `sum_symm_ordered_split`).**  Twice the
symmetric part equals the unordered rectangle plus the diagonal: `2·symCard = symRectCount +
diagSum`.  Per `p₁`, the weight `w p q = [cwin p₁ p q]` is symmetric (`cwin_comm`), so
`sum_symm_ordered_split` gives `2·(ordered ≤ sum) = (full S×S sum) + (diagonal sum)`; summing over
`p₁ ∈ bandP1Set`. -/
theorem symCard_two_mul (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (C : ℕ → Prop) :
    2 * symCard x z y ε₀ j N M C
      = symRectCount x z y ε₀ j N M C + diagSum x z y ε₀ j N M C := by
  classical
  rw [symCard_eq_sum, Finset.mul_sum, symRectCount, diagSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p₁ _ => ?_)
  have hsymm : ∀ a b : ℕ, (if cwin x C p₁ a b then (1 : ℝ) else 0)
      = (if cwin x C p₁ b a then (1 : ℝ) else 0) := by
    intro a b; rw [cwin_comm x C p₁ a b]
  have h := sum_symm_ordered_split (bandLargeSet x y N M)
    (fun a b => if cwin x C p₁ a b then (1 : ℝ) else 0) hsymm
  simpa using h

/-! ## Part C — the geometric three-piece cover (the partition on `N < p₂`) -/

open Classical in
/-- The band-box count at class `C` (the residue/unit count with `C` abstracted).  Equal to
`blockBoxResCount`/`blockBoxUnitCount` at the residue/unit class (`bandCard_eq_blockBoxResCount`,
`…UnitCount`). -/
noncomputable def bandCard (x z y : ℕ) (ε₀ : ℝ) (j N M a b : ℕ) (C : ℕ → Prop) : ℝ :=
  (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ C (prod3 t) ∧
      N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℝ)

open Classical in
/-- The `α_low`-rectangle count at class `C`: the band-box triples with the low large prime
`p₂ ≤ N` (so `p₂ ≤ N < p₃`, the ordering is automatic).  Carries the `m`-range `[a, b)` explicitly
(the threshold genuinely cuts here). -/
noncomputable def lowCard (x z y : ℕ) (ε₀ : ℝ) (j N M a b : ℕ) (C : ℕ → Prop) : ℝ :=
  (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ C (prod3 t) ∧
      N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧ t.2.1 ≤ N)).card : ℝ)

/-- `blockBoxResCount` is `bandCard` at the residue-`2` class. -/
lemma bandCard_eq_blockBoxResCount (x z y : ℕ) (ε₀ : ℝ) (j N M a b d : ℕ) :
    blockBoxResCount x z y ε₀ j N M a b d
      = bandCard x z y ε₀ j N M a b (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d)) := by
  unfold blockBoxResCount bandCard
  rw [Nat.cast_inj]
  apply congrArg Finset.card
  ext t
  simp only [Finset.mem_filter]

/-- `blockBoxUnitCount` is `bandCard` at the unit class. -/
lemma bandCard_eq_blockBoxUnitCount (x z y : ℕ) (ε₀ : ℝ) (j N M a b d : ℕ) :
    blockBoxUnitCount x z y ε₀ j N M a b d
      = bandCard x z y ε₀ j N M a b (fun v => IsUnit ((v : ℕ) : ZMod d)) := by
  unfold blockBoxUnitCount bandCard
  rw [Nat.cast_inj]
  apply congrArg Finset.card
  ext t
  simp only [Finset.mem_filter]

open Classical in
/-- **The three-piece cover at the count level (FULL).**  For `1 ≤ z`, `a ≤ z·N+1`, and
`x+1 ≤ b`, the band-box count partitions into the symmetric part (`p₂ > N`) and the `α_low` part
(`p₂ ≤ N`): `bandCard = symCard + lowCard`.  The partition is `card_filter_add_card_filter_not` on
`N < p₂`; in the symmetric part the `m`-range `[a, b)` is redundant (`p₁ ≥ z`, `p₂ ≥ N+1` force
`p₁p₂ ≥ z(N+1) ≥ zN+1 ≥ a`, and `p₁p₂ ≤ prod ≤ x < b`). -/
theorem bandCard_split (x z y : ℕ) (ε₀ : ℝ) (j N M a b : ℕ) (C : ℕ → Prop)
    (hz : 1 ≤ z) (ha : a ≤ z * N + 1) (hb : x + 1 ≤ b) :
    bandCard x z y ε₀ j N M a b C
      = symCard x z y ε₀ j N M C + lowCard x z y ε₀ j N M a b C := by
  classical
  unfold bandCard symCard lowCard
  rw [← Nat.cast_add, Nat.cast_inj,
    ← Finset.card_filter_add_card_filter_not
        (s := (tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ C (prod3 t) ∧
          N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b))
        (p := fun t => N < t.2.1)]
  congr 1
  · rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
    rw [tripleSet, Finset.mem_filter] at ht
    obtain ⟨_, hz1, _h1y, _hy2, h23, _hpr1, _hpr2, _hpr3, _hwlo, hwhi⟩ := ht
    have hp3pos : 1 ≤ t.2.2 := by omega
    constructor
    · rintro ⟨⟨hblk, hC, hN3, h3M, _ham, _hmb⟩, hN2⟩
      exact ⟨hblk, hC, hN2, hN3, h3M⟩
    · rintro ⟨hblk, hC, hN2, hN3, h3M⟩
      have hmul : z * N + z ≤ t.1 * t.2.1 := by
        have h1 : z * (N + 1) ≤ t.1 * t.2.1 := Nat.mul_le_mul hz1 (by omega)
        rwa [Nat.mul_add, Nat.mul_one] at h1
      have hle : t.1 * t.2.1 ≤ prod3 t := by
        rw [prod3]; exact Nat.le_mul_of_pos_right _ hp3pos
      exact ⟨⟨hblk, hC, hN3, h3M, by omega, by omega⟩, hN2⟩
  · rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr (fun t _ => ?_))
    constructor
    · rintro ⟨⟨hblk, hC, hN3, h3M, ham, hmb⟩, hnN2⟩
      exact ⟨hblk, hC, hN3, h3M, ham, hmb, by omega⟩
    · rintro ⟨hblk, hC, hN3, h3M, ham, hmb, h2N⟩
      exact ⟨⟨hblk, hC, hN3, h3M, ham, hmb⟩, by omega⟩

/-! ## Part D — the crude diagonal count bound -/

open Classical in
/-- **The diagonal count is crude (FULL).**  `diagSum C ≤ bandDiagCount`: the residue/unit-class
diagonal count injects, via `(p₁, p) ↦ (p₁, p, p)`, into the `p₂ = p₃` band triples counted by the
landed `bandDiagCount` (the class `C` and window only sharpen the filter).  Feeds
`BandSplit.bandDiagCount_le` (`#diag ≤ y·(M−N)`). -/
theorem diagSum_le_bandDiagCount (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (C : ℕ → Prop) :
    diagSum x z y ε₀ j N M C ≤ bandDiagCount x z y ε₀ j N M := by
  classical
  have hD : diagSum x z y ε₀ j N M C
      = (((bandP1Set x z y ε₀ j ×ˢ bandLargeSet x y N M).filter
          (fun w => cwin x C w.1 w.2 w.2)).card : ℝ) := by
    unfold diagSum
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    refine Finset.sum_congr rfl (fun p₁ _ => ?_)
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : cwin x C p₁ p p <;> simp [h]
  rw [hD, bandDiagCount, Nat.cast_le]
  apply Finset.card_le_card_of_injOn (fun w => (w.1, w.2, w.2))
  · rintro ⟨p₁, p⟩ hw
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, bandP1Set, bandLargeSet,
      Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, cwin] at hw
    obtain ⟨⟨⟨hp1i, hpr1, hz1, h1y, hblk⟩, ⟨hpi, hpr, hmax, hpM⟩⟩, _hC, hwlo, hwhi⟩ := hw
    change (p₁, p, p) ∈ (tripleSet x z y).filter (fun t : ℕ × ℕ × ℕ => blockIdx z ε₀ t.1 = j ∧
      t.2.1 = t.2.2 ∧ N < t.2.2 ∧ t.2.2 ≤ M)
    rw [Finset.mem_filter, tripleSet, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product]
    simp only [Finset.mem_Icc]
    exact ⟨⟨⟨⟨hp1i.1, hp1i.2⟩, ⟨hpi.1, hpi.2⟩, ⟨hpi.1, hpi.2⟩⟩,
        hz1, h1y, lt_of_le_of_lt (le_max_left _ _) hmax, le_refl _, hpr1, hpr, hpr, hwlo, hwhi⟩,
      hblk, trivial, lt_of_le_of_lt (le_max_right _ _) hmax, hpM⟩
  · rintro ⟨p₁, p⟩ _ ⟨p₁', p'⟩ _ heq
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext heq.1 heq.2.1

lemma diagSum_nonneg (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (C : ℕ → Prop) :
    0 ≤ diagSum x z y ε₀ j N M C := by
  classical
  unfold diagSum
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))

/-! ## Part E — the honest-discrepancy decomposition + the per-`d` triangle -/

open Classical in
/-- The symmetric UNORDERED rectangle honest discrepancy (`res − ν·unit`) — BV-priced downstream. -/
noncomputable def bandSymRectDisc (x z y : ℕ) (ε₀ : ℝ) (j N M d : ℕ) : ℝ :=
  symRectCount x z y ε₀ j N M (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))
    - nuChen d * symRectCount x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod d))

open Classical in
/-- The `α_low` rectangle honest discrepancy (`res − ν·unit`, `p₂ ≤ N < p₃`) — BV-priced
downstream. -/
noncomputable def bandLowDisc (x z y : ℕ) (ε₀ : ℝ) (j N M a b d : ℕ) : ℝ :=
  lowCard x z y ε₀ j N M a b (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))
    - nuChen d * lowCard x z y ε₀ j N M a b (fun v => IsUnit ((v : ℕ) : ZMod d))

open Classical in
/-- The diagonal honest discrepancy (`res − ν·unit`, `p₂ = p₃`) — crude. -/
noncomputable def bandDiagDisc (x z y : ℕ) (ε₀ : ℝ) (j N M d : ℕ) : ℝ :=
  diagSum x z y ε₀ j N M (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))
    - nuChen d * diagSum x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod d))

/-- `symCard = ½·(rectangle + diagonal)` (halving `symCard_two_mul`). -/
lemma symCard_eq_half (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (C : ℕ → Prop) :
    symCard x z y ε₀ j N M C
      = (symRectCount x z y ε₀ j N M C + diagSum x z y ε₀ j N M C) / 2 := by
  have := symCard_two_mul x z y ε₀ j N M C; linarith

/-- **The crude diagonal disc bound (FULL).**  `|bandDiagDisc| ≤ bandDiagCount` (both class counts
lie in `[0, bandDiagCount]` and `ν ∈ [0,1]`); the landed `BandSplit.bandDiagCount_le` then gives
`≤ y·(M−N)`. -/
theorem abs_diagDisc_le_bandDiagCount (x z y : ℕ) (ε₀ : ℝ) (j N M d : ℕ) :
    |bandDiagDisc x z y ε₀ j N M d| ≤ bandDiagCount x z y ε₀ j N M := by
  unfold bandDiagDisc
  have hR0 := diagSum_nonneg x z y ε₀ j N M (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))
  have hU0 := diagSum_nonneg x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod d))
  have hRC := diagSum_le_bandDiagCount x z y ε₀ j N M
    (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))
  have hUC := diagSum_le_bandDiagCount x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod d))
  have hc0 : 0 ≤ nuChen d := by rw [nuChen_apply]; positivity
  have hc1 : nuChen d ≤ 1 := nuChen_le_one d
  have hcU : nuChen d * diagSum x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod d))
      ≤ diagSum x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod d)) := mul_le_of_le_one_left hU0 hc1
  have hcUnn : 0 ≤ nuChen d * diagSum x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod d)) :=
    mul_nonneg hc0 hU0
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- **The band honest disc decomposes into three pieces (FULL).**  For `1 ≤ z`, the band sub-box
honest discrepancy is `½·symRect + ½·diag + low` (the `bandCard_split` partition + the
`symCard_two_mul` symmetry split, `ν`-linearly). -/
theorem bandDisc_eq_three (x z y : ℕ) (ε₀ : ℝ) (j N M d : ℕ) (hz : 1 ≤ z) :
    blockBoxHonestDisc x z y ε₀ j N M (min (z * N + 1) (x + 1)) (x + 1) d
      = (1 / 2) * bandSymRectDisc x z y ε₀ j N M d
        + (1 / 2) * bandDiagDisc x z y ε₀ j N M d
        + bandLowDisc x z y ε₀ j N M (min (z * N + 1) (x + 1)) (x + 1) d := by
  have ha : min (z * N + 1) (x + 1) ≤ z * N + 1 := min_le_left _ _
  have hb : x + 1 ≤ x + 1 := le_refl _
  unfold blockBoxHonestDisc
  rw [bandCard_eq_blockBoxResCount, bandCard_eq_blockBoxUnitCount,
    bandCard_split x z y ε₀ j N M (min (z * N + 1) (x + 1)) (x + 1)
      (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d)) hz ha hb,
    bandCard_split x z y ε₀ j N M (min (z * N + 1) (x + 1)) (x + 1)
      (fun v => IsUnit ((v : ℕ) : ZMod d)) hz ha hb,
    symCard_eq_half x z y ε₀ j N M (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d)),
    symCard_eq_half x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod d))]
  unfold bandSymRectDisc bandDiagDisc bandLowDisc
  ring

/-- **The per-`d` triangle over the three pieces (FULL — FLOOR A).**  `|band disc| ≤ ½·|symRect| +
|low| + ½·bandDiagCount` (the three-piece decomposition + the triangle + the crude diagonal). -/
theorem bandDisc_le_three_pieces (x z y : ℕ) (ε₀ : ℝ) (j N M d : ℕ) (hz : 1 ≤ z) :
    |blockBoxHonestDisc x z y ε₀ j N M (min (z * N + 1) (x + 1)) (x + 1) d|
      ≤ (1 / 2) * |bandSymRectDisc x z y ε₀ j N M d|
        + |bandLowDisc x z y ε₀ j N M (min (z * N + 1) (x + 1)) (x + 1) d|
        + (1 / 2) * bandDiagCount x z y ε₀ j N M := by
  rw [bandDisc_eq_three x z y ε₀ j N M d hz]
  have hdiag := abs_diagDisc_le_bandDiagCount x z y ε₀ j N M d
  have htri : |(1 / 2) * bandSymRectDisc x z y ε₀ j N M d
        + (1 / 2) * bandDiagDisc x z y ε₀ j N M d
        + bandLowDisc x z y ε₀ j N M (min (z * N + 1) (x + 1)) (x + 1) d|
      ≤ |(1 / 2) * bandSymRectDisc x z y ε₀ j N M d|
        + |(1 / 2) * bandDiagDisc x z y ε₀ j N M d|
        + |bandLowDisc x z y ε₀ j N M (min (z * N + 1) (x + 1)) (x + 1) d| := by
    have h1 := abs_add_le ((1 / 2) * bandSymRectDisc x z y ε₀ j N M d
      + (1 / 2) * bandDiagDisc x z y ε₀ j N M d)
      (bandLowDisc x z y ε₀ j N M (min (z * N + 1) (x + 1)) (x + 1) d)
    have h2 := abs_add_le ((1 / 2) * bandSymRectDisc x z y ε₀ j N M d)
      ((1 / 2) * bandDiagDisc x z y ε₀ j N M d)
    linarith
  rw [abs_mul, abs_mul, show |(1 : ℝ) / 2| = 1 / 2 by norm_num] at htri
  linarith

/-! ## Part F — the composed `Plo_discharge` -/

open Classical in
/-- **`Plo_discharge` (FULL) — the band slot of `hBlock_of_window_prices` priced by the three
pieces.**  The named low-piece band `Plo`-sum is bounded by `½·(the symmetric rectangle price
`Psym`) + (the `α_low` rectangle price `Plow`) + (the crude diagonal)`.  `Psym`, `Plow` are named
(discharged downstream by `general_BV_cutoff_final` at their own cutoffs); the diagonal is explicit
(`bandDiagCount` is `d`-free, so its guarded `d`-sum is `≤ #divisors · bandDiagCount ≤ #divisors ·
y·(M−N)`, the landed `BandSplit.bandDiagCount_le`).  Feeds the `Plo` hypothesis of
`hBlock_of_window_prices`. -/
theorem Plo_discharge (x z y : ℕ) (ε₀ : ℝ) (Ps : ℕ) (bound : ℝ) (j : ℕ) (Psym Plow : ℝ)
    (hz : 1 ≤ z)
    (hSym : (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |bandSymRectDisc x z y ε₀ j (pieceN k) (pieceM k) d| else 0)
      ≤ Psym)
    (hLow : (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |bandLowDisc x z y ε₀ j (pieceN k) (pieceM k)
          (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0) ≤ Plow) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k)
             (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
      ≤ (1 / 2) * Psym + Plow
        + (1 / 2) * ((Nat.divisors Ps).card : ℝ)
            * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
                (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ) := by
  classical
  set R := Finset.range (Nat.log 2 x + 1) with hR
  -- Per `(k, d)`: the guarded triangle over the three pieces.
  have hterm : ∀ (k d : ℕ),
      (if (d : ℝ) < bound then
          |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k)
             (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
        ≤ (1 / 2) * (if (d : ℝ) < bound then
              |bandSymRectDisc x z y ε₀ j (pieceN k) (pieceM k) d| else 0)
          + (if (d : ℝ) < bound then |bandLowDisc x z y ε₀ j (pieceN k) (pieceM k)
              (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
          + (1 / 2) * (if (d : ℝ) < bound then bandDiagCount x z y ε₀ j (pieceN k) (pieceM k)
              else 0) := by
    intro k d
    by_cases hd : (d : ℝ) < bound
    · simp only [if_pos hd]
      exact bandDisc_le_three_pieces x z y ε₀ j (pieceN k) (pieceM k) d hz
    · simp only [if_neg hd]; norm_num
  -- Sum the per-term bound, then split the RHS into the three named/explicit sums.
  refine le_trans (Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun d _ => hterm k d))) ?_
  have hsplit : ∀ k, (∑ d ∈ Nat.divisors Ps,
        ((1 / 2) * (if (d : ℝ) < bound then
              |bandSymRectDisc x z y ε₀ j (pieceN k) (pieceM k) d| else 0)
          + (if (d : ℝ) < bound then |bandLowDisc x z y ε₀ j (pieceN k) (pieceM k)
              (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
          + (1 / 2) * (if (d : ℝ) < bound then bandDiagCount x z y ε₀ j (pieceN k) (pieceM k)
              else 0)))
      = (1 / 2) * (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then |bandSymRectDisc x z y ε₀ j (pieceN k) (pieceM k) d| else 0)
        + (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then |bandLowDisc x z y ε₀ j (pieceN k)
            (pieceM k) (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
        + (1 / 2) * (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) else 0) := by
    intro k
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  -- Bound the three summands.
  have hdiagBound : ∑ k ∈ R, (∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) else 0)
      ≤ ((Nat.divisors Ps).card : ℝ)
          * ∑ k ∈ R, (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hnn : 0 ≤ bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) := by
      unfold bandDiagCount; positivity
    calc (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) else 0)
        ≤ ∑ _d ∈ Nat.divisors Ps, bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) := by
          refine Finset.sum_le_sum (fun d _ => ?_)
          split_ifs with h
          · exact le_refl _
          · exact hnn
      _ = ((Nat.divisors Ps).card : ℝ) * bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Nat.divisors Ps).card : ℝ) * ((y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact bandDiagCount_le x z y ε₀ j (pieceN k) (pieceM k)
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hsymSum : (1 / 2) * (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |bandSymRectDisc x z y ε₀ j (pieceN k) (pieceM k) d| else 0)
      ≤ (1 / 2) * Psym := mul_le_mul_of_nonneg_left hSym hhalf
  have hdiagSum : (1 / 2) * (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) else 0)
      ≤ (1 / 2) * (((Nat.divisors Ps).card : ℝ)
          * ∑ k ∈ R, (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiagBound hhalf
  linarith [hLow]

/-! ## Composition sanity — the end-to-end chain elaborates

`Plo_discharge` produces the `Plo` input of `PieceDecomp.hBlock_of_window_prices` (the named
band slot), whose output feeds `hHDblocks_of_perBlock → hBVblocks_of_generalBV`.  The symmetric
rectangle price `Psym` and the `α_low` rectangle price `Plow` are named residuals (BV-priced by
`WindowClose.general_BV_cutoff_final` at their own cutoffs); the diagonal is explicit. -/

section CompositionSanity

#check @Salt.Chen.bandDisc_le_three_pieces
#check @Salt.Chen.Plo_discharge
#check @Salt.Chen.hBlock_of_window_prices
#check @Salt.Chen.hHDblocks_of_perBlock
#check @Salt.Chen.hBVblocks_of_generalBV
#check @Salt.Chen.general_BV_cutoff_final

end CompositionSanity

end Salt.Chen
