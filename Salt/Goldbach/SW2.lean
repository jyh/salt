/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.BandIdent

/-!
# G-SW2 — the annulus pricing layer (wave W3b, Opt-A)

Design: `docs/exploration/pilot.md` (the `~16:35` G-WINDOWSW + `~17:35` G-BANDIDENT landed
interfaces, and the Opt-A adjudication).  This file is the Goldbach mirror of `Salt/Chen/SwitchW2`
Parts B–G, reshaped to the OUTER DYADIC ANNULUS structure of `Salt/Goldbach/WindowSW`.

Where the twin's window `x/2+2 ≤ prod ≤ x` is a SINGLE factor-2 annulus (`box_disc_three_way` on
the one T-difference `T = x`, `T = x/2+1`), the Goldbach window `2 ≤ prod ≤ N/2` spans `⌊log₂N⌋+1`
factor-2 annuli `(goldCut N k, goldCut N (k+1)]`.  So the twin's `hHD_of_box_discW` (a single
carrier difference) is replaced by `WindowSW.goldBoxHonestDisc_le_annulus_sum` (the telescoped
`Σ_k`) — and each annulus is priced by `box_disc_three_way` at `T₁ = goldCut N k`,
`T₂ = goldCut N (k+1)` (`goldCut_mono` supplies `T₁ ≤ T₂`; the factor-2 `goldCut_succ_le_two_mul`
is what downstream `dyadicBoundary_card_le_three` needs).  The `O(log N)` annuli cost ONE extra
`log`, absorbed by consuming the BV backbone at saving `A+1`.

## What this file lands (the byte-lock for G-PDIAG)

* **Part B — the `p₃`-piece decomposition**: `goldBlockHonestDiscW` (the full-block BV target,
  `SwitchBV`) `= Σ_k goldBlockBoxHonestDisc … (pieceN k) (pieceM k) 0 (N/2+1)` — WBV6's fibering
  over `k = ⌊log₂ p₃⌋` at the reflected pair `(Q·d, crtClassG Q d N a)`.
* **Part C — the `m`-range split**: `goldBlockBoxHonestDisc_split_m` (ordering-clear ⊔ band).
* **Part D — `gold_hBlockW_of_window_prices`**: the per-block assembly (Part D mirror).
* **Part E — `gold_hNum_at_opW`**: the box pricing — `goldBoxHonestDisc_le_annulus_sum` +
  per-annulus `box_disc_three_way`; output is the `Σ_k Σ_i Price k i` double sum (the one log).
* **Part F — the band close**: `gold_bandDiscW_le_three_pieces` (crude) /
  `gold_bandDiscW_le_three_pieces_diag` (honest, for G-PDIAG's `PloW_honest`) + the
  `gold_PloW_discharge` crude supplier.
* **Part G — `gold_PloW_sym_of_box_disc` / `gold_PloW_low_of_box_disc`**: the sym/low rectangle
  prices via `BandIdent.goldBandSymRectDisc_le_annulus_sum` / `…goldBandLowDisc_le_annulus_sum` +
  per-annulus `box_disc_three_way`.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset
open scoped BigOperators

namespace Salt.Goldbach

open Salt.Chen

/-! ## Part B — the `p₃`-piece decomposition (WBV6's fibering over `k = ⌊log₂ p₃⌋`) -/

open Classical in
/-- **The `goldTripleSet` piece-partition kernel.**  Any predicate-filtered count of
`goldTripleSet` partitions exactly over the `⌊log₂ N⌋ + 1` dyadic `p₃`-pieces (`p₃ ≤ N` from the
carrier box).  The `goldTripleSet` mirror of the private twin `count_eq_sum_pieceW`. -/
private lemma gold_count_eq_sum_pieceB {N z y : ℕ} (P : ℕ × ℕ × ℕ → Prop) [DecidablePred P] :
    (((goldTripleSet N z y).filter P).card : ℝ)
      = ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          (((goldTripleSet N z y).filter (fun t => Nat.log 2 t.2.2 = k ∧ P t)).card : ℝ) := by
  classical
  have hmaps : ∀ t ∈ (goldTripleSet N z y).filter P,
      Nat.log 2 t.2.2 ∈ Finset.range (Nat.log 2 N + 1) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have htri := ht.1
    rw [goldTripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc] at htri
    obtain ⟨⟨_, _, _, hp3le⟩, _⟩ := htri
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right hp3le)
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hfilt : ((goldTripleSet N z y).filter P).filter (fun t => Nat.log 2 t.2.2 = k)
      = (goldTripleSet N z y).filter (fun t => Nat.log 2 t.2.2 = k ∧ P t) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro t _; exact and_comm
  rw [hfilt]

open Classical in
/-- **The free-modulus block residue count partitions over the `p₃`-pieces.**  The `goldTripleSet`
mirror of `blockResCountM_eq_sum_pieces` — the full `m`-range box is `0 (N/2+1)` (redundant:
`p₁p₂ ≤ prod3 ≤ N/2`). -/
theorem goldBlockResCountM_eq_sum_pieces (N z y : ℕ) (ε₀ : ℝ) (j m c : ℕ) :
    goldBlockResCountM N z y ε₀ j m c
      = ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          goldBlockBoxResCount N z y ε₀ j (pieceN k) (pieceM k) 0 (N / 2 + 1) m c := by
  classical
  unfold goldBlockResCountM
  rw [gold_count_eq_sum_pieceB
        (fun t => blockIdx z ε₀ t.1 = j ∧ ((prod3 t : ℕ) : ZMod m) = ((c : ℕ) : ZMod m))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold goldBlockBoxResCount
  rw [Nat.cast_inj]
  refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
  rw [goldTripleSet, Finset.mem_filter] at ht
  obtain ⟨_, _, _, _, _, _hp1, _hp2, hp3, _hwlo, hwhi⟩ := ht
  have hp3pos : 1 ≤ t.2.2 := hp3.pos
  have hmle : t.1 * t.2.1 ≤ N / 2 := by
    have hprod : prod3 t = t.1 * t.2.1 * t.2.2 := rfl
    calc t.1 * t.2.1 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_right _ hp3.pos
      _ = prod3 t := hprod.symm
      _ ≤ N / 2 := hwhi
  rw [log_eq_iff_piece hp3pos]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hblk, hres⟩
    exact ⟨hblk, hres, hlo, hhi, Nat.zero_le _, by omega⟩
  · rintro ⟨hblk, hres, hlo, hhi, _, _⟩
    exact ⟨⟨hlo, hhi⟩, hblk, hres⟩

open Classical in
/-- **The free-modulus block unit count partitions over the `p₃`-pieces.** -/
theorem goldBlockUnitCountM_eq_sum_pieces (N z y : ℕ) (ε₀ : ℝ) (j m : ℕ) :
    goldBlockUnitCountM N z y ε₀ j m
      = ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          goldBlockBoxUnitCount N z y ε₀ j (pieceN k) (pieceM k) 0 (N / 2 + 1) m := by
  classical
  unfold goldBlockUnitCountM
  rw [gold_count_eq_sum_pieceB (fun t => blockIdx z ε₀ t.1 = j ∧ IsUnit ((prod3 t : ℕ) : ZMod m))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold goldBlockBoxUnitCount
  rw [Nat.cast_inj]
  refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
  rw [goldTripleSet, Finset.mem_filter] at ht
  obtain ⟨_, _, _, _, _, _hp1, _hp2, hp3, _hwlo, hwhi⟩ := ht
  have hp3pos : 1 ≤ t.2.2 := hp3.pos
  have hmle : t.1 * t.2.1 ≤ N / 2 := by
    have hprod : prod3 t = t.1 * t.2.1 * t.2.2 := rfl
    calc t.1 * t.2.1 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_right _ hp3.pos
      _ = prod3 t := hprod.symm
      _ ≤ N / 2 := hwhi
  rw [log_eq_iff_piece hp3pos]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hblk, hu⟩
    exact ⟨hblk, hu, hlo, hhi, Nat.zero_le _, by omega⟩
  · rintro ⟨hblk, hu, hlo, hhi, _, _⟩
    exact ⟨⟨hlo, hhi⟩, hblk, hu⟩

/-- **`goldBlockHonestDiscW_eq_sum_pieces` (the piece decomposition, EXACT).**  The full-block
BV target (`SwitchBV.goldBlockHonestDiscW`) is the `Σ_k` of the box honest discrepancies over the
`⌊log₂ N⌋ + 1` dyadic `p₃`-pieces (full `m`-range `0 (N/2+1)`) at the reflected pair `(Q·d,
crtClassG Q d N a)`.  `blockHonestDiscW_eq_sum_pieces`'s Goldbach mirror. -/
theorem goldBlockHonestDiscW_eq_sum_pieces (N z y : ℕ) (ε₀ : ℝ) (j Q a d : ℕ) :
    goldBlockHonestDiscW N z y ε₀ j Q a d
      = ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k) 0 (N / 2 + 1)
            (Q * d) (crtClassG Q d N a) := by
  unfold goldBlockHonestDiscW goldBlockBoxHonestDisc
  rw [goldBlockResCountM_eq_sum_pieces, goldBlockUnitCountM_eq_sum_pieces, Finset.mul_sum,
    ← Finset.sum_sub_distrib]

/-- **The triangle over the pieces.** -/
theorem gold_abs_blockHonestDiscW_le_sum_pieces (N z y : ℕ) (ε₀ : ℝ) (j Q a d : ℕ) :
    |goldBlockHonestDiscW N z y ε₀ j Q a d|
      ≤ ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          |goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k) 0 (N / 2 + 1)
            (Q * d) (crtClassG Q d N a)| := by
  rw [goldBlockHonestDiscW_eq_sum_pieces]
  exact Finset.abs_sum_le_sum_abs _ _

/-! ## Part C — the `m`-range split of the box counts (ordering-clear ⊔ band) -/

open Classical in
/-- **The `m`-range split of the box residue count.**  For `a ≤ mid ≤ b`, the box `[a, b)`
partitions into `[a, mid) ⊔ [mid, b)` on the `m = p₁p₂` axis.  `blockBoxResCountW_split_m`'s
Goldbach mirror. -/
theorem goldBlockBoxResCount_split_m (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M a mid b d R₀ : ℕ)
    (hac : a ≤ mid) (hcb : mid ≤ b) :
    goldBlockBoxResCount Ne z y ε₀ j Nf M a b d R₀
      = goldBlockBoxResCount Ne z y ε₀ j Nf M a mid d R₀
        + goldBlockBoxResCount Ne z y ε₀ j Nf M mid b d R₀ := by
  classical
  unfold goldBlockBoxResCount
  rw [← Nat.cast_add, Nat.cast_inj,
    ← Finset.card_filter_add_card_filter_not
        (s := (goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
          ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) ∧
          Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b))
        (p := fun t => t.1 * t.2.1 < mid)]
  congr 1
  · rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr ?_)
    intro t _
    constructor
    · rintro ⟨⟨hblk, hres, hN, hM, ham, _hmb⟩, hmc⟩
      exact ⟨hblk, hres, hN, hM, ham, hmc⟩
    · rintro ⟨hblk, hres, hN, hM, ham, hmc⟩
      exact ⟨⟨hblk, hres, hN, hM, ham, by omega⟩, hmc⟩
  · rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr ?_)
    intro t _
    constructor
    · rintro ⟨⟨hblk, hres, hN, hM, _ham, hmb⟩, hmc⟩
      exact ⟨hblk, hres, hN, hM, by omega, hmb⟩
    · rintro ⟨hblk, hres, hN, hM, hcm, hmb⟩
      exact ⟨⟨hblk, hres, hN, hM, by omega, hmb⟩, by omega⟩

open Classical in
/-- **The `m`-range split of the box unit count.** -/
theorem goldBlockBoxUnitCount_split_m (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M a mid b d : ℕ)
    (hac : a ≤ mid) (hcb : mid ≤ b) :
    goldBlockBoxUnitCount Ne z y ε₀ j Nf M a b d
      = goldBlockBoxUnitCount Ne z y ε₀ j Nf M a mid d
        + goldBlockBoxUnitCount Ne z y ε₀ j Nf M mid b d := by
  classical
  unfold goldBlockBoxUnitCount
  rw [← Nat.cast_add, Nat.cast_inj,
    ← Finset.card_filter_add_card_filter_not
        (s := (goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
          IsUnit ((prod3 t : ℕ) : ZMod d) ∧
          Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b))
        (p := fun t => t.1 * t.2.1 < mid)]
  congr 1
  · rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr ?_)
    intro t _
    constructor
    · rintro ⟨⟨hblk, hu, hN, hM, ham, _hmb⟩, hmc⟩
      exact ⟨hblk, hu, hN, hM, ham, hmc⟩
    · rintro ⟨hblk, hu, hN, hM, ham, hmc⟩
      exact ⟨⟨hblk, hu, hN, hM, ham, by omega⟩, hmc⟩
  · rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr ?_)
    intro t _
    constructor
    · rintro ⟨⟨hblk, hu, hN, hM, _ham, hmb⟩, hmc⟩
      exact ⟨hblk, hu, hN, hM, by omega, hmb⟩
    · rintro ⟨hblk, hu, hN, hM, hcm, hmb⟩
      exact ⟨⟨hblk, hu, hN, hM, by omega, hmb⟩, by omega⟩

/-- **The `m`-range split of the box honest discrepancy** — the splitter for Part D (ordering-clear
`[0, min(z·Nf+1, Ne/2+1))` + band `[min(z·Nf+1, Ne/2+1), Ne/2+1)`).  `blockBoxHonestDiscW_split_m`'s
Goldbach mirror. -/
theorem goldBlockBoxHonestDisc_split_m (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M a mid b d R₀ : ℕ)
    (hac : a ≤ mid) (hcb : mid ≤ b) :
    goldBlockBoxHonestDisc Ne z y ε₀ j Nf M a b d R₀
      = goldBlockBoxHonestDisc Ne z y ε₀ j Nf M a mid d R₀
        + goldBlockBoxHonestDisc Ne z y ε₀ j Nf M mid b d R₀ := by
  unfold goldBlockBoxHonestDisc
  rw [goldBlockBoxResCount_split_m Ne z y ε₀ j Nf M a mid b d R₀ hac hcb,
    goldBlockBoxUnitCount_split_m Ne z y ε₀ j Nf M a mid b d hac hcb]
  ring

/-! ## Part D — the per-block assembly: `gold_hBlockW_of_window_prices` -/

open Classical in
/-- **`gold_hBlockW_of_window_prices`** — the Goldbach mirror of `hBlockW_of_window_prices`: the
per-block honest-discrepancy `L¹`-over-`d` sum is bounded by the high-piece prices `Phi` plus the
named band budget `Plo`.  Each piece box `(0, N/2+1)` splits at `c k = min(z·pieceN k+1, N/2+1)`
into the ordering-clear sub-box (priced by `gold_hNum_at_opW`, Part E) and the band sub-box (priced
by `gold_PloW_discharge`, Part F).  Output = the exact per-block shape
`gold_hBVblocksW_of_generalBV`'s `hHD` consumes blockwise. -/
theorem gold_hBlockW_of_window_prices (N z y : ℕ) (ε₀ : ℝ) (Q a Ps : ℕ) (bound : ℝ) (j : ℕ)
    (Phi : ℕ → ℝ) (Plo : ℝ)
    (hHigh : ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k) 0
                 (min (z * pieceN k + 1) (N / 2 + 1)) (Q * d) (crtClassG Q d N a)| else 0) ≤ Phi k)
    (hLow : (∑ k ∈ Finset.range (Nat.log 2 N + 1), ∑ d ∈ Nat.divisors Ps,
                if (d : ℝ) < bound then
                  |goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k)
                     (min (z * pieceN k + 1) (N / 2 + 1)) (N / 2 + 1) (Q * d)
                     (crtClassG Q d N a)| else 0) ≤ Plo) :
    (∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |goldBlockHonestDiscW N z y ε₀ j Q a d| else 0)
      ≤ (∑ k ∈ Finset.range (Nat.log 2 N + 1), Phi k) + Plo := by
  classical
  set c : ℕ → ℕ := fun k => min (z * pieceN k + 1) (N / 2 + 1) with hc
  have hterm : ∀ d : ℕ,
      (if (d : ℝ) < bound then |goldBlockHonestDiscW N z y ε₀ j Q a d| else 0)
        ≤ ∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ((if (d : ℝ) < bound then
                |goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k) 0 (c k)
                  (Q * d) (crtClassG Q d N a)| else 0)
              + (if (d : ℝ) < bound then
                |goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k) (c k) (N / 2 + 1)
                  (Q * d) (crtClassG Q d N a)| else 0)) := by
    intro d
    by_cases hd : (d : ℝ) < bound
    · rw [if_pos hd]
      refine le_trans (gold_abs_blockHonestDiscW_le_sum_pieces N z y ε₀ j Q a d) ?_
      refine Finset.sum_le_sum (fun k _ => ?_)
      rw [if_pos hd, if_pos hd]
      have hsplit := goldBlockBoxHonestDisc_split_m N z y ε₀ j (pieceN k) (pieceM k) 0 (c k)
        (N / 2 + 1) (Q * d) (crtClassG Q d N a) (Nat.zero_le _) (min_le_right _ _)
      rw [hsplit]
      exact abs_add_le _ _
    · rw [if_neg hd]
      refine Finset.sum_nonneg (fun k _ => ?_)
      simp only [if_neg hd]; positivity
  calc (∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then |goldBlockHonestDiscW N z y ε₀ j Q a d| else 0)
      ≤ ∑ d ∈ Nat.divisors Ps, ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ((if (d : ℝ) < bound then
              |goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k) 0 (c k)
                (Q * d) (crtClassG Q d N a)| else 0)
            + (if (d : ℝ) < bound then
              |goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k) (c k) (N / 2 + 1)
                (Q * d) (crtClassG Q d N a)| else 0)) :=
        Finset.sum_le_sum (fun d _ => hterm d)
    _ = ∑ k ∈ Finset.range (Nat.log 2 N + 1), ∑ d ∈ Nat.divisors Ps,
          ((if (d : ℝ) < bound then
              |goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k) 0 (c k)
                (Q * d) (crtClassG Q d N a)| else 0)
            + (if (d : ℝ) < bound then
              |goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k) (c k) (N / 2 + 1)
                (Q * d) (crtClassG Q d N a)| else 0)) :=
        Finset.sum_comm
    _ = (∑ k ∈ Finset.range (Nat.log 2 N + 1), ∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k) 0 (c k)
                (Q * d) (crtClassG Q d N a)| else 0)
          + (∑ k ∈ Finset.range (Nat.log 2 N + 1), ∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k) (c k) (N / 2 + 1)
                (Q * d) (crtClassG Q d N a)| else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
    _ ≤ (∑ k ∈ Finset.range (Nat.log 2 N + 1), Phi k) + Plo :=
        add_le_add (Finset.sum_le_sum (fun k hk => hHigh k hk)) hLow

/-! ## Part E — the box pricing: `gold_hNum_at_opW` (annulus sum ∘ `box_disc_three_way`) -/

open Classical in
/-- **`gold_hNum_at_opW`** — the Goldbach mirror of `hNum_at_opW`, reshaped to the OUTER DYADIC
ANNULUS structure.  Where the twin prices a SINGLE T-difference (`T = x`, `T = x/2+1`) via one
`box_disc_three_way`, the Goldbach window `[2, N/2]` telescopes into the `⌊log₂ N⌋+1` factor-2
annuli (`WindowSW.goldBoxHonestDisc_le_annulus_sum`); each annulus `(goldCut N k, goldCut N (k+1)]`
is priced by `box_disc_three_way` at `T₁ = goldCut N k`, `T₂ = goldCut N (k+1)` (`goldCut_mono`
supplies `T₁ ≤ T₂`; the support floor `z·y` is the landed `medium_support_floor_high`).  The output
is the `Σ_k Σ_i Price k i` DOUBLE sum — the one extra `log` Opt-A pays (absorbed downstream by the
BV backbone at `A+1`).  `Dset := ((divisors Ps).filter (·<bound)).image (Q·)`,
`r := fun m => crtClassG Q (m/Q) N a`. -/
theorem gold_hNum_at_opW {N z y : ℕ} {ε₀ : ℝ} {j Nf M lo hi X : ℕ} (K Q a Ps : ℕ) (bound : ℝ)
    (Price : ℕ → ℕ → ℝ)
    (hN2 : 2 ≤ N) (hQ1 : 1 ≤ Q)
    (hz : 1 ≤ z) (hbX : hi ≤ X + 1) (hord : hi ≤ z * Nf + 1) (hK : Nat.log 2 X ≤ K)
    (hiX : ∀ k, ∀ i ∈ dyadicBoundary Nf M (goldCut N k) (goldCut N (k + 1)) (z * y) K,
        2 ^ (i + 1) ≤ X + 1)
    (hprice : ∀ k, ∀ i ∈ dyadicBoundary Nf M (goldCut N k) (goldCut N (k + 1)) (z * y) K,
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) lo hi)
                (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd Nf) (2 ^ (i + 1) - 1) M
                (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter
                (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) lo hi)
                  (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd Nf) (2 ^ (i + 1) - 1) M
                  (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
          ≤ Price k i) :
    (∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |goldBlockBoxHonestDisc N z y ε₀ j Nf M lo hi (Q * d) (crtClassG Q d N a)| else 0)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary Nf M (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price k i := by
  classical
  have hQ0 : 0 < Q := hQ1
  set Dset := ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d)
    with hDset
  rw [← Finset.sum_filter]
  have hLHS : ∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
        |goldBlockBoxHonestDisc N z y ε₀ j Nf M lo hi (Q * d) (crtClassG Q d N a)|
      = ∑ m ∈ Dset, |goldBlockBoxHonestDisc N z y ε₀ j Nf M lo hi m
          (crtClassG Q (m / Q) N a)| := by
    rw [hDset, Finset.sum_image (fun d₁ _ d₂ _ h => Nat.eq_of_mul_eq_mul_left hQ0 h)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Nat.mul_div_cancel_left d hQ0]
  rw [hLHS]
  refine le_trans (goldBoxHonestDisc_le_annulus_sum (Ne := N) (Nf := Nf) (M := M)
    (a := lo) (b := hi) (X := X) (fun m => crtClassG Q (m / Q) N a) Dset hN2 hz hbX hord) ?_
  refine Finset.sum_le_sum (fun k _ => ?_)
  exact box_disc_three_way K hK (goldCut_mono N (Nat.le_succ k))
    (fun m hm => medium_support_floor_high hm) Dset (fun m => crtClassG Q (m / Q) N a)
    (Price k) (hiX k) (hprice k)

/-! ## Part G — the band rectangle prices via the annulus-sum telescopes -/

open Classical in
/-- **`gold_PloW_sym_of_box_disc`** — the sym-band rectangle prices, the `hSym` input of the
band close.  Goldbach mirror of `PloW_sym_of_box_disc`: per piece `k'` the `Dset`-sum of symmetric
honest discrepancies telescopes (via `BandIdent.goldBandSymRectDisc_le_annulus_sum`) into the
`Σ_k` of the per-annulus carrier T-differences, bounded by `PsymK k'` (`hdiffK`; G-PDIAG discharges
each annulus by `box_disc_three_way` at `blockAlphaSym`, floor `medium_support_floor_sym`).  The
Goldbach `Σ_k` (the annulus telescope) is the one extra `log` vs the twin's single T-difference. -/
theorem gold_PloW_sym_of_box_disc {N z y : ℕ} {ε₀ : ℝ} {j X Q a : ℕ} (Ps : ℕ) (bound : ℝ)
    (PsymK : ℕ → ℝ) (hN2 : 2 ≤ N) (hQ1 : 1 ≤ Q) (hNeX : N / 2 ≤ X)
    (hdiffK : ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
        (∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k') (pieceM k'))
                (blockPrimeInd (max y (pieceN k'))) X (pieceM k') (crtClassG Q (m / Q) N a) m
                (goldCut N (k + 1))
              - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k') (pieceM k'))
                (blockPrimeInd (max y (pieceN k'))) X (pieceM k') (crtClassG Q (m / Q) N a) m
                (goldCut N k)‖) ≤ PsymK k') :
    (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |goldBandSymRectDisc N z y ε₀ j (pieceN k') (pieceM k') (Q * d)
            (crtClassG Q d N a)| else 0)
      ≤ ∑ k' ∈ Finset.range (Nat.log 2 N + 1), PsymK k' := by
  classical
  have hQ0 : 0 < Q := hQ1
  refine Finset.sum_le_sum (fun k' hk' => ?_)
  rw [← Finset.sum_filter]
  have hLHS : ∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
        |goldBandSymRectDisc N z y ε₀ j (pieceN k') (pieceM k') (Q * d) (crtClassG Q d N a)|
      = ∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
          |goldBandSymRectDisc N z y ε₀ j (pieceN k') (pieceM k') m
            (crtClassG Q (m / Q) N a)| := by
    rw [Finset.sum_image (fun d₁ _ d₂ _ h => Nat.eq_of_mul_eq_mul_left hQ0 h)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Nat.mul_div_cancel_left d hQ0]
  rw [hLHS]
  exact le_trans (goldBandSymRectDisc_le_annulus_sum (Ne := N) (Nf := pieceN k')
    (M := pieceM k') (X := X) (fun m => crtClassG Q (m / Q) N a) _ hN2 hNeX) (hdiffK k' hk')

open Classical in
/-- **`gold_PloW_low_of_box_disc`** — the low-band rectangle prices, the `hLow` input of the band
close.  Goldbach mirror of `PloW_low_of_box_disc` (via `BandIdent.goldBandLowDisc_le_annulus_sum`;
G-PDIAG discharges each annulus by `box_disc_three_way` at `blockAlphaLow`, floor
`medium_support_floor_low`).  The band `m`-range is `[min(z·pieceN k'+1, N/2+1), N/2+1)`. -/
theorem gold_PloW_low_of_box_disc {N z y : ℕ} {ε₀ : ℝ} {j X Q a : ℕ} (Ps : ℕ) (bound : ℝ)
    (PlowK : ℕ → ℝ) (hN2 : 2 ≤ N) (hQ1 : 1 ≤ Q) (hNeX : N / 2 + 1 ≤ X + 1)
    (hdiffK : ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
        (∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k'))
                  (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
                (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
                (goldCut N (k + 1))
              - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k'))
                  (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
                (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
                (goldCut N k)‖) ≤ PlowK k') :
    (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |goldBandLowDisc N z y ε₀ j (pieceN k') (pieceM k')
            (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1) (Q * d) (crtClassG Q d N a)| else 0)
      ≤ ∑ k' ∈ Finset.range (Nat.log 2 N + 1), PlowK k' := by
  classical
  have hQ0 : 0 < Q := hQ1
  refine Finset.sum_le_sum (fun k' hk' => ?_)
  rw [← Finset.sum_filter]
  have hLHS : ∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
        |goldBandLowDisc N z y ε₀ j (pieceN k') (pieceM k')
          (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1) (Q * d) (crtClassG Q d N a)|
      = ∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
          |goldBandLowDisc N z y ε₀ j (pieceN k') (pieceM k')
            (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1) m (crtClassG Q (m / Q) N a)| := by
    rw [Finset.sum_image (fun d₁ _ d₂ _ h => Nat.eq_of_mul_eq_mul_left hQ0 h)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Nat.mul_div_cancel_left d hQ0]
  rw [hLHS]
  exact le_trans (goldBandLowDisc_le_annulus_sum (Ne := N) (Nf := pieceN k')
    (M := pieceM k') (a := min (z * pieceN k' + 1) (N / 2 + 1)) (b := N / 2 + 1) (X := X)
    (fun m => crtClassG Q (m / Q) N a) _ hN2 hNeX) (hdiffK k' hk')

/-! ## Part F — the honest three-piece band-close triangle (G-PDIAG's `PloW_honest` slot)

Design note (deviation): the twin's crude `PloW_discharge` (SwitchW2 Part F) prices the diagonal by
`goldBandDiagCount_le` — infeasible at the razor margin (catch #68).  The Goldbach terminal
`gold_hBVblocksW_discharge'` routes through the HONEST diagonal (`Band.gold_diag_residue_crumb`,
G-PDIAG's `diagAggW_le_honest`), so the band-close bound G-PDIAG actually consumes is the honest
triangle below (which KEEPS `goldBandDiagDisc`), not the crude supplier.  The crude
`gold_PloW_discharge` is therefore not built (it would need the unbuilt `goldDiagSum` count bounds
and is dead weight for the honest terminal). -/

/-- **`gold_bandDiscW_le_three_pieces_diag`** — the per-`(k', d)` band triangle KEEPING the diagonal
disc; the Goldbach mirror of `Salt.Chen.bandDiscW_le_three_pieces_diag`.  Composes
`BandIdent.goldBandDiscW_eq_three` (the count-level `½sym + ½diag + low` decomposition) with the
triangle inequality.  G-PDIAG's `PloW_honest` sums this over `(k', d)` and prices the three legs by
`gold_PloW_sym_of_box_disc` / `gold_PloW_low_of_box_disc` / `diagAggW_le_honest`. -/
theorem gold_bandDiscW_le_three_pieces_diag (N z y : ℕ) (ε₀ : ℝ) (j Nf M d R₀ : ℕ) (hz : 1 ≤ z) :
    |goldBlockBoxHonestDisc N z y ε₀ j Nf M (min (z * Nf + 1) (N / 2 + 1)) (N / 2 + 1) d R₀|
      ≤ (1 / 2) * |goldBandSymRectDisc N z y ε₀ j Nf M d R₀|
        + |goldBandLowDisc N z y ε₀ j Nf M (min (z * Nf + 1) (N / 2 + 1)) (N / 2 + 1) d R₀|
        + (1 / 2) * |goldBandDiagDisc N z y ε₀ j Nf M d R₀| := by
  rw [goldBandDiscW_eq_three N z y ε₀ j Nf M d R₀ hz]
  have h1 := abs_add_le ((1 / 2) * goldBandSymRectDisc N z y ε₀ j Nf M d R₀
    + (1 / 2) * goldBandDiagDisc N z y ε₀ j Nf M d R₀)
    (goldBandLowDisc N z y ε₀ j Nf M (min (z * Nf + 1) (N / 2 + 1)) (N / 2 + 1) d R₀)
  have h2 := abs_add_le ((1 / 2) * goldBandSymRectDisc N z y ε₀ j Nf M d R₀)
    ((1 / 2) * goldBandDiagDisc N z y ε₀ j Nf M d R₀)
  rw [abs_mul, abs_mul, show |(1 : ℝ) / 2| = 1 / 2 by norm_num] at h2
  linarith

/-! ## Composition sanity — the byte-locked deliverables G-PDIAG consumes

The Goldbach terminal `gold_hBVblocksW_discharge'` (G-PDIAG) is discharged by chaining, per block:
`gold_hBlockW_of_window_prices` (Part D) ← `gold_hNum_at_opW` (Part E, the ordering-clear box) and
the honest band close (`gold_bandDiscW_le_three_pieces_diag` + `gold_PloW_sym_of_box_disc` /
`gold_PloW_low_of_box_disc` + G-PDIAG's `diagAggW_le_honest`), then
`SwitchBV.gold_hBVblocksW_of_generalBV`.  Every hypothesis of the pricers is a `box_disc_three_way`
input at the per-annulus survivor prices (blockAlpha / blockAlphaSym / blockAlphaLow; floors
`medium_support_floor_high/sym/low`), summed over the `⌊log₂N⌋+1` annuli — the one extra `log`. -/

section CompositionSanity

#check @Salt.Goldbach.gold_hBlockW_of_window_prices
#check @Salt.Goldbach.gold_hNum_at_opW
#check @Salt.Goldbach.gold_PloW_sym_of_box_disc
#check @Salt.Goldbach.gold_PloW_low_of_box_disc
#check @Salt.Goldbach.gold_bandDiscW_le_three_pieces_diag
#check @Salt.Goldbach.goldBlockHonestDiscW_eq_sum_pieces
#check @Salt.Goldbach.goldBlockBoxHonestDisc_split_m
#check @Salt.Chen.box_disc_three_way
#check @Salt.Goldbach.goldBoxHonestDisc_le_annulus_sum
#check @Salt.Goldbach.gold_hBVblocksW_of_generalBV

end CompositionSanity

end Salt.Goldbach
