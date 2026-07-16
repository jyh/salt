/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.SW2

/-!
# G-PDIAG — the honest diagonal close fills the abstract `Plo` slot (Goldbach terminal, wave W3b)

Design: `docs/exploration/pilot.md` (the band-chain arc: the re-cut, Opt-A, the landed
`WindowSW`/`BandIdent`/`SW2` interfaces) + the twin terminal `Salt/Chen/PDiag.lean`.  This file
is the Goldbach mirror of `Salt.Chen.hBVblocksW_discharge'` under `x ↦ N`, `crtClassW ↦ crtClassG`,
the reflected bottom-half window `2 ≤ prod ≤ N/2`, and the OUTER DYADIC ANNULUS axis threaded
through the box pricing (the "one extra `log`" Opt-A pays, absorbed by consuming BV at
saving `A+1`).

The crude diagonal aggregation (`½·τ(Ps)·Σ_k y·(pieceM k − pieceN k)`) is INFEASIBLE at the razor
margin (twin catch #68).  The terminal routes through the HONEST diagonal:

* **Ingredient (i) — the global diagonal support** (`goldDiagPairSet`,
  `sum_goldDiagTotal_le_goldDiagPairSet`, `goldDiagPairSet_card_le`): a diagonal triple is
  `(p₁, p, p)` with `p₁ ≤ y` and `p² ≤ p₁p² ≤ N/2 ⟹ p ≤ √N`, so the piece-summed class-free
  diagonal count is `≤ y·√N` GLOBALLY (each pair lives in ONE dyadic piece `k = ⌊log₂ p⌋`).
* **Ingredient (ii) — the residue crumb** (`Band.gold_diag_residue_crumb`, reused): per FIXED
  window point `v < N`, the admissible divisors meeting the reflected class `≡ N (mod d)` number
  `≤ 2^{Nat.log w' N}` — NOT `τ(Ps)`.
* **Ingredient (iii) — the ν-weighted unit side** (`Σ_{d ∣ Ps} ν(d)`): priced downstream by
  `Salt.Chen.nuChen_sum_divisors_le` (reused, carrier-free) at G-OP/G-ASM.
* **The keystone** (`gold_diagAggW_le_honest`): the aggregated guarded diagonal-disc double sum is
  `≤ y·√N·(2^{Nat.log w' N} + Σ_{d ∣ Ps} ν(d))`.
* **The honest band close** (`gold_bandDiscW_le_three_pieces_diag` [SW2] + `gold_PloW_honest`):
  the sym/low legs consumed VERBATIM from `gold_PloW_sym_of_box_disc`/`gold_PloW_low_of_box_disc`.
* **The terminal** (`gold_hBVblocksW_discharge'`): composes the box legs (`gold_hNum_at_opW`) + the
  honest band close + `SwitchBV.gold_hBVblocksW_of_generalBV`, consuming the windowed-BV backbone at
  saving `A+1`.  The box legs expose the extra annulus index (`Price : ℕ → ℕ → ℕ → ℕ → ℝ`); the
  sym/low legs absorb the annulus telescope into `PsymK/PlowK` (2-index, twin-shaped).

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]`).
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace Salt.Goldbach

open Salt.Chen

/-! ## Part A — ingredient (i): the global diagonal support -/

/-- `goldDiagSum` is nonnegative (a sum of `0/1` indicators). -/
lemma gold_diagSum_nonneg (N z y : ℕ) (ε₀ : ℝ) (j Nf M lo hi : ℕ) (C : ℕ → Prop) :
    0 ≤ goldDiagSum N z y ε₀ j Nf M lo hi C := by
  classical
  unfold goldDiagSum
  refine Finset.sum_nonneg (fun p₁ _ => Finset.sum_nonneg (fun p _ => ?_))
  split_ifs <;> norm_num

open Classical in
/-- **`goldDiagSum` as a filtered-product card** — the Goldbach mirror of `diagSum_eq_card`. -/
lemma gold_diagSum_eq_card (N z y : ℕ) (ε₀ : ℝ) (j Nf M lo hi : ℕ) (C : ℕ → Prop) :
    goldDiagSum N z y ε₀ j Nf M lo hi C
      = (((bandP1Set N z y ε₀ j ×ˢ bandLargeSet N y Nf M).filter
          (fun w => goldCwin lo hi C w.1 w.2 w.2)).card : ℝ) := by
  classical
  unfold goldDiagSum
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p₁ _ => ?_)
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : goldCwin lo hi C p₁ p p <;> simp [h]

/-- `goldDiagSum` is monotone toward the class-free count (the window conjuncts of `goldCwin` are
class-independent).  Mirror of `diagSum_le_diagSum_true`. -/
lemma gold_diagSum_le_diagSum_true (N z y : ℕ) (ε₀ : ℝ) (j Nf M lo hi : ℕ) (C : ℕ → Prop) :
    goldDiagSum N z y ε₀ j Nf M lo hi C ≤ goldDiagSum N z y ε₀ j Nf M lo hi (fun _ => True) := by
  classical
  unfold goldDiagSum
  refine Finset.sum_le_sum (fun p₁ _ => Finset.sum_le_sum (fun p _ => ?_))
  by_cases h : goldCwin lo hi C p₁ p p
  · have hwin : goldCwin lo hi (fun _ => True) p₁ p p := ⟨trivial, h.2.1, h.2.2⟩
    rw [if_pos h, if_pos hwin]
  · rw [if_neg h]
    split_ifs <;> norm_num

open Classical in
/-- **The global diagonal pair support.**  Pairs `(p₁, p)` with `p₁` a block small prime, `p > y`
prime, and the diagonal product `p₁·p²` in the bottom-half window `(1, N/2]`.  Every dyadic piece's
diagonal count fibres into it (`sum_goldDiagTotal_le_goldDiagPairSet`); its card is `≤ y·√N`
(`goldDiagPairSet_card_le`) — the `√N` cutoff from `p² ≤ p₁p² ≤ N/2 ≤ N`.  Mirrors `diagPairSet`. -/
noncomputable def goldDiagPairSet (N z y : ℕ) (ε₀ : ℝ) (j : ℕ) : Finset (ℕ × ℕ) :=
  (bandP1Set N z y ε₀ j ×ˢ ((Finset.Icc 1 N).filter (fun p => p.Prime ∧ y < p))).filter
    (fun w => 1 < w.1 * w.2 * w.2 ∧ w.1 * w.2 * w.2 ≤ N / 2)

/-- **The piece-summed class-free diagonal count is at most the global support card.**  Each pair
`(p₁, p)` lands in AT MOST ONE dyadic piece (`k = ⌊log₂ p⌋`).  Mirror of
`sum_diagTotal_le_diagPairSet`. -/
theorem sum_goldDiagTotal_le_goldDiagPairSet (N z y : ℕ) (ε₀ : ℝ) (j : ℕ) :
    (∑ k ∈ Finset.range (Nat.log 2 N + 1),
        goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2) (fun _ => True))
      ≤ ((goldDiagPairSet N z y ε₀ j).card : ℝ) := by
  classical
  unfold goldDiagSum
  rw [Finset.sum_comm]
  have hcard : ((goldDiagPairSet N z y ε₀ j).card : ℝ)
      = ∑ p₁ ∈ bandP1Set N z y ε₀ j,
          ∑ p ∈ (Finset.Icc 1 N).filter (fun p => p.Prime ∧ y < p),
            (if goldCwin 1 (N / 2) (fun _ => True) p₁ p p then (1 : ℝ) else 0) := by
    unfold goldDiagPairSet
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    refine Finset.sum_congr rfl (fun p₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
    by_cases h : 1 < p₁ * p * p ∧ p₁ * p * p ≤ N / 2
    · have hwin : goldCwin 1 (N / 2) (fun _ => True) p₁ p p := ⟨trivial, h.1, h.2⟩
      rw [if_pos h, if_pos hwin]; norm_num
    · have hnwin : ¬ goldCwin 1 (N / 2) (fun _ => True) p₁ p p := fun hc => h ⟨hc.2.1, hc.2.2⟩
      rw [if_neg h, if_neg hnwin]; norm_num
  rw [hcard]
  refine Finset.sum_le_sum (fun p₁ _ => ?_)
  calc (∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ p ∈ bandLargeSet N y (pieceN k) (pieceM k),
          (if goldCwin 1 (N / 2) (fun _ => True) p₁ p p then (1 : ℝ) else 0))
      = ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ p ∈ ((Finset.Icc 1 N).filter (fun p => p.Prime ∧ y < p)).filter
              (fun p => Nat.log 2 p = k),
            (if goldCwin 1 (N / 2) (fun _ => True) p₁ p p then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [bandLargeSet_piece_eq]
    _ = ∑ p ∈ ((Finset.Icc 1 N).filter (fun p => p.Prime ∧ y < p)).filter
          (fun p => Nat.log 2 p ∈ Finset.range (Nat.log 2 N + 1)),
        (if goldCwin 1 (N / 2) (fun _ => True) p₁ p p then (1 : ℝ) else 0) :=
        Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ p ∈ (Finset.Icc 1 N).filter (fun p => p.Prime ∧ y < p),
        (if goldCwin 1 (N / 2) (fun _ => True) p₁ p p then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => ?_)
        split_ifs <;> norm_num

/-- **Ingredient (i) — the global diagonal count is `≤ y·√N`.**  A diagonal pair has `p₁ ≤ y` and
`p·p ≤ p₁·p² ≤ N/2 ≤ N` so `p ≤ √N`.  Mirror of `diagPairSet_card_le`. -/
theorem goldDiagPairSet_card_le (N z y : ℕ) (ε₀ : ℝ) (j : ℕ) :
    ((goldDiagPairSet N z y ε₀ j).card : ℝ) ≤ (y : ℝ) * (Nat.sqrt N : ℝ) := by
  classical
  have hsub : goldDiagPairSet N z y ε₀ j ⊆ Finset.Icc 1 y ×ˢ Finset.Icc 1 (Nat.sqrt N) := by
    intro w hw
    unfold goldDiagPairSet at hw
    rw [Finset.mem_filter, Finset.mem_product] at hw
    obtain ⟨⟨h1, h2⟩, _hwlo, hwhi⟩ := hw
    rw [bandP1Set, Finset.mem_filter, Finset.mem_Icc] at h1
    rw [Finset.mem_filter, Finset.mem_Icc] at h2
    obtain ⟨⟨h1lo, _⟩, _, _, h1y, _⟩ := h1
    obtain ⟨⟨h2lo, _⟩, _, _⟩ := h2
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    have hpp : w.2 * w.2 ≤ N := by
      calc w.2 * w.2 ≤ w.1 * (w.2 * w.2) := Nat.le_mul_of_pos_left _ (by omega)
        _ = w.1 * w.2 * w.2 := by ring
        _ ≤ N / 2 := hwhi
        _ ≤ N := Nat.div_le_self _ _
    exact ⟨⟨h1lo, h1y⟩, h2lo, Nat.le_sqrt.mpr hpp⟩
  calc ((goldDiagPairSet N z y ε₀ j).card : ℝ)
      ≤ ((Finset.Icc 1 y ×ˢ Finset.Icc 1 (Nat.sqrt N)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (y : ℝ) * (Nat.sqrt N : ℝ) := by
        rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc, Nat.add_sub_cancel,
          Nat.add_sub_cancel]
        push_cast
        ring

/-! ## Part B — the keystone: the honest diagonal aggregate -/

/-- **`gold_diagAggW_le_honest` — the honest aggregated diagonal (the catch-#68 repair row).**
The full guarded diagonal-disc double sum over pieces `k` AND divisors `d` (at the Q-shifted
moduli `Q·d`, reflected residues `crtClassG Q d N a`) is bounded by

  `y·√N · (2^{Nat.log w' N} + Σ_{d ∣ Ps} ν(d))`

— ingredient (i) caps the support globally, ingredient (ii) caps the residue side per window point
by the `w'`-rough crumb (`Band.gold_diag_residue_crumb`, reused, NOT `τ(Ps)`), and the unit side
aggregates against `Σ ν(d)`.  Mirror of `Salt.Chen.diagAggW_le_honest`. -/
theorem gold_diagAggW_le_honest (N z y : ℕ) (ε₀ : ℝ) (Q a Ps w' : ℕ) (bound : ℝ) (j : ℕ)
    (hx : 2 ≤ N) (hQ1 : 1 ≤ Q) (hPs : Squarefree Ps) (hQPs : Nat.Coprime Q Ps)
    (hw' : 2 ≤ w') (hPw' : ∀ p ∈ Ps.primeFactors, w' ≤ p) :
    (∑ k ∈ Finset.range (Nat.log 2 N + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |goldBandDiagDisc N z y ε₀ j (pieceN k) (pieceM k) (Q * d) (crtClassG Q d N a)| else 0)
      ≤ (y : ℝ) * (Nat.sqrt N : ℝ)
          * ((2 : ℝ) ^ Nat.log w' N + ∑ d ∈ Nat.divisors Ps, nuChen d) := by
  classical
  set R := Finset.range (Nat.log 2 N + 1) with hRdef
  -- ① per (k, d): |diag disc| ≤ residue count + ν·unit count
  have habs : ∀ k d,
      |goldBandDiagDisc N z y ε₀ j (pieceN k) (pieceM k) (Q * d) (crtClassG Q d N a)|
      ≤ goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
          (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassG Q d N a : ℕ) : ZMod (Q * d)))
        + nuChen (Q * d) * goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
            (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) := by
    intro k d
    unfold goldBandDiagDisc
    have hR0 := gold_diagSum_nonneg N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
      (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassG Q d N a : ℕ) : ZMod (Q * d)))
    have hU0 := gold_diagSum_nonneg N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
      (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))
    have hc0 : 0 ≤ nuChen (Q * d) := by rw [nuChen_apply]; positivity
    have hcU : 0 ≤ nuChen (Q * d) * goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
        (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) := mul_nonneg hc0 hU0
    rw [abs_le]
    constructor
    · linarith
    · linarith
  -- ② split the guarded double sum into the residue leg + the unit leg
  have hsplit : (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |goldBandDiagDisc N z y ε₀ j (pieceN k) (pieceM k) (Q * d) (crtClassG Q d N a)| else 0)
      ≤ (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then
            goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
              (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassG Q d N a : ℕ) : ZMod (Q * d)))
          else 0)
        + (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then
            nuChen (Q * d) * goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
              (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))
          else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun d _ => ?_)
    by_cases hd : (d : ℝ) < bound
    · simp only [if_pos hd]; exact habs k d
    · simp only [if_neg hd]; norm_num
  -- ③ the residue leg: per window point, the crumb (ingredients (i)+(ii))
  have hres : (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
            (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassG Q d N a : ℕ) : ZMod (Q * d)))
        else 0)
      ≤ (2 : ℝ) ^ Nat.log w' N
          * ∑ k ∈ R, goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2) (fun _ => True) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    calc (∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then
            goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
              (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassG Q d N a : ℕ) : ZMod (Q * d)))
          else 0)
        = ∑ d ∈ Nat.divisors Ps,
            ∑ w ∈ bandP1Set N z y ε₀ j ×ˢ bandLargeSet N y (pieceN k) (pieceM k),
              (if (d : ℝ) < bound then
                (if goldCwin 1 (N / 2) (fun v => ((v : ℕ) : ZMod (Q * d))
                    = ((crtClassG Q d N a : ℕ) : ZMod (Q * d))) w.1 w.2 w.2
                  then (1 : ℝ) else 0) else 0) := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          by_cases hd : (d : ℝ) < bound
          · rw [if_pos hd, gold_diagSum_eq_card, ← Finset.sum_boole]
            exact Finset.sum_congr rfl (fun w _ => (if_pos hd).symm)
          · rw [if_neg hd]
            exact (Finset.sum_eq_zero (fun w _ => if_neg hd)).symm
      _ = ∑ w ∈ bandP1Set N z y ε₀ j ×ˢ bandLargeSet N y (pieceN k) (pieceM k),
            ∑ d ∈ Nat.divisors Ps,
              (if (d : ℝ) < bound then
                (if goldCwin 1 (N / 2) (fun v => ((v : ℕ) : ZMod (Q * d))
                    = ((crtClassG Q d N a : ℕ) : ZMod (Q * d))) w.1 w.2 w.2
                  then (1 : ℝ) else 0) else 0) := Finset.sum_comm
      _ ≤ ∑ w ∈ bandP1Set N z y ε₀ j ×ˢ bandLargeSet N y (pieceN k) (pieceM k),
            (2 : ℝ) ^ Nat.log w' N
              * (if goldCwin 1 (N / 2) (fun _ => True) w.1 w.2 w.2 then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum (fun w _ => ?_)
          by_cases hwin : 1 < w.1 * w.2 * w.2 ∧ w.1 * w.2 * w.2 ≤ N / 2
          · have hwinT : goldCwin 1 (N / 2) (fun _ => True) w.1 w.2 w.2 :=
              ⟨trivial, hwin.1, hwin.2⟩
            rw [if_pos hwinT, mul_one]
            have hvlt : w.1 * w.2 * w.2 < N :=
              lt_of_le_of_lt hwin.2 (Nat.div_lt_self (by omega) (by omega))
            calc (∑ d ∈ Nat.divisors Ps,
                  (if (d : ℝ) < bound then
                    (if goldCwin 1 (N / 2) (fun v => ((v : ℕ) : ZMod (Q * d))
                        = ((crtClassG Q d N a : ℕ) : ZMod (Q * d))) w.1 w.2 w.2
                      then (1 : ℝ) else 0) else 0))
                ≤ ∑ d ∈ Nat.divisors Ps,
                    (if ((w.1 * w.2 * w.2 : ℕ) : ZMod (Q * d))
                        = ((crtClassG Q d N a : ℕ) : ZMod (Q * d)) then (1 : ℝ) else 0) := by
                  refine Finset.sum_le_sum (fun d _ => ?_)
                  by_cases hg : (d : ℝ) < bound
                  · rw [if_pos hg]
                    by_cases hc : goldCwin 1 (N / 2) (fun v => ((v : ℕ) : ZMod (Q * d))
                        = ((crtClassG Q d N a : ℕ) : ZMod (Q * d))) w.1 w.2 w.2
                    · rw [if_pos hc, if_pos hc.1]
                    · rw [if_neg hc]; split_ifs <;> norm_num
                  · rw [if_neg hg]; split_ifs <;> norm_num
              _ = (((Nat.divisors Ps).filter
                    (fun d => ((w.1 * w.2 * w.2 : ℕ) : ZMod (Q * d))
                      = ((crtClassG Q d N a : ℕ) : ZMod (Q * d)))).card : ℝ) :=
                  Finset.sum_boole _ _
              _ ≤ (2 : ℝ) ^ Nat.log w' N := by
                  have hcr := gold_diag_residue_crumb (Q := Q) (Ps := Ps) (w' := w')
                    (N := N) (v := w.1 * w.2 * w.2) (a := a) hPs hw' hPw' hQPs hvlt
                  calc (((Nat.divisors Ps).filter
                        (fun d => ((w.1 * w.2 * w.2 : ℕ) : ZMod (Q * d))
                          = ((crtClassG Q d N a : ℕ) : ZMod (Q * d)))).card : ℝ)
                      ≤ ((2 ^ Nat.log w' N : ℕ) : ℝ) := by exact_mod_cast hcr
                    _ = (2 : ℝ) ^ Nat.log w' N := by push_cast; ring
          · have hz1 : ∀ d ∈ Nat.divisors Ps,
                (if (d : ℝ) < bound then
                  (if goldCwin 1 (N / 2) (fun v => ((v : ℕ) : ZMod (Q * d))
                      = ((crtClassG Q d N a : ℕ) : ZMod (Q * d))) w.1 w.2 w.2
                    then (1 : ℝ) else 0) else 0) = 0 := by
              intro d _
              by_cases hg : (d : ℝ) < bound
              · have hnc : ¬ goldCwin 1 (N / 2) (fun v => ((v : ℕ) : ZMod (Q * d))
                    = ((crtClassG Q d N a : ℕ) : ZMod (Q * d))) w.1 w.2 w.2 :=
                  fun hc => hwin ⟨hc.2.1, hc.2.2⟩
                rw [if_pos hg, if_neg hnc]
              · rw [if_neg hg]
            have hncT : ¬ goldCwin 1 (N / 2) (fun _ => True) w.1 w.2 w.2 :=
              fun hc => hwin ⟨hc.2.1, hc.2.2⟩
            rw [if_neg hncT, mul_zero]
            exact le_of_eq (Finset.sum_eq_zero hz1)
      _ = (2 : ℝ) ^ Nat.log w' N
            * goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2) (fun _ => True) := by
          rw [← Finset.mul_sum, Finset.sum_boole, ← gold_diagSum_eq_card]
  -- ④ the global support bound (ingredient (i))
  have hDGb : (∑ k ∈ R, goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2) (fun _ => True))
      ≤ (y : ℝ) * (Nat.sqrt N : ℝ) :=
    le_trans (sum_goldDiagTotal_le_goldDiagPairSet N z y ε₀ j)
      (goldDiagPairSet_card_le N z y ε₀ j)
  -- ⑤ the unit leg: `ν(Q·d) ≤ ν(d)`, support summed globally
  have hunit : (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          nuChen (Q * d) * goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
            (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))
        else 0)
      ≤ (∑ d ∈ Nat.divisors Ps, nuChen d) * ((y : ℝ) * (Nat.sqrt N : ℝ)) := by
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_le_sum (fun d hd => ?_)
    have hd1 : 0 < d := Nat.pos_of_mem_divisors hd
    have hν0 : 0 ≤ nuChen (Q * d) := by rw [nuChen_apply]; positivity
    have hνle : nuChen (Q * d) ≤ nuChen d := by
      rw [nuChen_apply, nuChen_apply]
      have hdvd : d.totient ∣ (Q * d).totient := Nat.totient_dvd_of_dvd (dvd_mul_left d Q)
      have hpos : 0 < (Q * d).totient := Nat.totient_pos.mpr (Nat.mul_pos hQ1 hd1)
      have hdpos : (0 : ℝ) < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd1
      apply one_div_le_one_div_of_le hdpos
      exact_mod_cast Nat.le_of_dvd hpos hdvd
    have hνd0 : 0 ≤ nuChen d := by rw [nuChen_apply]; positivity
    have hU0 : ∀ k ∈ R, 0 ≤ goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
        (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) := fun k _ =>
      gold_diagSum_nonneg N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2) _
    have hsumU : (∑ k ∈ R, goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
          (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))))
        ≤ (y : ℝ) * (Nat.sqrt N : ℝ) :=
      le_trans (Finset.sum_le_sum (fun k _ => gold_diagSum_le_diagSum_true N z y ε₀ j
        (pieceN k) (pieceM k) 1 (N / 2) _)) hDGb
    calc (∑ k ∈ R, if (d : ℝ) < bound then
            nuChen (Q * d) * goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
              (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) else 0)
        ≤ ∑ k ∈ R, nuChen (Q * d) * goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
            (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          split_ifs with h
          · exact le_refl _
          · exact mul_nonneg hν0 (hU0 k hk)
      _ = nuChen (Q * d) * ∑ k ∈ R, goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
            (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) := by rw [Finset.mul_sum]
      _ ≤ nuChen d * ((y : ℝ) * (Nat.sqrt N : ℝ)) :=
          mul_le_mul hνle hsumU (Finset.sum_nonneg hU0) hνd0
  -- ⑥ assemble
  have hresDG : (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
            (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassG Q d N a : ℕ) : ZMod (Q * d)))
        else 0)
      ≤ (2 : ℝ) ^ Nat.log w' N * ((y : ℝ) * (Nat.sqrt N : ℝ)) :=
    le_trans hres (mul_le_mul_of_nonneg_left hDGb (by positivity))
  calc (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |goldBandDiagDisc N z y ε₀ j (pieceN k) (pieceM k) (Q * d) (crtClassG Q d N a)| else 0)
      ≤ (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then
            goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
              (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassG Q d N a : ℕ) : ZMod (Q * d)))
          else 0)
        + (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then
            nuChen (Q * d) * goldDiagSum N z y ε₀ j (pieceN k) (pieceM k) 1 (N / 2)
              (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))
          else 0) := hsplit
    _ ≤ (2 : ℝ) ^ Nat.log w' N * ((y : ℝ) * (Nat.sqrt N : ℝ))
        + (∑ d ∈ Nat.divisors Ps, nuChen d) * ((y : ℝ) * (Nat.sqrt N : ℝ)) :=
        add_le_add hresDG hunit
    _ = (y : ℝ) * (Nat.sqrt N : ℝ)
        * ((2 : ℝ) ^ Nat.log w' N + ∑ d ∈ Nat.divisors Ps, nuChen d) := by ring

/-! ## Part C — the honest three-piece band close (`gold_PloW_honest`) -/

open Classical in
/-- **`gold_PloW_honest` — the honest three-piece supplier for the ABSTRACT `Plo` slot of
`gold_hBlockW_of_window_prices` (catch #68 repair (b)).**  The sym/low legs consume the VERBATIM
`hSym`/`hLow` shapes of `gold_PloW_sym_of_box_disc`/`gold_PloW_low_of_box_disc`; the diagonal is
priced by the NAMED `Pdiag` against its honest `y·√N·(crumb + Σν)` row (`gold_diagAggW_le_honest`).
Mirror of `Salt.Chen.PloW_honest`. -/
theorem gold_PloW_honest (N z y : ℕ) (ε₀ : ℝ) (Q a Ps w' : ℕ) (bound : ℝ) (j : ℕ)
    (Psym Plow Pdiag : ℝ)
    (hz : 1 ≤ z) (hx : 2 ≤ N) (hQ1 : 1 ≤ Q) (hPs : Squarefree Ps)
    (hQPs : Nat.Coprime Q Ps) (hw' : 2 ≤ w') (hPw' : ∀ p ∈ Ps.primeFactors, w' ≤ p)
    (hSym : (∑ k ∈ Finset.range (Nat.log 2 N + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |goldBandSymRectDisc N z y ε₀ j (pieceN k) (pieceM k) (Q * d)
            (crtClassG Q d N a)| else 0) ≤ Psym)
    (hLow : (∑ k ∈ Finset.range (Nat.log 2 N + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |goldBandLowDisc N z y ε₀ j (pieceN k) (pieceM k)
          (min (z * pieceN k + 1) (N / 2 + 1)) (N / 2 + 1) (Q * d)
          (crtClassG Q d N a)| else 0) ≤ Plow)
    (hDiag : (y : ℝ) * (Nat.sqrt N : ℝ)
        * ((2 : ℝ) ^ Nat.log w' N + ∑ d ∈ Nat.divisors Ps, nuChen d) ≤ Pdiag) :
    (∑ k ∈ Finset.range (Nat.log 2 N + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k)
             (min (z * pieceN k + 1) (N / 2 + 1)) (N / 2 + 1) (Q * d)
             (crtClassG Q d N a)| else 0)
      ≤ (1 / 2) * Psym + Plow + (1 / 2) * Pdiag := by
  classical
  set R := Finset.range (Nat.log 2 N + 1) with hR
  have hterm : ∀ (k d : ℕ),
      (if (d : ℝ) < bound then
          |goldBlockBoxHonestDisc N z y ε₀ j (pieceN k) (pieceM k)
             (min (z * pieceN k + 1) (N / 2 + 1)) (N / 2 + 1) (Q * d)
             (crtClassG Q d N a)| else 0)
        ≤ (1 / 2) * (if (d : ℝ) < bound then
              |goldBandSymRectDisc N z y ε₀ j (pieceN k) (pieceM k) (Q * d)
                (crtClassG Q d N a)| else 0)
          + (if (d : ℝ) < bound then |goldBandLowDisc N z y ε₀ j (pieceN k) (pieceM k)
              (min (z * pieceN k + 1) (N / 2 + 1)) (N / 2 + 1) (Q * d)
              (crtClassG Q d N a)| else 0)
          + (1 / 2) * (if (d : ℝ) < bound then
              |goldBandDiagDisc N z y ε₀ j (pieceN k) (pieceM k) (Q * d)
                (crtClassG Q d N a)| else 0) := by
    intro k d
    by_cases hd : (d : ℝ) < bound
    · simp only [if_pos hd]
      exact gold_bandDiscW_le_three_pieces_diag N z y ε₀ j (pieceN k) (pieceM k) (Q * d)
        (crtClassG Q d N a) hz
    · simp only [if_neg hd]; norm_num
  refine le_trans (Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun d _ =>
    hterm k d))) ?_
  have hsplit : ∀ k, (∑ d ∈ Nat.divisors Ps,
        ((1 / 2) * (if (d : ℝ) < bound then
              |goldBandSymRectDisc N z y ε₀ j (pieceN k) (pieceM k) (Q * d)
                (crtClassG Q d N a)| else 0)
          + (if (d : ℝ) < bound then |goldBandLowDisc N z y ε₀ j (pieceN k) (pieceM k)
              (min (z * pieceN k + 1) (N / 2 + 1)) (N / 2 + 1) (Q * d)
              (crtClassG Q d N a)| else 0)
          + (1 / 2) * (if (d : ℝ) < bound then
              |goldBandDiagDisc N z y ε₀ j (pieceN k) (pieceM k) (Q * d)
                (crtClassG Q d N a)| else 0)))
      = (1 / 2) * (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |goldBandSymRectDisc N z y ε₀ j (pieceN k) (pieceM k) (Q * d)
                (crtClassG Q d N a)| else 0)
        + (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then
            |goldBandLowDisc N z y ε₀ j (pieceN k) (pieceM k)
              (min (z * pieceN k + 1) (N / 2 + 1)) (N / 2 + 1) (Q * d)
              (crtClassG Q d N a)| else 0)
        + (1 / 2) * (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |goldBandDiagDisc N z y ε₀ j (pieceN k) (pieceM k) (Q * d)
                (crtClassG Q d N a)| else 0) := by
    intro k
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hsymS : (1 / 2) * (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |goldBandSymRectDisc N z y ε₀ j (pieceN k) (pieceM k) (Q * d)
            (crtClassG Q d N a)| else 0)
      ≤ (1 / 2) * Psym := mul_le_mul_of_nonneg_left hSym hhalf
  have hdiagS : (1 / 2) * (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |goldBandDiagDisc N z y ε₀ j (pieceN k) (pieceM k) (Q * d)
            (crtClassG Q d N a)| else 0)
      ≤ (1 / 2) * Pdiag :=
    mul_le_mul_of_nonneg_left
      (le_trans (gold_diagAggW_le_honest N z y ε₀ Q a Ps w' bound j hx hQ1 hPs hQPs hw' hPw')
        hDiag) hhalf
  linarith [hLow]

/-! ## Part D — the terminal: `gold_hBVblocksW_discharge'`

Catch-#68 non-applicability: the twin certificate `catch68_hSum_hNum_infeasible` requires its `hSum`
to carry the VERBATIM fixed summand `½·τ(Ps)·Σ_k y·(pieceM k − pieceN k)`.  The `hSum` below
carries `(1/2)·Pdiag` in that position, with `Pdiag` constrained only from BELOW by the honest
`hdiag` row `y·√N·(2^{Nat.log w' N} + Σν) ≤ Pdiag`; the certificate's hypotheses cannot be
instantiated against this bundle.  The box legs expose the annulus index (`Price j k' k i`, the one
extra `log`); the sym/low legs absorb the annulus telescope into `PsymK/PlowK` (twin-shaped). -/

open Classical in
/-- **`gold_hBVblocksW_discharge'` — THE COMPOSED W BLOCK-REMAINDER SUPPLIER (Goldbach terminal).**
Composes the box legs (`gold_hNum_at_opW`, annulus-telescoped) + the honest band close
(`gold_bandDiscW_le_three_pieces_diag` + `gold_PloW_sym_of_box_disc`/`gold_PloW_low_of_box_disc` +
`gold_diagAggW_le_honest`) via `gold_hBlockW_of_window_prices`, then
`SwitchBV.gold_hBVblocksW_of_generalBV`.  Emits the EXACT `hBVblocksW` slot (the summed W Rosser
remainders `≤ N/(log N)^10`).  Mirror of `Salt.Chen.hBVblocksW_discharge'` under `x ↦ N`,
`crtClassW ↦ crtClassG`, and the outer dyadic annulus axis. -/
theorem gold_hBVblocksW_discharge' (N z y : ℕ) (ε₀ : ℝ) (Q a Ps w' : ℕ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (hQPs : Nat.Coprime Q Ps)
    (hQ1 : 1 ≤ Q) (haN : a ≤ N)
    (QR : ℝ) (Dlev : ℕ) (X K : ℕ)
    (hz : 1 ≤ z) (hN2 : 2 ≤ N) (hNX : N / 2 ≤ X) (hK : Nat.log 2 X ≤ K)
    (hw'2 : 2 ≤ w') (hPw' : ∀ p ∈ Ps.primeFactors, w' ≤ p)
    (hiX : ∀ k', ∀ k, ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
        (goldCut N k) (goldCut N (k + 1)) (z * y) K, 2 ^ (i + 1) ≤ X + 1)
    (Price : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hprice : ∀ j k', ∀ k, ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (z * y) K,
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
                (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter
                (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                  (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
                  (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
          ≤ Price j k' k i)
    (PsymK PlowK : ℕ → ℕ → ℝ)
    (hpriceSym : ∀ j, ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
        (∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k') (pieceM k'))
                (blockPrimeInd (max y (pieceN k'))) X (pieceM k') (crtClassG Q (m / Q) N a) m
                (goldCut N (k + 1))
              - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k') (pieceM k'))
                (blockPrimeInd (max y (pieceN k'))) X (pieceM k') (crtClassG Q (m / Q) N a) m
                (goldCut N k)‖) ≤ PsymK j k')
    (hpriceLow : ∀ j, ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
        (∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k'))
                  (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
                (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
                (goldCut N (k + 1))
              - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k'))
                  (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
                (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
                (goldCut N k)‖) ≤ PlowK j k')
    (Pdiag RHD RCE : ℝ)
    (hdiag : (y : ℝ) * (Nat.sqrt N : ℝ)
        * ((2 : ℝ) ^ Nat.log w' N + ∑ d ∈ Nat.divisors Ps, nuChen d) ≤ Pdiag)
    (hSum : (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
        ((∑ k' ∈ Finset.range (Nat.log 2 N + 1),
            ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price j k' k i)
          + ((1 / 2) * (∑ k' ∈ Finset.range (Nat.log 2 N + 1), PsymK j k')
             + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), PlowK j k')
             + (1 / 2) * Pdiag))) ≤ RHD)
    (hCE : (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < QR * Dlev then goldBlockConvErrW N z y ε₀ j Q d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (N : ℝ) / (Real.log N) ^ 10) :
    -- the EXACT `hBVblocksW` slot (the summed W Rosser remainders):
    (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
        rosserRemainder (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd) (QR * Dlev))
      ≤ (N : ℝ) / (Real.log N) ^ 10 := by
  have hBlock : ∀ j ∈ Finset.range (maxBlock N z ε₀ + 1),
      (∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < QR * Dlev then |goldBlockHonestDiscW N z y ε₀ j Q a d| else 0)
        ≤ (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
            ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price j k' k i)
          + ((1 / 2) * (∑ k' ∈ Finset.range (Nat.log 2 N + 1), PsymK j k')
             + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), PlowK j k')
             + (1 / 2) * Pdiag) := by
    intro j _
    refine gold_hBlockW_of_window_prices N z y ε₀ Q a Ps (QR * Dlev) j
      (fun k' => ∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price j k' k i) _ ?_ ?_
    · intro k' _
      exact gold_hNum_at_opW K Q a Ps (QR * Dlev) (Price j k') hN2 hQ1 hz
        (le_trans (min_le_right _ _) (Nat.add_le_add_right hNX 1)) (min_le_left _ _)
        hK (hiX k') (hprice j k')
    · exact gold_PloW_honest N z y ε₀ Q a Ps w' (QR * Dlev) j _ _ Pdiag hz hN2 hQ1 hPs hQPs
        hw'2 hPw'
        (gold_PloW_sym_of_box_disc Ps (QR * Dlev) (PsymK j) hN2 hQ1 hNX (hpriceSym j))
        (gold_PloW_low_of_box_disc Ps (QR * Dlev) (PlowK j) hN2 hQ1
          (Nat.add_le_add_right hNX 1) (hpriceLow j))
        hdiag
  refine gold_hBVblocksW_of_generalBV N z y ε₀ Q a Ps hPs hPodd hQPs haN QR Dlev ?_ hCE hNum
  exact le_trans (Finset.sum_le_sum hBlock) hSum

/-! ## Composition sanity — the byte-locked deliverables (G-OP/G-ASM consume blind) -/

section CompositionSanity

-- ingredient (i) — the global diagonal support
#check @Salt.Goldbach.goldDiagPairSet
#check @Salt.Goldbach.gold_diagSum_eq_card
#check @Salt.Goldbach.gold_diagSum_le_diagSum_true
#check @Salt.Goldbach.sum_goldDiagTotal_le_goldDiagPairSet
#check @Salt.Goldbach.goldDiagPairSet_card_le
-- the keystone + the honest band close + the terminal
#check @Salt.Goldbach.gold_diagAggW_le_honest
#check @Salt.Goldbach.gold_PloW_honest
#check @Salt.Goldbach.gold_hBVblocksW_discharge'
-- ingredient (ii) — the residue crumb (Band.lean, reused)
#check @Salt.Goldbach.gold_diag_residue_crumb
-- the landed slots this composes with (SW2 / SwitchBV, verbatim reuse)
#check @Salt.Goldbach.gold_hBlockW_of_window_prices
#check @Salt.Goldbach.gold_hNum_at_opW
#check @Salt.Goldbach.gold_PloW_sym_of_box_disc
#check @Salt.Goldbach.gold_PloW_low_of_box_disc
#check @Salt.Goldbach.gold_bandDiscW_le_three_pieces_diag
#check @Salt.Goldbach.gold_hBVblocksW_of_generalBV
-- the ν-weighted unit side (Salt.Chen, carrier-free, reused downstream at G-OP)
#check @Salt.Chen.nuChen_sum_divisors_le

end CompositionSanity

end Salt.Goldbach
