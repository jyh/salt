/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SwitchBV

/-!
# SW3b — the dyadic box decomposition of the switched honest discrepancy

Design: `docs/blueprints/flags.md`, entry "2026-07-13 SW3" (the closing `hHD` obligation of
`hBVswitch_of_generalBV`).  SW3 landed the honest per-`d` split and named `hHD`:

  `∑_{d ∣ Ps, d < bound} |switchHonestDisc x z y d| ≤ RHD`,

where `switchHonestDisc x z y d = switchResCount − ν(d)·switchUnitCount` is the residue-`2`
count of admissible triples minus the coprime (unit) main term (`SwitchBV.lean`).  The clean
identity `switchHonestDisc d = ‖apDiscBilin(α,β,…)‖` FAILS on the nose because `apDiscBilin`
carries NO product-window coupling while the triples carry the hard window `x/2+2 ≤ prod ≤ x`.
This file performs the honest combinatorial layer of the removal — the **double-dyadic box
partition** — and packages the reduction of `hHD` into per-box discrepancy sums.

## Numeric plan (recorded FIRST, per the C+ discipline)

Write each admissible triple `t = (p₁,p₂,p₃)` via `m = p₁p₂` (the semiprime block) and
`p = p₃`, so `prod3 t = m·p`.  Decompose the `(m,p)`-plane into dyadic boxes
`B_{i,j} = {2^i ≤ m < 2^{i+1}, 2^j ≤ p < 2^{j+1}}` indexed by `(i,j) = (⌊log₂ m⌋, ⌊log₂ p⌋)`.
Both `m, p ≤ prod ≤ x`, so `(i,j) ∈ [0,K]²` with `K = ⌊log₂ x⌋` — at most `(K+1)² = O(log²x)`
boxes.

* **The product-window support collapse (this file, `boxHonestDisc_zero_of_windowDisjoint`).**
  A box is *window-disjoint* if `x < 2^{i+j}` (whole box above `x`) or `2^{i+j+2} ≤ x/2+2`
  (whole box below the window floor).  Every admissible triple in box `(i,j)` has
  `2^{i+j} ≤ prod < 2^{i+j+2}` and `x/2+2 ≤ prod ≤ x`, so a window-disjoint box is EMPTY and
  contributes `0`.  Non-disjoint boxes pin `2^{i+j}` to the factor-`8` band `(x/8, x]`, i.e.
  `i+j ∈ {K−2, K−1, K}` — only `O(K) = O(log x)` boxes survive.  **This is a stronger support
  than the anticipated `O(log²x)`.**

* **The per-box price (SW3c, downstream).**  On a surviving box the honest discrepancy is
  reduced to `‖apDiscBilin (semiprimeBlockInd z y|block) (blockPrimeInd 2^j) 2^{i+1} 2^{j+1}
  2 d‖` (the window edge removed by a finer sub-decomposition) + a boundary/ordering
  correction.  `general_BV_final'` prices each `∑_d ‖apDiscBilin‖` at `≤ K·(2^i·2^j)/(log)^A`
  with `A` free; since `2^i·2^j ~ x` on a surviving box and there are `O(log x)` of them, the
  summed interior price is `O(log x)·x/(log x)^A = x/(log x)^{A−1} ≤ x/(log x)^{10}` for
  `A ≥ 11` (a threshold, generous against the S4 budget).  `Coprime 2 d` is FREE here
  (`switch_dvd_coprime_two`).

* **The residual (two genuine obstructions, flagged for SW3c, NOT glossed).**
  (i) *Window edge.*  A single dyadic box spans a factor `4` in the product `2^{i+j} → 2^{i+j+2}`,
  WIDER than the factor-`2` window `x/2 → x`; hence NO surviving box is wholly inside the window,
  and the coupling cannot be removed by equal dyadic blocking alone — a finer (asymmetric /
  sub-dyadic) split of the crossing boxes plus the boundary-count savings is required.
  (ii) *The `p₂ ≤ p₃` ordering.*  `tripleSet` carries `y < p₂ ≤ p₃`, which couples the
  `m`-side's large factor `p₂` to the `p`-side `p₃` and does NOT enter a product coefficient
  `α(m)·β(p)`; the honest fix is the "same-block diagonal" correction (`p₂, p₃` in one dyadic
  block) bounded crudely and summed with the `1/φ(d)` savings.  Both are named precisely below
  and in the flag; they are the SW3c analytic core.

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* `boxResCount` / `boxUnitCount` / `boxHonestDisc` — the per-box residue / unit / honest-disc
  counts (filters of `tripleSet` by the dyadic block of `p₁p₂` and `p₃`).
* `switchResCount_eq_sum_box` / `switchUnitCount_eq_sum_box` — the EXACT partition of the two
  counts over the `(K+1)²` boxes (`Finset.card_eq_sum_card_fiberwise` over
  `t ↦ (⌊log₂(p₁p₂)⌋, ⌊log₂ p₃⌋)`).  **Floor A: every triple lands in exactly one box.**
* `switchHonestDisc_eq_sum_box` / `abs_switchHonestDisc_le_sum_box` — the honest disc partitions
  and the triangle bound.
* `windowDisjoint` + `boxHonestDisc_zero_of_windowDisjoint` — **the interior/boundary
  classification: window-disjoint boxes vanish.**
* `abs_switchHonestDisc_le_sum_relevant` — the triangle bound restricted to the `O(log x)`
  surviving (non-disjoint) boxes.
* `hHD_of_generalBV_inputs` — **the reduction: `hHD` follows from a per-box discrepancy bound
  (the SW3c apDiscBilin/general_BV_final' price) over the surviving boxes plus a numeric
  closure.**  This is the exact `hHD` slot shape `hBVswitch_of_generalBV` consumes.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the double-dyadic box partition of the residue / unit counts -/

/-- **The per-box residue count.**  Admissible triples in the dyadic box `(i,j)` (i.e.
`⌊log₂(p₁p₂)⌋ = i`, `⌊log₂ p₃⌋ = j`) whose product is `≡ 2 (mod d)`. -/
noncomputable def boxResCount (x z y d i j : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => Nat.log 2 (t.1 * t.2.1) = i ∧ Nat.log 2 t.2.2 = j ∧
        ((prod3 t : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))).card : ℝ)

open Classical in
/-- **The per-box unit count.**  Admissible triples in the dyadic box `(i,j)` whose product is
a unit mod `d` (coprime to `d`); the support of the coprime main term. -/
noncomputable def boxUnitCount (x z y d i j : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => Nat.log 2 (t.1 * t.2.1) = i ∧ Nat.log 2 t.2.2 = j ∧
        IsUnit ((prod3 t : ℕ) : ZMod d))).card : ℝ)

/-- **The per-box honest discrepancy** — the residue count against the coprime main term,
restricted to the dyadic box `(i,j)`.  Summing over boxes recovers `switchHonestDisc`. -/
noncomputable def boxHonestDisc (x z y d i j : ℕ) : ℝ :=
  boxResCount x z y d i j - nuChen d * boxUnitCount x z y d i j

/-- **The box-partition kernel (FULL — Floor A).**  Any predicate-filtered count of `tripleSet`
partitions exactly over the `(K+1)²` dyadic boxes `(⌊log₂(p₁p₂)⌋, ⌊log₂ p₃⌋)`, `K = ⌊log₂ x⌋`.
Every admissible triple has `p₁p₂ ≤ prod ≤ x` and `p₃ ≤ prod ≤ x`, so both logs land in
`[0,K]`; `Finset.card_eq_sum_card_fiberwise` over the pair-of-logs map does the rest. -/
private lemma count_eq_sum_box {x z y : ℕ} (P : ℕ × ℕ × ℕ → Prop) [DecidablePred P] :
    (((tripleSet x z y).filter P).card : ℝ)
      = ∑ c ∈ Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.log 2 x + 1),
          (((tripleSet x z y).filter
              (fun t => Nat.log 2 (t.1 * t.2.1) = c.1
                ∧ Nat.log 2 t.2.2 = c.2 ∧ P t)).card : ℝ) := by
  classical
  have hmaps : ∀ t ∈ (tripleSet x z y).filter P,
      (Nat.log 2 (t.1 * t.2.1), Nat.log 2 t.2.2)
        ∈ Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.log 2 x + 1) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have htri := ht.1
    rw [tripleSet, Finset.mem_filter] at htri
    obtain ⟨_, _, _, _, _, hp1, hp2, hp3, _hlo, hhi⟩ := htri
    have hp3pos : 0 < t.2.2 := hp3.pos
    have hmpos : 0 < t.1 * t.2.1 := Nat.mul_pos hp1.pos hp2.pos
    have hprod : prod3 t = t.1 * t.2.1 * t.2.2 := rfl
    have hmle : t.1 * t.2.1 ≤ x := by
      calc t.1 * t.2.1 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_right _ hp3pos
        _ = prod3 t := hprod.symm
        _ ≤ x := hhi
    have hple : t.2.2 ≤ x := by
      calc t.2.2 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_left _ hmpos
        _ = prod3 t := hprod.symm
        _ ≤ x := hhi
    have h1 : Nat.log 2 (t.1 * t.2.1) ≤ Nat.log 2 x := Nat.log_mono_right hmle
    have h2 : Nat.log 2 t.2.2 ≤ Nat.log 2 x := Nat.log_mono_right hple
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le h1, Nat.lt_succ_of_le h2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hfilt : ((tripleSet x z y).filter P).filter
        (fun t => (Nat.log 2 (t.1 * t.2.1), Nat.log 2 t.2.2) = c)
      = (tripleSet x z y).filter
        (fun t => Nat.log 2 (t.1 * t.2.1) = c.1 ∧ Nat.log 2 t.2.2 = c.2 ∧ P t) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro t _
    constructor
    · rintro ⟨hP, hc⟩
      rw [Prod.ext_iff] at hc
      exact ⟨hc.1, hc.2, hP⟩
    · rintro ⟨h1, h2, hP⟩
      exact ⟨hP, Prod.ext h1 h2⟩
  rw [hfilt]

/-- **The residue count partitions over the boxes (FULL — Floor A).** -/
theorem switchResCount_eq_sum_box (x z y d : ℕ) :
    switchResCount x z y d
      = ∑ c ∈ Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.log 2 x + 1),
          boxResCount x z y d c.1 c.2 := by
  unfold switchResCount boxResCount
  exact count_eq_sum_box (fun t => ((prod3 t : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))

/-- **The unit count partitions over the boxes (FULL — Floor A).** -/
theorem switchUnitCount_eq_sum_box (x z y d : ℕ) :
    switchUnitCount x z y d
      = ∑ c ∈ Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.log 2 x + 1),
          boxUnitCount x z y d c.1 c.2 := by
  classical
  unfold switchUnitCount boxUnitCount
  exact count_eq_sum_box (fun t => IsUnit ((prod3 t : ℕ) : ZMod d))

/-- **The honest discrepancy partitions over the boxes (FULL — Floor A).**  From the residue /
unit partitions and linearity (`Finset.mul_sum`, `Finset.sum_sub_distrib`). -/
theorem switchHonestDisc_eq_sum_box (x z y d : ℕ) :
    switchHonestDisc x z y d
      = ∑ c ∈ Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.log 2 x + 1),
          boxHonestDisc x z y d c.1 c.2 := by
  unfold switchHonestDisc
  rw [switchResCount_eq_sum_box, switchUnitCount_eq_sum_box, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  rfl

/-- **The summed triangle bound (FULL — Floor A).**  `|switchHonestDisc d| ≤ ∑_box
|boxHonestDisc d|`. -/
theorem abs_switchHonestDisc_le_sum_box (x z y d : ℕ) :
    |switchHonestDisc x z y d|
      ≤ ∑ c ∈ Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.log 2 x + 1),
          |boxHonestDisc x z y d c.1 c.2| := by
  rw [switchHonestDisc_eq_sum_box]
  exact Finset.abs_sum_le_sum_abs _ _

/-! ## Part B — the interior/boundary classification: window-disjoint boxes vanish -/

/-- **The window-disjoint predicate.**  The dyadic box `(i,j)` cannot contain an admissible
triple: its whole product range `[2^{i+j}, 2^{i+j+2})` lies above `x` or below the window floor
`x/2+2`. -/
def windowDisjoint (x i j : ℕ) : Prop := x < 2 ^ (i + j) ∨ 2 ^ (i + j + 2) ≤ x / 2 + 2

instance (x i j : ℕ) : Decidable (windowDisjoint x i j) := by
  unfold windowDisjoint; infer_instance

/-- **Window-disjoint boxes are empty of admissible triples.**  Every `t ∈ tripleSet` with
`⌊log₂(p₁p₂)⌋ = i`, `⌊log₂ p₃⌋ = j` obeys `2^{i+j} ≤ prod < 2^{i+j+2}` (dyadic bounds on the two
factors) and `x/2+2 ≤ prod ≤ x` (the window); a window-disjoint box contradicts one of these. -/
private lemma tripleSet_box_windowDisjoint {x z y i j : ℕ} (h : windowDisjoint x i j) :
    ∀ t ∈ tripleSet x z y, Nat.log 2 (t.1 * t.2.1) = i → Nat.log 2 t.2.2 = j → False := by
  intro t ht hi hj
  rw [tripleSet, Finset.mem_filter] at ht
  obtain ⟨_, _, _, _, _, hp1, hp2, hp3, hlo, hhi⟩ := ht
  have hp3pos : 0 < t.2.2 := hp3.pos
  have hmpos : 0 < t.1 * t.2.1 := Nat.mul_pos hp1.pos hp2.pos
  have hmlo : 2 ^ i ≤ t.1 * t.2.1 := by
    have := Nat.pow_log_le_self 2 hmpos.ne'
    rwa [hi] at this
  have hplo : 2 ^ j ≤ t.2.2 := by
    have := Nat.pow_log_le_self 2 hp3pos.ne'
    rwa [hj] at this
  have hmhi : t.1 * t.2.1 < 2 ^ (i + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (t.1 * t.2.1)
    rwa [hi] at this
  have hphi : t.2.2 < 2 ^ (j + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) t.2.2
    rwa [hj] at this
  have hprod : prod3 t = t.1 * t.2.1 * t.2.2 := rfl
  have hlo2 : 2 ^ (i + j) ≤ prod3 t := by
    rw [hprod, pow_add]
    exact Nat.mul_le_mul hmlo hplo
  have hhi2 : prod3 t < 2 ^ (i + j + 2) := by
    rw [hprod]
    have he : (2 : ℕ) ^ (i + 1) * 2 ^ (j + 1) = 2 ^ (i + j + 2) := by
      rw [← pow_add]; congr 1; omega
    calc t.1 * t.2.1 * t.2.2 < 2 ^ (i + 1) * 2 ^ (j + 1) :=
          mul_lt_mul'' hmhi hphi (Nat.zero_le _) (Nat.zero_le _)
      _ = 2 ^ (i + j + 2) := he
  rcases h with hcase | hcase
  · omega
  · omega

/-- **Window-disjoint box counts vanish (FULL).**  Both the residue and unit box counts are `0`
on a window-disjoint box (the box filter is empty). -/
theorem boxCounts_zero_of_windowDisjoint (x z y d i j : ℕ) (h : windowDisjoint x i j) :
    boxResCount x z y d i j = 0 ∧ boxUnitCount x z y d i j = 0 := by
  have hcon := tripleSet_box_windowDisjoint (x := x) (z := z) (y := y) h
  refine ⟨?_, ?_⟩
  · unfold boxResCount
    rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro t ht ⟨hi, hj, _⟩
    exact hcon t ht hi hj
  · classical
    unfold boxUnitCount
    rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro t ht ⟨hi, hj, _⟩
    exact hcon t ht hi hj

/-- **Window-disjoint boxes carry no honest discrepancy (FULL — the classification).** -/
theorem boxHonestDisc_zero_of_windowDisjoint (x z y d i j : ℕ) (h : windowDisjoint x i j) :
    boxHonestDisc x z y d i j = 0 := by
  obtain ⟨hr, hu⟩ := boxCounts_zero_of_windowDisjoint x z y d i j h
  unfold boxHonestDisc
  rw [hr, hu, mul_zero, sub_zero]

/-- **The triangle bound over the surviving boxes only (FULL).**  The window-disjoint boxes drop
out (they contribute `0`), leaving the `O(log x)` non-disjoint boxes — the ones the SW3c
apDiscBilin price addresses. -/
theorem abs_switchHonestDisc_le_sum_relevant (x z y d : ℕ) :
    |switchHonestDisc x z y d|
      ≤ ∑ c ∈ (Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.log 2 x + 1)).filter
            (fun c => ¬ windowDisjoint x c.1 c.2),
          |boxHonestDisc x z y d c.1 c.2| := by
  refine le_trans (abs_switchHonestDisc_le_sum_box x z y d) (le_of_eq ?_)
  refine (Finset.sum_subset (Finset.filter_subset _ _) (fun c hc hcnot => ?_)).symm
  rw [Finset.mem_filter, not_and, not_not] at hcnot
  rw [boxHonestDisc_zero_of_windowDisjoint x z y d c.1 c.2 (hcnot hc), abs_zero]

/-! ## Part C — the reduction of `hHD` to the per-box discrepancy sums -/

/-- **`hHD_of_generalBV_inputs` — the SW3b reduction (FULL).**  The `hHD` obligation of
`hBVswitch_of_generalBV` follows from a per-box discrepancy bound over the surviving
(non-window-disjoint) boxes (`hBox` — the SW3c input: each `∑_d |boxHonestDisc d (i,j)|` priced
via the box's `apDiscBilin` through `general_BV_final'`) plus a numeric closure (`hSum`).

Composition: swap the `d`- and box-sums (`Finset.sum_comm`) after the per-`d` triangle bound
`abs_switchHonestDisc_le_sum_relevant`, then chain `hBox`, `hSum`.  The conclusion is the EXACT
`hHD` slot shape `hBVswitch_of_generalBV` consumes (`bound := Q·Dlev`).

What SW3c still owes each `RBox (i,j)`: the box discrepancy `∑_d |boxHonestDisc d (i,j)|`
priced by `general_BV_final'` — removing the window edge inside the box (a sub-dyadic split; the
box's factor-`4` product spread exceeds the factor-`2` window) and the `p₂ ≤ p₃` same-block
diagonal correction (see the module numeric plan and the flag). -/
theorem hHD_of_generalBV_inputs (x z y Ps : ℕ) (_hPs : Squarefree Ps)
    (_hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (bound : ℝ)
    (RBox : ℕ × ℕ → ℝ) {RHD : ℝ}
    (hBox : ∀ c ∈ (Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.log 2 x + 1)).filter
              (fun c => ¬ windowDisjoint x c.1 c.2),
        (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then |boxHonestDisc x z y d c.1 c.2| else 0) ≤ RBox c)
    (hSum : (∑ c ∈ (Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.log 2 x + 1)).filter
              (fun c => ¬ windowDisjoint x c.1 c.2), RBox c) ≤ RHD) :
    (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then |switchHonestDisc x z y d| else 0) ≤ RHD := by
  set B := (Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.log 2 x + 1)).filter
      (fun c => ¬ windowDisjoint x c.1 c.2) with hB
  have hterm : ∀ d : ℕ, (if (d : ℝ) < bound then |switchHonestDisc x z y d| else 0)
      ≤ ∑ c ∈ B, (if (d : ℝ) < bound then |boxHonestDisc x z y d c.1 c.2| else 0) := by
    intro d
    by_cases hd : (d : ℝ) < bound
    · simp only [if_pos hd]
      exact abs_switchHonestDisc_le_sum_relevant x z y d
    · rw [if_neg hd]
      exact Finset.sum_nonneg (fun c _ => le_of_eq (if_neg hd).symm)
  calc (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then |switchHonestDisc x z y d| else 0)
      ≤ ∑ d ∈ Nat.divisors Ps,
          ∑ c ∈ B, (if (d : ℝ) < bound then |boxHonestDisc x z y d c.1 c.2| else 0) :=
        Finset.sum_le_sum (fun d _ => hterm d)
    _ = ∑ c ∈ B,
          ∑ d ∈ Nat.divisors Ps,
            (if (d : ℝ) < bound then |boxHonestDisc x z y d c.1 c.2| else 0) :=
        Finset.sum_comm
    _ ≤ ∑ c ∈ B, RBox c := Finset.sum_le_sum (fun c hc => hBox c hc)
    _ ≤ RHD := hSum

end Salt.Chen
