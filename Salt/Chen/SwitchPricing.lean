/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SwitchDyadic
import Salt.Chen.AlphaSide

/-!
# SW3c — per-box discrepancy pricing (the SW3b residual)

Design: `docs/blueprints/flags.md`, entries "2026-07-13 SW3b … CATCH #48" and "2026-07-13 SW3".
SW3b (`SwitchDyadic.lean`) reduced the honest-discrepancy obligation `hHD` of
`hBVswitch_of_generalBV` to a per-box interface: `hHD_of_generalBV_inputs` consumes a per-box
price `RBox (i,j)` bounding `∑_{d∣Ps, d<bound} |boxHonestDisc d (i,j)|` and a closure
`∑_{surviving boxes} RBox ≤ RHD`.  This file (SW3c) prices the boxes.

## Numeric plan (recorded FIRST, per the C+ discipline)

`K = ⌊log₂ x⌋`.  A box `(i,j)` collects triples with `m = p₁p₂ ∈ [2^i, 2^{i+1})`,
`p = p₃ ∈ [2^j, 2^{j+1})`; its product spans `[2^{i+j}, 2^{i+j+2})`.  SW3b's
`windowDisjoint` classification (re-used here) shows only boxes with `i+j ∈ {K−2, K−1, K}`
survive — the factor-`8` band `x/8 < 2^{i+j} ≤ x`.  This file **proves** the resulting
count bound `#{surviving boxes} ≤ 3·(K+1) = O(log x)` (`card_relevantBoxes_le`) — the
combinatorial backbone of the closure.

* **The O(log x) count → uniform price closure (`hHD_of_uniform_price`, FULL here).**  If every
  surviving box is priced by a single uniform bound `P`, then
  `∑_{surviving} P = #boxes · P ≤ 3(K+1)·P`, and `hHD` closes as soon as `3(K+1)·P ≤ RHD`.
  With `general_BV`'s per-box price `P ~ K·(2^i·2^j)/(log)^A ~ x/(log x)^A` on a surviving box
  (`2^i·2^j ~ x`), the closure is `3(K+1)·x/(log x)^A = x/(log x)^{A−1}·O(1) ≤ x/(log x)^{10}`
  for `A ≥ 11` (a threshold, generous against the S4 budget).  This file collapses the entire
  `hHD` to that single uniform per-box price plus the numeric threshold `3(K+1)·P ≤ RHD`.

* **The per-box price → apDiscBilin (`box_price_of_apDiscBilin`, FULL here modulo the two
  NAMED analytic residuals).**  For a surviving box the summed honest discrepancy is priced by
  the box's bilinear AP-discrepancy `‖apDiscBilin (boxAlpha z y i) (blockPrimeInd 2^j)
  2^{i+1} 2^{j+1} 2 d‖` (whose `∑_d` is priced by `general_BV_final'`/`general_BV_alpha_discharged`
  at residue `R₀ = 2`, `Coprime 2 d` FREE by `switch_dvd_coprime_two`) plus a per-`d` correction
  `boxCorr d`.  The reduction is packaged so the designer plugs `general_BV_alpha_discharged`'s
  output into `hMain` in one line.

* **The two analytic residuals (NAMED as `hIdent`, `boxCorr` — the genuine SW3c core, NOT
  glossed).**
  (i) *The window edge / hyperbola sub-split.*  A box spans a factor `4` in the product vs the
  factor-`2` window `x/2 < mp ≤ x`; the windowed box count is the DIFFERENCE of two hyperbola-
  truncated counts (`mp ≤ x` minus `mp ≤ x/2`).  For fixed `p` the `m`-range is an initial
  segment `[2^i, min(2^{i+1}−1, T/p)]` — NOT the rectangle `apDiscBilin` measures.  The honest
  route sub-splits the `m`-block dyadically (`log x` sub-blocks) so each (sub-block, `p`-block)
  pair is wholly under/over/crossing the hyperbola; crossing pairs at each level contribute
  geometrically-decreasing counts, leaving a final `O(1)`-width crossing strip per `p`.  The
  crossing-strip total over a box is `≤ (#p)·O(1) = O(2^j)`; after the `∑_d 1/φd ~ log D`
  saving this contributes `2^j·log D`, within budget for `2^j ≤ x/(log)^{12}` — TRUE on every
  surviving box EXCEPT the top `O(1)` values of `j` (where `2^j ~ x`).  For those top-`j` boxes
  `m` is tiny (`2^i ~ 1`), so the box carries `O(1)` triples total and the crude
  `|boxHonestDisc| ≤ boxCount` bound (proven here as `abs_boxHonestDisc_le_boxCount`) already
  clears the budget.  This edge accounting is the content behind `hIdent`.
  (ii) *The `p₂ ≤ p₃` diagonal.*  `tripleSet` carries `y < p₂ ≤ p₃`; the coupling binds only
  when `p₂, p₃` sit in the same/adjacent dyadic block (`m = p₁p₂` carries `p₂` implicitly).
  Off-diagonal box pairs have the ordering free, so `α(m)·β(p)` factorizes; the same-block
  diagonal count is `≪ x/log` (both large primes near `√(x/p₁)`) and is absorbed into `boxCorr`.

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* `boxCount` + `abs_boxHonestDisc_le_boxCount` — the crude per-`(d,box)` bound
  `|boxHonestDisc d (i,j)| ≤ boxCount (i,j)` (the top-`j` fallback of the numeric plan).  **FULL.**
* `card_relevantBoxes_le` — **the `O(log x)` surviving-box count**: the non-window-disjoint
  boxes are contained in the band `i+j ∈ {K−2,K−1,K}`, hence at most `3(K+1)`.  **FULL.**
* `hHD_of_uniform_price` — **the closure**: `hHD` reduced to a single uniform per-box price `P`
  plus the numeric threshold `3(K+1)·P ≤ RHD`, discharging `hHD_of_generalBV_inputs`' `hSum`
  via the proven count.  **FULL.**
* `boxAlpha` + `norm_boxAlpha_le_one` — the box-restricted semiprime `m`-side coefficient
  (`‖α‖ ≤ 1`, the `general_BV_final'` hypothesis shape).
* `box_price_of_apDiscBilin` — **the per-box pricing reduction**: the summed honest discrepancy
  of one box is bounded by its `∑_d ‖apDiscBilin‖` price (fed by `general_BV_alpha_discharged`)
  plus the correction sum, given the two NAMED residuals `hIdent` (the window-edge/hyperbola
  identification) and `boxCorr`/`hCorrSum` (the diagonal correction).  **FULL modulo the named
  residuals.**

Composition for the designer: pick `P := Pmain + Pcorr` uniform over surviving boxes, discharge
each box by `box_price_of_apDiscBilin` (its `hMain` from `general_BV_alpha_discharged`), then
close via `hHD_of_uniform_price`.  The only genuinely-open mathematics is the two residuals of
`box_price_of_apDiscBilin` (window edge + diagonal) — flagged precisely, the SW3c analytic core.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the box count and the crude per-`(d, box)` discrepancy bound -/

/-- **The per-box triple count** (no residue condition): admissible triples landing in the
dyadic box `(i,j)`.  Upper-bounds both `boxResCount` and `boxUnitCount`, hence
`|boxHonestDisc d (i,j)|` for every `d`. -/
noncomputable def boxCount (x z y i j : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => Nat.log 2 (t.1 * t.2.1) = i ∧ Nat.log 2 t.2.2 = j)).card : ℝ)

/-- `boxResCount ≤ boxCount` (the residue-`2` filter is a sub-filter of the box filter). -/
theorem boxResCount_le_boxCount (x z y d i j : ℕ) :
    boxResCount x z y d i j ≤ boxCount x z y i j := by
  unfold boxResCount boxCount
  rw [Nat.cast_le]
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, ht.2.1, ht.2.2.1⟩

/-- `boxUnitCount ≤ boxCount` (the unit filter is a sub-filter of the box filter). -/
theorem boxUnitCount_le_boxCount (x z y d i j : ℕ) :
    boxUnitCount x z y d i j ≤ boxCount x z y i j := by
  classical
  unfold boxUnitCount boxCount
  rw [Nat.cast_le]
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, ht.2.1, ht.2.2.1⟩

/-- **`ν(d) ≤ 1`** for every `d` (`ν(d) = 1/φ(d)`, with `φ(d) ≥ 1` for `d ≥ 1` and the
`ArithmeticFunction` convention `ν(0) = 0`). -/
theorem nuChen_le_one (d : ℕ) : nuChen d ≤ 1 := by
  rw [nuChen_apply]
  rcases Nat.eq_zero_or_pos d.totient with h | h
  · rw [h, Nat.cast_zero, div_zero]; norm_num
  · rw [div_le_one (by exact_mod_cast h)]
    have h1 : (1 : ℕ) ≤ d.totient := h
    exact_mod_cast h1

/-- **The crude per-`(d, box)` discrepancy bound (FULL).**  `|boxHonestDisc d (i,j)| ≤
boxCount (i,j)`: since `boxResCount, boxUnitCount ∈ [0, boxCount]` and `ν(d) ∈ [0,1]`, both
`boxResCount − ν(d)·boxUnitCount ≤ boxCount` and its negation are `≤ boxCount`.  This is the
top-`j` fallback of the numeric plan: on the `O(1)` boxes where `2^j ~ x` (so `m ~ O(1)`, a
box of bounded triple count) this crude bound already clears the budget. -/
theorem abs_boxHonestDisc_le_boxCount (x z y d i j : ℕ) :
    |boxHonestDisc x z y d i j| ≤ boxCount x z y i j := by
  have hA0 : 0 ≤ boxResCount x z y d i j := by unfold boxResCount; positivity
  have hB0 : 0 ≤ boxUnitCount x z y d i j := by unfold boxUnitCount; positivity
  have hAC : boxResCount x z y d i j ≤ boxCount x z y i j := boxResCount_le_boxCount x z y d i j
  have hBC : boxUnitCount x z y d i j ≤ boxCount x z y i j := boxUnitCount_le_boxCount x z y d i j
  have hc0 : 0 ≤ nuChen d := by rw [nuChen_apply]; positivity
  have hc1 : nuChen d ≤ 1 := nuChen_le_one d
  have hcB : nuChen d * boxUnitCount x z y d i j ≤ boxUnitCount x z y d i j :=
    mul_le_of_le_one_left hB0 hc1
  have hcBnn : 0 ≤ nuChen d * boxUnitCount x z y d i j := mul_nonneg hc0 hB0
  unfold boxHonestDisc
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-! ## Part B — the `O(log x)` surviving-box count -/

/-- **The surviving boxes are `O(log x)` (FULL).**  The non-window-disjoint boxes all have
`i + j` in the factor-`8` band `{K−2, K−1, K}` (`K = ⌊log₂ x⌋`): `2^{i+j} ≤ x` forces
`i+j ≤ K`, and `x/2+2 < 2^{i+j+2}` (i.e. `x < 2^{i+j+3}`) forces `K ≤ i+j+2`.  Injecting
`(i,j) ↦ (i+j, i)` into `Icc (K−2) K ×ˢ range (K+1)` counts them: `≤ 3·(K+1)`. -/
theorem card_relevantBoxes_le {x : ℕ} (hx : 1 ≤ x) :
    ((Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.log 2 x + 1)).filter
        (fun c => ¬ windowDisjoint x c.1 c.2)).card ≤ 3 * (Nat.log 2 x + 1) := by
  set K := Nat.log 2 x with hKdef
  have hxne : x ≠ 0 := by omega
  have hxge : (2 : ℕ) ^ K ≤ x := by
    have h := Nat.pow_log_le_self 2 hxne; rwa [← hKdef] at h
  have hxub : x < 2 ^ (K + 1) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) x; rwa [← hKdef] at h
  set R := Finset.range (K + 1) ×ˢ Finset.range (K + 1) with hR
  have hBS : R.filter (fun c => ¬ windowDisjoint x c.1 c.2)
      ⊆ R.filter (fun c => c.1 + c.2 ≤ K ∧ K ≤ c.1 + c.2 + 2) := by
    intro c hc
    obtain ⟨hcR, hnd⟩ := Finset.mem_filter.mp hc
    simp only [windowDisjoint, not_or, not_lt, not_le] at hnd
    obtain ⟨hle, hlt⟩ := hnd
    have hsK : c.1 + c.2 ≤ K := by
      by_contra h; rw [not_le] at h
      have hp : (2 : ℕ) ^ (K + 1) ≤ 2 ^ (c.1 + c.2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hpow : (2 : ℕ) ^ (c.1 + c.2 + 3) = 2 * 2 ^ (c.1 + c.2 + 2) := by
      rw [pow_add, pow_add]; ring
    have h2 : x ≤ 2 * (x / 2) + 1 := by omega
    have hxlt2 : x < 2 ^ (c.1 + c.2 + 3) := by omega
    have hKs : K ≤ c.1 + c.2 + 2 := by
      by_contra h; rw [not_le] at h
      have hp : (2 : ℕ) ^ (c.1 + c.2 + 3) ≤ 2 ^ K :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Finset.mem_filter.mpr ⟨hcR, hsK, hKs⟩
  calc (R.filter (fun c => ¬ windowDisjoint x c.1 c.2)).card
      ≤ (R.filter (fun c => c.1 + c.2 ≤ K ∧ K ≤ c.1 + c.2 + 2)).card :=
        Finset.card_le_card hBS
    _ ≤ (Finset.Icc (K - 2) K ×ˢ Finset.range (K + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun c => (c.1 + c.2, c.1)) ?_ ?_
        · intro c hc
          rw [Finset.mem_coe, hR, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
            Finset.mem_range] at hc
          obtain ⟨⟨hc1, _hc2⟩, hub, hlb⟩ := hc
          simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
          exact ⟨⟨by omega, by omega⟩, by omega⟩
        · intro a _ha b _hb hab
          simp only [Prod.mk.injEq] at hab
          obtain ⟨hsum, hfst⟩ := hab
          exact Prod.ext hfst (by omega)
    _ = (Finset.Icc (K - 2) K).card * (K + 1) := by
        rw [Finset.card_product, Finset.card_range]
    _ = (K + 1 - (K - 2)) * (K + 1) := by rw [Nat.card_Icc]
    _ ≤ 3 * (K + 1) := Nat.mul_le_mul (by omega) (le_refl _)

/-! ## Part C — the closure: `hHD` from a uniform per-box price -/

/-- **`hHD` from a uniform per-box price (FULL).**  If every surviving box is priced by a single
uniform bound `P ≥ 0` (`hPrice` — the SW3c per-box input, from `box_price_of_apDiscBilin` +
`general_BV_alpha_discharged`), and the numeric threshold `3(K+1)·P ≤ RHD` holds (`hclose`),
then the switched honest-discrepancy sum meets `RHD`.  Discharges `hHD_of_generalBV_inputs`'
`hSum` slot using the proven `O(log x)` box count `card_relevantBoxes_le`.

This is the exact `hHD` slot shape `hBVswitch_of_generalBV` consumes (`bound := Q·Dlev`), now
reduced to a SINGLE uniform per-box price plus a clean numeric threshold. -/
theorem hHD_of_uniform_price (x z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (hx : 1 ≤ x) {bound P RHD : ℝ} (hP : 0 ≤ P)
    (hPrice : ∀ c ∈ (Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.log 2 x + 1)).filter
                (fun c => ¬ windowDisjoint x c.1 c.2),
        (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then |boxHonestDisc x z y d c.1 c.2| else 0) ≤ P)
    (hclose : (3 * (Nat.log 2 x + 1) : ℝ) * P ≤ RHD) :
    (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then |switchHonestDisc x z y d| else 0) ≤ RHD := by
  refine hHD_of_generalBV_inputs x z y Ps hPs hPodd bound (fun _ => P) hPrice ?_
  have hcard := card_relevantBoxes_le (x := x) hx
  set B := (Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.log 2 x + 1)).filter
      (fun c => ¬ windowDisjoint x c.1 c.2) with hBdef
  simp only [Finset.sum_const, nsmul_eq_mul]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hP) hclose
  calc (B.card : ℝ) ≤ ((3 * (Nat.log 2 x + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (3 * (Nat.log 2 x + 1) : ℝ) := by push_cast; ring

/-! ## Part D — the per-box pricing reduction to `apDiscBilin` -/

open Classical in
/-- **The box-restricted semiprime-block indicator** — `boxAlpha z y i m = [2^i ≤ m]·α(m)`, the
`m`-side coefficient of the box `(i, ·)`: `semiprimeBlockInd z y` truncated below by the box's
lower dyadic edge `2^i` (the upper edge `< 2^{i+1}` is enforced by `apDiscBilin`'s `X = 2^{i+1}`
range).  Feeds `apDiscBilin`/`general_BV_final'` on the `m`-side. -/
noncomputable def boxAlpha (z y i m : ℕ) : ℂ :=
  if 2 ^ i ≤ m then semiprimeBlockInd z y m else 0

/-- `‖boxAlpha‖ ≤ 1` (the `general_BV_final'` `m`-side hypothesis shape). -/
theorem norm_boxAlpha_le_one (z y i m : ℕ) : ‖boxAlpha z y i m‖ ≤ 1 := by
  unfold boxAlpha
  split_ifs with h
  · exact norm_semiprimeBlockInd_le_one z y m
  · simp

/-- **The per-box pricing reduction (FULL modulo the two NAMED residuals).**  The summed honest
discrepancy of one surviving box `(i,j)` is bounded by its bilinear AP-discrepancy price
`∑_d ‖apDiscBilin (boxAlpha z y i) (blockPrimeInd 2^j) 2^{i+1} 2^{j+1} 2 d‖` (`hMain`, supplied
by `general_BV_alpha_discharged` at residue `R₀ = 2`, `Coprime 2 d` FREE via
`switch_dvd_coprime_two`) plus the correction sum (`hCorrSum`).

The two NAMED analytic residuals — the SW3c core, flagged precisely (module numeric plan):
* `hIdent` — the per-`d` identification `|boxHonestDisc d (i,j)| ≤ ‖apDiscBilin …‖ + boxCorr d`:
  removing the product-window edge (the hyperbola sub-split — `apDiscBilin` measures a rectangle,
  the windowed count is a difference of two hyperbola-truncated counts) into the apDiscBilin
  price plus the crossing-strip / diagonal correction `boxCorr`;
* `boxCorr` (with `hCorrSum`) — the `p₂ ≤ p₃` same-block diagonal + crossing-strip contribution,
  crude-bounded and summed with the `1/φd` savings.

Given these, the reduction composes by the triangle inequality + `Finset.sum_add_distrib`. -/
theorem box_price_of_apDiscBilin (x z y Ps : ℕ) (i j : ℕ) {bound Pmain Pcorr : ℝ}
    (boxCorr : ℕ → ℝ)
    (hIdent : ∀ d ∈ Nat.divisors Ps, (d : ℝ) < bound →
        |boxHonestDisc x z y d i j|
          ≤ ‖apDiscBilin (boxAlpha z y i) (blockPrimeInd (2 ^ j))
                (2 ^ (i + 1)) (2 ^ (j + 1)) 2 d‖ + boxCorr d)
    (hMain : (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then
        ‖apDiscBilin (boxAlpha z y i) (blockPrimeInd (2 ^ j))
            (2 ^ (i + 1)) (2 ^ (j + 1)) 2 d‖ else 0) ≤ Pmain)
    (hCorrSum : (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then boxCorr d else 0) ≤ Pcorr) :
    (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then |boxHonestDisc x z y d i j| else 0)
      ≤ Pmain + Pcorr := by
  classical
  calc (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then |boxHonestDisc x z y d i j| else 0)
      ≤ ∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then
          (‖apDiscBilin (boxAlpha z y i) (blockPrimeInd (2 ^ j))
              (2 ^ (i + 1)) (2 ^ (j + 1)) 2 d‖ + boxCorr d) else 0 := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        by_cases hc : (d : ℝ) < bound
        · rw [if_pos hc, if_pos hc]; exact hIdent d hd hc
        · rw [if_neg hc, if_neg hc]
    _ = (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then
            ‖apDiscBilin (boxAlpha z y i) (blockPrimeInd (2 ^ j))
                (2 ^ (i + 1)) (2 ^ (j + 1)) 2 d‖ else 0)
          + (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then boxCorr d else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        split_ifs <;> ring
    _ ≤ Pmain + Pcorr := add_le_add hMain hCorrSum

end Salt.Chen
