/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SwitchPricing

/-!
# SW3d — the hyperbola sub-split backbone + the decided/crossing classification

Design: `docs/blueprints/flags.md`, entries "2026-07-13 SW3c" (the two NAMED residual slots
`hIdent`, `boxCorr`/`hCorrSum` of `box_price_of_apDiscBilin`), "2026-07-13 SW3b … CATCH #48"
(the factor-4-box-vs-factor-2-window mismatch and the `p₂ ≤ p₃` diagonal), and "2026-07-13 SW3".

This file lands the *provable algebraic + geometric backbone* of the honest hyperbola sub-split —
the machinery the window-edge removal needs regardless of the final interface — and records, in
the flag `2026-07-13 SW3d`, the two genuine obstructions to discharging the SW3c slots as they are
currently coded (surfaced by working the arithmetic honestly, per the C+ "stop-and-flag"
discipline).

## Numeric plan (recorded FIRST, per the C+ discipline) — worked HONESTLY

Box `(i,j)`: triples with `m = p₁p₂ ∈ [2^i, 2^{i+1})`, `p = p₃ ∈ [2^j, 2^{j+1})`, product in the
window `W = [x/2+2, x]`.  On a *surviving* box `i+j ∈ {K−2,K−1,K}` (`K = ⌊log₂ x⌋`,
`card_relevantBoxes_le`), the product range `[2^{i+j}, 2^{i+j+2})` spans a factor `4`, STRICTLY
WIDER than the factor-`2` window — so the window boundary `m·p = x` (and `m·p = x/2+2`) cuts
through the box interior (e.g. `i+j = K−1`: range `[2^{K−1}, 2^{K+1}) ⊇ (x/2, 2x)`).

**`apDiscBilin` measures the full rectangle `[2^i,2^{i+1})×[2^j,2^{j+1})` with NO window.**  Write
`D := apDiscBilin(boxAlpha,…) − boxHonestDisc` = the honest discrepancy over the *outside-window*
part of the rectangle.  For a middle-cutting box the outside-window part is a constant fraction of
the rectangle, `≈ 2^i·2^j ≈ x` triples; crudely `|D| ≤ (outside count) ≈ x`, and summed over the
`~D` divisors `∑_{d<bound}|D(d)| ≈ D·x` — astronomically over the `x/(log x)^{10}` budget.  So the
single-`apDiscBilin`-`+`-`boxCorr` shape of `hIdent` (SwitchPricing's `box_price_of_apDiscBilin`)
is UNDER-POWERED for the middle-cutting boxes; `boxCorr` cannot be budget-small (finding SW3d-i).

**The honest window removal is a SUM of sub-box `apDiscBilin` terms, not one.**  Split the box's
`m`-range dyadically; each sub-block `[a,b)` paired with the `p`-block is either wholly IN the
window (`productInWindow_of_corners`: corner test `x/2+2 ≤ a·2^j`, `(b−1)·(2^{j+1}−1) ≤ x`) — then
its windowed count = its window-free count = its own `apDiscBilin` (`boxAlpha` restricted to
`[a,b)`, `‖·‖ ≤ 1`); wholly OUT (`productBelowWindow_of`/`productAboveWindow_of`) — then it is
window-empty and contributes `0`; or CROSSING.  `apDiscBilin` is ADDITIVE in `α`
(`apDiscBilin_sum_alpha`), so the decided-in sub-boxes' `apDiscBilin` terms sum coherently — but
they are a PROPER subset of the sub-boxes, so their sum is NOT the full-box `apDiscBilin`
(the OUT sub-boxes carry large window-free `apDiscBilin`s that must be dropped).  The correct
interface is therefore `|boxHonestDisc| ≤ ∑_{decided-in s} ‖apDiscBilin(α_s)‖ + (strip)`, a
`Finset.sum` over sub-boxes — a DIFFERENT slot shape than SW3c's `box_price_of_apDiscBilin`.

**The crossing strip is genuinely 2-D and needs its own mini-BV (finding SW3d-ii).**  Working the
count honestly: the window boundary `m·p = x` sweeps `m = x/p` over `p ∈ [2^j,2^{j+1})`, i.e. over
an `m`-interval of length `≈ x/2^{j+1} ≈ 2^{i−1}` — HALF the `m`-block.  Splitting `m` ALONE to
level `ℓ` (sub-block width `2^{i−ℓ}`) leaves `≈ 2^{ℓ−1}` crossing sub-blocks (the boundary passes
through a growing number of them) — the crossing sub-block COUNT grows as `2^ℓ`, it does NOT
geometrically decay.  What decays is the crossing AREA: splitting BOTH `m` and `p` to level `ℓ`,
the curve meets `≈ 2^ℓ` cells each of area `2^{i+j}/4^ℓ`, total crossing area `≈ 2^{i+j}/2^ℓ`
(the correct geometric decay).  At the finest level the residual strip carries `≈ 2^{max(i,j)}`
triples; for balanced boxes `≈ √x` (budget-OK after the `1/φd` savings), for the top-`j` boxes
`≈ x` — but there `2^i = O(1)` so the crude `abs_boxHonestDisc_le_boxCount` clears it.  Crucially
the strip is a prime-AP discrepancy over a diagonal band, priced only by an `apDiscBilin`-type
(mini-BV) estimate — NOT by an `O(log x)`-count of singleton-`α` terms as the SW3c flag's tentative
resolution hoped (a fixed `m`'s `δ_m`-`apDiscBilin` prices ALL `p` in the block, over-counting; and
the distinct straddling `m` across the block are `≫ log x`).  The strip pricing is the same
2-D-sub-split-plus-`general_BV` construction, recursed.

**Prerequisite gap (finding SW3d-iii).**  EVERY "= `apDiscBilin`" step above needs the
`tripleSet ↔ (m,n)`-pair bijection `(p₁,p₂,p₃) ↦ (p₁p₂, p₃)` (the `semiprimeBlockInd`
multiplicity), turning a `boxResCount`/`boxUnitCount` (a `tripleSet` filter) into the double sum
`apDiscBilin` measures.  This bridge is NOT in the corpus — it is a prerequisite for connecting
ANY of this file's `apDiscBilin` machinery to `boxHonestDisc`.

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

The algebraic + geometric backbone of the sub-split, all FULL:

* **`apDiscBilin_zero` / `apDiscBilin_congr` / `apDiscBilin_add_left` / `apDiscBilin_sum_alpha`** —
  `apDiscBilin` depends only on `α|[1,X]` and is ADDITIVE in `α`: a finite `α`-partition splits
  `apDiscBilin` into the sub-coefficient terms.  **This is the backbone — it is what makes the
  decided sub-boxes' `apDiscBilin` terms sum coherently.**
* **`restrictAlpha` + `norm_restrictAlpha_le`/`_le_one`, `apDiscBilin_split_threshold`** — the
  sub-block coefficient (`boxAlpha` truncated to `[a,b)`, `‖·‖ ≤ 1`) and the threshold split of
  `apDiscBilin`; iterating gives the dyadic sub-partition.
* **`apDiscBilin_singleton_collapse`** — a width-`1` sub-block's `apDiscBilin` collapses to a
  single-`m₀` prime-AP discrepancy over the `p`-block (the strip's `δ_m`-`α` shape identified).
* **`ProductInWindow`, `productInWindow_of_corners`, `productBelowWindow_of`,
  `productAboveWindow_of`** — the decided/crossing classification via corner tests: a sub-rectangle
  is wholly in / below / above the window from its four corner products.  **The geometric core of
  the decided-sub-box vanishing (out) and window-redundancy (in).**

## What remains NAMED (flag `2026-07-13 SW3d`)

The honest window removal needs a Fable-tier interface revision of `box_price_of_apDiscBilin`
(single-`apDiscBilin` → `Finset.sum` of sub-box `apDiscBilin`s) PLUS the `tripleSet ↔ (m,n)`
bijection bridge PLUS the 2-D strip mini-BV.  Findings SW3d-i/ii/iii are recorded precisely so the
downstream assembly does not grind on the under-powered slot.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — `apDiscBilin` is additive in `α` (the sub-split backbone) -/

/-- **`apDiscBilin` at the zero coefficient vanishes (FULL).** -/
theorem apDiscBilin_zero (β : ℕ → ℂ) (X Y N₀ d : ℕ) :
    apDiscBilin (fun _ => 0) β X Y N₀ d = 0 := by
  simp [apDiscBilin]

/-- **`apDiscBilin` depends only on `α|[1,X]` (FULL).**  Two coefficients agreeing on the
summation range `Icc 1 X` give the same bilinear discrepancy. -/
theorem apDiscBilin_congr {α α' β : ℕ → ℂ} {X Y N₀ d : ℕ}
    (h : ∀ m ∈ Finset.Icc 1 X, α m = α' m) :
    apDiscBilin α β X Y N₀ d = apDiscBilin α' β X Y N₀ d := by
  classical
  simp only [apDiscBilin]
  have hsum : ∀ (P : ℕ → ℕ → Prop) [∀ a b, Decidable (P a b)],
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, (if P m n then α m * β n else 0))
        = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, (if P m n then α' m * β n else 0)) := by
    intro P _
    refine Finset.sum_congr rfl (fun m hm => ?_)
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [h m hm]
  rw [hsum (fun m n => ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d)),
    hsum (fun m n => IsUnit ((m * n : ℕ) : ZMod d))]

/-- **`apDiscBilin` is additive in `α` (FULL).**  `apDiscBilin (α₁+α₂) = apDiscBilin α₁ +
apDiscBilin α₂`: both the residue count and the unit main term are `∑ₘ αₘ·(…)`, linear in `α`. -/
theorem apDiscBilin_add_left (α₁ α₂ β : ℕ → ℂ) (X Y N₀ d : ℕ) :
    apDiscBilin (fun m => α₁ m + α₂ m) β X Y N₀ d
      = apDiscBilin α₁ β X Y N₀ d + apDiscBilin α₂ β X Y N₀ d := by
  classical
  simp only [apDiscBilin]
  have hsum : ∀ (P : ℕ → ℕ → Prop) [∀ a b, Decidable (P a b)],
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, (if P m n then (α₁ m + α₂ m) * β n else 0))
        = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, (if P m n then α₁ m * β n else 0))
          + (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, (if P m n then α₂ m * β n else 0)) := by
    intro P _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    split_ifs <;> ring
  rw [hsum (fun m n => ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d)),
    hsum (fun m n => IsUnit ((m * n : ℕ) : ZMod d))]
  ring

/-- **`apDiscBilin` splits over a finite `α`-partition (FULL).**  If `α = ∑_{ℓ∈s} α ℓ` pointwise
then `apDiscBilin α = ∑_{ℓ∈s} apDiscBilin (α ℓ)`.  This is the backbone: a dyadic sub-partition of
the box's `m`-block turns the box `apDiscBilin` into a coherent sum of sub-box `apDiscBilin`s. -/
theorem apDiscBilin_sum_alpha (β : ℕ → ℂ) (X Y N₀ d : ℕ) {ι : Type*} (s : Finset ι)
    (α : ι → ℕ → ℂ) :
    apDiscBilin (fun m => ∑ ℓ ∈ s, α ℓ m) β X Y N₀ d
      = ∑ ℓ ∈ s, apDiscBilin (α ℓ) β X Y N₀ d := by
  classical
  induction s using Finset.induction with
  | empty => simp [apDiscBilin_zero]
  | @insert a s ha ih =>
    have hfun : (fun m => ∑ ℓ ∈ insert a s, α ℓ m) = (fun m => α a m + ∑ ℓ ∈ s, α ℓ m) := by
      funext m; rw [Finset.sum_insert ha]
    rw [hfun, apDiscBilin_add_left, ih, Finset.sum_insert ha]

/-! ## Part B — the sub-block coefficient `restrictAlpha` and the threshold split -/

/-- **The sub-block coefficient** — `α` truncated to the `m`-window `[a, b)`.  Applied to
`boxAlpha z y i` it is the box's `m`-side coefficient restricted to a dyadic sub-block; it feeds
`apDiscBilin`/`general_BV_final'` with `‖·‖ ≤ 1` intact. -/
noncomputable def restrictAlpha (α : ℕ → ℂ) (a b : ℕ) : ℕ → ℂ :=
  fun m => if a ≤ m ∧ m < b then α m else 0

/-- `‖restrictAlpha α a b m‖ ≤ ‖α m‖`. -/
theorem norm_restrictAlpha_le (α : ℕ → ℂ) (a b m : ℕ) :
    ‖restrictAlpha α a b m‖ ≤ ‖α m‖ := by
  unfold restrictAlpha
  split_ifs with h
  · exact le_refl _
  · rw [norm_zero]; exact norm_nonneg _

/-- `‖α‖ ≤ 1 ⟹ ‖restrictAlpha α a b‖ ≤ 1` (the `general_BV_final'` `m`-side hypothesis shape,
preserved under sub-blocking). -/
theorem norm_restrictAlpha_le_one {α : ℕ → ℂ} (h : ∀ m, ‖α m‖ ≤ 1) (a b m : ℕ) :
    ‖restrictAlpha α a b m‖ ≤ 1 :=
  le_trans (norm_restrictAlpha_le α a b m) (h m)

/-- **The threshold split of `apDiscBilin` (FULL).**  Splitting the `m`-block at `t` splits
`apDiscBilin` into the two sub-block terms `[1,t)` and `[t, X+1)`.  From `apDiscBilin_add_left` +
`apDiscBilin_congr` (the two restrictions sum to `α` on `Icc 1 X`).  Iterating gives the dyadic
sub-partition of the box. -/
theorem apDiscBilin_split_threshold (α β : ℕ → ℂ) (X Y N₀ d t : ℕ) :
    apDiscBilin α β X Y N₀ d
      = apDiscBilin (restrictAlpha α 1 t) β X Y N₀ d
        + apDiscBilin (restrictAlpha α t (X + 1)) β X Y N₀ d := by
  rw [← apDiscBilin_add_left]
  refine apDiscBilin_congr (fun m hm => ?_)
  rw [Finset.mem_Icc] at hm
  unfold restrictAlpha
  by_cases hmt : m < t
  · rw [if_pos ⟨hm.1, hmt⟩, if_neg (by omega), add_zero]
  · rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, zero_add]

/-! ## Part C — the singleton (width-`1`) sub-block: the strip's `δ_m`-`α` shape -/

open Classical in
/-- **The width-`1` sub-block collapse (FULL).**  `restrictAlpha α m₀ (m₀+1)` is the singleton
`δ_{m₀}`-coefficient; its `apDiscBilin` collapses the outer `m`-sum to `m₀`, leaving a single-`m₀`
prime-AP discrepancy over the `p`-block `Icc 1 Y`.  This is the shape of the finest-level crossing
strip: a prime-AP discrepancy in `p` at the pinned `m₀` (priced by the mini-BV, per the flag). -/
theorem apDiscBilin_singleton_collapse (α β : ℕ → ℂ) (X Y N₀ d m₀ : ℕ)
    (hm₀ : m₀ ∈ Finset.Icc 1 X) :
    apDiscBilin (restrictAlpha α m₀ (m₀ + 1)) β X Y N₀ d
      = (∑ n ∈ Finset.Icc 1 Y,
            if ((m₀ * n : ℕ) : ZMod d) = (N₀ : ZMod d) then α m₀ * β n else 0)
        - (1 / (d.totient : ℂ)) *
            (∑ n ∈ Finset.Icc 1 Y, if IsUnit ((m₀ * n : ℕ) : ZMod d) then α m₀ * β n else 0) := by
  classical
  simp only [apDiscBilin]
  have hcollapse : ∀ (P : ℕ → ℕ → Prop) [∀ a b, Decidable (P a b)],
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
          (if P m n then restrictAlpha α m₀ (m₀ + 1) m * β n else 0))
        = (∑ n ∈ Finset.Icc 1 Y, if P m₀ n then α m₀ * β n else 0) := by
    intro P _
    rw [Finset.sum_eq_single_of_mem m₀ hm₀]
    · refine Finset.sum_congr rfl (fun n _ => ?_)
      have : restrictAlpha α m₀ (m₀ + 1) m₀ = α m₀ := by
        unfold restrictAlpha; rw [if_pos ⟨le_refl _, Nat.lt_succ_self _⟩]
      rw [this]
    · intro m _ hmne
      have hz : restrictAlpha α m₀ (m₀ + 1) m = 0 := by
        unfold restrictAlpha; rw [if_neg]; rintro ⟨h1, h2⟩; omega
      simp [hz]
  rw [hcollapse (fun m n => ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d)),
    hcollapse (fun m n => IsUnit ((m * n : ℕ) : ZMod d))]

/-! ## Part D — the decided/crossing classification via corner products -/

/-- **The product-window membership** for a `(m, n)` cell: `x/2+2 ≤ m·n ≤ x` (the `tripleSet`
window on `prod3`). -/
def ProductInWindow (x m n : ℕ) : Prop := x / 2 + 2 ≤ m * n ∧ m * n ≤ x

instance (x m n : ℕ) : Decidable (ProductInWindow x m n) := by
  unfold ProductInWindow; infer_instance

/-- **Decided-IN by corners (FULL).**  A cell `(m, n)` with `a ≤ m ≤ b`, `c ≤ n ≤ e` lies wholly
in the window as soon as the two extreme corners do: `x/2+2 ≤ a·c` and `b·e ≤ x`.  For a dyadic
sub-block `[a, b) × [c, e)` (so `m ≤ b−1`, `n ≤ e−1`) this makes the `tripleSet` window redundant:
the windowed count equals the window-free (rectangle) count, the `apDiscBilin` target. -/
theorem productInWindow_of_corners {x a b c e m n : ℕ}
    (hlo : x / 2 + 2 ≤ a * c) (hhi : b * e ≤ x)
    (hma : a ≤ m) (hmb : m ≤ b) (hnc : c ≤ n) (hne : n ≤ e) :
    ProductInWindow x m n := by
  refine ⟨le_trans hlo (Nat.mul_le_mul hma hnc), le_trans (Nat.mul_le_mul hmb hne) hhi⟩

/-- **Decided-OUT below (FULL).**  If the top corner is already below the window floor
(`b·e < x/2+2`) the whole cell is below: `m·n < x/2+2`.  Such a sub-block is window-empty (it
contributes `0` to `boxHonestDisc`). -/
theorem productBelowWindow_of {x b e m n : ℕ} (hhi : b * e < x / 2 + 2)
    (hmb : m ≤ b) (hne : n ≤ e) : m * n < x / 2 + 2 :=
  lt_of_le_of_lt (Nat.mul_le_mul hmb hne) hhi

/-- **Decided-OUT above (FULL).**  If the bottom corner already exceeds `x` (`x < a·c`) the whole
cell is above: `x < m·n`.  Such a sub-block is window-empty. -/
theorem productAboveWindow_of {x a c m n : ℕ} (hlo : x < a * c)
    (hma : a ≤ m) (hnc : c ≤ n) : x < m * n :=
  lt_of_lt_of_le hlo (Nat.mul_le_mul hma hnc)

/-- **The decided-OUT cells carry no `ProductInWindow` (FULL).**  Packaging the two OUT tests:
a below-cell or an above-cell is not in the window. -/
theorem not_productInWindow_of_below {x m n : ℕ} (h : m * n < x / 2 + 2) :
    ¬ ProductInWindow x m n := by
  rintro ⟨hlo, _⟩; omega

theorem not_productInWindow_of_above {x m n : ℕ} (h : x < m * n) :
    ¬ ProductInWindow x m n := by
  rintro ⟨_, hhi⟩; omega

end Salt.Chen
