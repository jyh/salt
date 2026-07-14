/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.WindowClose

/-!
# WBV6 — the piece decomposition + the low-piece band

Design: `docs/blueprints/flags.md`, the `2026-07-14 WBV3`/`WBV4` entries and the WBV close's
section header in `Salt/Chen/WindowClose.lean` (the `hLowPieces` residual paragraph).  This file
is the WBV wave's last combinatorial layer: it decomposes the full-block honest discrepancy
`BlockPricing.blockHonestDisc` over the dyadic `p₃`-pieces (item 1), packages the `O(log x)`
piece count (item 2), assesses the low-piece ordering band (item 3), and assembles the pieces
into `BlockPricing.hHDblocks_of_perBlock`'s `hBlock` slot (item 4).

## Item 1 — the piece decomposition

Each admissible triple `t = (p₁, p₂, p₃)` is fibred by `k = ⌊log₂ p₃⌋` (the single dyadic index
on the `p₃`-side; the `m = p₁p₂`-side is NOT sub-divided — its range is the full `[0, x+1)`).
Every triple has `p₃ ≤ prod3 ≤ x`, so `k ∈ [0, ⌊log₂ x⌋]`, giving `Nat.log 2 x + 1` pieces.  Each
piece `k` is exactly `PairBijection.blockBoxResCount`/`blockBoxUnitCount` at
`(N, M) = (2^k − 1, 2^{k+1} − 1)` and the vacuous `m`-range `(a, b) = (0, x+1)` — matching the
`(block-m-range) × (dyadic p-piece)` box that `WindowSW.blockBox_windowDisc_eq` prices (its
`(a, b)` is the `m`-window, here full).  Mirrors `SwitchDyadic.count_eq_sum_box` at one dyadic
index.  `blockHonestDisc_eq_sum_pieces` (exact) + `abs_blockHonestDisc_le_sum_pieces` (triangle).

## Item 2 — the piece count

`card_pieces : (Finset.range (Nat.log 2 x + 1)).card = Nat.log 2 x + 1 = O(log x)`.  Empty pieces
(no prime `p₃` in the dyadic band, or the whole band above `x`) contribute `0` automatically.

## ★ Item 3 — the low-piece ordering band: NUMERIC ASSESSMENT (recorded FIRST) ★

Each piece box `(0, x+1)` splits at the ordering threshold `c = z·N + 1 = z·(2^k−1)+1`
(`blockBoxHonestDisc_split_m`):

* the **ordering-clear** sub-box `[0, c)` has every `m < c ⟹ p₂ = m/p₁ ≤ m/z ≤ N < 2^k ≤ p₃`, so
  `hord : b ≤ z·N+1` holds and `WindowClose.hHD_of_generalBV_window` prices it (the high-piece
  price, named `Phi` in item 4);
* the **band** sub-box `[c, x+1)` has `m ≥ c ⟹ p₂ > N`, i.e. `p₂, p₃` in the **same** dyadic band
  `(2^k, 2^{k+1})` (`p₂ ≤ p₃` from `tripleSet`).  These are the residual triples the corner-free
  identification cannot reach.

**The crude count does NOT clear the budget (assessed, flagged — honest correction to the design
note "crude thin-band count or a dedicated node").**  Write the band mass
`Σ_k #{band triples in piece k}`.  With `p₂, p₃ ∈ (2^k, 2^{k+1})` both prime and `p₁ ∈ [z, y]`,
`prod ∈ (x/2, x]`:

  `#band_k ≤ (π(2^{k+1}) − π(2^k))² · (x/(2·2^{2k}) + 1) ≈ (C·2^k/k)² · x/2^{2k} = C²·x/(2k²)`,

and `p₂ > y = x^{1/3}` forces `k ≥ k₀ ≈ (1/3)log₂ x`, so
`Σ_k #band_k ≤ (C²x/2)·Σ_{k≥k₀} 1/k² ≈ (C²x/2)/k₀ = Θ(x/log x)`.  Now the honest disc is bounded
crudely by the box count (`abs_blockBoxHonestDisc_le_blockBoxCount`:
`|blockBoxHonestDisc| ≤ blockBoxCount`, since `resCount, ν·unitCount ∈ [0, count]`), and summing
over `d < bound` (`bound = Q·Dlev ~ x^{1/2}`):

  * the `ν·unitCount` part sums to `#band · Σ_{d<bound, d∣Ps} 1/φ(d) ~ (x/log x)·(C·log x) = Θ(x)`;
  * the `resCount` part sums to `Σ_{band t} #{d<bound : d∣(prod−2)} ~ #band · x^{o(1)}`, worse.

Both **overshoot** `x/(log x)^{10}` (the first by `(log x)^{10}`, since `Θ(x) ≫ x/(log x)^{10}`;
`x^{o(1)}` beats every `(log x)^c`).  The band is `Θ(box)`-thick, NOT `1/(log x)^{10}`-thin: it
carries a genuine positive-density chunk of the discrepancy and needs the SAME BV/equidistribution
cancellation as the main term — a **crude count cannot close it**.  So the low-piece band stays a
**NAMED** hypothesis (`hLow` of `hBlock_of_window_prices`, item 4), to be discharged downstream by
a dedicated BV/SW node (its own apDiscBilin identification handling the `p₂ ≈ p₃` ordering), not
here.  See the closing flag `docs/blueprints/flags.md`, "2026-07-14 WBV6".

## Item 4 — the composed `hBlock`

`hBlock_of_window_prices` — items 1–3 assembled: `Σ_{d<bound} |blockHonestDisc j d|` bounded by
`(Σ_k high-piece price Phi k) + (named low-piece band Plo)`, the EXACT `hBlock` slot shape of
`BlockPricing.hHDblocks_of_perBlock` (whose composition feeds
`BlockPricing.hBVblocks_of_generalBV`).  `#check` block at the end confirms the chain elaborates.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the dyadic `p₃`-piece endpoints -/

/-- Lower endpoint `N` of the dyadic `p₃`-piece `k`: `N < p₃ ⟺ 2^k ≤ p₃`. -/
def pieceN (k : ℕ) : ℕ := 2 ^ k - 1

/-- Upper endpoint `M` of the dyadic `p₃`-piece `k`: `p₃ ≤ M ⟺ p₃ < 2^{k+1}`. -/
def pieceM (k : ℕ) : ℕ := 2 ^ (k + 1) - 1

/-- **`⌊log₂ p⌋ = k ⟺ p` in the dyadic piece `(pieceN k, pieceM k]`** (for `p ≥ 1`).  The dyadic
band `2^k ≤ p < 2^{k+1}` written as the half-open interval `(2^k − 1, 2^{k+1} − 1]`. -/
theorem log_eq_iff_piece {p k : ℕ} (hp : 1 ≤ p) :
    Nat.log 2 p = k ↔ pieceN k < p ∧ p ≤ pieceM k := by
  unfold pieceN pieceM
  have hp0 : p ≠ 0 := by omega
  have h2k : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
  have h2k1 : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by norm_num)
  constructor
  · intro hlog
    have hle : 2 ^ k ≤ p := by have := Nat.pow_log_le_self 2 hp0; rwa [hlog] at this
    have hlt : p < 2 ^ (k + 1) := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p; rwa [hlog] at this
    omega
  · rintro ⟨hlo, hhi⟩
    have hle : 2 ^ k ≤ p := by omega
    have hlt : p < 2 ^ (k + 1) := by omega
    exact Nat.log_eq_of_pow_le_of_lt_pow hle hlt

/-! ## Part B — the piece-partition kernel and the count decompositions (item 1) -/

/-- **The `p₃`-piece partition kernel (FULL).**  Any predicate-filtered count of `tripleSet`
partitions exactly over the `Nat.log 2 x + 1` dyadic `p₃`-pieces `k = ⌊log₂ p₃⌋`.  Every admissible
triple has `p₃ ≤ prod3 ≤ x`, so `⌊log₂ p₃⌋ ≤ ⌊log₂ x⌋`; `Finset.card_eq_sum_card_fiberwise` over
`t ↦ ⌊log₂ p₃⌋` does the rest.  The single-index analogue of `SwitchDyadic.count_eq_sum_box`. -/
private lemma count_eq_sum_piece {x z y : ℕ} (P : ℕ × ℕ × ℕ → Prop) [DecidablePred P] :
    (((tripleSet x z y).filter P).card : ℝ)
      = ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          (((tripleSet x z y).filter (fun t => Nat.log 2 t.2.2 = k ∧ P t)).card : ℝ) := by
  classical
  have hmaps : ∀ t ∈ (tripleSet x z y).filter P,
      Nat.log 2 t.2.2 ∈ Finset.range (Nat.log 2 x + 1) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have htri := ht.1
    rw [tripleSet, Finset.mem_filter] at htri
    obtain ⟨_, _, _, _, _, hp1, hp2, hp3, _hlo, hhi⟩ := htri
    have hmpos : 0 < t.1 * t.2.1 := Nat.mul_pos hp1.pos hp2.pos
    have hprod : prod3 t = t.1 * t.2.1 * t.2.2 := rfl
    have hple : t.2.2 ≤ x := by
      calc t.2.2 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_left _ hmpos
        _ = prod3 t := hprod.symm
        _ ≤ x := hhi
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right hple)
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hfilt : ((tripleSet x z y).filter P).filter (fun t => Nat.log 2 t.2.2 = k)
      = (tripleSet x z y).filter (fun t => Nat.log 2 t.2.2 = k ∧ P t) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro t _; exact and_comm
  rw [hfilt]

/-- **The block residue count partitions over the `p₃`-pieces (FULL — item 1).** -/
theorem blockResCount_eq_sum_pieces (x z y : ℕ) (ε₀ : ℝ) (j d : ℕ) :
    blockResCount x z y ε₀ j d
      = ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          blockBoxResCount x z y ε₀ j (pieceN k) (pieceM k) 0 (x + 1) d := by
  classical
  unfold blockResCount
  rw [count_eq_sum_piece
        (fun t => blockIdx z ε₀ t.1 = j ∧ ((prod3 t : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold blockBoxResCount
  rw [Nat.cast_inj]
  refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
  rw [tripleSet, Finset.mem_filter] at ht
  obtain ⟨_, _, _, _, _, hp1, hp2, hp3, _, hwhi⟩ := ht
  have hp3pos : 1 ≤ t.2.2 := hp3.pos
  have hmle : t.1 * t.2.1 ≤ x := by
    have hprod : prod3 t = t.1 * t.2.1 * t.2.2 := rfl
    calc t.1 * t.2.1 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_right _ hp3.pos
      _ = prod3 t := hprod.symm
      _ ≤ x := hwhi
  rw [log_eq_iff_piece hp3pos]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hblk, hres⟩
    exact ⟨hblk, hres, hlo, hhi, Nat.zero_le _, by omega⟩
  · rintro ⟨hblk, hres, hlo, hhi, _, _⟩
    exact ⟨⟨hlo, hhi⟩, hblk, hres⟩

/-- **The block unit count partitions over the `p₃`-pieces (FULL — item 1).** -/
theorem blockUnitCount_eq_sum_pieces (x z y : ℕ) (ε₀ : ℝ) (j d : ℕ) :
    blockUnitCount x z y ε₀ j d
      = ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          blockBoxUnitCount x z y ε₀ j (pieceN k) (pieceM k) 0 (x + 1) d := by
  classical
  unfold blockUnitCount
  rw [count_eq_sum_piece (fun t => blockIdx z ε₀ t.1 = j ∧ IsUnit ((prod3 t : ℕ) : ZMod d))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold blockBoxUnitCount
  rw [Nat.cast_inj]
  refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
  rw [tripleSet, Finset.mem_filter] at ht
  obtain ⟨_, _, _, _, _, hp1, hp2, hp3, _, hwhi⟩ := ht
  have hp3pos : 1 ≤ t.2.2 := hp3.pos
  have hmle : t.1 * t.2.1 ≤ x := by
    have hprod : prod3 t = t.1 * t.2.1 * t.2.2 := rfl
    calc t.1 * t.2.1 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_right _ hp3.pos
      _ = prod3 t := hprod.symm
      _ ≤ x := hwhi
  rw [log_eq_iff_piece hp3pos]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hblk, hres⟩
    exact ⟨hblk, hres, hlo, hhi, Nat.zero_le _, by omega⟩
  · rintro ⟨hblk, hres, hlo, hhi, _, _⟩
    exact ⟨⟨hlo, hhi⟩, hblk, hres⟩

/-- **`blockHonestDisc_eq_sum_pieces` (FULL — item 1).**  The full-block honest discrepancy is the
sum over the `O(log x)` dyadic `p₃`-pieces of the box honest discrepancies (full `m`-range
`(0, x+1)`).  Residue/unit partitions (`blockResCount_eq_sum_pieces`,
`blockUnitCount_eq_sum_pieces`) + linearity. -/
theorem blockHonestDisc_eq_sum_pieces (x z y : ℕ) (ε₀ : ℝ) (j d : ℕ) :
    blockHonestDisc x z y ε₀ j d
      = ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k) 0 (x + 1) d := by
  unfold blockHonestDisc blockBoxHonestDisc
  rw [blockResCount_eq_sum_pieces, blockUnitCount_eq_sum_pieces, Finset.mul_sum,
    ← Finset.sum_sub_distrib]

/-- **`abs_blockHonestDisc_le_sum_pieces` (FULL — item 1, the triangle).** -/
theorem abs_blockHonestDisc_le_sum_pieces (x z y : ℕ) (ε₀ : ℝ) (j d : ℕ) :
    |blockHonestDisc x z y ε₀ j d|
      ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k) 0 (x + 1) d| := by
  rw [blockHonestDisc_eq_sum_pieces]
  exact Finset.abs_sum_le_sum_abs _ _

/-! ## Part C — the piece count (item 2) -/

/-- **`card_pieces` (FULL — item 2).**  The number of dyadic `p₃`-pieces is `Nat.log 2 x + 1`,
`= O(log x)`.  Empty pieces contribute `0` to the item-1 sum automatically. -/
theorem card_pieces (x : ℕ) :
    (Finset.range (Nat.log 2 x + 1)).card = Nat.log 2 x + 1 := Finset.card_range _

/-! ## Part D — the crude per-box bound + the `m`-range split (item 3 machinery) -/

open Classical in
/-- **`blockBoxCount`** — the box's admissible-triple count (no residue/unit condition).  Upper
bounds both `blockBoxResCount` and `blockBoxUnitCount`, hence `|blockBoxHonestDisc|`.  The
block-narrow, `m`-windowed analogue of `SwitchPricing.boxCount`. -/
noncomputable def blockBoxCount (x z y : ℕ) (ε₀ : ℝ) (j N M a b : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧
        N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℝ)

/-- `blockBoxResCount ≤ blockBoxCount` (the residue-`2` filter is a sub-filter). -/
theorem blockBoxResCount_le_blockBoxCount (x z y : ℕ) (ε₀ : ℝ) (j N M a b d : ℕ) :
    blockBoxResCount x z y ε₀ j N M a b d ≤ blockBoxCount x z y ε₀ j N M a b := by
  unfold blockBoxResCount blockBoxCount
  rw [Nat.cast_le]
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  obtain ⟨hmem, hblk, _hres, hN, hM, ha, hb⟩ := ht
  exact ⟨hmem, hblk, hN, hM, ha, hb⟩

/-- `blockBoxUnitCount ≤ blockBoxCount` (the unit filter is a sub-filter). -/
theorem blockBoxUnitCount_le_blockBoxCount (x z y : ℕ) (ε₀ : ℝ) (j N M a b d : ℕ) :
    blockBoxUnitCount x z y ε₀ j N M a b d ≤ blockBoxCount x z y ε₀ j N M a b := by
  classical
  unfold blockBoxUnitCount blockBoxCount
  rw [Nat.cast_le]
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  obtain ⟨hmem, hblk, _hu, hN, hM, ha, hb⟩ := ht
  exact ⟨hmem, hblk, hN, hM, ha, hb⟩

/-- **The crude per-box honest-discrepancy bound (FULL — item 3, the count-form).**
`|blockBoxHonestDisc| ≤ blockBoxCount`: since `blockBoxResCount, ν(d)·blockBoxUnitCount ∈
[0, blockBoxCount]` (using `nuChen_le_one`), both `res − ν·unit` and its negation are `≤ count`.
This is the `|disc| ≤ resCount + ν·unitCount ≤ count`-form of the numeric plan.  **NOTE (item 3
finding):** summing this over the low-piece band's `Θ(x/log x)` triples and `d < bound` does NOT
clear the `x/(log x)^{10}` budget — see the module header numeric assessment; the band stays a
NAMED hypothesis. -/
theorem abs_blockBoxHonestDisc_le_blockBoxCount (x z y : ℕ) (ε₀ : ℝ) (j N M a b d : ℕ) :
    |blockBoxHonestDisc x z y ε₀ j N M a b d| ≤ blockBoxCount x z y ε₀ j N M a b := by
  have hR0 : 0 ≤ blockBoxResCount x z y ε₀ j N M a b d := by unfold blockBoxResCount; positivity
  have hU0 : 0 ≤ blockBoxUnitCount x z y ε₀ j N M a b d := by unfold blockBoxUnitCount; positivity
  have hRC : blockBoxResCount x z y ε₀ j N M a b d ≤ blockBoxCount x z y ε₀ j N M a b :=
    blockBoxResCount_le_blockBoxCount x z y ε₀ j N M a b d
  have hUC : blockBoxUnitCount x z y ε₀ j N M a b d ≤ blockBoxCount x z y ε₀ j N M a b :=
    blockBoxUnitCount_le_blockBoxCount x z y ε₀ j N M a b d
  have hc0 : 0 ≤ nuChen d := by rw [nuChen_apply]; positivity
  have hc1 : nuChen d ≤ 1 := nuChen_le_one d
  have hcU : nuChen d * blockBoxUnitCount x z y ε₀ j N M a b d
      ≤ blockBoxUnitCount x z y ε₀ j N M a b d := mul_le_of_le_one_left hU0 hc1
  have hcUnn : 0 ≤ nuChen d * blockBoxUnitCount x z y ε₀ j N M a b d := mul_nonneg hc0 hU0
  unfold blockBoxHonestDisc
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- **The `m`-range split of the box residue count (FULL).**  For `a ≤ c ≤ b`, the box `[a, b)`
partitions into `[a, c) ⊔ [c, b)` on the `m = p₁p₂` axis (`Finset.card_filter_add_card_filter_not`
at `m < c`). -/
theorem blockBoxResCount_split_m (x z y : ℕ) (ε₀ : ℝ) (j N M a c b d : ℕ)
    (hac : a ≤ c) (hcb : c ≤ b) :
    blockBoxResCount x z y ε₀ j N M a b d
      = blockBoxResCount x z y ε₀ j N M a c d
        + blockBoxResCount x z y ε₀ j N M c b d := by
  classical
  unfold blockBoxResCount
  rw [← Nat.cast_add, Nat.cast_inj,
    ← Finset.card_filter_add_card_filter_not
        (s := (tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
          ((prod3 t : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d) ∧
          N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b))
        (p := fun t => t.1 * t.2.1 < c)]
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

/-- **The `m`-range split of the box unit count (FULL).**  As `blockBoxResCount_split_m`, unit
filter. -/
theorem blockBoxUnitCount_split_m (x z y : ℕ) (ε₀ : ℝ) (j N M a c b d : ℕ)
    (hac : a ≤ c) (hcb : c ≤ b) :
    blockBoxUnitCount x z y ε₀ j N M a b d
      = blockBoxUnitCount x z y ε₀ j N M a c d
        + blockBoxUnitCount x z y ε₀ j N M c b d := by
  classical
  unfold blockBoxUnitCount
  rw [← Nat.cast_add, Nat.cast_inj,
    ← Finset.card_filter_add_card_filter_not
        (s := (tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
          IsUnit ((prod3 t : ℕ) : ZMod d) ∧
          N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b))
        (p := fun t => t.1 * t.2.1 < c)]
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

/-- **The `m`-range split of the box honest discrepancy (FULL).**  Linearity over the residue/unit
splits: `blockBoxHonestDisc [a,b) = blockBoxHonestDisc [a,c) + blockBoxHonestDisc [c,b)`.  The
splitter for item 4 (ordering-clear `[0, z·N+1)` + band `[z·N+1, x+1)`). -/
theorem blockBoxHonestDisc_split_m (x z y : ℕ) (ε₀ : ℝ) (j N M a c b d : ℕ)
    (hac : a ≤ c) (hcb : c ≤ b) :
    blockBoxHonestDisc x z y ε₀ j N M a b d
      = blockBoxHonestDisc x z y ε₀ j N M a c d
        + blockBoxHonestDisc x z y ε₀ j N M c b d := by
  unfold blockBoxHonestDisc
  rw [blockBoxResCount_split_m x z y ε₀ j N M a c b d hac hcb,
    blockBoxUnitCount_split_m x z y ε₀ j N M a c b d hac hcb]
  ring

/-! ## Part E — the composed `hBlock` (item 4) -/

open Classical in
/-- **`hBlock_of_window_prices` (FULL — item 4).**  Items 1–3 assembled into
`BlockPricing.hHDblocks_of_perBlock`'s `hBlock` slot: the per-block honest-discrepancy `L¹`-over-`d`
sum is bounded by the high-piece prices `Phi` plus the named low-piece band `Plo`.

Each piece box `(0, x+1)` splits at `c k = min (z·(pieceN k)+1) (x+1)`
(`blockBoxHonestDisc_split_m`) into the **ordering-clear** sub-box `[0, c k)` (`hord : b ≤ z·N+1`
holds — priced by `Phi`, one
`WindowClose.hHD_of_generalBV_window` application per `(j, piece)`) and the **band** sub-box
`[c k, x+1)` (the `p₂ ≈ p₃` residual — named `Plo`, per the module header: crude count does NOT
close it).  Chains `abs_blockHonestDisc_le_sum_pieces` (item 1) with the per-piece split; the
result is the EXACT per-block `hBlock` shape (`bound := Q·Dlev`) that `hHDblocks_of_perBlock`
composes into `hBVblocks_of_generalBV`. -/
theorem hBlock_of_window_prices (x z y : ℕ) (ε₀ : ℝ) (Ps : ℕ) (bound : ℝ) (j : ℕ)
    (Phi : ℕ → ℝ) (Plo : ℝ)
    (hHigh : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k) 0
                 (min (z * pieceN k + 1) (x + 1)) d| else 0) ≤ Phi k)
    (hLow : (∑ k ∈ Finset.range (Nat.log 2 x + 1),
              ∑ d ∈ Nat.divisors Ps,
                if (d : ℝ) < bound then
                  |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k)
                     (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0) ≤ Plo) :
    (∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |blockHonestDisc x z y ε₀ j d| else 0)
      ≤ (∑ k ∈ Finset.range (Nat.log 2 x + 1), Phi k) + Plo := by
  classical
  set c : ℕ → ℕ := fun k => min (z * pieceN k + 1) (x + 1) with hc
  -- Per `d`: the guarded honest disc is `≤` the summed (clear + band) guarded box terms.
  have hterm : ∀ d : ℕ,
      (if (d : ℝ) < bound then |blockHonestDisc x z y ε₀ j d| else 0)
        ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ((if (d : ℝ) < bound then
                |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k) 0 (c k) d| else 0)
              + (if (d : ℝ) < bound then
                |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k) (c k) (x + 1) d| else 0)) := by
    intro d
    by_cases hd : (d : ℝ) < bound
    · rw [if_pos hd]
      refine le_trans (abs_blockHonestDisc_le_sum_pieces x z y ε₀ j d) ?_
      refine Finset.sum_le_sum (fun k _ => ?_)
      rw [if_pos hd, if_pos hd]
      have hsplit := blockBoxHonestDisc_split_m x z y ε₀ j (pieceN k) (pieceM k) 0 (c k) (x + 1) d
        (Nat.zero_le _) (min_le_right _ _)
      rw [hsplit]
      exact abs_add_le _ _
    · rw [if_neg hd]
      refine Finset.sum_nonneg (fun k _ => ?_)
      simp only [if_neg hd]; positivity
  calc (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then |blockHonestDisc x z y ε₀ j d| else 0)
      ≤ ∑ d ∈ Nat.divisors Ps, ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          ((if (d : ℝ) < bound then
              |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k) 0 (c k) d| else 0)
            + (if (d : ℝ) < bound then
              |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k) (c k) (x + 1) d| else 0)) :=
        Finset.sum_le_sum (fun d _ => hterm d)
    _ = ∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
          ((if (d : ℝ) < bound then
              |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k) 0 (c k) d| else 0)
            + (if (d : ℝ) < bound then
              |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k) (c k) (x + 1) d| else 0)) :=
        Finset.sum_comm
    _ = (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k) 0 (c k) d| else 0)
          + (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k) (c k) (x + 1) d| else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
    _ ≤ (∑ k ∈ Finset.range (Nat.log 2 x + 1), Phi k) + Plo :=
        add_le_add (Finset.sum_le_sum (fun k hk => hHigh k hk)) hLow

/-! ## Composition sanity — the end-to-end chain elaborates

`hBlock_of_window_prices` produces the per-block `hBlock` input of
`BlockPricing.hHDblocks_of_perBlock`, whose output is the `hHD` input of
`BlockPricing.hBVblocks_of_generalBV` (the BVP endpoint).  The high-piece prices `Phi` are
`WindowClose.hHD_of_generalBV_window` applications; the low-piece band `Plo` is the named residual.
-/

section CompositionSanity

#check @Salt.Chen.blockHonestDisc_eq_sum_pieces
#check @Salt.Chen.abs_blockHonestDisc_le_sum_pieces
#check @Salt.Chen.abs_blockBoxHonestDisc_le_blockBoxCount
#check @Salt.Chen.blockBoxHonestDisc_split_m
#check @Salt.Chen.hBlock_of_window_prices
#check @Salt.Chen.hHDblocks_of_perBlock
#check @Salt.Chen.hHD_of_generalBV_window

end CompositionSanity

end Salt.Chen
