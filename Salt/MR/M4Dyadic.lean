/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Window
import Salt.MR.M4Residue
import Salt.MR.Lemma14
import Salt.Entropy.Chowla.ShiftCorr

/-!
# M4-4 — the change of variables, the trivial cut, and THE OUTER DYADIC COVER (`M4Dyadic`)

Source: Matomäki–Radziwiłł–Tao `1503.05121v3`, **§4 step (c)** (p. 15); the campaign freeze
`docs/exploration/s9-freeze-0726.md` :62 and its ⟦AMENDMENT B⟧ row `M4-4` (:279); the wave
plan `docs/exploration/m4-plan-0728.md` (wave 2).

MRT's step (c) is three moves, and this file is exactly those three:

1. **the change of variables** `y = x/(d d₀)` — the outer variable is rescaled and the inner
   short-interval sum is re-indexed by `n = d₀ m`;
2. **the trivial cut** — the part of the range below the floor (`y ≤ X/W^{10}`, and the
   windows shorter than the freeze's `H·d₀/W³`) is discarded against the *trivial* bound;
3. **the outer dyadic cover** — what survives, `y ∈ (X/W^{10}, X]`, is split into
   `≪ 10·log W/log 2` dyadic blocks `X′`, and Theorem A.2 is applied on each.

## ⟦WHY THIS ROW IS NOT SUBSUMED BY THE SUMMIT⟧

`thm_a2'_of_rows` (`ThmA2.lean:466`) is **single-scale**: its carrier is
`(1/X)∫_X^{2X}‖(1/h)·shortSum a s₀ x h‖²dx` at ONE `X`, with `X ≤ N ≤ 2X`.  The *outer*
cover over scales `X′ ∈ (X/W^{10}, X]` is a different object entirely and is untouched by
the S8 arc.  Nothing here instantiates `thm_a2'` (that is M4-5), closes the arithmetic
(M4-7) or glues the door (M4-8); this file lands the scale bookkeeping those rows consume.

## Conventions pinned in this file (pick one and document — the freeze's instruction)

* **ℝ-scales, `ℕ`-window adapters.**  `dyadScale X i = X/2^i` is REAL: there is no
  `ℕ`-division anywhere in this file.  The integer windows are obtained by *filtering* an
  ambient `Finset ℕ` against the real scale (`dyadPart`), exactly as `Lemma14.shortSum`
  filters `s₀` against real endpoints.  `⌈·⌉₊` appears in exactly one place, the count
  `dyadIdx`, and never inside a scale.
* **Half-open, downward.**  The `i`-th block is `(X_{i+1}, X_i] = (X/2^{i+1}, X/2^i]`,
  the `Ioc` genre of `SieveGlue.lean:75–79` (HS-6's half-open endpoint note) and of
  `logMeasure`'s own window
  `Finset.Ioc (x/ω) x`.  The blocks for `i < k` tile `(X/2^k, X]` EXACTLY — disjointly and
  with no endpoint uncovered (`sum_dyadPart`).  The bottom endpoint being *excluded* is
  what makes the cover and the trivial cut exact complements: the cut discards
  `n ≤ X/W^{10}`, the cover keeps `n > X/W^{10}`, and nothing is counted twice or lost.
* **The count is IN-STATEMENT** (law #253).  No `O(log W)` prose: every covering statement
  carries the numeral `10·log W/log 2 + 2`.
* **`W` is H-SCALE.**  `W = (log H)^{12}` (`P-2`, the landed `B₅ = 12` consequence chain),
  so `log W = 12·loglog H` and the count is `≤ 120·loglog H/log 2 + 2 ≤ 174·loglog H + 2`
  — `dyadCount_logPow_le` / `dyadCount_logPow_le_numeral`.  It is NEVER `loglog X`.
* **The index is `dyadIdx`, never `K`.**  `K` in this corpus is the Perron dyadic depth
  (`ThmA2.lean:88–90`'s glyph list) and the `K`-family's parameter; the outer cover's index
  is `i`, its top index `dyadIdx W`, and the number of scales `dyadCount W = dyadIdx W + 1`.

## The `d₀`-dilation is CONSUMED, not re-derived

`M4Residue.sum_reindex_dilate` already lands the reindexing `∑_{n ∈ A} F n = ∑_{m ∈ A/d} F(dm)`
on a set of multiples.  What is new here is the *window transport* — the statement that the
image of the window `(y·d, (y+h)·d]` under `n ↦ n/d` is the window `(y, y+h]`, i.e. the
change of variables itself (`image_div_window_dilate`, `sum_window_dilate`).  Likewise the
trivial bound `norm_absWindowSum_le` (`M4Window.lean:194`) is consumed for the cut, never
re-proved.

## Contents

* §1 `dyadScale`, `dyadIdx`, `dyadCount` — the family and the count bound.
* §2 `dyadPart`, `sum_dyadPart`, `sum_dyadCover`, `exists_dyadScale_cover` — THE COVER.
* §3 the scale-window gate transfers (`√X ≤ X′`, the `log`/`loglog` degradation, `exp 1`,
  `3`, the `h`-ceiling, the `hceil` band).
* §4 the change of variables — the `d₀`-dilation window transport, and the scale-invariance
  of the `thm_a2'` mean-square carrier.
* §5 the `1/n ≍ 1/X′` comparison on a dyadic block.
* §6 the trivial cut (`trivThresh`, the `absWindowSum` bound, its `logMeasure` L¹ form, and
  the `shortSum` card bound with its honest `±1`).
* §7 the per-scale summation — `Finset.sum` form and `sup'` form, and the fused
  `dyadCover_total_le`: per-scale `≤ B` gives total `≤ (10·log W/log 2 + 2)·B`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — the dyadic scale family and its count -/

/-- **The dyadic scale family**: `dyadScale X i = X/2^i`.  Real-valued; the `i`-th outer
scale below `X`.  (Trap: this is the OUTER cover's index — not the Perron depth `K`, not the
`K`-family's parameter.) -/
def dyadScale (X : ℝ) (i : ℕ) : ℝ := X / 2 ^ i

@[simp] theorem dyadScale_zero (X : ℝ) : dyadScale X 0 = X := by
  simp [dyadScale]

theorem dyadScale_succ (X : ℝ) (i : ℕ) : dyadScale X (i + 1) = dyadScale X i / 2 := by
  unfold dyadScale
  rw [pow_succ]
  ring

/-- The block ratio is exactly `2`: `X_i = 2·X_{i+1}`.  This is what makes the `i`-th block
`(X_{i+1}, X_i]` a *dyadic* window `[X_{i+1}, 2X_{i+1}]` in `thm_a2'`'s own shape. -/
theorem two_mul_dyadScale_succ (X : ℝ) (i : ℕ) : 2 * dyadScale X (i + 1) = dyadScale X i := by
  rw [dyadScale_succ]
  ring

theorem one_le_two_pow_real (i : ℕ) : (1 : ℝ) ≤ 2 ^ i := by
  induction i with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; nlinarith

theorem dyadScale_pos {X : ℝ} (hX : 0 < X) (i : ℕ) : 0 < dyadScale X i :=
  div_pos hX (by positivity)

theorem dyadScale_nonneg {X : ℝ} (hX : 0 ≤ X) (i : ℕ) : 0 ≤ dyadScale X i :=
  div_nonneg hX (by positivity)

theorem dyadScale_le_self {X : ℝ} (hX : 0 ≤ X) (i : ℕ) : dyadScale X i ≤ X :=
  div_le_self hX (one_le_two_pow_real i)

theorem dyadScale_succ_le {X : ℝ} (hX : 0 ≤ X) (i : ℕ) :
    dyadScale X (i + 1) ≤ dyadScale X i := by
  rw [dyadScale_succ]
  have : (0 : ℝ) ≤ dyadScale X i := dyadScale_nonneg hX i
  linarith

/-- **The top index of the cover.**  `dyadIdx W = ⌈10·log W/log 2⌉₊`: the least `k` with
`W^{10} ≤ 2^k`, i.e. with `X/2^k ≤ X/W^{10}` — the depth at which the dyadic ladder has
descended past the trivial-cut floor. -/
def dyadIdx (W : ℝ) : ℕ := ⌈10 * Real.log W / Real.log 2⌉₊

/-- **The number of scales in the cover**: `dyadIdx W + 1`, the count of admissible indices
`i ≤ dyadIdx W`.  (`dyadIdx W` blocks tile the range; the scale index of a covered point
runs over `dyadCount W` values, index `0` included.) -/
def dyadCount (W : ℝ) : ℕ := dyadIdx W + 1

theorem dyadCount_pos (W : ℝ) : 0 < dyadCount W := Nat.succ_pos _

theorem dyadIdx_lt_dyadCount (W : ℝ) : dyadIdx W < dyadCount W := Nat.lt_succ_self _

/-- **THE COUNT BOUND, in-statement** (law #253): `⌈10·log W/log 2⌉₊ ≤ 10·log W/log 2 + 1`. -/
theorem dyadIdx_le {W : ℝ} (hW : 1 ≤ W) :
    (dyadIdx W : ℝ) ≤ 10 * Real.log W / Real.log 2 + 1 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogW : (0 : ℝ) ≤ Real.log W := Real.log_nonneg hW
  have h0 : (0 : ℝ) ≤ 10 * Real.log W / Real.log 2 := by positivity
  exact le_of_lt (Nat.ceil_lt_add_one h0)

/-- **THE COUNT BOUND for the scale index**: `dyadCount W ≤ 10·log W/log 2 + 2`.  This is the
numeral every covering statement below carries. -/
theorem dyadCount_le {W : ℝ} (hW : 1 ≤ W) :
    (dyadCount W : ℝ) ≤ 10 * Real.log W / Real.log 2 + 2 := by
  have := dyadIdx_le hW
  unfold dyadCount
  push_cast
  linarith

/-- **The count at the campaign's `W`** — `W = (log H)^{12}` (P-2, `B₅ = 12`).  The scale is
`H`, never `X`: `log W = 12·loglog H`, so the cover has `≤ 120·loglog H/log 2 + 2` scales. -/
theorem dyadCount_logPow_le {H : ℝ} (hH : 1 ≤ Real.log H) :
    (dyadCount ((Real.log H) ^ (12 : ℕ)) : ℝ)
      ≤ 120 * Real.log (Real.log H) / Real.log 2 + 2 := by
  have hW : (1 : ℝ) ≤ (Real.log H) ^ (12 : ℕ) := one_le_pow₀ hH
  have h := dyadCount_le hW
  rw [Real.log_pow] at h
  push_cast at h
  calc (dyadCount ((Real.log H) ^ (12 : ℕ)) : ℝ)
      ≤ 10 * (12 * Real.log (Real.log H)) / Real.log 2 + 2 := h
    _ = 120 * Real.log (Real.log H) / Real.log 2 + 2 := by ring

/-- The same count with `log 2` evaluated: `≤ 174·loglog H + 2` (`120/log 2 = 173.12…`).
This is the freeze's "`≪ 10 log W/log 2` blocks" as a numeral, at the campaign's `W`. -/
theorem dyadCount_logPow_le_numeral {H : ℝ} (hH : 1 ≤ Real.log H) :
    (dyadCount ((Real.log H) ^ (12 : ℕ)) : ℝ) ≤ 174 * Real.log (Real.log H) + 2 := by
  have h := dyadCount_logPow_le hH
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hd9 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hLL : (0 : ℝ) ≤ Real.log (Real.log H) := Real.log_nonneg hH
  have hstep : 120 * Real.log (Real.log H) / Real.log 2 ≤ 174 * Real.log (Real.log H) := by
    rw [div_le_iff₀ hlog2]
    nlinarith
  linarith

/-- **The ladder descends past the floor**: `W^{10} ≤ 2^{dyadIdx W}`.  This is the whole
content of the ceiling in `dyadIdx`. -/
theorem pow_ten_le_two_pow_dyadIdx {W : ℝ} (hW : 1 ≤ W) :
    W ^ (10 : ℕ) ≤ 2 ^ (dyadIdx W) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogW : (0 : ℝ) ≤ Real.log W := Real.log_nonneg hW
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  have hceil : 10 * Real.log W / Real.log 2 ≤ (dyadIdx W : ℝ) := Nat.le_ceil _
  have hmul : 10 * Real.log W ≤ (dyadIdx W : ℝ) * Real.log 2 := by
    rw [div_le_iff₀ hlog2] at hceil
    exact hceil
  have hlogs : Real.log (W ^ (10 : ℕ)) ≤ Real.log ((2 : ℝ) ^ (dyadIdx W)) := by
    rw [Real.log_pow, Real.log_pow]
    push_cast
    linarith
  have hL : (0 : ℝ) < W ^ (10 : ℕ) := by positivity
  have hR : (0 : ℝ) < (2 : ℝ) ^ (dyadIdx W) := by positivity
  have := Real.exp_le_exp.mpr hlogs
  rwa [Real.exp_log hL, Real.exp_log hR] at this

/-- The bottom scale of the cover is below the trivial-cut floor: `X/2^{dyadIdx W} ≤ X/W^{10}`. -/
theorem dyadScale_dyadIdx_le {X W : ℝ} (hX : 0 ≤ X) (hW : 1 ≤ W) :
    dyadScale X (dyadIdx W) ≤ X / W ^ (10 : ℕ) := by
  have hW0 : (0 : ℝ) < W ^ (10 : ℕ) := by
    have : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
    positivity
  have hpow := pow_ten_le_two_pow_dyadIdx hW
  unfold dyadScale
  gcongr

/-! ## §2 — THE COVER: the blocks, the exact tiling, and the membership lemma -/

/-- **The `i`-th dyadic block**, as a `Finset ℕ`: the elements of the ambient window `S`
lying in `(X_{i+1}, X_i] = (X/2^{i+1}, X/2^i]`.  This is the `ℕ`-window adapter of the real
scale family — half-open at the bottom, matching `logMeasure`'s `Finset.Ioc (x/ω) x`. -/
def dyadPart (S : Finset ℕ) (X : ℝ) (i : ℕ) : Finset ℕ :=
  S.filter (fun n : ℕ => dyadScale X (i + 1) < (n : ℝ) ∧ (n : ℝ) ≤ dyadScale X i)

theorem mem_dyadPart {S : Finset ℕ} {X : ℝ} {i n : ℕ} :
    n ∈ dyadPart S X i ↔
      n ∈ S ∧ dyadScale X (i + 1) < (n : ℝ) ∧ (n : ℝ) ≤ dyadScale X i := by
  simp [dyadPart, Finset.mem_filter]

theorem dyadPart_subset (S : Finset ℕ) (X : ℝ) (i : ℕ) : dyadPart S X i ⊆ S :=
  Finset.filter_subset _ _

/-- **The block is a `thm_a2'` window**: every `n` in the `i`-th block satisfies
`X′ < n ≤ 2X′` at the block's own scale `X′ = X_{i+1}`. -/
theorem dyadPart_window {S : Finset ℕ} {X : ℝ} {i n : ℕ} (hn : n ∈ dyadPart S X i) :
    dyadScale X (i + 1) < (n : ℝ) ∧ (n : ℝ) ≤ 2 * dyadScale X (i + 1) := by
  rw [mem_dyadPart] at hn
  refine ⟨hn.2.1, ?_⟩
  rw [two_mul_dyadScale_succ]
  exact hn.2.2

/-- **THE EXACT TILING.**  The blocks `i < k` tile `(X/2^k, X]` — disjointly, no endpoint
lost.  Stated as an identity of sums in an arbitrary `AddCommMonoid`, so the consumer may
carry a real weight, a complex sum, or an `ℝ≥0∞` mass through it unchanged. -/
theorem sum_dyadPart {M : Type*} [AddCommMonoid M] (S : Finset ℕ) {X : ℝ} (hX : 0 ≤ X)
    (f : ℕ → M) (k : ℕ) :
    ∑ n ∈ S.filter (fun n : ℕ => dyadScale X k < (n : ℝ) ∧ (n : ℝ) ≤ X), f n
      = ∑ i ∈ Finset.range k, ∑ n ∈ dyadPart S X i, f n := by
  induction k with
  | zero =>
    have hempty : S.filter (fun n : ℕ => dyadScale X 0 < (n : ℝ) ∧ (n : ℝ) ≤ X) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro n _
      rw [dyadScale_zero]
      rintro ⟨h1, h2⟩
      linarith
    rw [hempty]
    simp
  | succ k ih =>
    have hle1 : dyadScale X (k + 1) ≤ dyadScale X k := dyadScale_succ_le hX k
    have hle2 : dyadScale X k ≤ X := dyadScale_le_self hX k
    have hsplit : S.filter (fun n : ℕ => dyadScale X (k + 1) < (n : ℝ) ∧ (n : ℝ) ≤ X)
        = (S.filter (fun n : ℕ => dyadScale X k < (n : ℝ) ∧ (n : ℝ) ≤ X)) ∪ dyadPart S X k := by
      ext n
      simp only [Finset.mem_union, Finset.mem_filter, mem_dyadPart]
      constructor
      · rintro ⟨hnS, h1, h2⟩
        rcases lt_or_ge (dyadScale X k) (n : ℝ) with h | h
        · exact Or.inl ⟨hnS, h, h2⟩
        · exact Or.inr ⟨hnS, h1, h⟩
      · rintro (⟨hnS, h1, h2⟩ | ⟨hnS, h1, h2⟩)
        · exact ⟨hnS, lt_of_le_of_lt hle1 h1, h2⟩
        · exact ⟨hnS, h1, le_trans h2 hle2⟩
    have hdisj : Disjoint (S.filter (fun n : ℕ => dyadScale X k < (n : ℝ) ∧ (n : ℝ) ≤ X))
        (dyadPart S X k) := by
      rw [Finset.disjoint_left]
      intro n hn hn'
      rw [Finset.mem_filter] at hn
      rw [mem_dyadPart] at hn'
      exact absurd hn'.2.2 (not_le.mpr hn.2.1)
    rw [hsplit, Finset.sum_union hdisj, ih, Finset.sum_range_succ]

/-- **THE COVER, with the trivial-cut floor**: what survives the cut — the ambient elements
in `(X/W^{10}, X]` — is dominated by the `dyadIdx W` blocks.  (The containment, not an
identity: the ladder's bottom block reaches slightly below the floor.) -/
theorem sum_dyadCover {S : Finset ℕ} {X W : ℝ} (hX : 0 ≤ X) (hW : 1 ≤ W) {f : ℕ → ℝ}
    (hf : ∀ n ∈ S, 0 ≤ f n) :
    ∑ n ∈ S.filter (fun n : ℕ => X / W ^ (10 : ℕ) < (n : ℝ) ∧ (n : ℝ) ≤ X), f n
      ≤ ∑ i ∈ Finset.range (dyadIdx W), ∑ n ∈ dyadPart S X i, f n := by
  have hfloor := dyadScale_dyadIdx_le hX hW
  have hsub : S.filter (fun n : ℕ => X / W ^ (10 : ℕ) < (n : ℝ) ∧ (n : ℝ) ≤ X)
      ⊆ S.filter (fun n : ℕ => dyadScale X (dyadIdx W) < (n : ℝ) ∧ (n : ℝ) ≤ X) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, lt_of_le_of_lt hfloor hn.2.1, hn.2.2⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
  · intro n hn _
    exact hf n (Finset.mem_of_mem_filter n hn)
  · exact le_of_eq (sum_dyadPart S hX f (dyadIdx W))

/-- **THE MEMBERSHIP LEMMA (block form).**  Every point of `(X/2^k, X]` lies in exactly one
block, and its index is `< k`. -/
theorem exists_dyadPart_mem {X : ℝ} (k : ℕ) {X' : ℝ}
    (hlo : dyadScale X k < X') (hhi : X' ≤ X) :
    ∃ i < k, dyadScale X (i + 1) < X' ∧ X' ≤ dyadScale X i := by
  induction k with
  | zero =>
    rw [dyadScale_zero] at hlo
    exact absurd hhi (not_le.mpr hlo)
  | succ k ih =>
    rcases lt_or_ge (dyadScale X k) X' with h | h
    · obtain ⟨i, hik, hi⟩ := ih h
      exact ⟨i, Nat.lt_succ_of_lt hik, hi⟩
    · exact ⟨k, Nat.lt_succ_self k, hlo, h⟩

/-- **THE MEMBERSHIP LEMMA (scale form) — the deliverable the close consumes.**  Every
scale `X′` surviving the trivial cut lies in a dyadic window `[X_i, 2X_i]` with the index
`i` below the IN-STATEMENT count `dyadCount W`.  This is the `thm_a2'`-side shape: `X_i` is
the theorem's `X`, and `X′` its `[X, 2X]` window point. -/
theorem exists_dyadScale_cover {X W X' : ℝ} (hX : 0 ≤ X) (hW : 1 ≤ W)
    (hlo : X / W ^ (10 : ℕ) < X') (hhi : X' ≤ X) :
    ∃ i < dyadCount W, dyadScale X i ≤ X' ∧ X' ≤ 2 * dyadScale X i := by
  have hfloor := dyadScale_dyadIdx_le hX hW
  obtain ⟨i, hik, h1, h2⟩ := exists_dyadPart_mem (dyadIdx W) (lt_of_le_of_lt hfloor hlo) hhi
  refine ⟨i + 1, ?_, h1.le, ?_⟩
  · unfold dyadCount
    omega
  · rw [two_mul_dyadScale_succ]
    exact h2

/-- The scale produced by the cover sits above `X/(2W^{10})` — one factor of `2` below the
trivial-cut floor.  This is the floor at which §3's gate transfers are applied. -/
theorem dyadScale_floor_of_cover {X W X' Xi : ℝ}
    (hlo : X / W ^ (10 : ℕ) < X') (hcov : X' ≤ 2 * Xi) :
    X / (2 * W ^ (10 : ℕ)) < Xi := by
  have h : X / (2 * W ^ (10 : ℕ)) = (X / W ^ (10 : ℕ)) / 2 := by
    ring
  rw [h]
  linarith

/-! ## §3 — the scale-window gates: what a block scale inherits from `X`

The freeze's side-condition list for M4-5 opens with `√X ≤ X′` "(from `X′ ≥ X/W^{10}` +
`W ≤ X^{1/250}` via `W_second_arm`)".  That derivation is here, together with the `thm_a2'`
gates that follow from it.  Every degradation is kept SYMBOLIC: at door scales it is
infinitesimal, but it is stated exactly. -/

/-- **The depth transfer.**  A floor `X/D ≤ X′` at depth `D ≤ √X` delivers `√X ≤ X′`.  (The
whole `√X`-side condition, with the depth left symbolic.) -/
theorem sqrt_le_of_depth {X D X' : ℝ} (hX : 1 ≤ X) (hD : 0 < D) (hDs : D ≤ Real.sqrt X)
    (hlo : X / D ≤ X') : Real.sqrt X ≤ X' := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  have hs0 : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hself : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hdiv : Real.sqrt X = X / Real.sqrt X := by
    field_simp
    linarith [hself]
  have : X / Real.sqrt X ≤ X / D := by gcongr
  linarith [hdiv ▸ this, hlo]

/-- **The door-scale depth**: `2W^{10} ≤ √X` from the freeze's `W ≤ X^{1/250}`
(`W_second_arm`'s arm).  The `2` is the cover's own factor (`dyadScale_floor_of_cover`), and
`8 ≤ X` is the only extra room the arithmetic needs (`2 ≤ X^{23/50}`). -/
theorem two_mul_pow_ten_le_sqrt {X W : ℝ} (hX : 8 ≤ X) (hW : 1 ≤ W)
    (hWX : W ≤ X ^ ((1 : ℝ) / 250)) : 2 * W ^ (10 : ℕ) ≤ Real.sqrt X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hW0 : (0 : ℝ) ≤ W := le_trans zero_le_one hW
  -- `W^{10} ≤ X^{1/25}`
  have h1 : W ^ (10 : ℕ) ≤ (X ^ ((1 : ℝ) / 250)) ^ (10 : ℕ) := by
    exact pow_le_pow_left₀ hW0 hWX 10
  have h2 : (X ^ ((1 : ℝ) / 250)) ^ (10 : ℕ) = X ^ ((1 : ℝ) / 25) := by
    rw [← Real.rpow_natCast (X ^ ((1 : ℝ) / 250)) 10, ← Real.rpow_mul hX0.le]
    norm_num
  -- `2 ≤ X^{23/50}`
  have h8 : (8 : ℝ) ^ ((23 : ℝ) / 50) ≤ X ^ ((23 : ℝ) / 50) :=
    Real.rpow_le_rpow (by norm_num) hX (by norm_num)
  have h8eq : (8 : ℝ) ^ ((23 : ℝ) / 50) = (2 : ℝ) ^ ((69 : ℝ) / 50) := by
    have : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [this, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h2le : (2 : ℝ) ≤ (2 : ℝ) ^ ((69 : ℝ) / 50) := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1 : ℝ) ≤ (69 : ℝ) / 50)
    rwa [Real.rpow_one] at this
  have h23 : (2 : ℝ) ≤ X ^ ((23 : ℝ) / 50) := by
    rw [h8eq] at h8
    linarith
  -- `√X = X^{1/25}·X^{23/50}`
  have hsplit : Real.sqrt X = X ^ ((1 : ℝ) / 25) * X ^ ((23 : ℝ) / 50) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX0]
    norm_num
  have hpos : (0 : ℝ) < X ^ ((1 : ℝ) / 25) := Real.rpow_pos_of_pos hX0 _
  calc 2 * W ^ (10 : ℕ) ≤ 2 * X ^ ((1 : ℝ) / 25) := by rw [← h2]; linarith
    _ ≤ X ^ ((1 : ℝ) / 25) * X ^ ((23 : ℝ) / 50) := by nlinarith
    _ = Real.sqrt X := hsplit.symm

/-- **THE `√X ≤ X′` SIDE CONDITION, assembled.**  A block scale `X_i` produced by the cover
above the trivial-cut floor, at the door's `W ≤ X^{1/250}`, dominates `√X`. -/
theorem sqrt_le_dyadScale {X W X' Xi : ℝ} (hX : 8 ≤ X) (hW : 1 ≤ W)
    (hWX : W ≤ X ^ ((1 : ℝ) / 250)) (hlo : X / W ^ (10 : ℕ) < X') (hcov : X' ≤ 2 * Xi) :
    Real.sqrt X ≤ Xi := by
  have hW0 : (0 : ℝ) < W ^ (10 : ℕ) := by
    have : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
    positivity
  have hdepth : 2 * W ^ (10 : ℕ) ≤ Real.sqrt X := two_mul_pow_ten_le_sqrt hX hW hWX
  have hfl : X / (2 * W ^ (10 : ℕ)) < Xi := dyadScale_floor_of_cover hlo hcov
  exact le_trans (sqrt_le_of_depth (by linarith) (by positivity) hdepth le_rfl) hfl.le

/-- `thm_a2'`'s `e ≤ X` gate at a block scale. -/
theorem exp_one_le_of_sqrt_le {X X' : ℝ} (hX : Real.exp 2 ≤ X) (h : Real.sqrt X ≤ X') :
    Real.exp 1 ≤ X' := by
  have hsq : Real.sqrt (Real.exp 2) = Real.exp 1 := by
    rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num,
      Real.sqrt_mul_self (Real.exp_pos 1).le]
  calc Real.exp 1 = Real.sqrt (Real.exp 2) := hsq.symm
    _ ≤ Real.sqrt X := Real.sqrt_le_sqrt hX
    _ ≤ X' := h

/-- `thm_a2'`'s `3 ≤ X` gate at a block scale. -/
theorem three_le_of_sqrt_le {X X' : ℝ} (hX : 9 ≤ X) (h : Real.sqrt X ≤ X') : 3 ≤ X' := by
  have hsq : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num, Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 3)]
  calc (3 : ℝ) = Real.sqrt 9 := hsq.symm
    _ ≤ Real.sqrt X := Real.sqrt_le_sqrt hX
    _ ≤ X' := h

/-- The scale's logarithm, exactly: `log X_i = log X − i·log 2`. -/
theorem log_dyadScale {X : ℝ} (hX : 0 < X) (i : ℕ) :
    Real.log (dyadScale X i) = Real.log X - (i : ℝ) * Real.log 2 := by
  unfold dyadScale
  rw [Real.log_div hX.ne' (by positivity), Real.log_pow]

/-- **The `log` degradation, symbolic**: a floor at depth `D` costs exactly `log D`. -/
theorem log_sub_log_le_log_of_floor {X D X' : ℝ} (hX : 0 < X) (hD : 0 < D)
    (hlo : X / D ≤ X') : Real.log X - Real.log D ≤ Real.log X' := by
  have h := Real.log_le_log (by positivity) hlo
  rwa [Real.log_div hX.ne' hD.ne'] at h

/-- **The `loglog` degradation, exactly `log 2`.**  Under the halving gate
`2·log D ≤ log X` — absurdly slack at door scales, where `log D = 10·log W = 120·loglog H`
against `log X` — a scale above `X/D` loses at most `log 2` of `loglog`.  This is the honest
form of the freeze's "loglog X_i ≥ loglog X − …": no `o(1)`, a numeral. -/
theorem loglog_sub_log_two_le {X D X' : ℝ} (hX : 1 < X) (hD : 0 < D)
    (hgate : 2 * Real.log D ≤ Real.log X) (hlo : X / D ≤ X') :
    Real.log (Real.log X) - Real.log 2 ≤ Real.log (Real.log X') := by
  have hLX : (0 : ℝ) < Real.log X := Real.log_pos hX
  have h1 : Real.log X - Real.log D ≤ Real.log X' :=
    log_sub_log_le_log_of_floor (by linarith) hD hlo
  have h2 : Real.log X / 2 ≤ Real.log X' := by linarith
  have h3 : Real.log (Real.log X / 2) ≤ Real.log (Real.log X') :=
    Real.log_le_log (by linarith) h2
  rwa [Real.log_div hLX.ne' (by norm_num)] at h3

/-- **The `h`-ceiling transfer.**  `thm_a2'`'s `h ≤ X(log X)^{−1/5}` at a block scale, from
the same bound at `√X`: the window frame survives the descent because `(log ·)^{−1/5}` is
antitone and `√X ≤ X′`. -/
theorem h_ceiling_transfer {X X' h : ℝ} (hL1 : 1 ≤ Real.log X') (hle : Real.log X' ≤ Real.log X)
    (hs : Real.sqrt X ≤ X') (hh : h ≤ Real.sqrt X * (Real.log X) ^ (-(1 : ℝ) / 5)) :
    h ≤ X' * (Real.log X') ^ (-(1 : ℝ) / 5) := by
  have hrp : (Real.log X) ^ (-(1 : ℝ) / 5) ≤ (Real.log X') ^ (-(1 : ℝ) / 5) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hle (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hrp0 : (0 : ℝ) ≤ (Real.log X) ^ (-(1 : ℝ) / 5) :=
    Real.rpow_nonneg (by linarith) _
  calc h ≤ Real.sqrt X * (Real.log X) ^ (-(1 : ℝ) / 5) := hh
    _ ≤ X' * (Real.log X') ^ (-(1 : ℝ) / 5) := by
        refine mul_le_mul hs hrp hrp0 (le_trans hs0 hs)

/-- **The `hceil` band transfer** — `thm_a2'`'s `5 ≤ loglog(2X/h)` at a block scale.  The
gate `1 ≤ log(2√X/h)` is the (door-trivial) positivity the monotone step needs. -/
theorem five_le_loglog_transfer {X X' h : ℝ} (hh : 0 < h) (hs : Real.sqrt X ≤ X')
    (hgate : 1 ≤ Real.log (2 * Real.sqrt X / h))
    (h5 : 5 ≤ Real.log (Real.log (2 * Real.sqrt X / h))) :
    5 ≤ Real.log (Real.log (2 * X' / h)) := by
  have hmono : 2 * Real.sqrt X / h ≤ 2 * X' / h := by gcongr
  have ht0 : (0 : ℝ) ≤ 2 * Real.sqrt X / h := by positivity
  have hpos : (0 : ℝ) < 2 * Real.sqrt X / h := by
    rcases ht0.lt_or_eq with h' | h'
    · exact h'
    · rw [← h', Real.log_zero] at hgate
      linarith
  have hlog : Real.log (2 * Real.sqrt X / h) ≤ Real.log (2 * X' / h) :=
    Real.log_le_log hpos hmono
  exact le_trans h5 (Real.log_le_log (by linarith) hlog)

/-! ## §4 — THE CHANGE OF VARIABLES

Two halves, matching MRT's two:  the inner sum's reindexing `n = d₀ m` (a `Finset` window
transport, consuming `M4Residue.sum_reindex_dilate`), and the outer variable's rescaling
`y = x/c` (the `thm_a2'` mean-square carrier is INVARIANT under it — the reason the cover
may be taken in the rescaled variable). -/

/-- **THE WINDOW TRANSPORT.**  Under `n ↦ n/d` the window `(y·d, (y+h)·d]` of multiples of
`d` becomes the window `(y, y+h]` — the change of variables `y = x/d`, `h = H′/d`, with no
`±1` slack (the divisibility makes the correspondence exact). -/
theorem image_div_window_dilate {d : ℕ} (hd : 0 < d) (S : Finset ℕ) (y hlen : ℝ) :
    ((S.filter (fun n : ℕ => d ∣ n)).filter
        (fun n : ℕ => y * d < (n : ℝ) ∧ (n : ℝ) ≤ (y + hlen) * d)).image (fun n : ℕ => n / d)
      = ((S.filter (fun n : ℕ => d ∣ n)).image (fun n : ℕ => n / d)).filter
          (fun m : ℕ => y < (m : ℝ) ∧ (m : ℝ) ≤ y + hlen) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  ext m
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨n, ⟨⟨hnS, hdvd⟩, hw1, hw2⟩, rfl⟩
    have hn : ((n / d : ℕ) : ℝ) * (d : ℝ) = (n : ℝ) := by
      rw [mul_comm, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    refine ⟨⟨n, ⟨hnS, hdvd⟩, rfl⟩, ?_, ?_⟩
    · refine lt_of_mul_lt_mul_right ?_ hd0.le
      rw [hn]
      exact hw1
    · refine le_of_mul_le_mul_right ?_ hd0
      rw [hn]
      exact hw2
  · rintro ⟨⟨n, ⟨hnS, hdvd⟩, rfl⟩, hw1, hw2⟩
    have hn : ((n / d : ℕ) : ℝ) * (d : ℝ) = (n : ℝ) := by
      rw [mul_comm, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    refine ⟨n, ⟨⟨hnS, hdvd⟩, ?_, ?_⟩, rfl⟩
    · have := mul_lt_mul_of_pos_right hw1 hd0
      rwa [hn] at this
    · have := mul_le_mul_of_nonneg_right hw2 hd0.le
      rwa [hn] at this

/-- **THE C.O.V. ON THE SUM** (MRT §4(b)+(c) in `Finset` form).  The short sum over the
multiples of `d` in `(x, x+H′]` is the sum of `F(d·)` over the rebased window `(y, y+h]`,
`x = y·d`, `H′ = h·d`.  This is the mechanical lemma M4-7/M4-8 consume; the reindexing
itself is `M4Residue.sum_reindex_dilate`, cited, not re-proved. -/
theorem sum_window_dilate {d : ℕ} (hd : 0 < d) (S : Finset ℕ) (y hlen : ℝ) (F : ℕ → ℂ) :
    ∑ n ∈ (S.filter (fun n : ℕ => d ∣ n)).filter
        (fun n : ℕ => y * d < (n : ℝ) ∧ (n : ℝ) ≤ (y + hlen) * d), F n
      = ∑ m ∈ ((S.filter (fun n : ℕ => d ∣ n)).image (fun n : ℕ => n / d)).filter
          (fun m : ℕ => y < (m : ℝ) ∧ (m : ℝ) ≤ y + hlen), F (d * m) := by
  rw [sum_reindex_dilate
      (fun n hn => (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2) F,
    image_div_window_dilate hd S y hlen]

/-- **THE OUTER C.O.V.: the mean-square carrier is scale-invariant.**  `y = x/c` turns the
normalised mean square at scale `c·X′` into the normalised mean square at scale `X′` — the
`thm_a2'` carrier on the nose.  (`intervalIntegral.integral_comp_div`'s `c` cancels the
`1/(cX′)` exactly; this is why MRT may pass to the rescaled variable before covering.) -/
theorem meanSq_scale_invariant (G : ℝ → ℝ) {c X' : ℝ} (hc : 0 < c) (hX' : 0 < X') :
    1 / (c * X') * (∫ x in (c * X')..(2 * (c * X')), G (x / c))
      = 1 / X' * ∫ y in X'..(2 * X'), G y := by
  rw [intervalIntegral.integral_comp_div G hc.ne']
  have h1 : c * X' / c = X' := by field_simp
  have h2 : 2 * (c * X') / c = 2 * X' := by field_simp
  rw [h1, h2, smul_eq_mul]
  field_simp

/-- The same at the landed carrier: `‖(1/h)·shortSum a s₀ · h‖²`.  The left side is MRT's
`x`-integral at scale `cX′` with the inner sum read at `y = x/c`; the right side is exactly
`thm_a2'_of_rows`' left-hand side at `X := X′`. -/
theorem meanSq_shortSum_scale (a : ℕ → ℂ) (s0 : Finset ℕ) (hlen : ℝ) {c X' : ℝ}
    (hc : 0 < c) (hX' : 0 < X') :
    1 / (c * X') * (∫ x in (c * X')..(2 * (c * X')),
        ‖((1 / hlen : ℝ) : ℂ) * shortSum a s0 (x / c) hlen‖ ^ 2)
      = 1 / X' * ∫ y in X'..(2 * X'),
          ‖((1 / hlen : ℝ) : ℂ) * shortSum a s0 y hlen‖ ^ 2 :=
  meanSq_scale_invariant (fun y => ‖((1 / hlen : ℝ) : ℂ) * shortSum a s0 y hlen‖ ^ 2) hc hX'

/-! ## §5 — the `1/n ≍ 1/X′` comparison on a block

The door's outer measure is the harmonic one (`logMeasure`: `∫f dμ = Z⁻¹∑ f(n)/n`,
`ShiftCorr.integral_logMeasure_eq`), so the dyadic cover meets the weights `1/n`.  On a
block these are constant up to a factor `2`, which is the entire content of the dyadic
choice.  Both directions are landed: the consumer needs the upper one to *spend* the
weight and the lower one to *recover* the mass. -/

/-- `∑ f(n)/n ≤ (∑ f(n))/X′` on a window with `X′ < n`. -/
theorem sum_div_le_of_window {S : Finset ℕ} {X' : ℝ} (hX' : 0 < X') {f : ℕ → ℝ}
    (hf : ∀ n ∈ S, 0 ≤ f n) (hS : ∀ n ∈ S, X' < (n : ℝ)) :
    ∑ n ∈ S, f n / (n : ℝ) ≤ (∑ n ∈ S, f n) / X' := by
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun n hn => ?_
  have h0 : (0 : ℝ) < X' := hX'
  have h1 : X' ≤ (n : ℝ) := (hS n hn).le
  have h2 : 0 ≤ f n := hf n hn
  gcongr

/-- `(∑ f(n))/(2X′) ≤ ∑ f(n)/n` on a window with `n ≤ 2X′`. -/
theorem le_sum_div_of_window {S : Finset ℕ} {X' : ℝ} {f : ℕ → ℝ}
    (hf : ∀ n ∈ S, 0 ≤ f n) (hS0 : ∀ n ∈ S, 0 < (n : ℝ)) (hS : ∀ n ∈ S, (n : ℝ) ≤ 2 * X') :
    (∑ n ∈ S, f n) / (2 * X') ≤ ∑ n ∈ S, f n / (n : ℝ) := by
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun n hn => ?_
  have h1 : (n : ℝ) ≤ 2 * X' := hS n hn
  have h2 : 0 ≤ f n := hf n hn
  have h3 : 0 < (n : ℝ) := hS0 n hn
  gcongr

/-- The upper comparison on the `i`-th block, at the block's own scale `X_{i+1}`. -/
theorem sum_div_dyadPart_le {S : Finset ℕ} {X : ℝ} (hX : 0 < X) (i : ℕ) {f : ℕ → ℝ}
    (hf : ∀ n ∈ S, 0 ≤ f n) :
    ∑ n ∈ dyadPart S X i, f n / (n : ℝ)
      ≤ (∑ n ∈ dyadPart S X i, f n) / dyadScale X (i + 1) :=
  sum_div_le_of_window (dyadScale_pos hX (i + 1))
    (fun n hn => hf n (dyadPart_subset S X i hn))
    (fun _ hn => (mem_dyadPart.mp hn).2.1)

/-- The lower comparison on the `i`-th block: the mass divided by the block top `X_i`
(`= 2X_{i+1}`) is below the harmonic sum. -/
theorem le_sum_div_dyadPart {S : Finset ℕ} {X : ℝ} (hX : 0 < X) (i : ℕ) {f : ℕ → ℝ}
    (hf : ∀ n ∈ S, 0 ≤ f n) :
    (∑ n ∈ dyadPart S X i, f n) / dyadScale X i
      ≤ ∑ n ∈ dyadPart S X i, f n / (n : ℝ) := by
  have h := le_sum_div_of_window (S := dyadPart S X i) (X' := dyadScale X (i + 1))
    (fun n hn => hf n (dyadPart_subset S X i hn))
    (fun _ hn => lt_trans (dyadScale_pos hX (i + 1)) (mem_dyadPart.mp hn).2.1)
    (fun _ hn => (dyadPart_window hn).2)
  rwa [two_mul_dyadScale_succ] at h

/-! ## §6 — THE TRIVIAL CUT

The freeze's threshold is `H·d₀/W³` (M4-5's trivial branch); it is carried SYMBOLICALLY
here — this file never evaluates it.  The bound itself is the landed one:
`M4Window.norm_absWindowSum_le` (a window of `H′` terms of modulus `≤ 1`), consumed, plus
its `L¹` form against the door's own measure. -/

/-- **The freeze's trivial-cut threshold**, symbolic: `H·d₀/W³`.  Never evaluated. -/
def trivThresh (H d₀ W : ℝ) : ℝ := H * d₀ / W ^ (3 : ℕ)

/-- **The trivial cut, pointwise**: a window shorter than the threshold is discarded against
the trivial bound (`norm_absWindowSum_le`, consumed). -/
theorem norm_absWindowSum_le_thresh {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) {H' : ℕ} {thr : ℝ}
    (hthr : (H' : ℝ) ≤ thr) (n : ℕ) (α : ℝ) : ‖absWindowSum a H' n α‖ ≤ thr :=
  le_trans (norm_absWindowSum_le ha H' n α) hthr

/-- The same at the freeze's own threshold. -/
theorem norm_absWindowSum_le_trivThresh {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) {H' : ℕ}
    {H d₀ W : ℝ} (hH' : (H' : ℝ) ≤ trivThresh H d₀ W) (n : ℕ) (α : ℝ) :
    ‖absWindowSum a H' n α‖ ≤ trivThresh H d₀ W :=
  norm_absWindowSum_le_thresh ha hH' n α

/-- **The `L¹` triviality, general**: the door's measure is a probability measure, so a
uniform pointwise bound passes under `∫ · ∂logMeasure` unchanged.  (Proved through
`ShiftCorr.integral_logMeasure_eq`, so no integrability side condition is incurred.) -/
theorem integral_logMeasure_le_of_le {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) {f : ℕ → ℝ} {B : ℝ}
    (hB : ∀ n, f n ≤ B) : (∫ n, f n ∂(logMeasure x ω)) ≤ B := by
  rw [integral_logMeasure_eq]
  set Z := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZdef
  have hZpos : 0 < Z := by
    rw [hZdef]
    refine Finset.sum_pos (fun n hn => ?_) (window_nonempty hx hω)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast window_one_le hn
    positivity
  have hle : ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹ ≤ B * Z := by
    rw [hZdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast window_one_le hn
    have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_right (hB n) hinv
  have hinvZ : (0 : ℝ) < Z⁻¹ := by positivity
  calc Z⁻¹ * ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹
      ≤ Z⁻¹ * (B * Z) := by exact mul_le_mul_of_nonneg_left hle hinvZ.le
    _ = B := by field_simp

/-- **THE TRIVIAL CUT IN THE DOOR'S OWN SHAPE.**  Below the threshold the M4 analytic
obligation is discharged with no analysis at all: the `logMeasure`-`L¹` norm of the
absolute-indexed window sum is `≤ H′ ≤ thr`.  This is the branch the consumer takes to
discard tiny windows (`mrtUniformityXi_of_absWindowBound`'s `hbd` at `thr := δ·H`). -/
theorem integral_logMeasure_absWindowSum_le_thresh {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω)
    {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) {H' : ℕ} {thr : ℝ} (hthr : (H' : ℝ) ≤ thr) (α : ℝ) :
    (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure x ω)) ≤ thr :=
  integral_logMeasure_le_of_le hx hω (fun n => norm_absWindowSum_le_thresh ha hthr n α)

/-- The card of a real short window `(x, x+h]`: at most `h + 1`.  The `+1` is the honest
half-open slack (the freeze's "±1 each side" for M4-8), stated once. -/
theorem card_shortWindow_le (s0 : Finset ℕ) {x hlen : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ hlen) :
    ((s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + hlen)).card : ℝ) ≤ hlen + 1 := by
  have hsub : s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + hlen)
      ⊆ Finset.Ioc ⌊x⌋₊ ⌊x + hlen⌋₊ := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_Ioc]
    exact ⟨(Nat.floor_lt hx).mpr hm.2.1, Nat.le_floor hm.2.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at hcard
  have hcast : ((s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + hlen)).card : ℝ)
      ≤ ((⌊x + hlen⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcard
  refine le_trans hcast ?_
  rcases le_or_gt ⌊x + hlen⌋₊ ⌊x⌋₊ with hcase | hcase
  · have : (⌊x + hlen⌋₊ - ⌊x⌋₊ : ℕ) = 0 := by omega
    rw [this]
    push_cast
    linarith
  · have hsub' : ((⌊x + hlen⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) = (⌊x + hlen⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) := by
      have : ⌊x⌋₊ ≤ ⌊x + hlen⌋₊ := hcase.le
      push_cast [Nat.cast_sub this]
      ring
    rw [hsub']
    have h1 : (⌊x + hlen⌋₊ : ℝ) ≤ x + hlen := Nat.floor_le (by linarith)
    have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith

/-- **The trivial bound at the `thm_a2'` carrier**: `‖shortSum a s₀ x h‖ ≤ h + 1` at a
1-bounded datum. -/
theorem norm_shortSum_le {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (s0 : Finset ℕ) {x hlen : ℝ}
    (hx : 0 ≤ x) (hh : 0 ≤ hlen) : ‖shortSum a s0 x hlen‖ ≤ hlen + 1 := by
  unfold shortSum
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun m _ => ha m)) ?_
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact card_shortWindow_le s0 hx hh

/-! ## §7 — THE PER-SCALE SUMMATION

The shape the M4-5 → M4-7 chain composes: a per-scale bound `B`, uniform over the cover,
becomes a total bound with the count made EXPLICIT (law #253 — no `O(log W)`).  Both
carriers are landed: the `Finset.sum` form (a uniform `B`) and the `sup'` form (the actual
per-scale maximum), since the freeze's (4.1) target is reached from either. -/

/-- `∑_{i<n} F i ≤ n·B` from a uniform per-index bound. -/
theorem sum_range_le_mul {n : ℕ} {F : ℕ → ℝ} {B : ℝ}
    (h : ∀ i ∈ Finset.range n, F i ≤ B) : ∑ i ∈ Finset.range n, F i ≤ (n : ℝ) * B := by
  have := Finset.sum_le_card_nsmul (Finset.range n) F B h
  simpa [nsmul_eq_mul] using this

/-- The `sup'` form: no uniform bound needed, the count multiplies the actual maximum. -/
theorem sum_range_le_mul_sup' {n : ℕ} (hn : 0 < n) (F : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, F i
      ≤ (n : ℝ) * (Finset.range n).sup' (Finset.nonempty_range_iff.mpr hn.ne') F :=
  sum_range_le_mul (fun _ hi => Finset.le_sup' F hi)

/-- **THE COVER'S SUMMATION, `Finset.sum` form.**  Per-block bound `B` ⟹ the whole surviving
range is `≤ (10·log W/log 2 + 2)·B`.  The count factor is in-statement and symbolic in `W`. -/
theorem dyadCover_total_le {S : Finset ℕ} {X W : ℝ} {f : ℕ → ℝ} {B : ℝ}
    (hX : 0 ≤ X) (hW : 1 ≤ W) (hB : 0 ≤ B) (hf : ∀ n ∈ S, 0 ≤ f n)
    (hpart : ∀ i < dyadCount W, ∑ n ∈ dyadPart S X i, f n ≤ B) :
    ∑ n ∈ S.filter (fun n : ℕ => X / W ^ (10 : ℕ) < (n : ℝ) ∧ (n : ℝ) ≤ X), f n
      ≤ (10 * Real.log W / Real.log 2 + 2) * B := by
  have hsum : ∑ i ∈ Finset.range (dyadIdx W), ∑ n ∈ dyadPart S X i, f n ≤ (dyadIdx W : ℝ) * B := by
    refine sum_range_le_mul (B := B) ?_
    intro i hi
    exact hpart i (lt_trans (Finset.mem_range.mp hi) (dyadIdx_lt_dyadCount W))
  have hcount : ((dyadIdx W : ℕ) : ℝ) ≤ 10 * Real.log W / Real.log 2 + 2 := by
    have h1 : ((dyadIdx W : ℕ) : ℝ) ≤ ((dyadCount W : ℕ) : ℝ) := by
      exact_mod_cast (dyadIdx_lt_dyadCount W).le
    exact le_trans h1 (dyadCount_le hW)
  exact le_trans (sum_dyadCover hX hW hf)
    (le_trans hsum (mul_le_mul_of_nonneg_right hcount hB))

/-- **THE COVER'S SUMMATION, `sup'` form.**  Same statement with the per-block maximum in
place of a supplied uniform bound. -/
theorem dyadCover_total_le_sup' {S : Finset ℕ} {X W : ℝ} {f : ℕ → ℝ}
    (hX : 0 ≤ X) (hW : 1 ≤ W) (hf : ∀ n ∈ S, 0 ≤ f n) (hIdx : 0 < dyadIdx W) :
    ∑ n ∈ S.filter (fun n : ℕ => X / W ^ (10 : ℕ) < (n : ℝ) ∧ (n : ℝ) ≤ X), f n
      ≤ (dyadIdx W : ℝ)
          * (Finset.range (dyadIdx W)).sup' (Finset.nonempty_range_iff.mpr hIdx.ne')
              (fun i => ∑ n ∈ dyadPart S X i, f n) :=
  le_trans (sum_dyadCover hX hW hf)
    (sum_range_le_mul_sup' hIdx (fun i => ∑ n ∈ dyadPart S X i, f n))

/-- **THE COVER'S SUMMATION AT THE CAMPAIGN'S `W`** — `W = (log H)^{12}`, the H-scale.  The
count is `≤ 174·loglog H + 2`; there is no `loglog X` anywhere in this bound. -/
theorem dyadCover_total_le_logPow {S : Finset ℕ} {X H : ℝ} {f : ℕ → ℝ} {B : ℝ}
    (hX : 0 ≤ X) (hH : 1 ≤ Real.log H) (hB : 0 ≤ B) (hf : ∀ n ∈ S, 0 ≤ f n)
    (hpart : ∀ i < dyadCount ((Real.log H) ^ (12 : ℕ)),
      ∑ n ∈ dyadPart S X i, f n ≤ B) :
    ∑ n ∈ S.filter (fun n : ℕ =>
        X / ((Real.log H) ^ (12 : ℕ)) ^ (10 : ℕ) < (n : ℝ) ∧ (n : ℝ) ≤ X), f n
      ≤ (174 * Real.log (Real.log H) + 2) * B := by
  have hW : (1 : ℝ) ≤ (Real.log H) ^ (12 : ℕ) := one_le_pow₀ hH
  have hsum : ∑ i ∈ Finset.range (dyadIdx ((Real.log H) ^ (12 : ℕ))),
      ∑ n ∈ dyadPart S X i, f n ≤ (dyadIdx ((Real.log H) ^ (12 : ℕ)) : ℝ) * B := by
    refine sum_range_le_mul (B := B) ?_
    intro i hi
    exact hpart i (lt_trans (Finset.mem_range.mp hi) (dyadIdx_lt_dyadCount _))
  have hcount : ((dyadIdx ((Real.log H) ^ (12 : ℕ)) : ℕ) : ℝ)
      ≤ 174 * Real.log (Real.log H) + 2 := by
    have h1 : ((dyadIdx ((Real.log H) ^ (12 : ℕ)) : ℕ) : ℝ)
        ≤ ((dyadCount ((Real.log H) ^ (12 : ℕ)) : ℕ) : ℝ) := by
      exact_mod_cast (dyadIdx_lt_dyadCount _).le
    exact le_trans h1 (dyadCount_logPow_le_numeral hH)
  exact le_trans (sum_dyadCover hX hW hf)
    (le_trans hsum (mul_le_mul_of_nonneg_right hcount hB))

end Salt.MR
