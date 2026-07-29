/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Door
import Salt.MR.SeamLemma14

/-!
# THE BRIDGE WAVE, B-4 — THE SUM→INTEGRAL BRIDGE (`M4BridgeIntegral`)

Source: `M4Close`'s ⟦THE FIVE OPEN BRIDGES⟧, item **4** — "the mean square lives on
`∫_X^{2X}·dx`, the door on a discrete harmonic sum.  The exact identity is available: for
`x ∈ [n, n+1)` the window `(x, x+H]` contains exactly `{n+1,…,n+H}`, so
`‖shortSum a s₀ x H‖` is constant on unit intervals and the discrete square-sum IS the
integral.  Landing it costs interval additivity + integrability of a piecewise-constant
integrand."

That is what this file does, and nothing else.  It is **pure plumbing**: no arithmetic
content, no constants, no sieve.  The two carriers it joins are

* the **mean square** (`ThmA2.thm_a2'_of_rows`, `M4MeanSq.m4_meansq_per_chi_gen`):
  `1/X * ∫ x in X..(2X), ‖((1/h : ℝ) : ℂ) * shortSum a s₀ x h‖ ^ 2` — Lebesgue on `[X, 2X]`;
* the **door** (`M4Close.M4SievedDoorSq`): `∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure x ω)`
  — the `1/n`-weighted, `Z`-normalised counting measure on `(x/ω, x]`.

## ⟦THE CONVENTION FINDING⟧ (the trap the brief named, resolved)

The unit cell must be **`Ico n (n+1)`** — left-closed, right-open — and this is *forced* by
`shortSum`'s half-open window `(x, x+H]`:

* `x < (m : ℝ) ↔ n < m` for `m : ℕ` needs `x` in `[n, n+1)`.  At the LEFT endpoint `x = n`
  exactly, `x < m` still rejects `m = n` (the window is open at the bottom), so the closed
  left end is *exactly right*; had the window been `[x, x+H)` the cell would have had to be
  `Ioc n (n+1)` instead.
* `(m : ℝ) ≤ x + H ↔ m ≤ n + H` needs `x < n+1` strictly.  At `x = n+1` the window has
  already slid to the next cell.

So the pairing is **`Ico` cells ↔ `Ioc` windows**, and it is exact — `shortSum_eq_inter_Ioc`
carries no error term at all.  The right endpoint `x = n+1` of the cell is the one point
where constancy fails; it is a single point, hence Lebesgue-null, which is why
`integral_unit_shortSum_sq` goes through `intervalIntegral.integral_congr_ae` rather than
`integral_congr` (the latter would ask for equality on `uIcc n (n+1)`, which is FALSE).

## ⟦THE ENDPOINT LEDGER⟧ (where the `±1` really lives)

`M4Door.card_shortWindow_band`'s `2/h` band is the **real-`x`** statement: a real window
`(x, x+h]` carries `h ± 1` lattice points.  At an **integer** `x = n` and an integer length
`H` the count is *exactly* `H` (`Nat.card_Ioc`), so the band collapses and the normalised
window sum obeys the clean `‖(1/H)·shortSum‖ ≤ 1` (`norm_shortSum_nat_sq_le_one`).

The `±1` therefore does **not** appear inside the window in this bridge.  It appears — and
only there — in the **outer** fit of the discrete block `(A, B]` into the real window
`[X, 2X]`, i.e. in whether `Ico (A+1) (B+1) ⊆ [X, 2X]`.  Two facts settle it:

* at the **door ladder** the fit is EXACT and unconditional: taking the block's own scale
  `X := X_{i+1} = doorLadder x H (i+1)`, `M4Door.doorLadder_fit` gives
  `X_i + H ≤ 2·X_{i+1}`, so `B + 1 ≤ B + H ≤ 2X` for every `H ≥ 1`, and `X ≤ A` is `rfl`.
  **There is no boundary loss on the ladder** (`sum_Ioc_absWindowSum_sq_div_le_ladder`);
* off the ladder, `sum_Ioc_shortSum_sq_le_meanSq_boundary` prices the overhang honestly:
  the leftover cells are counted (`(A' − (A+1)) + ((B+1) − B')`) and each is charged the
  trivial bound `Ctriv`.

## ⟦THE MEASURE EXCHANGE⟧ (the honest chain, per block)

```
   ∑_{n ∈ (A,B]} ‖absWindowSum c H n α‖² / n
 ≤ (∑_{n ∈ (A,B]} ‖absWindowSum c H n α‖²) / A            (M4Door.sum_div_Ioc_le: 1/n ≍ 1/A)
 = H² · (∑_{n ∈ [A+1,B+1)} ‖(1/H)·shortSum a s₀ n H‖²) / A      (the H² renormalisation)
 = H² · (∫ x in (A+1)..(B+1), ‖(1/H)·shortSum a s₀ x H‖²) / A   (§3, THE BRIDGE IDENTITY)
 ≤ H² · (∫ x in X..(2X), ‖(1/H)·shortSum a s₀ x H‖²) / A        (§3, monotone, nonneg)
 = H² · X · (1/X · ∫ …) / A  ≤  H² · MS                         (X ≤ A, and 1/X·∫ ≤ MS)
```

The `1/n ≍ 1/X` of the door and the `1/X` normaliser of `thm_a2'` **cancel exactly** at
`X = A`; the block therefore costs `H²·MS` and not a factor more.  Composing over the
`doorCount ω` blocks of the ladder (`M4Door.door_cover_sum_le`) and dividing by the door
normaliser `Z` (`M4Door.integral_logMeasure_le_div`) is `m4_bridge_door_sq_le`, whose shape
is `M4Close.M4SievedDoorSq`'s: `≤ Braw H · H²` with `Braw H = k·MS/Z + …`, and `k ≤ 3Z`
(`M4Door.door_count_le_three_mul_norm`) turns `k/Z` into the absolute `3`.

## What is CITED, never re-derived

`Lemma14.shortSum` (the carrier and its half-open convention), `M4Window.absWindowSum`,
`M4Door.sum_div_Ioc_le`, `M4Door.door_cover_sum_le`, `M4Door.integral_logMeasure_le_div`,
`M4Door.doorLadder_fit` / `doorLadder_step_le` / `doorLadder_floor`,
`intervalIntegral.sum_integral_adjacent_intervals_Ico` (the interval additivity the brief
names).  The measurability/boundedness route for the integrand is `Lemma14`'s own
(`shortSum_diff_sq_intervalIntegrable`'s), re-derived here at the SINGLE-`shortSum` shape
because `Lemma14`'s helpers are `private`.

## Contents

* §1 THE CONSTANCY LEMMA — `shortSum_eq_inter_Ioc`, `shortSum_const_unit`,
  `absWindowSum_eq_shortSum`, and the exact trivial bound at integer `x`.
* §2 PIECEWISE-CONSTANT INTEGRABILITY — `shortSum_sq_intervalIntegrable` (bounded +
  measurable; ~35 lines, no new measure theory).
* §3 THE BRIDGE IDENTITY — the unit-cell evaluation, the `Ico`-sum ↔ integral identity, and
  the monotone transfer into `[X, 2X]`.
* §4 THE ENDPOINT LEDGER — the honest boundary pricing off the ladder.
* §5 THE MEASURE EXCHANGE — the per-block harmonic bound, and its unconditional
  instantiation at the door ladder.
* §6 THE COMPOSED EXIT — `m4_bridge_door_sq_le`, at `M4SievedDoorSq`'s own shape.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE CONSTANCY LEMMA

For `x ∈ [n, n+1)` the real half-open window `(x, x+H]` is *exactly* the integer window
`(n, n+H]`.  Both directions of both inequalities are one cast each; see ⟦THE CONVENTION
FINDING⟧ for why `Ico` (not `Ioc`) is the forced cell shape. -/

/-- **THE WINDOW IS EXACTLY `Ioc n (n+H)` ON THE CELL `[n, n+1)`.**  The filter defining
`shortSum` collapses to an intersection with the integer window — no `±1`, no slack. -/
theorem shortSum_filter_eq_inter_Ioc (s0 : Finset ℕ) (H : ℕ) {n : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)) :
    s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + (H : ℝ))
      = s0 ∩ Finset.Ioc n (n + H) := by
  obtain ⟨hxl, hxr⟩ := hx
  ext m
  simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hm, h1, h2⟩
    refine ⟨hm, ?_, ?_⟩
    · have hR : (n : ℝ) < (m : ℝ) := lt_of_le_of_lt hxl h1
      exact_mod_cast hR
    · have hR : (m : ℝ) < ((n + H + 1 : ℕ) : ℝ) := by push_cast; linarith
      have hN : m < n + H + 1 := by exact_mod_cast hR
      omega
  · rintro ⟨hm, h1, h2⟩
    refine ⟨hm, ?_, ?_⟩
    · have hN : n + 1 ≤ m := h1
      have hR : ((n : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hN
      linarith
    · have hR : (m : ℝ) ≤ (n : ℝ) + (H : ℝ) := by exact_mod_cast h2
      linarith

/-- **THE CONSTANCY LEMMA (evaluated form).**  On the cell `[n, n+1)` the short-interval sum
is the integer window sum `∑_{m ∈ s₀ ∩ (n, n+H]} aₘ`.  This is the whole arithmetic content
of the bridge. -/
theorem shortSum_eq_inter_Ioc (a : ℕ → ℂ) (s0 : Finset ℕ) (H : ℕ) {n : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)) :
    shortSum a s0 x (H : ℝ) = ∑ m ∈ s0 ∩ Finset.Ioc n (n + H), a m := by
  rw [shortSum, shortSum_filter_eq_inter_Ioc s0 H hx]

/-- The cell's left endpoint is in the cell (`n ∈ [n, n+1)`) — the instance every consumer
below uses. -/
theorem mem_unit_cell (n : ℕ) : (n : ℝ) ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1) :=
  Set.left_mem_Ico.mpr (by linarith)

/-- **THE CONSTANCY LEMMA (transport form).**  `x ↦ shortSum a s₀ x H` is constant on each
cell `[n, n+1)`, with value the one at the integer left endpoint. -/
theorem shortSum_const_unit (a : ℕ → ℂ) (s0 : Finset ℕ) (H : ℕ) {n : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)) :
    shortSum a s0 x (H : ℝ) = shortSum a s0 (n : ℝ) (H : ℝ) := by
  rw [shortSum_eq_inter_Ioc a s0 H hx, shortSum_eq_inter_Ioc a s0 H (mem_unit_cell n)]

/-- **THE DOOR'S COEFFICIENT SEQUENCE**, read as a `shortSum` datum: `a(m) = c(m)·e(αm)`.
This is the only definition in the file, and it is a spelling, not an object. -/
def doorCoeffPhase (c : ℕ → ℂ) (α : ℝ) : ℕ → ℂ :=
  fun m => c m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((m : ℕ) : ℂ))

/-- **THE TWO CARRIERS AGREE.**  `absWindowSum c H n α = shortSum (c·e(α·)) s₀ n H`, provided
`s₀` misses no index at which `c` is nonzero inside the window.  (The corpus's `s₀` is
`seamS0 N X`, and its `a` vanishes off it — the hypothesis is exactly that support fact,
stated windowwise so no global support datum is needed.) -/
theorem absWindowSum_eq_shortSum (c : ℕ → ℂ) (s0 : Finset ℕ) (H n : ℕ) (α : ℝ)
    (hcov : ∀ m ∈ Finset.Ioc n (n + H), m ∉ s0 → c m = 0) :
    absWindowSum c H n α = shortSum (doorCoeffPhase c α) s0 (n : ℝ) (H : ℝ) := by
  rw [shortSum_eq_inter_Ioc _ s0 H (mem_unit_cell n), absWindowSum]
  refine (Finset.sum_subset Finset.inter_subset_right ?_).symm
  intro m hm hnot
  have hns : m ∉ s0 := fun hs => hnot (Finset.mem_inter.mpr ⟨hs, hm⟩)
  rw [hcov m hm hns, zero_mul]

/-- **THE ENDPOINT BAND COLLAPSES AT INTEGER `x`.**  `M4Door.card_shortWindow_band`'s `2/h`
band is a real-`x` statement; at an integer `x = n` and an integer length `H` the window
`(n, n+H]` carries *exactly* `H` lattice points, so the normalised sum obeys the clean
`‖(1/H)·shortSum‖² ≤ 1`.  This is the trivial bound the endpoint ledger of §4 charges. -/
theorem norm_shortSum_nat_sq_le_one {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (s0 : Finset ℕ)
    {H : ℕ} (hH : 0 < H) (n : ℕ) :
    ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 (n : ℝ) (H : ℝ)‖ ^ 2 ≤ 1 := by
  have hH0 : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hcard : ‖shortSum a s0 (n : ℝ) (H : ℝ)‖ ≤ (H : ℝ) := by
    rw [shortSum_eq_inter_Ioc a s0 H (mem_unit_cell n)]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 (fun m _ => ha m)) ?_
    rw [nsmul_eq_mul, mul_one]
    have hsub : s0 ∩ Finset.Ioc n (n + H) ⊆ Finset.Ioc n (n + H) := Finset.inter_subset_right
    have := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at this
    have hle : (s0 ∩ Finset.Ioc n (n + H)).card ≤ H := by omega
    exact_mod_cast hle
  have hnorm : ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 (n : ℝ) (H : ℝ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc 1 / (H : ℝ) * ‖shortSum a s0 (n : ℝ) (H : ℝ)‖
        ≤ 1 / (H : ℝ) * (H : ℝ) := by
          exact mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = 1 := by field_simp
  nlinarith [norm_nonneg (((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 (n : ℝ) (H : ℝ))]

/-! ## §2 — PIECEWISE-CONSTANT INTEGRABILITY

The lightest route, and the corpus's own: the integrand is **measurable** (a finite sum of
indicators of the intervals `[m − h, m)`) and **uniformly bounded** (by
`(|1/h|·∑_{m ∈ s₀}‖aₘ‖)²`), and a bounded measurable function is interval-integrable on
every finite interval.  This is byte-for-byte `Lemma14`'s route for
`shortSum_diff_sq_intervalIntegrable`, re-derived at the single-`shortSum` shape because
`Lemma14`'s three helpers are `private`.  **No step-function machinery, no simple functions,
no new measure theory.** -/

/-- `x ↦ shortSum a s₀ x h` is measurable: a finite sum of indicators of `[m − h, m)`. -/
private lemma shortSum_meas (a : ℕ → ℂ) (s0 : Finset ℕ) (hlen : ℝ) :
    Measurable (fun x : ℝ => shortSum a s0 x hlen) := by
  have hset : ∀ m : ℕ, {x : ℝ | x < (m : ℝ) ∧ (m : ℝ) ≤ x + hlen}
      = Set.Ico ((m : ℝ) - hlen) (m : ℝ) := by
    intro m
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  simp only [shortSum, Finset.sum_filter]
  refine Finset.measurable_sum _ (fun m _ => ?_)
  exact Measurable.ite (by rw [hset m]; exact measurableSet_Ico) measurable_const
    measurable_const

/-- The trivial uniform bound `‖shortSum a s₀ x h‖ ≤ ∑_{m ∈ s₀} ‖aₘ‖`. -/
private lemma shortSum_bound (a : ℕ → ℂ) (s0 : Finset ℕ) (x hlen : ℝ) :
    ‖shortSum a s0 x hlen‖ ≤ ∑ m ∈ s0, ‖a m‖ :=
  le_trans (norm_sum_le _ _)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => norm_nonneg _))

/-- A bounded measurable real function is interval-integrable (`Lemma14`'s helper). -/
private lemma bdd_meas_intervalIntegrable_bridge {f : ℝ → ℝ} {C : ℝ} (p q : ℝ)
    (hm : Measurable f) (hb : ∀ x, ‖f x‖ ≤ C) : IntervalIntegrable f volume p q :=
  ⟨MeasureTheory.Integrable.mono'
      (_root_.intervalIntegrable_const (μ := volume) (c := C) (a := p) (b := q)).1
      hm.aestronglyMeasurable (Filter.Eventually.of_forall hb),
   MeasureTheory.Integrable.mono'
      (_root_.intervalIntegrable_const (μ := volume) (c := C) (a := p) (b := q)).2
      hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)⟩

/-- **THE INTEGRABILITY OF THE MEAN-SQUARE INTEGRAND**, on every interval.  This is the
side condition the brief flagged; it costs one measurability lemma and one uniform bound,
which is why the piecewise-constant structure never has to be exhibited to `MeasureTheory`.
(The carrier is exactly `thm_a2'_of_rows`' — `‖((1/h : ℝ) : ℂ) * shortSum a s₀ x h‖ ^ 2`.) -/
theorem shortSum_sq_intervalIntegrable (a : ℕ → ℂ) (s0 : Finset ℕ) (hlen p q : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => ‖((1 / hlen : ℝ) : ℂ) * shortSum a s0 x hlen‖ ^ 2) volume p q := by
  refine bdd_meas_intervalIntegrable_bridge (C := (|1 / hlen| * ∑ m ∈ s0, ‖a m‖) ^ 2) p q
    (((shortSum_meas a s0 hlen).const_mul _).norm.pow_const 2) (fun x => ?_)
  have hsum0 : (0 : ℝ) ≤ ∑ m ∈ s0, ‖a m‖ :=
    Finset.sum_nonneg (fun m _ => norm_nonneg _)
  have hd : ‖((1 / hlen : ℝ) : ℂ) * shortSum a s0 x hlen‖
      ≤ |1 / hlen| * ∑ m ∈ s0, ‖a m‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (shortSum_bound a s0 x hlen) (abs_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h0 : (0 : ℝ) ≤ ‖((1 / hlen : ℝ) : ℂ) * shortSum a s0 x hlen‖ := norm_nonneg _
  nlinarith [mul_nonneg (abs_nonneg (1 / hlen)) hsum0]

/-! ## §3 — THE BRIDGE IDENTITY

Unit-cell evaluation, then interval additivity over the cells (`Ico A B` ↔ `[A, B]`), then
the monotone transfer into the mean square's own window `[X, 2X]`. -/

/-- **THE UNIT-CELL EVALUATION.**  `∫_n^{n+1} ‖(1/H)·shortSum a s₀ x H‖² dx` is the value at
`x = n`.  Proved by `integral_congr_ae`: the integrand agrees with the constant on all of
`Ι n (n+1) = (n, n+1]` except the single point `n+1` (⟦THE CONVENTION FINDING⟧), which is
Lebesgue-null. -/
theorem integral_unit_shortSum_sq (a : ℕ → ℂ) (s0 : Finset ℕ) (H n : ℕ) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1),
        ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 x (H : ℝ)‖ ^ 2)
      = ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 (n : ℝ) (H : ℝ)‖ ^ 2 := by
  have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hne : ∀ᵐ x : ℝ, x ≠ (n : ℝ) + 1 := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : ℝ | ¬ x ≠ (n : ℝ) + 1} = {((n : ℝ) + 1)} := by
      ext x; simp
    rw [hset]
    exact measure_singleton _
  have hae : ∀ᵐ x : ℝ, x ∈ Set.uIoc (n : ℝ) ((n : ℝ) + 1) →
      ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 x (H : ℝ)‖ ^ 2
        = ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 (n : ℝ) (H : ℝ)‖ ^ 2 := by
    filter_upwards [hne] with x hx hmem
    rw [Set.uIoc_of_le hle, Set.mem_Ioc] at hmem
    rw [shortSum_const_unit a s0 H ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hx⟩]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const]
  simp

/-- **THE BRIDGE IDENTITY.**  The discrete square-sum over the cells `[A, B) ⊆ ℕ` IS the
Lebesgue integral over `[A, B] ⊆ ℝ`.  Interval additivity
(`intervalIntegral.sum_integral_adjacent_intervals_Ico`) plus §2's integrability plus the
unit-cell evaluation — the brief's exact recipe. -/
theorem sum_Ico_shortSum_sq_eq_integral (a : ℕ → ℂ) (s0 : Finset ℕ) (H : ℕ) {A B : ℕ}
    (hAB : A ≤ B) :
    ∑ n ∈ Finset.Ico A B, ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 (n : ℝ) (H : ℝ)‖ ^ 2
      = ∫ x in (A : ℝ)..(B : ℝ),
          ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 x (H : ℝ)‖ ^ 2 := by
  have hcell : ∀ k : ℕ,
      ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 (k : ℝ) (H : ℝ)‖ ^ 2
        = ∫ x in ((k : ℕ) : ℝ)..(((k + 1 : ℕ)) : ℝ),
            ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 x (H : ℝ)‖ ^ 2 := by
    intro k
    have hc : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hc, integral_unit_shortSum_sq]
  calc ∑ n ∈ Finset.Ico A B,
          ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 (n : ℝ) (H : ℝ)‖ ^ 2
      = ∑ k ∈ Finset.Ico A B, ∫ x in ((k : ℕ) : ℝ)..(((k + 1 : ℕ)) : ℝ),
          ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 x (H : ℝ)‖ ^ 2 :=
        Finset.sum_congr rfl (fun k _ => hcell k)
    _ = ∫ x in (A : ℝ)..(B : ℝ),
          ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 x (H : ℝ)‖ ^ 2 :=
        intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun k : ℕ => (k : ℝ)) hAB
          (fun k _ => shortSum_sq_intervalIntegrable a s0 (H : ℝ) _ _)

/-- **THE MONOTONE TRANSFER.**  The integrand is `≥ 0`, so enlarging the interval only
increases the integral.  (Interval additivity again; §2 supplies every side condition.  Note
`p ≤ q` is not needed: for `q < p` the left side is `≤ 0`.) -/
theorem integral_shortSum_sq_mono (a : ℕ → ℂ) (s0 : Finset ℕ) (hlen : ℝ) {p q r s : ℝ}
    (hrp : r ≤ p) (hqs : q ≤ s) :
    (∫ x in p..q, ‖((1 / hlen : ℝ) : ℂ) * shortSum a s0 x hlen‖ ^ 2)
      ≤ ∫ x in r..s, ‖((1 / hlen : ℝ) : ℂ) * shortSum a s0 x hlen‖ ^ 2 := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (shortSum_sq_intervalIntegrable a s0 hlen r p) (shortSum_sq_intervalIntegrable a s0 hlen p s)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (shortSum_sq_intervalIntegrable a s0 hlen p q) (shortSum_sq_intervalIntegrable a s0 hlen q s)
  have hrp0 : (0 : ℝ) ≤ ∫ x in r..p, ‖((1 / hlen : ℝ) : ℂ) * shortSum a s0 x hlen‖ ^ 2 :=
    intervalIntegral.integral_nonneg hrp (fun u _ => by positivity)
  have hqs0 : (0 : ℝ) ≤ ∫ x in q..s, ‖((1 / hlen : ℝ) : ℂ) * shortSum a s0 x hlen‖ ^ 2 :=
    intervalIntegral.integral_nonneg hqs (fun u _ => by positivity)
  linarith

/-- `Ioc A B = Ico (A+1) (B+1)` on `ℕ` — the index shift that carries the door's half-open
blocks onto the bridge's cells. -/
theorem Ioc_eq_Ico_succ (A B : ℕ) : Finset.Ioc A B = Finset.Ico (A + 1) (B + 1) := by
  ext m
  simp only [Finset.mem_Ioc, Finset.mem_Ico]
  omega

/-- **THE MEAN SQUARE IS NONNEGATIVE** — used to spend `X ≤ A` in §5. -/
theorem meanSq_nonneg (a : ℕ → ℂ) (s0 : Finset ℕ) (hlen : ℝ) {X : ℝ} (hX : 0 < X) :
    (0 : ℝ) ≤ 1 / X * ∫ x in X..(2 * X),
        ‖((1 / hlen : ℝ) : ℂ) * shortSum a s0 x hlen‖ ^ 2 := by
  have h : (0 : ℝ) ≤ ∫ x in X..(2 * X), ‖((1 / hlen : ℝ) : ℂ) * shortSum a s0 x hlen‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => by positivity)
  positivity

/-- **THE BLOCK, INSIDE THE WINDOW.**  A discrete block `(A, B]` whose cells fit inside
`[X, 2X]` costs `X · MS` and no more.  The hypotheses `X ≤ A` and `B + 1 ≤ 2X` are exactly
"the cells `[A+1, B+1)` lie in `[X, 2X]`". -/
theorem sum_Ioc_shortSum_sq_le_meanSq (a : ℕ → ℂ) (s0 : Finset ℕ) (H : ℕ) {A B : ℕ}
    {X MS : ℝ} (hAB : A ≤ B) (hX : 0 < X) (hXA : X ≤ (A : ℝ)) (hB : (B : ℝ) + 1 ≤ 2 * X)
    (hMS : 1 / X * (∫ x in X..(2 * X),
        ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 x (H : ℝ)‖ ^ 2) ≤ MS) :
    ∑ n ∈ Finset.Ioc A B,
        ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 (n : ℝ) (H : ℝ)‖ ^ 2 ≤ X * MS := by
  have hAB' : A + 1 ≤ B + 1 := by omega
  have hlow : X ≤ ((A + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hhigh : ((B + 1 : ℕ) : ℝ) ≤ 2 * X := by push_cast; linarith
  have hid := sum_Ico_shortSum_sq_eq_integral a s0 H hAB'
  have hmono := integral_shortSum_sq_mono a s0 (H : ℝ) hlow hhigh
  have hMSX : (∫ x in X..(2 * X),
      ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 x (H : ℝ)‖ ^ 2) ≤ X * MS := by
    have := mul_le_mul_of_nonneg_left hMS hX.le
    rw [← mul_assoc] at this
    rwa [mul_one_div_cancel hX.ne', one_mul] at this
  rw [Ioc_eq_Ico_succ, hid]
  linarith

/-! ## §4 — THE ENDPOINT LEDGER

Off the ladder (§5 shows the ladder itself has *no* overhang) the block `(A, B]` may stick
out of `[X, 2X]` at either end.  The overhang is counted exactly and priced at the trivial
bound `norm_shortSum_nat_sq_le_one`. -/

/-- **THE OVERHANG SPLIT**, at a general nonnegative summand: peeling a core `[A', B')` out
of `[A, B)` costs the leftover cell count times the uniform bound. -/
theorem sum_Ico_le_core_add_boundary {v : ℕ → ℝ} {Ctriv : ℝ} {A B A' B' : ℕ}
    (hAA' : A ≤ A') (hA'B' : A' ≤ B') (hB'B : B' ≤ B)
    (htriv : ∀ n : ℕ, v n ≤ Ctriv) :
    ∑ n ∈ Finset.Ico A B, v n
      ≤ (∑ n ∈ Finset.Ico A' B', v n) + (((A' - A) + (B - B') : ℕ) : ℝ) * Ctriv := by
  have hA'B : A' ≤ B := le_trans hA'B' hB'B
  have hsplit1 := Finset.sum_Ico_consecutive v hAA' hA'B
  have hsplit2 := Finset.sum_Ico_consecutive v hA'B' hB'B
  have hlo : ∑ n ∈ Finset.Ico A A', v n ≤ ((A' - A : ℕ) : ℝ) * Ctriv := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ Ctriv (fun n _ => htriv n)) ?_
    rw [Nat.card_Ico, nsmul_eq_mul]
  have hhi : ∑ n ∈ Finset.Ico B' B, v n ≤ ((B - B' : ℕ) : ℝ) * Ctriv := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ Ctriv (fun n _ => htriv n)) ?_
    rw [Nat.card_Ico, nsmul_eq_mul]
  have hcast : (((A' - A) + (B - B') : ℕ) : ℝ) = ((A' - A : ℕ) : ℝ) + ((B - B' : ℕ) : ℝ) := by
    push_cast; ring
  rw [hcast]
  linarith

/-- **THE BLOCK, OVERHANGING THE WINDOW — the honest ledger.**  The core `[A', B')` is
charged to the mean square; the `(A' − (A+1)) + ((B+1) − B')` leftover cells are charged the
trivial bound.  At `A' = A+1`, `B' = B+1` (the ladder's exact fit, §5) the ledger is `0`. -/
theorem sum_Ioc_shortSum_sq_le_meanSq_boundary {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1)
    (s0 : Finset ℕ) {H : ℕ} (hH : 0 < H) {A B A' B' : ℕ} {X MS : ℝ}
    (hAA' : A + 1 ≤ A') (hA'B' : A' ≤ B') (hB'B : B' ≤ B + 1)
    (hX : 0 < X) (hXA' : X ≤ (A' : ℝ)) (hB' : (B' : ℝ) ≤ 2 * X)
    (hMS : 1 / X * (∫ x in X..(2 * X),
        ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 x (H : ℝ)‖ ^ 2) ≤ MS) :
    ∑ n ∈ Finset.Ioc A B,
        ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 (n : ℝ) (H : ℝ)‖ ^ 2
      ≤ X * MS + (((A' - (A + 1)) + ((B + 1) - B') : ℕ) : ℝ) := by
  have hcore : ∑ n ∈ Finset.Ico A' B',
      ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 (n : ℝ) (H : ℝ)‖ ^ 2 ≤ X * MS := by
    have hid := sum_Ico_shortSum_sq_eq_integral a s0 H hA'B'
    have hmono := integral_shortSum_sq_mono a s0 (H : ℝ) hXA' hB'
    have hMSX : (∫ x in X..(2 * X),
        ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 x (H : ℝ)‖ ^ 2) ≤ X * MS := by
      have := mul_le_mul_of_nonneg_left hMS hX.le
      rw [← mul_assoc] at this
      rwa [mul_one_div_cancel hX.ne', one_mul] at this
    rw [hid]; linarith
  have hledger := sum_Ico_le_core_add_boundary
    (v := fun n : ℕ => ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum a s0 (n : ℝ) (H : ℝ)‖ ^ 2)
    (Ctriv := 1) hAA' hA'B' hB'B (norm_shortSum_nat_sq_le_one ha s0 hH)
  rw [Ioc_eq_Ico_succ]
  have hmul : (((A' - (A + 1)) + ((B + 1) - B') : ℕ) : ℝ) * 1
      = (((A' - (A + 1)) + ((B + 1) - B') : ℕ) : ℝ) := by ring
  rw [hmul] at hledger
  linarith

/-! ## §5 — THE MEASURE EXCHANGE (the per-block lemma)

`logMeasure`'s `1/n` weight against Lebesgue's `dx`: on a block the weight is comparable to
`1/A` (`M4Door.sum_div_Ioc_le`), and `thm_a2'`'s normaliser is `1/X`.  At `X = A` — which is
exactly what the door ladder delivers — they **cancel**, and the block costs `H²·MS`. -/

/-- **THE PER-BLOCK HARMONIC BOUND** — the supplier `M4SievedDoorSq` composes over the
`doorLadder`.  Every hypothesis is either a fit (`X ≤ A`, `B + H ≤ 2X`) or the mean square
itself; the conclusion is the door's own weighted summand. -/
theorem sum_Ioc_absWindowSum_sq_div_le (c : ℕ → ℂ) (s0 : Finset ℕ) (α : ℝ)
    {H A B : ℕ} {X MS : ℝ} (hH : 0 < H) (hAB : A ≤ B) (hX : 0 < X) (hXA : X ≤ (A : ℝ))
    (hB : (B : ℝ) + (H : ℝ) ≤ 2 * X)
    (hcov : ∀ n ∈ Finset.Ioc A B, ∀ m ∈ Finset.Ioc n (n + H), m ∉ s0 → c m = 0)
    (hMS : 1 / X * (∫ x in X..(2 * X),
        ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum (doorCoeffPhase c α) s0 x (H : ℝ)‖ ^ 2) ≤ MS) :
    ∑ n ∈ Finset.Ioc A B, ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ) ≤ (H : ℝ) ^ 2 * MS := by
  have hH0 : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hA0 : (0 : ℝ) < (A : ℝ) := lt_of_lt_of_le hX hXA
  have hMS0 : (0 : ℝ) ≤ MS :=
    le_trans (meanSq_nonneg (doorCoeffPhase c α) s0 (H : ℝ) hX) hMS
  -- ⟦STEP 1⟧ the two carriers agree, and the `H²` renormalisation
  have hval : ∀ n ∈ Finset.Ioc A B, ‖absWindowSum c H n α‖ ^ 2
      = (H : ℝ) ^ 2
        * ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum (doorCoeffPhase c α) s0 (n : ℝ) (H : ℝ)‖ ^ 2 := by
    intro n hn
    rw [absWindowSum_eq_shortSum c s0 H n α (hcov n hn), norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (H : ℝ))]
    field_simp
  -- ⟦STEP 2⟧ spend the harmonic weight against the block bottom
  have hstep2 : ∑ n ∈ Finset.Ioc A B, ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ)
      ≤ (∑ n ∈ Finset.Ioc A B, ‖absWindowSum c H n α‖ ^ 2) / (A : ℝ) :=
    sum_div_Ioc_le hA0 (fun n _ => by positivity)
  -- ⟦STEP 3⟧ the bridge, on the renormalised summand
  have hstep3 : ∑ n ∈ Finset.Ioc A B, ‖absWindowSum c H n α‖ ^ 2
      ≤ (H : ℝ) ^ 2 * (X * MS) := by
    rw [Finset.sum_congr rfl hval, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine sum_Ioc_shortSum_sq_le_meanSq _ s0 H hAB hX hXA ?_ hMS
    have h1H : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    linarith
  -- ⟦STEP 4⟧ `X ≤ A` closes the exchange
  have hstep4 : (H : ℝ) ^ 2 * (X * MS) / (A : ℝ) ≤ (H : ℝ) ^ 2 * MS := by
    rw [div_le_iff₀ hA0]
    have hle : (H : ℝ) ^ 2 * MS * X ≤ (H : ℝ) ^ 2 * MS * (A : ℝ) :=
      mul_le_mul_of_nonneg_left hXA (by positivity)
    nlinarith
  have hdiv : (∑ n ∈ Finset.Ioc A B, ‖absWindowSum c H n α‖ ^ 2) / (A : ℝ)
      ≤ (H : ℝ) ^ 2 * (X * MS) / (A : ℝ) := by
    exact div_le_div_of_nonneg_right hstep3 hA0.le
  linarith

/-- **THE LADDER FIT IS UNCONDITIONAL.**  At the block's own scale `X := X_{i+1}` the two
fit hypotheses of `sum_Ioc_absWindowSum_sq_div_le` are `M4Door.doorLadder_fit` and `rfl` —
so the door ladder incurs **no boundary loss at all** (⟦THE ENDPOINT LEDGER⟧). -/
theorem sum_Ioc_absWindowSum_sq_div_le_ladder (c : ℕ → ℂ) (s0 : Finset ℕ) (α : ℝ)
    {x H i : ℕ} {MS : ℝ} (hH : 0 < H) (hxH : H + 1 ≤ x)
    (hcov : ∀ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i),
      ∀ m ∈ Finset.Ioc n (n + H), m ∉ s0 → c m = 0)
    (hMS : 1 / ((doorLadder x H (i + 1) : ℕ) : ℝ)
        * (∫ y in ((doorLadder x H (i + 1) : ℕ) : ℝ)..(2 * ((doorLadder x H (i + 1) : ℕ) : ℝ)),
            ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum (doorCoeffPhase c α) s0 y (H : ℝ)‖ ^ 2)
      ≤ MS) :
    ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i),
        ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ) ≤ (H : ℝ) ^ 2 * MS := by
  have hfloor := doorLadder_floor (x := x) (H := H) hxH (i + 1)
  have hXpos : (0 : ℝ) < ((doorLadder x H (i + 1) : ℕ) : ℝ) := by
    have : 0 < doorLadder x H (i + 1) := by omega
    exact_mod_cast this
  have hfit : doorLadder x H i + H ≤ 2 * doorLadder x H (i + 1) := doorLadder_fit x H i
  have hfitR : ((doorLadder x H i : ℕ) : ℝ) + (H : ℝ)
      ≤ 2 * ((doorLadder x H (i + 1) : ℕ) : ℝ) := by exact_mod_cast hfit
  exact sum_Ioc_absWindowSum_sq_div_le c s0 α hH (doorLadder_step_le hxH i) hXpos le_rfl
    hfitR hcov hMS

/-! ## §6 — THE COMPOSED EXIT

Cover the door window by the ladder (`M4Door.door_cover_sum_le`), then divide by the door
normaliser (`M4Door.integral_logMeasure_le_div`).  The shape is `M4Close.M4SievedDoorSq`'s:
`∫ ‖absWindowSum‖² ∂logMeasure ≤ Braw H · H²`. -/

/-- **`m4_bridge_door_sq_le` — THE BRIDGE'S EXIT.**  The per-block bound of §5, composed over
the door ladder and normalised.  This is the shape `M4Close.M4SievedDoorSq` reads: with
`k ≤ 3Z` (`M4Door.door_count_le_three_mul_norm`) the first term is `3·H²·MS`, and the second
is the ladder's geometric endpoint sum, already present in `m4_door_sieve_mass`. -/
theorem m4_bridge_door_sq_le {x H ω k : ℕ} {c : ℕ → ℂ} {α MS : ℝ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hxH : H + 1 ≤ x)
    (hreach : doorLadder x H k ≤ x / ω) (hpow : 2 ^ (k + 1) ≤ x)
    (hblk : ∀ i < k, ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i),
        ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ) ≤ (H : ℝ) ^ 2 * MS) :
    (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure x ω))
      ≤ ((k : ℝ) * ((H : ℝ) ^ 2 * MS) + 4 * 2 ^ k * (H : ℝ) / (x : ℝ))
          / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
  have hf0 : ∀ n : ℕ, (0 : ℝ) ≤ ‖absWindowSum c H n α‖ ^ 2 * (n : ℝ)⁻¹ := by
    intro n; positivity
  have hblk' : ∀ i < k, ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i),
      ‖absWindowSum c H n α‖ ^ 2 * (n : ℝ)⁻¹
      ≤ (H : ℝ) ^ 2 * MS + (H : ℝ) / ((doorLadder x H (i + 1) : ℕ) : ℝ) := by
    intro i hi
    have hnn : (0 : ℝ) ≤ (H : ℝ) / ((doorLadder x H (i + 1) : ℕ) : ℝ) := by positivity
    have h := hblk i hi
    simp only [div_eq_mul_inv] at h
    linarith
  have hcover := door_cover_sum_le (x := x) (H := H) (ω := ω) (k := k)
    (f := fun n : ℕ => ‖absWindowSum c H n α‖ ^ 2 * (n : ℝ)⁻¹)
    (P := (H : ℝ) ^ 2 * MS) hf0 hxH hreach hpow hblk'
  exact integral_logMeasure_le_div (door_norm_pos hx hω) hcover

/-! ## §7 — THE CONSUMER'S TWO FREE HYPOTHESES (the anti-vacuity duty)

M4-1's lesson (`door_window_not_one_block`) is that a fit hypothesis may be kernel-true and
consumable by nobody.  Both non-arithmetic hypotheses of §5–§6 are therefore *discharged*
here rather than left standing: the coverage datum `hcov` is free at the corpus's own `s₀`,
and the exit's ladder gates are inhabited at explicit numerals. -/

/-- **THE COVERAGE HYPOTHESIS IS FREE AT THE SEAM DATUM.**  `seamS0 N X` contains every index
of the block's short windows as soon as the block sits inside `(X, N]` — so `hcov` of
`sum_Ioc_absWindowSum_sq_div_le` is discharged, not assumed, at the `s₀` the mean-square
tower actually carries (`ThmA2.thm_a2'_of_rows`' `seamS0 N X`). -/
theorem mem_seamS0_of_block_window {N A B H : ℕ} {X : ℝ} (hXA : X ≤ (A : ℝ))
    (hBN : B + H ≤ N) {n : ℕ} (hn : n ∈ Finset.Ioc A B) {m : ℕ}
    (hm : m ∈ Finset.Ioc n (n + H)) : m ∈ seamS0 N X := by
  rw [Finset.mem_Ioc] at hn hm
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  have hAm : (A : ℝ) < (m : ℝ) := by
    have : A < m := by omega
    exact_mod_cast this
  linarith

/-- The same, in the exact shape `sum_Ioc_absWindowSum_sq_div_le`'s `hcov` slot asks for. -/
theorem hcov_of_seamS0 (c : ℕ → ℂ) {N A B H : ℕ} {X : ℝ} (hXA : X ≤ (A : ℝ))
    (hBN : B + H ≤ N) :
    ∀ n ∈ Finset.Ioc A B, ∀ m ∈ Finset.Ioc n (n + H), m ∉ seamS0 N X → c m = 0 :=
  fun _ hn _ hm hns => absurd (mem_seamS0_of_block_window hXA hBN hn hm) hns

/-- **THE EXIT'S LADDER GATES ARE INHABITED** — a concrete witness for
`m4_bridge_door_sq_le`'s four arithmetic gates at `(x, ω, H, k) = (64, 2, 1, 2)`.  (The
general witness is `M4Door.doorCount_gates` at `k := doorCount ω`; this one is the
kernel-checked existence proof that the gate list is not empty.) -/
theorem m4_bridge_door_gates_witness :
    2 ≤ 64 ∧ 2 ≤ 2 ∧ 1 + 1 ≤ 64 ∧ doorLadder 64 1 2 ≤ 64 / 2 ∧ 2 ^ (2 + 1) ≤ 64 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, by norm_num⟩
  simp only [doorLadder_succ, doorLadder_zero]
  norm_num

end Salt.MR
