/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Close

/-!
# BRIDGE 5 — THE HARMONIC-WEIGHTED COVER ASSEMBLY (`M4BridgeCover`)

Source: `M4Close`'s module header, ⟦THE FIVE OPEN BRIDGES⟧ **#5** — "the outer dyadic cover
at the door: `M4Dyadic.dyadCover_total_le(_logPow)` is landed for a `Finset` cover; the
bridge is the harmonic weight `1/n ≍ 1/X′` on a block meeting `logMeasure`'s normaliser `Z`."

This file is the **final composition layer** of the M4 door road: it turns a *per-block*
mean-square bound — the shape the residue/Abel/dilation/sum→integral chain (bridges 1–4)
natively delivers, one dyadic-ish block at a time — into the *door-integrated* `L²` bound
that is `M4Close.M4SievedDoorSq`, the wave's one open socket.

## THE ASSEMBLY, in one display

```
  ∑_{n ∈ (X_{i+1}, X_i]} ‖W(n)‖²  ≤  P·X_{i+1}  (+ E)         (bridges 1–4, PER BLOCK)
    ⟹ ∑_{n ∈ (X_{i+1}, X_i]} ‖W(n)‖²/n  ≤  P (+ E/X_{i+1})    (§1, THE WEIGHT EXCHANGE)
    ⟹ ∑_{n ∈ (x/ω, x]} ‖W(n)‖²/n  ≤  k·P + 4·2^k·E/x          (§2, THE LADDER SUM)
    ⟹ ∫ ‖W‖² dμ  ≤  (k/Z)·P + …  ≤  3·P + 4·2^k·E/x           (§3, THE ABSORPTION)
    ⟹ M4SievedDoorSq R M (3·B_blk)                             (§4, THE EXIT)
```

with `W(n) := absWindowSum (1_𝒮·λ) H n α` and `P := B_blk(H)·H²`.

## ⟦IT SPEAKS `doorLadder`, NOT `dyadScale`⟧ (the overhang, respected)

M4-8's ⟦OVERHANG FINDING⟧ is that an *exactly dyadic* cover of the door window cannot feed
the sieve gates: `m4_sieve_block_mass`'s window is `(a, b+H]`, so `b = 2a` reads `H ≤ 0`.
This bridge therefore covers with **`M4Door.doorLadder`** — `X_0 = x`,
`X_{i+1} = (X_i + H + 1)/2` — exactly the ladder `m4_door_glue` already eats, so the sieve
leg and the mean-square leg see the SAME blocks and the SAME count `k`.  Nothing here is
stated at `M4Dyadic.dyadScale`.

The ladder is still dyadic where it matters: `doorLadder_fit` gives `X_i ≤ 2·X_{i+1}`
(§1's `doorLadder_top_le_two_mul`), so the harmonic weight's block comparison
`1/X_i ≤ 1/n ≤ 1/X_{i+1}` is **two-sided within a factor 2** — that is the whole content of
choosing a dyadic-scale cover, and `block_weight_exchange_tight` states it.

## ⟦`Z`'S TWO ROLES, AND THE SINGLE PAYMENT⟧ (the trap, respected)

`Z = ∑_{n ∈ (x/ω,x]} 1/n` is both `logMeasure`'s normaliser and the `log ω` payer for the
cover's block count `k ≍ log ω/log 2`.  M4-8's §4 (`door_count_le_three_mul_norm`,
`door_mass_normalised_le`) performed that cancellation ONCE for the **sieve mass**, and the
price it paid there is the `M`-gate rescale `8C/δ ↦ 24C/δ` — a rescale this file does not
touch and does not repeat.

Here `Z` pays again, but for a **different term** (the mean square, not the sieve mass) and
in a **different currency**: no `δ`, no `M`-gate, just the absolute factor `3` in front of
the grade, `B_blk ↦ 3·B_blk`.  §3's `door_weight_absorb` is literally
`M4Door.door_mass_normalised_le` re-instantiated (`Hr := 1`, `δ := 12·P`), so the arithmetic
of the absorption exists in exactly one place in the corpus.  The factor `3` is then absorbed
by the grade gate: `m4_gradeGate_of_block_pricing` asks `3·B_blk H ≤ m4Saving H`, and the
quality demand's `W^{−5/2}` saving swallows an absolute constant without noticing.

## ⟦THE FOUR LOG SCALES⟧ — which one this file is about

M4-8 pinned four (`log H`, `log X`, `log x`, `log ω`).  This file touches **`log ω` only**,
and only through the two M4-8 lemmas it cites (`door_norm_ge`, `door_count_le_three_mul_norm`).
`W = (log H)^{12}` is never written here; the `H`-scale enters only as the window length
inside `absWindowSum` and as the `H²` of the mean square's own normalisation.

## ⟦`ℕ`-DIVISION AT THE LADDER STEPS⟧

Every block endpoint is `doorLadder R.x H i : ℕ`, whose `+1` rounding-up is load-bearing
(`doorLadder_fit` is unconditional *because* of it).  No `⌊·⌋` is introduced; the only
`ℕ`-division is `doorLadder`'s own and `x / ω` (the door window's bottom), both consumed as
given.  `doorLadder_pos` (§1) is the one arithmetic fact this file needs from the rounding:
`X_i ≥ H + 1 > 0`, so the block comparison never divides by zero.

## ⟦THE JOIN⟧ — landed, not deferred

Because `M4Close.m4_door_contradiction_of_live` carries `M4SievedDoorSq` as a *hypothesis*,
§4's `m4_cover_assembly` composes with it mechanically.  `m4_door_contradiction_of_blockMeanSq`
(and its collision form) is that composition: the whole M4/S9 chain, conditional on the
**per-block** mean square instead of the door-integrated one.  What remains open after this
file is exactly bridges 1–4 — the per-block bound `M4BlockMeanSq` — and nothing else on the
covering side.

## ⟦THE SUP ROUTE⟧ (bridge #2's socket — reachable, deliberately uncoupled)

Bridge #2 (`M4BridgePhase`, landed concurrently) states a *second* door-level socket
`M4SievedDoorSqSup`, at `subWindowSup` and at the rationals `b/q`, and discharges
`M4SievedDoorSq` from it at the drift price `(1 + 2π·arcDen 12 H)²`.  §3's
`integral_door_cover_le` is stated at a **general nonnegative `g : ℕ → ℝ`**, so it applies
verbatim at `g n := (subWindowSup (1_𝒮·λ) H n (b/q))²` — the covering side of the sup route
needs no new lemma, only the ~20-line repackaging of §4 (`M4BlockMeanSqSup` ⟹
`M4SievedDoorSqSup`, same factor `3`).  That repackaging is deliberately NOT written here:
it would import a sibling still in flight.  Land it in whichever of the two files settles
last.

## ⟦THE B-4 SEAM⟧

At this file's build time no sibling bridge file existed in `Salt/MR/`, so `M4BlockMeanSq` is
stated at the **natural per-block form**: `∑_{n ∈ block} ‖W(n)‖² ≤ B·H²·X_{i+1}`, i.e.
"mean square over a block ≤ grade × (block content)", with the block content taken at the
block *bottom* `X_{i+1}` (the ladder's fit `X_i ≤ 2X_{i+1}` makes bottom, top and cardinality
interchangeable up to the factor 2 — `block_weight_exchange_tight`).  If B-4 exits at the
block *cardinality* or the block *top* instead, the adapter is one `mul_le_mul` through
`doorLadder_top_le_two_mul` and costs a factor `2` in `B_blk`; the general lemma
`integral_door_cover_le` is stated at a free `P`, so no restatement is needed.

## Contents

* §1 THE BLOCK WEIGHT EXCHANGE — `1/n ≍ 1/X_{i+1}` on a ladder block, both directions.
* §2 THE LADDER SUM — the cover sum at a FREE endpoint numerator (M4-8's
  `door_cover_sum_le` is its `E := H` instance).
* §3 THE NORMALISATION AND THE ABSORPTION — `Z` spent once.
* §4 THE EXIT — `m4_cover_assembly`, its inhabitation witness, and THE JOIN.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE BLOCK WEIGHT EXCHANGE

On one ladder block `(X_{i+1}, X_i]` the harmonic weight `1/n` is comparable to the uniform
weight `1/X_{i+1}`.  `M4Door`'s `sum_div_Ioc_le` / `le_sum_div_Ioc` are the two directions;
this section instantiates them at the ladder and records that the loss is a factor `2`. -/

/-- The ladder never reaches `0`: `X_i ≥ H + 1 ≥ 1`.  This is the `ℕ`-division fact the
comparison needs — the `+1` rounding-up of `doorLadder` is what keeps the floor. -/
theorem doorLadder_pos {x H : ℕ} (hxH : H + 1 ≤ x) (i : ℕ) : 0 < (doorLadder x H i : ℝ) := by
  have h := doorLadder_floor hxH i
  have hn : 0 < doorLadder x H i := by omega
  exact_mod_cast hn

/-- **THE BLOCK IS DYADIC AFTER ALL.**  `X_i ≤ 2·X_{i+1}` — a direct consequence of the fit
`X_i + H ≤ 2·X_{i+1}`.  This is why the harmonic weight on a `doorLadder` block behaves
exactly as it would on an exactly-dyadic one, even though the ladder is `H`-offset. -/
theorem doorLadder_top_le_two_mul (x H i : ℕ) :
    (doorLadder x H i : ℝ) ≤ 2 * (doorLadder x H (i + 1) : ℝ) := by
  have h := doorLadder_fit x H i
  have hn : doorLadder x H i ≤ 2 * doorLadder x H (i + 1) := by omega
  exact_mod_cast hn

/-- **THE WEIGHT EXCHANGE** — the bridge's first stone.  A *block* bound
`∑_{n ∈ (a,b]} f(n) ≤ P·a + E` becomes a *harmonic* bound `∑_{n ∈ (a,b]} f(n)/n ≤ P + E/a`.

The exchange is exactly `M4Door.sum_div_Ioc_le` (`∑ f/n ≤ (∑ f)/a`) followed by the division;
the additive `E` is carried because the door's per-block endpoint leakage (M4-8's `H/X_i`
lattice-point term, HS-6) arrives in that shape.  The `f n * (n:ℝ)⁻¹` spelling is the door
carrier's own (`integral_logMeasure_le_div`); the `f n / (n:ℝ)` spelling is `M4Dyadic`'s. -/
theorem block_weight_exchange {a b : ℕ} {f : ℕ → ℝ} {P E : ℝ} (ha : 0 < (a : ℝ))
    (hf : ∀ n ∈ Finset.Ioc a b, 0 ≤ f n)
    (hbd : ∑ n ∈ Finset.Ioc a b, f n ≤ P * (a : ℝ) + E) :
    ∑ n ∈ Finset.Ioc a b, f n * (n : ℝ)⁻¹ ≤ P + E / (a : ℝ) := by
  have hrw : ∑ n ∈ Finset.Ioc a b, f n * (n : ℝ)⁻¹
      = ∑ n ∈ Finset.Ioc a b, f n / (n : ℝ) :=
    Finset.sum_congr rfl fun n _ => by rw [div_eq_mul_inv]
  rw [hrw]
  refine le_trans (sum_div_Ioc_le ha hf) ?_
  rw [div_le_iff₀ ha]
  have he : (P + E / (a : ℝ)) * (a : ℝ) = P * (a : ℝ) + E := by field_simp
  rw [he]
  exact hbd

/-- **THE EXCHANGE IS SHARP, up to `2`** — the recovery direction, at a ladder block.
`(∑ f)/(2·X_{i+1}) ≤ ∑ f(n)/n`, from `M4Door.le_sum_div_Ioc` and `doorLadder_top_le_two_mul`.

Kept because it is the *reason* the cover is a dyadic-scale ladder: with
`block_weight_exchange` it pins the harmonic mass of a block between `P/2` and `P`, so the
covering argument loses an absolute factor and never a `log`.  (Nothing downstream consumes
it; it is the two-sidedness the brief asks be visible.) -/
theorem block_weight_exchange_tight {x H i : ℕ} {f : ℕ → ℝ} (hxH : H + 1 ≤ x)
    (hf : ∀ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), 0 ≤ f n) :
    (∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n)
        / (2 * (doorLadder x H (i + 1) : ℝ))
      ≤ ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n * (n : ℝ)⁻¹ := by
  have hS : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n :=
    Finset.sum_nonneg hf
  have hXi : (0 : ℝ) < (doorLadder x H i : ℝ) := doorLadder_pos hxH i
  have hX1 : (0 : ℝ) < (doorLadder x H (i + 1) : ℝ) := doorLadder_pos hxH (i + 1)
  have h2 := doorLadder_top_le_two_mul x H i
  have hrw : ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n * (n : ℝ)⁻¹
      = ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n / (n : ℝ) :=
    Finset.sum_congr rfl fun n _ => by rw [div_eq_mul_inv]
  rw [hrw]
  refine le_trans ?_ (le_sum_div_Ioc hf)
  rw [div_le_div_iff₀ (by positivity) hXi]
  nlinarith

/-! ## §2 — THE LADDER SUM

`M4Door.door_cover_sum_le` sums a per-block bound `P + H/X_{i+1}` over the ladder.  Its
endpoint numerator is tied to the ladder's own `H` because the sieve leg's leakage is `H/X_i`
on the nose.  The mean-square leg's endpoint numerator is NOT `H`, so the numerator is freed
here; `door_cover_sum_le` is the `E := H` instance of what follows, and the proof consumes
the same four M4-8 stones (`sum_Ioc_ladder_split`, `doorLadder_step_le`, `doorLadder_inv_le`,
`sum_range_two_pow_shift_le`). -/

/-- **THE COVER SUM AT A FREE ENDPOINT NUMERATOR.**  A per-block bound `P + E/X_{i+1}`,
uniform over the ladder, sums to `k·P + 4·2^k·E/x` over the whole door window `(x/ω, x]`.

⟦THE TWO TERMS⟧
* `k·P` — the cover count, IN-STATEMENT (law #253).  §3 cancels it against `Z`.
* `4·2^k·E/x` — the geometric endpoint sum: `∑_{i<k} 1/X_{i+1} ≤ ∑_{i<k} 2^{i+2}/x ≤ 4·2^k/x`
  (`doorLadder_inv_le` + `sum_range_two_pow_shift_le`), M4-8's grade, unchanged. -/
theorem door_cover_weighted_le {x H ω k : ℕ} {f : ℕ → ℝ} {P E : ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hE : 0 ≤ E) (hxH : H + 1 ≤ x) (hreach : doorLadder x H k ≤ x / ω)
    (hpow : 2 ^ (k + 1) ≤ x)
    (hblk : ∀ i < k, ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n
        ≤ P + E / (doorLadder x H (i + 1) : ℝ)) :
    ∑ n ∈ Finset.Ioc (x / ω) x, f n ≤ (k : ℝ) * P + 4 * 2 ^ k * E / (x : ℝ) := by
  have hpowR : (2 : ℝ) ^ (k + 1) ≤ (x : ℝ) := by exact_mod_cast hpow
  have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hpowR
  -- ⟦STEP 1⟧ enlarge the door window to the ladder's own range
  have hsub : Finset.Ioc (x / ω) x ⊆ Finset.Ioc (doorLadder x H k) (doorLadder x H 0) := by
    rw [doorLadder_zero]
    intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨lt_of_le_of_lt hreach hn.1, hn.2⟩
  have hstep1 : ∑ n ∈ Finset.Ioc (x / ω) x, f n
      ≤ ∑ n ∈ Finset.Ioc (doorLadder x H k) (doorLadder x H 0), f n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf0 n)
  -- ⟦STEP 2⟧ the ladder split
  have hsplit := sum_Ioc_ladder_split (Xs := fun i => doorLadder x H i)
    (fun i => doorLadder_step_le hxH i) f k
  -- ⟦STEP 3⟧ the per-block bound, summed
  have hstep3 : ∑ i ∈ Finset.range k,
      ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n
      ≤ ∑ i ∈ Finset.range k, (P + E / (doorLadder x H (i + 1) : ℝ)) :=
    Finset.sum_le_sum (fun i hi => hblk i (Finset.mem_range.mp hi))
  -- ⟦STEP 4⟧ the endpoint sum is geometric
  have hgeo : ∑ i ∈ Finset.range k, E / (doorLadder x H (i + 1) : ℝ)
      ≤ 4 * 2 ^ k * E / (x : ℝ) := by
    have hterm : ∀ i ∈ Finset.range k,
        E / (doorLadder x H (i + 1) : ℝ) ≤ E * ((2 : ℝ) ^ (i + 2) / (x : ℝ)) := by
      intro i hi
      have hik := Finset.mem_range.mp hi
      have hpow' : 2 ^ (i + 1 + 1) ≤ x :=
        le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hpow
      have hinv := doorLadder_inv_le (x := x) (H := H) (i := i + 1) hpow'
      have hrw : E / (doorLadder x H (i + 1) : ℝ)
          = E * (1 / (doorLadder x H (i + 1) : ℝ)) := by ring
      have heq : i + 1 + 1 = i + 2 := by omega
      rw [heq] at hinv
      rw [hrw]
      exact mul_le_mul_of_nonneg_left hinv hE
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, ← Finset.sum_div]
    have hgs := sum_range_two_pow_shift_le k
    have hdiv : (∑ i ∈ Finset.range k, (2 : ℝ) ^ (i + 2)) / (x : ℝ)
        ≤ (4 * 2 ^ k) / (x : ℝ) := by
      rw [div_le_div_iff₀ hx0 hx0]
      nlinarith
    calc E * ((∑ i ∈ Finset.range k, (2 : ℝ) ^ (i + 2)) / (x : ℝ))
        ≤ E * ((4 * 2 ^ k) / (x : ℝ)) := mul_le_mul_of_nonneg_left hdiv hE
      _ = 4 * 2 ^ k * E / (x : ℝ) := by ring
  -- ⟦STEP 5⟧ the arithmetic
  have hconst : ∑ i ∈ Finset.range k, (P + E / (doorLadder x H (i + 1) : ℝ))
      = (k : ℝ) * P + ∑ i ∈ Finset.range k, E / (doorLadder x H (i + 1) : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsplit] at hstep1
  rw [hconst] at hstep3
  linarith

/-! ## §3 — THE NORMALISATION AND THE ABSORPTION

`Z` is spent exactly once, and the arithmetic of the spending lives in `M4Door` §4. -/

/-- **THE ABSORPTION, at a general grade.**  `(k·P + G)/Z ≤ 3·P + G/Z` whenever `k ≤ 3·Z`.

This is `M4Door.door_mass_normalised_le` re-instantiated at `Hr := 1`, `δ := 12·P` — the
SAME lemma M4-8 used for the sieve mass, so the `log ω` cancellation exists in one place.
What is *not* repeated is M4-8's price for it: the `M`-gate rescale `8C/δ ↦ 24C/δ` is the
sieve leg's, and the mean-square leg pays instead in the absolute grade factor `3`. -/
theorem door_weight_absorb {k : ℕ} {Z P G : ℝ} (hZ0 : 0 < Z) (hk3 : (k : ℝ) ≤ 3 * Z)
    (hP : 0 ≤ P) : ((k : ℝ) * P + G) / Z ≤ 3 * P + G / Z := by
  have h := door_mass_normalised_le (k := k) (Z := Z) (δ := 12 * P) (Hr := 1) (Gm := G)
    hZ0 hk3 (by linarith) zero_le_one
  have e1 : 12 * P / 3 / 4 * (1 : ℝ) = P := by ring
  have e2 : 12 * P / 4 * (1 : ℝ) = 3 * P := by ring
  rw [e1, e2] at h
  exact h

/-- **THE COMPOSED COVER BOUND — the bridge's centre of gravity.**  From a per-block bound
on the *unweighted* block sum, the `logMeasure`-integrated bound over the whole door window:

`∀ i<k, ∑_{n ∈ (X_{i+1},X_i]} g(n) ≤ P·X_{i+1} + E`  ⟹  `∫ g dμ ≤ 3·P + 4·2^k·E/x`.

⟦THE THREE STEPS, NAMED⟧ `block_weight_exchange` (§1) → `door_cover_weighted_le` (§2) →
`M4Door.integral_logMeasure_le_div` + `door_count_le_three_mul_norm` + `door_weight_absorb`
(§3).  The endpoint term survives the normalisation undivided because `Z ≥ log ω − 1 ≥ 3 ≥ 1`
(the `log ω ≥ 4` floor) and dividing by `Z ≥ 1` can only help. -/
theorem integral_door_cover_le {x ω H k : ℕ} {g : ℕ → ℝ} {P E : ℝ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (hlogω : 4 ≤ Real.log (ω : ℝ))
    (hcount : (k : ℝ) ≤ Real.log (ω : ℝ) / Real.log 2 + 2)
    (hg0 : ∀ n, 0 ≤ g n) (hP : 0 ≤ P) (hE : 0 ≤ E) (hxH : H + 1 ≤ x)
    (hreach : doorLadder x H k ≤ x / ω) (hpow : 2 ^ (k + 1) ≤ x)
    (hblk : ∀ i < k, ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), g n
        ≤ P * (doorLadder x H (i + 1) : ℝ) + E) :
    (∫ n, g n ∂(logMeasure x ω)) ≤ 3 * P + 4 * 2 ^ k * E / (x : ℝ) := by
  have hx0 : (0 : ℝ) < (x : ℝ) := by
    have : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  -- ⟦the normaliser, off M4-8's `log ω` page⟧
  have hZlo : Real.log (ω : ℝ) - 1 ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    door_norm_ge hx hω hωx
  have hZ1 : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
  have hZ0 : (0 : ℝ) < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
  -- ⟦§1, per block⟧
  have hwblk : ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), g n * (n : ℝ)⁻¹
        ≤ P + E / (doorLadder x H (i + 1) : ℝ) := fun i hi =>
    block_weight_exchange (doorLadder_pos hxH (i + 1)) (fun n _ => hg0 n) (hblk i hi)
  -- ⟦§2, the ladder⟧
  have hsum := door_cover_weighted_le (f := fun n => g n * (n : ℝ)⁻¹) (P := P) (E := E)
    (fun n => mul_nonneg (hg0 n) (by positivity)) hE hxH hreach hpow hwblk
  -- ⟦§3, the sharp normalisation⟧
  have hint := integral_logMeasure_le_div (x := x) (ω := ω) (f := g) hZ0 hsum
  -- ⟦§3, the absorption⟧
  have hk3 : (k : ℝ) ≤ 3 * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    door_count_le_three_mul_norm hlogω hcount hZlo
  have habs := door_weight_absorb (k := k)
    (Z := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) (P := P)
    (G := 4 * 2 ^ k * E / (x : ℝ)) hZ0 hk3 hP
  -- ⟦the endpoint term: `Z ≥ 1` can only help⟧
  have hG0 : (0 : ℝ) ≤ 4 * 2 ^ k * E / (x : ℝ) := by positivity
  have hend : (4 * 2 ^ k * E / (x : ℝ)) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹
      ≤ 4 * 2 ^ k * E / (x : ℝ) := by
    rw [div_le_iff₀ hZ0]
    nlinarith
  linarith

/-- **THE CLEAN CASE** (`E = 0`): a per-block bound with no endpoint leakage integrates to
`3·P` flat.  This is the shape the mean-square leg uses — the door's lattice-point leakage is
the *sieve* leg's business (M4-8's HS-6 term), already paid inside `m4_door_glue`. -/
theorem integral_door_cover_le_clean {x ω H k : ℕ} {g : ℕ → ℝ} {P : ℝ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (hlogω : 4 ≤ Real.log (ω : ℝ))
    (hcount : (k : ℝ) ≤ Real.log (ω : ℝ) / Real.log 2 + 2)
    (hg0 : ∀ n, 0 ≤ g n) (hP : 0 ≤ P) (hxH : H + 1 ≤ x)
    (hreach : doorLadder x H k ≤ x / ω) (hpow : 2 ^ (k + 1) ≤ x)
    (hblk : ∀ i < k, ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), g n
        ≤ P * (doorLadder x H (i + 1) : ℝ)) :
    (∫ n, g n ∂(logMeasure x ω)) ≤ 3 * P := by
  have h := integral_door_cover_le (x := x) (ω := ω) (H := H) (k := k) (g := g) (P := P)
    (E := 0) hx hω hωx hlogω hcount hg0 hP le_rfl hxH hreach hpow
    (fun i hi => by simpa using hblk i hi)
  simpa using h

/-! ## §4 — THE EXIT

`M4Close.M4SievedDoorSq`, discharged from a per-block mean square. -/

/-- **THE DOOR'S SIEVED DATUM**, named once: `1_𝒮·λ` at the door's own K-family
(`A = Adoor M`, `G = 3072·M`, `J = 2`).  This is byte-exactly the coefficient sequence
inside `M4Close.M4SievedDoorSq`; the `def` is a spelling, definitionally transparent. -/
def doorSievedCoeff (M : ℕ) : ℕ → ℂ :=
  memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC

/-- The sieved datum is 1-bounded (the indicator only ever deletes terms). -/
theorem norm_doorSievedCoeff_le_one (M m : ℕ) : ‖doorSievedCoeff M m‖ ≤ 1 :=
  norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m

/-- **`H + 1 ≤ x` FROM THE REGIME** — the ladder's floor invariant, off `R.hheadroom`
(`H ≤ Hhi ≤ x/ω ≤ x/2`) and `R.hx`.  Extracted from `M4Close.m4_hbd_of_live`'s proof, where
the same three lines appear inline. -/
theorem regime_window_headroom (R : ChowlaRegime) {H : ℕ} (hhi : H ≤ R.Hhi) : H + 1 ≤ R.x := by
  have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
  have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
  have h2 : 2 ≤ R.x := R.hx
  omega

/-- **THE PER-BLOCK MEAN SQUARE** — the shape bridges 1–4 deliver, one `doorLadder` block at
a time, uniformly over the admissible window range and over tight-major frequencies:

`∑_{n ∈ (X_{i+1}, X_i]} ‖∑_{n<m≤n+H} 1_𝒮(m)λ(m)e(αm)‖² ≤ B_blk(H)·H²·X_{i+1}`.

The right side is "grade × block content": `X_{i+1}` is the block bottom, which by the
ladder's fit (`doorLadder_top_le_two_mul`) is within a factor `2` of the block top and of the
block cardinality.  `H²` is the mean square's own normalisation (`thm_a2'`'s carrier is
`‖(1/h)·shortSum‖²`).  The blocks and the count `k` are the SAME ones `m4_door_glue` eats. -/
def M4BlockMeanSq (R : ChowlaRegime) (M k : ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ, NearRatTight (arcDen 12 H) H α →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          ‖absWindowSum (doorSievedCoeff M) H n α‖ ^ 2
        ≤ Bblk H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **`m4_cover_assembly` — BRIDGE 5's EXIT.**  The per-block mean square, assembled over the
door ladder and normalised against `logMeasure`, IS `M4Close.M4SievedDoorSq` at the grade
`3·B_blk`.

⟦WHAT IS CONSUMED⟧ the door-gate bundle `M4DoorGates` for its ladder data (`hlogω`, `hcount`,
`hpow`, `hreach`) — the same bundle `m4_hbd_of_live` reads, so the join needs no new
hypothesis; and `M4Door` §1–§4 through `integral_door_cover_le_clean`.

⟦WHERE THE `3` COMES FROM⟧ the cover has `k ≍ log ω/log 2` blocks and the door normaliser is
`Z ≍ log ω`; `door_count_le_three_mul_norm` cancels them at the absolute ratio `3`.  It is a
grade factor, not an `M`-gate rescale (see the module header's ⟦`Z`'S TWO ROLES⟧). -/
theorem m4_cover_assembly {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSq R M k Bblk) :
    M4SievedDoorSq R M (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi α harc
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (H : ℝ) ^ 2 := mul_nonneg (hB0 H) (by positivity)
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => ‖absWindowSum (doorSievedCoeff M) H n α‖ ^ 2)
    (P := Bblk H * (H : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount (fun n => by positivity) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi α harc)
  simp only [doorSievedCoeff] at hmain
  have heq : 3 * (Bblk H * (H : ℝ) ^ 2) = 3 * Bblk H * (H : ℝ) ^ 2 := by ring
  rw [heq] at hmain
  exact hmain

/-- **THE PER-BLOCK HYPOTHESIS IS INHABITED** (the anti-vacuity duty — M4-1's lesson, M4-8's
`doorCount_gates`, M4-7's `m4_sievedDoorSq_trivial`).  At the trivial grade `B_blk ≡ 1` the
per-block bound holds outright: each window carries `H` terms of modulus `≤ 1`, and the
block's cardinality `X_i − X_{i+1}` is `≤ X_{i+1}` by the ladder's fit.  So `M4BlockMeanSq`
is not satisfiable-by-nobody; ALL of its content is the grade. -/
theorem m4_blockMeanSq_trivial (R : ChowlaRegime) (M k : ℕ) :
    M4BlockMeanSq R M k (fun _ => 1) := by
  intro H _ hhi α _ i _
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hH2 : (0 : ℝ) ≤ (H : ℝ) ^ 2 := by positivity
  have hterm : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      ‖absWindowSum (doorSievedCoeff M) H n α‖ ^ 2 ≤ (H : ℝ) ^ 2 := by
    intro n _
    have h := norm_absWindowSum_le (norm_doorSievedCoeff_le_one M) H n α
    have h0 := norm_nonneg (absWindowSum (doorSievedCoeff M) H n α)
    nlinarith
  have hcard : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      ‖absWindowSum (doorSievedCoeff M) H n α‖ ^ 2
      ≤ ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ) * (H : ℝ) ^ 2 := by
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          ‖absWindowSum (doorSievedCoeff M) H n α‖ ^ 2
        ≤ ∑ _n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i), (H : ℝ) ^ 2 :=
          Finset.sum_le_sum hterm
      _ = ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
            * (H : ℝ) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
      ≤ (doorLadder R.x H (i + 1) : ℝ) := by
    rw [Nat.card_Ioc]
    have hfit := doorLadder_fit R.x H i
    have hn : doorLadder R.x H i - doorLadder R.x H (i + 1) ≤ doorLadder R.x H (i + 1) := by
      omega
    exact_mod_cast hn
  have hpos := doorLadder_pos hxH (i + 1)
  nlinarith

/-- **THE GRADE GATE AT THE BLOCK GRADE.**  `M4Close.m4_gradeGate_of_pricing`, read at the
assembly's own output grade `3·B_blk`: the absolute factor `3` is absorbed by asking the
pricing at `3·B_blk H ≤ m4Saving H` instead of `B_blk H ≤ m4Saving H`, and the quality
demand's `W^{−5/2}` saving has room for it. -/
theorem m4_gradeGate_of_block_pricing {R : ChowlaRegime} {C δ : ℝ} {Bblk : ℕ → ℝ} {k : ℕ}
    (hC : 2 ≤ C)
    (hB : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 3 * Bblk H ≤ m4Saving H)
    (hrest : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) :
    M4GradeGate R C δ (fun H => 3 * Bblk H) k :=
  m4_gradeGate_of_pricing hC hB hrest

/-! ### THE JOIN

`M4Close.m4_door_contradiction_of_live` carries `M4SievedDoorSq` as a hypothesis; §4
discharges it from `M4BlockMeanSq`.  Composing them moves the wave's open obligation from the
door-integrated mean square to the per-block one — i.e. off the covering side entirely, onto
bridges 1–4. -/

/-- **THE WAVE'S EXIT, AT THE PER-BLOCK HYPOTHESIS.**  `m4_door_contradiction_of_live` with
its socket replaced by `M4BlockMeanSq`: for every `C_MRT ≥ 0` and every floor/outer-scale
demand there is a regime at which log-Chowla-2 does not fail, conditional on

* `M4DoorGates Cg R M k δ` — M4-8's door list (unchanged; the assembly reads its ladder data),
* `0 ≤ B_blk H` — the block grade is a grade,
* `M4GradeGate R C δ (3·B_blk) k` — the budget line at the assembled grade
  (`m4_gradeGate_of_block_pricing`),
* `M4BlockMeanSq R M k B_blk` — **THE PER-BLOCK MEAN SQUARE**, owed by bridges 1–4.

Nothing on the covering side remains: the harmonic weight, the ladder sum, the `log ω`
absorption and the `L²→L¹` descent are all landed and consumed. -/
theorem m4_door_contradiction_of_blockMeanSq :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Bblk : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ → (∀ H : ℕ, 0 ≤ Bblk H) →
            M4GradeGate R C δ (fun H => 3 * Bblk H) k →
            M4BlockMeanSq R M k Bblk →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Bblk M k hgates hB0 hgrade hblk => ?_⟩
  exact hR δ (fun H => 3 * Bblk H) M k hgates
    (fun H => by have := hB0 H; linarith) hgrade (m4_cover_assembly hgates hB0 hblk)

/-- The join's collision form (`m4_door_False_of_live` composed with the same supply). -/
theorem m4_door_False_of_blockMeanSq :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Bblk : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ → (∀ H : ℕ, 0 ≤ Bblk H) →
            M4GradeGate R C δ (fun H => 3 * Bblk H) k →
            M4BlockMeanSq R M k Bblk →
              logChowla2Fails R.eps R.x R.ω → False := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_False_of_live
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Bblk M k hgates hB0 hgrade hblk => ?_⟩
  exact hR δ (fun H => 3 * Bblk H) M k hgates
    (fun H => by have := hB0 H; linarith) hgrade (m4_cover_assembly hgates hB0 hblk)

/-! ### ⟦THE SPLIT TWINS⟧ (second-road freeze v2, wave ①)

The family's contract is `M4Exit` §7.  Nothing on the covering side changes at all — the
assembly (`m4_cover_assembly`), its factor `3` and the anti-vacuity witness are all consumed
verbatim.  Only the budget line moves to the constant grade, and the `C_MRT` binder goes. -/

/-- **THE SPLIT GATE AT THE BLOCK GRADE** (`m4_gradeGate_of_block_pricing_split`) — the twin
of `m4_gradeGate_of_block_pricing` (:461).  `m4_gradeGate_of_pricing_split` read at the
assembly's own output grade `3·B_blk`: the absolute factor `3` is absorbed by asking the
pricing at `3·B_blk H ≤ (δ₀/2)²`. -/
theorem m4_gradeGate_of_block_pricing_split {R : ChowlaRegime} {δ₀ δ : ℝ} {Bblk : ℕ → ℝ}
    {k : ℕ} (hδ₀ : 0 ≤ δ₀)
    (hB : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 3 * Bblk H ≤ (δ₀ / 2) ^ 2)
    (hrest : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 2) :
    M4GradeGateSplit R δ₀ δ (fun H => 3 * Bblk H) k :=
  m4_gradeGate_of_pricing_split hδ₀ hB hrest

/-- **THE WAVE'S EXIT AT THE PER-BLOCK HYPOTHESIS, SPLIT**
(`m4_door_contradiction_of_blockMeanSq_split`) — the twin of
`m4_door_contradiction_of_blockMeanSq` (:488).

The landed register with `C` deleted and the budget line at `M4GradeGateSplit`; the door
gates, the block-grade positivity and `M4BlockMeanSq` are unchanged, and so is the
conclusion. -/
theorem m4_door_contradiction_of_blockMeanSq_split :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Bblk : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ → (∀ H : ℕ, 0 ≤ Bblk H) →
            M4GradeGateSplit R δ₀ δ (fun H => 3 * Bblk H) k →
            M4BlockMeanSq R M k Bblk →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_split
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Bblk M k hgates hB0 hgrade hblk => ?_⟩
  exact hR δ (fun H => 3 * Bblk H) M k hgates
    (fun H => by have := hB0 H; linarith) hgrade (m4_cover_assembly hgates hB0 hblk)

end Salt.MR

end
