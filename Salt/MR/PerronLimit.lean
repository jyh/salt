/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Lemma14

/-!
# S8 MR-CORE, nodes A3a-R4 / A3a-R1 — the wide collapse and the Perron `T → ∞` limit

Source pin: **MR arXiv v4** (`docs/sources/1501.04585v4.pdf`), §7, pp. 21–23.

This file discharges the two cheap named residuals of the Lemma-14 chain, on top of
`Salt.MR.Lemma14` and its ladder.

## P1 — `A3a-R4`, the top-edge collapse (the `x + h ≤ 2X` caveat removed)

The landed `zone_sum_collapsed` (`PerronZones.lean`) assumes `x ≤ 2X`, so its corollary
`Aperron_short_interval_collapsed` (`Lemma14Bridge.lean`) needs `x + h ≤ 2X` and fails on the
top edge `x ∈ [2X − h₂, 2X]` of the Lemma-14 average.  The honest range is
`x ∈ [X, 2X]`, `h ≤ h₂ ≤ X`, hence `x + h ≤ 3X`.

**The constants page.**  Re-running the collapse at the wide range:

* `zone_min_sum_le` needs `x ≤ 4X` only (it is the input to `decay_le_of_dist`,
  whose MR-range hypothesis is `x ≤ 4X`); its two harmonic reindexings already land in
  `[1, ⌊3X⌋]` for **any** `x ∈ [X, 4X]`: the right side has
  `m − ⌈x⌉ ≤ 4X − x ≤ 3X` and the left side `⌊x⌋ − m ≤ x − X ≤ 3X`.  So
  `zone_min_sum_le_wide` carries the *same* bound `3·BIG + (8X/T)(1 + log⌊3X⌋)` on all of
  `X ≤ x ≤ 4X` — nothing degrades.
* The only genuine loss is the per-term coefficient `2·(x/m)`: on `m ≥ X`, `x ≤ 2X` gives
  `x/m ≤ 2` (factor `4`), while `x ≤ 3X` gives `x/m ≤ 3` (factor `6`).  Hence
  `12·BIG + (32X/T)(1+log 3X)` becomes `18·BIG + (48X/T)(1+log 3X)` — exactly the `6/4`
  rescale, no new log.

So `Aperron_short_interval_collapsed_wide` (bound `2·(18·BIG + (48X/T)(1+log 3X))`) and
`perron_gap_collapsed_wide` (bound `4·(…)`) hold with **no** top-edge caveat on `[X, 2X]`,
and `lemma14_shortInterval_concrete` closes Lemma 14 in the `Sⱼ` form with a fully explicit
(non-vanishing) `Eper`, on the whole interval.

## P2 — `A3a-R1`, the per-point Perron limit

The zone-collapsed error does **not** vanish for large `T` (its near-diagonal `BIG` branch
grows like `log T`).  The *non-collapsed* error of `Aperron_representation` does: taking the
`min`-device's **decay** branch termwise, for a fixed `y` off the support (`(m:ℝ) ≠ y`)

`‖E(y,T)‖ ≤ (∑_{m ∈ s0} ‖aₘ‖·2(y/m)ᶜ/|log(y/m)|)/T = perronConst a s0 y c / T`,

which is decreasing in `T` and tends to `0` — the classical truncated-Perron limit
(`Aperron_error_le_of_T`, `Aperron_error_small`, `Aperron_tendsto`).  The constant is finite
for each admissible `y` but **blows up as `y` approaches an integer of the support**
(`1/|log(y/m)| ~ m/|y−m|`); that is exactly the non-uniformity the collapsed bound trades
away, and it is why the Lemma-14 consumer (which needs one `T` for a.e. `x ∈ [X,2X]`
simultaneously) cannot yet take `Eper = 0`.

## P3 — the per-`x` gap

`uSlab_gap_le_of_T` / `perron_gap_le_of_T` / `perron_gap_tendsto`: for each fixed `x` obeying
the boundary guards, the Lemma-14 Perron gap is `≤ C(x)/T` and tends to `0` as `T → ∞`.  The
`x`-uniform version (the true `Eper = 0`) needs a mean-square-in-`x` treatment of `C(x)`, i.e.
the integrated near-diagonal loss; that is the next stone, not this one.

All results are axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`,
no new axioms, no `sorry`.
-/

open MeasureTheory Complex Set intervalIntegral Filter Topology
open scoped BigOperators

noncomputable section
namespace Salt.MR

/-! ## P1 — `A3a-R4`: the collapse at the wide range `x ≤ 3X` -/

/-- **The `min`-sum bound, wide range** — `zone_min_sum_le` with the top-edge restriction
`x ≤ 2X` relaxed to `x ≤ 4X`, at *no* cost in the bound.  The near band (`|x−m| < 1`, `≤ 3`
integers, the `BIG` branch) is unchanged; both far sides still reindex injectively into
`[1, ⌊3X⌋]` because `m − ⌈x⌉ ≤ 4X − X = 3X` and `⌊x⌋ − m ≤ 4X − X = 3X`. -/
theorem zone_min_sum_le_wide (s0 : Finset ℕ) {X x T : ℝ}
    (hX : 1 ≤ X) (hT : 0 < T) (hx : X ≤ x) (hx4 : x ≤ 4 * X)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X) :
    ∑ m ∈ s0, min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
      ≤ 3 * (Real.pi + 2 * Real.log (1 + T))
        + (8 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hBIG_nn : (0 : ℝ) ≤ Real.pi + 2 * Real.log (1 + T) := by
    have h1 := Real.pi_pos
    have h2 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + T)
    linarith
  have hN1 : 1 ≤ ⌊3 * X⌋₊ := Nat.le_floor (by push_cast; linarith)
  rw [← Finset.sum_filter_add_sum_filter_not s0 (fun m : ℕ => |x - (m : ℝ)| < 1)]
  -- Near band: the BIG branch, at most 3 integers.
  have hnear : ∑ m ∈ s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1),
        min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
      ≤ 3 * (Real.pi + 2 * Real.log (1 + T)) := by
    have hle : ∑ m ∈ s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1),
          min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
        ≤ ∑ _m ∈ s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1),
          (Real.pi + 2 * Real.log (1 + T)) :=
      Finset.sum_le_sum (fun m _ => min_le_left _ _)
    rw [Finset.sum_const, nsmul_eq_mul] at hle
    have hcard : ((s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1)).card : ℝ) ≤ 3 := by
      have hsub : s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1)
          ⊆ s0.filter (fun m : ℕ => |x - (m : ℝ)| ≤ 1) := by
        intro m hm; rw [Finset.mem_filter] at hm ⊢; exact ⟨hm.1, le_of_lt hm.2⟩
      have h1 : ((s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1)).card : ℝ)
          ≤ ((s0.filter (fun m : ℕ => |x - (m : ℝ)| ≤ 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have h2 := zone_count_crossover s0 (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (1 : ℝ) ≤ x)
      linarith
    calc ∑ m ∈ s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1),
          min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
        ≤ ((s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1)).card : ℝ)
            * (Real.pi + 2 * Real.log (1 + T)) := hle
      _ ≤ 3 * (Real.pi + 2 * Real.log (1 + T)) := mul_le_mul_of_nonneg_right hcard hBIG_nn
  -- Far band: split at m ≥ x+1 vs m ≤ x−1, each an injective harmonic reindex.
  have hfar : ∑ m ∈ s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1),
        min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
      ≤ (8 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not
        (s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1)) (fun m : ℕ => x + 1 ≤ (m : ℝ))]
    have hfpos : ∑ m ∈ (s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1)).filter
          (fun m : ℕ => x + 1 ≤ (m : ℝ)),
          min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
        ≤ (4 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by
      refine far_side_bound hX0 hT _ hN1 (fun m => m - ⌈x⌉₊) ?_ ?_ ?_ ?_
      · intro a ha b hb hab
        simp only [Finset.mem_filter] at ha hb
        have hca : ⌈x⌉₊ < a := by
          have := Nat.ceil_lt_add_one hx0.le
          have h' : (↑⌈x⌉₊ : ℝ) < ↑a := by linarith [ha.2]
          exact_mod_cast h'
        have hcb : ⌈x⌉₊ < b := by
          have := Nat.ceil_lt_add_one hx0.le
          have h' : (↑⌈x⌉₊ : ℝ) < ↑b := by linarith [hb.2]
          exact_mod_cast h'
        omega
      · intro m hm
        simp only [Finset.mem_filter] at hm
        have := Nat.ceil_lt_add_one hx0.le
        have h' : (↑⌈x⌉₊ : ℝ) < ↑m := by linarith [hm.2]
        have : ⌈x⌉₊ < m := by exact_mod_cast h'
        omega
      · intro m hm
        simp only [Finset.mem_filter] at hm
        obtain ⟨hmlo, hmhi⟩ := hrange m hm.1.1
        have hc := Nat.ceil_lt_add_one hx0.le
        have hcm : ⌈x⌉₊ < m := by
          have h' : (↑⌈x⌉₊ : ℝ) < ↑m := by linarith [hm.2]
          exact_mod_cast h'
        have hcast : ((m - ⌈x⌉₊ : ℕ) : ℝ) ≤ 3 * X := by
          rw [Nat.cast_sub hcm.le]
          have := Nat.le_ceil x
          linarith
        exact Nat.le_floor hcast
      · intro m hm
        simp only [Finset.mem_filter] at hm
        obtain ⟨hmlo, hmhi⟩ := hrange m hm.1.1
        have hm0 : (0 : ℝ) < m := by linarith
        have hcm : ⌈x⌉₊ < m := by
          have := Nat.ceil_lt_add_one hx0.le
          have h' : (↑⌈x⌉₊ : ℝ) < ↑m := by linarith [hm.2]
          exact_mod_cast h'
        have hD0 : (0 : ℝ) < ((m - ⌈x⌉₊ : ℕ) : ℝ) := by
          have : 0 < m - ⌈x⌉₊ := by omega
          exact_mod_cast this
        have hDdist : ((m - ⌈x⌉₊ : ℕ) : ℝ) ≤ |x - (m : ℝ)| := by
          rw [Nat.cast_sub hcm.le, abs_sub_comm, abs_of_nonneg (by linarith [hm.2])]
          have := Nat.le_ceil x
          linarith
        exact (min_le_right _ _).trans
          (decay_le_of_dist hX0 hT hm0 hmhi hx0 (by linarith) hD0 hDdist)
    have hfneg : ∑ m ∈ (s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1)).filter
          (fun m : ℕ => ¬ (x + 1 ≤ (m : ℝ))),
          min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
        ≤ (4 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by
      have hle1 : ∀ m ∈ (s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1)).filter
          (fun m : ℕ => ¬ (x + 1 ≤ (m : ℝ))), (m : ℝ) ≤ x - 1 := by
        intro m hm
        simp only [Finset.mem_filter] at hm
        have hlt : (m : ℝ) < x + 1 := not_le.mp hm.2
        have hge : (1 : ℝ) ≤ |x - (m : ℝ)| := not_lt.mp hm.1.2
        have hxm1 : (1 : ℝ) ≤ x - (m : ℝ) := by
          by_contra hc
          have hlt2 : x - (m : ℝ) < 1 := not_le.mp hc
          have : |x - (m : ℝ)| < 1 := abs_lt.mpr ⟨by linarith, hlt2⟩
          linarith
        linarith
      refine far_side_bound hX0 hT _ hN1 (fun m => ⌊x⌋₊ - m) ?_ ?_ ?_ ?_
      · intro a ha b hb hab
        have hma : (a : ℝ) ≤ x - 1 := hle1 a ha
        have hmb : (b : ℝ) ≤ x - 1 := hle1 b hb
        have ha' : a + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
        have hb' : b + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
        omega
      · intro m hm
        have hmx : (m : ℝ) ≤ x - 1 := hle1 m hm
        have hm' : m + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
        omega
      · intro m hm
        have hmx : (m : ℝ) ≤ x - 1 := hle1 m hm
        simp only [Finset.mem_filter] at hm
        obtain ⟨hmlo, hmhi⟩ := hrange m hm.1.1
        have hm' : m + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
        have hcast : ((⌊x⌋₊ - m : ℕ) : ℝ) ≤ 3 * X := by
          rw [Nat.cast_sub (by omega)]
          have := Nat.floor_le hx0.le
          linarith
        exact Nat.le_floor hcast
      · intro m hm
        have hmx : (m : ℝ) ≤ x - 1 := hle1 m hm
        simp only [Finset.mem_filter] at hm
        obtain ⟨hmlo, hmhi⟩ := hrange m hm.1.1
        have hm0 : (0 : ℝ) < m := by linarith
        have hm' : m + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
        have hD0 : (0 : ℝ) < ((⌊x⌋₊ - m : ℕ) : ℝ) := by
          have : 0 < ⌊x⌋₊ - m := by omega
          exact_mod_cast this
        have hDdist : ((⌊x⌋₊ - m : ℕ) : ℝ) ≤ |x - (m : ℝ)| := by
          rw [Nat.cast_sub (by omega), abs_of_nonneg (by linarith)]
          have := Nat.floor_le hx0.le
          linarith
        exact (min_le_right _ _).trans
          (decay_le_of_dist hX0 hT hm0 hmhi hx0 (by linarith) hD0 hDdist)
    have heq8 : (8 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ))
        = (4 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ))
          + (4 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by ring
    linarith [hfpos, hfneg, heq8]
  linarith [hnear, hfar]

/-- **`zone_sum_collapsed_wide`** — the wide-range collapse of `perron_sum_error_bound`'s RHS
(at `c = 1`, `‖aₘ‖ ≤ 1`, `m ∈ [X,4X]`): for `X ≤ x ≤ 3X`,
`≤ 18·(π + 2·log(1+T)) + (48X/T)·(1 + log(3X))`.  Identical to `zone_sum_collapsed` except
that `x/m ≤ 3` (instead of `≤ 2`) turns the per-term factor `4` into `6`. -/
theorem zone_sum_collapsed_wide (a : ℕ → ℂ) (s0 : Finset ℕ) {X x T : ℝ}
    (hX : 1 ≤ X) (hT : 0 < T) (hx : X ≤ x) (hx3 : x ≤ 3 * X)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X) :
    ∑ m ∈ s0, ‖a m‖ * (2 * (x / m)
        * min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|)))
      ≤ 18 * (Real.pi + 2 * Real.log (1 + T))
        + (48 * X / T) * (1 + Real.log (3 * X)) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hBIG_nn : (0 : ℝ) ≤ Real.pi + 2 * Real.log (1 + T) := by
    have h1 := Real.pi_pos
    have h2 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + T)
    linarith
  have hstepA : ∑ m ∈ s0, ‖a m‖ * (2 * (x / m)
        * min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|)))
      ≤ 6 * ∑ m ∈ s0,
          min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    obtain ⟨hmlo, hmhi⟩ := hrange m hm
    have hm0 : (0 : ℝ) < m := by linarith
    set M := min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|)) with hMdef
    have hMnn : (0 : ℝ) ≤ M := by rw [hMdef]; exact le_min hBIG_nn (by positivity)
    have hxm3 : x / m ≤ 3 := by rw [div_le_iff₀ hm0]; linarith
    calc ‖a m‖ * (2 * (x / m) * M)
        ≤ 1 * (6 * M) := by
          refine mul_le_mul (ha m hm) ?_ ?_ zero_le_one
          · nlinarith [hxm3, hMnn]
          · exact mul_nonneg (by positivity) hMnn
      _ = 6 * M := one_mul _
  have hstepB := zone_min_sum_le_wide s0 hX hT hx (by linarith) hrange
  have hlogfloor : Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ) ≤ Real.log (3 * X) := by
    have hfp : 1 ≤ ⌊3 * X⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊3 * X⌋₊))
      (Nat.floor_le (by linarith))
  calc ∑ m ∈ s0, ‖a m‖ * (2 * (x / m)
          * min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|)))
      ≤ 6 * ∑ m ∈ s0,
          min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|)) := hstepA
    _ ≤ 6 * (3 * (Real.pi + 2 * Real.log (1 + T))
          + (8 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hstepB (by norm_num)
    _ = 18 * (Real.pi + 2 * Real.log (1 + T))
          + (48 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by ring
    _ ≤ 18 * (Real.pi + 2 * Real.log (1 + T))
          + (48 * X / T) * (1 + Real.log (3 * X)) := by
        have h48 : (0 : ℝ) ≤ 48 * X / T := by positivity
        have hmul := mul_le_mul_of_nonneg_left
          (by linarith [hlogfloor] :
            (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) ≤ 1 + Real.log (3 * X)) h48
        linarith [hmul]

/-- **`perron_sum_error_collapsed_wide`** — the end-to-end summed-error bound at the wide
range `X ≤ x ≤ 3X` (the `x ≤ 2X` version is `perron_sum_error_collapsed`). -/
theorem perron_sum_error_collapsed_wide (a : ℕ → ℂ) (s0 : Finset ℕ) {X x T : ℝ}
    (hX : 1 ≤ X) (hT : 0 < T) (hx : X ≤ x) (hx3 : x ≤ 3 * X)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hne : ∀ m ∈ s0, (m : ℝ) ≠ x) :
    ‖∑ m ∈ s0, a m * (perronContour (x / m) 1 T
        - 2 * (Real.pi : ℂ) * I * (if 1 < x / m then (1 : ℂ) else 0))‖
      ≤ 18 * (Real.pi + 2 * Real.log (1 + T))
        + (48 * X / T) * (1 + Real.log (3 * X)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hpos : ∀ m ∈ s0, 0 < m := by
    intro m hm
    obtain ⟨hmlo, _⟩ := hrange m hm
    exact_mod_cast (by linarith : (0 : ℝ) < m)
  have hbound := perron_sum_error_bound a s0 hx0 (by norm_num : (0 : ℝ) < 1) hT hpos hne
  refine hbound.trans ?_
  have hrw : ∑ m ∈ s0, ‖a m‖ * (2 * (x / m) ^ (1 : ℝ)
        * min (Real.pi + 2 * Real.log (1 + T / 1)) (1 / (T * |Real.log (x / m)|)))
      = ∑ m ∈ s0, ‖a m‖ * (2 * (x / m)
        * min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Real.rpow_one, div_one]
  rw [hrw]
  exact zone_sum_collapsed_wide a s0 hX hT hx hx3 ha hrange

/-- **`Aperron_short_interval_collapsed_wide`** — `A3a-R4`, THE stone: the short-interval
Perron bridge collapsed with **no top-edge caveat**.  The hypothesis is the honest range
`x + h ≤ 3X` (which every `x ∈ [X,2X]` with `h ≤ X` satisfies), in place of
`Aperron_short_interval_collapsed`'s `x + h ≤ 2X`.  Constant: `2·(18·BIG + (48X/T)(1+log 3X))`
against the narrow version's `2·(12·BIG + (32X/T)(1+log 3X))` — the pure `6/4` rescale of the
per-term factor `2(x/m)`. -/
theorem Aperron_short_interval_collapsed_wide (a : ℕ → ℂ) (s0 : Finset ℕ) {X x h T : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hT : 0 < T) (hx : X ≤ x) (hxh3 : x + h ≤ 3 * X)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hne_x : ∀ m ∈ s0, (m : ℝ) ≠ x) (hne_xh : ∀ m ∈ s0, (m : ℝ) ≠ x + h) :
    ‖(I * ∫ v in (-T)..T,
          (∑ m ∈ s0, a m / (m : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I))
            * (((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I)
               - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I))
            / ((1 : ℂ) + (v : ℂ) * I))
        - 2 * (Real.pi : ℂ) * I
            * ∑ m ∈ s0, a m
                * ((if 1 < (x + h) / m then (1 : ℂ) else 0)
                   - (if 1 < x / m then (1 : ℂ) else 0))‖
      ≤ 2 * (18 * (Real.pi + 2 * Real.log (1 + T))
          + (48 * X / T) * (1 + Real.log (3 * X))) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hpos : ∀ m ∈ s0, 0 < m := fun m hm => by
    exact_mod_cast (show (0 : ℝ) < m by linarith [(hrange m hm).1])
  have hmain := Aperron_short_interval a s0 (c := 1) hx0 hh one_pos hT hpos hne_x hne_xh
  refine hmain.trans ?_
  have hrw : ∀ y : ℝ, (∑ m ∈ s0, ‖a m‖ * (2 * (y / (m : ℝ)) ^ (1 : ℝ)
          * min (Real.pi + 2 * Real.log (1 + T / 1)) (1 / (T * |Real.log (y / m)|))))
        = ∑ m ∈ s0, ‖a m‖ * (2 * (y / (m : ℝ))
          * min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (y / m)|))) := by
    intro y
    exact Finset.sum_congr rfl fun m _ => by rw [Real.rpow_one, div_one]
  rw [hrw (x + h), hrw x]
  have h1 := zone_sum_collapsed_wide a s0 hX hT (by linarith : X ≤ x + h) hxh3 ha hrange
  have h2 := zone_sum_collapsed_wide a s0 hX hT hx (by linarith : x ≤ 3 * X) ha hrange
  linarith [h1, h2]

/-- **`perron_gap_collapsed_wide`** — the Perron defect of the weighted difference at the
honest range: no top-edge caveat, `x + hⱼ ≤ 3X`.  This is what makes
`lemma14_shortInterval_of_perron`'s a.e. hypothesis dischargeable on the **whole** interval
`[X, 2X]` (the narrow `perron_gap_collapsed` fails on `[2X − h₂, 2X]`). -/
theorem perron_gap_collapsed_wide (a : ℕ → ℂ) (s0 : Finset ℕ) {X x h₁ h₂ T : ℝ}
    (hX : 1 ≤ X) (hh1 : 1 ≤ h₁) (hh2 : 1 ≤ h₂) (hT : 0 < T)
    (hx : X ≤ x) (hxh1 : x + h₁ ≤ 3 * X) (hxh2 : x + h₂ ≤ 3 * X)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hne_x : ∀ m ∈ s0, (m : ℝ) ≠ x)
    (hne_1 : ∀ m ∈ s0, (m : ℝ) ≠ x + h₁) (hne_2 : ∀ m ∈ s0, (m : ℝ) ≠ x + h₂) :
    ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ T
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ T
        - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)‖
      ≤ 4 * (18 * (Real.pi + 2 * Real.log (1 + T))
          + (48 * X / T) * (1 + Real.log (3 * X))) := by
  have hpos : ∀ m ∈ s0, 0 < m := by
    intro m hm
    have hm1 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by linarith) (hrange m hm).1
    exact_mod_cast hm1
  have hobj : ∀ h : ℝ, uSlab (dpolyA a s0) x h T
      = I * ∫ v in (-T)..T,
          (∑ m ∈ s0, a m / (m : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I))
            * (((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I)
              - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I)) / ((1 : ℂ) + (v : ℂ) * I) := by
    intro h
    rw [uSlab]
    congr 1
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    simp only [dpolyA, uKernel]
    rw [mul_div_assoc]
  have hgap : ∀ h : ℝ, 1 ≤ h → x + h ≤ 3 * X → (∀ m ∈ s0, (m : ℝ) ≠ x + h) →
      ‖uSlab (dpolyA a s0) x h T - 2 * (Real.pi : ℂ) * I * shortSum a s0 x h‖
        ≤ 2 * (18 * (Real.pi + 2 * Real.log (1 + T))
            + (48 * X / T) * (1 + Real.log (3 * X))) := by
    intro h hh hxh hne
    have hh0 : (0 : ℝ) < h := by linarith
    have hcol := Aperron_short_interval_collapsed_wide a s0 hX hh0 hT hx hxh ha hrange hne_x hne
    rw [hobj h]
    simp only [shortSum]
    rw [← residue_diff_eq_shortInterval a s0 hh0 hpos hne_x hne]
    exact hcol
  have hg1 := hgap h₁ hh1 hxh1 hne_1
  have hg2 := hgap h₂ hh2 hxh2 hne_2
  have hkey : ((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ T
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ T
        - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)
      = ((1 / h₁ : ℝ) : ℂ)
          * (uSlab (dpolyA a s0) x h₁ T - 2 * (Real.pi : ℂ) * I * shortSum a s0 x h₁)
        - ((1 / h₂ : ℝ) : ℂ)
          * (uSlab (dpolyA a s0) x h₂ T - 2 * (Real.pi : ℂ) * I * shortSum a s0 x h₂) := by
    ring
  rw [hkey]
  have hn1 : ‖((1 / h₁ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h₁),
      div_le_one (by linarith)]
    linarith
  have hn2 : ‖((1 / h₂ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h₂),
      div_le_one (by linarith)]
    linarith
  have hmulle : ∀ (c g : ℂ) (B : ℝ), ‖c‖ ≤ 1 → ‖g‖ ≤ B → ‖c * g‖ ≤ B := by
    intro c g B hc hg
    rw [norm_mul]
    calc ‖c‖ * ‖g‖ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ = ‖g‖ := one_mul _
      _ ≤ B := hg
  refine le_trans (norm_sub_le _ _) ?_
  have p1 := hmulle _ _ _ hn1 hg1
  have p2 := hmulle _ _ _ hn2 hg2
  linarith

/-- **Lemma 14 in the frozen `Sⱼ` form with a fully explicit Perron defect.**  The `Eper`
datum of `lemma14_shortInterval_of_perron` discharged on the *whole* interval `[X,2X]` by
`perron_gap_collapsed_wide` at the pinned truncation `T = 2X/h₁` (`48X/T = 24h₁`):

`Eper = 4·(18·(π + 2·log(1 + 2X/h₁)) + 24·h₁·(1 + log 3X))`.

The a.e. quantifier is exactly what carries the boundary guards (`perron_guards_ae`: they fail
only on the finite set `⋃_{m∈s0}{m, m−h₁, m−h₂}`), and the wide collapse is exactly what
removes the top-edge exclusion `x ∈ [2X−h₂, 2X]`.

**Honest size.**  This closes the `Sⱼ` form *structurally* (every hypothesis discharged, whole
interval, absolute constants), but `Eper ≍ h₁·log X` is far larger than the three main terms:
the instance is quantitatively vacuous until the Perron defect is removed uniformly in `x`
(the `A3a-R1` residual; `perron_gap_tendsto` below is its per-point half). -/
theorem lemma14_shortInterval_concrete (a : ℕ → ℂ) (s0 : Finset ℕ) {X h₁ h₂ Msup : ℝ}
    (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ h₂)
    (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hMsup : ∀ T : ℝ, X / h₁ ≤ T →
      X / h₁ / T * ((∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2) ≤ Msup) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)
      ≤ 1 / (2 * Real.pi ^ 2) * ((2000 + 820 * Real.pi) * ((Real.log X) ^ (-(14 / 45 : ℝ))
          + ((∫ t in ((Real.log X) ^ (1 / 45 : ℝ))..(X / h₁), ‖dpolyA a s0 t‖ ^ 2)
              + ∫ t in (-(X / h₁))..(-((Real.log X) ^ (1 / 45 : ℝ))), ‖dpolyA a s0 t‖ ^ 2)
          + Msup)
        + (4 * (18 * (Real.pi + 2 * Real.log (1 + 2 * (X / h₁)))
            + 24 * h₁ * (1 + Real.log (3 * X)))) ^ 2) := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : (2 : ℝ) ≤ X := le_trans he2 hX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hh1' : (0 : ℝ) < h₁ := by linarith
  have hh2 : (1 : ℝ) ≤ h₂ := le_trans hh1 hh12
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1) hX
  have hLinv1 : (Real.log X) ^ (-(1 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hh2XX : h₂ ≤ X := by nlinarith [hh2X, hLinv1, hXpos]
  have hTpos : (0 : ℝ) < 2 * (X / h₁) := by positivity
  refine lemma14_shortInterval_of_perron a s0 hX hh1 hh12 hh2X ha hrange hMsup ?_
  have hguards := perron_guards_ae s0 h₁ h₂ (volume.restrict (Set.Icc X (2 * X)))
  have hmem : ∀ᵐ x ∂(volume.restrict (Set.Icc X (2 * X))), x ∈ Set.Icc X (2 * X) :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  filter_upwards [hguards, hmem] with x hg hxmem
  obtain ⟨g0, g1, g2⟩ := hg
  rw [Set.mem_Icc] at hxmem
  have hbnd := perron_gap_collapsed_wide a s0 (T := 2 * (X / h₁)) hX1 hh1 hh2 hTpos
    hxmem.1 (by linarith [hxmem.2] : x + h₁ ≤ 3 * X)
    (by linarith [hxmem.2] : x + h₂ ≤ 3 * X) ha hrange g0 g1 g2
  have heq : 48 * X / (2 * (X / h₁)) = 24 * h₁ := by
    field_simp
    ring
  rwa [heq] at hbnd

/-! ## P2 — `A3a-R1`: the per-point Perron limit `T → ∞` -/

/-- The **per-point Perron constant** `C(y) = ∑_{m ∈ s0} ‖aₘ‖·2(y/m)ᶜ/|log(y/m)|` — the
`T`-free half of the truncated-Perron decay branch (`perron_trunc`).  Finite for every `y`
off the support; it blows up as `y` approaches an index `m` (there `1/|log(y/m)| ~ m/|y−m|`),
which is precisely why the collapsed (uniform) bound trades it for the `log(1+T)` crossover
branch. -/
def perronConst (a : ℕ → ℂ) (s0 : Finset ℕ) (y c : ℝ) : ℝ :=
  ∑ m ∈ s0, ‖a m‖ * (2 * (y / (m : ℝ)) ^ c / |Real.log (y / (m : ℝ))|)

lemma perronConst_nonneg (a : ℕ → ℂ) (s0 : Finset ℕ) {y c : ℝ} (hy : 0 < y)
    (hpos : ∀ m ∈ s0, 0 < m) : 0 ≤ perronConst a s0 y c := by
  refine Finset.sum_nonneg fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos m hm
  have h1 : (0 : ℝ) < (y / (m : ℝ)) ^ c := Real.rpow_pos_of_pos (div_pos hy hm0) c
  exact mul_nonneg (norm_nonneg _) (div_nonneg (by linarith) (abs_nonneg _))

/-- The `min`-device sum, bounded by its **decay branch**: `≤ C(y)/T`.  This is the step the
zone collapse gives up (it takes the crossover branch on the near band); keeping the decay
branch everywhere is what makes the error vanish in `T` at fixed `y`. -/
private lemma min_sum_le_perronConst (a : ℕ → ℂ) (s0 : Finset ℕ) {y c T : ℝ}
    (hy : 0 < y) (hpos : ∀ m ∈ s0, 0 < m) :
    ∑ m ∈ s0, ‖a m‖ * (2 * (y / (m : ℝ)) ^ c
        * min (Real.pi + 2 * Real.log (1 + T / c)) (1 / (T * |Real.log (y / (m : ℝ))|)))
      ≤ perronConst a s0 y c / T := by
  rw [perronConst, Finset.sum_div]
  refine Finset.sum_le_sum fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos m hm
  have h1 : (0 : ℝ) < (y / (m : ℝ)) ^ c := Real.rpow_pos_of_pos (div_pos hy hm0) c
  have hstep : ‖a m‖ * (2 * (y / (m : ℝ)) ^ c
        * min (Real.pi + 2 * Real.log (1 + T / c)) (1 / (T * |Real.log (y / (m : ℝ))|)))
      ≤ ‖a m‖ * (2 * (y / (m : ℝ)) ^ c * (1 / (T * |Real.log (y / (m : ℝ))|))) := by
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
  refine hstep.trans (le_of_eq ?_)
  ring

/-- **`A3a-R1` — the truncated-Perron error decays in `T` at fixed `y`.**  For `y > 0` off the
support (`(m:ℝ) ≠ y`), the *non-collapsed* representation error of `Aperron_representation`
obeys `‖E(y,T)‖ ≤ perronConst a s0 y c / T` — an explicit bound **decreasing in `T`**.  (The
collapsed bound of `perron_sum_error_collapsed` cannot decay: its near-diagonal branch grows
like `log T`; the decay is bought with `y`-dependence.) -/
theorem Aperron_error_le_of_T (a : ℕ → ℂ) (s0 : Finset ℕ) {y c T : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hpos : ∀ m ∈ s0, 0 < m) (hne : ∀ m ∈ s0, (m : ℝ) ≠ y) :
    ‖(I * ∫ v in (-T)..T, (∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
          * (y : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I))
        - 2 * (Real.pi : ℂ) * I * ∑ m ∈ s0, a m * (if 1 < y / m then (1 : ℂ) else 0)‖
      ≤ perronConst a s0 y c / T :=
  (Aperron_representation a s0 hy hc hT hpos hne).trans (min_sum_le_perronConst a s0 hy hpos)

/-- **The `ε`-form of the Perron limit.**  For every `ε > 0` there is a threshold `T₀ > 0`
beyond which the truncated-Perron error at `y` is `≤ ε`: take `T₀ = max 1 (C(y)/ε)`. -/
theorem Aperron_error_small (a : ℕ → ℂ) (s0 : Finset ℕ) {y c ε : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hε : 0 < ε)
    (hpos : ∀ m ∈ s0, 0 < m) (hne : ∀ m ∈ s0, (m : ℝ) ≠ y) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ‖(I * ∫ v in (-T)..T, (∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
            * (y : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I))
          - 2 * (Real.pi : ℂ) * I * ∑ m ∈ s0, a m * (if 1 < y / m then (1 : ℂ) else 0)‖
        ≤ ε := by
  refine ⟨max 1 (perronConst a s0 y c / ε), lt_of_lt_of_le one_pos (le_max_left _ _),
    fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  refine (Aperron_error_le_of_T a s0 hy hc hT0 hpos hne).trans ?_
  have hCe : perronConst a s0 y c / ε ≤ T := le_trans (le_max_right _ _) hT
  rw [div_le_iff₀ hε] at hCe
  rw [div_le_iff₀ hT0]
  linarith

/-- **The classical truncated-Perron limit, per point** (`A3a-R1`).  For `y > 0` off the
support, the truncated critical-line integral converges as `T → ∞` to `2πi` times the
arithmetic partial sum `∑_{m < y} aₘ`.  Squeeze on `Aperron_error_le_of_T`'s `C(y)/T`. -/
theorem Aperron_tendsto (a : ℕ → ℂ) (s0 : Finset ℕ) {y c : ℝ}
    (hy : 0 < y) (hc : 0 < c)
    (hpos : ∀ m ∈ s0, 0 < m) (hne : ∀ m ∈ s0, (m : ℝ) ≠ y) :
    Filter.Tendsto (fun T : ℝ => I * ∫ v in (-T)..T,
        (∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
          * (y : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I))
      Filter.atTop
      (nhds (2 * (Real.pi : ℂ) * I * ∑ m ∈ s0, a m * (if 1 < y / m then (1 : ℂ) else 0))) := by
  have hg0 : Filter.Tendsto (fun T : ℝ => perronConst a s0 y c / T) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hg0
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
  exact Aperron_error_le_of_T a s0 hy hc hT hpos hne

/-! ## P3 — the per-`x` Lemma-14 gap -/

/-- **The short-interval Perron gap at fixed `x`, decaying in `T`.**  Under the boundary
guards, `‖Uⱼ(x,T) − 2πi·Sⱼ(x)‖ ≤ (C(x+h) + C(x))/T`. -/
theorem uSlab_gap_le_of_T (a : ℕ → ℂ) (s0 : Finset ℕ) {x h T : ℝ}
    (hx : 0 < x) (hh : 0 < h) (hT : 0 < T) (hpos : ∀ m ∈ s0, 0 < m)
    (hne_x : ∀ m ∈ s0, (m : ℝ) ≠ x) (hne_xh : ∀ m ∈ s0, (m : ℝ) ≠ x + h) :
    ‖uSlab (dpolyA a s0) x h T - 2 * (Real.pi : ℂ) * I * shortSum a s0 x h‖
      ≤ (perronConst a s0 (x + h) 1 + perronConst a s0 x 1) / T := by
  have hxh : (0 : ℝ) < x + h := by linarith
  have hobj : uSlab (dpolyA a s0) x h T
      = I * ∫ v in (-T)..T,
          (∑ m ∈ s0, a m / (m : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I))
            * (((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I)
              - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I)) / ((1 : ℂ) + (v : ℂ) * I) := by
    rw [uSlab]
    congr 1
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    simp only [dpolyA, uKernel]
    rw [mul_div_assoc]
  have hmain := Aperron_short_interval a s0 (c := 1) hx hh one_pos hT hpos hne_x hne_xh
  rw [hobj]
  simp only [shortSum]
  rw [← residue_diff_eq_shortInterval a s0 hh hpos hne_x hne_xh]
  refine hmain.trans ?_
  have h1 := min_sum_le_perronConst a s0 (c := 1) (T := T) hxh hpos
  have h2 := min_sum_le_perronConst a s0 (c := 1) (T := T) hx hpos
  rw [add_div]
  linarith

/-- **The Lemma-14 Perron gap at fixed `x`, decaying in `T`** — the weighted difference form
consumed by `lemma14_shortInterval_of_perron`.  The constant is `x`-dependent (it blows up as
`x` approaches an index or an index minus `hⱼ`), so this does **not** by itself give a uniform
`Eper → 0`; that needs the mean-square-in-`x` treatment of `C(x)`. -/
theorem perron_gap_le_of_T (a : ℕ → ℂ) (s0 : Finset ℕ) {x h₁ h₂ T : ℝ}
    (hx : 0 < x) (hh1 : 1 ≤ h₁) (hh2 : 1 ≤ h₂) (hT : 0 < T) (hpos : ∀ m ∈ s0, 0 < m)
    (hne_x : ∀ m ∈ s0, (m : ℝ) ≠ x)
    (hne_1 : ∀ m ∈ s0, (m : ℝ) ≠ x + h₁) (hne_2 : ∀ m ∈ s0, (m : ℝ) ≠ x + h₂) :
    ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ T
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ T
        - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)‖
      ≤ (perronConst a s0 (x + h₁) 1 + perronConst a s0 (x + h₂) 1
          + 2 * perronConst a s0 x 1) / T := by
  have hg1 := uSlab_gap_le_of_T a s0 hx (by linarith : (0 : ℝ) < h₁) hT hpos hne_x hne_1
  have hg2 := uSlab_gap_le_of_T a s0 hx (by linarith : (0 : ℝ) < h₂) hT hpos hne_x hne_2
  have hkey : ((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ T
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ T
        - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)
      = ((1 / h₁ : ℝ) : ℂ)
          * (uSlab (dpolyA a s0) x h₁ T - 2 * (Real.pi : ℂ) * I * shortSum a s0 x h₁)
        - ((1 / h₂ : ℝ) : ℂ)
          * (uSlab (dpolyA a s0) x h₂ T - 2 * (Real.pi : ℂ) * I * shortSum a s0 x h₂) := by
    ring
  rw [hkey]
  have hn1 : ‖((1 / h₁ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h₁),
      div_le_one (by linarith)]
    linarith
  have hn2 : ‖((1 / h₂ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h₂),
      div_le_one (by linarith)]
    linarith
  have hmulle : ∀ (c g : ℂ) (B : ℝ), ‖c‖ ≤ 1 → ‖g‖ ≤ B → ‖c * g‖ ≤ B := by
    intro c g B hc hg
    rw [norm_mul]
    calc ‖c‖ * ‖g‖ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ = ‖g‖ := one_mul _
      _ ≤ B := hg
  refine le_trans (norm_sub_le _ _) ?_
  have p1 := hmulle _ _ _ hn1 hg1
  have p2 := hmulle _ _ _ hn2 hg2
  have hsplit : (perronConst a s0 (x + h₁) 1 + perronConst a s0 (x + h₂) 1
        + 2 * perronConst a s0 x 1) / T
      = (perronConst a s0 (x + h₁) 1 + perronConst a s0 x 1) / T
        + (perronConst a s0 (x + h₂) 1 + perronConst a s0 x 1) / T := by
    ring
  rw [hsplit]
  linarith

/-- **The Lemma-14 Perron gap vanishes as `T → ∞`, at each admissible `x`.**  The honest
`A3a-R1` exit at the per-point level: for fixed `x` obeying the boundary guards the defect
`Eper` can be made arbitrarily small.  The consumer of `lemma14_shortInterval_of_perron`
needs one `T` for a.e. `x ∈ [X,2X]` at once, which this does not supply (see
`perron_gap_le_of_T`'s `x`-dependent constant). -/
theorem perron_gap_tendsto (a : ℕ → ℂ) (s0 : Finset ℕ) {x h₁ h₂ : ℝ}
    (hx : 0 < x) (hh1 : 1 ≤ h₁) (hh2 : 1 ≤ h₂) (hpos : ∀ m ∈ s0, 0 < m)
    (hne_x : ∀ m ∈ s0, (m : ℝ) ≠ x)
    (hne_1 : ∀ m ∈ s0, (m : ℝ) ≠ x + h₁) (hne_2 : ∀ m ∈ s0, (m : ℝ) ≠ x + h₂) :
    Filter.Tendsto (fun T : ℝ => ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ T
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ T
        - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)‖)
      Filter.atTop (nhds 0) := by
  have hg0 : Filter.Tendsto (fun T : ℝ => (perronConst a s0 (x + h₁) 1
      + perronConst a s0 (x + h₂) 1 + 2 * perronConst a s0 x 1) / T) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hg0
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
  exact perron_gap_le_of_T a s0 hx hh1 hh2 hT hpos hne_x hne_1 hne_2

end Salt.MR
