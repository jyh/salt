/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.BoxRows2

/-!
# G-D0WIN2 — the z-DEPENDENT D0-window + live-box floor (Goldbach keystone design fix)

Design: G-BOXROWS2's flag (the `z ≤ goldCut^{1/8}` blocker).  The landed
`gold_kfloor_live_annulus`/`gold_d0_window_annulus` (D0Win) carry a `7/16` floor whose hypothesis
`hz : (z : ℝ) ≤ (goldCut Ne (k+1))^{1/8}` is **FALSE at the operating point on every annulus**:
`z = opZ N ≈ N^{1/8}` is GLOBAL, while `goldCut Ne (k+1) ≤ N/2`, so `z^8 > N/2 ≥ goldCut` always
(G-BOXROWS2's verified arithmetic).  The house-adjudicated fix — NO operating-point change — is the
**z-dependent floor**: instead of substituting the false `z ≤ x^{1/8}`, keep `z` and read the honest
live-box geometry directly.

The three keystones, mirroring D0Win §1–§3 with the `7/16·log x − 7` floor replaced by
`W_honest := ½·(log(goldCut Ne (k+1)) − log(8·z))`:

* §0 **`gold_live_annulus_lower`** — the honest live-box lower bound `z·y² < 4·goldCut Ne (k+1)`,
  re-derived EXACTLY from the live conditions (the boundary `F`-floor `z·y < 2^{i+1}`, the corner
  `2^i·2^{k'} ≤ goldCut`, and the carrier-live `2^i < z·pieceN k' + 1`).  This is what makes the
  §2 ratio hypothesis satisfiable at op (`goldCut ≳ N^{19/24} ≫ (8z)^6 ≈ 8^6·N^{3/4}` for
  `N ≥ 2^432`, astronomically below the tower threshold `exp(10^9) ≤ goldCut`).
* §1 **`gold_kfloor_live_z`** — the z-dependent live floor `(goldCut Ne (k+1)/(8z))^{1/2} ≤ 2^{k'}`,
  derived from the SAME live geometry as `gold_kfloor_live_annulus` but WITHOUT the false `hz`
  substitution: `x/8 < z·(2^{k'})²` gives `x/(8z) < (2^{k'})²` directly.  Hypotheses are purely
  geometric (no z-vs-x bound), so trivially satisfiable at op.
* §2 **`gold_d0_window_z`** — the 9-conjunct `D0`-window at `W_honest`.  Character-for-character
  `gold_d0_window_annulus`'s conclusion with the floor conjunct `D0 ≤ x^{7/16}/8` replaced by
  `D0 ≤ (x/(8z))^{1/2}`.  The ratio conjunct needs `goldCut ≥ (8z)^6` — stated as the hypothesis
  `hz_ratio : 6·log(8z) + 15 ≤ log(goldCut Ne (k+1))`, discharged from `gold_live_annulus_lower` +
  the op scale facts (the enormous `N^{1/24}` margin).
* §3 **`gold_box_price_engine_at_live_z`** — the composition: `gold_box_price_engine`'s nine `hD0*`
  rows discharged from §2 (fed the §1 floor) at a live annulus.  The FALSE `hz` is gone; replaced by
  `hz1 : 1 ≤ z` (trivial at op) and `hz_ratio` (op-margin `N^{1/24}`).
* §4 the BoxRows3 handoff — the DEAD/LIVE dichotomy + slot mapping with the z-dependent forms.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 0. `gold_live_annulus_lower` — the honest live-box lower bound `z·y² < 4·goldCut` -/

/-- **`gold_live_annulus_lower` (§0).**  For a LIVE box (`hlive : 2^i < z·pieceN k' + 1`) in the
annulus boundary, `z·y² < 4·goldCut Ne (k+1)`.  This is the honest live-box lower bound: the
boundary `F`-floor `z·y < 2^{i+1}` and the carrier-live clause combine (via the corner
`2^i·2^{k'} ≤ goldCut`) to force `goldCut > z·y²/4`.  At op (`z ≈ N^{1/8}`, `y ≈ N^{1/3}`) this
reads `goldCut ≳ N^{19/24}`, making the §2 ratio hypothesis satisfiable with an `N^{1/24}`
margin.  Chain: `y < 2·2^{k'}` (from `z·y < 2^{i+1}`, `2^i ≤ z·2^{k'}`) and `z·y < 2·2^i`, so
`z·y² = (z·y)·y < (2·2^i)·(2·2^{k'}) = 4·2^i·2^{k'} ≤ 4·goldCut`. -/
theorem gold_live_annulus_lower {Ne z y k' k i K : ℕ} (hNe : 2 ≤ Ne)
    (hi : i ∈ dyadicBoundary (pieceN k') (pieceM k') (goldCut Ne k) (goldCut Ne (k + 1))
      (z * y) K)
    (hlive : 2 ^ i < z * pieceN k' + 1) :
    z * (y * y) < 4 * goldCut Ne (k + 1) := by
  rw [dyadicBoundary, Finset.mem_filter] at hi
  obtain ⟨-, hcorner, hfloorF, -⟩ := hi
  -- corner: `2^i·2^{k'} ≤ goldCut Ne (k+1)`.
  have hpk : pieceN k' + 1 = 2 ^ k' := by
    have h1 : (1 : ℕ) ≤ 2 ^ k' := Nat.one_le_pow _ _ (by norm_num)
    unfold pieceN; omega
  rw [hpk] at hcorner
  have h2i : (1 : ℕ) ≤ 2 ^ i := Nat.one_le_pow _ _ (by norm_num)
  have hgc1 : 1 ≤ goldCut Ne (k + 1) := one_le_goldCut hNe (k + 1)
  -- F-floor: `z·y < 2·2^i`.
  have hfloor2 : z * y < 2 * 2 ^ i := by
    have he : (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
    omega
  -- carrier-live: `2^i ≤ z·2^{k'}`.
  have hlive2 : 2 ^ i ≤ z * 2 ^ k' := by
    have hle : pieceN k' ≤ 2 ^ k' := by unfold pieceN; omega
    calc 2 ^ i ≤ z * pieceN k' := by omega
      _ ≤ z * 2 ^ k' := Nat.mul_le_mul (le_refl z) hle
  -- `y < 2·2^{k'}`.
  have hylt : y < 2 * 2 ^ k' := by
    have hchain : z * y < z * (2 * 2 ^ k') := by
      calc z * y < 2 * 2 ^ i := hfloor2
        _ ≤ 2 * (z * 2 ^ k') := by omega
        _ = z * (2 * 2 ^ k') := by ring
    exact lt_of_mul_lt_mul_left hchain (Nat.zero_le z)
  rcases Nat.eq_zero_or_pos y with hy0 | hypos
  · have hz0 : z * (y * y) = 0 := by rw [hy0]; ring
    omega
  · have hs1 : z * (y * y) < (2 * 2 ^ i) * y := by
      have he : z * (y * y) = (z * y) * y := by ring
      rw [he]; exact mul_lt_mul_of_pos_right hfloor2 hypos
    have hs2 : (2 * 2 ^ i) * y ≤ (2 * 2 ^ i) * (2 * 2 ^ k') :=
      Nat.mul_le_mul (le_refl _) (le_of_lt hylt)
    have hs3 : (2 * 2 ^ i) * (2 * 2 ^ k') = 4 * (2 ^ i * 2 ^ k') := by ring
    have hs4 : 4 * (2 ^ i * 2 ^ k') ≤ 4 * goldCut Ne (k + 1) :=
      Nat.mul_le_mul (le_refl 4) hcorner
    omega

/-! ## 1. `gold_kfloor_live_z` — the z-dependent live floor (deliverable 1)

The `gold_kfloor_live_annulus` mirror WITHOUT the false `hz : z ≤ goldCut^{1/8}` substitution.  The
live geometry gives `x/8 < z·(2^{k'})²` (`x := goldCut Ne (k+1)`), unconditionally; dividing by
`8z` (live boxes force `z ≥ 1`) yields `x/(8z) < (2^{k'})²`, i.e. `(x/(8z))^{1/2} ≤ 2^{k'}`.  This
is the honest z-dependent floor `√(goldCut Ne (k+1)/(8·z)) ≤ 2^{k'}` the §2 window consumes.  No
z-vs-x hypothesis, so satisfiable at op with `z = opZ N` for free (the entire point of the fix). -/

/-- **`gold_kfloor_live_z` (§1, the crux).**  For a LIVE box (`hlive : 2^i < z·pieceN k' + 1`) in
the annulus boundary, `(goldCut Ne (k+1)/(8·z))^{1/2} ≤ 2^{k'}`.  The `gold_kfloor_live_annulus`
mirror with the false `hz` DROPPED: keep `z`, read `x/8 < z·(2^{k'})²` off the geometry, divide by
`8z` (`z ≥ 1` forced by `hlive`).  Margin: the derivation is a strict inequality throughout. -/
theorem gold_kfloor_live_z {Ne z y k' k i K : ℕ} (hNe : 2 ≤ Ne)
    (hi : i ∈ dyadicBoundary (pieceN k') (pieceM k') (goldCut Ne k) (goldCut Ne (k + 1))
      (z * y) K)
    (hlive : 2 ^ i < z * pieceN k' + 1) :
    ((goldCut Ne (k + 1) : ℝ) / (8 * (z : ℝ))) ^ ((1 : ℝ) / 2) ≤ ((2 ^ k' : ℕ) : ℝ) := by
  -- annulus cutoff + pieceM bound: `goldCut Ne k < 4·(2^i·2^{k'})`.
  have hcut := (gold_box_XM_scale hi).1
  have hMub : pieceM k' ≤ 2 * 2 ^ k' := pieceM_le_two_pow k'
  have hXMub : (2 ^ (i + 1) - 1) * pieceM k' ≤ 4 * (2 ^ i * 2 ^ k') := by
    calc (2 ^ (i + 1) - 1) * pieceM k'
        ≤ 2 ^ (i + 1) * (2 * 2 ^ k') := Nat.mul_le_mul (Nat.sub_le _ _) hMub
      _ = 4 * (2 ^ i * 2 ^ k') := by rw [pow_succ]; ring
  have hGcut : goldCut Ne k < 4 * (2 ^ i * 2 ^ k') := lt_of_lt_of_le hcut hXMub
  have hle := goldCut_succ_le_two_mul Ne k
  have hxN : goldCut Ne (k + 1) < 8 * (2 ^ i * 2 ^ k') := by omega
  have hxpos : (0 : ℝ) < (goldCut Ne (k + 1) : ℝ) := by
    have h1 : (1 : ℕ) ≤ goldCut Ne (k + 1) := one_le_goldCut hNe (k + 1)
    exact_mod_cast (by omega : (0 : ℕ) < goldCut Ne (k + 1))
  set x := goldCut Ne (k + 1) with hxdef
  -- carrier-live gives `2^i ≤ z·2^{k'}` (Nat).
  have hliveN : 2 ^ i ≤ z * 2 ^ k' := by
    have hN : pieceN k' = 2 ^ k' - 1 := rfl
    rw [hN] at hlive
    calc 2 ^ i ≤ z * (2 ^ k' - 1) := by omega
      _ ≤ z * 2 ^ k' := Nat.mul_le_mul (le_refl z) (Nat.sub_le _ _)
  -- real forms.
  have hxR : (x : ℝ) < 8 * ((2 : ℝ) ^ i * (2 : ℝ) ^ k') := by exact_mod_cast hxN
  have hliveR : (2 : ℝ) ^ i ≤ (z : ℝ) * (2 : ℝ) ^ k' := by exact_mod_cast hliveN
  have hknn : (0 : ℝ) ≤ (2 : ℝ) ^ k' := by positivity
  have hcutR : (x : ℝ) / 8 < (2 : ℝ) ^ i * (2 : ℝ) ^ k' := by linarith [hxR]
  have hProd : (x : ℝ) / 8 < (z : ℝ) * ((2 : ℝ) ^ k' * (2 : ℝ) ^ k') := by
    nlinarith [hcutR, mul_le_mul_of_nonneg_right hliveR hknn]
  -- `z ≥ 1` is forced: `x/8 > 0` needs the RHS positive.
  have hzRpos : (0 : ℝ) < (z : ℝ) := by
    rcases Nat.eq_zero_or_pos z with hz0 | hzp
    · exfalso; rw [hz0] at hProd; simp at hProd; linarith [hxpos]
    · exact_mod_cast hzp
  have h8zpos : (0 : ℝ) < 8 * (z : ℝ) := mul_pos (by norm_num) hzRpos
  -- `x/(8z) < (2^{k'})²`.
  have hProd8 : (x : ℝ) < 8 * ((z : ℝ) * ((2 : ℝ) ^ k' * (2 : ℝ) ^ k')) := by linarith [hProd]
  have hdiv : (x : ℝ) / (8 * (z : ℝ)) < (2 : ℝ) ^ k' * (2 : ℝ) ^ k' := by
    rw [div_lt_iff₀ h8zpos]; nlinarith [hProd8]
  -- `(x/(8z))^{1/2} ≤ 2^{k'}`.
  set f := ((x : ℝ) / (8 * (z : ℝ))) ^ ((1 : ℝ) / 2) with hfdef
  have hfnn : (0 : ℝ) ≤ f := Real.rpow_nonneg (le_of_lt (div_pos hxpos h8zpos)) _
  have hk'pos : (0 : ℝ) < (2 : ℝ) ^ k' := by positivity
  have hf2 : f * f = (x : ℝ) / (8 * (z : ℝ)) := by
    rw [hfdef, ← Real.rpow_add (div_pos hxpos h8zpos),
      show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one]
  rw [show ((2 ^ k' : ℕ) : ℝ) = (2 : ℝ) ^ k' by push_cast; ring]
  nlinarith [hf2, hdiv, hfnn, hk'pos.le, show (0 : ℝ) ≤ f + (2 : ℝ) ^ k' by positivity]

/-! ## 2. `gold_d0_window_z` — the z-dependent D0-window (deliverable 2)

`gold_d0_window_annulus` re-run with `W := ½·(log x − log(8z))` (`x := goldCut Ne (k+1)`) replacing
`7/16·log x − 7`.  The floor hypothesis becomes `hNfloor : (x/(8z))^{1/2} ≤ Nb` (the §1 floor), and
the floor conjunct becomes `D0 ≤ (x/(8z))^{1/2}`; every other conjunct is character-for-character
`gold_d0_window_annulus`'s.  The ONLY new numeric input is the ratio hypothesis
`hz_ratio : 6·log(8z) + 15 ≤ log x` (equivalently `x ≥ (8z)^6·e^{15}`, the D0-window's `L ≤ 12/5·W`
requirement), discharged at op from `gold_live_annulus_lower` + the op scales (margin `N^{1/24}`).

Constants re-verified vs `gold_d0_window_annulus`: the `12/5` ratio (`hLW`, now EXACT:
`12/5·W = log x + 3 ≥ L`), `4·(12/5)^{17}` tower absorb (`hW4`), `W ≥ 1296` (`hW1296`), the
`W^{18} ≤ e^W` quad (`hexpW`, unchanged), and `e^W = (x/(8z))^{1/2}` (EXACT, replacing the twin's
`e^W ≤ x^{7/16}/8` with its `e^7 ≥ 8` slack).  The `L`-window (`L^{15}`,`L^{17}`,`L^{18}`,`262144`)
and the dyadic window are `L`-only, hence unchanged. -/

/-- **`gold_d0_window_z` (§2).**  `gold_d0_window_annulus` at the z-dependent floor
`W := ½(log(goldCut Ne (k+1)) − log(8z))`.  Conclusion character-for-character
`gold_d0_window_annulus`'s with the floor conjunct `D0 ≤ x^{7/16}/8` replaced by
`D0 ≤ (x/(8z))^{1/2}` and `hNfloor` the §1 floor.  The ratio conjunct is discharged from
`hz_ratio : 6·log(8z) + 15 ≤ log x` (`x ≥ (8z)^6·e^{15}`). -/
theorem gold_d0_window_z {Ne Nb M X k z : ℕ}
    (hx : Real.exp (10 ^ 9) ≤ (goldCut Ne (k + 1) : ℝ))
    (hz1 : 1 ≤ z)
    (hz_ratio : 6 * Real.log (8 * (z : ℝ)) + 15 ≤ Real.log (goldCut Ne (k + 1) : ℝ))
    (hNfloor : ((goldCut Ne (k + 1) : ℝ) / (8 * (z : ℝ))) ^ ((1 : ℝ) / 2) ≤ (Nb : ℝ))
    (hXMlo : goldCut Ne k < X * M)
    (hXMhi : X * M ≤ 4 * goldCut Ne (k + 1)) :
    ∃ D0 k0 : ℕ, D0 = 2 ^ k0 ∧ 2 ≤ D0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((15 : ℝ)) ≤ 2 * (2 : ℝ) ^ k0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((17 : ℝ)) ≤ (D0 : ℝ)
      ∧ (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((18 : ℝ))
      ∧ (D0 : ℝ) ≤ (Real.log (Nb : ℝ)) ^ ((18 : ℝ))
      ∧ (∀ LE : ℝ, Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * LE → (D0 : ℝ) ≤ LE ^ ((18 : ℝ)))
      ∧ (D0 : ℝ) ≤ ((goldCut Ne (k + 1) : ℝ) / (8 * (z : ℝ))) ^ ((1 : ℝ) / 2)
      ∧ D0 ≤ Nb := by
  -- the half-bound `x/2 + 1 ≤ X·M` (dissolves the off-by-one).
  have hle := goldCut_succ_le_two_mul Ne k
  have h2 : goldCut Ne (k + 1) / 2 + 1 ≤ X * M := by omega
  set x := goldCut Ne (k + 1) with hxdef
  -- ① scale facts: `t ≥ 10^9`, `x ≥ 2`.
  have h109 : (10 : ℝ) ^ 9 = 1000000000 := by norm_num
  have ht : (10 : ℝ) ^ 9 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by
    have h1 := Real.add_one_le_exp ((10 : ℝ) ^ 9)
    linarith
  have hx2 : 2 ≤ x := by exact_mod_cast hxR2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  -- ② the scale facts (annulus-native).
  have hXM4x : X * M ≤ 4 * x := hXMhi
  have hXMposN : 0 < X * M := by omega
  have hXMposR : (0 : ℝ) < (X : ℝ) * (M : ℝ) := by exact_mod_cast hXMposN
  have hXM4xR : (X : ℝ) * (M : ℝ) ≤ 4 * (x : ℝ) := by exact_mod_cast hXM4x
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  -- ③ `t − 1 ≤ L ≤ t + 3`.
  have hL_lo : Real.log x - 1 ≤ L := by
    have h1 : x < (x / 2 + 1) * 2 := by omega
    have h1R : (x : ℝ) < ((x / 2 + 1 : ℕ) : ℝ) * 2 := by exact_mod_cast h1
    have h2R : ((x / 2 + 1 : ℕ) : ℝ) ≤ (X : ℝ) * (M : ℝ) := by exact_mod_cast h2
    push_cast at h1R h2R
    have hhalf : (x : ℝ) / 2 < (X : ℝ) * (M : ℝ) := by linarith
    have hlog : Real.log ((x : ℝ) / 2) ≤ L := Real.log_le_log (by linarith) hhalf.le
    rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)] at hlog
    have h2log : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith
  have hL_up : L ≤ Real.log x + 3 := by
    have h1 : L ≤ Real.log (4 * (x : ℝ)) := Real.log_le_log hXMposR hXM4xR
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hxpos)] at h1
    have h4log : Real.log 4 ≤ 3 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
    linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hLnn : (0 : ℝ) ≤ L := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hL4 : (4 : ℝ) ≤ L := by linarith
  have hL20 : (1048576 : ℝ) ≤ L := by linarith
  -- ④ the z-dependent block-floor log: `W := ½(log x − log(8z)) ≤ log Nb`.
  have h8zpos : (0 : ℝ) < 8 * (z : ℝ) := by
    have : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
    positivity
  set W : ℝ := (Real.log x - Real.log (8 * (z : ℝ))) / 2 with hWdef
  have hfloorpos : (0 : ℝ) < ((x : ℝ) / (8 * (z : ℝ))) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (div_pos hxpos h8zpos) _
  have hWeq : W = Real.log (((x : ℝ) / (8 * (z : ℝ))) ^ ((1 : ℝ) / 2)) := by
    rw [Real.log_rpow (div_pos hxpos h8zpos),
      Real.log_div (ne_of_gt hxpos) (ne_of_gt h8zpos), hWdef]; ring
  have hWlogN : W ≤ Real.log Nb := by rw [hWeq]; exact Real.log_le_log hfloorpos hNfloor
  have heWfloor : Real.exp W = ((x : ℝ) / (8 * (z : ℝ))) ^ ((1 : ℝ) / 2) := by
    rw [hWeq, Real.exp_log hfloorpos]
  -- W lower bounds from the ratio hypothesis + tower threshold.
  have hWlb : (5 * Real.log x + 15) / 12 ≤ W := by rw [hWdef]; linarith [hz_ratio]
  have hWpos : (0 : ℝ) < W := by linarith [hWlb, ht]
  have hW1296 : (1296 : ℝ) ≤ W := by linarith [hWlb, ht]
  have hLW : L ≤ 12 / 5 * W := by linarith [hL_up, hWlb]
  have hW4 : 4 * ((12 : ℝ) / 5) ^ ((17 : ℝ)) ≤ W := by
    have hc : ((12 : ℝ) / 5) ^ ((17 : ℝ)) = ((12 : ℝ) / 5) ^ (17 : ℕ) := by
      rw [show ((17 : ℝ)) = ((17 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hnum : 4 * ((12 : ℝ) / 5) ^ (17 : ℕ) ≤ (5 * 10 ^ 9 + 15) / 12 := by norm_num
    rw [hc]; linarith [hWlb, ht]
  -- ⑤ the dyadic window: `D0 = 2^{k0} ∈ [L^{17}, 4·L^{17}]`.
  have hL17_1 : (1 : ℝ) ≤ L ^ ((17 : ℝ)) := Real.one_le_rpow hL1 (by norm_num)
  have hL17_2 : (2 : ℝ) ≤ L ^ ((17 : ℝ)) := by
    calc (2 : ℝ) ≤ L := by linarith
      _ = L ^ ((1 : ℝ)) := (Real.rpow_one L).symm
      _ ≤ L ^ ((17 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  obtain ⟨n, hn_ge, hn_le⟩ :
      ∃ n : ℕ, L ^ ((17 : ℝ)) ≤ (n : ℝ) ∧ (n : ℝ) ≤ L ^ ((17 : ℝ)) + 1 :=
    ⟨⌈L ^ ((17 : ℝ))⌉₊, Nat.le_ceil _,
      le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg hLnn _))⟩
  have hn1 : 1 < n := by
    have h1R : (1 : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast h1R
  obtain ⟨k0, hnpow, hpow2n⟩ : ∃ k0 : ℕ, n ≤ 2 ^ k0 ∧ 2 ^ k0 ≤ 2 * n := by
    refine ⟨Nat.clog 2 n, Nat.le_pow_clog (by norm_num) n, ?_⟩
    have hk0pos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) hn1
    have hpow_lt : 2 ^ (Nat.clog 2 n - 1) < n :=
      Nat.pow_pred_clog_lt_self (by norm_num) hn1
    have hsplit : 2 * 2 ^ (Nat.clog 2 n - 1) = 2 ^ Nat.clog 2 n := by
      rw [← pow_succ']
      congr 1
      omega
    rw [← hsplit]
    exact Nat.mul_le_mul (le_refl 2) (le_of_lt hpow_lt)
  have hD0_lo : L ^ ((17 : ℝ)) ≤ ((2 ^ k0 : ℕ) : ℝ) := by
    refine le_trans hn_ge ?_
    exact_mod_cast hnpow
  have hD0_hi : ((2 ^ k0 : ℕ) : ℝ) ≤ 4 * L ^ ((17 : ℝ)) := by
    have h1 : ((2 ^ k0 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hpow2n
    linarith
  have hL18eq : L ^ ((18 : ℝ)) = L * L ^ ((17 : ℝ)) := by
    have hh := Real.rpow_add hLpos 1 17
    rw [Real.rpow_one] at hh
    rw [show (18 : ℝ) = 1 + 17 by norm_num, hh]
  have h17nn : (0 : ℝ) ≤ L ^ ((17 : ℝ)) := Real.rpow_nonneg hLnn _
  -- ⑥ the `hD0N'` leg: `4·L^{17} ≤ W^{18}`.
  have hW18 : 4 * L ^ ((17 : ℝ)) ≤ W ^ ((18 : ℝ)) := by
    have hW17 : L ^ ((17 : ℝ)) ≤ ((12 : ℝ) / 5) ^ ((17 : ℝ)) * W ^ ((17 : ℝ)) := by
      calc L ^ ((17 : ℝ)) ≤ (12 / 5 * W) ^ ((17 : ℝ)) :=
            Real.rpow_le_rpow hLnn hLW (by norm_num)
        _ = ((12 : ℝ) / 5) ^ ((17 : ℝ)) * W ^ ((17 : ℝ)) :=
            Real.mul_rpow (by norm_num) hWpos.le
    have hW18eq : W ^ ((18 : ℝ)) = W * W ^ ((17 : ℝ)) := by
      have hh := Real.rpow_add hWpos 1 17
      rw [Real.rpow_one] at hh
      rw [show (18 : ℝ) = 1 + 17 by norm_num, hh]
    have h17Wnn : (0 : ℝ) ≤ W ^ ((17 : ℝ)) := Real.rpow_nonneg hWpos.le _
    rw [hW18eq]
    calc 4 * L ^ ((17 : ℝ))
        ≤ 4 * (((12 : ℝ) / 5) ^ ((17 : ℝ)) * W ^ ((17 : ℝ))) := by linarith
      _ = (4 * ((12 : ℝ) / 5) ^ ((17 : ℝ))) * W ^ ((17 : ℝ)) := by ring
      _ ≤ W * W ^ ((17 : ℝ)) := mul_le_mul_of_nonneg_right hW4 h17Wnn
  -- ⑦ the `hD0N` leg: `W^{18} ≤ e^W = (x/(8z))^{1/2}`.
  have hexpW : W ^ ((18 : ℝ)) ≤ Real.exp W := by
    have hunn : (0 : ℝ) ≤ W / 36 := by linarith
    have hquad : W ≤ (W / 36) ^ ((2 : ℝ)) := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hexpand : (W / 36) ^ (2 : ℕ) = W * W / 1296 := by ring
      rw [hexpand, le_div_iff₀ (by norm_num : (0 : ℝ) < 1296)]
      have keyq : (0 : ℝ) ≤ (W - 1296) * W := mul_nonneg (by linarith) hWpos.le
      linarith [keyq]
    have hu : W / 36 ≤ Real.exp (W / 36) := by linarith [Real.add_one_le_exp (W / 36)]
    calc W ^ ((18 : ℝ))
        ≤ ((W / 36) ^ ((2 : ℝ))) ^ ((18 : ℝ)) :=
          Real.rpow_le_rpow hWpos.le hquad (by norm_num)
      _ = (W / 36) ^ ((36 : ℝ)) := by
          rw [← Real.rpow_mul hunn]
          norm_num
      _ ≤ (Real.exp (W / 36)) ^ ((36 : ℝ)) := Real.rpow_le_rpow hunn hu (by norm_num)
      _ = Real.exp W := by
          rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
          congr 1
          ring
  have hexp_le : Real.exp W ≤ ((x : ℝ) / (8 * (z : ℝ))) ^ ((1 : ℝ) / 2) := le_of_eq heWfloor
  -- ⑧ emit the rows.
  have hcast : ((2 ^ k0 : ℕ) : ℝ) = (2 : ℝ) ^ k0 := by push_cast; ring
  refine ⟨2 ^ k0, k0, rfl, le_trans (by omega : 2 ≤ n) hnpow, ?_, hD0_lo, ?_, ?_, ?_, ?_, ?_⟩
  · -- `hD0lo_main`, exponent `15`
    have h15 : L ^ ((15 : ℝ)) ≤ L ^ ((17 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h2k0pos : (0 : ℝ) < (2 : ℝ) ^ k0 := by positivity
    calc L ^ ((15 : ℝ)) ≤ L ^ ((17 : ℝ)) := h15
      _ ≤ ((2 ^ k0 : ℕ) : ℝ) := hD0_lo
      _ = (2 : ℝ) ^ k0 := hcast
      _ ≤ 2 * (2 : ℝ) ^ k0 := by linarith
  · -- `hD0` (`D0 ≤ L^{18}`)
    rw [hL18eq]
    have key : (0 : ℝ) ≤ (L - 4) * L ^ ((17 : ℝ)) := mul_nonneg (by linarith) h17nn
    linarith [hD0_hi, key]
  · -- `hD0N'` (`D0 ≤ (log Nb)^{18}`)
    have hmono : W ^ ((18 : ℝ)) ≤ (Real.log Nb) ^ ((18 : ℝ)) :=
      Real.rpow_le_rpow hWpos.le hWlogN (by norm_num)
    linarith [hD0_hi, hW18, hmono]
  · -- `herr_D0E` in the `herr_scale` form
    intro LE hLE
    have hhalfpos : (0 : ℝ) < L / 2 := by linarith
    have hstep : 4 * L ^ ((17 : ℝ)) ≤ (L / 2) ^ ((18 : ℝ)) := by
      have hdiv : (L / 2) ^ ((18 : ℝ)) = L ^ ((18 : ℝ)) / (2 : ℝ) ^ ((18 : ℝ)) :=
        Real.div_rpow hLnn (by norm_num) _
      have h218 : (2 : ℝ) ^ ((18 : ℝ)) = 262144 := by
        rw [show ((18 : ℝ)) = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      rw [hdiv, h218, hL18eq, le_div_iff₀ (by norm_num : (0 : ℝ) < 262144)]
      have key : (0 : ℝ) ≤ (L - 1048576) * L ^ ((17 : ℝ)) := mul_nonneg (by linarith) h17nn
      linarith [key]
    have hmono : (L / 2) ^ ((18 : ℝ)) ≤ LE ^ ((18 : ℝ)) :=
      Real.rpow_le_rpow hhalfpos.le (by linarith) (by norm_num)
    linarith [hD0_hi]
  · -- the z-dependent floor bound (`D0 ≤ (x/(8z))^{1/2}`)
    linarith [hD0_hi, hW18, hexpW, hexp_le]
  · -- `hD0N` (`D0 ≤ Nb`)
    have hfin : ((2 ^ k0 : ℕ) : ℝ) ≤ (Nb : ℝ) := by
      linarith [hD0_hi, hW18, hexpW, hexp_le, hNfloor]
    exact_mod_cast hfin

/-! ## 3. The composition — `gold_box_price_engine`'s D0 rows from the two keystones (deliverable 3)

The shape-lock re-run at the z-dependent floor.  `gold_box_price_engine`'s nine `hD0*` rows are
discharged, at a LIVE annulus box, by `gold_kfloor_live_z` → the floor
`(goldCut Ne (ka+1)/(8z))^{1/2} ≤ 2^{kp}`, fed to `gold_d0_window_z` (via `gold_box_XM_scale`) →
the 9 conjuncts.
The FALSE `hz : z ≤ goldCut^{1/8}` is GONE; replaced by `hz1 : 1 ≤ z` (trivial at op) and
`hz_ratio : 6·log(8z) + 15 ≤ log(goldCut Ne (ka+1))` (satisfiable at op with `N^{1/24}` margin via
`gold_live_annulus_lower`).  Every other slot is byte-identical to
`gold_box_price_engine_at_live_annulus`. -/

/-- **`gold_box_price_engine_at_live_z` (§3).**  `gold_box_price_engine` re-exported with its nine
`hD0*` rows discharged from `gold_d0_window_z` (fed the `gold_kfloor_live_z` floor) at a live
annulus box.  The z-dependent replacement for `gold_box_price_engine_at_live_annulus`: the false
`z ≤ goldCut^{1/8}` is replaced by `hz1`/`hz_ratio`, and the floor `hDge` becomes
`(goldCut Ne (ka+1)/(8z))^{1/2} ≤ D`.  Conclusion byte-identical to the engine slot. -/
theorem gold_box_price_engine_at_live_z :
    ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
      ∀ (x Lb : ℝ) (F : ℕ) (β : ℕ → ℂ) (X M kp D : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ)
        (Kβ Km Kβ' : ℝ) (T₁ T₂ Ne z y K ka i : ℕ),
        2 ≤ Ne →
        i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut Ne ka) (goldCut Ne (ka + 1)) (z * y) K →
        2 ^ i < z * pieceN kp + 1 →
        1 ≤ z →
        6 * Real.log (8 * (z : ℝ)) + 15 ≤ Real.log (goldCut Ne (ka + 1) : ℝ) →
        Real.exp (10 ^ 9) ≤ (goldCut Ne (ka + 1) : ℝ) →
        X = 2 ^ (i + 1) - 1 → M = pieceM kp →
        ((goldCut Ne (ka + 1) : ℝ) / (8 * (z : ℝ))) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) →
        2 ≤ kp →
        (∀ m, ‖β m‖ ≤ 1) → 0 ≤ Kβ → 0 ≤ Km → 0 ≤ Kβ' → N₀ ≤ 2 ^ kp →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (1 ≤ Real.log ((X : ℝ) * (M : ℝ))) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < (2 ^ kp + 1) * (2 ^ kp + 1) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ ((2 ^ kp : ℕ) : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (13 : ℝ)) →
        2 ≤ X → 2 ≤ M →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (15 : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (X : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (M : ℝ)) →
        ((D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt ((X : ℝ) * (M : ℝ))) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt (M : ℝ)) →
        F ≤ X →
        ((D : ℝ) ≤ Real.sqrt x) →
        (Real.log ((X : ℝ) * (M : ℝ)) ≤ Lb) →
        (((3 : ℝ) / Real.log 2) ^ 8 * x ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt (F : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X → 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        ((D : ℝ) ≤ (X : ℝ) * (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (Kc * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 18)
            ≤ Kβ * (Real.log ((2 ^ kp : ℕ) : ℝ)) ^ ((13 : ℝ) + 2 * 18)) →
        (Kc * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 1 + 2 * 18)
            ≤ Km * (Real.log ((2 ^ kp : ℕ) : ℝ)) ^ ((13 : ℝ) + 2 * 18)) →
        (∀ e, 2 ≤ e → e ≤ D →
            Kc * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 1 + 1 + 2 * 18)
              ≤ Kβ' * (Real.log ((2 ^ kp : ℕ) : ℝ)) ^ ((13 : ℝ) + 1 + 2 * 18)) →
        (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp)) X M (r d) d T₂‖)
          + (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp)) X M (r d) d T₁‖)
          ≤ 2 * ((Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26)
                    + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kβ' + 15360 + 1)))
              * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (13 : ℝ)) := by
  obtain ⟨Kc, N₀, hKc, hbody⟩ := gold_box_price_engine
  refine ⟨Kc, N₀, hKc, ?_⟩
  intro x Lb F β X M kp D Dset r Kβ Km Kβ' T₁ T₂ Ne z y K ka i hNe hi hlive hz1 hz_ratio hx hXeq
    hMeq hDge hk hβ hKβ hKm hKβ' hN₀ hd1 hcop2 hL1 hD1 hDsetD hDsq habs hX2 hM2 hDscale hXsqrt
    hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor herr_LEpos hDXM herr_scale hcoupG hcoup3
    herr_book4
  -- the two keystones: the z-dependent live floor, feeding the annulus D0-window.
  have hfloorN := gold_kfloor_live_z hNe hi hlive
  have hsc := gold_box_XM_scale hi
  rw [← hXeq, ← hMeq] at hsc
  obtain ⟨D0, k0, hd_eq, hd_2, hd_main, hd_lo, hd_hi, hd_N', hd_conj7, hd_scale, hd_N⟩ :=
    gold_d0_window_z (Ne := Ne) (Nb := 2 ^ kp) (M := M) (X := X) (k := ka) (z := z)
      hx hz1 hz_ratio hfloorN hsc.1 hsc.2
  -- the x-generic geometry rows re-derived from the piece parameter.
  have hM2N : M ≤ 2 * 2 ^ kp := by rw [hMeq]; exact pieceM_le_two_pow kp
  have hNM : ((2 ^ kp : ℕ) : ℝ) ≤ (M : ℝ) := by rw [hMeq]; exact_mod_cast two_pow_le_pieceM kp
  -- the D0 rows re-shaped to the engine's exponents / slots.
  have hD0D : D0 ≤ D := Nat.cast_le.mp (le_trans hd_scale hDge)
  have hD0lo_main : (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 2) ≤ 2 * (2 : ℝ) ^ k0 := by
    rw [show ((13 : ℝ) + 2) = 15 by norm_num]; exact hd_main
  have herr_D0lo : (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 4) ≤ (D0 : ℝ) := by
    rw [show ((13 : ℝ) + 4) = 17 by norm_num]; exact hd_lo
  have herr_D0E : ∀ e, 2 ≤ e → e ≤ D → e ≤ X →
      (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (18 : ℝ) :=
    fun e he2 heD heX => hd_conj7 _ (herr_scale e he2 heD heX)
  exact hbody x Lb F β X M kp D0 D k0 Dset r Kβ Km Kβ' T₁ T₂ hk hβ hKβ hKm hKβ' hN₀ hM2N hd_N
    hd1 hcop2 hL1 hd_hi hd_N' hNM hD1 hDsetD hDsq habs hX2 hM2 hd_eq hd_2 hD0D hDscale hD0lo_main
    hXsqrt hMsqrt herr_lev herr_D0lo herr_Mlev hFX hDx hLbb hfloor herr_LEpos herr_D0E hDXM
    herr_scale hcoupG hcoup3 herr_book4

/-! ## 4. The BoxRows3 handoff — the z-dependent live/dead dichotomy + slot mapping (deliverable 4)

The updated per-box case split BoxRows3 assembles into `gold_hBVblocksW_discharge'`'s
`hprice`/`hpriceSym`/`hpriceLow` slots.  The dichotomy on a box `i` (in the annulus boundary,
piece `kp`, annulus `ka`) is UNCHANGED in shape — only the LIVE branch's floor is z-dependent:

* **DEAD** (`min (z·pieceN kp + 1) (Ne/2 + 1) ≤ 2^i`): the carrier is empty, both cutoff sums vanish
  (`gold_box_price_row_dead`, unchanged) — discharges any nonneg price.
* **LIVE** (`2^i < min (…)`, in particular `2^i < z·pieceN kp + 1`): invoke
  `gold_box_price_engine_at_live_z` (§3).  Its z-dependent hypotheses are, at op:
  - `hz1 : 1 ≤ z` — `z = opZ N ≥ 10^6` at op (density route), trivial;
  - `hz_ratio : 6·log(8z) + 15 ≤ log(goldCut Ne (ka+1))` — from `gold_live_annulus_lower`
    (`z·y² < 4·goldCut`, so `log goldCut > log z + 2·log y − log 4`) and the op scales
    `log z ≈ log N/8`, `log y ≈ log N/3`: the gap `2·log y − 5·log z ≈ log N/24` dominates the
    constants `6·log 8 + log 4 + 15 ≈ 29` for `log N ≥ 696` (margin `N^{1/24}`, astronomically below
    the tower threshold `exp(10^9) ≤ goldCut`, i.e. `log N ≥ 10^9`);
  - `hDge : (goldCut Ne (ka+1)/(8z))^{1/2} ≤ D` — the sieve level `D` clears the z-dependent floor
    (`(goldCut/(8z))^{1/2} ≤ (N/(16·opZ N))^{1/2} ≤ N^{7/16}`, and `D` is the op sieve level).

The conclusion of `gold_box_price_engine_at_live_z` is byte-identical to
`gold_box_price_engine_at_live_annulus`'s (the same two-cutoff `≤ 2·Kerr` sum), so the LIVE-branch
slot mapping into `gold_hBVblocksW_discharge'` is byte-for-byte the landed one — only the internal
floor discharge changed. -/

section BoxRows3Handoff

/-- DEAD branch (unchanged): the empty-carrier box fills the `hprice` slot for any nonneg price. -/
example {z y : ℕ} {ε₀ : ℝ} {j k' k i N Q a : ℕ} {P : ℝ} {Dset : Finset ℕ}
    (hcap : min (z * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i) (hP : 0 ≤ P) :
    (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
          (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
          (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
          (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
      + (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
            (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
            (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
            (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
      ≤ P :=
  gold_box_price_row_dead hcap hP Dset

-- the §0 honest lower bound (makes hz_ratio satisfiable at op) + the z-dependent keystones
#check @Salt.Goldbach.gold_live_annulus_lower
#check @Salt.Goldbach.gold_kfloor_live_z
#check @Salt.Goldbach.gold_d0_window_z
#check @Salt.Goldbach.gold_box_price_engine_at_live_z
-- the DEAD keystone the DEAD branch reuses + the terminal consumer the packagings feed
#check @Salt.Goldbach.gold_box_price_vanish
#check @Salt.Goldbach.gold_hBVblocksW_discharge'
-- the SUPERSEDED annulus engine (its `hz : z ≤ goldCut^{1/8}` is the flagged blocker)
#check @Salt.Goldbach.gold_box_price_engine_at_live_annulus

end BoxRows3Handoff

end Salt.Goldbach
