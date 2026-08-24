/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Exit
import Salt.MR.DoorFloor1500

/-!
# N1 — Tao's W-headroom, transported to the split road's exit socket

Item 15 (the MRT port), design block v6 §4, node **N1**.

`m4_exit_socket_split` (`M4Exit.lean:487`) hands the split road a regime together with
the `¬ logChowla2Fails` implication, but the headroom conjunct it carries is the
head's TOWER endpoint law
(`50 ≤ loglog H₋ → loglog H₊ ≤ (loglog H₋)^5`) — passed through unused.  The
`B₅ = 12` W-headroom chain (`DoorFloor1500.lean:75`/`:90`) is stated at a regime and
is therefore free to be fired at the socket's regime; this file does exactly that,
trading the tower conjunct for

`(log H₊)^{1500} ≤ log (x / (2ω))`.

## What is NEW here, and what is not

📌 `regime_head_W_headroom_1500` (`DoorFloor1500.lean:221`) ALREADY carries the same
inequality — but at a **different regime supplier** (`chowlaRegime_exists_param_head_gJoin`,
with an `H0door δ₀` floor conjunct and no failure implication).  N1's content is the
**transport to the socket's regime**, which additionally carries the
`¬ logChowla2Fails` implication; nothing about the inequality itself is re-proved.

## The floor slot stays open

The socket has already spent its `extraFloor` slot at `0` (`M4Exit.lean:500`), so its
`U1floor` binder is the LAST floor slot on this road.  The three floor demands this
proof needs are therefore joined into that one slot,

`U1floor := max extraFloor (max ⌈Real.exp 36000000⌉₊ (epsFloor ε))`,

and the caller's own `extraFloor` is re-exposed as a binder of the conclusion.  Pinning
it here would strand every downstream consumer.

`⌈Real.exp 36000000⌉₊` is a SHAPE, never evaluated — no closed numeral of that size is
formed, exactly as `DoorFloor.lean:40` records of its own `exp(9·10³⁸)`.  The `hbig`
arm is pure `Nat.le_ceil` / `Real.log_exp` / `Real.log_le_log` monotonicity.

## Measured strength

The conclusion is the **ℕ-power** form `(Real.log R.Hhi) ^ (1500 : ℕ)`.  It does **not**
deliver Tao arXiv:1509.05422v2 Prop. 2.4's `rpow` binder `W ≤ (log X)^{1/125}`; the
passage between the two is a separate, NOT-dispatchable step (v6 §4's exclusion list).
`B₅`'s live value is `12`; the `(log H)^5` forms elsewhere in the corpus are the
RETIRED `B₅ = 5` and are not cited here.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla

/-- **N1 — the socket, re-served with Tao's W-headroom at `B₅ = 12`.**  The split road's
exit socket (`m4_exit_socket_split`), with its unused tower conjunct traded for the
`1500`-headroom inequality `(log H₊)^{1500} ≤ log X_min`.  The caller's floor slot is
kept OPEN (`∀ extraFloor`); the three internal floor demands ride in the socket's own
last slot. -/
theorem regime_headroom_at_socket :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ (extraFloor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (Real.log (R.Hhi : ℝ)) ^ (1500 : ℕ) ≤ Real.log ((R.x : ℝ) / (2 * (R.ω : ℝ))) ∧
          ((∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
              NearRatTight (arcDen 12 H) H α →
                (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω)) ≤ δ₀ * (H : ℝ)) →
            ¬ logChowla2Fails R.eps R.x R.ω)
    := by
  obtain ⟨ε, δ₀, hε, hδ₀, hsock⟩ := m4_exit_socket_split
  refine ⟨ε, δ₀, hε, hδ₀, ?_⟩
  intro extraFloor g
  -- the socket's `U1floor` is the LAST floor slot: join all three demands into it
  obtain ⟨R, hReps, hU1, hRg, -, hR⟩ :=
    hsock (max extraFloor (max ⌈Real.exp 36000000⌉₊ (epsFloor ε))) g
  have hextra : extraFloor ≤ R.Hlo := le_trans (le_max_left _ _) hU1
  have hceil : ⌈Real.exp 36000000⌉₊ ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hepsF : epsFloor ε ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  -- the `hbig` arm: `exp 36000000 ≤ H₊` through the ceiling, then `log`-monotonicity
  have hbig : (36000000 : ℝ) ≤ Real.log (R.Hhi : ℝ) := by
    have hcast : ((⌈Real.exp (36000000 : ℝ)⌉₊ : ℕ) : ℝ) ≤ (R.Hhi : ℝ) := by
      exact_mod_cast le_trans hceil R.hHlohi
    have hle : Real.exp (36000000 : ℝ) ≤ (R.Hhi : ℝ) := le_trans (Nat.le_ceil _) hcast
    have hlog := Real.log_le_log (Real.exp_pos _) hle
    rwa [Real.log_exp] at hlog
  -- the `heps` arm composes only after `rw [hReps]` (`DoorFloor1500.lean:234-236`)
  have hepsHhi : epsFloor R.eps ≤ R.Hhi := by
    rw [hReps]
    exact le_trans hepsF R.hHlohi
  refine ⟨R, hReps, hextra, hRg, ?_, hR⟩
  exact regime_W_headroom_of_floor_1500 R
    (regime_hthr_of_scale_1500 R hbig (heps_arm_of_epsFloor hepsHhi))

end Salt.MR
