/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HDoorSupply

/-!
# ⟦TIER S — S-0⟧ THE SOCKET'S `A`-WINDOW IS INHABITED (`TierSSocket`)

`ArithPageLinear.SocketBaseL` and `HDoorSupply.SocketBaseLH` each carry FIVE conjuncts that
constrain the window anchor `A`, and every landed consumer takes the socket as a HYPOTHESIS.
Nothing in the corpus exhibits an `A` that meets all five at once, so every one of those
consumers is, as written, a claim about a set nobody has shown to be nonempty.

**`A := 2·x` meets all five**, for every regime and at every admissible `(M, H, L, q, j, s)`:

* `0 < A` and `A ≤ 2x` are immediate from `R.hx : 2 ≤ R.x`;
* `2^j ≤ A` is the dyadic floor — `j ≤ ⌊log₂ L⌋` puts `2^j ≤ L` (at `L > 0`), and
  `L ≤ H ≤ H₊ ≤ x/ω ≤ x/2` is the landed headroom chain (`DoorReceipt.lean:208-214`);
* `√H ≤ A` from the same chain;
* the window conjunct `x ≤ 16·ω·arcDen 12 H·A` holds with a factor of 64 to spare, since
  `arcDen 12 H ≥ 1` past the regime's window floor (`one_le_arcDen_of_regime`) and `ω ≥ 2`.

⛔ **THE `L = 0` SPLIT IS NOT COSMETIC.**  `Nat.pow_log_le_self` carries the side condition
`n ≠ 0`, and at `L = 0` the hypothesis `j ≤ Nat.log 2 L` degenerates to `j = 0` rather than
bounding `2^j` by `L`.  The two branches close by different arguments and both are needed —
the socket's `L` is not assumed positive anywhere.

⭐ **THE MUTATION CONTROL IS IN-MODULE** (`socketBaseLH_at_zero_false`): at `h = 0` the
inflated socket is UNINHABITABLE, because its window conjunct reads `x ≤ 0`.  So the
inhabitation above is not a statement that `SocketBaseLH` is vacuously easy for every `h`; it
is a statement about `h ≥ 1`, and the `h = 0` mutant is proved FALSE rather than left
unmeasured.  (This is the `feedback_mutation_control` form: the mutant makes the goal FALSE,
not merely unreachable by one route.)

Nothing here bears on twin primes.
-/

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — the shared scale facts -/

/-- `H + 1 ≤ x` at every admissible window — the landed headroom chain
`H ≤ H₊ ≤ x/ω ≤ x/2` (`DoorReceipt.lean:208-214`) plus `2 ≤ x`. -/
theorem tierS_succ_le_x_of_le_Hhi {R : ChowlaRegime} {H : ℕ} (hHhi : H ≤ R.Hhi) :
    H + 1 ≤ R.x := by
  have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
  have hle : H ≤ R.x / 2 := le_trans (le_trans hHhi R.hheadroom) hdiv
  have h2 : 2 ≤ R.x := R.hx
  omega

/-- `2 ^ j ≤ 2·x` — the dyadic floor at the anchor.  **The `L = 0` branch is separate**:
`Nat.pow_log_le_self` needs `L ≠ 0`, and at `L = 0` the bound comes from `j = 0` instead. -/
theorem tierS_two_pow_le_twice_x {R : ChowlaRegime} {H L j : ℕ}
    (hHhi : H ≤ R.Hhi) (hLH : L ≤ H) (hjL : j ≤ Nat.log 2 L) :
    2 ^ j ≤ 2 * R.x := by
  have hx : 2 ≤ R.x := R.hx
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · subst hL0
    have hj0 : j = 0 := by simpa using hjL
    subst hj0
    simpa using (by omega : 1 ≤ 2 * R.x)
  · have hpl : 2 ^ Nat.log 2 L ≤ L := Nat.pow_log_le_self 2 hLpos.ne'
    have hmono : 2 ^ j ≤ 2 ^ Nat.log 2 L := Nat.pow_le_pow_right (by norm_num) hjL
    have hHx : H + 1 ≤ R.x := tierS_succ_le_x_of_le_Hhi (R := R) hHhi
    omega

/-- `√H ≤ 2·x` — the same chain, read in `ℝ`. -/
theorem tierS_sqrt_le_twice_x {R : ChowlaRegime} {H : ℕ} (hHhi : H ≤ R.Hhi) :
    Real.sqrt (H : ℝ) ≤ ((2 * R.x : ℕ) : ℝ) := by
  have hHx : H + 1 ≤ R.x := tierS_succ_le_x_of_le_Hhi (R := R) hHhi
  have hHxn : H ≤ R.x := by omega
  have hHxR : (H : ℝ) ≤ (R.x : ℝ) := by exact_mod_cast hHxn
  have hxR : (2 : ℝ) ≤ (R.x : ℝ) := by exact_mod_cast R.hx
  have hc : ((2 * R.x : ℕ) : ℝ) = 2 * (R.x : ℝ) := by push_cast; ring
  rw [hc]
  have hsq : Real.sqrt (H : ℝ) ≤ Real.sqrt ((2 * (R.x : ℝ)) ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rwa [Real.sqrt_sq (by linarith)] at hsq

/-- **THE WINDOW CONJUNCT AT THE ANCHOR** — `x ≤ 16·ω·D·(2x)` for any `D ≥ 1`.  The
cofactor is `≥ 64`; no sharp constant is chased. -/
theorem tierS_window_of_one_le {R : ChowlaRegime} {D : ℝ} (hD : (1 : ℝ) ≤ D) :
    (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * D * ((2 * R.x : ℕ) : ℝ) := by
  have hxR : (2 : ℝ) ≤ (R.x : ℝ) := by exact_mod_cast R.hx
  have hωR : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
  have hc : ((2 * R.x : ℕ) : ℝ) = 2 * (R.x : ℝ) := by push_cast; ring
  rw [hc]
  have hprod : (32 : ℝ) ≤ 16 * (R.ω : ℝ) * D := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hprod
    (show (0 : ℝ) ≤ 2 * (R.x : ℝ) by linarith)
  linarith

/-! ## §2 — the two inhabitation theorems -/

/-- ⭐ **⟦TIER S S-0⟧ THE LINEAR SOCKET IS INHABITED AT `A = 2·x`**
(`socketBaseL_inhabited_at_twice_x`).  Every hypothesis of `ArithPageLinear.SocketBaseL` that
does not mention `A` is passed through; the five `A`-conjuncts are §1. -/
theorem socketBaseL_inhabited_at_twice_x
    {R : ChowlaRegime} {M H L q j s : ℕ}
    (hM : 1 ≤ M)
    (hHlo : R.Hlo ≤ H) (hHhi : H ≤ R.Hhi) (hLH : L ≤ H)
    (hq : 0 < q) (hqA : (q : ℝ) ≤ arcDen 12 H)
    (hjL : j ≤ Nat.log 2 L) (hjfl : doorRowFloorL M ≤ j) (hsL : s ≤ L) :
    SocketBaseL R M H L q j (2 * R.x) s := by
  have _hM := hM
  have hx : 2 ≤ R.x := R.hx
  have hA0 : 0 < 2 * R.x := by omega
  have hcap : ((2 * R.x : ℕ) : ℝ) ≤ 2 * (R.x : ℝ) := by push_cast; ring_nf; exact le_refl _
  exact ⟨hHlo, hHhi, hLH, hq, hqA, hjL, hjfl, hA0,
    tierS_two_pow_le_twice_x (R := R) hHhi hLH hjL,
    tierS_sqrt_le_twice_x (R := R) hHhi,
    tierS_window_of_one_le (R := R) (one_le_arcDen_of_regime (R := R) hHlo),
    hcap, hsL⟩

/-- ⭐ **⟦TIER S S-0⟧ THE INFLATED SOCKET IS INHABITED AT `A = 2·x`, FOR EVERY `h ≥ 1`**
(`socketBaseLH_inhabited_at_twice_x`).  Identical to the linear case with `D := h·arcDen 12 H`;
the inflation only RAISES the window conjunct's right-hand side, and `h ≥ 1` is exactly what
keeps `D ≥ 1`. -/
theorem socketBaseLH_inhabited_at_twice_x
    {h : ℕ} {R : ChowlaRegime} {M H L q j s : ℕ}
    (hh : 1 ≤ h) (hM : 1 ≤ M)
    (hHlo : R.Hlo ≤ H) (hHhi : H ≤ R.Hhi) (hLH : L ≤ H)
    (hq : 0 < q) (hqA : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H)
    (hjL : j ≤ Nat.log 2 L) (hjfl : doorRowFloorL M ≤ j) (hsL : s ≤ L) :
    SocketBaseLH h R M H L q j (2 * R.x) s := by
  have _hM := hM
  have hx : 2 ≤ R.x := R.hx
  have hA0 : 0 < 2 * R.x := by omega
  have hcap : ((2 * R.x : ℕ) : ℝ) ≤ 2 * (R.x : ℝ) := by push_cast; ring_nf; exact le_refl _
  have harc : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hHlo
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hD : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := by nlinarith
  exact ⟨hHlo, hHhi, hLH, hq, hqA, hjL, hjfl, hA0,
    tierS_two_pow_le_twice_x (R := R) hHhi hLH hjL,
    tierS_sqrt_le_twice_x (R := R) hHhi,
    tierS_window_of_one_le (R := R) hD,
    hcap, hsL⟩

/-! ## §3 — the in-module mutation control -/

/-- ⛔ **THE `h = 0` MUTANT IS FALSE** (`socketBaseLH_at_zero_false`).  At `h = 0` the window
conjunct reads `x ≤ 16·ω·(0·arcDen 12 H)·A = 0`, and `R.hx : 2 ≤ x` refutes it — for EVERY
regime, EVERY window and EVERY anchor.  This is the control that makes §2 a claim about
`h ≥ 1` rather than a claim that the inflated socket is cheap to inhabit at any `h`. -/
theorem socketBaseLH_at_zero_false
    {R : ChowlaRegime} {M H L q j s : ℕ} :
    ¬ SocketBaseLH 0 R M H L q j (2 * R.x) s := by
  intro hcon
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hw, -, -⟩ := hcon
  have hx : 2 ≤ R.x := R.hx
  norm_num at hw
  omega

end Salt.MR
