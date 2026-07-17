/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The regime instantiation — the anti-vacuity witness for `ChowlaRegime`

`entropy_decrement` (Tao 1509.05422 Lemma 3.1) is `ChowlaRegime`-parametric.
This file supplies the anti-vacuity obligation: an actual inhabitant
`∃ R : ChowlaRegime`.  Every field is pinned to a concrete constant —
`a = 1`, `ε = 1/2`, `H₋ = 4·10⁶`, `C₀ = 2`, `H₊ = chowlaTower 2 1 4·10⁶ J`,
`ω = 2`, `x = 2·(8·H₊³ + 8·M²)` with the (3.9) MAJORANT `M = 4^⌊ε²H₊⌋₊`
(`ε = 1/2` ⇒ `M = 4^⌊H₊/4⌋`) — the `~08:50` ruling restated `hPHheadroom` at the
`H`-uniform majorant `8·(4^⌊ε²H₊⌋₊)²·ω ≤ x` so it composes per-`H`
(`pH_headroom_at`), so the witness clears it by taking `P := M`.  Every
arithmetic side-condition (`hx … hcoprime`, `hfit`, `hheadroom`, `hheadroom'`,
`hPHheadroom`) discharges by pure computation.  The outer-scale half is
`regime_xside`: given ANY admissible `H₊ ≥ 4·10⁶` and any `P` (instantiated to
the majorant `M` at the call site), the choice `x = 2·(8·H₊³ + 8·P²)`, `ω = 2`
fulfils `hheadroom`/`hheadroom'`/`hωx` (`x/ω = 8·H₊³ + 8·P² ≥ H₊` and
`≥ 8·H₊·(log H₊)²`, using `log H₊ ≤ H₊`) plus `hPHheadroom`
(`8·P²·ω = 16·P² ≤ x`).

## The barely-divergent series (the ONE remaining input)

The sole non-arithmetic field is `hJcon : log 2 < towerDropSum 2 1 4·10⁶ J`,
the telescoped decrement `Σ_{j<J} 1/(2 log H_j · logloglog H_j)`.  With the
floor `H₋ = 4·10⁶` the summand at level `j` is `Θ(1/(j log j loglog j))` (since
`log H_j = Θ(j log j)` by the Harcos p.20 recursion bound `H_j ≤ exp(B j log j)`
and `logloglog H_j = Θ(loglog j)`), so the partial sum reaches `log 2 ≈ 0.693`
only near `J ≈ 1300`, where `H_J ≈ e^4825` — FAR beyond any `norm_num`/`decide`
reach.  So `hJcon` is NOT computable; it needs the DIVERGENCE of the
(barely-divergent) series.

`FLAG (divergence primitive — this node's floor).`  Mathlib has NO lemma on the
summability of iterated-logarithm series (`Σ 1/(n log n loglog n)`); the
reconnaissance confirmed the gap.  The unconditional discharge of `hJcon` is a
SEPARATE real-analysis sub-node, routed as: (1) an induction
`log (chowlaTower 2 1 4·10⁶ j) ≤ B·j·log j` (the increment
`log ⌊2 L_j M_j⌋ ≤ log 2 + 2 log L_j` closes it for large `B`); (2) two Cauchy
condensations `summable_condensed_iff_of_nonneg`
(`Mathlib/Analysis/PSeries.lean`) reducing `Σ 1/(n log n loglog n)` to the
harmonic `Real.not_summable_one_div_natCast`; (3) the bridge
`not_summable_iff_tendsto_nat_atTop_of_nonneg` + `exists_lt_of_tendsto_atTop`
to extract a finite `J` with partial sum `> log 2`.  Until it lands, the
instantiation is CONDITIONAL on that input (`regime_exists_of_dropSum`).
-/
import Salt.Entropy.Chowla.Tower

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ### The tower base floor (standalone, regime-free) -/

/-- Every value of the concrete tower `chowlaTower 2 1 4·10⁶` is `≥ 4·10⁶`
    (base `1·4·10⁶`; each step multiplies by `≥ 2` via `tower_mult_ge_two`).
    A regime-free twin of `chowlaTower_ge`, needed BEFORE any `ChowlaRegime`
    exists (the upper endpoint of the constructed regime is a tower value). -/
lemma chowlaTower_two_one_base_le (j : ℕ) : 4000000 ≤ chowlaTower 2 1 4000000 j := by
  induction j with
  | zero =>
    change (4000000 : ℕ) ≤ 1 * 4000000
    norm_num
  | succ n ih =>
    have hmult := tower_mult_ge_two (show (2 : ℕ) ≤ 2 from le_refl 2) ih
    rw [chowlaTower_succ]
    exact le_trans ih (Nat.le_mul_of_pos_right _ (by omega))

/-! ### The outer-scale `(x, ω)` half — unconditional -/

/-- **The outer-scale construction** (`hheadroom`/`hheadroom'`/`hωx`/`hPHheadroom`,
    unconditional).  Given any admissible upper endpoint `Hhi ≥ 4·10⁶` and any `P`
    (instantiated to the (3.9) majorant `4^⌊ε²Hhi⌋₊` at the call site), the choice
    `x = 2·(8·Hhi³ + 8·P²)`, `ω = 2` fits: `x/ω = 8·Hhi³ + 8·P²` dominates `Hhi` and
    `8·Hhi·(log Hhi)² ≤ 8·Hhi³` (using `Real.log Hhi ≤ Hhi`), and the house-re-freeze
    term `8·P²·ω = 16·P² ≤ x`. -/
lemma regime_xside (Hhi P : ℕ) (hHhi : 4000000 ≤ Hhi) :
    ∃ x ω : ℕ, 2 ≤ x ∧ 2 ≤ ω ∧ ω ≤ x ∧ Hhi ≤ x / ω ∧
      8 * (Hhi : ℝ) * Real.log Hhi * Real.log Hhi ≤ ((x / ω : ℕ) : ℝ) ∧
      8 * (P : ℝ) ^ 2 * (ω : ℝ) ≤ (x : ℝ) := by
  have hcube : Hhi ≤ Hhi ^ 3 := Nat.le_self_pow (by norm_num) Hhi
  have hdiv : (2 * (8 * Hhi ^ 3 + 8 * P ^ 2)) / 2 = 8 * Hhi ^ 3 + 8 * P ^ 2 := by omega
  refine ⟨2 * (8 * Hhi ^ 3 + 8 * P ^ 2), 2, by omega, le_refl 2, by omega, by omega, ?_, ?_⟩
  · rw [hdiv]
    have hHhiR : (4000000 : ℝ) ≤ (Hhi : ℝ) := by exact_mod_cast hHhi
    have hLnn : 0 ≤ Real.log (Hhi : ℝ) := Real.log_nonneg (by linarith)
    have hL : Real.log (Hhi : ℝ) ≤ (Hhi : ℝ) := Real.log_le_self (by linarith)
    have hsq : Real.log (Hhi : ℝ) * Real.log (Hhi : ℝ) ≤ (Hhi : ℝ) * (Hhi : ℝ) :=
      mul_le_mul hL hL hLnn (by linarith)
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 8 * (Hhi : ℝ) by positivity),
      sq_nonneg (P : ℝ)]
  · push_cast
    nlinarith [sq_nonneg (P : ℝ),
      pow_nonneg (show (0 : ℝ) ≤ (Hhi : ℝ) from Nat.cast_nonneg Hhi) 3]

/-! ### The instantiation, conditional on the barely-divergent series -/

/-- **The anti-vacuity witness, conditional on `hJcon`.**  Given a length `J`
    at which the telescoped decrement already exceeds `log 2` (the
    barely-divergent input — see the file header's FLAG), a full `ChowlaRegime`
    exists (with `a = 1`).  Every other field discharges by computation:
    `regime_xside` for the outer scale, `chowlaTower_two_one_base_le` for the
    endpoint order, `norm_num` for the numeric inequalities. -/
theorem regime_exists_of_dropSum (J : ℕ)
    (hJ : Real.log 2 < towerDropSum 2 1 4000000 J) :
    ∃ R : ChowlaRegime, R.a = 1 := by
  have hHhi : 4000000 ≤ chowlaTower 2 1 4000000 J := chowlaTower_two_one_base_le J
  obtain ⟨x, ω, hx2, hω2, hωx, hhead, hhead', hPH⟩ :=
    regime_xside _ (4 ^ ⌊(1 / 2 : ℚ) ^ 2 * (chowlaTower 2 1 4000000 J : ℚ)⌋₊) hHhi
  exact ⟨{ x := x, ω := ω, a := 1, eps := 1 / 2, Hlo := 4000000,
           Hhi := chowlaTower 2 1 4000000 J, C0 := 2, J := J,
           hx := hx2, hω := hω2, hωx := hωx, ha := le_refl 1,
           heps := by norm_num, heps1 := le_refl _,
           hHlo := by norm_num, hHlohi := hHhi, hC0 := le_refl 2,
           hHlo_floor := le_refl _, hheadroom := hhead,
           hcoprime := by norm_num, hfit := le_refl _,
           hJcon := hJ, hheadroom' := hhead', hPHheadroom := hPH,
           hPNTwindow := by
             have hsqrt : Real.sqrt ((4000000 : ℕ) : ℝ) = 2000 := by
               rw [show ((4000000 : ℕ) : ℝ) = (2000 : ℝ) ^ 2 by norm_num]
               exact Real.sqrt_sq (by norm_num)
             rw [hsqrt]; push_cast; norm_num }, rfl⟩

/-- **The anti-vacuity witness (existential form).**  As soon as the
    barely-divergent series clears `log 2` at SOME finite length, a regime
    exists.  The remaining obligation is exactly
    `∃ J, log 2 < towerDropSum 2 1 4·10⁶ J` (the flagged divergence sub-node). -/
theorem regime_exists_of_dropSum_exists
    (h : ∃ J, Real.log 2 < towerDropSum 2 1 4000000 J) :
    ∃ R : ChowlaRegime, R.a = 1 :=
  let ⟨J, hJ⟩ := h; regime_exists_of_dropSum J hJ

end Salt.Entropy.Chowla
