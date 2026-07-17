/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The regime instantiation — the anti-vacuity witness for `ChowlaRegime`

`entropy_decrement` (Tao 1509.05422 Lemma 3.1) is `ChowlaRegime`-parametric.
This file supplies the anti-vacuity obligation: an actual inhabitant
`∃ R : ChowlaRegime`.  Every field is pinned to a concrete constant —
`a = 1`, `ε = 1/2`, `H₋ = 4·10⁶`, `C₀ = 2`, `H₊ = chowlaTower 2 1 4·10⁶ J`,
`ω = (H₊+2)^40`, `x = K·ω` with `K = 16·H₊³ + 16·M²` and the (3.9) MAJORANT
`M = 4^⌊ε²H₊⌋₊` (`ε = 1/2` ⇒ `M = 4^⌊H₊/4⌋`) — the `~08:50` ruling restated
`hPHheadroom` at the `H`-uniform majorant `8·(4^⌊ε²H₊⌋₊)²·ω ≤ x` so it composes
per-`H` (`pH_headroom_at`), so the witness clears it by taking `P := M`.
**PATCH-4** raised the window floors: `ω` is no longer `2` but the pure power
`(H₊+2)^40`, chosen so `log ω = 40·log(H₊+2)` clears the HBUDGET coupling
`hωbig : log ω ≥ (16/ε)·log(ε²H₊) + 64/ε + 1` (the `ε = 1/2` form
`≥ 32·log(H₊/4) + 129`), and `x = K·ω` is enlarged to a clean product that still
funds every `x`/`ω`-field plus the shift floor `hxbig`.  Every arithmetic
side-condition (`hx … hcoprime`, `hfit`, `hheadroom`, `hheadroom'`,
`hPHheadroom`, `hωbig`, `hxbig`) discharges by pure computation.  The outer-scale
+ floor half is `regime_outer`: given ANY admissible `H₊ ≥ 4·10⁶` and any `P`
(instantiated to the majorant `M`), `ω = (H₊+2)^40`, `x = K·ω` fulfils
`hheadroom`/`hheadroom'`/`hωx` (`x/ω = K ≥ H₊` and `≥ 8·H₊·(log H₊)²`, using
`log H₊ ≤ H₊`), `hPHheadroom` (`8·P²·ω ≤ K·ω`), `hxbig` (`ω·H₊ + 864·ω ≤ K·ω`),
and `hωbig` (`40·log(H₊+2) ≥ 32·log(H₊/4) + 129`, using `H₊ ≥ 2^21`).

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

/-- **The outer-scale + floor construction** (PATCH-4; `hheadroom`/`hheadroom'`/`hωx`/
    `hPHheadroom` plus the new `hωbig`/`hxbig` floors, unconditional).  Given any
    admissible upper endpoint `Hhi ≥ 4·10⁶` and any `P` (instantiated to the (3.9)
    majorant `4^⌊ε²Hhi⌋₊` at the call site), the choice `ω = (Hhi+2)^40`,
    `x = (16·Hhi³ + 16·P²)·ω = K·ω` fits every field: `x/ω = K = 16·Hhi³ + 16·P²`
    dominates `Hhi` and `8·Hhi·(log Hhi)² ≤ 8·Hhi³ ≤ K`; the house term `8·P²·ω ≤ K·ω`
    (`8P² ≤ K`); the shift floor `ω·Hhi + 864·ω ≤ K·ω` (`Hhi + 864 ≤ K`); and the
    window coupling `log ω = 40·log(Hhi+2) ≥ 32·log(Hhi/4) + 129` (the ε = 1/2 form of
    `(16/ε)·log(ε²Hhi) + 64/ε + 1`), since `40·log(Hhi+2) − 32·(log Hhi − 2·log 2) =
    8·log Hhi + 64·log 2 ≥ 232·log 2 > 232·0.693 > 129` using `Hhi ≥ 2^21`.  The
    degree-40 defining equation `ω = (Hhi+2)^40` is CLEARED before the arithmetic
    branches: `linarith`/`nlinarith` would otherwise ring-expand it and diverge. -/
lemma regime_outer (Hhi P : ℕ) (hHhi : 4000000 ≤ Hhi) :
    ∃ x ω : ℕ, 2 ≤ x ∧ 2 ≤ ω ∧ ω ≤ x ∧ Hhi ≤ x / ω ∧
      8 * (Hhi : ℝ) * Real.log Hhi * Real.log Hhi ≤ ((x / ω : ℕ) : ℝ) ∧
      8 * (P : ℝ) ^ 2 * (ω : ℝ) ≤ (x : ℝ) ∧
      (32 : ℝ) * Real.log ((1 / 4 : ℝ) * (Hhi : ℝ)) + 129 ≤ Real.log (ω : ℝ) ∧
      (ω : ℝ) * (Hhi : ℝ) + 864 * (ω : ℝ) ≤ (x : ℝ) := by
  have hHhiR : (4000000 : ℝ) ≤ (Hhi : ℝ) := by exact_mod_cast hHhi
  have hcube : Hhi ≤ Hhi ^ 3 := Nat.le_self_pow (by norm_num) Hhi
  have hcubeR : (Hhi : ℝ) ≤ (Hhi : ℝ) ^ 3 := by exact_mod_cast hcube
  have hHhi3 : 1 ≤ Hhi ^ 3 := Nat.one_le_pow 3 Hhi (by omega)
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = (Hhi + 2) ^ 40 := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = 16 * Hhi ^ 3 + 16 * P ^ 2 := ⟨_, rfl⟩
  -- everything needing the VALUE of ω or K, proven before clearing the ^40 equation
  have hωpos : 0 < ω := by rw [hωdef]; positivity
  have hω2 : 2 ≤ ω := by
    rw [hωdef]
    calc (2 : ℕ) ≤ Hhi + 2 := by omega
      _ ≤ (Hhi + 2) ^ 40 := Nat.le_self_pow (by norm_num) _
  have homega : (32 : ℝ) * Real.log ((1 / 4 : ℝ) * (Hhi : ℝ)) + 129 ≤ Real.log (ω : ℝ) := by
    have hHpos : (0 : ℝ) < (Hhi : ℝ) := by linarith
    have e2 : Real.log (ω : ℝ) = 40 * Real.log ((Hhi : ℝ) + 2) := by
      rw [hωdef]; push_cast; rw [Real.log_pow]; push_cast; ring
    have e1 : Real.log ((1 / 4 : ℝ) * (Hhi : ℝ)) = Real.log (Hhi : ℝ) - 2 * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by positivity),
          show (1 / 4 : ℝ) = (2 : ℝ)⁻¹ ^ 2 by norm_num, Real.log_pow, Real.log_inv]
      push_cast; ring
    have e3 : Real.log (Hhi : ℝ) ≤ Real.log ((Hhi : ℝ) + 2) :=
      Real.log_le_log hHpos (by linarith)
    have e4 : (21 : ℝ) * Real.log 2 ≤ Real.log (Hhi : ℝ) := by
      have hp : ((2 : ℝ) ^ 21) ≤ (Hhi : ℝ) := by
        have h2 : (2 : ℕ) ^ 21 ≤ Hhi := le_trans (by norm_num) hHhi
        have : ((2 : ℕ) ^ 21 : ℝ) ≤ (Hhi : ℝ) := by exact_mod_cast h2
        simpa using this
      calc (21 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ 21) := by rw [Real.log_pow]; push_cast; ring
        _ ≤ Real.log (Hhi : ℝ) := Real.log_le_log (by positivity) hp
    have e5 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    rw [e1, e2]; linarith [e3, e4, e5]
  have hKR : ((K : ℕ) : ℝ) = 16 * (Hhi : ℝ) ^ 3 + 16 * (P : ℝ) ^ 2 := by
    rw [hKdef]; push_cast; ring
  have hK1 : 1 ≤ K := by rw [hKdef]; omega
  have hHhiK : Hhi ≤ K := by rw [hKdef]; omega
  -- clear the degree-40 equation so linarith/nlinarith see only opaque fvars
  clear hωdef hKdef
  refine ⟨K * ω, ω, ?_, hω2, ?_, ?_, ?_, ?_, homega, ?_⟩
  · exact le_trans hω2 (Nat.le_mul_of_pos_left ω (by omega))
  · exact Nat.le_mul_of_pos_left ω (by omega)
  · rw [Nat.mul_div_cancel K hωpos]; exact hHhiK
  · rw [Nat.mul_div_cancel K hωpos]
    have hLnn : 0 ≤ Real.log (Hhi : ℝ) := Real.log_nonneg (by linarith)
    have hL : Real.log (Hhi : ℝ) ≤ (Hhi : ℝ) := Real.log_le_self (by linarith)
    have hsq : Real.log (Hhi : ℝ) * Real.log (Hhi : ℝ) ≤ (Hhi : ℝ) * (Hhi : ℝ) :=
      mul_le_mul hL hL hLnn (by linarith)
    have hstep : 8 * (Hhi : ℝ) * Real.log Hhi * Real.log Hhi ≤ 8 * (Hhi : ℝ) ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 8 * (Hhi : ℝ) by positivity)]
    rw [hKR]
    linarith [hstep, pow_nonneg (show (0 : ℝ) ≤ (Hhi : ℝ) from Nat.cast_nonneg Hhi) 3,
      sq_nonneg (P : ℝ)]
  · have hωnn : (0 : ℝ) ≤ (ω : ℝ) := Nat.cast_nonneg _
    have hPK : 8 * (P : ℝ) ^ 2 ≤ (K : ℝ) := by
      rw [hKR]
      linarith [sq_nonneg (P : ℝ), pow_nonneg (show (0 : ℝ) ≤ (Hhi : ℝ) from Nat.cast_nonneg Hhi) 3]
    calc 8 * (P : ℝ) ^ 2 * (ω : ℝ) ≤ (K : ℝ) * (ω : ℝ) :=
          mul_le_mul_of_nonneg_right hPK hωnn
      _ = ((K * ω : ℕ) : ℝ) := by push_cast; ring
  · have hωnn : (0 : ℝ) ≤ (ω : ℝ) := Nat.cast_nonneg _
    have hbase : (Hhi : ℝ) + 864 ≤ (K : ℝ) := by
      rw [hKR]; linarith [sq_nonneg (P : ℝ), hcubeR, hHhiR]
    calc (ω : ℝ) * (Hhi : ℝ) + 864 * (ω : ℝ) = (ω : ℝ) * ((Hhi : ℝ) + 864) := by ring
      _ ≤ (ω : ℝ) * (K : ℝ) := mul_le_mul_of_nonneg_left hbase hωnn
      _ = ((K * ω : ℕ) : ℝ) := by push_cast; ring

/-! ### The instantiation, conditional on the barely-divergent series -/

/-- **The anti-vacuity witness, conditional on `hJcon`.**  Given a length `J`
    at which the telescoped decrement already exceeds `log 2` (the
    barely-divergent input — see the file header's FLAG), a full `ChowlaRegime`
    exists (with `a = 1`).  Every other field discharges by computation:
    `regime_outer` for the outer scale + the `hωbig`/`hxbig` floors,
    `chowlaTower_two_one_base_le` for the endpoint order, `norm_num` for the numeric
    inequalities.  The `hωbig`/`hxbig` fields carry `ε = 1/2` inside a `ℚ→ℝ` cast; a
    `push_cast; norm_num` bridge reduces them to `regime_outer`'s numeric forms. -/
theorem regime_exists_of_dropSum (J : ℕ)
    (hJ : Real.log 2 < towerDropSum 2 1 4000000 J) :
    ∃ R : ChowlaRegime, R.a = 1 := by
  have hHhi : 4000000 ≤ chowlaTower 2 1 4000000 J := chowlaTower_two_one_base_le J
  obtain ⟨x, ω, hx2, hω2, hωx, hhead, hhead', hPH, homega, hxb⟩ :=
    regime_outer _ (4 ^ ⌊(1 / 2 : ℚ) ^ 2 * (chowlaTower 2 1 4000000 J : ℚ)⌋₊) hHhi
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
             rw [hsqrt]; push_cast; norm_num
           hωbig := by
             have e : (((1 / 2 : ℚ) : ℝ)) ^ 2 * ((chowlaTower 2 1 4000000 J : ℕ) : ℝ)
                 = (1 / 4 : ℝ) * ((chowlaTower 2 1 4000000 J : ℕ) : ℝ) := by push_cast; ring
             rw [e]; norm_num; linarith [homega]
           hxbig := by
             have e : 48 * (ω : ℝ) * (1 + 2 / ((1 / 2 : ℚ) : ℝ) ^ 2) / ((1 / 2 : ℚ) : ℝ)
                 = 864 * (ω : ℝ) := by push_cast; ring
             rw [e]; exact hxb }, rfl⟩

/-- **The anti-vacuity witness (existential form).**  As soon as the
    barely-divergent series clears `log 2` at SOME finite length, a regime
    exists.  The remaining obligation is exactly
    `∃ J, log 2 < towerDropSum 2 1 4·10⁶ J` (the flagged divergence sub-node). -/
theorem regime_exists_of_dropSum_exists
    (h : ∃ J, Real.log 2 < towerDropSum 2 1 4000000 J) :
    ∃ R : ChowlaRegime, R.a = 1 :=
  let ⟨J, hJ⟩ := h; regime_exists_of_dropSum J hJ

end Salt.Entropy.Chowla
