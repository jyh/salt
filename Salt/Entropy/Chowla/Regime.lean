/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The Chowla parameter regime (entropy-decrement spine, Tao 1509.05422 §3)

The mandatory regime structure of the entropy-decrement argument (the A-R0
D-risk mitigation): every parameter and every inter-parameter inequality of
Tao 1509.05422 §3 (Liouville spine) lives in ONE structure `ChowlaRegime`.
No lemma of the rung may introduce a free parameter not drawn from the regime;
a missing inequality is a STOP-AND-FLAG (house re-freeze).

This file also freezes the two prerequisite recursion defs the structure's
`hfit`/`hJcon` fields reference: `chowlaTower` (the tower recursion
`H₁ = a·H₋`, `H_{j+1} = H_j·⌊C₀ log H_j logloglog H_j⌋`) and `towerDropSum`
(the telescoped per-step entropy decrement `Σ 1/(2 log H_j logloglog H_j)`).

Field list transcribed at page-image fidelity (S3-A2-GATE, pp. 11–20; whole
structure elaborates EXIT 0), with the wave-II strengthening `hheadroom'`
(S3-A2-W2GATE: `C = 8`, `p = 2` verified independently at 3.65× slack) and the
house re-freeze field `hPHheadroom` (the `~04:30` ledger ruling, amended `~08:50`
to the `H`-uniform MAJORANT form `8·(4^⌊ε²H₊⌋₊)²·ω ≤ x` — since the prime window
moves with `H`, `P_H` is not monotone, so the bound is stated at the primorial
majorant and composed per-`H` by `pH_headroom_at`; provenance in the docstrings).
-/
import Mathlib
import Salt.Entropy.Chowla.PrimeWindow

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ### The tower recursion and its telescoped decrement -/

/-- The tower recursion (Lemma 3.1, p.19): `H₁ = a·H₋` (index `0`),
    `H_{j+1} = H_j·⌊C₀ log H_j logloglog H_j⌋`.  The floor `⌊·⌋₊` at the
    regime floor `H₋ ≥ 4·10⁶` is `≥ 2` (strict growth: `logloglog H₋ ≥ 1`). -/
noncomputable def chowlaTower (C0 a Hlo : ℕ) : ℕ → ℕ
  | 0     => a * Hlo
  | (j+1) => chowlaTower C0 a Hlo j *
      ⌊(C0 : ℝ) * Real.log (chowlaTower C0 a Hlo j : ℝ)
        * Real.log (Real.log (Real.log (chowlaTower C0 a Hlo j : ℝ)))⌋₊

/-- The telescoped per-step entropy decrement
    `Σ_{j<J} 1/(2 log H_j logloglog H_j)`. -/
noncomputable def towerDropSum (C0 a Hlo J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J,
    1 / (2 * Real.log (chowlaTower C0 a Hlo j : ℝ)
           * Real.log (Real.log (Real.log (chowlaTower C0 a Hlo j : ℝ))))

/-! ### The regime structure -/

/-- The parameter regime of Tao 1509.05422 §3 (Liouville spine).  The gate
    verifies the hypothesis list against pp. 16–20 page images; executors NEVER
    add fields or hypotheses — a missing inequality is a STOP-AND-FLAG. -/
structure ChowlaRegime where
  /-- the outer scale -/
  x : ℕ
  /-- the log-window width (`n ∈ (x/ω, x]`) -/
  ω : ℕ
  /-- the arithmetic-progression stride (`H ≡ 0 mod a`) -/
  a : ℕ
  /-- the `ε` of the prime window (`ε²` scales `𝒫_H`) -/
  eps : ℚ
  /-- the admissible `H`-range lower endpoint `H₋` -/
  Hlo : ℕ
  /-- the admissible `H`-range upper endpoint `H₊` -/
  Hhi : ℕ
  /-- the tower ratio constant -/
  C0 : ℕ
  /-- the tower length -/
  J : ℕ
  hx : 2 ≤ x
  hω : 2 ≤ ω
  hωx : ω ≤ x
  ha : 1 ≤ a
  heps : 0 < eps
  heps1 : eps ≤ 1/2
  hHlo : a ≤ Hlo
  hHlohi : Hlo ≤ Hhi
  hC0 : 2 ≤ C0
  /-- `H₋ ≥ e^{e^e} ≈ 3.814·10⁶`: forces `logloglog H₋ ≥ 1`, hence the tower
      step `⌊C₀ logH logloglogH⌋ ≥ 2` (STRICT growth) and the decrement
      `1/(2 logH logloglogH) > 0`.  (The naive `H ≥ 16` floor STALLS the tower.) -/
  hHlo_floor : 4000000 ≤ Hlo
  /-- MINIMAL headroom (necessary, superseded by `hheadroom'` for the wave-II
      invariance error control). -/
  hheadroom : Hhi ≤ x / ω
  /-- `P_H` coprime to `a` (p.16): every prime of `𝒫_H` exceeds `ε²H/2 ≥
      ε²H₋/2 ≥ a`. -/
  hcoprime : (a : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) / 2
  /-- "H₊ sufficiently large depending on H₋, C₀, J" (p.19): the `J`-step tower
      fits below `H₊`; with monotonicity ⇒ every `H_j ∈ [H₋, H₊]`. -/
  hfit : chowlaTower C0 a Hlo J ≤ Hhi
  /-- "J sufficiently large depending on C₀, H₋, ε" (p.20): the telescoped
      decrement `Σ` exceeds the Liouville entropy ceiling `ℍ(X_H)/H ≤ log 2`,
      forcing the contradiction. -/
  hJcon : Real.log 2 < towerDropSum C0 a Hlo J
  /-- **wave-II strengthening** (S3-A2-W2GATE, `C = 8`, `p = 2`; verified
      independently at 3.65× slack).  The per-shift `ℓ¹` error times `H·log 2`
      (Fannes at `|S| ≤ 2^H`) stays below half the per-step decrement — the
      explicit replacement for Tao's `o_{A→∞}(1)`. -/
  hheadroom' : 8 * (Hhi : ℝ) * Real.log Hhi * Real.log Hhi ≤ ((x / ω : ℕ) : ℝ)
  /-- **house re-freeze, MAJORANT form** (the `~04:30` ledger ruling, amended by
      the `~08:50` ruling).  Tao's (3.9) demands the shift-average error
      `8·P_H²·ω/x → 0`, i.e. `P_H²·ω ≪ x` — the A2-GATE's deferred A-parameter
      (Tao p.11's hierarchy: `P_H` is exponential in `H`, the window scale `ω`
      sits a further tier above `H`).  It is confirmed BINDING by the landed
      `entropy_residueWindow_ge`, whose correction term is exactly `8·P_H²·ω/x`.
      Because the prime window `𝒫_H` MOVES with `H`, `P_H` is NOT monotone in
      `H`, so a field stated at `(P_H at H₊)²` does not compose to the
      decrement's `H ≤ H₊`.  The field is therefore stated at the honest
      `H`-uniform MAJORANT `4^⌊ε²H₊⌋₊ ≥ 4^⌊ε²H⌋₊ ≥ P_H` (the primorial bound,
      floor-monotone in `H`): `8·(4^⌊ε²H₊⌋₊)²·ω ≤ x`.  The per-`H` clearance
      `8·(P_H at H)²·ω ≤ x` for every `H ≤ H₊` is then `pH_headroom_at`. -/
  hPHheadroom :
    8 * ((4 ^ ⌊eps ^ 2 * (Hhi : ℚ)⌋₊ : ℕ) : ℝ) ^ 2 * (ω : ℝ) ≤ (x : ℝ)

/-! ### Smoke lemma (wave III consumer) -/

/-- The tower respects the stride: `a ∣ H_j` for every `j` (Tao's "which is a
    multiple of `a`").  Base `H₀ = a·H₋`; the step multiplies by an integer. -/
lemma dvd_chowlaTower (C0 a Hlo : ℕ) (j : ℕ) : a ∣ chowlaTower C0 a Hlo j := by
  induction j with
  | zero => exact ⟨Hlo, rfl⟩
  | succ n ih => exact ih.mul_right _

/-! ### Per-`H` headroom composition (the majorant route) -/

/-- **The per-`H` (3.9) clearance.**  The regime field `hPHheadroom` is stated at
    the `H`-uniform majorant `4^⌊ε²H₊⌋₊`.  For every admissible `H ≤ H₊` the honest
    per-`H` bound `8·(P_H at H)²·ω ≤ x` follows, because the primorial bound
    `PH eps H ≤ 4^⌊ε²H⌋₊` (`PH_le_four_pow`) composes with the floor-monotonicity
    `⌊ε²H⌋₊ ≤ ⌊ε²H₊⌋₊` (as `ε² ≥ 0` and `H ≤ H₊`).  This is the form every consumer
    (the deficiency `8·P_H²·ω/x` of `weakUniform_spine`) actually runs at. -/
lemma pH_headroom_at (R : ChowlaRegime) {H : ℕ} (hH : H ≤ R.Hhi) :
    8 * ((PH R.eps H : ℕ) : ℝ) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ) := by
  -- floor-monotonicity of the exponent: ⌊ε²H⌋₊ ≤ ⌊ε²H₊⌋₊
  have hfloor : ⌊R.eps ^ 2 * (H : ℚ)⌋₊ ≤ ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ := by
    apply Nat.floor_mono
    have hHle : (H : ℚ) ≤ (R.Hhi : ℚ) := by exact_mod_cast hH
    exact mul_le_mul_of_nonneg_left hHle (sq_nonneg R.eps)
  -- the ℕ majorant chain P_H ≤ 4^⌊ε²H⌋₊ ≤ 4^⌊ε²H₊⌋₊
  have hmaj : PH R.eps H ≤ 4 ^ ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ :=
    (PH_le_four_pow R.eps H).trans (Nat.pow_le_pow_right (by norm_num) hfloor)
  -- lift to ℝ, square, and apply the field
  have hmajR : ((PH R.eps H : ℕ) : ℝ) ≤ ((4 ^ ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast hmaj
  have hnn : (0 : ℝ) ≤ ((PH R.eps H : ℕ) : ℝ) := Nat.cast_nonneg _
  have hωnn : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hsq := mul_le_mul hmajR hmajR hnn (le_trans hnn hmajR)
  calc 8 * ((PH R.eps H : ℕ) : ℝ) ^ 2 * (R.ω : ℝ)
      ≤ 8 * ((4 ^ ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) ^ 2 * (R.ω : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hωnn
        nlinarith [hsq]
    _ ≤ (R.x : ℝ) := R.hPHheadroom

end Salt.Entropy.Chowla
