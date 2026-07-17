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
(S3-A2-W2GATE: `C = 8`, `p = 2` verified independently at 3.65× slack).
-/
import Mathlib

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

/-! ### Smoke lemma (wave III consumer) -/

/-- The tower respects the stride: `a ∣ H_j` for every `j` (Tao's "which is a
    multiple of `a`").  Base `H₀ = a·H₋`; the step multiplies by an integer. -/
lemma dvd_chowlaTower (C0 a Hlo : ℕ) (j : ℕ) : a ∣ chowlaTower C0 a Hlo j := by
  induction j with
  | zero => exact ⟨Hlo, rfl⟩
  | succ n ih => exact ih.mul_right _

end Salt.Entropy.Chowla
