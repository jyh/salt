/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The Chowla parameter regime (entropy-decrement spine, Tao arXiv:1509.05422v1 §3)

The mandatory regime structure of the entropy-decrement argument (the A-R0
D-risk mitigation): every parameter and every inter-parameter inequality of
Tao arXiv:1509.05422v1 §3 (Liouville spine) lives in ONE structure `ChowlaRegime`.
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

/-- The parameter regime of Tao arXiv:1509.05422v1 §3 (Liouville spine).  The gate
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
  /-- **PNT prime-window gate, ENDPOINT form** (the `~W3-c-pnt` re-freeze).  Tao's
      circle-method estimate (Lemma 3.4, p.22) cites `|𝒫_H| ≪ ε²H/log H` only "as ε
      is small and H is large"; `primeWindow_card_le_of_regime` makes this explicit
      under `√H ≤ ε²H/2` at each admissible `H`.  Since `t ↦ √t/t = t^(−1/2)` is
      decreasing, the strongest (hardest) instance sits at the LOWER endpoint `H₋`,
      so the field is frozen there: `√H₋ ≤ ε²H₋/2`.  It propagates upward to every
      `H ≥ H₋` by `sqrt_le_window_at` (monotonicity `√H·√H₋ ≤ H`, i.e. `H₋ ≤ H`). -/
  hPNTwindow : Real.sqrt (Hlo : ℝ) ≤ (eps : ℝ) ^ 2 * (Hlo : ℝ) / 2
  /-- **HBUDGET window-coupling floor, ENDPOINT form** (PATCH-4; `docs/exploration/
      s3-a3-design.md`, "HBUDGET STEP-0", the corrected `16/ε` calibration).  Funds the
      `hbudget_holds` binder `log ω ≥ (16/ε)·log(ε²H) + 64/ε + 1` (the collapse/swap
      slice `≤ 1/8` via `Z ≥ log ω − 1`).  The RHS `log ω` is `H`-free and the LHS is
      INCREASING in `H` (through `log(ε²H)`, `ε² ≥ 0`), so the field is frozen at the
      UPPER endpoint `H₊` and propagates DOWN to every admissible `H ≤ H₊` by
      `omega_big_at` (log-monotonicity `log(ε²H) ≤ log(ε²H₊)`). -/
  hωbig :
    (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (Hhi : ℝ)) + 64 / (eps : ℝ) + 1
      ≤ Real.log (ω : ℝ)
  /-- **HBUDGET shift `x`-floor, ENDPOINT form** (PATCH-4).  Funds the `hbudget_holds`
      binder `ω·H + 48·ω·(1 + 2/ε²)/ε ≤ x` (the shift slice `≤ 1/16`, and `x/ω ≥ H`).
      The LHS is INCREASING in `H` (the `ω·H` term), so the field is frozen at the
      UPPER endpoint `H₊` and propagates DOWN to every admissible `H ≤ H₊` by `x_big_at`
      (`ω·H ≤ ω·H₊`, the remaining term `H`-free). -/
  hxbig :
    (ω : ℝ) * (Hhi : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ)

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

/-! ### Per-`H` PNT-window gate (the endpoint monotonicity) -/

/-- **The per-`H` PNT-window clearance.**  The regime field `hPNTwindow` freezes
    `√H ≤ ε²H/2` at the LOWER endpoint `H₋`; this propagates to every admissible
    `H ≥ H₋`.  Route (elementary): from the endpoint field and `H₋ = √H₋·√H₋`,
    `2 ≤ ε²·√H₋` (divide by `√H₋ > 0`); and `√H·√H₋ = √(H·H₋) ≤ √(H·H) = H`
    (from `H₋ ≤ H`).  Multiplying `2 ≤ ε²·√H₋` by `H` and `√H·√H₋ ≤ H` by `2`
    gives `2·√H·√H₋ ≤ 2H ≤ ε²H·√H₋`, and dividing by `√H₋ > 0` yields
    `2·√H ≤ ε²H`, i.e. `√H ≤ ε²H/2`.  The `hhi` argument matches the house
    single-bound idiom of `pH_headroom_at` (here the LOWER bound is the binding
    one); it is carried for the consumer seam but the monotonicity needs only
    `hlo`. -/
theorem sqrt_le_window_at (R : ChowlaRegime) {H : ℕ}
    (hlo : R.Hlo ≤ H) (_hhi : H ≤ R.Hhi) :
    Real.sqrt (H : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) / 2 := by
  have hfloorN : 4000000 ≤ R.Hlo := R.hHlo_floor
  have hHfloorN : 4000000 ≤ H := le_trans hfloorN hlo
  have hf := R.hPNTwindow
  have hLpos : (0 : ℝ) < (R.Hlo : ℝ) := by exact_mod_cast (show 0 < R.Hlo by omega)
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hHL : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo
  set L := (R.Hlo : ℝ)
  set e := (R.eps : ℝ) ^ 2
  have hsqrtL_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hLeq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (le_of_lt hLpos)
  -- (i) `√H·√L ≤ H` (i.e. `√(H·L) ≤ √(H·H) = H`, from `L ≤ H`).
  have hi : Real.sqrt (H : ℝ) * Real.sqrt L ≤ (H : ℝ) := by
    have e1 : Real.sqrt (H : ℝ) * Real.sqrt L = Real.sqrt ((H : ℝ) * L) :=
      (Real.sqrt_mul (le_of_lt hHpos) L).symm
    rw [e1]
    have e2 : Real.sqrt ((H : ℝ) * L) ≤ Real.sqrt ((H : ℝ) * (H : ℝ)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hHL (le_of_lt hHpos))
    rwa [Real.sqrt_mul_self (le_of_lt hHpos)] at e2
  -- (ii) `2 ≤ e·√L` (from the endpoint field, dividing by `√L > 0`).
  have key : 2 * Real.sqrt L ≤ e * Real.sqrt L * Real.sqrt L := by
    calc 2 * Real.sqrt L
        ≤ 2 * (e * L / 2) := by linarith [hf]
      _ = e * L := by ring
      _ = e * (Real.sqrt L * Real.sqrt L) := by rw [hLeq]
      _ = e * Real.sqrt L * Real.sqrt L := by ring
  have he_sqrtL : (2 : ℝ) ≤ e * Real.sqrt L := le_of_mul_le_mul_right key hsqrtL_pos
  -- assemble: `2·√H·√L ≤ 2H ≤ e·H·√L`, divide by `√L`.
  have a1 : 2 * Real.sqrt (H : ℝ) * Real.sqrt L ≤ 2 * (H : ℝ) := by nlinarith [hi]
  have a2 : 2 * (H : ℝ) ≤ e * (H : ℝ) * Real.sqrt L := by nlinarith [he_sqrtL, hHpos]
  have combined : 2 * Real.sqrt (H : ℝ) * Real.sqrt L ≤ e * (H : ℝ) * Real.sqrt L :=
    le_trans a1 a2
  have final : 2 * Real.sqrt (H : ℝ) ≤ e * (H : ℝ) :=
    le_of_mul_le_mul_right combined hsqrtL_pos
  linarith [final]

/-! ### Per-`H` HBUDGET couplings (the endpoint→interior monotonicity) -/

/-- **The per-`H` window-coupling clearance.**  The regime field `hωbig` freezes
    `(16/ε)·log(ε²H₊) + 64/ε + 1 ≤ log ω` at the UPPER endpoint `H₊`; it propagates DOWN
    to every admissible `H ≤ H₊`, since the RHS `log ω` is `H`-free and
    `log(ε²H) ≤ log(ε²H₊)` (log-monotonicity, `ε²H > 0` from `h4`, and `16/ε > 0`).  The
    `4 ≤ ε²H` positivity `h4` is what the consumer already carries (via
    `sqrt_le_window_at`: `ε²H/2 ≥ √H ≥ √H₋ ≥ 2000`). -/
theorem omega_big_at (R : ChowlaRegime) {H : ℕ} (hH : H ≤ R.Hhi)
    (h4 : (4 : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ)) :
    (16 / (R.eps : ℝ)) * Real.log ((R.eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (R.eps : ℝ) + 1
      ≤ Real.log (R.ω : ℝ) := by
  have hepsR : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hεH_pos : (0 : ℝ) < (R.eps : ℝ) ^ 2 * (H : ℝ) := by linarith
  have hHle : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast hH
  have hεmono : (R.eps : ℝ) ^ 2 * (H : ℝ) ≤ (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) :=
    mul_le_mul_of_nonneg_left hHle (sq_nonneg _)
  have hlogmono : Real.log ((R.eps : ℝ) ^ 2 * (H : ℝ))
      ≤ Real.log ((R.eps : ℝ) ^ 2 * (R.Hhi : ℝ)) := Real.log_le_log hεH_pos hεmono
  have hmul : (16 / (R.eps : ℝ)) * Real.log ((R.eps : ℝ) ^ 2 * (H : ℝ))
      ≤ (16 / (R.eps : ℝ)) * Real.log ((R.eps : ℝ) ^ 2 * (R.Hhi : ℝ)) :=
    mul_le_mul_of_nonneg_left hlogmono (by positivity)
  linarith [R.hωbig, hmul]

/-- **The per-`H` shift `x`-floor clearance.**  The regime field `hxbig` freezes
    `ω·H₊ + 48·ω·(1+2/ε²)/ε ≤ x` at the UPPER endpoint `H₊`; it propagates DOWN to every
    admissible `H ≤ H₊`, since `ω·H ≤ ω·H₊` (`ω ≥ 0`) and the remaining term is
    `H`-free. -/
theorem x_big_at (R : ChowlaRegime) {H : ℕ} (hH : H ≤ R.Hhi) :
    (R.ω : ℝ) * (H : ℝ) + 48 * (R.ω : ℝ) * (1 + 2 / (R.eps : ℝ) ^ 2) / (R.eps : ℝ)
      ≤ (R.x : ℝ) := by
  have hHle : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast hH
  have hmul : (R.ω : ℝ) * (H : ℝ) ≤ (R.ω : ℝ) * (R.Hhi : ℝ) :=
    mul_le_mul_of_nonneg_left hHle (Nat.cast_nonneg _)
  linarith [R.hxbig, hmul]

end Salt.Entropy.Chowla
