/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HardyLittlewood.Selberg16

/-! # HL-3c node M6a — the twin Selberg sieve at level `N^(1−δ)`

A copy of `Sharp.lean`'s sieve with the level exponent symbolic: level `y = N^(1−δ)`,
truncation `z = ⌊N^((1−δ)/2)⌋`. `Sharp.lean` itself is merged and is not edited.

* `twin_le_sel` — `π₂(N) ≤ N/S + η·N/(log N)²` eventually, for every `η > 0`
  (the remainder `Σ 3^ω|r_d|` via `sum_six_pow_omega_le`, plus the `z + 1` small primes).
* `selbergBoundingSum_sel_ge` — `S ≥ mainTermSum z + mainTermSum (z/2)`: odd `ℓ` and
  `2ℓ` both contribute `gTwin ℓ`, since `selbergTerms 2 = 1`.
-/

open Finset Filter

namespace Salt.HardyLittlewood.Sel

/-- Sieve level `N^(1−δ)`. -/
noncomputable def ySel (δ : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (1 - δ)

/-- Truncation `⌊N^((1−δ)/2)⌋₊`. -/
noncomputable def zSel (δ : ℝ) (N : ℕ) : ℕ := ⌊(N : ℝ) ^ ((1 - δ) / 2)⌋₊

/-- Sift modulus. -/
noncomputable def PSel (δ : ℝ) (N : ℕ) : ℕ := primorial (zSel δ N)

lemma PSel_squarefree (δ : ℝ) (N : ℕ) : Squarefree (PSel δ N) :=
  Salt.M5Assembly.primorial_squarefree (zSel δ N)

/-- The twin Selberg sieve at level `N^(1−δ)`. -/
noncomputable def twinSieveSel (δ : ℝ) (hδ : δ < 1) (N : ℕ) (hN : 1 ≤ N) : SelbergSieve where
  toBoundingSieve := Salt.TwinSieve.sieve N (PSel δ N) (PSel_squarefree δ N)
  level := ySel δ N
  one_le_level := by
    unfold ySel
    exact Real.one_le_rpow (by exact_mod_cast hN) (by linarith)

/-- **M6a-1. The counting bound with the remainder absorbed.** -/
theorem twin_le_sel {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ hN : 1 ≤ N,
      (twinPrimeCounting N : ℝ) ≤
        (N : ℝ) / Salt.SelbergPort.selbergBoundingSum (twinSieveSel δ hδ1 N hN)
          + η * N / (Real.log N) ^ 2 := by
  sorry

/-- **M6a-2. The even-divisor denominator bound.** -/
theorem selbergBoundingSum_sel_ge {δ : ℝ} (hδ1 : δ < 1) (N : ℕ) (hN : 1 ≤ N) :
    Salt.M3Assembly.mainTermSum (zSel δ N) + Salt.M3Assembly.mainTermSum (zSel δ N / 2)
      ≤ Salt.SelbergPort.selbergBoundingSum (twinSieveSel δ hδ1 N hN) := by
  sorry

end Salt.HardyLittlewood.Sel
