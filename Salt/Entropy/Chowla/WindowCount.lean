/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The prime-window count (Tao 1509.05422 p. 22 PNT input), spine node W3-c-pnt

Tao's Lemma 3.4 (the circle-method estimate, `circle_method_estimate` v2 in
`docs/exploration/s3-a3-design.md`) cites, on p. 22, the Chebyshev/PNT bound
`|𝒫_H| ≪ ε²H/log H`, valid "as ε is small and H is large".  This file
discharges that hypothesis as an explicit, kernel-checked inequality and
supplies its anti-vacuity witness (the lesson of the v1 falsity: the bound is
*regime-gated* — it fails when `ε²H` is bounded, so a regime hypothesis relating
`eps` and `H` is mandatory).

* `primeWindow_card_le_of_regime` — **the keystone**: under the regime
  `√H ≤ ε²H/2` (i.e. `ε² ≥ 2·H^(−1/2)`) and `3 ≤ H`,
  `|𝒫_H| ≤ (2·log 4)·(ε²H / log H)`.  The consumer instantiates `C₀ := 2·log 4`.
* `regime_nonvacuous` — **the anti-vacuity witness**: at `eps = 1`, `H = 4` the
  regime holds (with equality `√4 = 2 = 4/2`) and the window `{3}` is NONEMPTY,
  so v2's added hypothesis is non-vacuously satisfiable by a kernel-checked
  instance, not by prose.

The proof route is Chebyshev-grade (all carriers in mathlib): every window prime
`p > ε²H/2` (`window_lb`) contributes `log p ≥ log(ε²H/2)`, so
`|𝒫_H|·log(ε²H/2) ≤ ∑_{p∈𝒫_H} log p ≤ θ(ε²H) ≤ log 4·ε²H`
(`Chebyshev.theta_le_log4_mul_x` via `theta_eq_sum_primesLE_log`, bridged by
`primeWindow_subset_primesLE`); the regime turns `log(ε²H/2) ≥ (1/2)log H` into
the `ε²H/log H` shape.
-/
import Salt.Entropy.Chowla.FBridge
import Mathlib

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-- **The prime-window count** (Tao 1509.05422 p. 22 PNT input, node W3-c-pnt).

Under the regime `√H ≤ ε²H/2` (equivalently `ε² ≥ 2·H^(−1/2)`) and `3 ≤ H`,
the prime window `𝒫_H = {p prime : ε²H/2 < p ≤ ε²H}` satisfies
`|𝒫_H| ≤ (2·log 4)·(ε²H / log H)`.

The regime is exactly Tao's "ε small, H large" gate: it forces `ε²H/2 ≥ √H > 1`,
so `log(ε²H/2) ≥ (1/2)log H > 0` and no window prime is too small.  The constant
`2·log 4` is what the Chebyshev bound `θ(x) ≤ log 4·x` yields; the consumer
`circle_method_estimate` v2 instantiates `C₀ := 2·log 4`. -/
theorem primeWindow_card_le_of_regime (eps : ℚ) (H : ℕ)
    (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2)
    (hH : 3 ≤ H) :
    ((primeWindow eps H).card : ℝ)
      ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) := by
  have hHR : (3 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hH1 : (1 : ℝ) < (H : ℝ) := by linarith
  have hlogH_pos : 0 < Real.log (H : ℝ) := Real.log_pos hH1
  have hLpos : 0 < Real.sqrt (H : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hWpos : 0 < (eps : ℝ) ^ 2 * (H : ℝ) / 2 := lt_of_lt_of_le hLpos hreg
  -- The regime, `log`-ed: `log H ≤ 2·log(ε²H/2)` (via `log √H = (1/2)log H`).
  have hlogW2 : Real.log (H : ℝ) ≤ 2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ) / 2) := by
    have h1 : Real.log (Real.sqrt (H : ℝ)) ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ) / 2) :=
      Real.log_le_log hLpos hreg
    rw [Real.log_sqrt (show (0 : ℝ) ≤ (H : ℝ) by linarith)] at h1
    linarith
  -- Every window prime `p > ε²H/2 > 0` has `log p ≥ log(ε²H/2)`.
  have hlow : ∀ p ∈ primeWindow eps H,
      Real.log ((eps : ℝ) ^ 2 * (H : ℝ) / 2) ≤ Real.log (p : ℝ) := fun p hp =>
    Real.log_le_log hWpos (le_of_lt (window_lb eps H ⟨p, hp⟩))
  -- `|𝒫_H|·log(ε²H/2) = ∑ log(ε²H/2) ≤ ∑_{p∈𝒫_H} log p`.
  have hLHS : ((primeWindow eps H).card : ℝ) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ) / 2)
      ≤ ∑ p ∈ primeWindow eps H, Real.log (p : ℝ) := by
    have hc : ∑ _p ∈ primeWindow eps H, Real.log ((eps : ℝ) ^ 2 * (H : ℝ) / 2)
        = ((primeWindow eps H).card : ℝ) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ) / 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← hc]
    exact Finset.sum_le_sum hlow
  -- `∑_{p∈𝒫_H} log p ≤ θ(⌊ε²H⌋) ≤ log 4·⌊ε²H⌋ ≤ log 4·ε²H`.
  have hUpper : ∑ p ∈ primeWindow eps H, Real.log (p : ℝ)
      ≤ Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ)) := by
    have hsub : primeWindow eps H ⊆ Nat.primesLE ⌊eps ^ 2 * (H : ℚ)⌋₊ :=
      primeWindow_subset_primesLE eps H
    have hsum_le : ∑ p ∈ primeWindow eps H, Real.log (p : ℝ)
        ≤ ∑ p ∈ Nat.primesLE ⌊eps ^ 2 * (H : ℚ)⌋₊, Real.log (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro p hpP _
      exact Real.log_nonneg (by exact_mod_cast (Nat.one_lt_of_mem_primesLE hpP).le)
    have hkle : ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
      have h0 : (0 : ℚ) ≤ eps ^ 2 * (H : ℚ) := by positivity
      calc ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ)
          = ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℚ) : ℝ) := by norm_cast
        _ ≤ ((eps ^ 2 * (H : ℚ) : ℚ) : ℝ) := by exact_mod_cast Nat.floor_le h0
        _ = (eps : ℝ) ^ 2 * (H : ℝ) := by push_cast; ring
    calc ∑ p ∈ primeWindow eps H, Real.log (p : ℝ)
        ≤ ∑ p ∈ Nat.primesLE ⌊eps ^ 2 * (H : ℚ)⌋₊, Real.log (p : ℝ) := hsum_le
      _ = Chebyshev.theta ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) :=
          (Chebyshev.theta_eq_sum_primesLE_log _).symm
      _ ≤ Real.log 4 * ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) :=
          Chebyshev.theta_le_log4_mul_x (by positivity)
      _ ≤ Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ)) :=
          mul_le_mul_of_nonneg_left hkle (Real.log_nonneg (by norm_num))
  -- Combine and clear the regime denominator.
  have hkey : ((primeWindow eps H).card : ℝ) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ) / 2)
      ≤ Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ)) := le_trans hLHS hUpper
  have hcard_nn : (0 : ℝ) ≤ ((primeWindow eps H).card : ℝ) := Nat.cast_nonneg _
  have hchain2 : ((primeWindow eps H).card : ℝ) * Real.log (H : ℝ)
      ≤ 2 * (Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ))) := by
    calc ((primeWindow eps H).card : ℝ) * Real.log (H : ℝ)
        ≤ ((primeWindow eps H).card : ℝ) * (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hlogW2 hcard_nn
      _ = 2 * (((primeWindow eps H).card : ℝ) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ) / 2)) := by
          ring
      _ ≤ 2 * (Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ))) := by linarith [hkey]
  rw [mul_div_assoc', le_div_iff₀ hlogH_pos]
  calc ((primeWindow eps H).card : ℝ) * Real.log (H : ℝ)
      ≤ 2 * (Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ))) := hchain2
    _ = 2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ)) := by ring

/-- **Anti-vacuity witness** (node W3-c-pnt, the mandatory lesson of the v1
falsity).  The regime hypothesis of `primeWindow_card_le_of_regime` is
satisfiable with a NONEMPTY window: at `eps = 1`, `H = 4` we have `3 ≤ H`, the
regime `√H ≤ ε²H/2` holds with equality (`√4 = 2 = 4/2`), and the window is
`𝒫_4 = {3}` (the single prime in `(2, 4]`).  So the added hypothesis of
`circle_method_estimate` v2 is non-vacuous by a kernel-checked instance. -/
theorem regime_nonvacuous :
    ∃ (eps : ℚ) (H : ℕ), 3 ≤ H ∧
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 ∧
      (primeWindow eps H).Nonempty := by
  refine ⟨1, 4, by norm_num, ?_, ?_⟩
  · have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [show ((4 : ℕ) : ℝ) = (4 : ℝ) by norm_num, h4]
    norm_num
  · exact ⟨3, mem_primeWindow.mpr ⟨Nat.le_floor (by norm_num), by norm_num, by norm_num⟩⟩

end Salt.Entropy.Chowla
