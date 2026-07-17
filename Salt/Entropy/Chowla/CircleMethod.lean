/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The circle-method objects (Tao 1509.05422 Lemma 3.4, (3.17)–(3.18)), spine node W3-b-defs

The definitional layer for Tao's Lemma 3.4 at the Liouville model
instantiation (`a = 1, b = 0, h = 1, c_p = 1`), on the `ZMod.dft` carrier:

* `expSum` — **the exponential sum (3.17)** `S_H(α) = ∑_{p ∈ 𝒫_H} (1/p) e(αp)`.
* `bigXi` — **the major-arc set `Ξ_H`**: the frequencies `ξ ∈ ℤ/Hℤ` where
  `|S_H(−ξ/H)| ≥ ε²/log H` (at `a = 1` the `η ∈ ℤ/aℤ` twist collapses to `0`,
  so the argument is exactly `−ξ/H`).
* `dft_is_fourier_coeff` — **the carrier bridge**: `ZMod.dft Φ ξ =
  ∑_j e(−jξ/H) Φ j`, matching Tao's Fourier coefficient
  `∑_{j=1}^{H} x_{1,j} e(−jξ/H)` (p. 24).

The Lemma 3.4 ESTIMATE itself ((3.18), `circle_method_estimate`) is frozen in
`docs/exploration/s3-a3-design.md` and lands here once proven — its proof is
gated on a Parseval/Plancherel lemma for `ZMod.dft`, which mathlib does not
have (node W3-b-parseval), plus the `Ξ_H` major/minor split (node W3-b-main).

Statements frozen and elaboration-checked by the A3-W3R recon (2026-07-19),
with the vacuity guard: any constant in (3.18) must be quantified UNIFORMLY
over `eps, H` (per-`H` versions are trivially true by finiteness).
-/
import Salt.Entropy.Chowla.FBridge
import Mathlib

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-- **The exponential sum (3.17)** at the model weights `c_p = 1`:
`S_H(α) = ∑_{p ∈ 𝒫_H} (1/p) e(αp)` with `e(θ) = exp(2πiθ)`. -/
noncomputable def expSum (eps : ℚ) (H : ℕ) (α : ℝ) : ℂ :=
  ∑ p : primeWindow eps H,
    (1 / (p : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((p : ℕ) : ℂ))

/-- **The major-arc frequency set `Ξ_H`** (Lemma 3.4, at `a = 1` where the
`η ∈ ℤ/aℤ` twist collapses): the `ξ ∈ ℤ/Hℤ` with `|S_H(−ξ/H)| ≥ ε²/log H`. -/
noncomputable def bigXi (eps : ℚ) (H : ℕ) [NeZero H] : Finset (ZMod H) := by
  classical
  exact Finset.univ.filter (fun ξ : ZMod H =>
    (eps : ℝ) ^ 2 / Real.log (H : ℝ) ≤ ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖)

/-- **The carrier bridge**: mathlib's finite Fourier transform is Tao's (p. 24)
Fourier coefficient — `ZMod.dft Φ ξ = ∑_{j : ℤ/Hℤ} e(−jξ/H) Φ j`, matching
`G_i(ξ) = (1/H) ∑_j x_{i,j} e(−jξ/H)` up to the `1/H` normalization, which
(3.18) carries explicitly. -/
theorem dft_is_fourier_coeff {H : ℕ} [NeZero H] (Φ : ZMod H → ℂ) (ξ : ZMod H) :
    ZMod.dft Φ ξ = ∑ j : ZMod H, ZMod.stdAddChar (-(j * ξ)) • Φ j :=
  ZMod.dft_apply Φ ξ

end Salt.Entropy.Chowla
