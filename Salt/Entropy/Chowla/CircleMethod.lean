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

/-! ### Parseval / Plancherel for `ZMod.dft` (spine node W3-b-parseval)

mathlib has no Parseval identity for its finite Fourier transform, so we derive it here from
character orthogonality (the exported `AddChar.sum_mulShift`, primitivity of `ZMod.stdAddChar`
coming packaged as `ZMod.isPrimitive_stdAddChar`). Since `ZMod.dft` is *unnormalized*
(`ZMod.dft_dft Φ = fun j => (N : ℂ) • Φ (-j)`), Parseval carries the factor `N` on the time
side: `∑_ξ ‖𝓕Φ ξ‖² = N · ∑_j ‖Φ j‖²`. The Cauchy–Schwarz corollary `dft_l1_bound` is the shape
Tao's Lemma 3.4 proof (1509.05422 p. 24) actually cites. -/

/-- Complex conjugation sends `stdAddChar y` to `stdAddChar (-y)` (the character is unit-modulus:
`conj z = z⁻¹` on the circle, and `stdAddChar (-y) = (stdAddChar y)⁻¹`). -/
private lemma conj_stdAddChar {N : ℕ} [NeZero N] (y : ZMod N) :
    (starRingEnd ℂ) (ZMod.stdAddChar y) = ZMod.stdAddChar (-y) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj]

/-- Character orthogonality on `ZMod N`: `∑_ξ e(bξ/N) = N` if `b = 0`, else `0`. This is the
sum that mathlib only proves inline inside `auxDFT_auxDFT`; we obtain it from the exported
`AddChar.sum_mulShift` applied to the primitive standard character. -/
private lemma stdAddChar_sum_orthogonality {N : ℕ} [NeZero N] (b : ZMod N) :
    ∑ ξ : ZMod N, ZMod.stdAddChar (b * ξ) = if b = 0 then (N : ℂ) else 0 := by
  have h := AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar N)
  rw [ZMod.card, Nat.cast_ite, Nat.cast_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun ξ _ => by rw [mul_comm]

/-- The `ℂ`-valued Parseval identity: `∑_ξ 𝓕Φ ξ · conj(𝓕Φ ξ) = N · ∑_j Φ j · conj(Φ j)`. -/
private lemma dft_sum_mul_conj {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) :
    ∑ ξ : ZMod N, ZMod.dft Φ ξ * (starRingEnd ℂ) (ZMod.dft Φ ξ)
      = (N : ℂ) * ∑ j : ZMod N, Φ j * (starRingEnd ℂ) (Φ j) := by
  have key : ∀ ξ : ZMod N,
      ZMod.dft Φ ξ * (starRingEnd ℂ) (ZMod.dft Φ ξ)
        = ∑ j : ZMod N, ∑ k : ZMod N,
            ZMod.stdAddChar ((k - j) * ξ) * (Φ j * (starRingEnd ℂ) (Φ k)) := by
    intro ξ
    rw [ZMod.dft_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_eq_mul, map_mul]
    have hcomb : (k - j) * ξ = -(j * ξ) + k * ξ := by ring
    rw [conj_stdAddChar, neg_neg, hcomb, AddChar.map_add_eq_mul]
    ring
  calc ∑ ξ : ZMod N, ZMod.dft Φ ξ * (starRingEnd ℂ) (ZMod.dft Φ ξ)
      = ∑ ξ : ZMod N, ∑ j : ZMod N, ∑ k : ZMod N,
          ZMod.stdAddChar ((k - j) * ξ) * (Φ j * (starRingEnd ℂ) (Φ k)) :=
        Finset.sum_congr rfl fun ξ _ => key ξ
    _ = ∑ j : ZMod N, ∑ k : ZMod N, ∑ ξ : ZMod N,
          ZMod.stdAddChar ((k - j) * ξ) * (Φ j * (starRingEnd ℂ) (Φ k)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j : ZMod N, ∑ k : ZMod N,
          (Φ j * (starRingEnd ℂ) (Φ k)) * ∑ ξ : ZMod N, ZMod.stdAddChar ((k - j) * ξ) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ξ _ => by ring
    _ = ∑ j : ZMod N, ∑ k : ZMod N,
          (Φ j * (starRingEnd ℂ) (Φ k)) * (if k - j = 0 then (N : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [stdAddChar_sum_orthogonality]
    _ = ∑ j : ZMod N, Φ j * (starRingEnd ℂ) (Φ j) * (N : ℂ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single j
              (fun k _ hkj => by rw [if_neg (sub_ne_zero.mpr hkj), mul_zero])
              (fun h => absurd (Finset.mem_univ j) h),
          sub_self, if_pos rfl]
    _ = (N : ℂ) * ∑ j : ZMod N, Φ j * (starRingEnd ℂ) (Φ j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- **Parseval / Plancherel for `ZMod.dft`** (node W3-b-parseval). As mathlib's `ZMod.dft` is
unnormalized, the factor `N` sits on the time side:
`∑_ξ ‖𝓕Φ ξ‖² = N · ∑_j ‖Φ j‖²`. -/
theorem dft_parseval {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) :
    ∑ ξ : ZMod N, ‖ZMod.dft Φ ξ‖ ^ 2 = (N : ℝ) * ∑ j : ZMod N, ‖Φ j‖ ^ 2 := by
  have e1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := fun z => by
    rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast]
  simp only [e1]
  exact dft_sum_mul_conj Φ

/-- The `∑_ξ ‖𝓕Φ ξ‖² ≤ N² M²` energy bound (Parseval + the pointwise bound `‖Φ j‖ ≤ M`). -/
private lemma dft_normSq_sum_le {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (M : ℝ)
    (hΦ : ∀ j, ‖Φ j‖ ≤ M) :
    ∑ ξ : ZMod N, ‖ZMod.dft Φ ξ‖ ^ 2 ≤ (N : ℝ) ^ 2 * M ^ 2 := by
  rw [dft_parseval]
  have hbound : ∑ j : ZMod N, ‖Φ j‖ ^ 2 ≤ (N : ℝ) * M ^ 2 := by
    calc ∑ j : ZMod N, ‖Φ j‖ ^ 2
        ≤ ∑ _j : ZMod N, M ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          gcongr
          exact hΦ j
      _ = (N : ℝ) * M ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  calc (N : ℝ) * ∑ j : ZMod N, ‖Φ j‖ ^ 2
      ≤ (N : ℝ) * ((N : ℝ) * M ^ 2) := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg N)
    _ = (N : ℝ) ^ 2 * M ^ 2 := by ring

/-- **The Cauchy–Schwarz corollary of Parseval that Lemma 3.4 cites** (Tao 1509.05422 p. 24,
`∑_ξ |G₁(ξ)| |G₂(ξ+s)| ≪ 1`; unnormalized this is `≤ N² M²`). For `M`-bounded windows `Φ, Ψ`
and any shift `t`, the `ℓ¹` inner product of the Fourier magnitudes is bounded by `N² M²`. -/
theorem dft_l1_bound {N : ℕ} [NeZero N] (Φ Ψ : ZMod N → ℂ) (M : ℝ)
    (hΦ : ∀ j, ‖Φ j‖ ≤ M) (hΨ : ∀ j, ‖Ψ j‖ ≤ M) (t : ZMod N) :
    ∑ ξ : ZMod N, ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Ψ (ξ + t)‖ ≤ (N : ℝ) ^ 2 * M ^ 2 := by
  have hCnn : (0 : ℝ) ≤ (N : ℝ) ^ 2 * M ^ 2 := by positivity
  have hSnonneg : 0 ≤ ∑ ξ : ZMod N, ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Ψ (ξ + t)‖ :=
    Finset.sum_nonneg fun ξ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hΨshift : ∑ ξ : ZMod N, ‖ZMod.dft Ψ (ξ + t)‖ ^ 2
      = ∑ ξ : ZMod N, ‖ZMod.dft Ψ ξ‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight t) _ _ (fun ξ => by simp [Equiv.coe_addRight])
  have hΦsum := dft_normSq_sum_le Φ M hΦ
  have hΨsum : ∑ ξ : ZMod N, ‖ZMod.dft Ψ (ξ + t)‖ ^ 2 ≤ (N : ℝ) ^ 2 * M ^ 2 := by
    rw [hΨshift]; exact dft_normSq_sum_le Ψ M hΨ
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod N))
    (fun ξ => ‖ZMod.dft Φ ξ‖) (fun ξ => ‖ZMod.dft Ψ (ξ + t)‖)
  have hSq : (∑ ξ : ZMod N, ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Ψ (ξ + t)‖) ^ 2
      ≤ ((N : ℝ) ^ 2 * M ^ 2) ^ 2 := by
    calc (∑ ξ : ZMod N, ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Ψ (ξ + t)‖) ^ 2
        ≤ (∑ ξ : ZMod N, ‖ZMod.dft Φ ξ‖ ^ 2)
            * (∑ ξ : ZMod N, ‖ZMod.dft Ψ (ξ + t)‖ ^ 2) := hCS
      _ ≤ ((N : ℝ) ^ 2 * M ^ 2) * ((N : ℝ) ^ 2 * M ^ 2) :=
          mul_le_mul hΦsum hΨsum (Finset.sum_nonneg fun _ _ => sq_nonneg _) hCnn
      _ = ((N : ℝ) ^ 2 * M ^ 2) ^ 2 := by ring
  have hfin := Real.sqrt_le_sqrt hSq
  rwa [Real.sqrt_sq hSnonneg, Real.sqrt_sq hCnn] at hfin

/-! ### Smoke test (normalization pin): Parseval on the delta function.

`𝓕δ₀ ≡ 1`, so the Parseval LHS `∑_ξ ‖𝓕δ₀ ξ‖² = N`, matching the RHS `N · ∑_j ‖δ₀ j‖² = N · 1`.
This forces the factor `N` onto the time side and rules out the flipped orientation. -/

/-- The finite Fourier transform of the delta function `δ₀` is the constant `1`. -/
example {N : ℕ} [NeZero N] :
    ZMod.dft (fun j : ZMod N => if j = 0 then (1 : ℂ) else 0) = fun _ => 1 := by
  ext ξ
  rw [ZMod.dft_apply]
  simp

/-- Parseval evaluated on `δ₀`: the frequency-side energy equals `N`, pinning the normalization. -/
example {N : ℕ} [NeZero N] :
    ∑ ξ : ZMod N, ‖ZMod.dft (fun j : ZMod N => if j = 0 then (1 : ℂ) else 0) ξ‖ ^ 2
      = (N : ℝ) := by
  have hdft : ZMod.dft (fun j : ZMod N => if j = 0 then (1 : ℂ) else 0) = fun _ => 1 := by
    ext ξ; rw [ZMod.dft_apply]; simp
  rw [hdft]
  simp only [norm_one, one_pow, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    mul_one]

end Salt.Entropy.Chowla
