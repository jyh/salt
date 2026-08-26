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

/-! ### The Lemma 3.4 circle-method estimate (spine node W3-b-main, v3 re-freeze)

The v3 form of Tao's Lemma 3.4 (1509.05422 (3.18)) at the Liouville model
(`a = 1, b = 0, h = 1, c_p = 1`): the truncated prime-window correlation is bounded by the
`Ξ_H` Fourier mass, with the PNT input `|𝒫_H| ≤ C₀·ε²H/log H` externalised as an explicit
hypothesis (the v1 uniform freeze was false — see `docs/exploration/s3-a3-design.md`).  The
proof periodises the correlation onto `ZMod H` (wraparound error `≤ |𝒫_H|`, funded by the
hypothesis), Fourier-expands via `ZMod.dft`, then splits `Ξ_H` into minor arcs (`dft_l1_bound`)
and major arcs (`window_lb` + the hypothesis).  Quantifier form (v3, house-ratified): the
PNT constant `C₀` is UNIVERSAL and outermost, so the consumer can instantiate it with a
specific constant — `C₀ := 2·log 4` from `primeWindow_card_le_of_regime` (node W3-c-pnt) —
and the output constant pins uniformly to `C = 1 + 2·C₀`. -/

-- inversion pointwise
private lemma inv_pt {H : ℕ} [NeZero H] (Φ : ZMod H → ℂ) (m : ZMod H) :
    (H : ℂ) * Φ m = ∑ ξ : ZMod H, ZMod.stdAddChar (ξ * m) * ZMod.dft Φ ξ := by
  have h := congrFun (ZMod.dft_dft Φ) (-m)
  rw [ZMod.dft_apply] at h
  simp only [neg_neg, smul_eq_mul] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun ξ _ => by congr 2; ring)

-- partial transform: ∑_m Φ(m) sc(ξ' m) = dft Φ (-ξ')
private lemma sum_char_eq_dft_neg {H : ℕ} [NeZero H] (Φ : ZMod H → ℂ) (ξ' : ZMod H) :
    ∑ m : ZMod H, Φ m * ZMod.stdAddChar (ξ' * m) = ZMod.dft Φ (-ξ') := by
  rw [ZMod.dft_apply]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [smul_eq_mul, mul_comm]
  congr 2
  ring

-- the correlation identity
private lemma correlation_dft {H : ℕ} [NeZero H] (Φ₁ Φ₂ : ZMod H → ℂ) (t : ZMod H) :
    (H : ℂ) * ∑ m : ZMod H, Φ₁ m * Φ₂ (m + t)
      = ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) * ZMod.stdAddChar (-(t * ξ)) := by
  calc (H : ℂ) * ∑ m : ZMod H, Φ₁ m * Φ₂ (m + t)
      = ∑ m : ZMod H, Φ₁ m * ((H : ℂ) * Φ₂ (m + t)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)
    _ = ∑ m : ZMod H, Φ₁ m *
          ∑ ξ' : ZMod H, ZMod.stdAddChar (ξ' * (m + t)) * ZMod.dft Φ₂ ξ' := by
        exact Finset.sum_congr rfl (fun m _ => by rw [inv_pt Φ₂ (m + t)])
    _ = ∑ m : ZMod H, ∑ ξ' : ZMod H,
          Φ₁ m * (ZMod.stdAddChar (ξ' * (m + t)) * ZMod.dft Φ₂ ξ') := by
        exact Finset.sum_congr rfl (fun m _ => by rw [Finset.mul_sum])
    _ = ∑ ξ' : ZMod H, ∑ m : ZMod H,
          Φ₁ m * (ZMod.stdAddChar (ξ' * (m + t)) * ZMod.dft Φ₂ ξ') := Finset.sum_comm
    _ = ∑ ξ' : ZMod H, ZMod.dft Φ₂ ξ' * ZMod.stdAddChar (ξ' * t) *
          ∑ m : ZMod H, Φ₁ m * ZMod.stdAddChar (ξ' * m) := by
        refine Finset.sum_congr rfl (fun ξ' _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [show ξ' * (m + t) = ξ' * m + ξ' * t by ring, ZMod.stdAddChar.map_add_eq_mul]
        ring
    _ = ∑ ξ' : ZMod H, ZMod.dft Φ₂ ξ' * ZMod.stdAddChar (ξ' * t) * ZMod.dft Φ₁ (-ξ') := by
        exact Finset.sum_congr rfl (fun ξ' _ => by rw [sum_char_eq_dft_neg Φ₁ ξ'])
    _ = ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) * ZMod.stdAddChar (-(t * ξ)) := by
        rw [← Equiv.sum_comp (Equiv.neg (ZMod H))
          (fun ξ' => ZMod.dft Φ₂ ξ' * ZMod.stdAddChar (ξ' * t) * ZMod.dft Φ₁ (-ξ'))]
        refine Finset.sum_congr rfl (fun ξ _ => ?_)
        simp only [Equiv.neg_apply, neg_neg]
        rw [show (-ξ) * t = -(t * ξ) by ring]
        ring

-- Φ bound
private lemma windowVal_c_norm_le {H : ℕ} {x : Fin H → ℤ} (hx : ∀ i, |x i| ≤ 1) (m : ZMod H) :
    ‖((windowVal H x m.val : ℤ) : ℂ)‖ ≤ 1 := by
  rw [show ((windowVal H x m.val : ℤ) : ℂ) = ((windowVal H x m.val : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real]
  exact windowVal_abs_le hx m.val

-- box bound: ‖dft Φ ξ‖ ≤ H when ‖Φ j‖ ≤ 1
private lemma dft_norm_le_card {H : ℕ} [NeZero H] (Φ : ZMod H → ℂ) (hΦ : ∀ j, ‖Φ j‖ ≤ 1)
    (ξ : ZMod H) : ‖ZMod.dft Φ ξ‖ ≤ (H : ℝ) := by
  rw [ZMod.dft_apply]
  calc ‖∑ j : ZMod H, ZMod.stdAddChar (-(j * ξ)) • Φ j‖
      ≤ ∑ j : ZMod H, ‖ZMod.stdAddChar (-(j * ξ)) • Φ j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : ZMod H, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [smul_eq_mul, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]
        exact hΦ j
    _ = (H : ℝ) := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]

-- reflection l1 bound: ∑_ξ ‖dft Φ₁ ξ‖ ‖dft Φ₂ (-ξ)‖ ≤ H²
private lemma dft_l1_reflect {H : ℕ} [NeZero H] (Φ₁ Φ₂ : ZMod H → ℂ)
    (h1 : ∀ j, ‖Φ₁ j‖ ≤ 1) (h2 : ∀ j, ‖Φ₂ j‖ ≤ 1) :
    ∑ ξ : ZMod H, ‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖ ≤ (H : ℝ) ^ 2 := by
  have hrefl : ∀ ξ : ZMod H, ZMod.dft Φ₂ (-ξ) = ZMod.dft (fun j => Φ₂ (-j)) ξ := by
    intro ξ; rw [ZMod.dft_comp_neg]
  have key := dft_l1_bound Φ₁ (fun j => Φ₂ (-j)) 1 h1 (fun j => h2 (-j)) 0
  simp only [add_zero, one_pow, mul_one] at key
  calc ∑ ξ : ZMod H, ‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖
      = ∑ ξ : ZMod H, ‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft (fun j => Φ₂ (-j)) ξ‖ := by
        refine Finset.sum_congr rfl (fun ξ _ => ?_); rw [hrefl ξ]
    _ ≤ (H : ℝ) ^ 2 := key

-- expSum connection
private lemma expSum_eq_char_sum {eps : ℚ} {H : ℕ} [NeZero H] (ξ : ZMod H) :
    expSum eps H (-(ξ.val : ℝ) / (H : ℝ))
      = ∑ p : primeWindow eps H,
          (1 / ((p : ℕ) : ℂ)) * ZMod.stdAddChar (-((((p : ℕ)) : ZMod H) * ξ)) := by
  unfold expSum
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hd : ZMod.stdAddChar (-((((p : ℕ)) : ZMod H) * ξ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((-(ξ.val : ℝ) / (H : ℝ)) : ℂ) * ((p : ℕ) : ℂ)) := by
    have hrw : -((((p : ℕ)) : ZMod H) * ξ) = ((-(((p : ℕ)) * ξ.val : ℕ) : ℤ) : ZMod H) := by
      push_cast [ZMod.natCast_zmod_val]; ring
    rw [hrw, ZMod.stdAddChar_coe]; push_cast; ring_nf
  rw [hd]; congr 2; push_cast; ring

-- ∑_{p ∈ primeWindow} 1/p ≤ 2 C₀ / log H
private lemma sum_inv_p_le {eps : ℚ} {H : ℕ} [NeZero H] {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hlog : 0 < Real.log (H : ℝ))
    (hcard : ((primeWindow eps H).card : ℝ) ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))) :
    ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℝ)) ≤ 2 * C₀ / Real.log (H : ℝ) := by
  rcases Finset.eq_empty_or_nonempty (primeWindow eps H) with hemp | hne
  · haveI : IsEmpty (primeWindow eps H) := Finset.isEmpty_coe_sort.mpr hemp
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    positivity
  · -- nonempty: eps²H ≥ 2, each 1/p ≤ 2/(eps²H)
    obtain ⟨p0, hp0⟩ := hne
    have hp0prime := prime_of_mem_primeWindow hp0
    have hepsH_pos : 0 < (eps : ℝ) ^ 2 * (H : ℝ) := by
      have hq : (p0 : ℚ) ≤ eps ^ 2 * (H : ℚ) :=
        le_trans (by exact_mod_cast (mem_primeWindow.mp hp0).1) (Nat.floor_le (by positivity))
      have hr : (p0 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by exact_mod_cast hq
      have h2 : (2 : ℝ) ≤ (p0 : ℝ) := by exact_mod_cast hp0prime.two_le
      linarith
    have hbound : ∀ p : primeWindow eps H, (1 / ((p : ℕ) : ℝ)) ≤ 2 / ((eps : ℝ) ^ 2 * (H : ℝ)) := by
      intro p
      have hlb := window_lb eps H p
      have hpp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast (prime_of_mem_primeWindow p.2).pos
      rw [div_le_div_iff₀ hpp hepsH_pos]
      nlinarith [hlb]
    calc ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℝ))
        ≤ ∑ _p : primeWindow eps H, 2 / ((eps : ℝ) ^ 2 * (H : ℝ)) :=
          Finset.sum_le_sum (fun p _ => hbound p)
      _ = ((primeWindow eps H).card : ℝ) * (2 / ((eps : ℝ) ^ 2 * (H : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ ≤ (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
            * (2 / ((eps : ℝ) ^ 2 * (H : ℝ))) := by
          gcongr
      _ = 2 * C₀ / Real.log (H : ℝ) := by
          have h1 : (eps : ℝ) ≠ 0 := fun h => by simp [h] at hepsH_pos
          have h2 : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne H)
          have h3 : Real.log (H : ℝ) ≠ 0 := ne_of_gt hlog
          field_simp

-- ‖expSum α‖ ≤ ∑_p 1/p
private lemma expSum_norm_le_sum {eps : ℚ} {H : ℕ} [NeZero H] (α : ℝ) :
    ‖expSum eps H α‖ ≤ ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℝ)) := by
  unfold expSum
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((p : ℕ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have : (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((p : ℕ) : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero]
  rw [this, mul_one]

private lemma expSum_norm_le_major {eps : ℚ} {H : ℕ} [NeZero H] {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hlog : 0 < Real.log (H : ℝ))
    (hcard : ((primeWindow eps H).card : ℝ) ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (α : ℝ) :
    ‖expSum eps H α‖ ≤ 2 * C₀ / Real.log (H : ℝ) :=
  (expSum_norm_le_sum α).trans (sum_inv_p_le hC₀ hlog hcard)

-- membership in bigXi
private lemma mem_bigXi {eps : ℚ} {H : ℕ} [NeZero H] {ξ : ZMod H} :
    ξ ∈ bigXi eps H ↔
      (eps : ℝ) ^ 2 / Real.log (H : ℝ) ≤ ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ := by
  unfold bigXi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

-- the Fourier split
private lemma fourier_split {eps : ℚ} {H : ℕ} [NeZero H] (Φ₁ Φ₂ : ZMod H → ℂ)
    (h1 : ∀ j, ‖Φ₁ j‖ ≤ 1) (h2 : ∀ j, ‖Φ₂ j‖ ≤ 1)
    {C₀ : ℝ} (hC₀ : 0 < C₀) (hlog : 0 < Real.log (H : ℝ))
    (hcard : ((primeWindow eps H).card : ℝ) ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))) :
    ‖∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
        expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖
      ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
        + (2 * C₀ * (H : ℝ) / Real.log (H : ℝ)) * ∑ ξ ∈ bigXi eps H, ‖ZMod.dft Φ₁ ξ‖ := by
  classical
  set g : ZMod H → ℝ := fun ξ =>
    ‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖ * ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ with hg
  have hstep1 : ‖∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
      expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ ≤ ∑ ξ : ZMod H, g ξ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [hg]; simp only; rw [norm_mul, norm_mul]
  refine hstep1.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ξ => ξ ∈ bigXi eps H) g]
  have hfilt : Finset.univ.filter (fun ξ => ξ ∈ bigXi eps H) = bigXi eps H := by
    ext ξ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hmajor : ∑ ξ ∈ Finset.univ.filter (fun ξ => ξ ∈ bigXi eps H), g ξ
      ≤ (2 * C₀ * (H : ℝ) / Real.log (H : ℝ)) * ∑ ξ ∈ bigXi eps H, ‖ZMod.dft Φ₁ ξ‖ := by
    rw [hfilt, Finset.mul_sum]
    refine Finset.sum_le_sum (fun ξ _ => ?_)
    rw [hg]; simp only
    have hb2 : ‖ZMod.dft Φ₂ (-ξ)‖ ≤ (H : ℝ) := dft_norm_le_card Φ₂ h2 (-ξ)
    have hbe : ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ ≤ 2 * C₀ / Real.log (H : ℝ) :=
      expSum_norm_le_major hC₀ hlog hcard _
    calc ‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖ * ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖
        ≤ ‖ZMod.dft Φ₁ ξ‖ * (H : ℝ) * (2 * C₀ / Real.log (H : ℝ)) := by gcongr
      _ = 2 * C₀ * (H : ℝ) / Real.log (H : ℝ) * ‖ZMod.dft Φ₁ ξ‖ := by ring
  have hminor : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXi eps H), g ξ
      ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ) := by
    have hle : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXi eps H), g ξ
        ≤ ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXi eps H),
            ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) * (‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖) := by
      refine Finset.sum_le_sum (fun ξ hξ => ?_)
      rw [Finset.mem_filter] at hξ
      have hlt : ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ < (eps : ℝ) ^ 2 / Real.log (H : ℝ) :=
        not_le.mp (fun h => hξ.2 (mem_bigXi.mpr h))
      rw [hg]; simp only
      calc ‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖ * ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖
          ≤ ‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖ * ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) := by
            gcongr
        _ = (eps : ℝ) ^ 2 / Real.log (H : ℝ) * (‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖) := by ring
    refine hle.trans ?_
    rw [← Finset.mul_sum]
    have hl1 : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXi eps H),
        (‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖)
          ≤ ∑ ξ : ZMod H, ‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun ξ _ _ => by positivity)
    have hl2 := dft_l1_reflect Φ₁ Φ₂ h1 h2
    calc (eps : ℝ) ^ 2 / Real.log (H : ℝ) *
          ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXi eps H),
            (‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖)
        ≤ (eps : ℝ) ^ 2 / Real.log (H : ℝ) * (H : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (hl1.trans hl2) (div_nonneg (by positivity) hlog.le)
      _ = (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ) := by ring
  linarith [hmajor, hminor]

-- T collapse: (H) * T = W
private lemma T_collapse {eps : ℚ} {H : ℕ} [NeZero H] (Φ₁ Φ₂ : ZMod H → ℂ) :
    (H : ℂ) * ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ∑ m : ZMod H, Φ₁ m * Φ₂ (m + ((p : ℕ) : ZMod H))
      = ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
          expSum eps H (-(ξ.val : ℝ) / (H : ℝ)) := by
  calc (H : ℂ) * ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ∑ m : ZMod H, Φ₁ m * Φ₂ (m + ((p : ℕ) : ZMod H))
      = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
          ((H : ℂ) * ∑ m : ZMod H, Φ₁ m * Φ₂ (m + ((p : ℕ) : ZMod H))) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
    _ = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
          ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
            ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * ξ)) := by
        exact Finset.sum_congr rfl (fun p _ => by
          rw [correlation_dft Φ₁ Φ₂ ((p : ℕ) : ZMod H)])
    _ = ∑ p : primeWindow eps H, ∑ ξ : ZMod H, (1 / ((p : ℕ) : ℂ)) *
          (ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) * ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * ξ))) := by
        exact Finset.sum_congr rfl (fun p _ => by rw [Finset.mul_sum])
    _ = ∑ ξ : ZMod H, ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
          (ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) * ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * ξ))) :=
        Finset.sum_comm
    _ = ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
          ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
            ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * ξ)) := by
        refine Finset.sum_congr rfl (fun ξ _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by ring)
    _ = ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
          expSum eps H (-(ξ.val : ℝ) / (H : ℝ)) := by
        exact Finset.sum_congr rfl (fun ξ _ => by rw [← expSum_eq_char_sum ξ])

-- norm of a windowVal cast (nat index version)
private lemma wv_c_norm {H : ℕ} {x : Fin H → ℤ} (hx : ∀ i, |x i| ≤ 1) (j : ℕ) :
    ‖((windowVal H x j : ℤ) : ℂ)‖ ≤ 1 := by
  rw [show ((windowVal H x j : ℤ) : ℂ) = ((windowVal H x j : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real]
  exact windowVal_abs_le hx j

-- count of wraparound indices ≤ p
private lemma card_wrap_le {H : ℕ} (p : ℕ) :
    ((Finset.range H).filter (fun j => H ≤ j + p)).card ≤ p := by
  have hsub : (Finset.range H).filter (fun j => H ≤ j + p) ⊆ Finset.Ico (H - p) H := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_Ico]
    exact ⟨by omega, hj.1⟩
  calc ((Finset.range H).filter (fun j => H ≤ j + p)).card
      ≤ (Finset.Ico (H - p) H).card := Finset.card_le_card hsub
    _ = H - (H - p) := Nat.card_Ico _ _
    _ ≤ p := by omega

-- per-prime periodization difference
private lemma perprime_diff_norm_le {H : ℕ} [NeZero H] {x1 x2 : Fin H → ℤ}
    (hx1 : ∀ i, |x1 i| ≤ 1) (hx2 : ∀ i, |x2 i| ≤ 1) (p : ℕ) :
    ‖((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) * (windowVal H x2 (j + p) : ℝ) : ℝ) : ℂ)
      - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
          ((windowVal H x2 (m + (p : ZMod H)).val : ℤ) : ℂ)‖ ≤ (p : ℝ) := by
  classical
  set a : ℕ → ℂ := fun j => ((windowVal H x1 j : ℤ) : ℂ) with ha
  set b : ℕ → ℂ := fun j => ((windowVal H x2 (j + p) : ℤ) : ℂ) with hb
  set c : ℕ → ℂ := fun j => ((windowVal H x2 ((j + p) % H) : ℤ) : ℂ) with hc
  -- rewrite real sum cast
  have hleft : ((∑ j ∈ Finset.range H,
      (windowVal H x1 j : ℝ) * (windowVal H x2 (j + p) : ℝ) : ℝ) : ℂ)
        = ∑ j ∈ Finset.range H, a j * b j := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ha, hb]; push_cast; ring
  -- rewrite ZMod sum
  have hright : ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
        ((windowVal H x2 (m + (p : ZMod H)).val : ℤ) : ℂ)
      = ∑ j ∈ Finset.range H, a j * c j := by
    rw [show (∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
          ((windowVal H x2 (m + (p : ZMod H)).val : ℤ) : ℂ))
        = ∑ j ∈ Finset.range H, ((windowVal H x1 ((j : ZMod H).val) : ℤ) : ℂ) *
          ((windowVal H x2 (((j : ZMod H) + (p : ZMod H)).val) : ℤ) : ℂ) from
      Finset.sum_nbij' (fun m : ZMod H => m.val) (fun j : ℕ => (j : ZMod H))
        (fun m _ => Finset.mem_range.mpr (ZMod.val_lt m)) (fun j _ => Finset.mem_univ _)
        (fun m _ => ZMod.natCast_zmod_val m)
        (fun j hj => ZMod.val_natCast_of_lt (Finset.mem_range.mp hj))
        (fun m _ => by rw [ZMod.natCast_zmod_val])]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hv1 : (j : ZMod H).val = j := ZMod.val_natCast_of_lt hj
    have hv2 : ((j : ZMod H) + (p : ZMod H)).val = (j + p) % H := by
      rw [← Nat.cast_add, ZMod.val_natCast]
    rw [ha, hc, hv1, hv2]
  rw [hleft, hright, ← Finset.sum_sub_distrib]
  calc ‖∑ j ∈ Finset.range H, (a j * b j - a j * c j)‖
      ≤ ∑ j ∈ Finset.range H, ‖a j * b j - a j * c j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range H, (if H ≤ j + p then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [← mul_sub, norm_mul]
        split_ifs with hjp
        · have hb0 : b j = 0 := by rw [hb]; simp only; rw [windowVal, dif_neg (by omega)]; simp
          rw [hb0, zero_sub, norm_neg]
          calc ‖a j‖ * ‖c j‖ ≤ 1 * 1 :=
                mul_le_mul (wv_c_norm hx1 j) (wv_c_norm hx2 _) (norm_nonneg _) (by norm_num)
            _ = 1 := by norm_num
        · have hbc : b j = c j := by
            rw [hb, hc]; simp only; rw [Nat.mod_eq_of_lt (by omega)]
          rw [hbc, sub_self, norm_zero, mul_zero]
    _ = (((Finset.range H).filter (fun j => H ≤ j + p)).card : ℝ) := by rw [Finset.sum_boole]
    _ ≤ (p : ℝ) := by exact_mod_cast card_wrap_le p

-- total periodization
private lemma periodization_total {eps : ℚ} {H : ℕ} [NeZero H] {x1 x2 : Fin H → ℤ}
    (hx1 : ∀ i, |x1 i| ≤ 1) (hx2 : ∀ i, |x2 i| ≤ 1) :
    ‖∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        (((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
            (windowVal H x2 (j + (p : ℕ)) : ℝ) : ℝ) : ℂ)
          - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
              ((windowVal H x2 (m + ((p : ℕ) : ZMod H)).val : ℤ) : ℂ))‖
      ≤ ((primeWindow eps H).card : ℝ) := by
  calc ‖∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        (((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
            (windowVal H x2 (j + (p : ℕ)) : ℝ) : ℝ) : ℂ)
          - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
              ((windowVal H x2 (m + ((p : ℕ) : ZMod H)).val : ℤ) : ℂ))‖
      ≤ ∑ p : primeWindow eps H, ‖(1 / ((p : ℕ) : ℂ)) *
          (((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
              (windowVal H x2 (j + (p : ℕ)) : ℝ) : ℝ) : ℂ)
            - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
                ((windowVal H x2 (m + ((p : ℕ) : ZMod H)).val : ℤ) : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ _p : primeWindow eps H, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
        have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by
          exact_mod_cast (prime_of_mem_primeWindow p.2).pos
        rw [div_mul_eq_mul_div, one_mul, div_le_one hp0]
        exact perprime_diff_norm_le hx1 hx2 (p : ℕ)
    _ = ((primeWindow eps H).card : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one]

theorem circle_method_estimate (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 x2 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) → (∀ i, |x2 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) *
          ∑ j ∈ Finset.range H,
            (windowVal H x1 j : ℝ) * (windowVal H x2 (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ)) *
            ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi eps H, (1 / (H : ℝ)) *
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖) := by
  refine ⟨1 + 2 * C₀, by positivity, ?_⟩
  intro eps H _ x1 x2 hx1 hx2 hcard
  by_cases hH2 : 2 ≤ H
  · -- main regime: H ≥ 2, so log H > 0
    have hH1r : (1 : ℝ) < (H : ℝ) := by exact_mod_cast hH2
    have hlog : 0 < Real.log (H : ℝ) := Real.log_pos hH1r
    have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
    set Φ₁ : ZMod H → ℂ := fun m => ((windowVal H x1 m.val : ℤ) : ℂ) with hΦ₁
    set Φ₂ : ZMod H → ℂ := fun m => ((windowVal H x2 m.val : ℤ) : ℂ) with hΦ₂
    have h1 : ∀ j, ‖Φ₁ j‖ ≤ 1 := fun j => windowVal_c_norm_le hx1 j
    have h2 : ∀ j, ‖Φ₂ j‖ ≤ 1 := fun j => windowVal_c_norm_le hx2 j
    set S : ℝ := ∑ ξ ∈ bigXi eps H, ‖ZMod.dft Φ₁ ξ‖ with hS
    set L : ℝ := ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
        ∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) * (windowVal H x2 (j + (p : ℕ)) : ℝ) with hL
    set T : ℂ := ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ∑ m : ZMod H, Φ₁ m * Φ₂ (m + ((p : ℕ) : ZMod H)) with hT
    set W : ℂ := ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
        expSum eps H (-(ξ.val : ℝ) / (H : ℝ)) with hW
    -- collapse and split
    have hWT : (H : ℂ) * T = W := T_collapse Φ₁ Φ₂
    have hTnorm : (H : ℝ) * ‖T‖ = ‖W‖ := by
      rw [← hWT, norm_mul, Complex.norm_natCast]
    have hnormW : ‖W‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
        + (2 * C₀ * (H : ℝ) / Real.log (H : ℝ)) * S :=
      fourier_split Φ₁ Φ₂ h1 h2 hC₀ hlog hcard
    -- cast L and periodization
    have hLcast : ((L : ℝ) : ℂ) = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
          (windowVal H x2 (j + (p : ℕ)) : ℝ) : ℝ) : ℂ) := by
      rw [hL, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      push_cast
      ring
    have hdiff : ((L : ℝ) : ℂ) - T = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        (((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
            (windowVal H x2 (j + (p : ℕ)) : ℝ) : ℝ) : ℂ)
          - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
              ((windowVal H x2 (m + ((p : ℕ) : ZMod H)).val : ℤ) : ℂ)) := by
      rw [hLcast, hT, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun p _ => by rw [mul_sub])
    have hperiod : ‖((L : ℝ) : ℂ) - T‖ ≤ ((primeWindow eps H).card : ℝ) := by
      rw [hdiff]; exact periodization_total hx1 hx2
    -- assemble
    have hLT : |L| ≤ ‖T‖ + ((primeWindow eps H).card : ℝ) := by
      have h := norm_add_le T (((L : ℝ) : ℂ) - T)
      rw [add_sub_cancel] at h
      calc |L| = ‖((L : ℝ) : ℂ)‖ := (Complex.norm_real L).symm
        _ ≤ ‖T‖ + ‖((L : ℝ) : ℂ) - T‖ := h
        _ ≤ ‖T‖ + ((primeWindow eps H).card : ℝ) := by linarith [hperiod]
    have hH0 : (H : ℝ) ≠ 0 := ne_of_gt hHpos
    have hLe0 : Real.log (H : ℝ) ≠ 0 := ne_of_gt hlog
    have hTle : ‖T‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
        + 2 * C₀ / Real.log (H : ℝ) * S := by
      have hHTle : (H : ℝ) * ‖T‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
          + (2 * C₀ * (H : ℝ) / Real.log (H : ℝ)) * S := hTnorm ▸ hnormW
      have key : (H : ℝ) * ‖T‖ ≤ (H : ℝ) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
          + 2 * C₀ / Real.log (H : ℝ) * S) := by
        refine hHTle.trans (le_of_eq ?_)
        ring
      exact le_of_mul_le_mul_left key hHpos
    rw [← Finset.mul_sum, ← hS]
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun ξ _ => norm_nonneg _)
    have hquot_nn : 0 ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) := by positivity
    have hrem_nn : 0 ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
        + S / Real.log (H : ℝ) :=
      add_nonneg (mul_nonneg hC₀.le hquot_nn) (div_nonneg hS_nn hlog.le)
    have heq : (1 + 2 * C₀) * ((H : ℝ) / Real.log (H : ℝ))
          * ((eps : ℝ) ^ 2 + 1 / (H : ℝ) * S)
        = ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) + 2 * C₀ / Real.log (H : ℝ) * S)
          + C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
          + (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) + S / Real.log (H : ℝ)) := by
      field_simp
      ring
    calc |L| ≤ ‖T‖ + ((primeWindow eps H).card : ℝ) := hLT
      _ ≤ (1 + 2 * C₀) * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + 1 / (H : ℝ) * S) := by
          rw [heq]; linarith [hTle, hcard, hrem_nn]
  · -- degenerate: H = 1
    have hH1 : H = 1 := by have := NeZero.pos H; omega
    have hlog0 : Real.log (H : ℝ) = 0 := by rw [hH1]; simp
    have hL0 : (∑ p : primeWindow eps H, (1 / (p : ℝ)) *
        ∑ j ∈ Finset.range H,
          (windowVal H x1 j : ℝ) * (windowVal H x2 (j + (p : ℕ)) : ℝ)) = 0 := by
      refine Finset.sum_eq_zero (fun p _ => ?_)
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      have hp2 := (prime_of_mem_primeWindow p.2).two_le
      have hge : ¬ (j + (p : ℕ) < H) := by omega
      have hz : windowVal H x2 (j + (p : ℕ)) = 0 := by rw [windowVal, dif_neg hge]
      rw [hz]; simp
    rw [hL0, abs_zero]
    have hmid : (H : ℝ) / Real.log (H : ℝ) = 0 := by rw [hlog0, div_zero]
    rw [hmid]; simp

/-! ### ⟦THE L² RESTRUCTURE⟧ stone 1 — the SQUARED major arm (additive twins)

`fourier_split` (above) discards the second Fourier factor on the major arc at
its trivial bound `‖dft Φ₂ (−ξ)‖ ≤ H`.  On the DIAGONAL — `Φ₁ = Φ₂ = Φ` with `Φ`
REAL-valued, which is the shell's only instantiation (`x₁ = x₂ = liouvilleWindow H n`,
`Theorem23Shell.lean` reads `liouvilleWindow` twice) — that factor equals
`‖dft Φ ξ‖` itself (`norm_dft_neg_of_real`), so KEEPING it turns the major arm
into `(2C₀/log H)·Σ_{ξ∈Ξ}‖dft Φ ξ‖²`.  This is a STRICT TIGHTENING of the landed
estimate (termwise: `‖dft Φ ξ‖ ≤ H`), delivered at the squared, per-`H²`
normalization `Σ_{ξ∈Ξ}(1/H²)‖dft Φ ξ‖²` mirroring the landed `Σ_{ξ∈Ξ}(1/H)‖dft Φ ξ‖`.
The output constant is UNCHANGED: `C = 1 + 2·C₀`.

Purely additive — `fourier_split` and `circle_method_estimate` are untouched.
The twins live in-file because the split/collapse/periodization lemmas they
consume are `private` (the S0-TOWER precedent). -/

/-- **The reality reflection.**  For a REAL-valued datum the reflected transform has the
same modulus, `‖𝓕Φ (−ξ)‖ = ‖𝓕Φ ξ‖` (`𝓕Φ (−ξ) = conj (𝓕Φ ξ)`).  This is the identity
that licenses KEEPING `fourier_split`'s discarded second factor on the diagonal. -/
theorem norm_dft_neg_of_real {N : ℕ} [NeZero N] (r : ZMod N → ℝ) (ξ : ZMod N) :
    ‖ZMod.dft (fun j => ((r j : ℝ) : ℂ)) (-ξ)‖ = ‖ZMod.dft (fun j => ((r j : ℝ) : ℂ)) ξ‖ := by
  have hconj : ZMod.dft (fun j => ((r j : ℝ) : ℂ)) (-ξ)
      = (starRingEnd ℂ) (ZMod.dft (fun j => ((r j : ℝ) : ℂ)) ξ) := by
    rw [ZMod.dft_apply, ZMod.dft_apply, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal]
    congr 1
    rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj,
      ← AddChar.map_neg_eq_inv]
    congr 2
    ring
  rw [hconj, RCLike.norm_conj]

/-- **Stone 1a, the squared Fourier split** (the `fourier_split` twin on the diagonal).

Same minor arc (`mem_bigXi` + `dft_l1_reflect`), but the MAJOR arm keeps the second
factor: with `hrefl : ‖𝓕Φ (−ξ)‖ = ‖𝓕Φ ξ‖` (supplied by `norm_dft_neg_of_real` at a
real datum) each major term is `‖𝓕Φ ξ‖²·‖S_H(−ξ/H)‖ ≤ (2C₀/log H)·‖𝓕Φ ξ‖²`, so

`‖Σ_ξ 𝓕Φ ξ · 𝓕Φ(−ξ) · S_H(−ξ/H)‖ ≤ ε²H²/log H + (2C₀/log H)·Σ_{ξ∈Ξ}‖𝓕Φ ξ‖²`.

Against `fourier_split`'s `(2C₀H/log H)·Σ_{ξ∈Ξ}‖𝓕Φ ξ‖` this is a strict tightening
(termwise `‖𝓕Φ ξ‖ ≤ H`). -/
theorem fourier_split_sq {eps : ℚ} {H : ℕ} [NeZero H] (Φ : ZMod H → ℂ)
    (h1 : ∀ j, ‖Φ j‖ ≤ 1) (hrefl : ∀ ξ : ZMod H, ‖ZMod.dft Φ (-ξ)‖ = ‖ZMod.dft Φ ξ‖)
    {C₀ : ℝ} (hC₀ : 0 < C₀) (hlog : 0 < Real.log (H : ℝ))
    (hcard : ((primeWindow eps H).card : ℝ) ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))) :
    ‖∑ ξ : ZMod H, ZMod.dft Φ ξ * ZMod.dft Φ (-ξ) *
        expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖
      ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
        + (2 * C₀ / Real.log (H : ℝ)) * ∑ ξ ∈ bigXi eps H, ‖ZMod.dft Φ ξ‖ ^ 2 := by
  classical
  set g : ZMod H → ℝ := fun ξ =>
    ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖ * ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ with hg
  have hstep1 : ‖∑ ξ : ZMod H, ZMod.dft Φ ξ * ZMod.dft Φ (-ξ) *
      expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ ≤ ∑ ξ : ZMod H, g ξ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [hg]; simp only; rw [norm_mul, norm_mul]
  refine hstep1.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ξ => ξ ∈ bigXi eps H) g]
  have hfilt : Finset.univ.filter (fun ξ => ξ ∈ bigXi eps H) = bigXi eps H := by
    ext ξ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hmajor : ∑ ξ ∈ Finset.univ.filter (fun ξ => ξ ∈ bigXi eps H), g ξ
      ≤ (2 * C₀ / Real.log (H : ℝ)) * ∑ ξ ∈ bigXi eps H, ‖ZMod.dft Φ ξ‖ ^ 2 := by
    rw [hfilt, Finset.mul_sum]
    refine Finset.sum_le_sum (fun ξ _ => ?_)
    rw [hg]; simp only
    have hbe : ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ ≤ 2 * C₀ / Real.log (H : ℝ) :=
      expSum_norm_le_major hC₀ hlog hcard _
    calc ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖ * ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖
        = ‖ZMod.dft Φ ξ‖ ^ 2 * ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ := by
          rw [hrefl ξ]; ring
      _ ≤ ‖ZMod.dft Φ ξ‖ ^ 2 * (2 * C₀ / Real.log (H : ℝ)) := by gcongr
      _ = 2 * C₀ / Real.log (H : ℝ) * ‖ZMod.dft Φ ξ‖ ^ 2 := by ring
  have hminor : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXi eps H), g ξ
      ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ) := by
    have hle : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXi eps H), g ξ
        ≤ ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXi eps H),
            ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) * (‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖) := by
      refine Finset.sum_le_sum (fun ξ hξ => ?_)
      rw [Finset.mem_filter] at hξ
      have hlt : ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ < (eps : ℝ) ^ 2 / Real.log (H : ℝ) :=
        not_le.mp (fun h => hξ.2 (mem_bigXi.mpr h))
      rw [hg]; simp only
      calc ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖ * ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖
          ≤ ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖ * ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) := by
            gcongr
        _ = (eps : ℝ) ^ 2 / Real.log (H : ℝ) * (‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖) := by ring
    refine hle.trans ?_
    rw [← Finset.mul_sum]
    have hl1 : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXi eps H),
        (‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖)
          ≤ ∑ ξ : ZMod H, ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun ξ _ _ => by positivity)
    have hl2 := dft_l1_reflect Φ Φ h1 h1
    calc (eps : ℝ) ^ 2 / Real.log (H : ℝ) *
          ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXi eps H),
            (‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖)
        ≤ (eps : ℝ) ^ 2 / Real.log (H : ℝ) * (H : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (hl1.trans hl2) (div_nonneg (by positivity) hlog.le)
      _ = (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ) := by ring
  linarith [hmajor, hminor]

/-- **Stone 1b, the squared circle-method estimate** — the `circle_method_estimate` twin at
the DIAGONAL window `x₁ = x₂` (the shell's only instantiation), with the major arm's second
Fourier factor KEPT:

`|Σ_p (1/p) Σ_j x_j x_{j+p}| ≤ C·(H/log H)·(ε² + Σ_{ξ∈Ξ}(1/H²)‖𝓕Φ ξ‖²)`,  `C = 1 + 2C₀`.

Same constant as `circle_method_estimate` (the `hbudget1` block downstream is unchanged);
the only change is `Σ_{ξ∈Ξ}(1/H)‖𝓕Φ ξ‖ ↦ Σ_{ξ∈Ξ}(1/H²)‖𝓕Φ ξ‖²` — the L² socket that the
Ξ-summed door consumes K-free. -/
theorem circle_method_estimate_sq (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) *
          ∑ j ∈ Finset.range H,
            (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ)) *
            ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi eps H, (1 / (H : ℝ) ^ 2) *
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2) := by
  refine ⟨1 + 2 * C₀, by positivity, ?_⟩
  intro eps H _ x1 hx1 hcard
  by_cases hH2 : 2 ≤ H
  · -- main regime: H ≥ 2, so log H > 0
    have hH1r : (1 : ℝ) < (H : ℝ) := by exact_mod_cast hH2
    have hlog : 0 < Real.log (H : ℝ) := Real.log_pos hH1r
    have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
    set Φ₁ : ZMod H → ℂ := fun m => ((windowVal H x1 m.val : ℤ) : ℂ) with hΦ₁
    have h1 : ∀ j, ‖Φ₁ j‖ ≤ 1 := fun j => windowVal_c_norm_le hx1 j
    -- the reality reflection at the (real, integer-valued) window datum
    have hreal : Φ₁ = fun j : ZMod H => ((windowVal H x1 (ZMod.val j) : ℝ) : ℂ) := by
      funext j
      simp only [hΦ₁]
      push_cast
      ring
    have hrefl : ∀ ξ : ZMod H, ‖ZMod.dft Φ₁ (-ξ)‖ = ‖ZMod.dft Φ₁ ξ‖ := by
      intro ξ
      rw [hreal]
      exact norm_dft_neg_of_real (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℝ)) ξ
    set S : ℝ := ∑ ξ ∈ bigXi eps H, ‖ZMod.dft Φ₁ ξ‖ ^ 2 with hS
    set L : ℝ := ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
        ∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ)) : ℝ) with hL
    set T : ℂ := ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ∑ m : ZMod H, Φ₁ m * Φ₁ (m + ((p : ℕ) : ZMod H)) with hT
    set W : ℂ := ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₁ (-ξ) *
        expSum eps H (-(ξ.val : ℝ) / (H : ℝ)) with hW
    -- collapse and split (the SQUARED major arm)
    have hWT : (H : ℂ) * T = W := T_collapse Φ₁ Φ₁
    have hTnorm : (H : ℝ) * ‖T‖ = ‖W‖ := by
      rw [← hWT, norm_mul, Complex.norm_natCast]
    have hnormW : ‖W‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
        + (2 * C₀ / Real.log (H : ℝ)) * S :=
      fourier_split_sq Φ₁ h1 hrefl hC₀ hlog hcard
    -- cast L and periodization (the diagonal instance of `periodization_total`)
    have hLcast : ((L : ℝ) : ℂ) = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
          (windowVal H x1 (j + (p : ℕ)) : ℝ) : ℝ) : ℂ) := by
      rw [hL, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      push_cast
      ring
    have hdiff : ((L : ℝ) : ℂ) - T = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        (((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
            (windowVal H x1 (j + (p : ℕ)) : ℝ) : ℝ) : ℂ)
          - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
              ((windowVal H x1 (m + ((p : ℕ) : ZMod H)).val : ℤ) : ℂ)) := by
      rw [hLcast, hT, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun p _ => by rw [mul_sub])
    have hperiod : ‖((L : ℝ) : ℂ) - T‖ ≤ ((primeWindow eps H).card : ℝ) := by
      rw [hdiff]; exact periodization_total hx1 hx1
    -- assemble
    have hLT : |L| ≤ ‖T‖ + ((primeWindow eps H).card : ℝ) := by
      have h := norm_add_le T (((L : ℝ) : ℂ) - T)
      rw [add_sub_cancel] at h
      calc |L| = ‖((L : ℝ) : ℂ)‖ := (Complex.norm_real L).symm
        _ ≤ ‖T‖ + ‖((L : ℝ) : ℂ) - T‖ := h
        _ ≤ ‖T‖ + ((primeWindow eps H).card : ℝ) := by linarith [hperiod]
    have hH0 : (H : ℝ) ≠ 0 := ne_of_gt hHpos
    have hLe0 : Real.log (H : ℝ) ≠ 0 := ne_of_gt hlog
    have hTle : ‖T‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
        + 2 * C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) * S := by
      have hHTle : (H : ℝ) * ‖T‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
          + (2 * C₀ / Real.log (H : ℝ)) * S := hTnorm ▸ hnormW
      have key : (H : ℝ) * ‖T‖ ≤ (H : ℝ) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
          + 2 * C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) * S) := by
        refine hHTle.trans (le_of_eq ?_)
        field_simp
      exact le_of_mul_le_mul_left key hHpos
    rw [← Finset.mul_sum, ← hS]
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun ξ _ => sq_nonneg _)
    have hquot_nn : 0 ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) := by positivity
    have hrem_nn : 0 ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
        + (1 / (H : ℝ)) * S / Real.log (H : ℝ) :=
      add_nonneg (mul_nonneg hC₀.le hquot_nn)
        (div_nonneg (mul_nonneg (by positivity) hS_nn) hlog.le)
    have heq : (1 + 2 * C₀) * ((H : ℝ) / Real.log (H : ℝ))
          * ((eps : ℝ) ^ 2 + 1 / (H : ℝ) ^ 2 * S)
        = ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
            + 2 * C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) * S)
          + C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
          + (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
              + (1 / (H : ℝ)) * S / Real.log (H : ℝ)) := by
      field_simp
      ring
    calc |L| ≤ ‖T‖ + ((primeWindow eps H).card : ℝ) := hLT
      _ ≤ (1 + 2 * C₀) * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + 1 / (H : ℝ) ^ 2 * S) := by
          rw [heq]; linarith [hTle, hcard, hrem_nn]
  · -- degenerate: H = 1
    have hH1 : H = 1 := by have := NeZero.pos H; omega
    have hlog0 : Real.log (H : ℝ) = 0 := by rw [hH1]; simp
    have hL0 : (∑ p : primeWindow eps H, (1 / (p : ℝ)) *
        ∑ j ∈ Finset.range H,
          (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ)) : ℝ)) = 0 := by
      refine Finset.sum_eq_zero (fun p _ => ?_)
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      have hp2 := (prime_of_mem_primeWindow p.2).two_le
      have hge : ¬ (j + (p : ℕ) < H) := by omega
      have hz : windowVal H x1 (j + (p : ℕ)) = 0 := by rw [windowVal, dif_neg hge]
      rw [hz]; simp
    rw [hL0, abs_zero]
    have hmid : (H : ℝ) / Real.log (H : ℝ) = 0 := by rw [hlog0, div_zero]
    rw [hmid]; simp

/-! ### ⟦THE `h`-FAMILY ENGINE ROOM⟧ — the circle-method estimate at offset `p·h` (wave W-F2)

The estimate above runs at the model offset `p` (Tao 1509.05422 at `h = 1`).  This block
opens the same machine at the offset `p·h`, ADDITIVELY: `circle_method_estimate`,
`fourier_split`, `T_collapse` and `periodization_total` keep every byte, and the offset-
and frequency-general lemmas (`correlation_dft`, `expSum_eq_char_sum`,
`perprime_diff_norm_le`, `dft_l1_reflect`, `dft_norm_le_card`, `expSum_norm_le_major`)
are REUSED rather than cloned.

WHERE THE TWIST GOES.  At offset `p·h` the character factor is
`e(−(p·h)ξ/H) = e(−p·((h : ZMod H)·ξ)/H)` (`Nat.cast_mul` and associativity), so
`expSum_eq_char_sum` fires at the frequency `(h : ZMod H)·ξ` while the two surviving DFT
factors stay at the UNTWISTED `ξ` and `−ξ`.  The twist therefore lives in exactly one
place — WHICH frequencies are large-spectrum — and `bigXiTwistFilter` is that set,
spelled on the `ZMod` side so that the shift fork's own large-spectrum set matches it
verbatim.

WHY THE SET IS DEFINED HERE.  `Salt.Entropy.Chowla.ShiftFork` IMPORTS this module, so
naming its objects here would be an import cycle; the wrapper that re-states the estimate
over the fork's set lives on the ShiftFork side, and this file stays import-closed.

`0 < h` is CONSUMED TWICE in `circle_method_estimate_h_core`: the constant
`h·(1 + 2·C₀)` is positive only then, and at `H = 1` the vanishing of the window
correlation needs `1 ≤ p·h`, which `Nat.mul_pos` supplies.  At `h = 0` the statement is
FALSE at `H = 1`, not merely unprovable. -/

/-- **The twisted large-spectrum set** — the `ξ ∈ ℤ/Hℤ` whose `h`-MULTIPLE is
large-spectrum: `|S_H(−((h·ξ).val)/H)| ≥ ε²/log H`.  At `h = 1` this is `bigXi` up to the
`Nat.cast_one`/`one_mul` rewrite; at general `h` it is the `μ_h`-preimage of `bigXi`
under `ξ ↦ (h : ZMod H)·ξ`.  The `ZMod`-side spelling of the twist is deliberate: it
makes the shift fork's set equal to this one by a filter congruence rather than by a
periodicity argument. -/
noncomputable def bigXiTwistFilter (h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] :
    Finset (ZMod H) := by
  classical
  exact Finset.univ.filter (fun ξ : ZMod H =>
    (eps : ℝ) ^ 2 / Real.log (H : ℝ)
      ≤ ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖)

-- membership in the twisted large-spectrum set
private lemma mem_bigXiTwistFilter {h : ℕ} {eps : ℚ} {H : ℕ} [NeZero H] {ξ : ZMod H} :
    ξ ∈ bigXiTwistFilter h eps H ↔
      (eps : ℝ) ^ 2 / Real.log (H : ℝ)
        ≤ ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖ := by
  unfold bigXiTwistFilter
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

-- T collapse at offset `p·h`: the DFT factors stay untwisted, the exponential moves
private lemma T_collapse_h {eps : ℚ} {H : ℕ} [NeZero H] (h : ℕ) (Φ₁ Φ₂ : ZMod H → ℂ) :
    (H : ℂ) * ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ∑ m : ZMod H, Φ₁ m * Φ₂ (m + (((p : ℕ) * h : ℕ) : ZMod H))
      = ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
          expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ)) := by
  have hfreq : ∀ (q : ℕ) (ξ : ZMod H),
      -(((q * h : ℕ) : ZMod H) * ξ) = -(((q : ℕ) : ZMod H) * ((h : ZMod H) * ξ)) := by
    intro q ξ
    push_cast
    ring
  calc (H : ℂ) * ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ∑ m : ZMod H, Φ₁ m * Φ₂ (m + (((p : ℕ) * h : ℕ) : ZMod H))
      = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
          ((H : ℂ) * ∑ m : ZMod H, Φ₁ m * Φ₂ (m + (((p : ℕ) * h : ℕ) : ZMod H))) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
    _ = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
          ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
            ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * ((h : ZMod H) * ξ))) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [correlation_dft Φ₁ Φ₂ (((p : ℕ) * h : ℕ) : ZMod H)]
        congr 1
        exact Finset.sum_congr rfl (fun ξ _ => by rw [hfreq (p : ℕ) ξ])
    _ = ∑ p : primeWindow eps H, ∑ ξ : ZMod H, (1 / ((p : ℕ) : ℂ)) *
          (ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
            ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * ((h : ZMod H) * ξ)))) := by
        exact Finset.sum_congr rfl (fun p _ => by rw [Finset.mul_sum])
    _ = ∑ ξ : ZMod H, ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
          (ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
            ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * ((h : ZMod H) * ξ)))) :=
        Finset.sum_comm
    _ = ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
          ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
            ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * ((h : ZMod H) * ξ))) := by
        refine Finset.sum_congr rfl (fun ξ _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by ring)
    _ = ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
          expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ)) := by
        exact Finset.sum_congr rfl
          (fun ξ _ => by rw [← expSum_eq_char_sum ((h : ZMod H) * ξ)])

-- total periodization at offset `p·h`: the per-prime wrap is `p·h`, so the total is `h·|𝒫_H|`
private lemma periodization_total_h {eps : ℚ} {H : ℕ} [NeZero H] (h : ℕ) {x1 x2 : Fin H → ℤ}
    (hx1 : ∀ i, |x1 i| ≤ 1) (hx2 : ∀ i, |x2 i| ≤ 1) :
    ‖∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        (((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
            (windowVal H x2 (j + (p : ℕ) * h) : ℝ) : ℝ) : ℂ)
          - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
              ((windowVal H x2 (m + (((p : ℕ) * h : ℕ) : ZMod H)).val : ℤ) : ℂ))‖
      ≤ (h : ℝ) * ((primeWindow eps H).card : ℝ) := by
  calc ‖∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        (((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
            (windowVal H x2 (j + (p : ℕ) * h) : ℝ) : ℝ) : ℂ)
          - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
              ((windowVal H x2 (m + (((p : ℕ) * h : ℕ) : ZMod H)).val : ℤ) : ℂ))‖
      ≤ ∑ p : primeWindow eps H, ‖(1 / ((p : ℕ) : ℂ)) *
          (((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
              (windowVal H x2 (j + (p : ℕ) * h) : ℝ) : ℝ) : ℂ)
            - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
                ((windowVal H x2 (m + (((p : ℕ) * h : ℕ) : ZMod H)).val : ℤ) : ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _p : primeWindow eps H, (h : ℝ) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
        have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by
          exact_mod_cast (prime_of_mem_primeWindow p.2).pos
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hp0]
        refine le_trans (perprime_diff_norm_le hx1 hx2 ((p : ℕ) * h)) (le_of_eq ?_)
        push_cast
        ring
    _ = (h : ℝ) * ((primeWindow eps H).card : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_comm]

/-- **The Fourier split at the twisted frequency** — the `fourier_split` clone
(`CircleMethod.lean:378-437`) whose exponential sum sits at `−((h·ξ).val)/H` and whose
major arm is summed over `bigXiTwistFilter h eps H`.

It is a CLONE and not an instance: `fourier_split` pins its frequency at the untwisted
`ξ.val` and its set at `bigXi`, and the reindexing `ξ ↦ h·ξ` that would relate them is
unavailable exactly when `gcd(h,H) > 1` — the case the fiber bound
(`bigXiH_card_le_gcd_mul`, `ShiftFork.lean`) exists for.  The two DFT factors are
untouched: they stay at `ξ` and `−ξ`. -/
theorem fourier_split_h {eps : ℚ} {H : ℕ} [NeZero H] (h : ℕ) (Φ₁ Φ₂ : ZMod H → ℂ)
    (h1 : ∀ j, ‖Φ₁ j‖ ≤ 1) (h2 : ∀ j, ‖Φ₂ j‖ ≤ 1)
    {C₀ : ℝ} (hC₀ : 0 < C₀) (hlog : 0 < Real.log (H : ℝ))
    (hcard : ((primeWindow eps H).card : ℝ) ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))) :
    ‖∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
        expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
      ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
        + (2 * C₀ * (H : ℝ) / Real.log (H : ℝ)) *
            ∑ ξ ∈ bigXiTwistFilter h eps H, ‖ZMod.dft Φ₁ ξ‖ := by
  classical
  set g : ZMod H → ℝ := fun ξ =>
    ‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖ *
      ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖ with hg
  have hstep1 : ‖∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
      expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖ ≤ ∑ ξ : ZMod H, g ξ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [hg]; simp only; rw [norm_mul, norm_mul]
  refine hstep1.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun ξ => ξ ∈ bigXiTwistFilter h eps H) g]
  have hfilt : Finset.univ.filter (fun ξ => ξ ∈ bigXiTwistFilter h eps H)
      = bigXiTwistFilter h eps H := by
    ext ξ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hmajor : ∑ ξ ∈ Finset.univ.filter (fun ξ => ξ ∈ bigXiTwistFilter h eps H), g ξ
      ≤ (2 * C₀ * (H : ℝ) / Real.log (H : ℝ)) *
          ∑ ξ ∈ bigXiTwistFilter h eps H, ‖ZMod.dft Φ₁ ξ‖ := by
    rw [hfilt, Finset.mul_sum]
    refine Finset.sum_le_sum (fun ξ _ => ?_)
    rw [hg]; simp only
    have hb2 : ‖ZMod.dft Φ₂ (-ξ)‖ ≤ (H : ℝ) := dft_norm_le_card Φ₂ h2 (-ξ)
    have hbe : ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
        ≤ 2 * C₀ / Real.log (H : ℝ) := expSum_norm_le_major hC₀ hlog hcard _
    calc ‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖ *
          ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
        ≤ ‖ZMod.dft Φ₁ ξ‖ * (H : ℝ) * (2 * C₀ / Real.log (H : ℝ)) := by gcongr
      _ = 2 * C₀ * (H : ℝ) / Real.log (H : ℝ) * ‖ZMod.dft Φ₁ ξ‖ := by ring
  have hminor : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXiTwistFilter h eps H), g ξ
      ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ) := by
    have hle : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXiTwistFilter h eps H), g ξ
        ≤ ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXiTwistFilter h eps H),
            ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) * (‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖) := by
      refine Finset.sum_le_sum (fun ξ hξ => ?_)
      rw [Finset.mem_filter] at hξ
      have hlt : ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
          < (eps : ℝ) ^ 2 / Real.log (H : ℝ) :=
        not_le.mp (fun hle' => hξ.2 (mem_bigXiTwistFilter.mpr hle'))
      rw [hg]; simp only
      calc ‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖ *
            ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
          ≤ ‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖ * ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) := by
            gcongr
        _ = (eps : ℝ) ^ 2 / Real.log (H : ℝ) * (‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖) := by ring
    refine hle.trans ?_
    rw [← Finset.mul_sum]
    have hl1 : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXiTwistFilter h eps H),
        (‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖)
          ≤ ∑ ξ : ZMod H, ‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun ξ _ _ => by positivity)
    have hl2 := dft_l1_reflect Φ₁ Φ₂ h1 h2
    calc (eps : ℝ) ^ 2 / Real.log (H : ℝ) *
          ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXiTwistFilter h eps H),
            (‖ZMod.dft Φ₁ ξ‖ * ‖ZMod.dft Φ₂ (-ξ)‖)
        ≤ (eps : ℝ) ^ 2 / Real.log (H : ℝ) * (H : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (hl1.trans hl2) (div_nonneg (by positivity) hlog.le)
      _ = (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ) := by ring
  linarith [hmajor, hminor]

/-- **Stone 1a-h, the squared Fourier split at the twisted frequency** — the empty cell of a
2×2 grid whose other three are landed: `fourier_split` (untwisted, L¹), `fourier_split_sq`
(untwisted, L²/diagonal, `:724`), `fourier_split_h` (twisted, L¹, above).  This is their
composition and it introduces no new estimate.

From `fourier_split_h` it takes the twist ONLY: the exponential sum sits at
`−((h·ξ).val)/H` and the major arm is summed over `bigXiTwistFilter h eps H`.  It is a CLONE
for the same reason `fourier_split_h` is — the reindex `ξ ↦ h·ξ` that would make it an
instance is unavailable exactly when `gcd(h,H) > 1`.

From `fourier_split_sq` it takes the diagonal: ONE window `Φ`, and the reality reflection
`hrefl : ‖𝓕Φ (−ξ)‖ = ‖𝓕Φ ξ‖` is *where the square comes from* — with `Φ₂ = Φ₁` the major
term's two Fourier factors collapse to `‖𝓕Φ ξ‖²`, so the second factor is KEPT rather than
bounded by `H`.  Hence the constant is `fourier_split_sq`'s `2C₀/log H`, **not**
`fourier_split_h`'s `2C₀·H/log H`: the `H` in the L¹ arm is exactly the factor this diagonal
does not spend.

The minor arc is untouched from `fourier_split_sq` — same `dft_l1_reflect Φ Φ`, same
`ε²H²/log H`.  `0 < h` is NOT required here and is deliberately absent: at `h = 0` the
statement degenerates to the untwisted split at `ξ ↦ 0`, which is still true.  The `0 < h`
fence belongs to the top-level estimate, where it pays for the wraparound. -/
theorem fourier_split_sq_h {eps : ℚ} {H : ℕ} [NeZero H] (h : ℕ) (Φ : ZMod H → ℂ)
    (h1 : ∀ j, ‖Φ j‖ ≤ 1) (hrefl : ∀ ξ : ZMod H, ‖ZMod.dft Φ (-ξ)‖ = ‖ZMod.dft Φ ξ‖)
    {C₀ : ℝ} (hC₀ : 0 < C₀) (hlog : 0 < Real.log (H : ℝ))
    (hcard : ((primeWindow eps H).card : ℝ) ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))) :
    ‖∑ ξ : ZMod H, ZMod.dft Φ ξ * ZMod.dft Φ (-ξ) *
        expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
      ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
        + (2 * C₀ / Real.log (H : ℝ)) * ∑ ξ ∈ bigXiTwistFilter h eps H, ‖ZMod.dft Φ ξ‖ ^ 2 := by
  classical
  set g : ZMod H → ℝ := fun ξ =>
    ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖ *
      ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖ with hg
  have hstep1 : ‖∑ ξ : ZMod H, ZMod.dft Φ ξ * ZMod.dft Φ (-ξ) *
      expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖ ≤ ∑ ξ : ZMod H, g ξ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [hg]; simp only; rw [norm_mul, norm_mul]
  refine hstep1.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ξ => ξ ∈ bigXiTwistFilter h eps H) g]
  have hfilt : Finset.univ.filter (fun ξ => ξ ∈ bigXiTwistFilter h eps H)
      = bigXiTwistFilter h eps H := by
    ext ξ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hmajor : ∑ ξ ∈ Finset.univ.filter (fun ξ => ξ ∈ bigXiTwistFilter h eps H), g ξ
      ≤ (2 * C₀ / Real.log (H : ℝ)) * ∑ ξ ∈ bigXiTwistFilter h eps H, ‖ZMod.dft Φ ξ‖ ^ 2 := by
    rw [hfilt, Finset.mul_sum]
    refine Finset.sum_le_sum (fun ξ _ => ?_)
    rw [hg]; simp only
    have hbe : ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
        ≤ 2 * C₀ / Real.log (H : ℝ) :=
      expSum_norm_le_major hC₀ hlog hcard _
    calc ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖ *
          ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
        = ‖ZMod.dft Φ ξ‖ ^ 2 * ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖ := by
          rw [hrefl ξ]; ring
      _ ≤ ‖ZMod.dft Φ ξ‖ ^ 2 * (2 * C₀ / Real.log (H : ℝ)) := by gcongr
      _ = 2 * C₀ / Real.log (H : ℝ) * ‖ZMod.dft Φ ξ‖ ^ 2 := by ring
  have hminor : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXiTwistFilter h eps H), g ξ
      ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ) := by
    have hle : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXiTwistFilter h eps H), g ξ
        ≤ ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXiTwistFilter h eps H),
            ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) * (‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖) := by
      refine Finset.sum_le_sum (fun ξ hξ => ?_)
      rw [Finset.mem_filter] at hξ
      have hlt : ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
          < (eps : ℝ) ^ 2 / Real.log (H : ℝ) :=
        not_le.mp (fun h => hξ.2 (mem_bigXiTwistFilter.mpr h))
      rw [hg]; simp only
      calc ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖ *
            ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
          ≤ ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖ * ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) := by
            gcongr
        _ = (eps : ℝ) ^ 2 / Real.log (H : ℝ) * (‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖) := by ring
    refine hle.trans ?_
    rw [← Finset.mul_sum]
    have hl1 : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXiTwistFilter h eps H),
        (‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖)
          ≤ ∑ ξ : ZMod H, ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun ξ _ _ => by positivity)
    have hl2 := dft_l1_reflect Φ Φ h1 h1
    calc (eps : ℝ) ^ 2 / Real.log (H : ℝ) *
          ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ bigXiTwistFilter h eps H),
            (‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (-ξ)‖)
        ≤ (eps : ℝ) ^ 2 / Real.log (H : ℝ) * (H : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (hl1.trans hl2) (div_nonneg (by positivity) hlog.le)
      _ = (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ) := by ring
  linarith [hmajor, hminor]

/-- **The circle-method estimate at offset `p·h`** — the `h`-family core of Tao's Lemma 3.4
(1509.05422 (3.18)), stated over the twisted large-spectrum set `bigXiTwistFilter h`.

Everything is as in `circle_method_estimate` except the offset (`p ↦ p·h`) and the
frequency set: the periodization's per-prime wraparound is now `p·h` places, so the total
wrap error is `h·|𝒫_H|` rather than `|𝒫_H|`, and the output constant is
`C = h·(1 + 2·C₀)` — the wrap multiplies the PERIODIZATION coefficient `C₀`, so the two
binding constraints are `C ≥ 1 + h·C₀` (the `ε²` arm) and `C ≥ 2·C₀` (the Fourier arm),
both met by `h·(1 + 2·C₀)` for `h ≥ 1` and by no constant of the form `h + 2·C₀`.

`0 < h` is consumed twice and is not cosmetic: it makes the constant positive, and at
`H = 1` it supplies `1 ≤ p·h`, without which the window correlation does not vanish and
the statement is FALSE rather than merely unproven. -/
theorem circle_method_estimate_h_core (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 x2 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) → (∀ i, |x2 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) *
          ∑ j ∈ Finset.range H,
            (windowVal H x1 j : ℝ) * (windowVal H x2 (j + (p : ℕ) * h) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ)) *
            ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiTwistFilter h eps H, (1 / (H : ℝ)) *
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖) := by
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  refine ⟨(h : ℝ) * (1 + 2 * C₀), mul_pos hhR (by positivity), ?_⟩
  intro eps H _ x1 x2 hx1 hx2 hcard
  by_cases hH2 : 2 ≤ H
  · -- main regime: H ≥ 2, so log H > 0
    have hH1r : (1 : ℝ) < (H : ℝ) := by exact_mod_cast hH2
    have hlog : 0 < Real.log (H : ℝ) := Real.log_pos hH1r
    have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
    set Φ₁ : ZMod H → ℂ := fun m => ((windowVal H x1 m.val : ℤ) : ℂ) with hΦ₁
    set Φ₂ : ZMod H → ℂ := fun m => ((windowVal H x2 m.val : ℤ) : ℂ) with hΦ₂
    have h1 : ∀ j, ‖Φ₁ j‖ ≤ 1 := fun j => windowVal_c_norm_le hx1 j
    have h2 : ∀ j, ‖Φ₂ j‖ ≤ 1 := fun j => windowVal_c_norm_le hx2 j
    set S : ℝ := ∑ ξ ∈ bigXiTwistFilter h eps H, ‖ZMod.dft Φ₁ ξ‖ with hS
    set L : ℝ := ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
        ∑ j ∈ Finset.range H,
          (windowVal H x1 j : ℝ) * (windowVal H x2 (j + (p : ℕ) * h) : ℝ) with hL
    set T : ℂ := ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ∑ m : ZMod H, Φ₁ m * Φ₂ (m + (((p : ℕ) * h : ℕ) : ZMod H)) with hT
    set W : ℂ := ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ) *
        expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ)) with hW
    -- collapse and split, at the twisted frequency
    have hWT : (H : ℂ) * T = W := T_collapse_h h Φ₁ Φ₂
    have hTnorm : (H : ℝ) * ‖T‖ = ‖W‖ := by
      rw [← hWT, norm_mul, Complex.norm_natCast]
    have hnormW : ‖W‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
        + (2 * C₀ * (H : ℝ) / Real.log (H : ℝ)) * S :=
      fourier_split_h h Φ₁ Φ₂ h1 h2 hC₀ hlog hcard
    -- cast L and periodize (the wrap is now `p·h` places per prime)
    have hLcast : ((L : ℝ) : ℂ) = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
          (windowVal H x2 (j + (p : ℕ) * h) : ℝ) : ℝ) : ℂ) := by
      rw [hL, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      push_cast
      ring
    have hdiff : ((L : ℝ) : ℂ) - T = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        (((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
            (windowVal H x2 (j + (p : ℕ) * h) : ℝ) : ℝ) : ℂ)
          - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
              ((windowVal H x2 (m + (((p : ℕ) * h : ℕ) : ZMod H)).val : ℤ) : ℂ)) := by
      rw [hLcast, hT, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun p _ => by rw [mul_sub])
    have hperiod : ‖((L : ℝ) : ℂ) - T‖ ≤ (h : ℝ) * ((primeWindow eps H).card : ℝ) := by
      rw [hdiff]; exact periodization_total_h h hx1 hx2
    -- assemble
    have hLT : |L| ≤ ‖T‖ + (h : ℝ) * ((primeWindow eps H).card : ℝ) := by
      have hna := norm_add_le T (((L : ℝ) : ℂ) - T)
      rw [add_sub_cancel] at hna
      calc |L| = ‖((L : ℝ) : ℂ)‖ := (Complex.norm_real L).symm
        _ ≤ ‖T‖ + ‖((L : ℝ) : ℂ) - T‖ := hna
        _ ≤ ‖T‖ + (h : ℝ) * ((primeWindow eps H).card : ℝ) := by linarith [hperiod]
    have hH0 : (H : ℝ) ≠ 0 := ne_of_gt hHpos
    have hLe0 : Real.log (H : ℝ) ≠ 0 := ne_of_gt hlog
    have hTle : ‖T‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
        + 2 * C₀ / Real.log (H : ℝ) * S := by
      have hHTle : (H : ℝ) * ‖T‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
          + (2 * C₀ * (H : ℝ) / Real.log (H : ℝ)) * S := hTnorm ▸ hnormW
      have key : (H : ℝ) * ‖T‖ ≤ (H : ℝ) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
          + 2 * C₀ / Real.log (H : ℝ) * S) := by
        refine hHTle.trans (le_of_eq ?_)
        ring
      exact le_of_mul_le_mul_left key hHpos
    rw [← Finset.mul_sum, ← hS]
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun ξ _ => norm_nonneg _)
    have hA_nn : 0 ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) := by positivity
    have hB_nn : 0 ≤ S / Real.log (H : ℝ) := div_nonneg hS_nn hlog.le
    have hc1 : 0 ≤ (h : ℝ) - 1 + (h : ℝ) * C₀ := by nlinarith [mul_pos hhR hC₀]
    have hc2 : 0 ≤ (h : ℝ) + 2 * C₀ * ((h : ℝ) - 1) := by
      nlinarith [mul_nonneg hC₀.le (by linarith : (0 : ℝ) ≤ (h : ℝ) - 1)]
    have hrem_nn : 0 ≤ ((h : ℝ) - 1 + (h : ℝ) * C₀)
          * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
        + ((h : ℝ) + 2 * C₀ * ((h : ℝ) - 1)) * (S / Real.log (H : ℝ)) :=
      add_nonneg (mul_nonneg hc1 hA_nn) (mul_nonneg hc2 hB_nn)
    have heq : (h : ℝ) * (1 + 2 * C₀) * ((H : ℝ) / Real.log (H : ℝ))
          * ((eps : ℝ) ^ 2 + 1 / (H : ℝ) * S)
        = ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) + 2 * C₀ / Real.log (H : ℝ) * S)
          + (h : ℝ) * (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
          + (((h : ℝ) - 1 + (h : ℝ) * C₀)
                * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
              + ((h : ℝ) + 2 * C₀ * ((h : ℝ) - 1)) * (S / Real.log (H : ℝ))) := by
      field_simp
      ring
    have hhcard : (h : ℝ) * ((primeWindow eps H).card : ℝ)
        ≤ (h : ℝ) * (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))) :=
      mul_le_mul_of_nonneg_left hcard hhR.le
    calc |L| ≤ ‖T‖ + (h : ℝ) * ((primeWindow eps H).card : ℝ) := hLT
      _ ≤ (h : ℝ) * (1 + 2 * C₀) * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + 1 / (H : ℝ) * S) := by
          rw [heq]; linarith [hTle, hhcard, hrem_nn]
  · -- degenerate: H = 1, where `0 < h` is what makes the correlation vanish
    have hH1 : H = 1 := by have := NeZero.pos H; omega
    have hlog0 : Real.log (H : ℝ) = 0 := by rw [hH1]; simp
    have hL0 : (∑ p : primeWindow eps H, (1 / (p : ℝ)) *
        ∑ j ∈ Finset.range H,
          (windowVal H x1 j : ℝ) * (windowVal H x2 (j + (p : ℕ) * h) : ℝ)) = 0 := by
      refine Finset.sum_eq_zero (fun p _ => ?_)
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      have hph : 0 < (p : ℕ) * h := Nat.mul_pos (prime_of_mem_primeWindow p.2).pos hh
      have hge : ¬ (j + (p : ℕ) * h < H) := by omega
      have hz : windowVal H x2 (j + (p : ℕ) * h) = 0 := by rw [windowVal, dif_neg hge]
      rw [hz]; simp
    rw [hL0, abs_zero]
    have hmid : (H : ℝ) / Real.log (H : ℝ) = 0 := by rw [hlog0, div_zero]
    rw [hmid]; simp

end Salt.Entropy.Chowla
