/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.ZetaInvShallow
import Salt.SW.Psi1Identity
import Salt.SW.ContourShift
import Salt.SW.ShiftAssembly
import Salt.TwinBar.LambdaRate

/-!
# The effective Möbius summatory rate `MmuRate` (trophy T-Mμ)

Design: `docs/exploration/s2-trackA-design.md` (AMENDMENT 1+2). This module lands the
`1/ζ` smoothed-Perron contour route to the frozen Prop
`Salt.TwinBar.MmuRate` (`Salt/TwinBar/LambdaRate.lean`):
`∀ A > 0, ∃ C x₀, ∀ y ≥ x₀, |M_μ(y)| ≤ C·y/(log y)^A`, where `M_μ(y) = ∑_{n ≤ y} μ(n)`.
On this landing `parity_wall` (`Salt/TwinBar/Wall.lean`) goes UNCONDITIONAL.

## Route (frozen; the mathematics overrides the sketch, a route change is STOP-AND-FLAG)

The smoothed Riesz mean `M₁_μ(x) = ∑_{n ≤ x} μ(n)·(1 − n/x)` has the reusable smoothed
Mellin/Perron kernel `y^s/(s(s+1))` (`Salt.SW.kernel_identity`), so — feeding the coefficient
sequence `↗μ` into the arithmetic-agnostic swap `Salt.SW.kernel_sum_swap` and the Dirichlet
entry point `Salt.SW.riesz_tsum_eq` — for `c > 1`:
```
M₁_μ(x) = (1/2π) ∫_ℝ  x^{c+it}/((c+it)(c+it+1)) · (ζ(c+it))⁻¹ dt.    (mmu1_eq_integral)
```
mathlib gives `∑ μ(n) n^{-s} = 1/ζ(s)` only in product form
(`LSeries_one_mul_Lseries_moebius` + `LSeries_one_eq_riemannZeta`
+ `riemannZeta_ne_zero_of_one_lt_re`); `LSeries_moebius_eq_zeta_inv` packages it.

The contour is then shifted from `Re s = c` onto the shallow line `σ₀ = 1 − c₄/log⁹(T+2)`.
Because `ζ`'s pole makes `1/ζ`'s singularity at `s = 1` REMOVABLE, `1/ζ` is analytic on the whole
shallow box, so the rectangle boundary integral vanishes (`rectBI_eq_zero_of_differentiableOn`,
`rectBI_right_split`) with NO residue term — the route's whole point. The three surviving edges
(two horizontals `Im = ±T`, the shallow vertical `Re = σ₀`) plus the truncation tail (`|t| > T`)
are each bounded via `zeta_inv_shallow` (`‖1/ζ‖ ≤ C·log⁷(|t|+2)` on the whole half-plane
`σ ≥ 1 − c₄/log⁹(|t|+2)`, `s ≠ 1`, which covers the `c`-line, the shallow line and the
horizontals uniformly). De-smoothing `M₁_μ → M_μ` is via short-interval averaging using the cheap
`|M_μ(y+h) − M_μ(y)| ≤ h` (`|μ| ≤ 1`; no monotonicity dance, unlike ψ).

## III.3″ numeric sanity witness (mpmath / symbolic)

At `x = 10⁶`, `|M_μ(x)| ≈ 212` (known). `log(10⁶) = 13.8155`, so
* `A = 2`: `x/log²x = 5.24e3`, so `C ≥ 212/5239 ≈ 0.0405` suffices;
* `A = 5`: `x/log⁵x = 1.99`, so `C ≥ 212/1.99 ≈ 106.5` — the constant is large because the
  asymptotic saving has not yet dominated at `x = 10⁶` (the branch-max `C` is expected).

Budget arithmetic (symbolic) at `log x = 100`: `(log x)^{1/10} = 100^{0.1} = 1.585`; the shallow
shift saving is `x^{σ₀−1} = exp(−c₄·log x/log⁹(T+2)) = exp(−c₄·(log x)^{1/10})` with
`log T = (log x)^{1/10}`. For any fixed `A`, `exp(−c₄·u^{1/10}) = o(u^{−A})` as `u = log x → ∞`
(a power of `log x` in the exponent beats every fixed log-power), with crossover at
`c₄·(log x)^{1/10} ≥ A·log log x` — a finite (astronomically large) threshold `x₀` that the
existential in `MmuRate` absorbs. Likewise the horizontal edges
`~ x·(log x)^{−3/10}·exp(−2u^{1/10})` and the tail `~ x·(log x)^{7/10}·exp(−u^{1/10})`
beat every `x/log^A x`.

## Case space (enumerated; a NEW case = STOP AND FLAG, per III.3‴)

vertical shallow segment × the two horizontal edges × the right anchor `Re = c = 1 + 1/log x`
× the truncation tail (`n` far from `x`; divisor-free since `|μ| ≤ 1`) × the near-diagonal `n ≈ x`
band (kernel-smoothing) × small-`y` (absorbed by `x₀`) × `s = 1` (removable; `zeta_inv_shallow`'s
`s ≠ 1` is supplied pointwise off the real axis / routed around via `Zc`).

All results are axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no new
axioms.
-/

open MeasureTheory Complex Set ArithmeticFunction
open scoped LSeries.notation ArithmeticFunction.Moebius

noncomputable section
namespace Salt.SW

/-! ## The Dirichlet series `∑ μ(n) n^{-s} = 1/ζ(s)` -/

/-- **`∑ μ(n) n^{-s} = 1/ζ(s)` for `Re s > 1`.** mathlib packages this only in product form
(`LSeries_one_mul_Lseries_moebius : L 1 s · L ↗μ s = 1`); combined with
`LSeries_one_eq_riemannZeta` this gives the inverse form. -/
lemma LSeries_moebius_eq_zeta_inv {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗μ s = (riemannZeta s)⁻¹ := by
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have h1 : riemannZeta s * LSeries ↗μ s = 1 := by
    rw [← LSeries_one_eq_riemannZeta hs]; exact LSeries_one_mul_Lseries_moebius hs
  field_simp
  linear_combination h1

/-! ## The domination hypothesis for the sum ↔ integral swap -/

/-- **Domination.** For `c > 1`, `∑ₙ ‖μ(n)‖·(x/n)^c < ∞`. Reduced to
`ArithmeticFunction.LSeriesSummable_moebius_iff` (the Möbius `L`-series converges absolutely at
`Re s = c > 1`), mirroring `Salt.SW.riesz_summable_dom`. -/
lemma mmu_summable_dom {x : ℝ} (hx : 0 ≤ x) {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ => ‖(↗μ : ℕ → ℂ) n‖ * (x / n) ^ c) := by
  have hcre : 1 < ((c : ℂ)).re := by simpa using hc
  have hLS : LSeriesSummable ↗μ (c : ℂ) := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hcre
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term ↗μ (c : ℂ) n‖) := summable_norm_iff.mpr hLS
  have hEq : (fun n : ℕ => ‖(↗μ : ℕ → ℂ) n‖ * (x / n) ^ c)
      = fun n : ℕ => x ^ c * ‖LSeries.term ↗μ (c : ℂ) n‖ := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re,
        Real.div_rpow hx (Nat.cast_nonneg n)]
      ring
  rw [hEq]
  exact hnorm.mul_left (x ^ c)

/-! ## The smoothed Riesz mean and its Perron representation -/

/-- The smoothed Möbius Riesz mean `M₁_μ(x) = ∑_{n ≤ x} μ(n)·(1 − n/x)` (ℂ-valued). Continuous
profile `(1 − ·)₊`; the finite `Icc 1 ⌊x⌋₊` support because the kernel value drops for `n > x`. -/
def Mmu1 (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℂ) * (1 - (n : ℂ) / (x : ℂ))

/-- **The smoothed Möbius Perron identity, `L(↗μ)` form.** For `x ≥ 1`, `c > 1`,
`M₁_μ(x) = (1/2π) ∫_ℝ x^{c+it}/((c+it)(c+it+1)) · L(↗μ)(c+it) dt`. Mirrors
`Salt.SW.psi1_eq_integral` with coefficient `↗μ` and no leading `x·` factor (the `μ` Riesz
mean is `∑ μ(n)(1−n/x)`, not `x·∑`). -/
theorem mmu1_eq_integral_LSeries {x : ℝ} (hx : 1 ≤ x) {c : ℝ} (hc : 1 < c) :
    Mmu1 x = (1 / (2 * Real.pi)) • ∫ t : ℝ,
        ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
            (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))
          * LSeries ↗μ ((c : ℂ) + (t : ℂ) * I) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hc0 : (0 : ℝ) < c := lt_trans one_pos hc
  have hsum := mmu_summable_dom hx0.le hc
  -- Rewrite the vertical integral as the tsum of per-term kernel integrals.
  have hInt : (∫ t : ℝ,
        ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
            (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))
          * LSeries ↗μ ((c : ℂ) + (t : ℂ) * I))
      = ∑' n : ℕ, ∫ t : ℝ, (↗μ : ℕ → ℂ) n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
    rw [kernel_sum_swap (↗μ : ℕ → ℂ) hx0 hc0 hsum]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    dsimp only
    rw [riesz_tsum_eq (↗μ : ℕ → ℂ) hx0.le (s_ne_zero hc0 t)]
    ring
  -- The tail terms of the tsum vanish, so it collapses to the `Icc` sum.
  have htail : ∀ n ∉ Finset.Icc 1 ⌊x⌋₊,
      (∫ t : ℝ, (↗μ : ℕ → ℂ) n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))) = 0 := by
    intro n hn
    rw [integral_term_eq ((↗μ : ℕ → ℂ) n)]
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with h | h
    · have hn0 : n = 0 := Nat.lt_one_iff.mp h
      subst hn0
      rw [show (↗μ : ℕ → ℂ) 0 = 0 by simp, zero_mul]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (by omega : n ≠ 0)
      have hypos : (0 : ℝ) < x / n := div_pos hx0 hnR
      have hylt : x / n < 1 := by
        rw [div_lt_one hnR]
        have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
        have h2 : ((⌊x⌋₊ : ℝ) + 1) ≤ n := by exact_mod_cast Nat.succ_le_of_lt h
        linarith
      have hker := kernel_identity hypos hc0
      rw [if_neg (not_le.mpr hylt), Complex.real_smul] at hker
      have hJ0 := (mul_eq_zero.mp hker).resolve_left (by
        simp only [Complex.ofReal_eq_zero]
        exact (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)).ne')
      rw [hJ0, mul_zero]
  rw [hInt, tsum_eq_sum htail, Finset.smul_sum]
  simp only [Mmu1]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_Icc] at hn
  obtain ⟨hn1, hn2⟩ := hn
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hxn : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hn2) (Nat.floor_le hx0.le)
  have hypos : (0 : ℝ) < x / n := div_pos hx0 hnR
  have hyge : 1 ≤ x / n := by rw [le_div_iff₀ hnR]; linarith
  have hker := kernel_identity hypos hc0
  rw [if_pos hyge] at hker
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  rw [integral_term_eq ((↗μ : ℕ → ℂ) n), ← mul_smul_comm, hker]
  push_cast
  field_simp

/-- **The smoothed Möbius Perron identity, `1/ζ` form** (the contour-shift consumable). For
`x ≥ 1`, `c > 1`,
`M₁_μ(x) = (1/2π) ∫_ℝ x^{c+it}/((c+it)(c+it+1)) · (ζ(c+it))⁻¹ dt`. -/
theorem mmu1_eq_integral {x : ℝ} (hx : 1 ≤ x) {c : ℝ} (hc : 1 < c) :
    Mmu1 x = (1 / (2 * Real.pi)) • ∫ t : ℝ,
        ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
            (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))
          * (riemannZeta ((c : ℂ) + (t : ℂ) * I))⁻¹ := by
  rw [mmu1_eq_integral_LSeries hx hc]
  refine congrArg (fun z : ℂ => (1 / (2 * Real.pi)) • z) ?_
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  have hre : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
  have hs : 1 < ((c : ℂ) + (t : ℂ) * I).re := by rw [hre]; exact hc
  rw [LSeries_moebius_eq_zeta_inv hs]

/-! ## The residue-free contour shift (the route's whole point)

`1/ζ` extends analytically through the pole `s = 1` (where `ζ`'s pole makes the singularity
removable, value `0`): the corpus's `Zc = (s−1)ζ` is entire with `Zc 1 = 1 ≠ 0`, so
`mmuG s = (s−1)/Zc s` is analytic wherever `Zc s ≠ 0` and agrees with `(ζ s)⁻¹` off `s = 1`.
Hence the shifted rectangle boundary integral VANISHES — no residue term — which is exactly what
distinguishes the `M_μ` contour from the `ψ` contour (`psi1_contour_shift_trivchar`, which must
subtract the `x²/2` pole residue). -/

/-- The analytic extension of `1/ζ` through the pole `s = 1`: `mmuG s = (s−1)/Zc s`, with
`Zc = (s−1)ζ` entire (`Zc_differentiable`) and `Zc 1 = 1`. -/
def mmuG (s : ℂ) : ℂ := (s - 1) / Zc s

/-- Off `s = 1` and where `ζ ≠ 0`, the extension equals the genuine inverse `(ζ s)⁻¹`. -/
lemma mmuG_eq_zeta_inv {s : ℂ} (hs1 : s ≠ 1) (_hζ : riemannZeta s ≠ 0) :
    mmuG s = (riemannZeta s)⁻¹ := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [mmuG, Zc_eq_of_ne hs1, div_mul_eq_div_div, div_self h1, one_div]

/-- `mmuG` is differentiable wherever `Zc ≠ 0` (in particular through the removable point `s = 1`,
since `Zc 1 = 1 ≠ 0`). -/
lemma mmuG_differentiableAt {s : ℂ} (hZc : Zc s ≠ 0) : DifferentiableAt ℂ mmuG s :=
  (differentiableAt_id.sub_const 1).div (Zc_differentiable s) hZc

/-- **The residue-free contour-shift vanishing.** For `x > 0` and a rectangle strictly to the right
of the imaginary axis (`0 < z.re`) whose closed interior contains no zero of `ζ`, the boundary
integral of the `M_μ` Perron integrand `x^s/(s(s+1)) · mmuG s` vanishes. Combined with
`Salt.SW.rectBI_right_split` this moves the `Re s = c` line integral onto the shallow left edge and
the two horizontals with NO residue correction — the whole point of the `1/ζ` route. -/
theorem mmu_rectBI_eq_zero {z w : ℂ} {x : ℝ} (hx : 0 < x) (hz0 : 0 < z.re)
    (hzw_re : z.re ≤ w.re)
    (hzf : ∀ ρ : ℂ, riemannZeta ρ = 0 → z.re ≤ ρ.re → ρ.re ≤ w.re →
      ρ.im ∈ Set.uIcc z.im w.im → False) :
    rectBI z w (fun s => (x : ℂ) ^ s / (s * (s + 1)) * mmuG s) = 0 := by
  apply rectBI_eq_zero_of_differentiableOn
  intro s hs
  rw [closedRect, mem_reProdIm] at hs
  have hsre_mem : s.re ∈ Set.Icc z.re w.re := by rw [← Set.uIcc_of_le hzw_re]; exact hs.1
  have hsre : 0 < s.re := lt_of_lt_of_le hz0 hsre_mem.1
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have : (s + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at this; linarith
  have hZc : Zc s ≠ 0 := by
    by_cases he : s = 1
    · rw [he, Zc_one]; exact one_ne_zero
    · rw [Zc_eq_of_ne he]
      exact mul_ne_zero (sub_ne_zero.mpr he) (fun hζ => hzf s hζ hsre_mem.1 hsre_mem.2 hs.2)
  have hd : DifferentiableAt ℂ (fun s => (x : ℂ) ^ s / (s * (s + 1)) * mmuG s) s := by
    apply DifferentiableAt.mul
    · apply DifferentiableAt.div
      · exact differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
      · exact differentiableAt_id.mul (differentiableAt_id.add_const 1)
      · exact mul_ne_zero hs0 hs1
    · exact mmuG_differentiableAt hZc
  exact hd.differentiableWithinAt

end Salt.SW

end
