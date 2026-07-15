/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Defs
import Salt.SW.Kernel

/-!
# The SW rung, wave S1b — the composite ψ₁ Perron identity

Design: `docs/blueprints/sw.md`, wave S1 (the de-risked keystone).  This module
assembles the landed *kernel* pieces (`Salt/SW/Kernel.lean`) with the Dirichlet
`L'/L` machinery (`Salt/SW/Defs.lean`) into the smoothed Perron identity for the
character Riesz mean:
```
ψ₁(x, χ) = x · (1/2π) ∫_ℝ  x^{s}/(s(s+1)) · (−L'/L)(s, χ) dt,   s = c + it,  c > 1.
```

## Route (worked, matching the blueprint's four steps)

1. **Per term** (`kern`-identity): for `n ≤ ⌊x⌋₊` we have `x/n ≥ 1` so
   `(1/2π) ∫ (x/n)^s/(s(s+1)) = 1 − n/x`, whence `x·Λχ(n)·(1 − n/x) = Λχ(n)·(x−n)`;
   for `n > ⌊x⌋₊` we have `x/n < 1` so the kernel value is `0` and the term drops.
   The `n = 0` term is killed by `(x/0)^s = 0^s = 0`.  This lets the *finite* `Icc`
   sum be rewritten as a `tsum` over all `n` (`tsum_eq_sum`, tail vanishing).
2. **Swap** (`kernel_sum_swap`): the domination hypothesis
   `Summable (‖Λχ(n)‖·(x/n)^c)` is `riesz_summable_dom` — proved *directly* from
   `DirichletCharacter.LSeriesSummable_twist_vonMangoldt` (no manual log-damping).
3. **Dirichlet series** (`riesz_tsum_eq`): `∑ₙ f(n)(x/n)^s = x^s · L(f, s)` via the
   real-quotient cpow split `(x/n)^s = x^s/n^s` (`ofReal_div_cpow_eq`).
4. **Assemble**: `x · x^s = x^{s+1}` bookkeeping is folded into the packaging.

## Main results

* `psi1_eq_integral` — the composite identity with the `L(↗χ·↗Λ)` factor (the
  form S1's swap produces).
* `psi1_eq_integral_logDeriv` — the same with the `−L'/L` factor S5 consumes.
  The `L(↗χ, s) ≠ 0` needed to divide is *unconditional* on the line `Re s = c > 1`
  (`DirichletCharacter.LSeries_ne_zero_of_one_lt_re`), so no extra hypothesis.

All axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no
new axioms, no `sorry`.
-/

open MeasureTheory Complex Set ArithmeticFunction
open scoped LSeries.notation

noncomputable section
namespace Salt.SW

/-! ## Algebraic helpers -/

/-- **Real-quotient cpow split.**  For `x ≥ 0` and `n ≥ 1`,
`((x/n : ℝ) : ℂ)^s = (x:ℂ)^s / (n:ℂ)^s`.  (`x/n = x·n⁻¹`; `mul_cpow_ofReal_nonneg`
splits the product and `inv_cpow` handles the positive-real `n⁻¹`.) -/
lemma ofReal_div_cpow_eq {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    ((x / n : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (n : ℂ) ^ s := by
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact (Real.pi_pos).ne
  rw [show (x / (n : ℝ) : ℝ) = x * (n : ℝ)⁻¹ by ring, Complex.ofReal_mul,
    mul_cpow_ofReal_nonneg hx (by positivity), Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.inv_cpow _ _ harg, div_eq_mul_inv]

/-- **Constant pull-out.**  A scalar coefficient factors out of the kernel integral. -/
lemma integral_term_eq {x c : ℝ} {n : ℕ} (w : ℂ) :
    (∫ t : ℝ, w * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))
      = w * ∫ t : ℝ, ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  rw [mul_div_assoc]

/-! ## The Dirichlet-series form of the summed kernel numerator -/

/-- **The Dirichlet series appears.**  For `s ≠ 0` and `x ≥ 0`,
`∑ₙ f(n)·(x/n)^s = x^s · L(f, s)`.  The `n = 0` term vanishes on both sides
(`(x/0)^s = 0^s = 0`); for `n ≥ 1` this is the cpow split of `ofReal_div_cpow_eq`. -/
lemma riesz_tsum_eq (f : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x) {s : ℂ} (hs : s ≠ 0) :
    ∑' n : ℕ, f n * ((x / n : ℝ) : ℂ) ^ s = (x : ℂ) ^ s * LSeries f s := by
  rw [LSeries, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Complex.zero_cpow hs]
  · rw [LSeries.term_of_ne_zero hn, ofReal_div_cpow_eq hx hn s]; ring

/-! ## The domination hypothesis for the sum ↔ integral swap -/

/-- **Domination.**  For `c > 1`, `∑ₙ ‖Λχ(n)‖·(x/n)^c < ∞`.  Reduced to the twist
`L`-summability `DirichletCharacter.LSeriesSummable_twist_vonMangoldt`: term by term
`‖Λχ(n)‖·(x/n)^c = x^c·‖LSeries.term (↗χ·↗Λ) c n‖`, and the twist `L`-series
converges absolutely at `Re s = c > 1`. -/
lemma riesz_summable_dom {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 ≤ x)
    {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ => ‖(↗χ * ↗vonMangoldt) n‖ * (x / n) ^ c) := by
  have hcre : 1 < ((c : ℂ)).re := by simpa using hc
  have hLS : LSeriesSummable (↗χ * ↗vonMangoldt) (c : ℂ) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hcre
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term (↗χ * ↗vonMangoldt) (c : ℂ) n‖) :=
    summable_norm_iff.mpr hLS
  have hEq : (fun n : ℕ => ‖(↗χ * ↗vonMangoldt) n‖ * (x / n) ^ c)
      = fun n : ℕ => x ^ c * ‖LSeries.term (↗χ * ↗vonMangoldt) (c : ℂ) n‖ := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re,
        Real.div_rpow hx (Nat.cast_nonneg n)]
      ring
  rw [hEq]
  exact hnorm.mul_left (x ^ c)

/-! ## The composite identity -/

/-- **The composite ψ₁ Perron identity** (S1b deliverable, `L(↗χ·↗Λ)` form).
For `x ≥ 1` and `c > 1`,
`ψ₁(x, χ) = x · (1/2π) ∫_ℝ  x^{c+it}/((c+it)(c+it+1)) · L(↗χ·↗Λ)(c+it) dt`. -/
theorem psi1_eq_integral {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x)
    {c : ℝ} (hc : 1 < c) :
    psi1Chi x χ
      = (x : ℂ) * ((1 / (2 * Real.pi)) • ∫ t : ℝ,
          ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
              (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))
            * LSeries (↗χ * ↗vonMangoldt) ((c : ℂ) + (t : ℂ) * I)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hc0 : (0 : ℝ) < c := lt_trans one_pos hc
  have hsum := riesz_summable_dom χ hx0.le hc
  -- Rewrite the vertical integral as the tsum of per-term kernel integrals.
  have hInt : (∫ t : ℝ,
        ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
            (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))
          * LSeries (↗χ * ↗vonMangoldt) ((c : ℂ) + (t : ℂ) * I))
      = ∑' n : ℕ, ∫ t : ℝ, (↗χ * ↗vonMangoldt) n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
    rw [kernel_sum_swap (↗χ * ↗vonMangoldt) hx0 hc0 hsum]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    dsimp only
    rw [riesz_tsum_eq (↗χ * ↗vonMangoldt) hx0.le (s_ne_zero hc0 t)]
    ring
  -- The tail terms of the tsum vanish, so it collapses to the `Icc` sum.
  have htail : ∀ n ∉ Finset.Icc 1 ⌊x⌋₊,
      (∫ t : ℝ, (↗χ * ↗vonMangoldt) n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))) = 0 := by
    intro n hn
    rw [integral_term_eq ((↗χ * ↗vonMangoldt) n)]
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with h | h
    · have hn0 : n = 0 := Nat.lt_one_iff.mp h
      subst hn0
      rw [show (↗χ * ↗vonMangoldt : ℕ → ℂ) 0 = 0 by simp, zero_mul]
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
  rw [hInt, tsum_eq_sum htail, Finset.smul_sum, Finset.mul_sum]
  simp only [psi1Chi]
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
  rw [integral_term_eq ((↗χ * ↗vonMangoldt) n), ← mul_smul_comm, hker]
  simp only [Pi.mul_apply]
  push_cast
  field_simp

/-! ## The `−L'/L` restatement (S5 interface) -/

/-- **The composite identity, `−L'/L` form** (what S5's contour shift consumes).
Identical to `psi1_eq_integral` with the integrand's `L(↗χ·↗Λ)` factor replaced by
`−L'/L(·, χ)`.  On the line `Re s = c > 1` the Dirichlet `L`-function is
nonvanishing (`DirichletCharacter.LSeries_ne_zero_of_one_lt_re`), so the quotient
`−L'/L = L(↗χ·↗Λ)` (the S0 re-export) needs no side hypothesis. -/
theorem psi1_eq_integral_logDeriv {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x)
    {c : ℝ} (hc : 1 < c) :
    psi1Chi x χ
      = (x : ℂ) * ((1 / (2 * Real.pi)) • ∫ t : ℝ,
          ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
              (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))
            * (-deriv (LSeries ↗χ) ((c : ℂ) + (t : ℂ) * I)
                / LSeries ↗χ ((c : ℂ) + (t : ℂ) * I))) := by
  rw [psi1_eq_integral χ hx hc]
  refine congrArg (fun z : ℂ => (x : ℂ) * ((1 / (2 * Real.pi)) • z)) ?_
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  have hre : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
  have hs : 1 < ((c : ℂ) + (t : ℂ) * I).re := by rw [hre]; exact hc
  rw [neg_logDeriv_LSeries_eq_LSeries_twist χ hs]

end Salt.SW

end
