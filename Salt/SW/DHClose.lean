/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.DHBalance

/-!
# The Deuring–Heilbronn close: the finite-truncation balance (HB-ENGINE, WP2, node DH-2b-v)

Design: `docs/exploration/s3-hb3-design.md`, "DH-2b — THE PRODUCT-DETECTOR FREEZE".
Source: Benlİ–Goel–Twiss–Zaman, arXiv:2410.06082, §§4–5.

This module supplies the **finite-N truncation** balance that the predecessor
(`DHBalance`, DH-2b-iv) named as the resume route after proving the naive vertical
integral non-integrable. The predecessors landed the full assembly:

* `DHRepulsion.dhDetector_floor` — the positivity floor `(1-1/x)₊ ≤ D(x,N)` (M2);
* `DHRepulsion.dhDetector_mellin` — the exact FINITE Mellin representation (summability-free);
* `DHContour.rectBI_zeta_LFunction_kernel` — the `L(1,χ)·x²/2` residue at the ζ-pole;
* `StripConvergence.norm_LFunction_sub_partial_le_strip` — the strip tail
  `‖L − Σ_{n≤N}‖ ≤ 3M(1+‖s‖/Re s)N^{−Re s}` (M = √q(1+log q) via Pólya–Vinogradov);
* `DHBalance.dh_repulsion_of_LFunction_one_lower` — the UNCONDITIONAL M4 inversion:
  any `Λ ≤ (L(1,χ)).re` yields `Λ/(25e(1+log q)²) ≤ 1−β`.

## What lands here (all sorry-free, axioms ⊆ [propext, Classical.choice, Quot.sound])

* **`dhDetector_floor_explicit`** — the floor in closed form `1 − 1/x ≤ D(x,N)` for `x > 1`
  (the competing LOWER estimate of the balance, `(1−1/x)₊ = 1−1/x`).
* **`LFunction_one_re_ge_partial`** — the **truncation-route `L(1,χ)` lower bound**, the honest
  M-A stone: applying the strip tail at `s = 1` to the UNMOLLIFIED `L(1,χ)` gives, for a
  primitive real `χ` mod `q ≥ 2` and any `N ≥ 1`,

    `Σ_{n≤N} χ_ℝ(n)/n  −  6·√q·(1+log q)/N  ≤  (L(1,χ)).re`.

  The partial character sum `Σ_{n≤N} χ_ℝ(n)/n` is the "main term", `6√q(1+log q)/N` the
  strip-truncation error. This is the finite balance in its cleanest (unmollified) form,
  delivered UNCONDITIONALLY (no contour, no subconvexity).
* **`dh_repulsion_partial`** — the M-C composition: feeding the truncation lower bound through
  M4 gives the reversed-Jutila repulsion inequality with the explicit partial-sum main term,

    `(Σ_{n≤N} χ_ℝ(n)/n − 6√q(1+log q)/N) / (25e(1+log q)²)  ≤  1 − β`,

  UNCONDITIONAL. Meaningful (a genuine repulsion) exactly once the main term is shown to
  exceed the error — which is what the mollifier is FOR (see the residual below).

## The single remaining residual (precisely named, PROSE not `sorry`)

The unmollified main term `Σ_{n≤N} χ_ℝ(n)/n` is NOT yet shown to reach the ρ-dependent
repulsion shape `c·(q(|γ|+2))^{−b(1−ρ.re)}/polylog` that the `dh_repulsion` target demands.
That shape is intrinsically a property of the **mollified detector's ρ-shift**: the residue
of `F(s+ρ)G(s+ρ)` at `s = 1−ρ` carries `x^{2−ρ}`, i.e. the `x^{−b(1−ρ.re)}` gain, and the
Graham/Barban–Vehov weights `G` are what cancel the `Σ χ_ℝ(n)/n` error down to `≍ 1/log z`
(the sharp `GrahamWeights` residual (2), still unbuilt). Concretely the residual is:

> **DH-MAIN.** For the mollified coefficient `dhCoeff = dhA·(Σ_{d∣n}θ_d)²`, the shifted sum
> `Σ_{n≤N} dhCoeff(n) n^{−ρ}(1−n/x)₊` has main term `≍ L(1,χ)·G(1−ρ)·x^{1−ρ}` with the
> Graham error `o(main)` — the Barban–Vehov cancellation (`Salt.SW.MobiusRate` + the
> lcm-regroup) fed through `dhDetector_mellin` + `rectBI_zeta_shift_mul`.

Any q-only `L(1,χ)` lower bound (Siegel/Goldfeld, already in the corpus) CANNOT reach the
target: as `ρ.re → 1` the target RHS `→ c/polylog(q(|γ|+2))`, a repulsion strictly stronger
than `L(1,χ) ≫ 1/√q`. The ρ-dependence is essential and comes only from the shift — this is
why DH-MAIN is the genuine crux, not a bookkeeping gap.

## Honesty / death map (HB-ENGINE, R4 — NO twin claim)

NOT a proof of the Twin Prime Conjecture. Delivers competing-estimate substrate for the
conditional `InfinitelyManySiegelZeros → TwinPrimeConjecture`; the death rung is R4.
-/

open Complex

noncomputable section

namespace Salt.SW

/-! ## The floor in closed form (the competing LOWER estimate) -/

/-- **The positivity floor, evaluated.** For a real `χ` (`χ² = 1`), `z ≥ 2`, `x > 1`, `N ≥ 1`,
the mollified detector is bounded below by `1 − 1/x` (the `n = 1` term `(1 − 1/x)₊`, which is
`1 − 1/x` since `1/x < 1`). This is `dhDetector_floor` with `dhKernR(1/x)` evaluated. -/
lemma dhDetector_floor_explicit {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {z : ℕ} (hz : 2 ≤ z) {x : ℝ} (hx : 1 < x) {N : ℕ} (hN : 1 ≤ N) :
    1 - 1 / x ≤ dhDetector χ z x N := by
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hle : 1 / x ≤ 1 := le_of_lt ((div_lt_one hx0).mpr hx)
  rw [← dhKernR_eq hle]
  exact dhDetector_floor χ hsq hz x hN

/-! ## M-A — the truncation-route `L(1,χ)` lower bound (the honest finite balance)

The naive vertical integral was non-integrable (`DHBalance`'s obstruction map). The finite
truncation sidesteps it entirely at the single point `s = 1`: the landed strip tail
`norm_LFunction_sub_partial_le_strip` bounds `‖L(1,χ) − Σ_{n≤N} χ(n) n^{−1}‖`, and taking real
parts turns the tail bound into a lower bound on `(L(1,χ)).re`. The partial sum is real (χ is
real), so its real part is the character sum `Σ_{n≤N} χ_ℝ(n)/n`. -/

/-- **M-A — the truncation `L(1,χ)` lower bound.** For a primitive real character `χ` mod
`q ≥ 2` and `N ≥ 1`,
`Σ_{n≤N} χ_ℝ(n)/n − 6·√q·(1+log q)/N ≤ (L(1,χ)).re`.
The strip tail at `s = 1` (`M = √q(1+log q)`, `1 + ‖1‖/1 = 2`, `N^{−1}`), real-part inverted.
UNCONDITIONAL; the finite balance in cleanest unmollified form. -/
theorem LFunction_one_re_ge_partial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, chiRe χ n / (n : ℝ))
        - 6 * Real.sqrt q * (1 + Real.log q) / N
      ≤ (DirichletCharacter.LFunction χ 1).re := by
  have hne : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hM : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod q)‖
      ≤ Real.sqrt q * (1 + Real.log q) := fun u => Salt.BV.polya_vinogradov χ hχ hq u
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0
  -- The strip tail at `s = 1`.
  have hstrip := norm_LFunction_sub_partial_le_strip χ hne hq hM (s := (1 : ℂ))
    (by rw [Complex.one_re]; norm_num) (le_of_eq Complex.one_re) hN
  set P : ℂ := ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-(1 : ℂ)) with hP
  -- The partial sum is the real character sum.
  have hPreal : P = ((∑ n ∈ Finset.Icc 1 N, chiRe χ n / (n : ℝ) : ℝ) : ℂ) := by
    rw [hP, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← chiRe_ofReal χ hsq n, Complex.cpow_neg, Complex.cpow_one]
    push_cast
    ring
  have hPre : P.re = ∑ n ∈ Finset.Icc 1 N, chiRe χ n / (n : ℝ) := by
    rw [hPreal, Complex.ofReal_re]
  -- Simplify the strip bound to `6√q(1+log q)/N`.
  have hstrip2 : ‖DirichletCharacter.LFunction χ 1 - P‖
      ≤ 6 * Real.sqrt q * (1 + Real.log q) / N := by
    refine hstrip.trans (le_of_eq ?_)
    rw [Complex.one_re, norm_one, Real.rpow_neg_one]
    field_simp
    ring
  -- Real-part inversion.
  have habs := (abs_le.mp (Complex.abs_re_le_norm (DirichletCharacter.LFunction χ 1 - P))).1
  have hsub : (DirichletCharacter.LFunction χ 1 - P).re
      = (DirichletCharacter.LFunction χ 1).re - P.re := Complex.sub_re _ _
  linarith [habs, hsub, hstrip2, hPre]

/-! ## M-C — the composition into the reversed-Jutila repulsion shape

Feeding the truncation lower bound (M-A) through the UNCONDITIONAL M4 inversion
(`dh_repulsion_of_LFunction_one_lower`) yields the repulsion inequality with the explicit
partial-sum main term. This is the M-C step: everything downstream of the `L(1,χ)` lower bound
is closed; only the identification of the main term with the ρ-dependent shape (DH-MAIN, the
mollifier residual named in the header) remains. -/

/-- **M-C — the truncation repulsion inequality.** For a primitive real `χ` mod `q ≥ 2` with a
real zero `β ∈ [1 − 1/(4(1+log q)), 1)`, the truncation lower bound composed with the Siegel
MVT gives, for any `N ≥ 1`,
`(Σ_{n≤N} χ_ℝ(n)/n − 6√q(1+log q)/N) / (25e(1+log q)²) ≤ 1 − β`.
UNCONDITIONAL. A genuine repulsion once the main term exceeds the error (the mollifier's job). -/
theorem dh_repulsion_partial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β : ℝ}
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hβlo : 1 - 1 / (4 * (1 + Real.log q)) ≤ β) (hβhi : β < 1) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, chiRe χ n / (n : ℝ) - 6 * Real.sqrt q * (1 + Real.log q) / N)
        / (25 * Real.exp 1 * (1 + Real.log q) ^ 2)
      ≤ 1 - β :=
  dh_repulsion_of_LFunction_one_lower χ hχ hq hzero hβlo hβhi
    (LFunction_one_re_ge_partial χ hχ hsq hq hN)

end Salt.SW

end
