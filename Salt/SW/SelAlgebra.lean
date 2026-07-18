/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.SelWeight

/-!
# The Selberg quadratic-form algebra (`T-BAL` R4) — generic diagonalization + R5 rescale

Design: the JYH-ratified **T-BAL S₀ synthesis freeze**
(`docs/exploration/tbal-s0-freeze.md`, the 5th design). This module lands the pure finite
multiplicative algebra of wave 2:

* **`selberg_diag`** — the generic Selberg / Barban–Vehov gcd-totient diagonalization
  `Σ_{d,e ≤ z} λ_d λ_e / lcm(d,e) = Σ_{g ≤ z} φ(g)·(Σ_{g ∣ d ≤ z} λ_d/d)²`, for an ARBITRARY
  real weight `λ : ℕ → ℝ` (the `graham_diagonalisation` proof ported to a generic weight — the
  quadratic form is `λ`-generic; only `sum_totient_indicator_eq_gcd` + field algebra are used).
  Its L²-positivity `selberg_diag_nonneg` records the sign of the form.

* **`rescale_inv_ge`** — the R5 elementary rescale `n^{−1} ≥ z^{β₀−1}·n^{−β₀}` on `1 ≤ n ≤ z`,
  `β₀ ≤ 1` (from `n^{−(1−β₀)} ≥ z^{−(1−β₀)}` at the smaller base with a nonpositive exponent).

The optimality `selberg_opt_eq` (`V(λ^opt) = 1/H(z)` EXACT) and R5's `H_lower` are the deeper
finite-algebra / analytic pieces; see `docs/blueprints/flags.md` (T-BAL wave 2).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open Finset

noncomputable section

namespace Salt.SW

open ArithmeticFunction

/-! ## §1 — the generic Selberg gcd-totient diagonalization -/

/-- **The generic `g`-restricted diagonal factor** `Σ_{d ≤ z, g ∣ d} λ_d/d`. The `λ = grahamTheta z`
case is `GrahamL2.innerG`. -/
def selInnerG (lam : ℕ → ℝ) (z g : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 z, if g ∣ d then lam d / (d : ℝ) else 0

/-- **R4 — the generic Selberg diagonalization.** For every real weight `λ` and every `z`, the
lcm-weighted quadratic form diagonalizes over the common divisor `g` via `1/lcm = gcd/(d·e)`
and `gcd = Σ_{g ∣ ·} φ`:
`Σ_{d,e ≤ z} λ_d λ_e / lcm(d,e) = Σ_{g ≤ z} φ(g)·(Σ_{g ∣ d ≤ z} λ_d/d)²`.
The classical Barban–Vehov / Selberg diagonal quadratic form (Heath-Brown, *Lectures on sieves*);
the `graham_diagonalisation` proof ported to a generic weight. -/
theorem selberg_diag (lam : ℕ → ℝ) (z : ℕ) :
    ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
        lam d * lam e / (Nat.lcm d e : ℝ)
      = ∑ g ∈ Finset.Icc 1 z, (Nat.totient g : ℝ) * (selInnerG lam z g) ^ 2 := by
  have hterm : ∀ d ∈ Finset.Icc 1 z, ∀ e ∈ Finset.Icc 1 z,
      lam d * lam e / (Nat.lcm d e : ℝ)
        = ∑ g ∈ Finset.Icc 1 z,
            (if g ∣ d then lam d / (d : ℝ) else 0)
              * (if g ∣ e then lam e / (e : ℝ) else 0) * (Nat.totient g : ℝ) := by
    intro d hd e he
    obtain ⟨hd1, hdz⟩ := Finset.mem_Icc.mp hd
    obtain ⟨he1, hez⟩ := Finset.mem_Icc.mp he
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have he0 : (e : ℝ) ≠ 0 := by positivity
    have hlcm0 : (Nat.lcm d e : ℝ) ≠ 0 := by
      have : Nat.lcm d e ≠ 0 := Nat.lcm_ne_zero (by omega) (by omega)
      exact_mod_cast this
    have hgl : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = (d : ℝ) * (e : ℝ) := by
      exact_mod_cast Nat.gcd_mul_lcm d e
    have hBsum := sum_totient_indicator_eq_gcd (z := z) (e := e) hd1 hdz
    have hstep : ∀ g : ℕ,
        (if g ∣ d then lam d / (d : ℝ) else 0)
            * (if g ∣ e then lam e / (e : ℝ) else 0) * (Nat.totient g : ℝ)
          = (lam d / (d : ℝ) * (lam e / (e : ℝ)))
              * (if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) else 0) := by
      intro g
      rw [ite_zero_mul_ite_zero]
      split_ifs with h <;> ring
    rw [Finset.sum_congr rfl (fun g _ => hstep g), ← Finset.mul_sum, hBsum]
    field_simp
    linear_combination (-(lam d * lam e)) * hgl
  calc ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
        lam d * lam e / (Nat.lcm d e : ℝ)
      = ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z, ∑ g ∈ Finset.Icc 1 z,
          (if g ∣ d then lam d / (d : ℝ) else 0)
            * (if g ∣ e then lam e / (e : ℝ) else 0) * (Nat.totient g : ℝ) :=
        Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hterm d hd e he))
    _ = ∑ d ∈ Finset.Icc 1 z, ∑ g ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
          (if g ∣ d then lam d / (d : ℝ) else 0)
            * (if g ∣ e then lam e / (e : ℝ) else 0) * (Nat.totient g : ℝ) :=
        Finset.sum_congr rfl (fun d _ => Finset.sum_comm)
    _ = ∑ g ∈ Finset.Icc 1 z, ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
          (if g ∣ d then lam d / (d : ℝ) else 0)
            * (if g ∣ e then lam e / (e : ℝ) else 0) * (Nat.totient g : ℝ) :=
        Finset.sum_comm
    _ = ∑ g ∈ Finset.Icc 1 z, (Nat.totient g : ℝ) * (selInnerG lam z g) ^ 2 := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        have hfac : ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
              (if g ∣ d then lam d / (d : ℝ) else 0)
                * (if g ∣ e then lam e / (e : ℝ) else 0) * (Nat.totient g : ℝ)
            = (Nat.totient g : ℝ) * (selInnerG lam z g * selInnerG lam z g) := by
          unfold selInnerG
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun e _ => ?_)
          ring
        rw [hfac, sq]

/-- **R4 — the diagonal form is nonnegative.** `Σ_{d,e ≤ z} λ_d λ_e / lcm(d,e) ≥ 0` for every real
weight `λ` (a sum of `φ(g)·squares`). The genuine L²-positivity of the Selberg quadratic form. -/
lemma selberg_diag_nonneg (lam : ℕ → ℝ) (z : ℕ) :
    0 ≤ ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
        lam d * lam e / (Nat.lcm d e : ℝ) := by
  rw [selberg_diag]
  exact Finset.sum_nonneg (fun g _ => by positivity)

/-! ## §2 — the R5 elementary rescale `n^{−1} ≥ z^{β₀−1}·n^{−β₀}` on `n ≤ z` -/

/-- **R5 rescale helper [A].** For `1 ≤ n ≤ z` and `β₀ ≤ 1`, `z^{β₀−1}·n^{−β₀} ≤ n^{−1}`.
`n^{−1} = n^{−β₀}·n^{−(1−β₀)}` and `n^{−(1−β₀)} ≥ z^{−(1−β₀)} = z^{β₀−1}` (smaller base, nonpositive
exponent). Used to lower-bound the `n^{−1}` harmonic weight by the `β₀`-rescaled `n^{−β₀}`. -/
lemma rescale_inv_ge {β₀ : ℝ} (hβ : β₀ ≤ 1) {z n : ℕ} (hn : 1 ≤ n) (hnz : n ≤ z) :
    (z : ℝ) ^ (β₀ - 1) * (n : ℝ) ^ (-β₀) ≤ (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnzR : (n : ℝ) ≤ (z : ℝ) := by exact_mod_cast hnz
  have hexp : β₀ - 1 ≤ 0 := by linarith
  -- z^{β₀−1} ≤ n^{β₀−1} : smaller base `n ≤ z`, nonpositive exponent.
  have hzn : (z : ℝ) ^ (β₀ - 1) ≤ (n : ℝ) ^ (β₀ - 1) :=
    Real.rpow_le_rpow_of_nonpos hn0 hnzR hexp
  calc (z : ℝ) ^ (β₀ - 1) * (n : ℝ) ^ (-β₀)
      ≤ (n : ℝ) ^ (β₀ - 1) * (n : ℝ) ^ (-β₀) :=
        mul_le_mul_of_nonneg_right hzn (Real.rpow_nonneg hn0.le _)
    _ = (n : ℝ) ^ ((β₀ - 1) + (-β₀)) := (Real.rpow_add hn0 _ _).symm
    _ = (n : ℝ) ^ (-1 : ℝ) := by congr 1; ring
    _ = (n : ℝ)⁻¹ := by rw [Real.rpow_neg_one]

end Salt.SW

end
