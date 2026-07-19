/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.L2MVT

/-!
# MR-CORE campaign, wave 1, node P1 (MV-HILBERT): the Dirichlet-polynomial L² mean value

Blueprint / freeze: `docs/exploration/s8-freeze.md` ([E3] MVHilbert, [P1] wave-1 table).

This file closes the `(2T + C_MV·N)` mean-value bound for Dirichlet polynomials, on
top of the honest reduction already landed in `Salt/MR/L2MVT.lean`
(`dirichlet_poly_l2_expand` / `dirichlet_poly_l2_diagonal`).

## The mathematics

For `F(t) = ∑_{1≤n≤N} aₙ·exp(i·t·log n)` the target is

  `∫_{-T}^{T} ‖F(t)‖² dt ≤ (2T + C_MV·N)·∑ ‖aₙ‖²`,  `C_MV ≤ 20`.

The `(T+N)` shape is **mandatory** — `T + N·log N` is a refuted substitution (the wave-4
consumer `E1` is log-intolerant at fixed `h`).  The naive triangle bound on the
off-diagonal loses exactly that `log N`, so genuine bilinear cancellation is required:
the **Montgomery–Vaughan generalized Hilbert inequality** (Montgomery–Vaughan 1974,
"Hilbert's Inequality"; Iwaniec–Kowalski, *Analytic Number Theory*, Thm 9.1).

### The sin-kernel is not an obstruction

`L2MVT.lean` flagged the off-diagonal kernel `Jₘₙ = 2 sin(Tθ)/θ` (θ = log m − log n) as
the gap.  The key structural observation (this file): `Jₘₙ = (e^{iTθ} − e^{-iTθ})/(iθ)`,
so with the *twisted* coefficients `cₖ = aₖ·k^{iT}`, `dₖ = aₖ·k^{-iT}` (both `‖·‖ = ‖aₖ‖`),
the off-diagonal splits as

  `OD = (1/i)·(H(c) − H(d))`,  `H(x) = ∑_{m≠n} xₘ·conj(xₙ)/(log m − log n)`,

i.e. **two applications of the pure Hilbert form** — no sin-kernel to fight.  Hence

  `‖OD‖ ≤ ‖H(c)‖ + ‖H(d)‖ ≤ 2·(π/δ)·∑‖aₙ‖²`

by the Montgomery–Vaughan inequality, with `δ = 1/N` the (uniform) frequency gap of
`{log n : 1 ≤ n ≤ N}`; `2π ≤ 20` gives `C_MV`.

### Status

The entire reduction is landed sorry-free.  The single irreducible hard core — the
Montgomery–Vaughan Hilbert inequality `‖H(x)‖ ≤ (π/δ)∑‖xₙ‖²` itself, which mathlib does
**not** have and which admits no Schur-type elementary proof (the Schur norm is `≍ N log N`)
— is carried as the explicit hypothesis `MVHilbertUniform` of `dirichlet_poly_l2_mvt`.
Also landed: `l2_duality`, the large-sieve duality principle (for the wave-2 consumer).
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory intervalIntegral

/-- The off-diagonal interval integral, evaluated by the FTC:
`∫_{-T}^{T} exp(i·t·θ) dt = (exp(iθT) − exp(iθ(-T))) / (iθ)` for `θ ≠ 0`. -/
lemma offdiag_integral_eq (θ : ℂ) (hθ : θ ≠ 0) (T : ℝ) :
    (∫ t in (-T)..T, Complex.exp (Complex.I * (t : ℂ) * θ))
      = (Complex.exp (Complex.I * θ * (T : ℂ))
          - Complex.exp (Complex.I * θ * ((-T : ℝ) : ℂ))) / (Complex.I * θ) := by
  have hc : Complex.I * θ ≠ 0 := mul_ne_zero Complex.I_ne_zero hθ
  have h1 : (∫ t in (-T)..T, Complex.exp (Complex.I * (t : ℂ) * θ))
      = ∫ t in (-T)..T, Complex.exp (Complex.I * θ * (t : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact congrArg Complex.exp (mul_right_comm Complex.I (t : ℂ) θ)
  rw [h1, integral_exp_mul_complex hc]

/-- The uniform frequency gap of `{log n : 1 ≤ n ≤ N}`: distinct integers in `[1,N]`
have `|log m − log n| ≥ 1/N`.  (Elementary: `log m − log n ≥ 1 − n/m ≥ (m−n)/m ≥ 1/N`.) -/
lemma log_gap_ge {N m n : ℕ} (hm : m ∈ Finset.Icc 1 N) (hn : n ∈ Finset.Icc 1 N)
    (hmn : m ≠ n) : (1 : ℝ) / N ≤ |Real.log m - Real.log n| := by
  have main : ∀ p q : ℕ, p ∈ Finset.Icc 1 N → q ∈ Finset.Icc 1 N → q < p →
      (1 : ℝ) / N ≤ Real.log p - Real.log q := by
    intro p q hp hq hqp
    rcases Finset.mem_Icc.1 hp with ⟨hp1, hpN⟩
    rcases Finset.mem_Icc.1 hq with ⟨hq1, _⟩
    have hNr : (0 : ℝ) < N := by
      have : (1 : ℕ) ≤ N := le_trans hp1 hpN
      exact_mod_cast lt_of_lt_of_le Nat.one_pos this
    have hppos : (0 : ℝ) < p := by exact_mod_cast lt_of_lt_of_le Nat.one_pos hp1
    have hqpos : (0 : ℝ) < q := by exact_mod_cast lt_of_lt_of_le Nat.one_pos hq1
    have hpN' : (p : ℝ) ≤ N := by exact_mod_cast hpN
    have h1 : Real.log ((q : ℝ) / p) ≤ (q : ℝ) / p - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log ((q : ℝ) / p) = Real.log q - Real.log p := by
      rw [Real.log_div (ne_of_gt hqpos) (ne_of_gt hppos)]
    have h3 : 1 - (q : ℝ) / p ≤ Real.log p - Real.log q := by rw [h2] at h1; linarith
    have hmn1 : (1 : ℝ) ≤ (p : ℝ) - q := by
      have hc : (q : ℝ) + 1 ≤ p := by exact_mod_cast hqp
      linarith
    have h1' : (N : ℝ) ≤ N * ((p : ℝ) - q) := by
      nlinarith [mul_nonneg (le_of_lt hNr) (show (0 : ℝ) ≤ (p : ℝ) - q - 1 by linarith)]
    have hexp : (N : ℝ) * ((p : ℝ) - q) = N * p - N * q := by ring
    have hcross : (p : ℝ) ≤ N * p - N * q := by rw [hexp] at h1'; linarith
    have hlow : (1 : ℝ) / N ≤ 1 - (q : ℝ) / p := by
      rw [le_sub_iff_add_le, div_add_div _ _ (ne_of_gt hNr) (ne_of_gt hppos),
        div_le_one (by positivity)]
      linarith [hcross]
    linarith [hlow, h3]
  have hNnn : (0 : ℝ) ≤ (1 : ℝ) / N := by positivity
  rcases lt_or_gt_of_ne hmn with h | h
  · have hval := main n m hn hm h
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact hval
  · have hval := main m n hm hn h
    rw [abs_of_nonneg (by linarith)]
    exact hval

/-- The `+`-twisted coefficient `cₖ = aₖ·k^{iT} = aₖ·exp(i·T·log k)`. -/
noncomputable def twistPos (a : ℕ → ℂ) (T : ℝ) (k : ℕ) : ℂ :=
  a k * Complex.exp (Complex.I * (T : ℂ) * (Real.log k : ℂ))

/-- The `−`-twisted coefficient `dₖ = aₖ·k^{-iT} = aₖ·exp(-i·T·log k)`. -/
noncomputable def twistNeg (a : ℕ → ℂ) (T : ℝ) (k : ℕ) : ℂ :=
  a k * Complex.exp (-(Complex.I * (T : ℂ) * (Real.log k : ℂ)))

/-- The pure Hilbert bilinear form at log-frequencies:
`H(x) = ∑_{1≤n≤N} ∑_{1≤m≤N, m≠n} xₘ·conj(xₙ)/(log m − log n)`. -/
noncomputable def hilbertLogSum (N : ℕ) (x : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
    x m * (starRingEnd ℂ) (x n) / ((Real.log m : ℂ) - (Real.log n : ℂ))

/-- **Montgomery–Vaughan generalized Hilbert inequality** (uniform-gap form), as a
reusable hypothesis.  For any finite `s`, real frequencies `lam` that are `δ`-separated
on `s`, and complex weights `x`:
`‖∑_{i∈s} ∑_{j∈s, j≠i} xⱼ·conj(xᵢ)/(lam j − lam i)‖ ≤ (π/δ)·∑_{i∈s} ‖xᵢ‖²`.
mathlib has no such lemma; it admits no Schur-type elementary proof (Schur norm `≍ N log N`).
Carried as the single hard hypothesis of `dirichlet_poly_l2_mvt`. -/
def MVHilbertUniform : Prop :=
  ∀ (s : Finset ℕ) (lam : ℕ → ℝ) (x : ℕ → ℂ) (δ : ℝ), 0 < δ →
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |lam i - lam j|) →
    ‖∑ i ∈ s, ∑ j ∈ s.erase i,
        x j * (starRingEnd ℂ) (x i) / ((lam j : ℂ) - (lam i : ℂ))‖
      ≤ Real.pi / δ * ∑ i ∈ s, ‖x i‖ ^ 2

/-- `conj(exp(i·T·r)) = exp(-i·T·r)` for real `T, r`. -/
lemma conj_exp_I_mul (T r : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * (T : ℂ) * (r : ℂ)))
      = Complex.exp (-(Complex.I * (T : ℂ) * (r : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- `conj(exp(-i·T·r)) = exp(i·T·r)` for real `T, r`. -/
lemma conj_exp_neg_I_mul (T r : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(Complex.I * (T : ℂ) * (r : ℂ))))
      = Complex.exp (Complex.I * (T : ℂ) * (r : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- The twist has unit modulus: `‖cₖ‖ = ‖aₖ‖`. -/
lemma norm_twistPos (a : ℕ → ℂ) (T : ℝ) (k : ℕ) : ‖twistPos a T k‖ = ‖a k‖ := by
  rw [twistPos, norm_mul,
    show Complex.I * (T : ℂ) * (Real.log k : ℂ)
        = ((T * Real.log k : ℝ) : ℂ) * Complex.I from by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The twist has unit modulus: `‖dₖ‖ = ‖aₖ‖`. -/
lemma norm_twistNeg (a : ℕ → ℂ) (T : ℝ) (k : ℕ) : ‖twistNeg a T k‖ = ‖a k‖ := by
  rw [twistNeg, norm_mul,
    show -(Complex.I * (T : ℂ) * (Real.log k : ℂ))
        = ((-(T * Real.log k) : ℝ) : ℂ) * Complex.I from by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **The twisted numerator identity.**  The off-diagonal numerator
`conj(aₙ)·aₘ·(e^{iθT} − e^{iθ(-T)})` (θ = log m − log n) equals `cₘ·conj(cₙ) − dₘ·conj(dₙ)`,
i.e. the two Hilbert-form numerators.  This is the algebraic heart of the sin-kernel
resolution. -/
lemma twist_num_eq (a : ℕ → ℂ) (T : ℝ) (m n : ℕ) :
    twistPos a T m * (starRingEnd ℂ) (twistPos a T n)
      - twistNeg a T m * (starRingEnd ℂ) (twistNeg a T n)
    = (starRingEnd ℂ) (a n) * a m
      * (Complex.exp (Complex.I * ((Real.log m : ℂ) - (Real.log n : ℂ)) * (T : ℂ))
          - Complex.exp (Complex.I * ((Real.log m : ℂ) - (Real.log n : ℂ)) * ((-T : ℝ) : ℂ))) := by
  have hLHSp : twistPos a T m * (starRingEnd ℂ) (twistPos a T n)
      = (starRingEnd ℂ) (a n) * a m
        * Complex.exp (Complex.I * ((Real.log m : ℂ) - (Real.log n : ℂ)) * (T : ℂ)) := by
    have e1 : Complex.exp (Complex.I * (T : ℂ) * (Real.log m : ℂ))
          * Complex.exp (-(Complex.I * (T : ℂ) * (Real.log n : ℂ)))
        = Complex.exp (Complex.I * ((Real.log m : ℂ) - (Real.log n : ℂ)) * (T : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    simp only [twistPos]
    rw [map_mul, conj_exp_I_mul T (Real.log n)]
    calc a m * Complex.exp (Complex.I * (T : ℂ) * (Real.log m : ℂ))
            * ((starRingEnd ℂ) (a n) * Complex.exp (-(Complex.I * (T : ℂ) * (Real.log n : ℂ))))
        = (starRingEnd ℂ) (a n) * a m
            * (Complex.exp (Complex.I * (T : ℂ) * (Real.log m : ℂ))
              * Complex.exp (-(Complex.I * (T : ℂ) * (Real.log n : ℂ)))) := by ring
      _ = _ := by rw [e1]
  have hLHSn : twistNeg a T m * (starRingEnd ℂ) (twistNeg a T n)
      = (starRingEnd ℂ) (a n) * a m
        * Complex.exp (Complex.I * ((Real.log m : ℂ) - (Real.log n : ℂ)) * ((-T : ℝ) : ℂ)) := by
    have e1 : Complex.exp (-(Complex.I * (T : ℂ) * (Real.log m : ℂ)))
          * Complex.exp (Complex.I * (T : ℂ) * (Real.log n : ℂ))
        = Complex.exp (Complex.I * ((Real.log m : ℂ) - (Real.log n : ℂ)) * ((-T : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp only [twistNeg]
    rw [map_mul, conj_exp_neg_I_mul T (Real.log n)]
    calc a m * Complex.exp (-(Complex.I * (T : ℂ) * (Real.log m : ℂ)))
            * ((starRingEnd ℂ) (a n) * Complex.exp (Complex.I * (T : ℂ) * (Real.log n : ℂ)))
        = (starRingEnd ℂ) (a n) * a m
            * (Complex.exp (-(Complex.I * (T : ℂ) * (Real.log m : ℂ)))
              * Complex.exp (Complex.I * (T : ℂ) * (Real.log n : ℂ))) := by ring
      _ = _ := by rw [e1]
  rw [hLHSp, hLHSn, ← mul_sub]

/-- Per off-diagonal term: `i·conj(aₙ)·aₘ·Jₘₙ` equals the difference of the two Hilbert-form
summands (for the twisted coefficients `c`, `d`).  The sin-kernel `Jₘₙ` disappears. -/
lemma offdiag_term_hilbert (a : ℕ → ℂ) (T : ℝ) {m n : ℕ} (hmn : m ≠ n)
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Complex.I * ((starRingEnd ℂ) (a n) * a m
        * ∫ t in (-T)..T,
            Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))))
      = twistPos a T m * (starRingEnd ℂ) (twistPos a T n)
          / ((Real.log m : ℂ) - (Real.log n : ℂ))
        - twistNeg a T m * (starRingEnd ℂ) (twistNeg a T n)
          / ((Real.log m : ℂ) - (Real.log n : ℂ)) := by
  have hθ : (Real.log m : ℂ) - (Real.log n : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    rw [Complex.ofReal_inj] at h
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hmn' : (m : ℝ) = n := by
      have := congrArg Real.exp h
      rwa [Real.exp_log hmpos, Real.exp_log hnpos] at this
    exact hmn (by exact_mod_cast hmn')
  rw [offdiag_integral_eq _ hθ, div_sub_div_same, twist_num_eq]
  field_simp

/-- **The sin-free off-diagonal identity.**  `i · OD = H(c) − H(d)`, where `OD` is the
`L2MVT` off-diagonal double sum and `H` the pure Hilbert form of the twisted coefficients. -/
lemma offdiag_eq_hilbert (N : ℕ) (a : ℕ → ℂ) (T : ℝ) :
    Complex.I * (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
        (starRingEnd ℂ) (a n) * a m
          * ∫ t in (-T)..T,
              Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))))
      = hilbertLogSum N (twistPos a T) - hilbertLogSum N (twistNeg a T) := by
  rw [Finset.mul_sum, hilbertLogSum, hilbertLogSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≠ n := Finset.ne_of_mem_erase hm
  have hm1 : 1 ≤ m := (Finset.mem_Icc.1 (Finset.mem_of_mem_erase hm)).1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  exact offdiag_term_hilbert a T hmn hm1 hn1

/-- The Montgomery–Vaughan bound, specialized to the log-frequency Hilbert form
`hilbertLogSum`. -/
lemma norm_hilbertLogSum_le (hMV : MVHilbertUniform) (N : ℕ) (x : ℕ → ℂ) {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : ∀ i ∈ Finset.Icc 1 N, ∀ j ∈ Finset.Icc 1 N, i ≠ j →
      δ ≤ |Real.log i - Real.log j|) :
    ‖hilbertLogSum N x‖ ≤ Real.pi / δ * ∑ n ∈ Finset.Icc 1 N, ‖x n‖ ^ 2 := by
  have h := hMV (Finset.Icc 1 N) (fun k => Real.log k) x δ hδ hgap
  simpa [hilbertLogSum] using h

/-- **The Dirichlet-polynomial L² mean value theorem** (`(T+N)` shape, `C_MV = 20`).
Given the Montgomery–Vaughan Hilbert inequality `hMV`, for `0 ≤ T`,
`∫_{-T}^{T} ‖F(t)‖² ≤ (2T + 20·N)·∑‖aₙ‖²`.  The `(T+N)` shape is mandatory (no `log N`). -/
theorem dirichlet_poly_l2_mvt (hMV : MVHilbertUniform) (N : ℕ) (a : ℕ → ℂ) (T : ℝ) :
    (∫ t in (-T)..T, ‖dpoly N a t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    simp [dpoly]
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    set P := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 with hPdef
    have hPnn : 0 ≤ P := by rw [hPdef]; exact Finset.sum_nonneg (fun n _ => by positivity)
    have hdiag := dirichlet_poly_l2_diagonal N a T
    have hIeq := offdiag_eq_hilbert N a T
    set S := ∫ t in (-T)..T, ‖dpoly N a t‖ ^ 2 with hSdef
    set OD := ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
        (starRingEnd ℂ) (a n) * a m
          * ∫ t in (-T)..T,
              Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ)))
      with hODdef
    have hsumcast : (∑ n ∈ Finset.Icc 1 N, ((‖a n‖ ^ 2 : ℝ) : ℂ)) = ((P : ℝ) : ℂ) := by
      rw [hPdef, Complex.ofReal_sum]
    rw [hsumcast] at hdiag
    have hODreal : OD = ((S - 2 * T * P : ℝ) : ℂ) := by
      have h2 : OD = (S : ℂ) - ((2 * T : ℝ) : ℂ) * ((P : ℝ) : ℂ) := by rw [hdiag]; ring
      rw [h2]; push_cast; ring
    have hnormOD : ‖OD‖ = ‖(S - 2 * T * P : ℝ)‖ := by rw [hODreal, Complex.norm_real]
    have hnorm_I : ‖OD‖
        = ‖hilbertLogSum N (twistPos a T) - hilbertLogSum N (twistNeg a T)‖ := by
      rw [← hIeq, norm_mul, Complex.norm_I, one_mul]
    have hδ : (0 : ℝ) < 1 / (N : ℝ) := one_div_pos.mpr hNr
    have hgap : ∀ i ∈ Finset.Icc 1 N, ∀ j ∈ Finset.Icc 1 N, i ≠ j →
        (1 : ℝ) / (N : ℝ) ≤ |Real.log i - Real.log j| :=
      fun i hi j hj hij => log_gap_ge hi hj hij
    have hc := norm_hilbertLogSum_le hMV N (twistPos a T) hδ hgap
    have hd := norm_hilbertLogSum_le hMV N (twistNeg a T) hδ hgap
    have hsumc : (∑ n ∈ Finset.Icc 1 N, ‖twistPos a T n‖ ^ 2) = P := by
      rw [hPdef]; exact Finset.sum_congr rfl (fun n _ => by rw [norm_twistPos])
    have hsumd : (∑ n ∈ Finset.Icc 1 N, ‖twistNeg a T n‖ ^ 2) = P := by
      rw [hPdef]; exact Finset.sum_congr rfl (fun n _ => by rw [norm_twistNeg])
    rw [one_div, div_inv_eq_mul, hsumc] at hc
    rw [one_div, div_inv_eq_mul, hsumd] at hd
    have hOD_bound : ‖OD‖ ≤ 2 * (Real.pi * N) * P := by
      rw [hnorm_I]
      calc ‖hilbertLogSum N (twistPos a T) - hilbertLogSum N (twistNeg a T)‖
          ≤ ‖hilbertLogSum N (twistPos a T)‖ + ‖hilbertLogSum N (twistNeg a T)‖ :=
            norm_sub_le _ _
        _ ≤ Real.pi * N * P + Real.pi * N * P := add_le_add hc hd
        _ = 2 * (Real.pi * N) * P := by ring
    have hSle : S - 2 * T * P ≤ 2 * (Real.pi * N) * P := by
      have h1 : S - 2 * T * P ≤ ‖(S - 2 * T * P : ℝ)‖ := Real.le_norm_self _
      rw [← hnormOD] at h1
      linarith [h1, hOD_bound]
    calc S ≤ 2 * T * P + 2 * (Real.pi * N) * P := by linarith [hSle]
      _ ≤ 2 * T * P + 20 * (N : ℝ) * P := by
          nlinarith [Real.pi_le_four, mul_nonneg hNr.le hPnn]
      _ = (2 * T + 20 * (N : ℝ)) * P := by ring

/-- One direction of the large-sieve **duality principle**: the dual bound implies the
primal.  `∑_n ‖∑_r conj(φ r n)·b_r‖² ≤ Δ ∑_r ‖b_r‖²` (for all `b`) gives
`∑_r ‖∑_n φ r n·a_n‖² ≤ Δ ∑_n ‖a_n‖²`.  Proof: the Parseval identity
`∑_r ‖c_r‖² = ∑_n a_n·conj(e_n)` (c = φ·a, e = conj(φ)·c) + Cauchy–Schwarz. -/
lemma l2_dual_of {ι κ : Type*} (s : Finset ι) (t : Finset κ) (φ : ι → κ → ℂ) {Δ : ℝ}
    (hΔ : 0 ≤ Δ)
    (hdual : ∀ b : ι → ℂ, ∑ n ∈ t, ‖∑ r ∈ s, (starRingEnd ℂ) (φ r n) * b r‖ ^ 2
        ≤ Δ * ∑ r ∈ s, ‖b r‖ ^ 2)
    (a : κ → ℂ) :
    ∑ r ∈ s, ‖∑ n ∈ t, φ r n * a n‖ ^ 2 ≤ Δ * ∑ n ∈ t, ‖a n‖ ^ 2 := by
  classical
  set c : ι → ℂ := fun r => ∑ n ∈ t, φ r n * a n with hc
  set e : κ → ℂ := fun n => ∑ r ∈ s, (starRingEnd ℂ) (φ r n) * c r with he
  change ∑ r ∈ s, ‖c r‖ ^ 2 ≤ Δ * ∑ n ∈ t, ‖a n‖ ^ 2
  have hcr : ∀ r, (∑ n ∈ t, φ r n * a n) = c r := fun r => rfl
  have hen : ∀ n, (∑ r ∈ s, (starRingEnd ℂ) (φ r n) * c r) = e n := fun n => rfl
  have hA_nonneg : 0 ≤ ∑ r ∈ s, ‖c r‖ ^ 2 := Finset.sum_nonneg fun r _ => by positivity
  have hB_nonneg : 0 ≤ ∑ n ∈ t, ‖a n‖ ^ 2 := Finset.sum_nonneg fun n _ => by positivity
  have hZ : (∑ r ∈ s, ((‖c r‖ ^ 2 : ℝ) : ℂ)) = ∑ n ∈ t, a n * (starRingEnd ℂ) (e n) := by
    have step1 : ∀ n ∈ t, a n * (starRingEnd ℂ) (e n)
        = ∑ r ∈ s, (starRingEnd ℂ) (c r) * (φ r n * a n) := by
      intro n _
      rw [← hen n, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [map_mul, Complex.conj_conj]
      ring
    rw [Finset.sum_congr rfl step1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.mul_sum, hcr r, ← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  have hAeq : ((∑ r ∈ s, ‖c r‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ t, a n * (starRingEnd ℂ) (e n) := by
    rw [Complex.ofReal_sum]; exact hZ
  have hAW : (∑ r ∈ s, ‖c r‖ ^ 2) ≤ ∑ n ∈ t, ‖a n‖ * ‖e n‖ := by
    have h1 : (∑ r ∈ s, ‖c r‖ ^ 2) = ‖∑ n ∈ t, a n * (starRingEnd ℂ) (e n)‖ := by
      rw [← hAeq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA_nonneg]
    rw [h1]
    calc ‖∑ n ∈ t, a n * (starRingEnd ℂ) (e n)‖
        ≤ ∑ n ∈ t, ‖a n * (starRingEnd ℂ) (e n)‖ := norm_sum_le _ _
      _ = ∑ n ∈ t, ‖a n‖ * ‖e n‖ := by
          apply Finset.sum_congr rfl; intro n _; rw [norm_mul, Complex.norm_conj]
  have hA2W2 : (∑ r ∈ s, ‖c r‖ ^ 2) ^ 2 ≤ (∑ n ∈ t, ‖a n‖ * ‖e n‖) ^ 2 :=
    pow_le_pow_left₀ hA_nonneg hAW 2
  have hW2 : (∑ n ∈ t, ‖a n‖ * ‖e n‖) ^ 2
      ≤ (∑ n ∈ t, ‖a n‖ ^ 2) * (∑ n ∈ t, ‖e n‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq t (fun n => ‖a n‖) (fun n => ‖e n‖)
  have hEA : (∑ n ∈ t, ‖e n‖ ^ 2) ≤ Δ * ∑ r ∈ s, ‖c r‖ ^ 2 := hdual c
  have hBE : (∑ n ∈ t, ‖a n‖ ^ 2) * (∑ n ∈ t, ‖e n‖ ^ 2)
      ≤ (∑ n ∈ t, ‖a n‖ ^ 2) * (Δ * ∑ r ∈ s, ‖c r‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hEA hB_nonneg
  have hfin : (∑ r ∈ s, ‖c r‖ ^ 2) ^ 2
      ≤ Δ * (∑ r ∈ s, ‖c r‖ ^ 2) * (∑ n ∈ t, ‖a n‖ ^ 2) := by
    nlinarith [hA2W2, hW2, hBE]
  rcases eq_or_lt_of_le hA_nonneg with hA0 | hApos
  · rw [← hA0]; exact mul_nonneg hΔ hB_nonneg
  · nlinarith [hfin, hApos]

/-- **The large-sieve duality principle** (MR L10).  For a finite complex matrix `φ` and
`0 ≤ Δ`, the primal `L²` bound holds for all `a` iff the dual bound holds for all `b`. -/
theorem l2_duality {ι κ : Type*} (s : Finset ι) (t : Finset κ) (φ : ι → κ → ℂ) {Δ : ℝ}
    (hΔ : 0 ≤ Δ) :
    (∀ a : κ → ℂ, ∑ r ∈ s, ‖∑ n ∈ t, φ r n * a n‖ ^ 2 ≤ Δ * ∑ n ∈ t, ‖a n‖ ^ 2) ↔
    (∀ b : ι → ℂ, ∑ n ∈ t, ‖∑ r ∈ s, (starRingEnd ℂ) (φ r n) * b r‖ ^ 2
        ≤ Δ * ∑ r ∈ s, ‖b r‖ ^ 2) := by
  constructor
  · intro hprimal b
    refine l2_dual_of t s (fun n r => (starRingEnd ℂ) (φ r n)) hΔ ?_ b
    intro c
    simp only [Complex.conj_conj]
    exact hprimal c
  · intro hdual a
    exact l2_dual_of s t φ hΔ hdual a

end Salt.MR
