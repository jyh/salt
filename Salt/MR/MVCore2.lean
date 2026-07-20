/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MVCore

/-!
# MR-CORE, node K2 (MV-CORE-2): discharging the generalized Hilbert inequality

This file discharges `MVHilbertUniform` (`Salt/MR/MVHilbert.lean`), the frozen hypothesis of
`dirichlet_poly_l2_mvt`, by porting the *proof method* of Montgomery & Vaughan, "Hilbert's
inequality", J. London Math. Soc. (2) 8 (1974), 73–82 (`docs/sources/mv1974-hilbert.pdf`),
Theorem 1 (§3, pp. 79–80) applied directly to the λ-kernel `1/(λ_r − λ_s)` (their Theorem 2,
eq. (1.6), p. 74).

## Why the λ-kernel and not the csc form

The paper's sharp inequality is stated for `csc π(x_r − x_s)` (Thm 1) and derived for
`1/(λ_r − λ_s)` (Thm 2) by an `ε → 0` limit (p. 82).  Porting the csc form requires
Lemmata 1–5 (contour integrals, convexity of `csc²`, pp. 76–78) — brutal.  But the *proof
method* of §3 ports verbatim to the λ-kernel, where every `csc`/`cot` degenerates to
`1/(λ_r − λ_s)` and the single analytic input is the diagonal bound
`Σ 1/(λ_r − λ_s)² ≤ π²/(3δ²)` — already landed as `sep_inv_sq_sum_le` in `MVCore.lean`.

## The port (§3, p. 79)

For an extremal eigenvector `u` with `Σ'_r u_r/(λ_r − λ_s) = iμ u_s` (eq. (3.1)), we bound
`Σ_s |Σ'_r u_r/(λ_r − λ_s)|² = Σ_s |iμ u_s|² = μ² Σ|u_s|²` from above.  Expanding the square
and using the partial-fraction identity (the λ-analog of (3.6))

  `1/((λ_r − λ_i)(λ_t − λ_i)) = 1/(λ_t − λ_r) · (1/(λ_r − λ_i) − 1/(λ_t − λ_i))`,

the "cot-analog" cross terms `S₃, S₄` are equal by (3.1) (the eigen-collapse — this is where
the genuine cancellation lives; the Schur route without it loses `log N`).  What survives is
the diagonal `S₁` plus a doubled off-diagonal, both controlled by `sep_inv_sq_sum_le`, giving
`μ² Σ|u_s|² ≤ (π²/δ²) Σ|u_s|²`, hence `|μ| ≤ π/δ`.
-/

namespace Salt.MR

open scoped BigOperators Matrix

/-- The λ-kernel `1/(λ_r − λ_i)` as a complex number (real-valued). -/
private noncomputable def mvKer (lam : ℕ → ℝ) (r i : ℕ) : ℂ := ((lam r : ℂ) - (lam i : ℂ))⁻¹

private lemma mvKer_self (lam : ℕ → ℝ) (i : ℕ) : mvKer lam i i = 0 := by
  simp [mvKer]

private lemma mvKer_swap (lam : ℕ → ℝ) (r t : ℕ) : mvKer lam t r = - mvKer lam r t := by
  rw [mvKer, mvKer, ← neg_sub ((lam r : ℂ)) ((lam t : ℂ)), inv_neg]

/-- The kernel denominator is nonzero for `δ`-separated distinct points. -/
private lemma mv_den_ne {s : Finset ℕ} {lam : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |lam i - lam j|)
    {a b : ℕ} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ((lam a : ℂ) - (lam b : ℂ)) ≠ 0 := by
  have hd : δ ≤ |lam a - lam b| := hsep a ha b hb hab
  have hr : lam a - lam b ≠ 0 := by
    intro h; rw [h, abs_zero] at hd; linarith
  rw [← Complex.ofReal_sub]
  exact_mod_cast hr

/-- **The partial-fraction sum (λ-analog of MV eq. (3.6)).**  For `δ`-separated points and
`r ≠ t` in `s`,
`Σ_i K(r,i)·K(t,i) = K(t,r)·(Σ_i K(r,i) − Σ_i K(t,i)) + 2·K(t,r)²`,
where `K = mvKer`.  Proof: the summand `g i = K(r,i)K(t,i) − K(t,r)(K(r,i) − K(t,i))`
vanishes off `{r,t}` (the partial-fraction identity) and equals `K(t,r)²` at each of `r, t`
(the Lean division-by-zero at the pole supplying the two boundary terms MV add by hand). -/
private lemma mvPF (s : Finset ℕ) (lam : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |lam i - lam j|)
    {r t : ℕ} (hr : r ∈ s) (ht : t ∈ s) (hrt : r ≠ t) :
    ∑ i ∈ s, mvKer lam r i * mvKer lam t i
      = mvKer lam t r * (∑ i ∈ s, mvKer lam r i)
        - mvKer lam t r * (∑ i ∈ s, mvKer lam t i)
        + 2 * mvKer lam t r ^ 2 := by
  classical
  set g : ℕ → ℂ := fun i => mvKer lam r i * mvKer lam t i
      - mvKer lam t r * (mvKer lam r i - mvKer lam t i) with hgdef
  have hgsum : ∑ i ∈ s, g i = 2 * mvKer lam t r ^ 2 := by
    have hsub : ({r, t} : Finset ℕ) ⊆ s := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h <;> subst h <;> assumption
    have hz : ∀ i ∈ s, i ∉ ({r, t} : Finset ℕ) → g i = 0 := by
      intro i hi hi2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi2
      obtain ⟨hir, hit⟩ := hi2
      have d1ne : ((lam r : ℂ) - (lam i : ℂ)) ≠ 0 := mv_den_ne hδ hsep hr hi (Ne.symm hir)
      have d2ne : ((lam t : ℂ) - (lam i : ℂ)) ≠ 0 := mv_den_ne hδ hsep ht hi (Ne.symm hit)
      have d3ne : ((lam t : ℂ) - (lam r : ℂ)) ≠ 0 := mv_den_ne hδ hsep ht hr (Ne.symm hrt)
      simp only [hgdef, mvKer]
      set d1 := (lam r : ℂ) - (lam i : ℂ) with hd1
      set d2 := (lam t : ℂ) - (lam i : ℂ) with hd2
      set d3 := (lam t : ℂ) - (lam r : ℂ) with hd3
      have hd : d3 = d2 - d1 := by rw [hd1, hd2, hd3]; ring
      have hd3' : d2 - d1 ≠ 0 := hd ▸ d3ne
      rw [hd]
      field_simp
      ring
    calc ∑ i ∈ s, g i = ∑ i ∈ ({r, t} : Finset ℕ), g i := (Finset.sum_subset hsub hz).symm
      _ = g r + g t := Finset.sum_pair hrt
      _ = 2 * mvKer lam t r ^ 2 := by
          have er : mvKer lam r r = 0 := mvKer_self lam r
          have et : mvKer lam t t = 0 := mvKer_self lam t
          have sw : mvKer lam t r = - mvKer lam r t := mvKer_swap lam r t
          simp only [hgdef, er, et]
          rw [sw]; ring
  have hexp : ∑ i ∈ s, mvKer lam r i * mvKer lam t i
      = ∑ i ∈ s, g i + mvKer lam t r * ∑ i ∈ s, (mvKer lam r i - mvKer lam t i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hgdef]; ring
  rw [hexp, hgsum, Finset.sum_sub_distrib, mul_sub]
  ring

/-- The kernel is real-valued, hence self-conjugate. -/
private lemma mvKer_conj (lam : ℕ → ℝ) (r i : ℕ) :
    (starRingEnd ℂ) (mvKer lam r i) = mvKer lam r i := by
  rw [mvKer, map_inv₀, map_sub, Complex.conj_ofReal, Complex.conj_ofReal]

/-- The discrete Hilbert transform `(Au)_i = Σ_r u_r/(λ_r − λ_i)` on all of `s`.  (The `r = i`
term vanishes by the Lean division-by-zero convention, so this equals the `Σ_{r≠i}` form.) -/
private noncomputable def mvAu (s : Finset ℕ) (lam : ℕ → ℝ) (u : ℕ → ℂ) (i : ℕ) : ℂ :=
  ∑ r ∈ s, u r * mvKer lam r i

private lemma conj_Imu (μ : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (Complex.I * (μ : ℂ) * z)
      = - (Complex.I * (μ : ℂ) * (starRingEnd ℂ) z) := by
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **The eigen-collapse (MV `S₃ = S₄`, p. 79).**  Under the eigen-equation `(Au)_i = iμ u_i`,
the two "cot-analog" cross sums coincide.  This is exactly where the genuine cancellation of
the off-diagonal lives — the Schur bound without it loses `log N`. -/
private lemma mvFA_eq_FB (s : Finset ℕ) (lam : ℕ → ℝ) (u : ℕ → ℂ) (μ : ℝ)
    (heig : ∀ i ∈ s, mvAu s lam u i = Complex.I * (μ : ℂ) * u i) :
    ∑ r ∈ s, ∑ t ∈ s,
        u r * (starRingEnd ℂ) (u t) * mvKer lam t r * (∑ i ∈ s, mvKer lam r i)
      = ∑ r ∈ s, ∑ t ∈ s,
        u r * (starRingEnd ℂ) (u t) * mvKer lam t r * (∑ i ∈ s, mvKer lam t i) := by
  have hconjsum : ∀ r : ℕ, ∑ t ∈ s, (starRingEnd ℂ) (u t) * mvKer lam t r
      = (starRingEnd ℂ) (mvAu s lam u r) := by
    intro r
    rw [mvAu, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, mvKer_conj]
  have hrev : ∀ t : ℕ, ∑ r ∈ s, u r * mvKer lam t r = - mvAu s lam u t := by
    intro t
    rw [eq_neg_iff_add_eq_zero, mvAu, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [mvKer_swap lam r t]; ring
  have hL : ∑ r ∈ s, ∑ t ∈ s,
        u r * (starRingEnd ℂ) (u t) * mvKer lam t r * (∑ i ∈ s, mvKer lam r i)
      = - (Complex.I * (μ : ℂ))
          * ∑ r ∈ s, (u r * (starRingEnd ℂ) (u r)) * (∑ i ∈ s, mvKer lam r i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hfac : ∑ t ∈ s, u r * (starRingEnd ℂ) (u t) * mvKer lam t r * (∑ i ∈ s, mvKer lam r i)
        = (u r * (∑ i ∈ s, mvKer lam r i))
            * (∑ t ∈ s, (starRingEnd ℂ) (u t) * mvKer lam t r) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring
    rw [hfac, hconjsum r, heig r hr, conj_Imu]
    ring
  have hR : ∑ r ∈ s, ∑ t ∈ s,
        u r * (starRingEnd ℂ) (u t) * mvKer lam t r * (∑ i ∈ s, mvKer lam t i)
      = - (Complex.I * (μ : ℂ))
          * ∑ r ∈ s, (u r * (starRingEnd ℂ) (u r)) * (∑ i ∈ s, mvKer lam r i) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have hfac : ∑ r ∈ s, u r * (starRingEnd ℂ) (u t) * mvKer lam t r * (∑ i ∈ s, mvKer lam t i)
        = ((starRingEnd ℂ) (u t) * (∑ i ∈ s, mvKer lam t i))
            * (∑ r ∈ s, u r * mvKer lam t r) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
    rw [hfac, hrev t, heig t ht]
    ring
  rw [hL, hR]

/-- The partial-fraction value (the RHS of `mvPF`), as a named function. -/
private noncomputable def mvPfR (s : Finset ℕ) (lam : ℕ → ℝ) (r t : ℕ) : ℂ :=
  mvKer lam t r * (∑ i ∈ s, mvKer lam r i) - mvKer lam t r * (∑ i ∈ s, mvKer lam t i)
    + 2 * mvKer lam t r ^ 2

private lemma mvPF2 (s : Finset ℕ) (lam : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |lam i - lam j|)
    {r t : ℕ} (hr : r ∈ s) (ht : t ∈ s) (hrt : r ≠ t) :
    ∑ i ∈ s, mvKer lam r i * mvKer lam t i = mvPfR s lam r t :=
  mvPF s lam hδ hsep hr ht hrt

/-- **The expansion (MV eqs. (3.3)–(3.9), p. 79, λ-form).**  Under the eigen-equation,
`Σ_i |(Au)_i|²` equals a doubled off-diagonal `2 Σ_{r,t} u_r ū_t / (λ_r − λ_t)²` plus the
diagonal `Σ_r |u_r|² Σ_i 1/(λ_r − λ_i)²`.  The dangerous `S₃ − S₄` cross terms have already
cancelled (`mvFA_eq_FB`); this is where they get discarded. -/
private lemma mvSqSum_eq (s : Finset ℕ) (lam : ℕ → ℝ) (u : ℕ → ℂ) {δ : ℝ} (μ : ℝ)
    (hδ : 0 < δ) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |lam i - lam j|)
    (heig : ∀ i ∈ s, mvAu s lam u i = Complex.I * (μ : ℂ) * u i) :
    ∑ i ∈ s, mvAu s lam u i * (starRingEnd ℂ) (mvAu s lam u i)
      = 2 * (∑ r ∈ s, ∑ t ∈ s, u r * (starRingEnd ℂ) (u t) * mvKer lam t r ^ 2)
        + ∑ r ∈ s, (u r * (starRingEnd ℂ) (u r)) * (∑ i ∈ s, mvKer lam r i * mvKer lam r i) := by
  classical
  have hstep1 : ∑ i ∈ s, mvAu s lam u i * (starRingEnd ℂ) (mvAu s lam u i)
      = ∑ r ∈ s, ∑ t ∈ s,
          u r * (starRingEnd ℂ) (u t) * (∑ i ∈ s, mvKer lam r i * mvKer lam t i) := by
    have e1 : ∀ i ∈ s, mvAu s lam u i * (starRingEnd ℂ) (mvAu s lam u i)
        = ∑ r ∈ s, ∑ t ∈ s,
            (u r * (starRingEnd ℂ) (u t)) * (mvKer lam r i * mvKer lam t i) := by
      intro i _
      simp only [mvAu]
      rw [show (starRingEnd ℂ) (∑ r ∈ s, u r * mvKer lam r i)
            = ∑ t ∈ s, (starRingEnd ℂ) (u t) * mvKer lam t i from by
              rw [map_sum]; exact Finset.sum_congr rfl fun t _ => by rw [map_mul, mvKer_conj]]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => by ring
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
  have hTermII : ∑ r ∈ s, ∑ t ∈ s,
        u r * (starRingEnd ℂ) (u t) * ((∑ i ∈ s, mvKer lam r i * mvKer lam t i) - mvPfR s lam r t)
      = ∑ r ∈ s, (u r * (starRingEnd ℂ) (u r)) * (∑ i ∈ s, mvKer lam r i * mvKer lam r i) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.sum_eq_single_of_mem r hr]
    · have hpf0 : mvPfR s lam r r = 0 := by simp only [mvPfR, mvKer_self]; ring
      rw [hpf0, sub_zero]
    · intro t ht htr
      rw [mvPF2 s lam hδ hsep hr ht (Ne.symm htr), sub_self, mul_zero]
  have hexp : ∑ r ∈ s, ∑ t ∈ s, u r * (starRingEnd ℂ) (u t) * mvPfR s lam r t
      = (∑ r ∈ s, ∑ t ∈ s,
            u r * (starRingEnd ℂ) (u t) * mvKer lam t r * (∑ i ∈ s, mvKer lam r i))
        - (∑ r ∈ s, ∑ t ∈ s,
            u r * (starRingEnd ℂ) (u t) * mvKer lam t r * (∑ i ∈ s, mvKer lam t i))
        + (∑ r ∈ s, ∑ t ∈ s, u r * (starRingEnd ℂ) (u t) * (2 * mvKer lam t r ^ 2)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [mvPfR]; ring
  have hTermI : ∑ r ∈ s, ∑ t ∈ s, u r * (starRingEnd ℂ) (u t) * mvPfR s lam r t
      = 2 * (∑ r ∈ s, ∑ t ∈ s, u r * (starRingEnd ℂ) (u t) * mvKer lam t r ^ 2) := by
    rw [hexp, mvFA_eq_FB s lam u μ heig, sub_self, zero_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hstep1]
  have hcomb : ∑ r ∈ s, ∑ t ∈ s,
        u r * (starRingEnd ℂ) (u t) * (∑ i ∈ s, mvKer lam r i * mvKer lam t i)
      = (∑ r ∈ s, ∑ t ∈ s, u r * (starRingEnd ℂ) (u t) * mvPfR s lam r t)
        + (∑ r ∈ s, ∑ t ∈ s, u r * (starRingEnd ℂ) (u t)
            * ((∑ i ∈ s, mvKer lam r i * mvKer lam t i) - mvPfR s lam r t)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hcomb, hTermI, hTermII]

/-- `K(r,i)² = 1/(λ_r − λ_i)²` as a real cast. -/
private lemma mvKer_sq_cast (lam : ℕ → ℝ) (r i : ℕ) :
    mvKer lam r i * mvKer lam r i = ((1 / (lam r - lam i) ^ 2 : ℝ) : ℂ) := by
  rw [mvKer, ← Complex.ofReal_sub, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  norm_cast
  rw [← mul_inv, one_div, sq]

/-- `‖K(t,r)²‖ = 1/(λ_r − λ_t)²`. -/
private lemma mvKer_sq_norm (lam : ℕ → ℝ) (r t : ℕ) :
    ‖mvKer lam t r ^ 2‖ = 1 / (lam r - lam t) ^ 2 := by
  have hcast : mvKer lam t r ^ 2 = ((1 / (lam r - lam t) ^ 2 : ℝ) : ℂ) := by
    rw [pow_two (mvKer lam t r), mvKer_sq_cast lam t r]
    norm_cast
    rw [show (lam t - lam r) ^ 2 = (lam r - lam t) ^ 2 from by ring]
  rw [hcast]
  exact (Complex.norm_real _).trans (abs_of_nonneg (by positivity))

/-- `z · conj z = ‖z‖²` as a real cast. -/
private lemma mul_conj_cast (z : ℂ) : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The `L²` bound for the transform (given the eigen-equation).**  `Σ_i |(Au)_i|² ≤
(π/δ)² Σ_i |u_i|²`.  Combines `mvSqSum_eq` with the diagonal stone `sep_inv_sq_sum_le` and
the AM-GM symmetrization of the off-diagonal (MV p. 80, the `Σ' ‖x_r − x_s‖⁻²` step). -/
private lemma mvSqSum_le (s : Finset ℕ) (lam : ℕ → ℝ) (u : ℕ → ℂ) {δ : ℝ} (μ : ℝ)
    (hδ : 0 < δ) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |lam i - lam j|)
    (heig : ∀ i ∈ s, mvAu s lam u i = Complex.I * (μ : ℂ) * u i) :
    ∑ i ∈ s, ‖mvAu s lam u i‖ ^ 2 ≤ (Real.pi / δ) ^ 2 * ∑ i ∈ s, ‖u i‖ ^ 2 := by
  classical
  set P := ∑ i ∈ s, ‖u i‖ ^ 2 with hP
  set NA := ∑ i ∈ s, ‖mvAu s lam u i‖ ^ 2 with hNA
  set Ed := ∑ r ∈ s, ‖u r‖ ^ 2 * (∑ t ∈ s, 1 / (lam r - lam t) ^ 2) with hEd
  set W := ∑ r ∈ s, ∑ t ∈ s, ‖u r‖ * ‖u t‖ * (1 / (lam r - lam t) ^ 2) with hW
  set OffC : ℂ := ∑ r ∈ s, ∑ t ∈ s, u r * (starRingEnd ℂ) (u t) * mvKer lam t r ^ 2 with hOffC
  -- diagonal stone
  have hstone : ∀ r ∈ s, ∑ t ∈ s, (1 : ℝ) / (lam r - lam t) ^ 2 ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
    intro r hr
    have hf : ∀ x ∈ s, x ∉ s.erase r → (1 : ℝ) / (lam r - lam x) ^ 2 = 0 := by
      intro x hx hxr
      have hxeq : x = r := by
        by_contra h; exact hxr (Finset.mem_erase.mpr ⟨h, hx⟩)
      rw [hxeq]; simp
    rw [← Finset.sum_subset (Finset.erase_subset r s) hf]
    exact sep_inv_sq_sum_le s lam hδ hsep hr
  -- Ed ≤ (π²/3δ²) P
  have hEd_le : Ed ≤ Real.pi ^ 2 / (3 * δ ^ 2) * P := by
    rw [hEd, hP, Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hstone r hr) (by positivity)
  -- W ≤ Ed (AM-GM + symmetry)
  have hW_le : W ≤ Ed := by
    rw [hW, hEd]
    have hA : ∑ r ∈ s, ∑ t ∈ s, ‖u r‖ ^ 2 * (1 / (lam r - lam t) ^ 2)
        = ∑ r ∈ s, ‖u r‖ ^ 2 * (∑ t ∈ s, 1 / (lam r - lam t) ^ 2) :=
      Finset.sum_congr rfl fun r _ => (Finset.mul_sum _ _ _).symm
    have hB : ∑ r ∈ s, ∑ t ∈ s, ‖u t‖ ^ 2 * (1 / (lam r - lam t) ^ 2)
        = ∑ r ∈ s, ∑ t ∈ s, ‖u r‖ ^ 2 * (1 / (lam r - lam t) ^ 2) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
      rw [show (1 : ℝ) / (lam t - lam r) ^ 2 = 1 / (lam r - lam t) ^ 2 from by
        rw [show (lam t - lam r) ^ 2 = (lam r - lam t) ^ 2 from by ring]]
    calc ∑ r ∈ s, ∑ t ∈ s, ‖u r‖ * ‖u t‖ * (1 / (lam r - lam t) ^ 2)
        ≤ ∑ r ∈ s, ∑ t ∈ s, (‖u r‖ ^ 2 + ‖u t‖ ^ 2) / 2 * (1 / (lam r - lam t) ^ 2) := by
          refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun t _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith [sq_nonneg (‖u r‖ - ‖u t‖), norm_nonneg (u r), norm_nonneg (u t)]
      _ = ∑ r ∈ s, ‖u r‖ ^ 2 * (∑ t ∈ s, 1 / (lam r - lam t) ^ 2) := by
          have hsplit : ∑ r ∈ s, ∑ t ∈ s, (‖u r‖ ^ 2 + ‖u t‖ ^ 2) / 2 * (1 / (lam r - lam t) ^ 2)
              = (1 / 2) * (∑ r ∈ s, ∑ t ∈ s, ‖u r‖ ^ 2 * (1 / (lam r - lam t) ^ 2))
                + (1 / 2) * (∑ r ∈ s, ∑ t ∈ s, ‖u t‖ ^ 2 * (1 / (lam r - lam t) ^ 2)) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun t _ => by ring
          rw [hsplit, hB, hA]; ring
  -- complex identity: ↑NA = 2·OffC + ↑Ed, hence 2·OffC = ↑(NA − Ed)
  have hLHScast : ∑ i ∈ s, mvAu s lam u i * (starRingEnd ℂ) (mvAu s lam u i) = (↑NA : ℂ) := by
    rw [hNA, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => mul_conj_cast _
  have hDiagcast : ∑ r ∈ s, (u r * (starRingEnd ℂ) (u r)) * (∑ i ∈ s, mvKer lam r i * mvKer lam r i)
      = (↑Ed : ℂ) := by
    rw [hEd, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_conj_cast (u r),
      show (∑ i ∈ s, mvKer lam r i * mvKer lam r i)
          = ((∑ i ∈ s, 1 / (lam r - lam i) ^ 2 : ℝ) : ℂ) from by
        rw [Complex.ofReal_sum]; exact Finset.sum_congr rfl fun i _ => mvKer_sq_cast lam r i]
    push_cast; ring
  have hid : (↑NA : ℂ) = 2 * OffC + ↑Ed := by
    rw [← hLHScast, mvSqSum_eq s lam u μ hδ hsep heig, hDiagcast]
  have h2off : (2 : ℂ) * OffC = ((NA - Ed : ℝ) : ℂ) := by
    push_cast; linear_combination -hid
  -- ‖OffC‖ ≤ W
  have hOffW : ‖OffC‖ ≤ W := by
    rw [hOffC, hW]
    calc ‖∑ r ∈ s, ∑ t ∈ s, u r * (starRingEnd ℂ) (u t) * mvKer lam t r ^ 2‖
        ≤ ∑ r ∈ s, ‖∑ t ∈ s, u r * (starRingEnd ℂ) (u t) * mvKer lam t r ^ 2‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ s, ∑ t ∈ s, ‖u r * (starRingEnd ℂ) (u t) * mvKer lam t r ^ 2‖ :=
          Finset.sum_le_sum fun r _ => norm_sum_le _ _
      _ = ∑ r ∈ s, ∑ t ∈ s, ‖u r‖ * ‖u t‖ * (1 / (lam r - lam t) ^ 2) := by
          refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj, mvKer_sq_norm]
  -- NA − Ed ≤ 2·W
  have hNAEd : NA - Ed ≤ 2 * W := by
    have key : NA - Ed ≤ 2 * ‖OffC‖ := by
      have h1 : (|NA - Ed| : ℝ) = ‖(2 : ℂ) * OffC‖ := by
        rw [h2off]; exact (Complex.norm_real _).symm
      have h2 : ‖(2 : ℂ) * OffC‖ = 2 * ‖OffC‖ := by rw [norm_mul]; norm_num
      calc NA - Ed ≤ |NA - Ed| := le_abs_self _
        _ = ‖(2 : ℂ) * OffC‖ := h1
        _ = 2 * ‖OffC‖ := h2
    linarith [key, hOffW]
  -- assemble
  calc NA = Ed + (NA - Ed) := by ring
    _ ≤ Real.pi ^ 2 / (3 * δ ^ 2) * P + 2 * (Real.pi ^ 2 / (3 * δ ^ 2) * P) := by
        have : W ≤ Real.pi ^ 2 / (3 * δ ^ 2) * P := le_trans hW_le hEd_le
        linarith [hEd_le, hNAEd, this]
    _ = (Real.pi / δ) ^ 2 * P := by
        have h : Real.pi ^ 2 / (3 * δ ^ 2) * P + 2 * (Real.pi ^ 2 / (3 * δ ^ 2) * P)
            = Real.pi ^ 2 / δ ^ 2 * P := by ring
        rw [h, div_pow]

/-- **STONE A — the eigenvector bound (MV Theorem 1, §3, λ-form).**  If `u` is an eigenvector
of the discrete Hilbert kernel on `δ`-separated points, i.e.
`Σ_{r≠i} u_r/(λ_r − λ_i) = iμ u_i` for all `i ∈ s`, and `u ≠ 0` on `s`, then `|μ| ≤ π/δ`.
This is the genuine Montgomery–Vaughan content: every eigenvalue of the (skew) kernel is
bounded by `π/δ`, with no `log N` loss.  Elementary — consumes only `sep_inv_sq_sum_le`. -/
theorem hilbert_eigen_bound (s : Finset ℕ) (lam : ℕ → ℝ) (u : ℕ → ℂ) {δ : ℝ} {μ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |lam i - lam j|)
    (heig : ∀ i ∈ s, ∑ r ∈ s.erase i, u r / ((lam r : ℂ) - (lam i : ℂ))
              = Complex.I * (μ : ℂ) * u i)
    (hu : 0 < ∑ i ∈ s, ‖u i‖ ^ 2) :
    |μ| ≤ Real.pi / δ := by
  classical
  -- convert the erase-form eigen-equation to the full-sum form `mvAu`
  have heig' : ∀ i ∈ s, mvAu s lam u i = Complex.I * (μ : ℂ) * u i := by
    intro i hi
    have hdiag0 : u i * mvKer lam i i = 0 := by rw [mvKer_self]; ring
    rw [mvAu, ← Finset.sum_erase s hdiag0,
      show (∑ r ∈ s.erase i, u r * mvKer lam r i)
          = ∑ r ∈ s.erase i, u r / ((lam r : ℂ) - (lam i : ℂ)) from
        Finset.sum_congr rfl fun r _ => by rw [mvKer, ← div_eq_mul_inv]]
    exact heig i hi
  -- the L² bound and the exact value μ²·P
  have hle := mvSqSum_le s lam u μ hδ hsep heig'
  have hEq : ∑ i ∈ s, ‖mvAu s lam u i‖ ^ 2 = μ ^ 2 * ∑ i ∈ s, ‖u i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hnorm : ‖Complex.I * (μ : ℂ) * u i‖ = |μ| * ‖u i‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
      congr 1
      exact Complex.norm_real μ
    rw [heig' i hi, hnorm, mul_pow, sq_abs]
  rw [hEq] at hle
  have hμ2 : μ ^ 2 ≤ (Real.pi / δ) ^ 2 := le_of_mul_le_mul_right hle hu
  have hpiδ : 0 ≤ Real.pi / δ := div_nonneg Real.pi_nonneg hδ.le
  calc |μ| = Real.sqrt (μ ^ 2) := (Real.sqrt_sq_eq_abs μ).symm
    _ ≤ Real.sqrt ((Real.pi / δ) ^ 2) := Real.sqrt_le_sqrt hμ2
    _ = Real.pi / δ := Real.sqrt_sq hpiδ

/-! ## STONE B — the spectral lift

The Hermitian matrix `H a b = i·K(b.val, a.val)` on the index type `↑s`.  Its sesquilinear
form is `star x ⬝ᵥ H *ᵥ x = i·B(x)` where `B` is the Hilbert bilinear form; diagonalizing via
the finite-dimensional spectral theorem and bounding each eigenvalue by `hilbert_eigen_bound`
gives `|B(x)| ≤ (π/δ)‖x‖²`. -/

/-- The Hermitian kernel matrix on `↑s`: `H a b = i·K(b,a) = i/(λ_b − λ_a)`. -/
private noncomputable def mvMat (s : Finset ℕ) (lam : ℕ → ℝ) :
    Matrix {i // i ∈ s} {i // i ∈ s} ℂ := fun a b => Complex.I * mvKer lam b.val a.val

private lemma mvMat_isHermitian (s : Finset ℕ) (lam : ℕ → ℝ) : (mvMat s lam).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b => ?_
  simp only [mvMat, ← starRingEnd_apply, map_mul, Complex.conj_I, mvKer_conj]
  rw [mvKer_swap lam a.val b.val]
  ring

/-- The `mulVec` of the kernel matrix, as `i` times the discrete Hilbert transform. -/
private lemma mvMat_mulVec (s : Finset ℕ) (lam : ℕ → ℝ) (w : {i // i ∈ s} → ℂ)
    (a : {i // i ∈ s}) :
    (mvMat s lam *ᵥ w) a = Complex.I * ∑ c : {i // i ∈ s}, mvKer lam c.val a.val * w c := by
  have hrfl : (mvMat s lam *ᵥ w) a = ∑ c : {i // i ∈ s}, mvMat s lam a c * w c := rfl
  rw [hrfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mvMat]; ring

/-- Extend an `↑s`-indexed vector to `ℕ → ℂ` by zero. -/
private noncomputable def mvExtend (s : Finset ℕ) (b : {i // i ∈ s} → ℂ) : ℕ → ℂ :=
  fun j => if h : j ∈ s then b ⟨j, h⟩ else 0

private lemma mvExtend_val (s : Finset ℕ) (b : {i // i ∈ s} → ℂ) (c : {i // i ∈ s}) :
    mvExtend s b c.val = b c := by
  simp only [mvExtend, c.property, dif_pos]

private lemma mv_sum_reindex {M : Type*} [AddCommMonoid M] (s : Finset ℕ) (f : ℕ → M) :
    ∑ c : {i // i ∈ s}, f c.val = ∑ r ∈ s, f r :=
  (Finset.sum_subtype s (fun _ => Iff.rfl) f).symm

/-- **The eigenvalue bound (Stone A → matrix).**  Every eigenvalue of the Hermitian kernel
matrix `mvMat` is bounded by `π/δ`. -/
private lemma mv_eigenvalue_bound (s : Finset ℕ) (lam : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |lam i - lam j|)
    (k : {i // i ∈ s}) :
    |(mvMat_isHermitian s lam).eigenvalues k| ≤ Real.pi / δ := by
  set hH := mvMat_isHermitian s lam with hHdef
  set d := hH.eigenvalues k with hd
  set b : {i // i ∈ s} → ℂ := ⇑(hH.eigenvectorBasis k) with hb
  set u : ℕ → ℂ := mvExtend s b with hu
  have huv : ∀ c : {i // i ∈ s}, u c.val = b c := fun c => by rw [hu]; exact mvExtend_val s b c
  -- componentwise eigen equation for the raw kernel sum
  have hcomp : ∀ a : {i // i ∈ s},
      ∑ c : {i // i ∈ s}, mvKer lam c.val a.val * b c = -Complex.I * (d : ℂ) * b a := by
    intro a
    have h2 : Complex.I * ∑ c : {i // i ∈ s}, mvKer lam c.val a.val * b c = (d : ℂ) * b a := by
      have hmv := hH.mulVec_eigenvectorBasis k
      have := congrFun (congrArg (fun v => v) hmv) a
      rw [mvMat_mulVec s lam b a] at this
      rw [this, Pi.smul_apply, Complex.real_smul]
    have hI2 : Complex.I * (-Complex.I * (d : ℂ) * b a) = (d : ℂ) * b a := by
      rw [show Complex.I * (-Complex.I * (d : ℂ) * b a)
          = -(Complex.I * Complex.I) * ((d : ℂ) * b a) from by ring, Complex.I_mul_I]
      ring
    exact mul_left_cancel₀ Complex.I_ne_zero (h2.trans hI2.symm)
  -- the eigen-hypothesis (erase form) with μ = -d
  have heig : ∀ i ∈ s, ∑ r ∈ s.erase i, u r / ((lam r : ℂ) - (lam i : ℂ))
      = Complex.I * ((-d : ℝ) : ℂ) * u i := by
    intro i hi
    have hui : u i = b ⟨i, hi⟩ := by rw [hu]; exact mvExtend_val s b ⟨i, hi⟩
    have hfull : ∑ r ∈ s.erase i, u r / ((lam r : ℂ) - (lam i : ℂ))
        = ∑ r ∈ s, u r * mvKer lam r i := by
      have hdiag0 : u i * mvKer lam i i = 0 := by rw [mvKer_self]; ring
      rw [← Finset.sum_erase s hdiag0]
      exact Finset.sum_congr rfl fun r _ => by rw [mvKer, div_eq_mul_inv]
    rw [hfull, ← mv_sum_reindex s (fun r => u r * mvKer lam r i)]
    have hre : ∑ c : {i // i ∈ s}, u c.val * mvKer lam c.val i
        = ∑ c : {i // i ∈ s}, mvKer lam c.val (⟨i, hi⟩ : {i // i ∈ s}).val * b c := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [huv c]; ring
    rw [hre, hcomp ⟨i, hi⟩, hui]
    push_cast; ring
  -- the eigenvector is a unit vector, so the L² norm on s is 1 > 0
  have hupos : 0 < ∑ i ∈ s, ‖u i‖ ^ 2 := by
    have hnorm : ∑ i ∈ s, ‖u i‖ ^ 2 = ∑ c : {i // i ∈ s}, ‖b c‖ ^ 2 := by
      rw [← mv_sum_reindex s (fun r => ‖u r‖ ^ 2)]
      exact Finset.sum_congr rfl fun c _ => by rw [huv c]
    rw [hnorm]
    have h1 : ∑ c : {i // i ∈ s}, ‖b c‖ ^ 2 = ‖hH.eigenvectorBasis k‖ ^ 2 :=
      (EuclideanSpace.norm_sq_eq _).symm
    rw [h1, hH.eigenvectorBasis.orthonormal.1 k]
    norm_num
  have := hilbert_eigen_bound s lam u hδ hsep heig hupos
  rwa [abs_neg] at this

open WithLp in
/-- **The Hermitian quadratic form bound (spectral).**  `‖star x ⬝ᵥ H *ᵥ x‖ ≤ (π/δ)‖x‖²`,
by diagonalizing `H = mvMat` in its orthonormal eigenbasis and bounding each eigenvalue with
`mv_eigenvalue_bound`. -/
private lemma mvForm_bound (s : Finset ℕ) (lam : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |lam i - lam j|)
    (x' : {i // i ∈ s} → ℂ) :
    ‖(star x') ⬝ᵥ (mvMat s lam *ᵥ x')‖ ≤ Real.pi / δ * ∑ c : {i // i ∈ s}, ‖x' c‖ ^ 2 := by
  classical
  set hH := mvMat_isHermitian s lam with hHdef
  set b := hH.eigenvectorBasis with hb
  have hLsym : ((mvMat s lam).toEuclideanLin).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  set y : EuclideanSpace ℂ {i // i ∈ s} := (WithLp.equiv 2 _).symm x' with hy
  have hofy : ofLp y = x' := rfl
  -- the eigen equation for the linear map
  have hLeig : ∀ k, (mvMat s lam).toEuclideanLin (b k) = ((hH.eigenvalues k : ℝ) : ℂ) • (b k) := by
    intro k
    apply WithLp.ofLp_injective 2
    simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, WithLp.ofLp_smul, hb]
    rw [hH.mulVec_eigenvectorBasis k]
    ext a
    simp [Complex.real_smul]
  -- the form equals ⟪y, L y⟫
  have hform : (star x') ⬝ᵥ (mvMat s lam *ᵥ x')
      = inner ℂ y ((mvMat s lam).toEuclideanLin y) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    rw [show ofLp ((mvMat s lam).toEuclideanLin y) = mvMat s lam *ᵥ x' from by
      simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, hofy]]
    rw [hofy, dotProduct_comm]
  -- expand the form over the eigenbasis
  have hexp : inner ℂ y ((mvMat s lam).toEuclideanLin y)
      = ∑ k : {i // i ∈ s}, ((hH.eigenvalues k : ℝ) : ℂ) * ((‖inner ℂ (b k) y‖ ^ 2 : ℝ) : ℂ) := by
    rw [← OrthonormalBasis.sum_inner_mul_inner b y ((mvMat s lam).toEuclideanLin y)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : inner ℂ (b k) ((mvMat s lam).toEuclideanLin y)
        = ((hH.eigenvalues k : ℝ) : ℂ) * inner ℂ (b k) y := by
      rw [← hLsym (b k) y, hLeig k, inner_smul_left, Complex.conj_ofReal]
    rw [h1,
      show inner ℂ y (b k) = (starRingEnd ℂ) (inner ℂ (b k) y) from (inner_conj_symm y (b k)).symm,
      show (starRingEnd ℂ) (inner ℂ (b k) y) * (((hH.eigenvalues k : ℝ) : ℂ) * inner ℂ (b k) y)
        = ((hH.eigenvalues k : ℝ) : ℂ) * (inner ℂ (b k) y * (starRingEnd ℂ) (inner ℂ (b k) y))
        from by ring,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hform, hexp]
  calc ‖∑ k : {i // i ∈ s}, ((hH.eigenvalues k : ℝ) : ℂ) * ((‖inner ℂ (b k) y‖ ^ 2 : ℝ) : ℂ)‖
      ≤ ∑ k : {i // i ∈ s},
          ‖((hH.eigenvalues k : ℝ) : ℂ) * ((‖inner ℂ (b k) y‖ ^ 2 : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ = ∑ k : {i // i ∈ s}, |hH.eigenvalues k| * ‖inner ℂ (b k) y‖ ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul]
        congr 1
        · exact Complex.norm_real _
        · exact (Complex.norm_real _).trans (abs_of_nonneg (by positivity))
    _ ≤ ∑ k : {i // i ∈ s}, (Real.pi / δ) * ‖inner ℂ (b k) y‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_right (mv_eigenvalue_bound s lam hδ hsep k) (by positivity)
    _ = (Real.pi / δ) * ∑ k : {i // i ∈ s}, ‖inner ℂ (b k) y‖ ^ 2 := by rw [Finset.mul_sum]
    _ = (Real.pi / δ) * ∑ c : {i // i ∈ s}, ‖x' c‖ ^ 2 := by
        rw [b.sum_sq_norm_inner_right y, EuclideanSpace.norm_sq_eq]
        congr 1

/-- **STONE B — `MVHilbertUniform` discharged.**  The Montgomery–Vaughan generalized Hilbert
inequality holds unconditionally: `‖Σ_{i,j≠i} x_j x̄_i/(λ_j − λ_i)‖ ≤ (π/δ) Σ‖x_i‖²`. -/
theorem mvHilbertUniform_holds : MVHilbertUniform := by
  intro s lam x δ hδ hsep
  -- the bilinear form is `i` times the Hermitian matrix form
  have hform_eq : (star (fun c : {i // i ∈ s} => x c.val))
        ⬝ᵥ (mvMat s lam *ᵥ (fun c => x c.val))
      = Complex.I * ∑ i ∈ s, ∑ j ∈ s.erase i,
          x j * (starRingEnd ℂ) (x i) / ((lam j : ℂ) - (lam i : ℂ)) := by
    have e1 : (star (fun c : {i // i ∈ s} => x c.val)) ⬝ᵥ (mvMat s lam *ᵥ (fun c => x c.val))
        = Complex.I * ∑ a : {i // i ∈ s},
            (starRingEnd ℂ) (x a.val) * ∑ c : {i // i ∈ s}, mvKer lam c.val a.val * x c.val := by
      rw [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mvMat_mulVec]
      simp only [Pi.star_apply, ← starRingEnd_apply]
      ring
    rw [e1]
    congr 1
    have hLHS : ∑ a : {i // i ∈ s},
          (starRingEnd ℂ) (x a.val) * ∑ c : {i // i ∈ s}, mvKer lam c.val a.val * x c.val
        = ∑ a : {i // i ∈ s},
          (starRingEnd ℂ) (x a.val) * ∑ r ∈ s, mvKer lam r a.val * x r := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mv_sum_reindex s (fun r => mvKer lam r a.val * x r)]
    rw [hLHS,
      mv_sum_reindex s (fun i => (starRingEnd ℂ) (x i) * ∑ r ∈ s, mvKer lam r i * x r)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_erase s (show mvKer lam i i * x i = 0 from by rw [mvKer_self]; ring),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mvKer, div_eq_mul_inv]; ring
  -- transfer the bound through the norm identity and the reindexing of `Σ‖x_i‖²`
  have hnorm : ‖∑ i ∈ s, ∑ j ∈ s.erase i,
        x j * (starRingEnd ℂ) (x i) / ((lam j : ℂ) - (lam i : ℂ))‖
      = ‖(star (fun c : {i // i ∈ s} => x c.val)) ⬝ᵥ (mvMat s lam *ᵥ (fun c => x c.val))‖ := by
    rw [hform_eq, norm_mul, Complex.norm_I, one_mul]
  have hP : ∑ c : {i // i ∈ s}, ‖x c.val‖ ^ 2 = ∑ i ∈ s, ‖x i‖ ^ 2 :=
    mv_sum_reindex s (fun i => ‖x i‖ ^ 2)
  rw [hnorm]
  calc ‖(star (fun c : {i // i ∈ s} => x c.val)) ⬝ᵥ (mvMat s lam *ᵥ (fun c => x c.val))‖
      ≤ Real.pi / δ * ∑ c : {i // i ∈ s}, ‖(fun c : {i // i ∈ s} => x c.val) c‖ ^ 2 :=
        mvForm_bound s lam hδ hsep _
    _ = Real.pi / δ * ∑ i ∈ s, ‖x i‖ ^ 2 := by rw [hP]

/-- **The exit stone.**  `dirichlet_poly_l2_mvt` unconditionally: the `(2T + 20N)` mean-value
bound for Dirichlet polynomials, with the Montgomery–Vaughan hypothesis now discharged. -/
theorem dirichlet_poly_l2_mvt_final (N : ℕ) (a : ℕ → ℂ) (T : ℝ) :
    (∫ t in (-T)..T, ‖dpoly N a t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
  dirichlet_poly_l2_mvt mvHilbertUniform_holds N a T

end Salt.MR
