/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.DerivTestK

/-!
# The van der Corput block estimate for the ζ-phase (`n^{-it}`)

This file applies the landed `k`-th derivative test (`vdC_kth_derivative`,
`Salt/ExpSum/DerivTestK.lean`) to the phase `φ(n) = −(t/2π)·log n`, so that
`eR (φ n)` is the phase of `n^{-it}`.  The consumer is the dyadic ζ-sum
assembly, which composes the per-block bound over `n ∈ (N, 2N]`.

## The bridge: finite differences vs. derivatives

The engine `IsVdCBound` consumes bounds `λ ≤ dk k f ≤ cλ` on the `k`-th
*forward difference*.  For `φ = −(t/2π)·log`, the `k`-th derivative is
`φ^{(k)}(x) = (t/2π)·(−1)^k·(k−1)!/x^k`, monotone in magnitude.  The bridge from
the discrete `dk k φ` to `φ^{(k)}` is the **finite-difference mean value
theorem**, proved here by the elementary route: `dk (k+1) f = dk k (Δf)`
(peel from inside), and one MVT step per level.  The general statement is
`dk_bound_of_deriv_tower`.

## Signs

`φ^{(k)}` alternates sign with `k`.  The test needs `λ ≤ dk k f` with `λ > 0`,
so we feed the phase `(−1)^k·φ` (whose `k`-th difference is positive) and use
`‖∑ eR ((−1)^k·φ)‖ = ‖∑ eR φ‖` (conjugation symmetry when `k` is odd).
-/

namespace Salt.ExpSum

open Real Finset
open scoped ComplexConjugate

/-! ## Section 0 — linearity and the peel-from-inside identity for `dk` -/

/-- `dk` scales by a constant: `dk k (c·g) = c·(dk k g)`. -/
lemma dk_const_mul (c : ℝ) (g : ℤ → ℝ) :
    ∀ (k : ℕ) (m : ℤ), dk k (fun x => c * g x) m = c * dk k g m := by
  intro k
  induction k with
  | zero => intro m; simp
  | succ n ih => intro m; rw [dk_succ, dk_succ, ih (m + 1), ih m]; ring

/-- `dk` negates: `dk k (−g) = −(dk k g)`. -/
lemma dk_neg (g : ℤ → ℝ) (k : ℕ) (m : ℤ) :
    dk k (fun x => -(g x)) m = -(dk k g m) := by
  have h := dk_const_mul (-1) g k m
  simp only [neg_one_mul] at h
  exact h

/-- **Peel from inside.**  The `(k+1)`-th difference is the `k`-th difference of
the first difference `Δf(x) = f(x+1) − f x`.  (`dk_succ` peels from *outside*;
this peels from *inside*, which is what the derivative-tower induction wants.) -/
lemma dk_peel_inside (f : ℤ → ℝ) (k : ℕ) (m : ℤ) :
    dk (k + 1) f m = dk k (fun x => f (x + 1) - f x) m := by
  rw [dk_sub (fun x => f (x + 1)) f k m, dk_shift f 1 k m, dk_succ]

/-! ## Section 1 — the finite-difference mean value theorem

The engine consumes bounds on the `k`-th forward difference `dk k f`.  We bound
`dk k` of a sampled smooth phase by the values of its `k`-th derivative, via the
elementary **finite-difference MVT**: peel `dk (k+1) f = dk k (Δf)` from inside,
and run one MVT step per level.  The derivative tower is carried abstractly as
`Φ : ℕ → ℝ → ℝ` with `HasDerivAt (Φ j) (Φ (j+1) x) x` on the positive reals; the
peeled tower `Δ_yΦ j := Φ j (·+1) − Φ j` satisfies the *same* hypothesis, which
is what makes the induction close. -/

/-- **Finite-difference MVT (bound form).**  For a phase sampled from a smooth
`Φ 0` with derivative tower `Φ` (each `Φ j` differentiating to `Φ (j+1)` on the
positive reals), if `lo ≤ Φ k ≤ hi` throughout `[n, n+k]` then the `k`-th
forward difference `dk k (Φ 0 ∘ cast)` at `n` lies in `[lo, hi]`.  Proved by
induction on `k`: `dk (k+1) = dk k ∘ (peel inside)`, and each MVT step turns the
top-level `Φ k (x+1) − Φ k x` into `Φ (k+1) ξ` for some `ξ ∈ (x, x+1)`. -/
lemma dk_bound_of_deriv_tower (n : ℤ) (hn : 0 < n) (k : ℕ) :
    ∀ (Φ : ℕ → ℝ → ℝ) (lo hi : ℝ),
      (∀ j : ℕ, ∀ x : ℝ, 0 < x → HasDerivAt (Φ j) (Φ (j + 1) x) x) →
      (∀ x : ℝ, (n : ℝ) ≤ x → x ≤ (n : ℝ) + (k : ℝ) → lo ≤ Φ k x) →
      (∀ x : ℝ, (n : ℝ) ≤ x → x ≤ (n : ℝ) + (k : ℝ) → Φ k x ≤ hi) →
      lo ≤ dk k (fun i : ℤ => Φ 0 (i : ℝ)) n ∧ dk k (fun i : ℤ => Φ 0 (i : ℝ)) n ≤ hi := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  induction k with
  | zero =>
      intro Φ lo hi _ hlo hhi
      simp only [dk_zero]
      refine ⟨hlo (n : ℝ) le_rfl (by simp), hhi (n : ℝ) le_rfl (by simp)⟩
  | succ k ih =>
      intro Φ lo hi hderiv hlo hhi
      -- the peeled tower `Ψ j y = Φ j (y+1) − Φ j y`
      set Ψ : ℕ → ℝ → ℝ := fun j y => Φ j (y + 1) - Φ j y with hΨ
      -- peel the goal's difference from inside, and cast-align the argument
      have hAB : (fun x : ℤ => Φ 0 ((↑(x + 1) : ℝ)) - Φ 0 (↑x))
          = (fun i : ℤ => Ψ 0 (↑i)) := by
        funext x; simp only [hΨ]; push_cast; ring
      have key : dk (k + 1) (fun i : ℤ => Φ 0 (↑i)) n = dk k (fun i : ℤ => Ψ 0 (↑i)) n := by
        rw [dk_peel_inside]; rw [hAB]
      rw [key]
      -- the peeled tower satisfies the same derivative hypothesis
      have hderiv' : ∀ j : ℕ, ∀ x : ℝ, 0 < x → HasDerivAt (Ψ j) (Ψ (j + 1) x) x := by
        intro j x hx
        have hxp1 : (0 : ℝ) < x + 1 := by linarith
        have h1 : HasDerivAt (fun y : ℝ => Φ j (y + 1)) (Φ (j + 1) (x + 1)) x :=
          (hderiv j (x + 1) hxp1).comp_add_const x 1
        have h2 : HasDerivAt (Φ j) (Φ (j + 1) x) x := hderiv j x hx
        have h3 : HasDerivAt (fun y : ℝ => Φ j (y + 1) - Φ j y)
            (Φ (j + 1) (x + 1) - Φ (j + 1) x) x := h1.sub h2
        simpa only [hΨ] using h3
      -- the peeled top level `Ψ k` is bounded on `[n, n+k]` by an MVT step
      have hΨbound : ∀ x : ℝ, (n : ℝ) ≤ x → x ≤ (n : ℝ) + (k : ℝ) →
          lo ≤ Ψ k x ∧ Ψ k x ≤ hi := by
        intro x hx1 hx2
        have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hn0 hx1
        have hcont : ContinuousOn (Φ k) (Set.Icc x (x + 1)) := by
          intro y hy
          rw [Set.mem_Icc] at hy
          exact ((hderiv k y (by linarith [hy.1])).continuousAt).continuousWithinAt
        have hmvt := exists_hasDerivAt_eq_slope (Φ k) (Φ (k + 1)) (by linarith : x < x + 1) hcont
          (fun y hy => by rw [Set.mem_Ioo] at hy; exact hderiv k y (by linarith [hy.1]))
        obtain ⟨ξ, hξ, hξeq⟩ := hmvt
        rw [Set.mem_Ioo] at hξ
        rw [show (x + 1) - x = 1 from by ring, div_one] at hξeq
        have hΨeq : Ψ k x = Φ (k + 1) ξ := by simp only [hΨ]; rw [hξeq]
        have hlb : lo ≤ Φ (k + 1) ξ :=
          hlo ξ (by linarith [hξ.1]) (by push_cast; linarith [hξ.2])
        have hub : Φ (k + 1) ξ ≤ hi :=
          hhi ξ (by linarith [hξ.1]) (by push_cast; linarith [hξ.2])
        rw [hΨeq]; exact ⟨hlb, hub⟩
      exact ih Ψ lo hi hderiv'
        (fun x hx1 hx2 => (hΨbound x hx1 hx2).1) (fun x hx1 hx2 => (hΨbound x hx1 hx2).2)

/-! ## Section 2 — the derivative tower of `Real.log`

`logD j` is the `j`-th derivative of `Real.log`: `logD 0 = log`, and for `j ≥ 1`,
`logD (j) x = (−1)^{j−1}·(j−1)!·x^{−j}`.  `logD_hasDerivAt` verifies the tower
relation `HasDerivAt (logD j) (logD (j+1) x) x` on the positive reals. -/

/-- The `j`-th derivative of `Real.log` (as an explicit tower). -/
noncomputable def logD : ℕ → ℝ → ℝ
  | 0 => Real.log
  | (j + 1) => fun x => (-1 : ℝ) ^ j * (j.factorial : ℝ) * x ^ (-(j + 1 : ℤ))

/-- The tower relation: `logD j` differentiates to `logD (j+1)` at every positive
real.  Base: `deriv log = x⁻¹`.  Step: the power rule `hasDerivAt_zpow`, with the
sign/factorial bookkeeping `(−1)^j·j!·(−(j+1)) = (−1)^{j+1}·(j+1)!`. -/
lemma logD_hasDerivAt : ∀ j : ℕ, ∀ x : ℝ, 0 < x → HasDerivAt (logD j) (logD (j + 1) x) x := by
  intro j x hx
  have hxne : x ≠ 0 := ne_of_gt hx
  cases j with
  | zero =>
      have e1 : logD 1 x = x⁻¹ := by
        simp only [logD]; norm_num
      rw [show logD 0 = Real.log from rfl, e1]
      exact Real.hasDerivAt_log hxne
  | succ i =>
      have hz : HasDerivAt (fun y : ℝ => y ^ (-(↑i + 1 : ℤ)))
          ((↑(-(↑i + 1 : ℤ)) : ℝ) * x ^ (-(↑i + 1 : ℤ) - 1)) x :=
        hasDerivAt_zpow _ x (Or.inl hxne)
      have hc := hz.const_mul ((-1 : ℝ) ^ i * (i.factorial : ℝ))
      have hfun : logD (i + 1)
          = fun y : ℝ => (-1 : ℝ) ^ i * (i.factorial : ℝ) * y ^ (-(↑i + 1 : ℤ)) := by
        funext y; simp only [logD]
      have hval : (-1 : ℝ) ^ i * (i.factorial : ℝ)
            * ((↑(-(↑i + 1 : ℤ)) : ℝ) * x ^ (-(↑i + 1 : ℤ) - 1)) = logD (i + 1 + 1) x := by
        simp only [logD]
        rw [show -(↑i + 1 : ℤ) - 1 = -(↑(i + 1) + 1 : ℤ) from by push_cast; ring,
          Nat.factorial_succ]
        push_cast; ring
      rw [hfun, ← hval]
      exact hc

/-! ## Section 3 — the ζ-phase and its `k`-th difference window

`phi t n = −(t/2π)·log n`, so `eR (phi t n)` is the phase of `n^{−it}`.  We feed
the **sign-corrected** phase `(−1)^k·phi` to the engine (its `k`-th difference is
positive); its derivative tower `Ξ j x = (−1)^k·(−(t/2π)·logD j x)` has top level
`Ξ k x = (t/2π)·(k−1)!·x^{−k} > 0`.  `zeta_dk_window` then reads off the uniform
window `[λ, cλ]` on `(N, 2N)` from monotonicity of `x^{−k}`. -/

/-- The ζ-phase: `eR (phi t n) = n^{−it}`'s phase (`= exp(−i·t·log n)`). -/
noncomputable def phi (t : ℝ) (n : ℤ) : ℝ := -(t / (2 * π)) * Real.log (n : ℝ)

/-- The sign-corrected phase tower differentiates one level up (on positives). -/
lemma xi_hasDerivAt (t : ℝ) (s : ℝ) (j : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => s * (-(t / (2 * π)) * logD j y))
      (s * (-(t / (2 * π)) * logD (j + 1) x)) x :=
  ((logD_hasDerivAt j x hx).const_mul (-(t / (2 * π)))).const_mul s

/-- The top level of the sign-corrected tower is the positive `(t/2π)·i!·x^{−(i+1)}`. -/
lemma xi_top_eval (t : ℝ) (i : ℕ) (x : ℝ) :
    (-1 : ℝ) ^ (i + 1) * (-(t / (2 * π)) * logD (i + 1) x)
      = t / (2 * π) * (i.factorial : ℝ) * (x ^ (i + 1))⁻¹ := by
  simp only [logD]
  rw [show (-(↑i + 1 : ℤ)) = -((i + 1 : ℕ) : ℤ) from by push_cast; ring, zpow_neg, zpow_natCast]
  have hss : (-1 : ℝ) ^ (i + 1) * (-1) ^ i = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨i, by ring⟩
  linear_combination (-(t / (2 * π) * (i.factorial : ℝ) * (x ^ (i + 1))⁻¹)) * hss

/-- **The per-`n` window bound.**  For `N < n < 2N`, the `k`-th forward difference
(`k = i+1`) of the sign-corrected ζ-phase lies in the uniform positive window
`[λ, cλ]` with `λ = (t/2π)·i!·(2N+k)^{−k}` and `cλ = (t/2π)·i!·N^{−k}`. -/
lemma zeta_dk_window (t : ℝ) (ht : 0 < t) (i : ℕ) (N : ℕ) (hN : 1 ≤ N)
    (n : ℤ) (hn1 : (N : ℤ) < n) (hn2 : n < 2 * (N : ℤ)) :
    t / (2 * π) * (i.factorial : ℝ) * (((2 * N + (i + 1) : ℕ) : ℝ) ^ (i + 1))⁻¹
        ≤ dk (i + 1) (fun m => (-1 : ℝ) ^ (i + 1) * phi t m) n
      ∧ dk (i + 1) (fun m => (-1 : ℝ) ^ (i + 1) * phi t m) n
        ≤ t / (2 * π) * (i.factorial : ℝ) * ((N : ℝ) ^ (i + 1))⁻¹ := by
  have hnpos : (0 : ℤ) < n := lt_trans (by exact_mod_cast hN) hn1
  have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have htp : (0 : ℝ) < t / (2 * π) := div_pos ht (by positivity)
  have hfacpos : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hcoefpos : (0 : ℝ) < t / (2 * π) * (i.factorial : ℝ) := mul_pos htp hfacpos
  set Φ : ℕ → ℝ → ℝ := fun j x => (-1 : ℝ) ^ (i + 1) * (-(t / (2 * π)) * logD j x) with hΦ
  -- top level value
  have hΦk : ∀ x : ℝ, Φ (i + 1) x = t / (2 * π) * (i.factorial : ℝ) * (x ^ (i + 1))⁻¹ := by
    intro x; simp only [hΦ]; exact xi_top_eval t i x
  -- the sampled phase agrees with the goal's function
  have hΦ0 : (fun m : ℤ => Φ 0 (m : ℝ)) = (fun m : ℤ => (-1 : ℝ) ^ (i + 1) * phi t m) := by
    funext m; simp only [hΦ, phi, logD]
  -- bounds on the top level over `[n, n+(i+1)]`
  have hupper : ∀ x : ℝ, (n : ℝ) ≤ x → x ≤ (n : ℝ) + ((i + 1 : ℕ) : ℝ) →
      Φ (i + 1) x ≤ t / (2 * π) * (i.factorial : ℝ) * ((N : ℝ) ^ (i + 1))⁻¹ := by
    intro x hx1 _
    rw [hΦk x]
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hn0R hx1
    have hNle : (N : ℝ) ≤ x := by
      have : (N : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      linarith
    have hpow : (N : ℝ) ^ (i + 1) ≤ x ^ (i + 1) :=
      pow_le_pow_left₀ (by positivity) hNle _
    have hinv : (x ^ (i + 1))⁻¹ ≤ ((N : ℝ) ^ (i + 1))⁻¹ :=
      inv_anti₀ (by positivity) hpow
    exact mul_le_mul_of_nonneg_left hinv (le_of_lt hcoefpos)
  have hlower : ∀ x : ℝ, (n : ℝ) ≤ x → x ≤ (n : ℝ) + ((i + 1 : ℕ) : ℝ) →
      t / (2 * π) * (i.factorial : ℝ) * (((2 * N + (i + 1) : ℕ) : ℝ) ^ (i + 1))⁻¹
        ≤ Φ (i + 1) x := by
    intro x hx1 hx2
    rw [hΦk x]
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hn0R hx1
    have hxle : x ≤ ((2 * N + (i + 1) : ℕ) : ℝ) := by
      have hn2R : (n : ℝ) ≤ 2 * (N : ℝ) := by
        have : (n : ℝ) < 2 * (N : ℝ) := by exact_mod_cast hn2
        linarith
      push_cast at hx2 ⊢; linarith
    have hpow : x ^ (i + 1) ≤ ((2 * N + (i + 1) : ℕ) : ℝ) ^ (i + 1) :=
      pow_le_pow_left₀ (le_of_lt hxpos) hxle _
    have hinv : (((2 * N + (i + 1) : ℕ) : ℝ) ^ (i + 1))⁻¹ ≤ (x ^ (i + 1))⁻¹ :=
      inv_anti₀ (by positivity) hpow
    exact mul_le_mul_of_nonneg_left hinv (le_of_lt hcoefpos)
  -- invoke the finite-difference MVT bound
  have hbound := dk_bound_of_deriv_tower n hnpos (i + 1) Φ
    (t / (2 * π) * (i.factorial : ℝ) * (((2 * N + (i + 1) : ℕ) : ℝ) ^ (i + 1))⁻¹)
    (t / (2 * π) * (i.factorial : ℝ) * ((N : ℝ) ^ (i + 1))⁻¹)
    (fun j x hx => xi_hasDerivAt t ((-1 : ℝ) ^ (i + 1)) j x hx)
    hlower hupper
  rw [hΦ0] at hbound
  exact hbound

/-! ## Section 4 — sign symmetry and the block estimate

The sum's norm is invariant under negating the phase (`eR (−x) = conj (eR x)`),
so feeding the sign-corrected `(−1)^k·phi` to the engine costs nothing. -/

/-- Negating the phase leaves the exponential-sum norm unchanged (conjugation). -/
lemma norm_sum_eR_neg (s : Finset ℤ) (a : ℤ → ℝ) :
    ‖∑ n ∈ s, eR (-(a n))‖ = ‖∑ n ∈ s, eR (a n)‖ := by
  have h : conj (∑ n ∈ s, eR (a n)) = ∑ n ∈ s, eR (-(a n)) := by
    rw [map_sum]; exact Finset.sum_congr rfl (fun n _ => conj_eR (a n))
  rw [← h, RCLike.norm_conj]

/-- Scaling the phase by `(−1)^k` leaves the exponential-sum norm unchanged:
`(−1)^k = 1` (even) is identity, `(−1)^k = −1` (odd) is conjugation. -/
lemma norm_sum_eR_signed (s : Finset ℤ) (a : ℤ → ℝ) (k : ℕ) :
    ‖∑ n ∈ s, eR ((-1 : ℝ) ^ k * a n)‖ = ‖∑ n ∈ s, eR (a n)‖ := by
  rcases Nat.even_or_odd k with he | ho
  · simp only [he.neg_one_pow, one_mul]
  · simp only [ho.neg_one_pow, neg_one_mul]; exact norm_sum_eR_neg s a

/-- **The van der Corput block estimate for `n^{−it}`.**  For every `k ≥ 2` there
is a constant `C ≥ 1` such that, on any dyadic block `(N, 2N]` with `k ≤ N` and
`t > 0`, writing `λ = (t/2π)·(k−1)!·(2N+k)^{−k}` (the honest lower bound on the
`k`-th-derivative magnitude over the block), `α = 1/(2^k−2)`, `β = 1 − 4/2^k`,
`‖∑_{N<n≤2N} n^{−it}‖ ≤ C·(N·λ^α + N^β·λ^{−α})`.

Route: the `k`-th finite difference of `(−1)^k·(−(t/2π)·log)` lies in the window
`[λ, cλ]` with `c = (2N+k)^k/N^k ≤ 3^k` (`zeta_dk_window` + `dk_bound_of_deriv_tower`),
sign-corrected so it is positive; then the engine `vdC_kth_derivative`; then the
`c`-grade `c^{4/2^k} ≤ (3^k)^{4/2^k}` is absorbed into `C`. -/
theorem zeta_block_vdC (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (t : ℝ) (N : ℕ) (lam : ℝ), 0 < t → k ≤ N →
      lam = t / (2 * π) * ((k - 1).factorial : ℝ) * (((2 * N + k : ℕ) : ℝ) ^ k)⁻¹ →
      ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), eR (phi t n)‖
        ≤ C * ((N : ℝ) * lam ^ (1 / ((2 : ℝ) ^ k - 2))
            + (N : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) * lam ^ (-(1 / ((2 : ℝ) ^ k - 2)))) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  obtain ⟨C₀, hC₀1, hC₀⟩ := vdC_kth_derivative (i + 1) hk
  refine ⟨C₀ * ((3 : ℝ) ^ (i + 1)) ^ (4 / (2 : ℝ) ^ (i + 1)), ?_, ?_⟩
  · have h3 : (1 : ℝ) ≤ ((3 : ℝ) ^ (i + 1)) ^ (4 / (2 : ℝ) ^ (i + 1)) :=
      Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)
    nlinarith [hC₀1, h3, mul_nonneg (sub_nonneg.mpr hC₀1) (sub_nonneg.mpr h3)]
  · intro t N lam ht hkN hlam
    simp only [Nat.add_sub_cancel] at hlam
    have hN1 : 1 ≤ N := by omega
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hNk_pos : (0 : ℝ) < (N : ℝ) ^ (i + 1) := by positivity
    have htp : (0 : ℝ) < t / (2 * π) := div_pos ht (by positivity)
    have hfacpos : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    -- the sign-corrected phase and its window
    set g : ℤ → ℝ := fun m => (-1 : ℝ) ^ (i + 1) * phi t m with hg
    have hlampos : (0 : ℝ) < lam := by
      rw [hlam]
      exact mul_pos (mul_pos htp hfacpos) (inv_pos.mpr (by positivity))
    -- the window ratio `c = (2N+k)^k / N^k`
    set cc : ℝ := ((2 * N + (i + 1) : ℕ) : ℝ) ^ (i + 1) / (N : ℝ) ^ (i + 1) with hcc
    have hnum_pos : (0 : ℝ) < ((2 * N + (i + 1) : ℕ) : ℝ) ^ (i + 1) := by positivity
    have hNle2N : (N : ℝ) ≤ ((2 * N + (i + 1) : ℕ) : ℝ) := by push_cast; linarith
    have hcc1 : 1 ≤ cc := by
      rw [hcc, one_le_div hNk_pos]
      exact pow_le_pow_left₀ (le_of_lt hNR) hNle2N _
    have hcc0 : (0 : ℝ) ≤ cc := le_trans zero_le_one hcc1
    have hratio : ((2 * N + (i + 1) : ℕ) : ℝ) / (N : ℝ) ≤ 3 := by
      rw [div_le_iff₀ hNR]; push_cast
      have : (i : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hkN
      linarith
    have hcc3 : cc ≤ (3 : ℝ) ^ (i + 1) := by
      rw [hcc, ← div_pow]
      exact pow_le_pow_left₀ (by positivity) hratio _
    -- `c · λ = (t/2π)·i!·N^{−k}` (the window's upper bound)
    have hclam : cc * lam = t / (2 * π) * (i.factorial : ℝ) * ((N : ℝ) ^ (i + 1))⁻¹ := by
      rw [hcc, hlam]
      have h1 : ((2 * N + (i + 1) : ℕ) : ℝ) ^ (i + 1) ≠ 0 := ne_of_gt hnum_pos
      have h2 : ((N : ℝ) ^ (i + 1)) ≠ 0 := ne_of_gt hNk_pos
      field_simp
    -- difference bounds from the window lemma
    have hdiff := fun (n : ℤ) (h1 : (N : ℤ) < n) (h2 : n < 2 * (N : ℤ)) =>
      zeta_dk_window t ht i N hN1 n h1 h2
    -- apply the engine
    have hbase := hC₀ g (N : ℤ) (2 * (N : ℤ)) lam cc (by omega) hlampos hcc1
      (fun n h1 h2 => by rw [hlam]; exact (hdiff n h1 h2).1)
      (fun n h1 h2 => by rw [hclam]; exact (hdiff n h1 h2).2)
    -- collapse `(b − a) = N` and rewrite `‖∑ eR g‖ = ‖∑ eR phi‖`
    have hlen : ((2 * (N : ℤ) : ℤ) : ℝ) - ((N : ℤ) : ℝ) = (N : ℝ) := by push_cast; ring
    have hnorm : ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * (N : ℤ)), eR (g n)‖
        = ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * (N : ℤ)), eR (phi t n)‖ := by
      simp only [hg]; exact norm_sum_eR_signed _ (phi t) (i + 1)
    rw [← hnorm]
    refine le_trans hbase ?_
    rw [hlen]
    have hX : (0 : ℝ) ≤ (N : ℝ) * lam ^ (1 / ((2 : ℝ) ^ (i + 1) - 2))
        + (N : ℝ) ^ (1 - 4 / (2 : ℝ) ^ (i + 1)) * lam ^ (-(1 / ((2 : ℝ) ^ (i + 1) - 2))) :=
      add_nonneg
        (mul_nonneg (Nat.cast_nonneg N) (le_of_lt (Real.rpow_pos_of_pos hlampos _)))
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
          (le_of_lt (Real.rpow_pos_of_pos hlampos _)))
    apply mul_le_mul_of_nonneg_right _ hX
    apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hC₀1)
    exact Real.rpow_le_rpow hcc0 hcc3 (by positivity)

/-- **The collapsed block bound.**  In the honest range `λ ∈ [N^{−3+8/2^k}, N^{−1}]`
(equivalently `t ∈ [c₁·N^{k−3+8/2^k}, c₂·N^{k−1}]`, the classical van der Corput
window where the two terms balance), the block estimate collapses to the single
power `‖∑_{N<n≤2N} n^{−it}‖ ≤ C·N^{1−1/(2^k−2)}`.  (Both terms of `zeta_block_vdC`
are `≤ N^{1−α}` on this range: `N·λ^α ≤ N^{1−α}` needs `λ ≤ N^{−1}`, and
`N^β·λ^{−α} ≤ N^{1−α}` needs `λ ≥ N^{−3+8/2^k}`, using `β = 1 − 4/2^k`.) -/
theorem zeta_block_bound (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (t : ℝ) (N : ℕ) (lam : ℝ), 0 < t → k ≤ N →
      lam = t / (2 * π) * ((k - 1).factorial : ℝ) * (((2 * N + k : ℕ) : ℝ) ^ k)⁻¹ →
      (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) ≤ lam → lam ≤ (N : ℝ) ^ (-1 : ℝ) →
      ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), eR (phi t n)‖
        ≤ C * (N : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k - 2)) := by
  obtain ⟨C, hC1, hCb⟩ := zeta_block_vdC k hk
  refine ⟨2 * C, by linarith, ?_⟩
  intro t N lam ht hkN hlam hrlo hrhi
  have hb := hCb t N lam ht hkN hlam
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have h2k : (4 : ℝ) ≤ (2 : ℝ) ^ k := four_le_two_pow k hk
  set p : ℝ := (2 : ℝ) ^ k with hp
  set α : ℝ := 1 / (p - 2) with hαdef
  set β : ℝ := 1 - 4 / p with hβdef
  have hppos : (0 : ℝ) < p := by rw [hp]; positivity
  have hpne : p ≠ 0 := ne_of_gt hppos
  have hp2ne : p - 2 ≠ 0 := ne_of_gt (by linarith [h2k])
  have hα0 : 0 < α := by rw [hαdef]; exact div_pos one_pos (by linarith [h2k])
  have hlampos : (0 : ℝ) < lam := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hrlo
  have hlamnn : (0 : ℝ) ≤ lam := le_of_lt hlampos
  -- term 1:  `N·λ^α ≤ N^{1−α}`  (from `λ ≤ N^{−1}`)
  have hterm1 : (N : ℝ) * lam ^ α ≤ (N : ℝ) ^ (1 - α) := by
    have h1 : lam ^ α ≤ (N : ℝ) ^ (-α) := by
      have hstep := Real.rpow_le_rpow hlamnn hrhi (le_of_lt hα0)
      rwa [← Real.rpow_mul (le_of_lt hNpos), show (-1 : ℝ) * α = -α from by ring] at hstep
    calc (N : ℝ) * lam ^ α ≤ (N : ℝ) * (N : ℝ) ^ (-α) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
      _ = (N : ℝ) ^ (1 - α) := by
          nth_rewrite 1 [← Real.rpow_one (N : ℝ)]
          rw [← Real.rpow_add hNpos, show (1 : ℝ) + (-α) = 1 - α from by ring]
  -- term 2:  `N^β·λ^{−α} ≤ N^{1−α}`  (from `λ ≥ N^{−3+8/p}`)
  have hterm2 : (N : ℝ) ^ β * lam ^ (-α) ≤ (N : ℝ) ^ (1 - α) := by
    set M : ℝ := (N : ℝ) ^ (-3 + 8 / p) with hM
    have hMpos : (0 : ℝ) < M := Real.rpow_pos_of_pos hNpos _
    have hlaminv : lam ^ (-α) ≤ M ^ (-α) := by
      rw [Real.rpow_neg hlamnn, Real.rpow_neg (le_of_lt hMpos)]
      exact inv_anti₀ (Real.rpow_pos_of_pos hMpos _)
        (Real.rpow_le_rpow (le_of_lt hMpos) hrlo (le_of_lt hα0))
    have hstep : (N : ℝ) ^ β * lam ^ (-α) ≤ (N : ℝ) ^ β * M ^ (-α) :=
      mul_le_mul_of_nonneg_left hlaminv (Real.rpow_nonneg (le_of_lt hNpos) _)
    have hcombine : (N : ℝ) ^ β * M ^ (-α) = (N : ℝ) ^ (1 - α) := by
      rw [hM, ← Real.rpow_mul (le_of_lt hNpos), ← Real.rpow_add hNpos]
      congr 1
      rw [hβdef, hαdef]; field_simp; ring
    rw [← hcombine]; exact hstep
  -- combine
  refine le_trans hb ?_
  have hsum : (N : ℝ) * lam ^ α + (N : ℝ) ^ β * lam ^ (-α) ≤ 2 * (N : ℝ) ^ (1 - α) := by
    linarith [hterm1, hterm2]
  calc C * ((N : ℝ) * lam ^ α + (N : ℝ) ^ β * lam ^ (-α))
      ≤ C * (2 * (N : ℝ) ^ (1 - α)) :=
        mul_le_mul_of_nonneg_left hsum (le_trans zero_le_one hC1)
    _ = 2 * C * (N : ℝ) ^ (1 - α) := by ring

end Salt.ExpSum
