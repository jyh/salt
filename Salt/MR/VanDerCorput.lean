/-
Copyright (c) 2026. All rights reserved.
-/
import Salt.ExpSum.ZetaGrowth
import Salt.ExpSum.Strip
import Salt.Vk.Strip

/-!
# The van der Corput socket for L9 (`halasz_integers`)

This file bridges the from-scratch van der Corput / exponential-sum corpus in
`Salt/ExpSum/` (the ζ-phase block bounds `zeta_block_kusmin`, `zeta_block_strip`,
…) to the socket shape demanded by
`Salt.MR.halasz_integers_of_vanDerCorput`, namely

  `hZ : ‖∑_{n=1}^N n^{iu}‖ ≤ Cvdc·(N/√(1+u²) + √(1+|u|)·(1+log(2+|u|)))`
      (`n^{iu} = exp(i·u·log n)`).

## Provenance / the socket–source gap (RESOLVED at the statement level)

VDC's SCOUT found the earlier log-free socket `Cvdc·(N/√(1+u²) + √(1+|u|))`
**strictly stronger than the source**: Montgomery, *Ten Lectures*, p. 141 (33)
proves only

  `Z(it) ≪ N/t + t^{1/2}·log t`,

with a `log t` on the middle term — (34) gives `t^{1/2}` per dyadic block on
`√t ≤ U ≤ t`, and (33) sums `≈ ½log₂ t` such blocks.  The **maestro ruling** (banked)
restates the socket to its honest shape (the `·(1+log(2+|u|))` tail above), which
`Salt.MR.halasz_integers_log_split` / `halasz_integers_of_vanDerCorput` now consume;
the frozen single-log L9 grade survives because the vdC log and the harmonic log live
in *different* terms (they add, never multiply).  The remaining analytic residual is
the middle band `1 ≤ |u| ≤ N²`: the dyadic assembly of the block tiles inherits the
ExpSum track's own **LITT-COVER** residual (no single global `k` covers all dyadic
scales; the second-derivative tile is `√U`-per-block, summing to `√t·log t`).

## What this file lands (Zeno partials — reusable corpus stones)

* `socketTerm_eq_conj_eR` / `norm_socketTerm` — the pointwise bridge
  `exp(i·u·log n) = conj(eR (phi u n))`, so each socket term has norm `1`.
* `norm_socketSum_eq_eR` — norm-level bridge from a socket sum to the corpus
  ζ-phase sum `∑ eR (phi u n)` over any `Finset ℕ`.
* `halasz_socket_small` / `halasz_socket_large` — the honest-log socket,
  **unconditionally**, on the two frequency corners `|u| ≤ 1` (`Cvdc = √2`) and
  `|u| ≥ N²` (`Cvdc = 1`), both via the trivial bound `‖∑‖ ≤ N`.
-/

noncomputable section

open Complex Finset
open scoped Real

namespace Salt.MR

open Salt.ExpSum (eR phi)

/-! ### STONE 1 — the socket ↔ corpus bridge -/

/-- **Pointwise bridge.**  The socket phase `exp(i·u·log n)` is the complex
conjugate of the corpus ζ-phase `eR (phi u n) = exp(−i·u·log n)`. -/
lemma socketTerm_eq_conj_eR (u : ℝ) (n : ℤ) :
    Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))
      = (starRingEnd ℂ) (eR (phi u n)) := by
  rw [Salt.ExpSum.conj_eR]
  unfold eR phi
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  congr 1
  push_cast
  field_simp

/-- Each socket term has unit norm. -/
lemma norm_socketTerm (u : ℝ) (n : ℤ) :
    ‖Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖ = 1 := by
  rw [socketTerm_eq_conj_eR, Complex.norm_conj, Salt.ExpSum.norm_eR]

/-- The ℕ-indexed form of the pointwise bridge. -/
lemma socketTerm_eq_conj_eR_nat (u : ℝ) (n : ℕ) :
    Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))
      = (starRingEnd ℂ) (eR (phi u (n : ℤ))) := by
  have h := socketTerm_eq_conj_eR u (n : ℤ)
  simpa only [Int.cast_natCast] using h

/-- Each socket term has unit norm (ℕ index). -/
lemma norm_socketTerm_nat (u : ℝ) (n : ℕ) :
    ‖Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖ = 1 := by
  rw [socketTerm_eq_conj_eR_nat, Complex.norm_conj, Salt.ExpSum.norm_eR]

/-- **Norm-level bridge (STONE 1).**  Over any `Finset ℕ`, the socket sum and the
corpus ζ-phase sum have equal norm.  This is the reusable hinge that lets every
`Salt/ExpSum/` block bound feed the socket. -/
lemma norm_socketSum_eq_eR (u : ℝ) (S : Finset ℕ) :
    ‖∑ n ∈ S, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      = ‖∑ n ∈ S, eR (phi u (n : ℤ))‖ := by
  have hcongr : ∑ n ∈ S, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))
      = ∑ n ∈ S, (starRingEnd ℂ) (eR (phi u (n : ℤ))) :=
    Finset.sum_congr rfl (fun n _ => socketTerm_eq_conj_eR_nat u n)
  rw [hcongr, ← map_sum, Complex.norm_conj]

/-! ### STONE 2 — the socket on `|u| ≤ 1` (trivial bound, unconditional) -/

/-- The trivial `‖∑‖ ≤ N` bound on the socket sum. -/
lemma norm_socketSum_le_card (u : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ (N : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_congr rfl (fun n (_ : n ∈ Finset.Icc 1 N) => norm_socketTerm_nat u n),
      Finset.sum_const, Nat.card_Icc]
  simp

/-- **STONE 2 — the socket for small frequencies.**  For `|u| ≤ 1` the honest-log
socket holds unconditionally with `Cvdc = √2`, straight from the trivial bound
`‖∑‖ ≤ N` and `√(1+u²) ≤ √2` (the tail's extra `·(1+log(2+|u|))` only enlarges the RHS). -/
theorem halasz_socket_small (N : ℕ) (u : ℝ) (hu : |u| ≤ 1) :
    ‖∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ Real.sqrt 2 * ((N : ℝ) / Real.sqrt (1 + u ^ 2)
          + Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|))) := by
  have hu2 : u ^ 2 ≤ 1 := by
    have := abs_le.mp hu
    nlinarith [this.1, this.2]
  have hden_pos : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hden_le : Real.sqrt (1 + u ^ 2) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt (by linarith)
  -- N ≤ √2 · N/√(1+u²)
  have hN_le : (N : ℝ) ≤ Real.sqrt 2 * ((N : ℝ) / Real.sqrt (1 + u ^ 2)) := by
    rw [mul_div_assoc']
    rw [le_div_iff₀ hden_pos]
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [mul_le_mul_of_nonneg_left hden_le hNnn]
  have h2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have htail_nn : 0 ≤ Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|)) := by
    have hlog : 0 ≤ 1 + Real.log (2 + |u|) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + |u| by have := abs_nonneg u; linarith)
      linarith
    exact mul_nonneg (Real.sqrt_nonneg _) hlog
  calc ‖∑ n ∈ Finset.Icc 1 N,
          Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ (N : ℝ) := norm_socketSum_le_card u N
    _ ≤ Real.sqrt 2 * ((N : ℝ) / Real.sqrt (1 + u ^ 2)) := hN_le
    _ ≤ Real.sqrt 2 * ((N : ℝ) / Real.sqrt (1 + u ^ 2)
          + Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|))) := by
        apply mul_le_mul_of_nonneg_left _ h2nn
        linarith [htail_nn]

/-- **STONE 2b — the socket for large frequencies.**  For `(N:ℝ)² ≤ |u|` the honest-log
socket holds unconditionally with `Cvdc = 1`, straight from the trivial bound `‖∑‖ ≤ N`:
here `N = √(N²) ≤ √(1+|u|) ≤ √(1+|u|)·(1+log(2+|u|))`, so the tail term alone already
dominates the whole sum.  Together with `halasz_socket_small` (`|u| ≤ 1`) this discharges
the socket unconditionally on the two frequency **corners**; the middle band
`1 ≤ |u| ≤ N²` is the dyadic-assembly residual (see the file header). -/
theorem halasz_socket_large (N : ℕ) (u : ℝ) (hu : (N : ℝ) ^ 2 ≤ |u|) :
    ‖∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ 1 * ((N : ℝ) / Real.sqrt (1 + u ^ 2)
          + Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|))) := by
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hN_le : (N : ℝ) ≤ Real.sqrt (1 + |u|) := by
    rw [show (N : ℝ) = Real.sqrt ((N : ℝ) ^ 2) from (Real.sqrt_sq hNnn).symm]
    exact Real.sqrt_le_sqrt (by linarith [abs_nonneg u])
  have hsqrt_nn : 0 ≤ Real.sqrt (1 + |u|) := Real.sqrt_nonneg _
  have hlog : (1 : ℝ) ≤ 1 + Real.log (2 + |u|) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + |u| by have := abs_nonneg u; linarith)
    linarith
  have hhead_nn : 0 ≤ (N : ℝ) / Real.sqrt (1 + u ^ 2) := by positivity
  calc ‖∑ n ∈ Finset.Icc 1 N,
          Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ (N : ℝ) := norm_socketSum_le_card u N
    _ ≤ Real.sqrt (1 + |u|) := hN_le
    _ ≤ Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|)) := le_mul_of_one_le_right hsqrt_nn hlog
    _ ≤ (N : ℝ) / Real.sqrt (1 + u ^ 2)
          + Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|)) := by linarith [hhead_nn]
    _ = 1 * ((N : ℝ) / Real.sqrt (1 + u ^ 2)
          + Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|))) := by rw [one_mul]

/-! ### STONE 3 — the single-dyadic-block halves in socket form (V2)

These are the reusable corpus stones: each Ten Lectures (34) regime, restated in
the socket's `exp(i·u·log n)` shape.  Only the **summation over dyadic blocks**
(which forces the `log` — the socket–source gap above) is left. -/

/-- ℤ-indexed norm bridge (companion to `norm_socketSum_eq_eR`). -/
lemma norm_socketSum_eq_eR_int (u : ℝ) (S : Finset ℤ) :
    ‖∑ n ∈ S, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      = ‖∑ n ∈ S, eR (phi u n)‖ := by
  have hcongr : ∑ n ∈ S, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))
      = ∑ n ∈ S, (starRingEnd ℂ) (eR (phi u n)) :=
    Finset.sum_congr rfl (fun n _ => socketTerm_eq_conj_eR u n)
  rw [hcongr, ← map_sum, Complex.norm_conj]

/-- **STONE 3a — the Kušmin (`U ≥ u`) block, socket form** (Ten Lectures (34),
first case `U > t`).  Consumes `Salt.ExpSum.zeta_block_kusmin`; constant `2π`. -/
theorem socketBlock_kusmin (U : ℕ) (u : ℝ) (hu : 0 < u) (hUu : u ≤ (U : ℝ))
    (hU1 : 1 ≤ U) :
    ‖∑ n ∈ Finset.Ioc (U : ℤ) (2 * U),
        Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ 2 * π * (2 * (U : ℝ) + 1) / u := by
  rw [norm_socketSum_eq_eR_int]
  exact Salt.ExpSum.zeta_block_kusmin u hu U hUu hU1

/-- **STONE 3b — the second-derivative (`u ≍ U` strip) block, socket form** (Ten
Lectures (34), middle case `√t ≤ U ≤ t`).  Consumes `Salt.Vk.zeta_block_strip`;
constant `112`. -/
theorem socketBlock_strip (U : ℕ) (u : ℝ) (hU1 : 1 ≤ U) (hUu : (U : ℝ) ≤ u)
    (huU : u ≤ 27 * π * U) :
    ‖∑ n ∈ Finset.Ioc (U : ℤ) (2 * U),
        Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ 112 * Real.sqrt (U : ℝ) := by
  rw [norm_socketSum_eq_eR_int]
  exact Salt.Vk.zeta_block_strip hU1 hUu huU

end Salt.MR
