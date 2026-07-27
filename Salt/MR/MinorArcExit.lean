/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MinorArcCore
import Salt.MR.BigXiArc

/-!
# S7 L-ladder — the closing stones (L1 the `1/p` strip, L2 the `Λ` conversion, L7 the exit)

The outer shell of the minor-arc ladder: everything between the landed analytic
core (`Salt/MR/MinorArcCore.lean`) and the sealed obligation
`Salt.MR.MinorArcBoundTight` of `Salt/MR/BigXiArc.lean`.  Nothing sealed is
edited; every statement here either *consumes* the core or *feeds* the sealed
reduction `bigXiArcTight_of_minorArcTight`.

## What is here

* **L1 (`norm_sum_Ioc_weighted_le_antitone`, `expSum_eq_indicator`,
  `expSum_abel`)** — the `1/p` strip.  `MinorArcCore.norm_sum_Ioc_weighted_le` is
  stated for *monotone* weights and pays a factor `2`; the weight `1/p` is
  antitone, and the antitone companion pays **nothing**: the honest constant is
  `w M = 1/M`, the weight at the left endpoint, and no more.  (The brief's
  "constant 3" is the *window* conversion `1/M ≤ 3/N`, not the Abel step.)

* **L2 (`sum_lambda_not_prime_le`, `norm_thetaPhase_sub_lambdaPhase`,
  `prime_sum_to_lambda`)** — the `Λ` conversion.  A second Abel summation, this
  time against the antitone weight `1/log n`, is where the *gain* `1/log M`
  comes from; the prime-power defect is mathlib's
  `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` read as
  `∑_{n ≤ J, n not prime} Λ(n) = ψ(J) − θ(J) ≤ 2√J log J`.

* **T1/T2 (`approx_reduced`, `approx_c_form`)** — the approximant, reduced and
  re-shaped.  `exists_large_den_of_minorTight` says nothing about coprimality,
  which every min-sum of the foundation needs; passing to lowest terms is free
  because the tight radius `Q/(qH)` only *improves* as `q` shrinks, and
  `¬NearRatTight` re-fires at the reduced denominator.  `approx_c_form` then
  produces the relaxed shape `|α − a/q| ≤ c/q²` at `c = 1 + Q/H ≤ 2` — the T2
  ceiling cost, paid exactly once.

* **The dyadic consumption (`typeII_dyadic_trunc`, `typeIIBlockBd_le_crude`,
  `typeII_dyadic_sum_le`)** — `MinorArcCore.typeII_dyadic_bound` leaves the
  dyadic index at `range x`, which is *useless*: the top blocks have `E − D ≍ x`
  and there `typeIIBlockBd ≍ x log x`, the trivial bound.  All the saving is in
  the **T6 truncation** `typeII_block_eq_zero`, consumed here: the range is cut
  at `K` with `W²·2^K ≥ x`.  Then `√(A+B+C+D) ≤ √A+√B+√C+√D`, each piece bounded
  uniformly in `k`, and the geometric sum replaced by the crude factor `K`
  (`K ≍ log₂ x`, and there are several powers of `log H` of slack).

* **L6 closed form (`vinoBd`, `vinoBd_mono`, `lambdaPhase_le`)** — the whole
  Vinogradov bound as one explicit expression, monotone in the summation length
  (which is what makes the Abel step's *uniform* partial-sum requirement
  dischargeable).

* **L7 (`expSum_le_vinoBd`, the parameter block, `exists_q_expSum_le`,
  `minorArcBoundTight_of_exitClose`)** — the exit.  Parameters:
  `N = ⌊ε²H⌋`, `M = ⌊ε²H/2⌋`, `W = ⌊⌊√M⌋^{1/2}⌋` (through `Nat.sqrt` twice, so
  the gate `W·W ≤ M` is a kernel fact and no `rpow` arithmetic is needed),
  `K = log₂(N/W²) + 1`, `hi = W·2^K`.

## The `H₀` arms (all absorbed by the target's own `∃ H₀`)

1. `H ≥ 8` — gives `log H ≥ 2`, hence `arcDen B₅ H ≥ 2` for `B₅ ≥ 1`.  This is
   what makes `arcDen ≤ H` a *consequence* rather than a hypothesis: from
   `arcDen < q ≤ H/arcDen + 1` one gets `arcDen² − arcDen < H`, and `arcDen ≥ 2`
   turns that into `arcDen < H`.  So the T5-style log-versus-power gate never
   has to be proved.
2. `H ≥ 4/ε²` — gives `M = ⌊ε²H/2⌋ ≥ 2`, the floor under both Abel steps.
3. `H ≥ H₀(ε)` from the residual `ExitClose` — the exponent close.

## The residual (Zeno)

`ExitClose B₅` is the single named hypothesis left: the explicit statement that
`exitBd ε H q < ε²/log H` for `H` large and `q` in the admissible Dirichlet
range.  `exitBd` is a *closed form* — no `O`, no `o(1)`, no implied constant.
`minorArcBoundTight_twelve_of_close` and `bigXiArcTight_twelve_of_close` are the
frozen targets at `B₅ = 12` modulo exactly that.

Two facts worth recording about the residual.  First, it is comfortably true and
the margin *widens*: the dominant term of `exitBd` is
`≍ (log N)²√(log q)/√W ≍ (log H)^{5/2}/(ε²H)^{1/8}`, against a threshold
`ε²/log H`.  Second, its hypothesis is *vacuous* below `arcDen² ≥ H`, i.e. for
`(log H)^{24} ≥ H` — up to `H ≈ e^{115}`; the minor arc is empty there, so the
analytic content of S7 begins only past that point.
-/

namespace Salt.MR

open Finset ArithmeticFunction Salt.LS Salt.ExpSum Salt.Entropy.Chowla
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ## Shared elementary facts -/

/-- Subadditivity of `√` on nonnegative arguments. -/
theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hkey : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-- Telescoping over `Ico` (the `Ioc`-Abel companion; `MinorArcCore`'s copy is private). -/
private theorem telescope_Ico (w : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ i ∈ Finset.Ico M N, (w i - w (i + 1)) = w M - w N := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hN ih => rw [Finset.sum_Ico_succ_top hN, ih]; ring

/-! ## L1 — the Abel strip of the `1/p` weight

`S_H(α) = ∑_{p ∈ 𝒫_H} (1/p) e(αp)` carries the weight `1/p`, which is *antitone*.
`MinorArcCore.norm_sum_Ioc_weighted_le` is stated for monotone weights and pays a
factor `2`; the antitone companion below pays **nothing** — the honest constant is
`w M`, the value of the weight at the left endpoint, and no more. -/

/-- **The antitone Abel bound.**  An antitone weight, nonnegative at the right
endpoint, against a uniform partial-sum bound `B`, costs exactly `w M`. -/
theorem norm_sum_Ioc_weighted_le_antitone {M N : ℕ} (hMN : M ≤ N) {w : ℕ → ℝ} {A : ℕ → ℂ}
    {B Wt : ℝ} (hB : 0 ≤ B) (hanti : ∀ i, M ≤ i → i < N → w (i + 1) ≤ w i) (hwN : 0 ≤ w N)
    (hwM : w M ≤ Wt)
    (hpart : ∀ K, M ≤ K → K ≤ N → ‖∑ m ∈ Finset.Ioc M K, A m‖ ≤ B) :
    ‖∑ m ∈ Finset.Ioc M N, ((w m : ℝ) : ℂ) * A m‖ ≤ Wt * B := by
  rw [sum_Ioc_abel M w A hMN]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖((w N : ℝ) : ℂ) * (∑ m ∈ Finset.Ioc M N, A m)‖ ≤ w N * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwN]
    exact mul_le_mul_of_nonneg_left (hpart N hMN le_rfl) hwN
  have h2 : ‖∑ i ∈ Finset.Ico M N, ((w (i + 1) - w i : ℝ) : ℂ) * (∑ m ∈ Finset.Ioc M i, A m)‖
      ≤ (w M - w N) * B := by
    calc ‖∑ i ∈ Finset.Ico M N, ((w (i + 1) - w i : ℝ) : ℂ) * (∑ m ∈ Finset.Ioc M i, A m)‖
        ≤ ∑ i ∈ Finset.Ico M N,
            ‖((w (i + 1) - w i : ℝ) : ℂ) * (∑ m ∈ Finset.Ioc M i, A m)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.Ico M N, (w i - w (i + 1)) * B := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          simp only [Finset.mem_Ico] at hi
          have hdi : 0 ≤ w i - w (i + 1) := by
            have := hanti i hi.1 hi.2
            linarith
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
            abs_of_nonneg hdi]
          exact mul_le_mul_of_nonneg_left (hpart i hi.1 (le_of_lt hi.2)) hdi
      _ = (w M - w N) * B := by rw [← Finset.sum_mul, telescope_Ico w hMN]
  have h3 : (w M - w N) * B + w N * B = w M * B := by ring
  have h4 : w M * B ≤ Wt * B := mul_le_mul_of_nonneg_right hwM hB
  linarith

/-- **The unweighted prime phase sum** on the window tail `(M, K]`: the object the
`1/p` strip hands to the `Λ`-conversion. -/
noncomputable def primePhaseSum (α : ℝ) (M K : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc M K, (if Nat.Prime n then eR (α * (n : ℝ)) else 0)

/-- `S_H(α)` written on the interval `(M, N]` with the window folded into an
indicator: the shape Abel summation reads. -/
theorem expSum_eq_indicator {eps : ℚ} {H : ℕ} (α : ℝ) {M N : ℕ}
    (hsub : ∀ p ∈ primeWindow eps H, M < p ∧ p ≤ N) :
    expSum eps H α
      = ∑ n ∈ Finset.Ioc M N,
          ((1 / (n : ℝ) : ℝ) : ℂ) * (if n ∈ primeWindow eps H then eR (α * (n : ℝ)) else 0) := by
  have hcs : expSum eps H α
      = ∑ n ∈ primeWindow eps H,
          (1 / (n : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (n : ℂ)) :=
    Finset.sum_coe_sort (primeWindow eps H)
      (fun n : ℕ => (1 / (n : ℂ)) * Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (n : ℂ)))
  rw [hcs]
  have hstep : (∑ n ∈ primeWindow eps H,
        (1 / (n : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (n : ℂ)))
      = ∑ n ∈ primeWindow eps H,
          ((1 / (n : ℝ) : ℝ) : ℂ) * (if n ∈ primeWindow eps H then eR (α * (n : ℝ)) else 0) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have h1 : ((1 / (p : ℝ) : ℝ) : ℂ) = 1 / ((p : ℕ) : ℂ) := by push_cast; ring
    have h2 : eR (α * ((p : ℕ) : ℝ))
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((p : ℕ) : ℂ)) := by
      rw [eR]; congr 1; push_cast; ring
    rw [if_pos hp, h1, h2]
  rw [hstep]
  refine Finset.sum_subset (fun p hp => Finset.mem_Ioc.mpr (hsub p hp)) (fun n _ hn => ?_)
  rw [if_neg hn, mul_zero]

/-! ## L2 — the prime sum against `Λ`

The unweighted prime phase sum is Abel-summed against the antitone weight
`1/log n`; the resulting log-weighted prime sum differs from the `Λ`-sum only by
the prime-power defect `ψ − θ`, which mathlib bounds by `2√x log x`
(`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`).  The gain of one factor
`1/log M` — the whole point of passing to `Λ` — comes out of the weight. -/

/-- The `Λ`-weighted phase sum `∑_{n ≤ J} Λ(n) e(αn)`: the object the landed
Vinogradov assembly (`vinogradov_lambda`) bounds. -/
noncomputable def lambdaPhase (α : ℝ) (J : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 J, (Λ n : ℂ) * eR (α * (n : ℝ))

/-- The log-weighted *prime* phase sum `∑_{p ≤ J} (log p) e(αp)`. -/
noncomputable def thetaPhase (α : ℝ) (J : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 J, (if Nat.Prime n then (Real.log n : ℂ) else 0) * eR (α * (n : ℝ))

/-- **The prime-power defect.**  `∑_{n ≤ J, n not prime} Λ(n) = ψ(J) − θ(J)`, which
mathlib bounds by `2√J log J`.  This is the only difference between the `Λ`-sum
and the log-weighted prime sum. -/
theorem sum_lambda_not_prime_le (J : ℕ) :
    ∑ n ∈ Finset.Icc 1 J, (Λ n - (if Nat.Prime n then Real.log n else 0))
      ≤ 2 * Real.sqrt J * Real.log J := by
  have hIcc : Finset.Icc 1 J = Finset.Ioc 0 J := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hfl : ⌊(J : ℝ)⌋₊ = J := Nat.floor_natCast J
  have hpsi : Chebyshev.psi (J : ℝ) = ∑ n ∈ Finset.Icc 1 J, Λ n := by
    rw [Chebyshev.psi, hfl, hIcc]
  have hth : Chebyshev.theta (J : ℝ)
      = ∑ n ∈ Finset.Icc 1 J, (if Nat.Prime n then Real.log n else 0) := by
    rw [Chebyshev.theta, hfl, hIcc, Finset.sum_filter]
  rcases Nat.lt_or_ge J 1 with hJ | hJ
  · interval_cases J
    · simp
  · have hJ1 : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
    have habs := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hJ1
    have hle : Chebyshev.psi (J : ℝ) - Chebyshev.theta (J : ℝ) ≤ 2 * Real.sqrt J * Real.log J := by
      have := abs_le.mp habs
      have hsq : Real.sqrt (J : ℝ) = Real.sqrt J := rfl
      rw [hsq] at this
      exact this.2
    rw [hpsi, hth, ← Finset.sum_sub_distrib] at hle
    exact hle

/-- **The `Θ`/`Λ` comparison.**  The two phase sums differ by at most the
prime-power defect. -/
theorem norm_thetaPhase_sub_lambdaPhase (α : ℝ) (J : ℕ) :
    ‖thetaPhase α J - lambdaPhase α J‖ ≤ 2 * Real.sqrt J * Real.log J := by
  rw [thetaPhase, lambdaPhase, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun n : ℕ =>
      Λ n - (if Nat.Prime n then Real.log n else 0)) (fun n _ => ?_)) (sum_lambda_not_prime_le J)
  rw [← sub_mul, norm_mul, norm_eR, mul_one]
  by_cases hp : Nat.Prime n
  · simp only [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self, norm_zero,
      le_refl]
  · simp only [if_neg hp, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg, sub_zero, le_refl]

/-- **L2 — the `Λ`-conversion.**  A uniform bound `B` on the `Λ`-phase sums over
`[M, N]` yields, through Abel summation against `1/log n` and the prime-power
defect, a bound on the unweighted prime phase sum carrying the gain `1/log M`. -/
theorem prime_sum_to_lambda {α : ℝ} {M N : ℕ} (hM : 2 ≤ M) {B : ℝ} (hB : 0 ≤ B)
    (hbd : ∀ J, M ≤ J → J ≤ N → ‖lambdaPhase α J‖ ≤ B) {K : ℕ} (hMK : M ≤ K) (hKN : K ≤ N) :
    ‖primePhaseSum α M K‖ ≤ (2 * B + 4 * Real.sqrt N * Real.log N) / Real.log M := by
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hMN : M ≤ N := le_trans hMK hKN
  have hNR : (2 : ℝ) ≤ (N : ℝ) := le_trans hMR (by exact_mod_cast hMN)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hsqN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  -- the uniform bound on `Θ`
  have hTheta : ∀ J, M ≤ J → J ≤ N → ‖thetaPhase α J‖ ≤ B + 2 * Real.sqrt N * Real.log N := by
    intro J hJ1 hJ2
    have h1 : ‖thetaPhase α J‖ ≤ ‖lambdaPhase α J‖ + ‖thetaPhase α J - lambdaPhase α J‖ := by
      have := norm_add_le (thetaPhase α J - lambdaPhase α J) (lambdaPhase α J)
      simp only [sub_add_cancel] at this
      linarith
    have h2 := norm_thetaPhase_sub_lambdaPhase α J
    have h3 : Real.sqrt J ≤ Real.sqrt N := Real.sqrt_le_sqrt (by exact_mod_cast hJ2)
    have h4 : Real.log J ≤ Real.log N := log_nat_mono hJ2
    have h5 : 0 ≤ Real.log (J : ℝ) := log_nat_nonneg J
    have h6 : 2 * Real.sqrt J * Real.log J ≤ 2 * Real.sqrt N * Real.log N := by
      have : 0 ≤ Real.sqrt (J : ℝ) := Real.sqrt_nonneg _
      nlinarith
    linarith [hbd J hJ1 hJ2]
  -- the weight rewrite
  have hrw : primePhaseSum α M K
      = ∑ n ∈ Finset.Ioc M K, ((1 / Real.log n : ℝ) : ℂ) *
          (if Nat.Prime n then (Real.log n : ℂ) * eR (α * (n : ℝ)) else 0) := by
    rw [primePhaseSum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    simp only [Finset.mem_Ioc] at hn
    by_cases hp : Nat.Prime n
    · rw [if_pos hp, if_pos hp]
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := le_trans hMR (by exact_mod_cast hn.1.le)
      have hlogn : Real.log n ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      have : ((1 / Real.log n : ℝ) : ℂ) * (Real.log n : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, one_div, inv_mul_cancel₀ hlogn, Complex.ofReal_one]
      rw [← mul_assoc, this, one_mul]
    · rw [if_neg hp, if_neg hp, mul_zero]
  rw [hrw]
  have hmain := norm_sum_Ioc_weighted_le_antitone (M := M) (N := K) hMK
    (w := fun n : ℕ => 1 / Real.log n)
    (A := fun n => if Nat.Prime n then (Real.log n : ℂ) * eR (α * (n : ℝ)) else 0)
    (B := 2 * (B + 2 * Real.sqrt N * Real.log N)) (Wt := 1 / Real.log M)
    (by positivity) ?_ (by positivity) le_rfl ?_
  · calc ‖∑ n ∈ Finset.Ioc M K, ((1 / Real.log n : ℝ) : ℂ) *
            (if Nat.Prime n then (Real.log n : ℂ) * eR (α * (n : ℝ)) else 0)‖
        ≤ 1 / Real.log M * (2 * (B + 2 * Real.sqrt N * Real.log N)) := hmain
      _ = (2 * B + 4 * Real.sqrt N * Real.log N) / Real.log M := by field_simp; ring
  · intro i hi _
    have hi2 : (2 : ℝ) ≤ (i : ℝ) := le_trans hMR (by exact_mod_cast hi)
    have hlogi : 0 < Real.log i := Real.log_pos (by linarith)
    exact one_div_le_one_div_of_le hlogi (log_nat_mono (Nat.le_succ i))
  · intro J hMJ hJK
    have hJN : J ≤ N := le_trans hJK hKN
    have hsplit : (∑ n ∈ Finset.Ioc M J,
        (if Nat.Prime n then (Real.log n : ℂ) * eR (α * (n : ℝ)) else 0))
        = thetaPhase α J - thetaPhase α M := by
      have hIcc : ∀ L : ℕ, Finset.Icc 1 L = Finset.Ioc 0 L := by
        intro L; ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
      have hg : (∑ n ∈ Finset.Ioc M J,
            (if Nat.Prime n then (Real.log n : ℂ) * eR (α * (n : ℝ)) else 0))
          = ∑ n ∈ Finset.Ioc M J,
            (if Nat.Prime n then (Real.log n : ℂ) else 0) * eR (α * (n : ℝ)) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        by_cases hp : Nat.Prime n
        · rw [if_pos hp, if_pos hp]
        · rw [if_neg hp, if_neg hp, zero_mul]
      rw [hg, thetaPhase, thetaPhase, eq_sub_iff_add_eq, add_comm, hIcc, hIcc,
        Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMJ]
    rw [hsplit]
    have := hTheta J hMJ hJN
    have := hTheta M le_rfl hMN
    calc ‖thetaPhase α J - thetaPhase α M‖ ≤ ‖thetaPhase α J‖ + ‖thetaPhase α M‖ :=
          norm_sub_le _ _
      _ ≤ 2 * (B + 2 * Real.sqrt N * Real.log N) := by linarith

/-! ## T1/T2 — the approximant, reduced and re-shaped

`exists_large_den_of_minorTight` delivers `a/q` at the tight radius but says
**nothing about coprimality**, which every min-sum statement of the foundation
requires (`Int.gcd a q = 1`).  Passing to lowest terms is free: the tight radius
`Q/(qH)` only *improves* when `q` shrinks, and `¬NearRatTight` re-fires at the
reduced denominator.  This is the T1 stone. -/

/-- **T1 — the coprime reduction.**  A tight-radius approximant may be taken in
lowest terms: `q' ∣ q`, `gcd a' q' = 1`, the tight radius survives, and
`¬NearRatTight` forces `q' > Q` at the *reduced* denominator. -/
theorem approx_reduced {Q : ℝ} {H : ℕ} {α : ℝ} (hH : 0 < H) (hQ : 0 ≤ Q)
    (hnot : ¬ NearRatTight Q H α) {a : ℤ} {q : ℕ} (hq : 0 < q)
    (hd : |α - (a : ℝ) / (q : ℝ)| ≤ Q / ((q : ℝ) * (H : ℝ))) :
    ∃ (a' : ℤ) (q' : ℕ), 0 < q' ∧ q' ≤ q ∧ Int.gcd a' (q' : ℤ) = 1 ∧
      Q < (q' : ℝ) ∧ |α - (a' : ℝ) / (q' : ℝ)| ≤ Q / ((q' : ℝ) * (H : ℝ)) := by
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set g : ℕ := Int.gcd a (q : ℤ) with hgdef
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · exfalso
      rw [hgdef, Int.gcd_eq_zero_iff] at h
      exact absurd h.2 (by exact_mod_cast hq.ne')
    · exact h
  have hgq : (g : ℤ) ∣ (q : ℤ) := Int.gcd_dvd_right a (q : ℤ)
  have hga : (g : ℤ) ∣ a := Int.gcd_dvd_left a (q : ℤ)
  have hgqN : g ∣ q := by exact_mod_cast hgq
  set a' : ℤ := a / (g : ℤ) with ha'def
  set q' : ℕ := q / g with hq'def
  have hq'0 : 0 < q' := Nat.div_pos (Nat.le_of_dvd hq hgqN) hg0
  have hq'q : q' ≤ q := Nat.div_le_self q g
  have hq'R : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'0
  have hcast : ((q' : ℕ) : ℤ) = (q : ℤ) / (g : ℤ) := by
    rw [hq'def]; exact Int.natCast_div q g
  have hcop : Int.gcd a' ((q' : ℕ) : ℤ) = 1 := by
    rw [hcast, ha'def, hgdef]
    exact Int.gcd_div_gcd_div_gcd (by exact_mod_cast hg0)
  -- the rational is unchanged
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg0
  have haR : (a : ℝ) = (a' : ℝ) * (g : ℝ) := by
    have : a' * (g : ℤ) = a := Int.ediv_mul_cancel hga
    exact_mod_cast this.symm
  have hqR' : (q : ℝ) = (q' : ℝ) * (g : ℝ) := by
    have : q' * g = q := Nat.div_mul_cancel hgqN
    exact_mod_cast this.symm
  have heq : (a : ℝ) / (q : ℝ) = (a' : ℝ) / (q' : ℝ) := by
    rw [haR, hqR']
    field_simp
  have hrad : |α - (a' : ℝ) / (q' : ℝ)| ≤ Q / ((q' : ℝ) * (H : ℝ)) := by
    rw [← heq]
    refine hd.trans ?_
    have hle : (q' : ℝ) * (H : ℝ) ≤ (q : ℝ) * (H : ℝ) := by
      have : (q' : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq'q
      nlinarith
    exact div_le_div_of_nonneg_left hQ (by positivity) hle
  refine ⟨a', q', hq'0, hq'q, hcop, ?_, hrad⟩
  by_contra hcon
  push Not at hcon
  exact hnot ⟨a', q', hq'0, hcon, hrad⟩

/-- **T2 — the min-sum input shape.**  The tight radius at a denominator bounded
by the Dirichlet order `H/Q + 1` *is* a relaxed rational approximation
`|α − a/q| ≤ c/q²` at `c = 1 + Q/H ≤ 2`.  The `2` is where the ceiling in
`exists_large_den_of_minorTight` is paid for. -/
theorem approx_c_form {Q : ℝ} {H : ℕ} {α : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (hQ : 0 < Q)
    (hH : 0 < H) (hqle : (q : ℝ) ≤ (H : ℝ) / Q + 1)
    (hd : |α - (a : ℝ) / (q : ℝ)| ≤ Q / ((q : ℝ) * (H : ℝ))) :
    |α - (a : ℝ) / (q : ℝ)| ≤ (1 + Q / (H : ℝ)) / (q : ℝ) ^ 2 := by
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  refine hd.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hstep : Q * (q : ℝ) ≤ (H : ℝ) + Q := by
    have h1 : (q : ℝ) * Q ≤ ((H : ℝ) / Q + 1) * Q := by nlinarith
    rw [add_mul, div_mul_cancel₀ _ hQ.ne', one_mul] at h1
    nlinarith
  have hexp : (1 + Q / (H : ℝ)) * ((q : ℝ) * (H : ℝ)) = ((H : ℝ) + Q) * (q : ℝ) := by
    field_simp
  rw [hexp]
  nlinarith

/-- **L1 — the `1/p` strip.**  Abel summation against the antitone weight `1/n` on
the dyadic window `(M, N]` turns `S_H(α)` into the *unweighted* prime phase sum,
at the honest cost `1/M` (the weight at the left endpoint) and nothing more. -/
theorem expSum_abel {eps : ℚ} {H : ℕ} {α : ℝ} {M N : ℕ} (hM1 : 1 ≤ M) (hMN : M ≤ N)
    (hsub : ∀ p ∈ primeWindow eps H, M < p ∧ p ≤ N)
    (hmem : ∀ n, M < n → n ≤ N → Nat.Prime n → n ∈ primeWindow eps H)
    {B : ℝ} (hB : 0 ≤ B)
    (hpart : ∀ K, M ≤ K → K ≤ N → ‖primePhaseSum α M K‖ ≤ B) :
    ‖expSum eps H α‖ ≤ B / (M : ℝ) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hind : ∀ K, K ≤ N →
      (∑ n ∈ Finset.Ioc M K, (if n ∈ primeWindow eps H then eR (α * (n : ℝ)) else 0))
        = primePhaseSum α M K := by
    intro K hK
    rw [primePhaseSum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    simp only [Finset.mem_Ioc] at hn
    by_cases hp : Nat.Prime n
    · rw [if_pos (hmem n hn.1 (le_trans hn.2 hK) hp), if_pos hp]
    · rw [if_neg hp, if_neg (fun hw => hp (prime_of_mem_primeWindow hw))]
  rw [expSum_eq_indicator α hsub]
  have hmain := norm_sum_Ioc_weighted_le_antitone (M := M) (N := N) hMN
    (w := fun n : ℕ => 1 / (n : ℝ))
    (A := fun n => if n ∈ primeWindow eps H then eR (α * (n : ℝ)) else 0)
    (Wt := 1 / (M : ℝ)) hB ?_ (by positivity) le_rfl ?_
  · calc ‖∑ n ∈ Finset.Ioc M N,
          ((1 / (n : ℝ) : ℝ) : ℂ) * (if n ∈ primeWindow eps H then eR (α * (n : ℝ)) else 0)‖
        ≤ 1 / (M : ℝ) * B := hmain
      _ = B / (M : ℝ) := by ring
  · intro i hi _
    have hi0 : (0 : ℝ) < (i : ℝ) := by
      have : 1 ≤ i := le_trans hM1 hi
      exact_mod_cast this
    have : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact one_div_le_one_div_of_le hi0 this
  · intro K _ hKN
    rw [hind K hKN]
    exact hpart K (by omega) hKN


/-! ## The dyadic Type II consumption

`MinorArcCore.typeII_dyadic_bound` leaves the dyadic index set at the crude
`range x`, which is useless: the top blocks have `E − D ≍ x`, and there
`typeIIBlockBd ≍ x log x` — the trivial bound.  The saving lives entirely in the
**T6 truncation** (`typeII_block_eq_zero`): a block whose left endpoint already
exceeds `x/(V+1)` contributes *nothing*.  So the dyadic range is cut at
`K` with `U·2^K·(V+1) ≥ x`, and the surviving blocks all have `E − D` small.

Then the `√`-sum: `√(A+B+C+D) ≤ √A+√B+√C+√D`, each of the four pieces bounded
uniformly in `k`, and the geometric sum replaced by the crude factor `K` (we have
several powers of `log H` of slack, and `K ≍ log₂ x`). -/

/-- Chopping `(B 0, B K]` into consecutive blocks (`MinorArcCore`'s copy is private). -/
private theorem sum_Ioc_chain_c (F : ℕ → ℂ) {Bl : ℕ → ℕ} (hB : Monotone Bl) (K : ℕ) :
    ∑ d ∈ Finset.Ioc (Bl 0) (Bl K), F d
      = ∑ k ∈ Finset.range K, ∑ d ∈ Finset.Ioc (Bl k) (Bl (k + 1)), F d := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [← Finset.sum_Ioc_consecutive F (hB (Nat.zero_le K)) (hB (Nat.le_succ K)),
        Finset.sum_range_succ, ih]

/-- **The truncated dyadic Type II bound.**  With the cut at `K` — any `K` with
`x ≤ min x (U·2^K)·(V+1)` — the blocks beyond `K` vanish outright, so the dyadic
index set is `range K`, not `range x`.  This is the fact the exponent close runs
on. -/
theorem typeII_dyadic_trunc {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q) (hc : c ≤ 2)
    (hcop : Int.gcd a (q : ℤ) = 1) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2)
    {U V x K : ℕ} (hUx : U ≤ x)
    (hcut : x ≤ min x (U * 2 ^ K) * (V + 1)) :
    ‖∑ d ∈ Finset.Ioc U x, (μ d : ℂ) *
        ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
          (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ))‖
      ≤ ∑ k ∈ Finset.range K,
          typeIIBlockBd q x (min x (U * 2 ^ k)) (min x (U * 2 ^ (k + 1))) := by
  have hstep : ∀ k : ℕ, U * 2 ^ k ≤ U * 2 ^ (k + 1) := fun k =>
    Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))
  have hB : Monotone (fun k => min x (U * 2 ^ k)) :=
    monotone_nat_of_le_succ (fun k => min_le_min le_rfl (hstep k))
  have hB0 : min x (U * 2 ^ 0) = U := by simp only [pow_zero, mul_one]; omega
  have hBKx : min x (U * 2 ^ K) ≤ x := min_le_left _ _
  have hUBK : U ≤ min x (U * 2 ^ K) := by
    have h := hB (Nat.zero_le K)
    simp only [hB0] at h
    exact h
  have hlt : x < (min x (U * 2 ^ K) + 1) * (V + 1) := by
    have hexp : (min x (U * 2 ^ K) + 1) * (V + 1) = min x (U * 2 ^ K) * (V + 1) + (V + 1) := by
      ring
    omega
  have hsplit := Finset.sum_Ioc_consecutive
    (fun d => (μ d : ℂ) *
      ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
        (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ))) hUBK hBKx
  have hzero := typeII_block_eq_zero (V := V) (x := x) (D := min x (U * 2 ^ K)) (E := x) hlt α
  have hchain := sum_Ioc_chain_c
    (fun d => (μ d : ℂ) *
      ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
        (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ))) hB K
  simp only [hB0] at hchain
  rw [← hsplit, hzero, add_zero, hchain]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun k _ => ?_))
  exact typeII_block_bound hq hc hcop happ (hB (Nat.le_succ k))

/-- **The crude block bound.**  With `lo ≤ D + 1` (so the inner range is `≤ x/lo`)
and `E − D ≤ hi`, and the dyadic shape `E ≤ 2D`, the block bound splits into four
`√`-terms, none of which sees `D` or `E` any more. -/
theorem typeIIBlockBd_le_crude {q x D E : ℕ} (hq : 1 ≤ q) {lo hi : ℝ}
    (hlo : 0 < lo) (hDE : D ≤ E) (hE2D : E ≤ 2 * D)
    (hloD : lo ≤ (D : ℝ) + 1) (hhi : (E : ℝ) - (D : ℝ) ≤ hi) :
    typeIIBlockBd q x D E ≤ Real.sqrt 2 * Real.log x *
      (Real.sqrt (7 * hi * (x : ℝ)) + Real.sqrt (6 * (x : ℝ) ^ 2 / (q : ℝ))
        + Real.sqrt (12 * (x : ℝ) ^ 2 * (1 + Real.log q) / lo)
        + Real.sqrt (12 * (x : ℝ) * (q : ℝ) * (1 + Real.log q))) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hLq : (0 : ℝ) ≤ 1 + Real.log q := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq)
    linarith
  have hxR : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hlogx : 0 ≤ Real.log (x : ℝ) := log_nat_nonneg x
  rw [typeIIBlockBd]
  set Δ : ℝ := (E : ℝ) - (D : ℝ) with hΔdef
  set P : ℝ := ((x / (D + 1) : ℕ) : ℝ) with hPdef
  have hDR : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hΔ0 : 0 ≤ Δ := by
    have : (D : ℝ) ≤ (E : ℝ) := by exact_mod_cast hDE
    rw [hΔdef]; linarith
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  have hhi0 : 0 ≤ hi := le_trans hΔ0 hhi
  have hD1 : (0 : ℝ) < (D : ℝ) + 1 := by linarith
  have hPx : P ≤ (x : ℝ) / ((D : ℝ) + 1) := by
    have h := Nat.cast_div_le (α := ℝ) (m := x) (n := D + 1)
    rw [hPdef]
    push_cast at h
    exact h
  have hPlo : P ≤ (x : ℝ) / lo := le_trans hPx (div_le_div_of_nonneg_left hxR hlo hloD)
  have hΔD : Δ ≤ (D : ℝ) := by
    have : (E : ℝ) ≤ 2 * (D : ℝ) := by exact_mod_cast hE2D
    rw [hΔdef]; linarith
  have hprod : Δ * P ≤ (x : ℝ) := by
    calc Δ * P ≤ (D : ℝ) * ((x : ℝ) / ((D : ℝ) + 1)) :=
          mul_le_mul hΔD hPx hP0 hDR
      _ ≤ (x : ℝ) := by
          rw [mul_div_assoc', div_le_iff₀ hD1]
          nlinarith
  have hΔP0 : 0 ≤ Δ * P := mul_nonneg hΔ0 hP0
  -- the five pieces
  have hb1 : Δ * (Δ * P) ≤ hi * (x : ℝ) := mul_le_mul hhi hprod hΔP0 hhi0
  have hb2 : 6 * (Δ * P) ^ 2 / (q : ℝ) ≤ 6 * (x : ℝ) ^ 2 / (q : ℝ) := by
    rw [div_le_div_iff₀ hqR hqR]
    nlinarith [mul_self_le_mul_self hΔP0 hprod]
  have hb3 : 12 * (Δ * P) * P * (1 + Real.log q)
      ≤ 12 * (x : ℝ) ^ 2 * (1 + Real.log q) / lo := by
    have h1 : (Δ * P) * P ≤ (x : ℝ) * ((x : ℝ) / lo) := mul_le_mul hprod hPlo hP0 hxR
    have heq3 : 12 * (x : ℝ) ^ 2 * (1 + Real.log q) / lo
        = 12 * ((x : ℝ) * ((x : ℝ) / lo)) * (1 + Real.log q) := by
      field_simp
    rw [heq3]
    nlinarith [mul_le_mul_of_nonneg_right h1 hLq]
  have hb4 : 6 * Δ * (Δ * P) ≤ 6 * (hi * (x : ℝ)) := by nlinarith
  have hb5 : 12 * (Δ * P) * (q : ℝ) * (1 + Real.log q)
      ≤ 12 * (x : ℝ) * (q : ℝ) * (1 + Real.log q) := by
    nlinarith [mul_nonneg hqR.le hLq]
  set A : ℝ := 7 * hi * (x : ℝ) with hAdef
  set Bq : ℝ := 6 * (x : ℝ) ^ 2 / (q : ℝ) with hBdef
  set Cq : ℝ := 12 * (x : ℝ) ^ 2 * (1 + Real.log q) / lo with hCdef
  set Dq : ℝ := 12 * (x : ℝ) * (q : ℝ) * (1 + Real.log q) with hDdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0' : 0 ≤ Bq := by rw [hBdef]; positivity
  have hC0 : 0 ≤ Cq := by rw [hCdef]; positivity
  have hD0 : 0 ≤ Dq := by rw [hDdef]; positivity
  have hexp : Δ * (Real.log (x : ℝ) * Real.log (x : ℝ) *
        (2 * P * (Δ + (P / (q : ℝ) + 1) * (6 * Δ + 12 * (q : ℝ) * (1 + Real.log q)))))
      = Real.log (x : ℝ) ^ 2 * (2 * (Δ * (Δ * P) + 6 * (Δ * P) ^ 2 / (q : ℝ)
          + 12 * (Δ * P) * P * (1 + Real.log q) + 6 * Δ * (Δ * P)
          + 12 * (Δ * P) * (q : ℝ) * (1 + Real.log q))) := by
    field_simp
    ring
  have hinner : Δ * (Δ * P) + 6 * (Δ * P) ^ 2 / (q : ℝ)
      + 12 * (Δ * P) * P * (1 + Real.log q) + 6 * Δ * (Δ * P)
      + 12 * (Δ * P) * (q : ℝ) * (1 + Real.log q) ≤ A + Bq + Cq + Dq := by
    rw [hAdef]; linarith
  have hmain : Δ * (Real.log (x : ℝ) * Real.log (x : ℝ) *
        (2 * P * (Δ + (P / (q : ℝ) + 1) * (6 * Δ + 12 * (q : ℝ) * (1 + Real.log q)))))
      ≤ Real.log (x : ℝ) ^ 2 * (2 * (A + Bq + Cq + Dq)) := by
    rw [hexp]
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  calc Real.sqrt (Δ * (Real.log (x : ℝ) * Real.log (x : ℝ) *
        (2 * P * (Δ + (P / (q : ℝ) + 1) * (6 * Δ + 12 * (q : ℝ) * (1 + Real.log q))))))
      ≤ Real.sqrt (Real.log (x : ℝ) ^ 2 * (2 * (A + Bq + Cq + Dq))) :=
        Real.sqrt_le_sqrt hmain
    _ = Real.log (x : ℝ) * Real.sqrt (2 * (A + Bq + Cq + Dq)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlogx]
    _ = Real.log (x : ℝ) * (Real.sqrt 2 * Real.sqrt (A + Bq + Cq + Dq)) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ Real.log (x : ℝ) *
          (Real.sqrt 2 * (Real.sqrt A + Real.sqrt Bq + Real.sqrt Cq + Real.sqrt Dq)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)) hlogx
        calc Real.sqrt (A + Bq + Cq + Dq)
            ≤ Real.sqrt (A + Bq + Cq) + Real.sqrt Dq :=
              sqrt_add_le_sqrt_add_sqrt (by linarith) hD0
          _ ≤ (Real.sqrt (A + Bq) + Real.sqrt Cq) + Real.sqrt Dq := by
              have := sqrt_add_le_sqrt_add_sqrt (a := A + Bq) (b := Cq) (by linarith) hC0
              linarith
          _ ≤ ((Real.sqrt A + Real.sqrt Bq) + Real.sqrt Cq) + Real.sqrt Dq := by
              have := sqrt_add_le_sqrt_add_sqrt (a := A) (b := Bq) hA0 hB0'
              linarith
    _ = Real.sqrt 2 * Real.log (x : ℝ) *
          (Real.sqrt A + Real.sqrt Bq + Real.sqrt Cq + Real.sqrt Dq) := by ring


/-- **The crude dyadic sum.**  Every surviving block obeys the same four-term
bound, so the truncated sum is at most `K` times it. -/
theorem typeII_dyadic_sum_le {q x U K : ℕ} (hq : 1 ≤ q) (hU : 1 ≤ U) (hUx : U ≤ x) {hi : ℝ}
    (hhi : ∀ k, k < K →
      ((min x (U * 2 ^ (k + 1)) : ℕ) : ℝ) - ((min x (U * 2 ^ k) : ℕ) : ℝ) ≤ hi) :
    ∑ k ∈ Finset.range K, typeIIBlockBd q x (min x (U * 2 ^ k)) (min x (U * 2 ^ (k + 1)))
      ≤ (K : ℝ) * (Real.sqrt 2 * Real.log x *
        (Real.sqrt (7 * hi * (x : ℝ)) + Real.sqrt (6 * (x : ℝ) ^ 2 / (q : ℝ))
          + Real.sqrt (12 * (x : ℝ) ^ 2 * (1 + Real.log q) / (U : ℝ))
          + Real.sqrt (12 * (x : ℝ) * (q : ℝ) * (1 + Real.log q)))) := by
  have hUR : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  calc ∑ k ∈ Finset.range K, typeIIBlockBd q x (min x (U * 2 ^ k)) (min x (U * 2 ^ (k + 1)))
      ≤ ∑ _k ∈ Finset.range K, (Real.sqrt 2 * Real.log x *
          (Real.sqrt (7 * hi * (x : ℝ)) + Real.sqrt (6 * (x : ℝ) ^ 2 / (q : ℝ))
            + Real.sqrt (12 * (x : ℝ) ^ 2 * (1 + Real.log q) / (U : ℝ))
            + Real.sqrt (12 * (x : ℝ) * (q : ℝ) * (1 + Real.log q)))) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        have hpow : U * 2 ^ k ≤ U * 2 ^ (k + 1) :=
          Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))
        have hDE : min x (U * 2 ^ k) ≤ min x (U * 2 ^ (k + 1)) := min_le_min le_rfl hpow
        have hE2D : min x (U * 2 ^ (k + 1)) ≤ 2 * min x (U * 2 ^ k) := by
          rcases le_or_gt x (U * 2 ^ k) with h | h
          · have h1 : min x (U * 2 ^ k) = x := min_eq_left h
            have h2 : min x (U * 2 ^ (k + 1)) ≤ x := min_le_left _ _
            omega
          · have h1 : min x (U * 2 ^ k) = U * 2 ^ k := min_eq_right h.le
            have h2 : min x (U * 2 ^ (k + 1)) ≤ U * 2 ^ (k + 1) := min_le_right _ _
            have h3 : U * 2 ^ (k + 1) = 2 * (U * 2 ^ k) := by ring
            omega
        have hUD : U ≤ min x (U * 2 ^ k) :=
          le_min hUx (Nat.le_mul_of_pos_right U (by positivity))
        have hloD : (U : ℝ) ≤ ((min x (U * 2 ^ k) : ℕ) : ℝ) + 1 := by
          have : (U : ℝ) ≤ ((min x (U * 2 ^ k) : ℕ) : ℝ) := by exact_mod_cast hUD
          linarith
        exact typeIIBlockBd_le_crude (lo := (U : ℝ)) (hi := hi) hq hUR hDE hE2D hloD (hhi k hk)
    _ = (K : ℝ) * (Real.sqrt 2 * Real.log x *
          (Real.sqrt (7 * hi * (x : ℝ)) + Real.sqrt (6 * (x : ℝ) ^ 2 / (q : ℝ))
            + Real.sqrt (12 * (x : ℝ) ^ 2 * (1 + Real.log q) / (U : ℝ))
            + Real.sqrt (12 * (x : ℝ) * (q : ℝ) * (1 + Real.log q)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## L6, closed form — the Vinogradov bound with every piece explicit -/

/-- **The closed-form Vinogradov bound** at `U = V = W`, dyadic cut at `K`, block
width bound `hi`: head + two Type I min-sum outputs + the crude dyadic sum. -/
noncomputable def vinoBd (q x W K : ℕ) (hi : ℝ) : ℝ :=
  (W : ℝ) * Real.log W
  + (2 * Real.log x * (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * (W : ℝ)))
        + 12 * ((W : ℝ) + (q : ℝ)) * (1 + Real.log q))
      + Real.log ((W * W : ℕ) : ℝ) *
        (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * ((W * W : ℕ) : ℝ)))
          + 12 * (((W * W : ℕ) : ℝ) + (q : ℝ)) * (1 + Real.log q)))
  + (K : ℝ) * (Real.sqrt 2 * Real.log x *
      (Real.sqrt (7 * hi * (x : ℝ)) + Real.sqrt (6 * (x : ℝ) ^ 2 / (q : ℝ))
        + Real.sqrt (12 * (x : ℝ) ^ 2 * (1 + Real.log q) / (W : ℝ))
        + Real.sqrt (12 * (x : ℝ) * (q : ℝ) * (1 + Real.log q))))

/-- `vinoBd` is monotone in the summation length: every piece grows with `x`. -/
theorem vinoBd_mono {q W K : ℕ} {hi : ℝ} (hq : 1 ≤ q) (hhi : 0 ≤ hi) {x y : ℕ}
    (hxy : x ≤ y) : vinoBd q x W K hi ≤ vinoBd q y W K hi := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hxyR : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hlog : Real.log (x : ℝ) ≤ Real.log (y : ℝ) := log_nat_mono hxy
  have hlog0 : (0 : ℝ) ≤ Real.log (x : ℝ) := log_nat_nonneg x
  have hLq : (0 : ℝ) ≤ 1 + Real.log q := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq)
    linarith
  have hlW : (0 : ℝ) ≤ 1 + Real.log (2 * (W : ℝ)) := by
    have : (0 : ℝ) ≤ Real.log (2 * (W : ℝ)) := by
      rcases Nat.eq_zero_or_pos W with h | h
      · simp [h]
      · refine Real.log_nonneg ?_
        have : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast h
        linarith
    linarith
  have hlW2 : (0 : ℝ) ≤ 1 + Real.log (2 * ((W * W : ℕ) : ℝ)) := by
    have : (0 : ℝ) ≤ Real.log (2 * ((W * W : ℕ) : ℝ)) := by
      rcases Nat.eq_zero_or_pos (W * W) with h | h
      · simp [h]
      · refine Real.log_nonneg ?_
        have : (1 : ℝ) ≤ ((W * W : ℕ) : ℝ) := by exact_mod_cast h
        linarith
    linarith
  have hlogWW : (0 : ℝ) ≤ Real.log ((W * W : ℕ) : ℝ) := log_nat_nonneg _
  unfold vinoBd
  gcongr

/-- **L6 in closed form.**  `vinogradov_lambda` with the Type II sum consumed by
the truncated dyadic bound and its crude four-term estimate. -/
theorem lambdaPhase_le {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q) (hc : c ≤ 2)
    (hcop : Int.gcd a (q : ℤ) = 1) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2)
    {W x K : ℕ} (hW : 1 ≤ W) (hWx : W * W ≤ x)
    (hcut : x ≤ min x (W * 2 ^ K) * (W + 1)) {hi : ℝ}
    (hhi : ∀ k, k < K →
      ((min x (W * 2 ^ (k + 1)) : ℕ) : ℝ) - ((min x (W * 2 ^ k) : ℕ) : ℝ) ≤ hi) :
    ‖lambdaPhase α x‖ ≤ vinoBd q x W K hi := by
  have hWle : W ≤ x := le_trans (Nat.le_mul_of_pos_left W hW) hWx
  have hraw := vinogradov_lambda (α := α) (a := a) (q := q) (c := c) hq hc hcop happ
    (U := W) (V := W) (x := x) hW hW hWle
  have hdy := le_trans (typeII_dyadic_trunc hq hc hcop happ (U := W) (V := W) hWle hcut)
    (typeII_dyadic_sum_le hq hW hWle hhi)
  rw [lambdaPhase, vinoBd]
  linarith


/-! ## L7 — the exit

L1 ∘ L2 ∘ L6, then the parameter instantiation, then the exponent close. -/

/-- **The assembled minor-arc estimate.**  The `1/p` strip, the `Λ` conversion and
the closed-form Vinogradov bound composed, with every window and parameter gate
carried explicitly. -/
theorem expSum_le_vinoBd {eps : ℚ} {H : ℕ} {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ}
    (hq : 1 ≤ q) (hc : c ≤ 2) (hcop : Int.gcd a (q : ℤ) = 1)
    (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2)
    {M N W K : ℕ} {hi : ℝ} (hM2 : 2 ≤ M) (hMN : M ≤ N) (hW : 1 ≤ W) (hWM : W * W ≤ M)
    (hhi0 : 0 ≤ hi)
    (hcut : ∀ J, M ≤ J → J ≤ N → J ≤ min J (W * 2 ^ K) * (W + 1))
    (hhi : ∀ J, M ≤ J → J ≤ N → ∀ k, k < K →
      ((min J (W * 2 ^ (k + 1)) : ℕ) : ℝ) - ((min J (W * 2 ^ k) : ℕ) : ℝ) ≤ hi)
    (hsub : ∀ p ∈ primeWindow eps H, M < p ∧ p ≤ N)
    (hmem : ∀ n, M < n → n ≤ N → Nat.Prime n → n ∈ primeWindow eps H) :
    ‖expSum eps H α‖
      ≤ (2 * vinoBd q N W K hi + 4 * Real.sqrt N * Real.log N) / ((M : ℝ) * Real.log M) := by
  have hbd : ∀ J, M ≤ J → J ≤ N → ‖lambdaPhase α J‖ ≤ vinoBd q N W K hi := by
    intro J hJ1 hJ2
    exact le_trans (lambdaPhase_le hq hc hcop happ hW (le_trans hWM hJ1)
      (hcut J hJ1 hJ2) (hhi J hJ1 hJ2)) (vinoBd_mono hq hhi0 hJ2)
  have hBv0 : 0 ≤ vinoBd q N W K hi := le_trans (norm_nonneg _) (hbd N hMN le_rfl)
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by linarith)
  have hlogN : 0 ≤ Real.log (N : ℝ) := log_nat_nonneg N
  have hnum : 0 ≤ 2 * vinoBd q N W K hi + 4 * Real.sqrt N * Real.log N := by
    have h4 : 0 ≤ 4 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) :=
      mul_nonneg (by positivity) hlogN
    linarith
  have hB0 : 0 ≤ (2 * vinoBd q N W K hi + 4 * Real.sqrt N * Real.log N) / Real.log M :=
    div_nonneg hnum hlogM.le
  have hfin := expSum_abel (eps := eps) (H := H) (α := α) (M := M) (N := N)
    (by omega) hMN hsub hmem hB0
    (fun J hJ1 hJ2 => prime_sum_to_lambda hM2 hBv0 hbd hJ1 hJ2)
  calc ‖expSum eps H α‖
      ≤ (2 * vinoBd q N W K hi + 4 * Real.sqrt N * Real.log N) / Real.log M / (M : ℝ) := hfin
    _ = (2 * vinoBd q N W K hi + 4 * Real.sqrt N * Real.log N) / ((M : ℝ) * Real.log M) := by
        rw [div_div, mul_comm (Real.log (M : ℝ))]

/-! ### The parameter instantiation -/

/-- The window top `⌊ε²H⌋` — the upper endpoint of `𝒫_H`, verbatim from
`primeWindow`. -/
noncomputable def winTop (eps : ℚ) (H : ℕ) : ℕ := ⌊eps ^ 2 * (H : ℚ)⌋₊

/-- The window bottom `⌊ε²H/2⌋` — one below the lower endpoint of `𝒫_H`. -/
noncomputable def winBot (eps : ℚ) (H : ℕ) : ℕ := ⌊(eps : ℝ) ^ 2 * (H : ℝ) / 2⌋₊

/-- The Vaughan parameter `W = ⌊(ε²H/2)^{1/4}⌋`, taken through `Nat.sqrt` twice so
that the gate `W·W ≤ M` is a kernel fact and no `rpow` arithmetic is needed. -/
noncomputable def vaughanW (eps : ℚ) (H : ℕ) : ℕ := Nat.sqrt (Nat.sqrt (winBot eps H))

/-- The dyadic cut: the least `K` with `W²·2^K ≥ N`, so the T6 truncation fires. -/
noncomputable def dyadicK (eps : ℚ) (H : ℕ) : ℕ :=
  Nat.log 2 (winTop eps H / (vaughanW eps H * vaughanW eps H)) + 1

/-- The block-width cap `W·2^K`. -/
noncomputable def dyadicHi (eps : ℚ) (H : ℕ) : ℝ :=
  ((vaughanW eps H * 2 ^ dyadicK eps H : ℕ) : ℝ)

/-- **The exit bound** — the fully explicit right-hand side of the assembled
minor-arc estimate at the S7 parameters.  No `O`, no `o(1)`, no implied
constant. -/
noncomputable def exitBd (eps : ℚ) (H q : ℕ) : ℝ :=
  (2 * vinoBd q (winTop eps H) (vaughanW eps H) (dyadicK eps H) (dyadicHi eps H)
      + 4 * Real.sqrt (winTop eps H) * Real.log (winTop eps H))
    / ((winBot eps H : ℝ) * Real.log (winBot eps H))


/-! ### The window and parameter gates -/

/-- The window bottom clears `2` once `H ≥ 4/ε²`. -/
theorem two_le_winBot {eps : ℚ} (heps : 0 < eps) {H : ℕ}
    (hH : (4 : ℝ) / (eps : ℝ) ^ 2 ≤ (H : ℝ)) : 2 ≤ winBot eps H := by
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hne : ((eps : ℝ) ^ 2) ≠ 0 := by positivity
  have heq : (eps : ℝ) ^ 2 * (4 / (eps : ℝ) ^ 2) = 4 := by field_simp
  have h4 : (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    have := mul_le_mul_of_nonneg_left hH (le_of_lt (by positivity : (0 : ℝ) < (eps : ℝ) ^ 2))
    linarith [heq]
  rw [winBot]
  refine Nat.le_floor ?_
  push_cast
  linarith

/-- The window bottom sits below the window top. -/
theorem winBot_le_winTop {eps : ℚ} (heps : 0 < eps) (H : ℕ) : winBot eps H ≤ winTop eps H := by
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have h1 : ((winBot eps H : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 := by
    rw [winBot]; exact Nat.floor_le (by positivity)
  have h2 : ((winBot eps H : ℕ) : ℝ) ≤ ((eps ^ 2 * (H : ℚ) : ℚ) : ℝ) := by
    push_cast
    nlinarith [sq_nonneg ((eps : ℝ))]
  rw [winTop]
  exact Nat.le_floor (by exact_mod_cast h2)

/-- `W ≥ 1` once the window bottom is positive. -/
theorem one_le_vaughanW {eps : ℚ} {H : ℕ} (h : 1 ≤ winBot eps H) : 1 ≤ vaughanW eps H := by
  have h1 : 1 ≤ Nat.sqrt (winBot eps H) := Nat.le_sqrt.mpr (by simpa using h)
  rw [vaughanW]
  exact Nat.le_sqrt.mpr (by simpa using h1)

/-- The Vaughan gate `W·W ≤ M`, by construction. -/
theorem vaughanW_sq_le (eps : ℚ) (H : ℕ) :
    vaughanW eps H * vaughanW eps H ≤ winBot eps H :=
  le_trans (Nat.sqrt_le _) (Nat.sqrt_le_self _)

/-- **The dyadic cut fires**: `N ≤ W²·2^K` at `K = dyadicK`, which is exactly the
condition under which the T6 truncation kills every block beyond `K`. -/
theorem winTop_le_pow {eps : ℚ} {H : ℕ} (hW : 1 ≤ vaughanW eps H) :
    winTop eps H ≤ vaughanW eps H * vaughanW eps H * 2 ^ dyadicK eps H := by
  have hWW : 0 < vaughanW eps H * vaughanW eps H := Nat.mul_pos hW hW
  have h1 : winTop eps H < (winTop eps H / (vaughanW eps H * vaughanW eps H) + 1)
      * (vaughanW eps H * vaughanW eps H) :=
    (Nat.div_lt_iff_lt_mul hWW).mp (Nat.lt_succ_self _)
  have h2 : winTop eps H / (vaughanW eps H * vaughanW eps H) < 2 ^ dyadicK eps H := by
    rw [dyadicK]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : (winTop eps H / (vaughanW eps H * vaughanW eps H) + 1)
      * (vaughanW eps H * vaughanW eps H)
      ≤ 2 ^ dyadicK eps H * (vaughanW eps H * vaughanW eps H) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : 2 ^ dyadicK eps H * (vaughanW eps H * vaughanW eps H)
      = vaughanW eps H * vaughanW eps H * 2 ^ dyadicK eps H := by ring
  omega

/-- The window membership facts, forward: `𝒫_H ⊆ (M, N]`. -/
theorem primeWindow_sub {eps : ℚ} {H : ℕ} :
    ∀ p ∈ primeWindow eps H, winBot eps H < p ∧ p ≤ winTop eps H := by
  intro p hp
  obtain ⟨hle, _, hlt⟩ := mem_primeWindow.mp hp
  refine ⟨?_, hle⟩
  have hltR : (eps : ℝ) ^ 2 * (H : ℝ) / 2 < (p : ℝ) := by exact_mod_cast hlt
  have hnn : (0 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 := by positivity
  have hfl : ((winBot eps H : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 := by
    rw [winBot]; exact Nat.floor_le hnn
  have : ((winBot eps H : ℕ) : ℝ) < (p : ℝ) := by linarith
  exact_mod_cast this

/-- The window membership facts, backward: every prime in `(M, N]` is in `𝒫_H`. -/
theorem mem_primeWindow_of_mem {eps : ℚ} {H : ℕ} :
    ∀ n, winBot eps H < n → n ≤ winTop eps H → Nat.Prime n → n ∈ primeWindow eps H := by
  intro n h1 h2 hp
  refine mem_primeWindow.mpr ⟨h2, hp, ?_⟩
  have hlt : (eps : ℝ) ^ 2 * (H : ℝ) / 2 < ((winBot eps H : ℕ) : ℝ) + 1 := by
    rw [winBot]; exact Nat.lt_floor_add_one _
  have hn : ((winBot eps H : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
  have : (eps : ℝ) ^ 2 * (H : ℝ) / 2 < (n : ℝ) := by linarith
  have hQ : ((eps ^ 2 * (H : ℚ) / 2 : ℚ) : ℝ) < (((n : ℕ) : ℚ) : ℝ) := by push_cast; linarith
  exact_mod_cast hQ

/-! ### The residual: the exponent close -/

/-- **THE RESIDUAL** — the exponent close, and nothing else.  Everything
structural in the L-ladder is discharged; what remains is the single explicit
numeric statement that the assembled bound `exitBd` eventually undercuts the
`Ξ_H` threshold `ε²/log H`, uniformly over the admissible Dirichlet
denominators `q ∈ ((log H)^{B₅}, H/(log H)^{B₅} + 1]`.

No `O`, no `o(1)`: `exitBd` is a closed form in `ε, H, q` (see `vinoBd`). -/
def ExitClose (B₅ : ℝ) : Prop :=
  ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H → ∀ q : ℕ,
    arcDen B₅ H < (q : ℝ) → (q : ℝ) ≤ (H : ℝ) / arcDen B₅ H + 1 →
      exitBd eps H q < (eps : ℝ) ^ 2 / Real.log (H : ℝ)

/-- **The exit estimate.**  Off the tight major arcs, the weighted prime
exponential sum is bounded by `exitBd eps H q` at a *reduced* Dirichlet
denominator `q` in the admissible range.  This is the whole L-ladder, assembled:
T1 (coprime reduction), T2 (the `c ≤ 2` shape), L1, L2, L4–L6, and the parameter
instantiation. -/
theorem exists_q_expSum_le {B₅ : ℝ} (hB1 : 1 ≤ B₅) {eps : ℚ} (heps : 0 < eps) {H : ℕ}
    (hH8 : 8 ≤ H) (hHeps : (4 : ℝ) / (eps : ℝ) ^ 2 ≤ (H : ℝ)) {α : ℝ}
    (hnot : ¬ NearRatTight (arcDen B₅ H) H α) :
    ∃ q : ℕ, arcDen B₅ H < (q : ℝ) ∧ (q : ℝ) ≤ (H : ℝ) / arcDen B₅ H + 1 ∧
      ‖expSum eps H α‖ ≤ exitBd eps H q := by
  have hB0 : (0 : ℝ) ≤ B₅ := by linarith
  have hH3 : 3 ≤ H := by omega
  have hHpos : 0 < H := by omega
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hHpos
  -- the arc datum is at least `2`
  have hlogH : (2 : ℝ) ≤ Real.log (H : ℝ) := by
    have h8 : (8 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH8
    have hmono : Real.log 8 ≤ Real.log (H : ℝ) := Real.log_le_log (by norm_num) h8
    have h2 : (2 : ℝ) ≤ Real.log 8 := by
      have hlt := Real.log_two_gt_d9
      have h83 : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
      rw [h83, Real.log_pow]
      push_cast
      linarith
    linarith
  have hden2 : (2 : ℝ) ≤ arcDen B₅ H := by
    rw [arcDen]
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2 : ℝ) ^ B₅ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hB1
      _ ≤ Real.log (H : ℝ) ^ B₅ := Real.rpow_le_rpow (by norm_num) hlogH hB0
  have hdenpos : (0 : ℝ) < arcDen B₅ H := by linarith
  -- the Dirichlet approximant, reduced to lowest terms
  obtain ⟨a0, q0, hq0big, hq0le, hq0rad⟩ := exists_large_den_of_minorTight hB0 hH3 hnot
  have hq0pos : 0 < q0 := by
    have : (0 : ℝ) < (q0 : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨a, q, hqpos, hqq0, hcop, hqbig, hqrad⟩ :=
    approx_reduced hHpos hdenpos.le hnot hq0pos hq0rad
  have hqceil : (q : ℝ) ≤ (H : ℝ) / arcDen B₅ H + 1 := by
    have h1 : (q : ℝ) ≤ (q0 : ℝ) := by exact_mod_cast hqq0
    have h2 : (q0 : ℝ) ≤ ((⌈(H : ℝ) / arcDen B₅ H⌉₊ : ℕ) : ℝ) := by exact_mod_cast hq0le
    have h3 : ((⌈(H : ℝ) / arcDen B₅ H⌉₊ : ℕ) : ℝ) < (H : ℝ) / arcDen B₅ H + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  -- `arcDen ≤ H`: forced by the very existence of a large denominator
  have hdenH : arcDen B₅ H ≤ (H : ℝ) := by
    have h1 : arcDen B₅ H < (H : ℝ) / arcDen B₅ H + 1 := lt_of_lt_of_le hqbig hqceil
    have h2 : arcDen B₅ H * arcDen B₅ H < (H : ℝ) + arcDen B₅ H := by
      have := mul_lt_mul_of_pos_right h1 hdenpos
      rw [add_mul, div_mul_cancel₀ _ hdenpos.ne', one_mul] at this
      linarith
    nlinarith
  -- the min-sum input shape
  set c : ℝ := 1 + arcDen B₅ H / (H : ℝ) with hcdef
  have hc2 : c ≤ 2 := by
    rw [hcdef]
    have : arcDen B₅ H / (H : ℝ) ≤ 1 := by
      rw [div_le_one hHR]; exact hdenH
    linarith
  have happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2 :=
    approx_c_form hqpos hdenpos hHpos hqceil hqrad
  refine ⟨q, hqbig, hqceil, ?_⟩
  -- the window and parameter gates
  have hM2 : 2 ≤ winBot eps H := two_le_winBot heps hHeps
  have hMN : winBot eps H ≤ winTop eps H := winBot_le_winTop heps H
  have hW1 : 1 ≤ vaughanW eps H := one_le_vaughanW (by omega)
  have hWM : vaughanW eps H * vaughanW eps H ≤ winBot eps H := vaughanW_sq_le eps H
  have hNle := winTop_le_pow hW1
  have hhi0 : (0 : ℝ) ≤ dyadicHi eps H := by rw [dyadicHi]; positivity
  have hcut : ∀ J, winBot eps H ≤ J → J ≤ winTop eps H →
      J ≤ min J (vaughanW eps H * 2 ^ dyadicK eps H) * (vaughanW eps H + 1) := by
    intro J _ hJN
    rcases le_or_gt J (vaughanW eps H * 2 ^ dyadicK eps H) with h | h
    · rw [min_eq_left h]
      exact Nat.le_mul_of_pos_right J (by omega)
    · rw [min_eq_right h.le]
      calc J ≤ vaughanW eps H * vaughanW eps H * 2 ^ dyadicK eps H := le_trans hJN hNle
        _ ≤ vaughanW eps H * vaughanW eps H * 2 ^ dyadicK eps H
              + vaughanW eps H * 2 ^ dyadicK eps H := Nat.le_add_right _ _
        _ = vaughanW eps H * 2 ^ dyadicK eps H * (vaughanW eps H + 1) := by ring
  have hhi : ∀ J, winBot eps H ≤ J → J ≤ winTop eps H → ∀ k, k < dyadicK eps H →
      ((min J (vaughanW eps H * 2 ^ (k + 1)) : ℕ) : ℝ)
        - ((min J (vaughanW eps H * 2 ^ k) : ℕ) : ℝ) ≤ dyadicHi eps H := by
    intro J _ _ k hk
    have hab : vaughanW eps H * 2 ^ (k + 1)
        = vaughanW eps H * 2 ^ k + vaughanW eps H * 2 ^ k := by ring
    have hstep : min J (vaughanW eps H * 2 ^ (k + 1))
        ≤ min J (vaughanW eps H * 2 ^ k) + vaughanW eps H * 2 ^ k := by
      rcases le_or_gt J (vaughanW eps H * 2 ^ k) with h | h
      · rw [min_eq_left h]
        exact le_trans (min_le_left _ _) (Nat.le_add_right _ _)
      · rw [min_eq_right h.le, hab]
        exact min_le_right _ _
    have hpk : vaughanW eps H * 2 ^ k ≤ vaughanW eps H * 2 ^ dyadicK eps H :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (le_of_lt hk))
    have h1 : ((min J (vaughanW eps H * 2 ^ (k + 1)) : ℕ) : ℝ)
        ≤ ((min J (vaughanW eps H * 2 ^ k) : ℕ) : ℝ)
          + ((vaughanW eps H * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hstep
    have h2 : ((vaughanW eps H * 2 ^ k : ℕ) : ℝ)
        ≤ ((vaughanW eps H * 2 ^ dyadicK eps H : ℕ) : ℝ) := by exact_mod_cast hpk
    rw [dyadicHi]
    linarith
  rw [exitBd]
  exact expSum_le_vinoBd hqpos hc2 hcop happ hM2 hMN hW1 hWM hhi0 hcut hhi
    primeWindow_sub mem_primeWindow_of_mem

/-- **THE EXIT, at the residual.**  Given the exponent close, the sealed
obligation `MinorArcBoundTight` follows — with the `H₀` arms accumulated by the
ladder (`H ≥ 8` for the arc datum, `H ≥ 4/ε²` for the window) absorbed into the
target's own `∃ H₀`. -/
theorem minorArcBoundTight_of_exitClose {B₅ : ℝ} (hB1 : 1 ≤ B₅) (hcl : ExitClose B₅) :
    MinorArcBoundTight B₅ := by
  intro eps heps
  obtain ⟨H₁, hH₁⟩ := hcl eps heps
  refine ⟨max (max H₁ 8) (⌈(4 : ℝ) / (eps : ℝ) ^ 2⌉₊ + 1), ?_⟩
  intro H _ hle α hnot
  have hH1le : H₁ ≤ H := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have hH8 : 8 ≤ H := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have hHeps : (4 : ℝ) / (eps : ℝ) ^ 2 ≤ (H : ℝ) := by
    have h1 : ⌈(4 : ℝ) / (eps : ℝ) ^ 2⌉₊ + 1 ≤ H := le_trans (le_max_right _ _) hle
    have h2 : (4 : ℝ) / (eps : ℝ) ^ 2 ≤ ((⌈(4 : ℝ) / (eps : ℝ) ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : ((⌈(4 : ℝ) / (eps : ℝ) ^ 2⌉₊ : ℕ) : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast (by omega : ⌈(4 : ℝ) / (eps : ℝ) ^ 2⌉₊ ≤ H)
    linarith
  obtain ⟨q, hq1, hq2, hbnd⟩ := exists_q_expSum_le hB1 heps hH8 hHeps hnot
  exact lt_of_le_of_lt hbnd (hH₁ H hH1le q hq1 hq2)

/-- **`MinorArcBoundTight 12`, at the residual** — the S7 target at the frozen
exponent `B₅ = 12`, reduced to the single exponent close `ExitClose 12`. -/
theorem minorArcBoundTight_twelve_of_close (hcl : ExitClose 12) : MinorArcBoundTight 12 :=
  minorArcBoundTight_of_exitClose (by norm_num) hcl

/-- **`BigXiArcTight 12`, at the residual** — the frozen S7 row itself, through
the sealed reduction `bigXiArcTight_of_minorArcTight`. -/
theorem bigXiArcTight_twelve_of_close (hcl : ExitClose 12) : BigXiArcTight 12 :=
  bigXiArcTight_of_minorArcTight (minorArcBoundTight_twelve_of_close hcl)

end Salt.MR
