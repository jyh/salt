/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MinorArcVaughan

/-!
# S7 L-ladder — the analytic core (Type I, Type II, the Λ-sum assembly)

Stones `L4`, `L5`, `L6` of the minor-arc ladder, built directly on the landed
foundation `Salt/MR/MinorArcVaughan.lean` (`vaughan_expSum`, `geom_phase_bound`,
`minTerm`, `minsum_shift`, `minsum_d_dependent`).  Source for the analytic
content: **Montgomery, *Ten Lectures*, CBMS 84, Chapter 3 §2, pp. 39–41**.

Nothing from the foundation is restated; every bound below *consumes* it.

## What is here

* **Shared bridges** — the two facts every stone needs.
  - `inner_range_eq`: the landed inner range `{m : V < d·m ≤ x}` (a `filter` on
    `Icc 1 x`) **is an interval**, `Ioc ⌊V/d⌋ ⌊x/d⌋`.  Without this
    `geom_phase_bound` (stated on `Ioc`) cannot be applied at all.
  - `eR_phase_reindex`: `e(α·(d·m)) = e((d·α)·m)`.  The `dist₁` argument is
    therefore `d·α`, which is *exactly* the indexing of `minsum_d_dependent`
    (`dist₁ (d·α) 0`, `d` over `Icc 1 D`) and of `minsum_shift`.

* **T3 (`sum_Ioc_abel`, `norm_sum_Ioc_weighted_le`)** — Abel summation on `Ioc`,
  proved by `Nat.le_induction`.  The Type I₁ inner sum carries the weight
  `log m`, which is *not* a pure phase sum; partial summation against the
  uniform partial-sum bound costs exactly one factor `2·log x` and no more.

* **L4 (`typeI_one_bound`, `typeI_two_bound`, `typeI_bound`)** — both Type I
  sums, through the shared skeleton `typeI_skeleton`: coefficient bound ×
  `geom_phase_bound` on the inner interval × `minsum_d_dependent` at `D`.
  `D = U` for `Σ₁` (the `μ`-coefficient is bounded by `1`), and `D = U·V` for
  `Σ₂` — there the support fact `typeICoeff_eq_zero` truncates the outer range
  *before* the min-sum is applied, and `|a(t)| ≤ log(U·V)` on what is left.

* **L5 (`typeII_block_bound`, shape `typeIIBlockBd`)** — the Type II bilinear sum
  over a block `D < d ≤ E`.  Route: Cauchy–Schwarz in `d`; expand
  `‖∑_m b(m) e(αdm)‖²` as a double sum over `(m, m')`; the resulting inner
  `d`-sum is again over an **interval** (`dpair_range_eq` — the constraint
  `V < d·m ≤ x` is an interval in `d` just as it is in `m`), so
  `geom_phase_bound` applies at phase `α(m − m')`; the `(m − m')` sum goes
  through `minsum_shift`, with the diagonal `m = m'` extracted first (there
  `minTerm`'s *first* argument is consulted — the `minTerm` convention is
  load-bearing exactly here).  The `d`-dependence of the inner range is removed
  by folding it into an indicator (`typeIIterm`), which is legitimate because the
  surviving pair constraint is again an interval.

  The T6 facts are separate and both proved: `typeIIData_eq_zero_of_le`
  (`b(m) = 0` for `m ≤ V`) and its block consequence `typeII_block_eq_zero`
  (a block with `x < (D+1)(V+1)` contributes nothing) — the effective outer
  range is `d ≤ x/V`, which is what L7's exponent arithmetic runs on.

* **L6 (`vinogradov_lambda`, `vinogradov_lambda_dyadic`, `vinogradov_lambda_sq`)**
  — the assembly: the head `n ≤ V` trivially, then `L4` twice, then Type II.
  `vinogradov_lambda` carries the Type II sum raw; `typeII_dyadic_bound` cuts its
  outer range into dyadic blocks `(min x (U·2^k), min x (U·2^(k+1))]` and applies
  `L5` on each; `vinogradov_lambda_dyadic` fuses the two.
  `vinogradov_lambda_sq` is the `U = V = W` instantiation the S7 parameters use
  at `W = ⌊x^{1/4}⌋`, gated by the clean `W·W ≤ x`.

  L6 deliberately stops at the three-term bound with the min-sum outputs
  explicit: the exponent close against the S7 threshold is L7's, not this file's.

## Conventions inherited (do not re-derive)

`minTerm Y t = if t = 0 then Y else min Y (1/(2t))` — never the literal `min`
with `1/dist₁`, which is junk at `0`.  All min-sum statements are at the relaxed
rational approximation `|α − a/q| ≤ c/q²` with `c ≤ 2` and coprimality carried as
`Int.gcd a (q : ℤ) = 1`.  Constants are crude and explicit throughout; no `O`,
no `o(1)`, no implied constant anywhere.
-/

namespace Salt.MR

open Finset ArithmeticFunction Salt.LS Salt.ExpSum
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta ComplexConjugate

/-! ## Shared bridges

`Real.log` at natural arguments, the inner range as an interval, and the phase
reindex that lines the `dist₁` argument up with the min-sum suite's indexing. -/

/-- `Real.log` is nonnegative on natural arguments (`log 0 = 0` covers `n = 0`). -/
theorem log_nat_nonneg (n : ℕ) : 0 ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- `Real.log` is monotone on natural arguments. -/
theorem log_nat_mono {m n : ℕ} (h : m ≤ n) : Real.log m ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm]
    simpa using log_nat_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

/-- `n ↦ log n` is monotone: the Abel weight of the Type I₁ inner sum. -/
theorem log_nat_monotone : Monotone (fun n : ℕ => Real.log n) := fun _ _ h => log_nat_mono h

/-- `dist₁ (·) 0` is even: the distance to the nearest integer does not see the sign.
Used to fold the two halves of the `(m − m')` shift sum onto one another. -/
theorem dist₁_neg_zero (y : ℝ) : dist₁ (-y) 0 = dist₁ y 0 := by
  rw [dist₁_comm y 0]
  simp only [dist₁, sub_zero, zero_sub]

/-- **The inner range is an interval.**  The landed Type I/II inner `m`-range
`{m ∈ Icc 1 x : V < d·m ∧ d·m ≤ x}` is exactly `Ioc ⌊V/d⌋ ⌊x/d⌋`.  This is what
lets `geom_phase_bound` (stated on `Finset.Ioc`) reach the landed sums. -/
theorem inner_range_eq {V x d : ℕ} (hd : 0 < d) :
    (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x) = Finset.Ioc (V / d) (x / d) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨-, hV, hx⟩
    refine ⟨(Nat.div_lt_iff_lt_mul hd).mpr ?_, (Nat.le_div_iff_mul_le hd).mpr ?_⟩
    · rw [mul_comm]; exact hV
    · rw [mul_comm]; exact hx
  · rintro ⟨h1, h2⟩
    have hV : V < d * m := by rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul hd).mp h1
    have hx : d * m ≤ x := by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd).mp h2
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hV; omega
      · exact h
    exact ⟨⟨hm1, le_trans (Nat.le_mul_of_pos_left m hd) hx⟩, hV, hx⟩

/-- **The phase reindex.**  `e(α·(d·m)) = e((d·α)·m)`: the phase carried into
`geom_phase_bound` is `d·α`, so the `dist₁` argument produced downstream is
`dist₁ (d·α) 0` — precisely the indexing of `minsum_d_dependent`. -/
theorem eR_phase_reindex (α : ℝ) (d m : ℕ) :
    eR (α * ((d * m : ℕ) : ℝ)) = eR (((d : ℝ) * α) * (m : ℝ)) := by
  congr 1
  push_cast
  ring

/-- Every partial sum of the inner phase sum obeys the same min-bound. -/
theorem partial_phase_bound {V x d : ℕ} (hd : 0 < d) (α : ℝ) {K : ℕ} (hK : K ≤ x / d) :
    ‖∑ m ∈ Finset.Ioc (V / d) K, eR (((d : ℝ) * α) * (m : ℝ))‖
      ≤ minTerm ((x : ℝ) / (d : ℝ)) (dist₁ ((d : ℝ) * α) 0) := by
  have hnn : (0 : ℝ) ≤ (x : ℝ) / (d : ℝ) := by positivity
  rcases le_or_gt (V / d) K with h | h
  · refine le_trans (geom_phase_bound _ h) (minTerm_mono_left ?_)
    have h1 : ((K : ℕ) : ℝ) ≤ ((x / d : ℕ) : ℝ) := by exact_mod_cast hK
    have h2 : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / (d : ℝ) := Nat.cast_div_le
    have h3 : (0 : ℝ) ≤ ((V / d : ℕ) : ℝ) := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]
    simpa using minTerm_nonneg hnn (dist₁_nonneg ((d : ℝ) * α) 0)

/-- The unweighted inner phase sum (the Type I₂ shape) obeys the min-bound. -/
theorem inner_phase_bound {V x d : ℕ} (hd : 0 < d) (α : ℝ) :
    ‖∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
        eR (α * ((d * m : ℕ) : ℝ))‖
      ≤ minTerm ((x : ℝ) / (d : ℝ)) (dist₁ ((d : ℝ) * α) 0) := by
  rw [inner_range_eq hd]
  simp only [eR_phase_reindex]
  exact partial_phase_bound hd α (le_refl (x / d))

/-! ## T3 — Abel summation for the `log m` weight

The Type I₁ inner sum is `∑_m (log m) e(θm)`, not a pure phase sum.  Partial
summation against the *uniform* partial-sum bound of `partial_phase_bound` costs
one factor `2 log x`, and nothing else: the min structure is preserved. -/

/-- Telescoping over `Ico`. -/
private theorem sum_Ico_telescope (w : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ i ∈ Finset.Ico M N, (w (i + 1) - w i) = w N - w M := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hN ih => rw [Finset.sum_Ico_succ_top hN, ih]; ring

/-- **Abel summation on `Ioc`.**  With `S K = ∑_{M < m ≤ K} A m`,
`∑_{M < m ≤ N} w(m) A(m) = w(N) S(N) − ∑_{M ≤ i < N} (w(i+1) − w(i)) S(i)`. -/
theorem sum_Ioc_abel (M : ℕ) (w : ℕ → ℝ) (A : ℕ → ℂ) {N : ℕ} (hMN : M ≤ N) :
    ∑ m ∈ Finset.Ioc M N, ((w m : ℝ) : ℂ) * A m
      = ((w N : ℝ) : ℂ) * (∑ m ∈ Finset.Ioc M N, A m)
        - ∑ i ∈ Finset.Ico M N, ((w (i + 1) - w i : ℝ) : ℂ) * (∑ m ∈ Finset.Ioc M i, A m) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ioc_succ_top hN (fun m => ((w m : ℝ) : ℂ) * A m),
        Finset.sum_Ico_succ_top hN
          (fun i => ((w (i + 1) - w i : ℝ) : ℂ) * (∑ m ∈ Finset.Ioc M i, A m)),
        Finset.sum_Ioc_succ_top hN A, ih]
      push_cast
      ring

/-- **The Abel bound.**  A monotone nonnegative weight capped by `W`, against a
uniform partial-sum bound `B`, costs a factor `2W`. -/
theorem norm_sum_Ioc_weighted_le {M N : ℕ} (hMN : M ≤ N) {w : ℕ → ℝ} {A : ℕ → ℂ} {B W : ℝ}
    (hB : 0 ≤ B) (hmono : Monotone w) (hw0 : 0 ≤ w M) (hwN : w N ≤ W)
    (hpart : ∀ K, M ≤ K → K ≤ N → ‖∑ m ∈ Finset.Ioc M K, A m‖ ≤ B) :
    ‖∑ m ∈ Finset.Ioc M N, ((w m : ℝ) : ℂ) * A m‖ ≤ 2 * W * B := by
  have hwMN : w M ≤ w N := hmono hMN
  have hWnn : (0 : ℝ) ≤ W := le_trans (le_trans hw0 hwMN) hwN
  rw [sum_Ioc_abel M w A hMN]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖((w N : ℝ) : ℂ) * (∑ m ∈ Finset.Ioc M N, A m)‖ ≤ W * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans hw0 hwMN)]
    exact mul_le_mul hwN (hpart N hMN le_rfl) (norm_nonneg _) hWnn
  have h2 : ‖∑ i ∈ Finset.Ico M N, ((w (i + 1) - w i : ℝ) : ℂ) * (∑ m ∈ Finset.Ioc M i, A m)‖
      ≤ (w N - w M) * B := by
    calc ‖∑ i ∈ Finset.Ico M N, ((w (i + 1) - w i : ℝ) : ℂ) * (∑ m ∈ Finset.Ioc M i, A m)‖
        ≤ ∑ i ∈ Finset.Ico M N,
            ‖((w (i + 1) - w i : ℝ) : ℂ) * (∑ m ∈ Finset.Ioc M i, A m)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.Ico M N, (w (i + 1) - w i) * B := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          simp only [Finset.mem_Ico] at hi
          have hdi : 0 ≤ w (i + 1) - w i := by
            have := hmono (Nat.le_succ i)
            linarith
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdi]
          exact mul_le_mul_of_nonneg_left (hpart i hi.1 (le_of_lt hi.2)) hdi
      _ = (w N - w M) * B := by rw [← Finset.sum_mul, sum_Ico_telescope w hMN]
  have h3 : (w N - w M) * B ≤ W * B := mul_le_mul_of_nonneg_right (by linarith) hB
  linarith

/-- The `log m`-weighted inner sum (the Type I₁ shape): one factor `2 log x`
above the pure phase bound. -/
theorem inner_log_phase_bound {V x d : ℕ} (hd : 0 < d) (α : ℝ) :
    ‖∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
        (Real.log ((m : ℕ) : ℝ) : ℂ) * eR (α * ((d * m : ℕ) : ℝ))‖
      ≤ 2 * Real.log x * minTerm ((x : ℝ) / (d : ℝ)) (dist₁ ((d : ℝ) * α) 0) := by
  have hmt : 0 ≤ minTerm ((x : ℝ) / (d : ℝ)) (dist₁ ((d : ℝ) * α) 0) :=
    minTerm_nonneg (by positivity) (dist₁_nonneg _ _)
  rw [inner_range_eq hd]
  simp only [eR_phase_reindex]
  rcases le_or_gt (V / d) (x / d) with h | h
  · exact norm_sum_Ioc_weighted_le (w := fun n : ℕ => Real.log n) h hmt log_nat_monotone
      (log_nat_nonneg _) (log_nat_mono (Nat.div_le_self x d))
      (fun _ _ hK2 => partial_phase_bound hd α hK2)
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty, norm_zero]
    exact mul_nonneg (by linarith [log_nat_nonneg x]) hmt

/-! ## L4 — the Type I bounds (Montgomery p. 40, display (5))

Both Type I sums have the same skeleton: a coefficient bound on the outer range,
`geom_phase_bound` on the inner interval, and `minsum_d_dependent` to sum the
resulting `minTerm (x/d, ‖dα‖)` over the outer range. -/

/-- The shared Type I skeleton.  `s` is the outer range (inside `Icc 1 D`), `F`
the summand, `κ` the coefficient×weight factor. -/
private theorem typeI_skeleton {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q) (hc : c ≤ 2)
    (hcop : Int.gcd a (q : ℤ) = 1) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2)
    {x D : ℕ} (hD : 1 ≤ D) {s : Finset ℕ} (hs : s ⊆ Finset.Icc 1 D)
    (F : ℕ → ℂ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hF : ∀ d ∈ s, ‖F d‖ ≤ κ * minTerm ((x : ℝ) / (d : ℝ)) (dist₁ ((d : ℝ) * α) 0)) :
    ‖∑ d ∈ s, F d‖ ≤ κ * (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * (D : ℝ)))
        + 12 * ((D : ℝ) + (q : ℝ)) * (1 + Real.log q)) := by
  calc ‖∑ d ∈ s, F d‖ ≤ ∑ d ∈ s, ‖F d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ s, κ * minTerm ((x : ℝ) / (d : ℝ)) (dist₁ ((d : ℝ) * α) 0) :=
        Finset.sum_le_sum hF
    _ ≤ ∑ d ∈ Finset.Icc 1 D, κ * minTerm ((x : ℝ) / (d : ℝ)) (dist₁ ((d : ℝ) * α) 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg hs
          (fun d _ _ => mul_nonneg hκ (minTerm_nonneg (by positivity) (dist₁_nonneg _ _)))
    _ = κ * ∑ d ∈ Finset.Icc 1 D, minTerm ((x : ℝ) / (d : ℝ)) (dist₁ ((d : ℝ) * α) 0) := by
        rw [Finset.mul_sum]
    _ ≤ κ * (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * (D : ℝ)))
          + 12 * ((D : ℝ) + (q : ℝ)) * (1 + Real.log q)) :=
        mul_le_mul_of_nonneg_left
          (minsum_d_dependent hq hc hcop happ (by positivity) hD) hκ

/-- **L4(i) — the Type I₁ bound.**  `∑_{d ≤ U} μ(d) ∑_m (log m) e(α d m)`, with
the `log m` weight paid for by Abel summation and the `d`-sum by the
`d`-dependent Vinogradov min-sum at `D = U`. -/
theorem typeI_one_bound {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q) (hc : c ≤ 2)
    (hcop : Int.gcd a (q : ℤ) = 1) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2)
    {U V x : ℕ} (hU : 1 ≤ U) :
    ‖∑ d ∈ (Finset.Icc 1 x).filter (· ≤ U), (μ d : ℂ) *
        ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
          (Real.log ((m : ℕ) : ℝ) : ℂ) * eR (α * ((d * m : ℕ) : ℝ))‖
      ≤ 2 * Real.log x * (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * (U : ℝ)))
          + 12 * ((U : ℝ) + (q : ℝ)) * (1 + Real.log q)) := by
  refine typeI_skeleton hq hc hcop happ hU ?_ _
    (by linarith [log_nat_nonneg x]) ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1.1, hd.2⟩
  · intro d hd
    have hd0 : 0 < d := by
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd
      omega
    rw [norm_mul]
    exact le_trans
      (mul_le_mul (norm_moebius_le d) (inner_log_phase_bound hd0 α) (norm_nonneg _) zero_le_one)
      (le_of_eq (one_mul _))

/-- **L4(ii) — the Type I₂ bound.**  `∑_t a(t) ∑_m e(α t m)` with
`a = typeICoeff U V`.  The support fact `typeICoeff_eq_zero` truncates the outer
range at `U·V` *before* the min-sum is applied — the min-sum is then at
`D = U·V`, and `|a(t)| ≤ log(U·V)` on what is left. -/
theorem typeI_two_bound {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q) (hc : c ≤ 2)
    (hcop : Int.gcd a (q : ℤ) = 1) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2)
    {U V x : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) :
    ‖∑ t ∈ Finset.Icc 1 x, (typeICoeff U V t : ℂ) *
        ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < t * m ∧ t * m ≤ x),
          eR (α * ((t * m : ℕ) : ℝ))‖
      ≤ Real.log ((U * V : ℕ) : ℝ) *
          (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * ((U * V : ℕ) : ℝ)))
            + 12 * (((U * V : ℕ) : ℝ) + (q : ℝ)) * (1 + Real.log q)) := by
  have hUV : 1 ≤ U * V := Nat.mul_le_mul hU hV
  have hsupp : ∀ t ∈ Finset.Icc 1 x, t ∉ (Finset.Icc 1 x).filter (· ≤ U * V) →
      (typeICoeff U V t : ℂ) *
        (∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < t * m ∧ t * m ≤ x),
          eR (α * ((t * m : ℕ) : ℝ))) = 0 := by
    intro t ht htn
    simp only [Finset.mem_filter, not_and, not_le] at htn
    rw [typeICoeff_eq_zero (htn ht)]
    simp
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hsupp]
  refine typeI_skeleton hq hc hcop happ hUV ?_ _ (log_nat_nonneg _) ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_Icc] at ht ⊢
    exact ⟨ht.1.1, ht.2⟩
  · intro t ht
    have ht0 : 0 < t := by
      simp only [Finset.mem_filter, Finset.mem_Icc] at ht
      omega
    have htUV : t ≤ U * V := by
      simp only [Finset.mem_filter] at ht
      exact ht.2
    rw [norm_mul]
    exact mul_le_mul (le_trans (norm_typeICoeff_le U V t) (log_nat_mono htUV))
      (inner_phase_bound ht0 α) (norm_nonneg _) (log_nat_nonneg _)

/-- **L4 — the Type I bound, fused.**  The two Type I sums of `vaughan_expSum`
together. -/
theorem typeI_bound {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q) (hc : c ≤ 2)
    (hcop : Int.gcd a (q : ℤ) = 1) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2)
    {U V x : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) :
    ‖(∑ d ∈ (Finset.Icc 1 x).filter (· ≤ U), (μ d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
            (Real.log ((m : ℕ) : ℝ) : ℂ) * eR (α * ((d * m : ℕ) : ℝ)))
        - (∑ t ∈ Finset.Icc 1 x, (typeICoeff U V t : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < t * m ∧ t * m ≤ x),
            eR (α * ((t * m : ℕ) : ℝ)))‖
      ≤ 2 * Real.log x * (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * (U : ℝ)))
            + 12 * ((U : ℝ) + (q : ℝ)) * (1 + Real.log q))
        + Real.log ((U * V : ℕ) : ℝ) *
            (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * ((U * V : ℕ) : ℝ)))
              + 12 * (((U * V : ℕ) : ℝ) + (q : ℝ)) * (1 + Real.log q)) :=
  le_trans (norm_sub_le _ _)
    (add_le_add (typeI_one_bound hq hc hcop happ hU) (typeI_two_bound hq hc hcop happ hU hV))

/-! ## L5 — the Type II bilinear bound (Montgomery p. 40, displays (7)–(9))

The Type II datum is the landed `b(m) = typeIIData V m = ∑_{c ∣ m, c > V} Λ c`
(the T7 deviation: *not* `Λ`), with `0 ≤ b(m) ≤ log m` and `b(m) = 0` for
`m ≤ V`.  The route is Cauchy–Schwarz in `d`, then the `(m, m')` expansion.

The one structural obstacle is that the inner `m`-range depends on `d`.  It is
removed by folding the range condition into an indicator (`typeIIterm`): after
the expansion the surviving `d`-range is
`{d ∈ (D, E] : V < d·m ≤ x ∧ V < d·m' ≤ x}`, which is **again an interval**
(`dpair_range_eq`) — the same `Nat` division bridge as `inner_range_eq`, read in
the other variable.  So `geom_phase_bound` applies in `d`, at phase
`α(m − m')`. -/

/-- The Type II summand with the `d`-dependent range folded into an indicator. -/
private noncomputable def typeIIterm (V x : ℕ) (α : ℝ) (d m : ℕ) : ℂ :=
  if V < d * m ∧ d * m ≤ x then (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ)) else 0

/-- **T6 — the effective range.**  The landed Type II datum vanishes below `V`:
`b(m) = 0` for `m ≤ V`.  (Every divisor `c ∣ m` has `c ≤ m ≤ V`, so the `c > V`
filter is empty.)  This is what makes the outer `d`-range effectively `d ≤ x/V`. -/
theorem typeIIData_eq_zero_of_le {V m : ℕ} (h : m ≤ V) : typeIIData V m = 0 := by
  rw [typeIIData]
  refine Finset.sum_eq_zero (fun c hc => ?_)
  exfalso
  simp only [Finset.mem_filter, Nat.mem_divisors] at hc
  obtain ⟨⟨hdvd, hm0⟩, hcV⟩ := hc
  have hcm : c ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
  omega

/-- **T6, consumed.**  If `x < d·(V+1)` the whole Type II inner sum at `d` vanishes:
`b(m) ≠ 0` forces `m > V`, hence `d·m ≥ d(V+1) > x`, contradicting `d·m ≤ x`. -/
theorem typeII_inner_vanishes {V x d : ℕ} (h : x < d * (V + 1)) (α : ℝ) :
    (∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
      (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ))) = 0 := by
  refine Finset.sum_eq_zero (fun m hm => ?_)
  simp only [Finset.mem_filter] at hm
  rcases le_or_gt m V with hmV | hmV
  · rw [typeIIData_eq_zero_of_le hmV]
    simp
  · exfalso
    have h1 : d * (V + 1) ≤ d * m := Nat.mul_le_mul_left d (by omega)
    omega

/-- **T6, on a block.**  A block whose left endpoint already exceeds `x/(V+1)`
contributes **nothing**: for `d > D` and `x < (D+1)(V+1)` the inner sum vanishes.
This is the fact that truncates the dyadic range of `typeII_dyadic_bound` at
`d ≤ x/V` — the exponent arithmetic downstream (L7) runs on it. -/
theorem typeII_block_eq_zero {V x D E : ℕ} (h : x < (D + 1) * (V + 1)) (α : ℝ) :
    (∑ d ∈ Finset.Ioc D E, (μ d : ℂ) *
      ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
        (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ))) = 0 := by
  refine Finset.sum_eq_zero (fun d hd => ?_)
  simp only [Finset.mem_Ioc] at hd
  have hlt : x < d * (V + 1) :=
    lt_of_lt_of_le h (Nat.mul_le_mul_right (V + 1) (by omega))
  rw [typeII_inner_vanishes hlt α, mul_zero]

/-- **The pair range in `d` is an interval.**  For `m, m' ≥ 1` the set of `d` in a
block `(D, E]` satisfying both range conditions is `Ioc (max …) (min …)` — the
`Nat`-division bridge of `inner_range_eq`, read in the `d` variable. -/
theorem dpair_range_eq (V x : ℕ) {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m') (D E : ℕ) :
    (Finset.Ioc D E).filter (fun d => (V < d * m ∧ d * m ≤ x) ∧ (V < d * m' ∧ d * m' ≤ x))
      = Finset.Ioc (max D (max (V / m) (V / m'))) (min E (min (x / m) (x / m'))) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ioc, max_lt_iff, le_min_iff,
    Nat.div_lt_iff_lt_mul hm, Nat.div_lt_iff_lt_mul hm',
    Nat.le_div_iff_mul_le hm, Nat.le_div_iff_mul_le hm']
  tauto

/-- The phase sum over the surviving `d`-interval, compared against the block length. -/
private theorem phase_block_sum_bound {A B D E : ℕ} (hDA : D ≤ A) (hBE : B ≤ E) (hDE : D ≤ E)
    (θ : ℝ) :
    ‖∑ d ∈ Finset.Ioc A B, eR (θ * (d : ℝ))‖ ≤ minTerm ((E : ℝ) - (D : ℝ)) (dist₁ θ 0) := by
  have hL : (0 : ℝ) ≤ (E : ℝ) - (D : ℝ) := by
    have : (D : ℝ) ≤ (E : ℝ) := by exact_mod_cast hDE
    linarith
  rcases le_or_gt A B with h | h
  · refine le_trans (geom_phase_bound θ h) (minTerm_mono_left ?_)
    have h1 : (D : ℝ) ≤ (A : ℝ) := by exact_mod_cast hDA
    have h2 : (B : ℝ) ≤ (E : ℝ) := by exact_mod_cast hBE
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]
    simpa using minTerm_nonneg hL (dist₁_nonneg θ 0)

/-- The `(m, m')` term of the Cauchy–Schwarz expansion, evaluated: the coefficients
factor out and the surviving `d`-sum is a pure phase sum at phase `α(m − m')`. -/
private theorem typeII_pair_sum_eq (V x : ℕ) {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (α : ℝ) (D E : ℕ) :
    ∑ d ∈ Finset.Ioc D E, typeIIterm V x α d m * conj (typeIIterm V x α d m')
      = ((typeIIData V m * typeIIData V m' : ℝ) : ℂ) *
          ∑ d ∈ Finset.Ioc (max D (max (V / m) (V / m'))) (min E (min (x / m) (x / m'))),
            eR ((α * ((m : ℝ) - (m' : ℝ))) * (d : ℝ)) := by
  rw [Finset.mul_sum, ← dpair_range_eq V x hm hm' D E, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases h1 : V < d * m ∧ d * m ≤ x
  · by_cases h2 : V < d * m' ∧ d * m' ≤ x
    · rw [if_pos ⟨h1, h2⟩]
      simp only [typeIIterm, if_pos h1, if_pos h2, map_mul, Complex.conj_ofReal]
      rw [show ((typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ))) *
            ((typeIIData V m' : ℂ) * conj (eR (α * ((d * m' : ℕ) : ℝ))))
          = ((typeIIData V m : ℂ) * (typeIIData V m' : ℂ)) *
            (eR (α * ((d * m : ℕ) : ℝ)) * conj (eR (α * ((d * m' : ℕ) : ℝ)))) by ring,
        eR_mul_conj]
      have hph : α * ((d * m : ℕ) : ℝ) - α * ((d * m' : ℕ) : ℝ)
          = (α * ((m : ℝ) - (m' : ℝ))) * (d : ℝ) := by push_cast; ring
      rw [hph]
      push_cast
      ring
    · rw [if_neg (by tauto)]
      simp only [typeIIterm, if_neg h2]
      simp
  · rw [if_neg (by tauto)]
    simp only [typeIIterm, if_neg h1]
    simp

/-- The `(m, m')` term, bounded: coefficients `≤ log x` each, phase sum by
`geom_phase_bound` at `α(m − m')`. -/
private theorem typeII_pair_bound (V : ℕ) {x m m' D E : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hmx : m ≤ x) (hm'x : m' ≤ x) (hDE : D ≤ E) (α : ℝ) :
    ‖∑ d ∈ Finset.Ioc D E, typeIIterm V x α d m * conj (typeIIterm V x α d m')‖
      ≤ Real.log x * Real.log x *
          minTerm ((E : ℝ) - (D : ℝ)) (dist₁ (α * ((m : ℝ) - (m' : ℝ))) 0) := by
  rw [typeII_pair_sum_eq V x hm hm' α D E, norm_mul]
  have hcoef : ‖((typeIIData V m * typeIIData V m' : ℝ) : ℂ)‖ ≤ Real.log x * Real.log x := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (typeIIData_nonneg V m) (typeIIData_nonneg V m'))]
    exact mul_le_mul (le_trans (typeIIData_le_log V m) (log_nat_mono hmx))
      (le_trans (typeIIData_le_log V m') (log_nat_mono hm'x)) (typeIIData_nonneg V m')
      (log_nat_nonneg x)
  exact mul_le_mul hcoef
    (phase_block_sum_bound (le_max_left _ _) (min_le_left _ _) hDE (α * ((m : ℝ) - (m' : ℝ))))
    (norm_nonneg _) (mul_nonneg (log_nat_nonneg x) (log_nat_nonneg x))

/-- **The Cauchy–Schwarz engine.**
`(∑_d ‖∑_m G d m‖)² ≤ #s · ∑_{m,m'} ‖∑_d G d m · conj (G d m')‖`. -/
private theorem cs_expand (s R : Finset ℕ) (G : ℕ → ℕ → ℂ) :
    (∑ d ∈ s, ‖∑ m ∈ R, G d m‖) ^ 2
      ≤ (s.card : ℝ) * ∑ m ∈ R, ∑ m' ∈ R, ‖∑ d ∈ s, G d m * conj (G d m')‖ := by
  have hCS : (∑ d ∈ s, ‖∑ m ∈ R, G d m‖) ^ 2
      ≤ (s.card : ℝ) * ∑ d ∈ s, ‖∑ m ∈ R, G d m‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun d => ‖∑ m ∈ R, G d m‖)
    simpa using h
  have hnn : (0 : ℝ) ≤ ∑ d ∈ s, ‖∑ m ∈ R, G d m‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hz : ∀ z : ℂ, ((‖z‖ : ℝ) : ℂ) ^ 2 = z * conj z := by
    intro z
    rw [Complex.mul_conj, ← Complex.ofReal_pow, Complex.sq_norm]
  have hd : ∀ d : ℕ, ((‖∑ m ∈ R, G d m‖ : ℝ) : ℂ) ^ 2
      = ∑ m ∈ R, ∑ m' ∈ R, G d m * conj (G d m') := by
    intro d
    rw [hz, map_sum, Finset.sum_mul_sum]
  have hcast : ((∑ d ∈ s, ‖∑ m ∈ R, G d m‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ R, ∑ m' ∈ R, ∑ d ∈ s, G d m * conj (G d m') := by
    calc ((∑ d ∈ s, ‖∑ m ∈ R, G d m‖ ^ 2 : ℝ) : ℂ)
        = ∑ d ∈ s, ((‖∑ m ∈ R, G d m‖ : ℝ) : ℂ) ^ 2 := by push_cast; ring
      _ = ∑ d ∈ s, ∑ m ∈ R, ∑ m' ∈ R, G d m * conj (G d m') :=
          Finset.sum_congr rfl (fun d _ => hd d)
      _ = ∑ m ∈ R, ∑ d ∈ s, ∑ m' ∈ R, G d m * conj (G d m') := Finset.sum_comm
      _ = ∑ m ∈ R, ∑ m' ∈ R, ∑ d ∈ s, G d m * conj (G d m') :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  have hexp : ∑ d ∈ s, ‖∑ m ∈ R, G d m‖ ^ 2
      ≤ ∑ m ∈ R, ∑ m' ∈ R, ‖∑ d ∈ s, G d m * conj (G d m')‖ := by
    calc ∑ d ∈ s, ‖∑ m ∈ R, G d m‖ ^ 2
        = ‖((∑ d ∈ s, ‖∑ m ∈ R, G d m‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      _ = ‖∑ m ∈ R, ∑ m' ∈ R, ∑ d ∈ s, G d m * conj (G d m')‖ := by rw [hcast]
      _ ≤ ∑ m ∈ R, ‖∑ m' ∈ R, ∑ d ∈ s, G d m * conj (G d m')‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ R, ∑ m' ∈ R, ‖∑ d ∈ s, G d m * conj (G d m')‖ :=
          Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
  exact le_trans hCS (mul_le_mul_of_nonneg_left hexp (by positivity))

/-- One row of the shift double sum: for a fixed `k`, the map `n ↦ |k − n|` is at most
two-to-one onto `[0, Mm]`. -/
private theorem shift_row_bound (α : ℝ) {Mm k : ℕ} (hk : k ≤ Mm) {L : ℝ} (hL : 0 ≤ L) :
    ∑ n ∈ Finset.Icc 1 Mm, minTerm L (dist₁ (α * ((k : ℝ) - (n : ℝ))) 0)
      ≤ 2 * ∑ h ∈ Finset.range (Mm + 1), minTerm L (dist₁ ((h : ℝ) * α) 0) := by
  have hw : ∀ h : ℕ, 0 ≤ minTerm L (dist₁ ((h : ℝ) * α) 0) :=
    fun h => minTerm_nonneg hL (dist₁_nonneg _ _)
  have hlow : ∑ n ∈ (Finset.Icc 1 Mm).filter (fun n => n ≤ k),
        minTerm L (dist₁ (α * ((k : ℝ) - (n : ℝ))) 0)
      ≤ ∑ h ∈ Finset.range (Mm + 1), minTerm L (dist₁ ((h : ℝ) * α) 0) := by
    have hrw : ∀ n ∈ (Finset.Icc 1 Mm).filter (fun n => n ≤ k),
        minTerm L (dist₁ (α * ((k : ℝ) - (n : ℝ))) 0)
          = minTerm L (dist₁ (((k - n : ℕ) : ℝ) * α) 0) := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      have he : α * ((k : ℝ) - (n : ℝ)) = ((k - n : ℕ) : ℝ) * α := by
        rw [Nat.cast_sub hn.2]; ring
      rw [he]
    have hinj : ∀ i ∈ (Finset.Icc 1 Mm).filter (fun n => n ≤ k),
        ∀ j ∈ (Finset.Icc 1 Mm).filter (fun n => n ≤ k), k - i = k - j → i = j := by
      intro i hi j hj hij
      simp only [Finset.mem_filter, Finset.mem_Icc] at hi hj
      omega
    calc ∑ n ∈ (Finset.Icc 1 Mm).filter (fun n => n ≤ k),
          minTerm L (dist₁ (α * ((k : ℝ) - (n : ℝ))) 0)
        = ∑ n ∈ (Finset.Icc 1 Mm).filter (fun n => n ≤ k),
            minTerm L (dist₁ (((k - n : ℕ) : ℝ) * α) 0) := Finset.sum_congr rfl hrw
      _ = ∑ h ∈ ((Finset.Icc 1 Mm).filter (fun n => n ≤ k)).image (fun n => k - n),
            minTerm L (dist₁ ((h : ℝ) * α) 0) :=
          (Finset.sum_image (f := fun h : ℕ => minTerm L (dist₁ ((h : ℝ) * α) 0)) hinj).symm
      _ ≤ ∑ h ∈ Finset.range (Mm + 1), minTerm L (dist₁ ((h : ℝ) * α) 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun h _ _ => hw h)
          intro h hh
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hh
          obtain ⟨i, ⟨⟨_, _⟩, _⟩, rfl⟩ := hh
          simp only [Finset.mem_range]
          omega
  have hhigh : ∑ n ∈ (Finset.Icc 1 Mm).filter (fun n => ¬ n ≤ k),
        minTerm L (dist₁ (α * ((k : ℝ) - (n : ℝ))) 0)
      ≤ ∑ h ∈ Finset.range (Mm + 1), minTerm L (dist₁ ((h : ℝ) * α) 0) := by
    have hrw : ∀ n ∈ (Finset.Icc 1 Mm).filter (fun n => ¬ n ≤ k),
        minTerm L (dist₁ (α * ((k : ℝ) - (n : ℝ))) 0)
          = minTerm L (dist₁ (((n - k : ℕ) : ℝ) * α) 0) := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      have he : α * ((k : ℝ) - (n : ℝ)) = -(((n - k : ℕ) : ℝ) * α) := by
        rw [Nat.cast_sub (by omega : k ≤ n)]; ring
      rw [he, dist₁_neg_zero]
    have hinj : ∀ i ∈ (Finset.Icc 1 Mm).filter (fun n => ¬ n ≤ k),
        ∀ j ∈ (Finset.Icc 1 Mm).filter (fun n => ¬ n ≤ k), i - k = j - k → i = j := by
      intro i hi j hj hij
      simp only [Finset.mem_filter, Finset.mem_Icc] at hi hj
      omega
    calc ∑ n ∈ (Finset.Icc 1 Mm).filter (fun n => ¬ n ≤ k),
          minTerm L (dist₁ (α * ((k : ℝ) - (n : ℝ))) 0)
        = ∑ n ∈ (Finset.Icc 1 Mm).filter (fun n => ¬ n ≤ k),
            minTerm L (dist₁ (((n - k : ℕ) : ℝ) * α) 0) := Finset.sum_congr rfl hrw
      _ = ∑ h ∈ ((Finset.Icc 1 Mm).filter (fun n => ¬ n ≤ k)).image (fun n => n - k),
            minTerm L (dist₁ ((h : ℝ) * α) 0) :=
          (Finset.sum_image (f := fun h : ℕ => minTerm L (dist₁ ((h : ℝ) * α) 0)) hinj).symm
      _ ≤ ∑ h ∈ Finset.range (Mm + 1), minTerm L (dist₁ ((h : ℝ) * α) 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun h _ _ => hw h)
          intro h hh
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hh
          obtain ⟨i, ⟨⟨_, _⟩, _⟩, rfl⟩ := hh
          simp only [Finset.mem_range]
          omega
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 Mm) (fun n => n ≤ k)
    (fun n => minTerm L (dist₁ (α * ((k : ℝ) - (n : ℝ))) 0))
  linarith

/-- The shift double sum: the diagonal `m = m'` (where `minTerm`'s *first* argument is
consulted — the `minTerm` convention is load-bearing here) plus the off-diagonal,
the latter through `minsum_shift`. -/
private theorem shift_double_sum_bound {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q) (hc : c ≤ 2)
    (hcop : Int.gcd a (q : ℤ) = 1) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2)
    (Mm : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∑ m ∈ Finset.Icc 1 Mm, ∑ m' ∈ Finset.Icc 1 Mm,
        minTerm L (dist₁ (α * ((m : ℝ) - (m' : ℝ))) 0)
      ≤ 2 * (Mm : ℝ) *
          (L + ((Mm : ℝ) / (q : ℝ) + 1) * (6 * L + 12 * (q : ℝ) * (1 + Real.log q))) := by
  have hQ : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hSr : ∑ h ∈ Finset.range (Mm + 1), minTerm L (dist₁ ((h : ℝ) * α) 0)
      ≤ L + ((Mm : ℝ) / (q : ℝ) + 1) * (6 * L + 12 * (q : ℝ) * (1 + Real.log q)) := by
    have hins : Finset.range (Mm + 1) = insert 0 (Finset.Ioc 0 Mm) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
      omega
    have hms := minsum_shift hq hc hcop happ 0 Mm hL
    rw [Nat.zero_add] at hms
    rw [hins, Finset.sum_insert (by simp)]
    have h0 : minTerm L (dist₁ (((0 : ℕ) : ℝ) * α) 0) = L := by
      simp [minTerm]
    rw [h0]
    linarith
  have hrow : ∀ m ∈ Finset.Icc 1 Mm,
      ∑ m' ∈ Finset.Icc 1 Mm, minTerm L (dist₁ (α * ((m : ℝ) - (m' : ℝ))) 0)
        ≤ 2 * ∑ h ∈ Finset.range (Mm + 1), minTerm L (dist₁ ((h : ℝ) * α) 0) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    exact shift_row_bound α hm.2 hL
  calc ∑ m ∈ Finset.Icc 1 Mm, ∑ m' ∈ Finset.Icc 1 Mm,
        minTerm L (dist₁ (α * ((m : ℝ) - (m' : ℝ))) 0)
      ≤ ∑ _m ∈ Finset.Icc 1 Mm,
          2 * ∑ h ∈ Finset.range (Mm + 1), minTerm L (dist₁ ((h : ℝ) * α) 0) :=
        Finset.sum_le_sum hrow
    _ = (Mm : ℝ) * (2 * ∑ h ∈ Finset.range (Mm + 1), minTerm L (dist₁ ((h : ℝ) * α) 0)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast [Nat.add_sub_cancel]
        ring
    _ ≤ (Mm : ℝ) * (2 * (L + ((Mm : ℝ) / (q : ℝ) + 1)
          * (6 * L + 12 * (q : ℝ) * (1 + Real.log q)))) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 2 * (Mm : ℝ) * (L + ((Mm : ℝ) / (q : ℝ) + 1)
          * (6 * L + 12 * (q : ℝ) * (1 + Real.log q))) := by ring

/-- Folding the `d`-dependent inner range into the indicator, on a block `d > D`. -/
private theorem typeII_inner_eq {V x D d : ℕ} (hd : D < d) (α : ℝ) :
    (∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
        (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ)))
      = ∑ m ∈ Finset.Icc 1 (x / (D + 1)), typeIIterm V x α d m := by
  have hd0 : 0 < d := by omega
  have hsub : (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x)
      ⊆ Finset.Icc 1 (x / (D + 1)) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    refine ⟨hm.1.1, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
    calc m * (D + 1) ≤ m * d := Nat.mul_le_mul le_rfl (by omega)
      _ = d * m := Nat.mul_comm m d
      _ ≤ x := hm.2.2
  calc (∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
        (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ)))
      = ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
          typeIIterm V x α d m := by
        refine Finset.sum_congr rfl (fun m hm => ?_)
        simp only [Finset.mem_filter] at hm
        simp only [typeIIterm, if_pos hm.2]
    _ = ∑ m ∈ Finset.Icc 1 (x / (D + 1)), typeIIterm V x α d m := by
        refine Finset.sum_subset hsub (fun m _ hmn => ?_)
        simp only [typeIIterm]
        rw [if_neg]
        intro hP
        refine hmn (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hP⟩)
        · rcases Nat.eq_zero_or_pos m with h | h
          · rw [h, mul_zero] at hP; omega
          · exact h
        · exact le_trans (Nat.le_mul_of_pos_left m hd0) hP.2

/-- **The L5 block bound, as a shape.**  With `L = E − D` the block length and
`Mm = ⌊x/(D+1)⌋` the effective inner range,
`√( L · (log x)² · 2·Mm · (L + (Mm/q + 1)(6L + 12q(1+log q))) )`.  The additive `L`
inside is the diagonal `m = m'`; the `6` and `12q(1+log q)` are the landed
`minsum_shift` output.  Naming the shape keeps the dyadic assembly readable. -/
noncomputable def typeIIBlockBd (q x D E : ℕ) : ℝ :=
  Real.sqrt (((E : ℝ) - (D : ℝ)) * (Real.log x * Real.log x *
    (2 * ((x / (D + 1) : ℕ) : ℝ) *
      (((E : ℝ) - (D : ℝ)) + (((x / (D + 1) : ℕ) : ℝ) / (q : ℝ) + 1) *
        (6 * ((E : ℝ) - (D : ℝ)) + 12 * (q : ℝ) * (1 + Real.log q))))))

/-- `typeIIBlockBd` is nonnegative (it is a square root). -/
theorem typeIIBlockBd_nonneg (q x D E : ℕ) : 0 ≤ typeIIBlockBd q x D E :=
  Real.sqrt_nonneg _

/-- **L5 — the Type II block bound.**  For a block `D < d ≤ E` of the outer variable,
Cauchy–Schwarz in `d` plus the `(m, m')` expansion give
`‖∑_d μ(d) ∑_m b(m) e(αdm)‖ ≤ typeIIBlockBd q x D E`.  Every constant is explicit. -/
theorem typeII_block_bound {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q) (hc : c ≤ 2)
    (hcop : Int.gcd a (q : ℤ) = 1) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2)
    {V x D E : ℕ} (hDE : D ≤ E) :
    ‖∑ d ∈ Finset.Ioc D E, (μ d : ℂ) *
        ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
          (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ))‖
      ≤ typeIIBlockBd q x D E := by
  rw [typeIIBlockBd]
  have hL : (0 : ℝ) ≤ (E : ℝ) - (D : ℝ) := by
    have : (D : ℝ) ≤ (E : ℝ) := by exact_mod_cast hDE
    linarith
  have hlogx : 0 ≤ Real.log x := log_nat_nonneg x
  have hSnn : (0 : ℝ) ≤ ∑ d ∈ Finset.Ioc D E,
      ‖∑ m ∈ Finset.Icc 1 (x / (D + 1)), typeIIterm V x α d m‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hcard : ((Finset.Ioc D E).card : ℝ) = (E : ℝ) - (D : ℝ) := by
    rw [Nat.card_Ioc, Nat.cast_sub hDE]
  have hdouble : ∑ m ∈ Finset.Icc 1 (x / (D + 1)), ∑ m' ∈ Finset.Icc 1 (x / (D + 1)),
        ‖∑ d ∈ Finset.Ioc D E, typeIIterm V x α d m * conj (typeIIterm V x α d m')‖
      ≤ Real.log x * Real.log x *
          (2 * ((x / (D + 1) : ℕ) : ℝ) *
            (((E : ℝ) - (D : ℝ)) + (((x / (D + 1) : ℕ) : ℝ) / (q : ℝ) + 1) *
              (6 * ((E : ℝ) - (D : ℝ)) + 12 * (q : ℝ) * (1 + Real.log q)))) := by
    have hterm : ∀ m ∈ Finset.Icc 1 (x / (D + 1)), ∀ m' ∈ Finset.Icc 1 (x / (D + 1)),
        ‖∑ d ∈ Finset.Ioc D E, typeIIterm V x α d m * conj (typeIIterm V x α d m')‖
          ≤ Real.log x * Real.log x *
              minTerm ((E : ℝ) - (D : ℝ)) (dist₁ (α * ((m : ℝ) - (m' : ℝ))) 0) := by
      intro m hm m' hm'
      simp only [Finset.mem_Icc] at hm hm'
      exact typeII_pair_bound V (by omega) (by omega)
        (le_trans hm.2 (Nat.div_le_self x (D + 1)))
        (le_trans hm'.2 (Nat.div_le_self x (D + 1))) hDE α
    calc ∑ m ∈ Finset.Icc 1 (x / (D + 1)), ∑ m' ∈ Finset.Icc 1 (x / (D + 1)),
          ‖∑ d ∈ Finset.Ioc D E, typeIIterm V x α d m * conj (typeIIterm V x α d m')‖
        ≤ ∑ m ∈ Finset.Icc 1 (x / (D + 1)), ∑ m' ∈ Finset.Icc 1 (x / (D + 1)),
            Real.log x * Real.log x *
              minTerm ((E : ℝ) - (D : ℝ)) (dist₁ (α * ((m : ℝ) - (m' : ℝ))) 0) :=
          Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun m' hm' => hterm m hm m' hm'))
      _ = Real.log x * Real.log x * ∑ m ∈ Finset.Icc 1 (x / (D + 1)),
            ∑ m' ∈ Finset.Icc 1 (x / (D + 1)),
              minTerm ((E : ℝ) - (D : ℝ)) (dist₁ (α * ((m : ℝ) - (m' : ℝ))) 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun _ _ => (Finset.mul_sum _ _ _).symm)
      _ ≤ Real.log x * Real.log x *
            (2 * ((x / (D + 1) : ℕ) : ℝ) *
              (((E : ℝ) - (D : ℝ)) + (((x / (D + 1) : ℕ) : ℝ) / (q : ℝ) + 1) *
                (6 * ((E : ℝ) - (D : ℝ)) + 12 * (q : ℝ) * (1 + Real.log q)))) :=
          mul_le_mul_of_nonneg_left
            (shift_double_sum_bound hq hc hcop happ (x / (D + 1)) hL)
            (mul_nonneg hlogx hlogx)
  have hsq : (∑ d ∈ Finset.Ioc D E,
        ‖∑ m ∈ Finset.Icc 1 (x / (D + 1)), typeIIterm V x α d m‖) ^ 2
      ≤ ((E : ℝ) - (D : ℝ)) * (Real.log x * Real.log x *
          (2 * ((x / (D + 1) : ℕ) : ℝ) *
            (((E : ℝ) - (D : ℝ)) + (((x / (D + 1) : ℕ) : ℝ) / (q : ℝ) + 1) *
              (6 * ((E : ℝ) - (D : ℝ)) + 12 * (q : ℝ) * (1 + Real.log q))))) := by
    refine le_trans
      (cs_expand (Finset.Ioc D E) (Finset.Icc 1 (x / (D + 1))) (typeIIterm V x α)) ?_
    rw [hcard]
    exact mul_le_mul_of_nonneg_left hdouble hL
  calc ‖∑ d ∈ Finset.Ioc D E, (μ d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
            (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ))‖
      ≤ ∑ d ∈ Finset.Ioc D E,
          ‖∑ m ∈ Finset.Icc 1 (x / (D + 1)), typeIIterm V x α d m‖ := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun d hd => ?_))
        rw [typeII_inner_eq (Finset.mem_Ioc.mp hd).1 α, norm_mul]
        exact le_trans (mul_le_mul_of_nonneg_right (norm_moebius_le d) (norm_nonneg _))
          (le_of_eq (one_mul _))
    _ = Real.sqrt ((∑ d ∈ Finset.Ioc D E,
          ‖∑ m ∈ Finset.Icc 1 (x / (D + 1)), typeIIterm V x α d m‖) ^ 2) :=
        (Real.sqrt_sq hSnn).symm
    _ ≤ Real.sqrt (((E : ℝ) - (D : ℝ)) * (Real.log x * Real.log x *
          (2 * ((x / (D + 1) : ℕ) : ℝ) *
            (((E : ℝ) - (D : ℝ)) + (((x / (D + 1) : ℕ) : ℝ) / (q : ℝ) + 1) *
              (6 * ((E : ℝ) - (D : ℝ)) + 12 * (q : ℝ) * (1 + Real.log q)))))) :=
        Real.sqrt_le_sqrt hsq

/-! ## L6 — the Λ-sum assembly

The head `n ≤ V` is trivial, the tail is `vaughan_expSum`, and the three pieces are
`L4` twice plus `L5`.  `typeII_dyadic_bound` cuts the Type II outer range into dyadic
blocks (`sum_Ioc_chain`) and applies `L5` on each; note the blocks beyond the point
where `U·2^k` reaches `x` are *empty*, and `typeIIBlockBd` is `0` there, so the range
`k < x` is a crude but honest index set. -/

/-- The head `∑_{n ≤ V} Λ(n) e(αn)`, trivially: `≤ V·log V`. -/
theorem norm_lambda_head_le (α : ℝ) (V : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * eR (α * (n : ℝ))‖ ≤ (V : ℝ) * Real.log V := by
  calc ‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * eR (α * (n : ℝ))‖
      ≤ ∑ n ∈ Finset.Icc 1 V, ‖(Λ n : ℂ) * eR (α * (n : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 V, Real.log V := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        simp only [Finset.mem_Icc] at hn
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
          norm_eR, mul_one]
        exact le_trans vonMangoldt_le_log (log_nat_mono hn.2)
    _ = (V : ℝ) * Real.log V := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast [Nat.add_sub_cancel]
        ring

/-- Splitting the Λ-sum at `V`. -/
theorem lambda_head_add_tail (α : ℝ) {V x : ℕ} (hVx : V ≤ x) :
    ∑ n ∈ Finset.Icc 1 x, (Λ n : ℂ) * eR (α * (n : ℝ))
      = (∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * eR (α * (n : ℝ)))
        + ∑ n ∈ Finset.Ioc V x, (Λ n : ℂ) * eR (α * (n : ℝ)) := by
  have hIcc : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hIccV : Finset.Icc 1 V = Finset.Ioc 0 V := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, hIccV, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le V) hVx]

/-- Chopping `(B 0, B K]` into the consecutive blocks `(B k, B (k+1)]`. -/
private theorem sum_Ioc_chain (F : ℕ → ℂ) {B : ℕ → ℕ} (hB : Monotone B) (K : ℕ) :
    ∑ d ∈ Finset.Ioc (B 0) (B K), F d
      = ∑ k ∈ Finset.range K, ∑ d ∈ Finset.Ioc (B k) (B (k + 1)), F d := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [← Finset.sum_Ioc_consecutive F (hB (Nat.zero_le K)) (hB (Nat.le_succ K)),
        Finset.sum_range_succ, ih]

/-- **The dyadic Type II bound.**  The outer range `(U, x]` is cut at
`B k = min x (U·2^k)`; `L5` applies on each block.  Beyond the first `k` with
`U·2^k ≥ x` the blocks are empty and `typeIIBlockBd` vanishes, so `k < x` is a crude
but honest index set. -/
theorem typeII_dyadic_bound {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q) (hc : c ≤ 2)
    (hcop : Int.gcd a (q : ℤ) = 1) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2)
    {U V x : ℕ} (hU : 1 ≤ U) (hUx : U ≤ x) :
    ‖∑ d ∈ Finset.Ioc U x, (μ d : ℂ) *
        ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
          (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ))‖
      ≤ ∑ k ∈ Finset.range x,
          typeIIBlockBd q x (min x (U * 2 ^ k)) (min x (U * 2 ^ (k + 1))) := by
  have hstep : ∀ k : ℕ, U * 2 ^ k ≤ U * 2 ^ (k + 1) := by
    intro k
    exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))
  have hB : Monotone (fun k => min x (U * 2 ^ k)) :=
    monotone_nat_of_le_succ (fun k => min_le_min le_rfl (hstep k))
  have hB0 : min x (U * 2 ^ 0) = U := by
    simp only [pow_zero, mul_one]
    omega
  have hBx : min x (U * 2 ^ x) = x := by
    have h1 : x < 2 ^ x := Nat.lt_two_pow_self
    have h2 : 2 ^ x ≤ U * 2 ^ x := Nat.le_mul_of_pos_left _ hU
    omega
  have hchain := sum_Ioc_chain
    (fun d => (μ d : ℂ) *
      ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
        (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ))) hB x
  simp only [hB0, hBx] at hchain
  rw [hchain]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun k _ => ?_))
  exact typeII_block_bound hq hc hcop happ (hB (Nat.le_succ k))

/-- **L6 — the Vinogradov Λ-sum bound.**  Head + Type I₁ + Type I₂ + Type II, at free
`U, V`.  The Type II term is left as the raw sum here; `vinogradov_lambda_dyadic`
replaces it by the dyadic `L5` output. -/
theorem vinogradov_lambda {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q) (hc : c ≤ 2)
    (hcop : Int.gcd a (q : ℤ) = 1) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2)
    {U V x : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hVx : V ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 x, (Λ n : ℂ) * eR (α * (n : ℝ))‖
      ≤ (V : ℝ) * Real.log V
        + (2 * Real.log x * (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * (U : ℝ)))
              + 12 * ((U : ℝ) + (q : ℝ)) * (1 + Real.log q))
            + Real.log ((U * V : ℕ) : ℝ) *
              (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * ((U * V : ℕ) : ℝ)))
                + 12 * (((U * V : ℕ) : ℝ) + (q : ℝ)) * (1 + Real.log q)))
        + ‖∑ d ∈ Finset.Ioc U x, (μ d : ℂ) *
            ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
              (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ))‖ := by
  rw [lambda_head_add_tail α hVx, vaughan_expSum hU hV x α]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (norm_lambda_head_le α V) (le_trans (norm_add_le _ _)
    (add_le_add (typeI_bound (x := x) hq hc hcop happ hU hV) (le_refl _)))) (le_of_eq (by ring))

/-- **L6, with `L5` plugged in.**  The three-term bound with every piece explicit:
head, the two Type I min-sum outputs, and the dyadic Type II sum. -/
theorem vinogradov_lambda_dyadic {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q) (hc : c ≤ 2)
    (hcop : Int.gcd a (q : ℤ) = 1) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2)
    {U V x : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hUx : U ≤ x) (hVx : V ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 x, (Λ n : ℂ) * eR (α * (n : ℝ))‖
      ≤ (V : ℝ) * Real.log V
        + (2 * Real.log x * (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * (U : ℝ)))
              + 12 * ((U : ℝ) + (q : ℝ)) * (1 + Real.log q))
            + Real.log ((U * V : ℕ) : ℝ) *
              (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * ((U * V : ℕ) : ℝ)))
                + 12 * (((U * V : ℕ) : ℝ) + (q : ℝ)) * (1 + Real.log q)))
        + ∑ k ∈ Finset.range x,
            typeIIBlockBd q x (min x (U * 2 ^ k)) (min x (U * 2 ^ (k + 1))) :=
  le_trans (vinogradov_lambda hq hc hcop happ hU hV hVx)
    (add_le_add le_rfl (typeII_dyadic_bound hq hc hcop happ hU hUx))

/-- **L6 at the S7 instantiation `U = V = W`.**  The parameters S7 uses take
`W = ⌊x^{1/4}⌋`; the gate here is the clean `W·W ≤ x`, which that choice satisfies.
The Type I₂ min-sum then runs at `D = W²`, the Type I₁ at `D = W`. -/
theorem vinogradov_lambda_sq {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q) (hc : c ≤ 2)
    (hcop : Int.gcd a (q : ℤ) = 1) (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2)
    {W x : ℕ} (hW : 1 ≤ W) (hWx : W * W ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 x, (Λ n : ℂ) * eR (α * (n : ℝ))‖
      ≤ (W : ℝ) * Real.log W
        + (2 * Real.log x * (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * (W : ℝ)))
              + 12 * ((W : ℝ) + (q : ℝ)) * (1 + Real.log q))
            + Real.log ((W * W : ℕ) : ℝ) *
              (30 * ((x : ℝ) / (q : ℝ)) * (1 + Real.log (2 * ((W * W : ℕ) : ℝ)))
                + 12 * (((W * W : ℕ) : ℝ) + (q : ℝ)) * (1 + Real.log q)))
        + ∑ k ∈ Finset.range x,
            typeIIBlockBd q x (min x (W * 2 ^ k)) (min x (W * 2 ^ (k + 1))) := by
  have hWle : W ≤ x := le_trans (Nat.le_mul_of_pos_left W hW) hWx
  exact vinogradov_lambda_dyadic hq hc hcop happ hW hW hWle hWle

end Salt.MR
