/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.TypeSums
import Salt.LS.Spacing
import Salt.ExpSum.Basic
import Salt.ExpSum.Kusmin

/-!
# S7 L-ladder — the Vaughan wire-in, the geometric phase bound, and the Vinogradov min-sums

Foundation stones `L3`, `L3c`, `L3b` of the minor-arc ladder behind
`Salt.MR.MinorArcBound` (see `Salt/MR/BigXiArc.lean`).  Source for the analytic
content: **Montgomery, *Ten Lectures on the Interface between Analytic Number
Theory and Harmonic Analysis*, CBMS 84, Chapter 3 §2, pp. 39–41** — the displays
`(2)`, `(5)`, `(7)`, `(8)`, `(9)`.  No Iwaniec–Kowalski staging is needed: the
Vaughan identity and its Type I/II reindex are already kernel-checked in
`Salt/LS/Vaughan.lean` and `Salt/LS/TypeSums.lean` (the Rung-5 dividend).

## What is here

* **L3 (`vaughan_expSum`)** — the landed `Salt.LS.tail_decomp` instantiated at the
  additive character, `f n := eR (α · n)`.  This is a *consumption*, not a
  restatement: the theorem is `tail_decomp` applied, and the coefficient bounds
  are re-exported on the `ℂ` side (`norm_moebius_le`, `norm_typeICoeff_le`,
  `norm_typeIIData_le`) in the shape a triangle-inequality step wants.  Note the
  landed Type II datum is `b(m) = ∑_{c ∣ m, c > V} Λ c` (`Salt.LS.typeIIData`),
  *not* `Λ(c)` — the landed `Σ₃` carries a residual cofactor, and that shape is
  preserved verbatim here.

* **L3c (`geom_phase_bound`)** — Montgomery p. 40 eq. (2): the closed geometric
  sum gives `‖∑_{M₁ < m ≤ M₂} e(θm)‖ ≤ min (M₂ − M₁, 1/(2‖θ‖))`.  Split into the
  trivial card bound (`geom_phase_card_bound`), the analytic bound
  (`geom_phase_dist_bound`), and their fusion.

* **L3b (`minsum_residue_count`, `minsum_block`, `minsum_shift`,
  `minsum_d_dependent`)** — the Vinogradov min-sum suite, Montgomery p. 41 eqs.
  (7), (8), (9).  All four are stated at the **relaxed** rational-approximation
  hypothesis `|α − a/q| ≤ c/q²` with `c ≤ 2` a *parameter*: the Dirichlet stone
  upstream delivers its approximation through a ceiling, which costs a factor `2`
  and would break a hard-wired `c = 1` by a hair.  The price is Montgomery's
  `N(u) ≤ 3` becoming `N(u) ≤ 6`; every constant downstream is stated
  explicitly and crudely.

## The two conventions worth knowing

1. **`minTerm`.**  Lean's `1/0 = 0` makes the literal `min Y (1/(2·‖t‖))` *false*
   at `‖t‖ = 0` (the sum is then as large as the trivial bound, not `0`).  We
   therefore carry the honest min as `minTerm Y t = if t = 0 then Y else
   min Y (1/(2t))`, i.e. the second argument is `+∞` exactly where the classical
   statement reads `1/‖t‖ = ∞`.

2. **`eR` vs `eK`.**  `Salt/ExpSum/Kusmin.lean` carries a private local character
   `eK` with a note asking the house to unify with `Basic.eR` at wire-in.  That is
   done here, once, by `eK_eq_eR`; every Kusmin fact used below is re-expressed at
   `eR` (`norm_one_sub_eR`).  No definition is changed.

## The one genuine design step (`minsum_d_dependent`)

Montgomery's printed eq. (9) is *uniform* in the first argument of the min.  Feeding
a `d`-dependent first argument `X/d` through (9) by dyadic decomposition leaks a bare
additive `X`, which already exceeds the trivial bound and is useless.  The derivation
below instead goes through the **block** form at a *weight function*
(`minsum_block_core`, stated at `Y : ℕ → ℝ`): in each length-`q` block of `d`'s only
the `≤ 6` members of the exceptional class consult `X/d` at all, and in the `k`-th
block those members satisfy `d > kq`, so their total is `≤ 6X/(kq)` and the harmonic
sum over blocks yields `(X/q)(1 + log 2D)`.  The `k = 0` block is the delicate one:
there the exceptional `d` cannot be small, because `‖da/q‖ ≥ 1/q` for `0 < d < q`
forces `4d ≥ q` (`four_mul_ge_of_mem_blockExc_zero`), so `X/d ≤ 4X/q`.

The block ladder is stated with the factor `1 + log q`, which is what the harmonic
sum literally produces; `one_add_log_le_two_mul_log` converts it to Montgomery's
printed `log 2q` shape at the cost of a factor `2`.  Note the `d`-dependent bound
lands at `(D + q)(1 + log q)`, one power of a logarithm *better* than the
`(D + q)(log 2q)²` the ladder budgets for.
-/

namespace Salt.MR

open Finset ArithmeticFunction Salt.LS Salt.ExpSum
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ## T0 — unifying the two additive characters

`Salt/ExpSum/Kusmin.lean` defines a private `eK` with the *same* definition as
`Salt/ExpSum/Basic.lean`'s `eR`, and its header asks for the unification at
wire-in.  Here it is; from now on only `eR` appears. -/

/-- **The `eK`/`eR` unification** (Kusmin header's own request).  The two
additive characters are definitionally the same function. -/
theorem eK_eq_eR (x : ℝ) : eK x = eR x := by
  rw [eK, eR]
  congr 1
  push_cast
  ring

/-- `‖1 − e(s)‖ = 2|sin πs|`, transported from `Salt.ExpSum.norm_one_sub_eK`. -/
theorem norm_one_sub_eR (s : ℝ) : ‖1 - eR s‖ = 2 * |Real.sin (Real.pi * s)| := by
  rw [← eK_eq_eR]; exact norm_one_sub_eK s

/-- `e(·)` is `1`-periodic, transported from `Salt.ExpSum.eK_add_intCast`. -/
theorem eR_add_intCast (x : ℝ) (k : ℤ) : eR (x + (k : ℝ)) = eR x := by
  rw [← eK_eq_eR, ← eK_eq_eR]; exact eK_add_intCast x k

/-- `e(θ·m) = e(θ)^m` for a natural multiple. -/
theorem eR_mul_natCast (θ : ℝ) (m : ℕ) : eR (θ * m) = eR θ ^ m := by
  induction m with
  | zero => simp [eR]
  | succ n ih =>
      have hcast : θ * ((n + 1 : ℕ) : ℝ) = θ * n + θ := by push_cast; ring
      rw [hcast, eR_add, ih, pow_succ]

/-! ## `dist₁` support lemmas

`Salt/LS/Dist.lean` supplies `dist₁`, its triangle inequality, the `ℤ`-shift
invariance and `dist₁_le_abs`; `Salt/LS/Spacing.lean` adds `dist₁_le_sub_int`.
The three facts below are the ones the min-sum ladder needs on top. -/

/-- `dist₁` only sees the difference of its arguments. -/
theorem dist₁_eq_sub_zero (x y : ℝ) : dist₁ x y = dist₁ (x - y) 0 := by
  simp only [dist₁, sub_zero]

/-- `|sin(π·)|` is `1`-periodic. -/
theorem abs_sin_pi_mul_add_intCast (x : ℝ) (k : ℤ) :
    |Real.sin (Real.pi * (x + (k : ℝ)))| = |Real.sin (Real.pi * x)| := by
  have h1 := norm_one_sub_eR (x + (k : ℝ))
  have h2 := norm_one_sub_eR x
  rw [eR_add_intCast, h2] at h1
  linarith

/-- **Jordan's inequality on the circle**: `2‖θ‖ ≤ |sin πθ|`, where `‖θ‖` is
`dist₁ θ 0`.  This is what converts the closed geometric sum's `1/|sin πθ|` into
Montgomery's `1/(2‖θ‖)` (p. 39, last display). -/
theorem two_mul_dist₁_le_abs_sin (θ : ℝ) : 2 * dist₁ θ 0 ≤ |Real.sin (Real.pi * θ)| := by
  have hkey : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → 2 * t ≤ Real.sin (Real.pi * t) := by
    intro t ht0 ht1
    have hjordan := Real.mul_le_sin (x := Real.pi * t) (by positivity)
      (by nlinarith [Real.pi_pos])
    have hid : 2 / Real.pi * (Real.pi * t) = 2 * t := by
      field_simp
    linarith
  have hd : dist₁ θ 0 = |θ - (round θ : ℝ)| := by simp only [dist₁, sub_zero]
  have habs : |θ - (round θ : ℝ)| ≤ 1 / 2 := abs_sub_round θ
  have h1 : 2 * |θ - (round θ : ℝ)| ≤ Real.sin (Real.pi * |θ - (round θ : ℝ)|) :=
    hkey _ (abs_nonneg _) habs
  have h2 : Real.sin (Real.pi * |θ - (round θ : ℝ)|)
      ≤ |Real.sin (Real.pi * (θ - (round θ : ℝ)))| := by
    rcases abs_cases (θ - (round θ : ℝ)) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; exact le_abs_self _
    · rw [he, show Real.pi * (-(θ - (round θ : ℝ))) = -(Real.pi * (θ - (round θ : ℝ))) by ring,
        Real.sin_neg]
      exact neg_le_abs _
  have h3 : |Real.sin (Real.pi * θ)| = |Real.sin (Real.pi * (θ - (round θ : ℝ)))| := by
    have := abs_sin_pi_mul_add_intCast (θ - (round θ : ℝ)) (round θ)
    rwa [show θ - (round θ : ℝ) + (round θ : ℝ) = θ by ring] at this
  rw [hd, h3]
  linarith

/-- If `q ∤ t` then `t/q` is at distance at least `1/q` from the integers. -/
theorem inv_le_dist₁_intCast_div {t : ℤ} {q : ℕ} (hq : 0 < q) (h : ¬ ((q : ℤ) ∣ t)) :
    1 / (q : ℝ) ≤ dist₁ ((t : ℝ) / (q : ℝ)) 0 := by
  have hQ : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hd : dist₁ ((t : ℝ) / (q : ℝ)) 0
      = |(t : ℝ) / (q : ℝ) - (round ((t : ℝ) / (q : ℝ)) : ℝ)| := by
    simp only [dist₁, sub_zero]
  set j : ℤ := round ((t : ℝ) / (q : ℝ)) with hj
  have hne : t - j * (q : ℤ) ≠ 0 := by
    intro hz
    exact h ⟨j, by linear_combination hz⟩
  have h1 : (1 : ℝ) ≤ |(t : ℝ) - (j : ℝ) * (q : ℝ)| := by
    have hz := Int.one_le_abs hne
    have hz' : ((1 : ℤ) : ℝ) ≤ ((|t - j * (q : ℤ)| : ℤ) : ℝ) := by exact_mod_cast hz
    rw [Int.cast_abs] at hz'
    push_cast at hz'
    exact hz'
  rw [hd, show (t : ℝ) / (q : ℝ) - (j : ℝ) = ((t : ℝ) - (j : ℝ) * (q : ℝ)) / (q : ℝ) by
    field_simp, abs_div, abs_of_pos hQ]
  gcongr

/-! ## L3 — Vaughan's identity at the additive character

Nothing is restated: `vaughan_expSum` **is** `Salt.LS.tail_decomp` at
`f n := eR (α n)`. -/

/-- **L3.**  Vaughan's identity for the prime exponential sum: the tail
`∑_{V < n ≤ x} Λ(n) e(αn)` splits as `TypeI₁ − TypeI₂ + TypeII`.  This is the
landed `Salt.LS.tail_decomp` instantiated at `f n := eR (α·n)`; the Type II datum
is the landed `typeIIData V m = ∑_{c ∣ m, c > V} Λ c`, not `Λ`. -/
theorem vaughan_expSum {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (x : ℕ) (α : ℝ) :
    (∑ n ∈ Finset.Ioc V x, (Λ n : ℂ) * eR (α * (n : ℝ)))
      = (∑ d ∈ (Finset.Icc 1 x).filter (· ≤ U), (μ d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
            (Real.log ((m : ℕ) : ℝ) : ℂ) * eR (α * ((d * m : ℕ) : ℝ)))
      - (∑ t ∈ Finset.Icc 1 x, (typeICoeff U V t : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < t * m ∧ t * m ≤ x),
            eR (α * ((t * m : ℕ) : ℝ)))
      + (∑ d ∈ Finset.Ioc U x, (μ d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
            (typeIIData V m : ℂ) * eR (α * ((d * m : ℕ) : ℝ))) :=
  Salt.LS.tail_decomp hU hV x (fun n => eR (α * (n : ℝ)))

/-- Re-export at the instantiation: the Möbius coefficient has `ℂ`-norm `≤ 1`. -/
theorem norm_moebius_le (d : ℕ) : ‖((μ d : ℤ) : ℂ)‖ ≤ 1 := by
  have hcast : ((μ d : ℤ) : ℂ) = ((((μ d : ℤ) : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  calc |((μ d : ℤ) : ℝ)| = ((|(μ d : ℤ)| : ℤ) : ℝ) := by rw [Int.cast_abs]
    _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast abs_moebius_le_one
    _ = 1 := by norm_num

/-- Re-export at the instantiation: the Type I₂ coefficient has `ℂ`-norm
`≤ log t` (`Salt.LS.abs_typeICoeff_le`, moved across the `ℝ → ℂ` coercion). -/
theorem norm_typeICoeff_le (U V t : ℕ) : ‖((typeICoeff U V t : ℝ) : ℂ)‖ ≤ Real.log t := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_typeICoeff_le U V t

/-- Re-export at the instantiation: the Type II datum has `ℂ`-norm `≤ log m`
(`Salt.LS.typeIIData_nonneg` + `Salt.LS.typeIIData_le_log`). -/
theorem norm_typeIIData_le (V m : ℕ) : ‖((typeIIData V m : ℝ) : ℂ)‖ ≤ Real.log m := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (typeIIData_nonneg V m)]
  exact typeIIData_le_log V m

/-! ## L3c — the geometric phase bound (Montgomery p. 40, eq. (2)) -/

/-- The trivial bound on a phase sum: the number of terms. -/
theorem geom_phase_card_bound (θ : ℝ) {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) :
    ‖∑ m ∈ Finset.Ioc M₁ M₂, eR (θ * (m : ℝ))‖ ≤ (M₂ : ℝ) - (M₁ : ℝ) := by
  calc ‖∑ m ∈ Finset.Ioc M₁ M₂, eR (θ * (m : ℝ))‖
      ≤ ∑ m ∈ Finset.Ioc M₁ M₂, ‖eR (θ * (m : ℝ))‖ := norm_sum_le _ _
    _ = (M₂ : ℝ) - (M₁ : ℝ) := by
        simp only [norm_eR, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
        rw [Nat.cast_sub h]

/-- **Montgomery p. 39–40, eq. (2), analytic half.**  The closed geometric sum
bounds a phase sum by `1/(2‖θ‖)`. -/
theorem geom_phase_dist_bound (θ : ℝ) (M₁ M₂ : ℕ) (hθ : dist₁ θ 0 ≠ 0) :
    ‖∑ m ∈ Finset.Ioc M₁ M₂, eR (θ * (m : ℝ))‖ ≤ 1 / (2 * dist₁ θ 0) := by
  have hd0 : 0 < dist₁ θ 0 := lt_of_le_of_ne (dist₁_nonneg θ 0) (Ne.symm hθ)
  have hsin : 4 * dist₁ θ 0 ≤ ‖1 - eR θ‖ := by
    rw [norm_one_sub_eR]; linarith [two_mul_dist₁_le_abs_sin θ]
  have hz1 : eR θ ≠ 1 := by
    intro hz
    rw [hz] at hsin
    simp only [sub_self, norm_zero] at hsin
    linarith
  have hsum : ∑ m ∈ Finset.Ioc M₁ M₂, eR (θ * (m : ℝ))
      = eR θ ^ (M₁ + 1) * ∑ i ∈ Finset.range (M₂ - M₁), eR θ ^ i := by
    have hIoc : Finset.Ioc M₁ M₂ = Finset.Ico (M₁ + 1) (M₂ + 1) := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc, Finset.sum_Ico_eq_sum_range]
    rw [show M₂ + 1 - (M₁ + 1) = M₂ - M₁ by omega, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [eR_mul_natCast, ← pow_add]
  rw [hsum, norm_mul, norm_pow, norm_eR, one_pow, one_mul, geom_sum_eq hz1, norm_div,
    norm_sub_rev (eR θ) 1]
  have h2 : ‖eR θ ^ (M₂ - M₁) - 1‖ ≤ 2 := by
    calc ‖eR θ ^ (M₂ - M₁) - 1‖ ≤ ‖eR θ ^ (M₂ - M₁)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_eR, one_pow, norm_one]; norm_num
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  have hstep : ‖eR θ ^ (M₂ - M₁) - 1‖ * (2 * dist₁ θ 0) ≤ 2 * (2 * dist₁ θ 0) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  linarith

/-! ## The honest min

Lean's junk value `1/0 = 0` makes the literal `min Y (1/(2t))` wrong at `t = 0`;
`minTerm` carries the classical convention `1/‖0‖ = +∞`. -/

/-- The Vinogradov min-term `min (Y, 1/(2t))`, with `1/(2·0)` read as `+∞`. -/
noncomputable def minTerm (Y t : ℝ) : ℝ := if t = 0 then Y else min Y (1 / (2 * t))

/-- `minTerm` never exceeds its first argument. -/
theorem minTerm_le_left (Y t : ℝ) : minTerm Y t ≤ Y := by
  unfold minTerm; split
  · exact le_rfl
  · exact min_le_left _ _

/-- Away from the integers, `minTerm` never exceeds `1/(2t)`. -/
theorem minTerm_le_inv {t : ℝ} (Y : ℝ) (ht : t ≠ 0) : minTerm Y t ≤ 1 / (2 * t) := by
  unfold minTerm; rw [if_neg ht]; exact min_le_right _ _

/-- `minTerm` is nonnegative on nonnegative data. -/
theorem minTerm_nonneg {Y t : ℝ} (hY : 0 ≤ Y) (ht : 0 ≤ t) : 0 ≤ minTerm Y t := by
  unfold minTerm; split
  · exact hY
  · rename_i h
    exact le_min hY (by positivity)

/-- `minTerm` is monotone in its first argument. -/
theorem minTerm_mono_left {Y Y' t : ℝ} (h : Y ≤ Y') : minTerm Y t ≤ minTerm Y' t := by
  unfold minTerm; split
  · exact h
  · exact min_le_min h le_rfl

/-- **L3c — Montgomery p. 40, eq. (2).**  `‖∑_{M₁ < m ≤ M₂} e(θm)‖ ≤
min(M₂ − M₁, 1/(2‖θ‖))`, with the honest min. -/
theorem geom_phase_bound (θ : ℝ) {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) :
    ‖∑ m ∈ Finset.Ioc M₁ M₂, eR (θ * (m : ℝ))‖
      ≤ minTerm ((M₂ : ℝ) - (M₁ : ℝ)) (dist₁ θ 0) := by
  unfold minTerm
  by_cases ht : dist₁ θ 0 = 0
  · rw [if_pos ht]; exact geom_phase_card_bound θ h
  · rw [if_neg ht]
    exact le_min (geom_phase_card_bound θ h) (geom_phase_dist_bound θ M₁ M₂ ht)

/-! ## L3b — the Vinogradov min-sum suite (Montgomery p. 41, eqs. (7), (8), (9))

Standing data: a frequency `α`, a rational approximation `a/q` with
`Int.gcd a q = 1`, and `|α − a/q| ≤ c/q²` with `c ≤ 2` **a parameter**.  The
parameter is not cosmetic: the upstream Dirichlet stone produces its
approximation through a ceiling, which costs a factor `2`, so a hard-wired
`c = 1` would break by a hair.  Paying `c ≤ 2` turns Montgomery's `N(u) ≤ 3`
into `N(u) ≤ 6`, and every constant below is the crude one that delivers. -/

/-- Montgomery's `N(u)` as a `Finset`: the members of the length-`q` block
`(M, M+q]` whose `α`-multiple sits within `1/(2q)` of `u` on the circle. -/
noncomputable def blockExc (α : ℝ) (q M : ℕ) (u : ℝ) : Finset ℕ :=
  (Finset.Ioc M (M + q)).filter (fun n => dist₁ ((n : ℝ) * α) u ≤ 1 / (2 * (q : ℝ)))

/-- `1 + log q ≤ 2 log 2q` for `q ≥ 1`: the bridge from the shape the harmonic sum
produces to Montgomery's printed `log 2q`. -/
theorem one_add_log_le_two_mul_log {q : ℕ} (hq : 1 ≤ q) :
    1 + Real.log q ≤ 2 * Real.log (2 * (q : ℝ)) := by
  have hQ : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hQ
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hsplit : Real.log (2 * (q : ℝ)) = Real.log 2 + Real.log q :=
    Real.log_mul (by norm_num) (by linarith)
  rw [hsplit]
  linarith

/-- The harmonic sum in the shape the block ladder produces it. -/
theorem sum_range_inv_succ_le (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have hcast : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1) := by
    rw [harmonic]
    push_cast
    simp [one_div]
  rwa [hcast] at h

/-- **L3b(i) — Montgomery p. 41, eq. (8)** at the relaxed hypothesis
`|α − a/q| ≤ c/q²`, `c ≤ 2`.  In any block of `q` consecutive integers, at most
`6` have `nα` within `1/(2q)` of a prescribed point of the circle.  (Montgomery
gets `3` at `c = 1`; the interval whose rationals `r/q` are counted has length
`(1 + 2c)/q`, so `c = 2` gives `6`.) -/
theorem minsum_residue_count {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q)
    (hc : c ≤ 2) (hcop : Int.gcd a (q : ℤ) = 1)
    (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2) (M : ℕ) (u : ℝ) :
    (blockExc α q M u).card ≤ 6 := by
  have hQ : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hc0 : 0 ≤ c := by
    by_contra hcon
    push Not at hcon
    have hneg : c / (q : ℝ) ^ 2 < 0 := div_neg_of_neg_of_pos hcon (by positivity)
    linarith [abs_nonneg (α - (a : ℝ) / (q : ℝ)), happ]
  set v : ℝ := u - (M : ℝ) * α with hv
  set L : ℤ := ⌈(q : ℝ) * v - 5 / 2⌉ with hL
  -- The counting map: `n ↦ a(n−M) − q·round(a(n−M)/q − v)`.
  set W : ℕ → ℤ := fun n =>
    a * ((n - M : ℕ) : ℤ)
      - (q : ℤ) * round (((a * ((n - M : ℕ) : ℤ) : ℤ) : ℝ) / (q : ℝ) - v) with hW
  have hcard : (Finset.Icc L (L + 5)).card = 6 := by
    rw [Int.card_Icc, show L + 5 + 1 - L = 6 by ring]
    rfl
  -- The key estimate: `W n` lies within `5/2` of `qv`.
  have hkey : ∀ n ∈ blockExc α q M u, |((W n : ℤ) : ℝ) - (q : ℝ) * v| ≤ 5 / 2 := by
    intro n hn
    simp only [blockExc, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
    have hmn : (n : ℝ) = (M : ℝ) + ((n - M : ℕ) : ℝ) := by
      have hsplit : (n - M : ℕ) + M = n := by omega
      calc (n : ℝ) = (((n - M : ℕ) + M : ℕ) : ℝ) := by rw [hsplit]
        _ = (M : ℝ) + ((n - M : ℕ) : ℝ) := by push_cast; ring
    have hmq : ((n - M : ℕ) : ℝ) ≤ (q : ℝ) := by
      have : (n - M : ℕ) ≤ q := by omega
      exact_mod_cast this
    have hmnn : (0 : ℝ) ≤ ((n - M : ℕ) : ℝ) := by positivity
    -- the phase identity `nα − u = mα − v`
    have hphase : (n : ℝ) * α - u = ((n - M : ℕ) : ℝ) * α - v := by rw [hmn, hv]; ring
    have hdelta : |((n - M : ℕ) : ℝ) * (α - (a : ℝ) / (q : ℝ))| ≤ c / (q : ℝ) := by
      rw [abs_mul, abs_of_nonneg hmnn]
      calc ((n - M : ℕ) : ℝ) * |α - (a : ℝ) / (q : ℝ)| ≤ (q : ℝ) * (c / (q : ℝ) ^ 2) :=
            mul_le_mul hmq happ (abs_nonneg _) (le_of_lt hQ)
        _ = c / (q : ℝ) := by field_simp
    -- the circle estimate for `(am)/q − v`
    have hx : dist₁ ((((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ) / (q : ℝ) - v) 0
        ≤ 5 / (2 * (q : ℝ)) := by
      have hstep1 := dist₁_triangle ((((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ) / (q : ℝ) - v)
        (((n - M : ℕ) : ℝ) * α - v) 0
      have hstep2 : dist₁ ((((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ) / (q : ℝ) - v)
          (((n - M : ℕ) : ℝ) * α - v) ≤ c / (q : ℝ) := by
        refine le_trans (dist₁_le_abs _ _) ?_
        have hrw : (((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ) / (q : ℝ) - v
            - (((n - M : ℕ) : ℝ) * α - v)
            = -(((n - M : ℕ) : ℝ) * (α - (a : ℝ) / (q : ℝ))) := by
          push_cast
          field_simp
          ring
        rw [hrw, abs_neg]
        exact hdelta
      have hstep3 : dist₁ (((n - M : ℕ) : ℝ) * α - v) 0 ≤ 1 / (2 * (q : ℝ)) := by
        rw [← hphase, ← dist₁_eq_sub_zero]
        exact hn3
      have hcq : c / (q : ℝ) ≤ 2 / (q : ℝ) := by gcongr
      have harith : 2 / (q : ℝ) + 1 / (2 * (q : ℝ)) = 5 / (2 * (q : ℝ)) := by
        field_simp; ring
      linarith
    simp only [dist₁, sub_zero] at hx
    have hmul : |(((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ)
        - (q : ℝ) * ((round ((((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ) / (q : ℝ) - v) : ℤ) : ℝ)
        - (q : ℝ) * v| ≤ 5 / 2 := by
      have hexp : (((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ)
          - (q : ℝ) * ((round ((((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ) / (q : ℝ) - v) : ℤ) : ℝ)
          - (q : ℝ) * v
          = (q : ℝ) * ((((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ) / (q : ℝ) - v
              - ((round ((((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ) / (q : ℝ) - v) : ℤ) : ℝ)) := by
        field_simp
        ring
      rw [hexp, abs_mul, abs_of_pos hQ]
      calc (q : ℝ) * |(((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ) / (q : ℝ) - v
              - ((round ((((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ) / (q : ℝ) - v) : ℤ) : ℝ)|
          ≤ (q : ℝ) * (5 / (2 * (q : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hx (le_of_lt hQ)
        _ = 5 / 2 := by field_simp
    have hgoal : ((W n : ℤ) : ℝ)
        = (((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ)
          - (q : ℝ) * ((round ((((a * ((n - M : ℕ) : ℤ) : ℤ)) : ℝ) / (q : ℝ) - v) : ℤ) : ℝ) := by
      simp only [hW]
      push_cast
      ring
    rw [hgoal]
    exact hmul
  refine le_trans (Finset.card_le_card_of_injOn W ?_ ?_) (le_of_eq hcard)
  · -- maps into `Icc L (L+5)`
    intro n hn
    rw [Finset.mem_coe] at hn
    have hb := hkey n hn
    rw [Finset.mem_coe, Finset.mem_Icc]
    have hlow : (q : ℝ) * v - 5 / 2 ≤ ((W n : ℤ) : ℝ) := by
      rw [abs_le] at hb; linarith [hb.1]
    have hhigh : ((W n : ℤ) : ℝ) ≤ (q : ℝ) * v + 5 / 2 := by
      rw [abs_le] at hb; linarith [hb.2]
    constructor
    · exact Int.ceil_le.mpr hlow
    · have hLge : (q : ℝ) * v - 5 / 2 ≤ (L : ℝ) := Int.le_ceil _
      have : ((W n : ℤ) : ℝ) ≤ ((L + 5 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  · -- injective on the exceptional class
    intro n hn n' hn' heq
    rw [Finset.mem_coe] at hn hn'
    simp only [blockExc, Finset.mem_filter, Finset.mem_Ioc] at hn hn'
    obtain ⟨⟨hn1, hn2⟩, -⟩ := hn
    obtain ⟨⟨hn1', hn2'⟩, -⟩ := hn'
    -- `W n = W n'` forces `a(n−M) ≡ a(n'−M) (mod q)`
    have hdvd : (q : ℤ) ∣ a * (((n - M : ℕ) : ℤ) - ((n' - M : ℕ) : ℤ)) := by
      simp only [hW] at heq
      refine ⟨round (((a * ((n - M : ℕ) : ℤ) : ℤ) : ℝ) / (q : ℝ) - v)
        - round (((a * ((n' - M : ℕ) : ℤ) : ℤ) : ℝ) / (q : ℝ) - v), ?_⟩
      linear_combination heq
    have hcop' : IsCoprime ((q : ℤ)) a := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hcop
    have hdvd' : (q : ℤ) ∣ (((n - M : ℕ) : ℤ) - ((n' - M : ℕ) : ℤ)) := by
      exact hcop'.dvd_of_dvd_mul_left hdvd
    have hlt : |(((n - M : ℕ) : ℤ) - ((n' - M : ℕ) : ℤ))| < (q : ℤ) := by
      rw [abs_lt]
      omega
    have hzero := Int.eq_zero_of_abs_lt_dvd hdvd' hlt
    omega

/-- **L3b(ii), core form — Montgomery p. 41, eq. (7).**  The block bound at a
*weight function*.  Over a block of `q` consecutive integers, every `n` outside
the exceptional class `blockExc α q M 0` is paid for by the geometric factor
`1/(2‖nα‖)` alone, at total cost `12·q·(1 + log q)`; the exceptional class is the
only place the *first* argument of the min is consulted at all.

Stating this at a weight function `Y : ℕ → ℝ` rather than a constant is what makes
the `d`-dependent sum (`minsum_d_dependent`) provable — see the module header. -/
theorem minsum_block_core {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q)
    (hc : c ≤ 2) (hcop : Int.gcd a (q : ℤ) = 1)
    (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2) (M : ℕ)
    (Y : ℕ → ℝ) (hY : ∀ n, 0 ≤ Y n) :
    ∑ n ∈ Finset.Ioc M (M + q), minTerm (Y n) (dist₁ ((n : ℝ) * α) 0)
      ≤ (∑ n ∈ blockExc α q M 0, Y n) + 12 * (q : ℝ) * (1 + Real.log q) := by
  have hQ : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set f : ℕ → ℝ := fun n => minTerm (Y n) (dist₁ ((n : ℝ) * α) 0) with hf
  set g : ℕ → ℕ := fun n => (round ((q : ℝ) * dist₁ ((n : ℝ) * α) 0)).toNat with hg
  -- Every band index lies in `[0, q]`.
  have hgmaps : ∀ n ∈ Finset.Ioc M (M + q), g n ∈ Finset.range (q + 1) := by
    intro n _
    simp only [hg, Finset.mem_range]
    have hle : dist₁ ((n : ℝ) * α) 0 ≤ 1 / 2 := dist₁_le_half _ _
    have hnn : (0 : ℝ) ≤ dist₁ ((n : ℝ) * α) 0 := dist₁_nonneg _ _
    have hbound : round ((q : ℝ) * dist₁ ((n : ℝ) * α) 0) ≤ (q : ℤ) := by
      rw [round_eq]
      refine Int.lt_add_one_iff.mp (Int.floor_lt.mpr ?_)
      push_cast
      nlinarith
    have hcast := Int.toNat_le.mpr hbound
    omega
  -- The defining property of the band index.
  have hband : ∀ n j : ℕ, g n = j →
      |(q : ℝ) * dist₁ ((n : ℝ) * α) 0 - (j : ℝ)| ≤ 1 / 2 := by
    intro n j hj
    have hnn : (0 : ℝ) ≤ (q : ℝ) * dist₁ ((n : ℝ) * α) 0 := by
      have := dist₁_nonneg ((n : ℝ) * α) 0; positivity
    have hround0 : 0 ≤ round ((q : ℝ) * dist₁ ((n : ℝ) * α) 0) := by
      rw [round_eq]; exact Int.floor_nonneg.mpr (by linarith)
    have hjeq : round ((q : ℝ) * dist₁ ((n : ℝ) * α) 0) = (j : ℤ) := by
      simp only [hg] at hj
      omega
    have hab := abs_sub_round ((q : ℝ) * dist₁ ((n : ℝ) * α) 0)
    rw [hjeq] at hab
    push_cast at hab
    exact hab
  -- Band `0` lands in the exceptional class.
  have hzero : ∑ n ∈ (Finset.Ioc M (M + q)).filter (fun n => g n = 0), f n
      ≤ ∑ n ∈ blockExc α q M 0, Y n := by
    refine le_trans (Finset.sum_le_sum (fun n _ => minTerm_le_left (Y n) _)) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hY n)
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨hnI, hn0⟩ := hn
    have hb := hband n 0 hn0
    simp only [Nat.cast_zero, sub_zero] at hb
    simp only [blockExc, Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨hnI, ?_⟩
    have hnn : (0 : ℝ) ≤ dist₁ ((n : ℝ) * α) 0 := dist₁_nonneg _ _
    rw [abs_of_nonneg (by positivity)] at hb
    rw [le_div_iff₀ (by positivity)]
    linarith
  -- Bands `j ≥ 1`: at most `12` members, each of size at most `q/j`.
  have hfibcard : ∀ i : ℕ,
      ((Finset.Ioc M (M + q)).filter (fun n => g n = i + 1)).card ≤ 12 := by
    intro i
    have hsub : (Finset.Ioc M (M + q)).filter (fun n => g n = i + 1)
        ⊆ blockExc α q M (((i : ℝ) + 1) / (q : ℝ))
          ∪ blockExc α q M (-(((i : ℝ) + 1) / (q : ℝ))) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨hnI, hj⟩ := hn
      have hb := hband n (i + 1) hj
      push_cast at hb
      have hdist : |dist₁ ((n : ℝ) * α) 0 - ((i : ℝ) + 1) / (q : ℝ)| ≤ 1 / (2 * (q : ℝ)) := by
        have hrw : dist₁ ((n : ℝ) * α) 0 - ((i : ℝ) + 1) / (q : ℝ)
            = ((q : ℝ) * dist₁ ((n : ℝ) * α) 0 - ((i : ℝ) + 1)) / (q : ℝ) := by
          field_simp
        rw [hrw, abs_div, abs_of_pos hQ, div_le_div_iff₀ hQ (by positivity)]
        nlinarith [hb, hQ]
      have hdr : dist₁ ((n : ℝ) * α) 0 = |(n : ℝ) * α - (round ((n : ℝ) * α) : ℝ)| := by
        simp only [dist₁, sub_zero]
      rcases le_or_gt 0 ((n : ℝ) * α - (round ((n : ℝ) * α) : ℝ)) with hpos | hneg
      · refine Finset.mem_union_left _ ?_
        simp only [blockExc, Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨hnI, ?_⟩
        refine le_trans
          (dist₁_le_sub_int ((n : ℝ) * α) (((i : ℝ) + 1) / (q : ℝ)) (round ((n : ℝ) * α))) ?_
        rw [show (n : ℝ) * α - ((i : ℝ) + 1) / (q : ℝ) - (round ((n : ℝ) * α) : ℝ)
            = ((n : ℝ) * α - (round ((n : ℝ) * α) : ℝ)) - ((i : ℝ) + 1) / (q : ℝ) by ring]
        rwa [hdr, abs_of_nonneg hpos] at hdist
      · refine Finset.mem_union_right _ ?_
        simp only [blockExc, Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨hnI, ?_⟩
        refine le_trans
          (dist₁_le_sub_int ((n : ℝ) * α) (-(((i : ℝ) + 1) / (q : ℝ))) (round ((n : ℝ) * α))) ?_
        rw [show (n : ℝ) * α - -(((i : ℝ) + 1) / (q : ℝ)) - (round ((n : ℝ) * α) : ℝ)
            = -((-((n : ℝ) * α - (round ((n : ℝ) * α) : ℝ))) - ((i : ℝ) + 1) / (q : ℝ)) by ring,
          abs_neg]
        rwa [hdr, abs_of_neg hneg] at hdist
    calc ((Finset.Ioc M (M + q)).filter (fun n => g n = i + 1)).card
        ≤ (blockExc α q M (((i : ℝ) + 1) / (q : ℝ))
            ∪ blockExc α q M (-(((i : ℝ) + 1) / (q : ℝ)))).card := Finset.card_le_card hsub
      _ ≤ (blockExc α q M (((i : ℝ) + 1) / (q : ℝ))).card
            + (blockExc α q M (-(((i : ℝ) + 1) / (q : ℝ)))).card := Finset.card_union_le _ _
      _ ≤ 6 + 6 := add_le_add (minsum_residue_count hq hc hcop happ M _)
            (minsum_residue_count hq hc hcop happ M _)
  have hfibsum : ∀ i : ℕ,
      ∑ n ∈ (Finset.Ioc M (M + q)).filter (fun n => g n = i + 1), f n
        ≤ 12 * ((q : ℝ) / ((i : ℝ) + 1)) := by
    intro i
    have hterm : ∀ n ∈ (Finset.Ioc M (M + q)).filter (fun n => g n = i + 1),
        f n ≤ (q : ℝ) / ((i : ℝ) + 1) := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      have hb := hband n (i + 1) hn.2
      push_cast at hb
      rw [abs_le] at hb
      have hdlow : ((i : ℝ) + 1) / (2 * (q : ℝ)) ≤ dist₁ ((n : ℝ) * α) 0 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hb.1, hQ]
      have hdpos : 0 < dist₁ ((n : ℝ) * α) 0 :=
        lt_of_lt_of_le (by positivity) hdlow
      calc f n ≤ 1 / (2 * dist₁ ((n : ℝ) * α) 0) := minTerm_le_inv _ (ne_of_gt hdpos)
        _ ≤ (q : ℝ) / ((i : ℝ) + 1) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hdlow, hQ, hdpos]
    have hcnt : (((Finset.Ioc M (M + q)).filter (fun n => g n = i + 1)).card : ℝ) ≤ 12 := by
      exact_mod_cast hfibcard i
    calc ∑ n ∈ (Finset.Ioc M (M + q)).filter (fun n => g n = i + 1), f n
        ≤ ((Finset.Ioc M (M + q)).filter (fun n => g n = i + 1)).card
            • ((q : ℝ) / ((i : ℝ) + 1)) := Finset.sum_le_card_nsmul _ _ _ hterm
      _ = (((Finset.Ioc M (M + q)).filter (fun n => g n = i + 1)).card : ℝ)
            * ((q : ℝ) / ((i : ℝ) + 1)) := by rw [nsmul_eq_mul]
      _ ≤ 12 * ((q : ℝ) / ((i : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hcnt (by positivity)
  rw [← Finset.sum_fiberwise_of_maps_to hgmaps f, Finset.sum_range_succ']
  have hsum1 : ∑ i ∈ Finset.range q,
      (∑ n ∈ (Finset.Ioc M (M + q)).filter (fun n => g n = i + 1), f n)
        ≤ 12 * (q : ℝ) * (1 + Real.log q) := by
    calc ∑ i ∈ Finset.range q,
          (∑ n ∈ (Finset.Ioc M (M + q)).filter (fun n => g n = i + 1), f n)
        ≤ ∑ i ∈ Finset.range q, 12 * ((q : ℝ) / ((i : ℝ) + 1)) :=
          Finset.sum_le_sum (fun i _ => hfibsum i)
      _ = 12 * (q : ℝ) * ∑ i ∈ Finset.range q, (1 : ℝ) / ((i : ℝ) + 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
      _ ≤ 12 * (q : ℝ) * (1 + Real.log q) := by
          have hh := sum_range_inv_succ_le q
          nlinarith [hh, hQ]
  linarith [hzero, hsum1]

/-- **L3b(ii) — Montgomery p. 41, eqs. (7)+(8).**  The block form at a constant
first argument: `∑_{M < n ≤ M+q} min(Y, 1/(2‖nα‖)) ≤ 6Y + 12 q (1 + log q)`. -/
theorem minsum_block {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q)
    (hc : c ≤ 2) (hcop : Int.gcd a (q : ℤ) = 1)
    (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2) (M : ℕ) {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ n ∈ Finset.Ioc M (M + q), minTerm Y (dist₁ ((n : ℝ) * α) 0)
      ≤ 6 * Y + 12 * (q : ℝ) * (1 + Real.log q) := by
  have hcore := minsum_block_core hq hc hcop happ M (fun _ => Y) (fun _ => hY)
  have hexc : ∑ _n ∈ blockExc α q M 0, Y ≤ 6 * Y := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc6 : ((blockExc α q M 0).card : ℝ) ≤ 6 := by
      exact_mod_cast minsum_residue_count hq hc hcop happ M (0 : ℝ)
    exact mul_le_mul_of_nonneg_right hc6 hY
  linarith

/-- Chopping `(D, D+Kq]` into `K` consecutive blocks of length `q`.  Pure
telescoping (`Finset.sum_Ioc_consecutive`). -/
private theorem sum_Ioc_blocks (F : ℕ → ℝ) (D q K : ℕ) :
    ∑ n ∈ Finset.Ioc D (D + K * q), F n
      = ∑ k ∈ Finset.range K, ∑ n ∈ Finset.Ioc (D + k * q) (D + k * q + q), F n := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ← ih, show D + (K + 1) * q = D + K * q + q by ring]
      exact (Finset.sum_Ioc_consecutive F (Nat.le_add_right _ _) (Nat.le_add_right _ _)).symm

/-- **L3b(iii) — Montgomery p. 41, eq. (9)**, in the *shifted* form.  Note this is
derived from the **block** form (which is stated at an arbitrary left endpoint `M`),
not from the printed eq. (9), whose sum starts at `h = 1`. -/
theorem minsum_shift {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q)
    (hc : c ≤ 2) (hcop : Int.gcd a (q : ℤ) = 1)
    (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2) (D H : ℕ) {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ n ∈ Finset.Ioc D (D + H), minTerm Y (dist₁ ((n : ℝ) * α) 0)
      ≤ ((H : ℝ) / (q : ℝ) + 1) * (6 * Y + 12 * (q : ℝ) * (1 + Real.log q)) := by
  have hQ : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hHK : H ≤ (H / q + 1) * q := by
    rcases Nat.lt_or_ge H ((H / q + 1) * q) with h | h
    · omega
    · exfalso
      have hle : H / q + 1 ≤ H / q := (Nat.le_div_iff_mul_le hq).mpr h
      omega
  have hnn : ∀ n : ℕ, 0 ≤ minTerm Y (dist₁ ((n : ℝ) * α) 0) :=
    fun n => minTerm_nonneg hY (dist₁_nonneg _ _)
  have hbr : 0 ≤ 6 * Y + 12 * (q : ℝ) * (1 + Real.log q) := by positivity
  calc ∑ n ∈ Finset.Ioc D (D + H), minTerm Y (dist₁ ((n : ℝ) * α) 0)
      ≤ ∑ n ∈ Finset.Ioc D (D + (H / q + 1) * q), minTerm Y (dist₁ ((n : ℝ) * α) 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ioc_subset_Ioc_right (by omega)) (fun n _ _ => hnn n)
    _ = ∑ k ∈ Finset.range (H / q + 1),
          ∑ n ∈ Finset.Ioc (D + k * q) (D + k * q + q), minTerm Y (dist₁ ((n : ℝ) * α) 0) :=
        sum_Ioc_blocks _ D q _
    _ ≤ ∑ _k ∈ Finset.range (H / q + 1), (6 * Y + 12 * (q : ℝ) * (1 + Real.log q)) :=
        Finset.sum_le_sum (fun k _ => minsum_block hq hc hcop happ (D + k * q) hY)
    _ = ((H / q + 1 : ℕ) : ℝ) * (6 * Y + 12 * (q : ℝ) * (1 + Real.log q)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((H : ℝ) / (q : ℝ) + 1) * (6 * Y + 12 * (q : ℝ) * (1 + Real.log q)) := by
        refine mul_le_mul_of_nonneg_right ?_ hbr
        push_cast
        have := Nat.cast_div_le (α := ℝ) (m := H) (n := q)
        linarith

/-- **The `k = 0` block is not dangerous.**  If `d ≤ q` and `‖dα‖ ≤ 1/(2q)` then
`d` cannot be small: `4d ≥ q`.  The reason is arithmetic, not analytic —
`‖da/q‖ ≥ 1/q` whenever `0 < d < q` (coprimality), and the perturbation
`d|α − a/q| ≤ 2d/q²` has to make up the difference.  This is the fact that stops
the `d`-dependent min-sum from leaking a bare `X`. -/
theorem four_mul_ge_of_mem_blockExc_zero {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q)
    (hc : c ≤ 2) (hcop : Int.gcd a (q : ℤ) = 1)
    (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2) {d : ℕ} (hd : d ∈ blockExc α q 0 0) :
    (q : ℝ) ≤ 4 * (d : ℝ) := by
  have hQ : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  simp only [blockExc, Finset.mem_filter, Finset.mem_Ioc, zero_add] at hd
  obtain ⟨⟨hd1, hd2⟩, hd3⟩ := hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  rcases eq_or_lt_of_le hd2 with heq | hlt
  · rw [heq]; linarith
  · have hnotdvd : ¬ ((q : ℤ) ∣ ((d : ℤ) * a)) := by
      intro hdvd
      have hcop' : IsCoprime ((q : ℤ)) a := by
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hcop
      have hqd : (q : ℤ) ∣ (d : ℤ) := hcop'.dvd_of_dvd_mul_right hdvd
      have : q ≤ d := Nat.le_of_dvd (by omega) (by exact_mod_cast hqd)
      omega
    have hlow := inv_le_dist₁_intCast_div (t := (d : ℤ) * a) (q := q) (by omega) hnotdvd
    have hstep : dist₁ ((((d : ℤ) * a : ℤ) : ℝ) / (q : ℝ)) ((d : ℝ) * α)
        ≤ (d : ℝ) * (c / (q : ℝ) ^ 2) := by
      refine le_trans (dist₁_le_abs _ _) ?_
      have hrw : (((d : ℤ) * a : ℤ) : ℝ) / (q : ℝ) - (d : ℝ) * α
          = -((d : ℝ) * (α - (a : ℝ) / (q : ℝ))) := by
        push_cast
        field_simp
        ring
      rw [hrw, abs_neg, abs_mul, abs_of_nonneg (le_of_lt hdR)]
      exact mul_le_mul_of_nonneg_left happ (le_of_lt hdR)
    have htri := dist₁_triangle ((((d : ℤ) * a : ℤ) : ℝ) / (q : ℝ)) ((d : ℝ) * α) 0
    have hkey : 1 / (q : ℝ) ≤ (d : ℝ) * (2 / (q : ℝ) ^ 2) + 1 / (2 * (q : ℝ)) := by
      have hmono : (d : ℝ) * (c / (q : ℝ) ^ 2) ≤ (d : ℝ) * (2 / (q : ℝ) ^ 2) := by
        gcongr
      linarith
    have h2q : (0 : ℝ) < 2 * (q : ℝ) ^ 2 := by positivity
    have e1 : 1 / (q : ℝ) * (2 * (q : ℝ) ^ 2) = 2 * (q : ℝ) := by field_simp
    have e2 : ((d : ℝ) * (2 / (q : ℝ) ^ 2) + 1 / (2 * (q : ℝ))) * (2 * (q : ℝ) ^ 2)
        = 4 * (d : ℝ) + (q : ℝ) := by field_simp; ring
    have hmul := mul_le_mul_of_nonneg_right hkey (le_of_lt h2q)
    rw [e1, e2] at hmul
    linarith

/-- **L3b(iv) — the `d`-dependent Vinogradov min-sum.**  This is the one step that
is *not* a corollary of the printed eq. (9): a uniform-`Y` dyadic decomposition
leaks a bare additive `X`.  The derivation runs through `minsum_block_core` at the
weight `Y d = X/d`, so that only the `≤ 6` exceptional `d` per block consult `X/d`
at all.  Constants are the crude ones the argument delivers. -/
theorem minsum_d_dependent {α : ℝ} {a : ℤ} {q : ℕ} {c : ℝ} (hq : 1 ≤ q)
    (hc : c ≤ 2) (hcop : Int.gcd a (q : ℤ) = 1)
    (happ : |α - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ 2) {X : ℝ} (hX : 0 ≤ X)
    {D : ℕ} (hD : 1 ≤ D) :
    ∑ d ∈ Finset.Icc 1 D, minTerm (X / (d : ℝ)) (dist₁ ((d : ℝ) * α) 0)
      ≤ 30 * (X / (q : ℝ)) * (1 + Real.log (2 * (D : ℝ)))
        + 12 * ((D : ℝ) + (q : ℝ)) * (1 + Real.log q) := by
  have hQ : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlogD : 0 ≤ Real.log (2 * (D : ℝ)) := Real.log_nonneg (by linarith)
  set Yw : ℕ → ℝ := fun n => X / (n : ℝ) with hYw
  have hYnn : ∀ n, 0 ≤ Yw n := fun n => by simp only [hYw]; positivity
  have hnn : ∀ n : ℕ, 0 ≤ minTerm (Yw n) (dist₁ ((n : ℝ) * α) 0) :=
    fun n => minTerm_nonneg (hYnn n) (dist₁_nonneg _ _)
  have hDK : D ≤ (D / q + 1) * q := by
    rcases Nat.lt_or_ge D ((D / q + 1) * q) with h | h
    · omega
    · exfalso
      have hle : D / q + 1 ≤ D / q := (Nat.le_div_iff_mul_le hq).mpr h
      omega
  -- the `k = 0` block
  have hS0 : ∑ d ∈ Finset.Ioc (0 : ℕ) (0 + q), minTerm (Yw d) (dist₁ ((d : ℝ) * α) 0)
      ≤ 24 * (X / (q : ℝ)) + 12 * (q : ℝ) * (1 + Real.log q) := by
    have hcore := minsum_block_core hq hc hcop happ 0 Yw hYnn
    have hterm : ∀ d ∈ blockExc α q 0 0, Yw d ≤ 4 * (X / (q : ℝ)) := by
      intro d hd
      have h4 := four_mul_ge_of_mem_blockExc_zero hq hc hcop happ hd
      have hd1 : 1 ≤ d := by
        simp only [blockExc, Finset.mem_filter, Finset.mem_Ioc] at hd; omega
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      simp only [hYw]
      rw [show 4 * (X / (q : ℝ)) = (4 * X) / (q : ℝ) by ring, div_le_div_iff₀ hdR hQ]
      nlinarith [h4, hX]
    have hexc : ∑ d ∈ blockExc α q 0 0, Yw d ≤ 24 * (X / (q : ℝ)) := by
      calc ∑ d ∈ blockExc α q 0 0, Yw d
          ≤ (blockExc α q 0 0).card • (4 * (X / (q : ℝ))) :=
            Finset.sum_le_card_nsmul _ _ _ hterm
        _ = ((blockExc α q 0 0).card : ℝ) * (4 * (X / (q : ℝ))) := by rw [nsmul_eq_mul]
        _ ≤ 6 * (4 * (X / (q : ℝ))) :=
            mul_le_mul_of_nonneg_right
              (by exact_mod_cast minsum_residue_count hq hc hcop happ 0 (0 : ℝ))
              (by positivity)
        _ = 24 * (X / (q : ℝ)) := by ring
    linarith
  -- the `k ≥ 1` blocks
  have hSi : ∀ i : ℕ,
      ∑ d ∈ Finset.Ioc ((i + 1) * q) ((i + 1) * q + q), minTerm (Yw d) (dist₁ ((d : ℝ) * α) 0)
        ≤ 6 * X / (((i : ℝ) + 1) * (q : ℝ)) + 12 * (q : ℝ) * (1 + Real.log q) := by
    intro i
    have hcore := minsum_block_core hq hc hcop happ ((i + 1) * q) Yw hYnn
    have hpos : (0 : ℝ) < ((i : ℝ) + 1) * (q : ℝ) := by positivity
    have hterm : ∀ d ∈ blockExc α q ((i + 1) * q) 0, Yw d ≤ X / (((i : ℝ) + 1) * (q : ℝ)) := by
      intro d hd
      simp only [blockExc, Finset.mem_filter, Finset.mem_Ioc] at hd
      have hdgt : ((i + 1) * q : ℕ) < d := hd.1.1
      have hdR : ((i : ℝ) + 1) * (q : ℝ) ≤ (d : ℝ) := by
        have : (((i + 1) * q : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast le_of_lt hdgt
        push_cast at this
        linarith
      simp only [hYw]
      gcongr
    have hexc : ∑ d ∈ blockExc α q ((i + 1) * q) 0, Yw d
        ≤ 6 * X / (((i : ℝ) + 1) * (q : ℝ)) := by
      calc ∑ d ∈ blockExc α q ((i + 1) * q) 0, Yw d
          ≤ (blockExc α q ((i + 1) * q) 0).card • (X / (((i : ℝ) + 1) * (q : ℝ))) :=
            Finset.sum_le_card_nsmul _ _ _ hterm
        _ = ((blockExc α q ((i + 1) * q) 0).card : ℝ) * (X / (((i : ℝ) + 1) * (q : ℝ))) := by
            rw [nsmul_eq_mul]
        _ ≤ 6 * (X / (((i : ℝ) + 1) * (q : ℝ))) :=
            mul_le_mul_of_nonneg_right
              (by exact_mod_cast minsum_residue_count hq hc hcop happ ((i + 1) * q) (0 : ℝ))
              (by positivity)
        _ = 6 * X / (((i : ℝ) + 1) * (q : ℝ)) := by ring
    linarith
  -- the harmonic sum over blocks
  have hharm : ∑ i ∈ Finset.range (D / q), (1 : ℝ) / ((i : ℝ) + 1)
      ≤ 1 + Real.log (2 * (D : ℝ)) := by
    refine le_trans (sum_range_inv_succ_le (D / q)) ?_
    have hle : ((D / q : ℕ) : ℝ) ≤ 2 * (D : ℝ) := by
      have h1 : ((D / q : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast Nat.div_le_self D q
      linarith
    rcases Nat.eq_zero_or_pos (D / q) with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      linarith
    · have : Real.log ((D / q : ℕ) : ℝ) ≤ Real.log (2 * (D : ℝ)) :=
        Real.log_le_log (by exact_mod_cast hpos) hle
      linarith
  -- assemble
  have hIcc : Finset.Icc 1 D = Finset.Ioc 0 D := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hmain : ∑ d ∈ Finset.Icc 1 D, minTerm (Yw d) (dist₁ ((d : ℝ) * α) 0)
      ≤ (6 * (X / (q : ℝ)) * (1 + Real.log (2 * (D : ℝ))) + 24 * (X / (q : ℝ)))
        + ((D / q : ℕ) + 1 : ℝ) * (12 * (q : ℝ) * (1 + Real.log q)) := by
    calc ∑ d ∈ Finset.Icc 1 D, minTerm (Yw d) (dist₁ ((d : ℝ) * α) 0)
        = ∑ d ∈ Finset.Ioc 0 D, minTerm (Yw d) (dist₁ ((d : ℝ) * α) 0) := by rw [hIcc]
      _ ≤ ∑ d ∈ Finset.Ioc 0 (0 + (D / q + 1) * q),
            minTerm (Yw d) (dist₁ ((d : ℝ) * α) 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Ioc_subset_Ioc_right (by omega)) (fun n _ _ => hnn n)
      _ = ∑ k ∈ Finset.range (D / q + 1),
            ∑ d ∈ Finset.Ioc (0 + k * q) (0 + k * q + q),
              minTerm (Yw d) (dist₁ ((d : ℝ) * α) 0) := sum_Ioc_blocks _ 0 q _
      _ = (∑ i ∈ Finset.range (D / q),
              ∑ d ∈ Finset.Ioc ((i + 1) * q) ((i + 1) * q + q),
                minTerm (Yw d) (dist₁ ((d : ℝ) * α) 0))
            + ∑ d ∈ Finset.Ioc (0 : ℕ) (0 + q), minTerm (Yw d) (dist₁ ((d : ℝ) * α) 0) := by
          rw [Finset.sum_range_succ']
          simp only [Nat.zero_add, Nat.zero_mul]
      _ ≤ (∑ i ∈ Finset.range (D / q),
              (6 * X / (((i : ℝ) + 1) * (q : ℝ)) + 12 * (q : ℝ) * (1 + Real.log q)))
            + (24 * (X / (q : ℝ)) + 12 * (q : ℝ) * (1 + Real.log q)) :=
          add_le_add (Finset.sum_le_sum (fun i _ => hSi i)) hS0
      _ = (6 * (X / (q : ℝ)) * (∑ i ∈ Finset.range (D / q), (1 : ℝ) / ((i : ℝ) + 1))
              + ((D / q : ℕ) : ℝ) * (12 * (q : ℝ) * (1 + Real.log q)))
            + (24 * (X / (q : ℝ)) + 12 * (q : ℝ) * (1 + Real.log q)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            Finset.mul_sum]
          congr 2
          refine Finset.sum_congr rfl (fun i _ => ?_)
          field_simp
      _ ≤ (6 * (X / (q : ℝ)) * (1 + Real.log (2 * (D : ℝ))) + 24 * (X / (q : ℝ)))
            + ((D / q : ℕ) + 1 : ℝ) * (12 * (q : ℝ) * (1 + Real.log q)) := by
          have hXq : 0 ≤ X / (q : ℝ) := by positivity
          nlinarith [hharm, hXq, hlogq, hQ]
  have hblocks : ((D / q : ℕ) + 1 : ℝ) * (q : ℝ) ≤ (D : ℝ) + (q : ℝ) := by
    have : ((D / q : ℕ) : ℝ) * (q : ℝ) ≤ (D : ℝ) := by
      have h1 : (D / q) * q ≤ D := Nat.div_mul_le_self D q
      exact_mod_cast h1
    linarith [this]
  have hXq : 0 ≤ X / (q : ℝ) := by positivity
  calc ∑ d ∈ Finset.Icc 1 D, minTerm (X / (d : ℝ)) (dist₁ ((d : ℝ) * α) 0)
      = ∑ d ∈ Finset.Icc 1 D, minTerm (Yw d) (dist₁ ((d : ℝ) * α) 0) := by
        simp only [hYw]
    _ ≤ (6 * (X / (q : ℝ)) * (1 + Real.log (2 * (D : ℝ))) + 24 * (X / (q : ℝ)))
          + ((D / q : ℕ) + 1 : ℝ) * (12 * (q : ℝ) * (1 + Real.log q)) := hmain
    _ ≤ 30 * (X / (q : ℝ)) * (1 + Real.log (2 * (D : ℝ)))
          + 12 * ((D : ℝ) + (q : ℝ)) * (1 + Real.log q) := by
        have h1 : ((D / q : ℕ) + 1 : ℝ) * (12 * (q : ℝ) * (1 + Real.log q))
            ≤ 12 * ((D : ℝ) + (q : ℝ)) * (1 + Real.log q) := by
          nlinarith [hblocks, hlogq, hQ]
        nlinarith [h1, hXq, hlogD]

end Salt.MR

