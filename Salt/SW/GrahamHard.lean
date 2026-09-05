/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.GrahamMean
import Salt.SW.MoebiusRateSharp
import Salt.SW.CoprimeBV

/-!
# ARM B part B2, wave **W6b-H1** — the SUBSTRATE of the Graham mean bound on the
# HARD half `z ≤ u < z²`

`Salt/SW/GrahamMean.lean` (W6b-E) landed the Graham / Barban–Vehov mean bound
`Σ_{n ≤ x} w(n) ≤ C·x/log z` on the EASY half `x ≥ z²`. Graham's theorem is the same
bound from `x ≥ z`, and the missing range `z ≤ x < z²` is reached by An 2022 §5's
one-level specialisation over `ℚ`. **This file lands that argument's SUBSTRATE, not its
conclusion.**

## What is here (the design freeze's rows H0–H6 and H9)

* **H1a/b/c** — the Λ-identity `Σ_{d ∣ n} μ(d)·log(z/d) = Λ(n)` (`n ≥ 2`), its level
  form `log z·Σ_{d ∣ n} θ^{(z)}_d = Λ(n) + T_z(n)`, and the vanishing of the tail
  `T_z(n) = Σ_{d ∣ n, d > z} μ(d)·log(d/z)` below the level (`n ≤ z`).
* **H2** — `w(n) ≤ (2Λ(n)² + 2T_z(n)²)/log²z`, the Cauchy–Schwarz split that DELETES
  An's cross sum `S₂` (two prime sums with their partial summations) outright.
* **H3** — `Σ_{n ≤ x} Λ(n)² ≤ (log 4 + 4)·x·log x`, from `Λ ≤ log` and Chebyshev.
* **H4** — An's (5.2): the tail second moment reindexed by the four-parameter bijection
  `(n, d, d′) ↔ (g, a, b, k)`, an EXACT identity.
* **H5a/H5c** — the squarefree count coprime to `r`, and its two-log weighted form.
* **H6a–f** — the Möbius sums with a power-of-log saving (An (3.1)–(3.3) and
  Lemmas 3.10–3.12 over `ℚ`).
* **H0b–e** — the four elementary divisor-sum bounds every error term of §5 is measured
  against (`σ_{−1/4}` on average, the `1/(n log²)` sum, the dyadic `Q^{1/2}` bound, and
  `Σ σ_{−1/4}(t)/t`).
* **H9** — the BELOW-level mean `Σ_{n ≤ x} w(n) ≤ 1 + C·x·log x/log²z` for `x ≤ z`,
  where the tail is identically zero and the whole weight is Λ.

## ⚠ THE HONEST LABEL — what this file does NOT prove

**It does not prove the full-range mean bound.** The three rows that would close it are
the NEXT wave's and are absent here: the tail second moment `Σ_{n ≤ u} T_z(n)² ≤ C·u·log z`
on `u ≤ z²` (An §5's `S₃`, class D), the full-range `Σ_{n ≤ x} w(n) ≤ C·x/log z` for
`x ≥ z`, and the two consumer-facing forms for Jutila's two-level weight. Nothing here
improves `GrahamMean.lean`'s hypothesis, and B2's closure table still reads the easy
half at no scale.

**Everything proved here is an UPPER bound or an exact identity** — no asymptotic and no
lower bound anywhere. Where a constant is `∃`-bound it is **non-effective**: the `H6`
rows pass through `mmuRate_holds`, whose `x₀` is not extracted, so their docstrings print
the DERIVATION of the constant and never a numeral.

`ρ₀·c₀ = 1` is true (`ρ₀ = 6/π²`, `c₀ = ζ(2)`) and is **never used**: every step that
meets the product absorbs it into an existential constant.

**F6** (no net numerator log): H3's bare `x·log x` and H9's `x·log x/log²z` are consumed
only under `x ≤ z²`, where `log x ≤ 2 log z` and the net is `x·log z` resp. `x/log z`;
every `H6` log is in a DENOMINATOR; H5c's is a log RATIO per variable.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no `sorry`.
-/

namespace Salt.SW

open ArithmeticFunction

/-! ## The four objects of An §2, specialised to `ℚ` -/

open ArithmeticFunction in
/-- The tail `T_z(n) = Σ_{d ∣ n, d > z} μ(d)·log(d/z)` — the part of the level-`z` weight
above the level. -/
noncomputable def tailT (z n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => z < d), (moebius d : ℝ) * Real.log ((d : ℝ) / z)

/-- `σ_{−1/4}(r) = Σ_{e ∣ r} e^{−1/4}`, the error weight of every H5/H6 row (dominates
`σ_{−1/2}`). -/
noncomputable def sigmaQ (r : ℕ) : ℝ := ∑ e ∈ r.divisors, (e : ℝ) ^ (-(1/4 : ℝ))

/-- `κ(r) = r·∏_{p ∣ r}(1 + 1/p)` (An §2). -/
noncomputable def kappa (r : ℕ) : ℝ := (r : ℝ) * ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ))

/-- `ρ₀ = Σ_{d ≥ 1} μ(d)/d²` — the squarefree density, DEFINED as its series
(`= 6/π²`, never needed). -/
noncomputable def rho0 : ℝ := ∑' d : ℕ, (moebius d : ℝ) / (d : ℝ) ^ 2

/-! ## H1 — the Λ-identity and the tail -/

/-- **H1a (An (5.1)).** For `n ≥ 2` and any `z > 0`,
`Σ_{d ∣ n} μ(d)·log(z/d) = Λ(n)`. The `log z` half dies on `Σ_{d ∣ n} μ(d) = 0`
(`n ≥ 2`, `CoprimeBV.sum_divisors_moebius_real`) and the `log d` half is mathlib's
`sum_moebius_mul_log_eq`.

⚠ At `n = 1` the identity would read `log z = 0` and is FALSE — the `n = 1` term is the
additive `1` of H9 (`grahamW z 1 = 1`), never inside H1. -/
theorem sum_divisors_moebius_mul_log_div_eq {z : ℝ} (hz : 0 < z) {n : ℕ} (hn : 2 ≤ n) :
    ∑ d ∈ n.divisors, (moebius d : ℝ) * Real.log (z / d)
      = ArithmeticFunction.vonMangoldt n := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hcongr : ∀ d ∈ n.divisors, (moebius d : ℝ) * Real.log (z / d)
      = (moebius d : ℝ) * Real.log z - (moebius d : ℝ) * Real.log (d : ℝ) := by
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
    rw [Real.log_div hzne hd0]; ring
  have hmu : ∑ d ∈ n.divisors, (moebius d : ℝ) = 0 := by
    rw [sum_divisors_moebius_real n, if_neg (by omega : ¬ n = 1)]
  have hlog : ∑ d ∈ n.divisors, (moebius d : ℝ) * Real.log (d : ℝ)
      = -ArithmeticFunction.vonMangoldt n := by
    have h := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
    simp only [ArithmeticFunction.log_apply] at h
    exact h
  rw [Finset.sum_congr rfl hcongr, Finset.sum_sub_distrib, ← Finset.sum_mul, hmu, hlog]
  ring

-- **H1a's binder-shape row** (the exit test). Off line at `(z, n) = (3, 6)`:
-- `Σ_{d ∣ 6} μ(d)·log(3/d) = log 3 − log(3/2) − log 1 + log(1/2) = 0 = Λ(6)`.
example : ∑ d ∈ (6 : ℕ).divisors, (moebius d : ℝ) * Real.log ((3 : ℝ) / d)
    = ArithmeticFunction.vonMangoldt 6 :=
  sum_divisors_moebius_mul_log_div_eq (by norm_num) (by norm_num)

/-- **H1c.** Below the level the tail is empty: every divisor of `n ≤ z` is `≤ z`. -/
theorem tailT_eq_zero_of_le {z n : ℕ} (hn : n ≤ z) : tailT z n = 0 := by
  have hemp : n.divisors.filter (fun d => z < d) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr ?_
    intro d hd
    have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hd).2
    have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_divisors hd)
    omega
  simp only [tailT, hemp, Finset.sum_empty]

/-- **H1b.** The level-`z` weight's divisor sum is Λ plus the tail:
`log z·Σ_{d ∣ n} θ^{(z)}_d = Λ(n) + T_z(n)` for `z, n ≥ 2`. Multiplying `θ` by `log z`
strips its denominator on the support `d ≤ z`; H1a supplies the untruncated sum and the
remaining `d > z` block is `−T_z(n)` because `log(z/d) = −log(d/z)`. -/
theorem log_mul_sum_grahamTheta_eq {z n : ℕ} (hz : 2 ≤ z) (hn : 2 ≤ n) :
    Real.log z * ∑ d ∈ n.divisors, grahamTheta z d
      = ArithmeticFunction.vonMangoldt n + tailT z n := by
  have hzR : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hz0 : (0 : ℝ) < (z : ℝ) := by linarith
  have hlz : Real.log (z : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hzR)
  have hLHS : Real.log (z : ℝ) * ∑ d ∈ n.divisors, grahamTheta z d
      = ∑ d ∈ n.divisors, (if d ≤ z then (moebius d : ℝ) * Real.log ((z : ℝ) / d) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h : d ≤ z
    · rw [grahamTheta_of_le h, if_pos h]; field_simp
    · rw [grahamTheta_of_lt (not_le.mp h), if_neg h, mul_zero]
  have htail : tailT z n
      = ∑ d ∈ n.divisors, (if z < d then -((moebius d : ℝ) * Real.log ((z : ℝ) / d)) else 0) := by
    simp only [tailT, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    by_cases h : z < d
    · rw [if_pos h, if_pos h]
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
      rw [Real.log_div hd0 (ne_of_gt hz0), Real.log_div (ne_of_gt hz0) hd0]
      ring
    · rw [if_neg h, if_neg h]
  have hfull : ∑ d ∈ n.divisors, (moebius d : ℝ) * Real.log ((z : ℝ) / d)
      = (∑ d ∈ n.divisors, (if d ≤ z then (moebius d : ℝ) * Real.log ((z : ℝ) / d) else 0))
        - tailT z n := by
    rw [htail, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h : d ≤ z
    · rw [if_pos h, if_neg (not_lt.mpr h)]; ring
    · rw [if_neg h, if_pos (not_le.mp h)]; ring
  have hH1a := sum_divisors_moebius_mul_log_div_eq hz0 hn
  rw [hLHS]
  linarith [hfull, hH1a]

/-! ## H2 — the Cauchy–Schwarz split -/

/-- **H2.** `w(n) ≤ (2Λ(n)² + 2T_z(n)²)/log²z` for `z, n ≥ 2`, by H1b and
`(a + b)² ≤ 2a² + 2b²`. This is what DELETES An's cross sum `S₂` (his pp.8–9, two prime
sums with their partial summations): the mean bound never needs the cross term, only both
halves separately. -/
theorem grahamW_le_two_mul_sq {z n : ℕ} (hz : 2 ≤ z) (hn : 2 ≤ n) :
    grahamW z n
      ≤ (2 * ArithmeticFunction.vonMangoldt n ^ 2 + 2 * tailT z n ^ 2) / Real.log z ^ 2 := by
  have hzR : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hlz : 0 < Real.log (z : ℝ) := Real.log_pos hzR
  rw [le_div_iff₀ (by positivity)]
  have hsq : grahamW z n * Real.log (z : ℝ) ^ 2
      = (ArithmeticFunction.vonMangoldt n + tailT z n) ^ 2 := by
    have h2 := log_mul_sum_grahamTheta_eq hz hn
    simp only [grahamW]
    rw [← h2]; ring
  rw [hsq]
  nlinarith [sq_nonneg (ArithmeticFunction.vonMangoldt n - tailT z n)]

/-! ## H3 — the second moment of Λ -/

/-- **H3.** `Σ_{n ≤ x} Λ(n)² ≤ (log 4 + 4)·x·log x` for `x ≥ 1`: `Λ(n)² ≤ Λ(n)·log n ≤
Λ(n)·log x` on the range, then Chebyshev's `ψ(x) ≤ (log 4 + 4)·x`
(`Chebyshev.psi_le_const_mul_self`).

**Measured truth (not a mutation).** The constant `log 4 + 4 = 5.386` is LOSSY: the true
ratio `Σ_{n ≤ x} Λ(n)²/(x·log x) = 0.543 / 0.698 / 0.836 / 0.888 / 0.912` at
`x = 8 / 10² / 10³ / 10⁴ / 10⁵`, rising to `1` from below (`ΣΛ² = x log x − x + o(x)`).
So a mutation of this constant to `1` would PASS at every tested `x` and is NOT a
kill-check for this row; what controls it is the binder `1 ≤ x` and Chebyshev's own
constant. -/
theorem sum_vonMangoldt_sq_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n ^ 2
      ≤ (Real.log 4 + 4) * x * Real.log x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have step1 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n ^ 2
      ≤ Real.log x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnf : n ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp hn).2
    have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hnf) (Nat.floor_le hx0)
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have h1 : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    have h2 : Real.log (n : ℝ) ≤ Real.log x := Real.log_le_log hn0 hnx
    have h3 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    nlinarith
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have step2 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n
      ≤ (Real.log 4 + 4) * x := by
    have hpsi := Chebyshev.psi_le_const_mul_self hx0
    rw [Chebyshev.psi] at hpsi
    rw [hIcc]
    exact hpsi
  have hchain : Real.log x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n
      ≤ Real.log x * ((Real.log 4 + 4) * x) := by
    exact mul_le_mul_of_nonneg_left step2 hlogx
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n ^ 2
      ≤ Real.log x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := step1
    _ ≤ Real.log x * ((Real.log 4 + 4) * x) := hchain
    _ = (Real.log 4 + 4) * x * Real.log x := by ring

/-! ## H9 — the mean BELOW the level -/

/-- **H9 (the below-level range).** For `2 ≤ x ≤ z`,
`Σ_{n ≤ x} w(n) ≤ 1 + C·x·log x/log²z` with `C = 2(log 4 + 4)`. Below the level the tail
vanishes identically (H1c), so H2 leaves only `2Λ(n)²/log²z`, and H3 sums it; the additive
`1` is the `n = 1` term `w(z, 1) = θ^{(z)}_1 ² = 1`, which H1 cannot see.

Off line at `(z, x) = (10, 5)`: `Σ_{n ≤ 5} w(n) = 1.897442` against
`1 + (log 4 + 4)·5·log 5/log²10 = 9.175`. (The constant is `∃`-bound, so the Lean row
below checks the BINDERS; the numerals are receipts.) -/
theorem grahamW_sum_le_low : ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 2 ≤ z → ∀ x : ℝ, 2 ≤ x → x ≤ z →
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, grahamW z n ≤ 1 + C * x * Real.log x / Real.log z ^ 2 := by
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨2 * (Real.log 4 + 4), by linarith, fun z hz x hx2 hxz => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hzR : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hlz : 0 < Real.log (z : ℝ) := Real.log_pos hzR
  have hNz : ⌊x⌋₊ ≤ z := by
    have : ⌊x⌋₊ ≤ ⌊((z : ℕ) : ℝ)⌋₊ := Nat.floor_le_floor hxz
    simpa using this
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
  have hins : Finset.Icc 1 ⌊x⌋₊ = insert 1 (Finset.Icc 2 ⌊x⌋₊) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnotmem : (1 : ℕ) ∉ Finset.Icc 2 ⌊x⌋₊ := by simp
  have hw1 : grahamW z 1 = 1 := by
    simp only [grahamW, Nat.divisors_one, Finset.sum_singleton, grahamTheta_one hz]
    norm_num
  have hbody : ∀ n ∈ Finset.Icc 2 ⌊x⌋₊,
      grahamW z n ≤ 2 * ArithmeticFunction.vonMangoldt n ^ 2 / Real.log (z : ℝ) ^ 2 := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnz : n ≤ z := le_trans (Finset.mem_Icc.mp hn).2 hNz
    have h := grahamW_le_two_mul_sq (z := z) (n := n) hz hn2
    rw [tailT_eq_zero_of_le hnz] at h
    calc grahamW z n
        ≤ (2 * ArithmeticFunction.vonMangoldt n ^ 2 + 2 * (0 : ℝ) ^ 2)
            / Real.log (z : ℝ) ^ 2 := h
      _ = 2 * ArithmeticFunction.vonMangoldt n ^ 2 / Real.log (z : ℝ) ^ 2 := by norm_num
  have hstep : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, grahamW z n
      ≤ ∑ n ∈ Finset.Icc 2 ⌊x⌋₊,
          2 * ArithmeticFunction.vonMangoldt n ^ 2 / Real.log (z : ℝ) ^ 2 :=
    Finset.sum_le_sum hbody
  have hext : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊,
      2 * ArithmeticFunction.vonMangoldt n ^ 2 / Real.log (z : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          2 * ArithmeticFunction.vonMangoldt n ^ 2 / Real.log (z : ℝ) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro k hk; rw [Finset.mem_Icc] at *; omega
    · intro k _ _; positivity
  have hcollect : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      2 * ArithmeticFunction.vonMangoldt n ^ 2 / Real.log (z : ℝ) ^ 2
      = 2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n ^ 2)
          / Real.log (z : ℝ) ^ 2 := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
  have hH3 := sum_vonMangoldt_sq_le hx1
  have hfin : 2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n ^ 2)
      / Real.log (z : ℝ) ^ 2
      ≤ 2 * (Real.log 4 + 4) * x * Real.log x / Real.log (z : ℝ) ^ 2 := by
    refine (div_le_div_iff_of_pos_right (by positivity)).mpr ?_
    nlinarith [hH3]
  rw [hins, Finset.sum_insert hnotmem, hw1]
  linarith [hstep, hext, hcollect.le, hcollect.ge, hfin]

-- **H9's binder-shape row** (the exit test). Off line at `(z, x) = (10, 5)`:
-- `Σ_{n ≤ 5} w(n) = 1.897442 ≤ 1 + (log 4 + 4)·5·log 5/log²10 = 9.175`.
example : ∃ C : ℝ, ∑ n ∈ Finset.Icc 1 ⌊(5 : ℝ)⌋₊, grahamW 10 n
    ≤ 1 + C * 5 * Real.log 5 / Real.log ((10 : ℕ) : ℝ) ^ 2 := by
  obtain ⟨C, -, h⟩ := grahamW_sum_le_low
  exact ⟨C, h 10 (by norm_num) 5 (by norm_num) (by norm_num)⟩


/-! ## The `rpow` substrate of the H0 bounds

Four elementary facts carry every H0 row: `Σ_{e ≤ N} e^{−5/4} ≤ 5`,
`Σ_{f ≤ N} f^{−1/2} ≤ 2√N`, `Σ_{f ≤ N} f^{−3/4} ≤ 4N^{1/4}` and `log u ≤ 4u^{1/4}`.
Each sum is proved by a telescoping induction whose step is an exact polynomial identity
in `a = (n+1)^{−q}`, `b = n^{−q}`, so no integral comparison is needed. -/

/-- `(x^q)^k = x^(q·k)` for a natural `k` — the bridge from `rpow` exponents to the
polynomial identities the induction steps use. -/
private lemma rpow_pow_nat {x : ℝ} (hx : 0 ≤ x) (q : ℝ) (k : ℕ) :
    (x ^ q) ^ k = x ^ (q * (k : ℝ)) := by
  rw [← Real.rpow_natCast (x ^ q) k, ← Real.rpow_mul hx]

private lemma rpow_neg_quarter_pow {t : ℝ} (ht : 0 < t) : (t ^ (-(1/4) : ℝ)) ^ 4 * t = 1 := by
  rw [rpow_pow_nat ht.le, show (-(1/4 : ℝ)) * ((4 : ℕ) : ℝ) = -(1 : ℝ) by norm_num,
    Real.rpow_neg ht.le, Real.rpow_one]
  field_simp

/-- The telescoping step of `Σ e^{−5/4}`: with `a = n^{−1/4}`, `b = (n+1)^{−1/4}` the
relation `a⁴ − b⁴ = a⁴b⁴` and `b ≤ a` give `b⁵ ≤ 4(a − b)`. -/
private lemma rpow_step_five_quarter {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) + 1) ^ (-(5/4) : ℝ)
      ≤ 4 * (n : ℝ) ^ (-(1/4) : ℝ) - 4 * ((n : ℝ) + 1) ^ (-(1/4) : ℝ) := by
  have hx0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hy0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hb5 : ((n : ℝ) + 1) ^ (-(5/4) : ℝ) = (((n : ℝ) + 1) ^ (-(1/4) : ℝ)) ^ 5 := by
    rw [rpow_pow_nat hy0.le, show (-(1/4 : ℝ)) * ((5 : ℕ) : ℝ) = -(5/4 : ℝ) by norm_num]
  rw [hb5]
  set a : ℝ := (n : ℝ) ^ (-(1/4) : ℝ) with ha
  set b : ℝ := ((n : ℝ) + 1) ^ (-(1/4) : ℝ) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos hx0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hy0 _
  have hna : a ^ 4 * (n : ℝ) = 1 := rpow_neg_quarter_pow hx0
  have hnb : b ^ 4 * ((n : ℝ) + 1) = 1 := rpow_neg_quarter_pow hy0
  have hba : b ≤ a := Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by norm_num)
  have hprod : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
  have h1 : (a ^ 4 - b ^ 4) * ((n : ℝ) * ((n : ℝ) + 1)) = 1 := by
    linear_combination ((n : ℝ) + 1) * hna - (n : ℝ) * hnb
  have h2 : (a ^ 4 * b ^ 4) * ((n : ℝ) * ((n : ℝ) + 1)) = 1 := by
    linear_combination (b ^ 4 * ((n : ℝ) + 1)) * hna + hnb
  have hdiff : a ^ 4 - b ^ 4 = a ^ 4 * b ^ 4 :=
    mul_right_cancel₀ hprod.ne' (h1.trans h2.symm)
  have hP : (0 : ℝ) < (a + b) * (a ^ 2 + b ^ 2) := by positivity
  have hd : (0 : ℝ) ≤ a - b := by linarith
  have h3 : b * ((a + b) * (a ^ 2 + b ^ 2)) ≤ 4 * a ^ 4 := by
    nlinarith [mul_nonneg (mul_nonneg ha0.le ha0.le) (mul_nonneg ha0.le hd),
      mul_nonneg (mul_nonneg ha0.le ha0.le) (mul_nonneg hb0.le hd),
      mul_nonneg (mul_nonneg ha0.le hb0.le) (mul_nonneg hb0.le hd),
      mul_nonneg (mul_nonneg hb0.le hb0.le) (mul_nonneg hb0.le hd)]
  have hb4 : (0 : ℝ) ≤ b ^ 4 := by positivity
  have hkey : b ^ 5 * ((a + b) * (a ^ 2 + b ^ 2))
      ≤ (4 * a - 4 * b) * ((a + b) * (a ^ 2 + b ^ 2)) := by
    have e1 : (4 * a - 4 * b) * ((a + b) * (a ^ 2 + b ^ 2)) = 4 * (a ^ 4 - b ^ 4) := by ring
    have e2 : b ^ 5 * ((a + b) * (a ^ 2 + b ^ 2))
        = b ^ 4 * (b * ((a + b) * (a ^ 2 + b ^ 2))) := by ring
    rw [e1, e2, hdiff]
    calc b ^ 4 * (b * ((a + b) * (a ^ 2 + b ^ 2))) ≤ b ^ 4 * (4 * a ^ 4) :=
          mul_le_mul_of_nonneg_left h3 hb4
      _ = 4 * (a ^ 4 * b ^ 4) := by ring
  exact le_of_mul_le_mul_right hkey hP

private lemma sum_rpow_neg_five_quarter_tail {N : ℕ} (hN : 1 ≤ N) :
    ∑ e ∈ Finset.Icc 2 N, (e : ℝ) ^ (-(5/4) : ℝ) ≤ 4 - 4 * (N : ℝ) ^ (-(1/4) : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [show Finset.Icc 2 1 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega)]
    simp
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1)]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith [ih, rpow_step_five_quarter hm]

/-- `Σ_{e ≤ N} e^{−5/4} ≤ 5` (the `e = 1` term plus `4(1 − N^{−1/4})`). -/
private lemma sum_rpow_neg_five_quarter_le (N : ℕ) :
    ∑ e ∈ Finset.Icc 1 N, (e : ℝ) ^ (-(5/4) : ℝ) ≤ 5 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hins : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hpos : (0 : ℝ) ≤ (N : ℝ) ^ (-(1/4) : ℝ) := Real.rpow_nonneg (by positivity) _
    rw [hins, Finset.sum_insert (by simp)]
    simp only [Nat.cast_one, Real.one_rpow]
    linarith [sum_rpow_neg_five_quarter_tail hN]

/-- The telescoping step of `Σ f^{−1/2}`: `(2a − 2b)a − 1 = (a − b)²` with `a² = t + 1`,
`b² = t`. -/
private lemma rpow_step_half (t : ℝ) (ht : 0 ≤ t) :
    (t + 1) ^ (-(1/2) : ℝ) ≤ 2 * (t + 1) ^ ((1/2) : ℝ) - 2 * t ^ ((1/2) : ℝ) := by
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have hinv : (t + 1) ^ (-(1/2) : ℝ) = ((t + 1) ^ ((1/2) : ℝ))⁻¹ := Real.rpow_neg ht1.le _
  rw [hinv]
  set a : ℝ := (t + 1) ^ ((1/2) : ℝ) with ha
  set b : ℝ := t ^ ((1/2) : ℝ) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos ht1 _
  have hb0 : (0 : ℝ) ≤ b := Real.rpow_nonneg ht _
  have ha2 : a ^ 2 = t + 1 := by
    rw [ha, rpow_pow_nat ht1.le, show ((1/2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hb2 : b ^ 2 = t := by
    rw [hb, rpow_pow_nat ht, show ((1/2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  rw [inv_eq_one_div, div_le_iff₀ ha0]
  nlinarith [sq_nonneg (a - b), ha2, hb2]

/-- `Σ_{f ≤ N} f^{−1/2} ≤ 2·N^{1/2}`. -/
private lemma sum_rpow_neg_half_le (N : ℕ) :
    ∑ f ∈ Finset.Icc 1 N, (f : ℝ) ^ (-(1/2) : ℝ) ≤ 2 * (N : ℝ) ^ ((1/2) : ℝ) := by
  induction N with
  | zero => simp [Real.zero_rpow]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith [ih, rpow_step_half (m : ℝ) (by positivity)]

/-- The telescoping step of `Σ f^{−3/4}`: `4(a − b)a³ − 1 = (a − b)²(3a² + 2ab + b²)` with
`a⁴ = t + 1`, `b⁴ = t`. -/
private lemma rpow_step_three_quarter (t : ℝ) (ht : 0 ≤ t) :
    (t + 1) ^ (-(3/4) : ℝ) ≤ 4 * (t + 1) ^ ((1/4) : ℝ) - 4 * t ^ ((1/4) : ℝ) := by
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have hcube : ((t + 1) ^ ((1/4) : ℝ)) ^ 3 = (t + 1) ^ ((3/4) : ℝ) := by
    rw [rpow_pow_nat ht1.le, show ((1/4 : ℝ)) * ((3 : ℕ) : ℝ) = (3/4 : ℝ) by norm_num]
  have hinv : (t + 1) ^ (-(3/4) : ℝ) = ((t + 1) ^ ((3/4) : ℝ))⁻¹ := Real.rpow_neg ht1.le _
  rw [hinv, ← hcube]
  set a : ℝ := (t + 1) ^ ((1/4) : ℝ) with ha
  set b : ℝ := t ^ ((1/4) : ℝ) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos ht1 _
  have hb0 : (0 : ℝ) ≤ b := Real.rpow_nonneg ht _
  have ha4 : a ^ 4 = t + 1 := by
    rw [ha, rpow_pow_nat ht1.le, show ((1/4 : ℝ)) * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hb4 : b ^ 4 = t := by
    rw [hb, rpow_pow_nat ht, show ((1/4 : ℝ)) * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have ha3 : (0 : ℝ) < a ^ 3 := by positivity
  rw [inv_eq_one_div, div_le_iff₀ ha3]
  nlinarith [mul_nonneg (sq_nonneg (a - b))
    (show (0 : ℝ) ≤ 3 * a ^ 2 + 2 * a * b + b ^ 2 by positivity), ha4, hb4]

/-- `Σ_{f ≤ N} f^{−3/4} ≤ 4·N^{1/4}`. -/
private lemma sum_rpow_neg_three_quarter_le (N : ℕ) :
    ∑ f ∈ Finset.Icc 1 N, (f : ℝ) ^ (-(3/4) : ℝ) ≤ 4 * (N : ℝ) ^ ((1/4) : ℝ) := by
  induction N with
  | zero => simp [Real.zero_rpow]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith [ih, rpow_step_three_quarter (m : ℝ) (by positivity)]

/-- `log u ≤ 4·u^{1/4}` for `u ≥ 1` — the device that trades the log of `H0d`'s weight for
a quarter power, which the `f^{−3/4}` sum then absorbs. -/
private lemma log_le_four_rpow_quarter {u : ℝ} (hu : 1 ≤ u) :
    Real.log u ≤ 4 * u ^ ((1/4) : ℝ) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have h1 : Real.log (u ^ ((1/4) : ℝ)) = (1/4 : ℝ) * Real.log u := Real.log_rpow hu0 _
  have h2 : Real.log (u ^ ((1/4) : ℝ)) ≤ u ^ ((1/4) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu0 _)
  have h3 : (0 : ℝ) ≤ u ^ ((1/4) : ℝ) := (Real.rpow_pos_of_pos hu0 _).le
  linarith

private lemma div_rpow_neg {Q e : ℝ} (hQ : 0 ≤ Q) (he : 0 ≤ e) (q : ℝ) :
    (Q / e) ^ q = Q ^ q * e ^ (-q) := by
  rw [div_eq_mul_inv, Real.mul_rpow hQ (inv_nonneg.mpr he), Real.inv_rpow he, Real.rpow_neg he]

/-- `Σ_{f ≤ m} 1/f ≤ 1 + log m` (mathlib's harmonic bound, cast to `ℝ`). -/
private lemma sum_inv_le_one_add_log (m : ℕ) :
    ∑ f ∈ Finset.Icc 1 m, ((f : ℝ))⁻¹ ≤ 1 + Real.log m := by
  have h := harmonic_le_one_add_log m
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-! ## The divisor-sum swap -/

/-- **The swap stone.** `Σ_{r ≤ N} Σ_{e ∣ r} F(e, r) = Σ_{e ≤ N} Σ_{f ≤ N/e} F(e, e·f)`:
`Finset.sum_comm'` moves `e` outside, then `CoprimeBV.sum_dvd_reindex` reindexes the
multiples of `e`. -/
private lemma sum_divisors_swap (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ r ∈ Finset.Icc 1 N, ∑ e ∈ r.divisors, F e r
      = ∑ e ∈ Finset.Icc 1 N, ∑ f ∈ Finset.Icc 1 (N / e), F e (e * f) := by
  have h1 : ∑ r ∈ Finset.Icc 1 N, ∑ e ∈ r.divisors, F e r
      = ∑ e ∈ Finset.Icc 1 N, ∑ r ∈ (Finset.Icc 1 N).filter (fun r => e ∣ r), F e r := by
    refine Finset.sum_comm' ?_
    intro r e
    simp only [Finset.mem_Icc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hr1, hrN⟩, hed, hr0⟩
      have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos hed (by omega)
      exact ⟨⟨⟨hr1, hrN⟩, hed⟩, he1, le_trans (Nat.le_of_dvd (by omega) hed) hrN⟩
    · rintro ⟨⟨⟨hr1, hrN⟩, hed⟩, _⟩
      exact ⟨⟨hr1, hrN⟩, hed, by omega⟩
  rw [h1]
  refine Finset.sum_congr rfl fun e he => ?_
  exact sum_dvd_reindex (Finset.mem_Icc.mp he).1 (fun r => F e r)

/-! ## H0b — the average of `σ_{−1/4}` -/

/-- **H0b.** `Σ_{r ≤ R} σ_{−1/4}(r) ≤ 5R`. Swap the divisor sum:
`Σ_{r ≤ N} Σ_{e ∣ r} e^{−1/4} = Σ_{e ≤ N} e^{−1/4}⌊N/e⌋ ≤ N·Σ_{e ≤ N} e^{−5/4} ≤ 5N ≤ 5R`
(the tail bound `Σ_e e^{−5/4} ≤ 1 + 4 = 5`). -/
theorem sum_sigmaQ_le (R : ℝ) (hR : 1 ≤ R) : ∑ r ∈ Finset.Icc 1 ⌊R⌋₊, sigmaQ r ≤ 5 * R := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hNR : ((⌊R⌋₊ : ℕ) : ℝ) ≤ R := Nat.floor_le hR0
  have hswap : ∑ r ∈ Finset.Icc 1 ⌊R⌋₊, sigmaQ r
      = ∑ e ∈ Finset.Icc 1 ⌊R⌋₊, ∑ _f ∈ Finset.Icc 1 (⌊R⌋₊ / e), (e : ℝ) ^ (-(1/4) : ℝ) :=
    sum_divisors_swap ⌊R⌋₊ (fun e _ => (e : ℝ) ^ (-(1/4) : ℝ))
  rw [hswap]
  have hstep : ∀ e ∈ Finset.Icc 1 ⌊R⌋₊,
      (∑ _f ∈ Finset.Icc 1 (⌊R⌋₊ / e), (e : ℝ) ^ (-(1/4) : ℝ)) ≤ R * (e : ℝ) ^ (-(5/4) : ℝ) := by
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
    have hcard : (∑ _f ∈ Finset.Icc 1 (⌊R⌋₊ / e), (e : ℝ) ^ (-(1/4) : ℝ))
        = ((⌊R⌋₊ / e : ℕ) : ℝ) * (e : ℝ) ^ (-(1/4) : ℝ) := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      norm_num
    have hdiv : ((⌊R⌋₊ / e : ℕ) : ℝ) ≤ R / (e : ℝ) := by
      rw [le_div_iff₀ he0]
      calc ((⌊R⌋₊ / e : ℕ) : ℝ) * (e : ℝ) = (((⌊R⌋₊ / e) * e : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((⌊R⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.div_mul_le_self _ _
        _ ≤ R := hNR
    have hexp : (e : ℝ) ^ (-(5/4) : ℝ) = (e : ℝ) ^ (-(1/4) : ℝ) / (e : ℝ) := by
      rw [show (-(5/4) : ℝ) = (-(1/4) : ℝ) + (-(1 : ℝ)) by norm_num, Real.rpow_add he0,
        Real.rpow_neg_one]
      ring
    rw [hcard, hexp]
    have hp : (0 : ℝ) ≤ (e : ℝ) ^ (-(1/4) : ℝ) := Real.rpow_nonneg he0.le _
    calc ((⌊R⌋₊ / e : ℕ) : ℝ) * (e : ℝ) ^ (-(1/4) : ℝ)
        ≤ (R / (e : ℝ)) * (e : ℝ) ^ (-(1/4) : ℝ) := by gcongr
      _ = R * ((e : ℝ) ^ (-(1/4) : ℝ) / (e : ℝ)) := by ring
  calc ∑ e ∈ Finset.Icc 1 ⌊R⌋₊, ∑ _f ∈ Finset.Icc 1 (⌊R⌋₊ / e), (e : ℝ) ^ (-(1/4) : ℝ)
      ≤ ∑ e ∈ Finset.Icc 1 ⌊R⌋₊, R * (e : ℝ) ^ (-(5/4) : ℝ) := Finset.sum_le_sum hstep
    _ = R * ∑ e ∈ Finset.Icc 1 ⌊R⌋₊, (e : ℝ) ^ (-(5/4) : ℝ) := by rw [Finset.mul_sum]
    _ ≤ R * 5 := by
        exact mul_le_mul_of_nonneg_left (sum_rpow_neg_five_quarter_le _) hR0
    _ = 5 * R := by ring

/-! ## H0e — the harmonic-weighted average of `σ_{−1/4}` -/

/-- **H0e.** `Σ_{t ≤ Q} σ_{−1/4}(t)/t ≤ 5(1 + log Q)`: the same swap, with the inner sum
now harmonic (`Σ_{f ≤ N/e} 1/f ≤ 1 + log N`) and the outer weight `e^{−5/4}`. -/
theorem sum_sigmaQ_div_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q →
    ∑ t ∈ Finset.Icc 1 ⌊Q⌋₊, sigmaQ t / t ≤ C * (1 + Real.log Q) := by
  refine ⟨5, by norm_num, fun Q hQ => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hNQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQ0.le
  have hN1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
  have hlogQ : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg hQ
  have hrew : ∀ t : ℕ, sigmaQ t / (t : ℝ) = ∑ e ∈ t.divisors, (e : ℝ) ^ (-(1/4) : ℝ) / (t : ℝ) := by
    intro t; rw [sigmaQ, Finset.sum_div]
  have hswap : ∑ t ∈ Finset.Icc 1 ⌊Q⌋₊, sigmaQ t / (t : ℝ)
      = ∑ e ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ f ∈ Finset.Icc 1 (⌊Q⌋₊ / e),
          (e : ℝ) ^ (-(1/4) : ℝ) / (((e * f : ℕ)) : ℝ) := by
    rw [Finset.sum_congr rfl (fun t _ => hrew t)]
    exact sum_divisors_swap ⌊Q⌋₊ (fun e r => (e : ℝ) ^ (-(1/4) : ℝ) / (r : ℝ))
  rw [hswap]
  have hstep : ∀ e ∈ Finset.Icc 1 ⌊Q⌋₊,
      (∑ f ∈ Finset.Icc 1 (⌊Q⌋₊ / e), (e : ℝ) ^ (-(1/4) : ℝ) / (((e * f : ℕ)) : ℝ))
        ≤ (e : ℝ) ^ (-(5/4) : ℝ) * (1 + Real.log Q) := by
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have heN : e ≤ ⌊Q⌋₊ := (Finset.mem_Icc.mp he).2
    have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
    have hexp : (e : ℝ) ^ (-(5/4) : ℝ) = (e : ℝ) ^ (-(1/4) : ℝ) / (e : ℝ) := by
      rw [show (-(5/4) : ℝ) = (-(1/4) : ℝ) + (-(1 : ℝ)) by norm_num, Real.rpow_add he0,
        Real.rpow_neg_one]
      ring
    have hp : (0 : ℝ) < (e : ℝ) ^ (-(1/4) : ℝ) := Real.rpow_pos_of_pos he0 _
    have hinner : (∑ f ∈ Finset.Icc 1 (⌊Q⌋₊ / e), (e : ℝ) ^ (-(1/4) : ℝ) / (((e * f : ℕ)) : ℝ))
        = ((e : ℝ) ^ (-(1/4) : ℝ) / (e : ℝ))
            * ∑ f ∈ Finset.Icc 1 (⌊Q⌋₊ / e), ((f : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      have hf1 : 1 ≤ f := (Finset.mem_Icc.mp hf).1
      have hf0 : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf1
      push_cast
      field_simp
    have hharm : (∑ f ∈ Finset.Icc 1 (⌊Q⌋₊ / e), ((f : ℝ))⁻¹) ≤ 1 + Real.log Q := by
      refine le_trans (sum_inv_le_one_add_log _) ?_
      have h1 : ((⌊Q⌋₊ / e : ℕ) : ℝ) ≤ Q := by
        refine le_trans ?_ hNQ
        exact_mod_cast Nat.div_le_self _ _
      rcases Nat.eq_zero_or_pos (⌊Q⌋₊ / e) with h0 | hpos
      · rw [h0]; simp [hlogQ]
      · have : (0 : ℝ) < ((⌊Q⌋₊ / e : ℕ) : ℝ) := by exact_mod_cast hpos
        have := Real.log_le_log this h1
        linarith
    rw [hinner, hexp]
    exact mul_le_mul_of_nonneg_left hharm (by positivity)
  calc ∑ e ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ f ∈ Finset.Icc 1 (⌊Q⌋₊ / e),
        (e : ℝ) ^ (-(1/4) : ℝ) / (((e * f : ℕ)) : ℝ)
      ≤ ∑ e ∈ Finset.Icc 1 ⌊Q⌋₊, (e : ℝ) ^ (-(5/4) : ℝ) * (1 + Real.log Q) :=
        Finset.sum_le_sum hstep
    _ = (∑ e ∈ Finset.Icc 1 ⌊Q⌋₊, (e : ℝ) ^ (-(5/4) : ℝ)) * (1 + Real.log Q) := by
        rw [Finset.sum_mul]
    _ ≤ 5 * (1 + Real.log Q) := by
        exact mul_le_mul_of_nonneg_right (sum_rpow_neg_five_quarter_le _) (by linarith)


/-! ## H0c — `Σ_{n ≤ Q} 1/(n·log²(2Q/n))` is bounded -/

/-- The telescoping engine of H0c. On `2 ≤ n ≤ Q`, `log(2Q/(n−1)) ≤ 2·log(2Q/n)` (the gap is
`log(n/(n−1)) ≤ log 2 ≤ log(2Q/n)`) and `log(n/(n−1)) ≥ 1/n`, so
`1/(n·log²(2Q/n)) ≤ 2(1/log(2Q/n) − 1/log(2Q/(n−1)))` and the sum telescopes to
`2/log(2Q/N) ≤ 2/log 2`. No integral comparison is used: the summand is NOT monotone in
`n` on the whole range (its denominator turns over at `2Q/n = e²`). -/
private lemma sum_inv_mul_log_sq_tail {Q : ℝ} (hQ : 1 ≤ Q) {N : ℕ} (hN : (N : ℝ) ≤ Q) :
    ∀ m : ℕ, 1 ≤ m → m ≤ N →
      ∑ n ∈ Finset.Icc 2 m, 1 / ((n : ℝ) * Real.log (2 * Q / n) ^ 2)
        ≤ 2 * (1 / Real.log (2 * Q / (m : ℝ)) - 1 / Real.log (2 * Q)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro _
    rw [show Finset.Icc 2 1 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega)]
    norm_num
  | succ m hm ih =>
    intro hmN
    have ihm := ih (by omega)
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1)]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    have hmQ : (m : ℝ) + 1 ≤ Q := by
      have h : ((m + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
      rw [hcast] at h; linarith
    set u : ℝ := Real.log (2 * Q / ((m : ℝ) + 1)) with hu_def
    set v : ℝ := Real.log (2 * Q / (m : ℝ)) with hv_def
    have hu2 : (2 : ℝ) ≤ 2 * Q / ((m : ℝ) + 1) := by
      rw [le_div_iff₀ hm1]; linarith
    have hu : Real.log 2 ≤ u := Real.log_le_log (by norm_num) hu2
    have hu0 : 0 < u := lt_of_lt_of_le hlog2 hu
    have hratio_lower : 1 / ((m : ℝ) + 1) ≤ Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
      have hpos : (0 : ℝ) < (m : ℝ) / ((m : ℝ) + 1) := by positivity
      have hle : (m : ℝ) / ((m : ℝ) + 1) ≤ Real.exp (-(1 / ((m : ℝ) + 1))) := by
        have heq : (m : ℝ) / ((m : ℝ) + 1) = -(1 / ((m : ℝ) + 1)) + 1 := by field_simp; ring
        rw [heq]; exact Real.add_one_le_exp _
      have hlog := (Real.log_le_iff_le_exp hpos).mpr hle
      have hs1 : Real.log ((m : ℝ) / ((m : ℝ) + 1)) = Real.log (m : ℝ) - Real.log ((m : ℝ) + 1) :=
        Real.log_div hm0.ne' hm1.ne'
      have hs2 : Real.log (((m : ℝ) + 1) / (m : ℝ)) = Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) :=
        Real.log_div hm1.ne' hm0.ne'
      linarith
    have hratio_upper : Real.log (((m : ℝ) + 1) / (m : ℝ)) ≤ Real.log 2 := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ hm0]
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hvu : v = u + Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
      rw [hv_def, hu_def, ← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have hv0 : 0 < v := by
      have : (0 : ℝ) ≤ Real.log (((m : ℝ) + 1) / (m : ℝ)) := le_trans (by positivity) hratio_lower
      linarith
    have hB : v ≤ 2 * u := by linarith
    have hA : (1 : ℝ) ≤ (v - u) * ((m : ℝ) + 1) := by
      have hd : 1 / ((m : ℝ) + 1) ≤ v - u := by rw [hvu]; linarith
      calc (1 : ℝ) = (1 / ((m : ℝ) + 1)) * ((m : ℝ) + 1) := by field_simp
        _ ≤ (v - u) * ((m : ℝ) + 1) := by gcongr
    have hstep : 1 / (((m : ℝ) + 1) * u ^ 2) ≤ 2 * (1 / u - 1 / v) := by
      have hrw : 2 * (1 / u - 1 / v) = (2 * (v - u)) / (u * v) := by field_simp
      rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
      have e1 : u ^ 2 * 1 ≤ u ^ 2 * ((v - u) * ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      have e2 : u * v ≤ u * (2 * u) := mul_le_mul_of_nonneg_left hB hu0.le
      nlinarith [e1, e2]
    linarith [ihm, hstep]

/-- **H0c (An Lemma 3.4, first form).** `Σ_{n ≤ Q} 1/(n·log²(2Q/n)) ≤ C` for every `Q ≥ 1`,
with `C = 1/log²2 + 2/log 2`. The `n = 1` term is `1/log²(2Q) ≤ 1/log²2`; the rest
telescopes. -/
theorem sum_inv_mul_log_sq_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q →
    ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, 1 / ((n : ℝ) * Real.log (2 * Q / n) ^ 2) ≤ C := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / Real.log 2 ^ 2 + 2 / Real.log 2,
    add_pos (div_pos one_pos (pow_pos hlog2 2)) (div_pos two_pos hlog2), fun Q hQ => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hNQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQ0.le
  have hN1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
  have hN0 : (0 : ℝ) < ((⌊Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN1
  have hins : Finset.Icc 1 ⌊Q⌋₊ = insert 1 (Finset.Icc 2 ⌊Q⌋₊) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hins, Finset.sum_insert (by simp)]
  have hterm1 : 1 / (((1 : ℕ) : ℝ) * Real.log (2 * Q / ((1 : ℕ) : ℝ)) ^ 2)
      ≤ 1 / Real.log 2 ^ 2 := by
    have h2Q : (2 : ℝ) ≤ 2 * Q := by linarith
    have hlog : Real.log 2 ≤ Real.log (2 * Q) := Real.log_le_log (by norm_num) h2Q
    have hsq : Real.log 2 ^ 2 ≤ Real.log (2 * Q) ^ 2 := by nlinarith
    simp only [Nat.cast_one, div_one, one_mul]
    exact one_div_le_one_div_of_le (pow_pos hlog2 2) hsq
  have htail := sum_inv_mul_log_sq_tail hQ hNQ ⌊Q⌋₊ hN1 le_rfl
  have hNlog : Real.log 2 ≤ Real.log (2 * Q / ((⌊Q⌋₊ : ℕ) : ℝ)) := by
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ hN0]; linarith
  have hNlogpos : (0 : ℝ) < Real.log (2 * Q / ((⌊Q⌋₊ : ℕ) : ℝ)) := lt_of_lt_of_le hlog2 hNlog
  have hbound1 : 1 / Real.log (2 * Q / ((⌊Q⌋₊ : ℕ) : ℝ)) ≤ 1 / Real.log 2 :=
    one_div_le_one_div_of_le hlog2 hNlog
  have hbound2 : (0 : ℝ) ≤ 1 / Real.log (2 * Q) := by
    have h2Q : (2 : ℝ) ≤ 2 * Q := by linarith
    have : (0 : ℝ) < Real.log (2 * Q) := lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) h2Q)
    positivity
  have hsum2 : (∑ n ∈ Finset.Icc 2 ⌊Q⌋₊, 1 / ((n : ℝ) * Real.log (2 * Q / n) ^ 2))
      ≤ 2 * (1 / Real.log 2) := le_trans htail (by linarith)
  refine le_trans (add_le_add hterm1 hsum2) (le_of_eq (by ring))

/-! ## H0d — the dyadic `Q^{1/2}` bound that feeds `ΣD` -/

/-- The one-variable core of H0d: `Σ_{f ≤ M} f^{−1/2}·log(2Y/f) ≤ (2 log 2 + 16)·Y^{1/2}`
whenever `M ≤ Y`. The log is traded for a quarter power (`log u ≤ 4u^{1/4}`), which the
`f^{−3/4}` sum absorbs — this is where the exponent `−1/4` of `σ` becomes load-bearing. -/
private lemma sum_rpow_neg_half_log_le {Y : ℝ} (hY : 1 ≤ Y) {M : ℕ} (hM : (M : ℝ) ≤ Y) :
    ∑ f ∈ Finset.Icc 1 M, (f : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * Y / (f : ℝ))
      ≤ (2 * Real.log 2 + 16) * Y ^ ((1/2) : ℝ) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hbound : ∀ f ∈ Finset.Icc 1 M,
      (f : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * Y / (f : ℝ))
        ≤ Real.log 2 * (f : ℝ) ^ (-(1/2) : ℝ)
          + 4 * Y ^ ((1/4) : ℝ) * (f : ℝ) ^ (-(3/4) : ℝ) := by
    intro f hf
    have hf1 : 1 ≤ f := (Finset.mem_Icc.mp hf).1
    have hfM : f ≤ M := (Finset.mem_Icc.mp hf).2
    have hf0 : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf1
    have hfY : (f : ℝ) ≤ Y := le_trans (by exact_mod_cast hfM) hM
    have hYf1 : (1 : ℝ) ≤ Y / (f : ℝ) := (one_le_div hf0).mpr hfY
    have hsplit : Real.log (2 * Y / (f : ℝ)) = Real.log 2 + Real.log (Y / (f : ℝ)) := by
      rw [show 2 * Y / (f : ℝ) = 2 * (Y / (f : ℝ)) by ring,
        Real.log_mul (by norm_num) (by positivity)]
    have hlogb : Real.log (Y / (f : ℝ)) ≤ 4 * (Y / (f : ℝ)) ^ ((1/4) : ℝ) :=
      log_le_four_rpow_quarter hYf1
    have hdr : (Y / (f : ℝ)) ^ ((1/4) : ℝ) = Y ^ ((1/4) : ℝ) * (f : ℝ) ^ (-(1/4) : ℝ) :=
      div_rpow_neg hY0.le hf0.le _
    have hmul : (f : ℝ) ^ (-(1/2) : ℝ) * (f : ℝ) ^ (-(1/4) : ℝ) = (f : ℝ) ^ (-(3/4) : ℝ) := by
      rw [← Real.rpow_add hf0, show (-(1/2 : ℝ)) + (-(1/4 : ℝ)) = (-(3/4) : ℝ) by norm_num]
    have hfp : (0 : ℝ) < (f : ℝ) ^ (-(1/2) : ℝ) := Real.rpow_pos_of_pos hf0 _
    rw [hsplit, mul_add]
    have hstep : (f : ℝ) ^ (-(1/2) : ℝ) * Real.log (Y / (f : ℝ))
        ≤ 4 * Y ^ ((1/4) : ℝ) * (f : ℝ) ^ (-(3/4) : ℝ) := by
      calc (f : ℝ) ^ (-(1/2) : ℝ) * Real.log (Y / (f : ℝ))
          ≤ (f : ℝ) ^ (-(1/2) : ℝ) * (4 * (Y / (f : ℝ)) ^ ((1/4) : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogb hfp.le
        _ = 4 * Y ^ ((1/4) : ℝ) * ((f : ℝ) ^ (-(1/2) : ℝ) * (f : ℝ) ^ (-(1/4) : ℝ)) := by
            rw [hdr]; ring
        _ = 4 * Y ^ ((1/4) : ℝ) * (f : ℝ) ^ (-(3/4) : ℝ) := by rw [hmul]
    have hcomm : (f : ℝ) ^ (-(1/2) : ℝ) * Real.log 2 = Real.log 2 * (f : ℝ) ^ (-(1/2) : ℝ) := by
      ring
    linarith [hstep, hcomm.le, hcomm.ge]
  have hMY2 : ((M : ℕ) : ℝ) ^ ((1/2) : ℝ) ≤ Y ^ ((1/2) : ℝ) :=
    Real.rpow_le_rpow (by positivity) hM (by norm_num)
  have hMY4 : ((M : ℕ) : ℝ) ^ ((1/4) : ℝ) ≤ Y ^ ((1/4) : ℝ) :=
    Real.rpow_le_rpow (by positivity) hM (by norm_num)
  have hYY : Y ^ ((1/4) : ℝ) * Y ^ ((1/4) : ℝ) = Y ^ ((1/2) : ℝ) := by
    rw [← Real.rpow_add hY0, show ((1/4 : ℝ)) + ((1/4 : ℝ)) = ((1/2) : ℝ) by norm_num]
  have hY4 : (0 : ℝ) ≤ Y ^ ((1/4) : ℝ) := Real.rpow_nonneg hY0.le _
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc ∑ f ∈ Finset.Icc 1 M, (f : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * Y / (f : ℝ))
      ≤ ∑ f ∈ Finset.Icc 1 M, (Real.log 2 * (f : ℝ) ^ (-(1/2) : ℝ)
          + 4 * Y ^ ((1/4) : ℝ) * (f : ℝ) ^ (-(3/4) : ℝ)) := Finset.sum_le_sum hbound
    _ = Real.log 2 * (∑ f ∈ Finset.Icc 1 M, (f : ℝ) ^ (-(1/2) : ℝ))
          + 4 * Y ^ ((1/4) : ℝ) * (∑ f ∈ Finset.Icc 1 M, (f : ℝ) ^ (-(3/4) : ℝ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ Real.log 2 * (2 * ((M : ℕ) : ℝ) ^ ((1/2) : ℝ))
          + 4 * Y ^ ((1/4) : ℝ) * (4 * ((M : ℕ) : ℝ) ^ ((1/4) : ℝ)) := by
        gcongr
        · exact sum_rpow_neg_half_le M
        · exact sum_rpow_neg_three_quarter_le M
    _ ≤ Real.log 2 * (2 * Y ^ ((1/2) : ℝ)) + 4 * Y ^ ((1/4) : ℝ) * (4 * Y ^ ((1/4) : ℝ)) := by
        gcongr
    _ = (2 * Real.log 2 + 16) * Y ^ ((1/2) : ℝ) := by rw [← hYY]; ring

/-- **H0d (the dyadic bound of An §A.5; feeds `ΣD`).**
`Σ_{r ≤ Q} r^{−1/2}·log(2Q/r)·σ_{−1/4}(r) ≤ C·Q^{1/2}` with `C = 5(2 log 2 + 16)`.
Swap the divisor sum, write `r = e·f`, and the inner sum is the one-variable core at
`Y = Q/e`; the outer weight is `e^{−3/4}·(Q/e)^{1/2} = Q^{1/2}·e^{−5/4}`.

**The must-FAIL control.** Sharpening the exponent to `C·Q^{1/4}` makes the row FALSE:
`Σ_{r ≤ Q} r^{−1/2}·log(2Q/r)·σ_{−1/4}(r)/Q^{1/4}` measures
`8.75 / 33.78 / 87.92 / 191.56 / 381.05 / 721.55` at `Q = 10 / 10² / 10³ / 10⁴ / 10⁵ / 10⁶`
— unbounded — against `/Q^{1/2}` = `4.918 / 10.683 / 15.635 / 19.156 / 21.428 / 22.817`,
which is bounded. The exponent `1/2` here is what `ΣD` needs at `u ≈ z²`; the naive route
(`|{X/e}| ≤ 1` per divisor, error `√M·d(r)`) costs a log and fails there. -/
theorem sum_rpow_neg_half_log_sigmaQ_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q →
    ∑ r ∈ Finset.Icc 1 ⌊Q⌋₊, (r : ℝ) ^ (-(1/2 : ℝ)) * Real.log (2 * Q / r) * sigmaQ r
      ≤ C * Q ^ (1/2 : ℝ) := by
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨5 * (2 * Real.log 2 + 16), by linarith, fun Q hQ => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hNQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQ0.le
  have hrew : ∀ r : ℕ, (r : ℝ) ^ (-(1/2 : ℝ)) * Real.log (2 * Q / r) * sigmaQ r
      = ∑ e ∈ r.divisors,
          (r : ℝ) ^ (-(1/2 : ℝ)) * Real.log (2 * Q / r) * (e : ℝ) ^ (-(1/4 : ℝ)) := by
    intro r; rw [sigmaQ, Finset.mul_sum]
  have hswap : ∑ r ∈ Finset.Icc 1 ⌊Q⌋₊,
        (r : ℝ) ^ (-(1/2 : ℝ)) * Real.log (2 * Q / r) * sigmaQ r
      = ∑ e ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ f ∈ Finset.Icc 1 (⌊Q⌋₊ / e),
          (((e * f : ℕ)) : ℝ) ^ (-(1/2 : ℝ)) * Real.log (2 * Q / ((e * f : ℕ) : ℝ))
            * (e : ℝ) ^ (-(1/4 : ℝ)) := by
    rw [Finset.sum_congr rfl (fun r _ => hrew r)]
    exact sum_divisors_swap ⌊Q⌋₊
      (fun e r => (r : ℝ) ^ (-(1/2 : ℝ)) * Real.log (2 * Q / r) * (e : ℝ) ^ (-(1/4 : ℝ)))
  rw [hswap]
  have hstep : ∀ e ∈ Finset.Icc 1 ⌊Q⌋₊,
      (∑ f ∈ Finset.Icc 1 (⌊Q⌋₊ / e),
        (((e * f : ℕ)) : ℝ) ^ (-(1/2 : ℝ)) * Real.log (2 * Q / ((e * f : ℕ) : ℝ))
          * (e : ℝ) ^ (-(1/4 : ℝ)))
        ≤ (2 * Real.log 2 + 16) * Q ^ (1/2 : ℝ) * (e : ℝ) ^ (-(5/4 : ℝ)) := by
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have heN : e ≤ ⌊Q⌋₊ := (Finset.mem_Icc.mp he).2
    have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
    have heQ : (e : ℝ) ≤ Q := le_trans (by exact_mod_cast heN) hNQ
    have hY1 : (1 : ℝ) ≤ Q / (e : ℝ) := (one_le_div he0).mpr heQ
    have hMY : ((⌊Q⌋₊ / e : ℕ) : ℝ) ≤ Q / (e : ℝ) := by
      rw [le_div_iff₀ he0]
      calc ((⌊Q⌋₊ / e : ℕ) : ℝ) * (e : ℝ) = (((⌊Q⌋₊ / e) * e : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.div_mul_le_self _ _
        _ ≤ Q := hNQ
    have hterm : ∀ f ∈ Finset.Icc 1 (⌊Q⌋₊ / e),
        (((e * f : ℕ)) : ℝ) ^ (-(1/2 : ℝ)) * Real.log (2 * Q / ((e * f : ℕ) : ℝ))
            * (e : ℝ) ^ (-(1/4 : ℝ))
          = (e : ℝ) ^ (-(3/4 : ℝ))
              * ((f : ℝ) ^ (-(1/2 : ℝ)) * Real.log (2 * (Q / (e : ℝ)) / (f : ℝ))) := by
      intro f hf
      have hf1 : 1 ≤ f := (Finset.mem_Icc.mp hf).1
      have hf0 : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf1
      have hcast : (((e * f : ℕ)) : ℝ) = (e : ℝ) * (f : ℝ) := by push_cast; ring
      have hsplit : ((e : ℝ) * (f : ℝ)) ^ (-(1/2 : ℝ))
          = (e : ℝ) ^ (-(1/2 : ℝ)) * (f : ℝ) ^ (-(1/2 : ℝ)) :=
        Real.mul_rpow he0.le hf0.le
      have harg : 2 * Q / ((e : ℝ) * (f : ℝ)) = 2 * (Q / (e : ℝ)) / (f : ℝ) := by
        field_simp
      have hmul : (e : ℝ) ^ (-(1/2 : ℝ)) * (e : ℝ) ^ (-(1/4 : ℝ)) = (e : ℝ) ^ (-(3/4 : ℝ)) := by
        rw [← Real.rpow_add he0, show (-(1/2 : ℝ)) + (-(1/4 : ℝ)) = (-(3/4) : ℝ) by norm_num]
      rw [hcast, hsplit, harg, ← hmul]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hcore := sum_rpow_neg_half_log_le hY1 hMY
    have hep : (0 : ℝ) < (e : ℝ) ^ (-(3/4 : ℝ)) := Real.rpow_pos_of_pos he0 _
    have hQe : (Q / (e : ℝ)) ^ ((1/2) : ℝ) = Q ^ ((1/2) : ℝ) * (e : ℝ) ^ (-(1/2) : ℝ) :=
      div_rpow_neg hQ0.le he0.le _
    have hcomb : (e : ℝ) ^ (-(3/4 : ℝ)) * (e : ℝ) ^ (-(1/2) : ℝ) = (e : ℝ) ^ (-(5/4 : ℝ)) := by
      rw [← Real.rpow_add he0, show (-(3/4 : ℝ)) + (-(1/2 : ℝ)) = (-(5/4) : ℝ) by norm_num]
    calc (e : ℝ) ^ (-(3/4 : ℝ))
          * ∑ f ∈ Finset.Icc 1 (⌊Q⌋₊ / e), (f : ℝ) ^ (-(1/2 : ℝ))
              * Real.log (2 * (Q / (e : ℝ)) / (f : ℝ))
        ≤ (e : ℝ) ^ (-(3/4 : ℝ)) * ((2 * Real.log 2 + 16) * (Q / (e : ℝ)) ^ ((1/2) : ℝ)) :=
          mul_le_mul_of_nonneg_left hcore hep.le
      _ = (2 * Real.log 2 + 16) * Q ^ ((1/2) : ℝ)
            * ((e : ℝ) ^ (-(3/4 : ℝ)) * (e : ℝ) ^ (-(1/2) : ℝ)) := by rw [hQe]; ring
      _ = (2 * Real.log 2 + 16) * Q ^ (1/2 : ℝ) * (e : ℝ) ^ (-(5/4 : ℝ)) := by rw [hcomb]
  have hQhalf : (0 : ℝ) ≤ Q ^ (1/2 : ℝ) := Real.rpow_nonneg hQ0.le _
  calc ∑ e ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ f ∈ Finset.Icc 1 (⌊Q⌋₊ / e),
        (((e * f : ℕ)) : ℝ) ^ (-(1/2 : ℝ)) * Real.log (2 * Q / ((e * f : ℕ) : ℝ))
          * (e : ℝ) ^ (-(1/4 : ℝ))
      ≤ ∑ e ∈ Finset.Icc 1 ⌊Q⌋₊, (2 * Real.log 2 + 16) * Q ^ (1/2 : ℝ) * (e : ℝ) ^ (-(5/4 : ℝ)) :=
        Finset.sum_le_sum hstep
    _ = (2 * Real.log 2 + 16) * Q ^ (1/2 : ℝ)
          * ∑ e ∈ Finset.Icc 1 ⌊Q⌋₊, (e : ℝ) ^ (-(5/4 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (2 * Real.log 2 + 16) * Q ^ (1/2 : ℝ) * 5 := by
        refine mul_le_mul_of_nonneg_left (sum_rpow_neg_five_quarter_le _) ?_
        have : (0 : ℝ) ≤ 2 * Real.log 2 + 16 := by linarith
        positivity
    _ = 5 * (2 * Real.log 2 + 16) * Q ^ (1/2 : ℝ) := by ring

end Salt.SW
