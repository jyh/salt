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


/-! ## H6a — the bare Möbius sum with a power-of-log saving -/

/-- **H6a (An (3.1) over `ℚ`).** `|Σ_{n ≤ Q} μ(n)| ≤ C·Q/(log 2Q)^A` for every `A > 0`.
This is the landed `mmuRate_holds` re-windowed onto a REAL cut-off: the sum is
`Mmu ⌊Q⌋₊`, `⌊Q⌋₊ ≤ Q`, and `log(2Q) ≤ 2·log ⌊Q⌋₊` once `⌊Q⌋₊ ≥ 4` (`2Q < 4⌊Q⌋₊ ≤ ⌊Q⌋₊²`),
so the `A`-th powers differ by at most `2^A`. Below `max(x₀, 4)` the trivial `|Σ| ≤ ⌊Q⌋₊ ≤ Q`
covers the row and the finite window is absorbed into `C`.

The constant is NON-EFFECTIVE: it is `max(C₀·2^A, log(2(N₀+1))^A)` where `C₀` and the window
`x₀` come from `mmuRate_holds` at the same `A`, and no numeral for `x₀` is extracted
anywhere in the corpus. -/
theorem abs_sum_moebius_le_div_log_pow (A : ℝ) (hA : 0 < A) : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q →
    |∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ)| ≤ C * Q / Real.log (2 * Q) ^ A := by
  obtain ⟨C₀, x₀, hC₀, hb⟩ := mmuRate_holds A hA
  set N₀ : ℕ := max x₀ 4 with hN₀def
  have hN₀4 : 4 ≤ N₀ := le_max_right x₀ 4
  have hlogpos : (0 : ℝ) < Real.log (2 * ((N₀ : ℝ) + 1)) := by
    refine Real.log_pos ?_
    have : (4 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀4
    linarith
  set C : ℝ := max (C₀ * 2 ^ A) (Real.log (2 * ((N₀ : ℝ) + 1)) ^ A) with hCdef
  have h2A : (0 : ℝ) < 2 ^ A := Real.rpow_pos_of_pos (by norm_num) _
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C, hCpos, fun Q hQ => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by linarith
  set n : ℕ := ⌊Q⌋₊ with hndef
  have hnQ : ((n : ℕ) : ℝ) ≤ Q := Nat.floor_le hQ0.le
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hQ)
  have hQn : Q < (n : ℝ) + 1 := by
    have := Nat.lt_floor_add_one Q
    exact_mod_cast this
  have h2Q : (2 : ℝ) ≤ 2 * Q := by linarith
  have hlog2Q : (0 : ℝ) < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hpowpos : (0 : ℝ) < Real.log (2 * Q) ^ A := Real.rpow_pos_of_pos hlog2Q _
  have hMmu : ∑ k ∈ Finset.Icc 1 n, (moebius k : ℝ) = Salt.TwinBar.Mmu n := rfl
  rcases le_or_gt N₀ n with hbig | hsmall
  · -- the rate's window
    have hx0n : x₀ ≤ n := le_trans (le_max_left x₀ 4) hbig
    have hn4 : 4 ≤ n := le_trans hN₀4 hbig
    have hnR4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    have hlogn : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hcmp : Real.log (2 * Q) ≤ 2 * Real.log (n : ℝ) := by
      have hstep : 2 * Q ≤ (n : ℝ) * (n : ℝ) := by nlinarith
      calc Real.log (2 * Q) ≤ Real.log ((n : ℝ) * (n : ℝ)) :=
            Real.log_le_log (by linarith) hstep
        _ = 2 * Real.log (n : ℝ) := by
            rw [Real.log_mul (by linarith) (by linarith)]; ring
    have hpow : Real.log (2 * Q) ^ A ≤ 2 ^ A * Real.log (n : ℝ) ^ A := by
      have h1 : Real.log (2 * Q) ^ A ≤ (2 * Real.log (n : ℝ)) ^ A :=
        Real.rpow_le_rpow hlog2Q.le hcmp hA.le
      rwa [Real.mul_rpow (by norm_num) hlogn.le] at h1
    have hrate := hb n hx0n
    rw [hMmu]
    have hlognA : (0 : ℝ) < Real.log (n : ℝ) ^ A := Real.rpow_pos_of_pos hlogn _
    calc |Salt.TwinBar.Mmu n| ≤ C₀ * (n : ℝ) / Real.log (n : ℝ) ^ A := hrate
      _ ≤ C₀ * Q / Real.log (n : ℝ) ^ A := by
          gcongr
      _ = C₀ * 2 ^ A * Q / (2 ^ A * Real.log (n : ℝ) ^ A) := by
          field_simp
      _ ≤ C₀ * 2 ^ A * Q / Real.log (2 * Q) ^ A := by
          gcongr
      _ ≤ C * Q / Real.log (2 * Q) ^ A := by
          gcongr
          exact le_max_left _ _
  · -- the finite window: the trivial bound
    have htriv : |∑ k ∈ Finset.Icc 1 n, (moebius k : ℝ)| ≤ (n : ℝ) := by
      calc |∑ k ∈ Finset.Icc 1 n, (moebius k : ℝ)|
          ≤ ∑ k ∈ Finset.Icc 1 n, |(moebius k : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [← Int.cast_abs]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        _ = (n : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            norm_num
    have hQsmall : Q < (N₀ : ℝ) + 1 := by
      have : (n : ℝ) + 1 ≤ (N₀ : ℝ) + 1 := by
        have : (n : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast (by omega : n ≤ N₀)
        linarith
      linarith
    have hlogle : Real.log (2 * Q) ≤ Real.log (2 * ((N₀ : ℝ) + 1)) :=
      Real.log_le_log (by linarith) (by linarith)
    have hpowle : Real.log (2 * Q) ^ A ≤ Real.log (2 * ((N₀ : ℝ) + 1)) ^ A :=
      Real.rpow_le_rpow hlog2Q.le hlogle hA.le
    have hCge : Real.log (2 * ((N₀ : ℝ) + 1)) ^ A ≤ C := le_max_right _ _
    have hfinal : Q ≤ C * Q / Real.log (2 * Q) ^ A := by
      rw [le_div_iff₀ hpowpos]
      nlinarith [mul_le_mul_of_nonneg_left (le_trans hpowle hCge) hQ0.le]
    linarith [htriv, hnQ, hfinal]

/-! ## H4 — An's (5.2): the tail second moment as a four-parameter box -/

/-- The μ-factorisation, coprime case: on `(k, ab) = 1` the pair `μ(ak)μ(bk)` splits. -/
private lemma moebius_mul_moebius_of_coprime {a b k : ℕ} (hk : Nat.Coprime k (a * b)) :
    ((moebius (a * k) : ℤ) : ℝ) * ((moebius (b * k) : ℤ) : ℝ)
      = ((moebius a : ℤ) : ℝ) * ((moebius b : ℤ) : ℝ) * ((moebius k : ℤ) : ℝ) ^ 2 := by
  have hka : Nat.Coprime a k := (Nat.Coprime.coprime_dvd_right (dvd_mul_right a b) hk).symm
  have hkb : Nat.Coprime b k := (Nat.Coprime.coprime_dvd_right (dvd_mul_left b a) hk).symm
  have h1 : (moebius (a * k) : ℤ) = moebius a * moebius k :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hka
  have h2 : (moebius (b * k) : ℤ) = moebius b * moebius k :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hkb
  rw [h1, h2]; push_cast; ring

/-- The μ-factorisation, zero case: off `(k, ab) = 1` a prime `p ∣ k` divides `a` or `b`, so
`p² ∣ ak` or `p² ∣ bk` and the pair VANISHES. This is what makes the frozen filter
`(k, ab) = 1` an indicator rather than a restriction — it is load-bearing on the right-hand
side and vacuous on the left. -/
private lemma moebius_mul_moebius_eq_zero_of_not_coprime {a b k : ℕ}
    (hk : ¬ Nat.Coprime k (a * b)) :
    ((moebius (a * k) : ℤ) : ℝ) * ((moebius (b * k) : ℤ) : ℝ) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · simp
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := Nat.gcd k (a * b)) hk
  have hpk : p ∣ k := hpd.trans (Nat.gcd_dvd_left _ _)
  have hpab : p ∣ a * b := hpd.trans (Nat.gcd_dvd_right _ _)
  rcases (Nat.Prime.dvd_mul hp).mp hpab with hpa | hpb
  · have hnsq : ¬ Squarefree (a * k) := by
      intro hsq
      have hpp : p * p ∣ a * k := mul_dvd_mul hpa hpk
      have h1 := hsq p hpp
      rw [Nat.isUnit_iff] at h1
      exact hp.one_lt.ne' h1
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]; simp
  · have hnsq : ¬ Squarefree (b * k) := by
      intro hsq
      have hpp : p * p ∣ b * k := mul_dvd_mul hpb hpk
      have h1 := hsq p hpp
      rw [Nat.isUnit_iff] at h1
      exact hp.one_lt.ne' h1
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]; simp

/-- The arithmetic core of the forward leg `(n, d, d′) ↦ (g, a, b, k)`. With `e = n/d`,
`f = n/d′`, `g = gcd(e,f)`, `a = e/g`, `b = f/g`, `k = n/(gab)`: every coordinate is `≥ 1`,
`gabk = n` EXACTLY (because `gab = lcm(e,f) ∣ n`), `bk = d`, `ak = d′`, and `(a,b) = 1`. -/
private lemma h4_core {n d d' g a b k : ℕ} (hn : 1 ≤ n) (hd : d ∣ n) (hd' : d' ∣ n)
    (hgdef : g = Nat.gcd (n / d) (n / d')) (hadef : a = n / d / g) (hbdef : b = n / d' / g)
    (hkdef : k = n / (g * a * b)) :
    1 ≤ g ∧ 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ k ∧ g * a * b * k = n ∧ b * k = d ∧ a * k = d'
      ∧ Nat.Coprime a b := by
  have hn0 : n ≠ 0 := by omega
  have hde : d * (n / d) = n := Nat.mul_div_cancel' hd
  have hdf : d' * (n / d') = n := Nat.mul_div_cancel' hd'
  have he0 : 1 ≤ n / d := by
    rcases Nat.eq_zero_or_pos (n / d) with h | h
    · rw [h, mul_zero] at hde; omega
    · exact h
  have hf0 : 1 ≤ n / d' := by
    rcases Nat.eq_zero_or_pos (n / d') with h | h
    · rw [h, mul_zero] at hdf; omega
    · exact h
  have hen : n / d ∣ n := ⟨d, by rw [mul_comm]; exact hde.symm⟩
  have hfn : n / d' ∣ n := ⟨d', by rw [mul_comm]; exact hdf.symm⟩
  have hg0 : 1 ≤ g := by
    rw [hgdef]
    rcases Nat.eq_zero_or_pos (Nat.gcd (n / d) (n / d')) with h | h
    · rw [Nat.gcd_eq_zero_iff] at h; omega
    · exact h
  have hgae : g * a = n / d := by
    rw [hadef, hgdef]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hgbf : g * b = n / d' := by
    rw [hbdef, hgdef]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have ha0 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, mul_zero] at hgae; omega
    · exact h
  have hb0 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, mul_zero] at hgbf; omega
    · exact h
  have hab : Nat.Coprime a b := by
    rw [hadef, hbdef, hgdef]
    exact Nat.coprime_div_gcd_div_gcd (by omega)
  have heb : (n / d) * b = Nat.lcm (n / d) (n / d') := by
    have h1 : g * ((n / d) * b) = (n / d) * (n / d') := by rw [← hgbf]; ring
    have h2 : g * Nat.lcm (n / d) (n / d') = (n / d) * (n / d') := by
      rw [hgdef]; exact Nat.gcd_mul_lcm _ _
    exact Nat.eq_of_mul_eq_mul_left (by omega) (h1.trans h2.symm)
  have hgabn : g * a * b ∣ n := by
    rw [hgae, heb]; exact Nat.lcm_dvd hen hfn
  have hgab0 : 0 < g * a * b := mul_pos (mul_pos hg0 ha0) hb0
  have hgabk : g * a * b * k = n := by rw [hkdef]; exact Nat.mul_div_cancel' hgabn
  have hk0 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hgabk; omega
    · exact h
  have hbk : b * k = d := by
    have h1 : (n / d) * (b * k) = n := by rw [← hgae, ← hgabk]; ring
    have h2 : (n / d) * d = n := by rw [mul_comm]; exact hde
    exact Nat.eq_of_mul_eq_mul_left (by omega) (h1.trans h2.symm)
  have hak : a * k = d' := by
    have h1 : (n / d') * (a * k) = n := by rw [← hgbf, ← hgabk]; ring
    have h2 : (n / d') * d' = n := by rw [mul_comm]; exact hdf
    exact Nat.eq_of_mul_eq_mul_left (by omega) (h1.trans h2.symm)
  exact ⟨hg0, ha0, hb0, hk0, hgabk, hbk, hak, hab⟩

/-- The arithmetic core of the inverse leg `(g, a, b, k) ↦ (gabk, bk, ak)`: the forward map
returns the four coordinates, using `gcd(ga, gb) = g·gcd(a,b) = g` on `(a,b) = 1`. -/
private lemma h4_core' {g a b k : ℕ} (hg : 1 ≤ g) (ha : 1 ≤ a) (hb : 1 ≤ b) (hk : 1 ≤ k)
    (hab : Nat.Coprime a b) :
    g * a * b * k / (b * k) = g * a ∧ g * a * b * k / (a * k) = g * b
      ∧ Nat.gcd (g * a) (g * b) = g ∧ g * a / g = a ∧ g * b / g = b
      ∧ g * a * b * k / (g * a * b) = k := by
  have hbk : 0 < b * k := mul_pos hb hk
  have hak : 0 < a * k := mul_pos ha hk
  have hgab : 0 < g * a * b := mul_pos (mul_pos hg ha) hb
  have hab1 : Nat.gcd a b = 1 := hab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show g * a * b * k = b * k * (g * a) by ring]; exact Nat.mul_div_cancel_left _ hbk
  · rw [show g * a * b * k = a * k * (g * b) by ring]; exact Nat.mul_div_cancel_left _ hak
  · rw [Nat.gcd_mul_left, hab1, mul_one]
  · exact Nat.mul_div_cancel_left _ hg
  · exact Nat.mul_div_cancel_left _ hg
  · exact Nat.mul_div_cancel_left _ hgab


/-- The left index set of H4's bijection: the triples `(n, d, d′)` with `d, d′ ∣ n` above the
level `z`, as a sigma-typed `Finset` (the divisor fibres depend on `n`). -/
private def h4L (z N : ℕ) : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 N).sigma (fun n =>
    ((Finset.Icc 1 N).filter (fun d => d ∣ n ∧ z < d)).sigma (fun _ =>
      (Finset.Icc 1 N).filter (fun d => d ∣ n ∧ z < d)))

/-- The right index set: the four-parameter box `(g, a, b, k)` **WITHOUT** the `k`-coprimality
(which is not automatic under the forward map — it holds exactly when `bk` and `ak` are
squarefree, and is restored by the summand's zero case, not by the index set). -/
private def h4R (z N : ℕ) : Finset (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 N).sigma (fun g =>
    (Finset.Icc 1 N).sigma (fun a =>
      ((Finset.Icc 1 N).filter (fun b => Nat.Coprime a b)).sigma (fun b =>
        (Finset.Icc 1 (N / (g * a * b))).filter (fun k => z < a * k ∧ z < b * k))))

/-- The forward leg `(n, d, d′) ↦ (g, a, b, k)`. -/
private def h4Fwd (q : Σ _ : ℕ, Σ _ : ℕ, ℕ) : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ :=
  ⟨Nat.gcd (q.1 / q.2.1) (q.1 / q.2.2),
   q.1 / q.2.1 / Nat.gcd (q.1 / q.2.1) (q.1 / q.2.2),
   q.1 / q.2.2 / Nat.gcd (q.1 / q.2.1) (q.1 / q.2.2),
   q.1 / (Nat.gcd (q.1 / q.2.1) (q.1 / q.2.2)
     * (q.1 / q.2.1 / Nat.gcd (q.1 / q.2.1) (q.1 / q.2.2))
     * (q.1 / q.2.2 / Nat.gcd (q.1 / q.2.1) (q.1 / q.2.2)))⟩

/-- The inverse leg `(g, a, b, k) ↦ (gabk, bk, ak)`. -/
private def h4Bwd (w : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) : Σ _ : ℕ, Σ _ : ℕ, ℕ :=
  ⟨w.1 * w.2.1 * w.2.2.1 * w.2.2.2, w.2.2.1 * w.2.2.2, w.2.1 * w.2.2.2⟩

/-- The left summand `μ(d)log(d/z)·μ(d′)log(d′/z)`. -/
private noncomputable def h4F3 (z : ℕ) (q : Σ _ : ℕ, Σ _ : ℕ, ℕ) : ℝ :=
  ((moebius q.2.1 : ℝ) * Real.log ((q.2.1 : ℝ) / z))
    * ((moebius q.2.2 : ℝ) * Real.log ((q.2.2 : ℝ) / z))

/-- The right summand, with the `(k, ab) = 1` filter carried as an INDICATOR. -/
private noncomputable def h4F4 (z : ℕ) (w : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) : ℝ :=
  if Nat.Coprime w.2.2.2 (w.2.1 * w.2.2.1) then
    (moebius w.2.1 : ℝ) * (moebius w.2.2.1 : ℝ) *
      ((moebius w.2.2.2 : ℝ) ^ 2 * Real.log (((w.2.1 * w.2.2.2 : ℕ) : ℝ) / z)
        * Real.log (((w.2.2.1 * w.2.2.2 : ℕ) : ℝ) / z))
  else 0

/-- **H4 (An (5.2)).** The tail second moment, reindexed EXACTLY by the four-parameter
bijection `(n, d, d′) ↔ (g, a, b, k)` of the design freeze:
`e = n/d`, `f = n/d′`, `g = gcd(e,f)`, `a = e/g`, `b = f/g`, `k = n/(gab)`, with inverse
`n = gabk`, `d = bk`, `d′ = ak`. The constraints translate as
`d > z ↔ bk > z`, `d′ > z ↔ ak > z`, `n ≤ u ↔ k ≤ u/(gab)`, and `(a,b) = 1` is forced by
construction; every `(g,a,b)` with a nonempty `k`-range is `≤ u`, so the three outer ranges
are frozen loosely (and exactly) as `Icc 1 ⌊u⌋₊`.

**The filter `(k, ab) = 1` is LOAD-BEARING on the right and vacuous on the left.** It is an
indicator, not a restriction: off it, `μ(ak)μ(bk) = 0` because a prime dividing both `k` and
`ab` squares inside `ak` or `bk`. Dropping it makes the identity FALSE. Receipt: at
`(z, u) = (2, 6)` all three agree (`1.484444`; no such `k` is in range); at `(z, u) = (2, 12)`
the left side and the FILTERED right side are `7.085333` while the unfiltered right side is
`3.451733`; at `(z, u) = (3, 20)` the pair is `15.322721` against `8.963376`.

`hz` and `hu` are the freeze's binders; the identity is an exact reindexing and consumes
neither (outside them both sides are the empty sum), so they are recorded and not spent. -/
theorem sum_tailT_sq_eq {z : ℕ} (hz : 1 ≤ z) {u : ℝ} (hu : 1 ≤ u) :
    ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, tailT z n ^ 2
      = ∑ g ∈ Finset.Icc 1 ⌊u⌋₊, ∑ a ∈ Finset.Icc 1 ⌊u⌋₊,
          ∑ b ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun b => Nat.Coprime a b),
            (moebius a : ℝ) * (moebius b : ℝ) *
            ∑ k ∈ (Finset.Icc 1 (⌊u⌋₊ / (g * a * b))).filter
                    (fun k => Nat.Coprime k (a * b) ∧ z < a * k ∧ z < b * k),
              (moebius k : ℝ) ^ 2 * Real.log (((a * k : ℕ) : ℝ) / z)
                * Real.log (((b * k : ℕ) : ℝ) / z) := by
  have _hbinders : 1 ≤ z ∧ 1 ≤ u := ⟨hz, hu⟩
  -- the divisor fibre, rewritten inside the ambient box
  have hTset : ∀ n ∈ Finset.Icc 1 ⌊u⌋₊,
      n.divisors.filter (fun d => z < d)
        = (Finset.Icc 1 ⌊u⌋₊).filter (fun d => d ∣ n ∧ z < d) := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hdn, -⟩, hzd⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdn (by omega),
        le_trans (Nat.le_of_dvd (by omega) hdn) hnN⟩, hdn, hzd⟩
    · rintro ⟨-, hdn, hzd⟩
      exact ⟨⟨hdn, by omega⟩, hzd⟩
  have hstep1 : ∀ n ∈ Finset.Icc 1 ⌊u⌋₊, tailT z n ^ 2
      = ∑ d ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun d => d ∣ n ∧ z < d),
          ∑ d' ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun d => d ∣ n ∧ z < d),
            ((moebius d : ℝ) * Real.log ((d : ℝ) / z))
              * ((moebius d' : ℝ) * Real.log ((d' : ℝ) / z)) := by
    intro n hn
    simp only [tailT, hTset n hn]
    rw [pow_two]
    exact Finset.sum_mul_sum _ _ _ _
  have hL : ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, tailT z n ^ 2 = ∑ q ∈ h4L z ⌊u⌋₊, h4F3 z q := by
    calc ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, tailT z n ^ 2
        = ∑ n ∈ Finset.Icc 1 ⌊u⌋₊,
            ∑ d ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun d => d ∣ n ∧ z < d),
              ∑ d' ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun d => d ∣ n ∧ z < d),
                ((moebius d : ℝ) * Real.log ((d : ℝ) / z))
                  * ((moebius d' : ℝ) * Real.log ((d' : ℝ) / z)) :=
          Finset.sum_congr rfl hstep1
      _ = ∑ n ∈ Finset.Icc 1 ⌊u⌋₊,
            ∑ p ∈ ((Finset.Icc 1 ⌊u⌋₊).filter (fun d => d ∣ n ∧ z < d)).sigma
                    (fun _ => (Finset.Icc 1 ⌊u⌋₊).filter (fun d => d ∣ n ∧ z < d)),
              ((moebius p.1 : ℝ) * Real.log ((p.1 : ℝ) / z))
                * ((moebius p.2 : ℝ) * Real.log ((p.2 : ℝ) / z)) :=
          Finset.sum_congr rfl (fun n _ => Finset.sum_sigma'
            ((Finset.Icc 1 ⌊u⌋₊).filter (fun d => d ∣ n ∧ z < d))
            (fun _ => (Finset.Icc 1 ⌊u⌋₊).filter (fun d => d ∣ n ∧ z < d))
            (fun d d' => ((moebius d : ℝ) * Real.log ((d : ℝ) / z))
              * ((moebius d' : ℝ) * Real.log ((d' : ℝ) / z))))
      _ = ∑ q ∈ h4L z ⌊u⌋₊, h4F3 z q :=
          Finset.sum_sigma' (Finset.Icc 1 ⌊u⌋₊)
            (fun n => ((Finset.Icc 1 ⌊u⌋₊).filter (fun d => d ∣ n ∧ z < d)).sigma
              (fun _ => (Finset.Icc 1 ⌊u⌋₊).filter (fun d => d ∣ n ∧ z < d)))
            (fun _ p => ((moebius p.1 : ℝ) * Real.log ((p.1 : ℝ) / z))
              * ((moebius p.2 : ℝ) * Real.log ((p.2 : ℝ) / z)))
  have hfilt : ∀ (M a b : ℕ) (h : ℕ → ℝ),
      ∑ k ∈ (Finset.Icc 1 M).filter (fun k => Nat.Coprime k (a * b) ∧ z < a * k ∧ z < b * k), h k
        = ∑ k ∈ (Finset.Icc 1 M).filter (fun k => z < a * k ∧ z < b * k),
            (if Nat.Coprime k (a * b) then h k else 0) := by
    intro M a b h
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : Nat.Coprime k (a * b) <;> by_cases h2 : z < a * k ∧ z < b * k <;>
      simp [h1, h2]
  have hR : (∑ g ∈ Finset.Icc 1 ⌊u⌋₊, ∑ a ∈ Finset.Icc 1 ⌊u⌋₊,
        ∑ b ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun b => Nat.Coprime a b),
          (moebius a : ℝ) * (moebius b : ℝ) *
          ∑ k ∈ (Finset.Icc 1 (⌊u⌋₊ / (g * a * b))).filter
                  (fun k => Nat.Coprime k (a * b) ∧ z < a * k ∧ z < b * k),
            (moebius k : ℝ) ^ 2 * Real.log (((a * k : ℕ) : ℝ) / z)
              * Real.log (((b * k : ℕ) : ℝ) / z))
      = ∑ w ∈ h4R z ⌊u⌋₊, h4F4 z w := by
    have h1 : ∀ g ∈ Finset.Icc 1 ⌊u⌋₊,
        (∑ a ∈ Finset.Icc 1 ⌊u⌋₊,
          ∑ b ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun b => Nat.Coprime a b),
            (moebius a : ℝ) * (moebius b : ℝ) *
            ∑ k ∈ (Finset.Icc 1 (⌊u⌋₊ / (g * a * b))).filter
                    (fun k => Nat.Coprime k (a * b) ∧ z < a * k ∧ z < b * k),
              (moebius k : ℝ) ^ 2 * Real.log (((a * k : ℕ) : ℝ) / z)
                * Real.log (((b * k : ℕ) : ℝ) / z))
        = ∑ a ∈ Finset.Icc 1 ⌊u⌋₊,
            ∑ b ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun b => Nat.Coprime a b),
              ∑ k ∈ (Finset.Icc 1 (⌊u⌋₊ / (g * a * b))).filter
                      (fun k => z < a * k ∧ z < b * k),
                h4F4 z ⟨g, a, b, k⟩ := by
      intro g _
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum, hfilt]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [h4F4]
    calc (∑ g ∈ Finset.Icc 1 ⌊u⌋₊, ∑ a ∈ Finset.Icc 1 ⌊u⌋₊,
            ∑ b ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun b => Nat.Coprime a b),
              (moebius a : ℝ) * (moebius b : ℝ) *
              ∑ k ∈ (Finset.Icc 1 (⌊u⌋₊ / (g * a * b))).filter
                      (fun k => Nat.Coprime k (a * b) ∧ z < a * k ∧ z < b * k),
                (moebius k : ℝ) ^ 2 * Real.log (((a * k : ℕ) : ℝ) / z)
                  * Real.log (((b * k : ℕ) : ℝ) / z))
        = ∑ g ∈ Finset.Icc 1 ⌊u⌋₊, ∑ a ∈ Finset.Icc 1 ⌊u⌋₊,
            ∑ b ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun b => Nat.Coprime a b),
              ∑ k ∈ (Finset.Icc 1 (⌊u⌋₊ / (g * a * b))).filter
                      (fun k => z < a * k ∧ z < b * k),
                h4F4 z ⟨g, a, b, k⟩ := Finset.sum_congr rfl h1
      _ = ∑ g ∈ Finset.Icc 1 ⌊u⌋₊, ∑ a ∈ Finset.Icc 1 ⌊u⌋₊,
            ∑ p ∈ ((Finset.Icc 1 ⌊u⌋₊).filter (fun b => Nat.Coprime a b)).sigma
                    (fun b => (Finset.Icc 1 (⌊u⌋₊ / (g * a * b))).filter
                      (fun k => z < a * k ∧ z < b * k)),
              h4F4 z ⟨g, a, p.1, p.2⟩ :=
          Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun a _ =>
            Finset.sum_sigma' ((Finset.Icc 1 ⌊u⌋₊).filter (fun b => Nat.Coprime a b))
              (fun b => (Finset.Icc 1 (⌊u⌋₊ / (g * a * b))).filter
                (fun k => z < a * k ∧ z < b * k))
              (fun b k => h4F4 z ⟨g, a, b, k⟩)))
      _ = ∑ g ∈ Finset.Icc 1 ⌊u⌋₊,
            ∑ r ∈ (Finset.Icc 1 ⌊u⌋₊).sigma (fun a =>
                    ((Finset.Icc 1 ⌊u⌋₊).filter (fun b => Nat.Coprime a b)).sigma
                      (fun b => (Finset.Icc 1 (⌊u⌋₊ / (g * a * b))).filter
                        (fun k => z < a * k ∧ z < b * k))),
              h4F4 z ⟨g, r.1, r.2.1, r.2.2⟩ :=
          Finset.sum_congr rfl (fun g _ => Finset.sum_sigma' (Finset.Icc 1 ⌊u⌋₊)
            (fun a => ((Finset.Icc 1 ⌊u⌋₊).filter (fun b => Nat.Coprime a b)).sigma
              (fun b => (Finset.Icc 1 (⌊u⌋₊ / (g * a * b))).filter
                (fun k => z < a * k ∧ z < b * k)))
            (fun a p => h4F4 z ⟨g, a, p.1, p.2⟩))
      _ = ∑ w ∈ h4R z ⌊u⌋₊, h4F4 z w :=
          Finset.sum_sigma' (Finset.Icc 1 ⌊u⌋₊)
            (fun g => (Finset.Icc 1 ⌊u⌋₊).sigma (fun a =>
              ((Finset.Icc 1 ⌊u⌋₊).filter (fun b => Nat.Coprime a b)).sigma
                (fun b => (Finset.Icc 1 (⌊u⌋₊ / (g * a * b))).filter
                  (fun k => z < a * k ∧ z < b * k))))
            (fun g r => h4F4 z ⟨g, r.1, r.2.1, r.2.2⟩)
  rw [hL, hR]
  refine Finset.sum_nbij' h4Fwd h4Bwd ?_ ?_ ?_ ?_ ?_
  · -- the forward map lands in the box
    intro q hq
    obtain ⟨n, d, d'⟩ := q
    simp only [h4L] at hq
    obtain ⟨hn, hq2⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hdm, hd'm⟩ := Finset.mem_sigma.mp hq2
    obtain ⟨hdI, hdn, hzd⟩ := Finset.mem_filter.mp hdm
    obtain ⟨hd'I, hd'n, hzd'⟩ := Finset.mem_filter.mp hd'm
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hg0, ha0, hb0, hk0, hgabk, hbk, hak, hab⟩ :=
      h4_core hn1 hdn hd'n rfl rfl rfl rfl
    simp only [h4R, h4Fwd]
    set g := Nat.gcd (n / d) (n / d') with hgd
    set a := n / d / g with had
    set b := n / d' / g with hbd
    set k := n / (g * a * b) with hkd
    have hgab0 : 0 < g * a * b := mul_pos (mul_pos hg0 ha0) hb0
    have hgN : g ≤ ⌊u⌋₊ :=
      le_trans (Nat.le_of_dvd (by omega) ⟨a * b * k, by rw [← hgabk]; ring⟩) hnN
    have haN : a ≤ ⌊u⌋₊ :=
      le_trans (Nat.le_of_dvd (by omega) ⟨g * b * k, by rw [← hgabk]; ring⟩) hnN
    have hbN : b ≤ ⌊u⌋₊ :=
      le_trans (Nat.le_of_dvd (by omega) ⟨g * a * k, by rw [← hgabk]; ring⟩) hnN
    have hkN : k ≤ ⌊u⌋₊ / (g * a * b) := by
      refine (Nat.le_div_iff_mul_le hgab0).mpr ?_
      calc k * (g * a * b) = g * a * b * k := by ring
        _ = n := hgabk
        _ ≤ ⌊u⌋₊ := hnN
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hg0, hgN⟩, Finset.mem_sigma.mpr
      ⟨Finset.mem_Icc.mpr ⟨ha0, haN⟩, Finset.mem_sigma.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hb0, hbN⟩, hab⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk0, hkN⟩, ?_, ?_⟩⟩⟩⟩
    · rw [hak]; exact hzd'
    · rw [hbk]; exact hzd
  · -- the inverse map lands in the triple box
    intro w hw
    obtain ⟨g, a, b, k⟩ := w
    simp only [h4R] at hw
    obtain ⟨hg, hw2⟩ := Finset.mem_sigma.mp hw
    obtain ⟨ha, hw3⟩ := Finset.mem_sigma.mp hw2
    obtain ⟨hbm, hkm⟩ := Finset.mem_sigma.mp hw3
    obtain ⟨hbI, hab⟩ := Finset.mem_filter.mp hbm
    obtain ⟨hkI, hza, hzb⟩ := Finset.mem_filter.mp hkm
    obtain ⟨hg1, hgN⟩ := Finset.mem_Icc.mp hg
    obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp hbI
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hkI
    have hgab0 : 0 < g * a * b := mul_pos (mul_pos hg1 ha1) hb1
    have hnN : g * a * b * k ≤ ⌊u⌋₊ := by
      have h := (Nat.le_div_iff_mul_le hgab0).mp hkN
      calc g * a * b * k = k * (g * a * b) := by ring
        _ ≤ ⌊u⌋₊ := h
    have hn1 : 1 ≤ g * a * b * k := mul_pos hgab0 hk1
    have hbkd : b * k ∣ g * a * b * k := ⟨g * a, by ring⟩
    have hakd : a * k ∣ g * a * b * k := ⟨g * b, by ring⟩
    have hbk1 : 0 < b * k := mul_pos hb1 hk1
    have hak1 : 0 < a * k := mul_pos ha1 hk1
    have hbkN : b * k ≤ ⌊u⌋₊ := le_trans (Nat.le_of_dvd (by omega) hbkd) hnN
    have hakN : a * k ≤ ⌊u⌋₊ := le_trans (Nat.le_of_dvd (by omega) hakd) hnN
    simp only [h4L, h4Bwd]
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, Finset.mem_sigma.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hbk1, hbkN⟩, hbkd, hzb⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hak1, hakN⟩, hakd, hza⟩⟩⟩
  · -- `j ∘ i = id`
    intro q hq
    obtain ⟨n, d, d'⟩ := q
    simp only [h4L] at hq
    obtain ⟨hn, hq2⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hdm, hd'm⟩ := Finset.mem_sigma.mp hq2
    obtain ⟨-, hdn, -⟩ := Finset.mem_filter.mp hdm
    obtain ⟨-, hd'n, -⟩ := Finset.mem_filter.mp hd'm
    obtain ⟨hn1, -⟩ := Finset.mem_Icc.mp hn
    obtain ⟨-, -, -, -, hgabk, hbk, hak, -⟩ := h4_core hn1 hdn hd'n rfl rfl rfl rfl
    simp only [h4Fwd, h4Bwd]
    rw [hgabk, hbk, hak]
  · -- `i ∘ j = id`
    intro w hw
    obtain ⟨g, a, b, k⟩ := w
    simp only [h4R] at hw
    obtain ⟨hg, hw2⟩ := Finset.mem_sigma.mp hw
    obtain ⟨ha, hw3⟩ := Finset.mem_sigma.mp hw2
    obtain ⟨hbm, hkm⟩ := Finset.mem_sigma.mp hw3
    obtain ⟨hbI, hab⟩ := Finset.mem_filter.mp hbm
    obtain ⟨hkI, -⟩ := Finset.mem_filter.mp hkm
    obtain ⟨hg1, -⟩ := Finset.mem_Icc.mp hg
    obtain ⟨ha1, -⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hb1, -⟩ := Finset.mem_Icc.mp hbI
    obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hkI
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h4_core' hg1 ha1 hb1 hk1 hab
    simp only [h4Fwd, h4Bwd]
    rw [e1, e2, e3, e4, e5, e6]
  · -- the summands agree
    intro q hq
    obtain ⟨n, d, d'⟩ := q
    simp only [h4L] at hq
    obtain ⟨hn, hq2⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hdm, hd'm⟩ := Finset.mem_sigma.mp hq2
    obtain ⟨-, hdn, -⟩ := Finset.mem_filter.mp hdm
    obtain ⟨-, hd'n, -⟩ := Finset.mem_filter.mp hd'm
    obtain ⟨hn1, -⟩ := Finset.mem_Icc.mp hn
    obtain ⟨-, -, -, -, -, hbk, hak, -⟩ := h4_core hn1 hdn hd'n rfl rfl rfl rfl
    simp only [h4F3, h4F4, h4Fwd]
    set g := Nat.gcd (n / d) (n / d') with hgd
    set a := n / d / g with had
    set b := n / d' / g with hbd
    set k := n / (g * a * b) with hkd
    have hbk2 : b * k = d := hbk
    have hak2 : a * k = d' := hak
    rw [← hbk2, ← hak2]
    by_cases hc : Nat.Coprime k (a * b)
    · rw [if_pos hc]
      linear_combination (Real.log (((a * k : ℕ) : ℝ) / z) * Real.log (((b * k : ℕ) : ℝ) / z))
        * moebius_mul_moebius_of_coprime hc
    · rw [if_neg hc]
      linear_combination (Real.log (((a * k : ℕ) : ℝ) / z) * Real.log (((b * k : ℕ) : ℝ) / z))
        * moebius_mul_moebius_eq_zero_of_not_coprime (a := a) (b := b) (k := k) hc

-- **H4's binder-shape row** (the exit test). Off line at `(z, u) = (2, 12)`, where the
-- `(k, ab) = 1` filter BITES: both sides are `7.085333`, against `3.451733` unfiltered.
example : ∑ n ∈ Finset.Icc 1 ⌊(12 : ℝ)⌋₊, tailT 2 n ^ 2
    = ∑ g ∈ Finset.Icc 1 ⌊(12 : ℝ)⌋₊, ∑ a ∈ Finset.Icc 1 ⌊(12 : ℝ)⌋₊,
        ∑ b ∈ (Finset.Icc 1 ⌊(12 : ℝ)⌋₊).filter (fun b => Nat.Coprime a b),
          (moebius a : ℝ) * (moebius b : ℝ) *
          ∑ k ∈ (Finset.Icc 1 (⌊(12 : ℝ)⌋₊ / (g * a * b))).filter
                  (fun k => Nat.Coprime k (a * b) ∧ 2 < a * k ∧ 2 < b * k),
            (moebius k : ℝ) ^ 2 * Real.log (((a * k : ℕ) : ℝ) / 2)
              * Real.log (((b * k : ℕ) : ℝ) / 2) :=
  sum_tailT_sq_eq (by norm_num) (by norm_num)


/-! ## H6b — the weighted Möbius sum with a power-of-log saving -/

/-- **The DISCRETE Abel identity** `Mw(X) = M_μ(X)/X + Σ_{n < X} M_μ(n)/(n(n+1))`.
H6b's whole transfer from `mmuRate_holds` runs through this and a telescoping sum: no
integral, no `IntegrableOn`, no improper-integral matching (contrast the `A = 1` route of
`MoebiusRateSharp`, which needs all three because it works on the reals). -/
private lemma mwWeighted_abel {X : ℕ} (hX : 1 ≤ X) :
    mwWeighted X = Salt.TwinBar.Mmu X / (X : ℝ)
      + ∑ n ∈ Finset.Ico 1 X, Salt.TwinBar.Mmu n / ((n : ℝ) * ((n : ℝ) + 1)) := by
  induction X, hX using Nat.le_induction with
  | base => simp [mwWeighted, Salt.TwinBar.Mmu]
  | succ X hX ih =>
    have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have hmw : mwWeighted (X + 1) = mwWeighted X + (moebius (X + 1) : ℝ) / ((X : ℝ) + 1) := by
      simp only [mwWeighted]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ X + 1)]
      push_cast
      ring
    have hM : Salt.TwinBar.Mmu (X + 1) = Salt.TwinBar.Mmu X + (moebius (X + 1) : ℝ) := by
      simp only [Salt.TwinBar.Mmu]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ X + 1)]
    rw [hmw, ih, Finset.sum_Ico_succ_top hX, hM]
    push_cast
    field_simp
    ring

/-- The telescoping step `1/((n+1)(log n)^{A+1}) ≤ (2^{A+1}/A)·((log n)^{−A} − (log(n+1))^{−A})`
for `n ≥ 3`. Convexity is never invoked: `e^s ≥ 1 + s` and `log x ≥ 1 − 1/x` give the
tangent bound `u^{−A} − v^{−A} ≥ A·v^{−A−1}(v − u)` directly, and `v ≤ 2u` (i.e.
`n + 1 ≤ n²`) converts `v^{−A−1}` into `2^{−A−1}u^{−A−1}`. -/
private lemma log_rpow_tele_step {A : ℝ} (hA : 0 < A) {n : ℕ} (hn : 3 ≤ n) :
    1 / (((n : ℝ) + 1) * Real.log n ^ (A + 1))
      ≤ 2 ^ (A + 1) / A * (Real.log n ^ (-A) - Real.log ((n : ℝ) + 1) ^ (-A)) := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hu1 : (1 : ℝ) < Real.log (n : ℝ) := by
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    exact (Real.lt_log_iff_exp_lt hn0).mpr (by linarith)
  set u : ℝ := Real.log (n : ℝ) with hudef
  set v : ℝ := Real.log ((n : ℝ) + 1) with hvdef
  have hu0 : 0 < u := by linarith
  have huv : u < v := by
    rw [hudef, hvdef]; exact Real.log_lt_log hn0 (by linarith)
  have hv0 : 0 < v := by linarith
  have hv2u : v ≤ 2 * u := by
    have hsq : (n : ℝ) + 1 ≤ (n : ℝ) * (n : ℝ) := by nlinarith
    have hlg : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) * (n : ℝ)) :=
      Real.log_le_log (by linarith) hsq
    rw [Real.log_mul (by linarith) (by linarith)] at hlg
    rw [hvdef, hudef]; linarith
  have hgap : 1 / ((n : ℝ) + 1) ≤ v - u := by
    have hpos : (0 : ℝ) < (n : ℝ) / ((n : ℝ) + 1) := by positivity
    have heq : (n : ℝ) / ((n : ℝ) + 1) = -(1 / ((n : ℝ) + 1)) + 1 := by field_simp; ring
    have hle : (n : ℝ) / ((n : ℝ) + 1) ≤ Real.exp (-(1 / ((n : ℝ) + 1))) := by
      rw [heq]; exact Real.add_one_le_exp _
    have h2 := (Real.log_le_iff_le_exp hpos).mpr hle
    have hs : Real.log ((n : ℝ) / ((n : ℝ) + 1)) = u - v := by
      rw [Real.log_div (by linarith) (by linarith), hudef, hvdef]
    rw [hs] at h2
    linarith
  -- the tangent bound `u^{-A} - v^{-A} ≥ A·v^{-A-1}·(v-u)`
  have hlogratio : 1 - u / v ≤ Real.log (v / u) := by
    have h1 : Real.log (u / v) ≤ u / v - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (u / v) = -Real.log (v / u) := by
      rw [Real.log_div hu0.ne' hv0.ne', Real.log_div hv0.ne' hu0.ne']; ring
    linarith
  have hquot : (u / v) ^ (-A) = Real.exp (A * Real.log (v / u)) := by
    rw [Real.rpow_def_of_pos (show (0 : ℝ) < u / v by positivity)]
    congr 1
    have h2 : Real.log (u / v) = -Real.log (v / u) := by
      rw [Real.log_div hu0.ne' hv0.ne', Real.log_div hv0.ne' hu0.ne']; ring
    rw [h2]; ring
  have hstep1 : 1 + A * (1 - u / v) ≤ (u / v) ^ (-A) := by
    rw [hquot]
    have h := Real.add_one_le_exp (A * Real.log (v / u))
    have h2 : A * (1 - u / v) ≤ A * Real.log (v / u) :=
      mul_le_mul_of_nonneg_left hlogratio hA.le
    linarith
  have hsplit : u ^ (-A) = v ^ (-A) * (u / v) ^ (-A) := by
    rw [div_rpow_neg hu0.le hv0.le, show (-(-A) : ℝ) = A by ring,
      show v ^ (-A) * (u ^ (-A) * v ^ A) = v ^ (-A) * v ^ A * u ^ (-A) by ring,
      ← Real.rpow_add hv0, show (-A + A : ℝ) = 0 by ring, Real.rpow_zero, one_mul]
  have hvA1 : v ^ (-A) / v = v ^ (-A - 1) := by
    rw [show (-A - 1 : ℝ) = (-A) + (-(1 : ℝ)) by ring, Real.rpow_add hv0, Real.rpow_neg_one]
    ring
  have hvApos : (0 : ℝ) < v ^ (-A) := Real.rpow_pos_of_pos hv0 _
  have htangent : A * v ^ (-A - 1) * (v - u) ≤ u ^ (-A) - v ^ (-A) := by
    have h1 : v ^ (-A) * (1 + A * (1 - u / v)) ≤ v ^ (-A) * (u / v) ^ (-A) :=
      mul_le_mul_of_nonneg_left hstep1 hvApos.le
    rw [← hsplit] at h1
    have h2 : v ^ (-A) * (1 + A * (1 - u / v)) = v ^ (-A) + A * (v ^ (-A) / v) * (v - u) := by
      field_simp
    rw [h2, hvA1] at h1
    linarith
  -- convert `v^{-A-1}` into `2^{-A-1}u^{-A-1}` and finish
  have hexp0 : (-A - 1 : ℝ) ≤ 0 := by linarith
  have hmono : (2 * u) ^ (-A - 1) ≤ v ^ (-A - 1) :=
    Real.rpow_le_rpow_of_nonpos hv0 hv2u hexp0
  have hsplit2 : (2 * u) ^ (-A - 1) = 2 ^ (-A - 1) * u ^ (-A - 1) :=
    Real.mul_rpow (by norm_num) hu0.le
  have h2pow : (2 : ℝ) ^ (-A - 1) = 1 / 2 ^ (A + 1) := by
    rw [show (-A - 1 : ℝ) = -(A + 1) by ring, Real.rpow_neg (by norm_num)]
    ring
  have huinv : u ^ (-A - 1) = 1 / u ^ (A + 1) := by
    rw [show (-A - 1 : ℝ) = -(A + 1) by ring, Real.rpow_neg hu0.le]
    ring
  have hupow : (0 : ℝ) < u ^ (A + 1) := Real.rpow_pos_of_pos hu0 _
  have h2A : (0 : ℝ) < (2 : ℝ) ^ (A + 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hchain : A / 2 ^ (A + 1) * (1 / (((n : ℝ) + 1) * u ^ (A + 1)))
      ≤ u ^ (-A) - v ^ (-A) := by
    refine le_trans ?_ htangent
    have hgap' : A * v ^ (-A - 1) * (1 / ((n : ℝ) + 1)) ≤ A * v ^ (-A - 1) * (v - u) := by
      refine mul_le_mul_of_nonneg_left hgap ?_
      have : (0 : ℝ) ≤ v ^ (-A - 1) := Real.rpow_nonneg hv0.le _
      positivity
    refine le_trans ?_ hgap'
    have hmono' : A * ((2 : ℝ) ^ (-A - 1) * u ^ (-A - 1)) * (1 / ((n : ℝ) + 1))
        ≤ A * v ^ (-A - 1) * (1 / ((n : ℝ) + 1)) := by
      rw [← hsplit2]
      have hnn : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmono hA.le) hnn
    refine le_trans (le_of_eq ?_) hmono'
    rw [h2pow, huinv]
    field_simp
  have hc : (0 : ℝ) < 2 ^ (A + 1) / A := by positivity
  calc 1 / (((n : ℝ) + 1) * u ^ (A + 1))
      = 2 ^ (A + 1) / A * (A / 2 ^ (A + 1) * (1 / (((n : ℝ) + 1) * u ^ (A + 1)))) := by
        field_simp
    _ ≤ 2 ^ (A + 1) / A * (u ^ (-A) - v ^ (-A)) := mul_le_mul_of_nonneg_left hchain hc.le

/-- The telescoped tail `Σ_{N ≤ n < X} 1/((n+1)(log n)^{A+1}) ≤ (2^{A+1}/A)·(log N)^{−A}`. -/
private lemma sum_Ico_log_tail {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 3 ≤ N) :
    ∀ X : ℕ, N ≤ X →
      ∑ n ∈ Finset.Ico N X, 1 / (((n : ℝ) + 1) * Real.log n ^ (A + 1))
        ≤ 2 ^ (A + 1) / A * Real.log N ^ (-A) := by
  have hkey : ∀ X : ℕ, N ≤ X →
      ∑ n ∈ Finset.Ico N X, 1 / (((n : ℝ) + 1) * Real.log n ^ (A + 1))
        ≤ 2 ^ (A + 1) / A * (Real.log N ^ (-A) - Real.log X ^ (-A)) := by
    intro X hX
    induction X, hX using Nat.le_induction with
    | base => simp
    | succ X hX ih =>
      rw [Finset.sum_Ico_succ_top hX]
      have hstep := log_rpow_tele_step hA (n := X) (by omega)
      have hcast : ((X + 1 : ℕ) : ℝ) = (X : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith [ih, hstep]
  intro X hX
  have h := hkey X hX
  have hXpos : (0 : ℝ) ≤ Real.log X ^ (-A) := by
    refine Real.rpow_nonneg ?_ _
    refine Real.log_nonneg ?_
    have : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast le_trans hN hX
    linarith
  have hc : (0 : ℝ) < 2 ^ (A + 1) / A := by
    have : (0 : ℝ) < (2 : ℝ) ^ (A + 1) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  nlinarith [h, hXpos, hc]

/-- The natural-cut-off form of H6b: `|Mw(N)| ≤ C/(log N)^A` for `N ≥ 3`. -/
private lemma abs_mwWeighted_le_inv_log_rpow (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N → |mwWeighted N| ≤ C / Real.log N ^ A := by
  obtain ⟨C₁, x₀, hC₁, hb⟩ := mmuRate_holds (A + 1) (by linarith)
  set N₀ : ℕ := max x₀ 3 with hN₀def
  have hN₀3 : 3 ≤ N₀ := le_max_right x₀ 3
  set K : ℝ := C₁ + C₁ * (2 ^ (A + 1) / A) with hKdef
  have h2A : (0 : ℝ) < (2 : ℝ) ^ (A + 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hKpos : 0 < K := by rw [hKdef]; positivity
  set C : ℝ := max K (Real.log (N₀ : ℝ) ^ A) with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le hKpos (le_max_left _ _)
  refine ⟨C, hCpos, fun N hN3 => ?_⟩
  have hN3R : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hlogN : (1 : ℝ) < Real.log (N : ℝ) := by
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith)
  have hlogNA : (0 : ℝ) < Real.log (N : ℝ) ^ A := Real.rpow_pos_of_pos (by linarith) _
  rcases le_or_gt N₀ N with hbig | hsmall
  · -- the rate's window: the discrete Abel split, then the telescoped tail
    have hx0N : x₀ ≤ N := le_trans (le_max_left x₀ 3) hbig
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hbound : ∀ X : ℕ, N ≤ X →
        |mwWeighted N| ≤ |mwWeighted X| + |Salt.TwinBar.Mmu X / (X : ℝ)| + K / Real.log N ^ A := by
      intro X hX
      have hidN := mwWeighted_abel (X := N) (by omega)
      have hidX := mwWeighted_abel (X := X) (by omega)
      have hsplit : ∑ n ∈ Finset.Ico 1 X, Salt.TwinBar.Mmu n / ((n : ℝ) * ((n : ℝ) + 1))
          = (∑ n ∈ Finset.Ico 1 N, Salt.TwinBar.Mmu n / ((n : ℝ) * ((n : ℝ) + 1)))
            + ∑ n ∈ Finset.Ico N X, Salt.TwinBar.Mmu n / ((n : ℝ) * ((n : ℝ) + 1)) := by
        rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 1 N X),
          Finset.Ico_union_Ico_eq_Ico (by omega) hX]
      have hkeyid : mwWeighted N = mwWeighted X - Salt.TwinBar.Mmu X / (X : ℝ)
          + Salt.TwinBar.Mmu N / (N : ℝ)
          - ∑ n ∈ Finset.Ico N X, Salt.TwinBar.Mmu n / ((n : ℝ) * ((n : ℝ) + 1)) := by
        rw [hidX, hsplit] at *
        linarith [hidN]
      -- the boundary term
      have hbdry : |Salt.TwinBar.Mmu N / (N : ℝ)| ≤ C₁ / Real.log (N : ℝ) ^ A := by
        have h := hb N hx0N
        have hLpos : (0 : ℝ) < Real.log (N : ℝ) ^ (A + 1) :=
          Real.rpow_pos_of_pos (by linarith) _
        have hle : |Salt.TwinBar.Mmu N| / (N : ℝ) ≤ C₁ / Real.log (N : ℝ) ^ (A + 1) := by
          rw [div_le_div_iff₀ hNpos hLpos]
          have h2 : |Salt.TwinBar.Mmu N| * Real.log (N : ℝ) ^ (A + 1)
              ≤ C₁ * (N : ℝ) / Real.log (N : ℝ) ^ (A + 1) * Real.log (N : ℝ) ^ (A + 1) :=
            mul_le_mul_of_nonneg_right h hLpos.le
          rw [div_mul_cancel₀ _ hLpos.ne'] at h2
          linarith
        have hmono : Real.log (N : ℝ) ^ A ≤ Real.log (N : ℝ) ^ (A + 1) :=
          Real.rpow_le_rpow_of_exponent_le hlogN.le (by linarith)
        rw [abs_div, abs_of_nonneg hNpos.le] at *
        calc |Salt.TwinBar.Mmu N| / (N : ℝ) ≤ C₁ / Real.log (N : ℝ) ^ (A + 1) := hle
          _ ≤ C₁ / Real.log (N : ℝ) ^ A := by
              refine div_le_div_of_nonneg_left hC₁.le hlogNA hmono
      -- the tail
      have htail : |∑ n ∈ Finset.Ico N X, Salt.TwinBar.Mmu n / ((n : ℝ) * ((n : ℝ) + 1))|
          ≤ C₁ * (2 ^ (A + 1) / A) / Real.log (N : ℝ) ^ A := by
        have hterm : ∀ n ∈ Finset.Ico N X,
            |Salt.TwinBar.Mmu n / ((n : ℝ) * ((n : ℝ) + 1))|
              ≤ C₁ * (1 / (((n : ℝ) + 1) * Real.log n ^ (A + 1))) := by
          intro n hn
          obtain ⟨hnN, -⟩ := Finset.mem_Ico.mp hn
          have hn3 : 3 ≤ n := le_trans (le_trans hN₀3 hbig) hnN
          have hnx0 : x₀ ≤ n := le_trans hx0N hnN
          have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
          have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
          have hlogn : (1 : ℝ) < Real.log (n : ℝ) := by
            have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
            exact (Real.lt_log_iff_exp_lt hnpos).mpr (by linarith)
          have hlognA : (0 : ℝ) < Real.log (n : ℝ) ^ (A + 1) :=
            Real.rpow_pos_of_pos (by linarith) _
          have h := hb n hnx0
          rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1))]
          rw [div_le_iff₀ (by positivity)]
          have hexp : C₁ * (1 / (((n : ℝ) + 1) * Real.log (n : ℝ) ^ (A + 1)))
              * ((n : ℝ) * ((n : ℝ) + 1))
              = (C₁ * (n : ℝ) / Real.log (n : ℝ) ^ (A + 1)) := by
            field_simp
          rw [hexp]
          exact h
        calc |∑ n ∈ Finset.Ico N X, Salt.TwinBar.Mmu n / ((n : ℝ) * ((n : ℝ) + 1))|
            ≤ ∑ n ∈ Finset.Ico N X, |Salt.TwinBar.Mmu n / ((n : ℝ) * ((n : ℝ) + 1))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ n ∈ Finset.Ico N X, C₁ * (1 / (((n : ℝ) + 1) * Real.log n ^ (A + 1))) :=
              Finset.sum_le_sum hterm
          _ = C₁ * ∑ n ∈ Finset.Ico N X, 1 / (((n : ℝ) + 1) * Real.log n ^ (A + 1)) := by
              rw [Finset.mul_sum]
          _ ≤ C₁ * (2 ^ (A + 1) / A * Real.log (N : ℝ) ^ (-A)) :=
              mul_le_mul_of_nonneg_left
                (sum_Ico_log_tail hA (le_trans hN₀3 hbig) X hX) hC₁.le
          _ = C₁ * (2 ^ (A + 1) / A) / Real.log (N : ℝ) ^ A := by
              rw [show Real.log (N : ℝ) ^ (-A) = 1 / Real.log (N : ℝ) ^ A by
                rw [Real.rpow_neg (by linarith)]; ring]
              ring
      have hK : K / Real.log (N : ℝ) ^ A
          = C₁ / Real.log (N : ℝ) ^ A + C₁ * (2 ^ (A + 1) / A) / Real.log (N : ℝ) ^ A := by
        rw [hKdef]; ring
      have e1 : mwWeighted X - Salt.TwinBar.Mmu X / (X : ℝ) + Salt.TwinBar.Mmu N / (N : ℝ)
          - ∑ n ∈ Finset.Ico N X, Salt.TwinBar.Mmu n / ((n : ℝ) * ((n : ℝ) + 1))
          = mwWeighted X + -(Salt.TwinBar.Mmu X / (X : ℝ)) + Salt.TwinBar.Mmu N / (N : ℝ)
            + -(∑ n ∈ Finset.Ico N X, Salt.TwinBar.Mmu n / ((n : ℝ) * ((n : ℝ) + 1))) := by ring
      have t1 := abs_add_le (mwWeighted X + -(Salt.TwinBar.Mmu X / (X : ℝ))
        + Salt.TwinBar.Mmu N / (N : ℝ))
        (-(∑ n ∈ Finset.Ico N X, Salt.TwinBar.Mmu n / ((n : ℝ) * ((n : ℝ) + 1))))
      have t2 := abs_add_le (mwWeighted X + -(Salt.TwinBar.Mmu X / (X : ℝ)))
        (Salt.TwinBar.Mmu N / (N : ℝ))
      have t3 := abs_add_le (mwWeighted X) (-(Salt.TwinBar.Mmu X / (X : ℝ)))
      rw [abs_neg] at t1 t3
      rw [hkeyid, hK, e1]
      linarith [t1, t2, t3, hbdry, htail]
    -- let `X → ∞`
    have hlim : Filter.Tendsto
        (fun X : ℕ => |mwWeighted X| + |Salt.TwinBar.Mmu X / (X : ℝ)| + K / Real.log (N : ℝ) ^ A)
        Filter.atTop (nhds (0 + 0 + K / Real.log (N : ℝ) ^ A)) := by
      refine Filter.Tendsto.add (Filter.Tendsto.add ?_ ?_) tendsto_const_nhds
      · simpa using mwWeighted_tendsto_zero.abs
      · simpa using Mmu_div_tendsto_zero.abs
    have hfin : |mwWeighted N| ≤ 0 + 0 + K / Real.log (N : ℝ) ^ A :=
      ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨N, fun X hX => hbound X hX⟩)
    have hKC : K ≤ C := le_max_left _ _
    calc |mwWeighted N| ≤ K / Real.log (N : ℝ) ^ A := by linarith
      _ ≤ C / Real.log (N : ℝ) ^ A := (div_le_div_iff_of_pos_right hlogNA).mpr hKC
  · -- the finite window
    have htriv : |mwWeighted N| ≤ 1 := abs_mwWeighted_le_one (by omega)
    have hNle : (N : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast (by omega : N ≤ N₀)
    have hlogle : Real.log (N : ℝ) ^ A ≤ Real.log (N₀ : ℝ) ^ A :=
      Real.rpow_le_rpow (by linarith) (Real.log_le_log (by linarith) hNle) hA.le
    have hCge : Real.log (N₀ : ℝ) ^ A ≤ C := le_max_right _ _
    rw [le_div_iff₀ hlogNA]
    nlinarith [htriv, hlogle, hCge, hlogNA]

/-- **H6b (An (3.2) over `ℚ`).** `|Σ_{n ≤ Q} μ(n)/n| ≤ C/(log 2Q)^A` for every `A > 0`.

Route: the DISCRETE Abel identity `Mw(X) = M_μ(X)/X + Σ_{n<X} M_μ(n)/(n(n+1))`, applied at
`N` and at `X ≥ N` and subtracted; `mmuRate_holds` at `A + 1` bounds the boundary term and,
through a telescoping `(log n)^{−A}` estimate, the whole tail by `C/(log N)^A`; letting
`X → ∞` against the landed `Mw(X) → 0` and `M_μ(X)/X → 0` removes the two `X`-terms.
The real cut-off is reached exactly as in H6a (`⌊Q⌋₊ ≤ Q`, `log 2Q ≤ 2 log ⌊Q⌋₊` above 4),
and the window `Q < max(x₀, 4)` by the landed `|Mw| ≤ 1`.

The constant is NON-EFFECTIVE: it carries `mmuRate_holds`'s `C` and `x₀` at the saving
`A + 1`, and no numeral for `x₀` is extracted anywhere in the corpus. -/
theorem abs_sum_moebius_div_le_inv_log_pow (A : ℝ) (hA : 0 < A) : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q →
    |∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n| ≤ C / Real.log (2 * Q) ^ A := by
  obtain ⟨C₀, hC₀, hcore⟩ := abs_mwWeighted_le_inv_log_rpow A hA
  have h2A : (0 : ℝ) < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) _
  have hlog8 : (0 : ℝ) < Real.log 8 := Real.log_pos (by norm_num)
  set C : ℝ := max (C₀ * 2 ^ A) (Real.log 8 ^ A) with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C, hCpos, fun Q hQ => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hnQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQ0.le
  have hQn : Q < ((⌊Q⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one Q
  have hlog2Q : (0 : ℝ) < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hpowpos : (0 : ℝ) < Real.log (2 * Q) ^ A := Real.rpow_pos_of_pos hlog2Q _
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n = mwWeighted ⌊Q⌋₊ := rfl
  rw [hsum]
  rcases le_or_gt 4 ⌊Q⌋₊ with hbig | hsmall
  · have hn4R : (4 : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast hbig
    have hlogn : (0 : ℝ) < Real.log ((⌊Q⌋₊ : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hlognA : (0 : ℝ) < Real.log ((⌊Q⌋₊ : ℕ) : ℝ) ^ A := Real.rpow_pos_of_pos hlogn _
    have hcmp : Real.log (2 * Q) ≤ 2 * Real.log ((⌊Q⌋₊ : ℕ) : ℝ) := by
      have hstep : 2 * Q ≤ ((⌊Q⌋₊ : ℕ) : ℝ) * ((⌊Q⌋₊ : ℕ) : ℝ) := by nlinarith
      calc Real.log (2 * Q) ≤ Real.log (((⌊Q⌋₊ : ℕ) : ℝ) * ((⌊Q⌋₊ : ℕ) : ℝ)) :=
            Real.log_le_log (by linarith) hstep
        _ = 2 * Real.log ((⌊Q⌋₊ : ℕ) : ℝ) := by
            rw [Real.log_mul (by linarith) (by linarith)]; ring
    have hpow : Real.log (2 * Q) ^ A ≤ 2 ^ A * Real.log ((⌊Q⌋₊ : ℕ) : ℝ) ^ A := by
      have h1 : Real.log (2 * Q) ^ A ≤ (2 * Real.log ((⌊Q⌋₊ : ℕ) : ℝ)) ^ A :=
        Real.rpow_le_rpow hlog2Q.le hcmp hA.le
      rwa [Real.mul_rpow (by norm_num) hlogn.le] at h1
    calc |mwWeighted ⌊Q⌋₊| ≤ C₀ / Real.log ((⌊Q⌋₊ : ℕ) : ℝ) ^ A := hcore _ (by omega)
      _ = C₀ * 2 ^ A / (2 ^ A * Real.log ((⌊Q⌋₊ : ℕ) : ℝ) ^ A) := by field_simp
      _ ≤ C₀ * 2 ^ A / Real.log (2 * Q) ^ A := by
          gcongr
      _ ≤ C / Real.log (2 * Q) ^ A := by
          gcongr
          exact le_max_left _ _
  · have htriv : |mwWeighted ⌊Q⌋₊| ≤ 1 := by
      rcases Nat.eq_zero_or_pos ⌊Q⌋₊ with h0 | hpos
      · rw [h0]; simp [mwWeighted]
      · exact abs_mwWeighted_le_one hpos
    have hQsmall : Q < 4 := by
      have : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : ⌊Q⌋₊ ≤ 3)
      linarith
    have hlogle : Real.log (2 * Q) ≤ Real.log 8 :=
      Real.log_le_log (by linarith) (by linarith)
    have hpowle : Real.log (2 * Q) ^ A ≤ Real.log 8 ^ A :=
      Real.rpow_le_rpow hlog2Q.le hlogle hA.le
    have hCge : Real.log 8 ^ A ≤ C := le_max_right _ _
    rw [le_div_iff₀ hpowpos]
    nlinarith [htriv, hpowle, hCge, hpowpos]

end Salt.SW
