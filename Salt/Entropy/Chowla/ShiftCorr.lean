/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# Shift invariance for correlation integrals against `logMeasure` (spine node SHIFT-CORR)

The carrier the STMT2 residual (`hreduce`) is blocked on: `harmonic_shift_l1_le`
(`Invariance.lean`) moves window LAWS, but Tao's Prop 2.6 reduction needs the
approximate translation invariance of a general bounded FUNCTION's expectation.

For any `f : ℕ → ℝ` with `|f| ≤ 1` and a shift `s : ℕ`, under `logMeasure x ω` the
`ℓ¹`/endpoint-mass argument on the finite Dirac sum gives

    |∫ f(n+s) − ∫ f(n)| ≤ (3·s·ω/x) / Z,   Z = ∑_{(x/ω, x]} 1/n.

The proof is finite-sum manipulation: `integral_logMeasure_eq` (the public form of
`ChowlaFailure`'s private Dirac reduction) turns each integral into `Z⁻¹·∑ f(n)/n`;
inserting the reindexed intermediate `∑ f(n+s)/(n+s)` splits the difference into
(i) a weight-mismatch sum `∑ f(n+s)·(1/n − 1/(n+s))` and (ii) a window-shift sum
`∑_{(x/ω+s, x+s]} f/m − ∑_{(x/ω, x]} f/m`; both collapse to the two `s`-point edge
windows via `Finset.sum_sdiff_sub_sum_sdiff`, each term `≤ ω/x` (a left edge above
`x/ω`, a right edge above `x`).

Exports:
* `integral_logMeasure_eq` — the general Dirac-reduction tool `∫ f dμ = Z⁻¹·∑ f/n`.
* `integral_shift_le` — the frozen shift-invariance bound (C-form `3·s·ω/x`).
* `corr_shift_le` — the direct consumer specialization at `s = 1` for the dilated
  Liouville correlation `λ(n+·+a)λ(n+·+b)`.
-/
import Salt.Entropy.Chowla.LogMeasure
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-- **The `logMeasure` expectation is the harmonic-weighted window sum ÷ `Z`.**
`∫ f dμ = (∑ 1/n)⁻¹ · ∑ f(n)/n` on the window `(x/ω, x]`, from the Dirac
decomposition of `logMeasure` and the `ℝ≥0∞→ℝ` normalizer bridge `norm_toReal`.
This is the public form of `ChowlaFailure`'s private `logMeasure_integral_eq`. -/
theorem integral_logMeasure_eq (f : ℕ → ℝ) (x ω : ℕ) :
    ∫ n, f n ∂(logMeasure x ω)
      = (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹ := by
  have hf : ∀ n ∈ Finset.Ioc (x / ω) x,
      Integrable f ((n : ℝ≥0∞)⁻¹ • Measure.dirac n) := fun n hn =>
    (integrable_dirac (by simp)).smul_measure
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast Nat.one_le_iff_ne_zero.mp (window_one_le hn)))
  unfold logMeasure
  rw [integral_smul_measure, integral_finsetSum_measure hf]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  rw [norm_toReal]
  congr 1
  exact Finset.sum_congr rfl (fun n _ => mul_comm _ _)

/-- Reindex a window sum by the shift `n ↦ n + s`: `∑_{(a,b]} g(n+s) = ∑_{(a+s,b+s]} g`. -/
private lemma sum_Ioc_shift (g : ℕ → ℝ) (a b s : ℕ) :
    ∑ n ∈ Finset.Ioc a b, g (n + s) = ∑ m ∈ Finset.Ioc (a + s) (b + s), g m := by
  rw [← Finset.map_add_right_Ioc a b s, Finset.sum_map]
  rfl

/-- The uniform edge bound `1/m ≤ ω/x` for any `m` just above `x/ω` (`m > x/ω`). -/
private lemma inv_le_div_of_lt {x ω m : ℕ} (hx : 1 ≤ x) (hω : 1 ≤ ω)
    (hm : x / ω < m) : (m : ℝ)⁻¹ ≤ (ω : ℝ) / (x : ℝ) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hm1 : x / ω + 1 ≤ m := hm
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hxlt : x < ω * m := by
    have hdm : ω * (x / ω) + x % ω = x := Nat.div_add_mod x ω
    have hmod : x % ω < ω := Nat.mod_lt x (by omega)
    have hml : ω * (x / ω + 1) ≤ ω * m := Nat.mul_le_mul (le_refl ω) hm1
    have he : ω * (x / ω + 1) = ω * (x / ω) + ω := by ring
    calc x = ω * (x / ω) + x % ω := hdm.symm
      _ < ω * (x / ω) + ω := by omega
      _ = ω * (x / ω + 1) := he.symm
      _ ≤ ω * m := hml
  have hxltR : (x : ℝ) < ω * m := by exact_mod_cast hxlt
  rw [le_div_iff₀ hx0]
  have hcancel : (m : ℝ)⁻¹ * (ω * m) = ω := by
    rw [mul_comm (ω : ℝ) m, ← mul_assoc, inv_mul_cancel₀ hmR.ne', one_mul]
  calc (m : ℝ)⁻¹ * x ≤ (m : ℝ)⁻¹ * (ω * m) :=
        mul_le_mul_of_nonneg_left hxltR.le (by positivity)
    _ = ω := hcancel

/-- An `s`-point edge window above `x/ω` has harmonic mass `≤ s·ω/x`. -/
private lemma edge_sum_le {x ω : ℕ} (c s : ℕ) (hx : 1 ≤ x) (hω : 1 ≤ ω)
    (hc : x / ω ≤ c) :
    ∑ m ∈ Finset.Ioc c (c + s), (m : ℝ)⁻¹ ≤ (s : ℝ) * ((ω : ℝ) / (x : ℝ)) := by
  calc ∑ m ∈ Finset.Ioc c (c + s), (m : ℝ)⁻¹
      ≤ ∑ _m ∈ Finset.Ioc c (c + s), (ω : ℝ) / (x : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_Ioc] at hm
        exact inv_le_div_of_lt hx hω (lt_of_le_of_lt hc hm.1)
    _ = (s : ℝ) * ((ω : ℝ) / (x : ℝ)) := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, show c + s - c = s by omega]

/-- The core finite-sum bound: the shifted harmonic-weighted window sum moves by at
most `3·s·ω/x` (a weight-mismatch edge + a window-shift double edge). -/
private lemma sum_shift_bound (x ω s : ℕ) (hx : 1 ≤ x) (hω : 1 ≤ ω)
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) :
    |(∑ n ∈ Finset.Ioc (x / ω) x, f (n + s) * (n : ℝ)⁻¹)
       - (∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹)|
      ≤ 3 * (s : ℝ) * (ω : ℝ) / (x : ℝ) := by
  set a : ℕ := x / ω with ha
  -- (i) the weight-mismatch sum `∑ f(n+s)·(1/n − 1/(n+s))`, bounded by the left edge.
  have hBbound : |(∑ n ∈ Finset.Ioc a x, f (n + s) * (n : ℝ)⁻¹)
                   - (∑ n ∈ Finset.Ioc a x, f (n + s) * ((n + s : ℕ) : ℝ)⁻¹)|
      ≤ (s : ℝ) * ((ω : ℝ) / (x : ℝ)) := by
    have hterm_nonneg : ∀ n ∈ Finset.Ioc a x,
        (0 : ℝ) ≤ (n : ℝ)⁻¹ - ((n + s : ℕ) : ℝ)⁻¹ := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn1 : 1 ≤ n := lt_of_le_of_lt (Nat.zero_le a) hn.1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hle : (n : ℝ) ≤ ((n + s : ℕ) : ℝ) := by
        push_cast; linarith [show (0 : ℝ) ≤ (s : ℝ) by positivity]
      linarith [inv_anti₀ hnpos hle]
    have hshift2 : (∑ n ∈ Finset.Ioc a x, ((n + s : ℕ) : ℝ)⁻¹)
        = ∑ m ∈ Finset.Ioc (a + s) (x + s), (m : ℝ)⁻¹ :=
      sum_Ioc_shift (fun m => (m : ℝ)⁻¹) a x s
    have hstep : (∑ n ∈ Finset.Ioc a x, f (n + s) * (n : ℝ)⁻¹)
                 - (∑ n ∈ Finset.Ioc a x, f (n + s) * ((n + s : ℕ) : ℝ)⁻¹)
        = ∑ n ∈ Finset.Ioc a x, f (n + s) * ((n : ℝ)⁻¹ - ((n + s : ℕ) : ℝ)⁻¹) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [hstep]
    calc |∑ n ∈ Finset.Ioc a x, f (n + s) * ((n : ℝ)⁻¹ - ((n + s : ℕ) : ℝ)⁻¹)|
        ≤ ∑ n ∈ Finset.Ioc a x, |f (n + s) * ((n : ℝ)⁻¹ - ((n + s : ℕ) : ℝ)⁻¹)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ioc a x, ((n : ℝ)⁻¹ - ((n + s : ℕ) : ℝ)⁻¹) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [abs_mul, abs_of_nonneg (hterm_nonneg n hn)]
          exact mul_le_of_le_one_left (hterm_nonneg n hn) (hf (n + s))
      _ = (∑ n ∈ Finset.Ioc a x, (n : ℝ)⁻¹)
            - (∑ n ∈ Finset.Ioc a x, ((n + s : ℕ) : ℝ)⁻¹) := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ n ∈ Finset.Ioc a x, (n : ℝ)⁻¹)
            - (∑ m ∈ Finset.Ioc (a + s) (x + s), (m : ℝ)⁻¹) := by rw [hshift2]
      _ = (∑ n ∈ Finset.Ioc a x \ Finset.Ioc (a + s) (x + s), (n : ℝ)⁻¹)
            - (∑ m ∈ Finset.Ioc (a + s) (x + s) \ Finset.Ioc a x, (m : ℝ)⁻¹) :=
          (Finset.sum_sdiff_sub_sum_sdiff).symm
      _ ≤ ∑ n ∈ Finset.Ioc a x \ Finset.Ioc (a + s) (x + s), (n : ℝ)⁻¹ := by
          have : (0 : ℝ)
              ≤ ∑ m ∈ Finset.Ioc (a + s) (x + s) \ Finset.Ioc a x, (m : ℝ)⁻¹ :=
            Finset.sum_nonneg (fun m _ => by positivity)
          linarith
      _ ≤ ∑ n ∈ Finset.Ioc a (a + s), (n : ℝ)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            rw [Finset.mem_sdiff, Finset.mem_Ioc, Finset.mem_Ioc] at hn
            rw [Finset.mem_Ioc]; omega
          · intro n _ _; positivity
      _ ≤ (s : ℝ) * ((ω : ℝ) / (x : ℝ)) := edge_sum_le a s hx hω ha.ge
  -- (ii) the window-shift sum, bounded by the two `s`-point edges (via `sum_sdiff`).
  have hAbound : |(∑ n ∈ Finset.Ioc a x, f (n + s) * ((n + s : ℕ) : ℝ)⁻¹)
                   - (∑ n ∈ Finset.Ioc a x, f n * (n : ℝ)⁻¹)|
      ≤ 2 * (s : ℝ) * ((ω : ℝ) / (x : ℝ)) := by
    have hR : (∑ n ∈ Finset.Ioc a x, f (n + s) * ((n + s : ℕ) : ℝ)⁻¹)
        = ∑ m ∈ Finset.Ioc (a + s) (x + s), f m * (m : ℝ)⁻¹ :=
      sum_Ioc_shift (fun m => f m * (m : ℝ)⁻¹) a x s
    rw [hR]
    have hAeq : (∑ m ∈ Finset.Ioc (a + s) (x + s), f m * (m : ℝ)⁻¹)
                 - (∑ n ∈ Finset.Ioc a x, f n * (n : ℝ)⁻¹)
        = (∑ m ∈ Finset.Ioc (a + s) (x + s) \ Finset.Ioc a x, f m * (m : ℝ)⁻¹)
          - (∑ n ∈ Finset.Ioc a x \ Finset.Ioc (a + s) (x + s), f n * (n : ℝ)⁻¹) :=
      (Finset.sum_sdiff_sub_sum_sdiff).symm
    rw [hAeq]
    have htri : ∀ X Y : ℝ, |X - Y| ≤ |X| + |Y| := fun X Y => by
      simpa using abs_sub_le X 0 Y
    have h1 : |∑ m ∈ Finset.Ioc (a + s) (x + s) \ Finset.Ioc a x, f m * (m : ℝ)⁻¹|
        ≤ (s : ℝ) * ((ω : ℝ) / (x : ℝ)) := by
      calc |∑ m ∈ Finset.Ioc (a + s) (x + s) \ Finset.Ioc a x, f m * (m : ℝ)⁻¹|
          ≤ ∑ m ∈ Finset.Ioc (a + s) (x + s) \ Finset.Ioc a x, |f m * (m : ℝ)⁻¹| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Ioc (a + s) (x + s) \ Finset.Ioc a x, (m : ℝ)⁻¹ := by
            apply Finset.sum_le_sum
            intro m _
            rw [abs_mul, abs_inv, Nat.abs_cast]
            exact mul_le_of_le_one_left (by positivity) (hf m)
        _ ≤ ∑ m ∈ Finset.Ioc x (x + s), (m : ℝ)⁻¹ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m hm
              rw [Finset.mem_sdiff, Finset.mem_Ioc, Finset.mem_Ioc] at hm
              rw [Finset.mem_Ioc]; omega
            · intro m _ _; positivity
        _ ≤ (s : ℝ) * ((ω : ℝ) / (x : ℝ)) := edge_sum_le x s hx hω (Nat.div_le_self x ω)
    have h2 : |∑ n ∈ Finset.Ioc a x \ Finset.Ioc (a + s) (x + s), f n * (n : ℝ)⁻¹|
        ≤ (s : ℝ) * ((ω : ℝ) / (x : ℝ)) := by
      calc |∑ n ∈ Finset.Ioc a x \ Finset.Ioc (a + s) (x + s), f n * (n : ℝ)⁻¹|
          ≤ ∑ n ∈ Finset.Ioc a x \ Finset.Ioc (a + s) (x + s), |f n * (n : ℝ)⁻¹| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.Ioc a x \ Finset.Ioc (a + s) (x + s), (n : ℝ)⁻¹ := by
            apply Finset.sum_le_sum
            intro n _
            rw [abs_mul, abs_inv, Nat.abs_cast]
            exact mul_le_of_le_one_left (by positivity) (hf n)
        _ ≤ ∑ n ∈ Finset.Ioc a (a + s), (n : ℝ)⁻¹ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro n hn
              rw [Finset.mem_sdiff, Finset.mem_Ioc, Finset.mem_Ioc] at hn
              rw [Finset.mem_Ioc]; omega
            · intro n _ _; positivity
        _ ≤ (s : ℝ) * ((ω : ℝ) / (x : ℝ)) := edge_sum_le a s hx hω ha.ge
    calc |(∑ m ∈ Finset.Ioc (a + s) (x + s) \ Finset.Ioc a x, f m * (m : ℝ)⁻¹)
            - (∑ n ∈ Finset.Ioc a x \ Finset.Ioc (a + s) (x + s), f n * (n : ℝ)⁻¹)|
        ≤ |∑ m ∈ Finset.Ioc (a + s) (x + s) \ Finset.Ioc a x, f m * (m : ℝ)⁻¹|
            + |∑ n ∈ Finset.Ioc a x \ Finset.Ioc (a + s) (x + s), f n * (n : ℝ)⁻¹| :=
          htri _ _
      _ ≤ (s : ℝ) * ((ω : ℝ) / (x : ℝ)) + (s : ℝ) * ((ω : ℝ) / (x : ℝ)) :=
          add_le_add h1 h2
      _ = 2 * (s : ℝ) * ((ω : ℝ) / (x : ℝ)) := by ring
  -- combine via the triangle inequality through the reindexed intermediate.
  calc |(∑ n ∈ Finset.Ioc a x, f (n + s) * (n : ℝ)⁻¹)
          - (∑ n ∈ Finset.Ioc a x, f n * (n : ℝ)⁻¹)|
      ≤ |(∑ n ∈ Finset.Ioc a x, f (n + s) * (n : ℝ)⁻¹)
            - (∑ n ∈ Finset.Ioc a x, f (n + s) * ((n + s : ℕ) : ℝ)⁻¹)|
          + |(∑ n ∈ Finset.Ioc a x, f (n + s) * ((n + s : ℕ) : ℝ)⁻¹)
            - (∑ n ∈ Finset.Ioc a x, f n * (n : ℝ)⁻¹)| :=
        abs_sub_le _ _ _
    _ ≤ (s : ℝ) * ((ω : ℝ) / (x : ℝ)) + 2 * (s : ℝ) * ((ω : ℝ) / (x : ℝ)) :=
        add_le_add hBbound hAbound
    _ = 3 * (s : ℝ) * (ω : ℝ) / (x : ℝ) := by ring

/-- **SHIFT-CORR (frozen).**  Approximate translation invariance for the expectation
of a bounded function against the log-sampling measure: for `|f| ≤ 1` and a shift `s`,

    |∫ f(n+s) − ∫ f(n)| ≤ (3·s·ω/x) / Z,   Z = ∑_{(x/ω, x]} 1/n.

The C-form is `3·s·ω/x`, of the frozen `c·s·ω/x`-grade STMT2's error budget needs. -/
theorem integral_shift_le (x ω s : ℕ) (hx : 2 ≤ x) (hω : 2 ≤ ω) (_hωx : ω ≤ x)
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) :
    |∫ n, f (n + s) ∂(logMeasure x ω) - ∫ n, f n ∂(logMeasure x ω)|
      ≤ 3 * (s : ℝ) * (ω : ℝ) / (x : ℝ)
          / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
  have hZpos : 0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    apply Finset.sum_pos _ (window_nonempty hx hω)
    intro n hn
    have h1 : 0 < n := window_one_le hn
    have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h1
    exact inv_pos.mpr h2
  have e1 : ∫ n, f (n + s) ∂(logMeasure x ω)
      = (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * ∑ n ∈ Finset.Ioc (x / ω) x, f (n + s) * (n : ℝ)⁻¹ :=
    integral_logMeasure_eq (fun n => f (n + s)) x ω
  have e2 : ∫ n, f n ∂(logMeasure x ω)
      = (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹ :=
    integral_logMeasure_eq f x ω
  rw [e1, e2, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hZpos)]
  have hbound := sum_shift_bound x ω s (by omega) (by omega) f hf
  calc (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * |(∑ n ∈ Finset.Ioc (x / ω) x, f (n + s) * (n : ℝ)⁻¹)
              - (∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹)|
      ≤ (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * (3 * (s : ℝ) * (ω : ℝ) / (x : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hZpos.le)
    _ = 3 * (s : ℝ) * (ω : ℝ) / (x : ℝ)
          / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
        ring

/-- Every real-cast Liouville value has modulus `≤ 1` (`±1` on positive args, `0` at `0`). -/
private lemma abs_liouville_le_one (k : ℕ) :
    |(ArithmeticFunction.liouville k : ℝ)| ≤ 1 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [ArithmeticFunction.liouville_apply hk]; push_cast; simp [abs_pow]

/-- **The direct consumer form (STMT2 `hreduce`).**  Shift invariance at `s = 1` for
the dilated Liouville correlation: `∫ λ(n+1+a)λ(n+1+b) − ∫ λ(n+a)λ(n+b)` is `≤ 3ω/x/Z`.
This is `integral_shift_le` at `f := fun n => λ(n+a)·λ(n+b)`, `s := 1`. -/
theorem corr_shift_le (a b : ℕ) {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) :
    |∫ n, (ArithmeticFunction.liouville (n + 1 + a) : ℝ)
            * (ArithmeticFunction.liouville (n + 1 + b) : ℝ) ∂(logMeasure x ω)
       - ∫ n, (ArithmeticFunction.liouville (n + a) : ℝ)
            * (ArithmeticFunction.liouville (n + b) : ℝ) ∂(logMeasure x ω)|
      ≤ 3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
  have hf : ∀ n : ℕ, |(ArithmeticFunction.liouville (n + a) : ℝ)
      * (ArithmeticFunction.liouville (n + b) : ℝ)| ≤ 1 := fun n => by
    rw [abs_mul]
    exact mul_le_one₀ (abs_liouville_le_one _) (abs_nonneg _) (abs_liouville_le_one _)
  have h := integral_shift_le x ω 1 hx hω hωx
    (fun n => (ArithmeticFunction.liouville (n + a) : ℝ)
            * (ArithmeticFunction.liouville (n + b) : ℝ)) hf
  simpa using h

end Salt.Entropy.Chowla
