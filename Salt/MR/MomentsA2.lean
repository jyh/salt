/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.MR.L2MVT
import Salt.MR.MVCore2
import Salt.MR.ShiuMoment

/-!
# MomentsA2 — the Lemma 12 / Lemma 13 moment machinery (S8 / MR-CORE, node A2)

The Matomäki–Radziwiłł moment/decomposition wave (MR §5–6, source
`docs/sources/1501.04585v4.pdf` pp.19–21; extract `docs/sources/mr_extract.md`
§2.2/2.5).  This file carries the **deferred D-class analytic keystone** that the
Decomp executor left for wave-4 A2: the mean-square (second-moment) bound for
Dirichlet polynomials in the `Σ_{X≤n≤2X} aₙ/n^{1+it}` form, on the landed
`(2T + 20N)` Montgomery–Vaughan MVT (`dirichlet_poly_l2_mvt_final`).

## The workhorse identity

For `n ≥ 1`, `n^{1+it} = n · e^{it log n}`, so

  `aₙ / n^{1+it} = (aₙ/n) · e^{-it log n}`,

i.e. `spoly N a t = dpoly N (aₙ/n) (-t)` where `dpoly` is the campaign's
mean-value Dirichlet polynomial (`Salt.MR.dpoly`).  The `∫_{-T}^{T}` interval is
symmetric, so the reflection `t ↦ -t` is free and the landed `(2T+20N)` MVT
transfers verbatim.  This is the analytic engine behind:

* **Lemma 12** (MR p.19–20): the Ramaré/Buchstab mean-square split — the main term
  is kept via **Cauchy–Schwarz over the block index `j`** and the error terms are
  bounded by this MVT.  (The eq (16) → Dirichlet-identity bridge is carried as a
  named seam `RAMARE-DPOLY`; the Ramaré combinatorial identity itself is landed as
  `Salt.MR.ramare_decomp`.)
* **Lemma 13** (MR p.20–21, eq (17)/(18)): the moment computation
  `∫_{-T}^{T} |Q(1+it)^ℓ A(1+it)|² dt ≪ (T/X + 2^ℓ Y₁)(ℓ+1)!²` — the analytic core
  is this MVT + the landed `shiu_moment_sq` (eq (18)); the coefficient-convolution
  count `|coeffₙ| ≤ ℓ!·g(n)` is carried as the named seam `MULT-SHIU`.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`), §§5–6.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory intervalIntegral Complex

/-- **The `σ = 1` Dirichlet polynomial** `F(t) = Σ_{1≤n≤N} aₙ / n^{1+it}` — the
object of MR Lemmas 12–14 (the paper's `Σ_{X≤n≤2X} aₙ/n^{1+it}`, with the lower
window folded into the coefficient `a`). -/
noncomputable def spoly (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)

/-- **The workhorse bridge.**  `spoly N a t = dpoly N (aₙ/n) (-t)`: the `σ=1`
Dirichlet polynomial is the mean-value Dirichlet polynomial with coefficients
`aₙ/n` at reflected frequency, since `n^{1+it} = n · e^{it log n}`. -/
lemma spoly_eq_dpoly (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    spoly N a t = dpoly N (fun n => a n / (n : ℂ)) (-t) := by
  rw [spoly, dpoly]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hlog : Complex.exp (-(Real.log n : ℂ)) = (n : ℂ)⁻¹ := by
    rw [Complex.natCast_log, Complex.exp_neg, Complex.exp_log hnC]
  rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log, div_eq_mul_inv,
    ← Complex.exp_neg, Complex.ofReal_neg]
  rw [show -((Real.log n : ℂ) * ((1 : ℂ) + (t : ℂ) * Complex.I))
        = -(Real.log n : ℂ) + Complex.I * (-(t : ℂ)) * (Real.log n : ℂ) by ring,
    Complex.exp_add, hlog]
  ring

/-- **THE DEFERRED KEYSTONE (G1's MVT machinery, MR Lemma 6 in `σ=1` form).**
The second-moment bound for the `Σ aₙ/n^{1+it}` Dirichlet polynomial:
`∫_{-T}^{T} |Σ_{1≤n≤N} aₙ/n^{1+it}|² dt ≤ (2T + 20N) · Σ_{1≤n≤N} |aₙ|²/n²`.

This is the piece the Decomp executor deferred ("Lemma 12's full mean-square
inequality is D-class analytic… left for wave-4 A2, which holds the MVT
machinery").  It rides the landed unconditional `dirichlet_poly_l2_mvt_final`. -/
theorem moment_core_bound (N : ℕ) (a : ℕ → ℂ) (T : ℝ) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
  -- rewrite the integrand through the bridge
  have hcongr : (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      = ∫ t in (-T)..T, ‖dpoly N (fun n => a n / (n : ℂ)) (-t)‖ ^ 2 := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [spoly_eq_dpoly]
  rw [hcongr]
  -- reflect t ↦ -t on the symmetric interval
  have hrefl : (∫ t in (-T)..T, ‖dpoly N (fun n => a n / (n : ℂ)) (-t)‖ ^ 2)
      = ∫ t in (-T)..T, ‖dpoly N (fun n => a n / (n : ℂ)) t‖ ^ 2 := by
    have h := intervalIntegral.integral_comp_neg
      (a := -T) (b := T) (fun x => ‖dpoly N (fun n => a n / (n : ℂ)) x‖ ^ 2)
    simpa using h
  rw [hrefl]
  -- the landed MVT, then rewrite the coefficient norms
  refine (dirichlet_poly_l2_mvt_final N (fun n => a n / (n : ℂ)) T).trans_eq ?_
  refine congrArg (fun s => (2 * T + 20 * (N : ℝ)) * s) ?_
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [norm_div, Complex.norm_natCast, div_pow]

/-- **G3 — the large-`T` sub-rung (prefactor absorption).**  The keystone
`moment_core_bound` is already `T`-uniform: its prefactor `2T + 20N` carries no
upper cutoff on `T`.  In the large-`T` regime `T ≥ N` (the freeze's "`T > X`
regimes via trivial MVT + prefactor absorption") the prefactor collapses to
`22T`, so the second moment is a clean `O(T)·Σ|aₙ|²/n²` uniformly — no separate
large-`T` machinery is needed.  This is what makes the downstream `prop_A3'`
`T`-uniform. -/
theorem moment_core_bound_large_T (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : (N : ℝ) ≤ T) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ 22 * T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
  refine (moment_core_bound N a T).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun n _ => by positivity))
  linarith [hT]

/-! ## G2 — the Lemma 13 moment (MR §6, eq (17)/(18)) -/

/-- **The dyadic-geometric Shiu sum** (MR eq (17)→(18): "split the sum over `n`
into dyadic intervals and apply (18)").  For the block-divisor `g = blockDiv Y₁`,
`Σ_{X ≤ n ≤ M} g(n)²/n² ≤ 3C/X`, **uniformly in the upper endpoint `M`**, where
`C` is the absolute Shiu constant of `shiu_moment_sq`.  The `1/n²` weight makes the
dyadic-block bounds `C/(2^k X)` geometrically summable, so the length of the range
is irrelevant.  This is the analytic core of Lemma 13. -/
lemma blockDiv_sq_div_sq_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y₁ X M : ℕ), 1 ≤ Y₁ → 1 ≤ X →
      ∑ n ∈ Finset.Icc X M, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
        ≤ 3 * C / (X : ℝ) := by
  obtain ⟨C, hC, hShiu⟩ := shiu_moment_sq
  refine ⟨C, hC, ?_⟩
  intro Y₁ X M hY₁ hX
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  -- one dyadic block: Σ_{Y≤n≤2Y} g²/n² ≤ C/Y (shiu_moment_sq + 1/n²≤1/Y²).
  have block : ∀ Y : ℕ, 1 ≤ Y →
      ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
        ≤ C / (Y : ℝ) := by
    intro Y hY
    have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
    calc ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 / (Y : ℝ) ^ 2 := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have hYn : (Y : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          gcongr
      _ = (1 / (Y : ℝ) ^ 2) * ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun n _ => by ring)
      _ ≤ (1 / (Y : ℝ) ^ 2) * (C * (Y : ℝ)) :=
          mul_le_mul_of_nonneg_left (hShiu Y₁ Y hY₁) (by positivity)
      _ = C / (Y : ℝ) := by field_simp
  -- induction on K: Σ_{X≤n≤2^K X} g²/n² ≤ (C/X)(3−2/2^K), geometric-slack invariant.
  have key : ∀ K : ℕ,
      ∑ n ∈ Finset.Icc X (2 ^ K * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
      ≤ (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ K) := by
    intro K
    induction K with
    | zero =>
      have h1 : Finset.Icc X (2 ^ 0 * X) ⊆ Finset.Icc X (2 * X) := by
        apply Finset.Icc_subset_Icc_right; simp only [pow_zero, one_mul]; omega
      calc ∑ n ∈ Finset.Icc X (2 ^ 0 * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
          ≤ ∑ n ∈ Finset.Icc X (2 * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg h1 (fun _ _ _ => by positivity)
        _ ≤ C / (X : ℝ) := block X hX
        _ = (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ 0) := by norm_num
    | succ K ih =>
      set Y : ℕ := 2 ^ K * X with hYdef
      have hYpos : 1 ≤ Y := by rw [hYdef]; exact Nat.mul_pos (by positivity) hX
      have hYr : (0 : ℝ) < Y := by exact_mod_cast hYpos
      have hXne : (X : ℝ) ≠ 0 := hXr.ne'
      have hp0 : (2 : ℝ) ^ K ≠ 0 := by positivity
      have hYeq : (Y : ℝ) = (2 : ℝ) ^ K * (X : ℝ) := by rw [hYdef]; push_cast; ring
      have hcover : Finset.Icc X (2 ^ (K + 1) * X)
          ⊆ Finset.Icc X Y ∪ Finset.Icc Y (2 * Y) := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        have h2Y : 2 ^ (K + 1) * X = 2 * Y := by rw [hYdef]; ring
        rw [h2Y] at hn
        rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
        by_cases hnY : n ≤ Y
        · exact Or.inl ⟨hn.1, hnY⟩
        · exact Or.inr ⟨by omega, hn.2⟩
      have hsplit :
          ∑ n ∈ Finset.Icc X (2 ^ (K + 1) * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
          ≤ (∑ n ∈ Finset.Icc X Y, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2)
            + ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
        have hle :
            ∑ n ∈ Finset.Icc X (2 ^ (K + 1) * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
            ≤ ∑ n ∈ Finset.Icc X Y ∪ Finset.Icc Y (2 * Y),
                (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover (fun i _ _ => by positivity)
        have hui : (∑ n ∈ Finset.Icc X Y ∪ Finset.Icc Y (2 * Y),
                (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2)
              + (∑ n ∈ Finset.Icc X Y ∩ Finset.Icc Y (2 * Y),
                (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2)
            = (∑ n ∈ Finset.Icc X Y, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2)
              + ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
          Finset.sum_union_inter
        have hinter : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc X Y ∩ Finset.Icc Y (2 * Y),
            (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
          Finset.sum_nonneg (fun _ _ => by positivity)
        linarith [hle, hui, hinter]
      have hXYr : ∑ n ∈ Finset.Icc X Y, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
          ≤ (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ K) := ih
      calc ∑ n ∈ Finset.Icc X (2 ^ (K + 1) * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
          ≤ (∑ n ∈ Finset.Icc X Y, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2)
            + ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 := hsplit
        _ ≤ (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ K)
              + (C / (X : ℝ)) * (1 / (2 : ℝ) ^ K) := by
            refine add_le_add hXYr ((block Y hYpos).trans_eq ?_)
            rw [mul_one_div, div_div, mul_comm (X : ℝ) ((2 : ℝ) ^ K), ← hYeq]
        _ = (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ (K + 1)) := by
            have hp : (2 : ℝ) ^ (K + 1) = 2 * (2 : ℝ) ^ K := by rw [pow_succ]; ring
            rw [hp]; ring
  -- choose `K = M`, so `M ≤ 2^M·X` and `Icc X M ⊆ Icc X (2^M·X)`.
  have hMsub : Finset.Icc X M ⊆ Finset.Icc X (2 ^ M * X) := by
    apply Finset.Icc_subset_Icc_right
    calc M ≤ 2 ^ M := (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ M * X := Nat.le_mul_of_pos_right _ hX
  have hgeo : (0 : ℝ) < 2 / (2 : ℝ) ^ M := by positivity
  calc ∑ n ∈ Finset.Icc X M, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc X (2 ^ M * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hMsub (fun _ _ _ => by positivity)
    _ ≤ (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ M) := key M
    _ ≤ 3 * C / (X : ℝ) := by
        have hCX : (0 : ℝ) ≤ C / (X : ℝ) := by positivity
        have hstep : (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ M) ≤ (C / (X : ℝ)) * 3 :=
          mul_le_mul_of_nonneg_left (by linarith [hgeo]) hCX
        calc (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ M) ≤ (C / (X : ℝ)) * 3 := hstep
          _ = 3 * C / (X : ℝ) := by ring

/-- **G2 — MR Lemma 13 (the moment computation, eq (17)/(18)).**  For the
Dirichlet polynomial `Q(1+it)^ℓ A(1+it) = Σ_{n} aₙ/n^{1+it}` with coefficients
`a` supported on `[X, N]` and satisfying the count bound `|aₙ| ≤ ℓ!·g(n)`
(`g = blockDiv Y₁`), the second moment is

  `∫_{-T}^{T} |Q(1+it)^ℓ A(1+it)|² dt ≤ (2T + 20N)·ℓ!²·(3C/X)`.

The analytic core is the keystone `moment_core_bound` (the MVT, eq (17)) + the
dyadic Shiu sum `blockDiv_sq_div_sq_sum_le` (eq (18)).  The two hypotheses
`hsupp`/`hcoeff` are exactly the **named seam `MULT-SHIU`**: the convolution
identity `Q^ℓ A = Σ aₙ/n^s` with coefficients supported on `[X, 2^{ℓ+1}Y₁X]` and
inner count `≤ ℓ!·g(n)` (MR p.20–21, the combinatorial step before eq (17)).  A
caller instantiating `N = 2^{ℓ+1}Y₁X` recovers the paper's `(T/X + 2^ℓ Y₁)ℓ!²`
shape (the `2^{ℓ+1}` vs `2^ℓ` and `ℓ!²` vs `(ℓ+1)!²` gaps are the admitted `C^ℓ`
slop). -/
theorem lemma13_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y₁ X N ℓ : ℕ) (a : ℕ → ℂ) (T : ℝ),
      1 ≤ Y₁ → 1 ≤ X → 0 ≤ T → (∀ n, n < X → a n = 0) →
      (∀ n, ‖a n‖ ≤ (ℓ.factorial : ℝ) * (blockDiv Y₁ n : ℝ)) →
      (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
        ≤ (2 * T + 20 * (N : ℝ)) * ((ℓ.factorial : ℝ) ^ 2 * (C / (X : ℝ))) := by
  obtain ⟨C, hC, hShiuSum⟩ := blockDiv_sq_div_sq_sum_le
  refine ⟨3 * C, by positivity, ?_⟩
  intro Y₁ X N ℓ a T hY₁ hX hT hsupp hcoeff
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hpre : (0 : ℝ) ≤ 2 * T + 20 * (N : ℝ) := by
    have hN := Nat.cast_nonneg (α := ℝ) N; linarith
  -- the coefficient L²-sum bound (eq (17) → (18))
  have hkey : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ (ℓ.factorial : ℝ) ^ 2 * (3 * C / (X : ℝ)) := by
    have hsub : Finset.Icc X N ⊆ Finset.Icc 1 N := by
      intro n hn; rw [Finset.mem_Icc] at *; omega
    have heq : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        = ∑ n ∈ Finset.Icc X N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
      refine (Finset.sum_subset hsub ?_).symm
      intro x hx hxni
      have hxX : x < X := by
        rw [Finset.mem_Icc] at hx
        by_contra h; exact hxni (Finset.mem_Icc.mpr ⟨not_lt.mp h, hx.2⟩)
      rw [hsupp x hxX, norm_zero]; simp
    rw [heq]
    calc ∑ n ∈ Finset.Icc X N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Icc X N,
            ((ℓ.factorial : ℝ) ^ 2 * (blockDiv Y₁ n : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          have h1 : ‖a n‖ ^ 2 ≤ (ℓ.factorial : ℝ) ^ 2 * (blockDiv Y₁ n : ℝ) ^ 2 := by
            nlinarith [hcoeff n, norm_nonneg (a n),
              mul_nonneg (Nat.cast_nonneg (α := ℝ) ℓ.factorial)
                (Nat.cast_nonneg (α := ℝ) (blockDiv Y₁ n))]
          gcongr
      _ = (ℓ.factorial : ℝ) ^ 2
            * ∑ n ∈ Finset.Icc X N, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun n _ => by ring)
      _ ≤ (ℓ.factorial : ℝ) ^ 2 * (3 * C / (X : ℝ)) :=
          mul_le_mul_of_nonneg_left (hShiuSum Y₁ X N hY₁ hX) (by positivity)
  -- assemble via the keystone MVT
  calc (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 :=
        moment_core_bound N a T
    _ ≤ (2 * T + 20 * (N : ℝ)) * ((ℓ.factorial : ℝ) ^ 2 * (3 * C / (X : ℝ))) :=
        mul_le_mul_of_nonneg_left hkey hpre

/-! ## G1 — the Cauchy–Schwarz-over-`j` step of MR Lemma 12 (p.20)

MR Lemma 12's proof, after the Ramaré identity (eq (16), landed as
`Salt.MR.ramare_decomp`), reads: "We square this, integrate over `𝒯` and then
apply **Cauchy–Schwarz on the first sum over `j`** and the mean-value theorem
(Lemma 6) on the remaining sums."  The mean-value theorem is the keystone
`moment_core_bound`; the Cauchy–Schwarz-over-`j` step is exactly the two lemmas
below.  The remaining eq (16) → Dirichlet-identity bridge (the construction of the
`Q_{j,H} R_{j,H}` polynomials and the `d_m`/diagonal/coprime-tail error split) is
the named seam **RAMARE-DPOLY**. -/

/-- **Cauchy–Schwarz over the block index `j`** (pointwise).  `‖Σ_{j∈s} z j‖² ≤
#s · Σ_{j∈s} ‖z j‖²` — the finite-sum Cauchy–Schwarz that MR Lemma 12 applies to
the sum over `j ∈ I`. -/
theorem cauchy_schwarz_sum_sq {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ‖∑ j ∈ s, z j‖ ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, ‖z j‖ ^ 2 := by
  have h1 : ‖∑ j ∈ s, z j‖ ≤ ∑ j ∈ s, ‖z j‖ := norm_sum_le s z
  have h2 : (∑ j ∈ s, ‖z j‖) ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, ‖z j‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun j => ‖z j‖) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    calc (∑ j ∈ s, ‖z j‖) ^ 2
        ≤ (∑ j ∈ s, ‖z j‖ ^ 2) * (s.card : ℝ) := hcs
      _ = (s.card : ℝ) * ∑ j ∈ s, ‖z j‖ ^ 2 := by ring
  have h0 : (0 : ℝ) ≤ ‖∑ j ∈ s, z j‖ := norm_nonneg _
  nlinarith [h1, h2, h0]

/-- **Cauchy–Schwarz over `j`, integrated** (MR Lemma 12 main-term step, on the
interval).  For continuous polynomials `u j`, `∫_a^b ‖Σ_{j∈s} u j t‖² dt ≤
#s · Σ_{j∈s} ∫_a^b ‖u j t‖² dt`.  Integrability is free from continuity; the
generalisation to a thin set `𝒯 ⊆ [-T,T]` (the `𝒰`-integral of §8.3) is the
measure-restriction refinement noted in the report. -/
theorem cauchy_schwarz_intervalIntegral {ι : Type*} (s : Finset ι) (u : ι → ℝ → ℂ)
    (a b : ℝ) (hab : a ≤ b) (hu : ∀ j ∈ s, Continuous (u j)) :
    (∫ t in a..b, ‖∑ j ∈ s, u j t‖ ^ 2)
      ≤ (s.card : ℝ) * ∑ j ∈ s, ∫ t in a..b, ‖u j t‖ ^ 2 := by
  have hcont_sum : Continuous (fun t => ∑ j ∈ s, u j t) :=
    continuous_finsetSum s (fun j hj => hu j hj)
  have hInt_f : IntervalIntegrable (fun t => ‖∑ j ∈ s, u j t‖ ^ 2) volume a b :=
    (hcont_sum.norm.pow 2).intervalIntegrable a b
  have hInt_uj : ∀ j ∈ s, IntervalIntegrable (fun t => ‖u j t‖ ^ 2) volume a b :=
    fun j hj => ((hu j hj).norm.pow 2).intervalIntegrable a b
  have hfe : (fun t => ∑ j ∈ s, ‖u j t‖ ^ 2) = ∑ i ∈ s, (fun t => ‖u i t‖ ^ 2) := by
    funext t; simp only [Finset.sum_apply]
  have hsumInt : IntervalIntegrable (fun t => ∑ j ∈ s, ‖u j t‖ ^ 2) volume a b := by
    rw [hfe]; exact IntervalIntegrable.sum s hInt_uj
  have hInt_g : IntervalIntegrable
      (fun t => (s.card : ℝ) * ∑ j ∈ s, ‖u j t‖ ^ 2) volume a b :=
    hsumInt.const_mul _
  calc (∫ t in a..b, ‖∑ j ∈ s, u j t‖ ^ 2)
      ≤ ∫ t in a..b, (s.card : ℝ) * ∑ j ∈ s, ‖u j t‖ ^ 2 := by
        refine intervalIntegral.integral_mono_on hab hInt_f hInt_g (fun t _ => ?_)
        exact cauchy_schwarz_sum_sq s (fun j => u j t)
    _ = (s.card : ℝ) * ∑ j ∈ s, ∫ t in a..b, ‖u j t‖ ^ 2 := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        exact intervalIntegral.integral_finsetSum (f := fun j t => ‖u j t‖ ^ 2) hInt_uj

/-- **G1 — MR Lemma 12 mean-square, assembled (conditional on RAMARE-DPOLY).**
Given the eq (16) Dirichlet-polynomial decomposition of `spoly` into the main
block sum `Σ_{j∈I} mainPoly j` plus an error polynomial `errPoly` (the seam
`RAMARE-DPOLY`), together with a bound `E` on the error second-moment (supplied by
the keystone `moment_core_bound` on the error coefficients), the full mean-square
splits as

  `∫ ‖spoly‖² ≤ 2·#I·Σ_{j∈I} ∫ ‖mainPoly j‖² + 2E`.

The main term rides `cauchy_schwarz_intervalIntegral` (the "Cauchy–Schwarz on the
sum over `j`" of MR p.20); the `2·(…)+2(…)` split is the free `‖x+y‖² ≤
2‖x‖²+2‖y‖²`.  Instantiating `mainPoly = Q_{j,H} R_{j,H}` and `E = (T+X)/X·(1/H +
1/P + Σ_{(n,Π)=1}|aₙ|²/n)` recovers the paper's `H log(Q/P)·Σ_j ∫|Q_{j,H}R_{j,H}|²
+ (T+X)/X·(…)` (the `#I ≈ H log(Q/P)` count and the factor 2 are absorbed). -/
theorem lemma12_meansq_conditional {N : ℕ} {a : ℕ → ℂ} {I : Finset ℕ}
    {mainPoly : ℕ → ℝ → ℂ} {errPoly : ℝ → ℂ} {E lo hi : ℝ}
    (hlohi : lo ≤ hi)
    (hmain_cont : ∀ j ∈ I, Continuous (mainPoly j))
    (herr_cont : Continuous errPoly)
    (hdecomp : ∀ t, spoly N a t = (∑ j ∈ I, mainPoly j t) + errPoly t)
    (herr : (∫ t in lo..hi, ‖errPoly t‖ ^ 2) ≤ E) :
    (∫ t in lo..hi, ‖spoly N a t‖ ^ 2)
      ≤ 2 * (I.card : ℝ) * (∑ j ∈ I, ∫ t in lo..hi, ‖mainPoly j t‖ ^ 2) + 2 * E := by
  have hcongr : (∫ t in lo..hi, ‖spoly N a t‖ ^ 2)
      = ∫ t in lo..hi, ‖(∑ j ∈ I, mainPoly j t) + errPoly t‖ ^ 2 :=
    intervalIntegral.integral_congr (fun t _ => by rw [hdecomp])
  rw [hcongr]
  have hmc : Continuous (fun t => ∑ j ∈ I, mainPoly j t) := continuous_finsetSum I hmain_cont
  have hInt_main : IntervalIntegrable (fun t => ‖∑ j ∈ I, mainPoly j t‖ ^ 2) volume lo hi :=
    (hmc.norm.pow 2).intervalIntegrable lo hi
  have hInt_err : IntervalIntegrable (fun t => ‖errPoly t‖ ^ 2) volume lo hi :=
    (herr_cont.norm.pow 2).intervalIntegrable lo hi
  have hInt_lhs : IntervalIntegrable
      (fun t => ‖(∑ j ∈ I, mainPoly j t) + errPoly t‖ ^ 2) volume lo hi :=
    ((hmc.add herr_cont).norm.pow 2).intervalIntegrable lo hi
  have hInt_rhs : IntervalIntegrable
      (fun t => 2 * ‖∑ j ∈ I, mainPoly j t‖ ^ 2 + 2 * ‖errPoly t‖ ^ 2) volume lo hi :=
    (hInt_main.const_mul 2).add (hInt_err.const_mul 2)
  calc (∫ t in lo..hi, ‖(∑ j ∈ I, mainPoly j t) + errPoly t‖ ^ 2)
      ≤ ∫ t in lo..hi, (2 * ‖∑ j ∈ I, mainPoly j t‖ ^ 2 + 2 * ‖errPoly t‖ ^ 2) := by
        refine intervalIntegral.integral_mono_on hlohi hInt_lhs hInt_rhs (fun t _ => ?_)
        nlinarith [norm_add_le (∑ j ∈ I, mainPoly j t) (errPoly t),
          norm_nonneg (∑ j ∈ I, mainPoly j t), norm_nonneg (errPoly t),
          norm_nonneg ((∑ j ∈ I, mainPoly j t) + errPoly t),
          sq_nonneg (‖∑ j ∈ I, mainPoly j t‖ - ‖errPoly t‖)]
    _ = 2 * (∫ t in lo..hi, ‖∑ j ∈ I, mainPoly j t‖ ^ 2)
          + 2 * (∫ t in lo..hi, ‖errPoly t‖ ^ 2) := by
        rw [intervalIntegral.integral_add (hInt_main.const_mul 2) (hInt_err.const_mul 2),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ 2 * ((I.card : ℝ) * ∑ j ∈ I, ∫ t in lo..hi, ‖mainPoly j t‖ ^ 2) + 2 * E := by
        have hcs := cauchy_schwarz_intervalIntegral I mainPoly lo hi hlohi hmain_cont
        gcongr
    _ = 2 * (I.card : ℝ) * (∑ j ∈ I, ∫ t in lo..hi, ‖mainPoly j t‖ ^ 2) + 2 * E := by
        ring

end Salt.MR
