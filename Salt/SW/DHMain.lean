/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.DHClose

/-!
# The Deuring–Heilbronn mollified ρ-shift: the Barban–Vehov cancellation (HB-ENGINE, DH-MAIN)

Design: `docs/exploration/s3-hb3-design.md`, "DH-2b — THE PRODUCT-DETECTOR FREEZE".
Source: Benlİ–Goel–Twiss–Zaman, arXiv:2410.06082, §§4–5; Graham, *An asymptotic estimate
related to Selberg's sieve* (the Barban–Vehov weight cancellation).

This is the final brick of the DH repulsion. The predecessors ground the campaign to the
mollified ρ-shift; `DH-2b-v` proved q-only bounds provably cannot reach the ρ-dependent
target, so the shift is the sole crux. This module builds the FIRST rung of the Zeno
ladder — the **sharp Barban–Vehov cancellation** `|Σ_{d≤z} θ_d/d| ≤ C/log z`, the
`GrahamWeights` residual (2), a standalone stone valuable regardless of the higher rungs.

## The identity (the Abel seam the `GrahamWeights` header named)

With the weighted Möbius partial sum `Mw(k) = Σ_{d≤k} μ(d)/d`, discrete summation by parts
(via `log(z/d) = Σ_{k=d}^{z-1} log((k+1)/k)` and a triangular sum-swap) gives the exact,
PNT-free identity

  `Σ_{d≤z} (μ(d)/d)·log(z/d) = Σ_{k=1}^{z-1} Mw(k)·(log(k+1) − log k)`.

Since `θ_d/d = (μ(d)/d)·log(z/d)/log z` on `d ≤ z`, dividing by `log z` turns any bound on
the RHS into a bound on `Σ_{d≤z} θ_d/d`.

## Honesty / death map (HB-ENGINE, R4 — NO twin claim)

NOT a proof of the Twin Prime Conjecture. Delivers competing-estimate substrate for the
conditional `InfinitelyManySiegelZeros → TwinPrimeConjecture`; the death rung is R4.
-/

open Complex

noncomputable section

namespace Salt.SW

open ArithmeticFunction Finset MeasureTheory

/-- The weighted Möbius partial sum `Mw(n) = Σ_{d≤n} μ(d)/d`. -/
noncomputable def mwWeighted (n : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 n, (moebius d : ℝ) / (d : ℝ)

/-! ## Rung 1b — the elementary uniform bound `|Mw(n)| ≤ 1`

The classical Möbius floor identity `Σ_{d≤n} μ(d)⌊n/d⌋ = 1` (from `Σ_{d∣m} μ(d) = [m=1]`
summed over `m ≤ n` and reorganized by the multiples count `⌊n/d⌋ = #{m ≤ n : d∣m}`), with
`⌊n/d⌋ = n/d − (n%d)/d`, gives `n·Mw(n) = 1 + Σ_{d≤n} μ(d)(n%d)/d`. The error sum has
`|·| ≤ n−1` (the `d=1` term vanishes, the rest are `< 1`), so `|Mw(n)| ≤ 1`. -/

/-- **The Möbius floor identity** `Σ_{d≤n} μ(d)·⌊n/d⌋ = 1` for `n ≥ 1`. Route: `⌊n/d⌋` is the
count of multiples of `d` in `(0,n]` (`Nat.Ioc_filter_dvd_card_eq_div`); swapping the double
sum regroups by the multiple `x`, whose inner sum `Σ_{d∣x} μ(d) = [x=1]`
(`coe_mul_zeta_apply` + `moebius_mul_coe_zeta`); only `x = 1` survives. -/
lemma sum_moebius_mul_div_eq_one {n : ℕ} (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (moebius d : ℤ) * ((n / d : ℕ) : ℤ) = 1 := by
  have hcard : ∀ d ∈ Finset.Icc 1 n, (moebius d : ℤ) * ((n / d : ℕ) : ℤ)
      = ∑ x ∈ Finset.filter (fun x => d ∣ x) (Finset.Ioc 0 n), (moebius d : ℤ) := by
    intro d _
    rw [Finset.sum_const, ← Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl hcard]
  -- Swap the double sum: regroup by the multiple `x`.
  rw [Finset.sum_comm' (t' := Finset.Ioc 0 n) (s' := fun x => Finset.filter (· ∣ x)
    (Finset.Icc 1 n)) (by
      intro d x
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      tauto)]
  -- Inner sum over divisors: `Σ_{d∣x} μ(d) = [x=1]`.
  have hinner : ∀ x ∈ Finset.Ioc 0 n,
      ∑ d ∈ Finset.filter (· ∣ x) (Finset.Icc 1 n), (moebius d : ℤ)
        = if x = 1 then (1 : ℤ) else 0 := by
    intro x hx
    obtain ⟨hx0, hxn⟩ := Finset.mem_Ioc.mp hx
    have hset : Finset.filter (· ∣ x) (Finset.Icc 1 n) = x.divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_, _⟩, hdx⟩; exact ⟨hdx, by omega⟩
      · rintro ⟨hdx, _⟩
        have hd0 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (fun h => by simp [h] at hdx; omega)
        exact ⟨⟨hd0, le_trans (Nat.le_of_dvd (by omega) hdx) hxn⟩, hdx⟩
    rw [hset, ← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' (Finset.Ioc 0 n) 1 (fun _ => (1 : ℤ))]
  simp [Finset.mem_Ioc, hn]

/-- **Rung 1b — the uniform bound `|Mw(n)| ≤ 1`.** For `n ≥ 1`, the weighted Möbius partial
sum satisfies `|Σ_{d≤n} μ(d)/d| ≤ 1`. Route: the floor identity gives
`n·Mw(n) = 1 + Σ_{d≤n} μ(d)(n%d)/d`, whose error sum is `≤ n−1` (the `d=1` term is `0`, the
rest are each `< 1`). Elementary and PNT-free. -/
lemma abs_mwWeighted_le_one {n : ℕ} (hn : 1 ≤ n) : |mwWeighted n| ≤ 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- The floor identity, cast to `ℝ`.
  have hfloorR : ∑ d ∈ Finset.Icc 1 n, (moebius d : ℝ) * ((n / d : ℕ) : ℝ) = 1 := by
    have h := sum_moebius_mul_div_eq_one hn
    have key : ∑ d ∈ Finset.Icc 1 n, (moebius d : ℝ) * ((n / d : ℕ) : ℝ)
        = ((∑ d ∈ Finset.Icc 1 n, (moebius d : ℤ) * ((n / d : ℕ) : ℤ) : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun d _ => by rw [Int.cast_mul, Int.cast_natCast]
    rw [key, h, Int.cast_one]
  -- Split `⌊n/d⌋ = n/d − (n%d)/d`.
  have hmod : ∀ d ∈ Finset.Icc 1 n, (moebius d : ℝ) * ((n / d : ℕ) : ℝ)
      = (n : ℝ) * ((moebius d : ℝ) / (d : ℝ))
        - (moebius d : ℝ) * ((n % d : ℕ) : ℝ) / (d : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hdm : (d : ℝ) * ((n / d : ℕ) : ℝ) + ((n % d : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.div_add_mod n d
    have hquot : ((n / d : ℕ) : ℝ) = ((n : ℝ) - ((n % d : ℕ) : ℝ)) / (d : ℝ) := by
      rw [eq_div_iff hdR]; linarith [hdm]
    rw [hquot]; field_simp
  -- The balance `n·Mw(n) − E = 1`.
  set E : ℝ := ∑ d ∈ Finset.Icc 1 n, (moebius d : ℝ) * ((n % d : ℕ) : ℝ) / (d : ℝ) with hEdef
  have hbal : (n : ℝ) * mwWeighted n - E = 1 := by
    rw [mwWeighted, Finset.mul_sum, hEdef, ← Finset.sum_sub_distrib, ← hfloorR]
    exact Finset.sum_congr rfl fun d hd => (hmod d hd).symm
  -- The error bound `|E| ≤ n − 1`.
  have hEbound : |E| ≤ (n : ℝ) - 1 := by
    rw [hEdef]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Finset.Icc 1 n,
        |(moebius d : ℝ) * ((n % d : ℕ) : ℝ) / (d : ℝ)| ≤ (if d = 1 then (0 : ℝ) else 1) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      by_cases h1 : d = 1
      · subst h1; simp [Nat.mod_one]
      · rw [if_neg h1]
        have hdpos : 0 < d := by omega
        have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
        have hμ : |(moebius d : ℝ)| ≤ 1 := by
          rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
        have hmodle : ((n % d : ℕ) : ℝ) / (d : ℝ) ≤ 1 := by
          rw [div_le_one hdR]
          exact_mod_cast le_of_lt (Nat.mod_lt n hdpos)
        have habs : |(moebius d : ℝ) * ((n % d : ℕ) : ℝ) / (d : ℝ)|
            = |(moebius d : ℝ)| * (((n % d : ℕ) : ℝ) / (d : ℝ)) := by
          rw [abs_div, abs_mul, Nat.abs_cast, Nat.abs_cast, mul_div_assoc]
        rw [habs]
        calc |(moebius d : ℝ)| * (((n % d : ℕ) : ℝ) / (d : ℝ))
            ≤ 1 * 1 := mul_le_mul hμ hmodle (by positivity) (by norm_num)
          _ = 1 := by norm_num
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    have hsplit : ∀ d, (if d = 1 then (0 : ℝ) else 1) = 1 - (if d = 1 then (1 : ℝ) else 0) := by
      intro d; by_cases h : d = 1 <;> simp [h]
    simp_rw [hsplit]
    rw [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_ite_eq' (Finset.Icc 1 n) 1 (fun _ => (1 : ℝ)),
      if_pos (Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩), Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, mul_one]
  -- Conclude `|Mw(n)| ≤ 1`.
  have key : |(n : ℝ) * mwWeighted n| ≤ (n : ℝ) := by
    have heq : (n : ℝ) * mwWeighted n = 1 + E := by linarith [hbal]
    rw [heq]
    refine (abs_add_le 1 E).trans ?_
    rw [abs_one]; linarith [hEbound]
  rw [abs_mul, abs_of_nonneg hn0.le] at key
  have : (n : ℝ) * |mwWeighted n| ≤ (n : ℝ) * 1 := by rw [mul_one]; exact key
  exact le_of_mul_le_mul_left this hn0

/-! ## Rung 1a — the discrete telescoping identity -/

/-- **Rung 1a — the discrete telescoping (Abel) identity.** For `z ≥ 1`,
`Σ_{d≤z} (μ(d)/d)·log(z/d) = Σ_{k=1}^{z-1} Mw(k)·(log(k+1) − log k)`, where
`Mw(k) = Σ_{d≤k} μ(d)/d`. Exact and PNT-free — the summation-by-parts seam the
`GrahamWeights` header named ("Abel against the corpus's Möbius-sum machinery"). Proved by
induction on `z`: both sides increase by `Mw(z)·(log(z+1) − log z)` at each step. -/
lemma sum_moebius_div_mul_log_eq (z : ℕ) (hz : 1 ≤ z) :
    ∑ d ∈ Finset.Icc 1 z, (moebius d : ℝ) / (d : ℝ) * Real.log ((z : ℝ) / (d : ℝ))
      = ∑ k ∈ Finset.Ico 1 z, mwWeighted k * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) := by
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ z hz ih =>
    have hz0 : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
    -- Peel the top term `d = z+1` off the LHS (its log is `log 1 = 0`).
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ z + 1)]
    have hzz : ((z + 1 : ℕ) : ℝ) / ((z + 1 : ℕ) : ℝ) = 1 :=
      div_self (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero z))
    -- Split each remaining summand: `log((z+1)/d) = log(z/d) + (log(z+1) − log z)`.
    have key : ∀ d ∈ Finset.Icc 1 z,
        (moebius d : ℝ) / (d : ℝ) * Real.log (((z + 1 : ℕ) : ℝ) / (d : ℝ))
          = (moebius d : ℝ) / (d : ℝ) * Real.log ((z : ℝ) / (d : ℝ))
            + (moebius d : ℝ) / (d : ℝ) * (Real.log ((z : ℝ) + 1) - Real.log (z : ℝ)) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hd0 : (d : ℝ) ≠ 0 := by positivity
      have hz1 : ((z : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      rw [Real.log_div hz1 hd0, Real.log_div (ne_of_gt hz0) hd0]
      ring
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, hzz, Real.log_one, mul_zero,
      add_zero, ih, ← Finset.sum_mul, Finset.sum_Ico_succ_top hz]
    rfl

/-! ## Rung 1c — the O(1) Barban–Vehov bound `|Σ_{d≤z} θ_d/d| ≤ 1`

Feeding `|Mw(k)| ≤ 1` (Rung 1b) through the telescoping identity (Rung 1a): the RHS sum is
`≤ Σ_{k<z}(log(k+1) − log k) = log z` (telescoping), and `θ_d/d = (μ(d)/d)·log(z/d)/log z`,
so dividing by `log z` gives the constant bound `≤ 1`. PNT-free, and a genuine improvement over
the crude `GrahamWeights` bound `|Σ_{d≤z} θ_d/d| ≤ 1 + log z`. -/

/-- **The log telescoping** `Σ_{k=1}^{z-1} (log(k+1) − log k) = log z`, for `z ≥ 1`. -/
lemma sum_Ico_log_succ_sub (z : ℕ) (hz : 1 ≤ z) :
    ∑ k ∈ Finset.Ico 1 z, (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) = Real.log (z : ℝ) := by
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ z hz ih => rw [Finset.sum_Ico_succ_top hz, ih]; push_cast; ring

/-- **Rung 1c — the O(1) Barban–Vehov cancellation.** For `z ≥ 2`,
`|Σ_{d≤z} θ_d/d| ≤ 1`. Improves the crude `abs_sum_grahamTheta_div_le` (`≤ 1 + log z`) to a
constant, via the discrete Abel identity and `|Mw| ≤ 1`. PNT-free. -/
lemma abs_sum_grahamTheta_div_le_one {z : ℕ} (hz : 2 ≤ z) :
    |∑ d ∈ Finset.Icc 1 z, grahamTheta z d / (d : ℝ)| ≤ 1 := by
  have hz1 : 1 ≤ z := by omega
  have hzR : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos hzR
  have hlogz' : Real.log (z : ℝ) ≠ 0 := ne_of_gt hlogz
  -- Rewrite the Graham sum via the Abel identity.
  have hrw : ∑ d ∈ Finset.Icc 1 z, grahamTheta z d / (d : ℝ)
      = (Real.log (z : ℝ))⁻¹
        * ∑ k ∈ Finset.Ico 1 z, mwWeighted k * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) := by
    rw [← sum_moebius_div_mul_log_eq z hz1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨hd1, hdz⟩ := Finset.mem_Icc.mp hd
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [grahamTheta_of_le hdz]
    field_simp
  rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.log (z : ℝ))⁻¹)]
  -- Bound the RHS sum by `log z` via `|Mw| ≤ 1` and telescoping.
  have hbound : |∑ k ∈ Finset.Ico 1 z,
      mwWeighted k * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ))| ≤ Real.log (z : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← sum_Ico_log_succ_sub z hz1]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkstep : 0 ≤ Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) := by
      have hle : Real.log (k : ℝ) ≤ Real.log ((k : ℝ) + 1) :=
        Real.log_le_log (by exact_mod_cast hk1) (by linarith)
      linarith
    rw [abs_mul, abs_of_nonneg hkstep]
    exact (mul_le_mul_of_nonneg_right (abs_mwWeighted_le_one hk1) hkstep).trans_eq (one_mul _)
  calc (Real.log (z : ℝ))⁻¹ * |∑ k ∈ Finset.Ico 1 z,
          mwWeighted k * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ))|
      ≤ (Real.log (z : ℝ))⁻¹ * Real.log (z : ℝ) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 1 := inv_mul_cancel₀ hlogz'

/-! ## Rung 2 — the shifted (mollified) detector and its finite Mellin identity

The zero-detecting shifted detector `D_ρ(x,N) = Σ_{n≤N} dhCoeff(n)·n^{−ρ}·(1−n/x)₊` — the
`ρ`-twist of `dhDetector` (Benli Prop 5.1). Its finite Mellin representation is
`dhDetector_mellin` with each coefficient carrying the extra `n^{−ρ}` factor; the vertical
integral of the finite Dirichlet polynomial `Σ_n dhCoeff(n)·n^{−ρ}·(x/n)^s` is `F(s+ρ)G(s+ρ)`
truncated (catch #61: staying FINITE sidesteps the integrability wall). This is the `Re s = c`
interface a finite-`N` shifted balance would consume; the pole at `s = 1−ρ` carries the
`x^{1−ρ}` damping and the `s = 0` term vanishes via `L(ρ,χ) = 0` (both gated behind the
non-convergent `J`, see the residual note). -/

/-- **The shifted (mollified) detector** `D_ρ(x,N) = Σ_{n≤N} dhCoeff(n)·n^{−ρ}·(1−n/x)₊`. The
`n^{−ρ}` twist makes it `ℂ`-valued; `ρ = 0` recovers `dhDetector` (cast to `ℂ`). -/
noncomputable def dhDetectorShift {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℕ) (x : ℝ)
    (N : ℕ) (ρ : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (dhCoeff χ z n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)

/-- **Rung 2 — the shifted finite Mellin representation.** For `x > 0` and any vertical line
`Re s = c > 0`, the shifted detector equals the single vertical integral of its finite
Dirichlet polynomial `Σ_{n≤N} dhCoeff(n)·n^{−ρ}·(x/n)^{c+ti}` against the smoothed-Perron
kernel `1/((c+ti)(c+ti+1))`. Exact, summability-free (finite `Σ↔∫` swap via `integrable_Fterm`
with the twisted coefficient). The `ρ = 0` case is `dhDetector_mellin`. -/
theorem dhDetectorShift_mellin {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℕ) {x : ℝ}
    (hx : 0 < x) {c : ℝ} (hc : 0 < c) (N : ℕ) (ρ : ℂ) :
    dhDetectorShift χ z x N ρ
      = (1 / (2 * Real.pi)) • ∫ t : ℝ,
          (∑ n ∈ Finset.Icc 1 N, (dhCoeff χ z n : ℂ) * (n : ℂ) ^ (-ρ) *
              ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) /
            (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
  -- Step 1: the shifted detector as a finite sum of per-term kernel integrals.
  have hstep : dhDetectorShift χ z x N ρ
      = ∑ n ∈ Finset.Icc 1 N, (1 / (2 * Real.pi)) • ∫ t : ℝ,
          ((dhCoeff χ z n : ℂ) * (n : ℂ) ^ (-ρ)) *
              ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
            (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
    rw [dhDetectorShift]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [dhKernR_eq_kernel_integral hx hc hn1, mul_smul_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only; ring
  rw [hstep, ← Finset.smul_sum]
  congr 1
  refine (integral_finsetSum (Finset.Icc 1 N)
    (fun n _ => integrable_Fterm ((dhCoeff χ z n : ℂ) * (n : ℂ) ^ (-ρ))
      (div_nonneg hx.le (Nat.cast_nonneg n)) hc)).symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [Finset.sum_div]

/-! ## The resume map (DH-MAIN → next; PROSE, not `sorry`)

LANDED here (all sorry-free, axioms `⊆ [propext, Classical.choice, Quot.sound]`):
* `sum_moebius_mul_div_eq_one` — the Möbius floor identity `Σ_{d≤n} μ(d)⌊n/d⌋ = 1`.
* `sum_moebius_div_mul_log_eq` (Rung 1a) — the discrete Abel identity
  `Σ_{d≤z}(μ(d)/d)log(z/d) = Σ_{k<z} Mw(k)(log(k+1)−log k)`.
* `abs_mwWeighted_le_one` (Rung 1b) — the uniform bound `|Σ_{d≤n} μ(d)/d| ≤ 1` (a genuine
  Möbius stone not previously in the corpus).
* `abs_sum_grahamTheta_div_le_one` (Rung 1c) — the **O(1) Barban–Vehov cancellation**
  `|Σ_{d≤z} θ_d/d| ≤ 1`, improving the crude `abs_sum_grahamTheta_div_le` (`≤ 1 + log z`).
* `dhDetectorShift` / `dhDetectorShift_mellin` (Rung 2) — the `ρ`-twisted detector and its
  exact finite Mellin representation (the `Re s = c` interface for a shifted balance).

### Residual A — the SHARP Barban–Vehov cancellation `|Σ_{d≤z} θ_d/d| ≤ C/log z`

The O(1) form (Rung 1c) is landed and PNT-free. The SHARP `≍ 1/log z` gain (the
`GrahamWeights` residual (2), what the mollifier ultimately needs to cancel the `Σ χ_ℝ(n)/n`
error) requires DECAY of `Mw(z) = Σ_{d≤z} μ(d)/d`, namely `|Mw(z)| ≤ C/log z`. Via the Abel
identity, `Σ_{d≤z} θ_d/d = Mw(z) − (1/log z)·Σ_{d≤z}(μ(d)/d)log d`, so the sharp bound needs
BOTH `|Mw(z)| ≤ C/log z` and `|Σ_{d≤z}(μ(d)/d)log d| ≤ C`. Each is a PNT-strength Möbius
partial-sum estimate. THE OBSTRUCTION: the corpus supplies only the UNWEIGHTED rate
`mmuRate_holds` (`|Σ_{n≤y} μ(n)| ≤ C·y/(log y)^A`); a forward Abel summation against it yields
only the O(1) bound (already landed) — the decay requires the tail cancellation
`Σ_{d=1}^∞ μ(d)/d = 0` (equivalently `1/ζ(1) = 0`), a genuine PNT-corollary NOT yet in the
corpus. Building `tsum_moebius_div_eq_zero` (from `mmuRate_holds` + the analytic value at the
`ζ`-pole) is the precise next stone; it is multi-session-hard and was scoped OUT here.

### Residual B — the shifted balance (Rung 3) and composition (Rung 4)

`dhDetectorShift_mellin` (landed) is the `Re s = c` finite Mellin of the shifted detector. The
contour shift to `Re s = 1/2 − β` collects (i) the pole at `s = 1 − ρ` (residue via the LANDED
`rectBI_zeta_shift_mul`, carrying the `x^{1−ρ}` damping); (ii) the `s = 0` term, which VANISHES
by `L(ρ,χ) = 0`; (iii) the shifted-line integral `J`. THE OBSTRUCTION (inherited, documented in
`DHBalance`'s `norm_dhIntegrand_le` note): `J` as an integral over `ℝ` does NOT converge — the
corpus `ζ`/`L` growth bounds are each `O(|t|)`, product `O(|t|²)`, and the kernel decay only
`O(|t|⁻²)`, leaving an `O(1)` non-integrable integrand. The honest route is the finite-`N`
truncation (staying FINITE, catch #61), mirroring `DHClose.LFunction_one_re_ge_partial` in the
SHIFTED frame: bound `‖D_ρ − residue‖` via `norm_LFunction_sub_partial_le_strip` at the single
frame, optimizing `N ≍ x`. This yields `Λ ≍ x^{−b(1−ρ.re)}/polylog ≤ (L(1,χ)).re`; then
`dh_repulsion_of_LFunction_one_lower` (M4, LANDED) inverts to the `dh_repulsion` target with
`x = (q(|ρ.im|+2))^{b'}`. Rung 3 is the genuine multi-session crux.

### Honesty (HB-ENGINE, R4 — NO twin claim)

NOT a proof of the Twin Prime Conjecture. Delivers competing-estimate substrate for the
conditional `InfinitelyManySiegelZeros → TwinPrimeConjecture`; the death rung is R4. -/

end Salt.SW

end
