/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.DerivTest

/-!
# van der Corput's `k`-th derivative test (the uniform induction)

This file generalises `vdC_third_derivative` (`Salt/ExpSum/DerivTest.lean`, the
`k = 3` case) to **arbitrary `k ≥ 2`** by iterating the Weyl–van der Corput
A-process.  The main result is `vdC_kth_derivative`:

For every `k ≥ 2` there is a constant `C ≥ 1` such that for any phase
`f : ℤ → ℝ` whose `k`-th forward differences `Δᵏf` obey `λ ≤ Δᵏf ≤ cλ` on the
range (`0 < λ`, `1 ≤ c`),
`‖∑ eR (f n)‖ ≤ C·c^{2^{2−k}}·(N·λ^{α_k} + N^{β_k}·λ^{−α_k})`,
with the classical Graham–Kolesnik exponents
`α_k = 1/(2^k−2)`, `β_k = 1 − 2^{2−k}` and `c`-grade `2^{2−k}`.

## The `∃ C`-per-`k` shape

The constant is threaded through the induction as an existential (`C = C(k)`,
here `C(k+1) = 4√C(k)`, so `C(2)=8`, `C(3)=8√2`, …).  This is strictly easier
than a uniform closed form and is exactly what the ζ-growth consumer needs
(`k` is log-grade).  The exponents are `Real.rpow` powers of the real number
`(2:ℝ)^k`.

## The difference operator `dk`

`Δᵏ` is a *recursive* forward-difference operator `dk k f`, mirroring the
landed `D2f` pattern (rather than mathlib's `fwdDiff`) so that it composes
directly with the base test's explicit second-difference form and with the
shift/linearity manipulations of the A-process step.

## Exponent bookkeeping

All exponent arithmetic is carried in an **opaque real** `p := (2:ℝ)^K`
(with `4 ≤ p`), so `ring`/`nlinarith` never see `2^K` symbolically.  The key
identities `α = 2α'(1+α)`, `1+β = 2β'`, `2·grade' = grade` are `field_simp`
facts in `p`.
-/

namespace Salt.ExpSum

open Real Finset
open scoped ComplexConjugate

/-! ## Section 0 — the recursive forward-difference operator `dk` -/

/-- The `k`-th forward difference: `dk 0 f = f`,
`dk (k+1) f m = dk k f (m+1) − dk k f m`.  So `dk 1 f m = f(m+1) − f m`,
`dk 2 f m = (f(m+2)−f(m+1)) − (f(m+1)−f m)`, etc. -/
def dk : ℕ → (ℤ → ℝ) → ℤ → ℝ
  | 0, f => f
  | (n + 1), f => fun m => dk n f (m + 1) - dk n f m

@[simp] lemma dk_zero (f : ℤ → ℝ) (m : ℤ) : dk 0 f m = f m := rfl

@[simp] lemma dk_succ (n : ℕ) (f : ℤ → ℝ) (m : ℤ) :
    dk (n + 1) f m = dk n f (m + 1) - dk n f m := rfl

/-- `dk 2` in the explicit form the second-derivative base test consumes. -/
lemma dk_two (f : ℤ → ℝ) (m : ℤ) :
    dk 2 f m = (f (m + 2) - f (m + 1)) - (f (m + 1) - f m) := by
  simp only [show (2 : ℕ) = 1 + 1 from rfl, dk_succ, dk_zero]
  rw [show m + 1 + 1 = m + 2 from by ring]

/-- `dk` commutes with a shift: `dk n (f(·+h)) = (dk n f)(·+h)`. -/
lemma dk_shift (f : ℤ → ℝ) (h : ℤ) (n : ℕ) :
    ∀ m : ℤ, dk n (fun x => f (x + h)) m = dk n f (m + h) := by
  induction n with
  | zero => intro m; rfl
  | succ n ih =>
      intro m
      rw [dk_succ, dk_succ, ih (m + 1), ih m, show m + 1 + h = m + h + 1 from by ring]

/-- `dk` is additive on differences: `dk n (g − f) = dk n g − dk n f`. -/
lemma dk_sub (g f : ℤ → ℝ) (n : ℕ) :
    ∀ m : ℤ, dk n (fun x => g x - f x) m = dk n g m - dk n f m := by
  induction n with
  | zero => intro m; rfl
  | succ n ih =>
      intro m
      rw [dk_succ, dk_succ, dk_succ, ih (m + 1), ih m]; ring

/-- The connection used by the A-process step: the `n`-th difference of the
shifted phase `g_h(x) = f(x+h) − f x` is `Δⁿf(·+h) − Δⁿf`. -/
lemma dk_diff_shift (f : ℤ → ℝ) (h : ℤ) (n : ℕ) (m : ℤ) :
    dk n (fun x => f (x + h) - f x) m = dk n f (m + h) - dk n f m := by
  rw [dk_sub (fun x => f (x + h)) f n m, dk_shift f h n m]

/-! ## Section 1 — general power sums

The two `∑_{h≤H} h^{±α}` bounds that the k=3 file did concretely (`sum_sqrt_range`,
`sum_inv_sqrt_range` for `α = 1/2`).  The up-sum is a crude termwise bound; the
down-sum is the sharp integral-comparison `∑ h^{−α} ≤ H^{1−α}/(1−α)`, proved by a
weighted-AM–GM telescope. -/

/-- Up-sum (crude): `∑_{i<H} (i+1)^α ≤ H·H^α`. -/
lemma sum_rpow_pos_le (α : ℝ) (hα : 0 ≤ α) (H : ℕ) :
    ∑ i ∈ Finset.range H, ((i : ℝ) + 1) ^ α ≤ (H : ℝ) * (H : ℝ) ^ α := by
  calc ∑ i ∈ Finset.range H, ((i : ℝ) + 1) ^ α
      ≤ ∑ _i ∈ Finset.range H, (H : ℝ) ^ α := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        exact Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast Nat.succ_le_of_lt hi) hα
    _ = (H : ℝ) * (H : ℝ) ^ α := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The per-term telescope inequality behind the down-sum, from weighted AM–GM:
`(j+1)^{−α} ≤ ((j+1)^{1−α} − j^{1−α})/(1−α)`. -/
lemma rpow_neg_telescope (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (j : ℕ) :
    ((j : ℝ) + 1) ^ (-α) ≤ (((j : ℝ) + 1) ^ (1 - α) - (j : ℝ) ^ (1 - α)) / (1 - α) := by
  set x : ℝ := (j : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1pos : 0 < x + 1 := by positivity
  have h1a : 0 < 1 - α := by linarith
  set A := (x + 1) ^ (-α) with hA
  set B := (x + 1) ^ α with hB
  have hApos : 0 < A := Real.rpow_pos_of_pos hx1pos _
  have hBpos : 0 < B := Real.rpow_pos_of_pos hx1pos _
  -- `A·B = 1` and `(x+1)^{1-α} = A·(x+1)`
  have hAB : A * B = 1 := by
    rw [hA, hB, ← Real.rpow_add hx1pos]; norm_num
  have hC : (x + 1) ^ (1 - α) = A * (x + 1) := by
    rw [hA, show (1 : ℝ) - α = -α + 1 from by ring, Real.rpow_add hx1pos, Real.rpow_one]
  -- weighted AM–GM:  x^{1-α}·(x+1)^α ≤ x + α
  have hAM : x ^ (1 - α) * B ≤ x + α := by
    have hg := Real.geom_mean_le_arith_mean2_weighted (le_of_lt h1a) (le_of_lt hα0)
      hx0 (le_of_lt hx1pos) (by ring : (1 - α) + α = 1)
    calc x ^ (1 - α) * B = x ^ (1 - α) * (x + 1) ^ α := by rw [hB]
      _ ≤ (1 - α) * x + α * (x + 1) := hg
      _ = x + α := by ring
  -- hence x^{1-α} ≤ A·(x+α)
  have hD : x ^ (1 - α) ≤ A * (x + α) := by
    have h := mul_le_mul_of_nonneg_left hAM (le_of_lt hApos)
    calc x ^ (1 - α) = A * B * x ^ (1 - α) := by rw [hAB]; ring
      _ = A * (x ^ (1 - α) * B) := by ring
      _ ≤ A * (x + α) := mul_le_mul_of_nonneg_left hAM (le_of_lt hApos)
  rw [le_div_iff₀ h1a, hC]; nlinarith [hD, hApos]

/-- Down-sum (sharp): `∑_{i<H} (i+1)^{−α} ≤ H^{1−α}/(1−α)` for `0 < α < 1`. -/
lemma sum_rpow_neg_le (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (H : ℕ) :
    ∑ i ∈ Finset.range H, ((i : ℝ) + 1) ^ (-α) ≤ (H : ℝ) ^ (1 - α) / (1 - α) := by
  have h1a : (0 : ℝ) < 1 - α := by linarith
  induction H with
  | zero => simp [Real.zero_rpow (by linarith : (1 : ℝ) - α ≠ 0)]
  | succ H ih =>
      rw [Finset.sum_range_succ]
      have hstep := rpow_neg_telescope α hα0 hα1 H
      have hcast : ((H : ℝ) + 1) = ((H + 1 : ℕ) : ℝ) := by push_cast; ring
      calc ∑ i ∈ Finset.range H, ((i : ℝ) + 1) ^ (-α) + ((H : ℝ) + 1) ^ (-α)
          ≤ (H : ℝ) ^ (1 - α) / (1 - α)
              + (((H : ℝ) + 1) ^ (1 - α) - (H : ℝ) ^ (1 - α)) / (1 - α) :=
            add_le_add ih hstep
        _ = ((H : ℝ) + 1) ^ (1 - α) / (1 - α) := by rw [← add_div]; congr 1; ring
        _ = ((H + 1 : ℕ) : ℝ) ^ (1 - α) / (1 - α) := by rw [hcast]

/-! ## Section 2 — the abstract H-optimization

After the A-process + power sums, the squared sum is bounded by three terms in
the clamp variable `q = λ^{2α'}·H ∈ [1/2, 1]`, with `s = q^{α}` (`≤ 1`) and
`sinv = q^{−α}` (`≤ 2`).  This lemma collapses them to `16·C'·cᵍ·(A²+B²)`.  It
is pure arithmetic on opaque reals — `A, B, q, C', cg, s, sinv, α` — so `2^K`
never appears. -/

lemma opt_core_gen (A2 B2 q Cp cg s sinv α : ℝ)
    (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2) (hq2 : 1 / 2 ≤ q)
    (hCp : 1 ≤ Cp) (hcg : 1 ≤ cg) (hs1 : s ≤ 1) (hsinv2 : sinv ≤ 2) (hα12 : α ≤ 1 / 2) :
    2 * A2 / q + 4 * Cp * cg * A2 * s + 4 * Cp * cg / (1 - α) * B2 * sinv
      ≤ 16 * Cp * cg * (A2 + B2) := by
  have hqpos : 0 < q := by linarith
  have h1a : 0 < 1 - α := by linarith
  have hCp0 : 0 ≤ Cp := by linarith
  have hcg0 : 0 ≤ cg := by linarith
  have hCpcg1 : (1 : ℝ) ≤ Cp * cg := by nlinarith [hCp, hcg]
  have hcoefA : 0 ≤ 4 * Cp * cg * A2 := by positivity
  have hCcgB : 0 ≤ Cp * cg * B2 := by positivity
  -- term 1:  2·A²/q ≤ 4·A²   (q ≥ 1/2)
  have hb1 : 2 * A2 / q ≤ 4 * A2 := by
    rw [div_le_iff₀ hqpos]; nlinarith [mul_nonneg hA2 (by linarith : (0 : ℝ) ≤ q - 1 / 2)]
  -- term 2:  4·C'·cg·A²·s ≤ 4·C'·cg·A²   (s ≤ 1)
  have hb2 : 4 * Cp * cg * A2 * s ≤ 4 * Cp * cg * A2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs1 hcoefA]
  -- term 3:  (4·C'·cg/(1-α))·B²·sinv ≤ 16·C'·cg·B²   (1/(1-α) ≤ 2, sinv ≤ 2)
  have hb3 : 4 * Cp * cg / (1 - α) * B2 * sinv ≤ 16 * Cp * cg * B2 := by
    have hrw : 4 * Cp * cg / (1 - α) * B2 * sinv
        = 4 * Cp * cg * B2 * sinv / (1 - α) := by ring
    rw [hrw, div_le_iff₀ h1a]
    have hscalar : 4 * sinv ≤ 16 * (1 - α) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hscalar hCcgB]
  -- combine:  4A² + 4C'cgA² ≤ 16C'cgA²   (C'cg ≥ 1)
  nlinarith [hb1, hb2, hb3, mul_nonneg hA2 (sub_nonneg.mpr hCpcg1)]

/-- `4 ≤ 2ᴷ` for `K ≥ 2` (used for `α_K > 0`, `β_K ≥ 0`, denominators nonzero). -/
lemma four_le_two_pow (K : ℕ) (hK : 2 ≤ K) : (4 : ℝ) ≤ (2 : ℝ) ^ K := by
  have h : (2 : ℕ) ^ 2 ≤ (2 : ℕ) ^ K := Nat.pow_le_pow_right (by norm_num) hK
  calc (4 : ℝ) = ((2 ^ 2 : ℕ) : ℝ) := by norm_num
    _ ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast h
    _ = (2 : ℝ) ^ K := by push_cast; ring

/-! ## Section 3 — the uniform induction

The conclusion predicate, carried through the induction with an existential
constant.  Integer endpoints `a ≤ b` (matching `vdC_2nd_ZR`) make the base case
and the A-process sub-window applications direct. -/

/-- `IsVdCBound k C`: the `k`-th derivative test holds with constant `C`.  For
any phase whose `k`-th differences `dk k f` lie in `[λ, cλ]` on `(a, b)`,
`‖∑ eR (f n)‖ ≤ C·c^{2^{2−k}}·((b−a)·λ^{α_k} + (b−a)^{β_k}·λ^{−α_k})`, with
`α_k = 1/(2^k−2)`, `β_k = 1 − 2^{2−k} = 1 − 4/2^k`, `c`-grade `2^{2−k} = 4/2^k`. -/
def IsVdCBound (k : ℕ) (C : ℝ) : Prop :=
  ∀ (f : ℤ → ℝ) (a b : ℤ) (lam c : ℝ), a ≤ b → 0 < lam → 1 ≤ c →
    (∀ n : ℤ, a < n → n < b → lam ≤ dk k f n) →
    (∀ n : ℤ, a < n → n < b → dk k f n ≤ c * lam) →
    ‖∑ n ∈ Finset.Ioc a b, eR (f n)‖
      ≤ C * c ^ (4 / (2 : ℝ) ^ k)
        * (((b : ℝ) - a) * lam ^ (1 / ((2 : ℝ) ^ k - 2))
          + ((b : ℝ) - a) ^ (1 - 4 / (2 : ℝ) ^ k) * lam ^ (-(1 / ((2 : ℝ) ^ k - 2))))

/-- **Base case `k = 2`.**  The second-derivative test `vdC_2nd_ZR` with `C = 8`
(the extra `c ≥ 1` slack absorbs the base test's `1/√λ` into `c/√λ`). -/
lemma isVdCBound_two : IsVdCBound 2 8 := by
  intro f a b lam c hab hlam hc hlb hub
  have hlb' : ∀ n : ℤ, a < n → n < b → lam ≤ (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) := by
    intro n h1 h2; rw [← dk_two]; exact hlb n h1 h2
  have hub' : ∀ n : ℤ, a < n → n < b → (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ≤ c * lam := by
    intro n h1 h2; rw [← dk_two]; exact hub n h1 h2
  have hbase := vdC_2nd_ZR f a b lam c hab hlam hc hlb' hub'
  refine le_trans hbase ?_
  have hL : 0 ≤ (b : ℝ) - a := by
    have h : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hval_c : c ^ (4 / (2 : ℝ) ^ 2) = c := by
    rw [show (4 : ℝ) / (2 : ℝ) ^ 2 = 1 from by norm_num, Real.rpow_one]
  have hval_a : lam ^ (1 / ((2 : ℝ) ^ 2 - 2)) = Real.sqrt lam := by
    rw [show (1 : ℝ) / ((2 : ℝ) ^ 2 - 2) = 1 / (2 : ℝ) from by norm_num, ← Real.sqrt_eq_rpow]
  have hval_b : ((b : ℝ) - a) ^ (1 - 4 / (2 : ℝ) ^ 2) = 1 := by
    rw [show (1 : ℝ) - 4 / (2 : ℝ) ^ 2 = 0 from by norm_num, Real.rpow_zero]
  have hval_na : lam ^ (-(1 / ((2 : ℝ) ^ 2 - 2))) = 1 / Real.sqrt lam := by
    rw [Real.rpow_neg (le_of_lt hlam), hval_a, inv_eq_one_div]
  rw [hval_c, hval_a, hval_b, hval_na]
  have hsq : 0 ≤ 1 / Real.sqrt lam := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hsq,
    mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c) hL) (Real.sqrt_nonneg lam)]

/-- **Per-shift bound (induction step).**  Given the level-`K` bound `hih` and
level-`(K+1)` differences of `f` in `[λ, cλ]`, the positive-shift differenced
sum is bounded by `hih` applied to `g_h(x) = f(x+h) − f x`, whose level-`K`
differences lie in `[hλ, c·hλ]` (accumulation of `dk (K+1) f`). -/
lemma Gh_bound_gen (K : ℕ) (Cp : ℝ) (hCp : 1 ≤ Cp) (hih : IsVdCBound K Cp)
    (f : ℤ → ℝ) (a : ℤ) (N : ℕ) (lam c : ℝ) (hlam : 0 < lam) (hc : 1 ≤ c)
    (hβ : 0 ≤ 1 - 4 / (2 : ℝ) ^ K)
    (hk1_lb : ∀ n : ℤ, a < n → n < a + N → lam ≤ dk (K + 1) f n)
    (hk1_ub : ∀ n : ℤ, a < n → n < a + N → dk (K + 1) f n ≤ c * lam)
    (h : ℤ) (hh1 : 1 ≤ h) (hhN : h ≤ (N : ℤ)) :
    ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter (fun n => n + h ∈ Finset.Ioc a (a + (N : ℤ))),
        eR (f (n + h) - f n)‖
      ≤ Cp * c ^ (4 / (2 : ℝ) ^ K)
        * ((N : ℝ) * ((h : ℝ) * lam) ^ (1 / ((2 : ℝ) ^ K - 2))
          + (N : ℝ) ^ (1 - 4 / (2 : ℝ) ^ K) * ((h : ℝ) * lam) ^ (-(1 / ((2 : ℝ) ^ K - 2)))) := by
  have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < h)
  have hmu : 0 < (h : ℝ) * lam := mul_pos hhpos hlam
  have hc0 : (0 : ℝ) ≤ c := by linarith
  set k₀ : ℕ := h.toNat with hk0
  have hk0Z : (k₀ : ℤ) = h := Int.toNat_of_nonneg (by omega)
  have hk0R : (k₀ : ℝ) = (h : ℝ) := by exact_mod_cast hk0Z
  have hfilter : (Finset.Ioc a (a + (N : ℤ))).filter (fun n => n + h ∈ Finset.Ioc a (a + (N : ℤ)))
      = Finset.Ioc a (a + (N : ℤ) - h) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_Ioc]; omega
  rw [hfilter]
  -- accumulation steps: increments of `dk K f` are `dk (K+1) f`
  have hstepU : ∀ m, a + 1 ≤ m → m < a + (N : ℤ) → dk K f (m + 1) - dk K f m ≤ c * lam := by
    intro m hm1 hm2; rw [← dk_succ]; exact hk1_ub m (by omega) hm2
  have hstepL : ∀ m, a + 1 ≤ m → m < a + (N : ℤ) →
      (fun x => -(dk K f x)) (m + 1) - (fun x => -(dk K f x)) m ≤ -lam := by
    intro m hm1 hm2; simp only
    rw [show -(dk K f (m + 1)) - -(dk K f m) = -(dk K f (m + 1) - dk K f m) from by ring, ← dk_succ]
    linarith [hk1_lb m (by omega) hm2]
  -- level-`K` differences of `g_h` on the sub-window
  have hlbφ : ∀ n : ℤ, a < n → n < a + (N : ℤ) - h →
      (h : ℝ) * lam ≤ dk K (fun x => f (x + h) - f x) n := by
    intro n hn1 hn2
    rw [dk_diff_shift f h K n]
    have hacc : -(dk K f (n + (k₀ : ℤ))) - -(dk K f n) ≤ (k₀ : ℝ) * (-lam) :=
      diff2_accum (fun x => -(dk K f x)) hstepL n (by omega) k₀ (by rw [hk0Z]; omega)
    rw [hk0Z, hk0R] at hacc; linarith
  have hubφ : ∀ n : ℤ, a < n → n < a + (N : ℤ) - h →
      dk K (fun x => f (x + h) - f x) n ≤ c * ((h : ℝ) * lam) := by
    intro n hn1 hn2
    rw [dk_diff_shift f h K n]
    have hacc := diff2_accum (dk K f) hstepU n (by omega) k₀ (by rw [hk0Z]; omega)
    rw [hk0Z, hk0R] at hacc; nlinarith [hacc]
  -- apply the induction hypothesis to `g_h`
  have hbase := hih (fun x => f (x + h) - f x) a (a + (N : ℤ) - h) ((h : ℝ) * lam) c
    (by omega) hmu hc hlbφ hubφ
  refine le_trans hbase ?_
  have hLen : (((a + (N : ℤ) - h : ℤ)) : ℝ) - (a : ℝ) = (N : ℝ) - (h : ℝ) := by push_cast; ring
  rw [hLen]
  have hNle : (h : ℝ) ≤ (N : ℝ) := by exact_mod_cast hhN
  have hNmh_nn : (0 : ℝ) ≤ (N : ℝ) - (h : ℝ) := by linarith
  have hNmh_le : (N : ℝ) - (h : ℝ) ≤ (N : ℝ) := by linarith [hhpos]
  have hCpg_nn : (0 : ℝ) ≤ Cp * c ^ (4 / (2 : ℝ) ^ K) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hc0 _)
  apply mul_le_mul_of_nonneg_left _ hCpg_nn
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right hNmh_le (Real.rpow_nonneg (le_of_lt hmu) _)
  · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hNmh_nn hNmh_le hβ)
      (Real.rpow_nonneg (le_of_lt hmu) _)

set_option maxHeartbeats 1600000 in
-- The A-process core assembles ~10 rpow atoms through `field_simp`/`ring`; the
-- large but bounded normal-form needs a raised heartbeat budget.
/-- **The induction step, main regime.**  With a shift parameter `H` chosen so
that `H ≤ λ^{−1/(2ᴷ−1)} < H+1` (i.e. `H = ⌊λ^{−2α'}⌋₊`, `1 ≤ H ≤ N`), the
A-process + the level-`K` bound give the level-`(K+1)` target with constant
`4√Cp`.  The clamp `q = λ^{2α'}·H ∈ [1/2, 1]`. -/
lemma vdC_kth_main (K : ℕ) (hK : 2 ≤ K) (Cp : ℝ) (hCp : 1 ≤ Cp) (hih : IsVdCBound K Cp)
    (f : ℤ → ℝ) (a : ℤ) (N : ℕ) (lam c : ℝ) (hlam : 0 < lam) (hc : 1 ≤ c)
    (hlb : ∀ n : ℤ, a < n → n < a + N → lam ≤ dk (K + 1) f n)
    (hub : ∀ n : ℤ, a < n → n < a + N → dk (K + 1) f n ≤ c * lam)
    (H : ℕ) (hH1 : 1 ≤ H) (hHN : H ≤ N)
    (hHlo : (H : ℝ) ≤ lam ^ (-(1 / ((2 : ℝ) ^ K - 1))))
    (hHhi : lam ^ (-(1 / ((2 : ℝ) ^ K - 1))) < (H : ℝ) + 1) :
    ‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖
      ≤ 4 * Real.sqrt Cp * c ^ (4 / (2 : ℝ) ^ (K + 1))
        * ((N : ℝ) * lam ^ (1 / ((2 : ℝ) ^ (K + 1) - 2))
          + (N : ℝ) ^ (1 - 4 / (2 : ℝ) ^ (K + 1))
              * lam ^ (-(1 / ((2 : ℝ) ^ (K + 1) - 2)))) := by
  classical
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hHRpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH1
  have hHR1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hc0 : (0 : ℝ) ≤ c := by linarith
  -- opaque `p = 2ᴷ` and the exponent zoo
  set p : ℝ := (2 : ℝ) ^ K with hp
  have hp4 : (4 : ℝ) ≤ p := four_le_two_pow K hK
  have hpK1 : (2 : ℝ) ^ (K + 1) = 2 * p := by rw [hp, pow_succ]; ring
  rw [hpK1]
  set α' : ℝ := 1 / (2 * p - 2) with hα'
  set β' : ℝ := 1 - 4 / (2 * p) with hβ'
  set g' : ℝ := 4 / (2 * p) with hg'
  set αK : ℝ := 1 / (p - 2) with hαK
  set A2exp : ℝ := 2 * α' with hA2exp
  set B2Nexp : ℝ := 2 * β' with hB2N
  set cg : ℝ := c ^ (4 / p) with hcg
  set AA : ℝ := (N : ℝ) ^ 2 * lam ^ A2exp with hAA
  set BB : ℝ := (N : ℝ) ^ B2Nexp * lam ^ (-A2exp) with hBB
  -- positivity / nonvanishing
  have hlamA : (0 : ℝ) < lam ^ A2exp := Real.rpow_pos_of_pos hlam _
  have hcg1 : (1 : ℝ) ≤ cg := Real.one_le_rpow hc (by positivity)
  have hcg0 : (0 : ℝ) ≤ cg := by linarith
  have hAA0 : (0 : ℝ) ≤ AA := by rw [hAA]; positivity
  have hBB0 : (0 : ℝ) ≤ BB := by rw [hBB]; positivity
  -- √ of the atoms
  have hsqrtAA : Real.sqrt AA = (N : ℝ) * lam ^ α' := by
    rw [hAA, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hN, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (le_of_lt hlam), show A2exp * (1 / 2 : ℝ) = α' from by rw [hA2exp]; ring]
  have hsqrtBB : Real.sqrt BB = (N : ℝ) ^ β' * lam ^ (-α') := by
    rw [hBB, Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hN, ← Real.rpow_mul (le_of_lt hlam),
      show B2Nexp * (1 / 2 : ℝ) = β' from by rw [hB2N]; ring,
      show -A2exp * (1 / 2 : ℝ) = -α' from by rw [hA2exp]; ring]
  have hsqrtcg : Real.sqrt cg = c ^ g' := by
    rw [hcg, Real.sqrt_eq_rpow, ← Real.rpow_mul hc0,
      show (4 / p) * (1 / 2 : ℝ) = g' from by rw [hg']; ring]
  -- ══ exponent facts, clamp, and the rpow bridges (independent of the A-process) ══
  have hp2 : (2 : ℝ) < p := by linarith
  have hp3 : (3 : ℝ) < p := by linarith
  have hpne0 : p ≠ 0 := by linarith
  have hpne1 : p - 1 ≠ 0 := by linarith
  have hpne2 : p - 2 ≠ 0 := by linarith
  have h2pne2 : 2 * p - 2 ≠ 0 := by linarith
  have hCp0 : (0 : ℝ) ≤ Cp := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans hH1 hHN); exact_mod_cast this
  have hHne : (H : ℝ) ≠ 0 := ne_of_gt hHRpos
  have hαKpos : 0 < αK := by rw [hαK]; positivity
  have hαKlt1 : αK < 1 := by rw [hαK, div_lt_one (by linarith)]; linarith
  have hαKle : αK ≤ 1 / 2 := by rw [hαK]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h1aKne : (1 : ℝ) - αK ≠ 0 := by
    have : αK < 1 := hαKlt1; linarith
  have hβKnn : (0 : ℝ) ≤ 1 - 4 / p := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  -- lam-power positivity and inverses
  have hlamAne : lam ^ A2exp ≠ 0 := ne_of_gt hlamA
  have hlamnA : (0 : ℝ) < lam ^ (-A2exp) := Real.rpow_pos_of_pos hlam _
  have hlamnAne : lam ^ (-A2exp) ≠ 0 := ne_of_gt hlamnA
  have hAinv : lam ^ A2exp * lam ^ (-A2exp) = 1 := by
    rw [← Real.rpow_add hlam]; simp
  -- exponent identities (in the opaque real `p`)
  have hI1add : A2exp + A2exp * αK = αK := by rw [hA2exp, hα', hαK]; field_simp; ring
  have hI1sub : -A2exp + A2exp * (-αK) = -αK := by rw [hA2exp, hα', hαK]; field_simp; ring
  have hI2add : (1 : ℝ) + (1 - 4 / p) = B2Nexp := by rw [hB2N, hβ']; ring
  have hA2exp_eq : A2exp = 1 / (p - 1) := by
    rw [hA2exp, hα', mul_one_div, div_eq_div_iff h2pne2 hpne1]; ring
  -- clamp `q = λ^{2α'}·H ∈ [1/2, 1]`
  set q : ℝ := lam ^ A2exp * (H : ℝ) with hq
  have hHlo' : (H : ℝ) ≤ lam ^ (-A2exp) := by rw [hA2exp_eq]; exact hHlo
  have hHhi' : lam ^ (-A2exp) < (H : ℝ) + 1 := by rw [hA2exp_eq]; exact hHhi
  have hqle1 : q ≤ 1 := by
    calc q = lam ^ A2exp * (H : ℝ) := hq
      _ ≤ lam ^ A2exp * lam ^ (-A2exp) := mul_le_mul_of_nonneg_left hHlo' (le_of_lt hlamA)
      _ = 1 := hAinv
  have hqge : (1 : ℝ) / 2 ≤ q := by
    have h2H : lam ^ (-A2exp) < 2 * (H : ℝ) := by linarith
    have hkey : (1 : ℝ) < 2 * q := by
      rw [hq]
      calc (1 : ℝ) = lam ^ A2exp * lam ^ (-A2exp) := hAinv.symm
        _ < lam ^ A2exp * (2 * (H : ℝ)) := mul_lt_mul_of_pos_left h2H hlamA
        _ = 2 * (lam ^ A2exp * (H : ℝ)) := by ring
    linarith
  have hqpos : (0 : ℝ) < q := by linarith
  -- the rpow bridges R1, R2, R3, hNpow, and their `q`-forms
  have R1 : lam ^ αK * (H : ℝ) ^ αK = lam ^ A2exp * q ^ αK := by
    rw [hq, Real.mul_rpow (le_of_lt hlamA) (le_of_lt hHRpos), ← Real.rpow_mul (le_of_lt hlam),
      ← mul_assoc, ← Real.rpow_add hlam, hI1add]
  have R2 : lam ^ (-αK) * (H : ℝ) ^ (-αK) = lam ^ (-A2exp) * q ^ (-αK) := by
    rw [hq, Real.mul_rpow (le_of_lt hlamA) (le_of_lt hHRpos), ← Real.rpow_mul (le_of_lt hlam),
      ← mul_assoc, ← Real.rpow_add hlam, hI1sub]
  have hqK : q ^ αK = lam ^ αK * (H : ℝ) ^ αK / lam ^ A2exp := by
    rw [eq_div_iff hlamAne, R1]; ring
  have hqnK : q ^ (-αK) = lam ^ (-αK) * (H : ℝ) ^ (-αK) / lam ^ (-A2exp) := by
    rw [eq_div_iff hlamnAne, R2]; ring
  have R3 : (H : ℝ) ^ (1 - αK) = (H : ℝ) * (H : ℝ) ^ (-αK) := by
    rw [show (1 : ℝ) - αK = 1 + -αK from by ring, Real.rpow_add hHRpos, Real.rpow_one]
  have hNpow : (N : ℝ) * (N : ℝ) ^ (1 - 4 / p) = (N : ℝ) ^ B2Nexp := by
    nth_rewrite 1 [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hNpos, hI2add]
  -- q-power bounds for opt_core_gen
  have hqK1 : q ^ αK ≤ 1 := Real.rpow_le_one (le_of_lt hqpos) hqle1 (le_of_lt hαKpos)
  have hqnK2 : q ^ (-αK) ≤ 2 := by
    have hqa : (1 : ℝ) / 2 ≤ q ^ αK := by
      calc (1 : ℝ) / 2 = ((1 : ℝ) / 2) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ ((1 : ℝ) / 2) ^ αK :=
            Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (le_of_lt hαKlt1)
        _ ≤ q ^ αK := Real.rpow_le_rpow (by norm_num) hqge (le_of_lt hαKpos)
    rw [Real.rpow_neg (le_of_lt hqpos)]
    calc (q ^ αK)⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ := inv_anti₀ (by norm_num) hqa
      _ = 2 := by norm_num
  -- the per-shift bound function
  set base : ℤ → ℝ := fun m => Cp * cg * ((N : ℝ) * (((m : ℝ)) * lam) ^ αK
    + (N : ℝ) ^ (1 - 4 / p) * (((m : ℝ)) * lam) ^ (-αK)) with hbasedef
  -- per-shift bound (defeq `base = Gh_bound_gen`, established before values are cleared)
  have hbase_bound : ∀ i : ℕ, i < H →
      ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
          (fun n => n + ((i : ℤ) + 1) ∈ Finset.Ioc a (a + (N : ℤ))),
          eR (f (n + ((i : ℤ) + 1)) - f n)‖ ≤ base ((i : ℤ) + 1) := fun i hiH =>
    Gh_bound_gen K Cp hCp hih f a N lam c hlam hc hβKnn hlb hub ((i : ℤ) + 1) (by omega) (by omega)
  -- make every exponent/atom opaque so `ring`/`field_simp` never expand `2ᴷ`
  clear_value base BB AA q cg B2Nexp A2exp αK g' β' α' p
  -- the squared bound (A-process + power sums + `opt_core_gen`)
  have hP : ‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖ ^ 2 ≤ 16 * Cp * cg * (AA + BB) := by
    have hA := weyl_vdC_expSum f a N H hH1 hHN
    have hsymm := sum_Icc_symm H (fun h : ℤ =>
      ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter (fun n => n + h ∈ Finset.Ioc a (a + (N : ℤ))),
          eR (f (n + h) - f n)‖)
    have hphi0 : ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
          (fun n => n + (0 : ℤ) ∈ Finset.Ioc a (a + (N : ℤ))), eR (f (n + 0) - f n)‖ ≤ (N : ℝ) := by
      calc ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
                (fun n => n + (0 : ℤ) ∈ Finset.Ioc a (a + (N : ℤ))), eR (f (n + 0) - f n)‖
          ≤ ∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
                (fun n => n + (0 : ℤ) ∈ Finset.Ioc a (a + (N : ℤ))), ‖eR (f (n + 0) - f n)‖ :=
            norm_sum_le _ _
        _ = ∑ _n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
                (fun n => n + (0 : ℤ) ∈ Finset.Ioc a (a + (N : ℤ))), (1 : ℝ) := by
            simp only [norm_eR]
        _ = (((Finset.Ioc a (a + (N : ℤ))).filter
                (fun n => n + (0 : ℤ) ∈ Finset.Ioc a (a + (N : ℤ)))).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ((Finset.Ioc a (a + (N : ℤ))).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        _ = (N : ℝ) := by rw [Int.card_Ioc, show a + (N : ℤ) - a = (N : ℤ) from by ring]; simp
    have hpair : ∀ i ∈ Finset.range H,
        ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
            (fun n => n + ((i : ℤ) + 1) ∈ Finset.Ioc a (a + (N : ℤ))),
            eR (f (n + ((i : ℤ) + 1)) - f n)‖
          + ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
            (fun n => n + (-((i : ℤ) + 1)) ∈ Finset.Ioc a (a + (N : ℤ))),
            eR (f (n + (-((i : ℤ) + 1))) - f n)‖
        ≤ 2 * base ((i : ℤ) + 1) := by
      intro i hi
      have hiH : i < H := Finset.mem_range.mp hi
      rw [Gh_norm_symm f a N ((i : ℤ) + 1)]
      linarith [hbase_bound i hiH]
    have hsumle : ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
          ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
              (fun n => n + h ∈ Finset.Ioc a (a + (N : ℤ))), eR (f (n + h) - f n)‖
        ≤ (N : ℝ) + 2 * ∑ i ∈ Finset.range H, base ((i : ℤ) + 1) := by
      rw [hsymm, Finset.mul_sum]
      have hpairsum := Finset.sum_le_sum hpair
      linarith [hphi0, hpairsum]
    have hbase_split : ∑ i ∈ Finset.range H, base ((i : ℤ) + 1)
        = Cp * cg * (N : ℝ) * lam ^ αK * (∑ i ∈ Finset.range H, ((i : ℝ) + 1) ^ αK)
          + Cp * cg * (N : ℝ) ^ (1 - 4 / p) * lam ^ (-αK)
              * (∑ i ∈ Finset.range H, ((i : ℝ) + 1) ^ (-αK)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [hbasedef]
      rw [show ((((i : ℤ) + 1 : ℤ)) : ℝ) = (i : ℝ) + 1 from by push_cast; ring,
        Real.mul_rpow (by positivity) (le_of_lt hlam),
        Real.mul_rpow (by positivity) (le_of_lt hlam)]
      ring
    have hbasesum : ∑ i ∈ Finset.range H, base ((i : ℤ) + 1)
        ≤ Cp * cg * (N : ℝ) * lam ^ αK * ((H : ℝ) * (H : ℝ) ^ αK)
          + Cp * cg * (N : ℝ) ^ (1 - 4 / p) * lam ^ (-αK) * ((H : ℝ) ^ (1 - αK) / (1 - αK)) := by
      rw [hbase_split]
      have hcoef1 : (0 : ℝ) ≤ Cp * cg * (N : ℝ) * lam ^ αK :=
        mul_nonneg (mul_nonneg (mul_nonneg hCp0 hcg0) hN) (le_of_lt (Real.rpow_pos_of_pos hlam _))
      have hcoef2 : (0 : ℝ) ≤ Cp * cg * (N : ℝ) ^ (1 - 4 / p) * lam ^ (-αK) :=
        mul_nonneg (mul_nonneg (mul_nonneg hCp0 hcg0) (Real.rpow_nonneg hN _))
          (le_of_lt (Real.rpow_pos_of_pos hlam _))
      exact add_le_add (mul_le_mul_of_nonneg_left (sum_rpow_pos_le αK (le_of_lt hαKpos) H) hcoef1)
        (mul_le_mul_of_nonneg_left (sum_rpow_neg_le αK hαKpos hαKlt1 H) hcoef2)
    have hbase_nn : (0 : ℝ) ≤ ∑ i ∈ Finset.range H, base ((i : ℤ) + 1) :=
      Finset.sum_nonneg fun i hi =>
        le_trans (norm_nonneg _) (hbase_bound i (Finset.mem_range.mp hi))
    have hfactor : ((N : ℝ) + (H : ℝ)) / ((H : ℝ) + 1) ≤ 2 * (N : ℝ) / (H : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hHRpos,
        show ((N : ℝ) + (H : ℝ)) * (H : ℝ) = (N : ℝ) * (H : ℝ) + (H : ℝ) * (H : ℝ) from by ring,
        show 2 * (N : ℝ) * ((H : ℝ) + 1) = 2 * ((N : ℝ) * (H : ℝ)) + 2 * (N : ℝ) from by ring]
      have hHNr : (H : ℝ) ≤ (N : ℝ) := by exact_mod_cast hHN
      have hHH : (H : ℝ) * (H : ℝ) ≤ (N : ℝ) * (H : ℝ) :=
        mul_le_mul_of_nonneg_right hHNr (le_of_lt hHRpos)
      linarith [hHH, hN]
    have hQopt : (2 * (N : ℝ) / (H : ℝ)) * ((N : ℝ) + 2 * (Cp * cg * (N : ℝ) * lam ^ αK
          * ((H : ℝ) * (H : ℝ) ^ αK)
          + Cp * cg * (N : ℝ) ^ (1 - 4 / p) * lam ^ (-αK) * ((H : ℝ) ^ (1 - αK) / (1 - αK))))
        = 2 * AA / q + 4 * Cp * cg * AA * q ^ αK + 4 * Cp * cg / (1 - αK) * BB * q ^ (-αK) := by
      rw [hqK, hqnK, hAA, hBB, ← hNpow, R3, hq]
      field_simp
      ring
    calc ‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖ ^ 2
        ≤ ((N : ℝ) + (H : ℝ)) / ((H : ℝ) + 1)
            * ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
              ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
                  (fun n => n + h ∈ Finset.Ioc a (a + (N : ℤ))), eR (f (n + h) - f n)‖ := hA
      _ ≤ ((N : ℝ) + (H : ℝ)) / ((H : ℝ) + 1)
            * ((N : ℝ) + 2 * ∑ i ∈ Finset.range H, base ((i : ℤ) + 1)) :=
          mul_le_mul_of_nonneg_left hsumle (by positivity)
      _ ≤ (2 * (N : ℝ) / (H : ℝ)) * ((N : ℝ) + 2 * (Cp * cg * (N : ℝ) * lam ^ αK
              * ((H : ℝ) * (H : ℝ) ^ αK)
              + Cp * cg * (N : ℝ) ^ (1 - 4 / p) * lam ^ (-αK) * ((H : ℝ) ^ (1 - αK) / (1 - αK)))) :=
          mul_le_mul hfactor (by linarith [hbasesum]) (by linarith [hbase_nn]) (by positivity)
      _ = 2 * AA / q + 4 * Cp * cg * AA * q ^ αK + 4 * Cp * cg / (1 - αK) * BB * q ^ (-αK) := hQopt
      _ ≤ 16 * Cp * cg * (AA + BB) :=
          opt_core_gen AA BB q Cp cg (q ^ αK) (q ^ (-αK)) αK hAA0 hBB0 hqge hCp hcg1 hqK1 hqnK2
            hαKle
  -- take square roots
  have hCp0 : (0 : ℝ) ≤ Cp := by linarith
  have hsum16 : (16 : ℝ) * Cp * cg * (AA + BB) = 16 * (Cp * (cg * (AA + BB))) := by ring
  calc ‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖
      = Real.sqrt (‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (16 * Cp * cg * (AA + BB)) := Real.sqrt_le_sqrt hP
    _ = 4 * (Real.sqrt Cp * (Real.sqrt cg * Real.sqrt (AA + BB))) := by
        rw [hsum16, Real.sqrt_mul (by norm_num), Real.sqrt_mul hCp0, Real.sqrt_mul hcg0,
          show Real.sqrt (16 : ℝ) = 4 from by
            rw [show (16 : ℝ) = 4 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]]
    _ ≤ 4 * (Real.sqrt Cp * (Real.sqrt cg * (Real.sqrt AA + Real.sqrt BB))) := by
        gcongr
        exact Real_sqrt_add_le AA BB hAA0 hBB0
    _ = 4 * Real.sqrt Cp * c ^ g' * ((N : ℝ) * lam ^ α' + (N : ℝ) ^ β' * lam ^ (-α')) := by
        rw [hsqrtcg, hsqrtAA, hsqrtBB]; ring

/-- **The induction step.**  From the level-`K` bound (constant `Cp`) obtain the
level-`(K+1)` bound with constant `4√Cp`: pick `H = ⌊λ^{−2α'}⌋₊` in the main
regime `1 ≤ λ^{−2α'} ≤ N`, and fall back to the trivial norm bound `‖S‖ ≤ N`
otherwise. -/
lemma isVdCBound_succ (K : ℕ) (hK : 2 ≤ K) (Cp : ℝ) (hCp : 1 ≤ Cp) (hih : IsVdCBound K Cp) :
    IsVdCBound (K + 1) (4 * Real.sqrt Cp) := by
  intro f a b lam c hab hlam hc hlb hub
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, b = a + N := ⟨(b - a).toNat, by omega⟩
  have hbN : ((a + (N : ℤ) : ℤ) : ℝ) - (a : ℝ) = (N : ℝ) := by push_cast; ring
  rw [hbN]
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hc0 : (0 : ℝ) ≤ c := by linarith
  set p : ℝ := (2 : ℝ) ^ K with hp
  have hp4 : (4 : ℝ) ≤ p := four_le_two_pow K hK
  have hpK1 : (2 : ℝ) ^ (K + 1) = 2 * p := by rw [hp, pow_succ]; ring
  have hxpos : 0 < lam ^ (-(1 / (p - 1))) := Real.rpow_pos_of_pos hlam _
  have htriv : ‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖ ≤ (N : ℝ) := by
    calc ‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖
        ≤ ∑ n ∈ Finset.Ioc a (a + (N : ℤ)), ‖eR (f n)‖ := norm_sum_le _ _
      _ = ∑ _n ∈ Finset.Ioc a (a + (N : ℤ)), (1 : ℝ) := by simp only [norm_eR]
      _ = ((Finset.Ioc a (a + (N : ℤ))).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = (N : ℝ) := by rw [Int.card_Ioc, show a + (N : ℤ) - a = (N : ℤ) from by ring]; simp
  by_cases hmain : 1 ≤ lam ^ (-(1 / (p - 1))) ∧ lam ^ (-(1 / (p - 1))) ≤ (N : ℝ)
  · -- main regime: `H = ⌊λ^{−1/(2ᴷ−1)}⌋₊`
    have hH1 : 1 ≤ ⌊lam ^ (-(1 / (p - 1)))⌋₊ := (Nat.one_le_floor_iff _).mpr hmain.1
    have hHle : (⌊lam ^ (-(1 / (p - 1)))⌋₊ : ℝ) ≤ lam ^ (-(1 / (p - 1))) :=
      Nat.floor_le (le_of_lt hxpos)
    have hHlt : lam ^ (-(1 / (p - 1))) < (⌊lam ^ (-(1 / (p - 1)))⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hHN : ⌊lam ^ (-(1 / (p - 1)))⌋₊ ≤ N := by
      have := le_trans hHle hmain.2; exact_mod_cast this
    exact vdC_kth_main K hK Cp hCp hih f a N lam c hlam hc hlb hub _ hH1 hHN hHle hHlt
  · -- trivial regime
    rw [not_and_or, not_le, not_le] at hmain
    refine le_trans htriv ?_
    rw [hpK1]
    set α' : ℝ := 1 / (2 * p - 2) with hα'
    set β' : ℝ := 1 - 4 / (2 * p) with hβ'
    have hp1pos : (0 : ℝ) < p - 1 := by linarith
    have h2p2pos : (0 : ℝ) < 2 * p - 2 := by linarith
    have hα'pos : 0 < α' := by rw [hα']; exact div_pos one_pos h2p2pos
    have hsqCp : (1 : ℝ) ≤ Real.sqrt Cp := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hCp
    have hcg1 : (1 : ℝ) ≤ c ^ (4 / (2 * p)) := Real.one_le_rpow hc (by positivity)
    have hM1 : (1 : ℝ) ≤ 4 * Real.sqrt Cp * c ^ (4 / (2 * p)) := by
      nlinarith [hsqCp, hcg1, Real.rpow_nonneg hc0 (4 / (2 * p))]
    have hbr_nn : (0 : ℝ) ≤ (N : ℝ) * lam ^ α' + (N : ℝ) ^ β' * lam ^ (-α') := by positivity
    refine le_trans ?_ (le_mul_of_one_le_left hbr_nn hM1)
    rcases hmain with hlt | hgt
    · -- `λ^{−2α'} < 1` ⟹ `λ ≥ 1` ⟹ `λ^{α'} ≥ 1`
      have hlam1 : 1 ≤ lam := by
        by_contra hcon; rw [not_le] at hcon
        have he : -(1 / (p - 1)) < 0 := by
          have : (0 : ℝ) < 1 / (p - 1) := div_pos one_pos hp1pos
          linarith
        have : 1 < lam ^ (-(1 / (p - 1))) :=
          (Real.one_lt_rpow_iff_of_pos hlam).mpr (Or.inr ⟨hcon, he⟩)
        linarith [hlt]
      have hla : (1 : ℝ) ≤ lam ^ α' := Real.one_le_rpow hlam1 (le_of_lt hα'pos)
      have h1 : (N : ℝ) ≤ (N : ℝ) * lam ^ α' := le_mul_of_one_le_right hN hla
      have h2 : (0 : ℝ) ≤ (N : ℝ) ^ β' * lam ^ (-α') := by positivity
      linarith
    · -- `λ^{−2α'} > N`
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · rw [hN0]; push_cast; positivity
      · have hNpos' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
        have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
        have hstep1 : (N : ℝ) ^ (1 - β') ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hNpos'
          rw [hβ', show (1 : ℝ) - (1 - 4 / (2 * p)) = 4 / (2 * p) from by ring,
            div_le_iff₀ (by linarith : (0 : ℝ) < 2 * p)]
          linarith
        have hwhalf : (lam ^ (-(1 / (p - 1)))) ^ (1 / 2 : ℝ) = lam ^ (-α') := by
          rw [← Real.rpow_mul (le_of_lt hlam), hα',
            show -(1 / (p - 1)) * (1 / 2 : ℝ) = -(1 / (2 * p - 2)) from by
              rw [neg_mul, one_div_mul_one_div, show (p - 1) * 2 = 2 * p - 2 from by ring]]
        have hstep2 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ lam ^ (-α') := by
          rw [← hwhalf]; exact Real.rpow_le_rpow hN (le_of_lt hgt) (by norm_num)
        have h2 : (N : ℝ) ≤ (N : ℝ) ^ β' * lam ^ (-α') := by
          have hNsplit : (N : ℝ) ^ β' * (N : ℝ) ^ (1 - β') = (N : ℝ) := by
            rw [← Real.rpow_add hNposR, show β' + (1 - β') = (1 : ℝ) from by ring, Real.rpow_one]
          calc (N : ℝ) = (N : ℝ) ^ β' * (N : ℝ) ^ (1 - β') := hNsplit.symm
            _ ≤ (N : ℝ) ^ β' * lam ^ (-α') :=
                mul_le_mul_of_nonneg_left (le_trans hstep1 hstep2) (Real.rpow_nonneg hN _)
        have h1 : (0 : ℝ) ≤ (N : ℝ) * lam ^ α' := by positivity
        linarith

/-- **van der Corput's `k`-th derivative test (uniform in `k`).**  For every
`k ≥ 2` there is a constant `C ≥ 1` such that for any phase `f : ℤ → ℝ` whose
`k`-th forward differences `dk k f` lie in `[λ, cλ]` on `(a, b)` (`0 < λ`,
`1 ≤ c`),
`‖∑ eR (f n)‖ ≤ C·c^{4/2^k}·((b−a)·λ^{1/(2^k−2)} + (b−a)^{1−4/2^k}·λ^{−1/(2^k−2)})`.
The `∃ C` is threaded through the induction (`C(2)=8`, `C(k+1)=4√C(k)`); the
exponents are the Graham–Kolesnik `α_k = 1/(2^k−2)`, `β_k = 1 − 2^{2−k}`,
`c`-grade `2^{2−k}`. -/
theorem vdC_kth_derivative : ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 1 ≤ C ∧ IsVdCBound k C := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨8, by norm_num, isVdCBound_two⟩
  | succ K hK ih =>
      obtain ⟨Cp, hCp1, hCp⟩ := ih
      refine ⟨4 * Real.sqrt Cp, ?_, isVdCBound_succ K hK Cp hCp1 hCp⟩
      have h : (1 : ℝ) ≤ Real.sqrt Cp := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hCp1
      linarith

end Salt.ExpSum
