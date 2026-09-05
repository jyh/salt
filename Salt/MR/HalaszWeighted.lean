/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# B2 W8 — Jutila's Lemma 7 (L7): Halász's inequality with the `η_j` retained

Jutila 1977, Lemma 7, p.51 (Montgomery, *Topics*, Lemma 1.6 with the unimodular `η_j` kept
rather than eliminated by absolute values — the feature Huxley's (3.7) exploits). For the
Dirichlet polynomials `f(s_j, χ_j) = Σ_{n ∈ S} a_n χ_j(n) n^{−s_j}`, `j = 1, …, J`, positive
weights `b_n > 0` wherever `a_n ≠ 0`, and unimodular `η_j` with `η_j f(s_j, χ_j) = |f(s_j, χ_j)|`,

    (Σ_j |f(s_j, χ_j)|)²  ≤  Σ_n |a_n|² b_n⁻¹ · Σ_{j,k} η̄_j η_k B(s̄_j + s_k; χ_j, χ_k),
    B(s; χ_j, χ_k) = Σ_n b_n χ̄_j(n) χ_k(n) n^{−s}.

The proof is Cauchy–Schwarz on `Σ_j |f_j| = Σ_j η_j f_j = Σ_n a_n (Σ_j η_j χ_j(n) n^{−s_j})`
followed by the expansion of `Σ_n b_n |Σ_j η_j χ_j(n) n^{−s_j}|²`. The "character" `χ̄_j χ_k`
enters only through its VALUES `conj(χ_j n) · χ_k n` — W9 rewrites it as `(χ_j⁻¹ * χ_k) n`
(`MulChar.star_apply'`) where the Euler product is wanted. The `tsum` form (`halasz_weighted_tsum`)
is the one W9 consumes: `B` summed over ALL `n` under the summability of each `(j, k)`-series,
with `b_n ≥ 0` everywhere and `b_0 = 0`; `halaszBTsum_eq` rewrites `B` as the L-series of the
character `χ₁⁻¹ * χ₂` (termwise, non-units included), so W9 never rewrites under a `tsum` binder.

## Why the binders are where they are

* `0 ∉ S` on the finite identity: at `n = 0` Lean's `0 ^ (−s)` is `1` when `s = 0` and `0`
  otherwise, so `0^{−s̄_j}·0^{−s_k} ≠ 0^{−(s̄_j + s_k)}` at `s_j = s_k = i` (`0 ≠ 1`). The mutation
  control runs at `q = 1` (`12 ≠ 16` at `S = {0,1,2,3}`, `b ≡ 1`, `s_j = s_k = i`): at any live
  modulus `χ(0) = 0` makes both sides vanish and a pass proves nothing. The binder STAYS — `q`
  carries no `NeZero`, and `q = 1` is in range.
* `b_0 = 0` on the `tsum` form, for the same `n = 0` junk value.
* `0 < b_n` only where `a_n ≠ 0`: where `a_n = 0` the term `‖a_n‖²/b_n` is `0` in Lean whatever
  `b_n` is; `0 ≤ b_n` on `S` is what Cauchy–Schwarz reads.

## The honest label

Every row here is an INPUT to the density theorem's assembly (W9); nothing bears on twin primes
or on the crown's conditions. No landed Halász file is consumed (`HalaszIntegers.lean:908`,
`VdCSocket.lean:547` are EVALUATIONS of `B`, which is W9b's work); `MVHilbert.lean` is untouched.

## The measured receipt (`h2c-desk/w7_receipts.py`, item (l))

`J = 2`, `S = [1, 50]`, `b_n = 1/n`, `χ mod 5` and its square, `s = (0.7 + 2i, 1.1 − 3i)`,
`a_n = sin n + 0.3i cos 2n`: the expansion identity holds to `8.9e−16`; `(Σ_j |f_j|)² = 6.7991
≤ 2913.48`; `|η_j| = 1`.
-/

open Complex

noncomputable section
namespace Salt.MR

variable {q : ℕ}

/-- The Dirichlet polynomial `f(s, χ) = Σ_{n ∈ S} a_n χ(n) n^{−s}`. -/
def dirichletPolyChi (S : Finset ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ n ∈ S, a n * χ n * (n : ℂ) ^ (-s)

/-- The weighted finite series `B(s; χ₁, χ₂) = Σ_{n ∈ S} b_n · conj(χ₁ n) · χ₂ n · n^{−s}`. -/
def halaszB (S : Finset ℕ) (b : ℕ → ℝ) (χ₁ χ₂ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ n ∈ S, (b n : ℂ) * (starRingEnd ℂ) (χ₁ n) * χ₂ n * (n : ℂ) ^ (-s)

/-- The weighted series over ALL `n`: `B(s; χ₁, χ₂) = Σ'_n b_n · conj(χ₁ n) · χ₂ n · n^{−s}`. -/
def halaszBTsum (b : ℕ → ℝ) (χ₁ χ₂ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (b n : ℂ) * (starRingEnd ℂ) (χ₁ n) * χ₂ n * (n : ℂ) ^ (-s)

theorem exists_unimodular_mul_eq_norm (z : ℂ) : ∃ η : ℂ, ‖η‖ = 1 ∧ η * z = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  · refine ⟨(‖z‖ : ℂ) / z, ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.mpr hz)]
    · exact div_mul_cancel₀ _ hz

theorem sum_norm_dirichletPolyChi_eq {J : ℕ} (S : Finset ℕ) (a : ℕ → ℂ)
    (χ : Fin J → DirichletCharacter ℂ q) (s : Fin J → ℂ) (η : Fin J → ℂ)
    (hη : ∀ j, η j * dirichletPolyChi S a (χ j) (s j) = ‖dirichletPolyChi S a (χ j) (s j)‖) :
    ((∑ j, ‖dirichletPolyChi S a (χ j) (s j)‖ : ℝ) : ℂ)
      = ∑ n ∈ S, a n * ∑ j, η j * χ j n * (n : ℂ) ^ (-(s j)) := by
  have h1 : ∀ j : Fin J, ((‖dirichletPolyChi S a (χ j) (s j)‖ : ℝ) : ℂ)
      = ∑ n ∈ S, η j * (a n * χ j n * (n : ℂ) ^ (-(s j))) := by
    intro j
    have hd : dirichletPolyChi S a (χ j) (s j)
        = ∑ n ∈ S, a n * χ j n * (n : ℂ) ^ (-(s j)) := rfl
    rw [← hη j, hd, Finset.mul_sum]
  rw [Complex.ofReal_sum, Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Cauchy-Schwarz on `‖a_n‖/√b_n` and `√b_n‖c_n‖`, with the `a_n = 0` terms handled by
Lean's `0 / 0 = 0`.  The abstract shape behind `sq_sum_norm_dirichletPolyChi_le`. -/
private lemma sq_le_of_norm_sum (S : Finset ℕ) (a c : ℕ → ℂ) {b : ℕ → ℝ} {A : ℝ}
    (hA0 : 0 ≤ A) (hb : ∀ n ∈ S, a n ≠ 0 → 0 < b n) (hb0 : ∀ n ∈ S, 0 ≤ b n)
    (hAeq : (A : ℂ) = ∑ n ∈ S, a n * c n) :
    A ^ 2 ≤ (∑ n ∈ S, ‖a n‖ ^ 2 / b n) * ∑ n ∈ S, b n * ‖c n‖ ^ 2 := by
  have hstep1 : A ≤ ∑ n ∈ S, ‖a n‖ * ‖c n‖ := by
    have h1 : A = ‖∑ n ∈ S, a n * c n‖ := by
      rw [← hAeq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0]
    rw [h1]
    calc ‖∑ n ∈ S, a n * c n‖ ≤ ∑ n ∈ S, ‖a n * c n‖ := norm_sum_le _ _
      _ = ∑ n ∈ S, ‖a n‖ * ‖c n‖ := Finset.sum_congr rfl fun n _ => norm_mul _ _
  have hsplit : ∀ n ∈ S, ‖a n‖ * ‖c n‖
      = ‖a n‖ / Real.sqrt (b n) * (Real.sqrt (b n) * ‖c n‖) := by
    intro n hn
    by_cases ha : a n = 0
    · simp [ha]
    · have hsq : Real.sqrt (b n) ≠ 0 := (Real.sqrt_pos.mpr (hb n hn ha)).ne'
      have h2 : ‖a n‖ / Real.sqrt (b n) * (Real.sqrt (b n) * ‖c n‖)
          = ‖a n‖ * ‖c n‖ * (Real.sqrt (b n) / Real.sqrt (b n)) := by ring
      rw [h2, div_self hsq, mul_one]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun n => ‖a n‖ / Real.sqrt (b n))
    (fun n => Real.sqrt (b n) * ‖c n‖)
  have hL : (∑ n ∈ S, (‖a n‖ / Real.sqrt (b n)) ^ 2) = ∑ n ∈ S, ‖a n‖ ^ 2 / b n :=
    Finset.sum_congr rfl fun n hn => by rw [div_pow, Real.sq_sqrt (hb0 n hn)]
  have hR : (∑ n ∈ S, (Real.sqrt (b n) * ‖c n‖) ^ 2) = ∑ n ∈ S, b n * ‖c n‖ ^ 2 :=
    Finset.sum_congr rfl fun n hn => by rw [mul_pow, Real.sq_sqrt (hb0 n hn)]
  calc A ^ 2 ≤ (∑ n ∈ S, ‖a n‖ * ‖c n‖) ^ 2 := pow_le_pow_left₀ hA0 hstep1 2
    _ = (∑ n ∈ S, ‖a n‖ / Real.sqrt (b n) * (Real.sqrt (b n) * ‖c n‖)) ^ 2 := by
        rw [Finset.sum_congr rfl hsplit]
    _ ≤ (∑ n ∈ S, (‖a n‖ / Real.sqrt (b n)) ^ 2)
          * ∑ n ∈ S, (Real.sqrt (b n) * ‖c n‖) ^ 2 := hCS
    _ = (∑ n ∈ S, ‖a n‖ ^ 2 / b n) * ∑ n ∈ S, b n * ‖c n‖ ^ 2 := by rw [hL, hR]

theorem sq_sum_norm_dirichletPolyChi_le {J : ℕ} (S : Finset ℕ) (a : ℕ → ℂ) {b : ℕ → ℝ}
    (hb : ∀ n ∈ S, a n ≠ 0 → 0 < b n) (hb0 : ∀ n ∈ S, 0 ≤ b n)
    (χ : Fin J → DirichletCharacter ℂ q) (s : Fin J → ℂ) (η : Fin J → ℂ)
    (hη : ∀ j, η j * dirichletPolyChi S a (χ j) (s j) = ‖dirichletPolyChi S a (χ j) (s j)‖) :
    (∑ j, ‖dirichletPolyChi S a (χ j) (s j)‖) ^ 2
      ≤ (∑ n ∈ S, ‖a n‖ ^ 2 / b n)
        * ∑ n ∈ S, b n * ‖∑ j, η j * χ j n * (n : ℂ) ^ (-(s j))‖ ^ 2 := by
  refine sq_le_of_norm_sum S a (fun n => ∑ j, η j * χ j n * (n : ℂ) ^ (-(s j)))
    (Finset.sum_nonneg fun j _ => norm_nonneg _) hb hb0 ?_
  exact sum_norm_dirichletPolyChi_eq S a χ s η hη

/-- The two swaps that bring the `n`-sum innermost. -/
private lemma sum_swap_three {J : ℕ} (S : Finset ℕ) (T : ℕ → Fin J → Fin J → ℂ) :
    ∑ n ∈ S, ∑ j, ∑ k, T n j k = ∑ j, ∑ k, ∑ n ∈ S, T n j k :=
  Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)

/-- The expansion of `b_n‖c_n‖²` at a single `n ≠ 0`: `‖z‖² = conj z · z`, the double sum,
and `n^{-conj s_j}·n^{-s_k} = n^{-(conj s_j + s_k)}` (which is where `n ≠ 0` is spent). -/
private lemma ofReal_mul_norm_sq_eq {J : ℕ} {n : ℕ} (hn : n ≠ 0) (b : ℕ → ℝ)
    (χ : Fin J → DirichletCharacter ℂ q) (s : Fin J → ℂ) (η : Fin J → ℂ) :
    ((b n * ‖∑ j, η j * χ j n * (n : ℂ) ^ (-(s j))‖ ^ 2 : ℝ) : ℂ)
      = ∑ j, ∑ k, (starRingEnd ℂ) (η j) * η k
          * ((b n : ℂ) * (starRingEnd ℂ) (χ j n) * χ k n
              * (n : ℂ) ^ (-((starRingEnd ℂ) (s j) + s k))) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_pos.ne
  have hconj : ∀ w : ℂ, (starRingEnd ℂ) ((n : ℂ) ^ (-w))
      = (n : ℂ) ^ (-((starRingEnd ℂ) w)) := by
    intro w
    rw [← map_neg, Complex.cpow_conj (n : ℂ) (-w) harg, Complex.conj_natCast]
  rw [Complex.ofReal_mul, Complex.sq_norm, Complex.normSq_eq_conj_mul_self, map_sum,
    Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_mul]
  rw [hconj, neg_add, Complex.cpow_add _ _ hn0]
  ring

theorem sum_mul_norm_sq_eq_halaszB {J : ℕ} {S : Finset ℕ} (hS : 0 ∉ S) (b : ℕ → ℝ)
    (χ : Fin J → DirichletCharacter ℂ q) (s : Fin J → ℂ) (η : Fin J → ℂ) :
    ((∑ n ∈ S, b n * ‖∑ j, η j * χ j n * (n : ℂ) ^ (-(s j))‖ ^ 2 : ℝ) : ℂ)
      = ∑ j, ∑ k, (starRingEnd ℂ) (η j) * η k
          * halaszB S b (χ j) (χ k) ((starRingEnd ℂ) (s j) + s k) := by
  have key : ∀ n ∈ S, ((b n * ‖∑ j, η j * χ j n * (n : ℂ) ^ (-(s j))‖ ^ 2 : ℝ) : ℂ)
      = ∑ j, ∑ k, (starRingEnd ℂ) (η j) * η k
          * ((b n : ℂ) * (starRingEnd ℂ) (χ j n) * χ k n
              * (n : ℂ) ^ (-((starRingEnd ℂ) (s j) + s k))) :=
    fun n hn => ofReal_mul_norm_sq_eq (ne_of_mem_of_not_mem hn hS) b χ s η
  rw [Complex.ofReal_sum, Finset.sum_congr rfl key,
    sum_swap_three S fun n j k => (starRingEnd ℂ) (η j) * η k
      * ((b n : ℂ) * (starRingEnd ℂ) (χ j n) * χ k n
          * (n : ℂ) ^ (-((starRingEnd ℂ) (s j) + s k)))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have hd : halaszB S b (χ j) (χ k) ((starRingEnd ℂ) (s j) + s k)
      = ∑ n ∈ S, (b n : ℂ) * (starRingEnd ℂ) (χ j n) * χ k n
          * (n : ℂ) ^ (-((starRingEnd ℂ) (s j) + s k)) := rfl
  rw [hd, Finset.mul_sum]

theorem halasz_weighted {J : ℕ} {S : Finset ℕ} (hS : 0 ∉ S) (a : ℕ → ℂ) {b : ℕ → ℝ}
    (hb : ∀ n ∈ S, a n ≠ 0 → 0 < b n) (hb0 : ∀ n ∈ S, 0 ≤ b n)
    (χ : Fin J → DirichletCharacter ℂ q) (s : Fin J → ℂ) (η : Fin J → ℂ)
    (hη : ∀ j, η j * dirichletPolyChi S a (χ j) (s j) = ‖dirichletPolyChi S a (χ j) (s j)‖) :
    (∑ j, ‖dirichletPolyChi S a (χ j) (s j)‖) ^ 2
      ≤ (∑ n ∈ S, ‖a n‖ ^ 2 / b n)
        * (∑ j, ∑ k, (starRingEnd ℂ) (η j) * η k
            * halaszB S b (χ j) (χ k) ((starRingEnd ℂ) (s j) + s k)).re := by
  have h2 := sum_mul_norm_sq_eq_halaszB (J := J) hS b χ s η
  have h3 : (∑ n ∈ S, b n * ‖∑ j, η j * χ j n * (n : ℂ) ^ (-(s j))‖ ^ 2)
      = (∑ j, ∑ k, (starRingEnd ℂ) (η j) * η k
          * halaszB S b (χ j) (χ k) ((starRingEnd ℂ) (s j) + s k)).re := by
    rw [← h2, Complex.ofReal_re]
  rw [← h3]
  exact sq_sum_norm_dirichletPolyChi_le S a hb hb0 χ s η hη

theorem halasz_weighted_tsum {J : ℕ} {S : Finset ℕ} (hS : 0 ∉ S) (a : ℕ → ℂ) {b : ℕ → ℝ}
    (hb : ∀ n ∈ S, a n ≠ 0 → 0 < b n) (hb0 : ∀ n, 0 ≤ b n) (hb00 : b 0 = 0)
    (χ : Fin J → DirichletCharacter ℂ q) (s : Fin J → ℂ) (η : Fin J → ℂ)
    (hη : ∀ j, η j * dirichletPolyChi S a (χ j) (s j) = ‖dirichletPolyChi S a (χ j) (s j)‖)
    (hsum : ∀ j k, Summable (fun n : ℕ => (b n : ℂ) * (starRingEnd ℂ) (χ j n) * χ k n
      * (n : ℂ) ^ (-((starRingEnd ℂ) (s j) + s k)))) :
    (∑ j, ‖dirichletPolyChi S a (χ j) (s j)‖) ^ 2
      ≤ (∑ n ∈ S, ‖a n‖ ^ 2 / b n)
        * (∑ j, ∑ k, (starRingEnd ℂ) (η j) * η k
            * halaszBTsum b (χ j) (χ k) ((starRingEnd ℂ) (s j) + s k)).re := by
  have hjk : ∀ j k : Fin J, Summable fun n : ℕ => (starRingEnd ℂ) (η j) * η k
      * ((b n : ℂ) * (starRingEnd ℂ) (χ j n) * χ k n
          * (n : ℂ) ^ (-((starRingEnd ℂ) (s j) + s k))) :=
    fun j k => (hsum j k).mul_left ((starRingEnd ℂ) (η j) * η k)
  have hj : ∀ j : Fin J, Summable fun n : ℕ => ∑ k, (starRingEnd ℂ) (η j) * η k
      * ((b n : ℂ) * (starRingEnd ℂ) (χ j n) * χ k n
          * (n : ℂ) ^ (-((starRingEnd ℂ) (s j) + s k))) :=
    fun j => summable_sum fun k _ => hjk j k
  have hF : Summable fun n : ℕ => ∑ j, ∑ k, (starRingEnd ℂ) (η j) * η k
      * ((b n : ℂ) * (starRingEnd ℂ) (χ j n) * χ k n
          * (n : ℂ) ^ (-((starRingEnd ℂ) (s j) + s k))) :=
    summable_sum fun j _ => hj j
  have hre : ∀ n : ℕ, b n * ‖∑ j, η j * χ j n * (n : ℂ) ^ (-(s j))‖ ^ 2
      = (∑ j, ∑ k, (starRingEnd ℂ) (η j) * η k
          * ((b n : ℂ) * (starRingEnd ℂ) (χ j n) * χ k n
              * (n : ℂ) ^ (-((starRingEnd ℂ) (s j) + s k)))).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hb00]
    · rw [← ofReal_mul_norm_sq_eq hn b χ s η, Complex.ofReal_re]
  have hgs : HasSum (fun n : ℕ => b n * ‖∑ j, η j * χ j n * (n : ℂ) ^ (-(s j))‖ ^ 2)
      (∑' n : ℕ, ∑ j, ∑ k, (starRingEnd ℂ) (η j) * η k
          * ((b n : ℂ) * (starRingEnd ℂ) (χ j n) * χ k n
              * (n : ℂ) ^ (-((starRingEnd ℂ) (s j) + s k)))).re := by
    simpa only [← hre] using Complex.hasSum_re hF.hasSum
  have htsum : (∑' n : ℕ, ∑ j, ∑ k, (starRingEnd ℂ) (η j) * η k
      * ((b n : ℂ) * (starRingEnd ℂ) (χ j n) * χ k n
          * (n : ℂ) ^ (-((starRingEnd ℂ) (s j) + s k))))
      = ∑ j, ∑ k, (starRingEnd ℂ) (η j) * η k
          * halaszBTsum b (χ j) (χ k) ((starRingEnd ℂ) (s j) + s k) := by
    rw [Summable.tsum_finsetSum fun j _ => hj j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Summable.tsum_finsetSum fun k _ => hjk j k]
    exact Finset.sum_congr rfl fun k _ => tsum_mul_left
  have hfin : (∑ j, ∑ k, (starRingEnd ℂ) (η j) * η k
      * halaszB S b (χ j) (χ k) ((starRingEnd ℂ) (s j) + s k)).re
      = ∑ n ∈ S, b n * ‖∑ j, η j * χ j n * (n : ℂ) ^ (-(s j))‖ ^ 2 := by
    rw [← sum_mul_norm_sq_eq_halaszB (J := J) hS b χ s η, Complex.ofReal_re]
  have hP : 0 ≤ ∑ n ∈ S, ‖a n‖ ^ 2 / b n :=
    Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (hb0 n)
  refine le_trans (halasz_weighted hS a hb (fun n _ => hb0 n) χ s η hη) ?_
  rw [hfin, ← htsum]
  exact mul_le_mul_of_nonneg_left
    (sum_le_hasSum S (fun n _ => mul_nonneg (hb0 n) (sq_nonneg _)) hgs) hP

theorem halaszBTsum_eq (b : ℕ → ℝ) (χ₁ χ₂ : DirichletCharacter ℂ q) (s : ℂ) :
    halaszBTsum b χ₁ χ₂ s = ∑' n : ℕ, (b n : ℂ) * ((χ₁⁻¹ * χ₂) n) * (n : ℂ) ^ (-s) := by
  have hd : halaszBTsum b χ₁ χ₂ s
      = ∑' n : ℕ, (b n : ℂ) * (starRingEnd ℂ) (χ₁ n) * χ₂ n * (n : ℂ) ^ (-s) := rfl
  rw [hd]
  refine tsum_congr fun n => ?_
  rw [MulChar.mul_apply, starRingEnd_apply, MulChar.star_apply']
  ring

/-- **The W8 exit row** at `J = 1`, `b ≡ 1`: Cauchy–Schwarz, INVOKING
`sq_sum_norm_dirichletPolyChi_le` (a `simpa` row over `Fin 1`). -/
example (S : Finset ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (s : ℂ) (η : ℂ)
    (hη : η * dirichletPolyChi S a χ s = ‖dirichletPolyChi S a χ s‖) :
    ‖dirichletPolyChi S a χ s‖ ^ 2
      ≤ (∑ n ∈ S, ‖a n‖ ^ 2 / (1 : ℝ)) * ∑ n ∈ S, (1 : ℝ) * ‖η * χ n * (n : ℂ) ^ (-s)‖ ^ 2 := by
  have h := sq_sum_norm_dirichletPolyChi_le (J := 1) S a (b := fun _ => (1 : ℝ))
    (fun _ _ _ => one_pos) (fun _ _ => zero_le_one) (fun _ => χ) (fun _ => s) (fun _ => η)
    (fun _ => hη)
  simpa using h

end Salt.MR

end
