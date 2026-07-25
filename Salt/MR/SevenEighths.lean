/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Dist
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Norm

/-!
# H-3 of the `hSup` ladder — the ⅞-bound (`SevenEighths`)

MRT's **seven-eighths device**: the pretentious-distance-controlled bound on the prime-side
exponential factor of the Halász error term (the `exp(∑_{p≤X} |1 − f(p)p^{−it₁}g_𝒥(p)|/p)`
object produced by [10, Lemma 7.1] in the proof of MRT's Lemma A.7).

## The source, VERBATIM

Matomäki–Radziwiłł–Tao, *An averaged form of Chowla's conjecture*, arXiv:1503.05121v3,
**printed page 25** (rendered), inside the proof of Lemma A.7:

> Here
> `∑_{p≤X} |1 − f(p)p^{−it₁}g_𝒥(p)|/p
>   = ∑_{p≤X, p∈∪_{j∈𝒥}(P_j,Q_j]} 1/p + ∑_{p≤X, p∉∪_{j∈𝒥}(P_j,Q_j]} |1 − f(p)p^{−it₁}|/p`
>
> As in [10, Proof of Corollary 3], note that for `z` in the unit disc,
> `|1 − z| = (1 + |z|² − 2ℜz)^{1/2} ≤ (2 − 2ℜz)^{1/2}`.  Applying this and Cauchy–Schwarz,
> we see that
>
> `∑_{p≤X, p∉∪_{j∈𝒥}(P_j,Q_j]} |1 − f(p)p^{−it₁}|/p
>    ≤ ∑_{p≤X, p∉∪_{j∈𝒥}(P_j,Q_j]} √(2 − 2ℜ f(p)p^{−it₁})/p`
> `   ≤ √(∑_{p≤X, p∉∪_{j∈𝒥}(P_j,Q_j]} 2/p) · √(∑_{p≤X} (1 − ℜ f(p)p^{−it₁})/p)`
> `   = √(∑_{p≤X, p∉∪_{j∈𝒥}(P_j,Q_j]} 1/p) · √(2M(f;X)).`
>
> Define `β` by
> `β log log X = ∑_{p≤X, p∈∪_{j∈𝒥}(P_j,Q_j]} 1/p.`
> Since `Q_J ≤ exp((log X)^{1/2})`, necessarily `β ∈ [0, 1/2 + O(1/log log X)]`.  Recalling
> `M(f;X) < (1/8) log log X`, we obtain
> `∑_{p≤X} |1 − f(p)p^{−it₁}g_𝒥(p)|/p ≤ β log log X + (√(1−β)/2) log log X + O(√(log log X)).`
> It is easy to see that the right hand side is increasing in `β` in our range, so it is
> maximized when `β = 1/2 + O(1/log log X)` in which case one gets a bound that is
> `≤ (7/8) log log X` and the claim follows.

**The page's constant IS `7/8`** (the true maximum of `β + √(1−β)/2` on `β ≤ 1/2` is
`1/2 + √2/4 = 0.85355…`; the printed `7/8 = 0.875` is that value rounded up, so the device
carries a genuine `0.0214… log log X` margin — see `beta_optimisation`).

## What this file lands (our conventions)

`M(f;X)` is our `pretDistSq u 1 x = ∑_{p≤x} (1 − ℜ u(p))/p` (`Salt/MR/Dist.lean:59`) at the
1-bounded datum `u(p) = f(p)p^{−it₁}`; the exceptional set `E = {p ≤ X : p ∈ ∪_{j∈𝒥}(P_j,Q_j]}`
is an arbitrary subset of the prime set, so the `𝒥`-instantiation is free.

* `norm_one_sub_sq` / `norm_one_sub_sq_le` / `norm_one_sub_le_sqrt` (S1) — the pointwise device
  `‖1 − z‖² = 1 + ‖z‖² − 2ℜz ≤ 2 − 2ℜz`, i.e. `‖1 − z‖ ≤ √(2 − 2ℜz)` on the unit disc.  This is
  the page's `|1 − z| = (1 + |z|² − 2ℜz)^{1/2} ≤ (2 − 2ℜz)^{1/2}` verbatim.  (Same algebra as
  `2(1 − ℜw) = ‖1 − w‖² + (1 − ‖w‖²)` powering `one_sub_re_pow_le`, `Salt/MR/ChiFloor.lean:93`.)
* `sq_sum_norm_one_sub_div_le` / `sum_norm_one_sub_div_le` (S2) — the prime-sum Cauchy–Schwarz
  `(∑_{p∈S} ‖1 − u(p)‖/p)² ≤ (∑_{p∈S} 2/p)·(∑_{p∈S} (1 − ℜu(p))/p)` and its √-form.  Note the
  device is applied in SQUARED form inside Cauchy–Schwarz (`r² ≤ f·g` with `f = 2/p`,
  `g = (1 − ℜu(p))/p`), so no √ is spent on the per-prime step.
* `beta_optimisation` (S3, the page's last sentence) — `β + √(1−β)/2 ≤ 7/8` for `β ≤ 1/2`.
* `seven_eighths_real` (S3) — the real core: `a + √(2b)·√m ≤ (7/8)·T` whenever `a + b ≤ T`,
  `a ≤ T/2`, `0 ≤ m ≤ T/8`; and `seven_eighths_real_slack`, the same at `a ≤ (17/32)·T`, which
  certifies that the page's `β = 1/2 + O(1/log log X)` excess does NOT break the `7/8`.
* `seven_eighths_bound` (S3, MAIN) — the ⅞-bound **exactly**, with NO error term, normalised by
  the true Mertens sum `T = ∑_{p∈S} 1/p` instead of `log log X`.
* `seven_eighths_bound_loglog` (S3′) — the page's literal `log log X`-normalised display, with
  its `O(√(log log X))` made explicit as `(√c/2)·√L`, where `c` is any Mertens budget with
  `∑_{p≤X} 1/p ≤ L + c` (`mertens_second_sharp`, `Salt/Mertens/Second.lean:216`, supplies
  `c = M + C/log X`); real core `seven_eighths_real_loglog`.
* `seven_eighths_bound_flat` (S3″) — the page's literal CLAIM, `≤ (7/8)·L` flat, once
  `c ≤ L/16` (the `O(√(log log X))` absorbed by the `0.0214…` margin); real core
  `seven_eighths_real_flat`.
* `sum_norm_one_sub_mul_split` (S4) — the page's FIRST display, as an exact identity:
  `∑_{p∈S} ‖1 − u(p)g(p)‖/p = ∑_{p∈E} 1/p + ∑_{p∈S∖E} ‖1 − u(p)‖/p` for `{0,1}`-valued `g`.
* `seven_eighths_bound_indicator` (S4) — the MRT-consumption form: the single sum
  `∑_{p∈S} ‖1 − u(p)·g(p)‖/p ≤ (7/8)·T` for `g` the `{0,1}`-valued `g_𝒥`.
* `seven_eighths_bound_primes` (S4) — the same at `S = {p ≤ x}` with `M(f;X)` presented as
  `pretDistSq u 1 x`, i.e. the shape Lemma A.7's error term consumes.

## The normalisation finding (why our main form has no `O(√(log log X))`)

The page's error term is an artefact of normalising by `log log X` while the Cauchy–Schwarz
produces `∑_{p≤X} 1/p = log log X + M + O(1/log X)`.  Normalising by `T := ∑_{p∈S} 1/p` itself
(so `β := (∑_{p∈E} 1/p)/T` exactly) makes the inequality EXACT: `seven_eighths_bound` has no
error term at all, and `seven_eighths_bound_loglog` recovers the printed form by paying
`√((1−β)L + c) ≤ √((1−β)L) + √c`.  Both hypotheses are the page's: `β ≤ 1/2` and
`M(f;X) ≤ T/8` (resp. `≤ L/8`).
-/

namespace Salt.MR

open scoped BigOperators

/-! ## S1 — the pointwise device on the unit disc -/

/-- **The exact identity of the page**: `|1 − z|² = 1 + |z|² − 2ℜz`. -/
theorem norm_one_sub_sq (z : ℂ) : ‖1 - z‖ ^ 2 = 1 + ‖z‖ ^ 2 - 2 * z.re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-- **The device, squared form.**  For `z` in the closed unit disc, `‖1 − z‖² ≤ 2 − 2ℜz`. -/
theorem norm_one_sub_sq_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖1 - z‖ ^ 2 ≤ 2 - 2 * z.re := by
  have h := norm_one_sub_sq z
  nlinarith [norm_nonneg z, hz]

/-- **The device, as printed** (`|1 − z| ≤ (2 − 2ℜz)^{1/2}` for `z` in the unit disc). -/
theorem norm_one_sub_le_sqrt {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖1 - z‖ ≤ Real.sqrt (2 - 2 * z.re) := by
  have h := Real.sqrt_le_sqrt (norm_one_sub_sq_le hz)
  rwa [Real.sqrt_sq (norm_nonneg _)] at h

/-- The per-prime Cauchy–Schwarz input: `(‖1 − u(p)‖/p)² ≤ (2/p)·((1 − ℜu(p))/p)`, i.e. the
device divided by `p²`. -/
private lemma sq_term_le {u : ℕ → ℂ} {p : ℕ} (hp : 0 < p) (hu : ‖u p‖ ≤ 1) :
    (‖1 - u p‖ / (p : ℝ)) ^ 2 ≤ 2 / (p : ℝ) * ((1 - (u p).re) / (p : ℝ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hnum : ‖1 - u p‖ ^ 2 ≤ 2 * (1 - (u p).re) := by
    have := norm_one_sub_sq_le hu; linarith
  have hinv : (0 : ℝ) ≤ 1 / ((p : ℝ) * (p : ℝ)) := by positivity
  calc (‖1 - u p‖ / (p : ℝ)) ^ 2 = ‖1 - u p‖ ^ 2 * (1 / ((p : ℝ) * (p : ℝ))) := by ring
    _ ≤ 2 * (1 - (u p).re) * (1 / ((p : ℝ) * (p : ℝ))) := mul_le_mul_of_nonneg_right hnum hinv
    _ = 2 / (p : ℝ) * ((1 - (u p).re) / (p : ℝ)) := by ring

/-! ## S2 — the prime-sum Cauchy–Schwarz -/

/-- **The prime-sum Cauchy–Schwarz, squared form.**  For 1-bounded `u` on a finite set `S` of
positive integers,
`(∑_{p∈S} ‖1 − u(p)‖/p)² ≤ (∑_{p∈S} 2/p)·(∑_{p∈S} (1 − ℜu(p))/p)`. -/
theorem sq_sum_norm_one_sub_div_le (S : Finset ℕ) (u : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0 < p) (hu : ∀ p ∈ S, ‖u p‖ ≤ 1) :
    (∑ p ∈ S, ‖1 - u p‖ / (p : ℝ)) ^ 2
      ≤ (∑ p ∈ S, (2 : ℝ) / (p : ℝ)) * ∑ p ∈ S, (1 - (u p).re) / (p : ℝ) := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S (fun p _ => by positivity)
    (fun p hp => ?_) (fun p hp => sq_term_le (hS p hp) (hu p hp))
  have h1 : (u p).re ≤ 1 := le_trans (Complex.re_le_norm _) (hu p hp)
  exact div_nonneg (by linarith) (Nat.cast_nonneg p)

/-- **The prime-sum Cauchy–Schwarz, √-form** — the page's chain
`∑ ‖1 − u(p)‖/p ≤ √(∑ 2/p)·√(∑ (1 − ℜu(p))/p)`. -/
theorem sum_norm_one_sub_div_le (S : Finset ℕ) (u : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0 < p) (hu : ∀ p ∈ S, ‖u p‖ ≤ 1) :
    ∑ p ∈ S, ‖1 - u p‖ / (p : ℝ)
      ≤ Real.sqrt (∑ p ∈ S, (2 : ℝ) / (p : ℝ))
          * Real.sqrt (∑ p ∈ S, (1 - (u p).re) / (p : ℝ)) := by
  have hnn : (0 : ℝ) ≤ ∑ p ∈ S, ‖1 - u p‖ / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg p)
  have hA : (0 : ℝ) ≤ ∑ p ∈ S, (2 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have h := Real.sqrt_le_sqrt (sq_sum_norm_one_sub_div_le S u hS hu)
  rw [Real.sqrt_sq hnn, Real.sqrt_mul hA] at h
  exact h

/-- The Cauchy–Schwarz reduction on the complement, shared by the three assemblies below:
`∑_{p∈S∖E} ‖1 − u(p)‖/p ≤ √(2·∑_{p∈S∖E} 1/p) · √(∑_{p∈S} (1 − ℜu(p))/p)`.  The distance sum on
the right runs over ALL of `S` (the page's `∑_{p≤X}`, not `∑_{p∉∪(P_j,Q_j]}`), which is
legitimate because 1-boundedness makes every term nonnegative. -/
private lemma cs_reduction (S E : Finset ℕ) (u : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0 < p) (hu : ∀ p ∈ S, ‖u p‖ ≤ 1) :
    ∑ p ∈ S \ E, ‖1 - u p‖ / (p : ℝ)
      ≤ Real.sqrt (2 * ∑ p ∈ S \ E, (1 : ℝ) / (p : ℝ))
          * Real.sqrt (∑ p ∈ S, (1 - (u p).re) / (p : ℝ)) := by
  classical
  have hsub : ∀ p ∈ S \ E, p ∈ S := fun p hp => (Finset.mem_sdiff.mp hp).1
  have hterm : ∀ p ∈ S, 0 ≤ (1 - (u p).re) / (p : ℝ) := fun p hp =>
    div_nonneg (by linarith [le_trans (Complex.re_le_norm (u p)) (hu p hp)]) (Nat.cast_nonneg p)
  have hCS := sum_norm_one_sub_div_le (S \ E) u (fun p hp => hS p (hsub p hp))
    (fun p hp => hu p (hsub p hp))
  have h2b : ∑ p ∈ S \ E, (2 : ℝ) / (p : ℝ) = 2 * ∑ p ∈ S \ E, (1 : ℝ) / (p : ℝ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
  rw [h2b] at hCS
  refine le_trans hCS (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun p hp _ => hterm p hp

/-! ## S3 — the `β`-optimisation and the ⅞-bound -/

/-- **The page's last sentence**, formalised: `β + √(1−β)/2 ≤ 7/8` for `β ≤ 1/2`.  The true
maximum on the page's range `β ∈ [0, 1/2]` is at `β = 1/2`, where the value is
`1/2 + √2/4 = 0.85355…`, so the printed `7/8` carries a `0.0214…` margin.  (The page's `0 ≤ β`
is not needed: the left side only decreases as `β ↓`.) -/
theorem beta_optimisation {β : ℝ} (h2 : β ≤ 1 / 2) :
    β + Real.sqrt (1 - β) / 2 ≤ 7 / 8 := by
  set s : ℝ := Real.sqrt (1 - β) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - β := Real.sq_sqrt (by linarith)
  -- `β ≤ 1/2` forces `s ≥ 1/√2 > 7/10`
  have hs7 : (7 : ℝ) / 10 ≤ s := by nlinarith [hs0, hs2]
  nlinarith [hs0, hs2, hs7, mul_nonneg hs0 (sub_nonneg.mpr hs7)]

/-- The √-packaging used twice below: `√(2b)·√m ≤ K` follows from `2bm ≤ K²`. -/
private lemma sqrt_mul_sqrt_le {b m K : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K)
    (h : 2 * b * m ≤ K ^ 2) : Real.sqrt (2 * b) * Real.sqrt m ≤ K := by
  have h2b : (0 : ℝ) ≤ 2 * b := by linarith
  rw [← Real.sqrt_mul h2b]
  calc Real.sqrt (2 * b * m) ≤ Real.sqrt (K ^ 2) := Real.sqrt_le_sqrt h
    _ = K := Real.sqrt_sq hK

/-- **The real core of the ⅞-bound.**  With `a` the exceptional-prime mass, `b` the remaining
Mertens mass, `m` the pretentious distance-squared budget and `T` the total: if `a + b ≤ T`,
`a ≤ T/2` (the page's `β ≤ 1/2`) and `0 ≤ m ≤ T/8` (the page's `M(f;X) < (1/8)log log X`), then
`a + √(2b)·√m ≤ (7/8)·T`.

The quadratic certificate is exact: `(7T/8 − a)² − (T − a)T/4 = (T²/16 + 2T(T/2 − a)
+ 4(T/2 − a)²)/4 ≥ 0`, whose `T²/16` slack is the `7/8 − (1/2 + √2/4)` margin. -/
theorem seven_eighths_real {a b m T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ T)
    (hhalf : a ≤ T / 2) (hm : 0 ≤ m) (hmT : m ≤ T / 8) :
    a + Real.sqrt (2 * b) * Real.sqrt m ≤ 7 / 8 * T := by
  have hT : 0 ≤ T := by linarith
  have hTa : 0 ≤ T - a := by linarith
  have hK : 0 ≤ 7 / 8 * T - a := by linarith
  have hquad : 2 * b * m ≤ (7 / 8 * T - a) ^ 2 := by
    have step1 : 2 * b * m ≤ 2 * (T - a) * (T / 8) := by
      nlinarith [mul_nonneg hm (sub_nonneg.mpr hab), mul_nonneg hTa (sub_nonneg.mpr hmT)]
    nlinarith [step1, sq_nonneg T, sq_nonneg (T / 2 - a),
      mul_nonneg hT (by linarith : (0 : ℝ) ≤ T / 2 - a)]
  linarith [sqrt_mul_sqrt_le hb hK hquad]

/-- **The ⅞-bound survives the page's `β = 1/2 + O(1/log log X)` slack.**  The page's `β` range
is `[0, 1/2 + O(1/log log X)]`, not `[0, 1/2]`; `seven_eighths_real` is stated at the clean
`a ≤ T/2`, and this variant certifies that the constant `7/8` still holds for any
`a ≤ (17/32)·T = (1/2 + 1/32)·T`.  The exact threshold is the root `a = (6 − √3)T/8
= 0.53349…·T` of `4a² − 6aT + (33/16)T²`; at `a = (17/32)T` the quadratic slack is still
`(1/256)T²`, so the `O(1/log log X)` excess is absorbed with room. -/
theorem seven_eighths_real_slack {a b m T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ T)
    (hslack : a ≤ 17 / 32 * T) (hm : 0 ≤ m) (hmT : m ≤ T / 8) :
    a + Real.sqrt (2 * b) * Real.sqrt m ≤ 7 / 8 * T := by
  have hT : 0 ≤ T := by linarith
  have hTa : 0 ≤ T - a := by linarith
  have hK : 0 ≤ 7 / 8 * T - a := by linarith
  have hquad : 2 * b * m ≤ (7 / 8 * T - a) ^ 2 := by
    have step1 : 2 * b * m ≤ 2 * (T - a) * (T / 8) := by
      nlinarith [mul_nonneg hm (sub_nonneg.mpr hab), mul_nonneg hTa (sub_nonneg.mpr hmT)]
    nlinarith [step1, sq_nonneg T, sq_nonneg (17 / 32 * T - a),
      mul_nonneg hT (by linarith : (0 : ℝ) ≤ 17 / 32 * T - a)]
  linarith [sqrt_mul_sqrt_le hb hK hquad]

/-- **The real core, `log log X`-normalised** (the page's own normalisation): if the Mertens
mass only satisfies `a + b ≤ L + c` for a budget `c ≥ 0`, the conclusion picks up exactly the
page's `O(√(log log X))`, here explicit as `(√c/2)·√L`.  The extra term is paid by
`√((1−β)L + c) ≤ √((1−β)L) + √c`. -/
theorem seven_eighths_real_loglog {a b m L c : ℝ} (hb : 0 ≤ b) (hab : a + b ≤ L + c)
    (hhalf : a ≤ L / 2) (hm : 0 ≤ m) (hmL : m ≤ L / 8) (hL : 0 ≤ L) (hc : 0 ≤ c) :
    a + Real.sqrt (2 * b) * Real.sqrt m ≤ 7 / 8 * L + Real.sqrt c / 2 * Real.sqrt L := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt c * Real.sqrt L / 2 := by positivity
  have hs2 : (Real.sqrt c * Real.sqrt L / 2) ^ 2 = c * L / 4 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hL]; ring
  have hKnn : 0 ≤ 7 / 8 * L - a + Real.sqrt c * Real.sqrt L / 2 := by linarith
  have hq : (L - a) * L / 4 ≤ (7 / 8 * L - a) ^ 2 := by
    nlinarith [sq_nonneg L, sq_nonneg (L / 2 - a),
      mul_nonneg hL (by linarith : (0 : ℝ) ≤ L / 2 - a)]
  have hquad : 2 * b * m ≤ (7 / 8 * L - a + Real.sqrt c * Real.sqrt L / 2) ^ 2 := by
    have hbm : 2 * b * m ≤ (L - a) * L / 4 + c * L / 4 := by
      nlinarith [mul_nonneg hm (by linarith : (0 : ℝ) ≤ L + c - a - b),
        mul_nonneg (by linarith : (0 : ℝ) ≤ L + c - a) (by linarith : (0 : ℝ) ≤ L / 8 - m)]
    nlinarith [hbm, hq, hs2, mul_nonneg (by linarith : (0 : ℝ) ≤ 7 / 8 * L - a) hs0]
  linarith [sqrt_mul_sqrt_le hb hKnn hquad]

/-- **The real core of the page's LITERAL claim** (`≤ (7/8) log log X`, flat).  The printed
`O(√(log log X))` is absorbed by the margin `7/8 − (1/2 + √2/4) = 0.0214…` as soon as the
Mertens budget satisfies `c ≤ L/16`: the quadratic certificate
`(7L/8 − a)² − (L − a)L/4 = (L²/16 + 2L(L/2 − a) + 4(L/2 − a)²)/4` has slack `L²/64 ≥ cL/4`
exactly then.  For `L = log log X → ∞` and `c = O(1)` this holds for all large `X`. -/
theorem seven_eighths_real_flat {a b m L c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ L + c) (hhalf : a ≤ L / 2) (hm : 0 ≤ m) (hmL : m ≤ L / 8)
    (hcL : c ≤ L / 16) :
    a + Real.sqrt (2 * b) * Real.sqrt m ≤ 7 / 8 * L := by
  have hL : 0 ≤ L := by linarith
  have hK : 0 ≤ 7 / 8 * L - a := by linarith
  have hquad : 2 * b * m ≤ (7 / 8 * L - a) ^ 2 := by
    have hbm : 2 * b * m ≤ (L - a) * L / 4 + c * L / 4 := by
      nlinarith [mul_nonneg hm (by linarith : (0 : ℝ) ≤ L + c - a - b),
        mul_nonneg (by linarith : (0 : ℝ) ≤ L + c - a) (by linarith : (0 : ℝ) ≤ L / 8 - m)]
    nlinarith [hbm, sq_nonneg L, sq_nonneg (L / 2 - a),
      mul_nonneg hL (by linarith : (0 : ℝ) ≤ L / 2 - a),
      mul_le_mul_of_nonneg_right hcL hL]
  linarith [sqrt_mul_sqrt_le hb hK hquad]

/-- **THE ⅞-BOUND (main form).**  Let `S` be a finite set of primes (positivity is all that is
used), `E ⊆ S` the exceptional set `{p : p ∈ ∪_{j∈𝒥}(P_j,Q_j]}`, and `u` a 1-bounded datum on
`S` (in MRT: `u(p) = f(p)p^{−it₁}`).  Write `T = ∑_{p∈S} 1/p` for the Mertens mass.  If

* `∑_{p∈E} 1/p ≤ T/2` (the page's `β ∈ [0, 1/2]`), and
* `∑_{p∈S} (1 − ℜu(p))/p ≤ T/8` (the page's `M(f;X) < (1/8) log log X`),

then
`(∑_{p∈E} 1/p) + ∑_{p∈S∖E} ‖1 − u(p)‖/p ≤ (7/8)·T`.

This is the page's display with `log log X` replaced by the true Mertens sum `T`; the printed
`O(√(log log X))` then vanishes identically (see `seven_eighths_bound_loglog` for the literal
form). -/
theorem seven_eighths_bound {S E : Finset ℕ} (u : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0 < p) (hu : ∀ p ∈ S, ‖u p‖ ≤ 1) (hES : E ⊆ S)
    (hbeta : ∑ p ∈ E, (1 : ℝ) / (p : ℝ) ≤ (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) / 2)
    (hM : ∑ p ∈ S, (1 - (u p).re) / (p : ℝ) ≤ (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) / 8) :
    (∑ p ∈ E, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ S \ E, ‖1 - u p‖ / (p : ℝ)
      ≤ 7 / 8 * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := by
  classical
  have hterm : ∀ p ∈ S, 0 ≤ (1 - (u p).re) / (p : ℝ) := fun p hp =>
    div_nonneg (by linarith [le_trans (Complex.re_le_norm (u p)) (hu p hp)]) (Nat.cast_nonneg p)
  have ha : (0 : ℝ) ≤ ∑ p ∈ E, (1 : ℝ) / (p : ℝ) := Finset.sum_nonneg fun p _ => by positivity
  have hb : (0 : ℝ) ≤ ∑ p ∈ S \ E, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hab : (∑ p ∈ E, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ S \ E, (1 : ℝ) / (p : ℝ)
      = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := by rw [add_comm]; exact Finset.sum_sdiff hES
  linarith [cs_reduction S E u hS hu,
    seven_eighths_real ha hb (le_of_eq hab) hbeta (Finset.sum_nonneg hterm) hM]

/-- **The ⅞-bound, `log log X`-normalised** — the page's display literally, with its
`O(√(log log X))` made explicit.  Here `L` plays `log log X` and `c ≥ 0` is any Mertens budget
with `∑_{p∈S} 1/p ≤ L + c` (`mertens_second_sharp`, `Salt/Mertens/Second.lean:216`, gives
`c = M + C/log X` at `S = {p ≤ X}`).  The conclusion is

`(∑_{p∈E} 1/p) + ∑_{p∈S∖E} ‖1 − u(p)‖/p ≤ (7/8)·L + (√c/2)·√L`,

the printed `β log log X + (√(1−β)/2) log log X + O(√(log log X)) ≤ (7/8) log log X`. -/
theorem seven_eighths_bound_loglog {S E : Finset ℕ} (u : ℕ → ℂ) (L c : ℝ)
    (hS : ∀ p ∈ S, 0 < p) (hu : ∀ p ∈ S, ‖u p‖ ≤ 1) (hES : E ⊆ S)
    (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hT : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ L + c)
    (hbeta : ∑ p ∈ E, (1 : ℝ) / (p : ℝ) ≤ L / 2)
    (hM : ∑ p ∈ S, (1 - (u p).re) / (p : ℝ) ≤ L / 8) :
    (∑ p ∈ E, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ S \ E, ‖1 - u p‖ / (p : ℝ)
      ≤ 7 / 8 * L + Real.sqrt c / 2 * Real.sqrt L := by
  classical
  have hterm : ∀ p ∈ S, 0 ≤ (1 - (u p).re) / (p : ℝ) := fun p hp =>
    div_nonneg (by linarith [le_trans (Complex.re_le_norm (u p)) (hu p hp)]) (Nat.cast_nonneg p)
  have hb : (0 : ℝ) ≤ ∑ p ∈ S \ E, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hab : (∑ p ∈ E, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ S \ E, (1 : ℝ) / (p : ℝ) ≤ L + c := by
    have hsum : (∑ p ∈ E, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ S \ E, (1 : ℝ) / (p : ℝ)
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := by rw [add_comm]; exact Finset.sum_sdiff hES
    linarith [hsum, hT]
  linarith [cs_reduction S E u hS hu,
    seven_eighths_real_loglog hb hab hbeta (Finset.sum_nonneg hterm) hM hL hc]

/-- **The ⅞-bound, the page's LITERAL claim**: `≤ (7/8) log log X`, flat, no error term.  Same
data as `seven_eighths_bound_loglog` plus `c ≤ L/16` — i.e. the Mertens budget is small against
`log log X`, which for `c = M + C/log X` holds for all large `X`.  This is the inequality MRT
then feed into `exp(·)` in Lemma A.7. -/
theorem seven_eighths_bound_flat {S E : Finset ℕ} (u : ℕ → ℂ) (L c : ℝ)
    (hS : ∀ p ∈ S, 0 < p) (hu : ∀ p ∈ S, ‖u p‖ ≤ 1) (hES : E ⊆ S)
    (hcL : c ≤ L / 16)
    (hT : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ L + c)
    (hbeta : ∑ p ∈ E, (1 : ℝ) / (p : ℝ) ≤ L / 2)
    (hM : ∑ p ∈ S, (1 - (u p).re) / (p : ℝ) ≤ L / 8) :
    (∑ p ∈ E, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ S \ E, ‖1 - u p‖ / (p : ℝ) ≤ 7 / 8 * L := by
  classical
  have hterm : ∀ p ∈ S, 0 ≤ (1 - (u p).re) / (p : ℝ) := fun p hp =>
    div_nonneg (by linarith [le_trans (Complex.re_le_norm (u p)) (hu p hp)]) (Nat.cast_nonneg p)
  have ha : (0 : ℝ) ≤ ∑ p ∈ E, (1 : ℝ) / (p : ℝ) := Finset.sum_nonneg fun p _ => by positivity
  have hb : (0 : ℝ) ≤ ∑ p ∈ S \ E, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hab : (∑ p ∈ E, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ S \ E, (1 : ℝ) / (p : ℝ) ≤ L + c := by
    have hsum : (∑ p ∈ E, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ S \ E, (1 : ℝ) / (p : ℝ)
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := by rw [add_comm]; exact Finset.sum_sdiff hES
    linarith [hsum, hT]
  linarith [cs_reduction S E u hS hu,
    seven_eighths_real_flat ha hb hab hbeta (Finset.sum_nonneg hterm) hM hcL]

/-! ## S4 — the MRT-consumption form (the single sum against `g_𝒥`) -/

/-- **The page's first display**, as an exact identity: for `g` the `{0,1}`-valued twist `g_𝒥`
(`g(p) = 0` on the exceptional set `E = {p ∈ ∪_{j∈𝒥}(P_j,Q_j]}`, `g(p) = 1` off it),

`∑_{p∈S} ‖1 − u(p)·g(p)‖/p = ∑_{p∈E} 1/p + ∑_{p∈S∖E} ‖1 − u(p)‖/p`.

Kept separate from the bound so it can be composed with any of the three ⅞-forms. -/
theorem sum_norm_one_sub_mul_split {S E : Finset ℕ} (u g : ℕ → ℂ) (hES : E ⊆ S)
    (hg0 : ∀ p ∈ E, g p = 0) (hg1 : ∀ p ∈ S \ E, g p = 1) :
    ∑ p ∈ S, ‖1 - u p * g p‖ / (p : ℝ)
      = (∑ p ∈ E, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ S \ E, ‖1 - u p‖ / (p : ℝ) := by
  classical
  have hsplit : (∑ p ∈ S \ E, ‖1 - u p * g p‖ / (p : ℝ))
      + ∑ p ∈ E, ‖1 - u p * g p‖ / (p : ℝ) = ∑ p ∈ S, ‖1 - u p * g p‖ / (p : ℝ) :=
    Finset.sum_sdiff hES
  have hE : ∑ p ∈ E, ‖1 - u p * g p‖ / (p : ℝ) = ∑ p ∈ E, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_congr rfl fun p hp => by rw [hg0 p hp, mul_zero, sub_zero, norm_one]
  have hoff : ∑ p ∈ S \ E, ‖1 - u p * g p‖ / (p : ℝ)
      = ∑ p ∈ S \ E, ‖1 - u p‖ / (p : ℝ) :=
    Finset.sum_congr rfl fun p hp => by rw [hg1 p hp, mul_one]
  rw [← hsplit, hE, hoff, add_comm]

/-- **The ⅞-bound in MRT's consumption shape.**  With `g` the `{0,1}`-valued twist `g_𝒥`
(`g(p) = 0` on the exceptional set `E`, `g(p) = 1` off it), the page's first display is the
split of `∑_{p∈S} ‖1 − u(p)g(p)‖/p`, and the device bounds the whole sum:

`∑_{p∈S} ‖1 − u(p)·g(p)‖/p ≤ (7/8)·∑_{p∈S} 1/p`.

Stated at a general 1-bounded `u` and a general `{0,1}`-valued `g`, so the
`u(p) = f(p)p^{−it₁}`, `g = g_𝒥` instantiation is free. -/
theorem seven_eighths_bound_indicator {S E : Finset ℕ} (u g : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0 < p) (hu : ∀ p ∈ S, ‖u p‖ ≤ 1) (hES : E ⊆ S)
    (hg0 : ∀ p ∈ E, g p = 0) (hg1 : ∀ p ∈ S \ E, g p = 1)
    (hbeta : ∑ p ∈ E, (1 : ℝ) / (p : ℝ) ≤ (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) / 2)
    (hM : ∑ p ∈ S, (1 - (u p).re) / (p : ℝ) ≤ (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) / 8) :
    ∑ p ∈ S, ‖1 - u p * g p‖ / (p : ℝ) ≤ 7 / 8 * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := by
  rw [sum_norm_one_sub_mul_split u g hES hg0 hg1]
  exact seven_eighths_bound u hS hu hES hbeta hM

/-- **The ⅞-bound at `S = {p ≤ x}`, with `M(f;X)` as `pretDistSq`** — the form Lemma A.7's
error term consumes.  `pretDistSq u 1 x = ∑_{p≤x} (1 − ℜu(p))/p` is our `M(f;X)` at
`u(p) = f(p)p^{−it₁}` (`Salt/MR/Dist.lean:59`); the exceptional set `E` is any subset of the
primes `≤ x`, so the `∪_{j∈𝒥}(P_j,Q_j]` instantiation is free. -/
theorem seven_eighths_bound_primes (x : ℝ) (u g : ℕ → ℂ) {E : Finset ℕ}
    (hu : ∀ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, ‖u p‖ ≤ 1)
    (hES : E ⊆ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime)
    (hg0 : ∀ p ∈ E, g p = 0)
    (hg1 : ∀ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime \ E, g p = 1)
    (hbeta : ∑ p ∈ E, (1 : ℝ) / (p : ℝ)
      ≤ (∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) / 2)
    (hM : pretDistSq u (fun _ => 1) x
      ≤ (∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) / 8) :
    ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, ‖1 - u p * g p‖ / (p : ℝ)
      ≤ 7 / 8 * ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
  have hMeq : pretDistSq u (fun _ => 1) x
      = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 - (u p).re) / (p : ℝ) := by
    unfold pretDistSq
    exact Finset.sum_congr rfl fun p _ => by rw [map_one, mul_one]
  rw [hMeq] at hM
  exact seven_eighths_bound_indicator u g
    (fun p hp => (Nat.Prime.pos (Finset.mem_filter.mp hp).2)) hu hES hg0 hg1 hbeta hM

end Salt.MR
