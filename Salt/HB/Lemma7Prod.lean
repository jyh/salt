/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Lemma7F
import Salt.Mertens.PrimePower

/-!
# HB 1983, Lemma 7 — node N4b, wave **W4**, part α: the product layer

Heath-Brown p.207.  W3 (`Salt/HB/Lemma7F.lean`) evaluated `log F` but had to carry the
*existence* of `F` as a free real together with the named binder `hcorr`, because the corpus
owned **no definition of the infinite Euler product**

    F  =  ∏_{p ≥ z} (1 − χ(p)/p)^{−1}                                        (HB p.207)

This file supplies it, and discharges the `hcorr` row.

## The route chosen (recorded, per the W4 brief's design freedom)

`F` is **not** a `tprod`.  Mathlib's `Multipliable` is unconditional (net) convergence, which for
this product is equivalent to the absolute convergence of `∑_{p ≥ z} |χ(p)|/p` — and that series
**diverges** (it is `∑_{p ≥ z, p ∤ q} 1/p`).  The Euler product over `p ≥ z` converges only
*conditionally*, in the ordered sense, so `∏'` is the mathematically wrong object here and no
amount of Lean effort would produce it.

Instead `F` is the **limit of the ordered partial products**, defined through its logarithm:

* `hbEulerLog χ z Y  = ∑_{z < p ≤ Y} −log(1 − χ(p)/p)`   (the finite log-product),
* `hbEulerProd χ z Y = ∏_{z < p ≤ Y} (1 − χ(p)/p)^{−1}`  (the finite product), with
  `Real.log (hbEulerProd χ z Y) = hbEulerLog χ z Y` proved (`log_hbEulerProd`),
* `hbLogF χ z := limUnder atTop (hbEulerLog χ z ·)` and `hbF χ z := Real.exp (hbLogF χ z)`.

So `log (hbF χ z) = hbLogF χ z` is definitional, `hbF χ z > 0` is free, and — the content —
`tendsto_hbEulerProd_hbF` shows that *whenever the log-products converge*, the partial **products**
converge to `hbF χ z`: `F` really is the Euler product, read in HB's own ordered sense.

## `hcorr`, discharged

HB's step 1 is `log F = ∑_{n ≥ z} χ(n)Λ(n)/(n log n) + O(z^{−1/2})`.  The two sides differ by the
`k ≥ 2` prime-power bookkeeping, and it splits cleanly:

* §2 (product side): `|−log(1 − x) − x| ≤ 2x²` at `|x| ≤ 1/2` (mathlib's
  `Real.abs_log_sub_add_sum_range_le` at `n = 1`), giving
  `|hbEulerLog χ z Y − ∑_{z<p≤Y} χ(p)/p| ≤ 2/⌊z⌋` (`hbEulerLog_sub_primeSum_le`);
* §3 (`Λ`-side): `(logChiSum χ z Y).re − ∑_{z<p≤Y} χ(p)/p` is bounded by the **prime-power
  defect** `ppDefect z Y = ∑_{z<n≤Y, n not prime} Λ(n)/(n log n)`, which is Chebyshev's `ψ − θ`
  read through the Abel weight `1/(t log t)` — bounded by `12/√z` in `ppDefect_le`.

Composing, `hb_hcorr` is HB's step 1 with `Ecorr = 2/⌊z⌋ + 12/√z`, and `hcorr` no longer rides.

## §4 — `hseg` (part β of the W4 brief)

`hb_hseg` is the `[z, X]` segment of `(4.7)`:
`|(logChiSum χ z X).re − (log log z − log log X)|` is bounded by Mertens' second theorem twice
(`mertens_second_sharp'`, whose Meissel–Mertens constant *cancels*), the prime-power defect above,
and the `p ∣ q` divisor-count correction `z₀/z` of hb1983-notes:451 — `at most z₀ = L/log z`
primes `p ∣ q` have `p ≥ z`, because `z^{#} ≤ ∏_{p ∣ q} p ≤ q`.
-/

open Complex DirichletCharacter ArithmeticFunction Filter Set MeasureTheory
open scoped Topology

namespace Salt.HB

/-! ## §0 — the window's primes, and `χ_ℝ` at the `TwinBar` namespace

W3's report records the trap: `chiRe` exists twice in the corpus (`Salt.SW.chiRe`,
`Salt.TwinBar.chiRe`), with identical definitions, and `PretenseSum` uses the **`TwinBar`** one.
W3 matched it; so does W4. -/

/-- `|χ_ℝ(n)| ≤ 1` at the `TwinBar` namespace (the `SW` proof, transported by definitional
equality — the two `chiRe`s are the same function). -/
lemma chiReTB_abs_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    |Salt.TwinBar.chiRe χ n| ≤ 1 :=
  Salt.SW.chiRe_abs_le_one χ n

/-- The primes of the window `(z, Y]`, as a `Finset`. -/
noncomputable def windowPrimes (z Y : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊).filter (fun n => Nat.Prime n)

lemma mem_windowPrimes {z Y : ℝ} {p : ℕ} :
    p ∈ windowPrimes z Y ↔ (⌊z⌋₊ < p ∧ p ≤ ⌊Y⌋₊) ∧ Nat.Prime p := by
  simp [windowPrimes, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

lemma windowPrimes_prime {z Y : ℝ} {p : ℕ} (hp : p ∈ windowPrimes z Y) : Nat.Prime p :=
  (mem_windowPrimes.mp hp).2

/-! ## §1 — the Euler product `F` as an object -/

/-- **The finite log-product** `∑_{z < p ≤ Y} −log(1 − χ(p)/p)`. -/
noncomputable def hbEulerLog {q : ℕ} (χ : DirichletCharacter ℂ q) (z Y : ℝ) : ℝ :=
  ∑ p ∈ windowPrimes z Y, -Real.log (1 - Salt.TwinBar.chiRe χ p / (p : ℝ))

/-- **The finite Euler product** `∏_{z < p ≤ Y} (1 − χ(p)/p)^{−1}`. -/
noncomputable def hbEulerProd {q : ℕ} (χ : DirichletCharacter ℂ q) (z Y : ℝ) : ℝ :=
  ∏ p ∈ windowPrimes z Y, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ))⁻¹

/-- Each Euler factor is `≥ 1/2 > 0`: `|χ_ℝ(p)| ≤ 1` and `p ≥ 2`. -/
lemma one_sub_chiRe_div_pos {q : ℕ} (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : Nat.Prime p) :
    (0 : ℝ) < 1 - Salt.TwinBar.chiRe χ p / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hc := abs_le.mp (chiReTB_abs_le_one χ p)
  have hdiv : Salt.TwinBar.chiRe χ p / (p : ℝ) ≤ 1 / (p : ℝ) := by gcongr; linarith
  have h1 : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff_of_pos_left one_pos (by linarith) (by norm_num)]; linarith
  linarith

/-- The finite Euler product is positive. -/
lemma hbEulerProd_pos {q : ℕ} (χ : DirichletCharacter ℂ q) (z Y : ℝ) :
    0 < hbEulerProd χ z Y :=
  Finset.prod_pos (fun _ hp => inv_pos.mpr (one_sub_chiRe_div_pos χ (windowPrimes_prime hp)))

/-- **`log` of the finite Euler product is the finite log-product.** -/
lemma log_hbEulerProd {q : ℕ} (χ : DirichletCharacter ℂ q) (z Y : ℝ) :
    Real.log (hbEulerProd χ z Y) = hbEulerLog χ z Y := by
  rw [hbEulerProd, hbEulerLog, Real.log_prod]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Real.log_inv]
  · intro p hp
    exact ne_of_gt (inv_pos.mpr (one_sub_chiRe_div_pos χ (windowPrimes_prime hp)))

/-- **`log F`** — the limit of the ordered partial log-products, HB's own convergence sense. -/
noncomputable def hbLogF {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) : ℝ :=
  limUnder Filter.atTop (fun Y : ℝ => hbEulerLog χ z Y)

/-- **`F = ∏_{p ≥ z}(1 − χ(p)/p)^{−1}`**, as a real number. -/
noncomputable def hbF {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) : ℝ :=
  Real.exp (hbLogF χ z)

@[simp] lemma hbF_pos {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) : 0 < hbF χ z :=
  Real.exp_pos _

@[simp] lemma log_hbF {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) :
    Real.log (hbF χ z) = hbLogF χ z := Real.log_exp _

/-- Identifying `log F` from any convergence proof of the partial log-products. -/
lemma hbLogF_eq_of_tendsto {q : ℕ} (χ : DirichletCharacter ℂ q) {z A : ℝ}
    (h : Tendsto (fun Y : ℝ => hbEulerLog χ z Y) atTop (𝓝 A)) : hbLogF χ z = A :=
  h.limUnder_eq

/-- **`F` really is the Euler product**: whenever the partial log-products converge, the partial
**products** converge to `hbF χ z`.  (This is the corollary the `exp`-of-series definition owes,
and it is paid here.) -/
lemma tendsto_hbEulerProd_hbF {q : ℕ} (χ : DirichletCharacter ℂ q) {z A : ℝ}
    (h : Tendsto (fun Y : ℝ => hbEulerLog χ z Y) atTop (𝓝 A)) :
    Tendsto (fun Y : ℝ => hbEulerProd χ z Y) atTop (𝓝 (hbF χ z)) := by
  have hlim : hbLogF χ z = A := hbLogF_eq_of_tendsto χ h
  have hexp : Tendsto (fun Y : ℝ => Real.exp (hbEulerLog χ z Y)) atTop (𝓝 (Real.exp A)) :=
    (Real.continuous_exp.tendsto A).comp h
  have hcongr : ∀ Y : ℝ, Real.exp (hbEulerLog χ z Y) = hbEulerProd χ z Y := by
    intro Y
    rw [← log_hbEulerProd χ z Y, Real.exp_log (hbEulerProd_pos χ z Y)]
  rw [hbF, hlim]
  exact hexp.congr hcongr

/-! ## §2 — the product side of HB's step 1: `−log(1 − x) = x + O(x²)` -/

/-- Mathlib's log-series remainder at `n = 1`, in the form W4 uses:
`|−log(1 − x) − x| ≤ 2x²` whenever `|x| ≤ 1/2`. -/
lemma abs_neg_log_one_sub_sub_self_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |(-Real.log (1 - x)) - x| ≤ 2 * x ^ 2 := by
  have hx1 : |x| < 1 := lt_of_le_of_lt hx (by norm_num)
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  rw [Finset.sum_range_one] at h
  have hsimp : x ^ (0 + 1) / ((0 : ℕ) + 1) = x := by norm_num
  rw [hsimp] at h
  have heq : (-Real.log (1 - x)) - x = -(x + Real.log (1 - x)) := by ring
  rw [heq, abs_neg]
  refine le_trans h ?_
  have hden : (1 : ℝ) / 2 ≤ 1 - |x| := by linarith
  have hnum : |x| ^ (1 + 1) = x ^ 2 := by
    rw [show (1 : ℕ) + 1 = 2 from rfl, ← abs_pow, abs_of_nonneg (sq_nonneg x)]
  rw [hnum]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg x]

/-- **The product side of HB's step 1.**  Termwise, the Euler log-product differs from
`∑_{z<p≤Y} χ(p)/p` by at most `∑ 2/p²`. -/
lemma hbEulerLog_sub_primeSum_termwise {q : ℕ} (χ : DirichletCharacter ℂ q) (z Y : ℝ) :
    |hbEulerLog χ z Y - ∑ p ∈ windowPrimes z Y, Salt.TwinBar.chiRe χ p / (p : ℝ)|
      ≤ ∑ p ∈ windowPrimes z Y, 2 / (p : ℝ) ^ 2 := by
  rw [hbEulerLog, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun p hp => ?_))
  have hpr := windowPrimes_prime hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hc := chiReTB_abs_le_one χ p
  have hxabs : |Salt.TwinBar.chiRe χ p / (p : ℝ)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hp0]
    rw [div_le_div_iff₀ hp0 (by norm_num)]
    linarith
  refine le_trans (abs_neg_log_one_sub_sub_self_le hxabs) ?_
  have hsq : (Salt.TwinBar.chiRe χ p / (p : ℝ)) ^ 2 ≤ 1 / (p : ℝ) ^ 2 := by
    have hc2 : Salt.TwinBar.chiRe χ p ^ 2 ≤ 1 := by nlinarith [abs_le.mp hc]
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((p : ℝ))]
  calc 2 * (Salt.TwinBar.chiRe χ p / (p : ℝ)) ^ 2 ≤ 2 * (1 / (p : ℝ) ^ 2) := by linarith
    _ = 2 / (p : ℝ) ^ 2 := by ring

/-- `∑_{z<p≤Y} 2/p² ≤ 2/⌊z⌋`, by comparison with all integers and mathlib's telescoping
`Finset.sum_Ioc_inv_sq_le_sub`. -/
lemma sum_two_div_sq_windowPrimes_le {z Y : ℝ} (hz : 1 ≤ z) :
    ∑ p ∈ windowPrimes z Y, 2 / (p : ℝ) ^ 2 ≤ 2 / (⌊z⌋₊ : ℝ) := by
  classical
  have hzf : 1 ≤ ⌊z⌋₊ := (Nat.one_le_floor_iff z).mpr hz
  have hzf0 : (0 : ℝ) < (⌊z⌋₊ : ℝ) := by exact_mod_cast hzf
  have hsub : ∑ p ∈ windowPrimes z Y, 2 / (p : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, 2 / (n : ℝ) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  refine le_trans hsub ?_
  rcases le_or_gt ⌊z⌋₊ ⌊Y⌋₊ with hle | hgt
  · have hkey := _root_.sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : ⌊z⌋₊ ≠ 0) hle
    have hrw : ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, 2 / (n : ℝ) ^ 2
        = 2 * ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, (((n : ℝ)) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by rw [div_eq_mul_inv, mul_comm])
    rw [hrw]
    have hYinv : (0 : ℝ) ≤ ((⌊Y⌋₊ : ℝ))⁻¹ := by positivity
    have : 2 * ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, (((n : ℝ)) ^ 2)⁻¹
        ≤ 2 * (((⌊z⌋₊ : ℝ))⁻¹ - ((⌊Y⌋₊ : ℝ))⁻¹) := by linarith
    rw [div_eq_mul_inv]
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity

/-! ## §3 — the `Λ` side: the prime-power defect -/

/-- **The prime-power defect** `∑_{z<n≤Y, n not prime} Λ(n)/(n log n)` — the `k ≥ 2` half of
HB's step 1 (p.207), and the same object the `[z,X]` segment (§4) has to discard.  It is
Chebyshev's `ψ − θ` read through the Abel weight `w(t) = 1/(t log t)`. -/
noncomputable def ppDefect (z Y : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊).filter (fun n => ¬ Nat.Prime n), wLog n * vonMangoldt n

lemma ppDefect_nonneg {z Y : ℝ} (hz : 1 ≤ z) : 0 ≤ ppDefect z Y := by
  classical
  refine Finset.sum_nonneg (fun n hn => ?_)
  rw [Finset.mem_filter, Finset.mem_Ioc] at hn
  have hzf : 1 ≤ ⌊z⌋₊ := (Nat.one_le_floor_iff z).mpr hz
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  exact mul_nonneg (wLog_nonneg hn1) vonMangoldt_nonneg

/-- For a real character the log-weighted window sum is the real sum `∑ w(n)Λ(n)χ_ℝ(n)`. -/
lemma logChiSum_re_eq_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z Y : ℝ) :
    (logChiSum χ z Y).re
      = ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, wLog n * vonMangoldt n * Salt.TwinBar.chiRe χ n := by
  rw [logChiSum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [chi_eq_ofReal_chiRe χ hsq n, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- **The `Λ` side of HB's step 1.**  The `Λ`-series over the window differs from the prime
series `∑_{z<p≤Y} χ(p)/p` by at most the prime-power defect: on a prime `p` the weight collapses
(`w(p)Λ(p) = 1/p`), and everything else is charged to `ppDefect`. -/
lemma logChiSum_re_sub_primeSum_le {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {z Y : ℝ} (hz : 1 ≤ z) :
    |(logChiSum χ z Y).re - ∑ p ∈ windowPrimes z Y, Salt.TwinBar.chiRe χ p / (p : ℝ)|
      ≤ ppDefect z Y := by
  classical
  have hzf : 1 ≤ ⌊z⌋₊ := (Nat.one_le_floor_iff z).mpr hz
  rw [logChiSum_re_eq_sum χ hsq z Y]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊) (fun n => Nat.Prime n)]
  -- the prime half is exactly the prime series
  have hprime : ∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊).filter (fun n => Nat.Prime n),
        wLog n * vonMangoldt n * Salt.TwinBar.chiRe χ n
      = ∑ p ∈ windowPrimes z Y, Salt.TwinBar.chiRe χ p / (p : ℝ) := by
    rw [windowPrimes]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hpr : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
    have hlogp : (0 : ℝ) < Real.log p := Real.log_pos (by linarith)
    rw [wLog, vonMangoldt_apply_prime hpr]
    field_simp
  rw [hprime, add_sub_cancel_left]
  -- the non-prime half is bounded by the defect
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [ppDefect]
  refine Finset.sum_le_sum (fun n hn => ?_)
  rw [Finset.mem_filter, Finset.mem_Ioc] at hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hw : 0 ≤ wLog n := wLog_nonneg hn1
  have hL : 0 ≤ (vonMangoldt n : ℝ) := vonMangoldt_nonneg
  rw [abs_mul, abs_of_nonneg (mul_nonneg hw hL)]
  have hc := chiReTB_abs_le_one χ n
  nlinarith [mul_nonneg hw hL]

end Salt.HB
