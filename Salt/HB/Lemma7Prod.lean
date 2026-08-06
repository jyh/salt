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

/-- `log 3 > 1`. -/
lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he

/-- The `⌊·⌋ → ℝ` bridge for the iterated logarithm: `|log log z − log log ⌊z⌋| ≤ 1/log z`
for `z ≥ 3`.  (`log z − log⌊z⌋ ≤ 1/⌊z⌋` by `log x ≤ x − 1`, then the same step again, then
`log z ≤ z − 1 < ⌊z⌋`.) -/
lemma abs_log_log_floor_sub_le {z : ℝ} (hz : 3 ≤ z) :
    |Real.log (Real.log z) - Real.log (Real.log (⌊z⌋₊ : ℝ))| ≤ 1 / Real.log z := by
  have hn3 : 3 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have hnR : (3 : ℝ) ≤ (⌊z⌋₊ : ℝ) := by exact_mod_cast hn3
  have hnz : ((⌊z⌋₊ : ℕ) : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hzn : z < (⌊z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z
  have hn0 : (0 : ℝ) < (⌊z⌋₊ : ℝ) := by linarith
  have hz0 : (0 : ℝ) < z := by linarith
  -- `log 3 > 1`
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
  have hlogn1 : (1 : ℝ) < Real.log (⌊z⌋₊ : ℝ) :=
    lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hnR)
  have hlogz1 : (1 : ℝ) < Real.log z := lt_of_lt_of_le hlogn1 (Real.log_le_log hn0 hnz)
  have hlogle : Real.log (⌊z⌋₊ : ℝ) ≤ Real.log z := Real.log_le_log hn0 hnz
  -- step 1: `log z − log ⌊z⌋ ≤ 1/⌊z⌋`
  have hstep1 : Real.log z - Real.log (⌊z⌋₊ : ℝ) ≤ 1 / (⌊z⌋₊ : ℝ) := by
    have hdiv : Real.log (z / (⌊z⌋₊ : ℝ)) ≤ z / (⌊z⌋₊ : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt hz0) (ne_of_gt hn0)] at hdiv
    have hq : z / (⌊z⌋₊ : ℝ) - 1 ≤ 1 / (⌊z⌋₊ : ℝ) := by
      rw [div_sub_one (ne_of_gt hn0), div_le_div_iff_of_pos_right hn0]
      linarith
    linarith
  -- step 2: the same for the iterated log
  have hstep2 : Real.log (Real.log z) - Real.log (Real.log (⌊z⌋₊ : ℝ))
      ≤ 1 / (⌊z⌋₊ : ℝ) := by
    have hdiv : Real.log (Real.log z / Real.log (⌊z⌋₊ : ℝ))
        ≤ Real.log z / Real.log (⌊z⌋₊ : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by linarith) (by linarith)] at hdiv
    have hq : Real.log z / Real.log (⌊z⌋₊ : ℝ) - 1 ≤ 1 / (⌊z⌋₊ : ℝ) := by
      rw [div_sub_one (by linarith), div_le_div_iff₀ (by linarith) hn0]
      have hle : Real.log z - Real.log (⌊z⌋₊ : ℝ) ≤ 1 / (⌊z⌋₊ : ℝ) := hstep1
      have h1 : (Real.log z - Real.log (⌊z⌋₊ : ℝ)) * (⌊z⌋₊ : ℝ) ≤ 1 := by
        rw [← le_div_iff₀ hn0]
        simpa [one_div] using hle
      nlinarith
    linarith
  -- `1/⌊z⌋ ≤ 1/log z` since `log z ≤ z − 1 < ⌊z⌋`
  have hcmp : 1 / (⌊z⌋₊ : ℝ) ≤ 1 / Real.log z := by
    have hlz : Real.log z ≤ z - 1 := Real.log_le_sub_one_of_pos hz0
    have : Real.log z ≤ (⌊z⌋₊ : ℝ) := by linarith
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) this
  have hnonneg : 0 ≤ Real.log (Real.log z) - Real.log (Real.log (⌊z⌋₊ : ℝ)) := by
    have := Real.log_le_log (by linarith) hlogle
    linarith
  rw [abs_of_nonneg hnonneg]
  linarith

/-- `log z ≤ 2 log ⌊z⌋` for `z ≥ 3` (i.e. `z ≤ ⌊z⌋²`) — the price of the `⌊·⌋ → ℝ`
re-indexing on every `C/log n` error. -/
lemma log_le_two_mul_log_floor {z : ℝ} (hz : 3 ≤ z) :
    Real.log z ≤ 2 * Real.log (⌊z⌋₊ : ℝ) := by
  have hn3 : 3 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have hnR : (3 : ℝ) ≤ (⌊z⌋₊ : ℝ) := by exact_mod_cast hn3
  have hzn : z < (⌊z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z
  have hsq : z ≤ (⌊z⌋₊ : ℝ) ^ 2 := by nlinarith
  have := Real.log_le_log (by linarith) hsq
  rwa [Real.log_pow, Nat.cast_ofNat] at this

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

/-! ## §4 — part β: the coprime half of the segment (HB `(4.7)`) -/

/-- The prime reciprocal sum up to `m`, in the shape `mertens_second_sharp'` delivers it. -/
noncomputable def primeRecipUpto (m : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (m + 1)).filter Nat.Prime, (1 : ℝ) / p

/-- The window's prime reciprocal sum telescopes off `primeRecipUpto`. -/
lemma sum_recip_windowPrimes_eq {z Y : ℝ} (h : ⌊z⌋₊ ≤ ⌊Y⌋₊) :
    ∑ p ∈ windowPrimes z Y, (1 : ℝ) / p = primeRecipUpto ⌊Y⌋₊ - primeRecipUpto ⌊z⌋₊ := by
  classical
  have hrange : ∀ m : ℕ, primeRecipUpto m
      = ∑ p ∈ Finset.Ioc 0 m, (if Nat.Prime p then (1 : ℝ) / p else 0) := by
    intro m
    rw [primeRecipUpto, Finset.sum_filter]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro p hp
      rw [Finset.mem_Ioc] at hp
      rw [Finset.mem_range]; omega
    · intro p hp hp'
      rw [Finset.mem_range] at hp
      rw [Finset.mem_Ioc] at hp'
      have : p = 0 := by omega
      subst this
      simp
  have hwin : ∑ p ∈ windowPrimes z Y, (1 : ℝ) / p
      = ∑ p ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, (if Nat.Prime p then (1 : ℝ) / p else 0) := by
    rw [windowPrimes, Finset.sum_filter]
  rw [hwin, hrange, hrange,
    ← Finset.sum_Ioc_consecutive (fun p => if Nat.Prime p then (1 : ℝ) / p else 0)
      (Nat.zero_le ⌊z⌋₊) h]
  ring

/-- **The `p ∣ q` divisor-count row** (hb1983-notes:451): at most `z₀ = L/log z` primes
dividing `q` are `> ⌊z⌋`, because `z^{#} < ∏_{p ∣ q} p ≤ q`.  Hence their reciprocals sum to
at most `z₀/z`. -/
lemma sum_recip_largePrimeFactors_le {q : ℕ} (hq : 0 < q) {z : ℝ} (hz : 3 ≤ z)
    (_hqz : (q : ℝ) ≠ 0) :
    ∑ p ∈ q.primeFactors.filter (fun p => ⌊z⌋₊ < p), (1 : ℝ) / p
      ≤ (Real.log q / Real.log z) / z := by
  classical
  set T := q.primeFactors.filter (fun p => ⌊z⌋₊ < p) with hT
  have hz0 : (0 : ℝ) < z := by linarith
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have hmem : ∀ p ∈ T, z < (p : ℝ) := by
    intro p hp
    rw [hT, Finset.mem_filter] at hp
    have h1 : (⌊z⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hp.2
    have h2 : z < (⌊z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z
    linarith
  -- the count bound: `z^{|T|} ≤ ∏_{p ∈ T} p ≤ q`
  have hprodT : (∏ p ∈ T, (p : ℝ)) ≤ (q : ℝ) := by
    have hdvd : (∏ p ∈ T, p) ∣ q := by
      refine dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)) ?_
      exact Nat.prod_primeFactors_dvd q
    have hle : (∏ p ∈ T, p) ≤ q := Nat.le_of_dvd hq hdvd
    have : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
    rwa [Nat.cast_prod] at this
  have hzpow : z ^ T.card ≤ ∏ p ∈ T, (p : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun p _ => by linarith) (fun p hp => (hmem p hp).le)
  have hcard : (T.card : ℝ) * Real.log z ≤ Real.log q := by
    have h1 : z ^ T.card ≤ (q : ℝ) := le_trans hzpow hprodT
    have h2 : Real.log (z ^ T.card) ≤ Real.log q :=
      Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at h2
  -- each reciprocal is `≤ 1/z`
  have hterm : ∀ p ∈ T, (1 : ℝ) / p ≤ 1 / z := by
    intro p hp
    exact div_le_div_of_nonneg_left (by norm_num) hz0 (hmem p hp).le
  calc ∑ p ∈ T, (1 : ℝ) / p ≤ ∑ _p ∈ T, (1 : ℝ) / z := Finset.sum_le_sum hterm
    _ = (T.card : ℝ) * (1 / z) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Real.log q / Real.log z) / z := by
        rw [mul_one_div, div_le_div_iff_of_pos_right hz0, le_div_iff₀ hlogz]
        linarith

/-- **PART β — the coprime half of HB's `(4.7)` segment.**  For `3 ≤ z ≤ X` and `q ≥ 1`,

    ∑_{z<n≤X, (n,q)=1} Λ(n)/(n log n)
        = log log X − log log z + O( ppDefect(z,X) + C/log z + (L/log z)/z ),

`L = log q`.  The main term is Mertens' second theorem fired twice — the Meissel–Mertens
constant `γ − B` **cancels** — the `⌊·⌋ → ℝ` re-indexing costs the factor `2` on `C` plus
`2/log z`, and the `p ∣ q` correction is the divisor-count row `z₀/z` of hb1983-notes:451.
The prime-power bookkeeping is the single object `ppDefect`. -/
theorem hb_coprime_segment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ), 0 < q → ∀ {z X : ℝ}, 3 ≤ z → z ≤ X →
      |(∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Coprime n q),
            wLog n * vonMangoldt n)
          - (Real.log (Real.log X) - Real.log (Real.log z))|
        ≤ ppDefect z X + C / Real.log z + (Real.log q / Real.log z) / z := by
  classical
  obtain ⟨C₀, hC₀, hM⟩ := Salt.Mertens.mertens_second_sharp'
  refine ⟨4 * C₀ + 2, by linarith, fun q hq z X hz hzX => ?_⟩
  have hX3 : (3 : ℝ) ≤ X := le_trans hz hzX
  have hzf3 : 3 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have hXf3 : 3 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX3)
  have hfle : ⌊z⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor hzX
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos (by linarith)
  have hlogzX : Real.log z ≤ Real.log X := Real.log_le_log (by linarith) hzX
  have hlogzf : (1 : ℝ) < Real.log (⌊z⌋₊ : ℝ) := by
    refine lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) ?_)
    exact_mod_cast hzf3
  have hlogXf : (1 : ℝ) < Real.log (⌊X⌋₊ : ℝ) := by
    refine lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) ?_)
    exact_mod_cast hXf3
  set S : ℝ := ∑ p ∈ windowPrimes z X, (1 : ℝ) / p with hSdef
  set D : ℝ := ∑ p ∈ windowPrimes z X with ¬ Nat.Coprime p q, (1 : ℝ) / p with hDdef
  set B : ℝ := ∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Coprime n q),
      wLog n * vonMangoldt n with hBdef
  -- (i) `B` versus the coprime prime sum
  have hBP : |B - (S - D)| ≤ ppDefect z X := by
    have hsplit : B = (∑ n ∈ ((Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Coprime n q)).filter
            (fun n => Nat.Prime n), wLog n * vonMangoldt n)
        + ∑ n ∈ ((Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Coprime n q)).filter
            (fun n => ¬ Nat.Prime n), wLog n * vonMangoldt n :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hset : ((Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Coprime n q)).filter
          (fun n => Nat.Prime n)
        = (windowPrimes z X).filter (fun p => Nat.Coprime p q) := by
      ext n
      simp only [Finset.mem_filter, mem_windowPrimes, Finset.mem_Ioc]
      tauto
    have hpr : (∑ n ∈ ((Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Coprime n q)).filter
            (fun n => Nat.Prime n), wLog n * vonMangoldt n) = S - D := by
      have hSD : S - D = ∑ p ∈ windowPrimes z X with Nat.Coprime p q, (1 : ℝ) / p := by
        rw [hSdef, hDdef, ← Finset.sum_filter_add_sum_filter_not (windowPrimes z X)
          (fun p => Nat.Coprime p q)]
        ring
      rw [hSD, hset]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Finset.mem_filter, mem_windowPrimes] at hn
      have hpr : Nat.Prime n := hn.1.2
      have hp2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpr.two_le
      have hlogp : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
      rw [wLog, vonMangoldt_apply_prime hpr]
      field_simp
    rw [hsplit, hpr, add_sub_cancel_left]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have habs : ∑ n ∈ ((Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Coprime n q)).filter
          (fun n => ¬ Nat.Prime n), |wLog n * vonMangoldt n|
        = ∑ n ∈ ((Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Coprime n q)).filter
          (fun n => ¬ Nat.Prime n), wLog n * vonMangoldt n := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      exact abs_of_nonneg (mul_nonneg (wLog_nonneg hn1) vonMangoldt_nonneg)
    rw [habs, ppDefect]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n hn _ => ?_)
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
      exact ⟨hn.1.1, hn.2⟩
    · simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      exact mul_nonneg (wLog_nonneg hn1) vonMangoldt_nonneg
  -- (ii) `D ≥ 0` and `D ≤ (log q / log z)/z`
  have hD0 : 0 ≤ D := by
    refine Finset.sum_nonneg (fun p _ => by positivity)
  have hDle : D ≤ (Real.log q / Real.log z) / z := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity))
      (sum_recip_largePrimeFactors_le hq hz (by positivity))
    intro p hp
    rw [Finset.mem_filter, mem_windowPrimes] at hp
    obtain ⟨⟨⟨hlo, _⟩, hpr⟩, hnc⟩ := hp
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    have hdvd : p ∣ q := by
      by_contra hnd
      exact hnc ((Nat.Prime.coprime_iff_not_dvd hpr).mpr hnd)
    exact ⟨⟨hpr, hdvd, by omega⟩, hlo⟩
  -- (iii) `S` versus `log log X − log log z`
  have hSm : |S - (Real.log (Real.log X) - Real.log (Real.log z))|
      ≤ (4 * C₀ + 2) / Real.log z := by
    have hSeq : S = primeRecipUpto ⌊X⌋₊ - primeRecipUpto ⌊z⌋₊ :=
      sum_recip_windowPrimes_eq hfle
    have hMX := hM ⌊X⌋₊ (by omega)
    have hMz := hM ⌊z⌋₊ (by omega)
    rw [← primeRecipUpto] at hMX hMz
    have hbz := abs_log_log_floor_sub_le hz
    have hbX := abs_log_log_floor_sub_le hX3
    -- the `C₀/log⌊·⌋ ≤ 2C₀/log ·` prices
    have hpz : C₀ / Real.log (⌊z⌋₊ : ℝ) ≤ 2 * C₀ / Real.log z := by
      rw [div_le_div_iff₀ (by linarith) hlogz]
      nlinarith [log_le_two_mul_log_floor hz]
    have hpX : C₀ / Real.log (⌊X⌋₊ : ℝ) ≤ 2 * C₀ / Real.log X := by
      rw [div_le_div_iff₀ (by linarith) hlogX]
      nlinarith [log_le_two_mul_log_floor hX3]
    have hmono : ∀ a : ℝ, 0 ≤ a → a / Real.log X ≤ a / Real.log z := by
      intro a ha
      exact div_le_div_of_nonneg_left ha hlogz hlogzX
    have hstep : |S - (Real.log (Real.log X) - Real.log (Real.log z))|
        ≤ C₀ / Real.log (⌊X⌋₊ : ℝ) + C₀ / Real.log (⌊z⌋₊ : ℝ)
          + 1 / Real.log X + 1 / Real.log z := by
      rw [hSeq]
      have habs := abs_le.mp hMX
      have habs' := abs_le.mp hMz
      have hbz' := abs_le.mp hbz
      have hbX' := abs_le.mp hbX
      rw [abs_le]
      constructor <;> linarith
    refine le_trans hstep ?_
    have h1 := hmono (2 * C₀) (by linarith)
    have h2 := hmono 1 (by norm_num)
    have : (4 * C₀ + 2) / Real.log z
        = 2 * C₀ / Real.log z + 2 * C₀ / Real.log z + 1 / Real.log z + 1 / Real.log z := by
      field_simp; ring
    linarith
  -- compose
  have hfin : B - (Real.log (Real.log X) - Real.log (Real.log z))
      = (B - (S - D)) + (S - (Real.log (Real.log X) - Real.log (Real.log z))) - D := by ring
  rw [hfin]
  have h1 := abs_le.mp hBP
  have h2 := abs_le.mp hSm
  rw [abs_le]
  constructor <;> linarith

/-- **`hseg` — W3's second residue row, discharged.**  Splitting `(4.7)` by the detector
identity (`logChiSum_re_eq`), the `χ_ℝ = 1` half rides as HB's own quantity (killed by W3's
`hb_chiOne_kill_at_window`) and everything else is the part-β estimate above:

    |∑_{z<n≤X} χΛ/(n log n) − (log log z − log log X)|
        ≤ 2·∑_{z<p≤X, χ_ℝ(p)=1} Λ/(p log p) + 3·ppDefect(z,X) + C/log z + (L/log z)/z. -/
theorem hb_hseg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (_hq : 0 < q) {z X : ℝ} (hz : 3 ≤ z) (_hzX : z ≤ X) {C : ℝ}
    (hC : |(∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Coprime n q),
            wLog n * vonMangoldt n)
          - (Real.log (Real.log X) - Real.log (Real.log z))|
        ≤ ppDefect z X + C / Real.log z + (Real.log q / Real.log z) / z) :
    |(logChiSum χ z X).re - (Real.log (Real.log z) - Real.log (Real.log X))|
      ≤ 2 * (∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter
              (fun n => Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1), wLog n * vonMangoldt n)
        + 3 * ppDefect z X + C / Real.log z + (Real.log q / Real.log z) / z := by
  classical
  have hzf : 1 ≤ ⌊z⌋₊ := (Nat.one_le_floor_iff z).mpr (by linarith)
  set A : ℝ := ∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter
      (fun n => Salt.TwinBar.chiRe χ n = 1), wLog n * vonMangoldt n with hAdef
  set Ap : ℝ := ∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter
      (fun n => Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1), wLog n * vonMangoldt n with hApdef
  set B : ℝ := ∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Coprime n q),
      wLog n * vonMangoldt n with hBdef
  have hterm_nonneg : ∀ n ∈ Finset.Ioc ⌊z⌋₊ ⌊X⌋₊, 0 ≤ wLog n * vonMangoldt n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    exact mul_nonneg (wLog_nonneg hn1) vonMangoldt_nonneg
  -- `A ≥ 0` and `A ≤ Ap + ppDefect`
  have hA0 : 0 ≤ A := by
    refine Finset.sum_nonneg (fun n hn => hterm_nonneg n (Finset.mem_filter.mp hn).1)
  have hAle : A ≤ Ap + ppDefect z X := by
    have hsplit : A = (∑ n ∈ ((Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter
            (fun n => Salt.TwinBar.chiRe χ n = 1)).filter (fun n => Nat.Prime n),
            wLog n * vonMangoldt n)
        + ∑ n ∈ ((Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter
            (fun n => Salt.TwinBar.chiRe χ n = 1)).filter (fun n => ¬ Nat.Prime n),
            wLog n * vonMangoldt n :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hset1 : ((Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Salt.TwinBar.chiRe χ n = 1)).filter
          (fun n => Nat.Prime n)
        = (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter
            (fun n => Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1) := by
      ext n; simp only [Finset.mem_filter]; tauto
    have hrest : ∑ n ∈ ((Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter
          (fun n => Salt.TwinBar.chiRe χ n = 1)).filter (fun n => ¬ Nat.Prime n),
          wLog n * vonMangoldt n ≤ ppDefect z X := by
      rw [ppDefect]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n hn _ => ?_)
      · intro n hn
        simp only [Finset.mem_filter] at hn ⊢
        exact ⟨hn.1.1, hn.2⟩
      · exact hterm_nonneg n (Finset.mem_filter.mp hn).1
    rw [hsplit, hset1, ← hApdef]
    linarith
  -- the detector split
  have hsplit := logChiSum_re_eq χ hsq z X
  rw [← hAdef, ← hBdef] at hsplit
  have hBabs := abs_le.mp hC
  have hppd : 0 ≤ ppDefect z X := ppDefect_nonneg (by linarith)
  have hAp0 : 0 ≤ Ap := by
    refine Finset.sum_nonneg (fun n hn => hterm_nonneg n (Finset.mem_filter.mp hn).1)
  rw [hsplit, abs_le]
  constructor <;> linarith

/-! ## §5 — `hcorr`: HB's step 1, at finite `Y` and in the limit -/

/-- **`hcorr` at finite `Y`.**  The Euler log-product and the `Λ`-series differ by the two
bookkeeping halves only:

    |log ∏_{z<p≤Y}(1−χ(p)/p)^{−1} − ∑_{z<n≤Y} χ(n)Λ(n)/(n log n)| ≤ 2/⌊z⌋ + ppDefect(z,Y). -/
theorem hb_hcorr_finite {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {z Y : ℝ} (hz : 1 ≤ z) :
    |hbEulerLog χ z Y - (logChiSum χ z Y).re| ≤ 2 / (⌊z⌋₊ : ℝ) + ppDefect z Y := by
  set P : ℝ := ∑ p ∈ windowPrimes z Y, Salt.TwinBar.chiRe χ p / (p : ℝ) with hP
  have h1 : |hbEulerLog χ z Y - P| ≤ 2 / (⌊z⌋₊ : ℝ) :=
    le_trans (hbEulerLog_sub_primeSum_termwise χ z Y) (sum_two_div_sq_windowPrimes_le hz)
  have h2 : |(logChiSum χ z Y).re - P| ≤ ppDefect z Y :=
    logChiSum_re_sub_primeSum_le χ hsq hz
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith

/-- **`hcorr` in the limit** — the shape W3's `hb_logF_at_split_point` consumes.  Given a
uniform bound `E` on the prime-power defect and the convergence of both sides, `log F` sits
within `2/⌊z⌋ + E` of the `Λ`-series' limit. -/
theorem hb_hcorr_at_limit {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {z A A' E : ℝ} (hz : 1 ≤ z)
    (hE : ∀ Y : ℝ, ppDefect z Y ≤ E)
    (hlimP : Tendsto (fun Y : ℝ => hbEulerLog χ z Y) atTop (𝓝 A))
    (hlimS : Tendsto (fun Y : ℝ => (logChiSum χ z Y).re) atTop (𝓝 A')) :
    |Real.log (hbF χ z) - A'| ≤ 2 / (⌊z⌋₊ : ℝ) + E := by
  have hlogF : Real.log (hbF χ z) = A := by
    rw [log_hbF]; exact hbLogF_eq_of_tendsto χ hlimP
  rw [hlogF]
  have hdiff : Tendsto (fun Y : ℝ => |hbEulerLog χ z Y - (logChiSum χ z Y).re|)
      atTop (𝓝 |A - A'|) := (hlimP.sub hlimS).abs
  refine le_of_tendsto hdiff (Filter.Eventually.of_forall (fun Y => ?_))
  exact le_trans (hb_hcorr_finite χ hsq hz) (by linarith [hE Y])

end Salt.HB
