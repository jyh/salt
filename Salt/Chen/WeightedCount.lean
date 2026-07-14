/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.TripleCount
import Salt.Chen.SwitchConstant

/-!
# The Chen rung, node CNT2 — the c̄-WEIGHTED triple-prime count

Design: catch #53 (`docs/blueprints/flags.md`, "THE SW-FIBER DESIGN BLOCK
RESOLVED").  The landed C3d count (`Salt.Chen.triple_count_le`) bounds the inner
`p₃`-count by a UNIFORM `1/log L` floor (`lam = log⌊x/(2y√x)⌋ ≈ 6/log x`), which
over-counts the true varying weight `1/log(N/p₁p₂)` by the factor `~3.3` that the
catch-#49 recon trace surfaced as the "×7".  BJS Lemma 52 (pp. 57–58) keeps the
`log(N/p₁p₂)` weight and rides it through two Abel passes to the switch constant

  `c̄ = ∫_{1/8}^{1/3} log(2 − 3β)/(β(1 − β)) dβ < 0.363084`  (`Salt.Chen.cbar`).

## The honest numeric budget (threading the ½-window)

Our `tripleSet` fixes `prod ∈ [x/2, x]`, i.e. `p₃ ∈ (L, U]` with
`U = ⌊x/(p₁p₂)⌋`, `L = ⌊x/(2p₁p₂)⌋`, `U − L ≈ x/(2p₁p₂)`.  The interval mass over
`(L, U]` has length `x/(2p₁p₂)`, so the ½ is GENUINE and we keep it (BJS bounds
the full `π(U)`; our window is strictly smaller — extra margin).  Since `L` is
large (`L ≥ ⌊x/(2y√x)⌋`, so `log L ≥ log(N/p₁p₂) − 2log 2`), the sharp landed
interval count `prime_count_Ioc_le` already gives the `(1+o(1))` constant with the
`log(N/p₁p₂)` denominator — NO separate Rosser–Schoenfeld `π`-upper is needed
(mathlib's Chebyshev `2·log 4 ≈ 2.77` would blow the c̄ budget by ×2.77):

  `#{p₃ ∈ (L,U]} ≤ (1 + 3K/log L)(1 + W₀)·(x/2)·1/(p₁p₂·log(N/p₁p₂)) + 1/log L`,

with the double sum `Σ_{p₁,p₂} 1/(p₁p₂·log(N/p₁p₂)) → (c̄ + slack)/log x` by the
two Abel passes (BJS Lemma 20).  Hence

  `tripleSum ≤ (1 + o(1))·(c̄/2)·x/log x ≤ (1 + o(1))·0.1815·x/log x`.

Honest window factor: `c̄/2 ≈ 0.1815` (½ threaded), vs the full-`π(U)` route's `c̄`.
The recon expects the weighted A₃ coefficient giving `½A₃/A₁ ≈ 0.165`; `c̄/2 ≤ c̄`
so this is compatible with strictly better margin.  The multiplicative slack is
`1 + O(1/log x) → 1`, well inside the generous budget (`0.3631` target vs the
honest `0.363084`).

## What this file lands (floor progress)

* **Step 1 (the π-upper input, corrected).** `per_pair_weighted_le` — the sharp
  per-pair inner count keeping the `log(N/p₁p₂)` weight (replaces the uniform-floor
  `per_pair_le` of the landed count).  This is catch #53's step-1 fix.
* **Step 2 (the reduction).** `tripleSum_le_weighted_pairSum` — `tripleSum` bounded
  by the c̄-weighted double sum `weightedPairSum` plus the `|pairSet|/log L₀`
  remainder.  This is the exact input the two Abel passes consume.

The remaining analytic core — the two BJS-Lemma-20 Abel passes (steps 3–5) and the
`t = N^τ` change of variables evaluating the double integral to `c̄/log N`
(step 6) — is flagged (see `docs/blueprints/flags.md`, CNT2).

No `sorry`, no `native_decide`, no new axioms.

## Composition (SW4 consumes this)

`Salt.Chen.mainA3_of_hBVswitch` carries `tripleSum x z y` as a SYMBOLIC factor;
SW4's numeric re-gate consumes a `tripleSum ≤ (c̄ + slack)·x/log x`-form — the
`tripleSum_le_weighted_pairSum` reduction here is its `Σ 1/(p₁p₂ log)` factor.
-/

open Salt.LS ArithmeticFunction
open scoped BigOperators

namespace Salt.Chen

/-- Nat division is antitone in the denominator (local copy of the landed private
`TripleCount.nat_div_le_div_denom`). -/
private lemma nat_div_le_div_denom' {k a b : ℕ} (hab : a ≤ b) (ha : 0 < a) :
    k / b ≤ k / a := by
  refine (Nat.le_div_iff_mul_le ha).mpr ?_
  calc (k / b) * a ≤ (k / b) * b := Nat.mul_le_mul (le_refl _) hab
    _ ≤ k := Nat.div_mul_le_self k b

/-- `x/m > (x:ℝ)/m − 1` for `0 < m` (local copy of the landed private
`TripleCount.cast_div_ge`). -/
private lemma cast_div_ge' {x m : ℕ} (hm : 0 < m) :
    (x : ℝ) / m - 1 < ((x / m : ℕ) : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h1 : m * (x / m) + x % m = x := Nat.div_add_mod x m
  have h2 : x % m < m := Nat.mod_lt x hm
  have h3 : (x : ℝ) < ((x / m : ℕ) : ℝ) * m + m := by
    have : (x : ℝ) = (m : ℝ) * ((x / m : ℕ) : ℝ) + ((x % m : ℕ) : ℝ) := by exact_mod_cast h1.symm
    have h2R : ((x % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast h2
    nlinarith [this, h2R]
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hmR]
  linarith [h3]

/-! ## Section 1 — the weighted (BJS `N/p₁p₂`) log-denominator and double sum -/

/-- The BJS weight denominator `log(N/(p₁p₂)) = log(x/(p₁p₂))`, the honest per-pair
`p₃`-count log-length (versus the landed count's uniform floor `log⌊x/(2y√x)⌋`). -/
noncomputable def logND (x : ℕ) (q : ℕ × ℕ) : ℝ := Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2))

/-- The c̄-weighted pair reciprocal sum `Σ_{(p₁,p₂) ∈ pairSet} 1/(p₁p₂·log(N/p₁p₂))`
— the object the two BJS Abel passes send to `(c̄ + slack)/log x`. -/
noncomputable def weightedPairSum (x z y : ℕ) : ℝ :=
  ∑ q ∈ pairSet x z y, 1 / ((q.1 : ℝ) * q.2 * logND x q)

/-! ## Section 2 — the corrected per-pair inner count (BJS Lemma 52, step 1) -/

set_option maxHeartbeats 1200000 in
-- maxHeartbeats bump: this is a monolithic per-pair chain — the landed sharp
-- interval count (`prime_count_Ioc_le`) followed by the two `log L`-vs-`log(N/p₁p₂)`
-- slack conversions — so it exceeds the 200000 default.
/-- **Step 1 — the per-pair weighted inner count.**  For an admissible pair `q`
(under the uniform inner floor `4 ≤ log⌊x/(2y√x)⌋`, which forces `L` large so the
`log L`-vs-`log(N/p₁p₂)` shift is a `1+O(1/log x)` slack), the inner PNT count keeps
the sharp `log(N/p₁p₂)` weight:

  `#{p₃ ∈ (L,U]} ≤ (1 + 3K/L₀)(1 + W₀)·(x/2)·1/(p₁p₂·log(N/p₁p₂)) + 1/L₀`,

with `L₀ = log⌊x/(2y√x)⌋` and `W₀ = 4log 2/log(2⌊x/(2y√x)⌋)` the uniform slack
pieces (both `→ 0`).  This REPLACES the landed `per_pair_le`'s uniform `1/log L`
floor by the honest varying weight — catch #53's step-1 repair. -/
theorem per_pair_weighted_le {K : ℝ} (hK0 : 0 ≤ K)
    (hpsi : ∀ n : ℕ, 3 ≤ n → |psiTot n - (n : ℝ)| ≤ K * n / Real.log n)
    {x z y : ℕ} (hLval4 : 4 ≤ Real.log (Lval x y)) {q : ℕ × ℕ} (hq : q ∈ pairSet x z y) :
    primeCountIoc (Lfun x q) (Ufun x q)
      ≤ (1 + 3 * K / Real.log (Lval x y))
          * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x y : ℝ)))
          * ((x : ℝ) / 2) * (1 / ((q.1 : ℝ) * q.2 * logND x q))
        + 1 / Real.log (Lval x y) := by
  rw [pairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
  obtain ⟨⟨⟨hq1lo, hq1x⟩, hq2lo, hq2x⟩, _hzq1, hq1y, hyq2, hq2sq, hp1, hp2⟩ := hq
  -- positivity of the denominator
  have hm : 0 < q.1 * q.2 := Nat.mul_pos hp1.pos hp2.pos
  have hmR : (0 : ℝ) < (q.1 : ℝ) * q.2 := by exact_mod_cast hm
  -- the uniform floor value and its log
  set L₀ : ℝ := Real.log (Lval x y) with hL₀
  have hLval4' : 4 ≤ L₀ := hLval4
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  -- Lval > 1 (from log ≥ 4)
  have hLval1 : 1 < Lval x y := by
    by_contra h
    have h' : Lval x y ≤ 1 := not_lt.mp h
    have : Real.log (Lval x y) ≤ 0 := Real.log_nonpos (by positivity) (by exact_mod_cast h')
    rw [← hL₀] at this; linarith
  have hLval2 : 2 ≤ Lval x y := hLval1
  have hLvalPos : (0 : ℝ) < (Lval x y : ℝ) := by exact_mod_cast (by omega : 0 < Lval x y)
  -- `Lval ≥ 5` from `log Lval ≥ 4` (via `5 = 4+1 ≤ exp 4 ≤ exp(log Lval) = Lval`)
  have hLval5R : (5 : ℝ) ≤ (Lval x y : ℝ) := by
    have h1 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    have h2 : Real.exp 4 ≤ Real.exp (Real.log (Lval x y)) := Real.exp_le_exp.mpr hLval4
    rw [Real.exp_log hLvalPos] at h2
    linarith
  have hLval5 : 5 ≤ Lval x y := by exact_mod_cast hLval5R
  -- Lval ≤ Lfun ≤ Ufun (identical to the landed `per_pair_le`)
  have hq2sqrt : q.2 ≤ Nat.sqrt x := Nat.le_sqrt.mpr hq2sq
  have hden_le : 2 * q.1 * q.2 ≤ 2 * y * Nat.sqrt x := by
    calc 2 * q.1 * q.2 = 2 * (q.1 * q.2) := by ring
      _ ≤ 2 * (y * Nat.sqrt x) := Nat.mul_le_mul (le_refl 2) (Nat.mul_le_mul hq1y hq2sqrt)
      _ = 2 * y * Nat.sqrt x := by ring
  have hm2 : 0 < 2 * q.1 * q.2 := Nat.mul_pos (Nat.mul_pos (by norm_num) hp1.pos) hp2.pos
  have hLvalL : Lval x y ≤ Lfun x q := by
    rw [Lval, Lfun]
    refine (Nat.le_div_iff_mul_le hm2).mpr ?_
    calc Lval x y * (2 * q.1 * q.2) ≤ Lval x y * (2 * y * Nat.sqrt x) :=
          Nat.mul_le_mul (le_refl _) hden_le
      _ ≤ x := by rw [Lval]; exact Nat.div_mul_le_self x (2 * y * Nat.sqrt x)
  have hL3 : 3 ≤ Lfun x q := le_trans (by omega) hLvalL
  have hLU : Lfun x q ≤ Ufun x q := by
    rw [Lfun, Ufun]
    refine nat_div_le_div_denom' ?_ hm
    calc q.1 * q.2 ≤ 2 * (q.1 * q.2) := by omega
      _ = 2 * q.1 * q.2 := by ring
  -- logs: L₀ ≤ log L ≤ log U
  set logL : ℝ := Real.log (Lfun x q) with hlogLdef
  have hLvalLR : (Lval x y : ℝ) ≤ (Lfun x q : ℝ) := by exact_mod_cast hLvalL
  have hlogL_ge : L₀ ≤ logL := by
    rw [hlogLdef, hL₀]
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < Lval x y)) hLvalLR
  have hlogLpos : 0 < logL := lt_of_lt_of_le (by linarith) hlogL_ge
  have hLfunposR : (0 : ℝ) < (Lfun x q : ℝ) := by exact_mod_cast (by omega : 0 < Lfun x q)
  have hlogU : logL ≤ Real.log (Ufun x q) :=
    Real.log_le_log hLfunposR (by exact_mod_cast hLU)
  -- the raw sharp interval count (landed)
  have hraw := prime_count_Ioc_le hK0 hpsi hL3 hLU
  -- cast bounds for U and L against the real `t = x/(2 q₁ q₂)`
  have hUup : (Ufun x q : ℝ) ≤ (x : ℝ) / ((q.1 : ℝ) * q.2) := by
    rw [Ufun]; refine le_trans Nat.cast_div_le (le_of_eq ?_); push_cast; ring
  have hLup : (Lfun x q : ℝ) ≤ (x : ℝ) / (2 * (q.1 : ℝ) * q.2) := by
    rw [Lfun]; refine le_trans Nat.cast_div_le (le_of_eq ?_); push_cast; ring
  have hLlow : (x : ℝ) / (2 * (q.1 : ℝ) * q.2) - 1 < (Lfun x q : ℝ) := by
    rw [Lfun]
    have := cast_div_ge' (x := x) (m := 2 * q.1 * q.2) hm2
    convert this using 3
    push_cast; ring
  set t : ℝ := (x : ℝ) / (2 * (q.1 : ℝ) * q.2) with ht
  have htnn : 0 ≤ t := by rw [ht]; positivity
  have hxm : (x : ℝ) / ((q.1 : ℝ) * q.2) = 2 * t := by rw [ht]; field_simp
  -- t ≥ Lfun ≥ Lval ≥ 2, so t ≥ 2
  have ht_ge_Lfun : (Lfun x q : ℝ) ≤ t := by rw [ht] at hLup ⊢; exact hLup
  have ht2 : (2 : ℝ) ≤ t := le_trans (by exact_mod_cast hLval2) (le_trans hLvalLR ht_ge_Lfun)
  -- the three-summand numerator bound `≤ (1 + 3K/logL)·t + 1`
  have hUL : (Ufun x q : ℝ) - Lfun x q ≤ t + 1 := by
    have : (Ufun x q : ℝ) ≤ 2 * t := by rw [← hxm]; exact hUup;
    linarith [this, hLlow]
  have hlogUpos : 0 < Real.log (Ufun x q) := lt_of_lt_of_le hlogLpos hlogU
  have hKU : K * (Ufun x q : ℝ) / Real.log (Ufun x q) ≤ K * (2 * t) / logL := by
    have hU2t : (Ufun x q : ℝ) ≤ 2 * t := by rw [← hxm]; exact hUup
    calc K * (Ufun x q : ℝ) / Real.log (Ufun x q)
        ≤ K * (Ufun x q : ℝ) / logL :=
          div_le_div_of_nonneg_left (mul_nonneg hK0 (by positivity)) hlogLpos hlogU
      _ ≤ K * (2 * t) / logL := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (by nlinarith [hU2t, hK0]) (by positivity)
  have hKL : K * (Lfun x q : ℝ) / logL ≤ K * t / logL := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hLup, hK0]) (by positivity)
  have hnum : (Ufun x q : ℝ) - Lfun x q
        + K * (Ufun x q : ℝ) / Real.log (Ufun x q)
        + K * (Lfun x q : ℝ) / logL
      ≤ (1 + 3 * K / logL) * t + 1 := by
    have hexp : (1 + 3 * K / logL) * t = t + 3 * K / logL * t := by ring
    have hid : K * (2 * t) / logL + K * t / logL = 3 * K / logL * t := by field_simp; ring
    linarith [hUL, hKU, hKL, hexp, hid]
  have h1p3 : (0 : ℝ) ≤ 1 + 3 * K / logL := by
    have : (0 : ℝ) ≤ 3 * K / logL := div_nonneg (by linarith [hK0]) hlogLpos.le
    linarith
  have hnn : (0 : ℝ) ≤ (1 + 3 * K / logL) * t + 1 := by nlinarith [mul_nonneg h1p3 htnn]
  have hstep0 : primeCountIoc (Lfun x q) (Ufun x q) ≤ ((1 + 3 * K / logL) * t + 1) / logL := by
    calc primeCountIoc (Lfun x q) (Ufun x q)
        ≤ ((Ufun x q : ℝ) - Lfun x q + K * (Ufun x q : ℝ) / Real.log (Ufun x q)
            + K * (Lfun x q : ℝ) / logL) / logL := hraw
      _ ≤ ((1 + 3 * K / logL) * t + 1) / logL := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hlogLpos.le)
  -- === the `log L`-vs-`log(N/p₁p₂)` conversion (the 1+O(1/log x) slack) ===
  set logN : ℝ := logND x q with hlogNdef
  set D : ℝ := Real.log (2 * (Lval x y : ℝ)) with hDdef
  set W₀ : ℝ := 4 * Real.log 2 / D with hW₀def
  -- logND x q = log(2t)
  have hND_eq : logN = Real.log (2 * t) := by
    rw [hlogNdef, logND, hxm]
  -- D = log 2 + L₀ and D ≥ log 2 + 4
  have hD_eq : D = Real.log 2 + L₀ := by
    rw [hDdef, hL₀, Real.log_mul (by norm_num) (by positivity)]
  have hDpos : 0 < D := by rw [hD_eq]; linarith
  have hD_ge : Real.log 2 + 4 ≤ D := by rw [hD_eq]; linarith
  -- logN ≥ D  (2t ≥ 2 Lval)
  have hlogN_ge_D : D ≤ logN := by
    rw [hND_eq, hDdef]
    apply Real.log_le_log (by positivity)
    have : (Lval x y : ℝ) ≤ t := le_trans hLvalLR ht_ge_Lfun
    linarith
  have hlogNpos : 0 < logN := lt_of_lt_of_le hDpos hlogN_ge_D
  -- logL ≥ logN − 2 log 2  (Lfun ≥ t/2)
  have hLfun_ge_half : t / 2 ≤ (Lfun x q : ℝ) := by
    have : (x : ℝ) / (2 * (q.1 : ℝ) * q.2) - 1 < (Lfun x q : ℝ) := hLlow
    rw [← ht] at this; linarith [ht2]
  have hlogL_ge_ND : logN - 2 * Real.log 2 ≤ logL := by
    have h1 : Real.log (t / 2) ≤ logL := by
      rw [hlogLdef]
      exact Real.log_le_log (by linarith) hLfun_ge_half
    have h2 : Real.log (t / 2) = Real.log t - Real.log 2 :=
      Real.log_div (by linarith) (by norm_num)
    have h3 : logN = Real.log 2 + Real.log t := by
      rw [hND_eq, Real.log_mul (by norm_num) (by linarith)]
    linarith
  -- W₀ ∈ [0, 1] and W₀·D = 4 log 2
  have hW₀nn : 0 ≤ W₀ := by rw [hW₀def]; positivity
  have hW₀D : W₀ * D = 4 * Real.log 2 := by rw [hW₀def]; field_simp
  have hW₀le1 : W₀ ≤ 1 := by
    rw [hW₀def, div_le_one hDpos]; nlinarith [hD_ge, hlog2pos]
  -- the key inequality `logN ≤ (1 + W₀)·logL`
  have hconv : logN ≤ (1 + W₀) * logL := by
    have hWlogN : 4 * Real.log 2 ≤ W₀ * logN := by
      calc 4 * Real.log 2 = W₀ * D := hW₀D.symm
        _ ≤ W₀ * logN := mul_le_mul_of_nonneg_left hlogN_ge_D hW₀nn
    nlinarith [hlogL_ge_ND, hWlogN, hW₀le1, hlog2pos, mul_nonneg hW₀nn hlogLpos.le]
  -- 1/logL ≤ (1 + W₀)/logN, hence t/logL ≤ (1+W₀)·t/logN
  have hW₀nn' : 0 ≤ 1 + W₀ := by linarith
  have ht_div : t / logL ≤ (1 + W₀) * t / logN := by
    rw [div_le_div_iff₀ hlogLpos hlogNpos]
    calc t * logN ≤ t * ((1 + W₀) * logL) := mul_le_mul_of_nonneg_left hconv htnn
      _ = (1 + W₀) * t * logL := by ring
  -- (1 + 3K/logL) ≤ (1 + 3K/L₀), and 1/logL ≤ 1/L₀
  have h3K : 1 + 3 * K / logL ≤ 1 + 3 * K / L₀ := by
    have : 3 * K / logL ≤ 3 * K / L₀ :=
      div_le_div_of_nonneg_left (by linarith [hK0]) (by linarith) hlogL_ge
    linarith
  have hL₀pos : 0 < L₀ := by linarith
  have hrem : 1 / logL ≤ 1 / L₀ := by
    rw [div_le_div_iff₀ hlogLpos hL₀pos]; linarith [hlogL_ge, one_mul L₀]
  -- assemble
  have h3Kge : 0 ≤ 1 + 3 * K / L₀ := by
    have : 0 ≤ 3 * K / L₀ := div_nonneg (by linarith [hK0]) hL₀pos.le
    linarith
  have hprod : (1 + 3 * K / logL) * (t / logL)
      ≤ (1 + 3 * K / L₀) * ((1 + W₀) * t / logN) :=
    mul_le_mul h3K ht_div (by positivity) h3Kge
  have hsplit : ((1 + 3 * K / logL) * t + 1) / logL
      = (1 + 3 * K / logL) * (t / logL) + 1 / logL := by rw [add_div]; ring
  have hfinal_eq : (1 + 3 * K / L₀) * ((1 + W₀) * t / logN)
      = (1 + 3 * K / L₀) * (1 + W₀) * ((x : ℝ) / 2) * (1 / ((q.1 : ℝ) * q.2 * logN)) := by
    rw [ht]; ring
  calc primeCountIoc (Lfun x q) (Ufun x q)
      ≤ ((1 + 3 * K / logL) * t + 1) / logL := hstep0
    _ = (1 + 3 * K / logL) * (t / logL) + 1 / logL := hsplit
    _ ≤ (1 + 3 * K / L₀) * ((1 + W₀) * t / logN) + 1 / L₀ := by linarith [hprod, hrem]
    _ = (1 + 3 * K / L₀) * (1 + W₀) * ((x : ℝ) / 2)
          * (1 / ((q.1 : ℝ) * q.2 * logN)) + 1 / L₀ := by rw [hfinal_eq]

/-! ## Section 3 — the reduction to the c̄-weighted double sum (BJS Lemma 52, step 2) -/

/-- **Step 2 — the reduction.**  Summing the per-pair weighted count over `pairSet`,
the switch count `tripleSum` is bounded by the c̄-weighted double sum
`weightedPairSum` (the object the two BJS Abel passes send to `(c̄ + slack)/log x`),
plus the `|pairSet|/log⌊x/(2y√x)⌋` remainder:

  `tripleSum ≤ (1 + 3K/L₀)(1 + W₀)·(x/2)·weightedPairSum + |pairSet|/L₀`,

with `L₀ = log⌊x/(2y√x)⌋`, `W₀ = 4log 2/log(2⌊x/(2y√x)⌋)`, `K` the unconditional
PNT-error constant.  This is the exact input BJS Lemma 52 (steps 3–6) consumes: the
Abel passes bound `weightedPairSum ≤ (c̄ + slack)/log x`, giving
`tripleSum ≤ (1 + o(1))·(c̄/2)·x/log x`.  Composes `triple_count_le_pairSum` (the
landed Fubini+projection reduction) with `per_pair_weighted_le` (step 1). -/
theorem tripleSum_le_weighted_pairSum {x z y : ℕ}
    (hLval4 : 4 ≤ Real.log (Lval x y)) :
    ∃ K : ℝ, 0 ≤ K ∧
      tripleSum x z y ≤
        (1 + 3 * K / Real.log (Lval x y))
            * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x y : ℝ)))
            * ((x : ℝ) / 2) * weightedPairSum x z y
        + ((pairSet x z y).card : ℝ) / Real.log (Lval x y) := by
  obtain ⟨K, hK0, hpsi⟩ := psiTot_pnt
  refine ⟨K, hK0, ?_⟩
  have hstep : ∀ q ∈ pairSet x z y,
      primeCountIoc (Lfun x q) (Ufun x q)
        ≤ (1 + 3 * K / Real.log (Lval x y))
            * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x y : ℝ))) * ((x : ℝ) / 2)
            * (1 / ((q.1 : ℝ) * q.2 * logND x q)) + 1 / Real.log (Lval x y) :=
    fun q hq => per_pair_weighted_le hK0 hpsi hLval4 hq
  calc tripleSum x z y
      ≤ ∑ q ∈ pairSet x z y, primeCountIoc (Lfun x q) (Ufun x q) :=
        triple_count_le_pairSum x z y
    _ ≤ ∑ q ∈ pairSet x z y, ((1 + 3 * K / Real.log (Lval x y))
            * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x y : ℝ))) * ((x : ℝ) / 2)
            * (1 / ((q.1 : ℝ) * q.2 * logND x q)) + 1 / Real.log (Lval x y)) :=
        Finset.sum_le_sum hstep
    _ = (1 + 3 * K / Real.log (Lval x y))
          * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x y : ℝ))) * ((x : ℝ) / 2)
          * weightedPairSum x z y
        + ((pairSet x z y).card : ℝ) / Real.log (Lval x y) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
          mul_one_div]
        rfl

/-! ## Section 4 — the c̄ inner integral (BJS Lemma 52, step 6, the `t = N^τ` core)

The two Abel passes (steps 3–5, flagged) send `weightedPairSum` to the double
integral `∫_{1/8}^{1/3} (1/β)·I(β) dβ / log x` with (after `u = N^β`, `v = N^σ`)

  `I(β) = ∫_{1/3}^{(1-β)/2} 1/(σ(1 − β − σ)) dσ`,

so `weightedPairSum·log x → c̄`.  This section evaluates the inner integral in
closed form and identifies the resulting single integral with `cbar`
(`Salt.Chen.cbar`) — the analytic HEART of the c̄ evaluation, landed here to
de-risk the WALL.  What remains for step 6 is only the `(t,s) → (β,σ)` change of
variables that produces this double integral from the Abel-pass output. -/

/-- **Step 6 core — the inner integral.**  For `β ∈ [1/8, 1/3]`, the partial-
fraction integral evaluates in closed form:

  `∫_{1/3}^{(1-β)/2} 1/(σ(1 − β − σ)) dσ = log(2 − 3β)/(1 − β)`.

Antiderivative `F(σ) = (1−β)⁻¹·(log σ − log(1 − β − σ))`; both `σ` and `1 − β − σ`
stay `≥ 1/3 > 0` on the interval (using `β ≤ 1/3`), and the top endpoint
`σ = (1−β)/2` makes `F = 0`, the bottom `σ = 1/3` gives `−(1−β)⁻¹·log(1/(2−3β))`. -/
theorem cbar_inner_integral {β : ℝ} (hβlo : (1 : ℝ) / 8 ≤ β) (hβhi : β ≤ 1 / 3) :
    ∫ σ in (1 / 3 : ℝ)..((1 - β) / 2), (σ * (1 - β - σ))⁻¹
      = Real.log (2 - 3 * β) / (1 - β) := by
  have hβ1 : (0 : ℝ) < 1 - β := by linarith
  have hle : (1 : ℝ) / 3 ≤ (1 - β) / 2 := by linarith
  -- pointwise: both factors ≥ 1/3 on the interval, and the antiderivative
  have hpos : ∀ σ ∈ Set.uIcc (1 / 3 : ℝ) ((1 - β) / 2),
      (0 : ℝ) < σ ∧ (0 : ℝ) < 1 - β - σ := by
    intro σ hσ
    rw [Set.uIcc_of_le hle, Set.mem_Icc] at hσ
    exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  -- the derivative of `F` at each point equals the integrand
  have hderiv : ∀ σ ∈ Set.uIcc (1 / 3 : ℝ) ((1 - β) / 2),
      HasDerivAt (fun s => (1 - β)⁻¹ * (Real.log s - Real.log (1 - β - s)))
        ((σ * (1 - β - σ))⁻¹) σ := by
    intro σ hσ
    obtain ⟨hσ0, h1βσ0⟩ := hpos σ hσ
    have hd1 : HasDerivAt (fun s : ℝ => Real.log s) σ⁻¹ σ := Real.hasDerivAt_log hσ0.ne'
    have hinner : HasDerivAt (fun s : ℝ => 1 - β - s) (-1) σ := by
      simpa using (hasDerivAt_id σ).const_sub (1 - β)
    have hd2 : HasDerivAt (fun s : ℝ => Real.log (1 - β - s)) ((1 - β - σ)⁻¹ * (-1)) σ :=
      (Real.hasDerivAt_log h1βσ0.ne').comp σ hinner
    have hF := (hd1.sub hd2).const_mul (1 - β)⁻¹
    have hval : (1 - β)⁻¹ * (σ⁻¹ - (1 - β - σ)⁻¹ * (-1)) = (σ * (1 - β - σ))⁻¹ := by
      rw [mul_inv]
      field_simp
      ring
    rwa [hval] at hF
  -- integrability of the integrand
  have hcont : ContinuousOn (fun σ : ℝ => (σ * (1 - β - σ))⁻¹)
      (Set.uIcc (1 / 3 : ℝ) ((1 - β) / 2)) := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro σ hσ
      obtain ⟨hσ0, h1βσ0⟩ := hpos σ hσ
      positivity
  have hint : IntervalIntegrable (fun σ : ℝ => (σ * (1 - β - σ))⁻¹) MeasureTheory.volume
      (1 / 3) ((1 - β) / 2) := hcont.intervalIntegrable
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hkey]
  -- evaluate the antiderivative at both endpoints
  have htop : Real.log ((1 - β) / 2) - Real.log (1 - β - (1 - β) / 2) = 0 := by
    have : (1 : ℝ) - β - (1 - β) / 2 = (1 - β) / 2 := by ring
    rw [this]; ring
  have hbot : Real.log (1 / 3 : ℝ) - Real.log (1 - β - 1 / 3)
      = -Real.log (2 - 3 * β) := by
    have hpos23 : (0 : ℝ) < 2 - 3 * β := by linarith [hβhi]
    have h23 : (1 : ℝ) - β - 1 / 3 = (2 - 3 * β) / 3 := by ring
    rw [h23, Real.log_div hpos23.ne' (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0), Real.log_one]
    ring
  rw [htop, hbot]
  ring

/-- **Step 6 identity — `c̄` as the `(β,σ)` double integral.**  Substituting the
closed-form inner integral (`cbar_inner_integral`) shows `cbar` (the landed
`Salt.Chen.cbar`) IS the BJS double integral in `(β,σ) = (log_N u, log_N v)`
coordinates:

  `cbar = ∫_{1/8}^{1/3} (1/β)·(∫_{1/3}^{(1-β)/2} 1/(σ(1 − β − σ)) dσ) dβ`.

This is the exact object the two Abel passes produce (after `u = N^β`, `v = N^σ`),
scaled by `1/log N` — so `weightedPairSum·log x → c̄`.  The only remaining step-6
work is the `(t,s) → (β,σ)` change of variables (`∫ · d(loglog) = ∫ · dβ/β`). -/
theorem cbar_eq_double_integral :
    cbar = ∫ β in (1 / 8 : ℝ)..(1 / 3),
      β⁻¹ * (∫ σ in (1 / 3 : ℝ)..((1 - β) / 2), (σ * (1 - β - σ))⁻¹) := by
  rw [cbar]
  refine intervalIntegral.integral_congr (fun β hβ => ?_)
  rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) / 8 ≤ 1 / 3), Set.mem_Icc] at hβ
  rw [cbar_inner_integral hβ.1 hβ.2]
  have hβ0 : (0 : ℝ) < β := by linarith [hβ.1]
  have hβ1 : (0 : ℝ) < 1 - β := by linarith [hβ.2]
  field_simp

-- **Composition (SW4).**  `Salt.Chen.mainA3_of_hBVswitch` (Salt.Chen.SwitchSieve)
-- carries `tripleSum x z y` as a symbolic factor; SW4's numeric re-gate consumes
-- `tripleSum_le_weighted_pairSum` — once the two Abel passes (flagged) bound
-- `weightedPairSum ≤ (c̄ + slack)/log x`, we get `tripleSum ≤ (1+o(1))·(c̄/2)·x/log x`.
#check @tripleSum_le_weighted_pairSum
#check @cbar_eq_double_integral

end Salt.Chen
