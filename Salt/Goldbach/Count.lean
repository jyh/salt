/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.CountFinal
import Salt.Goldbach.Switch

/-!
# G-COUNT — pricing the Goldbach triple carriers (wave W3)

Design: `docs/exploration/q1-design.md`, node **G-COUNT** (D3, W3).  This file mirrors the
twin count line (`Salt/Chen/TripleCount.lean`, `WeightedCount.lean`, `CountFinal.lean`) to the
REFLECTED Goldbach carriers `goldTripleSet`/`goldACount`/`goldTripleSum` (G-SW,
`Salt/Goldbach/Switch.lean`, imported — never redefined).

## The reflection and its ONE structural novelty (executor finding, REPORTED loudly)

The twin's `tripleSum` counts admissible triples `(p₁,p₂,p₃)` — `z ≤ p₁ ≤ y < p₂ ≤ p₃`, all
prime — with product in the **top-half** window `[x/2+2, x]` (`tripleSet` filter
`x/2 + 2 ≤ prod3 t ∧ prod3 t ≤ x`).  The Goldbach `goldTripleSum` counts the SAME admissible
triples with product in the **bottom-half** window `[2, N/2]` (`goldTripleSet` filter
`2 ≤ prod3 t ∧ prod3 t ≤ N / 2`), the reflection `n + 2 ↦ N − n` of `twinWindow N = [N/2, N−2]`.

**The leading constant is UNCHANGED: `c̄/2`, `c̄ = ∫_{1/8}^{1/3} log(2−3t)/(t(1−t)) dt` N-free.**
The honest arithmetic (integral form): for a fixed pair `(p₁,p₂)` with `β = log_N p₁ ∈ [1/8,1/3]`,
`σ = log_N p₂ ∈ [1/3, (1−β)/2]`, the per-pair `p₃`-count is `π(N/(2p₁p₂)) − π(p₂)`, whose leading
term is `(N/(2p₁p₂))/log(N/(2p₁p₂)) = (N/2)·1/(p₁p₂·log(N/p₁p₂))` — the SAME BJS weight
`1/(p₁p₂·logND)` and the SAME `(N/2)` factor as the twin.  Summing (`∑_{p₂} ↦ ∫ dσ`, `∑_{p₁} ↦
∫ dβ/β`) gives `∑_{p₁} (1/β) log(2−3β)/(1−β) dβ = c̄` (the σ-range and the inner integral
`∫_{1/3}^{(1−β)/2} 1/(σ(1−β−σ)) dσ = log(2−3β)/(1−β)` are BYTE-IDENTICAL to the twin's, up to a
`log_N 2 → 0` endpoint shift).  Verdict: **no re-certification; `c̄` is N-free as the design's
D1 invariance claim asserts, and the count bridge carries NO singular series `𝔖_N`** (D4.1
discharged for the leading term — `weightedPairSum'` is `𝔖_N`-free).

**BUT the twin's per-pair COUNTING MECHANISM does NOT mirror verbatim** — this is the bottom-half
structural break (the pilot brief's flagged risk).  The twin prices the per-pair `p₃`-count over
a *dyadic* interval `(Lfun x q, Ufun x q] = (x/(2p₁p₂), x/(p₁p₂)]` (ratio 2); on a dyadic
interval `log(lower) ≈ log(upper) ≈ logND`, so `prime_count_Ioc_le`'s interval-mass bound
`#{p ∈ (L,U]} ≤ (U − L + …)/log L` (`TripleCount.lean:118`) already carries the sharp `logND`
weight.  The lower endpoint `Lfun` is FORCED by the twin's LOWER product bound `x/2+2 ≤ prod`
(`card_tripleSet_le_pairSum'`, `CountFinal.lean:143` — the `L < p₃` step derives `2·prod > x`).

The Goldbach carrier has NO lower product bound (`2 ≤ prod` is vacuous once the prime-size
constraints force `prod ≥ z·y² = N^{19/24}`).  So the per-pair `p₃`-count runs over the NON-dyadic
interval `(y, N/(2p₁p₂)]` (lower endpoint `y = N^{1/3}`, `log y = (1/3) log N ≠ logND`).  Pricing
THIS with `prime_count_Ioc_le` at `L = y` gives the weight `1/log y`, NOT `1/logND` — over by the
factor `logND/log y = 3(1−β−σ) ∈ [1, 13/8]`, i.e. a region-dependent overshoot up to `~1.6×`.
The sharp `logND` weight requires a **sharp `π`-upper bound** `π(N/(2p₁p₂)) ≤ (1+o(1))·
(N/(2p₁p₂))/log(N/(2p₁p₂))` (equivalently a `p₃`-dyadic-sum + geometric series `∑_k 2^{−(k+1)}=1`
against `prime_count_Ioc_le` per piece — the mass concentrates at the top piece where
`log ≈ logND`, so the sum IS sharp `1+o(1)`, NOT the naive `×2`).

**No such sharp `π`-upper bound is available for reuse.**  The codebase's `π`-machinery is
Chebyshev-crude (`Salt/Maynard/ChebyshevInterval.lean`: `π⌊x⌋ ≤ log4·x/log√x + √x`, coefficient
`2·log 4 ≈ 2.77`) or a `π`-LOWER bound (`primes_in_interval_ge`); mathlib has no sharp PNT-`π`
in directly usable form.  A `2.77×` (or even `1.6×`) overshoot BREAKS the assembly margin
`2 log 3 − log 6 − c̄ = 0.4 − 0.363 = 0.037` (`SwitchConstant.lean:111`): `0.4 − 1.6·0.363 < 0`.

So the sharp Goldbach per-pair count is a NEW keystone (`p₃`-dyadic-sum construction, Class C,
~150–250 lines) that the twin chain never needed — it is NOT a "price-via-import" mirror of
`per_pair_weighted_le`.  This is a genuine under-scoping of G-COUNT (design est. Class B / 380k):
the node should be RE-CUT to split off `goldPerPair_pi_upper` (the sharp per-pair `π`-count) as a
dedicated Class-C sub-node, after which the rest of the chain (`weightedPairSum'_le_cbar` is
carrier-free and REUSES VERBATIM; then CountW/CountAtOp*/CountClose mirror) proceeds to the SAME
`c̄/2`.  See the G-COUNT ledger entry for the full reuse census and the recommended re-cut.

## What THIS file lands (the clean, honest reduction — the count line's first leg)

`goldTripleSum_le_pairSum`: `goldTripleSum N z y ≤ ∑_{q ∈ pairSet' N z y} primeCountIoc y
(Lfun N q)` — the Fubini reindex (`goldTripleSum_eq_card`, G-SW) composed with the projection to
`pairSet'` (REUSED verbatim from the twin — the sharp cutoff `p₁p₂² ≤ N` still contains the
Goldbach projections, since `p₁p₂² ≤ p₁p₂p₃ = prod ≤ N/2 ≤ N`).  The per-pair count lands on the
HONEST Goldbach interval `(y, Lfun N q]` with `Lfun N q = ⌊N/(2p₁p₂)⌋` (the twin's `Lfun`, reused
— it is exactly the Goldbach UPPER endpoint `prod ≤ N/2 ⟹ p₃ ≤ N/(2p₁p₂)`).  This lemma is the
faithful entry point for the sharp per-pair keystone above: it exposes precisely the
`primeCountIoc y (Lfun N q)` object that needs the sharp `π`-upper pricing.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.Chen

namespace Salt.Goldbach

/-! ## The Goldbach count reduction to the sharp pair set `pairSet'` (upper endpoint `Lfun N`) -/

/-- **The Goldbach projection reduction (sharp cutoff).**  `#{admissible Goldbach triples} ≤
Σ_{(p₁,p₂) ∈ pairSet' N z y} #{p₃ ∈ (y, ⌊N/(2p₁p₂)⌋]}`.  The projection `goldTripleSet → pairSet'`
lands in the SHARP twin pair set (`p₁p₂² ≤ p₁p₂p₃ = prod ≤ N/2 ≤ N`); the per-fibre map `t ↦ p₃`
injects into the primes of `(y, ⌊N/(2p₁p₂)⌋]` — the upper endpoint from `prod ≤ N/2` (the twin's
`Lfun N q`), the lower endpoint `y` from the ordering `y < p₂ ≤ p₃` (there is NO dyadic lower
endpoint: the Goldbach carrier lacks the twin's `x/2+2 ≤ prod` bound — see the module header). -/
theorem goldCard_le_pairSum (N z y : ℕ) :
    ((goldTripleSet N z y).card : ℝ)
      ≤ ∑ q ∈ pairSet' N z y, primeCountIoc y (Lfun N q) := by
  classical
  -- projection lands in the sharp pair set
  have Hmem : ∀ t ∈ goldTripleSet N z y, (t.1, t.2.1) ∈ pairSet' N z y := by
    intro t ht
    rw [goldTripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
    obtain ⟨⟨ht1, ht21, _⟩, hz1, hy1, hy2, h23, hp1, hp2, _hp3, _hlo, hhi⟩ := ht
    rw [pairSet', Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨ht1, ht21⟩, hz1, hy1, hy2, ?_, hp1, hp2⟩
    -- `p₁·p₂² ≤ p₁·p₂·p₃ = prod ≤ N/2 ≤ N`
    calc t.1 * (t.2.1 * t.2.1) ≤ t.1 * (t.2.1 * t.2.2) := by gcongr
      _ = prod3 t := by rw [prod3]; ring
      _ ≤ N / 2 := hhi
      _ ≤ N := Nat.div_le_self N 2
  rw [Finset.card_eq_sum_card_fiberwise Hmem]
  push_cast
  refine Finset.sum_le_sum (fun q _hq => ?_)
  rw [primeCountIoc]
  refine Nat.cast_le.mpr ?_
  refine Finset.card_le_card_of_injOn (fun t => t.2.2) ?_ ?_
  · -- MapsTo: each fibre element's `p₃ = t.2.2` lands in the prime window `(y, ⌊N/(2p₁p₂)⌋]`
    intro t ht
    rw [Finset.mem_coe, Finset.mem_filter] at ht
    obtain ⟨htmem, hprojq⟩ := ht
    have hq1 : q.1 = t.1 := by rw [← hprojq]
    have hq2 : q.2 = t.2.1 := by rw [← hprojq]
    rw [goldTripleSet, Finset.mem_filter] at htmem
    obtain ⟨_, _, _, hy2, h23, hp1, hp2, hp3, _hlo, hhi⟩ := htmem
    have hden2 : 0 < 2 * q.1 * q.2 := by
      rw [hq1, hq2]; exact Nat.mul_pos (Nat.mul_pos (by norm_num) hp1.pos) hp2.pos
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by omega, ?_⟩, hp3⟩
    -- `p₃ ≤ ⌊N/(2p₁p₂)⌋`: from `2·prod = p₃·(2p₁p₂)` and `prod ≤ N/2 ⟹ 2·prod ≤ N`
    rw [Lfun]
    refine (Nat.le_div_iff_mul_le hden2).mpr ?_
    rw [hq1, hq2]
    have heq : t.2.2 * (2 * t.1 * t.2.1) = 2 * prod3 t := by rw [prod3]; ring
    rw [heq]; omega
  · -- InjOn: `p₃` determines the fibre element (`p₁, p₂` fixed by the fibre projection)
    intro t ht t' ht' heq
    rw [Finset.mem_coe, Finset.mem_filter] at ht ht'
    obtain ⟨ht1, ht2⟩ := Prod.ext_iff.mp (ht.2.trans ht'.2.symm)
    exact Prod.ext ht1 (Prod.ext ht2 heq)

/-- **The Goldbach count headline (reduction form).**  `goldTripleSum N z y ≤ Σ_{pairSet'}
#{p₃ ∈ (y, ⌊N/(2p₁p₂)⌋]}`.  Composes the G-SW Fubini reindex `goldTripleSum_eq_card` with the
projection reduction `goldCard_le_pairSum`.  The RHS per-pair count is the honest Goldbach object
that the sharp per-pair `π`-upper keystone must price (see the module header). -/
theorem goldTripleSum_le_pairSum (N z y : ℕ) :
    goldTripleSum N z y ≤ ∑ q ∈ pairSet' N z y, primeCountIoc y (Lfun N q) := by
  rw [goldTripleSum_eq_card]; exact goldCard_le_pairSum N z y

end Salt.Goldbach
