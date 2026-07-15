/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.PiUpper

/-!
# G-COUNT-2 — the Goldbach count line's TRUE close at `c̄/2` (`goldTripleSum_le_cbar_final`)

Design: `docs/exploration/q1-design.md`, node **G-COUNT-2** (the compose leg of the dyadic-tear
re-cut, `docs/exploration/pilot.md` 2026-07-15 ~17:00 / ~17:10).  This module composes the three
landed pieces of the Goldbach count line into the leading `c̄/2` bound — the Goldbach mirror of
`Salt.Chen.tripleSum_le_cbar_final` (`Salt/Chen/CountFinal.lean`):

* the projection reduction `goldTripleSum_le_pairSum` (`Salt/Goldbach/Count.lean`):
  `goldTripleSum N z y ≤ Σ_{q ∈ pairSet'} primeCountIoc y (Lfun N q)` (the honest non-dyadic
  Goldbach interval `(y, ⌊N/(2p₁p₂)⌋]`);
* the sharp per-pair keystone `goldPerPair_pi_upper` (`Salt/Goldbach/PiUpper.lean`):
  `primeCountIoc y (Lfun N q) ≤ (1 + (4log2+16log3+32K)/log y)·(N/2)·1/(p₁p₂·logND)` — the
  dyadic-tear fix, with a PURELY MULTIPLICATIVE `1 + O(1/log y)` correction and **no additive
  per-pair remainder** (contrast the twin's `+1/L₀`);
* the analytic heart `weightedPairSum'_le_cbar` (`Salt/Chen/CountFinal.lean`), REUSED VERBATIM
  (carrier-free): `weightedPairSum' N z y ≤ c̄/log N + [Abel/boundary corrections]`.

## The composition (cleaner than the twin's)

Because the per-pair correction is a single multiplicative factor
`coef = 1 + (4log2+16log3+32K)/log y` (`K` the `psiTot_pnt` PNT-error constant) and there is NO
additive `|pairSet'|/L₀` remainder, the Goldbach close is

  `goldTripleSum ≤ coef·(c̄/2)·(N/log N) + coef·(N/2)·CORR`,

with `CORR` the same `o(1/log N)` Abel-error/boundary sum as `weightedPairSum'_le_cbar` (the two
outer boundary primes `zN`, `yN`, the outer Abel error, and the per-fibre boundary prime + inner
Abel error).  The leading constant is `c̄/2` unchanged — the design's D1 no-recertification claim,
realized at the count level.

## The operating-point tension (executor finding, FLAGGED — see the module tail + `flags.md`)

The keystone's hypothesis `log N ≤ 3·log y` (with `y : ℕ`) and `weightedPairSum'_le_cbar`'s
`(y:ℝ) ≤ yR`, `log yR = log N/3` (i.e. `yR = N^{1/3}`) force `y = ⌊N^{1/3}⌋`, at which
`log N ≤ 3·log⌊N^{1/3}⌋` FAILS for non-cube `N` (by `≤ 3·N^{−1/3}`, and at op by `≤ 3/999999`
via `op_at_facts`).  So the two landed lemmas are **jointly satisfiable at the operating point only
for perfect-cube `N`**.  This is a proof artifact of the keystone's loose `hND_le_ly`
(`logND ≤ log N − log y ≤ 2 log y`, which ignores `p₁ ≥ z`); the tension is design-tier and blocks
the honest op instantiation (`x := N`) of the count seam.  This module therefore lands the
composition PARAMETRICALLY (`hlogNy`, the `weightedPairSum'` geometry rows carried as hypotheses);
the op instantiation is left to a keystone revisit (relax `hND_le_ly` via `p₁ ≥ z`).

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.Chen Salt.LS

namespace Salt.Goldbach

/-! ## The count close with a UNIFORM `K` (K explicit — the reusable form for the op fold) -/

/-- **`goldCount_bound_uniformK` — the Goldbach `c̄/2` count close with `K` explicit.**  Composes
`goldTripleSum_le_pairSum`, the summed keystone `goldPerPair_pi_upper` (its multiplicative
correction threaded, no additive remainder), and the VERBATIM `weightedPairSum'_le_cbar`.  `K` is a
hypothesis (the `psiTot_pnt`-shaped PNT row) so the operating-point fold can thread ONE uniform
constant, as in `Salt.Chen.count_bound_uniformK`.  The two extra hypotheses `6 ≤ yN`,
`log N ≤ 3·log yN` are the keystone's (the non-dyadic interval's operating relation). -/
theorem goldCount_bound_uniformK {K : ℝ} (hK0 : 0 ≤ K)
    (hpsi : ∀ n : ℕ, 3 ≤ n → |psiTot n - (n : ℝ)| ≤ K * n / Real.log n)
    {N zN yN : ℕ} {zR yR : ℝ}
    (hy6 : 6 ≤ yN) (hlogNy : Real.log N ≤ 3 * Real.log yN)
    (hx1 : 1 < (N : ℝ))
    (hzR2 : 2 ≤ zR) (hzRyR : zR ≤ yR)
    (hlogz : Real.log zR = Real.log N / 8) (hlogy : Real.log yR = Real.log N / 3)
    (hzN_le : (zN : ℝ) ≤ zR) (hzN_ge : zR ≤ (zN : ℝ) + 1)
    (hyN_le : (yN : ℝ) ≤ yR) (hyN_ge : yR ≤ (yN : ℝ) + 1) :
    goldTripleSum N zN yN
      ≤ (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log yN)
            * (cbar / 2) * ((N : ℝ) / Real.log N)
        + (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log yN)
            * ((N : ℝ) / 2)
            * ( ( Ifun (N : ℝ) yR (zN : ℝ) / (zN : ℝ) + Ifun (N : ℝ) yR (yN : ℝ) / (yN : ℝ)
                  + (21 / Real.log zR) * Ifun (N : ℝ) yR zR )
                + ∑ p₁ ∈ S1set N zN yN, (1 / (p₁ : ℝ))
                    * ( hbjs (N : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((N : ℝ) / (p₁ : ℝ))⌋₊))
                          / (↑(⌊Real.sqrt ((N : ℝ) / (p₁ : ℝ))⌋₊))
                        + (21 / Real.log yR)
                            * hbjs (N : ℝ) (p₁ : ℝ) (Real.sqrt ((N : ℝ) / (p₁ : ℝ))) ) ) := by
  have hlypos : 0 < Real.log yN := Real.log_pos (by exact_mod_cast (by omega : 1 < yN))
  have hCnn : (0 : ℝ) ≤ 4 * Real.log 2 + 16 * Real.log 3 + 32 * K := by
    have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  have hcoef_nn : (0 : ℝ) ≤ 1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log yN := by
    have : (0 : ℝ) ≤ (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log yN :=
      div_nonneg hCnn hlypos.le
    linarith
  have hcoefN2_nn : (0 : ℝ)
      ≤ (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log yN) * ((N : ℝ) / 2) :=
    mul_nonneg hcoef_nn (by linarith [hx1])
  -- Step 1: `goldTripleSum ≤ ∑ pairSet' primeCountIoc ≤ coef·(N/2)·weightedPairSum'`
  have hsum : goldTripleSum N zN yN
      ≤ (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log yN)
          * ((N : ℝ) / 2) * weightedPairSum' N zN yN := by
    calc goldTripleSum N zN yN
        ≤ ∑ q ∈ pairSet' N zN yN, primeCountIoc yN (Lfun N q) :=
          goldTripleSum_le_pairSum N zN yN
      _ ≤ (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log yN)
            * ((N : ℝ) / 2) * weightedPairSum' N zN yN := by
          rw [weightedPairSum', Finset.mul_sum]
          refine Finset.sum_le_sum (fun q hq => ?_)
          have h := goldPerPair_pi_upper hK0 hpsi hy6 hlogNy hq
          calc primeCountIoc yN (Lfun N q)
              ≤ (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log yN)
                  * ((N : ℝ) / 2) * (1 / ((q.1 : ℝ) * q.2 * logND N q)) := h
            _ = (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log yN) * ((N : ℝ) / 2)
                  * (1 / ((q.1 : ℝ) * q.2 * logND N q)) := by ring
  -- Step 2: the analytic heart, REUSED VERBATIM
  have hwps := weightedPairSum'_le_cbar hx1 hzR2 hzRyR hlogz hlogy hzN_le hzN_ge hyN_le hyN_ge
  have hmul := mul_le_mul_of_nonneg_left hwps hcoefN2_nn
  calc goldTripleSum N zN yN
      ≤ (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log yN)
          * ((N : ℝ) / 2) * weightedPairSum' N zN yN := hsum
    _ ≤ (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log yN)
          * ((N : ℝ) / 2)
          * ( cbar / Real.log N
              + ( Ifun (N : ℝ) yR (zN : ℝ) / (zN : ℝ) + Ifun (N : ℝ) yR (yN : ℝ) / (yN : ℝ)
                  + (21 / Real.log zR) * Ifun (N : ℝ) yR zR )
              + ∑ p₁ ∈ S1set N zN yN, (1 / (p₁ : ℝ))
                  * ( hbjs (N : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((N : ℝ) / (p₁ : ℝ))⌋₊))
                        / (↑(⌊Real.sqrt ((N : ℝ) / (p₁ : ℝ))⌋₊))
                      + (21 / Real.log yR)
                          * hbjs (N : ℝ) (p₁ : ℝ) (Real.sqrt ((N : ℝ) / (p₁ : ℝ))) ) ) := hmul
    _ = _ := by ring

/-! ## The count line's TRUE close (K existential — the headline form) -/

/-- **`goldTripleSum_le_cbar_final` — the Goldbach count line's `c̄/2` close.**  The Goldbach
mirror of `Salt.Chen.tripleSum_le_cbar_final`: composing the projection reduction, the sharp
per-pair keystone, and the VERBATIM analytic heart gives the switch count with LEADING constant
`c̄/2`, N-free.  Unlike the twin, the correction is a SINGLE multiplicative factor
`coef = 1 + (4log2+16log3+32K)/log y` and there is NO additive `|pairSet'|/L₀` remainder (the
Abel identity of `goldPerPair_pi_upper` killed the piece floors), so the `Rem` here is purely the
`o(x/log x)` Abel-error/boundary sum of `weightedPairSum'_le_cbar`.  `K` is the `psiTot_pnt`
PNT-error constant (inner existential, as in the landed twin close).  The operating relations are
supplied at the instance; the `hlogNy : log N ≤ 3·log yN` row is the keystone's (see the module
header's op-tension flag). -/
theorem goldTripleSum_le_cbar_final {N zN yN : ℕ} {zR yR : ℝ}
    (hy6 : 6 ≤ yN) (hlogNy : Real.log N ≤ 3 * Real.log yN)
    (hx1 : 1 < (N : ℝ))
    (hzR2 : 2 ≤ zR) (hzRyR : zR ≤ yR)
    (hlogz : Real.log zR = Real.log N / 8) (hlogy : Real.log yR = Real.log N / 3)
    (hzN_le : (zN : ℝ) ≤ zR) (hzN_ge : zR ≤ (zN : ℝ) + 1)
    (hyN_le : (yN : ℝ) ≤ yR) (hyN_ge : yR ≤ (yN : ℝ) + 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      goldTripleSum N zN yN
        ≤ (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log yN)
              * (cbar / 2) * ((N : ℝ) / Real.log N)
          + (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log yN)
              * ((N : ℝ) / 2)
              * ( ( Ifun (N : ℝ) yR (zN : ℝ) / (zN : ℝ) + Ifun (N : ℝ) yR (yN : ℝ) / (yN : ℝ)
                    + (21 / Real.log zR) * Ifun (N : ℝ) yR zR )
                  + ∑ p₁ ∈ S1set N zN yN, (1 / (p₁ : ℝ))
                      * ( hbjs (N : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((N : ℝ) / (p₁ : ℝ))⌋₊))
                            / (↑(⌊Real.sqrt ((N : ℝ) / (p₁ : ℝ))⌋₊))
                          + (21 / Real.log yR)
                              * hbjs (N : ℝ) (p₁ : ℝ) (Real.sqrt ((N : ℝ) / (p₁ : ℝ))) ) ) := by
  obtain ⟨K, hK0, hpsi⟩ := psiTot_pnt
  exact ⟨K, hK0, goldCount_bound_uniformK hK0 hpsi hy6 hlogNy hx1 hzR2 hzRyR hlogz hlogy
    hzN_le hzN_ge hyN_le hyN_ge⟩

end Salt.Goldbach
