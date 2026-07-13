/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.WindowedStepC
import Salt.Chen.TwinA1
import Salt.Chen.TwinA2

/-!
# GL1 — the sharp (cB) ports of the twin-A₁/A₂ keystone consumers (pre-glue rewiring)

`twin_A1_lower` (C2a) and `twin_A2_per_prime` (C2b) are re-expressed against the FREEZE-V2
boundary-padded sharp coefficients `(cfSharpB, chSharpB, tauSharpB, CsharpB)` of `WindowedStepC`,
with the entire numeric τ-layer (`htau1`/`hτ0`/`hτrec`/`htau`) DISCHARGED and the single per-step
slot `hstepWPC : StepHypWPC (cfSharpB ·) (chSharpB ·) ε (tauSharpB ε)` surfaced.  Contraction gate
`ε < 1/249` (NOT `1/49`).

## The one architectural finding (GL1's primary value): the consumers sit at DIFFERENT layers

* **A₁** (`twin_A1_lower`) consumes the *hlevel plug* `hlevel_w_lower` (a per-level `T`-bound), then
  the Rosser assembly `linear_sieve_lower_rosser_assembled_final` — which itself takes an `hlevel`,
  NOT a `mainSum`.  So the correct B-substitute is `hlevel_wpc_lower` at the B-coefficients (the
  hlevel-layer sibling of the cB keystone), with the SAME numeric τ-inputs discharged that
  `bjs_theorem6_windowed_cB_lower` discharges.  The keystone `bjs_theorem6_windowed_cB_lower`
  itself is a `mainSum` bound — the WRONG layer for A₁; it cannot slot into the assembly.  No gap:
  `hlevel_wpc_lower`'s only top condition is `hStop : 2 ≤ logRatio z D`, exactly what twinA1
  provides; it handles the even/`n=0` parity internally (no top-parity side condition).
* **A₂** (`twin_A2_per_prime`) consumes the *keystone* `bjs_theorem6_windowed_upper` (a `mainSum`
  bound) directly, then `linear_sieve_upper_rosser`.  Here `bjs_theorem6_windowed_cB_upper` IS the
  exact 1:1 substitute (its `hStop : 1 ≤ logRatio zTop Dlev` matches verbatim).

Both `_B` conclusions are shape-identical to the originals with `C₂/C₁ ↦ CsharpB ε` (regression
block, Part C), so the H-glue swaps them 1:1 modulo the ledger `CsharpB`-arithmetic.
-/

open Finset ArithmeticFunction Salt.LS Salt.BV

namespace Salt.Chen

/-! ## Part A — the A₁ B-port (`twin_A1_lower_B`) via the conditioned hlevel plug -/

/-- **`twin_A1_lower_B` — the sharp (cB) A₁ lower bound.**  `twin_A1_lower` with the numeric
τ-hypotheses (`htau1`/`hτ0`/`hτrec`/`htau`) DROPPED and the FREEZE-V2 slot exposed: the single
per-step contract `hstepWPC : StepHypWPC (cfSharpB ·) (chSharpB ·) ε (tauSharpB ε)` plus the
contraction gate `hε49B : ε < 1/249`.  The proof is `twin_A1_lower`'s verbatim, with the *hlevel*
call `hlevel_w_lower` replaced by the conditioned `hlevel_wpc_lower` at the B-coefficients (the
numeric τ-inputs discharged by `tauSharpB_one`/`tauSharpB_nonneg`/`tauSharpB_hτrec`, the τ-close by
`tauSharpB_sum_even_le`).  Slack constant `C₂ ↦ CsharpB ε`.  See the module note: A₁ is at the
hlevel/assembly layer, so `hlevel_wpc_lower` (not the `_cB_lower` keystone) is the port. -/
theorem twin_A1_lower_B (x z D P : ℕ) (ε K Q : ℝ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPz : ∀ p ∈ P.primeFactors, p < z)
    (hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ (p : ℝ))
    (hz2 : 2 ≤ z) (hzD : z ≤ D) (hD : 1 ≤ D)
    (hStop : 2 ≤ logRatio z D)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hKe : K ≤ 1 + ε)
    (hε49B : ε < 1 / 249)
    (hstepWPC : StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε (tauSharpB ε))
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hQ : 1 ≤ Q)
    (hBV : rosserRemainder (twinA1Sieve x P hP hPodd) (Q * D) ≤ (x : ℝ) / (Real.log x) ^ 10) :
    (twinA1Sieve x P hP hPodd).totalMass *
        (Salt.BrunLower.W (twinA1Sieve x P hP hPodd) *
          (fchain (maxDepth (twinA1Sieve x P hP hPodd)) (logRatio z D)
            - ε * CsharpB ε * Real.exp 2 * hBJS (logRatio z D)))
      - (x : ℝ) / (Real.log x) ^ 10
    ≤ ∑ n ∈ twinWindow x, if Nat.Coprime P (n + 2) then vonMangoldt n else 0 := by
  set s := twinA1Sieve x P hP hPodd with hs
  -- side conditions for the concrete sieve (verbatim from `twin_A1_lower`)
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < z := hPz
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := twinA1_hnu P
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    twinA1_hguard hε hw0 hPodd hPlow
  have htm : 0 ≤ s.totalMass := by
    rw [twinA1Sieve_totalMass]; exact Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
  -- THE PORT: the CONDITIONED windowed per-level (hlevel) bound at the B-coefficients.
  -- Only remaining per-step obligation is `hstepWPC`; the τ-numerics are discharged inline.
  have hlevel := hlevel_wpc_lower s z D ε K (fun n => cfSharpB n ε) (fun _ => chSharpB ε)
    (tauSharpB ε) hD hzTop hguard hnu hε.le hKe (tauSharpB_one ε) (tauSharpB_nonneg hε.le)
    hstepWPC (fun n => tauSharpB_hτrec n) h4 hStop
  -- assemble to the sifted lower bound at level Q·D, with the achieved constant `C₂ = CsharpB ε`
  have hassembled := linear_sieve_lower_rosser_assembled_final s D z hz2 hzD hzTop htm
    (logRatio z D) ε (CsharpB ε) Q hQ hε.le (tauSharpB ε) hlevel
    (tauSharpB_sum_even_le hε.le hε49B (maxDepth s + 1))
  -- rewrite the sifted sum as the A₁ carrier and fold in the BV remainder
  rw [twinA1Sieve_siftedSum] at hassembled
  linarith [hassembled, hBV]

/-! ## Part B — the A₂ B-port (`twin_A2_per_prime_B`) via the conditioned cB keystone -/

/-- **`twin_A2_per_prime_B` — the sharp (cB) per-prime A₂ upper bound.**  `twin_A2_per_prime` with
the numeric τ-hypotheses DROPPED and the FREEZE-V2 slot exposed (`hstepWPC` + `h249 : ε < 1/249`).
Here A₂ genuinely consumes the *keystone*, so the port is the exact 1:1 swap
`bjs_theorem6_windowed_upper ↦ bjs_theorem6_windowed_cB_upper` (which discharges `htau1`/`hτ0`/
`hτrec`/`htau` internally at the B-coefficients).  `linear_sieve_upper_rosser` and the `calc`
re-association are untouched.  Main coefficient `C₁ ↦ CsharpB ε`. -/
theorem twin_A2_per_prime_B (sp0 : BoundingSieve) (zTop Dlev : ℕ) (ε K Q : ℝ)
    (hD2 : 2 ≤ Dlev) (htm : 0 ≤ sp0.totalMass) (hQ : 1 ≤ Q)
    (hzTop : ∀ q ∈ sp0.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ sp0.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ sp0.prodPrimes.primeFactors, sp0.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (h249 : ε < 1 / 249) (hKe : K ≤ 1 + ε)
    (hstepWPC : StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε (tauSharpB ε))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio zTop Dlev) :
    sp0.siftedSum
      ≤ (sp0.totalMass * Salt.BrunLower.W sp0)
          * (Fchain (maxDepth sp0) (logRatio zTop Dlev)
              + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio zTop Dlev))
        + rosserRemainder sp0 (Q * Dlev) := by
  -- THE PORT: the CONDITIONED cB keystone (mainSum bound), τ-numerics discharged internally.
  have hmain := bjs_theorem6_windowed_cB_upper sp0 zTop Dlev ε K
    (by omega : 1 ≤ Dlev) hzTop hguard hnu hε h249 hKe hstepWPC h4 hStop
  have h := linear_sieve_upper_rosser sp0 Dlev hD2 htm (maxDepth sp0) (logRatio zTop Dlev)
    ε (CsharpB ε) Q hQ hmain
  calc sp0.siftedSum
      ≤ sp0.totalMass * (Salt.BrunLower.W sp0 *
          (Fchain (maxDepth sp0) (logRatio zTop Dlev)
            + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio zTop Dlev)))
        + rosserRemainder sp0 (Q * Dlev) := h
    _ = (sp0.totalMass * Salt.BrunLower.W sp0)
          * (Fchain (maxDepth sp0) (logRatio zTop Dlev)
            + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio zTop Dlev))
        + rosserRemainder sp0 (Q * Dlev) := by rw [← mul_assoc]

/-! ## Part C — regression: the `_B` conclusions are shape-identical to the originals

The H-glue swaps `_B` for the original 1:1; the only ledger delta is the numeric constant
(`C₂ ↦ CsharpB ε` for A₁, `C₁ ↦ CsharpB ε` for A₂).  Uncomment the `#check`s to inspect:

A₁ slack term (the ONLY change, `sparam = logRatio z D`):
* `twin_A1_lower`  : slack `- ε * C₂       * e² * hBJS sparam`
* `twin_A1_lower_B`: slack `- ε * CsharpB ε * e² * hBJS sparam`
  (rest identical: `totalMass * (W * (fchain N sparam - ·)) - x/(log x)^10 ≤ A₁`)

A₂ main term (the ONLY change, `sparam = logRatio zTop Dlev`):
* `twin_A2_per_prime`  : main `+ ε * C₁       * e² * hBJS sparam`
* `twin_A2_per_prime_B`: main `+ ε * CsharpB ε * e² * hBJS sparam`
  (rest identical: `siftedSum ≤ (totalMass * W) * (Fchain N sparam + ·) + rosserRemainder`)
-/

-- #check @twin_A1_lower       -- original (parametric τ, slack ε·C₂·e²·hBJS)
-- #check @twin_A1_lower_B     -- B-port (τ = tauSharpB ε, slack ε·CsharpB ε·e²·hBJS)
-- #check @twin_A2_per_prime   -- original (parametric τ, main +ε·C₁·e²·hBJS)
-- #check @twin_A2_per_prime_B -- B-port (τ = tauSharpB ε, main +ε·CsharpB ε·e²·hBJS)

end Salt.Chen
