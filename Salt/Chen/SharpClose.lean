/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.SharpF
import Salt.Chen.AbelStep
import Salt.Chen.WindowedStepC
import Salt.Chen.TwinSharp

/-!
# E₁c-close — the sharp per-step slot `StepHypWPC` at the boundary-padded coefficients

This file discharges the LAST remaining per-step obligation of the Chen arc: the FREEZE-V2 slot
`StepHypWPC (cfSharpB ·) (chSharpB ·) ε (tauSharpB ε)`.  It is pure composition — the two sharp
Stieltjes comparisons `hf_sharp_of_window` (`SharpF`) and the sharp `h`-comparison
(`SharpH2`) plug through `AbelStep.stepHyp_lhs_eq` + `AbelStep.ledger_collect`, exactly as the
crude template `DecayMass.stepHyp_pointwise` composes `hf_of_window`/`hh_of_window`.

## The one composition subtlety (`h4` on the `h`-side)

`SharpH2.hh_sharp_of_window` **threads** `h4 : Vlow s' D' ≤ (3K/S)·W` (`K ≤ 1+ε`) as a
hypothesis — it does not derive it.  That `h4` is *consumed only in its flat cell* (`S ≤ 3`), but
demanded *uniformly* (for every operating point) by the monolithic statement.  `h4` is provably
FALSE for large `S` (`Vlow ≥ W` while `3(1+ε)/S·W → 0`), and VD1 (`SharpF.vlow_le_of_guard`)
produces it only for `S ≤ 3`.  So `hh_sharp_of_window` cannot be called monolithically.  The fix
(no real gap — every leaf composes) is to mirror its own internal case split here: source `h4`
from VD1 in the flat branch (`hh_sharp_flat`), and use the `h4`-free `hh_sharp_ge2` for `S > 3`.
The `f`-side (`hf_sharp_of_window`) is already `h4`-free and needs no such split.

The extra premises the sharp comparisons carry beyond the crude ones — `hlo` (loBnd invariant),
`hpar` (parity coupling) — are exactly the two premises `StepHypWPC` adds to `StepHyp` (catch #32);
`hεsmall : ε ≤ 1/1000` is a hypothesis ON `ε` (outside the `∀` of `StepHypWPC`), so it rides as an
ordinary theorem hypothesis of `stepHypWPC_sharpB`, requiring no change to `StepHypWPC`.

`maxHeartbeats`: default; every step is a term-level plug of a landed lemma.
-/

open Finset

namespace Salt.Chen

/-! ## Part A — the per-cell composition at the sharp coefficients -/

/-- **The pointwise `StepHypWPC` body at `(cfSharpB, chSharpB)`.**  The sharp sibling of
`DecayMass.stepHyp_pointwise`: `stepHyp_lhs_eq` reshapes the peel sum, `hsplit` splits it into
`f`- and `h`-parts, and `ledger_collect` closes under the τ-recursion, with the sharp
comparisons `hf_sharp_of_window` (`f`-part, `h4`-free) and the cased `h`-part (VD1 in the flat
cell, `hh_sharp_ge2` above) plugged in.  Premises: `StepHypWPC`'s per-cell premise set PLUS
`hεsmall : ε ≤ 1/1000` (carried by both sharp comparisons). -/
theorem stepHyp_sharpB_pointwise (s' : BoundingSieve) (ε : ℝ) (tau : ℕ → ℝ) (z side' D' n : ℕ)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000) (hn : 1 ≤ n) (hD : 1 ≤ D') (hτ0 : 0 ≤ tau n)
    (hside : side' = 1 ∨ side' = 2)
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (hS1 : 1 ≤ logRatio z D') (hSn : logRatio z D' ≤ (n : ℝ) + 3)
    (hlo : loBnd side' ≤ logRatio z D') (hpar : side' % 2 ≠ n % 2)
    (hτrec : cfSharpB n ε + ε * Real.exp 2 * chSharpB ε * tau n
        ≤ ε * Real.exp 2 * tau (n + 1)) :
    (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
        s'.nu p * fseqBound' logRatio ε tau (sieveBelow s' p) p (3 - side') (cdiv D' p) n)
      ≤ fseqBound' logRatio ε tau s' z side' D' (n + 1) := by
  rw [stepHyp_lhs_eq logRatio ε tau s' side' D' n]
  simp only [fseqBound']
  have hsplit :
      (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
          s'.nu p * Vbelow s' p
            * (fseq n (logRatio p (cdiv D' p))
                + ε * tau n * Real.exp 2 * hBJS (logRatio p (cdiv D' p))))
        = (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
              s'.nu p * Vbelow s' p * fseq n (logRatio p (cdiv D' p)))
          + ε * tau n * Real.exp 2
            * ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
                s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit]
  -- the sharp `h`-part comparison, cased on `side'`/`S` (VD1 for the flat cell, `hh_sharp_ge2`
  -- above); this replaces the monolithic `hh_sharp_of_window`, whose uniform `h4` demand is
  -- unsatisfiable for `S > 3`.
  have hh_cmp :
      (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
          s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p)))
        ≤ Salt.BrunLower.W s' * (chSharpB ε * hBJS (logRatio z D')) := by
    have hSpos : (0 : ℝ) < logRatio z D' := by linarith
    rcases hside with rfl | rfl
    · -- side' = 1
      by_cases hle3 : logRatio z D' ≤ 3
      · -- flat cell `S ∈ [1,3]`: `h4` from VD1
        have h4 : Vlow s' D' ≤ (3 * (1 + ε) / logRatio z D') * Salt.BrunLower.W s' :=
          vlow_le_of_guard s' ε z D' hε hz hguard hnu hS1 hle3
        have hfilter :
            s'.prodPrimes.primeFactors.filter (fun p => 1 % 2 = 1 → p ^ 3 < D')
              = s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D') :=
          Finset.filter_congr (fun p _ => ⟨fun h => h (by norm_num), fun h _ => h⟩)
        rw [hfilter]
        exact hh_sharp_flat s' ε z D' hε hεsmall hD hS1 hle3 hguard hnu h4
      · -- `S > 3 ⟹ S ≥ 2`: `h4`-free
        have hS2 : 2 ≤ logRatio z D' := by have := not_le.mp hle3; linarith
        exact hh_sharp_ge2 s' ε z D' hε hD hS2 hz hguard hnu
          (s'.prodPrimes.primeFactors.filter (fun p => 1 % 2 = 1 → p ^ 3 < D'))
          (Finset.filter_subset _ _)
    · -- side' = 2 ⟹ `S ≥ 2` (loBnd 2 = 2): `h4`-free
      have hS2 : 2 ≤ logRatio z D' := by rw [loBnd_two] at hlo; exact hlo
      exact hh_sharp_ge2 s' ε z D' hε hD hS2 hz hguard hnu
        (s'.prodPrimes.primeFactors.filter (fun p => 2 % 2 = 1 → p ^ 3 < D'))
        (Finset.filter_subset _ _)
  exact ledger_collect (Salt.BrunLower.W_pos s').le hε (Real.exp_pos 2).le (hBJS_pos _).le
    hτ0
    (hf_sharp_of_window s' ε z side' D' n hε hεsmall hn hD hside hz hguard hnu hS1 hSn hlo hpar)
    hh_cmp hτrec

/-! ## Part B — the slot, discharged -/

/-- **`StepHypWPC` at the boundary-padded sharp coefficients — THE SLOT (E₁c-close).**  The
per-step contract `StepHypWPC (cfSharpB ·) (chSharpB ·) ε (tauSharpB ε)` discharged, the analytic
keystone of the Chen arc completed.  `hεsmall : ε ≤ 1/1000` is a hypothesis on `ε` (it lives
outside `StepHypWPC`'s `∀`), so it rides as an ordinary theorem hypothesis — `StepHypWPC` is
unchanged. -/
theorem stepHypWPC_sharpB (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000) :
    StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε (tauSharpB ε) := by
  intro s' z side' D' n hside hD hn hτ0 hz hguard hnu hS1 hSn hlo hpar hτrec
  exact stepHyp_sharpB_pointwise s' ε (tauSharpB ε) z side' D' n hε hεsmall hn hD hτ0
    hside hz hguard hnu hS1 hSn hlo hpar hτrec

/-! ## Part C — the B-plugs with the slot FILLED (windowed sharp BJS Theorem 6, final) -/

/-- **BJS Theorem 6 (5), windowed, sharp, per-step-CLOSED (upper) — the E₁c-close payoff.**
`bjs_theorem6_windowed_cB_upper` with the FREEZE-V2 slot filled by `stepHypWPC_sharpB`: no per-step
hypothesis remains.  The contraction gate `h249 : ε < 1/249` is DERIVED from `hεsmall`
(`1/1000 < 1/249`).  The structural Hyp-(4) slot `h4` stays, in the CONDITIONED form
(catch #66/H4C) — it is discharged by the H-glue via `H4Cond.h4_cond_of_base`, not here. -/
theorem bjs_theorem6_sharpB_final_upper (s : BoundingSieve) (zTop D : ℕ) (ε K : ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z D' → logRatio z D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio zTop D) :
    s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      ≤ Salt.BrunLower.W s *
        (Fchain (maxDepth s) (logRatio zTop D)
          + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio zTop D)) :=
  bjs_theorem6_windowed_cB_upper s zTop D ε K hD hzTop hguard hnu hε
    (lt_of_le_of_lt hεsmall (by norm_num)) hKe (stepHypWPC_sharpB ε hε hεsmall) h4 hStop

/-- **BJS Theorem 6 (6), windowed, sharp, per-step-CLOSED (lower) — the E₁c-close payoff.**  The
dual lower plug, slot filled by `stepHypWPC_sharpB`, `h249` derived from `hεsmall`. -/
theorem bjs_theorem6_sharpB_final_lower (s : BoundingSieve) (zTop D : ℕ) (ε K : ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z D' → logRatio z D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 2 ≤ logRatio zTop D) :
    Salt.BrunLower.W s *
        (fchain (maxDepth s) (logRatio zTop D)
          - ε * CsharpB ε * Real.exp 2 * hBJS (logRatio zTop D))
      ≤ s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam :=
  bjs_theorem6_windowed_cB_lower s zTop D ε K hD hzTop hguard hnu hε
    (lt_of_le_of_lt hεsmall (by norm_num)) hKe (stepHypWPC_sharpB ε hε hεsmall) h4 hStop

/-! ## Part D — `#audit`: what the H-glue now consumes

With `stepHypWPC_sharpB` landed, the FREEZE-V2 per-step slot is DISCHARGED.  The H-glue's two
carriers each take a single `hstepWPC` slot of the exact type produced here:

  `{twin_A1_lower_B, twin_A2_per_prime_B}  ×  {stepHypWPC_sharpB}`

* `TwinSharp.twin_A1_lower_B`   (TwinSharp.lean:60) — slot
    `hstepWPC : StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε (tauSharpB ε)`
* `TwinSharp.twin_A2_per_prime_B` (TwinSharp.lean:108) — same slot type.

`stepHypWPC_sharpB ε hε hεsmall : StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε
(tauSharpB ε)` fills BOTH.  The two `#check`s below elaborate the actual partial applications
(named-argument `hstepWPC := …`), so the kernel confirms each slot accepts the term. -/

-- the produced type is definitionally the slot type of both carriers:
example (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000) :
    StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε (tauSharpB ε) :=
  stepHypWPC_sharpB ε hε hεsmall

-- literal slot-acceptance checks against the H-glue carriers:
#check fun (x z D P : ℕ) (ε K Q : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000) =>
  twin_A1_lower_B x z D P ε K Q (hstepWPC := stepHypWPC_sharpB ε hε hεsmall)

#check fun (sp0 : BoundingSieve) (zTop Dlev : ℕ) (ε K Q : ℝ) (hε : 0 ≤ ε)
    (hεsmall : ε ≤ 1 / 1000) =>
  twin_A2_per_prime_B sp0 zTop Dlev ε K Q (hstepWPC := stepHypWPC_sharpB ε hε hεsmall)

end Salt.Chen
