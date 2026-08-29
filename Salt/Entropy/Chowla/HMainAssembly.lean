/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# W3-F-A — the `hmain` assembly, terminal node of the `h211` producer chain

The last node of the `h211` producer chain (`docs/exploration/s3-a3-design.md`,
W3-e-final): discharge the frozen `hreduce` conclusion
`(1/2)·SP·H·|X| ≤ |∫F|` and compose it into `hreduce_holds`, where

* `SP  = ∑_{p ∈ 𝒫_H} 1/p`                          (the Mertens window sum),
* `X   = ∫ λ(n)·λ(n+1) ∂(logMeasure x ω)`           (the single correlation),
* `∫F  = ∫ fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)`.

## The reverse-triangle discharge of `hmain` (this landing's advance)

`HReduce.lean` isolated `hmain : SP·H·|X| − ETOT ≤ |∫F|` as the "sole remaining
residual (CARRIER-GAP G1/G2)".  We show `hmain` is FREE: with the explicit main
term

    MAIN := ∑_{p ∈ 𝒫_H} (H/p)·X_signed,   X_signed := ∫ λ(n)λ(n+1) ∂(logMeasure),

we have `|MAIN| = SP·H·|X|` (the common factor `X_signed` pulls out, all `H/p > 0`),
and setting `ETOT := |∫F − MAIN|` the reverse triangle inequality gives
`|MAIN| − |∫F − MAIN| ≤ |∫F|`, i.e. exactly `hmain`.  `hreduce_close` then composes
`hseed + hbudget + hmain` into the frozen conclusion.  So the ENTIRE analytic
content collapses onto the single error budget

    hbudget : |∫F − MAIN| ≤ (1/4)·SP·H·ε.

`hreduce_holds` below is stated with `hbudget` as its one hypothesis (besides the
single-correlation floor `hseed`).  This is the honest W3E-FINAL obligation.

## ✅ STOP-AND-FLAG — **RESOLVED 2026-08-21: STALE. THE GATE-FIX LANDED IN `d5916681`.**
##
## ⛔ The flag below describes the world BEFORE `d5916681` ("play A: GATE-FIX lands — fBridgeG
## gate corrected to (j+1), G12 composes at the root, 9128 green"). It was written in
## `b77e4172`, which is an ANCESTOR of the fix, and this file has not been touched since —
## so the text sat 35 days describing a defect that was repaired hours after it was written.
## MEASURED: `b77e4172^` has the gate at `((n + j : ℕ) : ZMod p) = 0`; the LIVE
## `fBridgeF_liouville_apply` (`Prop26.lean:90`) gates at `((n + j + 1 : ℕ) : ZMod p) = 0` —
## which is *precisely the residue class the flag below says the collapse needs*. The gate index
## and the product base index now AGREE at `n+j+1`; the off-by-one the flag is about is gone.
## ⇒ The consequence sentence below ("`hbudget` … may be UNDISCHARGEABLE / FALSE via the
## intended route") DOES NOT HOLD against the current tree, and no h-analogue inherits it.
## 🔑 THIRD INSTANCE IN ONE DAY OF ONE SHAPE: a fix lands and the prose that motivated it stays.
## (The read-first bank's cut-line header; K4 vs the §1 rewrite; this.) **A WITHDRAWAL MUST SWEEP
## ITS DOWNSTREAM — AND A FIX MUST SWEEP ITS UPSTREAM.** Nothing points from a repair back to the
## description that asked for it, so the description outlives it silently.
## *Text preserved verbatim below, not rewritten — it is the record of a real catch.*
##
## STOP-AND-FLAG (HISTORICAL, RESOLVED): `hbudget` is blocked by a gate-convention off-by-one

The intended discharge of `hbudget` is the per-pair reduction
`∫F = ∑_{p,j} T(p,j)`, then `T(p,j) ≈ (1/p)·X` via
`perPair_collapse` (collapse λ(pN)λ(pN+p)=λ(N)λ(N+1)) + `dilated_window_stability`
+ `corr_shift_le`, summed with the design's error table (dilation `2H·SP/Z`, swap
`2H·log(ε²H)·SP/Z ≤` budget at the RATIFIED `hωbig : log ω ≥ (8/ε)·log(ε²H)+1`,
shift x-suppressed, boundary `|𝒫_H|·|X|` at `ε ≤ 1/48`).

That route does NOT connect to the landed `fBridgeF`.  `fBridgeF_liouville_apply`
gates each `(p,j)` term on `p ∣ n+j` (`((n+j:ℕ):ZMod p) = 0`) with product
`λ(n+j+1)·λ(n+j+p+1)`.  The multiplicativity collapse needs the two product
arguments to be MULTIPLES of `p`, i.e. `p ∣ n+j+1` — the COMPLEMENTARY residue
class.  Concretely at `p=2, j=0`: `fBridgeF` sums even `n` (product
`λ(2N+1)λ(2N+3)`, coprime to 2, no collapse), while `perPair_collapse` needs the
odd-`n` class (`n=2M+1 ⟹ λ(2(M+1))λ(2(M+1)+2)=λ(M+1)λ(M+2)`).  No `j`-reindex
closes the unit gap: the gate index (`j`) and the product base index (`j+1`) shift
together under `j ↦ j±1`, so every `fBridgeF` good-pair term lands on the
non-collapsing gate.  The design's "one translation absorbed in the j-sum" (line
428–430) does not absorb this — it is a gate/product RELATIVE shift of `O(1/p·Z)`
magnitude (same size as the main term), not a `j`-translation.

Consequence: the true main term of `∫F` is a gap-correlation `SP·H·X'` with
`X' = E[λ(pN+1)λ(pN+p+1)]`, generally `≠ X`, so `hbudget` (with the TRUE `X`) may
be UNDISCHARGEABLE / FALSE via the intended route.  This is design/Fable-tier: it
needs either the `residueWindow`/`liouvilleWindow` `+1` conventions realigned (both
landed, rippling into the Hoeffding concentration machinery) or a `p`-strided shift
carrier.  Recorded here rather than in `flags.md` (this session touches only the new
file).  `hreduce_holds` is therefore a sound CONDITIONAL reduction: the target holds
whenever the F-bridge integral is `(1/4)·SP·H·ε`-close to the intended main term.
-/
import Salt.Entropy.Chowla.DilationStability
import Salt.Entropy.Chowla.ShiftCorr
import Salt.Entropy.Chowla.Prop26
import Salt.Entropy.Chowla.HReduce
import Salt.Entropy.Chowla.WindowMertensLower
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-- **W3-F-A (`hreduce_holds`, class C).**  The frozen `hreduce` conclusion, reduced
to the single error budget `hbudget`.  With the explicit main term
`MAIN = ∑_{p ∈ 𝒫_H} (H/p)·X_signed` (`X_signed = ∫ λ(n)λ(n+1)`), the flagged carrier
residual `hmain` is discharged FREE by the reverse triangle inequality
(`|MAIN| = SP·H·|X|` and `|MAIN| − |∫F − MAIN| ≤ |∫F|`), so `hseed + hbudget` compose
through `hreduce_close` into the target.  `hbudget` is the honest W3E-FINAL
obligation (its discharge is blocked by the `fBridgeF` gate off-by-one; see the
module note). -/
theorem hreduce_holds (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hseed : (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|)
    (hbudget : |(∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
              ∂(logMeasure x ω))
          - (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ)
              * (∫ n, (ArithmeticFunction.liouville n : ℝ)
                  * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)))|
        ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ)) :
    (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
        * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
      ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
          ∂(logMeasure x ω)| := by
  set SP : ℝ := ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) with hSP
  set Xs : ℝ := ∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)
  set IF : ℝ := ∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
      ∂(logMeasure x ω)
  set MAIN : ℝ := ∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * Xs with hMAIN
  have hSPnn : (0 : ℝ) ≤ SP := Finset.sum_nonneg (fun p _ => by positivity)
  have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  -- Pull the common factor `Xs` out of the window sum: `MAIN = (∑ H/p)·Xs`.
  have hfac : MAIN = (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ)) * Xs := by
    rw [hMAIN, Finset.sum_mul]
  have hsumnn : (0 : ℝ) ≤ ∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg (fun p _ => by positivity)
  have hSPH : (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ)) = SP * (H : ℝ) := by
    rw [hSP, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun p _ => by rw [one_div_mul_eq_div])
  -- Hence `|MAIN| = SP·H·|Xs|` (all factors `H, SP ≥ 0`).
  have hMAIN_abs : |MAIN| = SP * (H : ℝ) * |Xs| := by
    rw [hfac, abs_mul, abs_of_nonneg hsumnn, hSPH]
  -- `hmain` (the flagged carrier residual) via the reverse triangle inequality.
  have hmain : SP * (H : ℝ) * |Xs| - |IF - MAIN| ≤ |IF| := by
    have h1 : |MAIN| - |IF| ≤ |IF - MAIN| := by
      rw [abs_sub_comm IF MAIN]
      exact abs_sub_abs_le_abs_sub MAIN IF
    have h2 := hMAIN_abs
    linarith
  -- `hbudget` is now `|IF − MAIN| ≤ (1/4)·SP·H·ε` (the `set`s fold its subterms).
  -- Close by `hreduce_close`'s arithmetic (`ETOT := |IF − MAIN|`): with `|Xs| ≥ ε/2`
  -- the budget forces `ETOT ≤ (1/2)·SP·H·|Xs|`, so `main − err ≥ (1/2)·SP·H·|Xs|`.
  have hprod : (0 : ℝ) ≤ (2 * |Xs| - (eps : ℝ)) * (SP * (H : ℝ)) :=
    mul_nonneg (by linarith [hseed]) (mul_nonneg hSPnn hHnn)
  nlinarith [hmain, hbudget, hprod]

/-! ### W-F3 B-5 — the `hmain` assembly at shift `h`

The reverse-triangle discharge of `hmain` is `h`-BLIND: it names the correlation once as a
real `Xs` and never reads its index, so the gap-`h` main term
`MAIN_h = ∑_{p ∈ 𝒫_H} (H/p)·X_h` obeys `|MAIN_h| = SP·H·|X_h|` by the same factor-pull.  The
`h = 1` script is reused verbatim with `Xs` set to the gap-`h` correlation. -/

/-- **W3-F-A at shift `h` (`hreduce_holds_h`).**  The `h`-family port of `hreduce_holds`: the
shift-`h` frozen `hreduce` conclusion, reduced to the single error budget

    hbudget : |∫F_h − ∑_{p ∈ 𝒫_H} (H/p)·X_h| ≤ (1/4)·SP·H·ε,   X_h = ∫ λ(n)λ(n+h).

`hmain` is discharged FREE by the reverse triangle inequality exactly as at `h = 1`
(`|MAIN_h| = SP·H·|X_h|` and `|MAIN_h| − |∫F_h − MAIN_h| ≤ |∫F_h|`), so `hseed + hbudget`
compose into the target.  `hbudget` at shift `h` is `hbudget_holds_h` (`HBudget.lean`). -/
theorem hreduce_holds_h (h : ℕ) (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hseed : (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|)
    (hbudget : |(∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
              ∂(logMeasure x ω))
          - (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ)
              * (∫ n, (ArithmeticFunction.liouville n : ℝ)
                  * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)))|
        ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ)) :
    (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
        * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|
      ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
          ∂(logMeasure x ω)| := by
  set SP : ℝ := ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) with hSP
  set Xs : ℝ := ∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)
  set IF : ℝ := ∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
      ∂(logMeasure x ω)
  set MAIN : ℝ := ∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * Xs with hMAIN
  have hSPnn : (0 : ℝ) ≤ SP := Finset.sum_nonneg (fun p _ => by positivity)
  have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hfac : MAIN = (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ)) * Xs := by
    rw [hMAIN, Finset.sum_mul]
  have hsumnn : (0 : ℝ) ≤ ∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg (fun p _ => by positivity)
  have hSPH : (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ)) = SP * (H : ℝ) := by
    rw [hSP, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun p _ => by rw [one_div_mul_eq_div])
  have hMAIN_abs : |MAIN| = SP * (H : ℝ) * |Xs| := by
    rw [hfac, abs_mul, abs_of_nonneg hsumnn, hSPH]
  have hmain : SP * (H : ℝ) * |Xs| - |IF - MAIN| ≤ |IF| := by
    have h1 : |MAIN| - |IF| ≤ |IF - MAIN| := by
      rw [abs_sub_comm IF MAIN]
      exact abs_sub_abs_le_abs_sub MAIN IF
    have h2 := hMAIN_abs
    linarith
  have hprod : (0 : ℝ) ≤ (2 * |Xs| - (eps : ℝ)) * (SP * (H : ℝ)) :=
    mul_nonneg (by linarith [hseed]) (mul_nonneg hSPnn hHnn)
  nlinarith [hmain, hbudget, hprod]

/-- **C1 — the `h = 1` compat for the assembly.**  Stated at the LANDED conclusion of
`hreduce_holds` and discharged by `hreduce_holds_h 1`.  As in `hreduce_close_h_one`, the
`fBridgeF_h eps H 1 …` occurrences sit under the integral binder, so the compat must be
applied with `simp only [fBridgeF_h_one]`, not `rw`. -/
theorem hreduce_holds_h_one (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hseed : (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|)
    (hbudget : |(∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
              ∂(logMeasure x ω))
          - (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ)
              * (∫ n, (ArithmeticFunction.liouville n : ℝ)
                  * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)))|
        ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ)) :
    (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
        * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
      ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
          ∂(logMeasure x ω)| := by
  have := hreduce_holds_h 1 eps H hseed (by simp only [fBridgeF_h_one]; exact hbudget)
  simp only [fBridgeF_h_one] at this
  exact this

end Salt.Entropy.Chowla
