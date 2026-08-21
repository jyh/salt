/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# STMT2 `hreduce` discharge — the main-term extraction (Tao Prop 2.6), spine node HREDUCE

The last node of the `h211` producer chain: discharge the δ-independent hypothesis
`hreduce` of `fBridge_of_singleCorr` (`Prop26.lean`), i.e. show the F-bridge integral
dominates half the main term:

    (1/2)·(∑_p 1/p)·H·|X| ≤ |∫ F|,   X = ∫ λ(n)λ(n+1) ∂(logMeasure x ω).

## STEP-0 adjudication (the frozen shape — PROVABLE AS-IS, no re-freeze)

The night-shift note worried the frozen `hreduce` is δ-free while the reduction's
error families (dilation `2rⱼ/p²/Z`, shift `3ω/x/Z`, boundary `|𝒫_H|`) are
δ-INDEPENDENT, so `(1/2)·SP·H·|X| ≤ |∫F|` would fail for arbitrarily small `|X|`
(`|∫F| ≥ main − err` is vacuous once `err > main ~ SP·H·|X|`).

**Resolution: the binder does NOT need re-freezing.** The frozen conclusion is
provable *as stated* provided its DISCHARGE carries the single-correlation lower
bound `hseed : ε/2 ≤ |X|` (from `singleCorr_of_fails`, `ChowlaFailure.lean`) as a
regime hypothesis.  This is legitimate: `hreduce` is only ever needed INSIDE the
`logChowla2Fails` context, where `|X| ≥ ε/2` holds.  Concretely, the discharge is a
FIXED δ-free term (the regime + `hseed` are applied before any `δ`), so it is shared
unchanged across the `∀δ` wrapping into `hprop26`:

    fun {δ} hδ hseed_δ => fBridge_of_singleCorr eps H hlog hcM hmert HRED hδ hseed_δ
      : hprop26

where `HRED : (1/2)·SP·H·|X| ≤ |∫F|` is `hreduce_holds … hseed` (`hseed : ε/2 ≤ |X|`
supplied OUTSIDE the wrapping, from the ambient failure assumption).  With `|X| ≥ ε/2`
the window coupling `hωbig` forces `err ≤ (1/4)·SP·H·ε ≤ (1/2)·SP·H·|X|`, so
`|∫F| ≥ main − err ≥ (1/2)·SP·H·|X|`.  The `∀δ` collapses to the hardest case
`δ = |X|`, which is exactly this bound; tiny-δ instances hold trivially since the
main-term floor `(1/2)·SP·H·|X|` is fixed.  `Prop26.lean` is UNTOUCHED.

`consumability_probe` below machine-checks the wrapping; `hreduce_close` discharges
the error-budget/closing arithmetic, isolating the sole flagged residual `hmain`.

## STOP-AND-FLAG: the main-term identification `hmain` is a CARRIER-GAP residual

`hmain : SP·H·|X| − ETOT ≤ |∫F|` (main term minus total error) is NOT closeable with
the landed toolkit.  After `perPair_dilation` the per-pair term is
`(1/p)·∑_m λ(p(m+kⱼ)+1)·λ(p(m+kⱼ)+p+1)/m /Z`, and reaching `(1/p)·X` needs two carriers
that DO NOT exist:

* **(G1) p-strided unit shift.**  The multiplicativity collapse `liouville_mul`/`prime`
  needs `λ(pN)·λ(pN+p) = λ(N)·λ(N+1)`, but the dilated term carries `λ(pN+1)·λ(pN+p+1)`.
  Removing the inner `+1` is a shift by 1 in a `p`-STRIDED index; `corr_shift_le`
  only covers unit shifts of the BASE window integral.
* **(G2) dilated-window ↔ base-window correlation comparison.**  Even after collapse,
  `∑_{m ∈ (x/pω, x/p]} λ(m+kⱼ)λ(m+kⱼ+1)/m /Z` is a correlation over a `p`-times-smaller
  window; equating it to `X` over `(x/ω, x]` requires window-stability of the
  correlation — an `O(1)` gap, not an absorbable error, and arguably the analytic crux
  (Tao controls it via the entropy/pretentious machinery, not naive comparison).

See `docs/blueprints/flags.md` (HREDUCE).  These are Fable/design-tier (new carriers
or a redesign of the per-pair route); flagged rather than ground.
-/
import Salt.Entropy.Chowla.Prop26
import Salt.Entropy.Chowla.ShiftCorr
import Salt.Entropy.Chowla.WindowMertensLower
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-- **STEP-0, machine-checked: the frozen `hreduce` is consumable into `hprop26`
WITHOUT re-freeze.**  Given the frozen δ-free conclusion `HRED` as a hypothesis, the
landed glue `fBridge_of_singleCorr` produces the `∀δ ∃c` shape `hprop26` that
`h211_of_logChowla2Fails` consumes — the single fixed term `HRED` is shared across all
`δ`.  This is the STEP-0 verdict in Lean: no δ-dependent binder is required. -/
theorem consumability_probe (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hlog : 1 ≤ Real.log (H : ℝ)) {cM : ℝ} (hcM : 0 < cM)
    (hmert : cM / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
    (HRED : (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|) :
    ∀ {δ : ℝ}, 0 < δ →
        δ ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| →
        ∃ c : ℝ, 0 < c ∧
          c * (δ * (H : ℝ) / Real.log (H : ℝ))
            ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
                ∂(logMeasure x ω)| :=
  fun {δ} hδ hseed => fBridge_of_singleCorr (δ := δ) eps H hlog hcM hmert HRED hδ hseed

/-- **STMT2, closing arithmetic (Step 4).**  Given the single-correlation lower bound
`hseed : ε/2 ≤ |X|`, the total-error budget `hbudget : ETOT ≤ (1/4)·SP·H·ε` (the
δ-independent errors summed and controlled by the window coupling `hωbig`), and the
main-term-minus-error bound `hmain : SP·H·|X| − ETOT ≤ |∫F|`, the frozen `hreduce`
conclusion `(1/2)·SP·H·|X| ≤ |∫F|` follows.

This isolates the reduction's sole remaining residual as `hmain` (the main-term
identification): with `|X| ≥ ε/2` the budget gives `ETOT ≤ (1/2)·SP·H·|X|`, so
`main − err ≥ (1/2)·SP·H·|X|`.  `hmain` is the CARRIER-GAP residual (G1/G2, see the
module note and `flags.md`); everything AROUND it closes here sorry-free. -/
theorem hreduce_close (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hseed : (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|)
    {ETOT : ℝ}
    (hbudget : ETOT ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
        * (H : ℝ) * (eps : ℝ))
    (hmain : (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| - ETOT
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|) :
    (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
        * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
      ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
          ∂(logMeasure x ω)| := by
  set SP : ℝ := ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) with hSP
  set X : ℝ := |∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| with hX
  have hSPnn : (0 : ℝ) ≤ SP := Finset.sum_nonneg (fun p _ => by positivity)
  have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  -- `(2X − ε)·SP·H ≥ 0` from `hseed`; combined with `hbudget` gives `ETOT ≤ (1/2)SP·H·X`.
  have hprod : (0 : ℝ) ≤ (2 * X - (eps : ℝ)) * (SP * (H : ℝ)) :=
    mul_nonneg (by linarith) (mul_nonneg hSPnn hHnn)
  nlinarith [hmain, hbudget, hprod]

/-! ### W-F3 B-5 — the `hreduce` discharge at shift `h`

`h` enters this file ONLY through the two carried objects: the gap-`h` correlation
`X_h = ∫ λ(n)λ(n+h)` and the shift-`h` bridge `fBridgeF_h`.  Every inequality below is
`h`-free arithmetic on named reals, so the `h = 1` scripts are reused verbatim — this file's
port is the cheapest of the five and its cost is exactly the restatement. -/

/-- **STEP-0 at shift `h`, machine-checked: the shift-`h` frozen `hreduce` is consumable into
the shift-`h` `hprop26` WITHOUT re-freeze.**  The `h`-family port of `consumability_probe`,
against `fBridge_of_singleCorr_h`.  As at `h = 1`, the single fixed term `HRED` is shared
across all `δ`: no `δ`-dependent binder appears at any shift. -/
theorem consumability_probe_h (h : ℕ) (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hlog : 1 ≤ Real.log (H : ℝ)) {cM : ℝ} (hcM : 0 < cM)
    (hmert : cM / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
    (HRED : (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|) :
    ∀ {δ : ℝ}, 0 < δ →
        δ ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| →
        ∃ c : ℝ, 0 < c ∧
          c * (δ * (H : ℝ) / Real.log (H : ℝ))
            ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
                ∂(logMeasure x ω)| :=
  fun {δ} hδ hseed =>
    fBridge_of_singleCorr_h (δ := δ) h eps H hlog hcM hmert HRED hδ hseed

/-- **STMT2 at shift `h`, closing arithmetic (Step 4).**  The `h`-family port of
`hreduce_close`: from the gap-`h` seed `hseed : ε/2 ≤ |X_h|`, the total-error budget
`hbudget : ETOT ≤ (1/4)·SP·H·ε`, and `hmain : SP·H·|X_h| − ETOT ≤ |∫F_h|`, the shift-`h`
frozen conclusion `(1/2)·SP·H·|X_h| ≤ |∫F_h|` follows.

⛔ NOTE ON THE BUDGET CONSTANT.  The `1/4` here is the SAME `1/4` as at `h = 1` and is NOT
where the shift is paid: this lemma is `h`-free arithmetic (`nlinarith` on named reals), and
the shift's whole cost sits upstream, inside `hbudget`'s own `1/8 + 1/16 + 1/16 = 1/4`
decomposition (`HBudget.lean`), whose boundary slice is the one that acquires a factor `h`. -/
theorem hreduce_close_h (h : ℕ) (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hseed : (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|)
    {ETOT : ℝ}
    (hbudget : ETOT ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
        * (H : ℝ) * (eps : ℝ))
    (hmain : (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| - ETOT
        ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|) :
    (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
        * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|
      ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
          ∂(logMeasure x ω)| := by
  set SP : ℝ := ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) with hSP
  set X : ℝ := |∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| with hX
  have hSPnn : (0 : ℝ) ≤ SP := Finset.sum_nonneg (fun p _ => by positivity)
  have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hprod : (0 : ℝ) ≤ (2 * X - (eps : ℝ)) * (SP * (H : ℝ)) :=
    mul_nonneg (by linarith) (mul_nonneg hSPnn hHnn)
  nlinarith [hmain, hbudget, hprod]

/-- **C1 — the `h = 1` compat for the closing arithmetic.**  Stated at the LANDED conclusion
of `hreduce_close` and discharged by `hreduce_close_h 1`.  The bridge object needs the
definitional compat `fBridgeF_h_one`; the correlation index does not (`n + 1` IS the `h := 1`
instance of `n + h`).  The rewrite is `simp only` rather than `rw`: `fBridgeF_h eps H 1 …`
occurs under the integral binder `∫ n, …`, which `rw` cannot enter. -/
theorem hreduce_close_h_one (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hseed : (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|)
    {ETOT : ℝ}
    (hbudget : ETOT ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
        * (H : ℝ) * (eps : ℝ))
    (hmain : (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| - ETOT
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|) :
    (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
        * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
      ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
          ∂(logMeasure x ω)| := by
  have := hreduce_close_h 1 eps H hseed hbudget (ETOT := ETOT)
    (by simp only [fBridgeF_h_one]; exact hmain)
  simp only [fBridgeF_h_one] at this
  exact this

end Salt.Entropy.Chowla
