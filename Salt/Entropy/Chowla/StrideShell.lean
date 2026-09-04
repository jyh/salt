/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# λ-BV wave 2-S, step F4a — THE AFFINE SHELL AND THE AFFINE HEAD (the S-block)

The `L²` Theorem-2.3 shell at the affine forms — `log_chowla_two_shell_xi_sq_h`
(`Theorem23Shell.lean:624`) with the measure `logMeasureAff R.a R.x R.ω`, the F-function
`fBridgeF_aff`, the FILTERED decoupled correlation in the circle-method slot, the frequency set
`bigXiAff`, the door `MRTUniformityXiL2AffW` (F3-P9) and the seam at Tao's range
`contradiction_of_mrtDoorXiL2AffW` (F3-P11, `StridePair.lean:390`) — and above it THE AFFINE
HEAD: at the crown's regime `Ra` (`mrtUniformityXiL2AffW_holds_flat_stride`,
`StridePairReceipt.lean:2121`), the door at any grade `ρ' ≤ δ₀_aff` implies `¬ logChowlaFailsAff`.

THE DESIGN (price brief `2026-09-04-math-PRICE-lbv-w2S-F4-entropy-half.md` §2, Arm B — THE
PLAIN ROAD).  The crown exports a PLAIN `ChowlaRegimeAff` whose tower fits and crosses at stride
`a` (`regimeShrinkX_stride`, `StridePair.lean:135-227`); the affine decrement
(`entropy_decrementAff`, `StrideDecrement.lean`) runs on exactly that, at the plain threshold
`κ = H/(log H · logloglog H)`, and the PLAIN spine-budget witness `hbudget1_witness`
(`SpineFinal.lean:598`; `R : ChowlaRegime`, `cD3 C` free, NO `h` binder) supplies `hbudget1` at
`cD3' := cD3/a` (F2-C3: `c₁ ↦ c₁/a`).  Its floor `budgetFloor ε β` (`BudgetCore.lean:30`, a
triple exponential) is paid in the design constant `A`, which the crown quantifies `∀ A₀ ∃ A ≥
A₀` and which NO consumer caps (price brief §2): `budgetFloor_le_flatDesignBase` and
`nat_le_flatDesignBase` turn the head's floors into a choice of `A₀`.  Nothing on the MR side
moves.  The `h`-lane's FLAT head (`HloExportFlatH.lean:220-372`) is the template for the ORDER
of the head's proof (leaves first, then the pin, then the regime, then the decrement, the
witness, the core); its flat threshold is replaced by the plain one.

⭐ THE CIRCLE-METHOD SLOT (price brief §1, F-2).  The affine circle-method estimate — Tao Lemma
3.4 at the class filter, over `bigXiAff` — has no producer yet (F4b).  It enters the shell as
the hypothesis `hcirc` and the head as the hypothesis `hcm` carrying the CAP `C ≤ h·(1 + 2·C₀)`
(the `_bounded_h` shape, `HeadPinLeavesH.lean:511`).  The head reads `C` ONLY through that cap
(the ε-pin's ε²-arm `hε_D3C`, where `ε·16·a·C ≤ 16·6.55/500 = 0.2096 ≤ 1/4 = cD3` at every
`(a, h)` because `ε·a·h = 1/500`); if F4b's constant is `a·C(h)` instead, TWO cap reads fail —
`hε_D3C` and `hδ₀ge`'s `hkey` — and nothing else (v1.1, verdict A8(ii)); M1 is ISOLATED in those
two lines.

⛔ HONEST LABEL.  F4a produces `∀ ρ' ≤ δ₀_aff, MRTUniformityXiL2AffW h Ra ρ' → ¬ logChowlaFailsAff`
beside the crown's door at grade `a·Zr·ρ + E` — NOT composed: `a·Zr·ρ + E ≤ δ₀_aff` is the `214`
miss at `(210, 2)` and F5's numeral.  Conditional on the circle-method slot (F4b).  Nothing
here proves an estimate or bears on twin primes.  Every declaration below is statement-only at
the freeze (sorry-bodied, recipe in the docstring), built as a module through
`../saltbuild.sh`; NO executor fires before the helm's refuter verdict.  ⛔ MERGE FENCE (iron
rule 2): `math/lbv-w2s-f4a` never reaches `main` until every obligation in the four F4a files
lands sorry-free.  Import direction: `Salt.Entropy`-internal; the crown lives in `Salt.MR`, so
the head's CONSUMER of the crown is stated here as a hypothesis-free theorem that OBTAINS the
crown… — ⛔ NO: `Salt.Entropy` cannot import `Salt.MR` (the `xceil` fence, H3's lesson).  The
head therefore takes the crown's PAYLOAD as a binder (`hcrown`, the crown's own conclusion
shape at `(a, b, h, A₀)`), and the ONE-LINE consumer that feeds the landed crown into it is an
`Salt.MR` node (`StridePairReceipt`'s file or a sibling), listed in the freeze as F4-S6 and NOT
in this file.
-/
import Salt.Entropy.Chowla.StrideDecrement
import Salt.Entropy.Chowla.StrideCombine
import Salt.Entropy.Chowla.StrideReduce
import Salt.Entropy.Chowla.Theorem23Shell
import Salt.Entropy.Chowla.HloExportFlatH
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ## F4-S0 — the plain road's two floor lemmas (paid in `A`) -/

/-- **F4-S0a (class B).**  The triple-exponential budget floor sits below the flat design base
once `exp(budgetX ε β) ≤ 3.2·A`: `budgetFloor ε β = ⌈exp(exp(exp X))⌉₊ ≤ ⌈exp(exp(3.2A))⌉₊ =
flatDesignBase A` by `Real.exp_le_exp` twice and `Nat.ceil_le_ceil` (`BudgetCore.lean:30`,
`TowerFlatBuilder.lean:95`). -/
theorem budgetFloor_le_flatDesignBase (ε β A : ℝ) (hX : Real.exp (budgetX ε β) ≤ 3.2 * A) :
    budgetFloor ε β ≤ flatDesignBase A := by
  sorry

/-- **F4-S0b (class B).**  A natural below the flat design base: for `loglog n ≤ 3.2·A`,
`n ≤ flatDesignBase A`.  `n ≤ 1` is trivial (`flatDesignBase A ≥ 1`, `Nat.one_le_ceil`-shape);
for `2 ≤ n`, `log n > 0`, `Real.le_log_iff_exp_le`, `Real.exp_le_exp`, then `Nat.le_ceil`. -/
theorem nat_le_flatDesignBase (n : ℕ) (A : ℝ) (hn : Real.log (Real.log (n : ℝ)) ≤ 3.2 * A) :
    n ≤ flatDesignBase A := by
  sorry

/-! ## F4-S1 — THE `L²` SHELL AT THE AFFINE FORMS -/

-- `windowExpSum_norm_eq_dft` is a `private lemma` of `Theorem23Shell.lean:68` (v1.1, verdict A4;
-- precedent `HeadPinLeavesH.lean:50-51`).
open private windowExpSum_norm_eq_dft from Salt.Entropy.Chowla.Theorem23Shell in
/-- **F4-S1 (class B) — THE `L²` SHELL AT THE AFFINE FORMS** (`log_chowla_two_shell_xi_sq_aff`).
`log_chowla_two_shell_xi_sq_h` (`Theorem23Shell.lean:624`) with the six substitutions: the
measure `logMeasureAff R.a R.x R.ω`; `fBridgeF_aff R.eps H R.a R.b h` in `h211`; the FILTERED
decoupled correlation (SITE 3, `StrideBridge.lean:371-376`'s spelling) on the left of `hcirc`
and `bigXiAff R.a R.b h R.eps H` on its right; `MRTUniformityXiL2AffW h R` (F3-P9); the range
`R.a ∣ H ∧ R.a * R.Hlo ≤ H` (Tao's); `shellError R.toChowlaRegime H t g κ` UNCHANGED (its
`H[residueWindow; logMeasure R.x R.ω]` is the affine value by `entropy_residueWindow_aff_eq`).
Chain: `hoc := outer_combine_aff …` (with `hcop := coprime_PH_of_le R.ha R.hcoprime hlo'`,
`hlo' : R.Hlo ≤ H` from `hlo` and `R.ha`), the error term rewritten by the relabel into
`shellError`; Bridge B (`abs_integral_le_integral_abs`, `integral_mono_ae` at the stride
measure's `integrable_of_finiteSupport _`); Bridge A squared per `ξ` (`integral_const_mul`,
`integral_finsetSum`, `windowExpSum_norm_eq_dft` — reached by the `open private … in` above) —
the Fourier factor is at the UNTWISTED `ξ`
exactly as at `h`; `hstar`, `hmul`, `hlower : c₀·ε ≤ door`; finally
`contradiction_of_mrtDoorXiL2AffW h R hdvd hlo hhi hdoor hbudget2 hlower`.  `0 < h` is NOT a
binder (the discharger's fence, as at `h`). -/
theorem log_chowla_two_shell_xi_sq_aff (h : ℕ)
    (R : ChowlaRegimeAff) {H : ℕ} [NeZero H] (hdvd : R.a ∣ H) (hlo : R.a * R.Hlo ≤ H)
    (hhi : H ≤ R.Hhi)
    (hH : 3 ≤ H) (hlog : 1 ≤ Real.log (H : ℝ)) (hne : (primeWindow R.eps H).Nonempty)
    (hreg : Real.sqrt (H : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) / 2)
    (hhead : 8 * (PH R.eps H : ℝ) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ))
    {t : ℝ} (ht : 0 < t) {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
        / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    {κ : ℝ} (hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasureAff R.a R.x R.ω] ≤ κ)
    {c₁ : ℝ} (hc₁ : 0 < c₁)
    (h211 : c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ m, fBridgeF_aff R.eps H R.a R.b h (liouvilleWindow H m) (residueWindow R.eps H m)
            ∂(logMeasureAff R.a R.x R.ω)|)
    -- the SQUARED circle-method Fourier bound at the affine forms (THE SLOT — F4b's producer):
    {C : ℝ} (hC : 0 < C)
    (hcirc : ∀ m : ℕ,
      |∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod R.a) = (((p : ℕ) * R.b : ℕ) : ZMod R.a) then
            (windowVal H (liouvilleWindow H m) j : ℝ)
              * (windowVal H (liouvilleWindow H m) (j + (p : ℕ) * h) : ℝ) else 0|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiAff R.a R.b h R.eps H, (1 / (H : ℝ) ^ 2)
                * ‖ZMod.dft (fun j : ZMod H =>
                    (windowVal H (liouvilleWindow H m) (ZMod.val j) : ℂ)) ξ‖ ^ 2))
    -- the Ξ-SUMMED `L²` MRT door at the affine forms AT TAO'S RANGE (F3-P9); NO `K`:
    {ρ c₀ : ℝ} (hdoor : MRTUniformityXiL2AffW h R ρ)
    -- the two numeric-closure budgets:
    (hbudget1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
          + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + shellError R.toChowlaRegime H t g κ
        ≤ c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)))
    (hbudget2 : ρ < c₀ * (R.eps : ℝ)) :
    False := by
  sorry

/-! ## F4-S2 — the spine contradiction core at the affine forms -/

/-- **F4-S2 (class B) — the `L²` spine contradiction core at the affine forms.**
`spine_False_core_xi_sq_flat_h` (`HloExportFlatH.lean:67`, private) with the seed
`singleCorr_of_failsAff'` (F1-N2), the reduce `hred` in `hreduce_holds_final_aff`'s shape at the
GATE `ε·a·h ≤ cE/(64·log 4)` and the count slack `64·a ≤ ε·H`, the Mertens leaf `hD3` verbatim,
the circle SLOT `hcm` at the filtered sum over `bigXiAff`, the shell `log_chowla_two_shell_xi_sq_aff`.
The regime discharges are `R.toChowlaRegime`'s (`sqrt_le_window_at`, `omega_big_at`, `x_big_at`,
`pH_headroom_at`, `Regime.lean:195-261`, at `hlo' : R.Hlo ≤ H` from `hlo` and `R.ha`);
`hcop := coprime_PH_of_le R.ha R.hcoprime hlo'`; `hlog2 : 2 ≤ log ω` as at `h`; `h211` at
`c₁ := cD3/(4·R.a)` from `hredH` (`(1/2)·SP·(H/a)·X ≥ (1/2)·(H/a)·(cD3/log H)·(ε/2)`); `hcard`
from `primeWindow_card_le_of_regime`; `hcirc` from `hcm` at `liouvilleWindow H m`
(`abs_liouvilleWindow_le_one`).  Threshold-agnostic in `κ`, as at `h`. -/
theorem spine_False_core_xi_sq_aff (h : ℕ) (_hh : 0 < h) (R : ChowlaRegimeAff)
    (hblt : R.b < R.a) {ρ : ℝ}
    (hdoor : MRTUniformityXiL2AffW h R ρ)
    (cE : ℝ) (_hcE : 0 < cE) (H₀red : ℕ)
    (hred : ∀ (eps : ℚ) (H x ω : ℕ),
      Nat.Coprime R.a (PH eps H) →
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀red ≤ H →
      (eps : ℝ) * (R.a : ℝ) * (h : ℝ) ≤ cE / (64 * Real.log 4) →
      (64 : ℝ) * (R.a : ℝ) ≤ (eps : ℝ) * (H : ℝ) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1
          ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
          ≤ (x : ℝ) →
      (eps : ℝ) / 2 ≤ |∫ m, (ArithmeticFunction.liouville (m + R.b) : ℝ)
          * (ArithmeticFunction.liouville (m + R.b + h) : ℝ) ∂(logMeasureAff R.a x ω)| →
      (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (R.a : ℝ))
          * |∫ m, (ArithmeticFunction.liouville (m + R.b) : ℝ)
              * (ArithmeticFunction.liouville (m + R.b + h) : ℝ) ∂(logMeasureAff R.a x ω)|
        ≤ |∫ m, fBridgeF_aff eps H R.a R.b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff R.a x ω)|)
    (cD3 : ℝ) (hcD3 : 0 < cD3) (H₀D3 : ℕ)
    (hD3 : ∀ (eps : ℚ) (H : ℕ), H₀D3 ≤ H →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      (eps : ℝ) ^ 2 ≤ 1 →
      cD3 / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
    (C : ℝ) (hC : 0 < C)
    (hcm : ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod R.a) = (((p : ℕ) * R.b : ℕ) : ZMod R.a) then
            (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ) else 0|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiAff R.a R.b h eps H, (1 / (H : ℝ) ^ 2)
                * ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2))
    (H : ℕ) [NeZero H] (hdvd : R.a ∣ H) (hlo : R.a * R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    (hH₀ : max H₀red H₀D3 ≤ H)
    (hepsc : (R.eps : ℝ) * (R.a : ℝ) * (h : ℝ) ≤ cE / (64 * Real.log 4))
    (hcount : (64 : ℝ) * (R.a : ℝ) ≤ (R.eps : ℝ) * (H : ℝ))
    (t g κ c₀ : ℝ) (ht : 0 < t) (hg : 0 < g)
    (hgle : g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
        / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    (hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasureAff R.a R.x R.ω] ≤ κ)
    (hbudget1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
        + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
        + shellError R.toChowlaRegime H t g κ
      ≤ cD3 / (4 * (R.a : ℝ)) * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)))
    (hbudget2 : ρ < c₀ * (R.eps : ℝ))
    (hfail : logChowlaFailsAff R.a R.b h R.eps R.x R.ω) : False := by
  sorry

/-! ## F4-S3 — THE AFFINE HEAD -/

/-- **F4-S3 (class C, THE HEAD) — `log_chowla_aff_of_door`.**  For `b < a`, `0 < h`,
`log(a·h) ≤ 7`, the circle-method SLOT `hcm` (F4b's producer, with its cap), the crown's payload
`hcrown` (the conclusion of `mrtUniformityXiL2AffW_holds_flat_stride`, `StridePairReceipt.lean:2121`,
at the caller's `A₀'` — supplied by the MR-side one-liner F4-S6, since this file cannot import
`Salt.MR`) and every `A₀`: the regime `Ra` of the crown, its door at grade `a·Zr·ρ + E` FORWARDED,
and beside it THE ENTROPY HALF: `∀ ρ' ≤ δ₀_aff, MRTUniformityXiL2AffW h Ra ρ' → ¬ logChowlaFailsAff`,
with `1/(838400·(ah)²) ≤ δ₀_aff` (the road's own re-mint at `k = ah`, F2 §2).

THE ORDER (the `h`-head's, `HloExportFlatH.lean:256-372`, plain threshold): (1) the leaves —
`obtain ⟨cE, hcE, hcEge, H₀red, hred⟩ := hreduce_holds_final_aff` (FIVE-WIDE: F4-R6d EXPORTS
`1/4 ≤ c` since v1.1 — §3 S-7, verdict A1; `hcEge` is READ from the export, never re-derived
from another existential's `c`),
`⟨cD3, hcD3, hcD3ge, H₀D3, hD3⟩ := primeWindow_sum_inv_ge_bounded`, `⟨C, hC, hCcap, hcm'⟩ := hcm`;
(2) THE PIN `ε := 1/(500·(a·h))` and the numerals — `hεcE : ε·a·h = 1/500 ≤ cE/(64·log 4)`
(`cE ≥ 1/4`, `log 4 < 1.3863`), `hε_D3 : ε ≤ (cD3/a)/16`, `hε_D3C : ε ≤ (cD3/a)/(16·C)` from
`C ≤ 6.55·h` (`hCcap`, `Real.log_two_lt_d9`), `hδ₀ge : 1/(838400·(ah)²) ≤ (cD3/a)/(16·C)·ε/4`
(the `h`-head's `hkey` at `a·h`, zero slack), `hε32 : ε ≤ 1/32`; (3) `β' := (cD3/a)·ε/(144·log 4)`
and `A₀' := max A₀ (max 162 (max (Real.exp (budgetX ε β') / 3.2 + 1)
(Real.log (Real.log ((max H₀red H₀D3 : ℕ) : ℝ)) / 3.2 + 1)))`; (4) THE CROWN at `A₀'` (the
binder `hcrown`): `⟨ε, A, …, Ra, hRa, hRb, hReps, hHloB, hdes, ρ, Zr, E, …, hdoorC⟩` — forward
its payload; (5) `δ₀ := (cD3/a)/(16·C)·ε/4`; then `intro ρ' hρ'pos hρ' hdoor hfail`;
(6) `obtain ⟨H, hlo, hhi, hdvd, hMI⟩ := entropy_decrementAff Ra.toChowlaRegime` (Tao's range
`a·Ra.Hlo ≤ H`), `hI` by `mutualInfo_window_comm_aff`; `hH₀` from `nat_le_flatDesignBase` +
`hHloB` + `hlo`; `hcount : 64·a ≤ ε·H` from `Ra.hcoprime` (`a ≤ ε²·Hlo/2`), `hε32`, `Hlo ≤ H`;
(7) `hbudget1_witness Ra.toChowlaRegime H (cD3/a) C …` (`SpineFinal.lean:598`) at `hfloor` from
`budgetFloor_le_flatDesignBase` + `hHloB` + `hlo` (its `cD3/a/4` against the core's `cD3/(4·a)`
is `div_div` — v1.1, verdict A8(iv)); `hbudget2 : ρ' < (cD3/a)/(16·C)·ε` from
`hρ'`; (8) `spine_False_core_xi_sq_aff`.  `hcrown`'s shape is the crown's conclusion verbatim,
at `A₀'`. -/
theorem log_chowla_aff_of_door (a b h : ℕ) (ha : 0 < a) (hh : 0 < h) (hba : b < a)
    (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7)
    (hcm : ∃ C : ℝ, 0 < C ∧ C ≤ (h : ℝ) * (1 + 2 * (2 * Real.log 4)) ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ) else 0|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiAff a b h eps H, (1 / (H : ℝ) ^ 2)
                * ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2))
    (hcrown : ∀ A₀' : ℝ,
      ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
        ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀' ≤ A ∧
        ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
          flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
          ∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * ((a * h : ℕ) : ℝ) ^ 2) ∧
            1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
            E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
                * (Real.log (Ra.ω : ℝ) - 1)) ∧
            MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E))
    (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
        flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
        (∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * ((a * h : ℕ) : ℝ) ^ 2) ∧
          1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
          E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
              * (Real.log (Ra.ω : ℝ) - 1)) ∧
          MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E)) ∧
        ∃ δ₀ : ℝ, 0 < δ₀ ∧ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) ≤ δ₀ ∧
          ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ δ₀ → MRTUniformityXiL2AffW h Ra ρ' →
            ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω := by
  sorry

/-! ## F4-S4 — the `(1, 0)` compat of the shell -/

/-- **F4-S4 (class B) — the affine shell at `(1, 0)` recovers the `h`-shell's contradiction,
RESTATED v1.1 (verdict A2(c)) so that it can fail.**  The four slot hypotheses `hI`, `h211`,
`hcirc`, `hdoor` are in the AFFINE vocabulary at the regime `R` with `R.a = 1`, `b = 0`
(`logMeasureAff R.a R.x R.ω`, `fBridgeF_aff R.eps H R.a 0 h`, the CLASS-FILTERED inner sum over
`bigXiAff R.a 0 h R.eps H`, `MRTUniformityXiL2AffW h (ChowlaRegimeAff.ofRegime R 0 _)`); the REST
are the `h`-shell's binders (`Theorem23Shell.lean:624`) VERBATIM — the PLAIN range `R.Hlo ≤ H` with
NO `R.a ∣ H`, and `shellError R H t g κ` at the plain regime.  Discharge:
`log_chowla_two_shell_xi_sq_aff h (ChowlaRegimeAff.ofRegime R 0 (Nat.zero_le _))` with the range
bridged through `hR1` — `hdvd : R.a ∣ H` from `one_dvd`, `hlo' : R.a * R.Hlo ≤ H` from `one_mul` —
and `shellError` at `ofRegime_toChowlaRegime` (`rfl`).  The v1 form restated the `h`-shell plus an
unused `hR1` and could not fail; here the range bridges at `R.a = 1` are LOAD-BEARING: the receipt
says the affine shell's Tao-range demand is INVISIBLE at stride `1`, and nothing more. -/
theorem log_chowla_two_shell_xi_sq_aff_one_zero (h : ℕ)
    (R : ChowlaRegime) (hR1 : R.a = 1) {H : ℕ} [NeZero H] (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    (hH : 3 ≤ H) (hlog : 1 ≤ Real.log (H : ℝ)) (hne : (primeWindow R.eps H).Nonempty)
    (hreg : Real.sqrt (H : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) / 2)
    (hhead : 8 * (PH R.eps H : ℝ) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ))
    {t : ℝ} (ht : 0 < t) {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
        / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    {κ : ℝ} (hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasureAff R.a R.x R.ω] ≤ κ)
    {c₁ : ℝ} (hc₁ : 0 < c₁)
    (h211 : c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ m, fBridgeF_aff R.eps H R.a 0 h (liouvilleWindow H m) (residueWindow R.eps H m)
            ∂(logMeasureAff R.a R.x R.ω)|)
    {C : ℝ} (hC : 0 < C)
    (hcirc : ∀ m : ℕ,
      |∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod R.a) = (((p : ℕ) * 0 : ℕ) : ZMod R.a) then
            (windowVal H (liouvilleWindow H m) j : ℝ)
              * (windowVal H (liouvilleWindow H m) (j + (p : ℕ) * h) : ℝ) else 0|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiAff R.a 0 h R.eps H, (1 / (H : ℝ) ^ 2)
                * ‖ZMod.dft (fun j : ZMod H =>
                    (windowVal H (liouvilleWindow H m) (ZMod.val j) : ℂ)) ξ‖ ^ 2))
    {ρ c₀ : ℝ} (hdoor : MRTUniformityXiL2AffW h (ChowlaRegimeAff.ofRegime R 0 (Nat.zero_le _)) ρ)
    (hbudget1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
          + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + shellError R H t g κ
        ≤ c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)))
    (hbudget2 : ρ < c₀ * (R.eps : ℝ)) :
    False := by
  sorry

end Salt.Entropy.Chowla
