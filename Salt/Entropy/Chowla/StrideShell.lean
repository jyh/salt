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
(F4b S-1, 2026-09-04 16:1x: the slot's `∀` carries `a ∣ H →` — `bigXiAff`'s grid is ℕ-division,
every
consumer holds `hdvd`, and the producer needs it; the slot no longer demands the estimate where
the object is undefined)
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
  unfold budgetFloor flatDesignBase
  exact Nat.ceil_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hX))

/-- **F4-S0b (class B).**  A natural below the flat design base: for `loglog n ≤ 3.2·A`,
`n ≤ flatDesignBase A`.  `n ≤ 1` is trivial (`flatDesignBase A ≥ 1`, `Nat.one_le_ceil`-shape);
for `2 ≤ n`, `log n > 0`, `Real.le_log_iff_exp_le`, `Real.exp_le_exp`, then `Nat.le_ceil`. -/
theorem nat_le_flatDesignBase (n : ℕ) (A : ℝ) (hn : Real.log (Real.log (n : ℝ)) ≤ 3.2 * A) :
    n ≤ flatDesignBase A := by
  have hone : (1 : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by
    have h1 := Real.add_one_le_exp (Real.exp (3.2 * A))
    have h2 := Real.exp_pos (3.2 * A)
    linarith
  have hkey : (n : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hlogpos : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by linarith)
      have h2 : Real.log (n : ℝ) ≤ Real.exp (3.2 * A) :=
        (Real.log_le_iff_le_exp hlogpos).mp hn
      exact (Real.log_le_iff_le_exp hnpos).mp h2
    · have hn1 : (n : ℝ) ≤ 1 := by exact_mod_cast h1
      linarith
  have hceil := Nat.le_ceil (Real.exp (Real.exp (3.2 * A)))
  have hfin : (n : ℝ) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    unfold flatDesignBase; linarith
  exact_mod_cast hfin

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
  haveI hpm : IsProbabilityMeasure (logMeasure R.x R.ω) :=
    isProbabilityMeasure_logMeasure R.hx R.hω
  have hHpos : 0 < H := NeZero.pos H
  have hlogpos : 0 < Real.log (H : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hApos : 0 < C * ((H : ℝ) / Real.log (H : ℝ)) :=
    mul_pos hC (div_pos (by exact_mod_cast hHpos) hlogpos)
  have heps1R : (R.eps : ℝ) ≤ 1 := by
    have hle : R.eps ≤ 1 := le_trans R.heps1 (by norm_num)
    exact_mod_cast hle
  have hlo' : R.Hlo ≤ H := le_trans (Nat.le_mul_of_pos_left _ R.ha) hlo
  have hcop : Nat.Coprime R.a (PH R.eps H) := coprime_PH_of_le R.ha R.hcoprime hlo'
  -- THE RELABEL: the residue entropy is the landed one, so `shellError` is unchanged.
  have hent : H[residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      = H[residueWindow R.eps H ; logMeasure R.x R.ω] :=
    entropy_residueWindow_aff_eq R.eps H hcop
  -- abbreviations (SITE 3's spelling for `gm`)
  set gm : ℕ → ℝ := fun m =>
      ∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
        if ((j + 1 : ℕ) : ZMod R.a) = (((p : ℕ) * R.b : ℕ) : ZMod R.a) then
          (windowVal H (liouvilleWindow H m) j : ℝ)
            * (windowVal H (liouvilleWindow H m) (j + (p : ℕ) * h) : ℝ) else 0 with hgm
  set door : ℝ := ∑ ξ ∈ bigXiAff R.a R.b h R.eps H, (1 / (H : ℝ) ^ 2)
      * ∫ m, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasureAff R.a R.x R.ω) with hdoorS
  set RHS : ℕ → ℝ := fun m => C * ((H : ℝ) / Real.log (H : ℝ))
      * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiAff R.a R.b h R.eps H, (1 / (H : ℝ) ^ 2)
          * ‖ZMod.dft (fun j : ZMod H =>
              (windowVal H (liouvilleWindow H m) (ZMod.val j) : ℂ)) ξ‖ ^ 2) with hRHS
  -- (I) the affine `outer_combine_aff` mass lower bound (`shellError` folds in, defeq).
  have hoc : c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
      - shellError R.toChowlaRegime H t g κ
      ≤ |∫ m, gm m ∂(logMeasureAff R.a R.x R.ω)| := by
    have key := outer_combine_aff R.eps H R.a R.b h R.hx R.hω R.hωx hcop R.heps heps1R hne hreg
      hH hlog hhead ht hg hgle hI hc₁ h211
    rw [hent] at key
    exact key
  have hcirc' : ∀ m, |gm m| ≤ RHS m := hcirc
  -- Bridge B, step 1+2: `|∫ gm| ≤ ∫ RHS`.
  have hB : |∫ m, gm m ∂(logMeasureAff R.a R.x R.ω)|
      ≤ ∫ m, RHS m ∂(logMeasureAff R.a R.x R.ω) :=
    le_trans abs_integral_le_integral_abs
      (integral_mono_ae (integrable_of_finiteSupport _) (integrable_of_finiteSupport _)
        (Filter.Eventually.of_forall hcirc'))
  -- Bridge B, step 3: Bridge A SQUARED, per `ξ`, at the stride measure.
  have hRHSeq : ∫ m, RHS m ∂(logMeasureAff R.a R.x R.ω)
      = C * ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2 + door) := by
    rw [hRHS, integral_const_mul]
    congr 1
    rw [integral_add (integrable_const _) (integrable_of_finiteSupport _), integral_const,
      probReal_univ, one_smul,
      integral_finsetSum (bigXiAff R.a R.b h R.eps H) (fun ξ _ => integrable_of_finiteSupport _)]
    congr 1
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [integral_const_mul]
    congr 1
    exact integral_congr_ae
      (Filter.Eventually.of_forall (fun m =>
        congrArg (fun z : ℝ => z ^ 2) (windowExpSum_norm_eq_dft m ξ).symm))
  -- (★): assemble the chain.
  have hstar : c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
      - shellError R.toChowlaRegime H t g κ
      ≤ C * ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2 + door) :=
    le_trans hoc (le_trans hB (le_of_eq hRHSeq))
  have hmul : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
      ≤ C * ((H : ℝ) / Real.log (H : ℝ)) * door := by
    have hexp : C * ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2 + door)
        = C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + C * ((H : ℝ) / Real.log (H : ℝ)) * door := by ring
    linarith [hstar, hbudget1, hexp]
  have hlower : c₀ * (R.eps : ℝ) ≤ door := le_of_mul_le_mul_left hmul hApos
  exact contradiction_of_mrtDoorXiL2AffW h R hdvd hlo hhi hdoor hbudget2 hlower

/-! ## F4-S2 — the spine contradiction core at the affine forms -/

/-- **F4-S2 (class B) — the `L²` spine contradiction core at the affine forms.**
`spine_False_core_xi_sq_flat_h` (`HloExportFlatH.lean:67`, private) with the seed
`singleCorr_of_failsAff'` (F1-N2), the reduce `hred` in `hreduce_holds_final_aff`'s shape at the
GATE `ε·a·h ≤ cE/(64·log 4)` and the count slack `64·a ≤ ε·H`, the Mertens leaf `hD3` verbatim,
the circle SLOT `hcm` at the filtered sum over `bigXiAff`, the shell
`log_chowla_two_shell_xi_sq_aff`.
The regime discharges are `R.toChowlaRegime`'s (`sqrt_le_window_at`, `omega_big_at`, `x_big_at`,
`pH_headroom_at`, `Regime.lean:195-261`, at `hlo' : R.Hlo ≤ H` from `hlo` and `R.ha`);
`hcop := coprime_PH_of_le R.ha R.hcoprime hlo'`; `hlog2 : 2 ≤ log ω` as at `h`; `h211` at
`c₁ := cD3/(4·R.a)` from `hredH` (`(1/2)·SP·(H/a)·X ≥ (1/2)·(H/a)·(cD3/log H)·(ε/2)`); `hcard`
from `primeWindow_card_le_of_regime`; `hcirc` from `hcm` at `liouvilleWindow H m`
(`abs_liouvilleWindow_le_one`).  Threshold-agnostic in `κ`, as at `h`. -/
theorem spine_False_core_xi_sq_aff (h : ℕ) (_hh : 0 < h) (R : ChowlaRegimeAff)
    (_hblt : R.b < R.a) {ρ : ℝ}
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
      R.a ∣ H →
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
  have hepsRpos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hepshalf : (R.eps : ℝ) ≤ 1 / 2 := by
    have hq : (2 : ℝ) * (R.eps : ℝ) ≤ 1 := by
      exact_mod_cast (by linarith [R.heps1] : (2 : ℚ) * R.eps ≤ 1)
    linarith
  have hepssq : (R.eps : ℝ) ^ 2 ≤ 1 := by nlinarith [hepshalf, hepsRpos]
  have haRpos : (0 : ℝ) < (R.a : ℝ) := by exact_mod_cast R.ha
  -- the affine range's plain shadow
  have hlo' : R.Hlo ≤ H := le_trans (Nat.le_mul_of_pos_left _ R.ha) hlo
  have hcop : Nat.Coprime R.a (PH R.eps H) := coprime_PH_of_le R.ha R.hcoprime hlo'
  -- floor bookkeeping
  have hHnatM : 4000000 ≤ H := le_trans R.hHlo_floor hlo'
  have hH3 : 3 ≤ H := by omega
  have hH₀red : H₀red ≤ H := le_trans (le_max_left _ _) hH₀
  have hH₀D3 : H₀D3 ≤ H := le_trans (le_max_right _ _) hH₀
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHnatM
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  have hlogH : 1 ≤ Real.log (H : ℝ) := by
    rw [Real.le_log_iff_exp_le hHpos]
    exact le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
  have hlogHpos : 0 < Real.log (H : ℝ) := by linarith
  -- the regime discharges, at the plain shadow of Tao's range
  have hreg : Real.sqrt (H : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) / 2 :=
    sqrt_le_window_at R.toChowlaRegime hlo' hhi
  have hsqrt2000 : (2000 : ℝ) ≤ Real.sqrt (H : ℝ) := by
    rw [show (2000 : ℝ) = Real.sqrt 4000000 by
      rw [show (4000000 : ℝ) = 2000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hHR
  have h4 : (4 : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) := by nlinarith [hreg, hsqrt2000]
  have hωbig : (16 / (R.eps : ℝ)) * Real.log ((R.eps : ℝ) ^ 2 * (H : ℝ))
      + 64 / (R.eps : ℝ) + 1 ≤ Real.log (R.ω : ℝ) := omega_big_at R.toChowlaRegime hhi h4
  have hxbig : (R.ω : ℝ) * (H : ℝ)
      + 48 * (R.ω : ℝ) * (1 + 2 / (R.eps : ℝ) ^ 2) / (R.eps : ℝ) ≤ (R.x : ℝ) :=
    x_big_at R.toChowlaRegime hhi
  have hhead : 8 * (PH R.eps H : ℝ) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ) :=
    pH_headroom_at R.toChowlaRegime hhi
  -- 2 ≤ log ω
  have hlogε2H_nn : (0 : ℝ) ≤ Real.log ((R.eps : ℝ) ^ 2 * (H : ℝ)) :=
    Real.log_nonneg (by linarith [h4])
  have hterm1 : (0 : ℝ) ≤ (16 / (R.eps : ℝ)) * Real.log ((R.eps : ℝ) ^ 2 * (H : ℝ)) :=
    mul_nonneg (by positivity) hlogε2H_nn
  have h64 : (128 : ℝ) ≤ 64 / (R.eps : ℝ) := by
    rw [le_div_iff₀ hepsRpos]; nlinarith [hepshalf]
  have hlog2 : 2 ≤ Real.log (R.ω : ℝ) := by nlinarith [hωbig, hterm1, h64]
  -- the D3 Mertens lower bound + nonemptiness
  set SP : ℝ := ∑ p ∈ primeWindow R.eps H, (1 / (p : ℝ)) with hSP
  have hmert : cD3 / Real.log (H : ℝ) ≤ SP := hD3 R.eps H hH₀D3 hreg hepssq
  have hSPnn : (0 : ℝ) ≤ SP := Finset.sum_nonneg (fun p _ => by positivity)
  have hSPpos : (0 : ℝ) < SP := lt_of_lt_of_le (div_pos hcD3 hlogHpos) hmert
  have hne : (primeWindow R.eps H).Nonempty := by
    rcases (primeWindow R.eps H).eq_empty_or_nonempty with he | hn
    · exact absurd (hSP.trans (by rw [he, Finset.sum_empty])) (ne_of_gt hSPpos)
    · exact hn
  -- the affine single-correlation seed and the affine reduce (the `h211` producer)
  set X : ℝ := |∫ m, (ArithmeticFunction.liouville (m + R.b) : ℝ)
      * (ArithmeticFunction.liouville (m + R.b + h) : ℝ)
        ∂(logMeasureAff R.a R.x R.ω)| with hXdef
  have hseed : (R.eps : ℝ) / 2 ≤ X :=
    singleCorr_of_failsAff' R.a R.b h R.eps R.hx R.hω R.hωx hlog2 hfail
  have hredH : (1 / 2) * SP * ((H : ℝ) / (R.a : ℝ)) * X
      ≤ |∫ m, fBridgeF_aff R.eps H R.a R.b h (liouvilleWindow H m) (residueWindow R.eps H m)
          ∂(logMeasureAff R.a R.x R.ω)| :=
    hred R.eps H R.x R.ω hcop R.hx R.hω R.hωx R.heps hepssq hH3 hlogH h4 hreg hH₀red
      hepsc hcount hωbig hxbig hseed
  -- the concrete `h211` at the coefficient `c₁ = cD3/(4·a)`
  have hAX : (cD3 / Real.log (H : ℝ)) * ((R.eps : ℝ) / 2) ≤ SP * X :=
    mul_le_mul hmert hseed (by positivity) hSPnn
  have h211 : cD3 / (4 * (R.a : ℝ)) * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
      ≤ |∫ m, fBridgeF_aff R.eps H R.a R.b h (liouvilleWindow H m) (residueWindow R.eps H m)
          ∂(logMeasureAff R.a R.x R.ω)| := by
    calc cD3 / (4 * (R.a : ℝ)) * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        = (1 / 2) * ((H : ℝ) / (R.a : ℝ))
            * ((cD3 / Real.log (H : ℝ)) * ((R.eps : ℝ) / 2)) := by
          field_simp; ring
      _ ≤ (1 / 2) * ((H : ℝ) / (R.a : ℝ)) * (SP * X) :=
          mul_le_mul_of_nonneg_left hAX (by positivity)
      _ = (1 / 2) * SP * ((H : ℝ) / (R.a : ℝ)) * X := by ring
      _ ≤ _ := hredH
  -- the SQUARED circle-method bound at the class filter, at the Liouville window
  have hcard : ((primeWindow R.eps H).card : ℝ)
      ≤ (2 * Real.log 4) * ((R.eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) :=
    primeWindow_card_le_of_regime R.eps H hreg hH3
  have hcirc : ∀ m : ℕ,
      |∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod R.a) = (((p : ℕ) * R.b : ℕ) : ZMod R.a) then
            (windowVal H (liouvilleWindow H m) j : ℝ)
              * (windowVal H (liouvilleWindow H m) (j + (p : ℕ) * h) : ℝ) else 0|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiAff R.a R.b h R.eps H, (1 / (H : ℝ) ^ 2)
                * ‖ZMod.dft (fun j : ZMod H =>
                    (windowVal H (liouvilleWindow H m) (ZMod.val j) : ℂ)) ξ‖ ^ 2) :=
    fun m => hcm R.eps H (liouvilleWindow H m)
      (fun i => abs_liouvilleWindow_le_one H m i) hdvd hcard
  exact log_chowla_two_shell_xi_sq_aff h R hdvd hlo hhi hH3 hlogH hne hreg hhead ht hg hgle hI
    (by positivity) h211 hC hcirc hdoor hbudget1 hbudget2

/-! ## F4-S3 — THE AFFINE HEAD -/

set_option maxHeartbeats 1600000 in
-- THE HEAD is one large elaboration: the crown's payload, the five-wide reduce leaf and the
-- circle SLOT all sit in the context while the pin's numerals and the budget witness are
-- discharged, exactly as at the `h`-lane's flat head (`HloExportFlatH.lean:398`, 1000000)
-- and the affine budget (`StrideReduce.lean:732`, 1600000); the ceiling here is the latter.
/-- **F4-S3 (class C, THE HEAD) — `log_chowla_aff_of_door`.**  For `b < a`, `0 < h`,
`log(a·h) ≤ 7`, the circle-method SLOT `hcm` (F4b's producer, with its cap), the crown's payload
`hcrown` (the conclusion of `mrtUniformityXiL2AffW_holds_flat_stride`,
`StridePairReceipt.lean:2121`,
at the caller's `A₀'` — supplied by the MR-side one-liner F4-S6, since this file cannot import
`Salt.MR`) and every `A₀`: the regime `Ra` of the crown, its door at grade `a·Zr·ρ + E` FORWARDED,
and beside it THE ENTROPY HALF:
`∀ ρ' ≤ δ₀_aff, MRTUniformityXiL2AffW h Ra ρ' → ¬ logChowlaFailsAff`,
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
    (_hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7)
    (hcm : ∃ C : ℝ, 0 < C ∧ C ≤ (h : ℝ) * (1 + 2 * (2 * Real.log 4)) ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      a ∣ H →
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
  -- ⟦(1) THE LEAVES⟧
  obtain ⟨cE, hcE, hcEge, H₀red, hred⟩ := hreduce_holds_final_aff
  obtain ⟨cD3, hcD3, hcD3ge, H₀D3, hD3⟩ := primeWindow_sum_inv_ge_bounded
  obtain ⟨C, hC, hCcap, hcm'⟩ := hcm
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hane : (a : ℝ) ≠ 0 := ne_of_gt haR
  have hhne : (h : ℝ) ≠ 0 := ne_of_gt hhR
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hkeq : ((a * h : ℕ) : ℝ) = (a : ℝ) * (h : ℝ) := by push_cast; ring
  have hkpos : (0 : ℝ) < ((a * h : ℕ) : ℝ) := by rw [hkeq]; positivity
  have hkne : ((a * h : ℕ) : ℝ) ≠ 0 := ne_of_gt hkpos
  have hk1 : (1 : ℝ) ≤ ((a * h : ℕ) : ℝ) := by rw [hkeq]; nlinarith
  -- the cap read: `C ≤ 6.55·h` (`log 4 = 2·log 2 < 1.3863`)
  have hCnum : C ≤ (h : ℝ) * (655 / 100) := by
    refine le_trans hCcap ?_
    have hb : (1 : ℝ) + 2 * (2 * Real.log 4) ≤ 655 / 100 := by rw [hlog4eq]; linarith
    exact mul_le_mul_of_nonneg_left hb hhR.le
  -- ⟦(2)–(3) THE PIN, THE DESIGN CONSTANT AND THE HEAD'S OWN FLOORS⟧
  obtain ⟨ε₀, hε₀def⟩ : ∃ q : ℚ, q = 1 / (500 * ((a * h : ℕ) : ℚ)) := ⟨_, rfl⟩
  obtain ⟨β', hβ'def⟩ : ∃ r : ℝ, r = cD3 / (a : ℝ) * (ε₀ : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have h32 : (3.2 : ℝ) = 16 / 5 := by norm_num
  obtain ⟨A₀', hA₀'def⟩ : ∃ r : ℝ, r = max A₀ (max 162 (max
      (Real.exp (budgetX (ε₀ : ℝ) β'))
      (Real.log (Real.log ((max H₀red H₀D3 : ℕ) : ℝ))))) := ⟨_, rfl⟩
  -- ⟦(4) THE CROWN AT `A₀'`⟧
  obtain ⟨ε, A, hεpos, _hεge, hεeq, hA162, hA₀'A, Ra, hRa, hRb, hReps, hHloB, hdes,
    ρ, Zr, Ecr, hρpos, hρle, hZr1, hZr102, hEcr0, hEcrle, hdoorC⟩ := hcrown A₀'
  have hεε₀ : ε = ε₀ := hεeq.trans hε₀def.symm
  have hA₀le : A₀ ≤ A :=
    le_trans (by rw [hA₀'def]; exact le_max_left _ _) hA₀'A
  have hXA : Real.exp (budgetX (ε₀ : ℝ) β') ≤ 3.2 * A := by
    have h1 : Real.exp (budgetX (ε₀ : ℝ) β') ≤ A := by
      refine le_trans ?_ hA₀'A
      rw [hA₀'def]
      exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    rw [h32]; linarith
  have hnatA : Real.log (Real.log ((max H₀red H₀D3 : ℕ) : ℝ)) ≤ 3.2 * A := by
    have h1 : Real.log (Real.log ((max H₀red H₀D3 : ℕ) : ℝ)) ≤ A := by
      refine le_trans ?_ hA₀'A
      rw [hA₀'def]
      exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    rw [h32]; linarith
  -- ⟦THE PIN'S NUMERALS⟧
  have herR : (ε : ℝ) = 1 / (500 * ((a * h : ℕ) : ℝ)) := by
    rw [hεeq]; push_cast; ring
  have herpos : (0 : ℝ) < (ε : ℝ) := by rw [herR]; positivity
  have herk : (ε : ℝ) * ((a * h : ℕ) : ℝ) = 1 / 500 := by rw [herR]; field_simp
  have herah : (ε : ℝ) * ((a : ℝ) * (h : ℝ)) = 1 / 500 := by rw [← hkeq]; exact herk
  have her500 : (ε : ℝ) ≤ 1 / 500 := by
    rw [herR]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have her32 : (ε : ℝ) ≤ 1 / 32 := by linarith
  have herhalf : (ε : ℝ) ≤ 1 / 2 := by linarith
  have hepsa : (ε : ℝ) * (a : ℝ) ≤ 1 / 500 := by
    nlinarith [herah, mul_nonneg (mul_pos herpos haR).le (by linarith : (0:ℝ) ≤ (h:ℝ) - 1)]
  -- the reduce's GATE, at `64` (not `32`)
  have hεcE : (ε : ℝ) * (a : ℝ) * (h : ℝ) ≤ cE / (64 * Real.log 4) := by
    rw [show (ε : ℝ) * (a : ℝ) * (h : ℝ) = (ε : ℝ) * ((a : ℝ) * (h : ℝ)) by ring, herah,
      le_div_iff₀ (by positivity), hlog4eq]
    linarith
  -- the two `ε`-pin arms of the budget witness
  have hε_D3 : (ε : ℝ) ≤ cD3 / (a : ℝ) / 16 := by
    rw [div_div, le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) * 16)]
    have hrw : (ε : ℝ) * ((a : ℝ) * 16) = 16 * ((ε : ℝ) * (a : ℝ)) := by ring
    rw [hrw]; linarith
  have hε_D3C : (ε : ℝ) ≤ cD3 / (a : ℝ) / (16 * C) := by
    rw [div_div, le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) * (16 * C))]
    have hrw : (ε : ℝ) * ((a : ℝ) * (16 * C)) = 16 * C * ((ε : ℝ) * (a : ℝ)) := by ring
    rw [hrw]
    have hstep : 16 * C * ((ε : ℝ) * (a : ℝ))
        ≤ 16 * ((h : ℝ) * (655 / 100)) * ((ε : ℝ) * (a : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ (mul_pos herpos haR).le
      linarith
    have heq2 : 16 * ((h : ℝ) * (655 / 100)) * ((ε : ℝ) * (a : ℝ))
        = (1048 / 10) * ((ε : ℝ) * ((a : ℝ) * (h : ℝ))) := by ring
    rw [heq2, herah] at hstep
    linarith
  -- ⟦(5) THE `δ₀` FLOOR⟧ the road's re-mint at `k = a·h`, exact at zero slack
  have hc₀pos : (0 : ℝ) < cD3 / (a : ℝ) / (16 * C) :=
    div_pos (div_pos hcD3 haR) (mul_pos (by norm_num) hC)
  have hδ₀pos : (0 : ℝ) < cD3 / (a : ℝ) / (16 * C) * (ε : ℝ) / 4 :=
    div_pos (mul_pos hc₀pos herpos) (by norm_num)
  have hkey : (5 : ℝ) / (2096 * ((a * h : ℕ) : ℝ)) ≤ cD3 / (a : ℝ) / (16 * C) := by
    rw [div_div, le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) * (16 * C))]
    have hfac : (0 : ℝ) ≤ (5 : ℝ) / (2096 * ((a * h : ℕ) : ℝ)) := by positivity
    have h1 : (5 : ℝ) / (2096 * ((a * h : ℕ) : ℝ)) * ((a : ℝ) * (16 * C))
        ≤ (5 : ℝ) / (2096 * ((a * h : ℕ) : ℝ))
            * ((a : ℝ) * (16 * ((h : ℝ) * (655 / 100)))) := by
      refine mul_le_mul_of_nonneg_left ?_ hfac
      refine mul_le_mul_of_nonneg_left ?_ haR.le
      linarith
    have h2 : (5 : ℝ) / (2096 * ((a * h : ℕ) : ℝ))
        * ((a : ℝ) * (16 * ((h : ℝ) * (655 / 100)))) = 1 / 4 := by
      rw [hkeq]; field_simp; ring
    linarith
  have hδ₀ge : (1 : ℝ) / (838400 * ((a * h : ℕ) : ℝ) ^ 2)
      ≤ cD3 / (a : ℝ) / (16 * C) * (ε : ℝ) / 4 := by
    have hstep : (1 : ℝ) / (838400 * ((a * h : ℕ) : ℝ) ^ 2)
        = (5 : ℝ) / (2096 * ((a * h : ℕ) : ℝ))
            * (1 / (500 * ((a * h : ℕ) : ℝ))) / 4 := by
      field_simp; ring
    rw [hstep, herR]
    have hpos : (0 : ℝ) < 1 / (500 * ((a * h : ℕ) : ℝ)) := by positivity
    gcongr
  -- ⟦THE PACKAGE⟧ the crown's payload forwarded, the entropy half beside it
  refine ⟨ε, A, hεpos, hεeq, hA162, hA₀le, Ra, hRa, hRb, hReps, hHloB, hdes,
    ⟨ρ, Zr, Ecr, hρpos, hρle, hZr1, hZr102, hEcr0, hEcrle, hdoorC⟩,
    cD3 / (a : ℝ) / (16 * C) * (ε : ℝ) / 4, hδ₀pos, hδ₀ge, ?_⟩
  intro ρ' _hρ'pos hρ' hdoor hfail
  have hRe : Ra.eps = ε := hReps
  have hblt : Ra.b < Ra.a := by rw [hRa, hRb]; exact hba
  -- ⟦(6) THE AFFINE DECREMENT AT TAO'S RANGE⟧
  obtain ⟨H, hlo, hhi, hdvd, hMI⟩ := entropy_decrementAff Ra.toChowlaRegime
  have hlo' : Ra.Hlo ≤ H := le_trans (Nat.le_mul_of_pos_left _ Ra.ha) hlo
  have hH4 : 4000000 ≤ H := le_trans Ra.hHlo_floor hlo'
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow Ra.eps H : liouvilleWindow H ; logMeasureAff Ra.a Ra.x Ra.ω]
      ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
    rw [← mutualInfo_window_comm_aff Ra.toChowlaRegime H]; exact hMI
  have hH₀ : max H₀red H₀D3 ≤ H :=
    le_trans (le_trans (nat_le_flatDesignBase (max H₀red H₀D3) A hnatA) hHloB) hlo'
  have hepscR : (Ra.eps : ℝ) * (Ra.a : ℝ) * (h : ℝ) ≤ cE / (64 * Real.log 4) := by
    rw [hRe, hRa]; exact hεcE
  -- the COUNT slack `64·a ≤ ε·H`, paid by the regime's own coprimality floor and `ε ≤ 1/32`
  have hcopR : ((Ra.a : ℕ) : ℝ) ≤ (Ra.eps : ℝ) ^ 2 * ((Ra.Hlo : ℕ) : ℝ) / 2 := by
    exact_mod_cast Ra.hcoprime
  have hHloRR : ((Ra.Hlo : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo'
  have hcountR : (64 : ℝ) * (Ra.a : ℝ) ≤ (Ra.eps : ℝ) * (H : ℝ) := by
    rw [hRe] at hcopR ⊢
    have hEHnn : (0 : ℝ) ≤ (ε : ℝ) * (H : ℝ) := mul_nonneg herpos.le (Nat.cast_nonneg H)
    have h1 : (Ra.a : ℝ) ≤ (ε : ℝ) ^ 2 * (H : ℝ) / 2 := by
      have hmono : (ε : ℝ) ^ 2 * ((Ra.Hlo : ℕ) : ℝ) ≤ (ε : ℝ) ^ 2 * (H : ℝ) :=
        mul_le_mul_of_nonneg_left hHloRR (sq_nonneg _)
      linarith only [hcopR, hmono]
    have h2 : (ε : ℝ) ^ 2 * (H : ℝ) ≤ (1 / 32) * ((ε : ℝ) * (H : ℝ)) := by
      have h3 := mul_le_mul_of_nonneg_right her32 hEHnn
      have h4 : (ε : ℝ) ^ 2 * (H : ℝ) = (ε : ℝ) * ((ε : ℝ) * (H : ℝ)) := by ring
      rw [h4]; exact h3
    linarith only [h1, h2]
  have hfailR : logChowlaFailsAff Ra.a Ra.b h Ra.eps Ra.x Ra.ω := by
    rw [hRa, hRb]; exact hfail
  have hredR := fun (eps : ℚ) (H' x' ω' : ℕ) (hc : Nat.Coprime Ra.a (PH eps H')) =>
    hred Ra.a Ra.b h eps H' x' ω' hh Ra.ha hblt hc
  have hcmR := hcm'
  rw [← hRa, ← hRb] at hcmR
  -- ⟦(7) THE PLAIN SPINE-BUDGET WITNESS AT `cD3/a`⟧
  have hεhalfR : (Ra.eps : ℝ) ≤ 1 / 2 := by rw [hRe]; exact herhalf
  have hε_D3R : (Ra.eps : ℝ) ≤ cD3 / (a : ℝ) / 16 := by rw [hRe]; exact hε_D3
  have hε_D3CR : (Ra.eps : ℝ) ≤ cD3 / (a : ℝ) / (16 * C) := by rw [hRe]; exact hε_D3C
  have hfloorH : budgetFloor (Ra.eps : ℝ)
      (cD3 / (a : ℝ) * (Ra.eps : ℝ) / (144 * Real.log 4)) ≤ H := by
    have hX : Real.exp (budgetX (Ra.eps : ℝ)
        (cD3 / (a : ℝ) * (Ra.eps : ℝ) / (144 * Real.log 4))) ≤ 3.2 * A := by
      rw [hRe, hεε₀, ← hβ'def]; exact hXA
    exact le_trans (budgetFloor_le_flatDesignBase _ _ A hX) (le_trans hHloB hlo')
  obtain ⟨t, g, ht, hg, hgle, hbud1⟩ :=
    hbudget1_witness Ra.toChowlaRegime H (cD3 / (a : ℝ)) C (div_pos hcD3 haR) hC
      hεhalfR hε_D3R hε_D3CR hhi hfloorH
  have hbudget1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (cD3 / (a : ℝ) / (16 * C) * (Ra.eps : ℝ))
        + C * ((H : ℝ) / Real.log (H : ℝ)) * (Ra.eps : ℝ) ^ 2
        + shellError Ra.toChowlaRegime H t g
            ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))))
      ≤ cD3 / (4 * (Ra.a : ℝ)) * ((Ra.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) := by
    have heq : cD3 / (4 * (Ra.a : ℝ)) = cD3 / (a : ℝ) / 4 := by
      rw [hRa, div_div]; ring
    rw [heq]; exact hbud1
  have hbudget2 : ρ' < cD3 / (a : ℝ) / (16 * C) * (Ra.eps : ℝ) := by
    rw [hRe]
    have hp : (0 : ℝ) < cD3 / (a : ℝ) / (16 * C) * (ε : ℝ) := mul_pos hc₀pos herpos
    linarith only [hρ', hp]
  -- ⟦(8) THE CORE⟧
  exact spine_False_core_xi_sq_aff h hh Ra hblt hdoor cE hcE H₀red hredR cD3 hcD3 H₀D3 hD3
    C hC hcmR H hdvd hlo hhi hH₀ hepscR hcountR t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) (cD3 / (a : ℝ) / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfailR

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
  have hdvd : R.a ∣ H := by rw [hR1]; exact one_dvd _
  have hlo' : R.a * R.Hlo ≤ H := by rw [hR1, one_mul]; exact hlo
  exact log_chowla_two_shell_xi_sq_aff h (ChowlaRegimeAff.ofRegime R 0 (Nat.zero_le _))
    hdvd hlo' hhi hH hlog hne hreg hhead ht hg hgle hI hc₁ h211 hC hcirc hdoor hbudget1 hbudget2

end Salt.Entropy.Chowla
