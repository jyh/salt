/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The constant-hoisted terminal surface of the log-Chowla-2 spine, node SPINE-HOIST

`log_chowla_two_conditional` (`SpineClose.lean`, node W3E-FINAL) closes the
contradiction but `∃`-quantifies its four producer constants (`c₁ = cD3/4`, `C`,
`K`, `cE`) INSIDE a fixed regime `R`.  Three of them — `c₁`, `C`, `cE` — are in
fact regime-FREE: their generating lemmas (`primeWindow_sum_inv_ge`,
`circle_method_estimate` at `C₀ = 2·log 4`, `hreduce_holds_final`) are all
`∃`-shaped over the constant with `eps` `∀`-quantified INSIDE (verified: none
takes `eps` as a witness-determining argument).  Only `K` genuinely depends on
`eps` — `bigXi_bounded` takes `eps` as an explicit argument.

This file hoists the three regime-free constants BEFORE the regime quantifier
(`log_chowla_two_conditional_hoisted`) — the `∃`-ordering fix identified in
PATCH-5 — and then, feeding the parametric regime builder
(`chowlaRegime_exists_param`, PATCH-5) at an honestly-chosen `ε`, delivers the
terminal quotable surface `log_chowla_two_final`.
-/
import Salt.Entropy.Chowla.RegimeParam
import Salt.Entropy.Chowla.TowerExport
import Salt.Entropy.Chowla.BudgetCore
import Salt.Entropy.Chowla.BudgetDeficit
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-- Mutual information is symmetric at the window pair (a re-statement of the
`private` twin in `TowerDischarge.lean`): `entropy_decrement` produces the
`liouville : residue` order, the shell consumes `residue : liouville`. -/
private lemma mutualInfo_window_comm' (R : ChowlaRegime) (H : ℕ) :
    I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      = I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] := by
  simp only [mutualInfo_def]
  rw [entropy_comm (measurable_residueWindow R.eps H) (measurable_liouvilleWindow H)
    (logMeasure R.x R.ω)]
  ring

/-- **The spine contradiction, constants lifted to parameters.**  This is the
body of `log_chowla_two_conditional` (`SpineClose.lean` lines 62–151) with the
four producer chains (`hreduce_holds_final`, `primeWindow_sum_inv_ge`,
`circle_method_estimate`, `bigXi_bounded`) supplied as hypotheses rather than
`obtain`-ed internally — so the caller controls the `∃`-ordering of the
constants.  Both hoisted surfaces below instantiate it. -/
private theorem spine_False_core (R : ChowlaRegime) {δ : ℝ} (hdoor : MRTUniformity R δ)
    (cE : ℝ) (_hcE : 0 < cE) (H₀red : ℕ)
    (hred : ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀red ≤ H →
      (eps : ℝ) ≤ cE / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1
          ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
          ≤ (x : ℝ) →
      (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| →
      (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|)
    (cD3 : ℝ) (hcD3 : 0 < cD3) (H₀D3 : ℕ)
    (hD3 : ∀ (eps : ℚ) (H : ℕ), H₀D3 ≤ H →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      (eps : ℝ) ^ 2 ≤ 1 →
      cD3 / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
    (C : ℝ) (hC : 0 < C)
    (hcm : ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 x2 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) → (∀ i, |x2 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H x1 j : ℝ) * (windowVal H x2 (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi eps H, (1 / (H : ℝ))
                * ‖(ZMod.dft (fun j : ZMod H =>
                    (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖))
    (K : ℝ) (_hK : 0 < K) (H₀xi : ℕ)
    (hxi : ∀ (H : ℕ) [NeZero H], H₀xi ≤ H → ((bigXi R.eps H).card : ℝ) ≤ K)
    (H : ℕ) [NeZero H] (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    (hH₀ : max (max H₀red H₀D3) H₀xi ≤ H)
    (hepsc : (R.eps : ℝ) ≤ cE / (32 * Real.log 4))
    (t g κ c₀ : ℝ) (ht : 0 < t) (hg : 0 < g)
    (hgle : g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
        / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    (hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω] ≤ κ)
    (hbudget1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
        + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
        + shellError R H t g κ
      ≤ cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)))
    (hbudget2 : K * δ < c₀ * (R.eps : ℝ))
    (hfail : logChowla2Fails R.eps R.x R.ω) : False := by
  classical
  have hepsRpos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hepshalf : (R.eps : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) * (R.eps : ℝ) ≤ 1 := by
      exact_mod_cast (by linarith [R.heps1] : (2 : ℚ) * R.eps ≤ 1)
    linarith
  have hepssq : (R.eps : ℝ) ^ 2 ≤ 1 := by nlinarith [hepshalf, hepsRpos]
  -- floor bookkeeping
  have hHnatM : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hH3 : 3 ≤ H := by omega
  have hH₀red : H₀red ≤ H := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hH₀
  have hH₀D3 : H₀D3 ≤ H := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hH₀
  have hH₀xi : H₀xi ≤ H := le_trans (le_max_right _ _) hH₀
  -- real-side H facts
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHnatM
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  have hlogH : 1 ≤ Real.log (H : ℝ) := by
    rw [Real.le_log_iff_exp_le hHpos]
    exact le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
  have hlogHpos : 0 < Real.log (H : ℝ) := by linarith
  have hlogHne : Real.log (H : ℝ) ≠ 0 := ne_of_gt hlogHpos
  -- the regime discharges (sqrt / ω / x / head)
  have hreg : Real.sqrt (H : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) / 2 :=
    sqrt_le_window_at R hlo hhi
  have hsqrt2000 : (2000 : ℝ) ≤ Real.sqrt (H : ℝ) := by
    rw [show (2000 : ℝ) = Real.sqrt 4000000 by
      rw [show (4000000 : ℝ) = 2000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hHR
  have h4 : (4 : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) := by nlinarith [hreg, hsqrt2000]
  have hωbig : (16 / (R.eps : ℝ)) * Real.log ((R.eps : ℝ) ^ 2 * (H : ℝ))
      + 64 / (R.eps : ℝ) + 1 ≤ Real.log (R.ω : ℝ) := omega_big_at R hhi h4
  have hxbig : (R.ω : ℝ) * (H : ℝ)
      + 48 * (R.ω : ℝ) * (1 + 2 / (R.eps : ℝ) ^ 2) / (R.eps : ℝ) ≤ (R.x : ℝ) :=
    x_big_at R hhi
  have hhead : 8 * (PH R.eps H : ℝ) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ) := pH_headroom_at R hhi
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
  -- the single-correlation seed and the reduce (h211 producer)
  set X : ℝ := |∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure R.x R.ω)| with hXdef
  have hseed : (R.eps : ℝ) / 2 ≤ X :=
    singleCorr_of_fails R.eps R.hx R.hω R.hωx hlog2 hfail
  have hredH : (1 / 2) * SP * (H : ℝ) * X
      ≤ |∫ n, fBridgeF R.eps H (liouvilleWindow H n) (residueWindow R.eps H n)
          ∂(logMeasure R.x R.ω)| :=
    hred R.eps H R.x R.ω R.hx R.hω R.hωx R.heps hepssq hH3 hlogH h4 hreg hH₀red hepsc
      hωbig hxbig hseed
  -- the concrete h211 (coefficient c₁ = cD3/4)
  have hXnn : (0 : ℝ) ≤ X := abs_nonneg _
  have hAX : (cD3 / Real.log (H : ℝ)) * ((R.eps : ℝ) / 2) ≤ SP * X :=
    mul_le_mul hmert hseed (by positivity) hSPnn
  have h211 : cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
      ≤ |∫ n, fBridgeF R.eps H (liouvilleWindow H n) (residueWindow R.eps H n)
          ∂(logMeasure R.x R.ω)| := by
    calc cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        = (1 / 2) * (H : ℝ) * ((cD3 / Real.log (H : ℝ)) * ((R.eps : ℝ) / 2)) := by
          field_simp; ring
      _ ≤ (1 / 2) * (H : ℝ) * (SP * X) :=
          mul_le_mul_of_nonneg_left hAX (by positivity)
      _ = (1 / 2) * SP * (H : ℝ) * X := by ring
      _ ≤ _ := hredH
  -- the circle-method bound (hcirc) via the card discharge
  have hcard : ((primeWindow R.eps H).card : ℝ)
      ≤ (2 * Real.log 4) * ((R.eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) :=
    primeWindow_card_le_of_regime R.eps H hreg hH3
  have hcirc : ∀ n : ℕ,
      |∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ))
                * ‖ZMod.dft (fun j : ZMod H =>
                    (windowVal H (liouvilleWindow H n) (ZMod.val j) : ℂ)) ξ‖) :=
    fun n => hcm R.eps H (liouvilleWindow H n) (liouvilleWindow H n)
      (fun i => abs_liouvilleWindow_le_one H n i)
      (fun i => abs_liouvilleWindow_le_one H n i) hcard
  -- the large-spectrum count
  have hXi : ((bigXi R.eps H).card : ℝ) ≤ K := hxi H hH₀xi
  -- fire the shell
  exact log_chowla_two_shell R hlo hhi hH3 hlogH hne hreg hhead ht hg hgle hI
    (by positivity) h211 hC hcirc hXi hdoor hbudget1 hbudget2

/-- **The Ξ_H-restricted spine contradiction, constants lifted to parameters**
(S0 XI-REWIRE).  Verbatim twin of `spine_False_core` consuming the Tao-faithful
`MRTUniformityXi R δ` in place of the full `MRTUniformity R δ`, plus the explicit
`hδ : 0 ≤ δ` the weakened door can no longer derive.  The door is threaded
UNTOUCHED to the final shell call — every producer step (`hred`/`hD3`/`hcm`/`hxi`
assembly, the `h211`/`hcirc`/`hXi` derivation) is door-independent — so the body
is reproduced exactly; only the closer swaps `log_chowla_two_shell` for
`log_chowla_two_shell_xi`.  Additive — `spine_False_core` is untouched. -/
private theorem spine_False_core_xi (R : ChowlaRegime) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdoor : MRTUniformityXi R δ)
    (cE : ℝ) (_hcE : 0 < cE) (H₀red : ℕ)
    (hred : ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀red ≤ H →
      (eps : ℝ) ≤ cE / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1
          ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
          ≤ (x : ℝ) →
      (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| →
      (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|)
    (cD3 : ℝ) (hcD3 : 0 < cD3) (H₀D3 : ℕ)
    (hD3 : ∀ (eps : ℚ) (H : ℕ), H₀D3 ≤ H →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      (eps : ℝ) ^ 2 ≤ 1 →
      cD3 / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
    (C : ℝ) (hC : 0 < C)
    (hcm : ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 x2 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) → (∀ i, |x2 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H x1 j : ℝ) * (windowVal H x2 (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi eps H, (1 / (H : ℝ))
                * ‖(ZMod.dft (fun j : ZMod H =>
                    (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖))
    (K : ℝ) (_hK : 0 < K) (H₀xi : ℕ)
    (hxi : ∀ (H : ℕ) [NeZero H], H₀xi ≤ H → ((bigXi R.eps H).card : ℝ) ≤ K)
    (H : ℕ) [NeZero H] (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    (hH₀ : max (max H₀red H₀D3) H₀xi ≤ H)
    (hepsc : (R.eps : ℝ) ≤ cE / (32 * Real.log 4))
    (t g κ c₀ : ℝ) (ht : 0 < t) (hg : 0 < g)
    (hgle : g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
        / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    (hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω] ≤ κ)
    (hbudget1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
        + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
        + shellError R H t g κ
      ≤ cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)))
    (hbudget2 : K * δ < c₀ * (R.eps : ℝ))
    (hfail : logChowla2Fails R.eps R.x R.ω) : False := by
  classical
  have hepsRpos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hepshalf : (R.eps : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) * (R.eps : ℝ) ≤ 1 := by
      exact_mod_cast (by linarith [R.heps1] : (2 : ℚ) * R.eps ≤ 1)
    linarith
  have hepssq : (R.eps : ℝ) ^ 2 ≤ 1 := by nlinarith [hepshalf, hepsRpos]
  -- floor bookkeeping
  have hHnatM : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hH3 : 3 ≤ H := by omega
  have hH₀red : H₀red ≤ H := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hH₀
  have hH₀D3 : H₀D3 ≤ H := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hH₀
  have hH₀xi : H₀xi ≤ H := le_trans (le_max_right _ _) hH₀
  -- real-side H facts
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHnatM
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  have hlogH : 1 ≤ Real.log (H : ℝ) := by
    rw [Real.le_log_iff_exp_le hHpos]
    exact le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
  have hlogHpos : 0 < Real.log (H : ℝ) := by linarith
  have hlogHne : Real.log (H : ℝ) ≠ 0 := ne_of_gt hlogHpos
  -- the regime discharges (sqrt / ω / x / head)
  have hreg : Real.sqrt (H : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) / 2 :=
    sqrt_le_window_at R hlo hhi
  have hsqrt2000 : (2000 : ℝ) ≤ Real.sqrt (H : ℝ) := by
    rw [show (2000 : ℝ) = Real.sqrt 4000000 by
      rw [show (4000000 : ℝ) = 2000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hHR
  have h4 : (4 : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) := by nlinarith [hreg, hsqrt2000]
  have hωbig : (16 / (R.eps : ℝ)) * Real.log ((R.eps : ℝ) ^ 2 * (H : ℝ))
      + 64 / (R.eps : ℝ) + 1 ≤ Real.log (R.ω : ℝ) := omega_big_at R hhi h4
  have hxbig : (R.ω : ℝ) * (H : ℝ)
      + 48 * (R.ω : ℝ) * (1 + 2 / (R.eps : ℝ) ^ 2) / (R.eps : ℝ) ≤ (R.x : ℝ) :=
    x_big_at R hhi
  have hhead : 8 * (PH R.eps H : ℝ) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ) := pH_headroom_at R hhi
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
  -- the single-correlation seed and the reduce (h211 producer)
  set X : ℝ := |∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure R.x R.ω)| with hXdef
  have hseed : (R.eps : ℝ) / 2 ≤ X :=
    singleCorr_of_fails R.eps R.hx R.hω R.hωx hlog2 hfail
  have hredH : (1 / 2) * SP * (H : ℝ) * X
      ≤ |∫ n, fBridgeF R.eps H (liouvilleWindow H n) (residueWindow R.eps H n)
          ∂(logMeasure R.x R.ω)| :=
    hred R.eps H R.x R.ω R.hx R.hω R.hωx R.heps hepssq hH3 hlogH h4 hreg hH₀red hepsc
      hωbig hxbig hseed
  -- the concrete h211 (coefficient c₁ = cD3/4)
  have hXnn : (0 : ℝ) ≤ X := abs_nonneg _
  have hAX : (cD3 / Real.log (H : ℝ)) * ((R.eps : ℝ) / 2) ≤ SP * X :=
    mul_le_mul hmert hseed (by positivity) hSPnn
  have h211 : cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
      ≤ |∫ n, fBridgeF R.eps H (liouvilleWindow H n) (residueWindow R.eps H n)
          ∂(logMeasure R.x R.ω)| := by
    calc cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        = (1 / 2) * (H : ℝ) * ((cD3 / Real.log (H : ℝ)) * ((R.eps : ℝ) / 2)) := by
          field_simp; ring
      _ ≤ (1 / 2) * (H : ℝ) * (SP * X) :=
          mul_le_mul_of_nonneg_left hAX (by positivity)
      _ = (1 / 2) * SP * (H : ℝ) * X := by ring
      _ ≤ _ := hredH
  -- the circle-method bound (hcirc) via the card discharge
  have hcard : ((primeWindow R.eps H).card : ℝ)
      ≤ (2 * Real.log 4) * ((R.eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) :=
    primeWindow_card_le_of_regime R.eps H hreg hH3
  have hcirc : ∀ n : ℕ,
      |∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ))
                * ‖ZMod.dft (fun j : ZMod H =>
                    (windowVal H (liouvilleWindow H n) (ZMod.val j) : ℂ)) ξ‖) :=
    fun n => hcm R.eps H (liouvilleWindow H n) (liouvilleWindow H n)
      (fun i => abs_liouvilleWindow_le_one H n i)
      (fun i => abs_liouvilleWindow_le_one H n i) hcard
  -- the large-spectrum count
  have hXi : ((bigXi R.eps H).card : ℝ) ≤ K := hxi H hH₀xi
  -- fire the Ξ_H shell (explicit `0 ≤ δ` threaded to the Ξ_H seam)
  exact log_chowla_two_shell_xi R hlo hhi hH3 hlogH hne hreg hhead ht hg hgle hI
    (by positivity) h211 hC hcirc hXi hδ hdoor hbudget1 hbudget2

/-- **W3E-FINAL, constants hoisted before the regime.**  Identical content to
`log_chowla_two_conditional` (`SpineClose.lean`), but the three regime-free
producer constants `c₁ = cD3/4`, `C`, `cE` are `∃`-quantified BEFORE the regime
`R`, exposing that they do not depend on `R` (their generating lemmas are
`eps`-free).  Only `K` (from `bigXi_bounded`, which takes `eps` as an argument)
and the combined floor `H₀` remain inside, `∃`-bound after `R` is fixed.  This is
the `∃`-ordering that `log_chowla_two_final`'s regime-builder dance requires. -/
theorem log_chowla_two_conditional_hoisted :
    ∃ (c₁ C cE : ℝ), 0 < c₁ ∧ 0 < C ∧ 0 < cE ∧
      ∀ (R : ChowlaRegime) {δ : ℝ}, MRTUniformity R δ →
        ∃ (K : ℝ) (H₀ : ℕ), 0 < K ∧
          ∀ (H : ℕ) [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → H₀ ≤ H →
            (R.eps : ℝ) ≤ cE / (32 * Real.log 4) →
            ∀ (t g κ c₀ : ℝ), 0 < t → 0 < g →
              g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
                  / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2 →
              I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω] ≤ κ →
              C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
                  + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
                  + shellError R H t g κ
                ≤ c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) →
              K * δ < c₀ * (R.eps : ℝ) →
              logChowla2Fails R.eps R.x R.ω →
              False := by
  classical
  obtain ⟨cE, hcE, H₀red, hred⟩ := hreduce_holds_final
  obtain ⟨cD3, hcD3, H₀D3, hD3⟩ := primeWindow_sum_inv_ge
  obtain ⟨C, hC, hcm⟩ := circle_method_estimate (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  refine ⟨cD3 / 4, C, cE, by positivity, hC, hcE, ?_⟩
  intro R δ hdoor
  have hepsRpos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hepshalf : (R.eps : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) * (R.eps : ℝ) ≤ 1 := by
      exact_mod_cast (by linarith [R.heps1] : (2 : ℚ) * R.eps ≤ 1)
    linarith
  have heps2 : (R.eps : ℝ) ^ 2 < 1 / 2 := by nlinarith [hepshalf, hepsRpos]
  obtain ⟨K, hK, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded R.eps R.heps heps2
  refine ⟨K, max (max H₀red H₀D3) H₀xi, hK, ?_⟩
  intro H hNe hlo hhi hH₀ hepsc t g κ c₀ ht hg hgle hI hbudget1 hbudget2 hfail
  exact spine_False_core R hdoor cE hcE H₀red hred cD3 hcD3 H₀D3 hD3 C hC hcm
    K hK H₀xi hxi H hlo hhi hH₀ hepsc t g κ c₀ ht hg hgle hI hbudget1 hbudget2 hfail

/-- **THE terminal log-Chowla-2 surface.**

SUPERSEDED AS CITATION (A1, 2026-07-19): the `t`/`g`/`hbudget1` residual is
unsatisfiable at `c₀ = 1` (F0, catch #249); cite `log_chowla_two_door_only(_xi)` /
`log_chowla_two_budget_head` instead.

Tao's logarithmically-averaged
two-point Chowla theorem (Tao 1509.05422, the `a=1,b=0,h=1,g₁=g₂=λ` model form),
machine-checked: there is a witnessed regime `R` and a door-smallness threshold
`δ₀ > 0` at which log-Chowla-2 does NOT fail, conditional ONLY on the
Matomäki–Radziwiłł–Tao Fourier-uniformity theorem (arXiv:1503.05121) at any
sufficiently small uniformity level `δ ≤ δ₀`.  Every other input — the entropy
decrement, the circle method, the restriction-free large-spectrum bound, the
sieve machinery, the regime numerics — is proven in this repository from mathlib,
axioms `[propext, Classical.choice, Quot.sound]`.

The three opaque residuals of `log_chowla_two_of_door` are here DISCHARGED by the
parametric builder: `ε` is chosen (via `exists_rat_btwn`) below `cE/(32·log 4)`,
clearing the reduce coupling `hepsc`; the regime is built at that `ε` with floor
`Hlo ≥ H₀`, clearing `H₀ ≤ H` against the `entropy_decrement` level; and the
door threshold `δ₀ = ε/(2K)` folds in `hbudget2`.  The mutual-information budget
`hI` is discharged at `κ = H/(log H · logloglog H)` (Lemma 3.1).

What remains explicit is exactly the entropy-decrement AM–GM residual: the
decrement parameters `t`, `g` (under `0 < t`, `0 < g`, `hgle`) and the
`shellError`-margin `hbudget1` — the honest analytic core (balancing `t`, `g` to
beat the `c₁·εH/log H` margin) is Tao's Lemma-3.x quantitative close, not part of
this constant-hoist.  The producer constants `c₁ = cD3/4`, `C` it references are
exposed (they are opaque `∃`-outputs). -/
theorem log_chowla_two_final :
    ∃ (δ₀ : ℝ) (R : ChowlaRegime) (H : ℕ) (c₁ C : ℝ),
      0 < δ₀ ∧ 0 < c₁ ∧ 0 < C ∧ R.Hlo ≤ H ∧ H ≤ R.Hhi ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ → MRTUniformity R δ →
        ∀ (t g : ℝ), 0 < t → 0 < g →
          g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
              / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2 →
          C * ((H : ℝ) / Real.log (H : ℝ)) * (1 * (R.eps : ℝ))
              + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
              + shellError R H t g
                  ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))))
            ≤ c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨cE, hcE, H₀red, hred⟩ := hreduce_holds_final
  obtain ⟨cD3, hcD3, H₀D3, hD3⟩ := primeWindow_sum_inv_ge
  obtain ⟨C, hC, hcm⟩ := circle_method_estimate (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  -- choose ε : a rational in (0, min(cE/(32·log 4), 1/2))
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hbound_pos : (0 : ℝ) < min (cE / (32 * Real.log 4)) (1 / 2) :=
    lt_min (by positivity) (by norm_num)
  obtain ⟨ε, hε0, hεlt⟩ := exists_rat_btwn hbound_pos
  have hεR0 : (0 : ℝ) < (ε : ℝ) := hε0
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεlt_half : (ε : ℝ) < 1 / 2 := lt_of_lt_of_le hεlt (min_le_right _ _)
  have hεQ1 : ε ≤ 1 / 2 := by
    have h2 : (2 : ℝ) * (ε : ℝ) < 1 := by linarith [hεlt_half]
    have h2Q : (2 : ℚ) * ε < 1 := by exact_mod_cast h2
    linarith
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) :=
    le_of_lt (lt_of_lt_of_le hεlt (min_le_left _ _))
  have hε2 : (ε : ℝ) ^ 2 < 1 / 2 := by nlinarith [hεR0, hεlt_half]
  obtain ⟨K, hK, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded ε hεQpos hε2
  -- build the regime at ε with the combined producer floor
  obtain ⟨R, hReps, hRHlo⟩ :=
    chowlaRegime_exists_param ε hεQpos hεQ1 (max (max H₀red H₀D3) H₀xi)
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrement R
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hRepsPos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  -- re-index the ε-facts to R.eps
  have hxiR : ∀ (H' : ℕ) [NeZero H'], H₀xi ≤ H'
      → ((bigXi R.eps H').card : ℝ) ≤ K := by
    intro H' hne hh
    haveI := hne
    rw [hReps]; exact hxi H' hh
  have hepscR : (R.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max (max H₀red H₀D3) H₀xi ≤ H := le_trans hRHlo hlo
  refine ⟨(R.eps : ℝ) / (2 * K), R, H, cD3 / 4, C,
    div_pos hRepsPos (by positivity), by positivity, hC, hlo, hhi, ?_⟩
  intro δ hδpos hδ hdoor t g ht hg hgle hbud1 hfail
  have hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
    rw [mutualInfo_window_comm']; exact hMI
  have hbudget2 : K * δ < 1 * (R.eps : ℝ) := by
    have hle : K * δ ≤ K * ((R.eps : ℝ) / (2 * K)) :=
      mul_le_mul_of_nonneg_left hδ (le_of_lt hK)
    have heq : K * ((R.eps : ℝ) / (2 * K)) = (R.eps : ℝ) / 2 := by field_simp
    rw [heq] at hle; rw [one_mul]; linarith
  exact spine_False_core R hdoor cE hcE H₀red hred cD3 hcD3 H₀D3 hD3 C hC hcm
    K hK H₀xi hxiR H hlo hhi hH₀ hepscR t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) 1
    ht hg hgle hI hbud1 hbudget2 hfail

/-- **THE terminal log-Chowla-2 surface, Ξ_H-restricted door** (S0 XI-REWIRE).

SUPERSEDED AS CITATION (A1, 2026-07-19): the `t`/`g`/`hbudget1` residual is
unsatisfiable at `c₀ = 1` (F0, catch #249); cite `log_chowla_two_door_only(_xi)` /
`log_chowla_two_budget_head` instead.

Identical conclusion and hypothesis list to `log_chowla_two_final`, differing in
EXACTLY ONE binder: the MR obligation is the Tao-faithful `MRTUniformityXi R δ`
(`MRTDoor.lean`, α restricted to the ≤ K major-arc frequencies `−ξ/H`,
`ξ ∈ Ξ_H = bigXi R.eps H`) rather than the full `∀ α`-outside `MRTUniformity R δ`.
This is the licensed weakening for the Liouville case (`c_p = 1`, major arcs
only; Tao 1509.05422, chowla.txt:743–750, riding [17] Theorem A.1) — it shrinks
the MR SURFACE (drops the minor-arc package), not its DEPTH (`ξ = 0 ∈ Ξ_H` is
already full short-interval strength; W4-MAJOR-R0 RED).  Every other input — the
entropy decrement, circle method, large-spectrum bound, sieve machinery, regime
numerics — is proven in this repository, axioms
`[propext, Classical.choice, Quot.sound]`.  The three explicit residuals (`t`,
`g` under `0 < t`, `0 < g`, `hgle`, and the `shellError` margin) are the SAME
SPINE-BUDGET AM–GM balance carried by `log_chowla_two_final`; this rewire touches
neither them nor the witnessed constants.  Additive — `log_chowla_two_final`
stays landed beside this.

**δ-threading numeric sanity (flags #163, off-trivial).**  The door threshold is
`δ₀ = R.eps/(2K)` (unchanged from the full-door terminal).  The seam's smallness
obligation `hbudget2 : K·δ < c₀·R.eps` fires at `c₀ = 1`: for any `δ ≤ δ₀`,
`K·δ ≤ K·(R.eps/(2K)) = R.eps/2 < R.eps = 1·R.eps` — a strict margin of factor 2,
identical arithmetic to `log_chowla_two_final` (the Ξ_H restriction alters the
door PREDICATE, never the δ-budget).  The one obligation the weakened door adds,
`0 ≤ δ` (no longer derivable from the door — the derivation fired at `α = 0`,
which `MRTUniformityXi` drops), is discharged FOR FREE from the ambient `0 < δ`
via `le_of_lt`; so the hypothesis list is genuinely door-only different. -/
theorem log_chowla_two_final_xi :
    ∃ (δ₀ : ℝ) (R : ChowlaRegime) (H : ℕ) (c₁ C : ℝ),
      0 < δ₀ ∧ 0 < c₁ ∧ 0 < C ∧ R.Hlo ≤ H ∧ H ≤ R.Hhi ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
        ∀ (t g : ℝ), 0 < t → 0 < g →
          g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
              / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2 →
          C * ((H : ℝ) / Real.log (H : ℝ)) * (1 * (R.eps : ℝ))
              + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
              + shellError R H t g
                  ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))))
            ≤ c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨cE, hcE, H₀red, hred⟩ := hreduce_holds_final
  obtain ⟨cD3, hcD3, H₀D3, hD3⟩ := primeWindow_sum_inv_ge
  obtain ⟨C, hC, hcm⟩ := circle_method_estimate (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  -- choose ε : a rational in (0, min(cE/(32·log 4), 1/2))
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hbound_pos : (0 : ℝ) < min (cE / (32 * Real.log 4)) (1 / 2) :=
    lt_min (by positivity) (by norm_num)
  obtain ⟨ε, hε0, hεlt⟩ := exists_rat_btwn hbound_pos
  have hεR0 : (0 : ℝ) < (ε : ℝ) := hε0
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεlt_half : (ε : ℝ) < 1 / 2 := lt_of_lt_of_le hεlt (min_le_right _ _)
  have hεQ1 : ε ≤ 1 / 2 := by
    have h2 : (2 : ℝ) * (ε : ℝ) < 1 := by linarith [hεlt_half]
    have h2Q : (2 : ℚ) * ε < 1 := by exact_mod_cast h2
    linarith
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) :=
    le_of_lt (lt_of_lt_of_le hεlt (min_le_left _ _))
  have hε2 : (ε : ℝ) ^ 2 < 1 / 2 := by nlinarith [hεR0, hεlt_half]
  obtain ⟨K, hK, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded ε hεQpos hε2
  -- build the regime at ε with the combined producer floor
  obtain ⟨R, hReps, hRHlo⟩ :=
    chowlaRegime_exists_param ε hεQpos hεQ1 (max (max H₀red H₀D3) H₀xi)
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrement R
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hRepsPos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  -- re-index the ε-facts to R.eps
  have hxiR : ∀ (H' : ℕ) [NeZero H'], H₀xi ≤ H'
      → ((bigXi R.eps H').card : ℝ) ≤ K := by
    intro H' hne hh
    haveI := hne
    rw [hReps]; exact hxi H' hh
  have hepscR : (R.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max (max H₀red H₀D3) H₀xi ≤ H := le_trans hRHlo hlo
  refine ⟨(R.eps : ℝ) / (2 * K), R, H, cD3 / 4, C,
    div_pos hRepsPos (by positivity), by positivity, hC, hlo, hhi, ?_⟩
  intro δ hδpos hδ hdoor t g ht hg hgle hbud1 hfail
  -- the free `0 ≤ δ` the Ξ_H seam demands (derived from ambient `0 < δ`)
  have hδnn : (0 : ℝ) ≤ δ := le_of_lt hδpos
  have hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
    rw [mutualInfo_window_comm']; exact hMI
  -- δ-threading: K·δ ≤ K·(ε/(2K)) = ε/2 < ε = 1·ε (margin 2; c₀ = 1)
  have hbudget2 : K * δ < 1 * (R.eps : ℝ) := by
    have hle : K * δ ≤ K * ((R.eps : ℝ) / (2 * K)) :=
      mul_le_mul_of_nonneg_left hδ (le_of_lt hK)
    have heq : K * ((R.eps : ℝ) / (2 * K)) = (R.eps : ℝ) / 2 := by field_simp
    rw [heq] at hle; rw [one_mul]; linarith
  exact spine_False_core_xi R hδnn hdoor cE hcE H₀red hred cD3 hcD3 H₀D3 hD3 C hC hcm
    K hK H₀xi hxiR H hlo hhi hH₀ hepscR t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) 1
    ht hg hgle hI hbud1 hbudget2 hfail

/-- **The `hbudget1` witness (SPINE-BUDGET rung R5).**  At `c₀ := cD3 / (16·C)`,
the entropy-decrement AM–GM residual of the spine budget is DISCHARGED: there are
decrement parameters `t`, `g` (`0 < t`, `0 < g`, `g` at the `hgle` cap) for which
the four-slice `shellError` margin holds at the frozen mutual-information budget
`κ = H / (log H · logloglog H)`.  Each of the four slices shares
`cD3/16 · εH/log H`: `S1` exact (the `c₀ = cD3/(16·C)` choice), `S2 ⟸ ε ≤ cD3/(16·C)`,
`S3 ⟸ ε ≤ cD3/16`, and `S4 = 2·boxGrade·((t+2log2)/g + (κ+D)/t) ≤ slice` via
`bracket_close` (R3) and `deficit_le_log_two` (R4) at `β = cD3·ε/(144·log 4)`,
with `t = √(g·(κ+log2))`, `g = gcap`.  Public for the SPINE-BUDGET head (R6). -/
theorem hbudget1_witness (R : ChowlaRegime) (H : ℕ) [NeZero H]
    (cD3 C : ℝ) (hcD3 : 0 < cD3) (hC : 0 < C)
    (hε_half : (R.eps : ℝ) ≤ 1 / 2)
    (hε_D3 : (R.eps : ℝ) ≤ cD3 / 16)
    (hε_D3C : (R.eps : ℝ) ≤ cD3 / (16 * C))
    (hhi : H ≤ R.Hhi)
    (hfloor : budgetFloor (R.eps : ℝ)
        (cD3 * (R.eps : ℝ) / (144 * Real.log 4)) ≤ H) :
    ∃ (t g : ℝ), 0 < t ∧ 0 < g ∧
      g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
          / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2 ∧
      C * ((H : ℝ) / Real.log (H : ℝ)) * (cD3 / (16 * C) * (R.eps : ℝ))
          + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + shellError R H t g
              ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))))
        ≤ cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) := by
  classical
  have hlog4_pos : 0 < Real.log 4 := log_four_pos_aux
  have hlog2_pos : 0 < Real.log 2 := log_two_pos_aux
  have hlog4ne : Real.log 4 ≠ 0 := hlog4_pos.ne'
  have hεpos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hHRpos : (0 : ℝ) < (H : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne H)
  set β : ℝ := cD3 * (R.eps : ℝ) / (144 * Real.log 4) with hβ_def
  have hβpos : 0 < β := by
    rw [hβ_def]
    exact div_pos (mul_pos hcD3 hεpos) (mul_pos (by norm_num) hlog4_pos)
  obtain ⟨hlogH1, hgcap_pos, hL3pos, hiv, hv⟩ :=
    budget_facts (R.eps : ℝ) β hεpos hε_half hβpos H hfloor
  have hlogHpos : 0 < Real.log (H : ℝ) := by linarith [hlogH1]
  have hLne : Real.log (H : ℝ) ≠ 0 := hlogHpos.ne'
  have hΛpos : (0 : ℝ) < (H : ℝ) / Real.log (H : ℝ) := div_pos hHRpos hlogHpos
  set gcap : ℝ := (R.eps : ℝ) ^ 6 * (H : ℝ)
      / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2 with hgcap_def
  set κ : ℝ := (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) with hκ_def
  have hκpos : 0 < κ := by
    rw [hκ_def]; exact div_pos hHRpos (mul_pos hlogHpos hL3pos)
  have hs : 0 < κ + Real.log 2 := by linarith [hκpos, hlog2_pos]
  set tcap : ℝ := Real.sqrt (gcap * (κ + Real.log 2)) with htcap_def
  have htcap_pos : 0 < tcap := by
    rw [htcap_def]; exact Real.sqrt_pos.mpr (mul_pos hgcap_pos hs)
  have hdef : Real.log (PH R.eps H : ℝ)
      - H[residueWindow R.eps H ; logMeasure R.x R.ω] ≤ Real.log 2 :=
    deficit_le_log_two R hhi
  have hbr : (tcap + 2 * Real.log 2) / gcap
      + (κ + (Real.log (PH R.eps H : ℝ)
          - H[residueWindow R.eps H ; logMeasure R.x R.ω])) / tcap ≤ β := by
    have hbc := bracket_close gcap β κ
      (κ + (Real.log (PH R.eps H : ℝ)
        - H[residueWindow R.eps H ; logMeasure R.x R.ω]))
      hgcap_pos hβpos hs (by linarith [hdef]) hiv hv
    rw [← htcap_def] at hbc
    exact hbc
  clear_value tcap gcap κ β
  refine ⟨tcap, gcap, htcap_pos, hgcap_pos, le_rfl, ?_⟩
  set W : ℝ := cD3 / 16 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) with hW_def
  clear_value W
  have hCne : C ≠ 0 := hC.ne'
  -- slice S1 (exact)
  have hS1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (cD3 / (16 * C) * (R.eps : ℝ)) = W := by
    rw [hW_def]; field_simp
  -- the coupling `C·ε ≤ cD3/16`
  have hCε : C * (R.eps : ℝ) ≤ cD3 / 16 := by
    have h16C : (0 : ℝ) < 16 * C := mul_pos (by norm_num) hC
    have h := (le_div_iff₀ h16C).mp hε_D3C
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    nlinarith [h]
  -- slice S2
  have hS2 : C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2 ≤ W := by
    have key : C * (R.eps : ℝ) ^ 2 ≤ cD3 / 16 * (R.eps : ℝ) := by nlinarith [hCε, hεpos]
    rw [hW_def]
    calc C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
        = ((H : ℝ) / Real.log (H : ℝ)) * (C * (R.eps : ℝ) ^ 2) := by ring
      _ ≤ ((H : ℝ) / Real.log (H : ℝ)) * (cD3 / 16 * (R.eps : ℝ)) :=
          mul_le_mul_of_nonneg_left key hΛpos.le
      _ = cD3 / 16 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) := by ring
  -- the shellError two-slice bound
  have hshellbd : shellError R H tcap gcap κ ≤ W + W := by
    simp only [shellError, boxGrade]
    have hS3 : (R.eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) ≤ W := by
      have key : (R.eps : ℝ) ^ 2 ≤ cD3 / 16 * (R.eps : ℝ) := by nlinarith [hε_D3, hεpos]
      rw [hW_def]
      calc (R.eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
          = ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2) := by ring
        _ ≤ ((H : ℝ) / Real.log (H : ℝ)) * (cD3 / 16 * (R.eps : ℝ)) :=
            mul_le_mul_of_nonneg_left key hΛpos.le
        _ = cD3 / 16 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) := by ring
    have hbox_nn : (0 : ℝ) ≤ 2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
        * ((H : ℝ) / Real.log (H : ℝ)) := by
      apply mul_nonneg
      · exact mul_nonneg (mul_nonneg (by norm_num) hlog4_pos.le) (by positivity)
      · exact hΛpos.le
    have hcoeff_nn : (0 : ℝ) ≤ 2 * (2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
        * ((H : ℝ) / Real.log (H : ℝ))) := by linarith [hbox_nn]
    have hS4a : 2 * (2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
          * ((H : ℝ) / Real.log (H : ℝ)))
        * ((tcap + 2 * Real.log 2) / gcap
            + (κ + (Real.log (PH R.eps H : ℝ)
                - H[residueWindow R.eps H ; logMeasure R.x R.ω])) / tcap)
      ≤ 2 * (2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
          * ((H : ℝ) / Real.log (H : ℝ))) * β :=
      mul_le_mul_of_nonneg_left hbr hcoeff_nn
    have hS4b : 2 * (2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
          * ((H : ℝ) / Real.log (H : ℝ))) * β ≤ W := by
      have h2e : (R.eps : ℝ) ^ 2 ≤ 1 / 4 := by nlinarith [hε_half, hεpos]
      have hcD3εA : (0 : ℝ) ≤ cD3 * (R.eps : ℝ) * ((H : ℝ) / Real.log (H : ℝ)) :=
        mul_nonneg (mul_nonneg hcD3.le hεpos.le) hΛpos.le
      have hLHSeq : 2 * (2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
            * ((H : ℝ) / Real.log (H : ℝ))) * β
          = (2 + (R.eps : ℝ) ^ 2)
              * (cD3 * (R.eps : ℝ) * ((H : ℝ) / Real.log (H : ℝ))) / 36 := by
        rw [hβ_def]; field_simp; ring
      have hWeq : W = cD3 * (R.eps : ℝ) * ((H : ℝ) / Real.log (H : ℝ)) / 16 := by
        rw [hW_def]; ring
      have h94 : (2 + (R.eps : ℝ) ^ 2) ≤ 9 / 4 := by linarith [h2e]
      have hPQ : (2 + (R.eps : ℝ) ^ 2)
            * (cD3 * (R.eps : ℝ) * ((H : ℝ) / Real.log (H : ℝ)))
          ≤ 9 / 4 * (cD3 * (R.eps : ℝ) * ((H : ℝ) / Real.log (H : ℝ))) :=
        mul_le_mul_of_nonneg_right h94 hcD3εA
      rw [hLHSeq, hWeq]
      linarith [hPQ]
    have hS4 : 2 * (2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
          * ((H : ℝ) / Real.log (H : ℝ)))
        * ((tcap + 2 * Real.log 2) / gcap
            + (κ + (Real.log (PH R.eps H : ℝ)
                - H[residueWindow R.eps H ; logMeasure R.x R.ω])) / tcap) ≤ W :=
      le_trans hS4a hS4b
    exact add_le_add hS3 hS4
  have hRHS : cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) = 4 * W := by
    rw [hW_def]; ring
  calc C * ((H : ℝ) / Real.log (H : ℝ)) * (cD3 / (16 * C) * (R.eps : ℝ))
          + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + shellError R H tcap gcap κ
      ≤ W + W + (W + W) := by
        rw [hS1]; exact add_le_add (add_le_add le_rfl hS2) hshellbd
    _ = 4 * W := by ring
    _ = cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) := hRHS.symm

/-- **The SPINE-BUDGET head (rung R6, T-HEAD).**  The full log-Chowla-2 spine
contradiction with the AM–GM residual `t`/`g`/`hbudget1` DISCHARGED internally at
`c₀ := cD3/(16·C)` (via `hbudget1_witness`): there is an honestly chosen
`ε : ℚ` and a door threshold `δ₀ = (cD3/(16·C))·ε/(2K) > 0` such that, for EVERY
extra regime-floor demand `extraFloor`, a regime `R` at that `ε` with
`extraFloor ≤ R.Hlo` makes log-Chowla-2 not fail, conditional ONLY on the
Ξ_H-restricted Matomäki–Radziwiłł–Tao door `MRTUniformityXi R δ` at any `δ ≤ δ₀`.

This SUPERSEDES the `t/g/hbudget1` residual of `log_chowla_two_final(_xi)` (which
is unsatisfiable at the baked `c₀ = 1`, freeze finding F0 / catch #249): the
budget rebalance `c₀ := cD3/(16·C)`, the two extra `ε`-arms (`ε ≤ cD3/16`,
`ε ≤ cD3/(16·C)`), and the `budgetFloor`/`extraFloor` floor arms discharge the
four-slice margin unconditionally.  The `∀ extraFloor` interface is what the
short-interval MR compose (S11) consumes to place `H₀door(δ₀)` under `R.Hlo`. -/
theorem log_chowla_two_budget_head :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ extraFloor : ℕ, ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨cE, hcE, H₀red, hred⟩ := hreduce_holds_final
  obtain ⟨cD3, hcD3, H₀D3, hD3⟩ := primeWindow_sum_inv_ge
  obtain ⟨C, hC, hcm⟩ := circle_method_estimate (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- choose ε below `min(min(min (cE/(32·log4)) (1/2)) (cD3/16)) (cD3/(16·C))`
  have hbound_pos : (0 : ℝ) < min (min (min (cE / (32 * Real.log 4)) (1 / 2))
      (cD3 / 16)) (cD3 / (16 * C)) := by
    refine lt_min (lt_min (lt_min ?_ ?_) ?_) ?_
    · exact div_pos hcE (mul_pos (by norm_num) hlog4)
    · norm_num
    · exact div_pos hcD3 (by norm_num)
    · exact div_pos hcD3 (mul_pos (by norm_num) hC)
  obtain ⟨ε, hε0, hεlt⟩ := exists_rat_btwn hbound_pos
  have hεR0 : (0 : ℝ) < (ε : ℝ) := hε0
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := le_of_lt (lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)))
  have hε_half_lt : (ε : ℝ) < 1 / 2 := lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _))
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := le_of_lt (lt_of_lt_of_le hεlt
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := le_of_lt (lt_of_lt_of_le hεlt (min_le_right _ _))
  have hεQ1 : ε ≤ 1 / 2 := by
    have h2 : (2 : ℝ) * (ε : ℝ) < 1 := by linarith [hε_half_lt]
    have h2Q : (2 : ℚ) * ε < 1 := by exact_mod_cast h2
    linarith
  have hε2 : (ε : ℝ) ^ 2 < 1 / 2 := by nlinarith [hεR0, hε_half_lt]
  obtain ⟨K, hK, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded ε hεQpos hε2
  refine ⟨ε, cD3 / (16 * C) * (ε : ℝ) / (2 * K), hεQpos,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0)
      (mul_pos (by norm_num) hK), ?_⟩
  intro extraFloor
  obtain ⟨R, hReps, hRHlo⟩ := chowlaRegime_exists_param ε hεQpos hεQ1
    (max (max (max (max H₀red H₀D3) H₀xi)
      (budgetFloor (ε : ℝ) (cD3 * (ε : ℝ) / (144 * Real.log 4)))) extraFloor)
  refine ⟨R, hReps, le_trans (le_max_right _ _) hRHlo, ?_⟩
  intro δ hδpos hδ hdoor hfail
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrement R
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
    rw [mutualInfo_window_comm']; exact hMI
  have hxiR : ∀ (H' : ℕ) [NeZero H'], H₀xi ≤ H'
      → ((bigXi R.eps H').card : ℝ) ≤ K := by
    intro H' hne hh
    haveI := hne
    rw [hReps]; exact hxi H' hh
  have hepscR : (R.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max (max H₀red H₀D3) H₀xi ≤ H :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hRHlo) hlo
  have hfloorH : budgetFloor (R.eps : ℝ)
      (cD3 * (R.eps : ℝ) / (144 * Real.log 4)) ≤ H := by
    rw [hReps]
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRHlo) hlo
  obtain ⟨t, g, ht, hg, hgle, hbudget1⟩ :=
    hbudget1_witness R H cD3 C hcD3 hC
      (by rw [hReps]; exact le_of_lt hε_half_lt)
      (by rw [hReps]; exact hε_D3)
      (by rw [hReps]; exact hε_D3C) hhi hfloorH
  have hbudget2 : K * δ < cD3 / (16 * C) * (R.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hle : K * δ ≤ K * (cD3 / (16 * C) * (ε : ℝ) / (2 * K)) :=
      mul_le_mul_of_nonneg_left hδ hK.le
    have heq : K * (cD3 / (16 * C) * (ε : ℝ) / (2 * K)) = cD3 / (16 * C) * (ε : ℝ) / 2 := by
      field_simp
    rw [heq] at hle
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hle, hpos]
  exact spine_False_core_xi R (le_of_lt hδpos) hdoor cE hcE H₀red hred cD3 hcD3 H₀D3 hD3
    C hC hcm K hK H₀xi hxiR H hlo hhi hH₀ hepscR t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail

/-- **The SPINE-BUDGET head, g-twin (REGIME-CUT).**  Additive twin of
`log_chowla_two_budget_head` carrying TWO extra levers in one statement:

* `U1floor` — a SECOND regime-floor demand, delivered as `U1floor ≤ R.Hlo`
  alongside the original `extraFloor ≤ R.Hlo` (the U1 floor-raise: the caller no
  longer has to fold its own floor into `extraFloor`, so the two floors stay
  independently addressable at the call site);
* `g : ℕ → ℕ → ℕ` — an arbitrary outer-scale demand, delivered as
  `g R.Hhi R.ω ≤ R.x` (the parametric `x`-vs-`H₊` lever).  `g` is fixed BEFORE
  the `∃ R`, and reads only `(Hhi, ω)`, so the demand is acyclic: enlargement
  moves `x` alone, never the arguments of `g`.

⟦THE NAMED AMENDMENT⟧ (the 2026-07-29 anchor ruling).  The `∃ R` carries a THIRD
payload: the tower endpoint law

```
50 ≤ loglog R.Hlo → loglog R.Hhi ≤ (loglog R.Hlo)^5
```

(`TowerExport.chowlaRegime_exists_param_head_tower'`, whose builder re-points the
tower's `J` at the minimal crossing length `towerJmin`).  It is what makes a
CONSTANT door anchor sound against this regime: without it the regime exports no
upper control on `H₊` whatsoever.  The guard `50 ≤ loglog R.Hlo` is the crossing
law's own base floor and is free at every door-road call site (their floors are
astronomically past `exp(exp 50)`); it cannot be dropped here, because the
builder's own base is only `4·10⁶` when the caller asks for nothing more.

The proof is the original's, with two changes.  (1) The regime is built by
`chowlaRegime_exists_param_head_tower'` (`TowerExport.lean`, the tower-pointed
twin of `RegimeParam.chowlaRegime_exists_param_head'`) instead of
`chowlaRegime_exists_param`, which is what supplies the `g`-clearance and the
endpoint law.  (2) The floor argument gains a FIFTH
max-arm, placed OUTERMOST-RIGHT and paired with `extraFloor` —
`max (4-tower) (max extraFloor U1floor)` — so the four-fold LEFT spine is
syntactically untouched and the `le_max` chains feeding `hH₀`/`hfloorH` (hence
`spine_False_core_xi`'s `max (max H₀red H₀D3) H₀xi ≤ H` binder) are unchanged.
Everything below the `refine` is the original body verbatim.

The `g`-lever stays PARAMETRIC here: downstream stones instantiate it (the
regime-enlargement law: an arbitrary `x`-demand absorbs any `X`-INDEPENDENT
debit, and can never touch an `X`-dependent one). -/
theorem log_chowla_two_budget_head_g :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ (extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), ∃ R : ChowlaRegime,
        R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ 5) ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨cE, hcE, H₀red, hred⟩ := hreduce_holds_final
  obtain ⟨cD3, hcD3, H₀D3, hD3⟩ := primeWindow_sum_inv_ge
  obtain ⟨C, hC, hcm⟩ := circle_method_estimate (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- choose ε below `min(min(min (cE/(32·log4)) (1/2)) (cD3/16)) (cD3/(16·C))`
  have hbound_pos : (0 : ℝ) < min (min (min (cE / (32 * Real.log 4)) (1 / 2))
      (cD3 / 16)) (cD3 / (16 * C)) := by
    refine lt_min (lt_min (lt_min ?_ ?_) ?_) ?_
    · exact div_pos hcE (mul_pos (by norm_num) hlog4)
    · norm_num
    · exact div_pos hcD3 (by norm_num)
    · exact div_pos hcD3 (mul_pos (by norm_num) hC)
  obtain ⟨ε, hε0, hεlt⟩ := exists_rat_btwn hbound_pos
  have hεR0 : (0 : ℝ) < (ε : ℝ) := hε0
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := le_of_lt (lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)))
  have hε_half_lt : (ε : ℝ) < 1 / 2 := lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _))
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := le_of_lt (lt_of_lt_of_le hεlt
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := le_of_lt (lt_of_lt_of_le hεlt (min_le_right _ _))
  have hεQ1 : ε ≤ 1 / 2 := by
    have h2 : (2 : ℝ) * (ε : ℝ) < 1 := by linarith [hε_half_lt]
    have h2Q : (2 : ℚ) * ε < 1 := by exact_mod_cast h2
    linarith
  have hε2 : (ε : ℝ) ^ 2 < 1 / 2 := by nlinarith [hεR0, hε_half_lt]
  obtain ⟨K, hK, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded ε hεQpos hε2
  refine ⟨ε, cD3 / (16 * C) * (ε : ℝ) / (2 * K), hεQpos,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0)
      (mul_pos (by norm_num) hK), ?_⟩
  intro extraFloor U1floor g₅
  obtain ⟨R, hReps, hRHlo, hRg, hRtow⟩ := chowlaRegime_exists_param_head_tower' ε hεQpos hεQ1
    (max (max (max (max H₀red H₀D3) H₀xi)
      (budgetFloor (ε : ℝ) (cD3 * (ε : ℝ) / (144 * Real.log 4)))) (max extraFloor U1floor)) g₅
  refine ⟨R, hReps, le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, hRtow, ?_⟩
  intro δ hδpos hδ hdoor hfail
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrement R
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
    rw [mutualInfo_window_comm']; exact hMI
  have hxiR : ∀ (H' : ℕ) [NeZero H'], H₀xi ≤ H'
      → ((bigXi R.eps H').card : ℝ) ≤ K := by
    intro H' hne hh
    haveI := hne
    rw [hReps]; exact hxi H' hh
  have hepscR : (R.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max (max H₀red H₀D3) H₀xi ≤ H :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hRHlo) hlo
  have hfloorH : budgetFloor (R.eps : ℝ)
      (cD3 * (R.eps : ℝ) / (144 * Real.log 4)) ≤ H := by
    rw [hReps]
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRHlo) hlo
  obtain ⟨t, g, ht, hg, hgle, hbudget1⟩ :=
    hbudget1_witness R H cD3 C hcD3 hC
      (by rw [hReps]; exact le_of_lt hε_half_lt)
      (by rw [hReps]; exact hε_D3)
      (by rw [hReps]; exact hε_D3C) hhi hfloorH
  have hbudget2 : K * δ < cD3 / (16 * C) * (R.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hle : K * δ ≤ K * (cD3 / (16 * C) * (ε : ℝ) / (2 * K)) :=
      mul_le_mul_of_nonneg_left hδ hK.le
    have heq : K * (cD3 / (16 * C) * (ε : ℝ) / (2 * K)) = cD3 / (16 * C) * (ε : ℝ) / 2 := by
      field_simp
    rw [heq] at hle
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hle, hpos]
  exact spine_False_core_xi R (le_of_lt hδpos) hdoor cE hcE H₀red hred cD3 hcD3 H₀D3 hD3
    C hC hcm K hK H₀xi hxiR H hlo hhi hH₀ hepscR t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail

/-- **THE Ξ_H door-only terminal (rung R7, T-XI).**  The SPINE-BUDGET head at
`extraFloor := 0`: there is a witnessed regime `R` and a door threshold `δ₀ > 0`
at which log-Chowla-2 does NOT fail, conditional ONLY on the Ξ_H-restricted
Matomäki–Radziwiłł–Tao door `MRTUniformityXi R δ` at any `δ ≤ δ₀`.  Unlike
`log_chowla_two_final_xi`, there is NO residual `t`/`g`/`hbudget1` block — it is
discharged inside the head (`hbudget1_witness`).  This is the surface S8's door
lane should now cite; `log_chowla_two_final_xi` is superseded as citation (F0). -/
theorem log_chowla_two_door_only_xi :
    ∃ (δ₀ : ℝ) (R : ChowlaRegime), 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
        ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨_ε, δ₀, _hεpos, hδ₀pos, hbody⟩ := log_chowla_two_budget_head
  obtain ⟨R, _hReps, _h0Hlo, hδbody⟩ := hbody 0
  exact ⟨δ₀, R, hδ₀pos, hδbody⟩

/-- **THE full door-only terminal (rung R7, T-FULL).**  Identical to
`log_chowla_two_door_only_xi` but consuming the full `∀ α`-outside door
`MRTUniformity R δ`, derived from the Ξ_H-restricted terminal via the landed
kernel-checked implication `mrtUniformity_implies_xi` (MRTDoor).  The full door
implies its Ξ_H restriction, so this is a strict corollary — no second core
replay, no statement change.  Both Chowla terminals are now door-only-conditional
with the `t`/`g`/`hbudget1` residual gone from every surface. -/
theorem log_chowla_two_door_only :
    ∃ (δ₀ : ℝ) (R : ChowlaRegime), 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformity R δ →
        ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨δ₀, R, hδ₀pos, hδbody⟩ := log_chowla_two_door_only_xi
  exact ⟨δ₀, R, hδ₀pos, fun δ hδpos hδ hdoor =>
    hδbody δ hδpos hδ (mrtUniformity_implies_xi R δ hdoor)⟩

/-- **THE SPINE-BUDGET HEAD AT `K = 9/2`** (`log_chowla_two_budget_head_g_45`) —
the ADDITIVE twin of `log_chowla_two_budget_head_g` carrying the sharper tower
endpoint law

```
50 ≤ loglog R.Hlo → loglog R.Hhi ≤ (loglog R.Hlo)^(9/2)
```

(ruling C-A, 2026-07-30: S11-SCOPE's two-λ audit found the compose window EMPTY
at `K = 5` — the P2 arm reads `λ₊`, the drift arm caps `λ₋`, and the tower is
their only bridge — while `TowerExport.tower_loglog_le_45` shows `K = 9/2` is
free arithmetic, the crossing budget `w_J − w₀ < 3/2` clearing
`log (9/2) = 1.50408` exactly as it clears `log 5`).

The proof is `log_chowla_two_budget_head_g`'s VERBATIM, with ONE byte changed:
the regime is built by `TowerExport.chowlaRegime_exists_param_head_tower45'`
instead of `..._head_tower'`.  Every other component — the `ε` choice, the
five-arm floor, the `hbudget1`/`hbudget2` block, the `spine_False_core_xi`
discharge — is identical, and the tower conjunct is passed through untouched
here as it is there.  The landed `K = 5` head is not modified; both live side by
side, and `TowerExport.rpow_nine_halves_le_pow_five` weakens this one back to
the landed shape for any consumer already wired to `^5`. -/
theorem log_chowla_two_budget_head_g_45 :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ (extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), ∃ R : ChowlaRegime,
        R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨cE, hcE, H₀red, hred⟩ := hreduce_holds_final
  obtain ⟨cD3, hcD3, H₀D3, hD3⟩ := primeWindow_sum_inv_ge
  obtain ⟨C, hC, hcm⟩ := circle_method_estimate (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- choose ε below `min(min(min (cE/(32·log4)) (1/2)) (cD3/16)) (cD3/(16·C))`
  have hbound_pos : (0 : ℝ) < min (min (min (cE / (32 * Real.log 4)) (1 / 2))
      (cD3 / 16)) (cD3 / (16 * C)) := by
    refine lt_min (lt_min (lt_min ?_ ?_) ?_) ?_
    · exact div_pos hcE (mul_pos (by norm_num) hlog4)
    · norm_num
    · exact div_pos hcD3 (by norm_num)
    · exact div_pos hcD3 (mul_pos (by norm_num) hC)
  obtain ⟨ε, hε0, hεlt⟩ := exists_rat_btwn hbound_pos
  have hεR0 : (0 : ℝ) < (ε : ℝ) := hε0
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := le_of_lt (lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)))
  have hε_half_lt : (ε : ℝ) < 1 / 2 := lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _))
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := le_of_lt (lt_of_lt_of_le hεlt
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := le_of_lt (lt_of_lt_of_le hεlt (min_le_right _ _))
  have hεQ1 : ε ≤ 1 / 2 := by
    have h2 : (2 : ℝ) * (ε : ℝ) < 1 := by linarith [hε_half_lt]
    have h2Q : (2 : ℚ) * ε < 1 := by exact_mod_cast h2
    linarith
  have hε2 : (ε : ℝ) ^ 2 < 1 / 2 := by nlinarith [hεR0, hε_half_lt]
  obtain ⟨K, hK, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded ε hεQpos hε2
  refine ⟨ε, cD3 / (16 * C) * (ε : ℝ) / (2 * K), hεQpos,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0)
      (mul_pos (by norm_num) hK), ?_⟩
  intro extraFloor U1floor g₅
  -- ⟦THE ONE CHANGED BYTE⟧ the `K = 9/2` builder in place of the `K = 5` builder
  obtain ⟨R, hReps, hRHlo, hRg, hRtow⟩ := chowlaRegime_exists_param_head_tower45' ε hεQpos hεQ1
    (max (max (max (max H₀red H₀D3) H₀xi)
      (budgetFloor (ε : ℝ) (cD3 * (ε : ℝ) / (144 * Real.log 4)))) (max extraFloor U1floor)) g₅
  refine ⟨R, hReps, le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, hRtow, ?_⟩
  intro δ hδpos hδ hdoor hfail
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrement R
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
    rw [mutualInfo_window_comm']; exact hMI
  have hxiR : ∀ (H' : ℕ) [NeZero H'], H₀xi ≤ H'
      → ((bigXi R.eps H').card : ℝ) ≤ K := by
    intro H' hne hh
    haveI := hne
    rw [hReps]; exact hxi H' hh
  have hepscR : (R.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max (max H₀red H₀D3) H₀xi ≤ H :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hRHlo) hlo
  have hfloorH : budgetFloor (R.eps : ℝ)
      (cD3 * (R.eps : ℝ) / (144 * Real.log 4)) ≤ H := by
    rw [hReps]
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRHlo) hlo
  obtain ⟨t, g, ht, hg, hgle, hbudget1⟩ :=
    hbudget1_witness R H cD3 C hcD3 hC
      (by rw [hReps]; exact le_of_lt hε_half_lt)
      (by rw [hReps]; exact hε_D3)
      (by rw [hReps]; exact hε_D3C) hhi hfloorH
  have hbudget2 : K * δ < cD3 / (16 * C) * (R.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hle : K * δ ≤ K * (cD3 / (16 * C) * (ε : ℝ) / (2 * K)) :=
      mul_le_mul_of_nonneg_left hδ hK.le
    have heq : K * (cD3 / (16 * C) * (ε : ℝ) / (2 * K)) = cD3 / (16 * C) * (ε : ℝ) / 2 := by
      field_simp
    rw [heq] at hle
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hle, hpos]
  exact spine_False_core_xi R (le_of_lt hδpos) hdoor cE hcE H₀red hred cD3 hcD3 H₀D3 hD3
    C hC hcm K hK H₀xi hxiR H hlo hhi hH₀ hepscR t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail

/-! ## ⟦THE L² RESTRUCTURE⟧ stone 4 — the spine head twin at the `K`-FREE `δ₀`

`docs/exploration/l2-restructure-freeze-0730.md`, stone 4, on bank A
(`CircleMethod.circle_method_estimate_sq`, `Theorem23Shell.log_chowla_two_shell_xi_sq`,
`MRTDoor.MRTUniformityXiL2`).  Two declarations, both additive, both in-file
because `spine_False_core_xi` and its twin are `private` (the S0-TOWER precedent):

* `spine_False_core_xi_sq` — the core at the Ξ-SUMMED `L²` door.  `K`, `_hK`,
  `H₀xi` and `hxi` are GONE from the binder list (the shell twin takes no
  `hXi : |Ξ_H| ≤ K`), the circle-method input is the DIAGONAL squared socket, and
  the closure budget is the `K`-free `hbudget2 : ρ < c₀·ε`.
* `log_chowla_two_budget_head_g_sq(_count)` — the head at

  ```
  δ₀ := cD3/(16·C) · ε / 4      (= c₀·ε/4, with c₀ = cD3/(16·C))
  ```

  **NO `1/(2K)`.**  The landed head's `δ₀ = c₀·ε/(2K)` paid the frequency count
  because the `L¹` seam multiplied the door's grade by `|Ξ_H| ≤ K`; the summed
  `L²` seam reads the door's grade ONCE, so the count leaves the `δ`-line
  entirely (REF-L2-ARITH: "K IS ABSENT FROM δ₀'"; the `4` is that page's share
  allocation `δ₀' = c₀ε/4`, the strict inequality `ρ ≤ c₀ε/4 < c₀ε` carrying the
  ε-room the landed derivation carried at `c₀ε/2 < c₀ε`).

⟦WHERE THE COUNT WENT⟧ `|Ξ_H| ≤ K` did not disappear from the argument — it moved
from the SPINE to the ROAD, where `M4Window.sum_bigXi_norm_windowExpSum_sq_le`
spends it against the SIEVED leg only (the α-independent insert leg is paid once,
by Parseval).  Only the head knows `ε`, so only the head can produce that `K`:
`log_chowla_two_budget_head_g_sq_count` therefore EXPORTS the count gate as a
payload conjunct, and `log_chowla_two_budget_head_g_sq` is that head with the
conjunct dropped — the brief's `K`-free shape, one proof between them.

⟦THE TOWER PAYLOAD⟧ is the `9/2` law (ruling C-A, 2026-07-30), not `^5`: S11-SCOPE's
two-λ window is EMPTY at `K = 5`.  Consumers wired to `^5` read
`Salt.MR.tower_conjunct_45_le_five` (landed) for the free downgrade. -/

/-- **The Ξ-SUMMED `L²` spine contradiction, constants lifted to parameters**
(⟦THE L² RESTRUCTURE⟧ stone 4).  Twin of `spine_False_core_xi` threading the `L²`
door: the shell is `log_chowla_two_shell_xi_sq`, the door hypothesis is
`MRTUniformityXiL2 R ρ` and the closure budget is `hbudget2 : ρ < c₀·ε`.

Three binder-list changes, all forced by the shell twin, none optional:

* `hcirc` is the SQUARED, DIAGONAL circle-method bound (discharger
  `circle_method_estimate_sq`, which takes ONE window `x1` — the shell's only
  instantiation is `x1 = x2 = liouvilleWindow H n`).  The constant `C = 1 + 2C₀`
  is UNCHANGED, so `hbudget1` is byte-identical to the landed core's.
* `K`, `_hK`, `H₀xi`, `hxi` are ABSENT — the summed seam
  (`contradiction_of_mrtDoorXiL2`) consumes no cardinality hypothesis — and with
  them the `H₀xi` arm of the floor binder, which is now `max H₀red H₀D3 ≤ H`.
* `hδ : 0 ≤ δ` is ABSENT: the summed seam derives its collision from
  `ρ < c₀·ε ≤ (the summed L² mass)` alone.

⚠ **THE SEAM WARNING** (`MRTDoor.lean:174–182`, re-stated per REF-L2 mandate R4).
THE QUANTIFIERS STAY OUTSIDE THE INTEGRAL.  `MRTUniformityXiL2` is a FINITE SUM OF
INTEGRALS — the frequency quantifier is a `∑` over `Ξ_H` sitting outside `∫`, and
there is no `sup` anywhere inside the integral.  The sup-inside form is Tao
1509.05422 (4.1), which is OPEN; moving a quantifier inside silently downgrades a
theorem-door (Prop 2.4, PROVEN in Matomäki–Radziwiłł–Tao, arXiv:1503.05121) into
an open conjecture.  The `L²` door is SUPPLIED BY THE ROAD (`M4Window`'s adapter
`mrtUniformityXiL2_of_absWindowSqBound`, over the socket + Parseval stone), never
claimed from Prop 2.4; `MRTDoor.mrtUniformityXiL2_of_xi` is the standing proof
that it is IMPLIED by the landed `L¹` theorem-door at grade `K·δ`.

Additive — `spine_False_core` and `spine_False_core_xi` are untouched. -/
private theorem spine_False_core_xi_sq (R : ChowlaRegime) {ρ : ℝ}
    (hdoor : MRTUniformityXiL2 R ρ)
    (cE : ℝ) (_hcE : 0 < cE) (H₀red : ℕ)
    (hred : ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀red ≤ H →
      (eps : ℝ) ≤ cE / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1
          ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
          ≤ (x : ℝ) →
      (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| →
      (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|)
    (cD3 : ℝ) (hcD3 : 0 < cD3) (H₀D3 : ℕ)
    (hD3 : ∀ (eps : ℚ) (H : ℕ), H₀D3 ≤ H →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      (eps : ℝ) ^ 2 ≤ 1 →
      cD3 / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
    (C : ℝ) (hC : 0 < C)
    -- the SQUARED, DIAGONAL circle-method estimate (`circle_method_estimate_sq`):
    (hcm : ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi eps H, (1 / (H : ℝ) ^ 2)
                * ‖(ZMod.dft (fun j : ZMod H =>
                    (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2))
    (H : ℕ) [NeZero H] (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    (hH₀ : max H₀red H₀D3 ≤ H)
    (hepsc : (R.eps : ℝ) ≤ cE / (32 * Real.log 4))
    (t g κ c₀ : ℝ) (ht : 0 < t) (hg : 0 < g)
    (hgle : g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
        / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    (hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω] ≤ κ)
    (hbudget1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
        + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
        + shellError R H t g κ
      ≤ cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)))
    (hbudget2 : ρ < c₀ * (R.eps : ℝ))
    (hfail : logChowla2Fails R.eps R.x R.ω) : False := by
  classical
  have hepsRpos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hepshalf : (R.eps : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) * (R.eps : ℝ) ≤ 1 := by
      exact_mod_cast (by linarith [R.heps1] : (2 : ℚ) * R.eps ≤ 1)
    linarith
  have hepssq : (R.eps : ℝ) ^ 2 ≤ 1 := by nlinarith [hepshalf, hepsRpos]
  -- floor bookkeeping
  have hHnatM : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hH3 : 3 ≤ H := by omega
  have hH₀red : H₀red ≤ H := le_trans (le_max_left _ _) hH₀
  have hH₀D3 : H₀D3 ≤ H := le_trans (le_max_right _ _) hH₀
  -- real-side H facts
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHnatM
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  have hlogH : 1 ≤ Real.log (H : ℝ) := by
    rw [Real.le_log_iff_exp_le hHpos]
    exact le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
  have hlogHpos : 0 < Real.log (H : ℝ) := by linarith
  -- the regime discharges (sqrt / ω / x / head)
  have hreg : Real.sqrt (H : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) / 2 :=
    sqrt_le_window_at R hlo hhi
  have hsqrt2000 : (2000 : ℝ) ≤ Real.sqrt (H : ℝ) := by
    rw [show (2000 : ℝ) = Real.sqrt 4000000 by
      rw [show (4000000 : ℝ) = 2000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hHR
  have h4 : (4 : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) := by nlinarith [hreg, hsqrt2000]
  have hωbig : (16 / (R.eps : ℝ)) * Real.log ((R.eps : ℝ) ^ 2 * (H : ℝ))
      + 64 / (R.eps : ℝ) + 1 ≤ Real.log (R.ω : ℝ) := omega_big_at R hhi h4
  have hxbig : (R.ω : ℝ) * (H : ℝ)
      + 48 * (R.ω : ℝ) * (1 + 2 / (R.eps : ℝ) ^ 2) / (R.eps : ℝ) ≤ (R.x : ℝ) :=
    x_big_at R hhi
  have hhead : 8 * (PH R.eps H : ℝ) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ) := pH_headroom_at R hhi
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
  -- the single-correlation seed and the reduce (h211 producer)
  set X : ℝ := |∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure R.x R.ω)| with hXdef
  have hseed : (R.eps : ℝ) / 2 ≤ X :=
    singleCorr_of_fails R.eps R.hx R.hω R.hωx hlog2 hfail
  have hredH : (1 / 2) * SP * (H : ℝ) * X
      ≤ |∫ n, fBridgeF R.eps H (liouvilleWindow H n) (residueWindow R.eps H n)
          ∂(logMeasure R.x R.ω)| :=
    hred R.eps H R.x R.ω R.hx R.hω R.hωx R.heps hepssq hH3 hlogH h4 hreg hH₀red hepsc
      hωbig hxbig hseed
  -- the concrete h211 (coefficient c₁ = cD3/4)
  have hAX : (cD3 / Real.log (H : ℝ)) * ((R.eps : ℝ) / 2) ≤ SP * X :=
    mul_le_mul hmert hseed (by positivity) hSPnn
  have h211 : cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
      ≤ |∫ n, fBridgeF R.eps H (liouvilleWindow H n) (residueWindow R.eps H n)
          ∂(logMeasure R.x R.ω)| := by
    calc cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        = (1 / 2) * (H : ℝ) * ((cD3 / Real.log (H : ℝ)) * ((R.eps : ℝ) / 2)) := by
          field_simp; ring
      _ ≤ (1 / 2) * (H : ℝ) * (SP * X) :=
          mul_le_mul_of_nonneg_left hAX (by positivity)
      _ = (1 / 2) * SP * (H : ℝ) * X := by ring
      _ ≤ _ := hredH
  -- the SQUARED circle-method bound (hcirc) via the card discharge, at the diagonal
  have hcard : ((primeWindow R.eps H).card : ℝ)
      ≤ (2 * Real.log 4) * ((R.eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) :=
    primeWindow_card_le_of_regime R.eps H hreg hH3
  have hcirc : ∀ n : ℕ,
      |∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2)
                * ‖ZMod.dft (fun j : ZMod H =>
                    (windowVal H (liouvilleWindow H n) (ZMod.val j) : ℂ)) ξ‖ ^ 2) :=
    fun n => hcm R.eps H (liouvilleWindow H n)
      (fun i => abs_liouvilleWindow_le_one H n i) hcard
  -- fire the Ξ-SUMMED L² shell (no `hXi`, no `0 ≤ δ`: the seam needs neither)
  exact log_chowla_two_shell_xi_sq R hlo hhi hH3 hlogH hne hreg hhead ht hg hgle hI
    (by positivity) h211 hC hcirc hdoor hbudget1 hbudget2

/-- **THE `L²` SPINE-BUDGET HEAD, count-exporting form**
(`log_chowla_two_budget_head_g_sq_count`, ⟦THE L² RESTRUCTURE⟧ stone 4).

The twin of `log_chowla_two_budget_head_g_45` at the Ξ-SUMMED `L²` door, with

```
δ₀ := cD3 / (16 · C) · ε / 4          -- = c₀·ε/4,  c₀ = cD3/(16·C)
```

— **`K`-FREE**.  The landed head's `δ₀ = c₀·ε/(2K)` divided by the frequency
count because the `L¹` seam multiplied the door's grade by `|Ξ_H| ≤ K`
(`contradiction_of_mrtDoorXi`'s `hsmall : K·δ < c₀·ε`).  The summed `L²` seam
(`contradiction_of_mrtDoorXiL2`) reads the door's grade ONCE, so its budget is
`hbudget2 : ρ < c₀·ε` and the count leaves the `δ`-line entirely.  The `4` is
REF-L2-ARITH's share allocation (`δ₀' = c₀ε/4`, `1.19·10^(-6)` at the certified
constants); the derivation is the landed `:944–953` block minus the `K` step —
`ρ ≤ c₀ε/4 < c₀ε` since `c₀ε > 0`, the same strict-margin shape the landed proof
got from `K·δ ≤ c₀ε/2 < c₀ε`.

⟦THE COUNT, EXPORTED⟧  `|Ξ_H| ≤ K` has not left the argument, only the spine: in
the `L²` architecture the road spends it (`M4Window`'s adapter multiplies the
SIEVED leg by `K`, the α-independent insert leg being paid once by Parseval).
Only the head knows `ε`, hence only the head can produce the `K` that goes with
it — so this form carries `K` in the `∃`-prefix and delivers the gate

```
∀ H, [NeZero H] → R.Hlo ≤ H → H ≤ R.Hhi → (|Ξ_H| : ℝ) ≤ K
```

as a payload conjunct, placing `bigXi_bounded`'s own floor `H₀xi` under `R.Hlo`
exactly as the landed head does.  `K` NEVER touches `δ₀`.

⟦THE TOWER PAYLOAD⟧ is the `9/2` law (ruling C-A) as in
`log_chowla_two_budget_head_g_45`; `Salt.MR.tower_conjunct_45_le_five` downgrades
it to `^5` for consumers wired to the landed exponent.

⚠ **THE SEAM WARNING** (`MRTDoor.lean:174–182`, REF-L2 mandate R4, re-stated on
the twin per the doctrine).  THE QUANTIFIERS STAY OUTSIDE THE INTEGRAL.
`MRTUniformityXiL2 R ρ` is a FINITE SUM OF INTEGRALS — the frequency quantifier is
a `∑` over `Ξ_H` outside `∫`, with no `sup` inside.  The sup-inside form is Tao
1509.05422 (4.1), which is OPEN; moving a quantifier inside silently downgrades a
theorem-door (Prop 2.4, PROVEN in Matomäki–Radziwiłł–Tao, arXiv:1503.05121) into
an open conjecture.  This head does not CLAIM the `L²` door from Prop 2.4: it is
supplied by the ROAD (`Salt.MR.mrtUniformityXiL2_of_absWindowSqBound`, over the
sieved socket and the Parseval insert stone), and
`MRTDoor.mrtUniformityXiL2_of_xi` records that it is in any case IMPLIED by the
landed `L¹` theorem-door at grade `K·δ`.

Everything else is `log_chowla_two_budget_head_g_45`'s proof verbatim: the same
`ε` choice below `min(min(min (cE/(32·log4)) (1/2)) (cD3/16)) (cD3/(16·C))`, the
same `hbudget1_witness` discharge at `c₀ = cD3/(16·C)`, the same five-arm floor,
the same `chowlaRegime_exists_param_head_tower45'` builder.  `C` now comes from
`circle_method_estimate_sq` — the SAME constant `1 + 2·C₀`, so `hbudget1` is
untouched. -/
theorem log_chowla_two_budget_head_g_sq_count :
    ∃ (ε : ℚ) (K δ₀ : ℝ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      ∀ (extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), ∃ R : ChowlaRegime,
        R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
        (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
          ((bigXi R.eps H).card : ℝ) ≤ K) ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨cE, hcE, H₀red, hred⟩ := hreduce_holds_final
  obtain ⟨cD3, hcD3, H₀D3, hD3⟩ := primeWindow_sum_inv_ge
  -- ⟦THE ONE CHANGED PRODUCER⟧ the SQUARED circle-method estimate; `C = 1 + 2C₀` unchanged
  obtain ⟨C, hC, hcm⟩ := circle_method_estimate_sq (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- choose ε below `min(min(min (cE/(32·log4)) (1/2)) (cD3/16)) (cD3/(16·C))`
  have hbound_pos : (0 : ℝ) < min (min (min (cE / (32 * Real.log 4)) (1 / 2))
      (cD3 / 16)) (cD3 / (16 * C)) := by
    refine lt_min (lt_min (lt_min ?_ ?_) ?_) ?_
    · exact div_pos hcE (mul_pos (by norm_num) hlog4)
    · norm_num
    · exact div_pos hcD3 (by norm_num)
    · exact div_pos hcD3 (mul_pos (by norm_num) hC)
  obtain ⟨ε, hε0, hεlt⟩ := exists_rat_btwn hbound_pos
  have hεR0 : (0 : ℝ) < (ε : ℝ) := hε0
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := le_of_lt (lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)))
  have hε_half_lt : (ε : ℝ) < 1 / 2 := lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _))
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := le_of_lt (lt_of_lt_of_le hεlt
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := le_of_lt (lt_of_lt_of_le hεlt (min_le_right _ _))
  have hεQ1 : ε ≤ 1 / 2 := by
    have h2 : (2 : ℝ) * (ε : ℝ) < 1 := by linarith [hε_half_lt]
    have h2Q : (2 : ℚ) * ε < 1 := by exact_mod_cast h2
    linarith
  have hε2 : (ε : ℝ) ^ 2 < 1 / 2 := by nlinarith [hεR0, hε_half_lt]
  obtain ⟨K, hK, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded ε hεQpos hε2
  -- ⟦THE K-FREE δ₀⟧ `c₀·ε/4`, NOT `c₀·ε/(2K)`
  refine ⟨ε, K, cD3 / (16 * C) * (ε : ℝ) / 4, hεQpos, hK,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num), ?_⟩
  intro extraFloor U1floor g₅
  obtain ⟨R, hReps, hRHlo, hRg, hRtow⟩ := chowlaRegime_exists_param_head_tower45' ε hεQpos hεQ1
    (max (max (max (max H₀red H₀D3) H₀xi)
      (budgetFloor (ε : ℝ) (cD3 * (ε : ℝ) / (144 * Real.log 4)))) (max extraFloor U1floor)) g₅
  have hxiHlo : H₀xi ≤ R.Hlo :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hRHlo
  refine ⟨R, hReps, le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, ?_, hRtow, ?_⟩
  · -- ⟦THE EXPORTED COUNT GATE⟧ the road's `hXi`, at this head's own `ε`
    intro H' _ hlo' _
    rw [hReps]
    exact hxi H' (le_trans hxiHlo hlo')
  intro ρ _hρpos hρ hdoor hfail
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrement R
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
    rw [mutualInfo_window_comm']; exact hMI
  have hepscR : (R.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max H₀red H₀D3 ≤ H :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_left _ _)) hRHlo) hlo
  have hfloorH : budgetFloor (R.eps : ℝ)
      (cD3 * (R.eps : ℝ) / (144 * Real.log 4)) ≤ H := by
    rw [hReps]
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRHlo) hlo
  obtain ⟨t, g, ht, hg, hgle, hbudget1⟩ :=
    hbudget1_witness R H cD3 C hcD3 hC
      (by rw [hReps]; exact le_of_lt hε_half_lt)
      (by rw [hReps]; exact hε_D3)
      (by rw [hReps]; exact hε_D3C) hhi hfloorH
  -- ⟦THE K-FREE hbudget2⟧ `ρ ≤ c₀ε/4 < c₀ε` (the landed `:944–953` chain minus the K step)
  have hbudget2 : ρ < cD3 / (16 * C) * (R.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hρ, hpos]
  exact spine_False_core_xi_sq R hdoor cE hcE H₀red hred cD3 hcD3 H₀D3 hD3
    C hC hcm H hlo hhi hH₀ hepscR t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail

/-- **THE `L²` SPINE-BUDGET HEAD** (`log_chowla_two_budget_head_g_sq`) — the
count-exporting head with its count conjunct dropped, i.e. the exact `∃ ε δ₀`
shape of `log_chowla_two_budget_head_g(_45)` with

* the door hypothesis `MRTUniformityXiL2 R ρ` (Ξ-SUMMED, `L²`-integrand) in place
  of `MRTUniformityXi R δ`, and
* the **`K`-FREE** threshold `δ₀ = cD3/(16·C) · ε / 4` in place of
  `cD3/(16·C) · ε / (2K)`.

Use `log_chowla_two_budget_head_g_sq_count` when the consumer also needs the
large-spectrum count `|Ξ_H| ≤ K` (the `L²` road does: `M4Window`'s adapter spends
it on the sieved leg).  The seam warning on that head rides here unchanged. -/
theorem log_chowla_two_budget_head_g_sq :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ (extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), ∃ R : ChowlaRegime,
        R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨ε, _K, δ₀, hε, _hK, hδ₀, hbody⟩ := log_chowla_two_budget_head_g_sq_count
  refine ⟨ε, δ₀, hε, hδ₀, fun extraFloor U1floor g => ?_⟩
  obtain ⟨R, hReps, hExtra, hU1, hRg, _hcount, hRtow, hR⟩ := hbody extraFloor U1floor g
  exact ⟨R, hReps, hExtra, hU1, hRg, hRtow, hR⟩

end Salt.Entropy.Chowla
