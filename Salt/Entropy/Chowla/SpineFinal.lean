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

/-- **THE terminal log-Chowla-2 surface.**  Tao's logarithmically-averaged
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

end Salt.Entropy.Chowla
