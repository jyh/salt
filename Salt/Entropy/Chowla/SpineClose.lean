/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The terminal glue of the log-Chowla spine (Tao arXiv:1509.05422v1 §2–§3), node W3E-FINAL

The single theorem closing the conditional chain
(`docs/exploration/s3-a3-design.md`, "W3-e-final — THE TERMINAL GLUE").  The four
landed keystones + the producer chains compose into `log_chowla_two_shell`'s
contradiction, with the still-open inputs threaded through as explicit hypotheses.
-/
import Salt.Entropy.Chowla.Theorem23Shell
import Salt.Entropy.Chowla.HBudget
import Salt.Entropy.Chowla.GoldbachEnergyFinal
import Salt.Entropy.Chowla.ChowlaFailure
import Salt.Entropy.Chowla.Prop26
import Salt.Entropy.Chowla.WindowMertensLower
import Salt.Entropy.Chowla.WindowCount
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-- **W3E-FINAL, the terminal glue.**  Composes the landed producer chains and the
four spine keystones into `log_chowla_two_shell`'s contradiction. -/
theorem log_chowla_two_conditional (R : ChowlaRegime) {δ : ℝ}
    (hdoor : MRTUniformity R δ) :
    ∃ (c₁ C K cE : ℝ) (H₀ : ℕ), 0 < c₁ ∧ 0 < C ∧ 0 < K ∧ 0 < cE ∧
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
  -- basic ε facts (regime-uniform)
  have hepsRpos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hepshalf : (R.eps : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) * (R.eps : ℝ) ≤ 1 := by
      exact_mod_cast (by linarith [R.heps1] : (2 : ℚ) * R.eps ≤ 1)
    linarith
  have hepssq : (R.eps : ℝ) ^ 2 ≤ 1 := by nlinarith [hepshalf, hepsRpos]
  have heps2 : (R.eps : ℝ) ^ 2 < 1 / 2 := by nlinarith [hepshalf, hepsRpos]
  -- obtain the four opaque chains (all H-uniform)
  obtain ⟨cE, hcE, H₀red, hred⟩ := hreduce_holds_final
  obtain ⟨cD3, hcD3, H₀D3, hD3⟩ := primeWindow_sum_inv_ge
  obtain ⟨C, hC, hcm⟩ := circle_method_estimate (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  obtain ⟨K, hK, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded R.eps R.heps heps2
  refine ⟨cD3 / 4, C, K, cE, max (max H₀red H₀D3) H₀xi,
    by positivity, hC, hK, hcE, ?_⟩
  intro H hNe hlo hhi hH₀ hepsc t g κ c₀ ht hg hgle hI hbudget1 hbudget2 hfail
  haveI : NeZero H := hNe
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

/-- **W3E-FINAL, the quotable citation surface.**  log-Chowla-2 (Tao arXiv:1509.05422v1,
the model `a=1,b=0,h=1,g₁=g₂=λ` form of Chowla's two-point conjecture) holds
CONDITIONAL on exactly three families of inputs — this theorem certifies that if
log-Chowla-2 FAILS on the regime then a contradiction follows, given:

1. **The MRT uniformity theorem** (`hdoor : MRTUniformity R δ`): Tao's
   Proposition 2.4, which is PROVEN in Matomäki–Radziwiłł–Tao, arXiv:1503.05121
   ("An averaged form of Chowla's conjecture"); it enters here as an explicit
   hypothesis (a published theorem-door, the strongest honesty class).
2. **The tower-budget numerics** (`hbudget1`, `hbudget2` inside the ∀, plus the
   decrement budgets `ht`/`hg`/`hgle`/`hI` and the coupling `hepsc`): the
   tower/entropy machinery is expected to discharge these downstream; they stay
   explicit at this node (the honest scope — see `docs/exploration/s3-a3-design.md`,
   "THE HONEST SCOPE").  The obtained constants `c₁ = cD3/4`, `C`, `K`, `cE` are
   the opaque outputs of the landed producer chains, so the statement is
   ∃-quantified over them and the combined regime floor `H₀`.
3. **The stated regime range** (`R.Hlo ≤ H`, `H ≤ R.Hhi`, `H₀ ≤ H`): the tower's
   admissible `H`-window with the finitely-many opaque floors folded into `H₀`.

Everything else — the `(2.11)` producer chain (`h211`), Lemma 3.4 (the circle
method, `hcirc`), Lemma 3.5 (`|Ξ_H| ≤ K`, `hXi`), and the 13-row regime discharge
of `hreduce_holds_final` — is COMPOSED internally (see `log_chowla_two_conditional`).
The `∀ α`-outside-the-integral invariant of `MRTUniformity` is what keeps input (1)
a theorem rather than Tao's open (4.1). -/
theorem log_chowla_two_conditional_regime (R : ChowlaRegime) {δ : ℝ}
    (hdoor : MRTUniformity R δ) :
    ∃ (c₁ C K cE : ℝ) (H₀ : ℕ), 0 < c₁ ∧ 0 < C ∧ 0 < K ∧ 0 < cE ∧
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
          False :=
  log_chowla_two_conditional R hdoor

end Salt.Entropy.Chowla
