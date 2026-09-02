/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦THE FLAT HEAD AT SHIFT `h`⟧ — wave X of the `_L_gk` h-family, part (ii)

`HloExportFlat.log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat` is the `h = 1` road's
EXIT: it chooses `ε`, exports the pins `1/500 ≤ ε` and `1/838400 ≤ δ₀`, and closes
`∀ ρ ≤ δ₀, MRTUniformityXiL2 R ρ → ¬ logChowla2Fails`.  Nothing on `main` concluded
`¬ logChowlaFails h` for `h ≠ 1`: the `h`-register `m4_second_road_L2_H_gk_flatRoot_L`
(`Salt/MR/S16FlatTerminalLinearH.lean`) is in DOOR FORM precisely because no exit existed at
shift `h`.  This file is that exit.

⟦WHAT MOVES — FOUR SCALINGS, ONE BINDER, NOTHING ELSE⟧  (a) the pins scale to `1/(500·h) ≤ ε`
and `1/(838400·h²) ≤ δ₀`, under which EVERY gate of the landed head takes exactly its `h = 1`
value: the HBudget gate reads `ε·h = 1/500`, `hε_D3C` reads `16·C·ε ≤ 16·(6.55h)/(500h)` with
the `h` cancelling, and `hδ₀ge` is exact at zero slack (`5/(2096h) · (1/(500h)) / 4 =
1/(838400h²)`); (b) the circle constant is capped at `C ≤ h·(1 + 2·C₀)` (`HeadPinLeavesH`),
the `h`-core's own `refine` witness; (c) the large-spectrum count set is `bigXiH h` with
`K := h·Cxi` from `bigXiH_bounded` — existential, no numeral moves; (d) `0 < h` is a stated
binder, required by every `_h` leaf and by the pins themselves.  The conclusion is
`¬ logChowlaFails h R.eps R.x R.ω` (`ShiftFork.lean:62`), NEVER `¬ logChowla2Fails`, which
hard-codes shift `1` and from which nothing derives the shift-`h` seed.

⟦WHAT DOES NOT MOVE⟧  `A`, `β`, `Hopq`, the flat cap equation, the regime witness, the tower
conjunct, `hbudget1`'s symbolic witness and the `κ = H/(A·log H)` threshold are the landed
head's, unchanged.  ⛔ `hh7 : log h ≤ 7` is NOT carried: nothing here pays for it, and
carrying it would narrow the exit below what it proves.

⟦THE IMPORT GATE⟧  `HloExportFlat`'s closure already holds `ShiftFork`, `Theorem23Shell`,
`ChowlaFailure`, `HBudget`, `HeadPinLeaves` and `CircleMethod`.  This file adds only Entropy-side
modules; there is no `Salt.MR.*` edge, and the MR side consumes this file, never the reverse.

⟦THE `ρ`-THREAD⟧  `ρ` stays FREE here exactly as at `h = 1`: `ρ ≤ δ₀` is a hypothesis of the
composed statement, discharged by the consumer's budget line and never here.

Nothing here bears on twin primes: the exit at shift `h` is conditional on the same open door
(`MRTUniformityXiL2H h R ρ`) its `h = 1` twin is conditional on.
-/
import Salt.Entropy.Chowla.HloExportFlat
import Salt.Entropy.Chowla.HeadPinLeavesH
import Salt.Entropy.Chowla.Theorem23Shell

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-- **The `L²` spine contradiction core, flat-file twin, AT SHIFT `h`**
(`spine_False_core_xi_sq_flat_h`) — `HloExportFlat.spine_False_core_xi_sq_flat` (`private`,
`HloExportFlat.lean:60`) VERBATIM under a fresh name with the shift threaded: the seed is
`singleCorr_of_fails_h`, the reduce arrives from `hreduce_holds_final_h_bounded` at the gate
`ε·h ≤ cE/(32·log 4)`, the circle estimate sums over `bigXiH h`, and the shell is
`log_chowla_two_shell_xi_sq_h`.  The bridge is `fBridgeF_h eps H h`; the failure Prop is
`logChowlaFails h` (`ShiftFork.lean:62`), passed to the seed by definitional unfolding.  The
core takes `κ` as an EXPLICIT ARGUMENT, so it is threshold-agnostic, as at `h = 1`. -/
private theorem spine_False_core_xi_sq_flat_h (h : ℕ) (hh : 0 < h) (R : ChowlaRegime) {ρ : ℝ}
    (hdoor : MRTUniformityXiL2H h R ρ)
    (cE : ℝ) (_hcE : 0 < cE) (H₀red : ℕ)
    (hred : ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀red ≤ H →
      (eps : ℝ) * (h : ℝ) ≤ cE / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1
          ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
          ≤ (x : ℝ) →
      (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| →
      (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|)
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
          (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiH h eps H, (1 / (H : ℝ) ^ 2)
                * ‖(ZMod.dft (fun j : ZMod H =>
                    (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2))
    (H : ℕ) [NeZero H] (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    (hH₀ : max H₀red H₀D3 ≤ H)
    (hepsc : (R.eps : ℝ) * (h : ℝ) ≤ cE / (32 * Real.log 4))
    (t g κ c₀ : ℝ) (ht : 0 < t) (hg : 0 < g)
    (hgle : g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
        / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    (hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω] ≤ κ)
    (hbudget1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
        + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
        + shellError R H t g κ
      ≤ cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)))
    (hbudget2 : ρ < c₀ * (R.eps : ℝ))
    (hfail : logChowlaFails h R.eps R.x R.ω) : False := by
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
      * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure R.x R.ω)| with hXdef
  have hseed : (R.eps : ℝ) / 2 ≤ X :=
    singleCorr_of_fails_h h R.eps R.hx R.hω R.hωx hlog2 hfail
  have hredH : (1 / 2) * SP * (H : ℝ) * X
      ≤ |∫ n, fBridgeF_h R.eps H h (liouvilleWindow H n) (residueWindow R.eps H n)
          ∂(logMeasure R.x R.ω)| :=
    hred R.eps H R.x R.ω R.hx R.hω R.hωx R.heps hepssq hH3 hlogH h4 hreg hH₀red hepsc
      hωbig hxbig hseed
  -- the concrete h211 (coefficient c₁ = cD3/4)
  have hAX : (cD3 / Real.log (H : ℝ)) * ((R.eps : ℝ) / 2) ≤ SP * X :=
    mul_le_mul hmert hseed (by positivity) hSPnn
  have h211 : cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
      ≤ |∫ n, fBridgeF_h R.eps H h (liouvilleWindow H n) (residueWindow R.eps H n)
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
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiH h R.eps H, (1 / (H : ℝ) ^ 2)
                * ‖ZMod.dft (fun j : ZMod H =>
                    (windowVal H (liouvilleWindow H n) (ZMod.val j) : ℂ)) ξ‖ ^ 2) :=
    fun n => hcm R.eps H (liouvilleWindow H n)
      (fun i => abs_liouvilleWindow_le_one H n i) hcard
  exact log_chowla_two_shell_xi_sq_h h R hlo hhi hH3 hlogH hne hreg hhead ht hg hgle hI
    (by positivity) h211 hC hcirc hdoor hbudget1 hbudget2

/-! ### §2 — THE FLAT HEAD -/


/-! ### §2 — THE FLAT HEAD AT SHIFT `h` -/

/-- **THE `L²` SPINE-BUDGET HEAD AT THE FLAT THRESHOLD, CAPPED AND PINNED, AT SHIFT `h`**
(`log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat_h`).

`HloExportFlat.log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat` with the four scalings
of the file header and nothing else.  The proof is the landed body with those substitutions;
`A`, `β`, `Hopq`, the cap equation and the regime witness are byte-identical, and every numeral
of the landed head is recovered at the pinned `ε` because `ε·h = 1/500` exactly.

⚠ THE SEAM WARNING rides this statement unchanged (`MRTDoor.lean:174–182`). -/
theorem log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat_h (h : ℕ) (hh : 0 < h)
    (A₀ : ℝ) (hA₀ : 26 ≤ A₀) :
    ∃ (ε : ℚ) (K δ₀ A β : ℝ) (Hcap Hopq : ℕ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧ 0 < β ∧ 26 ≤ A ∧ A₀ ≤ A ∧
      budgetAFlat (ε : ℝ) β ≤ A ∧
      Hcap = max (flatDesignFloor A)
        (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
      ∀ (extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), ∃ R : ChowlaRegime,
        R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
        (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
          ((bigXiH h R.eps H).card : ℝ) ≤ K) ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        R.Hlo ≤ max Hcap (max extraFloor U1floor) ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2H h R ρ →
          ¬ logChowlaFails h R.eps R.x R.ω := by
  classical
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  obtain ⟨cE, hcE, hcEge, H₀red, hred⟩ := hreduce_holds_final_h_bounded
  obtain ⟨cD3, hcD3, hcD3ge, H₀D3, hD3⟩ := primeWindow_sum_inv_ge_bounded
  obtain ⟨C, hC, hCcap, hcm⟩ := circle_method_estimate_sq_bounded_h h hh (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- ⟦THE LEAF NUMERALS⟧ `log 4 = 2·log 2 < 1.3863`, hence `C ≤ 6.55·h`
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hCnum : C ≤ (h : ℝ) * (655 / 100) := by
    rw [hlog4eq] at hCcap
    nlinarith [hCcap, hhR, hlog2lt]
  -- ⟦THE PIN⟧ `ε := 1/(500·h)`, so `ε·h = 1/500`: every gate reads as at `h = 1`
  obtain ⟨ε, hεdef⟩ : ∃ e : ℚ, e = 1 / (500 * (h : ℚ)) := ⟨_, rfl⟩
  have hεR : ((ε : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) := by rw [hεdef]; push_cast; ring
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by rw [hεR]; positivity
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεh : (ε : ℝ) * (h : ℝ) = 1 / 500 := by rw [hεR]; field_simp
  have hεcE : (ε : ℝ) * (h : ℝ) ≤ cE / (32 * Real.log 4) := by
    rw [hεh, le_div_iff₀ (by positivity), hlog4eq]
    linarith
  have hε500 : (ε : ℝ) ≤ 1 / 500 := by
    rw [hεR]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hε_half_lt : (ε : ℝ) < 1 / 2 := by linarith
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]; linarith
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]
    have h1 : (ε : ℝ) * (16 * C) ≤ (ε : ℝ) * (16 * ((h : ℝ) * (655 / 100))) := by
      gcongr
    have h2 : (ε : ℝ) * (16 * ((h : ℝ) * (655 / 100)))
        = 16 * (655 / 100) * ((ε : ℝ) * (h : ℝ)) := by ring
    rw [hεh] at h2
    linarith
  have hεQ1 : ε ≤ 1 / 2 := by
    have hhQ : (1 : ℚ) ≤ (h : ℚ) := by exact_mod_cast hh
    rw [hεdef]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hε2 : (ε : ℝ) ^ 2 < 1 / 2 := by nlinarith [hε500, hεR0]
  -- ⟦THE `δ₀` FLOOR⟧ the binding arm at its worst case, exact at zero slack
  have hδ₀ge : (1 : ℝ) / (838400 * (h : ℝ) ^ 2) ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    have hkey : (5 : ℝ) / (2096 * (h : ℝ)) ≤ cD3 / (16 * C) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]
      have h1 : (5 : ℝ) / (2096 * (h : ℝ)) * (16 * C)
          ≤ (5 : ℝ) / (2096 * (h : ℝ)) * (16 * ((h : ℝ) * (655 / 100))) := by
        gcongr
        positivity
      have h2 : (5 : ℝ) / (2096 * (h : ℝ)) * (16 * ((h : ℝ) * (655 / 100))) = 1 / 4 := by
        field_simp; ring
      linarith
    have hstep : (1 : ℝ) / (838400 * (h : ℝ) ^ 2)
        = (5 : ℝ) / (2096 * (h : ℝ)) * (1 / (500 * (h : ℝ))) / 4 := by
      field_simp; ring
    rw [hstep, hεR]
    have hpos : (0 : ℝ) < 1 / (500 * (h : ℝ)) := by positivity
    gcongr
  -- ⟦THE COUNT⟧ `bigXiH h` bounded by `h·Cxi`, existential (word 8(c))
  obtain ⟨Cxi, hCxi, H₀xi, _hH₀xi2, hxi⟩ := bigXiH_bounded h hh ε hεQpos hε2
  -- ⟦THE FLAT DESIGN CONSTANT⟧ symbolic: the caller's `A₀`, raised to the budget demand
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = cD3 * (ε : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hcD3 hεR0) (by positivity)
  obtain ⟨A, hAdefA⟩ : ∃ a : ℝ, a = max A₀ (budgetAFlat (ε : ℝ) β) := ⟨_, rfl⟩
  have hA26 : 26 ≤ A := by rw [hAdefA]; exact le_trans hA₀ (le_max_left _ _)
  have hA₀A : A₀ ≤ A := by rw [hAdefA]; exact le_max_left _ _
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by rw [hAdefA]; exact le_max_right _ _
  -- ⟦THE HEAD'S OWN FOUR-ARM FLOOR⟧ (flat), and the consumer-free cap it induces
  obtain ⟨Hopq, hOpqdef⟩ : ∃ n : ℕ, n = max (max H₀red H₀D3) H₀xi := ⟨_, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ n : ℕ, n = max Hopq (budgetFloorFlat (ε : ℝ) β A) := ⟨_, rfl⟩
  refine ⟨ε, (h : ℝ) * Cxi, cD3 / (16 * C) * (ε : ℝ) / 4, A, β,
    max (flatDesignFloor A) (max F (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), Hopq, hεQpos, mul_pos hhR hCxi,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num),
    hεdef.ge, hδ₀ge, hβpos, hA26, hA₀A, hAge, by rw [hFdef], ?_⟩
  intro extraFloor U1floor g₅
  obtain ⟨Rf, hReps, hRA, hRHlo, hRg, _hRcapEq, hRwid⟩ :=
    chowlaRegimeFlat_exists_param_head A hA26 ε hεQpos hεQ1
      (max F (max extraFloor U1floor)) g₅
  have hFlo : F ≤ Rf.Hlo := le_trans (le_max_left _ _) hRHlo
  have hxiHlo : H₀xi ≤ Rf.Hlo := by
    rw [hFdef, hOpqdef] at hFlo
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hFlo
  have hbudHlo : budgetFloorFlat (ε : ℝ) β A ≤ Rf.Hlo := by
    rw [hFdef] at hFlo; exact le_trans (le_max_right _ _) hFlo
  have hredHlo : max H₀red H₀D3 ≤ Rf.Hlo := by
    rw [hFdef, hOpqdef] at hFlo
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hFlo
  refine ⟨Rf.toChowlaRegime, hReps,
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, ?_,
    fun _ => hRwid, ?_, ?_⟩
  · -- ⟦THE EXPORTED COUNT GATE⟧ the road's `hXi`, at this head's own `ε`
    intro H' _ hlo' _
    rw [hReps]
    exact hxi H' (le_trans hxiHlo hlo')
  · -- ⟦THE CAP⟧ the flat base equation, shuffled onto the consumer's floors
    rw [_hRcapEq]
    exact flatCap_shuffle _ _ _ _ _
  intro ρ _hρpos hρ hdoor hfail
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrementFlat Rf
  have hH4 : 4000000 ≤ H := le_trans Rf.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow Rf.eps H : liouvilleWindow H ; logMeasure Rf.x Rf.ω]
      ≤ (H : ℝ) / (Rf.A * Real.log H) := by
    rw [mutualInfo_window_comm_flat]; exact hMI
  have hepsc : (Rf.eps : ℝ) * (h : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max H₀red H₀D3 ≤ H := le_trans hredHlo hlo
  have hβR : cD3 * (Rf.eps : ℝ) / (144 * Real.log 4) = β := by rw [hReps, hβdef]
  have hAgeR : budgetAFlat (Rf.eps : ℝ) (cD3 * (Rf.eps : ℝ) / (144 * Real.log 4)) ≤ Rf.A := by
    rw [hβR, hReps, hRA]; exact hAge
  have hfloorH : budgetFloorFlat (Rf.eps : ℝ)
      (cD3 * (Rf.eps : ℝ) / (144 * Real.log 4)) Rf.A ≤ H := by
    rw [hβR, hReps, hRA]
    exact le_trans hbudHlo hlo
  obtain ⟨t, g, ht, hg, hgle, hbudget1⟩ :=
    hbudget1_witnessFlat Rf H cD3 C hcD3 hC
      (by rw [hReps]; exact le_of_lt hε_half_lt)
      (by rw [hReps]; exact hε_D3)
      (by rw [hReps]; exact hε_D3C) hhi hAgeR hfloorH
  -- ⟦THE K-FREE hbudget2⟧ `ρ ≤ c₀ε/4 < c₀ε`
  have hbudget2 : ρ < cD3 / (16 * C) * (Rf.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hρ, hpos]
  -- ⟦THE CORE⟧ at the FLAT threshold `κ = H/(A·log H)`
  exact spine_False_core_xi_sq_flat_h h hh Rf.toChowlaRegime hdoor cE hcE H₀red
    (fun eps H x ω => hred h eps H x ω hh) cD3 hcD3
    H₀D3 hD3 C hC hcm H hlo hhi hH₀ hepsc t g
    ((H : ℝ) / (Rf.A * Real.log H)) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail

end Salt.Entropy.Chowla
