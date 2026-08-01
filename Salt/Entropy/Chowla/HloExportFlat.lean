/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# THE FLAT SPINE HEAD — `hloCap`-carrying, pinned, HEIGHT 1 (freeze F-1..F-5)

`HloExport.log_chowla_two_budget_head_g_sq_count_hloCap_pinned` is the landed
head the whole MR road hangs from.  This file is its FLAT twin: the same
statement with

* the regime produced by the FLAT builder (`chowlaRegimeFlat_exists_param_head`),
  so the exported tower conjunct is the A-FREE WIDTH EXPORT
  `loglog H₊ ≤ exp (loglog H₋ / 2)` (freeze F-5) rather than the landed `9/2`;
* the mutual-information bound produced by `entropy_decrementFlat` at the FLAT
  threshold `κ = H/(A·log H)` (freeze F-2);
* the spine-budget residual discharged by `hbudget1_witnessFlat` against
  `budget_factsFlat` (freeze F-3), whose floor `budgetFloorFlat` is a SINGLE
  exponential where the landed `budgetFloor` is a TRIPLE one;
* four extra `∃`-prefix items — `A`, `β`, `Hcap`, `Hopq` — and the CAP EQUATION

```
Hcap = max (flatDesignFloor A) (max (max Hopq (budgetFloorFlat ε β A)) (4·⌈1/ε⌉₊⁴))
```

  which is the landed cap's shape with `4·10⁶ ⟶ flatDesignFloor A` and
  `budgetFloor ⟶ budgetFloorFlat`.  THAT is the height collapse, stated so a
  consumer can see it: the only opaque arm is `Hopq` (the three leaf floors,
  IDENTICAL to the landed head's), and both named arms are `⌈exp ·⌉₊`.

Everything is additive; no landed declaration is touched.  The two `private`
items of `HloExport` — the `max`-shuffle and the in-file transcription of
`SpineFinal`'s `private` core — are re-stated here under fresh names for the same
reason they were re-stated there: `private` blocks citation across files.  The
core is κ-GENERIC (its `κ` is an explicit argument), so the transcription is
byte-for-byte the landed one; only its CALLER changes.
-/
import Salt.Entropy.Chowla.HloExport
import Salt.Entropy.Chowla.SpineFlat
import Salt.Entropy.Chowla.TowerFlatBuilder

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ### §1 — the two re-stated `private` helpers -/

/-- The `max`-lattice shuffle (`HloExport.hloCap_shuffle`, re-stated: `private`
blocks the citation).  Here `a = flatDesignFloor A`. -/
private lemma flatCap_shuffle (a b c d e : ℕ) :
    max a (max (max b (max d e)) c) ≤ max (max a (max b c)) (max d e) := by
  omega

/-- **The `L²` spine contradiction core, flat-file twin**
(`spine_False_core_xi_sq_flat`) — `HloExport.spine_False_core_xi_sq_cap`
(itself `SpineFinal.lean:1164`'s `private` core) VERBATIM under a fresh name.
The core takes `κ` as an EXPLICIT ARGUMENT, so it is threshold-agnostic: the flat
head fires it at `κ = H/(A·log H)` exactly as the landed head fires it at
`κ = H/(log H·logloglog H)`.  Nothing in the body reads the threshold. -/
private theorem spine_False_core_xi_sq_flat (R : ChowlaRegime) {ρ : ℝ}
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
  exact log_chowla_two_shell_xi_sq R hlo hhi hH3 hlogH hne hreg hhead ht hg hgle hI
    (by positivity) h211 hC hcirc hdoor hbudget1 hbudget2

/-! ### §2 — THE FLAT HEAD -/

/-- **THE `L²` SPINE-BUDGET HEAD AT THE FLAT THRESHOLD, CAPPED AND PINNED**
(`log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat`).

`HloExport.log_chowla_two_budget_head_g_sq_count_hloCap_pinned` with FOUR new
`∃`-prefix items (`A`, `β`, and the cap's two components) and the tower conjunct
at the FLAT shape.  The leading `A₀` is the caller's design constant: the head
uses `A = max A₀ (budgetAFlat ε β)`, so `A₀ ≤ A` is exported and the design
constant is under the CONSUMER's control from below while the head still owns the
budget demand `budgetAFlat ε β ≤ A` it must discharge internally.  Nothing is a
numeral: `A` is symbolic throughout (FLAT-REF §4 — the bracket question dissolves
because the whole design is symbolic in `A`).

⟦THE HEIGHT COLLAPSE, VISIBLE IN THE STATEMENT⟧  The exported cap equation

```
Hcap = max (flatDesignFloor A) (max (max Hopq (budgetFloorFlat ε β A)) (4·⌈1/ε⌉₊⁴))
```

is the landed head's cap with two substitutions: `4·10⁶ ⟶ flatDesignFloor A`
(the flat re-basing, FLAT-REF amendment 2) and `budgetFloor ε β ⟶
budgetFloorFlat ε β A`.  The landed `budgetFloor ε β = ⌈e^{e^{e^{X}}}⌉₊` is a
TRIPLE exponential; `budgetFloorFlat ε β A = ⌈e^{max (4X) (2·log A + 2)}⌉₊` is a
SINGLE one.  `Hopq` — the three leaf floors `H₀red`, `H₀D3`, `H₀xi` — is
IDENTICAL to the landed head's, arm for arm.

⚠ THE SEAM WARNING rides this statement unchanged (`MRTDoor.lean:174–182`). -/
theorem log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat (A₀ : ℝ) (hA₀ : 26 ≤ A₀) :
    ∃ (ε : ℚ) (K δ₀ A β : ℝ) (Hcap Hopq : ℕ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧ 26 ≤ A ∧ A₀ ≤ A ∧
      budgetAFlat (ε : ℝ) β ≤ A ∧
      Hcap = max (flatDesignFloor A)
        (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
      ∀ (extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), ∃ R : ChowlaRegime,
        R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
        (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
          ((bigXi R.eps H).card : ℝ) ≤ K) ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        R.Hlo ≤ max Hcap (max extraFloor U1floor) ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨cE, hcE, hcEge, H₀red, hred⟩ := hreduce_holds_final_bounded
  obtain ⟨cD3, hcD3, hcD3ge, H₀D3, hD3⟩ := primeWindow_sum_inv_ge_bounded
  obtain ⟨C, hC, hCcap, hcm⟩ := circle_method_estimate_sq_bounded (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- ⟦THE LEAF NUMERALS⟧ `log 4 = 2·log 2 < 1.3863`, hence `C ≤ 6.55`
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hCnum : C ≤ 655 / 100 := by
    rw [hlog4eq] at hCcap; linarith
  -- ⟦THE PIN⟧ `ε := 1/500`
  obtain ⟨ε, hεdef⟩ : ∃ e : ℚ, e = 1 / 500 := ⟨_, rfl⟩
  have hεR : ((ε : ℚ) : ℝ) = 1 / 500 := by rw [hεdef]; norm_num
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by rw [hεR]; norm_num
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := by
    rw [hεR, le_div_iff₀ (by positivity), hlog4eq]
    linarith
  have hε_half_lt : (ε : ℝ) < 1 / 2 := by rw [hεR]; norm_num
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := by
    rw [hεR, le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]; linarith
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := by
    rw [hεR, le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
  have hεQ1 : ε ≤ 1 / 2 := by rw [hεdef]; norm_num
  have hε2 : (ε : ℝ) ^ 2 < 1 / 2 := by rw [hεR]; norm_num
  -- ⟦THE `δ₀` FLOOR⟧ the binding arm at its worst case
  have hδ₀ge : (1 : ℝ) / 838400 ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    have hkey : (5 : ℝ) / 2096 ≤ cD3 / (16 * C) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
    rw [hεR]; linarith
  obtain ⟨K, hK, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded ε hεQpos hε2
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
  refine ⟨ε, K, cD3 / (16 * C) * (ε : ℝ) / 4, A, β,
    max (flatDesignFloor A) (max F (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), Hopq, hεQpos, hK,
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
  have hepsc : (Rf.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
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
  exact spine_False_core_xi_sq_flat Rf.toChowlaRegime hdoor cE hcE H₀red hred cD3 hcD3
    H₀D3 hD3 C hC hcm H hlo hhi hH₀ hepsc t g
    ((H : ℝ) / (Rf.A * Real.log H)) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail

end Salt.Entropy.Chowla

