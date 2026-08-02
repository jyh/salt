/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16FlatFinal

/-!
# `S16Uniform` — ⟦THE A-UNIFORM TWIN CHAIN⟧ and ⟦THE INEFFECTIVE LIMIT⟧

⟦THE DISCHARGE WAVE, ROUTE 6 GENERALISED⟧  The landed flat terminal
`S16FlatFinal.logChowla2_witnessed_scale_flat_L_v2` has the shape

```
∀ A₀ ≥ 162, ∃ (ε Cg Kc δ₀ Ct A β x₀ Hopq Mfl …), … ∧ (x₀ ≤ e^{e^{3.2A}/10} → Hopq ≤ …A… → …)
```

— every constant is chosen AFTER the caller's `A₀`.  That quantifier order is what blocks the
council's classical-limit argument: "the windows grow without bound in `A`, so they eventually
hold" is only a sentence about constants that do NOT move when `A` moves.  Nothing in the
statement says `x₀` and `Hopq` are `A₀`-free, and no consumer can recover it: `Classical.choose`
of the terminal at two different `A₀` are choices from two DIFFERENT propositions.

⟦THE FINDING⟧ at the bytes the constants ARE `A₀`-free.  In the flat head
(`HloExportFlat.log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat`) the caller's `A₀`
enters at exactly ONE line — `A := max A₀ (budgetAFlat ε β)` — and every constant
(`ε`, `K = Kc`, `δ₀`, `β`, `Hopq = max (max H₀red H₀D3) H₀xi`) is minted strictly BEFORE it.
`x₀` and `Cband` come from `hband`, which has no `A` at all; `Ct`, `Cq`, `cs`, `T₀`, `Kq`, `Ks`
and `Mfl` likewise.  So the whole flat road can be re-cut with the design constant HOISTED OUT
of the `∃`-prefix:

```
∃ (constants), … ∧ ∀ A, 162 ≤ A → budgetAFlat ε β ≤ A → ∃ Hcap, … (the same body)
```

§1–§7 walk the seven-link linear flat road, one additive twin per link, each twin's body the
landed one with `intro A hA hAge` moved to where the landed proof chose `A`:

* §1 `flat_head_uniform`         ← `HloExportFlat.…_hloCap_pinned_flat` (:227)
* §2 `flat_socket_uniform`       ← `HloExportMRFlatRoot.m4_exit_socket_split_sq_arc_flatRoot` (:70)
* §3 `flat_doorL2_uniform`       ← `S16FlatTerminalLinear.m4_doorL2_close_split_sq_…_L` (:179)
* §4 `flat_road_uniform`         ← `S16FlatTerminalLinear.m4_second_road_L2_gk_flatRoot_L` (:239)
* §5 `flat_capstone_uniform`     ← `S16FlatTerminalLinear.logChowla2_capstone_…_flatRoot_L` (:356)
* §6 `flat_conditional_uniform`  ← `S16FlatTerminalLinear.logChowla2_conditional_…_L` (:1033)
* §7 `logChowla2_witnessed_scale_flat_L_v2_uniform` ← `S16FlatFinal.…_v2` (:125)

§8 is the point: `logChowla2_ineffective` — the terminal with the TWO SIEGEL RIDERS GONE.  With
`x₀` and `Hopq` fixed, `A` is chosen above them and both windows close by
`Real.add_one_le_exp`, twice.  What survives is `hband`, the four numeric constant riders, the
two socket ceilings and the two carried predicates — no Siegel item of any kind.

**PURELY ADDITIVE.**  No landed declaration is touched.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.Entropy.Chowla

/-! ## §0 — THE THREE `private` HELPERS, RE-STATED

The corpus's own precedent (`SpineFinal.spine_False_core_xi_sq` →
`HloExport.spine_False_core_xi_sq_cap` → `HloExportFlat.spine_False_core_xi_sq_flat`): a
`private` declaration cannot be cited across files, so the in-file VERBATIM transcription is
the sanctioned device.  Both bodies below are byte-for-byte the flat file's. -/

/-- `HloExportMRFlatRoot`'s private `flatRootCap_arc`, re-stated. -/
private lemma uniformCap_arc (d p b c h : ℕ) :
    max (max d (max (max p b) c)) h ≤ max d (max (max (max p h) b) c) := by
  omega

/-- `HloExportFlat`'s private `flatCap_shuffle`, re-stated. -/
private lemma uniformCap_shuffle (a b c d e : ℕ) :
    max a (max (max b (max d e)) c) ≤ max (max a (max b c)) (max d e) := by
  omega

/-- **The `L²` spine contradiction core** (`spine_False_core_xi_sq_uniform`) —
`HloExportFlat.spine_False_core_xi_sq_flat` (`private`, hence uncitable) VERBATIM, statement
and proof, under a fresh name.  The core takes `κ` as an EXPLICIT ARGUMENT and reads nothing
about the design constant, which is why the `A`-hoist costs it nothing. -/
private theorem spine_False_core_xi_sq_uniform (R : ChowlaRegime) {ρ : ℝ}
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

end Salt.Entropy.Chowla

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE FLAT HEAD, WITH THE DESIGN CONSTANT HOISTED -/

/-- **⟦THE `A`-UNIFORM FLAT HEAD⟧** (`flat_head_uniform`) —
`HloExportFlat.log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat` with the caller's `A₀`
REPLACED by a `∀ A` inside the `∃`-prefix.  The body is the landed one verbatim; the only edit
is that the landed line `A := max A₀ (budgetAFlat ε β)` becomes `intro A hA26 hAge`, which is
legal precisely because every `obtain` above that line is `A`-free. -/
theorem flat_head_uniform :
    ∃ (ε : ℚ) (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 26 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
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
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = cD3 * (ε : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hcD3 hεR0) (by positivity)
  -- ⟦THE HEAD'S OWN FOUR-ARM FLOOR⟧ (flat) — `A`-FREE, which is the whole point
  obtain ⟨Hopq, hOpqdef⟩ : ∃ n : ℕ, n = max (max H₀red H₀D3) H₀xi := ⟨_, rfl⟩
  refine ⟨ε, K, cD3 / (16 * C) * (ε : ℝ) / 4, β, Hopq, hεQpos, hK,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num),
    hεdef.ge, hδ₀ge, hβpos, ?_⟩
  -- ⟦THE HOIST⟧ the landed proof chose `A := max A₀ (budgetAFlat ε β)` HERE
  intro A hA26 hAge
  obtain ⟨F, hFdef⟩ : ∃ n : ℕ, n = max Hopq (budgetFloorFlat (ε : ℝ) β A) := ⟨_, rfl⟩
  refine ⟨max (flatDesignFloor A) (max F (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), by rw [hFdef], ?_⟩
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
    exact uniformCap_shuffle _ _ _ _ _
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
  exact spine_False_core_xi_sq_uniform Rf.toChowlaRegime hdoor cE hcE H₀red hred cD3 hcD3
    H₀D3 hD3 C hC hcm H hlo hhi hH₀ hepsc t g
    ((H : ℝ) / (Rf.A * Real.log H)) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail

/-! ## §2 — THE ROAD-FORM SOCKET, UNIFORM -/

/-- **⟦THE `A`-UNIFORM SPLIT SOCKET⟧** (`flat_socket_uniform`) —
`HloExportMRFlatRoot.m4_exit_socket_split_sq_arc_flatRoot` on §1.  Body verbatim; `Hopq` gains
M4-0's arc floor `H₀` (still `A`-free) and `Hcap` gains it inside the `∀ A`. -/
theorem flat_socket_uniform :
    ∃ (ε : ℚ) (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              (∀ (a e : ℕ → ℂ) (Bsieve : ℕ → ℝ) (Binsert : ℝ),
                (∀ m, lamCoeff m = a m + e m) →
                (∀ H : ℕ, 0 ≤ Bsieve H) →
                (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
                  NearRatTight (arcDen 12 H) H α →
                    (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                      ≤ Bsieve H * (H : ℝ) ^ 2) →
                (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
                  (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
                    ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                      ∂(logMeasure R.x R.ω)) ≤ Binsert) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  K * (2 * Bsieve H) + 2 * Binsert ≤ δ₀) →
                ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨ε, K, δ₀, β, Hopq, hε, hK, hδ₀, hεpin, hδpin, hβ, hhead⟩ := flat_head_uniform
  obtain ⟨H₀, hH₀⟩ := sum_bigXi_norm_windowExpSum_sq_le_twelve ε hε
  refine ⟨ε, K, δ₀, β, max Hopq H₀, hε, hK, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro A hA162 hAge
  obtain ⟨Hcap, hCapEq, hhd⟩ := hhead A (by linarith) hAge
  refine ⟨max Hcap H₀, by rw [hCapEq]; exact uniformCap_arc _ _ _ _ _, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, _, hRU1, hRg, hcount, hRtow, hRcap, hR⟩ := hhd 0 (max U1floor H₀) g
  have hU1 : U1floor ≤ R.Hlo := le_trans (le_max_left _ _) hRU1
  have harc : H₀ ≤ R.Hlo := le_trans (le_max_right _ _) hRU1
  refine ⟨R, hReps, hU1, hRg, hRtow, le_trans hRcap (by omega), ?_⟩
  intro a e Bsieve Binsert hsplit hB0 hsock hins hρ
  refine hR δ₀ hδ₀ le_rfl ?_
  intro H _ hlo hhi
  exact le_trans (hH₀ R hReps harc a e Bsieve K Binsert hsplit hB0 hsock hcount hins
    H hlo hhi) (hρ H hlo hhi)

/-! ## §3 — THE CLOSED LOOP AT THE LINEAR LADDER, UNIFORM -/

/-- **⟦THE `A`-UNIFORM CLOSED LOOP⟧** (`flat_doorL2_uniform`) —
`S16FlatTerminalLinear.m4_doorL2_close_split_sq_gk_flatRoot_L` on §2.  `A` rides the prefix in
the landed proof and is never read by the door body, so the hoist is a pure re-bracketing. -/
theorem flat_doorL2_uniform (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
                M4DoorGates_L_gk K Cg R M k δ →
                (∀ H : ℕ, 0 ≤ Braw H) →
                M4SievedDoorSq_L_gk K R M Braw →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                  ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  obtain ⟨ε, Kb, δ₀, β, Hopq, hε, hKb, hδ₀, hεpin, hδpin, hβ, hsk⟩ := flat_socket_uniform
  refine ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro A hA162 hAge
  obtain ⟨Hcap, hCapLe, hexit⟩ := hsk A hA162 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hexit U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  have hA : 1 ≤ AdoorL M := one_le_AdoorL hgates.hM
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
    intro H hhi
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  refine hR (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2
      liouvilleC)
    (fun m => lamCoeff m - memSCoeff (calP (AdoorL M) (s13GK K M))
      (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC m)
    Braw (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) (fun m => by ring) hBraw0
    (hsock m4_bandTransport) ?_ ?_
  · intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (AdoorL M) (s13GK K M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · intro H hlo hhi
    rw [l2_budget_line Kb (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * Kb * Braw H ≤ 2 * Kb * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

/-! ## §4 — THE FLAT ROAD'S TERMINAL REGISTER, UNIFORM -/

/-- **⟦THE `A`-UNIFORM TERMINAL REGISTER⟧** (`flat_road_uniform`) —
`S16FlatTerminalLinear.m4_second_road_L2_gk_flatRoot_L` on §3, body verbatim. -/
theorem flat_road_uniform (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
                M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
                (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
                (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                    ≤ Braw H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                M4ChiSummedFreeRow_L_gk K R M RS →
                  ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, hβ, hdoor⟩ :=
    flat_doorL2_uniform K
  refine ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro A hA162 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hdoor A hA162 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  have harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    nlinarith [h1, harc1]
  have harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 2 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    nlinarith [h1, harc1]
  have hchi : M4ChiSummedBlockMeanSqN_L_gk K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied_L_gk K j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummed_L_gk K (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  have hcov := m4_cover_assembly_blk2_L_gk K hgates hBblk0 hblk2
  refine hR Braw Bceil δ M k hgates hBraw0 ?_ hceil hbudget
  refine m4_sievedDoorSq_of_blk2_L_gk K (ℓ := blockLen)
    (fun H => by have := hBblk0 H; positivity)
    (fun H q _ _ _ _ => one_le_blockLen H q) ?_ ?_ ?_ ?_ hcov
  · intro H q hlo hhi _ _
    have h1 := harc H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hH1 : 1 ≤ H := by
      have : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
      exact_mod_cast this
    exact blockLen_le H q hH1
  · intro H q hlo hhi _ _
    exact blockLen_narrow (R := R) hlo (harc H hlo hhi)
  · intro H q hlo hhi hq _
    exact blockLen_drift (R := R) hlo hq (harc H hlo hhi)
  · intro H hlo hhi
    have h := hdrift H hlo hhi
    have hres0 : (0 : ℝ) ≤ strataResidual H :=
      strataResidual_nonneg (one_le_arcDen_of_regime (R := R) hlo)
    have hB := hBcl0 H
    nlinarith [h]

/-! ## §5 — THE CAPSTONE AT THE FLAT ROOT AND THE LINEAR LADDER, UNIFORM -/

set_option maxHeartbeats 1600000 in
-- Same cause as the landed HOP 3: the ~120-line residue re-elaborates against the re-cut
-- prefix, which here loses `A`/`Hcap` from the `∃` and gains the `∀ A` binder.
/-- **⟦THE `A`-UNIFORM CAPSTONE⟧** (`flat_capstone_uniform`) —
`S16FlatTerminalLinear.logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_L` on §4.
`Ct` (the constant-pool fuse), `Cq`/`cs`/`T₀`/`Kq`/`Ks` (the cap-wire fuse), and `x₀`/`Cband`
(and hence `Mfl`) are all minted from `A`-FREE suppliers, so all of them hoist out with the
road's own constants.  Body verbatim. -/
theorem flat_capstone_uniform (K : ℕ) (hK : K ≤ 170000000)
    (hband : S16BandLaneCBoundedL K) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (M : ℕ), Mfl ≤ M →
                  ∃ C' : ℝ, 0 < C' ∧
                    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                        ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                    ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                      -- ⟦A⟧ THE SPINE ARITHMETIC
                      M4DoorGates_L_gk K Cg R M k δ₀ →
                      8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                          (fun H => 2 * rStrWitness H) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                          (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                          5 ≤ Real.log (Real.log (2 * T)) →
                          (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                            ≤ 8 * (0 : ℝ) ^ 2
                              + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                    \ seamBall (((A + s : ℕ)) : ℝ) 0)
                                  ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                      (calP (AdoorL M) (s13GK K M))
                                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                      (mrAlpha (1 / 12)) 2,
                                  ‖spoly (2 * (A + s))
                                    (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                              + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                                  * (Real.log (((A + s : ℕ)) : ℝ))
                                      ^ (-theta293 + epsrf (A + s)))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hδ₀, hεpin, hδpin, hβ, hroadU⟩ :=
    flat_road_uniform K
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_L_gk K hK
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cband, hCband0, hCband40, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, s11_grade_floor_hoistCb_prod_le Cband hCband0 hCband40, hβ, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hroad⟩ := hroadU A hA26 hAge
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hMfloor
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_L_gk K R M
      (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho_L M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
    have hKcpos : (0 : ℝ) < 16 * Kc := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

/-! ## §6 — THE FLAT CONDITIONAL AT THE LINEAR LADDER, UNIFORM -/

set_option maxHeartbeats 1000000 in
-- Same cause as the landed HOP 4: the residue re-elaborates against the prefix.
/-- **⟦THE `A`-UNIFORM CONDITIONAL⟧** (`flat_conditional_uniform`) —
`S16FlatTerminalLinear.logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_L` on §5.
Body verbatim. -/
theorem flat_conditional_uniform (K : ℕ) (hK : K ≤ 170000000)
    (hband : S16BandLaneCBoundedL K) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ M : ℕ,
                S15Sel''_L_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                S15CrossingBound_L_gk K R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, β, x₀, Hopq, Mfl, hCg, hε, hKc,
    hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hMflb, hβ, hcapU⟩ :=
    flat_capstone_uniform K hK hband
  refine ⟨ε, Cg, Kc, δ₀, Ct, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCgle, hεpin, hδpin, hMflb, hβ, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapU A hA26 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the LINEAR anchor
  have harith := s15_doorArithFrameRho_L_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register⟧
  have hgate : S13BandGate'_L_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_L_gk K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_gen le_rfl (s13_g2_jfloor_of_MSelect'_L_gk K (by linarith) hS))
    (s13_gate8_L_gk le_rfl (s13_gate8_of_MSelect'_L_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_L_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket_L hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorL_gk K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hlam50 htow
        hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM (hgate.block H L q j A s hb)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_L_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith


/-! ## §7 — THE FLAT LINEAR TERMINAL `v2`, UNIFORM -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 1600000 in
-- Same cause as the landed §2 of `S16FlatFinal`: the long binder prefix re-elaborates beside
-- the crossing supply's six constants, now under the `∀ A` binder.
/-- **⟦THE FLAT LINEAR TERMINAL, `v2`, `A`-UNIFORM⟧**
(`logChowla2_witnessed_scale_flat_L_v2_uniform`) — `S16FlatFinal.logChowla2_witnessed_scale_
flat_L_v2` with the design constant `A` HOISTED OUT of the `∃`-prefix.

⟦WHAT CHANGES⟧ nothing in the hypothesis list, nothing in the conclusion: the surviving riders
are the SAME eight (`Kc ≤ 2^539`, `Ct ≤ 2^23`, the `x₀` window, the `Hopq` arm census, and the
fuse's four numerals) and the same two carried predicates.  What changes is the QUANTIFIER
ORDER: `ε`, `Cg`, `Kc`, `δ₀`, `Ct`, `β`, `x₀`, `Hopq`, `Mfl`, `Cq`, `cs`, `T₀`, `Kq`, `Ks`, `C`
are now chosen ONCE, and `A` ranges over every admissible design constant afterwards.  That is
exactly what the classical-limit argument of §8 needs and what the landed `v2` cannot supply.

⟦THE ADMISSIBILITY CONDITION⟧ the landed terminal hid `budgetAFlat ε β ≤ A` inside its own
choice of `A`; here it is a hypothesis of the `∀`, discharged by any caller who takes
`A ≥ budgetAFlat ε β` — and `budgetAFlat ε β` is now a NAMEABLE real, since `ε` and `β` are
bound outside. -/
theorem logChowla2_witnessed_scale_flat_L_v2_uniform
    (hband : S16BandLaneCBoundedL 32000000) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        (Kc ≤ 2 ^ 539 → Ct ≤ 2 ^ 23 →
          (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          Real.exp (-100) ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
          Real.exp (-100) ≤ Ks →
          ∀ g : ℕ → ℕ → ℕ, ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            (S16CofactorSupply_L_gk 32000000 Cq R (flatDoorM A) →
              S16BaseScaleCap96_L_gk 32000000 R (flatDoorM A) →
                ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hcond⟩ :=
    flat_conditional_uniform 32000000 (by norm_num) hband
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40, hsupply⟩ :=
    s15_crossing_supplied_L_gk 32000000
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond (max 162 (budgetAFlat (ε : ℝ) β)) (le_max_left _ _) (le_max_right _ _)
  obtain ⟨R0, hR0eps, -, -, -, -⟩ :=
    hbody0 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have hεR : (1 : ℝ) / 500 ≤ (ε : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hεpin
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
    exact h
  refine ⟨ε, Cg, Kc, δ₀, Ct, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb, hβ, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge
  refine ⟨fun hopq => flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hKb hCtb hx0win hopq hcs hT₀ hKq hKs g
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  -- ⟦THE REGISTER, SUPPLIED⟧ at the flat design modulus
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have hKle : (32000000 : ℕ) ≤ 170000000 * flatDoorM A := by
    calc (32000000 : ℕ) ≤ 170000000 * 1 := by norm_num
      _ ≤ 170000000 * flatDoorM A := Nat.mul_le_mul_left _ hM1
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by
    rw [hReps]
    have : (1 : ℚ) / 2 ^ 9 ≤ 1 / 500 := by norm_num
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  have hsel := s15_sel''_L_gk_witness_flat_bumped hA26 32000000 hKle hδ₀ hδpin hKc hKb
    hCt hCtb hCgle hMflb hx0win heps hlo hwin
  -- ⟦THE CROSSING, SUPPLIED⟧ the block floor off the register's own `blk` line
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk 32000000 (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk 32000000 (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel
    (hsupply hcs hT₀ hKq hKs R (flatDoorM A) hM1 hfl hblk hcof hcapsc)


/-! ## §8 — ⟦THE INEFFECTIVE LIMIT⟧ THE TWO SIEGEL RIDERS, DISSOLVED -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 800000 in
-- the hoisted prefix plus the two window discharges re-elaborate the terminal's conclusion
/-- **⟦THE INEFFECTIVE LIMIT⟧** (`logChowla2_ineffective`) — the campaign's ORIGINAL target,
recovered: a Chowla regime at arbitrary depth with **NO SIEGEL HYPOTHESIS OF ANY KIND**.

⟦WHAT IS GONE, AND WHY⟧ the landed terminal carries two riders that no proof on this road can
discharge, both Siegel-ineffective:

* `(x₀ : ℝ) ≤ e^{e^{3.2A}/10}` — ⟦THE `x0` WINDOW⟧, a ceiling on the band lane's opaque
  Siegel threshold;
* `Hopq ≤ flatDesignBase A` — ⟦THE ARM CENSUS⟧, a ceiling on the road's opaque floor arm,
  whose `H₀red`/`H₀D3` ride the Siegel-ineffective `K_Chen`.

Neither is a statement about a MOVING quantity: `x₀` and `Hopq` are FIXED naturals, minted by
suppliers that never see the design constant (§1–§7 is precisely the proof of that).  Both
windows, on the other hand, grow without bound in `A` — `e^{e^{3.2A}}` is a double exponential.
So there is an `A` above both, and at that `A` the riders are THEOREMS, not hypotheses.  The
arithmetic is two applications of `Real.add_one_le_exp`: `A ≥ 4x₀` closes the first,
`A ≥ Hopq` the second.

⟦WHAT THIS COSTS⟧ effectivity, and only effectivity.  `A` is produced by
`Classical.choice`-bound constants, so no numeral for the witnessed scale can be read off —
exactly the price the whole analytic literature pays for Siegel's theorem.  In exchange the
STATEMENT is unconditional in the Siegel direction: the caller supplies no threshold, no arm
ceiling, no `x₀`.

⟦THE SURVIVING LIST, EXACT AND COMPLETE⟧ outer: `hband : S16BandLaneCBoundedL 32000000` (the
band-lane constant, ⟦C_mu⟧, ours to close, not the field's).  Inner: `Kc ≤ 2^539` and
`Ct ≤ 2^23` (the two socket ceilings — TRUE at the chains' closed forms `12·10^161` and
`6·e^14`, unread from the `∃`-witnesses); `e^{-100} ≤ cs`, `T₀ ≤ e^{e^100}`, `Kq ≤ e^100`,
`e^{-100} ≤ Ks` (the fuse's four numerals, spent on constants THIS THEOREM PRODUCES).
Conclusion-side: the two carried predicates `S16CofactorSupply_L_gk` and
`S16BaseScaleCap96_L_gk`.  **No `x₀`.  No `Hopq`.  No Siegel.**

⟦THE DEPTH⟧ `A₀` is the caller's: for EVERY `A₀` the theorem returns a regime whose window
base is `⌈e^{e^{3.2A}}⌉₊` with `A ≥ A₀`.  The regime is therefore arbitrarily deep, and
`R.Hlo` is pinned — exported as an EQUATION, not a bound.

⟦THE NAMING⟧ `_ineffective` names the price (the `A` is not computable), not a weakness of the
conclusion; the Captain's to rename. -/
theorem logChowla2_ineffective (hband : S16BandLaneCBoundedL 32000000) (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      (Kc ≤ 2 ^ 539 → Ct ≤ 2 ^ 23 →
        Real.exp (-100) ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (S16CofactorSupply_L_gk 32000000 Cq R (flatDoorM A) →
            S16BaseScaleCap96_L_gk 32000000 R (flatDoorM A) →
              ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb, hβ, hmain⟩ :=
    logChowla2_witnessed_scale_flat_L_v2_uniform hband
  -- ⟦THE CLASSICAL LIMIT⟧ the design constant, chosen ABOVE the two fixed Siegel constants
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (max A₀ 162)
      (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))) := ⟨_, rfl⟩
  have hA162 : (162 : ℝ) ≤ A := by
    rw [hAdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hA₀A : A₀ ≤ A := by
    rw [hAdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    rw [hAdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  -- ⟦RIDER 3, DISCHARGED⟧ the `x₀` window: `e^{e^{3.2A}/10} ≥ e^{3.2A}/10 + 1 ≥ 1.28·x₀`
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
    have h2 : Real.exp (3.2 * A) / 10 + 1 ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
      Real.add_one_le_exp _
    linarith
  -- ⟦RIDER 4, DISCHARGED⟧ the arm census: `⌈e^{e^{3.2A}}⌉₊ ≥ e^{3.2A} + 1 ≥ A ≥ Hopq`
  have hopq : Hopq ≤ flatDesignBase A := by
    have h2 : Real.exp (3.2 * A) + 1 ≤ Real.exp (Real.exp (3.2 * A)) := Real.add_one_le_exp _
    have hR : ((Hopq : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by linarith
    have hceil := le_trans hR (Nat.le_ceil (Real.exp (Real.exp (3.2 * A))))
    rw [flatDesignBase]; exact_mod_cast hceil
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAge
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb, hβ, hA162, hA₀A, ?_⟩
  intro hKb hCtb hcs hT₀ hKq hKs g
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hKb hCtb hx0win hopq hcs hT₀ hKq hKs g
  exact ⟨R, hReps, by rw [hHlo]; exact hbase hopq, hRg, hRtow, hdes, hwin, hfire2⟩


/-! ## §9 — ⟦THE BAND WINDOW⟧ THE LAST RIDER, DISSOLVED

⟦BAND-WINDOW, 2026-08-02⟧  §8 left ONE outer hypothesis standing: `hband :
S16BandLaneCBoundedL 32000000`, whose only content beyond a LANDED theorem
(`S11HoistLinear.m4_hband_at_door_slot_split_graded_L_gk`, at `Aexp := s13Aexp`, on the
unconditional `PortClose.mmuChiRate_holds_gated`) is the conjunct `log Cband ≤ 40`.

CMU-HUNT walked every `∃`-hop that mints that constant and found it EFFECTIVE but far above
`40`: `Cband = 2·C_mu·4³ + 1` with `log C_mu ≈ 22 656`, dominated by `Vk/PowRegion`'s literal
double-exponential `T₀`.  So `40` is not a rider anyone can pay — but it is also not what the
consumer needs.  The `40` is spent at exactly ONE place: `S11HoistGrade.
s11_grade_floor_hoistCb_prod_le`, to put the graded twin's `Mfl` under the numeral pin `2^355`,
which `FlatFloorBump.flatDoorM_Mfl_bump` then charges against `flatDoorM A` at `A ≥ 162`.  And
`flatDoorM A = ⌊e^{1.6A}/310301⌋₊` grows without bound in a constant the terminal quantifies
SYMBOLICALLY.

⟦THE WINDOW⟧ `FlatFloorBump.flatDoorM_gradeFloor_win` prices the trade at the bytes:

> `162 ≤ A` and `log Cband ≤ 0.64·A − 20`  ⟹  `Mfl ≤ flatDoorM A`,

so the rider is not a NUMBER but a WINDOW, and the design constant chooses it.  §9 threads that
window through §5-§7's three twins (§9.1-§9.3) — the numeral conjunct `Mfl ≤ 2^355`
becomes the `A`-free Π-statement `∀ A ≥ max 162 Awin, Mfl ≤ flatDoorM A`, carried in the
same slot — and §9.0's `s16_bandLaneWinL_holds` DISCHARGES the rider outright: `C_mu` is a
FIXED real (no `A` occurs anywhere in its mint), so
`Awin := max 162 ((log Cband + 20)/0.64)` is a real number, and the classical limit of §8 —
one more term in the same `max` that already dissolved the two Siegel windows — closes it.

⟦WHAT `logChowla2_ineffective_v2` COSTS⟧ nothing that §8 did not already pay: the same
ineffectivity (`A` is `Classical.choice`-bound), the same six numeral riders inside, the same
two carried predicates.  **No band rider.  No Siegel hypothesis.  No hypothesis at all except
the caller's depth `A₀`.**

**PURELY ADDITIVE.**  §5–§8 are untouched; §9 is their windowed transcription. -/

/-! ### §9.0 — THE WINDOWED RIDER, AND ITS DISCHARGE -/

/-- **⟦THE BAND-LANE RIDER, WINDOWED⟧** (`S16BandLaneCBoundedL_win`) —
`S16FlatTerminalLinear.S16BandLaneCBoundedL` with the numeral tolerance `log Cband ≤ 40`
replaced by the design constant's own window `log Cband ≤ 0.64·Awin − 20`.  Everything else is
byte-identical, and everything else is a LANDED THEOREM at this very witness. -/
def S16BandLaneCBoundedL_win (Awin : ℝ) (K : ℕ) : Prop :=
  ∃ (x₀ : ℕ) (Cband : ℝ), 0 < Cband ∧ Real.log Cband ≤ 0.64 * Awin - 20 ∧ ∀ (M : ℕ), 1 ≤ M →
    ∃ C' : ℝ, 0 < C' ∧
      C' ≤ (Cband * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1)
          * (M : ℝ) ^ (2.1 : ℝ) ∧
      ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
        ((∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
            DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
          ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
            ∀ χ : DirichletCharacter ℂ q,
              (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                ≤ t0BandB (((A + s : ℕ)) : ℝ)
                    (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))

/-- **⟦THE LANDED RIDER IS THE WINDOW AT `A = 93.75`⟧** (`s16_bandLaneWinL_of_bandL`) — the
corpus's `log Cband ≤ 40` is exactly the window at `Awin = 93.75` (`0.64·93.75 − 20 = 40`), so
every consumer of the windowed rider accepts the landed one at any `Awin ≥ 93.75`.  The two
statements are therefore comparable, and the windowed chain is a strict generalisation. -/
theorem s16_bandLaneWinL_of_bandL (K : ℕ) {Awin : ℝ} (hAwin : 93.75 ≤ Awin)
    (hband : S16BandLaneCBoundedL K) : S16BandLaneCBoundedL_win Awin K := by
  obtain ⟨x₀, Cband, hCband0, hCband40, hbody⟩ := hband
  exact ⟨x₀, Cband, hCband0, by linarith, hbody⟩

/-- **⟦THE WINDOWED RIDER IS A THEOREM⟧** (`s16_bandLaneWinL_holds`) — ⟦THE PRIZE⟧.

`S11HoistLinear.m4_hband_at_door_slot_split_graded_L_gk` at `Aexp := s13Aexp`, on
`PortClose.mmuChiRate_holds_gated` (LANDED, unconditional), hands out `∃ x₀ Cb, 0 < Cb ∧ …`
with the band body VERBATIM and NO ceiling on `Cb`.  The rider's shape asks for the constant in
the form `Cband·4^{Aexp}·(e^{52.5}·4^{1.05}) + 1`; dividing gives `Cband := Cb/E`, and the `+1`
is pure slack.  The window is then satisfied BY CONSTRUCTION at
`Awin := max 162 ((log Cband + 20)/0.64)` — a real number, because `C_mu` carries no `A`
(CMU-HUNT §1: every leaf of both rows is a closed form in the corpus's own literals).

⟦WHAT IS INEFFECTIVE HERE⟧ nothing that was not already: `Cb` is a `Classical.choose`, so
`Awin` is not a numeral — exactly the price §8 pays for `x₀` and `Hopq`. -/
theorem s16_bandLaneWinL_holds (K : ℕ) :
    ∃ Awin : ℝ, 162 ≤ Awin ∧ S16BandLaneCBoundedL_win Awin K := by
  obtain ⟨x₀, Cb, hCb0, hsplit⟩ :=
    m4_hband_at_door_slot_split_graded_L_gk K mmuChiRate_holds_gated s13Aexp
      (by rw [s13Aexp]; norm_num)
  set E : ℝ := (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) with hEdef
  have hE0 : (0 : ℝ) < E := by
    rw [hEdef]
    have h4 : (0 : ℝ) < (4 : ℝ) ^ (s13Aexp) := Real.rpow_pos_of_pos (by norm_num) _
    have h1 : (0 : ℝ) < (4 : ℝ) ^ (1.05 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set Cband : ℝ := Cb / E with hCbanddef
  have hCband0 : (0 : ℝ) < Cband := div_pos hCb0 hE0
  refine ⟨max 162 ((Real.log Cband + 20) / 0.64), le_max_left _ _,
    x₀, Cband, hCband0, ?_, ?_⟩
  · -- ⟦THE WINDOW, BY CONSTRUCTION⟧
    have h := le_max_right (162 : ℝ) ((Real.log Cband + 20) / 0.64)
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.64)] at h
    linarith
  · intro M hM
    obtain ⟨C', hC'0, hC'le, hbody⟩ := hsplit M hM
    refine ⟨C', hC'0, ?_, hbody⟩
    have hid : Cband * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) = Cb := by
      rw [hCbanddef, hEdef]; field_simp
    have hMpow : (0 : ℝ) ≤ (M : ℝ) ^ (2.1 : ℝ) :=
      Real.rpow_nonneg (Nat.cast_nonneg M) _
    rw [hid]
    nlinarith [hC'le, hMpow]


/-! ### §9.1 — THE CAPSTONE, WINDOWED -/

set_option maxHeartbeats 1600000 in
-- Same cause as §5: the ~120-line residue re-elaborates against the re-cut prefix, whose
-- numeral `Mfl` conjunct is now the window's Π-statement.
/-- **⟦THE `A`-UNIFORM CAPSTONE, WINDOWED⟧** (`flat_capstone_uniform_win`) — §5 on the windowed
rider.  The ONE change: the prefix conjunct `Mfl ≤ 2^355` — the image of `log Cband ≤ 40` under
`s11_grade_floor_hoistCb_prod_le` — becomes `∀ A ≥ max 162 Awin, Mfl ≤ flatDoorM A`, the image
of the window under `FlatFloorBump.flatDoorM_gradeFloor_win`.  Body verbatim. -/
theorem flat_capstone_uniform_win (K : ℕ) (hK : K ≤ 170000000) (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_win Awin K) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (M : ℕ), Mfl ≤ M →
                  ∃ C' : ℝ, 0 < C' ∧
                    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                        ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                    ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                      -- ⟦A⟧ THE SPINE ARITHMETIC
                      M4DoorGates_L_gk K Cg R M k δ₀ →
                      8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                          (fun H => 2 * rStrWitness H) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                          (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                          5 ≤ Real.log (Real.log (2 * T)) →
                          (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                            ≤ 8 * (0 : ℝ) ^ 2
                              + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                    \ seamBall (((A + s : ℕ)) : ℝ) 0)
                                  ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                      (calP (AdoorL M) (s13GK K M))
                                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                      (mrAlpha (1 / 12)) 2,
                                  ‖spoly (2 * (A + s))
                                    (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                              + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                                  * (Real.log (((A + s : ℕ)) : ℝ))
                                      ^ (-theta293 + epsrf (A + s)))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hδ₀, hεpin, hδpin, hβ, hroadU⟩ :=
    flat_road_uniform K
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_L_gk K hK
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin,
    (fun A hA162 hAw => flatDoorM_gradeFloor_win hA162 hCband0 (by linarith)),
    hβ, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hroad⟩ := hroadU A hA26 hAge
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hMfloor
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_L_gk K R M
      (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho_L M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
    have hKcpos : (0 : ℝ) < 16 * Kc := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]
/-! ### §9.2 — THE CONDITIONAL, WINDOWED -/

set_option maxHeartbeats 1000000 in
-- Same cause as §6: the residue re-elaborates against the prefix.
/-- **⟦THE `A`-UNIFORM CONDITIONAL, WINDOWED⟧** (`flat_conditional_uniform_win`) — §6 on §9.1.
The window's Π-statement rides the same slot the numeral pin rode.  Body verbatim. -/
theorem flat_conditional_uniform_win (K : ℕ) (hK : K ≤ 170000000) (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_win Awin K) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ M : ℕ,
                S15Sel''_L_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                S15CrossingBound_L_gk K R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, β, x₀, Hopq, Mfl, hCg, hε, hKc,
    hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hMflb, hβ, hcapU⟩ :=
    flat_capstone_uniform_win K hK Awin hband
  refine ⟨ε, Cg, Kc, δ₀, Ct, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCgle, hεpin, hδpin, hMflb, hβ, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapU A hA26 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the LINEAR anchor
  have harith := s15_doorArithFrameRho_L_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register⟧
  have hgate : S13BandGate'_L_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_L_gk K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_gen le_rfl (s13_g2_jfloor_of_MSelect'_L_gk K (by linarith) hS))
    (s13_gate8_L_gk le_rfl (s13_gate8_of_MSelect'_L_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_L_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket_L hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorL_gk K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hlam50 htow
        hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM (hgate.block H L q j A s hb)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_L_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith

/-! ### §9.3 — THE FLAT LINEAR TERMINAL `v2`, WINDOWED -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 1600000 in
-- Same cause as §7: the long binder prefix re-elaborates beside the crossing supply's six
-- constants, now under the `∀ A` binder with the window's admissibility line added.
/-- **⟦THE FLAT LINEAR TERMINAL, `v2`, `A`-UNIFORM, WINDOWED⟧**
(`logChowla2_witnessed_scale_flat_L_v2_uniform_win`) — §7 on §9.2.  TWO changes: the prefix
carries the window's Π-statement in the numeral pin's slot, and the `∀ A` binder gains the
admissibility line `Awin ≤ A` (the window is monotone in `A`, so any caller deep enough for the
band constant is deep enough).  The `Mfl` floor is then spent through
`FlatFloorBump.s15_sel''_L_gk_witness_flat_bumped_win` — at the door modulus directly, never at
`2^355`.  Body verbatim. -/
theorem logChowla2_witnessed_scale_flat_L_v2_uniform_win (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_win Awin 32000000) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        (Kc ≤ 2 ^ 539 → Ct ≤ 2 ^ 23 →
          (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          Real.exp (-100) ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
          Real.exp (-100) ≤ Ks →
          ∀ g : ℕ → ℕ → ℕ, ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            (S16CofactorSupply_L_gk 32000000 Cq R (flatDoorM A) →
              S16BaseScaleCap96_L_gk 32000000 R (flatDoorM A) →
                ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hcond⟩ :=
    flat_conditional_uniform_win 32000000 (by norm_num) Awin hband
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40, hsupply⟩ :=
    s15_crossing_supplied_L_gk 32000000
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond (max 162 (budgetAFlat (ε : ℝ) β)) (le_max_left _ _) (le_max_right _ _)
  obtain ⟨R0, hR0eps, -, -, -, -⟩ :=
    hbody0 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have hεR : (1 : ℝ) / 500 ≤ (ε : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hεpin
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
    exact h
  refine ⟨ε, Cg, Kc, δ₀, Ct, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb, hβ, ?_⟩
  intro A hA26 hAwin hAge
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge
  refine ⟨fun hopq => flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hKb hCtb hx0win hopq hcs hT₀ hKq hKs g
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  -- ⟦THE REGISTER, SUPPLIED⟧ at the flat design modulus
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have hKle : (32000000 : ℕ) ≤ 170000000 * flatDoorM A := by
    calc (32000000 : ℕ) ≤ 170000000 * 1 := by norm_num
      _ ≤ 170000000 * flatDoorM A := Nat.mul_le_mul_left _ hM1
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by
    rw [hReps]
    have : (1 : ℚ) / 2 ^ 9 ≤ 1 / 500 := by norm_num
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win hA26 32000000 hKle hδ₀ hδpin hKc hKb
    hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win heps hlo hwin
  -- ⟦THE CROSSING, SUPPLIED⟧ the block floor off the register's own `blk` line
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk 32000000 (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk 32000000 (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel
    (hsupply hcs hT₀ hKq hKs R (flatDoorM A) hM1 hfl hblk hcof hcapsc)


/-! ### §9.4 — ⟦THE INEFFECTIVE LIMIT, `v2`⟧ THE LAST OUTER HYPOTHESIS, GONE -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 800000 in
-- Same cause as §8: the hoisted prefix plus the three window discharges re-elaborate the
-- terminal's conclusion.
/-- **⟦THE INEFFECTIVE LIMIT, WITHOUT THE BAND RIDER⟧** (`logChowla2_ineffective_v2`) — §8 with
its ONE outer hypothesis discharged.

⟦THE DEVICE⟧ identical to §8's, one term longer.  `Awin` (§9.0), `x₀` and `Hopq` are FIXED
reals/naturals minted by suppliers that never see the design constant; all three windows —
`log Cband ≤ 0.64·A − 20`, `x₀ ≤ e^{e^{3.2A}/10}`, `Hopq ≤ ⌈e^{e^{3.2A}}⌉₊` — grow without
bound in `A`; so `A` is chosen above all three at ONE `max` line and all three become theorems.

⟦THE SURVIVING LIST, EXACT AND COMPLETE⟧ **outer: NOTHING** (the caller supplies only the depth
`A₀`).  Inner: the six numeral riders `Kc ≤ 2^539`, `Ct ≤ 2^23`, `e^{-100} ≤ cs`,
`T₀ ≤ e^{e^{100}}`, `Kq ≤ e^{100}`, `e^{-100} ≤ Ks` — all six on constants THIS THEOREM
produces.  Conclusion-side: the two carried predicates `S16CofactorSupply_L_gk` and
`S16BaseScaleCap96_L_gk`.  **No band rider.  No `x₀`.  No `Hopq`.  No Siegel hypothesis.**

⟦WHAT IS EXPORTED IN PLACE OF THE PIN⟧ §8 exported the numeral conjunct `Mfl ≤ 2^355`; here
the same slot carries `Mfl ≤ flatDoorM A` — the statement the pin existed to produce, now at
the theorem's own design constant. -/
theorem logChowla2_ineffective_v2 (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      (Kc ≤ 2 ^ 539 → Ct ≤ 2 ^ 23 →
        Real.exp (-100) ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (S16CofactorSupply_L_gk 32000000 Cq R (flatDoorM A) →
            S16BaseScaleCap96_L_gk 32000000 R (flatDoorM A) →
              ¬ logChowla2Fails R.eps R.x R.ω)) := by
  -- ⟦RIDER 0, DISCHARGED⟧ the band lane's own constant, at its own window
  obtain ⟨Awin, -, hband⟩ := s16_bandLaneWinL_holds 32000000
  obtain ⟨ε, Cg, Kc, δ₀, Ct, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb, hβ, hmain⟩ :=
    logChowla2_witnessed_scale_flat_L_v2_uniform_win Awin hband
  -- ⟦THE CLASSICAL LIMIT⟧ the design constant, chosen ABOVE all three fixed constants
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (max (max A₀ 162) Awin)
      (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))) := ⟨_, rfl⟩
  have hA162 : (162 : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hA₀A : A₀ ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hAwinA : Awin ≤ A := by
    rw [hAdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    rw [hAdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  -- ⟦RIDER 3, DISCHARGED⟧ the `x₀` window
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
    have h2 : Real.exp (3.2 * A) / 10 + 1 ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
      Real.add_one_le_exp _
    linarith
  -- ⟦RIDER 4, DISCHARGED⟧ the arm census
  have hopq : Hopq ≤ flatDesignBase A := by
    have h2 : Real.exp (3.2 * A) + 1 ≤ Real.exp (Real.exp (3.2 * A)) := Real.add_one_le_exp _
    have hR : ((Hopq : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by linarith
    have hceil := le_trans hR (Nat.le_ceil (Real.exp (Real.exp (3.2 * A))))
    rw [flatDesignBase]; exact_mod_cast hceil
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A, ?_⟩
  intro hKb hCtb hcs hT₀ hKq hKs g
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hKb hCtb hx0win hopq hcs hT₀ hKq hKs g
  exact ⟨R, hReps, by rw [hHlo]; exact hbase hopq, hRg, hRtow, hdes, hwin, hfire2⟩

/-! ## §9u — ⟦THE WINDOWED RIDER, `K`-UNIFORM⟧ -/

/-- **⟦THE PRIZE, `K`-UNIFORM⟧** (`s16_bandLaneWinL_holds_uniform`) — ⟦CAP-RECUT P1⟧ the
`∀K ∃Awin` → `∃Awin ∀K` swap.  BAND-K-PROBE's finding: `Cband = Cb/E` is minted `K`-FREE and
`A`-FREE (the band lane reads `K` only through `s13GK`, and the LEVEL2-PROD per-block reprice of
7/31 removed the `2^{1.05K}` recoil from the mass witness), so the same `Awin ≈ 35439` serves
EVERY `K` — in particular the raised lever `KlevF A`.  Body verbatim off
`m4_hband_at_door_slot_split_graded_L_gk_uniform`; the per-`K` original is untouched. -/
theorem s16_bandLaneWinL_holds_uniform :
    ∃ Awin : ℝ, 162 ≤ Awin ∧ ∀ K : ℕ, S16BandLaneCBoundedL_win Awin K := by
  obtain ⟨x₀, Cb, hCb0, hsplit⟩ :=
    m4_hband_at_door_slot_split_graded_L_gk_uniform mmuChiRate_holds_gated s13Aexp
      (by rw [s13Aexp]; norm_num)
  set E : ℝ := (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) with hEdef
  have hE0 : (0 : ℝ) < E := by
    rw [hEdef]
    have h4 : (0 : ℝ) < (4 : ℝ) ^ (s13Aexp) := Real.rpow_pos_of_pos (by norm_num) _
    have h1 : (0 : ℝ) < (4 : ℝ) ^ (1.05 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set Cband : ℝ := Cb / E with hCbanddef
  have hCband0 : (0 : ℝ) < Cband := div_pos hCb0 hE0
  refine ⟨max 162 ((Real.log Cband + 20) / 0.64), le_max_left _ _, ?_⟩
  intro K
  refine ⟨x₀, Cband, hCband0, ?_, ?_⟩
  · -- ⟦THE WINDOW, BY CONSTRUCTION⟧
    have h := le_max_right (162 : ℝ) ((Real.log Cband + 20) / 0.64)
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.64)] at h
    linarith
  · intro M hM
    obtain ⟨C', hC'0, hC'le, hbody⟩ := hsplit K M hM
    refine ⟨C', hC'0, ?_, hbody⟩
    have hid : Cband * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) = Cb := by
      rw [hCbanddef, hEdef]; field_simp
    have hMpow : (0 : ℝ) ≤ (M : ℝ) ^ (2.1 : ℝ) :=
      Real.rpow_nonneg (Nat.cast_nonneg M) _
    rw [hid]
    nlinarith [hC'le, hMpow]

/-! ## §Xw — ⟦KWIDE-65⟧ THE WIDE-CEILING TWINS (this file)

Mechanical widening of the flat `hK` ceiling binders on the `L`-chain: the ceiling moves
INSIDE the internal `∀ M` as `≤ 170000000 * M`, so the raised lever `KlevF` can flow.
Statements and proofs are verbatim apart from that antecedent and the `_kwide` re-pointing.
The originals are untouched.
-/

/-- ⟦WIDE CEILING TWIN⟧ (`flat_capstone_uniform_kwide`) —
`flat_capstone_uniform`
with the flat ceiling moved inside the `∀ M` as `K ≤ 170000000 * M`.
Statement and proof otherwise verbatim, off the `_kwide` upstream. -/
theorem flat_capstone_uniform_kwide (K : ℕ)
    (hband : S16BandLaneCBoundedL K) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (M : ℕ), Mfl ≤ M → K ≤ 170000000 * M →
                  ∃ C' : ℝ, 0 < C' ∧
                    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                        ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                    ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                      -- ⟦A⟧ THE SPINE ARITHMETIC
                      M4DoorGates_L_gk K Cg R M k δ₀ →
                      8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                          (fun H => 2 * rStrWitness H) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                          (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                          5 ≤ Real.log (Real.log (2 * T)) →
                          (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                            ≤ 8 * (0 : ℝ) ^ 2
                              + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                    \ seamBall (((A + s : ℕ)) : ℝ) 0)
                                  ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                      (calP (AdoorL M) (s13GK K M))
                                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                      (mrAlpha (1 / 12)) 2,
                                  ‖spoly (2 * (A + s))
                                    (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                              + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                                  * (Real.log (((A + s : ℕ)) : ℝ))
                                      ^ (-theta293 + epsrf (A + s)))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hδ₀, hεpin, hδpin, hβ, hroadU⟩ :=
    flat_road_uniform K
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_L_gk_kwide K
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cband, hCband0, hCband40, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, s11_grade_floor_hoistCb_prod_le Cband hCband0 hCband40, hβ, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hroad⟩ := hroadU A hA26 hAge
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hMfloor hKw
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_L_gk K R M
      (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho_L M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
    have hKcpos : (0 : ℝ) < 16 * Kc := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

/-- ⟦WIDE CEILING TWIN⟧ (`flat_conditional_uniform_kwide`) —
`flat_conditional_uniform`
with the flat ceiling moved inside the `∀ M` as `K ≤ 170000000 * M`.
Statement and proof otherwise verbatim, off the `_kwide` upstream. -/
theorem flat_conditional_uniform_kwide (K : ℕ)
    (hband : S16BandLaneCBoundedL K) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ M : ℕ,
                S15Sel''_L_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                 K ≤ 170000000 * M →
                S15CrossingBound_L_gk K R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, β, x₀, Hopq, Mfl, hCg, hε, hKc,
    hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hMflb, hβ, hcapU⟩ :=
    flat_capstone_uniform_kwide K hband
  refine ⟨ε, Cg, Kc, δ₀, Ct, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCgle, hεpin, hδpin, hMflb, hβ, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapU A hA26 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hsel hKw
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor hKw
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the LINEAR anchor
  have harith := s15_doorArithFrameRho_L_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register⟧
  have hgate : S13BandGate'_L_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_L_gk K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_gen le_rfl (s13_g2_jfloor_of_MSelect'_L_gk K (by linarith) hS))
    (s13_gate8_L_gk le_rfl (s13_gate8_of_MSelect'_L_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_L_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket_L hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorL_gk K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hlam50 htow
        hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM (hgate.block H L q j A s hb)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_L_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith

/-- ⟦WIDE CEILING TWIN⟧ (`flat_capstone_uniform_win_kwide`) —
`flat_capstone_uniform_win`
with the flat ceiling moved inside the `∀ M` as `K ≤ 170000000 * M`.
Statement and proof otherwise verbatim, off the `_kwide` upstream. -/
theorem flat_capstone_uniform_win_kwide (K : ℕ) (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_win Awin K) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (M : ℕ), Mfl ≤ M → K ≤ 170000000 * M →
                  ∃ C' : ℝ, 0 < C' ∧
                    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                        ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                    ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                      -- ⟦A⟧ THE SPINE ARITHMETIC
                      M4DoorGates_L_gk K Cg R M k δ₀ →
                      8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                          (fun H => 2 * rStrWitness H) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                          (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                          5 ≤ Real.log (Real.log (2 * T)) →
                          (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                            ≤ 8 * (0 : ℝ) ^ 2
                              + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                    \ seamBall (((A + s : ℕ)) : ℝ) 0)
                                  ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                      (calP (AdoorL M) (s13GK K M))
                                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                      (mrAlpha (1 / 12)) 2,
                                  ‖spoly (2 * (A + s))
                                    (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                              + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                                  * (Real.log (((A + s : ℕ)) : ℝ))
                                      ^ (-theta293 + epsrf (A + s)))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hδ₀, hεpin, hδpin, hβ, hroadU⟩ :=
    flat_road_uniform K
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_L_gk_kwide K
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin,
    (fun A hA162 hAw => flatDoorM_gradeFloor_win hA162 hCband0 (by linarith)),
    hβ, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hroad⟩ := hroadU A hA26 hAge
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hMfloor hKw
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_L_gk K R M
      (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho_L M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
    have hKcpos : (0 : ℝ) < 16 * Kc := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

/-- ⟦WIDE CEILING TWIN⟧ (`flat_conditional_uniform_win_kwide`) —
`flat_conditional_uniform_win`
with the flat ceiling moved inside the `∀ M` as `K ≤ 170000000 * M`.
Statement and proof otherwise verbatim, off the `_kwide` upstream. -/
theorem flat_conditional_uniform_win_kwide (K : ℕ) (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_win Awin K) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ M : ℕ,
                S15Sel''_L_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                 K ≤ 170000000 * M →
                S15CrossingBound_L_gk K R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, β, x₀, Hopq, Mfl, hCg, hε, hKc,
    hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hMflb, hβ, hcapU⟩ :=
    flat_capstone_uniform_win_kwide K Awin hband
  refine ⟨ε, Cg, Kc, δ₀, Ct, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCgle, hεpin, hδpin, hMflb, hβ, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapU A hA26 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hsel hKw
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor hKw
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the LINEAR anchor
  have harith := s15_doorArithFrameRho_L_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register⟧
  have hgate : S13BandGate'_L_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_L_gk K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_gen le_rfl (s13_g2_jfloor_of_MSelect'_L_gk K (by linarith) hS))
    (s13_gate8_L_gk le_rfl (s13_gate8_of_MSelect'_L_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_L_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket_L hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorL_gk K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hlam50 htow
        hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM (hgate.block H L q j A s hb)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_L_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith

end Salt.MR

end
