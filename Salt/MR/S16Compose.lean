/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16Uniform
import Salt.MR.NumeralCt
import Salt.MR.NumeralKq
import Salt.Entropy.Chowla.GoldbachEnergyKc

/-!
# `S16Compose` — ⟦THE BAR-2 CLOSING PASS⟧ AND `logChowla2_ineffective_v3`

⟦THE STATE BEFORE THIS FILE⟧ `S16Uniform.logChowla2_ineffective_v2` carries **no outer
hypothesis at all** (the caller supplies only a depth `A₀`) and **six inner numeral riders**:

* `Kc ≤ 2^539` — the `|Ξ_H|` count constant at the head's pinned `ε = 1/500`;
* `Ct ≤ 2^23` — the constant-pool fuse's wide socket constant;
* `Kq ≤ e^100` — the cap wire's Halász/zero-free constant;
* `e^{-100} ≤ cs`, `T₀ ≤ e^{e^100}`, `e^{-100} ≤ Ks` — the remaining three.

The BAR-2 NUMERAL wave (`GoldbachEnergyKc`, `NumeralCt`, `NumeralKq`) priced the FIRST THREE
at their leaves and carried each up to the last hop outside the terminal lane, exporting three
`_ceiling` hooks whose statements are the landed ones plus ONE conjunct.  This file THREADS
those hooks through the uniform lane and mints

> `logChowla2_ineffective_v3 (A₀ : ℝ)` — `v2` with `Kc ≤ 2^539`, `Ct ≤ 2^23` and
> `Kq ≤ e^100` **REMOVED-BECAUSE-PROVEN**.

⟦THE ROUTE, HOOK BY HOOK⟧

* **`Kc`** — `bigXi_bounded_ceiling_of_pin` drops into the flat head at the pin `ε = 1/500`
  (`S16Uniform` §1 :284).  The conjunct then rides SEVEN twins: §1 head → §2 socket →
  §3 door-`L²` → §4 road → §6 capstone (windowed) → §7 conditional (windowed) → §9 terminal.
  It cannot be short-circuited higher: `K` enters §1 as an UPPER BOUND ON A COUNT (monotone
  up) and leaves §3 as a BUDGET COEFFICIENT in a hypothesis (monotone down), so no `min`
  trick survives the sign change.
* **`Ct`** — `m4_hrowsSlot_at_door_zero'_L_gk_ceiling` drops into
  `m4_closure_fuse_zero'_const_nonneg_L_gk` (§5 here), whose twin then feeds §6–§9.
* **`Kq`** — ⟦THE ONE CORRECTION TO THE MISSION BRIEF⟧ the `Kq` of the terminal's `∃`-prefix
  is **not** the one `S16Uniform` :660 opens: that `obtain`'s payload is DISCARDED (`… , -⟩`)
  and its five constants are re-exported only to be dropped again by `flat_conditional_*`.
  The terminal's `Kq` is minted by `S16FlatFinal.s15_crossing_supplied_L_gk`, off the LINEAR
  wire `S16FlatTerminalLinear.m4_fuse_hcap_of_capWS_L_gk` → `M4CapWireLinear.
  m4_hcap_at_door_perBlock_L_gk` → `M4RowsChi.m4_rowChi_capstone_perBlock`.  NUMERAL's route 3
  bounded the WIDE lane (`SocketBase`, `Adoor`, `doorChiCoeff_gk`); its leaf
  `m4_rowChi_capstone_perBlock_bounded` is however SHARED, so §8 here re-cuts the three LINEAR
  hops against that same leaf and lands the ceiling where the terminal actually reads it.
  `m4_fuse_hcap_of_capWS_gk_ceiling` (the wide hook) is therefore NOT consumed.

⟦WHAT SURVIVES IN `v3`⟧ outer: **nothing but `A₀`**.  Inner: `e^{-100} ≤ cs`,
`T₀ ≤ e^{e^100}`, `e^{-100} ≤ Ks` — three, not six.  Conclusion-side: the same two carried
predicates `S16CofactorSupply_L_gk` and `S16BaseScaleCap96_L_gk` at `flatDoorM A`.

**PURELY ADDITIVE.**  No landed declaration is touched anywhere; every proof body below is the
landed one with the named `obtain`/`refine` widened by one conjunct.
-/

-- ⟦BYTE-FAITHFUL REPLAY⟧ every proof body below is the landed proof, copied so that the twin
-- is auditable against its original line for line.  The three `private` helpers of
-- `S16Uniform` §0 are reached by `open private` (Batteries), the corpus's sanctioned device
-- (`GoldbachEnergyKc`, `HeadPinLeaves`) — no landed file gains a declaration.
open private spine_False_core_xi_sq_uniform uniformCap_arc uniformCap_shuffle from
  Salt.MR.S16Uniform

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE FLAT HEAD, WITH THE `Kc` CEILING -/

/-- **⟦THE `A`-UNIFORM FLAT HEAD, WITH ITS COUNT CONSTANT PRICED⟧**
(`flat_head_uniform_ceiling`) — `S16Uniform.flat_head_uniform` with ONE conjunct added,
`K ≤ 2^539`.  The body is the landed one; the only edit is the `ε`-pinned count hook
`Salt.Entropy.Chowla.bigXi_bounded_ceiling_of_pin ε hεdef` in place of
`bigXi_bounded ε hεQpos hε2`, which exports the same shape plus the ceiling. -/
theorem flat_head_uniform_ceiling :
    ∃ (ε : ℚ) (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 539 ∧ 0 < δ₀ ∧
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
  -- ⟦THE `δ₀` FLOOR⟧ the binding arm at its worst case
  have hδ₀ge : (1 : ℝ) / 838400 ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    have hkey : (5 : ℝ) / 2096 ≤ cD3 / (16 * C) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
    rw [hεR]; linarith
  -- ⟦THE ONE EDIT⟧ the count hook at the pin, carrying `Kc ≤ 2^539`
  obtain ⟨K, hK, hKb, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded_ceiling_of_pin ε hεdef
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = cD3 * (ε : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hcD3 hεR0) (by positivity)
  -- ⟦THE HEAD'S OWN FOUR-ARM FLOOR⟧ (flat) — `A`-FREE, which is the whole point
  obtain ⟨Hopq, hOpqdef⟩ : ∃ n : ℕ, n = max (max H₀red H₀D3) H₀xi := ⟨_, rfl⟩
  refine ⟨ε, K, cD3 / (16 * C) * (ε : ℝ) / 4, β, Hopq, hεQpos, hK, hKb,
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

/-! ## §2 — THE ROAD-FORM SOCKET, WITH THE `Kc` CEILING -/

/-- **⟦THE `A`-UNIFORM SPLIT SOCKET, PRICED⟧** (`flat_socket_uniform_ceiling`) —
`S16Uniform.flat_socket_uniform` on §1's twin, carrying `K ≤ 2^539`.  Body verbatim. -/
theorem flat_socket_uniform_ceiling :
    ∃ (ε : ℚ) (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 539 ∧ 0 < δ₀ ∧
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
  obtain ⟨ε, K, δ₀, β, Hopq, hε, hK, hKb, hδ₀, hεpin, hδpin, hβ, hhead⟩ :=
    flat_head_uniform_ceiling
  obtain ⟨H₀, hH₀⟩ := sum_bigXi_norm_windowExpSum_sq_le_twelve ε hε
  refine ⟨ε, K, δ₀, β, max Hopq H₀, hε, hK, hKb, hδ₀, hεpin, hδpin, hβ, ?_⟩
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

/-! ## §3 — THE CLOSED LOOP AT THE LINEAR LADDER, WITH THE `Kc` CEILING -/

/-- **⟦THE `A`-UNIFORM CLOSED LOOP, PRICED⟧** (`flat_doorL2_uniform_ceiling`) —
`S16Uniform.flat_doorL2_uniform` on §2's twin, carrying `Kb ≤ 2^539`.  Body verbatim. -/
theorem flat_doorL2_uniform_ceiling (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 539 ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
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
  obtain ⟨ε, Kb, δ₀, β, Hopq, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, hsk⟩ :=
    flat_socket_uniform_ceiling
  refine ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, ?_⟩
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

/-! ## §4 — THE FLAT ROAD'S TERMINAL REGISTER, WITH THE `Kc` CEILING -/

/-- **⟦THE `A`-UNIFORM TERMINAL REGISTER, PRICED⟧** (`flat_road_uniform_ceiling`) —
`S16Uniform.flat_road_uniform` on §3's twin.  Body verbatim. -/
theorem flat_road_uniform_ceiling (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 539 ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
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
  obtain ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, hdoor⟩ :=
    flat_doorL2_uniform_ceiling K
  refine ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, ?_⟩
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

/-! ## §5 — THE CONSTANT-POOL FUSE, WITH THE `Ct` CEILING -/

set_option maxHeartbeats 1000000 in
-- Same cause as the landed `m4_closure_fuse_zero'_const_nonneg_L_gk`: the ~50-binder
-- statement re-elaborates, here with one extra conjunct in the `∃`-prefix.
/-- **⟦THE CONSTANT-POOL FUSE, PRICED⟧** (`m4_closure_fuse_zero'_const_nonneg_L_gk_ceiling`) —
`S16FlatTerminalLinear.m4_closure_fuse_zero'_const_nonneg_L_gk` with `Ct ≤ 2^23` carried, off
`NumeralCt.m4_hrowsSlot_at_door_zero'_L_gk_ceiling`.  Body verbatim. -/
theorem m4_closure_fuse_zero'_const_nonneg_L_gk_ceiling (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kc ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 < ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          GRowsZeroGate'''_L_gk K M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
            ≤ (theta293 - ε (A + s)) * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kc ρ) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hCtb, hslot⟩ := m4_hrowsSlot_at_door_zero'_L_gk_ceiling K hK
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro Cp hCp R M C₁ M₀ ε Kc ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows hthr _heps293
    hband4096 hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_L_gk K (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := fun _ => constPool ρ R.Hhi)
    (RSbig := fun _ H => RSanDoorRho ρ H) hM ?_
    (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband
    (fun _ => constPool_nonneg hρ.le) (m4_arith_henv_constPool_L_gk K hρ.le harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_pos_L_gk K (hbf H L q j A s hb)
    (hgP1 H L q j A s hb) (hgRows H L q j A s hb) hρ (hthr H L q j A s hb) hM hXd
    (hband4096 H L q j A s hb)

/-! ## §6 — THE CAPSTONE, WINDOWED, WITH BOTH SOCKET CEILINGS -/

set_option maxHeartbeats 1600000 in
-- Same cause as `S16Uniform` §9.1: the ~120-line residue re-elaborates against the re-cut
-- prefix, which here gains two numeral conjuncts.
/-- **⟦THE `A`-UNIFORM CAPSTONE, WINDOWED AND PRICED⟧** (`flat_capstone_uniform_win_ceiling`)
— `S16Uniform.flat_capstone_uniform_win` on §4 and §5, carrying `Kc ≤ 2^539` and
`Ct ≤ 2^23`.  Body verbatim. -/
theorem flat_capstone_uniform_win_ceiling (K : ℕ) (hK : K ≤ 170000000) (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_win Awin K) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧ Ct ≤ 2 ^ 23 ∧
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
  obtain ⟨Cg, ε, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hKcb, hδ₀, hεpin, hδpin, hβ, hroadU⟩ :=
    flat_road_uniform_ceiling K
  obtain ⟨Ct, hCt, hCtb, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_L_gk_ceiling K hK
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, hKcb, hCtb,
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

/-! ## §7 — THE CONDITIONAL, WINDOWED, WITH BOTH SOCKET CEILINGS -/

set_option maxHeartbeats 1000000 in
-- Same cause as `S16Uniform` §9.2: the residue re-elaborates against the prefix.
/-- **⟦THE `A`-UNIFORM CONDITIONAL, WINDOWED AND PRICED⟧**
(`flat_conditional_uniform_win_ceiling`) — `S16Uniform.flat_conditional_uniform_win` on §6.
Body verbatim. -/
theorem flat_conditional_uniform_win_ceiling (K : ℕ) (hK : K ≤ 170000000) (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_win Awin K) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧ Ct ≤ 2 ^ 23 ∧
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
    hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hKcb, hCtb, hMflb,
    hβ, hcapU⟩ :=
    flat_capstone_uniform_win_ceiling K hK Awin hband
  refine ⟨ε, Cg, Kc, δ₀, Ct, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCgle, hεpin, hδpin, hKcb, hCtb, hMflb, hβ, ?_⟩
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

/-! ## §8 — THE LINEAR CAP WIRE, WITH THE `Kq` CEILING

⟦THE CORRECTION⟧ NUMERAL's route 3 bounded the WIDE cap wire; the flat linear terminal reads
the LINEAR one.  Both bottom out at the SAME leaf (`M4RowsChi.m4_rowChi_capstone_perBlock`,
bounded as `NumeralKq.m4_rowChi_capstone_perBlock_bounded`), so the three linear hops below are
the landed bodies replayed against that leaf's twin. -/

set_option maxHeartbeats 1600000 in
-- Same cause as the landed `m4_hcap_at_door_perBlock_L_gk`: one application of a ~45-binder
-- capstone, here re-elaborated with one extra conjunct in the `∃`-prefix.
/-- **⟦Kq BOUNDED TWIN, LINEAR⟧** `M4CapWireLinear.m4_hcap_at_door_perBlock_L_gk` +
`Kq ≤ 126848 / 10 ^ 8`.  Body verbatim. -/
theorem m4_hcap_at_door_perBlock_L_gk_bounded (K : ℕ) :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 : ℝ),
              DoorCapBasePerBlock_L_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf (2 * T)
                VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKqb, hKs, hcapstone⟩ :=
    m4_rowChi_capstone_perBlock_bounded
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKqb, hKs, ?_⟩
  intro R M cU ε hcU hfam H L q j A s hb χ T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, hd⟩ :=
    hfam H L q j A s hb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hlogX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := hd.logX_four
    linarith
  have hres := hcapstone q cU hcU (calP (AdoorL M) (s13GK K M))
    (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M)) (mrAlpha (1 / 12)) 2 Jb
    hd.Jb_lo hd.Jb_hi hd.Hseq_two hd.alpha_nonneg
    (2 * T) VJ V Lr (((A + s : ℕ)) : ℝ) hd.Tann_one hd.qTann_one hd.P_three hd.PQ hd.QTann
    hd.kappa30Q hd.loglog5 hd.VJ_bound η εd hd.alpha_eta hd.eta_half hd.Tann_X hd.X_pos
    hd.debit hd.logX_pos hd.q_logX hd.V_one hd.V_inv hd.T0_Tann hd.floor1 hd.floor2
    hd.floor3 hd.floor4 hd.logqT_one hd.logqT_L hd.L_exp hd.logV_L
    hd.H83_two hd.logX_exp hd.logX_four hTgate
    (2 * (A + s)) Xd P Q Mr (winCutH (A + s) (doorCoeffU_L_gk K M)) b cf hd.cf_one hd.P_low
    hd.Q_pos hd.Q_high hd.range hd.budget hd.Hj hd.B3 hd.BT hd.kappa30 hd.BT10 hd.WL hd.gate
    Rbd CR hd.Rbd_nonneg hd.Rbd_grade hd.Cq_gate
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ)) hd.Rbd_binder
    KS hd.KS_nonneg hd.KS_binder hd.KS_gate E EP2 (ε (A + s)) hd.epsr_nonneg hd.abs8640
    hd.EP2_gate hd.E_row hd.E_binder (doorCap_hXN (A + s)) (doorCap_hN2 (A + s))
    (fun n hn => doorRowDatumU_supp0_L_gk K M (A + s) hn)
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ))
    (m4_hSup_door_at_zero q (winCutH (A + s) (doorCoeffU_L_gk K M)) (2 * (A + s)) hlogX1) χ
  rw [chiBarCoeff_doorRowDatum_L_gk] at hres
  simpa using hres

set_option maxHeartbeats 1600000 in
-- Same cause as the landed `m4_fuse_hcap_of_capWS_L_gk`: the wire's own statement, here with
-- one extra conjunct in the `∃`-prefix.
/-- **⟦THE LINEAR CAP-WIRE FUSE, PRICED⟧** (`m4_fuse_hcap_of_capWS_L_gk_ceiling`) —
`S16FlatTerminalLinear.m4_fuse_hcap_of_capWS_L_gk` with `Kq ≤ e^100` carried.  Body
verbatim. -/
theorem m4_fuse_hcap_of_capWS_L_gk_ceiling (K : ℕ) :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ Kq ≤ Real.exp 100 ∧ 0 < Ks ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
              G2Scaffold.DoorCapErrWS_L_gk K M (A + s) q Xd P Q b cf (2 * T) E Mtail
                ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                      ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                        (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU_L_gk K M)))
                        (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                    → DoorCapBasePerBlock_L_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                        (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKqb, hKs, hwire⟩ :=
    m4_hcap_at_door_perBlock_L_gk_bounded K
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq,
    le_trans hKqb kq_closed_form_le_exp_hundred, hKs, ?_⟩
  intro R M cU ε hc1 hcapWS
  refine hwire R M cU ε hc1 ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (G2Scaffold.m4_capE_at_door_L_gk K hws)⟩

set_option maxHeartbeats 1600000 in
-- Same cause as the landed `s15_crossing_supplied_L_gk`: the eighteen-slot `hcapWS` family
-- re-elaborates against the wire's own shape, here with one extra conjunct.
/-- **⟦THE CROSSING SUPPLY, PRICED⟧** (`s15_crossing_supplied_L_gk_ceiling`) —
`S16FlatFinal.s15_crossing_supplied_L_gk` with `Kq ≤ e^100` carried.  Body verbatim. -/
theorem s15_crossing_supplied_L_gk_ceiling (K : ℕ) :
    ∃ Cq cs T₀ Kq Ks C : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ Kq ≤ Real.exp 100 ∧
      0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      (Real.exp (-100) ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ (R : ChowlaRegime) (M : ℕ), 1 ≤ M → loglogFloor50 ≤ R.Hlo →
          (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → s13BlockFloor_L_gk K M ≤ A + s) →
          S16CofactorSupply_L_gk K Cq R M → S16BaseScaleCap96_L_gk K R M →
          S15CrossingBound_L_gk K R M) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs0, hT₀3, hKq0, hKqb, hKs0, hwire⟩ :=
    m4_fuse_hcap_of_capWS_L_gk_ceiling K
  obtain ⟨C, hC0, hC40, hband⟩ := m4_tail_mass_at_band_bounded
  refine ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKqb, hKs0, hC0, hC40, ?_⟩
  intro hcs hT₀ hKq hKs R M hM hfl hblk hcof hcap
  have hgate := s16_capGate_supply_L_gk K hM hfl hcs hblk hT₀ hKq hKs hC0 hC40
    (fun _ => le_rfl) hcap hcof
  refine hwire R M liouvilleC (fun _ => theta293 - 1 / 500) liouvilleC_norm_le_one ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨P, Q, Rrad, Rbd, CR, EP2, hg⟩ := hgate H L q j A s hsb T hTlo hThi hTgate hTll
  have hq : 1 ≤ q := hsb.2.2.2.1
  have hA : 0 < A := hsb.2.2.2.2.2.2.2.1
  have hNd : 1 ≤ A + s := by omega
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by have := hg.logX_eight; linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
  have hT1 : (1 : ℝ) < 2 * T := by linarith
  exact doorCapBundle_at_workingPoint_perBlock_L_gk K hband hM hNd hq hg hT1 hThi hTll

/-! ## §9 — THE FLAT LINEAR TERMINAL `v2`, UNIFORM, WINDOWED, THREE RIDERS GONE -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 1600000 in
-- Same cause as `S16Uniform` §9.3: the long binder prefix re-elaborates beside the crossing
-- supply's six constants, under the `∀ A` binder with the window's admissibility line.
/-- **⟦THE FLAT LINEAR TERMINAL, `v2`, `A`-UNIFORM, WINDOWED, PRICED⟧**
(`logChowla2_witnessed_scale_flat_L_v2_uniform_win_ceiling`) —
`S16Uniform.logChowla2_witnessed_scale_flat_L_v2_uniform_win` with the inner antecedents
`Kc ≤ 2^539`, `Ct ≤ 2^23` and `Kq ≤ e^100` **REMOVED-BECAUSE-PROVEN**: the first two arrive as
conjuncts of §7's `∃`-prefix, the third as a conjunct of §8's crossing supply.  The `∃`-prefix
is byte-identical to the landed one (the ceilings are spent, not re-exported).  Body
verbatim. -/
theorem logChowla2_witnessed_scale_flat_L_v2_uniform_win_ceiling (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_win Awin 32000000) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          Real.exp (-100) ≤ cs → T₀ ≤ Real.exp (Real.exp 100) →
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
    hCgle, hεpin, hδpin, hKcb, hCtb, hMflb, hβ, hcond⟩ :=
    flat_conditional_uniform_win_ceiling 32000000 (by norm_num) Awin hband
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKqb, hKs0, hC0, hC40, hsupply⟩ :=
    s15_crossing_supplied_L_gk_ceiling 32000000
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
  intro hx0win hopq hcs hT₀ hKs g
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
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win hA26 32000000 hKle hδ₀ hδpin hKc hKcb
    hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win heps hlo hwin
  -- ⟦THE CROSSING, SUPPLIED⟧ the block floor off the register's own `blk` line
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk 32000000 (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk 32000000 (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel
    (hsupply hcs hT₀ hKqb hKs R (flatDoorM A) hM1 hfl hblk hcof hcapsc)

/-! ## §10 — ⟦THE INEFFECTIVE LIMIT, `v3`⟧ THREE OF THE SIX NUMERAL RIDERS, GONE -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 800000 in
-- Same cause as `S16Uniform` §9.4: the hoisted prefix plus the three window discharges
-- re-elaborate the terminal's conclusion.
/-- **⟦THE INEFFECTIVE LIMIT, `v3`⟧** (`logChowla2_ineffective_v3`) —
`S16Uniform.logChowla2_ineffective_v2` with THREE of its six inner riders
**REMOVED-BECAUSE-PROVEN**: `Kc ≤ 2^539`, `Ct ≤ 2^23` and `Kq ≤ e^100`.

⟦WHY THEY GO⟧ each was a rider only because every hop on its chain packs the constant into an
`∃ C, 0 < C ∧ …` that exports POSITIVITY ALONE — never because the constant is large.  The
BAR-2 NUMERAL wave priced all three at their leaves (`32·e^40·(2^35)²·500^10 ≤ 2^228.2`;
`6·e^14 = 2^22.78`; `1.26848·10^{-3}`) and this file carries the three conjuncts up the uniform
lane, where the proof spends them at `s15_sel''_L_gk_witness_flat_bumped_win` (`Kc`, `Ct`) and
at `s15_crossing_supplied_L_gk` (`Kq`).

⟦THE SURVIVING LIST, EXACT AND COMPLETE⟧ **outer: NOTHING** (the caller supplies only the depth
`A₀`).  Inner: THREE numeral riders — `e^{-100} ≤ cs`, `T₀ ≤ e^{e^{100}}`, `e^{-100} ≤ Ks` — all
three on constants THIS THEOREM produces, and all three open traces over unbounded
compactness/VK leaves (the `cs`/`T₀`/`Ks` lane, untouched by the numeral wave).
Conclusion-side: the two carried predicates `S16CofactorSupply_L_gk` and
`S16BaseScaleCap96_L_gk` at `flatDoorM A`.  **No band rider.  No `x₀`.  No `Hopq`.  No Siegel
hypothesis.  No `Kc`, no `Ct`, no `Kq`.** -/
theorem logChowla2_ineffective_v3 (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      (Real.exp (-100) ≤ cs → T₀ ≤ Real.exp (Real.exp 100) →
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
    logChowla2_witnessed_scale_flat_L_v2_uniform_win_ceiling Awin hband
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
  intro hcs hT₀ hKs g
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq hcs hT₀ hKs g
  exact ⟨R, hReps, by rw [hHlo]; exact hbase hopq, hRg, hRtow, hdes, hwin, hfire2⟩

end Salt.MR

end
