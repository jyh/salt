/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HloExportMRFlat
import Salt.MR.S15Witness
import Salt.Entropy.Chowla.HloExportFlat

/-!
# THE ROAD AT THE FLAT ROOT — `HloExportMR`'s chain re-rooted (freeze F-1..F-5)

`Salt.MR.HloExportMRFlat` (W2) carries the FLAT width conjunct
`loglog H₊ ≤ e^{loglog H₋/2}` across the road, but its twins are rooted, through
their landed originals, in the LANDED head — hence in the landed `9/2` producer
AND in the landed triple-exponential `budgetFloor`.  This file supplies THE
REPLACEMENT ROOT: the same three road statements built directly on
`Salt.Entropy.Chowla.log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat`,
so that

* the width conjunct comes from `towerFlat_width_export` (freeze F-5) with NO
  `9/2` law anywhere in the derivation — the shape bridge is gone, not applied;
* the base cap is the FLAT cap, whose only named arms are `flatDesignFloor A`
  and the HEIGHT-1 `budgetFloorFlat ε β A`;
* the design constant `A` rides the `∃`-prefix, SYMBOLIC, above a caller-supplied
  `A₀` (FLAT-REF §4: no numeral is chosen anywhere in the build).

⟦THE CHAIN⟧ socket (§1) → loop (§2, and §GK at the lever) → second road (§3, and
§GK) — the `HloExportMR` §4/§GK template with three edits per step: the root, the
conjunct shape, and the two new prefix items carried through the
destructure/rebuild.  Every proof body below is the landed one verbatim.

⟦§4 — THE CAP COMPARISON⟧ the point of the whole flat road, stated as theorems:
`budgetFloorFlat` is `⌈e^{max (4X) (2 log A + 2)}⌉₊` where the landed
`budgetFloor` is `⌈e^{e^{e^{X}}}⌉₊`, and `flatDesignFloor A` is a `max` of three
`⌈e^·⌉₊`.  So the flat cap clears the compose's witness floor
`S15Witness.s15WitFloor2 = ⌈e^{2^{400}}⌉₊` under EXPLICIT, SYMBOLIC side
conditions on `A` and on the budget exponent — which is exactly the arithmetic
the flat compose has to price, and which no landed statement could even state.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — the two `max`-lattice shuffles -/

/-- The arc floor absorbed into the cap's opaque arm. -/
private lemma flatRootCap_arc (d p b c h : ℕ) :
    max (max d (max (max p b) c)) h ≤ max d (max (max (max p h) b) c) := by
  omega

/-! ## §1 — the road-form socket at the flat root -/

/-- **THE SPLIT SOCKET, ROAD FORM, AT THE FLAT ROOT**
(`m4_exit_socket_split_sq_arc_flatRoot`) — `HloExportMR`'s
`m4_exit_socket_split_sq_arc_hloCap_pinned` with the FLAT head as its root.  Two
new `∃`-prefix items (`A`, `β`) and one new `∃`-prefix `ℕ` (`Hopq`, the road's
opaque floor arm) ride beside the landed prefix; the cap conjunct becomes the
FLAT cap BOUND, and the tower conjunct is at the flat shape by construction.

M4-0's arc floor `H₀` is absorbed into `Hopq` (not into a fresh `Hcap` arm), so
the cap bound keeps the head's three-arm shape and the height claim survives the
step. -/
theorem m4_exit_socket_split_sq_arc_flatRoot (A₀ : ℝ) (hA₀ : 26 ≤ A₀) :
    ∃ (ε : ℚ) (K δ₀ A β : ℝ) (Hcap Hopq : ℕ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧ 26 ≤ A ∧ A₀ ≤ A ∧
      budgetAFlat (ε : ℝ) β ≤ A ∧
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
  obtain ⟨ε, K, δ₀, A, β, Hcap, Hopq, hε, hK, hδ₀, hεpin, hδpin, hβ, hA26, hA₀A,
    hAge, hCapEq, hhead⟩ := log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat A₀ hA₀
  obtain ⟨H₀, hH₀⟩ := sum_bigXi_norm_windowExpSum_sq_le_twelve ε hε
  refine ⟨ε, K, δ₀, A, β, max Hcap H₀, max Hopq H₀, hε, hK, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, by rw [hCapEq]; exact flatRootCap_arc _ _ _ _ _, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, _, hRU1, hRg, hcount, hRtow, hRcap, hR⟩ := hhead 0 (max U1floor H₀) g
  have hU1 : U1floor ≤ R.Hlo := le_trans (le_max_left _ _) hRU1
  have harc : H₀ ≤ R.Hlo := le_trans (le_max_right _ _) hRU1
  refine ⟨R, hReps, hU1, hRg, hRtow, le_trans hRcap (by omega), ?_⟩
  intro a e Bsieve Binsert hsplit hB0 hsock hins hρ
  refine hR δ₀ hδ₀ le_rfl ?_
  intro H _ hlo hhi
  exact le_trans (hH₀ R hReps harc a e Bsieve K Binsert hsplit hB0 hsock hcount hins
    H hlo hhi) (hρ H hlo hhi)

/-! ## §2 — the closed loop at the flat root -/

/-- **THE LOOP, CLOSED, AT THE FLAT ROOT** (`m4_doorL2_close_split_sq_flatRoot`) —
`HloExportMR.m4_doorL2_close_split_sq_hloCap_pinned` on §1.  A pure conjunct
carry: the door body is the landed one, verbatim. -/
theorem m4_doorL2_close_split_sq_flatRoot (A₀ : ℝ) (hA₀ : 26 ≤ A₀) :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ A β : ℝ) (Hcap Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      26 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
      Hcap ≤ max (flatDesignFloor A)
        (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq R M Braw →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * K * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  obtain ⟨ε, K, δ₀, A, β, Hcap, Hopq, hε, hK, hδ₀, hεpin, hδpin, hβ, hA26, hA₀A,
    hAge, hCapLe, hexit⟩ := m4_exit_socket_split_sq_arc_flatRoot A₀ hA₀
  refine ⟨Cg, ε, K, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hK, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, hCapLe, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hexit U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  have hA : 1 ≤ Adoor M := by
    have h := Adoor_ge M
    omega
  have hG : 1 ≤ 3072 * M := by
    have := hgates.hM
    omega
  have hHx : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
    intro H hhi
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  refine hR (memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC)
    (fun m => lamCoeff m - memSCoeff (calP (Adoor M) (3072 * M))
      (calQK (Adoor M) (3072 * M) M) 2 liouvilleC m)
    Braw (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) (fun m => by ring) hBraw0
    (hsock m4_bandTransport) ?_ ?_
  · intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (Adoor M) (3072 * M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · intro H hlo hhi
    rw [l2_budget_line K (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * K * Braw H ≤ 2 * K * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

/-! ## §GK-2 — the closed loop at the flat root, at the G-lever -/

/-- `m4_doorL2_close_split_sq_flatRoot` at `G := s13GK K M` (the `GLever` form the
capstone compose actually consumes), `(K : ℕ)` first, the road's `L²` constant
alpha-renamed to `Kb` per THE KDESIGN. -/
theorem m4_doorL2_close_split_sq_gk_flatRoot (K : ℕ) (A₀ : ℝ) (hA₀ : 26 ≤ A₀) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ A β : ℝ) (Hcap Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      26 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
      Hcap ≤ max (flatDesignFloor A)
        (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq_gk K R M Braw →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  obtain ⟨ε, Kb, δ₀, A, β, Hcap, Hopq, hε, hKb, hδ₀, hεpin, hδpin, hβ, hA26, hA₀A,
    hAge, hCapLe, hexit⟩ := m4_exit_socket_split_sq_arc_flatRoot A₀ hA₀
  refine ⟨Cg, ε, Kb, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, hCapLe, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hexit U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  have hA : 1 ≤ Adoor M := by
    have h := Adoor_ge M
    omega
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
    intro H hhi
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  refine hR (memSCoeff (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) 2
      liouvilleC)
    (fun m => lamCoeff m - memSCoeff (calP (Adoor M) (s13GK K M))
      (calQK (Adoor M) (s13GK K M) M) 2 liouvilleC m)
    Braw (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) (fun m => by ring) hBraw0
    (hsock m4_bandTransport) ?_ ?_
  · intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (Adoor M) (s13GK K M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · intro H hlo hhi
    rw [l2_budget_line Kb (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * Kb * Braw H ≤ 2 * Kb * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

/-! ## §3 — THE SECOND ROAD'S TERMINAL REGISTER, AT THE FLAT ROOT -/

/-- **⟦THE SECOND ROAD'S TERMINAL REGISTER, `L²`, AT THE FLAT ROOT⟧**
(`m4_second_road_L2_flatRoot`) — `HloExportMR.m4_second_road_L2_hloCap_pinned` on
§2.  THE ELEVEN-ITEM CENSUS and the four named suppliers are the landed ones,
item for item; the proof body is the landed one, verbatim. -/
theorem m4_second_road_L2_flatRoot (A₀ : ℝ) (hA₀ : 26 ≤ A₀) :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ A β : ℝ) (Hcap Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      26 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
      Hcap ≤ max (flatDesignFloor A)
        (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
            M4DoorGates Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * K * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
            M4ChiSummedFreeRow R M RS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hK, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, hCapLe, hmain⟩ := m4_doorL2_close_split_sq_flatRoot A₀ hA₀
  refine ⟨Cg, ε, K, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hK, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, hCapLe, ?_⟩
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
  have hchi : M4ChiSummedBlockMeanSqN R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hblk2 := m4_blockMeanSqBlk2_of_chiSummed (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  have hcov := m4_cover_assembly_blk2 hgates hBblk0 hblk2
  refine hR Braw Bceil δ M k hgates hBraw0 ?_ hceil hbudget
  refine m4_sievedDoorSq_of_blk2 (ℓ := blockLen)
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

/-! ## §GK-3 — THE DELIVERABLE: the terminal register at the flat root, at the lever -/

/-- **⟦THE FLAT ROAD'S TERMINAL REGISTER⟧** (`m4_second_road_L2_gk_flatRoot`) —
§3 at `G := s13GK K M`.  THIS is the surface the flat compose reads: the exact
statement `HloExportMRFlat.m4_second_road_L2_hloCap_pinned_gk_flat` carries, plus
the three flat prefix items (`A`, `β`, `Hopq`) and the FLAT cap bound — and,
unlike that twin, rooted in the flat head, so no triple-exponential `budgetFloor`
occurs anywhere beneath it and the threshold spent is `κ = H/(A·log H)`.

⚠ ⟦ONE HONEST RESIDUE⟧ the `9/2` law has NOT disappeared from the derivation.
`ChowlaRegimeFlat` extends `ChowlaRegime`, so the builder's endpoint is
`H₊ = max (landed tower) (flat tower)` and the width export is proved arm by
arm: the flat arm by freeze F-5, the LANDED arm still by
`tower_loglog_le_45` + `pow_nine_halves_le_exp_half`.  The exported SHAPE is flat
either way; what survives is a citation, not a `9/2` bound in any statement. -/
theorem m4_second_road_L2_gk_flatRoot (K : ℕ) (A₀ : ℝ) (hA₀ : 26 ≤ A₀) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ A β : ℝ) (Hcap Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      26 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
      Hcap ≤ max (flatDesignFloor A)
        (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
            M4DoorGates_gk K Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
            M4ChiSummedFreeRow_gk K R M RS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kb, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, hCapLe, hmain⟩ := m4_doorL2_close_split_sq_gk_flatRoot K A₀ hA₀
  refine ⟨Cg, ε, Kb, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, hCapLe, ?_⟩
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
  have hchi : M4ChiSummedBlockMeanSqN_gk K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied_gk K j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummed_gk (k := k) K hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  have hcov := m4_cover_assembly_blk2_gk K hgates hBblk0 hblk2
  refine hR Braw Bceil δ M k hgates hBraw0 ?_ hceil hbudget
  refine m4_sievedDoorSq_of_blk2_gk (ℓ := blockLen) K
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

/-! ## §4 — THE CAP COMPARISON: the flat cap against the compose's witness floor -/

/-- `e^{400·log 2} = 2^400` — the bridge between the flat design law's exponential
and `s15WitFloor2`'s numeral. -/
theorem exp_four_hundred_log_two : Real.exp (400 * Real.log 2) = (2 : ℝ) ^ (400 : ℕ) := by
  rw [show (400 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ (400 : ℕ)) by
    rw [Real.log_pow]; norm_num]
  exact Real.exp_log (by positivity)

/-- **THE DESIGN WINDOW.**  `e^{3.2A} ≤ 2^400` is EXACTLY `3.2·A ≤ 400·log 2` —
the symbolic ceiling the flat design constant meets at the compose's witness
floor.  (No numeral for `A` is chosen: this is the inequality the compose has to
satisfy, stated.) -/
theorem flat_design_exp_le_pow400 {A : ℝ} (h : 3.2 * A ≤ 400 * Real.log 2) :
    Real.exp (3.2 * A) ≤ (2 : ℝ) ^ (400 : ℕ) := by
  rw [← exp_four_hundred_log_two]
  exact Real.exp_le_exp.mpr h

/-- **THE FLAT DESIGN FLOOR CLEARS THE WITNESS FLOOR** — under the design window
and the (far weaker) base-arm bound. -/
theorem flatDesignFloor_le_s15WitFloor2 {A : ℝ} (hA : 1 ≤ A)
    (hbase : 200 * flatC A + 10000 ≤ (2 : ℝ) ^ (400 : ℕ))
    (hdes : 3.2 * A ≤ 400 * Real.log 2) :
    flatDesignFloor A ≤ s15WitFloor2 :=
  flatDesignFloor_le_ceil_exp hA hbase (flat_design_exp_le_pow400 hdes)

/-- **THE HEIGHT-1 BUDGET FLOOR CLEARS THE WITNESS FLOOR.**  `budgetFloorFlat` is
`⌈e^{max (4X) (2·log A + 2)}⌉₊` — ONE exponential — so a bound on the exponent is
all it takes.  The landed `budgetFloor ε β = ⌈e^{e^{e^{X}}}⌉₊` admits no such
statement at any finite exponent bound: that is the height collapse, in one
comparison. -/
theorem budgetFloorFlat_le_s15WitFloor2 (ε β A : ℝ)
    (h : max (4 * budgetXFlat ε β) (2 * Real.log A + 2) ≤ (2 : ℝ) ^ (400 : ℕ)) :
    budgetFloorFlat ε β A ≤ s15WitFloor2 := by
  rw [budgetFloorFlat, s15WitFloor2]
  exact Nat.ceil_le_ceil (Real.exp_le_exp.mpr h)

/-- **THE FLAT CAP CLEARS THE WITNESS FLOOR** — the three-arm assembly.  Fired
with the two named-arm bounds above, plus the road's own opaque arm and the
`ε`-arm, it discharges `Hcap ≤ s15WitFloor2`, i.e. the compose may fire the flat
road at `U1floor := s15WitFloor2` and PIN the base there. -/
theorem flatCap_le_s15WitFloor2 {A β : ℝ} {ε : ℚ} {Hcap Hopq : ℕ}
    (hCapLe : Hcap ≤ max (flatDesignFloor A)
      (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)))
    (hdf : flatDesignFloor A ≤ s15WitFloor2)
    (hopq : Hopq ≤ s15WitFloor2)
    (hbud : budgetFloorFlat (ε : ℝ) β A ≤ s15WitFloor2)
    (heps : 4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4 ≤ s15WitFloor2) :
    Hcap ≤ s15WitFloor2 :=
  le_trans hCapLe (max_le hdf (max_le (max_le hopq hbud) heps))

end Salt.MR

