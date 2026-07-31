/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S11Thread
import Salt.MR.S11Hoist
import Salt.MR.S11Arc36
import Salt.MR.S11CoefWS
import Salt.MR.M4DoorL2
import Salt.Entropy.Chowla.HloExport
import Salt.MR.CgPin

/-!
# ⟦THE `Hlo` CAP⟧ on the road — the MR half of the re-thread (node HLO-EXPORT)

`Salt.Entropy.Chowla.HloExport` re-threads the regime builder's discarded base
equation up to the spine head
(`log_chowla_two_budget_head_g_sq_count_hloCap`, which carries
`R.Hlo ≤ max Hcap (max extraFloor U1floor)` at a consumer-FREE `Hcap`).  This
file carries that ONE conjunct across the three remaining road statements —
`S11ExitL2.m4_exit_socket_split_sq_arc`, `M4DoorL2.m4_doorL2_close_split_sq`,
`S12Compose.m4_second_road_L2` — as ADDITIVE TWINS.  Every landed declaration is
untouched; each twin's statement is its landed original with

* `(Hcap : ℕ)` appended to the `∃`-prefix (it depends on `ε` alone, so it is
  fixed before the consumer's `(U1floor, g)` binder — that is what makes the
  conjunct usable), and
* `R.Hlo ≤ max Hcap U1floor` inserted in the `∃R` payload, immediately after the
  tower conjunct.

⟦WHAT THE CAP BUYS⟧  With the landed `U1floor ≤ R.Hlo` beside it, a consumer who
fires at `U1floor ≥ Hcap` gets `R.Hlo ≤ max Hcap U1floor = U1floor ≤ R.Hlo`: the
base is PINNED at the consumer's own floor.  A band that is two-sided in
`loglog R.Hlo` — the compose's M-band — can then be closed from below AND above,
which no landed surface in this chain permits.

⟦THE `H₀` ABSORPTION⟧  `m4_exit_socket_split_sq_arc` fires the head at
`U1floor := max U1floor H₀` (M4-0's ε-determined arc floor).  `H₀` is
consumer-free, so it is absorbed into the twin's own `Hcap := max Hcap' H₀` and
the exported shape stays `R.Hlo ≤ max Hcap U1floor`; the `max`-shuffles are all
`omega`.

The door-form socket `m4_exit_socket_split_sq` (`S11ExitL2.lean:81`) needs no
twin: the arc form does not route through it — both read the head directly.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — the road-form socket, cap-carrying -/

/-- **THE SPLIT SOCKET, ROAD FORM, WITH THE BASE CAP**
(`m4_exit_socket_split_sq_arc_hloCap`) — `S11ExitL2.m4_exit_socket_split_sq_arc`
(`S11ExitL2.lean:121`) plus `(Hcap : ℕ)` in the `∃`-prefix and the payload
conjunct `R.Hlo ≤ max Hcap U1floor`.

The proof is the landed one on the cap-carrying head
(`log_chowla_two_budget_head_g_sq_count_hloCap`), with M4-0's arc floor `H₀`
hoisted out of the `∀ U1floor` block (it never depended on it) and absorbed into
the exported `Hcap`. -/
theorem m4_exit_socket_split_sq_arc_hloCap :
    ∃ (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
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
  obtain ⟨ε, K, δ₀, Hcap, hε, hK, hδ₀, hhead⟩ :=
    log_chowla_two_budget_head_g_sq_count_hloCap
  obtain ⟨H₀, hH₀⟩ := sum_bigXi_norm_windowExpSum_sq_le_twelve ε hε
  refine ⟨ε, K, δ₀, max Hcap H₀, hε, hK, hδ₀, ?_⟩
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

/-! ## §2 — the closed loop, cap-carrying -/

/-- **THE LOOP, CLOSED, WITH THE BASE CAP** (`m4_doorL2_close_split_sq_hloCap`) —
`M4DoorL2.m4_doorL2_close_split_sq` (`M4DoorL2.lean:592`) plus `(Hcap : ℕ)` in the
`∃`-prefix and `R.Hlo ≤ max Hcap U1floor` in the payload.  A pure conjunct carry:
the proof is the landed one, reading §1 instead of the landed socket, with the new
conjunct destructured and re-emitted. -/
theorem m4_doorL2_close_split_sq_hloCap :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq R M Braw →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * K * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hpars⟩ := parseval_insert_budget_door
  obtain ⟨ε, K, δ₀, Hcap, hε, hK, hδ₀, hexit⟩ := m4_exit_socket_split_sq_arc_hloCap
  refine ⟨Cg, ε, K, δ₀, Hcap, hCg, hε, hK, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hexit U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  -- ⟦the door's own scales, off the regime⟧
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
  · -- ⟦THE FUSE⟧ the insert budget, from the Parseval stone, in W4's own spelling
    intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (Adoor M) (3072 * M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · -- ⟦the budget line⟧ `l2_budget_line`, then the `H`-uniform ceiling on the socket leg
    intro H hlo hhi
    rw [l2_budget_line K (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * K * Braw H ≤ 2 * K * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

/-! ## §3 — THE TERMINAL: the second road's register, cap-carrying -/

/-- **⟦THE SECOND ROAD'S TERMINAL REGISTER, AT THE `L²` DOOR, WITH THE BASE CAP⟧**
(`m4_second_road_L2_hloCap`) — `S12Compose.m4_second_road_L2` (`S12Compose.lean:100`)
plus `(Hcap : ℕ)` in the `∃`-prefix and the payload conjunct

```
R.Hlo ≤ max Hcap U1floor
```

immediately after the `9/2` tower conjunct.  THE ELEVEN-ITEM CENSUS is unchanged
item for item, the four named suppliers are unchanged, and the proof is the landed
one with §2 read in place of `m4_doorL2_close_split_sq` and the new conjunct
carried through the destructure/rebuild.

⟦THE DELIVERABLE⟧  This is the surface the capstone recut consumes: fired at any
`U1floor ≥ Hcap`, its payload pins `R.Hlo` between `U1floor` (landed conjunct) and
`max Hcap U1floor = U1floor` (this conjunct), so a two-sided `loglog R.Hlo` band
— the M-band — is available where the landed statement offered only the lower
half. -/
theorem m4_second_road_L2_hloCap :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
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
  obtain ⟨Cg, ε, K, δ₀, Hcap, hCg, hε, hK, hδ₀, hmain⟩ := m4_doorL2_close_split_sq_hloCap
  refine ⟨Cg, ε, K, δ₀, Hcap, hCg, hε, hK, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  -- ⟦the window floor, read at the two powers the chain spends⟧
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
  -- ⟦the blocked block mean square⟧
  have hblk2 := m4_blockMeanSqBlk2_of_chiSummed (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  -- ⟦the cover, then the socket⟧
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

/-! ## §4 — THE ROAD, PINNED: the numerals ride the `∃`-prefix -/

/-- **THE SPLIT SOCKET, ROAD FORM, CAPPED AND PINNED**
(`m4_exit_socket_split_sq_arc_hloCap_pinned`) — §1 plus the head's two pin
conjuncts `1/500 ≤ ε` and `1/838400 ≤ δ₀`
(`HloExport.log_chowla_two_budget_head_g_sq_count_hloCap_pinned`, §4 there).  A
pure conjunct carry: the §1 proof with the pinned head read in place of the
capped one, the two new items destructured and re-emitted. -/
theorem m4_exit_socket_split_sq_arc_hloCap_pinned :
    ∃ (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
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
  obtain ⟨ε, K, δ₀, Hcap, hε, hK, hδ₀, hεpin, hδpin, hhead⟩ :=
    log_chowla_two_budget_head_g_sq_count_hloCap_pinned
  obtain ⟨H₀, hH₀⟩ := sum_bigXi_norm_windowExpSum_sq_le_twelve ε hε
  refine ⟨ε, K, δ₀, max Hcap H₀, hε, hK, hδ₀, hεpin, hδpin, ?_⟩
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

/-- **THE LOOP, CLOSED, CAPPED AND PINNED** (`m4_doorL2_close_split_sq_hloCap_pinned`)
— §2 plus THREE conjuncts: `Cg ≤ 2·10^12` (from `CgPin`'s terminal twin
`parseval_insert_budget_door_bounded`, the eight-link carry off
`ConstantsExposed.typical_density_le_bounded`), `1/500 ≤ ε` and `1/838400 ≤ δ₀`
(from §4.1).  A pure conjunct carry; the door body is §2's, verbatim. -/
theorem m4_doorL2_close_split_sq_hloCap_pinned :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq R M Braw →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * K * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  obtain ⟨ε, K, δ₀, Hcap, hε, hK, hδ₀, hεpin, hδpin, hexit⟩ :=
    m4_exit_socket_split_sq_arc_hloCap_pinned
  refine ⟨Cg, ε, K, δ₀, Hcap, hCg, hCgle, hε, hK, hδ₀, hεpin, hδpin, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hexit U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  -- ⟦the door's own scales, off the regime⟧
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
  · -- ⟦THE FUSE⟧ the insert budget, from the Parseval stone, in W4's own spelling
    intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (Adoor M) (3072 * M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · -- ⟦the budget line⟧ `l2_budget_line`, then the `H`-uniform ceiling on the socket leg
    intro H hlo hhi
    rw [l2_budget_line K (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * K * Braw H ≤ 2 * K * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

/-- **⟦THE SECOND ROAD'S TERMINAL REGISTER, `L²`, CAPPED AND PINNED⟧**
(`m4_second_road_L2_hloCap_pinned`) — §3 plus the same three conjuncts, carried
through the destructure/rebuild.  The ELEVEN-ITEM CENSUS and the four named
suppliers are §3's, item for item.

⟦THE DELIVERABLE⟧  This is the surface the capstone compose consumes when it
needs the constants AS NUMBERS.  Its `∃`-prefix now carries, beside the base cap,

```
Cg ≤ 2·10^12,   1/500 ≤ ε,   1/838400 ≤ δ₀
```

— i.e. exactly `ConstantsExposed.Cg_le`'s ceiling and `S13FramesA.s13Delta0_ge`'s
floor, but as facts ABOUT THE ROAD'S OWN CONSTANTS rather than about closed-form
stand-ins.  The register line `24·Cg/δ₀ ≤ M` is therefore reachable here at
numerals: `24·(2·10^12)·838400 = 4.024·10^19 < 2^66`. -/
theorem m4_second_road_L2_hloCap_pinned :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ),
      1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
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
  obtain ⟨Cg, ε, K, δ₀, Hcap, hCg, hCgle, hε, hK, hδ₀, hεpin, hδpin, hmain⟩ :=
    m4_doorL2_close_split_sq_hloCap_pinned
  refine ⟨Cg, ε, K, δ₀, Hcap, hCg, hCgle, hε, hK, hδ₀, hεpin, hδpin, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  -- ⟦the window floor, read at the two powers the chain spends⟧
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
  -- ⟦the blocked block mean square⟧
  have hblk2 := m4_blockMeanSqBlk2_of_chiSummed (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  -- ⟦the cover, then the socket⟧
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

/-! ## §GK — the G-lever twin

The `L²` door export at `G := s13GK K M` (`GLever`), `(K : ℕ)` first.

⟦§1 IS `G`-FREE AND IS REUSED VERBATIM⟧ `m4_exit_socket_split_sq_arc_hloCap` (:68) and its
pinned twin (:277) speak an ABSTRACT split `(a, e)` — no door object occurs in either
statement — so both are consumed unchanged by the twins below.  `parseval_insert_budget_door`,
its bounded twin, `sum_bigXi_insert_spelling_eq` and `l2_budget_line` are `(A, G)`-ABSTRACT or
datum-abstract and are RE-INSTANTIATED at `calP (Adoor M) (s13GK K M)` /
`calQK (Adoor M) (s13GK K M) M`; `m4_bandTransport` is `G`-blind.

⟦WHY THESE FOUR DO NEED TWINS⟧ their own text reads the ladder only at LEVEL 1 (`hdgate`'s
`𝒫₁`), but they carry `M4Close.M4SievedDoorSq`, `M4Close.M4DoorGates` and
`M4ChiSummed.M4ChiSummedFreeRow` in their hypothesis lists, and all three read the door datum
`memSCoeff (calP (Adoor M) (3072M)) (calQK (Adoor M) (3072M) M) 2 …` at LEVEL 2.  The twins
are at `M4SievedDoorSq_gk`, `M4DoorGates_gk`, `M4ChiSummedFreeRow_gk` (all landed elsewhere in
this dispatch).

⚠ ⟦THE BINDER SHADOW⟧ all four landed statements bind a REAL `K` in their `∃`-prefix — the
`L²` budget constant.  It is ALPHA-RENAMED to `Kb` so the lever's `(K : ℕ)` can go first, per
THE KDESIGN. -/

/-- `m4_doorL2_close_split_sq_hloCap` (:112), at the lever. -/
theorem m4_doorL2_close_split_sq_hloCap_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ : ℝ) (Hcap : ℕ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq_gk K R M Braw →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hpars⟩ := parseval_insert_budget_door
  obtain ⟨ε, Kb, δ₀, Hcap, hε, hKb, hδ₀, hexit⟩ := m4_exit_socket_split_sq_arc_hloCap
  refine ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hε, hKb, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hexit U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  -- ⟦the door's own scales, off the regime⟧
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
  · -- ⟦THE FUSE⟧ the insert budget, from the Parseval stone, in W4's own spelling
    intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (Adoor M) (s13GK K M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · -- ⟦the budget line⟧ `l2_budget_line`, then the `H`-uniform ceiling on the socket leg
    intro H hlo hhi
    rw [l2_budget_line Kb (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * Kb * Braw H ≤ 2 * Kb * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

/-- `m4_second_road_L2_hloCap` (:188), at the lever. -/
theorem m4_second_road_L2_hloCap_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ : ℝ) (Hcap : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
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
  obtain ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hε, hKb, hδ₀, hmain⟩ :=
    m4_doorL2_close_split_sq_hloCap_gk K
  refine ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hε, hKb, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  -- ⟦the window floor, read at the two powers the chain spends⟧
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
  -- ⟦the blocked block mean square⟧
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummed_gk K (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  -- ⟦the cover, then the socket⟧
  have hcov := m4_cover_assembly_blk2_gk K hgates hBblk0 hblk2
  refine hR Braw Bceil δ M k hgates hBraw0 ?_ hceil hbudget
  refine m4_sievedDoorSq_of_blk2_gk K (ℓ := blockLen)
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

/-- `m4_doorL2_close_split_sq_hloCap_pinned` (:320), at the lever. -/
theorem m4_doorL2_close_split_sq_hloCap_pinned_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ : ℝ) (Hcap : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq_gk K R M Braw →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  obtain ⟨ε, Kb, δ₀, Hcap, hε, hKb, hδ₀, hεpin, hδpin, hexit⟩ :=
    m4_exit_socket_split_sq_arc_hloCap_pinned
  refine ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hexit U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  -- ⟦the door's own scales, off the regime⟧
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
  · -- ⟦THE FUSE⟧ the insert budget, from the Parseval stone, in W4's own spelling
    intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (Adoor M) (s13GK K M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · -- ⟦the budget line⟧ `l2_budget_line`, then the `H`-uniform ceiling on the socket leg
    intro H hlo hhi
    rw [l2_budget_line Kb (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * Kb * Braw H ≤ 2 * Kb * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

/-- `m4_second_road_L2_hloCap_pinned` (:394), at the lever. -/
theorem m4_second_road_L2_hloCap_pinned_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ : ℝ) (Hcap : ℕ),
      1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧ 0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
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
  obtain ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, hmain⟩ :=
    m4_doorL2_close_split_sq_hloCap_pinned_gk K
  refine ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  -- ⟦the window floor, read at the two powers the chain spends⟧
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
  -- ⟦the blocked block mean square⟧
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummed_gk K (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  -- ⟦the cover, then the socket⟧
  have hcov := m4_cover_assembly_blk2_gk K hgates hBblk0 hblk2
  refine hR Braw Bceil δ M k hgates hBraw0 ?_ hceil hbudget
  refine m4_sievedDoorSq_of_blk2_gk K (ℓ := blockLen)
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

end Salt.MR

end

-- #audit (temporary)
