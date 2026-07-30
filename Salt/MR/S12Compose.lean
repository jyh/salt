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

/-!
# ⟦S12⟧ — THE ROAD-THREADING TWIN AT THE `L²` DOOR, AND THE COMPOSE

Two stages, both PURELY ADDITIVE (no landed declaration is touched anywhere in this file).

## §1 — the road-threading twin (`m4_second_road_L2`)

`S11Thread.m4_second_road_tower` threads `M4SecondRoad.m4_second_road`'s eleven-item census
onto the `L¹` exit `M4Close.m4_door_contradiction_of_live_split`.  §1 is its `L²` twin: the
SAME eleven items, the SAME four named suppliers

* `M4ChiSummed.m4_chiSummedN_supplied` (items 3–8 + ⟦item 11⟧),
* `M4SecondRoad.m4_blockMeanSqBlk2_of_chiSummed` (the blocked block mean square),
* `M4SecondRoad.m4_cover_assembly_blk2` (the cover),
* `M4SecondRoad.m4_sievedDoorSq_of_blk2` (the socket),

fired against `M4DoorL2.m4_doorL2_close_split_sq` instead.  Exactly two edits to the register:

* the grade-gate read `M4GradeGateSplit R δ₀ δ Braw k` is REPLACED by the pair
  `Braw H ≤ Bceil` (⟦THE NEW SLOT⟧ — the `H`-uniform ceiling that makes the door's grade
  `H`-free) and the budget line `2·K·Bceil + δ/2 + 8·2^k/x ≤ δ₀`;
* the tower conjunct is carried at the `S0-TOWER` exponent `9/2`
  (`S11Exit45.tower_conjunct_45_le_five` is the free downgrade for a `^5` consumer).

⟦THE FOUR LOG SCALES⟧ untouched: `log H` (the strata/socket scale), `log ω` (inside
`M4DoorGates` only), `log x` (only through `2^k/x`), `log log H` (the band floor).

## §2 — the compose (`logChowla2_capstone_conditional`)

§1's road is fired against the `A4` terminal `S11Hoist.m4_socket_discharged_capwired_ws_hoisted`
at ⟦A1 THE BINDER SPLIT⟧'s **two thresholds, never unified**:

* `δ_sock := √(δ₀/(16·K))` — the SOCKET-CEILING side.  The terminal's `∀`-bound `δ₀` slot is
  instantiated HERE and only here; its `ρ` is `doorRhoOfDelta δ_sock`.
* `δ₀` — the GLUE side, the spine's own `K`-FREE threshold, which is what
  `M4DoorGates.hMδ` (`24·Cg/δ ≤ M`) reads and the only threshold the `b`-floor ledger sees.

Unifying them costs `√K` in the `M`-floor (`M4DoorL2.m4_doorL2_binder_floor_unified`): the
kernel record of the 324-bit blow-up stands guard over this file.

⟦THE SHARE TABLE⟧ (the banked amendment, `flags.md` 2026-07-30 14:16 — **NOT** `M4DoorL2`
§3/§4's table, which prices a different target): glue `δ := δ₀` (share `1/2`, entering as
`δ/2`), socket `Bceil := δ₀/(8·K)` (share `1/4`, entering as `2·K·Bceil`), endpoint
`8·2^k/x ≤ δ₀/4` (share `1/4`).  The three sum to `δ₀` EXACTLY, which is the budget line.

The socket ceiling is `Bceil = 2·δ_sock²`: one `δ_sock²` for the terminal's own ceiling
conjunct and one for the graded price's `H`-decaying head (`M4Maximal.m4SmallGradeFits`'s
object), which is why `δ_sock² = δ₀/(16K)` rather than `δ₀/(8K)`.

What §2 DISCHARGES from landed suppliers, and what it CARRIES, is enumerated field by field
in `logChowla2_capstone_conditional`'s own docstring.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE ROAD-THREADING TWIN AT THE `L²` DOOR -/

/-- **⟦THE SECOND ROAD'S TERMINAL REGISTER, AT THE `L²` DOOR⟧** (`m4_second_road_L2`).

`S11Thread.m4_second_road_tower` with the `L¹` exit replaced by
`M4DoorL2.m4_doorL2_close_split_sq`.  THE ELEVEN-ITEM CENSUS, unchanged item for item:

1. `M4DoorGates Cg R M k δ` — the door-glue bundle (`M4Close`'s own list, UNCHANGED);
2. `1 ≤ M`;
3. the three envelope nonnegativities `0 ≤ RSan`, `0 ≤ RStr`, `0 ≤ Braw`;
4. `RS j H ≤ RSan H` at `j₀ ≤ j` — the analytic envelope read;
5. ⟦G1⟧ `arcDen 12 H ^ 7 ≤ RStr H`;
6. ⟦G2⟧ `44·RSan H + 87·arcDen 12 H ≤ (4/3)^{j₀}`;
7. the arc floor `128·arcDen 12 H ^ 3 ≤ H` (`S11Arc36.arc36_of_regime` is its supplier);
8. the block-drift gate `arcDen 12 H < 𝒫₁`;
9. the drift price `96(1+2π)²·strataResidual H²·m4BclGraded j₀ (2RSan) (2RStr) H ≤ Braw H`;
10. ⟦REPLACED⟧ the `H`-uniform ceiling `Braw H ≤ Bceil` **and** the budget line
    `2·K·Bceil + δ/2 + 8·2^k/x ≤ δ₀` — where `M4GradeGateSplit R δ₀ δ Braw k` stood.  `K`
    multiplies the socket leg ONLY; the glue `δ` is `K`-FREE;
11. `M4ChiSummedFreeRow R M RS` — the analytic slot, carried.

⟦WHAT IS GONE⟧ relative to the `L¹` twin: the `√` on the socket grade (the Cauchy–Schwarz
descent of `m4_hbd_of_live` is deleted on the `L²` route), and with it `mrtDeliveredGrade`.

The proof is `m4_second_road_tower`'s, byte for byte, with its final `hR` application
re-plumbed onto the `L²` register. -/
theorem m4_second_road_L2 :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
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
  obtain ⟨Cg, ε, K, δ₀, hCg, hε, hK, hδ₀, hmain⟩ := m4_doorL2_close_split_sq
  refine ⟨Cg, ε, K, δ₀, hCg, hε, hK, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, ?_⟩
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

/-! ## §2 — THE COMPOSE

The two floors the compose can place FOR the consumer are absorbed into the road's `U1floor`
slot exactly as `S11ExitL2.m4_exit_socket_split_sq_arc` absorbs its two: the arc floor
`arcFloor36` (⟦gate 7⟧, `S11Arc36`) and the register's `H`-floor `loglogFloor50`
(`50 ≤ loglog H`, the terminal's `hHreg`).  Both are pure `R.Hlo` floors, so a `max` in the
call site discharges them and the consumer's own `U1floor` survives. -/

/-- **THE REGISTER'S `H`-FLOOR AS A NUMERAL** (`loglogFloor50`) — `⌈exp(exp 50)⌉₊`, the
window length past which `50 ≤ loglog H`.  The terminal's `hHreg` is an `R.Hlo` floor and
nothing else, so it is absorbable into the road's `U1floor`. -/
def loglogFloor50 : ℕ := ⌈Real.exp (Real.exp 50)⌉₊

/-- **⟦THE `hHreg` FLOOR, DISCHARGED⟧** (`regime_Hfloor_of_loglogFloor50`) — the socket
terminals' register hypothesis `0 ≤ log H ∧ 50 ≤ loglog H` at every window length past
`loglogFloor50`. -/
theorem regime_Hfloor_of_loglogFloor50 {H : ℕ} (hH : loglogFloor50 ≤ H) :
    0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) := by
  have hceil : Real.exp (Real.exp 50) ≤ ((loglogFloor50 : ℕ) : ℝ) := Nat.le_ceil _
  have hHR : ((loglogFloor50 : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have h1 : Real.exp (Real.exp 50) ≤ (H : ℝ) := le_trans hceil hHR
  have hlog : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 50)) h1
    rwa [Real.log_exp] at h
  have hpos : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hlog
  refine ⟨hpos.le, ?_⟩
  have h := Real.log_le_log (Real.exp_pos (50 : ℝ)) hlog
  rwa [Real.log_exp] at h

/-- **⟦A1 — THE SOCKET'S OWN THRESHOLD⟧** (`s12DeltaSock δ₀ K`) — `√(δ₀/(16·K))`, the
threshold at which the `A4` terminal's ceiling conjunct is instantiated.

It is NEVER unified with the glue `δ₀` that `M4DoorGates.hMδ` reads: at the certified
numerals the two sit 79 orders apart, and `M4DoorL2.m4_doorL2_binder_floor_unified` is the
kernel record of what unifying them costs (`√K` in the `M`-floor, `b = 324`, the compose
fails).  The `16` rather than `8` is the graded price's `H`-decaying head — one `δ_sock²` for
the terminal's ceiling conjunct, one for `M4Maximal.m4SmallGradeFits`'s half. -/
def s12DeltaSock (δ₀ K : ℝ) : ℝ := Real.sqrt (δ₀ / (16 * K))

theorem s12DeltaSock_pos {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K) : 0 < s12DeltaSock δ₀ K := by
  unfold s12DeltaSock
  exact Real.sqrt_pos.mpr (by positivity)

theorem s12DeltaSock_sq {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K) :
    s12DeltaSock δ₀ K ^ 2 = δ₀ / (16 * K) := by
  unfold s12DeltaSock
  exact Real.sq_sqrt (by positivity)

/-- **⟦THE CAPSTONE, CONDITIONAL⟧** (`logChowla2_capstone_conditional`) — ¬`logChowla2Fails`
at the spine's own regime, with the residue enumerated.

⟦THE WIRING⟧  `m4_second_road_L2` (§1) supplies the road; `S11Hoist`'s cap-wired terminal
`m4_socket_discharged_capwired_ws_hoisted` supplies ⟦item 11⟧ (`M4ChiSummedFreeRow`), ⟦gate
4⟧'s envelope read, and the socket's ceiling conjunct — the terminal's `∀`-bound `δ₀` slot
instantiated at `δ_sock = s12DeltaSock δ₀ K`, its `ρ` at `doorRhoOfDelta δ_sock` (⟦A1⟧).
THE SHARE TABLE (the banked amendment, NOT `M4DoorL2` §3/§4's): glue `δ := δ₀` (`δ/2`),
socket `Bceil := δ₀/(8K)` (`2·K·Bceil = δ₀/4`), endpoint `≤ δ₀/4`; the three sum to `δ₀`.

⟦WHAT IS DISCHARGED HERE, and by which landed lemma⟧
* ⟦gate 7⟧ the arc floor `128·arcDen 12 H³ ≤ H` — `S11Arc36.arc36_of_regime`, off the
  `arcFloor36` absorbed into `U1floor`;
* the terminal's register floor `0 ≤ log H ∧ 50 ≤ loglog H` — `regime_Hfloor_of_loglogFloor50`,
  off the `loglogFloor50` absorbed into `U1floor`;
* ⟦gate 3⟧ the three envelope nonnegativities — `M4ArithRho.RSanDoorRho_nonneg`,
  `M4SecondRoad.rStrWitness_nonneg`, `M4Maximal.m4BclGraded_nonneg`;
* ⟦gate 4⟧ the envelope read — the terminal's own second conjunct;
* ⟦gate 5⟧ ⟦G1⟧ — `M4SecondRoad.rStrWitness_G1` at the witness `RStr := rStrWitness`;
* ⟦gate 6⟧ ⟦G2⟧ — `M4SecondRoad.g2_of_j0_floor` (through `RSanDoorRho ρ H ≤ 1 ≤ rSanWitness H`,
  `doorRhoOfDelta_le_one` against `strataResidual ≥ 1`);
* ⟦gate 9⟧ the drift price — `le_rfl` at `Braw :=` the drift price itself;
* ⟦gate 10a⟧ the `H`-uniform ceiling — `M4Maximal.m4BclGraded_le_of_fits` composed with the
  terminal's ceiling conjunct (this is where `δ_sock²` is spent, twice);
* ⟦gate 10b⟧ the budget line — the share table, arithmetically;
* ⟦item 11⟧ — the terminal's first conjunct;
* `DoorRowZeroBase.coefWS`, and the two `1`-boundedness demands — `S11CoefWS`'s witness
  (`doorRowZeroBase_coefWS_witness`, `norm_doorPunctCoeffU_le_one`,
  `M4Residue.liouvilleC_norm_le_one`): the row bundle's ONE analytic field is GONE, and its
  `(cU, bU)` are pinned to the puncture family rather than left free.

⟦THE RESIDUE, GROUPED BY KIND⟧  (nothing else is assumed; each is a hypothesis below)

**(A) SPINE ARITHMETIC at the certified working point** (`m = 66`, `λ₋ ∈ [74.198, 83.667]`) —
the four demands that couple `(M, k, R)` and are the S11 spine's own page:
1. `M4DoorGates Cg R M k δ₀` — the door-glue register at the glue threshold (`hMδ`'s
   `24·Cg/δ₀ ≤ M` is the `b`-floor: `b = 65.125`, `m = 66`);
2. `8·2^k/R.x ≤ δ₀/4` — the endpoint share (a pure `g`-lever, `H`-free);
3. the ⟦G2⟧ `j₀`-floor `4·log(263·max 1 (arcDen 12 H)) ≤ doorRowFloor M`;
4. ⟦gate 8⟧ `arcDen 12 H < 𝒫₁` — the socket `M`-cap, the arm that binds above;
5. `m4SmallGradeFits` on the register — the `H ≳ 2^{j₀}` threshold of the graded split.

**(B) THE A4 TERMINAL'S FRAMES**, at every base the socket reaches — `DoorFuseFrame`
(suppliers for two of its eleven fields are landed: `M4SocketDischarge.gP1_at_socketBase`,
`M4ArithZero.gRows_zero_of_gate`), the five NON-`coefWS` fields of `DoorRowZeroBase`, the
`DoorCapErrWS` bundle (`RamErrWS`/`M4CapWire`'s wires), `DoorBandBase` (at the hoisted
`(C', x₀)`), and `DoorArithFrameRho` at `ρ = doorRhoOfDelta δ_sock` (field suppliers:
`M4ArithRho` §7 — `m4_arith_arm_of_gArmRho`, `m4_arith_anchor_of_C1_rho`,
`m4_arith_jfloor_of_anchor_rho`, `m4_arith_M0_window_lower_rho`).

**(C) GENUINELY OPEN** — NOTHING.  The terminal's own analytic slot `MmuChiRate` is
DISCHARGED here from `PortClose.mmuChiRate_holds_gated` (the port's landed centerpiece, which
carries no hypotheses); `Aexp` is a free saving PARAMETER of the band, not an open statement.

⟦THE FOUR LOG SCALES⟧ stay apart, and the ⟦TWO THRESHOLDS⟧ `δ₀` (glue) and `δ_sock` (socket)
are never unified. -/
theorem logChowla2_capstone_conditional (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ Ct Cq cs T₀ Kq Ks : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp → ∀ (M : ℕ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
              ∀ (C₁ M₀ epsf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                -- ⟦A⟧ THE SPINE ARITHMETIC
                M4DoorGates Cg R M k δ₀ →
                8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloor M : ℕ) : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  m4SmallGradeFits (doorRowFloor M)
                    (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ K)) H)
                    (fun H => 2 * rStrWitness H) H) →
                -- ⟦B⟧ THE A4 TERMINAL'S FRAMES
                (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                  DoorFuseFrame M (A + s) j Ct Cp (epsf (A + s))) →
                (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                  calQK (Adoor M) (3072 * M) M 2 ≤ A + s ∧
                    Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
                        ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                    (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                    (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                    ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                  ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                    2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                    5 ≤ Real.log (Real.log (2 * T)) →
                    ∃ (Xd P Q Mr Jb : ℕ) (b cf : ℕ → ℂ)
                      (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
                      DoorCapErrWS M (A + s) q Xd P Q b cf (2 * T) E Mtail
                        ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                              ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                                (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU M)))
                                (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                            → DoorCapBase Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf (2 * T)
                                VJ V Lr η εd (epsf (A + s)) Rbd CR KS E EP2)) →
                (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                  DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                  DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                    (doorRhoOfDelta (s12DeltaSock δ₀ K))) →
                  ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, hCg, hε, hK, hδ₀, hroad⟩ := m4_second_road_L2
  obtain ⟨Ct, Cq, cs, T₀, Kq, Ks, hCt, hCq, hcs, hT₀, hKq, hKs, hterm⟩ :=
    m4_socket_discharged_capwired_ws_hoisted mmuChiRate_holds_gated Aexp hAexp
  refine ⟨Cg, ε, K, δ₀, Ct, Cq, cs, T₀, Kq, Ks, hCg, hε, hK, hδ₀, hCt, hCq, hcs, hT₀, hKq,
    hKs, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', x₀, hC'pos, hsockterm⟩ := hterm Cp hCp M hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, ?_⟩
  intro C₁ M₀ epsf Kf k hgates hend hj0 hdgate hfit hframe hbase5 hcapWS hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ K with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hK
  have hδssq : δs ^ 2 = δ₀ / (16 * K) := s12DeltaSock_sq hδ₀ hK
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorRowZeroBase M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦THE A4 TERMINAL⟧ fired at `δ_sock`
  obtain ⟨hrow, hgate4, hceilconj⟩ := hsockterm R C₁ M₀ epsf liouvilleC
    (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M))
      (calQK (Adoor M) (3072 * M) M) 2 i liouvilleC) Kf δs hδs hHreg
    (fun i m => norm_doorPunctCoeffU_le_one M i m) (fun p => liouvilleC_norm_le_one p)
    hframe hbase hcapWS hbandbase harith
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * K))
    (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloor M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloor M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H; simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H; simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
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
    have hG := g2_of_j0_floor H (j₀ := doorRowFloor M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloor M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
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
    have hKpos : (0 : ℝ) < 16 * K := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * K) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * K * (δ₀ / (8 * K)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

/-! ## §3 — ⟦KNOT-1 ARITY SURGERY⟧ the capstone-conditional at the PER-BLOCK range cap

⟦THE RATIFIED STATEMENT CHANGE⟧  This is the ONE place where the KNOT-1 surgery alters a
statement rather than adding beside one: the residue's `hcapWS` slot binds `Mr : ℕ → ℕ`
instead of `Mr : ℕ`.  Iron rule 1 forbids weakening a blueprint statement to make a proof go
through — this is not that: `Mr` is OUR OWN existential inside OUR OWN residue, the conclusion
`¬ logChowla2Fails R.eps R.x R.ω` is untouched, and the change makes the residue STRICTLY
HARDER to satisfy in no direction and strictly easier in exactly one (a constant family is
still admissible, so every model of the landed residue that fixes `Mr` remains a model).

**THE GRANT**: JYH, 2026-07-30 16:02 PDT — "BOTH RATIFIED (JYH) — the KNOT-1 sequence (the
binder ruling GRANTED, refuter → surgery)", recorded in `docs/blueprints/flags.md` after
KNOT1-SCOPE's finding that the scalar `Mr` — not any analytic obstruction — was what forced
the ram-block band to a point (`range`@bottom vs `Mr_sharp`@top ⟹ `Q ≤ 2P`, three lines).

Everything else in the statement and the proof is VERBATIM §2. -/

/-- **⟦THE CAPSTONE, CONDITIONAL, PER-BLOCK⟧** (`logChowla2_capstone_conditional_perBlock`).
§2 with the `hcapWS` residue's range-cap binder at type `ℕ → ℕ` (the ONE ratified statement
change of the KNOT-1 arity surgery — see §3's header for the grant) and
`M4CapWire.DoorCapBasePerBlock` in place of `DoorCapBase`.  The conclusion, the four other
frame families, the spine arithmetic, the share table and the ten gate discharges are
byte-identical to §2. -/
theorem logChowla2_capstone_conditional_perBlock (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ Ct Cq cs T₀ Kq Ks : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp → ∀ (M : ℕ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
              ∀ (C₁ M₀ epsf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                -- ⟦A⟧ THE SPINE ARITHMETIC
                M4DoorGates Cg R M k δ₀ →
                8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloor M : ℕ) : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  m4SmallGradeFits (doorRowFloor M)
                    (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ K)) H)
                    (fun H => 2 * rStrWitness H) H) →
                -- ⟦B⟧ THE A4 TERMINAL'S FRAMES
                (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                  DoorFuseFrame M (A + s) j Ct Cp (epsf (A + s))) →
                (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                  calQK (Adoor M) (3072 * M) M 2 ≤ A + s ∧
                    Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
                        ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                    (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                    (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                    ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                  ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                    2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                    5 ≤ Real.log (Real.log (2 * T)) →
                    ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
                      (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
                      DoorCapErrWS M (A + s) q Xd P Q b cf (2 * T) E Mtail
                        ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                              ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                                (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU M)))
                                (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                            → DoorCapBasePerBlock Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                                (2 * T) VJ V Lr η εd (epsf (A + s)) Rbd CR KS E EP2)) →
                (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                  DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                  DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                    (doorRhoOfDelta (s12DeltaSock δ₀ K))) →
                  ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, hCg, hε, hK, hδ₀, hroad⟩ := m4_second_road_L2
  obtain ⟨Ct, Cq, cs, T₀, Kq, Ks, hCt, hCq, hcs, hT₀, hKq, hKs, hterm⟩ :=
    m4_socket_discharged_capwired_ws_hoisted_perBlock mmuChiRate_holds_gated Aexp hAexp
  refine ⟨Cg, ε, K, δ₀, Ct, Cq, cs, T₀, Kq, Ks, hCg, hε, hK, hδ₀, hCt, hCq, hcs, hT₀, hKq,
    hKs, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', x₀, hC'pos, hsockterm⟩ := hterm Cp hCp M hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, ?_⟩
  intro C₁ M₀ epsf Kf k hgates hend hj0 hdgate hfit hframe hbase5 hcapWS hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ K with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hK
  have hδssq : δs ^ 2 = δ₀ / (16 * K) := s12DeltaSock_sq hδ₀ hK
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorRowZeroBase M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦THE A4 TERMINAL⟧ fired at `δ_sock`
  obtain ⟨hrow, hgate4, hceilconj⟩ := hsockterm R C₁ M₀ epsf liouvilleC
    (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M))
      (calQK (Adoor M) (3072 * M) M) 2 i liouvilleC) Kf δs hδs hHreg
    (fun i m => norm_doorPunctCoeffU_le_one M i m) (fun p => liouvilleC_norm_le_one p)
    hframe hbase hcapWS hbandbase harith
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * K))
    (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloor M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloor M)
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
    have hG := g2_of_j0_floor H (j₀ := doorRowFloor M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloor M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
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
    have hKpos : (0 : ℝ) < 16 * K := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * K) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * K * (δ₀ / (8 * K)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

end Salt.MR

end
