/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16FlatTerminalLinear
import Salt.MR.HDoorArc
import Salt.MR.HDoorSupply

/-!
# THE SECOND ROAD AT SHIFT `h`, ON THE TERMINAL'S LANE — the `_L_gk` h-family

⟦WHAT THIS FILE SETTLES⟧  The flat road's terminal register
`m4_second_road_L2_gk_flatRoot_L` (`S16FlatTerminalLinear.lean:239`) reads the arc's
denominator cap `arcDen 12 H` in five places and closes at `h = 1`.  The twisted `L²` door
(`HDoorArc`, `HDoorClose`) hands the road `α`'s certified only at the `h`-inflated allowance
`h · arcDen 12 H`, and its consumer `log_chowla_two_shell_xi_sq_h` (`Theorem23Shell.lean:624`)
takes the door in the shape `MRTUniformityXiL2H h R ρ`.  This file is the register's
h-sibling: every link of the chain

    socket `M4ChiSummedFreeRow_L_gk` → shift block → block mean square (N) → stratified
    block sup → blocked block mean square → cover → the door `M4SievedDoorSq_L_gk`
    → the mint → `MRTUniformityXiL2H h R (…)`

re-stated with the modulus cap `(q : ℝ) ≤ h · arcDen 12 H`, the `α`-cap
`NearRatTight (h · arcDen 12 H) H α`, the drift scale, and the x-scale floor all read at the
inflated cap, and each proof body the landed one with the cap threaded.

⟦THE CAP, WHERE IT IS READ⟧  Three roles: the MODULUS cap (the six predicates and the framed
base), the `α`-cap / drift scale (the door, its blocked forms, the `ℓ`-witness), and the
x-SCALE floor `R.x ≤ 16·ω·(h·arcDen 12 H)·A`.  ⚠️ The third is inflated TOO, against the
signature draft's first reading: the stratified consumer (`m4_freeBlockSup_of_chiSummedH_L_gk`,
step (iii)) derives the χ-summed datum's x-floor at the DILATED base `⌊A/d⌋ − 1` from the
ladder's `R.x ≤ 8·ω·A` and the stratum bound `d ≤ cap`; the `arcDen` of the x-floor is the
largest stratum, i.e. the modulus cap's shadow through the dilation, and it moves with the cap.

⟦THE RESIDUAL⟧  The Gauss strata's harmonic sum `∑_{d ∣ q} 1/d ≤ 1 + log q` is bounded through
`q ≤ h·arcDen` by `strataResidualH h H := 1 + log(h·arcDen 12 H)` and by nothing smaller.  The
grades stay in the BASE residual (`RSanDoorRho`, `RSanDoor` untouched); the two reads of the
residual (the stratified link and the register's drift gate) are at `strataResidualH`, and one
consumer-side ceiling lemma (`m4_arith_rs_ceiling_met_rhoH_two`, §6) pays the `log 2` at
`h = 2` under the LANDED constant `110525` — `strataResidualH 2 H = strataResidual H + log 2`
exactly, and at the ceiling's own floor `50 ≤ loglog H` the ratio² is below `1.00231`.

⟦THE `ℓ`-WITNESS⟧  `blockLenH h H q := max 1 (H / (⌊h·arcDen 12 H⌋₊ + 1))` — the landed
`blockLen ≈ H/arcDen` fails the drift binder `cap·ℓ ≤ q·H` at `q = 1` under cap `2·arcDen`
(`2·arcDen·ℓ ≈ 2H > H`), the exact pinch the `q = 1` repair removed at `h = 1`; the witness
must halve with the cap.

⟦THE REGISTER'S CONCLUSION⟧  DOOR FORM: at shift `h` there is no exit socket and no budget head
(nothing on `main` concludes `¬ logChowlaFails h` for `h ≠ 1`), so the register concludes
`MRTUniformityXiL2H h R (2·Kc·Bceil + δ/2 + 8·2^k/x)` — the mint's shape — whose consumer is
exactly the shell's `hdoor` slot.

⟦NOT IN THIS FILE⟧  The producer population (the `SocketBaseL`-framed hypotheses of
`M4ClosureRepairLinear` and the `S16*` pages), re-quantified over `HDoorSupply.SocketBaseLH h`;
and the six
hops above the register on the terminal path.  Both are the h-fork campaign's next wave.

**PURELY ADDITIVE.**  No landed declaration is touched; `M4SievedDoorSqH` (`HDoorArc`, the base
lane) is neither repaired nor consumed.  `B₅` stays `12` throughout (iron rule 1): the cap that
moves is the ALLOWANCE, never the exponent.  Nothing here bears on twin primes: it is a spelling
of obligations at shift `h`, each conditional exactly where its `h = 1` twin is.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla
open Salt.ExpSum
open G2Scaffold

/-! ## §0 — the inflated cap, read four ways -/

/-- The inflated cap is nonnegative, hypothesis-free (`arcDen_nonneg`). -/
theorem hArcDen_nonneg (h H : ℕ) : 0 ≤ (h : ℝ) * arcDen 12 H :=
  mul_nonneg (Nat.cast_nonneg _) (arcDen_nonneg 12 H)

/-- `arcDen 12 H ≤ h · arcDen 12 H` at `1 ≤ h` — the one-way direction of the inflation. -/
theorem arcDen_le_hArcDen {h : ℕ} (hh : 1 ≤ h) (H : ℕ) :
    arcDen 12 H ≤ (h : ℝ) * arcDen 12 H := by
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have := arcDen_nonneg 12 H
  nlinarith

/-- `1 ≤ h · arcDen 12 H` past the regime's window floor (`one_le_arcDen_of_regime`, inflated). -/
theorem one_le_hArcDen_of_regime {h : ℕ} (hh : 1 ≤ h) {R : ChowlaRegime} {H : ℕ}
    (hlo : R.Hlo ≤ H) : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H :=
  le_trans (one_le_arcDen_of_regime (R := R) hlo) (arcDen_le_hArcDen hh H)

/-- `1 ≤ h · arcDen 12 H` from any admissible modulus — the form the link proofs read, since
the cap binder `0 < q ∧ q ≤ h·arcDen` already forces it (and forces `1 ≤ h`). -/
theorem one_le_hArcDen_of_cap {h q H : ℕ} (hq : 0 < q) (hqQ : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H) :
    (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H :=
  le_trans (by exact_mod_cast hq : (1 : ℝ) ≤ (q : ℝ)) hqQ

/-- The inflated cap being `≥ 1` forces the shift to be positive. -/
theorem one_le_of_hArcDen {h H : ℕ} (h1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H) : 1 ≤ h := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · norm_num at h1
  · exact hpos

/-- `4 ≤ h · arcDen 12 H` past the window floor (`four_le_arcDen_of_regime`, inflated). -/
theorem four_le_hArcDen_of_regime {h : ℕ} (hh : 1 ≤ h) {R : ChowlaRegime} {H : ℕ}
    (hlo : R.Hlo ≤ H) : (4 : ℝ) ≤ (h : ℝ) * arcDen 12 H :=
  le_trans (four_le_arcDen_of_regime (R := R) hlo) (arcDen_le_hArcDen hh H)

/-! ## §1 — root helpers: the residual and the `ℓ`-witness at the inflated cap -/

/-- **THE STRATA RESIDUAL AT THE INFLATED CAP** — `1 + log(h · arcDen 12 H)`.  Read at the
stratified link (§4) and at the register's drift gate (§5); paid at the ceiling (§6). -/
def strataResidualH (h : ℕ) (H : ℕ) : ℝ := 1 + Real.log ((h : ℝ) * arcDen 12 H)

/-- At `h = 1` the inflated residual is the landed one (the compat direction). -/
theorem strataResidualH_one (H : ℕ) : strataResidualH 1 H = strataResidual H := by
  simp only [strataResidualH, strataResidual, Nat.cast_one, one_mul]

/-- `strataResidualH h H = strataResidual H + log h` — EXACTLY; this is what the ceiling
lemma (§6) reads: the inflation costs an additive `log h`, not a factor. -/
theorem strataResidualH_eq {h : ℕ} (hh : 0 < h) {H : ℕ} (hL : 0 < Real.log (H : ℝ)) :
    strataResidualH h H = strataResidual H + Real.log (h : ℝ) := by
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have harc : arcDen 12 H ≠ 0 := by
    unfold arcDen
    exact (Real.rpow_pos_of_pos hL 12).ne'
  rw [strataResidualH, strataResidual, Real.log_mul hh0 harc]
  ring

theorem strataResidualH_nonneg {h H : ℕ} (h1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H) :
    0 ≤ strataResidualH h H := by
  unfold strataResidualH
  have := Real.log_nonneg h1
  linarith

/-- **THE BLOCK LENGTH AT THE INFLATED CAP** — `ℓ H q := max 1 (H / (⌊h·arcDen 12 H⌋₊ + 1))`.

⚠️ WHY A NEW WITNESS AND NOT THE LANDED `blockLen`: at cap `2·arcDen` the landed
`blockLen ≈ H/arcDen` FAILS the drift binder `cap·ℓ ≤ q·H` at `q = 1` (`2·arcDen·ℓ ≈ 2H > H`)
— the exact pinch the `q = 1` repair removed at `h = 1`.  The witness must halve with the cap:
the admissible interval is `[H/cap², H/cap]` and this sits at its top end, where the drift
binder holds at EVERY `q ≥ 1` with the whole factor `q` to spare. -/
def blockLenH (h : ℕ) (H : ℕ) (_q : ℕ) : ℕ := max 1 (H / (⌊(h : ℝ) * arcDen 12 H⌋₊ + 1))

theorem one_le_blockLenH (h H q : ℕ) : 1 ≤ blockLenH h H q := le_max_left _ _

theorem blockLenH_le (h H q : ℕ) (hH : 1 ≤ H) : blockLenH h H q ≤ H := by
  unfold blockLenH
  exact max_le hH (Nat.div_le_self H _)

/-- The floor ceiling `D = ⌊h·arcDen⌋₊ + 1` sits above the inflated cap … -/
theorem hArcDen_lt_floor_succ (h H : ℕ) :
    (h : ℝ) * arcDen 12 H < ((⌊(h : ℝ) * arcDen 12 H⌋₊ + 1 : ℕ) : ℝ) := by
  push_cast
  exact Nat.lt_floor_add_one _

/-- … and below twice it. -/
theorem floor_succ_le_two_mul_h {h H : ℕ} (h1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H) :
    ((⌊(h : ℝ) * arcDen 12 H⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * ((h : ℝ) * arcDen 12 H) := by
  push_cast
  have := Nat.floor_le (le_trans zero_le_one h1)
  linarith

/-- **THE DRIFT BINDER AT THE WITNESS** — `h·arcDen 12 H · ℓ ≤ q·H` for every `q ≥ 1`
(`M4SecondRoad.blockLen_drift` with the cap opaque). -/
theorem blockLenH_drift {h : ℕ} (hh : 1 ≤ h) {R : ChowlaRegime} {H q : ℕ} (hlo : R.Hlo ≤ H)
    (hq : 0 < q) (hgate : 128 * ((h : ℝ) * arcDen 12 H) ^ 2 ≤ (H : ℝ)) :
    (h : ℝ) * arcDen 12 H * ((blockLenH h H q : ℕ) : ℝ) ≤ (q : ℝ) * (H : ℝ) := by
  have harc1 : (1 : ℝ) ≤ ((h : ℝ) * arcDen 12 H) := one_le_hArcDen_of_regime (R := R) hh hlo
  have harc0 : (0 : ℝ) < ((h : ℝ) * arcDen 12 H) := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  have hD := hArcDen_lt_floor_succ h H
  have hkey : ((h : ℝ) * arcDen 12 H) * ((blockLenH h H q : ℕ) : ℝ) ≤ (H : ℝ) := by
    unfold blockLenH
    rcases Nat.eq_zero_or_pos (H / (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1)) with hz | hpos
    · rw [hz, max_eq_left (Nat.zero_le 1)]
      push_cast
      nlinarith
    · rw [max_eq_right hpos]
      have hcast := Nat.cast_div_le (α := ℝ) (m := H) (n := ⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1)
      have hD0 : (0 : ℝ) < ((⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      have hstep : ((h : ℝ) * arcDen 12 H) * ((H / (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1) : ℕ) : ℝ)
          ≤ ((h : ℝ) * arcDen 12 H) * ((H : ℝ) / ((⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcast harc0.le
      have hfrac : ((h : ℝ) * arcDen 12 H) * ((H : ℝ) / ((⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1 : ℕ) : ℝ))
          ≤ (H : ℝ) := by
        rw [mul_div_assoc'] at *
        rw [div_le_iff₀ hD0]
        nlinarith
      linarith
  nlinarith

/-- **THE COUNT BINDER AT THE WITNESS** — `H ≤ (h·arcDen 12 H)² · ℓ`
(`M4SecondRoad.blockLen_narrow` with the cap opaque). -/
theorem blockLenH_narrow {h : ℕ} (hh : 1 ≤ h) {R : ChowlaRegime} {H q : ℕ} (hlo : R.Hlo ≤ H)
    (hgate : 128 * ((h : ℝ) * arcDen 12 H) ^ 2 ≤ (H : ℝ)) :
    (H : ℝ) ≤ ((h : ℝ) * arcDen 12 H) ^ 2 * ((blockLenH h H q : ℕ) : ℝ) := by
  have harc4 : (4 : ℝ) ≤ ((h : ℝ) * arcDen 12 H) := four_le_hArcDen_of_regime (R := R) hh hlo
  have harc0 : (0 : ℝ) < ((h : ℝ) * arcDen 12 H) := by linarith
  have hD2 := floor_succ_le_two_mul_h (h := h) (H := H) (by linarith)
  have hD0 : (0 : ℝ) < ((⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1 : ℕ) : ℝ) := by
    have := hArcDen_lt_floor_succ h H; linarith
  -- ⟦the ℕ-division floor, honestly⟧ `H ≤ D·(H/D) + D ≤ D·ℓ + D`
  have hmod : H ≤ (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1) * (H / (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1))
      + (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1) := by
    have h1 := Nat.div_add_mod H (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1)
    have h2 : H % (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1) < ⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1 :=
      Nat.mod_lt _ (Nat.succ_pos _)
    omega
  have hle : H / (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1) ≤ blockLenH h H q := le_max_right _ _
  have hmulR : (H : ℝ) ≤ ((⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1 : ℕ) : ℝ) * ((blockLenH h H q : ℕ) : ℝ)
      + ((⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1 : ℕ) : ℝ) := by
    have hstep : H ≤ (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1) * (blockLenH h H q) + (⌊((h : ℝ)
        * arcDen 12 H)⌋₊ + 1) := by
      have := Nat.mul_le_mul_left (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1) hle
      omega
    exact_mod_cast hstep
  have hL0 : (0 : ℝ) ≤ ((blockLenH h H q : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦`H ≤ 2·arcDen·(ℓ + 1)`, then the two arc floors⟧
  have hchain : (H : ℝ) ≤ 2 * ((h : ℝ) * arcDen 12 H) * ((blockLenH h H q : ℕ) : ℝ) + 2 * ((h : ℝ)
      * arcDen 12 H) := by
    nlinarith
  nlinarith

/-- **THE ARC FLOOR AT THE WITNESS** — `32·h·arcDen 12 H ≤ ℓ`
(`M4SecondRoad.blockLen_arc_floor` with the cap opaque). -/
theorem blockLenH_arc_floor {h : ℕ} (hh : 1 ≤ h) {R : ChowlaRegime} {H q : ℕ} (hlo : R.Hlo ≤ H)
    (hgate : 128 * ((h : ℝ) * arcDen 12 H) ^ 2 ≤ (H : ℝ)) :
    32 * ((h : ℝ) * arcDen 12 H) ≤ ((blockLenH h H q : ℕ) : ℝ) := by
  have harc4 : (4 : ℝ) ≤ ((h : ℝ) * arcDen 12 H) := four_le_hArcDen_of_regime (R := R) hh hlo
  have harc0 : (0 : ℝ) < ((h : ℝ) * arcDen 12 H) := by linarith
  have hD2 := floor_succ_le_two_mul_h (h := h) (H := H) (by linarith)
  have hD0 : (0 : ℝ) < ((⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1 : ℕ) : ℝ) := by
    have := hArcDen_lt_floor_succ h H; linarith
  have hmod : H ≤ (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1) * (H / (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1))
      + (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1) := by
    have h1 := Nat.div_add_mod H (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1)
    have h2 : H % (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1) < ⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1 :=
      Nat.mod_lt _ (Nat.succ_pos _)
    omega
  have hle : H / (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1) ≤ blockLenH h H q := le_max_right _ _
  have hmulR : (H : ℝ) ≤ ((⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1 : ℕ) : ℝ) * ((blockLenH h H q : ℕ) : ℝ)
      + ((⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1 : ℕ) : ℝ) := by
    have hstep : H ≤ (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1) * (blockLenH h H q) + (⌊((h : ℝ)
        * arcDen 12 H)⌋₊ + 1) := by
      have := Nat.mul_le_mul_left (⌊((h : ℝ) * arcDen 12 H)⌋₊ + 1) hle
      omega
    exact_mod_cast hstep
  have hL0 : (0 : ℝ) ≤ ((blockLenH h H q : ℕ) : ℝ) := Nat.cast_nonneg _
  have hchain : (H : ℝ) ≤ 2 * ((h : ℝ) * arcDen 12 H) * ((blockLenH h H q : ℕ) : ℝ) + 2 * ((h : ℝ)
      * arcDen 12 H) := by
    nlinarith
  nlinarith

/-! ## §1′ — the blocked drift at an OPAQUE cap (the helm's RESPELL of the rpow identity)

`M4BridgeBlock.lean:222/268/300` read `arcDen B₅ H` as an opaque nonnegative real; the three
siblings below take that real as a binder `Q`, so the drift lemmas fire at `Q := h · arcDen 12 H`
with no rpow identity and no pin to `h = 2`.  Proof bodies verbatim. -/

/-- `M4BridgeBlock.abs_mul_window_le_of_arcDen_block`, cap opaque. -/
theorem abs_mul_window_le_of_cap_block {Q : ℝ} {H q ℓ : ℕ} (hq : 0 < q) (hH : 0 < H)
    {θ : ℝ} (hθ : |θ| ≤ Q / ((q : ℝ) * (H : ℝ)))
    (hadm : Q * (ℓ : ℝ) ≤ (q : ℝ) * (H : ℝ)) :
    |θ| * (ℓ : ℝ) ≤ 1 := by
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqH : (0 : ℝ) < (q : ℝ) * (H : ℝ) := mul_pos hqR hHR
  have hℓ0 : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
  have h1 : |θ| * (ℓ : ℝ) ≤ Q / ((q : ℝ) * (H : ℝ)) * (ℓ : ℝ) :=
    mul_le_mul_of_nonneg_right hθ hℓ0
  have h2 : Q / ((q : ℝ) * (H : ℝ)) * (ℓ : ℝ) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hqH]
    exact hadm
  linarith

/-- `M4BridgeBlock.norm_absWindowSum_le_drift_blocked`, cap opaque. -/
theorem norm_absWindowSum_le_drift_blocked_Q {Q : ℝ} {H q n ℓ : ℕ} (hq : 0 < q) (hH : 0 < H)
    (hℓ : 0 < ℓ) {β θ : ℝ} (hθ : |θ| ≤ Q / ((q : ℝ) * (H : ℝ)))
    (hadm : Q * (ℓ : ℝ) ≤ (q : ℝ) * (H : ℝ)) (a : ℕ → ℂ) :
    ‖absWindowSum a H n (β + θ)‖
      ≤ (1 + 2 * Real.pi)
          * ∑ m ∈ Finset.range (numBlocks H ℓ), subWindowSup a ℓ (n + m * ℓ) β := by
  have hdrift := abs_mul_window_le_of_cap_block (Q := Q) (ℓ := ℓ) hq hH hθ hadm
  -- ⟦the window, cut into blocks⟧
  have hchunk : absWindowSum a H n (β + θ)
      = ∑ m ∈ Finset.range (numBlocks H ℓ),
          ∑ j ∈ Finset.Ioc (blockCut n H ℓ m) (blockCut n H ℓ (m + 1)),
            eR (θ * (j : ℝ)) * phaseCoeff a β j := by
    rw [absWindowSum_add_eq_phase_sum,
      sum_Ioc_chunk (fun j => eR (θ * (j : ℝ)) * phaseCoeff a β j) (blockCut_mono n H ℓ)
        (numBlocks H ℓ), blockCut_zero, blockCut_numBlocks hℓ]
  rw [hchunk]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  have hmlt := Finset.mem_range.mp hm
  have hbase : blockCut n H ℓ m = n + m * ℓ := blockCut_eq_of_lt hmlt
  have hle : blockCut n H ℓ m ≤ blockCut n H ℓ (m + 1) := blockCut_mono n H ℓ (Nat.le_succ m)
  have h := norm_block_phase_sum_le (ℓ := ℓ) hle (blockCut_succ_sub_le n H ℓ m) hdrift a β
  rw [hbase] at h
  rw [hbase]
  exact h

/-- `M4BridgeBlock.norm_absWindowSum_sq_le_drift_blocked`, cap opaque. -/
theorem norm_absWindowSum_sq_le_drift_blocked_Q {Q : ℝ} {H q n ℓ : ℕ} (hq : 0 < q) (hH : 0 < H)
    (hℓ : 0 < ℓ) {β θ : ℝ} (hθ : |θ| ≤ Q / ((q : ℝ) * (H : ℝ)))
    (hadm : Q * (ℓ : ℝ) ≤ (q : ℝ) * (H : ℝ)) (a : ℕ → ℂ) :
    ‖absWindowSum a H n (β + θ)‖ ^ 2
      ≤ (1 + 2 * Real.pi) ^ 2 * (numBlocks H ℓ : ℝ)
          * ∑ m ∈ Finset.range (numBlocks H ℓ), (subWindowSup a ℓ (n + m * ℓ) β) ^ 2 := by
  have hlin := norm_absWindowSum_le_drift_blocked_Q (Q := Q) (n := n) (β := β) (θ := θ)
    hq hH hℓ hθ hadm a
  have hS0 : (0 : ℝ) ≤ ∑ m ∈ Finset.range (numBlocks H ℓ), subWindowSup a ℓ (n + m * ℓ) β :=
    Finset.sum_nonneg fun m _ => subWindowSup_nonneg a ℓ (n + m * ℓ) β
  have hpi : (0 : ℝ) ≤ 1 + 2 * Real.pi := by positivity
  have hsq : ‖absWindowSum a H n (β + θ)‖ ^ 2
      ≤ (1 + 2 * Real.pi) ^ 2
          * (∑ m ∈ Finset.range (numBlocks H ℓ), subWindowSup a ℓ (n + m * ℓ) β) ^ 2 := by
    have hnn := norm_nonneg (absWindowSum a H n (β + θ))
    nlinarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (numBlocks H ℓ))
    (f := fun m => subWindowSup a ℓ (n + m * ℓ) β)
  rw [Finset.card_range] at hcs
  nlinarith [Finset.sum_nonneg (f := fun m => (subWindowSup a ℓ (n + m * ℓ) β) ^ 2)
    (s := Finset.range (numBlocks H ℓ)) (fun m _ => sq_nonneg _), sq_nonneg (1 + 2 * Real.pi)]

/-! ## §2 — the predicates at the inflated cap (statement-tier)

Naming: `<Name>H_L_gk (h K : ℕ) …` — the `h`-binder EXPLICIT and FIRST, `2` supplied by the
consumer.  Bodies byte-identical to their `M4RowLinear` / `M4RowSpineLinear` / `M4LadderLinear`
twins except the cap: modulus `(q : ℝ) ≤ h · arcDen 12 H`, the narrowing/count binders at the
inflated cap, the x-scale floor `R.x ≤ 16·ω·(h·arcDen 12 H)·A` (see the header), the φ(q)-ledger
count `8·(h·arcDen)`. -/

/-- **THE DEBT LINE, ON THE TERMINAL'S LANE** — `M4ChiSummedFreeRow_L_gk`
(`M4RowLinear.lean:8002`) with the modulus cap `(q : ℝ) ≤ h · arcDen 12 H` and the x-scale
floor at `16·ω·(h·arcDen 12 H)·A`. -/
def M4ChiSummedFreeRowH_L_gk (h K : ℕ) (R : ChowlaRegime) (M : ℕ) (RS : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ (h : ℝ) * arcDen 12 H → ∀ j ≤ Nat.log 2 L, ∀ A : ℕ, 0 < A →
      2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * ((h : ℝ) * arcDen 12 H) * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      ∀ s ≤ L,
        ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s) ≤ RS j H

/-- `M4ChiSummedFreeShiftBlock_L_gk` (`M4RowLinear.lean:8139`) at the inflated cap; the
`8·arcDen` is the φ(q)-ledger's character count and inflates with the cap. -/
def M4ChiSummedFreeShiftBlockH_L_gk (h K : ℕ) (R : ChowlaRegime) (M : ℕ) (F : ℕ → ℕ → ℝ) :
    Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ (h : ℝ) * arcDen 12 H → ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
      ∀ A B : ℕ, 0 < A → 2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * ((h : ℝ) * arcDen 12 H) * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      4 ≤ L → B + L ≤ 2 * A + 4 →
        ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc (A + s) (B + s),
            ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + (2 * F j H + 8 * ((h : ℝ) * arcDen 12 H)) * ((2 ^ j : ℕ) : ℝ) ^ 2

/-- `M4ChiSummedBlockMeanSqN_L_gk` (`M4RowLinear.lean:8211`) at the inflated cap; the
NARROWING `H ≤ cap³·L` is the count binder at the cap and inflates. -/
def M4ChiSummedBlockMeanSqNH_L_gk (h K : ℕ) (R : ChowlaRegime) (M : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H →
    (H : ℝ) ≤ ((h : ℝ) * arcDen 12 H) ^ 3 * (L : ℝ) →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
      ∀ A B : ℕ, 0 < A → L ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * ((h : ℝ) * arcDen 12 H) * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      B + L ≤ 2 * A + 4 →
        ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
          ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

/-- `M4BlockMeanSqBlk2_L_gk` (`M4RowSpineLinear.lean:665`) at the inflated cap. -/
def M4BlockMeanSqBlk2H_L_gk (h K : ℕ) (R : ChowlaRegime) (M k : ℕ) (ℓ : ℕ → ℕ → ℕ)
    (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
    (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
    1 ≤ ℓ H q → ℓ H q ≤ H → (H : ℝ) ≤ ((h : ℝ) * arcDen 12 H) ^ 2 * (ℓ H q : ℝ) →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          blockSupSq (doorSievedCoeff_L_gk K M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
        ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2
            * (doorLadder R.x H (i + 1) : ℝ)

/-- `M4SievedDoorSqBlk2_L_gk` (`M4RowSpineLinear.lean:584`) at the inflated cap. -/
def M4SievedDoorSqBlk2H_L_gk (h K : ℕ) (R : ChowlaRegime) (M : ℕ) (ℓ : ℕ → ℕ → ℕ)
    (Bblk : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
      (q : ℝ) ≤ (h : ℝ) * arcDen 12 H → 1 ≤ ℓ H q → ℓ H q ≤ H →
      (H : ℝ) ≤ ((h : ℝ) * arcDen 12 H) ^ 2 * (ℓ H q : ℝ) →
        (∫ n, blockSupSq (doorSievedCoeff_L_gk K M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
            ∂(logMeasure R.x R.ω))
          ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2

/-- **THE DOOR AT THE INFLATED CAP, ON THE TERMINAL'S LANE** — `M4SievedDoorSq_L_gk`
(`M4LadderLinear.lean:961`) with the `α`-binder at `NearRatTight ((h:ℝ) * arcDen 12 H) H α`.
This is the object the base-lane `M4SievedDoorSqH` (`HDoorArc.lean:441`) is the wrong-lane
twin of; that one is left alone. -/
def M4SievedDoorSqH_L_gk (h K : ℕ) (R : ChowlaRegime) (M : ℕ) (Braw : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight ((h : ℝ) * arcDen 12 H) H α →
        (∫ n, ‖absWindowSum (memSCoeff (calP (AdoorL M) (s13GK K M))
              (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H n α‖ ^ 2
            ∂(logMeasure R.x R.ω))
          ≤ Braw H * (H : ℝ) ^ 2

/-- The compat arm (anti-drift): the door at `h ≥ 1` implies the landed door
(`nearRatTight_mono`, `arcDen ≤ h·arcDen`). -/
theorem m4_sievedDoorSq_L_gk_of_H {h : ℕ} (hh : 1 ≤ h) {K : ℕ} {R : ChowlaRegime} {M : ℕ}
    {Braw : ℕ → ℝ} (hd : M4SievedDoorSqH_L_gk h K R M Braw) : M4SievedDoorSq_L_gk K R M Braw := by
  intro htr H _ hlo hhi α hα
  exact hd htr H hlo hhi α (nearRatTight_mono (arcDen_le_hArcDen hh H) hα)

/-! ## §3 — the link theorems, socket → door (transcription, the cap threaded) -/

/-- **3.1 ANTI-VACUITY at the inflated cap** — the trivial witness is `4·h·arcDen`
(`φ(q) ≤ q ≤ h·arcDen`, absolute grade `4`); `M4RowLinear.lean:8011`. -/
theorem m4_chiSummedFreeRow_trivialH_L_gk (h K : ℕ) (R : ChowlaRegime) (M : ℕ) :
    M4ChiSummedFreeRowH_L_gk h K R M (fun _ H => 4 * ((h : ℝ) * arcDen 12 H)) := by
  intro H _ _ L _ q hq hqQ j _ A hA _ _ _ _ s _
  haveI : NeZero q := ⟨hq.ne'⟩
  have hAs : 0 < A + s := by omega
  have hterm : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      chiFreeRowSq_L_gk K χ M j (A + s) ≤ 4 := fun χ _ => chiFreeRowSq_le_four_L_gk K χ M j hAs
  have hsum : ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s)
      ≤ ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ) * 4 := by
    calc ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s)
        ≤ ∑ _χ : DirichletCharacter ℂ q, (4 : ℝ) := Finset.sum_le_sum hterm
      _ = ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ) * 4 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_dirichletCharacter_nat q] at hsum
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  linarith

/-- **3.2** `m4_chiSummedShiftBlock_of_freeRow_L_gk` (`M4RowLinear.lean:8151`), the cap
threaded. -/
theorem m4_chiSummedShiftBlock_of_freeRowH_L_gk (h K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {RS : ℕ → ℕ → ℝ} (hrow : M4ChiSummedFreeRowH_L_gk h K R M RS) :
    M4ChiSummedFreeShiftBlockH_L_gk h K R M (fun j H => 2 * RS j H) := by
  intro H hlo hhi L hLH q hq hqQ j hjL s hsL A B hA hAj hAsq hAx hAcap hL4 hfit
  haveI : NeZero q := ⟨hq.ne'⟩
  have hAs : 0 < A + s := by omega
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  -- ⟦the pointwise bound at each character's OWN row datum⟧
  have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      ∑ n ∈ Finset.Ioc (A + s) (B + s),
          ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ 2 * chiFreeRowSq_L_gk K χ M j (A + s) * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (4 * chiFreeRowSq_L_gk K χ M j (A + s) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := fun χ _ =>
    chiFreeShift_pointwise_L_gk K χ M hjL hsL hA hL4 hfit le_rfl
  refine le_trans (Finset.sum_le_sum hper) ?_
  -- ⟦the sum splits into the row sum and the absolute residue⟧
  have hsplit : ∑ χ : DirichletCharacter ℂ q,
      (2 * chiFreeRowSq_L_gk K χ M j (A + s) * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (4 * chiFreeRowSq_L_gk K χ M j (A + s) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2)
      = (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s))
          * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
        + ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ)
            * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
    calc ∑ χ : DirichletCharacter ℂ q,
          (2 * chiFreeRowSq_L_gk K χ M j (A + s) * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + (4 * chiFreeRowSq_L_gk K χ M j (A + s) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2)
        = ∑ χ : DirichletCharacter ℂ q,
            (chiFreeRowSq_L_gk K χ M j (A + s)
                * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
              + 8 * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
          Finset.sum_congr rfl fun χ _ => by ring
      _ = (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s)
              * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2))
            + ∑ _χ : DirichletCharacter ℂ q, 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
          Finset.sum_add_distrib
      _ = (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s))
            * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
          + ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ)
              * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
          rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsplit, card_dirichletCharacter_nat q]
  have hrowsum := hrow H hlo hhi L hLH q hq hqQ j hjL A hA hAj hAsq hAx hAcap s hsL
  have hrow0 : (0 : ℝ) ≤ ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s) :=
    Finset.sum_nonneg fun χ _ => chiFreeRowSq_nonneg_L_gk K χ M j hAs
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ ((h : ℝ) * arcDen 12 H) := le_trans hφq hqQ
  have hfac0 : (0 : ℝ) ≤ 2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    positivity
  have h1 : (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s))
        * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
      ≤ RS j H * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hrowsum hfac0
  have h2 : (q.totient : ℝ) * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2)
      ≤ ((h : ℝ) * arcDen 12 H) * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
    refine mul_le_mul_of_nonneg_right hφarc ?_
    positivity
  nlinarith [h1, h2]

set_option maxHeartbeats 3200000 in
-- the dyadic assembly is re-elaborated against `∑_χ` as well as the free `(A, B]` and `L` —
-- exactly as at `M4RowLinear.lean:8220` (no tactic search below is unbounded)
/-- **3.3** `m4_chiSummedBlockN_of_shiftBlock_L_gk` (`M4RowLinear.lean:8227`): the φ(q)-ledger's
two constants inflate with the cap (`2·arcDen⁷ → 2·(h·arcDen)⁷`, `432/5·arcDen →
432/5·(h·arcDen)`), the NARROWING gate `8·arcDen³ ≤ H` likewise. -/
theorem m4_chiSummedBlockN_of_shiftBlockH_L_gk (h K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {F : ℕ → ℕ → ℝ} {Fan Ftr : ℕ → ℝ} (j₀ : ℕ)
    (hFan0 : ∀ H : ℕ, 0 ≤ Fan H) (hFtr0 : ∀ H : ℕ, 0 ≤ Ftr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * ((h : ℝ) * arcDen 12 H) ^ 7 ≤ Ftr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      108 / 5 * Fan H + 432 / 5 * ((h : ℝ) * arcDen 12 H) ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ))
    (hfix : M4ChiSummedFreeShiftBlockH_L_gk h K R M F) :
    M4ChiSummedBlockMeanSqNH_L_gk h K R M (m4BclGraded j₀ Fan Ftr) := by
  classical
  intro H hlo hhi L hLH hnar q hq hqQ A B hA hAL hAsq hAx hAcap hfit
  haveI : NeZero q := ⟨hq.ne'⟩
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have harc1 : (1 : ℝ) ≤ ((h : ℝ) * arcDen 12 H) := one_le_hArcDen_of_cap hq hqQ
  have harc0 : (0 : ℝ) < ((h : ℝ) * arcDen 12 H) := by linarith
  have hBcl0 : (0 : ℝ) ≤ m4BclGraded j₀ Fan Ftr H :=
    m4BclGraded_nonneg (hFan0 H) (hFtr0 H)
  -- ⟦THE NARROWING, read against the arc gate: the free length cannot be short⟧
  have harc30 : (0 : ℝ) < ((h : ℝ) * arcDen 12 H) ^ 3 := by positivity
  have hL8R : (8 : ℝ) ≤ (L : ℝ) :=
    le_of_mul_le_mul_left
      (by have := harc8 H hlo hhi; linarith :
        ((h : ℝ) * arcDen 12 H) ^ 3 * 8 ≤ ((h : ℝ) * arcDen 12 H) ^ 3 * (L : ℝ)) harc30
  have hL8 : 8 ≤ L := by exact_mod_cast hL8R
  have hL0 : 0 < L := by omega
  have hL0R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL0
  by_cases hAB : B < A
  · -- ⟦the empty block⟧
    have hzero : ∀ χ : DirichletCharacter ℂ q,
        ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2 = 0 := by
      intro χ
      rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    rw [Finset.sum_congr rfl (fun χ _ => hzero χ), Finset.sum_const, smul_zero]
    exact mul_nonneg (mul_nonneg hBcl0 (sq_nonneg _)) (Nat.cast_nonneg _)
  rw [Nat.not_lt] at hAB
  -- ⟦the non-empty block: the fit's three consequences⟧
  have hA4 : 4 ≤ A := by omega
  have hB2A : B ≤ 2 * A := by omega
  have hL2A : (L : ℝ) ≤ 2 * (A : ℝ) := by
    have hnat : L ≤ 2 * A := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  set Lg := Nat.log 2 L with hLg
  -- ⟦R-P5, THE LENGTH ANTECEDENT PROPAGATED⟧ every dyadic window of the assembly is at most
  -- the free length (`2^j ≤ 2^{log₂L} ≤ L`), so the block's own `L ≤ A` supplies the shifted
  -- family's `2^j ≤ A` at every scale the analytic half reads
  have h2jL : ∀ j : ℕ, j ≤ Lg → 2 ^ j ≤ A := by
    intro j hj
    have h1 : 2 ^ j ≤ 2 ^ Lg := Nat.pow_le_pow_right (by norm_num) hj
    have h2 : 2 ^ Lg ≤ L := by rw [hLg]; exact Nat.pow_log_le_self 2 hL0.ne'
    omega
  set X : DirichletCharacter ℂ q → ℕ → ℕ → ℕ → ℝ := fun χ j t n =>
    ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2 with hX
  set Y : ℕ → ℕ → ℕ → ℝ := fun j t n => ∑ χ : DirichletCharacter ℂ q, X χ j t n with hY
  set SL : ℝ := ∑ j ∈ Finset.range (Lg + 1), (3 / 2 : ℝ) ^ j with hSL
  have hSL0 : (0 : ℝ) ≤ SL := (geom_weight_sum_pos Lg).le
  -- ⟦STEP 1⟧ the pointwise maximal bound per character, with the sums already commuted
  have hchi : ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
        ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
    intro χ
    have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
        ≤ ∑ n ∈ Finset.Ioc A B, SL
            * ∑ j ∈ Finset.range (Lg + 1),
                (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X χ j t n) * (2 / 3 : ℝ) ^ j :=
      Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic_L_gk K χ M L n
    have hswap : ∑ n ∈ Finset.Ioc A B, SL
          * ∑ j ∈ Finset.range (Lg + 1),
              (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X χ j t n) * (2 / 3 : ℝ) ^ j
        = SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul]
      congr 1
      exact Finset.sum_comm
    exact hswap ▸ hstep1
  -- ⟦STEP 1′⟧ the character sum, taken through the assembly
  have hsummed : ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
      ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, Y j t n) * (2 / 3 : ℝ) ^ j := by
    refine le_trans (Finset.sum_le_sum fun χ _ => hchi χ) (le_of_eq ?_)
    calc ∑ χ : DirichletCharacter ℂ q, SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j
        = SL * ∑ χ : DirichletCharacter ℂ q, ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
      _ = SL * ∑ j ∈ Finset.range (Lg + 1), ∑ χ : DirichletCharacter ℂ q,
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
          rw [Finset.sum_comm]
      _ = SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, Y j t n) * (2 / 3 : ℝ) ^ j := by
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_comm]
  -- ⟦STEP 2⟧ each (scale, offset) pair is a shifted fixed-length block sum, summed over χ
  have hsle : ∀ j t : ℕ, t ≤ L / 2 ^ (j + 1) → 2 ^ (j + 1) * t ≤ L := by
    intro j t ht
    calc 2 ^ (j + 1) * t ≤ 2 ^ (j + 1) * (L / 2 ^ (j + 1)) := Nat.mul_le_mul_left _ ht
      _ = L / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_comm _ _
      _ ≤ L := Nat.div_mul_le_self L (2 ^ (j + 1))
  have hshiftY : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, Y j t n
      = ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
            ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2 := by
    intro j t
    rw [hY, Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ _ => ?_
    exact sum_Ioc_shift (fun n => ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2)
      A B _
  -- ⟦the analytic half: the χ-summed datum, read through the envelope⟧
  have hjtL : ∀ j t : ℕ, j ≤ Lg → j₀ ≤ j → t ≤ L / 2 ^ (j + 1) →
      ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H)) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t hjLg hj₀ ht
    rw [hshiftY j t]
    have hd := hfix H hlo hhi L hLH q hq hqQ j hjLg (2 ^ (j + 1) * t) (hsle j t ht) A B hA
      (h2jL j hjLg) hAsq hAx hAcap (by omega) hfit
    have hFle := han j H hj₀
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hP0 hA0R]
  -- ⟦the trivial half: the ABSOLUTE grade `1`, φ(q) times⟧
  have hjtS : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, Y j t n
      ≤ ((h : ℝ) * arcDen 12 H) * (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t
    rw [hshiftY j t]
    have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
        ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
            ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
      intro χ _
      have hterm : ∀ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
          ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
            ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by
        intro n _
        have h := norm_sum_doorSievedWindow_le_L_gk K χ M (2 ^ j) n
        have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ :=
          norm_nonneg _
        nlinarith
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      have hcast : ((B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) : ℕ) : ℝ) ≤ (A : ℝ) := by
        have hnat : B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) ≤ A := by omega
        exact_mod_cast hnat
      have h2j : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
      nlinarith
    have hsum := Finset.sum_le_sum hper
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_dirichletCharacter_nat q] at hsum
    have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
    have hφarc : (q.totient : ℝ) ≤ ((h : ℝ) * arcDen 12 H) := le_trans hφq hqQ
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    have hmid : (q.totient : ℝ) * ((A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2)
        ≤ ((h : ℝ) * arcDen 12 H) * ((A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
      refine mul_le_mul_of_nonneg_right hφarc ?_
      positivity
    nlinarith [hsum, hmid]
  -- ⟦STEP 3⟧ the per-scale count × weight
  set W : ℕ → ℝ := fun j =>
    (((L / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 with hW
  have hW0 : ∀ j, (0 : ℝ) ≤ W j := fun j => dyadic_count_weight_term_nonneg L j
  have hWw0 : ∀ j, (0 : ℝ) ≤ W j * (2 / 3 : ℝ) ^ j := fun j =>
    mul_nonneg (hW0 j) (by positivity)
  have hjL : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H))) * (W j * (2 / 3 : ℝ) ^ j)
            := by
    intro j hjm
    have hjmem := Finset.mem_filter.mp hjm
    have hjLg : j ≤ Lg := by have := Finset.mem_range.mp hjmem.1; omega
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            (Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
              + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H)) * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
      Finset.sum_le_sum fun t ht =>
        hjtL j t hjLg hjmem.2 (by have := Finset.mem_range.mp ht; omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H))) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H))) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H))) * (W j * (2 / 3 : ℝ) ^ j)
          := by
          ring
  have hjS : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (((h : ℝ) * arcDen 12 H) * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j _
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ((h : ℝ) * arcDen 12 H) * (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
      Finset.sum_le_sum fun t _ => hjtS j t
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ (((h : ℝ) * arcDen 12 H) * (A : ℝ)) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((((h : ℝ) * arcDen 12 H) * (A : ℝ)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (((h : ℝ) * arcDen 12 H) * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  -- ⟦STEP 4⟧ THE SPLIT
  have hCan0 : (0 : ℝ) ≤ Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H)) := by
    have := hFan0 H; nlinarith
  have harcA0 : (0 : ℝ) ≤ ((h : ℝ) * arcDen 12 H) * (A : ℝ) := by positivity
  have hlarge : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H)))
          * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H))) * (W j * (2 / 3 : ℝ)
                ^ j) :=
          Finset.sum_le_sum hjL
      _ ≤ ∑ j ∈ Finset.range (Lg + 1),
            (Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H))) * (W j * (2 / 3 : ℝ)
                ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hCan0 (hWw0 j))
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H)))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hsmall : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (((h : ℝ) * arcDen 12 H) * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    have hsub : (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
            (((h : ℝ) * arcDen 12 H) * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := Finset.sum_le_sum hjS
      _ ≤ ∑ j ∈ Finset.range j₀, (((h : ℝ) * arcDen 12 H) * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg harcA0 (hWw0 j))
      _ = (((h : ℝ) * arcDen 12 H) * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hcount : ∑ j ∈ Finset.range (Lg + 1),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H)))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
        + (((h : ℝ) * arcDen 12 H) * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Lg + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧ the two weighted counts, then the mirrored ledger
  have hLgN : Nat.log 2 L ≤ Nat.log 2 H := Nat.log_mono_right hLH
  have hgl1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ Lg := one_le_pow₀ (by norm_num)
  have hglg : (3 / 2 : ℝ) ^ Lg ≤ (3 / 2 : ℝ) ^ (Nat.log 2 H) := by
    rw [hLg]; gcongr; norm_num
  have hg0 : (0 : ℝ) < (3 / 2 : ℝ) ^ (Nat.log 2 H) := by positivity
  have hfull : SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
      ≤ 54 / 5 * (L : ℝ) ^ 2 := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_le hL0
  have hhead : SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_small_le hL0 j₀
  -- ⟦G1, at `arcDen³`⟧ the two consequences the mirrored weighted head needs
  have harc2 : (1 : ℝ) ≤ ((h : ℝ) * arcDen 12 H) ^ 2 := by nlinarith
  have harc3 : (1 : ℝ) ≤ ((h : ℝ) * arcDen 12 H) ^ 3 := by nlinarith
  have hG1H := hG1 H hlo hhi
  have hFtrL : 2 * ((h : ℝ) * arcDen 12 H) * (H : ℝ) ≤ Ftr H * (L : ℝ) := by
    have hchain : 2 * ((h : ℝ) * arcDen 12 H) * (H : ℝ) ≤ 2 * ((h : ℝ) * arcDen 12 H) ^ 4 * (L : ℝ)
        := by
      have h1 : 2 * ((h : ℝ) * arcDen 12 H) * (H : ℝ)
          ≤ 2 * ((h : ℝ) * arcDen 12 H) * (((h : ℝ) * arcDen 12 H) ^ 3 * (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hnar (by positivity)
      nlinarith [h1]
    have hle47 : ((h : ℝ) * arcDen 12 H) ^ 4 ≤ ((h : ℝ) * arcDen 12 H) ^ 7 := by
      calc ((h : ℝ) * arcDen 12 H) ^ 4 = ((h : ℝ) * arcDen 12 H) ^ 4 * 1 := by ring
        _ ≤ ((h : ℝ) * arcDen 12 H) ^ 4 * ((h : ℝ) * arcDen 12 H) ^ 3 :=
            mul_le_mul_of_nonneg_left harc3 (by positivity)
        _ = ((h : ℝ) * arcDen 12 H) ^ 7 := by ring
    have hle : 2 * ((h : ℝ) * arcDen 12 H) ^ 4 ≤ 2 * ((h : ℝ) * arcDen 12 H) ^ 7 := by linarith
    have hstep : 2 * ((h : ℝ) * arcDen 12 H) ^ 4 * (L : ℝ) ≤ Ftr H * (L : ℝ) :=
      mul_le_mul_of_nonneg_right (le_trans hle hG1H) hL0R.le
    linarith
  have hFtrL2 : ((h : ℝ) * arcDen 12 H) * (H : ℝ) ^ 2 ≤ Ftr H * (L : ℝ) ^ 2 := by
    have hsq : (H : ℝ) ^ 2 ≤ (((h : ℝ) * arcDen 12 H) ^ 3 * (L : ℝ)) ^ 2
        := by nlinarith [hnar, hH0R.le]
    have hstep : ((h : ℝ) * arcDen 12 H) * (H : ℝ) ^ 2 ≤ ((h : ℝ) * arcDen 12 H) ^ 7 * (L : ℝ) ^ 2
        := by
      nlinarith [mul_le_mul_of_nonneg_left hsq harc0.le]
    have hstep2 : ((h : ℝ) * arcDen 12 H) ^ 7 * (L : ℝ) ^ 2 ≤ Ftr H * (L : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hG1H (sq_nonneg ((L : ℝ)))]
    linarith
  -- ⟦the first budget line⟧
  have hEkey : ((h : ℝ) * arcDen 12 H) * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg)
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
          * (L : ℝ) ^ 2 := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hH0R]
    have hstep : ((h : ℝ) * arcDen 12 H) * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg)
        * (H : ℝ)
        ≤ ((h : ℝ) * arcDen 12 H) * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H))
            * (H : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hglg
        (by positivity : (0 : ℝ) ≤ ((h : ℝ) * arcDen 12 H) * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ)))
      nlinarith [h, hH0R.le]
    have hmain : ((h : ℝ) * arcDen 12 H) * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ)
        ^ (Nat.log 2 H))
          * (H : ℝ)
        ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ * Ftr H * (L : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hFtrL
        (by positivity : (0 : ℝ) ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀
          * (L : ℝ))
      nlinarith [h]
    linarith
  have hres : 54 / 5 * (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H)) * (L : ℝ) ^ 2
        + ((h : ℝ) * arcDen 12 H) * (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ)
            ^ j₀)
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hg2 := hG2 H hlo hhi
    have hstep : 54 / 5 * (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H)) * (L : ℝ) ^ 2
        ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ)) := by
      have h1 : 54 / 5 * (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H)) * (L : ℝ) ^ 2
          ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hg2 (sq_nonneg ((L : ℝ)))
        nlinarith [this]
      nlinarith [mul_le_mul_of_nonneg_left hL2A
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ))]
    have hgl : (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ))
        ≤ (2 / 9) * ((A : ℝ)
            * (((h : ℝ) * arcDen 12 H) * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg))) := by
      have hbig : (1 : ℝ) ≤ ((h : ℝ) * arcDen 12 H) * (3 / 2 : ℝ) ^ Lg := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hbig
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (A : ℝ))]
    have hbud := mul_le_mul_of_nonneg_left hEkey hA0R
    nlinarith [hstep, hgl, hbud]
  -- ⟦the second budget line⟧
  have hres2 : ((h : ℝ) * arcDen 12 H) * (A : ℝ) * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
    have hkey : ((h : ℝ) * arcDen 12 H) * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) * (H : ℝ)
        ^ 2
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) := by
      have h1 : ((h : ℝ) * arcDen 12 H) * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) * (H : ℝ)
          ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀
              * (((h : ℝ) * arcDen 12 H) * (H : ℝ) ^ 2) := by
        have h := mul_le_mul_of_nonneg_left hglg
          (by positivity : (0 : ℝ) ≤ 9 / 5 * (8 / 3 : ℝ) ^ j₀ * ((h : ℝ) * arcDen 12 H) * (H : ℝ)
              ^ 2)
        nlinarith [h]
      have h2 : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀
            * (((h : ℝ) * arcDen 12 H) * (H : ℝ) ^ 2)
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hFtrL2 (by positivity)
      linarith
    have hdiv : ((h : ℝ) * arcDen 12 H) * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2) := by
      have hrw : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2)
          = (9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2))
              / (H : ℝ) ^ 2 := by
        field_simp
      rw [hrw, le_div_iff₀ hH2]
      linarith [hkey]
    nlinarith [mul_le_mul_of_nonneg_left hdiv hA0R]
  have hfinal : (Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H))) * (54 / 5 * (L : ℝ)
      ^ 2)
        + (((h : ℝ) * arcDen 12 H) * (A : ℝ)) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ)
            ^ j₀
          + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hexp : m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ)
        = 54 / 5 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
          + 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ)
          + 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ) := by
      unfold m4BclGraded m4Cmax
      ring
    rw [hexp]
    nlinarith [hres, hres2]
  calc ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
      ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, Y j t n) * (2 / 3 : ℝ) ^ j := hsummed
    _ ≤ SL * ((Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H)))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
          + (((h : ℝ) * arcDen 12 H) * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hcount hSL0
    _ = (Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H)))
            * (SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j)
          + (((h : ℝ) * arcDen 12 H) * (A : ℝ)) * (SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ)
              ^ j) := by
        ring
    _ ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * ((h : ℝ) * arcDen 12 H))) * (54 / 5 * (L : ℝ) ^ 2)
          + (((h : ℝ) * arcDen 12 H) * (A : ℝ)) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ)
              ^ j₀
            + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) := by
        have h1 := mul_le_mul_of_nonneg_left hfull hCan0
        have h2 := mul_le_mul_of_nonneg_left hhead harcA0
        linarith
    _ ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := hfinal

/-- **3.4** `m4_chiSummedN_supplied_L_gk` (`M4RowLinear.lean:8648`): 3.2 and 3.3 composed
(`87 → 174` at `h = 2`). -/
theorem m4_chiSummedN_suppliedH_L_gk (h K : ℕ) {R : ChowlaRegime} {M : ℕ} {RS : ℕ → ℕ → ℝ}
    {RSan RStr : ℕ → ℝ} (j₀ : ℕ)
    (hRSan0 : ∀ H : ℕ, 0 ≤ RSan H) (hRStr0 : ∀ H : ℕ, 0 ≤ RStr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ((h : ℝ) * arcDen 12 H) ^ 7 ≤ RStr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      44 * RSan H + 87 * ((h : ℝ) * arcDen 12 H) ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ))
    (hrow : M4ChiSummedFreeRowH_L_gk h K R M RS) :
    M4ChiSummedBlockMeanSqNH_L_gk h K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) := by
  refine m4_chiSummedBlockN_of_shiftBlockH_L_gk h K (F := fun j H => 2 * RS j H) j₀
    ?_ ?_ ?_ ?_ ?_ harc8
    (m4_chiSummedShiftBlock_of_freeRowH_L_gk h K hrow)
  · intro H; have := hRSan0 H; linarith
  · intro H; have := hRStr0 H; linarith
  · intro j H hj; have := han j H hj; linarith
  · intro H hlo hhi; have := hG1 H hlo hhi; linarith
  · intro H hlo hhi
    have hg2 := hG2 H hlo hhi
    have h0 := hRSan0 H
    have harc := hArcDen_nonneg h H
    linarith

/-! ## §4 — the stratified block sup at the inflated cap: WHERE THE RESIDUAL ENTERS -/

set_option maxHeartbeats 1600000 in
-- the stratified assembly re-elaborates the divisor sum, the fibre count, the χ-datum and
-- the ledger at every stratum, as at `M4RowLinear.lean:9745`
/-- **THE STRATIFIED CONSUMER AT THE INFLATED CAP** — `m4_freeBlockSup_of_chiSummed_L_gk`
(`M4RowLinear.lean:9750`).  The Gauss strata's harmonic sum `∑_{d ∣ q} 1/d ≤ 1 + log q` is
bounded through `q ≤ h·arcDen` by `strataResidualH h H` and by nothing smaller; the dilated
base's x-floor (step (iii)) is where the x-scale floor's inflation is SPENT (`d ≤ h·arcDen`). -/
theorem m4_freeBlockSup_of_chiSummedH_L_gk (h K : ℕ) {R : ChowlaRegime} {M : ℕ} {Bcl : ℕ → ℝ}
    (hM : 1 ≤ M)
    (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (h : ℝ) * arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
    (hchi : M4ChiSummedBlockMeanSqNH_L_gk h K R M Bcl) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H →
      (H : ℝ) ≤ ((h : ℝ) * arcDen 12 H) ^ 2 * (L : ℝ) → 32 * ((h : ℝ) * arcDen 12 H) ≤ (L : ℝ) →
      16 * ((h : ℝ) * arcDen 12 H) ^ 2 ≤ (H : ℝ) →
      ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
        ∀ A B : ℕ, 0 < A → 2 * (H : ℝ) ≤ (A : ℝ) →
          (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) → B + L ≤ 2 * A →
          ∑ n ∈ Finset.Ioc A B,
              (subWindowSup (doorSievedCoeff_L_gk K M) L n ((b : ℝ) / (q : ℝ))) ^ 2
            ≤ 4 * strataResidualH h H ^ 2 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by
  classical
  intro H hlo hhi L hLH hnar hLarc harcsq b q hq hqQ A B hA hAH hAx hAcap hfit
  have harc1 : (1 : ℝ) ≤ ((h : ℝ) * arcDen 12 H) := one_le_hArcDen_of_cap hq hqQ
  have harc0 : (0 : ℝ) < ((h : ℝ) * arcDen 12 H) := by linarith
  have hAarc : 32 * ((h : ℝ) * arcDen 12 H) ≤ (A : ℝ) := by
    have hLHR : (L : ℝ) ≤ (H : ℝ) := by exact_mod_cast hLH
    linarith
  have hres0 : (0 : ℝ) ≤ strataResidualH h H := strataResidualH_nonneg harc1
  have hB0 := hBcl0 H
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  have hL0R : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have hdiv0 : (0 : ℝ) ≤ ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) :=
    Finset.sum_nonneg fun d _ => by positivity
  have hdivres : ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) ≤ strataResidualH h H := by
    refine le_trans (sum_inv_divisors_le hq) ?_
    unfold strataResidualH
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have := Real.log_le_log (by linarith) hqQ
    linarith
  by_cases hAB : B < A
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity
  rw [Nat.not_lt] at hAB
  -- ⟦the block's own consequences: the tight fit and the two arc floors⟧
  have hLA : L ≤ A := by omega
  have hLAR : (L : ℝ) ≤ (A : ℝ) := by exact_mod_cast hLA
  have hL32 : (32 : ℝ) ≤ (L : ℝ) := by nlinarith
  have hL2 : 2 ≤ L := by
    have : (2 : ℝ) ≤ (L : ℝ) := by linarith
    exact_mod_cast this
  -- ⟦R-P5, THE THREE ANTECEDENTS AT THE UNDILATED BASE⟧ the two arithmetic facts every
  --  dilated instance below re-reads: `4·((h : ℝ) * arcDen 12 H) ≤ √H` (the window floor at its
  -- square)
  -- and `2L ≤ A` (the length antecedent with the two units of `ℕ`-division slack)
  have hH0 : 0 < H := by omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have hLHR : (L : ℝ) ≤ (H : ℝ) := by exact_mod_cast hLH
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have hsqsq : Real.sqrt (H : ℝ) ^ 2 = (H : ℝ) := Real.sq_sqrt hH0R.le
  have harcsqrt : 4 * ((h : ℝ) * arcDen 12 H) ≤ Real.sqrt (H : ℝ) := by
    have h1 : Real.sqrt ((4 * ((h : ℝ) * arcDen 12 H)) ^ 2) ≤ Real.sqrt (H : ℝ) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hsqrtle : Real.sqrt (H : ℝ) ≤ (H : ℝ) := by nlinarith [harcsqrt, harc1]
  have h2LA : 2 * L ≤ A := by
    have h : (2 : ℝ) * (L : ℝ) ≤ (A : ℝ) := by linarith
    exact_mod_cast h
  -- ⟦the per-base stratified bound, summed⟧
  have hpt : ∀ n ∈ Finset.Ioc A B,
      (subWindowSup (doorSievedCoeff_L_gk K M) L n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm_L_gk K M q L d n := fun n _ =>
    subWindowSup_sq_le_strata_L_gk K hM hq hqQ (hgate H hlo hhi) b
  refine le_trans (Finset.sum_le_sum hpt) ?_
  have hswap : ∑ n ∈ Finset.Ioc A B,
        ((∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm_L_gk K M q L d n)
      = (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
        * ∑ d ∈ q.divisors, (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]
  rw [hswap]
  -- ⟦THE PER-STRATUM BUDGET⟧ the fibre count, the χ-datum, the sharp ledger
  have hstr : ∀ d ∈ q.divisors,
      (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n
        ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * ((1 : ℝ) / (d : ℝ)) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdarc : (d : ℝ) ≤ ((h : ℝ) * arcDen 12 H) :=
      le_trans (by exact_mod_cast Nat.le_of_dvd hq hdq) hqQ
    have hdA2R : 2 * (d : ℝ) ≤ (A : ℝ) := by nlinarith
    have hdA2 : 2 * d ≤ A := by exact_mod_cast hdA2R
    have hdA : d ≤ A := by omega
    have hdL : (d : ℝ) ≤ (L : ℝ) := by nlinarith
    have h32dL : 32 * d ≤ L := by
      have h : (32 : ℝ) * (d : ℝ) ≤ (L : ℝ) := by linarith
      exact_mod_cast h
    have hdA3 : 3 * d ≤ A := by
      have h : (3 : ℝ) * (d : ℝ) ≤ (A : ℝ) := by linarith
      exact_mod_cast h
    -- ⟦the reduced modulus⟧
    have hq0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
    have hq0Q : ((q / d : ℕ) : ℝ) ≤ ((h : ℝ) * arcDen 12 H) :=
      le_trans (by exact_mod_cast Nat.div_le_self q d) hqQ
    -- ⟦the dilated cap is admissible⟧
    have hcapL : capL L d ≤ L := capL_le hd0 hL2
    have hcapH : capL L d ≤ H := le_trans hcapL hLH
    have hcapmul : (L : ℝ) ≤ (d : ℝ) * ((capL L d : ℕ) : ℝ) := by
      exact_mod_cast le_mul_capL (L := L) (d := d) hd0
    have hcap0 : (0 : ℝ) ≤ ((capL L d : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcapnar : (H : ℝ) ≤ ((h : ℝ) * arcDen 12 H) ^ 3 * ((capL L d : ℕ) : ℝ) := by
      have h1 : (L : ℝ) ≤ ((h : ℝ) * arcDen 12 H) * ((capL L d : ℕ) : ℝ) := by
        have := mul_le_mul_of_nonneg_right hdarc hcap0
        linarith [hcapmul]
      have h2 : ((h : ℝ) * arcDen 12 H) ^ 2 * (L : ℝ)
          ≤ ((h : ℝ) * arcDen 12 H) ^ 2 * (((h : ℝ) * arcDen 12 H) * ((capL L d : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have heq : ((h : ℝ) * arcDen 12 H) ^ 2 * (((h : ℝ) * arcDen 12 H) * ((capL L d : ℕ) : ℝ))
          = ((h : ℝ) * arcDen 12 H) ^ 3 * ((capL L d : ℕ) : ℝ) := by ring
      rw [heq] at h2
      linarith [hnar]
    -- ⟦the re-indexed block⟧
    have hA'2 : 2 ≤ A / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
    have hA'pos : 0 < A / d - 1 := by omega
    have hA'3 : 3 ≤ A / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
    -- ⟦R-P5, THE THREE ANTECEDENTS AT THE DILATED BASE⟧ each spends exactly one power of
    --  `((h : ℝ) * arcDen 12 H)` (because `d ≤ ((h : ℝ) * arcDen 12 H)`) and the two `ℕ`-division
    -- units the `⌊·⌋` and
    -- the `−1` cost — the same pattern as `hcapnar` above
    have hA'cast : ((A / d - 1 : ℕ) : ℝ) = ((A / d : ℕ) : ℝ) - 1 := by
      have h1 : 1 ≤ A / d := by omega
      rw [Nat.cast_sub h1, Nat.cast_one]
    have hAdiv : (A : ℝ) ≤ (d : ℝ) * ((A / d : ℕ) : ℝ) + (d : ℝ) := by
      have h' := (Nat.cast_le (α := ℝ)).mpr (le_mul_div_add (A := A) (d := d) hd0)
      push_cast at h'
      linarith
    have hA'0 : (0 : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hA'2R : (2 : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := by
      have h : (2 : ℕ) ≤ A / d - 1 := by omega
      exact_mod_cast h
    -- (i) THE LENGTH ANTECEDENT `capL L d ≤ ⌊A/d⌋ − 1`
    have hcapA : capL L d ≤ A / d - 1 := capL_le_dilated_base hd0 h32dL h2LA
    -- (ii) THE `√H` ANTECEDENT
    have hsqA' : Real.sqrt (H : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := by
      rw [hA'cast]
      have hd4 : 4 * (d : ℝ) ≤ Real.sqrt (H : ℝ) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hd4
        (by positivity : (0 : ℝ) ≤ Real.sqrt (H : ℝ) + 2)
      have hkey : (d : ℝ) * (Real.sqrt (H : ℝ) + 2) ≤ (A : ℝ) := by
        nlinarith [hmul, hsqsq, hsqrtle, hAH, hH0R, hA0R]
      have hstep : (d : ℝ) * Real.sqrt (H : ℝ)
          ≤ (d : ℝ) * (((A / d : ℕ) : ℝ) - 1) := by nlinarith [hAdiv, hkey]
      exact le_of_mul_le_mul_left hstep hd0R
    -- (iii) THE x-SCALE ANTECEDENT
    have hxA' : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * ((h : ℝ) * arcDen 12 H) * ((A / d - 1 : ℕ) : ℝ) := by
      have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
      have hAd2 : (A : ℝ) ≤ (d : ℝ) * ((A / d - 1 : ℕ) : ℝ) + 2 * (d : ℝ) := by
        rw [hA'cast]; linarith [hAdiv]
      have s1 : (R.x : ℝ)
          ≤ 8 * (R.ω : ℝ) * ((d : ℝ) * ((A / d - 1 : ℕ) : ℝ) + 2 * (d : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hAd2 (by positivity : (0 : ℝ) ≤ 8 * (R.ω : ℝ))
        linarith [hAx]
      have s2 : (d : ℝ) * ((A / d - 1 : ℕ) : ℝ) + 2 * (d : ℝ)
          ≤ 2 * (((h : ℝ) * arcDen 12 H) * ((A / d - 1 : ℕ) : ℝ)) := by
        have h1 : (d : ℝ) * ((A / d - 1 : ℕ) : ℝ)
            ≤ ((h : ℝ) * arcDen 12 H) * ((A / d - 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hdarc hA'0
        have h2 : 2 * ((h : ℝ) * arcDen 12 H) ≤ ((h : ℝ) * arcDen 12 H) * ((A / d - 1 : ℕ) : ℝ)
            := by
          nlinarith [hA'2R, harc0]
        linarith
      have s3 := mul_le_mul_of_nonneg_left s2 (by positivity : (0 : ℝ) ≤ 8 * (R.ω : ℝ))
      nlinarith [s1, s3]
    -- (iv) THE BASE CAP, INHERITED (the (α) base-cap surgery, JYH-granted 2026-07-30):
    -- `⌊A/d⌋ − 1 ≤ A`, so the cap passes to the dilated base with NO `arcDen` power spent
    have hcapA' : ((A / d - 1 : ℕ) : ℝ) ≤ 2 * (R.x : ℝ) := by
      have hle : ((A / d - 1 : ℕ) : ℝ) ≤ (A : ℝ) := by
        have hnat : A / d - 1 ≤ A := le_trans (Nat.sub_le _ _) (Nat.div_le_self A d)
        exact_mod_cast hnat
      linarith
    have hfit' : B / d + capL L d ≤ 2 * (A / d - 1) + 4 := by
      have h := dilBlock_reindex_fit (A := A) (B := B) (H := L) (d := d) hd0 hdA hfit
      have hc := capL_le_div_succ (L := L) (d := d) hd0
      omega
    -- ⟦the fibre count⟧
    have hf0 : ∀ n' : ℕ, (0 : ℝ) ≤ ∑ χ : DirichletCharacter ℂ (q / d),
        (doorChiSup_L_gk K χ M (capL L d) n') ^ 2 := fun n' =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hmaps : ∀ n ∈ Finset.Ioc A B, n / d ∈ Finset.Ioc (A / d - 1) (B / d) := fun n hn =>
      div_mem_reindexed hd0 hdA hn
    have hfib := sum_Ioc_comp_div_le (f := fun n' => ∑ χ : DirichletCharacter ℂ (q / d),
      (doorChiSup_L_gk K χ M (capL L d) n') ^ 2) hf0 hd0 hmaps
    -- ⟦the χ-summed datum at the reduced modulus⟧
    have hdatum := hchi H hlo hhi (capL L d) hcapH hcapnar (q / d) hq0 hq0Q
      (A / d - 1) (B / d) hA'pos hcapA hsqA' hxA' hcapA' hfit'
    -- ⟦the sharp ledger⟧
    have hled := capL_ledger (A := A) (L := L) (d := d) hd0 hB0
    have hdatum' : ∑ n' ∈ Finset.Ioc (A / d - 1) (B / d),
          ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup_L_gk K χ M (capL L d) n') ^ 2
        ≤ Bcl H * ((capL L d : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ) := by
      rw [Finset.sum_comm]
      exact hdatum
    have hchain : ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n
        ≤ (d : ℝ) * (Bcl H * ((capL L d : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ)) := by
      refine le_trans hfib ?_
      exact mul_le_mul_of_nonneg_left hdatum' hd0R.le
    have hfinal : ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n
        ≤ Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2 := le_trans hchain hled
    have hLd : ((L : ℝ) + (d : ℝ)) ^ 2 ≤ 4 * (L : ℝ) ^ 2 := by nlinarith
    have hstep : (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n
        ≤ (d : ℝ) * (Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hfinal hd0R.le
    have hdne : ((d : ℝ)) ≠ 0 := ne_of_gt hd0R
    have hrw : (d : ℝ) * (Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2)
        = (Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ)) * ((1 : ℝ) / (d : ℝ)) := by
      field_simp
    refine le_trans hstep ?_
    rw [hrw]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith [mul_le_mul_of_nonneg_left hLd (mul_nonneg hB0 hA0R)]
  -- ⟦the recombination⟧
  have hsum : ∑ d ∈ q.divisors, (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n
      ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hstr
  have hbig0 : (0 : ℝ) ≤ 4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by positivity
  calc (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
        * ∑ d ∈ q.divisors, (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n
      ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ((4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ))
            * ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hdiv0
    _ ≤ strataResidualH h H * ((4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * strataResidualH h H) := by
        have h1 : (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ))
              * ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ)
            ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * strataResidualH h H :=
          mul_le_mul_of_nonneg_left hdivres hbig0
        have h2 : (0 : ℝ) ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * strataResidualH h H := by
          positivity
        nlinarith [hdivres, hdiv0]
    _ = 4 * strataResidualH h H ^ 2 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by ring

set_option maxHeartbeats 1200000 in
-- the block sum is re-associated over the drift blocks and then over the ladder block, as at
-- `M4RowSpineLinear.lean:695`
/-- **3.5** `m4_blockMeanSqBlk2_of_chiSummed_L_gk` (`M4RowSpineLinear.lean:699`) at the witness
`blockLenH h`; `hgate` is the door gate `h·(log H)^12 < P₁`, a HYPOTHESIS here as at `h = 1`. -/
theorem m4_blockMeanSqBlk2_of_chiSummedH_L_gk (h K : ℕ) {R : ChowlaRegime} {M k : ℕ}
    {Bcl : ℕ → ℝ} (hM : 1 ≤ M) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (h : ℝ) * arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * ((h : ℝ) * arcDen 12 H) ^ 2 ≤ (H : ℝ))
    (hcount : (k : ℝ) ≤ Real.log (R.ω : ℝ) / Real.log 2 + 2)
    (hchi : M4ChiSummedBlockMeanSqNH_L_gk h K R M Bcl) :
    M4BlockMeanSqBlk2H_L_gk h K R M k (blockLenH h)
      (fun H => 8 * strataResidualH h H ^ 2 * Bcl H) := by
  intro H hlo hhi b q hq hqQ hℓ1 hℓH hℓcnt i hik
  have harc1 : (1 : ℝ) ≤ ((h : ℝ) * arcDen 12 H) := one_le_hArcDen_of_cap hq hqQ
  have hh1 : 1 ≤ h := one_le_of_hArcDen harc1
  have harcH := harc H hlo hhi
  have hres0 : (0 : ℝ) ≤ strataResidualH h H := strataResidualH_nonneg harc1
  have hB0 := hBcl0 H
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
  have hfit : doorLadder R.x H i + H ≤ 2 * doorLadder R.x H (i + 1) := doorLadder_fit R.x H i
  have hApos : 0 < doorLadder R.x H (i + 1) := by omega
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  set L := blockLenH h H q with hLdef
  set N := numBlocks H L with hN
  have hLarc : 32 * ((h : ℝ) * arcDen 12 H) ≤ (L : ℝ) := blockLenH_arc_floor (R := R) hh1 hlo harcH
  have hL16 : 16 * ((h : ℝ) * arcDen 12 H) ^ 2 ≤ (H : ℝ) := by
    nlinarith [harcH, sq_nonneg (((h : ℝ) * arcDen 12 H))]
  -- ⟦R-P5, THE x-SCALE LADDER AT THIS RUNG⟧ the base antecedents `M4Gauss` now asks for,
  -- discharged from the ladder's geometric floor (`doorLadder_ge_x_div_four_omega`), its
  -- CEILING (`doorLadder_le_start`, the (α) base cap) and the regime's own wave-II headroom
  -- `8·H₊·log²H₊ ≤ ⌊x/ω⌋` (whose two log factors are `≥ 1` at `H₊ ≥ 4·10⁶`)
  -- — NO new regime field, NO `g`-arm movement
  have hω0N : 0 < 4 * R.ω := by have := R.hω; omega
  have hω0 : (0 : ℝ) < (R.ω : ℝ) := by
    have h : 0 < R.ω := by have := R.hω; omega
    exact_mod_cast h
  have hxdiv : R.x / (4 * R.ω) ≤ A := by
    rw [hA]
    exact doorLadder_ge_x_div_four_omega (H := H) R.hω hcount (by omega)
  -- ⟦(α) THE BASE CAP AT THIS RUNG⟧ the ceiling side of the socket's fourth base antecedent
  -- (the (α) base-cap surgery, JYH-granted 2026-07-30): the ladder never exceeds its own
  -- top, so `X_{i+1} ≤ x` and every drift-shifted base is `≤ x + H ≤ 2x`
  have hAtop : A ≤ R.x := by
    rw [hA]
    exact doorLadder_le_start hxH (i + 1)
  have hHhi4 : (4000000 : ℝ) ≤ (R.Hhi : ℝ) := by
    have h : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
    exact_mod_cast h
  have hlogHhi : (1 : ℝ) ≤ Real.log (R.Hhi : ℝ) := by
    have hexp : Real.exp 1 ≤ (R.Hhi : ℝ) := by nlinarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by linarith)).mpr hexp
  have hxω : 8 * (R.ω : ℝ) * (R.Hhi : ℝ) ≤ (R.x : ℝ) := by
    have hh := R.hheadroom'
    have hcast : (((R.x / R.ω : ℕ)) : ℝ) ≤ (R.x : ℝ) / (R.ω : ℝ) := Nat.cast_div_le
    have hlogsq : (1 : ℝ) ≤ Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) := by
      nlinarith [hlogHhi]
    have h1 : 8 * (R.Hhi : ℝ) ≤ (R.x : ℝ) / (R.ω : ℝ) := by
      calc 8 * (R.Hhi : ℝ) = 8 * (R.Hhi : ℝ) * 1 := by ring
        _ ≤ 8 * (R.Hhi : ℝ) * (Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogsq (by linarith)
        _ = 8 * (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) := by ring
        _ ≤ (((R.x / R.ω : ℕ)) : ℝ) := hh
        _ ≤ (R.x : ℝ) / (R.ω : ℝ) := hcast
    rw [le_div_iff₀ hω0] at h1
    linarith
  have hHhiR : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast hhi
  have h8ωH : 8 * R.ω * H ≤ R.x := by
    have h : (8 : ℝ) * (R.ω : ℝ) * (H : ℝ) ≤ (R.x : ℝ) := by nlinarith [hxω, hHhiR, hω0]
    exact_mod_cast h
  have h2HA : 2 * (H : ℝ) ≤ (A : ℝ) := by
    have hn : 2 * H ≤ A := by
      refine le_trans ((Nat.le_div_iff_mul_le hω0N).mpr ?_) hxdiv
      calc 2 * H * (4 * R.ω) = 8 * R.ω * H := by ring
        _ ≤ R.x := h8ωH
    exact_mod_cast hn
  have hxA : (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * (A : ℝ) := by
    have hdivub : R.x ≤ 4 * R.ω * (R.x / (4 * R.ω)) + 4 * R.ω :=
      le_mul_div_add (A := R.x) (d := 4 * R.ω) hω0N
    have h1 := (Nat.cast_le (α := ℝ)).mpr hdivub
    have h2 : (((R.x / (4 * R.ω) : ℕ)) : ℝ) ≤ (A : ℝ) := by exact_mod_cast hxdiv
    push_cast at h1
    have hbig : 8 * (R.ω : ℝ) ≤ (R.x : ℝ) := by nlinarith [hxω, hHhi4, hω0]
    nlinarith [h1, h2, hω0, hbig]
  -- ⟦the drift blocks, one free block each⟧
  have hstrat := m4_freeBlockSup_of_chiSummedH_L_gk h K (R := R) (M := M) (Bcl
      := Bcl) hM hBcl0 hgate
    hchi H hlo hhi L hℓH hℓcnt hLarc hL16 b q hq hqQ
  have hper : ∀ m ∈ Finset.range N,
      ∑ n ∈ Finset.Ioc A B, (subWindowSup (doorSievedCoeff_L_gk K M) L (n + m * L)
          ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ 8 * strataResidualH h H ^ 2 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by
    intro m hm
    have hmL : m * L ≤ H := mul_le_of_lt_numBlocks (Finset.mem_range.mp hm)
    have hshift : ∑ n ∈ Finset.Ioc A B,
        (subWindowSup (doorSievedCoeff_L_gk K M) L (n + m * L) ((b : ℝ) / (q : ℝ))) ^ 2
        = ∑ n ∈ Finset.Ioc (A + m * L) (B + m * L),
            (subWindowSup (doorSievedCoeff_L_gk K M) L n ((b : ℝ) / (q : ℝ))) ^ 2 :=
      sum_Ioc_shift (fun n => (subWindowSup (doorSievedCoeff_L_gk K M) L n ((b : ℝ) / (q : ℝ))) ^ 2)
        A B _
    rw [hshift]
    have hApos' : 0 < A + m * L := by omega
    have hAle : (A : ℝ) ≤ ((A + m * L : ℕ) : ℝ) := by
      exact_mod_cast (by omega : A ≤ A + m * L)
    have h2HA' : 2 * (H : ℝ) ≤ ((A + m * L : ℕ) : ℝ) := by linarith
    have hxA' : (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * ((A + m * L : ℕ) : ℝ) := by
      nlinarith [hxA, hAle, hω0]
    have hcapA' : ((A + m * L : ℕ) : ℝ) ≤ 2 * (R.x : ℝ) := by
      have hnat : A + m * L ≤ 2 * R.x :=
        calc A + m * L ≤ R.x + H := Nat.add_le_add hAtop hmL
          _ ≤ 2 * R.x := by omega
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this ⊢
      linarith
    have hfit' : (B + m * L) + L ≤ 2 * (A + m * L) := by omega
    have hst := hstrat (A + m * L) (B + m * L) hApos' h2HA' hxA' hcapA' hfit'
    have hbase : ((A + m * L : ℕ) : ℝ) ≤ 2 * (A : ℝ) := by
      have hnat : A + m * L ≤ 2 * A := by omega
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this ⊢
      linarith
    have hfac0 : (0 : ℝ) ≤ 4 * strataResidualH h H ^ 2 * Bcl H * (L : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hbase hfac0]
  -- ⟦the drift-block sum⟧
  have hswap : ∑ n ∈ Finset.Ioc A B, blockSupSq (doorSievedCoeff_L_gk K M) H L n ((b : ℝ) / (q : ℝ))
      = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.Ioc A B,
          (subWindowSup (doorSievedCoeff_L_gk K M) L (n + m * L) ((b : ℝ) / (q : ℝ))) ^ 2 := by
    unfold blockSupSq
    exact Finset.sum_comm
  rw [hswap]
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine le_of_eq ?_
  ring

/-- **3.6** `m4_cover_assembly_blk2_L_gk` (`M4RowSpineLinear.lean:676`), verbatim
(`integral_door_cover_le_clean` reads no cap). -/
theorem m4_cover_assembly_blk2H_L_gk (h K : ℕ) {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {ℓ : ℕ → ℕ → ℕ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates_L_gk K Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqBlk2H_L_gk h K R M k ℓ Bblk) :
    M4SievedDoorSqBlk2H_L_gk h K R M ℓ (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ h1 h2 h3
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2 := by
    have := hB0 H; positivity
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => blockSupSq (doorSievedCoeff_L_gk K M) H (ℓ H q) n ((b : ℝ) / (q : ℝ)))
    (P := Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount
    (fun n => blockSupSq_nonneg _ _ _ _ _) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ h1 h2 h3)
  refine le_trans hmain (le_of_eq ?_)
  ring

/-- **3.7 THE BLOCKED DRIFT AT THE INFLATED `α`-SET** — `m4_sievedDoorSq_of_blk2_L_gk`
(`M4RowSpineLinear.lean:595`) with the drift lemma fired at the opaque cap
`Q := h · arcDen 12 H` (§1′); `h`-general. -/
theorem m4_sievedDoorSq_of_blk2H_L_gk (h K : ℕ) {R : ChowlaRegime} {M : ℕ} {ℓ : ℕ → ℕ → ℕ}
    {Bblk Braw : ℕ → ℝ}
    (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hℓ1 : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
      1 ≤ ℓ H q)
    (hℓH : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
      ℓ H q ≤ H)
    (hℓcnt : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
      (H : ℝ) ≤ ((h : ℝ) * arcDen 12 H) ^ 2 * (ℓ H q : ℝ))
    (hℓdrift : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
      (h : ℝ) * arcDen 12 H * (ℓ H q : ℝ) ≤ (q : ℝ) * (H : ℝ))
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * (1 + 2 * Real.pi) ^ 2 * Bblk H ≤ Braw H)
    (hblk : M4SievedDoorSqBlk2H_L_gk h K R M ℓ Bblk) : M4SievedDoorSqH_L_gk h K R M Braw := by
  intro htr H _ hlo hhi α hα
  have hH : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  obtain ⟨b, q, hq, hqQ, hd⟩ := hα
  have hℓ1' := hℓ1 H q hlo hhi hq hqQ
  have hℓH' := hℓH H q hlo hhi hq hqQ
  have hℓcnt' := hℓcnt H q hlo hhi hq hqQ
  have hℓdrift' := hℓdrift H q hlo hhi hq hqQ
  have hℓ0 : 0 < ℓ H q := hℓ1'
  set c := doorSievedCoeff_L_gk K M with hc
  set β : ℝ := (b : ℝ) / (q : ℝ) with hβ
  set L := ℓ H q with hL
  set N := numBlocks H L with hN
  have hpt : ∀ n : ℕ, ‖absWindowSum c H n α‖ ^ 2
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β := by
    intro n
    have h := norm_absWindowSum_sq_le_drift_blocked_Q (Q := ((h : ℝ) * arcDen 12 H)) (H := H) (q
        := q) (n := n)
      (ℓ := L) hq hH hℓ0 (β := β) (θ := α - β) hd hℓdrift' c
    have he : β + (α - β) = α := by ring
    rw [he] at h
    exact h
  have hmono : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ ∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_mono hpt
  have hconst : (∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β
        ∂(logMeasure R.x R.ω))
      = (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * ∫ n, blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_const_mul _ _
  have hsupply := hblk htr H hlo hhi b q hq hqQ hℓ1' hℓH' hℓcnt'
  have hfac0 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) := by positivity
  have hstep : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := by
    rw [hconst] at hmono
    exact le_trans hmono (mul_le_mul_of_nonneg_left hsupply hfac0)
  have hNL : N * L ≤ 2 * H := by
    have h1 : N * L ≤ H + L := by rw [hN]; exact numBlocks_mul_le H L
    omega
  have hNLR : (N : ℝ) * (L : ℝ) ≤ 2 * (H : ℝ) := by
    have : ((N * L : ℕ) : ℝ) ≤ ((2 * H : ℕ) : ℝ) := by exact_mod_cast hNL
    push_cast at this
    linarith
  have hNL0 : (0 : ℝ) ≤ (N : ℝ) * (L : ℝ) := by positivity
  have hsq : ((N : ℝ) * (L : ℝ)) ^ 2 ≤ 4 * (H : ℝ) ^ 2 := by nlinarith
  have hB := hB0 H
  have hpi2 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 := sq_nonneg _
  have hfin : (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
      ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by
    calc (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
        = (1 + 2 * Real.pi) ^ 2 * Bblk H * (((N : ℝ) * (L : ℝ)) ^ 2) := by ring
      _ ≤ (1 + 2 * Real.pi) ^ 2 * Bblk H * (4 * (H : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hpi2 hB)
      _ = 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by ring
  have hgr := hgrade H hlo hhi
  calc (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := hstep
    _ ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := hfin
    _ ≤ Braw H * (H : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hgr (sq_nonneg _)

/-! ## §3′ — THE EXIT AT SHIFT `h`: the door mint on the terminal's lane -/

/-- **3.8 THE MINT** — `HDoorArc.m4_doorL2_supply_H` (`:491`) with `M4DoorGates →
M4DoorGates_L_gk K`, `M4SievedDoorSqH → M4SievedDoorSqH_L_gk h K`, and the sieve insert fired at
`(AdoorL M) (s13GK K M)`; `parseval_insert_budget_door` is lane-general and the arc supply at
the twisted set (`nearRatTight_of_bigXiArcTight_H`) is lane-free.  `(hh : 0 < h)` is carried
explicitly per the `ShiftFork` module fence. -/
theorem m4_doorL2_supply_H_L_gk (h : ℕ) (hh : 0 < h) (K : ℕ) :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (eps : ℚ), 0 < eps → ∃ H₀ : ℕ,
        ∀ (R : ChowlaRegime), R.eps = eps → H₀ ≤ R.Hlo →
          ∀ (Braw : ℕ → ℝ) (Kc Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSqH_L_gk h K R M Braw →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((bigXiH h R.eps H).card : ℝ) ≤ Kc) →
            0 ≤ Kc →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
              MRTUniformityXiL2H h R (2 * Kc * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ)) := by
  obtain ⟨Cg, hCg, hpars⟩ := parseval_insert_budget_door
  refine ⟨Cg, hCg, ?_⟩
  intro eps heps
  obtain ⟨H₀, hH₀⟩ := nearRatTight_of_bigXiArcTight_H bigXiArcTight_twelve heps hh
  refine ⟨H₀, ?_⟩
  intro R hReps hfloor Braw Kc Bceil δ M k hgates hBraw0 hsock hXi hK0 hceil
  -- ⟦the arc supply at the TWISTED set, transported to the regime's own `ε`⟧
  have harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXiH h R.eps H,
      NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)) := by
    intro H _ hH ξ hξ
    rw [hReps] at hξ
    exact hH₀ H hH ξ hξ
  -- ⟦the door's own scales, off the regime — the lane's four lines⟧
  have hA : 1 ≤ AdoorL M := one_le_AdoorL hgates.hM
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
    intro H hhi
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  -- ⟦THE FUSE⟧ the adapter's `hins`, fired at `Xi := bigXiH h R.eps H`.
  have hins : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ bigXiH h R.eps H,
        ∫ n, ‖absWindowSum lamCoeff H n (-(ξ.val : ℝ) / (H : ℝ))
            - absWindowSum (memSCoeff (calP (AdoorL M) (s13GK K M))
                (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω)
        ≤ δ / 4 + 4 * 2 ^ k / (R.x : ℝ) := by
    intro H _ hlo hhi
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (AdoorL M) (s13GK K M) M 2 R.x R.ω H k liouvilleC δ (bigXiH h R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  -- ⟦the adapter⟧ N4c: arc + socket at the inflated cap + count + the fused insert budget.
  have hkey := sum_bigXiH_norm_windowExpSum_sq_le_parseval h R
    (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC)
    Braw Kc (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) hfloor harc hBraw0 (hsock m4_bandTransport)
    hXi hins
  -- ⟦the budget line⟧ and the `H`-uniform ceiling on the socket leg.
  intro H _ hlo hhi
  have hb := hkey H hlo hhi
  rw [l2_budget_line Kc (Braw H) δ (R.x : ℝ) k] at hb
  have hmono : 2 * Kc * Braw H ≤ 2 * Kc * Bceil :=
    mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
  linarith

/-- **THE `_500` PIN** — `HDoorArc.m4_doorL2_supply_500_H` (`:575`) on the lane: the count
discharged from `bigXiH_card_le_mul` against `bigXi_bounded_500`'s third conjunct, the exported
constant `KXi = h · 32·K_lcm·(2^35)² / ε^10` at `ε = 1/500`, `h`-explicit in the witness. -/
theorem m4_doorL2_supply_500_H_L_gk (h : ℕ) (hh : 0 < h) (K : ℕ) :
    ∃ (Cg KXi : ℝ), 1 ≤ Cg ∧ 0 < KXi ∧ ∃ H₀ : ℕ,
      ∀ (R : ChowlaRegime), R.eps = 1 / 500 → H₀ ≤ R.Hlo →
        ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
          M4DoorGates_L_gk K Cg R M k δ →
          (∀ H : ℕ, 0 ≤ Braw H) →
          M4SievedDoorSqH_L_gk h K R M Braw →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            MRTUniformityXiL2H h R (2 * KXi * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ)) := by
  obtain ⟨Cg, hCg, hsup⟩ := m4_doorL2_supply_H_L_gk h hh K
  obtain ⟨Klcm, hKlcm, _, hcount⟩ := bigXi_bounded_500
  obtain ⟨H₀, hH₀⟩ := hsup (1 / 500) (by norm_num)
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have h500 : (0 : ℝ) < (((1 : ℚ) / 500 : ℚ) : ℝ) ^ 10 := by norm_num
  refine ⟨Cg, (h : ℝ) * (32 * Klcm * ((2 : ℝ) ^ 35) ^ 2 / (((1 : ℚ) / 500 : ℚ) : ℝ) ^ 10),
    hCg, ?_, H₀, ?_⟩
  · exact mul_pos hhR (by positivity)
  intro R hReps hfloor Braw Bceil δ M k hgates hBraw0 hsock hceil
  refine hH₀ R hReps hfloor Braw _ Bceil δ M k hgates hBraw0 hsock ?_ ?_ hceil
  · intro H _ hlo _
    have h2 : 2 ≤ H := le_trans (two_le_regime_Hlo R) hlo
    have hfib : ((bigXiH h R.eps H).card : ℝ) ≤ (h : ℝ) * ((bigXi R.eps H).card : ℝ) := by
      exact_mod_cast bigXiH_card_le_mul h hh R.eps H
    have hbase : ((bigXi R.eps H).card : ℝ)
        ≤ 32 * Klcm * ((2 : ℝ) ^ 35) ^ 2 / (((1 : ℚ) / 500 : ℚ) : ℝ) ^ 10 := by
      rw [hReps]
      exact hcount H h2
    exact le_trans hfib (mul_le_mul_of_nonneg_left hbase hhR.le)
  · positivity

/-! ## §5 — THE REGISTER AT SHIFT `h`, DOOR FORM -/

/-- **⟦THE SECOND ROAD'S TERMINAL REGISTER AT SHIFT `h`, ON THE TERMINAL'S LANE — DOOR FORM⟧**
(`m4_second_road_L2_gk_flatRoot_L`, `S16FlatTerminalLinear.lean:239`, with every cap read at
`h · arcDen 12 H`).  The five cap reads: ⟦G1⟧ `(h·arcDen)^7 ≤ RStr` · ⟦G2⟧ `87·(h·arcDen)` ·
⟦floor⟧ `128·(h·arcDen)^3 ≤ H` · ⟦door gate⟧ `h·arcDen < P₁` · ⟦drift⟧ `strataResidualH h H`.
The exit is the mint (§3′), so the `Kb`/`δ₀` budget line of the `h = 1` register is replaced by
the count `Kc` and the door's grade is the conclusion's argument; the consumer is
`log_chowla_two_shell_xi_sq_h h`'s `hdoor` slot, whose `hbudget2 : ρ < c₀·ε` becomes the
caller's budget line — the same three-term line `l2_budget_line` the `h = 1` register checks
against `δ₀`. -/
theorem m4_second_road_L2_H_gk_flatRoot_L (h : ℕ) (hh : 0 < h) (K : ℕ) :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (eps : ℚ), 0 < eps → ∃ H₀ : ℕ,
        ∀ (R : ChowlaRegime), R.eps = eps → H₀ ≤ R.Hlo →
          ∀ (δ Bceil Kc : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
            M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ((h : ℝ) * arcDen 12 H) ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * ((h : ℝ) * arcDen 12 H) ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              (h : ℝ) * arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((bigXiH h R.eps H).card : ℝ) ≤ Kc) →
            0 ≤ Kc →
            M4ChiSummedFreeRowH_L_gk h K R M RS →
              MRTUniformityXiL2H h R (2 * Kc * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ)) := by
  obtain ⟨Cg, hCg, hmint⟩ := m4_doorL2_supply_H_L_gk h hh K
  refine ⟨Cg, hCg, ?_⟩
  intro eps heps
  obtain ⟨H₀, hH₀⟩ := hmint eps heps
  refine ⟨H₀, ?_⟩
  intro R hReps hfloor δ Bceil Kc RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han
    hG1 hG2 harc3 hdgate hdrift hceil hXi hKc0 hrow
  have hh1 : 1 ≤ h := hh
  have harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh1 hlo
    nlinarith [h1, harc1]
  have harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * ((h : ℝ) * arcDen 12 H) ^ 2 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh1 hlo
    nlinarith [h1, harc1]
  have hchi : M4ChiSummedBlockMeanSqNH_L_gk h K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_suppliedH_L_gk h K j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummedH_L_gk h K (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidualH h H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  have hcov := m4_cover_assembly_blk2H_L_gk h K hgates hBblk0 hblk2
  refine hH₀ R hReps hfloor Braw Kc Bceil δ M k hgates hBraw0 ?_ hXi hKc0 hceil
  refine m4_sievedDoorSq_of_blk2H_L_gk h K (ℓ := blockLenH h)
    (fun H => by have := hBblk0 H; positivity)
    (fun H q _ _ _ _ => one_le_blockLenH h H q) ?_ ?_ ?_ ?_ hcov
  · intro H q hlo hhi _ _
    have h1 := harc H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh1 hlo
    have hH1 : 1 ≤ H := by
      have : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
      exact_mod_cast this
    exact blockLenH_le h H q hH1
  · intro H q hlo hhi _ _
    exact blockLenH_narrow (R := R) hh1 hlo (harc H hlo hhi)
  · intro H q hlo hhi hq _
    exact blockLenH_drift (R := R) hh1 hlo hq (harc H hlo hhi)
  · intro H hlo hhi
    have hdr := hdrift H hlo hhi
    have hres0 : (0 : ℝ) ≤ strataResidualH h H :=
      strataResidualH_nonneg (one_le_hArcDen_of_regime hh1 hlo)
    have hB := hBcl0 H
    nlinarith [hdr]

/-! ## §6 — the three named extras: the splice, the framed base, the ceiling -/

/-- **THE SPLICED GRADE AT THE INFLATED CAP** (`m4ChiRowGraded_L`, `M4RowLinear.lean:8931`) —
the analytic grade above the door's floor, the absolute grade `4·h·arcDen 12 H` below it. -/
def m4ChiRowGradedH_L (h M : ℕ) (RSbig : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun j H => if doorRowFloorL M ≤ j then RSbig j H else 4 * ((h : ℝ) * arcDen 12 H)

theorem m4ChiRowGradedH_big_L (h M : ℕ) (RSbig : ℕ → ℕ → ℝ) {j : ℕ} (H : ℕ)
    (hj : doorRowFloorL M ≤ j) : m4ChiRowGradedH_L h M RSbig j H = RSbig j H := if_pos hj

theorem m4ChiRowGradedH_small_L (h M : ℕ) (RSbig : ℕ → ℕ → ℝ) {j : ℕ} (H : ℕ)
    (hj : ¬ doorRowFloorL M ≤ j) :
    m4ChiRowGradedH_L h M RSbig j H = 4 * ((h : ℝ) * arcDen 12 H) := if_neg hj

/-- ⟦GATE 4, READ⟧ at the inflated cap: above the floor the spliced grade IS the analytic one. -/
theorem m4ChiRowGradedH_an_L {h M : ℕ} {RSbig : ℕ → ℕ → ℝ} {RSan : ℕ → ℝ}
    (han : ∀ j H : ℕ, doorRowFloorL M ≤ j → RSbig j H ≤ RSan H) :
    ∀ j H : ℕ, doorRowFloorL M ≤ j → m4ChiRowGradedH_L h M RSbig j H ≤ RSan H := by
  intro j H hj
  rw [m4ChiRowGradedH_big_L h M RSbig H hj]
  exact han j H hj

/-- `M4ChiSummedFreeRowBig_L_gk` (`M4RowLinear.lean:8970`) at the inflated cap — the
producer-facing surface: what the socket's producers supply at moduli up to `h·arcDen`. -/
def M4ChiSummedFreeRowBigH_L_gk (h K : ℕ) (R : ChowlaRegime) (M : ℕ) (RSbig : ℕ → ℕ → ℝ) :
    Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ (h : ℝ) * arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloorL M ≤ j → ∀ A : ℕ, 0 < A →
      2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * ((h : ℝ) * arcDen 12 H) * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      ∀ s ≤ L,
        ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s) ≤ RSbig j H

/-- **THE GRADED SPLICE** (`m4_chiSummedFreeRow_of_big_L_gk`, `M4RowLinear.lean:8980`) at the
inflated cap: above the floor the hypothesis fires verbatim, below it the anti-vacuity witness
(3.1) carries the socket at `4·h·arcDen 12 H`. -/
theorem m4_chiSummedFreeRow_of_bigH_L_gk (h K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {RSbig : ℕ → ℕ → ℝ} (hbig : M4ChiSummedFreeRowBigH_L_gk h K R M RSbig) :
    M4ChiSummedFreeRowH_L_gk h K R M (m4ChiRowGradedH_L h M RSbig) := by
  intro H hlo hhi L hLH q hq hqQ j hjL A hA hAj hAsq hAx hAcap s hsL
  by_cases hcase : doorRowFloorL M ≤ j
  · rw [m4ChiRowGradedH_big_L h M RSbig H hcase]
    exact hbig H hlo hhi L hLH q hq hqQ j hjL hcase A hA hAj hAsq hAx hAcap s hsL
  · rw [m4ChiRowGradedH_small_L h M RSbig H hcase]
    exact m4_chiSummedFreeRow_trivialH_L_gk h K R M H hlo hhi L hLH q hq hqQ j hjL A hA hAj hAsq hAx
      hAcap s hsL

/-! **THE FRAMED BASE AT THE INFLATED CAP IS ALREADY LANDED** — `SocketBaseLH`
(`HDoorSupply.lean:535`, the 08/31 producer wave) is `SocketBaseL` with BOTH arc reads inflated,
the x-scale floor included, and `socketBaseLH_of_socketBaseL` beside it.  The signature draft
proposed the same definition under the same name; the aggregate's environment caught the
collision, and the landed one is REUSED here rather than redefined — which also confirms, from an
independent wave, that the x-scale floor moves with the cap. -/

/-- **⟦THE CEILING, MET AT `ρ` AND `h = 2`⟧** — `m4_arith_rs_ceiling_met_rho`
(`M4ArithRho.lean:548`) with the drift gate's residual at `strataResidualH 2 H`.  The grades
stay in the base residual, so `hcancel` leaves `(strataResidualH 2 H / strataResidual H)² ·
108/5 · ρ`; `strataResidualH 2 H = strataResidual H + log 2` exactly and at this page's own
floor `50 ≤ loglog H` (where `strataResidual H ≥ 601`) the ratio² is below `1.00231`, so the
LANDED constant `110525` still pays: `109,994 × 1.00231 < 110,251 ≤ 110525` — at
`Real.pi_lt_d4`; the landed page's `π < 3.15` does NOT fit.  ⚠️ A `×1.0025` margin is exact
arithmetic, not a design freedom; the `h`-general form runs out of slack at `h ≥ 5`, so this is
STATED AT `2`. -/
theorem m4_arith_rs_ceiling_met_rhoH_two {ρ δ₀ : ℝ} (hρ : 0 < ρ) (hρδ : 110525 * ρ ≤ δ₀ ^ 2)
    {H : ℕ} (hL0 : 0 ≤ Real.log (H : ℝ)) (hlam : 50 ≤ Real.log (Real.log (H : ℝ))) :
    96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH 2 H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
      ≤ δ₀ ^ 2 := by
  have hL1 : 1 < Real.log (H : ℝ) := one_lt_log_of_loglog_ge hL0 (by norm_num) hlam
  have hstr : strataResidual H = 1 + 12 * Real.log (Real.log (H : ℝ)) :=
    strataResidual_eq_of_pos (by linarith)
  have hs601 : (601 : ℝ) ≤ strataResidual H := by rw [hstr]; linarith
  have hspos : (0 : ℝ) < strataResidual H := by linarith
  have hsH : strataResidualH 2 H = strataResidual H + Real.log 2 :=
    strataResidualH_eq (by norm_num) (by linarith)
  have hl2 : Real.log 2 < 0.6932 := by
    have := Real.log_two_lt_d9
    linarith
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- ⟦the ratio²⟧ `(s + log 2)² ≤ 1.00231 · s²` at `s ≥ 601`
  have hratio : (strataResidual H + Real.log 2) ^ 2 ≤ 1.00231 * strataResidual H ^ 2 := by
    have h1 : 2 * strataResidual H * Real.log 2 ≤ 1.3864 / 601 * strataResidual H ^ 2 := by
      nlinarith [hs601, hl2, hl2pos]
    have h2 : Real.log 2 ^ 2 ≤ 0.4806 / 601 ^ 2 * strataResidual H ^ 2 := by
      nlinarith [hs601, hl2, hl2pos]
    nlinarith [h1, h2]
  -- ⟦the cancellation⟧ against the base residual's square
  have hcancel : strataResidualH 2 H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
      = 108 / 5 * ρ * ((strataResidual H + Real.log 2) ^ 2 / strataResidual H ^ 2) := by
    rw [hsH, RSanDoorRho]
    field_simp
  have hdiv : (strataResidual H + Real.log 2) ^ 2 / strataResidual H ^ 2 ≤ 1.00231 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hratio]
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq : (1 + 2 * Real.pi) ^ 2 ≤ 53.046 := by nlinarith
  have hrho0 : (0 : ℝ) ≤ 108 / 5 * ρ := by positivity
  have hq0 : (0 : ℝ) ≤ (strataResidual H + Real.log 2) ^ 2 / strataResidual H ^ 2 := by
    positivity
  calc 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH 2 H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
      = 96 * (1 + 2 * Real.pi) ^ 2
          * (strataResidualH 2 H ^ 2 * (108 / 5 * RSanDoorRho ρ H)) := by ring
    _ = 96 * (1 + 2 * Real.pi) ^ 2
          * (108 / 5 * ρ * ((strataResidual H + Real.log 2) ^ 2 / strataResidual H ^ 2)) := by
        rw [hcancel]
    _ ≤ 96 * 53.046 * (108 / 5 * ρ * 1.00231) := by
        have hA : 108 / 5 * ρ * ((strataResidual H + Real.log 2) ^ 2 / strataResidual H ^ 2)
            ≤ 108 / 5 * ρ * 1.00231 := mul_le_mul_of_nonneg_left hdiv hrho0
        have hB : (0 : ℝ) ≤ 108 / 5 * ρ * 1.00231 := by positivity
        have hC : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hA hC, mul_le_mul_of_nonneg_right hsq hB]
    _ ≤ 110525 * ρ := by nlinarith
    _ ≤ δ₀ ^ 2 := hρδ

end Salt.MR
