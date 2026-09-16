/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.DoorReceipt
import Salt.Entropy.Chowla.StrideShell
import Salt.MR.FlatDoorEpsChain
import Mathlib

/-!
# ⟦TIER S — THE DOOR AT THE HEAD'S GRADE, `ε`-FAMILY⟧ (`FlatDoorEpsFamily`)
(council 2026-09-16 ①, the Captain's SECOND word on road F: FREEZE W-ε + E2′, statement-only;
the wave is a THIRD word.  STATEMENT-ONLY AT THE FREEZE: two `sorry`-bodied statements, the
rest PROVED from them or from numerals.  NOT imported by any aggregate.  v1.1, after math's
non-author pass — NO KILL on W, Wc, E2′, E2″; Wc's cap RESTATED (K8), the payload landed in
closed form (N10, math's construction), the lattice-top numeral proved (C7), rung 2 un-priced (N3).
v1.2, after the helm's THIRD-PARTY confirm of v1.1 — CONFIRMED-WITH-REPAIRS, every repair on the
record or the instrument: three docstrings repaired here (Wc's "verbatim", E2″'s bridge pin, C1's
interval); NO statement moved, W byte- and type-identical to v1 and v1.1.  v1.3, at the fire
(the Captain's THIRD word, rung 1 only): ONE import added, `Salt.MR.FlatDoorEpsChain` — the
wave's own file, born empty, because this file's guard refuses a new declaration or import
here; NO statement moved, every type byte-identical to v1.2.)

**HONEST LABEL, FIRST LINE.**  Nothing here bears on twin primes.  What W-ε would land is the
landed `L²` MRT door on the flat family (`mrtUniformityXiL2_holds_flat`, `DoorReceipt.lean:1110`,
UNCONDITIONAL at the ONE pin `ε = 1/500`) at EVERY `0 < ε ≤ 1/500`, on the head's own regime and
at the head's own door threshold — `ρ := δ₀`, the mint `cD3/(16·C)·ε/4` read at the leaves'
pinned witnesses `cD3 = 1/4`, `C = 1 + 4·log 4` — with that threshold's un-rounded FLOOR
`ε/(256·(1 + 4·log 4)) ≤ δ₀` and its GRADE `δ₀ ≤ 500·ε/837782` (the receipt's numeral, scaled)
exported, and the head's slot `∀ ρ ≤ δ₀, door → ¬ logChowla2Fails` carried on the SAME regime.
At `ε := 1/500` the grade is `1/837782` to the digit and the statement REDUCES to the landed
door (`mrtUniformityXiL2_holds_flat_of_epsFamily` below, PROVED from W-ε); this is the zero
level, and it is a kernel control rather than a sentence.  E2′ is then ONE `exact`: the door at
`δ₀` fed to the slot at `δ₀` (`logChowla2_epsFamily_of_flatDoor`, PROVED from W-ε) — the `∀ ε`
arm's conclusion (`EpsFamilyReceipt.lean:42`'s, `logChowla2_epsFamily_of_flatDoor_floor`) with
NO crown and NO `L¹ → L²` step.  Each fixed `ε` still has a CONSTANT margin: the `∃ ε` tripwire
`spine_eps_constant_floor` (`SpineEpsFence.lean:102`) is untouched, W-δ (a grade `→ 0` at fixed
`ε`) is not stated, and the crown `MRTDoorAllGrades` (`∀ R`, `L¹`) stays the minted target.

**WHY `ρ := δ₀` AND NOT A ROUNDED GRADE ON `ρ`** (the corrected statement, h2c's walk §3 and its
own second correction at this freeze): the receipt's grade rounds UP (`1/837782 > 1/837782.7`)
and any consumer's floor on its threshold rounds DOWN, so a door stated at `ρ ≤ 500·ε/837782`
never provably meets a slot `∀ ρ ≤ δ₀'` on another regime — not even with that slot's floor
exported un-rounded (`ε/1675.565 < ε/1675.564`).  The door and the slot are therefore stated at
ONE `δ₀` on ONE regime, which is what the chain proves (the socket hands the door out at
`ρ := δ₀`, `XThread.lean:723`); the floor and the grade are exports ABOUT `δ₀`, never a
substitute for it.

**THE ROUTE (road F, h2c's per-hop walk of 2026-09-15 in the seat record):** the flat road's
eight hops re-cut at generic `ε ≤ 1/500` — the pin `1/500 ≤ ε` enters at ONE site
(`XThread.lean:587`) and is spent by exactly four proofs, each absorbed by an `ε`-dependent floor
the corpus already carries; the head at the leaves' PINNED witnesses (the door-head's device,
`DoorReceipt.lean:1001`, with the three leaf estimates transported by one monotone step each) so
that the mint carries BOTH bounds and the tail (the entropy collision) still fires.  The capped
rung (`…_capped`, `1/(500·8103) ≤ ε` — the lattice top `h = 8103`) is EXACTLY where every helper's
landed `_h`/`_b9` numeral applies as it stands.  The full family (rung 2) is NOT priced here: each
absorption the walk measured holds on a finite range of `ε` and W-ε runs to `ε → 0`, so every cap
becomes an `ε`-dependent term — walked one lift at a time before it is priced (math's N3).
-/

noncomputable section

open scoped BigOperators
open Salt.Entropy.Chowla

namespace Salt.MR

/-! ## §1 — ⟦THE NUMERALS⟧ the mint's floor and grade, as numerals (PROVED) -/

/-- **⟦C1 — THE FLOOR IS BELOW THE GRADE⟧** (`flatDoorMint_floor_le_grade`) — the un-rounded mint
`ε/(256·(1 + 4·log 4))` sits below the receipt's scaled grade `500·ε/837782` for every `ε ≥ 0`:
`837782 ≤ 128000·(1 + 8·log 2)` needs `log 2 ≥ 0.6931465`, and `Real.log_two_gt_d9` gives
`0.6931471803`.  The interval W-ε's `δ₀` lives in is nonempty; at `ε = 1/500` it is
`[1/(128000·(1 + 8·log 2)), 1/837782]`, whose LEFT end is the receipt's own `δ₀` — the receipt
states `δ₀ ∈ (1/837783, 1/837782)` (`DoorReceipt.lean:80`).  (v1.2; v1.1 wrote the interval as
`(1/837782.7, 1/837782]` and called it the receipt's, which it is not — the helm's §6(2).) -/
theorem flatDoorMint_floor_le_grade (ε : ℝ) (hε : 0 ≤ ε) :
    ε / (256 * (1 + 4 * Real.log 4)) ≤ 500 * ε / 837782 := by
  have hlog2gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hlog4eq, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **⟦C2 — THE GRADE AT THE PIN IS THE LANDED NUMERAL⟧** (`flatDoorMint_grade_at_pin`) —
`500·(1/500)/837782 = 1/837782`, the receipt predicate's grade (`MRTDoorReceipt`,
`DoorReceipt.lean:85`), to the digit. -/
theorem flatDoorMint_grade_at_pin :
    500 * (((1 : ℚ) / 500 : ℚ) : ℝ) / 837782 = 1 / 837782 := by
  norm_num

/-! ## §2 — ⟦W-ε⟧ the door at the head's grade, `ε`-family (FROZEN) -/

/-- **⟦W-ε — THE `L²` DOOR ON THE FLAT FAMILY AT EVERY `ε ≤ 1/500`, AT `ρ := δ₀`⟧**
(`mrtUniformityXiL2_holds_flat_epsFamily`, FROZEN) — `mrtUniformityXiL2_holds_flat`
(`DoorReceipt.lean:1110`) with `ε` moved from the `∃`-prefix to a hypothesis `0 < ε ≤ 1/500`,
the door stated AT the head's own threshold `δ₀` (not at some `ρ ≤ 1/837782`), the threshold's
FLOOR `ε/(256·(1 + 4·log 4)) ≤ δ₀` and GRADE `δ₀ ≤ 500·ε/837782` exported, and the head's slot
`∀ ρ ≤ δ₀, MRTUniformityXiL2 R ρ → ¬ logChowla2Fails …` carried on the same regime
(`flat_head_uniform_xceil`'s last conjunct, `XThread.lean:556`).  The regime conjuncts are the
landed door's verbatim: `R.eps = ε`, `R.Hlo = flatDesignBase A`, `162 ≤ A`, `A₀ ≤ A`,
`3.2·A ≤ loglog R.Hlo`.  A consumer wanting `extraFloor ≤ R.Hlo` takes `A₀ := extraFloor` and
`nat_le_flatDesignBase` (`logChowla2_epsFamily_of_flatDoor_floor` does).

Zero level: at `ε := 1/500` the grade is `1/837782` (C2) and the statement reduces to the landed
door — `mrtUniformityXiL2_holds_flat_of_epsFamily` below.  What is NOT exported, on purpose: the
count bound `K`, `β`, `Hopq`, the tower and width conjuncts — the head's other exports, none of
which E2′ or the receipt spend; a later re-cut may add them without moving anything here. -/
theorem mrtUniformityXiL2_holds_flat_epsFamily (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
    (A₀ : ℝ) :
    ∃ (δ₀ A : ℝ), 0 < δ₀ ∧
      (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) ≤ δ₀ ∧ δ₀ ≤ 500 * (ε : ℝ) / 837782 ∧
      162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        MRTUniformityXiL2 R δ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  sorry

/-- **⟦W-ε, CAPPED — THE FIRST RUNG⟧** (`mrtUniformityXiL2_holds_flat_epsFamily_capped`, FROZEN)
— W-ε under the one extra hypothesis `1/(500·8103) ≤ ε`: the lattice top `h = 8103`, the largest
`h : ℕ` with `log h ≤ 9` (`h_le_8103_of_log_le_nine`; `log 8103 ≤ 9` is `flatDoor_cap_lattice_top`
below).  This is EXACTLY the range on which every capped helper of the flat road applies AS
LANDED: the `_b9` twins take `h : ℕ`, `0 < h`, `log h ≤ 9` and `1/(500·h) ≤ ε`, so at `h := 8103`
their binders are this hypothesis and C7 — verbatim for the two that take the rational cap
(`flat_arm_eps_le_h_b9`, `klevF_capNumeral_h_b9`) and through a FOUR-line cast (`1 ≤ 4051500·ε`
in `ℚ`, lifted, then `div_le_iff₀`; ONE `exact_mod_cast` does NOT lift a divided cap) for the
two that take the real one (`flat_arm_budget_le_h_b9`, `flat_witFloor_eq_designBase_h_b9`) —
v1.2, the helm's Q2, each DRIVEN at `h := 8103` in the record's Q5(e) receipt; the
real-`c` helpers (`s15Arm_log_le_scaled`'s `log c ≤ 14`, the count hook's `K ≤ 2^539`) take
`c := ⌈1/(500ε)⌉ ≤ 8103`.  v1 stated the cap as `log(1/(500·ε)) ≤ 9`, which admits a sliver
`ε ∈ [1/(500·e⁹), 1/4051500)`, about 42 units wide in `1/ε`, on which NO natural `h` meets the
twins' binders (math's non-author pass, K8, kernel-checked at `ε = 1/4051541`); the restatement is
math's recommendation (i), adopted at v1.1 — a STRONGER hypothesis, so this rung is implied by
v1's (`flatDoor_cap_restated_in_v1`).  Same conclusion as W-ε, token for token; landing W-ε
discharges this by `mrtUniformityXiL2_holds_flat_epsFamily_capped_of_epsFamily` below. -/
theorem mrtUniformityXiL2_holds_flat_epsFamily_capped (ε : ℚ) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 500) (hcap : (1 : ℚ) / (500 * 8103) ≤ ε) (A₀ : ℝ) :
    ∃ (δ₀ A : ℝ), 0 < δ₀ ∧
      (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) ≤ δ₀ ∧ δ₀ ≤ 500 * (ε : ℝ) / 837782 ∧
      162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        MRTUniformityXiL2 R δ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  sorry

/-! ## §3 — ⟦THE CONTROLS⟧ every consumer and the zero level, PROVED from W-ε (no sorry read) -/

/-- **⟦C3 — THE ZERO LEVEL IS THE LANDED DOOR⟧** (`mrtUniformityXiL2_holds_flat_of_epsFamily`) —
W-ε at `ε := 1/500` yields `mrtUniformityXiL2_holds_flat`'s statement VERBATIM
(`DoorReceipt.lean:1110`): the witness `ρ := δ₀` with `δ₀ ≤ 500·(1/500)/837782 = 1/837782`.
This is the kernel's word that the corrected W-ε reduces to the landed receipt at the pin — the
check the charter-request's K6 got backwards (it read the FLOOR's ordering for the GRADE's). -/
theorem mrtUniformityXiL2_holds_flat_of_epsFamily (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / 500 ≤ ε ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 837782 ∧ MRTUniformityXiL2 R ρ := by
  obtain ⟨δ₀, A, hδ₀, -, hgrade, hA162, hA₀A, R, hReps, hHlo, hdes, hdoor, -⟩ :=
    mrtUniformityXiL2_holds_flat_epsFamily (1 / 500) (by norm_num) le_rfl A₀
  refine ⟨1 / 500, A, by norm_num, le_rfl, hA162, hA₀A, R, hReps, hHlo, hdes, δ₀, hδ₀, ?_,
    hdoor⟩
  rw [flatDoorMint_grade_at_pin] at hgrade
  exact hgrade

/-- **⟦E2′ — THE `∀ ε` ARM FROM THE FLAT DOOR, NO CROWN⟧** (`logChowla2_epsFamily_of_flatDoor`) —
the door at `δ₀` fed to the slot at `δ₀` on the same regime: `hslot δ₀ hδ₀ le_rfl hdoor`.  This is
`logChowla2_epsFamily_of_allGrades` (`EpsFamilyReceipt.lean:42`) with `mrtUniformityXiL2_of_xi`
and the crown REMOVED, on the flat family's own regime conjuncts. -/
theorem logChowla2_epsFamily_of_flatDoor (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500) (A₀ : ℝ) :
    ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧ ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
      3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧ ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨δ₀, A, hδ₀, -, -, hA162, hA₀A, R, hReps, hHlo, hdes, hdoor, hslot⟩ :=
    mrtUniformityXiL2_holds_flat_epsFamily ε hε0 hε A₀
  exact ⟨A, hA162, hA₀A, R, hReps, hHlo, hdes, hslot δ₀ hδ₀ le_rfl hdoor⟩

/-- **⟦E2′ IN E2's OWN SHAPE⟧** (`logChowla2_epsFamily_of_flatDoor_floor`) — the conclusion of
`logChowla2_epsFamily_of_allGrades` (`EpsFamilyReceipt.lean:42`) token for token, with the crown
binder gone: `A₀ := extraFloor` and `nat_le_flatDesignBase` (`StrideShell.lean:83`) at
`loglog extraFloor ≤ extraFloor ≤ A ≤ 3.2·A` (`Real.log_le_self` twice, the bridge's own chain
at `TierSBridge.lean:181–186`, inside `band_Hhi_unbounded_g12b`; v1.2 — v1.1 wrote `:180`, the
line above it, the helm's §6(1)). -/
theorem logChowla2_epsFamily_of_flatDoor_floor (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
    (extraFloor : ℕ) :
    ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨A, hA162, hA₀A, R, hReps, hHlo, -, hfails⟩ :=
    logChowla2_epsFamily_of_flatDoor ε hε0 hε (extraFloor : ℝ)
  refine ⟨R, hReps, ?_, hfails⟩
  rw [hHlo]
  refine nat_le_flatDesignBase extraFloor A ?_
  have hnn : (0 : ℝ) ≤ (extraFloor : ℝ) := Nat.cast_nonneg extraFloor
  have h1 : Real.log (Real.log (extraFloor : ℝ)) ≤ Real.log (extraFloor : ℝ) :=
    Real.log_le_self (Real.log_natCast_nonneg extraFloor)
  have h2 : Real.log (extraFloor : ℝ) ≤ (extraFloor : ℝ) := Real.log_le_self hnn
  linarith

/-- **⟦THE CAPPED RUNG IS IMPLIED BY THE FAMILY⟧**
(`mrtUniformityXiL2_holds_flat_epsFamily_capped_of_epsFamily`) — the first rung's statement from
W-ε by dropping `hcap`; so once W-ε lands, the rung's own proof is this one line. -/
theorem mrtUniformityXiL2_holds_flat_epsFamily_capped_of_epsFamily (ε : ℚ) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 500) (_hcap : (1 : ℚ) / (500 * 8103) ≤ ε) (A₀ : ℝ) :
    ∃ (δ₀ A : ℝ), 0 < δ₀ ∧
      (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) ≤ δ₀ ∧ δ₀ ≤ 500 * (ε : ℝ) / 837782 ∧
      162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        MRTUniformityXiL2 R δ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
          ¬ logChowla2Fails R.eps R.x R.ω :=
  mrtUniformityXiL2_holds_flat_epsFamily ε hε0 hε A₀

/-- **⟦C5 — THE PIN IS INSIDE THE CAPPED RUNG⟧** (`flatDoor_pin_in_cap`) — `1/(500·8103) ≤ 1/500`,
so the zero level `ε = 1/500` is reached by the first rung, not only by the family. -/
theorem flatDoor_pin_in_cap : (1 : ℚ) / (500 * 8103) ≤ 1 / 500 := by
  norm_num

/-- **⟦C7 — THE LATTICE TOP MEETS `log h ≤ 9`⟧** (`flatDoor_cap_lattice_top`) — `log 8103 ≤ 9`,
the `_b9` twins' other binder at `h := 8103` (`8103 < e⁹ = 8103.0839…`, via `Real.exp_one_gt_d9`).
The corpus carries the converse only (`h_le_8103_of_log_le_nine`) and states this one in prose. -/
theorem flatDoor_cap_lattice_top : Real.log (8103 : ℝ) ≤ 9 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h3 : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have h4 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h5 : (2.7182818283 : ℝ) ^ (9 : ℕ) < (Real.exp 1) ^ (9 : ℕ) :=
    pow_lt_pow_left₀ h4 (by norm_num) (by norm_num)
  have h6 : (8103 : ℝ) ≤ (2.7182818283 : ℝ) ^ (9 : ℕ) := by norm_num
  rw [h3]; linarith

/-- **⟦C8 — THE RESTATED CAP SITS INSIDE v1's⟧** (`flatDoor_cap_restated_in_v1`) —
`1/(500·8103) ≤ ε` gives v1's `log(1/(500·ε)) ≤ 9`: the v1.1 rung is IMPLIED by the v1 rung (its
hypothesis is stronger), so nothing that survived math's pass is widened; what is dropped is
exactly the sliver. -/
theorem flatDoor_cap_restated_in_v1 (ε : ℚ) (hε0 : 0 < ε) (hcap : (1 : ℚ) / (500 * 8103) ≤ ε) :
    Real.log (1 / (500 * (ε : ℝ))) ≤ 9 := by
  have hε0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  have h1 : (1 : ℚ) ≤ 4051500 * ε := by
    rw [div_le_iff₀ (by norm_num)] at hcap
    linarith
  have h1R : (1 : ℝ) ≤ 4051500 * (ε : ℝ) := by exact_mod_cast h1
  have hx : (1 : ℝ) / (500 * (ε : ℝ)) ≤ 8103 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc Real.log (1 / (500 * (ε : ℝ))) ≤ Real.log 8103 := Real.log_le_log (by positivity) hx
    _ ≤ 9 := flatDoor_cap_lattice_top

/-! ## §4 — ⟦THE PAYLOAD⟧ the closed-form predicate the wave delivers (math's N10, transcribed) -/

/-- **⟦THE PAYLOAD, CLOSED FORM⟧** (`FlatDoorPayload`) — the predicate on a regime that the wave's
`ε`-chain delivers at the head form: the door at the EXACT mint `R.eps/(256·(1 + 4·log 4))` and
the slot at the same term.  math's construction at its non-author pass (N10; kernel-checked there,
transcribed here and labelled math's): v1 §3.4 wrote the payload as `∃ δ, floor δ ∧ grade δ ∧
door R δ ∧ slot R δ`, which yields `∃ A, ∃ R, ∃ δ` — the wrong quantifier order for W-ε (`δ₀`
before `A`), and since floor ≠ grade the `δ` cannot be moved out in front.  Naming `δ` as the mint
in `R.eps` fixes the order; the head supplies it (a door at `ρ ≤ δ₀` is a door at `δ₀`, the door
being monotone up in `ρ`; the slot is the tail's). -/
def FlatDoorPayload (R : ChowlaRegime) : Prop :=
  MRTUniformityXiL2 R ((R.eps : ℝ) / (256 * (1 + 4 * Real.log 4))) ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ (R.eps : ℝ) / (256 * (1 + 4 * Real.log 4)) → MRTUniformityXiL2 R ρ →
      ¬ logChowla2Fails R.eps R.x R.ω

/-- **⟦C6 — THE CLOSED PAYLOAD COMPOSES TO W-ε⟧**
(`mrtUniformityXiL2_holds_flat_epsFamily_of_payload`) — from the chain-shaped hypothesis
(`∃ A ≥ max 162 A₀, ∃ R` on the flat family with `FlatDoorPayload R`) W-ε's conclusion follows
with `δ₀ :=` the exact mint: the floor by `le_rfl`, the grade by C1.  math's P7
(`probe_closedP_gives_W`), transcribed; its control with the grade mutated to `837783` REFUSES
(that W is FALSE, math's P5).  This is the ONE shape v1 §3.4 said the corpus did not carry; it is
landed here, so the executor's §3.4 step is to deliver `FlatDoorPayload` from the head and apply
this. -/
theorem mrtUniformityXiL2_holds_flat_epsFamily_of_payload (ε : ℚ) (hε0 : 0 < ε) (A₀ : ℝ)
    (hV : ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧ ∃ R : ChowlaRegime, R.eps = ε ∧
      R.Hlo = flatDesignBase A ∧ 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧ FlatDoorPayload R) :
    ∃ (δ₀ A : ℝ), 0 < δ₀ ∧
      (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) ≤ δ₀ ∧ δ₀ ≤ 500 * (ε : ℝ) / 837782 ∧
      162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        MRTUniformityXiL2 R δ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨A, hA162, hA₀A, R, hReps, hHlo, hdes, hdoor, hslot⟩ := hV
  have hε0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  refine ⟨(ε : ℝ) / (256 * (1 + 4 * Real.log 4)), A, by positivity, le_rfl,
    flatDoorMint_floor_le_grade (ε : ℝ) hε0R.le, hA162, hA₀A, R, hReps, hHlo, hdes, ?_, ?_⟩
  · rw [← hReps]; exact hdoor
  · rw [← hReps]; exact hslot

end Salt.MR

end
