/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.DoorReceipt
import Salt.Entropy.Chowla.StrideShell
import Mathlib

/-!
# ⟦TIER S — THE DOOR AT THE HEAD'S GRADE, `ε`-FAMILY⟧ (`FlatDoorEpsFamily`)
(council 2026-09-16 ①, the Captain's SECOND word on road F: FREEZE W-ε + E2′, statement-only;
the wave is a THIRD word.  STATEMENT-ONLY AT THE FREEZE: two `sorry`-bodied statements, the
rest PROVED from them or from numerals.  NOT imported by any aggregate.)

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
rung (`…_capped`, `log(1/(500ε)) ≤ 9`) is where every helper's landed `_h`/`_b9` numeral applies
as it stands; the full family lifts eight caps (class A each, the `_b9` twins the precedent).
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
`(1/837782.7, 1/837782]`, the receipt's own (`DoorReceipt.lean:80`). -/
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
— W-ε under the one extra hypothesis `log(1/(500·ε)) ≤ 9`, i.e. `ε ≥ 1/(500·8103)`: the range on
which every capped helper of the flat road applies AS LANDED (`bigXiH_bounded_ceiling_of_pin`'s
`K ≤ 2^539`, `klevF_capNumeral_h`, `s15Arm_log_le_scaled`'s `log c ≤ 14`, the witness's
`c ≤ 1096`/`_b9` caps — the walk §4's eight), so the rung is a transcription of the shift lane's
re-cuts with the twist dropped.  Same conclusion as W-ε, token for token; landing W-ε discharges
this by `mrtUniformityXiL2_holds_flat_epsFamily_capped_of_epsFamily` below.  At the lattice
`ε = 1/(500·h)` the hypothesis is `log h ≤ 9`, the `_b9` twins' own binder. -/
theorem mrtUniformityXiL2_holds_flat_epsFamily_capped (ε : ℚ) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 500) (hcap : Real.log (1 / (500 * (ε : ℝ))) ≤ 9) (A₀ : ℝ) :
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
at `TierSBridge.lean:180`). -/
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
    (hε : ε ≤ 1 / 500) (_hcap : Real.log (1 / (500 * (ε : ℝ))) ≤ 9) (A₀ : ℝ) :
    ∃ (δ₀ A : ℝ), 0 < δ₀ ∧
      (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) ≤ δ₀ ∧ δ₀ ≤ 500 * (ε : ℝ) / 837782 ∧
      162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        MRTUniformityXiL2 R δ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
          ¬ logChowla2Fails R.eps R.x R.ω :=
  mrtUniformityXiL2_holds_flat_epsFamily ε hε0 hε A₀

/-- **⟦THE PIN IS INSIDE THE CAPPED RUNG⟧** (`flatDoor_pin_in_cap`) — `log(1/(500·(1/500))) = 0`,
so the zero level `ε = 1/500` is reached by the first rung, not only by the family. -/
theorem flatDoor_pin_in_cap : Real.log (1 / (500 * (((1 : ℚ) / 500 : ℚ) : ℝ))) ≤ 9 := by
  norm_num

end Salt.MR

end
