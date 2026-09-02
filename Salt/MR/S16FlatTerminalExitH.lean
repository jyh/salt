/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16FlatTerminalLinearH
import Salt.Entropy.Chowla.HloExportFlatH

/-!
# ⟦THE EXIT BELOW THE REGISTER, AT SHIFT `h`⟧ — wave X, parts (iii)/(iv)

`S16FlatTerminalLinearH.m4_second_road_L2_H_gk_flatRoot_L` is in DOOR FORM: it concludes
`MRTUniformityXiL2H h R ρ` at the budget line `ρ = 2·Kb·Bceil + δ/2 + 8·2^k/x`, because when
it landed nothing at shift `h` consumed a door.  `HloExportFlatH` is now that consumer.  This
file composes the two into the `h`-twin of `S16FlatTerminalLinear.m4_second_road_L2_gk_flatRoot_L`
(`:239`) — the terminal register in `¬ Fails` form, at shift `h`.

⟦WHAT THE COMPOSE COST, AND WHY (iii) IS NOT TWO LEMMAS⟧  The commission priced part (iii) as
`h`-twins of `HloExportMRFlatRoot.m4_exit_socket_split_sq_arc_flatRoot` (`:70`) and
`S16FlatTerminalLinear.m4_doorL2_close_split_sq_gk_flatRoot_L` (`:179`).  Those two exist at
`h = 1` because the `h = 1` register is built in the SPLIT form (`a`/`e`, `Bsieve`/`Binsert`) and
must be walked back to the door: the socket unfolds `MRTUniformityXiL2` into the split and the
loop re-closes it.  At shift `h` that walk is already paid — the mint
`m4_doorL2_supply_H_L_gk` delivers the door itself, so the register's conclusion IS the head's
`hdoor` slot.  What remains is one arc-shuffle of floors and one monotonicity step in `ρ`.
⇒ **the interface below the register at `h` is the DOOR, and a door needs no unfolding twin.**

⟦THE FOUR SCALINGS AND NOTHING ELSE⟧  Against the `h = 1` twin (`:239`) this statement moves by:
the two pins of word 8(a) (`1/(500·h) ≤ ε`, `1/(838400·h²) ≤ δ₀`); the conclusion Prop of word 7
(`¬ logChowlaFails h`, never `¬ logChowla2Fails`, which hard-codes shift `1`); the count set of
word 8(c) (`bigXiH h`, `Kb` existential — no numeral moves); and the `0 < h` binder of word 8(d).
TWO further differences are INHERITED from the landed door-form register, not minted here, and
are named so the tripwire is not silently crossed: the five cap reads are at `h · arcDen 12 H`
and the drift residual is `strataResidualH h H` (that is the `h`-family's shape since `#17`), and
the `Cg ≤ 2·10^12` conjunct is absent because the mint exports only `1 ≤ Cg`.  `162 ≤ A₀` and
`162 ≤ A` are kept at the twin's numerals, and `ρ` stays FREE: `2·Kb·Bceil + δ/2 + 8·2^k/x ≤ δ₀`
is a hypothesis here exactly as it is at `h = 1`.

Nothing here bears on twin primes: the exit at shift `h` is conditional on the same socket
(`M4ChiSummedFreeRowH_L_gk h`) and the same door gates its `h = 1` twin is conditional on.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — the floor shuffle -/

/-- The register's own floor absorbed into the cap's opaque arm — `HloExportMRFlatRoot`'s
`flatRootCap_arc` (`:54`, `private` there), restated for this file.  Pure `ℕ` lattice
arithmetic; no shift enters. -/
private lemma flatRootCapH_arc (d p b c f : ℕ) :
    max (max d (max (max p b) c)) f ≤ max d (max (max (max p f) b) c) := by
  omega

/-! ## §1 — the door is monotone in its budget -/

/-- `MRTUniformityXiL2H` is a family of upper bounds by `ρ`, so it weakens upward.  This is the
one step the `h = 1` socket does not need: there the head is applied at `ρ := δ₀` from inside the
split, here the register hands us the door at the budget line and the head wants it at `δ₀`. -/
theorem mrtUniformityXiL2H_mono {h : ℕ} {R : ChowlaRegime} {ρ ρ' : ℝ}
    (hdoor : MRTUniformityXiL2H h R ρ) (hle : ρ ≤ ρ') : MRTUniformityXiL2H h R ρ' := by
  intro H _ hlo hhi
  exact le_trans (hdoor H hlo hhi) hle

/-! ## §2 — THE TERMINAL REGISTER AT SHIFT `h`, IN `¬ Fails` FORM -/

/-- **⟦THE SECOND ROAD'S TERMINAL REGISTER AT SHIFT `h`, ON THE TERMINAL'S LANE — EXIT FORM⟧**
(`m4_second_road_L2_H_gk_flatRoot_L_exit`) — the `h`-twin of
`S16FlatTerminalLinear.m4_second_road_L2_gk_flatRoot_L` (`:239`), composed from the landed
door-form register (`S16FlatTerminalLinearH.lean:1567`) and the flat head at shift `h`
(`HloExportFlatH.lean:210`).

The register supplies `MRTUniformityXiL2H h R (2·Kb·Bceil + δ/2 + 8·2^k/x)`; the budget
hypothesis lifts that to `δ₀` by `mrtUniformityXiL2H_mono`; the head consumes it at `ρ := δ₀`
and concludes `¬ logChowlaFails h R.eps R.x R.ω`.  `Kb` is the head's own count bound, taken as
the register's `Kc` (word 8(c)): the same real serves as the `bigXiH h` count and as the budget
line's coefficient, exactly as at `h = 1`. -/
theorem m4_second_road_L2_H_gk_flatRoot_L_exit (h : ℕ) (hh : 0 < h) (K : ℕ) (A₀ : ℝ)
    (hA₀ : 162 ≤ A₀) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ A β : ℝ) (Hcap Hopq : ℕ), 1 ≤ Cg ∧
      0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧
      1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧ 0 < β ∧
      162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
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
            2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
            M4ChiSummedFreeRowH_L_gk h K R M RS →
              ¬ logChowlaFails h R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hreg⟩ := m4_second_road_L2_H_gk_flatRoot_L h hh K
  obtain ⟨ε, Kb, δ₀, A, β, Hcap, Hopq, hε, hKb, hδ₀, hεpin, hδpin, hβ, _hA26, hA₀A,
    hAge, hCapEq, hhead⟩ :=
      log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat_h h hh A₀
        (by linarith : (26 : ℝ) ≤ A₀)
  obtain ⟨H₀, hH₀⟩ := hreg ε hε
  refine ⟨Cg, ε, Kb, δ₀, A, β, max Hcap H₀, max Hopq H₀, hCg, hε, hKb, hδ₀, hεpin, hδpin, hβ,
    le_trans hA₀ hA₀A, hA₀A, hAge, by rw [hCapEq]; exact flatRootCapH_arc _ _ _ _ _, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hRextra, hRU1, hRg, hcount, hRtow, hRcap, hR⟩ := hhead H₀ U1floor g
  refine ⟨R, hReps, hRU1, hRg, hRtow, le_trans hRcap (by omega), ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  have hdoor := hH₀ R hReps hRextra δ Bceil Kb RS RSan RStr Braw M k j₀ hgates hM hRSan0
    hRStr0 hBraw0 han hG1 hG2 harc3 hdgate hdrift hceil hcount hKb.le hrow
  exact hR δ₀ hδ₀ le_rfl (mrtUniformityXiL2H_mono hdoor hbudget)

/-! ## §3 — the `h = 1` twin law, and the NEGATIVE check the `h = 1` law cannot perform -/

/-- At `h = 1` the door of this file's compose IS the landed `h = 1` door. -/
example (R : ChowlaRegime) (ρ : ℝ) : MRTUniformityXiL2 R ρ = MRTUniformityXiL2H 1 R ρ :=
  mrtUniformityXiL2_eq_xiL2H_one R ρ

/-- At `h = 1` the exit's conclusion Prop IS the landed `h = 1` conclusion. -/
example (eps : ℚ) (x ω : ℕ) : logChowla2Fails eps x ω = logChowlaFails 1 eps x ω := by
  rw [logChowla2Fails_eq_logChowlaFails_one]

/-- At `h = 1` the `ε`-pin of word 8(a) IS the landed `1/500 ≤ ε`. -/
example (ε : ℚ) : 1 / (500 * ((1 : ℕ) : ℚ)) ≤ ε ↔ 1 / 500 ≤ ε := by norm_num

/-- **⟦THE NEGATIVE CHECK⟧** (commission §4, refuter R2's acceptance repair).  The three twin
laws above are the `h = 1` INSTANTIATION, and at `h = 1` the shift is invisible — every one of
them would hold just as well of a statement that had silently dropped the parameter.  What
discriminates the two spellings is a SYMBOLIC `h`: the `h = 1` conclusion Prop `logChowla2Fails`
hard-codes shift `1` in its own definition (`ChowlaFailure.lean:62`) and takes no shift argument,
so the `h = 1` spelling of this wave's conclusion does not even ELABORATE at symbolic `h`, while
the `h`-spelling does.  A green `h = 1` check cannot see that; this can. -/
example (h : ℕ) (R : ChowlaRegime) : Prop := by
  fail_if_success exact ¬ logChowla2Fails h R.eps R.x R.ω
  exact ¬ logChowlaFails h R.eps R.x R.ω

end Salt.MR
