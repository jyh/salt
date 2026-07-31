/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey
-/
import Salt.MR.S12FuseCompose
import Salt.MR.S13BandBase

/-!
# ⟦THE SPLIT-HOIST'S PAYOFF⟧ — `S13BandGate.grade` AS AN ORDINARY `M`-FLOOR

`S14Compose`'s frontier records ⟦B5 `grade`⟧: `S13BandGate.grade` asks

  `8·C' ≤ (log 2 · doorRowFloor M)^{s13Aexp − 1/2 + 1/1000}`   (`= …^{2.501}`)

and in every LANDED export the band constant `C'` is quantified AFTER `M`, so the line cannot
be absorbed into an `M`-floor: `M` is chosen before `C'` is revealed.

The seven-link graded split-hoist (`LambdaChiMask` §8 → `M4T0DatumDischarge` §8 → `S11Hoist`
§6 → `S12FuseCompose` §6) removes exactly that obstruction: it exposes the `Aexp`-only
constant `C` before the mass budget and carries the explicit cap

  `C' ≤ Cb · M^{2.1}`,  `Cb` in the top constant block,

whose one analytic step is `S11Hoist.s11_windowMassConst_door_le`.  This file closes the loop.

## Contents

* §1 the grade RHS floor (`s11_grade_rhs_floor`): `(4·10^{10}·M)^{2.501}` sits below the gate's
  right side, off `log 2 > 0.693` and `Adoor M ≥ 2^{36}`;
* §2 ⟦THE ABSORPTION LEMMA⟧ (`s11_grade_absorption`): the `M^{2.1}` cap meets the `M^{2.501}`
  right side at an EXPLICIT `M`-floor — `M₀ = ⌈max 1 (8Cb)^{2.5}⌉ + 1`, i.e. `M₀ = 1 + 1`
  whenever `8·Cb ≤ 1` and never worse than the `Cb^{2.5}` form;
* §3 the terminal (`s11_hband_slot_grade_discharged`): the band slot at `Aexp := s13Aexp` with
  the gate's `grade` line DELIVERED rather than assumed.

⚠ NOT a capstone twin.  `DoorBandBase` remains a hypothesis; this file supplies `grade` and
nothing else.  The `M`-floor is honest: it is a floor, not a proof for all `M ≥ 1`, and the
headroom that makes it finite is the exponent gap `2.501 − 2.1 = 0.401`.
-/

set_option maxRecDepth 8000

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Salt.MR
open Salt.Entropy.Chowla

/-! ## §1 — THE GRADE RHS FLOOR -/

/-- **THE GATE'S RIGHT SIDE, FLOORED** (`s11_grade_rhs_floor`) —
`(4·10^{10}·M)^{2.501} ≤ (log 2 · doorRowFloor M)^{2.501}` for `M ≥ 1`.
`doorRowFloor M = M · Adoor M` and `Adoor M ≥ 2^{36} = 68719476736`, so the inner factor is at
least `0.6931471803 · 68719476736 · M > 4·10^{10}·M`. -/
theorem s11_grade_rhs_floor (M : ℕ) (hM : 1 ≤ M) :
    ((40000000000 : ℝ) * (M : ℝ)) ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
      ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
          ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hAd : (68719476736 : ℝ) ≤ ((Adoor M : ℕ) : ℝ) := by
    have h : 2 ^ 36 ≤ Adoor M := Adoor_ge M
    exact_mod_cast h
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hdr : ((doorRowFloor M : ℕ) : ℝ) = (M : ℝ) * ((Adoor M : ℕ) : ℝ) := by
    rw [doorRowFloor]; push_cast; ring
  refine Real.rpow_le_rpow (by positivity) ?_ (by rw [s13Aexp]; norm_num)
  rw [hdr]
  nlinarith [hAd, hMR, hlog2]

/-! ## §2 — ⟦THE ABSORPTION LEMMA⟧ -/

/-- **⟦THE ABSORPTION⟧** (`s11_grade_absorption`) — given the split-hoist's explicit cap
`C' ≤ Cb·M^{2.1}`, the band gate's `grade` line holds at every `M` above an EXPLICIT floor:

  `M₀ := ⌈(max 1 (8·Cb))^{5/2}⌉₊ + 1`.

The floor is honest and it is finite for one reason only: the gate's exponent
`s13Aexp − 1/2 + 1/1000 = 2.501` exceeds the window's price `2.1`, leaving `M^{0.401}` to
swallow `8·Cb`.  When `8·Cb ≤ 1` the floor collapses to `M₀ = 2`; otherwise it is the
`Cb^{5/2}` form (and `5/2 ≥ 1/0.401 = 2.4938…` is where that exponent comes from). -/
theorem s11_grade_absorption (Cb : ℝ) (hCb : 0 < Cb) :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ (M : ℕ), M₀ ≤ M → ∀ C' : ℝ,
      C' ≤ Cb * (M : ℝ) ^ (2.1 : ℝ) →
        8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
          ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) := by
  refine ⟨⌈(max 1 (8 * Cb)) ^ (2.5 : ℝ)⌉₊ + 1, Nat.le_add_left 1 _, ?_⟩
  intro M hM C' hC'
  have hM1 : 1 ≤ M := le_trans (Nat.le_add_left 1 _) hM
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  set u : ℝ := max 1 (8 * Cb) with hu
  have hu1 : (1 : ℝ) ≤ u := le_max_left _ _
  have hu8 : 8 * Cb ≤ u := le_max_right _ _
  -- ⟦the floor, read back⟧ `u^{5/2} ≤ M`
  have hMu : u ^ (2.5 : ℝ) ≤ (M : ℝ) := by
    have h1 : u ^ (2.5 : ℝ) ≤ (⌈u ^ (2.5 : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈u ^ (2.5 : ℝ)⌉₊ : ℕ) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast le_trans (Nat.le_succ _) hM
    linarith
  -- ⟦the headroom⟧ `8·Cb ≤ M^{0.401}`
  have hkey : 8 * Cb ≤ (M : ℝ) ^ (0.401 : ℝ) := by
    have h1 : (u ^ (2.5 : ℝ)) ^ (0.401 : ℝ) ≤ (M : ℝ) ^ (0.401 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hMu (by norm_num)
    have h2 : (u ^ (2.5 : ℝ)) ^ (0.401 : ℝ) = u ^ (1.0025 : ℝ) := by
      rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ u)]; norm_num
    have h3 : u ≤ u ^ (1.0025 : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num : (1 : ℝ) ≤ 1.0025)
      rwa [Real.rpow_one] at h
    rw [h2] at h1; linarith
  refine le_trans ?_ (s11_grade_rhs_floor M hM1)
  have he : s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000) = 2.501 := by rw [s13Aexp]; norm_num
  have hpow : ((40000000000 : ℝ) * (M : ℝ)) ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
      = (40000000000 : ℝ) ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
        * ((M : ℝ) ^ (2.1 : ℝ) * (M : ℝ) ^ (0.401 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) (by linarith), ← Real.rpow_add hMpos, he]
    norm_num
  rw [hpow]
  have hone : (1 : ℝ) ≤ (40000000000 : ℝ) ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 40000000000)
      (by rw [s13Aexp]; norm_num : (0 : ℝ) ≤ s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
    rwa [Real.one_rpow] at h
  have h21 : (0 : ℝ) ≤ (M : ℝ) ^ (2.1 : ℝ) := by positivity
  have hp0 : (0 : ℝ) ≤ (M : ℝ) ^ (2.1 : ℝ) * (M : ℝ) ^ (0.401 : ℝ) := by positivity
  have hprod : 8 * C' ≤ (M : ℝ) ^ (2.1 : ℝ) * (M : ℝ) ^ (0.401 : ℝ) := by
    calc 8 * C' ≤ 8 * (Cb * (M : ℝ) ^ (2.1 : ℝ)) := by linarith
      _ = (8 * Cb) * (M : ℝ) ^ (2.1 : ℝ) := by ring
      _ ≤ (M : ℝ) ^ (0.401 : ℝ) * (M : ℝ) ^ (2.1 : ℝ) :=
          mul_le_mul_of_nonneg_right hkey h21
      _ = (M : ℝ) ^ (2.1 : ℝ) * (M : ℝ) ^ (0.401 : ℝ) := by ring
  nlinarith [hprod, hone, hp0]

/-! ## §3 — THE TERMINAL: THE BAND SLOT WITH `grade` DELIVERED -/

/-- **⟦`S13BandGate.grade`, DISCHARGED AT AN `M`-FLOOR⟧**
(`s11_hband_slot_grade_discharged`) — the graded split-hoist's band slot at
`Aexp := s13Aexp`, with the gate's third line

  `8·C' ≤ (log 2 · doorRowFloor M)^{s13Aexp − 1/2 + 1/1000}`

now a CONCLUSION rather than a hypothesis, for every `M` above the explicit floor `M₀`.  The
conclusion's body is `S12FuseCompose.m4_fuse_hband_of_bandBase`'s byte for byte.

What this does NOT do: `DoorBandBase` is still a hypothesis (it is a hypothesis everywhere in
the corpus), and the other four lines of `S13BandGate` (`x0_le`, `C1_one`, `err_res`, `block`)
are untouched — `x0_le` is now absorbable for the same reason (`x₀` is in the top block), the
other three are separate items. -/
theorem s11_hband_slot_grade_discharged (hMmu : MmuChiRate) :
    ∃ (x₀ M₀ : ℕ), 1 ≤ M₀ ∧ ∀ (M : ℕ), M₀ ≤ M →
      ∃ C' : ℝ, 0 < C' ∧
        8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
            ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
        ∀ (R : ChowlaRegime) (C₁ Mb : ℕ → ℝ),
          ((∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorBandBase x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (Mb (A + s))) →
            ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q,
                (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                  ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                  ≤ t0BandB (((A + s : ℕ)) : ℝ)
                      (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (Mb (A + s))) := by
  obtain ⟨x₀, Cb, hCb, hband⟩ := m4_fuse_hband_of_bandBase_graded hMmu s13Aexp s13Aexp_pos
  obtain ⟨M₀, hM₀, habs⟩ := s11_grade_absorption Cb hCb
  refine ⟨x₀, M₀, hM₀, ?_⟩
  intro M hM
  obtain ⟨C', hC'pos, hC'le, hbody⟩ := hband M (le_trans hM₀ hM)
  exact ⟨C', hC'pos, habs M hM C' hC'le, hbody⟩

end Salt.MR

end
