/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# λ-BV wave 2-S, step F5 (β) — THE AFFINE HEAD AT THE GRADED CROWN (the Entropy side of the
# graded sibling lane)

`Salt.Entropy` cannot import `Salt.MR` (the `xceil` fence), so the affine head
`log_chowla_aff_of_door` (`StrideShell.lean:433`) takes the crown's PAYLOAD as a binder `hcrown`
whose shape is the crown's conclusion verbatim, and its own conclusion FORWARDS that payload
beside the entropy half.  The graded crown (`Salt/MR/StridePairReceiptG.lean`,
`mrtUniformityXiL2AffW_holds_flat_stride_g`) hands the door out at `ρ ≤ 1/(837782·2^11·(ah)²)`;
under an `∃` the door and the entropy half compose only through the SAME witness `Ra`, so the
finer grade must enter the head through its binder and leave through its conclusion — this file
is the landed head with `837782 ↦ 837782 · 2^11` in EXACTLY those two places (the `hcrown` binder
and the conclusion; the entropy half's own pin `1/(838400·(ah)²) ≤ δ₀_aff` is the HEAD's demand
and does not move).  The head's proof never reads the ceiling: the crown's `hρle` is obtained
(`StrideShell.lean:501`, the `obtain … hρle …` from `hcrown A₀'`) and re-packaged untouched
(`:581`, the `refine` package) — `grep -n 837782` on the landed file hits :452 and :461 only —
so the body is the landed body VERBATIM.  Its conclusion is `GradedAffHeadAt a b h A₀`
(`StridePrize.lean:166`) byte for byte — the MR one-liner
`StrideGradeReceipt.log_chowla_aff_of_door_crowned_unslotted_g` checks that identity in the kernel
by `unfold GradedAffHeadAt; exact …`.

HONEST LABEL.  Two declarations; nothing new is proved about the entropy half, which is the
landed one.  Statement-only at the freeze (the head's body is a verbatim copy for the executor;
the unslotted twin is its landed one-liner at the graded name).  Nothing here bears on twin primes.
-/
import Salt.Entropy.Chowla.StrideShell
import Salt.Entropy.Chowla.StrideCircle
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ## F5-β-S3 — THE AFFINE HEAD AT THE GRADED CROWN -/

set_option maxHeartbeats 1600000 in
-- THE HEAD is one large elaboration (the crown's payload, the five-wide reduce leaf and the circle
-- slot all in context while the pin's numerals and the budget witness are discharged); the ceiling
-- is the landed head's own (`StrideShell.lean:397`, 1600000) — the body is that head's, verbatim.
/-- **F5-β-S3 (class C by size, mechanically A — a verbatim copy) — `log_chowla_aff_of_door_g`.**
`log_chowla_aff_of_door` (`StrideShell.lean:433-468`, salt `c80481a1`) with `837782 * ((a * h : ℕ) :
ℝ) ^ 2 ↦ 837782 * 2 ^ 11 * ((a * h : ℕ) : ℝ) ^ 2` at source lines 452 (the `hcrown` binder) and
461 (the conclusion).  BODY: `StrideShell.lean:469-649` VERBATIM — `hρle` is obtained from
`hcrown A₀'` (`:501`, the `obtain`) and re-packaged in the `refine` (`:581`); no other line
mentions `ρ`'s ceiling; the `maxHeartbeats 1600000` is the landed head's. -/
theorem log_chowla_aff_of_door_g (a b h : ℕ) (ha : 0 < a) (hh : 0 < h) (hba : b < a)
    (_hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7)
    (hcm : ∃ C : ℝ, 0 < C ∧ C ≤ (h : ℝ) * (1 + 2 * (2 * Real.log 4)) ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      a ∣ H →
      ((primeWindow eps H).card : ℝ)
          ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ) else 0|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiAff a b h eps H, (1 / (H : ℝ) ^ 2)
                * ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2))
    (hcrown : ∀ A₀' : ℝ,
      ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
        ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀' ≤ A ∧
        ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
          flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
          ∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 11 * ((a * h : ℕ) : ℝ) ^ 2) ∧
            1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
            E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
                * (Real.log (Ra.ω : ℝ) - 1)) ∧
            MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E))
    (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
        flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
        (∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 11 * ((a * h : ℕ) : ℝ) ^ 2) ∧
          1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
          E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
              * (Real.log (Ra.ω : ℝ) - 1)) ∧
          MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E)) ∧
        ∃ δ₀ : ℝ, 0 < δ₀ ∧ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) ≤ δ₀ ∧
          ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ δ₀ → MRTUniformityXiL2AffW h Ra ρ' →
            ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω := by
  -- ⟦(1) THE LEAVES⟧
  obtain ⟨cE, hcE, hcEge, H₀red, hred⟩ := hreduce_holds_final_aff
  obtain ⟨cD3, hcD3, hcD3ge, H₀D3, hD3⟩ := primeWindow_sum_inv_ge_bounded
  obtain ⟨C, hC, hCcap, hcm'⟩ := hcm
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hane : (a : ℝ) ≠ 0 := ne_of_gt haR
  have hhne : (h : ℝ) ≠ 0 := ne_of_gt hhR
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hkeq : ((a * h : ℕ) : ℝ) = (a : ℝ) * (h : ℝ) := by push_cast; ring
  have hkpos : (0 : ℝ) < ((a * h : ℕ) : ℝ) := by rw [hkeq]; positivity
  have hkne : ((a * h : ℕ) : ℝ) ≠ 0 := ne_of_gt hkpos
  have hk1 : (1 : ℝ) ≤ ((a * h : ℕ) : ℝ) := by rw [hkeq]; nlinarith
  -- the cap read: `C ≤ 6.55·h` (`log 4 = 2·log 2 < 1.3863`)
  have hCnum : C ≤ (h : ℝ) * (655 / 100) := by
    refine le_trans hCcap ?_
    have hb : (1 : ℝ) + 2 * (2 * Real.log 4) ≤ 655 / 100 := by rw [hlog4eq]; linarith
    exact mul_le_mul_of_nonneg_left hb hhR.le
  -- ⟦(2)–(3) THE PIN, THE DESIGN CONSTANT AND THE HEAD'S OWN FLOORS⟧
  obtain ⟨ε₀, hε₀def⟩ : ∃ q : ℚ, q = 1 / (500 * ((a * h : ℕ) : ℚ)) := ⟨_, rfl⟩
  obtain ⟨β', hβ'def⟩ : ∃ r : ℝ, r = cD3 / (a : ℝ) * (ε₀ : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have h32 : (3.2 : ℝ) = 16 / 5 := by norm_num
  obtain ⟨A₀', hA₀'def⟩ : ∃ r : ℝ, r = max A₀ (max 162 (max
      (Real.exp (budgetX (ε₀ : ℝ) β'))
      (Real.log (Real.log ((max H₀red H₀D3 : ℕ) : ℝ))))) := ⟨_, rfl⟩
  -- ⟦(4) THE CROWN AT `A₀'`⟧
  obtain ⟨ε, A, hεpos, _hεge, hεeq, hA162, hA₀'A, Ra, hRa, hRb, hReps, hHloB, hdes,
    ρ, Zr, Ecr, hρpos, hρle, hZr1, hZr102, hEcr0, hEcrle, hdoorC⟩ := hcrown A₀'
  have hεε₀ : ε = ε₀ := hεeq.trans hε₀def.symm
  have hA₀le : A₀ ≤ A :=
    le_trans (by rw [hA₀'def]; exact le_max_left _ _) hA₀'A
  have hXA : Real.exp (budgetX (ε₀ : ℝ) β') ≤ 3.2 * A := by
    have h1 : Real.exp (budgetX (ε₀ : ℝ) β') ≤ A := by
      refine le_trans ?_ hA₀'A
      rw [hA₀'def]
      exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    rw [h32]; linarith
  have hnatA : Real.log (Real.log ((max H₀red H₀D3 : ℕ) : ℝ)) ≤ 3.2 * A := by
    have h1 : Real.log (Real.log ((max H₀red H₀D3 : ℕ) : ℝ)) ≤ A := by
      refine le_trans ?_ hA₀'A
      rw [hA₀'def]
      exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    rw [h32]; linarith
  -- ⟦THE PIN'S NUMERALS⟧
  have herR : (ε : ℝ) = 1 / (500 * ((a * h : ℕ) : ℝ)) := by
    rw [hεeq]; push_cast; ring
  have herpos : (0 : ℝ) < (ε : ℝ) := by rw [herR]; positivity
  have herk : (ε : ℝ) * ((a * h : ℕ) : ℝ) = 1 / 500 := by rw [herR]; field_simp
  have herah : (ε : ℝ) * ((a : ℝ) * (h : ℝ)) = 1 / 500 := by rw [← hkeq]; exact herk
  have her500 : (ε : ℝ) ≤ 1 / 500 := by
    rw [herR]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have her32 : (ε : ℝ) ≤ 1 / 32 := by linarith
  have herhalf : (ε : ℝ) ≤ 1 / 2 := by linarith
  have hepsa : (ε : ℝ) * (a : ℝ) ≤ 1 / 500 := by
    nlinarith [herah, mul_nonneg (mul_pos herpos haR).le (by linarith : (0:ℝ) ≤ (h:ℝ) - 1)]
  -- the reduce's GATE, at `64` (not `32`)
  have hεcE : (ε : ℝ) * (a : ℝ) * (h : ℝ) ≤ cE / (64 * Real.log 4) := by
    rw [show (ε : ℝ) * (a : ℝ) * (h : ℝ) = (ε : ℝ) * ((a : ℝ) * (h : ℝ)) by ring, herah,
      le_div_iff₀ (by positivity), hlog4eq]
    linarith
  -- the two `ε`-pin arms of the budget witness
  have hε_D3 : (ε : ℝ) ≤ cD3 / (a : ℝ) / 16 := by
    rw [div_div, le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) * 16)]
    have hrw : (ε : ℝ) * ((a : ℝ) * 16) = 16 * ((ε : ℝ) * (a : ℝ)) := by ring
    rw [hrw]; linarith
  have hε_D3C : (ε : ℝ) ≤ cD3 / (a : ℝ) / (16 * C) := by
    rw [div_div, le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) * (16 * C))]
    have hrw : (ε : ℝ) * ((a : ℝ) * (16 * C)) = 16 * C * ((ε : ℝ) * (a : ℝ)) := by ring
    rw [hrw]
    have hstep : 16 * C * ((ε : ℝ) * (a : ℝ))
        ≤ 16 * ((h : ℝ) * (655 / 100)) * ((ε : ℝ) * (a : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ (mul_pos herpos haR).le
      linarith
    have heq2 : 16 * ((h : ℝ) * (655 / 100)) * ((ε : ℝ) * (a : ℝ))
        = (1048 / 10) * ((ε : ℝ) * ((a : ℝ) * (h : ℝ))) := by ring
    rw [heq2, herah] at hstep
    linarith
  -- ⟦(5) THE `δ₀` FLOOR⟧ the road's re-mint at `k = a·h`, exact at zero slack
  have hc₀pos : (0 : ℝ) < cD3 / (a : ℝ) / (16 * C) :=
    div_pos (div_pos hcD3 haR) (mul_pos (by norm_num) hC)
  have hδ₀pos : (0 : ℝ) < cD3 / (a : ℝ) / (16 * C) * (ε : ℝ) / 4 :=
    div_pos (mul_pos hc₀pos herpos) (by norm_num)
  have hkey : (5 : ℝ) / (2096 * ((a * h : ℕ) : ℝ)) ≤ cD3 / (a : ℝ) / (16 * C) := by
    rw [div_div, le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) * (16 * C))]
    have hfac : (0 : ℝ) ≤ (5 : ℝ) / (2096 * ((a * h : ℕ) : ℝ)) := by positivity
    have h1 : (5 : ℝ) / (2096 * ((a * h : ℕ) : ℝ)) * ((a : ℝ) * (16 * C))
        ≤ (5 : ℝ) / (2096 * ((a * h : ℕ) : ℝ))
            * ((a : ℝ) * (16 * ((h : ℝ) * (655 / 100)))) := by
      refine mul_le_mul_of_nonneg_left ?_ hfac
      refine mul_le_mul_of_nonneg_left ?_ haR.le
      linarith
    have h2 : (5 : ℝ) / (2096 * ((a * h : ℕ) : ℝ))
        * ((a : ℝ) * (16 * ((h : ℝ) * (655 / 100)))) = 1 / 4 := by
      rw [hkeq]; field_simp; ring
    linarith
  have hδ₀ge : (1 : ℝ) / (838400 * ((a * h : ℕ) : ℝ) ^ 2)
      ≤ cD3 / (a : ℝ) / (16 * C) * (ε : ℝ) / 4 := by
    have hstep : (1 : ℝ) / (838400 * ((a * h : ℕ) : ℝ) ^ 2)
        = (5 : ℝ) / (2096 * ((a * h : ℕ) : ℝ))
            * (1 / (500 * ((a * h : ℕ) : ℝ))) / 4 := by
      field_simp; ring
    rw [hstep, herR]
    have hpos : (0 : ℝ) < 1 / (500 * ((a * h : ℕ) : ℝ)) := by positivity
    gcongr
  -- ⟦THE PACKAGE⟧ the crown's payload forwarded, the entropy half beside it
  refine ⟨ε, A, hεpos, hεeq, hA162, hA₀le, Ra, hRa, hRb, hReps, hHloB, hdes,
    ⟨ρ, Zr, Ecr, hρpos, hρle, hZr1, hZr102, hEcr0, hEcrle, hdoorC⟩,
    cD3 / (a : ℝ) / (16 * C) * (ε : ℝ) / 4, hδ₀pos, hδ₀ge, ?_⟩
  intro ρ' _hρ'pos hρ' hdoor hfail
  have hRe : Ra.eps = ε := hReps
  have hblt : Ra.b < Ra.a := by rw [hRa, hRb]; exact hba
  -- ⟦(6) THE AFFINE DECREMENT AT TAO'S RANGE⟧
  obtain ⟨H, hlo, hhi, hdvd, hMI⟩ := entropy_decrementAff Ra.toChowlaRegime
  have hlo' : Ra.Hlo ≤ H := le_trans (Nat.le_mul_of_pos_left _ Ra.ha) hlo
  have hH4 : 4000000 ≤ H := le_trans Ra.hHlo_floor hlo'
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow Ra.eps H : liouvilleWindow H ; logMeasureAff Ra.a Ra.x Ra.ω]
      ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
    rw [← mutualInfo_window_comm_aff Ra.toChowlaRegime H]; exact hMI
  have hH₀ : max H₀red H₀D3 ≤ H :=
    le_trans (le_trans (nat_le_flatDesignBase (max H₀red H₀D3) A hnatA) hHloB) hlo'
  have hepscR : (Ra.eps : ℝ) * (Ra.a : ℝ) * (h : ℝ) ≤ cE / (64 * Real.log 4) := by
    rw [hRe, hRa]; exact hεcE
  -- the COUNT slack `64·a ≤ ε·H`, paid by the regime's own coprimality floor and `ε ≤ 1/32`
  have hcopR : ((Ra.a : ℕ) : ℝ) ≤ (Ra.eps : ℝ) ^ 2 * ((Ra.Hlo : ℕ) : ℝ) / 2 := by
    exact_mod_cast Ra.hcoprime
  have hHloRR : ((Ra.Hlo : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo'
  have hcountR : (64 : ℝ) * (Ra.a : ℝ) ≤ (Ra.eps : ℝ) * (H : ℝ) := by
    rw [hRe] at hcopR ⊢
    have hEHnn : (0 : ℝ) ≤ (ε : ℝ) * (H : ℝ) := mul_nonneg herpos.le (Nat.cast_nonneg H)
    have h1 : (Ra.a : ℝ) ≤ (ε : ℝ) ^ 2 * (H : ℝ) / 2 := by
      have hmono : (ε : ℝ) ^ 2 * ((Ra.Hlo : ℕ) : ℝ) ≤ (ε : ℝ) ^ 2 * (H : ℝ) :=
        mul_le_mul_of_nonneg_left hHloRR (sq_nonneg _)
      linarith only [hcopR, hmono]
    have h2 : (ε : ℝ) ^ 2 * (H : ℝ) ≤ (1 / 32) * ((ε : ℝ) * (H : ℝ)) := by
      have h3 := mul_le_mul_of_nonneg_right her32 hEHnn
      have h4 : (ε : ℝ) ^ 2 * (H : ℝ) = (ε : ℝ) * ((ε : ℝ) * (H : ℝ)) := by ring
      rw [h4]; exact h3
    linarith only [h1, h2]
  have hfailR : logChowlaFailsAff Ra.a Ra.b h Ra.eps Ra.x Ra.ω := by
    rw [hRa, hRb]; exact hfail
  have hredR := fun (eps : ℚ) (H' x' ω' : ℕ) (hc : Nat.Coprime Ra.a (PH eps H')) =>
    hred Ra.a Ra.b h eps H' x' ω' hh Ra.ha hblt hc
  have hcmR := hcm'
  rw [← hRa, ← hRb] at hcmR
  -- ⟦(7) THE PLAIN SPINE-BUDGET WITNESS AT `cD3/a`⟧
  have hεhalfR : (Ra.eps : ℝ) ≤ 1 / 2 := by rw [hRe]; exact herhalf
  have hε_D3R : (Ra.eps : ℝ) ≤ cD3 / (a : ℝ) / 16 := by rw [hRe]; exact hε_D3
  have hε_D3CR : (Ra.eps : ℝ) ≤ cD3 / (a : ℝ) / (16 * C) := by rw [hRe]; exact hε_D3C
  have hfloorH : budgetFloor (Ra.eps : ℝ)
      (cD3 / (a : ℝ) * (Ra.eps : ℝ) / (144 * Real.log 4)) ≤ H := by
    have hX : Real.exp (budgetX (Ra.eps : ℝ)
        (cD3 / (a : ℝ) * (Ra.eps : ℝ) / (144 * Real.log 4))) ≤ 3.2 * A := by
      rw [hRe, hεε₀, ← hβ'def]; exact hXA
    exact le_trans (budgetFloor_le_flatDesignBase _ _ A hX) (le_trans hHloB hlo')
  obtain ⟨t, g, ht, hg, hgle, hbud1⟩ :=
    hbudget1_witness Ra.toChowlaRegime H (cD3 / (a : ℝ)) C (div_pos hcD3 haR) hC
      hεhalfR hε_D3R hε_D3CR hhi hfloorH
  have hbudget1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (cD3 / (a : ℝ) / (16 * C) * (Ra.eps : ℝ))
        + C * ((H : ℝ) / Real.log (H : ℝ)) * (Ra.eps : ℝ) ^ 2
        + shellError Ra.toChowlaRegime H t g
            ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))))
      ≤ cD3 / (4 * (Ra.a : ℝ)) * ((Ra.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) := by
    have heq : cD3 / (4 * (Ra.a : ℝ)) = cD3 / (a : ℝ) / 4 := by
      rw [hRa, div_div]; ring
    rw [heq]; exact hbud1
  have hbudget2 : ρ' < cD3 / (a : ℝ) / (16 * C) * (Ra.eps : ℝ) := by
    rw [hRe]
    have hp : (0 : ℝ) < cD3 / (a : ℝ) / (16 * C) * (ε : ℝ) := mul_pos hc₀pos herpos
    linarith only [hρ', hp]
  -- ⟦(8) THE CORE⟧
  exact spine_False_core_xi_sq_aff h hh Ra hblt hdoor cE hcE H₀red hredR cD3 hcD3 H₀D3 hD3
    C hC hcmR H hdvd hlo hhi hH₀ hepscR hcountR t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) (cD3 / (a : ℝ) / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfailR

/-! ## F5-β-N11 — THE DISCHARGE: the graded head without its slot -/

/-- **F5-β-N11 (class A) — the graded affine head UNSLOTTED.**  `log_chowla_aff_of_door_unslotted`
(`StrideCircle.lean:1090-1114`) with the ceiling at `837782 * 2 ^ 11` in `hcrown` and the conclusion
(source lines 1098, 1107); the body is the landed one-liner at the graded head, LANDED AT THE
FREEZE as the shape control of the substitution (it elaborates iff the graded head's binder and
conclusion are the graded crown's and `GradedAffHeadAt`'s text). -/
theorem log_chowla_aff_of_door_unslotted_g (a b h : ℕ) (ha : 0 < a) (hh : 0 < h) (hba : b < a)
    (hgcd : Nat.gcd (b + h) a ∣ h)
    (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7)
    (hcrown : ∀ A₀' : ℝ,
      ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
        ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀' ≤ A ∧
        ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
          flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
          ∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 11 * ((a * h : ℕ) : ℝ) ^ 2) ∧
            1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
            E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
                * (Real.log (Ra.ω : ℝ) - 1)) ∧
            MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E))
    (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
        flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
        (∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 11 * ((a * h : ℕ) : ℝ) ^ 2) ∧
          1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
          E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
              * (Real.log (Ra.ω : ℝ) - 1)) ∧
          MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E)) ∧
        ∃ δ₀ : ℝ, 0 < δ₀ ∧ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) ≤ δ₀ ∧
          ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ δ₀ → MRTUniformityXiL2AffW h Ra ρ' →
            ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω := by
  exact log_chowla_aff_of_door_g a b h ha hh hba hah7
    (circle_method_estimate_sq_bounded_aff a b h ha hh hgcd (2 * Real.log 4) (by positivity))
    hcrown A₀

end Salt.Entropy.Chowla
