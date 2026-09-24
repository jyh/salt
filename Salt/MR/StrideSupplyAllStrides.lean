/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.StrideDoorAllGrades
import Salt.MR.TierSLadder
import Salt.Entropy.Chowla.StrideShellBand
import Mathlib

/-!
# ⟦TIER S — ROAD F, THE STRIDE SUPPLY: `LogChowlaAffSupplyW` AT EVERY STRIDE, TWIST AND CLASS
(ARM S)⟧
(`StrideSupplyAllStrides`)

**THE HONEST LABEL, FIRST.**  Nothing here bears on twin primes.  ARM S does NOT touch the crown
`MRTDoorAllGrades`, its quantifier `∃ H₀ ∀ R`, its `ε`-range or its family; "closer to the crown"
is false of it.  Its terminal (§3) is ELEMENTARY at each fixed `P`: `{n | twinLogWeight P n ≠ 0}`
is the set of `n` with `n(n+2)` coprime to `P` and `Ω(n(n+2))` odd, and Pell periodicity turns one
witness into infinitely many at every fixed `z` with no analytic input (`StridePrizePell.lean`,
`docs/QUEUE.md:1044–1048`).  **NO NEW UNCONDITIONAL THEOREM ABOUT TWIN PRIMES.**

WHAT IS NOW TRUE.  `strideSupplyAllStridesW_holds : StrideSupplyAllStridesW` — the landed per-class
analytic supply `LogChowlaAffSupplyW a b h` (`StridePrize.lean:89`: the log-Chowla non-failure at
the forms `a·n+b`, `a·n+b+h` on a flat regime above every floor) at EVERY stride `a > 0`, twist
`h > 0` and class `b < a` with `gcd(b+h, a) ∣ h`, and NO cap: the landed producer
`logChowlaAffSupplyW_holds` (`StrideGradeReceipt.lean:57`) stops at `log(a·h) ≤ 7`, and the
ladder's crown twin (`TierSLadder.lean:420`) at `P ≤ 2310`.  As a corollary
(`twinLogWeight_support_infinite_all_P`), the direct road's terminal at EVERY sieve level
`P > 0` from landed names, through the generic consumer `zRough_oddOmega_infinite_of_affSupplyW`
(`StridePrize.lean:121`).

THE ROUTE (freeze v1 2026-09-23 §3, every row DRIVEN in scratch at the three axioms before the
wave; the scratch is archived by sha `944a9509fc64` beside the freeze).  S1 —
`log_chowla_aff_of_door_at_regime_uncapped` is S-4's entropy arrow
`log_chowla_aff_of_door_at_regime_g12b` (`StrideShellBand.lean:90–274`) with the binder
`(hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9)` and the line `have _hcap := hah9` DELETED and the body
otherwise byte-identical: the cap is READ NOWHERE in the arrow (the landed original names it
`_hcap`, unused).  S2 — `strideSupplyAllStridesW_of_arrow`: ARM Z (`strideDoorAllGradesW_holds`,
`StrideDoorAllGrades.lean`) at the pin `ε = 1/(500·a·h)`, the grade `ρ = 1/(838400·(a·h)²)` and
the floor `max A₀ A₁` hands the arrow a regime carrying the door at the floor; the arrow returns
`¬ logChowlaFailsAff`; `Ra.toChowlaRegime` closes the supply's `∃ R`.  S3 —
`twinLogWeight_support_infinite_of_supply`: the terminal at every `P > 0`, through
`zRough_oddOmega_infinite_of_affSupplyW` and a `mono` through `twinLogWeight`'s `if` and
`liouville_apply` (the ladder's P6 body, `TierSLadder.lean:420`, with the supply in place of the
crown twin).  Every statement below is token-identical to the freeze's (guard arm B); no landed
declaration moves; the landed capped names are KEPT beside these.

WHAT IS NOT SAID.  The crown still has NO producer and E2's `hcrown` binder
(`EpsFamilyReceipt.lean:42`) STANDS; `docs/QUEUE.md:252` ("E2 stays conditional on
`MRTDoorAllGrades`") is STILL TRUE.  No rate is exported.  The apex is untouched.

⚖️ THE SENTENCES THAT GO FALSE AT THIS LANDING (freeze §4 + addendum 1 L3, the SEVEN sites),
and where each is re-stamped.  (i) `docs/QUEUE.md:627` "the crown gates unbounded `z` only" —
re-stamped there.  (ii) `TierSLadder.lean:412–419` "the general-`P` consumer's only landed
supplier stops at `P ≤ 548`" — re-stamped in that docstring (a comment-only edit; its rebuild cone
is one module).  (iii) the five-levels walk's §4 (seat record) — re-stamped by the freeze author.
(iv) `AffineFork.lean:91–92` "At `a ≥ 2`: NONE — that is wave 2-S" — ALREADY FALSE since the
capped G12b supply (`logChowlaAffSupplyW_holds`) and false without qualification after S;
⚠ RECORDED HERE AND NOT EDITED THERE, because `AffineFork.lean` has 32 downstream modules
(measured at `2d0e2129`) and a comment-only edit would rebuild every one of them for no
kernel content; the re-stamp is owed to that file at its next substantive edit.  (v)
`docs/QUEUE.md:766` "`z ≥ 11` rides on the unproved crown" — re-stamped there.  (vi)
`docs/QUEUE.md:779–781`: its "no producer" clause is discharged; its first clause is the
Captain's naming and gets a dated RIDER, never an edit.  (vii) `docs/QUEUE.md:554`/`:604`
"CO-DEPENDENT ON THE UNPROVED CROWN" — dated riders, the stamps left as written.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
open Salt.TwinBar

/-! ## §1 — S1: THE ENTROPY ARROW WITH ITS CAP BINDER DELETED (S-4's body, byte-identical) -/

namespace Salt.Entropy.Chowla

set_option maxHeartbeats 1600000 in
-- THE ARROW is one large elaboration: the ceiling is S-4's own (`StrideShellBand.lean:67`,
-- `1600000`, itself the landed head's, `StrideShellG.lean:310`) — the body is S-4's with its cap
-- binder gone, so the demand is unchanged.
theorem log_chowla_aff_of_door_at_regime_uncapped (a h : ℕ) (ha : 0 < a) (hh : 0 < h) :
    ∃ A₁ : ℝ, 162 ≤ A₁ ∧
      ∀ b : ℕ, b < a → Nat.gcd (b + h) a ∣ h →
      ∀ Ra : ChowlaRegimeAff, Ra.a = a → Ra.b = b →
        Ra.eps = 1 / (500 * ((a * h : ℕ) : ℚ)) → flatDesignBase A₁ ≤ Ra.Hlo →
        ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) →
          MRTUniformityXiL2AffW h Ra ρ' → ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω := by
  -- ⟦(1) THE LEAVES⟧ both are `b`-free by their statements, so they are obtained before the
  -- class; the circle slot depends on `b` and `hgcd` and is obtained after `intro b`
  obtain ⟨cE, hcE, hcEge, H₀red, hred⟩ := hreduce_holds_final_aff
  obtain ⟨cD3, hcD3, hcD3ge, H₀D3, hD3⟩ := primeWindow_sum_inv_ge_bounded
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
  -- ⟦(2)–(3) THE PIN, THE DESIGN CONSTANT AND THE ONE `b`-FREE THRESHOLD `A₁`⟧
  obtain ⟨ε₀, hε₀def⟩ : ∃ q : ℚ, q = 1 / (500 * ((a * h : ℕ) : ℚ)) := ⟨_, rfl⟩
  obtain ⟨β', hβ'def⟩ : ∃ r : ℝ, r = cD3 / (a : ℝ) * (ε₀ : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have h32 : (3.2 : ℝ) = 16 / 5 := by norm_num
  obtain ⟨A₁, hA₁def⟩ : ∃ r : ℝ, r = max 162 (max
      (Real.exp (budgetX (ε₀ : ℝ) β'))
      (Real.log (Real.log ((max H₀red H₀D3 : ℕ) : ℝ)))) := ⟨_, rfl⟩
  have hA₁162 : (162 : ℝ) ≤ A₁ := by rw [hA₁def]; exact le_max_left _ _
  -- ⟦(4) ⟦REPLACED⟧ the crown call is DELETED — the regime arrives through the binders, and the
  -- two facts that step produced are read off `A₁`'s own `max`
  have hXA₁ : Real.exp (budgetX (ε₀ : ℝ) β') ≤ 3.2 * A₁ := by
    have h1 : Real.exp (budgetX (ε₀ : ℝ) β') ≤ A₁ := by
      rw [hA₁def]; exact (le_max_left _ _).trans (le_max_right _ _)
    rw [h32]; linarith
  have hnatA₁ : Real.log (Real.log ((max H₀red H₀D3 : ℕ) : ℝ)) ≤ 3.2 * A₁ := by
    have h1 : Real.log (Real.log ((max H₀red H₀D3 : ℕ) : ℝ)) ≤ A₁ := by
      rw [hA₁def]; exact (le_max_right _ _).trans (le_max_right _ _)
    rw [h32]; linarith
  -- ⟦THE PIN'S NUMERALS⟧ the `b`-free and circle-free half
  have herR : (ε₀ : ℝ) = 1 / (500 * ((a * h : ℕ) : ℝ)) := by
    rw [hε₀def]; push_cast; ring
  have herpos : (0 : ℝ) < (ε₀ : ℝ) := by rw [herR]; positivity
  have herk : (ε₀ : ℝ) * ((a * h : ℕ) : ℝ) = 1 / 500 := by rw [herR]; field_simp
  have herah : (ε₀ : ℝ) * ((a : ℝ) * (h : ℝ)) = 1 / 500 := by rw [← hkeq]; exact herk
  have her500 : (ε₀ : ℝ) ≤ 1 / 500 := by
    rw [herR]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have her32 : (ε₀ : ℝ) ≤ 1 / 32 := by linarith
  have herhalf : (ε₀ : ℝ) ≤ 1 / 2 := by linarith
  have hepsa : (ε₀ : ℝ) * (a : ℝ) ≤ 1 / 500 := by
    nlinarith [herah, mul_nonneg (mul_pos herpos haR).le (by linarith : (0:ℝ) ≤ (h:ℝ) - 1)]
  -- the reduce's GATE, at `64` (not `32`)
  have hεcE : (ε₀ : ℝ) * (a : ℝ) * (h : ℝ) ≤ cE / (64 * Real.log 4) := by
    rw [show (ε₀ : ℝ) * (a : ℝ) * (h : ℝ) = (ε₀ : ℝ) * ((a : ℝ) * (h : ℝ)) by ring, herah,
      le_div_iff₀ (by positivity), hlog4eq]
    linarith
  have hε_D3 : (ε₀ : ℝ) ≤ cD3 / (a : ℝ) / 16 := by
    rw [div_div, le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) * 16)]
    have hrw : (ε₀ : ℝ) * ((a : ℝ) * 16) = 16 * ((ε₀ : ℝ) * (a : ℝ)) := by ring
    rw [hrw]; linarith
  refine ⟨A₁, hA₁162, ?_⟩
  -- ⟦THE CLASS⟧ and the circle slot at it (the only `b`-dependent leaf)
  intro b hba hgcd Ra hRa hRb hReps hHloB
  obtain ⟨C, hC, hCcap, hcm'⟩ :=
    circle_method_estimate_sq_bounded_aff a b h ha hh hgcd (2 * Real.log 4) (by positivity)
  -- the cap read: `C ≤ 6.55·h` (`log 4 = 2·log 2 < 1.3863`)
  have hCnum : C ≤ (h : ℝ) * (655 / 100) := by
    refine le_trans hCcap ?_
    have hb : (1 : ℝ) + 2 * (2 * Real.log 4) ≤ 655 / 100 := by rw [hlog4eq]; linarith
    exact mul_le_mul_of_nonneg_left hb hhR.le
  have hε_D3C : (ε₀ : ℝ) ≤ cD3 / (a : ℝ) / (16 * C) := by
    rw [div_div, le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) * (16 * C))]
    have hrw : (ε₀ : ℝ) * ((a : ℝ) * (16 * C)) = 16 * C * ((ε₀ : ℝ) * (a : ℝ)) := by ring
    rw [hrw]
    have hstep : 16 * C * ((ε₀ : ℝ) * (a : ℝ))
        ≤ 16 * ((h : ℝ) * (655 / 100)) * ((ε₀ : ℝ) * (a : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ (mul_pos herpos haR).le
      linarith
    have heq2 : 16 * ((h : ℝ) * (655 / 100)) * ((ε₀ : ℝ) * (a : ℝ))
        = (1048 / 10) * ((ε₀ : ℝ) * ((a : ℝ) * (h : ℝ))) := by ring
    rw [heq2, herah] at hstep
    linarith
  -- ⟦(5) THE GRADE FLOOR⟧ the road's re-mint at `k = a·h`, exact at zero slack; here it turns
  -- the statement's own floor `ρ' ≤ 1/(838400·k²)` into the budget's strict cap
  have hc₀pos : (0 : ℝ) < cD3 / (a : ℝ) / (16 * C) :=
    div_pos (div_pos hcD3 haR) (mul_pos (by norm_num) hC)
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
      ≤ cD3 / (a : ℝ) / (16 * C) * (ε₀ : ℝ) / 4 := by
    have hstep : (1 : ℝ) / (838400 * ((a * h : ℕ) : ℝ) ^ 2)
        = (5 : ℝ) / (2096 * ((a * h : ℕ) : ℝ))
            * (1 / (500 * ((a * h : ℕ) : ℝ))) / 4 := by
      field_simp; ring
    rw [hstep, herR]
    have hpos : (0 : ℝ) < 1 / (500 * ((a * h : ℕ) : ℝ)) := by positivity
    gcongr
  intro ρ' _hρ'pos hρ' hdoor hfail
  have hRe : Ra.eps = ε₀ := hReps.trans hε₀def.symm
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
    le_trans (le_trans (nat_le_flatDesignBase (max H₀red H₀D3) A₁ hnatA₁) hHloB) hlo'
  have hepscR : (Ra.eps : ℝ) * (Ra.a : ℝ) * (h : ℝ) ≤ cE / (64 * Real.log 4) := by
    rw [hRe, hRa]; exact hεcE
  -- the COUNT slack `64·a ≤ ε·H`, paid by the regime's own coprimality floor and `ε ≤ 1/32`
  have hcopR : ((Ra.a : ℕ) : ℝ) ≤ (Ra.eps : ℝ) ^ 2 * ((Ra.Hlo : ℕ) : ℝ) / 2 := by
    exact_mod_cast Ra.hcoprime
  have hHloRR : ((Ra.Hlo : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo'
  have hcountR : (64 : ℝ) * (Ra.a : ℝ) ≤ (Ra.eps : ℝ) * (H : ℝ) := by
    rw [hRe] at hcopR ⊢
    have hEHnn : (0 : ℝ) ≤ (ε₀ : ℝ) * (H : ℝ) := mul_nonneg herpos.le (Nat.cast_nonneg H)
    have h1 : (Ra.a : ℝ) ≤ (ε₀ : ℝ) ^ 2 * (H : ℝ) / 2 := by
      have hmono : (ε₀ : ℝ) ^ 2 * ((Ra.Hlo : ℕ) : ℝ) ≤ (ε₀ : ℝ) ^ 2 * (H : ℝ) :=
        mul_le_mul_of_nonneg_left hHloRR (sq_nonneg _)
      linarith only [hcopR, hmono]
    have h2 : (ε₀ : ℝ) ^ 2 * (H : ℝ) ≤ (1 / 32) * ((ε₀ : ℝ) * (H : ℝ)) := by
      have h3 := mul_le_mul_of_nonneg_right her32 hEHnn
      have h4 : (ε₀ : ℝ) ^ 2 * (H : ℝ) = (ε₀ : ℝ) * ((ε₀ : ℝ) * (H : ℝ)) := by ring
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
        (cD3 / (a : ℝ) * (Ra.eps : ℝ) / (144 * Real.log 4))) ≤ 3.2 * A₁ := by
      rw [hRe, ← hβ'def]; exact hXA₁
    exact le_trans (budgetFloor_le_flatDesignBase _ _ A₁ hX) (le_trans hHloB hlo')
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
    have hp : (0 : ℝ) < cD3 / (a : ℝ) / (16 * C) * (ε₀ : ℝ) := mul_pos hc₀pos herpos
    linarith only [hρ', hδ₀ge, hp]
  -- ⟦(8) THE CORE⟧
  exact spine_False_core_xi_sq_aff h hh Ra hblt hdoor cE hcE H₀red hredR cD3 hcD3 H₀D3 hD3
    C hC hcmR H hdvd hlo hhi hH₀ hepscR hcountR t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) (cD3 / (a : ℝ) / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfailR


end Salt.Entropy.Chowla

/-! ## §2 — S2: THE STATEMENT OF RECORD, AND S FROM ARM Z AND THE ARROW -/

namespace Salt.MR

/-- **CANDIDATE S — `StrideSupplyAllStridesW`** (the 09-19 draft's text, unchanged): the landed
supply `LogChowlaAffSupplyW a b h` with the route's class binders and NO cap. -/
def StrideSupplyAllStridesW : Prop :=
  ∀ a b h : ℕ, 0 < a → 0 < h → b < a → Nat.gcd (b + h) a ∣ h → LogChowlaAffSupplyW a b h

/-- **THE ONE OWED ROW, AS A HYPOTHESIS** — S-4's arrow (`log_chowla_aff_of_door_at_regime_g12b`)
with its cap binder deleted, at every `(a, h)`. -/
def S4ArrowUncapped : Prop :=
  ∀ a h : ℕ, 0 < a → 0 < h → ∃ A₁ : ℝ, 162 ≤ A₁ ∧
    ∀ b : ℕ, b < a → Nat.gcd (b + h) a ∣ h →
    ∀ Ra : ChowlaRegimeAff, Ra.a = a → Ra.b = b →
      Ra.eps = 1 / (500 * ((a * h : ℕ) : ℚ)) → flatDesignBase A₁ ≤ Ra.Hlo →
      ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) →
        MRTUniformityXiL2AffW h Ra ρ' → ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω

/-- **S FROM Z AND THE ARROW (class A, PROVED)** — Z at the pin `ε = 1/(500·a·h)` and the grade
floor `1/(838400·(a·h)²)`, above `max A₀ A₁`, hands the arrow a regime carrying the door at the
floor; the arrow returns `¬ logChowlaFailsAff`. -/
theorem strideSupplyAllStridesW_of_arrow (hS4 : S4ArrowUncapped) : StrideSupplyAllStridesW := by
  intro a b h ha hh hba hgcd A₀
  obtain ⟨A₁, _hA₁, harrow⟩ := hS4 a h ha hh
  have hkpos : 0 < a * h := Nat.mul_pos ha hh
  have hkQ1 : (1 : ℚ) ≤ ((a * h : ℕ) : ℚ) := by exact_mod_cast hkpos
  have hεle : (1 : ℚ) / (500 * ((a * h : ℕ) : ℚ)) ≤ 1 / 500 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  obtain ⟨A, hA162, hA₀A, Ra, hRa, hRb, hReps, hHlo, _hdes, hdoor⟩ :=
    strideDoorAllGradesW_holds a b h ha hba hh (1 / (500 * ((a * h : ℕ) : ℚ))) le_rfl hεle
      (1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2)) (by positivity) (max A₀ A₁)
  refine ⟨A, hA162, le_trans (le_max_left _ _) hA₀A, Ra.toChowlaRegime, hHlo, ?_⟩
  have hfloor : flatDesignBase A₁ ≤ Ra.Hlo :=
    le_trans (flatDesignBase_mono (le_trans (le_max_right _ _) hA₀A)) hHlo
  exact harrow b hba hgcd Ra hRa hRb hReps hfloor _ (by positivity) le_rfl hdoor

/-- **THE ARROW HOLDS** — from the cap-free copy above. -/
theorem s4ArrowUncapped_holds : S4ArrowUncapped :=
  fun a h ha hh => log_chowla_aff_of_door_at_regime_uncapped a h ha hh

/-- **S HOLDS, IN SCRATCH, FROM LANDED NAMES AND THE COPIED BODY.** -/
theorem strideSupplyAllStridesW_holds : StrideSupplyAllStridesW :=
  strideSupplyAllStridesW_of_arrow s4ArrowUncapped_holds

/-! ## §3 — S3: THE TERMINAL AT EVERY SIEVE LEVEL (the consumer control of the supply) -/

/-- **CONSUMER CONTROL of S** (the 09-19 draft's `crownNext_Z_terminal`, unchanged) — from
the uncapped supply, the direct road's terminal at EVERY `P > 0`. -/
theorem twinLogWeight_support_infinite_of_supply (hZ : StrideSupplyAllStridesW) (P : ℕ)
    (hP : 0 < P) :
    {n : ℕ | twinLogWeight P n ≠ 0}.Infinite := by
  obtain ⟨k, rfl⟩ : ∃ k, P = k + 1 := ⟨P - 1, by omega⟩
  have hcop : Nat.Coprime (k * (k + 2)) (k + 1) := by
    rw [Nat.coprime_mul_iff_left]
    refine ⟨Nat.coprime_self_add_right.mpr (Nat.coprime_one_right k), ?_⟩
    rw [show k + 2 = (k + 1) + 1 from rfl]
    exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  have hgcd : Nat.gcd (k + 2) (k + 1) ∣ 2 := gcd_dvd_two_of_coprime hcop
  have hsup : LogChowlaAffSupplyW (k + 1) k 2 := hZ (k + 1) k 2 hP two_pos (by omega) hgcd
  have hinf := zRough_oddOmega_infinite_of_affSupplyW hP hcop hsup
  refine hinf.mono ?_
  rintro n ⟨hc, hodd⟩
  simp only [Set.mem_setOf_eq]
  have hn0 : n * (n + 2) ≠ 0 := by
    intro h0; rw [h0] at hodd; simp at hodd
  have hn : n ≠ 0 := by rintro rfl; simp at hn0
  unfold twinLogWeight
  rw [if_pos hc, ArithmeticFunction.liouville_apply hn0, hodd.neg_one_pow]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  norm_num [hnR]

/-- **THE TERMINAL AT EVERY SIEVE LEVEL, IN SCRATCH.** -/
theorem twinLogWeight_support_infinite_all_P (P : ℕ) (hP : 0 < P) :
    {n : ℕ | twinLogWeight P n ≠ 0}.Infinite :=
  twinLogWeight_support_infinite_of_supply strideSupplyAllStridesW_holds P hP

end Salt.MR

end
