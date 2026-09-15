/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦TIER S — S-4⟧ THE ENTROPY ARROW AT EVERY REGIME (`StrideShellBand`)

**S-4 (desk NE, chartered by the helm 2026-09-14 19:4x under council ⑩'s tempo order) — FROZEN
STATEMENT-ONLY.  HONEST LABEL, FIRST LINE: NO NEW UNCONDITIONAL THEOREM.**  S-4 restates the landed
entropy head `log_chowla_aff_of_door_g12b` (`StrideShellG.lean:320`) with the REGIME quantifier
moved: the landed head proves `door Ra ρ' → ¬ logChowlaFailsAff` at the ONE regime `Ra` it obtains
from the crown's payload `hcrown` (`∃ Ra`); S-4 states the same arrow at EVERY affine regime at the
pin `ε = 1/(500·a·h)` whose lower endpoint clears a design threshold `A₁` (`∀ Ra`), with the
threshold chosen ONCE for every class `b < a` and the grade floor `1/(838400·(a·h)²)` explicit.
The mechanism on `main` is already regime-generic (`spine_False_core_xi_sq_aff`,
`StrideShell.lean:245`); the landed head's proof reads its regime through exactly four facts
(`Ra.a = a`, `Ra.b = b`, `Ra.eps = ε`, `flatDesignBase A ≤ Ra.Hlo` at `A` above the leaves'
threshold) and the structure fields.  Nothing here produces a door: the doors are S-3's
(`Salt/MR/TierSBandU.lean`, one band for every class).  At fixed `z` Tier S is a SECOND PROOF of a
terminal that already lands; E2 is conditional on `MRTDoorAllGrades`, which has no producer; the
`∃ε` tripwire is untouched.  Nothing here bears on twin primes.

⛔ THIS IS NOT the item the QUEUE's Tier S block also calls "S-4" (the plateau argument upgrading
`∃ᶠ N` to `∀`); the helm minted the entropy-arrow bridge as S-4 on desk NE, and the collision is
reported in the freeze, not resolved here.

WHY `∀ Ra` IS CONTENT AND `∀ b` IS NOT.  The landed statement cannot be instantiated at a regime of
the consumer's choosing: its `hcrown` binder demands a regime above EVERY `A₀'`, which no single
`Ra` supplies, and its conclusion's `Ra` is the crown's own.  So the `∀ Ra` form is not derivable
from `main` by any finite move.  The class hoist (`∃ A₁` above `∀ b`) IS derivable from the
per-class form by a finite `max` over `b < a` and `flatDesignBase_mono`; it is stated because the
threshold is `b`-free at the witness (the leaves `hreduce_holds_final_aff` and
`primeWindow_sum_inv_ge_bounded` carry no `b`; the circle constant `C` enters only after the
class is fixed) and because the bridge reads it once against S-3's `∀ b` band.

THE ROUTE (priced in the freeze, NOT fired): the landed head's body (`StrideShellG.lean:356-536`)
with step (4) — `hcrown A₀'` — replaced by `intro b hba hgcd Ra hRa hRb hReps hHloB`, the circle
slot discharged per class by `circle_method_estimate_sq_bounded_aff` under `hgcd`, `A ↦ A₁ :=
max 162 (max (exp (budgetX ε₀ β')) (loglog (max H₀red H₀D3)))`, and the grade floor read directly
(`hδ₀ge` becomes the hypothesis `ρ' ≤ floor`).  No landed declaration moves.
-/
import Salt.Entropy.Chowla.StrideShellG
import Salt.Entropy.Chowla.StridePrize
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ## §0 — the design floor is monotone (class A, PROVED) -/

/-- **⟦S-4 M⟧ (class A, PROVED) — `flatDesignBase` IS MONOTONE.**  `⌈exp (exp (3.2·A))⌉₊` grows
with `A`: `Nat.ceil_mono` over two `Real.exp_le_exp`.  What the bridge and the control below spend
to lower the consumer's `A` to S-4's threshold `A₁`. -/
theorem flatDesignBase_mono {A A' : ℝ} (h : A ≤ A') : flatDesignBase A ≤ flatDesignBase A' := by
  unfold flatDesignBase
  exact Nat.ceil_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith)))

/-! ## §1 — THE STATEMENT: the arrow at every regime at the pin above one threshold -/

set_option maxHeartbeats 1600000 in
-- THE ARROW is one large elaboration (the five-wide reduce leaf and the circle slot both in
-- context while the pin's numerals and the budget witness are discharged); the ceiling is the
-- landed head's own (`StrideShellG.lean:310`, 1600000) — the body is that head's, step (4) gone.
/-- **⟦S-4⟧ THE ENTROPY ARROW AT EVERY REGIME** — `log_chowla_aff_of_door_g12b`'s entropy half
(`StrideShellG.lean:353-355`: `∀ ρ' ≤ δ₀, MRTUniformityXiL2AffW h Ra ρ' → ¬ logChowlaFailsAff a b h
Ra.eps Ra.x Ra.ω`) stated at EVERY `Ra : ChowlaRegimeAff` with `Ra.a = a`, `Ra.b = b`, `Ra.eps =
1/(500·a·h)` and `flatDesignBase A₁ ≤ Ra.Hlo`, for ONE threshold `A₁ ≥ 162` chosen before the class
`b`, at the explicit grade floor `1/(838400·(a·h)²)` (the landed `∃ δ₀ ≥ floor` collapses to it:
the composition reads `δ₀` only through that floor, `StridePrize.lean:353` and `:384`).  The circle
slot is discharged, so the class carries the entropy side's own binder `hgcd : gcd (b + h) a ∣ h`
(`log_chowla_aff_of_door_unslotted_g12b`, `StrideShellG.lean:544`).

What it says that no landed statement says: the arrow does not depend on WHICH regime the crown
built — any regime at the pin above the threshold that carries the door at the floor is a window
where log-Chowla does not fail.  Composed with S-3's band (every `y ∈ [x₀, exp(31·Hhi₀/ε)/a]` at
the same `ω₀`, every class) this is D12's `hwin` for every class over ONE band
(`Salt/MR/TierSBridge.lean`).

Route (module header; not fired): the landed head's body with step (4) removed, `A ↦ A₁`, the
threshold's two reads `hXA`/`hnatA` at `A₁` by `le_max_*`, the circle slot obtained after `intro b`,
`hbudget2 : ρ' < (cD3/a)/(16·C)·ε` from `hρ' ≤ floor ≤ (cD3/a)/(16·C)·ε/4` (the landed `hδ₀ge`),
then steps (6)–(8) verbatim. -/
theorem log_chowla_aff_of_door_at_regime_g12b (a h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9) :
    ∃ A₁ : ℝ, 162 ≤ A₁ ∧
      ∀ b : ℕ, b < a → Nat.gcd (b + h) a ∣ h →
      ∀ Ra : ChowlaRegimeAff, Ra.a = a → Ra.b = b →
        Ra.eps = 1 / (500 * ((a * h : ℕ) : ℚ)) → flatDesignBase A₁ ≤ Ra.Hlo →
        ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) →
          MRTUniformityXiL2AffW h Ra ρ' → ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω := by
  -- the product cap is not read below: the landed head carries it as `_hah9` (census band 4
  -- row 12 — `hCnum`, `hepsa`, `hkey`, `hcountR` are cap-free); it is named by the statement
  have _hcap := hah9
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

/-! ## §2 — the grade composition at an arbitrary regime (the bridge's owed name) -/

set_option exponentiation.threshold 4000 in
/-- **⟦S-4 C⟧ (class B) — THE COMPOSITION `a·Zr·ρ + E ≤ floor` AT AN ARBITRARY REGIME.**  The body
of `log_chowla_aff_composed_of_headG_g12b` (`StridePrize.lean:321-396`) FACTORED: that theorem
takes the graded head's `∃ Ra` package and returns a fresh `∃ Ra`, losing `Ra.x = y`; the bridge
needs the inequality at the regime it holds.  Every fact the landed body reads is a binder here or a
structure field: THE DOOR ARM `a·Zr·ρ ≤ 0.58·floor` from `a ≤ 2310` (the granted binder, council
2026-09-13 A② clause 2), `Zr ≤ 1.02`, the `ρ` cap; THE `E` ARM `E ≤ 0.42·floor` from
`flatDesignBase_ge_pow600 hA162`, `hHlo`, `Ra.hHlohi`, `Ra.hheadroom` (so `2^600 ≤ Ra.x/Ra.ω`),
`regime_logOmega_ge Ra.toChowlaRegime` (`log ω ≥ 129`) and `a·h ≤ 8103`.  Split 0.58/0.42 as landed.
BODY: the source's `:333-396` with `δ₀ := floor` and `hδ₀ge := le_rfl`. -/
theorem affGrade_composes_g12b (a h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9) (ha2310 : a ≤ 2310)
    (Ra : ChowlaRegimeAff) {A : ℝ} (hA162 : 162 ≤ A) (hHlo : flatDesignBase A ≤ Ra.Hlo)
    {ρ Zr E : ℝ} (hρ : 0 < ρ) (hρle : ρ ≤ 1 / (837782 * 2 ^ 12 * ((a * h : ℕ) : ℝ) ^ 2))
    (hZr1 : 1 ≤ Zr) (hZr2 : Zr ≤ 1.02) (hE0 : 0 ≤ E)
    (hEle : E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
        * (Real.log (Ra.ω : ℝ) - 1))) :
    0 < (a : ℝ) * Zr * ρ + E ∧
      (a : ℝ) * Zr * ρ + E ≤ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) := by
  sorry

/-! ## §3 — the conservativity control K1 (PROVED; reads no `sorry`) -/

/-- **⟦S-4 K1⟧ (class A, PROVED) — CONSERVATIVITY: S-4 RECOVERS THE LANDED GRADED HEAD.**  The
`∀ Ra` arrow, taken as a hypothesis with the statement spelled out, together with the crown's
payload `hcrown` (the landed head's own binder, `StrideShellG.lean:334-343`, byte for byte), gives
`GradedAffHeadAt_g12b a b h A₀` (`StridePrize.lean:295`) — the landed head's conclusion — at every
`A₀`: obtain the crown at `max A₀ A₁`, lower its `flatDesignBase A ≤ Ra.Hlo` to `A₁` by
`flatDesignBase_mono`, and take `δ₀ := floor`.  Stated with the hypothesis spelled out rather than
through the `sorry` above, so its axiom audit is the kernel's three. -/
theorem gradedAffHeadAt_g12b_of_at_regime (a b h : ℕ) (ha : 0 < a) (hh : 0 < h) (hba : b < a)
    (hgcd : Nat.gcd (b + h) a ∣ h)
    (hS4 : ∃ A₁ : ℝ, 162 ≤ A₁ ∧
      ∀ b : ℕ, b < a → Nat.gcd (b + h) a ∣ h →
      ∀ Ra : ChowlaRegimeAff, Ra.a = a → Ra.b = b →
        Ra.eps = 1 / (500 * ((a * h : ℕ) : ℚ)) → flatDesignBase A₁ ≤ Ra.Hlo →
        ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) →
          MRTUniformityXiL2AffW h Ra ρ' → ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω)
    (hcrown : ∀ A₀' : ℝ,
      ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
        ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀' ≤ A ∧
        ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
          flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
          ∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 12 * ((a * h : ℕ) : ℝ) ^ 2) ∧
            1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
            E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
                * (Real.log (Ra.ω : ℝ) - 1)) ∧
            MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E))
    (A₀ : ℝ) : GradedAffHeadAt_g12b a b h A₀ := by
  obtain ⟨A₁, _hA₁162, harrow⟩ := hS4
  obtain ⟨ε, A, hεpos, _hεge, hεeq, hA162, hA₀'A, Ra, hRa, hRb, hReps, hHloB, hdes,
    ρ, Zr, E, hρpos, hρle, hZr1, hZr2, hE0, hEle, hdoor⟩ := hcrown (max A₀ A₁)
  have hA₀A : A₀ ≤ A := le_trans (le_max_left _ _) hA₀'A
  have hA₁A : A₁ ≤ A := le_trans (le_max_right _ _) hA₀'A
  have hfloor : flatDesignBase A₁ ≤ Ra.Hlo := le_trans (flatDesignBase_mono hA₁A) hHloB
  have hk : (0 : ℝ) < ((a * h : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos ha hh
  have hpos : (0 : ℝ) < 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) := by positivity
  unfold GradedAffHeadAt_g12b
  exact ⟨ε, A, hεpos, hεeq, hA162, hA₀A, Ra, hRa, hRb, hReps, hHloB, hdes,
    ⟨ρ, Zr, E, hρpos, hρle, hZr1, hZr2, hE0, hEle, hdoor⟩,
    1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2), hpos, le_rfl,
    fun ρ' hρ'pos hρ' hd =>
      harrow b hba hgcd Ra hRa hRb (hReps.trans hεeq) hfloor ρ' hρ'pos hρ' hd⟩

end Salt.Entropy.Chowla
