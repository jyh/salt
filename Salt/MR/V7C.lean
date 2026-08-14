/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RegisterCompose

/-!
# `V7C` — ⟦THE `T₀`-ARM⟧: `logChowla2_ineffective_v6`'s SECOND RIDER, DISCHARGED

`logChowla2_ineffective_v6` (`RegisterCompose:345`) carries five inner riders.  The second is

  `T₀ ≤ exp(√(flatDesignBase A)/2)`

— the socket tolerance `S13CapFloor.capfloor_T0_Tann_sharp` really needs.  `RIDER-TRACE`
established that `T₀` has **no effective ceiling** in the corpus (its VK leg bottoms out at
`zeta_zero_free_strip_height`, `RiderTrace:54-92`), so the rider cannot be discharged by
computing `T₀`.

⟦THE ROUTE⟧ it does not have to be.  In `v6`'s own proof the six crossing constants — `T₀`
among them — are minted at `RegisterCompose:368` **BEFORE** the design constant `A` is chosen
at `:373`; `A` is a `max` over five arms, each an absorption threshold.  `T₀` is a fixed real,
so it may be made a **sixth arm**.  Then `T₀ ≤ A`, and the tolerance is a THREE-DEEP
exponential tower in `A`, so it clears with two whole exponentials to spare.  No numeric value
of `T₀` is needed, wanted, or used.

⟦THE MEASURED MARGIN⟧ the design block's charter said the corpus's floor "clears by two
exponential levels".  That is TRUE and conservative; §1 measures the margin exactly and
proves both halves:

* `t0_arm_three_levels` — `exp(exp(exp T₀)) ≤ exp(√(flatDesignBase A)/2)` for every `T₀ ≤ A`
  and every `A ≥ 162`: **THREE exponential levels of headroom**, not two.
* `t0_arm_four_levels_fails` — the FOURTH level breaks, at the design floor and at every `A`
  above it: `exp(√(flatDesignBase A)/2) < exp(exp(exp(exp A)))` for all `A ≥ 162`, witnessed
  at the extremal admissible `T₀ = A`.  So three is exact, not a floor.

The reason is visible in the arithmetic: `√(flatDesignBase A) ≥ e^{e^{3.2A}/2}`, so the
tolerance is `≥ exp(e^{e^{3.2A}/2}/2)` — a tower of height 3 over `A` — while the demand
`T₀ ≤ A` sits at height 0.  The fourth level would ask `e^{e^{A}} ≤ e^{3.2A}/2`, doubly
exponential against singly exponential, and that is false for every `A ≥ 162`.

⟦WHAT THIS FILE DELIVERS⟧ `logChowla2_ineffective_v6_T0arm`: `v6` verbatim with the `T₀`
arrow **GONE** from the inner list — four riders, not five.  Byte-for-byte additive: `v6`
itself is untouched and remains citable.  This is the form the `v7` mint (node V7-E) consumes;
this file does NOT mint `v7`.

**PURELY ADDITIVE.**  No landed declaration is touched.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla
open scoped BigOperators

/-! ## §1 — ⟦THE TOLERANCE ARITHMETIC⟧ the margin, measured -/

/-- `√(flatDesignBase A) ≥ e^{e^{3.2A}/2}` — the ceiling's floor, square-rooted. -/
theorem flatDesignBase_sqrt_ge (A : ℝ) :
    Real.exp (Real.exp (3.2 * A) / 2) ≤ Real.sqrt ((flatDesignBase A : ℕ) : ℝ) := by
  have hD : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    rw [flatDesignBase]; exact Nat.le_ceil _
  have hsq : Real.exp (Real.exp (3.2 * A) / 2) ^ 2 = Real.exp (Real.exp (3.2 * A)) := by
    rw [sq, ← Real.exp_add]; ring_nf
  calc Real.exp (Real.exp (3.2 * A) / 2)
      = Real.sqrt (Real.exp (Real.exp (3.2 * A))) := by
        rw [← hsq, Real.sqrt_sq (Real.exp_nonneg _)]
    _ ≤ Real.sqrt ((flatDesignBase A : ℕ) : ℝ) := Real.sqrt_le_sqrt hD

/-- ⟦TWO LEVELS⟧ `2·e^{e^{A}} ≤ e^{e^{3.2A}/2}` at `A ≥ 162` — the engine of the margin: the
inner gap `e^{3.2A} ≥ 357·e^{A}` is already enough to eat a whole exponential and a factor 2. -/
theorem t0_arm_two_levels {A : ℝ} (hA : 162 ≤ A) :
    2 * Real.exp (Real.exp A) ≤ Real.exp (Real.exp (3.2 * A) / 2) := by
  have hexpA : A + 1 ≤ Real.exp A := Real.add_one_le_exp A
  have h22 : 2.2 * A + 1 ≤ Real.exp (2.2 * A) := Real.add_one_le_exp _
  have hexpApos : (0 : ℝ) < Real.exp A := Real.exp_pos _
  have hsplit : Real.exp (3.2 * A) = Real.exp A * Real.exp (2.2 * A) := by
    rw [← Real.exp_add]; ring_nf
  have h357 : (357 : ℝ) ≤ Real.exp (2.2 * A) := by linarith
  have h163 : (163 : ℝ) ≤ Real.exp A := by linarith
  have hprod : 357 * Real.exp A ≤ Real.exp A * Real.exp (2.2 * A) := by
    nlinarith [hexpApos, h357]
  have hkey : Real.exp A + 1 ≤ Real.exp (3.2 * A) / 2 := by
    rw [hsplit]; linarith
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc 2 * Real.exp (Real.exp A)
      ≤ Real.exp 1 * Real.exp (Real.exp A) := by
        nlinarith [Real.exp_pos (Real.exp A)]
    _ = Real.exp (Real.exp A + 1) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (Real.exp (3.2 * A) / 2) := Real.exp_le_exp.mpr hkey

/-- **⟦THE MARGIN, MEASURED⟧** the socket tolerance clears `T₀` by **THREE** exponential
levels: `exp(exp(exp T₀)) ≤ exp(√(flatDesignBase A)/2)` for every `T₀ ≤ A` and `A ≥ 162`.
The design block's charter claimed two; three is what the bytes give. -/
theorem t0_arm_three_levels {A T : ℝ} (hA : 162 ≤ A) (hT : T ≤ A) :
    Real.exp (Real.exp (Real.exp T))
      ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) := by
  have hmono : Real.exp (Real.exp T) ≤ Real.exp (Real.exp A) :=
    Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hT)
  have h2 := t0_arm_two_levels hA
  have hs := flatDesignBase_sqrt_ge A
  exact Real.exp_le_exp.mpr (by linarith)

/-- **⟦THE `T₀` RIDER, DISCHARGED FROM THE ARM⟧** `T₀ ≤ A` and `162 ≤ A` give the socket
tolerance outright — the level-0 consequence of `t0_arm_three_levels`. -/
theorem t0_arm_le_tolerance {A T : ℝ} (hA : 162 ≤ A) (hT : T ≤ A) :
    T ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) := by
  have a1 : T ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have a2 : Real.exp T ≤ Real.exp (Real.exp T) := Real.exp_le_exp.mpr a1
  have a3 : Real.exp (Real.exp T) ≤ Real.exp (Real.exp (Real.exp T)) :=
    Real.exp_le_exp.mpr a2
  have := t0_arm_three_levels hA hT
  linarith

/-- **⟦THE MARGIN IS EXACTLY THREE⟧** the FOURTH exponential level breaks — at the design
floor AND at every `A` above it: `exp(√(flatDesignBase A)/2) < exp(exp(exp(exp A)))` for all
`A ≥ 162`, witnessed at the extremal admissible `T₀ = A`.  The gate is `e^{e^{A}}` against
`e^{3.2A}/2`, doubly exponential against singly exponential.  So `t0_arm_three_levels` is
SHARP in tower height, not merely true. -/
theorem t0_arm_four_levels_fails {A : ℝ} (hA : 162 ≤ A) :
    Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2)
      < Real.exp (Real.exp (Real.exp (Real.exp A))) := by
  refine Real.exp_lt_exp.mpr ?_
  -- ⟦THE CEILING, FROM ABOVE⟧ `flatDesignBase A = ⌈E⌉₊ ≤ E + 1 ≤ E²`, `E = e^{e^{3.2A}}`
  have hE1 : (1 : ℝ) ≤ Real.exp (3.2 * A) := by
    have h := Real.add_one_le_exp (3.2 * A); linarith
  have hE2 : (2 : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by
    have h := Real.add_one_le_exp (Real.exp (3.2 * A)); linarith
  have hD : ((flatDesignBase A : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) ^ 2 := by
    rw [flatDesignBase]
    have h := Nat.ceil_lt_add_one (Real.exp_pos (Real.exp (3.2 * A))).le
    nlinarith [h, hE2, sq_nonneg (Real.exp (Real.exp (3.2 * A)) - 2)]
  have hEnn : (0 : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := (Real.exp_pos _).le
  have hsqrt : Real.sqrt ((flatDesignBase A : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by
    have h := Real.sqrt_le_sqrt hD
    rwa [Real.sqrt_sq hEnn] at h
  -- ⟦THE FOURTH LEVEL⟧ `3.2A ≤ e^{A}` at `A ≥ 162`, off `e^{A} ≥ (A/2 + 1)²`
  have hhalf : A / 2 + 1 ≤ Real.exp (A / 2) := Real.add_one_le_exp _
  have hsplit : Real.exp A = Real.exp (A / 2) * Real.exp (A / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hlin : 3.2 * A ≤ Real.exp A := by
    rw [hsplit]; nlinarith [hhalf, hA, Real.exp_pos (A / 2)]
  have hstep : Real.exp (3.2 * A) ≤ Real.exp (Real.exp A) := Real.exp_le_exp.mpr hlin
  have hstep2 : Real.exp (Real.exp (3.2 * A)) ≤ Real.exp (Real.exp (Real.exp A)) :=
    Real.exp_le_exp.mpr hstep
  have hpos : (0 : ℝ) < Real.exp (Real.exp (Real.exp A)) := Real.exp_pos _
  linarith

/-! ## §2 — ⟦THE `T₀`-ARMED TERMINAL⟧ `v6` with the rider gone

Body verbatim from `RegisterCompose.logChowla2_ineffective_v6` (`:345-447`) with exactly two
changes: `T₀` is prepended to the design constant's `max` (each of the five landed absorption
proofs therefore ends in one extra `le_max_right`), and the `T₀` arrow is discharged from
inside by §1 instead of being asked of the caller. -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 1600000 in
-- Same cause as `v6`: the `∃`-prefix and the window discharges re-elaborate the conclusion.
/-- **⟦THE INEFFECTIVE LIMIT, `T₀`-ARMED⟧** (`logChowla2_ineffective_v6_T0arm`) —
`logChowla2_ineffective_v6` with its SECOND inner rider **discharged**.

⟦THE SURVIVING LIST⟧ outer: NOTHING.  Inner, **four** items (was five):

* `e^{-100} ≤ cs` — node V7-B.
* ~~`T₀ ≤ exp(√(flatDesignBase A)/2)`~~ — **GONE**, this theorem.
* `e^{-100} ≤ Ks` — node V7-A.
* `XCeilRiderStrict ε g` — the caller's own request, node V7-D.
* the `K_vt` cushion — the Siegel-genre core, the honest one (KVT-1…4).

⟦HOW⟧ `T₀` is minted before the design constant `A` and is `A`-independent, so it joins `A`'s
`max` as a sixth arm; §1 then clears it by three exponential levels
(`t0_arm_le_tolerance`).  The discharge needs NO effective ceiling on `T₀` — which is what
makes it available at all, since `RIDER-TRACE` proved no such ceiling exists in the corpus.

`v6` is untouched and remains citable; this is the form node V7-E's mint consumes. -/
theorem logChowla2_ineffective_v6_T0arm (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (Real.exp (-100) ≤ cs →
        Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
              + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
            ≤ Real.log (R.Hhi : ℝ) / 4 →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  -- ⟦THE REPAIRED CO-FACTOR SUPPLY⟧ its four Skolem constants, minted outside everything
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ := cofkR_cofactorSupply_L_gk
  obtain ⟨Awin, -, hband⟩ := s16_bandLaneWinL_holdsU
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40, hmainU⟩ :=
    logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist Awin hband
  -- ⟦THE DESIGN CONSTANT, WITH THE `T₀`-ARM⟧ chosen above all five landed thresholds AND
  -- above `T₀` itself — legal for the same reason the other five arms are: every one of the
  -- six constants is minted BEFORE the lever, `T₀` at the `cqhoist` obtain just above.
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max T₀
      (max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
        (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ)))) := ⟨_, rfl⟩
  have hT₀A : T₀ ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hA162 : (162 : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)
  have hA₀A : A₀ ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)
  have hAwinA : Awin ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)) (le_max_right _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
      (le_max_left _ _)) (le_max_right _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _) (le_max_right _ _))
      (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
    have h2 : Real.exp (3.2 * A) / 10 + 1 ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
      Real.add_one_le_exp _
    linarith
  have hopq : Hopq ≤ flatDesignBase A := by
    have h2 : Real.exp (3.2 * A) + 1 ≤ Real.exp (Real.exp (3.2 * A)) := Real.add_one_le_exp _
    have hR : ((Hopq : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by linarith
    have hceil := le_trans hR (Nat.le_ceil (Real.exp (Real.exp (3.2 * A))))
    rw [flatDesignBase]; exact_mod_cast hceil
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, hCt, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hKw
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A, hKvt0, ?_⟩
  intro hcs hKs g hg
  -- ⟦THE `T₀` RIDER, DISCHARGED⟧ §1's arm at the design constant's own sixth `max` slot
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq hcs (by rw [hbase hopq]; exact hT₀) hKs g hg
  refine ⟨R, hReps, by rw [hHlo]; exact hbase hopq, hRg, hRtow, hdes, hwin, ?_⟩
  intro hKvtcush
  -- ⟦ITEM 3, DISCHARGED⟧ the base-scale cap at `K = KlevF A`
  have heps500 : (1 : ℚ) / 500 ≤ R.eps := by rw [hReps]; exact hεpin
  have hxceil : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [hReps]; exact hRx
  -- ⟦RULING 9, DISCHARGED⟧ the co-factor supply at the repaired ladder
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA26
  have heps500R : (1 : ℝ) / 500 ≤ (R.eps : ℝ) := by
    rw [hReps]
    have h := (Rat.cast_le (K := ℝ)).mpr hεpin
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
    exact h
  have h518 : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by nlinarith [hdes, hA162]
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA162
  have hthrgate : cofkRThr Cq Cb Xsk Y0 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    linarith [hthrA, hlo, hexp1]
  have hcofsupply : S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) :=
    hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush
  exact hfire2 hcofsupply
    (s16_baseScaleCap96_L_at_klevF hA26 (flatDoorM_one_le hA26) heps500 hxceil hwin)

end Salt.MR

end
