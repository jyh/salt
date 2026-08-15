/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.V7B
import Salt.MR.V7C

/-!
# `V7E` — ⟦THE MINT⟧ `logChowla2_ineffective_v7`

`RegisterCompose.logChowla2_ineffective_v6` carries five inner riders.  Two of them were
discharged separately, each against `v6`'s own statement:

* `V7B.logChowla2_ineffective_v6_csarm` — `Real.exp (-100) ≤ cs` GONE from the arrow and
  delivered instead as a prefix conjunct, off the eleven-declaration carry thread that lifts
  the floor from the two leaves (`c_vk = 1/10^8`, `c₀ = 1/10^9`) to the flat terminal
  `logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree`.
* `V7C.logChowla2_ineffective_v6_T0arm` — `T₀ ≤ exp(√(flatDesignBase A)/2)` GONE, by making
  `T₀` a sixth arm of the design constant's `max` (`T₀` is minted before `A` and is
  `A`-independent) and clearing the tolerance by three exponential levels
  (`t0_arm_le_tolerance`).

This file mints the terminal that carries BOTH discharges at once.

⟦WHY NOT A COMPOSE⟧ neither arm can be applied to the other from outside.  `_csarm`'s
`∃`-prefix exports `3 ≤ T₀` and nothing more, so its `T₀` arrow cannot be met by a caller;
symmetrically `_T0arm`'s prefix exports `0 < cs` alone.  Both discharges are facts about
constants the theorem itself mints, so both have to happen INSIDE the terminal construction.
The mint therefore re-runs that construction once: `V7C`'s `T₀`-armed design constant wired
to `V7B`'s `_csfree` terminal consumption.

**PURELY ADDITIVE.**  `logChowla2_ineffective_v6`, `…_v6_csarm` and `…_v6_T0arm` are all
byte-untouched and remain citable.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla
open scoped BigOperators

/-! ## §1 — ⟦THE TERMINAL⟧ both riders discharged inside

Body: `V7B.logChowla2_ineffective_v6_csarm`'s, with `V7C`'s two changes folded in — `T₀`
prepended to the design constant's `max` (so each of the five landed absorption proofs ends
in one extra `le_max_right`), and the `T₀` arrow discharged from inside by
`t0_arm_le_tolerance` instead of being asked of the caller. -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 3200000 in
-- Same cause as `v6`: the `∃`-prefix and the window discharges re-elaborate the conclusion
-- under the raised lever, now with the co-factor supply discharged inside.
/-- **⟦`v6` WITH RIDERS 1 AND 2 DISCHARGED⟧** (`logChowla2_ineffective_v7`) —
`RegisterCompose.logChowla2_ineffective_v6` with the `cs` arrow and the `T₀` arrow both GONE
from the inner implication.

⟦THE SURVIVING LIST⟧ outer hypotheses: NOTHING.  Inner, exactly **three** items:

* `Real.exp (-100) ≤ Ks`;
* `XCeilRiderStrict ε g` — the caller's own request;
* the `K_vt` cushion
  `32·Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊ + 32·(2·log (flatDoorM A) + log 4 + 50) ≤ log R.Hhi / 4`.

⟦WHAT MOVED⟧ `Real.exp (-100) ≤ cs` is no longer asked: it is DELIVERED, as a conjunct of the
`∃`-prefix, carried from the two leaves that produce the constant (V7-B).  `T₀ ≤
exp(√(flatDesignBase A)/2)` is no longer asked either: `T₀` joins the design constant's `max`
as a sixth arm and the tolerance clears it by three exponential levels (V7-C).  The `∃`-prefix
is otherwise `v6`'s, including `3 ≤ T₀` and `0 < cs`.

`logChowla2_ineffective_v6`, `logChowla2_ineffective_v6_csarm` and
`logChowla2_ineffective_v6_T0arm` are byte-untouched and remain citable. -/
theorem logChowla2_ineffective_v7 (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (Real.exp (-100) ≤ Ks →
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
  -- ⟦THE cs-FREE FLAT TERMINAL⟧ V7-B's §4: the floor arrives as `hcsf`, not as an arrow
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ :=
    logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree Awin hband
  -- ⟦THE DESIGN CONSTANT, WITH THE `T₀`-ARM⟧ V7-C's sixth arm: chosen above all five landed
  -- thresholds AND above `T₀` itself — legal for the same reason the other five arms are,
  -- every one of the six constants is minted BEFORE the lever, `T₀` at the obtain just above.
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
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A, hKvt0, ?_⟩
  intro hKs g hg
  -- ⟦RIDER 2, DISCHARGED⟧ V7-C's arm at the design constant's own sixth `max` slot
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKs g hg
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

/-! ## §2 — ⟦V7-D G-INSTANT⟧ the mint read at `g ≡ 0`

`v7`'s second inner rider, `XCeilRiderStrict ε g`, is a property of the function the CALLER
supplies as its outer-scale request.  A caller who requests nothing supplies `g ≡ 0`, and then
the rider is met by `Real.log 0 = 0` — the same three-line discharge the corpus already runs
inside `RegisterCompose` (:247-251), `XThread` (:1247) and `V7B` (:1760) to read off the
`ε`-ceiling.  This section states that instance as its own citable declaration.

Additive: `logChowla2_ineffective_v7` is byte-untouched and remains the object of record. -/

/-- **⟦THE `g ≡ 0` INSTANCE OF THE MINT⟧** (`logChowla2_ineffective_v7_g0`) — a machine-checked,
witnessed-scale **instance** of the logarithmically averaged two-point Chowla bound, carrying
**two named inner riders** (`Real.exp (-100) ≤ Ks`; the Siegel-genre `K_vt` cushion),
ineffective, outer hypotheses none — at one opaque tolerance and one produced window.

⟦WHAT IT IS⟧ `logChowla2_ineffective_v7` — which carries **three** named inner riders
(`Real.exp (-100) ≤ Ks`; the caller-side scale-request property `XCeilRiderStrict ε g`; the
`K_vt` cushion) — read at the trivial request `g ≡ 0`.  The scale-request rider is NOT
discharged in general: it is VOID at this instance, because a caller who asks for nothing has
nothing to prove.  The price is paid in the conclusion: `v7`'s `g R.Hhi R.ω ≤ R.x` conjunct
becomes `0 ≤ R.x` and is dropped, so this instance makes no outer-scale demand at all.  The
`∃`-prefix is `v7`'s verbatim, and the remaining two riders are `v7`'s unchanged.

⟦THE SCOPE, STATED⟧ what the statement does and does not say, in its own bytes:

* the tolerance `ε` is OPAQUE and bounded only from BELOW — all that is exported is
  `1 / 500 ≤ ε` (with the regime's own `ε ≤ 1/2`).  The theorem is at one produced `ε`, not
  at every `ε`, and not at any named value;
* the window is `(x/ω, x]` weighted by `1/n` against `ε · log ω` (`logChowla2Fails`,
  `ChowlaFailure.lean:59-63`) — a windowed partial sum, not the full logarithmic average over
  `n ≤ x` against `log x`;
* the shift is `n + 1` (the `2` counts the factors `λ(n)·λ(n+1)`, not the shift);
* `ineffective`: the design constant `A` is produced by `Classical.choice` through the chain,
  and `Ks` carries Siegel's ineffective constant, so no numerical scale is extractable;
* nothing here bears on twin primes — the transport wall is untouched at this rung. -/
theorem logChowla2_ineffective_v7_g0 (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (Real.exp (-100) ≤ Ks →
        ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
              + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
            ≤ Real.log (R.Hhi : ℝ) / 4 →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb, hβ, hA162, hA₀A, hKvt0, hmain⟩ :=
    logChowla2_ineffective_v7 A₀
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb, hβ, hA162, hA₀A, hKvt0, ?_⟩
  intro hKs
  -- ⟦THE RIDER, VOID⟧ the caller's request is `0`, and `log 0 = 0` leaves the margin intact
  have hzero : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := by
    intro Hhi ω hgate
    obtain ⟨-, -, hωw⟩ := hgate
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [Real.log_natCast_nonneg ω]
  obtain ⟨R, hReps, hHlo, -, hRtow, hdes, hwin, hfire⟩ := hmain hKs (fun _ _ => 0) hzero
  exact ⟨R, hReps, hHlo, hRtow, hdes, hwin, hfire⟩

end Salt.MR

end
