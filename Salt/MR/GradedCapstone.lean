/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CaseASocket

/-!
# `GradedCapstone` — the graded `hU` row with NO socket (`hUG34_unconditional`)

`USetGradedPrice.hUG34_fully_priced` (:956) is the graded seam row's `𝒰`-leg fully priced —
conditional on ONE named page, the CASE-A window-floor supply at the `y₂` truncation height,
carried there as the hypothesis

  `∀ j ∈ ramI …, ∀ t, CaseASocket2 g P Q (1/e) Cb X θ₂₉₃ (kk j) (Mt j) t`.

`CaseASocket.caseASocket2_discharged` (:1059) PROVES that page.  This file is the composition:
the same row, byte-for-byte, with the socket binder GONE.

## The transplant device

The statement of `hUG34_unconditional` is `hUG34_fully_priced`'s **verbatim** — same binder
list, same order, same conclusion — with exactly one line removed (the socket) and the
socket's own gates put in its place.  Nothing is tidied, renamed, or re-associated: the row
that the graded `𝒯`-leg (`G2`–`G5`) will consume must be the row that landed.

## The carried gates (law #253)

`caseASocket2_discharged` re-introduces five gates.  Two of them are the `c`-contract and are
DISCHARGED here, because `hUG34_fully_priced` pins `c := 1/e` in its own statement:
`0 < 1/e` and `1/e ≤ 1/e` (the third `c`-gate, `2c < 1`, is `hUG34_fully_priced`'s `hc1`
verbatim).  The remaining three are stated, and stated at the block-range floor `kmin` rather
than per block, so each is ONE hypothesis rather than a `∀ j`:

* `ShortIntervalDatum Cb` — the Chebyshev datum at the named constant.  `Cb` stays
  UNIVERSALLY quantified (`GradeConst.exists_shortIntervalDatum` would pin it at `250` and
  hand back a weaker theorem; the consumer's own `hCqgate` reads `gradeCR2 Cb`, so `Cb` must
  stay free).
* `X₀ ≤ kmin` — §0's datum-free threshold, hoisted into the existential prefix.  The `∃X₀`
  of `caseASocket2_discharged` sits OUTERMOST (before the datum `g`), so it is uniform in
  every remaining binder and may be hoisted; this is the one thing to re-read before citing
  any supply.  Transported to each block by the landed `kmin ≤ (kk j : ℝ)`.
* `0 ≤ cofactorMfl X θ₂₉₃ kmin` — `cofactor_Rbd34_local`'s floor-value binder.  Transported
  to each block by `USetPrice.cofactorMfl_mono` (the floor GROWS with the descent anchor), so
  the weakest instance is the one stated.

Two further gates of `caseASocket2_discharged` need NO hypothesis at all — they are already
inside `USetGradedPrice.TLBlockGates34`:

* `pin2Gate ≤ (kk j : ℝ)` — from the bundle's `ballQuarterThreshold ≤ (kk j : ℝ)` through
  `USetGradedPrice.pin2Gate_le_ballQuarterThreshold`;
* the dyadic window `kk j ≤ Mt j ≤ 2·kk j` — from the bundle's two roundings of the
  co-factor length: `Mt j ≤ 2(ramRbot − 1)` with `ramRbot ≤ kk j + 1` gives the upper leg,
  and `2·ramRbot < Mt j + 3` with `kk j < ramRbot` and `3 ≤ ballQuarterThreshold` gives the
  lower one.

## The stones

* `hUG34_unconditional` — the graded row's `𝒰`-leg, socket-free.
* `hUG34_unconditional_beats_door` — that exit read at the door
  (`USetPrice.priced_exit_beats_door`): the third summand at `(log X)^{−1/500}`, the door's
  floor `c₀ ≥ 1/500`, cleared at the ratified margin `1.7067×`
  (`CofactorDist.exit_margin_293`).
-/

noncomputable section

namespace Salt.MR

open MeasureTheory

/-! ## §1 — the composition -/

/-- **THE GRADED STATION PRIZE, UNCONDITIONAL** (`hUG34_unconditional`).
`USetGradedPrice.hUG34_fully_priced` with its ONE socket discharged by
`CaseASocket.caseASocket2_discharged`.

Everything else is that theorem's statement verbatim — the §8.3 pins `H := H₈₃ X θ₂₉₃`,
`θ := θ₂₉₃`, `c := 1/e`, all four grade slots discharged, the co-factor grade `R̄` discharged
through the repaired `q = 3/4` + `T*₂` + localized chain, the radius pin `Rrad` in BOTH
directions (⟦V6a⟧'s silent-vacuity catch), and `TannGate X Tann` riding in-statement.

In place of the socket line stand the three gates `caseASocket2_discharged` genuinely needs
(module docstring): the short-interval datum, the datum-free threshold `X₀ ≤ kmin`, and the
CASE-A floor value `0 ≤ cofactorMfl X θ₂₉₃ kmin`.  The `c`-contract is discharged at the
pinned `c = 1/e`, and the R2 family gate plus the dyadic window come free from
`TLBlockGates34`. -/
theorem hUG34_unconditional :
    ∃ Cq cq T₀ C X₀ : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
      ∀ (g fb a cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖fb n‖ ≤ 1) →
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq m₀ Ms Mt kk : ℕ → ℕ) (Hseq αseq : ℕ → ℝ),
      ∀ (X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S : ℝ),
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        Real.exp 2 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        1 < (Qseq Jb : ℝ) → Real.log (Qseq Jb) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        1 ≤ Jb → Jb ≤ Jset → 2 ≤ Hseq Jb → 0 ≤ αseq Jb →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ Tann →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
        αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 C → 0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X) →
        -- ⟦THE TRANSPLANT⟧ the CASE-A socket stood HERE; in its place stand exactly the
        -- gates `caseASocket2_discharged` asks for, at the block-range floor `kmin`
        ShortIntervalDatum Cb →
        X₀ ≤ kmin →
        0 ≤ cofactorMfl X theta293 kmin →
        -- the block-range data: the mixed worst corner, and the window's own geometry
        2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        -- the two block gates and Lemma 12's rows
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        -- the graded row's own frame
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                ∩ seamTtotG fb Pseq Qseq Hseq αseq Jset, ‖spoly N a t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨X₀, hX₀0, hsock⟩ := caseASocket2_discharged
  obtain ⟨Cq, cq, T₀, C, hCq, hcq, hT₀, hpriced⟩ := hUG34_fully_priced
  refine ⟨Cq, cq, T₀, C, X₀, hCq, hcq, hT₀, hX₀0, ?_⟩
  intro g fb a cf hg hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup
  -- the `c`-contract at the PINNED `c = 1/e` (`hUG34_fully_priced`'s own two lines)
  have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  -- the socket, discharged at every block of the graded partition
  have hA2 : ∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ,
      CaseASocket2 g P Q (1 / Real.exp 1) Cb X theta293 (kk j) (Mt j) t := by
    intro j hj t
    obtain ⟨-, -, -, -, -, -, hk₀th, -, hk₀lo, hk₀hi, -, -, hhigh, hMtop, -, -, -⟩ :=
      hblk j hj
    -- the R2 family gate, free from the bundle's `q = 3/4` conversion threshold
    have hk₀pin : pin2Gate ≤ ((kk j : ℕ) : ℝ) :=
      le_trans pin2Gate_le_ballQuarterThreshold hk₀th
    have hk3 : (3 : ℝ) ≤ ((kk j : ℕ) : ℝ) := le_trans three_le_ballQuarterThreshold hk₀th
    -- the dyadic window, free from the bundle's two roundings of the co-factor length
    have hkMR : ((kk j : ℕ) : ℝ) ≤ ((Mt j : ℕ) : ℝ) := by linarith
    have hkM : kk j ≤ Mt j := by exact_mod_cast hkMR
    have hM2k : ((Mt j : ℕ) : ℝ) ≤ 2 * ((kk j : ℕ) : ℝ) := by linarith
    -- the two transported gates: the threshold and the floor value
    have hX₀kk : X₀ ≤ ((kk j : ℕ) : ℝ) := le_trans hX₀k (hkk j hj)
    have hMflkk : (0 : ℝ) ≤ cofactorMfl X theta293 ((kk j : ℕ) : ℝ) :=
      le_trans hMfl0 (cofactorMfl_mono X theta293 (hkk j hj))
    exact hsock g hg P Q (1 / Real.exp 1) Cb X theta293 (kk j) (Mt j) t hc0 le_rfl hc1
      hCb0 hCbound hX₀kk hk₀pin hkM hM2k hMflkk
  exact hpriced g fb a cf hg hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad hRlow
    hblk hbox hA2 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup

/-! ## §2 — the composed exit at the door -/

/-- **THE UNCONDITIONAL GRADED EXIT CLEARS THE DOOR** (`hUG34_unconditional_beats_door`).
`hUG34_unconditional` read through `USetPrice.priced_exit_beats_door`: at any `o(1)` with
`ε ≤ 1/1000` the third summand is `2(Tann/X + 1)(log X)^{−1/500}`, the door's floor
`c₀ ≥ 1/500`, cleared with the ratified margin `1.7067×` (`CofactorDist.exit_margin_293`).

The statement is `hUG34_unconditional`'s with ONE hypothesis added — `ε ≤ 1/1000`, beside the
`0 ≤ ε` that was already there — and the exit exponent `−θ₂₉₃ + ε` replaced by `−1/500`.  The
first two summands (`8S²` and the graded `𝒯`-leg) ride untouched, exactly as in the flat
chain's `priced_exit_beats_door`. -/
theorem hUG34_unconditional_beats_door :
    ∃ Cq cq T₀ C X₀ : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
      ∀ (g fb a cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖fb n‖ ≤ 1) →
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq m₀ Ms Mt kk : ℕ → ℕ) (Hseq αseq : ℕ → ℝ),
      ∀ (X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S : ℝ),
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        Real.exp 2 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        1 < (Qseq Jb : ℝ) → Real.log (Qseq Jb) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        1 ≤ Jb → Jb ≤ Jset → 2 ≤ Hseq Jb → 0 ≤ αseq Jb →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ Tann →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
        αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 C → 0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X) →
        -- ⟦THE TRANSPLANT⟧ the CASE-A socket's three surviving gates
        ShortIntervalDatum Cb →
        X₀ ≤ kmin →
        0 ≤ cofactorMfl X theta293 kmin →
        -- the block-range data: the mixed worst corner, and the window's own geometry
        2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        -- the two block gates and Lemma 12's rows
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        -- the door's own `o(1)` gate, beside the nonnegativity that was already here
        0 ≤ ε → ε ≤ 1 / 1000 →
        8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        -- the graded row's own frame
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                ∩ seamTtotG fb Pseq Qseq Hseq αseq Jset, ‖spoly N a t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-(1 : ℝ) / 500)) := by
  obtain ⟨Cq, cq, T₀, C, X₀, hCq, hcq, hT₀, hX₀0, huncond⟩ := hUG34_unconditional
  refine ⟨Cq, cq, T₀, C, X₀, hCq, hcq, hT₀, hX₀0, ?_⟩
  intro g fb a cf hg hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 hε1 habs hEP2 hErow herr hXN hN2 hsupp hSup
  exact priced_exit_beats_door X Tann ε _ _ _ hε1 (by linarith) hX0 hTgate
    (huncond g fb a cf hg hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk Hseq αseq
      X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
      hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
      hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hm₀2 hm₀ hMs4
      hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad hRlow
      hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
      hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup)

end Salt.MR
