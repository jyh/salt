/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SupStation
import Salt.MR.USetPrice

/-!
# THE SEAM TERMINAL — the three-leg row with the `𝒯`-leg as a SOCKET (`SeamTerminal`)

The seam row of Proposition A.3 splits the annulus integral into three legs:

  `∫_{Ann} ‖spoly N a t‖² ≤ 8·S²  +  ∫_{(Ann∖ball) ∩ 𝒯tot} ‖spoly N a t‖²  +  𝒰`.

Two of the three are CLOSED in the corpus:

* the **ball leg** by `SupStation.seam_ball_leg_station_M` (the ⟦TWO-M⟧ option-(A) exit at
  `S = ballSupS X (C₁·e^{−M₀/(2e)} + 4(log X)^{−1/2+1/1000})`, valid at any lower bound `M₀`
  for `𝔻²(·; X)` on MRT's own window `|v| ≤ X` — in particular at
  `M(f;X) = inf_{|t|≤X} 𝔻²`);
* the **`𝒰` leg** by `USetPrice.hU_fully_priced` (all four grade slots discharged at the §8.3
  pins), landing at `2(Tann/X+1)(log X)^{−θ₂₉₃+ε}`, which `priced_exit_beats_door` grades to
  the door's floor `2(Tann/X+1)(log X)^{−1/500}`.

The third — the `𝒯` leg, MR §8.1+§8.2's `Σ_j E_j` — is a giant (⟦V6⟧: the flat-`δ` wall, Route
G). **This file makes it a SOCKET, not a blocker**: the terminal carries

  `hT : ∫_{(Ann∖ball) ∩ 𝒯tot} ‖spoly N a t‖² ≤ Tbd`

as a NAMED BINDER at a free `Tbd`, exactly as `hU` was carried before U-9, and composes the
other two legs around it.  The moment Route G lands a `Tbd`, the row's terminal is a one-line
application — no re-proof of the ball or `𝒰` sides.

## The three composition seams (⟦V6⟧, as built here)

1. **`t₁` produced-then-fed.**  `seam_ball_leg_station_M` PRODUCES the centre `t₁` (with
   `|t₁| ≤ X` — the MVT-guarded `seamGateRstar X Tann ≤ X`); `hU_fully_priced` needs `t₁` as a
   FREE parameter (its far-leg radius and ball datum are stated about the same `t₁` the `𝒰`
   integral is centred on).  The terminal intros the station's `t₁` FIRST and instantiates
   both `hU` and `hT` at it.  The three `t₁`-dependent hypotheses of the `𝒰` side are handled
   thus: `|t₁| ≤ X` comes free from the station; `Tann + |t₁| ≤ Dmax` is supplied by the
   `t₁`-FREE binder `Tann + X ≤ Dmax` (which is what a consumer can actually check); and the
   `𝒰`-side ball datum rides as an ANTECEDENT of the exit, next to the cap.

2. **THE TWO DATA (no adapter).**  The station's cap is at
   `seamCoeff (ellLin g) (fun _ => 1) t₀`, the `𝒰` side's datum at `ellLin g`.  These are
   DIFFERENT objects (⟦V5e⟧: the false byte-fit the U-9 assembly refused), so BOTH are carried:

   * `hMcap` — `∀ x ∈ [X, 2X], 𝔻²(seamCoeff (ellLin g) 1 t₀, n^{it₁}; x) ≤ (1/16)·loglog X`
     (the A-10 ball cap, at the seam datum, on the whole dyadic window);
   * `hrow` — `𝔻²(ellLin g, n^{it₁}; X) ≤ (1/16)·loglog X` (the `𝒰` side's own datum, at the
     bare `ℓ`-linearisation, at the single scale `X`).

   No adapter is attempted between them: relating `seamCoeff (ellLin g) 1 t₀` to `ellLin g`
   is a `t₀`-drift question, not a composition question.

3. **The A-10 dichotomy.**  The station's ball-leg bound is an IMPLICATION from the cap.  The
   terminal is stated UNDER the cap (`seam_terminal_row`) — the cleaner form, and the one MR's
   own proof shape wants, since §A.3 splits at `M(f;X) ≥ (1/8)loglog X` and gives the
   cap-fails arm its own trivial/pretentious treatment.  **THE FAR-ARM SOCKET** (W-1,
   `FarArm.lean`, ⟦V6⟧'s A-10 far arm) is the missing `¬hMcap` case; `seam_terminal_dichotomy`
   below carries it as the named binder `hFar` and performs the case split, so W-1 plugs in
   with no change to this file.

## What is here

* §1 — the two small bridges: the `M₀ = 0` discharge of the window binder (the statement is
  never vacuous), and the `t₁`-free `Dmax` bridge.
* §2 — **`seam_terminal_row`**: THE TERMINAL, under the cap, with `hT` a socket.
* §3 — **`seam_terminal_dichotomy`**: the same with the far arm as the named binder `hFar`.

**Law #253**: the `𝒯` leg rides as the ONE enumerated union `seamTtot fb Pseq Qseq δ Jset`
(`⋃ j ∈ Icc 1 Jset, Tset …`), never as a `Σ_j` of `J` copies — verbatim the set that
`hU_fully_priced` leaves on the right, so the socket byte-fits whatever Route G produces.

**ASSEMBLY GUARD** (⟦V4⟧): the row is trivially satisfiable at degenerate pins (`fb := 0`
gives `Uset = ∅`; `Jset := 0` gives `seamTtot = ∅`) — a consumer MUST pin `fb` to the datum
primes and `Jset := J` or the row carries no content.

**LIVE GUARD** (inherited from the ball chain): `c = 1/(2e)` is the BALL arm's halved
constant; a §8.3 consumer citing the ball exit is a STOP.

Source pins (D5): MR arXiv v4 (`1501.04585v4`) §8.3 pp. 19–20, 27–29 and Prop. A.3 p. 22 of
the rendered `1503.05121v3`; `docs/exploration/hsup-design.md` ⟦TWO-M RATIFIED⟧,
⟦A.3 FAITHFULNESS⟧, ⟦V5e⟧, ⟦V5f⟧, ⟦V6⟧.
-/

namespace Salt.MR

open scoped BigOperators
open Finset MeasureTheory

/-! ## §1 — the two bridges -/

/-- The window binder of `seam_ball_leg_station_M` is ALWAYS dischargeable at `M₀ = 0`:
`pretDistSq` of two 1-bounded arguments is nonnegative.  So the terminal below is never
vacuous — it degrades to the `M₀ = 0` row (`e^{−0} = 1`), which is the honest statement that
the ball leg costs `8·ballSupS X (C₁ + 4(log X)^{−1/2+1/1000})²` with no pretentious gain. -/
theorem seam_window_datum_zero {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (t₀ X : ℝ) :
    ∀ v : ℝ, |v| ≤ X →
      (0 : ℝ) ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X := by
  intro v _
  have hEllOne : ∀ n : ℕ, ‖ellLin g n‖ ≤ 1 := fun n => ellLin_norm_le_one g hg n
  have hSeamOne : ∀ n : ℕ, ‖seamCoeff (ellLin g) (fun _ => 1) t₀ n‖ ≤ 1 :=
    fun n => norm_seamCoeff_le hEllOne (fun _ => le_of_eq norm_one) t₀ n
  exact pretDistSq_nonneg _ _ _ hSeamOne (fun n => le_of_eq (costwist_norm v n))

/-- **The `t₁`-free `Dmax` bridge.**  `hU_fully_priced` needs `Tann + |t₁| ≤ Dmax` at the
PRODUCED centre; the station guarantees `|t₁| ≤ X`, so the consumer-checkable `t₁`-free gate
`Tann + X ≤ Dmax` suffices.  (This is why the terminal's `Dmax` binder is stated at `X`.) -/
theorem seam_Dmax_bridge {Tann X Dmax t₁ : ℝ} (hDmaxX : Tann + X ≤ Dmax) (ht₁ : |t₁| ≤ X) :
    Tann + |t₁| ≤ Dmax := by linarith

/-! ## §2 — THE TERMINAL

The three legs composed.  Read the conclusion as: the annulus integral is at most

  `8·ballSupS X (C₁·e^{−M₀/(2e)} + 4(log X)^{−1/2+1/1000})²`  (the ball leg, closed)
  `+ Tbd`                                                     (the `𝒯` leg, SOCKETED)
  `+ 2(Tann/X + 1)(log X)^{−1/500}`                           (the `𝒰` leg, closed at the door).
-/

/-- **THE SEAM TERMINAL** (`seam_terminal_row`).  For `g` 1-bounded at the primes and any seam
phase `t₀`, there are absolute constants such that for every dyadic scale `X ≤ N ≤ 2X` above
the threshold, every annulus height `Tann` in MRT's own working range
`exp(30(log X)^{1/2}) ≤ Tann ≤ X/2` (the ⟦A.3 FAITHFULNESS⟧ MVT guard — MR's own opening move
reduces to `T ≤ X/2`), every §8.3 pin bundle, and every `M₀` bounding `𝔻²(·;X)` from below on
the window `|v| ≤ X`, the seam row's ball centre `t₁` exists with `|t₁| ≤ X` and, **under the
A-10 cap** `hMcap` and the `𝒰`-side datum `hrow`, for EVERY bound `Tbd` on the `𝒯` leg:

  `∫_{Ann} ‖spoly N a t‖² ≤ 8·ballSupS X (C₁·e^{−M₀/(2e)} + 4(log X)^{−1/2+1/1000})²
      + Tbd + 2(Tann/X + 1)(log X)^{−1/500}`.

The `𝒯`-leg hypothesis is the SOCKET: it is stated at the enumerated union
`seamTtot fb Pseq Qseq δ Jset` (law #253), the integrand `‖spoly N a t‖²` and the domain
`(seamAnn X Tann ∖ seamBall X t₁) ∩ …` verbatim as `hU_fully_priced` leaves them, so Route G's
exit plugs in with no adapter.

Instantiating `M₀ := M(f;X) = inf_{|t|≤X} 𝔻²(f, n^{it}; X)` is legal by
⟦A.3 FAITHFULNESS⟧: the infimum is stated here as the `∀`-form (`hM₀`), which is what an
`sInf` supplies and what a consumer can check, with no `sInf` plumbing in the statement. -/
theorem seam_terminal_row {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ C₁ Cq cq T₀ Xg C X₀ : ℝ,
      0 ≤ C₁ ∧ 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xg ∧ 0 < X₀ ∧
      ∀ (fb a cf : ℕ → ℂ), (∀ n : ℕ, ‖fb n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X Tann M₀ δ δ' V L α η cg Cb Dmax Rrad kmin Ymax CR ε EP2 E : ℝ),
        X₀ ≤ X →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X / 2 →
        1 < (Qseq Jb : ℝ) → Real.log (Qseq Jb) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        0 < δ → 1 ≤ Jb → Jb ≤ Jset → 1 ≤ V →
        V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ) → V⁻¹ ≤ δ' →
        3 ≤ Pseq Jb → (Qseq Jb : ℝ) ≤ Tann →
        Real.log V ≤ α * Real.log (Pseq Jb) → α ≤ 1 / 4 - η → 2 * η ≤ 1 →
        Real.log V ≤ 100 * Real.log L →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundle Tann V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        0 < cg → cg ≤ 1 / Real.exp 1 → 2 * cg < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        collisionGate X 25 C → 0 < Rrad → Rrad ≤ seamRad X → Tann + X ≤ Dmax →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates cq Xg (H83 X theta293) P N Xd Mt kk
          Tann L cg Cb X theta293 Dmax Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          ∀ k : ℕ, kk j ≤ k → k ≤ Mt j → |t| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ 3 * X) →
        1 < kmin → (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        cofactorRbd cg Cb X theta293 kmin Ymax (Dmax + 1) Rrad
            ≤ CR * (Real.log X) ^ (-rho293) →
        1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → ε ≤ 1 / 1000 → 8640 ≤ (Real.log X) ^ ε →
        12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        (∀ v : ℝ, |v| ≤ X →
          M₀ ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) →
        ∃ t₁ : ℝ, |t₁| ≤ X ∧
          ((∀ x : ℝ, X ≤ x → x ≤ 2 * X →
              pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
                ≤ (1 / 16) * Real.log (Real.log X)) →
            pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
            ∀ Tbd : ℝ,
              (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ seamTtot fb Pseq Qseq δ Jset,
                  ‖spoly N a t‖ ^ 2) ≤ Tbd →
              (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
                ≤ 8 * ballSupS X (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
                      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) ^ 2
                  + Tbd
                  + 2 * ((Tann / X + 1) * Real.log X ^ (-(1 : ℝ) / 500))) := by
  obtain ⟨C₁, XA, hC₁0, hXA0, HS⟩ := seam_ball_leg_station_M hg t₀
  obtain ⟨Cq, cq, T₀, Xg, C, hCq, hcq, hT₀, hXg0, HU⟩ := hU_fully_priced
  refine ⟨C₁, Cq, cq, T₀, Xg, C, XA, hC₁0, hCq, hcq, hT₀, hXg0, hXA0, ?_⟩
  intro fb a cf hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk
    X Tann M₀ δ δ' V L α η cg Cb Dmax Rrad kmin Ymax CR ε EP2 E
    hXlb hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX2 hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hδ0 hJb1 hJbJ hV1 hVinv hVδ hP3 hQT hVα hα hη2 hlogV hMs hbudget
    hm₀2 hm₀ hMs4 hc0 hce hc1 hCb0 hCbound hPlow hQ0 hQhigh hPQ hcoll hR0 hRrad
    hDmaxX hblk hbox hkmin hkk hMt hRgrade hCqgate hKSgate hε0 hε1 habs hEP2 hErow herr
    hXN hN2 hsupp hDatum hM₀
  -- the frame facts the two sides need in slightly different shapes
  have hTann0 : (0 : ℝ) ≤ Tann := by linarith
  have hTX : Tann ≤ X := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  -- SEAM 1: the station PRODUCES the centre; everything below is instantiated at it
  obtain ⟨t₁, ht₁X, hexit⟩ :=
    HS X N Tann M₀ a hXlb hXN hN2 hTann0 hTX2 hsupp hDatum hM₀
  refine ⟨t₁, ht₁X, fun hMcap hrow Tbd hT => ?_⟩
  -- SEAM 3: under the cap, the station's exit IS the row's `hSup` binder, at
  -- `S := ballSupS X (C₁·e^{−M₀/(2e)} + 4(log X)^{−1/2+1/1000})`
  have hSup := hexit hMcap
  -- SEAM 1 (cont.): the `t₁`-free `Dmax` gate discharges the `𝒰` side's `t₁`-dependent one
  have hDmax : Tann + |t₁| ≤ Dmax := seam_Dmax_bridge hDmaxX ht₁X
  -- the `𝒰` leg, fully priced, at the produced centre (SEAM 2: `hrow` is the `𝒰` side's own
  -- datum at `ellLin g`, NOT the station's cap at `seamCoeff (ellLin g) 1 t₀`)
  have hrowbd := HU g fb a cf hg hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk
    X Tann t₁ δ δ' V L α η cg Cb Dmax Rrad kmin Ymax CR ε EP2 E
    (ballSupS X (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)))
    hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hδ0 hJb1 hJbJ hV1 hVinv hVδ hP3 hQT hVα hα hη2 hlogV hMs hbudget
    hm₀2 hm₀ hMs4 hc0 hce hc1 hCb0 hCbound hPlow hQ0 hQhigh hPQ ht₁X hrow hcoll hR0 hRrad
    hDmax hblk hbox hkmin hkk hMt hRgrade hCqgate hKSgate hε0 habs hEP2 hErow herr
    hXN hN2 hsupp hSup
  -- the `𝒯` leg is the SOCKET: replace the integral by its named bound
  have hstep : (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
      ≤ 8 * ballSupS X (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
            + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) ^ 2
        + Tbd
        + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by linarith
  -- the `𝒰` leg's grade meets the door's floor
  exact priced_exit_beats_door X Tann ε
    (8 * ballSupS X (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) ^ 2)
    Tbd _ hε1 hL1 hX0 hTgate hstep

/-! ## §3 — the A-10 dichotomy, with the far arm as a NAMED BINDER

⟦V6⟧'s W-1 (`FarArm.lean`) owns the `¬hMcap` case — the ball-centre dichotomy, where the seam
datum is NOT pretentious to `n^{it₁}` on the whole dyadic window and MR's own trivial /
pretentious treatment applies instead.  Until W-1 lands, the arm is a socket exactly like the
`𝒯` leg: `hFar` below.  When it lands, `seam_terminal_dichotomy` discharges it and the row's
terminal is unconditional in the cap. -/

/-- **THE TERMINAL, CAP-FREE, WITH THE FAR ARM SOCKETED** (`seam_terminal_dichotomy`).
`seam_terminal_row` with the A-10 cap removed from the antecedents and the `¬cap` arm carried
as the named binder `hFar` (⟦V6⟧'s W-1, `FarArm.lean`).  The proof is the case split: on the
cap, §2's terminal; off it, `hFar`.  The two arms deliver the SAME bound at the SAME centre,
so no disjunction survives the exit — the same discipline the station used for its own
empty/nonempty dichotomy. -/
theorem seam_terminal_dichotomy {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ C₁ Cq cq T₀ Xg C X₀ : ℝ,
      0 ≤ C₁ ∧ 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xg ∧ 0 < X₀ ∧
      ∀ (fb a cf : ℕ → ℂ), (∀ n : ℕ, ‖fb n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X Tann M₀ δ δ' V L α η cg Cb Dmax Rrad kmin Ymax CR ε EP2 E : ℝ),
        X₀ ≤ X →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X / 2 →
        1 < (Qseq Jb : ℝ) → Real.log (Qseq Jb) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        0 < δ → 1 ≤ Jb → Jb ≤ Jset → 1 ≤ V →
        V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ) → V⁻¹ ≤ δ' →
        3 ≤ Pseq Jb → (Qseq Jb : ℝ) ≤ Tann →
        Real.log V ≤ α * Real.log (Pseq Jb) → α ≤ 1 / 4 - η → 2 * η ≤ 1 →
        Real.log V ≤ 100 * Real.log L →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundle Tann V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        0 < cg → cg ≤ 1 / Real.exp 1 → 2 * cg < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        collisionGate X 25 C → 0 < Rrad → Rrad ≤ seamRad X → Tann + X ≤ Dmax →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates cq Xg (H83 X theta293) P N Xd Mt kk
          Tann L cg Cb X theta293 Dmax Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          ∀ k : ℕ, kk j ≤ k → k ≤ Mt j → |t| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ 3 * X) →
        1 < kmin → (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        cofactorRbd cg Cb X theta293 kmin Ymax (Dmax + 1) Rrad
            ≤ CR * (Real.log X) ^ (-rho293) →
        1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → ε ≤ 1 / 1000 → 8640 ≤ (Real.log X) ^ ε →
        12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        (∀ v : ℝ, |v| ≤ X →
          M₀ ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) →
        ∃ t₁ : ℝ, |t₁| ≤ X ∧
          (pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
            ∀ Tbd : ℝ,
              (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ seamTtot fb Pseq Qseq δ Jset,
                  ‖spoly N a t‖ ^ 2) ≤ Tbd →
              -- the far arm (W-1, `FarArm.lean`) as a NAMED SOCKET
              (¬ (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
                    pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
                      ≤ (1 / 16) * Real.log (Real.log X)) →
                (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
                  ≤ 8 * ballSupS X (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
                        + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) ^ 2
                    + Tbd
                    + 2 * ((Tann / X + 1) * Real.log X ^ (-(1 : ℝ) / 500))) →
              (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
                ≤ 8 * ballSupS X (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
                      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) ^ 2
                  + Tbd
                  + 2 * ((Tann / X + 1) * Real.log X ^ (-(1 : ℝ) / 500))) := by
  obtain ⟨C₁, Cq, cq, T₀, Xg, C, X₀, hC₁0, hCq, hcq, hT₀, hXg0, hX₀0, H⟩ :=
    seam_terminal_row hg t₀
  refine ⟨C₁, Cq, cq, T₀, Xg, C, X₀, hC₁0, hCq, hcq, hT₀, hXg0, hX₀0, ?_⟩
  intro fb a cf hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk
    X Tann M₀ δ δ' V L α η cg Cb Dmax Rrad kmin Ymax CR ε EP2 E
    hXlb hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX2 hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hδ0 hJb1 hJbJ hV1 hVinv hVδ hP3 hQT hVα hα hη2 hlogV hMs hbudget
    hm₀2 hm₀ hMs4 hc0 hce hc1 hCb0 hCbound hPlow hQ0 hQhigh hPQ hcoll hR0 hRrad
    hDmaxX hblk hbox hkmin hkk hMt hRgrade hCqgate hKSgate hε0 hε1 habs hEP2 hErow herr
    hXN hN2 hsupp hDatum hM₀
  obtain ⟨t₁, ht₁X, Hexit⟩ :=
    H fb a cf hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk
      X Tann M₀ δ δ' V L α η cg Cb Dmax Rrad kmin Ymax CR ε EP2 E
      hXlb hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX2 hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
      hδ0 hJb1 hJbJ hV1 hVinv hVδ hP3 hQT hVα hα hη2 hlogV hMs hbudget
      hm₀2 hm₀ hMs4 hc0 hce hc1 hCb0 hCbound hPlow hQ0 hQhigh hPQ hcoll hR0 hRrad
      hDmaxX hblk hbox hkmin hkk hMt hRgrade hCqgate hKSgate hε0 hε1 habs hEP2 hErow herr
      hXN hN2 hsupp hDatum hM₀
  refine ⟨t₁, ht₁X, fun hrow Tbd hT hFar => ?_⟩
  by_cases hMcap : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
        ≤ (1 / 16) * Real.log (Real.log X)
  · exact Hexit hMcap hrow Tbd hT
  · exact hFar hMcap

end Salt.MR
