/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16FlatTerminalLinear
import Salt.MR.S16ProducersH
import Salt.MR.S16FlatTerminalExitH

/-!
# THE FLAT-LINEAR LANE AT THE INFLATED SOCKET — the two riders, re-quantified

⟦WHAT THIS FILE SETTLES⟧  `S16FlatTerminalLinear` carries the flat-linear lane's two open
riders — the band-lane `C` rider `S16BandLaneCBoundedL` and the crossing bound
`S15CrossingBound_L_gk` — both quantified over the LANDED linear socket `SocketBaseL`.  The
`h`-lane's hops need the same two riders quantified over the INFLATED socket
`HDoorSupply.SocketBaseLH h`, whose arc denominator is `h · arcDen 12 H`.  This file states
them and pins each to its landed twin at `h = 1`.

⛔ **NEITHER DEF IS A THEOREM AND NEITHER GAINS A PRODUCER HERE.**  `S16BandLaneCBoundedL`
has **no producer anywhere in the corpus** at `h = 1` (34 binder sites across 9 modules, zero
discharges); re-quantifying it at `SocketBaseLH h` re-states an open rider, it does not open a
new one.  `S15CrossingBound_LH_gk` is H2c's target.  The `h`-lane's conditionality is therefore
**exactly** the `h = 1` lane's conditionality, on the same two objects.

⭐ **THE DIRECTION THAT HOLDS IS THE ONE THAT IS USELESS HERE.**
`socketBaseLH_of_socketBaseL` gives `SocketBaseL → SocketBaseLH h`, so an `LH` rider — whose
socket sits in HYPOTHESIS position under a `∀` — is a **STRONGER** Prop than its landed twin:
`S16BandLaneCBoundedLH h K → S16BandLaneCBoundedL K` is the implication that would follow, and
the converse, which is the one a consumer at `h ≥ 2` would want, is **NOT** claimed and is
false in general at `h ≥ 2`.  Only the `h = 1` twin laws below are stated, and they are stated
as theorems rather than left as docstring claims.

⟦IMPORT DIRECTION⟧  This file does **not** import `Salt.MR.HSeamCheck`.  `HSeamCheck` is a leaf
(`All.lean` is its only importer) and it hosts the integration acceptance for this lane, so the
edge runs `HSeamCheck → S16FlatTerminalLinearLH`; the reverse edge is a cycle Lake rejects.

**PURELY ADDITIVE.**  No landed declaration is touched.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — THE BAND-LANE RIDER AT THE INFLATED SOCKET -/

/-- **⟦THE BAND-LANE `C` RIDER, AT THE INFLATED SOCKET⟧** (`S16BandLaneCBoundedLH`) —
`S16FlatTerminalLinear.S16BandLaneCBoundedL` with **both** of its
`∀ H L q j A s, SocketBaseL R M H L q j A s →` quantifiers read at
`HDoorSupply.SocketBaseLH h R M H L q j A s`.  Everything else — the `x₀`/`Cband` witness, the
`log Cband ≤ 40` cap, the `C'` bound, the band base `DoorBandBase_L_gk` and the `t0BandB`
conclusion — is byte-identical to the landed rider.

The landed rider has no producer in the corpus; this one re-quantifies that same open rider at
the inflated socket.  `s16BandLaneCBoundedLH_one_iff` pins it. -/
def S16BandLaneCBoundedLH (h K : ℕ) : Prop :=
  ∃ (x₀ : ℕ) (Cband : ℝ), 0 < Cband ∧ Real.log Cband ≤ 40 ∧ ∀ (M : ℕ), 1 ≤ M →
    ∃ C' : ℝ, 0 < C' ∧
      C' ≤ (Cband * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1)
          * (M : ℝ) ^ (2.1 : ℝ) ∧
      ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
        ((∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
            DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
          ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
            ∀ χ : DirichletCharacter ℂ q,
              (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                ≤ t0BandB (((A + s : ℕ)) : ℝ)
                    (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))

/-! ## §1 — THE CROSSING BOUND AT THE INFLATED SOCKET -/

/-- **⟦THE CROSSING BOUND AT THE INFLATED SOCKET⟧** (`S15CrossingBound_LH_gk`) —
`S16FlatTerminalLinear.S15CrossingBound_L_gk` with its one
`∀ H L q j A s, SocketBaseL R M H L q j A s →` quantifier read at `SocketBaseLH h`.

⭐ **THE `ε_r` WINDOW DOES NOT MOVE.**  The exponent `-theta293 + (theta293 - 1/500)` is
carried UNCHANGED: the window is `h`-blind, and at `h = 1` it is discharged socket-free at the
landed site.  A `1/(500·h)` here would be a different object, not a port. -/
def S15CrossingBound_LH_gk (h K : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
    ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
      (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
          ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
        ≤ 8 * (0 : ℝ) ^ 2
          + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                \ seamBall (((A + s : ℕ)) : ℝ) 0)
              ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                  (calP (AdoorL M) (s13GK K M))
                  (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                  (mrAlpha (1 / 12)) 2,
              ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
              * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + (theta293 - 1 / 500)))


/-! ## §2 — THE `h = 1` TWIN LAWS (the anti-drift gate) -/

/-- ⭐ **THE BAND-LANE RIDER AT `h = 1` IS THE LANDED RIDER**
(`s16BandLaneCBoundedLH_one_iff`) — the anti-drift gate for §0.  A def that did not reduce to
its landed twin at `h = 1` would be a different definition wearing the same name, and nothing
downstream could see the drift: both occurrences of the socket sit in HYPOTHESIS position, so a
drifted def would still elaborate everywhere it is consumed.  Stated as a theorem, not asserted
in a docstring. -/
theorem s16BandLaneCBoundedLH_one_iff (K : ℕ) :
    S16BandLaneCBoundedLH 1 K ↔ S16BandLaneCBoundedL K := by
  unfold S16BandLaneCBoundedLH S16BandLaneCBoundedL
  simp only [socketBaseLH_one_iff]

/-- ⭐ **THE CROSSING BOUND AT `h = 1` IS THE LANDED CROSSING BOUND**
(`s15CrossingBound_LH_gk_one_iff`) — the anti-drift gate for §1, and the statement that keeps
H2c honest: its target at `h = 1` must be the object the landed supplier already meets. -/
theorem s15CrossingBound_LH_gk_one_iff (K : ℕ) (R : ChowlaRegime) (M : ℕ) :
    S15CrossingBound_LH_gk 1 K R M ↔ S15CrossingBound_L_gk K R M := by
  unfold S15CrossingBound_LH_gk S15CrossingBound_L_gk
  simp only [socketBaseLH_one_iff]


/-! ## §3 — HOP 1 AT THE INFLATED SOCKET: the capstone in `¬ logChowlaFails h` form -/

set_option maxHeartbeats 1000000 in
-- The landed hop's own budget: the ~120-line residue re-elaborates against a prefix that
-- gains `h`, two pins and a conjunct.
/-- **⟦HOP 1, AT THE FLAT ROOT, THE LINEAR LADDER AND THE INFLATED SOCKET⟧**
(`logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_LH`) —
`S16FlatTerminalLinear.logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_L`
(`:356`) with the twelve statement moves of the `h` lane and no others:

(i) `1/500 ≤ ε` → `1/(500·h) ≤ ε` and (ii) `1/838400 ≤ δ₀` → `1/(838400·h²) ≤ δ₀`, both the
exit's own exports (`S16FlatTerminalExitH:95-96`); (iii) **`Kc ≤ 2^539` ADDED** as a conjunct
after `Mfl ≤ 2^355` — the `h` lane is here STRICTLY STRONGER than its `h = 1` twin, which has
no such export, because the head's count bound `Kb` serves as the register's `Kc`;
(iv) `hj0` at `4·log(263·h·max 1 (arcDen 12 H))` (`S16ProducersH.g2_of_j0_floor_h`'s demand);
(v) `hdgate` at `h·arcDen 12 H < calP …`; (vi) `hfit` at the inflated envelope
`RSanDoorRhoH ρ h` and the inflated `ℓ`-witness `h⁷·rStrWitness`; (vii)–(xii) every
`SocketBaseL R M H L q j A s →` read at `SocketBaseLH h R M H L q j A s`, bodies unchanged.

⭐ **THE `h` IS PAID ONCE, IN THE CONSTANT, NOT ONCE PER STRATUM.** The envelope
`RSanDoorRhoH ρ h H = ρ / strataResidualH h H ²` cancels the drift gate's residual EXACTLY, so
the ceiling closes at the `h`-FREE `110525·ρ ≤ δ₀²` — the same constant as at `h = 1`, for every
`h ≤ 1096`.

⛔ **`arcFloor36` CANNOT CARRY THIS AND IS NOT USED FOR IT.** The exit's `harc3` demands
`128·(h·arcDen 12 H)³ ≤ H`, and the landed `arcFloor36` route clears `h = 1` by 1.14×, so it
fails from `h = 2`; the floor read here is `loglogFloor50`, through H2a's `arc36_of_regime_h`. -/
theorem logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_LH (h : ℕ) (hh : 0 < h)
    (hh7 : Real.log (h : ℝ) ≤ 7) (K : ℕ) (hK : K ≤ 170000000)
    (hband : S16BandLaneCBoundedLH h K) (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks A β : ℝ) (x₀ Hcap Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Mfl ≤ 2 ^ 355 ∧ Kc ≤ 2 ^ 539 ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
      Hcap ≤ max (flatDesignFloor A)
        (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
        ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
          ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            R.Hlo ≤ max Hcap U1floor ∧
            ∀ (M : ℕ), Mfl ≤ M →
              ∃ C' : ℝ, 0 < C' ∧
                8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                    ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                  -- ⟦A⟧ THE SPINE ARITHMETIC
                  M4DoorGates_L_gk K Cg R M k δ₀ →
                  8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    4 * Real.log (263 * (h : ℝ) * max 1 (arcDen 12 H))
                      ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    (h : ℝ) * arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    m4SmallGradeFits (doorRowFloorL M)
                      (fun H => 2 * RSanDoorRhoH (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) h H)
                      (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H) →
                  -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                  (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                    DoorBaseFrame (A + s) j) →
                  (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                    374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                    GRowsZeroGate'''_L_gk K M (A + s) Cp
                      (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                  (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                        + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                      ≤ (theta293 - epsrf (A + s))
                          * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                  (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                      * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                  (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                    0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                  (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                    calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                      Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                          ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                      ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                  -- ⟦B4 RAW⟧ the crossing bound, carried
                  (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                    ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                      (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                      5 ≤ Real.log (Real.log (2 * T)) →
                      (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                          ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                        ≤ 8 * (0 : ℝ) ^ 2
                          + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                \ seamBall (((A + s : ℕ)) : ℝ) 0)
                              ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                  (calP (AdoorL M) (s13GK K M))
                                  (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                  (mrAlpha (1 / 12)) 2,
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                          + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                              * (Real.log (((A + s : ℕ)) : ℝ))
                                  ^ (-theta293 + epsrf (A + s)))) →
                  (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                    DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                    DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                    ¬ logChowlaFails h R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kb, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, hCapLe, hroad⟩ :=
      m4_second_road_L2_H_gk_flatRoot_L_exit h hh hh7 K A₀ hA₀
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_H_L_gk h hh hh7 K hK
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cband, hCband0, hCband40, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kb, δ₀, Ct, Cq, cs, T₀, Kq, Ks, A, β, x₀,
    max Hcap (max arcFloor36 loglogFloor50),
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKb, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, s11_grade_floor_hoistCb_prod_le Cband hCband0 hCband40, hKbb,
    hβ, hA26, hA₀A, hAge, flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hMfloor
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the absorbed floor the `h` lane must read⟧ `arcFloor36` cannot carry `h³` (1.14×)
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`; the head's count bound IS the register's `Kc`
  set δs : ℝ := s12DeltaSock δ₀ Kb with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKb
  have hδssq : δs ^ 2 = δ₀ / (16 * Kb) := s12DeltaSock_sq hδ₀ hKb
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned at LH
  have hbase : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨b1, b2, b3, b4, b5⟩ := hbase5 H L q j A s hb
    exact ⟨b1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, b2, b3, b4, b5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE AT THE INFLATED SOCKET⟧
  have hrow : M4ChiSummedFreeRowH_L_gk h K R M
      (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TERMINAL CEILING⟧ the residual's square cancels the envelope EXACTLY: `h`-FREE
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 * (108 / 5 * RSanDoorRhoH ρ h H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_deltaH hh hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road at shift `h`, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kb))
    (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) (RSanDoorRhoH ρ h)
    (fun H => (h : ℝ) ^ 7 * rStrWitness H)
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
          (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRhoH_nonneg hρpos.le h H)
    (fun H => rStrWitness_mul_nonneg h H) ?_ (m4_arith_gate4_rhoH_L h M ρ)
    (fun H _ _ => rStrWitness_G1_h h H) ?_
    (arc36_of_regime_h hh hh7 hllfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hbcl := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRhoH ρ h H)
      (Ftr := fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) (H := H)
      (by have := RSanDoorRhoH_nonneg hρpos.le h H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRhoH ρ h H))
      (by have := rStrWitness_mul_nonneg h H
          simpa using (by linarith : (0:ℝ) ≤ 2 * ((h : ℝ) ^ 7 * rStrWitness H)))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor, with the `h` inside the log
    intro H hlo hhi
    have hh1 : 1 ≤ h := hh
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh1 hlo
    have hSR1 : (1 : ℝ) ≤ strataResidualH h H := one_le_strataResidualH harc1
    have hSRsq : (1 : ℝ) ≤ strataResidualH h H ^ 2 := by nlinarith
    have hRSle : RSanDoorRhoH ρ h H ≤ rSanWitness H := by
      have hle1 : RSanDoorRhoH ρ h H ≤ 1 := by
        unfold RSanDoorRhoH
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans hle1 (le_max_left _ _)
    have hG := g2_of_j0_floor_h h hh H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRhoH ρ h H)
      (Ftr := fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) hH0 (hfit H hlo hhi)
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
            (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRhoH ρ h H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRhoH ρ h H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
            * (108 / 5 * RSanDoorRhoH ρ h H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
        * (108 / 5 * RSanDoorRhoH ρ h H)) ≤ 2 * δs ^ 2 := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kb) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly, at the head's `Kb`
    have hval : 2 * Kb * (δ₀ / (8 * Kb)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

/-! ## §4 — THE DISCHARGERS THE `h` FIRE NEEDS (words 4, 6, 7, and the envelope's direction) -/

/-- ⭐ **THE INFLATED ENVELOPE IS THE SMALLER ONE** (`RSanDoorRhoH_le_RSanDoorRho`) — same
numerator, larger denominator (`strataResidualH h H = strataResidual H + log h` past the
window floor).  Stated because the inflation's DIRECTION is the thing a reader gets backwards:
the SOCKET gets weaker and the ENVELOPE gets smaller, and those are not the same monotonicity.
Stated past the window floor, which is the only place the `h` lane reads it. -/
theorem RSanDoorRhoH_le_RSanDoorRho {ρ : ℝ} (hρ : 0 ≤ ρ) {h : ℕ} (hh : 1 ≤ h)
    {R : ChowlaRegime} {H : ℕ} (hlo : R.Hlo ≤ H) :
    RSanDoorRhoH ρ h H ≤ RSanDoorRho ρ H := by
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harch : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh hlo
  have hS1 : (1 : ℝ) ≤ strataResidual H := by
    have := Real.log_nonneg harc1
    unfold strataResidual; linarith
  have hSh1 : (1 : ℝ) ≤ strataResidualH h H := one_le_strataResidualH harch
  have hle : strataResidual H ≤ strataResidualH h H := by
    unfold strataResidual strataResidualH
    have := Real.log_le_log (by linarith : (0 : ℝ) < arcDen 12 H)
      (by nlinarith : arcDen 12 H ≤ (h : ℝ) * arcDen 12 H)
    linarith
  unfold RSanDoorRhoH RSanDoorRho
  exact div_le_div_of_nonneg_left hρ (by nlinarith) (by nlinarith)

/-- **⟦GATE 8 AT THE INFLATED CAP⟧** (`s13_gate8_L_gk_h`, wave H2b word 4) —
`S13FramesLinear.s13_gate8_L_gk` with the cap inflated to `h · arcDen 12 H`.

⛔ **THE MARGIN IS IN THE SIGNATURE, NOT IN THE PROSE.**  The route is
`log(h·arcDen 12 H) = log h + 12·loglog H ≤ 7 + 12·Λ`, closed against
`AdoorL M · log 2 ≥ 242·Λ·log 2 > 167.7·Λ`, which needs `7 < 155.7·Λ` — a LOWER bound on `Λ`.
Without one the statement is FALSE (take `12·Λ = A·log 2 − 3`, `M = 1`, `H = R.Hhi`:
`7 + A·log 2 − 3 > A·log 2`), so `hΛ1 : 1 ≤ Λ` is carried as a hypothesis.  At the fire site
both new binders are already in scope: `hgr` is the register's `gRows`, `hΛ1` the regime's own
`Λ`-floor. -/
theorem s13_gate8_L_gk_h {h : ℕ} {R : ChowlaRegime} {K M : ℕ} {Λ : ℝ} (hh : 0 < h)
    (hh7 : Real.log (h : ℝ) ≤ 7)
    (hΛ : Real.log (Real.log (R.Hhi : ℝ)) ≤ Λ) (hΛ1 : 1 ≤ Λ)
    (hgr : 242 * Λ ≤ ((AdoorL M : ℕ) : ℝ)) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (h : ℝ) * arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
  intro H hlo hhi
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hLH : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
  have hL0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hLH
  have hlogarc : Real.log (arcDen 12 H) = 12 * Real.log (Real.log (H : ℝ)) := by
    rw [arcDen, Real.log_rpow hL0]
  have hle := le_trans (s13_loglog_le_of_range (R := R) hlo hhi) hΛ
  have hlogP : Real.log ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
      = ((AdoorL M : ℕ) : ℝ) * Real.log 2 := log_calP_one_gen _ _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
    have hpos : 0 < calP (AdoorL M) (s13GK K M) 1 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast hpos
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hmul : 242 * Λ * Real.log 2 ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hgr (by linarith)
  have hlogmul : Real.log ((h : ℝ) * arcDen 12 H)
      = Real.log (h : ℝ) + Real.log (arcDen 12 H) :=
    Real.log_mul (by positivity) (by linarith)
  have hlt : Real.log ((h : ℝ) * arcDen 12 H)
      < Real.log ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
    rw [hlogmul, hlogarc, hlogP]
    nlinarith [hmul, hle, hh7, hΛ1, hlog2]
  have hexp := Real.exp_lt_exp.mpr hlt
  rwa [Real.exp_log (by nlinarith : (0 : ℝ) < (h : ℝ) * arcDen 12 H), Real.exp_log hP0] at hexp

/-- **⟦`DoorBaseFrame` AT THE INFLATED SOCKET⟧** (`doorBaseFrame_at_socket_LH`, word 6) —
`S16FlatTerminalLinear.doorBaseFrame_at_socket_L` with `hb` read at `SocketBaseLH h`.  The
thirteen-name `obtain` is unchanged because both sockets are 13-conjunct in the SAME order;
the body reads exactly TWO of the thirteen (`hLH`, `hjL`), neither of them an inflated one,
so the proof replays verbatim. -/
theorem doorBaseFrame_at_socket_LH {h : ℕ} {R : ChowlaRegime} {M H L q j A s : ℕ}
    {C₁ M₀ K ρ : ℝ}
    (hb : SocketBaseLH h R M H L q j A s)
    (hfr : DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) C₁ M₀ K ρ) :
    DoorBaseFrame (A + s) j := by
  obtain ⟨hlo, hhi, hLH, hqp, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  have hAs : 0 < A + s := by omega
  have hX0 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hLX : (10 : ℝ) ^ 10 ≤ Real.log (((A + s : ℕ)) : ℝ) := frames_logX_ge_L hfr
  have hLXn : (10000000000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    le_trans (by norm_num) hLX
  have hLX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  -- ⟦the `H`-side scales⟧
  have hH1 : (1 : ℝ) < Real.log (H : ℝ) := hfr.one_lt_logH
  have hH0 : (0 : ℝ) < Real.log (H : ℝ) := by linarith
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    rcases lt_or_ge 0 (H : ℝ) with h | h
    · exact h
    · exfalso
      have hz : (H : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg H)
      rw [hz, Real.log_zero] at hH1; linarith
  have hlam : (50 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := hfr.Hfloor
  have hlr : (0 : ℝ) ≤ Real.log (1 / ρ) := hfr.logInvRho_nonneg
  -- ⟦the window index⟧
  have hjR : (1078 : ℝ) ≤ (j : ℝ) := by have := hfr.jfloor; linarith
  have hjN : 1078 ≤ j := by exact_mod_cast hjR
  have hLne : L ≠ 0 := by
    rintro rfl
    rw [Nat.log_zero_right] at hjL
    omega
  have h2jH : 2 ^ j ≤ H :=
    le_trans (le_trans (Nat.pow_le_pow_right (by norm_num) hjL)
      (Nat.pow_log_le_self 2 hLne)) hLH
  have h2jHR : ((2 ^ j : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h2jH
  have h2jpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  -- ⟦the ARM, at its weakest reading: `log X_d ≥ e·log H`⟧
  have hstep : Real.log (Real.log (H : ℝ)) + 1 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
    have := hfr.armWeak; linarith
  have hEH : Real.log (H : ℝ) * Real.exp 1 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h1 := Real.exp_le_exp.mpr hstep
    rwa [Real.exp_add, Real.exp_log hH0, Real.exp_log hLX0] at h1
  have hHX : 2.7 * Real.log (H : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have he27 : (2.7 : ℝ) < Real.exp 1 := exp_one_gt_27
    nlinarith [hEH, he27, hH0]
  have hllX : Real.log (Real.log (((A + s : ℕ)) : ℝ)) ≤ Real.log (((A + s : ℕ)) : ℝ) - 1 := by
    have := Real.add_one_le_exp (Real.log (Real.log (((A + s : ℕ)) : ℝ)))
    rw [Real.exp_log hLX0] at this; linarith
  -- ⟦the shared lower bound on the annulus height `2·X_d/2^j`⟧
  have hXH : Real.exp (Real.log (((A + s : ℕ)) : ℝ) - Real.log (H : ℝ))
      = (((A + s : ℕ)) : ℝ) / (H : ℝ) := by
    rw [Real.exp_sub, Real.exp_log hX0, Real.exp_log hHpos]
  have hdiv : (((A + s : ℕ)) : ℝ) / (H : ℝ)
      ≤ 2 * ((((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ)) := by
    have hd : (((A + s : ℕ)) : ℝ) / (H : ℝ)
        ≤ (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) := by gcongr
    have hpos : (0 : ℝ) ≤ (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) := by positivity
    linarith
  have hann : Real.exp (Real.log (((A + s : ℕ)) : ℝ) - Real.log (H : ℝ))
      ≤ 2 * ((((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ)) := by rw [hXH]; exact hdiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ⟦`X_exp`⟧
    have h := Real.exp_le_exp.mpr (by linarith : (1 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ))
    rwa [Real.exp_log hX0] at h
  · -- ⟦`X_three`⟧
    have h := frames_base_ge hAs hLX
    have h3 : (3 : ℝ) ≤ 1 + (10 : ℝ) ^ 10 := by norm_num
    linarith
  · -- ⟦`h_four`⟧
    have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hR : ((2 ^ 2 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast h4
    simpa using hR
  · -- ⟦`h_window`⟧
    have hprod : (((A + s : ℕ)) : ℝ) * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-(1 / 5 : ℝ))
        = Real.exp (Real.log (((A + s : ℕ)) : ℝ)
            + Real.log (Real.log (((A + s : ℕ)) : ℝ)) * (-(1 / 5 : ℝ))) := by
      rw [Real.rpow_def_of_pos hLX0, Real.exp_add, Real.exp_log hX0]
    rw [hprod]
    calc ((2 ^ j : ℕ) : ℝ) ≤ (H : ℝ) := h2jHR
      _ = Real.exp (Real.log (H : ℝ)) := (Real.exp_log hHpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · -- ⟦`tann`⟧
    rw [TannGate]
    have hsq : Real.sqrt (Real.log (((A + s : ℕ)) : ℝ))
        ≤ Real.log (((A + s : ℕ)) : ℝ) / 60 := by
      have hnn : (0 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) / 60 := by positivity
      have hle : Real.log (((A + s : ℕ)) : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ) / 60) ^ 2 := by
        nlinarith [hLXn, hLX0]
      calc Real.sqrt (Real.log (((A + s : ℕ)) : ℝ))
          ≤ Real.sqrt ((Real.log (((A + s : ℕ)) : ℝ) / 60) ^ 2) := Real.sqrt_le_sqrt hle
        _ = Real.log (((A + s : ℕ)) : ℝ) / 60 := Real.sqrt_sq hnn
    rw [← Real.sqrt_eq_rpow]
    refine le_trans (Real.exp_le_exp.mpr ?_) hann
    linarith
  · -- ⟦`ceil5`⟧
    have he5 : Real.exp 5 ≤ 1000 := by
      have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have hh : Real.exp 5 = (Real.exp 1) ^ (5 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      rw [hh]
      have hc : (Real.exp 1) ^ (5 : ℕ) ≤ (2.7182818286 : ℝ) ^ (5 : ℕ) :=
        pow_le_pow_left₀ hpos.le he.le 5
      have hn : (2.7182818286 : ℝ) ^ (5 : ℕ) ≤ 1000 := by norm_num
      linarith
    have hlog : Real.exp 5
        ≤ Real.log (2 * ((((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ))) := by
      have h1 : Real.log (((A + s : ℕ)) : ℝ) - Real.log (H : ℝ)
          ≤ Real.log (2 * ((((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ))) := by
        have h2 := Real.log_le_log (Real.exp_pos _) hann
        rwa [Real.log_exp] at h2
      linarith
    have := Real.log_le_log (Real.exp_pos 5) hlog
    rwa [Real.log_exp] at this

/-- **⟦THE `gRows` CONSUMER AT THE INFLATED SOCKET⟧**
(`s15_gRows_const_at_socket_flat_doorLH_gk`, word 7) —
`S16FlatTerminalLinear.s15_gRows_const_at_socket_flat_doorL_gk` with `hb` at `SocketBaseLH h`.

⛔ The landed body's FIRST line built the landed socket out of `hb` (`socketBase_of_socketBaseL`)
— exactly the step that does not exist at `h ≥ 2`.  It is deleted, and the two consumers that
read it are re-pointed at the LH substrate already landed in `S16ProducersH`
(`s13_socketBase_loglogA_LH`, `s12c_llX_ge_LH`, binder order `hh hh7 hfl hb`).  The socket is
read in exactly four places and nothing else moves. -/
theorem s15_gRows_const_at_socket_flat_doorLH_gk (K : ℕ) {h : ℕ} (hh : 0 < h)
    (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime}
    {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hM : 1 ≤ M)
    (hρ0 : 0 < ρ) (_hρ1 : ρ ≤ 1)
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000)
    (hlvl : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        + (1 / 3) * Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ))
        + (-Real.log ρ)
      ≤ (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2) :
    GRowsZeroGate'''_L_gk K M (A + s) 0 (constPool ρ R.Hhi) := by
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le _hρ1
  have hQ0 : (0 : ℝ)
      ≤ Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) := by
    rw [calQK_L_one_gk_eq]; exact s15_loglogQ1_L_nonneg hM
  obtain ⟨-, hL50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have hp2 : 27 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ := by
    linarith [hlvl, hQ0, hL50, hlogρ]
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hAs : 0 < A + s := by omega
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA_LH hh hh7 hfl hb
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hllle : Real.log (Real.log (((A + s : ℕ)) : ℝ)) ≤ Real.log (((A + s : ℕ)) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hll := s12c_llX_ge_LH hh hh7 hfl hb
  have hcore := flat_lambda_core_17 hlam50
  have hendbud : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + (-Real.log ρ)
      ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h1 : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        ≤ 14 * Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := by linarith
    linarith [hcore, hll, hllle, hrho, h1]
  exact gRowsZeroGate'''_L_gk_of_budget K hM hAs hρ0 (by linarith) hp2 hendbud

set_option maxHeartbeats 1000000 in
-- The landed `s13_smallGradeFits`' own budget (`S13FramesA:580`): the two log-comparison
-- claims re-elaborate, here each carrying two more terms.
/-- **⟦A-5 AT THE INFLATED SOCKET⟧** (`s13_smallGradeFits_h`, wave H2b word 5) —
`S13FramesA.s13_smallGradeFits` with the envelope at `RSanDoorRhoH ρ h` and the `ℓ`-witness at
`h⁷·rStrWitness`, from ONE gate that carries the shift TWICE:

`(7/10)·j₀ + 3·(log 9 + 84·loglog H + 2·log(strataResidualH h H) − log ρ) + 7·log h ≤ log H`.

⭐ **THE TWO COSTS ARE NOT THE SAME KIND, AND ONLY ONE OF THEM IS PAID IN FULL.**  The
`ℓ`-witness costs `7·log h` on the LEFT of the demand and is carried at coefficient ONE (the
`+ 7·log h` term); the residual costs `2·(log S_h − log S)` on the RIGHT, and the gate pays it
at coefficient THREE because `log(strataResidualH h H)` sits inside the landed `3·(…)` — an
over-payment of `4·(log S_h − log S)`, kept because it is what makes the gate a single
readable line.

⛔ **AND THE `h` ARM NEEDS A FLOOR THE `h = 1` ARM DOES NOT.**  At `h = 1` the first claim
closes with slack `0.0018·log H + 0.24·G ≥ 0`, true for free.  At `h ≥ 2` it must absorb
`4.11·log h ≤ 28.8`, which needs `84·log(log H) ≳ 118` — i.e. `log H ≥ 4.1`.  The regime's own
`4·10⁶ ≤ H` gives `log H ≥ 15` and `log log H ≥ 2`, and those two lines are carried explicitly
below for exactly this reason. -/
theorem s13_smallGradeFits_h {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {j₀ H : ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hlo : R.Hlo ≤ H)
    (hgate : (7 / 10 : ℝ) * (j₀ : ℝ)
        + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
            + 2 * Real.log (strataResidualH h H) - Real.log ρ)
        + 7 * Real.log (h : ℝ)
      ≤ Real.log (H : ℝ)) :
    m4SmallGradeFits j₀ (fun H => 2 * RSanDoorRhoH ρ h H)
      (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H := by
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hlogh0 : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_nonneg hh1
  obtain ⟨hlog3up, hlog3lo⟩ := s13_log_three_bounds
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  -- ⟦the window scale⟧
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hH0 : (0 : ℝ) < (H : ℝ) := by
    have : (0 : ℕ) < H := by omega
    exact_mod_cast this
  set Λ : ℝ := Real.log (H : ℝ) with hΛdef
  -- ⟦the two floors the `h` arm needs: `log H ≥ 15` and `loglog H ≥ 2`⟧
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp15 : Real.exp 15 ≤ 4000000 := by
    have h15 : Real.exp 15 = (Real.exp 1) ^ (15 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    have hp : (Real.exp 1) ^ (15 : ℕ) ≤ (2.7182818286 : ℝ) ^ (15 : ℕ) :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he1.le 15
    rw [h15]
    calc (Real.exp 1) ^ (15 : ℕ) ≤ (2.7182818286 : ℝ) ^ (15 : ℕ) := hp
      _ ≤ 4000000 := by norm_num
  have hΛ15 : (15 : ℝ) ≤ Λ := by
    rw [hΛdef, Real.le_log_iff_exp_le hH0]
    linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hΛ1 : (2 : ℝ) < Λ := by linarith
  have hexp2 : Real.exp 2 ≤ 15 := by
    have h2 : Real.exp 2 = (Real.exp 1) ^ (2 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    have hp : (Real.exp 1) ^ (2 : ℕ) ≤ (2.7182818286 : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he1.le 2
    rw [h2]
    calc (Real.exp 1) ^ (2 : ℕ) ≤ (2.7182818286 : ℝ) ^ (2 : ℕ) := hp
      _ ≤ 15 := by norm_num
  have hlogΛ2 : (2 : ℝ) ≤ Real.log Λ := by
    rw [Real.le_log_iff_exp_le hΛ0]
    linarith
  have hlogΛ0 : (0 : ℝ) < Real.log Λ := by linarith
  -- ⟦the arc scale, as a nat power⟧
  have harcpow : arcDen 12 H = Λ ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harch : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh hlo
  set S : ℝ := strataResidualH h H with hSdef
  have hS1 : (1 : ℝ) ≤ S := one_le_strataResidualH harch
  have hS0 : (0 : ℝ) < S := by linarith
  have hlogS0 : (0 : ℝ) ≤ Real.log S := Real.log_nonneg hS1
  have hRSt : rStrWitness H = Λ ^ (84 : ℕ) := by
    rw [rStrWitness, harcpow, ← pow_mul]
    exact max_eq_right (one_le_pow₀ (by linarith))
  -- ⟦the dyadic index⟧
  set L : ℕ := Nat.log 2 H with hLdef
  have hLpow : ((2 : ℝ)) ^ L ≤ (H : ℝ) := by
    have h : (2 : ℕ) ^ L ≤ H := Nat.pow_log_le_self 2 (by omega)
    have h' : ((2 ^ L : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h
    simpa using h'
  have hLlog : (L : ℝ) * Real.log 2 ≤ Λ := by
    have h := Real.log_le_log (by positivity) hLpow
    rwa [Real.log_pow] at h
  -- ⟦the three log numerals⟧
  have hlog32 : Real.log (3 / 2 : ℝ) ≤ 24 / 41 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith
  have hlog320 : (0 : ℝ) ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog43 : Real.log (4 / 3 : ℝ) ≤ 2890 / 10000 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    linarith
  have hlog83 : Real.log (8 / 3 : ℝ) ≤ 9825 / 10000 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast
    linarith
  -- ⟦the `(3/2)^L` spend⟧
  have hu32 : (L : ℝ) * Real.log (3 / 2 : ℝ) ≤ 24 / 41 * Λ := by
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    calc (L : ℝ) * Real.log (3 / 2 : ℝ) ≤ (L : ℝ) * (24 / 41 * Real.log 2) :=
          mul_le_mul_of_nonneg_left hlog32 hL0
      _ = 24 / 41 * ((L : ℝ) * Real.log 2) := by ring
      _ ≤ 24 / 41 * Λ := by linarith
  -- ⟦`G ≥ 0`⟧
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  have h9 : (0 : ℝ) ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hG0 : (0 : ℝ) ≤ Real.log 9 + 84 * Real.log Λ + 2 * Real.log S - Real.log ρ := by
    linarith
  have hj0 : (0 : ℝ) ≤ (j₀ : ℝ) := Nat.cast_nonneg j₀
  -- ⟦the two claims, by log comparison⟧
  set Q : ℝ := (H : ℝ) ^ 2 * RSanDoorRhoH ρ h H with hQdef
  have hRS : RSanDoorRhoH ρ h H = ρ / S ^ 2 := rfl
  have hQ0 : (0 : ℝ) < Q := by
    rw [hQdef, hRS]; positivity
  have hlogQ : Real.log Q = 2 * Λ + Real.log ρ - 2 * Real.log S := by
    rw [hQdef, hRS, Real.log_mul (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlogD : Real.log (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)))
      = Real.log 2 + 7 * Real.log (h : ℝ) + 84 * Real.log Λ := by
    rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hD0 : (0 : ℝ) < 2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)) := by positivity
  have hclaim1 : 9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
      * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))) ≤ Q := by
    have hP0 : (0 : ℝ) < 9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
        * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))) := by positivity
    have hlogP : Real.log (9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
          * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))))
        = Real.log (9 / 2) + (L : ℝ) * Real.log (3 / 2 : ℝ)
          + (j₀ : ℝ) * Real.log (4 / 3 : ℝ) + Λ
          + (Real.log 2 + 7 * Real.log (h : ℝ) + 84 * Real.log Λ) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, hlogD]
    have hle : Real.log (9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
        * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)))) ≤ Real.log Q := by
      rw [hlogP, hlogQ]
      have h92 : Real.log (9 / 2 : ℝ) + Real.log 2 = Real.log 9 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        norm_num
      have h43 : (j₀ : ℝ) * Real.log (4 / 3 : ℝ) ≤ (j₀ : ℝ) * (2890 / 10000) :=
        mul_le_mul_of_nonneg_left hlog43 hj0
      linarith [hgate, hu32, h43, h92, hlogΛ2, hh7, h9, hlogS0, hlogρ, hΛ15, hlogh0]
    have h := Real.exp_le_exp.mpr hle
    rwa [Real.exp_log hP0, Real.exp_log hQ0] at h
  have hclaim2 : 9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀
      * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))) ≤ Q := by
    have hP0 : (0 : ℝ) < 9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀
        * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))) := by positivity
    have hlogP : Real.log (9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀
          * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))))
        = Real.log (9 / 5) + (L : ℝ) * Real.log (3 / 2 : ℝ)
          + (j₀ : ℝ) * Real.log (8 / 3 : ℝ)
          + (Real.log 2 + 7 * Real.log (h : ℝ) + 84 * Real.log Λ) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, hlogD]
    have hle : Real.log (9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀
        * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)))) ≤ Real.log Q := by
      rw [hlogP, hlogQ]
      have h95 : Real.log (9 / 5 : ℝ) + Real.log 2 ≤ Real.log 9 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        exact Real.log_le_log (by norm_num) (by norm_num)
      have h83 : (j₀ : ℝ) * Real.log (8 / 3 : ℝ) ≤ (j₀ : ℝ) * (9825 / 10000) :=
        mul_le_mul_of_nonneg_left hlog83 hj0
      linarith [hgate, hu32, h83, h95, hlogh0, hG0]
    have h := Real.exp_le_exp.mpr hle
    rwa [Real.exp_log hP0, Real.exp_log hQ0] at h
  -- ⟦assemble through the landed threshold lemma⟧
  refine m4SmallGradeFits_of_threshold (D := 2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)))
    (le_of_eq (by rw [hRSt])) ?_ ?_
  · have := RSanDoorRhoH_nonneg hρ0.le h H
    linarith
  · rw [← hLdef]
    have hexpand : (9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
          + 9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀)
            * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)))
        = 9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
            * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ)))
          + 9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀
            * (2 * ((h : ℝ) ^ 7 * Λ ^ (84 : ℕ))) := by ring
    rw [hexpand]
    have hQ2 : (H : ℝ) ^ 2 * (2 * RSanDoorRhoH ρ h H) = 2 * Q := by rw [hQdef]; ring
    rw [hQ2]
    linarith

/-- **⟦THE WINDOW GATE AT THE INFLATED RESIDUAL, FROM THE HALF-WINDOW FLOOR⟧**
(`s13_winFit_h_of_halfWindow_gen`) — `S13FramesLinear.s13_winFit_of_halfWindow_gen` with the
residual read at `strataResidualH h H` and the `ℓ`-witness's `7·log h` added.

⛔ **THE ENTRY POINT MOVED ONE STEP EARLIER, AND IT HAD TO.**  The commission routes word 5's
`_of_MSelect'` form through `MSelect'_L_gk.winFit`.  That field is a bare inequality
`(7/10)·j₀ + 3·(… landed residual …) ≤ log H` with **no exposed reserve**: from it one cannot
get the same line plus `91` for any positive amount, because nothing in it says `log H` exceeds
its own left side.  The reserve the commission correctly names — `w = √(log H) ≥ 7.2·10^10`
against a spend of order `900·w` — lives in the HALF-WINDOW floor, one step upstream, which is
exactly where the landed `_gen` lemma spends it.  So the `h` twin is taken from `hhalf`, not
from `winFit`, and the extra `6·log h + 7·log h ≤ 91` is paid out of `w²/2 − 648·w`. -/
theorem s13_winFit_h_of_halfWindow_gen {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {jr ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hhalf : (7 / 10 : ℝ) * jr + 3 * Real.log (1 / ρ) ≤ Real.log (R.Hlo : ℝ) / 2) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (7 / 10 : ℝ) * jr
          + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
              + 2 * Real.log (strataResidualH h H) - Real.log ρ)
          + 7 * Real.log (h : ℝ)
        ≤ Real.log (H : ℝ) := by
  intro H hlo _
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hlogh0 : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_nonneg hh1
  have hHlo4 : 4000000 ≤ R.Hlo := R.hHlo_floor
  have hH4 : 4000000 ≤ H := le_trans hHlo4 hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hHloR : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast hHlo4
  have hloR : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo
  have hlogmono : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hloR
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have hlogHbig : (4000000 : ℝ) ≤ Real.log (H : ℝ) := le_trans s13_four_million_le_exp50 hexp50
  set w : ℝ := Real.sqrt (Real.log (H : ℝ)) with hw
  have hw2 : w ^ 2 = Real.log (H : ℝ) := Real.sq_sqrt hlogH0.le
  have hw0 : (0 : ℝ) < w := by rw [hw]; exact Real.sqrt_pos.mpr hlogH0
  have hw2000 : (2000 : ℝ) ≤ w := by nlinarith [hw2, hw0, hlogHbig]
  have hlogw : Real.log w = Real.log (Real.log (H : ℝ)) / 2 := by
    rw [hw]; exact Real.log_sqrt hlogH0.le
  have hlogwle : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hw0
  have hllH : Real.log (Real.log (H : ℝ)) ≤ 2 * w - 2 := by rw [hlogw] at hlogwle; linarith
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hSval : strataResidualH h H
      = 1 + Real.log (h : ℝ) + 12 * Real.log (Real.log (H : ℝ)) := by
    rw [strataResidualH, harcpow,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by linarith
  have hS1 : (1 : ℝ) ≤ strataResidualH h H := by rw [hSval]; linarith
  have hlogS : Real.log (strataResidualH h H) ≤ strataResidualH h H - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hSle : strataResidualH h H - 1 ≤ 24 * w - 24 + 7 := by rw [hSval]; linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hlog9 : Real.log 9 ≤ 4 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; linarith
  have hinv : Real.log (1 / ρ) = - Real.log ρ := by rw [one_div, Real.log_inv]
  rw [hinv] at hhalf
  nlinarith [hhalf, hlogmono, hllH, hlogS, hSle, hlog9, hw2, hw2000, hw0, hh7, hlogh0]

/-- **⟦A-5 AT THE INFLATED SOCKET, FROM THE REGISTER'S HALF-WINDOW FIELD⟧**
(`s13_smallGradeFits_of_halfWindow_L_gk_h`, wave H2b word 5, second half) — the form the `h`
fire consumes, at `j₀ := doorRowFloorL M`.

⛔ **NAMED FOR ITS INPUT, WHICH IS NOT THE COMMISSION'S.**  The commission calls this
`s13_smallGradeFits_of_MSelect'_L_gk_h` and feeds it `hS.winFit`; that cannot work (see
`s13_winFit_h_of_halfWindow_gen`), so it is fed the register's own `half` field instead and
named for it.  At the fire site the substitution is free: `hsel.half` is in scope exactly where
`hS` is, and `hS` is itself built from `hsel.half`. -/
theorem s13_smallGradeFits_of_halfWindow_L_gk_h {h : ℕ} (hh : 0 < h)
    (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime} {M : ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hfl : loglogFloor50 ≤ R.Hlo)
    (hhalf : (7 / 10 : ℝ) * ((doorRowFloorL M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
      ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 2) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      m4SmallGradeFits (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
        (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H :=
  fun H hlo hhi =>
    s13_smallGradeFits_h hh hh7 hρ0 hρ1 hlo
      (s13_winFit_h_of_halfWindow_gen hh hh7 hfl hhalf H hlo hhi)

/-! ## §5 — HOP 2 AT THE INFLATED SOCKET: the conditional sharp form -/

/-- **⟦THE `j₀`-FLOOR GATE WITH THE SHIFT'S `28` IN IT⟧**
(`s13_g2_jfloor_of_MSelect'_L_gk_shift28`) — `S13FramesLinear.s13_g2_jfloor_of_MSelect'_L_gk`
with the `28` that H2a's word 6 carries in its hypothesis.  The margin is the register's own:
`4·log 263 + 48·Λ + 28 ≤ 52 + 48·Λ ≤ 100·Λ ≤ 242·Λ ≤ AdoorL M ≤ doorRowFloorL M`, so the
numeral is paid 2.4× over at `Λ = 1` and the ratio only improves. -/
theorem s13_g2_jfloor_of_MSelect'_L_gk_shift28 (K : ℕ) {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime}
    {M : ℕ} (hΛ : 1 ≤ Λ) (hS : MSelect'_L_gk K Cg δ₀ Λ ρ R M) :
    4 * Real.log 263 + 48 * Λ + 28 ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
  have hlog := s13_log263_le_six
  have hdr : ((AdoorL M : ℕ) : ℝ) ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    have h : AdoorL M ≤ doorRowFloorL M := by
      rw [doorRowFloorL]
      calc AdoorL M = 1 * AdoorL M := (one_mul _).symm
        _ ≤ M * AdoorL M := Nat.mul_le_mul_right _ hS.hM
    exact_mod_cast h
  have hgr := hS.gRows
  nlinarith [hgr, hdr, hlog, hΛ]

set_option maxHeartbeats 1000000 in
-- Same cause as the landed HOP 4: the residue re-elaborates against the prefix.
/-- **⟦HOP 2, AT THE FLAT ROOT, THE LINEAR LADDER AND THE INFLATED SOCKET⟧**
(`logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_LH`) —
`S16FlatTerminalLinear.logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_L` (`:1034`)
on §3, with moves (i)–(iii) and the crossing rider at `S15CrossingBound_LH_gk h`.

⭐ **THE REGISTER DOES NOT MOVE.**  `S15Sel''_L_gk` is SOCKET-BLIND — its twelve fields are
regime-level real inequalities and neither it nor `MSelect'_L_gk` mentions a socket anywhere —
so hop 2 at shift `h` consumes the LANDED register unchanged.  That is why this wave costs
what it costs: the expensive-looking object turned out to be `h`-invariant. -/
theorem logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_LH (h : ℕ) (hh : 0 < h)
    (hh7 : Real.log (h : ℝ) ≤ 7) (K : ℕ) (hK : K ≤ 170000000)
    (hband : S16BandLaneCBoundedLH h K) (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (x₀ Hcap Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Mfl ≤ 2 ^ 355 ∧ Kc ≤ 2 ^ 539 ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
      Hcap ≤ max (flatDesignFloor A)
        (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
        ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          ∀ M : ℕ,
            S15Sel''_L_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
            S15CrossingBound_LH_gk h K R M → ¬ logChowlaFails h R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, A, β, x₀, Hcap, Hopq, Mfl, hCg, hε, hKc,
    hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hMflb, hKcb, hβ, hA26,
    hA₀A, hAge, hCapLe, hmain⟩ :=
    logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_LH h hh hh7 K hK hband
      A₀ hA₀
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hcap, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCgle, hεpin, hδpin, hMflb, hKcb, hβ, hA26, hA₀A, hAge, hCapLe, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15ArmH h δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15ArmH h δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15ArmH_demoted h δ₀ ρ R.Hhi R.ω) hRarm
  have hhω : (0 : ℝ) ≤ (h : ℝ) * (R.ω : ℝ) := by positivity
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 ((h : ℝ) * (R.ω : ℝ)) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hhω ?_ hhi) (s15ArmH_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family at the inflated socket, arm read at `h·ω`
  have harith := s15_doorArithFrameRho_L_familyH'' (C₁ := fun _ : ℕ => (1 : ℝ)) hh hsel.hM
    hρ0 hρ1 hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧ — the register and its bridges are SOCKET-BLIND
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦slot 3⟧ H2a word 6's OUTER step, over the `h`-free family, with the `28` in the gate
  have hj0raw : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * max 1 (arcDen 12 H)) + 28 ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    have hgate := s13_g2_jfloor_of_MSelect'_L_gk_shift28 K (by linarith) hS
    have hbase := s13_g2_jfloor_gen (R := R)
      (F := ((doorRowFloorL M : ℕ) : ℝ) - 28) le_rfl (by linarith)
    intro H hlo hhi
    linarith [hbase H hlo hhi]
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_of_MSelect'_L_gk_h hh hh7 hj0raw)
    (s13_gate8_L_gk_h hh hh7 le_rfl (by linarith) hsel.gRows)
    (s13_smallGradeFits_of_halfWindow_L_gk_h hh hh7 hρ0 hρ1 hfl hsel.half)
    (fun H L q j A s hb => doorBaseFrame_at_socket_LH hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorLH_gk K hh hh7 hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flatH hh hh7 hfl hb hlam50 htow hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flatH hh hh7 hfl hb hρ0 hlam50 htow hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flatH hh hh7 hfl hb hρ0 hlam50 htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM
        (s15_block_at_socketH_L_gk K hh hh7 hb (hHreg H hb.1 hb.2.1) hsel.blk)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'H_L_gk K hh hh7 hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (s15ArmH_rho hRarm) harith hsel.x0M (fun _ => le_rfl) hgrade
      (fun H L q j A s hb =>
        s15_block_at_socketH_L_gk K hh hh7 hb (hHreg H hb.1 hb.2.1) hsel.blk))
    harith

/-! ## §6 — HOP 3: THE FIRST `h`-TERMINAL, WITH THE REGISTER SUPPLIED AT SHIFT `h` -/

set_option maxHeartbeats 1000000 in
-- Same cause as the landed terminal: the 27-item `obtain` and the register call re-elaborate
-- against a prefix that gains `h`, two pins and a conjunct.
/-- **⟦THE FLAT TERMINAL AT THE LINEAR LADDER AND THE INFLATED SOCKET⟧**
(`logChowla2_witnessed_scale_flat_LH`) — `S16FlatTerminalLinear.logChowla2_witnessed_scale_flat_L`
(`:1672`) at shift `h`, with the `S15` register **SUPPLIED, NOT CARRIED**, from
`FlatFloorBump.s15_sel''_L_gk_witness_flat_bumped` at `c := h`.

⭐ **`Kc ≤ 2^539` LEAVES THE DEBT LIST HERE AND BECOMES AN EXPORTED FACT.**  At `h = 1` it is
rider 1 of the landed terminal — an ask about an opaque `∃ C, 0 < C ∧ …`.  On the `h` lane the
head's OWN count bound `Kb` plays the register's `Kc` and carries `Kb ≤ 2^539` out of
`S16FlatTerminalExitH` (H2a word 1d), so the rider is `REMOVED-BECAUSE-PROVEN` and appears as a
conjunct instead.  **This is the one place the `h` lane is strictly stronger than its `h = 1`
twin, and it is stronger because the shift forced the count to be computed rather than
assumed.**

⛔ **`Ct ≤ 2^23` IS NOT REMOVED and is carried exactly as at `h = 1`** — the constant-pool
fuse's `Ct` is still an opaque `∃ Ct, 0 < Ct`, and nothing in the shift touches it.

⟦THE SURVIVING HYPOTHESIS LIST⟧ `Ct ≤ 2^23`, the `x₀` window, `Hopq ≤ flatDesignBase A`, and
the crossing bound at the inflated socket — the `h`-twin of the landed list minus rider 1. -/
theorem logChowla2_witnessed_scale_flat_LH (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    (hband : S16BandLaneCBoundedLH h 32000000) (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Mfl ≤ 2 ^ 355 ∧ Kc ≤ 2 ^ 539 ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
      (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
      (Ct ≤ 2 ^ 23 →
        (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
        Hopq ≤ flatDesignBase A →
        ∀ g : ℕ → ℕ → ℕ, ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (S15CrossingBound_LH_gk h 32000000 R (flatDoorM A) →
            ¬ logChowlaFails h R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hcap, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hKcb, hβ, hA26, hA₀A, hAge, hCapLe, hbody⟩ :=
    logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_LH h hh hh7 32000000
      (by norm_num) hband A₀ hA₀
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1` (the census needs `ε ≤ 1/2`)
  obtain ⟨R0, hR0eps, -, -, -, -⟩ :=
    hbody (flatWitFloor ε β A Hopq) (fun _ _ => 0) (flatCap_le_flatWitFloor hCapLe)
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  -- ⟦THE `ε` PIN, CAST⟧ the shift rides inside the denominator
  have hεR : (1 : ℝ) / (500 * (h : ℝ)) ≤ (ε : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hεpin
    rw [show ((((1 : ℚ) / (500 * (h : ℚ))) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) by push_cast; ring]
      at hc
    exact hc
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hopq, Mfl,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCgle, hεpin, hδpin, hMflb, hKcb, hβ, hA26, hA₀A, hAge,
    fun hopq => flat_witFloor_eq_designBase_h hh hh7 hA26 hβ hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hCtb hx0win hopq g
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase_h hh hh7 hA26 hβ hεR hε2 hε hεpin hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRtow, hdes, hwin, ?_⟩
  intro hcross
  -- ⟦THE REGISTER, SUPPLIED AT SHIFT `h`⟧ at the flat design modulus
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have hKle : (32000000 : ℕ) ≤ 170000000 * flatDoorM A := by
    calc (32000000 : ℕ) ≤ 170000000 * 1 := by norm_num
      _ ≤ 170000000 * flatDoorM A := Nat.mul_le_mul_left _ hM1
  have heps : (1 : ℚ) / (2 ^ 9 * (h : ℚ)) ≤ R.eps := by
    rw [hReps]
    exact le_trans (Salt.Entropy.Chowla.eps_line_h h hh) hεpin
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  have hsel := s15_sel''_L_gk_witness_flat_bumped (c := h) hA26 32000000 hKle hh
    (Salt.Entropy.Chowla.h_le_1096_of_log_le_seven hh hh7) hh7 hδ₀ hδpin hKc hKcb
    hCt hCtb hCgle hMflb hx0win heps hlo hwin
  exact hfire (flatDoorM A) hsel hcross

end Salt.MR
