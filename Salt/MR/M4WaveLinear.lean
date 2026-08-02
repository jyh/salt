/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4LadderLinear
import Salt.MR.M4WaveClosed
import Salt.MR.M4Band
import Salt.MR.M4Maximal
import Salt.MR.M4NonCoprime
import Salt.MR.M4DoorRow
import Salt.MR.M4Puncture

/-!
# `M4WaveLinear` — the M4 wave's χ-twisted door datum at `AdoorL M = 2^36·M`

⟦LADDER-L, G1 §4⟧  THE SEED OF THE WHOLE LADDER WAVE IS HERE: `doorChiCoeff_L` /
`doorChiCoeff_L_gk`, a DEFINITION whose type is door-free but whose BODY reads the ladder at
the door's anchor.  Everything else on this page — the band/puncture coefficient laws
(`M4Band`, `M4Puncture`), the row page (`M4DoorRow`), the non-coprime class page
(`M4NonCoprime`), the maximal step (`M4Maximal`) — is a restatement over it, at
`AdoorL M = 2^36·M` with the `G`-slot unchanged (`3072·M`, resp. `s13GK K M`).

The one place the re-cut costs a hypothesis is `classSup_le_dilate_L` /
`m4_nonCoprime_classMeanSq_L`, which ride `DoorLadderLinear.memS_dilate_door_L`'s `1 ≤ M`;
every consumer of the class page already carries it (`M4DoorGates_L.hM`).

`door_length_gate_L(_iff)` is NOT re-cut here — `DoorLinear` already landed it as
`doorL_length_gate`/`doorL_length_gate_iff`; this page consumes those.

Source pins: `docs/blueprints/flags.md` ⟦COMPOSE-FLAT-2⟧, ⟦LINEAR-PAGE⟧.
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators
open MeasureTheory
open Salt.ExpSum
open Salt.Entropy.Chowla

/-! ### `M4WaveClosed` :194 — `M4ClassBlockMeanSq` -/
/-- **THE ANALYTIC ITEM** (`M4ClassBlockMeanSq_L`) — the per-class block mean square of the
door's sieved `λ`, at the arc's own modulus range.  This is what the M4 wave's supply side
must deliver, and it is the mean-square shape: the sum over the block's door indices of the
squared class sup, NOT a maximum over the block. -/
def M4ClassBlockMeanSq_L (R : ChowlaRegime) (M k : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ r, r < q →
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff_L M) H n q r) ^ 2
        ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-! ### `M4WaveClosed` :362 — `doorSievedWindow` -/
/-- **THE DOOR'S SIEVED WINDOW**, named once: `{n < m ≤ n+K : m ∈ 𝒮}` at the door's own
K-family.  `M4ClassPrice.sievedWindow` at `p := MemS (calP …) (calQK …) 2`. -/
def doorSievedWindow_L (M K n : ℕ) : Finset ℕ :=
  sievedWindow (MemS (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2) K n

/-! ### `M4WaveClosed` :706 — `doorChiCoeff` -/
/-- **THE SIEVED, χ-TWISTED DATUM** `doorChiCoeff_L χ M = 1_𝒮·λχ̄` at the door's own K-family.
The ⟦lam collision⟧: `liouChi`, never `lamChi` — the sum runs over integers. -/
def doorChiCoeff_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) : ℕ → ℂ :=
  memSCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 (liouChi χ)

/-! ### `M4WaveClosed` :711 — `absWindowSum_doorChiCoeff_zero` -/
/-- The indicator-restricted window sum IS the sum over the sieved window. -/
theorem absWindowSum_doorChiCoeff_zero_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) :
    absWindowSum (doorChiCoeff_L χ M) H n 0 = ∑ m ∈ doorSievedWindow_L M H n, liouChi χ m := by
  rw [absWindowSum_zero, doorSievedWindow_L, sievedWindow, Finset.sum_filter]
  rfl

/-! ### `M4WaveClosed` :717 — `M4ChiRowMeanSq` -/
/-- **THE ROW INPUT, PER CHARACTER** (`M4ChiRowMeanSq_L`) — the mean square of the door's
sieved, χ-twisted, UN-PHASED datum on one ladder block, in `ThmA2.thm_a2'_of_rows_L`' own
currency (`1/X·∫_X^{2X}‖(1/H)·shortSum a (seamS0 N X) y H‖²` at `X = X_{i+1}`, `N = 2X_{i+1}`,
`h = H`).

The instantiation is forced, not chosen — the two pins `X_d = X` and `N = 2X_d` are exactly
`M4MeanSq.m4_meansq_per_chi_gen_L`'s, and the window length is the door's own `H`.  This is
`M4ClassPrice.M4RowMeanSqUnphased` at the χ-twisted datum: the same block, the same seam
index set, the same currency, with `liouvilleC` replaced by `liouChi χ` under the sieve. -/
def M4ChiRowMeanSq_L (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
      1 / (doorLadder R.x H (i + 1) : ℝ)
          * (∫ y in (doorLadder R.x H (i + 1) : ℝ)..(2 * (doorLadder R.x H (i + 1) : ℝ)),
              ‖((1 / (H : ℝ) : ℝ) : ℂ)
                  * shortSum (doorChiCoeff_L χ M)
                      (seamS0 (2 * doorLadder R.x H (i + 1))
                        (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
        ≤ MS H

/-! ### `M4WaveClosed` :889 — `M4ClassBlockMeanSq_gk` -/
/-- **THE ANALYTIC ITEM AT THE LEVER** — `M4ClassBlockMeanSq_L` (:198). -/
def M4ClassBlockMeanSq_L_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ r, r < q →
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
        ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-! ### `M4WaveClosed` :996 — `doorSievedWindow_gk` -/
/-- **THE DOOR'S SIEVED WINDOW AT THE LEVER** — `doorSievedWindow_L` (:364), with the
sub-window binder α-renamed `K ↦ Kw`.  THE SIEVE SET GENUINELY MOVES: `𝒫`, `𝒬` grow with the
lever, so this is a different `Finset`. -/
def doorSievedWindow_L_gk (K M Kw n : ℕ) : Finset ℕ :=
  sievedWindow (MemS (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2) Kw n

/-! ### `M4WaveClosed` :1241 — `doorChiCoeff_gk` -/
/-- **THE SIEVED, χ-TWISTED DATUM AT THE LEVER** — `doorChiCoeff_L` (:708). -/
def doorChiCoeff_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) : ℕ → ℂ :=
  memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 (liouChi χ)

/-! ### `M4WaveClosed` :1245 — `absWindowSum_doorChiCoeff_zero_gk` -/
/-- The indicator-restricted window sum IS the sum over the levered sieved window —
`absWindowSum_doorChiCoeff_zero_L` (:712). -/
theorem absWindowSum_doorChiCoeff_zero_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M H n : ℕ) :
    absWindowSum (doorChiCoeff_L_gk K χ M) H n 0
      = ∑ m ∈ doorSievedWindow_L_gk K M H n, liouChi χ m := by
  rw [absWindowSum_zero, doorSievedWindow_L_gk, sievedWindow, Finset.sum_filter]
  rfl

/-! ### `M4WaveClosed` :1254 — `M4ChiRowMeanSq_gk` -/
/-- **THE ROW INPUT, PER CHARACTER, AT THE LEVER** — `M4ChiRowMeanSq_L` (:726). -/
def M4ChiRowMeanSq_L_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
      1 / (doorLadder R.x H (i + 1) : ℝ)
          * (∫ y in (doorLadder R.x H (i + 1) : ℝ)..(2 * (doorLadder R.x H (i + 1) : ℝ)),
              ‖((1 / (H : ℝ) : ℝ) : ℂ)
                  * shortSum (doorChiCoeff_L_gk K χ M)
                      (seamS0 (2 * doorLadder R.x H (i + 1))
                        (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
        ≤ MS H

/-! ### `M4Band` :167 — `doorChiCoeff_seamCoefW_band` -/
/-- **THE DOOR'S BAND PAIR LAW** (`doorChiCoeff_seamCoefW_band_L`) — `memSCoeff_seamCoefW_band`
at the door's own K-family, where `doorChiCoeff_L χ M` is the sieved datum by definition. -/
theorem doorChiCoeff_seamCoefW_band_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd P Q : ℕ)
    (hgate : ∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (3072 * M) M j < P) :
    SeamCoefW Xd P Q (winCut Xd (doorChiCoeff_L χ M)) (doorChiCoeff_L χ M) (liouChi χ) :=
  memSCoeff_seamCoefW_band χ (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2
    Xd P Q hgate

/-! ### `M4Band` :313 — `doorChiCoeff_seamCoefWS_band_H` -/
/-- **THE DOOR'S STRICT HALF-OPEN BAND PAIR LAW** (`doorChiCoeff_seamCoefWS_band_H_L`). -/
theorem doorChiCoeff_seamCoefWS_band_H_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd P Q : ℕ)
    (a : ℕ → ℂ)
    (hgate : ∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (3072 * M) M j < P)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_L χ M n) :
    SeamCoefWS Xd P Q a (doorChiCoeff_L χ M) (liouChi χ) :=
  memSCoeff_seamCoefWS_band_H χ (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2
    Xd P Q a hgate haH

/-! ### `M4Band` :322 — `doorChiCoeff_seamCoefWS_at_door_H` -/
/-- **`hcoefPin` AT THE DOOR, STRICT** (`doorChiCoeff_seamCoefWS_at_door_H_L`) — the strict
sibling of `doorChiCoeff_seamCoefW_at_door_H_L`: the band gate discharged from the capstone's
own `hQXd`/`hPlow`, and NO endpoint obligation at all. -/
theorem doorChiCoeff_seamCoefWS_at_door_H_L {q : ℕ} (χ : DirichletCharacter ℂ q) {M Xd P Q : ℕ}
    {X : ℝ} {a : ℕ → ℂ} (hM : 1 ≤ M) (hX : 1 < Real.log X)
    (hQlog : Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log X))
    (hPlow : P83 X theta293 ≤ (P : ℝ))
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_L χ M n) :
    SeamCoefWS Xd P Q a (doorChiCoeff_L χ M) (liouChi χ) :=
  doorChiCoeff_seamCoefWS_band_H_L χ M Xd P Q a
    (door_band_gate_of_log (by omega : 1 ≤ 3072 * M) hX hQlog hPlow) haH

/-! ### `M4Band` :334 — `doorChiCoeff_seamCoefW_band_H` -/
/-- **THE DOOR'S HALF-OPEN BAND PAIR LAW** (`doorChiCoeff_seamCoefW_band_H_L`) —
`memSCoeff_seamCoefW_band_H` at the door's own K-family. -/
theorem doorChiCoeff_seamCoefW_band_H_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd P Q : ℕ)
    (a : ℕ → ℂ)
    (hgate : ∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (3072 * M) M j < P)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_L χ M n)
    (ha0 : a Xd = 0) (hend : doorChiCoeff_L χ M Xd = 0) :
    SeamCoefW Xd P Q a (doorChiCoeff_L χ M) (liouChi χ) :=
  memSCoeff_seamCoefW_band_H χ (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2
    Xd P Q a hgate haH ha0 hend

/-! ### `M4Band` :345 — `doorChiCoeff_seamCoefW_at_door_H` -/
/-- **`hcoefPin` AT THE DOOR, HALF-OPEN** (`doorChiCoeff_seamCoefW_at_door_H_L`) — the half-open
sibling of `M4DoorRow.doorChiCoeff_seamCoefW_at_door_L`: the band gate discharged from the
capstone's own `hQXd`/`hPlow`, the endpoint discharged by `hend`. -/
theorem doorChiCoeff_seamCoefW_at_door_H_L {q : ℕ} (χ : DirichletCharacter ℂ q) {M Xd P Q : ℕ}
    {X : ℝ} {a : ℕ → ℂ} (hM : 1 ≤ M) (hX : 1 < Real.log X)
    (hQlog : Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log X))
    (hPlow : P83 X theta293 ≤ (P : ℝ))
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_L χ M n)
    (ha0 : a Xd = 0) (hend : doorChiCoeff_L χ M Xd = 0) :
    SeamCoefW Xd P Q a (doorChiCoeff_L χ M) (liouChi χ) :=
  doorChiCoeff_seamCoefW_band_H_L χ M Xd P Q a
    (door_band_gate_of_log (by omega : 1 ≤ 3072 * M) hX hQlog hPlow) haH ha0 hend

/-! ### `M4Band` :405 — `doorChiCoeff_seamCoefW_band_gk` -/
/-- **THE DOOR'S BAND PAIR LAW, AT THE G-LEVER** (`doorChiCoeff_seamCoefW_band_L_gk`). -/
theorem doorChiCoeff_seamCoefW_band_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M Xd P Q : ℕ)
    (hgate : ∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (s13GK K M) M j < P) :
    SeamCoefW Xd P Q (winCut Xd (doorChiCoeff_L_gk K χ M)) (doorChiCoeff_L_gk K χ M)
      (liouChi χ) :=
  memSCoeff_seamCoefW_band χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2
    Xd P Q hgate

/-! ### `M4Band` :414 — `doorChiCoeff_seamCoefWS_band_H_gk` -/
/-- **THE DOOR'S STRICT HALF-OPEN BAND PAIR LAW, AT THE G-LEVER**
(`doorChiCoeff_seamCoefWS_band_H_L_gk`). -/
theorem doorChiCoeff_seamCoefWS_band_H_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M Xd P Q : ℕ) (a : ℕ → ℂ)
    (hgate : ∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (s13GK K M) M j < P)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_L_gk K χ M n) :
    SeamCoefWS Xd P Q a (doorChiCoeff_L_gk K χ M) (liouChi χ) :=
  memSCoeff_seamCoefWS_band_H χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M)
    2 Xd P Q a hgate haH

/-! ### `M4Band` :424 — `doorChiCoeff_seamCoefWS_at_door_H_gk` -/
/-- **`hcoefPin` AT THE DOOR, STRICT, AT THE G-LEVER**
(`doorChiCoeff_seamCoefWS_at_door_H_L_gk`).  The band gate is the calibration's own at the
levered base; `1 ≤ s13GK K M` is `GLever.one_le_s13GK`. -/
theorem doorChiCoeff_seamCoefWS_at_door_H_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {M Xd P Q : ℕ} {X : ℝ} {a : ℕ → ℂ} (hM : 1 ≤ M) (hX : 1 < Real.log X)
    (hQlog : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log X))
    (hPlow : P83 X theta293 ≤ (P : ℝ))
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_L_gk K χ M n) :
    SeamCoefWS Xd P Q a (doorChiCoeff_L_gk K χ M) (liouChi χ) :=
  doorChiCoeff_seamCoefWS_band_H_L_gk K χ M Xd P Q a
    (door_band_gate_of_log (one_le_s13GK K hM) hX hQlog hPlow) haH

/-! ### `M4Band` :436 — `doorChiCoeff_seamCoefW_band_H_gk` -/
/-- **THE DOOR'S HALF-OPEN BAND PAIR LAW, AT THE G-LEVER**
(`doorChiCoeff_seamCoefW_band_H_L_gk`). -/
theorem doorChiCoeff_seamCoefW_band_H_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M Xd P Q : ℕ) (a : ℕ → ℂ)
    (hgate : ∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (s13GK K M) M j < P)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_L_gk K χ M n)
    (ha0 : a Xd = 0) (hend : doorChiCoeff_L_gk K χ M Xd = 0) :
    SeamCoefW Xd P Q a (doorChiCoeff_L_gk K χ M) (liouChi χ) :=
  memSCoeff_seamCoefW_band_H χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2
    Xd P Q a hgate haH ha0 hend

/-! ### `M4Band` :447 — `doorChiCoeff_seamCoefW_at_door_H_gk` -/
/-- **`hcoefPin` AT THE DOOR, HALF-OPEN, AT THE G-LEVER**
(`doorChiCoeff_seamCoefW_at_door_H_L_gk`). -/
theorem doorChiCoeff_seamCoefW_at_door_H_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {M Xd P Q : ℕ} {X : ℝ} {a : ℕ → ℂ} (hM : 1 ≤ M) (hX : 1 < Real.log X)
    (hQlog : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log X))
    (hPlow : P83 X theta293 ≤ (P : ℝ))
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_L_gk K χ M n)
    (ha0 : a Xd = 0) (hend : doorChiCoeff_L_gk K χ M Xd = 0) :
    SeamCoefW Xd P Q a (doorChiCoeff_L_gk K χ M) (liouChi χ) :=
  doorChiCoeff_seamCoefW_band_H_L_gk K χ M Xd P Q a
    (door_band_gate_of_log (one_le_s13GK K hM) hX hQlog hPlow) haH ha0 hend

/-! ### `M4Maximal` :1016 — `M4ChiDyadicRowMeanSq` -/
/-- **THE ROW INPUT, PER DYADIC LENGTH AND SHIFT** (`M4ChiDyadicRowMeanSq_L`) — the mean square
of the door's sieved, χ-twisted, UN-PHASED datum in `ThmA2.thm_a2'_of_rows_L`' own currency, at
the window length `h = 2^j` (`j ≤ log₂H`) and the scale `X = X_{i+1} + s` (`s ≤ H`), with the
capstone's two pins `X_d = X` and `N = 2X_d` intact at every instance.

**LENGTH-GRADED**: the grade is `MS j H` — one per dyadic length, not one for all of them.
⟦WALL 2⟧ (the header) is why: the capstone cannot be STATED below `j = M·AdoorL M`, and at
`j = 0` the quantity is the block density, `≍ 1`.  A supplier therefore owes a small grade
only where the capstone speaks, and the trivial grade everywhere else; §5's split is what
makes that enough. -/
def M4ChiDyadicRowMeanSq_L (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, ∀ s ≤ H,
      1 / ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)
          * (∫ y in ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)..(2
                * ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)),
              ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                  * shortSum (doorChiCoeff_L χ M)
                      (seamS0 (2 * (doorLadder R.x H (i + 1) + s))
                        ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
        ≤ MS j H

/-! ### `M4Maximal` :1519 — `M4ChiDyadicRowMeanSq_gk` -/
/-- **THE GRADED DYADIC ROW DATUM AT THE LEVER** — `M4ChiDyadicRowMeanSq_L` (:1026). -/
def M4ChiDyadicRowMeanSq_L_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, ∀ s ≤ H,
      1 / ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)
          * (∫ y in ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)..(2
                * ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)),
              ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                  * shortSum (doorChiCoeff_L_gk K χ M)
                      (seamS0 (2 * (doorLadder R.x H (i + 1) + s))
                        ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
        ≤ MS j H

/-! ### `M4NonCoprime` :299 — `classSup_le_dilate` -/
/-- **THE POINTWISE TRANSPORT.**  The class sup at `(q, r)` and base `n` is under the class
sup at the reduced pair `(q/d₀, r/d₀)` and base `⌊n/d₀⌋`, read at the uniform dilated length
`⌊H/d₀⌋ + 1`.  Loss-free at every length: the underlying step is the equality of
`M4ClassPrice` §3, taken at the residual frequency `0` (no arc datum, hence no enlarged
cap). -/
theorem classSup_le_dilate_L {M H q r n : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) :
    classSup (doorSievedCoeff_L M) H n q r
      ≤ classSup (doorSievedCoeff_L M) (H / Nat.gcd r q + 1) (n / Nat.gcd r q)
          (q / Nat.gcd r q) (r / Nat.gcd r q) := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  refine classSup_le fun K hK => ?_
  have heq := norm_sum_windowClass_memS_dilate_L (M := M) (J := 2) (q := q) (r := r)
    (H := K) (n := n) (W := W) hM hq hqW hW
  have hlen : dilLen K n (Nat.gcd r q) ≤ H / Nat.gcd r q + 1 :=
    le_trans (dilLen_le K n hd) (Nat.add_le_add_right (Nat.div_le_div_right hK) 1)
  simp only [doorSievedCoeff_L]
  rw [heq]
  exact le_classSup _ _ _ _ _ hlen

/-! ### `M4NonCoprime` :324 — `M4CoprimeBlockMeanSq` -/
/-- **THE COPRIME FAMILY** (the interval-general, length-general coprime block mean square).

Three generalisations against `M4WaveClosed.M4ClassBlockMeanSq_L`, each forced by the
re-index and by nothing else:

* the block is a FREE half-open interval `(A, B]` with `0 < A` — the dilated block is not a
  `doorLadder` block;
* the window length is a FREE `L ≤ H`, priced at its OWN `L²` — the dilated window has
  length `≈ H/d₀`;
* the fit carries `M4ClassPrice` §5's endpoint slack, at `4` (see `dilBlock_reindex_fit`).

The modulus range is unchanged (`0 < q'`, `q' ≤ arcDen 12 H`), and it covers every reduced
modulus `q₀ = q/d₀ ≤ q` the transport can produce — this is the "at all `q' ≤ q`" of the
freeze.  The grade is read at the AMBIENT `H`, so no monotonicity of `B_cl` is assumed
anywhere. -/
def M4CoprimeBlockMeanSq_L (R : ChowlaRegime) (M : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H → ∀ r, r < q → Nat.Coprime q r →
      ∀ A B : ℕ, 0 < A → B + L ≤ 2 * A + 4 →
        ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff_L M) L n q r) ^ 2
          ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

/-! ### `M4NonCoprime` :372 — `m4_nonCoprime_classMeanSq` -/
/-- **⟦R2⟧ — `m4_nonCoprime_classMeanSq_L`.**  The coprime family gives `M4ClassBlockMeanSq_L` at
EVERY class of `q`, at the SAME grade:

* `d₀ = (r,q) = 1` — the datum is read at `L = H`, `(A, B] = ` the door block, verbatim
  (the door block's `doorLadder_fit` is the interface's fit with slack to spare);
* `d₀ > 1` — the pointwise transport (§4), the `d₀`-to-one fibre count (§1) onto the
  re-indexed block (§2), the datum at `(q/d₀, r/d₀)`, and ⟦THE d₀-LEDGER⟧ (§3).

**No loss.**  The output grade is `B_cl H · H² · X_{i+1}`, identical to the coprime half's,
so the `q²` slot `M4ClassPrice` §4 opened is untouched and the composed drift price is
unchanged.  The two added hypotheses are the module header's ⟦THE TWO GATES⟧ — both
`H`-only regime thresholds of ⟦THE FINAL REGISTER⟧'s class (a). -/
theorem m4_nonCoprime_classMeanSq_L {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hM : 1 ≤ M) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ))
    (hcp : M4CoprimeBlockMeanSq_L R M Bcl) :
    M4ClassBlockMeanSq_L R M k Bcl := by
  intro H hlo hhi q hq hqQ i _ r hrq
  -- ⟦the block, and the ladder's two facts⟧
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
  have hfit : doorLadder R.x H i + H ≤ 2 * doorLadder R.x H (i + 1) := doorLadder_fit R.x H i
  have hApos : 0 < doorLadder R.x H (i + 1) := by omega
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  by_cases hcase : Nat.gcd r q = 1
  · -- ⟦d₀ = 1⟧ the class is already coprime: the datum, read at the door block
    have hcopqr : Nat.Coprime q r := by
      rw [Nat.Coprime, Nat.gcd_comm]; exact hcase
    exact hcp H hlo hhi H le_rfl q hq hqQ r hrq hcopqr
      (doorLadder R.x H (i + 1)) (doorLadder R.x H i) hApos (by omega)
  · -- ⟦d₀ > 1⟧ ONE dilation, then the `d₀`-to-one re-index of the block
    have hd2 : 2 ≤ Nat.gcd r q := by omega
    -- ⟦the modulus gates⟧
    have hdq : Nat.gcd r q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)
    have h2q : 2 * q ≤ H := by
      have hR : ((2 * q : ℕ) : ℝ) ≤ (H : ℝ) := by
        push_cast
        have := harc H hlo hhi
        linarith
      exact_mod_cast hR
    have hdA : Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hdA2 : 2 * Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hA2 : 2 ≤ doorLadder R.x H (i + 1) / Nat.gcd r q :=
      (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hA'pos : 0 < doorLadder R.x H (i + 1) / Nat.gcd r q - 1 := by omega
    -- ⟦the reduced pair⟧
    have hq₀ : 0 < q / Nat.gcd r q :=
      Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)) hd
    have hq₀Q : ((q / Nat.gcd r q : ℕ) : ℝ) ≤ arcDen 12 H := by
      refine le_trans ?_ hqQ
      exact_mod_cast Nat.div_le_self q (Nat.gcd r q)
    have hr₀q₀ : r / Nat.gcd r q < q / Nat.gcd r q := by
      rcases Nat.lt_or_ge (r / Nat.gcd r q) (q / Nat.gcd r q) with hlt | hcon
      · exact hlt
      refine absurd hrq (not_lt.mpr ?_)
      have hqd : Nat.gcd r q * (q / Nat.gcd r q) = q :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right r q)
      have h1 : Nat.gcd r q * (q / Nat.gcd r q)
          ≤ Nat.gcd r q * (r / Nat.gcd r q) := Nat.mul_le_mul le_rfl hcon
      have h2 : Nat.gcd r q * (r / Nat.gcd r q) ≤ r := by
        rw [Nat.mul_comm]; exact Nat.div_mul_le_self r (Nat.gcd r q)
      rw [← hqd]
      exact h1.trans h2
    have hcop₀ : Nat.Coprime (q / Nat.gcd r q) (r / Nat.gcd r q) :=
      (m4_class_dilate_coprime hq r).symm
    -- ⟦the dilated window length⟧
    have hH'H : H / Nat.gcd r q + 1 ≤ H := by
      have hstep : H / Nat.gcd r q ≤ H / 2 := Nat.div_le_div_left hd2 (by norm_num)
      omega
    -- ⟦the pointwise transport, then the fibre count, then the datum, then the ledger⟧
    have hpt : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff_L M) H n q r) ^ 2
          ≤ (fun n' => (classSup (doorSievedCoeff_L M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2) (n / Nat.gcd r q) := by
      intro n _
      have hle := classSup_le_dilate_L (M := M) (H := H) (q := q) (r := r) (n := n)
        (W := arcDen 12 H) hM hq hqQ (hgate H hlo hhi)
      have h0 := classSup_nonneg (doorSievedCoeff_L M) H n q r
      simp only
      nlinarith
    have hmaps : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        n / Nat.gcd r q ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
          (doorLadder R.x H i / Nat.gcd r q) := fun n hn => div_mem_reindexed hd hdA hn
    have hdatum := hcp H hlo hhi (H / Nat.gcd r q + 1) hH'H (q / Nat.gcd r q) hq₀ hq₀Q
      (r / Nat.gcd r q) hr₀q₀ hcop₀ (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
      (doorLadder R.x H i / Nat.gcd r q) hA'pos (dilBlock_reindex_fit hd hdA hfit)
    have hd0R : (0 : ℝ) ≤ (Nat.gcd r q : ℝ) := Nat.cast_nonneg _
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff_L M) H n q r) ^ 2
        ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L M) (H / Nat.gcd r q + 1) (n / Nat.gcd r q)
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 := Finset.sum_le_sum hpt
      _ ≤ (Nat.gcd r q : ℝ)
            * ∑ n' ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
                (doorLadder R.x H i / Nat.gcd r q),
              (classSup (doorSievedCoeff_L M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 :=
          sum_Ioc_comp_div_le
            (f := fun n' => (classSup (doorSievedCoeff_L M) (H / Nat.gcd r q + 1) n'
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2)
            (fun _ => sq_nonneg _) (d := Nat.gcd r q) hd hmaps
      _ ≤ (Nat.gcd r q : ℝ)
            * (Bcl H * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) ^ 2
                * ((doorLadder R.x H (i + 1) / Nat.gcd r q - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hdatum hd0R
      _ ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) :=
          d0_ledger hd hH'H (hBcl0 H)

/-! ### `M4NonCoprime` :506 — `M4CoprimeBlockMeanSqN` -/
/-- **THE NARROWED COPRIME FAMILY** (`M4CoprimeBlockMeanSqN_L`) — `M4CoprimeBlockMeanSq_L` with
⟦THE NARROWING⟧ `(H : ℝ) ≤ arcDen 12 H · L` inserted directly after `L ≤ H`, and NOTHING
else changed.  Strictly weaker as a hypothesis on a supplier, strictly stronger as a demand
on a consumer — and `m4_nonCoprime_classMeanSq_N_L` shows the demand is free. -/
def M4CoprimeBlockMeanSqN_L (R : ChowlaRegime) (M : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → (H : ℝ) ≤ arcDen 12 H * (L : ℝ) →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H → ∀ r, r < q → Nat.Coprime q r →
      ∀ A B : ℕ, 0 < A → B + L ≤ 2 * A + 4 →
        ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff_L M) L n q r) ^ 2
          ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

/-! ### `M4NonCoprime` :543 — `m4_nonCoprime_classMeanSq_N` -/
/-- **⟦R2⟧, AT THE NARROWED TWIN** (`m4_nonCoprime_classMeanSq_N_L`).  Byte-for-byte
`m4_nonCoprime_classMeanSq_L` with its coprime datum read at `M4CoprimeBlockMeanSqN_L`: the SAME
hypothesis list, the SAME conclusion `M4ClassBlockMeanSq_L R M k Bcl`, the SAME grade — the
narrowing is discharged inside, at each of the two sites, from facts the proof already had.

* `d₀ = 1`, `L = H`: `(H:ℝ) ≤ arcDen 12 H · H` is `one_le_arcDen_of_regime`;
* `d₀ > 1`, `L = ⌊H/d₀⌋ + 1`: `H ≤ d₀·L` is `Nat.div_add_mod` + `Nat.mod_lt`, and
  `d₀ ≤ q ≤ arcDen 12 H` is `Nat.gcd_dvd_right` + the modulus gate. -/
theorem m4_nonCoprime_classMeanSq_N_L {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hM : 1 ≤ M) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ))
    (hcp : M4CoprimeBlockMeanSqN_L R M Bcl) :
    M4ClassBlockMeanSq_L R M k Bcl := by
  intro H hlo hhi q hq hqQ i _ r hrq
  -- ⟦the block, and the ladder's two facts⟧
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
  have hfit : doorLadder R.x H i + H ≤ 2 * doorLadder R.x H (i + 1) := doorLadder_fit R.x H i
  have hApos : 0 < doorLadder R.x H (i + 1) := by omega
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hH0R : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  by_cases hcase : Nat.gcd r q = 1
  · -- ⟦d₀ = 1⟧ the class is already coprime: the datum, read at the door block, `L = H`
    have hcopqr : Nat.Coprime q r := by
      rw [Nat.Coprime, Nat.gcd_comm]; exact hcase
    have hnarrow : (H : ℝ) ≤ arcDen 12 H * (H : ℝ) := by nlinarith
    exact hcp H hlo hhi H le_rfl hnarrow q hq hqQ r hrq hcopqr
      (doorLadder R.x H (i + 1)) (doorLadder R.x H i) hApos (by omega)
  · -- ⟦d₀ > 1⟧ ONE dilation, then the `d₀`-to-one re-index of the block
    have hd2 : 2 ≤ Nat.gcd r q := by omega
    -- ⟦the modulus gates⟧
    have hdq : Nat.gcd r q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)
    have h2q : 2 * q ≤ H := by
      have hR : ((2 * q : ℕ) : ℝ) ≤ (H : ℝ) := by
        push_cast
        have := harc H hlo hhi
        linarith
      exact_mod_cast hR
    have hdA : Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hdA2 : 2 * Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hA2 : 2 ≤ doorLadder R.x H (i + 1) / Nat.gcd r q :=
      (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hA'pos : 0 < doorLadder R.x H (i + 1) / Nat.gcd r q - 1 := by omega
    -- ⟦the reduced pair⟧
    have hq₀ : 0 < q / Nat.gcd r q :=
      Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)) hd
    have hq₀Q : ((q / Nat.gcd r q : ℕ) : ℝ) ≤ arcDen 12 H := by
      refine le_trans ?_ hqQ
      exact_mod_cast Nat.div_le_self q (Nat.gcd r q)
    have hr₀q₀ : r / Nat.gcd r q < q / Nat.gcd r q := by
      rcases Nat.lt_or_ge (r / Nat.gcd r q) (q / Nat.gcd r q) with hlt | hcon
      · exact hlt
      refine absurd hrq (not_lt.mpr ?_)
      have hqd : Nat.gcd r q * (q / Nat.gcd r q) = q :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right r q)
      have h1 : Nat.gcd r q * (q / Nat.gcd r q)
          ≤ Nat.gcd r q * (r / Nat.gcd r q) := Nat.mul_le_mul le_rfl hcon
      have h2 : Nat.gcd r q * (r / Nat.gcd r q) ≤ r := by
        rw [Nat.mul_comm]; exact Nat.div_mul_le_self r (Nat.gcd r q)
      rw [← hqd]
      exact h1.trans h2
    have hcop₀ : Nat.Coprime (q / Nat.gcd r q) (r / Nat.gcd r q) :=
      (m4_class_dilate_coprime hq r).symm
    -- ⟦the dilated window length⟧
    have hH'H : H / Nat.gcd r q + 1 ≤ H := by
      have hstep : H / Nat.gcd r q ≤ H / 2 := Nat.div_le_div_left hd2 (by norm_num)
      omega
    -- ⟦THE NARROWING, at the dilated length: `H ≤ d₀·L ≤ arcDen·L`⟧
    have hnarrow : (H : ℝ) ≤ arcDen 12 H * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := by
      have hexp : Nat.gcd r q * (H / Nat.gcd r q + 1)
          = Nat.gcd r q * (H / Nat.gcd r q) + Nat.gcd r q := by ring
      have hdm : Nat.gcd r q * (H / Nat.gcd r q) + H % Nat.gcd r q = H :=
        Nat.div_add_mod H (Nat.gcd r q)
      have hmod : H % Nat.gcd r q < Nat.gcd r q := Nat.mod_lt _ hd
      have hnat : H ≤ Nat.gcd r q * (H / Nat.gcd r q + 1) := by omega
      have hR : (H : ℝ) ≤ (Nat.gcd r q : ℝ) * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hdR : (Nat.gcd r q : ℝ) ≤ arcDen 12 H := by
        refine le_trans ?_ hqQ
        exact_mod_cast hdq
      have hL0 : (0 : ℝ) ≤ ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    -- ⟦the pointwise transport, then the fibre count, then the datum, then the ledger⟧
    have hpt : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff_L M) H n q r) ^ 2
          ≤ (fun n' => (classSup (doorSievedCoeff_L M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2) (n / Nat.gcd r q) := by
      intro n _
      have hle := classSup_le_dilate_L (M := M) (H := H) (q := q) (r := r) (n := n)
        (W := arcDen 12 H) hM hq hqQ (hgate H hlo hhi)
      have h0 := classSup_nonneg (doorSievedCoeff_L M) H n q r
      simp only
      nlinarith
    have hmaps : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        n / Nat.gcd r q ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
          (doorLadder R.x H i / Nat.gcd r q) := fun n hn => div_mem_reindexed hd hdA hn
    have hdatum := hcp H hlo hhi (H / Nat.gcd r q + 1) hH'H hnarrow (q / Nat.gcd r q) hq₀ hq₀Q
      (r / Nat.gcd r q) hr₀q₀ hcop₀ (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
      (doorLadder R.x H i / Nat.gcd r q) hA'pos (dilBlock_reindex_fit hd hdA hfit)
    have hd0R : (0 : ℝ) ≤ (Nat.gcd r q : ℝ) := Nat.cast_nonneg _
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff_L M) H n q r) ^ 2
        ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L M) (H / Nat.gcd r q + 1) (n / Nat.gcd r q)
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 := Finset.sum_le_sum hpt
      _ ≤ (Nat.gcd r q : ℝ)
            * ∑ n' ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
                (doorLadder R.x H i / Nat.gcd r q),
              (classSup (doorSievedCoeff_L M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 :=
          sum_Ioc_comp_div_le
            (f := fun n' => (classSup (doorSievedCoeff_L M) (H / Nat.gcd r q + 1) n'
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2)
            (fun _ => sq_nonneg _) (d := Nat.gcd r q) hd hmaps
      _ ≤ (Nat.gcd r q : ℝ)
            * (Bcl H * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) ^ 2
                * ((doorLadder R.x H (i + 1) / Nat.gcd r q - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hdatum hd0R
      _ ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) :=
          d0_ledger hd hH'H (hBcl0 H)

/-! ### `M4NonCoprime` :676 — `classSup_le_dilate_gk` -/
/-- **THE POINTWISE TRANSPORT AT THE LEVER** — `classSup_le_dilate_L` (:304). -/
theorem classSup_le_dilate_L_gk (K : ℕ) {M H q r n : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) :
    classSup (doorSievedCoeff_L_gk K M) H n q r
      ≤ classSup (doorSievedCoeff_L_gk K M) (H / Nat.gcd r q + 1) (n / Nat.gcd r q)
          (q / Nat.gcd r q) (r / Nat.gcd r q) := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  refine classSup_le fun Kw hK => ?_
  have heq := norm_sum_windowClass_memS_dilate_L_gk K (M := M) (J := 2) (q := q) (r := r)
    (H := Kw) (n := n) (W := W) hM hq hqW hW
  have hlen : dilLen Kw n (Nat.gcd r q) ≤ H / Nat.gcd r q + 1 :=
    le_trans (dilLen_le Kw n hd) (Nat.add_le_add_right (Nat.div_le_div_right hK) 1)
  simp only [doorSievedCoeff_L_gk]
  rw [heq]
  exact le_classSup _ _ _ _ _ hlen

/-! ### `M4NonCoprime` :692 — `M4CoprimeBlockMeanSq_gk` -/
/-- **THE COPRIME FAMILY AT THE LEVER** — `M4CoprimeBlockMeanSq_L` (:339). -/
def M4CoprimeBlockMeanSq_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H → ∀ r, r < q → Nat.Coprime q r →
      ∀ A B : ℕ, 0 < A → B + L ≤ 2 * A + 4 →
        ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff_L_gk K M) L n q r) ^ 2
          ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

/-! ### `M4NonCoprime` :723 — `m4_nonCoprime_classMeanSq_gk` -/
/-- **⟦R2⟧ AT THE LEVER** — `m4_nonCoprime_classMeanSq_L` (:384). -/
theorem m4_nonCoprime_classMeanSq_L_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hM : 1 ≤ M) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ))
    (hcp : M4CoprimeBlockMeanSq_L_gk K R M Bcl) :
    M4ClassBlockMeanSq_L_gk K R M k Bcl := by
  intro H hlo hhi q hq hqQ i _ r hrq
  -- ⟦the block, and the ladder's two facts⟧
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
  have hfit : doorLadder R.x H i + H ≤ 2 * doorLadder R.x H (i + 1) := doorLadder_fit R.x H i
  have hApos : 0 < doorLadder R.x H (i + 1) := by omega
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  by_cases hcase : Nat.gcd r q = 1
  · -- ⟦d₀ = 1⟧ the class is already coprime: the datum, read at the door block
    have hcopqr : Nat.Coprime q r := by
      rw [Nat.Coprime, Nat.gcd_comm]; exact hcase
    exact hcp H hlo hhi H le_rfl q hq hqQ r hrq hcopqr
      (doorLadder R.x H (i + 1)) (doorLadder R.x H i) hApos (by omega)
  · -- ⟦d₀ > 1⟧ ONE dilation, then the `d₀`-to-one re-index of the block
    have hd2 : 2 ≤ Nat.gcd r q := by omega
    -- ⟦the modulus gates⟧
    have hdq : Nat.gcd r q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)
    have h2q : 2 * q ≤ H := by
      have hR : ((2 * q : ℕ) : ℝ) ≤ (H : ℝ) := by
        push_cast
        have := harc H hlo hhi
        linarith
      exact_mod_cast hR
    have hdA : Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hdA2 : 2 * Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hA2 : 2 ≤ doorLadder R.x H (i + 1) / Nat.gcd r q :=
      (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hA'pos : 0 < doorLadder R.x H (i + 1) / Nat.gcd r q - 1 := by omega
    -- ⟦the reduced pair⟧
    have hq₀ : 0 < q / Nat.gcd r q :=
      Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)) hd
    have hq₀Q : ((q / Nat.gcd r q : ℕ) : ℝ) ≤ arcDen 12 H := by
      refine le_trans ?_ hqQ
      exact_mod_cast Nat.div_le_self q (Nat.gcd r q)
    have hr₀q₀ : r / Nat.gcd r q < q / Nat.gcd r q := by
      rcases Nat.lt_or_ge (r / Nat.gcd r q) (q / Nat.gcd r q) with hlt | hcon
      · exact hlt
      refine absurd hrq (not_lt.mpr ?_)
      have hqd : Nat.gcd r q * (q / Nat.gcd r q) = q :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right r q)
      have h1 : Nat.gcd r q * (q / Nat.gcd r q)
          ≤ Nat.gcd r q * (r / Nat.gcd r q) := Nat.mul_le_mul le_rfl hcon
      have h2 : Nat.gcd r q * (r / Nat.gcd r q) ≤ r := by
        rw [Nat.mul_comm]; exact Nat.div_mul_le_self r (Nat.gcd r q)
      rw [← hqd]
      exact h1.trans h2
    have hcop₀ : Nat.Coprime (q / Nat.gcd r q) (r / Nat.gcd r q) :=
      (m4_class_dilate_coprime hq r).symm
    -- ⟦the dilated window length⟧
    have hH'H : H / Nat.gcd r q + 1 ≤ H := by
      have hstep : H / Nat.gcd r q ≤ H / 2 := Nat.div_le_div_left hd2 (by norm_num)
      omega
    -- ⟦the pointwise transport, then the fibre count, then the datum, then the ledger⟧
    have hpt : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
          ≤ (fun n' => (classSup (doorSievedCoeff_L_gk K M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2) (n / Nat.gcd r q) := by
      intro n _
      have hle := classSup_le_dilate_L_gk K (M := M) (H := H) (q := q) (r := r) (n := n)
        (W := arcDen 12 H) hM hq hqQ (hgate H hlo hhi)
      have h0 := classSup_nonneg (doorSievedCoeff_L_gk K M) H n q r
      simp only
      nlinarith
    have hmaps : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        n / Nat.gcd r q ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
          (doorLadder R.x H i / Nat.gcd r q) := fun n hn => div_mem_reindexed hd hdA hn
    have hdatum := hcp H hlo hhi (H / Nat.gcd r q + 1) hH'H (q / Nat.gcd r q) hq₀ hq₀Q
      (r / Nat.gcd r q) hr₀q₀ hcop₀ (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
      (doorLadder R.x H i / Nat.gcd r q) hA'pos (dilBlock_reindex_fit hd hdA hfit)
    have hd0R : (0 : ℝ) ≤ (Nat.gcd r q : ℝ) := Nat.cast_nonneg _
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
        ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L_gk K M) (H / Nat.gcd r q + 1) (n / Nat.gcd r q)
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 := Finset.sum_le_sum hpt
      _ ≤ (Nat.gcd r q : ℝ)
            * ∑ n' ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
                (doorLadder R.x H i / Nat.gcd r q),
              (classSup (doorSievedCoeff_L_gk K M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 :=
          sum_Ioc_comp_div_le
            (f := fun n' => (classSup (doorSievedCoeff_L_gk K M) (H / Nat.gcd r q + 1) n'
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2)
            (fun _ => sq_nonneg _) (d := Nat.gcd r q) hd hmaps
      _ ≤ (Nat.gcd r q : ℝ)
            * (Bcl H * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) ^ 2
                * ((doorLadder R.x H (i + 1) / Nat.gcd r q - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hdatum hd0R
      _ ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) :=
          d0_ledger hd hH'H (hBcl0 H)

/-! ### `M4NonCoprime` :822 — `M4CoprimeBlockMeanSqN_gk` -/
/-- **THE NARROWED COPRIME FAMILY AT THE LEVER** — `M4CoprimeBlockMeanSqN_L` (:510). -/
def M4CoprimeBlockMeanSqN_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → (H : ℝ) ≤ arcDen 12 H * (L : ℝ) →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H → ∀ r, r < q → Nat.Coprime q r →
      ∀ A B : ℕ, 0 < A → B + L ≤ 2 * A + 4 →
        ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff_L_gk K M) L n q r) ^ 2
          ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

/-! ### `M4NonCoprime` :843 — `m4_nonCoprime_classMeanSq_N_gk` -/
/-- **⟦R2⟧, AT THE NARROWED TWIN, AT THE LEVER** — `m4_nonCoprime_classMeanSq_N_L` (:551). -/
theorem m4_nonCoprime_classMeanSq_N_L_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hM : 1 ≤ M) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ))
    (hcp : M4CoprimeBlockMeanSqN_L_gk K R M Bcl) :
    M4ClassBlockMeanSq_L_gk K R M k Bcl := by
  intro H hlo hhi q hq hqQ i _ r hrq
  -- ⟦the block, and the ladder's two facts⟧
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
  have hfit : doorLadder R.x H i + H ≤ 2 * doorLadder R.x H (i + 1) := doorLadder_fit R.x H i
  have hApos : 0 < doorLadder R.x H (i + 1) := by omega
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hH0R : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  by_cases hcase : Nat.gcd r q = 1
  · -- ⟦d₀ = 1⟧ the class is already coprime: the datum, read at the door block, `L = H`
    have hcopqr : Nat.Coprime q r := by
      rw [Nat.Coprime, Nat.gcd_comm]; exact hcase
    have hnarrow : (H : ℝ) ≤ arcDen 12 H * (H : ℝ) := by nlinarith
    exact hcp H hlo hhi H le_rfl hnarrow q hq hqQ r hrq hcopqr
      (doorLadder R.x H (i + 1)) (doorLadder R.x H i) hApos (by omega)
  · -- ⟦d₀ > 1⟧ ONE dilation, then the `d₀`-to-one re-index of the block
    have hd2 : 2 ≤ Nat.gcd r q := by omega
    -- ⟦the modulus gates⟧
    have hdq : Nat.gcd r q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)
    have h2q : 2 * q ≤ H := by
      have hR : ((2 * q : ℕ) : ℝ) ≤ (H : ℝ) := by
        push_cast
        have := harc H hlo hhi
        linarith
      exact_mod_cast hR
    have hdA : Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hdA2 : 2 * Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hA2 : 2 ≤ doorLadder R.x H (i + 1) / Nat.gcd r q :=
      (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hA'pos : 0 < doorLadder R.x H (i + 1) / Nat.gcd r q - 1 := by omega
    -- ⟦the reduced pair⟧
    have hq₀ : 0 < q / Nat.gcd r q :=
      Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)) hd
    have hq₀Q : ((q / Nat.gcd r q : ℕ) : ℝ) ≤ arcDen 12 H := by
      refine le_trans ?_ hqQ
      exact_mod_cast Nat.div_le_self q (Nat.gcd r q)
    have hr₀q₀ : r / Nat.gcd r q < q / Nat.gcd r q := by
      rcases Nat.lt_or_ge (r / Nat.gcd r q) (q / Nat.gcd r q) with hlt | hcon
      · exact hlt
      refine absurd hrq (not_lt.mpr ?_)
      have hqd : Nat.gcd r q * (q / Nat.gcd r q) = q :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right r q)
      have h1 : Nat.gcd r q * (q / Nat.gcd r q)
          ≤ Nat.gcd r q * (r / Nat.gcd r q) := Nat.mul_le_mul le_rfl hcon
      have h2 : Nat.gcd r q * (r / Nat.gcd r q) ≤ r := by
        rw [Nat.mul_comm]; exact Nat.div_mul_le_self r (Nat.gcd r q)
      rw [← hqd]
      exact h1.trans h2
    have hcop₀ : Nat.Coprime (q / Nat.gcd r q) (r / Nat.gcd r q) :=
      (m4_class_dilate_coprime hq r).symm
    -- ⟦the dilated window length⟧
    have hH'H : H / Nat.gcd r q + 1 ≤ H := by
      have hstep : H / Nat.gcd r q ≤ H / 2 := Nat.div_le_div_left hd2 (by norm_num)
      omega
    -- ⟦THE NARROWING, at the dilated length: `H ≤ d₀·L ≤ arcDen·L`⟧
    have hnarrow : (H : ℝ) ≤ arcDen 12 H * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := by
      have hexp : Nat.gcd r q * (H / Nat.gcd r q + 1)
          = Nat.gcd r q * (H / Nat.gcd r q) + Nat.gcd r q := by ring
      have hdm : Nat.gcd r q * (H / Nat.gcd r q) + H % Nat.gcd r q = H :=
        Nat.div_add_mod H (Nat.gcd r q)
      have hmod : H % Nat.gcd r q < Nat.gcd r q := Nat.mod_lt _ hd
      have hnat : H ≤ Nat.gcd r q * (H / Nat.gcd r q + 1) := by omega
      have hR : (H : ℝ) ≤ (Nat.gcd r q : ℝ) * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hdR : (Nat.gcd r q : ℝ) ≤ arcDen 12 H := by
        refine le_trans ?_ hqQ
        exact_mod_cast hdq
      have hL0 : (0 : ℝ) ≤ ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    -- ⟦the pointwise transport, then the fibre count, then the datum, then the ledger⟧
    have hpt : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
          ≤ (fun n' => (classSup (doorSievedCoeff_L_gk K M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2) (n / Nat.gcd r q) := by
      intro n _
      have hle := classSup_le_dilate_L_gk K (M := M) (H := H) (q := q) (r := r) (n := n)
        (W := arcDen 12 H) hM hq hqQ (hgate H hlo hhi)
      have h0 := classSup_nonneg (doorSievedCoeff_L_gk K M) H n q r
      simp only
      nlinarith
    have hmaps : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        n / Nat.gcd r q ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
          (doorLadder R.x H i / Nat.gcd r q) := fun n hn => div_mem_reindexed hd hdA hn
    have hdatum := hcp H hlo hhi (H / Nat.gcd r q + 1) hH'H hnarrow (q / Nat.gcd r q) hq₀ hq₀Q
      (r / Nat.gcd r q) hr₀q₀ hcop₀ (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
      (doorLadder R.x H i / Nat.gcd r q) hA'pos (dilBlock_reindex_fit hd hdA hfit)
    have hd0R : (0 : ℝ) ≤ (Nat.gcd r q : ℝ) := Nat.cast_nonneg _
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
        ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L_gk K M) (H / Nat.gcd r q + 1) (n / Nat.gcd r q)
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 := Finset.sum_le_sum hpt
      _ ≤ (Nat.gcd r q : ℝ)
            * ∑ n' ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
                (doorLadder R.x H i / Nat.gcd r q),
              (classSup (doorSievedCoeff_L_gk K M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 :=
          sum_Ioc_comp_div_le
            (f := fun n' => (classSup (doorSievedCoeff_L_gk K M) (H / Nat.gcd r q + 1) n'
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2)
            (fun _ => sq_nonneg _) (d := Nat.gcd r q) hd hmaps
      _ ≤ (Nat.gcd r q : ℝ)
            * (Bcl H * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) ^ 2
                * ((doorLadder R.x H (i + 1) / Nat.gcd r q - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hdatum hd0R
      _ ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) :=
          d0_ledger hd hH'H (hBcl0 H)

/-! ### `M4DoorRow` :229 — `norm_doorChiCoeff_le_one` -/
/-- The door's sieved, χ-twisted datum is `1`-bounded (`memSCoeff` only deletes terms). -/
theorem norm_doorChiCoeff_le_one_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M n : ℕ) :
    ‖doorChiCoeff_L χ M n‖ ≤ 1 :=
  norm_memSCoeff_le_one (norm_liouChi_le_one χ) _ _ 2 n

/-! ### `M4DoorRow` :234 — `doorRow_ha1` -/
/-- `ha1` at the door row datum. -/
theorem doorRow_ha1_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd : ℕ) (n : ℕ) :
    ‖winCutH Xd (doorChiCoeff_L χ M) n‖ ≤ 1 :=
  norm_winCutH_le (norm_doorChiCoeff_le_one_L χ M) n

/-! ### `M4DoorRow` :239 — `doorRow_hsupp0` -/
/-- `hsupp0` at the door row datum. -/
theorem doorRow_hsupp0_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd : ℕ) (n : ℕ)
    (h : (n : ℝ) ≤ ((Xd : ℕ) : ℝ)) :
    winCutH Xd (doorChiCoeff_L χ M) n = 0 :=
  winCutH_supp0 _ h

/-! ### `M4DoorRow` :245 — `doorRow_hasupp` -/
/-- `hasupp` at the door row datum. -/
theorem doorRow_hasupp_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd : ℕ) (n : ℕ)
    (h : winCutH Xd (doorChiCoeff_L χ M) n ≠ 0) :
    Xd ≤ n ∧ n ≤ 2 * Xd :=
  winCutH_asupp h

/-! ### `M4DoorRow` :259 — `doorCofactor0_door_eq` -/
/-- The supplier's datum at the shift `1` IS the door's sieved χ-twisted datum. -/
theorem doorCofactor0_door_eq_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) :
    doorCofactor0 χ (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 1
      = doorChiCoeff_L χ M :=
  doorCofactor0_at_one χ _ _ 2

/-! ### `M4DoorRow` :265 — `cofactorSocket_doorChiCoeff` -/
/-- **THE SOCKET, AT THE CAPSTONE'S `b`-SLOT** — `m4_supplier_complete`'s conclusion at
`Ps := 1`, re-read at the door datum. -/
theorem cofactorSocket_doorChiCoeff_L {q : ℕ} (χ : DirichletCharacter ℂ q) {M : ℕ}
    {H : ℝ} {N Xd P Q : ℕ} {Tann Rrad t₁ Rbar : ℝ}
    (h : CofactorSocket H N Xd P Q Tann Rrad t₁ Rbar
      (doorCofactor0 χ (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 1)) :
    CofactorSocket H N Xd P Q Tann Rrad t₁ Rbar (doorChiCoeff_L χ M) := by
  rwa [doorCofactor0_door_eq_L] at h

/-! ### `M4DoorRow` :281 — `doorChiCoeff_seamCoefW_at_door` -/
/-- **`hcoefPin`, AT THE DOOR** — the band pair law with its gate discharged from the
capstone's own `hQXd`/`hPlow`. -/
theorem doorChiCoeff_seamCoefW_at_door_L {q : ℕ} (χ : DirichletCharacter ℂ q) {M Xd P Q : ℕ}
    {X : ℝ} (hM : 1 ≤ M) (hX : 1 < Real.log X)
    (hQlog : Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log X))
    (hPlow : P83 X theta293 ≤ (P : ℝ)) :
    SeamCoefW Xd P Q (winCut Xd (doorChiCoeff_L χ M)) (doorChiCoeff_L χ M) (liouChi χ) :=
  doorChiCoeff_seamCoefW_band_L χ M Xd P Q
    (door_band_gate_of_log (by omega : 1 ≤ 3072 * M) hX hQlog hPlow)

/-! ### `M4DoorRow` :297 — `m4_door_tail_supply` -/
/-- **THE DOOR ROW'S TAIL TRIPLE** (`m4_door_tail_supply_L`) — the coprime-tail mass, its
nonnegativity, and the capstone's `hEP2` budget line, all at
`M_tail := C·(log P/log Q)/X_d + 1/X_d²` and the door's own cut datum. -/
theorem m4_door_tail_supply_L :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (M P Q Xd N : ℕ) (X ε : ℝ),
        (Xd : ℝ) = X → (N : ℝ) = 2 * X → 0 < X → 256 ≤ Real.log X →
        2 ≤ P → P ≤ Q → 1 ≤ Xd →
        100 * Real.log Q ≤ Real.log Xd →
        ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
        P83 X theta293 ≤ (P : ℝ) →
        10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ) →
        8640 ≤ (Real.log X) ^ ε →
        Real.log (P : ℝ) / Real.log (Q : ℝ)
          ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293)) →
        2688 * C * Real.log (Real.log X) ≤ (Real.log X) ^ ε →
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖winCutH Xd (doorChiCoeff_L χ M) n‖ ^ 2 / (n : ℝ) ^ 2
            ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)
          ∧ 0 ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2
          ∧ 12 * (witEP2 X N Xd P
              + 4 / 3 * ((2 * X + 20 * (N : ℝ))
                * (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)))
            ≤ (Real.log X) ^ (-theta293 + ε) := by
  obtain ⟨C, hC0, hband⟩ := m4_tail_supply_at_band
  refine ⟨C, hC0, ?_⟩
  intro q χ M P Q Xd N X ε hXd hN hX0 hL hP2 hPQ hXd1 hgate hdom hP83 hthr habs hgrade hthr2
  exact hband P Q Xd N (winCutH Xd (doorChiCoeff_L χ M)) X ε hXd hN hX0 hL hP2 hPQ hXd1 hgate
    hdom (doorRow_ha1_L χ M Xd) (fun n hn => doorRow_hasupp_L χ M Xd n hn) hP83 hthr habs hgrade
    hthr2

/-! ### `M4DoorRow` :329 — `m4_door_tail_supply_end` -/
/-- **THE DOOR ROW'S TAIL TRIPLE, WITH THE ENDPOINT CRUMB** (`m4_door_tail_supply_end_L`) —
`m4_door_tail_supply_L` at ⟦THE ENDPOINT WALL⟧'s `EP₂` budget line (the extra
`(4/3)(2X+20N)·M_end` summand).  The threshold list is the landed one, unchanged. -/
theorem m4_door_tail_supply_end_L :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (M P Q Xd N : ℕ) (X ε : ℝ),
        (Xd : ℝ) = X → (N : ℝ) = 2 * X → 0 < X → 256 ≤ Real.log X →
        2 ≤ P → P ≤ Q → 1 ≤ Xd →
        100 * Real.log Q ≤ Real.log Xd →
        ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
        P83 X theta293 ≤ (P : ℝ) →
        10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ) →
        8640 ≤ (Real.log X) ^ ε →
        Real.log (P : ℝ) / Real.log (Q : ℝ)
          ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293)) →
        2688 * C * Real.log (Real.log X) ≤ (Real.log X) ^ ε →
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖winCutH Xd (doorChiCoeff_L χ M) n‖ ^ 2 / (n : ℝ) ^ 2
            ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)
          ∧ 0 ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2
          ∧ 12 * (witEP2 X N Xd P
              + 4 / 3 * ((2 * X + 20 * (N : ℝ))
                * (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2))
              + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * endMass Xd))
            ≤ (Real.log X) ^ (-theta293 + ε) := by
  obtain ⟨C, hC0, hband⟩ := m4_tail_supply_at_band_end
  refine ⟨C, hC0, ?_⟩
  intro q χ M P Q Xd N X ε hXd hN hX0 hL hP2 hPQ hXd1 hgate hdom hP83 hthr habs hgrade hthr2
  exact hband P Q Xd N (winCutH Xd (doorChiCoeff_L χ M)) X ε hXd hN hX0 hL hP2 hPQ hXd1 hgate
    hdom (doorRow_ha1_L χ M Xd) (fun n hn => doorRow_hasupp_L χ M Xd n hn) hP83 hthr habs hgrade
    hthr2

/-! ### `M4DoorRow` :403 — `door_block_one_wide` -/
/-- **THE DOOR'S LEVEL-1 K-BLOCK IS WIDE** (`door_block_one_wide_L`).  `𝒫_1 = 2^{AdoorL M}` and
`𝒬K_1 = 2^{M·AdoorL M}`, so already at `M ≥ 2` the block contains a factor `4` — and
`AdoorL M ≥ 2^18`, so the true spread is `2^{(M−1)·2^18}`.  Against §6's ratio lock this is the
wall. -/
theorem door_block_one_wide_L {M : ℕ} (hM : 2 ≤ M) :
    4 * calP (AdoorL M) (3072 * M) 1 ≤ calQK (AdoorL M) (3072 * M) M 1 := by
  have hE : calE (AdoorL M) (3072 * M) 1 = AdoorL M := calE_one _ _
  have hA2 : 2 ≤ AdoorL M := le_trans (by norm_num) (AdoorL_ge (by omega : 1 ≤ M))
  have hstep : AdoorL M + 2 ≤ 1 ^ 2 * M * AdoorL M := by
    have h2 : 2 * AdoorL M ≤ M * AdoorL M := Nat.mul_le_mul_right _ hM
    simp only [one_pow, one_mul]
    omega
  have hL : 4 * calP (AdoorL M) (3072 * M) 1 = 2 ^ (AdoorL M + 2) := by
    simp only [calP, hE, pow_add]
    ring
  have hR : calQK (AdoorL M) (3072 * M) M 1 = 2 ^ (1 ^ 2 * M * AdoorL M) := by
    simp only [calQK, hE]
  rw [hL, hR]
  exact Nat.pow_le_pow_right (by norm_num) hstep

/-! ### `M4DoorRow` :440 — `door_length_gate_fails_of_small` -/
/-- **THE SMALL-`j` INSTANCES ARE UNREACHABLE** (`door_length_gate_fails_of_small_L`).  For
`1 ≤ M` the capstone's window gate is violated at every dyadic length `2^j` with
`j < 2^18 ≤ M·AdoorL M` — in particular at `j = 0`, which
`M4Maximal.M4ChiDyadicRowMeanSq_L` demands at every `H`.

⟦THE 2026-07-29 ANCHOR RE-PIN⟧: the hypothesis is deliberately left at the PRE-RE-PIN
threshold `2^18`.  With `AdoorL M ≥ 2^36` the statement is now true-and-weaker (the honest
reach is `j < 2^36`), so every downstream instance survives verbatim; nothing on the road
asks for the wider window. -/
theorem door_length_gate_fails_of_small_L {M j : ℕ} (hM : 1 ≤ M) (hj : j < 2 ^ 18) :
    ¬ ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
  intro h
  have hle := doorL_length_gate h
  have hA : 2 ^ 18 ≤ AdoorL M := AdoorL_ge_old hM
  have : AdoorL M ≤ M * AdoorL M := Nat.le_mul_of_pos_left _ hM
  omega

/-! ### `M4DoorRow` :519 — `doorRow_ha1_gk` -/
/-- `ha1` at the levered door row datum. -/
theorem doorRow_ha1_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd : ℕ) (n : ℕ) :
    ‖winCutH Xd (doorChiCoeff_L_gk K χ M) n‖ ≤ 1 :=
  norm_winCutH_le (fun m => norm_memSCoeff_le_one (norm_liouChi_le_one χ) _ _ 2 m) n

/-! ### `M4DoorRow` :524 — `doorRow_hsupp0_gk` -/
/-- `hsupp0` at the levered door row datum. -/
theorem doorRow_hsupp0_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd : ℕ) (n : ℕ)
    (h : (n : ℝ) ≤ ((Xd : ℕ) : ℝ)) :
    winCutH Xd (doorChiCoeff_L_gk K χ M) n = 0 :=
  winCutH_supp0 _ h

/-! ### `M4DoorRow` :530 — `doorRow_hasupp_gk` -/
/-- `hasupp` at the levered door row datum. -/
theorem doorRow_hasupp_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd : ℕ) (n : ℕ)
    (h : winCutH Xd (doorChiCoeff_L_gk K χ M) n ≠ 0) :
    Xd ≤ n ∧ n ≤ 2 * Xd :=
  winCutH_asupp h

/-! ### `M4DoorRow` :536 — `doorCofactor0_door_eq_gk` -/
/-- The supplier's datum at the shift `1` IS the levered door datum
(`doorCofactor0_door_eq_L_gk`). -/
theorem doorCofactor0_door_eq_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) :
    doorCofactor0 χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 1
      = doorChiCoeff_L_gk K χ M :=
  doorCofactor0_at_one χ _ _ 2

/-! ### `M4DoorRow` :543 — `cofactorSocket_doorChiCoeff_gk` -/
/-- **THE SOCKET, AT THE CAPSTONE'S `b`-SLOT, AT THE G-LEVER**
(`cofactorSocket_doorChiCoeff_L_gk`). -/
theorem cofactorSocket_doorChiCoeff_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) {M : ℕ}
    {H : ℝ} {N Xd P Q : ℕ} {Tann Rrad t₁ Rbar : ℝ}
    (h : CofactorSocket H N Xd P Q Tann Rrad t₁ Rbar
      (doorCofactor0 χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 1)) :
    CofactorSocket H N Xd P Q Tann Rrad t₁ Rbar (doorChiCoeff_L_gk K χ M) := by
  rwa [doorCofactor0_door_eq_L_gk] at h

/-! ### `M4DoorRow` :552 — `doorChiCoeff_seamCoefW_at_door_gk` -/
/-- **`hcoefPin`, AT THE DOOR, AT THE G-LEVER** (`doorChiCoeff_seamCoefW_at_door_L_gk`). -/
theorem doorChiCoeff_seamCoefW_at_door_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {M Xd P Q : ℕ} {X : ℝ} (hM : 1 ≤ M) (hX : 1 < Real.log X)
    (hQlog : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log X))
    (hPlow : P83 X theta293 ≤ (P : ℝ)) :
    SeamCoefW Xd P Q (winCut Xd (doorChiCoeff_L_gk K χ M)) (doorChiCoeff_L_gk K χ M)
      (liouChi χ) :=
  doorChiCoeff_seamCoefW_band_L_gk K χ M Xd P Q
    (door_band_gate_of_log (one_le_s13GK K hM) hX hQlog hPlow)

/-! ### `M4DoorRow` :562 — `m4_door_tail_supply_gk` -/
/-- **THE DOOR ROW'S TAIL TRIPLE, AT THE G-LEVER** (`m4_door_tail_supply_L_gk`). -/
theorem m4_door_tail_supply_L_gk (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (M P Q Xd N : ℕ) (X ε : ℝ),
        (Xd : ℝ) = X → (N : ℝ) = 2 * X → 0 < X → 256 ≤ Real.log X →
        2 ≤ P → P ≤ Q → 1 ≤ Xd →
        100 * Real.log Q ≤ Real.log Xd →
        ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
        P83 X theta293 ≤ (P : ℝ) →
        10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ) →
        8640 ≤ (Real.log X) ^ ε →
        Real.log (P : ℝ) / Real.log (Q : ℝ)
          ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293)) →
        2688 * C * Real.log (Real.log X) ≤ (Real.log X) ^ ε →
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖winCutH Xd (doorChiCoeff_L_gk K χ M) n‖ ^ 2 / (n : ℝ) ^ 2
            ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)
          ∧ 0 ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2
          ∧ 12 * (witEP2 X N Xd P
              + 4 / 3 * ((2 * X + 20 * (N : ℝ))
                * (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)))
            ≤ (Real.log X) ^ (-theta293 + ε) := by
  obtain ⟨C, hC0, hband⟩ := m4_tail_supply_at_band
  refine ⟨C, hC0, ?_⟩
  intro q χ M P Q Xd N X ε hXd hN hX0 hL hP2 hPQ hXd1 hgate hdom hP83 hthr habs hgrade hthr2
  exact hband P Q Xd N (winCutH Xd (doorChiCoeff_L_gk K χ M)) X ε hXd hN hX0 hL hP2 hPQ hXd1
    hgate hdom (doorRow_ha1_L_gk K χ M Xd) (fun n hn => doorRow_hasupp_L_gk K χ M Xd n hn) hP83
    hthr habs hgrade hthr2

/-! ### `M4DoorRow` :592 — `m4_door_tail_supply_end_gk` -/
/-- **THE DOOR ROW'S TAIL TRIPLE, WITH THE ENDPOINT CRUMB, AT THE G-LEVER**
(`m4_door_tail_supply_end_L_gk`). -/
theorem m4_door_tail_supply_end_L_gk (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (M P Q Xd N : ℕ) (X ε : ℝ),
        (Xd : ℝ) = X → (N : ℝ) = 2 * X → 0 < X → 256 ≤ Real.log X →
        2 ≤ P → P ≤ Q → 1 ≤ Xd →
        100 * Real.log Q ≤ Real.log Xd →
        ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
        P83 X theta293 ≤ (P : ℝ) →
        10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ) →
        8640 ≤ (Real.log X) ^ ε →
        Real.log (P : ℝ) / Real.log (Q : ℝ)
          ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293)) →
        2688 * C * Real.log (Real.log X) ≤ (Real.log X) ^ ε →
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖winCutH Xd (doorChiCoeff_L_gk K χ M) n‖ ^ 2 / (n : ℝ) ^ 2
            ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)
          ∧ 0 ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2
          ∧ 12 * (witEP2 X N Xd P
              + 4 / 3 * ((2 * X + 20 * (N : ℝ))
                * (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2))
              + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * endMass Xd))
            ≤ (Real.log X) ^ (-theta293 + ε) := by
  obtain ⟨C, hC0, hband⟩ := m4_tail_supply_at_band_end
  refine ⟨C, hC0, ?_⟩
  intro q χ M P Q Xd N X ε hXd hN hX0 hL hP2 hPQ hXd1 hgate hdom hP83 hthr habs hgrade hthr2
  exact hband P Q Xd N (winCutH Xd (doorChiCoeff_L_gk K χ M)) X ε hXd hN hX0 hL hP2 hPQ hXd1
    hgate hdom (doorRow_ha1_L_gk K χ M Xd) (fun n hn => doorRow_hasupp_L_gk K χ M Xd n hn) hP83
    hthr habs hgrade hthr2

/-! ### `M4DoorRow` :626 — `door_block_one_wide_gk` -/
/-- **THE DOOR'S LEVEL-1 K-BLOCK IS WIDE, AT THE G-LEVER** (`door_block_one_wide_L_gk`) —
LEVEL 1, hence a transport: both sides are the landed symbols. -/
theorem door_block_one_wide_L_gk (K : ℕ) {M : ℕ} (hM : 2 ≤ M) :
    4 * calP (AdoorL M) (s13GK K M) 1 ≤ calQK (AdoorL M) (s13GK K M) M 1 := by
  rw [calP_gk_one_eq, calQK_gk_one_eq]
  exact door_block_one_wide_L hM

/-! ### `M4DoorRow` :633 — `door_length_gate_gk` -/
/-- **THE LENGTH GATE, SOLVED, AT THE G-LEVER** (`door_length_gate_L_gk`) — LEVEL 1, hence a
transport; the floor is the landed `M·AdoorL M`, unmoved. -/
theorem door_length_gate_L_gk (K : ℕ) {M j : ℕ}
    (h : ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) :
    M * AdoorL M ≤ j := by
  rw [calQK_gk_one_eq] at h
  exact doorL_length_gate h

/-! ### `M4DoorRow` :641 — `door_length_gate_fails_of_small_gk` -/
/-- **THE SMALL-`j` INSTANCES ARE UNREACHABLE, AT THE G-LEVER**
(`door_length_gate_fails_of_small_L_gk`) — LEVEL 1, hence a transport. -/
theorem door_length_gate_fails_of_small_L_gk (K : ℕ) {M j : ℕ} (hM : 1 ≤ M) (hj : j < 2 ^ 18) :
    ¬ ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
  rw [calQK_gk_one_eq]
  exact door_length_gate_fails_of_small_L hM hj

/-! ### `M4DoorRow` :648 — `door_length_gate_iff_gk` -/
/-- **THE LENGTH GATE, BOTH WAYS, AT THE G-LEVER** (`door_length_gate_iff_L_gk`) — LEVEL 1,
hence a transport.  `doorRowFloorL M` is `G`-FREE and is NOT twinned. -/
theorem door_length_gate_iff_L_gk (K : ℕ) {M j : ℕ} :
    ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
      ↔ doorRowFloorL M ≤ j := by
  rw [calQK_gk_one_eq]
  exact doorL_length_gate_iff

/-! ### `M4Puncture` :166 — `door_block_separation` -/
/-- **THE DOOR'S BLOCK SEPARATION** (`door_block_separation_L`).  At the door's calibration
`G = 3072M` the gate `M < 4G` reads `M < 12288M`, free at `1 ≤ M`. -/
theorem door_block_separation_L {M : ℕ} (hM : 1 ≤ M) :
    calQK (AdoorL M) (3072 * M) M 1 < calP (AdoorL M) (3072 * M) 2 :=
  calQK_one_lt_calP_two (one_le_AdoorL hM) (by omega)

/-! ### `M4Puncture` :172 — `door_block_sep_at` -/
/-- **THE DOOR'S TWO BLOCKS ARE SEPARATED, POINTWISE** (`door_block_sep_at_L`).  The `hsep`
binder of §2 discharged at the door's own two-level ladder, at every prime of block `j`. -/
theorem door_block_sep_at_L {M j p : ℕ} (hM : 1 ≤ M) (hj : j ∈ Finset.Icc 1 2)
    (hlo : calP (AdoorL M) (3072 * M) j ≤ p) (hhi : p ≤ calQK (AdoorL M) (3072 * M) M j) :
    ∀ i ∈ Finset.Icc 1 2, i ≠ j →
      ¬ (calP (AdoorL M) (3072 * M) i ≤ p ∧ p ≤ calQK (AdoorL M) (3072 * M) M i) := by
  have hsplit := door_block_separation_L hM
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  intro i hi hij
  rw [Finset.mem_Icc] at hi
  obtain ⟨hi1, hi2⟩ := hi
  rintro ⟨hilo, hihi⟩
  -- `j` and `i` are the two distinct levels of `{1, 2}`
  interval_cases j <;> interval_cases i <;> omega

/-! ### `M4Puncture` :242 — `doorChiCoeff_seamCoefW_punct_H` -/
/-- **`hcoefBand` AT THE DOOR, HALF-OPEN** (`doorChiCoeff_seamCoefW_punct_H_L`) — the whole
level family at once, in exactly the shape `M4MeanSq.m4_meansq_per_chi_gen_L`'s band binder
reads it: `∀ j ∈ [1,2], SeamCoefW X_d 𝒫_j 𝒬K_j a (bfam j) λχ̄`, with

  `bfam j := 1_{𝒮∖j}·λχ̄`   (`memSPunctCoeff … 2 j (liouChi χ)`).

The separation is `door_block_sep_at_L`, the endpoint `M4Band` §4's `hend`. -/
theorem doorChiCoeff_seamCoefW_punct_H_L {q : ℕ} (χ : DirichletCharacter ℂ q) {M Xd : ℕ}
    {a : ℕ → ℂ} (hM : 1 ≤ M)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_L χ M n)
    (ha0 : a Xd = 0) (hend : doorChiCoeff_L χ M Xd = 0) :
    ∀ j ∈ Finset.Icc 1 2,
      SeamCoefW Xd (calP (AdoorL M) (3072 * M) j) (calQK (AdoorL M) (3072 * M) M j) a
        (memSPunctCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 j
          (liouChi χ)) (liouChi χ) := by
  intro j hj
  exact memSCoeff_seamCoefW_punct_H χ (calP (AdoorL M) (3072 * M))
    (calQK (AdoorL M) (3072 * M) M) 2 j Xd a hj
    (fun p hp hlo hhi => door_block_sep_at_L hM hj hlo hhi) haH ha0 hend

/-! ### `M4Puncture` :303 — `doorChiCoeff_seamCoefWS_punct_H` -/
/-- **`hcoefBand` AT THE DOOR, STRICT** (`doorChiCoeff_seamCoefWS_punct_H_L`) — the whole level
family at once, in the shape the capstone's band binder reads it, with no endpoint
obligation. -/
theorem doorChiCoeff_seamCoefWS_punct_H_L {q : ℕ} (χ : DirichletCharacter ℂ q) {M Xd : ℕ}
    {a : ℕ → ℂ} (hM : 1 ≤ M)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_L χ M n) :
    ∀ j ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (AdoorL M) (3072 * M) j) (calQK (AdoorL M) (3072 * M) M j) a
        (memSPunctCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 j
          (liouChi χ)) (liouChi χ) := by
  intro j hj
  exact memSCoeff_seamCoefWS_punct_H χ (calP (AdoorL M) (3072 * M))
    (calQK (AdoorL M) (3072 * M) M) 2 j Xd a hj
    (fun p hp hlo hhi => door_block_sep_at_L hM hj hlo hhi) haH

/-! ### `M4Puncture` :318 — `norm_doorPunctCoeff_le_one` -/
/-- The door's punctured co-factor family is `1`-bounded — the capstone's `hbf1` slot. -/
theorem norm_doorPunctCoeff_le_one_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M j n : ℕ) :
    ‖memSPunctCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 j
      (liouChi χ) n‖ ≤ 1 :=
  norm_memSPunctCoeff_le_one (norm_liouChi_le_one χ) _ _ 2 j n

/-! ### `M4Puncture` :331 — `door_block_separation_gk` -/
/-- **THE DOOR'S BLOCK SEPARATION, AT THE G-LEVER** (`door_block_separation_L_gk`).  `M < 4G`
at `G = s13GK K M` follows from `M < 4·(3072M)` and `3072M ≤ s13GK K M`. -/
theorem door_block_separation_L_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    calQK (AdoorL M) (s13GK K M) M 1 < calP (AdoorL M) (s13GK K M) 2 :=
  calQK_one_lt_calP_two (one_le_AdoorL hM)
    (lt_of_lt_of_le (show M < 4 * (3072 * M) by omega)
      (Nat.mul_le_mul_left 4 (le_s13GK K M)))

/-! ### `M4Puncture` :339 — `door_block_sep_at_gk` -/
/-- **THE DOOR'S TWO BLOCKS ARE SEPARATED, POINTWISE, AT THE G-LEVER**
(`door_block_sep_at_L_gk`). -/
theorem door_block_sep_at_L_gk (K : ℕ) {M j p : ℕ} (hM : 1 ≤ M) (hj : j ∈ Finset.Icc 1 2)
    (hlo : calP (AdoorL M) (s13GK K M) j ≤ p)
    (hhi : p ≤ calQK (AdoorL M) (s13GK K M) M j) :
    ∀ i ∈ Finset.Icc 1 2, i ≠ j →
      ¬ (calP (AdoorL M) (s13GK K M) i ≤ p ∧ p ≤ calQK (AdoorL M) (s13GK K M) M i) := by
  have hsplit := door_block_separation_L_gk K hM
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  intro i hi hij
  rw [Finset.mem_Icc] at hi
  obtain ⟨hi1, hi2⟩ := hi
  rintro ⟨hilo, hihi⟩
  -- `j` and `i` are the two distinct levels of `{1, 2}`
  interval_cases j <;> interval_cases i <;> omega

/-! ### `M4Puncture` :356 — `doorChiCoeff_seamCoefW_punct_H_gk` -/
/-- **`hcoefBand` AT THE DOOR, HALF-OPEN, AT THE G-LEVER**
(`doorChiCoeff_seamCoefW_punct_H_L_gk`). -/
theorem doorChiCoeff_seamCoefW_punct_H_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {M Xd : ℕ} {a : ℕ → ℂ} (hM : 1 ≤ M)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_L_gk K χ M n)
    (ha0 : a Xd = 0) (hend : doorChiCoeff_L_gk K χ M Xd = 0) :
    ∀ j ∈ Finset.Icc 1 2,
      SeamCoefW Xd (calP (AdoorL M) (s13GK K M) j) (calQK (AdoorL M) (s13GK K M) M j) a
        (memSPunctCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 j
          (liouChi χ)) (liouChi χ) := by
  intro j hj
  exact memSCoeff_seamCoefW_punct_H χ (calP (AdoorL M) (s13GK K M))
    (calQK (AdoorL M) (s13GK K M) M) 2 j Xd a hj
    (fun p hp hlo hhi => door_block_sep_at_L_gk K hM hj hlo hhi) haH ha0 hend

/-! ### `M4Puncture` :371 — `doorChiCoeff_seamCoefWS_punct_H_gk` -/
/-- **`hcoefBand` AT THE DOOR, STRICT, AT THE G-LEVER**
(`doorChiCoeff_seamCoefWS_punct_H_L_gk`). -/
theorem doorChiCoeff_seamCoefWS_punct_H_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {M Xd : ℕ} {a : ℕ → ℂ} (hM : 1 ≤ M)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_L_gk K χ M n) :
    ∀ j ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) j) (calQK (AdoorL M) (s13GK K M) M j) a
        (memSPunctCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 j
          (liouChi χ)) (liouChi χ) := by
  intro j hj
  exact memSCoeff_seamCoefWS_punct_H χ (calP (AdoorL M) (s13GK K M))
    (calQK (AdoorL M) (s13GK K M) M) 2 j Xd a hj
    (fun p hp hlo hhi => door_block_sep_at_L_gk K hM hj hlo hhi) haH

/-! ### `M4Puncture` :385 — `norm_doorPunctCoeff_le_one_gk` -/
/-- The door's punctured co-factor family at the G-lever is `1`-bounded
(`norm_doorPunctCoeff_le_one_L_gk`). -/
theorem norm_doorPunctCoeff_le_one_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M j n : ℕ) :
    ‖memSPunctCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 j
      (liouChi χ) n‖ ≤ 1 :=
  norm_memSPunctCoeff_le_one (norm_liouChi_le_one χ) _ _ 2 j n

end Salt.MR

end
