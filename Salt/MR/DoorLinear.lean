/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.DoorFrame
import Salt.MR.S11Hoist
import Salt.MR.S16Budget

/-!
# `DoorLinear` — the door's anchor RE-CUT LINEAR in `M` (`AdoorL M := 2^36·M`)

⟦W0-DOOR, the flat-tower build wave, FLAT-REF amendment 0⟧  This page is **additive**:
`DoorFrame.Adoor` and every landed consumer of it are untouched.  What is minted here is the
`_L` twin family, so the flat-threshold wave (`W1`–`W3`) has a door whose anchor grows
LINEARLY with `M` rather than logarithmically.

## Why the re-cut is mandatory

At the landed `Adoor M = 2^36·(⌊log₂ M⌋ + 1)` every `λ₊`-cap of the register is
`≤ c·Adoor M`, while the only `M`-upper the frame exposes is `log₂(M·Adoor M) ≤ 1.4427·λ₋`.
The two together give `λ₊ ≤ 1.79·10^8·λ₋` **uniformly in `λ₋`** — a cap that no exponential
width can pass.  Against the flat necessity `log λ₊ ≥ log λ₋ + (20/21)·A·log 4` this pins the
flat design constant at `A ≤ 15.2`, dead against its own floor.  With `AdoorL M = 2^36·M` the
`M`-upper becomes `log₂ M ≤ λ₋/2`-shaped and the cap reads `λ₊ ≤ 1.24·10^8·M`, i.e.
`λ₊ ≲ 400·e^{λ₋/2}` — exponential in `λ₋`, which is exactly what the flat width demands.
(FLAT-REF probe `f8`; the design law is `26 ≤ A` with `3.2·A ≤ loglog H₋`, and NO numeral for
`A` is fixed anywhere — the whole page is symbolic in the door's `M`.)

## What moves and what does not

* **Moves — the four arithmetic bridges.**  `AdoorL_cast` (the `Adoor_cast` genre),
  `calE_doorL_two`(`_gk`) (the `calE_door_two` genre), `log_calE_doorL_two`(`_gk`), and
  `log_four_M_doorL` (the `log_four_M_door` genre, re-shaped from `⌊log₂ M⌋` to `M`).
  The level-2 exponent NUMERAL is unchanged — `844424930131968` in both cuts, because the
  landed `(⌊log₂ M⌋ + 1)` and the linear `M` occupy the same slot.
* **Survives verbatim — the `Adoor_ge` genre.**  `AdoorL_ge`/`AdoorL_ge_old`/`one_le_AdoorL`
  have the LANDED conclusions (`2^36 ≤ ·`, `2^18 ≤ ·`, `1 ≤ ·`); the one difference is the
  hypothesis `1 ≤ M`, which every door consumer already carries.  So the ~97 sites reading
  only the anchor's FLOOR re-instantiate without a proof change.
* **Survives verbatim — the log bound.**  `log e₂ ≤ (2⌊log₂ M⌋ + 52)·log 2` holds at BOTH
  cuts: the landed proof pays `⌊log₂ M⌋ + 1 ≤ 2^{⌊log₂ M⌋+1}` where the linear one pays
  `M ≤ 2^{⌊log₂ M⌋+1}`, the same base-2 bound in the same slot.

## The frame gate, and the new `K`-ceiling

`A_gate_logK` (`SeamCalibrationK`'s `CalFrameK`) is
`16(log 4M + log e₂) ≤ (1/24)(A·log 2 − 1)`.  At the linear anchor the right side is
`(1/24)(68719476736·M·log 2 − 1)` and the left is `≤ (48⌊log₂ M⌋ + 880 + 16K)·log 2`, so with
`⌊log₂ M⌋ ≤ M` the lever's ceiling becomes

  `K ≤ 2^36·M/384 ≈ 1.79·10^8·M`,

the landed `1.7·10^8` **times `M`** — the pin `hK : K ≤ 170000000 * M` used below sits at
94.9 % of that ceiling and still clears the gate by a factor `> 1.05` in the leading term.
This is the whole point of the re-cut at the register: the `K`-budget now BUYS LINEARLY.

## The cap chain

`S13CapGrid.s13CapGrid_Lambda_sharp`/`_lo` are anchor-FREE (they read the socket's own `A + s`,
not the door's `Adoor M`) and get no twin.  The door-reading link is `S16BaseScaleCap_gk`, and
its `_L` twin is not merely stated but **implied by the landed one**
(`s16_baseScaleCapL_of_baseScaleCap`): the re-cut only RAISES the anchor
(`Adoor_le_AdoorL`), hence raises `log 𝒫₂`, hence WEAKENS the cap.  Every existing supplier of
the landed cap therefore supplies the linear cap for free.  The deep chains below the cap
re-instantiate at `AdoorL`; they do not re-derive.

Source pins: `docs/blueprints/flags.md` ⟦FLAT-REF⟧ (amendment 0, §2's `F8`);
`docs/exploration/s9-design-0726.md` (D-FAMILY, ⟦AMENDMENT A⟧) for the landed cut.
-/

open Salt.Entropy.Chowla

namespace Salt.MR

/-! ## §0 — the linear anchor -/

/-- **The door's anchor exponent, RE-CUT LINEAR** `A_L(M) := 2^36·M`.  The `2^36` is the
landed size (`DoorFrame.Adoor`'s docstring: the smallest anchor clearing ⟦SANDWICH-REF⟧'s
gate-12/length-floor pair, with ~64× beyond); the `M` in place of `⌊log₂ M⌋ + 1` is
FLAT-REF amendment 0.  `M` is still never evaluated — at the door it is `⌈8C/δ₀⌉`-shaped. -/
def AdoorL (M : ℕ) : ℕ := 2 ^ 36 * M

lemma AdoorL_ge {M : ℕ} (hM : 1 ≤ M) : 2 ^ 36 ≤ AdoorL M :=
  Nat.le_mul_of_pos_right _ (by omega)

/-- **The anchor at the PRE-RE-PIN bound** `2^18 ≤ A_L(M)`, the `Adoor_ge_old` twin: every
consumer written against the old anchor survives verbatim at the linear cut too. -/
lemma AdoorL_ge_old {M : ℕ} (hM : 1 ≤ M) : 2 ^ 18 ≤ AdoorL M :=
  le_trans (by norm_num) (AdoorL_ge hM)

lemma one_le_AdoorL {M : ℕ} (hM : 1 ≤ M) : 1 ≤ AdoorL M :=
  le_trans (by norm_num) (AdoorL_ge hM)

/-- **THE RE-CUT IS A WIDENING** `Adoor M ≤ AdoorL M` (`⌊log₂ M⌋ + 1 ≤ M`, `Nat.log_lt_self`).
Every monotone-in-`A` consumer of the landed door transports to the linear door for free —
this is what makes the cap twin below a one-line implication rather than a re-derivation. -/
lemma Adoor_le_AdoorL {M : ℕ} (hM : 1 ≤ M) : Adoor M ≤ AdoorL M := by
  have h : Nat.log 2 M < M := Nat.log_lt_self 2 (by omega)
  simp only [Adoor, AdoorL]
  exact Nat.mul_le_mul le_rfl (by omega)

/-- The linear anchor in ℝ, with `2^36` evaluated — the form `A_gate_logK`'s right side needs
(the `Adoor_cast` twin, at the consumer shape). -/
lemma AdoorL_cast (M : ℕ) : ((AdoorL M : ℕ) : ℝ) = 68719476736 * (M : ℝ) := by
  simp only [AdoorL]
  push_cast
  norm_num

/-! ## §1 — the level-2 exponent identity -/

/-- **The linear door's `e₂`, as a ℕ identity**: `e₂ = A_L·G·(2!)² = 2^36 M·3072M·4
= 3·2^{48}·M²`.  The NUMERAL is the landed `calE_door_two`'s, unchanged — the re-cut swaps
`⌊log₂ M⌋ + 1` for `M` in the same slot.  No `2^{2^36}` is ever formed. -/
lemma calE_doorL_two (M : ℕ) :
    calE (AdoorL M) (3072 * M) 2 = 844424930131968 * (M * M) := by
  simp only [calE, AdoorL, Nat.factorial]
  ring

/-- **The linear door's `e₂` at the G-lever**: the landed numeral times `2^K`
(`GLever.calE_gk_two`). -/
lemma calE_doorL_two_gk (K M : ℕ) :
    calE (AdoorL M) (s13GK K M) 2 = 2 ^ K * (844424930131968 * (M * M)) := by
  rw [calE_gk_two, calE_doorL_two]

/-! ## §2 — the `Nat.log`→`Real.log` bridges -/

/-- `x ≤ 2^k → log x ≤ k log 2` (the landed `DoorFrame`'s private helper, re-derived: the
corpus copy is not exported).  Every size fact below is routed through a base-2 exponent. -/
private lemma logL_le_pow_two {x : ℝ} {k : ℕ} (hx : 0 < x) (h : x ≤ (2 : ℝ) ^ k) :
    Real.log x ≤ (k : ℝ) * Real.log 2 := by
  calc Real.log x ≤ Real.log ((2 : ℝ) ^ k) := Real.log_le_log hx h
    _ = (k : ℝ) * Real.log 2 := by rw [Real.log_pow]

/-- **`A_gate_logK`'s second logarithm at the linear door**: `log e₂ ≤ (2L + 52) log 2`,
`L := ⌊log₂ M⌋` — the LANDED bound, unchanged.  The landed proof paid `L + 1 ≤ 2^{L+1}`
(`Nat.lt_two_pow_self`); this one pays `M ≤ 2^{L+1}` (`Nat.lt_pow_succ_log_self`) in the same
slot, so the exponent ladder `3·2^{48}M² ≤ 2^{50}·2^{L+1}·2^{L+1}` closes identically. -/
lemma log_calE_doorL_two {M : ℕ} (hM : 1 ≤ M) :
    Real.log ((calE (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)
      ≤ (2 * (Nat.log 2 M : ℝ) + 52) * Real.log 2 := by
  have hMle : M ≤ 2 ^ (Nat.log 2 M + 1) := (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) M).le
  have hN : calE (AdoorL M) (3072 * M) 2 ≤ 2 ^ (2 * Nat.log 2 M + 52) := by
    rw [calE_doorL_two]
    calc 844424930131968 * (M * M)
        ≤ 2 ^ 50 * (2 ^ (Nat.log 2 M + 1) * 2 ^ (Nat.log 2 M + 1)) :=
          Nat.mul_le_mul (by norm_num) (Nat.mul_le_mul hMle hMle)
      _ = 2 ^ (2 * Nat.log 2 M + 52) := by
          rw [← pow_add, ← pow_add]
          congr 1
          ring
  have hNR : ((calE (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * Nat.log 2 M + 52) := by
    exact_mod_cast hN
  have hpos : (0 : ℝ) < ((calE (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) := by
    have hEpos : 0 < calE (AdoorL M) (3072 * M) 2 := by
      rw [calE_doorL_two]
      exact Nat.mul_pos (by norm_num) (Nat.mul_pos hM hM)
    exact_mod_cast hEpos
  refine le_trans (logL_le_pow_two hpos hNR) (le_of_eq ?_)
  push_cast
  ring

/-- **`A_gate_logK`'s second logarithm at the levered linear door**: `(2L + 52 + K) log 2` —
the lever costs exactly its own `K`, as at the landed cut. -/
lemma log_calE_doorL_two_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    Real.log ((calE (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)
      ≤ (2 * (Nat.log 2 M : ℝ) + 52 + (K : ℝ)) * Real.log 2 := by
  have hMle : M ≤ 2 ^ (Nat.log 2 M + 1) := (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) M).le
  have hN : calE (AdoorL M) (s13GK K M) 2 ≤ 2 ^ (2 * Nat.log 2 M + 52 + K) := by
    rw [calE_doorL_two_gk]
    calc 2 ^ K * (844424930131968 * (M * M))
        ≤ 2 ^ K * (2 ^ 50 * (2 ^ (Nat.log 2 M + 1) * 2 ^ (Nat.log 2 M + 1))) :=
          Nat.mul_le_mul le_rfl (Nat.mul_le_mul (by norm_num) (Nat.mul_le_mul hMle hMle))
      _ = 2 ^ (2 * Nat.log 2 M + 52 + K) := by
          rw [← pow_add, ← pow_add, ← pow_add]
          congr 1
          ring
  have hNR : ((calE (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ (2 * Nat.log 2 M + 52 + K) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < ((calE (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) := by
    have hEpos : 0 < calE (AdoorL M) (s13GK K M) 2 := by
      rw [calE_doorL_two_gk]
      exact Nat.mul_pos (Nat.two_pow_pos K) (Nat.mul_pos (by norm_num) (Nat.mul_pos hM hM))
    exact_mod_cast hEpos
  refine le_trans (logL_le_pow_two hpos hNR) (le_of_eq ?_)
  push_cast
  ring

/-- **`A_gate_logK`'s first logarithm, AT THE LINEAR CONSUMER SHAPE**: `log(4M) ≤ (M + 3) log 2`
(`log_four_M_door` composed with `⌊log₂ M⌋ ≤ M`).  The landed bridge is anchor-free and so
survives as it stands; this is the shape the linear gate's `linarith` reads, since the gate's
right side is now linear in `M` rather than in `⌊log₂ M⌋`. -/
lemma log_four_M_doorL {M : ℕ} (hM : 1 ≤ M) :
    Real.log ((2 : ℝ) ^ 2 * (M : ℝ)) ≤ ((M : ℝ) + 3) * Real.log 2 := by
  have hLM : (Nat.log 2 M : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.log_le_self 2 M
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine le_trans (log_four_M_door hM) ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hl2

/-- **THE LINEAR GATE'S LEFT SIDE, FUSED** — `log(4M) + log e₂ ≤ (3M + 55) log 2`.  This is
the one bound the frame inhabitants below consume; it is the `add_le_add` of the two bridges
with `⌊log₂ M⌋ ≤ M` applied once. -/
lemma log_gate_doorL {M : ℕ} (hM : 1 ≤ M) :
    Real.log ((2 : ℝ) ^ 2 * (M : ℝ)) + Real.log ((calE (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)
      ≤ (3 * (M : ℝ) + 55) * Real.log 2 := by
  have hLM : (Nat.log 2 M : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.log_le_self 2 M
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsum := add_le_add (log_four_M_door hM) (log_calE_doorL_two hM)
  have hstep : ((Nat.log 2 M : ℝ) + 3) * Real.log 2
      + (2 * (Nat.log 2 M : ℝ) + 52) * Real.log 2 ≤ (3 * (M : ℝ) + 55) * Real.log 2 := by
    have h3 : 3 * (Nat.log 2 M : ℝ) + 55 ≤ 3 * (M : ℝ) + 55 := by linarith
    calc ((Nat.log 2 M : ℝ) + 3) * Real.log 2 + (2 * (Nat.log 2 M : ℝ) + 52) * Real.log 2
        = (3 * (Nat.log 2 M : ℝ) + 55) * Real.log 2 := by ring
      _ ≤ (3 * (M : ℝ) + 55) * Real.log 2 := mul_le_mul_of_nonneg_right h3 hl2
  linarith

/-- **THE LINEAR GATE'S LEFT SIDE AT THE LEVER** — `log(4M) + log e₂ ≤ (3M + 55 + K) log 2`. -/
lemma log_gate_doorL_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    Real.log ((2 : ℝ) ^ 2 * (M : ℝ)) + Real.log ((calE (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)
      ≤ (3 * (M : ℝ) + 55 + (K : ℝ)) * Real.log 2 := by
  have hLM : (Nat.log 2 M : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.log_le_self 2 M
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsum := add_le_add (log_four_M_door hM) (log_calE_doorL_two_gk K hM)
  have hstep : ((Nat.log 2 M : ℝ) + 3) * Real.log 2
      + (2 * (Nat.log 2 M : ℝ) + 52 + (K : ℝ)) * Real.log 2
      ≤ (3 * (M : ℝ) + 55 + (K : ℝ)) * Real.log 2 := by
    have h3 : 3 * (Nat.log 2 M : ℝ) + 55 + (K : ℝ) ≤ 3 * (M : ℝ) + 55 + (K : ℝ) := by linarith
    calc ((Nat.log 2 M : ℝ) + 3) * Real.log 2
          + (2 * (Nat.log 2 M : ℝ) + 52 + (K : ℝ)) * Real.log 2
        = (3 * (Nat.log 2 M : ℝ) + 55 + (K : ℝ)) * Real.log 2 := by ring
      _ ≤ (3 * (M : ℝ) + 55 + (K : ℝ)) * Real.log 2 := mul_le_mul_of_nonneg_right h3 hl2
  linarith

/-! ## §3 — the frame inhabitants at the linear anchor -/

/-- **THE LINEAR DOOR'S K-STATION FRAME** (`calFrameK_satisfiable_doorL`).  `CalFrameK` is
inhabited at `η = 1/12`, `A = AdoorL M`, `G = 3072M`, `Jb = 2`, `H₁ = P₁^{1/6}`, `X_d = Q_{Jb}`,
for EVERY `M ≥ 1` — `DoorFrame.calFrameK_satisfiable_door` field for field at the linear cut.

* `G_gateK` is untouched: `64·(2²M) = 256M ≤ (1/12)(3072M) = 256M`, EQUALITY, `A`-free.
* `A_gate_logK` is where the re-cut pays.  Left `≤ (48M + 880) log 2` (`log_gate_doorL`),
  right `(1/24)(68719476736·M·log 2 − 1)`: the margin is a FACTOR `> 3·10^6` at every `M`,
  and unlike the landed cut it grows LINEARLY with the demand rather than logarithmically.
* `A_gate_lin`, `A_floor`, `H1_two`, `H1_pin` read only the anchor's floor `2^36 ≤ AdoorL M`
  (`AdoorL_ge`) and level 1, so they are the landed arguments verbatim.

`P₁ = 2^{AdoorL M}` is never evaluated. -/
theorem calFrameK_satisfiable_doorL (M : ℕ) (hM : 1 ≤ M) :
    CalFrameK (1 / 12) (((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6))
      (AdoorL M) (3072 * M) M 2 (calQK (AdoorL M) (3072 * M) M 2) := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hMl2 : Real.log 2 ≤ (M : ℝ) * Real.log 2 := le_mul_of_one_le_left hl2 hMR
  -- `P₁ ≥ 64`, symbolically (the exponent is never expanded)
  have h64 : (64 : ℕ) ≤ calP (AdoorL M) (3072 * M) 1 := by
    have hE : (6 : ℕ) ≤ calE (AdoorL M) (3072 * M) 1 := by
      rw [calE_one]
      exact le_trans (by norm_num) (AdoorL_ge hM)
    have h6 : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [calP, h6]
    exact Nat.pow_le_pow_right (by norm_num) hE
  have h64R : (64 : ℝ) ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by exact_mod_cast h64
  have hP1pos : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  refine
    { eta_pos := by norm_num, eta_lt := by norm_num, one_le_Jb := by norm_num,
      one_le_G := by omega, one_le_M := hM, G_gateK := by push_cast; linarith,
      A_gate_lin := ?_, A_gate_logK := ?_, A_floor := le_trans (by norm_num) (AdoorL_ge hM),
      H1_two := ?_, H1_pin := ?_, Q_le_Xd := le_rfl }
  · -- `A_gate_lin`: `2Jb = 4 ≤ 2^36·M`
    rw [AdoorL_cast]
    push_cast
    linarith
  · -- `A_gate_logK`: `16(log 4M + log e₂) ≤ (1/24)(2^36·M·log 2 − 1)`, linearly in `M`
    push_cast
    rw [AdoorL_cast]
    refine le_trans (mul_le_mul_of_nonneg_left (log_gate_doorL hM) (by norm_num)) ?_
    linarith [Real.log_two_gt_d9, hMl2]
  · -- `H1_two`: `2 = 64^{1/6} ≤ P₁^{1/6}`
    calc (2 : ℝ) = (64 : ℝ) ^ ((1 : ℝ) / 6) := by
          rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast 2 6,
            ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6) :=
          Real.rpow_le_rpow (by norm_num) h64R (by norm_num)
  · -- `H1_pin`: `(P₁^{1/6})³ = P₁^{1/2}` — equality, the largest width the frame allows
    have hid : ((((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) ^ (3 : ℕ))
        = ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) 3,
        ← Real.rpow_mul hP1pos.le, show (1 : ℝ) / 6 * ((3 : ℕ) : ℝ) = (1 : ℝ) / 2 by norm_num]
    rw [hid]

/-- **THE LINEAR DOOR'S K-STATION FRAME, AT THE G-LEVER** — `DoorFrame`'s
`calFrameK_satisfiable_door_gk` at the linear anchor, and ⟦THE `K`-CEILING RE-CUT⟧.

The landed side condition is the ABSOLUTE `K ≤ 1.7·10^8`; here it is `K ≤ 1.7·10^8·M`.  The
gate's arithmetic: left `≤ (48M + 880 + 16K) log 2`, right `(1/24)(68719476736·M·log 2 − 1)`,
so the exact ceiling is `K ≤ 2^36·M/384 ≈ 1.7896·10^8·M` and the pin below spends 94.9 % of
it.  This is the register face the flat tower needs: the width demand `K ≈ 1.44·e^{λ₋/2}` is
met by a ceiling `577·e^{λ₋/2}`, a uniform 400× margin INDEPENDENT of the design constant. -/
theorem calFrameK_satisfiable_doorL_gk (K M : ℕ) (hM : 1 ≤ M) (hK : K ≤ 170000000 * M) :
    CalFrameK (1 / 12) (((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6))
      (AdoorL M) (s13GK K M) M 2 (calQK (AdoorL M) (s13GK K M) M 2) := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hMl2 : Real.log 2 ≤ (M : ℝ) * Real.log 2 := le_mul_of_one_le_left hl2 hMR
  have hKR : (K : ℝ) ≤ 170000000 * (M : ℝ) := by exact_mod_cast hK
  have hKl2 : (K : ℝ) * Real.log 2 ≤ 170000000 * ((M : ℝ) * Real.log 2) := by
    have := mul_le_mul_of_nonneg_right hKR hl2
    linarith [this]
  -- `P₁ ≥ 64`, symbolically (level 1 is K-invariant)
  have h64 : (64 : ℕ) ≤ calP (AdoorL M) (s13GK K M) 1 := by
    have hE : (6 : ℕ) ≤ calE (AdoorL M) (s13GK K M) 1 := by
      rw [calE_gk_one]
      exact le_trans (by norm_num) (AdoorL_ge hM)
    have h6 : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [calP, h6]
    exact Nat.pow_le_pow_right (by norm_num) hE
  have h64R : (64 : ℝ) ≤ ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by exact_mod_cast h64
  have hP1pos : (0 : ℝ) < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by linarith
  -- `G = 3072·2^K·M ≥ 3072M`, in ℝ — the a-fortiori direction for `G_gateK`
  have hGle : (3072 : ℝ) * (M : ℝ) ≤ ((s13GK K M : ℕ) : ℝ) := by
    have h : 3072 * M ≤ s13GK K M := le_s13GK K M
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at this
    linarith
  refine
    { eta_pos := by norm_num, eta_lt := by norm_num, one_le_Jb := by norm_num,
      one_le_G := one_le_s13GK K hM, one_le_M := hM, G_gateK := ?_,
      A_gate_lin := ?_, A_gate_logK := ?_, A_floor := le_trans (by norm_num) (AdoorL_ge hM),
      H1_two := ?_, H1_pin := ?_, Q_le_Xd := le_rfl }
  · -- `G_gateK`: a LOWER bound on `G`, so the lever only helps
    push_cast
    linarith [hGle]
  · -- `A_gate_lin`: `2Jb = 4 ≤ 2^36·M`
    rw [AdoorL_cast]
    push_cast
    linarith
  · -- `A_gate_logK`: the lever costs `16K log 2`, paid by the ceiling `K ≤ 1.7·10^8·M`
    push_cast
    rw [AdoorL_cast]
    refine le_trans (mul_le_mul_of_nonneg_left (log_gate_doorL_gk K hM) (by norm_num)) ?_
    linarith [Real.log_two_gt_d9, hMl2, hKl2]
  · -- `H1_two`: `2 = 64^{1/6} ≤ P₁^{1/6}`
    calc (2 : ℝ) = (64 : ℝ) ^ ((1 : ℝ) / 6) := by
          rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast 2 6,
            ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6) :=
          Real.rpow_le_rpow (by norm_num) h64R (by norm_num)
  · -- `H1_pin`: level 1, untouched by the lever
    have hid : ((((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) ^ (3 : ℕ))
        = ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) 3,
        ← Real.rpow_mul hP1pos.le, show (1 : ℝ) / 6 * ((3 : ℕ) : ℝ) = (1 : ℝ) / 2 by norm_num]
    rw [hid]

/-! ## §4 — what the linear door family inherits -/

/-- **The twelve `LevelGates` at the linear door family**, free from the frame. -/
theorem levelGates_calibrated_doorL (M : ℕ) (hM : 1 ≤ M) :
    ∀ j ∈ Finset.Icc 2 2,
      LevelGates (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M)
        (calH ((((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)))) (1 / 12)
        ((calP (AdoorL M) (3072 * M)) 1) (calQK (AdoorL M) (3072 * M) M 2) j :=
  levelGates_calibratedK (calFrameK_satisfiable_doorL M hM)

/-- **The twelve `LevelGates` at the levered linear door family**, free from the frame. -/
theorem levelGates_calibrated_doorL_gk (K M : ℕ) (hM : 1 ≤ M) (hK : K ≤ 170000000 * M) :
    ∀ j ∈ Finset.Icc 2 2,
      LevelGates (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M)
        (calH ((((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)))) (1 / 12)
        ((calP (AdoorL M) (s13GK K M)) 1) (calQK (AdoorL M) (s13GK K M) M 2) j :=
  levelGates_calibratedK (calFrameK_satisfiable_doorL_gk K M hM hK)

/-- **MR eq (28) at the linear door family** — `eq28_clears_of_M` composed.  The demand is
`8/δ ≤ M`, unchanged: eq (28) reads `log P_j/log Q_j = 1/(j²M)`, which is `A`-free and
`G`-free, so the re-cut costs it nothing. -/
theorem eq28_doorL_clears {M : ℕ} (hM : 1 ≤ M) (Jb : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hMδ : 8 / δ ≤ (M : ℝ)) :
    δ / 50 + (2 + 1 / 50) * ∑ j ∈ Finset.Icc 1 Jb,
        Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
          / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ)
      ≤ δ :=
  eq28_clears_of_M (one_le_AdoorL hM) (by omega) hM Jb hδ hMδ

/-- **MR eq (28) at the levered linear door family**. -/
theorem eq28_doorL_clears_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) (Jb : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hMδ : 8 / δ ≤ (M : ℝ)) :
    δ / 50 + (2 + 1 / 50) * ∑ j ∈ Finset.Icc 1 Jb,
        Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
          / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ)
      ≤ δ :=
  eq28_clears_of_M (one_le_AdoorL hM) (one_le_s13GK K hM) hM Jb hδ hMδ

/-- **The level-1 containment arm at the linear door** `log Q₁ = M·A_L(M)·log 2`.  With the
re-cut this is `2^36·M²·log 2`, so the floor arm `H_K := ⌈exp(M·AdoorL M·log 2)⌉₊` is
`exp(2^36 M²log 2)`-shaped — quadratic in the demand where the landed cut was `M log M`. -/
lemma log_calQK_doorL_one (M : ℕ) :
    Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)
      = (M : ℝ) * ((AdoorL M : ℕ) : ℝ) * Real.log 2 := by
  rw [log_calQK, calE_one]
  push_cast
  ring

/-- **THE LEVEL-1 TRANSPORT AT THE LINEAR DOOR** — `log Q₁` does not move under the lever. -/
lemma log_calQK_doorL_one_gk (K M : ℕ) :
    Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)
      = (M : ℝ) * ((AdoorL M : ℕ) : ℝ) * Real.log 2 := by
  rw [calQK_gk_one_eq]
  exact log_calQK_doorL_one M

/-- **THE LEVEL-1 `𝒫` TRANSPORT AT THE LINEAR DOOR** — `P₁` does not move under the lever. -/
lemma calP_doorL_one_gk (K M : ℕ) :
    calP (AdoorL M) (s13GK K M) 1 = calP (AdoorL M) (3072 * M) 1 :=
  calP_gk_one_eq (AdoorL M) K M

/-! ## §5 — the S11 hoist genre at the linear anchor

`S11Hoist`'s three arithmetic reads of the door (`s11_calE_door_two`,
`s11_log_calQK_door_two`, `s11_log_calP_door_one`) keep the anchor as a SYMBOL, so their
linear twins are the same statements with `AdoorL` in the anchor slot.  The `M`-slope of the
window-mass constant is therefore unchanged at the shape level; what changes is the VALUE of
the anchor, and every consumer reads it through `((AdoorL M : ℕ) : ℝ)`. -/

/-- `s11_calE_door_two` at the linear anchor: `e₂ = 12288·M·A_L(M)`. -/
theorem s11_calE_doorL_two (M : ℕ) :
    calE (AdoorL M) (3072 * M) 2 = 12288 * M * AdoorL M := by
  rw [calE_doorL_two, AdoorL]
  ring

/-- `s11_log_calQK_door_two` at the linear anchor: `log 𝒬₂ = 49152·M²·A_L(M)·log 2`. -/
theorem s11_log_calQK_doorL_two (M : ℕ) :
    Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
      = 49152 * (M : ℝ) ^ 2 * ((AdoorL M : ℕ) : ℝ) * Real.log 2 := by
  rw [calQK, s11_calE_doorL_two]
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

/-- `s11_log_calP_door_one` at the linear anchor: `log 𝒫₁ = A_L(M)·log 2` (`calE_one`). -/
theorem s11_log_calP_doorL_one (M : ℕ) :
    Real.log ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) = ((AdoorL M : ℕ) : ℝ) * Real.log 2 := by
  rw [calP, calE_one]
  push_cast
  rw [Real.log_pow]

/-- `s11_calE_door_two_gk` at the linear anchor: `e₂ = 12288·2^K·M·A_L(M)`. -/
theorem s11_calE_doorL_two_gk (K M : ℕ) :
    calE (AdoorL M) (s13GK K M) 2 = 12288 * 2 ^ K * M * AdoorL M := by
  rw [calE_gk_two, s11_calE_doorL_two]
  ring

/-- `s11_log_calQK_door_two_gk` at the linear anchor:
`log 𝒬₂ = 49152·2^K·M²·A_L(M)·log 2`. -/
theorem s11_log_calQK_doorL_two_gk (K M : ℕ) :
    Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      = 49152 * 2 ^ K * (M : ℝ) ^ 2 * ((AdoorL M : ℕ) : ℝ) * Real.log 2 := by
  rw [calQK, s11_calE_doorL_two_gk]
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

/-! ## §6 — the cap chain's door-reading link

`S13CapGrid.s13CapGrid_Lambda_sharp`/`_lo` read the SOCKET's `A + s`, never the door's anchor,
so the `Λ`-floor is anchor-free and gets no twin.  The single door-reading link in the cap
chain is `S16Budget.S16BaseScaleCap_gk` (and its relaxed `96` sibling), and both are supplied
for free from the landed cap by monotonicity of `𝒫₂` in the anchor. -/

/-- ⟦THE CAP AT THE LINEAR DOOR⟧ `S16BaseScaleCap_gk` with `AdoorL` in the anchor slot. -/
def S16BaseScaleCapL_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
    Real.log (Real.log (((A + s : ℕ)) : ℝ))
      ≤ Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) / 24

/-- ⟦THE RELAXED CAP AT THE LINEAR DOOR⟧ the `9.60000096` divisor of ⟦REPAIRS-LANE ITEM 3⟧. -/
def S16BaseScaleCapL96_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
    Real.log (Real.log (((A + s : ℕ)) : ℝ))
      ≤ Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) / 9.60000096

/-- ⟦THE RE-CUT IS FREE AT THE CAP INTERFACE⟧ the LANDED cap implies the LINEAR cap.  The
re-cut only raises the anchor (`Adoor_le_AdoorL`), hence raises `log 𝒫₂ = 4·A·G·log 2`, hence
WEAKENS the cap — so every supplier of `S16BaseScaleCap_gk` supplies `S16BaseScaleCapL_gk`
with no new obligation.  This is why the flat wave's cap face needs no re-derivation. -/
theorem s16_baseScaleCapL_of_baseScaleCap (K : ℕ) {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    (hcap : S16BaseScaleCap_gk K R M) : S16BaseScaleCapL_gk K R M := by
  intro H L q j A s hb
  refine le_trans (hcap H L q j A s hb) ?_
  have hmono : ((4 * (Adoor M * s13GK K M) : ℕ) : ℝ)
      ≤ ((4 * (AdoorL M * s13GK K M) : ℕ) : ℝ) := by
    have h : 4 * (Adoor M * s13GK K M) ≤ 4 * (AdoorL M * s13GK K M) :=
      Nat.mul_le_mul le_rfl (Nat.mul_le_mul (Adoor_le_AdoorL hM) le_rfl)
    exact_mod_cast h
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hstep := mul_le_mul_of_nonneg_right hmono hl2
  rw [s16_logP2, s16_logP2]
  linarith

/-- ⟦ITEM 3 AT THE LINEAR DOOR⟧ the linear cap implies its relaxed sibling — `/24` is `2.5×`
the demand of `/9.60000096`, exactly as at the landed anchor. -/
theorem s16_baseScaleCapL96_of_baseScaleCapL (K : ℕ) {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    (hcap : S16BaseScaleCapL_gk K R M) : S16BaseScaleCapL96_gk K R M := by
  intro H L q j A s hb
  have hLp0 : (0 : ℝ) < Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) := by
    rw [s16_logP2]
    have hA : (1 : ℕ) ≤ AdoorL M := one_le_AdoorL hM
    have hG : (1 : ℕ) ≤ s13GK K M := one_le_s13GK K hM
    have h4 : (1 : ℝ) ≤ ((4 * (AdoorL M * s13GK K M) : ℕ) : ℝ) := by
      have h : (1 : ℕ) ≤ 4 * (AdoorL M * s13GK K M) := by
        have := Nat.mul_le_mul hA hG; omega
      exact_mod_cast h
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith
  have hdiv : Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) / 24
      ≤ Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) / 9.60000096 :=
    div_le_div_of_nonneg_left hLp0.le (by norm_num) (by norm_num)
  linarith [hcap H L q j A s hb, hdiv]

/-! ## §7 — the level-1 length floor, the other door-reading link

`M4DoorRow.doorRowFloor M = M·Adoor M` is the exponent of `𝒬₁`, hence the capstone's dyadic
length gate.  At the linear anchor it becomes `2^36·M²` — QUADRATIC in the demand where the
landed cut was `M·log M`.  The gate itself (`doorL_length_gate_iff`) keeps its landed shape:
it is `calE_one` plus `Nat.pow_le_pow_iff_right`, both anchor-agnostic. -/

/-- **THE LINEAR DOOR'S LENGTH FLOOR** `doorRowFloorL M := M·A_L(M) = 2^36·M²`. -/
def doorRowFloorL (M : ℕ) : ℕ := M * AdoorL M

lemma doorRowFloorL_eq (M : ℕ) : doorRowFloorL M = 2 ^ 36 * (M * M) := by
  simp only [doorRowFloorL, AdoorL]
  ring

/-- `𝒬₁ = 2^{doorRowFloorL M}` at the linear door family — the identity behind `Q1_le_h`. -/
theorem s13_calQK_doorL_one (M : ℕ) :
    calQK (AdoorL M) (3072 * M) M 1 = 2 ^ doorRowFloorL M := by
  rw [calQK, calE_one, doorRowFloorL]
  ring_nf

/-- `𝒬₂ = 2^{16·A_L·G·M}` at the linear door family. -/
theorem s13_calQK_doorL_two (M : ℕ) :
    calQK (AdoorL M) (3072 * M) M 2 = 2 ^ (16 * (AdoorL M * (3072 * M) * M)) := by
  rw [calQK, calE_two]
  ring_nf

/-- **THE LENGTH GATE AT THE LINEAR DOOR** — the capstone's `hQ1h` at the dyadic length
`h = 2^j` forces `j` above the floor. -/
theorem doorL_length_gate {M j : ℕ}
    (h : ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) :
    M * AdoorL M ≤ j := by
  have hN : calQK (AdoorL M) (3072 * M) M 1 ≤ 2 ^ j := by exact_mod_cast h
  rw [calQK, calE_one] at hN
  have hle : 1 ^ 2 * M * AdoorL M ≤ j := (Nat.pow_le_pow_iff_right (by norm_num)).mp hN
  simpa using hle

/-- **THE LENGTH GATE AT THE LINEAR DOOR, BOTH WAYS** — the graded split's partition
`j < j₀ | j₀ ≤ j` is the capstone's own statement boundary at the linear anchor too. -/
theorem doorL_length_gate_iff {M j : ℕ} :
    ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
      ↔ doorRowFloorL M ≤ j := by
  constructor
  · intro h
    exact doorL_length_gate h
  · intro h
    have hN : calQK (AdoorL M) (3072 * M) M 1 ≤ 2 ^ j := by
      rw [calQK, calE_one]
      refine Nat.pow_le_pow_right (by norm_num) ?_
      simpa [doorRowFloorL] using h
    exact_mod_cast hN

