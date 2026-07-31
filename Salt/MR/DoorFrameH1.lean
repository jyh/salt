/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.DoorFrame

/-!
# `DoorFrameH1` — the door frame at MR's OWN `H₁` (the G6 repair)

`SeamCalibrationK.calFrameK_satisfiable` and `DoorFrame.calFrameK_satisfiable_door` both pin
`H₁ = P₁^{1/6}` — the frame's MAXIMUM, chosen to shrink Lemma 12's window rows.  That pin is
admissible (`H1_pin` holds with equality there) but it is **useless downstream**: the §8.1
level-1 term of `seam_row_calibratedK` has the shape

  `2(H₁ log Q₁ + 1)·(T Q₁/X_d + 1)·P₁^{−2α₁}·(4(H₁/(1−2α₁))e^{(1−2α₁)/H₁}
        + 60(H₁/α₁)e^{4α₁/H₁})   ≍   H₁²·log Q₁·P₁^{−2α₁}·(T Q₁/X_d + 1)`,

and at `η = 1/12` the level-1 exponent is `α₁ = mrAlpha (1/12) 1 = 1/4 − (1/12)(1 + 1/2)
= 1/8`, so `P₁^{−2α₁} = P₁^{−1/4}` and

  `H₁ = P₁^{1/6}`  ⟹  `H₁²·log Q₁·P₁^{−1/4} = P₁^{1/3−1/4}·log Q₁ = P₁^{1/12}·log Q₁`,

which **GROWS in `P₁`**.  Any `thm_A2′` wave built on that inhabitant lands true-but-useless.

## The corrected pin, and its honest value

MR's own width (p.24) is `H_j = j²·P₁^{1/6−η}/(log Q₁)^{1/3}`; at `η = 1/12` and `j = 1` that
is `H₁ = P₁^{1/12}/(log Q₁)^{1/3}`, which is what `H1door` takes.  The exponent arithmetic —
`H1door_level1_identity`, an **exact identity**, not an estimate — is

  `H₁²·log Q₁·P₁^{−1/4} = P₁^{1/6}(log Q₁)^{−2/3}·log Q₁·P₁^{−1/4}
                        = P₁^{1/6−1/4}(log Q₁)^{1/3} = (log Q₁)^{1/3}/P₁^{1/12}`,

i.e. exactly the interface's `(log Q₁)^{1/3}/P₁^{1/6−η}` at `η = 1/12` (`TLegE1`'s recorded
G3b verdict, lines 73–79, transplanted from MR's `H_j`/`α_j` pins to the door's `η`).  The
term now **DECAYS in `P₁`**, at rate `P₁^{−1/12}` up to the cube root of a logarithm.  That
identity is the certificate that G6 is fixed; `level1_term_door_decays` carries it through the
whole §8.1 level-1 factor with the absolute constant `5280`.

## Why the two gates still close, with room

Only two `CalFrameK` fields mention `H₁` (`H1_two`, `H1_pin`); every other field of
`calFrameK_satisfiable_door` is reproduced verbatim.

* `H1_two` `2 ≤ H₁`: cube it — `8 log Q₁ ≤ P₁^{1/4}`.  The V9c law keeps `P₁` symbolic:
  `Adoor M = 2^36(L+1) = 4·(2^34(L+1))` is divisible by `4`, so
  `P₁^{1/4} = 2^{17179869184(L+1)}` EXACTLY (no rpow estimate of a `2^{68719476736}`-scale
  number is ever attempted), while
  `8 log Q₁ = 8·M·A·log 2 ≤ 8MA ≤ 2^{2L+41}` by the base-2 bounding doctrine
  (`M ≤ 2^{L+1}`, `L+1 ≤ 2^{L+1}`).  The gate is `2L + 41 ≤ 17179869184(L+1)` — a margin of
  ~4.2·10⁸ at `L = 0`, widening with `M`.
* `H1_pin` `H₁³ ≤ P₁^{1/2}`: `H₁³ = P₁^{1/4}/log Q₁ ≤ P₁^{1/4} ≤ P₁^{1/2}`, the trivial
  direction, using only `log Q₁ ≥ 1` (which is `M·A·log 2 ≥ 262144 log 2`).  Where the old pin
  sat at EQUALITY, the corrected pin sits a full `P₁^{1/4}·log Q₁` below the ceiling — the
  frame was never the binding constraint; §8.1 was.

## The stones

* `Kdoor`, `Adoor_eq_four_mul` — the anchor's quarter, kept a DEFINITION so that
  `2^{K(M)}` is an atom to `ring`/`linarith` (the V9c law, tactic-side).
* `H1door` — the corrected width, `P₁^{1/12}/(log Q₁)^{1/3}`, symbolic in `calP`/`calQK`.
* `calP_door_one_ge`, `calP_door_one_rpow_quarter`, `one_le_log_calQK_door_one` — the three
  door-scale facts (`P₁ ≥ 64`, `P₁^{1/4} = 2^{K(M)}`, `log Q₁ ≥ 1`).
* `H1door_two`, `H1door_cube`, `H1door_pin` — the two gates.
* **`calFrameK_satisfiable_doorH1`** — the inhabitant, uniform in `M ≥ 1`.
* `levelGates_calibrated_doorH1` — the twelve `LevelGates`, free.
* `mrAlpha_door_one`, `H1door_level1_identity`, `H1door_level1_certificate`,
  **`level1_term_door_decays`** — the decay certificate.

The MARGIN-HYGIENE LAW is honoured: `M` is free throughout and no numeral here is a function
of `δ₀`.  The V9c law is honoured: `calP` and `calQK` are never evaluated; the only rewrites
used are `calE_one`, `log_calQK_door_one`, and base-2 exponent bounding.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 p.6, p.24 (the `H_j` table), eq (20)
p.24 (the `α_j` sequence), §8.1 p.25; `docs/sources/mr_extract.md` §2.7;
`Salt/MR/TLegE1.lean` lines 69–83 (the recorded G3b verdict);
`docs/exploration/pilot.md` 2026-07-27 (S8-INV's G6 finding).
-/

namespace Salt.MR

/-! ## §0 — two rpow collapses, on abstract reals

The V9c law forbids letting `norm_num`/`positivity`/`ring` anywhere near
`calP (Adoor M) …` — those tactics whnf the ℕ argument of the cast and try to evaluate a
`2^{68719476736}`-scale numeral.  Both rpow↔pow collapses this file needs are therefore proved
ONCE on abstract reals, where the arithmetic side goal carries no door symbol at all. -/

/-- `(x^a)^n = x^b` whenever `a·n = b` — the rpow-gate idiom, on an abstract base. -/
private lemma rpow_pow_eq {x : ℝ} (hx : 0 ≤ x) {a b : ℝ} (n : ℕ) (h : a * (n : ℝ) = b) :
    (x ^ a) ^ n = x ^ b := by
  rw [← Real.rpow_natCast (x ^ a) n, ← Real.rpow_mul hx, h]

/-- `(x^a)^n = x` whenever `a·n = 1`. -/
private lemma rpow_pow_one {x : ℝ} (hx : 0 ≤ x) {a : ℝ} (n : ℕ) (h : a * (n : ℝ) = 1) :
    (x ^ a) ^ n = x := by
  rw [← Real.rpow_natCast (x ^ a) n, ← Real.rpow_mul hx, h, Real.rpow_one]

/-- `(x^n)^a = x` whenever `n·a = 1` — the other direction, used to take the exact fourth
root of `P₁ = (2^{Kdoor M})^4`. -/
private lemma pow_rpow_one {x : ℝ} (hx : 0 ≤ x) (n : ℕ) {a : ℝ} (h : (n : ℝ) * a = 1) :
    (x ^ n) ^ a = x := by
  rw [← Real.rpow_natCast x n, ← Real.rpow_mul hx, h, Real.rpow_one]

/-! ## §1 — the corrected pin -/

/-- **The door anchor's quarter** `K(M) := 2^34(⌊log₂M⌋+1)`, so that `Adoor M = 4·K(M)`
(`Adoor_eq_four_mul`).  It is kept as a DEFINITION rather than a numeral expression precisely
so that `ring`/`linarith` treat `2^{K(M)}` as an atom and never attempt to expand
`2^{17179869184(L+1)}` (the V9c law). -/
def Kdoor (M : ℕ) : ℕ := 17179869184 * (Nat.log 2 M + 1)

lemma Adoor_eq_four_mul (M : ℕ) : Adoor M = 4 * Kdoor M := by
  rw [Adoor, Kdoor]
  ring

/-- **The door's corrected width** `H₁ := P₁^{1/12}/(log Q₁)^{1/3}` — MR p.24's own
`H_j = j²P₁^{1/6−η}/(log Q₁)^{1/3}` read at `j = 1`, `η = 1/12`.  This is the pin that makes
the §8.1 level-1 term decay (`H1door_level1_identity`); the landed `P₁^{1/6}` makes it grow.
`P₁ = 2^{Adoor M}` and `Q₁ = 2^{M·Adoor M}` stay symbols. -/
noncomputable def H1door (M : ℕ) : ℝ :=
  ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)
    / (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)

/-! ## §2 — the three door-scale facts -/

/-- `P₁ ≥ 64`, symbolically: `e₁ = A ≥ 2^36 ≥ 6` (`calE_one`, `Adoor_ge`). -/
lemma calP_door_one_ge (M : ℕ) : (64 : ℝ) ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
  have hE : (6 : ℕ) ≤ calE (Adoor M) (3072 * M) 1 := by
    rw [calE_one]
    exact le_trans (by norm_num) (Adoor_ge M)
  have h64 : (64 : ℕ) ≤ calP (Adoor M) (3072 * M) 1 := by
    rw [calP, show (64 : ℕ) = 2 ^ 6 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) hE
  exact_mod_cast h64

/-- **`P₁^{1/4}` EXACTLY, with no estimate**: `Adoor M = 4·K(M)`, so `P₁ = (2^{K(M)})^4` and
the fourth root is the base-2 power itself.  This is the V9c law's escape hatch — the
`2^{68719476736}`-scale symbol is never evaluated, only re-associated. -/
lemma calP_door_one_rpow_quarter (M : ℕ) :
    ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ Kdoor M := by
  have hnat : calP (Adoor M) (3072 * M) 1 = (2 ^ Kdoor M) ^ 4 := by
    rw [calP, calE_one, Adoor_eq_four_mul, pow_mul']
  have hcast : ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) = ((2 : ℝ) ^ Kdoor M) ^ (4 : ℕ) := by
    rw [hnat]
    push_cast
    ring
  rw [hcast]
  exact pow_rpow_one (pow_nonneg (by norm_num) _) 4 (by norm_num)

/-- The door's `8MA`, bounded by a base-2 exponent (the symbolic-log doctrine): `M ≤ 2^{L+1}`
and `L+1 ≤ 2^{L+1}`, so `8·M·A = 2^3·M·2^36(L+1) ≤ 2^{2L+41}`. -/
private lemma door_MA_bound (M : ℕ) :
    8 * (M * Adoor M) ≤ 2 ^ (2 * Nat.log 2 M + 41) := by
  have hMle : M ≤ 2 ^ (Nat.log 2 M + 1) := (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) M).le
  have hLle : Nat.log 2 M + 1 ≤ 2 ^ (Nat.log 2 M + 1) := (Nat.log 2 M + 1).lt_two_pow_self.le
  calc 8 * (M * Adoor M) = 2 ^ 3 * (M * (2 ^ 36 * (Nat.log 2 M + 1))) := by
        rw [Adoor]; ring
    _ ≤ 2 ^ 3 * (2 ^ (Nat.log 2 M + 1) * (2 ^ 36 * 2 ^ (Nat.log 2 M + 1))) :=
        Nat.mul_le_mul le_rfl (Nat.mul_le_mul hMle (Nat.mul_le_mul le_rfl hLle))
    _ = 2 ^ (2 * Nat.log 2 M + 41) := by
        rw [← pow_add, ← pow_add, ← pow_add]
        congr 1
        omega

/-- **`log Q₁ ≥ 1`** at the door family: `log Q₁ = M·A·log 2 ≥ 262144·log 2`
(`log_calQK_door_one`, `Adoor_cast`).  This is what makes the corrected pin's denominator
legitimate — nothing is divided by a possibly-zero logarithm. -/
lemma one_le_log_calQK_door_one {M : ℕ} (hM : 1 ≤ M) :
    (1 : ℝ) ≤ Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hL0 : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) := Nat.cast_nonneg _
  have hA : (262144 : ℝ) ≤ ((Adoor M : ℕ) : ℝ) := by rw [Adoor_cast]; linarith
  have hprod : (262144 : ℝ) * 0.6931471803 ≤ ((Adoor M : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul hA Real.log_two_gt_d9.le (by norm_num) (by linarith)
  have hAL : (1 : ℝ) ≤ ((Adoor M : ℕ) : ℝ) * Real.log 2 := by linarith
  have hstep : ((Adoor M : ℕ) : ℝ) * Real.log 2
      ≤ (M : ℝ) * (((Adoor M : ℕ) : ℝ) * Real.log 2) :=
    le_mul_of_one_le_left (by linarith) hMR
  rw [log_calQK_door_one]
  linarith

/-! ## §3 — the two gates that move -/

/-- **`H1_two` at the corrected pin.**  Cubed, the gate is `8 log Q₁ ≤ P₁^{1/4}`, i.e.
`8MA log 2 ≤ 2^{17179869184(L+1)}`; the left side is `≤ 2^{2L+41}` by base-2 bounding, and
`2L + 41 ≤ 17179869184(L+1)` with vast room. -/
lemma H1door_two {M : ℕ} (hM : 1 ≤ M) : 2 ≤ H1door M := by
  have hlogQ1 := one_le_log_calQK_door_one hM
  have hlogQ0 : (0 : ℝ) < Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := by linarith
  have hP64 := calP_door_one_ge M
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hz0 : (0 : ℝ)
      < (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hlogQ0 _
  have hz3 : ((Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ)
      = Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) :=
    rpow_pow_one hlogQ0.le 3 (by norm_num)
  have hw3 : (((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) ^ (3 : ℕ)
      = ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
    rpow_pow_eq hP0.le 3 (by norm_num)
  -- the arithmetic side: `8 log Q₁ ≤ 2^{2L+23} ≤ 2^{K(M)}`
  have hMAR : (8 : ℝ) * ((M : ℝ) * ((Adoor M : ℕ) : ℝ))
      ≤ (2 : ℝ) ^ (2 * Nat.log 2 M + 41) := by
    exact_mod_cast door_MA_bound M
  have hMA0 : (0 : ℝ) ≤ (M : ℝ) * ((Adoor M : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hlog2le : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hshrink : (8 : ℝ) * ((M : ℝ) * ((Adoor M : ℕ) : ℝ) * Real.log 2)
      ≤ (8 : ℝ) * ((M : ℝ) * ((Adoor M : ℕ) : ℝ)) := by nlinarith
  have hexpgrow : (2 : ℝ) ^ (2 * Nat.log 2 M + 41) ≤ (2 : ℝ) ^ Kdoor M :=
    pow_le_pow_right₀ (by norm_num) (by simp only [Kdoor]; omega)
  have hfinal : (2 : ℝ) ^ (3 : ℕ) * Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ Kdoor M := by
    have h8 : (2 : ℝ) ^ (3 : ℕ) = 8 := by norm_num
    rw [h8, log_calQK_door_one]
    linarith
  rw [H1door, le_div_iff₀ hz0]
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (Real.rpow_nonneg hP0.le _) ?_
  rw [mul_pow, hz3, hw3, calP_door_one_rpow_quarter]
  exact hfinal

/-- **The cube of the corrected pin**: `H₁³ = P₁^{1/4}/log Q₁`.  Two rpow collapses and
nothing else. -/
lemma H1door_cube {M : ℕ} (hM : 1 ≤ M) :
    (H1door M) ^ 3
      = ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)
          / Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := by
  have hlogQ1 := one_le_log_calQK_door_one hM
  have hlogQ0 : (0 : ℝ) < Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := by linarith
  have hP64 := calP_door_one_ge M
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hz3 : ((Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ)
      = Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) :=
    rpow_pow_one hlogQ0.le 3 (by norm_num)
  have hw3 : (((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) ^ (3 : ℕ)
      = ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
    rpow_pow_eq hP0.le 3 (by norm_num)
  rw [H1door, div_pow, hz3, hw3]

/-- **`H1_pin` at the corrected pin**, with room to spare: `H₁³ = P₁^{1/4}/log Q₁ ≤ P₁^{1/4}
≤ P₁^{1/2}`.  The landed `P₁^{1/6}` sat at EQUALITY here; the corrected pin sits a factor
`P₁^{1/4}·log Q₁` below the ceiling. -/
lemma H1door_pin {M : ℕ} (hM : 1 ≤ M) :
    (H1door M) ^ 3 ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
  have hlogQ1 := one_le_log_calQK_door_one hM
  have hP64 := calP_door_one_ge M
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hP1 : (1 : ℝ) ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  rw [H1door_cube hM]
  calc ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)
        / Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)
      ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
        div_le_self (Real.rpow_nonneg hP0.le _) hlogQ1
    _ ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)

/-! ## §4 — the inhabitant -/

/-- **THE DOOR'S K-STATION FRAME AT MR'S OWN `H₁`** (`calFrameK_satisfiable_doorH1`).
`CalFrameK` is inhabited at `η = 1/12`, `A = Adoor M`, `G = 3072M`, `Jb = 2`,
`H₁ = P₁^{1/12}/(log Q₁)^{1/3}`, `X_d = Q_{Jb}`, for EVERY `M ≥ 1`.

Field for field this is `DoorFrame.calFrameK_satisfiable_door`: only `H1_two` and `H1_pin`
mention `H₁` at all, and both are re-proved here (`H1door_two`, `H1door_pin`).  The ten
remaining fields — `eta_pos`, `eta_lt`, `one_le_Jb`, `one_le_G`, `one_le_M`, `G_gateK`
(EQUALITY at `G = 768·Jb²M`), `A_gate_lin`, `A_gate_logK` (uniform in `M` via
`log_four_M_door`/`log_calE_door_two`), `A_floor`, `Q_le_Xd` — are byte-identical, since none
of them sees the width.

The point of the change is downstream, not here: see `level1_term_door_decays`. -/
theorem calFrameK_satisfiable_doorH1 (M : ℕ) (hM : 1 ≤ M) :
    CalFrameK (1 / 12) (H1door M) (Adoor M) (3072 * M) M 2
      (calQK (Adoor M) (3072 * M) M 2) := by
  have hL0 : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) := Nat.cast_nonneg _
  have hL0' : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) * Real.log 2 :=
    mul_nonneg hL0 (Real.log_nonneg (by norm_num))
  refine
    { eta_pos := by norm_num, eta_lt := by norm_num, one_le_Jb := by norm_num,
      one_le_G := by omega, one_le_M := hM, G_gateK := by push_cast; linarith,
      A_gate_lin := ?_, A_gate_logK := ?_, A_floor := le_trans (by norm_num) (Adoor_ge M),
      H1_two := H1door_two hM, H1_pin := H1door_pin hM, Q_le_Xd := le_rfl }
  · -- `A_gate_lin`: `2Jb = 4 ≤ 2^36 ≤ Adoor M`
    rw [Adoor_cast]
    push_cast
    linarith
  · -- `A_gate_logK`: `16(log 4M + log e₂) ≤ (1/24)(Adoor M · log 2 − 1)`, uniformly in `M`
    push_cast
    rw [Adoor_cast]
    refine le_trans (mul_le_mul_of_nonneg_left
      (add_le_add (log_four_M_door hM) (log_calE_door_two hM)) (by norm_num)) ?_
    linarith [Real.log_two_gt_d9, hL0, hL0']

/-- **The twelve `LevelGates` at the corrected door family**, free from the frame
(`levelGates_calibratedK`), at `Jb = 2`. -/
theorem levelGates_calibrated_doorH1 (M : ℕ) (hM : 1 ≤ M) :
    ∀ j ∈ Finset.Icc 2 2,
      LevelGates (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M)
        (calH (H1door M)) (1 / 12)
        ((calP (Adoor M) (3072 * M)) 1) (calQK (Adoor M) (3072 * M) M 2) j :=
  levelGates_calibratedK (calFrameK_satisfiable_doorH1 M hM)

/-! ## §5 — the decay certificate (the G6 fix, made explicit) -/

/-- `α₁ = 1/4 − η(1 + 1/2) = 1/8` at `η = 1/12` (MR eq (20) p.24, `TLegKill.mrAlpha`). -/
lemma mrAlpha_door_one : mrAlpha (1 / 12 : ℝ) 1 = 1 / 8 := by
  rw [mrAlpha]
  norm_num

/-- The abstract shape behind the identity: `(w/z)²·z³·(w³)⁻¹ = z/w`. -/
private lemma level1_ratio {w z L P : ℝ} (hw : 0 < w) (hz : 0 < z)
    (hL : L = z ^ (3 : ℕ)) (hP : P = (w ^ (3 : ℕ))⁻¹) :
    (w / z) ^ 2 * L * P = z / w := by
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hz0 : z ≠ 0 := ne_of_gt hz
  subst hL
  subst hP
  field_simp

/-- **THE G6 CERTIFICATE, as an exact identity.**  At the corrected pin the §8.1 level-1
block factor is

  `H₁²·log Q₁·P₁^{−1/4} = P₁^{1/6}(log Q₁)^{−2/3}·log Q₁·P₁^{−1/4}
                        = P₁^{1/6−1/4}(log Q₁)^{1/3} = (log Q₁)^{1/3}/P₁^{1/12}`,

i.e. MR §8.1's own `(log Q₁)^{1/3}/P₁^{1/6−η}` at `η = 1/12` — a term that **DECAYS in `P₁`**
at rate `P₁^{−1/12}`.  The exponent `e` is taken as a hypothesis so the consumer may present
`−1/4` in whatever form its own `α`-arithmetic produced. -/
theorem H1door_level1_identity {M : ℕ} (hM : 1 ≤ M) {e : ℝ} (he : e = -((1 : ℝ) / 4)) :
    (H1door M) ^ 2 * Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)
        * ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ e
      = (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
          / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) := by
  have hlogQ1 := one_le_log_calQK_door_one hM
  have hlogQ0 : (0 : ℝ) < Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := by linarith
  have hP64 := calP_door_one_ge M
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hz0 : (0 : ℝ)
      < (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hlogQ0 _
  have hw0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
    Real.rpow_pos_of_pos hP0 _
  have hz3 : ((Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ)
      = Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) :=
    rpow_pow_one hlogQ0.le 3 (by norm_num)
  have hw3 : (((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) ^ (3 : ℕ)
      = ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
    rpow_pow_eq hP0.le 3 (by norm_num)
  rw [H1door]
  refine level1_ratio hw0 hz0 hz3.symm ?_
  rw [he, hw3, Real.rpow_neg hP0.le]

/-- The certificate in the `mrAlpha` form the §8.1 row actually carries. -/
theorem H1door_level1_certificate {M : ℕ} (hM : 1 ≤ M) :
    (H1door M) ^ 2 * Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)
        * ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12) 1))
      = (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
          / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
  H1door_level1_identity hM (by rw [mrAlpha_door_one]; norm_num)

/-- The abstract §8.1 level-1 shape, at `α₁ = 1/8` and `H₁ ≥ 2`: the bracket is
`(16/3)H₁e^{3/(4H₁)} + 480H₁e^{1/(2H₁)} ≤ (16/3 + 480)e·H₁ ≤ 1320H₁` and the block count
`H₁log Q₁ + 1 ≤ 2H₁log Q₁`, so the whole factor is `≤ 2·2·1320·H₁²log Q₁·P₁^{−1/4}`. -/
private lemma level1_shape {Ha Lq Pq R : ℝ} (hH2 : 2 ≤ Ha) (hLq : 1 ≤ Lq)
    (hPq : 0 < Pq) (hR : 0 ≤ R) :
    2 * (Ha * Lq + 1) * R * Pq
        * (4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
            + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha))
      ≤ 5280 * R * (Ha ^ 2 * Lq * Pq) := by
  have hHa0 : (0 : ℝ) < Ha := by linarith
  have he1 : Real.exp ((3 / 4 : ℝ) / Ha) ≤ 2.7182818286 := by
    have h : (3 / 4 : ℝ) / Ha ≤ 1 := by rw [div_le_one hHa0]; linarith
    exact le_trans (Real.exp_le_exp.mpr h) Real.exp_one_lt_d9.le
  have he2 : Real.exp ((1 / 2 : ℝ) / Ha) ≤ 2.7182818286 := by
    have h : (1 / 2 : ℝ) / Ha ≤ 1 := by rw [div_le_one hHa0]; linarith
    exact le_trans (Real.exp_le_exp.mpr h) Real.exp_one_lt_d9.le
  have hB1 : 4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
      ≤ 16 / 3 * Ha * 2.7182818286 := by
    have hEq : 4 * (Ha / (3 / 4 : ℝ)) = 16 / 3 * Ha := by ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_left he1 (by linarith)
  have hB2 : 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha)
      ≤ 480 * Ha * 2.7182818286 := by
    have hEq : 60 * (Ha / (1 / 8 : ℝ)) = 480 * Ha := by ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_left he2 (by linarith)
  have hB : 4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
      + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha) ≤ 1320 * Ha := by linarith
  have hB0 : (0 : ℝ) ≤ 4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
      + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha) := by
    have hc1 : (0 : ℝ) ≤ 4 * (Ha / (3 / 4 : ℝ)) := by linarith
    have hc2 : (0 : ℝ) ≤ 60 * (Ha / (1 / 8 : ℝ)) := by linarith
    linarith [mul_nonneg hc1 (Real.exp_pos ((3 / 4 : ℝ) / Ha)).le,
      mul_nonneg hc2 (Real.exp_pos ((1 / 2 : ℝ) / Ha)).le]
  have hHL : (1 : ℝ) ≤ Ha * Lq := by nlinarith
  have key : 2 * (Ha * Lq + 1)
        * (4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
            + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha))
      ≤ 5280 * (Ha ^ 2 * Lq) := by
    calc 2 * (Ha * Lq + 1)
          * (4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
              + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha))
        ≤ (4 * (Ha * Lq)) * (1320 * Ha) :=
          mul_le_mul (by linarith) hB hB0 (by linarith)
      _ = 5280 * (Ha ^ 2 * Lq) := by ring
  calc 2 * (Ha * Lq + 1) * R * Pq
        * (4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
            + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha))
      = (2 * (Ha * Lq + 1)
          * (4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
              + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha))) * (R * Pq) := by ring
    _ ≤ (5280 * (Ha ^ 2 * Lq)) * (R * Pq) :=
        mul_le_mul_of_nonneg_right key (mul_nonneg hR hPq.le)
    _ = 5280 * R * (Ha ^ 2 * Lq * Pq) := by ring

/-- **G6, FIXED — the §8.1 level-1 factor at the corrected pin DECAYS in `P₁`.**

The factor is `seam_row_calibratedK`'s level-1 term verbatim (its `(Tann·Q₁/X_d + 1)` carried
as the free nonnegative `R`), at `η = 1/12`, `H₁ = H1door M`:

  `2(H₁ log Q₁ + 1)·R·P₁^{−2α₁}·(4(H₁/(1−2α₁))e^{(1−2α₁)/H₁} + 60(H₁/α₁)e^{4α₁/H₁})
      ≤ 5280·R·(log Q₁)^{1/3}/P₁^{1/12}`.

The constant `5280 = 2·2·1320` is honest and absolute: `1320 ≥ (16/3 + 480)·e` bounds the
bracket by `1320H₁` (using only `H₁ ≥ 2`, so both exponentials are `≤ e`), one factor `2`
absorbs `H₁ log Q₁ + 1 ≤ 2H₁ log Q₁`, and the leading `2` is the row's own.  The right side
is exactly MR §8.1's `(log Q₁)^{1/3}/P₁^{1/6−η}` at `η = 1/12`, via the exact identity
`H1door_level1_certificate`.

`5280` is the `H₁ ≥ 2`-ONLY constant, deliberately crude: at the door, `H₁ ≈ 2^{21845}`, so
both exponentials are `1 + o(1)` and the `+1` is negligible against `H₁ log Q₁`, whence the
true value is `2(16/3 + 480) ≈ 970.7` — S8-INV's `970`.  Tightening costs the consumer only a
numeral and is not done here, since the DECAY, not the constant, is what G6 was about.

At the LANDED pin `H₁ = P₁^{1/6}` the same factor is `≍ P₁^{1/12}·log Q₁·R`, which grows —
that is the whole content of the G6 finding, and the whole reason this file exists. -/
theorem level1_term_door_decays {M : ℕ} (hM : 1 ≤ M) {R : ℝ} (hR : 0 ≤ R) :
    2 * (calH (H1door M) 1 * Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) + 1) * R
        * ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12) 1))
        * (4 * (calH (H1door M) 1 / (1 - 2 * mrAlpha (1 / 12) 1))
              * Real.exp ((1 - 2 * mrAlpha (1 / 12) 1) / calH (H1door M) 1)
            + 60 * (calH (H1door M) 1 / mrAlpha (1 / 12) 1)
                * Real.exp (4 * mrAlpha (1 / 12) 1 / calH (H1door M) 1))
      ≤ 5280 * R
          * ((Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
              / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by
  have hP64 := calP_door_one_ge M
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hcalH : calH (H1door M) 1 = H1door M := by
    rw [calH, Nat.cast_one, one_pow, one_mul]
  have hαe : (-(2 * mrAlpha (1 / 12 : ℝ) 1)) = -((1 : ℝ) / 4) := by
    rw [mrAlpha_door_one]; norm_num
  have hα1 : (1 - 2 * mrAlpha (1 / 12 : ℝ) 1) = 3 / 4 := by rw [mrAlpha_door_one]; norm_num
  have hα3 : (4 * mrAlpha (1 / 12 : ℝ) 1) = 1 / 2 := by rw [mrAlpha_door_one]; norm_num
  rw [hcalH, hαe, hα1, hα3, mrAlpha_door_one,
    ← H1door_level1_identity (M := M) hM (e := -((1 : ℝ) / 4)) rfl]
  exact level1_shape (H1door_two hM) (one_le_log_calQK_door_one hM)
    (Real.rpow_pos_of_pos hP0 _) hR

/-! ## §GK — the G-lever twin

**THIS WHOLE PAGE IS K-INVARIANT EXCEPT THE FRAME.**  `H1door M = P₁^{1/12}/(log Q₁)^{1/3}`
reads the door's ladder at LEVEL 1 ONLY, and level 1 does not see `G` (`GLever.calE_gk_one`).
So `H1door`, `calP_door_one_ge`, `calP_door_one_rpow_quarter`, `one_le_log_calQK_door_one`,
`H1door_two`, `H1door_cube`, `H1door_pin`, `H1door_level1_identity`,
`H1door_level1_certificate` and `level1_term_door_decays` **KEEP THEIR LANDED NAMES** under
the lever and are used verbatim inside every `_gk` consumer.  What they get is the transport
equality `H1door_gk_eq` (and `calP_door_one_gk`/`log_calQK_door_one_gk` upstream), not a twin.

The ONE object that genuinely moves is the frame inhabitant, because `A_gate_logK` and
`G_gateK` read level `Jb = 2`. -/

/-- **THE WIDTH IS K-INVARIANT** (`H1door_gk_eq`).  MR's own `H₁` re-read at the lever's base
IS `H1door M` — both of its ladder reads are at level 1.  This is why the whole `DoorFrameH1`
page survives the G-lever with no twin at all. -/
lemma H1door_gk_eq (K M : ℕ) :
    ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)
        / (Real.log ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
      = H1door M := by
  rw [calP_gk_one_eq, calQK_gk_one_eq, H1door]

/-- `P₁ ≥ 64` at the lever — level-1 transport of `calP_door_one_ge`. -/
lemma calP_door_one_ge_gk (K M : ℕ) :
    (64 : ℝ) ≤ ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) := by
  rw [calP_door_one_gk]
  exact calP_door_one_ge M

/-- `log Q₁ ≥ 1` at the lever — level-1 transport of `one_le_log_calQK_door_one`. -/
lemma one_le_log_calQK_door_one_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    (1 : ℝ) ≤ Real.log ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) := by
  rw [calQK_gk_one_eq]
  exact one_le_log_calQK_door_one hM

/-- **G6 AT THE LEVER** — `level1_term_door_decays` transported.  Every symbol in the §8.1
level-1 factor is level-1, so the lever leaves the decay certificate untouched. -/
theorem level1_term_door_decays_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) {R : ℝ} (hR : 0 ≤ R) :
    2 * (calH (H1door M) 1 * Real.log ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) + 1) * R
        * ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12) 1))
        * (4 * (calH (H1door M) 1 / (1 - 2 * mrAlpha (1 / 12) 1))
              * Real.exp ((1 - 2 * mrAlpha (1 / 12) 1) / calH (H1door M) 1)
            + 60 * (calH (H1door M) 1 / mrAlpha (1 / 12) 1)
                * Real.exp (4 * mrAlpha (1 / 12) 1 / calH (H1door M) 1))
      ≤ 5280 * R
          * ((Real.log ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
              / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by
  rw [calP_door_one_gk, calQK_gk_one_eq]
  exact level1_term_door_decays hM hR

/-- **THE DOOR'S K-STATION FRAME AT MR'S OWN `H₁`, AT THE G-LEVER**
(`calFrameK_satisfiable_doorH1_gk`).  `CalFrameK` at `η = 1/12`, `A = Adoor M`,
`G = s13GK K M`, `Jb = 2`, `H₁ = H1door M` (the LANDED width — it is K-invariant),
`X_d = Q_{Jb}`, for every `M ≥ 1` and every `K ≤ 1.7·10⁸`.

Exactly as in the landed file, only `H1_two` and `H1_pin` mention `H₁`, and both are the
landed lemmas: `H1_two` does not mention `G` at all, and `H1_pin`'s `P₁` is level 1
(`calP_door_one_gk`).  The other ten fields are `calFrameK_satisfiable_door_gk`'s, which is
where the lever's only real cost — the `+K` inside `A_gate_logK`'s second logarithm — is
paid, hence the same `K ≤ 1.7·10⁸` side condition. -/
theorem calFrameK_satisfiable_doorH1_gk (K M : ℕ) (hM : 1 ≤ M) (hK : K ≤ 170000000) :
    CalFrameK (1 / 12) (H1door M) (Adoor M) (s13GK K M) M 2
      (calQK (Adoor M) (s13GK K M) M 2) := by
  have hF := calFrameK_satisfiable_door_gk K M hM hK
  refine ⟨hF.eta_pos, hF.eta_lt, hF.one_le_Jb, hF.one_le_G, hF.one_le_M, hF.G_gateK,
    hF.A_gate_lin, hF.A_gate_logK, hF.A_floor, H1door_two hM, ?_, hF.Q_le_Xd⟩
  rw [calP_door_one_gk]
  exact H1door_pin hM

/-- **The twelve `LevelGates` at the levered corrected door family**, free from the frame. -/
theorem levelGates_calibrated_doorH1_gk (K M : ℕ) (hM : 1 ≤ M) (hK : K ≤ 170000000) :
    ∀ j ∈ Finset.Icc 2 2,
      LevelGates (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M)
        (calH (H1door M)) (1 / 12)
        ((calP (Adoor M) (s13GK K M)) 1) (calQK (Adoor M) (s13GK K M) M 2) j :=
  levelGates_calibratedK (calFrameK_satisfiable_doorH1_gk K M hM hK)

-- #audit (temporary)

end Salt.MR
