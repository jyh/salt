/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SeamCalibrationK

/-!
# `DoorFrame` — the K-station frame at the door's `M`, PARAMETRIC

`SeamCalibrationK.calFrameK_satisfiable` inhabits `CalFrameK` at ONE pin (`A = 65536`,
`G = 2457600`, `M = 800`).  The §4 major-arc port runs the sieve family `𝒮` at the K-ladder
(`docs/exploration/s9-design-0726.md` ruling D-FAMILY), and there the re-pin scale is
`M = ⌈8C/δ₀⌉`-shaped — the eq-(28) demand `8/δ ≤ M` of `eq28_clears_of_M`, at the door's
`δ₀` and MR Lemma 2.2's constant.  That `M` overflows the pinned frame: `A_gate_logK`'s left
side grows like `32 log M`, so a FIXED `A` closes only up to `M ≈ e^{48}`.

`δ₀`'s only exposed property is `0 < δ₀` (`SpineFinal`'s existential — the value `2·10^{−49}`
is a shape, not a datum), so no fixed-`A` stone can be proved: the ⟦AMENDMENT A⟧ ruling is
that **the inhabitant is parametric**, and the standing MARGIN-HYGIENE LAW is that no numeral
in this file is a function of `δ₀`.  `M` stays a free variable throughout; nothing here
evaluates it, and nothing here evaluates `P₁ = 2^{Adoor M}` either (the V9c law).

## The parametrisation

  `Adoor M := 2^18 · (Nat.log 2 M + 1)`,   `G := 3072 · M`,   `Jb := 2`,   `η := 1/12`,
  `H₁ := P₁^{1/6}`,   `X_d := Q_{Jb}`.

The `Nat.log 2 M + 1` factor is the whole device: it is a base-2 logarithm of the anchor's
own `M`, so the anchor grows with the demand, and `A_gate_logK` — the one gate that sees
`M` logarithmically on the left and linearly through `A` on the right — closes UNIFORMLY.

## The gate-by-gate account (all twelve, at `Jb = 2`)

* `G_gateK` `64(Jb²M) ≤ ηG`: `256M ≤ (1/12)(3072M) = 256M` — EQUALITY, so `G = 3072M` is the
  smallest admissible base at this `η`, exactly as `G = 768·Jb²M` was at the landed pin
  (`768·4·800 = 2457600`).  The K-factor is the only linear cost of the re-pin.
* `A_gate_logK` `16(log(4M) + log e₂) ≤ (1/24)(A log 2 − 1)`: the two logarithms are bounded
  by base-2 exponents rather than evaluated — `4M ≤ 2^{L+3}` (`Nat.lt_pow_succ_log_self`) and
  `e₂ = 4AG = 3·2^{30}(L+1)M ≤ 2^{2L+34}` (`Nat.lt_two_pow_self` for the `L+1`), with
  `L := Nat.log 2 M`.  So the left side is `≤ (48L + 592) log 2` and the right side is
  `(1/24)(262144(L+1) log 2 − 1)` — a margin of ~18× at `L = 0` widening to ~227× as `L → ∞`.
  Both sides carry `L` linearly; the gate is one `linarith` over the atoms `log 2`, `L log 2`.
* `A_gate_lin` `2Jb ≤ A`, `A_floor` `24 ≤ A`: `Adoor M ≥ 2^18` (`Adoor_ge`).
* `H1_two` `2 ≤ H₁`: `P₁ ≥ 64` from `calE A G 1 = A ≥ 6` (`calE_one`) — `P₁` stays symbolic.
* `H1_pin` `H₁³ ≤ P₁^{1/2}`: EQUALITY at `H₁ = P₁^{1/6}`, the K-3 width (`SeamCalibrationK`'s
  ⟦V9b⟧ finding (iii)), transplanted verbatim.
* `one_le_G` `1 ≤ 3072M`, `one_le_M`, `one_le_Jb`, `eta_pos`, `eta_lt`, `Q_le_Xd` (`le_rfl` at
  `X_d := Q_{Jb}`): immediate.

## The stones

* `Adoor`, `Adoor_ge`, `one_le_Adoor`, `Adoor_cast`, `calE_door_two` — the anchor and its
  arithmetic (`e₂ = 3221225472·(L+1)M`, a ℕ identity; no `2^{2^18}` is ever formed).
* `log_four_M_door`, `log_calE_door_two` — the two `Nat.log`→`Real.log` bridges, the only
  place `M`'s size is used.
* **`calFrameK_satisfiable_door`** — the inhabitant, uniform in `M ≥ 1`.
* `levelGates_calibrated_door` — the twelve `LevelGates` at the door family, free.
* `eq28_door_clears` — MR eq (28) at the door family for ANY `δ > 0` with `8/δ ≤ M`
  (`eq28_clears_of_M` composed): the demand side, parametric, no numeral pinned to `δ₀`.
* `log_calQK_door_one` — `log Q₁ = M·A·log 2`, the level-1 containment arm `[P₁,Q₁] ⊂ [1,h]`
  (⟦AMENDMENT A⟧'s corrected `H_K`: `log h ≥ M·Adoor M·log 2`, NOT the top-block form).

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 p.6 ((2), (3), (4)), §9 p.31 (eq (28));
MRT `1503.05121v3` A.2, Lemma 2.2 p.8; `docs/exploration/s9-design-0726.md` (D-FAMILY,
D-FLOOR, ⟦AMENDMENT A⟧); `docs/exploration/hsup-design.md` ⟦V9b⟧, ⟦V9c⟧.
-/

namespace Salt.MR

/-! ## §0 — the door's anchor -/

/-- **The door's anchor exponent** `A(M) := 2^18·(⌊log₂ M⌋ + 1)`.  The `2^18` is the size
`A_gate_logK` needs against the door's `e₂`; the `⌊log₂ M⌋ + 1` is what makes that gate
uniform in `M` (⟦AMENDMENT A⟧ — the fixed-`A` stone is unprovable, `δ₀` having no exposed
lower bound).  `M` is never evaluated: at the door it is `⌈8C/δ₀⌉`-shaped. -/
def Adoor (M : ℕ) : ℕ := 2 ^ 18 * (Nat.log 2 M + 1)

lemma Adoor_ge (M : ℕ) : 2 ^ 18 ≤ Adoor M := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

lemma one_le_Adoor (M : ℕ) : 1 ≤ Adoor M := le_trans (by norm_num) (Adoor_ge M)

/-- The anchor in ℝ, with `2^18` evaluated — the form `A_gate_logK`'s right side needs. -/
lemma Adoor_cast (M : ℕ) : ((Adoor M : ℕ) : ℝ) = 262144 * ((Nat.log 2 M : ℝ) + 1) := by
  simp only [Adoor]
  push_cast
  norm_num

/-- **The door's `e₂`, as a ℕ identity**: `e₂ = A·G·(2!)² = 2^18(L+1)·3072M·4
= 3·2^{30}·(L+1)M`.  This is the only place the door family's exponent ladder is computed,
and it is computed at level 2 only — `calE_one` covers level 1 and nothing above `Jb = 2`
is ever formed. -/
lemma calE_door_two (M : ℕ) :
    calE (Adoor M) (3072 * M) 2 = 3221225472 * ((Nat.log 2 M + 1) * M) := by
  simp only [calE, Adoor, Nat.factorial]
  ring

/-! ## §1 — the two `Nat.log`→`Real.log` bridges -/

/-- `x ≤ 2^k → log x ≤ k log 2`.  Every size fact below is routed through a base-2 exponent,
so no logarithm of a door-scale number is ever estimated numerically. -/
private lemma log_le_pow_two {x : ℝ} {k : ℕ} (hx : 0 < x) (h : x ≤ (2 : ℝ) ^ k) :
    Real.log x ≤ (k : ℝ) * Real.log 2 := by
  calc Real.log x ≤ Real.log ((2 : ℝ) ^ k) := Real.log_le_log hx h
    _ = (k : ℝ) * Real.log 2 := by rw [Real.log_pow]

/-- **`A_gate_logK`'s first logarithm**: `log(Jb²M) = log(4M) ≤ (L + 3) log 2`, from
`M < 2^{L+1}` (`Nat.lt_pow_succ_log_self` — `Nat.log` is the FLOOR log, so this is the
inequality that holds, and `Nat.log 2 1 = 0` is not an exception to it). -/
lemma log_four_M_door {M : ℕ} (hM : 1 ≤ M) :
    Real.log ((2 : ℝ) ^ 2 * (M : ℝ)) ≤ ((Nat.log 2 M : ℝ) + 3) * Real.log 2 := by
  have hMle : (M : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 M + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) M).le
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hstep : (2 : ℝ) ^ 2 * (M : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 M + 3) := by
    have hsplit : (2 : ℝ) ^ (Nat.log 2 M + 3) = (2 : ℝ) ^ 2 * (2 : ℝ) ^ (Nat.log 2 M + 1) := by
      rw [← pow_add]
      ring_nf
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hMle (by positivity)
  refine le_trans (log_le_pow_two (by positivity) hstep) (le_of_eq ?_)
  push_cast
  ring

/-- **`A_gate_logK`'s second logarithm**: `log e₂ ≤ (2L + 34) log 2`, from
`e₂ = 3·2^{30}(L+1)M ≤ 2^{32}·2^{L+1}·2^{L+1}` — the `L+1` paid by `Nat.lt_two_pow_self`,
the `M` by the floor-log bound again. -/
lemma log_calE_door_two {M : ℕ} (hM : 1 ≤ M) :
    Real.log ((calE (Adoor M) (3072 * M) 2 : ℕ) : ℝ)
      ≤ (2 * (Nat.log 2 M : ℝ) + 34) * Real.log 2 := by
  have hMle : M ≤ 2 ^ (Nat.log 2 M + 1) := (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) M).le
  have hLle : Nat.log 2 M + 1 ≤ 2 ^ (Nat.log 2 M + 1) := (Nat.log 2 M + 1).lt_two_pow_self.le
  have hN : calE (Adoor M) (3072 * M) 2 ≤ 2 ^ (2 * Nat.log 2 M + 34) := by
    rw [calE_door_two]
    calc 3221225472 * ((Nat.log 2 M + 1) * M)
        ≤ 2 ^ 32 * (2 ^ (Nat.log 2 M + 1) * 2 ^ (Nat.log 2 M + 1)) :=
          Nat.mul_le_mul (by norm_num) (Nat.mul_le_mul hLle hMle)
      _ = 2 ^ (2 * Nat.log 2 M + 34) := by
          rw [← pow_add, ← pow_add]
          congr 1
          ring
  have hNR : ((calE (Adoor M) (3072 * M) 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * Nat.log 2 M + 34) := by
    exact_mod_cast hN
  have hpos : (0 : ℝ) < ((calE (Adoor M) (3072 * M) 2 : ℕ) : ℝ) := by
    have hEpos : 0 < calE (Adoor M) (3072 * M) 2 := by
      rw [calE_door_two]
      exact Nat.mul_pos (by norm_num) (Nat.mul_pos (Nat.succ_pos _) hM)
    exact_mod_cast hEpos
  refine le_trans (log_le_pow_two hpos hNR) (le_of_eq ?_)
  push_cast
  ring

/-! ## §2 — the inhabitant, uniform in `M` -/

/-- **THE DOOR'S K-STATION FRAME** (`calFrameK_satisfiable_door`).  `CalFrameK` is inhabited
at `η = 1/12`, `A = Adoor M`, `G = 3072M`, `Jb = 2`, `H₁ = P₁^{1/6}`, `X_d = Q_{Jb}`, for
EVERY `M ≥ 1` — in particular at the door's `M = ⌈8C/δ₀⌉`-shape, which the landed pinned
inhabitant (`calFrameK_satisfiable`, `A = 65536`) cannot reach.

Three things are certified at once, and none of them pins a numeral to `δ₀`.

* **The K-gate closes with EQUALITY.**  `G_gateK` is `64·(2²M) = 256M ≤ (1/12)(3072M)
  = 256M`, so `G = 768·Jb²M` remains the smallest admissible base at this `η`, exactly as in
  the landed frame.  The re-pin's whole cost to the ladder is this one linear factor, and it
  rides `M` rather than a numeral.
* **The anchor pays only a logarithm, and pays it uniformly.**  `A_gate_logK` is
  `16(log 4M + log e₂) ≤ (1/24)(A log 2 − 1)`; both logarithms are bounded by base-2
  exponents (`log_four_M_door`, `log_calE_door_two`), giving `(48L + 592) log 2` on the left
  against `(1/24)(262144(L+1) log 2 − 1)` on the right, `L := ⌊log₂ M⌋`.  The margin is ~18×
  at `L = 0` and widens to ~227× — the `(L+1)` factor inside `Adoor` is precisely what turns
  the fixed-`A` overflow into headroom that grows with the demand.
* **The K-3 width survives the reparametrisation.**  `H1_pin` holds with EQUALITY at
  `H₁ = P₁^{1/6}` and `H1_two` from `P₁ ≥ 64`, both symbolic in `A = Adoor M`.

`P₁ = 2^{Adoor M}` is never evaluated — it stays the symbol `calP (Adoor M) (3072 * M) 1`
throughout, and `X_d = calQK (Adoor M) (3072 * M) M 2` stays a symbol as well. -/
theorem calFrameK_satisfiable_door (M : ℕ) (hM : 1 ≤ M) :
    CalFrameK (1 / 12) (((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6))
      (Adoor M) (3072 * M) M 2 (calQK (Adoor M) (3072 * M) M 2) := by
  have hL0 : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) := Nat.cast_nonneg _
  have hL0' : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) * Real.log 2 :=
    mul_nonneg hL0 (Real.log_nonneg (by norm_num))
  -- `P₁ ≥ 64`, symbolically (the exponent is never expanded)
  have h64 : (64 : ℕ) ≤ calP (Adoor M) (3072 * M) 1 := by
    have hE : (6 : ℕ) ≤ calE (Adoor M) (3072 * M) 1 := by
      rw [calE_one]
      exact le_trans (by norm_num) (Adoor_ge M)
    have h6 : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [calP, h6]
    exact Nat.pow_le_pow_right (by norm_num) hE
  have h64R : (64 : ℝ) ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by exact_mod_cast h64
  have hP1pos : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  refine
    { eta_pos := by norm_num, eta_lt := by norm_num, one_le_Jb := by norm_num,
      one_le_G := by omega, one_le_M := hM, G_gateK := by push_cast; linarith,
      A_gate_lin := ?_, A_gate_logK := ?_, A_floor := le_trans (by norm_num) (Adoor_ge M),
      H1_two := ?_, H1_pin := ?_, Q_le_Xd := le_rfl }
  · -- `A_gate_lin`: `2Jb = 4 ≤ 2^18 ≤ Adoor M`
    rw [Adoor_cast]
    push_cast
    linarith
  · -- `A_gate_logK`: `16(log 4M + log e₂) ≤ (1/24)(Adoor M · log 2 − 1)`, uniformly in `M`
    push_cast
    rw [Adoor_cast]
    refine le_trans (mul_le_mul_of_nonneg_left
      (add_le_add (log_four_M_door hM) (log_calE_door_two hM)) (by norm_num)) ?_
    linarith [Real.log_two_gt_d9, hL0, hL0']
  · -- `H1_two`: `2 = 64^{1/6} ≤ P₁^{1/6}`
    calc (2 : ℝ) = (64 : ℝ) ^ ((1 : ℝ) / 6) := by
          rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast 2 6,
            ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6) :=
          Real.rpow_le_rpow (by norm_num) h64R (by norm_num)
  · -- `H1_pin`: `(P₁^{1/6})³ = P₁^{1/2}` — equality, the largest width the frame allows
    have hid : ((((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) ^ (3 : ℕ))
        = ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) 3,
        ← Real.rpow_mul hP1pos.le, show (1 : ℝ) / 6 * ((3 : ℕ) : ℝ) = (1 : ℝ) / 2 by norm_num]
    rw [hid]

/-! ## §3 — what the door family inherits -/

/-- **The twelve `LevelGates` at the door family**, free from the frame
(`levelGates_calibratedK`).  At `Jb = 2` the range `Icc 2 2` is the single level `j = 2` —
the truncation license of ⟦AMENDMENT A⟧ (our `thm_A2′` is stated at the K-family's `Jb = 2`;
MRT's `J`-maximality is their proof device, not an obligation of the port). -/
theorem levelGates_calibrated_door (M : ℕ) (hM : 1 ≤ M) :
    ∀ j ∈ Finset.Icc 2 2,
      LevelGates (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M)
        (calH ((((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)))) (1 / 12)
        ((calP (Adoor M) (3072 * M)) 1) (calQK (Adoor M) (3072 * M) M 2) j :=
  levelGates_calibratedK (calFrameK_satisfiable_door M hM)

/-- **MR eq (28) at the door family** (`eq28_clears_of_M` composed).  For ANY `δ > 0` with
`8/δ ≤ M`, the small-`h` accounting clears — `δ` stays a variable and `M` stays a variable,
so the door's `δ₀` and MR Lemma 2.2's constant `C` enter only at the instantiation site
(the MARGIN-HYGIENE LAW: no numeral here is a function of `δ₀`). -/
theorem eq28_door_clears {M : ℕ} (hM : 1 ≤ M) (Jb : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hMδ : 8 / δ ≤ (M : ℝ)) :
    δ / 50 + (2 + 1 / 50) * ∑ j ∈ Finset.Icc 1 Jb,
        Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
          / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ)
      ≤ δ :=
  eq28_clears_of_M (one_le_Adoor M) (by omega) hM Jb hδ hMδ

/-- **The level-1 containment arm** `log Q₁ = M·A·log 2` (`calE_one`).  MRT A.2 / MR Thm 3
demand `[P₁,Q₁] ⊂ [1,h]`, i.e. `Q₁ ≤ h`; ⟦AMENDMENT A⟧'s correction is that this is the
LEVEL-1 statement, not the top-block one, so the new floor arm is
`log h ≥ M · Adoor M · log 2` and `H_K := ⌈exp(M·Adoor M·log 2)⌉₊`-shaped. -/
lemma log_calQK_door_one (M : ℕ) :
    Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)
      = (M : ℝ) * ((Adoor M : ℕ) : ℝ) * Real.log 2 := by
  rw [log_calQK, calE_one]
  push_cast
  ring

end Salt.MR
