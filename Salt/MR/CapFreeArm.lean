/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SeamNumber

/-!
# `CapFreeArm` — THE CAP-FREE (large-`M`) ARM of the seam station

The landed §8.3 ladder (`USetGradedPrice` → `CaseASocket` → `GradedCapstone` →
`SeamCalibrationK` → `SeamNumber`) runs under the ROW CAP

  `hrow : 𝔻²(ℓg, p^{it₁}; X) ≤ (1/16)·loglog X`,

which is what `CofactorDist.pocket_collision_window` consumes to pin the CASE-B pocket centre
`t₁'` to within `1` of the row centre `t₁`.  The large-`M` arm has no such cap.  This file
supplies the OTHER half of the dichotomy, and does it without duplicating the ladder.

## THE COLLISION-AS-SOCKET PATTERN

Instead of two ladders there is ONE, parameterised over a single socket

  `PocketSocket g P Q X θ t₁ :=
     ∀ x ∈ [0,1], ∀ t₁', |t₁'| ≤ X → 𝔻²(ℓ(g_x), p^{it₁'}; X) ≤ (1/32 − θ)loglog X
        → |t₁' − t₁| < 1`

— exactly the conclusion the landed CASE-B branch reads off `pocket_collision_window`, and
nothing more.  The socket has TWO suppliers:

* **the cap branch** (`pocketSocket_of_row`): `hrow` + `collisionGate` + the §8.3 endpoint
  pins, i.e. `pocket_collision_window` verbatim.  Re-deriving the landed chain.
* **the cap-free branch** (`pocketSocket_of_floor`): a genuine large-`M` DATUM floor
  (`CapFreeFloor`) makes the socket's ANTECEDENT FALSE, so the socket holds VACUOUSLY at
  EVERY `t₁` — in particular at `t₁ := 0`, where the ball leg vanishes by emptiness
  (`ball_leg_vacuous_at_zero`).

## THE FLOOR, AND WHY THE `θ` CANCELS

`CapFreeFloor g X` asks `(1/32)loglog X + 25 < 𝔻²(ℓg, p^{iv}; X)` on the whole box
`|v| ≤ X`, at the BARE datum.  The damping costs at most the §8.3 block-window mass
(`RamWeight.gxDatum_pretDistSq_costwist`), which `CofactorDist.blockWindow_mertens_pin` pins
at `θ·loglog X + 25`; so the damped datum still exceeds `(1/32 − θ)loglog X` — **the `θ`
cancels exactly** — and no pocket can exist at any damping (`no_pocket_of_floor`).

The floor is supplied at the honest large-`M` value by `capFreeFloor_of_row_floor`: a
uniform `(1/16)loglog X` floor plus the explicit threshold `800 < loglog X` (the gap is
`(1/16 − 1/32)loglog X − 25 = (1/32)loglog X − 25`, positive exactly past `loglog X = 800`).

**⚠ THE FRAME WARNING (flags 2026-07-27, trap T3).**  `CapFreeFloor` is a *datum
hypothesis*, never `¬hrow`: the station minimises the `t₀`-SHIFTED datum
(`HalaszHead.seamCoeff_trivial_dist_eq`) while `hrow` is stated at `t₁` BARE, so negating
`hrow` at the produced centre yields no uniform floor anywhere.  Nothing in this file
derives `CapFreeFloor` from a negation.

**⚠ THE BAN.**  The cap-free branch NEVER touches `SupStation`'s produced centre: `hSup`
discharges by emptiness at `t₁ := 0` (`ball_leg_vacuous_at_zero`).  Keeping the station's
centre walks into `FarArm`'s `(log X)²` inflation, and it is avoidable by construction.
No `SupStation`/`FarArm` name occurs below.

## THE BOX GATE (S10)

`USetGradedPrice.pocket_transport_pin2` reports its pocket inside `|t₁'| ≤ 3X`, while the
floor lives on `|v| ≤ X`.  `box_gate_le_X` tightens the contour gate to
`|t| + T*₂(M, log M) ≤ X` and reports `|t₁'| ≤ X`, so the socket's antecedent and the
floor's box are the SAME box.  No landed statement widens.

## `X`-FREEDOM (Amendment C, trap 7 — the dilated-scales coupling)

Every stone below takes `X` as a FREE parameter, so Route III may instantiate the whole
chain at the dilated scales `X/d`.  Audited: `no_pocket_of_floor`, `box_gate_le_X`,
`PocketSocket`, both suppliers and `cofactor_Rbd34_local_nocap` carry `X` as a bound
variable with no pin.  (The `§8.3`-pinned stones downstream — everything at `theta293` /
`H83 X theta293` — pin `θ`, never `X`.)

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §8.3 pp. 27–29;
`docs/exploration/s8-freeze-0727.md` ⟦AMENDMENT B⟧ (A2-3b) and ⟦AMENDMENT C⟧ (trap 7);
`docs/blueprints/flags.md` 2026-07-27 (KC-A23B).
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators
open Finset MeasureTheory

/-! ## §1 (S1) — the `ellLin` transparency of `pretDistSq` -/

/-- **S1 — `𝔻²` DOES NOT SEE `ellLin`.**  `pretDistSq` is a sum over PRIMES only
(`Dist.pretDistSq`), and `ellLin` is the identity at primes
(`HalaszLambda.ellLin_apply_prime`); so the linearised datum and the bare datum have the same
pretentious distance to every target.

This is what lets a floor stated on the BARE datum `g` plug the slot the ladder states on
`ellLin g` — without it `lambda_nonpret`'s floor cannot reach the pocket. -/
theorem pretDistSq_ellLin_eq (g w : ℕ → ℂ) (X : ℝ) :
    pretDistSq (ellLin g) w X = pretDistSq g w X :=
  pretDistSq_congr_primes (fun _ hp => ellLin_apply_prime g hp) X

/-! ## §2 (S2) — the large-`M` floor kills every pocket, at every damping -/

/-- **THE CAP-FREE DATUM FLOOR.**  The large-`M` arm's hypothesis: on the whole contour box
`|v| ≤ X` the BARE datum stays strictly above `(1/32)loglog X + 25`.

Stated with a STRICT `<` on purpose.  The damping price and the floor's own `25` cancel
exactly (see `no_pocket_of_floor`), so at the non-strict form the pocket's cap
`≤ (1/32 − θ)loglog X` and the transported floor `≥ (1/32 − θ)loglog X` would meet rather
than contradict.  `capFreeFloor_of_row_floor` supplies the strict form from the honest
`(1/16)loglog X` datum floor with room to spare. -/
def CapFreeFloor (g : ℕ → ℂ) (X : ℝ) : Prop :=
  ∀ v : ℝ, |v| ≤ X →
    (1 / 32) * Real.log (Real.log X) + 25 < pretDistSq g (costwist v) X

/-- **The floor at the honest large-`M` value.**  A uniform `(1/16)loglog X` floor on the box
gives `CapFreeFloor` as soon as `800 < loglog X`: the gap is
`(1/16 − 1/32)loglog X − 25 = (1/32)loglog X − 25`, which is positive exactly past
`loglog X = 800`.  The threshold is carried EXPLICITLY (law #253: no hidden `X₀`). -/
theorem capFreeFloor_of_row_floor {g : ℕ → ℂ} {X : ℝ} (hLL : 800 < Real.log (Real.log X))
    (hfl : ∀ v : ℝ, |v| ≤ X →
      (1 / 16) * Real.log (Real.log X) ≤ pretDistSq g (costwist v) X) :
    CapFreeFloor g X := by
  intro v hv
  have h := hfl v hv
  linarith

/-- **S2 — NO POCKET AT ANY DAMPING.**  Under the bare-datum floor, the damped datum
`ℓ(g_x)` stays strictly above the pocket's cap `(1/32 − θ)loglog X` at every `x ∈ [0,1]` and
every `v` in the box.

The arithmetic, in one line: `RamWeight.gxDatum_pretDistSq_costwist` says the damping costs
at most the block-window mass; `CofactorDist.blockWindow_mertens_pin` pins that mass at
`θ·loglog X + 25`; so

  `𝔻²(ℓ(g_x), p^{iv}; X) ≥ 𝔻²(ℓg, p^{iv}; X) − (θ·loglog X + 25)
                          > (1/32)loglog X + 25 − θ·loglog X − 25 = (1/32 − θ)loglog X`

— **the `θ` cancels exactly**, and so does the `25`.  `pretDistSq_ellLin_eq` (S1) is what
moves the floor from the bare `g` onto `ℓg`. -/
theorem no_pocket_of_floor {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (P Q : ℕ)
    {X θ x v : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hθ0 : 0 < θ) (hθ32 : θ ≤ 1 / 32)
    (hLX : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X θ ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q)
    (hfloor : CapFreeFloor g X) (hv : |v| ≤ X) :
    ¬ (pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) X
        ≤ (1 / 32 - θ) * Real.log (Real.log X)) := by
  intro hpock
  have hdamp := gxDatum_pretDistSq_costwist (g := g) (P := P) (Q := Q) (x := x) (X := X)
    (t := v) hx0 hx1 hg
  have hwin := blockWindow_mertens_pin P Q X θ hθ0 (by linarith) hLX hPlow hQhigh hPQ
  have hbare : (1 / 32) * Real.log (Real.log X) + 25
      < pretDistSq (ellLin g) (costwist v) X := by
    rw [pretDistSq_ellLin_eq]
    exact hfloor v hv
  linarith

/-! ## §3 (S10) — the box gate: the pocket lands inside `|t₁'| ≤ X` -/

/-- **S10 — THE TIGHTENED CONTOUR BOX.**  `USetGradedPrice.pocket_transport_pin2` with its
contour gate sharpened from `|t| + T*₂(M, log M) ≤ 3X` to `≤ X`, so that CASE B reports its
pocket centre inside `|t₁'| ≤ X` rather than `≤ 3X`.

That is the box the cap-free floor lives on, so with this gate the ladder's `by_cases` is
EXHAUSTIVE against `CapFreeFloor`.  The landed statement is untouched: this is a strictly
stronger hypothesis giving a strictly stronger conclusion, derived from it. -/
theorem box_gate_le_X {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (P Q : ℕ)
    {k₀ M : ℕ} {X θ t x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hk₀pin : pin2Gate ≤ (k₀ : ℝ)) (hMX : (M : ℝ) ≤ X)
    (hTM : |t| + Tstar2 (M : ℝ) (Real.log (M : ℝ)) ≤ X) :
    (∀ k : ℕ, k₀ ≤ k → k ≤ M → ∀ v : ℝ, |v - t| ≤ Tstar2 (k : ℝ) (Real.log (k : ℝ)) →
        cofactorMfl X θ (k₀ : ℝ)
          ≤ pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) (k : ℝ))
      ∨ (∃ t₁' : ℝ, |t - t₁'| ≤ Tstar2 (M : ℝ) (Real.log (M : ℝ)) ∧ |t₁'| ≤ X ∧
          pretDistSq (ellLin (gxDatum g P Q x)) (costwist t₁') X
            ≤ (1 / 32 - θ) * Real.log (Real.log X)) := by
  have hX0 : (0 : ℝ) ≤ X := le_trans (Nat.cast_nonneg M) hMX
  have hTM3 : |t| + Tstar2 (M : ℝ) (Real.log (M : ℝ)) ≤ 3 * X := by linarith
  rcases pocket_transport_pin2 hg P Q hx0 hx1 hk₀pin hMX hTM3 with hA | hB
  · exact Or.inl hA
  · obtain ⟨t₁', hRmax, -, hpock⟩ := hB
    refine Or.inr ⟨t₁', hRmax, ?_, hpock⟩
    have h1 : |t₁'| ≤ |t| + |t - t₁'| := by
      have h := abs_add_le t (t₁' - t)
      rw [show t + (t₁' - t) = t₁' by ring, abs_sub_comm t₁' t] at h
      exact h
    linarith

/-! ## §4 — THE SOCKET, and its two suppliers -/

/-- **THE COLLISION SOCKET.**  Everything the ladder's CASE-B branch reads off the collision
page: a pocket centre in the box, at the pocket's own cap, is within `1` of `t₁`.

One socket, one ladder, two suppliers — `pocketSocket_of_row` (the landed cap branch) and
`pocketSocket_of_floor` (the cap-free branch, VACUOUSLY). -/
def PocketSocket (g : ℕ → ℂ) (P Q : ℕ) (X θ t₁ : ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ t₁' : ℝ, |t₁'| ≤ X →
    pretDistSq (ellLin (gxDatum g P Q x)) (costwist t₁') X
        ≤ (1 / 32 - θ) * Real.log (Real.log X) →
    |t₁' - t₁| < 1

/-- **SUPPLIER 1 — THE CAP BRANCH.**  `CofactorDist.pocket_collision_window` read as a
socket: the row cap `hrow` at the centre `t₁`, the named gate `collisionGate X 25 C`, and the
§8.3 endpoint pins.  The box narrows from `3X` to `X` on the way in (`X ≥ 0` from
`e ≤ X`), which only makes the hypothesis easier to meet.

⚠ THE TWO `(1/16)`-CAPS (flags 2026-07-27, T2): `hrow` here is the ROW cap, at the row's own
centre `t₁` and the global scale `X`.  It is NOT the A-10 station cap `hMcap`; this file
touches only `hrow`'s chain. -/
theorem pocketSocket_of_row :
    ∃ C : ℝ, ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → ∀ (P Q : ℕ) (X θ t₁ : ℝ),
      Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 0 < θ → θ ≤ 1 / 32 →
      P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
      pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
      collisionGate X 25 C →
      PocketSocket g P Q X θ t₁ := by
  obtain ⟨C, hC⟩ := pocket_collision_window
  refine ⟨C, ?_⟩
  intro g hg P Q X θ t₁ hX hLX hθ0 hθ32 hPlow hQhigh hPQ ht₁ hrow hgate x hx0 hx1 t₁' ht₁'
    hpock
  have hX0 : (0 : ℝ) ≤ X := le_trans (le_of_lt (Real.exp_pos 1)) hX
  exact hC g hg P Q X x θ t₁ t₁' hX hLX hθ0 hθ32 hx0 hx1 hPlow hQhigh hPQ ht₁
    (by linarith) hrow hpock hgate

/-- **SUPPLIER 2 — THE CAP-FREE BRANCH, VACUOUSLY.**  Under `CapFreeFloor` the socket's
ANTECEDENT is false (S2), so the socket holds at EVERY centre `t₁` — no cap, no collision
page, no gate `collisionGate`, and no constant `C`.

This is the whole content of the cap-free arm: the large-`M` datum floor does not *beat* the
collision, it *removes the case*. -/
theorem pocketSocket_of_floor {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) {P Q : ℕ}
    {X θ : ℝ} (hθ0 : 0 < θ) (hθ32 : θ ≤ 1 / 32) (hLX : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X θ ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q)
    (hfloor : CapFreeFloor g X) (t₁ : ℝ) :
    PocketSocket g P Q X θ t₁ := by
  intro x hx0 hx1 t₁' ht₁' hpock
  exact absurd hpock
    (no_pocket_of_floor hg P Q hx0 hx1 hθ0 hθ32 hLX hPlow hQhigh hPQ hfloor ht₁')

/-! ## §5 (S8) — the ball leg VANISHES at `t₁ := 0` -/

/-- **S8 — THE BALL LEG IS VACUOUS AT THE ORIGIN.**  At `t₁ := 0` the seam ball misses the
seam annulus entirely (`SeamSplit`'s `seamRad X < seamT0 X`, i.e.
`CenterCore.seamRad_lt_seamT0`), so
`CenterCore.seamAnn_inter_seamBall_eq_empty` applies and
`SeamGate.seam_sup_binder_of_inter_empty` discharges the row's `hSup` binder at `S := 0`.

Consequence: on the cap-free branch the seam row's fourth summand `8·S²` is **ZERO**, and
the row never needs a produced centre.  ⚠ THE BAN: this is what keeps the cap-free arm off
`SupStation`'s centre and out of `FarArm`'s `(log X)²` inflation. -/
theorem ball_leg_vacuous_at_zero {N : ℕ} {a : ℕ → ℂ} {X T : ℝ} (hL : 1 < Real.log X) :
    ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - 0| ≤ seamRad X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ 0 * m / (1 + |t - 0|) := by
  refine seam_sup_binder_of_inter_empty (N := N) (a := a) (T := T) (S := 0) ?_
  refine seamAnn_inter_seamBall_eq_empty ?_
  have h := seamRad_lt_seamT0 hL
  rw [abs_zero]
  linarith

/-! ## §6 (S3) — the co-factor bound, SOCKETED -/

/-- **S3 — THE CO-FACTOR `Rbd` AT THE SOCKET** (`cofactor_Rbd34_local_nocap`).
`USetGradedPrice.cofactor_Rbd34_local` with the collision page lifted out into the socket.

**THE HYPOTHESIS DIFF versus `cofactor_Rbd34_local`.**

*Removed.*  `|t₁| ≤ X`, the row cap `hrow`, `collisionGate X 25 C` — and with them the
existential constant `C` and the five §8.3 endpoint pins (`e ≤ X`, `e ≤ log X`, `0 < θ`,
`θ ≤ 1/32`, `P₈₃ ≤ P`, `Q ≤ Q₈₃`, `P ≤ Q`) that fed the collision and nothing else.  They
reappear at the SUPPLY site (`pocketSocket_of_row` / `pocketSocket_of_floor`), which is the
point of the pattern.

*Added.*  `PocketSocket g P Q X θ t₁`.

*Tightened.*  The contour gate `|t| + T*₂(M, log M) ≤ X` (S10) in place of `≤ 3X`, so the
pocket lands in the socket's box.

*Kept verbatim.*  The seven window-geometry binders, `M ≤ X`, the loglog charge `hgate32`,
the far-leg lower gate `0 < R` and `R ≤ |t − t₁|`, the CASE-A socket, the half-open endpoint
charge `hend`, and the EXIT EXPRESSION — `cofactorRbd34loc`'s `max` is untouched (T7: byte
identity with `hCqgate` downstream). -/
theorem cofactor_Rbd34_local_nocap {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1)
    (H : ℝ) (N Xn P Q j M k₀ : ℕ) (c Cb X θ t t₁ R : ℝ)
    (hc1 : 2 * c < 1) (hCb0 : 0 ≤ Cb)
    (hk₀th : ballQuarterThreshold ≤ (k₀ : ℝ))
    (hMN : M ≤ N) (hk₀lo : (k₀ : ℝ) < ramRbot H Xn j)
    (hk₀hi : ramRbot H Xn j ≤ (k₀ : ℝ) + 1) (hbot : 1 < ramRbot H Xn j)
    (hlow : ramRbot H Xn j - 1 ≤ (M : ℝ)) (hhigh : (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1))
    (hMtop : 2 * ramRbot H Xn j < (M : ℝ) + 3) (hMX : (M : ℝ) ≤ X)
    (hTM : |t| + Tstar2 (M : ℝ) (Real.log (M : ℝ)) ≤ X)
    (hgate32 : 18 + Real.log (Real.log X) - Real.log (Real.log (k₀ : ℝ))
      ≤ 32 * θ * Real.log (Real.log X))
    (hR0 : 0 < R) (hfar : R ≤ |t - t₁|)
    (hsock : PocketSocket g P Q X θ t₁)
    (hA2 : CaseASocket2 g P Q c Cb X θ k₀ M t)
    (hend : 2 / ramRbot H Xn j
      ≤ cofactorRbd34loc c Cb X θ (k₀ : ℝ) (M : ℝ)
          (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R / 3) :
    ‖ramR H N Xn P Q j (ellLin g) t‖
      ≤ cofactorRbd34loc c Cb X θ (k₀ : ℝ) (M : ℝ)
          (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R := by
  have hk₀3R : (3 : ℝ) ≤ (k₀ : ℝ) := le_trans three_le_ballQuarterThreshold hk₀th
  have hk₀1 : (1 : ℝ) ≤ (k₀ : ℝ) := by linarith
  have hk₀pin : pin2Gate ≤ (k₀ : ℝ) := le_trans pin2Gate_le_ballQuarterThreshold hk₀th
  set S : ℝ := max (2 * caseAS2 c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ))
    (farSupS34 (k₀ : ℝ) (M : ℝ) (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R) with hS
  have hSA : 2 * caseAS2 c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) ≤ S := le_max_left _ _
  have hSB : farSupS34 (k₀ : ℝ) (M : ℝ) (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R ≤ S :=
    le_max_right _ _
  have hRbdS : cofactorRbd34loc c Cb X θ (k₀ : ℝ) (M : ℝ)
      (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R = 3 * S := rfl
  have hendS : 2 / ramRbot H Xn j ≤ S := by
    rw [hRbdS] at hend; linarith
  rw [hRbdS]
  refine ramR_abel_sup (fun n => ellLin_norm_le_one g hg n) hbot hlow hhigh hMtop hendS ?_
  intro m hm
  refine spolyA_ramRcoeff_le_of_damp ?_
  intro x hx
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rcases box_gate_le_X hg P Q hx.1 hx.2 hk₀pin hMX hTM with hA | hB
  · -- CASE A at this `x` — the socket, at the `y₂` window floor
    have hk₀M : k₀ ≤ M := by
      have hk₀MR : (k₀ : ℝ) ≤ (M : ℝ) := by linarith
      exact_mod_cast hk₀MR
    have hS0 : (0 : ℝ) ≤ caseAS2 c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) :=
      caseAS2_nonneg hc1 hCb0 hk₀1
    have hbd := caseA_damped_partial (g := g) (H := H) (N := N) (Xn := Xn) (P := P) (Q := Q)
      (j := j) (M := M) (k₀ := k₀) (x := x) (t := t) hS0 hMN hk₀M hk₀lo hk₀hi hhigh
      (hA2 x hx.1 hx.2 hA) m hm
    have hmul : 2 * caseAS2 c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) * (m : ℝ) ≤ S * (m : ℝ) :=
      mul_le_mul_of_nonneg_right hSA hm0
    linarith
  · -- CASE B at this `x` — the pocket is in the socket's box, so the socket collides it
    obtain ⟨t₁', hRmax, ht₁'abs, hpock⟩ := hB
    have hcoll := hsock x hx.1 hx.2 t₁' ht₁'abs hpock
    have hRle : R ≤ 1 + |t - t₁'| := by
      have := pocket_far_from_ball hcoll hfar
      linarith
    have hbd := damped_partial_transfer_34 hg hx.1 hx.2 hk₀th hMN hk₀lo hk₀hi hhigh hMX
      hgate32 hpock hR0 hRle hRmax m hm
    have hmul : farSupS34 (k₀ : ℝ) (M : ℝ) (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R * (m : ℝ)
        ≤ S * (m : ℝ) := mul_le_mul_of_nonneg_right hSB hm0
    linarith

/-! ## §7 (S4) — the `𝒯_L` exit, SOCKETED -/

/-- **S4 — THE `𝒯_L` EXIT AT THE SOCKET** (`tL_supply_discharged34_local_nocap`).
`USetGradedPrice.tL_supply_discharged34_local` with its co-factor supply taken from S3.
Same diff as S3: the three collision inputs and the five endpoint pins are gone (with the
constant `C`), the socket is in, and the per-`t` contour gate is the tightened
`|t| + T*₂(M, log M) ≤ Xg`. -/
theorem tL_supply_discharged34_local_nocap :
    ∃ Cq cq T₀ : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (H : ℝ), 2 ≤ H → ∀ (P Q j N Xn M k₀ : ℕ) (cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      H ≤ (j : ℝ) →
      ∀ (T V L δ' : ℝ) (𝒯 : Finset ℝ), WellSpaced 𝒯 →
      (∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) → T₀ ≤ T → 1 < T →
      3 ≤ ramQbase H P j → (ramQbase H P j : ℝ) ≤ T →
      30 ≤ Real.log T / Real.log (ramQbase H P j) →
      5 ≤ Real.log (Real.log T) → 1 ≤ V → V⁻¹ ≤ δ' →
      Real.log T ≤ L → 1 ≤ Real.log T → Real.exp 1 ≤ L →
      Real.log (ramQbase H P j) ≤ L → Real.log V ≤ 100 * Real.log L →
      420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cq * (Real.log (ramQbase H P j)) ^ 2 →
      ∀ (c Cb Xg θ t₁ R : ℝ),
        2 * c < 1 → 0 ≤ Cb → ballQuarterThreshold ≤ (k₀ : ℝ) →
        M ≤ N → (k₀ : ℝ) < ramRbot H Xn j → ramRbot H Xn j ≤ (k₀ : ℝ) + 1 →
        1 < ramRbot H Xn j → ramRbot H Xn j - 1 ≤ (M : ℝ) →
        (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1) → 2 * ramRbot H Xn j < (M : ℝ) + 3 →
        (M : ℝ) ≤ Xg →
        18 + Real.log (Real.log Xg) - Real.log (Real.log (k₀ : ℝ))
          ≤ 32 * θ * Real.log (Real.log Xg) →
        0 < R →
        PocketSocket g P Q Xg θ t₁ →
        (∀ t : ℝ, CaseASocket2 g P Q c Cb Xg θ k₀ M t) →
        2 / ramRbot H Xn j
          ≤ cofactorRbd34loc c Cb Xg θ (k₀ : ℝ) (M : ℝ)
              (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R / 3 →
        (∀ t ∈ tLset H P Q j cf δ' 𝒯, R ≤ |t - t₁| ∧
          |t| + Tstar2 (M : ℝ) (Real.log (M : ℝ)) ≤ Xg) →
        ∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N Xn P Q (ellLin g) cf j t‖ ^ 2
          ≤ 54 * Cq * cofactorRbd34loc c Cb Xg θ (k₀ : ℝ) (M : ℝ)
                (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R ^ 2
              * (H / (j : ℝ)) ^ 2 := by
  obtain ⟨Cq, cq, T₀, hCq, hcq, hT₀, htL⟩ := tL_main_sumsq
  refine ⟨Cq, cq, T₀, hCq, hcq, hT₀, ?_⟩
  intro g hg H hH P Q j N Xn M k₀ cf hcf1 hHj T V L δ' 𝒯 hws hsub hT₀T hT hB3 hBT hκ30 hLL5
    hV1 hVδ hTL hlogT1 hLe hWL hlogV hkill c Cb Xg θ t₁ R hc1 hCb0 hk₀th hMN hk₀lo hk₀hi
    hbot hlow hhigh hMtop hMX hgate32 hR0 hsock hA2 hend hper
  have hk₀1 : (1 : ℝ) ≤ (k₀ : ℝ) := by
    have := le_trans three_le_ballQuarterThreshold hk₀th
    linarith
  refine htL H hH P Q j N Xn cf (ellLin g) hcf1 hHj T V L δ'
    (cofactorRbd34loc c Cb Xg θ (k₀ : ℝ) (M : ℝ) (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R)
    𝒯 hws hsub hT₀T hT hB3 hBT hκ30 hLL5 hV1 hVδ hTL hlogT1 hLe hWL hlogV hkill
    (cofactorRbd34loc_nonneg hc1 hCb0 hk₀1) ?_
  intro t ht
  obtain ⟨hfar, hTM⟩ := hper t ht
  exact cofactor_Rbd34_local_nocap hg H N Xn P Q j M k₀ c Cb Xg θ t t₁ R hc1 hCb0 hk₀th hMN
    hk₀lo hk₀hi hbot hlow hhigh hMtop hMX hTM hgate32 hR0 hfar hsock (hA2 t) hend

/-! ## §8 (S5) — the graded `hU` supply, SOCKETED -/

/-- **S5 — THE GRADED `hU` SUPPLY AT THE SOCKET** (`hUG34_supplied_nocap`).
`USetGradedPrice.hUG34_supplied` with its `𝒯_L` feed taken from S4.  The `𝒯_S` half is
verbatim (`TSG_feed_of_thin`), the far-leg geometry is derived exactly as in the landed twin
(`Rrad ≤ seamRad X` plus `t ∉ ball`), and the contour box is the tightened one,
`|t| + T*₂(M_j, log M_j) ≤ X`.

Diff versus the landed twin: `|t₁| ≤ X`, `hrow`, `collisionGate X 25 C` and the endpoint
pins `e ≤ X`, `e ≤ log X`, `0 < θ`, `θ ≤ 1/32`, `P₈₃ ≤ P`, `Q ≤ Q₈₃`, `P ≤ Q` are gone (with
the constant `C`); `PocketSocket g P Q X θ t₁` is in; the box gate is `≤ X`. -/
theorem hUG34_supplied_nocap :
    ∃ Cq cq T₀ : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧
      ∀ (g fb a cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖fb n‖ ≤ 1) →
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq Ms Mt kk : ℕ → ℕ)
        (Hseq αseq : ℕ → ℝ),
      ∀ (X Tann t₁ δ' V VJ L η cg Cb θ Rrad KS Rbar E : ℝ),
        0 < X → TannGate X Tann → 1 < Tann → Tann ≤ X →
        1 < (Qseq Jb : ℝ) → Real.log (Qseq Jb) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        1 ≤ Jb → Jb ≤ Jset → 2 ≤ Hseq Jb → 0 ≤ αseq Jb →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ Tann →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
        αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 →
        (∀ j : ℕ, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j : ℕ, thinBundleG Tann VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        2 * cg < 1 → 0 ≤ Cb →
        0 < Rrad → Rrad ≤ seamRad X →
        PocketSocket g P Q X θ t₁ →
        (∀ j ∈ ramI H P Q, TLBlockGates34 cq H P N Xd Mt kk Tann L cg Cb X θ Rrad j) →
        (∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ X) →
        (∀ j ∈ ramI H P Q, ∀ t : ℝ, CaseASocket2 g P Q cg Cb X θ (kk j) (Mt j) t) →
        (∀ j ∈ ramI H P Q, 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
            * (∑ m ∈ Finset.Icc 1 (Ms j),
                ‖ramRcoeff H N Xd P Q j (ellLin g) m‖ ^ 2 / (m : ℝ) ^ 2) ≤ KS) →
        (∀ j ∈ ramI H P Q,
          cofactorRbd34loc cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
            (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ≤ Rbar) →
        2 ≤ ⌊H * Real.log (P : ℝ)⌋₊ →
        (∫ t in (-Tann)..Tann, ‖ramErr H N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset,
            ‖spoly N a t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (((ramI H P Q).card : ℝ) * KS
                  + 54 * Cq * Rbar ^ 2 * H ^ 2
                      / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E := by
  obtain ⟨Cq, cq, T₀, hCq, hcq, hT₀, hTL⟩ := tL_supply_discharged34_local_nocap
  refine ⟨Cq, cq, T₀, hCq, hcq, hT₀, ?_⟩
  intro g fb a cf hg hfb1 hcf1 H hH N Xd P Q Jset Jb Pseq Qseq Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η cg Cb θ Rrad KS Rbar E
    hX0 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hH2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hV1 hVδ hlogV
    hc1 hCb0 hR0 hRrad hsock hblk hbox hA2 hKS hRbdU hj₀ herr
  have hTann0 : (0 : ℝ) ≤ Tann := by linarith
  have hκ30 : 30 ≤ Real.log Tann / Real.log (Qseq Jb) :=
    kappa30_of_TannGate X Tann (Qseq Jb) hQ1 hQpin hTgate
  have hRsub : (seamAnn X Tann \ seamBall X t₁) ⊆ Set.Icc (-Tann) Tann :=
    fun _ ht => seamAnn_subset_Icc X Tann ht.1
  have hTSfeed := TSG_feed_of_thin fb hfb1 Pseq Qseq Hseq αseq Jset Jb hJb1 hJbJ hH2 hα0
    Tann VJ hT1 hP3 hPQ hQT hκ30 hLL5 hVJ η X hα hη2 hTX
    (seamAnn X Tann \ seamBall X t₁) hRsub H N Xd P Q (ellLin g) cf δ' Ms hMs hbudget
  have hTLj : ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 →
      (↑𝒯 : Set ℝ) ⊆ (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset →
      (∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N Xd P Q (ellLin g) cf j t‖ ^ 2)
        ≤ 54 * Cq * cofactorRbd34loc cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
            (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ^ 2
            * (H / (j : ℝ)) ^ 2 := by
    intro j hj 𝒯 hws h𝒯A
    obtain ⟨hHj, hB3, hBT, hκ30j, hWL, hkill, hk₀th, hMN, hk₀lo, hk₀hi, hbot, hlow, hhigh,
      hMtop, hMX, hgate32, hend⟩ := hblk j hj
    refine hTL g hg H hH P Q j N Xd (Mt j) (kk j) cf hcf1 hHj Tann V L δ' 𝒯 hws
      (fun t ht => hRsub (h𝒯A (Finset.mem_coe.mpr ht)).1) hT₀T hT1 hB3 hBT hκ30j hLL5 hV1 hVδ
      hTLle hlogT1 hLe hWL hlogV hkill cg Cb X θ t₁ Rrad hc1 hCb0 hk₀th hMN hk₀lo hk₀hi
      hbot hlow hhigh hMtop hMX hgate32 hR0 hsock (hA2 j hj) hend ?_
    intro t ht
    have ht𝒯 : t ∈ 𝒯 := tLset_subset H P Q j cf δ' 𝒯 ht
    have htA := h𝒯A (Finset.mem_coe.mpr ht𝒯)
    have hTabs : |t| ≤ Tann := htA.1.1.2
    have hnot : ¬ (|t - t₁| ≤ seamRad X) := htA.1.2
    exact ⟨le_trans hRrad (le_of_lt (not_le.mp hnot)), hbox j hj t hTabs⟩
  refine hUG_exit_of_branches H N Xd P Q a (ellLin g) cf fb Pseq Qseq Hseq αseq Jset
    X Tann t₁ E hTann0 herr δ'
    (fun j => 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
      * ∑ m ∈ Finset.Icc 1 (Ms j), ‖ramRcoeff H N Xd P Q j (ellLin g) m‖ ^ 2 / (m : ℝ) ^ 2)
    (fun j => 54 * Cq * cofactorRbd34loc cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
      (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ^ 2 * (H / (j : ℝ)) ^ 2)
    KS Cq Rbar (le_of_lt hCq) hj₀ (fun j _ 𝒯 hws h𝒯A => hTSfeed j 𝒯 hws h𝒯A) hTLj hKS ?_
  intro j hj
  obtain ⟨-, -, -, -, -, -, hk₀th, -, -, -, -, -, -, -, -, -, -⟩ := hblk j hj
  have hk₀1 : (1 : ℝ) ≤ ((kk j : ℕ) : ℝ) := by
    have := le_trans three_le_ballQuarterThreshold hk₀th
    linarith
  exact tL_block_weight Cq H _ Rbar j (le_of_lt hCq)
    (cofactorRbd34loc_nonneg hc1 hCb0 hk₀1) (hRbdU j hj)

/-! ## §9 (S6) — the graded station prize, SOCKETED -/

/-- **S6 — THE GRADED STATION PRIZE AT THE SOCKET** (`hUG34_fully_priced_nocap`).
`USetGradedPrice.hUG34_fully_priced` with its `𝒰`-integral taken from S5.  All four grade
slots are discharged exactly as in the landed twin (`KS_supplied`, `Rbd34loc_uniform`,
`Rbd34loc_grade_priced`, `balance_priced_main`/`rem_priced`); the radius pin `Rrad` still
rides in BOTH directions (⟦V6a⟧'s silent-vacuity catch).

Diff versus the landed twin: `|t₁| ≤ X`, `hrow` and `collisionGate X 25 C` are gone (with
the constant `C`); `PocketSocket g P Q X θ₂₉₃ t₁` is in; the contour box is `≤ X`.  The
§8.3 endpoint pins STAY — `P₈₃ ≤ P` feeds `floor_pin`, `Q ≤ Q₈₃` and `e ≤ log X` feed
`ramI_card_le_pin` — and they are exactly what `pocketSocket_of_floor` needs at the supply
site, so the cap-free instantiation adds no gate that is not already here. -/
theorem hUG34_fully_priced_nocap :
    ∃ Cq cq T₀ : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧
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
        (∀ j : ℕ, ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j : ℕ, thinBundleG Tann VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j : ℕ, 2 ≤ m₀ j) →
        (∀ j : ℕ, ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j : ℕ, ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        PocketSocket g P Q X theta293 t₁ →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ X) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ,
          CaseASocket2 g P Q (1 / Real.exp 1) Cb X theta293 (kk j) (Mt j) t) →
        2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                ∩ seamTtotG fb Pseq Qseq Hseq αseq Jset, ‖spoly N a t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, hCq, hcq, hT₀, hsup⟩ := hUG34_supplied_nocap
  refine ⟨Cq, cq, T₀, hCq, hcq, hT₀, ?_⟩
  intro g fb a cf hg hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hH2 hX0 _hXe hLXe hL4 hlX2 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow
    hblk hbox hA2 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hH0 : (0 : ℝ) ≤ H83 X theta293 := by linarith
  have hHeq : H83 X theta293 = (Real.log X) ^ theta293 := by rw [H83]
  have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hlog2T : (0 : ℝ) ≤ 1 + Real.log (2 * Tann) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * Tann by linarith)
    linarith
  have hKS0 : (0 : ℝ) ≤ 20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)) :=
    mul_nonneg (by positivity) hlog2T
  have hkmin1 : (1 : ℝ) < kmin := by linarith
  have hMt1 : ∀ j ∈ ramI (H83 X theta293) P Q, (1 : ℝ) ≤ ((Mt j : ℕ) : ℝ) := by
    intro j hj
    have h1 : (1 : ℝ) ≤ pin2Gate := Real.one_le_exp (by norm_num)
    exact le_trans h1 (hMtpin j hj)
  have hRbar0 : (0 : ℝ) ≤ cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 kmin Ymax
      (Tstar2 Ymax (Real.log Ymax)) Rrad :=
    cofactorRbd34loc_nonneg hc1 hCb0 (le_of_lt hkmin1)
  have hKSb := KS_supplied (H83 X theta293) N Xd P Q g hg m₀ Ms Tann δ' (le_of_lt hT1)
    hm₀2 hm₀ hMs hMs4
  have hRb := Rbd34loc_uniform (H83 X theta293) P Q Mt kk (1 / Real.exp 1) Cb X theta293
    Rrad kmin Ymax hc0 hc1 hCb0 hkmin1 hMtpin hkk hMt1 hMt
  have hRgrade := Rbd34loc_grade_priced (X := X) (Cb := Cb) (kmin := kmin) (Ymax := Ymax)
    (Rrad := Rrad) hCb0 hk2 hkX hlX2 hgateW hRlow hYpin hWY hXY hthr
  have hfl := floor_pin X P hL4 hPlow
  have hU := hsup g fb a cf hg hfb1 hcf1 (H83 X theta293) hH2 N Xd P Q Jset Jb Pseq Qseq
    Ms Mt kk Hseq αseq X Tann t₁ δ' V VJ L η (1 / Real.exp 1) Cb theta293 Rrad
    (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)))
    (cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 kmin Ymax
      (Tstar2 Ymax (Real.log Ymax)) Rrad) E
    hX0 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hV1 hVδ hlogV
    hc1 hCb0 hR0 hRrad hsock hblk hbox hA2 hKSb hRb hfl.1 herr
  have hmain := balance_priced_main X (H83 X theta293) Cq (gradeCR2 Cb)
    (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)))
    (cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 kmin Ymax
      (Tstar2 Ymax (Real.log Ymax)) Rrad) P Q hL0 hH0
    (ramI_card_le_pin X P Q hQ0 hQhigh hLXe) (le_of_eq hHeq) hfl.2
    (le_of_lt hCq) hKS0 hRbar0 hRgrade hKSgate hCqgate
  have hrem := rem_priced X Tann (H83 X theta293) ε EP2 E hL1 hX0 (by linarith)
    (le_of_eq hHeq.symm) habs hEP2 hErow
  have hbal := hUG_balance a fb N Pseq Qseq Hseq αseq Jset X Tann t₁ ε _ _ hε0 hL1 hX0
    hTgate hU hmain hrem
  exact prop_A3_T1_row_split_weightedG a N fb Pseq Qseq Hseq αseq Jset X Tann t₁ S _ hL0.le
    (by linarith) hX0 hXN hN2 hsupp hSup hbal

/-! ## §10 (S7) — the unconditional graded exit, SOCKETED, and its door reading -/

/-- **S7a — THE GRADED STATION PRIZE, UNCONDITIONAL, AT THE SOCKET**
(`hUG34_unconditional_nocap`).  S6 with its CASE-A socket discharged by
`CaseASocket.caseASocket2_discharged` — **which is already cap-free**, so it re-instantiates
VERBATIM: the transplant block (`ShortIntervalDatum Cb`, `X₀ ≤ kmin`,
`0 ≤ cofactorMfl X θ₂₉₃ kmin`) and the per-block discharge are the landed twin's, byte for
byte.  The COLLISION socket is what remains open, and it is what the two suppliers close. -/
theorem hUG34_unconditional_nocap :
    ∃ Cq cq T₀ X₀ : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
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
        (∀ j : ℕ, ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j : ℕ, thinBundleG Tann VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j : ℕ, 2 ≤ m₀ j) →
        (∀ j : ℕ, ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j : ℕ, ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        PocketSocket g P Q X theta293 t₁ →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ X) →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin →
        0 ≤ cofactorMfl X theta293 kmin →
        2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                ∩ seamTtotG fb Pseq Qseq Hseq αseq Jset, ‖spoly N a t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨X₀, hX₀0, hsockA⟩ := caseASocket2_discharged
  obtain ⟨Cq, cq, T₀, hCq, hcq, hT₀, hpriced⟩ := hUG34_fully_priced_nocap
  refine ⟨Cq, cq, T₀, X₀, hCq, hcq, hT₀, hX₀0, ?_⟩
  intro g fb a cf hg hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup
  have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have hA2 : ∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ,
      CaseASocket2 g P Q (1 / Real.exp 1) Cb X theta293 (kk j) (Mt j) t := by
    intro j hj t
    obtain ⟨-, -, -, -, -, -, hk₀th, -, hk₀lo, hk₀hi, -, -, hhigh, hMtop, -, -, -⟩ :=
      hblk j hj
    have hk₀pin : pin2Gate ≤ ((kk j : ℕ) : ℝ) :=
      le_trans pin2Gate_le_ballQuarterThreshold hk₀th
    have hk3 : (3 : ℝ) ≤ ((kk j : ℕ) : ℝ) := le_trans three_le_ballQuarterThreshold hk₀th
    have hkMR : ((kk j : ℕ) : ℝ) ≤ ((Mt j : ℕ) : ℝ) := by linarith
    have hkM : kk j ≤ Mt j := by exact_mod_cast hkMR
    have hM2k : ((Mt j : ℕ) : ℝ) ≤ 2 * ((kk j : ℕ) : ℝ) := by linarith
    have hX₀kk : X₀ ≤ ((kk j : ℕ) : ℝ) := le_trans hX₀k (hkk j hj)
    have hMflkk : (0 : ℝ) ≤ cofactorMfl X theta293 ((kk j : ℕ) : ℝ) :=
      le_trans hMfl0 (cofactorMfl_mono X theta293 (hkk j hj))
    exact hsockA g hg P Q (1 / Real.exp 1) Cb X theta293 (kk j) (Mt j) t hc0 le_rfl hc1
      hCb0 hCbound hX₀kk hk₀pin hkM hM2k hMflkk
  exact hpriced g fb a cf hg hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow
    hblk hbox hA2 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup

/-- **S7b — THE SOCKETED EXIT CLEARS THE DOOR** (`hUG34_unconditional_beats_door_nocap`).
S7a read through `USetPrice.priced_exit_beats_door`: at any `o(1)` with `ε ≤ 1/1000` the
third summand is `2(Tann/X + 1)(log X)^{−1/500}`, the door's floor `c₀ ≥ 1/500`, cleared at
the ratified margin `1.7067×` (`CofactorDist.exit_margin_293`).  One hypothesis added
(`ε ≤ 1/1000`), the exit exponent `−θ₂₉₃ + ε` replaced by `−1/500`; the first two summands
ride untouched. -/
theorem hUG34_unconditional_beats_door_nocap :
    ∃ Cq cq T₀ X₀ : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
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
        (∀ j : ℕ, ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j : ℕ, thinBundleG Tann VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j : ℕ, 2 ≤ m₀ j) →
        (∀ j : ℕ, ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j : ℕ, ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        PocketSocket g P Q X theta293 t₁ →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ X) →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin →
        0 ≤ cofactorMfl X theta293 kmin →
        2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → ε ≤ 1 / 1000 →
        8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                ∩ seamTtotG fb Pseq Qseq Hseq αseq Jset, ‖spoly N a t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-(1 : ℝ) / 500)) := by
  obtain ⟨Cq, cq, T₀, X₀, hCq, hcq, hT₀, hX₀0, huncond⟩ := hUG34_unconditional_nocap
  refine ⟨Cq, cq, T₀, X₀, hCq, hcq, hT₀, hX₀0, ?_⟩
  intro g fb a cf hg hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 hε1 habs hEP2 hErow herr hXN hN2 hsupp hSup
  exact priced_exit_beats_door X Tann ε _ _ _ hε1 (by linarith) hX0 hTgate
    (huncond g fb a cf hg hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk Hseq αseq
      X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
      hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
      hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hm₀2 hm₀ hMs4
      hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow
      hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
      hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup)

/-! ## §11 (S9) — the K-frame seam row, SOCKETED -/

set_option maxHeartbeats 1000000 in
-- `SeamCalibrationK.seam_row_calibratedK`'s own raise (:889): the same 23 ladder-reads and
-- the same two large predicate-blind applications, with the socket in place of the cap
/-- **S9a — THE SEAM ROW AT THE K-LADDER, SOCKETED** (`seam_row_calibratedK_nocap`).
`SeamCalibrationK.seam_row_calibratedK` with its `𝒰`-leg taken from S7a.  Every ladder-read
is the landed twin's, discharged from `CalFrameK` alone; the `𝒯`-leg
(`TLegExit.TLeg_feeds_capstone`) is predicate-blind and rides verbatim.

Diff: `|t₁| ≤ X`, `hrow`, `collisionGate X 25 Ccol` gone (with the constant `Ccol`);
`PocketSocket g P Q X θ₂₉₃ t₁` in; the contour box at `≤ X`. -/
theorem seam_row_calibratedK_nocap :
    ∃ Cq cq T₀ X₀ Cs : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        Real.exp 2 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j : ℕ, ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j : ℕ, thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j : ℕ, 2 ≤ m₀ j) →
        (∀ j : ℕ, ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j : ℕ, ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        PocketSocket g P Q X theta293 t₁ →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ X) →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin →
        0 ≤ cofactorMfl X theta293 kmin →
        2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
                  * (Tann * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
                  * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                      + 60 * (calH H1 1 / mrAlpha η 1)
                          * Real.exp (4 * mrAlpha η 1 / calH H1 1))
                + 1536 * Cs * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
                    * (1 / ((calP A G 1 : ℕ) : ℝ))
                + ∑ j ∈ Finset.Icc 1 Jb,
                    lemma12Rows N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann a b c)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, hCq, hcq, hT₀, hX₀0, hcap⟩ := hUG34_unconditional_nocap
  obtain ⟨Cs, hCs, hfeed⟩ := TLeg_feeds_capstone
  refine ⟨Cq, cq, T₀, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hwin
  have hη := hF.eta_pos
  have hη6 := hF.eta_lt
  have hJb1 := hF.one_le_Jb
  have hG1 := hF.one_le_G
  have hM1 := hF.one_le_M
  have hEJbN : 24 ≤ calE A G Jb := by
    have h := calE_mono A hG1 hJb1
    rw [calE_one] at h
    exact le_trans hF.A_floor h
  have hJbR : (1 : ℝ) ≤ (Jb : ℝ) := by exact_mod_cast hJb1
  have hKpos : 1 ≤ (Jb ^ 2 * M) * calE A G Jb :=
    Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hJb1) hM1) (by omega)
  have hQnat : 1 < calQK A G M Jb := by
    simp only [calQK]
    calc (1 : ℕ) < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ((Jb ^ 2 * M) * calE A G Jb) := Nat.pow_le_pow_right (by norm_num) hKpos
  have hQ1 : (1 : ℝ) < ((calQK A G M Jb : ℕ) : ℝ) := by exact_mod_cast hQnat
  have hQpos : (0 : ℝ) < ((calQK A G M Jb : ℕ) : ℝ) := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (by omega) hF.Q_le_Xd
  have hHb2 : (2 : ℝ) ≤ calH H1 Jb := by
    simp only [calH]; nlinarith [hF.H1_two]
  have hHb0 : (0 : ℝ) < calH H1 Jb := by linarith
  have hα0 : (0 : ℝ) ≤ mrAlpha η Jb := (mrAlpha_pos η hη hη6 hJb1).le
  have hP3 : 3 ≤ calP A G Jb := by
    simp only [calP]
    calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ calE A G Jb := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hPQ : calP A G Jb ≤ calQK A G M Jb := calP_le_calQK hM1 hJb1
  have hlogX0 : (0 : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (by linarith) _
  have hQT : ((calQK A G M Jb : ℕ) : ℝ) ≤ Tann := by
    calc ((calQK A G M Jb : ℕ) : ℝ) = Real.exp (Real.log ((calQK A G M Jb : ℕ) : ℝ)) :=
          (Real.exp_log hQpos).symm
      _ ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2)) := Real.exp_le_exp.mpr hJdef
      _ ≤ Real.exp (30 * (Real.log X) ^ ((1 : ℝ) / 2)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ ≤ Tann := hTgate
  have hVJ : ∀ v ∈ ramI (calH H1 Jb) (calP A G Jb) (calQK A G M Jb),
      Real.exp (mrAlpha η Jb * (v : ℝ) / calH H1 Jb) ≤ VJ := by
    intro v hv
    have htop := ramI_top_le hHb0 hQ1.le hv
    have hstep : mrAlpha η Jb * (v : ℝ) / calH H1 Jb
        ≤ mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left htop hα0
    exact le_trans (Real.exp_le_exp.mpr hstep) hVJg
  have hα : mrAlpha η Jb ≤ 1 / 4 - η := by
    have hinv : (0 : ℝ) ≤ 1 / (2 * (Jb : ℝ)) := by positivity
    rw [mrAlpha]
    nlinarith
  have hcalH1 : calH H1 1 = H1 := by simp [calH]
  have hH1two : (2 : ℝ) ≤ calH H1 1 := by rw [hcalH1]; exact hF.H1_two
  have hQ1Xd : calQK A G M 1 ≤ Xd := le_trans (calQK_mono A hG1 hJb1) hF.Q_le_Xd
  have hbot1 : ∀ v ∈ ramI (calH H1 1) (calP A G 1) (calQK A G M 1),
      1 ≤ ramRbot (calH H1 1) Xd v :=
    fun v hv => ramRbot_one_le_of_mem_ramI (by linarith)
      (one_le_calQK A G M 1) hQ1Xd hv
  have hP1pos : (0 : ℝ) < ((calP A G 1 : ℕ) : ℝ) := by
    have h : 1 ≤ calP A G 1 := by simp only [calP]; exact Nat.one_le_two_pow
    have : (1 : ℝ) ≤ ((calP A G 1 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  have hcapinst := hcap g c a cf hg hc1 hcf1 N Xd P Q Jb Jb (calP A G) (calQK A G M) m₀ Ms
    Mt kk (calH H1) (mrAlpha η) X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hQ1 hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 le_rfl hHb2 hα0 hP3 hPQ hQT hVJ hα (by linarith) hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup
  exact hfeed c a b (calP A G) (calQK A G M) (calH H1) η Jb N Xd (calP A G 1) X Tann t₁ S ε
    hη hη6 hJb1 hXd1 hNXd (by linarith) hP1pos (levelGates_calibratedK hF) hH1two
    (by simp only [calP]; exact Nat.one_le_two_pow)
    (calP_le_calQK hM1 le_rfl) hbot1 hcoef hb1 (fun p => hc1 p) hwin
    hcapinst

set_option maxHeartbeats 1000000 in
-- the same fuse as `SeamNumber.seam_row_number`, at the socketed row: two large
-- predicate-blind applications composed by `.trans`
/-- **S9b — THE SOCKETED SEAM ROW AS ONE NUMBER** (`seam_row_number_nocap`).
`SeamNumber.seam_row_number` at S9a: `Σ_j lemma12Rows` priced by
`TypicalPriceK.sum_lemma12Rows_priced_calibratedK2`, so the whole right-hand side is a
formula in the parameters — no integral, no coefficient sum, no ladder hypothesis, and now
**no row cap either**.

`t₁` is FREE and `hSup` is a hypothesis, exactly as in the landed twin.  On the cap-free
branch the consumer takes `t₁ := 0` and discharges `hSup` at `S := 0` by
`ball_leg_vacuous_at_zero`, which makes the `8S²` summand VANISH — the branch never touches
a produced centre.  The socket is closed by `pocketSocket_of_floor`.

The six `X_d`-side reconciliation gates (R1)–(R6) and the `X_d ≤ X` bridge are the landed
twin's, verbatim. -/
theorem seam_row_number_nocap :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        Real.exp 2 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j : ℕ, ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j : ℕ, thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j : ℕ, 2 ≤ m₀ j) →
        (∀ j : ℕ, ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j : ℕ, ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        PocketSocket g P Q X theta293 t₁ →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ X) →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin →
        0 ≤ cofactorMfl X theta293 kmin →
        2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 Jb,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ)
              * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
                  * (Tann * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
                  * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                      + 60 * (calH H1 1 / mrAlpha η 1)
                          * Real.exp (4 * mrAlpha η 1 / calH H1 1))
                + 1536 * Cs * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
                    * (1 / ((calP A G 1 : ℕ) : ℝ))
                + 480 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + C * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, hseam⟩ := seam_row_calibratedK_nocap
  obtain ⟨C, hC, hK2⟩ := sum_lemma12Rows_priced_calibratedK2
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hwin
    hQXd hXdbig hN4 hdom ha1 hasupp
  have hA : 1 ≤ A := le_trans (by norm_num) hF.A_floor
  have hG1 : 1 ≤ G := hF.one_le_G
  have hM1 : 1 ≤ M := hF.one_le_M
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd1
  have hT0 : (0 : ℝ) ≤ Tann := by linarith
  have hH10 : (0 : ℝ) < H1 := by linarith [hF.H1_two]
  -- ⟦THE BRIDGE⟧ `X_d ≤ X`, from the junction's own two binders
  have hXdX : (Xd : ℝ) ≤ X := by
    have h2 : (2 : ℝ) * (Xd : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNXd
    linarith
  have hJdef : Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) := by
    have hlog : Real.log (Xd : ℝ) ≤ Real.log X := Real.log_le_log hXd0 hXdX
    calc Real.log ((calQK A G M Jb : ℕ) : ℝ)
        ≤ Real.sqrt (Real.log (Xd : ℝ)) := hQXd
      _ ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt hlog
      _ = (Real.log X) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hreg : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine le_trans (Real.log_le_log ?_ ?_) hQXd
    · have h : (0 : ℕ) < calQK A G M j := lt_of_lt_of_le Nat.zero_lt_one (one_le_calQK A G M j)
      exact_mod_cast h
    · exact_mod_cast calQK_mono A hG1 hj.2
  have hseaminst := hseam g c a b cf hg hc1 hb1 hcf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hwin
  have hK2inst := hK2 A G M Jb N Xd H1 Tann a b c hA hG1 hM1 hXd1 hT0 hH10 hN4
    hreg hXdbig hdom ha1 hb1 hc1 hasupp hwin
  exact hseaminst.trans
    (add_le_add (add_le_add le_rfl (add_le_add le_rfl hK2inst)) le_rfl)

/-! ## §12 — THE CAP-FREE ARM, INSTANTIATED

The point of the whole file, in one statement: at a genuine large-`M` datum floor the seam
row closes with **no row cap, no collision gate, no produced centre, and no `8S²` term**. -/

set_option maxHeartbeats 1000000 in
-- one application of `seam_row_number_nocap`, at `t₁ := 0`, `S := 0`
/-- **THE CAP-FREE ARM** (`seam_row_number_capfree`).  `seam_row_number_nocap` with both
remaining openings closed on the large-`M` side:

* the collision socket by `pocketSocket_of_floor` — the floor `CapFreeFloor g X` makes the
  pocket impossible at every damping, so the socket is VACUOUS (S1 + S2 + S10);
* the ball binder `hSup` by `ball_leg_vacuous_at_zero` at `t₁ := 0`, `S := 0` — the seam
  ball around the origin misses the annulus, so **the `8S²` summand is gone from the
  right-hand side entirely**.

⚠ Nothing here reads a produced centre: `t₁ := 0` is a choice, not an output.  This is the
FarArm ban discharged by construction.

The `θ`-side gates `pocketSocket_of_floor` needs (`0 < θ₂₉₃`, `θ₂₉₃ ≤ 1/32`, `e ≤ log X`,
and the §8.3 endpoints `P₈₃ ≤ P`, `Q ≤ Q₈₃`, `P ≤ Q`) are ALREADY in the K-frame row's
hypothesis list, so the cap-free branch adds exactly one datum: the floor. -/
theorem seam_row_number_capfree :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        Real.exp 2 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j : ℕ, ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j : ℕ, thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j : ℕ, 2 ≤ m₀ j) →
        (∀ j : ℕ, ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j : ℕ, ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        -- ⟦THE ONE NEW DATUM⟧ the large-`M` floor, on the bare datum, at the `|v| ≤ X` box
        CapFreeFloor g X →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ X) →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin →
        0 ≤ cofactorMfl X theta293 kmin →
        2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 Jb,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ)
              * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
                  * (Tann * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
                  * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                      + 60 * (calH H1 1 / mrAlpha η 1)
                          * Real.exp (4 * mrAlpha η 1 / calH H1 1))
                + 1536 * Cs * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
                    * (1 / ((calP A G 1 : ℕ) : ℝ))
                + 480 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + C * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hnum⟩ := seam_row_number_nocap
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hfloor hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hNXd hcoef hwin
    hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦SUPPLIER 2⟧ the socket, VACUOUSLY, at the centre `0`
  have hsock : PocketSocket g P Q X theta293 0 :=
    pocketSocket_of_floor hg theta293_pos (le_of_lt theta293_lt_one_div_32) hLXe hPlow
      hQhigh hPQ83 hfloor 0
  -- ⟦S8⟧ the ball binder, from the emptiness at the origin, at `S := 0`
  have hSup := ball_leg_vacuous_at_zero (N := N) (a := a) (T := Tann)
    (show (1 : ℝ) < Real.log X by linarith)
  have h := hnum g c a b cf hg hc1 hb1 hcf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann 0 δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E 0
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hwin
    hQXd hXdbig hN4 hdom ha1 hasupp
  exact h.trans (le_of_eq (by ring))

end Salt.MR
