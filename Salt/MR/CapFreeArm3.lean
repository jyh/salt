/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CapFreeArm
import Salt.MR.M4RowMR

/-!
# `CapFreeArm3` — THE CAP-FREE ARM AT THE `3X` BOX (the additive mint)

`CapFreeArm`'s chain runs at the TIGHTENED contour gate `|t| + T*₂(M, log M) ≤ X`
(`box_gate_le_X`), and `ThmA2.A2Frame.box` demands that gate for every `|t| ≤ X`.  At
`|t| = X` the demand reads `X + T*₂ ≤ X` with `T*₂ > 0` — **FALSE**, so `A2Frame` has no
inhabitants and `thm_a2'` has no models through it (flags, `TLGATES-SCOPE` R2).

This file is the council-ratified repair (C1, 2026-07-28): **the additive mint at the `3X`
convention**.  Nothing landed is altered.  Beside every stone of `CapFreeArm` we mint a twin
whose contour gate is the SIBLING convention `≤ 3X` — the one
`USetGradedPrice.pocket_transport_pin2` reports at natively — and whose floor/socket boxes
widen to match.  The mint is satisfiable where the original is not: at `|t| ≤ X` the demand
`|t| + T*₂ ≤ 3X` holds as soon as `T*₂ ≤ 2X` (`a2Frame3_satisfiable_partial`'s `box` field).

## WHAT MOVES, AND WHAT DOES NOT

Exactly three things move, in every twin:

1. the contour gate `|t| + T*₂(M, log M) ≤ 3X` (was `≤ X`);
2. the pocket/floor BOX `|v| ≤ 3X`, `|t₁'| ≤ 3X` (was `≤ X`) — `CapFreeFloor3`,
   `PocketSocket3`;
3. the twin consumed one layer down.

**⚠ THE SCALE TRAP (T2).**  The floor's DEMAND numerals do not move: `CapFreeFloor3` still
asks `(1/32)·loglog X + 25 <  𝔻²(g, p^{iv}; X)` — `loglog X`, never `loglog 3X`, and
`𝔻²(·, ·; X)`, never at `3X`.  The pretentious scale is GLOBAL; only the box widens.  The
same holds for the pocket cap `(1/32 − θ)loglog X` and for the whole §8.3 numerology.

## THE GATE, MINTED

`box_gate_le_3X` is `pocket_transport_pin2` verbatim — the 3X twin simply SKIPS the
tightening step that `box_gate_le_X` performs (`|t₁'| ≤ |t| + |t − t₁'| ≤ X`).  That is the
entire analytic content of the repair: the landed arm paid a step it did not have to pay,
and the price was the frame's satisfiability.

## THE COST

`no_pocket_of_floor3`, `pocketSocket_of_floor3` transplant verbatim (their arithmetic never
inspects `v` beyond membership in the box).  From `cofactor_Rbd34_local_nocap3` up, each
twin's proof is the landed twin's with the three substitutions above; every other binder,
every ladder-read and every EXIT EXPRESSION is byte-identical, so the downstream weighting
(`ThmA2Rows.a2Rows_of_capfree3`) plugs the frozen `hrows` slot unchanged.

NOT MINTED: `hUG34_unconditional_beats_door_nocap` (S7b, the door reading) — a leaf off the
row path (`seam_row_calibratedK_nocap` reads S7a directly), so the 3X arm has no consumer
for it.  Mint it if a door-side consumer ever appears.

Source pins: `docs/blueprints/flags.md` 2026-07-27 (TLGATES-SCOPE R2) and 2026-07-28
(the C1 ruling); `Salt/MR/CapFreeArm.lean` §§2–12 for the transplanted proofs.
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators
open Finset MeasureTheory

/-! ## §1 — the floor at the `3X` box -/

/-- **THE CAP-FREE DATUM FLOOR, AT THE `3X` BOX** (`CapFreeFloor3`).  `CapFreeFloor` with
the box widened from `|v| ≤ X` to `|v| ≤ 3X` and NOTHING else touched: the demand is still
`(1/32)·loglog X + 25` at the scale `X`, on the bare datum (trap T2 — the pretentious scale
is global, so `loglog X` never becomes `loglog 3X`).

Strictly stronger than `CapFreeFloor` (a bigger box), which is the price of the mint. -/
def CapFreeFloor3 (g : ℕ → ℂ) (X : ℝ) : Prop :=
  ∀ v : ℝ, |v| ≤ 3 * X →
    (1 / 32) * Real.log (Real.log X) + 25 < pretDistSq g (costwist v) X

/-- `CapFreeFloor3` implies `CapFreeFloor` for `0 ≤ X`: the smaller box is contained in the
bigger one.  (The converse is FALSE — the widening is real content.) -/
theorem capFreeFloor_of_capFreeFloor3 {g : ℕ → ℂ} {X : ℝ} (hX0 : 0 ≤ X)
    (h3 : CapFreeFloor3 g X) : CapFreeFloor g X :=
  fun v hv => h3 v (by linarith)

/-- **The `3X` floor at the honest large-`M` value.**  `capFreeFloor_of_row_floor` with both
boxes widened: a uniform `(1/16)loglog X` floor on `|v| ≤ 3X` gives `CapFreeFloor3` past
`800 < loglog X`.  The threshold is carried EXPLICITLY (law #253). -/
theorem capFreeFloor3_of_row_floor {g : ℕ → ℂ} {X : ℝ} (hLL : 800 < Real.log (Real.log X))
    (hfl : ∀ v : ℝ, |v| ≤ 3 * X →
      (1 / 16) * Real.log (Real.log X) ≤ pretDistSq g (costwist v) X) :
    CapFreeFloor3 g X := by
  intro v hv
  have h := hfl v hv
  linarith

/-- **NO POCKET AT ANY DAMPING, ON THE `3X` BOX** (`no_pocket_of_floor3`).
`no_pocket_of_floor` at the widened box: the `θ` and the `25` cancel exactly as before —
the arithmetic never inspects `v` beyond its membership in the floor's box. -/
theorem no_pocket_of_floor3 {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (P Q : ℕ)
    {X θ x v : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hθ0 : 0 < θ) (hθ32 : θ ≤ 1 / 32)
    (hLX : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X θ ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q)
    (hfloor : CapFreeFloor3 g X) (hv : |v| ≤ 3 * X) :
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

/-! ## §2 — the box gate at the sibling convention -/

/-- **THE CONTOUR BOX AT `3X`** (`box_gate_le_3X`).  `USetGradedPrice.pocket_transport_pin2`
consumed DIRECTLY: it already reports its pocket centre inside `|t₁'| ≤ 3X`, so the 3X twin
of `box_gate_le_X` simply skips the tightening step.

That skipped step is the whole R2 defect: `box_gate_le_X` narrows the report to `|t₁'| ≤ X`
at the cost of demanding `|t| + T*₂ ≤ X`, which is unsatisfiable at `|t| = X`.  Here the
gate is `≤ 3X`, satisfiable for every `|t| ≤ X` as soon as `T*₂ ≤ 2X`. -/
theorem box_gate_le_3X {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (P Q : ℕ)
    {k₀ M : ℕ} {X θ t x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hk₀pin : pin2Gate ≤ (k₀ : ℝ)) (hMX : (M : ℝ) ≤ X)
    (hTM : |t| + Tstar2 (M : ℝ) (Real.log (M : ℝ)) ≤ 3 * X) :
    (∀ k : ℕ, k₀ ≤ k → k ≤ M → ∀ v : ℝ, |v - t| ≤ Tstar2 (k : ℝ) (Real.log (k : ℝ)) →
        cofactorMfl X θ (k₀ : ℝ)
          ≤ pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) (k : ℝ))
      ∨ (∃ t₁' : ℝ, |t - t₁'| ≤ Tstar2 (M : ℝ) (Real.log (M : ℝ)) ∧ |t₁'| ≤ 3 * X ∧
          pretDistSq (ellLin (gxDatum g P Q x)) (costwist t₁') X
            ≤ (1 / 32 - θ) * Real.log (Real.log X)) :=
  pocket_transport_pin2 hg P Q hx0 hx1 hk₀pin hMX hTM

/-! ## §3 — the socket at the `3X` box -/

/-- **THE COLLISION SOCKET AT THE `3X` BOX** (`PocketSocket3`).  `PocketSocket` with its
antecedent box widened to `|t₁'| ≤ 3X`, so it accepts `box_gate_le_3X`'s report verbatim.
Strictly stronger than `PocketSocket` (it speaks about more centres). -/
def PocketSocket3 (g : ℕ → ℂ) (P Q : ℕ) (X θ t₁ : ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ t₁' : ℝ, |t₁'| ≤ 3 * X →
    pretDistSq (ellLin (gxDatum g P Q x)) (costwist t₁') X
        ≤ (1 / 32 - θ) * Real.log (Real.log X) →
    |t₁' - t₁| < 1

/-- **THE CAP-FREE SUPPLIER AT `3X`, VACUOUSLY** (`pocketSocket_of_floor3`).  Under
`CapFreeFloor3` the socket's antecedent is false on the whole `3X` box, so the socket holds
at EVERY centre `t₁`.  `pocketSocket_of_floor`'s proof, at the widened box. -/
theorem pocketSocket_of_floor3 {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) {P Q : ℕ}
    {X θ : ℝ} (hθ0 : 0 < θ) (hθ32 : θ ≤ 1 / 32) (hLX : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X θ ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q)
    (hfloor : CapFreeFloor3 g X) (t₁ : ℝ) :
    PocketSocket3 g P Q X θ t₁ := by
  intro x hx0 hx1 t₁' ht₁' hpock
  exact absurd hpock
    (no_pocket_of_floor3 hg P Q hx0 hx1 hθ0 hθ32 hLX hPlow hQhigh hPQ hfloor ht₁')

/-! ## §4 — the co-factor bound, at the `3X` socket -/

/-- **THE CO-FACTOR `Rbd` AT THE `3X` SOCKET** (`cofactor_Rbd34_local_nocap3`).
`CapFreeArm.cofactor_Rbd34_local_nocap` with (i) the contour gate weakened to
`|t| + T*₂(M, log M) ≤ 3X` and (ii) the socket taken at `PocketSocket3`.  The `by_cases` on
the damping runs through `box_gate_le_3X`, whose CASE-B report `|t₁'| ≤ 3X` is exactly the
3X socket's antecedent.  The EXIT EXPRESSION is untouched (byte identity with `hCqgate`
downstream).

⟦THE SOCKET CUT⟧ **This lemma is the row's ONE reader of `b`'s structure** — the CASE-A/B
pocket machinery (coprime multiplicativity, `f 1 = 1`, the `pretDistSq` cap) is refutably
false at a generic `1`-bounded datum.  Everything above it is `b`-generic, so from §4′ up the
chain carries `CofactorSocket` instead and THIS lemma is the canonical inhabitant, packaged
as `cofactorSocket_of_ellLin`. -/
theorem cofactor_Rbd34_local_nocap3 {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1)
    (H : ℝ) (N Xn P Q j M k₀ : ℕ) (c Cb X θ t t₁ R : ℝ)
    (hc1 : 2 * c < 1) (hCb0 : 0 ≤ Cb)
    (hk₀th : ballQuarterThreshold ≤ (k₀ : ℝ))
    (hMN : M ≤ N) (hk₀lo : (k₀ : ℝ) < ramRbot H Xn j)
    (hk₀hi : ramRbot H Xn j ≤ (k₀ : ℝ) + 1) (hbot : 1 < ramRbot H Xn j)
    (hlow : ramRbot H Xn j - 1 ≤ (M : ℝ)) (hhigh : (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1))
    (hMtop : 2 * ramRbot H Xn j < (M : ℝ) + 3) (hMX : (M : ℝ) ≤ X)
    (hTM : |t| + Tstar2 (M : ℝ) (Real.log (M : ℝ)) ≤ 3 * X)
    (hgate32 : 18 + Real.log (Real.log X) - Real.log (Real.log (k₀ : ℝ))
      ≤ 32 * θ * Real.log (Real.log X))
    (hR0 : 0 < R) (hfar : R ≤ |t - t₁|)
    (hsock : PocketSocket3 g P Q X θ t₁)
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
  rcases box_gate_le_3X hg P Q hx.1 hx.2 hk₀pin hMX hTM with hA | hB
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
  · -- CASE B at this `x` — the pocket is in the 3X socket's box, so the socket collides it
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

/-! ## §4′ — ⟦THE SOCKET CUT⟧: the co-factor datum, FREED

`ROW-GENERICITY`'s verdict (2026-07-28): the whole `𝒰`/err leg of the cap-free row reads
exactly ONE structural fact about its co-factor datum, and that fact is §4's conclusion.
Above §4 every stone (`tL_main_sumsq`, `TSG_feed_of_thin`, `KS_priced`, the `𝒯_S` branch, the
exits) is generic in the datum.  So the cut: carry §4's conclusion as a NAMED PREDICATE, free
the datum, and let the caller inhabit the predicate however it can.

The bonus is what the row loses: `g`, `hg`, `PocketSocket3`, `CaseASocket2`, the `3X` contour
box, `ShortIntervalDatum`, the `kmin`/`Ymax` ladder and `CapFreeFloor3` all leave the row's
statement, replaced by `CofactorSocket` plus the single grade
`R̄ ≤ gradeCR2 C_b · (log X)^{−ρ₂₉₃}` that `USetPrice.balance_priced_main` actually consumes. -/

/-- **THE CO-FACTOR SOCKET** (`CofactorSocket`).  On the annulus `|t| ≤ Tann`, off the ball of
radius `Rrad` about `t₁`, every block's Ramaré co-factor polynomial is bounded by `R̄`:

`∀ j ∈ I, ∀ |t| ≤ Tann, Rrad ≤ |t − t₁| → ‖R_{j,H}(1+it)‖ ≤ R̄`.

This is `cofactor_Rbd34_local_nocap3`'s conclusion, quantified over the block index set — the
ONLY fact the row reads about `b`. -/
def CofactorSocket (H : ℝ) (N Xd P Q : ℕ) (Tann Rrad t₁ Rbar : ℝ) (b : ℕ → ℂ) : Prop :=
  ∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann → Rrad ≤ |t - t₁| →
    ‖ramR H N Xd P Q j b t‖ ≤ Rbar

/-- The socket is ANTITONE in the annulus height: a socket at the window's TOP serves every
admissible height below it.  (`A2Frame3.box_at`'s shape, for the socket.) -/
theorem CofactorSocket.mono {H : ℝ} {N Xd P Q : ℕ} {Tann Tann' Rrad t₁ Rbar : ℝ} {b : ℕ → ℂ}
    (hs : CofactorSocket H N Xd P Q Tann' Rrad t₁ Rbar b) (hT : Tann ≤ Tann') :
    CofactorSocket H N Xd P Q Tann Rrad t₁ Rbar b :=
  fun j hj t ht hfar => hs j hj t (le_trans ht hT) hfar

/-- **`ramR` IS LINEAR IN ITS CO-FACTOR SLOT** (`ramR_sum_fin`).  `R_{j,H}` is a finite sum
whose only dependence on `b` is the coefficient `b m`, so a finite linear combination of data
gives the same combination of co-factor polynomials.  This is the route the inclusion–
exclusion supplier takes (`cofactorSocket_of_pieces`). -/
lemma ramR_sum_fin {n : ℕ} (H : ℝ) (N Xd P Q j : ℕ) (ε : Fin n → ℂ) (bp : Fin n → ℕ → ℂ)
    (t : ℝ) :
    ramR H N Xd P Q j (fun m => ∑ i, ε i * bp i m) t
      = ∑ i, ε i * ramR H N Xd P Q j (bp i) t := by
  simp only [ramR, Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

/-- **THE SOCKET IS CLOSED UNDER SHORT LINEAR COMBINATIONS** (`cofactorSocket_of_pieces`).
If `b = Σ_{i<n} ε_i·b_i` with `‖ε_i‖ ≤ 1` (the inclusion–exclusion signs `ε_i = ±1` are the
intended instance) and each piece carries a socket at `R̄_i`, then `b` carries one at
`Σ_i R̄_i` — by `ramR`'s linearity and the triangle inequality.

This is the consumer the door-side supplier feeds: `prod_one_sub_gJ` reduces the sieved datum
`1_𝒮(P·)·λχ̄` to FOUR completely multiplicative pieces, and the factor `4` (`16` in the
square) is absorbed by the standing grade margins. -/
theorem cofactorSocket_of_pieces {n : ℕ} {H : ℝ} {N Xd P Q : ℕ} {Tann Rrad t₁ : ℝ}
    {b : ℕ → ℂ} {bp : Fin n → ℕ → ℂ} {ε : Fin n → ℂ} {Rb : Fin n → ℝ}
    (hε : ∀ i, ‖ε i‖ ≤ 1) (hb : ∀ m, b m = ∑ i, ε i * bp i m)
    (hs : ∀ i, CofactorSocket H N Xd P Q Tann Rrad t₁ (Rb i) (bp i)) :
    CofactorSocket H N Xd P Q Tann Rrad t₁ (∑ i, Rb i) b := by
  intro j hj t ht hfar
  have hbeq : b = fun m => ∑ i, ε i * bp i m := funext hb
  rw [hbeq, ramR_sum_fin]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  have hi := hs i j hj t ht hfar
  rw [norm_mul]
  calc ‖ε i‖ * ‖ramR H N Xd P Q j (bp i) t‖
      ≤ 1 * Rb i := mul_le_mul (hε i) hi (norm_nonneg _) (by norm_num)
    _ = Rb i := one_mul _

/-- **THE CANONICAL INHABITANT** (`cofactorSocket_of_ellLin`).  §4 packaged as a
`CofactorSocket` at the multiplicative datum `b := ellLin g`: the pocket floor supplies
`PocketSocket3`, the CASE-A discharge supplies `CaseASocket2`, the frame supplies the `3X`
contour box and the §8.3 block gates, and `Rbd34loc_uniform` supplies the uniform ceiling.

Every hypothesis here is one the row's statement USED to carry; after the cut they live here
and nowhere above. -/
theorem cofactorSocket_of_ellLin {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1)
    {H : ℝ} {N Xd P Q : ℕ} {Mt kk : ℕ → ℕ}
    {cq L cg Cb X θ Rrad Tann t₁ Rbar : ℝ}
    (hc1 : 2 * cg < 1) (hCb0 : 0 ≤ Cb) (hR0 : 0 < Rrad)
    (hsock : PocketSocket3 g P Q X θ t₁)
    (hblk : ∀ j ∈ ramI H P Q, TLBlockGates34 cq H P N Xd Mt kk Tann L cg Cb X θ Rrad j)
    (hbox : ∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
      |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X)
    (hA2 : ∀ j ∈ ramI H P Q, ∀ t : ℝ, CaseASocket2 g P Q cg Cb X θ (kk j) (Mt j) t)
    (hRbdU : ∀ j ∈ ramI H P Q,
      cofactorRbd34loc cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
          (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ≤ Rbar) :
    CofactorSocket H N Xd P Q Tann Rrad t₁ Rbar (ellLin g) := by
  intro j hj t ht hfar
  obtain ⟨-, -, -, -, -, -, hk₀th, hMN, hk₀lo, hk₀hi, hbot, hlow, hhigh, hMtop, hMX,
    hgate32, hend⟩ := hblk j hj
  exact le_trans
    (cofactor_Rbd34_local_nocap3 hg H N Xd P Q j (Mt j) (kk j) cg Cb X θ t t₁ Rrad hc1 hCb0
      hk₀th hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hMX (hbox j hj t ht) hgate32 hR0 hfar
      hsock (hA2 j hj t) hend)
    (hRbdU j hj)

/-! ## §5 — the `𝒯_L` exit, AT THE SOCKET -/

/-- **THE `𝒯_L` EXIT AT THE CO-FACTOR SOCKET** (`tL_supply_discharged34_local_nocap3`).
`CapFreeArm.tL_supply_discharged34_local_nocap` with its co-factor supply taken from the
CARRIED datum (§4′) instead of the `g`-derived pocket chain: the per-`t` bound
`‖R_{j,H}(1+it)‖ ≤ R̄` is read off `CofactorSocket`, and `USetThinTL.tL_main_sumsq` does the
rest.

⟦THE SOCKET CUT⟧ against the landed twin the binder list LOSES `g`, `hg`, `PocketSocket3`,
`CaseASocket2`, the contour box and the whole descent/window geometry (`k₀`, `M`, `c`, `C_b`,
`X_g`, `θ`, the endpoint charge) — every one of them served only the co-factor bound.  What
remains is `tL_main_sumsq`'s own gate list, the socket, and the far-leg geometry. -/
theorem tL_supply_discharged34_local_nocap3 :
    ∃ Cq cq T₀ : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧
      ∀ (b : ℕ → ℂ) (H : ℝ), 2 ≤ H → ∀ (P Q j N Xn : ℕ) (cf : ℕ → ℂ),
      (∀ n : ℕ, ‖cf n‖ ≤ 1) → H ≤ (j : ℝ) → j ∈ ramI H P Q →
      ∀ (T V L δ' : ℝ) (𝒯 : Finset ℝ), WellSpaced 𝒯 →
      (∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) → T₀ ≤ T → 1 < T →
      3 ≤ ramQbase H P j → (ramQbase H P j : ℝ) ≤ T →
      30 ≤ Real.log T / Real.log (ramQbase H P j) →
      5 ≤ Real.log (Real.log T) → 1 ≤ V → V⁻¹ ≤ δ' →
      Real.log T ≤ L → 1 ≤ Real.log T → Real.exp 1 ≤ L →
      Real.log (ramQbase H P j) ≤ L → Real.log V ≤ 100 * Real.log L →
      420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cq * (Real.log (ramQbase H P j)) ^ 2 →
      ∀ (t₁ Rrad Rbar : ℝ), 0 ≤ Rbar →
        CofactorSocket H N Xn P Q T Rrad t₁ Rbar b →
        (∀ t ∈ tLset H P Q j cf δ' 𝒯, Rrad ≤ |t - t₁| ∧ |t| ≤ T) →
        ∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N Xn P Q b cf j t‖ ^ 2
          ≤ 54 * Cq * Rbar ^ 2 * (H / (j : ℝ)) ^ 2 := by
  obtain ⟨Cq, cq, T₀, hCq, hcq, hT₀, htL⟩ := tL_main_sumsq
  refine ⟨Cq, cq, T₀, hCq, hcq, hT₀, ?_⟩
  intro b H hH P Q j N Xn cf hcf1 hHj hj T V L δ' 𝒯 hws hsub hT₀T hT hB3 hBT hκ30 hLL5
    hV1 hVδ hTL hlogT1 hLe hWL hlogV hkill t₁ Rrad Rbar hRbar0 hsock hper
  refine htL H hH P Q j N Xn cf b hcf1 hHj T V L δ' Rbar 𝒯 hws hsub hT₀T hT hB3 hBT hκ30 hLL5
    hV1 hVδ hTL hlogT1 hLe hWL hlogV hkill hRbar0 ?_
  intro t ht
  obtain ⟨hfar, hTabs⟩ := hper t ht
  exact hsock j hj t hTabs hfar

/-! ## §6 — the graded `hU` supply, AT THE SOCKET -/

/-- **THE GRADED `hU` SUPPLY AT THE CO-FACTOR SOCKET** (`hUG34_supplied_nocap3`).
`CapFreeArm.hUG34_supplied_nocap` with its `𝒯_L` feed taken from §5.  The `𝒯_S` half, the
far-leg geometry and the exit expression are the landed twin's verbatim; the co-factor supply
is the CARRIED `CofactorSocket` at `R̄`, so the `𝒯_L` leg no longer needs the per-block
`cofactorRbd34loc` ceiling (`hRbdU`), the `3X` contour box, `PocketSocket3` or
`CaseASocket2`. -/
theorem hUG34_supplied_nocap3 :
    ∃ Cq cq T₀ : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧
      ∀ (b fb a cf : ℕ → ℂ), (∀ n : ℕ, ‖fb n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
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
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q,
          thinBundleG Tann VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        Rrad ≤ seamRad X →
        0 ≤ Rbar → CofactorSocket H N Xd P Q Tann Rrad t₁ Rbar b →
        (∀ j ∈ ramI H P Q, TLBlockGates34 cq H P N Xd Mt kk Tann L cg Cb X θ Rrad j) →
        (∀ j ∈ ramI H P Q, 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
            * (∑ m ∈ Finset.Icc 1 (Ms j),
                ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) ≤ KS) →
        2 ≤ ⌊H * Real.log (P : ℝ)⌋₊ →
        (∫ t in (-Tann)..Tann, ‖ramErr H N Xd P Q a b cf t‖ ^ 2) ≤ E →
        (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset,
            ‖spoly N a t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (((ramI H P Q).card : ℝ) * KS
                  + 54 * Cq * Rbar ^ 2 * H ^ 2
                      / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E := by
  obtain ⟨Cq, cq, T₀, hCq, hcq, hT₀, hTL⟩ := tL_supply_discharged34_local_nocap3
  refine ⟨Cq, cq, T₀, hCq, hcq, hT₀, ?_⟩
  intro b fb a cf hfb1 hcf1 H hH N Xd P Q Jset Jb Pseq Qseq Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η cg Cb θ Rrad KS Rbar E
    hX0 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hH2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hV1 hVδ hlogV
    hRrad hRbar0 hsockR hblk hKS hj₀ herr
  have hTann0 : (0 : ℝ) ≤ Tann := by linarith
  have hκ30 : 30 ≤ Real.log Tann / Real.log (Qseq Jb) :=
    kappa30_of_TannGate X Tann (Qseq Jb) hQ1 hQpin hTgate
  have hRsub : (seamAnn X Tann \ seamBall X t₁) ⊆ Set.Icc (-Tann) Tann :=
    fun _ ht => seamAnn_subset_Icc X Tann ht.1
  have hTSfeed := TSG_feed_of_thin fb hfb1 Pseq Qseq Hseq αseq Jset Jb hJb1 hJbJ hH2 hα0
    Tann VJ hT1 hP3 hPQ hQT hκ30 hLL5 hVJ η X hα hη2 hTX
    (seamAnn X Tann \ seamBall X t₁) hRsub H N Xd P Q b cf δ' Ms hMs hbudget
  have hTLj : ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 →
      (↑𝒯 : Set ℝ) ⊆ (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset →
      (∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N Xd P Q b cf j t‖ ^ 2)
        ≤ 54 * Cq * Rbar ^ 2 * (H / (j : ℝ)) ^ 2 := by
    intro j hj 𝒯 hws h𝒯A
    obtain ⟨hHj, hB3, hBT, hκ30j, hWL, hkill, -, -, -, -, -, -, -, -, -, -, -⟩ := hblk j hj
    refine hTL b H hH P Q j N Xd cf hcf1 hHj hj Tann V L δ' 𝒯 hws
      (fun t ht => hRsub (h𝒯A (Finset.mem_coe.mpr ht)).1) hT₀T hT1 hB3 hBT hκ30j hLL5 hV1 hVδ
      hTLle hlogT1 hLe hWL hlogV hkill t₁ Rrad Rbar hRbar0 hsockR ?_
    intro t ht
    have ht𝒯 : t ∈ 𝒯 := tLset_subset H P Q j cf δ' 𝒯 ht
    have htA := h𝒯A (Finset.mem_coe.mpr ht𝒯)
    have hTabs : |t| ≤ Tann := htA.1.1.2
    have hnot : ¬ (|t - t₁| ≤ seamRad X) := htA.1.2
    exact ⟨le_trans hRrad (le_of_lt (not_le.mp hnot)), hTabs⟩
  refine hUG_exit_of_branches H N Xd P Q a b cf fb Pseq Qseq Hseq αseq Jset
    X Tann t₁ E hTann0 herr δ'
    (fun j => 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
      * ∑ m ∈ Finset.Icc 1 (Ms j), ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
    (fun j => 54 * Cq * Rbar ^ 2 * (H / (j : ℝ)) ^ 2)
    KS Cq Rbar (le_of_lt hCq) hj₀ (fun j hj 𝒯 hws h𝒯A => hTSfeed j hj 𝒯 hws h𝒯A) hTLj hKS ?_
  intro j _
  exact tL_block_weight Cq H Rbar Rbar j (le_of_lt hCq) hRbar0 le_rfl

/-! ## §7 — the graded station prize, AT THE SOCKET -/

/-- **THE GRADED STATION PRIZE AT THE CO-FACTOR SOCKET** (`hUG34_fully_priced_nocap3`).
`CapFreeArm.hUG34_fully_priced_nocap` with its `𝒰`-integral taken from §6.  All four grade
slots are discharged exactly as in the landed twin; the §8.3 endpoint pins stay (they feed
`floor_pin` and `ramI_card_le_pin`, not the box).

⟦THE SOCKET CUT⟧ the co-factor leg is now TWO carried facts — the socket at `R̄` and the
single grade `R̄ ≤ gradeCR2 C_b·(log X)^{−ρ₂₉₃}` that `USetPrice.balance_priced_main` actually
consumes.  The `kmin`/`Ymax` ladder (`Rbd34loc_uniform`, `Rbd34loc_grade_priced`) and the
CASE-A/pocket data leave the statement: they are the SUPPLIER's business
(`cofactorSocket_of_ellLin` for the multiplicative datum). -/
theorem hUG34_fully_priced_nocap3 :
    ∃ Cq cq T₀ : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧
      ∀ (b fb a cf : ℕ → ℂ), (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖fb n‖ ≤ 1) →
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq m₀ Ms Mt kk : ℕ → ℕ) (Hseq αseq : ℕ → ℝ),
      ∀ (X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S : ℝ),
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
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
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE SOCKET CUT⟧ the co-factor leg, as two carried facts
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q Tann Rrad t₁ Rbar b →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                ∩ seamTtotG fb Pseq Qseq Hseq αseq Jset, ‖spoly N a t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, hCq, hcq, hT₀, hsup⟩ := hUG34_supplied_nocap3
  refine ⟨Cq, cq, T₀, hCq, hcq, hT₀, ?_⟩
  intro b fb a cf hb1 hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S
    hH2 hX0 hLXe hL4 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hH0 : (0 : ℝ) ≤ H83 X theta293 := by linarith
  have hHeq : H83 X theta293 = (Real.log X) ^ theta293 := by rw [H83]
  have hlog2T : (0 : ℝ) ≤ 1 + Real.log (2 * Tann) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * Tann by linarith)
    linarith
  have hKS0 : (0 : ℝ) ≤ 20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)) :=
    mul_nonneg (by positivity) hlog2T
  -- ⟦P-b AT THE FREE DATUM⟧ `USetPrice.KS_priced` never read `ellLin`-ness
  have hKSb : ∀ j ∈ ramI (H83 X theta293) P Q,
      5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
          * (∑ m ∈ Finset.Icc 1 (Ms j),
              ‖ramRcoeff (H83 X theta293) N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
        ≤ 20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)) := fun j hj =>
    KS_priced (H83 X theta293) N Xd P Q j b hb1 (m₀ j) (Ms j) (hm₀2 j hj) (hm₀ j hj)
      (hMs j hj) (hMs4 j hj) Tann δ' (le_of_lt hT1)
  have hfl := floor_pin X P hL4 hPlow
  have hU := hsup b fb a cf hfb1 hcf1 (H83 X theta293) hH2 N Xd P Q Jset Jb Pseq Qseq
    Ms Mt kk Hseq αseq X Tann t₁ δ' V VJ L η (1 / Real.exp 1) Cb theta293 Rrad
    (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) Rbar E
    hX0 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hV1 hVδ hlogV
    hRrad hRbar0 hsockR hblk hKSb hfl.1 herr
  have hmain := balance_priced_main X (H83 X theta293) Cq (gradeCR2 Cb)
    (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) Rbar P Q hL0 hH0
    (ramI_card_le_pin X P Q hQ0 hQhigh hLXe) (le_of_eq hHeq) hfl.2
    (le_of_lt hCq) hKS0 hRbar0 hRgrade hKSgate hCqgate
  have hrem := rem_priced X Tann (H83 X theta293) ε EP2 E hL1 hX0 (by linarith)
    (le_of_eq hHeq.symm) habs hEP2 hErow
  have hbal := hUG_balance a fb N Pseq Qseq Hseq αseq Jset X Tann t₁ ε _ _ hε0 hL1 hX0
    hTgate hU hmain hrem
  exact prop_A3_T1_row_split_weightedG a N fb Pseq Qseq Hseq αseq Jset X Tann t₁ S _ hL0.le
    (by linarith) hX0 hXN hN2 hsupp hSup hbal

/-! ## §8 — the unconditional graded exit, AT THE SOCKET -/

/-- **THE GRADED STATION PRIZE, UNCONDITIONAL, AT THE CO-FACTOR SOCKET**
(`hUG34_unconditional_nocap3`).

⟦THE SOCKET CUT⟧ the landed twin's ONE job was to discharge §7's `CaseASocket2` binder by
`CaseASocket.caseASocket2_discharged`.  At a FREE co-factor datum there is no `CaseASocket2`
binder to discharge — the pointwise bound is CARRIED as `CofactorSocket`, and the CASE-A
discharge has moved to the socket's supplier (`cofactorSocket_of_ellLin`, whose consumer
instantiates `caseASocket2_discharged` at its own multiplicative datum).

So the twin is §7 verbatim.  The `X₀` slot of the existential is RETAINED — it is the shape
every consumer down to `ThmA2Rows.a2Rows_of_capfree3` destructures, and the row's own
statement never reads it; a supplier that needs the genuine `X₀` takes it from
`caseASocket2_discharged` directly. -/
theorem hUG34_unconditional_nocap3 :
    ∃ Cq cq T₀ X₀ : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
      ∀ (b fb a cf : ℕ → ℂ), (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖fb n‖ ≤ 1) →
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq m₀ Ms Mt kk : ℕ → ℕ) (Hseq αseq : ℕ → ℝ),
      ∀ (X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S : ℝ),
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
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
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q Tann Rrad t₁ Rbar b →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                ∩ seamTtotG fb Pseq Qseq Hseq αseq Jset, ‖spoly N a t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, hCq, hcq, hT₀, hpriced⟩ := hUG34_fully_priced_nocap3
  exact ⟨Cq, cq, T₀, 1, hCq, hcq, hT₀, one_pos, hpriced⟩

/-! ## §9 — the K-frame seam row, AT THE SOCKET -/

set_option maxHeartbeats 1000000 in
-- `SeamCalibrationK.seam_row_calibratedK`'s own raise, inherited by the socketed twin
/-- **THE SEAM ROW AT THE K-LADDER, SOCKETED** (`seam_row_calibratedK_nocap3`).
`CapFreeArm.seam_row_calibratedK_nocap` with its `𝒰`-leg taken from §8.  Every ladder-read
is discharged from `CalFrameK` alone and the `𝒯`-leg is predicate-blind, so both ride
verbatim; only the co-factor supply moves.

⟦THE SOCKET CUT⟧ the `𝒰`-leg's co-factor datum is now the SAME free `b` the `𝒯`-leg already
carried (`a(pm) = b m · c p`) — which is exactly how the door's sieved datum factorizes — so
the row gains no parameter, and `g`, `hg` leave the statement outright.

⟦WALL 1⟧ (2026-07-28).  `hwin` is GONE from the `𝒯`-leg: `M4DoorRow.band_window_ratio_lock`
shows the door datum cannot inhabit it at the K-blocks, so the leg is fed through
`TLegExit.TLeg_feeds_capstone_gen` at `M4RowMR`'s `hwin`-free FOUR-row Lemma-12 exit
(`lemma12_on_TsetG_mr_windowed`).  Two statement consequences: `hcoef` is the ON-WINDOW
factorization (`SeamRowWindowed.SeamCoefW`, level by level) and MR's dyadic support pin
`hasupp` joins the list — the four-row split reads it.  The row on the right is
`lemma12RowsMR`. -/
theorem seam_row_calibratedK_nocap3 :
    ∃ Cq cq T₀ X₀ Cs : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q Tann Rrad t₁ Rbar b →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
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
                + ∑ j ∈ Finset.Icc 1 Jb,
                    lemma12RowsMR N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann a
                      (bfam j) c)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, hCq, hcq, hT₀, hX₀0, hcap⟩ := hUG34_unconditional_nocap3
  obtain ⟨Cs, hCs, hfeed⟩ := TLeg_feeds_capstone_gen
  refine ⟨Cq, cq, T₀, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hasupp
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
  have hcapinst := hcap b c a cf hb1 hc1 hcf1 N Xd P Q Jb Jb (calP A G) (calQK A G M) m₀ Ms
    Mt kk (calH H1) (mrAlpha η) X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S
    hH2 hX0 hLXe hL4 hTgate hT1 hTX hQ1 hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 le_rfl hHb2 hα0 hP3 hPQ hQT hVJ hα (by linarith) hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup
  -- ⟦WALL 1's ROW⟧ the per-level Lemma-12 conclusion at the `hwin`-FREE four-row exit
  have hHj : ∀ j ∈ Finset.Icc 1 Jb, (2 : ℝ) ≤ calH H1 j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    rw [calH]
    nlinarith [hF.H1_two]
  have hPj1 : ∀ j : ℕ, 1 ≤ calP A G j := fun j => by
    simp only [calP]; exact Nat.one_le_two_pow
  refine hfeed c a bfam (calP A G) (calQK A G M) (calH H1) η Jb N Xd (calP A G 1) X Tann t₁ S ε
    (fun j => lemma12RowsMR N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann a (bfam j) c)
    hη hη6 hJb1 hXd1 (by linarith) hP1pos (levelGates_calibratedK hF) hH1two
    (by simp only [calP]; exact Nat.one_le_two_pow)
    (calP_le_calQK hM1 le_rfl) hbot1 hbf1 (fun p => hc1 p) ?_
    hcapinst
  intro j hj
  exact lemma12_on_TsetG_mr_windowed c (calP A G) (calQK A G M) (calH H1) (mrAlpha η) Jb j
    (hHj j hj) N Xd hXd1 hNXd (hPj1 j) a (bfam j) c (hcoef j hj) (hbf1 j) (fun p => hc1 p)
    (hasupp_real_of_nat hasupp) X Tann t₁ (by linarith)

set_option maxHeartbeats 1000000 in
-- the same fuse as `SeamNumber.seam_row_number`, at the socketed row
/-- **THE SOCKETED SEAM ROW AS ONE NUMBER** (`seam_row_number_nocap3`).
`CapFreeArm.seam_row_number_nocap` at §9's row: `Σ_j lemma12RowsMR` priced by
`M4RowMR.sum_lemma12RowsMR_priced_calibratedK2`, so the whole right-hand side is a
formula in the parameters.  The six `X_d`-side reconciliation gates and the `X_d ≤ X` bridge
are the landed twin's, verbatim.

⟦WALL 1⟧ the row prefactor is `960` where the `hwin`-carrying twin has `480` — the four-row
split's price (see `M4RowMR` §3).  `ThmA2Rows.a2_term3_weigh_mr` absorbs it inside `a2Mrow`'s
`5760`, so no interface numeral moves. -/
theorem seam_row_number_nocap3 :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q Tann Rrad t₁ Rbar b →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
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
                + 960 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + C * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, hseam⟩ := seam_row_calibratedK_nocap3
  obtain ⟨C, hC, hK2⟩ := sum_lemma12RowsMR_priced_calibratedK2
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp
  have hA : 1 ≤ A := le_trans (by norm_num) hF.A_floor
  have hG1 : 1 ≤ G := hF.one_le_G
  have hM1 : 1 ≤ M := hF.one_le_M
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd1
  have hT0 : (0 : ℝ) ≤ Tann := by linarith
  have hH1two : (2 : ℝ) ≤ H1 := hF.H1_two
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
  have hseaminst := hseam c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hasupp
  have hK2inst := hK2 A G M Jb N Xd H1 Tann a bfam c hA hG1 hM1 hXd1 hNXd hT0 hH1two hN4
    hreg hXdbig hdom ha1 hbf1 hc1 hasupp
  exact hseaminst.trans
    (add_le_add (add_le_add le_rfl (add_le_add le_rfl hK2inst)) le_rfl)

/-! ## §10 — THE CAP-FREE ARM AT `3X`, INSTANTIATED -/

set_option maxHeartbeats 1000000 in
-- one application of `seam_row_number_nocap3`, at `t₁ := 0`, `S := 0`
/-- **THE CAP-FREE ARM AT THE `3X` BOX** (`seam_row_number_capfree3`).
`seam_row_number_nocap3` with its remaining ball opening closed on the large-`M` side: the
binder `hSup` by `CapFreeArm.ball_leg_vacuous_at_zero` at `t₁ := 0`, `S := 0` — so the `8S²`
summand is gone from the right-hand side entirely.

⟦THE SOCKET CUT⟧ the collision socket USED to be closed here too, by `pocketSocket_of_floor3`
from `CapFreeFloor3 g X`.  At the free co-factor datum there is no collision socket in the
statement: the row carries `CofactorSocket … 0 R̄ b` (at the centre `t₁ = 0` the ball leg
picks) and the floor is the SUPPLIER's datum.  So `g`, `hg` and `CapFreeFloor3` leave.

The conclusion is `CapFreeArm.seam_row_number_capfree`'s, byte for byte. -/
theorem seam_row_number_capfree3 :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann δ' V VJ L η Cb Rrad Rbar ε EP2 E : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the ball's centre, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q Tann Rrad 0 Rbar b →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
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
                + 960 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + C * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hnum⟩ := seam_row_number_nocap3
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann δ' V VJ L η Cb Rrad Rbar ε EP2 E
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦S8⟧ the ball binder, from the emptiness at the origin, at `S := 0`
  have hSup := ball_leg_vacuous_at_zero (N := N) (a := a) (T := Tann)
    (show (1 : ℝ) < Real.log X by linarith)
  have h := hnum c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann 0 δ' V VJ L η Cb Rrad Rbar ε EP2 E 0
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp
  exact h.trans (le_of_eq (by ring))

/-! ## §11 — THE FRAME BUNDLE AT `3X` (`A2Frame3`)

`ThmA2.A2Frame` with its `box` field alone re-cut at the sibling convention.  THIS is the
repair's payload: `A2Frame.box` demands `|t| + T*₂ ≤ X` for every `|t| ≤ X`, FALSE at
`|t| = X` since `T*₂ > 0`; `A2Frame3.box` demands `≤ 3X`, which holds for every `|t| ≤ X`
as soon as `T*₂ ≤ 2X` (`ThmA2Rows.a2Frame3_satisfiable_partial`'s new field).

The other ten fields are `A2Frame`'s, verbatim — same names, same order, same statements —
so the two projection helpers below are `A2Frame.box_at` / `A2Frame.ksGate_at`'s shapes and
every consumer reads them the same way. -/

/-- **THE `∀Tann` FRAME BUNDLE AT `3X`** (`A2Frame3`).  `ThmA2.A2Frame` with `box` at the
sibling convention `|t| + T*₂(M_j, log M_j) ≤ 3X` — SATISFIABLE, which `A2Frame.box` is
not.  All other fields are byte-identical to `A2Frame`'s.

⟦THE SOCKET CUT⟧ the first parameter is the CO-FACTOR DATUM ITSELF (`b`), not a
multiplicative generator: `err` reads `ramErr … a b cf`, never `ramErr … a (ellLin g) cf`.
The frame is therefore `b`-generic, and at the capstone `b` is the SAME datum the row's
factorization binder `a(pm) = b m · c p` already carries. -/
structure A2Frame3 (b cf a : ℕ → ℂ) (N Xd P Q A G M Jb : ℕ) (Ms Mt kk : ℕ → ℕ)
    (H1 X h δ' VJ L η Cb Rrad EP2 cq T₀ : ℝ) : Prop where
  /-- MR's contour gate at every admissible height. -/
  tannGate : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X → TannGate X Tann
  /-- The height is a genuine height. -/
  one_lt : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X → 1 < Tann
  /-- The row's own floor `T₀` (`seam_row_number_nocap3`'s existential, `3 ≤ T₀`). -/
  T0_le : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X → T₀ ≤ Tann
  /-- The `h`-ceiling, read at the height (monotone; the freeze's `5 ≤ loglog(2X/h)`). -/
  loglog5 : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X → 5 ≤ Real.log (Real.log Tann)
  /-- `1 ≤ log Tann` (free from `loglog5`, kept as a field to mirror the row). -/
  one_le_log : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X → 1 ≤ Real.log Tann
  /-- The `L`-budget (monotone in `Tann`). -/
  log_le_L : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X → Real.log Tann ≤ L
  /-- The thin-bundle demand on the `Ms`-ladder, per height. -/
  thin : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
    ∀ j ∈ ramI (H83 X theta293) P Q,
      thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb) * X ^ (1 - 2 * η)
        ≤ ((Ms j : ℕ) : ℝ)
  /-- The §8.3 block gates, per height. -/
  blocks : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
    ∀ j ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk Tann L (1 / Real.exp 1) Cb X
        theta293 Rrad j
  /-- The contour box AT THE SIBLING CONVENTION `3X`, at the window's TOP — anti-monotone,
  see `A2Frame3.box_at`.  This is the field the R2 repair moves. -/
  box : ∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X
  /-- The kernel/short-interval gate, at the window's TOP — see `A2Frame3.ksGate_at`. -/
  ksGate : 32 * (Real.log X) ^ (2 + 2 * theta293)
      * (20512 * δ' ^ 2 * (1 + Real.log (2 * X))) ≤ (Real.log X) ^ (-theta293)
  /-- The Ramaré error mass, per height, at the row's own ceiling (so `hErow` is `le_rfl`). -/
  err : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
    (∫ t in (-Tann)..Tann, ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2)
      ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2)

namespace A2Frame3

variable {b cf a : ℕ → ℂ} {N Xd P Q A G M Jb : ℕ} {Ms Mt kk : ℕ → ℕ}
  {H1 X h δ' VJ L η Cb Rrad EP2 cq T₀ : ℝ}

/-- The `3X` contour box at any admissible height, from the top instance (anti-monotone).
`ThmA2.A2Frame.box_at`'s shape, at the sibling convention. -/
theorem box_at (F : A2Frame3 b cf a N Xd P Q A G M Jb Ms Mt kk H1 X h δ' VJ L η Cb Rrad
      EP2 cq T₀) {Tann : ℝ} (hTX : Tann ≤ X) :
    ∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
      |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X :=
  fun j hj t ht => F.box j hj t (le_trans ht hTX)

/-- The kernel gate at any admissible height, from the top instance (monotone in `Tann`
through `log(2Tann) ≤ log(2X)`).  `ThmA2.A2Frame.ksGate_at`'s proof, verbatim. -/
theorem ksGate_at (F : A2Frame3 b cf a N Xd P Q A G M Jb Ms Mt kk H1 X h δ' VJ L η Cb Rrad
      EP2 cq T₀) {Tann : ℝ} (hT0 : 0 < Tann) (hTX : Tann ≤ X) (hL0 : 0 ≤ Real.log X) :
    32 * (Real.log X) ^ (2 + 2 * theta293)
        * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) := by
  refine le_trans ?_ F.ksGate
  have hlog : Real.log (2 * Tann) ≤ Real.log (2 * X) :=
    Real.log_le_log (by linarith) (by linarith)
  have hrp : (0 : ℝ) ≤ (Real.log X) ^ (2 + 2 * theta293) := Real.rpow_nonneg hL0 _
  have hδ : (0 : ℝ) ≤ 20512 * δ' ^ 2 := by positivity
  nlinarith [mul_nonneg hrp hδ]

end A2Frame3


/-! ## §9′ — ⟦THE ENDPOINT WALL⟧: the K-frame seam row at the STRICT pair law -/

set_option maxHeartbeats 1000000 in
-- `seam_row_calibratedK_nocap3`'s own raise, inherited by the strict/fused sibling
/-- **THE SEAM ROW AT THE K-LADDER, SOCKETED — STRICT/FUSED** (`seam_row_calibratedK_nocap3_end`).
`seam_row_calibratedK_nocap3` at ⟦THE ENDPOINT WALL⟧'s repair: the inlined pair-law binder
carries the STRICT antecedent `X_d < p·m` (so a HALF-OPEN cut inhabits it with no endpoint
obligation on the datum), and the row on the right is `M4RowMR.lemma12RowsMR_end` — the same
FOUR rows with the `p²` row at the fused coefficient `ramP2coeffEndMR`.  Everything else is
the landed twin's, byte for byte. -/
theorem seam_row_calibratedK_nocap3_end :
    ∃ Cq cq T₀ X₀ Cs : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q Tann Rrad t₁ Rbar b →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → (Xd : ℝ) < (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
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
                + ∑ j ∈ Finset.Icc 1 Jb,
                    lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann a
                      (bfam j) c)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, hCq, hcq, hT₀, hX₀0, hcap⟩ := hUG34_unconditional_nocap3
  obtain ⟨Cs, hCs, hfeed⟩ := TLeg_feeds_capstone_gen
  refine ⟨Cq, cq, T₀, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hasupp
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
  have hcapinst := hcap b c a cf hb1 hc1 hcf1 N Xd P Q Jb Jb (calP A G) (calQK A G M) m₀ Ms
    Mt kk (calH H1) (mrAlpha η) X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S
    hH2 hX0 hLXe hL4 hTgate hT1 hTX hQ1 hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 le_rfl hHb2 hα0 hP3 hPQ hQT hVJ hα (by linarith) hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup
  -- ⟦WALL 1's ROW⟧ the per-level Lemma-12 conclusion at the `hwin`-FREE four-row exit
  have hHj : ∀ j ∈ Finset.Icc 1 Jb, (2 : ℝ) ≤ calH H1 j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    rw [calH]
    nlinarith [hF.H1_two]
  have hPj1 : ∀ j : ℕ, 1 ≤ calP A G j := fun j => by
    simp only [calP]; exact Nat.one_le_two_pow
  refine hfeed c a bfam (calP A G) (calQK A G M) (calH H1) η Jb N Xd (calP A G 1) X Tann t₁ S ε
    (fun j => lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann a (bfam j) c)
    hη hη6 hJb1 hXd1 (by linarith) hP1pos (levelGates_calibratedK hF) hH1two
    (by simp only [calP]; exact Nat.one_le_two_pow)
    (calP_le_calQK hM1 le_rfl) hbot1 hbf1 (fun p => hc1 p) ?_
    hcapinst
  intro j hj
  exact lemma12_on_TsetG_mr_windowed_end c (calP A G) (calQK A G M) (calH H1) (mrAlpha η) Jb j
    (hHj j hj) N Xd hXd1 hNXd (hPj1 j) a (bfam j) c (hcoef j hj) (hbf1 j) (fun p => hc1 p)
    (hasupp_real_of_nat hasupp) X Tann t₁ (by linarith)

set_option maxHeartbeats 1000000 in
-- the same fuse as `seam_row_number_nocap3`, at the strict/fused row
/-- **THE SOCKETED SEAM ROW AS ONE NUMBER — STRICT/FUSED** (`seam_row_number_nocap3_end`).
`seam_row_number_nocap3` at the strict binder.  ⟦AMENDMENT 1⟧: the endpoint mass is absorbed
inside `M4RowMR.four_rows_le_end`'s `1.5×` slack on the `B2` slot, gated by
`log₂(2X_d)·P ≤ 2·X_d`, so **the right-hand side is the landed twin's BYTE FOR BYTE** — the
prefactor is still `960`, and `ThmA2.a2RowsSum`/`a2Mrow` never move. -/
theorem seam_row_number_nocap3_end :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q Tann Rrad t₁ Rbar b →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → (Xd : ℝ) < (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
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
                + 960 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + C * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, hseam⟩ := seam_row_calibratedK_nocap3_end
  obtain ⟨C, hC, hK2⟩ := sum_lemma12RowsMR_priced_calibratedK2_end
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp
  have hA : 1 ≤ A := le_trans (by norm_num) hF.A_floor
  have hG1 : 1 ≤ G := hF.one_le_G
  have hM1 : 1 ≤ M := hF.one_le_M
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd1
  have hT0 : (0 : ℝ) ≤ Tann := by linarith
  have hH1two : (2 : ℝ) ≤ H1 := hF.H1_two
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
  have hseaminst := hseam c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hasupp
  have hK2inst := hK2 A G M Jb N Xd H1 Tann a bfam c hA hG1 hM1 hXd1 hNXd hT0 hH1two hN4
    hreg hXdbig hdom ha1 hbf1 hc1 hasupp
  exact hseaminst.trans
    (add_le_add (add_le_add le_rfl (add_le_add le_rfl hK2inst)) le_rfl)

set_option maxHeartbeats 1000000 in
-- one application of `seam_row_number_nocap3_end`, at `t₁ := 0`, `S := 0`
/-- **THE CAP-FREE ARM AT THE `3X` BOX — STRICT/FUSED** (`seam_row_number_capfree3_end`).
`seam_row_number_capfree3` at the strict pair-law binder; the conclusion is the landed one,
byte for byte. -/
theorem seam_row_number_capfree3_end :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann δ' V VJ L η Cb Rrad Rbar ε EP2 E : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the ball's centre, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q Tann Rrad 0 Rbar b →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → (Xd : ℝ) < (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
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
                + 960 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + C * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hnum⟩ := seam_row_number_nocap3_end
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann δ' V VJ L η Cb Rrad Rbar ε EP2 E
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦S8⟧ the ball binder, from the emptiness at the origin, at `S := 0`
  have hSup := ball_leg_vacuous_at_zero (N := N) (a := a) (T := Tann)
    (show (1 : ℝ) < Real.log X by linarith)
  have h := hnum c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann 0 δ' V VJ L η Cb Rrad Rbar ε EP2 E 0
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp
  exact h.trans (le_of_eq (by ring))

end Salt.MR
