/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.Wall
import Salt.TwinBar.TwinDoor
import Salt.Chen.WeightNoGo
import Salt.TwinBar.Constrained

/-!
# THREAD M — the separation-game master and its instances

A single **tolerant separation lemma** (`wall_of_indistinguishable`) that
RE-DERIVES two of the three landed parity walls — W3 (`no_readable_certificate`)
and W2 (`parity_wall`) — as literal instances.  This file is a
**unification / atlas** result: it produces **no new twin-prime progress**.  Every
node here concludes a ceiling (`Φ … ≤ small`); the ONLY implication to twins is the
LANDED door `input_breaks_wall` (M5), whose premise `TwinB_min` is class-D open.

The master is *trivial as pure logic* (a three-line `linarith`); its value is
organizational.  ALL mathematical content lives in the landed decoy witnesses
(`impostor_feasible`, `sieveAgree_pair`, `siftedSum_sPlus`), which the instances
lift unchanged.

## The nodes

* **M1** `wall_of_indistinguishable` (tolerant) + `wall_of_indistinguishable_eq`
  (the `B = 0` reading corner).
* **M2** `no_readable_certificate_via_master` — W3 through the master (`B = 0`,
  decoy = the impostor).  Byte-identical conclusion to
  `Salt.Chen.no_readable_certificate`.
* **M3** `parity_wall_via_master` — W2 through the master (cap = `siftedSum`,
  decoy = `sPlus x`, budget `B`).  Byte-identical conclusion to
  `Salt.TwinBar.parity_wall`.
* **M4** `IndistWall` (the shared shape, per-instance `radius`) + its two
  instances + `each_indist_wall_from_master`.  Purely organizational.
* **M5** the door leg (`input_breaks_wall`) + the threshold leg (W1 re-exports)
  + the R4 open board.

## The frozen design blocks (docs/exploration/m-design.md)

* BLOCK 1 — the master is TOLERANT (a shared budget `B`), not equality; equality
  is only the `B = 0` corner used by W3.
* BLOCK 2 — the three "critical strengths" are DIFFERENT numbers in different
  roles; `radius` is a per-instance role, never one shared quantity.  No Lean
  statement asserts them equal or commensurable.
* BLOCK 3 — the `0.614` price tie is a W1-internal definitional identity (prose
  only; the single `example` below is decorative).
* BLOCK 4 — W1 (`no_twin_weight`) is a Cauchy–Schwarz ceiling, NOT an
  indistinguishability instance; it is the threshold / enlargement leg (M5).
-/

open Salt.Chen Salt.TwinBar

namespace Salt.TwinBar.Sep

/-! ## M1 — the tolerant separation master and the `B = 0` corollary -/

/-- **The tolerant separation master.**  `agree` bakes in the budget `B`
(equality is the `B = 0` corner).  If a decoy `w` is reading-indistinguishable
from a target `u` at budget `B`, the certificate `Φ` is `2·B`-tolerant under
`agree`, and `Φ` is valid at the decoy (`Φ w ≤ cap w`), then the certificate at
the target is capped by the decoy's ceiling plus the tolerance:
`Φ u ≤ cap w + 2·B`.  Trivial as pure logic — ALL content is in the instances'
landed `agree` / `cap` witnesses. -/
theorem wall_of_indistinguishable
    {C : Type*} (agree : C → C → Prop) (Φ cap : C → ℝ) (B : ℝ) (u w : C)
    (hagree : agree u w)
    (htol : ∀ a b, agree a b → |Φ a - Φ b| ≤ 2 * B)
    (hvalid : Φ w ≤ cap w) :
    Φ u ≤ cap w + 2 * B := by
  have h := htol u w hagree
  rcases abs_le.mp h with ⟨_, h2⟩
  linarith

/-- The equality corner of the master (`B = 0`): `Φ` reads only `read`,
`read u = read w`, the decoy's ceiling is `≤ 0`  ⟹  `Ψ (read u) ≤ 0`.  Proved
as an instance of `wall_of_indistinguishable` with `agree a b := read a = read b`
and `B = 0`. -/
theorem wall_of_indistinguishable_eq
    {C R : Type*} (read : C → R) (Ψ : R → ℝ) (cap : C → ℝ) (u w : C)
    (hread : read u = read w) (hvalid : Ψ (read w) ≤ cap w) (hcap : cap w ≤ 0) :
    Ψ (read u) ≤ 0 := by
  have h := wall_of_indistinguishable (fun a b => read a = read b)
    (fun c => Ψ (read c)) cap 0 u w hread
    (fun a b hab => by simp only [hab, sub_self, abs_zero]; norm_num) hvalid
  simp only [mul_zero, add_zero] at h
  linarith

/-! ## M2 — the W3 instance (re-derives `no_readable_certificate`)

Config `= ℝ⁶`; `read` = the first four coordinates; `cap` = the `p₁`-slot; decoy
`w` = the impostor `(a₁, a₂, a₃, s, 0, p₁ + e₂)` via `impostor_feasible`; `B = 0`. -/

/-- W3 as an instance of the master.  Byte-identical conclusion to
`Salt.Chen.no_readable_certificate`, proved through
`wall_of_indistinguishable_eq` (the `B = 0` corner). -/
theorem no_readable_certificate_via_master {A₁lo A₁hi A₂hi A₃hi Shi : ℝ}
    (Φ : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hΦ : ∀ a₁ a₂ a₃ s p₁ e₂,
      Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂ → Φ a₁ a₂ a₃ s ≤ p₁) :
    ∀ a₁ a₂ a₃ s p₁ e₂,
      Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂ → Φ a₁ a₂ a₃ s ≤ 0 := by
  intro a₁ a₂ a₃ s p₁ e₂ hf
  exact wall_of_indistinguishable_eq
    (fun c : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ => (c.1, c.2.1, c.2.2.1, c.2.2.2.1))
    (fun r => Φ r.1 r.2.1 r.2.2.1 r.2.2.2)
    (fun c => c.2.2.2.2.1)
    (a₁, a₂, a₃, s, p₁, e₂) (a₁, a₂, a₃, s, 0, p₁ + e₂)
    rfl (hΦ a₁ a₂ a₃ s 0 (p₁ + e₂) (impostor_feasible hf)) (le_refl 0)

/-! ## M3 — the W2 instance (re-derives `parity_wall`)

`cap = siftedSum`, decoy = `sPlus x`, target = `sMinus x`, budget `B`; the
`SieveAgree` witness is `⟨rfl, rfl, rfl, hminus, hplus⟩`. -/

/-- W2 as an instance of the master.  Byte-identical conclusion to
`Salt.TwinBar.parity_wall`, proved through `wall_of_indistinguishable`. -/
theorem parity_wall_via_master (x : ℕ) (hx : 2 ≤ x) (D : ℕ) (B : ℝ)
    (hplus : Salt.Chen.rosserRemainder (sPlus x) (D : ℝ) ≤ B)
    (hminus : Salt.Chen.rosserRemainder (sMinus x) (D : ℝ) ≤ B)
    (Φ : BoundingSieve → ℝ)
    (htol : ∀ s t, SieveAgree s t D B → |Φ s - Φ t| ≤ 2 * B)
    (hcert : ∀ s, Φ s ≤ s.siftedSum) :
    Φ (sMinus x) ≤ 2 + 2 * B := by
  have h := wall_of_indistinguishable (fun s t => SieveAgree s t D B) Φ
    (fun s => s.siftedSum) B (sMinus x) (sPlus x)
    ⟨rfl, rfl, rfl, hminus, hplus⟩ htol (hcert (sPlus x))
  simp only [siftedSum_sPlus x hx] at h
  exact h

/-! ## M4 — `IndistWall`: the shared shape of the two indistinguishability walls

Organizational ONLY: proves nothing beyond M1 + the instances.  `radius` is a
per-instance role (BLOCK 2) — W3's `1/200`, W2's `A > 2` threshold — NEVER one
shared quantity, and NO field or lemma equates the radii.  W1 is deliberately
absent: it is a Cauchy–Schwarz ceiling, not a separation instance (BLOCK 4). -/

/-- The data shared by the two indistinguishability walls (W2, W3): a config type,
an `agree` relation carrying budget `B`, a certificate `Φ` valid at the decoy `w`
and `2·B`-tolerant under `agree`, and a decoy indistinguishable from a target `u`.
`radius` records this wall's OWN critical strength (per-instance, BLOCK 2). -/
structure IndistWall where
  C : Type
  agree : C → C → Prop
  Φ : C → ℝ
  cap : C → ℝ
  B : ℝ
  u : C
  w : C
  radius : ℝ
  hagree : agree u w
  htol : ∀ a b, agree a b → |Φ a - Φ b| ≤ 2 * B
  hvalid : Φ w ≤ cap w

/-- Every `IndistWall` yields its wall conclusion by `wall_of_indistinguishable`.
The structure only records the data; the content is the master. -/
theorem each_indist_wall_from_master (W : IndistWall) :
    W.Φ W.u ≤ W.cap W.w + 2 * W.B :=
  wall_of_indistinguishable W.agree W.Φ W.cap W.B W.u W.w W.hagree W.htol W.hvalid

/-- The W2 wall as an `IndistWall` (cap = `siftedSum`, decoy = `sPlus x`,
target = `sMinus x`).  `radius = 2` records W2's `A > 2` threshold role — this
wall's own number, NOT commensurable with W3's `1/200` (BLOCK 2). -/
noncomputable def W2inst (x D : ℕ) (B : ℝ)
    (hplus : Salt.Chen.rosserRemainder (sPlus x) (D : ℝ) ≤ B)
    (hminus : Salt.Chen.rosserRemainder (sMinus x) (D : ℝ) ≤ B)
    (Φ : BoundingSieve → ℝ)
    (htol : ∀ s t, SieveAgree s t D B → |Φ s - Φ t| ≤ 2 * B)
    (hcert : ∀ s, Φ s ≤ s.siftedSum) : IndistWall where
  C := BoundingSieve
  agree := fun s t => SieveAgree s t D B
  Φ := Φ
  cap := fun s => s.siftedSum
  B := B
  u := sMinus x
  w := sPlus x
  radius := 2
  hagree := ⟨rfl, rfl, rfl, hminus, hplus⟩
  htol := htol
  hvalid := hcert (sPlus x)

/-- The W3 wall as an `IndistWall` (`B = 0`, decoy = the impostor, cap = the
`p₁`-slot).  `radius = 1/200` records W3's razor margin role — this wall's own
number, NOT commensurable with W2's `2` (BLOCK 2). -/
noncomputable def W3inst {A₁lo A₁hi A₂hi A₃hi Shi : ℝ} (Φ : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hΦ : ∀ a₁ a₂ a₃ s p₁ e₂,
      Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂ → Φ a₁ a₂ a₃ s ≤ p₁)
    (a₁ a₂ a₃ s p₁ e₂ : ℝ)
    (hf : Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂) : IndistWall where
  C := ℝ × ℝ × ℝ × ℝ × ℝ × ℝ
  agree := fun c c' =>
    c.1 = c'.1 ∧ c.2.1 = c'.2.1 ∧ c.2.2.1 = c'.2.2.1 ∧ c.2.2.2.1 = c'.2.2.2.1
  Φ := fun c => Φ c.1 c.2.1 c.2.2.1 c.2.2.2.1
  cap := fun c => c.2.2.2.2.1
  B := 0
  u := (a₁, a₂, a₃, s, p₁, e₂)
  w := (a₁, a₂, a₃, s, 0, p₁ + e₂)
  radius := 1 / 200
  hagree := ⟨rfl, rfl, rfl, rfl⟩
  htol := by
    intro a b h
    obtain ⟨e1, e2, e3, e4⟩ := h
    simp only [e1, e2, e3, e4, sub_self, abs_zero]
    norm_num
  hvalid := hΦ a₁ a₂ a₃ s 0 (p₁ + e₂) (impostor_feasible hf)

/-- `IndistWall` is inhabited (anti-vacuity): the impostor construction fed the
landed feasible witness and the zero certificate (`0 ≤ p₁` from `Feasible`).  The
LOAD-BEARING inhabitants are `W2inst` / `W3inst` fed their landed decoy witnesses
(`sieveAgree_pair` + `siftedSum_sPlus`; `impostor_feasible`). -/
theorem indistWall_nonempty : Nonempty IndistWall :=
  ⟨W3inst (A₁lo := 1) (A₁hi := 21 / 20) (A₂hi := 1) (A₃hi := 1) (Shi := 1)
    (fun _ _ _ _ => 0)
    (fun _ _ _ _ p₁ _ hf => by
      have h : (0 : ℝ) ≤ p₁ := by unfold Feasible at hf; exact hf.2.2.2.2.2.2.2.2.1
      simpa using h)
    1 (199 / 300) (199 / 300) (199 / 300) 0 (1 / 200) (by norm_num [Feasible])⟩

/-! ## M5 — the door leg, the threshold leg, and the R4 open board

The two remaining master legs re-export LANDED, axiom-clean theorems.  The door is
the ONLY route from an input to twins; its premise is class-D open. -/

/-- **The door leg (W2), `input_breaks_wall`.**  The LANDED door: a distributional
input at strength `TwinB_min` walks through the wall to twins.  This is the ONLY
twin-existence implication in the whole thread, and its premise is class-D OPEN. -/
theorem input_breaks_wall : TwinB_min → TwinPrimeConjecture :=
  twinB_min_implies_twins

/-- **The threshold leg (W1), base.**  The LANDED `k = 2` Cauchy–Schwarz ceiling:
no continuous positive-mass weight crosses the strict twin gate.  W1 is NOT an
`IndistWall` instance (BLOCK 4) — it is a ceiling, re-exported here as the
enlargement leg's base case. -/
alias twin_ceiling_base := no_twin_weight

/-- **The threshold leg (W1), `decoy_survives_below_radius`.**  The LANDED enlarged
no-go PERSISTS strictly below the enlargement radius `δ₀ = 1/log 2 − 1 ≈ 0.4427`.
`δ₀` is W1's OWN per-instance role (BLOCK 2) — a DIFFERENT number from W2's `2` and
W3's `1/200`, never commensurable. -/
alias decoy_survives_below_radius := no_twin_weight_enlarged

/-- **The threshold leg (W1), constrained.**  The LANDED marginal-vanishing
variant: the no-go survives even under the marginal constraint.  A `Constrained`
object, re-exported as part of W1's threshold leg. -/
alias decoy_survives_constrained := no_twin_weight_constrained

/-- BLOCK 3, decorative ONLY: the `≈ 0.614` "price tie"
`δ₀·(2·log 2) = 2 − 2·log 2` is the ring-trivial rearrangement of the enlargement
threshold `2·(1+δ₀)·log 2 = 2`.  It is INTERNAL to W1 (both sides are W1
quantities) and is NEVER a cross-wall coincidence. -/
example : (1 / Real.log 2 - 1) * (2 * Real.log 2) = 2 - 2 * Real.log 2 := by
  have h : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp

/-! ### The R4 open board (class-D, STATED-NOT-ATTEMPTED, never `sorry`'d)

These are the ONLY routes to actual twin progress; ALL are open, none attempted:

* **The door's premise** `TwinB_min` (= `TwinTypeII`), re-recorded below — the
  flagship Challenge 2.  A level-θ distributional input, class-D.
* **GAP-E** — the below-`y` decoration's escape carrier: the missing lower bound
  on heavy-semiprime mass (`bigOmegaGt`, `TwinDeficit.hE2lo`-shaped).  Parity-hard.
* **TwinLambda** — the fixed-shift Chowla input `Σ λ(n)·λ(n+2) = o(x)` plus the
  `λ → Λ` transfer.  Open. -/

/-- R4 board, item 1: the door's OPEN premise, re-recorded.  `open_door_premise`
is DEFINITIONALLY `TwinB_min`; nothing in this thread proves it. -/
abbrev open_door_premise : Prop := TwinB_min

end Salt.TwinBar.Sep
