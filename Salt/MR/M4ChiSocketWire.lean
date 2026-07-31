/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ChiSummed

/-!
# ⟦A4-D4⟧ — THE SOCKET WIRING, THE WIRING HALF (`M4ChiSocketWire`)

Design provenance: `docs/exploration/a4-bridge-freeze-0730.md`, the A4 BRIDGE freeze,
**v2 addendum, amendment ⟦A2⟧**.  The freeze's D4 was rescoped by the refuter pass
(REF-A4-SHAPE, `R-A4-5(e)`): the φ(q)-LEDGER ARITHMETIC PAGE — the six-debit classification
of `thm_a2'`'s summands into g-arm-absorbable (`X`-side) and ⟦gate 8⟧-tightening
(`P₁/M`-side) — is COUNCIL work and appears NOWHERE in this file.  What lands here is the
WIRING: how `M4ChiSummed.M4ChiSummedFreeRow` — `m4_second_road`'s ⟦item 11⟧, the second
road's one analytic slot — is fed from a large-`j` grade plus the landed small-`j` trivial
half, and how the door's own per-character row datum discharges the large-`j` shape.

## ⟦THE GRADED SPLICE⟧ — why the split is at `doorRowFloor M`, and why it is free

The corpus's row grades are ALREADY split at the door's floor `doorRowFloor M = M·Adoor M`:

* ABOVE the floor the capstone speaks — `M4DoorClose.m4_door_meansq_carried` is stated
  `doorRowFloor M ≤ j → …` and produces the row mean square at the carried register's grade;
* BELOW it the absolute grade `4` is all there is
  (`M4DoorClose.doorRow_trivial_grade`), and `M4ChiSummed.m4_chiSummedFreeRow_trivial`
  already carries the whole socket at `4·arcDen 12 H`.

⟦KERNEL-CONFIRMED CLEAN⟧ `chiFreeRowSq` is DEFEQ to `m4_door_meansq_carried`'s conclusion
(`chiFreeRowSq_le_four`'s proof term is `doorRow_trivial_grade` applied directly, with no
`unfold` anywhere), so the two halves meet at the byte, not at a rewrite.

⟦THE SPLIT COSTS THE CONSUMER NOTHING⟧ `m4_second_road`'s ⟦gate 4⟧ reads `RS` ONLY above the
floor (`∀ j H, j₀ ≤ j → RS j H ≤ RSan H`); the trivial half `j < j₀` is charged inside
`M4ChiSummed.m4_chiSummedBlockN_of_shiftBlock` against `RStr` and READS NO ROW DATUM AT ALL.
So at `j₀ := doorRowFloor M` the spliced grade `m4ChiRowGraded M RSbig` presents exactly
`RSbig` to every gate that looks (`m4ChiRowGraded_an`), and the `else` branch is invisible.
No supplier choice is forced: `RSbig` is an ABSTRACT parameter throughout, and the leg
census, the partition fork and the ⟦Rbd HOLE⟧ of the v2 addendum are untouched here.

## ⟦THE φ(q) LEDGER⟧ — stated, not paid

The door's row datum is PER CHARACTER, so summing it over `χ` multiplies by
`φ(q) ≤ q ≤ arcDen 12 H`.  Following `M4ChiSummed`'s header doctrine — *the `φ(q)` is paid
where it is stated, never hidden* — `m4_chiSummedFreeRowBig_of_doorCarried` carries that
factor VISIBLY in its conclusion's grade, `fun j H => arcDen 12 H * Bd j H`, and makes no
attempt to absorb it.  Whether that debit is affordable against
`m4_second_road_rs_ceiling` is the council's arithmetic page, not this file's.

⟦WHAT IS DELIBERATELY NOT ATTEMPTED⟧ the per-character `DoorRowCarried` register is taken as
a HYPOTHESIS quantified `∀ χ`; discharging it is D2/D3's job (the `hrows`/`hT0band` slots of
the A4 bridge).  This file is a conditional wrapper and nothing more.

## Contents

* §1 `M4ChiSummedFreeRowBig` — the socket's binders with `doorRowFloor M ≤ j` inserted;
* §2 `m4ChiRowGraded` and the splice `m4_chiSummedFreeRow_of_big`, plus the gate-4 reader;
* §3 `m4_chiSummedFreeRowBig_of_doorCarried` — the door-datum instantiation, and the
  composite `m4_chiSummedFreeRow_of_doorCarried` that lands ⟦item 11⟧ outright.

⟦THE TRAPS RESPECTED⟧ `arcDen 12 H` is never evaluated and never conflated with a `log X`
scale; the modulus predicates stay `q`-FREE (the socket's `RS` is a function of `(j, H)`
only); every gate (`0 < q`, `R.Hlo ≤ H ≤ R.Hhi`, `2^j ≤ A`, `√H ≤ A`, the x-scale
antecedent and the base cap `A ≤ 2·R.x` of the (α) base-cap surgery, JYH-granted
2026-07-30) is carried verbatim from the landed socket, never weakened.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE LARGE-`j` HALF OF THE SOCKET

`M4ChiSummed.M4ChiSummedFreeRow`'s own quantifier structure — the two regime binders, the
cap-general length, the modulus range, the dyadic window index, the three base antecedents
of ⟦R-P5⟧, the base cap of the (α) base-cap surgery (JYH-granted 2026-07-30) and the free
shift — with the ONE extra antecedent `doorRowFloor M ≤ j` that the door's capstone
demands. -/

/-- **THE `Σ_χ` FREE-BASE ROW SOCKET, ABOVE THE DOOR'S FLOOR** (`M4ChiSummedFreeRowBig`).

Byte-for-byte `M4ChiSummedFreeRow R M RSbig` with `doorRowFloor M ≤ j` inserted immediately
after the window index — the shape a supplier can actually meet, because
`M4DoorClose.m4_door_meansq_carried` is itself stated only above that floor.

⟦the (α) base-cap surgery, JYH-granted 2026-07-30⟧ the socket's fourth base antecedent
`(A : ℝ) ≤ 2·R.x` is carried here verbatim, so `m4_chiSummedFreeRow_of_big` still meets the
socket byte for byte and every supplier below serves only the BOUNDED base range — which is
what makes `M4Assembly.DoorFuseFrame`'s decaying upper caps satisfiable at all. -/
def M4ChiSummedFreeRowBig (R : ChowlaRegime) (M : ℕ) (RSbig : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloor M ≤ j → ∀ A : ℕ, 0 < A →
      2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      ∀ s ≤ L,
        ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s) ≤ RSbig j H

/-! ## §2 — THE GRADED SPLICE -/

/-- **THE SPLICED GRADE** (`m4ChiRowGraded M RSbig`) — the analytic grade above the door's
floor, the landed absolute grade `4·arcDen 12 H` below it.  `q`-FREE, as the socket demands
(the `arcDen` is the ⟦φ(q) LEDGER⟧'s character count, never the modulus). -/
def m4ChiRowGraded (M : ℕ) (RSbig : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun j H => if doorRowFloor M ≤ j then RSbig j H else 4 * arcDen 12 H

/-- Above the floor the spliced grade IS the analytic grade — this is what ⟦gate 4⟧ reads. -/
theorem m4ChiRowGraded_big (M : ℕ) (RSbig : ℕ → ℕ → ℝ) {j : ℕ} (H : ℕ)
    (hj : doorRowFloor M ≤ j) : m4ChiRowGraded M RSbig j H = RSbig j H := if_pos hj

/-- Below the floor the spliced grade is the absolute one — the half no consumer reads. -/
theorem m4ChiRowGraded_small (M : ℕ) (RSbig : ℕ → ℕ → ℝ) {j : ℕ} (H : ℕ)
    (hj : ¬ doorRowFloor M ≤ j) : m4ChiRowGraded M RSbig j H = 4 * arcDen 12 H := if_neg hj

/-- **⟦GATE 4, READ⟧** — `m4_second_road`'s analytic-envelope gate at `j₀ := doorRowFloor M`
sees only the `RSbig` branch, so an envelope for `RSbig` is an envelope for the splice.  This
is the whole reason the `else` branch costs nothing. -/
theorem m4ChiRowGraded_an {M : ℕ} {RSbig : ℕ → ℕ → ℝ} {RSan : ℕ → ℝ}
    (han : ∀ j H : ℕ, doorRowFloor M ≤ j → RSbig j H ≤ RSan H) :
    ∀ j H : ℕ, doorRowFloor M ≤ j → m4ChiRowGraded M RSbig j H ≤ RSan H := by
  intro j H hj
  rw [m4ChiRowGraded_big M RSbig H hj]
  exact han j H hj

/-- **⟦A4-D4a⟧ THE GRADED SPLICE** (`m4_chiSummedFreeRow_of_big`).  An ABSTRACT large-`j`
`Σ_χ` grade inhabits `m4_second_road`'s ⟦item 11⟧ at the spliced grade: above the door's
floor the hypothesis fires verbatim, below it the landed anti-vacuity witness
`m4_chiSummedFreeRow_trivial` carries the socket at `4·arcDen 12 H` (the `φ(q) ≤ arcDen`
count against `M4DoorClose.doorRow_trivial_grade`'s absolute `4`).

No supplier is named and no fork is entered: `RSbig` is a parameter. -/
theorem m4_chiSummedFreeRow_of_big {R : ChowlaRegime} {M : ℕ} {RSbig : ℕ → ℕ → ℝ}
    (hbig : M4ChiSummedFreeRowBig R M RSbig) :
    M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) := by
  intro H hlo hhi L hLH q hq hqQ j hjL A hA hAj hAsq hAx hAcap s hsL
  by_cases hcase : doorRowFloor M ≤ j
  · rw [m4ChiRowGraded_big M RSbig H hcase]
    exact hbig H hlo hhi L hLH q hq hqQ j hjL hcase A hA hAj hAsq hAx hAcap s hsL
  · rw [m4ChiRowGraded_small M RSbig H hcase]
    exact m4_chiSummedFreeRow_trivial R M H hlo hhi L hLH q hq hqQ j hjL A hA hAj hAsq hAx
      hAcap s hsL

/-! ## §3 — THE DOOR DATUM, INSTANTIATED

`M4DoorClose.m4_door_meansq_carried` is stated PER CHARACTER at the grade `B`; its conclusion
is DEFEQ to `chiFreeRowSq χ M j Xd ≤ B` (kernel-confirmed — `chiFreeRowSq_le_four` composes
with `doorRow_trivial_grade` by `exact`, no unfolding).  Summing over `χ` therefore costs
exactly the character count. -/

/-- **⟦A4-D4b⟧ THE DOOR DATUM, `Σ_χ`** (`m4_chiSummedFreeRowBig_of_doorCarried`).  A
CONDITIONAL WRAPPER: given the door's per-character carried register at every base the socket
quantifies over — **quantified `∀ χ`, and NOT discharged here** (that is the A4 bridge's
D2/D3, the `hrows`/`hT0band` slots) — the door row summed over characters inhabits the
large-`j` socket at

  `RSbig j H := arcDen 12 H · Bd j H`.

⟦THE φ(q), STATED⟧ the `arcDen 12 H` factor IS the ledger debit `φ(q) ≤ q ≤ arcDen 12 H`,
carried in the open where the freeze's ⟦A2⟧ demands it.  Nothing here tries to absorb it, and
nothing here reads `m4_second_road_rs_ceiling`: pricing the debit is the council's page.

The `∃`-bound constants are `m4_door_meansq_carried`'s own, hoisted once; `Qm` is the modulus
range the door's capstone was proved in, and `hQm` is the cap `arcDen 12 H ≤ Qm` that puts
the socket's characters inside it — the same idiom as
`M4DoorClose.m4_dyadicRow_carried`. -/
theorem m4_chiSummedFreeRowBig_of_doorCarried :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (R : ChowlaRegime) (Qm M : ℕ) (Bd : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, 0 ≤ Bd j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
          (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloor M ≤ j → ∀ A : ℕ, 0 < A →
            2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
            (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
            (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
              ∀ χ : DirichletCharacter ℂ q,
                DoorRowCarried Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M (A + s) j
                  (Bd j H)) →
        M4ChiSummedFreeRowBig R M (fun j H => arcDen 12 H * Bd j H) := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_door_meansq_carried
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro R Qm M Bd hM hQm hBd0 hcar H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx
    hAcap s hsL
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦the modulus range: the socket's cap put inside the capstone's⟧
  have hqQm : q ≤ Qm := by
    have hR : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
    exact_mod_cast hR
  -- ⟦the row, PER CHARACTER — the conclusion is `chiFreeRowSq` at the byte⟧
  have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      chiFreeRowSq χ M j (A + s) ≤ Bd j H := fun χ _ =>
    hrow Qm q χ hq hqQm M (A + s) j (Bd j H) hM hjfl
      (hcar H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL χ)
  -- ⟦the character sum: the ledger's factor, in the open⟧
  have hsum : ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s)
      ≤ ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ) * Bd j H := by
    calc ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s)
        ≤ ∑ _χ : DirichletCharacter ℂ q, Bd j H := Finset.sum_le_sum hper
      _ = ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ) * Bd j H := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_dirichletCharacter_nat q] at hsum
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  have hmid : (q.totient : ℝ) * Bd j H ≤ arcDen 12 H * Bd j H :=
    mul_le_mul_of_nonneg_right hφarc (hBd0 j H)
  exact le_trans hsum hmid

/-- **⟦A4-D4, ASSEMBLED⟧** (`m4_chiSummedFreeRow_of_doorCarried`) — §3 spliced with §2:
the door's carried per-character register, quantified `∀ χ` and NOT discharged, inhabits
`m4_second_road`'s ⟦item 11⟧ outright, at the graded grade

  `RS j H = if doorRowFloor M ≤ j then arcDen 12 H · Bd j H else 4 · arcDen 12 H`.

Both branches carry the ⟦φ(q) LEDGER⟧'s `arcDen 12 H` explicitly; `m4ChiRowGraded_an` is
what ⟦gate 4⟧ then reads.  This is the whole wiring half of the freeze's D4 — the arithmetic
that decides whether such a grade meets `m4_second_road_rs_ceiling` is council work. -/
theorem m4_chiSummedFreeRow_of_doorCarried :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (R : ChowlaRegime) (Qm M : ℕ) (Bd : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, 0 ≤ Bd j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
          (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloor M ≤ j → ∀ A : ℕ, 0 < A →
            2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
            (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
            (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
              ∀ χ : DirichletCharacter ℂ q,
                DoorRowCarried Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M (A + s) j
                  (Bd j H)) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun j H => arcDen 12 H * Bd j H)) := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hbig⟩ :=
    m4_chiSummedFreeRowBig_of_doorCarried
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro R Qm M Bd hM hQm hBd0 hcar
  exact m4_chiSummedFreeRow_of_big (hbig R Qm M Bd hM hQm hBd0 hcar)

/-! ## §GK — the G-lever twin

The additive `_gk` family at `G := s13GK K M` (`GLever`): each declaration below is its
landed original with `(K : ℕ)` as a new FIRST binder and the socket's row square read at
`chiFreeRowSq_gk`.  `J` stays `2`; `m4ChiRowGraded` and its three lemmas read no door
object and keep their landed names, as does `doorRowFloor M` (LEVEL 1, K-INVARIANT).

⟦WHAT IS NOT HERE, AND WHY⟧ §3's two door-carried wires,
`m4_chiSummedFreeRowBig_of_doorCarried` (:171) and `m4_chiSummedFreeRow_of_doorCarried`
(:227), are BLOCKED, not attempted: both discharge `DoorRowCarried` through
`M4DoorClose.m4_door_meansq_carried`, which carries no `_gk` sibling (`M4DoorClose`'s own
§GK flags the gap — its door-row suppliers in `M4DoorRow`/`M4T0Datum`/`M4Puncture` are
untwinned).  The rewrite is mechanical once that lands; no numeral is in question.
-/

/-- `M4ChiSummedFreeRowBig` (:96), at the lever. -/
def M4ChiSummedFreeRowBig_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (RSbig : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloor M ≤ j → ∀ A : ℕ, 0 < A →
      2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      ∀ s ≤ L,
        ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_gk K χ M j (A + s) ≤ RSbig j H

/-- `m4_chiSummedFreeRow_of_big` (:137), at the lever. -/
theorem m4_chiSummedFreeRow_of_big_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {RSbig : ℕ → ℕ → ℝ}
    (hbig : M4ChiSummedFreeRowBig_gk K R M RSbig) :
    M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M RSbig) := by
  intro H hlo hhi L hLH q hq hqQ j hjL A hA hAj hAsq hAx hAcap s hsL
  by_cases hcase : doorRowFloor M ≤ j
  · rw [m4ChiRowGraded_big M RSbig H hcase]
    exact hbig H hlo hhi L hLH q hq hqQ j hjL hcase A hA hAj hAsq hAx hAcap s hsL
  · rw [m4ChiRowGraded_small M RSbig H hcase]
    exact m4_chiSummedFreeRow_trivial_gk K R M H hlo hhi L hLH q hq hqQ j hjL A hA hAj hAsq hAx
      hAcap s hsL

end Salt.MR

end

-- #audit (temporary)
