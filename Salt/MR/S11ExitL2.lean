/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S11Exit45

/-!
# ⟦THE L² RESTRUCTURE⟧ stone 4, MR side — the split socket at the `K`-FREE head

`S11Exit45.m4_exit_socket_split_45` hands the road the landed `L¹` head: the
regime `R`, the tower endpoint law at `K = 9/2`, and one open binder — the door
integral bound at the constant grade `δ₀ = c₀·ε/(2K)`.  The restructure
(`docs/exploration/l2-restructure-freeze-0730.md`) re-cuts that handoff at the
Ξ-SUMMED `L²` door, where the spine's threshold is

```
δ₀ = cD3/(16·C) · ε / 4        (= c₀·ε/4)      -- NO 1/(2K)
```

(`SpineFinal.log_chowla_two_budget_head_g_sq`).  Two sockets, both additive, both
carrying the `9/2` tower conjunct (`tower_conjunct_45_le_five` is the free
downgrade to `^5` for consumers wired to the landed exponent):

* `m4_exit_socket_split_sq` — the DOOR-form socket.  One open binder,
  `MRTUniformityXiL2 R δ₀`, byte-identical to the predicate `MRTDoor` landed and
  `M4Window`'s adapter closes onto.  This is the doctrine's minimal shape: the
  `L²` door is SUPPLIED, never claimed.
* `m4_exit_socket_split_sq_arc` — the ROAD-form socket.  The two floors the road
  cannot place itself (M4-0's arc floor `H₀`, and `bigXi_bounded`'s count floor,
  both `ε`-determined and therefore knowable only on this side of the head) are
  ABSORBED into the head's `U1floor` slot, and the large-spectrum count `K` is
  delivered in the `∃`-prefix beside `ε` and `δ₀`.  What is left open is exactly
  what the road owns: the sieved socket grade `Bsieve`, the Parseval insert
  budget `Binsert`, and the closing budget line

  ```
  K · (2 · Bsieve H) + 2 · Binsert ≤ δ₀       (the freeze's 2K·Braw + δ/2 + 8·2^k/x)
  ```

⟦A1 — THE BINDER SPLIT⟧ (REF-L2-ARITH, mandatory).  The socket's own ceiling
conjunct lives at `δ_sock = √(c₀ε/(4K))`, the spine's `hMδ` at the glue `δ₀`
itself — 79 orders apart, both free.  Nothing here unifies them: `Bsieve` and
`Binsert` are independent binders and the only thing that couples them is the
budget line above.

⚠ **THE SEAM WARNING** (`MRTDoor.lean:174–182`, REF-L2 mandate R4).  THE
QUANTIFIERS STAY OUTSIDE THE INTEGRAL.  `MRTUniformityXiL2` is a finite sum of
integrals — no `sup` inside — and is IMPLIED by the landed `L¹` theorem-door
(`MRTDoor.mrtUniformityXiL2_of_xi`).  The sup-inside form is Tao arXiv:1509.05422v2 (4.1),
which is OPEN.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **THE SPLIT SOCKET AT THE `L²` DOOR** (`m4_exit_socket_split_sq`) — the twin of
`m4_exit_socket_split_45` whose single open binder is the Ξ-SUMMED `L²` door
predicate at the head's own `K`-FREE constant grade:

```
MRTUniformityXiL2 R δ₀ → ¬ logChowla2Fails R.eps R.x R.ω
```

Statement diff against `m4_exit_socket_split_45`: the open binder alone.  The
`ε`/`δ₀` prefix, the `∀ (U1floor, g)` binder order, the tower conjunct at `9/2`
and the conclusion are byte-identical; `extraFloor` is fired at `0` exactly as
there.  Note what is NOT here: no `NearRatTight` arc hypothesis and no `arcDen`
— at this shape the road hands over a finished door, so the arc gate belongs to
whoever builds it (`m4_exit_socket_split_sq_arc` below builds it here).

⚠ The `MRTDoor` seam warning rides this statement: the door is a finite sum of
integrals with the `∑` OUTSIDE the `∫` and no `sup` inside, supplied by the road
(`mrtUniformityXiL2_of_absWindowSqBound`), never claimed from Prop 2.4. -/
theorem m4_exit_socket_split_sq :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          (MRTUniformityXiL2 R δ₀ → ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨ε, δ₀, hε, hδ₀, hhead⟩ := log_chowla_two_budget_head_g_sq
  refine ⟨ε, δ₀, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, _, hRU1, hRg, hRtow, hR⟩ := hhead 0 U1floor g
  exact ⟨R, hReps, hRU1, hRg, hRtow, fun hdoor => hR δ₀ hδ₀ le_rfl hdoor⟩

/-- **THE SPLIT SOCKET, ROAD FORM** (`m4_exit_socket_split_sq_arc`) — the same
handoff with the two `ε`-determined floors ABSORBED and the large-spectrum count
`K` delivered in the `∃`-prefix.

`ε`, `K` and `δ₀` are fixed FIRST; then for every extra floor / outer-scale demand
`(U1floor, g)` there is a regime `R` at that `ε` whose floor absorbs

* M4-0's arc floor (`sum_bigXi_norm_windowExpSum_sq_le_twelve`, the `B₅ = 12`
  adapter — `bigXiArcTight_twelve` unconditional), and
* `bigXi_bounded`'s count floor, via the head's exported count gate
  (`log_chowla_two_budget_head_g_sq_count`),

**and nothing else**.  What stays open is the road's own supply, in
`M4Window`'s exact spelling:

* `hsplit` — the coefficient split `λ = a + e` (`a` sieved, `e` the α-independent
  insert complement);
* `hB0`/`hsock` — the sieved `L²` socket at every tight-major `α`
  (`M4Close.M4SievedDoorSq`'s per-`α` shape at the abstract `a`);
* `hins` — the ALREADY-SUMMED insert budget (the Parseval stone,
  `parseval_insert_budget_door`), paid ONCE because the datum is α-independent;
* `hρ` — the budget line `K·(2·Bsieve H) + 2·Binsert ≤ δ₀`, which
  `l2_budget_line` rewrites as the freeze's `2K·Braw + δ/2 + 8·2^k/x < c₀ε`.

`K` multiplies the SIEVED leg only; it never touches `δ₀`.  That is the whole
shed of ⟦THE L² RESTRUCTURE⟧, and it is visible in this statement's shape. -/
theorem m4_exit_socket_split_sq_arc :
    ∃ (ε : ℚ) (K δ₀ : ℝ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          (∀ (a e : ℕ → ℂ) (Bsieve : ℕ → ℝ) (Binsert : ℝ),
            (∀ m, lamCoeff m = a m + e m) →
            (∀ H : ℕ, 0 ≤ Bsieve H) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
              NearRatTight (arcDen 12 H) H α →
                (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                  ≤ Bsieve H * (H : ℝ) ^ 2) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
                ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                  ∂(logMeasure R.x R.ω)) ≤ Binsert) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              K * (2 * Bsieve H) + 2 * Binsert ≤ δ₀) →
            ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨ε, K, δ₀, hε, hK, hδ₀, hhead⟩ := log_chowla_two_budget_head_g_sq_count
  refine ⟨ε, K, δ₀, hε, hK, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨H₀, hH₀⟩ := sum_bigXi_norm_windowExpSum_sq_le_twelve ε hε
  obtain ⟨R, hReps, _, hRU1, hRg, hcount, hRtow, hR⟩ := hhead 0 (max U1floor H₀) g
  have hU1 : U1floor ≤ R.Hlo := le_trans (le_max_left _ _) hRU1
  have harc : H₀ ≤ R.Hlo := le_trans (le_max_right _ _) hRU1
  refine ⟨R, hReps, hU1, hRg, hRtow, ?_⟩
  intro a e Bsieve Binsert hsplit hB0 hsock hins hρ
  refine hR δ₀ hδ₀ le_rfl ?_
  intro H _ hlo hhi
  exact le_trans (hH₀ R hReps harc a e Bsieve K Binsert hsplit hB0 hsock hcount hins
    H hlo hhi) (hρ H hlo hhi)

/-! ### The two MRT thresholds installed on the ROAD-FORM exit — QUEUE item 12

`m4_exit_socket_split_sq_arc` above is the **fully-composed** L² exit: it consumes the door
producer internally and hands the caller `¬ logChowla2Fails` directly.  What it leaves to the
caller are two `ℕ`/function slots — `U1floor ≤ R.Hlo` and `g R.Hhi R.ω ≤ R.x` — and **those are
exactly the quantities QUEUE item 12's two ε-dependent thresholds bound.**  So the thresholds
install from OUTSIDE: no edit to the exit, no new import (`DoorFloor` is already in this file's
closure).

⚠️⚠️ **TWO DIFFERENT "TWO ε-DETERMINED FLOORS" LIVE ONE PHRASE APART, AND THEY ARE NOT THE SAME
PAIR.**  The exit's own audit card says it *"absorbs the two `ε`-determined floors the road cannot
place for itself"* — those are **M4-0's arc floor and `bigXi_bounded`'s count floor**, determined
by the CHOWLA budget `ε : ℚ`.  **This theorem's pair is `H₀mrt(ε)` and `H₊*(ε)`, determined by the
MRT error demand `ε : ℝ`** — a different quantity in a different type.  *Reading the card before
building nearly cancelled this node as redundant.*
⇒ 🔑 ***THE SAME LETTER NAMING TWO QUANTITIES POISONS READING AS WELL AS WRITING.***

📌 **The Chowla budget is spelled `q` here, not `e`,** because the payload block below binds
`(a e : ℕ → ℂ)` and an `e` in the `∃`-prefix would be SHADOWED inside it — legal, silent, and
exactly the kind of thing that makes a statement read wrong later.  *(The `DoorFloor` twins spell
it `e`; there is no payload block there to shadow it.)*

⛔ **The payload block is COPIED BYTE-FOR-BYTE from `m4_exit_socket_split_sq_arc`'s statement**, not
retyped — a transcription defect in a duplicated statement is invisible to every downstream check,
and both copies elaborating proves only that they agree with each other. -/

/-- **QUEUE item 12's thresholds, on the live composed exit.**  `m4_exit_socket_split_sq_arc` fired
at `U1floor := H₀mrt(ε)` and `g := fun _ _ => H₊*(ε)`, carrying the two MRT payoffs: above the
regime's own window floor and outer scale, `MRTThmA1`'s two threshold-shaped error terms are each
`≤ ε`.

⛔ **Nothing here supplies the road's own obligations** — the coefficient split, `Bsieve`, `Binsert`
and the closing budget line remain exactly as the exit states them. -/
theorem m4_exit_socket_split_sq_arc_at_mrt_floors (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (q : ℚ) (K δ₀ : ℝ), 0 < q ∧ 0 < K ∧ 0 < δ₀ ∧
      ∃ R : ChowlaRegime, R.eps = q ∧
        H0mrt ε ≤ R.Hlo ∧ HplusStar ε ≤ R.x ∧
        (∀ y : ℝ, ((R.Hlo : ℕ) : ℝ) ≤ y →
            (Real.log (Real.log y)) ^ 2 / Real.log y ^ 2 ≤ ε) ∧
        (∀ X : ℝ, ((R.x : ℕ) : ℝ) ≤ X →
            1 / (Real.log X) ^ ((1 : ℝ) / 50) ≤ ε) ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          (∀ (a e : ℕ → ℂ) (Bsieve : ℕ → ℝ) (Binsert : ℝ),
            (∀ m, lamCoeff m = a m + e m) →
            (∀ H : ℕ, 0 ≤ Bsieve H) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
              NearRatTight (arcDen 12 H) H α →
                (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                  ≤ Bsieve H * (H : ℝ) ^ 2) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
                ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                  ∂(logMeasure R.x R.ω)) ≤ Binsert) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              K * (2 * Bsieve H) + 2 * Binsert ≤ δ₀) →
            ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨q, K, δ₀, hq, hK, hδ₀, hexit⟩ := m4_exit_socket_split_sq_arc
  obtain ⟨R, hReps, hU1, hg, htow, hbody⟩ :=
    hexit (H0mrt ε) (fun _ _ => HplusStar ε)
  refine ⟨q, K, δ₀, hq, hK, hδ₀, R, hReps, hU1, hg, ?_, ?_, htow, hbody⟩
  · intro y hy
    refine mrt_middle_le_of_H0mrt hε hε1 (le_trans ?_ hy)
    exact_mod_cast Nat.cast_le.mpr hU1
  · intro X hX
    refine mrt_tail_le_of_HplusStar hε (le_trans ?_ hX)
    exact_mod_cast Nat.cast_le.mpr hg

/-- **The 34-lane floors on the live composed exit (E34 V4)** — twin of
`m4_exit_socket_split_sq_arc_at_mrt_floors` at `g := fun _ _ => H₊*₇₀(ε)`, tail payoff at
`1/70`.  ⛔ GLYPH GUARD, applied: the `50 ≤ loglog R.Hlo` antecedent below is the TOWER
THRESHOLD, not the tail rate — it does not move.  The payload block is copied byte-for-byte
from the exit's statement, exactly as its sibling's was.  Nothing here supplies the road's
own obligations. -/
theorem m4_exit_socket_split_sq_arc_at_mrt_floors_34 (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (q : ℚ) (K δ₀ : ℝ), 0 < q ∧ 0 < K ∧ 0 < δ₀ ∧
      ∃ R : ChowlaRegime, R.eps = q ∧
        H0mrt ε ≤ R.Hlo ∧ HplusStar70 ε ≤ R.x ∧
        (∀ y : ℝ, ((R.Hlo : ℕ) : ℝ) ≤ y →
            (Real.log (Real.log y)) ^ 2 / Real.log y ^ 2 ≤ ε) ∧
        (∀ X : ℝ, ((R.x : ℕ) : ℝ) ≤ X →
            1 / (Real.log X) ^ ((1 : ℝ) / 70) ≤ ε) ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          (∀ (a e : ℕ → ℂ) (Bsieve : ℕ → ℝ) (Binsert : ℝ),
            (∀ m, lamCoeff m = a m + e m) →
            (∀ H : ℕ, 0 ≤ Bsieve H) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
              NearRatTight (arcDen 12 H) H α →
                (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                  ≤ Bsieve H * (H : ℝ) ^ 2) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
                ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                  ∂(logMeasure R.x R.ω)) ≤ Binsert) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              K * (2 * Bsieve H) + 2 * Binsert ≤ δ₀) →
            ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨q, K, δ₀, hq, hK, hδ₀, hexit⟩ := m4_exit_socket_split_sq_arc
  obtain ⟨R, hReps, hU1, hg, htow, hbody⟩ :=
    hexit (H0mrt ε) (fun _ _ => HplusStar70 ε)
  refine ⟨q, K, δ₀, hq, hK, hδ₀, R, hReps, hU1, hg, ?_, ?_, htow, hbody⟩
  · intro y hy
    refine mrt_middle_le_of_H0mrt hε hε1 (le_trans ?_ hy)
    exact_mod_cast Nat.cast_le.mpr hU1
  · intro X hX
    refine mrt_tail_le_of_HplusStar70 hε (le_trans ?_ hX)
    exact_mod_cast Nat.cast_le.mpr hg

end Salt.MR

end
