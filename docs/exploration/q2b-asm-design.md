# Q2b N4-ASM DESIGN — the 4-D Fubini assembly (Fable draft, PRE-GATE)

*2026-07-15. Status: DESIGNED, NOT DISPATCHED. Per registration amendment
A1, N4-ASM runs in-sprint only if the parity wall (Q6a) closes first;
otherwise it is scheduled assembly debt. An adversarial gate MUST run on
this design before any dispatch (C-tier nodes). Sources: the Q2bc-recon
report (exploration ledger ~11:20) + the landed N4-CORE carriers
(Salt/TwinBar/FourBar.lean, 1d0b8e0).*

## Target

`four_bar : FourBar` — for continuous F on `R₄`,
`J₁₄ + J₂₄ + J₃₄ + J₄₄ ≤ (4/3)·log 4 · I₄`, discharging the Prop that
`no_quad_weight_of_fourBar` already consumes. This is the M₄ leg of the
A1 least-k theorem.

## The structural plan (from the recon, against the landed 3-D assembly)

Product shape `ℝ×(ℝ×(ℝ×ℝ))`; peel `t₁` at an extreme (the 3-D file's
trick — t₁ never leaves the association-first slot; the associativity
wall is never hit). Residual: a **size-s** 3-simplex `Δ₃(1−t₁)`. The four
peels reconcile to canonical `(t₄,t₃,t₂,t₁)` as:

- **J₁₄** (t₁ inner): canonical — free.
- **J₂₄** (t₂ inner, order t₄,t₃,t₁,t₂): inner-two swap with (t₃,t₄)
  fixed outer — the landed fixed-outer 2-D `simplex_swap_param` at size
  `1−t₃−t₄`, verbatim. No new 3-D machinery.
- **J₃₄ / J₄₄** (the deep peels): reduce to size-s 3-D reorderings on
  `(t₂,t₃,t₄)` — the size-parametrized analogues of
  `canonical_eq_region` / `w3order_eq_region`. **This is the new burden:
  the entire 3-D reduction layer (region↔iterated, psi, outer
  marginals, integrabilities) is hardwired to size 1 and must be
  parametrized by s.**

**Carrier orders consumed (POST-GATE, correction 1 applied 2026-07-15):**
J₁₄ outers t₄,t₃,t₂ (peel t₁ inner → canonical₃); J₂₄ outers t₄,t₃,t₁
(one plain inner-two swap (t₁,t₂) at size 1−t₃−t₄ → peel t₁ inner →
canonical₃); **J₃₄ outers t₁,t₂,t₄ (REORDERED by the gate — was
t₄,t₂,t₁, which left the t₃ marginal unreachable without an unbudgeted
size-s marginal-continuity lemma): peel t₁ outer → one plain inner-two
swap (t₄,t₃) at size 1−t₁−t₂ → w3order₃**; J₄₄ outers t₁,t₂,t₃ (peel
t₁ outer → w3order₃, no swap). Route census: {0,0,1,1} plain inner-two
swaps + the two size-s reduce3 lemmas; every t₁-peel is at an extreme
(the association slot never moves); NO marginal is ever swapped.

**Node-a deliverable signatures (PINNED, gate correction 2 — node b
consumes these verbatim, no renegotiation):**
- `Δ₃ (s : ℝ) : Set (ℝ × ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧
  0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 ≤ s}` with `Δ₃_one_eq_R₃ : Δ₃ 1 = R₃`
  (definitional; the s=1 regression anchor — gate correction 4; do NOT
  refactor the landed three_bar to consume size-s versions).
- `canonical_eq_region₃ (s) (hs : 0 ≤ s) (hF : ContinuousOn f (Δ₃ s)) :
  (∫ t₄ in 0..s, ∫ t₃ in 0..s−t₄, ∫ t₂ in 0..s−t₄−t₃, f t₂ t₃ t₄)
  = ∫ region (Δ₃ s)` — t₂ inner, mirroring the landed size-1 shape.
- `w3order_eq_region₃ (s) (hs : 0 ≤ s) (hF : …) :
  (∫ t₂ in 0..s, ∫ t₃ in 0..s−t₂, ∫ t₄ in 0..s−t₂−t₃, f t₂ t₃ t₄)
  = ∫ region (Δ₃ s)` — t₄ inner.
- `psi_eq₃ s`, `region_integrable₃ s`, size-s outer-marginal
  integrabilities: mirror the landed names with the `(s) (hs)` prefix.
- **The two slice-continuity lemmas (gate correction 3, owner: NODE A):**
  fix-one-var → `ContinuousOn … (Δ₃ s)` and fix-two-var →
  `ContinuousOn … (Δ s)` (consumed by J₂₄'s and J₃₄'s swaps) — cheap
  MapsTo-into-R₄ mirrors of slice_fix_t1/t3.

## Nodes

- **N4-ASM-a — the size-s 3-D reduction layer (C, THE RISK NODE,
  critical path for J₃₄/J₄₄).** Size-s `Δ₃ s` geometry (compact, closed,
  measurable), size-s psi-analogue, `canonical_eq_region₃ s`,
  `w3order_eq_region₃ s`, size-s outer-marginal integrabilities.
  **Anti-vacuity/regression obligation: instantiating s = 1 must
  recover the landed size-1 lemmas** (stated as `example`s), and the
  degenerate s = 0 case must be checked non-pathological (empty
  simplex, zero integrals — not false side-conditions).
- **N4-ASM-b — Δ₄ geometry + the 4-D reorderings (C).** `Δ₄`
  compact/closed/measurable; the t₁-marginal identity (psi₄); the four
  region↔iterated reductions (POST-GATE routes): J₁₄ via peel-t₁-inner
  + size-1 canonical₃; J₂₄ via `simplex_swap_param` + peel-t₁-inner +
  size-1 canonical₃; **J₄₄ via peel-t₁-outer + size-s w3order₃; J₃₄
  via peel-t₁-outer + one plain inner-two swap (t₄,t₃) at size
  1−t₁−t₂ + size-s w3order₃** (consumes N4-ASM-a). J₃₄'s route has no
  3-D mirror — it stays IN NODE B (gate: if it leaks to node c, c
  becomes B/C).
- **N4-ASM-c — the peel bounds + combine (B).** The four `J_m4_bound`
  (triple-nested `integral_mono_of_nonneg` + `sliceCS_m4` + nested
  marginal integrabilities), then `four_bar` and the unconditional
  `no_quad_weight`.

Dependency: a ∥ b's-geometry, then b, then c. Budget ~250–350k
tokens/node (TB3-ASM actual: 413k for the whole 3-D assembly; the
reduction layer roughly doubles here).

## Gate mandate (run before dispatch, adversarial)

1. Enumerate the four peel orders against canonical EXPLICITLY and
   verify each claimed reconciliation route is reachable (no fifth
   ordering hiding in the carrier defs; check FourBar.lean's actual
   outer orders character-by-character).
2. Stress the size-s statements jointly at s = 1 − t₁ ∈ [0,1]: the
   s = 0 degenerate case, the `0 ≤ s − a` side-condition family, and
   whether any size-s lemma is false at the boundary the way strict-z
   sifting was (the Q6a lesson: check small concrete instances).
3. Integrability side-conditions at variable size: every
   `IntervalIntegrable`/`Integrable` hypothesis in the size-1 layer,
   re-derived or re-hypothesized at size s — no silent strengthening.
4. Numeric sanity target for the assembled four_bar: a compiled
   spot-check on a concrete F (the tent analogue) if statable cheaply.

## Predicted friction (recon + N4-CORE)

The s-hypothesis proliferation (`0 ≤ s`, `0 ≤ s − a` linarith
side-goals threading s = 1 − t₁) is the dominant bookkeeping cost;
`indicator` preimage bookkeeping at `Icc 0 (s − ·)`; the eight Q2a
friction notes all recur. Finish on `lake build`, never `lake env lean`
alone.
