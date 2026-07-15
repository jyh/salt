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

**Carrier orders consumed (fixed by N4-CORE; re-fixable there without
touching the analytic core if the gate prefers):** J₁₄ outers t₄,t₃,t₂;
J₂₄ outers t₄,t₃,t₁; J₃₄ outers t₄,t₂,t₁; J₄₄ outers t₁,t₂,t₃.

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
  region↔iterated reductions: canonical via peel-t₁-inner + size-1
  reduce3; J₃₄/J₄₄ via peel-t₁-outer + **size-s** reduce3 (consumes
  N4-ASM-a); J₂₄ via `simplex_swap_param`.
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
