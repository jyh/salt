/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.ShiuS5b

/-!
# The GEH door — the `hshiu` wire (node N-HDOM)

This file wires the freshly-proven Shiu core `sum_tau_in_ap_le : ShiuCore`
(`Salt/Maynard/ShiuS5b.lean`) into the shallow interface `hshiu` of the anchored
multiblock combinator `pieceObligationU_of_anchored_multiblock`
(`Salt/Maynard/GehAnchor.lean`, top-level namespace `GehAnchor`).

The combinator's `hshiu` slot (GehAnchor.lean:450–453), specialised to the vP3
double-dyadic family (`α i x = muBlock (a i x) x`, `β i x = tiiBlock (b i x) x`,
`N i x = nScale (a i x) x`, `M i x = nScale (b i x) x`, `θ = 3999/4000`), reads

    ∀ A' > 0, ∃ Bsh Csh, 0 ≤ Bsh ∧ ∀ x ≥ 3, ∀ i < m x,
      (2·nScale (a i x) x·nScale (b i x) x : ℝ) < x/(log x)^F → ∀ y ≤ x,
        ∑_{q ∈ [1, ⌊x^{3999/4000}/(log x)^Bsh⌋]}
            seqDiscrepancy (dconv (muBlock (a i x) x) (tiiBlock (b i x) x)) y q
          ≤ Csh·x/(log x)^{A'}.

`shiu_for_blocks_of_core` (ShiuBlocks.lean:312) delivers *exactly* this body — for
one fixed pair `(A', F)` subject to `A' + 3 ≤ F`.  Instantiating its per-pair `a b`
at `a i x`, `b i x` and reading `N i x, M i x` back as `nScale (a i x) x,
nScale (b i x) x` is a pure binder rename: the two wires below.

## Catch #54 (LIVE, recorded — the door does NOT close through this combinator)

The combinator's `hshiu` quantifies `A'` universally with a **single fixed `F`**
(the theorem parameter `{θ ε F : ℝ}`), and it invokes `hshiu (A + p)` for the
`PieceObligationU`-saving `A`, which ranges over *all* positive reals
(GehAnchor.lean:455–458).  But the honest Shiu bound needs `A' + 3 ≤ F`
(ShiuBlocks.lean:313; mathematically forced — a shallow block has `z ≤ x/(log x)^F`,
so its summed AP discrepancy is `≈ z·log³x ≈ x/(log x)^{F-3}`, which beats
`x/(log x)^{A'}` only for `F - 3 ≥ A'`).  A fixed finite `F` therefore caps the
attainable saving at `F - 3`, so `hshiu` at unbounded `A'` is **unprovable** with
fixed `F`.  The repair is a combinator signature change (`F : ℝ` → `F : ℝ → ℝ`,
the shallow threshold and split read at `F A'`), a **Fable/design-tier** edit of
the landed `GehAnchor.lean` — outside this executor node.

`hshiu_wire_sharp` below is the **fully `A'`-quantified** wire against the
`A'`-dependent threshold `F A' := A' + 3`: it is *exactly* what the re-cut
(F-as-a-function) combinator would consume, with no residual gate.  It demonstrates
that the analytic content is landed and the only remaining gap is the interface
rename in the combinator.
-/

namespace Salt.Maynard

open Finset

/-- **The `hshiu` wire, F-floor-gated (the honest general form).**  From the Shiu
core `sum_tau_in_ap_le`, for every saving `A' > 0` and every haircut floor `F` with
`A' + 3 ≤ F`, the vP3 double-dyadic family's shallow blocks satisfy the anchored
combinator's `hshiu` body.  This is `shiu_for_blocks_of_core` with the per-pair
anchors `(a, b)` read as the per-block-index anchors `(a i x, b i x)` — a pure
binder rename.  The extra `A' + 3 ≤ F` hypothesis is catch #54: the combinator's
`hshiu` slot omits it (fixed `F`, universal `A'`), so this does **not** plug in
until the combinator's `F` goes `A'`-dependent (Fable-tier). -/
theorem hshiu_shallow_of_core (m : ℕ → ℕ) (a b : ℕ → ℕ → ℕ) (F A' : ℝ)
    (hA' : 0 < A') (hFfloor : A' + 3 ≤ F) :
    ∃ Bsh Csh : ℝ, 0 ≤ Bsh ∧ ∀ x : ℕ, 3 ≤ x → ∀ i : ℕ, i < m x →
      ((2 * nScale (a i x) x * nScale (b i x) x : ℕ) : ℝ) < (x : ℝ) / Real.log x ^ F →
        ∀ y : ℕ, y ≤ x →
          (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / Real.log x ^ Bsh⌋₊,
              seqDiscrepancy (dconv (muBlock (a i x) x) (tiiBlock (b i x) x)) y q)
            ≤ Csh * (x : ℝ) / Real.log x ^ A' := by
  obtain ⟨Bsh, Csh, hBsh0, hbd⟩ := shiu_for_blocks_of_core sum_tau_in_ap_le A' F hA' hFfloor
  exact ⟨Bsh, Csh, hBsh0,
    fun x hx i _ hshallow y hyx => hbd x hx (a i x) (b i x) hshallow y hyx⟩

/-- **The `hshiu` wire, sharp (fully `A'`-quantified at the `A'`-dependent floor
`F A' := A' + 3`).**  This is precisely the `hshiu` obligation an F-as-a-function
re-cut of `pieceObligationU_of_anchored_multiblock` would demand — the Shiu core
discharges it with **no residual gate**.  Concretely: for every `A' > 0` there is a
haircut `Bsh` and constant `Csh` so that every vP3 double-dyadic block whose anchor
is `A'`-shallow (`2·N·M < x/(log x)^{A'+3}`) has its summed AP discrepancy
`≤ Csh·x/(log x)^{A'}`.  The whole analytic debt of `hshiu` is thereby landed; only
the combinator's fixed-`F` interface (catch #54) stands between this and the door. -/
theorem hshiu_wire_sharp (m : ℕ → ℕ) (a b : ℕ → ℕ → ℕ) :
    ∀ A' : ℝ, 0 < A' → ∃ Bsh Csh : ℝ, 0 ≤ Bsh ∧ ∀ x : ℕ, 3 ≤ x → ∀ i : ℕ,
      i < m x → ((2 * nScale (a i x) x * nScale (b i x) x : ℕ) : ℝ)
          < (x : ℝ) / Real.log x ^ (A' + 3) →
        ∀ y : ℕ, y ≤ x →
          (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / Real.log x ^ Bsh⌋₊,
              seqDiscrepancy (dconv (muBlock (a i x) x) (tiiBlock (b i x) x)) y q)
            ≤ Csh * (x : ℝ) / Real.log x ^ A' :=
  fun A' hA' => hshiu_shallow_of_core m a b (A' + 3) A' hA' (le_refl _)

end Salt.Maynard
