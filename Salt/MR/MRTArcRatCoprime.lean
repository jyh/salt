/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ClassPrice

/-!
# ⟦W1 · lane B⟧ — THE RATIONAL SPLIT WITH THE COPRIME HEAD KEPT WHOLE (`MRTArcRatCoprime`)

`M4ClassPrice.norm_absWindowSum_rat_le_class_sums` prices the window sum at a rational `b/q`
by the triangle inequality over **all** `q` classes, one norm per class.  That is the right
move for the non-coprime residues — they are served by ⟦BRIDGE 3⟧'s `d₀`-dilation, class by
class — but it is the WRONG move for the coprime head: `M4Gauss`'s stratified consumer
(`norm_sq_coprime_window_le`) eats the coprime residues **as a single sum**, phases and all,

`‖∑_{(r,q)=1} e(br/q) · ∑_{m ≡ r (q)} a(m)‖`,

because the Gauss-sum saving lives in the cancellation *between* those `q`-coprime terms.
Splitting them apart first destroys exactly the quantity the consumer is built to exploit.

So this file lands the one split that keeps both halves in their consumers' shapes: the
coprime head **un-split, inside one norm**, and the non-coprime tail **fully split, one norm
per class**.  Nothing else — no arc hypothesis, no 1-boundedness, no datum, no `λ`, and no
constraint relating `K` to `q`.  Road-neutral by construction.

## The route (four landed pieces, no new mathematics)

1. `M4BridgeResidue.absWindowSum_residue_split` at `θ = 0` — the residue-class split at a
   *general* coefficient sequence.
2. `M4ClassPrice.classPhaseSum_zero` — at the zero residual frequency the class carrier is
   the bare class sum `∑_{m ∈ windowClass} a m`; no `e(·)` survives.
3. `Finset.sum_filter_add_sum_filter_not` — the `r`-sum cut at `Nat.Coprime q r`.
4. `norm_add_le`, then `norm_sum_le` + `M4BridgeResidue.norm_ratPhase` on the tail only.

The asymmetry between the two legs is the whole content: step 4's triangle inequality is
applied to the tail and **withheld** from the head.
-/

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **THE RATIONAL SPLIT WITH THE COPRIME HEAD KEPT WHOLE.**  At `α = b/q` with `0 < q`, and
at a *general* coefficient sequence `a : ℕ → ℂ`,

`‖∑_{n<m≤n+K} a(m) e((b/q)m)‖
  ≤ ‖∑_{(r,q)=1} e(br/q) ∑_{m≡r (q)} a(m)‖
    + ∑_{(r,q)>1} ‖∑_{m≡r (q)} a(m)‖`.

The head is the exact object `M4Gauss.norm_sq_coprime_window_le` consumes (same phases, same
single norm); the tail is one bare class sum per non-coprime residue, the shape ⟦BRIDGE 3⟧'s
dilation takes.  Compare `M4ClassPrice.norm_absWindowSum_rat_le_class_sums`, which triangles
over *all* `q` classes and so cannot reach the Gauss consumer. -/
theorem norm_absWindowSum_rat_le_coprime_head_add (a : ℕ → ℂ) (K n : ℕ) {q : ℕ}
    (hq : 0 < q) (b : ℤ) :
    ‖absWindowSum a K n ((b : ℝ) / (q : ℝ))‖
      ≤ ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
            ratPhase b q r * ∑ m ∈ windowClass K n q r, a m‖
        + ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
            ‖∑ m ∈ windowClass K n q r, a m‖ := by
  -- (1)+(2): the split at `θ = 0`, with the class carriers identified as bare class sums.
  have hsplit : absWindowSum a K n ((b : ℝ) / (q : ℝ))
      = ∑ r ∈ Finset.range q, ratPhase b q r * ∑ m ∈ windowClass K n q r, a m := by
    have h := absWindowSum_residue_split a K n hq b 0
    rw [add_zero] at h
    simpa only [classPhaseSum_zero] using h
  -- (3): cut the `r`-sum at coprimality, both legs still carrying their phases.
  have hcut : ∑ r ∈ Finset.range q, ratPhase b q r * ∑ m ∈ windowClass K n q r, a m
      = (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
            ratPhase b q r * ∑ m ∈ windowClass K n q r, a m)
        + ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
            ratPhase b q r * ∑ m ∈ windowClass K n q r, a m :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- (4): the tail only — the unimodular phases drop, one norm per non-coprime class.
  have htail : ‖∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
        ratPhase b q r * ∑ m ∈ windowClass K n q r, a m‖
      ≤ ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
            ‖∑ m ∈ windowClass K n q r, a m‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun r _ => by rw [norm_mul, norm_ratPhase, one_mul]
  -- Triangle the OUTER sum, then spend `htail` on the tail; the head is left whole.
  rw [hsplit, hcut]
  exact (norm_add_le _ _).trans (by linarith)

end Salt.MR
