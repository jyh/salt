/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Summit2
import Mathlib.Data.Set.Card

/-!
# COMPREHENSIBILITY CERTIFICATE — the Vinogradov mean value theorem

Campaign: `saltworks/docs/cert-layer-design-0811.md` (the fifth deliverable).
Landed theorem certified: `Salt.Vmvt.vmvt` (`Salt/Vmvt/Summit2.lean:151`); audit
`Salt/Vmvt/All.lean:39`. Paper anchors (`docs/CERT-ANCHORS-0811.md`, row 9):
**Pi `thm:vmvt`** (`main.tex:311`) with the Appendix A decode (`:986–1002`), and
**Nature draft :202–203** (the census row — *"the Vinogradov
mean value theorem"*; the quote is the renumber-proof half of a line pin in a
label-free markdown draft, and the phrase WRAPS across the two lines, so a
single-line grep false-negatives on it — probe by either half). The Appendix A decode stops at the *named*
definitions (`VmvtBound`, `JkI`, `vmvtExp`, `vmvtEta`); this certificate finishes the
decode — every corpus name is replaced by primitive vocabulary, and the replacement is
kernel-proved, not asserted.

## WHAT THE THEOREM SAYS, in one sentence
**For `k ≥ 2`, `r ≥ 1`, `x ≥ 1`, the number of pairs `(m, n)` of `(k·r)`-tuples of
integers from `{1, …, x}` whose power sums agree at every degree `1, …, k` — that is,
`∑ᵢ mᵢʲ = ∑ᵢ nᵢʲ` for `1 ≤ j ≤ k` — is at most
`k^(24k²r) · x^(2rk − k(k+1)/2 + η)` with `η = (k²/2)·(1 − 1/k)^r`.**

Why the exponent shape is the whole content: the diagonal pairs `(m, m)` alone
contribute `x^{kr}` solutions and the trivial count is `x^{2kr}`, so the theorem's
value is the *saving* in the exponent — as `r` grows, `η → 0` and the bound approaches
`x^{2rk − k(k+1)/2}`, a saving of nearly `x^{k(k+1)/2}` over trivial. This is
Theorem 24.5 of Vaughan's notes (the Linnik–Karatsuba elementary induction), the
classical form of the VMVT — the engine behind the corpus's Weyl-sum estimates
(Pi `thm:pow` consumes it).

## THE VOCABULARY, unfolded (and kernel-tied by `cert_vmvt_iff`)
* `JkI k (k·r) x` — the interval solution count — becomes a literal set-builder count:
  pairs of tuples `mn : (Fin (k·r) → ℤ) × (Fin (k·r) → ℤ)`, each entry bounded by
  `1 ≤ · ≤ x`, power sums agreeing at every degree `1 ≤ j ≤ k`, counted by `Set.ncard`.
  The chain `JkI → Jk → solSet → PowerSumEq` (`Salt/Vmvt/Defs.lean`) is walked by the
  proof of the iff; no `Salt.*` name survives into the certificate statement.
* `vmvtConst k r = (k^(24k²))^r` collapses to the single power **`k^(24k²r)`**
  (`pow_mul`). ⚠️ **This constant is house-RE-GRADED, generous by design** (VMVT-R5b /
  SUMMIT-2, 2026-07-18): the induction's own per-step constant `k⁶·k!·2^(k²)·3` sits
  below `k^(24k²)` (`old_c0_le`), and the source leaves `D(k,r)` free ("constants
  utterly free, track honestly"). **No sharpness is claimed or should be read.**
* `vmvtExp k r` and `vmvtEta k r` are inlined as the visible exponent
  `2rk − k(k+1)/2 + (k²/2)·(1 − 1/k)^r`. **The exponent is the load-bearing half and
  matches the source EXACTLY** — this is where nothing may be (and nothing is) traded.

## DIRECTION (rule 3)
`cert_vmvt` is an **implication, cert ← landed theorem**, proved from `Salt.Vmvt.vmvt`.
**Nothing is traded, and that is kernel-proved, not asserted**: `cert_vmvt_iff` states
`Salt.Vmvt.VmvtBound k r x` — the landed conclusion, by name — equivalent to the
certificate body, **for ALL `k r x` with no hypotheses**. The equivalence is pure
decoding (definitional unfolding + `pow_mul` + `ring`); the hypotheses are needed to
*prove* the bound, never to *state* it.

## HYPOTHESES — three, all stated, all live (rule 6)
`2 ≤ k` (the source's range; `k = 0, 1` are degenerate for a degree-`k` system),
`1 ≤ r` (at least one induction step), `1 ≤ x` (a nonempty interval). This is the
cert layer's **first hypothesis-carrying certificate**, so the vacuity control is
discharged in-file: the packet is satisfiable, witnessed by instantiating the
certificate itself at the smallest admissible point `(k, r, x) = (2, 1, 1)`.

## WHAT THIS CERTIFICATE DOES **NOT** CLAIM (rule 2)
* **No sharpness of the constant** — see the re-grade warning above. `k^(24k²r)` is an
  upper bound the induction affords, not a measured quantity.
* **Not the main-conjecture VMVT.** The exponent carries the classical Linnik–Karatsuba
  decay `η(k,r) = (k²/2)(1−1/k)^r`, **not** the `ε`-form of the resolved main
  conjecture (Bourgain–Demeter–Guth / Wooley). Pi `thm:vmvt`'s claim is the explicit
  classical theorem, and that is what is certified.
* **Interval form only.** The count is over the interval `{1, …, x}` (the consumer's
  `JkI`), exactly as the landed theorem states it; the corpus's general-set `Jk` API
  is not restated here.
* **No priority language.** The certificate's whole content is: this proposition is
  proved, from the stated three hypotheses alone.

## AXIOMS
`#print axioms` for both declarations ⇒ `[propext, Classical.choice, Quot.sound]`
(the standard three; recorded at the landing of this file).
-/

namespace Salt.Certs

open Finset

/-- **THE NO-TRADE CHECK.** For every `k`, `r`, `x` — no hypotheses — the landed
conclusion `Salt.Vmvt.VmvtBound k r x` and the certificate's body are the *same
proposition*: the corpus names (`JkI`/`Jk`/`solSet`/`PowerSumEq`, `vmvtConst`,
`vmvtExp`/`vmvtEta`) decode to the set-builder count, the single power `k^(24k²r)`,
and the inline exponent, with nothing lost in either direction. This is what licenses
the phrase "nothing is traded" in the header. -/
theorem cert_vmvt_iff (k r x : ℕ) :
    Salt.Vmvt.VmvtBound k r x ↔
      (({ mn : (Fin (k * r) → ℤ) × (Fin (k * r) → ℤ) |
            (∀ i, 1 ≤ mn.1 i ∧ mn.1 i ≤ (x : ℤ)) ∧
            (∀ i, 1 ≤ mn.2 i ∧ mn.2 i ≤ (x : ℤ)) ∧
            ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, mn.1 i ^ j = ∑ i, mn.2 i ^ j }.ncard : ℝ)
        ≤ (k : ℝ) ^ (24 * k ^ 2 * r) *
            (x : ℝ) ^ (2 * (r : ℝ) * (k : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2
              + (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ r)) := by
  have hset :
      { mn : (Fin (k * r) → ℤ) × (Fin (k * r) → ℤ) |
          (∀ i, 1 ≤ mn.1 i ∧ mn.1 i ≤ (x : ℤ)) ∧
          (∀ i, 1 ≤ mn.2 i ∧ mn.2 i ≤ (x : ℤ)) ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, mn.1 i ^ j = ∑ i, mn.2 i ^ j }
        = ↑(Salt.Vmvt.solSet k (k * r) (Finset.Ioc (0 : ℤ) (x : ℤ))) := by
    ext mn
    rw [Finset.mem_coe, Salt.Vmvt.mem_solSet]
    simp only [Set.mem_setOf_eq, Finset.mem_Ioc, Salt.Vmvt.PowerSumEq,
      Finset.mem_Icc, and_imp]
    constructor <;>
      exact fun ⟨h1, h2, h3⟩ =>
        ⟨fun i => ⟨by have := (h1 i).1; omega, (h1 i).2⟩,
         fun i => ⟨by have := (h2 i).1; omega, (h2 i).2⟩, h3⟩
  have hcard :
      (({ mn : (Fin (k * r) → ℤ) × (Fin (k * r) → ℤ) |
            (∀ i, 1 ≤ mn.1 i ∧ mn.1 i ≤ (x : ℤ)) ∧
            (∀ i, 1 ≤ mn.2 i ∧ mn.2 i ≤ (x : ℤ)) ∧
            ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, mn.1 i ^ j = ∑ i, mn.2 i ^ j }.ncard : ℝ))
        = (Salt.Vmvt.JkI k (k * r) x : ℝ) := by
    rw [hset, Set.ncard_coe_finset]
    rfl
  have hconst : Salt.Vmvt.vmvtConst k r = (k : ℝ) ^ (24 * k ^ 2 * r) := by
    unfold Salt.Vmvt.vmvtConst Salt.Vmvt.vmvtC0
    rw [← pow_mul]
  have hexp :
      Salt.Vmvt.vmvtExp k r
        = 2 * (r : ℝ) * (k : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2
            + (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ r := by
    unfold Salt.Vmvt.vmvtExp Salt.Vmvt.vmvtEta
    ring
  unfold Salt.Vmvt.VmvtBound
  rw [hconst, hexp, ← hcard]

/-- **THE CERTIFICATE — the Vinogradov mean value theorem, decoded.**
For `k ≥ 2`, `r ≥ 1`, `x ≥ 1`: the number of pairs of `(k·r)`-tuples of integers
from `{1, …, x}` whose power sums agree at every degree `1, …, k` is at most
`k^(24k²r) · x^(2rk − k(k+1)/2 + (k²/2)(1−1/k)^r)`. The constant is house-graded
(generous by design — header ⚠️); the exponent matches Vaughan's Theorem 24.5 exactly.
Proved from `Salt.Vmvt.vmvt` through the unconditional decoding `cert_vmvt_iff`. -/
theorem cert_vmvt (k r x : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) (hx : 1 ≤ x) :
    (({ mn : (Fin (k * r) → ℤ) × (Fin (k * r) → ℤ) |
          (∀ i, 1 ≤ mn.1 i ∧ mn.1 i ≤ (x : ℤ)) ∧
          (∀ i, 1 ≤ mn.2 i ∧ mn.2 i ≤ (x : ℤ)) ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, mn.1 i ^ j = ∑ i, mn.2 i ^ j }.ncard : ℝ)
      ≤ (k : ℝ) ^ (24 * k ^ 2 * r) *
          (x : ℝ) ^ (2 * (r : ℝ) * (k : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2
            + (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ r)) :=
  (cert_vmvt_iff k r x).mp (Salt.Vmvt.vmvt k r x hk hr hx)

/-- **Rule-6 vacuity control** (first hypothesis-carrying certificate): the hypothesis
packet is satisfiable — the certificate instantiates at `(k, r, x) = (2, 1, 1)`. -/
theorem cert_vmvt_witness : Salt.Vmvt.VmvtBound 2 1 1 :=
  Salt.Vmvt.vmvt 2 1 1 (by norm_num) (by norm_num) (by norm_num)

/-- The cert-form instantiation follows by `(cert_vmvt_iff 2 1 1).mp
cert_vmvt_witness`; the named theorem above is what the axiom census reads. -/
example := (cert_vmvt_iff 2 1 1).mp cert_vmvt_witness

#print axioms cert_vmvt_iff
#print axioms cert_vmvt
#print axioms cert_vmvt_witness

end Salt.Certs
