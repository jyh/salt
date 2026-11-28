/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.Targets

/-!
# O90 stage 2 — the two reuse variants (statements only)

The reuse half of O90's stage-2 reader test asks for a proof of a statement that the landed
O106 theorems do not give by application, so that writing it needs their proofs read. Each
variant below is a landed theorem with every log power raised by one, written as a `def … : Prop`
so that nothing here asserts it and no `sorry` is needed:

* `O90VariantPiLi` is `piLi2_two_of_vonKoch` (PiLi.lean, `VonKochPsi 3 → PiLi2 2`) one power up;
* `O90VariantCramer` is `cramerGap_of_vonKoch` (Cramer.lean, `VonKochPsi 3 → CramerGap 3`) one
  power up.

Why the originals do not apply: the variants' hypothesis `VonKochPsi 4` is weaker than the
originals' `VonKochPsi 3`, and no landed theorem goes from `VonKochPsi 4` to either conclusion.
Whether either is a short composition of landed facts is the audit's question, not a claim here.
-/

namespace Salt.RH

/-- **V1.** `piLi2_two_of_vonKoch` one power up: from `|ψ(x) − x| ≤ C √x (log x)⁴` for `x ≥ 2`,
`|π(x) − Li₂(x)| ≤ C' √x (log x)³` for `x ≥ 2`. -/
def O90VariantPiLi : Prop :=
  VonKochPsi 4 → PiLi2 3

/-- **V2.** `cramerGap_of_vonKoch` one power up: from `|ψ(x) − x| ≤ C √x (log x)⁴` for `x ≥ 2`,
consecutive primes satisfy `p_{n+1} − p_n ≤ C' √p_n (log p_n)⁴`. -/
def O90VariantCramer : Prop :=
  VonKochPsi 4 → CramerGap 4

end Salt.RH
