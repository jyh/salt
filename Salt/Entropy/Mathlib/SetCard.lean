/-
Copyright (c) 2023 The Polynomial Freiman–Ruzsa (PFR) project contributors.
Released under the Apache License, Version 2.0; see the full license text in
`Salt/Entropy/LICENSE-PFR-Apache-2.0`.

Derivative work notice. This file is adapted from the Polynomial Freiman–Ruzsa
(PFR) project, upstream file `PFR/Mathlib/Data/Set/Card.lean`, at commit
a177b2e4abe4b31c8024b9afebe646bf6bb8f91b (upstream toolchain
`leanprover/lean4:v4.33.0-rc1`).

Original authors: Terence Tao and the PFR project contributors.

Modifications for Salt (ported to mathlib v4.32.0-rc1, toolchain
`leanprover/lean4:v4.32.0-rc1`):
- Converted the PFR module-system header (`module`, `public import`s of
  `Mathlib.Data.Set.Card`, `PFR.Mathlib.Data.Set.Basic`, and
  `PFR.Mathlib.Data.Set.Insert`, `public section`) to a plain `import Mathlib`.
  The two transitive PFR patch residues (`Basic`, `Insert`) supply no lemma
  needed by the two proofs here (both close by `split_ifs <;> simp [*]`), so
  they are not ported.
- All declarations, names, and proof bodies are otherwise verbatim from upstream.
-/
import Mathlib

namespace Set
variable {α : Type*}

-- TODO: Rename `ncard_singleton_inter` to `ncard_singleton_inter_le_one`

lemma ncard_singleton_inter' (a : α) (s : Set α) [Decidable (a ∈ s)] :
    ({a} ∩ s).ncard = if a ∈ s then 1 else 0 := by
  split_ifs <;> simp [*]

lemma ncard_inter_singleton (a : α) (s : Set α) [Decidable (a ∈ s)] :
    (s ∩ {a}).ncard = if a ∈ s then 1 else 0 := by
  split_ifs <;> simp [*]

end Set
