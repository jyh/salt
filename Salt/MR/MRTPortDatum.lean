/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MRTProp24
import Salt.MR.M4Exit

/-!
# N4 — `lamCoeff` inhabits MRT's 1-bounded completely multiplicative datum

Item 15, node N4 of the MRT port (design block
`seat/briefs/2026-08-24-item15-mrt-port-DESIGN-BLOCK-v6.md`, §4).  One theorem:
the Liouville coefficient sequence `lamCoeff` (`M4Window.lean:73`) satisfies
`MrtCompMultDatum` (`MRTProp24.lean:195-201`), the structure that packages MRT's
"1-bounded completely multiplicative" hypothesis.

All three fields come off the `liouvilleC` arm of the corpus, transported by the
spelling bridge `lamCoeff_eq_liouvilleC` (`M4Exit.lean:99`, which is `rfl`):

| field | discharged by |
|---|---|
| `map_one : g 1 = 1` | `liouvilleC_one` (`M4Residue.lean:96`) |
| `map_mul : ∀ m n, m ≠ 0 → n ≠ 0 → g (m*n) = g m * g n` | `liouvilleC_mul` (`M4Residue.lean:103`) |
| `norm_le_one : ∀ n, ‖g n‖ ≤ 1` | `liouvilleC_norm_le_one` (`M4Residue.lean:121`) |

`liouvilleC_mul` is the **unconditional** form `liouvilleC (m*n) = liouvilleC m *
liouvilleC n`, with no `m ≠ 0` / `n ≠ 0` side conditions at all — strictly
stronger than the field asks for.  The two hypothesis binders are therefore
consumed and discarded (`fun m n _ _ => …`); stronger discharges weaker.

⚠️ **Statement-level caution, recorded not acted on** (flagged to the helm in the
design block, §4, N4).  `MrtCompMultDatum` encodes **complete** multiplicativity —
that is Proposition 2.4's hypothesis (p. 10).  MRT **Theorem 1.7** (p. 6) asks only
for a 1-bounded **multiplicative** function.  Using this structure for a Theorem 1.7
port therefore **over-assumes**.  `lamCoeff` satisfies the stronger form, so this
node is true as stated and this file builds it exactly as stated; restating the
structure at the weaker hypothesis is a Fable/human-tier statement change.

⛔ This node closes a residual.  It does **not** compose to the door.
-/

namespace Salt.MR

/-- **N4.**  The Liouville coefficient sequence is a 1-bounded completely
multiplicative datum in MRT's sense.

Proof: `lamCoeff = liouvilleC` definitionally (`lamCoeff_eq_liouvilleC`, `rfl`),
then the three landed `liouvilleC` facts.  `liouvilleC_mul` carries no
nonvanishing hypotheses, so the structure's `m ≠ 0` / `n ≠ 0` binders are
consumed unused. -/
theorem mrtCompMultDatum_lamCoeff : MrtCompMultDatum lamCoeff := by
  rw [lamCoeff_eq_liouvilleC]
  exact
    { map_one := liouvilleC_one
      map_mul := fun m n _ _ => liouvilleC_mul m n
      norm_le_one := liouvilleC_norm_le_one }

end Salt.MR
