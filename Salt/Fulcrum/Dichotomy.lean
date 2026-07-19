/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Fulcrum.Basic
import Salt.Fulcrum.Gadget

/-!
# THE FULCRUM DICHOTOMY — the crown, kernel-real (`fulcrum`)

Design / provenance: `docs/exploration/fulcrum-pass3.md` (THE HUNT VERDICT, Pass 3,
commission D1 "MAKE THE DICHOTOMY KERNEL-REAL") and `docs/exploration/pass2_e2.md`
§0 Form A (the kernel-composable route). This module lands the **dichotomy itself**
on top of the already-landed fulcrum surfaces — additively, touching nothing.

The organizing statement of the whole fulcrum program is the trivial excluded
middle `FulcrumQualityMin C ∨ ¬ FulcrumQualityMin C`. What makes it a *theorem*
worth stating is what each horn *delivers*:

## The two horns

* **Horn `¬F` — LANDED, KERNEL-REAL TODAY.** `not_fulcrum_implies_noSiegelZeros`:
  `¬ FulcrumQualityMin C → NoSiegelZeros` for any `C > 0`. This is the campaign
  stone. It is a pure propositional composition of kernel-checked pieces:
  contrapose, feed the resulting `InfinitelyManySiegelZeros` through the landed
  compactness gadget `imsz_gives_fulcrum_witnesses` (`Salt/Fulcrum/Gadget.lean`)
  to recover `FulcrumQualityMin C` (its conclusion at a fixed `C` is DEFEQ to
  `FulcrumQualityMin C` — the gadget's `∀C` binder sits outside), contradicting
  `¬F`; the wrapper `noSiegelZeros_iff_not_infinitely`
  (`Salt/TwinBar/SiegelTwin.lean`) turns `¬ IMSZ` into `NoSiegelZeros`. HONEST
  SHAPE (pass2_e2 §0 Form A): the `∃c` obtained this way is a BARE existential —
  the below-`Q` isolation radii come from the cheap-ball continuity route, no
  rate. `NoSiegelZeros` is an *effective-gap* currency; it does not cross the
  parity barrier `Z` (verdict §"THE CAMPAIGN RE-PRICED", horn `¬F`).

* **Horn `F` — CONDITIONAL on the (unbuilt) Heath-Brown engine.** A fulcrum
  witness family `FulcrumQualityMin C` manufactures twin primes only through the
  Heath-Brown engine at threshold `C`, formalized here as the hypothesis
  `hEngine : FulcrumQualityMin C → TwinPrimeConjecture`. That engine is NOT
  proven — it is the future HB-L2c node (the analytic μ↔χ correlation at the
  fulcrum's one fixed strength; cf. `HeathBrownStatement`, the Siegel-side
  sibling `IMSZ → TPC`). So the composite below carries the engine as an explicit,
  honestly-labeled hypothesis. WALL-4 (verdict) prices this horn: even when the
  engine lands, its twin yield sits at a *forced* exp-exp threshold `C⁽¹⁾`.

## The composite (PROVABLE TODAY)

`fulcrum_dichotomy`: given the engine hypothesis, `HeathBrownDichotomy`
(`= TwinPrimeConjecture ∨ NoSiegelZeros`). On the `F` branch the engine fires
(left horn); on the `¬F` branch `not_fulcrum_implies_noSiegelZeros` fires (right
horn). This is the *honest* dichotomy: it does NOT overstate a twin consequence.

## What upgrades when Horn A closes

When HB-L2c lands `FulcrumQualityMin C⋆ → TwinPrimeConjecture` unconditionally at
the calibrated constant `C⋆`, instantiate `hEngine` at that term and `C := C⋆`:
`fulcrum_dichotomy` then becomes the UNCONDITIONAL dichotomy
`TwinPrimeConjecture ∨ NoSiegelZeros`. Until then, the *only* unconditional half
is the `¬F` horn — and by the honest-shape law (verdict) neither horn is presented
as a twin route: `¬F` pays purely in effectivity, `F` purely in window twins at
astronomically ineffective thresholds. Neither crosses `Z`.
-/

open Salt.TwinBar

namespace Salt.Fulcrum

/-- **HORN `¬F` — the dichotomy's kernel-real half** (verdict D1, pass2_e2 §0
Form A). For any `C > 0`, the failure of the fulcrum hypothesis
`FulcrumQualityMin C` yields the effective no-Siegel-zeros gap `NoSiegelZeros`.

Route (the contrapositive of the landed machinery): `NoSiegelZeros` is defeq to
`¬ InfinitelyManySiegelZeros` (`noSiegelZeros_iff_not_infinitely`); assuming
`InfinitelyManySiegelZeros`, the landed compactness gadget
`imsz_gives_fulcrum_witnesses` delivers a term whose type is DEFEQ to
`FulcrumQualityMin C` (checked by the `have hF` below), contradicting `hnF`.

HONEST SHAPE: the produced `NoSiegelZeros` constant is a bare existential from the
cheap-ball route — effective-in-`(Q, c(Q))` only in principle, no extracted
numeral (pass2_e2 §0 Form A caveat; owed at `Basic.lean:169`). -/
theorem not_fulcrum_implies_noSiegelZeros {C : ℝ} (hC : 0 < C)
    (hnF : ¬ FulcrumQualityMin C) : NoSiegelZeros := by
  rw [noSiegelZeros_iff_not_infinitely]
  intro himsz
  have hF : FulcrumQualityMin C := imsz_gives_fulcrum_witnesses himsz C hC
  exact hnF hF

/-- **THE FULCRUM DICHOTOMY (honest composite)** (verdict D1, the crown object).
Given the Heath-Brown engine at threshold `C` as an explicit hypothesis
`hEngine : FulcrumQualityMin C → TwinPrimeConjecture` (the unbuilt HB-L2c node),
the excluded middle on `FulcrumQualityMin C` delivers `HeathBrownDichotomy`
(`= TwinPrimeConjecture ∨ NoSiegelZeros`):

* `F` branch — the engine manufactures the Twin Prime Conjecture (left horn);
* `¬F` branch — `not_fulcrum_implies_noSiegelZeros` supplies the effective gap
  `NoSiegelZeros` (right horn).

When HB-L2c lands `hEngine` unconditionally at `C := C⋆`, this becomes the
UNCONDITIONAL dichotomy. The engine is carried as a hypothesis precisely so the
statement never overstates a twin consequence (honest-shape law, verdict). -/
theorem fulcrum_dichotomy {C : ℝ} (hC : 0 < C)
    (hEngine : FulcrumQualityMin C → TwinPrimeConjecture) :
    HeathBrownDichotomy := by
  by_cases hF : FulcrumQualityMin C
  · exact Or.inl (hEngine hF)
  · exact Or.inr (not_fulcrum_implies_noSiegelZeros hC hF)

end Salt.Fulcrum
