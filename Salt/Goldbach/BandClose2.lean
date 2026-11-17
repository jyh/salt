/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.BandClose

/-!
# G-BANDCLOSE-2 — the aggregation supersession with a band-tail slot (A₃ band close, deliverable C)

`GeoSum.gold_hSum_geo` routes the band legs `PsymK 0 k'`/`PlowK 0 k'` STRICTLY into `Wband`, with NO
additive crumb slot (only the box `Price` leg carries `+ Btail`).  But the `Surv.lean` discharges
`gold_band_hsym_tail_discharge` / `gold_band_hlow_tail_discharge` deliver the band legs WITH a crumb
`+ Σ_k Σ_i goldBandBtailSlot` — order `N/L^{11}`, landing exactly where the box crumb is `0`
(high-pass = box-DEAD), so it cannot fold into the box `htail`.

This file landed (the `(C)` half of the `(C)+(D)+(5)` split) the theorem named below, which now
lives in `GeoSum`, directly above `gold_hSum_geo` (its instance at zero crumbs); this module keeps
the record and its importers:

* **`gold_hSum_geo_band`** — the `gold_hSum_geo` supersession: the band legs `hsym`/`hlow` carry
  per-leg crumbs `BTsym`/`BTlow` (`PsymK 0 k' ≤ Wband + BTsym k'`, `PlowK 0 k' ≤ Wband + BTlow k'`),
  and the routed sum `(1/2)·Σ BTsym + Σ BTlow` is discharged by an ENLARGED tail `hbandtail`
  (`≤ Ctail_band·Kc·N/L^{11}`).  SAME LHS aggregate as `gold_hSum_geo`; the conclusion constant
  gains `+ Ctail_band`.  The box legs (`hmain`, `hboxleg`) and diag are byte-for-byte the landed.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.

## Flagged (NOT closed here — see the G-BANDCLOSE report / `flags.md`)

* **(D) the tower close** — `Σ` of the per-box crumbs `goldBtailMinSlot` (box) + `goldBandBtailSlot`
  (band) over the `O(L²)` boxes × the annulus structure `≤ Ctail_total·Kc·N/(log N)^{11}`, via
  `Surv.gold_band_btail_slot_firing_le` and the firing criterion `X·M ≤ (D·L^{18})²`.  This is the
  `hbandtail`/`htail` input `gold_hSum_geo_band` consumes; the deficit-exponent estimate is a large
  standalone analytic obligation, NOT landed here.
* **(5) the terminal re-wire** — `gold_hBVblocksW_at_op_band`, the minimal-diff `Final2` terminal
  variant consuming (A)–(D): the band legs discharged via `gold_band_survsum_geoN_floored` (item 2)
  and `gold_hSum_geo_band` (now in `GeoSum`); residuals: the op rows + hCE/hNum/hdiag + constants.
  This edits the LANDED terminal aggregation and is Fable/house tier.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

end Salt.Goldbach
