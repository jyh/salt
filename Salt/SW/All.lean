/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Defs
import Salt.SW.Kernel
import Salt.SW.Psi1Identity
import Salt.SW.ZeroCount
import Salt.Tactic.AuditAxioms

/-!
# The SW rung (`sw`) — aggregate import

Design: `docs/blueprints/sw.md`. THE project's remaining gate: discharge
`Salt.BV.SiegelWalfisz` (`Salt/BV/Defs.lean`), turning
`Salt.BV.bounded_gaps_of_siegelWalfisz` into UNCONDITIONAL bounded prime gaps.
The route is the Fable Riesz amendment (smooth `ψ₁` carrier, absolutely
convergent Mellin kernel) with error-#14's orthogonality-first de-smoothing.
Wired into `Salt.lean` from the first commit; extended as waves S1–S6 land.

## Landed (wave S0 — the Riesz carriers)

`Defs`:
* the carriers `psi1Chi` (ℂ character Riesz mean) and `psi1AP` (real AP Riesz
  carrier), conventions matching `Salt.LS.psiAP`, plus the floor bridge `psiAPr`;
* `psi1Chi_eq_sum_psi1AP` — the character expansion of the Riesz carrier;
* `psi1_fold` — the orthogonality fold `∑_χ χ̄(a)·ψ₁(x,χ) = φ(q)·ψ₁(x;q,a)` (the
  ψ₁-analog of the landed `Salt.BV.MaxReduction` identity; the algebraic half of
  S6's "orthogonality FIRST" order);
* `psi1AP_nonneg` and the first-difference sandwich `psi1AP_sandwich`
  (`psi1AP_sub_lower` / `psi1AP_sub_upper`) — the monotonicity hypothesis S6's
  de-smoothing consumes;
* `neg_logDeriv_LSeries_eq_LSeries_twist` — the `−L'/L = LSeries (χ·Λ)` identity
  on `Re s > 1` (re-export of mathlib's `LSeries_twist_vonMangoldt_eq`), the
  Dirichlet-series input S1 feeds through the Mellin/Perron identity.

## Gate reference

The frozen target is `Salt.BV.SiegelWalfisz` (unchanged since the BV rung). No
weakening to bounded `C` is permitted (Iron Rule 1): the effective-only route
reaches `C < 2` and is not the theorem. The `∃ K` top-level shape absorbs
Siegel's intrinsic ineffective constant.
-/

-- Build-time axiom audit (T5 adoption): a stray axiom in the SW track fails
-- `lake build` here, not only at out-of-band lint time.
open Salt.Tactic in
#audit_axioms Salt.SW.psi1Chi_eq_sum_psi1AP Salt.SW.psi1_fold
  Salt.SW.psi1AP_nonneg Salt.SW.psi1AP_sandwich
  Salt.SW.psi1AP_sub_lower Salt.SW.psi1AP_sub_upper
  Salt.SW.neg_logDeriv_LSeries_eq_LSeries_twist
  Salt.SW.kernel_identity Salt.SW.kernel_sum_swap
  Salt.SW.psi1_eq_integral Salt.SW.psi1_eq_integral_logDeriv
  Salt.SW.LFunction_center_lower Salt.SW.LFunction_zero_count_le
  Salt.SW.norm_deriv_le_of_re_le
