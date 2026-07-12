/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.Defs
import Salt.BV.MaxReduction
import Salt.BV.SWChar
import Salt.BV.MaxLS
import Salt.BV.SWMaxY
import Salt.BV.PolyaVinogradov
import Salt.BV.Completion
import Salt.BV.TypeI
import Salt.BV.BilinearLS
import Salt.Tactic.AuditAxioms
import Salt.BV.DivisorSum

/-!
# The BV rung (`bv`) — aggregate import

Bombieri–Vinogradov modulo the single named `SiegelWalfisz` gate. Design:
`docs/blueprints/bv.md`. Extended as modules land; wired into `Salt.lean`
from the first commit so the bare `lake build` covers the track.

Landed: `Defs` (V0.1 — the frozen carrier `SiegelWalfisz` + trivia:
monotonicity in the saving exponent `A`, the `q = 1` instance recovering an
unconditional bound on `psiTot`, and the `a`/`a % q` coprimality
normalization); `DivisorSum` (V1b — the divisor summatory bound
`sum_card_divisors_le` `Σ τ(n) ≤ x(1 + log x)` via the mathlib hyperbola
identity `sum_Ioc_sigma0_eq_sum_div`, plus the ℓ²-flavored corollary
`sum_log_sq_le`).
-/

-- Build-time axiom audit (T5 adoption): a stray axiom in the BV track fails
-- `lake build` here, not just the out-of-band lint.
open Salt.Tactic in
#audit_axioms Salt.BV.sum_card_divisors_le Salt.BV.psiAP_discrepancy_le
  Salt.BV.psiAP_discrepancy_sup'_le Salt.BV.siegelWalfisz_psiTot
  Salt.BV.psiChi_le_of_siegelWalfisz Salt.BV.psiChi_le_of_siegelWalfisz_absorbed
  Salt.BV.norm_psiChi_one_sub_psiTot_le Salt.BV.char_LS_max
  Salt.BV.sup_div_log_pow_le Salt.BV.polya_vinogradov
  Salt.BV.fourierCutoff_indicator Salt.BV.sum_norm_fourierCutoff_le
  Salt.BV.bilinear_factorization Salt.BV.typeI_one_maxdisc_le
  Salt.BV.typeI_two_maxdisc_le Salt.BV.bilinear_LS_shell
