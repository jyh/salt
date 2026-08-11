/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Certs.Vaughan
import Salt.Tactic.AuditAxioms

/-!
# `Salt/Certs/` — the comprehensibility-certificate layer, roll-call

Campaign: `saltworks/docs/cert-layer-design-0811.md`, opened at the Captain's word
2026-08-11 as the workflow's **fifth deliverable** (implementation · specification ·
proof · tests · **certificates**).

A certificate file restates one paper-cited headline claim in simplified, primitive
vocabulary and carries a **kernel proof linking the restatement to the landed
theorem** — the proof is what separates a certificate from documentation. Each file
declares its DIRECTION (`iff` where true, `←`-implication otherwise) and states in
its docstring exactly what, if anything, was traded for readability.

## LANDED
* `Salt/Certs/Vaughan.lean` — `cert_vaughan`, certifying `Salt.LS.vaughan`.
  Direction: **equality**, no generality traded. Names the three summands
  (`typeI`, `cross`, `typeII`) so the shape `Λ = TypeI − Cross + TypeII` is legible
  from the certificate alone. Its docstring also records that this corpus claims
  **no priority** on Vaughan's identity (independently and publicly formalized
  earlier — see the file).

## OWED (target list v1, ≈14 salt files)
`bounded_gaps_unconditional` · `chen_headline` · `chen_goldbach` · `gaps_le_twelve`
· `siegelWalfisz_holds` · `analytic_LS + char_LS` · `zeta_zero_free_region_pow` ·
`vmvt` (the likely class-C translation; maestro owns it) ·
`norm_kloosterman_estermann` · `twin_bar/no_twin_weight/least_k_theorem` ·
`sufficient_true_not_parityInv` · `log_chowla_two_door_only` · `psiTot_pnt`.

⚠️ **ROOTING IS NOT DONE AND IS NOT THIS SEAT'S TO DO.** `Salt.lean` does not yet
import `Salt.Certs.All`; reported to the maestro rather than added here, per the
root-is-maestro-only law. Until that line lands, this tree is built by naming the
file, not by the hub build.
-/

open Salt.Tactic in
#audit_axioms Salt.Certs.cert_vaughan
