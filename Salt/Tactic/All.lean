/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Tactic.AuditAxioms
import Salt.Tactic.EventuallyBudget
import Salt.Tactic.DyadicRec

/-!
# Salt tactic toolkit — aggregate import

Project tactics per the ledger `docs/blueprints/tactics.md`. Landed:
`AuditAxioms` (T5 — the `#audit_axioms` build-time whitelist command) and
`EventuallyBudget` (T2 — the `∀ᶠ` threshold-stack combinators + the
`eventually_budget` macro); `DyadicRec` (T6/T9 — the dyadic-assembly
schema: `dyadic_cover_sum_le(_range)` fibering, the `geom_sum_le_top/bot`
domination quartet, and the `dyadic_interval_rec` eliminator;
verified against four landed consumers).
-/
