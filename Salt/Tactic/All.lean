/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Tactic.AuditAxioms
import Salt.Tactic.EventuallyBudget

/-!
# Salt tactic toolkit — aggregate import

Project tactics per the ledger `docs/blueprints/tactics.md`. Landed:
`AuditAxioms` (T5 — the `#audit_axioms` build-time whitelist command) and
`EventuallyBudget` (T2 — the `∀ᶠ` threshold-stack combinators + the
`eventually_budget` macro).
-/
