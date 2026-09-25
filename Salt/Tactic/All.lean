/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Tactic.AuditAxioms
import Salt.Tactic.EventuallyBudget
import Salt.Tactic.DyadicRec
import Salt.Tactic.CertEval
import Salt.Tactic.ExpLogNum
import Salt.Tactic.LogNum
import Salt.Tactic.NlinarithSuggest

/-!
# Salt tactic toolkit — aggregate import

Project tactics per the ledger `docs/blueprints/tactics.md`. Landed:
`AuditAxioms` (T5 — the `#audit_axioms` build-time whitelist command) and
`EventuallyBudget` (T2 — the `∀ᶠ` threshold-stack combinators + the
`eventually_budget` macro); `DyadicRec` (T6/T9 — the dyadic-assembly
schema: `dyadic_cover_sum_le(_range)` fibering, the `geom_sum_le_top/bot`
domination quartet, and the `dyadic_interval_rec` eliminator;
verified against four landed consumers); `ExpLogNum` (T3 first cut, rung (a) —
seven lemmas closing numeral `exp`/`log` bounds at integer exponent in one line each, with
red-first selftests and refusal arms; first consumer `Salt.MR.s13_smallGradeFits_h_L`, from the
O15 census of 2026-09-24); `LogNum` (T3 cut 2, rung (a) — five lemmas closing base-2 decimal
`log` bounds and the identity `log (b ^ k) = k * log b` in one line each, with selftests and
refusal arms; the `log 2` route `ExpLogNum` declared a later cut, from the O15 pull-3 census of
2026-09-25); `NlinarithSuggest` (T3 second cut — `nlinarith?`, certificate replay:
runs `nlinarith`'s search once and prints the verified `nlinarith only [...]` / `linarith only
[... products]` call that replays it; provenance-carrying preprocessing; from the O15 price brief
of 2026-09-25).
-/
