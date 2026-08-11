/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Certs.Vaughan
import Salt.Certs.ParityGap
import Salt.Certs.ZetaPowRegion
import Salt.Certs.ChowlaSpine
import Salt.Certs.BoundedGaps
import Salt.Certs.Chen
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

* `Salt/Certs/ParityGap.lean` — `cert_parity_gap`, certifying
  `Salt.Parity.sufficient_true_not_parityInv` (paper `thm:gap`). Direction:
  **same proposition**, nothing traded. Carries the mechanism in one line (the witness
  is `twinFree`, whose twin mass is identically `0`) and **reports that TWO of the four
  stated hypotheses are frozen and unused** in the landed proof — `1 ≤ A₀` and
  `E oneWeight` — so the result is strictly stronger than it is written as. Flagged for
  the design desk under iron rule 1; **not altered here.**

* `Salt/Certs/ZetaPowRegion.lean` — `cert_zeta_zero_free_pow`, certifying
  `Salt.Vk.zeta_zero_free_region_pow` (paper `thm:pow`). Direction: **contrapositive**,
  logically equivalent, nothing traded. States the result as *a region containing no
  zeros* rather than as an inequality satisfied by every zero — which is what the phrase
  "zero-free region" means — and records that **the `∃ c T₀` in the landed statement is
  not evidence of inexplicitness**: the chain bottoms out in `K = 8104`,
  `t₀ = exp (exp 100)`, so the paper's word "effective" is earned by the proof.

* `Salt/Certs/ChowlaSpine.lean` — `cert_log_chowla_door_only`, certifying
  `Salt.Entropy.Chowla.log_chowla_two_door_only` (paper `thm:spine`). Direction: **same
  proposition**, nothing traded. Both opaque predicates are **unfolded in place**:
  `MRTUniformity` becomes the explicit log-averaged bound over every window length and
  every frequency, and `¬ logChowla2Fails` becomes the Chowla bound
  `|∑ λ(n)λ(n+1)/n| ≤ ε·log ω` itself. *That the unfolded form closes by `exact` is the
  proof the unfolding is definitional, not merely plausible.* **TWO certs in this file** —
  `thm:spine` names two declarations under one label, and evidence's adequacy arm caught
  that the first version covered only one.

* `Salt/Certs/BoundedGaps.lean` — `cert_bounded_gaps` (+ `_iff`,
  `_infinitely_many`, `_infinitely_many_iff`), certifying
  `Salt.SW.bounded_gaps_unconditional`. Direction: **implication from the landed
  theorem, with the no-trade claim KERNEL-PROVED** — `cert_bounded_gaps_iff` states
  the landed matrix verbatim as its LHS, so the type-check itself certifies the
  paraphrase; the `Set.Infinite` rendering is likewise tied by a proved iff (the
  executor's own first draft called it "genuinely weaker" — false, caught by rule 2,
  repaired by proof rather than rewording). Zero hypotheses, stated as such.
  (W-CERT-1 executor draft; landed at the helm.)

* `Salt/Certs/Chen.lean` — `cert_chen` + `cert_chen_omega`, certifying
  `Salt.Chen.chen_headline` and `Salt.Fulcrum.chen_omega_prod_le_three` (one paper
  phrase, three declarations — the header carries the phrase→declaration map;
  the Goldbach half is row 6, NOT certified here). Direction: **same proposition**
  both (set equality; Ω rendered as `primeFactorsList.length`, bridged by mathlib's
  `cardFactors_apply`). The `IsP2 2` threshold clauses are vacuous and their
  omission is kernel-checked (the reverse inclusion rebuilds them from primality).
  The one-directional superset transport behind the Ω-corollary is FENCED in the
  docstring: the `Ω(p+2) ≤ 2` reading is a reader's gloss, its converse unproved
  in this corpus. (W-CERT-1 executor draft; landed at the helm.)

## OWED (target list v1, anchored rows remaining)
`chen_goldbach` (row 6) · `siegelWalfisz_holds` · `analytic_LS + char_LS` ·
`vmvt` (the likely class-C translation; maestro owns it) ·
`norm_kloosterman_estermann` · `twin_bar/no_twin_weight/least_k_theorem` (THE WALL,
anchor = Pi's `neutrality_rate` :1173) · `psiTot_pnt` [parked pending anchor ruling].

✅ **ROOTED.** `Salt.lean:31` imports `Salt.Certs.All` (maestro, 2026-08-11, at the
first cert's seal), so the hub build replays this tree: full `../saltbuild.sh` green at
9724 jobs with `✓ Salt.Certs.cert_vaughan [3 axioms]` firing inside the hub run, not only
when the file is named. *This paragraph replaced a "rooting is not done" note that my own
commit left behind — it went stale the moment the import landed.*
-/

open Salt.Tactic in
#audit_axioms Salt.Certs.cert_vaughan
  Salt.Certs.cert_parity_gap
  Salt.Certs.cert_zeta_zero_free_pow
  Salt.Certs.cert_log_chowla_door_only
  Salt.Certs.cert_log_chowla_budget_head
  Salt.Certs.cert_bounded_gaps
  Salt.Certs.cert_bounded_gaps_iff
  Salt.Certs.cert_bounded_gaps_infinitely_many
  Salt.Certs.cert_bounded_gaps_infinitely_many_iff
  Salt.Certs.cert_chen
  Salt.Certs.cert_chen_omega
