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
import Salt.Certs.Vmvt
import Salt.Tactic.AuditAxioms
import Salt.Certs.Kloosterman
import Salt.Certs.SiegelWalfisz
import Salt.Certs.LargeSieve
import Salt.Certs.ChenGoldbach
import Salt.Certs.TwinBar

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
  `Salt.Parity.sufficient_true_not_parityInv` (Pi `thm:gap`). Direction:
  **same proposition**, nothing traded. Carries the mechanism in one line (the witness
  is `twinFree`, whose twin mass is identically `0`) and **reports that TWO of the four
  stated hypotheses are frozen and unused** in the landed proof — `1 ≤ A₀` and
  `E oneWeight` — so the result is strictly stronger than it is written as. Flagged for
  the design desk under iron rule 1; **not altered here.**

* `Salt/Certs/ZetaPowRegion.lean` — `cert_zeta_zero_free_pow`, certifying
  `Salt.Vk.zeta_zero_free_region_pow` (Pi `thm:pow`). Direction: **contrapositive**,
  logically equivalent, nothing traded. States the result as *a region containing no
  zeros* rather than as an inequality satisfied by every zero — which is what the phrase
  "zero-free region" means — and records that **the `∃ c T₀` in the landed statement is
  not evidence of inexplicitness**: the chain bottoms out in `K = 8104`,
  `t₀ = exp (exp 100)`, so Pi's word "effective" is earned by the proof.

* `Salt/Certs/ChowlaSpine.lean` — `cert_log_chowla_door_only`, certifying
  `Salt.Entropy.Chowla.log_chowla_two_door_only` (Pi `thm:spine`). Direction: **same
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

* `Salt/Certs/Vmvt.lean` — `cert_vmvt` (+ `_iff`), certifying `Salt.Vmvt.vmvt`
  (Pi `thm:vmvt`; the Appendix A decode finished to primitive vocabulary).
  Direction: **same proposition, kernel-tied by an UNCONDITIONAL iff** — the solution
  count becomes a literal set-builder count (`Set.ncard`, no `Salt.*` name survives),
  the constant collapses to the single power `k^(24k²r)` (⚠️ house-RE-GRADED, generous
  by design — the header forbids reading it as sharp), and the exponent
  `2rk − k(k+1)/2 + (k²/2)(1−1/k)^r` is inlined (the load-bearing half; matches
  Vaughan 24.5 exactly). **First hypothesis-carrying cert**, so rule 6's vacuity
  control debuts: satisfiability witnessed in-file at `(k,r,x) = (2,1,1)`.
  (Maestro's row, landed at the helm.)

* `Salt/Certs/TwinBar.lean` — `cert_twin_bar`, `cert_no_twin_weight`, `cert_least_k`
  (+ `cert_twin_bar_witness` and its two carrier lemmas), certifying
  `Salt.TwinBar.twin_bar`, `no_twin_weight` and `least_k_theorem` — **THE WALL**, row 11,
  three declarations in one file because they are one story. Direction: **same
  proposition** for all three, each proved by `exact`. The `k = 2` pair is unfolded to
  primitive vocabulary — **no `Salt.*` name survives in `cert_twin_bar` or
  `cert_no_twin_weight`**, only `∫`, `^`, `+`, `<`, `≤` and `Real.log`.
  ⭐ **THE CARRIER ASYMMETRY IS THE RULE-2 TRAP HERE and the header states it rather
  than smoothing it:** the three no-gos are about continuous real weights on the real
  simplices, while the `k = 5` conjunct is an exact `ℚ` certificate at one explicit
  polynomial — *"the least `k` is 5"* as plain English claims a single object the theorem
  does not provide, and the unifying bracket is registered debt.
  ⚠️ **Rule 1 is applied BY DOCSTRING for the `k = 3`/`k = 4` conjuncts** (unfolding them
  yields fifteen nested integrals with no gain); declared in the header, not silent.
  Rule 6: `cert_twin_bar` carries hypotheses ⇒ **NON-DEGENERACY witness**, and the
  degenerate one it rejects is named — `F ≡ 0` is continuous, satisfies every hypothesis,
  and makes the bound read `0 ≤ 0`. The witness is `F ≡ 1`, where the mass is `1/2 > 0`
  and the bar reads `2/3 ≤ log 2` — **non-vacuous AND near-sharp, a 3.9 % margin.**
  The other two certs are hypothesis-free ⇒ EXEMPT.

## OWED (target list v1, anchored rows remaining)
`psiTot_pnt` [parked pending anchor ruling] — and NOTHING ELSE anchored.
**THE WALL (`twin_bar`/`no_twin_weight`/`least_k_theorem`, anchor = Pi's `neutrality_rate`
:1173) LANDED at `de7429b`, 2026-08-12, and moved to the roll-call above** — re-derived
from the roll-call per this stanza's own warning, not edited on memory. — re-derived from the roll-call
per this stanza's own warning, not edited on memory.

⛔ **THIS LIST WENT STALE THE SAME WAY THE ANCHOR TABLE'S COUNT DID.** It named
`siegelWalfisz_holds`, `analytic_LS + char_LS` and `norm_kloosterman_estermann` as OWED
while their certs sat in the roll-call *below it in this same file*. **A list of what is
missing is a derived fact and rots exactly like a count** — re-derive it from the roll-call,
never read it. (`scripts/anchor_pin_check.py` ARM 5 checks the anchor table's marks against
the corpus; this list is the same class of claim and is NOT yet under any arm.)

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
  Salt.Certs.cert_vmvt_iff
  Salt.Certs.cert_vmvt
  Salt.Certs.cert_vaughan_witness
  Salt.Certs.cert_parity_gap_witness
  Salt.Certs.cert_vmvt_witness
  -- row 10 (Nature :202, "the Weil bound for Kloosterman sums"): the landed bound is
  -- ESTERMANN's composite-modulus form; the cert closes the NAME gap by DERIVING the
  -- classical Weil bound 2√p at odd primes, where all three correction factors are one
  Salt.Certs.cert_kloosterman_estermann Salt.Certs.cert_weil_bound_prime
  Salt.Certs.cert_weil_bound_prime_witness
  -- row 7 (Nature :200 + Pi :322, "an unconditional Siegel–Walfisz theorem"): the landed
  -- statement is TWO opaque names deep (SiegelWalfisz, then psiAP); the cert unfolds BOTH
  -- and closes by `exact`, so the kernel certifies the paraphrase
  Salt.Certs.cert_siegel_walfisz
  -- row 8 (Nature :201 + :205, the adversary sentence): the anchor's point is that the
  -- external BV projects take the large sieve as an AXIOM, so both certs carry their
  -- CONSTANTS in the statement — δ⁻¹ + 13N and Q² + 13N, explicit, no O(·)
  Salt.Certs.cert_analytic_large_sieve Salt.Certs.cert_char_large_sieve
  -- witnesses NAMED at the maestro's 11:05 ruling: a witness the census cannot see is a
  -- control the census cannot vouch for. The two level-* rows are the Q = 2 MEASUREMENT
  -- (level 1 primitive, level 2 not), which the docstring's thinness claim rests on
  Salt.Certs.cert_analytic_large_sieve_witness Salt.Certs.cert_char_large_sieve_witness
  Salt.Certs.cert_char_large_sieve_level_one_primitive
  Salt.Certs.cert_char_large_sieve_level_two_not_primitive
  -- row 6 (Nature :202, "Chen's theorem"): the paper's ONE phrase covers TWO theorems and
  -- the corpus proves them as TWO declarations — the twin half is cert_chen above, this is
  -- the GOLDBACH half; the _isP2_iff PROVES the z = 2 size decorations are recoverable, so
  -- dropping them is a restatement and not a weakening
  Salt.Certs.cert_chen_goldbach_isP2_iff Salt.Certs.cert_chen_goldbach
  -- row 11 (THE WALL, anchor Pi :1173 `neutrality_rate`): the k = 2 pair is unfolded to
  -- primitive vocabulary and closes by `exact`, so the kernel certifies the paraphrase;
  -- the witness is NON-DEGENERACY (F ≡ 1, mass 1/2, bar within 3.9% of equality) because
  -- the obvious F ≡ 0 satisfies every hypothesis and makes the bound read 0 ≤ 0
  Salt.Certs.cert_twin_bar Salt.Certs.cert_no_twin_weight Salt.Certs.cert_least_k
  Salt.Certs.cert_twin_bar_witness

