# Model routing policy

Principle: **spend top-model tokens where decisions compound; spend cheap tokens
where the kernel makes failure free.** A failed proof attempt costs only its own
tokens — the Lean kernel rejects it and nothing downstream is contaminated. A bad
decomposition (blueprint) makes every lemma under it one difficulty class harder
and taxes the entire grind. Route accordingly.

## Routing table

| Tier | Model | Work |
|---|---|---|
| Design | Fable 5 (`claude-fable-5`) | Blueprint decompositions, Barrier Atlas synthesis, verification-policy decisions, frontier proofs where Opus has demonstrably stalled, interactive math/design sessions |
| Workhorse | Opus 4.8 (`claude-opus-4-8`) | Harness engineering, first-pass formalization of known proofs, top of the automated cascade |
| Bulk | Sonnet 5 (`claude-sonnet-5`) | Routine lemma proving, recon/reading agents, docs, test scaffolds |
| Floor | Haiku 4.5 (`claude-haiku-4-5`) | First attempt on everything, glue lemmas, syntax-repair loops, premise-selection experiments |

## Escalation gates (automated cascade)

```
Haiku pass@2 → Sonnet pass@2 → Opus pass@3 → STOP: human-review queue
```

- **Fable is never in the automated loop.** Lemmas that survive Opus go to a
  reviewed queue; the usual diagnosis is a decomposition problem (fix the
  blueprint — design-tier work), not a hard lemma.
- **Per-lemma cost cap: $5.** The cascade abandons and flags rather than grinding.
  A flagged lemma is a blueprint-refactor signal.
- Escalation gate = the full verdict (proof kernel-checked AND statement matches
  the blueprint node), not "compiled".

## Mechanisms

1. **Telemetry before the first automated proof.** Every API call logs
   `usage.input_tokens` / `output_tokens` (and cache fields); every lemma gets a
   real dollar cost and difficulty class. No unmetered spend.
2. **Batch API for all offline grinding** — flat 50% discount.
3. **Prompt caching** once harness prompts exceed the ~4K-token minimum cacheable
   prefix (system prompt + stable premise slice under the breakpoint).
4. **Session hygiene:** interactive design/math sessions run Fable; routine
   pair-programming sessions run Opus (`/model`).

## Pricing snapshot (2026-07, per MTok, first-party API)

| Model | Input | Output |
|---|---|---|
| Haiku 4.5 | $1 | $5 |
| Sonnet 5 | $3 ($2 intro through 2026-08-31) | $15 ($10 intro) |
| Opus 4.8 | $5 | $25 |
| Fable 5 | $10 | $50 |

Batch API: 50% off. Cache reads ~0.1× input; cache writes 1.25× (5-min TTL).
Re-verify against current pricing before large runs.

## Wave protocol (interactive tracks)

*Added 2026-07-10 after the Maynard track. Empirical basis: the expensive
failure mode was Opus grinding past a design defect (three failed S₂-inner
attempts + the reverted vacuous-herr work cost more than the Fable design pass
that resolved them); every Opus wave run from a committed Fable design landed.
Both Fable design docs caught a fragility at design time.*

The loop: **Fable wave → committed design + sketch cards → Opus waves until the
queue forces the next Fable wave.**

### Fable wave contract
A Fable wave ends only when it has COMMITTED a design doc containing, per node:
1. the frozen Lean statement;
2. a hand-verified constant/dimension chain (B-vs-A check pre-done);
3. a sketch card — numbered route steps naming the landed/mathlib lemmas,
   with the one hard trick spelled out;
4. known traps;
5. a verifier brief (2–4 decisive checks for the adversarial pass);
6. the narrowest permitted PORT-BLOCKER.
Fable writes docs, not Lean. The moment remaining work is "copy a landed proof
with modifications", "thread constants", "assembly", or "threshold analysis",
Fable stops — all of those succeed at Opus.

### Escalation tripwires (Opus → FABLE-QUEUE)
Do not spend the third attempt. Queue (in `docs/blueprints/flags.md`,
`FABLE-QUEUE` section) and move to the next independent node when:
- an atom fails a satisfiability sanity-check (no consistent toy instance);
- 2 adversarial-verification failures on the same node for *mathematical*
  (not Lean-mechanical) reasons;
- any statement needs changing (iron rule 1);
- an error term fails the dimensional check with no landed fix;
- a constant needed later for numerics goes ∃-opaque;
- an agent claims something is *impossible* — impossibility claims are
  diagnosis work, always Fable.

### Opus wave discipline
Opus drives; writes agent-dispatch recipes from the sketch cards; runs
adversarial verification at Opus (it catches defects in Fable-authored
scaffolding too — never spend Fable on verification); drains every node whose
card exists; pushes A/B nodes to Sonnet agents. Background Agents for heavy
dispatch (workflow-parallel stalls on long builds); module-scoped `lake build`
only.

### Fable cadence + pre-flight
Trigger: start of a rung, OR the queue has ≥ 2 entries, OR Opus fully blocked.
Fixed pre-flight, batched into one session: (i) drain FABLE-QUEUE; (ii)
reconciliation sweep (per CLAUDE.md); (iii) review Opus-authored scaffolding
defs since the last wave (design-debt rule — scaffolding statements are where
Opus-tier design errors hide, cf. AnalyticFrontier); (iv) write/ratify the next
design doc with sketch cards; (v) commit, hand off. Don't over-design: cards
only for the next Opus wave; later waves get cards after the information
arrives.
