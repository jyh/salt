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
