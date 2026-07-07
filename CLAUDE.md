# salt — session instructions

Lean 4 + mathlib project. Objective: a machine-checked proof of the Twin Prime
Conjecture; current track: Brun's theorem (`docs/blueprints/brun.md`).
Full routing policy: `docs/MODEL_POLICY.md`. The Lean kernel is the referee:
`lake build` checks every proof.

## Before proving anything: classify

Every lemma gets a difficulty class BEFORE any proof attempt:

- **A** — one-step or computational: `norm_num`/`decide`/`omega`/`simp`-shaped,
  a single known mathlib lemma, ≤ ~20 lines.
- **B** — standard multi-step: needs finding 2–5 mathlib lemmas, routine
  induction/case analysis/Finset manipulation.
- **C** — real proof design: new definitions, long `calc` chains, porting
  external proofs, delicate estimates.
- **D** — open-ended/research. Never attempted in an automated loop.

Blueprint nodes are pre-classified in `docs/blueprints/*.md` — use those, do
not reclassify. Helper lemmas you introduce inherit your node's class; if a
helper feels harder than your tier, STOP and flag it (see below).

## Know your tier

Identify which model you are, then attempt only nodes at your tier or below:

| Model | May attempt |
|---|---|
| Haiku | A |
| Sonnet | A, B |
| Opus | A, B, C |
| Fable | anything + design/blueprint changes |

## Iron rules (all tiers)

1. **Never alter a blueprint statement to make a proof go through.** If the
   statement seems wrong or unprovable as stated, stop and record why in
   `docs/blueprints/flags.md`. Statement changes are Fable/human-tier only.
2. **No `sorry` on `main`.** Work on the track branch (`brun`); a node counts
   as done only when its proof is sorry-free.
3. **No `native_decide`, no new axioms.** Verify when a node completes:
   `#print axioms <name>` must show at most
   `[propext, Classical.choice, Quot.sound]`.
4. **Give up early, loudly.** Budget ~3 serious attempts per node at your
   tier. Then append a flag entry (node id, what you tried, where it broke)
   to `docs/blueprints/flags.md`, commit it, and move to the next node.
   A recorded failure is the cascade working; a long grind is waste.
5. **Don't touch** `CLAUDE.md`, `docs/MODEL_POLICY.md`, blueprint node tables,
   or already-merged proofs, unless you are a Fable/human-directed session.

## Workflow per node

1. Pick an unproven node of your class from the blueprint whose dependencies
   are done (check `docs/blueprints/flags.md` for claims/flags).
2. Write the proof in the track's file (Brun track: `Salt/Brun/` modules,
   imported from `Salt/Brun.lean`).
3. Verify: `lake build` (must succeed, no warnings introduced), then the
   axiom check (rule 3).
4. Commit on the track branch with message `brun: N<id> <name>` and a line
   noting your model and attempt count.

## Build commands

```sh
lake build                 # kernel-checks everything (fast; mathlib is cached)
lake env lean Scratch.lean # for #print axioms checks (don't commit Scratch.lean)
```

If `lake` is not on PATH: `~/.elan/bin/lake`.
