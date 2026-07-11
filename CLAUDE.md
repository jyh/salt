# salt — session instructions

Lean 4 + mathlib project. Objective: a machine-checked proof of the Twin Prime
Conjecture. Tracks: Brun's theorem (`docs/blueprints/brun.md`, branch `brun`)
and — currently active — explicit bounded gaps ≤ 12
(`docs/blueprints/explicit12-design.md`, branch `explicit12`; commit messages
`explicit12 <node>: <name>`; note `scripts/blueprint_lint.py` audits only the
Brun guide, so explicit12 docs↔code checks are manual).
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
   already-merged proofs, or the prose and card **Statement**/**Role** fields
   of `docs/blueprints/brun-guide.md`, unless you are a Fable/human-directed
   session. Card *volatile* fields (Status/Lean/Difficulty/Proof idea/Notes),
   Mermaid status colors, and the briefing frontier list are open to all
   tiers via workflow step 5.

## Workflow per node

1. Pick an unproven node of your class from the guide's catalog/frontier list
   (`docs/blueprints/brun-guide.md`); `docs/blueprints/flags.md` is the
   detailed history behind it.
2. Write the proof in the track's file (Brun track: `Salt/Brun/` modules,
   imported from `Salt/Brun.lean`).
3. Verify: `lake build` (must succeed, no warnings introduced), then the
   axiom check (rule 3).
4. Commit on the track branch with message `brun: N<id> <name>` and a line
   noting your model and attempt count.
5. Update docs in the SAME commit: your node's card in
   `docs/blueprints/brun-guide.md` (status token, Lean names, actual
   difficulty, one-line proof idea), the Mermaid graphs' status
   colors/emoji, and the briefing frontier list. Failed attempt? Set the
   card to ⛔ with a flags pointer instead. Field-by-field rules: the
   guide's preamble.

Fable sessions additionally open with a reconciliation sweep: read the
guide's briefing block, resolve `<!-- TODO -->` markers and ⛔ statuses,
and run the lint.

## Build commands

```sh
lake build                        # kernel-checks everything (mathlib is cached)
lake env lean Scratch.lean        # for #print axioms checks (don't commit Scratch.lean)
python3 scripts/blueprint_lint.py # docs↔code consistency + axiom audit (phase 1)
```

If `lake` is not on PATH: `~/.elan/bin/lake`.
