# salt — session instructions

Lean 4 + mathlib project. Objective: a machine-checked proof of the Twin Prime
Conjecture. The LIVE WORK ROUTING is **`docs/QUEUE.md`** — the Captain-ratified
salt queue (P1 finish-first · P2 behind the doors · P3; strict tiering; the
fleet PULLS at seams; the bus carries orders, the queue carries standing work).
Seats pick from the queue at their tier; the current campaign is the Salt-method
twin-prime program (W1/E-ladder ports, the h-fork, λ-BV), worked on track
branches named in the queue's own items.
HISTORICAL TRACKS, both closed and preserved: Brun's theorem
(`docs/blueprints/brun.md`, closed 07-07, "Frontier: none") and explicit gaps
≤ 12 (`docs/blueprints/explicit12-design.md`, closed 07-11, "RUNG CLOSED"). The
blueprint node workflow below applies **when and only when** a blueprint track
is reopened by a Fable/human session; `scripts/blueprint_lint.py` still audits
the Brun guide and still runs in CI.
Full routing policy: `docs/MODEL_POLICY.md`. The Lean kernel is the referee:
`../saltbuild.sh` checks every proof (NEVER bare `lake` — see Build commands).

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

1. Pull the highest open item AT YOUR TIER from `docs/QUEUE.md` (P1 before P2;
   never let a lower tier gate a higher). Blueprint guides are pulled only when
   a queue item names one. `docs/blueprints/flags.md` remains the failure
   record for ALL tracks — flag there exactly as before.
2. Write the proof in the track's file (Brun track: `Salt/Brun/` modules,
   imported from `Salt/Brun.lean`).
3. Verify: `../saltbuild.sh` (must succeed, no warnings introduced), then the
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

⛔⛔ **NEVER BARE `lake`, NEVER BARE `lean` — EVERY Lean invocation in this repo goes through
`../saltbuild.sh`.** Fleet-wide rule, ratified 2026-08-06 after TWO OOM incidents in one morning:
single elaborations on salt's heavy files reach 6–9 GB, and five seats at default parallelism
exhausted 64 GB plus 8 GB of swap. The wrapper takes an atomic cross-seat lock (one heavy job
fleet-wide, stale-reaped) and caps `LEAN_NUM_THREADS`; this `lake` has no `-j`, so the Lean task
pool IS the job pool.

```sh
../saltbuild.sh                     # full build of this repo (kernel-checks everything)
../saltbuild.sh Salt.Brun.Foo       # targeted build — PREFER THIS while iterating
../saltbuild.sh Scratch.lean        # audit run for #print axioms (don't commit Scratch.lean)
python3 scripts/blueprint_lint.py   # docs↔code consistency + axiom audit (phase 1)
```

⛔ **Judge a build ONLY on the printed `saltbuild EXIT=N` line, and READ THE NUMBER** — never a
pipe's exit status, and never the harness's own report (it has printed "exit code 0" over a run
whose log read `EXIT=1`). `143` is SIGTERM, the box taking your process, not Lean. Killed builds
resume from cache; a lock timeout is safe to retry. **NEVER PIPE the wrapper.**
⛔ **Put this rule VERBATIM in every executor/subagent brief you write** — a subagent that does not
know it will OOM the fleet.

*(This block instructed bare `lake build` until 2026-09-11, when the 51st helm head measured it:
the rule was ratified fleet-wide, carded, re-enacted in four council minutes and present in the
Lean seats' own boot briefs, and the string `saltbuild` occurred **ZERO** times in this file
against a positive control of five for `lake`. ⇒ 🔑 ***A RULE CAN REACH EVERY SPECIALIST AND MISS
THE ONE DOCUMENT EVERY SESSION READS*** — and this file did not merely omit it, it printed the
forbidden command in the imperative. Found from the other end: `kent` was auditing whether the
08-06 rules were the Captain's own words, which sent me to look at where they had landed.)*

⛔⛔ **NEVER `grep -r` FROM `~/projects/claude` — IT SEARCHES THREE FILES AND RETURNS A CLEAN ZERO.**
Here `grep` is a shell function wrapping `ugrep -G --ignore-files`, `--ignore-files` honours
`.gitignore`, and the fleet root's `.gitignore` is `*` with three exceptions — so **every tree,
including this one, is ignored.** The false zero exits **rc=1 with an empty stderr, byte-identical
to a true absence.** Driven 2026-09-09: `grep -rl theorem ~/projects/claude` → **0**, the same
needle scoped to `~/projects/claude/salt` → **5221**.
✅ Scope inside the tree (`grep -r <needle> ~/projects/claude/salt`), or use `git grep`.
⇒ This is the MECHANISM under the standing rule that **an empty grep is not evidence of absence** —
which matters here more than anywhere, because absence claims about mathlib and about this corpus
are how nodes get classified and how "no such lemma exists" gets written down. Always `grep -F`
for Lean identifiers.

If the wrapper reports that `lake` is not on PATH, it lives at `~/.elan/bin/lake` —
put it on PATH; do not reach past the wrapper to call it.

## Public-repo commit hygiene (ratified 2026-08-23)

No `Claude-Session:` trailer lines and no chat-session URLs in commit messages —
this repository is public, and the 2026-08-16 history purge's scope is the
standing rule. Enforcement: a `commit-msg` hook tracked at `.githooks/`
(fresh clone: `git config core.hooksPath .githooks` once) and the Scrub CI
workflow, which checks every pushed delta. `Co-Authored-By` is fine.

**A Windows CI lane for Scrub is a DECLARED NON-GOAL** (ruled 2026-09-01,
closing `#8`): the scrub gates are authoritative on the Linux job, and no
Windows checkout commits here. Recorded rather than left implicit because an
undeclared gap reads as *covered* — a gate that never runs on a platform
reports green there, not unknown.

What the declaration accepts, stated so this is a KNOWN hole and not a stale
one. Measured on real Windows, and on hosted `windows-latest`, 2026-08-31:
a redirected Python stdout there is **cp1252**, and these gates print an
em-dash. `check_private_paths.py --self-test` renders `... scratch repo
<U+FFFD> trichotomy ...` — the em-dash becomes byte `0x97`, the stream stops
being valid UTF-8, and the process **exits 0**. A character outside cp1252 is
worse: `UnicodeEncodeError`, empty output, exit **1** — the same code these
gates use for *finding found*.

⇒ **None of that can reach CI, which is Linux-only and UTF-8**, and the Linux
job blocks the push, so a Windows-specific defect in these three scripts cannot
leak into public history. The only live Windows surface would be a `commit-msg`
hook on a Windows checkout of this repository, and none exists. A Windows job in
the merge gate would be a perpetual cost — a flaky runner blocks a merge — for a
class that cannot leak.

**A working lane exists on branch `flask/windows-scrub-lane`, retained at origin.
Reopen it the day a Windows contributor or a Windows checkout of this repository
appears.** That branch also carries two platform-neutral pieces that stand on
their own and can be cherry-picked without the lane: a UTF-8 stdout shim with the
three gate scripts hardened to use it, and `check_verdict_encoding.py`, which
adjudicates the whole class from Linux by forcing the codec on a child.
