# OPERATIONS — the daily routine and the confidence contract
### (ratified 2026-07-19 evening; the post-cliff operating ritual)

## The four properties this document guarantees

**P1 — WHERE WE ARE is always in the repo, never in a head.** The
state lives in: `docs/exploration/pilot.md` (the ledger — every
landing, every catch, appended same-hour), `git log` (the pulse),
`docs/exploration/roadmap.md` (the roads), the freeze docs (the
law), `docs/blueprints/flags.md` (the catch authority). Sessions
are disposable; the repo is not. This survived, today alone: one
context compaction, three account switches, one quota clip, one
ToS outage.

**P2 — WHAT'S NEXT is deterministic.** Every queued item has a
class, a route, a gate, and usually a banked brief (the freezes'
executor notes). The conductor never invents work; it dispatches
the next ungated item from the roadmap's roads.

**P3 — THE FORGE IS HOT, verifiably.** The conductor's boot ritual
(below) runs every session; JYH's independent 60-second check runs
anytime, no conductor needed:
```
git log --oneline -5          # the pulse: landings today?
tail -50 docs/exploration/pilot.md   # the story
lake build                    # the truth (kernel-checked, green)
```
If the pulse is stale a day with items ungated, the forge is cold —
say "board" to any session and it must produce the full board from
P1's files.

**P4 — ESCALATION FIRES BY LAW, not judgment-in-the-moment.** The
triggers are enumerated and each has a tape-proven precedent:
- Executor hits statement-layer trouble → STOP + report (iron rule
  1; precedents #245 #247 #252 #254).
- ~3 serious attempts on a rung → flag + move on (iron rule 4;
  Zeno partials are success).
- A rung looks D → ONE fresh Opus scoper w/ resistance map BEFORE
  any escalation (the #255 law). The map either kills the D or
  aims the consult.
- Conductor (Opus) meets a statement-layer decision → NEVER rules;
  freezes the site, writes the consult brief (gap + candidate
  rulings + arithmetic), chimes JYH (the Monday-protocol law #1).
  JYH decides or wakes Fable-on-credits for ONE turn.
- Quantitative house rulings → worst-corner pass incl. ASYMPTOTIC
  corners before broadcast (#248, #253).
- Catch rate rises to ~daily → the conductor proposes a Fable
  shift with a dollar estimate (the escalation trigger).
- New design blocks → JYH-gated with honest credit estimates,
  always.

## The conductor's boot ritual (every session, first acts)
1. Read MEMORY.md → project_gold_window → this file → the pilot
   tail (~100 lines) → the roadmap.
2. Check in-flight work: any dispatched-but-unlanded item in the
   pilot tail = investigate (orphans are visible because DISPATCH
   is ledgered, not just landings).
3. Emit THE BOARD to JYH: landings since last board / in flight /
   next dispatches / anything PENDING-JYH.
4. Dispatch the day's ungated items from banked briefs (the brief
   boilerplate: no-git #244, single-writer, report-NOTES #245,
   frozen statements BINDING, the trap lists via grep
   SCOUT/CATCH in pilot.md, Zeno = success).
5. Ceremony loop: verify build → wire manifests → #audit_axioms →
   ledger w/ `date`-stamped entry → commit by name → push.

## The drift tripwires (JYH's weekly 5-minute audit)
- flags.md new entries: every statement-layer item should read
  STOP/PENDING-JYH or cite a ratification — a silent Opus ruling
  on a statement is THE red flag.
- pilot.md: every dispatch has a landing or an investigation.
- The audit blocks: `lake build Salt.<track>.All` green = no
  axiom drift, mechanically.
- Ask any session "board" — a correct board from cold proves P1.

The kernel remains the referee; the ledger remains the memory; the
laws remain the judgment. Sessions come and go.
