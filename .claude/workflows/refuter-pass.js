export const meta = {
  name: 'refuter-pass',
  description: 'Adversarial refuter pass over a design freeze: N parallel refuters with assigned kill-checks, structured verdicts gathered',
  whenToUse: 'After banking any design freeze, before executor waves consume it (verify-posture law, catch #98). args: { freeze, context?, refuters: [{ id, questions }] }',
  phases: [{ title: 'Refute', detail: 'N parallel adversarial refuters, structured verdicts' }],
}

// args:
//   freeze   : path to the freeze doc under attack (required)
//   context  : extra reading list — sources, consumer files, line anchors (optional string)
//   refuters : [{ id: 'REF-A', questions: 'R-1: ...; R-2: ...' }, ...] (required)
// Returns { verdicts: [...] } — one structured verdict object per refuter.

const VERDICT = {
  type: 'object',
  properties: {
    refuter: { type: 'string' },
    verdicts: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          question: { type: 'string', description: 'the assigned kill-check id/summary' },
          verdict: { type: 'string', enum: ['CONFIRMED-FATAL', 'CONFIRMED-REPAIRABLE', 'UNFOUNDED'] },
          finding: { type: 'string', description: 'the finding with file:line / page citations' },
          repair: { type: 'string', description: 'the exact repair, when verdict is CONFIRMED-REPAIRABLE' },
        },
        required: ['question', 'verdict', 'finding'],
      },
    },
    unassignedKills: {
      type: 'array', items: { type: 'string' },
      description: 'kills found outside the assigned questions',
    },
    overall: { type: 'string', enum: ['FIRE', 'REPAIR-THEN-FIRE', 'HOLD'] },
  },
  required: ['refuter', 'verdicts', 'overall'],
}

const BOILERPLATE = `You are an adversarial REFUTER for the salt project
(Lean 4 + mathlib, /Users/jyh/projects/claude/salt). Your job is to BREAK a
design freeze before executors burn quota on it. You are READ-ONLY: no git
commands, no edits, no file writes. DISCIPLINE: default to REFUTED if
uncertain — a false kill costs one round-trip; a missed kill costs an
executor campaign. Distinguish CONFIRMED-FATAL (the route cannot work as
designed) / CONFIRMED-REPAIRABLE (gap real, repair evident — state the exact
repair) / UNFOUNDED (the freeze survives your attack — say why). Cite
file:line for every corpus claim and page numbers for every source claim;
read PDFs DIRECTLY with the Read tool (pages parameter) — never from memory.
Hunt asymptotic corners (catch #253): any regime where a constant silently
depends on a growing quantity. Check every freeze ⟦R⟧/amendment block for
internal consistency.`

phase('Refute')
const results = await parallel(args.refuters.map((r) => () =>
  agent(
    BOILERPLATE +
      '\n\nYou are ' + r.id + '.\n\nTHE FREEZE UNDER ATTACK (read first): ' + args.freeze +
      (args.context ? '\n\nALSO READ (the sources and consumers): ' + args.context : '') +
      '\n\nYOUR ASSIGNED KILL-CHECKS:\n' + r.questions +
      '\n\nAlso report any UNASSIGNED kills you find. Set refuter to "' + r.id + '".',
    { label: r.id, model: 'opus', schema: VERDICT },
  ),
))

const verdicts = results.filter(Boolean)
log(verdicts.length + '/' + args.refuters.length + ' refuters reported; overall: ' +
  verdicts.map((v) => v.refuter + '=' + v.overall).join(', '))
return { verdicts }
