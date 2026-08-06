# TS-1 DISPATCH PROMPT — staged 2026-08-06 for the 20:00 gate

Paste as the `prompt` of a single `Agent` call, `subagent_type: "general-purpose"`, `model: "opus"`,
`run_in_background: false`. Written now so the gate is pure execution.

**⛔ THE `-M` PROBE (queue item 1), corrected spec — still OPEN as of 13:24; compiler's attempt was
voided by a shell syntax error, not a memory failure.**
- Cap must sit **above** the ~670 MB Lean+mathlib baseline and **below** baseline + reduction:
  `--cap 900` with a ~300–500 MB `decide +kernel` reduction.
- **Judge by the ERROR TEXT, never the exit code.** Only Lean's own memory diagnostic
  (`memory limit exceeded` / `maximum memory`) counts as a cap hit. `syntax error near unexpected
  token`, `EXIT=75`, or a missing file mean **the run did not test the cap** — void and retry, do
  **not** adjust the cap.
- Sanity first: a no-`decide` file at the same cap must exit 0. If it dies, read *why* before
  concluding the cap is too low.
- Run only when the wrapper has been quiet long enough that no in-place edit can be mid-flight.

**Pre-flight, by me, before dispatching:**
1. `date` — confirm ≥ 20:00. The gate is judged by `date`, never by a bus stamp.
2. `git pull --ff-only` in `/Users/jyh/projects/claude/salt`.
3. `git status --short` — confirm `Salt/SW/TBal*.lean` are CLEAN (another seat may have touched the
   tree; my TS-1 patch is held outside it).
4. Check the bus for a TS-3 ruling — if one landed, re-read the brief before firing.
5. Check whether COMPILER already ran the `-M` probe; if so, skip probe, record their verdict.

---

You are an OPUS EXECUTOR on the salt project (`/Users/jyh/projects/claude/salt`, Lean 4 + mathlib,
branch `main`). You are executing **WAVE TS-1** of the TAU-SHARP campaign. You execute; you do not
redesign.

## ⛔ BUILD ETIQUETTE — MANDATORY, NO EXCEPTIONS
Three OOM incidents took this fleet down today. **EVERY Lean invocation — builds AND audit runs —
goes through the fleet wrapper. NEVER bare `lake build`, NEVER bare `lake env lean`, NEVER bare
`lean`.**
```
/Users/jyh/projects/claude/saltbuild.sh                    # full build
/Users/jyh/projects/claude/saltbuild.sh Salt.SW.TBalR8     # targeted build
/Users/jyh/projects/claude/saltbuild.sh ScratchTS1.lean    # audit run
```
It takes a cross-seat lock and caps memory. It prints `saltbuild EXIT=N` — **that line is the only
verdict.**

⛔ **NEVER PIPE IT.** Run `saltbuild.sh …` with **no `| tail`, no `| grep`, nothing** — especially
in a backgrounded task. A pipeline's exit status is the *last command's*, so `saltbuild … | tail`
reports `tail`'s success and yields a **phantom green**: this exact mistake produced an unverified
commit in this fleet today. The harness captures full output; read the `saltbuild EXIT=N` line.

⚠️ **THREE NON-ZERO EXITS MEAN DIFFERENT THINGS — do not report a wave failure without checking
which:**
1. a genuine build failure (Lean errors in the output) — **this is the only real failure**;
2. **`EXIT=75`** — lock-wait timeout after 90 min. **The build never started. RETRY.**
3. **`syntax error near unexpected token`** — someone edited `saltbuild.sh` in place while your
   instance was queued (bash reads scripts by byte offset). **Not your build. RETRY.**

Killed builds resume incrementally, so retries are cheap. **Prefer TARGETED builds while
iterating**; full build only at wave exit.
⚠️ `Salt/SW/TBalTall.lean` imports `Salt.SW.TauExt` which imports `Salt.SW.TBalR8` — they are a
dependency **CHAIN**, so build `TBalR8` first, then `TBalTall`. They cannot elaborate concurrently.

## ⛔ SHARED-TREE ETIQUETTE
Other seats commit into this same checkout concurrently. **Commit with
`git commit <your explicit paths> -m/-F` as ONE command. NEVER `git add` then `git commit`** — with
no paths on the `commit`, git commits the whole index including other seats' staged files. Expect
other seats' files in `git status`; they are not yours to touch.

## START HERE — WORK IS ALREADY BANKED
A killed pre-rule executor got partway. Its output is preserved and **verified to re-apply cleanly**:
```
cd /Users/jyh/projects/claude/salt
git apply --check ~/.claude/salt-ts1-wip/ts1-partial.patch   # must pass
git apply         ~/.claude/salt-ts1-wip/ts1-partial.patch
```
It contains **S6 (636 → 570)** and **S5(a) (627 → 248)** propagated through
`C2Rho_le_tall` → `row_Eρ_cap_tall` → `KEρ`, plus the `neg_log_le_rpow'` roll-call row in
`Salt/SW/All.lean`. `~/.claude/salt-ts1-wip/ScratchTS1.lean` additionally holds **proved** (elaborated,
not axiom-audited) versions of S1's generalised `tbal_tau_le_split`, the sharp
`neg_log_le_rpow' : −log u ≤ u^{−δ}/(e·δ)`, and `logz_factor_le` at 248. **None of it has ever
completed a build.**

## YOUR SCOPE AND THE FULL BRIEF
`docs/exploration/tau-sharp-ts1-ts2-briefs-0806.md` is your brief — **read it in full first.** It
carries the stone list (S1 + S5 + S6), the both-towers kill, the exact-rational γ-floors, the arm
table, the `-M` cap check, and the mutation check. `docs/exploration/tau-sharp-refuter-0806.md` §1
and §5 are BINDING amendments to the original freeze and override it where they differ.

**The one thing you must not get wrong:** there are **TWO** parallel assemblies.
`dh_repulsion_inst` (`TBalR8:1373`) → the **LANDED** `dh_repulsion_ordered` (`:1752`), with an
**11-fold** `c`-min at `TBalR8:1776-1833`; and `dh_repulsion_inst_tall` (`TBalTall:1673`) →
`dh_repulsion_tall` (`:2081`), with a **10-fold** `c`-min at `TBalTall:2105-2156`. `hc_t1` is
consumed at **TWO** sites — `TBalTall:1730-1733` **and `TBalR8:1425-1428`**. Edit only the tall side
and a landed theorem with live consumers goes red.

## IRON RULES
No `sorry`. No `native_decide`. No new axioms — every new declaration must audit at
`[propext, Classical.choice, Quot.sound]` via `saltbuild.sh ScratchTS1.lean` (do **not** commit that
file). **Never alter a blueprint statement to make a proof go through** — flag it in
`docs/blueprints/flags.md` instead. ~3 serious attempts per piece, then flag and move on. **DO NOT
TOUCH** any `Salt/HB/Lemma7*.lean`, anything under `papers/`, `CLAUDE.md`, or blueprint node tables.

## DELIVERABLE
Lean edits in both towers; a `docs/blueprints/flags.md` entry (`## ⟦TAU-SHARP TS-1 — …⟧`) recording
what landed, attempt counts, the **honest** line count vs the dossier's ~120 ln price, anything
abandoned under the brief's stop-rule and why, and the new ten-arm table; ONE commit
`play M: TAU-SHARP TS-1 — …` with `[skip ci]` and the trailers. **Report back**: what landed, what
did not and why, the honest line count, the arm table, the commit SHA, and everything TS-2 needs to
know about the **TBalR8 11-fold min tower**, since TS-2 must edit it too.
