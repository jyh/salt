# TS-2 DISPATCH PROMPT — staged 2026-08-06 for the 20:00 gate

Paste as the `prompt` of a single `Agent` call, `subagent_type: "general-purpose"`, `model: "opus"`,
`run_in_background: false`. **Fires only AFTER TS-1 lands green and is committed.**
Node name goes FIRST in the `description` field.

**Pre-flight, by the math seat, before dispatching:**
1. TS-1 committed, `saltbuild EXIT=0` on a full build, axioms clean.
2. `git status --short Salt/SW/` — clean apart from anything TS-1 intentionally left.
3. If TS-1 landed **S5(b)**, the two Eρ/Eβ floors change — see "IF S5(b) LANDED" below and
   edit the numerals in this prompt before pasting.
4. Announce lock take on `FLEET.md`.

---

You are an OPUS EXECUTOR on the salt project (`/Users/jyh/projects/claude/salt`, Lean 4 + mathlib,
branch `main`). You are executing **WAVE TS-2** of the TAU-SHARP campaign — the γ-honest arms.
You execute; you do not redesign.

## ⛔ BUILD ETIQUETTE — MANDATORY, NO EXCEPTIONS
Three OOM incidents took this fleet down on 8/6. **EVERY Lean invocation — builds AND audit runs —
goes through the fleet wrapper. NEVER bare `lake build`, NEVER bare `lake env lean`, NEVER bare
`lean`.**
```
/Users/jyh/projects/claude/saltbuild.sh                    # full build
/Users/jyh/projects/claude/saltbuild.sh Salt.SW.TBalR8     # targeted build
/Users/jyh/projects/claude/saltbuild.sh ScratchTS2.lean    # audit run
```
⛔ **NEVER PIPE IT.** No `| tail`, no `| grep`, nothing. A pipeline's exit status is the *last
command's*, so `saltbuild … | tail` reports `tail`'s success — a **phantom green**. This exact
mistake produced an unverified commit in this fleet on 8/6. Read the `saltbuild EXIT=N` line.

⚠️ **JUDGE BY THE ERROR TEXT, NEVER BY THE NUMBER.** Three non-zero exits mean different things:
1. **Lean errors in the output** — the only real build failure;
2. **`EXIT=75`** — lock-wait timeout. The build **never started**. RETRY the same command;
3. **`syntax error near unexpected token`** — the wrapper was edited in place while you were
   queued. **Not your build.** RETRY.
A memory-cap hit counts **only** on Lean's own diagnostic, whose ACTUAL wordings (compiler's
binary-verified strings, 8/6 16:10) are `(kernel) excessive memory consumption detected` or
`excessive memory consumption detected at '<component>'` — nothing else. `(deterministic) timeout`,
GMP/allocator errors, and shell noise mean the run did not test what you think it tested.

⚠️ `Salt/SW/TBalTall.lean` imports `Salt.SW.TauExt` which imports `Salt.SW.TBalR8` — a dependency
**CHAIN**. Build `TBalR8` **first**, then `TBalTall`. They cannot elaborate concurrently.
**Prefer TARGETED builds while iterating**; full build only at wave exit.

⚠️ **This wave runs with NO memory bound.** `saltbuild.sh:27` is `lake build "$@"` with no `-M`;
the cap applies only to the `*.lean` audit branch. This is a known, Captain-ratified condition, not
something for you to fix. Run targeted builds one at a time and do not launch anything concurrently.

## ⛔ SHARED-TREE ETIQUETTE
Other seats commit into this same checkout concurrently. **Commit with
`git commit <your explicit paths> -m/-F` as ONE command. NEVER `git add` then a bare `git commit`** —
with no paths, git commits the whole index including other seats' staged files. Expect other seats'
files in `git status`; they are not yours to touch. Never `git add -A`, never `git commit -a`.

## YOUR BRIEF
Read **in this order, in full**, before editing anything:
1. `docs/exploration/wip/ts1-ts2-addendum-0806.md` — **BINDING; amends the brief on four points,
   including the site census. Read it first.**
2. `docs/exploration/tau-sharp-ts1-ts2-briefs-0806.md` §"WAVE TS-2" — the design.
3. `docs/exploration/tau-sharp-refuter-0806.md` §1 and §5 — binding amendments to the freeze.

## THE JOB
Each of the three collapse *rows* currently throws its true exponent away by collapsing to the
uniform `c ^ (1/8)`. Replace that with **each row's own γ-floor**: restate the row's `hg` as
`K · c^{γ₀} ≤ 1/8`, and change the corresponding `c`-min arm to `c ≤ (1/(8K))^{1/γ₀}`.
`hcollapse` (`TBalTall:1973`, and the twin inside the R8 min block) already takes an **arbitrary
rational `pinv`**, with the side condition `pinv * p = 1` closed `by norm_num`.

### ⛔ THERE ARE **FOUR** SITES, NOT THREE — the brief's table is incomplete
`TBalR8:939-940` is TBalR8's **own Eρ row**, the forked twin of `TBalTall:1644-1645`, and the brief
omits it. Same exponent, same floor.

| # | row | `hcγ` site | `hg` hypothesis | discharge | exact γ | **floor to use** |
|---|---|---|---|---|---|---|
| 1 | A | `R8:542-543` | `R8:454` | `R8:1674`, `Tall:1987` | `49/50 − 14(w−u)` | `133/850` |
| 2 | Eβ | `R8:816-817` | `R8:746` | `R8:1683`, `Tall:1996` | `14σ − 1109/100` | `3547/1700` |
| 3 | **Eρ (R8)** | **`R8:939-940`** | **`R8:872`** | **`R8:1693`** | `14σ − 1009/100` | **`5247/1700`** |
| 4 | Eρ (Tall) | `Tall:1644-1645` | `Tall:1578` | `Tall:2006` | `14σ − 1009/100` | `5247/1700` |

Plus the two arm definitions: `hc_t7` (Eρ) and `hc_t6` (Eβ) in **both** mins — `R8:1387-1388`
(free `Z₀`) and `Tall:2097-2098` (numerals). Line numbers are pre-TS-1; re-locate with
**`grep -nF`** (see the grep warning below) rather than trusting them after TS-1's edits.

### ⛔ USE EXACT RATIONALS — THE FREEZE'S DECIMALS ARE INADMISSIBLE
Each γ is a function of σ alone and strictly increasing, so the infimum is at the **closed**
endpoint `hσlo : 16/17 ≤ σ`. At `σ = 16/17`, `14σ − 1009/100 = 5247/1700` **exactly** and
`14σ − 1109/100 = 3547/1700` **exactly**. The freeze's `3.0865` and `2.0865` each **exceed** their
infimum by `2.941e−5` and are therefore **FALSE at the endpoint**. Use the rationals.

**Close the side goals with `linarith [hσlo]` — tight-but-true, equality at the endpoint — NOT
`nlinarith`.** The goals are linear in σ; `nlinarith`'s preprocessing can stumble at exact equality.

Direction is safe: `rpow_le_rpow_of_exponent_ge (hx0) (hx1 : x ≤ 1) (hyz : z ≤ y) : x^y ≤ x^z` is
applied with the side goal in the FLOOR direction. Substituting `γ₀ > 1/8` keeps the shape and makes
`hg` a **weaker** demand on `c`. `hσlo` is already in scope and already load-bearing at all four
sites — no uniformity trap.

### IF TS-1 LANDED S5(b) (the δ re-tune `1/100 → ≈1/50`)
The `u`-exponent becomes `−9/50` in place of `−9/100`, so **recompute both Eρ/Eβ floors before
writing any numeral**: `5247/1700 − 9/100` and `3547/1700 − 9/100`. If TS-1 abandoned S5(b) under
its stop-rule (the likely case), use the floors in the table above unchanged. **Check the TS-1
flags entry to find out which — do not assume.**

## ⭐ THE MUTATION CHECK — THIS WAVE DOES NOT EXIT ON A GREEN BUILD
A green build proves the floors are **sufficient**. It does not prove they are **load-bearing** — a
numeral satisfied for an unrelated reason also builds green, and that is the vacuity failure this
campaign has been hunting. So, after the γ-honest arms land green:

1. Substitute the **inadmissible** `3.0865` for `γ_Eρ`'s `5247/1700` (at **`Tall:1645`**).
2. `saltbuild.sh Salt.SW.TBalTall`. **It MUST fail**, and it must fail **at that side goal** —
   `linarith [hσlo]` unable to close `3.0865 ≤ 14σ − 1009/100` at `σ = 16/17`.
   ⛔ **Confirm the build actually re-elaborated `TBalTall`** (the module must appear as compiling
   in the output). A green from a cached/no-op build is not evidence of anything — on 8/6 the
   silicon seat's `#audit_axioms` printed `✓ [0 axioms]` for two theorems that had never elaborated.
3. Restore the exact rational. Build green again.
4. **Report both outcomes in the flags entry, with the error text quoted.**

**This mutation is a VALID positive control** because the mutated goal is *arithmetically false* at
the endpoint — no tactic can close it and there is no alternative route. **If the mutated build
PASSES: STOP, change nothing further, and flag it immediately** — it would mean the arm table is not
measuring what it claims to measure.

### The S1 mutation is DIFFERENT — do not halt the campaign on it
If you also run the S1 control (`1/40 → 2`, i.e. strictly `> 1`), understand that it removes
`hc_t1` as *one route* to `hc : c ≤ 1` while `c ≤ 1` **remains true and provable** via the `1/2`
arm. **A pass therefore proves nothing about vacuity.** If it passes, determine *which* hypothesis
discharged `hc1`, record that as a routing fact, and **do not treat it as a defect.**
(Note `1/40 → 1` is a no-op mutation — `c ≤ 1` holds at equality — so it tests nothing. Use `> 1`.)

## EXIT TEST
1. `saltbuild.sh Salt.SW.TBalR8`, then `saltbuild.sh Salt.SW.TBalTall` while iterating; full
   `saltbuild.sh` at wave exit with **`saltbuild EXIT=0`** and no new warnings.
2. **BOTH** `dh_repulsion_ordered` and `dh_repulsion_tall` build, same witness shape `⟨680, c, 14⟩`.
3. `#print axioms` on both = `[propext, Classical.choice, Quot.sound]`, via
   `saltbuild.sh ScratchTS2.lean` — **unique name, do NOT commit it.** `ScratchTS1.lean`,
   `ScratchCT.lean`, `ScratchW3T.lean`, `ScratchW4A.lean`, `ScratchW4Q.lean`, `ScratchW5T.lean`
   belong to other waves — **do not disturb them.**
4. The mutation check above, both outcomes recorded.
5. **Record the post-wave ten-arm table as a comment beside BOTH `c`-min blocks.**

## THE ARM TABLE — the ledger this wave must not lose
`c` is a `min` over ten arms (eleven in R8); `log(1/c)` is the **MAX**.

| arm | landed | after TS-1+TS-2 |
|---|---|---|
| `2^{−250}` → `1/40` | 173.29 | 3.69 |
| **`(c₀/32)^{17/3}`** | 86.23 | **86.23 ← BINDING** |
| `(1/805)^{50/49}` | 6.83 | 6.83 |
| `(1/(8·1610·e))^8` → A-row γ | 83.71 | 66.87 |
| `1/2` | 0.69 | 0.69 |
| `(1/KEβ)^8` → γ_Eβ | 536.67 | 32.15 |
| `(c₀/KEρ)^8` → γ_Eρ | **631.58 ← BINDING** | 25.58 |
| `1/(3A₀)` | 4.85 | 4.85 |
| `1/18` | 2.89 | 2.89 |
| `1/576` | 6.36 | 6.36 |
| **MAX** | **631.58** | **86.23** |

`c₀ = 1/126848` (`ZeroFreeReal.lean:392/:605`), `log(1/c₀) = 11.7507`.
**Recompute the two Eρ/Eβ rows against the actual post-TS-1 constants** (TS-1 changes `627 → 248`
and, tall-side, `636 → 570`) rather than copying these figures — and say so in the flags entry if
they differ from the predictions above.

## IRON RULES
No `sorry`. No `native_decide`. No new axioms. **Never alter a blueprint statement to make a proof
go through** — flag it in `docs/blueprints/flags.md` instead. ~3 serious attempts per piece, then
flag and move on. **DO NOT TOUCH** any `Salt/HB/Lemma7*.lean` (another seat is wiring them),
anything under `papers/`, `CLAUDE.md`, `docs/MODEL_POLICY.md`, or blueprint node tables.
**HELD, NOT YOURS:** TS-3 (S3+S4), the dossier §6 design ruling, and the `k → 1` scope are
statement-layer and HELD. If you find yourself editing `ray_pow_bound`'s statement, or `a`/`m`/`b`,
or `k`, **you have left your wave** — stop and report.

## 🔧 GREP WARNING — YOU WILL NEED THIS
BSD `grep` treats `^` mid-pattern as an anchor, so `grep -n "c ^ (1 / 8" Salt/SW/TBal*.lean`
returns **zero matches** while `grep -nF` on the same pattern returns **28**. In Lean source,
**always `grep -F`** (or escape `\^`). An empty grep here is not evidence of absence — this defect
nearly cost the math seat the four-site census above.

## DELIVERABLE
Lean edits in both towers; a `docs/blueprints/flags.md` entry (`## ⟦TAU-SHARP TS-2 — …⟧`) recording
what landed, attempt counts, the honest line count, **both mutation-check outcomes with error text
quoted**, and the recomputed arm table; ONE commit `play M: TAU-SHARP TS-2 — …` with `[skip ci]` on
its own line before the trailers and **explicit pathspecs only**; push after commit.

**Report back:** what landed, what did not and why, the honest line count, the recomputed arm table
with the new MAX, both mutation outcomes, and the commit SHA.

## HONEST STATEMENT — put this in the landing commit so no later reader misreads it
`log(1/c)`: **631.58 → 86.23**, i.e. §D2's `e^{1264}` → `e^{172}`, with **no parameter changed and
no statement outside the two files**. Per TS-0's K3 this is explicit-constant hygiene: it moves the
`hN+ ∧ hηq` non-emptiness floor, and it buys the **N11 door nothing**, because
`imsz_gives_fulcrum_witnesses` accepts every *constant* `C > 0` — the door is gated on the L-power,
not on the size of `log(1/c)`.
