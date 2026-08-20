# W-F3 — THE h-SHELL (P1 fill item 5). DESIGN BLOCK

**Pen:** math. **Drafted** 2026-08-20 13:4x. ⛔ **REFUTER PASS NOT RUN — not dispatchable yet**
(verify-posture law; the λ-BV block failed exactly this gate three hours ago and the lesson is
priced in below).

## §0 — WHAT THIS IS

The fork road's arc-finisher: the **h-analogue** of `Theorem23Shell`'s door-conditional terminal,
consuming the two landed h-objects and yielding the h-family terminal.

⛔ **PROVENANCE CORRECTED BEFORE USE.** The queue cites the seam guarantee as `ba20701`'s record.
**`ba20701` is NOT on the history** — a pre-flip orphan that `cat-file`s clean and prints a perfect
message. The live commit is **`5b5c0ed3`** (identical subject, ancestor of HEAD). *Tested with
`merge-base --is-ancestor`, which is the only test that distinguishes them.*

📌 **`Theorem23Shell` is a MODULE, not a declaration** — `Salt/Entropy/Chowla/Theorem23Shell.lean`,
rooted at `Salt/Entropy/All.lean:66`. *A declaration-shaped grep correctly returns nothing; that is
a category error in the query, not an absence and not a broken matcher.*

## §1 — THE OBJECTS, verified present at the cited lines

| object | where | role |
|---|---|---|
| `log_chowla_two_shell_xi` | `Theorem23Shell.lean:242` | **the statement to mirror at `h`** |
| `log_chowla_two_shell_xi_sq` | `:361` | the squared variant; consumed by `M4DoorL2.lean:408` |
| `circle_method_estimate_h` | `ShiftFork.lean:397` | supplies `hcirc` **at offset `p·h`** |
| `contradiction_of_mrtDoorXiH` | `ShiftFork.lean:338` | the door-firing contradiction at `bigXiH h` |
| `MRTUniformityXiH h R δ` | ShiftFork | the h-twisted door hypothesis |
| `bigXiH h R.eps H` | ShiftFork | the h-twisted large-spectrum set |

## §2 — THE DELTA, stated as a diff against the landed terminal

`log_chowla_two_shell_xi` takes `(R : ChowlaRegime) {H} [NeZero H]`, regime bounds, an entropy
datum `hI`, a `(2.11)` lower bound `h211`, a circle-method bound `hcirc` at offset `j + p`, a
spectrum cap `hXi`, the door `MRTUniformityXi R δ`, and budget inequalities. **The h-analogue
changes exactly four things:**

1. **add** `(h : ℕ) (hh : 0 < h)`;
2. `hcirc`'s inner offset `j + (p : ℕ)` → **`j + (p : ℕ) * h`** — this is precisely
   `circle_method_estimate_h`'s conclusion, so `hcirc` becomes *supplied*, not carried;
3. `bigXi R.eps H` → **`bigXiH h R.eps H`** everywhere (in `hcirc`'s tail sum and in `hXi`);
4. `MRTUniformityXi R δ` → **`MRTUniformityXiH h R δ`**, and the contradiction step routes through
   `contradiction_of_mrtDoorXiH` rather than its untwisted twin.

**Everything else — the regime bounds, `hI`, `h211`, the budget arithmetic — is unchanged.**
⇒ *This is a transport along one parameter, not a new estimate. The constant carried by
`circle_method_estimate_h` is `h·(1 + 2·C₀)` per `5b5c0ed3`'s record: **the wrap multiplies the
periodization coefficient**, so the budget inequalities inherit an `h` factor and must be
re-checked, not assumed to transport.*

## §3 — KILL-CHECKS (the refuter pass must run these; wave 1 is gated on them)

**J1 — DOES THE BUDGET SURVIVE THE `h` FACTOR?** `circle_method_estimate_h`'s constant carries `h`.
`hbudget1`'s left side is `C·(H/log H)·(c₀·ε) + C·(H/log H)·ε²`. **KILL CONDITION: if the `h`
factor breaks the budget inequality for `h > 1`, the terminal is vacuous above `h = 1` and the
"arc-finisher" finishes nothing.** *Check the inequality symbolically before any Lean is written.*

**J2 — IS `h = 1` THE LANDED THEOREM, ON THE NOSE?** The h-analogue at `h = 1` must reduce to
`log_chowla_two_shell_xi` definitionally or by one `simp`. **KILL CONDITION: if it does not, the
generalisation is not a generalisation and the two will drift.** *`5b5c0ed3` already landed an
`h = 1` compat lemma for the L² door — mirror that pattern, do not invent one.*

**J3 — IS `bigXiH h` NONEMPTY / IS THE CAP `K` ACHIEVABLE at `h > 1`?** A door-conditional
terminal whose hypothesis set is empty is vacuously true and worthless. **Exhibit a non-vacuity
witness that makes the mutated statement FALSE, not merely unreachable** (the E4a house rule).

**J4 — WHERE IS EVERY HYPOTHESIS SUPPLIED?** The landed terminal carries ~15 hypotheses. For each,
name the supplier in the h-wave *before proving anything*. **The kernel checks theorems, not that
they compose** — seven dangling interfaces in one file in one day on the E4a campaign, none
catchable by a build.

**J5 — THE λ-BV LESSON, PRICED IN: GREP THE TREE BEFORE BELIEVING A DESIGN DOC.** Three hours ago
this seat drafted a block whose "specified, unbuilt" nodes were **already landed**, because it
trusted a design document instead of the tree. **Before dispatching: grep for an existing
h-analogue.** *If `log_chowla_two_shell_xi_h` or similar already exists, this wave is a no-op.*

**J6 — SCOPE.** E7's fence binds: nothing here claims a band floor. And this terminal is
**door-conditional** — it consumes `MRTUniformityXiH`, it does not discharge it. Discharging
`MRTUniformityXi` is the standing recon lane (QUEUE P2 item 9), not this wave.

## §4 — WAVE SHAPE (conditional on J1–J6)

One Opus executor: state the h-analogue in `Salt/Entropy/Chowla/ShiftFork.lean` (where both inputs
live, so no import is added and no cycle is risked — the two-file placement `5b5c0ed3` established
carries the seam across the `CircleMethod → ShiftFork` boundary), prove it by transport from the
landed terminal, add the `h = 1` compat lemma, root and audit in the same commit.
**Class B/C. Not a campaign.**
