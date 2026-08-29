# W-F3 — THE h-SHELL (P1 fill item 5). DESIGN BLOCK

# ⛔⛔ REFUTER VERDICT (lens A, 14:1x) — **J1 REFUTED. THE "ONE-PARAMETER TRANSPORT" FRAMING IS FALSE. THIS IS A BRIDGE CAMPAIGN, NOT ONE EXECUTOR.**
*(Lens B — vacuity/interface/scope — still running; its verdict will be folded in on return.)*

# ⛔⛔ REFUTER VERDICT (lens B, 14:2x) — **J3 AND J4 ALSO REFUTED. "ARC-FINISHER" IS AN OVERCLAIM AGAINST A FILE WHOSE OWN HEADER SAYS OTHERWISE.**

## B1 — MY KILL-CHECK J3 IS MALFORMED AND CANNOT BE SATISFIED
`log_chowla_two_shell_xi` concludes **`False`** — its entire content *is* that its hypotheses are
unsatisfiable. **A "non-vacuity witness" satisfying all of them would REFUTE the landed theorem.**
I fused two different tests: E4a's mutation control (witness against the *mutated* statement) and
a satisfiability check. *Only the first is runnable here, and it says nothing about vacuity.*

## B2 — THE DOOR HAS NO PRODUCER, AND AT `h ≥ 2` THE ROUTE IS INVERTED
`hXi` **is** supplied — by `bigXiH_bounded` (`ShiftFork.lean:253`, landed, `K := h·C`), **which my
block never named.** But the door is not: `mrtUniformityXi_of_absWindowBound` runs through
`BigXiArcTight`, whose arc-tightness follows from largeness at **`ξ`**, while `bigXiH h` asserts
largeness at **`−(h·ξ).val/H`** — the arc supply lands on the **wrong frequency**.
🔑 ***`ShiftFork.lean:292-295` says it in its own words: "`MRTUniformityXiH h` is the `h`-family's
OPEN HYPOTHESIS … this file adds no producer and claims none."*** ⇒ **Calling this "the fork
road's arc-finisher" is an overclaim I made against a file that states the opposite in its header.**

## B3 — THE HYPOTHESIS COUNT WAS 33% LOW, AND "EXACTLY FOUR CHANGES" IS FALSE
I wrote *"~15 hypotheses"*. Mechanically, from the **signature** (`:242-272`): **20 Prop
hypotheses**, 1 instance, 10 data — 30 binder groups. ⛔ **The docstring-shaped count again, third
time today.** And **ELEVEN of the twenty** (`hne hreg hH hlog hhead ht hg hgle hI hc₁ h211`) exist
*solely to feed `outer_combine`*, which is hard-coded at offset `j + p`. At `h > 1` their consumer
produces the wrong object and `le_trans hoc (le_trans hB …)` will not typecheck.
⛔ **Also false: §4's "no import is added".** `shellError` (`Theorem23Shell.lean:52`) is **not** in
`ShiftFork`'s import cone, so stating the terminal there *does* add an import.

## B4 — ⛔ AND MY SIGNATURE ERROR, COMMITTED IN A BLOCK THAT CITES THE LAW AGAINST IT
§1's table says `log_chowla_two_shell_xi_sq` is *"consumed by `M4DoorL2.lean:408`"*.
**`M4DoorL2.lean:408` IS PROSE inside a `/-! … -/` section-doc block, and `Salt/MR/M4DoorL2.lean`
does not import `Theorem23Shell` at all.** ***Docstring-as-declaration — the exact defect in my own
banked six-corrections law — written into a design block whose J-gates cite that law.***
The real consumers: `SpineFinal.lean:1302` · `S16Uniform.lean:219` · `HloExport.lean:362` ·
`HloExportFlat.lean:196`. And `_sq` consumes **`MRTUniformityXiL2`**, is **`K`-free**, and would
need `MRTUniformityXiL2H`/`contradiction_of_mrtDoorXiL2H` — objects my §2 delta never mentions.
**§1 lists the L² object as in-scope while §2 specifies only the L¹ path. Pick one.**

## ⇒ SPLIT, per lens B (J6 survives: an h-terminal is strictly WEAKER, so no downstream consumer is at risk)
**Wave A — Class C, dispatchable now:** the h-port of `fBridgeG`/`fBridgeF` and the deterministic
`|·| ≤ 1` bounds. *Genuinely offset-agnostic; genuinely a transport.*
**Wave B — Class C, CAMPAIGN-TIER, not one executor:** `badSet_h`, `fBridge_concentration_decoupled_sharp`
at `h`, `badSet_transport_at_calibration`, `outer_badMass_le`, `outer_combine_h`. **This is the
concentration/entropy heart.** Needs its own design block.
**Wave C — Class B, gated on A+B:** the terminal + the `h = 1` compat (which is a 3-lemma rewrite
off ALREADY-LANDED compats), plus the `Theorem23Shell` import.

---

## A1 — MY KILL-CONDITION WAS A PHANTOM
J1 asked whether the budget survives the `h·(1+2·C₀)` constant. **The constant is real**
(`CircleMethod.lean:1139` witnesses `⟨(h:ℝ)*(1+2*C₀), …⟩`) **and INERT**: the shell takes
`{C : ℝ} (hC : 0 < C)` **universally** (`Theorem23Shell.lean:147, 255`) with `hcirc` as a
hypothesis, so **the h-shell never instantiates `C`** and the budget cannot inherit anything.
*My J1 was aimed at a step that does not occur in this object. The arithmetic, done anyway for the
downstream instantiation, does not collapse at `h = 2` either — `h` enters linearly as a divisor
of the admissible window.*

## A2 — ⛔ THE ACTUAL KILL: THERE IS A FIFTH CHANGE, AND IT IS CAMPAIGN-SIZED
Offending sentence: *"Everything else — the regime bounds, `hI`, `h211`, the budget arithmetic —
is unchanged."* **`hI` is h-free; `h211` is NOT.**
`h211` is stated over `fBridgeF = ∑_p fBridgeG ∘ residueProj`, and **`fBridgeG` bakes the offset
multiplier 1 into its DEFINITION** (`FBridge.lean:89-92`, `windowVal H v (j + (p:ℕ))`).
🔑 ***Its own docstring says so in as many words: "at the Liouville model (`a=1,b=0,h=1,c_p=1`)".
The parameter I proposed to generalise is named FIXED AT 1 in the definition I proposed to reuse.***
Machine-checked: the offset-1 and offset-`p·h` correlations are **not defeq**, so the shell's
`have hcirc' : ∀ n, |gm n| ≤ RHS n := hcirc` cannot fire and the chain does not typecheck —
**precisely the "kernel checks theorems, not that they compose" class this block cites in its own
J4, walked into by §2.**
⇒ **THE FIFTH CHANGE:** h-versions of `fBridgeG`/`fBridgeF`, hence of `outer_combine`
(`OuterCombine.lean:281`, carries no `h`) and its whole cone — `fBridgeF_abs_le_box*`, `boxGrade`,
`badSet*`, `fBridge_var_le`, `fBridge_concentration*`, `fBridgeG_mean`, `fBridgeF_mean`,
`fBridge_varTerm` — plus (2.11) restated at shift `h`. **Measured: 19 `fBridge*` declarations and
`outer_combine`, ZERO carrying an `h` today.** *That is re-deriving Tao §2's bridge at shift `h`.*
⇒ **AND A SIXTH:** if `hcirc` really is *supplied*, the shell also acquires
`circle_method_estimate_h`'s side hypothesis `((primeWindow eps H).card : ℝ) ≤ C₀·(ε²H/log H)`
and the parameter `C₀`.

## A3 — §2 CONTAINED AN INTERNAL CONTRADICTION AND I DID NOT SEE IT
Change #2 says `hcirc` *"becomes supplied, not carried"*; the next line says the budget arithmetic
*"is unchanged"*; the closing gloss says the budget *"inherits an `h` factor"*. **Those three
cannot all hold.** *No instrument catches this — only reading my own paragraph as a reader would.*

## A4 — J2 SURVIVES BUT NARROWER, AND MY CITATION WAS WRONG IN MY FAVOUR
`h = 1` does **not** reduce definitionally (`p*1` is not defeq to `p`; `bigXi_eq_bigXiH_one`
says of itself *"NOT `rfl`-grade"*; the door compat is proved by `propext`). It reduces by a
**3-lemma rewrite** — cheap, and it does not fork the corpus. ⛔ **But I wrote "mirror the L² compat
pattern, do not invent one" when the L¹ compat I actually need is ALREADY LANDED:**
`bigXi_eq_bigXiH_one` (`ShiftFork.lean:105`) and `mrtUniformityXi_eq_xiH_one` (`:307`).
*Nothing to mirror and nothing to invent — I sent an executor to build what exists.*

## A5 — J5 SURVIVES, independently re-verified with a positive control
No h-analogue exists; the control returns 20 `log_chowla_*` declarations across 9 files, so the
zero is real and not a broken matcher. **The wave is not a no-op — it is bigger than stated.**

## ⇒ RECLASSIFIED: **NOT Class B/C, not one executor.** Two honest exits, neither mine to choose:
**(1) NARROW THE CLAIM** — carry `outer_combine`'s output as an explicit hypothesis at offset
`p·h` (keep `hcirc` *carried*, not supplied). Then it genuinely is re-plumbing — **but the
terminal becomes conditional on TWO unproduced objects**, which contradicts J6's "door-conditional",
and §2's "`h211` unchanged" must be struck either way.
**(2) ACCEPT THE BRIDGE CAMPAIGN** — transport the `fBridgeG → outer_combine` cone to shift `h`
first. **That is the arc-finisher's real cost, and it was invisible in this block.**

---

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
