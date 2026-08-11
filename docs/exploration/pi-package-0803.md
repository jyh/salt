# The Fulcrum — submission package (2026-08-03)

**Agent:** PI-PACK. **Purpose:** make `arXiv post → Pi submit` a
form-filling exercise with zero assembly latency. Everything a
submission form or a covering letter will ask for is either answered
below or named as an open decision with the facts a decision would
consume.

**Companion document:** `docs/exploration/pi-prep-0731.md` (PREP-PI's
ground survey — the venue requirements, the G1–G18 gap checklist, the
verification-appendix spec, the cover-letter fact sheet). This file does
not repeat it; it records what changed since, what was applied to the
manuscript, and the ordered sequence.

**Citation law.** Web claims carry their URL (all URLs here are
PREP-PI's, re-used not re-verified — re-check any URL before relying on
it at submission time). Repo claims carry `file:line`. Repo numbers are
as of `HEAD = b828cf1`, 2026-08-03, and are re-measurable by the
commands given in §4.

**Voice law.** Everything below is facts and bullets. Nothing here is
drafted prose and nothing is paste-ready. JYH voices the covering
letter, the overview, and every word that a human at Cambridge will
read.

---

## 1. THE TRIM PATCH — FINDING (read this first)

**There is no flagship trim patch, and there never was one.** The item
tracked as "the trim patch" is a *different artifact in a different
lane*:

- `docs/exploration/jacobian-trim-preview.patch` (101 lines), created by
  commit `387f330` (2026-07-31 08:00 "the PR fixed (module-mode) + trim
  prepared") and refreshed by `55e825c` (2026-07-31 08:35 "the refreshed
  trim patch").
- Its target is `Counterexamples/JacobianConjecture.lean` — the
  **mathlib PR** docstring, in the Jacobian-counterexample lane. It
  trims module-docstring prose and the `formal-conjectures`
  correspondence note. It has no relation to
  `papers/flagship/main.tex`.
- The ledger entry that banked it is `docs/blueprints/flags.md:18247`
  ("the PR module-fix pushed + **the trim PREPARED-unpushed**"), which
  is unambiguously the PR.
- The line that made it look like a Fulcrum item is
  `docs/exploration/council-0801.md:69` — a status bullet reading
  "**The Fulcrum**: trim patch standing by; Pi prep dossier complete;
  arXiv gated on endorsement only." The trim patch belongs to the
  bullet above it, not to the Fulcrum. **This is a mis-bucketed council
  line, and it has now propagated into two briefs.** Correct it at the
  source if council-0801 is ever revised.

**Consequence for the paper's length.** No trim was owed on length
grounds either: PREP-PI checked and **Pi states no page limit and no
word limit** anywhere in its author instructions or its IFC PDF — the
only manuscript rule is "Papers should be typed with generous margins.
Pages must be numbered" (Pi IFC PDF p.2; `pi-prep-0731.md:204-207`). The
manuscript is 10 pages. Nothing was cut for length, and nothing should
be.

**What was applied instead** (the dossier's own recommendations, item
G16, the only trim-genre item in the checklist): §2 below.

---

## 2. WHAT CHANGED IN `papers/flagship/main.tex` TODAY

Three edits. Two are Pi-conformance; one is the C⋆ note. No claim, no
theorem statement, no number, and no acknowledgment text was touched.
File grew 793 → 820 lines.

### 2.1 CUT — the `companion` bibliography entry

Deleted:

```
\bibitem{companion} J.~Hickey, \emph{The Salt method}, in preparation.
```

Why: Pi's IFC is explicit — "Any papers mentioned in the text that have
not been at least submitted for review, should be cited as eg. 'T.
Smith, unpublished observations' and **must not appear in the reference
list**" (Pi IFC PDF pp.2–3; `pi-prep-0731.md:219-221`). The entry was
also **uncited** — mechanically confirmed, no `\cite{companion}`
anywhere — so nothing broke. The prose mention survives untouched at
`main.tex:703-705`: "A companion paper (\emph{The Salt Method}) will
give the full treatment", which is exactly the handling Pi prescribes.

This is the only cut.

### 2.2 REORDER — the bibliography, alphabetical by first-author surname

Pi requires "References should be listed at the end of the paper and
numbered in alphabetical order (by surname of the first author).
References should be cited numerically in the text" (Pi IFC PDF p.2;
`pi-prep-0731.md:216-218`). The list was in citation-ish order. New
order (9 entries):

1. Chen1973 · 2. HalesKepler · 3. HB1983 · 4. Littlewood1922 ·
5. mathlib · 6. MR2016 · 7. MRT · 8. Maynard2015 · 9. TaoChowla

(`mathlib` sorts before `Matomäki` on "math" < "mato"; MR2016 before
MRT on the shorter author list.) A one-line source comment above
`\begin{thebibliography}` records the convention. No `\bibitem` key
changed, so every `\cite` still resolves; `amsart` renumbers
automatically.

### 2.3 ADDED — the C⋆-vs-C⁽¹⁾ remark (§4, after the existing remark)

FULCRUM-ROAD's flagged item (`fleet-meeting-0803-brief.md:50`;
`council-0803.md:84`). Inserted as a second `remark` in
`\section{The fulcrum}`, immediately before the §5 rule. Verbatim as
committed:

> **Remark (The two arms of $C^\star$).**
> Only the second arm of $C^\star = \max(C^{(1)}, 2/c_0)$ is a numeral.
> The first, $C^{(1)} = \exp\exp\{2A/(\mathfrak{S}\,C(\alpha))\}$ in the
> notation of [HB1983] (its Corollary 2, with $A$ the effective constant
> of its Corollary 1), is the threshold at which that engine's error
> budget closes. It is a double exponential: an inner exponent as small
> as $2A/(\mathfrak{S}\,C(\alpha)) = 10$ already places $C^{(1)}$ near
> $e^{22026}$, against the reality arm's $2/c_0 = 253696$. So $C^{(1)}$
> decides the maximum, and the constant this paper exhibits as a numeral
> is the reality floor — the quality at or above which Theorem 4.2
> derives that the witnessing zero is real — not the quality at which
> any engine is expected to run.
>
> No statement here depends on the size of that gap. Theorem 5.1
> quantifies $C$ away: it is stated for every $C > 0$ and consumes the
> engine implication at that same $C$, so an engine supplying
> $h_{\mathrm{Engine}}$ at $C^{(1)}$ instantiates the dichotomy at
> $C^{(1)}$, with the same conclusion. The reality derivation runs in
> the same direction — its hypothesis is $C \ge 2/c_0$, so it applies a
> fortiori at any threshold above the numeral. We report $253696$
> because it is the arm the corpus certifies
> (`fulcrum_zero_real_numeral`), not as a prediction of where
> $h_{\mathrm{Engine}}$ will be supplied.

Every claim in it grounded before writing:

| Claim | Ground |
|---|---|
| $C^{(1)} = \exp\exp\{2A/(\mathfrak{S}C(\alpha))\}$, HB Cor. 2, $A$ from Cor. 1 | `docs/exploration/fulcrum_audit_source.md:33-36, :145` |
| inner exponent 10 ⟹ $C^{(1)} \approx e^{22026}$ | `docs/exploration/fulcrum-pass3-records/pass3_t4.md:88-89`; $\exp(e^{10}) = \exp(22026.47)$ |
| $2/c_0 = 253696$ at $c_0 = 1/126848$ | `Salt/Fulcrum/CZeroNumeral.lean:410` (`c_star_second_arm`, `norm_num`) |
| reality needs $C \ge 2/c_0$, and is monotone upward in $C$ | `Salt/Fulcrum/Basic.lean:93` (`hC : 2 ≤ C * c₀`); numeral form `CZeroNumeral.lean:427` (`hC : 253696 ≤ C`) |
| Thm 5.1 quantifies $C$ away | `Salt/Fulcrum/Dichotomy.lean:102` — `fulcrum_dichotomy {C : ℝ} (hC : 0 < C) (hEngine : FulcrumQualityMin C → TwinPrimeConjecture) : HeathBrownDichotomy`; the ¬F horn `Dichotomy.lean:82` is likewise `{C : ℝ} (hC : 0 < C)` |
| the F3 saturation clause (below $2/c_0$ the derivation fails) | `pass3_t4.md:79-92` |

Voice laws held: no "honest", no "load-bearing"; the two strong claims
("double exponential", "decides the maximum") are each paid by a number
($e^{22026}$ vs $2.5\times10^5$); the conditionality is named at the
statement it belongs to (Theorem 5.1's $h_{\mathrm{Engine}}$).

### 2.4 NOT done, deliberately — carried as decisions

- **Six uncited bibliography entries remain**: `Chen1973`,
  `HalesKepler`, `Littlewood1922`, `MR2016`, `MRT`, `Maynard2015`. Pi:
  "Only those works that are cited should be included in the references
  list." All six are discussed in the body **by name, without a
  `\cite`**. The fix is one `\cite` at each site — but the paper is
  under a JYH-ratified citation style (commit `ca41713`: citations must
  be parenthetical and survive the delete-the-bracket test), so
  placement is a voice call. Exact sites:
  `Chen1973` → `main.tex:242` ("a machine-checked Chen's theorem") and
  `:584` (the census row); `Littlewood1922` → `:194` (Thm 3.1's name)
  and `:210` ("the 1922 Littlewood region"); `MR2016` → `:652`
  ("the corpus's staged Matomäki–Radziwiłł program");
  `MRT` → `:650` ("Matomäki–Radziwiłł–Tao's Proposition 2.4");
  `Maynard2015` → `:580` ("the $k=2$ Maynard bound").
  **`HalesKepler` is not mentioned in the body at all** — it is either
  cited somewhere (the natural home is §2 or §10, as the venue's own
  formalization precedent) or removed. **JYH's call, six insertions.**
- **`\bibitem{Littlewood1922}` has no page range** (`main.tex:802-804`).
  Not supplied here — it needs a source check, not a guess.
- **The numbers were not refreshed.** See §4: they must be measured at
  the moment of posting, not now.
- **The source header comment** `main.tex:5` still reads "Target: Google
  approval -> arXiv ... -> Pi". The approval is in hand (7/30). It is a
  `%` comment — invisible in the PDF, but it ships with the source at
  acceptance. Trivial; left alone rather than touched without warrant.

---

## 3. VERIFICATION RECORD (2026-08-03)

No LaTeX toolchain exists on this machine (stated in the file's own
header, `main.tex:9-10`), so every check below is by inspection or by
script. Script kept out of the repo; it is reproducible from this
description.

### 3.1 LaTeX structural balance — **PASS, zero problems**

Checked over the comment-stripped source (a `%` preceded by `\` is not a
comment):

| Check | Result |
|---|---|
| `\begin`/`\end` environment stack | balanced, correctly nested, empty at EOF |
| unescaped `$` | 404 = 202 pairs, even; no pair spans a blank line |
| `\[` / `\]` | 14 / 14, every close after its open |
| braces `{` `}` (escaped ones excluded) | depth returns to 0, no negative excursion |
| `\ref` → `\label` | 21 refs, 30 labels, **no dangling ref** |
| `\cite` → `\bibitem` | 3 cited keys, 9 bibitems, **no dangling cite** |

Unused labels (harmless — hyperref targets): `def:sign`, `def:z`,
`rem:arms`, `sec:dichotomy`, `sec:forward`, `sec:intro`, `sec:spine`,
`sec:trust`, `thm:vmvt`.

**Caveat, stated plainly:** this establishes *balance*, not
*compilability*. There is no substitute for one `pdflatex` run before
posting — see §6 step 1.

### 3.2 `\leanname` / `\leaninline` inventory — **32/32 verified in the tree**

Not a spot check: every declaration name cited in the paper was matched
against a real declaration under `Salt/`, by a declaration-keyword regex
(not a bare grep). Five representative rows:

| Cited in paper | Found at |
|---|---|
| `Salt.SW.dh_repulsion_ordered` | `Salt/SW/TBalR8.lean:1752` |
| `Salt.Fulcrum.fulcrum_dichotomy` | `Salt/Fulcrum/Dichotomy.lean:102` |
| `Salt.HB.hb_l2c_master_unconditional` | `Salt/HB/L2cMasterUncond.lean:85` |
| `Salt.Parity.sufficient_true_not_parityInv` | `Salt/Parity/Z.lean:670` |
| `Salt.Entropy.Chowla.log_chowla_two_door_only` | `Salt/Entropy/Chowla/SpineFinal.lean:981` |

The other 27, all found: `zeta_zero_free_region_littlewood`
(`Vk/Littlewood.lean:409`), `zeta_zero_free_region_pow`
(`Vk/GrowthPow.lean:1044`), `vk_block_core` (`Vk/Core.lean:256`),
`vmvt` (`Vmvt/Summit2.lean:151`), `FulcrumQualityMin`
(`Fulcrum/Basic.lean:61`), `fulcrum_zero_real` (`Fulcrum/Basic.lean:93`),
`not_fulcrum_implies_noSiegelZeros` (`Fulcrum/Dichotomy.lean:82`),
`chen_omega_prod_le_three` (`Fulcrum/ChenCorollary.lean:34`),
`twin_almost_prime` (`BrunLower/TwinInstance.lean:16`), `glue_master`
(`HB/L2cGlue.lean:357`), `IsSignFunction` (`HB/SignChain.lean:39`),
`S1_le_S2Gen` (`HB/SignChain.lean:511`), `neutrality_rate`
(`HB/SignRate.lean:53`), `LamTildeGen_lamR_eq_vonMangoldt`
(`HB/SignLiouville.lean:93`), `S2Gen_lamR_eq_S1` (`:97`),
`overshootExactGen_lamR` (`:103`), `PretenseSumGen_lamR_eq_zero`
(`:109`), `Z` (`Parity/Z.lean:102`), `ParityInv` (`:68`),
`TPC_implies_Z` (`:216`), `Z_implies_TPC` (`:687`),
`Z_trivial_of_not_completion` (`:125`), `fulcrum_zero_real_numeral`
(`Fulcrum/CZeroNumeral.lean:427`), `zero_free_region_all_numeral`
(`:387`), `log_chowla_two_budget_head`
(`Entropy/Chowla/SpineFinal.lean:750`), `TwinPrimeConjecture`
(`Salt/Basic.lean:25`), `NoSiegelZeros` (`TwinBar/SiegelTwin.lean:76`).

Two paper claims about *counts* re-verified: 59 sign-function
declarations in `Salt/HB/SignChain.lean` (`main.tex:507`) and ten
declarations in `Salt/Parity/Instances.lean` (`main.tex:593`) — both
still exact.

### 3.3 The λ(n)λ(n+1) shift-display fix — **PRESENT at the bytes**

- `papers/flagship/main.tex:635` reads
  `\frac{\lambda(n)\,\lambda(n+1)}{n}`. Confirmed by grep on the file,
  not from memory.
- It matches the kernel object: `logChowla2Fails`
  (`Salt/Entropy/Chowla/ChowlaFailure.lean:59`) sums
  `liouville n * liouville (n + 1) / n` — Tao (2.4) at `h = 1`.
- The neighbouring von Mangoldt twin sums at `main.tex:398-399` remain
  `\Lambda(n)\Lambda(n+2)` — correct, a different object. The erratum
  was display-only.
- Landed in `084b63d` (2026-08-02); banked at `flags.md:18854` item (2).

### 3.4 `\thanks` and Acknowledgments — **INTACT, unmodified**

- `\thanks` at `main.tex:32-34`: the Claude collaboration pointer, the
  §10 cross-reference, the commit-ledger sentence, "Written in a
  personal capacity."
- `\section*{Acknowledgments}` at `main.tex:745-758`, all five
  components present and byte-unchanged: personal capacity / personal
  time / personal equipment / no confidential or proprietary employer
  information; views-are-my-own; the Claude pointer with "implies no
  position or endorsement on the part of Anthropic"; "The author
  directed and ratified every design decision and bears sole
  responsibility for the claims"; the mathlib credit.
- **Still absent** (Pi asks for it under Acknowledgements): the word
  *funding*. See §5, G15.

---

## 4. THE PRE-POST NUMBER REFRESH (do this at posting time, not before)

The manuscript's corpus statistics are from 2026-07-19 and are now
understated by ~95%. They are **deliberately not patched here**: the
corpus grows daily, and a number frozen on 8/3 will be wrong on the day
the paper posts. Measure, then paste, in one edit.

Measured 2026-08-03 at `HEAD = b828cf1`:

| Site | Paper says | 2026-08-03 | Command |
|---|---|---|---|
| `main.tex:71`, `:135` | 324,724 lines | **631,947** | `git ls-files 'Salt/*.lean' \| xargs cat \| wc -l` |
| `main.tex:72`, `:136` | 751 files | **1,107** | `git ls-files 'Salt/*.lean' \| wc -l` |
| `main.tex:136` | 1034 commits | **1,847** | `git rev-list --count HEAD` |
| `main.tex:137` | ≈9,400 jobs | **9,680** | last full build, `flags.md:18931` |
| — (cover letter only) | 16,542 declarations | **18,953** | `python3 scripts/search/extract.py` (comment-masked; theorem 11,546 / lemma 5,150 / def 2,059 / structure 106 / instance 75 / abbrev 15 / class 2) |
| — (cover letter only) | 127 audit invocations | **147** over 23 `All.lean` files | `git ls-files 'Salt/*/All.lean' \| xargs grep -c '#audit_axioms'` |
| `main.tex:35` | `\date{July 19, 2026}` | **set to the posting date** | — |

**Declaration counts must come from the comment-masked extractor**, not
from grep: a naive line regex invents declarations out of wrapped module
docstrings (measured: 27 lines start with `class ` under `Salt/`, of
which **2** are declarations — `flags.md:18959`). A bare grep here
returns 19,025; the true figure is 18,953.

**The ledger count is unchanged and stays as written.** `#256` is still
the highest numbered entry (2026-07-20, `flags.md:11664`). The paper's
three phrasings are each exact as they stand: "(256 numbered entries)"
(`main.tex:73`), "stands at 256 catches" (`:122`), "256 numbered
catches" (`:696`). Catches banked after 7/20 carry dated headings
without numbers, so "256 catches" at `:122` is an undercount — the
tightest fix, if one is wanted, is one word: *numbered*. (Note there is
a **separate** operational-catch series in the ledger, currently at
#104 — do not conflate the two when quoting a number.)

---

## 5. OPEN DECISIONS — the dossier's checklist, updated to 2026-08-03

Statuses that **changed** since `pi-prep-0731.md`:

- **G3 affiliation / G9 conflicts of interest.** Two approvals are on the record; the submission is personal-capacity with a covering-letter COI line. Still JYH's call: what the first-page affiliation line literally says.
- **G5 the leanchecker sentence — effectively satisfied, one asterisk.**
  `main.tex:156-159` promises that "before submission every declaration
  is replayed through `leanchecker`". As of 2026-08-02 the ceremony
  stands at **1097/1097 content modules PASS, zero kernel rejections**,
  plus a `--fresh` gold replay of the terminal module
  (`Salt.MR.S16Compose`) and a `Salt.Brun` solo pass
  (`flags.md:18977`). Two modules were **OOM-killed, not rejected** —
  the import-only root aggregator `Salt` and `Salt.Maynard` solo,
  reproducibly across three environments including a quiet 64 GB machine
  (`flags.md:19476`); both are validated transitively and the direct
  solo replay is registered as standing hygiene needing a
  larger-memory host. **Decision, now small:** re-run at the posting
  HEAD and either (a) leave the forward-tense sentence as a promise kept,
  or (b) restate it in the past tense with the score. If (b), the
  asterisk must survive the restatement.
- **G13 artifact availability — unchanged and still the largest
  structural gap.** The repo is private (`origin
  https://github.com/jyh/salt.git`); the paper refers to "the
  repository" ~9× and never names it. The *legal* side of the public
  gate is now clear (the copyright-waiver filing, above); the remaining gates are the program's
  own — history purge, the SaltBench wave boundary, JYH's word
  (`flags.md:18364-18368`). Facts for a statement: Apache-2.0
  (`LICENSE`); toolchain `leanprover/lean4:v4.32.0-rc1`; `lake-manifest`
  version 1.2.0 with mathlib pinned at
  `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` (inputRev `v4.32.0-rc1`),
  batteries `954dbc98`, aesop `b5b9e2bb`, Qq `7a62bd13`, proofwidgets
  `e6518a67`, plausible `f3f26cc7`, importGraph `41f407a8`,
  LeanSearchClient `c5d5b8fe`, Cli `406ebb8c`. Pi's posture: data/code
  availability is **encouraged, not required**. See §7.3 for the shape
  of the statement the gate permits today.

Statuses **unchanged** from `pi-prep-0731.md` — read them there, they
are not restated here: **G1** ORCID (mandatory, registration free, a
form prerequisite not a manuscript one); **G2** MSC 2020 codes (missing;
candidate list at `pi-prep-0731.md:395`); **G4** the 350–500 word
Overview (missing, distinct from the 315-word abstract, JYH's to write);
**G8** AI-declaration framing ("joint work" / "co-authored" vs
Cambridge's authorship bar — present and over-satisfied on substance,
the question is whether one labelled declaration paragraph replaces four
distributed sites); **G10** APC £1,960 / $2,740 and the discretionary
waiver; **G11** licence CC-BY default; **G14** Appendix A is a
placeholder (12 headline rows, "Full index generated at release", and
the promised prose↔Lean side-by-side renderings are not in the file —
this one is visible to a referee); **G15** funding statement (no funder;
the *absence* is what a reader looks for); **G17** anonymity N/A;
**G18** `amsart` acceptable at submission.

---

## 6. THE POST-ENDORSEMENT SEQUENCE (exact order)

The gate is **arXiv endorsement only** — publishing approval is in hand
(7/30), the copyright-waiver filing copyright waiver in hand (7/31). The endorsement decision
(nudge + third endorser) sits on **Tue 2026-08-04**
(`council-0803.md:68`); Loeffler was the first approach, with a
shortlist fallback (`flags.md:15671`). One the copyright-waiver filing item is scheduled but
explicitly **not a blocker**: the reapplication naming Claude under the
waiver's GenAI clause 6, joined to the 8/4–8/5 sitting — JYH ruled arXiv
proceeds (`flags.md:18398`).

**Step 1 — compile, once, somewhere with LaTeX.** There is no toolchain
on this machine. `pdflatex` twice (cross-references and the
bibliography numbering both need the second pass), then read the log for
overfull boxes — the paper was swept to **0 overfull hboxes** on
2026-07-24 (`bbebd4c`), and §2's three edits are the first prose changes
since, so re-check that the new remark did not reintroduce one.

**Step 2 — the number refresh + date.** §4, in one edit, at the posting
HEAD.

**Step 3 — the leanchecker re-run at the posting HEAD.** §5, G5. Record
the score; it feeds both the manuscript sentence and the covering
letter.

**Step 4 — arXiv post.** `math.NT` primary, `cs.LO` cross — the route
recorded in the paper's own header (`main.tex:5`). Cambridge's preprint
policy permits sharing "any pre-submission version … anywhere, at any
time, under any licence", and "sharing your preprint anywhere else shall
not be viewed as prior publication" — so this does not compromise Pi's
step-0 item 4. arXiv's own metadata form wants: title, authors, abstract
(the 315-word one), MSC codes (G2), comments field (the natural home for
the corpus size, the axiom base, and the repository posture), and a
licence choice — pick one compatible with Pi's CC-BY.

**Step 5 — the arXiv ID lands.** Cambridge's encouraged best practice is
to cite the preprint in the submitted manuscript and to update the
preprint record to point at the Version of Record after publication. So
the ID goes back into `main.tex` before Pi submission if that practice
is followed.

**Step 6 — Pi submission**, at `https://cup.msp.org/submit_new.php?jpath=pi`
(MSP EditFlow, **not** Cambridge Core; e-mail fallback
`fom@cambridge.org`). Article type: **Research Article** (the only one
Pi accepts). Fill from §7.

---

## 7. THE SUBMISSION FIELDS, ANSWERED

### 7.1 Step-0 consent gate (all seven must be ticked)

Verbatim list at `pi-prep-0731.md:156-174`. The three that need a
position rather than a click:

- **Item 3, conflicts of interest** — "I confirm that I and my
  co-authors do not have any conflicts of interest, or any such
  conflicts have been declared in the covering letter." This is what
  makes the covering letter the designated place. Facts in play:
  employment at an AI-lab-adjacent employer; the paper's methodological
  subject is the use of a commercial AI vendor's product; the manuscript
  already carries the personal-capacity and no-endorsement statements
  (`main.tex:747-758`); publishing approval and the copyright waiver are
  both on the record. Pi's own example template is "Conflicts of
  Interest: Author A is employed at company B."
- **Item 5, the AI policy tick** — binding, per-submission. What the
  manuscript already does, against Cambridge's four principles: declared
  and explained at four sites plus a full methodology section (abstract
  `main.tex:43-47`, `\thanks` `:32-34`, acknowledgments `:751-756`, §10
  `sec:method`) — materially more than the policy demands; AI **not** in
  the author byline (`\author{Jason Hickey}`, sole author); no
  third-party text presented as the author's; accountability stated
  verbatim ("The author directed and ratified every design decision and
  bears sole responsibility for the claims"). The policy prescribes **no
  section, no wording, no word limit, no template** — only that the use
  be *declared and clearly explained*. Pi publishes no journal-specific
  AI supplement.
- **Item 6, the APC consent** — £1,960 / $2,740, "unless one of the
  following applies". The applicable route is the discretionary waiver
  ("This journal also grants waivers on a discretionary basis, for
  authors who are not covered by one of the above funding routes"),
  reinforced by the IFC's "No author will be expected to pay out of
  their own pocket", and decoupled from the decision ("The decision
  whether to accept a paper for publication will rest solely with the
  Editor, and without reference to the funding situation of the
  authors"). **Open — G10.**

### 7.2 Manuscript first-page requirements

| Field | State |
|---|---|
| Title | present, `main.tex:30` |
| Author name | present, `main.tex:31` |
| **Institution / affiliation** | **MISSING — G3.** Required: "please declare all applicable affiliations in the manuscript and source files" |
| **MSC 2020 codes, primary + secondary** | **MISSING — G2.** Candidates with official definitions at `pi-prep-0731.md:395`: 11N05, 11N35, 11N36, 11M06, 11M20, 11M26, 11N13, 68V05, 68V15, 68V20 |
| Short abstract | present, 315 words, `main.tex:39-75` |
| **Overview, 350–500 words** | **MISSING — G4.** Pi requires *both*. Must cover: general context (pointing to external papers as required); how this paper fits it; what the main new results are. Raw material at `main.tex:82-129` |
| ORCID (corresponding author) | **MISSING — G1**, mandatory, a form prerequisite |
| E-mail | required by the form regardless of the manuscript |
| Pages numbered, generous margins | `amsart` + `geometry` at 1.1in — satisfied |

### 7.3 Data-availability / artifact statement

Pi **encourages, does not require**, a Data Availability Statement, and
prescribes no wording. The statement the current gate permits — as
facts, for JYH to phrase:

- The paper is self-contained: every theorem it states is stated in
  full, and Appendix A maps statement → declaration → axiom audit. A
  referee can read and check the mathematics without the repository.
- The corpus is a private repository today, Apache-2.0 licensed, held
  private behind a program gate (history purge + the SaltBench wave
  boundary), not a legal one — employer copyright waiver granted
  2026-07-31.
- The pins that make the artifact reproducible when it opens are fixed
  and quotable now (§5, G13).
- The trust argument does not rest on a reader's access: `#audit_axioms`
  is a **build-time gate**, not a print
  (`Salt/Tactic/AuditAxioms.lean:81`) — it fails elaboration if any
  listed declaration's axiom closure exceeds the three. `lake build`
  succeeding *is* the audit passing.
- Public precedent for the author's kernel-checked work, if a referee
  wants to see the working style before the corpus opens:
  `github.com/jyh/jacobian-verify` (public; the kernel-checked
  verification of the 2026 Jacobian-conjecture counterexample) and
  `github.com/jyh/jas` (public; its paper on arXiv). Neither is salt
  code. **JYH's call whether either belongs in a submission at all** —
  they are different subjects.
- **Decision that cannot be deferred past submission:** a referee who
  cannot see the corpus cannot check §2's epistemic argument
  (`main.tex:132-184`, especially `:180-184`). Either the gate opens
  before or at submission, or the letter says plainly what a referee can
  and cannot verify, and offers the artifact under embargo. The
  verification-appendix spec that would make an opened artifact
  checkable in an afternoon is written and waiting at
  `pi-prep-0731.md:425-557` (toolchain pin, build, the audit mechanism,
  the independent replay, the TCB list, the finite check).

### 7.4 Covering-letter facts — BULLETS ONLY

**JYH voices this. Nothing below is a sentence to paste.** The full
fact sheet is `pi-prep-0731.md:561-677`; what follows is the delta and
the letter-specific items.

*What the paper is:*
- A single hypothesis (the fulcrum, `Salt/Fulcrum/Basic.lean:61`) at one
  fixed constant, under which — with a named engine hypothesis — Siegel
  zeros give infinitely many twin primes; the zero's reality is
  **derived**, not assumed (`Basic.lean:93`).
- Unconditionally: ¬fulcrum ⟹ `NoSiegelZeros` (`Dichotomy.lean:82`).
  With the engine implication: TPC ∨ NoSiegelZeros (`:102`). **No
  unconditional twin-prime claim is made** (`main.tex:129`), and every
  conditional is tabled with its exact residual (Table 1).
- Four unconditional banners, two of them firsts in any proof assistant
  (the Littlewood-strength region; the θ = 3/4 power-saving region).
- The keystone of the Heath-Brown engine, proven unconditional
  (`Salt/HB/L2cMasterUncond.lean:85`).
- The exchange-rate wall over arbitrary real sign functions, with
  Liouville as the exact fixed point — stated falsifiably.
- The parity gap as an object: `Z`, the gap theorem, `Z ⟺ TPC`, and a
  ten-theorem census placing the corpus inside the parity-invariant
  cone.
- Log-Chowla (Tao's theorem) machine-checked door-only.

*Machine-checked status* — use §4's numbers as measured on the day, not
these:
- 631,947 lines / 1,107 files / 1,847 commits / 18,953 declarations at
  2026-08-03.
- Zero `sorry`, zero `native_decide`, zero home-rolled axioms.
- Axiom base exactly `{propext, Classical.choice, Quot.sound}`, enforced
  at build time across 147 `#audit_axioms` invocations in 23 track
  manifests.
- Independent kernel replay: 1097/1097 content modules, zero rejections,
  2026-08-02, with the two OOM asterisks named (§5, G5). **Do not quote
  this as "every declaration" without the asterisk.**

*Disclosure and conflicts:*
- Sole author; AI not in the byline; AI use declared at four sites plus
  a methodology section.
- Personal capacity, personal time, personal equipment; no confidential
  or proprietary employer information; no employer or Anthropic
  endorsement.
- Employer publishing approval 2026-07-30; employer copyright waiver
  2026-07-31 (copyright only, scope-bound as described above).
- The method under study uses a commercial AI vendor's product — the
  fact a COI declaration would name.

*Venue fit:*
- Pi has published a formalization flagship: Hales et al., *A formal
  proof of the Kepler conjecture*, Forum of Mathematics Pi **5** (2017),
  e2 — in the paper's bibliography (and see §2.4: currently uncited in
  the body).
- Pi published `TaoChowla`, which §9 formalizes conditionally.
- Pi→Sigma: "If a paper is rejected from Pi on the grounds that its
  interest is more specialised, then you will be able to submit it to
  Sigma."
- **Scrupulous silence on editors** stands as the Captain's ruling
  (`flags.md:18247`). The board roster in `pi-prep-0731.md:343-372` is a
  factual list only; no editor is suggested, ranked, or recommended
  anywhere, and none should be in the letter.

*Prior art the letter should not overstate* — the comparison set a
referee will reach for, to be checked before any "first" is asserted:
the PNT+ project (Kontorovich–Tao); Eberl–Loeffler,
*Formalizing zeta and L-functions in Lean* (arXiv:2503.00959); Eberl et
al.'s Isabelle ζ/L development; Song–Yao's Isabelle PNT with the
classical error term. The paper's firsts are narrow and stated narrowly
(`main.tex:208-212`): a Littlewood-strength region, and a power-saving
region at θ = 3/4.

---

## 8. THE ORDERED RESIDUE — what is owed before the form opens

Blocking (the form will not accept a submission without them):
1. **ORCID** (G1) — register, free, minutes.
2. **MSC 2020 codes** (G2) — pick from the candidate list.
3. **Affiliation line** (G3) — decide the wording.
4. **The 350–500 word Overview** (G4) — JYH writes.

Blocking on judgment, not on typing:
5. **The artifact/gate timing decision** (G13, §7.3).
6. **The APC route** (G10) — waiver request, or not.
7. **The COI line** (G9) — what it names.

Owed at posting, mechanical:
8. **The number refresh + the date** (§4).
9. **One `pdflatex` run** (§6 step 1).
10. **The leanchecker re-run at the posting HEAD** (G5).

Referee-facing, strongly recommended, not required:
11. ~~**Appendix A completion** (G14)~~ — **DONE 2026-08-03**, see §9.1.
    The promise (now `main.tex:227-229`) is kept: 24 side-by-side entries
    covering 16 numbered statements + 63 declarations.
12. **The six uncited references** (§2.4).
13. **A funding statement** (G15) — the absence of funding, said.

---

## 9. WHAT LANDED AFTER THE DOSSIER WAS WRITTEN

### 9.1 APPENDIX A — the renderings (G14, §8 item 11) — **DONE**

`papers/flagship/main.tex`, commit of 2026-08-03. The existing 12-row
table is untouched; the renderings follow it as `\subsection`s A.1–A.9
(`main.tex:843-1309`).

- **Coverage:** 24 code blocks, 63 declarations, 16 numbered paper
  statements (Thm 3.1–3.4, Def 4.1, Thm 4.2, Thm 5.1, Thm 6.1, Def 7.1,
  Thm 7.2, Thm 7.3, Def 8.1, Thm 8.2, Thm 8.3, Prop 8.4, Thm 9.1) plus
  the two inherited almost-prime statements of §3 and the grade guard.
- **Fidelity:** every line was extracted from the tree at
  `HEAD = 244ba62` by script (declaration's source lines, proof body cut,
  nothing else changed) and then re-checked by an independent pass: all
  **180** transcribed lines match a `Salt/**.lean` line byte-for-byte.
  Only three LaTeX escapes occur inside a listing — `\{`, `\}`,
  `\textbackslash{}` — and a mechanical check confirms no others.
- **Packages added: one, `alltt`** (base LaTeX), plus 36
  `\DeclareUnicodeCharacter` mappings and one `\lchar` box macro
  (`main.tex:23-68`). Reason: Lean statements carry 36 distinct non-ASCII
  codepoints; `verbatim` makes UTF-8 lead bytes catcode-12 and breaks
  under pdfLaTeX, `alltt` leaves them active so the mappings apply. The
  mappings need a LaTeX kernel of 2018+ (UTF-8 by default); the one-line
  fallback for an older one (`\usepackage[utf8]{inputenc}`) is stated in
  the preamble comment. **The rest of `main.tex` is pure ASCII** (checked:
  0 non-ASCII bytes before this change), so the mappings affect the
  appendix only.
- **Width:** every listing line is ≤ 93 characters; `\lchar` sets each
  glyph in one tt-character box measured from the current font, so a line
  is exactly (chars × charwidth) wide — 93 × 4.725pt = 439pt against the
  6.3in (454.5pt) measure at `\footnotesize`. No listing can overflow.
  This is a computation, not a compile: §6 step 1 still owed.
- **Structural re-check after the edit** (same script shape as §3.1):
  environments balanced, brace depth 0, `$` count 472 (even), `\[`14 =
  `\]`14, no dangling `\ref`/`\cite`, and every non-ASCII byte in the file
  declared. Six labels that §3.1 listed as unused are now referenced
  (`def:sign`, `def:z`, `rem:arms`, `sec:dichotomy`, `sec:spine`,
  `thm:vmvt`).

**Three things the renderings expose, each stated in the appendix itself
rather than smoothed over** — a referee will find them, so they are on
the record here:

1. **Thm 3.3's constants are proof data, not statement data.**
   `dh_repulsion_ordered` (`Salt/SW/TBalR8.lean:1752`) binds `b c k`
   **existentially**; the numerals reach them at `:1836`
   (`refine ⟨680, c, 14, …⟩`), with `c` the explicit `min`-tower `set` at
   `:1776`. The paper's §3 says "There are explicit constants
   $b = 680$, $k = 14$" — true, and true of the proof; the appendix says
   where they live.
2. **No Lean declaration asserts the fulcrum's minimality.** The corpus
   carries `FulcrumQualityMin` (`Salt/Fulcrum/Basic.lean:61`) and the
   reality derivation (`:93`); minimality is a property of the demand
   audit (the Fulcrum Hunt) recorded in the exploration ledger. A.3 says
   so in as many words.
3. **Four of Prop 8.4's ten census declarations are outside the audit
   block.** `Salt/Parity/All.lean:22` names six;
   `parityInv_twin_gate_fails`, `parityInv_no_twin_weight`,
   `parityInv_noSiegel_iff` and `parityInv_N6_2`
   (`Salt/Parity/Instances.lean:53, 62, 72, 93`) appear in no
   `#audit_axioms` block anywhere under `Salt/` — mechanically checked
   across all 23 manifests. **Cheap fix, not applied here** (this agent
   touched no `.lean`): four names appended to that block. Until then the
   appendix reports the 6/10 split rather than claiming ten.

One inventory correction to §3.2: `twin_almost_prime` is cited there as
`BrunLower/TwinInstance.lean:16` — line 16 is inside the module
docstring's code fence; the declaration is at **`:771`**.

### 9.2 MSC-SUGGESTIONS (G2) — candidate codes for the form

**These are SUGGESTIONS. The Captain picks; nothing below is ratified.**
Pi wants primary + secondary on the first page (§7.2); arXiv's metadata
form asks for the same codes (§6 step 4), so one list serves both. Code
definitions are PREP-PI's transcription at `pi-prep-0731.md:395`
(re-used, not re-verified against <https://msc2020.org/> today — check
before entering them). The manuscript currently declares none:
`\subjclass` does not appear in `main.tex`.

*Primary — one of these two; the choice is what the paper is filed as:*

| Code | MSC 2020 title | Why it fits |
|---|---|---|
| **11N05** | Distribution of primes | The targets are prime-distribution statements: `TwinPrimeConjecture` (`Salt/Basic.lean:25`) is the conclusion of Thm 5.1 and one side of Thm 8.3; §8's whole apparatus is a statement about twin counting. |
| **11N36** | Applications of sieve methods | The machinery that carries the results is sieve-theoretic: the sifted window of §6 (`l2cWindow`, `Salt/HB/L2cCore.lean:159`), Chen at Ω ≤ 3 (`Salt/Fulcrum/ChenCorollary.lean:34`), Ω(n(n+2)) ≤ 20 (`Salt/BrunLower/TwinInstance.lean:771`), the Brun-grade witness of Thm 8.2. |

*Secondary — the four that name the paper's other halves:*

| Code | MSC 2020 title | Why it fits |
|---|---|---|
| **11M20** | Real zeros of $L(s,\chi)$; exceptional and Siegel zeros | The fulcrum **is** a hypothesis about real zeros of quadratic $L$-functions (`Salt/Fulcrum/Basic.lean:61`), `NoSiegelZeros` is its negation-side object (`Salt/TwinBar/SiegelTwin.lean:76`), and Thm 3.3 is a Deuring–Heilbronn repulsion contract. |
| **11M26** | Nonreal zeros of $\zeta$ and $L$-functions; RH | The two banner regions are ζ zero-free regions (`Salt/Vk/Littlewood.lean:409`, `Salt/Vk/GrowthPow.lean:1044`); Thm 4.2 derives reality *from* one of them. |
| **68V20** | Formalization of mathematics in connection with theorem provers | Every stated result is Lean 4 + mathlib, kernel-checked at a 3-axiom base; Appendix A is the statement↔declaration audit. |
| **68V15** | Theorem proving (automated and interactive theorem provers, deduction, resolution, etc.) | §10 is a method contribution about how the proofs were produced — difficulty-class routing across model tiers with the kernel as referee. |

*Alternates, if the form takes more than five:* **11N35** (sieves —
narrower sibling of 11N36); **11M06** ($\zeta(s)$ and $L(s,\chi)$ —
generic, and 11M20/11M26 are sharper); **11N13** (primes in progressions
— fits the Siegel–Walfisz / Bombieri–Vinogradov infrastructure of §3,
not the headline results).

*Deliberately not suggested:* **68V05** "Computer assisted proofs of
proofs-by-exhaustion type". The corpus forbids `native_decide`
(`main.tex:200`) and no result here is a proof by exhaustion; the code
would misdescribe the work to exactly the readers who search on it.

---

# ADDENDUM — 2026-08-10, THE WEEK-COLD REFRESH (math seat, life 9, under ruling (f-i))

*The paper was last touched 2026-08-03 11:08 (`e484956`). It went cold at
11:08 and the corpus landed a banner-grade improvement to one of its own
theorems at **20:44 the same day**. This addendum records what today's
sitting changed, re-runs this document's own gates against the live tree,
and refreshes §4's table — including §4's **line numbers**, which were
themselves stale.*

## A1. WHAT CHANGED IN `main.tex` TODAY

| # | Site | Change |
|---|---|---|
| 1 | Thm 3.3 (`thm:rep`) | **Restated to the unrestricted contract.** The height binder `\|Im ρ\| ≤ 1` is gone from the hypothesis and the cited name moves `dh_repulsion_ordered → dh_repulsion_tall`. Same $b = 680$, $k = 14$; the height-bounded twin is kept beside it in the new remark. |
| 2 | after Thm 3.3 | **New Remark `rem:repc`** — the constant's price: `log(1/c) = 86.2267` at `c₀ = 1/126848`, ten arms, binding arm `(c₀/32)^{17/3}`; the 8/6 sharpening from `631.5764`; and *what it does not buy* (the dichotomy is stated for every `C > 0`, so no threshold in the paper moves). |
| 3 | §9 `sec:forward` | **The hb-engine campaign given coordinates**: HB §§6–7, Lemma 10's single outside citation (Estermann, now a real `\cite`), the p.217 character-sum bound **discharged in the corpus for every primitive real character**, the Weil track's supply and its named `2^{v₂(k)/2}` residue, and the sawtooth completion kit with its two coefficient bounds. |
| 4 | intro, `:169` | The one-word ledger fix this document's §4 asked for: *"stands at 256 **numbered** catches"*. |
| 5 | bibliography | **`\bibitem{Estermann}`** added (Mathematika **8** (1961), 83–86), alphabetical between `Chen1973` and `HalesKepler`; it is **cited**, so the uncited list is unchanged at six. |

⛔ **AND ONE PAPER CLAIM THE WEEK FALSIFIED, which is why item 1 is not cosmetic.**
Thm 3.3 read *"$c > 0$ (with $c = c_1^8$ for an explicit $c_1$)"*. That was true
when written and is **false at the bytes today**: TAU-SHARP TS-2 replaced the
uniform exponent `8` by each row's own Hölder floor, so the arms now carry
`17/3`, `50/49`, `850/133`, `1700/3547`, `1700/5247`… — heterogeneous, and no
single `c₁^8` describes them (`Salt/SW/TBalTall.lean:2114-2130`, the realised
arm table). *A week-cold draft does not merely omit new results; it can assert
an old shape the corpus has since changed underneath it.*

## A2. THIS DOCUMENT'S OWN GATES, RE-RUN AT THE LIVE TREE

*A banked pin is a claim about a file that kept moving — 168 commits have
landed since this doc was written. Both gates were re-run, not assumed.*

```
§3.2 THE NAME GATE      96 names cited (was 90) · 71 resolve to a real
                        declaration under Salt/ (was 65) · +6 = exactly this
                        sitting's new citations, each with file:line:
    Salt.SW.dh_repulsion_tall                     Salt/SW/TBalTall.lean:2090
    Salt.HB.sum_two_forms_le_gcd_of_isPrimitive   Salt/HB/RealPrimStructure.lean:763
    Salt.HB.structure_of_isPrimitive              Salt/HB/RealPrimStructure.lean:737
    Salt.Weil.sawtoothMajorant_fourier_expansion  Salt/Weil/MajorantExpansion.lean:166
    Salt.Weil.norm_majorantCoeff_le_sq            Salt/Weil/Sawtooth.lean:970
    Salt.Weil.tsum_norm_majorantCoeff_le          Salt/Weil/Sawtooth.lean:1434
  ⚠️ NAMES STABLE, LINE PINS NOT: this doc records dh_repulsion_ordered at
     TBalR8:1752; it is at :1813 today. Cite names, verify lines at posting.
§3.1 THE BALANCE GATE   re-run after the edits: environments balanced and empty
                        at EOF · 518 unescaped $ = 259 pairs · \[ 16 / \] 16 ·
                        brace depth returns to 0 · 28 refs / 33 labels, ZERO
                        dangling · 4 cited keys / 10 bibitems, ZERO dangling.
                        Still BALANCE, not compilability — §6 step 1 stands.
AXIOMS                  #print axioms run LITERALLY (not the audit macro) on the
                        three load-bearing new citations, via ../saltbuild.sh:
                        dh_repulsion_tall · dh_repulsion_ordered ·
                        sawtoothMajorant_fourier_expansion — all three at
                        [propext, Classical.choice, Quot.sound]. EXIT=0.
FULL BUILD              ../saltbuild.sh at HEAD a1f8f0b: EXIT=0, 9,722 jobs.
```

## A3. §4's TABLE, REFRESHED — **AND ITS LINE NUMBERS WERE WRONG**

⚠️ **Every site in §4 above is stale by +47 lines.** Appendix A's Unicode
preamble (`\DeclareUnicodeCharacter`, ~47 lines) landed in `e484956` *after*
this document was written, and pushed every number site down. **The numbers
were the thing §4 was protecting, and the pointers to them had rotted.**

Measured today, HEAD `a1f8f0b`, with §4's own commands (line numbers are
pre-this-sitting; items 1–5 of A1 shift them again, so re-grep at posting):

| Site (2026-08-03 → **today**) | Paper says | 8/3 | **2026-08-10** |
|---|---|---|---|
| `:71`, `:135` → **`:118`, `:182`** | 324,724 lines | 631,947 | **658,073** |
| `:72`, `:136` → **`:119`, `:183`** | 751 files | 1,107 | **1,141** |
| `:136` → **`:183`** | 1034 commits | 1,847 | **2,034** |
| `:137` → **`:184`** | ≈9,400 jobs | 9,680 | **9,722** (measured today, EXIT=0) |
| cover letter only | 16,542 declarations | 18,953 | **19,690** (theorem 11,848 / lemma 5,491 / def 2,151 / structure 107 / instance 76 / abbrev 15 / class 2) |
| cover letter only | 127 audit invocations | 147 / 23 | **156 over 23 manifests** |
| `:35` → **`:82`** | `\date{July 19, 2026}` | set at posting | unchanged, per policy |

**THE POLICY IS UNCHANGED AND WAS DELIBERATELY NOT OVERRIDDEN TODAY: the
numbers are still not patched into `main.tex`.** They move daily; §4 says
measure-then-paste in one edit at posting time, and that is still right. What
this addendum fixes is the *pointer* rot, not the policy.

## A4. WHAT IS OWED, AND BY WHOM

- **Maestro (Fable) review before this goes anywhere** — ruling (f)'s own gate.
  Three items want a design eye rather than an executor's: (i) whether Thm 3.3
  should *lead* with the unrestricted form or state both; (ii) the §9 sentence
  attributing the p.217 bound to \cite{HB1983} *without proof* — that is a
  claim about another author's paper, sourced to `docs/sources/hb1983-notes.md:947`
  and to the corpus's own docstring, and it should be confirmed by a reader of
  the source, not by an executor's transcription; (iii) whether the Weil
  material belongs in §9 at all or wants a subsection of its own.
- **THE SUBMISSION CLICK IS THE CAPTAIN'S ALONE**, and evidence's 17:46 flag
  rides with it: `salt` is private behind a stated hard gate (history purge +
  the SaltBench boundary), and *the gate and the click are two different
  decisions*. Nothing in this addendum touches either.
- **Unchanged from §8's ordered residue:** one `pdflatex` run; the six uncited
  bibliography entries (JYH's voice call); `Littlewood1922`'s page range.

## A5. THE NUMBER SWEEP — evidence's 18:05 amendment, executed

*Their correction, adopted: a phrase-shaped staleness sweep covers only claims
that **announce their tense** ("remains", "not yet"). An asserted NUMBER
announces nothing, and it fails toward OVER-claiming — which is the direction
that propagates, because a reader who trusts it carries it onward. The target
list is enumerable: every exponent, constant, arm count and shape word the
prose asserts about an object the corpus owns.*

| Asserted | Site | Re-derived at the source today |
|---|---|---|
| $b = 680$, $k = 14$ | Thm 3.3 | ✅ both towers' witness is `⟨680, c, 14, …⟩` (`TBalR8:1921`, `TBalTall:2194`) |
| $c = c_1^8$ | Thm 3.3 | ⛔ **FALSIFIED** by TS-2's per-row Hölder floors — struck today (A1) |
| $\|Im\ ρ\| \le 1$ | Thm 3.3 | ⛔ **RETIRED** by `dh_repulsion_tall` — hypothesis removed today (A1) |
| $2^{31}$ | Thm 6.1 | ✅ `noncomputable def L2cCmain : ℝ := 2 ^ 31` (`L2cMaster.lean:356`) |
| the master's three rows | Thm 6.1 | ✅ shape matches the statement at `L2cMasterUncond.lean:85-92` term for term: $x/z_0$ · $(x/\log x)e^{5z_0}\mathrm{PS}$ · $e^{2z_0}(xz^{-1/8}+x^{9/10})L^3$ |
| ten parity instances | §8 | ✅ **10** (comment-masked extractor, `Salt/Parity/Instances.lean`) |
| 59 sign-function declarations | §7 | ⚠️ **the extractor reads 60** — structure 1 / def 11 / lemma 42 / theorem 6. **The file has ZERO commits since the 8/3 verification, so this is an INSTRUMENT delta, not rot.** $60 - 1$ structure $= 59$, which is very likely what the 8/3 count measured. **Flagged, not silently changed:** this document's own rule is that counts come from the comment-masked extractor, so either the number becomes 60 or the sentence names which 59. **A verified claim is not re-verified by a second instrument disagreeing with it once.** |
| 19 `ChowlaRegime` fields | App. A | covered — `Regime.lean` unchanged since the verification |

**THE ZERO-COMMIT COVER, and its honest limit.** Every other numeric claim in
the paper rests on a file that has **not moved since 2026-08-03**:
```
Salt/Fulcrum 0 · Salt/Parity 0 · Salt/Vk 0 · Salt/TwinBar 0 · Salt/Entropy (proofs) 0
L2cMasterUncond 0 · L2cGlue 0 · CZeroNumeral 0 · Vk/Core 0 · Regime 0 · Parity/Z 0
MOVED: Salt/SW 22 commits (TAU-EXT + TAU-SHARP) · Salt/HB (the WEIL-TRIO wave + HSIGMA-COMP)
```
⚠️ ***Zero commits proves NO ROT SINCE THE LAST CHECK. It does not re-verify a
number.*** Two were re-derived at the source anyway ($2^{31}$, the ten
instances); the rest inherit the 8/3 gate, and that inheritance is stated here
rather than presented as a fresh pass.

⛔ **THE CLASS THIS SWEEP STRUCTURALLY CANNOT COVER, named so a green is not
read as clean:** the priority claims — *"the first formalization of any
zero-free region of Littlewood strength"*, *"none had been formalized
before"*, *"to our knowledge a new mode of discovery"*. **They are claims about
the literature, and no instrument inside this repository can check them.** They
were not touched today and they want a reader, not a script.

**SPINE UNMOVED, CONFIRMED BY MEASUREMENT, NOT BY MEMORY:** `Salt/MR/` and
`Salt/Entropy/` carry no proof-content commits since 08-03 (two commits, both
comment-only), so §8's door and the conditional table's second row stand
exactly as written.
