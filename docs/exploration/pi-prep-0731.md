# Pi submission prep — ground survey (2026-07-31)

**Agent:** PREP-PI (read-only on the repo; this file is the only write).
**Target:** *Forum of Mathematics, Pi* (Cambridge University Press), for the
first flagship paper `papers/flagship/main.tex` — "Twin Primes and Siegel
Zeros: a Fulcrum".

**Scope discipline.** Nothing here is submitted, and nothing in
`papers/flagship/` is modified. No human-voiced prose is drafted: every
section below is facts, bullets, and statuses for JYH to phrase. Editor
names appear as a factual roster only — **no editor recommendation is made
or implied** (Captain's ruling: scrupulous silence).

**Citation law used below.** Web claims carry their URL; repo claims carry
`file:line`. Repo numbers are as of HEAD = `main`, 2026-07-31.

---

## 1. Inventory — `papers/flagship/` as it stands

### 1.1 Files

| Path | Size | Note |
|---|---|---|
| `papers/flagship/main.tex` | 793 lines, 41,577 B, mtime 2026-07-24 14:35 | the paper; **self-contained** — no `\input`/`\include`, no external `.bib` |
| `papers/flagship/main.pdf` | 382,062 B, **10 pages**, letter, pdfTeX 1.40.29, built 2026-07-24 14:36 | in sync with the `.tex` (built 1 min after) |
| `papers/flagship/floor-chen-seed.tex` | 333 lines | a **different paper's** skeleton — "A machine-checked proof of Chen's theorem" (`floor-chen-seed.tex:29`); header targets arXiv → Pi (`:2`) |
| `papers/flagship/inserts/windmill-pattern.md` | 3,683 B | banked insert, JYH-ratified as a paper theme 2026-07-22; marked "JYH's voice pass expected" (`inserts/windmill-pattern.md:3-8`) |
| `papers/flagship/inserts/fmin-sweep-comparison.md` | 291,874 B | data insert |

No `README`, no `.bib`, no `Makefile`, no class file in `papers/`.

### 1.2 Front matter present

- **Class:** `\documentclass[11pt]{amsart}` (`main.tex:12`), `geometry` at
  1.1in margins (`:13`), `amsmath/amssymb/amsthm`, `booktabs`, `hyperref`
  (colorlinks), `microtype`, `xcolor` (`:14-18`).
- **Title:** "Twin Primes and Siegel Zeros: a Fulcrum" (`main.tex:30`).
- **Author:** `Jason Hickey` (`main.tex:31`) — **no affiliation, no email,
  no ORCID**.
- **`\thanks`** (`main.tex:32-34`): "Developed in collaboration with Claude
  (Anthropic's Fable~5 and Opus models); see §\ref{sec:method} and the
  repository's commit ledger, in which every commit is co-authored. Written
  in a personal capacity."
- **`\date{July 19, 2026}`** (`main.tex:35`) — stale relative to the 7/24
  build.
- **Abstract:** `main.tex:39-75`, **315 words** (measured:
  `awk '/\\begin\{abstract\}/,/\\end\{abstract\}/' main.tex | sed 's/\\[a-zA-Z]*//g' | wc -w`).
- **No MSC codes anywhere** in `main.tex`. **No keywords.**
- **Acknowledgments:** `main.tex:719-733` — unnumbered `\section*`. Contains
  (a) the personal-capacity / no-employer-resources / no-confidential-
  information statement, (b) the views-are-my-own disclaimer, (c) the Claude
  collaboration pointer + "likewise implies no position or endorsement on
  the part of Anthropic", (d) "The author directed and ratified every design
  decision and bears sole responsibility for the claims", (e) the mathlib
  credit. **No funding statement** (no funder to name — see §3).
- **Bibliography:** inline `thebibliography` (`main.tex:767-791`), 10 items,
  alphabetical by first-author surname, numeric `\bibitem` keys → cited as
  `\cite{HB1983}` etc. Rendered numerically by `amsart` default.

### 1.3 Structure (9 sections + 1 appendix)

| § | Label | Content |
|---|---|---|
| 1 | `sec:intro` | the four movements; conditionality as first-class |
| 2 | `sec:trust` | the corpus + the referee (mechanically excluded / specification gap) |
| 3 | `sec:banners` | Thms 3.1–3.4: Littlewood region, power-saving θ=3/4, DH repulsion, VMVT |
| 4 | `sec:fulcrum` | the discovery + Def 4.1 (the fulcrum), Thm 4.2 (reality derived) |
| 5 | `sec:dichotomy` | Thm 5.1 the dichotomy, `NoSiegelZeros` unfolded |
| 6 | `sec:keystone` | Thm 6.1 the master estimate, unconditional |
| 7 | `sec:walls` | Def 7.1 sign functions, Thm 7.2 neutrality+rate, Thm 7.3 the neutrality point |
| 8 | `sec:parity` | Def 8.1 `Z`, Thm 8.2 the gap theorem, Thm 8.3 `Z` iff TPC, Prop 8.4 the census |
| 9 | `sec:spine` | Thm 9.1 log-Chowla, door-only |
| 10 | `sec:method` | the Salt method |
| 11 | `sec:forward` | three campaigns + Table 1 (`tab:conditional`) — every conditional with its residual |
| App A | `app:index` | Table 2 — statement → declaration → axioms, 12 rows, "the three" |

### 1.4 Existing artifact / verification / AI-disclosure text (what is already there)

- **Verification, in-body:** `main.tex:142-163` (§2.1 "Mechanically excluded")
  — `sorryAx` propagation, `#audit_axioms` printing the closure, the three
  axioms, `native_decide` forbidden, tactics-vs-kernel trust surface, and the
  leanchecker sentence at `main.tex:156-159`: "before submission every
  declaration is replayed through `leanchecker`, the toolchain's standalone
  proof checker, independently of the elaborator and build cache that
  produced it."
- **Specification-gap discussion:** `main.tex:165-184`.
- **Appendix A** (`main.tex:736-765`): the statement↔declaration↔axiom table,
  with the comment `% At release: generated from the All.lean audit blocks`
  (`:740`) and the caption "Full index generated at release" (`:764`).
- **AI disclosure:** three sites — abstract (`main.tex:43-47`), `\thanks`
  (`:32-34`), acknowledgments (`:726-731`), plus all of §10 `sec:method`.
- **Artifact/repository availability statement:** **none.** The paper refers
  to "the repository" nine times (e.g. `main.tex:33`, `:122`, `:260`,
  `:434`, `:680`) but never names it, gives no URL, no DOI, no licence, no
  archived snapshot, and no availability statement.

### 1.5 Numbers asserted in the paper vs. the repo today

| Paper claim | `main.tex` | Repo today | Status |
|---|---|---|---|
| 324,724 lines of Lean | `:71`, `:135` | **537,908** lines (`git ls-files 'Salt/*.lean' \| xargs cat \| wc -l`) | **STALE (+66%)** |
| 751 files | `:72`, `:136` | **1,049** tracked `.lean` under `Salt/` | **STALE (+40%)** |
| 1,034 commits | `:136` | **1,735** (`git rev-list --count HEAD`) | **STALE (+68%)** |
| ≈9,400 compilation jobs | `:137` | 9,465 last measured, `docs/exploration/pilot.md:13367` | OK ("roughly") |
| 256 numbered ledger catches | `:73`, `:122` | max is still **#256**, `docs/blueprints/flags.md:11664` | number OK; see note |
| 59 sign-function declarations | `:482` | exactly 59 in `Salt/HB/SignChain.lean` | OK |
| ten census declarations | `:568` | exactly 10 in `Salt/Parity/Instances.lean` | OK |
| C\* = 253696 | `:284` | `fulcrum_zero_real_numeral` hypothesis reads `(hC : 253696 ≤ C)`, `Salt/Fulcrum/CZeroNumeral.lean:427` | OK |
| zero `sorry`, zero `native_decide` | `:143-153` | confirmed zero in tactic position; all 263 `sorry` grep hits are docstring prose | OK |

Note on the ledger: numbering **stopped** at #256 on 2026-07-20
(`docs/blueprints/flags.md:11664`). Ten further catch entries were banked as
dated headings without numbers (`flags.md:11676, 11691, 11704, 11727, 11747,
11763` — 2026-07-24; `:11779, 11795, 11808, 11818` — 2026-07-25). If
numbering had continued the count would be 266. "256" is defensible as
stated (it is the high-water numbered mark) but is no longer the count of
catches.

All 22 Lean declaration names cited in the paper **exist and their
namespaces match** — verified individually; e.g.
`Salt.SW.dh_repulsion_ordered` at `Salt/SW/TBalR8.lean:1752`,
`Salt.Parity.Z` at `Salt/Parity/Z.lean:102`,
`Salt.Entropy.Chowla.log_chowla_two_door_only` at
`Salt/Entropy/Chowla/SpineFinal.lean:981`.

---

## 2. Forum of Mathematics, Pi — current requirements (web research)

### 2.1 Submission route

- Submission is **not** through Cambridge Core. "We partner with a secure
  submission system to handle manuscript submissions"; the system is MSP's
  EditFlow at `https://cup.msp.org/submit_new.php?jpath=pi`.
  <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/author-instructions>
- Fallback: "If you cannot submit your paper via the above website, please
  submit this as an e-mail an attachment to fom@cambridge.org." (Pi
  Instructions-for-Contributors PDF,
  <https://www.cambridge.org/core/services/aop-file-manager/file/575a803676fa00070ad0e994>)
- Article types: "We accept the following types of articles: Research
  Article".
  <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/instructions-contributors>
- Pi↔Sigma relation: "If a paper is rejected from Pi on the grounds that its
  interest is more specialised, then you will be able to submit it to
  Sigma."
  <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/faqs-on-pi>
- Peer review: "All submitted articles are peer-reviewed, and the decision to
  accept is made by the Editors independently of the publisher." (same FAQ)

### 2.2 The submission-system consent gate (Step 0) — VERBATIM

Every author must tick these before the form opens
(<https://cup.msp.org/submit_new.php?jpath=pi>):

1. "I am submitting information voluntarily and agree to the use of the
   personal data I provide as described in this policy."
2. "If I am submitting information on behalf of co-authors, I have their
   consent to do so and my co-authors also agree to the use of their data as
   described in this policy."
3. "I confirm that I and my co-authors do not have any conflicts of
   interest, or any such conflicts have been declared in the covering
   letter."
4. "I confirm that this article has not been submitted or published
   elsewhere."
5. **"I have read and agree to comply with the Cambridge University Press
   Artificial Intelligence (AI) Contributions to Research Content Policy,
   and will transparently declare such use, in line with the guidance
   outlined in the policy and in accordance with the journal's
   requirements."**
6. "I/we consent to paying the Open Access Article Processing Charge (APC)
   in the event of successful acceptance, unless one of the following
   applies…"
7. "I have read and understood these statements/policies, and I accept."

Item 3 establishes that **a covering letter is the designated place for a
conflict-of-interest declaration**; item 5 is a binding, per-submission AI
declaration undertaking.

### 2.3 Manuscript preparation requirements

Source:
<https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/author-instructions/preparing-your-materials>
(current web page; supersedes the older PDF where they differ — see 2.7).

- **First page must give**: "Title", "The authors' name and institution
  (please declare all applicable affiliations in the manuscript and source
  files)", "The 2020 Subject Classification codes (primary and secondary)",
  "Short abstract."
- **Overview AND abstract — both.** Verbatim: "The overview should be between
  350 and 500 words and explain • The general context of the subject matter
  (pointing to external papers as required) • How the present paper fits
  within that context • What the main new results are. The abstract is a
  conventional abstract and it should be short and self-contained."
- **LaTeX**: "The LaTex template files for submission can be found following
  the links below". The template is **offered, not mandated at submission**;
  the binding requirement is at acceptance — "On acceptance of a paper,
  authors should forward to the Editorial Office at fom@cambridge.org the
  LATEX source code including the figures and all author-defined macro and
  style files, together with a pdf produced using the same file." (Pi IFC
  PDF, p.1.) Also: "The publisher reserves the right to typeset any article
  by conventional means if the author's TEX code presents problems in
  production." (Pi IFC PDF, p.1.) → **`amsart` is acceptable at submission.**
- **Length**: no page or word limit is stated anywhere on the author-
  instruction pages or in the IFC PDF. Manuscript rule is only: "Papers
  should be typed with generous margins. Pages must be numbered." (Pi IFC
  PDF, p.2.)
- **ORCID — mandatory**: "We require all corresponding authors to identify
  themselves using ORCID when submitting a manuscript to this journal."
  <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/author-instructions/submitting-your-materials>
- **Funding**: "Please identify all funding sources (by name and contract
  number, as appropriate)." — under the **Acknowledgements** heading (Pi IFC
  PDF, p.2).
- **References**: "References should be listed at the end of the paper and
  numbered in alphabetical order (by surname of the first author).
  References should be cited numerically in the text. Only those works that
  are cited should be included in the references list." … "Journal titles
  should be abbreviated as in Mathematical Reviews." … "NB. Any papers
  mentioned in the text that have not been at least submitted for review,
  should be cited as eg. 'T. Smith, unpublished observations' and must not
  appear in the reference list." (Pi IFC PDF, pp.2–3.)
- **Supplementary materials**: "Supplementary materials will not be typeset
  or copyedited, so should be supplied exactly as they are to appear
  online"; they are "a formal part of the academic record".
- **Conflicts of interest** (Pi IFC PDF, p.2): "If the authors have any
  Conflicts of Interests that they would like to declare, a statement should
  be included in the covering letter." … "Conflicts of Interest are
  situations that could be perceived to exert an undue influence on an
  author's presentation of their work. They may include, but are not limited
  to, financial, professional, contractual or personal relationships or
  situations." … "If no conflicts exist, the declaration does not need to be
  included in the cover letter." Example wording given: "Conflicts of
  Interest: Author A is employed at company B. …"
- **Licence**: "Before Cambridge can publish your manuscript, we need a
  signed licence to publish agreement." "Authors of articles published in
  the journal will hold the copyright of their published paper and articles
  will be published under a creative commons attribution license (CC-BY).
  The default licence is CC-BY (Attribution) but others are available on
  request: CC-BY-NC-SA … CC-BY-NC-ND." (Pi IFC PDF, p.1.)

### 2.4 Open access / APC

- Fully Gold OA. Current APC on the journal's fees page: **"GBP (£) 1960"
  and "USD ($) 2740"**.
  <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/author-instructions/fees-and-pricing>
- Funding routes and waivers
  (<https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/journal-policies/open-access-options>):
  institutional read-and-publish agreements ("in the majority of cases these
  cover the full costs of Gold OA"); the Cambridge Open Equity Initiative
  (100+ low/middle-income countries); grant-funded authors "are asked to use
  this funding to pay an APC"; and — the operative one here — "This journal
  also grants waivers on a discretionary basis, for authors who are not
  covered by one of the above funding routes."
- Decoupling clause: **"The decision whether to accept a paper for
  publication will rest solely with the Editor, and without reference to the
  funding situation of the authors."** (same page)
- Older Pi IFC PDF adds: "Waivers of APCs may also be available to those
  whose funding body and institution do not have funds available for APCs.
  **No author will be expected to pay out of their own pocket.**" (p.2) —
  note this PDF is stale on the amount (see 2.7).

### 2.5 Cambridge's generative-AI policy — the operative clauses, VERBATIM

The four "Cambridge principles for generative AI in research publishing",
announced 14 Mar 2023
(<https://www.cambridge.org/news-and-insights/cambridge-launches-ai-research-ethics-policy>),
restated in the journals ethics guidelines under **"AI contributions to
research content"**
(<https://www.cambridge.org/core/services/authors/publishing-ethics/research-publishing-ethics-guidelines-for-journals/authorship-and-contributorship#ai-contributions-to-research-content>):

1. **"AI use must be declared and clearly explained in publications such as
   research papers, just as we expect scholars to do with other software,
   tools and methodologies."**
2. **"AI does not meet the Cambridge requirements for authorship, given the
   need for accountability. AI and LLM tools may not be listed as an author
   on any scholarly work published by Cambridge."**
3. **"Any use of AI must not breach Cambridge's plagiarism policy. Scholarly
   works must be the author's own, and not present others' ideas, data,
   words or other material without adequate citation and transparent
   referencing."**
4. **"Authors are accountable for the accuracy, integrity and originality of
   their research papers, including for any use of AI."**

Plus: **"Please note, individual journals may have more specific
requirements or guidelines for upholding this policy."** (same page)

Authorship criteria on the same page (all four must be met): "Substantial
contributions to the conception or design of the work; or the acquisition,
analysis, or interpretation of data for the work"; "Drafting the work or
revising it critically for important intellectual content"; "Final approval
of the version to be published"; "Agreement to be accountable for all
aspects of the work". Non-qualifying contributors: "list anyone who does not
meet the criteria for authorship in an Acknowledgments section".

**What the policy does NOT specify:** no prescribed section, no prescribed
wording, no word limit, and no template for the AI declaration. The
requirement is only that it be *declared and clearly explained*. FoM Pi
publishes no journal-specific AI supplement (the Pi journal-policies hub
lists only open-access options, publishing ethics, research transparency,
rights and permissions, privacy, sponsorship and advertising —
<https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/journal-policies>).

### 2.6 Research transparency / data availability (Pi)

<https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/journal-policies/research-transparency>

- **"We encourage the use of Data Availability Statements to describe whether
  the materials that underpin research findings have been made available to
  readers, and if so, where."** → **encouraged, not mandatory.**
- Authors should "make evidence, data, code, and other materials that
  underpin their findings available to readers", preferably in "a dedicated
  repository" with "permanent identifiers and robust preservation policies".
- "This journal believes in the importance of transparent and reproducible
  research."
- No prescribed wording.

### 2.7 Version conflict to be aware of

The Pi "Instructions for Contributors" PDF linked from Cambridge Core
(<https://www.cambridge.org/core/services/aop-file-manager/file/575a803676fa00070ad0e994>)
is **stale**: it says "The 2010 Subject Classification codes" and quotes the
APC as "£770 / $1030". The current web pages say **2020** MSC codes and
**£1960 / $2740**. Treat the web pages as authoritative; the PDF remains the
only source for several items the web pages omit (cover-letter conflicts of
interest, proofs, citation format, the "no author out of pocket" sentence).

### 2.8 Preprint / arXiv posture

<https://www.cambridge.org/core/services/open-research/preprint-policy>

- Cambridge "permit[s] you to share any pre-submission version of your
  manuscript anywhere, at any time, under any licence."
- "sharing your preprint anywhere else shall not be viewed as prior
  publication."
- Encouraged best practice: cite the preprint in the submitted manuscript,
  and update the preprint record to link to the Version of Record after
  publication.
- Green-OA embargoes are irrelevant here: Pi is Gold OA CC-BY.
- → **arXiv-first (math.NT primary, cs.LO cross) is compatible with Pi
  submission**, which is the route already recorded in the paper's own
  header (`main.tex:5`).

### 2.9 Editorial board — FACTS ONLY, for awareness

Source:
<https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/about-this-journal/editorial-board>
(retrieved 2026-07-31). **No editor is suggested, ranked, or recommended in
this document.**

**Managing Editors** — Michael R. Magee (Durham); Jason Miller (DPMMS,
Cambridge).

**Pi Committee** — Simon Donaldson (Imperial); Martin Hairer (EPFL); Curtis
McMullen (Harvard); Alexander Razborov (Chicago, CS); Terence Tao (UCLA);
Richard Taylor (Stanford).

**Editors** — Mohammed Abouzaid (Stanford); Benjamin Bakker (UIC); Roman
Bezrukavnikov (MIT); Sara Billey (Washington); Lucia Caporaso (Roma Tre);
Henry Cohn (MIT); Ivan Corwin (Columbia); Jian Ding (Peking); Jacob Fox
(Stanford); Patricia Hersh (Oregon); Arieh Iserles (Cambridge); Niky Kamran
(McGill); Peter Keevash (Oxford); Bernhard Keller (Paris VII); Bo'az
Klartag (Weizmann); Bruce Kleiner (NYU); Marc Lackenby (Oxford); Lek-Heng
Lim (Chicago); Fanghua Lin (Courant); Ivan Loseu (Yale); Shachar Lovett (UC
San Diego); Ieke Moerdijk (Utrecht); Richard Montgomery (Warwick); Stefan
Müller (Bonn); Bruno Nachtergaele (UC Davis); Kenji Nakanishi (Kyoto); Hee
Oh (Yale); Guergana Petrova (Texas A&M); Jonathan Pila (Oxford); Dhruv
Ranganathan (Cambridge); Julian Sahasrabudhe (Cambridge); Anne Schilling (UC
Davis); Sylvia Serfaty (Sorbonne/NYU); Zuowei Shen (NUS); Theodore Slaman
(UC Berkeley); Kannan Soundararajan (Stanford); Gabor Szabo (KU Leuven);
Ulrike Tillmann (Oxford); Stevo Todorčević (Toronto); Ravi Vakil (Stanford);
Sarah Zerbes (ETH Zurich); Shouwu Zhang (Princeton); Ziquan Zhuang (Johns
Hopkins).

Two facts JYH may want on the record without any recommendation attached:
(i) T. Tao sits on the Pi Committee and is the author of `\cite{TaoChowla}`,
which the paper's §9 formalizes conditionally (`main.tex:776-778`,
`main.tex:586-605`); (ii) the paper already cites a Pi paper as precedent
for a formalization flagship — Hales et al., *A formal proof of the Kepler
conjecture*, Forum of Mathematics, Pi **5** (2017), e2
(`main.tex:786-787`).

---

## 3. THE GAP CHECKLIST

Legend: **PRESENT** (with `file:line`) / **MISSING** / **NEEDS-DECISION**
(JYH's call). Each row carries the facts a fix would consume; no wording is
drafted.

### 3.1 Hard blockers (submission cannot proceed / is non-compliant without)

| # | Requirement | Status | Facts for the fix |
|---|---|---|---|
| G1 | **ORCID for corresponding author** | **MISSING / NEEDS-DECISION** | Mandatory: "We require all corresponding authors to identify themselves using ORCID when submitting a manuscript to this journal" (submitting-your-materials). Repo-wide grep for "ORCID" across `docs/` and `papers/` returns **nothing** — JYH may or may not already hold one. Registration is free at orcid.org and is a prerequisite of the EditFlow form, not of the manuscript. |
| G2 | **MSC 2020 codes (primary + secondary) on the first page** | **MISSING** | Required first-page element. `main.tex` has none. Candidate codes and their official MSC2020 definitions (for JYH to select): 11N05 distribution of primes; 11N35 sieves; 11N36 applications of sieve methods; 11M06 ζ(s) and L(s,χ); 11M20 real zeros of L(s,χ) / exceptional zeros; 11M26 nonreal zeros of ζ and L-functions, RH; 11N13 primes in progressions; 68V20 "Formalization of mathematics in connection with theorem provers"; 68V15 "Theorem proving (automated and interactive theorem provers, deduction, resolution, etc.)"; 68V05 "Computer assisted proofs of proofs-by-exhaustion type" (68Vxx = "Computer science support for mathematical research and practice", a class new in MSC2020). <https://msc2020.org/> |
| G3 | **Author affiliation on the first page** | **MISSING / NEEDS-DECISION** | Required: "The authors' name and institution (please declare all applicable affiliations in the manuscript and source files)". `main.tex:31` gives the name only. This intersects the employer lane: the paper's `\thanks` (`:32-34`) and acknowledgments (`:722-733`) already assert personal capacity. The decision is whether the first page carries an employer affiliation, an "independent researcher"-style line, or a postal/e-mail contact — **JYH's call, and a lane question, not a formatting one**. Cambridge also requires an author e-mail through the submission form regardless. |
| G4 | **The 350–500 word Overview** (separate from the abstract) | **MISSING** | Pi requires *both*. Current abstract = 315 words (`main.tex:39-75`), which reads as the "short and self-contained" abstract. The overview must cover: general context (pointing to external papers as required); how the present paper fits that context; what the main new results are. Raw material exists at `main.tex:82-129` (§1 intro, four movements) — but the overview is author-voice prose and is **JYH's to write**. |
| G5 | **The leanchecker claim at `main.tex:156-159`** | **NEEDS-DECISION — the paper asserts something not yet true** | The sentence promises "before submission **every declaration** is replayed through `leanchecker`". The only replay on record is `docs/reports/lean4checker-local-1.md` (2026-07-21 18:49–19:18 PDT): "replayed **259 / 259** salt-authored content modules across all seven target tracks and accepted every declaration (**0 failures**)" (`:11`); table total `259 / 259 PASS, 0 FAIL / 1040 s` (`:125`). Three facts make the claim currently unsatisfied: (a) **259 is modules, not declarations** (`:80`); (b) the scope was **7 tracks** — HB 33, Fulcrum 5, Parity 2, MR 45, TwinBar 27, Chen 146, Keller 1 (`:117-125`) — while the corpus now has **23** tracks carrying `#audit_axioms` (BV, BrunLower, Entropy, ExpSum, Goldbach, HardyLittlewood, Mertens, SW, Tactic, Vk, Vmvt, Weil were **not** replayed); (c) the corpus has grown 66% in lines since. The pre-arXiv re-replay is already an owed item on the record: `docs/exploration/paper-diffs-0724.md:5`, `docs/exploration/council-0727.md:94-96`, `docs/exploration/roadmap.md:4` ("Review revisions → lean4checker ceremony → the generated appendix"), `docs/reports/dichotomy-day-report.md:81` ("lean4checker ceremony + release appendix | release | pre-submission"). Cloud replay attempts never reached Step 5 (`docs/reports/cloud-trial-night-2.md:121`, `cloud-trial-night-4.md:170-172`). **Decision: re-run at full scope before submission, or restate the sentence to match what was done.** |
| G6 | **Stale corpus statistics** | **MISSING (refresh)** | `main.tex:71-73` and `:135-137`: 324,724 lines → **537,908**; 751 files → **1,049**; 1,034 commits → **1,735**; ≈9,400 jobs → 9,465 last measured (`docs/exploration/pilot.md:13367`). The ledger's "256" is still the correct **highest numbered** catch (`docs/blueprints/flags.md:11664`) but 10 further catches were banked unnumbered after 2026-07-20 (`flags.md:11676–11818`) — so "256 numbered entries" is exact and "256 catches" is an undercount by ten. |
| G7 | **`\date{July 19, 2026}`** (`main.tex:35`) | **MISSING (refresh)** | Trivial; but it is the paper's only visible date and it precedes the PDF build (7/24) and the current corpus state. |

### 3.2 Compliance items that need a decision, not a fix

| # | Requirement | Status | Facts |
|---|---|---|---|
| G8 | **AI declaration adequacy under the Cambridge policy** | **PRESENT, but NEEDS-DECISION on framing** | Against the four principles: (1) *declared and clearly explained* — satisfied at four sites: abstract `main.tex:43-47`, `\thanks` `:32-34`, acknowledgments `:726-731`, and a full methodology section §10 `sec:method` `:634-689`. This is materially **more** explanation than the policy demands. (2) *AI may not be listed as an author* — satisfied: `\author{Jason Hickey}` (`:31`) is the sole author; Claude appears only in `\thanks` and acknowledgments. (3) *plagiarism policy* — no third-party text is presented as the authors'; the corpus's sources are cited. (4) *accountability* — satisfied verbatim at `main.tex:730-731`: "The author directed and ratified every design decision and bears sole responsibility for the claims." **The decision:** the abstract says the mathematics "is joint work of the author and Claude" (`main.tex:44-46`) and the `\thanks` says the commit ledger records that "every commit is co-authored" (`:33-34`). Cambridge bars AI from the *author byline*, which the paper respects — but an editor reading "joint work" and "co-authored" may read a de-facto co-authorship claim. JYH may want to decide, in advance and in his own words, (a) whether that framing stands as-is, and (b) whether a single explicitly-labelled declaration paragraph (an "AI use" statement) is added so the disclosure is findable in one place rather than distributed across four. **No wording is proposed here.** |
| G9 | **Conflicts of interest** | **NEEDS-DECISION (cover letter)** | The submission gate requires confirming "I and my co-authors do not have any conflicts of interest, or any such conflicts have been declared in the covering letter" (cup.msp.org step 0). Pi's IFC: conflicts "may include, but are not limited to, financial, professional, contractual or personal relationships", and the example wording template is "Author A is employed at company B". Facts in play: JYH is employed by an AI-lab-adjacent employer (portfolio `CLAUDE.md`, employer lane), and the paper's central methodological claim concerns the use of a commercial AI product (Anthropic's Claude). The paper already carries a no-employer-resources / no-endorsement statement at `main.tex:722-731`. **Decision: whether employment, and/or the use of a commercial AI vendor's product as the method under study, is declared in the covering letter, and in what terms.** |
| G10 | **APC — £1,960 / $2,740** | **NEEDS-DECISION** | Step-0 consent item 6 requires consenting to pay the APC on acceptance "unless one of the following applies". Relevant facts: no funder exists for this work (the paper states it was done "on personal time and personal equipment", `main.tex:722-723`); Pi "grants waivers on a discretionary basis, for authors who are not covered by one of the above funding routes"; the 2020 IFC states "No author will be expected to pay out of their own pocket"; and acceptance "will rest solely with the Editor, and without reference to the funding situation of the authors". A no-affiliation or personal-capacity submission is the case the discretionary waiver exists for. **Decision: request the waiver at submission, route through an institutional agreement if the affiliation decision (G3) creates one, or self-fund.** |
| G11 | **Licence: CC-BY default** | **NEEDS-DECISION** | "Authors … will hold the copyright of their published paper and articles will be published under a creative commons attribution license (CC-BY). The default licence is CC-BY … but others are available on request: CC-BY-NC-SA, CC-BY-NC-ND." Interaction to check: the repo is Apache-2.0 licensed (`LICENSE`, 11,358 B) and currently **private** (`origin https://github.com/jyh/salt.git`); CC-BY on the paper is independent of the code licence, but any artifact bundle deposited as supplementary material inherits whatever licence is declared for it. |
| G12 | **Prior-publication confirmation** | **PRESENT (no obstacle)** | Step-0 item 4 requires "this article has not been submitted or published elsewhere". arXiv posting is explicitly carved out: "sharing your preprint anywhere else shall not be viewed as prior publication" (Cambridge preprint policy). The `main.tex:5` route (arXiv → Pi) is therefore compliant. |

### 3.3 Encouraged-but-absent (referee-facing, high value here)

| # | Item | Status | Facts for the fix |
|---|---|---|---|
| G13 | **Data / code availability statement + a citable artifact** | **MISSING** | Pi: "We encourage the use of Data Availability Statements to describe whether the materials that underpin research findings have been made available to readers, and if so, where", with "a dedicated repository" having "permanent identifiers and robust preservation policies". Current state: repo is **private** (`git remote -v` → `https://github.com/jyh/salt.git`), the paper cites "the repository" ~9× without naming it, and the public gate is a portfolio-level rule ("Private now; public later behind a hard gate (history purge + the SaltBench wave boundary)", portfolio `CLAUDE.md`). Repo facts a statement would consume: **537,908 lines** of Lean 4 in **1,049** files under `Salt/`; **16,542** declarations (theorem 9,828 / lemma 4,752 / def 1,835 / instance 74 / structure 37 / abbrev 14 / class 2); **23** `All.lean` aggregate files carrying **127** `#audit_axioms` invocations over **~5,515** audited names; **zero** `sorry` and **zero** `native_decide` in tactic position; **Apache-2.0**; toolchain `leanprover/lean4:v4.32.0-rc1`; mathlib pinned at rev `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` (inputRev `v4.32.0-rc1`), `lake-manifest.json`. **This is the single biggest structural gap**: a referee cannot check a private repository, and the paper's entire epistemic argument (`main.tex:132-184`) is that the corpus is checkable. See §4. |
| G14 | **Appendix A is a placeholder** | **PRESENT but INCOMPLETE** | `main.tex:740` `% At release: generated from the All.lean audit blocks`; `:764` "Full index generated at release"; `:742` "[v0.1: headline rows only]" — 12 rows, all axiom cells reading "the three". The generator does not exist as a script; the source of truth is the 127 `#audit_axioms` blocks in the 23 `Salt/*/All.lean` files. Also promised at `main.tex:180-182`: "Appendix~\ref{app:index} renders every headline statement **in Lean and in prose side by side**" — the side-by-side renderings are not in the file. |
| G15 | **Funding statement** | **NEEDS-DECISION** | Pi: "Please identify all funding sources (by name and contract number, as appropriate)" under Acknowledgements. If there is no funding, the fact that there is none is what a reader looks for; `main.tex:722-723` states personal time and personal equipment but never uses the word "funding". |
| G16 | **Reference-style conformance** | **NEEDS-CHECK (minor)** | Pi wants alphabetical-by-first-author-surname numbering, numeric citation, MR-abbreviated journal titles, and no uncited or unsubmitted works in the list. `main.tex:767-791`: the 10 entries are **not** in alphabetical order (Heath-Brown, Chen, Littlewood, Tao, Matomäki–Radziwiłł, MRT, Maynard, Hales, mathlib, Hickey). Entry `\bibitem{companion}` (`:790`) is "J. Hickey, *The Salt method*, in preparation" — Pi's NB is explicit: papers "that have not been at least submitted for review, should be cited as eg. 'T. Smith, unpublished observations' and **must not appear in the reference list**". `\bibitem{Littlewood1922}` (`:773-775`) has no page range. |
| G17 | **Anonymity** | **N/A** | Pi/FoM does not operate double-blind review; no anonymized manuscript is required. Nothing in the author instructions requests one. |
| G18 | **LaTeX class** | **PRESENT (compliant)** | `amsart` at submission is fine — the FoM template is offered, and source is only demanded on acceptance ("On acceptance of a paper, authors should forward … the LATEX source code including … all author-defined macro and style files"). The two custom macros `\leanname` / `\leaninline` (`main.tex:20-21`) are author-defined style and must ship with the source at that point. |

---

## 4. THE VERIFICATION APPENDIX — spec (factual outline, not prose)

Purpose: give a referee a bounded, executable procedure that establishes
what the paper claims about its own corpus, without reading 537,908 lines.
The paper today asserts the trust surface in §2 (`main.tex:132-184`) but
gives no procedure. This is the outline of the missing appendix; **JYH
writes the words**.

**A. Artifact identity (prerequisite — see G13)**
- Repository URL, commit SHA, and licence (Apache-2.0) of the exact state
  the paper describes.
- An archival snapshot with a permanent identifier (Pi's transparency page
  asks for "permanent identifiers and robust preservation policies").
- Statement of what is and is not in the artifact.

**B. Toolchain pin**
- `lean-toolchain` = `leanprover/lean4:v4.32.0-rc1`.
- `lake-manifest.json` version 1.2.0; mathlib rev
  `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`, inputRev `v4.32.0-rc1`;
  batteries `954dbc98`, aesop `b5b9e2bb`, Qq `7a62bd13`, proofwidgets
  `e6518a67`, plausible `f3f26cc7`, importGraph `41f407a8`, LeanSearchClient
  `c5d5b8fe`, Cli `406ebb8c`.
- `lakefile.toml`: package `salt` v0.1.0, defaultTargets `["Salt"]`;
  leanOptions `pp.unicode.fun=true`, `relaxedAutoImplicit=false`,
  `weak.linter.mathlibStandardSet=true`, `maxSynthPendingDepth=3`.

**C. Build**
- `lake exe cache get` then `lake build`.
- Expected job count: **9,465** at last measurement
  (`docs/exploration/pilot.md:13367`); 9,351 at the replay ceremony
  (`docs/reports/lean4checker-local-1.md:36`).
- Expected wall-clock and hardware envelope: state it; the 7/21 replay took
  1,040 s for 259 modules (`lean4checker-local-1.md:125`), and a cold corpus
  needs >4 h on a hosted runner (`.github/workflows/seed_cache.yml`, a
  235-minute incremental seeder).
- CI facts, if cited: `.github/workflows/lean_action_ci.yml` runs
  `leanprover/lean-action@v1` with `use-mathlib-cache: true`, then
  `python3 scripts/blueprint_lint.py`, then `docgen-action@v1`.
  `.github/workflows/ci.yml` is the explicit-step equivalent with its push
  trigger deliberately disabled (PR + `workflow_dispatch` only).

**D. Axiom audit — the mechanism, stated as a mechanism**
- `#audit_axioms` is a **build-time gate**, not a print: defined at
  `Salt/Tactic/AuditAxioms.lean:81`
  (`elab (name := auditAxiomsCmd) "#audit_axioms" ids:ident+ : command => do`),
  blueprint node T5 (`docs/blueprints/tactics.md:101`). It **fails
  elaboration** if any listed declaration's transitive axiom closure exceeds
  `[propext, Classical.choice, Quot.sound]`. Consequence a referee can use:
  *the audit is not a claim in the paper, it is a build failure if false* —
  `lake build` succeeding is the audit passing.
- Coverage today: **23** `Salt/<Track>/All.lean` files, **127** invocations,
  **~5,515** audited names. Largest: `Salt/MR/All.lean` (99 blocks, ~3,436
  names), `Salt/Chen/All.lean` (712), `Salt/SW/All.lean` (333),
  `Salt/Goldbach/All.lean` (226), `Salt/Entropy/All.lean` (190). There is no
  single repo-wide `All.lean`; `Salt.lean` is the root import target.
- Per-statement spot check for a referee: `#print axioms <name>` after
  importing the module (12 such uses already exist in-tree).
- Optional external cross-check that requires no salt code:
  `leanprover-community/axiom-audit` — "fail CI if any declaration in your
  library transitively depends on an axiom outside an allowlist", default
  allowlist `propext, Classical.choice, Quot.sound`, invoked
  `lake build && lake exe axiom-audit`, and it detects `sorryAx`,
  `native_decide` (`Lean.ofReduceBool`), and custom axioms by inspecting the
  kernel environment rather than source text.
  <https://github.com/leanprover-community/axiom-audit>

**E. Independent kernel replay**
- Naming fact to get right: the standalone `lean4checker` repo is
  **deprecated**; the tool was merged into Lean 4 itself (v4.28.0+) and ships
  as `leanchecker`, invoked `lake env leanchecker`.
  <https://github.com/leanprover/lean4checker>
- Semantics: `lake exe lean4checker <module>` "will replay the environment in
  `<module>`, starting from the environment provided by its imports"; with
  no argument it "run[s] … in parallel on every `.olean` file on the search
  path"; `--fresh <module>` replays "all the constants (both imported and
  defined in that file) into a fresh environment". (same README)
- What it does and does not buy, per the Lean reference
  (<https://lean-lang.org/doc/reference/latest/ValidatingProofs/>): it
  "[r]eplays proofs from `.olean` files through the kernel; detects bugs in
  Lean's core kernel handling and meta-programs bypassing state"; the TCB
  remains "Lean's kernel implementation" and it "assumes `.olean` format
  validity" — it "[c]annot validate the `.olean` file format itself". This
  matches the paper's own hedge at `main.tex:158-160` ("checker and kernel
  share an implementation") and that hedge should be kept.
- The stronger option, if JYH wants the strongest available referee story:
  the Lean FRO's **comparator** (<https://github.com/leanprover/comparator>),
  described in the Lean reference as the gold standard — builds in a
  sandbox, validates the exported proof format outside the sandbox, replays
  with the Lean kernel **and/or external checkers (e.g. `nanoda`)**, and
  ensures the proved statements match a trusted challenge statement. Its
  TCB is sandbox security, the statement, and the external checkers. This is
  the only route that removes the Lean kernel implementation from the sole
  trust position.
- Record of what has actually been run:
  `docs/reports/lean4checker-local-1.md`, 2026-07-21, built-in `leanchecker`
  from `v4.32.0-rc1`, kernel build
  `b4812ae53eea93439ad5dce5a5c26591c31cb697`; **259/259 modules, 0
  failures, 1,040 s**, over 7 tracks (HB 33, Fulcrum 5, Parity 2, MR 45,
  TwinBar 27, Chen 146, Keller 1). `.All` manifests were excluded as
  0-declaration aggregators (`:72-77`). **No CI job and no script invokes
  leanchecker** — nothing in `.github/workflows/`, no Makefile, nothing in
  `scripts/`. It was a one-off manual ceremony. (G5.)

**F. The TCB statement — the enumerable list**
1. The Lean 4 kernel (v4.32.0-rc1) — *not* removed by a leanchecker replay,
   since checker and kernel share an implementation; removed only by a
   comparator run with external checkers.
2. The three axioms `propext, Classical.choice, Quot.sound`, and nothing
   else — enforced at build time by `#audit_axioms`, not asserted.
3. mathlib at the pinned rev, as a body of *statements* the definitions
   bottom out in (`Nat.Prime`, `DirichletCharacter`, `LFunction` —
   `main.tex:168-170`).
4. The `.olean` format and the build cache — excluded by a fresh-environment
   replay, not by the ordinary build.
5. **Not** in the TCB: tactics, elaborator, `native_decide` (forbidden; the
   repo `README.md` "Trust policy" section states this independently of the
   paper). Toolchain fact worth checking before writing: on Lean ≥ 4.29 a
   native-evaluated proof no longer surfaces as `Lean.trustCompiler` but as
   dedicated per-computation axioms — so the paper's "a fourth axiom" phrase
   at `main.tex:153-154` should be checked against v4.32 behaviour before it
   is restated.
   <https://lean-lang.org/doc/reference/latest/ValidatingProofs/>
6. The irreducible one: the statement↔prose translation (§2.2 of the paper,
   `main.tex:165-184`) — reduced to Appendix A, which must therefore
   actually be complete (G14).

**G. The finite check a referee can perform in an afternoon**
- Read Appendix A's ~12 rows (or the full generated index): statement,
  declaration, axiom column.
- For each, open the cited `file:line` and read the Lean statement against
  the prose statement.
- Run `lake build` (the audit gates fire) and one `leanchecker` pass.
- Everything else is delegated to the kernel.

---

## 5. THE COVER-LETTER FACT SHEET

**Facts for JYH's phrasing.** Bullets only — nothing below is drafted
sentences, and none of it should be pasted. Every item carries its source so
JYH can check it before using it.

### 5.1 What the paper proves

- A single hypothesis, the **fulcrum** (`FulcrumQualityMin C*`), defined at
  `Salt/Fulcrum/Basic.lean:61`; `C* = max(C^(1), 2/c_0)` with
  `c_0 = 1/126848`, the `2/c_0` arm equal to **253696**, kernel-certified at
  that numeral (`Salt/Fulcrum/CZeroNumeral.lean:387, :427`).
- **The zero's reality is derived, not assumed** —
  `Salt.Fulcrum.fulcrum_zero_real`, `Salt/Fulcrum/Basic.lean:93`.
- **The dichotomy** — unconditionally, ¬fulcrum ⟹ `NoSiegelZeros`
  (`Salt/Fulcrum/Dichotomy.lean:82`); with the named engine implication,
  TwinPrimeConjecture ∨ NoSiegelZeros (`Salt/Fulcrum/Dichotomy.lean:102`).
  The paper makes **no unconditional twin-prime claim** (`main.tex:129`) and
  tables every conditional with its exact residual
  (Table 1, `main.tex:703-717`).
- **Four unconditional banners**: Littlewood-strength zero-free region for ζ
  (`Salt/Vk/Littlewood.lean:409`); the θ = 3/4 power-saving region
  (`Salt/Vk/GrowthPow.lean:1044`); Deuring–Heilbronn repulsion in ordered
  two-zero contract form with every constant explicit, b = 680, k = 14
  (`Salt/SW/TBalR8.lean:1752`); the Vinogradov mean value theorem
  (`Salt/Vmvt/Summit2.lean:151`).
- **The keystone, unconditional** — the master estimate
  `Salt/HB/L2cMasterUncond.lean:85`, the site of Heath-Brown 1983's Lemma 2,
  proved on an exact identity rather than a τ-crude majorant.
- **The exchange-rate wall** — neutrality over arbitrary real sign functions
  (`Salt/HB/SignChain.lean:39, :511`; `Salt/HB/SignRate.lean:53`), with the
  Liouville function as the exact fixed point; falsifiable as stated
  (`main.tex:477-480`).
- **The parity gap as an object** — `Salt/Parity/Z.lean:102` (`Z`),
  `:670` (no true, twin-sufficient, parity-invariant completion exists),
  `:216` and `:687` (Z ⟺ TPC over the certified grade window), plus a
  ten-theorem census placing the corpus inside the parity-invariant cone
  (`Salt/Parity/Instances.lean`, exactly 10 declarations).
- **Log-Chowla, door-only** — the residual of Tao's two-point logarithmic
  Chowla reduced to one named MRT uniformity door
  (`Salt/Entropy/Chowla/SpineFinal.lean:981`).

### 5.2 Machine-checked status (the numbers, current as of 2026-07-31)

- **537,908 lines** of Lean 4 over mathlib, **1,049 files** under `Salt/`,
  **1,735 commits**, **16,542 declarations**.
- **Zero `sorry`. Zero `native_decide`. Zero home-rolled axioms.** Verified
  in tactic position, not by prose grep; the repo `README.md` "Trust policy"
  section states the same standard independently.
- Axiom base exactly `{propext, Classical.choice, Quot.sound}`, **enforced at
  build time** by `#audit_axioms` (`Salt/Tactic/AuditAxioms.lean:81`) across
  **127 invocations** over **~5,515 names** in **23** track manifests — a
  violation is a build failure, not an unchecked claim.
- Toolchain `leanprover/lean4:v4.32.0-rc1`; mathlib pinned at
  `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`.
- Independent kernel replay on record: **259/259 modules, 0 failures**,
  2026-07-21 (`docs/reports/lean4checker-local-1.md:11, :125`) — **scope
  caveat in G5; do not quote this as "every declaration" until the full-scope
  re-run exists.**
- Build: ~9,465 jobs (`docs/exploration/pilot.md:13367`).

### 5.3 Priority / independence / novelty facts (each is checkable)

- The paper's "first" claims are: first formalization of a
  Littlewood-strength (1922) zero-free region for ζ, and first
  power-saving zero-free region (θ = 3/4) in **any** proof assistant
  (`main.tex:208-212`), against a stated prior state of the art of
  "classical de la Vallée Poussin shape".
- The comparison set a referee will reach for, for JYH to check the claims
  against before asserting them in a letter: the PNT+ project
  (Kontorovich–Tao, Lean, PNT via Wiener–Ikehara, with an explicit error
  term as a stated future goal); Eberl–Loeffler, *Formalizing zeta and
  L-functions in Lean* (<https://arxiv.org/abs/2503.00959>); Eberl et al.'s
  Isabelle ζ/L-function development; Song–Yao's Isabelle PNT with the
  classical error term.
- Methodological novelty claimed: **demand-audited hypothesis minimization**
  as a mode of discovery (`main.tex:95-104`) — the fulcrum was extracted from
  a formal corpus, not transcribed from the literature.
- Process evidence: the public error ledger, **256 numbered catches against
  zero wrong proofs** (`docs/blueprints/flags.md:11664`), plus the claim that
  **no design error was first discovered by the kernel** (`main.tex:682-689`).
  Ten further catches were banked unnumbered after 2026-07-20 (`flags.md:11676–11818`).
- Precedent in this exact venue: Hales et al., *A formal proof of the Kepler
  conjecture*, Forum of Mathematics, Pi **5** (2017), e2 — already cited at
  `main.tex:786-787`.
- Companion in preparation: *The Salt Method* (`main.tex:790`) — note Pi's
  reference-list rule about not-yet-submitted work (G16).

### 5.4 The artifact

- Corpus: 537,908 lines / 1,049 files / 16,542 declarations, Apache-2.0
  (`LICENSE`).
- Current access state: **private** (`origin https://github.com/jyh/salt.git`).
  The public gate is a portfolio-level rule, not a technical one: "Private
  now; public later behind a hard gate (history purge + the SaltBench wave
  boundary)" (portfolio `CLAUDE.md`).
- Referee-facing check procedure: §4 above.
- Pi's posture: data/code availability is **encouraged, not required**
  (research-transparency page) — so this is a strength to offer, not a
  compliance box; but the paper's own epistemic argument
  (`main.tex:132-184`, `:180-184`) is unreadable to a referee who cannot see
  the corpus. **Timing decision for JYH: the public gate and the submission
  date interact.**

### 5.5 Disclosure facts the letter may need (see G8, G9)

- Sole author; AI not listed as an author (Cambridge requirement met).
- AI use declared at four sites in the manuscript and given a full
  methodology section (§10).
- Accountability sentence already present verbatim: "The author directed and
  ratified every design decision and bears sole responsibility for the
  claims" (`main.tex:730-731`).
- Personal capacity, personal time, personal equipment, no confidential or
  proprietary employer information, no employer or Anthropic endorsement
  (`main.tex:722-731`).
- The submission gate will require an affirmative AI-policy compliance tick
  and a conflicts-of-interest position (§2.2 items 3 and 5).

---

## Appendix — source index

**Forum of Mathematics, Pi**
- Author instructions hub — <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/author-instructions>
- Instructions for contributors — <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/instructions-contributors>
- Preparing your materials — <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/author-instructions/preparing-your-materials>
- Submitting your materials (ORCID, licence) — <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/author-instructions/submitting-your-materials>
- Fees and pricing (APC) — <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/author-instructions/fees-and-pricing>
- Open access options (waivers) — <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/journal-policies/open-access-options>
- Research transparency (data availability) — <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/journal-policies/research-transparency>
- Journal policies hub — <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/journal-policies>
- FAQs on Pi — <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/faqs-on-pi>
- Editorial board — <https://www.cambridge.org/core/journals/forum-of-mathematics-pi/information/about-this-journal/editorial-board>
- Submission system (step 0 consents) — <https://cup.msp.org/submit_new.php?jpath=pi>
- Pi Instructions-for-Contributors PDF (**stale on MSC year and APC**) — <https://www.cambridge.org/core/services/aop-file-manager/file/575a803676fa00070ad0e994>
- Sigma IFC PDF (same body text, cross-check) — <https://www.cambridge.org/core/services/aop-file-manager/file/5e6a337a24ab61e00a85aa87/FMS-ifc-Mar2020.pdf>

**Cambridge policy**
- AI contributions to research content (the four principles) — <https://www.cambridge.org/core/services/authors/publishing-ethics/research-publishing-ethics-guidelines-for-journals/authorship-and-contributorship#ai-contributions-to-research-content>
- AI ethics policy announcement, 14 Mar 2023 — <https://www.cambridge.org/news-and-insights/cambridge-launches-ai-research-ethics-policy>
- Preprint policy — <https://www.cambridge.org/core/services/open-research/preprint-policy>

**Toolchain / verification**
- lean4checker (deprecated → `leanchecker` in Lean ≥ 4.28) — <https://github.com/leanprover/lean4checker>
- Lean reference, "Validating a Lean Proof" (leanchecker, comparator, `#print axioms`, TCB) — <https://lean-lang.org/doc/reference/latest/ValidatingProofs/>
- comparator — <https://github.com/leanprover/comparator>
- axiom-audit — <https://github.com/leanprover-community/axiom-audit>
- MSC2020 — <https://msc2020.org/>

**Prior-art comparison set**
- Formalizing zeta and L-functions in Lean — <https://arxiv.org/abs/2503.00959>
