# The method-stats compilation — the quantitative record

*The project's quantitative ledger, assembled read-only from primary sources on
2026-07-15 (main @ `4bfe09d`, i.e. `e5165e2` + the token-data commit). Sources,
each cited inline: `git log` / `git log --numstat` on main; the catch taxonomy
(`docs/writeup/taxonomy.md`); the house-recorded token counts
(`docs/writeup/token-data.md`); the exploration ledger
(`docs/exploration/pilot.md`); the flags ledger (`docs/blueprints/flags.md`).
Where the commit convention is ambiguous the counting rule is stated and the
conservative choice taken. Numbers are reproducible from the git commands named.*

Repository life: **2026-07-06 23:17:39 → 2026-07-15 09:49:08 PDT ≈ 8.44 days**
(scaffold → the token-data commit). **468 commits** on main
(`git rev-list --count main`), of which **3 are merges** (Merge brun, Merge
maynard, MERGE Chen) → 465 non-merge. Final Lean corpus **187,397 lines across
358 files** (`find Salt -name '*.lean' -exec cat {} + | wc -l`), plus 16,062
lines of markdown under `docs/`. Cumulative lines added over history (churn-
inclusive) **206,015** against **1,824** deleted (`git log --numstat`).

---

## 1. Per-arc table

Arc assignment rule: each commit is bucketed by the house convention
`<track> <node>: <name>` in its subject (both `track ` and `track:` forms;
Maynard-node / fragility design commits filed under `docs:` are folded into
Maynard/Twelve). The **Chen arc is split at the razor** — commit `8f64dba`
"chen SW4: THE RAZOR IS POSITIVE — M = 0.012151" (2026-07-14 05:20:00): build =
Chen commits at/before the razor, endgame = after. Lines are numstat additions
per arc (churn-inclusive; corroborated by final per-directory LOC, see notes).
Catches are the canonical taxonomy numbering (#1–#78). Tokens exist only for the
endgame + exploration (token-data.md).

| Arc | Commits | Lines + | Span (PDT, first→last commit) | Catches (canonical #) | Output tokens |
|---|---|---|---|---|---|
| **Brun** | 25 | 3,769 | 07-06 23:37 → 07-07 15:35 (~16 h) | 0 counted¹ | not metered |
| **Maynard/Twelve** (maynard + explicit12) | 128 | 55,434 | 07-07 16:49 → 07-11 15:33 (~3.9 d) | 6 (#1–#6) | not metered |
| **LS / largesieve** | 14 | 4,040 | 07-11 11:05 → 07-11 14:48 (~3.7 h) | 0 counted¹ | not metered |
| **BV** | 24 | 7,624 | 07-11 16:01 → 07-12 01:30 (~9.5 h) | 7 (#7–#13) | not metered |
| **twinbar** | 8 | 2,034 | 07-12 02:12 → 07-12 04:18 (~2.1 h) | 0 counted¹ | not metered |
| **P0/P1** | 14 | 5,654 | 07-12 04:39 → 07-12 09:46 (~5.1 h) | 5 (#15–#19) | not metered |
| **SW** | 33 | 15,830 | 07-12 03:47 → 07-13 00:40 (~20.9 h) | 1 (#14) | not metered |
| **Chen-build** (→ razor) | 117 | 75,742 | 07-12 11:50 → 07-14 05:20 (~1.73 d) | 39 (#20–#58) | not metered |
| **Chen-endgame** (razor → headline) | 57 | 28,435 | 07-14 05:41 → 07-15 09:21² (~1.15 d) | 20 (#59–#78) | **≈13.0 M / 49 runs** |
| **Exploration** (pilot + sprint) | 11 | 1,973 | 07-14 17:44 → 07-15 09:22 (~15.6 h) | 0 (pilot lessons³) | **≈1.54 M / 9 runs** |
| *Infra / method-docs / merges* | 37 | 5,480 | 07-06 23:17 → 07-15 09:49 (spans) | — | — |
| **TOTAL** | **468** | **206,015** | 07-06 → 07-15 (8.44 d) | **78** | — |

¹ Brun, LS, twinbar carry **zero canonical catches** but each had real
pre-execution design amendments the ledger's running total deliberately excludes
(Brun's strict-vs-nonstrict statement amendment; largesieve's "unprovable 7N" and
"Field-only Gauss lemma"; the twinbar squeeze redesign). taxonomy.md
"Ledger inconsistencies" §1 states the canonical 78 is "a curated subset" and the
true first-five-rung design-catch count is higher. So "0 counted" ≠ "0 caught."

² The Chen-endgame arc's last commit is a post-headline docs cleanup
(`chen 58c`, 07-15 09:21); the proving core is razor → headline (below).

³ Exploration produced no catches by design — its ledger records **pilot
lessons** (naive-witness alarm, recon-before-freezing) rather than defect catches.

**Wall-clock arcs interleave — spans are not disjoint.** SW (07-12 03:47 →
07-13 00:40) ran concurrently with Chen-build (opened 07-12 11:50); Chen consumed
the SW gate, and the two tracks alternate commit-by-commit across 07-12/07-13.
twinbar and P0 overlap SW's opening; the Maynard/Twelve PNT seam (07-11 15:33)
postdates the LS window (11:05 → 14:48). Read the spans as overlapping windows,
not a partition of the 8.44 days.

**Node counts** are deliberately omitted from the table as a headline: the
subject-regex proxy over-counts (multi-node commits like "N1.2/N1.3/N1.4",
gate/recon/docs commits with no node label). Authoritative counts where the
ledger states them: **Brun 27/27 nodes** (`git log` "blueprint complete, 27/27",
Merge brun); **P0 13 dispatches** (P0 RUNG-COMPLETE body); **Chen-endgame 49
metered runs** (token-data.md; runs > nodes because gates and re-dispatches are
separate runs); **Chen keystone-1 / C1c family 14 nodes** (commit body).

---

## 2. The attempt-rate analysis

**Convention.** Commit bodies carry a `Model: … attempt N` line. It was adopted
**systematically only from the P0 rung onward** (2026-07-12). Of the 465
non-merge commits, **183 carry an attempt line; 285 do not** (all of Brun,
early Maynard, LS, BV, twinbar, and infra predate/omit it). The rate below is
therefore measured on the 183 that record it.

| | Commits with attempt line | attempt = 1 | attempt > 1 |
|---|---|---|---|
| **Overall (recorded)** | 183 | **178 (97.3%)** | 5 |
| Maynard (early) | 5 | 0 | **5** |
| P0/P1 | 10 | 10 | 0 |
| SW | 26 | 26 | 0 |
| Chen-build | 89 | 89 | 0 |
| Chen-endgame | 50 | 50 | 0 |
| Exploration | 3 | 3 | 0 |

**The five multi-attempt commits are ALL in the pre-convention Maynard arc**
(2026-07-08/09): `N3.3-sharp` (attempt 3), `N4.4-quant` (attempt 3),
`Lemma 5.3` (attempt 3), `Lemma 5.3 tail` (attempt 2), `Wave 5` (attempt 2).
**From P0 onward the record is uniform and complete: 178 of 178 committed
landings compiled on the executor's first attempt — zero committed retries**
(`git log --grep='attempt [2-9]'` returns only the two Maynard "attempt 3"
subjects).

**The honest caveat (state it wherever the 178/178 is quoted).** "attempt 1"
counts the executor's first *build success* after the design was frozen —
*including* re-frozen after a gate or STEP-0 catch. Failed pre-commit executor
attempts that tripped STOP-AND-FLAG are recorded in `flags.md`, not as
`attempt > 1` commits. So 178/178 measures **clean landings on the (possibly
amended) statement**, not the absence of design iteration. The design iteration
*is* the 78 catches — the two metrics are complementary, not redundant.

**Streaks** (all from commit bodies / subjects):
- **P0: "13 dispatches, 13 first-attempt landings, 0 floors"** (P0 RUNG-COMPLETE body) — the memory's "13/13 first-attempt."
- **Chen keystone-1: "the C1c family closes at 14 nodes, all first-attempt."**
- **SW S6a "first-attempt compile"; SW wave-2 "all four wave-2 nodes first-attempt."**
- **The post-H2-GATE run:** from `H2-GATE` (07-14 11:33) to the headline
  (07-15 06:49), all **45** subsequent Chen commits landed on the first attempt
  (0 committed retries); the ledger records a **"Six consecutive first-attempt
  FULLs. 67 catches, 0 wrong proofs"** streak inside this window.

---

## 3. The velocity record

**Commits per calendar day** (`git log --date=format-local:'%Y-%m-%d'`), total 468:

| Day | 07-06 | 07-07 | 07-08 | 07-09 | 07-10 | 07-11 | 07-12 | 07-13 | 07-14 | 07-15 |
|---|---|---|---|---|---|---|---|---|---|---|
| Commits | 3 | 40 | 22 | 37 | 44 | 60 | 80 | **88** | 65 | 29 |

Average **≈55 commits/day** over 8.44 days; **54.5/day** over the eight full
days (07-07 → 07-14); **peak 88 on 07-13** (the Chen keystone/SW day).

**The Chen-endgame day(s), in detail.** The razor→headline proving window is
**07-14 05:20 → 07-15 06:49 ≈ 25.5 hours**. In it:
- **57-commit Chen-endgame arc** (07-14 05:41 → 07-15, one post-headline docs commit); ~56 proving commits razor→headline.
- **20 catches raised and repaired — the entire #59–#78 block** (#59 GLU-BV at 07-14 05:55 → #78 FIN-LED-2 at 07-15 05:38). The cluster is #59–#74 on 07-14, #75/#77/#78 on 07-15. Per taxonomy.md, **all 20 were caught before any wrong proof; 0 kernel-discovered.**
- Keystones landed in-window: GBV2–5 (m-sub-blocking / transpose / √D cutoff), GLU-1/2 (the normalized package), **H-amendment 2 = the W-trick layer** (catch #65 repair), the PRICE-family (per-box pricing), fin4–fin8d (boundary), HCOUNT-3 (the count line), and `chen_headline`.

**The headline timeline** (reconstructed from commit timestamps):

| Moment | Commit | PDT | Elapsed from razor |
|---|---|---|---|
| **Razor positive** (M = 0.012151) | `8f64dba` chen SW4 | 07-14 05:20:00 | 0 |
| H-amendment 2 / W-trick design | `0daf76c` | 07-14 11:11 | +5.9 h |
| H2-GATE (start of the first-attempt run) | `c4a2a39` | 07-14 11:33 | +6.2 h |
| Count line closed (HCOUNT-3) | `f9bfe69` | 07-15 03:48 | +22.5 h |
| Last catch (#78) repaired | `aa2d608` | 07-15 05:38 | +24.3 h |
| **THE HEADLINE** `chen_headline` | `9306e04` | 07-15 06:49:44 | **+25.5 h** |
| MERGE the Chen arc | `0339268` | 07-15 06:53:28 | +25.6 h |

---

## 4. The economics section

All token figures are output tokens, house-recorded from task-completion
notifications, **endgame + exploration only** (token-data.md). Earlier arcs were
not metered.

**The Chen endgame** (token-data.md, 49 runs GBV3 → HCOUNT-3):
- **Total ≈ 13.0 M output tokens across 49 runs.**
- Per-run distribution: **median ≈ 270 k; max HCOUNT-3 = 661 k** (the count-line
  composition); **min FIN-A3b = 147 k** (mechanical restatements).
- **Cost per landed run ≈ 265 k** (13.0 M / 49).
- **Cost per endgame catch ≈ 650 k** (13.0 M / 20 catches, #59–#78). This is the
  *only* window where cost-per-catch and cost-per-landed-node are computable;
  the 58 earlier catches are unmetered.

**The Fable-inheritance window, priced separately.** By the 2026-07-14 routing
mistake, runs **GBV3 → GLU-2W-first (≈ 4.8 M, ~37% of the endgame total)** ran on
Fable pricing unintentionally before the account switch (token-data.md; the fix
and the user-ratified routing rule are in the ledger). The method paper's
economics must price this ~4.8 M slice at Fable rates and the remaining
~8.2 M at Opus rates.

**The exploration pilot + sprint** (token-data.md, 9 runs):
- **Total so far ≈ 1.54 M.** recon median ≈ 100 k; probe median ≈ 200 k.
- Per-run (ktok / outcome): PILOT-recon 138 · P-A 201 (theorem+threshold) ·
  P-C 183 (sharp constant+conditional no-go) · Q1-recon 102 · Q6a-recon 95 ·
  Q5a 243 (obstruction theorem + no-go + numerics) · Q3-recon 97 · Q4 136 ·
  TAXONOMY 348 (the 78-row dataset).
- Sprint per-question cost (pilot.md, tokens / tool-uses / wall): Q1-recon
  102 k / 30 / ~7 min; Q6a-recon 95 k / 29 / ~9 min; Q5a 243 k / 49 / ~36 min;
  Q3-recon 97 k / 23 / ~6 min; Q4 136 k / 30 / ~11 min. Pilot P-A ≈ 1 web check
  + ~5 build cycles + one de-risking scratch (pilot.md calibration).

**THE HONEST GAPS** (verbatim from token-data.md "Known gaps"):
> - Pre-endgame arcs (SW, BV, P0/P1, the Chen build phase to the razor):
>   token counts not retained; only node/commit/attempt data (git + flags)
>   survives. The method paper reports the endgame economics as measured
>   and the earlier arcs as commit-count proxies.
> - House-session (Fable) tokens: not separately metered; the session
>   transcript is the only record.
> - The 2026-07-14 Fable-inheritance window: GBV3 through GLU-2W-first
>   (~4.8 M of the above) ran on Fable pricing by mistake; the fix and the
>   user-ratified routing rule are in the ledger.

---

## 5. Headline-number candidates (with exact sources)

The numbers the papers will quote. Each is reproducible from the cited file or
git command.

1. **78 catches, 0 proofs on a wrong statement.** — taxonomy.md line 116
   ("Verified total: 78 catches, 0 proofs on wrong statements"); flags.md closes
   at "78 catches, 0 wrong proofs."
2. **0 kernel-discovered defects** — no catch was surfaced by a build/typecheck
   failure; 5 carry a machine-checked *counterexample* but each was surfaced by
   an executor/gate/STEP-0 first. — taxonomy.md "Discovery mechanism" (kernel 0%).
3. **Structural reuse for Chen-2/twin: 63% verbatim / 35% parametric-mirror /
   2% re-derive.** — `git log` commit `56bbbb0` "the structural reuse data
   (63/35/2)"; pilot.md Q1-recon (corpus denominator ≈ 125k lines).
4. **Final corpus 187,397 lines / 358 Lean files**, of which **32,529 (17%) are
   machine-generated numeric certificates** (CbarCert 21,189 + SuperPanels
   11,340). — `find Salt -name '*.lean' -exec cat {} + | wc -l`.
5. **206,015 cumulative lines added** (churn-inclusive) / 1,824 deleted. —
   `git log main --numstat`.
6. **468 commits over 8.44 days; ≈55/day, peak 88 (07-13).** — `git rev-list
   --count main`; `git log --date=format-local:'%Y-%m-%d'`.
7. **The Chen endgame: 20 catches (#59–#78) + Chen's theorem, razor → headline
   in 25.5 hours** (07-14 05:20 → 07-15 06:49:44). — commit timestamps `8f64dba`
   → `9306e04`.
8. **Endgame economics ≈ 13.0 M output tokens / 49 runs (median 270 k); ≈650 k
   tokens per catch.** — token-data.md.
9. **178/178 committed landings from P0 onward compiled on the first attempt;
   only 5 multi-attempt commits in all history, all in pre-convention Maynard.**
   — `git log --grep='attempt'`; §2 above.
10. **Brun 27/27 nodes; P0 rung 13/13 first-attempt dispatches; Chen keystone-1
    14/14 nodes first-attempt.** — commit bodies / Merge brun.
11. **Catch shape: interface-shaped 26 (33%), estimate/statement 33 (42%),
    design-local 18 (23%); integration phase 91% interface, build phase 60%
    local.** — taxonomy.md category + phase tables.
12. **twinbar impossibility rung: 8 commits, 2,034 lines, ~2.1 hours**
    (M₂ ≤ 2·log 2 < 2). — arc table above; the fastest full rung.

---

## Data-quality issues found

1. **The `attempt N` convention is partial.** Present in 183/465 non-merge
   commits; systematic only from P0 (07-12) onward. First-attempt rate is
   honest only for that window. **"attempt 1" = first build success on the
   (possibly re-frozen) statement, not "no design iteration"** — the design
   iteration is the 78 catches; do not conflate the two.
2. **Token data covers only the endgame (GBV3→) + exploration.** Cost-per-catch
   is computable for 20 of 78 catches; the rest are commit-count proxies only
   (token-data.md gaps, quoted verbatim in §4).
3. **The Fable-inheritance window (~4.8 M, ~37% of endgame tokens) is
   mispriced** at Fable rates by the 2026-07-14 routing mistake — must be priced
   separately.
4. **Corpus LOC 187,397 (measured now) vs Q1-recon's "≈125k" working
   denominator** (pilot.md). The gap is largely the ~32.5k certificate/panel
   lines plus comment/blank differences; Q1-recon's 125k methodology (likely
   structural-code-only) is unstated. Report 187,397 as the measured corpus and
   125k as the reuse-audit denominator, not interchangeably.
5. **Canonical 78 is a curated count.** taxonomy.md "Ledger inconsistencies":
   #1–#16 are not individually headered (reconstructed from tally lines);
   #54/#55/#76 lack dedicated tally lines; #79 never occurs; and design catches
   in Brun/LS/twinbar are excluded from the running total. The true count of
   pre-execution design catches in the first five rungs exceeds the canonical
   count attributed to them (0/6/0/7/0). Attribute per-arc catches as "canonical
   #" and note the exclusions.
6. **Node counts are a subject-regex proxy** (multi-node commits, gate/recon/docs
   commits without a node). Use the ledger's authoritative counts (Brun 27, P0
   13, endgame 49 runs, C1c 14) for any headline; the proxy is directional only.
7. **Arc wall-clock spans overlap** (SW ∥ Chen-build; twinbar/P0 ∥ SW; Twelve PNT
   seam past LS; exploration pilot ∥ Chen-endgame). Do not sum the spans into a
   sequential timeline.
8. **Commit total is 468** (`git rev-list --count main`), incl. 3 merges. An
   early transient `git log --oneline | wc -l` reading of 467 was superseded;
   468 is authoritative and matches the numstat header count.
9. **Chen arc split point.** Build/endgame is cut at the SW4 razor (07-14
   05:20). token-data's *metered* endgame starts slightly later (GBV3, 07-14
   06:49) — 4 commits (GLU-1, GLU-BV, WLOW, GBV2, incl. catches #59/#60) fall in
   the razor→GBV3 gap and are counted in the endgame arc but not in the 49
   metered runs. The arc's 57 commits ⊋ token-data's 49 runs.
