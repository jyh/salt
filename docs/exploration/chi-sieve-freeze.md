# CHI-SIEVE FINAL FREEZE (judge-final, 2026-07-19 ~20:20 PDT; wf_7a96d497; 7/7, ~966k; THE RESIDUAL PROVEN UNNECESSARY)

## CHOSEN

RESTRUCTURE (DES-B fused with REF-B Repair B): route BOTH sibling counts through the FROZEN engine hb_lemma8'_unconditional at the small-pp modulus (d2=w for ER, d1=v for class (c)) — chi-blind, landing in the master's J1 row; reprove the master conclusion VERBATIM from {hsq, hz100, hz8, hzx} only. hcount AND hLz0 both leave the hypothesis surface. Execution-complete, NO residual.

KILL ADJUDICATION (all four):
- ENGINE-VARIANT (DES-A hcore) — KILLED. (i) REF-A's free-q witness (packet q-freeness re-verified: ER_Tsw'_bound_of_count L2cERTsw.lean:380-388 carries no x-q coupling) makes hcount-as-frozen plausibly FALSE, forcing glue-site coupling and parking hcore = HB Lemma-5/Kloosterman + pretense-bridge content (flags :9974 circularity) indefinitely; (ii) the restructure delivers strictly more (unconditional master, zero residual) at comparable cost with no new C-tier instrument; (iii) honest-shape law: do not freeze an interface whose free-standing form is disbelieved. RETAINED: the free-q witness (amendment A2-i, #98 refuter pass) and the R2/R3 injection craft (reused in W1). REF-A's prose fix (L'/z0^2 -> Theta(L'/z0)) inherited-moot.
- IMPORT (char_LS/BDH/BV) — KILLED per MAP-A, re-affirmed: mean-square UPPER bounds over the primitive family; one term can consume the whole RHS, so no positive fixed-exceptional-chi extraction; SW range excludes the exceptional modulus; level-1/2 capped. No salt surface produces (L'/L)^2.
- GRAFT (Chen switching) — KILLED: character-free machinery; flags #61 explicitly does not transfer to the chi-weighted extraction.
- DES-B AS-WRITTEN (four-block, W0=z^{5/8}, fiberSieve) — SUPERSEDED by its own referee: the confirmed Zs=floor(z^{1/32}) 100-gate bust at z=100^16 (Zs=10), plus Repair B (verified this session): the engine has NO legality hypothesis and the repo Mertens is GENERAL-N, so W0:=z closes everything through the frozen engine, deleting the sole C-tier instrument (~1900 lines). Block L survives only as optional follow-on (A3).

INDEPENDENT RE-VERIFICATION (files opened this session): MixedCount.lean:609-616 (engine hyps = 100<=Z, 1<=Z, 0<d1, 0<d2, Odd both, Coprime — NO legality; flat +2Z^8); L2cMaster.lean:354-455 (ledger J1=2^30+4, J2=40345603+524288, junk<=24580, L2cCmain=2^31; master proof = linarith over NAMED public rows r1-r13 + 5 cover lemmas — sibling assembly mechanically mirrorable from a new file); L2cCore.lean:437-439 (mertens_vonMangoldt_div_le GENERAL-N: Sum_{Ioc 0 N} Lambda/d <= log N + log4+4 — Repair B's hinge TRUE; "2L'" was the N=2x+2 usage site), :159-163 (l2cWindow subset of Ioc x (2x) — matches baseSet PairInstance.lean:64-65, so both injections are subset inclusions via the identity map), :336-366 (Zz/Zf; Zf_ge_100 LANDED), :372/:396 (pretense counters); L2cERTsw.lean:67-147 (guard/IsERTsw/ER_Tsw'/sharp identity :106/peel :139), :327/:341 (z0>=3; 2z0^2<=e^{5z0}); L2cMop.lean:348-355/:504-506/:672-730/:1585-1674 (cPairSet; ELodd_cover'; hLz0's SOLE path cap->absorb->EL_minusPrimePair->EL_uncov_bound->_final; Tmirror C=17915904). Import topology verified: L2cMop imports L2cMaster; MixedCount imports PairSieveMixed; new leaf imports both, no cycle. ENEMY ARITHMETIC RE-DERIVED: 64*(9/4)=144; (log Zf)^-2 <= 3600/L'^2 (log Zf >= L'/60 needs log x >= ~46; have >= 221 at x >= 100^48); Mertens absorb log z + 5.39 <= (9/8)log z at log z >= 43.1 (have 73.68 at the z-floor); 144*3600*(9/8) = 583200; x2L' peel = 1166400 <= 2^21; J1 tally 2^30+4+2^22 < 2^31. All margins >= 40%.

## FREEZE

NODE HB-L2C-CHI-SIEVE — FINAL FREEZE. VERDICT: EXECUTION-COMPLETE, full C-ladder, NO residual, no class D. Deliverable: hb_l2c_master_unconditional — the landed master conclusion VERBATIM from {hsq : chi^2=1, hz100 : 100^16 <= z, hz8 : Lwin x^8 <= z, hzx : (z:R)^3 <= x}. Landed files untouched (iron rules 1/5); two NEW files, single-writer each.

W1 — Salt/HB/L2cEngineRoute.lean (imports Salt.HB.L2cMop + Salt.HB.MixedCount):
THE GENERAL LEMMA (one shape, both orientations; totient folded 64*(m/phi m)^2 <= 144 for odd pp):
theorem engineRoute_card_right {x m : N} (hZ : 100 <= Zf x) (hm : IsPrimePow m) (ho : Odd m) :
  (((baseSet x 1 m).filter (fun n => Nat.Coprime (primorial (Zf x)) (n / 1 * ((n + 2) / m)))).card : R)
    <= 144 * ((x : R) / m) / Real.log (Zf x) ^ 2 + 2 * (Zf x : R) ^ 8
theorem engineRoute_card_left — mirror (baseSet x m 1, sift (n/m)*((n+2)/1)). Both := hb_lemma8'_unconditional (hZ from Zf_ge_100; 1-side hyps trivial) + Nat.totient_prime_pow.
INSTANTIATION 1 (ER):
theorem erTsw_weightedCount_unconditional (chi) (hsq) {z x} (hz100) (hzx) :
  Sum_{n in (l2cWindow chi z x).filter (IsERTsw chi z)} Lambda (nMinus chi (n+2))
    <= 583200 * x * Real.log z / Lwin x ^ 2 + x ^ ((9:R)/10) * Lwin x
theorem ER_Tsw'_bound_unconditional (chi) (hsq) {z x} (hz100) (hzx) :
  ER_Tsw' chi z x <= 2^21 * (x / z0 z x) + x ^ ((9:R)/10) * Lwin x ^ 3
INSTANTIATION 2 (class (c)), NEW sharp cap (no exp factor; strictly sharper than cpair_summand_cap):
theorem cpair_summand_sharp (chi) (hsq) {z x n} (hn : n in cPairSet chi z x) :
  (LamTilde chi n - Lambda n) * LamTilde chi (n+2) <= 2 * Lambda (nMinus chi n) * Lwin x
theorem cPairSum_bound_unconditional (chi) (hsq) {z x} (hz100) (hzx) :
  cPairSum chi z x <= 2^21 * (x / z0 z x) + x ^ ((9:R)/10) * Lwin x ^ 3

W2 — Salt/HB/L2cMasterUncond.lean (imports W1):
theorem EL_uncov_bound_unconditional (chi) (hsq) {z x} (hz100) (hz8) (hzx) :
  L2cELuncov chi z x <= 2^26 * (x / Lwin x) * exp(5*z0) * PretenseSum chi (2x+2)
    + 2^21 * (x / z0 z x) + exp(2*z0) * (x/(z:R)^(1/8:R) + x^((9:R)/10)) * Lwin x ^ 3
theorem hb_l2c_master_unconditional (chi) (hsq) {z x} (hz100) (hz8) (hzx) :
  S2 chi (l2cWindow chi z x) - S1 (l2cWindow chi z x)
    <= L2cCmain * (x / z0 z x)
     + L2cCmain * (x / Real.log x) * exp(5*z0) * PretenseSum chi (2x+2)
     + L2cCmain * exp(2*z0) * (x/(z:R)^(1/8:R) + x^((9:R)/10)) * Lwin x ^ 3   [char-for-char = L2cMaster:377-382]

RUNG LADDER (~900 lines):
R1 [B ~160]: floors (60*log(Zf x) >= Lwin x under hz100+hzx; log z + log4+4 <= (9/8)log z at z >= 100^16; psi(z) <= z*Lwin crude) + both general-lemma orientations.
R2 [B/C ~200]: ER: fiber over w := nMinus(n+2) (sum_fiberwise pattern L2cERTsw:194); per-w fiber subset of engineRoute_card_right's set — n in Ioc x 2x (l2cWindow_subset), w | n+2, n prime > x > Zf, U = nPlus(n+2) prime > x/z >= x^{2/3} > Zf (hzx) => product Zf-rough; w odd/pp/<z (IsERTsw). Chain 144*x*(log Zf)^-2 * Sum Lambda(w)/w + 2Zf^8*psi(z) <= 583200*x*log z/L'^2 + x^{9/10}L'. Peel ER_Tsw'_le_weightedCount (:139) => 2^21 row.
R3 [B/C ~290]: (c): sharp cap via LamTilde_eq_single_of_card_one BOTH sides (n-side fChiSum(nPlus n)=2 by erTsw_fChiSum_eq_two + nPlus_sign mirror of :99-101 => LamTilde(n)=2*Lambda(v); (n+2)-side nPlus=1 => LamTilde(n+2)=fChiSum(1)*Lambda(n+2) <= L'). Split q' := base(n+2) vs Zf (complete dichotomy): q'>Zf => v-fiber into engineRoute_card_left (P=n/v prime > x/z > Zf; n+2 Zf-rough), same chain; q'<=Zf => n+2 proper-pp (e>=2 forced, q'^e > x >= 100^48), count <= 3*sqrt(2x+2) (ER_squarefull_junk pattern), row <= 8L'^2*sqrt(x) => junk. => 2^21 row.
R4 [B/C ~250, W2]: EL_uncov' = linarith{ELodd_cover' L2cMop:504, EL_TmirrorT2_bound :1589 (17915904<=2^26), L2cMid_bound, new (c) row}; master' = MIRROR of L2cMaster:383-454 (5 covers + r1-r11,r13 unchanged; r12 := ER_Tsw'_bound_unconditional; hEL_uncov := EL_uncov').

DEGENERATES FIRST (#245/#246/#252): w=1/v=1 (IsPrimePow kills); even w/v (n prime>2 => n+2 odd; (c) Odd-n conjunct); w,v>=z (conjunct kills); U=1 ((n+2)+ prime kills); U or P <= Zf IMPOSSIBLE (> x/z >= x^{2/3} > x^{1/48} >= Zf, hzx only, all corners); junk-w IN-scope (engine needs no junk guard; Mertens majorizes all pp <= z); p|q (window coprimality => exact n+*n- factorization); q'<=Zf ((c) only: squarefull row); empty families (0 <= RHS); z floor 100^16 (log z 73.68 >= 43.1 gate; Zf_ge_100 landed); z ceiling x^{1/3} (z0=3); PS=0 (new rows PS-free). COVERS: ER = single total injection, NO split; (c) = q'>Zf or q'<=Zf, complete by linear order.

ENEMY-REGIME RECORD (PS=Theta(1), z0 bounded [250,500]z0*, L'->inf): ER_Tsw' <= 2^21*x/z0 + o(x); cPairSum same — Theta(x)/z0*, INSIDE the pre-existing J1 grade the campaign already absorbs by z0*-tuning; conclusion VERBATIM => NET NEW BURDEN ZERO; J2 tally strictly drops (-524288). Asymptotic corners (#253): glue z0->inf (z >= L'^8): rows x/z0 decay — load-bearing that Mertens is at-z (log z + 5.39), NOT the 2L' usage site (REF-B catch honored); Zf is x-pinned, z-corner-safe. Section-7 (L2cERTsw:414-445) NOT contradicted: its impossibility was of the J2/PS-carrying target; its own d2:=w line (:425-427) concedes the J1-shaped total this freeze consumes.

CONSUMPTION CERTIFICATES: (1) master': two-swap proof-mirror of L2cMaster:383-454; J1 tally 2^30+4+2*2^21 = 2^30+4+2^22 < 2^31 = L2cCmain; J2 unchanged-minus-524288; junk +<=2 vs 24580; conclusion identical to landed :1668-1673 => zero downstream edits; glue later switches _final -> _unconditional, deleting hLz0/hcount plumbing (A4). (2) EL_uncov': composes ELodd_cover' + Tmirror + Mid + new (c) row; landed 2-row hEL_uncov hypothesis and _of_count/_final stay untouched as conditional siblings.

CONSTANT LEDGER: 144 (totient) x 3600 (log Zf >= L'/60) x 9/8 (Mertens absorb) = 583200; x2L' peel = 1166400 <= 2^21 per family (x1.8 headroom; even floor-constant 74 in R1 keeps 1774224 <= 2^21); junk coefficient 1 (2x^{1/2}L' and 8L'^2*sqrt(x) both << x^{9/10}L'-grade at x >= 100^48).

## BRIEFS

W1 BRIEF (subagent_type "HB-L2C-CHI-SIEVE-W1", model: "opus"; dispatch tonight): You are the SINGLE WRITER of Salt/HB/L2cEngineRoute.lean (NEW file). Touch ONLY this file; the rest of the repo is READ-ONLY. Prove sorry-free, in order: (R1) sixty_mul_log_Zf_ge_Lwin, mertens_absorb (log z + (Real.log 4 + 4) <= (9/8)*Real.log z at 100^16 <= z), psi_crude (Sum_{Ioc 0 z} Lambda <= z * Lwin x for (z:R)^3 <= x), engineRoute_card_right, engineRoute_card_left; (R2) erTsw_weightedCount_unconditional, ER_Tsw'_bound_unconditional; (R3) cpair_summand_sharp, cPairSum_bound_unconditional — statements exactly as in the freeze; they are FROZEN: if any is unprovable AS STATED, STOP after 3 serious attempts and flag (report the break in your text output with a drafted flags.md entry; you do NOT edit flags.md). Imports: Salt.HB.L2cMop and Salt.HB.MixedCount. ANCHORS (all verified in-repo by the panel): engine = hb_lemma8'_unconditional MixedCount.lean:609 (hyps: 100<=Z, 1<=Z, 0<d1, 0<d2, Odd both, Coprime — no others); Zf gate = Zf_ge_100 L2cCore.lean:353; Mertens = mertens_vonMangoldt_div_le L2cCore.lean:437 (GENERAL-N — do NOT use any 2L' instantiation); window = l2cWindow_subset L2cCore.lean:162 (subset of Ioc x (2x), matching baseSet PairInstance.lean:64 — your injections are subset inclusions via the identity map); fibration pattern = L2cERTsw.lean:194ff; peel = ER_Tsw'_le_weightedCount L2cERTsw.lean:139; sharp-identity pattern = erTsw_lamTilde_np2 L2cERTsw.lean:106 mirrored to the n-side with nPlus_sign as at :99-101; cPairSet = L2cMop.lean:348; squarefull pattern = ER_squarefull_junk (L2cER.lean). PRE-FLIGHT PINS (verify before proving; a mismatch is a flag, not a reshape): (a) LamTilde_eq_single_of_card_one signature + the value fChiSum chi 1 — if it is not 1, a factor-2 slack is authorized in YOUR two family rows only (2^21 -> 2^22), recorded in your module NOTES for W2; (b) the reusable proper-prime-power interval count in L2cER — else prove a fresh <= 3*sqrt(2x+2) B-lemma in your file; (c) Nat.totient_prime_pow for (m/phi m)^2 <= 9/4 on odd prime powers. LAWS: iron rule 1 — never alter any landed/frozen statement or blueprint statement; introduce NO conditional hypotheses (hcount/hcore must not appear); budget 3 serious attempts per rung then flag and stop (rule 4). VERIFY: lake build (clean, no new warnings) and #print axioms for EVERY new theorem via an uncommitted Scratch.lean — must be a subset of [propext, Classical.choice, Quot.sound]. NO-GIT LAW (#244, verbatim): you may not run ANY git command — no add, no commit, no push, no stash, no checkout, no branch; the orchestrator owns the working tree and all commits.

W2 BRIEF (subagent_type "HB-L2C-CHI-SIEVE-W2", model: "opus"; dispatch after W1 lands AND amendment A1 is ratified): You are the SINGLE WRITER of Salt/HB/L2cMasterUncond.lean (NEW file; imports Salt.HB.L2cEngineRoute). Targets, sorry-free: EL_uncov_bound_unconditional and hb_l2c_master_unconditional, statements exactly as in the freeze — the master conclusion must be CHARACTER-FOR-CHARACTER the landed conclusion of hb_l2c_master_of_count (L2cMaster.lean:377-382). Route: EL_uncov' = linarith over ELodd_cover' (L2cMop.lean:504-506) + EL_TmirrorT2_bound (:1589) + L2cMid_bound + cPairSum_bound_unconditional (W1). master' = MIRROR the landed proof L2cMaster.lean:383-454: the same 5 cover lemmas and rows r1-r11, r13; replace r12 with ER_Tsw'_bound_unconditional (W1) and hEL_uncov with your EL_uncov'; extend the linarith fact list with the new rows' nonnegativity facts; the J1 target absorbs 2^30+4+2^22 < 2^31. If linarith stalls, restructure to calc — never weaken the conclusion. Before landing, re-verify in-file the constants you consume (Tmirror 17915904; W1's actual family constants per its NOTES). Same laws as W1 verbatim: iron rule 1; 3-attempt budget then flag; lake build + #print axioms subset of [propext, Classical.choice, Quot.sound]; touch ONLY your file. NO-GIT LAW (#244, verbatim): you may not run ANY git command — no add, no commit, no push, no stash, no checkout, no branch; the orchestrator owns the working tree and all commits. Doc updates (guide card, frontier line, Mermaid status) are DRAFTED as a text block in your final output; the orchestrator lands them in the same commit per workflow step 5 — you do not edit the guide.

## SCOPE_DIFFS

Ledger vs the l2c-freeze + HOUSE AMENDMENTS 1-5 + catch #253:
1. NODE DELIVERABLE RESHAPED: was "TWO sibling (log z)^2 PS-counts (hcount + the class-(c) engine-regime count)" per #253(3); now "hb_l2c_master_unconditional, packet {hsq,hz100,hz8,hzx}, conclusion verbatim". The sibling counts are NOT proven and leave the critical path; hcount's free-standing truth is DOUBTED (REF-A free-q witness, refuter pass pending).
2. hLz0 (Amendment 5's gate) ELIMINATED from the master surface — catch #253's z0-bounded failure mode mooted; the z=x^{o(1)} glue workaround is no longer needed for the master.
3. ROW RE-ROUTING: ER_Tsw' and class (c) move J2 -> J1 inside the master (chi-blind engine counts); internal tallies: J2 -524288, J1 +2^22, junk +<=2. Conclusion shape unchanged => zero downstream diffs; enemy-regime campaign burden unchanged.
4. hb_l2c_master_of_count / hb_l2c_master_final / ER_Tsw'_bound_of_count remain LANDED and UNTOUCHED (conditional siblings). No landed or blueprint statement edited.
5. hEL_uncov's 2-row hypothesis shape NOT amended; superseded internally by the new 3-row sibling theorem (REF-B PENDING #2 resolved without statement surgery).
6. HB-ENGINE campaign (chi-weighted one-form sieve / Lemma-5 (L'/L)^2 extraction / Kloosterman sections 5-7): DE-COUPLED from Horn A's critical path; remains registered (commit e63133a) as research, needed only for a PS-carrying standalone ER bound (A3 option).
7. DES-B's four-block W0=z^{5/8} program + fiberSieve instrument DROPPED (about -1900 lines, -1 C-tier risk, and REF-B's Zs floor bust voided); REF-A's coupling packet (hzq/hq250/hq500) DROPPED — no statement requires x-q coupling anymore.
8. Amendments #245/#246 (junk-block and odd-guard repairs) UNTOUCHED and still load-bearing upstream of both families; the new route needs no junk guard of its own (upper-bound majorization).

## AMENDMENTS_PENDING

A1 (node re-scope; ratify BEFORE W2's guide-card commit): HB-L2C-CHI-SIEVE closed by RESTRUCTURE as frozen here; guide card / frontier / Mermaid text lands with W2's commit. W1's math is scope-independent (new theorems only) and does not wait.
A2 (flags.md entries — this panel cites, never edits; orchestrator writes after ratification): (i) hcount-as-frozen (q free) plausibly FALSE — REF-A's CRT/quadratic-reciprocity witness (chi(p)=-1 for all p <= 2x+2 except chi(U)=+1; one pair (U, 3U-2); PS = log U / U makes RHS < Lambda(3)); REQUIRES the catch-#98 parallel refuter pass before banking (two independent re-derivations of the arithmetic exist — REF-A and this panel — but the witness's existence step still gets the refuter); (ii) META-CATCH: an impossibility analysis is coupled to its TARGET SHAPE — the section-7 exhaustive d2-defeat was against the J2-only shape; worst-corner law extended: price candidates against the consumer's FULL row space; (iii) REF-B's two catches: the Zs=floor(z^{1/32}) 100-gate floor bust at z=100^16 (#245-family) and the Mertens lemma-vs-usage-site (2L') conflation (#253-family).
A3 (optional registration, NOT dispatched): block-L per-fiber twin sieve at Zz (PS-carrying standalone ER_Tsw' <= 2^19*(x/L')*e^{5z0}*PS) as a writeup-tier follow-on if statement economy ever wants the o(x)-in-the-enemy-regime family bound.
A4 (post-W2, surgical, Fable/JYH-tier, separate commit): doc-comment pointers on hb_l2c_master_final/_of_count to the unconditional sibling; glue call-site switch _final -> _unconditional (deletes the hLz0/hcount discharge plumbing).

## OPEN_RISKS

1. fChiSum chi 1 / LamTilde_eq_single_of_card_one exact form at nPlus=1 — W1 pre-flight pin (a); factor-2 slack authorized (J1 still fits at 2*2^22).
2. Proper-prime-power interval count reuse from L2cER — pin (b); worst case a fresh B-tier <= 3*sqrt(2x+2) lemma; junk headroom vast.
3. master' linarith mirror (26+ facts) brittleness — calc fallback authorized; all inputs are public named theorems (line-verified this session).
4. Totient plumbing ((m/phi m) <= 3/2 for odd pp) — B-tier, pin (c).
5. n/1 = n and exact-division simp friction in the engine's coprimality filter — cosmetic; the injections are identity-map subset inclusions (window and baseSet share Ioc x (2x), verified).
6. Floor-constant slack: if R1's 60 must relax under floor-vs-rpow friction, any constant <= 74 still lands the family rows under 2^21 (1774224 <= 2097152); actual constant recorded in W1 NOTES and re-checked by W2.
7. Process: W2's guide-card consummation gated on A1; executors are Opus (not Fable-gated per the workflow-gate memory); commits orchestrator-only, on the campaign branch, never main without approval; A2-i must not be banked before the #98 refuter pass.
8. Honest scope note: the chi-weighted one-form sieve itself (HB Lemma-5 extraction) remains unproven and OPEN as research — this freeze closes the CONSUMERS, not that lemma; anyone later citing "CHI-SIEVE closed" must mean the node, not the extraction (guide-card text must say so, per A1).

## SUMMARY_FOR_JYH

1. CHOSE RESTRUCTURE (DES-B + its referee's Repair B): both CHI-SIEVE siblings route through the FROZEN engine at the small-pp modulus — chi-blind, landing in the master's J1 row. Section-7's "impossible" was impossibility against the J2-only shape; its own d2:=w line concedes exactly the J1 total we consume.
2. DELIVERABLE: hb_l2c_master_unconditional — hcount AND hLz0 both gone; packet hsq/hz100/hz8/hzx; conclusion VERBATIM the landed shape, so zero downstream changes. Execution-complete, NO residual, all rungs <= C (~900 lines, 2 waves, 2 new files, landed files untouched).
3. Every load-bearing citation re-opened this session; enemy arithmetic re-derived: per-family row 1166400*x/z0 <= 2^21; J1 tally 2^30+4+2^22 < 2^31; J2 drops 524288; net new campaign burden at the fulcrum witness ZERO. Key hinges verified in-file: engine has no legality hypothesis; repo Mertens is general-N; window = baseSet's Ioc.
4. hcount itself stays unproven and is plausibly FALSE with q free (REF-A's witness — needs your #98 refuter pass before flags-banking); the HB-ENGINE/Kloosterman campaign leaves the critical path and stays registered as research.
5. dispatch_ready TRUE: W1 (L2cEngineRoute.lean, Opus, zero staging debt) tonight; W2 (master assembly + guide card) after W1 lands and you ratify the re-scope (A1); 4 amendments pending, listed.

dispatch_ready: True
