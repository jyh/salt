# WALL-3 + D4 RATIFICATION (judge-final, 2026-07-19 ~09:50 PT; wf_8308a21e; 7/7 agents, ~720k)

## RATIFIED

RULING — WALL-3: W1 RATIFIED, W2 RATIFIED, W3 RATIFIED (split per diff #3, masterGen comment-frozen). D4: DEFINE — Z RATIFIED with REF-Z repairs R-1/R-2 applied. Authoritative frozen text = DES-W.statements + DES-Z.definition/lemma_shapes as amended below; both refuter-certified line-exact, and judge spot-check re-verified this session (all GROUNDED): Transfer.lean:176/179/185/189-192; L2cCore.lean:54/57/68/76; TwistChain.lean:94/98-99; TransferFull.lean:183-185; chiRe locked to DirichletCharacter at Salt/TwinBar/TwistedSieve.lean:63 (dup Salt/SW/DHDetector.lean:78); Salt/Basic.lean:25-26; Salt.M5BigO.N5_3 (M5BigO.lean:295, namespace :25); mathlib Liouville.lean:27/31/37/40, VonMangoldt.lean:130 vs :133; Salt/Brun/All.lean:13 imports M5BigO while Salt/Brun.lean imports Mathlib only; no SignChain/SignLiouville/SignRate/L2cMaster/Salt.Parity files exist; all frozen names grep-clean; All.lean has no L2c line.

== W1 — Salt/HB/SignChain.lean [B, volume-flagged ~600-800 lines] ==
FROZEN VERBATIM = DES-W §W1 full Lean text (in the record; REF-W certificate: every cited line exact; hcop-erasure sound — the sole hcop consumer chiRe_eq_one_or_neg_one is replaced hypothesis-free by prime_pm). The sole hypothesis packet (replaces χ : DirichletCharacter ℂ q + hsq : χ^2 = 1; record ℱ = f²=1 everywhere, NO modulus, pass3_t3.md:29):
structure IsSignFunction (f : ℕ → ℝ) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ a b : ℕ, f (a * b) = f a * f b
  abs_le_one : ∀ n : ℕ, |f n| ≤ 1
  prime_pm : ∀ p : ℕ, p.Prime → f p = 1 ∨ f p = -1
Defs (12): fGenSum, LamTildeGen (KEEP Real.log ((n / d : ℕ) : ℝ), ℕ-division per TC:99), gGen, fGenArith = ζ * gGen f, nPlusGen/nMinusGen (open Classical), S2Gen, overshootExactGen, PretenseSumGen (TF:183-185 mirror), excPrimorialGen (q-part GONE), l2cWindowGen (q DROPPED). Theorems (24 + TCC:89-161 helper block, signatures verbatim per DES-W): fGen_pow; gGen_mult; fGenArith_mult; fGenArith_nonneg; LamTildeGen_eq_conv [packet-free]; vonMangoldt_le_LamTildeGen [1(b)]; eq_nPlusGen_mul_nMinusGen [hcop DROPPED]; coprime_nPlusGen_nMinusGen; fGenArith_eq_two_pow; fGenSum_n_eq_zero; LamTildeGen_eq_zero_of_two_le_card; LamTildeGen_eq_single_of_card_one; LamTildeGen_le_of_nMinus_one; LamTildeGen_sub_vonMangoldt_le [1(c), hcop DROPPED]; S1_le_S2Gen (S1 of TR:176 reused VERBATIM); S2Gen_sub_S1_eq [packet-free, LC:76 mirror]; four lamTildeGen_sub_eq_zero_* + lamTildeGen_sub_support_classification (LC:89-130 mirrors); l2cWindowGen_roughness [{z x} implicit — cosmetic deviation from LC:180, ratified as frozen]; omega_capGen; lamTildeGen_cap; sum_inv_plusprime_le_pretenseGen; chebyshev_chi_countGen. NOT re-typed: the χ-free KC1 layer (consumed as-is); the bypassed TR:60-71 overshoot trio + TF majorant chain (diff #1). Packet-free lemmas stay packet-free. Route: substitution table (chiRe_mul↦map_mul, chiRe_one↦map_one, chiRe_abs_le_one↦abs_le_one, chiRe_eq_one_or_neg_one↦prime_pm) + delete all hcop threads; re-grep every TCC line (±1 drift).

== W2 — Salt/HB/SignLiouville.lean [A/B; gate: W1 def-slice + LamTildeGen_eq_conv] ==
FROZEN (full):
noncomputable def lamR : ℕ → ℝ := fun n => ((ArithmeticFunction.liouville n : ℤ) : ℝ)
theorem lamR_prime {p : ℕ} (hp : p.Prime) : lamR p = -1
theorem isSignFunction_lamR : IsSignFunction lamR
lemma moebius_sq_mul_lamR (d : ℕ) : (μ d : ℝ) ^ 2 * lamR d = (μ d : ℝ)
lemma gGen_lamR_eq_moebius : gGen lamR = (μ : ArithmeticFunction ℝ)
theorem LamTildeGen_lamR_eq_vonMangoldt (n : ℕ) : LamTildeGen lamR n = Λ n
theorem S2Gen_lamR_eq_S1 (A : Finset ℕ) : S2Gen lamR A = S1 A
lemma overshootExactGen_lamR (n : ℕ) : overshootExactGen lamR n = 0
theorem PretenseSumGen_lamR_eq_zero (N : ℕ) : PretenseSumGen lamR N = 0
Route (mathlib lines verified): THE POLE = LamTildeGen_eq_conv + gGen_lamR_eq_moebius + moebius_mul_log_eq_vonMangoldt (VonMangoldt.lean:130; NOT :133 which is ∑μ(d)log d = −Λ); liouville_apply NEEDS n≠0 (:31); liouville_apply_mul :40 unconditional; μ²λ=μ by Squarefree split (Moebius.lean:60/64).

== W3 — Salt/HB/SignRate.lean [neutrality_rate: B given W1; masterGen: FROZEN TARGET, D, NO ATTEMPT] ==
FROZEN (full):
noncomputable def EngineBound (Cmain : ℝ) (z x : ℕ) (P : ℝ) : ℝ :=
  Cmain * ((x : ℝ) / z0 z x)
    + Cmain * ((x : ℝ) / Real.log x) * Real.exp (5 * z0 z x) * P
    + Cmain * Real.exp (2 * z0 z x)
        * ((x : ℝ) / (z : ℝ) ^ ((1 : ℝ) / 8) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3
theorem neutrality_rate (f : ℕ → ℝ) (hf : IsSignFunction f) (z x : ℕ) (Cmain : ℝ)
    (hbudget : ∑ n ∈ l2cWindowGen f z x, overshootExactGen f n
        ≤ EngineBound Cmain z x (PretenseSumGen f (2 * x + 2))) :
    0 ≤ S2Gen f (l2cWindowGen f z x) - S1 (l2cWindowGen f z x) ∧
      S2Gen f (l2cWindowGen f z x) - S1 (l2cWindowGen f z x)
        ≤ EngineBound Cmain z x (PretenseSumGen f (2 * x + 2))
AMENDMENT J2 (mandatory, REF-W repair 2): neutrality_rate's docstring states its unconditional content = S1_le_S2Gen; the rate content is hbudget-conditional pending masterGen (flags-wording guard, l2c-freeze.md:146). AMENDMENT J1: hb_l2c_masterGen (∃ Cmain, 0 < Cmain ∧ ∀ f, IsSignFunction f → ∀ z x, 100^16 ≤ z → Lwin x^8 ≤ z → z³ ≤ x → S2Gen−S1 ≤ EngineBound Cmain z x (PretenseSumGen f (2x+2))) is COMMENT-FROZEN in SignRate.lean as a docstring block, NOT a Lean declaration (a sorried decl = warning = build-discipline breach); authoritative text = DES-W §W3 verbatim. AMENDMENT J3 (recorded ruling, REF-W repair 1): ∃Cmain OUTSIDE ∀f∀z∀x is the ratified reading of the freeze's ABSOLUTE; moving ∃ inside the context is Cmain-monotonically trivial = vacuous = FORBIDDEN. Catch-#98 refuter pass on the EngineBound transcription: RUN by REF-W term-by-term vs l2c-freeze.md:27-33 — clean. N pinned to 2x+2 throughout; horn B (o(1)/staircase/HL) has NO Lean statement — W4 prose only (W5 law).

== D4 — RULING: DEFINE ==
FROZEN Salt/Parity/Z.lean = DES-Z.definition text VERBATIM (twinRho, typeISum, typeIError, Completion, ParityInv, twinMass, TwinSufficient, oneWeight, twinFree, Z, ParityBarrier — the last lands as a def, stated never assumed) with amendments: J4 (R-1) imports = Mathlib + Salt.Basic + Salt.Brun.M5BigO ONLY (minimal; verified necessary); keystone cited qualified Salt.M5BigO.N5_3; MODULE INVARIANT: Z.lean never imports Salt.HB/Salt.TwinBar — oracle-cleanliness checkable by import list alone; L0 instantiations move to a separate Salt/Parity/Instances.lean. J5 (R-2) Z's docstring carries the grade guard: demand-force is conditional on oneWeight ∈ Completion θ A₀ (certified window θ∈(0,1/2), A₀≥0; outside it Z trivializes via E := (· = oneWeight)); plus commissioned lemma Z_trivial_of_not_completion : ¬ Completion θ A₀ oneWeight → Z θ A₀ [A]. J6: L3's h0/h1 hypotheses KEPT as frozen (no strengthening at Lean time). **[SPENT 2026-08-11 — Captain's ruling (a) at council.** The guard was a FLAGS-WORDING guard aimed at this desk, and its purpose is discharged: writing `Salt/Certs/ParityGap.lean` proved the unused binders were `h1` and `ht` — **not** `h0`, which the proof does use via `twinFree_mem`. Both dropped; the name is kept because strengthening preserves a name's meaning.**] Commissioned nodes (shapes verbatim per DES-Z.lemma_shapes): L0 parityInv_of_closed [A] + instances [A, Instances.lean]; L1 oneWeight_mem θ<1/2 [B]; L2 twinFree_mem [B/C KEYSTONE, consumes Salt.M5BigO.N5_3] + twinFree_twinMass [A]; L3 sufficient_true_not_parityInv [B — THE GAP]; L4 twinMass_oneWeight_unbounded_iff [A/B]; L5 Z_implies_TPC [B]; L6 TPC_implies_Z [A]. NOT commissioned: τ²-density θ<1 extension [C, flagged follow-on]; ParityBarrier proof [D].

## BRIEFS

COMMON DOCTRINE BLOCK (every brief carries verbatim): model: "opus" (executor-model law); subagent_type = node name (agent-naming law); NO GIT — catch #244: no add/commit/push/branch/checkout, the conductor commits; working tree is the track branch prepared conductor-side. SINGLE-WRITER: you own exactly your one target file; edit NOTHING landed; All.lean/manifest lines wait for the conductor. Re-grep ALL cited corpus lines AND frozen names at start (catch #245 am.1; TCC drift ±1; 8 executors in flight on L2c* files). STATEMENTS LAND VERBATIM from the frozen set — no strengthening/weakening/renaming; packet-free lemmas stay packet-free; no (hf) added for uniformity (flags-wording guard l2c-freeze.md:146). `open Classical in` on every f-filter def (precedent TC:386/TF:177). ≤3 serious attempts per lemma, then STOP and return a flag report (node id, attempts, break point) to the conductor — do NOT edit flags.md (sole catch authority). Verify: lake build (no new warnings) + #print axioms ≤ [propext, Classical.choice, Quot.sound] via uncommitted Scratch.lean; no native_decide, no new axioms. Tools: Read, Bash (grep + ~/.elan/bin/lake), Write/Edit (own file only).

BRIEF W1 [B, volume-flagged] — file Salt/HB/SignChain.lean; import Salt.HB.L2cCore; namespace Salt.HB. Land DES-W §W1 frozen set: IsSignFunction packet + 12 defs + ~24 theorems + the TCC:89-161 helper block. Substitution table: chiRe_mul χ hsq ↦ hf.map_mul; chiRe_one ↦ hf.map_one; chiRe_abs_le_one ↦ hf.abs_le_one; chiRe_eq_one_or_neg_one ↦ hf.prime_pm (hypothesis-FREE — erases every downstream hcop). Keep Real.log ((n / d : ℕ) : ℝ) exactly (ℕ-division, TC:99). gGen map_zero' by simp — explicit term if simp regresses. Order: defs first (the §defs milestone unblocks W2), then TC mirrors, TCC mirrors (re-grep each line), Transfer layer, window+caps, counters. DO NOT re-type: χ-free KC1 layer (consume as-is); bypassed TR:60-71 + TF majorant chain. "KC1 already discharged" does NOT cover the LamTilde/Transfer layer — no skipping.

BRIEF W2 [A/B] — file Salt/HB/SignLiouville.lean; import Salt.HB.SignChain. GATE: dispatch once W1 defs + LamTildeGen_eq_conv compile. Land the 9 frozen decls. Route pins: liouville_apply needs n ≠ 0 (Liouville.lean:31); liouville_apply_mul :40 unconditional (one cast for map_mul); μ²λ=μ via Squarefree split (Moebius.lean:60/64, plus d=0); THE POLE via moebius_mul_log_eq_vonMangoldt (VonMangoldt.lean:130) — NOT sum_moebius_mul_log_eq (:133, wrong shape); S2Gen_lamR_eq_S1 by Finset.sum_congr + pole; PretenseSumGen zero via everywhere-false filter (lamR_prime gives −1 ≠ 1).

BRIEF W3 [B given W1] — file Salt/HB/SignRate.lean; import Salt.HB.SignChain. GATE: W1 landed. Land EngineBound (transcribe EXACTLY — refuter-checked text in the ratified set; rpow discipline on 1/8 and 9/10) + neutrality_rate with the J2 docstring line. Proof: left conjunct = sub_nonneg.mpr (S1_le_S2Gen hf _); right = rw [S2Gen_sub_S1_eq]; exact hbudget. Then append the J1 COMMENT-FROZEN hb_l2c_masterGen docstring block verbatim — NO declaration, NO sorry, NO attempt.

BRIEF D4-a [A/B] — file Salt/Parity/Z.lean; imports Mathlib, Salt.Basic, Salt.Brun.M5BigO ONLY (module invariant: never import Salt.HB/Salt.TwinBar); namespace Salt.Parity. Land all 11 frozen defs (J4/J5 docstrings included) + L0 parityInv_of_closed [A] + L4 bridge [A/B; pure Finset/Nat.count vs TPC Salt/Basic.lean:25-26] + L6 TPC_implies_Z [A; tautological witness E := fun a => ∀C ∃x, C < twinMass a x] + Z_trivial_of_not_completion [A]. rpow not pow for Real.log x ^ A₀ (GEH-FIX catch).

BRIEF D4-b [B/C KEYSTONE] — same file, SEQUENCED after D4-a (single-writer: one executor on the file at a time; conductor hands off). Land L1 oneWeight_mem [B: per-d error ≤ ρ(d) ≤ d; Σ_{d≤x^θ} d ≪ x^{2θ} = o(x·log^{−A₀}x)] + L2 twinFree_mem [B/C: per-d diff ≤ 4·twinPrimeCounting x via the 4-divisor argument {1,n,n+2,n(n+2)}; consume Salt.M5BigO.N5_3 (M5BigO.lean:295) with an x₀-split absorbing atTop into the ∃C ∀x≥2 slot] + twinFree_twinMass [A]. If the absorption turns C-shaped: STOP+flag; do not improvise a weaker statement.

BRIEF D4-c [B] — same file, after D4-b. Land L3 sufficient_true_not_parityInv [B: ParityInv → E twinFree; TwinSufficient + L2 → twinMass twinFree unbounded; companion says ≡ 0] + L5 Z_implies_TPC [B via L1+L4]. Keep h0/h1 hypotheses AS FROZEN (J6 — no trimming). **[J6 SPENT 2026-08-11: `h1` and `ht` dropped by the Captain's ruling (a); `h0` was never unused.]**

BRIEF D4-inst [A] — file Salt/Parity/Instances.lean; imports Salt.Parity.Z + Salt.HB.All, Salt.TwinBar.All, Salt.Chen.All, Salt.BrunLower.All, Salt.Brun.All. Land the L0 instantiations, one line each via parityInv_of_closed, QUALIFIED names only: Salt.HB.S1_le_S2; Salt.TwinBar.{twin_bar, twin_gate_fails, no_twin_weight, noSiegelZeros_iff_not_infinitely}; Salt.Chen.chen_headline (IsP2 is Salt.Chen.IsP2); Salt.BrunLower.twin_almost_prime; Salt.N6.N6_2; Salt.M5BigO.N5_3. Re-grep every name first.

## SCOPE_DIFFS

CONSOLIDATED CATCH-#224 LEDGER (pass3 record → ratified set; mandatory item).
W-SERIES (DES-W #1-10, all RATIFIED as declared, REF-W-checked):
W1. Majorant→exact spine: W3 built on S2_sub_S1_eq (LC:76); hb_lemma2/hres bypassed (l2c-freeze.md:5,12-18; zero consumers); of TransferFull only PretenseSum re-types.
W2. W3 shape: conjunction 0≤·∧·≤EngineBound; pret-independent floor + pinned constants (Aexp=5, junk rpow (x/z^{1/8}+x^{9/10})·L'³, N=2x+2); pret=0 ⇏ bound=0 — "evaluating S2 IS evaluating S1" and pretQ·evalQ=o(1) stay W4 prose (W5 law); λ-corner exact via W2 nodes, bypassing EngineBound.
W3. W3 split: neutrality_rate (budget-conditional, provable now) vs hb_l2c_masterGen (frozen target, D, no attempt).
W4. Dependency order W1-defs < W2: chiRe DirichletCharacter-locked (Salt/TwinBar/TwistedSieve.lean:63, judge-verified); the verdict's W2-first listing was a pricing artifact.
W5. Freeze gates (hz100/hz8/hzx) live ONLY on masterGen — dead hypotheses on neutrality_rate rejected.
W6. Mathlib corrections vs MAP-W: liouville_apply conditional on n≠0 (Liouville.lean:31); liouville_apply_mul unconditional (:40).
W7. Window drops q: excPrimorialGen/l2cWindowGen filter on f alone; CoprimeSupport has NO generic analogue — deleted, not re-typed.
W8. Catch-#245 guards (¬junkBlock, Zz-vs-Zf) live in the future generic EL/ER files; zero impact on the frozen texts.
W9. abs_le_one carried though derivable — honest weakening, keeps the TC:63 route verbatim.
W10. No subsumption: IsSignFunction (chiRe χ) FALSE for q>1; the two chains reconcile only in W4 prose.
W11 (REF-W add): record §5(A) abstract EngineBound(pret, N free) → window-pinned 3-term concrete — a freeze-level decision (l2c-freeze.md:21-31), operative surface followed.
W12 (REF-W add): l2cWindowGen_roughness binds {z x} implicit vs LC:180 explicit — cosmetic, ratified as frozen.
JUDGE AMENDMENTS: J1 masterGen COMMENT-FROZEN (no decl, no sorry — build-discipline). J2 neutrality_rate docstring (unconditional content = S1_le_S2Gen). J3 quantifier ruling (∃Cmain outside ∀; inside = vacuous = forbidden).
Z-SERIES (DES-Z #1-6 with REF-Z corrections APPLIED):
Z1 REWRITTEN: the pass2 sketch (fulcrum-pass2.md:37) already pins g = twin singular-series density; the freeze's contribution is FORMALIZING it as twinRho d / d and foreclosing the ∀g misreading — not a sketch-bug fix (REF-Z misattribution corrected).
Z2 RELABELED: certified range θ∈(0,1/2); "true sequence fails its own norm at θ=1" is MEMORY/heuristic-grade (needs a typeIError LOWER bound, C-class, unproven); the load-bearing fact is only that L1's route caps at θ<1/2; the freeze claims nothing at θ=1.
Z3. Quality A₀ = grade parameter, not ∀A; the ∀A₀ target is the open ParityBarrier def.
Z4 RELABELED: the nonneg pin's rationale is barrier-side naturality (TwinSufficient satisfiability is protected at every grade by the sign-insensitive tautological witness).
Z5. Z = TwinSufficient ∧ E oneWeight; ¬ParityInv DERIVED (L3), not primitive.
Z6. twinMass indicator vs Λ-weighted B(x): the M4 bridge is dodged entirely.
JUDGE Z-AMENDMENTS: J4 import/name plumbing (R-1: import Salt.Brun.M5BigO — judge-verified Salt/Brun.lean lacks it, Salt/Brun/All.lean:13 has it; qualified Salt.M5BigO.N5_3; Instances.lean split; oracle-clean-by-imports invariant). J5 grade guard + Z_trivial_of_not_completion [A] (R-2). J6 L3 h0/h1 kept (flags-wording guard).
CITATION CORRECTIONS (judge, this session): TwistedSieve.lean lives at Salt/TwinBar/TwistedSieve.lean (chiRe :63; dup Salt/SW/DHDetector.lean:78) — MAP-W's path was unqualified and REF-W claimed verification without the path; S1 def is Transfer.lean:176 (MAP-Z cited :173); PretenseSum is TransferFull.lean:183-185, NOT Basic.lean (mission-brief correction per MAP-W diff #6).

## OPEN_RISKS

1. masterGen frozen against an UNLANDED character master (re-verified: no L2cMaster.lean, no All.lean L2c line): MANDATORY catch-#224 EngineBound re-diff at that landing BEFORE any hb_l2c_masterGen attempt; landed junk-row constants (16, 24576) already show Cmain absorbs ≥2.5e4-grade factors — shape unchanged so far.
2. STAGING DEBT gating any writeup use: (a) Hoffstein–Lockhart UNSTAGED — horn B / "full evaluation cone" claims are conditional, W4 prose only; NO Lean statement may depend on it. (b) H-B pp.193-198 must be re-staged before load-bearing reuse of the C⁽³⁾-vacuity benchmark (M6). (c) Selberg 1949 / Bombieri / Opera de Cribro ch.16 UNSTAGED (M1/M2) — gates every ParityBarrier-grade claim; R2 stands: the full barrier may be beyond current mathematics in the (n,n+2) configuration (staged log-Chowla explicitly does not transport — chowla.txt:196-200, GROUNDED).
3. GRADE-INFLATION HAZARD (R1): L2/L3 land BRUN-grade (A₀≤2, θ<1/2), NOT the parity barrier proper; every writeup line carries the grade qualifier + θ-window (R5). Mandatory language (R-4): the parity boundary separates completion-PREDICATES, not theorems; inside-cone certificates are type-level; the arithmetic content lives in the witness completions.
4. W1 volume/grind risk (~600-800 lines, B throughout): TCC line drift ±1 — executors re-grep every cited line; any C-shaped helper ⇒ STOP+flag (iron rule 4); "KC1 already discharged" covers ONLY the pair-sieve/count layer.
5. Z grade-degeneracy: at (θ,A₀) with oneWeight ∉ Completion, Z is trivially satisfied — every downstream Z-claim carries the θ∈(0,1/2) window (J5 guard + Z_trivial_of_not_completion make it kernel-visible).
6. GATES: this set is statement-layer and blueprint-adjacent — JYH sign-off required before any merge toward main (l2c-freeze.md:145 + commit-policy memory); Opus executors on the track branch are NOT gated. Single-writer-on-names: 8 executors in flight on L2c* files — re-grep frozen names at each dispatch.
7. Priced execution frictions (R6, not design risks): ∃C ∀x≥2 absorbing N5_3's atTop force (x₀-split); twinRho edges at d∈{1,2} and the n=1 window edge; rpow-not-pow discipline on Real.log x ^ A₀.
8. M4 (TPC ⟺ Λ-weighted B(x)) remains unlanded — dodged by design, but any future writeup using B(x) re-opens it. M7: Ω(p(p+2))≤3 Chen corollary still unlanded [A]. c₀=1/126848 numeral extraction debt is fulcrum-side, untouched by this block.

## SUMMARY_FOR_JYH

WALL-3: W1+W2+W3 all RATIFIED (both refuters clean; I independently re-verified every load-bearing citation, incl. the mathlib Liouville/vonMangoldt lines and the chiRe lock). hb_l2c_masterGen = comment-frozen target only — no attempt until the character master lands + a mandatory EngineBound re-diff.
D4: DEFINE — Z ratified with the refuter's import-plumbing and grade-guard repairs applied; the gap theorem L3 lands at Brun grade via N5_3; ParityBarrier stays open/D-class.
Dispatch order: W1 now (B, volume-flagged), W2 after the W1 def-slice, then W3 + the D4 chain (D4-a → b → c, Instances parallel); all Opus, no-git executors, track branch.
Your gates: sign-off before any merge toward main; HL/Selberg/Bombieri staging debt gates all writeup claims (grade qualifiers mandatory).
Ledger complete: W#1-12 + J1-J3, Z#1-6 + J4-J6; one refuter misattribution corrected (pass2 had already pinned g) and three citation paths fixed.

dispatch_ready: True

# APPENDIX — THE AUTHORITATIVE FROZEN TEXT (designer records the verdict cites)

## DES-W

### statements

FROZEN STATEMENT SET (namespace Salt.HB; 3 NEW single-writer files, no landed-file edits, All.lean lines wait for landing). Source legend: TC=Salt/HB/TwistChain.lean, TCC=TwistChainC.lean, TR=Transfer.lean, TF=TransferFull.lean, LC=L2cCore.lean, SW=StarWindow.lean. Common: `variable {f : ℕ → ℝ} {n m p : ℕ}`.

== W1 — Salt/HB/SignChain.lean (imports Salt.HB.L2cCore) ==
```lean
/-- W1 PACKET: replaces `χ : DirichletCharacter ℂ q` + `hsq : χ^2 = 1`; record ℱ = f²=1 at EVERY prime, NO modulus (pass3_t3.md:29). -/
structure IsSignFunction (f : ℕ → ℝ) : Prop where
  map_one    : f 1 = 1
  map_mul    : ∀ a b : ℕ, f (a * b) = f a * f b
  abs_le_one : ∀ n : ℕ, |f n| ≤ 1
  prime_pm   : ∀ p : ℕ, p.Prime → f p = 1 ∨ f p = -1

noncomputable def fGenSum (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ d ∈ n.divisors, (μ d : ℝ) ^ 2 * f d  -- TC:94
noncomputable def LamTildeGen (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (μ d : ℝ) ^ 2 * f d * Real.log ((n / d : ℕ) : ℝ)  -- TC:98-99 (keep ℕ-division cast)
noncomputable def gGen (f : ℕ → ℝ) : ArithmeticFunction ℝ := ⟨fun n => (μ n : ℝ) ^ 2 * f n, by simp⟩  -- TC:118
noncomputable def fGenArith (f : ℕ → ℝ) : ArithmeticFunction ℝ := ζ * gGen f  -- TC:136
open Classical in
noncomputable def nPlusGen (f : ℕ → ℝ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => f p = 1), p ^ (n.factorization p)  -- TC:388
open Classical in
noncomputable def nMinusGen (f : ℕ → ℝ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => f p = -1), p ^ (n.factorization p)  -- TC:393
noncomputable def S2Gen (f : ℕ → ℝ) (A : Finset ℕ) : ℝ := ∑ n ∈ A, LamTildeGen f n * LamTildeGen f (n + 2)  -- TR:179
noncomputable def overshootExactGen (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (LamTildeGen f n - Λ n) * LamTildeGen f (n + 2) + Λ n * (LamTildeGen f (n + 2) - Λ (n + 2))  -- LC:68
open Classical in
noncomputable def PretenseSumGen (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ f p = 1), Real.log (p : ℝ) / p  -- TF:183-185; = pret f N
open Classical in
noncomputable def excPrimorialGen (f : ℕ → ℝ) (z : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range z).filter (fun p => p.Prime ∧ f p ≠ -1), p  -- SW:72, q-part GONE
noncomputable def l2cWindowGen (f : ℕ → ℝ) (z x : ℕ) : Finset ℕ :=
  (Finset.Ioc x (2 * x)).filter (fun n => Nat.Coprime (n * (n + 2)) (excPrimorialGen f z))  -- LC:159, q DROPPED

lemma fGen_pow (hf : IsSignFunction f) (a k : ℕ) : f (a ^ k) = f a ^ k  -- TC:55
lemma gGen_mult (hf : IsSignFunction f) : (gGen f).IsMultiplicative  -- TC:181
lemma fGenArith_mult (hf : IsSignFunction f) : (fGenArith f).IsMultiplicative  -- TC:211
lemma fGenArith_nonneg (hf : IsSignFunction f) (n : ℕ) : 0 ≤ fGenArith f n  -- TC:251
lemma LamTildeGen_eq_conv (f : ℕ → ℝ) (n : ℕ) : LamTildeGen f n = (gGen f * ArithmeticFunction.log) n  -- TC:324, packet-free
theorem vonMangoldt_le_LamTildeGen (hf : IsSignFunction f) (n : ℕ) : Λ n ≤ LamTildeGen f n  -- TC:368, Lemma 1(b)
theorem eq_nPlusGen_mul_nMinusGen (hf : IsSignFunction f) (hn : n ≠ 0) : n = nPlusGen f n * nMinusGen f n  -- TC:408, hcop DROPPED
theorem coprime_nPlusGen_nMinusGen (f : ℕ → ℝ) (n : ℕ) : Nat.Coprime (nPlusGen f n) (nMinusGen f n)  -- TC:424
lemma fGenArith_eq_two_pow (hf : IsSignFunction f) (hn : n ≠ 0) (hall : ∀ p ∈ n.primeFactors, f p = 1) :
    fGenArith f n = 2 ^ n.primeFactors.card  -- TCC:67
lemma fGenSum_n_eq_zero (hf : IsSignFunction f) (hn : n ≠ 0) (hM : nMinusGen f n ≠ 1) : fGenSum f n = 0  -- TCC:184, hcop DROPPED
lemma LamTildeGen_eq_zero_of_two_le_card (hf : IsSignFunction f) (hn : n ≠ 0)
    (hM : 2 ≤ (nMinusGen f n).primeFactors.card) : LamTildeGen f n = 0  -- TCC:252, hcop DROPPED
lemma LamTildeGen_eq_single_of_card_one (hf : IsSignFunction f) (hn : n ≠ 0) (hM : IsPrimePow (nMinusGen f n)) :
    LamTildeGen f n = fGenSum f (nPlusGen f n) * Λ (nMinusGen f n)  -- TCC:268, hcop DROPPED
lemma LamTildeGen_le_of_nMinus_one (hf : IsSignFunction f) (hn : n ≠ 0) (hM : nMinusGen f n = 1) :
    LamTildeGen f n ≤ fGenSum f n * Real.log n  -- TCC:293, hcop DROPPED
theorem LamTildeGen_sub_vonMangoldt_le (hf : IsSignFunction f) (hn : n ≠ 0) :
    LamTildeGen f n - Λ n ≤ 2 * (fGenSum f n * Real.log n + (fGenSum f (nPlusGen f n) - 1) * Λ (nMinusGen f n))  -- TCC:317, Lemma 1(c), hcop DROPPED
-- + nPlusGen/nMinusGen sign/pos helper block, signatures verbatim mod chiRe↦f (TCC:89-161)
theorem S1_le_S2Gen (hf : IsSignFunction f) (A : Finset ℕ) : S1 A ≤ S2Gen f A  -- TR:189-192; S1 (TR:176) reused VERBATIM
theorem S2Gen_sub_S1_eq (f : ℕ → ℝ) (A : Finset ℕ) : S2Gen f A - S1 A = ∑ n ∈ A, overshootExactGen f n  -- LC:76, packet-free
lemma lamTildeGen_sub_eq_zero_of_prime (hf : IsSignFunction f) (hp : p.Prime) : LamTildeGen f p - Λ p = 0  -- LC:89
lemma lamTildeGen_sub_eq_zero_of_one (f : ℕ → ℝ) : LamTildeGen f 1 - Λ 1 = 0  -- LC:98
lemma lamTildeGen_sub_eq_zero_of_pure_minus (hf : IsSignFunction f) (hn : n ≠ 0) (hP1 : nPlusGen f n = 1)
    (hM : IsPrimePow (nMinusGen f n)) : LamTildeGen f n - Λ n = 0  -- LC:107, hcop DROPPED
lemma lamTildeGen_sub_eq_zero_of_two_le_card (hf : IsSignFunction f) (hn : n ≠ 0)
    (hM : 2 ≤ (nMinusGen f n).primeFactors.card) : LamTildeGen f n - Λ n = 0  -- LC:118, hcop DROPPED
lemma lamTildeGen_sub_support_classification (hf : IsSignFunction f) (hn : n ≠ 0)
    (hne : LamTildeGen f n - Λ n ≠ 0) :
    ¬ n.Prime ∧ n ≠ 1 ∧ (nMinusGen f n = 1 ∨ (IsPrimePow (nMinusGen f n) ∧ 1 < nPlusGen f n))  -- LC:130
lemma l2cWindowGen_roughness {z x : ℕ} (hn : n ∈ l2cWindowGen f z x) (hp : p.Prime)
    (hpd : p ∣ n * (n + 2)) (hf1 : f p ≠ -1) : z ≤ p  -- LC:180, packet-free
lemma omega_capGen (hf : IsSignFunction f) (z x : ℕ) (hz2 : 2 ≤ z) (hm0 : m ≠ 0) (hmle : m ≤ 2 * x + 2)
    (hrough : ∀ p ∈ (nPlusGen f m).primeFactors, z ≤ p) :
    (2 : ℝ) ^ (nPlusGen f m).primeFactors.card ≤ Real.exp (Real.log 2 * z0 z x)  -- LC:196, hcop DROPPED
lemma lamTildeGen_cap (hf : IsSignFunction f) (z x : ℕ) (hz2 : 2 ≤ z) (hm0 : m ≠ 0) (hmle : m ≤ 2 * x + 2)
    (hrough : ∀ p, p.Prime → p ∣ m → f p ≠ -1 → z ≤ p) :
    LamTildeGen f m ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x  -- LC:227, hcop DROPPED
lemma sum_inv_plusprime_le_pretenseGen (f : ℕ → ℝ) (z N : ℕ) (hz : 1 < z) :
    (∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ f p = 1 ∧ z ≤ p), (1 : ℝ) / p)
      ≤ PretenseSumGen f N / Real.log z  -- LC:372, packet-free
lemma chebyshev_chi_countGen (f : ℕ → ℝ) {a b N : ℕ} (ha : 1 < a) (hbN : b ≤ N) :
    (((Finset.Ioc a b).filter (fun p => Nat.Prime p ∧ f p = 1)).card : ℝ)
      ≤ ((b : ℝ) / Real.log a) * PretenseSumGen f N  -- LC:396, packet-free
-- NOT re-typed (already χ-free, consumed as-is): geomSum_nonneg/sum_ite_lt_pow_nonneg TC:63/78;
-- l2c_pair_count/_clean, Zz/Zf + 100-gates, Mertens re-exports LC:285-366+ (the KC1 layer).
-- NOT re-typed (BYPASSED, zero consumers): overshoot/overshootLog/overshootPP TR:60-71,
-- overshootMajorant/majLogL../hb_lemma2 TF (all but PretenseSum) — see diffs #1.
```

== W2 — Salt/HB/SignLiouville.lean (imports Salt.HB.SignChain; mathlib Liouville) ==
```lean
noncomputable def lamR : ℕ → ℝ := fun n => ((ArithmeticFunction.liouville n : ℤ) : ℝ)
theorem lamR_prime {p : ℕ} (hp : p.Prime) : lamR p = -1
theorem isSignFunction_lamR : IsSignFunction lamR
lemma moebius_sq_mul_lamR (d : ℕ) : (μ d : ℝ) ^ 2 * lamR d = (μ d : ℝ)
lemma gGen_lamR_eq_moebius : gGen lamR = (μ : ArithmeticFunction ℝ)
theorem LamTildeGen_lamR_eq_vonMangoldt (n : ℕ) : LamTildeGen lamR n = Λ n   -- THE λ-POLE
theorem S2Gen_lamR_eq_S1 (A : Finset ℕ) : S2Gen lamR A = S1 A
lemma overshootExactGen_lamR (n : ℕ) : overshootExactGen lamR n = 0
theorem PretenseSumGen_lamR_eq_zero (N : ℕ) : PretenseSumGen lamR N = 0     -- perfect pretense
```

== W3 — Salt/HB/SignRate.lean (imports Salt.HB.SignChain) ==
```lean
/-- Frozen engine-bound shape (l2c-freeze.md:27-33): Aexp = 5 pinned, junk in rpow form,
    scales z0/Lwin landed at LC:54-57. NOT a function of P alone: P-independent floor. -/
noncomputable def EngineBound (Cmain : ℝ) (z x : ℕ) (P : ℝ) : ℝ :=
  Cmain * ((x : ℝ) / z0 z x)
    + Cmain * ((x : ℝ) / Real.log x) * Real.exp (5 * z0 z x) * P
    + Cmain * Real.exp (2 * z0 z x)
        * ((x : ℝ) / (z : ℝ) ^ ((1 : ℝ) / 8) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3

/-- W3 RATIFIED FORM — the neutrality rate, budget-conditional (provable NOW given W1). -/
theorem neutrality_rate (f : ℕ → ℝ) (hf : IsSignFunction f) (z x : ℕ) (Cmain : ℝ)
    (hbudget : ∑ n ∈ l2cWindowGen f z x, overshootExactGen f n
        ≤ EngineBound Cmain z x (PretenseSumGen f (2 * x + 2))) :
    0 ≤ S2Gen f (l2cWindowGen f z x) - S1 (l2cWindowGen f z x) ∧
      S2Gen f (l2cWindowGen f z x) - S1 (l2cWindowGen f z x)
        ≤ EngineBound Cmain z x (PretenseSumGen f (2 * x + 2))

/-- W3 DISCHARGE TARGET (frozen shape ONLY — DO NOT ATTEMPT until the generic EL/ER
    families + the character hb_l2c_master land; D-shaped today, scope diff #2). -/
theorem hb_l2c_masterGen :
    ∃ Cmain : ℝ, 0 < Cmain ∧
      ∀ (f : ℕ → ℝ), IsSignFunction f → ∀ z x : ℕ,
        100 ^ 16 ≤ z → Lwin x ^ 8 ≤ (z : ℝ) → (z : ℝ) ^ 3 ≤ (x : ℝ) →
        S2Gen f (l2cWindowGen f z x) - S1 (l2cWindowGen f z x)
          ≤ EngineBound Cmain z x (PretenseSumGen f (2 * x + 2))
```
N is PINNED to 2x+2 (window top) throughout; horn B (staircase, HL) has NO Lean statement — W4 prose only.

### routes

W2 (A/B, after W1's def slice). lamR_prime: liouville_apply (mathlib Liouville.lean:31, NEEDS h : p ≠ 0 — from hp.pos) + cardFactors_apply_prime (Ω(p)=1) gives (-1)^1; cast to ℝ. isSignFunction_lamR: map_one = liouville_apply_one (:37); map_mul = liouville_apply_mul (:40 — unconditionally completely multiplicative, push_cast); abs_le_one: n=0 → liouville 0 = 0 (def :27); n≠0 → |(-1)^Ω| = 1; prime_pm: right disjunct via lamR_prime. moebius_sq_mul_lamR: case Squarefree d → moebius_apply_of_squarefree (Moebius.lean:60) makes μ d = (-1)^cardFactors d = liouville d (liouville_apply), and (μ d)² = 1; case ¬Squarefree → moebius_eq_zero_of_not_squarefree (:64), both sides 0; d = 0 → μ 0 = 0. gGen_lamR_eq_moebius: ArithmeticFunction.ext + moebius_sq_mul_lamR. THE POLE: LamTildeGen_eq_conv (W1, mirror of TC:324) + gGen_lamR_eq_moebius + moebius_mul_log_eq_vonMangoldt (mathlib VonMangoldt.lean:130, the CONVOLUTION half — NOT sum_moebius_mul_log_eq :133, wrong shape per map). S2Gen_lamR_eq_S1: Finset.sum_congr, rewrite both factors by the pole; simpler than the map's pure-minus-vanishing route (no hcop machinery). overshootExactGen_lamR: rewrite both differences to 0 by the pole, ring. PretenseSumGen_lamR_eq_zero: the filter predicate is everywhere-false (lamR_prime gives -1 ≠ 1), Finset.sum_eq_zero over filter membership.

W1 (B, real re-derivation ~600-800 lines, no design content). Mechanical substitution table: chiRe_mul χ hsq ↦ hf.map_mul; chiRe_one ↦ hf.map_one; chiRe_abs_le_one (TC:49) ↦ hf.abs_le_one; chiRe_eq_one_or_neg_one (TC:397, needed Coprime p q) ↦ hf.prime_pm (hypothesis-FREE — this single swap erases every downstream hcop). (a) Local-factor/nonneg layer TC:63-314 survives verbatim: geomSum_nonneg is already generic; 1 + f p ≥ 0 and |f p| ≤ 1 from abs_le_one (map obstacle iii). (b) ± factorization TC:407-439: filter-congr step at TC:414-420 consumes prime_pm directly; hn : n ≠ 0 is the sole hypothesis. (c) TCC re-types: proofs mirror TCC:67-317 with hcop threads deleted; re-grep TCC lines before citing (±1 drift, memory flag). (d) Transfer layer: S1_le_S2Gen via re-typed twin_termwise_nonneg (TR:143-152 shape, 1(b)-only); S2Gen_sub_S1_eq is unfold + sum_sub_distrib + ring (LC:76-80 verbatim). (e) Window: l2cWindowGen drops q; roughness mirrors LC:180-192 (Finset.dvd_prod_of_mem on excPrimorialGen); NO CoprimeSupport analogue exists anywhere generic — the only consumer of q-coprimality was 1(c)'s hcop, now gone. (f) Counters LC:372-408: chiRe appears only inside filter predicates — pure substitution. Decidability: `open Classical in` on every f-filter def (corpus precedent TC:386, TF:177).

W3 (ratified form: B given W1; target: frozen only). neutrality_rate: left conjunct = S1_le_S2Gen f (l2cWindowGen f z x); right conjunct = rw [S2Gen_sub_S1_eq] then exact hbudget — the exact spine (landed LC:76) replaces the bypassed majorant, à la hb_lemma2's hres slot (TF:204-214) but on the EQUALITY. hb_l2c_masterGen discharge plan (NOT now): generic re-run of the frozen L2c program — re-typed EL_T1/T2/T3/Tsw + ER mirrors + catch-#245 junk rows and inline ¬junkBlock guards (l2c-freeze.md S4 + :156-189) + master assembly; mirror the character hb_l2c_master AFTER it lands (it does not exist yet — no L2cMaster.lean, no All.lean L2c line), so the generic proof copies a proven artifact, not a plan.

### diffs

CATCH-#224 DIFFS (pass3 record / mission brief vs frozen set; corpus followed in each):
1. MAJORANT→EXACT SPINE. Record routes W3 through hb_lemma2/hres (pass3_t3.md:17-19, :100-101); the L2c freeze BYPASSED that layer (l2c-freeze.md:5,12-18, zero consumers grep-verified). W1 therefore does NOT re-type overshoot/overshootLog/overshootPP (TR:60-71) nor TransferFull's majorant chain — of TransferFull only PretenseSum re-types. This narrows the mission phrase "re-typing of the Transfer/TransferFull chain": the live chain is Transfer §3 + TwistChain/TwistChainC + L2cCore, with TF:183-185 as the sole TF survivor.
2. W3 SHAPE. Record: `|S2(f) − S1| ≤ EngineBound(pret(f,N))` (pass3_t3.md:140), EngineBound abstract in pret, N free. Frozen: conjunction 0 ≤ · ∧ · ≤ · (abs redundant given S1_le_S2Gen; corpus style); EngineBound is NOT a function of pret alone — pret-independent floor Cmain·x/z₀ + junkExpr, pret coefficient Cmain·(x/log x)·e^{5z₀}; constants pinned per freeze (Aexp=5, junk (x/z^{1/8}+x^{9/10})·L'³ in rpow form); N PINNED to 2x+2. Consequence (honest-shape law): at pret = 0 the bound is NOT 0 — "evaluating S2(f) IS evaluating S1" and pretQ·evalQ = o(1) remain W4 PROSE (W5 law: no o(1)/staircase/cone content in any Lean statement). For f = λ alone, S2−S1 = 0 EXACTLY via W2 + S2Gen_sub_S1_eq, bypassing EngineBound.
3. W3 SPLIT (ratified vs target). Record priced one C-class theorem; but hb_l2c_master is frozen-UNLANDED (no L2cMaster.lean; All.lean has no L2c line — scope diff #2). Frozen set: neutrality_rate = budget-conditional, provable now (hres-style hypothesis on the EXACT sum, memory-flag-#3 discipline); hb_l2c_masterGen = the ∃-Cmain-absolute discharge shape, statement frozen, proof forbidden until the generic families + character master land.
4. DEPENDENCY ORDER. Verdict/commissions listed W2 before W1 (pricing artifact); true order is W1-defs < W2 (chiRe is DirichletCharacter-locked, TwistedSieve.lean:63 — "Λ̃_λ" is untypeable against LamTilde χ). Mitigation: W2 consumes only the W1 def slice + LamTildeGen_eq_conv, so W2 may dispatch immediately after W1 §defs, before the full W1 chain.
5. GATES MOVED. The freeze's hyp-set (hz100/hz8/hzx, l2c-freeze.md:28) does no work in the conditional proof; carrying them on neutrality_rate would be dead hypotheses (lint + dishonest bulk). They live ONLY on hb_l2c_masterGen. Types on the target unchanged — interface-safe.
6. MATHLIB GROUNDING CORRECTIONS vs MAP-W: liouville_apply is `{n : ℕ} (h : n ≠ 0)` (Liouville.lean:31) — NOT unconditional as the map's citation reads; and liouville_apply_mul (:40) gives complete multiplicativity unconditionally — map_mul for lamR is one cast, cheaper than the map's squarefree case split (that split is still the route for μ²λ=μ).
7. WINDOW DROPS q. l2cWindowGen/excPrimorialGen filter on f alone (record ℱ "no modulus", pass3_t3.md:29; scope diff #7). CoprimeSupport q A has NO generic analogue anywhere — the record's re-typing of it is vacuous, deleted rather than re-typed. The generic window is load-bearing beyond W3 (future generic S2_sub_S3_window / WP3 parallel — NOT commissioned here).
8. CATCH #245 (post-record amendment): the ¬junkBlock family guards and Zz-vs-Zf sift-floor correction (l2c-freeze.md:156-189) live inside the future generic EL/ER files; zero impact on these frozen statement texts (reconciliation iff-lemmas travel with the discharge).
9. PACKET REDUNDANCY: abs_le_one is derivable (n ≥ 1) from map_one+map_mul+prime_pm but is carried per the map's packet spec — an extra hypothesis weakens, never falsely strengthens (honest); it keeps the TC:63 geomSum route verbatim.
10. NO SUBSUMPTION: `IsSignFunction (chiRe χ)` is FALSE for q > 1 (χ vanishes at p ∣ q) — the generic chain does not instantiate to characters; pole (b) stays on the landed χ-typed chain. Record's ℱ honored exactly; the two chains reconcile only in W4 prose.

### risks

1. TARGET FROZEN AGAINST AN UNLANDED MASTER: hb_l2c_masterGen mirrors a character theorem that exists only as a frozen plan (l2c-freeze.md:27-33). If character Wave-3 assembly repairs any constant (Aexp, junk exponents, gate set), EngineBound must be RE-frozen — a mandatory catch-#224 freeze-to-freeze diff at that landing. Until then hb_l2c_masterGen is D-shaped: no automated attempt (iron-rule discipline); the provable-now W3 deliverable is neutrality_rate only.
2. W1 VOLUME: a genuine re-derivation (~600-800 lines), B-class throughout but with grind risk; TwistChainC line drift ±1 (freeze S7) — executors must re-grep every cited line; any helper that turns C-shaped ⇒ STOP and flag per iron rule 4. "KC1 already discharged" covers ONLY the pair-sieve/count layer — do not let an executor skip the LamTilde/Transfer re-proofs on that basis.
3. ELABORATION TRAPS: (a) every filter over `f p = 1` / `f p ≠ -1` needs `open Classical in` (precedent TC:386, TF:177); (b) keep `Real.log ((n / d : ℕ) : ℝ)` with ℕ-division exactly as TC:99 — "fixing" to real division is statement drift; (c) gGen's map_zero' `by simp` must close (μ 0 = 0); give an explicit term if simp regresses.
4. NAME HYGIENE: all frozen names grep-clean in Salt/ today, but files are in flight elsewhere; single-writer law extends to NAMES (catch-#245 amendment 1) — re-grep at dispatch. Packet-free lemmas are marked packet-free deliberately; executors must not add (hf) "for uniformity" (lint/interface drift).
5. FALSIFIABILITY POSTURE: the corollary pretQ·evalQ = o(1), the staircase, and Hoffstein–Lockhart are NOT stated (W5 law; HL unstaged — no Lean statement may depend on it). The Lean-fixed consequences are exactly: S2Gen_lamR_eq_S1 + PretenseSumGen_lamR_eq_zero (the tautology corner, exact) and neutrality_rate (the priced rate). Flags-wording guard (l2c-freeze.md:146) applies: statements land verbatim, no strengthening at Lean time.
6. RATIFICATION GATE: this set is statement-layer and blueprint-adjacent — JYH sign-off required before any merge toward main (l2c-freeze.md:145; Fable workflow gate; commit-policy memory). Opus executors for W1/W2 on the track branch are not gated. Suggested classes for dispatch: W2 = A/B (post W1-defs), W1 = B (volume-flagged), neutrality_rate = B (given W1), hb_l2c_masterGen = frozen/unattempted.
7. VERIFY POSTURE (catch #98): the EngineBound constant arithmetic (5·z0, 2·z0, 1/8, 9/10, L'³) is a solo freeze of pinned numerals — warrant a parallel refuter pass on the EngineBound expression against l2c-freeze.md:27-33 before W3 dispatch (cheap; the transcription is the risk, not the math).
8. AXIOM/BUILD: all statements use only landed types + mathlib; expected axiom profile propext/Classical.choice/Quot.sound (Classical via filter decidability); no native_decide anywhere.

## DES-Z

### verdict

define

### definition

FROZEN Lean text (new module, suggested Salt/Parity/Z.lean; namespace Salt.Parity; imports Mathlib + Salt.Basic + Salt.Brun):

```lean
namespace Salt.Parity

/-- ρ(d): #{r < d : d ∣ r(r+2)} — the local twin density numerator.
    PINNED, not quantified: completions must share the TRUE twin Type-I
    main term (fixes the pass2 sketch's ∀g bug, which admitted a ≡ 0
    with g ≡ 0 as a completion). -/
def twinRho (d : ℕ) : ℕ :=
  ((Finset.range d).filter (fun r => d ∣ r * (r + 2))).card

/-- The (n,n+2) Type-I congruence sum of weight `a` at level `d`, window `x`.
    NOTE: this is the ONLY functional through which the class reads `a` —
    pure Type-I is pinned by the TYPE, so Type-II bilinear data (M5 knob,
    fulcrum-pass2.md:82) is structurally inexpressible, not merely excluded. -/
noncomputable def typeISum (a : ℕ → ℝ) (d x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, if d ∣ n * (n + 2) then a n else 0

/-- Pure Type-I error norm at divisor level x^θ. -/
noncomputable def typeIError (a : ℕ → ℝ) (θ : ℝ) (x : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊,
    |typeISum a d x - (twinRho d : ℝ) / d * x|

/-- 𝒞(θ,A₀): nonnegative completions carrying the true twin Type-I data at
    level x^θ, quality (log x)^(−A₀), with a per-completion constant. -/
def Completion (θ A₀ : ℝ) (a : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ a n) ∧
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
    typeIError a θ x ≤ C * x / Real.log x ^ A₀

/-- ParityInv at grade (θ,A₀): E holds in EVERY completion.  Semantic
    (model-class) invariance — quantifies over the mechanism, not the method. -/
def ParityInv (θ A₀ : ℝ) (E : (ℕ → ℝ) → Prop) : Prop :=
  ∀ a : ℕ → ℝ, Completion θ A₀ a → E a

/-- Twin mass of a completion (consumers use the W5 shape ∀C ∃x). -/
noncomputable def twinMass (a : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, if n.Prime ∧ (n + 2).Prime then a n else 0

/-- Twin-sufficiency: E semantically FORCES unbounded twin mass in every
    completion satisfying it.  The load-bearing lower-bound clause. -/
def TwinSufficient (θ A₀ : ℝ) (E : (ℕ → ℝ) → Prop) : Prop :=
  ∀ a : ℕ → ℝ, Completion θ A₀ a → E a →
    ∀ C : ℝ, ∃ x : ℕ, C < twinMass a x

def oneWeight : ℕ → ℝ := fun _ => 1

/-- The Brun-grade twin-free completion 𝒜⁻ (the landable witness). -/
noncomputable def twinFree : ℕ → ℝ :=
  fun n => if n.Prime ∧ (n + 2).Prime then 0 else 1

/-- **Z — the demand specification, frozen.**  A twin proof must supply a
    predicate on completions that forces unbounded twin mass across the whole
    pure-Type-I model class AND holds for the true sequence.  No
    DirichletCharacter, no L-function, no exceptional-character oracle
    appears anywhere in the inputs. -/
def Z (θ A₀ : ℝ) : Prop :=
  ∃ E : (ℕ → ℝ) → Prop, TwinSufficient θ A₀ E ∧ E oneWeight

/-- The OPEN full-quality parity barrier (stated, never assumed): a bounded-
    twin completion at EVERY quality.  M1/M2-grade target, D-class. -/
def ParityBarrier (θ : ℝ) : Prop :=
  ∀ A₀ : ℝ, 1 ≤ A₀ → ∃ a : ℕ → ℝ, Completion θ A₀ a ∧
    ∃ M : ℝ, ∀ x : ℕ, twinMass a x ≤ M

end Salt.Parity
```

CATCH #224 FREEZE-TO-FREEZE SCOPE DIFFS vs the pass2 sketch (fulcrum-pass2.md:37-39) — all six are deliberate:
1. g PINNED to twinRho d / d (sketch quantified ∀g — a bug: admits the zero completion, voiding the model class).
2. θ ∈ (0,1) open, instances landed at θ < 1/2 (sketch said θ ≤ 1; at θ = 1 the TRUE sequence fails its own norm: Σ_{d≤x} ρ(d) ≍ x·log x ≫ x·log⁻ᴬx — arithmetic catch, this session).
3. Quality A₀ is a GRADE PARAMETER, not ∀A (the sketch's ∀A form makes non-vacuity M1-hard; grading makes it Brun-landable at A₀ ≤ 2 while keeping ∀A₀ as the flagged open ParityBarrier).
4. Completions pinned nonnegative (blocks signed pathologies that would make TwinSufficient unsatisfiable even under TPC — the graver vacuity pole).
5. Z stated as TwinSufficient ∧ E(oneWeight); ¬ParityInv is DERIVED (lemma L3), not primitive — closes the trivial-satisfiability hole (E := "a = oneWeight" fails TwinSufficient).
6. Twin functional = indicator twinMass over actual prime pairs, NOT Λ-weighted B(x): the M4 bridge (MEMORY, unlanded, fulcrum-pass2.md:88) is DODGED entirely; the repo TPC (Salt/Basic.lean:25-26) is already ∀∃-shaped and bridges to twinMass oneWeight by A/B Finset arithmetic.

### lemma_shapes

INSENSITIVITY (bar ii — cheap Opus nodes):
L0 schema [A]: theorem parityInv_of_closed (θ A₀ : ℝ) {P : Prop} (hP : P) : ParityInv θ A₀ (fun _ => P) := fun _ _ => hP. Instantiations (each one line, `parityInv_of_closed _ _ <landed>`): parityInv_S1_le_S2 (P := ∀ q (χ : DirichletCharacter ℂ q), χ^2 = 1 → ∀ A, Salt.HB.S1 A ≤ Salt.HB.S2 χ A; Transfer.lean:189-192); parityInv_twin_bar (Impossibility.lean:173); parityInv_twin_gate_fails (:262); parityInv_no_twin_weight (:276); parityInv_noSiegel_iff (SiegelTwin.lean:129-131, the 𝒟(¬F)-cone anchor; the K1 contrapositive instance lands when D1 lands); parityInv_chen_headline (ChenTheorem.lean:32); parityInv_twin_almost_prime (BrunLower/TwinInstance.lean:16); parityInv_brun (N5_3, M5BigO.lean:295; N6_2, N6.lean:231). Honest label: these certify that every listed landed theorem is a CLOSED proposition — it never reads the completion — which is exactly the formal content of "𝒟(¬F) ⊆ ParityInv" under semantic invariance. Optional C-class upgrades (relativized in-model Selberg/Brun ceilings, e.g. ∀ a, Completion θ 2 a → sieve upper bound on twinMass a) are follow-on nodes, NOT required by the bar.

MODEL-CLASS LEMMAS:
L1 true-completion membership [B at θ<1/2; C-node for θ<1]: theorem oneWeight_mem {θ A₀ : ℝ} (h0 : 0 < θ) (h : θ < 1/2) (hA : 0 ≤ A₀) : Completion θ A₀ oneWeight. Proof: |typeISum 1 d x − ρ(d)x/d| ≤ ρ(d) ≤ d, Σ_{d≤x^θ} d ≪ x^{2θ} = o(x·log⁻ᴬ⁰x). The θ<1 extension needs ρ(d) ≤ 2·τ(d)² (roots of r(r+2) ≡ 0 pinned by divisor pairs via gcd(r,r+2) ∣ 2 + CRT) — a separate flagged C-node.
L2 Brun witness [B/C — the keystone, consumes GROUNDED N5_3]: theorem twinFree_mem {θ A₀ : ℝ} (h0 : 0 < θ) (h : θ < 1/2) (hA : A₀ ≤ 2) : Completion θ A₀ twinFree. Proof: the diff from oneWeight at each d is ≤ #{twins n ≤ x with d ∣ n(n+2)}; each twin n contributes to at most its 4 divisors {1, n, n+2, n(n+2)}, so the level-summed diff is ≤ 4·twinPrimeCounting x, and N5_3 : TwinCountingBigO (M5BigO.lean:295) gives O(x/log²x). Companion [A]: theorem twinFree_twinMass : ∀ x, twinMass twinFree x = 0.

THE GAP (necessity) THEOREM [B given L2]:
L3: theorem sufficient_true_not_parityInv {θ A₀ : ℝ} (h0 : 0 < θ) (h : θ < 1/2) (h2 : A₀ ≤ 2) {E} (hs : TwinSufficient θ A₀ E) : ¬ ParityInv θ A₀ E. **[RE-CUT 2026-08-11 — `h1` and `ht` dropped as provably unused; the shape above is the CURRENT one, the original carried `(h1 : 1 ≤ A₀)` and `(ht : E oneWeight)`.]** Proof: ParityInv gives E twinFree; TwinSufficient + L2 forces twinMass twinFree unbounded; L2-companion says it is 0. THIS is Z's gap statement made kernel-real: every twin-sufficient true estimate must break parity-invariance at Brun grade.

THE DEMAND LEMMA (bar iii — honest landing point: full TwinPrimeConjecture, no weakening needed):
L4 bridge [A/B]: theorem twinMass_oneWeight_unbounded_iff : (∀ C : ℝ, ∃ x : ℕ, C < twinMass oneWeight x) ↔ TwinPrimeConjecture (repo form Basic.lean:25-26; Finset counting, no Λ, no M4).
L5 demand [B given L1+L4]: theorem Z_implies_TPC {θ A₀ : ℝ} (h0 : 0 < θ) (h : θ < 1/2) (hA : 0 ≤ A₀) : Z θ A₀ → TwinPrimeConjecture.
L6 non-degeneracy converse [A]: theorem TPC_implies_Z {θ A₀ : ℝ} : TwinPrimeConjecture → Z θ A₀ (witness E := fun a => ∀ C, ∃ x, C < twinMass a x — tautologically sufficient; E oneWeight ⟺ TPC via L4). So Z θ A₀ ⟺ TPC: Z is exactly a demand specification, and L3 proves every way of meeting it is parity-breaking.

OPEN TARGET (stated in the freeze, never assumed): ParityBarrier θ — D-class, M1/M2-flagged; see risks.

### rationale

VERDICT: define. The refined Boundary A′ passes all four bars where the map's raw candidates each failed one, and the deadlock the map priced (non-vacuity resting on MEMORY M1) dissolves under quality grading.

Bar (i) — precise demand spec, oracle-free: Z θ A₀ is a Prop family in real corpus types (ℕ → ℝ weights, Finset sums, Real.log); no DirichletCharacter, LamTilde, L-function, or ¬F anywhere in its inputs (GROUNDED: the frozen text above is self-contained modulo Salt.Basic + Salt.Brun). It states exactly what a twin-sufficient parity-breaking estimate IS: a predicate on pure-Type-I completions forcing twin mass, true of the real sequence.

Bar (ii) — all mapped inside theorems provably insensitive: discharged by the L0 schema + one-line instantiations (every listed inside object — S1_le_S2, the 𝒟(¬F) anchors, twin_bar family, chen_headline, twin_almost_prime, Brun — is a closed proposition; all names/lines re-verified this session). Semantic invariance is the honest formalization: a proof-theoretic "derivable-from-Type-I" ParityInv would need a deep-embedded proof system (D-class) and would ossify the method — precisely failure (iv). The model-class rendering is the standard analytic-number-theory meaning of the parity phenomenon (two completions, same data, different twin counts), and it puts the content where it belongs: in the witness completions.

Bar (iii) — twin-sufficiency provably outside: L3 lands it at grade A₀ ≤ 2, θ < 1/2, using ONLY in-house theorems — the decisive grounding find is N5_3 : TwinCountingBigO (Salt/Brun/M5BigO.lean:295, proven and imported on main via Salt.lean:2-4), which certifies the twin-free completion twinFree ∈ 𝒞(θ,2) because a twin pair n has exactly 4 divisors of n(n+2). Honest landing point of the demand lemma: full TwinPrimeConjecture (L5) — no weaker surrogate needed, because freezing twinMass as an indicator functional against the repo's ∀∃-form TPC (Basic.lean:25-26) removes the Λ-weighted B(x) object and with it the unlanded M4 bridge entirely.

Bar (iv) — anti-ossification: E quantifies over ALL predicates on completions — a future Friedlander–Iwaniec-style bilinear estimate in the (n,n+2) configuration enters as the semantic consequence class of whatever it proves, with zero reference to Selberg weights, LamTilde, or characters (the map's ossification failure modes for B and C are structurally impossible here). Boundaries B and C become PROVEN in-cone instances (parityInv_twin_bar, parityInv_S1_le_S2), never the boundary. Type-II smuggling (M5) is closed by the type of typeIError, not by a side condition — the definitional cliff the map flagged as swinging both risk poles is welded shut in the only direction that keeps 𝒜⁻ a model.

Why the map's DEFER-shaped deadlock dissolves: the map treated non-vacuity as resting wholly on M1 (Selberg/Bombieri twin-free completion, MEMORY, unstaged). Quality grading splits that claim: at A₀ ≤ 2 the barrier certificate is SPARSITY-grade and Brun-landable now (L2/L3); the full parity grade (∀A₀ — the λ-biased completion) is exactly the frozen open ParityBarrier target. Z's demand shape, the demand lemma, and the inside cone are all A₀-uniform, so nothing in the freeze waits on M1. The freeze also caught and repaired two outright bugs in the pass2 sketch (∀g; θ = 1 falsified by the true sequence) — recorded as catch #224 scope diffs 1-2.

Node pricing for the ratification block: L0 instances A-class (Opus/Sonnet); L1 B; L2 B/C (keystone, consumes N5_3); L3 B; L4 A/B; L5 B; L6 A. The τ²-density node (θ < 1 extension) and any relativized-ceiling upgrades are optional follow-ons. ParityBarrier is D-class, not commissioned.

### risks

R1 (dominant, honest-shape law) — GRADE INFLATION HAZARD: the landable L3 certificate at A₀ ≤ 2 is BRUN-grade (twins are sparse), NOT the parity barrier proper. It must never be presented as "the parity problem formalized" — the parity-grade statement is exactly ParityBarrier (∀A₀), which remains OPEN. Every writeup line about L3 needs the grade qualifier.

R2 (sharpens fulcrum-pass2.md:81, MEMORY→concrete) — the full ParityBarrier may be beyond current mathematics in the (n,n+2) configuration, not merely unstaged: the λ-biased completion a = 1 − λ(n)λ(n+2) requires two-point λ-correlation cancellation in arithmetic progressions UNIFORMLY to level x^θ; the staged log-Chowla corpus (1503.05121/chowla.txt, and the landed log_chowla_two) is fixed-coefficient and log-averaged, and Tao's disclaimer (chowla.txt:196-200, GROUNDED) is verbatim that it does not transport to twin-type sums. The classical Selberg 1949/Bombieri examples (M1/M2, MEMORY, unstaged) are single-variable; staging Opera de Cribro ch.16 may NOT mechanically discharge the twin-config case. Consequence if ParityBarrier is unprovable: Z and all frozen lemmas survive unchanged (nothing depends on it); only the barrier's GRADE stays Brun+kernel-k=2 — the honest state, already labeled.

R3 (referee-facing) — Z θ A₀ ⟺ TPC (L5+L6) is BY DESIGN (demand specification): the content is L3 (every satisfaction breaks invariance) plus the model class itself, not Z's raw satisfiability. A reader mistaking Z for "new content beyond TPC" must be pointed at L3; a reader calling Z circular must be pointed at L6's tautological witness — the W5 law is what makes the ∀C∃x shape non-degenerate.

R4 (semantic-vs-derivability, priced in rationale) — semantic invariance makes the L0 inside lemmas trivial. This is honest (closed props cannot read a completion) but means the inside cone certification carries no arithmetic information; the map's derivability intuition is captured only by the optional relativized-ceiling C-nodes. Accepted trade: the alternative (deep-embedded derivability) is D-class and ossifies.

R5 (instance-range debt) — L1/L2/L3/L5 land at θ < 1/2 (crude ρ(d) ≤ d). The θ < 1 extension needs the ρ(d) ≤ 2τ(d)² node (C-class). Until it lands, barrier instances cover level < x^{1/2} — which already includes every level the corpus's sieves actually use, but the θ-range must be stated in any claim.

R6 (formal fit) — small Lean frictions to expect at execution: the ∃C ∀x≥2 constant-slot form must absorb small-x and the atTop-only force of N5_3 (choose C after an x₀-split — B-grade fiddle, not a design risk); twinRho at d ∈ {1,2} and the n=1 window edge need the usual norm_num edge lemmas; Real.log x ^ A₀ needs rpow vs pow discipline (the corpus's GEH-FIX catch — use rpow).

MEMORY-LABEL SUMMARY: everything in the frozen definition and lemmas L0-L6 is GROUNDED-buildable (all cited names/lines re-verified this session, including N5_3 on main). MEMORY items remaining load-bearing ONLY for the open ParityBarrier target: M1/M2 (Selberg/Bombieri, unstaged), the R2 two-point-Chowla-in-APs obstruction analysis (this session's arithmetic, unrefereed). M4 is dodged, M5 is welded shut by the type, M3 is honored (nothing encodes "no such bilinear structure exists"), M6/M7 do not touch Z.

## REFW (refuter record)

### verdicts

{
"W1_SignChain": {"verdict": "SURVIVES", "certificate": "TYPE-CHECK: every cited corpus line verified exact this pass (GROUNDED): TC:94/98-99/118/136/388/393 defs, TC:55/181/211/251/324/368/408/424 lemmas; TCC:67/184/252/268/293/317 + helper block TCC:89-161; TR:176/179/189-192; TF:183-185; LC:68/76/89/98/107/118/130/159/180/196/227/372/396; SW:72-73. No ±1 drift in any citation used. UNPROVABILITY: the hcop-erasure checked at its load-bearing point — the SOLE hcop consumer in the whole chain is chiRe_eq_one_or_neg_one (TC:397, consumed at TC:414-420 and TCC:136-150); prime_pm replaces it hypothesis-free; every downstream hcop-drop (eq_nPlusGen_mul_nMinusGen through omega_capGen/lamTildeGen_cap) reduces to that one swap — sound. vonMangoldt_le_LamTildeGen re-derivation priced: gGen local factor via fGen_pow (map_one+map_mul induction) + sum_ite_lt_pow_nonneg with hf.abs_le_one — B-class as claimed. Decidability: open Classical precedent TC:386/TF:177 GROUNDED. VACUITY: cleared — map_one blocks f≡0; witnesses f≡1 and λ exist. Packet note: complete multiplicativity (∀ a b) vs record's 'multiplicative' is the record's own WLOG (pass3_t3.md:29-32 'determined by ε: Primes → {±1}'; engine reads f only at squarefree d, :11-12) — not a silent scope change. NAME HYGIENE: all frozen names grep-clean in Salt/ at this pass; SignChain/SignLiouville/SignRate files do not exist. Minor: l2cWindowGen_roughness binds {z x} implicit vs LC:180 explicit — elaborates (inferable from hn), cosmetic only."},
"W2_SignLiouville": {"verdict": "SURVIVES", "certificate": "MATHLIB GROUNDING verified at exact lines: liouville : ArithmeticFunction ℤ (Liouville.lean:27-29); liouville_apply {n}(h : n ≠ 0) :31 — DES-W's correction of MAP-W CONFIRMED; apply_one :37; apply_mul UNCONDITIONAL :40 — confirmed; cardFactors_apply_prime Misc.lean:303; moebius_apply_of_squarefree Moebius.lean:60; moebius_eq_zero_of_not_squarefree :64; moebius_mul_log_eq_vonMangoldt VonMangoldt.lean:130 = (μ : ArithmeticFunction ℝ) * log = Λ — the convolution half, correct shape; sum_moebius_mul_log_eq :133 is indeed the wrong shape (∑ μ(d)·log d = −Λ). POLE route case-complete: moebius_sq_mul_lamR holds at d=0/non-squarefree/squarefree (squarefree ⇒ d≠0 unlocks liouville_apply); gGen_lamR ext incl. n=0 via map_zero. lamR carries the required noncomputable (Int.cast into ℝ). λ-CORNER consistency: excPrimorialGen lamR z = 1 (empty filter), window unsifted, but S2Gen−S1 ≡ 0 exactly — no falsity, matches diff #2's bypass note. PretenseSumGen_lamR: filter everywhere-false via lamR_prime — provable. All A/B pricing confirmed."},
"W3_SignRate_neutrality_rate": {"verdict": "SURVIVES (with recorded notes)", "certificate": "Provable now given W1: left conjunct = sub_nonneg.mpr (S1_le_S2Gen hf W); right = rw [S2Gen_sub_S1_eq]; exact hbudget. Diff #5 correct: the freeze gates do no work here — carrying them would be dead hypotheses; total-function degeneracies at z≤1 (z0=0, x/0=0) are semantic only, no falsity. NOTE for the minutes: its UNCONDITIONAL content is exactly S1_le_S2Gen; the priced-rate content lives in hbudget until masterGen — declared (diff #3, hres precedent TF:204-214), acceptable as ratified interface."},
"W3_SignRate_EngineBound_and_masterGen": {"verdict": "SURVIVES (with recorded notes)", "certificate": "TRANSCRIPTION (catch #98 refuter pass, the declared risk): term-by-term vs l2c-freeze.md:27-33 — Cmain·x/z0 ✓; Cmain·(x/log x)·e^{5·z0}·P, Aexp=5 ✓; junk Cmain·e^{2·z0}·(x/z^{1/8}+x^{9/10})·L'³ rpow form ✓; N pinned 2x+2 ✓; gates hz100/hz8/hzx verbatim (Lwin x^8 ≤ z ⇔ (log(2x+2))^8 ≤ z, LC:54) ✓. POST-FREEZE SURFACE: landed junk rows (L2cELJunk: 16·e^{2z0}·x/z^{1/8}·L'³, 24576·e^{2z0}·x^{9/10}·L'³) fit the shape, constants Cmain-absorbable — no drift yet; character master still unlanded (no L2cMaster.lean, All.lean L2c-line absent — verified), so risk #1's mandatory re-diff at that landing stands. QUANTIFIER: ∃Cmain ∀f∀z∀x is the ONLY non-vacuous reading of the freeze's 'EXISTS Cmain > 0 ABSOLUTE' — ∃ inside the context would be trivially dischargeable by Cmain-monotonicity of EngineBound (the vacuity trap; DES-W avoided it). VACUITY: gate region nonempty (z=100^16, x ∈ [10^96, e^{10^4}] approx). WORST CORNERS run: f=λ (S2−S1=0, EngineBound ≥ 0 at pret=0 — holds, bypass per diff #2); f≡1 (pret ≈ L maximal; pretense term ~Cmain·x·e^{5z0} dominates the capped/sifted S2 since 5 > 2log2, z0² absorbable); adversarial f (all p<z at −1, window-scale primes +1: window UNSIFTED, pret=O(1), but overshoot support is empty in-window — n₊·n₋ needs n₊ > x, n₋ ≥ 2 ⇒ n > 2x; the general adversary is λ-pretender-grade, exactly what the freeze's χ-uniform rows price; T1-corner arithmetic re-run: Σ_v 2Λ(v)·L·x/(v·log²x) ≈ 2Cx/z0 fits the no-PS row). No falsifying instance found. D-freeze discipline on masterGen correct."},
"cross_cutting": {"verdict": "SURVIVES", "certificate": "CATCH #224: all 10 declared diffs check out against BOTH surfaces (pass3_t3.md:17-19/29/100-101/137-141; l2c-freeze.md:5/12-18/21-33/145-146/156-189). Independent sweep found two additional diffs, neither silent-fatal: (i) record §5(A) arbitrary-A/abstract EngineBound(pret) → window-pinned 3-term concrete — a freeze-level decision (l2c-freeze.md:21-31), DES-W follows the operative surface; (ii) the roughness binder cosmetics. W5 LAW: no Q/q, no o(1)/staircase/HL in any Lean text; horn B prose-only ✓. HONEST-SHAPE: pret-independent floor kept, no compression ✓. Diff #4 verified: chiRe is DirichletCharacter-locked at TwistedSieve.lean:63. Diff #10 verified: IsSignFunction (chiRe χ) false for q>1 (χ vanishes on p∣q vs prime_pm) — no false subsumption claimed."}
}

### repairs

NONE BLOCKING. Four non-blocking hardenings for the ratification minutes: (1) RECORD the quantifier ruling — hb_l2c_masterGen's ∃Cmain-OUTSIDE-∀ is the ratified reading of the freeze's 'ABSOLUTE'; guard against any future 'faithful' transcription moving ∃ inside the hypothesis context, which is trivially provable (Cmain-monotonicity) = vacuous. (2) Land neutrality_rate with a docstring line stating its unconditional content = S1_le_S2Gen and that the rate content is hbudget-conditional pending masterGen (flags-wording guard, l2c-freeze.md:146 discipline — no strengthening at Lean time). (3) Risk #1 is confirmed live: the character hb_l2c_master is unlanded (no L2cMaster.lean; All.lean L2c-line absent); at that landing a mandatory catch-#224 EngineBound re-diff must run before any masterGen attempt — landed junk-row constants (16, 24576) already show Cmain must absorb ≥ 2.5e4-grade factors, shape unchanged. (4) Cosmetic: the `(… : ℤ)` ascription in lamR is redundant (liouville n is already ℤ); harmless either way. Executors: re-grep all frozen names at dispatch (8 executors in flight on L2c* files; single-writer-on-names law, catch #245 am.1).

### overall

survives

## REFZ (refuter record)

### verdicts

(1) BOUNDARY BOTH SIDES — SURVIVES. Side A (wrongly-satisfying landed theorem): impossible. Every landed theorem is a closed prop P; for E := fun _ => P with P TRUE, TwinSufficient fails at a := twinFree (twinFree ∈ 𝒞(θ,A₀≤2) via L2/Salt.M5BigO.N5_3 [GROUNDED M5BigO.lean:294-295, verified; nat_absorb :227-229 gives explicit 25700]; twinMass twinFree ≡ 0 refutes ∀C∃x); with P FALSE, E oneWeight fails. So no closed prop witnesses Z — double-locked by L5 (Z→TPC at certified grades; no landed theorem implies TPC). Side B (wrongly-excluded route): impossible. L6's tautological witness E := fun a => ∀C ∃x, C < twinMass a x is TwinSufficient at EVERY grade with no hypotheses (verified: statement elaborates; E a IS the conclusion), so any TPC proof of any technique — bilinear/FI, exceptional-character, circle method — satisfies Z. M3 honored; pass2's no-go warning (fulcrum-pass2.md:~92) respected. Both attacks fail for the same reason: Z ⟺ TPC carries no methodological content — R3 declares this honestly; the content is the model class + L2 + L3. (2) VACUITY — SURVIVES WITH ONE REAL FINDING. Not over-strong (L6 grade-free). Not satisfiable-by-non-twin at certified grades θ∈(0,1/2), A₀≥0 (L5 via L1: per-d error ≤ ρ(d) ≤ d, Σ_{d≤x^θ}d ≪ x^{2θ} = o(x·log^{−A₀}x) — arithmetic checked). FINDING: at grades where oneWeight ∉ 𝒞 (plausibly θ=1, A₀=3), Z is TRIVIALLY satisfied by E := (· = oneWeight) — TwinSufficient vacuous, E oneWeight definitional. Z's docstring has no grade guard. Repair 2, not a kill: every commissioned lemma carries explicit θ<1/2 packets and R5 flags the range. (3) ORACLE LEAK — CLEAN, elaboration-verified: the frozen module compiles from Mathlib+Salt.Basic+Salt.Brun alone (Basic.lean is 32 pure lines, verified); no DirichletCharacter/LamTilde/L-function/¬F in any input. Characters appear only in L0-INSTANCE content (SiegelTwin.lean:129-131, verified) — the inside cone, which is the point. (4) DEMAND LEMMA — PLAUSIBLE AS STATED. Repo TPC verified ∀∃-shaped (Basic.lean:25-26: ∀n ∃p, n ≤ p ∧ p.Prime ∧ (p+2).Prime); twinMass oneWeight x = twin count on [1,x]; L4 is pure Finset/Nat.count arithmetic, A/B as priced. The M4 bridge (fulcrum-pass2.md:88, verified: "TPC ⟺ B(x)-unbounded-mod-dust... unlanded") is GENUINELY dodged — no Λ anywhere. Diff-6 claim TRUE. (5) OSSIFICATION — NONE. The only technique-shaped constraint (pure-Type-I class type) binds the BARRIER side; E reads a directly (Type-II expressible in the demand), and L6 admits every route. The M5 weld (fulcrum-pass2.md:82, verified) is in the correct direction. Residual (R4, honestly priced): ParityInv contains EVERY true closed prop — including TPC itself if ever proven — so cone membership of theorems is type-level, not arithmetic; the boundary bites only at predicate level. GROUNDING SWEEP: all cited names/lines verified against files — S1_le_S2 (HB/Transfer.lean:189-192; S1 is q-free, :176, so the design's P text is well-typed — elaborated), twin_bar (Impossibility.lean:173), twin_gate_fails (:262), no_twin_weight (:276), noSiegelZeros_iff_not_infinitely (SiegelTwin.lean:129-131), chen_headline (ChenTheorem.lean:32), twin_almost_prime (TwinInstance.lean:16 doc/:771 thm), N6_2 (N6.lean:231), Tao disclaimer verbatim (chowla.txt:196-200), no Salt.Parity collisions, twinRho/typeISum/ParityInv/TwinSufficient names fresh. KERNEL CHECK: frozen module + L0 (with the design's exact proof term) + L1-L6 statement shapes all elaborate via lake env lean --stdin (sorry-warnings only on the statement stubs). L2's 4-divisor argument verified sound (twin n ⇒ n(n+2) has exactly divisors {1,n,n+2,n(n+2)}; twinPrimeCounting def Brun.lean:19 matches). TWO ELABORATION-VERIFIED DEFECTS (repair 1): (a) the frozen import list cannot see N5_3 — Salt/Brun.lean does NOT import M5BigO (that path is Salt.Brun.All); (b) the name is Salt.M5BigO.N5_3, not bare N5_3 (namespace Salt.M5BigO, M5BigO.lean:25); likewise the L0 instantiations need corpus imports absent from the frozen list (Salt.HB.S1 unknown — reproduced). ONE MISATTRIBUTION (repair 3): fulcrum-pass2.md:37 (verified) PINS g ("g the twin singular-series density") — diff-1's "sketch quantified ∀g" is false as history; the freeze's pinning is faithful, the diff table is wrong. Diff-2's stated reason (Σρ(d) ≍ x log x) is upper-bound-shaped and does not PROVE θ=1 failure of the true sequence — non-membership needs a typeIError LOWER bound (fractional-part non-cancellation, C-grade, unproven; conclusion plausible — my check: error_p ≈ −({x/p}+{(x+2)/p}) for primes p, no cancellation, heuristically ≍ x/log x ≫ x/log³x). Nothing frozen depends on it. Diff-4's rationale overstated (the tautological witness is sign-insensitive, so signed classes never make Z unsatisfiable); the nonneg pin is still correct for barrier-side naturality and provably harmless (λ-biased weight 1−λ(n)λ(n+2) ∈ {0,2} ✓ nonneg; L5/L6 insensitive to the pin). Nits: L3's h1 : 1 ≤ A₀ and L1/L2/L3's h0 : 0 < θ are unnecessary hypotheses (harmless; L5 in fact holds at θ ≤ 0 too since the level window empties).

### repairs

R-1 (MANDATORY, elaboration-verified): fix the module's import/name plumbing. Z.lean must import Salt.Brun.All (or Salt.Brun.M5BigO) for L2's keystone — the frozen "Salt.Basic + Salt.Brun" list cannot see it; cite the keystone as Salt.M5BigO.N5_3 (namespace at M5BigO.lean:25), not bare N5_3. Put the L0 instantiations in a separate Salt/Parity/Instances.lean importing the corpus (Salt.HB.All, Salt.TwinBar.All, Salt.Chen.All, Salt.BrunLower.All, Salt.Brun.All) — verified working with qualified names Salt.HB.S1_le_S2, Salt.TwinBar.{twin_bar,twin_gate_fails,no_twin_weight,noSiegelZeros_iff_not_infinitely}, Salt.Chen.chen_headline (IsP2 is Salt.Chen.IsP2), Salt.BrunLower.twin_almost_prime, Salt.N6.N6_2; keep Z.lean's demand-spec module oracle-clean by NOT importing HB/TwinBar there (the clean-inputs claim then stays checkable by import list alone — recommend stating this as the module invariant). R-2 (MANDATORY, doc-level): grade-guard Z. At any (θ,A₀) with oneWeight ∉ Completion θ A₀, Z is trivially satisfied by E := (· = oneWeight) (TwinSufficient vacuous) — zero twin content. Docstring must say the demand-force is conditional on true-sequence membership (certified window θ ∈ (0,1/2), any A₀ ≥ 0); optionally land the A-class lemma Z_trivial_of_not_completion : ¬ Completion θ A₀ oneWeight → Z θ A₀ to make the degeneracy kernel-visible. Every downstream Z-claim carries the window (extends R5). R-3 (catch #224 diff-table corrections, before the freeze is banked): diff-1 rewrite — the pass2 sketch (fulcrum-pass2.md:37) already pins g to the twin singular-series density; the freeze's contribution is FORMALIZING it as twinRho d / d and foreclosing the ∀g misreading, not fixing a sketch bug. Diff-2 relabel — "true sequence fails its own norm at θ=1" is MEMORY/heuristic-grade (needs a typeIError lower bound via fractional-part equidistribution, C-class, unproven); the load-bearing fact is only that L1's route caps at θ<1/2 (crude ρ(d) ≤ d) resp. θ<1 (the τ² node) — the freeze correctly claims nothing at θ=1. Diff-4 relabel — rationale is barrier-side naturality, not TwinSufficient-satisfiability (which the sign-insensitive tautological witness protects at every grade). R-4 (writeup discipline, extends R1/R4): mandatory language — the parity boundary separates completion-PREDICATES, not theorems; every true closed proposition (TPC itself included, if proven) sits in ParityInv by L0, so inside-cone certificates are type-level facts; arithmetic insensitivity content lives only in the witness completions (L2) and the optional relativized-ceiling C-nodes. Nits (optional): drop L3's h1 and the unused h0's, or keep for interface fidelity — statement-text choice, no math risk.

### overall

survives-with-repairs

