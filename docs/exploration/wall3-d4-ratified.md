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
FROZEN Salt/Parity/Z.lean = DES-Z.definition text VERBATIM (twinRho, typeISum, typeIError, Completion, ParityInv, twinMass, TwinSufficient, oneWeight, twinFree, Z, ParityBarrier — the last lands as a def, stated never assumed) with amendments: J4 (R-1) imports = Mathlib + Salt.Basic + Salt.Brun.M5BigO ONLY (minimal; verified necessary); keystone cited qualified Salt.M5BigO.N5_3; MODULE INVARIANT: Z.lean never imports Salt.HB/Salt.TwinBar — oracle-cleanliness checkable by import list alone; L0 instantiations move to a separate Salt/Parity/Instances.lean. J5 (R-2) Z's docstring carries the grade guard: demand-force is conditional on oneWeight ∈ Completion θ A₀ (certified window θ∈(0,1/2), A₀≥0; outside it Z trivializes via E := (· = oneWeight)); plus commissioned lemma Z_trivial_of_not_completion : ¬ Completion θ A₀ oneWeight → Z θ A₀ [A]. J6: L3's h0/h1 hypotheses KEPT as frozen (no strengthening at Lean time). Commissioned nodes (shapes verbatim per DES-Z.lemma_shapes): L0 parityInv_of_closed [A] + instances [A, Instances.lean]; L1 oneWeight_mem θ<1/2 [B]; L2 twinFree_mem [B/C KEYSTONE, consumes Salt.M5BigO.N5_3] + twinFree_twinMass [A]; L3 sufficient_true_not_parityInv [B — THE GAP]; L4 twinMass_oneWeight_unbounded_iff [A/B]; L5 Z_implies_TPC [B]; L6 TPC_implies_Z [A]. NOT commissioned: τ²-density θ<1 extension [C, flagged follow-on]; ParityBarrier proof [D].

## BRIEFS

COMMON DOCTRINE BLOCK (every brief carries verbatim): model: "opus" (executor-model law); subagent_type = node name (agent-naming law); NO GIT — catch #244: no add/commit/push/branch/checkout, the conductor commits; working tree is the track branch prepared conductor-side. SINGLE-WRITER: you own exactly your one target file; edit NOTHING landed; All.lean/manifest lines wait for the conductor. Re-grep ALL cited corpus lines AND frozen names at start (catch #245 am.1; TCC drift ±1; 8 executors in flight on L2c* files). STATEMENTS LAND VERBATIM from the frozen set — no strengthening/weakening/renaming; packet-free lemmas stay packet-free; no (hf) added for uniformity (flags-wording guard l2c-freeze.md:146). `open Classical in` on every f-filter def (precedent TC:386/TF:177). ≤3 serious attempts per lemma, then STOP and return a flag report (node id, attempts, break point) to the conductor — do NOT edit flags.md (sole catch authority). Verify: lake build (no new warnings) + #print axioms ≤ [propext, Classical.choice, Quot.sound] via uncommitted Scratch.lean; no native_decide, no new axioms. Tools: Read, Bash (grep + ~/.elan/bin/lake), Write/Edit (own file only).

BRIEF W1 [B, volume-flagged] — file Salt/HB/SignChain.lean; import Salt.HB.L2cCore; namespace Salt.HB. Land DES-W §W1 frozen set: IsSignFunction packet + 12 defs + ~24 theorems + the TCC:89-161 helper block. Substitution table: chiRe_mul χ hsq ↦ hf.map_mul; chiRe_one ↦ hf.map_one; chiRe_abs_le_one ↦ hf.abs_le_one; chiRe_eq_one_or_neg_one ↦ hf.prime_pm (hypothesis-FREE — erases every downstream hcop). Keep Real.log ((n / d : ℕ) : ℝ) exactly (ℕ-division, TC:99). gGen map_zero' by simp — explicit term if simp regresses. Order: defs first (the §defs milestone unblocks W2), then TC mirrors, TCC mirrors (re-grep each line), Transfer layer, window+caps, counters. DO NOT re-type: χ-free KC1 layer (consume as-is); bypassed TR:60-71 + TF majorant chain. "KC1 already discharged" does NOT cover the LamTilde/Transfer layer — no skipping.

BRIEF W2 [A/B] — file Salt/HB/SignLiouville.lean; import Salt.HB.SignChain. GATE: dispatch once W1 defs + LamTildeGen_eq_conv compile. Land the 9 frozen decls. Route pins: liouville_apply needs n ≠ 0 (Liouville.lean:31); liouville_apply_mul :40 unconditional (one cast for map_mul); μ²λ=μ via Squarefree split (Moebius.lean:60/64, plus d=0); THE POLE via moebius_mul_log_eq_vonMangoldt (VonMangoldt.lean:130) — NOT sum_moebius_mul_log_eq (:133, wrong shape); S2Gen_lamR_eq_S1 by Finset.sum_congr + pole; PretenseSumGen zero via everywhere-false filter (lamR_prime gives −1 ≠ 1).

BRIEF W3 [B given W1] — file Salt/HB/SignRate.lean; import Salt.HB.SignChain. GATE: W1 landed. Land EngineBound (transcribe EXACTLY — refuter-checked text in the ratified set; rpow discipline on 1/8 and 9/10) + neutrality_rate with the J2 docstring line. Proof: left conjunct = sub_nonneg.mpr (S1_le_S2Gen hf _); right = rw [S2Gen_sub_S1_eq]; exact hbudget. Then append the J1 COMMENT-FROZEN hb_l2c_masterGen docstring block verbatim — NO declaration, NO sorry, NO attempt.

BRIEF D4-a [A/B] — file Salt/Parity/Z.lean; imports Mathlib, Salt.Basic, Salt.Brun.M5BigO ONLY (module invariant: never import Salt.HB/Salt.TwinBar); namespace Salt.Parity. Land all 11 frozen defs (J4/J5 docstrings included) + L0 parityInv_of_closed [A] + L4 bridge [A/B; pure Finset/Nat.count vs TPC Salt/Basic.lean:25-26] + L6 TPC_implies_Z [A; tautological witness E := fun a => ∀C ∃x, C < twinMass a x] + Z_trivial_of_not_completion [A]. rpow not pow for Real.log x ^ A₀ (GEH-FIX catch).

BRIEF D4-b [B/C KEYSTONE] — same file, SEQUENCED after D4-a (single-writer: one executor on the file at a time; conductor hands off). Land L1 oneWeight_mem [B: per-d error ≤ ρ(d) ≤ d; Σ_{d≤x^θ} d ≪ x^{2θ} = o(x·log^{−A₀}x)] + L2 twinFree_mem [B/C: per-d diff ≤ 4·twinPrimeCounting x via the 4-divisor argument {1,n,n+2,n(n+2)}; consume Salt.M5BigO.N5_3 (M5BigO.lean:295) with an x₀-split absorbing atTop into the ∃C ∀x≥2 slot] + twinFree_twinMass [A]. If the absorption turns C-shaped: STOP+flag; do not improvise a weaker statement.

BRIEF D4-c [B] — same file, after D4-b. Land L3 sufficient_true_not_parityInv [B: ParityInv → E twinFree; TwinSufficient + L2 → twinMass twinFree unbounded; companion says ≡ 0] + L5 Z_implies_TPC [B via L1+L4]. Keep h0/h1 hypotheses AS FROZEN (J6 — no trimming).

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
