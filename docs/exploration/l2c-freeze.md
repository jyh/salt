# THE HB-L2C FREEZE (judge-final, 2026-07-19 04:15 PT; shiu-native + all repairs; EXECUTION-COMPLETE, no class D)

## VERDICT

shiu-native (exact-overshoot surgery) with ALL verified repairs from both its refuter passes applied (T2 modulus law via >=z-cofactor; T-sw swap family for the missing S2^4 block; (c)-junk repriced x/z^{1/8}; Z_f := floor(x^{1/48}) healing the 100-gate; explicit even-block e-split; Aexp=5). Faithful REJECTED as spine: its verbatim-hres discharge survives only with drifting witnesses and x^{1+eps} junk_V dumps (refuter-confirmed), i.e. vacuous-grade, at ~3x the line cost; hb_lemma2 has zero landed consumers (grep-verified this pass: All.lean:34 manifest only), so bypassing hres strands nothing. Both candidates independently confirm the operative verdict: the tau-crude majorant slot is dead for Horn A at FulcrumQualityMin; the live export is the absolute-Cmain sharp/exact conclusion — shiu-native's hb_l2c_master IS that export, proven directly.

## THE FREEZE

# HB-L2C FREEZE (JUDGE-FINAL): exact-overshoot surgery, all refuter repairs baked

CHOSEN: shiu-native + repairs R-F1..R-F4 (both refuter passes) + faithful grafts.
hres (TransferFull.lean:204-214, verified verbatim this pass) is BYPASSED, not filled:
undischargeable at constant witnesses (Wall A: minus-prime family, majorant ~
(x/L)PS*z0*loglog z, Euler-factor (log z)^2-grade over slot ceiling; Wall B: both-prime
pairs, majorant 12L^2/pair, truth 0, pricing = Class D). hb_lemma2 has ZERO landed
consumers (grep: All.lean:34 manifest only) — bypass strands nothing. We prove
hb_lemma2's CONCLUSION shape verbatim on the exact identity instead.

## S1 TARGET (interface = hb_lemma2 conclusion, verbatim)

W := l2cWindow chi z x := (Ioc x (2x)).filter (fun n => Nat.Coprime (n*(n+2))
(q * excPrimorial chi z)) [G8: CoprimeSupport via coprimeSupport_window Transfer.lean:223
+ dvd_mul_right; per-element excPrimorial-coprimality via Coprime.coprime_dvd_right feeds
the PARAMETRIC S2_sub_S3_window StarWindow.lean:393 — ONE window serves WP3].
z0 := Real.log(2x+2)/Real.log z; L' := log(2x+2).

THEOREM hb_l2c_master (chi hsq) (z x : Nat)
 (hz100 : 100^16 <= z) (hz8 : (Real.log(2x+2))^8 <= z) (hzx : (z:R)^3 <= x) :
 EXISTS Cmain > 0 ABSOLUTE: S2 chi W - S1 W
  <= Cmain*(x/z0) + Cmain*(x/Real.log x)*Real.exp(5*z0)*PretenseSum chi (2x+2) + junkExpr,
 junkExpr := Cmain*Real.exp(2*z0)*(x/(z:R)^(1/8:R) + (x:R)^(9/10:R))*L'^3.
[Repairs baked: hyp-set => x >= 100^48 (heals sqrt(x)L'^2 <= x^{9/10}); junk x/sqrt z ->
x/z^{1/8}; Aexp=5.] Downstream (z = q^{1/z0*}, x in [q^250,q^500]): hyps trivial, junk o(x).

## S2 CORE SURGERY

overshootExact chi n := (Lt(n)-Lam(n))*Lt(n+2) + Lam(n)*(Lt(n+2)-Lam(n+2)) [Lt = LamTilde].
S2-S1 <= Sum_{n in W} overshootExact (export the hid ring identity, Transfer.lean:163-165).
Lt-Lam = 0 at primes / 1 / pure chi=-1 prime powers (TwistChainC :121/:268; f(1)=1);
= 0 when omega(n_minus) >= 2 (:252). => both-prime pairs contribute 0 (Wall B dead);
prime class dead (Wall A dead). Support: n composite AND (n_minus=1 OR (IsPrimePow n_minus
AND 1 < n_plus)). Window caps: every chi!=-1 prime of n(n+2) is >= z => 2^omega(n_plus)
<= e^{(log2)z0} (G7 dissolved); Lt(m) = f(m_plus)*Lam(m_minus) single-block (:268),
<= e^{(log2)z0}*L' all-plus (:293); f = 2^omega on all-plus via :67 + nPlus_sign :111.
Parity: n even iff n+2 even; blocks odd unless chiRe(2)=-1 with both 2-powers.

## S3 COUNT ENGINE

hb_lemma8'_unconditional (MixedCount.lean:609-616; NOTE extra arg hZ1 : 1 <= Z; sifts the
PRODUCT of both cofactors; Odd d1 d2, Coprime d1 d2): card <= 64(d1d2/phi)^2(x/(d1d2))
/(log Z)^2 + 2Z^8. Clean form l2c_pair_count_clean: d1d2*Z^8*(log Z)^2 <= 32x =>
<= 128(...)/(log Z)^2. Z_z := floor(z^{1/16}) (100 <= Z_z from hz100); Z_f :=
floor(x^{1/48}) (100 <= Z_f from hz100+hzx — REPAIR: was 1/68, gate undischargeable).
chi-counters: PS-conv Sum_{z<=p<=N,chi=1}1/p <= z0*PS/L'; chebyshev_chi #{p in Ioc a b,
chi=1} <= (b/log a)*PS; Mertens sum_vonMangoldt_div_le (Maynard/Mertens.lean:97; Ioc 0 N
IS the pp-sum), sum_log_div_prime_le :152. ShiuCore NOT consumed (de-scoped).

## S4 FAMILIES — E_L = Sum(Lt-Lam)(n)*Lt(n+2) [n+2 = w*m single-block, w<z chi=-1-pp or 1]

T1 [n_plus=P prime, m=U prime, blocks v,w < z, v>1, odd]: fibers (v,w) at Z_f; cofactors
P,U > sqrt x rough at any Z < sqrt x; weights 4*Lam(v)Lam(w) (w=1: *log U <= L'); clean
legality z^2 x^{1/6} L'^2 <= 32x OK; budget C*x/z0^2 + C*x/z0 -> J1, NO PS ((3.3) reborn).
T2 [n_plus composite] REPAIRED LAW: n_plus = p'*c, p' = minFac(n_plus), c >= z =>
d1 := v*p' = n/c <= 2x/z. w-routing (= T3's): w <= z^{1/4} into modulus [law
(2x/z)z^{1/4} = 2x*z^{-3/4}; legality z^{1/4} >= (log z)^2/4096 from hz100];
w in (z^{1/4},z] prime or pp-base > Z_z -> cofactor route; small-base squarefull ->
(c)-junk. PS from Sum 1/p' <= z0*PS/L'. Budget <= C*x*z0^3 e^{1.4z0} PS/L' -> J2.
T3 [n_plus=P prime, v >= z prime; v pp e>=2 -> junk]: P <= 2x/z; d1 := P (PS via Sum 1/P);
d2 := w if w <= z^{1/4} else 1 (same w-routing); modulus <= 2x*z^{-3/4};
budget <= C*x*z0^3 e^{0.7z0} PS/L' -> J2.
T-sw [NEW — repairs the missing S2^4 block: n_plus=P prime, 1<v<z, w >= z, m=U prime]:
d2 := U <= (2x+2)/z (chi=+1 prime modulus; PS via Sum 1/U); d1 := v if v <= z^{1/4} else 1
(v in (z^{1/4},z] pp-base > Z_z -> cofactor; squarefull small-base -> (c)-junk); cofactors
P > x/z >= z^2, w >= z, both Z_z-rough; weights 2Lam(v)*2L'; budget C*x*z0^2 e^{0.7z0}
PS/L' -> J2.
[n_plus=P prime, v<z, m composite]: p'' := minFac(m), d2 := w*p'' = (n+2)/c' <= (2x+2)/z —
T2-mirror with the repaired law.
CORNERS: even-blocks (chiRe(2)=-1: v=2^e iff w=2^{e'}): e-split EXPLICIT — 2^e <= sqrt x:
chebyshev_chi at a >= sqrt(x)-grade -> 8x*PS/L'; 2^e > sqrt x: crude <= 4*sqrt x + L'
terms -> junk. m=1 (pure-pp n+2) -> junk; squarefull blocks >= z: <= 4x/sqrt(z)*caps ->
junk; v or w > x^{1/4} -> x^{3/4}*caps junk. (c)-JUNK (smallest-index for ALL w/v-routing,
priced FIRST): small-base (<= Z_z) pp in (z^{1/4},z], e >= 2: Sum_{p<=Z_z, p^e>z^{1/4}}
x/p^e <= 4x*z^{-1/8} -> junkExpr's x/z^{1/8} term (REPAIR: x/sqrt z too narrow by z^{5/16}).

E_R = Sum Lam(n)*(Lt-Lam)(n+2): n = p^k; k>=2 -> junk (<= 2*sqrt(2x)*L'^2 e^{0.7z0});
k=1: left weight log p <= L', right = T1/T2/T3/T-sw roles swapped — RESTATED, not
symmetry-hand-waved; both-prime pairs vanish exactly.

BUDGET LAW: J1 = Cmain*x/z0 (absolute, never e^{z0}); J2 = C(x/L')e^{5z0}PS
(z0^3 e^{1.4z0} <= e^{4.4z0} <= e^{5z0}); junkExpr explicit. Class D: NONE.

## S5 FILES/WAVES (single-writer by FILE; no landed-file edits; ~1230 ln)

W1 Salt/HB/L2cCore.lean [~470]:
 R1 [B] overshootExact + S2_sub_S1_exact + vanishing lemmas + support classification.
 R2 [B] l2cWindow + CoprimeSupport glue + roughness/omega/Lt caps + parity.
 R3 [C] l2c_pair_count + _clean + Z_z/Z_f wrappers (gates from hz100/hzx).
 R4 [B] PS-conversion, chebyshev_chi, Mertens re-exports.
W2a Salt/HB/L2cEL.lean [~380]: R5 [C] EL_T1/T2/T3/T-sw/corners ((c)-junk priced first).
W2b Salt/HB/L2cER.lean [~200]: R6 [C] ER mirrors + k>=2 junk. [W2a PARALLEL W2b]
W3 Salt/HB/L2cMaster.lean [~180]:
 R7 [B] junk ledger + exact_overshoot_bound (collect J1/J2/junkExpr).
 R8 [B] hb_l2c_master + S1/S2-preservation glue (vonMangoldt_le_LamTilde) + module doc
 + All.lean manifest lines (W3 only). + flags.md entry (frozen text): "hb_lemma2/hres =
 over-reduction: the tau-crude majorant is L^2-inflated at the worst pattern (chi=+1-prime
 class, floor 8L^2*R_A; provability-level — the concentration pattern is unexcludable by
 the pattern-blind L2c toolkit; note q=3 degeneracy majLogL == 0); at FulcrumQualityMin
 any verbatim chain forces log eta >~ L^4. Superseded by hb_l2c_master (same conclusion
 shape, exact identity); hb_lemma2 stays green, zero consumers."

## S6 GLUE RUNGS (Horn A end-to-end; fulcrum_audit_glue.md; B-class, audited thin)

W4 Salt/Fulcrum/HornAGlue.lean [~250]:
 G1 [B] twin_door_unbounded : (ALL n, EX x >= n, 0 < p1PrimeSum x 1) -> TwinPrimeConjecture
  — twin_survivor_of_pos (TwinBar/TwinDoor.lean:204-223) + the Chen ALL-X-EX plumbing
  template (Chen/Assembly.lean:425-440, Set.infinite_of_forall_exists_gt).
 G2 [B] fulcrum->(1.11) bridge: FulcrumQualityMin C (Fulcrum/Basic.lean:61-64) =>
  ALL Q EX q>Q (chi,beta): eta >= C; window x in [q^250,q^500], z := q^{1/z0*}, z0*
  CONSTANT with the two-named-constants discipline (z0*-choice const < 1/6 vs Lemma-3's
  (log eta)^{-1/2}); hb_l2c_master hyps trivial at large q.
 G3 [B] WP1 o WP2 composition: hb_l2c_master + WP2 Lemma-3 export (PS <= C*L(log
  eta)^{-1/2}) + S(3) main-term chain on the SAME l2cWindow (S2_sub_S3_window parametric)
  => 0 < S1 W per window => carrier bridge to p1PrimeSum (or survivor extraction on S1's
  own carrier) => G1's hypothesis. Consumes quantity (ALL-Q-EX-q) exactly once.
  [Name-parametric on WP2's final export names — see open_risks.]

## S7 EXECUTION GOTCHAS (verified this pass or by refuters)

hZ1 : 1 <= Z extra arg on hb_lemma8'; sifting is on the PRODUCT of cofactors (drives
T-sw/(c)-routing); TwistChainC line numbers +-1 — re-grep before citing; excPrimorial =
prod_{p<z, chiRe(p)!=-1} p incl. p=2 clause (StarWindow.lean:72-73); ShiuCore's z-arg is
the window top, NOT sieve-z (naming hazard); Lambda-lower Mertens NOT in repo
(grep-verified) and NOT needed (faithful's M1 dropped); dispatch model: "opus",
subagent_type = node name; commit on track branch, never main.

## GRAFTS

- faithful/flags discipline: provability-level wording, q=3 degeneracy (majLogL == 0), 8L^2*R_A floor (not 16L^2) — folded into the frozen W3 flags text
- faithful/downstream death verdict: any verbatim-hres chain forces log eta >~ L^4 at FulcrumQualityMin (eta >= C constant, ledger W2) — the recorded reason the sharp/exact export is the sole Horn-A vehicle
- faithful/two-named-constants z0 discipline (z0*-choice constant < 1/6 vs Lemma-3's (log eta)^{-1/2} balance; source-map hazard S11.2) — baked into glue rung G2
- faithful/M1 retirement: Chebyshev-LOWER Mertens grep-verified absent from repo AND unconsumed by the chosen route — dropped, removing the one flagged supplier C-risk

## OPEN RISKS

- RATIFICATION: the hres supersession + Horn-A consumption switch is a statement-layer, blueprint-adjacent move (additive only — hb_lemma2 stays green, zero consumers grep-verified). Flags text is frozen in W3's spec; needs JYH sign-off before any merge toward main (branch work unblocked per commit policy).
- FLAGS WORDING GUARD: Walls A/B are worst-pattern PROVABILITY claims, not truth-level lower bounds (Siegel-pattern existence open; q=3 pattern empty). W3 must land the frozen wording verbatim — no strengthening at Lean time.
- R5/R6 COVER COMPLETENESS: both refuters closed the family list against HB's L2/L3/L4 partition post-repair (T-sw added, (c)-junk routed), but a Lean-time disjoint-cover proof may surface a micro-subclass; +100-line contingency budgeted; any needed STATEMENT change => STOP and flag (iron rule 1), do not improvise witnesses.
- W4 GATE: G3 is name-parametric on WP2's Lemma-3 export and the S(3) main-term chain names (glue audit 2026-07-18 lists the WP2 endgame in flight); dispatch W4 only after those exports are green — W1-W3 have no such dependency.
- MERGED-TEXT VERIFY POSTURE (catch #98): each candidate got refuter passes, and every repair baked here is refuter-derived and cross-checked, but no third pass ran on the MERGED S4 branch table as a whole; a cheap parallel refuter on S4 alone is warranted if quota allows before W2a dispatch (W1 is unaffected).
- MINOR SCOPE-DIFFS: fChiArith_eq_two_pow's exact hypothesis shape and TwistChainC +-1 line drift affect only cap constants; executors re-grep cited lines before use (catch #224 hygiene).

## EXECUTOR NOTES

WAVE-1 BRIEF SKELETON (dispatch now; model: "opus"; subagent_type: "hb-l2c-core"; one executor, one file). FILE Salt/HB/L2cCore.lean (new; touch NO landed file, All.lean manifest waits for W3). Imports: Salt.HB.TransferFull, Salt.HB.MixedCount, Salt.HB.StarWindow, Salt.Maynard.Mertens. DELIVERABLES: R1 — def overshootExact chi n := (LamTilde chi n - Lambda n)*LamTilde chi (n+2) + Lambda n*(LamTilde chi (n+2) - Lambda (n+2)); theorem S2_sub_S1_exact (hsq) (hA : CoprimeSupport q A) : S2 chi A - S1 A <= Sum_{n in A} overshootExact chi n [per-term ring identity — mirror Transfer.lean:163-165 + LamTilde_nonneg + vonMangoldt_le_LamTilde]; vanishing: LamTilde_sub_vonMangoldt_eq_zero_of_prime / _of_one / _of_pure_minus [TwistChainC :121 divisor collapse, :268 single-block with f(1)=1, :252 two-block kill]; overshootExact_support_classification (nonzero => n composite AND (n_minus=1 OR (IsPrimePow n_minus AND 1 < n_plus))). R2 — def l2cWindow (filter Coprime (n*(n+2)) (q*excPrimorial chi z) on Ioc x (2x)); l2cWindow_coprimeSupport [coprimeSupport_window Transfer.lean:223 + dvd_mul_right]; l2cWindow_roughness (chi!=-1 prime of n(n+2) => >= z; mirror excSq_ge_z_of_window StarWindow.lean:79, confirm excPrimorial def at :72-73 incl. p=2 clause); l2cWindow_omega_cap (2^omega(n_plus) <= Real.exp((Real.log 2)*z0), z0 := log(2x+2)/log z); lamTilde_cap_single_block (:268 + fChiArith_eq_two_pow :67 + nPlus_sign :111 — re-grep exact lines/hyps first); lamTilde_cap_all_plus (:293); l2cWindow_parity_link. R3 — l2c_pair_count (fiber subset baseSet PairInstance.lean:64 -> hb_lemma8'_unconditional MixedCount.lean:609-616; REMEMBER both hZ : 100 <= Z and hZ1 : 1 <= Z; Odd d1, Odd d2, Coprime d1 d2 side conditions; sifts PRODUCT of cofactors); l2c_pair_count_clean (hyp d1*d2*Z^8*(log Z)^2 <= 32*x, conclusion 128-form); wrappers lemma8'_Zz at Z := floor(z^{1/16}) [gate: 100 <= Z_z iff z >= 100^16 = hz100 exactly] and lemma8'_Zf at Z := floor(x^{1/48}) [gate from hz100+hzx: x >= 100^48]. R4 — sum_inv_plusprime_le_pretense (Sum_{z<=p<=N, chiRe=1} 1/p <= PretenseSum chi N / Real.log z; PretenseSum TransferFull.lean:183-185, termwise log p/p >= (log z)/p); chebyshev_chi_count (#{p in Ioc a b, prime, chiRe=1} <= (b/Real.log a)*PretenseSum chi N via log p <= b*log p/p); re-export sum_vonMangoldt_div_le (Maynard/Mertens.lean:97) + sum_log_div_prime_le (:152). VERIFY: lake build clean (no new warnings); #print axioms on every new theorem (must be within propext/Classical.choice/Quot.sound; no native_decide); commit on the track branch (NEVER main) msg "hb-l2c W1: L2cCore lands (R1-R4)" + model + attempt count. RULES: helpers inherit B/C class — if one feels D-shaped STOP and flag (docs/blueprints/flags.md); do not alter any frozen statement; budget ~3 serious attempts per rung then flag. WAVE 2 SKELETONS (dispatch after W1 green; two parallel executors): W2a "hb-l2c-el" Salt/HB/L2cEL.lean — EL_T1_bound, EL_T2_bound (REPAIRED law d1 = n/c <= 2x/z via >=z cofactor; w-split at z^{1/4}), EL_T3_bound, EL_Tsw_bound (NEW family), EL_corners_bound (even-block e-split at sqrt x; (c)-junk 4x*z^{-1/8} priced FIRST; m=1, squarefull, >x^{1/4} corners); per-family budgets and modulus laws verbatim from freeze S4. W2b "hb-l2c-er" Salt/HB/L2cER.lean — ER_squarefull_junk (k>=2, <= 2*sqrt(2x)*L'^2*e^{0.7z0}) + ER_T1'/T2'/T3'/Tsw' with roles swapped, restated in full. WAVE 3 "hb-l2c-master" Salt/HB/L2cMaster.lean — exact_overshoot_bound + hb_l2c_master + S1/S2-preservation glue + All.lean manifest + the FROZEN flags.md text (verbatim from freeze S5; no rewording). WAVE 4 "horna-glue" Salt/Fulcrum/HornAGlue.lean — G1/G2/G3 per freeze S6; GATED on WP2 export names being green; twin_survivor_of_pos at TwinDoor.lean:204-223, plumbing template Chen/Assembly.lean:425-440. Chime protocol on wave completions; PushNotification suppressed while JYH at terminal.

## HOUSE AMENDMENTS (Fable ruling, 2026-07-19 06:20 PT — catch #245)

The T3 executor surfaced the freeze's own R5/R6 COVER-COMPLETENESS
open risk as a concrete statement-layer under-specification: the
natural family filters (no structure condition on the z^{1/4}-routed
block) CONTAIN the small-base squarefull corner terms — blocks
m = p^e with p prime, p ≤ Zz z, e ≥ 2, (z:ℝ)^{1/4} < m ("junk
blocks") — which cannot fit the J2 row (PretenseSum may be
arbitrarily small) but total ≤ e^{c·z0}·L'²·x·z^{−1/8} (per-p
geometric tails, ≤ Zz primes, Σ ≤ 2z^{−3/16} ≤ z^{−1/8}), i.e.
exactly the junkExpr shape. THE RULING (forced, not discretionary):

1. **Every family slice carries the inline guard** ¬junkBlock on
   whichever block that family routes at z^{1/4} (E_L: T2/T3 guard
   w = (n+2)₋, Tsw guards v = n₋; E_R mirrors: roles swapped).
   Guard stated INLINE per family with a family-prefixed local
   predicate (no shared def across in-flight files — the
   single-writer law extends to names); W3 reconciles via trivial
   iff-lemmas.
2. **The junk row owns the excluded class on BOTH sides of BOTH
   sums**: EL_cJunk_bound extends to (v-junk ∨ w-junk), and the
   E_R w-side corner gets its own row ER_wJunk_bound (junkExpr
   shape); L2cELJunk may import Salt.HB.L2cER for it. Conclusion
   shapes UNCHANGED (constants absorb the factor 2).
3. **Sift-floor correction (T3 catch 2, proof-layer, broadcast):**
   where a fibration's cofactor is only guaranteed ≥ z (or
   ≥ z^{1/4}), sift at Zz = ⌊z^{1/16}⌋, NOT Zf — in-regime
   Zf = ⌊x^{1/48}⌋ may EXCEED z, making a Zf-sift unsound.
   Legality at Zz holds comfortably (d₁d₂·Zz⁸(log Zz)² ≪ z³ ≤ x).
   Zf remains correct where cofactors are genuinely ≥ Zf.
4. T3 catch 1 recorded as confirmation: the crude capped route
   provably diverges from J2 by z0·L'²·e^{−4.3z0} → ∞ in-regime —
   the sharp single-block cap + weighted pair-count fibration are
   mandatory. The freeze's design is vindicated, not repaired.

## HOUSE AMENDMENT 2 (Fable ruling, 2026-07-19 08:50 PT — catch #246)

F-junk surfaced the second cover gap: when χ_ℝ(2) = −1 the window
admits EVEN elements (2 ∉ excPrimorial by its def, StarWindow :72),
whose χ=−1 blocks 2^e ≤ z^{1/4} are neither junk (fail the z^{1/4}
threshold) nor family-eligible (the engine needs odd moduli). THE
RULING: (1) **all family slices guard n ODD** (one predicate; by the
parity link n even ⟺ n+2 even this excises the whole class from
both sums; landed files needing no rework: M-T3's junk guard already
excises its even corner since IsPrimePow w ∧ z ≤ w forces w = 2^e
junk; M-Tsw's landed rows are unconditional/parity-blind — but the
future hcount discharge must handle or excise even w, filed under
HB-L2C-CHI-SIEVE). (2) **THE EVEN-CORNER ROW** (sixth line,
EL_evenCorner_bound): the even class of BOTH overshoot summands,
frozen conclusion = the corners shape Cmain·exp(2·z0)·x^{9/10}·L'³.
House-verified route: even survivors have BOTH n₋ = 2^{e₁} and
(n+2)₋ = 2^{e₂} pure (the two-block kill applies on each side —
any odd χ=−1 block alongside 2^e kills Λ̃), so both weights ≤
e^{(log2)z0}·log2; count per (e₁,e₂) fiber (e₂ ∈ {1, free-at-e₁=1})
via l2c_pair_count_clean at (d₁,d₂) = (1,1) sifted at Zz (cofactors
z-rough by l2cWindow_roughness hence Zz-rough; legality trivial);
geometric Σ over e gives ≤ C·z0²·x/L'² which fits the x^{9/10} line
absolutely (z0²e^{2log2·z0} ≤ 25e^{2z0}; x^{1/10} ≥ L'² from
hz100/hzx). NO PretenseSum — the class is character-blind; the
freeze's old √x-chebyshev sketch is superseded.

## HOUSE AMENDMENT 3 (Fable ruling, 2026-07-19 09:55 PT — catch #247)

M-T1 refuted the frozen ER_T1'_bound J1 shape AT TRUTH LEVEL
(principal χ counterexample: the all-plus class contains the
primes p with p+2 = QR, Q,R ≥ z — Λ̃ exponential in ω, mass
x·log z0 ≫ x/z0 at the z ≍ L'⁸ packet corner). Provenance: the
roles-swap orphaned the composite-plus-part class (w = 1,
(n+2) composite all-plus) into J1, where E_L routes its analogue
through T2's J2 row — the R6 cover risk realized a second time.
THE RULING (the executor's recommended repair, adopted verbatim):
**ER_T1'_bound is REPLACED by the landed ER_T1'_bound_mixed** —
the exact-cover split ER_T1'_split with (a) the pp-slice ≤ 4·(x/z0)
(true J1) and (b) the composite slice ≤ 2^19·(x/L')·e^{5z0}·PS
(the exact J2 row shape). W3's ledger absorbs it with budget
shapes UNCHANGED: the pp part sums into the J1 line, the
composite part into the J2 line. No other row affected. The
freeze's W3 assembly spec is amended accordingly: the E_R
all-plus row contributes to BOTH ledger lines.

## HOUSE AMENDMENT 4 (Fable ruling, 2026-07-19 11:40 PT — catch #248;
SUPERSEDES Amendment 2's even-row conclusion and route)

The even-corner executor refuted Amendment 2's frozen x^{9/10} shape
on three independent grounds (all house-verified): (1) the
absorption inequality was written BACKWARDS (x^{1/10} ≥ Lwin² gives
x^{9/10} ≤ x/Lwin², not the needed direction); (2) the (1,1)/Zz
pair-count route is unsound for even n (the engine's primorial
coprimality contains 2 — even fibers do not embed at all); (3) truth
level: survivors n = 2^{e}·(χ=+1-rough) carry Hardy–Littlewood-grade
x/polylog mass ≫ x^{9/10}. The class is NOT character-blind. THE
RE-FROZEN ROW (the pre-Amendment-2 J2 intuition, now with a
house-verified route):
`EL_evenCorner_bound : evenCornerSum χ z x ≤ Cmain·((x:ℝ)/Lwin x)·
Real.exp (5·z0 z x)·PretenseSum χ (2x+2) + Cmain·Real.exp (2·z0 z x)
·((x:ℝ)/(z:ℝ)^(1/8:ℝ))·(Lwin x)^3` — J2 + standard junk, Cmain
absolute. Route (house-verified arithmetic, NO pair-count engine —
crude divisor counting only): by the landed evenCorner_survivor +
exponent split, fiber on e₁ (resp. e₂); the odd cofactor m = n₊ > 1
is z-rough with all prime factors χ_ℝ = +1 (window q-coprimality
kills χ_ℝ = 0); pick p | m, p ≥ z, χ=+1; count multiples of 2^{e}·p
in (x, 2x] crudely (≤ 2x/(2^e p) + 1); Σ_p 1/p → PretenseSum/log z =
z0·PS/Lwin via sum_inv_plusprime_le_pretense; Σ_e 2^{−e} ≤ 1; the
weight e^{2z0}·2z0 ≤ e^{5z0}. The +1 tail: p ≤ 2x/2^e and p ≥ z ⟹
≤ 2x/(2^e z) values ⟹ Σ ≤ 2x/z ≤ x/z^{1/8} junk. The n₊ = 1 corner
(n a pure 2-power): ≤ Lwin terms ≤ e^{2z0}·Lwin — junk-absorbed.
W3 LEDGER NOTE: the even row contributes to the J2 and junk lines
(NOT an x^{9/10} line). Composes with the landed
evenCornerSum_le_survivor_card layer.

## HOUSE AMENDMENT 5 (Fable ruling, worst-corner-passed; catch #252)

L2c-mop landed class (b) (L2cMid_bound, junk row at coeff 1, huge
headroom) and surfaced: (i) CLASS (c) — n₊ prime ∧ n₋ = v pp < z ∧
n+2 = q a single χ=−1 prime ((n+2)₊ = 1) — real, nonzero
(2Λ(v)·log q), escapes all six slices + (a) + (b); its sharp pricing
is CHI-SIEVE-shaped (both q-primality and P-χ needed), BUT the
crude chebyshev route closes IN THE RESTRICTED REGIME; (ii) the
coeff-1 J2 line of hEL_uncov is unreachable (class (a) mirrors
EL_T2's 17915904). THE RULING: (1) new packet hypothesis
`hLz0 : Lwin x ≤ Real.exp (z0 z x)` — excludes only the
intermediate regime (z ≈ x^{1/3}, z0 ≈ 3); trivially true at the
downstream instantiation (z0 ≥ 250-grade), so the Horn A glue is
unaffected. Under hLz0, class (c) closes at C = 8 on the J2 line:
per-v count via chebyshev_chi_count (P = n/v is the χ=+1 prime ≥ z,
range 2x/v, floor log z), weight e^{(log2)z0}·Λ(v)·L' via
lamTilde_single_block_le, Σ Λ(v)/v ≤ 2 log z; total
8x·L'·PS·e^{z0} ≤ 8·(x/L')·e^{5z0}·PS ⟸ 8L'²e^{z0} ≤ 8e^{4z0}·e^{z0}
⟸ L'² ≤ e^{4z0} (hLz0, z0 ≥ 3 from hzx). WORST-CORNER PASSED:
z0 ≥ 3 forced by hzx; the chain holds at every packet corner.
(2) hEL_uncov's J2 coefficient re-tallied 1 → 2^26 (mirror ~2^25 +
class (c) 8 + margin); the landed master's hypothesis is amended
accordingly (house-authorized statement edit, #247 precedent);
Cmain = 2^31 SURVIVES the re-tally (J2 total ≈ 1.1e8 ≪ 2^31).
(3) mop-2 lands: the amended hypothesis, class (a) via the
EL_T2-mirror fibration, class (c) as above, EL_uncov_bound (hLz0)
composed, and the corollary hb_l2c_master_final (hLz0 + hcount
only). The freeze's residual taxonomy is (a) ∪ (b) ∪ (c), closed.
