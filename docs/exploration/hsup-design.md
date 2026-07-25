# THE hSUP BLOCK — the pointwise ball sup (the T1 seam's first named binder)

*Maestro design block, 2026-07-25 afternoon. Status: DRAFT — HSUP-SCOPE
dispatched on the central pages BEFORE any freeze (the socket/supply lesson
of last night is carved above this door: `halasz_ball_decay` is a scalar
shuffle, not a supply; nothing below claims a supply it has not exhibited).*

## The object

SeamSplit's `prop_A3_T1_row_split` consumes
  hSup : ∀ t, |t − t₁| ≤ r → ∀ m ≤ N, ‖A_t(m)‖ ≤ S·m,
A_t(m) = Σ_{n≤m} aₙ n^{−it} (hsupp kills n ≤ X; effectively the dyadic
partial sums), t₁ ∈ M_range's window with dist² < M_range + 1, r =
(logX)^{1/16}. The needed grade: S ≍ e^{−cM} + (logX)^{−1/2+ε} (MRT A.7's
shape) — the ball leg then delivers 2r(2S)² ≍ (logX)^{1/16}e^{−2cM} + …,
the e^{−M} main term of prop_A3′. **This is MRT Lemma A.6/A.7 — the
pointwise Halász bound at ball frequencies — the last genuinely classical
unlanded piece of the T1 chain.**

## Why there is no dodge (the honest walls, named up front)

- **The L² dodge is DEAD for this leg**: the ball mean square of a generic
  dyadic polynomial is O(1) by the MVT (no decay — verified page:
  (4r+20N)·Σ‖aₙ/n‖² ≍ 40); DECAY requires the coefficient structure
  (non-pretentiousness), whose tool is precisely the pointwise bound. And
  ∫_ball ‖·‖² ≪ e^{−M} IS the 𝒯₀-bound of Prop A.3 — assuming it is
  circular. (Recorded so it is never re-proposed.)
- **The naive Perron transfer has a contamination page**: A_t(m) =
  (1/2πi)∫ P(1+σ+i(t+v))·m^{σ+iv}/(σ+iv) dv (the landed truncated-Perron
  machinery at the shifted frequency); the integrand at v ≈ −t hits the
  trivial frequency where the L-series/polynomial is Θ(1/σ) = Θ(logX)-sized,
  damped only by 1/|v| ≈ 1/T₀ = (logX)^{−1/15}: naive contribution
  (logX)^{1−1/15} ≫ S. Whether the min-kernel/zone structure + the WINDOW
  geometry (t + v stays outside the trivial zone until |v| ≈ |t| ≥ T₀)
  kills this honestly is HSUP-SCOPE's Q1 — the page must be worked, not
  hoped.

## The candidate routes (to be priced by the scoper, then frozen)

- **ROUTE H (the MRT-faithful pointwise Halász; the expected primary)**:
  port A.6's proof shape — inclusion–exclusion over the g_J smooth parts +
  the classical pretentious pointwise bound per piece. The corpus's
  ingredients: the B-ladder at 1+σ (euler_log_bound, head_sigma_bound,
  window_sup_decay — LANDED, the L-series pointwise decay ON the window);
  the missing step is the L-series → partial-sum transfer at 1+1/logX
  (Perron with the contamination page, or GHS Lemma 1's own
  partial-summation route). The t₀-shift: A_t at ball t = the seam datum
  re-centered (seamCoeff's t₀ is a free parameter — the machinery is
  twist-generic BY DESIGN; verify the re-instantiation is mechanical).
- **ROUTE P (the smoothed/hat Perron)**: the corpus's hat-smoothed sum IS
  a smoothed Perron; the S1′ representation is stated at a free center t₀
  and free scale X (SEAM-SCOPE/BRIDGE-REF verified X free). The hat kernel
  kills the sharp-truncation zones; the cost is the representation error E
  (C_E·((X+h)/log(X+h))·log y + …), which HExit's CODA records as
  MAIN-TERM-SIZED at log y ≍ log X — but the y-pin is a free parameter of
  the split: AT log y ≍ (logX)^{1/2} the E-error is tail-grade. Q2: does
  the B-ladder's decay survive the y-re-pin (the smooth part grows as y
  shrinks; head_sigma_bound's grade vs the y-dependence — the honest
  trade-off page).
- **ROUTE D (defer)**: leave hSup as the named binder permanently at this
  layer and route the e^{−M} main term through a DIFFERENT decomposition
  (MR's Prop-1 shape has NO e^{−M} term — only MRT's A.3 does; if the
  s8-freeze's exp(−M/2) term can be supplied at the ASSEMBLY level by the
  f=1/λ specialization's own structure rather than per-row…). Q3: check
  the freeze's actual consumer — does thm_A2′'s f-arm need the e^{−M} term
  from THIS row, or does the λ-instantiation supply its quality floor
  elsewhere (the S9/λχ̄ arm)? If the latter, hSup's grade demand may drop
  to polylog — a rescope, not a proof.

## HSUP-SCOPE's charges (dispatched now; read-only)

Q1 the contamination page (Route H/P shared): the honest Perron-transfer
arithmetic at ball frequencies with the landed zone machinery — does the
trivial-frequency mass die? Work it at the four corners. Q2 the y-re-pin
page (Route P): the E-error vs the B-ladder decay as y moves — is there a
y where BOTH are tail-grade? Q3 the consumer audit (Route D): what does
thm_A2′ actually need from this row's ball leg (read the s8-freeze wave-5
card + MRT A.3's role in the §3 assembly) — the honest grade demand. Q4
the corpus census for Route H: GHS Lemma 1's proof shape vs our landed
surfaces — the exact missing stones, classed. Q5 THE LADDER + classes +
GO per route.

*The freeze follows the scoper's report; refuters follow the freeze; the
wave follows the verdicts. No executor consumes this block before then.*

## ⟦THE SCOPE VERDICT + AMENDMENT V1 (maestro ruling, 2026-07-24 ~18:20)⟧

HSUP-SCOPE (Opus 5, 278k, the week's deepest recon) — the verdict reshapes
the block:

1. **ROUTE H IS THE ONLY ROUTE.** Route P is not separate — it IS H-6, and
   ~60% of it is landed (prop21_unconditional_clean's E-error is byte-for-byte
   GHS Prop 2.1's remainder; the B-ladder is y-FREE — the feared smooth-mass
   penalty does not exist in any landed statement; MRT's own y-pin
   exp((logX)^{1/2}) sits inside our gates, and the frozen interface's
   (logX)^{−1/2} second term IS the E-error at that pin). Route D is REFUTED
   by an explicit datum (f = n^{iT₀}: no decay exists at M ≈ 0 without the
   M-shape) — the e^{−M} stays on this row. The naive Perron transfer is dead
   at v ≈ 0 (the 1/σ prefactor × the kernel's log-mass — the contamination
   worry was second-order; the page died earlier).
2. **THE DECISIVE DEFECT: ball_leg_of_sup (landed yesterday) is fatally
   crude** — 2r·(2S)² DIVERGES at every live M (numerics: at M ↑
   (1/16)loglog X the exit is (logX)^{+0.0395} → ∞). MRT never take a sup:
   A.7's 1/(1+|t−t₁|) factor stays INSIDE the integral, giving 16S² with NO
   r-factor. Repair = the t-WEIGHTED binder hSup′ (S·m/(1+|t−t₁|)) + the
   weighted ball leg [B, ~150]. spoly_abel_sup needs no change (per-t).
   Flags entry banked; the row's hSup consumer repairs additively.
3. **THE CENTRE IS WRONG (defect #3, counterexample f ≡ 1)**: the ball
   centre must be the GLOBAL minimizer of M(f;X) over |t| ≤ X — NOT the
   M_range near-minimizer (M_range ≥ M makes the claim stronger AND false;
   for f ≡ 1 the true ball sits below T₀, Ann∩ball = ∅, the ball leg is
   ZERO, and the far leg's Mrange floor does the work — exactly MRT's
   architecture: M(f;X) on 𝒯₀, M_range on 𝒯₁).
4. **THE GRADE HALVES (defect #1)**: (A.13)/(A.14)'s square root halves the
   pointwise exponent — with our B-ladder c = 1/e the honest exit is
   e^{−M/(2e)}, and the final grade becomes (logX)^{−1/(64e)}. Existential-c₀
   posture absorbs it (and the W-conversion needs only c₀ ≥ 1/500 — margin
   3–30×); the frozen halasz_ball_decay stays as heritage; NEW stones carry
   the honest grade. **S-3's re-freeze goes to JYH at the morning council.**
5. **THE BALL'S LIVE BAND IS NARROW**: the A.4 dichotomy (landed,
   dist_split_A4_frozen) kills the ball at M ≥ (1/16)loglog X; the MVT
   covers M = O(1). The ball leg works only on 1 ≤ M < (1/16)loglog X.
6. **R2.4's "GS[10] Lemma 7.1 dissolved" verdict is RETRACTED** (defect #4):
   A.7's renormalisation factor is exactly what the weighted repair consumes;
   GS Lemma 7.1 re-enters as **H-4 [D, 800–1200] — the campaign's one
   remaining D-node** (the D-count honestly: 1 → 0 (CHI-CHECK) → 1 (this)).
   Fail-fast discipline when dispatched; an unhurried design block first.
7. **NOTHING IS BLOCKED BY hSUP** (grep-verified: no consumer). The campaign
   advances on the other fronts while H-4 gets its block.

THE REPAIR WAVE (dispatched now, additive): H-0 (annulus-restrict the
binder — window-legality free win) + H-1 (the weighted ball leg) + the
re-centred row variant (S-1/S-2 applied) + H-2 (the σ-cutoff 1/e-clone,
mechanical). H-3 (the ⅞-bound) + H-5/H-6/H-7 follow the morning council's
ratifications (S-3, S-4) and the H-4 design block.

## ⟦S-3 RATIFIED — ROUTE-SCOPED, WITH THE TRIPWIRE (JYH, 2026-07-25 morning council)⟧

The grade halving (c = 1/(2e), the A.13/A.14 square root) applies to the
BALL leg only; the §8.3/L3 arm keeps the un-halved 1/(32e) ledger (Halász
consumed directly, Lemma-1 form). Mechanics: halasz_ball_decay untouched
(heritage); new ball stones carry e^{−M/(2e)} (the σ-cutoff 1/(2e) instance
already landed); existential-c₀ posture in all statements. **THE TRIPWIRE
(named, load-bearing): the H-4/H-6 design block MUST verify the un-halved
supply genuinely reaches L3 before any §8.3 assembly wave fires — if the
H-6 route forces the square root into L3's input, the §8.3 balance page
re-runs and returns to JYH; no silent absorption.** The real-χ Siegel-arm
stays on S9 (scope-diff 9) — confirmed informational.

## ⟦THE H-BLOCK FREEZE v2 (maestro, 2026-07-25, from H4-SCOPE's source-grounded map)⟧

**THE HEADLINE: THE D IS DEAD — the campaign's D-count goes 1 → 0, against
the source.** GS Lemma 7.1 (math/9911246 p.22, staged in docs/sources) is
ELEMENTARY: f = 1∗g, the d-split, Halberstam–Richert (7.1) + its Abel
corollary (7.2), the Euler bound on Σ|g|/d, "use twice, once at α = 0."
No Halász, no contour, no max-modulus, no 𝔻. The two sieve inputs are
LANDED (hall_tenenbaum_core :783 + euler_exp_bound :925, MultShiu — κ=1→2
constant relaxation, the day-1 fail-fast). H-4 re-priced **[C, 900–1400]**.
NOTE the deflation mechanism: the Shiu/Hall–Tenenbaum ladder, NOT the
B-ladder (HSUP-SCOPE's B-ladder hypothesis was right about GHS Cor 1.2 =
H-6's max-modulus replacement, inapplicable to 7.1 itself).

**THE TRIPWIRE CLEARS (the ratified S-3 route-scoping is CORRECT against
the source)**: the square root enters at (A.11)'s 𝒥-symmetrisation,
propagates through (A.13)/(A.14), and is consumed ONLY in the 𝒯₀/ball
assembly (p.28's max display → e^{−M/2}). NOT in GS 7.1 (additive M-free
error); NOT in the 𝒯₁ branch (absolute floors; dist_mul_half's ½ is the
twist cost, already priced, non-compounding); NOT in MR Lemma 3 (real f,
no 𝒥). ρ = 1/(32e) stands for §8.3: 1/261 vs c₀ ≥ 1/500, margin 1.92×.
**THE LIVE GUARD (replaces the tripwire)**: L3's arm cites
sigma_cutoff_pretentious_of_gen (c = 1/e); the ball's arm cites _half
(c = 1/(2e)); **a citation of _half in any §8.3 consumer is a STOP** —
both instances landed side-by-side, discipline is the only requirement.

**TWO SOURCE CATCHES (flags entry)**: (A) MRT (A.8) prints the CONJUGATE
factor — state H-4 correct-sign (X^{i(t₁−t)}/(1+i(t₁−t))), the executor
re-derives the sign as step 0; the modulus page: (1+u²)^{−1/2} ≤
√2/(1+|u|) — the √2 lands in S. (B) GS 7.1 ≠ GHS Thm 1.5 — the target is
GS [10] Lemma 7.1, unambiguous.

**THE LADDER v2 (all C, total ~2450–3800)**: H-3 [B/C, 250–350, ALOFT]
the ⅞-bound (numerics verified: 0.8536 ≤ 0.875, slack 0.0214; β ≤ ½ via
the landed mertens_second_sharp_real — an exact fit); **H-4 [C, 900–1400,
DISPATCHING]** GS 7.1 correct-sign with the day-1 κ=2 fail-fast + the
crude-O(1+|α|log z) fallback for the Euler–Maclaurin stone (survives at
|α| ≤ (logX)^{1/16} — the ball radius makes the α-range trivial);
H-5 [C, 550–800] the 𝒥-factorisation on the LANDED halasz_cosh_ineq
(= Lemma A.8 byte-for-byte — confirmed) + the (P_j,Q_j] half-open pin
BEFORE dispatch; H-6 [C, 400–700 residual] the direct-form Halász core
(head_sigma_bound + _of_gen — the citation guard); H-7 [C, 350–550] the
assembly into ball_leg_of_sup_weighted's exact binder. Dispatch order:
H-4 alone now (H-3 already aloft); H-5 next; H-6/H-7 last.

**Refused supplies recorded**: the B-ladder for H-4; zeta_partial_em (gated
off Re = 0; its SUB-machinery is the right genre for the 1st-order term);
GHS Thm 1.5; MRT (A.8) verbatim.

## ⟦THE HCENTER FREEZE (maestro, 2026-07-25 10:56 PDT; from HCENTER-SCOPE's map)⟧

**ROUTE A ALONE** (the S1'/hat wire ∘ desmooth): ~1450-2380 ln, all A-C.
REFUSED with arithmetic: A2 the box-collapse (the (X/y)^{2eta} wall at every
legal y); B the truncated Perron (the (logX)^2 main-term deficit -- the
min-kernel machinery is IRRELEVANT to this socket, never list it again);
C the L^2 dodge (circular); GS 7.1 at the centre (a transfer manufactures
no bound -- the socket/supply lesson, again). ROUTE D (sharp truncation +
a Lambda-mean-value stone [C,400-700]) recorded as the fallback if the
epsilon ruling ever bites.

**THE STEP-0 RULINGS (maestro tier, each within a ratified posture):**
1. **Mglob ADOPTED** -- the global-min distance over |t| <= X, the
   formalization of the ALREADY-RATIFIED centre semantics (the ball re-pin's
   S-1: the centre = the global M(f;X) minimizer). A new def + scale_floor
   clone [B]; it PINS the seam row's deliberately-open centre semantics.
2. **THE hgrade epsilon RULED under the existential-c0 posture** (freeze
   N4/scope-diff 6): the supplier states S0 with the +epsilon slot (the
   sharp kernel's loglog X deficit absorbed as (logX)^{-1/(64e)+eps});
   T1_decay_conditional_final's exact head exponent gains the eps AT THE
   SUPPLIER (no landed statement edited; the additive variant carries it).
   Surfaced to JYH in the ledger; Route D remains the priced alternative.
3. **THE GATE-(b) SHAPE CORRECTED** (the scoper's highest-value catch): the
   JointHead residual record's (X/y)^{2beta} target is TRUE but UNCOMPOSABLE
   (the X^beta gap diverges at every polylog y); the S5/S6 wave fires
   against the HONEST product X^beta y^{-2beta}(L+C)^2 -- which is GHS's own
   x^{1-alpha}y^{-beta} and composes. Flags entry banked.

**THE LADDER** (the scoper's, adopted): A-7 the uniform-constant hoist
[A/B, DISPATCHING NOW -- independent]; A-1 Mglob + scale_floor_Mglob [B];
A-2/A-3 the centre clones [B]; A-4 hpret concrete [C, 250-400 -- the
JointHead:266 PENDING note is STALE, retired herewith: head_sigma_bound
landed since]; A-5 hbridge at the pinned home, HONEST TARGET ONLY [C,
500-800]; A-6 hgrade per ruling 2 [C]; A-8/A-9 the assembly
center_halasz_supply [B/C] -- the freeze-ready statement in the scoper's
report, byte-compatible with BallSup:479 at f := seamCoeff (ellLin g) 1 t0
(the datum gate: the supplier is for THE SEAM DATUM ONLY -- ellLin route (i);
general multiplicative f has NO supply and must not be instantiated).
The y-pin free in the gates; y = (logX)^4 recommended (E/X = (logX)^{-1+o(1)},
margin 0.99 powers), e^{sqrt L} the fallback if the eta-box tightens.
X0 is g/t0-independent (HExit:741 -- recorded, nobody re-derives it).

**REFUTERS on this freeze** (2, firing): SHAPE-REF (the A-5 honest-target
page + the A-9 binder byte-compat + the datum gate) + GRADE-REF (the full
grade page at the corners: the desmooth 1/sqrt-log, the E-term at both
y-pins, the eps absorption, the S0 bracket vs ballSupS's demand). The wave
fires on the verdicts.

## ⟦HCENTER AMENDMENT V2 — the refuter verdicts applied (2026-07-25 11:17 PDT)⟧

Both REPAIR-THEN-FIRE. THE REPAIRS (adopted):
1. **A-5's target restored to BOTH sharp factors**: S₋·S₊ ≤ C·X^β·y^{−2β}·
   min(L,1/σ)² (my correction had dropped the sharp Mertens factor while
   fixing the X-power — half-applied; the composed page then overshoots by
   L·η, a FULL log beyond the arcsinh absorption). NEW STONE A-5a: the
   σ-damped Λ-window masses (Abel on A(u) = Σ Λ/n ≤ log u + C) [C, 250-450];
   A-5 re-priced 750-1250. The verified landing: Agrade on X·L^{3/2} — the
   ledger's own pre-existing kernel-mass residual, nothing new.
2. **A-7 TIGHTENED to the datum-hoisted form** [B, 120-180]: the MS witnesses
   are g- AND t₀-FREE absolute expressions (MultShiu:1434/:2220/:1908;
   ShortIntervalPsi:411) — hoist past (g, t₀) too; REQUIRED because A-9
   instantiates the twist at t₀+t₁(X) (X-dependent centre) — the t₀-bound
   constant would be circular. Without this the row's constants are not
   X-uniform (SHAPE-REF's teeth).
3. **The ε pinned**: ∀ε ∃X₀(ε) quantifier order at A-6 ONLY; ε := 1/1000
   (below both caps: 1/(192e) = 0.0019 keeps the ball off the critical
   path; 1/(64e)−1/500 = 0.0037 the hard door wall); the price recorded:
   X₀(ε) ≍ exp(C^{1/ε}) becomes the campaign's dominant threshold —
   Route D is the effective-X₀ alternative.
4. **THE M-SHAPE (R-1e, the kill)**: the supplier is M-SHAPED, no numeral —
   ≤ (C·exp(−(1/(2e))·pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀)
   (costwist t₁) X) + C·loglog X·(logX)^{−1/2})·k; numeric exponents ONLY
   at consumers where hfloor lives. The μ²-refutation (g ≡ 1: S₀ ≈ 0.608)
   kills any bare-power supplier. **A-10 ADDED [B/C, 150-300]: the
   ball-centre dichotomy** — |t₁| ≤ seamT0 − seamRad ⟹ Ann ∩ ball = ∅
   (the ball leg is 0; the pretentious case exits here) OR the floor at t₁
   on the enlarged window via Mrange_one_floor's per-t step.
5. **The LIVE GUARD extended**: a §8.3 consumer citing _half OR the
   ball-graded head of center_halasz_supply is a STOP.
6. **A2's refusal reworded** (the joint-constraint form — the wall and the
   E-term cannot both be tail-grade); the y-pin restated as the RANGE
   2·loglog X ≤ log y ≤ (log X)^{1−δ} (pins are instantiations).
7. **The live band tripwire**: the ball's honest band is [(1/32)loglog,
   (1/16)loglog) — factor 2, NO slack; any re-grade moving either numeral
   empties it.
8. UNASSIGNED-3 is ALREADY DISCHARGED (SMALLSTONES landed the Mertens
   conversion an hour before the refuter read the older docstring); its
   two sub-residuals (the twist-slot transfer; the X→[X,2X] drift) fold
   into A-9. UNASSIGNED-2 (hfloor's seam-datum provenance over-claim,
   pre-existing) — flags entry banked.

**THE GOVERNANCE ITEM (to JYH, per the refuters)**: the two-M architecture
vs AMENDMENT J0 — see the consult in-session.

## ⟦THE TWO-M READING RATIFIED (JYH, 2026-07-25 12:02 PDT)⟧

Ball leg = the global M via the minimizer (M-shaped statements; the frozen
terminal's own exp(−M(f;X)/2)); far/annulus legs = M_range (J0 intact on
its domain); J0 refined, not reversed (its target was the seam-t₀ drift,
not the minimizer). The main assembly wave releases.

## ⟦GRADE-SCOPE VERDICT + AMENDMENT V3 (2026-07-25 13:44 PDT)⟧

(1) crossKer: ONE def in the corpus — the ramp ladder is byte-ready, no
adapter. (2) The y-gate excluded at the pin (2·2⁸ dropped in the old
reading) BUT the width is decouplable: A := (y/2)^{1/8} ≈ 0.92√L makes the
gate true BY CONSTRUCTION at cost 2.9× constant — internal to HeadGrade,
no re-pin. (3) The composed page: the landed decayed grade halves the
deficit (L·logL → L); THE FULL CLOSE = ONE new stone (A-3, the
Plancherelized tail: hatKernel_branch2 + the Lorentzian domination +
mixed_weight_cs + widthA_plancherel at width A — every ingredient LANDED)
→ **Agrade ≤ C·k ABSOLUTE. The geometric mean carries min¹ not min² — the
whole win.** (4) Consumer tolerance INDEPENDENTLY CONFIRMED: not even one
L is tolerable (overshoot ~1.99 powers) — the Plancherel route is
LOAD-BEARING. (5) **THE SIXTH VACUITY CATCH: hmin-on-ℝ is VACUOUS in the
live band** — Kronecker density makes the ℝ-inf of the finite distance sum
Σ(1−|f(p)|)/p = 0 for unimodular data, contradicting the band floor;
hRHS_discharged/center_halasz_of_grade are vacuous in the live branch AS
STATED (kernel-valid; caught pre-consumption — flags). THE REPAIR: the
CONTOUR TRUNCATION at T* := L⁴ (the far t-part crude at the FREE M = 0
floor × hat_tail, absorbed via hMcap at margin L^{−2.5}; hmin restricted
to the compact |v−t₁| ≤ T* where ATTAINMENT IS FREE — the ℝ-caveat moot);
the overhang via the uncapped dist_one_floor_pow + recenter_sq_floor + the
cap. NO statement changes anywhere — added hypotheses + internal widths
only. THE LADDER: A-1..A-6 (the width-decoupled Plancherel close,
~755 ln, one new analytic stone A-3) + B-1..B-3 (the truncation, ~480 ln).
GO: A-1→A-2→A-3 ∥ B-2; then A-4/5/6; B-1/B-3 last.

## ⟦V3a — GRADEA-WAVE as-built addendum⟧

The A-arm landed (WidthGrade.lean, 12 public stones, zero warnings). Two
deviations from the V3 ladder, both improvements, both kernel-checked:

1. **THE DIAGONAL CORRECTION (the step that makes the constant absolute).**
   The ladder's naive `diag ≤ 2·mass` is NOT enough — it leaves
   `Amp·(π/A)·2 ≍ 218√L`. The landed `diag_le_mass_width`: under the y-gate
   `2A⁸ ≤ n` and `c ≥ 3/4`, `‖b_n‖/n^c ≤ 2/n^{1/4} ≤ 2/A²`, hence
   **`diag ≤ (2/A²)·mass`** → `Amp·Kfac ≈ 638·C` ABSOLUTE.
2. **`lorentz_compare` NOT NEEDED.** Head and tail are referred to ONE shared
   pair of full-line width-A moments via `band_weight_le_lorentz`
   (`∫_band ‖P‖²/√(cw²+τ²) ≤ (2T₀²/cw)·∫_ℝ ‖P‖²/(A²+τ²)`), deleting a
   grading stone and the windowSum→Dirichlet fold from A-4.

Confirmations: hband_discharge/offdiag_widthA_*/widthA_plancherel carry the
width as a FREE parameter (A-2 was ~60% instantiation); the y-gate is free
by construction at A := (y/2)^{1/8} (width_pin_gates: 2A⁸ = y ≤ n on the
window); the min(L,1/σ) is spent ONCE — min¹ confirmed in the kernel.
A-5 exit carries NO L factor; the full L·log L deficit is removed.

RESIDUALS (the GRADEB brief): (1) Cb uniformity over β — obtain C once from
the c/β-agnostic hband_discharge, re-derive the private symmetrization
(~25 ln), restate A-5 as ∃Cb ∀αβ; (2) A-6 proper (rhsAgrade_const +
rhs_grade_at_scale_const + the C₁ corollary) — all landed plumbing, ~150 ln,
gated on (1); (3) the pin arithmetic Amp·Kfac ≤ Cabs (~60 ln rpow).

## ⟦V3b — THE GRADE SOCKET DISCHARGED ABSOLUTE (GRADEB-WAVE as-built)⟧

All three residuals closed (GradeConst.lean, 12 public stones, zero warnings).
The chain: exists_shortIntervalDatum (the constant lifted ONCE, outermost) →
crossKer_width_sigma_bound_uniform (ONE Cb, uniform in β AND scale) →
width_pin_bracket_le (the pin numeral: widthKampBr ≤ 175616·(1+Cb); the two
L's cancel; ~275× looser than the design page — sharpness irrelevant) →
rhsAgradeConst_le (**Agrade ≤ gradeAbsConst·k, free of k, X, L**) →
hRHS_discharged_const → center_halasz_of_grade_const (THE CAPSTONE: C₁
absolute, quantified outermost; grade socket GONE).

**THE REUSE FINDING**: hRHS_discharged itself is NOT reusable — its hgrade
hypothesis is stated on rhsAgrade (the old L·log L amplitude), never ≤ C·k
absolutely. Iron rule 1 respected: statement untouched; the same CONCLUSION
re-proved through the width face, and byte-exactness MACHINE-VERIFIED by
composing with the actual consumer (center_halasz_of_grade_const compiles =
the binder-compatibility proof). Scale gate: exp 64 ≤ k (inherited);
h hard-wired to k/√L (R-2's numeral needs the concrete pin).

**STATION STATUS**: the hSup ANALYTIC frontier is CLOSED. Remaining carried
hypotheses on the capstone, exactly two: (1) hmin — still the on-ℝ (vacuous)
form; the swap point is center_dist_floor (:1334 in the capstone's proof) →
TruncFactor's center_dist_floor_trunc/_compact; (2) the four JointIntegrableAt
sockets. Both are SUPCLOSE-WAVE (glue, no new analysis).
