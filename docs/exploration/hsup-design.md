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

## ⟦V3c — SUPCLOSE as-built: the TRUE seam + a V3b CORRECTION⟧

**CORRECTION (maestro error, machine-refuted)**: V3b's "the swap point is
center_dist_floor (:1334)" was WRONG. Wall 1: rhs_grade_at_scale_const's hMt
is on-ℝ INSIDE the grade (it rides joint_cs_factoring's ∀-t hsupF) — the
compact floor is an application type mismatch there, captured verbatim. The
true seam is one rung down, at joint_cs_factoring_trunc. Wall 2: the
recentred consumption (contour centred at t₀+t₁, floor centred at t₀) forces
the gate |t₁| + T ≤ R, which exists_min_dist_abs alone cannot discharge.

**AS-BUILT (SupClose.lean, 5 stones)**: joint_supF_pin_at (the floor at the
ONE consumed point) → center_dist_floor_recentred (gate |t₁|+T ≤ R) →
joint_supF_pin_trunc (joint_cs_factoring_trunc's hsupF from COMPACT
minimality alone) → joint_cs_trunc_pin (the byte-exactness compile) →
**rhs_grade_at_scale_trunc: ‖prop21RHS‖ ≤ gradeAbsConst·k·e^{−M/(2e)}
+ (1/π)·η²·(Ffar·Kfar)** — main term byte-identical to hRHS_discharged_const's
RHS; hmin NON-vacuous (|v| ≤ R only). ball_sup_supplied carries NO hmin —
the vacuity enters the crown solely through hRHS; the seam to the crown is
exactly ONE un-absorbed far term.

**RESIDUALS**: Z1 far absorption (analysis: Ffar numeral via joint_supF_pin_at
at M := 0; Kfar via crossKerFar_pin_le at T := L⁴; the hMcap pricing of
e^{−M/(2e)}) — FARCLOSE-WAVE. Z2 the overhang gate |t₁| ≤ R − L⁴ — DESIGN
BLOCK: the landed localization (compact_min_package) requires hgap, which the
frozen 1/16 live-band numeral fails by a logloglog sliver (B-2's finding);
candidate repair = shift the seam case-split threshold by −O(logloglog),
priced as a (loglog)^{O(1)} factor absorbed by the ε-slot via loglog_absorb —
Z2-SCOPE dispatched to locate the numeral (parameter vs frozen statement) and
price the shift. If a ratified-frozen statement must change: JYH GATE.

## ⟦V3d — Z2-SCOPE VERDICT: THE NO-GAP ROUTE (b) ADOPTED⟧

**VERDICT (C)**: the gate |t₁| + T ≤ R needs NO hgap, NO localization, NO
numeral shift. Seam geometry closes it: on the ball leg's own domain
(t ∈ seamAnn ∩ seamBall) the intersection being nonempty forces
**|t₁| ≤ T_ann + seamRad X** (the outer companion of the landed inner cut
CenterCore:490 — ~8 ln, the shape M_range already encodes at
DistHalasz:264). Instantiate exists_min_dist_abs at
**R := T_ann + seamRad X + (log 2X)⁴ + 1**: hgate discharges outright; if
the intersection is EMPTY, hSup is vacuous (its guards ARE membership) and
the row applies with any S. Acid test passed in BOTH regimes — in T_ann ≈ X
(the L14 row) the B-2 counterexample's minimizer sits exactly where
|t₁| ≤ X is FALSE, and the gate never references X. Cost ~50 ln class B,
ZERO statement changes, NO JYH gate. (Route (a) — the threshold shift — is
banked as the fallback: the honest price is σ = (5/4)·logloglog + (C+1)/4,
absorbed by the frozen statement's own −5·logloglog slack at K ≤ 10, zero
conclusion change; ~200 ln + advisory ratification. Route (c) T-shrink:
refuted as a route (the gate's shape is T-independent); trade curve banked —
break-even T ≈ L^{0.512}, landed L⁴ carries ~L² unused slack.)

**CENSUS**: exactly TWO blocking floor-direction sites of the 1/16 numeral
(PropA3Core:74 branch_a, :172 dist_split_A4_frozen — the latter FROZEN per
s8-freeze N2, no code consumer yet); both are thin wrappers over the
free-parameter engine dist_split_fgJ (DistSplit:201, Lf free). ALL other
sites are cap-direction (monotone-safe) or M-shaped (R-1e discipline held —
no numeral anywhere on the grade chain).

**RECORD CORRECTIONS** (scoper's, verified): (i) the CompactMin flags entry
UNDERSTATES the hgap failure — it fails DIVERGENTLY (deficit 5·logloglog + C
with C ≳ e^100 ≈ 10⁴³ from dist_one_floor_pow's witness), not "at the
boundary"; the docstring's "1/64 clears it for large X" is true only past a
3-tower and would drag the frozen (1/32) conclusion to (1/128). (ii) NOTE
FOR JYH (two-M adjacency, surfaced not resolved): with R ≤ X the minimizer's
bound IMPLIES the terminal M(f;X)-shape (strong direction); with R > X (the
T_ann ≈ X regime) it does NOT without a further step — the main assembly
wave must pick the direction consciously before consuming either route.

## ⟦V3e — FAR-ARM FINDING + THE T* RULING (FARCLOSE + GATE composite)⟧

**FARCLOSE's refutation (honest, machine-checked to the last arithmetic)**:
the crude far absorption at T* = L⁴ is FALSE — Kfar's ℓ¹ window masses carry
(k/y)^{η−1/L} = e^{L/(4logL)−2+o(1)}, superpolynomial in L; no absolute Cfar
exists (invisible at the exp-64 gate, decisive just past it). The hfar
socket is carried, NOT forced; everything downstream is landed: F-4 at ONE
term (C₁ = gradeAbsConst + Cfar absolute), hRHS_socket_of_far VERBATIM =
ball_sup_supplied's hRHS, and **ball_sup_closed — the crown DELIVERED at the
non-vacuous hmin, modulo hgate + hfar**.

**GATE-WAVE landed route (b) whole** (SeamGate.lean, zero traps): G-1/G-2
hypothesis-free; seamGateR := Tann + seamRad + log⁴(2X) + 1;
rhs_grade_at_scale_seam_gate = the trunc grade with hgate DISCHARGED from
nonemptiness (the compile = the fit proof); the empty arm supplies hSup
byte-for-byte at any S (ball_leg_of_inter_empty ≤ 8S²).

**THE RULING (maestro, from the composite)**: repair (i) — T* := y·k^{1/log y}
— is ADOPTED. FARCLOSE priced it "expensive" on the R-blow-up, but route (b)
makes R a FREE parameter discharged geometrically at ANY value; and T* =
X^{1/(4·loglog X)} is SUB-POLYNOMIAL in X, so the polyT regime keeps R ≪ X
(the strong two-M direction SURVIVES there; the L14 regime was already
R > X). far_kernel_bound_T is already stated free-T; the margin page at T*
is FARCLOSE's own (ratio ≤ L^{−3/2}/log L, decreasing). Repair (ii) (the
Plancherelized far region) is REFUTED as a cheap route: the dyadic-width
treatment breaks the offdiag y-gate (2S⁸ ≤ n) at widths S > √L — the
kernel-tail decay (2^jT*)^{−2} exactly cancels the band growth without it;
C/D-tier if ever revived. FARSTAR-WAVE: re-pin the far arm at T*, the
monotone per-k gate (k ↦ y(k)·k^{1/log y(k)} increasing), seamGateRstar,
and the closed chain ball_sup_closed_star. NO statement changes.

## ⟦TWO-M DIRECTION RATIFIED (JYH): OPTION (A)⟧

The ball-leg exit is stated at the ENLARGED-window infimum (over |t| ≤ R,
R = seamGateRstar) UNIFORMLY in both regimes — one clean statement; the
polyT regime's strong M(f;X) direction remains derivable there as a
corollary (R ≤ X ⟹ enlarged inf = the [−X,X] inf restricted comparison).
Pre-assembly obligation (maestro): verify MRT A.3's own M-convention (the
working-window infimum) against the RENDERED page — the faithfulness check.

## ⟦A.3 FAITHFULNESS CHECK — PASSED, WITH A BONUS (rendered p.22, 1503.05121v3)⟧

Verified on the rendered page: (i) Prop A.3's statement carries
M(f;X)/exp(M(f;X)) at **M(f;X) = inf_{|t|≤X} 𝔻(f, n↦n^{it}; X)²** — the
[−X,X]-capped infimum, with t₁ "the value of t which attains the minimum"
(attainment ASSERTED, not proved — our exists_min_dist_on_Icc is exactly
the formal grounding; a nice paper footnote someday). (ii) **THE BONUS —
MRT's own MVT escape**: the proof opens "Since the mean value theorem gives
the bound O(T/X+1), we can assume T ≤ X/2 and M(f;X) ≥ 1." So the honest
working range always has T ≤ X/2, and OUR R = Tann + seamRad + T* + 1 with
Tann ≤ X/2 and T* = X^{1/(4loglog X)} sub-polynomial gives **R ≤ X in every
live row** — [−R,R] ⊆ [−X,X], the R-window inf ≥ M(f;X), hence
exp(−c·𝔻²(t₁)) ≤ exp(−c·M(f;X)): the ratified option-(A) statement IMPLIES
the M(f;X)-shape in every live instantiation. B-2's counterexample corner
(R > X) lives entirely beyond the MVT escape. ASSEMBLY GUARD: the assembly
wave carries the T ≤ X/2 reduction explicitly (the trivial MVT row bound
covers T > X/2), mirroring MRT's own opening move.

## ⟦V3f — THE hSUP STATION CLOSES (ASSEMBLY-WAVE as-built)⟧

**seam_ball_leg_station** (SupStation.lean :540): the composed ball-leg exit.
Discharged INTERNALLY: Cb (exists_shortIntervalDatum outermost — C₁ =
gradeAbsConst Cb + farCStar absolute), hmin (compact), hgate, hk64, hInt,
hne (BOTH dichotomy arms deliver the SAME binder at the same S — no
disjunction survives). Remaining: hg, the scale frame, the two coefficient
equations, and the A-10 cap as the exit's ANTECEDENT (the seam's own case
split, not a socket). No MVT guard needed — option (A) uniform, as ratified.
**seam_ball_leg_station_M** :717 — the M(f;X) form at any M₀ lower bound +
|t₁| ≤ X; the X-gate (seamGateRstar ≤ X) proven, dominated by exp(exp 40).
**prop_A3_T1_row_station** :782 — plugs prop_A3_T1_row_split_weighted's
hSup slot VERBATIM (the compile = the certificate); the row exits at
8·ballSupS² + the 𝒯-leg + U.

**THE QUANTIFIER PAGE**: the circularity was REAL as stated (the crown fixes
t₁ before X; the station's t₁ depends on X) and RESOLVED — the threshold
witness is t₁-FREE all the way down (ballMertensThreshold = exp(exp 40),
XA/XB datum-hoisted numerals). Fixed via uniform-X₀ replay clones (§2,
265 ln). **QUEUED REFACTOR (Fable-tier, not urgent)**: hoist ∃X₀ past t₁
in center_halasz_supply / ball_sup_supplied / ball_sup_closed_star
(binder-order only, proofs unchanged except intro order) — then §2 deletes.

**BONUS**: JointIntegrableAt is M-FREE — rhsFbound M = e^{−M/(2e)}·rhsFbound 0
factors out (rhsFbound_eq_exp_mul); jointIntegrableAt_pin_free costs only
exp 64 ≤ k. ⟦V3b⟧ residual (2) closed without touching the vacuous
minimality. Residual notes: the exit height is pinned at the row's Tann
(consumers with Tb ≤ Tann covered); the far arm of the A-10 cap is the
seam's other case, out of station scope.

**STATION LEDGER (the day)**: CompactMin → WidthGrade → CompactMin/TruncFactor
→ GradeConst → SupClose → FarClose ∥ SeamGate → FarStar → JointPlumb →
SupStation. Ten files, ~6,900 ln, every stone ≤ 3 axioms, zero warnings.
The hSup station is CLOSED.

## ⟦V4 — U8-SCOPE VERDICT: the hU map corrected + THE C-GENERIC RULING⟧

**MAP CORRECTION (the scoper's catch, against my brief)**: U-8's 𝒯_L is a
branch INSIDE §8.3's hU, NOT the row's 𝒯-leg. The row's 𝒯-leg is §8.1+§8.2
(MR's Σ_j E_j) — SEPARATE, UNSCOPED, ~[C, 1500–2500]. Closing U-5/7/8/9
supplies hU ONLY. Also: U-5 (𝒯_S) was unblocked 7/24 by HZ-WAVE and never
dispatched.

**THE COST DISCOVERY (S-3 adjacent, NOT the tripwire)**: the corpus's only
pointwise partial-sum Halász supplier is graded e^{−M/(2e)} from rhsFbound's
DEFINITION (127 numeral sites, 12 files); §8.3/L3 needs e^{−M/e} on a
DIFFERENT object (the Ramaré co-factor). The citation guard HOLDS (no §8.3
file cites _half — audited) but guards an empty room. The balance page does
NOT re-run (the ½ is a free monotone downgrade taken early; ρ = 1/(32e)
stands, margin 1.916×) — so no JYH tripwire; an INFORM (the ~1.2–2.5k
un-halved replay was never ledgered).

**THE RULING (maestro, Fable-tier)**: the c-generic supplier — ADOPTED, in
the PROCESS-SAFE form: a NEW file defines rhsFboundC (c M L σ) general +
the identity rhsFbound = rhsFboundC (1/(2e)); the chain replays c-generically
in NEW files; the un-halved arm lands as the c := 1/e instantiation. NO
landed file is edited (iron rule 5 never engaged); W1-of-U7 collapses
~1200–2500 → ~300–500.

**THE LADDERS (execution-ready, the scoper's)**:
- U-5 [B/C, 330–460] → USetThinTS.lean (spec: hu-scope-0724.md + the HZ
  unblock at pilot 7/24 22:20).
- U-8 [C, 730–1170] → USetThinTL.lean: U-8a ramQ↔dpoly adapter (mirror
  primeBlockPoly_eq_dpoly USetThin:392; the −𝒯 sign bridge re-arms) [B,80–120];
  U-8b |𝒯_L| ≤ exp((logX)^{θ+o(1)}) T-free via large_value_count :631 at
  V=(logX)^100 — THE X₀: hκ30 forces log X ≥ 30^{3/ρ} ≈ 10^{385}, in-statement
  ALWAYS [B/C,150–250]; U-8c Lemma 11 via halasz_primes_pow :3641 (gates free)
  [C,200–300]; U-8d the 1/v prime-window gain [B,150–250]; U-8e the kill
  (margin 64× at ρ=1/(32e); the VK β=3/4 is where the 1/4 lives) [B/C,150–250].
- U-9a [B, 250–400] → USetPins.lean: the pin arithmetic — Q_J² ≤ X^{o(1)}
  T-FREE via the definition of J (route (a), state THIS one); P-ii + P₈₃≤Q₈₃
  free; **the NEW Tann gate: hU's exit MUST carry Tann ≥ exp(30(logX)^{1/2})
  in-statement** (fails at polylog Tann — silent vacuity otherwise); the
  balance θ=ρ/3 exit (T/X+1)(logX)^{−1/(96e)+o(1)}, 1/261 vs c₀≥1/500 margin
  1.916×; loglog absorbable at 1/(32e) NOT 1/(64e).
- GO: U-5 ∥ U-8 ∥ U-9a NOW; then W4 (the c-generic supplier, post-ruling =
  now unblocked); W5 U-7 SCOPE; W6 U-7 wave; W7 U-9b/c/d serial; W8 the
  A-10 far arm [C,300–500]; the §8.1/§8.2 block needs its own scope.
- ASSEMBLY GUARD (new): the row is trivially satisfiable at degenerate
  fb/Jb pins (fb:=0 ⟹ Uset=∅; Jb:=0 ⟹ seamTtot=∅) — the consumer MUST pin
  fb to the datum primes and Jb:=J or the row carries no content.

**TOTALS (honest)**: to a supplied hU ~2,700–4,400 ln (prior estimate under
by ~2.4×); to the seam terminal ~4,500–7,400 (incl. the far arm + §8.1/8.2).
JYH GATES: none.

## ⟦V4a — U-5 as-built findings (for the U-9 assembly)⟧

U-5 LANDED WHOLE (USetThinTS.lean; the exit uset_TS_branch(_meanvalue) —
MR's §8.3 𝒯_S conclusion at the ε² gain × the mean-value grade). THREE
FINDINGS the U-9 assembly MUST consume:
1. **The sharp M is the CO-FACTOR length** M ≍ 2X·e^{−j/H}, NOT the dyadic
   N ≍ 2X — pricing at N blows the branch by e^{j/H} (up to
   exp(logX/loglogX)). Every U-5 statement takes M as a parameter with
   ramRrange ⊆ [1,M]; feed the sharp one.
2. **The α gate is α, not α_J**: at δ := P_J^{−α_J}, V := K₀/δ the honest
   exponent is α = α_J + log K₀/log P_J > α_J; discharge α ≤ 1/4−η′ via the
   η/(2J) slack (take η′ := η/2); the exit exponent is then 1−η. The naive
   "gate holds at α_J" is FALSE as stated.
3. **Two independent −𝒯 sign bridges that do NOT compose** (Uset_thin
   negates internally; ramR_sq_sum_le negates here) — both statements are in
   the un-negated variable; no adjustment crosses. Byte-checked.
Also: T ≤ X (MR Step 0) rides the exit in-statement; thinBundle carries the
count as an EXPRESSION (law #253); half-open audit clean.

## ⟦V4b — U-8 as-built (for U-9/U-7)⟧

U-8 LANDED WHOLE (USetThinTL.lean, all five stones, no Zeno). The exit
tL_main_sumsq: Σ_{𝒯_L}‖ramMain‖² ≤ 54·C·Rbd²/v² — one 1/v from L11's
1/log P, one from the window gain. **U-7's supply rides as the named
hypothesis `∀ t ∈ 𝒯_L, ‖ramR‖ ≤ Rbd`** — carried, never assumed away.
FINDINGS: (1) the honest window gain is **27/v, NOT 1/(Hv)** — Mertens'
own 12/log t error is 1/v-sized and dominates the window width; 1/v is
what MR's page needs, so no loss. (2) FREE GATE: P ≤ T^10 derives from
hκ30 alone (ramQbase_le_pow_ten) — one fewer gate to thread. (3) the kill
gate in-statement: 420·L·L^{3/4}·(log L)^5 ≤ c·(log base)² — satisfiable
iff θ < 1/8; at θ = 1/(96e) the 64× margin reproduced in-kernel. (4) 𝒯_L
is defined against ARBITRARY well-spaced 𝒯 — U-3's discretisation composes
without re-pinning. (5) the −𝒯 bridge (catch #B) handled inside
ramQ_eq_dpoly; ramQ_eq_halaszSum carries NO flip (the L11 integrand
byte-for-byte).

## ⟦V5 — U7-SCOPE VERDICT: the two-arm route + THE 1_S LAW + the ρ amendment⟧

**THE ROUTE**: U-7 = a dichotomy on the co-factor datum's own pretentiousness,
both arms exiting at the SAME Rbd = (log X)^{−ρ_eff}, ρ_eff = 3θ:
- CASE A (window floor everywhere): the c-generic grade route at c = 1/e —
  W4 as specced below, in WINDOW-FLOOR form (hMwin replaces hmin/hgate —
  SIMPLER than the seam original; the far arm carried ADDITIVELY via
  hfar_star's numeral, never absorbed).
- CASE B (a pocket t₁* exists): the NEW collision lemma (PretentiousTriangle
  + dist_one_floor_pow: hMcap ∧ pocket ⟹ |t₁*−t₁| < 1) + the LANDED GS-7.1
  transfer at large radius (reach exp((log X)^{0.488}) — the (log X)^{0.49}
  limit is on the normalized S, not the bound; no c-generic anything).
The cheaper σ-integral bypass REFUSED (the banked (log X)² deficit — GHS
2.1's (α,β) device is the only repair; halasz_direct_gen has zero consumers).

**W3 DISSOLVES + THE 1_S LAW (STANDING)**: the landed row's datum
(SupStation:787) carries NO 1_S restriction ⟹ Lemma 5 + the Q-smooth Rankin
count NOT NEEDED (that stone was an artifact of MR's proof shape); P-ii is
decorative. **THE LAW: the S-restriction must NEVER enter this row's
coefficients** — if it returns, U-7 dies outright (the damped datum loses
(1/2)loglog X of distance mass = 16× the floor; both arms fail; MR survive
only via their real-f Lemma 2, which has no complex port). 1_S enters at
the door/sieve level (§9) only.

**W2 = the ∫₀¹ x^ω route + THE ρ AMENDMENT**: the weight becomes
multiplicative inside ellLin (g_x p := g p·(x on [P,Q]); hg survives); the
price is a one-sided distance loss θ·loglog X (factor 1, not 2) ⟹ the
self-consistent pin **θ = 1/(32(3e+1)) ≈ 1/293** (was 1/(96e) ≈ 1/261);
**margin over c₀ ≥ 1/500: 1.916× → 1.707×, still passes.** USetPins'
theta83/rhoB4 are DEFS (not frozen) — the amended-pin twins land with U7-C.

**W4 CORRECTED (my ruling's estimate was low 3×): 1100–1400 ln**, the exact
list: W4-1 rhsFboundC/rhsSigmaGC defs + identities [A,60]; W4-2
joint_supF_pinC (RHSGrade:248) [B,120]; W4-3 beta_integral_pin_constC
(GradeConst:1025, cites sigma_cutoff_pretentious_gen at c) [B/C,250]; W4-4
rhs_grade_at_scale in WINDOW-FLOOR form (GradeConst:1089 + SupClose:334;
hMwin replaces hmin/hgate) [C,300]; W4-5 JointIntegrableAtC + the JointPlumb
clone (30 sites; σ^{2c−1} integrable at c > 0) [B,250–350]; W4-6
center_halasz_supply B-ABSTRACT (CenterSupply:296; the exponent opaque —
c-free forever after) [B,150]. C-FREE VERBATIM (do NOT clone): the whole
amplitude side (crossKer_width_sigma_bound_uniform, widthKamp,
rhsAgradeConst/gradeAbsConst chains), the FarClose/FarStar far arm,
prop21_uniform_at_scale_absC, spoly_abel_sup. SKIPPABLE (seam-specific):
center_dist_floor + the vacuous forms, SeamGate/seamGateRstar,
far_term_priced (carry additively), ball_center_dichotomy, SupStation.

**THE LADDER + GO**: W4-1/2/3 ∥ U7-A (the ramR = spoly adapter + Abel via
spoly_abel_sup; the half-open endpoint +2-terms page) [B,150–250] ∥ U7-B
(the ∫x^ω route + ellLin g_x + the interchange) [B,200–300] → U7-C (the
distance page + THE COLLISION LEMMA + the amended-pin twins) [C,300–500] →
W4-4/5/6 → U7-E (CASE A assembly at scale X') [C,500–800], U7-D (CASE B:
the radius-free transfer clone at S₀ = O(1)) [C,350–550] parallel → U7-F
(the dichotomy assembly, both arms → the same Rbd, no disjunction) [B/C,
250–400]. ZENO LINES: Z-1 hsep (the annulus-floor sliver — closure (i)
raise the 𝒰 inner height = assembly-tier; closure (ii) widen seamRad = a
FROZEN-STATEMENT change = JYH GATE, not U-7's to spend); Z-2 hMball
byte-fit; Z-3 the collision X₀ tower exp(exp(4·10^44)) — IN-STATEMENT
always. TOTALS: U-7 proper 1750–2800; with W4 2850–4200; hU honest
~4,000–5,800.

**SIDE-FINDING BANKED (not on U-7's path)**: FARCLOSE's "no absolute Cfar"
refutation is partly an ARTIFACT of two independent weakenings in
far_kernel_bound (the β-cancellation destroyed by separate majorizations);
a β-paired far bound puts T* back at ≈ L^{5.5} and would shrink
seamGateRstar + simplify FarStar — a [C,300–500] repair for whenever the
far arm next opens.

## ⟦V5 RATIFICATIONS (JYH: "1, 2 both look good")⟧

(1) THE ρ AMENDMENT RATIFIED: θ = 1/(32(3e+1)) ≈ 1/293; door margin 1.707×.
The amended-pin twins land with U7-C. (2) THE 1_S LAW RATIFIED as a standing
rule: the S-restriction never enters the row's coefficients; door/sieve
level only.

## ⟦V5c — U7-C as-built + THE MARGIN CORRECTION⟧

U7-C LANDED WHOLE (CofactorDist.lean, 663 ln: the window page at
θ·loglog X + 25 with the −logloglog gain discarded; the amended-pin twins;
THE COLLISION LEMMA at the asymmetric two-caps stone — MANDATORY, the
symmetric max-form gives exactly the floor with zero margin; the θ-EXACT
cancellation (1/32−θ)L + (θL+Cw) = (1/32)L + Cw is the pin's job, by ring;
K² = 3/32 + √2/16 ≈ 0.1821, margin 0.0679; pocket_collision_window = C-1∘C-3
the single U7-D consumable; both C-4 directions shipped — my brief's
direction error caught by the executor).

**MARGIN CORRECTION (executor's catch, kernel-proven both ways)**: V5's
"margin 1.707×" is FALSE in the 4th decimal — 500·θ₂₉₃ = 1.70674…;
exit_margin_293 proves 1.706/500 ≤ θ₂₉₃ AND exit_margin_293_sharp proves
θ₂₉₃ < 1.707/500. The ratified amendment stands at **margin 1.7067×**;
exit_beats_c0_293 intact at ε ≤ 1/1000. (JYH INFORM at morning — precision
only, nothing substantive moves.)

**THE X₀ TOWER as-split** (collisionGate_of_five): five charges each ≤
0.0135·loglog X; the floor's own C ≈ e^100 forces loglog X ≳ 2·10⁴⁵ ⟹
X ≳ exp(exp(2·10⁴⁵)) — consistent with Z-3's estimate; IN-STATEMENT always.
RESIDUAL (pre-U7-F): the asymptotic discharge ∃X₀ ∀X ≥ X₀ collisionGate
[B/C, 150–250] — folded into the U7-D brief as an optional stone.

## ⟦V5d — U-7 COMPLETE (U7-F as-built)⟧

ALL SEVEN U-7 LANES LANDED WHOLE (A/B/C/D/E/F + the W4 pair). U7-F's route
findings: (1) **the per-x dichotomy via the EMPTY-WINDOW COLLAPSE**
(gxDatum g 1 0 x = g — caseA_partial_supply at the trivial window IS its own
per-x slice; a general device for any damped-family ∀x→∀x lemma; iron rule 1
never engaged). (2) **the ascent problem DISSOLVED**: the dichotomy runs at
the GLOBAL X — the pocket (an upper bound) descends free by scale
monotonicity; only the FLOOR pays, once, via the Mertens tail
2(S(X)−S(k₀)) carried as an EXPRESSION inside cofactorMfl (the descent gate
verbatim: (1−1/loglog X)·log X ≤ log k₀; the CASE-A factor
e^{(2/e)(S(X)−S(k₀))} visible in caseAS_293; the leading grade at the
GLOBAL (log X)^{−ρ₂₉₃}). (3) cofactor_Rbd = 3·max(2·caseAS, farSupS) — no
disjunction survives; the hypothesis union enumerated in the docstring
(the ∀x arms GONE — manufactured by the dichotomy). (4) **F-3 THE PRIZE:
tL_supply_discharged COMPILED** — tL_main_sumsq's Rbd hypothesis discharged;
the 𝒯_L branch has NO co-factor hypothesis; the only new socket is the
per-t geometric bundle hTL (𝒰-side, stated not assumed). (5) F-4 with the
collision gate DISCHARGED at the explicit Z-3 tower. Non-vacuity
spot-checked (M ≤ X live at 0.74X; the loglog gate live with ~10⁴³ spare).
**hU's remaining work: U-9b/c/d (the serial balance) ONLY.**

## ⟦V5e — U-9 STRUCTURAL CLOSE (U9BCD as-built) + THE PRICING RESIDUALS⟧

hU is STRUCTURALLY SUPPLIED: the split is an IDENTITY (filter p / filter ¬p
at ε := δ′ — nothing lost at the branch seam); the composition costs 4·|I|
(CS + parity halving); the j-sum telescopes to 1/(⌊H log P⌋−1) — MR's
1/log P in the only form the kernel signs; **hU_discharged COMPILED into
prop_A3_T1_row_split_weighted's hU binder** (the station plug REFUSED for
three reasons, banked: t₁-free vs produced; the datum mismatch — the
station's hMcap is at seamCoeff (ellLin g), U-7's at ellLin g, DIFFERENT
objects, the consumer supplies both; the one-line consumer step).
hU_balance_beats_door at the RATIFIED θ₂₉₃, margin 1.7067×. The TannGate
WORKS (supplies hκ30 via kappa30_of_TannGate), not decorates. The far-leg
geometry DERIVED from the ball removal, not assumed. **Ms ≠ Mt** (different
roundings of the co-factor length — a false byte-fit avoided; both
parameters carried). Honest slack: the 𝒯_L side carries (log X)^{−2θ}
spare; the 𝒯_S side pays |I| twice (absorbed by ε² = (log X)^{−200},
carried explicitly). TS-budget non-vacuity (arithmetic, not kernel):
η ≳ 1/(2 loglog X) at the top block — the consumer must not pick η smaller
(consistent with V4a's η/(2J) slack).

**THE PRICING RESIDUALS (U9PRICE-WAVE — the LAST hU work):**
P-a [C, 400–700] discharge hmain/hrem at the full pin (H := H83, P := P83,
Q := Q83; price card(ramI); Lemma 12's three error rows into E);
P-b [B, 100–150] hKS via ramRcoeff_mass_le + the harmonic-square page
(Ms·Σ 1/m² ≤ 4); P-c [B/C, 150–250] hRbdU — cofactorRbd monotone in k₀/M
across the block range.

## ⟦V5f — hU FULLY PRICED (U9PRICE as-built): §8.3's hU IS DONE⟧

ALL FOUR STONES + THE PRIZE: **hU_fully_priced** — the row's exit at
8S² + the 𝒯-leg + 2(Tann/X+1)(log X)^{−θ₂₉₃+ε}, all four balance
hypotheses (hKS/hRbdU/hmain/hrem) DISCHARGED at the pins;
priced_exit_beats_door at ε ≤ 1/1000 → (log X)^{−1/500}. The card page
deliberately discards the 1/loglog (the 𝒯_L spare pays it); the floor page
at 4 ≤ log X; the 𝒯_L leg collapses to 864·C_q·C_R²·(log X)^{−3θ} —
V5e's spare IN LEAN. WORST-END VERDICT: the two arms disagree (caseAS worst
at smallest k₀; farErr's numerator at largest Mt) — R̄ is the MIXED corner
(kmin, Ymax), not a single block. TWO HONESTY CATCHES: (i) the
SILENT-VACUITY catch — R̄ ≤ (log X)^{−ρ} without a constant is vacuous
(gradeAbsConstC > 1); C_R carried, absorbed by the numeral-vs-growing-power
gate; (ii) the Ms sandwich makes the η ≳ 1/(2 loglog X) floor ENFORCEABLE
BY INSPECTION (two in-file binders).

**RESIDUAL GATES (all in-statement by design, law #253):**
R-1 [B, ~100] R̄ ≤ C_R·(log X)^{−ρ₂₉₃} — the S(X)−S(k₀) Mertens conversion
(descent_tail_le's page, already landed in CofactorSupply — likely a small
composition); R-2 EP2's own page (Lemma 12's 1/P row) with the gate
12·EP2 ≤ (log X)^{−θ}; R-3 the three numeral gates (C_q-vs-power; the
δ'-level KS gate; 8640 ≤ (log X)^ε). These ride the statements; the
consumers discharge at the pins. **hU's supply chain is COMPLETE.**
THE ROW'S REMAINING WORK: the 𝒯-leg (§8.1/8.2 — TLEG-SCOPE dispatched),
the A-10 far arm, the terminal assembly.

## ⟦V6 — TLEG-SCOPE VERDICT: THE FLAT-δ WALL (a true giant) + ROUTE G + THE GRADED GATE⟧

**THE WALL (pin-free, all corners dead)**: the row's 𝒯-leg is IMPOSSIBLE at
the landed flat-δ BlockSmallAt. The 𝒯-side needs δ ≲ Q_j^{−1/2} (the
co-factor mass e^{v/H} at the top of I_j); the 𝒰-side floor forces
δ ≥ K₀·P_J^{−1/4} (Lemma 8's thinness exponent). Collision: P_J^{1/4} ≲ 1 —
contradiction for every P_J > 1, independent of T/Tann/X/V/η/pins. MR's
e^{−α_j v/H_j} graded threshold is LOAD-BEARING TWICE (pays the co-factor
mass in (23) AND calibrates Lemma 8's exponent to 2α_j at the block's own
base). CENSUS: the engine room ~40% landed (Lemma 12-on-subset, Lemma 13,
MVT, the partition frame, co-factor mass); the §8.1/8.2 CONTENT 0/9 landed;
prop_A3_T1_row_moment is a DIFFERENT object (it ASSUMES the eq-(24) split
as hsplit — supplies what the seam row proves, not what it leaves open).

**ROUTE G (the only route — MR's own (21), restored fidelity)**: a parallel
graded partition family in NEW files (process-safe, iron rule 5 never
engages): G0 graded predicate/partition/row [B, 460–680] → G1a graded
thinness (CLEANER than flat — the pigeonhole disappears; log V/log base =
α_J exactly) [C, 300–450] + G1b THE V-SPLIT hU REPLAY [C, 700–1200] → G2
§8-preamble [B/C, 490–830] → G3 §8.1 E₁ [B/C, 320–520] → G4 §8.2 E_j
(G4c MULT-SHIU = the genuinely new stone [C, 500–800]; G4a/b/d/e/f
[C, 1200–1850]) → G5 collection+exit [B/C, 600–950].
**𝒯-leg total ~4,600–7,400; seam terminal total ~6,000–9,500 (V4's
estimate under 2.5–3×).**

**⚠ THE JYH GATE (morning, decision-ready)**: ratify Route G before G1b's
~1,000-line hU replay is spent. The case FOR: it is MR's own (21) — the
flat δ was OUR simplification, now proven impossible; every corner is dead;
process-safe. The cost: ~doubles the seam-terminal estimate. The
alternative: none found (the scoper worked five corners, all dead).

**UNGATED NOW (dispatched)**: W-0 SeamTerminal.lean — the three-leg terminal
with the 𝒯-leg as a NAMED BINDER hT (the 𝒯-leg becomes a socket, not a
blocker; the two-M option-(A) exit + the Tann ≤ X/2 MRT guard) [C,400–700];
W-1 FarArm.lean — the A-10 far arm (the ball-centre dichotomy) [C,300–500];
W-2 the hU residuals R-1/R-2/R-3 (closing the hU chain COMPLETELY;
kept separate from G* — the parameter-regime mixing risk) [B/C,350–600].
The three composition seams for W-0 banked from the scope: t₁
produced-then-fed; the TWO DATA (seamCoeff (ellLin g) vs ellLin g — both
supplied, no adapter); the far arm's dichotomy.

## ⟦V6a — THE SECOND WALL (HURES, kernel-certified) + R-2/R-3 CLOSED⟧

**R-1 REFUTED AT THE LIVE Tann**: farErr carries 1 + log(3 + Rmax(1+log Y))
at Rmax ≥ Tann, and TannGate FORCES Tann ≥ exp(30(logX)^{1/2}) (its
polylog-failure is itself a theorem) — against only √(log kmin) ≤ √(log X)
below. Kernel-certified: farErr_TannGate_floor (an ABSOLUTE floor
120·ballSupC), Rbd_TannGate_floor (360·ballSupC ≤ R̄),
Rbd_grade_refuted (¬(R̄ ≤ C_R(logX)^{−ρ}) past an explicit threshold), and
**Rbd_and_Cq_gates_collide — the two V5f gates JOINTLY unsatisfiable (an
explicit CEILING on log X)**. At the live row height the far error GROWS
like √(log X). No escape (log kmin ≤ log X structurally). THE REPAIR
TARGET stated + proven usable: farErr_le_of_ambient_gate /
Rbd_grade_priced_of_ambient — but ambient_cap_below_TannGate_floor shows
the repair window is EMPTY as-built. **The fix must remove log Rmax from
the far-arm transfer error — a CofactorBall/A-10 DESIGN question**
(FARERR-SCOPE dispatched). R-4 correctly REFUSED (would be vacuous where
it matters). SECOND SILENT-VACUITY CATCH: the pricing needs the LOWER gate
seamRad X ≤ Rrad (hU_fully_priced carries only ≤) — the consumer must pin
Rrad = seamRad X. SCALE-MISMATCH CATCH: hErow reads X, Lemma 12 reads Xd;
they meet only under X ≤ Xd (unpinned — the consumer's).

**POSITIVE (landed)**: the caseAS arm priced END-TO-END with C_R explicit
(gradeCR Cb; the descent factor a NUMERAL e^13); the max's 2√2/R half
collapses as V5f said (farErr does not); R-2's assembly landed
(E_priced(_row_scale); EP2 free at P83 with (logX)^{2−5θ} spare) with the
ℓ²-mass residual EXACTLY specified ([C, 200–300]: the SmallStones
p²-route is TOO LOSSY for §8.3 — kernel-checked insufficiency; the
ℓ²-preserving route mapped in four steps); R-3 ALL THREE GATES DISCHARGED
at explicit thresholds (numeral_gates_discharged).

## ⟦V6b — FARERR-SCOPE VERDICT: the wall structural, the repair three stones + THE UNIFIED MORNING RULING⟧

**Q1**: log Rmax is GS 7.1's OWN d-split exit factor (Renormalise :759/:1003
→ ballErr BallSup:256 → farErr CofactorBall:175) — intrinsic, not artifact;
sharp-R5 buys nothing. The transfer is informative only while
log Rmax ≤ (log W)^q, q = 1/2 as built.
**Q2 (decisive)**: the per-t LOCAL dichotomy is REAL and cheap (localize
CofactorSupply:312's by_cases to |v−t| ≤ T*; the pocket branch hands
|t−t₁'| ≤ T* free, replacing the Dmax supply) — BUT T* ≥ exp(2√L) by pure
AM–GM (log T* = log y + L/log y; η = 1/log y FORCED by the smooth Euler
leg). The need: q ≥ 1/2 + 2θ₂₉₃ — **the wall is a miss of exactly 2θ₂₉₃**.
The consumer demand re-derived: R̄ ≲ (log X)^{−2θ} (not −ρ); 1θ of slack
exists, nowhere near enough. q sharpens 1/2 → 3/4 FREE from data CASE B
already has (the pocket's real cap α = 1/32 was converted to the crude 1/8
— √(2P)·√(P/32) = P/4; the threshold exp(exp 165) ≪ the collision tower).
**THE THREE STONES**: R1 [B/C, 200–350] the localized dichotomy
(CofactorSupply:293–352, CofactorBall:539–612, one binder USetPrice:602;
Rmax → Tstar(M, log M)); R3 [B, 250–450] the 3/4-budget twin
(budget_le_quarter at α = 1/32 + ballErr34/transfer_at_scale_34/farErr34 +
the exp(exp 165) threshold; new stones only, BallSup:120/144/165/256/307 +
SmallStones:152 as sources); **R2 [C; THE JYH GATE] the y re-pin
log y = L^{2/5}** — parallel pin family RECOMMENDED (~1500–3000; in-place =
statement changes on landed binders, Fable/JYH tier, NOT recommended — the
hSup station rides the same pin and must not move). The re-pin is mostly
RE-INSTANTIATION: LambdaMass:243's S1′ is ALREADY free-y (gates hold at
exp(L^{2/5})); FarStar's far_mass_cancel residual is e^{−2} at ANY y;
widthKampBr IMPROVES. R1+R3 alone leave farErr divergent (the certificate
pair, not the closure); R2 closes: farErr ≈ 8C′·L^{−3/20} ≤ L^{−2θ} at
L ≥ 10⁶⁷ (free vs the tower). The numbers table + the three FREEZE RISKS
(supF_pret_pointwise's interior at the new y; hidden y-numerals beyond the
pin_basic64 triples; the C_E-dependent X₀ — the L^{2/5}-not-L^{1/2} choice
pinned HERE, not left to the executor) — per the scoper's report
(task output banked by reference; the ledger carries the ruling).
**ROUTE G INTERACTION — THE AMENDED RULING**: the graded family cannot
relax the Rbd demand, and **G1b's ~1,000-line hU replay would DUPLICATE the
broken far arm. HOLD G1b until R1/R2/R3 land.** Route G's SHAPE may be
ratified independently; the replay lane waits. Wall stones stay TRUE
post-repair (they carry hDmax as a hypothesis that simply goes unsupplied
— the refutation becomes historical). SEQUEL BANKED: FarClose repair (ii)
(the Plancherel far region) — its refuting y-gate LOOSENS under R2; if R2
lands it would retire T* entirely.

**THE MORNING SLATE (unified)**: (1) R2 gate — the parallel y-pin family
(recommendation: YES, parallel form); (2) Route G — ratify the shape, HOLD
G1b behind the far-arm repair; (3) R1+R3 dispatched ungated tonight;
(4) the standing INFORMs.

## ⟦MORNING RATIFICATIONS (JYH 7/26): R2 + ROUTE G SHAPE⟧

(1) **R2 RATIFIED**: the y-pin parallel family at log y = L^{2/5} (no landed
statement touched; the V6b freeze notes bind: the L^{2/5}-not-L^{1/2}
choice is PINNED here; the three freeze risks ride the wave brief).
(2) **ROUTE G SHAPE RATIFIED; G1b HELD** behind R2's landing (the far-arm
replay must not be paid twice). G0 (the graded partition core) is
far-arm-independent — fires now. R3's Zeno (the F-2 assembly twin at the
3/4 transfer, ~150–200 mechanical) rides with the R2 wave.

## ⟦V7 — THE SECOND WALL CLOSES (R2 as-built) + THE WIDTH RULING⟧

**farErr34_local_closes (KERNEL-CERTIFIED, the R1+R3+R2 composition)**:
farErr34 W Y (Tstar2 Y (log Y)) ≤ (log Y)^{−ρ₂₉₃} at Y ≥ Y₀ explicit,
FREE of the TannGate tower; the gate form at a free target exponent serves
both ρ₂₉₃ and 2θ₂₉₃ (three_twentieths_gap proven). The chain: log Tstar2 =
L^{2/5} + L^{3/5} EXACT → 4L^{3/5}/(L^{3/4}/2) = 32C·L^{−3/20}. FarStar
re-instantiates at y₂ with the SAME e^{−2} residual ("at ANY y" now a
theorem); the F-page does NOT move (the σ-sup attains at the LEFT endpoint
1/L — pin-blind); supF_pret_pointwise pin-agnostic (freeze risk i
DISCHARGED); the E-slot closes for EVERY C_E (risk iii); the hidden-y
census enumerated (risk ii) with ONE real hit:
**THE BANDWIDTH HIT + THE RULING (maestro)**: pin_width_gates' 4th
conjunct y ≤ 2·T₀⁸ ≈ 512·L⁴ FAILS at y₂ (kernel-certified). RULING: the
width A was ALWAYS free (V3a); it STAYS at the old scale A := (L⁴/2)^{1/8}
≈ 0.92√L; only the y-gate discharge changes — 2A⁸ = L⁴ ≤ n now via
n > y₂ ≥ L⁴ (free at L ≥ the pin2 gate) instead of y = L⁴ exactly. A
[B]-tier twin of the pin lemma, NOT a design block; no statement changes.
**RESIDUAL WAVE (PIN2-REST)**: the width-gate twin [B, 60–100];
seamGateRstar2 + the gate package at Tstar2 (log manifestly increasing)
[B, 120–180]; the SupClose pin layer (joint_supF_pin_trunc2 /
joint_cs_trunc_pin2 / rhs_grade_at_scale_trunc2) [B/C, 200–300]; FarStar §5
at y₂ (closed_star2 / socket_star2 / ball_sup_closed_star2) [C, 250–400];
caseAS at y₂ re-read [B, 100–150]; cosmetic adapters. G1a (graded thinness)
ALSO ungated — fires with it.

## ⟦V8 — THE SEAM ROW CLOSES: seam_row_calibrated⟧

THE STATION IS DONE. seam_row_calibrated (SeamCalibration.lean): the graded
seam row — the ball leg at the ratified two-M/option-(A) grade + the
𝒯-leg at MR's §8.1 exponent + the 𝒰-leg beating the door — WITH NO
INTEGRAL ON THE RIGHT AND NO LADDER HYPOTHESIS STANDING; 23 ladder-reads
discharged from ONE CalFrame (11 scalar gates, inhabited at explicit
numerals — G = 768 the smallest admissible base at η = 1/12; genuinely
non-vacuous, block-nonempty certified); the surviving frame = 69 binders
ENUMERATED (4 norm contracts + CalFrame + 2 calibrated replacements + 3
𝒯-frame + 59 𝒰-side analytic gates carried verbatim). THE CORRESPONDENCE
FINDING: no j-level talks to the §8.3 pins — the 𝒯-ladder sits STRICTLY
BELOW the 𝒰-window (ladder_below_station, via the landed pins);
Jset := Jb (MR's one J). The ℕ-ladder ruling: calP/calQ base-2 powers
(MR's (4) is not ℕ-valued; (2)/(3) — what CellGates transcribes — are
proved; (4) is one witness, docstringed not hidden). Zeno (none blocking):
the anchor-cutoff coupling A ≳ Jb³ log Jb (MR's own quantifier order,
visible in ONE place); Jset > Jb would need LevelGates on the gap.
**THE WEEK'S ARC COMPLETE: hSup → hU → the two walls → Route G → THE SEAM.
NEXT: the door road — A3a-R3 → thm_A2′/A1′ → §9 → S7 → S9 → Siegel →
S10b/S11 → COMPOSE at log_chowla_two_budget_head.**

## ⟦V9 — DOOR-SCOPE: THE ROAD BELOW THE SEAM (the execution map)⟧

**THE CONSUMPTION MAP**: seam_row_calibrated is PURE SUPPLY (zero consumers);
its designed consumer is lemma14_contour (Lemma14 :295). EXACT on the hard
axes (the 1/15 inner cutoff IDENTICAL TERM; the line Re = 1; the grade
shape at θ₂₉₃; η = 1/12 CONSISTENT with the s8-freeze card; our §8.1
P₁^{−1/4} BEATS MR's). **THE DECISIVE FINDING: hMsup's ∀T binder fires
ONCE (Lemma14 :346/:463 at T = X/h₁ only)** — one supply instance covers
it; prefer the additive lemma14_contour_of_Msup_at variant. FOUR cheap
breaks: (1) hrange is on s0's ELEMENTS — fix s0 := Icc.filter (X < ·) +
spoly = dpolyA (J2); (2) **ha : ‖a‖ ≤ 1 is NOT in the 69-frame — a NEW
binder at the junction, flagged never silent**; (3) no seamAnn ↔ two-
intervalIntegral bridge exists (J1; needs 0 < seamT0 from 1 < X); (4) hSup
supply is flat-granularity — the graded station re-assembly (J5; ball
machinery predicate-free). Column A (prop_A3_T1_row_moment) is HERITAGE —
its hsplit is flags-recorded unsatisfiable; do NOT wire; its E1/Ej/largeT
rows remain engines.

**WAVE 1 — L14-JUNCTION (dispatched)**: Salt/MR/SeamLemma14.lean, J1–J6
per the scoped table (J1 the split [B,100–160]; J2 the filter/hrange
repair [A/B]; J3 mid-range at Tann := X/h₁; J4 Msup at Tann := 2X/h₁ + the
single-instance variant; J5 the graded station plug at S := ballSupS-form;
J6 the exit lemma14_contour_seam_supplied). ADDED BINDERS: ha; h₁ ≥ 2
(the 2X/h₁ ≤ X gate); h₁ ≤ h₂ ≤ X(log X)^{−1/5}; CalFrame at η = 1/12.
GATE HAND-CHECKS ALL PASS in the door regime (TannGate at log X ≳ 950; H83
at X ≥ exp(10^88); ballSupC34 at log Ymax ≳ 10^31). TRAPS: the ∃-prefix of
seam_row_calibrated vs lemma14's implicit block (the binder-position
check FIRST); Xd vs X are DIFFERENT symbols; the numeral-exponent linter
(keep calP anchors symbolic); Lemma14's PRIVATE helpers will bite J6
(re-derive verbatim); the J-factor trap.

**A3a-R3 (the next design block)**: the kernel IS required — the scoper
RAN the kill-check (the finite dyadic extension without the kernel fails:
the un-kernel'd cost (log X)^{4+ε}·Msup ≫ 1 at θ₂₉₃); the kernel is
destroyed at Lemma14Vtail :894's early CS; the closed forms are LANDED
(uKernel/ramp/tent); R3-a..R3-f [C, ~1020–1780] with R3-c the risk stone.
ANTI-TRAP: hsup-design :203's "min-kernel irrelevant" is about the hSUP
socket — a DIFFERENT object; do not suppress R3.

**THE CENSUS (honest)**: junction 750–1250; Σ_j lemma12Rows pricing (the
typical-density wire — **UN-PRICED inside the closed row: the seam row is
a FORMULA not a number**) 400–800; A3a-R3 1020–1780; hfloor provenance
(flags :11808 live) 300–500; thm_A2′ 800–1500 (under-budgeted at 500);
thm_A1′ 300–500; §9 glue 1000–2000 (Lemma 5 critical); S7 ARC 2500; S9
4000 (design block DISCHARGED 2026-07-26: the A.8 defect is H-block lane and
already repaired+landed as `renormalise_shifted`; S9 is the straight §4
major-arc port, band 3250–5200, freeze at s9-freeze-0726.md; preconditions
P-1 exact-denominator S7 exit + P-2 W choice); Siegel arm 500 (the real-χ exceptional gap — pilot-only, now
flagged); S10b 900 → LANDED 2026-07-26 (RegimeHead.lean: gJoin +
chowlaRegime_exists_param_head at arbitrary g + epsFloor; M0/X0MR typed slots
await S9; the S11 boundary: g threads inside SpineFinal, not post-hoc);
**H₀door: NO LEAN DEFINITION EXISTS (~150, unowned —
JYH-informational)**; S11 COMPOSE 600 (spine_False_core_xi is PRIVATE —
the wave appends INSIDE SpineFinal.lean). **TOTAL ~13.3k–19.9k, zero
D-nodes, NO live JYH gates** (the spine-budget-freeze PENDING-JYH text is
STALE — A1+A2 ratified 7/19, pilot :9725 + mr-freeze :52). GO: W1
junction → W2 (R3-DESIGN ∥ SEC9-GLUE ∥ HFLOOR-FIX) → W3 (the pricing ∥
S7) → W4 (R3 → A2′ → A1′) → W5 (S9-design ∥ Siegel ∥ S10b) → W6 (H₀door →
COMPOSE).

## ⟦V9a — A3a-R3 CLOSES: THE DAMPED-COEFFICIENT ROUTE⟧

R3 landed WHOLE, R3-c UNDIVIDED, via a route SIMPLER than the spec: the
kernel's 1/s moves ONTO THE COEFFICIENT (dampA: B(t) := A(1+it)/(1+it));
vSeg = I·((x+h)G(x+h) − xG(x)) EXACTLY (no Fubini, no side conditions —
the early-CS destruction site never runs); the LANDED tent machinery
applies to G; ‖B‖² = ‖A‖²/(1+t²) IS the kernel. THE SPEC CORRECTION: the
(X/h₁)² factor REQUIRED not slack (proven; cancels exactly at
dyadic_tail_proper's 8·Msup/W²). THE GAP CLOSES: lemma14_contour_kernel
N-uniform at Tcut = 2^N(X/h₁); Egap → 0 at δ ≍ 2^{−N/2} (the old
irreducible floor GONE). No improper limit (the monotone limit unowned,
likely never needed). Residual: the δ-instantiation (consumer's).

## ⟦V9b — TYPDEN's KERNEL-CERTIFIED REFUTATION + THE K-LADDER RULING⟧

**THE REFUTATION**: log calP/log calQ = 1/2 EXACTLY at every level (calQ =
calP² by construction) ⟹ Σ_j = Jb/2 (sum_calibrated_ratio_eq) — MR's
eq-(28) needs the j²-decay of their (4)-ladder (log P_j/log Q_j =
log P₁/(j² log Q₁), Σ = π²/6·δ/4-shape); at the calibrated pin δ = 2 —
VACUOUS. calibrated_ratio_not_MR_shape: no constant ρ gives ρ/j². The
pricing wire itself is GENERIC (the ratio symbolic on the right — only
the calibration instance changes). **THE RULING (maestro, process-safe):
the PARALLEL K-LADDER — calQK A G M j := 2^((j²·M)·calE)-shape in a NEW
file; G_gate absorbs K as 64K ≤ ηG; A_gate_log gains only log K; the
SeamCalibration theorems re-derive at the K-family; NO landed edit.**
TWO MORE PRICING FINDINGS: (ii) the p² row's 64/P² is USELESS at scale
(X_d ≥ P² ⟹ every level ≥ 64) — the direct route Σf² ≤ (max f)(Σf) with
2^ω(n) ≤ n gives MR's 16·log₂(2X_d)/(X_d·P) [B, ~100]; (iii) H₁ = 2's
inhabitant makes the window row O(1) — H1_pin permits P₁^{1/6}; a better
inhabitant [A, ~30]. CONSUMER DEBT: X ≍ X_d (the junction's two symbols)
owed at the wiring. CALREPIN-WAVE dispatched (all four items).

## ⟦V9c — THE K-LADDER LANDS: THE SEAM ROW'S FORMULA IS A NUMBER⟧

CALREPIN whole: calQK := 2^((j²M)·calE) — **no calEK needed** (calP
unchanged; only the Q-exponent moves — the deviation rational, recorded);
log ratio = 1/(j²M) EXACT; **THE HONEST Σ-AT-M PAGE KERNEL-RUN**:
sum_ratioK_le ≤ 2/M uniform in Jb (Σ j⁻² ≤ 2 — Basel declined, the
factor-2 paid in the pin: M = 8/δ vs MR's 4/δ); eq28_clears_of_M with the
demand-side gate IN-STATEMENT; the pinned inhabitant clears at 1.9×
(A=65536, G=2457600, M=800, δ=1/100; G_gateK EXACT — G = 768·Jb²M the
smallest base, mirroring the landed G=768). The 12 LevelGates fields:
5 moved (the K in the gates), gate-3's j²-cancellation STILL FIRES exactly
(48K ≤ ηG the true demand; 64K leaves 4/3); the rest verbatim. K-2 the
p²-direct route (16·log₂(2X_d)/(X_d·P) — MR's grade, replacing the ≥64
row); K-3 H₁ = P₁^{1/6} SYMBOLIC (H1_pin with equality — the largest
permitted width; the window row now negligible). K-4:
**seam_row_calibratedK + sum_lemma12Rows_priced_calibratedK — the density
collection C·(2/M), THE FORMULA IS A NUMBER** (modulo the p²-K-wire
[B, 150–250 mechanical — P2WIRE dispatched] + the Basel upgrade [~40,
optional] + the K-times-harder cutoff gate (asymptotically free, the
consumer's X-threshold moves — unexamined numerically) + the δ-coupling
at the consumer). NEW TRAPS: norm_num UNFOLDS closed calP-terms into
2^65536 (never let norm_num/simp see one — explicit show-rewrites);
linarith defeated by compound-argument log atoms (eliminate first);
card_le_card_of_injOn's beta-unreduced equation (ascribe); Nat.pow_pos
implicit exponent; the four privates transplant-mandatory.
