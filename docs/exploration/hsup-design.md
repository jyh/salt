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
