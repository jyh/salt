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
