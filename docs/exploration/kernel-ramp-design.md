# THE KERNEL-RAMP BLOCK — the last obstruction of the terminal assembly

*Maestro design block, 2026-07-23 ~11:35. Status: **FIRE (verified
~12:20) — BOTH PAGES CLOSE AT GRADE.** RAMP-TAIL: the cancellation is
EXACT ALGEBRA (A2*(2/T0) = 2(X+h)^a); tail = (1/pi)(1+o(1))*grade,
log-free, all corners. RAMP-HEAD: HEAD-CLOSES via route A' — the
landed dirichlet_plancherel COUPLES width to line (the scaled-c trick
dies on the lemma) BUT its PROOF separates them (cexp_pois_full takes
width a and frequency theta as free parameters) — the width-a clone
widthA_plancherel is clean; the off-diagonal-kept evaluation decays
like C*L/a via the short-interval grain (back in play after all);
the band count multiplies only the tiny diagonal floor (log y / y
grade — route B's own discovery repurposed); head = C*L, the tail =
C*L even crudely, the alpha-integral's 1/L cancels: NET = CONSTANT*X*
e^{-cM}. Routes B (the lossy 2T+20N MVT: leaks sqrt X at y=X^{1/4})
and C (no-split: branch-2 reinstates the ramp; branch-1 diverges)
both honestly killed. ONE named residual: the y=sqrt-L extreme corner
needs a<=n^{1/8} — carried as the bounded (loglog)^2 concession or a
PNT-lift coda (siegelWalfisz in-corpus); a coda, not a leak. THE
RAMP-WAVE fires: 8 stones, ~700 ln, Salt/MR/HeadGrade.lean.* THE SITUATION: SHARP-SCOPE's
isolation numerics prove that with the off-diagonal kept (S-ii, now
landing) and the g-datum floor (S-iii, landing), the ONLY remaining
gap to the grade C″·X·e^{−cM} is the √L kernel ramp — the amplitude
(X+h)/h = √L+1 that enters when the |s|⁻² branch of hat_mellin_bound
is used GLOBALLY to feed dirichlet_plancherel's Lorentzian weight.
The ramp is an artifact of composition order, not of the kernel: the
kernel's honest L¹ mass is X·log L (HGRADE's landed sharp bound).*

## The load-bearing claim to VERIFY FIRST (the scoper's own caveat)

CLAIM-0: the current crossKer wiring (JointHead:76 + mixed_weight_cs)
genuinely requires the kernel to supply the |s|⁻² Lorentzian weight —
i.e. the √L enters exactly and only through norm_hatKernel_le's
branch-2 amplitude. VERIFY against the actual Lean (the CS step's
weight w := ‖hatKernel‖ vs w := Lorentzian; which form the landed
mixed_weight_cs actually takes — it is weight-AGNOSTIC (any w ≥ 0)!
— so the wiring may already permit Candidate 1 with no new CS).

## Candidate 1 — THE τ-SPLIT (the primary; fully inside the corpus)

Split crossKer's τ-integral at the branch crossover T₀ := 2(X+h)/h
(= 2√L-grade at the pin):

- **TAIL |τ| > T₀**: branch-2 (amplitude X√L·(X+h)^{−α−β}, weight
  1/|s|²): the tail mass ∫_{|τ|>T₀} |s|⁻² ≤ 2/T₀ = 1/√L-grade —
  amplitude × tail-mass = X-grade AT GRADE with the window legs'
  crude sup (the P-legs' sup ≤ their mass, L-grade each... WORK IT:
  X√L · (1/√L) · [P-sup²]... the P-sup² is (L·(x/y)^β-grade)² — vs
  the head's Plancherel L¹... the tail must come out ≤ the head's
  grade; the tail's smallness budget is 1/√L against the sup-form's
  L² vs the Plancherel's single-L: net √L·L²·... — NO: bound the
  TAIL's ∫|P₋||P₊|/|s|² by CS-with-Lorentzian on the tail region
  (mixed_weight_cs at w = the tail-restricted Lorentzian) → the
  tail Plancherel masses × 1/T₀ — dirichlet_plancherel is full-line;
  a tail-restricted variant ≤ the full-line one (nonneg integrand:
  monotonicity — a one-line lemma) → tail ≤ X√L·(1/√L… no, the
  1/T₀ improvement needs the RESTRICTED second moment... honest
  route: ∫_{tail}|P₋||P₊|w ≤ (sup_{tail} extra-decay) × full
  Plancherel — the Lorentzian at |τ|>T₀ is ≤ 1/T₀²·... CAREFUL:
  1/(c²+τ²) ≤ 1/τ² ≤ (1/T₀)·(1/|τ|)... the executor must do the
  dyadic version; the DESIGN CLAIM: tail ≤ (1/T₀)·[the head's
  form]·polylog — verify in the pass).
- **HEAD |τ| ≤ T₀**: branch-1 (amplitude X-grade·(X+h)^{−α−β}, decay
  1/|s|): CS with weight w := 1/|s| (mixed_weight_cs is
  weight-agnostic — landed) → per-leg ∫_{|τ|≤T₀} ‖P‖²/|s| dτ. The
  evaluation: dyadic in |τ| (bands |τ| ~ 2^j, j ≤ log T₀): per band,
  (2^{-j})·∫_{|τ|≤2^{j+1}}‖P‖² — and the SECOND MOMENT over a finite
  range via the corpus's continuous mean-value machinery
  (ParsevalSL's lpoly_mean_sq_bound — READ its exact form; or the
  landed dirichlet_plancherel itself at a scaled c ~ 2^j: the
  Lorentzian at width c ≈ 2^j IS the band-restricted second moment
  up to constants — the SCALED-c PLANCHEREL TRICK: ∫_{|τ|~2^j}
  ‖P‖²dτ ≤ (c²+τ²≤2·2^{2j} on the band)·∫‖P‖²/(2^j... i.e.
  ∫_{band}‖P‖² ≤ 2·2^{2j}·∫ ‖P‖²/((2^j)²+τ²) = 2·2^{j}·π·
  [dirichlet_plancherel at c := 2^j]) — the c-scaled diagonal
  Σ‖b‖²·e^{−2^j|log m/n|}/(mn)^{c₀}... the KEY GAIN: the DIAGONAL
  second-moment mass Σ_{win} Λ(n)²/n^{2c₀−...} is (log y)·L-grade?
  — NO: Σ Λ(n)²/n^{2c₀∓2β}-ish over (y, X/y): Λ(n)² ≤ (log X)·Λ(n)
  crude gives L·(single mass) = L²... the honest gain needs the
  off-diagonal-kept form per band (S-ii's machinery AT the scaled
  c) — the pass must page this fully: the CLAIM: head ≤ X·polylog·
  (the S-ii single-L form)·log T₀, i.e. the √L never appears and
  the residual is log-powers ABSORBED by the B4 tolerance (the
  grade's o(1) headroom: (log X)^{−1/(32e)+o(1)} tolerates polylog
  factors ONLY if they sit in the o(1)... NO — polylog × X·e^{−cM}
  vs C″·X·e^{−cM}: a residual log-power is NOT absorbable; the
  head page must close to CONSTANT×X or the candidate fails; the
  pass decides).

## Candidate 2 — THE WIDTH RE-DERIVATION (h re-pinned)

The ramp is (X+h)/h; at h = X/polylog the ramp is polylog (vs √L).
The h = X/√L pin came from the freeze's desmooth economics (the
T-chain's Utail budget X·L^{−1/2}). RE-DERIVE: what does the T-chain
ACTUALLY need from h? (T1_decay_trivial's htail/hsplit binders; the
s2_tail_ledger; the V5-5 sliver bound's h-dependence — the sliver
mass ~ (h/y)·log X re-enters at larger h: at h = X/log^A the sliver
is X·log X/(y·log^A) vs E-grade X·log y/L: needs y·log^A ≥ L·...
WORK IT — the sliver gate y ≥ √L helps). If the T-chain tolerates
h = X/(log X)^A for some fixed A, the ramp becomes log^A and the
CRUDE route closes to X·log^{A+...}-grade... same absorbability
problem — polylog over grade is still over grade. Candidate 2 only
works if the ramp's log-power lands INSIDE a factor the assembly
already pays (e.g. folded into C″ via a re-pinned σ-integral) — the
pass prices it honestly. LIKELY WEAKER than Candidate 1.

## Candidate 3 — THE GHS REVERT (sharp truncation)

Replace the hat kernel by GHS's sharp x^s/s + explicit T-truncation
in the S1′ chain — the classical route. HONEST COST: re-opens the
representation layer (prop21RHS's kernel is frozen P21-3K-amended
hat; the S1′ chain consumed it verbatim) — a MULTI-AMENDMENT
cascade. LAST RESORT ONLY; the pass need not price it unless 1 and
2 both fail.

## The pass (firing now)

1. **WIRE-VERIFY**: CLAIM-0 against the actual Lean; then the
   τ-split's TAIL page (dyadic, honest) — is the tail ≤ grade?
2. **HEAD-PAGE**: the head's full page via the scaled-c Plancherel
   trick + S-ii's banded machinery — does it close to CONSTANT×X×
   e^{−cM}-grade (no residual log)? Numerics at the four corners
   mandatory. If a residual log survives: name its exact power and
   whether ANY corpus surface (the second-moment diagonal
   Σ Λ²/n^{2c}; the ParsevalSL forms) kills it.

Verdicts per the house schema; on FIRE the RAMP-WAVE closes the
terminal assembly; on HOLD the candidates iterate.
