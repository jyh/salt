# SPRINT-2 GAP-U DESIGN (FROZEN off the B2 census; JYH-ratified "yes, let's do GAP-U")

*2026-07-17. The terminal, stated honestly per the census: GAP-U's
landing makes twin_razor_deficit's U-side unconditional — the P₁
no-go conditional on GAP-E ALONE (the one-hypothesis deficit), never
P₁ itself. The Zeno tripwire pre-armed by B2 is DISCHARGED by this
user discussion: the chain has a declared 3-node terminal.*

## Nodes
- **G3 (C, THE RISK — gated first): the F-continuation cert at
  s ∈ [3.9992, 4].** The [1,3] mass-ledger identity (Fchain =
  (3+M)/s) does NOT cover s = 4 — a genuinely new panel regime.
  The route: the linear-sieve DDE continuation (s·F(s))′ = f(s−1)
  on [3,4]: 4·F(4) = 3·F(3) + ∫_3^4 f(u−1) du with f the landed
  lower value; the numeric target F(4) = (2e^γ/4)·(1 + ∫_1^2
  log v/(1+v) dv) ≈ 1.0-grade — THE III.3″ WITNESS: the executor
  evaluates F(4) numerically (mpmath) BEFORE freezing a1up, with
  ≥ 1% slack, exactly as FchainPoint did for the switch window.
  CASE SPACE (the gate checks completeness): the s-regimes —
  [1,3] (the landed identity) vs (3,4] (the continuation) vs the
  seam s = 3; the panel machinery mirrors SuperPanelsE/O at the
  new regime.
- **G1 (B): the upper keystone at the A₁ carrier** —
  bjs_theorem6_windowed_upper (WindowedStep:402, instance-generic)
  at twinA1Sieve, the twin_A2_upper mirror: A1primeSum ≤
  XW·W·(Fchain + slack) + rem; the rem via the LANDED A₁ BV row
  (G2 = twin_A1_lower's hBV, reused verbatim).
- **G-U-CAP (B): the one-hypothesis deficit** — twin_razor_deficit
  with GAP-U discharged: p1RazorValue ≤ −δ·XW conditional on
  GAP-E alone, δ explicit from a1up vs the hypothesized e2lo; the
  honest docstring states the census verdict (the terminal is the
  sharpened obstruction; GAP-E remains the named missing theorem).

## Gate mandate (before G3/G1 dispatch)
(1) The DDE continuation identity's exact form vs the landed
RosserChain recursion (is (sF)′ = f(s−1) the corpus's convention or
does the landed chain use a different normalization? — read
RosserChain/FchainPoint at proof level; a mismatched normalization
is the classic tear); (2) the F(4) numeric evaluation + the a1up
slack; (3) the s = 3 seam (F(3) from the landed [1,3] side —
which landed lemma supplies it, at what window?); (4) the case-space
completeness; (5) the G1 carrier check (twinA1Sieve satisfies the
upper keystone's hypotheses — the same instance facts the lower
consumed, verify nothing upper-specific is missing).
