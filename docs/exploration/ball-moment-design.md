# THE BALL-MOMENT BLOCK (S3/S4) — the true last mountain, honestly zoned

*Maestro design block, 2026-07-23 evening. Status: **ZONES DISSOLVED
(ZONE-SCOPE ~17:10) — the head was ALWAYS annular.** Q1: the resonant
core is excised BY CONSTRUCTION (Decomp's U-set starts at
(logX)^{1/15}; the core's mass is the MOMENT row -- E1_row, landed,
no decay needed; J0 already declared center-M dead; even a literal
ball can't reach resonance: 1/16 < 1/15). Q2: the gap floor is
ALREADY LANDED and STRONGER than requested (dist_one_floor_pow has
NO upper cap -- the full (1-o(1))loglog floor on the whole annulus).
Q3 moot (contingency: delta0 <= L^{-0.023}, polylog-easy). Q4: E^2
clears with a FULL L to spare. THE LADDER: zone C alone -- landed
decay stones + ONE B-stone (the annulus measure x sup t-integral) +
ONE A/B (the E^2 corner), MODULO the single standing residual: the
S1'->spoly bridge (the Perron/Fubini, HalaszSeam:66-77 -- possibly a
STALE note post-v5; scope tomorrow). S4 PIN CORRECTED per the scoper:
annHead = the ANNULAR integral of spoly (sigma=1 line, MomentsA2:53
conventions), T0 = (logX)^{1/15}, upper T+(logX)^{1/16} matching
M_range VERBATIM. ROUTE LAW: the decay grounds through the SupF/
window_sup_decay route ONLY (the contour/k4 route is M-independent
by theorem -- T-0b's own record). Also: the HLOSS-WINDOW freeze note
is STALE (superseded by the landed T-1 chain) -- coda tomorrow.
ORIGINAL DRAFT BELOW (historical); the refuter pass follows its
report; the S4 object pin goes to JYH in the morning (statement-tier:
the T-0 card's ball geometry). Inputs: UHEAD-SCOPE's definitive map
(Uhead = an ungrounded socket everywhere; the intended object = the
ball-L² head of the seam polynomial); GRAND-COMP's structural finding
(the joint path grades mass; the decay lives on the window);
WINDOW-COMP's landed S1/S2 (the on-window pointwise decay + its
σ-integral, consumable).*

## S4 — THE OBJECT PIN (the JYH-tier proposal, stated for ratification)

Per the s8-freeze's int_U design and the T-0 card:

  def ballHead (a : ℕ → ℂ) (t₀ R : ℝ) : ℝ :=
    ∫ t in Set.Icc (t₀ − R) (t₀ + R), ‖∑ n ∈ (support), a n · (n:ℂ)^(−(t:ℂ)·I)‖²
  -- the exact support/normalization per Decomp's 𝒰-set conventions;
  -- R = (log X)^{1/16}-grade per the freeze; the seam datum
  -- a := seamCoeff (ellLin g) 1 t₀ (the H-EXIT convention).

Uhead := ballHead(the seam datum, t₀, R); the hhead binder then reads
Uhead ≤ C₁·X·exp(−(1/e)·M_range(seam datum) X T). The pin makes the
T-0 design's prose object a Lean def — no landed statement changes
(the sockets bind to it; the P21-2X precedent: mention-only).

## S3 — THE THREE-ZONE SPLIT (the honest anatomy of the ball integral)

∫_ball ‖spoly(t)‖² dt splits at radii δ₀ (the resonance width) and
r₁ := (log X)^{1/15} (M_range's inner radius):

- **ZONE A (the resonant core, |t| ≤ δ₀)**: no decay exists here (the
  trivial twist); the bound is measure × the crude sup:
  2δ₀·(X-grade)². The design bet: δ₀ = 1/L-grade (the classical
  resonance width of a length-X polynomial) gives X²/L ≪ the target
  X²·e^{−2cM} = X²·L^{−2/(32e)+o(1)}. ZONE A CLOSES CRUDELY iff
  δ₀ ≤ L^{−1}-grade — the sup itself via the trivial seam-mass bound
  (Σ‖a‖·hatK ≤ X-grade, landed surfaces).
- **ZONE C (the M_range window, r₁ ≤ |t| ≤ R... note R < r₁?? THE
  GEOMETRY QUESTION — see ZONE-SCOPE Q1): where S1's decay holds:
  measure × window_sup_decay_sq + the E² term (E = T1_head_wire's
  budget, X·log y/L-grade; E² ≪ the target — the arithmetic in the
  16:21 analysis). ZONE C CLOSES on the landed S1/S2 + the E²-page.
- **ZONE B (the gap, δ₀ < |t| < r₁) — THE OPEN DESIGN QUESTION**: no
  M_range floor here (the window excludes it), no resonance-width
  crudeness either. The classical fact wanted: the PARTIAL floor
  D²(datum, costwist t; X) ≥ c·log(|t|·L)-grade for 1/L ≤ |t| (the
  twist-decorrelation lower bound — GHS's T₀-machinery territory).
  With it: the zone-B integrand decays like e^{−c·log(|t|L)} =
  (|t|L)^{−c}, and ∫_{1/L}^{r₁} (|t|L)^{−2c} dt = L^{−1}·O(1)-grade
  at 2c < 1 — ZONE B CLOSES iff the partial floor exists at ANY
  fixed c > 0. THE QUESTION: which corpus surface supplies it
  (dist_one_floor_pow's range? the log_zeta bounds? sigma_shift's
  machinery at scale e^{1/|t|}?) or is it a new stone (class it)?

## THE GEOMETRY QUESTION (possibly dissolving zones A+B entirely)

M_range's window is (log X)^{1/15} ≤ |t| ≤ T+(log X)^{1/16} — but
WHICH t does the ball integral actually range over? If the s8
design's ball is |t−t₀| ≤ (log X)^{1/16} with t₀ ITSELF in the
window (the resonant frequency being HUNTED, not avoided), then the
ball's ABSOLUTE frequencies t₀+τ sit inside the window whenever
|t₀| ≥ 2r₁-grade — and the seam datum's centering at t₀ means the
RELATIVE twist τ has D²(datum, costwist τ) = D²(f, costwist(t₀+τ))
— the ABSOLUTE distance, floored by M_range when t₀+τ is in the
window. THE ZONES MAY BE AN ARTIFACT of conflating relative and
absolute frequencies: if the consumers only ever take t₀ in the
window and the ball stays inside it, ZONE A/B never occur and S3 =
ZONE C alone = measure × S1_sq + E² — ALL LANDED PIECES. ZONE-SCOPE
settles this FIRST (Q1) — it is the whole design's fork.

## ZONE-SCOPE's charges (overnight)

Q1 THE GEOMETRY (the fork): read Decomp's 𝒰/𝒯ⱼ set split, the
s8-freeze's int_U card, PropA3Core's T1 row, DistHalasz's M_range
design rationale (the mr-freeze if referenced): is the T1 ball
centered at window-interior frequencies (the zones dissolve) or does
it genuinely include the resonant core (the zones stand)? Q2 THE
PARTIAL FLOOR (if zones stand): the corpus surfaces for
D² ≥ c·log(|t|L) at 1/L ≤ |t| ≤ r₁ — dist_one_floor_pow's exact
range/shape; the DistHalasz log_zeta machinery; sigma_shift at scale
e^{1/|t|}; GHS's own T₀-handling (pp. 12-13); class the stone if
new. Q3 THE RESONANCE WIDTH (zone A): δ₀ = 1/L via which surface
(the trivial |spoly(t)−spoly(0)| ≤ |t|·Σ‖a‖·log n-grade Lipschitz
bound — a B-stone?); the crude sup's landed form. Q4 THE E²-PAGE
(zone C): the honest arithmetic at the corners. Q5 THE LADDER +
classes + GO.


## ⟦RATIFIED — THE B-PIN (JYH, 2026-07-23 evening)⟧

Option B: annHead pinned at Re = 1+sigma (consuming window_sup_decay
directly; the seam crossed on the mechanical/counting side — the
moment rows restate at 1+sigma where masses only shrink; the last
analytic stone never exists). The socket aligns to the honest grade;
the hsplit-shape amendment rides the P21-2X hypothesis-shape
precedent; the frozen interfaces (statement-line-agnostic per the
s8-freeze's own INTERFACE CONTRACT) untouched. PIN-WAVE fires.
