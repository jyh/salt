# THE SUPF DESIGN BLOCK — leg (i), the last leg of hRHS

*Maestro design block, 2026-07-23 morning. Status: **HOLD (refuted
~08:00) — the ASSEMBLY is fatal; the pointwise layer survives.**
EULER-REF (REPAIRABLE, repairs exact): SF-0's ratio constant needs
mertens_first_upper's cancellation (the 'elementary e^3' claim FALSE
-- the additive fallback illusory at (log y)^{e^2}); SF-1 needs the
twist adapter (IsMultiplicative.eulerProduct_tprod, NOT the
completely-multiplicative drop-ins); SF-2's tail fine (prime_tail_
shift), the sigma=2eta scale-mismatch flagged. BALL-REF
(CONFIRMED-FATAL): prop21RHS_le_head's socket stacks three never-co-
occurring worst cases (full-line sup discards kernel localization;
pointwise window mass discards the L^2-mean; full-line Kmass) --
overshoot L^{3/2}, regime-robust, arsinh-proof; the sigma-cutoff has
NO home in the box-collapsed socket; the drift is loglog-grade
CONFIRMED. THE RULING: the C-tier adjudication was UNFOUNDED for the
assembly -- the D-reading stands there; the hybrid path: (a) the
EULER LAYER (SF-0 repaired + SF-1 + SF-2) lands as route-independent
shelf stones (any head bound needs them); (b) the JOINT HEAD
(window x kernel diagonalized together, the live sigma-integral) is
scoped honestly -- BALL-REF's option (ii), a t-split Plancherel-joint
LEG-II rebuild, scoped BEFORE conceding the full A.10 port (the
exact-kernel dividend question, one more time).* Inputs: SUPF-SCOPE's
map (the D-reading), M-BRIDGE-SCOPE's map (the C-reading + the exact
σ-cutoff arithmetic), LEG-II's landed socket (hsupF/hKint),
NIGHT-SIGMA's landed sigma_cutoff (C = 1) + kernel_mass_ledger.*

## THE TIER ADJUDICATION: C — the D-reading priced the wrong route

The R2.3 fail-fast (HalaszCore:126-129) priced the MRT A.9–A.14
machinery: the Perron/Plancherel representation feeding the ball
INTEGRAL bound U. That was the old route's need. LEG-II's socket
changed the requirement: hsupF asks only for the POINTWISE bound
‖𝒮(s−α−β)·𝓛(s+β)‖ ≤ F0 over the box — no Plancherel, no A.10, no
contour. The pointwise bound is the classical Euler-product log
computation, and its ingredients are substantially LANDED:

- 𝒮·𝓛 = LSeries (ellLin g) (lseries_ellLin_eq_smooth_mul_large,
  LANDED) and ellLin has SQUAREFREE support
  (ellLin_prime_pow_ge_two = 0, LANDED) ⟹ the Euler product has
  LINEAR local factors (1 + g(p)·twist/p^s) — mathlib's
  EulerProduct/ArithmeticFunction machinery applies at Re > 1.
- The k≥2 tail: LANDED (Dist.lean's Euler tail).
- The distance identification: pretDistSq_principal_eval + Mertens
  (mertens_second_sharp) + rough_prime_tail — LANDED.
- The ball uniformization: PretentiousTriangle (LANDED module) +
  M_range (DistHalasz:262, LANDED).
- The single genuinely-new content: the Euler-log bridge (the S1
  MR-W1 residual, long flagged) — C-grade, not D.

The mixed-argument wrinkle (𝒮 at Re possibly < 1) is dissolved by
GHS's own p.12 move: the smooth-leg RATIO |𝒮(s−α−β)/𝒮(s+β)| ≤ C
(finite sum over p ≤ y with exponents ≤ 3η = 3/log y ⟹ p^{3η} ≤ e³
— elementary), reducing to the single-argument F at Re = c₀+β > 1
where the Euler product converges. No object is ever evaluated where
it diverges. The precedent stands a fourth time: the wall priced as
D shrinks on contact with what the corpus already owns.

## The ladder (serial; each gated; new file Salt/MR/SupF.lean except
## SF-EXIT which extends HExit.lean)

- **SF-0** [B, ~150] `smooth_ratio_bound`: ∀ (α,β) ∈ [0,η]², t:
  ‖smoothSeries y g (s−α−β)‖ ≤ C_S·‖smoothSeries y g (s+β)‖-free
  form — state as the direct bound ‖𝒮(s−α−β)·𝓛(s+β)‖ ≤
  C_S·‖F(c₀+β+it)‖ with F := LSeries (ellLin g) evaluated via the
  ratio; C_S explicit (e³-grade from p^{3η} ≤ e³ on p ≤ y).
  Fail-fast: if 𝒮's finite-product structure resists the ratio
  (log-of-finite-sum vs product), STOP — the fallback shape is the
  additive crude bound with the SAME grade.
- **SF-1** [C, ~400] `euler_log_bound` (THE BRIDGE, the risk stone):
  for Re s = 1+σ > 1: ‖LSeries (ellLin g) s‖ ≤
  C·exp(Re Σ_p (g(p)·twist)/p^s) with the k≥2/squarefree tail
  absorbed into C. Route: mathlib's Euler product for the
  multiplicative ellLin (squarefree support ⟹ linear factors);
  ‖Π(1+z_p)‖ ≤ Π(1+‖z_p‖) ≤ exp(Σ‖z_p‖) on one side and the
  Re-refined |1+z| ≤ exp(Re z + ‖z‖²) on the sharp side (the ‖z‖²
  sum = Σ 1/p² -grade, absorbed). FAIL-FAST at ~5 unanticipated
  sublemmas: STOP + report (the mathlib EulerProduct API's exact
  reach is this stone's real risk).
- **SF-2** [B/C, ~250] `dist_identification`: Re Σ_p (g·twist)(p)/
  p^{1+σ+it} = Σ_{p≤X} 1/p − pretDistSq-form + O(1) at σ ∈
  [1/L, 2η]: the head/tail comparison (p > X tail via
  rough_prime_tail-grade at σ ≥ 1/L; the p ≤ X head matches the
  distance's Mertens evaluation). Exit: ‖F(1+σ+it)‖ ≤
  C·L·e^{−M(t)} (the pretentious bound) AND ≤ C/σ (dropping the
  distance term — htriv falls out here for free).
- **SF-3** [C, ~300] `ball_uniformization`: the box/ball sup: M(t) ≥
  M(center) − drift, drift ≤ the pretentious-triangle bound over the
  kernel's effective t-range; exit = hsupF's exact socket shape with
  F0 = C·L·e^{−M(center)}·e^{drift}. The drift's grade must be O(1)
  or absorbed into sigma_cutoff's M — work the drift arithmetic on
  paper FIRST; if the kernel's effective range makes drift grow with
  L, STOP (the Tsplit refinement of kernel_mass_ledger becomes
  load-bearing — a named pivot, not a wall).
- **SF-4** [B, ~100] `htriv_supply`: package SF-2's 1/σ side into
  sigma_cutoff's htriv socket.
- **SF-EXIT** [B/C, ~300, extends HExit.lean] `hRHS_discharged` +
  `T1_decay_unconditional`: THE GRADE ASSEMBLY — compose
  prop21RHS_le_head (hsupF ← SF-3, hKint ← kernel_mass_ledger) with
  sigma_cutoff (hpret ← SF-2/3, htriv ← SF-4) per M-BRIDGE-SCOPE's
  dimensional chain; the FULL log-power page written in the
  executor's notes BEFORE Lean (the known excess: Kmass's crude √L —
  absorbed or the arsinh refinement triggered; the η² = 1/L²; the
  window-mass log²; the α-integral 1/L; the σ-integral's L). Exit:
  hRHS discharged → T1_head_wire composed → T1_decay_trivial's
  hhead supplied → the T-chain's decay UNCONDITIONAL. If the grade
  page shows a log-power gap, STOP with the exact deficit (maestro
  re-rules — a log-power gap is repairable by regime tightening,
  never by silent absorption).

## Corner ledger

- **No object below its abscissa, ever**: the ratio move (SF-0) is
  what keeps the Euler product at Re > 1; any stone finding itself
  evaluating 𝓛 or F at Re ≤ 1 has misread the design — STOP.
- **The twist placement**: F's datum is the CENTERED g_{t₀} (the
  H-EXIT convention); M(t) is the distance at costwist t against the
  centered datum = pretDistSq f (costwist (t+t₀)) X by the landed
  identity — keep the t₀-bookkeeping explicit in every statement.
- **The σ-range**: sigma_cutoff wants [1/L, 2η]; SF-2's comparison
  must hold on ALL of it (the worst corner σ = 2η = 2/log y, where
  p^{−σ} decay is weakest — check the tail comparison THERE).
- **grade_EM's 2 is load-bearing** (M-BRIDGE numerics); the exit
  grade is (1+M)e^{−M} → 2e^{−M/2} via the landed grade_EM only.
- **No ζ-theory**: the trivial bound's 1/σ comes from Σ p^{−1−σ} ≤
  log(1/σ)+C-grade elementary sums (Mertens machinery), never from
  ζ's analytic continuation.

## Refuter charges (firing now)

1. **EULER-REF**: attack SF-0/1/2 — the ratio's uniformity and its
   finite-product mechanics; mathlib's EulerProduct API reach for
   squarefree-supported multiplicative ℂ-valued data (name the exact
   lemmas; if the API needs completely-multiplicative or norm-1
   hypotheses ellLin lacks, that is the finding); the σ-shift
   comparison at BOTH corners (σ = 1/L and σ = 2η); the k≥2/‖z‖²
   absorption grades.
2. **BALL-REF**: attack SF-3/SF-EXIT — the drift arithmetic against
   the kernel's true effective range; the M-center reconciliation
   against T1_head_wire's exact binder; THE FULL DIMENSIONAL CHAIN
   with every log power tracked (re-derive M-BRIDGE-SCOPE's page on
   the assembled route, including Kmass's crude √L — does the
   composition clear the hRHS grade or is the arsinh refinement
   load-bearing from day one?).

Verdicts per the house schema; the wave fires on FIRE /
REPAIR-THEN-FIRE with repairs applied.
