# THE PINNED ASSEMBLY — the terminal assembly's closing block

*Maestro design block, 2026-07-23 ~10:50. Status: **HOLD (refuted
~11:15) — the composition premise was FALSE.** PAGE-REF (FATAL): the
landed crude surfaces compose to L^{3/2}·X·e^{-cM} (numerics at four
corners; super-polynomial at the sliver floor) via two INDEPENDENT
intrinsic losses — (A) norm_hatKernel_le's sqrt-L ramp (the seam's
PASSING ledger used the MEAN-VALUE head bound |hatKernel| ~
(a+1)X^a/|s|^2, NOT landed); (B) k4_plan_le_diag_sharp DROPS
exp(-c|log m/n|) ('the only thing dropped') and that drop costs a
factor L — the sharp single-min form needs the off-diagonal KEPT.
BINDER-REF (REPAIRABLE): the datum seam — head_sigma_bound decays in
the g-datum distance while scale_floor_Mrange floors the g-FREE one;
M_range(1) is the WRONG M in the strong-cancellation regime; the
g-datum floor clone is the repair. THE TRUE FRONTIER, now named:
THREE SHARP STONES — (S-i) the MVT kernel head bound; (S-ii) the
off-diagonal-KEPT window evaluation on top of the LANDED
dirichlet_plancherel (the HalaszSeam:110-115 'mathlib-absent' note
may predate that landing — SHARP-SCOPE verifying); (S-iii) the
g-datum M_range floor. The refuters' arithmetic says the sharp seam
route PASSES — the ledger was always built on the sharp forms. THE LAST DESIGN BLOCK OF THE TERMINAL ASSEMBLY: every
ingredient below is LANDED; this block pins the free parameters and
composes the chain end to end. On its wave's landing, Part 3's T1
row discharges and the terminal assembly stands whole.*

## The pin (the parameter set, stated once, used everywhere)

L := Real.log X; c₀ := 1 + 1/L; η := 1/Real.log y; h := X/Real.sqrt L;
the gates: Real.exp 1 ≤ X (thresholded ∃X₀ where needed), 10 ≤ y,
y ≤ Real.sqrt X, Real.sqrt L ≤ y (the sliver gate), 0 < c₀ − 2η
(implied at the y-floor; carry explicitly), the M_range window
membership for the t-range in play. c := 1/Real.exp 1 (B4's).

## The chain (all names LANDED unless marked P#)

```
prop21RHS  --[J1 joint_cs_factoring]-->  (1/π)∫∫ supF·crossKer
  crossKer --[S2 mixed_weight_cs + S3 lorentz_compare +
              S4 k4_plan_le_diag_sharp @ c₀∓β]-->
              B(a)·√(C₋C₊)·(π/√(p₋p₊))·S₋·S₊
  S₋·S₊  --[P1: the pinned window-mass product]-->
              C·(X/y)^{2β}·min(L, 1/σ)²        (gate-b verified)
  supF   --[P2: the pinned supF supply]-->
              C·(1/σ)·exp(−c·(M_range − 2log(σL) − 48))
              via SF-0 ratio + head_sigma_bound + scale_floor_Mrange
  ∫_β    --[B3 sigma_cutoff_pretentious (flat) + the htriv tail]-->
              C′·exp(−c·M_range)·L per α-slice     (P3 packages)
  ∫_α    --[P4: the α-decay (X+h)^{−α} integral = 1/L-grade]-->
              the final grade C″·X·exp(−c·M_range)
  ⟹ hRHS (B4 form) --[T1_head_wire]--> T1_decay_trivial's hhead
  ⟹ P5: T1_decay_unconditional — THE EXIT.
```

## The stones (one wave, serial, new file Salt/MR/PinnedAssembly.lean;
## P5 extends HExit)

- **P1** [C, ~350] `window_mass_product_pinned`: BRIDGE-EXEC's
  gate-(b) arithmetic formalized AT THE PIN: S₋ ≤ (X/y)^{max(β−1/L,0)}
  ·(L+C) and S₊ ≤ y^{−σ}·(L+C) (via lambdaLin_window_bound-grade
  coefficient bounds + mertens_first_upper + the geometric window
  sums), then the product vs C·(X/y)^{2β}/σ²: the e^{−Lσ} kill
  (X^{−σ} = exp(−Lσ) beats (Lσ)² — v²e^{−v} ≤ 4e^{−2}·... state the
  clean sup lemma). The empty-window corner (y = √X) explicit.
- **P2** [B/C, ~250] `supF_pinned`: the per-(α,β) sup bound: the
  SF-0 ratio (smooth_ratio_bound + the smoothEuler↔smoothSeries
  finite-support bridge — land it here; finite support makes the
  tsum a Finset.sum everywhere, the Nat.Primes/Subtype fight routed
  around via Finset.filter) composed with head_sigma_bound at
  σ = β + 1/L and scale_floor_Mrange (the membership hypothesis
  threaded from the pin's t-range). Exit shape = B3's hpret socket.
- **P3** [B/C, ~250] `beta_integral_pinned`: the β-collapse per
  α-slice: split at σ* (B3 covers ANY b — the corner subsumed);
  the flat arm via sigma_cutoff_pretentious; the tail arm via the
  htriv (1/σ) side (the landed tail pattern from sigma_cutoff's
  proof, re-derived at the c-form — pure interval analysis); the
  P1 window-mass and P2 supF threaded; exit: ≤ C′·e^{−c·M_range}·L
  ·(the α-carried kernel amplitude).
- **P4** [B, ~150] `alpha_integral_pinned`: ∫₀^η (X+h)^{−α} dα ≤
  1/L-grade (the landed pattern from HGRADE's α-decay analysis;
  elementary FTC) composed with P3 → the final grade C″·X·e^{−c·M}.
- **P5** [B, ~200, HExit] `T1_decay_unconditional`: hRHS discharged
  (B4's binder shape) via P1-P4 + T1_head_wire; then the exit:
  T1_decay_trivial's hhead SUPPLIED — the theorem stated with ONLY
  the pin's regime hypotheses + route (i) + ‖g‖ ≤ 1. Docstring: the
  full provenance chain (the freeze → P21-2X → P21-3K → V5-0 → the
  v5 wave → J0 → B4 → this). THE TERMINAL ASSEMBLY'S T1 IS WHOLE.

## Corner ledger

- **The grade page** (every log power): B(a) = 2(X+h)^{a+1}/h carries
  X√L·(X+h)^{−α−β}; the α-integral eats (X+h)^{−α} → 1/L; the β-side:
  (X+h)^{−β} vs the (X/y)^{2β} from P1 and the σ-powers from B3 —
  WORK THE FULL PAGE FIRST (the executor's notes): the target is
  C″·X·e^{−cM} EXACTLY; the known tensions: the √L in B(a) (from
  2(X+h)/h) must cancel against the min(L,1/σ)² deficit vs 1/σ² —
  gate-b's arithmetic says it does (the e^{−Lσ} kill has L-powers of
  slack) — but the composed page must SHOW it; a residual log-power
  → STOP with the exact deficit.
- **The twist/datum bookkeeping**: P2's M_range is at the CENTERED
  datum (H-EXIT's g_{t₀} convention); the membership hypothesis
  threads the pin's t-range; T1_head_wire's binder (J0's M_range
  form, B4's e^{−cM} shape) must match BYTE-CONSISTENTLY — grep the
  binder before stating P5.
- **No ζ-theory beyond the landed log-of-ζ surfaces** (B1's route is
  blessed — norm_riemannZeta_le is a growth bound, not zero-theory).
- **The sliver gate** (y ≥ √L) and the empty-window corner both
  live in the pin — every stone's hypotheses come FROM the pin
  block, never ad-hoc.

## Refuter charges (firing now)

1. **PAGE-REF**: re-derive the FULL grade page independently at the
   pin (every log power, the √L cancellation, the (X/y)^{2β} flow,
   the σ-powers) — the composition must hit C″·X·e^{−cM} with no
   residual log; check the empty-window and y = √L corners.
2. **BINDER-REF**: byte-audit the whole consumption chain: P5's
   statement vs T1_head_wire's post-J0/post-B4 binder vs
   T1_decay_trivial's hhead vs the B3/P2/P1 socket shapes vs the
   pin's hypothesis set — any mismatch in the M_range instantiation,
   the twist placement, or the c-form is the finding.

Wave fires on FIRE / REPAIR-THEN-FIRE with repairs applied.
