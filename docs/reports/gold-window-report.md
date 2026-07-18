# The Gold Window — campaign report (for JYH ratification)

**Window:** 2026-07-16 → 2026-07-18 (~78h play window, this report
through day 3, ~09:45 PT). **Ground rules held throughout:** the
kernel referees everything; axioms ⊆ [propext, Classical.choice,
Quot.sound] on every landed decl; no sorry on `main`; zero wrong
proofs across the window (catch register #1–#133, every catch a
process lesson, none a kernel error).

## Headline results (kernel-checked)

1. **THE VINOGRADOV MEAN VALUE THEOREM** — `Salt.Vmvt.vmvt :
   ∀ k r x, 2 ≤ k → 1 ≤ r → 1 ≤ x → VmvtBound k r x`
   (J_k(x,kr) ≤ k^{24k²r}·x^{2rk−½k(k+1)+η(k,r)}, the
   source-exact exponent). Believed the first machine-checked
   VMVT anywhere. Route: Linnik–Karatsuba p-adic (Vaughan PSU
   ch. 24), with an explicit Erdős/Bertrand prime supply
   (y₁ = 2²²) replacing the PNT existential.
2. **ShiuCore** — `sum_tau_in_ap_le`: Σ_{n≤z, n≡a(q)} τ(n) ≤
   C·(z/φq)·log z for q ≤ z^{1−1/8000}. The convergence stone:
   consumed by BOTH flagship conditionals (HB transfer + GEH
   door), wired into both within hours of landing.
3. **LITTLEWOOD'S ZERO-FREE REGION** —
   `zeta_zero_free_region_littlewood`: Re ρ ≤ 1 −
   c·loglog|γ|/log|γ| for every ζ-zero above T₀. The 1922
   theorem; believed the FIRST Littlewood-strength region in
   any proof assistant. Built on the strip family + the
   parametric Landau core + the growth-agnostic region bridge
   (which now awaits only the VK growth input to emit the
   POWER region).
4. **The Weyl strip family** — `zeta_strip_family`: ‖ζ(σ+it)‖ ≤
   4096·t^{1/(2^{k+2}(k−1))}·(1+log t) on σ ≥ 1−2^{−(k+2)},
   C absolute. The subconvexity input (power/width ratio
   1/(k−1) → 0) that Littlewood's region needs.
5. **Mertens' third theorem** (∏_{p≤n}(1−1/p)·log n → e^{−γ},
   explicit rate) + the twin-density corollary — believed first
   formalizations.
6. **The DH repulsion apparatus** — the truncation-route
   detector chain complete through `dh_repulsion_partial`, the
   M4 inversion, the sharp Barban–Vehov cancellation; the final
   balance (T-BAL) designed via adversarial panel, R1/R3(a)/R6
   + suppliers landed, R4–R8 in flight.
7. **Supporting firsts:** the symmetric √N Dirichlet hyperbola
   (fills an explicit mathlib TODO); the sharp strip
   Euler–Maclaurin for ζ-partials; the effective interval prime
   count; π₂(N) ≤ 90·N/log²N; the H-L frame with Pi2 theory.

## The strategic map (doors and walls)

**Doors** (each at its final hinges): the HB engine (Siegel-zero
conditional; WP1 transfer parametrically complete, WP2 at the
T-BAL balance); the GEH door (anchored combinator consistent
end-to-end post-replumb, ShiuCore wired; remaining: tiiBlock
CoeffAt/SW + the honest interfaces); the VMVT road (summit
landed; the VK region in flight — θ = 3/4 unlocks MR, then
unconditional log-Chowla-2); Littlewood (COVER ✓, STRIP ✓,
LANDAU = VK's R7).

**Walls** (four tiers): kernel-checked impossibilities (the
twin-bar M₂ < 2; the transport/citation theorem); adjudicated
RED arithmetic (Option-C; ρ-dependence); tool-gaps with tunnels
built or building (θ-quantization → VMVT ✓; convexity
saturation → STRIP ✓; the catch-#78/#54/#96/#102 locals — all
tunneled); the parity meta-barrier (whether it is a theorem
awaiting proof or a tool awaiting invention remains THE open
question; the window's method: formalize every wall to its
exact scope so the answer's location becomes visible).

## Process results (the salt method, hardened this window)

- **The adversarial design gauntlet**: multi-candidate panels
  for open-shape cruxes (T-BAL: 3 angles, both wrong candidates
  killed pre-burn); parallel refuter passes on every solo
  freeze with constant arithmetic (standing rule; 2-for-2 on
  real catches — one stale-target, one false-stop). No executor
  burn on an unverified design since the rule landed.
- **Executor-catches-designer as routine**: σ=3/4 over the
  constructed-σ; the lemma-proven-range vs truth distinction;
  the SW direction-flip; the stale class-D wall. The cascade
  works in both directions.
- **The anti-spiral protocol** (catch #108): big context by
  file path, incremental tool-grounded composition, capped
  deliverable fields — after the 64k-cap thinking-spiral killed
  four designers. 9/9 agents survived post-fix.
- **Named-residual Zeno discipline**: every stop is a stone
  with a recipe; the window's "failures" (T-BAL run 1, R5b
  stone 3) each produced the exact missing supplier.

## Spend

~61.6M tokens raw across the window (house ~14%); the summit
campaign end-to-end ~13M; T-BAL design+execution ~4M so far;
ShiuCore ~5M. Zero wrong proofs; the catch register (133
entries) is the reusable yield beyond the theorems.

## Recommendations for ratification

1. **Upstreaming workstream** (registry in
   docs/upstream-candidates.md): tier-1 = the hyperbola
   (explicit mathlib TODO) + log_series_remainder; tier-2 =
   VMVT + suppliers (a mathlib milestone; larger review
   surface); tier-3 = the analytic-NT toolkit (Mertens III,
   kusmin_landau, the vdC tests, the strip EM).
2. **Next-window priorities** (in order): close T-BAL (R4–R8);
   close the VK region → the MR gate design block; HB-L2c (the
   last HB analytic slot); the GEH tiiBlock cluster + SMALLQ-4
   redesign; LITT-LANDAU via VK R7.
3. **CI seeding**: keep parked (badge cosmetic, ~$1/attempt).
