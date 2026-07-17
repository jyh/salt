# s3-a3-design — the log-Chowla spine, wave 3 (A-R3 W3)

Frozen by the A3-W3R recon, adjudicated by the house 2026-07-19.
Paper: Tao, arXiv 1509.05422 (page-image fidelity; the cached PDF +
`chowla_pages/` in the session scratchpad). Model instantiation
throughout: `a = 1, b = 0, h = 1, c_p = 1` (the Liouville case).

## Page-fidelity transcriptions

**(3.15)** — p. 22 (bottom):

    | E (1/P_H) ∑_{y ∈ ℤ/P_Hℤ} F(X_H, y) |  ≫  ε · H/log H

**(3.16)** — p. 23 (top; after the `g_{i,ε²} → g_i` replacement at
cost `O(ε² H/log H)`):

    | E ∑_{p∈𝒫_H} (c_p/p) ∑_{j : j, j+ph ∈ [1,H]} 1_{j ≡ pb (a)}
        · g₁(a n + j) · g₂(a n + j + ph) |  ≫  ε · H/log H

(`n` = the log-uniform random integer; `E` over `n`.)

**Lemma 3.4 (circle method estimate)** — p. 23, defs pp. 23–24:
`S_H(α) := ∑_{p∈𝒫_H} (c_p/p) e(αp)` (3.17); `Ξ_H` := the `ξ ∈ ℤ/Hℤ`
with `|S_H(−(b+h)η/a − hξ/H)| ≥ ε²/log H` for some `η ∈ ℤ/aℤ`; then
for `|x_{i,j}| ≤ 1`:

    ∑_{p∈𝒫_H} (c_p/p) ∑_{j : j,j+ph∈[1,H]} 1_{j≡pb (a)} x_{1,j} x_{2,j+ph}
      ≪_{a,h}  (H/log H) · ( ε² + ∑_{ξ∈Ξ_H} (1/H) |∑_{j=1}^H x_{1,j} e(−jξ/H)| )   (3.18)

Proof substrate (p. 24): `G_i(ξ) := (1/H) ∑_j x_{i,j} e(−jξ/H)`,
Fourier inversion, and Plancherel/Cauchy–Schwarz
`∑_ξ |G_1(ξ)||G_2(ξ + (H/a)η)| ≪ 1`.

**Model collapse check** (`a=1,b=0,h=1,c_p=1`): the (3.18) LHS is
exactly the RHS of `fBridgeF_mean` — W3-b bounds precisely the object
W3-a produces. The seam is tight.

## Landed at adjudication (house ceremony, no executor)

- `Salt/Entropy/Chowla/Decoupled.lean` — **W3-a-1** `fBridgeF_mean`,
  **W3-a-2** `fBridge_concentration_decoupled` (the recon's validity
  probes WERE full proofs; class A each).
- `Salt/Entropy/Chowla/CircleMethod.lean` — **W3-b-defs**: `expSum`
  (3.17), `bigXi` (Ξ_H at `a=1`), `dft_is_fourier_coeff` (the
  carrier bridge, = `ZMod.dft_apply`).

## The frozen W3-b-main statement — RE-FROZEN v2 (2026-07-19)

**⛔ THE v1 FREEZE WAS FALSE** (W3-b-main executor STOP-AND-FLAG,
zero proof attempts wasted). Counterexample family: `eps = 1/k`,
`H = 5k²` (so ε²H = 5, 𝒫_H = {3,5}), `x1 = x2 ≡ 1`: LHS = Θ(H) but
RHS = Θ(H/log H); LHS/RHS = Θ(log H) unbounded — violated at k = 10
for C = 1, at k = 10⁶⁰ for C = 100. ROOT CAUSE: the v1 vacuity
guard (uniform C over ALL (eps,H)) over-corrected into falsity —
Tao's Lemma 3.4 is regime-gated: his p. 22 uses the PNT bound
`|𝒫_H| ≪ ε²H/log H` ("as ε is small and H is large"), which fails
when ε²H is bounded. The catch genre: ANTI-VACUITY OVERCORRECTION
(the dual trap to the per-H vacuity trap — recorded for the method
paper).

**v2 (house re-freeze): externalize Tao's PNT input as an explicit
hypothesis** — LHS/RHS byte-identical to v1, one hypothesis added,
quantifier discipline unchanged:

```lean
theorem circle_method_estimate :
    ∃ C C₀ : ℝ, 0 < C ∧ 0 < C₀ ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 x2 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) → (∀ i, |x2 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) *
          ∑ j ∈ Finset.range H,
            (windowVal H x1 j : ℝ) * (windowVal H x2 (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ)) *
            ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi eps H, (1 / (H : ℝ)) *
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖) := by
  sorry -- lands in CircleMethod.lean via W3-b-main-v2
```

**VACUITY GUARD (v2 form):** `eps, H, x1, x2` stay INSIDE the ∃;
the new hypothesis is satisfiable non-trivially (PNT: for any fixed
eps, all large H — the WITNESS obligation is node **W3-c-pnt**,
which must also produce the anti-vacuity instance; until it lands,
v2's non-vacuity rests on Tao p. 22, flagged not proven).

**The proof device (transcribed at page fidelity by the flag
report):** periodize x_i with period H — the wraparound error is
O(Σ_p (1/p)·p) = O(|𝒫_H|) ≤ C₀ε²H/log H by the NEW HYPOTHESIS
(the truncated-vs-cyclic seam is a non-issue once the hypothesis
exists); Fourier-expand; minor arcs (ξ ∉ Ξ_H): |S_H| < ε²/log H by
the bigXi filter + `dft_l1_bound` (M = 1); major arcs (ξ ∈ Ξ_H):
bound G₂ crudely by O(1) (box: ‖𝓕‖ ≤ H) and |S_H| ≤ Σ_p 1/p ≤
card·2/(ε²H) ≤ 2C₀/log H via `window_lb` (p > ε²H/2) + the
hypothesis.

## Carrier inventory (`Mathlib/Analysis/Fourier/ZMod.lean`)

`ZMod.dft : (ZMod N → E) ≃ₗ[ℂ] (ZMod N → E)` (scoped `𝓕`);
`dft_apply`, `dft_apply_zero`, `dft_dft` (inversion:
`𝓕(𝓕Φ) = fun j => (N:ℂ) • Φ (−j)`), `invDFT_apply`,
`dft_const_smul/-mul`, `dft_comp_neg`, `dft_comp_unitMul`;
`ZMod.stdAddChar` with `stdAddChar_apply` = `exp(2πi·/N)`; character
orthogonality IS exported (the recon's inline-only finding was
wrong): `AddChar.sum_mulShift` + `ZMod.isPrimitive_stdAddChar`
(found by the W3-b-parseval executor). `dft_eq_fourier` bridges to
the continuous FT.

**⚠ CARRIER GAP (CLOSED 2026-07-19):** mathlib has NO
Parseval/Plancherel for `ZMod.dft` — node **W3-b-parseval** LANDED
it in `CircleMethod.lean`: `dft_parseval`
(`∑_ξ ‖𝓕Φ ξ‖² = N · ∑_j ‖Φ j‖²`, factor N on the time side, pinned
by a delta-function smoke test) + `dft_l1_bound`
(`∑_ξ ‖𝓕Φ ξ‖·‖𝓕Ψ (ξ+t)‖ ≤ N²M²`, the CS corollary Lemma 3.4's
proof cites; shift in the SECOND factor). Both upstreamable.

## House rulings (adjudication 2026-07-19)

1. **The `≪_{a,h}` constant**: the existential-`C` freeze is ACCEPTED
   for the sprint (the model `a=h=1` constant is absolute; the
   vacuity guard makes it honest). The explicit-constant doctrine
   option (pin a numeral during proof) is OPPORTUNISTIC for the
   executor — if the proof yields a clean numeral, pin it; do not
   spend attempts hunting one.
2. **W3-a-3 (the outer (3.15)→(3.16) combine): DEFERRED to a house
   design block.** New doors identified by the recon: (i) the
   Chowla-failure hypothesis (2.11) as an explicit input; (ii) the
   good-`x` selector (union bound: decrement (3.13) +
   `weakUniform_spine` + `fBridge_concentration_decoupled` over the
   outer `logMeasure`); (iii) outer-expectation Fubini plumbing that
   does not exist in the landed API. NOT executor-safe as
   "elementary"; do not dispatch without a frozen design.
3. **Node cuts**: W3-a-1/2 + W3-b-defs landed at adjudication (house);
   W3-b-parseval (C, ~15–25k) dispatches next; W3-b-main (C, ~25–40k,
   may sub-split reduce-to-Fourier / Ξ_H-split) queues behind it.

## Kill-check record

Elaboration: all frozen statements elaborate against the landed API
(`ProbeW3.lean`, sorry-skeletons, zero errors). Validity: W3-a-1/2
PROVEN (`ProbeW3_validate.lean`). Falsity/degeneracy: zero-window
instance collapses both sides to 0; W3-b small-`H` consistent
(`H=1`: Lean's `log 1 = 0` zeroes both sides); the per-`H` vacuity
trap identified and dodged (see the guard above). Deprecation note:
use `integral_finsetSum` (not `integral_finset_sum`).

## W3-a-3 — the outer combine (HOUSE DESIGN BLOCK, 2026-07-19)

Page-fidelity source: p. 22 (read in-house). The chain from (2.11)
to (3.15):

1. Lemma 3.3 concentration (PRODUCT world, uniform y) — landed as
   `fBridge_concentration_decoupled`.
2. Lemma 3.2 transport: the deviation event E_bad ⊂ ZMod P_H has
   exp-small UNIFORM measure ⟹ log|E_bad| ≤ log P_H − g′ + log 2;
   `weakUniform_spine` then bounds its CONDITIONAL measure (given
   liouvilleWindow = x₀) by (t + corr + log 2)/g′ where t = the
   per-x₀ entropy deficiency. "Good x" = x₀ with small t.
3. Markov selection of good x₀ — landed as `decrement_markov` (t ≤
   (κ + defect)/θ for logMeasure-most x₀; κ from the decrement at
   the tower-selected H, defect funded by (3.9) =
   `entropy_residueWindow_ge`).
4. Deterministic box |F| ≪ H/log H on the bad set — needs
   `fBridgeG_abs_le` (H/p + 1) summed via **W3-c-pnt** (the SECOND
   consumer of that node: Σ_p (H/p+1) ≤ H·Σ1/p + |𝒫_H| ≪ H/log H).
5. Fubini + take E over logMeasure; (2.11-model) as the DOOR input:
   `|∫ fBridgeF eps H (liouvilleWindow H n) ((n : ZMod (PH eps H)))
   ∂(logMeasure x ω)| ≥ c·ε·H/log H` ⟹ (3.15-model), then
   `fBridgeF_mean` rewrites the y-mean as the two-point correlation.

**⚠ THE MARGIN CHECK (house, confirmed at design level): the
honest-exponent pinch is REAL.** The transport (step 2) needs the
deficiency budget t ≪ g′. Our landed exponent is g′ ≈ ε⁶H/(8·log²H)
(the PNT-free prime count in W2-b), one log below Tao's ε⁷H/log H.
The tower telescope selects H against budgets whose tower-sum
diverges: Σ 1/(n log n) diverges (landed,
`not_summable_one_div_nat_log`) but **Σ 1/(n log² n) CONVERGES** —
a two-log budget is NOT fundable by widening the tower. Tao's
one-log grade sits exactly on the divergence boundary; ours is
across it. REMEDY (mandatory prerequisite): **node W2-b′ — the
single-spot Chebyshev swap** in FBridge.lean's prime-count step,
pre-identified by the W2-b executor as a local upgrade, restoring
g′ to the ε⁷H/log H grade. Without W2-b′, W3-a-3c is UNPROVABLE as
designed — do not dispatch 3c before b′ lands.

**Node cuts:**
| node | content | class | prereq |
|---|---|---|---|
| W2-b′ | the Chebyshev swap: fBridge_concentration at Tao-grade exponent ε⁷H/log H | B | none (local to FBridge) |
| W3-a-3a | bad-set transport: Hoeffding card bound + weakUniform_spine compose, per-x₀ | B | W2-b′ |
| W3-a-3b | good-x₀ selection | A (≈ decrement_markov applied) | none |
| W3-a-3c | the outer Fubini assembly → (3.15/3.16-model), (2.11) as hypothesis | C | ALL of: W2-b′, 3a, 3b, W3-c-pnt, the v2 circle method |

**Doors (explicit hypotheses, believed-true, no new axioms):**
(2.11-model) — discharged later by W3-e from the log-Chowla-failure
assumption (the contradiction hypothesis; it is SUPPOSED to be
false); the MR Prop 2.4 door is downstream of this block (feeds
W3-e, not W3-a-3).
