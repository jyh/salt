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

## The frozen W3-b-main statement (NOT yet landed — proof pending)

```lean
theorem circle_method_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 x2 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) → (∀ i, |x2 i| ≤ 1) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) *
          ∑ j ∈ Finset.range H,
            (windowVal H x1 j : ℝ) * (windowVal H x2 (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ)) *
            ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi eps H, (1 / (H : ℝ)) *
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖) := by
  sorry -- lands in CircleMethod.lean via W3-b-parseval → W3-b-main
```

**VACUITY GUARD (binding):** `eps, H, x1, x2` are quantified INSIDE
the `∃ C` — a per-`(eps,H)` constant is trivially true by finiteness
of the bounded-window set. Any executor restatement must preserve
this quantifier order. Elaboration-checked (recon probe `ProbeW3.lean`).

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
