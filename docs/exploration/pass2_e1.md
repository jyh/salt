# PASS 2 / E1 — THE EFFECTIVE-L ENUMERATION: what ¬F buys

E1 of the fulcrum Pass-2 sweep. Ground rule honored: every implication route is labeled
GROUNDED (file:line or source:line, checked this pass) or MEMORY (classical knowledge not
in the staged corpus). NO Lean was written.

## §0 — The negation, precisely

`F(C) := FulcrumQualityMin C` (kernel-checked, `Salt/Fulcrum/Basic.lean:61-64`):
∀Q ∃q>Q, ∃ primitive quadratic χ ≠ 1 mod q, ∃ρ: `LFunction χ ρ = 0 ∧ ‖1-ρ‖·(C·log q) ≤ 1`.

**¬F(C⋆)**: ∃Q₀ such that for EVERY q > Q₀, every primitive quadratic χ ≠ 1 mod q, every
zero ρ of L(·,χ): `‖1-ρ‖ · C⋆·log q > 1` — a uniform, fixed-quality, effective zero-free
ball at s = 1 for the whole family above Q₀. Monotonicity: F(C) ⟹ F(C') for C' ≤ C
(smaller C = bigger ball = weaker demand), so ¬F(C⋆) ⟹ ¬F(C) for all C ≥ C⋆. The
constants structure of everything below: **(C⋆, Q₀)** from ¬F, plus the landed effective
c₀ (ZFR; numeral extraction owed, `c₀ = 1/126848` per `Salt/Fulcrum/Basic.lean:166-169`),
c₃ (ζ-region), and δ_fin(Q₀) — the finite-range real-zero gap over conductors ≤ Q₀
(computable in principle; Lean shape = the unproven gadget, see D2).

**Marginal content of ¬F** (scope-diff, catch-#224 class): the landed
`zero_free_region_all` (`Salt/SW/ZeroFreeReal.lean:605-608`, effective) already excludes
every zero with `χ² ≠ 1 ∨ Im ρ ≠ 0` from a c₀/log(q(|Im ρ|+2)) neighborhood. So inside
the ¬F ball the only zeros not already excluded are REAL zeros of QUADRATIC primitive χ.
¬F's entire marginal content is: **no real zero β with 1−β ≤ 1/(C⋆ log q), q > Q₀** —
exactly the Siegel-zero hole, matching `fulcrum_zero_real` (`Basic.lean:93-103`) which
derives reality of F-witnesses from the same landed ZFR.

## §1 — Corpus inventory consulted (all GROUNDED)

| Piece | Where | Direction |
|---|---|---|
| `FulcrumQualityMin`, `SiegelModulusUnbounded` (interface, UNPROVEN), `imsz_implies_fulcrum_of_gadget` | `Salt/Fulcrum/Basic.lean:61,73,193` | statement layer |
| `zero_free_region_all` | `Salt/SW/ZeroFreeReal.lean:605` | complex/non-quadratic ZFR, effective |
| `siegel_theorem` (ε-quantified, INEFFECTIVE C) | `Salt/SW/SiegelClose.lean:841-844`; ineffective choice at :850 via `siegel_dichotomy` (`Salt/SW/Siegel.lean:227-238`, `Classical.em`) | zero-free, q^{-ε} |
| `LFunction_one_re_le_mvt` / `_sharp` | `Salt/SW/SiegelFinal.lean:106-109` (27√f(1+log f)); `Salt/SW/SiegelClose.lean:458-461` ((1−β)·25e(1+log f)²) | zero ⟹ L(1) CAP |
| `L1_lower_siegel` | `Salt/SW/DHCore.lean:808-816` | deep zero ⟹ L(1) ≥ 0.27(1−β₀)(2−β₀), guard-gated |
| `LFunction_one_re_ge_partial`, `dh_repulsion_partial` | `Salt/SW/DHClose.lean:105-109,154-160` | unconditional truncation/repulsion |
| `dh_repulsion_ordered` (effective b,c,k) | `Salt/SW/TBalR8.lean:1752-1759` (constants built :1768-1779) | real zero repels complex zeros |
| SW chain: `psi1_char_bound` → `psi1AP_main_bound` → `siegelWalfisz_holds` | `Salt/SW/CharDispatch.lean:317-324`, `Salt/SW/Fold.lean:157-174,282-311`, `Salt/SW/Gate.lean:150` | the gate |
| `NoSiegelZeros`/`IMSZ`/HB defs + equivalences | `Salt/TwinBar/SiegelTwin.lean:76-98,111-131` | dichotomy frame |
| MV vol. 3 (staged) | `docs/sources/montgomery3.txt` | classical grounding (below) |
| Tao log-Chowla (staged) | `docs/sources/chowla.txt` (title/abstract, lines 1-40) | consumer side only; NOT an L(1) source |

Key source citations: exceptional-zero statement + (28.62) `1/(c₂q₁^{1/2}(log q₁)²) ≤ δ₁ <
1/(c₁ log T)` — montgomery3.txt:21680-21703; **"if as T varies there are only a finite
number of exceptional moduli, then in principle one could simply adjust the constant c₁
and eliminate the concept of 'exceptional'... this leads inexorably to the
non-computability of c₁"** — montgomery3.txt:21716-21727 (¬F is exactly the finite-moduli
hypothesis, WITH computable data); ψ(x,χ) with isolated E₁·x^{β₁}/β₁ term, Thm 24.22 —
montgomery3.txt:7504-7537; **"Note that c1 is effective. However, in the current state of
knowledge, x0(A) is not"** (Cor 24.24/24.25) — montgomery3.txt:7576-7614; Deuring–
Heilbronn Cor 28.15 — montgomery3.txt:21743-21757; no-exceptional-zero ⟹ extended-range
effective PNT(q,a), Exercise 28.4.3.1 — montgomery3.txt:20087-20109.

## §2 — The deliverables

### D1. Full effective zero-free region, no exceptional zeros, above Q₀
¬F plugs the one hole in the landed ZFR. For q > Q₀, all χ primitive mod q, all zeros:
`Re ρ ≤ 1 − min(c₀,1/C⋆)/log(q(|Im ρ|+2))`-shaped, real quadratic zeros included
(real zeros: 1−β = ‖1−ρ‖ > 1/(C⋆ log q) from ¬F verbatim; the rest:
`zero_free_region_all`). GROUNDED both legs. **Effective**: min(c₀, 1/C⋆). This is the
MV (28.61) region with E₁ = 0 — montgomery3.txt:21680-21688. Consumers: the
exceptional branch of `psi1_char_bound` (CharDispatch.lean:319-321, case (iii) at :435)
loses its sting above Q₀ (the Landau zero β₁ ∈ [9/10,1) may exist but is quality-capped).

### D2. NoSiegelZeros, hence ¬IMSZ — modulo the ONE gadget
`NoSiegelZeros` (`SiegelTwin.lean:76-80`, ∃c-form over ALL q) follows from ¬F(C⋆) with
c = min(1/C⋆, c_fin(Q₀)) once the conductors ≤ Q₀ are handled — which is EXACTLY the
unproven compactness interface `SiegelModulusUnbounded` (`Fulcrum/Basic.lean:73-77`,
FULCRUM-S2, consumed abstractly at :194; grep confirms no proof anywhere). Then
`noSiegelZeros_iff_not_infinitely` (`SiegelTwin.lean:129`) gives ¬IMSZ. **The same
unproven gadget serves both arms**: IMSZ→F (`imsz_implies_fulcrum_of_gadget`) and
¬F→NoSiegelZeros. It is THE shared finite-range debt of the whole fulcrum program.
Effective: yes, with c_fin computable in principle (finitely many χ, each L(1,χ) ≠ 0).

### D3. THE HEADLINE — effective Siegel–Walfisz
The entire `siegelWalfisz_holds` chain (`Gate.lean:150`, discharging `Salt.BV.SiegelWalfisz`,
`Salt/BV/Defs.lean:35-38`) has **exactly one ineffective input**: Cₛ from `siegel_theorem`,
obtained at `Fold.lean:167` and applied at `Fold.lean:282-283` (`Cₛ/f^ε ≤ 1−β₁` at the
CONDUCTOR f = χ.conductor) to kill the exceptional term `x^{β₁+1}/(β₁(β₁+1))` via
`x^{β₁+1} ≤ x²e^{−Cₛ(log x)^{3/4}} ≤ x²e^{−Cₛ√log x}` (Fold.lean:32-34, 294-335). Grep
confirms no other consumer of `siegel_theorem` and no `Classical.em` elsewhere in
Fold/CharDispatch/Gate; cc/ct/Kc/Kt trace to the effective c₀/c₃ regions; the Gate
de-smoothing (`Gate.lean:22-43`) is effective arithmetic; K = 1 at Fold, the final ∃K
absorbs x₀.

**Under ¬F the swap is architecture-preserving**: 1−β₁ > 1/(C⋆ log f) ≥ 1/(C⋆·C·log log x)
(f ≤ q ≤ (log x)^C), so `(1−β₁)log x ≥ c5√log x` holds once `√log x ≥ c5·C⋆·C·log log x` —
one new effective eventually-fact in the x₀ extraction (Fold.lean:180-196); the
`e^{−c5√log x}` bound then closes identically. Result: `SiegelWalfisz` with **effective
K(A,C)** computable from (A, C, C⋆, Q₀, c₀, c₃, δ_fin(Q₀)) — modulo the conductor-level
finite range f ≤ Q₀ (D2's gadget). ~B-class Lean work at the single choke point.
Classical grounding: MV Cor 24.25 + the effectivity remark montgomery3.txt:7612-7614 —
¬F makes the ineffective x₀(A) effective, verbatim the textbook's gap.

**Eat list** (every landed consumer of `siegelWalfisz_holds` upgrades from
∃K-ineffective to effective-K): `bounded_gaps_unconditional` (`Gate.lean`, audit
`SW/All.lean:226`) — effective localization of bounded-gap prime pairs;
`Salt.BV.bounded_gaps_of_siegelWalfisz` (BV chain); Chen (`Salt/Chen/BetaSW.lean:217`);
Maynard (`Salt/Maynard/GehSW.lean:214`); Goldbach (`Salt/Goldbach/A1.lean:328`,
`psi_BV_of_siegelWalfisz'` at saving 11); the Chowla spine's PNT input
(`Salt/Entropy/Chowla/WindowMertensLower.lean:14`, via `Salt.Chen.psiTot_pnt`).

### D4. Super-SW error term + extended q-range (latent)
Under ¬F the exceptional term obeys `x^{β₁} ≤ x·exp(−log x/(C⋆ log f))`, so for
q ≤ (log x)^C the AP error improves to `x·exp(−c(C⋆,C)·log x/log log x)`-type, and the
range extends to `q ≤ exp(log x/(c₂ log log x))` with error `exp(−c(log x)^{1/2})`-type.
GROUNDED classically: MV Thm 24.22 (montgomery3.txt:7504-7537; E₁ is the sole
obstruction) and Exercise 28.4.3.1 (montgomery3.txt:20087-20109 — literally the
no-exceptional-zero hypothesis). Effective throughout. **No landed consumer demands
better than SW-shape** — this is a latent upgrade, priced but unclaimed.

### D5. Effective L(1,χ) ≫ 1/log q — TRUE classically, NOT corpus-derivable (honest gap)
The classical route (Hecke/Landau: L(1,χ) small forces a real zero near 1; contrapositive
under ¬F gives L(1,χ) ≥ c(C⋆)/log q, q > Q₀) is **MEMORY** — MV vol. 1 Ch. 11 territory;
the staged montgomery3.txt is vol. 3 (its 28.62 CITES Cor 11.12 rather than proving it),
and chowla.txt is Tao's log-Chowla paper, not an L(1) source. The corpus's three
L(1)-facing lemmas do NOT compose to it:
- `L1_lower_siegel` (DHCore.lean:808): needs an ACTUAL zero + deep-regime guards
  (hN/hscale/hguard, kept as hypotheses in Lean). Under ¬F it yields, for characters
  that DO carry a real zero in the overlap window (1/(C⋆ log q) < 1−β₀ ≲ 1/(c·log q)
  where the guard regime lives), `L(1,χ).re > 0.27/(C⋆ log q)` — partial coverage only,
  and conditional on the guard-discharge nodes (T-BAL freeze ledger).
- `LFunction_one_re_le_mvt(_sharp)`: the CAP direction (zero ⟹ L(1) small) — converts
  L(1) lower bounds INTO repulsion, never the reverse.
- `LFunction_one_re_ge_partial` (DHClose.lean:105): unconditional, but the partial-sum
  main term `Σ_{n≤N}χ_ℝ(n)/n` is not sign-controlled by anything landed.
**Verdict**: ¬F ⟹ effective L(1,χ) lower bound requires a NEW C-class node (the Hecke
argument). If built: fully effective, and it retires the Goldfeld/Estermann apparatus
(Siegel.lean, SiegelFinal.lean, SiegelClose.lean §closer) for q > Q₀. Downstream then:
effective class-number bounds h(−d) ≫ √d/log d (MEMORY; no corpus consumer exists).

### D6. What ¬F retires (anti-consumers)
- The HB engine arm: `F_min` is "the weakest hypothesis from which the Heath-Brown engine
  can still manufacture twin primes" (`Fulcrum/Basic.lean:19-21`); ¬F starves it. The
  registered HB-ENGINE campaign and `HeathBrownStatement` (`SiegelTwin.lean:92`) target
  the OTHER arm. Under ¬F, `HeathBrownDichotomy` (`SiegelTwin.lean:97`) resolves to its
  right disjunct (via D2) — with NO twin-prime yield. ¬F buys constants, not twins.
- Deuring–Heilbronn as leverage: `dh_repulsion_ordered` (TBalR8.lean:1752) and the T-BAL
  product stay true (unconditional, effective constants) but their intended fuel — a β₀
  of extreme quality boosting the ZFR — has no witnesses above Q₀. Classical mirror:
  Cor 28.15 (montgomery3.txt:21743-21757) becomes vacuous when β₁ doesn't exist.
- `siegel_theorem` itself is SUPERSEDED, not effectivized: ¬F does not shrink the
  dichotomy window δ = min(ε/36,1/20) (SiegelClose.lean:846), and zeros in
  [1−δ, 1−1/(C⋆ log q)] remain possible at every q — the ε-statement's constant stays
  ineffective under ¬F. Its one load-bearing use (Fold.lean:167) is what D3 replaces.

### D7. Character sums: nothing in-corpus
`polya_vinogradov` (consumed at DHClose.lean:112) is unconditional; Burgess is absent;
Siegel-zero⟺pretentious-χ links are MEMORY with no landed consumer. ¬F buys nothing
here against the current corpus. Honest zero.

## §3 — Catch ledger for this pass
1. (scope-diff) ¬F ball vs real-zero content: marginal content is real quadratic zeros
   only (§0) — do not double-claim the complex region, it is already landed.
2. (scope-diff) Conductor vs modulus: the SW kill runs at `χ.conductor` (Fold.lean:282);
   ¬F must be instantiated at conductors; the finite-range debt is conductors ≤ Q₀.
3. (fossil-risk) `SiegelModulusUnbounded` is an INTERFACE (def, no proof) — any Pass-2
   claim of "NoSiegelZeros" or "effective SW, all q" is conditional on it; it is a
   single shared B/C-class debt, deliberately identical on both dichotomy arms.
4. (fossil-risk) `L1_lower_siegel`'s guards are Lean hypotheses; freeze-ledger discharge
   is doc-side. Do not cite it as an unconditional L(1) floor.
5. (source-scope) montgomery3.txt = MV vol. 3; every vol.-1 citation (Cor 11.12, Thm
   11.14/11.15, Hecke) inside it is a POINTER, not a staged proof — MEMORY tier.
