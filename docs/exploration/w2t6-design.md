# W2T6-FREEZE — full Theorem 6 (per-m moment ↔ eigenvalue) via the η / L-function apparatus

Design pass author: **W2T6-FREEZE** (Opus). Status: **FROZEN, ready for executor pickup.**
Scope: the Fable-blocked gold-thread node — prove Harcos Thm 6 for *all* `n ≥ 1`
(the landed substrate has only `n = 1`). Read-only pass; this doc is the sole deliverable.

Source pinned at page-image fidelity: Harcos, *Weil's bound for Kloosterman sums*, §2–3,
pp. 4–8. Every definition below is transcribed from the page images (Def 3/4/5, Lemma 6/7,
Thm 3/4/5/6, Cor 2/3). Substrate: `Salt/Weil/{Kloosterman,ArtinSchreier,Orbits,LocalFactor,Moments}.lean`.

---

## 0. Headline decisions

1. **The full-Thm-6 target reduces to an `m`-free statement**, because Harcos's `η^m` is just
   `η` with the base parameters twisted `(a,b) ↦ (ma,mb)`, and the substrate already lands the
   `m`-twist (`kloostermanMoment_twist`). We prove
   ```
   kloostermanMoment a b n = - localPowerSum (kloosterman a b).re p n     (∀ n ≥ 1, a≠0, b≠0)
   ```
   and get the per-`m` identity `−(αₘⁿ+βₘⁿ) = Σₜ e_p(m·Trₙ(at+bt⁻¹))` by instantiating
   `(a,b) := (m·a, m·b)`. This is the *all-n generalization of the landed
   `kloostermanMoment_one_eq_neg_localPowerSum`*.

2. **Route for part (3) — the L/ζ rationality — is the FINITE COMBINATORIAL NEWTON IDENTITY,
   NOT the formal `PowerSeries.log`/`derivativeFun` route.** The kill-check's "PowerSeries route
   GREEN" is *necessary-but-not-sufficient*: `PowerSeries.log`/`derivativeFun` do exist, but the
   log-derivative argument fundamentally needs the **Euler product over irreducible monic
   polynomials of `𝔽_p[X]`**, and mathlib has **no** Euler-product theory for polynomial rings
   (only `Mathlib.NumberTheory.EulerProduct` over ℕ). Any power-series realization — even a
   degree-`n`-truncated finite product — must still prove the same UFD fact
   (`[Tⁿ] ∏(1−η(k)T^{deg k})⁻¹ = Σ_{monic deg n} η(k)`) and *adds* power-series overhead on top.
   The finite Newton reindex proves exactly that UFD content with the least scaffolding and
   produces the three-term recurrence that **matches the already-landed `localPowerSum_rec`
   verbatim**. See §5.

3. **`a ≠ 0` and `b ≠ 0` are load-bearing hypotheses** (III.3‴ catch, numerically confirmed at
   p=5, §6). The identity holds trivially at `n=1` for *all* `a,b`, but **fails at `n ≥ 2`**
   whenever `a=0` or `b=0`. The `n=1` landed lemma is hypothesis-free; the full node is not.

4. **η is defined by the COEFFICIENT form using `Polynomial.nextCoeff`** — not via roots in an
   algebraic closure. `nextCoeff` auto-collapses the constant-polynomial case to `1`
   (`nextCoeff = 0` at degree 0), and complete multiplicativity follows from the mathlib lever
   `Polynomial.Monic.nextCoeff_mul` (probe-verified) plus `coeff_mul`. No closure, no `roots`
   multiset in the *definition*.

5. **The proof splits into three independent mathematical ingredients + a trivial endgame:**
   `H1` (orbit reorganization: moment = irreducible-sum), `H2` (Theorem 5: the coefficient
   values `a_d`), `H3` (Newton: `n·a_n = Σ a_{n-j} c_j`), `H4` (2-step induction matching
   `localPowerSum_rec`). `H1` is the critical-path node (subsumes W1.3′'s orbit substrate).

---

## 1. Exact source definitions (transcribed from the page images)

Additive character `e_p : 𝔽_p → ℂ` = the standard primitive char; substrate `ZMod.stdAddChar`.
Kloosterman sum `S(a,b;p) = Σ_{t∈𝔽_p^×} e_p(at + bt⁻¹)`; substrate `kloosterman a b`
(def: `Σ_{t:(ZMod p)ˣ} stdAddChar (a·t + b·t⁻¹)`, **no sign**), real by `kloosterman_conj`.

**Definition 3 (n-trace).** For `α ∈ 𝔽_{pⁿ}`, `Trₙ(α) := Σ_{i=0}^{n−1} σⁱ(α)`, `σ : x ↦ xᵖ`.
Substrate: `Algebra.trace (ZMod p) (GaloisField p n)`; character `ψₙ = e_p∘Trₙ` = `traceAddChar p n`.

**Theorem 4 (Artin–Schreier count).** `#{x∈𝔽_{pⁿ} : xᵖ−x = y} = p·[Trₙ(y)=0]`. Substrate:
`card_artinSchreier_solutions` (ArtinSchreier.lean), used by `sum_kloostermanMoment_twist`.

**Definition 4 (η).** For `k(X) = c₀Xᵈ + ⋯ + c_d ∈ 𝔽_p[X]` with `c₀ ≠ 0 ≠ c_d`, split
`k = c₀(X−t₁)⋯(X−t_d)` over `𝔽̄_p`, and set
```
η(k) := e_p(a(t₁+⋯+t_d)) · e_p(b(t₁⁻¹+⋯+t_d⁻¹))
      = e_p(−a·c₁/c₀) · e_p(−b·c_{d−1}/c_d).       [Vieta: Σtᵢ = −c₁/c₀, Σtᵢ⁻¹ = −c_{d−1}/c_d]
```
For all other `k` (i.e. `c_d = 0`, equivalently `X ∣ k`, including `k=0`), `η(k) := 0`.
The `m`-twist: `ηᵐ(k) = η(k)ᵐ = e_p(ma·Σt)e_p(mb·Σt⁻¹)` = `η` with `(a,b) ↦ (ma,mb)`.

**Lemma 6.** `|η(k)| ≤ 1`, and `η` is **completely multiplicative**: `η(k₁k₂) = η(k₁)η(k₂)`.

**Definition 5 / Lemma 7 (L-function, Euler product).** `L(s,ηᵐ) = Σ_{k monic} ηᵐ(k)·p^{−deg(k)s}`,
and `L(s,ηᵐ) = ∏_{k irred monic}(1 − ηᵐ(k)p^{−deg(k)s})⁻¹` for `ℜs > 1`.

**Theorem 5.** `L(s,ηᵐ) = 1 + S(ma,mb;p)·p^{−s} + p^{1−2s}`. Proof (page 6): with
`a_d := Σ_{k monic, deg=d} ηᵐ(k)`,
```
a₀ = 1,   a₁ = S(ma,mb;p),   a₂ = p,   a_d = 0  (d ≥ 3).
```
`a₂ = p` via `p−1 + (Σ_{c∈𝔽_p^×} e_p(c))² = p−1+(−1)² = p`; `a_{d≥3}=0` because for `d≥3` the two
independent middle coefficients `c₁, c_{d−1}` (distinct since `1 ≠ d−1`) are each summed over all
of `𝔽_p`, and `Σ_{c∈𝔽_p} e_p(−ma·c) = 0` (orthogonality, needs `ma ≠ 0`).

**Theorem 3 / Corollary 2 (Gauss).** Frobenius orbit of size `d` in `𝔽̄_p` ↔ irreducible monic of
degree `d`; `X^{pⁿ}−X = ∏_{d∣n} ∏_{k irred monic, deg=d} k`. Substrate (Orbits.lean):
`galoisField_minpoly_irreducible`, `galoisField_minpoly_natDegree_dvd`,
`squarefree_X_pow_card_pow_sub_X`, `irreducible_monic_dvd_X_pow_card_pow_sub_X_iff`.

**Theorem 6 (equation 8).** For `1 ≤ m ≤ p−1`, `n ≥ 1`:
`−(αₘⁿ + βₘⁿ) = Σ_{t∈𝔽_{pⁿ}^×} e_p(m·Trₙ(at + bt⁻¹))`. Harcos's proof (pages 7–8): take the
logarithmic derivative of the Euler product (9), expand `log(1−z) = −Σ zⁿ/n`, differentiate
termwise, compare Dirichlet coefficients to get (10)
`−(αₘⁿ+βₘⁿ) = Σ_{d∣n} Σ_{k irred deg d} d·η^{mn/d}(k)`, then identify each orbit contribution
`d·η^{mn/d}(k) = Σ_{j} e_p(m·Trₙ(at_j+bt_j⁻¹))` via `Trₙ(t_j) = (n/d)Σt_i` (Def 3 + Galois
invariance of the trace).

---

## 2. Target statement (Lean) — probe-verified to elaborate

```lean
-- reduced, m-free (this is the node; a≠0, b≠0 required):
theorem kloostermanMoment_eq_neg_localPowerSum
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    kloostermanMoment a b n = - localPowerSum (kloosterman a b).re p n

-- per-m corollary (instantiate a := m*a, b := m*b; ma,mb ≠ 0 since m,a,b ≠ 0):
theorem kloostermanMoment_twist_eq_neg_localPowerSum
    (a b m : ZMod p) (hm : m ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    kloostermanMoment (m*a) (m*b) n = - localPowerSum (kloosterman (m*a) (m*b)).re p n
```

Both elaborate against the current substrate (probe `Probe2.lean`). The reduction in decision (1)
is real: `kloostermanMoment (m*a) (m*b) n` is literally the RHS of Thm 6 (the `m`-twisted moment),
and `localPowerSum (kloosterman (m*a) (m*b)).re p n = αₘⁿ+βₘⁿ` because
`localRootPair` is built from exactly `S = (kloosterman (m*a) (m*b)).re` with `α+β=−S`, `αβ=p`.

---

## 3. The η definition in Lean shape

```lean
open Polynomial in
/-- Harcos Def 4, coefficient form. `nextCoeff k = coeff (natDegree−1)` for deg ≥ 1 and `0`
for constants, so the constant case collapses to `1` automatically. Correct for MONIC `k`
(leading coeff 1 ⇒ Σroots = −nextCoeff). `X ∣ k ⇔ coeff 0 = 0 ⇒ η = 0`. -/
noncomputable def eta (a b : ZMod p) (k : (ZMod p)[X]) : ℂ :=
  if k.coeff 0 = 0 then 0
  else ZMod.stdAddChar (-(a * k.nextCoeff))
     * ZMod.stdAddChar (-(b * (k.coeff 1 / k.coeff 0)))
```

Basic facts to land alongside (all A/B):
- `eta_of_coeff_zero : k.coeff 0 = 0 → eta a b k = 0` (defeq/`simp`).
- `eta_one : eta a b 1 = 1` (coeff 0 = 1, nextCoeff = 0, coeff 1 = 0).
- `eta_C_ne_zero : c ≠ 0 → eta a b (C c) = 1`.
- `norm_eta_le_one : ‖eta a b k‖ ≤ 1` (product of two unit-norm chars, or 0).

**Complete multiplicativity (Lemma 6), the crux basic lemma — class B/C:**
```lean
theorem eta_mul (a b : ZMod p) {k₁ k₂ : (ZMod p)[X]} (h₁ : k₁.Monic) (h₂ : k₂.Monic) :
    eta a b (k₁ * k₂) = eta a b k₁ * eta a b k₂
```
Proof map (probe-verified levers):
- **coeff 0 splits:** `mul_coeff_zero : (k₁k₂).coeff 0 = k₁.coeff 0 * k₂.coeff 0`. If either is 0,
  both sides are 0.
- **Factor 1 (nextCoeff):** `Monic.nextCoeff_mul h₁ h₂ : (k₁k₂).nextCoeff = k₁.nextCoeff + k₂.nextCoeff`,
  then `stdAddChar (−a·(x+y)) = stdAddChar(−a·x)·stdAddChar(−a·y)` (`AddChar.map_add_mul`).
- **Factor 2 (coeff 1 / coeff 0):** `coeff_mul … 1` over `antidiagonal 1 = {(0,1),(1,0)}` gives
  `(k₁k₂).coeff 1 = c₁₀c₂₁ + c₁₁c₂₀`; with `(k₁k₂).coeff 0 = c₁₀c₂₀` and `c₁₀,c₂₀ ≠ 0` (field),
  `(c₁₀c₂₁+c₁₁c₂₀)/(c₁₀c₂₀) = c₂₁/c₂₀ + c₁₁/c₁₀`; split the char as above.
- Regroup the four factors. `ring`/`AddChar` bookkeeping.

Corollaries (B): `eta_pow : eta a b (k^r) = eta a b k ^ r` (induction via `eta_mul`, `pow_succ`,
`Monic.pow`), and `eta_multiset_prod` over a factor multiset of a monic (for H3).

---

## 4. Node ladder — Theorem 5 (the coefficient sums `a_d`)

**Naming note (disambiguation).** Standard convention, used throughout this doc: `a_d :=
Σ_{k monic, deg=d} η(k)` (the FULL monic sum, Harcos's `a_d`), and `c_n :=
Σ_{k irred, r·deg k=n} deg(k)·η(k)^r` (the irreducible / von-Mangoldt / log-derivative sum, the
Newton term). The freeze brief's "degree-n coefficient sum `c_n` with `c_1 = −S`" refers to the
former (`= a_d` here) — but note **`a_1 = +S`, not `−S`** (Harcos page 6 states `a_1 = S(ma,mb;p)`;
p=5 witness gives `a_1 = +0.38197 = +S`). The only `−S` in the picture is `P_1 = α+β = −S`
(`localPowerSum_one`). Do not carry a spurious sign into `a_1`.

Parametrize monic degree-`d` polys by the coefficient tuple (Harcos's own `Σ_{c₁…c_d}`), avoiding
the *missing* `Finite {k // k.Monic ∧ k.natDegree = d}` instance (probe: synthesis FAILS):

```lean
open scoped BigOperators in
/-- `a_d = Σ_{k monic, deg=d} η(k)`, summed over the non-leading coefficient tuple. -/
noncomputable def aCoeff (a b : ZMod p) (d : ℕ) : ℂ :=
  ∑ c : Fin d → ZMod p, eta a b (X^d + ∑ i : Fin d, C (c i) * X^(i:ℕ))
```
(The map `c ↦ X^d + Σ C(cᵢ)X^i` is a bijection onto monic degree-`d` polys; land a helper
`monicTupleEquiv` or work with `aCoeff` as the *definition* and never leave the tuple picture.)

| node | statement | class | ~lines | consumes |
|---|---|---|---|---|
| **W2T6.T5-a0** | `aCoeff a b 0 = 1` | A | ~10 | `eta_one` |
| **W2T6.T5-a1** | `aCoeff a b 1 = kloosterman a b` | B | ~60 | `eta`, `kloosterman_conj`, `AddChar.map_add_mul` |
| **W2T6.T5-a2** | `a ≠ 0 → b ≠ 0 → aCoeff a b 2 = p` | C | ~140 | `AddChar.sum_mulShift` (probe-verified), `isPrimitive_stdAddChar` |
| **W2T6.T5-ad** | `a ≠ 0 → 3 ≤ d → aCoeff a b d = 0` | C | ~120 | `AddChar.sum_mulShift`, `Fintype.sum_congr`/`Finset.sum_comm` |

Notes:
- **a1 = S is a conjugation identity, no reindex needed:** `aCoeff a b 1 = Σ_{c₀≠0} stdAddChar(−a c₀)·stdAddChar(−b/c₀) = Σ_{c₀≠0} stdAddChar(−(a c₀ + b c₀⁻¹)) = conj(kloosterman a b) = kloosterman a b` (real). It equals `↑(kloosterman a b).re` since `kloosterman_im = 0`.
- **a2 = p** is the fiddliest: split the `c₁` sum into `c₁=0` (contributes `p−1`) and `c₁≠0`
  (contributes `(Σ_{c∈𝔽_p^×} e_p(c))² = 1` after the orthogonality substitutions); needs BOTH
  `a≠0` and `b≠0` (each squared factor is `−1` only then). This is where `b≠0` first bites.
- **a_{d≥3}=0:** fix all coeffs but `c₁`; `Σ_{c₁} stdAddChar(−a c₁·(…)) = 0` by
  `AddChar.sum_mulShift` since `a ≠ 0` (the shift is nonzero). `a≠0` suffices here; `b≠0` not needed.
  Note the paper uses `c₁` and `c_{d−1}`; formally pick the single free variable `c₁`.

`AddChar.sum_mulShift` signature (probe): `∑ x, ψ (x * b) = if b = 0 then card R else 0` for
primitive `ψ`. This is the one orthogonality engine for both a2 and a_{d≥3}.

---

## 5. Node ladder — Theorem 6 (the chosen route)

Define the irreducible-sum `c_n` (the "honest per-n identity" — Newton's `Λ`-convolution term):
```lean
open scoped BigOperators Classical in
/-- `c_n = Σ_{k irred monic, r·deg k = n} deg(k)·η(k)^r`. Indexed as `Σ_{d∣n} d·Σ_{irred deg d} η(k)^{n/d}`. -/
noncomputable def cCoeff (a b : ZMod p) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (d : ℂ) *
    ∑ k ∈ (irredMonicOfDeg p d), eta a b k ^ (n / d)
```
where `irredMonicOfDeg p d` is the finite set of irreducible monic degree-`d` polynomials (build
as a `Finset` via the tuple/`AdjoinRoot` picture, or filter the degree-`d` monics — the
`irreducible` filter is decidable over a finite field).

### H1 — orbit reorganization (the moment IS the irreducible-sum). **Class C, critical path.**
```lean
theorem kloostermanMoment_eq_cCoeff (a b : ZMod p) {n : ℕ} (hn : n ≠ 0) :
    kloostermanMoment a b n = cCoeff a b n           -- holds for ALL a,b (no ab≠0 needed)
```
Two sub-lemmas:
- **H1a (orbit-trace / η identity), C.** For `k` irreducible monic of degree `d ∣ n`, `k ≠ X`,
  and `t ∈ 𝔽_{pⁿ}` a root of `k`:
  `traceAddChar p n (a·t + b·t⁻¹) = eta a b k ^ (n/d)`.
  Mechanism: `Trₙ(t) = (n/d)·Tr_d(t) = (n/d)·(−nextCoeff k)` and `Trₙ(t⁻¹) = (n/d)·(−coeff₁/coeff₀)`
  via the trace tower `Algebra.trace_trace` + `Algebra.trace` of a base element `= [K:F]•x`
  (`Algebra.trace_algebraMap`-family), and `Tr_d(t) = −nextCoeff(minpoly)` (Vieta / sum of the
  `d` conjugate roots). Then the char factors as an `(n/d)`-th power. **This is W1.3′'s payload;**
  its friction is exactly the "splitting levers" — relating `Trₙ` on `𝔽_{pⁿ}` to the degree-`d`
  minpoly data. Substrate ready: `galoisField_minpoly_*`, `galoisField_frobenius_orbit_isRoot`.
- **H1b (orbit partition), C.** Reindex `Σ_{t∈𝔽_{pⁿ}^×}` by `t ↦ minpoly(ZMod p) t`
  (`Finset.sum_fiberwise`/`sum_partition`): each fiber = the `deg k` roots of an irreducible monic
  `k` with `deg k ∣ n`, `k ≠ X`. Fiber size `= deg k` from separability
  (`squarefree_X_pow_card_pow_sub_X`) + splitting in `𝔽_{pⁿ}`
  (`irreducible_monic_dvd_X_pow_card_pow_sub_X_iff`). Combine with H1a (constant on each fiber) to
  get `Σ_{fiber} = deg k · η(k)^{n/d} = d·η(k)^{n/d}`, then sum over `d∣n`. `k = X` costs nothing
  (`η(X) = 0` and `0 ∉ 𝔽_{pⁿ}^×` — self-consistent).

### H2 — the `a_d` values. See §4 (W2T6.T5-a0/a1/a2/ad).

### H3 — Newton's identity (the UFD bridge). **Class C.**
```lean
theorem newton_aCoeff_cCoeff (a b : ZMod p) {n : ℕ} (hn : n ≠ 0) :
    (n : ℂ) * aCoeff a b n = ∑ j ∈ Finset.Icc 1 n, aCoeff a b (n - j) * cCoeff a b j
```
Proof (pure finite combinatorics, **no power series, no infinite products**): expand the RHS,
`aCoeff a b (n−j) · cCoeff a b j = Σ_{k' monic deg (n−j)} Σ_{π irred, r·deg π = j} η(k')·deg(π)·η(π)^r`.
Use `η(k')·η(π)^r = η(k')·η(π^r) = η(k'·π^r)` (`eta_pow`, `eta_mul`). Reindex the whole double
sum by `K := k'·π^r` (monic degree `n`); for fixed `K` the multiplicity-weighted sum collapses via
```
Σ_{π irred ∣ K} v_π(K)·deg(π) = deg(K) = n          (natDegree_multiset_prod on the factor multiset)
```
giving `Σ_{K monic deg n} η(K)·n = n·aCoeff a b n`. Levers (probe-verified):
`UniqueFactorizationMonoid.factors`, `Polynomial.natDegree_multiset_prod` (`0∉t → prod.natDegree =
(map natDegree t).sum`). **This is the heaviest bookkeeping node** (the `(k',π,r) ↔ (K, chosen prime
power)` reindex over `Finset`s of monic polynomials). It is the entire content that the rejected
PowerSeries/Euler-product route would ALSO have to prove — here with no analytic overhead.

### H4 — endgame (2-step induction). **Class B.**
```lean
theorem kloostermanMoment_eq_neg_localPowerSum
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    kloostermanMoment a b n = - localPowerSum (kloosterman a b).re p n
```
Set `S := (kloosterman a b).re`. From H2 (`a₀=1,a₁=S,a₂=p,a_{≥3}=0`) + H3, `c_n := cCoeff a b n`
satisfies, with `c₁ = a₁ = S` (Newton at `n=1`) and `c₂ = 2a₂ − a₁c₁ = 2p − S²` (Newton at `n=2`):
```
c_n = − S·c_{n−1} − p·c_{n−2}          for n ≥ 3
```
(Newton at `n≥3`: `0 = n·a_n = a₂c_{n−2} + a₁c_{n−1} + a₀c_n = p c_{n−2} + S c_{n−1} + c_n`, all
other `a_{≥3}=0`). Meanwhile `−localPowerSum S p` satisfies the **same** recurrence
(`localPowerSum_rec`: `P_{n+2} = −S P_{n+1} − p P_n`) with `−P₁ = S` (`localPowerSum_one`) and
`−P₂ = 2p − S²` (`P₂ = S²−2p` from the rec + `P₀=2`). Two-step induction ⇒ `c_n = −P_n`; H1 gives
`kloostermanMoment a b n = c_n = −P_n`. **The `n=1` base is exactly the landed
`kloostermanMoment_one_eq_neg_localPowerSum`; the `n=2` base is new (needs `a₂=p`, hence `ab≠0`).**

### The rejected route (recorded)
`PowerSeries.log`/`derivativeFun` over `PowerSeries ℂ`: would define `Z = 1 + S·X + p·X²`, its
inverse, and the log-derivative, then read off `[Xⁿ](X·Z'/Z) = c_n = −P_n`. **Blocked** because
identifying `X·Z'/Z`'s coefficients with the irreducible sum `c_n` requires
`Z = ∏_{irred}(1−η(k)X^{deg k})⁻¹` — an infinite product of power series with no mathlib support
for `𝔽_p[X]`; a truncated finite product still needs H3's UFD reindex. Newton dominates it.

---

## 6. III.3‴ case space + III.3″ witnesses

**III.3‴ enumerated case space (halt/flag if an executor strays outside):**
- **`a ≠ 0 ∧ b ≠ 0`** — REQUIRED for `n ≥ 2`. Not a convenience: the theorem is FALSE without it.
  Enters via H2 (`a₂=p` needs both; `a_{≥3}=0` needs `a≠0`). The `n=1` reduction is hypothesis-free.
- **`m` coprime to `p`** (`m ≠ 0`) — needed only to keep `ma,mb ≠ 0` under the twist. Handled by
  the `kloostermanMoment_twist_eq_neg_localPowerSum` wrapper; the core node never sees `m`.
- **`p` arbitrary prime** — NO `p=2` split and NO odd-`p` requirement. (Odd `p` + `ab≠0` is only
  needed for Cor 3's completing-the-square `y² = (xᵖ−x)²−4ab`, which is DOWNSTREAM of this node and
  already handled by the landed `sum_kloostermanMoment_twist` via the Artin–Schreier form.)
- **Two induction bases** (`n=1`, `n=2`), one recurrence (`n≥3`). `n=0` excluded (`hn : n ≠ 0`).

**III.3″ witnesses — computed at `p = 5` (`scratchpad/w2t6_witness.py`, all MATCH):**

| a | b | S=(kloos).re | −(αⁿ+βⁿ) vs Mₙ, n=1,2,3 | verdict |
|---|---|---|---|---|
| 1 | 1 | 0.381966 | (0.38197, 9.85410, −5.67376) = Mₙ | ✅ all n |
| 2 | 3 | 0.381966 | same (S depends only on ab≡1) | ✅ all n |
| 0 | 1 | −1 | Mₙ ≡ −1; −(αⁿ+βⁿ) = (−1, **9**, **14**) | ✅ n=1, ❌ n≥2 |
| 1 | 0 | −1 | Mₙ ≡ −1; −(αⁿ+βⁿ) = (−1, **9**, **14**) | ✅ n=1, ❌ n≥2 |
| 0 | 0 | 4 | Mₙ = (4, 24, 124); −(αⁿ+βⁿ) = (4, −6, 4) | ✅ n=1, ❌ n≥2 |

Auxiliary witnesses (p=5, a=b=1, all MATCH): `a₀,a₁,a₂,a₃,a₄ = 1, S, 5, 0, 0` (Theorem 5);
`c₁,c₂,c₃ = S, 2p−S², … = −P_n = M_n` (H1 + recurrence); Newton `n·a_n = Σ a_{n−j}c_j` holds
for `n = 1,2,3,4`. These pre-verify H2, H3, and the endgame arithmetic simultaneously.

---

## 7. Node plan, estimates, dependency order

```
Kloosterman/ArtinSchreier/Orbits/LocalFactor/Moments  (LANDED substrate)
         │
   W2T6.eta   (def eta, eta_one, eta_mul[C], eta_pow)            ~180 L, C
         ├──────────────┬───────────────────────────┐
   W2T6.T5 (a0/a1/a2/ad) │                    W2T6.H1 (H1a[C]+H1b[C]: moment=cCoeff)  ~500 L, C  ◀ critical path
   ~330 L, C            │                           │
         └──────┬───────┴─────── W2T6.H3 (Newton) ──┘   ~420 L, C
                │                    │
                └──── W2T6.main (H4 induction) ──────────  ~130 L, B
                             │
                W2T6.twist (per-m wrapper) ~40 L, A/B
```
Suggested new file: `Salt/Weil/LFunction.lean` (η + a_d + Newton) and `Salt/Weil/MomentEuler.lean`
(H1 + main), imported after `Orbits`/`Moments`. Total ≈ **1600 lines across 5 nodes, all C except
the endgame** — genuinely Fable-scale / multi-session. Recommended pickup order:
`eta → T5 → H3 → (H1 in parallel) → main → twist`. **H1 and H3 are the two independent hard C
nodes; H1a (the trace-tower Vieta identity) is the single riskiest step** and should get the first
serious scouting.

---

## 8. Gate charge (standing kill-check discipline for every executor on this ladder)

1. **Probe-elaborate every frozen statement before proving.** The signatures in §2/§3/§5 were
   elaborated against the live substrate (`Probe2.lean`); re-run after any mathlib bump. `nextCoeff`,
   `Monic.nextCoeff_mul`, `coeff_mul`, `mul_coeff_zero`, `AddChar.sum_mulShift`,
   `UniqueFactorizationMonoid.factors`, `natDegree_multiset_prod` are all probe-confirmed present.
2. **The `ab≠0` tripwire (III.3‴).** Any lemma on the `n≥2` path that does NOT carry `a≠0`/`b≠0`
   in scope is wrong or vacuous — audit it. Conversely do NOT thread `ab≠0` through H1 (it holds for
   all `a,b`) or the `n=1` base (hypothesis-free); a spurious hypothesis there signals a mis-proof.
3. **swat_vacuous / quantifier audit.** `aCoeff`, `cCoeff`, and the `Fin d → ZMod p` sums are over
   nonempty finite index types for the `d` we use; guard against `d=0` degenerating `aCoeff`
   (handled by `T5-a0`) and against `n.divisors` edge behavior at the induction seams (`n=1,2`).
4. **Verify each landed-lemma consumption against the ACTUAL signature.** Confirmed intended
   consumers: `kloostermanMoment_one_eq_neg_localPowerSum` (H4 base, `n=1`), `localPowerSum_rec`
   (H4 recurrence), `localPowerSum_one` (`−P₁=S`), `kloosterman_conj`/`kloosterman_im` (a₁ real),
   `kloostermanMoment_twist` (per-m wrapper), and the Orbits.lean Theorem-3 quartet (H1a/H1b).
   `sum_kloostermanMoment_twist` and `card_artinSchreier_solutions` are NOT consumed here (they are
   the Cor-3 route, downstream) — do not accidentally reroute through them.
5. **No `native_decide`, no new axioms.** On each node completion, `#print axioms` ⊆
   `{propext, Classical.choice, Quot.sound}`. The `Classical`/`Fintype.ofFinite` instances in
   Moments.lean are noncomputable but axiom-clean; keep new `Finset`s (`irredMonicOfDeg`) on the
   same footing (decidable `Irreducible` over a finite field, or `Classical` + `Fintype.ofFinite`).
6. **Iron rule 1 stands:** the `ab≠0` hypothesis is a *discovery about the true statement*, not a
   weakening to force a proof — it is mathematically necessary (§6 witnesses). Recording it here is
   the freeze doing its job; it is not a blueprint edit.

---

## 9. Friction / open risks (ranked)

1. **H1a trace-tower identity (highest risk).** `Trₙ(t) = (n/d)·Tr_d(t)` for `t ∈ 𝔽_{p^d} ⊆ 𝔽_{pⁿ}`
   needs `Algebra.trace_trace` composed with `trace` of a scalar-tower base element. The
   `GaloisField p d ↪ GaloisField p n` embedding (for `d ∣ n`) is *not* a bare instance — Orbits.lean
   obtains roots via `AdjoinRoot`/`nonempty_algHom_of_finrank_dvd` rather than a canonical inclusion.
   Expect real work wiring the intermediate field. If it stalls, fall back to computing `Trₙ(t)` as
   `Σ_{i<n} t^{p^i}` directly (Def 3 as a `Finset.sum` of Frobenius powers) and grouping the `n/d`
   period copies of the orbit — bypasses the tower but needs the orbit-period fact.
2. **H3 reindex bookkeeping.** The `(k', π, r) ↔ K` reindex over `Finset`s of monic polynomials is
   correct (numerically confirmed) but Multiset/`factors` manipulation in mathlib is verbose. Budget
   generously; consider an intermediate `∑_{K monic deg n} η(K)·(Σ_{π∣K} v_π(K)·deg π)` lemma proven
   in isolation before the reindex.
3. **`irredMonicOfDeg` construction.** No mathlib `Finite {k // Monic ∧ natDegree = d}` (probe:
   synthesis fails). Build the degree-`d` monic `Finset` from `Fin d → ZMod p` (the `aCoeff` tuple
   equiv) and filter by `Irreducible`; keep a single `monicTupleEquiv` helper shared by `aCoeff`,
   `cCoeff`, and H3 so the three sums live in one index picture.
4. **a₂ = p boundary term.** The `c₁=0` vs `c₁≠0` split (yielding `p−1 + (−1)²`) is where sign/one
   conventions of `stdAddChar` and the `−b/c₀` reciprocal must line up exactly; the p=5 witness
   (`a₂ = 5.00000`) is the anchor to test against with `decide`/`norm_num` on a concrete instance.
5. **Coercion hygiene.** `(kloosterman a b).re : ℝ` vs `kloosterman a b : ℂ` — a₁ produces a ℂ value
   equal to `↑(…).re` only after `kloosterman_im`. Match the substrate's `S := (kloosterman a b).re`
   convention exactly (as Moments.lean already does at `n=1`) to avoid a real/complex seam in H4.

---

## 10. GATE VERDICT — W2T6-GATE (adversarial adjudication, persist-at-adjudication)

**VERDICT: GO-WITH-BLOCK.** The design is mathematically sound (numerically triple-confirmed at
p=3,5,7 with an independently-written script — NOT the freeze's), every frozen statement elaborates
against the live substrate, and every critical mathlib lever exists. No kill; the blocks below are
name/spec corrections, not a re-cut. Executors MUST apply BLOCK-1..3 before proving.

### Findings by charge (gate's own numbers)

**Charge 1 — numerics (independent rebuild, p=3/5/7).** PASS.
- p=5 reproduced EXACTLY: (a,b)=(1,1) → `a_d = (1, 0.38197=S, 5, 0, 0)`; `M_n = (0.38197, 9.85410,
  −5.67376, −47.1033) = −(αⁿ+βⁿ)` all n; ab=0 exhibits match the §6 table verbatim ((0,1)/(1,0) →
  `M_n≡−1`, `−(αⁿ+βⁿ)=(−1,9,14,−31)`, fail n≥2; (0,0) → `M_n=(4,24,124,624)` vs `(4,−6,4,14)`).
- p=3 (1,1) → `a_d=(1,−1=S,3,0,0)`, Thm6 all n. p=7 (1,1) → `a_d=(1,2.04892=S,7,0,0)`, Thm6 all n
  (degree-4 field, 2401 elts enumerated). Both ab=0 sets fail n≥2. Single-prime thinness resolved.
- TWO structural confirmations beyond the freeze: (i) **H1 (`M_n=c_n`) holds for ALL (a,b) incl.
  ab=0** — True in every case, so H1 correctly needs no ab≠0. (ii) **Newton holds for ALL (a,b)
  incl. (0,0)** — H3 is a hypothesis-free combinatorial identity. The ab≠0 requirement enters ONLY
  through `a₂=p` and `a_{d≥3}=0`. Also: `a₁=kloosterman` holds universally (even (0,0): =p−1).

**Charge 2 — m-free reduction + m=0 exclusion.** SOUND (numerically closed).
- The twist `(a,b)↦(ma,mb)` makes `kloostermanMoment (ma)(mb) n` literally `Σₜ e_p(m·Trₙ(at+bt⁻¹))`
  (= Harcos eq 8 RHS, via the landed `kloostermanMoment_twist`), and the RHS `−localPowerSum
  (kloosterman(ma)(mb)).re p n = −(αₘⁿ+βₘⁿ)` because `localRootPair` is built from `S(ma,mb)`. The
  m-free core AT `(ma,mb)` reconstructs Harcos eq 8 exactly.
- m=0 exclusion is CORRECT: `M_n(0,0)=p^n−1` exactly (verified p=3/5/7, n=1..4), which is Cor 3's
  standalone `(p^n−1)` term, NOT covered by Thm 6 (needs m≠0). Verified for all p∈{3,5,7}, n∈{1,2,3}:
  `Σ_{m=0}^{p−1} M_n(ma,mb) = [p^n−1 − Σ_{m=1}^{p−1}(αₘⁿ+βₘⁿ)] = p·#{t:Trₙ=0}` — all three equal.
  So per-m Thm 6 (m=1..p−1) + the trivial m=0 term reconstruct Cor 3's LHS, and the reconstruction
  matches the substrate's already-landed `sum_kloostermanMoment_twist` fiber-count RHS. This node is
  correctly scoped to per-m Thm 6; Cor 3 assembly + m=0 stay downstream (gate charge #4 holds).

**Charge 3 — η / H2 audit.** SOUND, one lever misnamed.
- `Monic.nextCoeff_mul (hp : Monic p)(hq : Monic q) : (p*q).nextCoeff = p.nextCoeff + q.nextCoeff`
  — EXACT, both-monic required (matches `eta_mul`'s two Monic hyps). `nextCoeff(1)=0` (natDegree 0)
  gives `eta_one` for free. Complete-multiplicativity map in §3 is correct.
- `a_{d≥3}=0` proof is PURE additive orthogonality (`AddChar.sum_mulShift`, `a≠0` kills the free `c₁`
  sum), NOT "Artin–Schreier + orthogonality" — the CHARGE's framing is the inaccurate one; the
  freeze §4 is correct. `a₂=p` needs BOTH a≠0 and b≠0 (the `c₂=−b/a` term; b=0 ⇒ a₂=0), confirmed.
- **BLOCK-1 (lever name):** freeze §3 cites `AddChar.map_add_mul` as "probe-verified" — that constant
  does NOT exist. Correct name is **`AddChar.map_add_eq_mul (ψ)(x y) : ψ(x+y)=ψ x * ψ y`**. Also
  `nextCoeff_pow` is `Polynomial.Monic.nextCoeff_pow (hp : Monic p) : (p^n).nextCoeff = n•p.nextCoeff`
  (a bonus that gives `eta_pow` directly). All other §8 levers confirmed present:
  `Polynomial.nextCoeff`, `coeff_mul`, `mul_coeff_zero`, `AddChar.sum_mulShift`
  (`Σ x, ψ(x*b) = ↑(if b=0 then card R else 0)`), `ZMod.isPrimitive_stdAddChar`,
  `natDegree_multiset_prod`, `UniqueFactorizationMonoid.factors`.

**Charge 4 — H1a / H1 lemma list + the reverse-direction question.** ACHIEVABLE; reverse IS needed.
- H1 needs the **REVERSE** direction of Orbits' Thm 3 (the FORWARD `orbit ⊆ rootSet` alone is
  insufficient): H1b's partition completeness + fiber-size both require that every irreducible of
  degree d∣n has ALL d of its roots in 𝔽_{p^n}. Available: `irreducible_monic_dvd_X_pow_card_pow_sub_X_iff`
  (⟸ direction, landed) + **BLOCK-2:** name the packaging lemma `Polynomial.card_rootSet_eq_natDegree
  (hsep : Separable)(hsplit : Splits (map (algebraMap) k)) : card (rootSet K) = natDegree` (the freeze
  says "fiber size = deg k from separability + splitting" but never names it; it is the cheap lever the
  Orbits friction note anticipates).
- H1a is achievable via the Frobenius-sum FALLBACK (avoids the intermediate-field inclusion):
  `galoisField_trace_eq_sum_frobenius` (landed) gives `algebraMap(Trₙ t)=Σ_{i<n}t^{p^i}`; group n/d
  period copies using `t^{p^d}=t` (from the ⟸ iff at n:=d, since deg k = d ∣ d); identify the
  orbit-sum with `−nextCoeff` via **`Splits.nextCoeff_eq_neg_sum_roots_of_monic (hf)(hm) :
  nextCoeff = −roots.sum`** (landed in mathlib — the key H1a Vieta lever, name it).
- **BLOCK-3 (residual highest risk):** the RECIPROCAL side `Σ tⱼ⁻¹ = −coeff₁/coeff₀` has NO single
  mathlib lemma — compose via `Polynomial.reverse` (roots = reciprocals; k≠X ⇒ all roots ≠0) + the
  same Vieta on the reversed poly, or `Splits.coeff_zero_eq_prod_roots_of_monic` + coeff-1 product
  relations. This multi-step reciprocal-Vieta is the single riskiest sub-proof; scout it FIRST, as §7
  already recommends. Note the fallback route ALSO leans on the reverse direction (for `t^{p^d}=t`),
  not only the "orbit-period fact" as §9 friction #1 phrases it.
- Exact H1 lemma list (landed signatures): `galoisField_minpoly_irreducible`,
  `galoisField_minpoly_natDegree_dvd`, `irreducible_monic_dvd_X_pow_card_pow_sub_X_iff`,
  `squarefree_X_pow_card_pow_sub_X`, `card_rootSet_eq_natDegree`, `Finset.sum_fiberwise`/`sum_partition`
  (H1b); `galoisField_trace_eq_sum_frobenius`, `Splits.nextCoeff_eq_neg_sum_roots_of_monic`,
  `Splits.coeff_zero_eq_prod_roots_of_monic`+`reverse`, `Algebra.trace` linearity (`map_add`/`map_smul`,
  cf. `trace_smul_arg`), `AddChar.map_add_eq_mul` (H1a).

**Charge 5 — node plan / quantifier order / wave-1 cut.** SOUND.
- Every frozen statement PROBE-ELABORATES against the live substrate (gate re-ran the §2/§3/§5
  signatures; only `sorry`, zero elaboration errors). Quantifier/vacuity audit clean: `n≠0` guards the
  n=0 seam; `aCoeff a b 0 = η(1) = 1` (Fin 0 → singleton, non-vacuous); `cCoeff a b 0 = 0`
  (`Nat.divisors 0 = ∅`) but c₀ is never consumed (Newton/induction start at n≥1); `Icc 1 n` at n=1 is
  `{1}` giving `c₁=a₁`; `eta_mul` carries both Monic; H1/`newton` carry NO ab≠0 (correct — both hold
  ∀ a,b, confirmed); `T5-ad` a≠0 is sufficient (not tight — also holds a=0,b≠0 via the c_{d−1} sum —
  but keep as-is, main has both). `a₁=kloosterman a b` (NOT −S): the RHS sign is correct.
- Estimates (~1600 L, 5 C-nodes + B endgame) are reasonable vs the 150–210 L/file substrate baseline;
  H1 (~500) and H3 (~420) may run over given mathlib Multiset/`factors` verbosity (freeze already says
  "budget generously"). Wave-1 cut `eta → {T5, H3, H1 parallel} → main → twist` is correct: `eta` is the
  shared dependency; H1/H3 independent; main+twist cheap. H1a (reciprocal-Vieta) is the correct first
  scouting target.

### Verbatim-ready frozen statements (GATE-elaborated, BLOCK corrections folded in)

```lean
open Polynomial in
noncomputable def eta (a b : ZMod p) (k : (ZMod p)[X]) : ℂ :=
  if k.coeff 0 = 0 then 0
  else ZMod.stdAddChar (-(a * k.nextCoeff)) * ZMod.stdAddChar (-(b * (k.coeff 1 / k.coeff 0)))

noncomputable def aCoeff (a b : ZMod p) (d : ℕ) : ℂ :=
  ∑ c : Fin d → ZMod p, eta a b (X^d + ∑ i : Fin d, C (c i) * X^(i:ℕ))

noncomputable def cCoeff (a b : ZMod p) (n : ℕ) : ℂ :=          -- irredMonicOfDeg shared with H1/H3
  ∑ d ∈ n.divisors, (d : ℂ) * ∑ k ∈ (irredMonicOfDeg p d), eta a b k ^ (n / d)

theorem eta_one    (a b : ZMod p) : eta a b 1 = 1
theorem norm_eta_le_one (a b : ZMod p) (k : (ZMod p)[X]) : ‖eta a b k‖ ≤ 1
theorem eta_mul (a b : ZMod p) {k₁ k₂ : (ZMod p)[X]} (h₁ : k₁.Monic) (h₂ : k₂.Monic) :
    eta a b (k₁ * k₂) = eta a b k₁ * eta a b k₂                 -- uses AddChar.map_add_eq_mul
theorem eta_pow (a b : ZMod p) {k : (ZMod p)[X]} (h : k.Monic) (r : ℕ) :
    eta a b (k ^ r) = eta a b k ^ r
theorem T5_a0 (a b : ZMod p) : aCoeff a b 0 = 1
theorem T5_a1 (a b : ZMod p) : aCoeff a b 1 = kloosterman a b
theorem T5_a2 (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) : aCoeff a b 2 = (p : ℂ)
theorem T5_ad (a b : ZMod p) (ha : a ≠ 0) {d : ℕ} (hd : 3 ≤ d) : aCoeff a b d = 0
theorem kloostermanMoment_eq_cCoeff (a b : ZMod p) {n : ℕ} (hn : n ≠ 0) :   -- NO ab≠0
    kloostermanMoment a b n = cCoeff a b n
theorem newton_aCoeff_cCoeff (a b : ZMod p) {n : ℕ} (hn : n ≠ 0) :          -- NO ab≠0
    (n : ℂ) * aCoeff a b n = ∑ j ∈ Finset.Icc 1 n, aCoeff a b (n - j) * cCoeff a b j
theorem kloostermanMoment_eq_neg_localPowerSum
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    kloostermanMoment a b n = - localPowerSum (kloosterman a b).re p n
theorem kloostermanMoment_twist_eq_neg_localPowerSum
    (a b m : ZMod p) (hm : m ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    kloostermanMoment (m*a) (m*b) n = - localPowerSum (kloosterman (m*a) (m*b)).re p n
```
(All above elaborated by the gate against `Salt.Weil.Moments` + mathlib; `irredMonicOfDeg` is the one
object still to be constructed — build from the `Fin d → ZMod p` tuple equiv + `Irreducible` filter,
Classical/`Fintype.ofFinite` for axiom-cleanliness, and SHARE it across `cCoeff`, H1, H3.)
