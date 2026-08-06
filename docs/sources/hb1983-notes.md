# HB 1983 — source notes (fair-use research extract)

**Source.** D. R. Heath-Brown, *Prime Twins and Siegel Zeros*, Proc. London Math. Soc. (3) **47**
(1983), 193–224. Received 1 April 1982. Magdalen College, Oxford. (Prepared at the Universities of
Toronto and Texas, per the paper's acknowledgement.)

**Node:** HB-STAGE (source extraction, no Lean), 2026-08-03. **Staging debt retired.**

**COPYRIGHT / SCOPE.** The PDF is **not** in this repo and must never be. What follows is my own
summary written for the campaign: the logical skeleton, the *statements* of the definitions and
lemmas (mathematical formulas are facts and are transcribed faithfully), the parameter choices and
constants, and one-paragraph proof-idea summaries per lemma. It contains **no verbatim prose
passages** beyond short attributed phrases where the exact wording is the object of a campaign
ruling (e.g. the "sieving limit β ≥ 3" sentence that the N5 gate check turned on). Standard
fair-use research annotation.

**Page map.** PDF page *n* = journal page *n* + 192. All references below are to **journal pages**.
Every formula here was read this session from the page images; the regions that carry campaign
weight (Thm 1, Cor 1, Lemma 5's κ/G, the S-set identity, S₁, (4.2), §8) were additionally
re-rendered at 400 dpi and re-read to defeat OCR risk.

**Labels.** Everything is GROUNDED (read this session) unless marked **[INFERENCE]** (my
reconstruction, not the paper's words) or **[MEMORY]**.

**Standing assumptions (p.196).** Throughout the paper: conditions (1.3)–(1.9) on the forms,
hypothesis (1.11) on the zero, and *x* in the range (1.13). All implied constants may depend on
α_i, β_i and ε. The constants are effective **except** in the proof of Theorem 2 (§8).
⚠ This is why Lemma 5 is *formally* stated under (1.11) even though its proof (§§5–7) consumes no
zero — see §11 below.

---

## §0. The results, with exact parameter windows

### Setup (pp.193–194)

Forms `l_i(n) = α_i n + β_i` (i = 1,2); write `l = l₁l₂`, and `α = (α₁, α₂)`. Conditions:

| # | condition |
|---|---|
| (1.3) | α_i ∈ ℕ, β_i ∈ ℤ (i = 1,2) |
| (1.4) | (α_i, β_i) = 1 |
| (1.5) | 2 ∣ α_i |
| (1.6) | α₁β₂ − α₂β₁ ≠ 0 |
| (1.7) | p ∣ α₁β₂ − α₂β₁ ⟹ p ∣ α_i (i = 1,2) |
| (1.8) | p ∣ α₁ ⟺ p ∣ α₂ |
| (1.9) | p ∣ α_i ⟹ p² ∣ α_i (i = 1,2) |

These are a *normalization*, not a restriction: HB shows (p.194) that an arbitrary admissible pair
reduces to this shape by replacing `l_i(n)` with the k pairs `l_i(kn+j)`, `1 ≤ j ≤ k`, with
`k = 4α₁²α₂²(α₁β₂ − α₂β₁)²` (the degenerate case `α₁β₂ − α₂β₁ = 0` is Dirichlet). Note
(1.4)+(1.5)+(1.7) ⟹ `l_i(n)` odd and `(l₁(n), l₂(n)) = 1`.

Twin primes proper come from the pairs `(4n−1, 4n+1)` and `(4n+1, 4n+3)` (p.195).

`𝔖 = 2 ∏_{p>2} (1 − (p−1)^{−2})` (1.2).

**The hypothesis.** (1.10): there is an effectively computable `C⁽⁰⁾` with `L(σ+it, χ) ≠ 0` for
`σ ≥ 1 − C⁽⁰⁾/log(q(|t|+2))`, except possibly for one real zero of a real χ (a *Siegel zero*).
**(1.11)**: `L(β₀, χ) = 0` for a **real primitive** character χ (mod q) and a **real** β₀ with

    1 − β₀ ≤ (3 log q)^{−1},        η := {(1 − β₀) log q}^{−1}  (so η ≥ 3),   L := log q.

`η ≪ q` by Davenport ch. 14 (14) — "an estimate which we shall use from time to time" (p.194).
Its load-bearing use: `z₀ ≤ A log log η ⟹ z₀ ≤ L^{1/3}` automatically (p.198).

### THEOREM 1 (p.195)

Let the forms satisfy (1.3)–(1.9) and let (q, χ, β₀) satisfy (1.11). Then, with `α = (α₁, α₂)`,

    Σ_{x < n ≤ 2x} Λ(l₁(n)) Λ(l₂(n)) = 𝔖 C(α) x + O(x (log log η)^{−1}),

    C(α) = 2 ∏_{p∣α, p ≠ 2} (1 − 2/p)^{−1},                                   (1.12)

**uniformly for**

    q^250 ≤ x ≤ q^500.                                                        (1.13)

The implied constant is **effective** and depends on α_i, β_i only.

### COROLLARY 1 (p.195; proved p.223)

    #{n ≤ x : l₁(n), l₂(n) both prime}
        = 𝔖 C(α) x (log x)^{−2} + O(x (log x)^{−2} (log log η)^{−1}),

**uniformly for `q^300 ≤ x ≤ q^500`.** Implied constant effective, depends on α_i, β_i only.
(A sequence of triples with η → ∞ therefore gives the asymptotic
`#{n ≤ x : l_i(n) both prime} ~ 𝔖C(α)x(log x)^{−2}` valid in each range `q^300 ≤ x ≤ q^500`;
for twins, `N(x) ~ 2𝔖C(4)(x/4)(log x)^{−2} ~ 𝔖x(log x)^{−2}`, since `C(4) = 2` — the (1.12)
product is empty at α = 4.)

### COROLLARY 2 (p.195; proved p.223) — THE FULCRUM LINK

For any α_i, β_i satisfying (1.3)–(1.9) there is an **effectively computable** positive constant
`C⁽¹⁾ = C⁽¹⁾(α_i, β_i)` such that: if `η ≥ C⁽¹⁾` for **infinitely many triples (q, χ, β₀)**, then
there are infinitely many n with `l₁(n), l₂(n)` simultaneously prime.

    C⁽¹⁾ = exp exp{2A (𝔖C(α))^{−1}},        A = the implied constant of Corollary 1   (p.223)

### THEOREM 2 (pp.195–196; proved p.223)

There is an **(ineffective)** positive constant `C⁽²⁾` such that at least one of the following holds:

  (i) every pair of forms satisfying (1.3)–(1.9) represents primes simultaneously for infinitely
      many n;
  (ii) for all q ≥ 2 and all χ (mod q), `L(σ+it, χ) ≠ 0` for `σ ≥ 1 − C⁽²⁾/log(q(|t|+2))`.

Proof (p.223): two cases. If there is a sequence of triples with η → ∞, take `C⁽²⁾ = 1` and (i)
holds by Corollary 2. Otherwise η is bounded (or no zeros satisfy (1.11)); if `η ≤ A` for all real
β₀ and all real χ then take `C⁽²⁾ = Min(A^{−1}, C⁽⁰⁾)`. **The ineffectivity is exactly "we cannot
decide which case, and sup η is not computable if finite" — Siegel's theorem is never used.**

### Remarks HB makes that bear on the campaign

- **C⁽³⁾ (p.196), the ineffectivity parable:** there is a constant `C⁽³⁾` such that to prove
  infinitude of twins it suffices to exhibit one pair `p, p+2` with `p > C⁽³⁾` (define `C⁽³⁾ = 1`
  if there are infinitely many; else `C⁽³⁾ = max{p : p, p+2 both prime}`).
- **Montgomery's remark (p.196):** results of this kind can be proved *more easily by the circle
  method*, but only under the **stronger** assumption `η(log q)^{−1} → ∞` (i.e. 1−β₀ = o(L^{−2})).
  The whole sieve/Kloosterman apparatus exists to weaken the quality demand into the band
  `1 − β₀ ≤ (const · log q)^{−1}`.
- **Goldbach (p.196):** the method would give `2n = p + p′` only for 2n in the sparse intervals
  `q^A ≤ 2n ≤ q^B` with q restricted to a very sparse set — HB's own sparsity caveat.
- **Prime gaps (p.196):** an effective `C⁽⁴⁾` with `p_{n+1} − p_n ≤ p_n^ε` for primes in a suitable
  range `q^A ≤ p_n ≤ q^B`, if (q,χ,β₀) has `η ≥ C⁽⁴⁾`.
- **Turán [13] (p.193):** in Turán's analysis of N(x) via L-zeros, zeros with real part β > 5/6
  make a *negligible* contribution — HB's paper is the reverse effect.
- **The underlying idea (p.196):** if η is large then most primes have χ(p) = −1, so μ²(n)χ(n)
  behaves like μ(n); replacing Λ by Λ̃ turns the target into a divisor-correlation sum of the
  `Σ_{x<n≤2x} d(n)d(n+1)` type, where Estermann's methods [5] apply in principle — but one must
  save a power of x, hence the Kloosterman work.

---

## §1. The skeleton (§2, pp.197–198)

Fix `2 ≤ z ≤ q` and set

    P = ∏_{2 < p < z, χ(p) = 1} p .

The four sums:

    S⁽⁰⁾ = Σ_{x < n ≤ 2x} Λ(l₁)Λ(l₂)
    S⁽¹⁾ = Σ_{x < n ≤ 2x, (l, qP) = 1} Λ(l₁)Λ(l₂)
    S⁽²⁾ = Σ_{x < n ≤ 2x, (l, qP) = 1} Λ̃(l₁)Λ̃(l₂)
    S⁽³⁾ = Σ_{x < n ≤ 2x, (l, qP) = 1} Λ*(l₁)Λ*(l₂)

**S⁽⁰⁾ → S⁽¹⁾** (p.197): `S⁽¹⁾ ≤ S⁽⁰⁾ ≤ S⁽¹⁾ + O(Σ_{(l,qP) ≠ 1} ΛΛ)`; the error is trivially
`≪ L² Σ_{p ∣ qP} L/log p ≪ L⁴ + L³z`, so **`S⁽⁰⁾ = S⁽¹⁾ + O(L⁴z)`**.

**The three weights.**

    Λ̃(n) = Σ_{d∣n} μ²(d) χ(d) log(n/d)                                  (p.196)
    Λ*(n) = Σ*_{d∣n} χ(d) log(n/d),   Σ* : if p < z and χ(p) = −1 then p² ∤ d   (p.197)

**The ± factorization (2.1).** For (n, q) = 1 write `n = n₊n₋` with

    n₊ = ∏_{p^e ∥ n, χ(p) = 1} p^e ,      n₋ = ∏_{p^e ∥ n, χ(p) = −1} p^e .    (2.1)

**f(n).** `f(n) = Σ_{d∣n} μ²(d)χ(d)`, multiplicative; if (n,q) = 1 then `f(n) = 2^{ω(n)}` or
`f(n) = 0` according as `n₋ = 1` or not (p.197).

**LEMMA 1** (p.198; proved p.201). Let (n, q) = 1. Then `Λ*(n) ≥ 0` and

    0 ≤ Λ̃(n) − Λ(n) ≪ f(n) log n + (f(n₊) − 1) Λ(n₋).

Trivially gives `S⁽¹⁾ ≤ S⁽²⁾`.

**LEMMA 2** (p.198; proved pp.201–203). Define `z₀ = (log q)/(log z)` (≥ 1). If `z₀ ≤ L^{1/3}` then

    S⁽¹⁾ = S⁽²⁾ + O(x z₀^{−1}) + O( x L^{−1} exp(A z₀) Σ_{p ≤ x, χ(p) = 1} p^{−1} log p ).

**LEMMA 3** (p.198; proved pp.206–207). `Σ_{p ≤ x, χ(p) = 1} p^{−1} log p ≪ L (log η)^{−1/2}`.
HB notes this "is not necessarily the best bound of its type, but it suffices".

Lemmas 2+3 ⟹ `S⁽¹⁾ = S⁽²⁾ + O(xz₀^{−1})` **if `z₀ ≤ A log log η`**; and since η ≪ q, `z₀ ≤ L^{1/3}`
then holds automatically.

**S⁽²⁾ → S⁽³⁾** (p.198): if `(l_i, qP) = 1` then `Λ̃(l_i) = Λ*(l_i)` **except** when `p² ∣ l_i` for
some `p ≥ z`. Since `Λ̃(l_i), Λ*(l_i) ≪ L 2^{ω(l_i)}`,

    S⁽²⁾ − S⁽³⁾ ≪ Σ_{p ≥ z} Σ_{x<n≤2x, p²∣l_i} L² 2^{ω(l₁)+ω(l₂)}
               ≪ x L² exp(A L (log L)^{−1}) z^{−1} ≪ x z₀^{−1}   (if z₀ ≤ A log log η).

**LEMMA 4** (p.198). `S⁽⁰⁾ = S⁽³⁾ + O(x z₀^{−1})` if `z₀ ≤ A log log η`.

So the chain is `S⁽⁰⁾ →(L⁴z) S⁽¹⁾ →(L1,L2,L3) S⁽²⁾ →(p²∣l_i tail) S⁽³⁾`, and everything after
Lemma 4 is about `S⁽³⁾`.

---

## §2. THE SIEVE PAGES (pp.198–200) — the N5 consumers

### 2a. The Rosser weights and (2.2) (p.198)

"The next stage of the proof uses a fundamental lemma derived from the **4-dimensional Rosser
sieve**, to deal with the condition (l, P) = 1 in S⁽³⁾. The necessary theory may be found in a
paper by Iwaniec [10]." For `d ∈ ℕ` and `D ≥ 2` there exist weights `λ_d^±(D)`, depending only on
d, D and the sign, with

    λ_1^±(D) = 1,        |λ_d^±(D)| ≤ 1  for all d,
    ± Σ_{d ∣ n} λ_d^±(D) ≥ 0  (n > 1),   λ_d^±(D) = 0 for d ≥ D.

Since `Λ*(l₁)Λ*(l₂) ≥ 0` (Lemma 1),

    Σ_{d∣P} λ_d^−(D) S(d)  ≤  S⁽³⁾  ≤  Σ_{d∣P} λ_d^+(D) S(d),                (2.2)

where

    S(d) = Σ_{x < n ≤ 2x, d ∣ l, (l,q) = 1} Λ*(l₁)Λ*(l₂),     D ≥ 2.

**Both signs are used at (2.2).** For the rest of §2 HB treats the **upper** bound only, "the
treatment of the lower bound being similar", and writes `λ_d` for `λ_d^+(D)` (p.199). At the end
(p.200): "An analogous argument shows that `S⁽³⁾ ≥ x𝔖C(α) + O(xe^{−z₀/4})`."

### 2b. LEMMA 5 — exact statement (p.199)

> **LEMMA 5.** Let `d ∣ P`, `(d, α) = 1`, and `d, z ≤ q^{1/3}`. Then
>
>     S(d) = κ (G(d)/d) { (L′(1,χ)/L(1,χ))² + A²(d) + A′(d) + C₀ }
>              + O( x L⁴ z^{−1} d^{−1} 4^{ω(d)} ).
>
> Here
>
>     κ = x L(1,χ)² ∏_{p∣q, p∤α} (1 − 2/p) · ∏_{p∣α} (1 − χ(p)/p)²
>           · ∏_{p∤α, χ(p)=1} (1 − 1/p²) · ∏_{p∤α, χ(p)=−1} (1 − 2/p)(1 + 1/p)² ,
>
>     G(d) = 2^{ω(d)} ∏_{p∣d} ( (2p − 1)/(p + 1) ).
>
> Moreover `A(d), A′(d)` are **additive** functions for which
>
>     A(p) ≪ log p,      A′(p) ≪ B log p,      B := L + |L′(1,χ)/L(1,χ)| ,
>
> and `C₀` is **independent of d** and satisfies `C₀ ≪ BL`.

HB: "The proof of this lemma is the most difficult part of the paper, there being many
complications of detail. However, the underlying principle, of reducing the problem to an
estimation involving Kloosterman sums, is well known." (p.199)

Note `G(p) = 2(2p−1)/(p+1) < 4`, and `1 − G(p)/p = (p−1)(p−2)/(p(p+1))` (used at p.207).

### 2c. The parameter choice and (2.3) (p.199)

Substituting Lemma 5 into (2.2) with **`z ≤ q^{1/3}`, `D = q^{1/3}`**, the error terms contribute

    ≪ x L⁴ z^{−1} Σ_{d ≤ D} d^{−1} 4^{ω(d)}  ≪  x L⁸ z^{−1}.                  (2.3)

### 2d. The Iwaniec S-set decomposition identity (p.199) — the CHECK-2 object

The construction of `λ_d` in [10, §3] is such that **there exists a set S depending on D** with:

- if `δ ∈ S` and `δ ∣ P` then `1 < δ ≤ Max(D, z²) ≤ q`;
- with `p(δ)` = smallest prime factor of δ and `P(δ) = ∏_{p ∣ P, p < p(δ)} p`, **for any function
  ρ(d)**

      Σ_{d∣P} ρ(d) λ_d  =  Σ_{d∣P} ρ(d) μ(d)  +  Σ_{δ ∈ S, δ∣P} Σ_{d ∣ P(δ)} ρ(dδ) μ(d).

In the notation of [10, §3], S has characteristic function `σ_d`. **"To obtain the bound δ ≤ q we
need the fact that the sieving limit satisfies β ≥ 3 for the case of dimension 4."**
Convention: `G(d) = 0` when `(d, α) ≠ 1`.

⟦This is the sentence the N5 gate check turned on. The β ≥ 3 fact is spent **only** on the support
bookkeeping `δ ≤ Max(D, z²) ≤ q`; the operating point is deep in the fundamental-lemma regime
(`(log D)/(log z) = z₀/3 → ∞`). Confirmed verbatim this session.⟧

### 2e. LEMMA 6 (pp.199–200) — the three densities

> **LEMMA 6.** Let `ρ₁(d) = G(d)/d`, `ρ₂(d) = G(d)A′(d)/d`, `ρ₃(d) = G(d)A(d)²/d`. Set
>
>     S^{(i)}(δ) = Σ_{d ∣ P(δ)} ρ_i(dδ) μ(d),      S_i = Σ_{d ∣ P} ρ_i(d) μ(d).
>
> Then `S^{(1)}(δ), S₁ ≥ 0`, and for any `δ ≤ q`, `δ ∣ P`,
>
>     S^{(2)}(δ), S^{(3)}(δ) ≪ B L S^{(1)}(δ).
>
> Moreover `S₂, S₃ ≪ B L S₁`.

### 2f. The p.200 assembly

Write `S_i′ = Σ_{d ∣ P} ρ_i(d) λ_d`. Then the S-set identity plus Lemma 6 give the **per-δ
transfer**

    |S_i′ − S_i| ≪ B L |S₁′ − S₁|      (i = 2, 3),        S_i ≪ B L S₁  (i = 2,3).

From (2.2) and (2.3):

    S⁽³⁾ ≤ κ S₁ { (L′(1,χ)/L(1,χ))² + O(BL) } + O(κ B² |S₁′ − S₁|) + O(x L⁸ z^{−1}).

**The fundamental-lemma application.** Since `(log D)/(log z) = ⅓ z₀`, the proof of
[10, Theorem 4] gives

    S₁′ − S₁ ≪ exp(−¼ z₀) S₁ .

**"As `G(p) ≤ 4` we need a sieve of dimension 4."** Hence

    S⁽³⁾ ≤ κ S₁ { (L′(1,χ)/L(1,χ))² + O(BL) + O(B² e^{−z₀/4}) } + O(x L⁸ z^{−1}).

**LEMMA 7** (p.200; proved pp.207–210). Whenever `z₀ ≤ A log log η`:

    L′(1,χ)/L(1,χ) = η L + O(L (log η)^{−1/2}),                                (2.4)
    κ S₁ = {1 + O(z₀ (log η)^{−1/2})} x 𝔖 C(α) (ηL)^{−2}.

**The closing move (p.200).** For `z₀ ≤ A log log η`,

    S⁽³⁾ ≤ {1 + O(e^{−z₀/4})} x𝔖C(α) + O(xL⁸z^{−1}) = x𝔖C(α) + O(x e^{−z₀/4}),

and analogously `S⁽³⁾ ≥ x𝔖C(α) + O(xe^{−z₀/4})`. With Lemma 4,
`S⁽⁰⁾ = x𝔖C(α) + O(xz₀^{−1})`, and **Theorem 1 follows on taking `z₀ = A log log η`.**

**THE STRUCTURAL CANCELLATION.** Main term `= κS₁ · (L′/L(1,χ))² = x𝔖C(α)(ηL)^{−2} · (ηL)²
= x𝔖C(α)`. The zero-dependent factors cancel **exactly**; the zero never feeds the *size* of the
main term. It is consumed only (i) to make Λ̃ ≈ Λ (Lemma 3) and (ii) to control errors. This is why
the quality η enters only logarithmically. **[INFERENCE — the identity is HB's; the framing is
ours, and it matches the recorded reading at `fulcrum_audit_source.md:75–78`.]**

**Relative-error ledger at the assembly** (all divided by `(L′/L)² = (ηL)²(1+o(1))`):
`O(BL)/(ηL)² = O(1/η)` (since `B ≍ ηL`); `O(B²e^{−z₀/4})/(ηL)² = O(e^{−z₀/4})`;
`O(xL⁸z^{−1})` absorbed since `z = q^{1/z₀}` with `z₀ ≤ A log log η ≤ A log log q`.
**[INFERENCE — HB does not display this ledger; it is the arithmetic behind his one-line
conclusion.]**

---

## §3. §3 of the paper — proofs of Lemmas 1, 2, 6 (+ Lemma 8), pp.201–206

### Lemma 1 (p.201)

*Λ\* ≥ 0.* For `(a,b) = 1`, splitting `d ∣ ab` as `d = ef` gives the **twisted product rule**

    Λ*(ab) = Λ*(a) f*(b) + Λ*(b) f*(a),
    f*(n) = ∏_{p∣n, χ(p) = −1, p < z} (1 + χ(p)) · ∏_{p^e ∥ n, χ(p) ≠ −1 or p ≥ z} (1 + χ(p) + … + χ(p^e))  ≥ 0.

And `Λ*(p^e) = log p` if `χ(p) = −1, p < z`; otherwise
`Λ*(p^e) ≥ log p^e − log p^{e−1} + log p^{e−2} − … ≥ 0` (an alternating-sum positivity). Hence
`Λ*(n) ≥ 0` whenever (n,q) = 1.

*The Λ̃ − Λ bound.* Same product rule `Λ̃(ab) = Λ̃(a)f(b) + Λ̃(b)f(a)`; and
`Λ̃(p^e) = log p^e + χ(p) log p^{e−1} ≥ log p = Λ(p^e)`, so `Λ̃ ≥ Λ` everywhere. For (n,q) = 1,
`Λ̃(n) = Λ̃(n₋)f(n₊) + Λ̃(n₊)f(n₋)`, and `f(n₋) = 0` for `n₋ > 1`. Three cases:
`ω(n₋) ≥ 2 ⟹ Λ̃(n) = 0`; `n₋ = 1 ⟹ Λ̃(n) = Λ̃(n₊) ≤ 2^{ω(n₊)} log n₊ ≪ f(n) log n`;
`ω(n₋) = 1 ⟹ Λ̃(n) = Λ(n₋)f(n₊)` and `f(n₊) ≪ f(n₊) − 1` unless `n₊ = 1` (in which case
`Λ̃ − Λ = 0`).

### Lemma 2 (pp.201–203)

*Step 1 — the prime-power tail.* (3.1): if `(n, 2qP) = 1` then `f(l) ≤ f(l₊) = 2^{ω(l₊)} ≪ exp(Az₀)`
(every prime of `l₊` is ≥ z, so `ω(l₊) ≪ log x/log z ≍ z₀`). Hence `Λ̃(l₁)Λ̃(l₂) ≪ L² exp(Az₀)`, and
(3.2) the terms with `p^e ∣ l_i`, `p^e ≥ z`, `e ≥ 2` contribute
`≪ L² exp(Az₀) x z^{−1/2} ≪ x z₀^{−1} L^{−1}` (uses `z₀ ≤ L^{1/3}`).

*Step 2 — the combinatorial sets.* Put `R = ∏_{p<z} p` and

    U = {n ≥ z : (n, qR) = 1},   V = {p^e ≤ z : χ(p) = −1},   W = V ∪ {1},
    L₁ = {p : p ∣ qR},
    L₂ = {pv : χ(p) = 1, p ≥ z, v ∈ V},
    L₃ = {puw : χ(p) = 1, p ≥ z, u ∈ U, w ∈ W},
    L₄ = {uw : u ∈ U, w ∈ W}  ⊇ L₁ ∪ L₂ ∪ L₃.

Lemma 1 forces each `l_i` into one of these; and if `Λ̃(l₁)Λ̃(l₂) ≠ Λ(l₁)Λ(l₂)` then `(l₁,l₂)` or
`(l₂,l₁)` lies in `L₂ × (L₁∪L₂)` or `L₃ × L₄`. Thus
`S⁽²⁾ − S⁽¹⁾ ≪ S₁^{(3)} + S₂^{(3)} + S₁^{(4)} + S₂^{(4)} + xz₀^{−1}` where the `S_i^{(j)}` are the
corresponding restricted sums. (⚠ these `S_i^{(j)}` are **local to §3** and unrelated to
`S^{(1)},…,S^{(3)}` of §2 — see §10.)

*Step 3 — Selberg upper bounds.* With
`S(d₁,d₂;Z) = #{n : x < n ≤ 2x, d_i ∣ l_i, (l_i/d_i, ∏_{p ≤ z} p) = 1}` one gets (3.3)–(3.5), each
handled by:

> **LEMMA 8** (p.203; proved pp.203–204). Let `Z ≪ (x/d₁d₂)²`. Then
> `S(d₁,d₂;Z) ≪ (x/φ(d₁d₂)) (log Z)^{−2}`.

*Proof of Lemma 8:* Halberstam–Richert Theorem 4.1 (Selberg), with `𝒜 = {l/d₁d₂ : x < n ≤ 2x,
d_i ∣ l_i}`; the density `N(k)` is multiplicative with `N(p) = 2` if `p ∤ d₁d₂α`, `N(p) = 1` if
`p ∣ d₁d₂, p ∤ α`, `N(p) = 0` if `p ∣ α`; conditions (Ω₁), (Ω₂), (Ω₂(2)) of [7] hold; then
`S ≪ XW(Z^{1/5}) + Σ_{d < Z^{2/5}} μ²(d)3^{ω(d)}N(d)` with `X = x/(d₁d₂)` and
`W(Z^{1/5}) ≪ (log Z)^{−2} d₁d₂/φ(d₁d₂)`; the remainder sum is `≪ Z^{1/2}(log Z)^{−2}`.
Zero unless `(d_i, α_i) = 1` and `(d₁,d₂) = 1`.

The three sums then come out `≪ xz₀^{−1}` and `≪ xL^{−1}z₀³ exp(Az₀){Σ_{p ≤ x, χ(p)=1} p^{−1}log p}`
— the second is exactly the shape Lemma 2 advertises (the `z₀³` is absorbed into `exp(Az₀)`).

### Lemma 6 (pp.204–206)

`ρ₁` is multiplicative, so

    S^{(1)}(δ) = ρ₁(δ) ∏_{p ∣ P(δ)} (1 − ρ₁(p)) = G(δ)δ^{−1} ∏_{p ∣ P(δ)} (1 − G(p)p^{−1}),

and `0 ≤ G(p) ≤ p` gives `S^{(1)}(δ) ≥ 0`, `S₁ ≥ 0`. For `S^{(2)}(δ)` the key identity is (3.6):

    S^{(2)}(δ) = S^{(1)}(δ) { A′(δ) − Σ_{p ∣ P(δ)} A′(p) G(p)/(p − G(p)) }.

Since P is odd, `G(p) < p` for `p ∣ P(δ)`, and `A′(p) ≪ B log p`, so
`S^{(2)}(δ) ≪ S^{(1)}(δ){BL + Σ_{p ≤ q} B(log p)p^{−1}} ≪ BL S^{(1)}(δ)` **when δ ≤ q** (this is
where the S-set bound `δ ≤ q` is spent). Same for `S₂ ≪ BLS₁`.

For `S^{(3)}(δ)`: split `A(d)² = A₁(d) + A₂(d)` with `A₁(d) = Σ_{pp′ ∣ d, p ≠ p′} A(p)A(p′)` and
`A₂(d) = Σ_{p∣d} A(p)²` (d squarefree). `A₂` behaves like `A′` (as `A(p)² ≪ B log p`). For `A₁`,
(3.7)+(3.8) plus `A₁(δ) ≪ (log δ)²`, `A(δ) ≪ log δ`, `Σ_{p ∣ P(δ)} A(p)G(p)/(p−G(p)) ≪ log δ` give
**`S^{(3)}(δ) ≪ L² S^{(1)}(δ)`** and `S₃ ≪ L²S₁` — sharper than the stated `BL` (note `BL ≥ L²`
since `B ≥ L`).

---

## §4. §4 of the paper — Lemmas 3 and 7 (pp.206–210): the N3/N4 consumers

### Lemma 3 (pp.206–207)

Start from Davenport ch.12 formula (17) with `s = 1 + L^{−1}` and `s′ = 1 + aL^{−1}` (`a ≫ 1`):

    L′/L(s′,χ) − L′/L(s,χ) = Σ_ρ ( 1/(s′−ρ) − 1/(s−ρ) ) + O(1).

Isolate `ρ = β₀` (`(s′−β₀)^{−1} ≪ (s′−1)^{−1} ≪ La^{−1}`) and use `s′ − s ≪ aL^{−1}`:

    = −1/(s−β₀) + O(La^{−1}) + O( aL^{−1} Σ_{ρ ≠ β₀} |ρ−1|^{−2} ).                (4.1)

Three inputs finish it:

1. zeros with `|γ| ≥ 1` contribute `aL^{−1} Σ_{|γ|≥1} |2−ρ|^{−2} ≪ a` (Davenport ch.14 (3));
2. **Prachar's disc count** [12, ch.10, Lemma 2.1]: the number of zeros in `|s−1| ≤ r` is
   `≪ 1 + r log q` for `r ≤ 2` — UNCONDITIONAL — so the `ρ ≠ β₀, |γ| ≤ 1` part is
   `≪ aL^{−1}{r₀^{−2} + L r₀^{−1}}` with `r₀ = min{|1−ρ| : ρ ≠ β₀}`;
3. **Deuring–Heilbronn repulsion** (Jutila [11, Theorem 2]): `r₀ ≫ L^{−1} log η`, giving
   `aL^{−1} Σ_{ρ≠β₀,|γ|≤1} |ρ−1|^{−2} ≪ aL(log η)^{−1}`.

Also `L′/L(s′,χ) ≪ Σ Λ(n)n^{−s′} ≪ (s′−1)^{−1} ≪ La^{−1}`. Comparing,

    − L′(s,χ)/L(s,χ) = − 1/(s − β₀) + O(La^{−1}) + O(a L (log η)^{−1}).            (4.2)

**Optimal choice `a = (log η)^{1/2}`** — balancing `La^{−1}` against `aL(log η)^{−1}` — giving the
rate `L(log η)^{−1/2}`. From Davenport ch.12 (8), `−ζ′/ζ(s) = 1/(s−1) + O(1)` (4.3). Then

    Σ_{p ≤ x, χ(p)=1} (log p)/p ≪ Σ_{n ≤ x, χ(n)=1} Λ(n)/n ≪ −ζ′/ζ(s) − L′/L(s,χ),

and `1/(s−1) − 1/(s−β₀) = (1−β₀)/((s−1)(s−β₀)) ≪ (ηL)^{−1}(s−1)^{−2} = Lη^{−1} ≪ L(log η)^{−1/2}`.
∎ **This rate is the ultimate source of the paper's final error**: balancing `e^{Az₀}(log η)^{−1/2}
≤ z₀^{−1}` in Lemma 2 forces `z₀ = A log log η`, hence `O(x(log log η)^{−1})` in Theorem 1.

**What the zero is consumed for here:** (i) its *existence* — the `−1/(s−β₀)` term at `s = 1+L^{−1}`
dominates `−L′/L`; (ii) Deuring–Heilbronn repulsion, and only **logarithmically** in η; (iii) nothing
else. Prachar and Davenport inputs are unconditional.

### Lemma 7 (pp.207–210)

**(2.4)** falls out of the same analysis run at `s = 1` in place of `s = 1 + L^{−1}`, with the same
`a = (log η)^{1/2}`.

**κS₁.** First the Euler products (p.207):

    S₁ = ∏_{p < z, χ(p)=1, p∤α} (1 − G(p)p^{−1}) = ∏ (p−1)(p−2)/(p(p+1))   (same range).

Since `z^{z₀} = q`, at most `z₀` primes `p ∣ q` have `p ≥ z`, so
`∏_{p∣q, p∤α}(1−2/p) = {1+O(z^{−1}z₀)} ∏_{p<z, p∣q, p∤α}(1−2/p)`. Rearranging κS₁ (assuming
`z > α`):

    κ S₁ = {1 + O(z^{−1}z₀)} x C(α) F² ∏_{p<z}(1−p^{−1})² 𝔖(z,χ),                 (4.4)

    𝔖(z,χ) = 2 ∏_{2<p<z}(1 − (p−1)^{−2}) ∏_{p≥z, χ(p)=1}(1 − p^{−2})
                 ∏_{p≥z, χ(p)=−1}(1 − 2/p)(1 + 1/p)²,
    F = ∏_{p ≥ z} (1 − χ(p)p^{−1})^{−1}   (convergent),

    𝔖(z,χ) = {1 + O(z^{−1})} 𝔖,                                                   (4.5)
    ∏_{p<z}(1−p^{−1})² = {1 + O(L^{−1}z₀)} e^{−2γ₀} (log z)^{−2},   γ₀ = Euler's constant.  (4.6)

**The F computation** is where the zero re-enters. `log F = Σ_{n ≥ z} χ(n)Λ(n)/(n log n) + O(z^{−1/2})`.
Taking `x = q^{500}` in **Lemma 3** kills the `χ(n)=1` part
(`≪ L(log z)^{−1}(log η)^{−1/2} ≪ z₀(log η)^{−1/2}`), and Mertens handles the rest, giving

    log F = log log z − log log x + Σ_{n ≥ x} χ(n)Λ(n)/(n log n) + O(z₀(log η)^{−1/2}).   (4.7)

**The explicit formula** (Davenport ch.19 (13),(14)):

    ψ(y,χ) = − y^{β₀}/β₀ − Σ′_{|ρ| ≤ T} y^ρ/ρ + O(y T^{−1}(log qy)²) + O(y^{1/4} log y),
    for 2 ≤ T ≤ y, Σ′ omitting ρ = β₀ and 1 − β₀.

Take `y ≥ x`, `T = y^{1/3}`: errors `O(y^{3/4})`. Since `Σ′_{|ρ|≤T} |ρ|^{−1} ≪ (log qy)²`, the zeros
with `Re ρ ≤ 4/5` contribute only `O(y^{5/6})`. Partial summation gives (4.8), and then:

- **Jutila's density theorem** [11, Theorem 1] — UNCONDITIONAL:

      N(σ, T, χ) ≪ (qT)^{(5/2)(1−σ)}        (4/5 ≤ σ ≤ 1).                        (4.9)

  At `σ = 4/5`, zeros with `|ρ| ≥ q²` contribute `≪ q^{−1/2}` (4.10).
- **Deuring–Heilbronn again**: `σ₀ := max_{|ρ| ≤ q², ρ ≠ β₀} β ≤ 1 − A L^{−1} log η`, so the
  `ρ ≠ β₀` zeros contribute `≪ L u^{(σ₀−1)/2} ≪ L η^{−A}`, **using `q^{15/2} ≤ x^{1/4} ≤ u^{1/4}`,
  i.e. `x ≥ q^30`** — far weaker than the window's lower edge.

  🔴 **LOUD FLAG — the τ-range.** The maximum defining `σ₀` runs over **`|ρ| ≤ q²`**, i.e. this
  application of Deuring–Heilbronn must be uniform for `|Im ρ|` up to ≈ `q²`. Our landed contract
  `dh_repulsion_ordered` (TBalR8.lean:1752) hypothesizes **`|Im ρ| ≤ 1`** and therefore does **not**
  serve this site as it stands. Lemma 3's use of D–H (p.206) *is* confined to `|γ| ≤ 1` and is
  served. So the two D–H sites have **different τ-demands**, and only one of them is currently
  covered. Jutila [11, Theorem 2] is τ-uniform, so the mathematics is available — the gap is on our
  side of the interface. See §11.

Result:

    Σ_{u < n ≤ v} χ(n)Λ(n)/n = (1 − β₀)^{−1}(v^{β₀−1} − u^{β₀−1}) + O(L η^{−A}).     (4.11)

Partial summation on (4.12) turns this into
`Σ_{x<n≤y} χ(n)Λ(n)/(n log n) = −∫_x^y v^{β₀−2}/log v dv + O(η^{−A})`, uniformly in y, so

    log F = log log z − log log x − ∫_x^∞ v^{β₀−2}(log v)^{−1} dv + O(z₀(log η)^{−1/2}).

**The integral (p.210) — where the UPPER window edge is consumed.** Substituting `v = e^{tLη}`
(note `(1−β₀)^{−1} = ηL`):

    ∫_x^∞ v^{β₀−2}/log v dv = ∫_{t₀}^∞ e^{−t} dt/t,     t₀ = (1−β₀) log x = log x/(ηL) ≤ 500/η,
      = [e^{−t} log t]_{t₀}^∞ + ∫_{t₀}^∞ e^{−t} log t dt
      = log(η/500)(1 + O(η^{−1})) + ∫_0^∞ e^{−t} log t dt + O(η^{−1} log η)
      = log ηL − log log x − γ₀ + O(η^{−1} log η).

Hence `log F = log log z − log ηL + γ₀ + O(z₀(log η)^{−1/2})`, and (4.4)+(4.5)+(4.6) yield

    κ S₁ = {1 + O(z₀(log η)^{−1/2})} x 𝔖 C(α) (ηL)^{−2}.   ∎

⟦The window's **upper** edge `x ≤ q^500` is exactly the demand `t₀ = (1−β₀)log x ≤ 500/η → 0` —
"the zero's reach must cover the whole range", so that `v^{β₀−1} ≈ 1` throughout. Any fixed power
of q works; a polynomial-in-q window is FORCED (below by the Weil saving at (6.11), above here).⟧

---

## §5. §5 of the paper — Lemma 5, preliminary steps (pp.210–214): the N7 consumers

**The two-variable structure.** Everything in §§5–7 is about the bilinear object

    S(δ₁, δ₂; V₁, V₂) = Σ_{x<n≤2x, (l,q)=1, δ_i ∣ l_i}
                          ( Σ_{w₁v₁ = l₁/δ₁, v₁ > V₁} χ(w₁) ) ( Σ_{w₂v₂ = l₂/δ₂, v₂ > V₂} χ(w₂) ).

**Getting there (p.210).** Put `Q = ∏_{p<z, χ(p)=−1} p`. Then

    Λ*(n) = Σ*_{u∣n} χ(u) log(n/u)
          = Σ_{m∣Q} μ(m) Σ_{u ∣ n, m²∣u} χ(u) log(n/u)
          = Σ_{m ∣ Q, m < q} μ(m) Σ_{v ∣ nm^{−2}} χ(v) log(nm^{−2}/v)
            + O( d(n)(log n) Σ_{m² ∣ n, m ≥ q} 1 ),

i.e. Λ* is the μ-sieved version of `Λ′(n) = Σ_{u∣n} χ(u) log(n/u)`, truncated at `m < q`. The
truncation error in `S(d)` is `≪ Σ_{m ≥ q} x^{1+ε}m^{−2} ≪ x^{1+ε}q^{−1}`.

A Dirichlet-hyperbola manipulation for `Λ′(n)` with `e ∣ n` (p.211) converts each factor into the
`Σ_{v>V} χ(w)`-shape, and yields:

> **LEMMA 9** (p.211). Let `d ∣ P`. Then
>
>     S(d) = Σ_{m_i ∣ Q, m_i < q} μ(m₁)μ(m₂) Σ_{d = d₁d₂} Σ_{j_ik_i ∣ d_i} μ(j₁)μ(j₂)
>              × ∫_{(j₁k₁)^{−1}}^{∞} ∫_{(j₂k₂)^{−1}}^{∞} S(m₁²d₁j₁, m₂²d₂j₂; V₁,V₂) (dV₂/V₂)(dV₁/V₁)
>            + O(x^{1+ε} q^{−1}).

**Support conditions (5.1).** `S(δ₁,δ₂;V₁,V₂)` vanishes unless `(δ_i, q) = 1`, `(δ_i, α) = 1`,
`(δ₁, δ₂) = 1`.

**The dyadic decomposition (5.2).** Break the ranges into `R_i < v_i ≤ 2R_i`, `S_i < w_i ≤ 2S_i`
with `R_i/V_i` and `S_i` powers of 2; since `x ≪ l_i ≪ x`, one may assume
`R_i ≥ V_i`, `S_i ≫ 1`, `x ≪ δ_i R_i S_i ≪ x`.

**The CRT / residue-class step (p.211).** Decompose by residue classes mod q:

    S(δ₁,δ₂;V₁,V₂) = Σ_{R_i,S_i} Σ_{a_i,b_i=1}^{q} χ(b₁b₂) S,      (q, a_ib_i) = 1,    (5.3)
    S = #{(v_i,w_i) : R_i<v_i≤2R_i, S_i<w_i≤2S_i, δ_i v_i w_i = l_i(n),
                       x<n≤2x, v_i ≡ a_i, w_i ≡ b_i (mod q)}.

`S = 0` unless

    δ_i a_i b_i ≡ β_i (mod Δ),                                                    (5.4)
    α₁(δ₂a₂b₂ − β₂) ≡ α₂(δ₁a₁b₁ − β₁) (mod qα),                                   (5.5)

with `α = (α₁,α₂)` and `Δ = (α₁,q) = (α₂,q)`. **⟦q CUBE-FREE is consumed here⟧**: "since χ is real
and primitive, q can have no cube factors. Thus (1.8) and (1.9) yield `(α₁,q) = (α₂,q)`."

**Eliminating n and v₁** (case `S₁ ≤ R₁`, pp.212–213). Requires `(w₁,α) = (w₁,δ₂) = (w₁,q) = 1`
(5.6). Substituting `n = (δ₂v₂w₂ − β₂)/α₂` produces the equivalent congruence system

    δ₂v₂w₂ ≡ β₂ (mod α₂),                                                          (5.7)
    α₁δ₂v₂w₂ + α₂β₁ − α₁β₂ ≡ 0 (mod α₂δ₁w₁),                                       (5.8)
    α₁δ₂v₂w₂ + α₂β₁ − α₁β₂ ≡ α₂δ₁a₁b₁ (mod α₂q),                                   (5.9)
    v₂w₂ ≡ a₂b₂ (mod q),                                                           (5.10)

and these four are shown equivalent to the **single congruence**

    v₂w₂ ≡ C  (mod D δ₁ w₁),        D = α₂ q Δ^{−1},                          (5.11), (5.12)

with `C` independent of `v₂, w₂` and `(C, Dδ₁w₁) = 1`. The proof is a CRT consistency check
`(m_j, m_k) ∣ (X_j − X_k)` (5.13) over the four moduli
`α₁α₂ ; α₂δ₁w₁ ; α₂q ; α₁δ₂q` (with `X = α₁δ₂v₂w₂`), followed by an explicit lcm computation
`m₀ = α₁δ₂ · δ₁w₁ · α₂q/(α,q)`. Coprimality `(C, Dδ₁w₁) = 1` uses (1.7).

**The ψ-reduction (5.14)–(5.17).**

    S = Σ_{S₁<w₁≤2S₁, w₁ ≡ b₁ (q)} #{v₂ : v₂w₂ ≡ C (mod Dδ₁w₁), T₁ < v₂ ≤ T₂},      (5.14)
    T₁(w₁,w₂) = Max{ R₂, (α₂x+β₂)/(δ₂w₂), (α₂δ₁w₁R₁ + α₁β₂ − α₂β₁)/(α₁δ₂w₂) },      (5.15)
    T₂(w₁,w₂) = Min{ 2R₂, (2α₂x+β₂)/(δ₂w₂), (2α₂δ₁w₁R₁ + α₁β₂ − α₂β₁)/(α₁δ₂w₂) },   (5.16)

and with `ψ(θ) = θ − [θ] − ½` and `w̄₂` defined by `0 < w̄₂ ≤ Dδ₁w₁`, `w₂w̄₂ ≡ 1 (mod Dδ₁w₁)`:

    #{v₂ : …} = (T₂−T₁)(Dδ₁w₁)^{−1} + ψ((T₁ − Cw̄₂)/(Dδ₁w₁)) − ψ((T₂ − Cw̄₂)/(Dδ₁w₁)).  (5.17)

**LEMMA 10** (p.213–214, proved in §7). Let `(C,k) = 1`, `q ∣ k`, `(q,b) = 1`. Define `n̄` by
`0 < n̄ ≤ k`, `nn̄ ≡ 1 (mod k)`. Let `I` be a subinterval of `(E, 2E]`, `E ≥ 1`, and let `T` be any
real. Then

    Σ′_{n ∈ I} ψ(f(n)) ≪ (1 + |T| E^{−1} k^{−1})(E + k) q^{3/2} k^{ε − 1/4},

for `f(n) = (T − Cn̄)/k` **or** `f(n) = (T/n − Cn̄)/k`, where `Σ′` imposes `(n,k) = 1` and
`n ≡ b (mod q)`.

**Applying Lemma 10** (p.214). Take `k = Dδ₁w₁`, `E = S₂`, and (breaking the w₂-range into O(1)
parts so that `T_i(w₁,w₂) = T` or `T/w₂` on each) `T ≪ R₂ + x/δ₂ + δ₁w₁R₁/δ₂ ≪ x/δ₂`. Summing,

    total ψ-contribution to S ≪ δ₁ q^{5/2}(S₁S₂ + S₁² + x + xS₁/S₂) S₁^{ε−1/4}
                              ≪ δ₁ q^{5/2} x^{15/16+ε},

using `S₁ ≤ R₁` ⟹ `S₁ ≪ x^{1/2}` [**HB prints `x^{1/4}` — a typo in the paper, see below**];
valid provided `S₂ ≪ x^{1/2}` [**HB prints `x^{1/4}` — the same typo again**] and
`S₁S₂ ≫ x^{15/16}`, and trivially true otherwise (there are `O(S₁S₂)` terms in (5.14) and each ψ
is O(1)).

> ## ⚠️ **[corrected 2026-08-06 — RESOLVED AT THE SOURCE, p.214]**
>
> **THIS IS AN ERRATUM IN THE PUBLISHED PAPER, NOT A TRANSCRIPTION ERROR.** The notes originally
> read `S₁ ≪ x^{1/4}` because **that is what HB prints** (p.214, line 6: *"Since `S₁ ≤ R₁` we have
> `S₁ ≪ x^{1/4}` by (5.2)"*). `weil-trio-design-0806.md` §D6 ruled the exponent should be `1/2`
> and was **right about the mathematics**, but described it as a defect in these notes; the notes
> were a faithful transcription. Both statements are now reconciled here.
>
> **PROOF THAT HB MEANT `1/2`, FROM HB'S OWN NEXT DISPLAY.** He substitutes into
> `(S₁S₂ + S₁² + x + xS₁/S₂)·S₁^{ε−1/4}` and gets
> `(x^{3/8}S₂ + x^{7/8} + xS₁^{−1/4} + x^{11/8}S₂^{−1})x^ε`. Solve each substituted term for the
> `θ` in `S₁ ≪ x^θ` that it presupposes:
>
> | term | substitution | forces |
> |---|---|---|
> | `S₁S₂·S₁^{−1/4} = S₁^{3/4}S₂` | `→ x^{3/8}S₂` | `θ = 1/2` |
> | `S₁²·S₁^{−1/4} = S₁^{7/4}` | `→ x^{7/8}` | `θ = 1/2` |
> | `xS₁/S₂·S₁^{−1/4} = xS₁^{3/4}/S₂` | `→ x^{11/8}S₂^{−1}` | `θ = 1/2` |
>
> **Three independent confirmations, all `1/2`, none consistent with `1/4`.** The derivation from
> (5.2) agrees: `δ₁R₁S₁ ≍ x` with `S₁ ≤ R₁` gives `S₁² ≤ R₁S₁ ≍ x/δ₁ ≤ x`.
>
> **AND THE SAME TYPO OCCURS TWICE IN ONE SENTENCE — this closes the residual flagged earlier.**
> HB's proviso `S₂ ≪ x^{1/4}` is wrong for the identical reason (the symmetric (5.2) argument in
> the case `S₂ ≤ R₂` gives `S₂ ≪ x^{1/2}`), and **as printed it is what empties the regime**:
> `S₁ ≪ x^{1/2}` with `S₂ ≪ x^{1/4}` forces `S₁S₂ ≪ x^{3/4}`, contradicting `S₁S₂ ≫ x^{15/16}`.
> With both at `x^{1/2}` the regime is `S₁S₂ ∈ (x^{15/16}, x]` — **non-empty**.
>
> **THE CORRECTED ARGUMENT CLOSES, TERM BY TERM** (verified in exact rationals). Requiring each
> substituted term `≪ x^{15/16}`:
> `term1 ⟹ S₂ ≪ x^{9/16}` · `term2` holds always · `term3 ⟹ S₁ ≫ x^{1/4}` ·
> `term4 ⟹ S₂ ≫ x^{7/16}`.
> Given `S₁S₂ ≫ x^{15/16}` with `S₁, S₂ ≪ x^{1/2}`: `S₂ ≫ x^{15/16}/x^{1/2} = x^{7/16}` — **term 4
> is free, exactly at the margin** — and `S₁ ≫ x^{7/16} > x^{1/4}` — **term 3 is free**. Only
> term 1 binds, and `S₂ ≪ x^{1/2} ≤ x^{9/16}` discharges it. So the only conditions actually
> needed are **`S₁, S₂ ≪ x^{1/2}` (from (5.2)) and `S₁S₂ ≫ x^{15/16}`** — HB's `S₂ ≪ x^{1/4}` is
> not merely mistyped, it is **not needed at all**.
>
> **STATUS: the residual is CLOSED.** N7 no longer owes a resolution before consuming (5.19); it
> owes only the corrected exponents. This is the **second** erratum-grade finding in HB 1983,
> alongside the (5.5) hole at `v₂(q)=3` recorded in `weil-trio-design-0806.md` §D6 — and unlike
> that one, this affects the twin-prime road directly, since (5.19) is on the critical path.

> **LEMMA 11** (p.214). `S(δ₁,δ₂;V₁,V₂) = Σ_{R_i,S_i} Σ_{a_i,b_i=1}^{q} χ(b₁b₂) S`  (5.18), the
> `R_i/V_i, S_i` powers of 2 subject to (5.2) and `a_i,b_i` subject to (5.3),(5.4),(5.5); and if
> `S_i ≤ R_i` (i = 1,2) then
>
>     S = Σ*_{S_i<w_i≤2S_i, w_i ≡ b_i (q)} (T₂ − T₁)(Dδ₁w₁)^{−1} + O(δ₁ q^{5/2} x^{15/16+ε}),  (5.19)
>
> where `Σ*` imposes `T₂ > T₁`, `w₁` satisfying (5.6), and `(w₂, Dδ₁w₁) = 1`; D is (5.12) and the
> `T_i` are (5.15),(5.16).

HB's own remarks (p.214, campaign-relevant): **S is symmetric in i = 1,2 while the RHS of (5.19) is
not** — the §6 evaluation rectifies this, and by symmetry one may apply "appropriate analogues" of
(5.19) when `S_i ≤ R_i` fails. Also: *"the error term in (5.19) can be improved. However, all that
is necessary for our purposes is to have an exponent for x that is less than 1."*

---

## §6. §6 of the paper — Lemma 5, the leading terms (pp.215–221)

Three regimes, by whether `S_i ≤ R_i`.

**(a) `S_i ≤ R_i` for both i** (pp.215–216) — the main term. Lemma 11 applies directly; the `w_i`
conditions become symmetric: `S_i < w_i ≤ 2S_i`, `w_i ≡ b_i (mod q)`, and

    (w_i, α) = (w₁, δ₂) = (w₂, δ₁) = (w₁, w₂) = 1.                                 (6.1)

The summand of (5.19) is `K^{−1}(w₁w₂)^{−1} A` (6.2), with

    K = δ₁δ₂ q Δ^{−1},      A(w₁,w₂) = mes{ t ∈ ℝ : x ≤ t ≤ 2x, R_i ≤ l_i(t)/(δ_i w_i) ≤ 2R_i }.

Summation over `a_i, b_i` in (5.18): one must count solutions `a_i` of (5.3),(5.4),(5.5) given
`b_i ≡ w_i (mod q)`. The congruences (6.3),(6.4) reduce (via `t_2 ≡ γ t_1 (mod q/Δ)`) to: each
admissible `a₁` determines exactly one `a₂ (mod q)`, and coprimality `(a₂, q) = 1` becomes
`a₂ ≡ c a₁ + b (mod q/Δ)` with `(c, q/Δ) = (b, q/Δ) = 1` — **using (1.9) and q cube-free to get
`(α_i, q/Δ) = 1` and `(Δ, q/Δ) = 1`**. The count of available `a₁` is therefore

    ∏_{p ∣ q/Δ} (p − 2) = q Δ^{−1} ∏_{p ∣ q/Δ, p ∤ α} (1 − 2/p) =: q Δ^{−1} M,

and the contribution to `S(δ₁,δ₂;V₁,V₂)` is `M(δ₁δ₂)^{−1} F(R_i,S_i)` where
`F(R_i,S_i) = Σ_{w_i} χ(w₁w₂)(w₁w₂)^{−1} A(w₁,w₂)`.

**(b) `S₁ ≤ R₁`, `S₂ > R₂`** (p.216) — killed by **primitivity**. Here the analogous count produces
`Σ_{a₁,b₂} χ(b₂) = Σ χ(b₂)` over `b₂` subject to (6.5) and `(b₂ + b″, q/Δ) = 1`; Möbius-expanding
that coprimality gives `Σ_{d ∣ q/Δ} μ(d) Σ χ(b₂)` with the inner sum over a congruence class
mod `dΔ`. **Since χ is primitive, this last sum vanishes unless `dΔ = q`** — so (6.6) is O(1), and
the whole regime contributes `≪ x L⁴ (q δ₁δ₂)^{−1}` (using `Δ ≤ α₁ ≪ 1`). Symmetric for
`S₂ ≤ R₂, S₁ > R₁`.

**(c) `S_i > R_i` for both i** (p.217) — killed by the **real-primitive character-sum bound**. One
must estimate `Σ_{a_i} χ(a₁a₂)` subject to (6.7),(6.8); the same `t_i ≡ γ_i t (mod q/Δ)`
parametrization turns it into

    |Σ| = | Σ_{t=1}^{q/Δ} χ(Δγ₁ t + β₁) χ(Δγ₂ t + β₂) | ,      γ_i = α_i/α .

HB then quotes (proof omitted as straightforward): **for a real primitive χ (mod q)**

    Σ_{t=1}^{q} χ(ut + u′) χ(vt + v′) ≪ (q, uv′ − vu′).

Hence `Σ ≪ Δ^{−1}(q, Δγ₁β₂ − Δγ₂β₁) ≪ Δ^{−1}(q, Δα^{−1}(α₁β₂ − α₂β₁)) ≪ 1`, **using (1.6)**
(`α₁β₂ − α₂β₁ ≠ 0`). Contribution again `≪ xL⁴(qδ₁δ₂)^{−1}`.

**Assembling (6.9).**

    S(δ₁,δ₂;V₁,V₂) = Σ_{R_i,S_i} M(δ₁δ₂)^{−1} F(R_i,S_i) + O(xL⁴(qδ₁δ₂)^{−1})
                       + O(δ₁δ₂ q^{13/2} x^{15/16+2ε}),      the sum over S_i ≤ R_i.

The `S₁ > R₁` terms of the first sum are trimmed by partial summation plus the **Pólya–Vinogradov-
free** bound (6.10) `Σ_{w ∈ I, (w,f)=1} χ(w) = Σ_{g∣f} μ(g) Σ_{w∈I, g∣w} χ(w) ≪ q d(f)` (valid since
`|Σχ(w)| ≤ q` over any interval): `F(R_i,S_i) ≪ x^{1/2+ε} q δ₁δ₂`, absorbed into the same error.

**(6.11) — where the LOWER window edge is consumed.** Feeding (6.9) into Lemma 9 (the sums vanish
for `V_i ≫ x`, so the integrals may be taken over `V_i ≤ x`), for `d ≤ q^{1/3}` the error terms
contribute to `S(d)`

    ≪ x^{1+ε} q^{−1} + x^{15/16+3ε} q^{14} ≪ x^{1+ε} q^{−1},
        since δ₁δ₂ ≤ q⁴d²  and  x ≥ q^250.                                         (6.11)

⟦The true requirement is `q^{15} ≪ x^{1/16−2ε}`, i.e. `x ≫ q^{240+O(ε)}` — about 10 powers of q of
visible slack at the lower edge. HB himself remarks (p.214) that any exponent for x less than 1
suffices in (5.19).⟧

**The main term (pp.218–221).** `Σ_{R_i} A(w₁,w₂) = mes{t : x ≤ t ≤ 2x, l_i(t)/(δ_iw_i) ≥ V_i}`, so
the main terms contribute `M ∫_x^{2x} S(d;t) dt` with `S(d;t)` given by (6.12)/(6.13):

    S(d;t) = Σ_{d_i,r_i, r_i ≤ l_i(t)} S(d₁,r₁)S(d₂,r₂),                            (6.12)
    S(d_i,r_i) = χ(r_i)(r_id_i)^{−1} log(l_i(t)/r_i) M(r_i) Σ_{h_i ∣ (d_i,r_i)} h_i Σ_{j_i ∣ h_i} μ(j_i)/j_i,
    M(r) = Σ_{m ∣ Q, m² ≤ r} μ(m),

    S(d;t) = Σ_{r_i ≤ l_i(t), d = d₁d₂} χ(r₁r₂)(d r₁r₂)^{−1} log(l₁(t)/r₁) log(l₂(t)/r₂)
                 M(r₁)M(r₂)(d₁,r₁)(d₂,r₂),                                          (6.13)
    subject to (r_id_i, α) = (r₁,r₂) = (r₁,d₂) = (r₂,d₁) = 1.                        (6.14)

Three successive replacements clean this up:

1. `M(r) → N(r)` where `N(r) = 0` if `p² ∣ r` for some `p` with `χ(p) = −1`, else `N(r) = 1`; error
   `≪ L⁴ z^{−1} d^{−1} 4^{ω(d)}` (6.15) — **this is Lemma 5's stated error term**.
2. Extend the r_i-summation to infinity via the Dirichlet series `S′(d_i;t,σ)`, `S(d_i,l_i,σ)`
   (`σ > 1`), with `S′(d;t) = d^{−1} lim_{σ→1} Σ_{d=d₁d₂} S′(d_i;t,σ)`; the tail is estimated by
   partial summation (6.16) plus a Möbius/character manipulation and (6.10) again, total
   `≪ q d x^{ε−1/4}`.
3. Evaluate `S(d_i,l_i,σ) = f_{uv}(0,0)` where `f(u,v) = l₁^u l₂^v F(u,v) G(u,v)` factors as an
   **Euler product**:

       F(u,v) = ∏_{p ∤ α, χ(p)=1} (1 − p^{−2σ−u−v}) / {(1 − p^{−σ−u})(1 − p^{−σ−v})}
                · ∏_{p ∤ α, χ(p)=−1} (1 − p^{−σ−u} − p^{−σ−v}),
       G(u,v) = ∏_{p ∣ d} { (2 + p/(p^{σ+u}−1) + p/(p^{σ+v}−1)) (1−p^{−σ−u})(1−p^{−σ−v})/(1−p^{−2σ−u−v}) }.

Logarithmic differentiation gives `F_u(0,0)/F(0,0) = F_v(0,0)/F(0,0) = L′(σ,χ)/L(σ,χ) + C₁`,
`F_{uv}(0,0) = F(0,0)((L′/L)² + 2C₁(L′/L) + C₂)`, `G_u(0,0) = G_v(0,0) = G(0,0)A₁(d)`,
`G_{uv}(0,0) = G(0,0)(A₂(d) + A₁(d)²)`, where the `C_i` are continuous in σ ≥ 1, `≪ 1` uniformly in
q, t, σ, and `A₁, A₂` are additive in d with `A₁(p) ≪ log p`, `A₂(p) ≪ (log p)²`. Hence

    Σ_{d = d₁d₂} S(d_i,l_i,σ) = F(0,0)G(0,0){ (L′(σ,χ)/L(σ,χ))² + A₁(d)² + A₃(d)
                                              + L²C₃ + L C₄ (L′(σ,χ)/L(σ,χ)) },

with `A₃` additive, t-dependent, `A₃(p) ≪ (L + |L′(σ,χ)/L(σ,χ)|) log p`. Letting `σ → 1`:
`M F(0,0) → κ x^{−1}` and `G(0,0) → G(d)`; **Lemma 5 follows on integrating over t**, since the
t-integral of `A₃(d)` is again additive in d.

⟦Dictionary to Lemma 5's statement: `A(d) = A₁(d)`; `A′(d) = ∫ A₃(d) dt`; `C₀ = L²C₃ + LC₄(L′/L)
≪ L² + L|L′/L| ≪ BL`. `A₂` (with `A₂(p) ≪ (log p)²`) folds into `A₃` because `p ∣ d` and
`d ≤ q^{1/3}` force `log p ≤ L/3`. **[INFERENCE]** — HB states the identification only implicitly.⟧

---

## §7. §7 of the paper — proof of Lemma 10 (pp.221–223): the Kloosterman core

**The one deep input** — Estermann's bound [6] (1961) for the Kloosterman sum:

    S(k; u,v) = Σ_{n=1, (n,k)=1}^{k} e( (un + v n̄)/k ) ≪ d(k) k^{1/2} (k,u,v)^{1/2},   e(x) = exp(2πix).   (7.1)

Weil-strength, **elementary and effective** (Estermann's proof is elementary). This is the paper's
only algebraic-geometry-grade ingredient, and it enters as a black box.

The rest of §7 is classical harmonic analysis on `ψ`:

    ψ(θ) = − Σ_{0 < |m| ≤ K} e(mθ)/(2πim) + O( Min(1/(K‖θ‖), 1) ),                  (7.2)
    Min(1/(K‖θ‖),1) = Σ_{m=−∞}^{∞} a_m e(mθ)   (K ≥ 2),                             (7.3)
    a_m ≪ Min( (log K)/K, K/m² ).                                                    (7.4)

So everything reduces to `S_m = Σ′_{n ∈ I} e(mf(n))`, `m > 0`, with the trivial bound `S_m ≪ E`
(7.5) and, by partial summation for `f(n) = (T/n − Cn̄)/k`,

    S_m ≪ (1 + m|T|E^{−1}k^{−1}) | Σ′_{n ∈ I₀} e(Cm n̄/k) |,     I₀ ⊆ I.               (7.6)

The inner sum is completed by additive characters mod k (detecting `n ≡ r`), which produces exactly
the Kloosterman sums `S(k; s, Cm)`; with `k₀ = k/q` (recall `q ∣ k`) and
`Σ_{n ∈ I₀, q ∣ n−b} e(−sn/k) ≪ Min(E, ‖sq/k‖^{−1})`, (7.1) gives

    Σ′_{n∈I₀} g(n) ≪ d(k) k^{−1/2} q^{3/2} { E(k₀,Cm)^{1/2} + Σ_{1 ≤ s ≤ k₀} k₀(k₀,s)^{1/2} s^{−1} },
    Σ_{1 ≤ s ≤ k₀} (k₀,s)^{1/2} s^{−1} ≪ d(k₀) log(2k₀),                              (7.7)
    Σ_{M < m ≤ 2M} |S_m| ≪ (1 + M|T|E^{−1}k^{−1}) d(k)³ (log 2k)³ q^{3/2} M {E + k} k^{−1/2}.   (7.8)

Combining (7.2)–(7.4) with (7.5) for `m ≥ Kk^{1/2}` and (7.8) otherwise:

    Σ′_{n∈I} ψ(f(n)) ≪ d³(k)(log Kk)³ { EK^{−1} + (1 + K|T|E^{−1}k^{−1}) q^{3/2}(E+k) k^{−1/2} },

and the choice **`K = 2 + k^{1/4}`** gives Lemma 10. ∎

**Elementary vs. cited, in §§5–7.** Cited: Estermann [6] (7.1) only. Everything else — the CRT
gymnastics (5.4)–(5.17), the dyadic decomposition, the character-sum bound on p.217 (proof omitted
as "straightforward"), (6.10), the Euler-product differentiation of §6 — is elementary and
self-contained. **No β₀, no η, no zero-hypothesis appears anywhere in §§5–7** (re-verified this
session, page by page). Lemma 5 is *formally* under the standing (1.11) of p.196, but its proof
consumes none of it.

---

## §8. Constants census (every explicit constant / exponent, with its page)

| Object | Value | Page / eq |
|---|---|---|
| `𝔖` | `2 ∏_{p>2}(1 − (p−1)^{−2})` | p.193 (1.2) |
| `C(α)` | `2 ∏_{p∣α, p≠2}(1 − 2/p)^{−1}`; `C(4) = 2` | p.195 (1.12) |
| reduction multiplier k | `4α₁²α₂²(α₁β₂ − α₂β₁)²` | p.194 |
| `C⁽⁰⁾` | effective zero-free-region constant | p.194 (1.10) |
| **(1.11) quality** | `1 − β₀ ≤ (3 log q)^{−1}`; `η = {(1−β₀)L}^{−1} ≥ 3` | p.194 |
| `η ≪ q` | Davenport ch.14 (14) | p.194 |
| **Thm 1 window** | `q^250 ≤ x ≤ q^500` | p.195 (1.13) |
| **Cor 1 window** | `q^300 ≤ x ≤ q^500` | p.195 |
| **§8 intermediate window** | `q^250 ≤ x ≤ ½ q^500` (dyadic step) | p.223 |
| `C⁽¹⁾` | `exp exp{2A(𝔖C(α))^{−1}}`, A = Cor 1's constant | p.223 |
| `C⁽²⁾` | `1` (case 1) or `Min(A^{−1}, C⁽⁰⁾)` (case 2) — **ineffective** | p.223 |
| `C⁽³⁾` | `max{p : p, p+2 twin}` or 1 | p.196 |
| `C⁽⁴⁾` | effective, prime-gaps remark | p.196 |
| `L` | `log q` | p.196 |
| `A` | a **floating** effective positive constant, dep. only on α_i, β_i; not the same at each occurrence | pp.196–197 |
| `z₀` | `= (log q)/(log z) ≥ 1`; **chosen `z₀ = A log log η`**; needs `z₀ ≤ L^{1/3}` | pp.198, 200 |
| `z` | sieve cut, `z ≤ q^{1/3}` (so `z₀ ≥ 3`); `z = q^{1/z₀}` | pp.198–199 |
| `D` (sieve level) | `q^{1/3}` | p.199 |
| S-set support | `1 < δ ≤ Max(D, z²) ≤ q`; needs **sieving limit β ≥ 3 at dimension 4** | p.199 |
| Rosser weights | `λ_1^± = 1`, `|λ_d^±| ≤ 1`, `λ_d^± = 0` for `d ≥ D` | p.198 |
| sieve dimension | 4, because `G(p) = 2(2p−1)/(p+1) ≤ 4` | pp.199, 200 |
| FL gain | `S₁′ − S₁ ≪ exp(−z₀/4)S₁`, from `(log D)/(log z) = z₀/3` | p.200, Iwaniec [10, Thm 4] |
| `B` | `L + |L′(1,χ)/L(1,χ)|` (`≍ ηL` under (2.4)) | p.199 |
| Lemma 5 error | `O(xL⁴z^{−1}d^{−1}4^{ω(d)})`; summed: `O(xL⁸z^{−1})` (2.3) | p.199 |
| Lemma 3 rate | `≪ L(log η)^{−1/2}`; optimal `a = (log η)^{1/2}` | pp.198, 206 |
| D–H repulsion | `r₀ ≫ L^{−1} log η` (Jutila [11, Thm 2]) | p.206 |
| Prachar disc count | `≪ 1 + r log q` for `r ≤ 2` | p.206 |
| Jutila density | `N(σ,T,χ) ≪ (qT)^{(5/2)(1−σ)}`, `4/5 ≤ σ ≤ 1` | p.209 (4.9) |
| D–H (zero-free) | `σ₀ ≤ 1 − AL^{−1} log η` for `|ρ| ≤ q²`, `ρ ≠ β₀` | p.209 |
| explicit formula | `T = y^{1/3}`, errors `O(y^{3/4})`; `Re ρ ≤ 4/5` part `O(y^{5/6})` | p.208 |
| interior x-demand | `q^{15/2} ≤ x^{1/4}`, i.e. `x ≥ q^30` | p.209 |
| upper-edge demand | `t₀ = (1−β₀)log x ≤ 500/η → 0` | p.210 |
| Mertens constant | `∏_{p<z}(1−p^{−1})² = {1+O(L^{−1}z₀)} e^{−2γ₀}(log z)^{−2}` | p.207 (4.6) |
| Lemma 8 hypothesis | `Z ≪ (x/d₁d₂)²`; sifting exponents `Z^{1/5}`, `Z^{2/5}` | pp.203–204 |
| §5 modulus | `D = α₂ q Δ^{−1}` (**collides with the sieve level D**) | p.212 (5.12) |
| §5 ψ-error | `≪ δ₁ q^{5/2} x^{15/16+ε}` | pp.214 (5.19) |
| §6 error | `≪ xL⁴(qδ₁δ₂)^{−1} + δ₁δ₂q^{13/2}x^{15/16+2ε}` | p.217 (6.9) |
| **§6 lower-edge** | `x^{1+ε}q^{−1} + x^{15/16+3ε}q^{14} ≪ x^{1+ε}q^{−1}`, uses `δ₁δ₂ ≤ q⁴d²`, `x ≥ q^250` | p.218 (6.11) |
| §6 M(r)→N(r) | error `≪ L⁴z^{−1}d^{−1}4^{ω(d)}` | p.219 (6.15) |
| §6 tail | `≪ q d x^{ε−1/4}` | p.220 |
| Estermann | `S(k;u,v) ≪ d(k)k^{1/2}(k,u,v)^{1/2}` | p.221 (7.1) |
| Lemma 10 | `≪ (1+|T|E^{−1}k^{−1})(E+k)q^{3/2}k^{ε−1/4}`; `K = 2 + k^{1/4}` | pp.213–214, 223 |
| §8 p^e tail | `O(x^{1/2})` | p.223 |
| Λ at primes | `Λ(l_i(n)) = log x + O(1)` | p.223 |

**Porting note [INFERENCE].** Theorem 1 is *formally* asserted for every η ≥ 3, but is
non-vacuous only once `log log η` exceeds the implied constant; for bounded η both sides are `O(x)`
(the LHS by a trivial upper-bound sieve), so no separate threshold hypothesis is needed. A Lean
statement may keep the η ≥ 3 form.

**References of the paper** (for staging the next debts): [1] Atkin–Rickert; [2] Brent; [3] Chen;
[4] Davenport, *Multiplicative Number Theory* (chs. 12, 14, 19); [5] Estermann 1931 (divisor
correlations); [6] Estermann, *On Kloosterman's sum*, Mathematika 8 (1961) 83–86; [7]
Halberstam–Richert, *Sieve Methods* (Thms 3.11, 4.1); [8] Hardy–Littlewood; [9] Heilbronn; **[10]
Iwaniec, "Rosser's sieve", Acta Arith. 36 (1980) 171–202** (§3 = the λ_d construction and the S-set;
Thm 4 = the fundamental lemma); [11] **Jutila, "On Linnik's constant", Math. Scand. 41 (1977)
45–62** (Thm 1 = density, Thm 2 = Deuring–Heilbronn); [12] Prachar, *Primzahlverteilung* (ch.10
Lemma 2.1); [13] Turán.
**Staging status: Jutila [11] staged 2026-08-03 (`docs/sources/jutila1977-notes.md`). Iwaniec [10]
is the one source on this road still unstaged — and it is N5's source.**

---

## §9. THE CAMPAIGN CROSSWALK — what each node consumes

Road (from `docs/exploration/fleet-meeting-0803-brief.md:40–43`):
`N0 → {N1 ∥ N2} → {N3, N4} ∥ {N6 → N7} ∥ N5 → N8 → N9 → N10 → N11 → N12`.

| Node | Name | Pages consumed | Lemmas / equations | Notes |
|---|---|---|---|---|
| **N0** | T-BAL-BUDGET audit | p.194 (1.10),(1.11); p.206; p.209 | D–H interface (Jutila [11, Thm 2]) at **two** sites with **different τ-ranges**: `r₀ ≫ L^{−1}log η` over `\|γ\| ≤ 1` (Lemma 3) and `σ₀ ≤ 1 − AL^{−1}log η` over `\|ρ\| ≤ q²` (Lemma 7) | only `log η`-strength is ever used, but 🔴 our `dh_repulsion_ordered` assumes `\|Im ρ\| ≤ 1` and covers only the **first** site |
| **N1** | sharp ψ | p.208 | Davenport ch.19 (13),(14); `T = y^{1/3}`, errors `O(y^{3/4})`; `Σ′|ρ|^{−1} ≪ (log qy)²` | feeds Lemma 7 only |
| **N2** | crude zero-density | p.209 (4.9); p.206 | Jutila [11, Thm 1] `(qT)^{(5/2)(1−σ)}`, `4/5 ≤ σ ≤ 1`; Prachar disc count | **unconditional**; the `σ = 4/5` cut and `|ρ| ≥ q²` truncation (4.10) are the only uses |
| **N3** | HB Lemma 3 | stmt p.198; proof pp.206–207 | (4.1),(4.2),(4.3); `a = (log η)^{1/2}` | the consuming node **`Salt.HB.PretenseSum`** (TransferFull.lean:183) |
| **N4** | HB Lemma 7 | stmt p.200 (2.4); proof pp.207–210 | (4.4)–(4.12); the `log F` integral | needs N1 + N2 + the (4.6) Mertens constant; consumes the **upper** window edge; 🔴 needs D–H **τ-uniformly to `\|ρ\| ≤ q²`** — the one interface gap this staging found |
| **N5** | dim-4 Rosser–Iwaniec | pp.198–200 | λ_d^± properties; (2.2); the **S-set identity**; `δ ≤ Max(D,z²) ≤ q` (β ≥ 3); Lemma 6 (ρ₁/ρ₂/ρ₃, per-δ bounds); FL `e^{−z₀/4}`; `G(p) ≤ 4` | **route (a) as amended** needs: a first-failure decomposition of the kept-set complement (the `δ ≤ Max(D,z²)` analogue) **+ the per-δ transfer** `|S_i′−S_i| ≪ BL|S₁′−S₁|`; both λ^+ and λ^− used |
| **N6** | Weil deltas | p.221 (7.1); p.217 | Estermann `d(k)k^{1/2}(k,u,v)^{1/2}`; the real-primitive `Σχ(ut+u′)χ(vt+v′) ≪ (q,uv′−vu′)` | two *separate* character-sum inputs — the second is stated without proof in HB and must be supplied |
| **N7** | WP5-CORE (Lemma 5) | pp.210–223 (§§5,6,7) | Lemmas 9, 10, 11; (5.1)–(5.19); (6.1)–(6.16); (7.1)–(7.8) | **the biggest block, elementary, Siegel-free**; also needs `Λ*` positivity from Lemma 1 |
| **N8** | the §2 assembly | pp.197–204 + p.200 | Lemmas 1, 2, 4, 8 (the Λ̃/Λ* reduction) **and** the p.200 chain `S⁽³⁾ ≤ κS₁{…} + …` both signs | ⚠ the road's node list does not separately name Lemmas 1/2/4/8; they sit in N8's tray unless split out — **flag for pricing** |
| **N9** | Theorem 1 | p.195; assembled p.200 | Lemma 4 + the two-sided S⁽³⁾ bound; `z₀ = A log log η` | the structural cancellation `κS₁·(L′/L)² = x𝔖C(α)` lives here |
| **N10** | Corollaries 1 & 2 | p.195; proof p.223 | `p^e` tail `O(x^{1/2})`; dyadic sum `x = X/2, X/4, …`; window shrink 250 → 300; `C⁽¹⁾ = exp exp{2A(𝔖C(α))^{−1}}` | the `½q^500` intermediate window is the §8 dyadic step, **not** (1.13) |
| **N11** | door bridge | p.195 Cor 2 shape | one triple per modulus; the per-triple yield lives only in `[q^300, q^500]` | our side: `InfinitelyManySiegelZeros` (SiegelTwin.lean:85) → Cor 2's hypothesis `η ≥ C⁽¹⁾ i.o.` |
| **N12** | THE CROWN | pp.195–196 Thm 2; proof p.223 | the two-case split; `C⁽²⁾ = 1` / `Min(A^{−1},C⁽⁰⁾)` | ¬F horn already landed (`fulcrum_dichotomy`, Dichotomy.lean:102); only the F horn is owed |

**Cross-cutting facts every node must respect.**

1. **q cube-free** (from χ real primitive) is *consumed*, not convenient: at (5.5) to get
   `(α₁,q) = (α₂,q)`, and at p.216 to get `(α_i, q/Δ) = 1` and `(Δ, q/Δ) = 1` via (1.9).
2. **χ primitive** is consumed at p.216 (the `Σχ(b₂)` vanishing) — N7.
3. **χ real** is consumed in the very definition of `Λ̃`, `Λ*`, the `n₊n₋` splitting, and the p.217
   character-sum bound.
4. **(1.6)** (`α₁β₂ − α₂β₁ ≠ 0`) is consumed at p.217; **(1.7)** at (5.11)'s coprimality;
   **(1.9)** at pp.212, 215–216.
5. Only the `λ^−` side plus upper error bounds are needed for **existence** of twins; `λ^+` only
   sharpens to the asymptotic (pp.199, 200).

---

## §10. Notation hazards for a Lean port (read before naming anything)

- **`A` is a floating constant** (p.196–197): "an effective positive constant, depending only on
  α_i and β_i… not the same at each occurrence, so that we may write `e^{Ax} log x ≪ e^{Ax}`."
  Every `A` in the paper is a *fresh* existential. In Corollary 2's proof, `A` is instead a *fixed*
  named constant (Corollary 1's implied constant) — a different `A`.
- **`D` is overloaded**: the Rosser sieve level `D = q^{1/3}` (§2) vs. `D = α₂qΔ^{−1}` (5.12) in §5.
- **`S` is massively overloaded**: `S⁽⁰⁾…S⁽³⁾` (§2); `S(d)` (2.2); `S`, the Iwaniec set (p.199);
  `S^{(i)}(δ)`, `S_i`, `S_i′` (Lemma 6, p.199–200); `S_i^{(j)}` (§3 combinatorics, p.202);
  `S(d₁,d₂;Z)` (Selberg count, p.202); `S(δ₁,δ₂;V₁,V₂)` (p.211); the bare `S` of (5.3);
  `S_i` the dyadic w-scale (5.2); `S(d;t)`, `S(d_i,r_i)`, `S′(d_i;t,σ)` (§6); `S(k;u,v)`
  Kloosterman (7.1); `S_m` exponential sum (§7). **Eleven distinct meanings.**
- **`A(d)`, `A′(d)`, `A₁, A₂, A₃`** (Lemma 5, §6) vs. the floating constant `A` vs. `A(w₁,w₂)` the
  measure at (6.2). Four families.
- **`κ`, `G`, `F`, `M`** each have one meaning in §2/§4 and another in §6 (`F(u,v)`, `G(u,v)`,
  `M(r)`, `M` the a₁-count). `F` in (4.4) is the L-function tail product; `F(R_i,S_i)` in §6 is a
  character sum; `F(u,v)` is an Euler product.
- `Σ*` means two different things: the `Λ*` restriction (p.197) and (5.19)'s `T₂>T₁` restriction.
- `L` = `log q` throughout, but `L(w)` at p.202 is `Λ`-or-`L` on `W`, and `L(s,χ)` is the
  L-function. `l = l₁l₂`, `l_i(n)` the forms.
- `ψ` is both `θ − [θ] − ½` (§5, §7) and `ψ(y,χ)` the Chebyshev function (§4).

---

## §11. Checks against our recorded readings (`docs/exploration/fulcrum_audit_source.md`)

**CONFIRMED, verbatim-level** (spot-checked at 400 dpi): the hypothesis (1.11) and η ≥ 3; `η ≪ q`
and its one load-bearing use; the Thm 1 / Cor 1 / Cor 2 / Thm 2 statements and windows; `C⁽¹⁾ =
exp exp{2A(𝔖C(α))^{−1}}`; the S⁽⁰⁾→S⁽³⁾ chain and Lemmas 1–4; Lemma 5's full statement including
the `xL⁴z^{−1}d^{−1}4^{ω(d)}` error; the `β ≥ 3` / `δ ≤ Max(D,z²) ≤ q` sentence; the FL rate
`e^{−z₀/4}` from `(log D)/(log z) = z₀/3`; `G(p) ≤ 4 ⟹ dimension 4`; Lemma 6 and the per-δ
transfer; Lemma 3's rate and `a = (log η)^{1/2}`; Lemma 7's (2.4) and κS₁; the (4.9) density and
its unconditionality; `x ≥ q^30` at (4.10)/(4.11); the `t₀ ≤ 500/η` upper-edge consumption; (6.11)
and the `x ≥ q^250` lower edge; the structural cancellation; Siegel's theorem **never** used; the
`λ^−`-only remark; Montgomery's circle-method remark; the ineffectivity structure of Theorem 2.

**AUDIT FINDING RE-CONFIRMED (the important one).** `fulcrum_audit_source.md:91,98` records "no
β₀/η appears anywhere in §§5–7" as an audit finding rather than a stated claim. **Re-verified this
session page by page (pp.210–223): correct.** Lemma 5's only zero-flavoured content is the *value*
`L′(1,χ)/L(1,χ)` (and `B`), which is a value, not a hypothesis. The de-scoping is real, and a Lean
port may state Lemma 5 without (1.11).

**Corrections to the recorded readings (all minor; none changes a ruling):**

1. ⚠ **`fulcrum_audit_source.md:95`** transcribes the p.217 character-sum bound as
   `Σ_t χ(ut+u′)χ(t+v′) ≪ (q, uv′−vu′)`. The paper has **`Σ_{t=1}^{q} χ(ut+u′)χ(vt+v′)`** — the
   `v` in the second factor is missing in our copy. With `v` dropped, the stated bound
   `(q, uv′−vu′)` no longer matches its own arguments. **Fix before N6 quotes it.**
2. **`fulcrum_audit_source.md:84`** states Lemma 8 without its hypothesis. The paper's Lemma 8
   requires **`Z ≪ (x/d₁d₂)²`**. (Harmless in context — §3 verifies it at each use — but a Lean
   statement omitting it would be false.)
3. **`fulcrum_audit_source.md:99`** gives "Lemma 11 + §6 leading terms (pp.214–218)". §6 actually
   runs **pp.215–221**; Lemma 5 is completed at the top of p.221.
4. `fulcrum_audit_source.md:50` writes `P = ∏_{2<p<z, χ(p)=1} p` — correct — but note the paper
   also fixes `2 ≤ z ≤ q` at that point, and separately imposes `z ≤ q^{1/3}` from p.199 onward.
5. Not an error, but a resolution: the "**250-vs-300 window discrepancy**" flagged in
   `fulcrum-pass2.md:53,92` is **not** a discrepancy in the source. There are **three** distinct
   windows and all three are correct as printed: `q^250 ≤ x ≤ q^500` (Thm 1, (1.13));
   `q^250 ≤ x ≤ ½q^500` (the §8 dyadic intermediate, p.223); `q^300 ≤ X ≤ q^500` (Cor 1, after
   summing `x = X/2, X/4, …` and absorbing the `O(q^250)` tail). The pass-3 ratification
   (`fulcrum-pass3.md:17`) is confirmed by the bytes.

**Nothing in the paper contradicts a recorded ruling.** In particular the N5 gate check's three
verdicts (β ≥ 3 spent only on support; `G(p) ≤ 4` uniform; the S-set identity used at three
densities with the FL rate needed at ρ₁ only) are all confirmed verbatim.

### 🔴 The one NEW gap this staging found: the D–H τ-range at p.209

HB uses Deuring–Heilbronn (Jutila [11, Theorem 2]) at **two sites with different τ-demands**:

| site | statement | ρ-range demanded |
|---|---|---|
| p.206 (Lemma 3) | `r₀ = min{\|1−ρ\| : ρ ≠ β₀} ≫ L^{−1} log η` | `\|γ\| ≤ 1` |
| **p.209 (Lemma 7)** | `σ₀ = max_{\|ρ\| ≤ q², ρ ≠ β₀} β ≤ 1 − A L^{−1} log η` | **`\|ρ\| ≤ q²`** |

Our landed `dh_repulsion_ordered` (TBalR8.lean:1752) carries the hypothesis `|Im ρ| ≤ 1`. It
therefore serves the **first** site and **not the second**. The recorded consumer chain
(`pass3_t4.md:38–50`, restated by JUTILA-STAGE as "L3-ii is the sole direct consumer; L2 multiplies
the rate; L7") reads the p.209 use as downstream of Lemma 3 — but at the bytes it is an
**independent invocation** of the same Jutila theorem, with a different conclusion shape (a
zero-free strip for all non-exceptional zeros in a disc of radius `q²`, not a repulsion radius
around `s = 1`). Jutila's Theorem 2 *is* τ-uniform, so nothing is mathematically missing; the gap
is on our side of the interface, and it belongs to **N0's audit and N4's dependency list**, not to
N3. Cheapest resolutions, in order: (a) widen the contract's τ-hypothesis; (b) re-derive p.209's
`σ₀` bound from the `|γ| ≤ 1` contract plus the classical zero-free region for `|γ| > 1` (the
region (1.10) already gives `β ≤ 1 − C⁽⁰⁾/log(q(|t|+2))`, which for `1 < |γ| ≤ q²` is
`≤ 1 − A L^{−1}` — **weaker than `1 − AL^{−1}log η`, so this does not close it by itself**);
(c) restrict the explicit-formula truncation so that only `|γ| ≤ 1` zeros survive, which would
change (4.8)–(4.10). ⟦Not adjudicated here — HB-STAGE is a scribe. Flagged for N0.⟧

### Cross-source reconciliation with `docs/sources/jutila1977-notes.md` (staged same day)

- **Density.** HB quotes `N(σ,T,χ) ≪ (qT)^{(5/2)(1−σ)}` for `4/5 ≤ σ ≤ 1` (4.9). JUTILA-STAGE
  records Jutila's Theorem 1 as `(qT)^{(2+ε)(1−α)}`, `4/5 ≤ α ≤ 1`. **These agree**: HB has simply
  fixed `ε = 1/2`. Our node-N2 tolerance (`D ≤ 83`) is far coarser than either.
- **Repulsion.** HB's `[11, Theorem 2]` is Jutila's (1.10). Both of HB's uses need only
  **log η-order** repulsion — confirming, at the source, the pass-3 ruling that the log shape is
  what D–H methods give.
- **Staging status of this road.** Jutila [11] is now staged (`docs/sources/jutila1977-notes.md`,
  2026-08-03). **`Iwaniec, "Rosser's sieve", Acta Arith. 36 (1980) 171–202` remains the one
  unstaged source** on the fulcrum road — and it is precisely N5's source (§3 = the λ_d
  construction and the S-set with its `σ_d`; Theorem 4 = the fundamental lemma; the `β ≥ 3`
  sieving-limit fact for dimension 4). Everything N5 needs from it is quoted in §2 above, but the
  *proofs* behind those quotations are not.
