# Three primes: the proof plan (O82 target B)

**Theorem (Vinogradov, 1937).** There is an N₀ such that every odd integer N > N₀ is a sum of
three primes.

This document is the plan for a proof written for a mathematician to read and learn from. The Lean
is its check; the explanation is the artifact. It is written prose-first. Lean names appear only in
§5, and no Lean is written until a non-author reader has worked through this plan (O83 item 3).

**Scope.** "Sufficiently large", with N₀ **ineffective**: the major arcs rest on the Siegel–Walfisz
theorem, whose constant comes from Siegel's theorem and cannot be computed. Nothing here touches
Helfgott's N₀ = 10²⁷ or the full ternary Goldbach conjecture; that is a different, much larger
project (explicit estimates at every step) and is out of scope.

---

## 1. The idea in one paragraph

Count representations with weights. Let Λ be the von Mangoldt function and set

  R(N) = Σ_{n₁+n₂+n₃ = N} Λ(n₁) Λ(n₂) Λ(n₃).

If R(N) is larger than what prime powers (p², p³, …) can contribute, some representation uses three
primes. The circle method writes R(N) as an integral over the circle,

  R(N) = ∫₀¹ S(α)³ e(−Nα) dα,  where S(α) = Σ_{n ≤ N} Λ(n) e(nα) and e(x) = exp(2πix),

and splits the circle in two. Near a rational a/q with small q (a **major arc**), the primes'
distribution in residue classes mod q makes S(α) look like a simple explicit function, and the
integral there gives the main term 𝔖(N)·N²/2. Everywhere else (the **minor arcs**), S(α) is small,
smaller than N by a power of log N. This is Vinogradov's estimate and the heart of the proof. Since
∫|S|² is only about N log N, the minor arcs contribute less than the main term. The **singular
series** 𝔖(N) is a product over primes p, one factor per prime. It is bounded below by a positive
constant exactly when N is odd. That is where oddness enters, and the only place it enters.

## 2. The skeleton

Fix N odd and large, and a parameter P = (log N)^B, with B chosen at the end (B = 2A + 10 suffices
for an error of N²(log N)^{−A}).

**Step 0. From primes to Λ, and back.** Let r(N) = #{(p₁,p₂,p₃) : p₁+p₂+p₃ = N}. Then

  R(N) ≤ (log N)³ r(N) + O(N^{3/2} (log N)³),

because the terms where some nᵢ is a proper prime power number O(N^{1/2} log N) per slot.
*Role: the reduction. It says a lower bound R(N) ≫ N² proves the theorem.*

**Step 1. The integral identity.** R(N) = ∫₀¹ S(α)³ e(−Nα) dα.
*Role: turns counting into analysis. It is orthogonality, ∫₀¹ e(mα) dα = [m = 0], applied to a
finite sum.*

**Step 2. The dissection.** For q ≤ P and (a, q) = 1, the major arc is
𝔐(q, a) = {α : |α − a/q| ≤ P/N}. These are disjoint for N large, and 𝔐 is their union. The minor
arcs are 𝔪 = [0,1) \ 𝔐.
*Role: defines the two regimes. P controls the trade-off: a larger P means a weaker minor-arc
bound is enough, but the major-arc error is harder to control.*

**Step 3. Major arcs: S near a/q.** For α = a/q + β ∈ 𝔐(q, a),

  S(α) = (μ(q)/φ(q)) · v(β) + O(N exp(−c√log N)),  where v(β) = Σ_{n ≤ N} e(nβ).

The proof has three moves.
 (3a) Split n ≤ N by its residue r mod q. Terms with (r, q) > 1 are prime powers of primes dividing
 q, and contribute O((log N)²).
 (3b) For (r, q) = 1, Siegel–Walfisz gives ψ(x; q, r) = x/φ(q) + O(x exp(−c√log x)) uniformly for
 q ≤ P. Summing e(ar/q) over the reduced residues gives the Ramanujan sum c_q(a) = μ(q).
 (3c) Abel summation moves the twist e(nβ) onto the smooth main term. The error picks up a factor
 1 + |β|N ≤ 1 + P, which the exp(−c√log N) absorbs.
*Role: the only place primes in arithmetic progressions are used, and the only source of
ineffectivity.*

**Step 4. Major arcs: the integral.** Cube, integrate over 𝔐, and complete the sums:

  ∫_𝔐 S(α)³ e(−Nα) dα = 𝔖(N, P) · J(N, P) + O(N² (log N)^{−A}),

where 𝔖(N, P) = Σ_{q ≤ P} (μ(q)/φ(q)³) c_q(N), and J(N, P) = ∫_{|β| ≤ P/N} v(β)³ e(−Nβ) dβ.
Completing both:
 (4a) J(N) = ∫₀¹ v(β)³ e(−Nβ) dβ = #{(n₁,n₂,n₃) ≥ 1 : n₁+n₂+n₃ = N} = (N−1)(N−2)/2. The tail
 |β| > P/N costs O(N²/P²), because |v(β)| ≤ 1/(2‖β‖).
 (4b) 𝔖(N) − 𝔖(N, P) = O(P^{−1+ε}), from |c_q(N)| ≤ φ(q) and Σ_{q > P} μ²(q)/φ(q)² ≪ P^{−1+ε}.
*Role: the main term, N²/2 times the arithmetic density 𝔖(N).*

**Step 5. The singular series is positive for odd N.** c_q(N) and μ(q)/φ(q)³ are multiplicative in
q, so

  𝔖(N) = Π_{p | N} (1 − 1/(p−1)²) · Π_{p ∤ N} (1 + 1/(p−1)³).

At p = 2 the first kind of factor is 0, so 𝔖(N) = 0 for even N. That is the parity obstruction:
three odd primes have an odd sum. For odd N the p = 2 factor is 2. Every factor with p ≥ 3 lies in
[3/4, 9/8], and Π_{p ≥ 3}(1 − 1/(p−1)²) converges, so 𝔖(N) ≥ c₀ > 0 with c₀ independent of N.
*Role: the only place oddness is used.*

**Step 6. Minor arcs: Vinogradov's estimate.** For every α ∈ 𝔪,

  |S(α)| ≪ N (log N)⁴ P^{−1/2}.

 (6a) Dirichlet: some a/q with q ≤ N/P and |α − a/q| ≤ P/(qN). If q ≤ P then α ∈ 𝔐, so on 𝔪 we
 have P < q ≤ N/P.
 (6b) Vaughan's identity, with U = V = N^{2/5}, writes Λ(n) for n > U as a type I sum (the shape
 Σ_{m ≤ M} a_m Σ_{n ≤ N/m} e(mnα), with |a_m| ≤ log N), plus a type II sum (Σ_{m ~ M} Σ_n a_m b_n
 e(mnα), with M, N/M both ≥ N^{2/5}).
 (6c) Type I: the inner sum is geometric, bounded by min(N/m, 1/(2‖mα‖)). The **reciprocal-sum
 lemma** Σ_{m ≤ M} min(N/m, 1/‖mα‖) ≪ (N/q + M + q) log(2qM) finishes it.
 (6d) Type II: Cauchy–Schwarz in m, expand the square, and apply the same lemma to the resulting
 type I shape in the difference n − n′.
 (6e) Together: S(α) ≪ (N q^{−1/2} + N^{4/5} + N^{1/2} q^{1/2}) (log N)⁴. Insert P < q ≤ N/P.
*Role: the heart of the proof. It is the one estimate that is not "primes in progressions", and
the one with no analogue for two primes.*

**Step 7. Minor arcs: the integral.**

  |∫_𝔪 S(α)³ e(−Nα) dα| ≤ sup_𝔪 |S| · ∫₀¹ |S(α)|² dα = sup_𝔪 |S| · Σ_{n ≤ N} Λ(n)²
                        ≪ N (log N)⁴ P^{−1/2} · N log N.

With P = (log N)^B and B ≥ 2A + 10, this is O(N² (log N)^{−A}).
*Role: Parseval turns a pointwise bound into an integral bound, at the cost of one factor log N.
This is why the minor-arc saving must beat a power of log N, not merely be o(N).*

**Step 8. Assembly.** R(N) = 𝔖(N) N²/2 + O(N² (log N)^{−A}) ≥ (c₀/3) N² for N large and odd.
Step 0 gives r(N) ≥ (c₀/4) N² (log N)^{−3} > 0.

## 3. The lemma list, with role lines

Each line is one lemma the proof states, in the order a reader meets it. **New** means our corpus
must supply it (see §4 for what already exists).

| # | lemma | role |
|---|---|---|
| L1 | orthogonality ∫₀¹ e(mα) dα = [m = 0] | counting becomes integration (Step 1) |
| L2 | R(N) = ∫ S³ e(−N·) | the identity the whole proof evaluates (Step 1) |
| L3 | prime powers contribute O(N^{1/2} log N) per slot | Λ-weights ⇒ primes (Step 0) |
| L4 | major arcs are disjoint for N > N₁(B) | the dissection is a partition (Step 2) |
| L5 | Ramanujan sum: c_q(a) = μ(q) when (a, q) = 1; c_q multiplicative; \|c_q(N)\| ≤ (q, N) | the arithmetic of the major arc (Step 3b, Step 5) |
| L6 | Siegel–Walfisz for ψ(x; q, r), q ≤ (log x)^B | primes in progressions; source of N₀'s ineffectivity (Step 3b) |
| L7 | Abel summation with a twist e(nβ) | moves β onto the smooth term (Step 3c) |
| L8 | S(a/q + β) = (μ(q)/φ(q)) v(β) + error | the major-arc approximation (Step 3) |
| L9 | \|v(β)\| ≤ min(N, 1/(2‖β‖)) | geometric sums, used in Steps 4a and 6c |
| L10 | J(N) = (N−1)(N−2)/2, and the truncation error | the singular integral (Step 4a) |
| L11 | 𝔖(N) converges absolutely; the tail bound | completing the series (Step 4b) |
| L12 | Euler product for 𝔖(N) | multiplicativity (Step 5) |
| L13 | 𝔖(N) ≥ c₀ > 0 for odd N; 𝔖(N) = 0 for even N | oddness (Step 5) |
| L14 | Dirichlet approximation | locates α on the minor arc (Step 6a) |
| L15 | Vaughan's identity | splits Λ into bilinear pieces (Step 6b) |
| L16 | reciprocal-sum lemma Σ min(X/m, 1/‖mα‖) | the engine of both type I and type II (Steps 6c, 6d) |
| L17 | type I bound | (Step 6c) |
| L18 | type II bound | (Step 6d) |
| L19 | Vinogradov's minor-arc estimate | the heart (Step 6) |
| L20 | Parseval: ∫\|S\|² = Σ Λ(n)², and Σ_{n ≤ N} Λ(n)² ≪ N log N | pointwise ⇒ integral (Step 7) |
| L21 | the asymptotic for R(N), and the theorem | assembly (Step 8) |

## 4. What the corpus already has

Every entry below was read at its statement (inventory 2026-10-16, re-checked at the object for
the starred rows). **About half of the skeleton is already proved, and it is the half most people
would call hard.** The minor arcs are essentially done. The major arcs are not started.

| lemma | status | where | note |
|---|---|---|---|
| L1 orthogonality | **have** ★ | `Salt.LS.integral_e_int`, `Salt/LS/Parseval.lean:30` | ∫₀¹ e(kα) dα = [k = 0] for k : ℤ |
| L20 Parseval | **have** ★ | `Salt.LS.parseval`, `Salt/LS/Parseval.lean:76` | over `range N` with `e`; S is over `Icc 1 x` with `eR`. **No bridge lemma exists**: a small seam to close first |
| L20 Σ Λ² ≪ N log N | **have** ★ | `Salt.LS.sum_vonMangoldt_sq_le`, `Salt/LS/BDHPrep.lean:70` | ≤ (log 4 + 4) x log x |
| L6 Siegel–Walfisz | **have** ★ | `Salt.SW.siegelWalfisz_holds : Salt.BV.SiegelWalfisz`, `Salt/SW/Gate.lean:150` | Λ-weighted ψ(x; q, a), q ≤ (log x)^C, any A; ineffective. (The docstring at `Salt/BV/Defs.lean:31` still says "assumed": stale) |
| L7 Abel summation | **have** | `Salt.MR.sum_Ioc_abel`, `Salt/MR/MinorArcCore.lean:177`; mathlib `sum_mul_eq_sub_sub_integral_mul` | discrete and continuous |
| L9 geometric sum | **have** | `Salt.MR.geom_phase_bound`, `Salt/MR/MinorArcVaughan.lean:298` | ≤ min(M, 1/(2‖θ‖)) |
| L14 Dirichlet | **have** ★ | `Salt.MR.exists_dirichlet_approx`, `Salt/MR/BigXiArc.lean:229`; `approx_reduced`, `approx_c_form` (`Salt/MR/MinorArcExit.lean:333`, `:387`) | to lowest terms, then to the \|α − a/q\| ≤ c/q² shape the bound consumes |
| L15 Vaughan | **have** ★ | `Salt.LS.vaughan`, `Salt/LS/Vaughan.lean:91`; `Salt.MR.vaughan_expSum` | exact identity, and its exponential-sum form |
| L16–L18 type I/II | **have** | `typeI_bound`, `typeII_block_bound`, `typeII_dyadic_bound` (`Salt/MR/MinorArcCore.lean`) | explicit constants |
| L19 Vinogradov | **have**, in a different shape ★ | `Salt.MR.lambdaPhase_le` → `vinoBd`, `Salt/MR/MinorArcExit.lean:706`, `:661` | U = V = W with W² ≤ x, a dyadic count K. It must be **specialised** to N P^{−1/2}(log N)^c on P < q ≤ N/P. The log power c comes out of `vinoBd`, not the textbook's 4, and B is re-derived from it |
| L5 Ramanujan sums | **absent** | (only c_{p^e}(a) = 0, e ≥ 2, inside `Salt/Weil/GcdBranch.lean`) | new: c_q(a) = μ(q) for (a, q) = 1; multiplicativity; \|c_q(N)\| ≤ (q, N) |
| L8 major-arc approximation | **absent** | — | **the single biggest piece**: residue split, SW per class, Ramanujan sum, Abel summation in β |
| L10 singular integral | **absent** | — | elementary: a count, plus the tail from L9 |
| L11–L13 𝔖(N) | **absent** | — | the corpus's 𝔖 is the twin/binary one (`twinSingularSeries`); new: convergence, Euler product, positivity for odd N |
| L2, L3, L4, L21 | **absent** | — | the identity, the prime-power removal, the disjointness, the assembly |

Nothing in the corpus states a three-primes or ternary theorem (searched: `three_primes`,
`threePrimes`, "sum of three primes", `goldbach_ternary`, "weak Goldbach", "odd Goldbach",
`major_arc`, `singularIntegral`, all 0; controls: "Vaughan" in 55 files, `𝔖` 85 hits). The
`Salt/Goldbach/` tree is **Chen's binary theorem** (`Salt.Goldbach.chen_goldbach`,
`Salt/Goldbach/ChenGoldbach.lean:41`: every large even N is p + P₂), a sieve, and contributes nothing
here except shared tools.

**The work, by size.** Major arcs L5 + L8: the largest. Singular series L11–L13: moderate and
self-contained, the most pleasant to explain. Minor-arc specialisation L19: small, but it fixes B.
Glue L2–L4, L10, L20 seam, L21: small.

## 5. Lean shape (only after the non-author read)

A sketch, not acted on before O83 item 3. One directory, `Salt/ThreePrimes/`, one module per step of
§2, in reading order: `Count` (L1–L3), `Arcs` (L4), `Ramanujan` (L5), `MajorArc` (L7–L8),
`SingularIntegral` (L9–L10), `SingularSeries` (L11–L13), `MinorArc` (L14–L19 specialised), `Assembly`
(L20–L21). Each module opens with the §2 paragraph it proves, and each lemma's docstring is its
role line from §3, **written before its proof** (O83 item 4). The final theorem carries no hypotheses:
`∃ N₀, ∀ N > N₀, Odd N → ∃ p₁ p₂ p₃, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N`.

## 6. Design choices made for the reader

- **Λ-weights, sharp cutoff n ≤ N.** A smooth weight would shorten Steps 4a and 7 and lengthen the
  explanation of why it is allowed. The sharp cutoff makes J(N) a count a reader can verify by hand.
- **Vaughan, not Heath-Brown.** The classical type I/type II split has one parameter pair and reads
  as one idea. Heath-Brown's identity buys flexibility that three primes does not need.
- **Siegel–Walfisz as a black box with its scope stated.** It is the one imported deep result. Its
  ineffectivity is named at the theorem, not discovered by the reader in a footnote.
- **One parameter P = (log N)^B** threaded through every step, chosen once at the end, so a reader
  can see what each step costs in powers of log N.

## Sources

Davenport, *Multiplicative Number Theory*, chapters 24–26 (the skeleton and Vaughan's form of
Step 6). Vaughan, *The Hardy–Littlewood Method*, chapter 3. Iwaniec–Kowalski, *Analytic Number
Theory*, §13.4 and chapter 19.
