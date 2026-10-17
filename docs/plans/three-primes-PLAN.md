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

**Why Λ and not the primes themselves.** Three reasons, and one price. The tools speak Λ: Siegel–Walfisz
is a statement about ψ(x; q, a) = Σ_{n ≤ x, n ≡ a} Λ(n). The minor-arc method needs Λ = μ ∗ log to be a
Dirichlet convolution, because that is what lets Vaughan's identity split it into bilinear pieces.
Counting primes with weight 1 has no such identity. The price is Step 0: converting back to primes
costs a factor (log N)³ and a prime-power error of size N^{3/2}, both far below N².

**Why three primes and not two.** The same method fails for N = p₁ + p₂, and Step 7 is where. With
three copies of S, one copy is bounded pointwise and the other two by Parseval, ∫|S|² ≈ N log N. With
two copies there is no spare copy to take the supremum of. The minor-arc integral of |S|² can only be
bounded by ≈ N log N, which is larger than the main term ≈ N. (The method does show that almost every
even number is a sum of two primes, but that is a different argument.)

## 2. The skeleton

Fix N odd and large, and a parameter P = (log N)^B, with B chosen at the end, in Step 7. With the
textbook minor-arc bound, which carries (log N)⁴, B = 2A + 10 gives an error of N²(log N)^{−A}. The
corpus's own bound carries a different power of log, and B is re-derived from it (§4, L19).

**Step 0. From primes to Λ, and back.** Let r(N) = #{(p₁,p₂,p₃) : p₁+p₂+p₃ = N}. Then

  R(N) ≤ (log N)³ r(N) + O(N^{3/2} (log N)²),

because of the proper prime powers p^k ≤ N (k ≥ 2). There are O(N^{1/2}) of them, with total Λ-weight
O(N^{1/2}). For fixed n₁, the other two slots weigh Σ_{n₂+n₃ = N−n₁} Λ(n₂)Λ(n₃) ≤ N (log N)². So each
slot holding a prime power contributes O(N^{3/2} (log N)²), well inside the stated error.
*Role: the reduction. It says a lower bound R(N) ≫ N² proves the theorem.*

**Step 1. The integral identity.** R(N) = ∫₀¹ S(α)³ e(−Nα) dα.
*Role: turns counting into analysis. It is orthogonality, ∫₀¹ e(mα) dα = [m = 0], applied to a
finite sum.*

**Step 2. The dissection.** Work on the circle ℝ/ℤ, so the arc around 0 = 1 is one interval that
wraps around. For q ≤ P, 0 ≤ a < q and (a, q) = 1 (so a = 0 only when q = 1), the major arc is
𝔐(q, a) = {α : ‖α − a/q‖ ≤ P/N}. 𝔐 is their union and the minor arcs are 𝔪 = (ℝ/ℤ) \ 𝔐.
**The arcs are disjoint once N > 2P³.** Two distinct fractions a/q ≠ a′/q′ with q, q′ ≤ P satisfy
‖a/q − a′/q′‖ ≥ 1/(qq′) ≥ 1/P², which exceeds 2P/N. This matters because Step 4 computes ∫_𝔐 one arc
at a time, using that arc's own approximation from Step 3. An overlap would count the overlapping
piece twice, with two different approximations.
**Why P is a power of log N and not a power of N.** Step 3 needs primes in progressions mod q,
pointwise and uniformly in q. Siegel–Walfisz gives that only for q up to a power of log N. For q up
to N^δ it is not known: it would follow from the generalised Riemann hypothesis. So P is as large as
Siegel–Walfisz allows.
*Role: defines the two regimes. A larger P makes the minor-arc bound N P^{−1/2} of Step 6 stronger.
Siegel–Walfisz caps P at a power of log N, and Step 7 then fixes the power B.*

**Step 3. Major arcs: S near a/q.** For α = a/q + β ∈ 𝔐(q, a),

  S(α) = (μ(q)/φ(q)) · v(β) + O(N (log N)^{−C})  for every fixed C,  where v(β) = Σ_{n ≤ N} e(nβ).

The proof has three moves.
 (3a) Split n ≤ N by its residue r mod q. Terms with (r, q) > 1 are prime powers of primes dividing
 q, and contribute O((log N)²).
 (3b) For (r, q) = 1, Siegel–Walfisz gives ψ(t; q, r) = t/φ(q) + O(t (log t)^{−D}) for every D,
 uniformly for q ≤ (log t)^{C′}. (This is the form the corpus proves. The classical saving
 exp(−c√log t) is stronger and not needed.) Summing e(ar/q) over the reduced residues gives the
 Ramanujan sum c_q(a) = μ(q).
 **The uniformity is in t, not N, and Abel summation needs every t ≤ N.** Split at t = N^{1/2}. For
 t ≤ N^{1/2}, bound trivially: the contribution is O(N^{1/2} log N). For t > N^{1/2}, log t ≥ ½ log N,
 so q ≤ P = (log N)^B ≤ (log t)^{2B} once N is large, and Siegel–Walfisz with C′ = 2B applies.
 (3c) Abel summation moves the twist e(nβ) onto the smooth main term. Its cost is the twist's total
 variation, 2π|β|N ≤ 2πP, plus 1. Summed over the φ(q) ≤ P classes, the error is
 O(P² · N (log N)^{−D}). (Abel summation produces (1/φ(q))∫₀^N e(tβ) dt rather than v(β)/φ(q); the
 swap costs O(1 + P) per class and is absorbed.) Since D is ours to choose, take D = C + 2B, which leaves O(N (log N)^{−C}).
 That is why the error may grow with |β|N: Siegel–Walfisz saves every power of log N, so any
 polynomial in P is paid for. It is also why it may grow only polynomially in P.
*Role: the only place primes in arithmetic progressions are used, and the only source of
ineffectivity.*

**Step 4. Major arcs: the integral.** Cube, integrate over 𝔐, and complete the sums:

  ∫_𝔐 S(α)³ e(−Nα) dα = 𝔖(N, P) · J(N, P) + O(N² (log N)^{−A}),

where 𝔖(N, P) = Σ_{q ≤ P} (μ(q)/φ(q)³) c_q(N), and J(N, P) = ∫_{|β| ≤ P/N} v(β)³ e(−Nβ) dβ.
Two pieces of bookkeeping. **The error:** on 𝔐(q, a) write S = M + E, with M = (μ(q)/φ(q)) v(β) and
|E| ≤ E₀ = O(N (log N)^{−C}). Since |S| ≤ ψ(N) ≪ N and |M| ≤ N, |S³ − M³| ≪ E₀ N². The total measure
of 𝔐 is at most P² · 2P/N, so the error integrates to O(N² P³ (log N)^{−C}) = O(N² (log N)^{−A}) with
C = A + 3B. **The main term:** integrating M³ e(−Nα) over 𝔐(q, a) gives
(μ(q)/φ(q))³ e(−Na/q) · ∫_{|β| ≤ P/N} v(β)³ e(−Nβ) dβ. Since μ(q)³ = μ(q), and
Σ_{(a,q)=1} e(−Na/q) = c_q(N) (the Ramanujan sum, which is real and even in N), summing over a and q
gives 𝔖(N, P) J(N, P).
Completing both:
 (4a) J(N) = ∫₀¹ v(β)³ e(−Nβ) dβ = #{(n₁,n₂,n₃) ≥ 1 : n₁+n₂+n₃ = N} = (N−1)(N−2)/2. The tail
 |β| > P/N costs O(N²/P²), because |v(β)| ≤ 1/(2‖β‖).
 (4b) 𝔖(N) − 𝔖(N, P) = O(P^{−1+ε}), from the trivial |c_q(N)| ≤ φ(q) and
 Σ_{q > P} μ²(q)/φ(q)² ≪ P^{−1+ε}. Times J(N) ≤ N², this costs O(N² P^{−1+ε}), and
 |𝔖(N, P)| = O(1) times (4a)'s tail costs O(N²/P²). Both are O(N² (log N)^{−A}) for B as in Step 7.
*Role: the main term, N²/2 times the arithmetic density 𝔖(N).*

**Step 5. The singular series is positive for odd N.** The series converges absolutely, since its
terms are bounded by μ²(q)/φ(q)², and Σ_q μ²(q)/φ(q)² < ∞ (the same bound as 4b). Its terms
c_q(N) · μ(q)/φ(q)³ are multiplicative in q and vanish unless q is squarefree. So it is an Euler
product with one factor 1 + μ(p) c_p(N)/φ(p)³ per prime, where c_p(N) = p − 1 if p | N and −1
otherwise:

  𝔖(N) = Π_{p | N} (1 − 1/(p−1)²) · Π_{p ∤ N} (1 + 1/(p−1)³).

At p = 2 the first kind of factor is 0, so 𝔖(N) = 0 for even N. That is the parity obstruction:
three odd primes have an odd sum. For odd N the p = 2 factor is 2. Every factor with p ≥ 3 lies in
[3/4, 9/8], and Π_{p ≥ 3}(1 − 1/(p−1)²) converges, so 𝔖(N) ≥ c₀ > 0 with c₀ independent of N.
For even N the conclusion is right, not merely an artefact: three primes summing to an even N must
include 2 (once, or three times if N = 6), so r(N) ≤ 3·#{(p, p′) : p + p′ = N − 2} + 1
≪ N log log N/(log N)², by the upper-bound sieve. That is far below the N²/(log N)³ the theorem asserts
for odd N.
*Role: the only place oddness is used.*

**Step 6. Minor arcs: Vinogradov's estimate.** For every α ∈ 𝔪,

  |S(α)| ≪ N (log N)⁴ P^{−1/2}.

 (6a) Dirichlet: some a/q in lowest terms with q ≤ N/P and |α − a/q| ≤ P/(qN). If q ≤ P then α ∈ 𝔐,
 so on 𝔪 we have P < q ≤ N/P. Since q ≤ N/P, also |α − a/q| ≤ P/(qN) ≤ 1/q². This is the hypothesis
 every bound below needs.
 (6b) Vaughan's identity, with U = V = N^{2/5}, writes S(α) as four pieces.
  · the terms n ≤ V, trivially O(V);
  · **type I**, Σ_{d ≤ U} μ(d) Σ_{m ≤ N/d} (log m) e(dmα). The weight log m is removed by partial
    summation, at a cost of log N;
  · **type I**, Σ_{t ≤ UV} c_t Σ_{r ≤ N/t} e(trα), with c_t = Σ_{dm = t, d ≤ U, m ≤ V} μ(d) Λ(m), so
    |c_t| ≤ log t. The range t ≤ UV = N^{4/5} is where the N^{4/5} below comes from;
  · **type II**, Σ_{U < m ≤ N/V} a_m Σ_{V < k ≤ N/m} Λ(k) e(mkα), with a_m = Σ_{d | m, d ≤ U} μ(d).
    Here |a_m| ≤ τ(m), the divisor function, **not** a power of log, and the two variables are
    coupled by mk ≤ N.
 (6c) Type I: each inner sum is geometric, bounded by min(N/m, 1/(2‖mα‖)) (L9). The **reciprocal-sum
 lemma** Σ_{m ≤ M} min(X/m, 1/‖mα‖) ≪ (X/q + M + q) log(2qX), valid when |α − a/q| ≤ 1/q², finishes it.
 (6d) Type II: split m into dyadic blocks m ~ M. Apply Cauchy–Schwarz in m, using Σ_{m ~ M} τ(m)² ≪
 M (log M)³. Expanding the square gives
 Σ_{k, k′} Λ(k)Λ(k′) Σ_m e(m(k − k′)α), where m runs over an interval because of the coupling, so the
 inner sum is still geometric. That leaves a **variant** of the lemma, with a constant first argument:
 Σ_{h ≤ H} min(X, 1/‖hα‖) ≪ (H/q + 1)(X + q log q).
 (6e) Together: S(α) ≪ (N q^{−1/2} + N^{4/5} + N^{1/2} q^{1/2}) (log N)⁴. Insert P < q ≤ N/P.
 **Where the four logs come from**, all in the type II piece and all under the Cauchy–Schwarz square
 root: τ² contributes (log)^{3/2}; Λ(k)Λ(k′) ≤ (log N)² contributes 1; the variant lemma's q log q
 contributes ½; and the dyadic split into ≈ log N blocks contributes 1. The corpus's bound (`vinoBd`)
 does its own accounting, and that is the power B is set from.

**The idea of Step 6, which the moves above implement.** Why should S(α) be small when α is far
from every fraction with a small denominator? Because the primes have no structure that correlates
with e(nα) there, but that has to be made quantitative, and Λ alone gives no handle. Vaughan's
identity supplies one: it rewrites the sum as bilinear forms Σ_m Σ_k a_m b_k e(mkα), with nothing
known about the type II coefficients except their size. A bilinear form whose two ranges are both
long cannot correlate with e(mkα) when α is near no fraction of small denominator. That is the
heuristic; the lemmas make it quantitative. After Cauchy–Schwarz in m, what remains is Σ_m e(m(k − k′)α) for
each pair k, k′: a geometric series, small unless (k − k′)α is close to an integer. When α is close
to a/q with q large, in each run of q consecutive differences h = k − k′ about one has hα within
1/q of an integer and contributes the full X; the rest contribute about q log q in all (the harmonic
tail). Hence (H/q + 1)(X + q log q), and that is the saving. The square root from Cauchy–Schwarz halves it, which is why
the bound gains q^{−1/2} and not q^{−1}. The type I pieces are easier: one variable is smooth, the
inner sum is geometric at once, and its leading term saves the full 1/q. The other two terms mark the
method's edges. N^{4/5} is where the type I range UV meets the type II losses N/√U and N/√V; U = V =
N^{2/5} balances them. N^{1/2}q^{1/2} comes from the q log q tail of the lemmas. It dominates N q^{−1/2}
once q > N^{1/2}, when the denominator is too large for the "one in q" count to save anything, and the
restriction q ≤ N/P is what keeps it ≤ N P^{−1/2}.
*Role: the heart of the proof. It is the one estimate that is not "primes in progressions". It holds
equally for two primes. What fails there is Step 7, not this.*

**Step 7. Minor arcs: the integral.**

  |∫_𝔪 S(α)³ e(−Nα) dα| ≤ sup_𝔪 |S| · ∫₀¹ |S(α)|² dα = sup_𝔪 |S| · Σ_{n ≤ N} Λ(n)²
                        ≪ N (log N)⁴ P^{−1/2} · N log N.

With P = (log N)^B and B ≥ 2A + 10, this is O(N² (log N)^{−A}). In general, if the minor-arc bound
carries (log N)^c, the condition is B ≥ 2A + 2c + 2. With the textbook c = 4 that is 2A + 10.
*Role: Parseval turns a pointwise bound into an integral bound, at the cost of one factor log N.
This is why the minor-arc saving must beat a power of log N, not merely be o(N). It is also the step
with no two-prime version: it needs a third copy of S to take the supremum of (§1).*

**Step 8. Assembly.** R(N) = 𝔖(N) N²/2 + O(N² (log N)^{−A}) ≥ (c₀/3) N² for N large and odd.
Step 0 gives r(N) ≥ (c₀/4) N² (log N)^{−3} > 0.

## 3. The lemma list, with role lines

Each line is one lemma the proof states, in the order a reader meets it. **New** means our corpus
must supply it (see §4 for what already exists).

| # | lemma | role |
|---|---|---|
| L1 | orthogonality ∫₀¹ e(mα) dα = [m = 0] | counting becomes integration (Step 1) |
| L2 | R(N) = ∫ S³ e(−N·) | the identity the whole proof evaluates (Step 1) |
| L3 | prime powers contribute O(N^{3/2} (log N)²) per slot | Λ-weights ⇒ primes (Step 0) |
| L4 | major arcs are disjoint once N > 2P³ | each arc is computed with its own approximation (Step 2) |
| L5 | Ramanujan sum: c_q(a) = μ(q) when (a, q) = 1; c_q(N) = Σ_{(a,q)=1} e(−Na/q) is real and multiplicative in q; \|c_q(N)\| ≤ φ(q); c_p(N) = p − 1 or −1 | the arithmetic of the major arc (Steps 3b, 4, 4b, 5) |
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
| L16 | reciprocal-sum lemma Σ min(X/m, 1/‖mα‖), and its variant Σ min(X, 1/‖hα‖), under \|α − a/q\| ≤ 1/q² | the engine of type I (6c) and, in the variant, type II (6d) |
| L17 | type I bound | (Step 6c) |
| L18 | type II bound, with Σ τ(m)² ≪ M log³ M | (Step 6d) |
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
| L5 Ramanujan sums | **absent** | (only c_{p^e}(a) = 0, e ≥ 2, inside `Salt/Weil/GcdBranch.lean`) | new: c_q(a) = μ(q) for (a, q) = 1; multiplicativity; the trivial \|c_q(N)\| ≤ φ(q), which is the only bound 4b uses |
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
