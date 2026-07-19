# FULCRUM AUDIT — SOURCE MAP: Heath-Brown 1983, "Prime Twins and Siegel Zeros"

Source: Proc. London Math. Soc. (3) 47 (1983) 193–224. Staged PDF (32 pp) read in full.
All references below are GROUNDED to journal page / equation numbers unless marked MEMORY.
Audit question: walk "infinitely many Siegel zeros ⟹ infinitely many twin primes" and
record, per link, EXACTLY what the Siegel-zero hypothesis feeds it (quality / quantity /
range / effectivity), consumed vs convenient.

---

## 0. The hypothesis, exactly (his (1.11)-grade condition)

GROUNDED p.194, (1.10)–(1.11):

- Classical effective zero-free region (1.10): L(σ+it,χ) ≠ 0 for σ ≥ 1 − C⁽⁰⁾/log(q(|t|+2)),
  C⁽⁰⁾ effectively computable, except possibly one real zero of a real χ. Those exceptions
  are the Siegel zeros.
- HYPOTHESIS (1.11): L(β₀,χ) = 0 for a REAL PRIMITIVE character χ (mod q) and a REAL β₀ with
      1 − β₀ ≤ (3 log q)⁻¹.
- Definitions: η := {(1−β₀) log q}⁻¹ (so η ≥ 3); L := log q. Effective upper bound η ≪ q
  (Davenport Ch.14 (14)), "used from time to time" — its one load-bearing use: z₀ ≤ A log log η
  ≤ L^{1/3} automatically (p.198).

Quality parameter of the whole paper = η. Quantity parameter = number of triples (q,χ,β₀).

## 1. Top-level results and their demands

- THEOREM 1 (p.195, (1.12)–(1.13)): Σ_{x<n≤2x} Λ(l₁(n))Λ(l₂(n)) = 𝔖C(α)x + O(x(log log η)⁻¹),
  uniformly for q²⁵⁰ ≤ x ≤ q⁵⁰⁰. ONE triple consumed; quality only through (log log η)⁻¹;
  implied constant EFFECTIVE, depends on α_i, β_i only.
- COROLLARY 1 (p.195; proof p.223): prime-pair count 𝔖C(α)x(log x)⁻² {1+O((log log η)⁻¹)},
  uniformly q³⁰⁰ ≤ x ≤ q⁵⁰⁰. Window shrinks 250→300 to absorb the dyadic tail O(q²⁵⁰).
- COROLLARY 2 (p.195; proof p.223): THE FULCRUM LINK. If η ≥ C⁽¹⁾ for INFINITELY MANY triples
  (q,χ,β₀), then infinitely many n with l₁(n), l₂(n) simultaneously prime.
  C⁽¹⁾ = exp exp{2A(𝔖C(α))⁻¹}, A = effective Cor 1 constant ⟹ C⁽¹⁾ EFFECTIVE.
  So the demanded quality is a FIXED effective constant: 1−β₀ ≤ (C⁽¹⁾ log q)⁻¹.
- THEOREM 2 (pp.195–196; proof p.223): dichotomy (twins for every admissible pair of forms, OR
  a zero-free region with INEFFECTIVE C⁽²⁾). The only ineffectivity in the paper; it comes from
  "sup η not computable if finite", NOT from Siegel's theorem (never used).
- Twin primes proper: recovered from forms (4n−1,4n+1) and (4n+1,4n+3) (p.195):
  N(x) ~ 2𝔖C(4)(x/4)(log x)⁻² = 𝔖x(log x)⁻².

## 2. Dependency skeleton (§2, pp.197–200)

S⁽⁰⁾ (Λ·Λ target) → S⁽¹⁾ (coprimality to qP) → [Lemma 1,2,3] → S⁽²⁾ (Λ̃·Λ̃) → S⁽³⁾ (Λ*·Λ*)
→ [Rosser λ± , level D=q^{1/3}, dim 4] → Σ λ_d S(d) → [Lemma 5: S(d) asymptotic via
Kloosterman §§5–7] → κS₁{(L'/L)² + errors} → [Lemma 7: L'/L(1,χ)=ηL, κS₁ = x𝔖C(α)(ηL)⁻²]
→ S⁽⁰⁾ = 𝔖C(α)x + O(xz₀⁻¹), z₀ = A log log η (p.200).

Parameters: z (sieve cut), z₀ = log q/log z, P = Π_{2<p<z, χ(p)=1} p, D = q^{1/3}, d,z ≤ q^{1/3}.

## 3. The zero is consumed at exactly TWO analytic points

(A) LEMMA 3 (p.198; proof pp.206–207, (4.1)–(4.3)):
    Σ_{p≤x, χ(p)=1} p⁻¹ log p ≪ L (log η)^{-1/2}.
    "χ behaves like the exceptional character": χ(p) = −1 for almost all p (log-density), up to
    x = q⁵⁰⁰. Consumes: (i) existence of β₀ — the term −1/(s−β₀) at s = 1+L⁻¹ dominates −L'/L;
    (ii) DEURING–HEILBRONN repulsion r₀ = min{|1−ρ|: ρ≠β₀} ≫ L⁻¹ log η (Jutila [11, Thm 2]) —
    quality consumed LOGARITHMICALLY; (iii) Prachar disc count ≪ 1 + r log q (unconditional).
    Optimal a = (log η)^{1/2} gives the rate. This rate is the ultimate source of the paper's
    final error: exp(Az₀)·(log η)^{-1/2} ≤ z₀⁻¹ forces z₀ = A log log η.

(B) LEMMA 7 (p.200 (2.4); proof pp.207–210) + (4.9)–(4.11):
    L'/L(1,χ) = ηL + O(L(log η)^{-1/2})   [the zero AS a value: 1/(1−β₀) = ηL]
    κS₁ = {1+O(z₀(log η)^{-1/2})} x𝔖C(α)(ηL)⁻².
    Consumes: explicit formula ψ(y,χ) with main term −y^{β₀}/β₀ (Davenport Ch.19 (13),(14),
    T = y^{1/3}); other zeros killed by Jutila density N(σ,T,χ) ≪ (qT)^{(5/2)(1−σ)} (4.9,
    UNCONDITIONAL) + Deuring–Heilbronn σ₀ ≤ 1 − AL⁻¹ log η (p.209) + q^{15/2} ≤ x^{1/4}
    (i.e. x ≥ q³⁰ — far weaker than the window's q²⁵⁰ edge), giving (4.11):
    Σ_{u<n≤v} χ(n)Λ(n)/n = (1−β₀)⁻¹(v^{β₀−1} − u^{β₀−1}) + O(Lη^{−A}).
    Then log F = log log z − log ηL + γ₀ + O(z₀(log η)^{-1/2}) via ∫_x^∞ v^{β₀−2}/log v dv
    = log(η/500) + ... (p.210) — the computation that CONSUMES the upper window edge:
    (1−β₀) log x ≤ 500/η → 0, i.e. v^{β₀−1} ≈ 1 throughout the range ("the zero's reach").

STRUCTURAL CANCELLATION (pp.200, 210): main term = κS₁ · (L'/L(1,χ))²
= x𝔖C(α)(ηL)⁻² · (ηL)² = x𝔖C(α). The zero-dependent factors cancel EXACTLY; the zero never
feeds the size of the main term — it is consumed only to (i) make Λ̃ ≈ Λ (Lemma 3), and
(ii) control every error term. This is why quality enters only logarithmically.

## 4. Everything else is UNCONDITIONAL (no zero consumed)

- Lemma 1 (p.198; p.201): Λ* ≥ 0 and 0 ≤ Λ̃−Λ ≪ f(n)log n + (f(n₊)−1)Λ(n₋). Needs only χ real.
- Lemma 2 (p.198; pp.201–203): S⁽¹⁾ = S⁽²⁾ + O(xz₀⁻¹) + O(xL⁻¹e^{Az₀}·[Lemma-3 sum]); z₀ ≤ L^{1/3}.
- Lemma 8 (p.203–204): Selberg sieve, S(d₁,d₂;Z) ≪ x φ(d₁d₂)⁻¹(log Z)⁻² (H–R Thm 4.1).
- Lemma 6 (pp.199–200; 204–206): S⁽²⁾(δ),S⁽³⁾(δ) ≪ BLS⁽¹⁾(δ); B := L + |L'/L(1,χ)|.
- Rosser sieve, dim 4, D = q^{1/3} (Iwaniec [10]; pp.198–200): λ_d^± weights; needs sieving
  limit β ≥ 3 (dim 4) so δ ≤ Max(D,z²) ≤ q (p.199); fundamental lemma S₁'−S₁ ≪ e^{−z₀/4}S₁
  from (log D)/(log z) = z₀/3 (p.200).
- LEMMA 5 (p.199; §§5–7 pp.210–223): the paper's hardest lemma —
  S(d) = κ G(d)d⁻¹{(L'/L(1,χ))² + A²(d) + A'(d) + C₀} + O(xL⁴z⁻¹d⁻¹4^{ω(d)}), κ = xL(1,χ)²Π(...),
  for d|P, (d,α)=1, d,z ≤ q^{1/3}, x in (1.13). AUDITED: no β₀/η appears anywhere in §§5–7.
  Machinery: Λ* opening (p.210–211), congruence gymnastics (5.4)–(5.17), Lemma 10 ψ-sums via
  ESTERMANN's Kloosterman bound S(k;u,v) ≪ d(k)k^{1/2}(k,u,v)^{1/2} (7.1) — Weil-strength,
  effective, elementary (Estermann 1961); real-primitive-χ character sums (p.216–217), incl.
  Σ_t χ(ut+u')χ(t+v') ≪ (q, uv'−vu') and "Σχ(b₂) vanishes unless dΔ = q since χ primitive";
  q CUBE-FREE (from χ real primitive) consumed at (α_i, q/Δ)=1 steps via (1.9) (pp.212, 215–216).
  CAVEAT (architecture-fossil hazard): the paper's standing assumptions (p.196) formally include
  (1.11) throughout; Lemma 5's independence from the zero is my audit finding, not a stated claim.
- Lemma 9 (p.211): decomposition, error O(x^{1+ε}q⁻¹). Lemma 10 (pp.213–214; §7). Lemma 11 +
  §6 leading terms (pp.214–218). Zero-density (4.9) and Prachar disc count: unconditional.
- §8 conversion Λ → primes: p^e (e ≥ 2) terms O(x^{1/2}) (p.223).

## 5. Quality accounting — the triple-log cascade

1−β₀ ≤ (3L)⁻¹ defines η. Then:
  (log η)^{-1/2}  [Lemmas 3 & 7 rates; a = (log η)^{1/2}, D–H gives only log η repulsion]
  → z₀ := A log log η  [balance e^{Az₀}(log η)^{-1/2} ≤ z₀⁻¹ (Lemma 2→4); also e^{−z₀/4}
     fundamental-lemma gain and B²e^{−z₀/4} vs (ηL)² in the assembly (p.200)]
  → final error O(xz₀⁻¹) = O(x(log log η)⁻¹).
Relative-error ledger at assembly (p.200): O(BL)/(L'/L)² = O(1/η); O(B²e^{−z₀/4})/(L'/L)² =
O(e^{−z₀/4}); O(xL⁸z⁻¹) absorbed since z = q^{1/z₀}, z₀ ≤ A log log η ≤ A log log q.
CONSEQUENCE: the proof cannot exploit stronger zeros (e.g. 1−β₀ ≤ q^{−δ}) any better —
(log log η)⁻¹ is the architecture's ceiling; and for MERE INFINITUDE only η ≥ C⁽¹⁾ is consumed.

## 6. Range accounting — the x-vs-q window

- LOWER EDGE x ≥ q²⁵⁰: consumed at (6.11) p.218 — Kloosterman-derived error
  x^{15/16+3ε}q^{14} ≪ x^{1+ε}q⁻¹ (uses δ₁δ₂ ≤ q⁴d², d ≤ q^{1/3}); true need ≈ q^{240+O(ε)} —
  visible slack ~10 powers of q. HB remarks (p.214) any exponent < 1 for x suffices.
- UPPER EDGE x ≤ q⁵⁰⁰: consumed in Lemma 7's integral (p.210): (1−β₀)log x ≤ 500/η → 0 keeps
  v^{β₀−1} ≈ 1 (zero's influence must cover the whole range); and Lemma 3 applied at x = q⁵⁰⁰
  (p.208). Any fixed power works; polynomial-in-q is FORCED both ways (below by Weil saving,
  above by log x ≪ ηL for the zero's reach — binding only when η is at the constant threshold).
- Interior uses: x ≥ q³⁰ at (4.10)/(4.11) (p.209); z, d ≤ q^{1/3} (Lemma 5, Rosser level).
- Corollary 1 shrinks to [q³⁰⁰, q⁵⁰⁰]: dyadic sum down to q²⁵⁰, tail O(q²⁵⁰) (p.223).

## 7. Quantity accounting

- ONE zero per modulus. Uniqueness NOT assumed; multiplicity irrelevant; if several qualifying
  zeros exist pick any (D–H then constrains the rest automatically).
- Prachar disc count ⟹ O(1) qualifying zeros per χ; ≤ 2 real primitive χ per q [MEMORY: per
  modulus, real primitive characters correspond to fundamental discriminants ±q-ish] ⟹
  infinitely many triples ⟺ infinitely many distinct moduli q → ∞.
- Modulus shape demanded: ONLY "carries a real primitive character" (⟹ q cube-free, which §6
  actually consumes). No smoothness/progression/spacing constraints on the sequence of q.
- Per-triple yield: ≥ ½𝔖C(α)x(log x)⁻² pairs at x = q³⁰⁰ (Cor 1 + η ≥ C⁽¹⁾). Twins land only
  in the sparse windows [q³⁰⁰, q⁵⁰⁰] — HB's own sparsity caveat in the Goldbach remark (p.196).

## 8. Effectivity structure

| Object | Effective? | Source |
|---|---|---|
| C⁽⁰⁾ zero-free region | YES | p.194 (1.10) |
| Thm 1 / Cor 1 constants | YES, dep. α_i,β_i (and ε) only | p.195, p.196 |
| C⁽¹⁾ = exp exp{2A(𝔖C(α))⁻¹} | YES | p.223 |
| η ≪ q | YES (Davenport Ch.14 (14)) | p.194 |
| Estermann Kloosterman (7.1) | YES (elementary Weil-strength) | p.221 |
| Jutila density (4.9), D–H (Jutila Thm 2) | YES | pp.206, 209 |
| Iwaniec Rosser sieve, H–R Selberg sieve | YES | pp.198–199, 203 |
| C⁽²⁾ (Thm 2) | NO — dichotomy artifact only | p.223 |
| C⁽³⁾ caution ("max twin") | ineffectivity parable | p.196 |
Siegel's ineffective lower bound on L(1,χ): NEVER used.

## 9. Uses-LESS-than-hypothesis audit (the weakenings visible in the source)

1. The "3" in (1.11) is normalization (makes η ≥ 3, log η > 1). For infinitude the binding
   demand is η ≥ C⁽¹⁾, C⁽¹⁾ fixed effective: F = "∞ many (q, χ real primitive, β₀ real):
   L(β₀,χ)=0, 1−β₀ ≤ (C⁽¹⁾ log q)⁻¹". η → ∞ needed only for the ASYMPTOTIC (1.1).
2. Quality is consumed only through log η (D–H repulsion, a-averaging) — never polynomially.
3. Lemma 3's demand is really "Σ_{p≤q⁵⁰⁰, χ(p)=1} p⁻¹log p ≤ εL with ε small effective" —
   any hypothesis delivering that + the L'/L(1,χ) evaluation (B) would drive the same engine
   (the zero per se is convenient packaging for both).
4. Only the λ⁻ (lower-bound) side of the sieve + upper error bounds are needed for EXISTENCE
   of twins; the λ⁺ side only sharpens to an asymptotic (p.199 "treatment of the lower bound
   being similar", p.200 "analogous argument shows S⁽³⁾ ≥ ...").
5. x ≥ q²⁵⁰ has ~q¹⁰ slack; x ≤ q⁵⁰⁰ arbitrary fixed power; window shape log x ≍ L binding.
6. Montgomery's remark (p.196): circle method would need the STRONGER η(log q)⁻¹ → ∞
   (1−β₀ = o(L⁻²)). The entire sieve/Kloosterman apparatus exists to weaken quality demand
   into the band (const·log q)⁻¹ ≥ 1−β₀ — HB's genuine contribution band.

## 10. Misremembering hazards for downstream links (catch-genre #224/#239)

- Hazard: "needs 1−β₀ = o(1/log q)" — FALSE for infinitude (η ≥ C⁽¹⁾ suffices; Cor 2).
- Hazard: "needs zero-density conditionally" — Jutila (4.9) is unconditional.
- Hazard: "Lemma 5 is conditional" — formally under standing (1.11) (p.196) but consumes no
  zero (audited); any Lean port must re-verify this de-scoping.
- Hazard: forgetting BOTH window edges bind for different reasons (Weil below, zero-reach above).
- Hazard: treating "real primitive" as convenience — it is consumed (cube-free q in §6
  congruences via (1.9); primitivity for the Σχ(b₂) vanishing at p.216; real-χ in Λ̃, in the
  ± decomposition n₊n₋, and in the p.217 character-sum bound).
- Hazard: "one zero, quality only" — correct per triple, but the QUANTITY demand (infinitely
  many moduli) is irreducible in this architecture: each triple yields twins only inside its
  own window [q³⁰⁰, q⁵⁰⁰].
