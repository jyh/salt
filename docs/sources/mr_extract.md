# MR extraction — arXiv:1501.04585v4 (Matomäki–Radziwiłł, "Multiplicative functions in short intervals")

**Node:** MR-STAGE (source extraction, no Lean). **Source:** `docs/sources/1501.04585v4.pdf`
(41 pp, arXiv v4, 15 Oct 2017 timestamp; LaTeX text layer — clean extraction). Annals of Math. 183(3):1015–1056,
2016. This is Tao's **[16]** (chowla.txt:1527) and MRT's **[17]** (1503.05121 refs, p.32). Its own reference
map (MR refs, pp.39–41): **[8]** = Friedlander–Iwaniec *Opera de Cribro* (sieve); **[9]** = Friedlander–Granville
(smoothing smooth numbers); **[12]** = Granville–Soundararajan *Decay of mean values* (Halász input);
**[19]** = Ivić *Riemann Zeta-Function* (ζ′/ζ bound); **[20]** = Iwaniec–Kowalski *Analytic Number Theory*
(mean/large-value theorems); **[32]** = Montgomery *Ten Lectures* (duality); **[36]** = Shiu (moment bound);
**[31]** = the MRT paper (1503.05121). **[8]** and **[20]** here differ in numbering from MRT's `[8]/[20]`.

**Labels:** GROUNDED (page/eq read this session) is the default; every statement carries a page ref. Ambiguities
flagged **⚠**. Cross-refs to `mrt_extract.md` (the complex extension) and `mr_map_sources.md` (the port map).

---

## 1. THE MAIN-THEOREM CHAIN FOR THE λ/SHORT-INTERVAL CASE THE FREEZE CONSUMES

**What the gate actually consumes:** Tao's Prop 2.4 at λ (c_p=1, major arcs only) → **MRT Theorem A.1**
(chowla.txt:743–750, GROUNDED). Theorem A.1's proof (mrt_extract §3.1) = **MRT Theorem A.2** (main term, with
the `M(f;X)` factor) **+ MR Theorem 3 with f≡1** (indicator term) **+ MRT Lemma 2.2** (density). So the MR-paper
node the gate rides is **Theorem 3**, and its complex-non-pretentious extension is MRT Appendix A. The bilinear
√X theorems (Thm 2, Thm 4) and Corollaries 1–6 (smooth numbers, sign changes) are **NOT gate inputs**.

- **Theorem 1** (p.1) — NOT the gate input, but the parent: `f:ℕ→[−1,1]` mult. ∃ absolute `C, C′>1` s.t. for
  `2 ≤ h ≤ X`, `δ>0`: `|(1/h)Σ_{x≤n≤x+h}f(n) − (1/X)Σ_{X≤n≤2X}f(n)| ≤ δ + C′(loglog h/log h)` for all but at most
  `CX((log h)^{1/3}/(δ²h^{δ/25}) + 1/(δ²(log X)^{1/50}))` integers `x∈[X,2X]`. **`C′ = 20000`** (p.2).
- **Theorem 3** (p.7) — **THE GATE-CONSUMED CORE** (real-valued; MRT A.1 wraps it):
  > `f:ℕ→[−1,1]` mult, `S = S_X` (Def §2) with `η∈(0,1/6)`, `[P₁,Q₁]⊂[1,h]`. For `X > X(η)`:
  > `(1/X)∫_X^{2X} |(1/h)Σ_{x≤n≤x+h, n∈S} f(n) − (1/X)Σ_{X≤n≤2X, n∈S} f(n)|² dx ≪ (log h)^{1/3}/P₁^{1/6−η} + 1/(log X)^{1/50}`.

  **Crucial for λ:** Theorem 3 is UNCONDITIONAL (no non-pretentiousness hypothesis) — it compares short-average
  to long-average. For λ the long-average `(1/X)Σ_{X≤n≤2X}λ(n)` is `o(1)` by PNT, so short-average is `o(1)` in
  almost all short intervals. **The non-pretentiousness enters, for the real λ, only through the long average
  (PNT), not through a separate M-factor.** BUT the gate's modulated/twisted sums (λ·χ after the major-arc
  reduction) are complex → the `M`-quantitative Theorem A.2 (mrt_extract §3.2) is what the port needs.

**Def of S (MR §2, p.6):** identical to MRT Def 2.1. `η∈(0,1/6)`; `Q₁ ≤ exp(√log X)`;
(2) `loglog Q_j/(log P_{j−1}−1) ≤ η/(4j²)`; (3) `(η/j²)log P_j ≥ 8 log Q_{j−1} + 16 log j`;
(4) `P_j = exp(j^{4j}(log Q₁)^{j−1}log P₁)`, `Q_j = exp(j^{4j+2}(log Q₁)^j)`; `J` = largest j with
`Q_J ≤ exp((log X)^{1/2})`. Density of complement: `X·log P₁/log Q₁` (fundamental lemma, p.6).

Theorem 3 reduces (eq (5), p.7) to **Proposition 1** (below). `Theorem 1 ⟸ Theorem 3 (with f and f≡1) +
fundamental lemma of sieve` (p.30–31).

---

## 2. THE PROOF ARCHITECTURE (Dirichlet-poly decomposition · large-value machinery · Halász points)

All page/eq refs GROUNDED. The engine is Sections 3–8.

### 2.1 Proposition 1 (the mean-square Dirichlet-polynomial bound), p.23 — the core

> `f:ℕ→[−1,1]` mult, `S` as in §2, `F(s) = Σ_{X≤n≤2X, n∈S} f(n)/n^s`. For any T:
> `∫_{(log X)^{1/15}}^T |F(1+it)|² dt ≪ (T/(X/Q₁) + 1)·((log Q₁)^{1/3}/P₁^{1/6−η} + 1/(log X)^{1/50})`.

Trivial bound (Lemma 6 MVT): `T/X + 1`. Proof (§8.1–8.4, pp.24–29): the exponent `α_j := 1/4 − η(1 + 1/(2j))`
(eq (20), p.24), so `1/4 − (3/2)η ≤ α₁ ≤ … ≤ α_J ≤ 1/4 − η`.

### 2.2 The Dirichlet-polynomial (Buchstab/Ramaré) decomposition — pp.8–10, 19–20

Split the integration range `(log X)^{1/15} ≤ t ≤ X/h` into `J+1` disjoint sets `𝒯₁,…,𝒯_J, 𝒰` by the size of
the **prime Dirichlet polynomials** `Σ_{P_j≤p≤Q_j} f(p)/p^{1+it}` (eq (6), p.8). `t∈𝒯_j` iff j is the smallest
index for which all narrow subdivisions of (6) over `[P_j,Q_j]` are small; `𝒰` = the residual (no such j).
**`𝒰` is thin: measure `O(T^{1/2−ε})`** (p.8) — the exceptional/extreme-t set.

- On `𝒯_j`: **Buchstab/Ramaré identity** (eq (9), p.9; §5 "a variant of Ramaré's identity [8, §17.3]", credited
  to Tao) extracts a prime polynomial over `[P_j,Q_j]` (small by def of `𝒯_j`) times a mean-value over the
  co-factor `m`. **⚠ Sedunova–Wang correction (footnote 1, p.9):** the `1_{(p,m)=1}` term "was incorrectly
  expressed as 1" in the published version — corrected here (identical to MRT footnote 3). The port must use v4.
- **Lemma 12** (p.19–20, the decomposition mean-square bound): `∫_𝒯 |Σ_{X≤n≤2X}a_n/n^{1+it}|² dt ≪ H log(Q/P)·
  Σ_{j∈I} ∫_𝒯 |Q_{j,H}(1+it)R_{j,H}(1+it)|² dt + (T+X)/X·(1/H + 1/P + Σ_{(n,Π p)=1}|a_n|²/n)`, `I = [⌊H log P⌋,
  H log Q]`. This is the workhorse splitting of the integer polynomial into (short-prime-block)·(co-factor).

### 2.3 The mean- and large-value machinery — §4, pp.15–18 (GROUNDED)

- **Lemma 6** (MVT, [20, Thm 9.1]): `∫_{−T}^T |A(it)|² dt = (T + O(N)) Σ_{n≤N}|a_n|²`. [= freeze S6a target.]
- **Lemma 7** (well-spaced, [20, Thm 9.4]): `Σ_{t∈𝒯}|A(it)|² ≪ (T+N) log 2N Σ|a_n|²` (𝒯 well-spaced: `|t−r|≥1`).
- **Lemma 8** (large-value): `P(s)=Σ_{P≤p≤2P}a_p/p^s`, `|a_p|≤1`, 𝒯 well-spaced with `|P(1+it)|≥V^{−1}`. Then
  **`|𝒯| ≪ T^{2 log V/log P} V² exp(2 (log T/log P) loglog T)`** (p.15–16, via `P(s)^k`, `k=⌈log T/log P⌉`).
- **Lemma 9** (Halász inequality for integers, [20, Thm 9.6]): `Σ_{t∈𝒯}|A(it)|² ≪ (N + |𝒯|√T) log 2T Σ|a_n|²`.
- **Lemma 10** (duality, [32, Ch.7 Thm 6]): the L²-duality bridge.
- **Lemma 11** (**Halász inequality for PRIMES**, p.17–18): `P(s)=Σ_{P≤p≤2P}a_p p^{−s}` prime-supported,
  𝒯 well-spaced ⊂[−T,T]. `Σ_{t∈𝒯}|P(it)|² ≪ (P + |𝒯|P exp(−log P/(log T)^{2/3+ε})(log T)²)·Σ|a_p|²/log P`.
  **⚠ ζ VK REGION ENTRY #2:** proof (p.17–18) uses duality (Lemma 10) + Mellin + the `ζ′/ζ` contour shift to
  `σ = 1 − c(log T)^{−2/3+ε}` inside the ζ zero-free region, bounding `ζ′/ζ(σ+it) ≪ (log T)^{1+2/3+ε}` via
  **[19, formula (1.52)]** (Ivić): `O(log T)` zeros, `≫ (log T)^{−2/3+ε}` from the contour. **θ=2/3.**

### 2.4 The Halász input points — §3, pp.11–13 (GROUNDED) — THE pointwise decay

Halász's theorem (NOT in mathlib — see §5 pricing). "unless a multiplicative function pretends to be `p^{it}`,
it is small on average."

- **Lemma 1** (Halász, p.11–12): `F(s)=Σ_{x≤n≤2x}f(n)/n^s`, `T₀≥1`, `M(x,T₀) := min_{|t₀|≤T₀} 𝔻(f, p^{i(t+t₀)}; x)²`
  (⚠ transcribed verbatim: the OCR shows `p^{it+it₀}`, i.e. distance to `p^{i(t+t₀)}`, the same `t` as in
  `F(σ+it)` — the "pretentious-near-t" quantity). Then
  `|F(σ+it)| ≪ x^{1−σ}(M(x,T₀)exp(−M(x,T₀)) + 1/T₀ + loglog x/log x)`. Source: **[12, Corollary 1]**
  (Granville–Soundararajan) + partial summation.
- **Lemma 2** (p.12) — **⚠ ζ VK REGION ENTRY #1** (the internal non-pretentiousness): `f:ℕ→[−1,1]` mult, `ε>0`.
  For fixed `A` and **`1 ≤ |α| ≤ x^A`**: `𝔻(f, p^{iα}; x) ≥ (1/(2√3) − ε)√(loglog x) + O(1)`. Proof:
  `𝔻(1, p^{2iα}; x)² ≥ (1/3 − ε)loglog x + O(1)` "by the zero-free region for the Riemann zeta-function"; prime
  cutoff `exp((log X)^{2/3+ε})`. **θ=2/3, coefficient 1/3; heights `|α| ≤ x^A`.**
- **Lemma 3** (p.12–13): the `R`-polynomial (Buchstab co-factor) Halász bound: `R(s)=Σ_{X≤n≤2X}f(n)/n^s·
  1/(#{p∈[P,Q]:p|n}+1)`, `X≥Q≥P≥2`, real f. For `t∈[(log X)^{1/16}, X^A]`:
  `|R(1+it)| ≪ log Q/((log X)^{1/16}log P) + log X·exp(−(log X/(3 log Q))·log(log X/log Q))`. Uses Lemmas 1,2 +
  Q-smooth-number count. **Heights up to `X^A`.**
- **Lemma 4** (p.13, Lipschitz, Granville–Soundararajan): `(1/y)Σ_{x≤n≤x+y}f(n) = (1/X)Σ_{X≤n≤2X}f(n) +
  O(1/(log X)^{1/20})` for `X/(log X)^{1/5} ≤ y ≤ X`.

### 2.5 The moment computation (Shiu input) — §6, pp.20–21 (GROUNDED)

- **Lemma 13** (p.20–21): `Q(s)=Σ_{Y₁≤p≤2Y₁}c_p/p^s`, `A(s)=Σ_{X/Y₂≤m≤2X/Y₂}a_m/m^s`, `ℓ=⌈log Y₂/log Y₁⌉`.
  `∫_{−T}^T |Q(1+it)^ℓ A(1+it)|² dt ≪ (T/X + 2^ℓ Y₁)(ℓ+1)!²`. Uses **Shiu's bound [36, Thm 1]** (eq (18), p.21):
  `Σ_{Y≤n≤2Y} g(n)² ≪ Y Π_{p≤Y}(1 + (|g(p)|²−1)/p) ≪ Y` for the divisor-type g with `g(p^k)=(k+1)` on `[Y₁,2Y₁]`.
  **[Landed-corpus note: `ShiuCore` is proven (`Salt/Maynard/ShiuFinal.lean: sum_tau_in_ap_le`); adjacent but a
  τ-in-AP form — needs adaptation to this `Σ g(n)²` shape, partial credit in pricing.]**

### 2.6 The Parseval bound — §7, pp.21–23 (GROUNDED)

- **Lemma 14** (Parseval, p.21–23): `|a_m|≤1`, `1 ≤ h₁ ≤ h₂ = X/(log X)^{1/5}`, `A(s)=Σ_{X≤m≤4X}a_m/m^s`.
  `(1/X)∫_X^{2X}|(1/h₁)S_1(x) − (1/h₂)S_2(x)|² dx ≪ 1/(log X)^{2/15} + ∫_{1+i(log X)^{1/15}}^{1+iX/h₁}|A(s)|²|ds|
  + max_{T≥X/h₁}(X/h₁)/T ∫_{1+iT}^{1+i2T}|A(s)|²|ds|`. Via Perron's formula + a smoothing (à la Saffari–Vaughan
  [35]) to exchange the order of integration. **[Landed-corpus: `Salt/LS/Parseval.lean` scaffolds this.]**

### 2.7 Assembly of Proposition 1 — §8, pp.24–29 (GROUNDED)

`[T₀,T] = ⋃_{j=1}^J 𝒯_j ∪ 𝒰`, `T₀=(log X)^{1/15}`; `∫_{T₀}^T|F(1+it)|² dt ≪ E₁ + … + E_J + ∫_𝒰|F(1+it)|² dt` (eq 24).
- **§8.1 E₁** (p.25): mean-value theorem (Lemma 6), `≪ (T/(X/Q₁)+1)(log Q₁)^{1/3}/P₁^{1/6−η}`.
- **§8.2 E_j, 2≤j≤J** (p.25–27): split `𝒯_j = ⋃_r 𝒯_{j,r}`, raise the large prime-block polynomial to a power
  `ℓ_{j,r} = ⌈(v/H_j)/(r/H_{j−1})⌉`, apply the moment **Lemma 13**; `E_j ≪ (T/X+1)/(j²P₁)`.
- **§8.3 ∫_𝒰** (p.27–29): Lemma 12 (with `P=exp((log X)^{1−1/48})`, `Q=exp(log X/loglog X)`, `H=(log X)^{1/48}`),
  well-spaced points (𝒰 thin, `O(T^{1/2−ε})`), **large-value Lemma 8** + **Halász-for-integers Lemma 9** +
  **Halász-for-primes Lemma 11** + **Lemma 3** (R-bound). The prime-window gain saves the extra logarithm:
  `∫_𝒰|F(1+it)|² dt ≪ (T/X+1)(log X)^{−1/48+o(1)}`. This is the intricate core (§8.3).
- **§8.4** (p.29): collect → Proposition 1.

**Skeleton (matches the freeze's S8, mr-freeze.md:18):** `Parseval (L14) → MVT (L6=S6a) → Ramaré/Buchstab
(L12=S6b) → Halász-grade pointwise (L1–3, L11) → extreme-t via the ζ region (L2, L11, MRT A.6=S3)`.

---

## 3. THE SPECIFIC INPUTS (mean-value · sieve · zeta) — GROUNDED page refs

| input | where consumed | source (MR ref) | corpus status |
|---|---|---|---|
| MVT for Dirichlet polys `∫|A|²=(T+O(N))Σ|a_n|²` | Lemma 6; E₁, moments | **[20, Thm 9.1]** (Iwaniec–Kowalski) | freeze S6a `dirichlet_poly_l2_mvt`; LS/ scaffolds |
| well-spaced mean value | Lemma 7 | **[20, Thm 9.4]** | LS/Spacing.lean (well-spaced defs) |
| large-value estimate | Lemma 8; §8.3 | self-contained (P(s)^k) | none — port |
| Halász large sieve (integers) | Lemma 9; §8.3 | **[20, Thm 9.6]** | none — port |
| duality principle | Lemma 10 → Lemma 11 | **[32, Ch.7 Thm 6]** (Montgomery) | none — port |
| Halász for primes (ζ′/ζ) | Lemma 11; §8.3 | **[19, (1.52)]** (Ivić) + **ζ VK region** | ζ region LANDED (`zeta_zero_free_region_pow`, θ=3/4); ζ′/ζ partial (SW Landau) |
| Halász theorem (pointwise) | Lemmas 1,3; complex A.4–A.8 | **[12, Cor 1]** / **[9]** (Granville–Sound. / GHS) | **NONE — the dominant gap** |
| ζ zero-free region (internal non-pretentiousness) | Lemma 2; MRT A.6 | ζ VK region | **LANDED** (θ=3/4; serves via S3, coeff 1/4 vs their 1/3) |
| fundamental lemma of sieve | S-density; Thm 1 assembly; Cor | **[8, Thm 6.17]** (Friedlander–Iwaniec) | Brun/ sieve scaffolds |
| Shiu's theorem (`Σ g(n)² ≪ Y`) | Lemma 13 (moments) | **[36, Thm 1]** (Shiu) | **ShiuCore LANDED**, adapt |
| Perron / smoothing | Lemma 14 (Parseval) | [35] Saffari–Vaughan | LS/Parseval scaffolds |

**Zeta information consumed, precisely:** the ζ (Riemann, NOT L(s,χ)) VK zero-free region, at exactly THREE
places — Lemma 2 (p.12, heights `|α|≤x^A`), Lemma 11 (p.17–18, ζ′/ζ contour), and (in the complex extension)
MRT (A.6) (extreme t `|t−t₁|>(log X)^{20}`). **All three are served by the landed `zeta_zero_free_region_pow`
(θ=3/4); coefficient 1/3→1/4 is qualitatively harmless.** This **settles the "elementary-Halász-only" question
(mr_map_sources.md §0/§4, entry point 2): NO — the ζ VK region IS consumed inside the MR proof, at Lemmas 2 & 11.
But it is the ζ region (which is landed), not an L-function region.** The claim "the classical MR proof needs
only elementary-Halász inputs for λ" is **FALSE** as grounded; the correct statement is "needs elementary-Halász
PLUS the ζ VK region, both of which the campaign holds."

---

## 4. S8 PRICING — THE NODE COUNT + LINE BAND FOR MR-CORE AT λχ-TWISTS

**Scope (per mr-freeze.md:18, S8):** qualitative fixed-δ MR at λ·χ, `q ≤ W`, consuming S6a/S6b/S2/S3 and the
landed ShiuCore/LS as inputs. **What S8-proper must port** = MR Prop 1 + Theorem 3, AND the MRT-Appendix-A
complex extension (Prop A.3, Lemmas A.4–A.8, Theorems A.1/A.2), because the major-arc reduction produces complex
λ·χ (mrt_extract §4). "Qualitative fixed-δ" means only `mean-square → 0` is needed, not the sharp exponents.

### 4.1 Node inventory (S8-proper, excluding already-priced wave rungs S6a/S6b/S2/S3)

| block | MR/MRT nodes | line estimate | notes |
|---|---|---|---|
| **Halász theorem (pointwise)** | Lemma 1–3 (real) + Lemmas A.4–A.8 (complex, method [9]) | **4.0–7.0k** | **the dominant gap; no corpus.** [12]/[9] proofs from scratch. Even qualitative ≥ 2–3k. |
| Large-value + duality + Halász-primes | Lemmas 7,8,9,10,11 (beyond S6a=L6) | 2.5–4.0k | LS/Spacing partial; ζ′/ζ couples to SW Landau; ζ region landed |
| Parseval bound | Lemma 14 | 1.0–1.5k | LS/Parseval scaffolds |
| Moment / Shiu | Lemma 13 | 0.5–1.5k | **ShiuCore landed**, adapt to `Σ g(n)²` |
| Buchstab/Ramaré (beyond S6b) | Lemma 12 + §5 + Sedunova–Wang fix | 1.0–2.0k | v4 corrected identity |
| Prop 1 assembly (§8.1–8.4) | E₁, E_j, ∫_𝒰, the 𝒯_j/𝒰 split | 2.0–3.5k | intricate combinatorics; §8.3 is the hard core |
| Complex extension assembly | Prop A.3 (v3-corrected) + Thm A.2 + Thm A.1 | 2.0–3.5k | the M-factor; the Fei-Wei correction; S9 surface |
| Theorem 3 + density + Def S | Thm 3, Lemma 2.2, Def 2.1/§2, MR §9 glue | 1.0–2.0k | ties to the door |
| **S8-proper total** | | **14–25k** | center **~18k** |

### 4.2 The band — narrowing the freeze's 8–20k

**Narrowed band: 14–22k lines, center ~18k. CLASS D confirmed.** The freeze's floor of 8k is **NOT reachable**:
Halász-from-scratch (4–7k) + the large-value/Halász-primes block (2.5–4k) already exceed 6.5k with zero corpus,
before Prop 1 assembly and the complex extension. **Recommend revising the freeze's floor UP from 8k to ~14k.**
The qualitative simplification (no sharp exponents) trims the upper tail but does NOT remove Halász's theorem as
a full theorem port. If a qualitative Halász could be sourced from MNT-III Thm 23.15 (montgomery3.txt:3538) the
low end could approach 14k — **but MEMORY/mr_map_sources §5 confirm 23.15 is only the qualitative EQUIVALENCE,
not the pointwise `|F(σ+it)| ≪ x^{1−σ}(Me^{−M}+…)` form (Lemma 1) with the needed uniformity** — so the Lemma 1
bound must be ported via [12]/[9] regardless. Net honest band: **14–22k**.

### 4.3 Top 3 port risks (with the freeze rungs they land on)

1. **Halász's theorem is a full C/D port with NO corpus scaffolding (grep-confirmed empty).**
   — the pointwise `|F(σ+it)| ≪ x^{1−σ}(M(x,T₀)e^{−M(x,T₀)} + 1/T₀ + loglog x/log x)` (Lemma 1, via [12, Cor 1])
   AND its complex M-version (Lemmas A.4–A.8, via [9] Granville–Harper–Soundararajan). This is the single largest
   sub-block (4–7k) and gates everything downstream. **Lands on: S8 skeleton "Halász-grade pointwise"; the OPEN
   "quantitative-Halász sourcing" (mr-freeze.md:39).** *Mitigation:* the complex A.4–A.8 and real Lemma 1–3 share
   the [9] method — port [9]'s Halász proof once, reuse. RISK LEVEL: highest; D.

2. **The large-value / Halász-for-primes block, including the ζ′/ζ contour shift (Lemmas 7–11).**
   — Lemma 8 (`|𝒯| ≪ T^{2 log V/log P}V²…`), Lemma 9 ([20, 9.6]), Lemma 11 (prime-restricted, via [19,(1.52)]
   ζ′/ζ into the ζ VK region). The well-spaced-points bookkeeping and the duality (Lemma 10) are not in mathlib;
   the ζ′/ζ partial-fraction couples to the landed SW `Landau.lean`/`ContourShift.lean` but at the ζ level.
   **Lands on: S7 (ARC large-value machinery) + S2 (Landau/ζ′/ζ) + S8.** *Risk:* the `O(log T)` zeros / `≫(log
   T)^{−2/3+ε}`-from-contour estimate must be re-derived from the landed θ=3/4 region (their (1.52) is θ=2/3);
   the coefficient shifts but the shape survives. RISK LEVEL: high; C/D.

3. **The complex non-pretentious extension (MRT Appendix A: Prop A.3 with the published-proof ERROR).**
   — Prop A.3's published proof is "incorrect when M(f;X) grows very slowly with X" (mrt_extract §3.3, Fei Wei);
   the port MUST use the arXiv-v3 corrected `exp(−M)` proof (the `𝒯₀`/`𝒯₁` split at `M ≥ (1/8)loglog X`, Lemmas
   A.4–A.8). Getting the slow-M regime right is delicate, and the scale coupling (`M(f;X)` at interval scale X,
   height `|t|≤X`, coefficient 1/3→1/4) must be tracked. **Lands on: S9 (MRT-A1, the FLAW-1 repair) + the A-arm.**
   *Mitigation:* the A-arm itself is now clean (mrt_extract §0.3 — rides on `W ≤ (log X)^{1/125}`, margin ~10×);
   the risk is the Prop A.3 mean-square, not the quality bookkeeping. RISK LEVEL: high; C/D.

**Honorable-mention risk (below the top 3):** the Sedunova–Wang `1_{(p,m)=1}` correction (MR footnote 1 p.9 /
MRT footnote 3) must be carried through Lemma 12 and every Buchstab step — a silent off-by-one there is exactly
the Benli-flavored trap (an identity that is "obviously 1" but isn't). Port from v4 only.

---

## 5. MR EXPONENT LEDGER (verbatim) + FLAGS

| quantity | value | ref |
|---|---|---|
| Thm 1 exceptional set | `CX((log h)^{1/3}/(δ²h^{δ/25}) + 1/(δ²(log X)^{1/50}))`, `C′=20000` | p.1–2 |
| Thm 3 RHS | `(log h)^{1/3}/P₁^{1/6−η} + 1/(log X)^{1/50}`, `η∈(0,1/6)`, `[P₁,Q₁]⊂[1,h]` | p.7 |
| Prop 1 RHS | `(T/(X/Q₁)+1)((log Q₁)^{1/3}/P₁^{1/6−η} + 1/(log X)^{1/50})`; `∫` from `(log X)^{1/15}` | p.23 |
| α_j (case exponent) | `1/4 − η(1 + 1/(2j))` | p.24 (20) |
| Lemma 1 (Halász) | `x^{1−σ}(M e^{−M} + 1/T₀ + loglog x/log x)`, `M=min_{|t₀|≤T₀}𝔻(f,p^{i(t+t₀)};x)²` | p.11–12 |
| Lemma 2 (ζ region) | `𝔻(f,p^{iα};x) ≥ (1/(2√3)−ε)√loglog x`; `𝔻(1,p^{2iα})²≥(1/3−ε)loglog x`; `1≤|α|≤x^A` | p.12 |
| Lemma 3 (R-Halász) | `log Q/((log X)^{1/16}log P) + log X·exp(−(log X/3 log Q)log(log X/log Q))`; `t∈[(log X)^{1/16},X^A]` | p.12–13 |
| Lemma 8 (large-value) | `|𝒯| ≪ T^{2 log V/log P} V² exp(2(log T/log P)loglog T)` | p.15–16 |
| Lemma 11 (Halász primes) | `(P + |𝒯|P exp(−log P/(log T)^{2/3+ε})(log T)²)Σ|a_p|²/log P`; **θ=2/3** | p.17–18 |
| Lemma 13 (moment) | `(T/X + 2^ℓ Y₁)(ℓ+1)!²`, `ℓ=⌈log Y₂/log Y₁⌉`; Shiu `Σ g(n)²≪Y` | p.20–21 |
| Lemma 14 (Parseval) | `1/(log X)^{2/15} + ∫_{1+i(log X)^{1/15}}^{1+iX/h₁}|A|² + max_T (X/h₁)/T ∫_{1+iT}^{1+i2T}|A|²` | p.21–23 |
| §8.3 𝒰 split params | `P=exp((log X)^{1−1/48})`, `Q=exp(log X/loglog X)`, `H=(log X)^{1/48}`; `∫_𝒰 ≪ (log X)^{−1/48+o(1)}` | p.27–29 |
| Def S | `P_j=exp(j^{4j}(log Q₁)^{j−1}log P₁)`, `Q_j=exp(j^{4j+2}(log Q₁)^j)` | p.6 |

**FLAGS (LOUD):**
1. **⚠ Lemma 1 `M(x,T₀)` centering:** OCR shows `𝔻(f, p^{it+it₀}; x)²`, i.e. distance to `p^{i(t+t₀)}` with the
   same `t` as in `F(σ+it)` — the pretentious-near-t quantity. Transcribed verbatim; the exact `t`/`t₀`
   coupling is at p.11–12. Not a rounding issue, but note the argument is `p^{i(t+t₀)}`, not `p^{it₀}`.
2. **⚠ θ=2/3 vs landed θ=3/4:** MR's coefficient 1/3 (Lemma 2) and the sharp exponents `1/6−η`, `1/48`, `1/50`,
   `1/700`, `1/3000` are VK-θ=2/3-tied. For the **qualitative fixed-δ S8** this is irrelevant (only need the
   mean-square `→ 0`, which holds for any `c > 3/125`, mrt_extract §0.3). For any QUANTITATIVE port they shift —
   re-derive from the landed region. This is precisely the Benli-trap discipline: do not silently carry 1/3.
3. **⚠ Sedunova–Wang `1_{(p,m)=1}` correction** (footnote 1, p.9): port from v4; the published "=1" is wrong.
4. **⚠ Shiu adaptation:** ShiuCore (landed, `sum_tau_in_ap_le`) is τ-in-AP; Lemma 13 needs `Σ_{Y≤n≤2Y} g(n)² ≪ Y`
   for the specific block-divisor g. Adjacent, not identical — priced as adaptation (0.5–1.5k), not free reuse.
5. **No scanned-image OCR risk:** LaTeX text layer; exponents crisp. The genuine ambiguities are #1 and the
   mrt_extract Q-vs-W (Thm 2.3).

---

## 6. §9 — THE TWO-CASE PARAMETER SET (transcribed 2026-07-25, SEC9-SCRIBE)

**Why:** §4.1's row "Theorem 3 + density + Def S … MR §9 glue" and §1's one-line `Theorem 1 ⟸ Theorem 3 +
fundamental lemma (p.30–31)` priced the §9 glue without transcribing it. The **§9-glue rung (door-road stone 6)**
consumes the actual parameter instantiation. This section supplies it. **Purely additive: no row above is
altered.** Where §6 restates something §1–§5 already carries, the agreement is stated explicitly in §6.6.

**Method (the two-read rule):** every formula below was read twice at different moments — once from the PDF
text layer (`pdftotext`), once from the rendered page image — and the two compared. **This caught a live trap:**
the text layer renders `H_j := j²·P₁^{1/6−η}/(log Q₁)^{1/3}` (p.24) as if the `j²` were `2^j`, and `P_j ≥ P₁^{j²}`
(p.25) as if it were `P₁^j`. Superscript-vs-subscript flattening in the text layer is the defect generator; the
rendered image is the referee. **Every row below carries a page + display/eq cite.**

§9 = pp. 29 (bottom third) – 31 (top). §10 begins p.31 mid-page.

### 6.1 Theorem 3's proof (p.29 bottom → p.30) — the two-step skeleton

**Step 1 (Lemma 14 ∘ Proposition 1)** — p.29, bottom, unnumbered display, continued onto p.30 line 1:

> `(1/X)∫_X^{2X} |(1/h)Σ_{x≤n≤x+h, n∈S} f(n) − (1/h₂)Σ_{x≤n≤x+h₂, n∈S} f(n)|² dx ≪ (log h)^{1/3}/P₁^{1/6−η} + 1/(log X)^{1/50}`,
> **when `Q₁ ≤ h ≤ h₂ = X/(log X)^{1/5}`.**

⚠ **Note the RHS comparand: it is the `h₂`-average, NOT the `X`-average.** Theorem 3 as stated (p.7, extract
:29–30) compares to `(1/X)Σ_{X≤n≤2X, n∈S} f(n)`. The bridge from `h₂`-average to `X`-average is Step 2. The
door road must carry both steps.

**Step 2 (eq (26))** — p.30, "Using Lemma 4 together with Lemma 5 we have, for any `X ≤ x ≤ 2X`,"

> (26) `(1/h₂)Σ_{x≤n≤x+h₂, n∈S} f(n) = (1/X)Σ_{X≤n≤2X, n∈S} f(n) + O((log X)^{−1/20+o(1)})`

then verbatim: *"and the claim follows in case `h ≤ h₂`. In case `h > h₂`, the claim follows immediately
from (26)."* (p.30, ∎ ends the Theorem 3 proof.)

- `h₂ = X/(log X)^{1/5}` is **exactly** the lower endpoint of Lemma 4's `y`-range (`X/(log X)^{1/5} ≤ y ≤ X`,
  p.13) — the two constants are the same constant, not a coincidence. GROUNDED p.13 + p.30.
- **[DERIVED, not in the paper]** the `o(1)` in `(log X)^{−1/20+o(1)}` (vs Lemma 4's clean `O(1/(log X)^{1/20})`)
  is the cost of the `2^J` inclusion–exclusion terms Lemma 5 introduces; MR spell out `2^J ≪ (log X)^{o(1)}`
  at p.28 (in §8.3) but not at (26).
- **[DERIVED]** squaring (26) gives `O((log X)^{−1/10+o(1)})`, absorbed by the `1/(log X)^{1/50}` of Step 1
  (`−1/10 < −1/50`). That is why the two steps compose without loss.

### 6.2 🚨 LOUD CORRECTION — Lemma 4 + Lemma 5 are **NOT** retired by `h ≤ h₂`

The dispatch brief asked for these marked *"not needed on the door road (h ≤ h₂ by exponential margin)"*.
**Read twice at p.30: that is wrong.** Eq (26) is stated **once** and used in **both** branches:

| branch | what (26) does | door road (`h = O(log X)`) |
|---|---|---|
| `h ≤ h₂` | converts Step 1's `h₂`-average into Theorem 3's `X`-average — the **only** bridge | **LOAD-BEARING** |
| `h > h₂` | gives the whole claim by itself (interval already long; no exceptional set) | RETIRED (`h ≪ log X ≪ h₂`) |

**What `h ≤ h₂` retires is only the second row — the standalone long-interval branch. Lemma 4 (Lipschitz,
Granville–Soundararajan, p.13) and Lemma 5 (inclusion–exclusion for `n ∈ S`, p.15) stay on the critical path
of the door road.** Any port plan that drops them cannot reach Theorem 3's stated `X`-average comparand.

- **Lemma 4** (p.13; extract already carries it at :107–108, verified verbatim this session): `f:ℕ→[−1,1]` mult.
  For any `x ∈ [X,2X]` and `X/(log X)^{1/5} ≤ y ≤ X`:
  `(1/y)Σ_{x≤n≤x+y} f(n) = (1/X)Σ_{X≤n≤2X} f(n) + O(1/(log X)^{1/20})`.
  Proof (p.13–14) reduces to (13) `|（1/X)Σ_{n≤X}f(n) − (1/Y)Σ_{n≤Y}f(n)| ≪ 1/(log X)^{1/4}` for `X/4 ≤ Y ≤ X`,
  via `t_f` = minimiser of `𝔻(f,p^{it};X)` over `|t| ≤ log X`, Halász (Lemma 1) when `𝔻(f,p^{it_f};X)² ≥ (1/3)loglog X`,
  and **[12, Lemma 7.1 and Theorem 4]** + **[12, Corollary 3]** (Granville–Soundararajan) otherwise; the
  `|t_f| ≥ 1/100` case uses `𝔻(f,p^{it_f};X)² ≥ (1 − 2/π − o(1))loglog X` by partial summation + PNT.
  **NEW ROW vs §2.4: the `1 − 2/π` constant and the `|t_f| ≤ 1/100`, `(1/3)loglog X` thresholds (p.14).**
- **Lemma 5** (p.15) — **NOT PREVIOUSLY IN THE EXTRACT AT ALL.** Let `S` be as in §2. For `𝒥 ⊆ {1,…,J}`, let
  `g_𝒥` be the completely multiplicative function
  `g_𝒥(p^j) = 1 if p ∉ ⋃_{j∈𝒥}[P_j,Q_j]; 0 otherwise.` Then
  `Σ_{X≤n≤2X, n∈S} a_n = Σ_{X≤n≤2X} a_n Π_{j=1}^{J}(1 − g_{{j}}(n)) = Σ_{𝒥⊆{1,…,J}} (−1)^{#𝒥} Σ_{X≤n≤2X} g_𝒥(n)a_n`.
  Stated as "an immediate consequence of the inclusion–exclusion principle" (p.14 bottom); no proof given.
  Also consumed at **p.28** (§8.3, "by Lemmas 3 and 5 (since `2^J ≪ (log X)^{o(1)}`)").
  ⚠ **Source notation collision (not a rendering ambiguity):** MR reuse the letter `j` for both the exponent in
  `p^j` and the index in `⋃_{j∈𝒥}`. The rendering is crisp; the collision is the authors'. The exponent is
  immaterial (`g` is completely multiplicative), the index is the live one.

### 6.3 Theorem 1 from Theorem 3 (pp.30–31) — the deduction

**(a) Splitting off `n ∉ S`** (p.30, unnumbered):

> `|(1/h)Σ_{x≤n≤x+h}f(n) − (1/X)Σ_{X≤n≤2X}f(n)| ≤ |(1/h)Σ_{x≤n≤x+h,n∈S}f(n) − (1/X)Σ_{X≤n≤2X,n∈S}f(n)| + (1/h)Σ_{x≤n≤x+h, n∉S}1 + (1/X)Σ_{X≤n≤2X, n∉S}1`

**(b) The count identity** (p.30, unnumbered) — how the *short*-interval `n ∉ S` count is traded for a *long*-interval one:

> `(1/h)Σ_{x≤n≤x+h, n∉S}1 = 1 + O(1/h) − (1/h)Σ_{x≤n≤x+h, n∈S}1`
> `= (1/X)Σ_{X≤n≤2X, n∉S}1 + (1/X)Σ_{X≤n≤2X, n∈S}1 + O(1/h) − (1/h)Σ_{x≤n≤x+h, n∈S}1`

**(c) The resulting four-term bound** (p.30, unnumbered) — note the coefficient **2**:

> `|(1/h)Σ_{x≤n≤x+h}f(n) − (1/X)Σ_{X≤n≤2X}f(n)| ≤ |(1/h)Σ_{n∈S}f(n) − (1/X)Σ_{n∈S}f(n)| + |(1/h)Σ_{x≤n≤x+h,n∈S}1 − (1/X)Σ_{X≤n≤2X,n∈S}1| + (2/X)Σ_{X≤n≤2X, n∉S}1 + O(1/h)`

**(d) Two applications of Theorem 3, at `f` and at `1`** (p.30): *"Theorem 3 applied to `f(n)` and to `1` implies
that the first and second terms are both at most `δ/100` with at most"*

> (27) `≪ X(log h)^{1/3}/(P₁^{1/6−η}δ²) + X/((log X)^{1/50}δ²)`

*"exceptions."* — **[DERIVED]** the `δ²` is Chebyshev on the mean-square at threshold `δ/100` (the `100²`
absorbed into `C`); the `X` is the measure normalisation of `(1/X)∫_X^{2X}`.

**(e) The fundamental lemma of the sieve** (p.31, unnumbered display) — *"for all large enough `X`"*:

> `Σ_{X≤n≤2X, n∉S} 1 ≤ (1 + 1/100) X Σ_{j≤J} Π_{P_j≤p≤Q_j}(1 − 1/p) ≤ (1 + 1/100) X Σ_{j≤J} log P_j/log Q_j`

**NEW: the explicit `(1 + 1/100)` sieve constant and the Mertens step `Π_{P_j≤p≤Q_j}(1−1/p) ≤ log P_j/log Q_j`.**
§1's Def-of-S block (:41) records only the p.6 heuristic form; this is the rigorous p.31 form the glue uses.
Source ref: **[8, Thm 6.17]** (Friedlander–Iwaniec) per §3's table.

**(f) The assembled bound** (p.31):

> (28) `|(1/h)Σ_{x≤n≤x+h}f(n) − (1/X)Σ_{X≤n≤2X}f(n)| ≤ δ/50 + (2 + 1/50) Σ_j log P_j/log Q_j`
> with at most (27) exceptions.

⚠ The parenthesised factor is `(2 + 1/50)` — **read twice**; the text layer flattens this into a bare `2 +`
followed by a stacked `1/50`, which invites the misreading `δ/50 + 2 + (1/50)Σ…`. **The rendered page shows
`(2 + 1/50)` as a single displayed factor multiplying the sum.** (`2` from (c)'s `2/X` term, `1/50` from the
`(1+1/100)` doubled.)

### 6.4 THE CASE SPLIT AND THE TWO PARAMETER SETS (p.31) — the door-road payload

*"To deduce Theorem 1 we pick an appropriate sequence of intervals `[P_j, Q_j]`."* The threshold is
**`h ⋛ exp((log X)^{1/2})`** — confirmed verbatim, twice, p.31. `P_j` and `Q_j` are **as in (4)** in both cases.

| | **SMALL-h case** | **LARGE-h case** |
|---|---|---|
| condition | `h ≤ exp((log X)^{1/2})` | `h > exp((log X)^{1/2})` |
| `η` | `1/150` | `1/150` |
| `Q₁` | `h` | `exp((log X)^{1/2})` |
| `P₁` | `max{h^{δ/4}, (log h)^{40/η}}` | `Q₁^{δ/4}` |
| `P_j, Q_j` (`j ≥ 2`) | as in (4), p.6 | as in (4), p.6 |
| side condition | — (the `max` enforces `P₁ ≥ (log Q₁)^{40/η}` outright) | *"we can assume `δ ≥ (log X)^{−1/100}`, so that `P₁ ≥ (log Q₁)^{40/η}`"* |
| (28) evaluates to | `δ + 20000·loglog h/log h` | `δ` |
| exceptions | "as claimed" (= Thm 1's set) | "as claimed" |
| **door road** | **THIS IS OUR CASE** | **RETIRED** |

Byte-verbatim, p.31: *"In case `h ≤ exp((log X)^{1/2})`, we choose `η = 1/150, Q₁ = h, P₁ = max{h^{δ/4}, (log h)^{40/η}}`
and `P_j` and `Q_j` as in (4). With this choice the expression in (28) is at most `δ+20000 loglog h/log h` and the
number of exceptions is as claimed."* / *"In case `h > exp((log X)^{1/2})`, we choose `η = 1/150, Q₁ = exp((log X)^{1/2}),
P₁ = Q₁^{δ/4}` and `P_j` and `Q_j` as in (4). This is a valid choice since we can assume `δ ≥ (log X)^{−1/100}`,
so that `P₁ ≥ (log Q₁)^{40/η}`. With this choice the expression in (28) is at most `δ` and the number of
exceptions is as claimed."*

**Notes.** (i) `δ` **does** appear in `P₁`, in both cases, as `(·)^{δ/4}`. (ii) There is exactly **one** `δ` in
the paper — Theorem 1's, not a second sieve-δ. (iii) `η = 1/150 ∈ (0,1/6)` ✓ (Theorem 3's hypothesis, p.7).
(iv) The `(log Q₁)^{40/η}` shape is inherited verbatim from **p.6's admissibility example**:
*"given `0 < η < 1/6` choose any `[P₁,Q₁]` with `exp(√(log X)) ≥ Q₁ ≥ P₁ ≥ (log Q₁)^{40/η}` large enough"* —
so in the small-h case `Q₁ = h` turns `(log Q₁)^{40/η}` into `(log h)^{40/η}`. **This p.6 constraint is NEW to
the extract** (§1 :38–41 records `Q₁ ≤ exp(√log X)`, (2), (3), (4), `J` — but not `P₁ ≥ (log Q₁)^{40/η}`).
(v) The small-h case's `Q₁ = h` is exactly the extremal choice permitted by Theorem 3's `[P₁,Q₁] ⊂ [1,h]`.

**[DERIVED, marked as derivation — not paper text]**

- `40/η = 40·150 = **6000**` at `η = 1/150`. So `P₁ ≥ (log h)^{6000}` in the small-h case.
- The `j = 1` term of (28)'s sum is `log P₁/log Q₁ = log P₁/log h`, which is `δ/4` when the `max` is `h^{δ/4}`,
  and `6000·loglog h/log h` when it is `(log h)^{6000}`. Hence (28) `≤ δ/50 + (2+1/50)(δ/4) + (2+1/50)·6000·loglog h/log h
  + tail` — the `δ` part is `δ(1/50 + 0.5125) ≈ 0.53δ ≤ δ`, and `(2+1/50)·6000 = 12120 ≤ 20000 = C′`, the slack
  covering `Σ_{j≥2} log P_j/log Q_j`. **This is the arithmetic origin of `C′ = 20000` (p.2).**
- Large-h validity: `log Q₁ = (log X)^{1/2}`, `log P₁ = (δ/4)(log X)^{1/2}`; need `≥ 6000·log((log X)^{1/2})
  = 3000 loglog X`. With `δ ≥ (log X)^{−1/100}`: LHS `≥ (1/4)(log X)^{49/100} ≫ 3000 loglog X`. ✓
- **Why `δ ≥ (log X)^{−1/100}` is free:** if `δ < (log X)^{−1/100}` then `δ² < (log X)^{−1/50}`, so (27)'s second
  term exceeds `X` and Theorem 1's exceptional set is `≥ CX` — vacuous. (MR say only "we can assume".)

### 6.5 🔴 THE `h^{δ/25}` CROSS-CHECK — VERDICT: **EXACT AGREEMENT, NO DISCREPANCY**

The corrected row at :27 / :236 reads `CX((log h)^{1/3}/(δ²h^{δ/25}) + 1/(δ²(log X)^{1/50}))`, `C′ = 20000`.
Re-read from **p.1 (Theorem 1 statement) and p.2 (the displayed exceptional set)** this session:

> `|(1/h)Σ_{x≤n≤x+h}f(n) − (1/X)Σ_{X≤n≤2X}f(n)| ≤ δ + C′ loglog h/log h`
> for all but at most `CX((log h)^{1/3}/(δ²h^{δ/25}) + 1/(δ²(log X)^{1/50}))` integers `x ∈ [X,2X]`.
> One can take `C′ = 20000`. (p.1–2, `2 ≤ h ≤ X`, `δ > 0`, `C, C′ > 1` absolute.)

**AGREES byte-for-byte with :27/:236** — numerator `(log h)^{1/3}`, denominator `δ²h^{δ/25}`; second term
`1/(δ²(log X)^{1/50})`; `C′ = 20000`. **No discrepancy.**

**Where `h^{δ/25}` enters — the exact derivation, now grounded end-to-end:** (27) has `P₁^{1/6−η}`. At `η = 1/150`,
`1/6 − η = 25/150 − 1/150 = 24/150 = **4/25**` **exactly**. The small-h case takes `P₁ ≥ h^{δ/4}`, so
`P₁^{1/6−η} ≥ h^{(δ/4)·(4/25)} = **h^{δ/25}**`. The `4` in `P₁ = max{h^{δ/4}, …}` and the `4/25` from `η = 1/150`
cancel exactly — `δ/25` is not a rounded constant. **This closes the loop (27) → Theorem 1's exceptional set.**
Likewise `(log h)^{1/3}` passes through unchanged from (27), which inherits it from Theorem 3's `(log h)^{1/3}`
(p.7), which inherits it from Prop 1's `(log Q₁)^{1/3}` at `Q₁ = h ≤ h` (p.23). **Chain verified, no gaps.**

**[DERIVED — door-road sanity]** with `h = O(log X)` the exceptional set is
`CX((loglog X)^{1/3}/(δ²(log X)^{δ/25}) + 1/(δ²(log X)^{1/50})) = o(X)` for fixed `δ > 0` ✓. Note the `max` in `P₁`
resolves to `h^{δ/4}` only once `h^{δ/4} ≥ (log h)^{6000}`; for `h ≍ log X` and fixed `δ` this needs
`(log X)^{δ/4} ≥ (loglog X)^{6000}`, true for `X > X(δ)` but with a `δ`-dependent threshold. **Flag for the
door road: the `X(δ)` threshold here is large and must be carried, not assumed away.**

### 6.6 What §9 consumes from earlier sections that §1–§5 did not record

| item | where consumed | statement | page/eq |
|---|---|---|---|
| **Lemma 5** (incl.–excl. for `n ∈ S`) | (26) in §9; §8.3 p.28 | `Σ_{n∈S} a_n = Σ_{𝒥⊆{1,…,J}} (−1)^{#𝒥} Σ g_𝒥(n)a_n` | **p.15** (new) |
| `P₁ ≥ (log Q₁)^{40/η}` admissibility | §9 both cases (`(log h)^{40/η}`) | `exp(√(log X)) ≥ Q₁ ≥ P₁ ≥ (log Q₁)^{40/η}` | **p.6** (new) |
| fundamental lemma, explicit constant | §9 (e), p.31 | `≤ (1+1/100) X Σ_{j≤J} Π_{P_j≤p≤Q_j}(1−1/p)` | **p.31** (new) |
| Mertens step | §9 (e) | `Π_{P_j≤p≤Q_j}(1−1/p) ≤ log P_j/log Q_j` | **p.31** (new) |
| per-`j` complement density (with `j²`) | §2 / §9 (e) | `X log P_j/log Q_j`, `= X log P₁/(j² log Q₁)` under (4) | **p.6** (refines :41) |
| typical-density remark (MR's analogue of MRT Lemma 2.2) | §2 motivation only; **not** load-bearing in §9 | a typical integer has about `log(log Q_j/log P_j) = 2 log j + loglog Q₁ − loglog P₁` distinct prime factors in `[P_j,Q_j]` | **p.6** (new) |
| `H_j` (the §8 block width) | §8.1–8.2, feeds Prop 1 | `H_j := **j²**·P₁^{1/6−η}/(log Q₁)^{1/3}` | **p.24** (new) |
| `P_j ≥ P₁^{j²}` (from (3)) | §8.1 collection | used to sum `Σ_j (1/H_j + 1/P_j) ≪ (log Q₁)^{1/3}/P₁^{1/6−η}` | **p.25** (new) |
| `𝒥_j` / `I_j` index range | §8 | `I_j := {v : ⌊H_j log P_j⌋ ≤ v ≤ H_j log Q_j}` | p.24 (matches :72) |
| Lemma 4's inner constants | Lemma 4 proof | `|t_f| ≤ 1/100`; `𝔻(f,p^{it_f};X)² < (1/3)loglog X`; `(1 − 2/π − o(1))loglog X` | **p.14** (new) |

⚠ **On "MRT Lemma 2.2 / typical density":** MR's §9 does **not** use a density lemma of that shape. Its
`n ∉ S` accounting is entirely (e) — the fundamental lemma of the sieve at p.31. The p.6 "typical integer has
about `2 log j + loglog Q₁ − loglog P₁` prime factors" sentence is **motivational only**; nothing in §9 cites
it. **The door road needs the sieve bound, not a typical-density lemma.** (MRT's Lemma 2.2 is a different
paper's node — see `mrt_extract.md`.)

**[DERIVED] why `[P₁,Q₁] ⊂ [1,h]` is the load-bearing hypothesis:** Step 1 applies Prop 1 at `T = X/h₁ = X/h`,
whose prefactor is `(T/(X/Q₁) + 1) = (Q₁/h + 1)`. `Q₁ ≤ h` makes this `O(1)`. The Lemma 14 max-term
`max_{T≥X/h}(X/h)/T ∫_{1+iT}^{1+i2T}` likewise collapses: `((X/h)/T)(2TQ₁/X + 1) ≪ Q₁/h + (X/h)/T ≪ 1`.
Both collapses need exactly `Q₁ ≤ h`. In §9's small-h case `Q₁ = h` saturates it.

### 6.7 SPOT-VERIFY ADDENDUM (2026-07-25) — §2.6 and §2.7 re-read against the PDF

Requested independent re-verification. **No existing row edited; verdicts recorded here.**

**§2.6 Lemma 14 (:120–123) and ledger row (:246) vs p.21 — ✅ AGREE, byte-for-byte.** All six components
re-read from the rendered page: `|a_m| ≤ 1` ✓ · `1 ≤ h₁ ≤ h₂ = X/(log X)^{1/5}` ✓ · `S_j(x) = Σ_{x≤m≤x+h_j} a_m`
for `X ≤ x ≤ 2X` ✓ · `A(s) := Σ_{X≤m≤4X} a_m/m^s` ✓ · LHS `(1/X)∫_X^{2X}|(1/h₁)S₁(x) − (1/h₂)S₂(x)|² dx` ✓ ·
RHS `≪ 1/(log X)^{2/15} + ∫_{1+i(log X)^{1/15}}^{1+iX/h₁}|A(s)|²|ds| + max_{T≥X/h₁} (X/h₁)/T ∫_{1+iT}^{1+i2T}|A(s)|²|ds|` ✓.
The `2/15` exponent is confirmed independently by the proof (p.22): the `U`-part is `≪ T₀²·(x/X)(h₂/X)
= (log X)^{2/15−1/5} = (log X)^{−1/15}` pointwise, squared → `(log X)^{−2/15}`. **Internally consistent.**

**§2.7 rows (:127–135) vs pp.24–29 — ✅ ALL AGREE.** eq (20) `α_j = 1/4 − η(1 + 1/(2j))` p.24 ✓ ·
`[T₀,T] = ⋃_{j=1}^J 𝒯_j ∪ 𝒰`, `T₀ = (log X)^{1/15}` p.24 ✓ · eq (24) p.25 ✓ · §8.1 `E₁ ≪ (T/(X/Q₁)+1)(log Q₁)^{1/3}/P₁^{1/6−η}`
p.25 ✓ · `ℓ_{j,r} = ⌈(v/H_j)/(r/H_{j−1})⌉` p.26 ✓ · `E_j ≪ (T/X+1)/(j²P₁)` p.27 ✓ · §8.3 `P = exp((log X)^{1−1/48})`,
`Q = exp(log X/(log log X))`, `H = (log X)^{1/48}` p.27 ✓ · `∫_𝒰 ≪ (T/X+1)(log X)^{−1/48+o(1)}` p.29 ✓.
Also re-verified in passing: §2.5 Lemma 13 (:112–114, :245) `ℓ = ⌈log Y₂/log Y₁⌉`, `≪ (T/X + 2^ℓ Y₁)(ℓ+1)!²`,
`g(p^k) = (k+1)` on `[Y₁,2Y₁]` and `1` otherwise, Shiu (18) `Σ_{Y≤n≤2Y} g(n)² ≪ Y Π_{p≤Y}(1 + (|g(p)|²−1)/p) ≪ Y`
— p.20–21 ✅ AGREE. §2.3 Lemmas 6, 7, 8 p.15 ✅ AGREE. §2.2 `𝒰` measure `O(T^{1/2−ε})` p.8 ✅ AGREE (the
rigorous §8.3 form is `|𝒯| ≪ T^{1/2−η}X^{o(1)}`, p.28 — `η` there, `ε` on p.8; both as printed).

**Three NITS (not defects; no action required, recorded for completeness):**
1. :58 writes `1/4 − (3/2)η ≤ α₁ ≤ … ≤ α_J ≤ 1/4 − η`. p.24 has `1/4 − (3/2)η **=** α₁ ≤ α₂ ≤ … ≤ α_J ≤ 1/4 − η`.
   A weakening (`≤` for `=`), harmless but the equality is the sharper fact.
2. :41 records the `S`-complement density as `X·log P₁/log Q₁`. p.6 gives it **per `j`** as `X log P_j/log Q_j`,
   `= X log P₁/(j² log Q₁)` under choice (4). The dropped `j²` is what makes `Σ_j` converge (`Σ 1/j² = π²/6`);
   the summed statement at :41 is right, but the `j²` is the mechanism.
3. §2.7 does not record `H_j` (p.24), `P_j ≥ P₁^{j²}` (p.25), or §8.4's summation range `Σ_{2≤j≤J−1}` (p.29,
   printed `J−1`, not `J`). Supplied in §6.6 above.

### 6.8 AMBIGUITIES FLAGGED (this transcription)

1. **⚠ TEXT-LAYER TRAP, not a source ambiguity — `H_j` (p.24).** `pdftotext` renders
   `H_j := j²·P₁^{1/6−η}/(log Q₁)^{1/3}` in an order that reads as `2^j·P₁^{…}`. **The rendered page is
   unambiguous: it is `j²`.** Same trap at p.25 (`P_j ≥ P₁^{j²}`, not `P₁^j`) and p.25 (`H₁²log Q₁·P₁^{−1/2+3η}`,
   the square on `H₁` lost in the text layer). Any future extraction from this PDF must use the rendered page.
2. **⚠ `(2 + 1/50)` in (28) (p.31).** Text layer invites `δ/50 + 2 + (1/50)Σ`; rendered page shows the factor
   `(2 + 1/50)` multiplying `Σ_j log P_j/log Q_j`. Read twice; the parenthesised form is correct.
3. **⚠ `j` reused in Lemma 5 (p.15).** `g_𝒥(p^j)` exponent vs `⋃_{j∈𝒥}` index — the authors' collision, crisp
   in the rendering. Immaterial (complete multiplicativity) but a Lean port must not alias them.
4. **⚠ `q` vs `p` as the prime variable (p.24).** `Q_{v,H_j}(s) := Σ_{P_j≤q≤Q_j, e^{v/H_j}≤q≤e^{(v+1)/H_j}} f(q)/q^s`
   uses `q`, while eq (6) (p.8) and Lemma 12 use `p`. Same object; cosmetic.
5. **No ambiguity anywhere in §9's parameter displays (p.31).** `η = 1/150`, `Q₁ = h`,
   `P₁ = max{h^{δ/4}, (log h)^{40/η}}`, `Q₁ = exp((log X)^{1/2})`, `P₁ = Q₁^{δ/4}`, `δ ≥ (log X)^{−1/100}`,
   `δ + 20000 loglog h/log h`, and the threshold `h ⋛ exp((log X)^{1/2})` are all crisp in both reads.
