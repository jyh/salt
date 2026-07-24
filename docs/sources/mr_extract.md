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
