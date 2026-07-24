# MRT extraction — arXiv:1503.05121v3 (Matomäki–Radziwiłł–Tao, "An averaged form of Chowla's conjecture")

**Node:** MR-STAGE (source extraction, no Lean). **Source:** `docs/sources/1503.05121v3.pdf`
(32 pp, arXiv v3, 1 Mar 2022 timestamp; LaTeX text layer — clean extraction, no scanned-image OCR).
This is Tao's **[17]** (chowla.txt:1529, MRTDoor.lean:9). The MR paper 1501.04585 is its **[17]→[17-internal]** ref;
inside THIS paper the MR paper is cited as **[17]** as well (MRT refs, p.32: "[17] Kaisa Matomäki and Maksym
Radziwiłł. Multiplicative functions in short intervals. Ann. of Math. 183(3):1015–1056, 2016").

**Labels:** GROUNDED (page/eq read this session) is the default; every statement below carries a page ref.
Where the PDF text layer is ambiguous it is flagged **⚠ FLAG** loudly (per the Benli rounded-constant
cautionary tale, flags.md wf1 / the 2026-07-18 F1 entry: a rounded/mis-scaled constant can hide a power-of-Q
defect — so every exponent here is transcribed verbatim and the one genuine ambiguity is called out).

---

## 0. THE A-ARM RESOLUTION (the top deliverable — stated plainly first)

**The freeze's open risk (mr-freeze.md:38, OPEN RISKS):** "[17] A-arm reading (MRT quality-fixed vs
quality ≥ W) unresolved". S10b shipped a dual channel: *quality-fixed → Hlo-floor arm*;
*quality ≥ W → g triple-exp arm*. **This extraction resolves it.**

**VERDICT: NEITHER label is literally correct. The required non-pretentiousness LEVEL is
`M ≥ 3 log W = 15 loglog H` (Thm 2.3 / Prop 2.4), or NO threshold at all for λ (Thm A.1). The modulus
RANGE is `Q = W` (grows). The discharge rides entirely on MRT's OWN structural hypothesis
`W ≤ (log X)^{1/125}` plus region coefficient `c ≥ 3/125 ≈ 0.024` — i.e. the Hlo-floor channel, and
it can be SIMPLIFIED (no separate floor needed). The g-triple-exp arm is DEAD (not needed).**

**ADDENDUM (CHI-CHECK 2026-07-24) — "DEAD" was scoped too broadly; softening the verdict.**
The declaration above is retained as written, but its scope must be read as: dead *for the region
route*. The triple-exp arm is NOT dead in general — it is the price of **Route A's H1**. The
k-th-power route to the χ-twisted quality floor buys its floor at the cost of an x-floor,
`loglog X ≥ 240 (log H)^{10} loglog H`, which is a one-sided condition and is free in the regime
we work in. So the arm is alive as a *paid* channel, not a discarded one. (`chi_floor_of_order`
landed 2026-07-25, `Salt/MR/ChiFloor.lean` — the H1 exit that consumes it.)

### 0.1 The two quality quantities (GROUNDED, p.4, eq (1.6) and the M(g;X,Q) definition)

- `M(f; X) := inf_{|t|≤X} 𝔻(f, n↦n^{it}; X)²`  — **NO character** (modulus 1), heights `|t| ≤ X` (the
  interval scale). This is (1.6), p.4. Appears in **Theorem A.1 / A.2**.
- `M(g; X, Q) := inf_{q≤Q; χ mod q} M(gχ̄; X) = inf_{|t|≤X; q≤Q; χ mod q} 𝔻(g, χ·n^{it}; X)²` — **character
  modulus range `q ≤ Q`**, heights `|t| ≤ X`. p.4. Appears in **Theorem 2.3 / Prop 2.4 / Prop 5.3 / Thm 1.6/1.7**.
- `𝔻(f,g;X)² := Σ_{p≤X} (1 − Re(f(p)ḡ(p)))/p` (the pretentious distance, p.4).

**KEY: heights are `|t| ≤ X` = the SHORT-INTERVAL scale, NOT the outer scale.** This is a DIFFERENT, and
strictly EASIER, non-pretentiousness consumption than Tao's hypothesis (1.6), whose heights are `|t| ≤ Ax`
at the outer scale x (GROUNDED chowla.txt:214). The freeze's **S5** (heights `|t| ≤ Qx`) serves Tao's (1.6);
the MRT-internal M above is a separate, smaller-height consumption. Do not conflate them.

### 0.2 The requirement shape (GROUNDED)

- **Theorem A.1 (p.20)** — the surface Route M / S9 actually consumes for λ (see §3, and the license
  chowla.txt:743–750, §0.4 below): **there is NO quality-threshold hypothesis at all.** The bound
  `(1/X)∫_X^{2X}|(1/h)Σ f(n)|² dx ≪ exp(−M(f;X))·M(f;X) + (loglog h)²/(log h)² + 1/(log X)^{1/50}` holds for
  **any** 1-bounded multiplicative f. Quality `M(f;X)` appears only in the CONCLUSION's error term. So the
  "quality" needed is merely `M(f;X) → ∞` at ANY rate — the landed region's `(1/4)loglog X → ∞` suffices.
- **Theorem 2.3 (p.9) / Prop 2.4 (p.10) / Prop 5.3 (p.17)** — the full Route-F surface: hypothesis
  `W ≤ exp(M(g;X,Q)/3)`, i.e. **`M(g;X,Q) ≥ 3 log W`**. The required LEVEL is `3 log W`. With `W = log⁵ H`
  (Tao's Prop 2.4 choice, chowla.txt:624), `3 log W = 15 loglog H` — **logarithmic in W, NOT W-grade.**

The faithful R5 worry (mr-freeze.md:5, "quality log⁵ Hhi ≫ (1/4)loglog x") **conflated the modulus RANGE
`Q = W = log⁵ H` with the required LEVEL `3 log W = 15 loglog H`** — the latter is a factor `≈ (log H)⁴/15`
smaller. That is the whole error.

### 0.3 The discharge arithmetic (airtight, all at interval scale X)

Requirement (Thm 2.3, taking Q = W per §0.5): `M(λ;X,W) ≥ 3 log W`.
Region delivery (θ=3/4): `M(λ;X,W) ≥ (1/4 − ε) loglog X`. [MRT's own (1.12), p.6, gives `(1/3 − ε)loglog X`
for the VK θ=2/3 region; our landed `zeta_zero_free_region_pow` θ=3/4 gives coefficient 1/4.]
`W = (log H)^k`, Tao uses k = 5. MRT's OWN hypothesis (Thm 2.3, p.9): `W ≤ (log X)^{1/125}`.

  `W ≤ (log X)^{1/125}` ⟺ `k·loglog H ≤ (1/125)loglog X` ⟺ `loglog H ≤ (1/(125k))·loglog X`.
  Binding case (H as large as allowed): `3 log W = 3k·loglog H ≤ (3k/(125k))·loglog X = (3/125)·loglog X`.
  **The `k` CANCELS.** So requirement reduces to `c·loglog X ≥ (3/125)·loglog X`, i.e. **`c ≥ 3/125 ≈ 0.024`.**

Our region `c = 1/4 = 0.25` ≥ 0.024 → **margin ~10.4×**. (MRT's own `c = 1/3`; even the anchor-only bridge
`c = 3/16 = 0.1875` of map-#1 N1 gives 7.8× margin.) **The A-arm discharge is automatic given
`W ≤ (log X)^{1/125}` (which the port must enforce anyway) and any region coefficient `> 3/125`.**

### 0.4 Why Theorem A.1 (not Lemma 2.2 + Thm 2.3) for λ — GROUNDED chowla.txt:743–750

Tao, verbatim (chowla.txt:745–750): "in the Liouville case g₁ = g₂ = λ, we have c_p = 1. This leads to some
minor simplification … we only need to apply Proposition 2.4 for 'major arc' values of α, allowing one to
replace [17, Lemma 2.2, Theorem 2.3] by the simpler [17, **Theorem A.1**]". → **Route M/S9 consumes
Theorem A.1.** Theorem A.1 has no character (modulus 1) and no quality threshold. The character-bearing
Theorem 2.3 (and Q = W) is Route F's surface.

### 0.5 ⚠ FLAG — Theorem 2.3 writes `M(g;X,Q)`, but Q is undefined in its statement

Theorem 2.3 (p.9) hypothesis reads `W ≤ exp(M(g;X,Q)/3)`, yet **Q is not defined in the theorem
statement.** Proposition 2.4 (p.10), from which Thm 2.3 is *deduced* (p.10, "we will deduce Theorem 2.3
from Proposition 2.4"), writes `W ≤ exp(M(g;X,**W**)/3)`. Proposition 5.3 (p.17) likewise uses
`M(g;X,W)`. The top-level Theorems 1.6/1.7 define `Q := min(log^{1/125}X, log^{20}H)` (1.6) resp.
`min(log^{1/125}X, log⁵H)` (1.7); Prop 5.1 (p.16) carries this top-level Q. In the regime where Thm 2.3/
Prop 5.1 validly apply, the hypothesis `W ≤ (log X)^{1/125}` forces `log^{power}H ≤ log^{1/125}X`, hence
`Q = min(log^{1/125}X, log^{power}H) = W`. **RESOLUTION: throughout the workhorse chain Q = W; treat the "Q"
in Thm 2.3 as W (either a typographical carry from Prop 5.1's top-level Q, or an intentional free parameter
instantiated to W).** Confidence: high on the arithmetic (Q ≤ W in-regime, so `M(g;X,W) ≤ M(g;X,Q)`, and
Q = W exactly when the hypotheses bind); the only unresolved point is whether the printed "Q" is a typo.
This does NOT change the A-arm verdict (the required level is `3 log W` either way).

---

## 1. MAIN THEOREMS (exact statements, GROUNDED)

- **Theorem 1.1** (Chowla on average), p.2: for any k, `10 ≤ H ≤ X`,
  `Σ_{1≤h₁,…,h_k≤H} |Σ_{1≤n≤X} λ(n+h₁)···λ(n+h_k)| ≪ k(loglog H/log H + 1/log^{1/3000}X) H^k X`. (1.2)
  Slightly stronger (1.3): the `k=1` factor `λ(n)` split off, `H^{k−1}X`.
- **Theorem 1.2** (k=2 refined), p.2: for fixed `δ ∈ (0,1]`, ∃ fixed `H=H(δ)` s.t. for all large X,
  `|Σ_{1≤n≤X} λ(n)λ(n+h)| ≤ δX` for all but at most **`H^{1−δ/5000}`** integers `|h| ≤ H`. (1.4)
- **Theorem 1.3** (exponential sum), p.3: for `10 ≤ H ≤ X`,
  `sup_{α∈ℝ} ∫_0^X |Σ_{x≤n≤x+H} λ(n)e(αn)| dx ≪ (loglog H/log H + 1/log^{1/700}X) HX`.
- **Lemma 1.4** (Fourier identity), p.3: `∫_𝕋 (∫_ℝ|Σ_{x≤n≤x+H}f(n)e(αn)|² dx)² dα = Σ_{|h|≤H}(H−|h|)²|Σ_n f(n)f̄(n+h)|²`.
- **Theorem 1.6** (Elliott on average), p.5: `10 ≤ H ≤ X`, `A ≥ 1`; `g_1,…,g_k` 1-bounded, `a_j ≤ A`,
  `b_j ≤ AX`; `g_{j₀}` multiplicative. Then `Σ_{h}|Σ_n Π_j g_j(a_jn+b_j+h_j)| ≪ A²k(exp(−M/80) + loglog H/log H
  + 1/log^{1/3000}X)H^k X` where **`M := M(g_{j₀}; 10AX, Q)`**, **`Q := min(log^{1/125}X, log^{20}H)`**. (1.10)
- **Theorem 1.7** (exp sum, general g), p.6: `X ≥ H ≥ 10`, g 1-bounded mult.
  `sup_α ∫_0^X|Σ_{x≤n≤x+H}g(n)e(αn)|dx ≪ (exp(−M(g;X,Q)/20) + loglog H/log H + 1/log^{1/700}X)HX`,
  **`Q := min(log^{1/125}X, log⁵H)`**.
- **(1.12)** (the λ-instantiation of M, GROUNDED p.6): for `g = λ`,
  `M ≥ inf_{|t|≤X; q≤Q; χ} Σ_{exp((log X)^{2/3+ε})≤p≤X} (1 + Re χ(p)p^{it})/p ≥ (1/3 − ε)loglog X + O(1)`,
  "established via standard methods from the Vinogradov–Korobov type zero-free region
  `{σ+it : σ > 1 − c/max{log q, (log(3+|t|))^{2/3}(loglog(3+|t|))^{1/3}}}` for `L(s,χ)`, which applies since
  χ has conductor `q ≤ (log X)^{1/125}` (so that there are no exceptional zeros), see [20, §9.5]." **The 1/125
  provenance: no-exceptional-zero window for L(s,χ). Coefficient 1/3 = 1 − 2/3 (θ=2/3 VK); our θ=3/4 → 1/4.**
  "our arguments make no use of exceptional zeroes, all the implied constants in our theorems are effective."

---

## 2. THE PROP-2.4-RELEVANT CHAIN — Lemma 2.2, Theorem 2.3, Prop 2.4 (exact quantifiers = the A-arm)

### 2.1 The typical-factorization set (Def 2.1, p.8; = MR Def §2)

`10 < P₁ < Q₁ ≤ X`, `√X ≤ X₀ ≤ X`, `Q₁ ≤ exp(√(log X₀))`. For `j > 1`:
`P_j := exp(j^{4j}(log Q₁)^{j−1} log P₁)`, `Q_j := exp(j^{4j+2}(log Q₁)^j)`. Intervals `[P_j,Q_j]` disjoint,
increasing; `P₁ < Q₁ < exp(2⁸ log Q₁ log P₁) = P₂`. `J` = largest j with `Q_J ≤ exp((log X₀)^{1/2})`.
`S_{P₁,Q₁,X₀,X}` = integers `1 ≤ n ≤ X` with a prime factor in each `[P_j,Q_j]`, `1 ≤ j ≤ J`.

### 2.2 Lemma 2.2 (density; NO quality parameter), p.8–9 — GROUNDED

> `10 < P₁ < Q₁ ≤ X`, `√X ≤ X₀ ≤ X`, `Q₁ ≤ exp(√(log X₀))`. Then for every large enough X,
> `#{1 ≤ n ≤ X : n ∉ S_{P₁,Q₁,X₀,X}} ≪ (log P₁ / log Q₁)·X`.

**Quantifier structure: a pure SIEVE-DENSITY lemma. No `M`, no quality, no non-pretentiousness.** Proof
(p.9): fundamental lemma of sieve theory ([8, Thm 6.17] = Friedlander–Iwaniec), `≪ X Π_{P_j≤p≤Q_j}(1−1/p)
≪ (log P_j/log Q_j)X`, sum over j. **This is not an A-arm input at all** — it bounds the density of the
complement of the typical set, consumed additively.

### 2.3 Theorem 2.3 (Key exponential sum estimate), p.9 — GROUNDED (the A-arm carrier)

> `X, H, W ≥ 10` with **`(log H)⁵ ≤ W ≤ min{H^{1/250}, (log X)^{1/125}}`**; `g` 1-bounded multiplicative with
> **`W ≤ exp(M(g;X,Q)/3)`** [Q = W in-regime, §0.5]. Set `S := S_{P₁,Q₁,√X,X}`, `P₁ := W^{200}`, `Q₁ := H/W³`.
> Then for any `α ∈ 𝕋`: `∫_ℝ |Σ_{x≤n≤x+H} 1_S(n)g(n)e(αn)| dx ≪ ((log H)^{1/4} loglog H / W^{1/4}) HX`. (2.2)

Quantifier structure of the quality hypothesis: **`M(g;X,Q) ≥ 3 log W`** (heights `|t| ≤ X`, modulus `q ≤ Q = W`).
Level = `3 log W`, logarithmic in W. Deduced from Prop 2.4 (p.10, Möbius-inversion off completely-mult g₁).

### 2.4 Proposition 2.4 (completely-mult version; Q = W EXPLICIT), p.10 — GROUNDED

> `X, H, W ≥ 10`, `(log H)⁵ ≤ W ≤ min{H^{1/250}, (log X)^{1/125}}`; `g` 1-bounded **completely** multiplicative
> with **`W ≤ exp(M(g;X,W)/3)`** (2.3); `d < W` natural. `S := S_{P₁,Q₁,√X,X/d}`, `P₁ = W^{200}`, `Q₁ = H/W³`.
> Then for any `α ∈ 𝕋`: `∫_ℝ |Σ_{x/d≤n≤x/d+H/d} 1_S(n)g(n)e(αn)| dx ≪ (1/d^{3/4})·((log H)^{1/4}loglog H/W^{1/4}) HX`. (2.4)

**Here `Q = W` is written out.** This is the ground truth for the A-arm: modulus range = W, required level = 3 log W.

### 2.5 Prop 5.3 (the k=2 core mean-square), p.17 — GROUNDED

> `log^{20}H ≤ W ≤ min{H^{1/250},(log X)^{1/125}}`; g 1-bounded mult, **`W ≤ exp(M(g;X,W)/3)`**; `S = S_{P₁,Q₁,√X,X}`,
> `P₁=W^{200}`, `Q₁=H/W³`. Then `Σ_{1≤h≤H}|Σ_n 1_S g(n) 1_S ḡ(n+h)|² ≪ HX²/W^{1/5}`. (5.5)

Again `Q = W`. Proof (p.18): Lemma 1.4 (Fourier) → Parseval → reduces to `sup_α ∫|Σ 1_S g e(αn)| dx ≪ HX/W^{1/5}`,
which "follows from Theorem 2.3 (using `W ≥ log^{20}H` to absorb the `log^{1/4}H loglog H` factors)."

### 2.6 The reduction ladder (GROUNDED, Section 5)

`Thm 1.6 ⟸ Prop 5.1 (p.16, truncated Elliott, `W ≤ exp(M(g_{j₀};10AX,Q)/3)`, Q top-level)
 ⟸ Prop 5.3 (k=2 core, Q=W) ⟸ Thm 2.3 ⟸ Prop 2.4`. Van der Corput reduces the k≥2 product to the k=2
mean-square (only `g_{j₀}` need be multiplicative, footnote 2 p.6). `Thm 1.7 ⟸ Thm 2.3` directly (p.9–10,
via `H₀ = min(log^{1/700}X loglog X, exp(M/20)M)`).

---

## 3. THEOREM A.1 / A.2 (the λ-major-arc surface) + proof sketch — GROUNDED, Appendix A (pp.20–28)

Appendix A "proves a complex variant of results in [17] [=the MR paper] in the case that f is not p^{it}
pretentious." It is the bridge into 1501.04585.

### 3.1 Theorem A.1, p.20 — GROUNDED (what Route M/S9 consumes)

> `f` 1-bounded multiplicative, `M(f;X)` as in (1.6). Then for `X ≥ h ≥ 10`:
> `(1/X) ∫_X^{2X} |(1/h) Σ_{x≤n≤x+h} f(n)|² dx ≪ exp(−M(f;X))·M(f;X) + (loglog h)²/(log h)² + 1/(log X)^{1/50}`.

**Remark (p.21): the factor `exp(−M(f;X))·M(f;X)` may be replaced by `exp(−M(f;X))`** (see Prop A.3 remark).
No quality threshold; character-free; heights `|t| ≤ X`. **Proof (p.28):**
`(1/X)∫|(1/h)Σ_{x≤n≤x+h}f|² dx ≤ (1/X)∫|(1/h)Σ_{n∈S}f|² dx + (1/X)∫|(1/h)Σ_{n∉S}1|² dx`; the first integral is
Theorem A.2; the second is the indicator, `≪` via **[17, Theorem 3 with f=1] and Lemma 2.2** (η=1/12,
P₁=(log h)^{480}, Q₁=h). → **Theorem A.1 = Theorem A.2 (main, with M) + MR-Theorem-3 (indicator, f≡1) + density Lemma 2.2.**

### 3.2 Theorem A.2, p.21 — GROUNDED (the M-quantitative core on the typical set)

> `f` 1-bounded mult, `S` typical-factorization set with `η ∈ (0,1/6)`, `[P₁,Q₁] ⊂ [1,h]`. For `X > X(η)`,
> `h ≥ 3`: `(1/X)∫_X^{2X}|(1/h)Σ_{x≤n≤x+h, n∈S}f(n)|² dx ≪ exp(−M(f;X))·M(f;X) + (log h)^{1/3}/P₁^{1/6−η} + 1/(log X)^{1/50}`.

Proof (p.21): "proceeds as the proof of [17, Theorem 3]. The first step is a Parseval bound
`(1/X)∫|(1/h)Σ_{n∈S}f|² dx ≪ ∫_1^{1+iX/h_1}|F(s)|²|ds| + max_{T≥X/h_1}(X/h_1)/T ∫_{1+iT}^{1+i2T}|F(s)|²|ds|`,
… same way as [17, Lemma 14] … Theorem A.2 follows from the following variant of [17, Proposition 1]" = Prop A.3.

### 3.3 Proposition A.3 + its correction, p.22 — GROUNDED (⚠ known published-proof error)

> `f` 1-bounded mult, `S` typical set, `η ∈ (0,1/6)`, `F(s) = Σ_{X≤n≤2X, n∈S} f(n)/n^s`. For `T ≥ 1`:
> `∫_{−T}^T |F(1+it)|² dt ≪ (T/(X/Q₁) + 1)·((log Q₁)^{1/3}/P₁^{1/6−η} + M(f;X)/exp(M(f;X)) + 1/(log X)^{1/50})`.

**⚠ FLAG (GROUNDED p.22 Remark):** "In the published version of the paper, the proof of this proposition is
**incorrect when M(f;X) grows very slowly with X**. The corrected proof that we provide here gives a slightly
stronger result with `exp(−M(f;X))` in place of `exp(−M(f;X))M(f;X)`. We state the result with the weaker
factor … to remain consistent with the published version." (This is the Fei Wei correction, acknowledged p.7.)
**The port MUST use the arXiv-v3 corrected proof (pp.22–28), NOT the Annals-published one.** The correction
lives in Lemmas A.4–A.8 (the T₀/T₁ split at `M(f;X) ≥ (1/8)loglog X`).

### 3.4 The Halász machinery of Appendix A (Lemmas A.4–A.8), pp.22–28 — GROUNDED

- Split `𝒯₀ := {|t|≤T : |t−t₁| ≤ (log X)^{1/16}}`, `𝒯₁ := {|t|≤T : |t−t₁| > (log X)^{1/16}}`, where `t₁`
  attains `M(f;X) = min_{|t|≤X}𝔻(f,n^{it};X)²` (p.22).
- **Lemma A.4** (p.22): `𝔻(fg_𝒥,p^{it};X)² ≥ ½𝔻(f,p^{it};X)²`; if `M(f;X)≥(1/8)loglog X` or `|t−t₁|>(log X)^{1/16}/2`
  then `𝔻(fg_𝒥,p^{it};X)² ≥ (1/6 − 1/3π − ε)loglog X`. (Granville–Soundararajan-style.)
- **𝒯₁ handled by Halász** (p.23): `𝔻(f g_𝒥, p^{it'};X)² ≥ (1/6 − 1/3π − ε)loglog X + O(1)` ⟹ (via
  **[10, Corollary 1 with T=(log X)^{1/16}/4]** = Granville–Soundararajan "Decay of mean values")
  `Σ_{X≤n≤2X} g_𝒥(n)f(n)n^{−it} ≪ X/(log X)^{1/6 − 1/3π − ε}`.
- **⚠ THE ζ VK REGION ENTERS HERE (GROUNDED p.23, eq A.5/A.6):** for `(log X)^{1/16}/2 ≤ |t−t₁| ≤ (log X)^{20}`,
  `𝔻(1,p^{it};X)² ≥ (1 − 2/π)log(log X/log Y) + O(1)` (Y = exp((log X)^{2/3+ε})); and **"when `|t−t₁| > (log X)^{20}`
  and `|t| ≤ X`, `(t−t₁)log p /2π` is equidistributed (mod 1) by the Erdős–Turán inequality and the
  Vinogradov–Korobov zero free region for ζ(s)"**, giving `𝔻(f,p^{it};X)² ≥ (1/3 − 2/3π − ε)loglog X` (A.6).
  → **the ONLY zero-free-region input in the MRT-appendix proof is the ζ (not L(s,χ)) VK region, at extreme t.**
- **Lemma A.5** (p.24): the `R`-polynomial Halász bound (the Buchstab-polynomial analogue), the "only part …
  that needed f to be real-valued" now removed by the complex extension.
- **Lemma A.6 → A.8** (pp.24–28): `𝒯₀` handled by "the method of the proof of Halász's theorem from **[9]**"
  (= Granville–Harper–Soundararajan, "A new proof of Halász's theorem"), with the multiplicative `s_𝒥, ℓ, Λ_ℓ`
  decomposition, the cosine inequality Lemma A.8 (`e^α+e^{−α}−2cos θ ≤ e^{√(α²+θ²)}`), yielding
  `U ≪ X/exp(M(f;X)/2) + X/(log X)^{1/2}` (p.28) ⟹ (A.7) ⟹ Prop A.3.

**Net: Appendix A re-proves the MR engine for complex non-pretentious f, with the `exp(−M(f;X))` factor,
using the ζ VK region at extreme t and Halász's theorem ([9],[10]).** This is the S9 / complex-extension surface.

---

## 4. THE MAJOR-ARC REDUCTION Route M rides (MRT Section 4, pp.14–16) — GROUNDED

Prop 2.4, major-arc case `q ≤ W` (Section 4). By Dirichlet approximation (p.11) every `α = a/q + θ`,
`(a,q)=1`, `q ≤ H/W`, `|θ| ≤ W/(qH)`. **Major arc = `q ≤ W`.** The reduction (p.14–16):

1. **Integration by parts to freeze the phase drift (eq 4.2, p.14):**
   `|Σ 1_S g e((a/q)n + θn)| ≪ |Σ 1_S g e(an/q)| + (W/(Hq)) ∫_0^{H/d} |Σ_{x/d≤n≤x/d+H'} 1_S g e(an/q)| dH'`.
   **This is the mechanism the freeze's S9 FLAW-1 "phase-freezing subdivision" re-derives** (mr-freeze.md:19,
   `H' = ε²δ₀H/(20π(log H)^{B5})`, per-block drift `2π|β|H' ≤ δ₀/10`). MRT's own (4.2) is the template: the
   drift term carries the small factor `W/(Hq)`.
2. **Split into residues mod q, detect via characters mod q₀ | q (eq p.14):** `1_{n≡b (mod q)}` → for `n ≡ b
   (mod q)`, `d₀ := (b,q)|n`, write `b=d₀b₀, q=d₀q₀, n=d₀m`; since g completely mult and `d₀ ≤ q ≤ W ≤ P₁`,
   `1_S(n)g(n) = g(d₀)·1_{S_{P₁,Q₁,√X,X/(dd₀)}}(m)·g(m)`; then `1_{m≡b₀ (mod q₀)} = (1/φ(q₀)) Σ_{χ mod q₀} χ(b₀)χ̄(m)`.
   → **produces the character-twisted function `g·χ̄`, χ mod q₀ ≤ q ≤ W.** (eq 4.4, p.15.)
3. **Apply Theorem A.2 to `g·χ̄` (p.15, "η = 1/20"):** the key bridge line — **`M(gχ̄;X') ≥ M(g;X,W) − O(1)`**
   ("From Mertens' theorem and definition of `M(g,X,W)`", p.15). This is exactly why `Q = W`: the character
   version `M(g;X,W)` (inf over χ mod q ≤ W) is the uniform lower bound across all the twists `gχ̄` the
   major-arc reduction produces. Then Cauchy–Schwarz + dyadic-X assembly → (4.1) `≪ HX/(dW^{1/4})`.

**For Route M (S9):** ride this reduction at `g = λ`. Preserve the `∀α`-OUTSIDE-integral form
(MRTDoor.lean:98–102) — the door is `sup_α ∫`, Tao's (4.1) sup-inside is OPEN, do not adopt it. The dyadic-X
average → log-measure glue is Tao's Prop 2.4 averaging (chowla.txt:633–640) vs `logMeasure R.x R.ω`.

---

## 5. APPENDICES B, C (context; NOT gate inputs) — GROUNDED

- **Appendix B (p.28–30), Theorem B.1:** counterexample to the *uncorrected* Elliott (Conjecture 1.5): a
  1-bounded mult g with `M(g;∞,∞)=∞` but `|Σ_{n≤t_m} g(n)ḡ(n+1)| ≫ t_m`. Iterative construction of g(p) on the
  unit circle. **This is WHY the fixed-Q condition (1.9) `M(g_{j₀};X,Q)→∞ for each fixed Q` is needed** rather
  than (1.7) `M(g;∞,∞)=∞`. Not a λ-gate input (λ is real, (1.7)⟺(1.9) by Appendix C).
- **Appendix C (p.30–31):** Granville–Soundararajan equivalence of (1.7)⇔(1.9) for real `g_{j₀}`. Lemma C.1:
  `𝔻(f, χn^{iα};x) ≥ (1/4)√(loglog x) + O_χ(1)` for `1≤|α|≤x`; when χ² non-principal holds for all `|α|≤x`
  ("by the zero-free … region for Dirichlet L-functions"). Confirms λ (real) needs only the (1.7) form.

---

## 6. MRT EXPONENT LEDGER (verbatim; the citation authority)

| quantity | value | ref |
|---|---|---|
| Thm 1.1 decay | `loglog H/log H + 1/log^{1/3000}X` | p.2 (1.2) |
| Thm 1.2 exceptional set | `H^{1−δ/5000}` | p.2 (1.4) |
| Thm 1.3 decay | `loglog H/log H + 1/log^{1/700}X` | p.3 |
| Thm 1.6 quality | `M(g_{j₀};10AX,Q)`, `Q=min(log^{1/125}X, log^{20}H)`, `exp(−M/80)` | p.5 |
| Thm 1.7 quality | `M(g;X,Q)`, `Q=min(log^{1/125}X, log⁵H)`, `exp(−M/20)` | p.6 |
| λ M-lower (VK θ=2/3) | `M ≥ (1/3 − ε)loglog X`; prime cutoff `exp((log X)^{2/3+ε})` | p.6 (1.12) |
| 1/125 provenance | `q ≤ (log X)^{1/125}` ⟹ no exceptional L-zeros | p.6 |
| **Thm 2.3 W-window** | **`(log H)⁵ ≤ W ≤ min{H^{1/250}, (log X)^{1/125}}`** | p.9 |
| **Thm 2.3 quality** | **`W ≤ exp(M(g;X,Q)/3)` ⟺ `M ≥ 3 log W`; Q=W in-regime** | p.9 (§0.5) |
| Thm 2.3 params | `P₁=W^{200}`, `Q₁=H/W³`, RHS `(log H)^{1/4}loglog H/W^{1/4}` | p.9 |
| Prop 2.4 quality | `W ≤ exp(M(g;X,W)/3)` (Q=W explicit), `d<W`, RHS `1/d^{3/4}·…` | p.10 |
| Prop 5.3 | `log^{20}H ≤ W ≤ …`, RHS `HX²/W^{1/5}`, Q=W | p.17 |
| Prop 5.1 W-window | `log^{20}H ≤ W ≤ min{H^{1/500},(log X)^{1/125}}` | p.16 |
| Def 2.1 | `P_j=exp(j^{4j}(log Q₁)^{j−1}log P₁)`, `Q_j=exp(j^{4j+2}(log Q₁)^j)` | p.8 |
| **Thm A.1** | **`≪ exp(−M(f;X))M(f;X) + (loglog h)²/(log h)² + 1/(log X)^{1/50}`; NO threshold** | p.20 |
| Thm A.1 remark | `exp(−M)M` → `exp(−M)` | p.21 |
| Thm A.2 | `≪ exp(−M(f;X))M(f;X) + (log h)^{1/3}/P₁^{1/6−η} + 1/(log X)^{1/50}` | p.21 |
| Prop A.3 correction | published proof wrong for slow-growing M; v3 gives `exp(−M)` (Fei Wei) | p.22 |
| A.4 distance floor | `(1/6 − 1/3π − ε)loglog X` | p.22 |
| A.5 Halász saving | `X/(log X)^{1/6 − 1/3π − ε}` (via [10, Cor 1]) | p.23 |
| ζ VK region entry | extreme t `|t−t₁|>(log X)^{20}`, Erdős–Turán + VK region for ζ | p.23 (A.6) |
| Lemma 2.2 density | `≪ (log P₁/log Q₁)X` (sieve [8]) | p.8 |
| M(f;X) / M(g;X,Q) | `inf_{|t|≤X}𝔻(f,n^{it};X)²` / `inf_{|t|≤X;q≤Q;χ}𝔻(g,χn^{it};X)²` | p.4 |

**ADDENDUM (CHI-CHECK 2026-07-24) — the 1/125 has a SECOND, structural provenance.**
The table row above (`1/125 provenance`, p.6) records the zero-free-region reading: `q ≤ (log X)^{1/125}`
⟹ no exceptional L-zeros. That reading stands and is not amended. But it is not the provenance the
§4 proof consumes. Inside §4 the same exponent arises arithmetically: `(1/50) ÷ (5/2) = 1/125`, i.e.
`W^{125} ≤ log X` is exactly what makes the `(log X')^{−1/50}` term `≤ W^{−5/2}`. So the window
`W ≤ (log X)^{1/125}` is what lets the §4 error term be absorbed into the `W`-power budget — a
structural constraint of the argument, independent of (and consumed before) the L-zero consideration.
Both provenances are real; the §4 one is the one a port must honour.

---

## 7. OCR / AMBIGUITY FLAGS (LOUD)

1. **⚠ Theorem 2.3's `M(g;X,Q)` with undefined Q** (§0.5, §2.3): resolved to Q = W via Prop 2.4 / Prop 5.3 /
   the in-regime collapse `Q = min(log^{1/125}X, log^{power}H) = W`. Only open point: whether printed "Q" is a
   typo for "W". Does not affect the A-arm verdict.
2. **⚠ θ-coefficient mismatch:** MRT uses the VK θ=2/3 region → coefficient 1/3 (in (1.12), Lemma A.4/A.6, the
   `1/6 − 1/3π` and `1/125` exponents). Our landed region is θ=3/4 → coefficient 1/4. **For the qualitative
   fixed-δ S8/S9 this is irrelevant** (only need `c > 0`, in fact `c > 3/125`, §0.3). For any QUANTITATIVE port
   the sharp exponents (`1/6−1/3π`, `1/3000`, `1/700`, `1/50`) are θ=2/3-tied and would shift — re-derive.
3. **⚠ Prop A.3 published-vs-arXiv-v3 divergence** (§3.3): port the v3 corrected proof only.
4. **No scanned-image OCR risk:** the PDF is a LaTeX text layer; all exponents extracted crisply. The only
   genuine ambiguity is #1.
