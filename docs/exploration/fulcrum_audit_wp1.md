# FULCRUM AUDIT — WP1: the transfer chain (Salt/HB/)

Auditor: WP1 subagent, 2026-07-18. All claims GROUNDED unless marked MEMORY.
Question per link: where does "the zero exists" actually enter, at what quality, what slack?

## Headline

The entire LANDED WP1 chain consumes NO Siegel-zero input whatsoever. Every landed
theorem is conditional only on:
  (a) `χ ^ 2 = 1` — χ is a real (quadratic) Dirichlet character mod q, ARBITRARY;
  (b) support/window hypotheses (CoprimeSupport, honestWindow, z ≥ 1 / z ≥ 100);
  (c) parametric `hres`-slots where the zero WILL enter later.
The Siegel zero enters WP1 only through the two named symbolic slots:
  - `PretenseSum χ N = Σ_{p ≤ N, χ(p)=1} log p / p` (TransferFull.lean:183) — the
    Lemma-3 slot; the zero's QUALITY (1−β₀ small) is what will make this sum small.
  - the open `hres` hypothesis of `hb_lemma2` (HB-L2c) — the (3.3)-shaped bound on
    `overshootMajorant`, whose PretenseSum factor is the zero's entry point.

## Link-by-link ledger

### L1. TwistChain.lean (HB-1, Lemma 1(a),(b) + the ± factorization)
- GROUNDED TwistChain.lean:359 `LamStar_nonneg (χ) (hsq : χ^2 = 1) (z n) : 0 ≤ LamStar χ z n`
- GROUNDED TwistChain.lean:368 `vonMangoldt_le_LamTilde (hsq : χ^2 = 1) : Λ n ≤ LamTilde χ n`
- GROUNDED TwistChain.lean:408 `eq_nPlus_mul_nMinus` (needs n ≠ 0, Coprime n q)
- GROUNDED TwistChain.lean:424 `coprime_nPlus_nMinus` (no hypotheses beyond χ)
- Siegel input consumed: NONE. Only χ²=1 (any real character — not even primitivity,
  not non-principality, not q > 1). z is a free ℕ parameter (the Admissible window
  `p < z, χ(p) = −1` truncation, TwistChain.lean:103).
- Slack: maximal — these are identities/positivity facts true for EVERY real χ.
  Note Lemma 1(a),(b) landed WITHOUT the paper's (n,q)=1 hypothesis (header lines 33-35).

### L2. TwistChainC.lean (HB-1c, Lemma 1(c) — the overshoot bound)
- GROUNDED TwistChainC.lean:317 `LamTilde_sub_vonMangoldt_le (hsq) (hn : n ≠ 0)
  (hcop : Coprime n q) : Λ̃(n) − Λ(n) ≤ 2(f(n)log n + (f(n₊)−1)Λ(n₋))`
- Siegel input: NONE. Consumes χ²=1 + coprimality of n to q only.
- Slack: the constant 2 is HB's; the f(n₊) = 2^{ω(n₊)} structure is where the
  χ(p)=+1 primes (the pretense) will be charged downstream. Nothing about the zero yet.

### L3. Transfer.lean (HB-L2 rung 1, Lemma 2's transfer inequality)
- GROUNDED Transfer.lean:189 `S1_le_S2 (hsq) : S1 A ≤ S2 χ A` — unconditional per χ²=1.
- GROUNDED Transfer.lean:199 `S2_sub_S1_le (hsq) (hA : CoprimeSupport q A) :
  S2 − S1 ≤ Σ_{n∈A} (D(n)Λ̃(n+2) + Λ(n)D(n+2))`, D = overshoot.
- GROUNDED Transfer.lean:185 `CoprimeSupport q A : ∀ n ∈ A, n ≠ 0 ∧ Coprime n q ∧ Coprime (n+2) q`
- GROUNDED Transfer.lean:223 `coprimeSupport_window` — any (x,2x] window filtered by
  Coprime (n(n+2)) m with q ∣ m feeds CoprimeSupport.
- Siegel input: NONE. Pure termwise algebra + Lemma 1(b),(c).
- Slack: `S1_le_S2` needs no support hypothesis at all (Lemma 1(b) is global).

### L4. TransferFull.lean (HB-L2 rungs 2-3; hb_lemma2 = the assembly; HB-L2c = OPEN hres)
- GROUNDED TransferFull.lean:102 `LamTilde_le_tau_log : Λ̃(m) ≤ τ(m) log m` (m ≠ 0) — crude, χ-free
  content (|χ| ≤ 1 only).
- GROUNDED TransferFull.lean:126 `hb_lemma2_transfer_bound (hsq) (hA : CoprimeSupport q A) :
  S2 − S1 ≤ overshootMajorant χ A` where overshootMajorant (line 119) =
  `Σ_{n∈A} (D(n)·τ(n+2)log(n+2) + log n·D(n+2))`.
- GROUNDED TransferFull.lean:167 `overshootMajorant_split = majLogL + majPPL + majLogR + majPPR`
  (the four HB L₁–L₄ exceptional sub-sums).
- GROUNDED TransferFull.lean:183 **PretenseSum** def:
  `PretenseSum χ N = Σ_{p ∈ range(N+1), p prime ∧ chiRe χ p = 1} log p / p`.
- GROUNDED TransferFull.lean:204-214 **hb_lemma2 — THE EXACT OPEN HYPOTHESIS SHAPE (HB-L2c)**:
  ```
  theorem hb_lemma2 (χ) (hsq : χ ^ 2 = 1) {A} (hA : CoprimeSupport q A)
      (x : ℝ) (N : ℕ) (Cmain z0 Aexp junk : ℝ)
      (hres : overshootMajorant χ A
          ≤ Cmain * (x / z0)
            + Cmain * (x / Real.log x) * Real.exp (Aexp * z0) * PretenseSum χ N
            + junk) :
      S2 χ A - S1 A ≤ Cmain * (x / z0)
        + Cmain * (x / Real.log x) * Real.exp (Aexp * z0) * PretenseSum χ N + junk
  ```
  i.e. hb_lemma2 is `le_trans (hb_lemma2_transfer_bound ...) hres` — one composition step.
- Siegel input: NONE CONSUMED; ONE SLOT CREATED. The zero enters WP1's ledger only
  as the FUTURE bound on `PretenseSum` (Lemma 3: PretenseSum ≪ L(log η)^{−1/4},
  needing 1−β₀ = η/L small) and the FUTURE discharge of hres (HB-L2c: the fibration
  of the PP-parts by the χ=−1 prime power v, inner count via hb_lemma8'_unconditional,
  Mertens sums giving exp(Aexp z₀)·PretenseSum — header lines 43-50).
- Slack: hres is completely parametric — Cmain, z0, Aexp, junk are FREE reals; even
  z0's sign is unconstrained here. Any (3.3)-shaped bound feeds through. The demand
  on the zero is thus deferred entirely to (i) HB-L2c's arithmetic (no zero needed —
  it is unconditional sieve work) and (ii) Lemma 3's PretenseSum estimate (zero needed).

### L5. StarStep.lean (HB-L4, the S⁽²⁾ → S⁽³⁾ star step)
- GROUNDED StarStep.lean:86 `LamStar_sub_LamTilde_eq_starDiff` (exact identity, no hyp beyond χ).
- GROUNDED StarStep.lean:254 `S2_sub_S3_le (hsq) (z) (A) : |S2 − S3| ≤ Σ_{n∈A}
  (starErrBound·tauLog(n+2) + tauLog·starErrBound(n+2))` — NO coprimality needed.
- GROUNDED StarStep.lean:328 `S2_sub_S3_bound` — parametric hres slot (Cerr·x/z + junk shape).
- Siegel input: NONE. The z-window here is the Λ* truncation parameter (Admissible:
  drop p² for p < z, χ(p) = −1); free ℕ.
- The honest finding (header lines 39-49): the landed Admissible ALSO leaves small
  χ(p)=+1 squares exceptional (O(x) residual) — resolved not by def change but by
  the window's P-coprimality (next link). Catch #80 genre: an architecture-fossil
  candidate that was caught and resolved by the house (s3-hb3-design.md:1165-1180).

### L6. StarWindow.lean (HB-L4b — the star residual DISCHARGED, unconditional)
- GROUNDED StarWindow.lean:72 `excPrimorial χ z = ∏_{p<z prime, χ_ℝ(p) ≠ −1} p` —
  the minimal honest modulus (subsumes HB's q·P AND the p=2 case HB's ∏_{2<p<z} misses).
- GROUNDED StarWindow.lean:288 `hstar_window (z x) (hz : 1 ≤ z) (A ⊆ Ioc x 2x)
  (hcop : ∀ n∈A, Coprime (n(n+2)) (excPrimorial χ z)) (ε>0) : ∃ C>0, star-majorant sum
  ≤ 2(C(2x+2)^ε log(2x+2))²·(2x/z + √(2x+2))` — grade x^{1+2ε}log²x/z + x^{½+2ε}log²x.
- GROUNDED StarWindow.lean:429 `S2_sub_S3_honestWindow` — the composed instance on
  `honestWindow χ z x` (line 408).
- Siegel input: NONE. Fully discharged: the S⁽²⁾→S⁽³⁾ step has NO remaining slot.
- Slack: needs only z ≥ 1 and the window coprimality; the τ ≤ C_ε m^ε weight is
  Maynard's card_divisors_le_rpow (cross-flagship reuse). The √(2x+2) junk term is
  far below HB's needs. Binding constraint downstream: z must satisfy x/z ≪ target,
  i.e. z ≥ (log x)^{2+} grade for Lemma-4 purposes — wide open slack.

### L7. PairSieve.lean + PairInstance.lean (Lemma 8, rough case — UNCONDITIONAL)
- GROUNDED PairSieve.lean:192 `boundingSum_ge_log_sq_of_twinDensity (z ≥ 100, level ≥ z²,
  twin density 2/p) : S ≥ (1/64)(log z)²`.
- GROUNDED PairInstance.lean:414 `hb_lemma8 (z ≥ 100) (d₁,d₂ > 0 coprime z-rough) :
  S(d₁,d₂;z) ≤ 64(x/(d₁d₂))/(log z)² + 2z⁸`.
- Siegel input: NONE — not even a character appears. Pure Selberg on the landed
  Brun/M3/M5 engine.
- Slack: constant 64 crude (Brun-track heritage); error 2z⁸ crude (forces z ≤ x^{1/8−}
  in consumers; HB uses z ~ small powers, so harmless). ρ(d)-remainder ≤ 2ρ(d) exact.

### L8. PairSieveMixed.lean + MixedCount.lean (Lemma 8′, mixed/cofactor case — UNCONDITIONAL)
- GROUNDED PairSieveMixed.lean:301 `pairSieveMixed_lemma8 : siftedSum ≤
  16(M/φ(M))²·mass/(log Z)² + E` (M = 2d₁d₂, twin density off M, 1/p on M).
- GROUNDED MixedCount.lean:609 `hb_lemma8'_unconditional (Z ≥ 100, d₁,d₂ odd coprime
  positive — NO roughness) : S′(d₁,d₂;Z) ≤ 64(d₁d₂/φ(d₁d₂))²(x/(d₁d₂))/(log Z)² + 2Z⁸`
  — "fully supplying HB's (3.3)" per its docstring; the φ-factor is the honest
  mixed-density price (R2 closed).
- GROUNDED MixedCount.lean:201 `rhoK_prime`: per-prime mixed root count
  1 if p ∣ 2d₁d₂ else 2 — a clean ZMod p field-root count.
- Siegel input: NONE. This is the inner pair-count that HB-L2c will call at
  d₁ = v (the χ=−1 prime power), d₂ = 1.

### L9. QuadCharSum.lean (HB-2 — the p.217 omitted lemma, prime case)
- GROUNDED QuadCharSum.lean:62 `quadraticChar_sum_mul_shift (ringChar F ≠ 2, e ≠ 0) :
  Σ_t χ(t)χ(t+e) = −1`; :137 two-forms bound ≤ 2; :202 Legendre specializations.
- Siegel input: NONE. Consumer is WP6 (leading-term character averaging), not the
  transfer chain proper. Residuals named in-file: QCS-3 (composite squarefree via
  Jacobi symbol + CRT) and prime-power/mod-8 cases — OPEN (QuadCharSum.lean:218-241).

### L10. All.lean — the audit
- GROUNDED All.lean:31-70: `#audit_axioms` over all 39 landed HB names (the audit
  gate: at most [propext, Classical.choice, Quot.sound]). MEMORY: build green per
  pilot ceremonies (9215-job builds cited at the HB-L4b/L2b landings).

## What remains OPEN in WP1 (grounded)

1. **HB-L2c — the ONLY open WP1 arithmetic** = discharge hb_lemma2's `hres`:
   bound `overshootMajorant χ A` by the (3.3) shape. GROUNDED pilot.md:7386-7395
   (2026-07-18 ~03:20 PT consumer recon): "the HB transfer has NO literal ShiuCore
   slot — the τ-in-AP content sits inside overshootMajorant (hb_lemma2's hres; the
   star-step hres is already discharged by S2_sub_S3_honestWindow) ... the divisor
   fibration of f meets ShiuCore at residue 2 mod d and the Λ(n₋) piece feeds
   PretenseSum — but NO L2c design exists in the docs (the 'v-fibration' label was
   memory-tier, not grounded). HB-L2c re-classed: UNDESIGNED (C+), queues for its
   own design block." Content per TransferFull.lean:43-50: fibration of the PP-parts
   by v = n₋ (χ=−1 prime power), inner pair-count via hb_lemma8'_unconditional
   (d₁ = v, d₂ = 1), Mertens Σ_v Λ(v)/v → exp(A z₀), τ-AP inner sums Σ_m τ(vm+2)
   via ShiuCore. ShiuCore IS closed: `sum_tau_in_ap_le : ShiuCore`
   (ShiuBlocks.lean:292 def; ShiuFinal/ShiuIV land it) with range constraint
   q ≤ z^{1−1/8000} — the range HB-L2c must respect when fibring.
   NOTE: HB-L2c is UNCONDITIONAL sieve/divisor arithmetic — it consumes NO zero.
2. **Lemma 3 (the PretenseSum estimate)** — WP2 territory: PretenseSum χ N ≪
   L(log η)^{−1/4} under the zero (s3-hb3-design.md:850-852). THE quality entry point.
3. **WP7 assembly** — Lemma 5 → S⁽³⁾ → Theorem 1 → Corollary 2 + the windowed twin
   door (design doc:867-871): not started; the (1.13) window q^250 ≤ x ≤ q^500 and
   Corollary 2's effective C^(1) shape (design doc:824-830) exist nowhere in Lean yet.
4. QCS-3 + prime-power quadratic character sums (WP6 inputs) — named residuals.

## THE FULCRUM READING (WP1's demand on "the zero exists")

- The landed WP1 chain is a ZERO-FREE machine: every theorem holds for EVERY real
  χ mod q (χ² = 1 — not even primitivity or non-principality is consumed). The
  Siegel zero enters WP1 ONLY as the future supplier of PretenseSum smallness.
- EXACT demand shape at the WP1/WP2 seam: make
  `Cmain·(x/z₀) + Cmain·(x/log x)·exp(Aexp·z₀)·PretenseSum χ N + junk` beat the
  S⁽¹⁾ main term. The zero per se is NOT needed — ANY hypothesis F implying
  "Σ_{p ≤ N, χ(p)=1} log p/p is o((log x)·exp(−A z₀))-grade for suitable z₀" feeds
  the slot identically. The pretense (χ(p) = −1 for almost all small p, log-weighted)
  is the TRUE consumable, not the zero; the zero is HB's way of manufacturing it
  (via L′/L(1,χ) = ηL + O(L(log η)^{−1/4}), Lemma 3, needing η large = first-power
  quality 1−β₀ ≤ 1/(ηL)).
- Quality consumed downstream (grounded, design doc:824-830): HB (1.11) FIRST-POWER,
  1−β₀ ≤ (3 log q)^{−1}, η := ((1−β₀)L)^{−1} ≥ 3; Corollary 2 needs only η ≥ C^(1)
  (fixed effective constant) INFINITELY OFTEN — this is exactly the corpus's
  `InfinitelyManySiegelZeros` (SiegelTwin.lean:85, ∀c∃-order: ∀c>0 ∃ q,χ real
  primitive quadratic ≠ 1, β with LFunction χ β = 0 ∧ 1 − c/log q < β < 1).
  The mis-aimed squared-log `SiegelSequence` is bypassed (design doc:876-880).
- Quantity: a SEQUENCE of moduli (infinitely many q), one zero each; no zero-density
  demand inside WP1 (density + repulsion live in WP2's Lemma 3/7).
- Range: per-q window (1.13) q^250 ≤ x ≤ q^500 — not yet formalized; WP1's landed
  windows are generic dyadic (x, 2x] with free z, z₀ — strictly wider than needed.
- Effectivity: preserved so far (all WP1 constants explicit/parametric); the
  repulsion route (Jutila) keeps C^(1) effective (design doc:946-949).

