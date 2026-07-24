# SEAM-SCOPE — the §8.3 mechanism + the hsplit object finding (2026-07-24 night)

*Read-only recon for the eq-(24) seam freeze. MAESTRO CORRECTION APPLIED at §3′:
the scoper's "L11 NOT landed" claim is FALSE — `halasz_primes_pow`
(HalaszPrimesCore.lean:3641, All-wired) is exactly MR Lemma 11's well-spaced
discrete shape at the frozen θ=3/4 header. The rest is banked as reported.*

## 1. THE §8.3 MECHANISM (MR v4 pp.24–29, verbatim-grounded)

- **Step 0 (p.24)**: "Since the mean value theorem gives O(T/X+1), we can assume
  T ≤ X." All T > X ride the trivial MVT. (MRT Prop A.3 same, T ≤ X/2.)
- **Step 1 — Lemma 12 at P=exp((logX)^{1−1/48}), Q=exp(logX/loglogX),
  H=(logX)^{1/48}**: ∫_𝒰|F|² ≪ H²(logX)²·∫_𝒰|Q_{v,H}·R_{v,H}|² +
  (T/X+1)·(1/H + 1/P + logP/logQ), for SOME v (prime block Q_{v,H} of
  log-width 1/H; Ramaré co-factor R_{v,H}). ALL T-dependence sits in the
  additive remainder.
- **Step 2**: well-spaced discretization 𝒯 ⊆ 𝒰.
- **Step 3 — 𝒰's thinness (the ONLY use of its defining property)**: Lemma 8 ⇒
  |𝒯| ≪ T^{1/2−η}X^{o(1)}.
- **Step 4 — split at |Q_{v,H}| = (logX)^{−100}; the two branches SWAP which
  factor is pointwise-small**:
  * 𝒯_S (prime factor small): co-factor mean square via **Lemma 9 (Halász
    integers)**; thinness consumed here (|𝒯|√T ≪ X^{1−o(1)}). Grade (logX)^{−199}.
  * 𝒯_L (co-factor small): (i) |𝒯_L| ≪ exp((logX)^{1/48+o(1)}) — T-free BECAUSE
    of Step 0; (ii) **Lemma 3+5: the unconditional pointwise Halász bound on
    the Ramaré co-factor** |R(1+iu)| ≪ (logX)^{−1/16+o(1)}·logQ/logP on the
    whole range (NOT a 𝒰-property); (iii) **Lemma 11 (Halász primes)** on
    Σ_{𝒯_L}|Q|² — the decay kills |𝒯_L|; (iv) the prime-window gain
    Σ_{p∈block}1/p ≍ 1/v — "the extra logarithm the whole apparatus exists
    to save" (p.29 verbatim).
- **Step 5 — the balance**: H=(logX)^θ, ρ = the R-polynomial Halász exponent
  (MR: 1/16): main (logX)^{5θ−2ρ} vs remainder (logX)^{−θ} ⇒ **θ = ρ/3**;
  at ρ=1/16, θ=1/48 — THE ENTIRE ORIGIN OF 1/48. MRT p.24 confirms the
  parametrization ("replacing 1/48 by ρ/3 > 1/50", ρ ≈ 0.0606). Our ρ-analogue
  is the B4 grade 1/(32e) ≈ 0.0115 ⇒ our ∫_𝒰 grade ≈ (logX)^{−0.0038} —
  positive, c₀-existential posture survives; **never carry 1/48 or 1/50
  literally** (Benli discipline).
- **Step 6 — the (T/(X/Q₁)+1) grade arises in §8.1 ONLY** (E₁'s co-factor
  support N ≥ X/Q₁); §8.2/§8.3 carry (T/X+1). Lemma 14's unbounded max-term
  closes on the trivial MVT via the **Q₁-gain** (needs Q₁ε ≥ 1 ⟺
  h ≳ (logX)^{1/50}, true at the door's H) — NOT via (T/X+1) alone. Our rows
  carry (T/X+1); the Q₁-form must be stated where consumed. Also
  s8-freeze:63's "T ≤ X² covers Lemma-14's max" is wrong as written (hMsup
  quantifies over ALL T ≥ X/h₁); the substance (trivial MVT + Q₁-gain beyond
  X) is fine.
- Consumer T pinned: the door's h₁ = H = O_ε(log x) ⇒ **T ≍ X/logX**.

## 2. THE OBJECT FINDING — annHead is NOT the 𝒰-object, at any T

| object | integrand | true L²-size on [−T,T] |
|---|---|---|
| MR ∫_𝒰\|F\|² / spoly (dyadic, Σ\|a\|²/n² ≍ 1/X) | dyadic polynomial | ≍ T/X + 1 |
| annHead (AnnHead:60) | the FULL seam L-series at 1+σ (ellLin: ALL squarefree n, a₁=1 ⇒ Σ\|a\|²/n^{2+2σ} ≥ 1) | **≍ T** |

**Consequences**: (1) `hsplit : Itot = (annHead+Utail)+Imom` is UNSATISFIABLE at
the intended semantics (LHS ≍ T/X+1, RHS ≥ annHead ≍ T) — the three landed
rows are kernel-valid but VACUOUS for the intended instantiation; only ≤ is
true and even that is weaker than the trivial MVT for T ≥ (logX)^{1/15}.
(2) T-RESHAPE's refutation under-stated: the OBJECT's own size exceeds the
bare-X socket once T > X(logX)^{−2/e} — no sup-step repair exists.
(3) The (logX)² = 1/σ² is an OBJECT cost (the ζ-like full L-series at 1+σ is
Θ(1/σ)); MR Lemma 1's dyadic pointwise bound has NO 1/σ. (4) Even on the
ball, measure×our-sup is short by (logX)² — **the 1/σ must go**.

**The honest identification chain (MRT A.6→A.7)**: the X-scaled twisted SUM
bound (Lemma-A.6-grade = exactly `halasz_ball_decay`'s U ≪ X(e^{−cM} +
(logX)^{−1/2+ε})) converts to the pointwise POLYNOMIAL bound by **partial
summation**: spoly = A_t(2X)/2X − A_t(X)/X + ∫A_t(u)/u²du ⇒ |spoly| ≤
3·sup_u|A_t(u)|/u — no logX loss. Square + integrate over the ball
(measure 2(logX)^{1/16}) ⇒ the 𝒯₀ leg. THIS resolves BRIDGE-CHECK's
"three X-powers" amber: the head object should be the SEAM-SUM (X-graded);
the bridge is partial summation, NOT a line re-pin. Class C, ~300–500 ln.
Worst corner: halasz_ball_decay delivers U at scale X only; Abel needs
sup_{X≤u≤2X}|A_t(u)| — a uniformity rung on the S1′/S2′ seam (or hatKernel
re-instantiation per u) must be checked. **Authority: annHead is a post-freeze
S4 pin (JYH-ratified 2026-07-23) — the re-pin is design-block remit but
JYH-TIER, exactly as the original.**

## 3. THE PARTITION LEMMA — cheap (B, ~300–450 ln, zero analytic content)

primeBlockPoly continuous [A,30]; BlockSmallAt sets = countable ∩ of closed
⇒ closed [B,40]; Uset open / Tset Borel [A/B,40]; disjointness + exhaustiveness
LANDED (Tset_disjoint :250, Tset_Uset_disjoint :256, exists_Tset_or_mem_Uset
:265); disjoint-union setIntegral via integral_finset_biUnion + continuity-
integrability [B,150–250]; annulus-restricted exhaustiveness [A/B,50].

### 3′. MAESTRO CORRECTION — the §8.3 corpus status
The scoper's residual list said "L11 NOT landed" — **FALSE**:
`halasz_primes_pow` (HalaszPrimesCore.lean:3641, All.lean:328) is precisely
MR Lemma 11's discrete well-spaced shape — prime-supported blocks, WellSpaced
𝒯, the C·(P + |𝒯|·P·exp(−c·logP/((logT)^{3/4}(loglogT)⁴))·(logT)²)/logP
grade with the 1/logP prime-window gain, P ≤ T^10, at the frozen θ=3/4
override. The scoper grepped HalaszPrimes.lean (the duality gateway file)
only. CORRECTED honest §8.3 residuals: **L3 for the dyadic Ramaré co-factor
(the pointwise (logX)^{−1/16}-grade bound — not landed for that object);
L9's van-der-Corput socket hZ (halasz_integers_of_vanDerCorput conditional —
open named residual); L12's herr (rough-tail pricing, C, ~400–800)**. With
L7/L8/L11/L12-core landed, the §8.3 interior honest add ≈ **1–2k, C**
(down from the scoper's 1.5–3k C/D).

## 4. THE hsplit DESIGN CANDIDATES (for the morning freeze)

- **SHAPE 0** [A, ~20 ln/row, do regardless]: weaken every hsplit `=` → `≤`
  (a genuine eq-(24) yields inequalities). Note the two `_row_` lemmas
  constrain Itot ONLY via hsplit — currently informationless until wired.
- **SHAPE A** [RECOMMENDED]: the MRT ball/far split on the ANNULUS target
  (matching lemma14_contour's datum T₀ ≤ |t| ≤ T): 𝒯₀ = ball |t−t₁| ≤
  (logX)^{1/16} (T-FREE; measure×sup via the partial-summation bridge — kills
  both the T-gate AND the (logX)²); 𝒯₁ = the far leg via the §8 rows
  (T-general). Stones: 2-set setIntegral [B,150]; ball measure×sup [B,120];
  the bridge [C,300–500]; far-leg binders [design]. Worst corners: the
  sup-over-u uniformity; the 1/(1+|t−t₁|) factor not needed (accept the
  (logX)^{1/16} measure cost, as MRT itself does).
- **SHAPE B**: the literal eq-(24) 𝒯ⱼ/𝒰 partition with per-piece binders
  [B, 350–500 incl. §3] — provable, composes as SHAPE A's 𝒯₁ interior.
  Worst corner: Tset's single-δ shape vs MR's v-dependent e^{−αv/H} — the
  v-indexed re-pin of Tset is a Decomp statement change, **Fable/JYH-tier**.
- **SHAPE C — REFUTED, do not re-propose**: polylog-T head + trivial-MVT
  beyond leaves the consumer's window (logX)^A < T < X uncovered (the
  Q₁-gain closes only T ≳ X).

## 5. Door-road corrections (folded into door-road-0724.md's corrections block)

Stone 1 re-priced (partition B/400 + bridge C/300–500 + the 𝒯₁ interior);
the road's finding #2 repair superseded (the object, not the socket shape, was
the defect — SHAPE A makes the head T-FREE); §8.3 interior added (≈1–2k C
post-correction); the target restated on the ANNULUS (the |t| ≤ T₀ core has
no M_range information — MR integrate from T₀; free consistency with
lemma14_contour); the (T/X+1)-vs-(T/(X/Q₁)+1) and s8-freeze:63 notes; the
M_range geometry PRAISE (the (logX)^{1/16} widening IS the ball radius — the
frozen geometry was built for this route and fits unchanged; the moment side
is correct and T-general — the head leg alone must move).
