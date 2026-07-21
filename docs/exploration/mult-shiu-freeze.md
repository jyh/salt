# MULT-SHIU freeze — the hfactor secondary bound (GHS Lemma 2.4 at κ=1)

*Maestro design block, 2026-07-21 morning council (JYH nod: "let's do it!").
Status: DESIGNED, awaiting refuter pass. Source: GHS 1706.03749v1.pdf pp.8–11
(read directly this session). Consumer: `hfactor`'s E budget in
`Salt/MR/HalaszRepAsm.lean:450` (`prop21_analog`) — the "Shiu/Lemma-2.4
secondary term O(X/log X·(log y)^κ)" at κ=1, per the HFACTOR scoper re-price
(pilot 2026-07-20 17:09).*

## THE DISSOLUTION CLAIM (windmill candidate #9)

The HFACTOR scoper priced MULT-SHIU C/D because "the general 1-bounded-
multiplicative Brun–Titchmarsh is absent" — Shiu's Theorem 1 (short intervals
+ arithmetic progressions) is genuinely hard. **But GHS never uses that
generality on our surviving route.** Page-anchored:

1. Lemma 2.4's proof applies Lemma 2.3 "(with z = x and q = 1 there)" —
   GHS's own parenthetical, p.9. Full interval, no progression.
2. The only genuine short-interval application of Lemma 2.3 in the paper is
   Lemma 2.5's final step (d_κ(N) in windows of length x/T, p.11) — and
   Lemma 2.5 is the truncation error **already dissolved** by the exact hat
   kernel (HalaszFactor.lean docstring; the campaign carries no T-truncation).

The z = x, q = 1 case of Shiu is NOT Shiu: it is the elementary
**Hall–Tenenbaum bound** (Tenenbaum, *Introduction to Analytic and
Probabilistic NT*, Thm III.3.5 shape): for non-negative multiplicative F,

  S(x)·log x ≤ (1 + A + B)·x·Σ_{n≤x} F(n)/n,

proven by the swap-order argument — no bootstrap, no sieve:
S(x)log x = Σ_{n≤x}F(n)log(x/n) + Σ_{n≤x}F(n)log n; the first term ≤
x·Σ F(n)/n pointwise (log t ≤ t); in the second, log n = Σ_{p^ν∥n} log p^ν,
so Σ_{n≤x}F(n)log n ≤ Σ_{p^ν≤x} log(p^ν)·F(p^ν)·S(x/p^ν)-grade sums, and
**summing over p FIRST** (Σ_{p≤x/m}F(p)log p ≤ θ(x/m) ≤ c_θ·x/m) turns the
ν=1 mass into A·x·Σ_{m≤x}F(m)/m; the ν≥2 mass is the absolutely convergent
prime-power tail B. Then Σ_{n≤x}F(n)/n ≤ Π_{p≤x}(Σ_ν F(p^ν)p^{-ν}) ≤
exp(Σ_{p≤x}F(p)/p + B₂) and Mertens closes.

**Re-price: MULT-SHIU = C-ladder, no D.** All stones ≤ C.

## FROZEN TARGETS (statement layer — iron rule 1; carriers = corpus-native)

Setting: g : ℕ → ℂ the prime datum (‖g p‖ ≤ 1), y ≥ 2 the GHS smooth/rough
cut, η = 1/log y, x ≥ x₀. Corpus carriers: s = the y-smooth part
(`restrictBelow`-side coefficients), ℓ = the y-rough part (`restrictAbove`),
Λ_ℓ = `lambdaLin (restrictAbove y g)` (mass ≤ Λ pointwise — Amendment S1-B).
All constants HONEST-EXPLICIT or ∃-packaged (house law); nothing absorbed
silently (#253).

- **MS-A (Term 1 of GHS (2.4)):**
  `Σ_{m·n ≤ x} ‖s m‖·‖ℓ n‖/n^η ≤ C_A·(x/log x)·log y`
  for x ≥ x₀, 2 ≤ y ≤ x (∃ C_A, x₀ — or explicit if the executor's Mertens
  constants permit; the shape at κ=1 is `(x/log x)·(log y)¹`).
- **MS-B (Term 2 of GHS (2.4)):**
  `∫₀^η Σ_{m·k·n ≤ x} ‖s m‖·(Λ_ℓ k/k^α)·‖ℓ n‖/n^{2η+α} dα
     ≤ C_B·(x/log x)·log y` (same regime).
- **MS-EXIT:** the sum MS-A + MS-B packaged as the hfactor secondary-term
  bound in exactly the shape hfactor's E consumes (the (2.4)-defect of the
  window truncation; see HalaszFactor.lean §2 "THE WINDOW-TRUNCATION").

Freeze rule: MS-A/MS-B statement shapes above are BINDING once the refuter
pass confirms; internal helper shapes are the executor's.

## THE STONE LADDER (single writer, `Salt/MR/MultShiu.lean`, ~900–1300 ln)

- **HT-1** [C, 300] `hall_tenenbaum_core`: F : ℕ → ℝ, 0 ≤ F, F multiplicative,
  F ≤ 1 (1-bounded suffices for κ=1 — do NOT port the d_κ version), x ≥ 2:
  `(Σ_{n≤x} F n)·log x ≤ (1 + A + B)·x·(Σ_{n≤x} F n / n)` with A = the
  θ-Chebyshev constant, B = the prime-power tail constant. Route: the
  swap-order argument above. Wirsing input: `Σ_{p≤t} F(p)·log p ≤ θ(t) ≤
  c_θ·t` — from mathlib `Nat.primorial_le_4_pow` (θ(t) ≤ t·log 4; the
  Brun/Maynard corpus has adjacent stones, see `Salt/Maynard/
  ChebyshevInterval.lean` π-Chebyshev). Prime-power tail: reuse the
  `Salt/Mertens/PrimePower.lean` apparatus (`mertensB ≤ 2` pattern).
- **HT-2** [B/C, 200] `euler_exp_bound`: Σ_{n≤x} F(n)/n ≤
  Π_{p≤x}(1 + Σ_{ν≥1} F(p^ν)p^{-ν}) ≤ exp(Σ_{p≤x} F(p)/p + B₂), B₂ explicit
  from the prime-power tail (1-boundedness ⟹ Σ_ν≥2 p^{-ν} = 1/(p(p-1))).
- **CHEB-Λ** [B/C, 150] `lambda_partial_alpha`: Σ_{k≤K} Λ(k)/k^α ≤
  c_ψ·K^{1-α}/(1-α) for α ∈ [0, 1/2] (partial summation over ψ(t) ≤ c_ψ·t;
  ψ from θ + the elementary prime-power correction ≤ √t·(log t)²-grade —
  route θ = primorial, correction in-file). Only α ≤ η ≤ 1/log 2 is consumed.
- **ROUGH-TAIL** [B, 120] `rough_prime_tail`: Σ_{y<p≤x} p^{-1-η} ≤ c_R
  (absolute), via log p ≥ log y on the range:
  ≤ (1/log y)·Σ_n Λ(n)n^{-1-η} ≤ (1/log y)·(c_ψ'/η + c'') = c_R-grade
  (consumes CHEB-Λ's partial-summation machinery at exponent 1+η, NOT the
  K^{1-α} form — a sibling stone, same technique).
- **MERT** [named input] `mertens_second_sharp` (`Salt/Mertens/Second.lean:216`
  — VERIFIED present) for Σ_{p≤y} 1/p ≤ loglog y + c_M; Mertens FIRST
  (Σ_{p≤y} log p/p ≤ log y + c) — grep `Salt/Mertens/` first; if absent it is
  a [B, 80] in-file stone from θ ≤ c_θ·t by partial summation.
- **SPLIT** [B/C, 250] `smooth_rough_split`: the mn ≤ x smooth×rough
  factorization bijection: every N has unique N = m·n with m y-smooth, n
  y-rough; the Finset.sum reindex `Σ_{N≤x} F N = Σ_{mn≤x} (smooth m)(rough n)`
  and multiplicativity of the assembled F. Technique: the UFD scoper's
  nested-antidiagonal induction on `Nat.primeFactors_mul` (windmill #8's
  dissolution — same tool, pilot 2026-07-21 morning).
- **MS-A-ASM** [C, 200]: assemble HT-1 ∘ HT-2 ∘ MERT ∘ ROUGH-TAIL at
  F(N) = ‖s m‖·‖ℓ n‖·n^{-η} (F(p^ν) = ‖s(p^ν)‖ ≤ 1 for p ≤ y;
  = ‖ℓ(p^ν)‖p^{-νη} ≤ 1 for p > y): exp-argument = Σ_{p≤y}1/p +
  Σ_{y<p≤x}p^{-1-η} ≤ loglog y + c ⟹ MS-A.
- **MS-B-ASM** [C, 300]: Term 2. Pull Σ_k Λ_ℓ(k)/k^α ≤ Σ_{k≤x}Λ(k)/k^α ≤
  c_ψ·x^{1-α}/(1-α) (CHEB-Λ; Λ_ℓ ≤ Λ by S1-B); the remaining (m,n)-sum at
  exponents (1-α on the smooth side via m ≤ x absorption, 1+2η rough) by the
  SAME HT/Euler machinery at shifted exponent: Σ_{p≤y} p^{α-1} ≤
  Σ_{p≤y}1/p + e·α·Σ_{p≤y}(log p)/p ≤ loglog y + c (α·log y ≤ 1 — this is
  where η = 1/log y is load-bearing); then ∫₀^η x^{1-α}dα ≤ x/log x.
- **MS-EXIT** [B, 100]: package for hfactor.

Total ~1.6k ln band, one file, one executor (serial rungs) — or split
(HT-1/HT-2/CHEB-Λ/ROUGH-TAIL) ∥ (SPLIT) into two writers if quota favors
parallelism; single-writer is the default (shared helpers).

## CORNER LEDGER (worst-corner pass, incl. asymptotic — #253)

- **y small (y < y₀, e.g. y < 16 so loglog y < 1 or η > 1/log 2):** MS-A/B
  still true — log y bounded below by log 2; the exp-argument's loglog y + c
  degrades to a constant; the (x/log x)·log y RHS stays ≥ (x/log x)·log 2.
  The freeze RESTRICTS to y ≥ 3 (hfactor's y is a power of log X — always
  large); executor carries `3 ≤ y`.
- **y near x (y > √x, say):** the rough range (y, x] thins; ROUGH-TAIL and
  the Euler products only shrink. No corner. (hfactor consumes y ≪ x^{o(1)};
  the freeze allows y ≤ x for robustness.)
- **α → η endpoint (Term 2):** 1/(1-α) ≤ 2 for α ≤ 1/2 — η ≤ 1/log 3 < 1/2
  given y ≥ 3. ✓
- **x moderate (x < x₀):** ∃-packaged x₀ (house pattern); hfactor's X → ∞.
- **η-weight direction:** n^{-η} ≤ 1 used only as F ≤ 1 in HT-1; the SAVING
  from n^{-η} enters only via ROUGH-TAIL (p^{-1-η} summable-grade). The
  ledger: no stone needs n^{-η} smallness beyond that. ✓
- **F multiplicativity at p | both-parts:** impossible — smooth/rough parts
  are coprime by construction (p ≤ y xor p > y). The SPLIT stone carries it.

## TRAPS (fleet list pointers — grep SCOUT/CATCH in pilot.md)

log-of-arithmetic linarith law (set-abstract every log-of-literal atom);
sum_inter_add_sum_sdiff as THE sdiff primitive; sum_image forward-stating;
factorial-notation scope; ℤ-default bound anchoring; the multiline-sum body
detachment (σ-dangles); div_le_div_iff₀; Nat.primeFactors_mul induction
pattern (from the UFD scoper report, pilot 2026-07-21).

## EXECUTOR BOILERPLATE (verbatim per house law)

Model: opus MANDATORY. You write ONLY Salt/MR/MultShiu.lean. NO-GIT (#244).
Statement shapes MS-A/MS-B/MS-EXIT FROZEN (iron rule 1); helpers yours; a
helper harder than C → STOP, flags.md. 3 serious attempts per stone → flags
entry → next stone. Gate: lake build Salt.MR.MultShiu, no new warnings +
#print axioms per stone ⊆ [propext, Classical.choice, Quot.sound]. Growing
quantities in-statement, never absorbed (#253). Zeno partials with named
residuals = success.

## REFUTER QUESTIONS (this freeze's kill-checks)

R-1: Is the z=x,q=1-only claim TRUE against GHS pp.8–11 — does any OTHER
Lemma-2.3 consumption survive into hfactor's route (check the Prop 2.1 proof
chain and the window-truncation defect shape)? R-2: Does the swap-order
argument really close at F ≤ 1 with the stated A, B (check the ν≥2 bookkeeping
and the p∤m/p∣m split — no circularity, no hidden S(x/p) bootstrap)? R-3:
MS-B's exponent bookkeeping: does Σ_{p≤y}p^{α-1} ≤ loglog y + c really hold
for ALL α ∈ [0, η] with the e·α·log y ≤ e device (Mertens-first dependence),
and is the smooth-side exponent shift 1-α (not 1-α-β or 1) correct against
GHS's display? R-4: does MS-EXIT's shape actually plug into hfactor's E
(read HalaszRepAsm:450 and the HalaszFactor resistance list — is the
window-truncation defect EXACTLY MS-A+MS-B, or is there an uncounted third
term)? R-5: asymptotic corners — any regime (y, x, η joint) where a stone's
constant silently depends on a growing quantity (#253)?
