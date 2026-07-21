# MULT-SHIU freeze — the hfactor secondary bound (GHS Lemma 2.4 at κ=1)

*Maestro design block, 2026-07-21 morning council (JYH nod: "let's do it!").
Status: **REFUTER PASS COMPLETE — REPAIR-THEN-FIRE applied, FROZEN** (MS-REF-A
+ MS-REF-B verdicts digested ~10:50; binding repairs folded in below, marked
⟦R⟧). Source: GHS 1706.03749v1.pdf pp.8–11 (read directly this session).
Consumer: `hfactor`'s E budget in `Salt/MR/HalaszRepAsm.lean:450`
(`prop21_analog`) — the "Shiu/Lemma-2.4 secondary term O(X/log X·(log y)^κ)"
at κ=1, per the HFACTOR scoper re-price (pilot 2026-07-20 17:09).*

## ⟦R⟧ SCOPE (binding — MS-REF-B R-4)

This freeze closes **hfactor's E only**. The codebase names "MULT-SHIU" at a
SECOND site — the `hloss`/W seam (`DistSplit.lean:172`, `PropA3Core.lean:33/
:167`): `pretDistSq f (fgJ f t₀ y Y) X ≤ W`, a per-prime pretentious window
mass (loglog-scale), a DIFFERENT object at a DIFFERENT layer. It is NOT
discharged here. Registered as the separate residual **HLOSS-WINDOW**:
out-of-window mass = Mertens-second (LANDED, `mertens_second_sharp`);
in-window twist-defect `Σ_{y<p<X/y}(1−Re(|f p|²p^{it₀}))/p` = a ball-center
quantity, its own design block. Landing this freeze does NOT retire hloss.
Additionally (MS-REF-A #3): GHS Lemma 2.6 (classical Brun–Titchmarsh, prime
counts in intervals — NOT Shiu-multiplicative) is a downstream Thm-1.1
main-integral tool, outside hfactor's E; if the campaign ever consumes it,
it is a Brun-track-shaped separate stone. The dissolution headline reads:
"GHS never uses Shiu on the Prop-2.1 representation route (= hfactor's E)."

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

Setting: g : ℕ → ℂ the prime datum (‖g p‖ ≤ 1), **y ≥ 8** the GHS smooth/rough
cut ⟦R: floor raised from 3 — both refuters caught 1/log 3 ≈ 0.910 > 1/2;
y ≥ 8 gives η = 1/log y ≤ 0.481 < 1/2, restoring every α ≤ 1/2 claim; free
since hfactor's y is (log X)-power-sized⟧, η = 1/log y, x ≥ x₀. Corpus
carriers: s = the y-smooth part
(`restrictBelow`-side coefficients), ℓ = the y-rough part (`restrictAbove`),
Λ_ℓ = `lambdaLin (restrictAbove y g)` (mass ≤ Λ pointwise — Amendment S1-B).
All constants HONEST-EXPLICIT or ∃-packaged (house law); nothing absorbed
silently (#253).

- **MS-A (Term 1 of GHS (2.4)):**
  `Σ_{m·n ≤ x} ‖s m‖·‖ℓ n‖/n^η ≤ C_A·(x/log x)·log y`
  for x ≥ x₀, **8 ≤ y ≤ x** (∃ C_A, x₀ — or explicit if the executor's
  Mertens constants permit; the shape at κ=1 is `(x/log x)·(log y)¹`).
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
  F ≤ 1 (1-bounded suffices for κ=1 — do NOT port the d_κ version), F 1 = 1,
  x ≥ 2: `(Σ_{n≤x} F n)·log x ≤ (1 + A + B)·x·(Σ_{n≤x} F n / n)` with A = the
  θ-Chebyshev constant, B = the prime-power tail constant. Route: the
  swap-order argument above. Wirsing input: `Σ_{p≤t} F(p)·log p ≤ θ(t) ≤
  c_θ·t` — from mathlib `Nat.primorial_le_four_pow` ⟦R: NON-deprecated name;
  `_le_4_pow` is a deprecated alias and trips the warnings gate⟧ (θ(t) ≤
  t·log 4; adjacent corpus stones: `Salt/Maynard/ChebyshevInterval.lean`
  π-Chebyshev, `Salt.Maynard.sum_log_div_prime_le`).
  ⟦R (MS-REF-A R-2, BINDING — the √y-divergence trap): the ν≥2 mass is
  handled by `S(x/p^ν) ≤ x/p^ν` — which NEEDS F ≤ 1 — giving
  `Σ_p Σ_{ν≥2} ν·log p·F(p^ν)·S(x/p^ν) ≤ x·Σ_{p,ν≥2} ν·log p/p^ν = B·x`,
  then reattach the `Σ_{m≤x}F(m)/m` factor via `F(1) = 1 ⟹ Σ F(m)/m ≥ 1`.
  Do NOT instead bound `F(p^ν) ≤ 1` and drop the `p^{-ν}` weight — that
  path hits ψ(y)−θ(y) ~ √y and DIVERGES. The prime-power constant
  `Σ_{p,ν≥2} ν log p/p^ν` rides the `Salt/Mertens/PrimePower.lean`
  apparatus (`mertensB ≤ 2` pattern). Alternate route (executor's option
  if cleaner in Lean): group ν≥2 by m with `ψ(t)−θ(t)` bounds — commit to
  ONE route in the file docstring.⟧
- **HT-2** [B/C, 200] `euler_exp_bound`: Σ_{n≤x} F(n)/n ≤
  Π_{p≤x}(1 + Σ_{ν≥1} F(p^ν)p^{-ν}) ≤ exp(Σ_{p≤x} F(p)/p + B₂), B₂ explicit
  from the prime-power tail (1-boundedness ⟹ Σ_ν≥2 p^{-ν} = 1/(p(p-1))).
  ⟦R (MS-REF-B gap 1): MS-B-ASM consumes this at SHIFTED exponent — the
  smooth-side tail `Σ_{p≤y} Σ_{ν≥2} p^{ν(α-1)}` for α ∈ [0, η], η ≤ 1/2:
  uniformly bounded (`p^{α-1} ≤ p^{-1/2}`, geometric tail
  `p^{2(α-1)}/(1-p^{α-1}) ≤ 2·p^{-1}`-grade), but it is a SEPARATE small
  stone — state and prove `euler_exp_bound_shifted` alongside, do not
  silently reuse the exponent-1 version.⟧
- **CHEB-Λ** [B/C, 150] `lambda_partial_alpha`: Σ_{k≤K} Λ(k)/k^α ≤
  c_ψ·K^{1-α}/(1-α) for α ∈ [0, 1/2] (partial summation over ψ(t) ≤ c_ψ·t;
  ψ from θ + the elementary prime-power correction ≤ √t·(log t)²-grade —
  route θ = primorial, correction in-file). Only α ≤ η ≤ 1/log 2 is consumed.
- **ROUGH-TAIL** [B, 120] `rough_prime_tail`: Σ_{y<p≤x} p^{-1-η} ≤ c_R
  (absolute), via log p ≥ log y on the range:
  ≤ (1/log y)·Σ_n Λ(n)n^{-1-η} ≤ (1/log y)·(c_ψ'/η + c'') = c_R-grade
  (consumes CHEB-Λ's partial-summation machinery at exponent 1+η, NOT the
  K^{1-α} form — a sibling stone, same technique).
- **MERT** [named input — ⟦R: COLLAPSES TO WRAPPERS, MS-REF-A inventory
  find⟧] `mertens_second_sharp` (`Salt/Mertens/Second.lean:216` — VERIFIED)
  for Σ_{p≤y} 1/p ≤ loglog y + c_M; Mertens FIRST is **ALREADY LANDED
  SHARP**: `mertens_first_upper` (`Salt/MR/PrimeSigmaShift.lean:46`,
  `Σ_{p≤x}(log p)/p ≤ log x + (log 4 + 4)`, coefficient 1, wraps
  `Salt.Maynard.sum_log_div_prime_le`). AND the MS-B exponent-shift device
  is pre-landed: `sigma_shift_term_le` / `sigma_shift`
  (`PrimeSigmaShift.lean:62/:95`: `p^{-1}−p^{-1-δ} ≤ δ·(log p)/p` and the
  summed form at δ = 1/log x). The executor CONSUMES these (δ↔α, x↔y),
  never rebuilds them.
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

Total ⟦R: re-priced ~1.2–1.5k ln — MERT + the exponent-shift device are
pre-landed wrappers (PrimeSigmaShift.lean)⟧, one file, ONE executor (serial
rungs; single-writer).

## ⟦AMENDMENT MS-B-ROUGH (maestro-ruled 2026-07-21 evening, from
MS-CLOSE's in-session catch)⟧ The naive MS-B decoupling — ‖ℓ n‖ ≤ 1 and
Σ n^{-1-2η} = O(log y) — combined with the smooth factor's O(log y)
yields (log y)², BREAKING κ=1. The honest route: the rough n-factor is
O(1) ABSOLUTE, because ℓ vanishes on p ≤ y so its Euler product closes
via rough_prime_tail (landed as `ms_b_rough_factor` ≤ exp(2(log4+4)+4)).
The (log y)¹ lives ONLY in the smooth m-factor (euler_exp_bound_shifted
+ the e^t ≤ 1+(e-1)t linearization at α·log y ≤ 1). The carriers, pinned:
s = ellLin (restrictBelow y g); ℓ = ellLin (restrictAbove y g); Λ_ℓ =
lambdaLin (restrictAbove y g) — NOTE the corpus's `smoothPart`
(HalaszLambda:402) is the smoothing CONVOLUTION, not the s-carrier.

## CORNER LEDGER (worst-corner pass, incl. asymptotic — #253)

- **y small:** ⟦R — REPAIRED (both refuters): the original ledger claimed
  `η ≤ 1/log 3 < 1/2` — FALSE (1/log 3 ≈ 0.910). The freeze now RESTRICTS
  to **y ≥ 8**: η = 1/log y ≤ 1/log 8 ≈ 0.481 < 1/2, so `1/(1−α) ≤ 2` for
  all α ∈ [0, η] and CHEB-Λ's domain α ∈ [0, 1/2] covers the consumed
  range. Free restriction — hfactor's y is (log X)-power-sized. Executor
  carries `8 ≤ y`.⟧
- **y near x (y > √x, say):** the rough range (y, x] thins; ROUGH-TAIL and
  the Euler products only shrink. No corner. (hfactor consumes y ≪ x^{o(1)};
  the freeze allows y ≤ x for robustness.)
- **α → η endpoint (Term 2):** 1/(1-α) ≤ 2 for α ≤ 1/2 — η ≤ 1/log 8 < 1/2
  given y ≥ 8 ⟦R⟧. ✓ (The exponent device is refuter-CONFIRMED valid at the
  edge p = y, α = η exactly: `y^η = e`, `p^α − 1 = e−1 ≤ e·α·log p` tight
  with room.)
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
