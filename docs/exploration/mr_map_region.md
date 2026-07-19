# MR map — the landed region and its MR-shaped consumption surface

Labels: **G** = GROUNDED (file:line read this session), **M** = MEMORY (standard
literature, NOT in the corpus — verify before freezing anything on it).

## 1. The landed pow region — exact statements

### 1a. `vkTheta` (G: Salt/Vk/PowRegion.lean:35–36)
`vkTheta t = (1/1000) / ((log t)^(3/4) * (log log t)^2)` — rpow 3/4, NATURAL
square on the loglog. Note the STRIP half-width has (loglog)²; the REGION ends
up with (loglog)³ — the extra power is bought by the `Lq` width algebra
(`Lq ≤ 2.25e7·L^{3/4}·ℓ³`, PowRegion.lean:313), not by the strip.

### 1b. The growth `zeta_growth_pow` (G: Salt/Vk/GrowthPow.lean:977–1036)
`ZetaGrowthPow` (G: PowRegion.lean:78–81) is
`∃ K t₀, 1 ≤ K ∧ 3 ≤ t₀ ∧ ∀ σ t, t₀ ≤ t → 1 − vkTheta t ≤ σ → σ ≤ 3 →
 ‖ζ(σ+it)‖ ≤ K·log t`.
Proven witnesses (G: GrowthPow.lean:978): **K = 8104, t₀ = exp(exp 100)**.
Growth FORM: `K·log t` — dlVP-GRADE growth on a VK-WIDE strip. The VK content
is the strip WIDTH (vkTheta), not the growth exponent; there is NO landed
`|ζ(1+it)| ≪ (log t)^{3/4}`-grade pointwise bound (see §4, gap Q2).

### 1c. The region (G: GrowthPow.lean:1044–1048; emission PowRegion.lean:354–401)
`zeta_zero_free_region_pow :
 ∃ c T₀, 0 < c ∧ 3 ≤ T₀ ∧ ∀ ρ, ζ ρ = 0 → T₀ ≤ |ρ.im| →
   ρ.re ≤ 1 − c / ((log|ρ.im|)^(3/4) * (log log|ρ.im|)^3)`
θ = 3/4 exactly; rpow 3/4, natural cube. **c and T₀ are EXISTENTIAL in the
exported statement** — consumers see only `0 < c` and `3 ≤ T₀`. The concrete
witnesses inside the proof (G: PowRegion.lean:365 with K = 8104, t₀ = exp(exp 100)):
`c = 1/10⁹`, `T₀ = exp(exp(8·log(20000·8104) + 1100)) + exp(exp 100) + 3`.
Arithmetic: `8·log(20000·8104) + 1100 = 1251.23`, so
**T₀ ≈ exp(exp 1251.23)** — NOT exp(exp 100)-grade; exp(exp 100) is the
GROWTH threshold only, and it is dwarfed. loglog T₀ ≈ 1251.
Unconditional, sorry-free, axioms clean per flags VK-7/VK-9 entries
(flags.md:9673–9705) and commit f37a35b ("9136 green").

Naming flag: PowRegion.lean:16 says "Montgomery–Renyi (MR) gate"; the corpus's
MR is Matomäki–Radziwiłł (G: docs/blueprints/next-rung-scoping.md:269, 273 —
"sieve stack + BV + MR + log-Chowla"). "Montgomery–Renyi" is a docstring
misnomer; the freeze target ("MR-gate satisfying", flags.md:9675) is the
Matomäki–Radziwiłł gate.

### 1d. The siblings below/alongside
- **Classical dlVP region** (G: Salt/SW/ZetaZeroFree.lean:235–237):
  `zeta_zero_free_region : ∃ c₃ > 0, ∀ ρ, ζ ρ = 0 → 1/2 ≤ ρ.re →
   ρ.re ≤ 1 − c₃/log(|ρ.im| + 2)`, `c₃ = min(1/75712, ε₀·log 2)` with ε₀ the
  existential fixed-strip constant. **NO height threshold — covers ALL t
  including t = 0.**
- **Littlewood region** (G: Salt/Vk/Littlewood.lean:409): width
  `c·loglog/log`, `c = 1/88214`, own T₀ = exp(exp(log C + 400))-grade
  (flags.md:9641–9644). Strictly between dlVP and pow; for MR purposes
  superseded by pow above T₀ and by dlVP below (it buys nothing extra in the
  split — its own threshold is also astronomical).
- **1/ζ, dlVP-grade, ALL t** (G: Salt/SW/ZetaInvShallow.lean:116–118):
  `zeta_inv_shallow : ∃ c₄ > 0, C > 0, ∀ σ t, 1 − c₄/log⁹(|t|+2) ≤ σ → s ≠ 1 →
   ‖ζ(σ+it)⁻¹‖ ≤ C·log⁷(|t|+2)`. Built FROM `zeta_zero_free_region` + compact
  pole-patch (|t| < 2 branch) — the landed template for region→consumption.

## 2. What MR-shaped consumption the corpus DEMANDS (the demand side, landed)

The terminal surface `log_chowla_two_final`
(G: Salt/Entropy/Chowla/SpineFinal.lean:260–272) is conditional ONLY on
`MRTUniformity R δ` (δ ≤ δ₀ = R.eps/(2K)) plus the explicit entropy-decrement
residuals (t, g, shellError budget). `MRTUniformity R δ`
(G: Salt/Entropy/Chowla/MRTDoor.lean:48–50):
`∀ H ∈ [R.Hlo, R.Hhi], ∀ α : ℝ, ∫ ‖windowExpSum H n α‖ d(logMeasure R.x R.ω) ≤ δ·H`
— Tao 1509.05422 Prop 2.4, a THEOREM in the literature (from MRT 1503.05121),
OPEN in the corpus. Weakened Ξ_H-restricted form `MRTUniformityXi` +
`mrtUniformity_implies_xi` also landed (MRTDoor.lean:109–119). Nothing in
Salt/ proves either predicate (G: grep — consumers only, in SpineClose/
SpineFinal/Theorem23Shell/TowerDischarge).

Scales at the door (G): `logMeasure x ω` supported on `(x/ω, x]`
(LogMeasure.lean:79), probability measure for x, ω ≥ 2 (LogMeasure.lean:70);
regime has `Hlo ≥ 4·10⁶` (Regime.lean:85), `Hhi ≤ x/ω` (Regime.lean:88), and the
builder `chowlaRegime_exists_param` takes an arbitrary floor — x can be pushed
arbitrarily large (SpineFinal.lean:295–297).

**So the MR campaign's obligation is: prove `MRTUniformity R δ` for one
sufficiently-large built regime.** That is where the region gets consumed.

## 3. How the region is consumed (the classical chain) — M unless marked

[M] MRT Prop 2.4's proof = circle-method reduction + the Matomäki–Radziwiłł
short-interval theorem for twisted Liouville sums. Analytic core: Dirichlet
polynomials of length ~x, Parseval over frequencies |t| up to x-grade
(x/H·log-powers for the minor-arc L² part; |t| ≤ log^{O(1)}x major arcs). The
ζ-inputs:
1. **Pretentious/Halász lower bound**: 𝔻(λ, n^{it}; x)² = Σ_{p≤x}(1 − Re p^{−it})/p
   ≥ loglog x − log|ζ(1 + 1/log x + it)| − O(1). Needs an UPPER bound on
   log|ζ| just right of σ = 1, UNIFORM over |t| ≤ x-grade.
2. **Region→log ζ bridge** [M]: inside a zero-free region of width η(t), the
   Landau/Borel–Carathéodory machinery gives ζ'/ζ ≪ 1/η and hence
   log|ζ(1+it)| ≤ log(1/η(t)) + O(1). With the pow width
   η = c/((log t)^{3/4}(llt)³): log(1/η) = (3/4)·loglog t + 3·logloglog t + O(1),
   so 𝔻² ≥ (1/4 − o(1))·loglog x uniformly for |t| ≤ x. **Any θ < 1 wins a
   positive proportion; θ = 3/4 gives asymptotic proportion 1/4.** This is the
   MR gate the freeze named — the SHAPE (θ < 1), not the constants.
3. With ONLY dlVP-grade inputs (what §1d supplies today):
   log|ζ(1+it)| ≤ loglog t + O(1) ⇒ 𝔻² ≥ loglog x − loglog t − O(1), which
   DIES at t ~ x. dlVP suffices only for |t| ≤ exp((log x)^β), β < 1. **This
   is exactly why the pow region is load-bearing for MR and nothing weaker is.**
4. The other MR ingredient [M]: continuous-t Dirichlet-polynomial L² mean value
   `∫₀ᵀ |Σ aₙ n^{it}|² dt ≪ (T + N)·Σ|aₙ|²` + a Ramaré-identity factorization.
   Halász's theorem itself is ALSO consumed (its proof needs only σ > 1 zeta
   facts, not the region).

## 4. Honest t-range bookkeeping (the core deliverable)

| t-range | supplier (G) | width there | MR pretentious yield |
|---|---|---|---|
| all t (incl. 0, compact ranges) | `zeta_zero_free_region` (ZetaZeroFree.lean:235) + `zeta_inv_shallow` (ZetaInvShallow.lean:116) | c₃/log(|t|+2) | log ζ ≤ loglog t + O(1) |
| t ≤ T₀ ≈ exp(exp 1251) | same classical region | same | loglog t ≤ loglog T₀ ≈ **1251** ⇒ 𝔻² ≥ loglog x − O(1251): an ABSOLUTE additive constant — better than needed |
| t ≥ T₀ | `zeta_zero_free_region_pow` (GrowthPow.lean:1044) | c/((log t)^{3/4}(llt)³) | log(1/η) = (3/4)loglog t + 3 logloglog t ⇒ 𝔻² ≥ (1/4 − o(1))loglog x up to t = x |

- **Does T₀ = exp(exp ~1251) hurt?** For any ASYMPTOTIC consumer: NO. The
  T₀-split costs one additive constant ≈ loglog T₀ ≈ 1251 in the 𝔻² lower
  bound, absorbed once loglog x ≫ 1251, i.e. x ≥ exp(exp(~5000))-grade — and
  the spine's regime builder places no upper cap on x (G: SpineFinal.lean:295,
  Regime.lean floors are one-sided). The pow region's export being existential
  in (c, T₀) is exactly the right interface for this: consumers destruct and
  split.
- **EFFECTIVE consumers** (explicit finite-x MR, explicit PNT constants): the
  pow region is vacuous below exp(exp 1251) and its c = 1/10⁹ is design-grade;
  any explicit-x claim below exp(exp(exp-grade)) sees only the classical
  region. Also c₃ contains the EXISTENTIAL ε₀ (compactness, ZetaZeroFree.lean:238)
  — even the classical region is not fully effective. Price accordingly.
- **Small-t coverage need**: the door's α near rationals ↔ ζ-input near t = 0.
  Covered WITHOUT the pow region: (i) at t = 0, 𝔻(λ, 1; x)² = Σ 2/p =
  2 loglog x needs only prime reciprocal sums (corpus: `primeWindow_sum_inv_ge`,
  G: SpineFinal.lean:275); (ii) compact |t| < 2 is `zeta_inv_shallow`'s
  pole-patch branch (G: ZetaInvShallow.lean:115). No consumer starves below T₀.
- Shape crossover sanity: pow beats dlVP width iff (llt)³ ≤ (log t)^{1/4}·(c/c₃)
  ⟺ roughly loglog t ≥ 12·logloglog t + O(1); at loglog t = 1251,
  12·logloglog t ≈ 85.6 ≪ 1251 — the pow width genuinely dominates from T₀ on
  (modulo the existential c₃; for any fixed c₃ this holds at T₀ unless
  ε₀ < exp(−300)-grade).

## 5. Supply inventory for an MR campaign (what exists vs what's missing)

**HAVE (G):**
- Demand side complete: MRTDoor + spine + `log_chowla_two_final` (§2).
- Pow region unconditional (§1c) + classical region all-t (§1d) — the two-range
  ζ-region supply is COMPLETE for the asymptotic chain.
- Region→consumption template at dlVP grade: `zeta_inv_shallow` →
  `MobiusRateClose` (trophy `MmuRate`, G: MobiusRateClose.lean:1054) — the
  contour/absorption pattern a pow-grade analogue would copy.
- Borel–Carathéodory/Landau partial fractions: `entire_norm_logDeriv_sub_sum_scaled`
  (G: Vk/Landau.lean:11–12, exported Vk/All.lean:93) + the SW DH* stack.
- Large-sieve stack Salt/LS/ (Gallagher pointwise = Sobolev lemma,
  G: LS/Gallagher.lean:38; BDH, CharLS, Conductor) — ingredients for mean
  values, character-flavored.
- ExpSum/ (van der Corput, Kusmin) and Vmvt/ (Vinogradov integral) — the
  exponential-sum engines.

**MISSING (G: greps this session):**
- Halász anything: `grep -riE 'halasz|pretentious' Salt/` hits ONE prose
  comment (HReduce.lean:56). No pretentious distance def, no Halász theorem,
  no mean-value-of-multiplicative-function bound.
- The region→log ζ/1/ζ bridge at POW grade (the pow analogue of
  `zeta_inv_shallow`: width (log t)^{3/4}(llt)³-shaped strip, price
  (log t)^{3/4}-grade). §3.2 is entirely unformalized. This is the FIRST
  missing rung and it consumes the landed region directly.
- Continuous-t Dirichlet polynomial L² MVT (∫|Σaₙn^{it}|²): not found (LS is
  character/Sobolev-flavored; grep-confidence, not exhaustive).
- Short-interval multiplicative theorem, Ramaré identity, the MRT twist.
- **The pow region currently has ZERO consumers outside Salt/Vk/**
  (G: grep `zeta_zero_free_region_pow|ZetaGrowthPow` — no hits outside Vk).
  It is landed supply awaiting the MR campaign.

## 6. One-line verdict

The landed `zeta_zero_free_region_pow` is exactly the MR-gate shape (θ = 3/4 <
1) and its astronomical concrete threshold T₀ ≈ exp(exp 1251) is harmless to
every asymptotic MR-shaped consumer because the ALL-HEIGHT classical region
(`zeta_zero_free_region`, no threshold) fills [0, T₀] at the cost of one
additive constant ≈ 1251 in the pretentious lower bound; what the MR campaign
lacks is not region supply but the ENTIRE Halász/pretentious middle — starting
with the pow-grade region→log ζ bridge, for which the dlVP-grade template
(`zeta_inv_shallow` → `MmuRate`) is already landed and copyable.
