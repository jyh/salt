# The SW rung — discharging the gate (`sw`)

*Fable, 2026-07-12. THE project's remaining gate: prove
`Salt.BV.SiegelWalfisz` (`Salt/BV/Defs.lean` — the frozen `∀A ∀C ∃K` ψ-AP
statement). The day this lands: `bounded_gaps_of_siegelWalfisz` becomes
UNCONDITIONAL bounded prime gaps; k=105 → gaps ≤ 600 unconditional
(CertEval probe GO); future Chen-mod-SW → Chen unconditional. Route
recon: 3 scouts (`wf_4c323c06-8f9`), UNANIMOUS — pretentious route
provably capped below ∀A (Halász floor (log x)^{-2}); pure-elementary
dead (Bombieri–Wirsing unformalized-anywhere + the Siegel wall does not
dissolve); classical contour FEASIBLE with mathlib far readier than
folklore (Borel–Carathéodory full, Jensen/Nevanlinna, 3-4-1 shape,
LSeries positivity engine). Siegel is UNAVOIDABLE (∀C forces it — both
independent scouts confirm); Goldfeld's proof + mathlib positivity makes
it C+, not D. Adversarial pass 2026-07-12: error #14 caught (the
de-smoothing order — sandwich needs monotonicity, ψ(x,χ) oscillates ⇒
orthogonality-first, folded below); MellinInversion CONFIRMED serving
the kernel (all three hypotheses check for `(1−·)₊`); the S1 exponent
bookkeeping and the χ₀ main-term chain re-derived correct. Multi-session arc: this window = blueprint + gate +
opening waves; the corpus is cumulative.*

## THE FABLE AMENDMENT (de-risking the keystone): Riesz smoothing

Scout A's blocker was effective truncated Perron (sharp cutoff, C+/D,
no scaffold). STRUCK — we never touch the sharp cutoff:

Work with **`ψ₁(x, χ) := Σ_{n} Λ(n)·χ(n)·(x − n)₊`** (the Riesz mean).
Its Mellin kernel `x^{s+1}/(s(s+1))` has `1/|s|²` decay — vertical
integrals converge ABSOLUTELY (no truncation bookkeeping), and the
kernel target `y ↦ (1−1/y)₊` is CONTINUOUS — the exact case mathlib's
`MellinInversion` machinery serves (the discontinuous step is what it
can't do). **De-smoothing (CORRECTED, error #14 — the adversarial pass confirmed
Fable's own suspicion):** the sandwich needs MONOTONICITY, and
`ψ(x,χ)` is ℂ-valued/oscillating — so S6's order is
**orthogonality FIRST**: fold `ψ₁(x;q,a) := (1/φq)·Σ_χ χ̄(a)·ψ₁(x,χ)`
(the ψ₁-analog of the landed MaxReduction identity — a REAL carrier
with nonneg terms, `ψ₁(·;q,a) = ∫₀^· psiAP`, convex, psiAP
nondecreasing), THEN the first-difference sandwich
`(ψ₁(x)−ψ₁(x−h))/h ≤ psiAP(x) ≤ (ψ₁(x+h)−ψ₁(x))/h` at
`h = x/(log x)^{A+2}`: width `h/φq + O(x²E/h)`, and
`E = e^{−c√log x}` beats every log power.

## Doctrine

Iron rules per `CLAUDE.md`; constants explicit-or-∃-before-use;
`#audit_axioms` from the first commit; namespace `Salt.SW`, files
`Salt/SW/*.lean`, branch `sw` (off main after the twinbar/T7 merge).
The INEFFECTIVE constant in Siegel is intrinsic and FINE (the gate's K
is a top-level ∃ — recorded in Defs.lean's design). NO weakening of the
gate to bounded C (Iron Rule 1 — the temptation is flagged by Scout C;
the effective-only route reaches C < 2 and is NOT the theorem).

## The DAG (waves; est. ~40–60 nodes total, NO D-node after the amendment)

| wave | content | class | key mathlib seeds |
|---|---|---|---|
| S0 | Carriers: `ψ₁(x,χ)` (ℂ) AND the REAL AP carrier `ψ₁(x;q,a)` (matching psiAP's Icc/residue conventions) + the orthogonality fold identity + the MONOTONICITY/convexity lemma (`vonMangoldt ≥ 0` ⇒ psiAP nondecreasing, ψ₁ = its integral — the hypothesis the sandwich consumes); `−L'/L = LSeries Λχ` on Re s > 1; contour conventions | B | `DirichletContinuation`, `LSeries` API |
| S1 | **The smoothed Mellin/Perron identity**: `ψ₁(x,χ) = (1/2πi)∫_{(c)} x^{s+1}/(s(s+1))·(−L'/L)(s,χ) ds` (at `c > 1` — the composite needs Dirichlet-series absolute convergence; the kernel identity alone needs only c > 0) — kernel identity `(1/2πi)∫ y^s/(s(s(+1))) ds = (1−1/y)₊` via mathlib `MellinInversion` (continuous target!) or the benign two-pole contour (1/|s|² arcs vanish cleanly); sum↔integral swap by dominated convergence (absolute kernel) | C (the de-risked keystone) | `MellinInversion`, `integral_boundary_rect_*` |
| S2 | **L'/L partial fractions + zero counting**: `−L'/L(s) = Σ_ρ 1/(s−ρ) + O(log q(|t|+2))` near the 1-line; #zeros in disks via Jensen/Nevanlinna; Borel–Carathéodory for the log-derivative bounds | C-cluster | `JensenFormula.AnalyticOnNhd.sum_divisor_le`, `BorelCaratheodory` |
| S3 | **Quantitative zero-free region uniform in q**: the 3-4-1 argument made quantitative (`1−β ≥ c/log(q(|t|+2))`, all χ, exceptional real-zero caveat) + Landau–Page (≤1 exceptional zero; one exceptional modulus per range) | C-cluster | `Nonvanishing.lean`'s 3-4-1 shape, S2 |
| S4 | **Siegel via Goldfeld**: `L(1,χ) ≫_ε q^{−ε}` (ineffective ∃) via the 4-fold product `ζ·L(χ₁)·L(χ₂)·L(χ₁χ₂)` + the positivity-of-Taylor engine; ⇒ `1−β ≥ c(ε)/q^ε`. ⚠️ NEW SUB-NODE (verify pass): the 4-fold nonneg-COEFFICIENTS input — mathlib's `zetaMul_nonneg` is 2-fold/single-quadratic-χ only; the two-distinct-real-characters product needs its own Euler-factor positivity lemma (the ENGINE `LSeries_positive`/`iteratedDeriv_LSeries_alternating` is character-agnostic and ready) | C+ | `LSeries_positive`, `iteratedDeriv_LSeries_alternating`, NEW: 4-fold nonneg |
| S5 | **The contour shift**: move S1's line into the S3 region; residues-lite hand-built (poles ONLY at s=1 for χ₀ and the exceptional β — mathlib has no residue theorem; build from Cauchy-for-circles + rectangle splits); bound the shifted integrand by S2+S3 ⇒ `ψ₁(x,χ) = [x²/2]_{χ=χ₀} − [x^{β+1}/(β(β+1))]_{exc} + O(x²e^{−c√log x})` uniform q ≤ (log x)^C via S4 | C-cluster (the assembly) | S1–S4 |
| S6 | **Orthogonality THEN de-smooth** (order fixed — error #14). DESIGN FROZEN (Fable, 2026-07-12 night, post-S5): parameters `L := log x`, `T := exp(√L)`, `q ≤ L^C`, so `log(f(T+2)) ≤ 2√L` eventually; base `σ₀ := 1 − c₀/(8√L)`, `w := c₀/(16√L)` (σ₀−w ≥ 9/10 eventually ✓). Sub-nodes: **S6a** the imprimitive ψ₁-transfer (`ψ₁(x,χ) = ψ₁(x,χ₁) + O(log q·(log x)·√x-shape)` — the p ∣ q prime-power strip; Dirichlet-series algebra); **S6b** the per-character dispatcher: EVERY χ mod q gets a shifted bound via the case split — (i) χ₀: S5d at hzfζ from S3f (c₃ ∃-composes); (ii) primitive χ ≠ 1, no exceptional zero in the box: S5b clean (hzf from zero_free_region_all: any zero has Re ≤ 1 − c₀/(2√L) < σ₀ − w ✓ 3/16 < 1/2); (iii) the Landau-exceptional β₁ ≥ σ₀ − w (real quadratic χ only; all OTHER real zeros ≤ 1 − c₁/((C+1) log L) ≪ σ₀ − w by S3e): the ADAPTIVE BOX — if β₁ < σ₀ − w clean, else re-base `σ₀'' := β₁ − 2w` (≥ σ₀ − 3w, still 1 − O(1/√L) ✓, and hβsep σ₀''+w = β₁−w ≤ β₁ ✓) and use S5c; **S6c** the fold (`psi1_fold`) + the exceptional-term Siegel bound (`x^{β₁+1}/(β₁(β₁+1)) ≤ x²exp(−(1−β₁)L)`; `siegel_theorem` at ε := 1/(4C): (1−β₁)L ≥ C_ε L^{3/4}` — beats every log power; Page/S4c: at most one exceptional modulus per range if needed for uniformity); **S6d** the REAL first-difference sandwich (`psi1AP_sandwich`) at `h := x/(log x)^{A+2}` + the gate-statement plumbing → **`siegelWalfisz_holds : SiegelWalfisz`** and `bounded_gaps` UNCONDITIONAL | B/C-cluster | S5b/S5c/S5d + S3d/S3e/S3f + S4b⁗/S4c + S0 |

## PB-floors
- Every wave lands standalone value (S2/S3 are mathlib-first zero-theory;
  S4 is the first Siegel anywhere). The rung is DONE at S6.
- If S1's MellinInversion consumption fights: the direct two-pole contour
  for the FIXED kernel is the fallback (benign: quantitative arcs from
  1/|s|²).
- If S5's residues-lite balloons: PB-floor = ψ₁ bound with the residue
  extraction as ONE stated lemma + flag.
- Multi-session by design: each wave commits landed; future sessions
  resume from the blueprint + flags.

## Statement-design decisions reserved to Fable
S1's exact identity packaging; S3's region shape; the S5/S6 interface;
NO gate changes ever (frozen in Salt/BV/Defs.lean since the BV rung).
