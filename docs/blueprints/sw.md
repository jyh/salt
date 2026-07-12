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
it C+, not D. Multi-session arc: this window = blueprint + gate +
opening waves; the corpus is cumulative.*

## THE FABLE AMENDMENT (de-risking the keystone): Riesz smoothing

Scout A's blocker was effective truncated Perron (sharp cutoff, C+/D,
no scaffold). STRUCK — we never touch the sharp cutoff:

Work with **`ψ₁(x, χ) := Σ_{n} Λ(n)·χ(n)·(x − n)₊`** (the Riesz mean).
Its Mellin kernel `x^{s+1}/(s(s+1))` has `1/|s|²` decay — vertical
integrals converge ABSOLUTELY (no truncation bookkeeping), and the
kernel target `y ↦ (1−1/y)₊` is CONTINUOUS — the exact case mathlib's
`MellinInversion` machinery serves (the discontinuous step is what it
can't do). **De-smoothing:** `ψ(x) − ψ(x−h) ≤ (ψ₁(x+h) − 2ψ₁(x) +
ψ₁(x−h))/h`-style finite differences at `h = x/(log x)^{A+2}`: the
smoothed error `x²·exp(−c√log x)` beats every log power, so each `A` is
bought by choosing `h`. Node W6.

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
| S0 | Carriers: `ψ₁(x,χ)` (ℂ), the de-smooth combinatorics stated, `−L'/L = LSeries Λχ` identity on Re s > 1 (mathlib `LSeries`/PrimesInAP shapes), the contour-rectangle conventions | B | `DirichletContinuation`, `LSeries` API |
| S1 | **The smoothed Mellin/Perron identity**: `ψ₁(x,χ) = (1/2πi)∫_{(c)} x^{s+1}/(s(s+1))·(−L'/L)(s,χ) ds` — kernel identity `(1/2πi)∫ y^s/(s(s(+1))) ds = (1−1/y)₊` via mathlib `MellinInversion` (continuous target!) or the benign two-pole contour (1/|s|² arcs vanish cleanly); sum↔integral swap by dominated convergence (absolute kernel) | C (the de-risked keystone) | `MellinInversion`, `integral_boundary_rect_*` |
| S2 | **L'/L partial fractions + zero counting**: `−L'/L(s) = Σ_ρ 1/(s−ρ) + O(log q(|t|+2))` near the 1-line; #zeros in disks via Jensen/Nevanlinna; Borel–Carathéodory for the log-derivative bounds | C-cluster | `JensenFormula.AnalyticOnNhd.sum_divisor_le`, `BorelCaratheodory` |
| S3 | **Quantitative zero-free region uniform in q**: the 3-4-1 argument made quantitative (`1−β ≥ c/log(q(|t|+2))`, all χ, exceptional real-zero caveat) + Landau–Page (≤1 exceptional zero; one exceptional modulus per range) | C-cluster | `Nonvanishing.lean`'s 3-4-1 shape, S2 |
| S4 | **Siegel via Goldfeld**: `L(1,χ) ≫_ε q^{−ε}` (ineffective ∃) via the 4-fold product `ζ·L(χ₁)·L(χ₂)·L(χ₁χ₂)` nonneg coefficients + the positivity-of-Taylor engine; ⇒ `1−β ≥ c(ε)/q^ε` | C+ | `zetaMul_nonneg`, `LSeries_positive`, `iteratedDeriv_LSeries_alternating` |
| S5 | **The contour shift**: move S1's line into the S3 region; residues-lite hand-built (poles ONLY at s=1 for χ₀ and the exceptional β — mathlib has no residue theorem; build from Cauchy-for-circles + rectangle splits); bound the shifted integrand by S2+S3 ⇒ `ψ₁(x,χ) = [x²/2]_{χ=χ₀} − [x^{β+1}/(β(β+1))]_{exc} + O(x²e^{−c√log x})` uniform q ≤ (log x)^C via S4 | C-cluster (the assembly) | S1–S4 |
| S6 | **De-smooth + orthogonality**: ψ₁ → ψ per (q,a) via finite differences at A-tuned h; the χ-orthogonality inversion to `psiAP` (the landed `Salt/BV/SWChar`/`MaxReduction` machinery REVERSED — mostly present); land **`siegelWalfisz_holds : SiegelWalfisz`** and the three unconditional headliners (`bounded_gaps` unconditional!) | B/C | landed corpus |

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
