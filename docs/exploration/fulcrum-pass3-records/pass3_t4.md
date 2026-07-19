# PASS-3 T4 — THE C⁽¹⁾ LEDGER FREEZE (S2 kill-check)

Date: 2026-07-19. One session, no Lean. Sources: docs/exploration/fulcrum_audit_source.md
(the F-horn audit), H-B 1983 PDF re-read at pp.195, 223 (PDF pp.3, 31), fulcrum-pass2.md:53
(S2 clause) + :71 (T4 charge), Salt/Fulcrum/Basic.lean (F3). Labels: GROUNDED = file:line /
page:eq re-verified this session; AUDIT-DERIVED = my forcing analysis on grounded mechanism;
MEMORY marked explicitly.

## 0. The 250-vs-300 adjudication (audit :166 vs :183) — RESOLVED, NOT a contradiction

GROUNDED p.195 (PDF p.3, re-read): Theorem 1 is uniform for q²⁵⁰ ≤ x ≤ q⁵⁰⁰ (1.13);
Corollary 1 is uniform for q³⁰⁰ ≤ x ≤ q⁵⁰⁰. GROUNDED p.223 (PDF p.31, re-read, §8):
N(2x) − N(x) = 𝔖C(α)x(log x)⁻² + O(xL⁻²(log log η)⁻¹) uniformly for q²⁵⁰ ≤ x ≤ ½q⁵⁰⁰;
adding the sub-q²⁵⁰ ranges trivially costs +O(q²⁵⁰); "If we now take X in the range
q³⁰⁰ ≤ X ≤ q⁵⁰⁰, and sum for x = X/2, X/4, X/8, …, we obtain Corollary 1."

So: TWO windows for TWO objects. Audit :166 (x ≥ q²⁵⁰, ~q¹⁰ slack at (6.11) p.218) is
THEOREM 1's analytic edge — the Kloosterman/Weil jaw. Audit :183 ([q³⁰⁰, q⁵⁰⁰]) is
COROLLARY 1/2's HARVEST window — the 250-edge plus dyadic-truncation bookkeeping
(q²⁵⁰ tail must sit under X(log X)⁻²·(log log η)⁻¹, so the cumulative edge rises to a
clean 300). Both audit lines are correct in their own scope. FREEZE RULE: any downstream
numeral reuse must cite Thm-1-window (250) for engine-interior estimates and Cor-1-window
(300) for twin-yield claims; per-triple yield lives ONLY in [q³⁰⁰, q⁵⁰⁰]. The q¹⁰ slack
propagates 250→~240 hence 300→~290 at best: sub-polynomial, window edges NOT in play for
the dial (both bind for independent reasons — Weil below, zero-reach above; audit §6).

## 1. THE CONSTANT, verbatim

GROUNDED p.223: A := Corollary 1's implied constant (effective, depends on α_i, β_i only —
p.195); then C⁽¹⁾ = exp exp{2A(𝔖C(α))⁻¹}. The outer exp-exp is the INVERSION of Cor 1's
relative error A(log log η)⁻¹/(𝔖C(α)) < ½ ⟺ η ≥ exp exp{2A(𝔖C(α))⁻¹}. So the shape of
C⁽¹⁾ = the shape of the final error rate; the ONLY other ingredients (2, 𝔖C(α)) are fixed.

## 2. THE FROZEN CONSUMPTION LEDGER (η-contact points, pp.198–224), ABSORBABLE vs NOT

"ABSORBABLE" = the constant at this point can be fed by weaker/better engine constants
(ShiuCore / Weil-bank / T-BAL) — which by §1 moves ONLY the inner exponent 2A/𝔖C(α).

| # | Point | What is consumed | Absorbable? |
|---|---|---|---|
| L3-i | Lemma 3 (pp.206–207): −1/(s−β₀) dominates −L′/L at s = 1+L⁻¹ | existence of β₀ — the hypothesis itself | NOT (no engine replaces the zero) |
| L3-ii | Lemma 3: D–H repulsion r₀ ≫ L⁻¹log η (Jutila Thm 2) | quality, LOG-only | constant YES (T-BAL: dh_repulsion_ordered is exactly this artillery, in-house, log-shape — ledger A2); SHAPE NOT (log-order is what D–H-type methods give; polynomial-in-η repulsion is on no staged menu — MEMORY for literature optimality) |
| L3-iii | Prachar disc count ≪ 1 + rL | unconditional | YES, marginal |
| L2 | Lemma 2 (pp.201–203): amplification e^{Az₀} (Λ̃-vs-Λ price, sieve products over χ(p)=1 primes) | none directly; multiplies L3's rate | exponent-constant YES (ShiuCore-grade); the exponential-in-z₀ SHAPE is the Λ̃ construction itself — NOT |
| L7 | Lemma 7 (pp.207–210): L′/L(1,χ) = ηL + O(L(log η)^{−1/2}); κS₁ | explicit formula + D–H σ₀ + Jutila density (4.9, unconditional) | the (log η)^{−1/2} here is FED BY Lemma 3; L7's own zero-sum errors are already POLYNOMIAL in η (audit :70, (4.11): O(Lη^{−A})) — so L7 adds no independent wall; constants YES |
| FL | Rosser dim-4 fundamental lemma e^{−z₀/4}; assembly B²e^{−z₀/4} vs (ηL)² (p.200) | none; same side of the balance as e^{Az₀} | YES (Iwaniec-constant grade), inner only |
| ASM | Assembly O(BL)/(L′/L)² = O(1/η) (p.200) | quality, POLYNOMIALLY | harmless; this is the architecture's best-case floor — by itself it would demand only η ≥ const |
| K | Lemma 5 / §§5–7 Kloosterman (pp.210–223), edge (6.11) | NO η consumed (audited: no β₀/η anywhere in §§5–7) | YES (Weil-bank) but WINDOW-only (~q¹⁰ slack), zero dial contact |
| C1 | Cor 1 dyadic tail O(q²⁵⁰), edge 300 (p.223) | none beyond Thm 1 | bookkeeping |
| C2 | Cor 2 inversion (p.223) | image of the final rate | not independently absorbable |

## 3. THE SHAPE-FORCING ARGUMENT (the kill)

The cascade (GROUNDED audit §5, p.200): final error = z₀⁻¹ with z₀ = A log log η, forced by
the two-jaw balance e^{Az₀}·r(η) ≤ z₀⁻¹ where r(η) = Lemma 3's rate. Every absorbable entry
above moves A, the D–H constant, or the Weil window — never r's SHAPE. Two escapes exist, and
only two:

(a) r(η) polynomial (η^{−δ}). Then z₀ ≈ (δ/A)log η, final error (log η)⁻¹, C⁽¹⁾ = exp{2A/(δ𝔖)}
— the exp peels. Blocked: r's log-shape source is L3-ii's consumption MODE, and — the sharper
point (AUDIT-DERIVED) — Lemma 3's object Σ_{p≤x, χ(p)=1} p⁻¹log p is SCALE-UNIFORM down to
p = 2, while the zero disciplines χ only at scales log y ≫ L/log η (below that, the explicit
formula's other-zero error e^{−(1−σ₀)log y} does not bite even under ARBITRARY repulsion
strength — repulsion improves σ₀ only inside a factor that is inert at small scales). The
sub-q^{c/log η} scales alone contribute ≍ L/log η to the sum: a power-of-log-η floor
INDEPENDENT of every constant in the ledger. Consistent with the audit's own ceiling finding
(:112–113): even η → ∞ per triple cannot beat (log log η)⁻¹ — quality is not the bottleneck,
the consumption mode is.

(b) Remove the e^{Az₀} amplifier. It is the price of Λ̃ ≈ Λ (Lemma 1/2, the χ(p)=1 sieve
products) — i.e. of the entire §2 skeleton. Removing it is a different engine, not a constant
feed (that hypothetical is the unbuilt HB-ENGINE campaign, out of T4's scope and priced
elsewhere).

CONCLUSION: exp-exp is FORCED for this architecture. ShiuCore/Weil-bank/T-BAL spend moves
C⁽¹⁾ from exp exp{2A/𝔖} to exp exp{2A′/𝔖} — numerically enormous, shape-inert. The S2 KC
criterion (fulcrum-pass2.md:53,71: "Forced exp-exp shape = kill") fires. No WP2 run.

## 4. THE F3 SATURATION CLAUSE (frozen form)

GROUNDED Salt/Fulcrum/Basic.lean:93–94 (hC : 2 ≤ C·c₀) with mechanism at :126–137: at
C ≥ 2/c₀ the ball radius 1/(C·log q) ≤ ½ forces |Im ρ| + 2 < 3 ≤ q, so a non-real witness
fires the ZFR disjunction (χ² = 1 ∨ Im ρ ≠ 0) into the contradiction q ≤ |Im ρ| + 2 — the
zero is REAL with ½ ≤ Re ρ < 1 (fulcrum_zero_real). CLAUSE: every dial gain cashes out only
down to C⋆ = max(C⁽¹⁾, 2/c₀); below C = 2/c₀ the reality derivation FAILS, F-witnesses need
not be real zeros, the limit-shape dichotomy must be restated on REAL zeros, and ¬F(C) no
longer pins η < C⁽¹⁾ (fulcrum-pass2.md:53, judge-verified). Calibration: c₀ = 1/126848
(docstring-grade, Basic.lean:169 per ledger scope note) puts the floor at 2/c₀ ≈ 2.5×10⁵ ≈
2^18. Distance: even a fantasy inner exponent 2A/𝔖 = 10 gives C⁽¹⁾ ≈ exp(e^{10}) ≈ e^{22026}.
STATUS: the clause is REAL but UNREACHED — it is the terminus of a dial that §3 shows cannot
start. It becomes the binding object only after an exp-peel, which is dead. (Upside corner
unchanged: both-horn overlap; understates, never overstates twin content.)

## 5. VERDICT

KILLED. The exp-exp shape of C⁽¹⁾ is forced; the ~20–30% "dial moves ≥ exp-order" prior
(fulcrum-pass2.md:53) resolves NEGATIVE. Bank the wall-theorem candidate (see assault brief).
Residual honest value (NOT a Pass-3 target): within-shape A-reduction still serves both horns
(S2's shared-C⋆ note) — engineering, ledger-recorded, unpriced here.
