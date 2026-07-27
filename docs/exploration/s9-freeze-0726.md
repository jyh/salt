# S9 freeze — the §4 major-arc port at g = λ (2026-07-26)

Source: S9DESIGN-SCOPE (read-only, MRT `1503.05121v3` pp. 10–16 + 22–28 rendered;
GS `math/9911246` p. 22; chowla.txt :743–750; the landed corpus). Maestro-verified
cites: `Renormalise.lean` (:1003/:749, 0 sorries, All.lean :79, consumed
`BallSup.lean` :88/:142), the census row `hsup-design.md` :1017–1019, `mr-freeze.md`
:19/:49, `s8-freeze.md` :61, `BigXiArc.lean` :137–178 (the NearRat exit — P-1 real).
Refuter pass: dispatched same evening (verify-posture law); verdicts appended below.

## HEADLINE — the design block is DISCHARGED

The census row's "⚠ A.8 SIGN DEFECT — verbatim port UNPROVABLE, design block
first" is dead twice over:

1. **Wrong lane.** (A.8) is Lemma A.7, inside the 𝒯₀ leg of Prop A.3 → Thm A.2 →
   Thm A.1 (MRT pp. 22–28) — the H-block, one lane up. S9 is the **§4 major-arc
   reduction** (pp. 14–16), which consumes Theorem A.2 as an interface and never
   touches (A.8).
2. **Already repaired and landed.** `Salt/MR/Renormalise.lean`: `renormalise`
   (:1003 — GS 7.1 itself), `renormalise_shifted` (the MRT-shaped corollary with
   the CORRECT sign `X^{i(t₁−t)}/(1+i(t₁−t))`), `renormalise_factor_norm(_le)`,
   `renormaliseConst` (:749). The printed (A.8) is the complex conjugate of the
   provable identity — false as an equality (a genuine phase, not a constant);
   the in-file header records the re-derivation and the refusal. The scoper
   re-derived independently two ways (via GS 7.1 at F(n) := g_𝒥(n)f(n)n^{−it₁},
   α := t₁−t; and from scratch via ∫u^{−iβ}dA). Also on that page: A.7 binds
   𝓘 but displays g_𝒥; MRT's log(e+|α|) → loglog X substitution is legitimate
   only via t ∈ 𝒯₀ ⟹ |t−t₁| ≤ (log X)^{1/16} — that must be a Lean step.
   Flags :11779–11793 confirmed correct in every particular.

**⇒ No A.8 repair work exists in S9.** S9 is a straight port: [C], no D-node,
**3250–5200 ln, band centre ≈ 4200** (V9's 4000 stands as a number; the
composition changes: −IBP/−Dirichlet/−Möbius ≈ −800/−1300, +1_𝒮 insert and
+q-uniform quality ≈ +650/+1100).

## The source skeleton (byte-verified)

**Prop 2.4** (p. 10): X,H,W ≥ 10; (log H)⁵ ≤ W ≤ min{H^{1/250},(log X)^{1/125}};
g 1-bounded COMPLETELY multiplicative with (2.3) W ≤ exp(M(g;X,W)/3); d < W;
𝒮 := 𝒮_{P₁,Q₁,√X,X/d}, **P₁ := W^{200}, Q₁ := H/W³** (⚠ p. 16's Q₁ = H^{1/2}/W³
is Prop 5.1's — a different node; do not cross-wire). Conclusion ∀α:
∫|Σ_{x/d≤n≤x/d+H/d} 1_𝒮 g e(αn)|dx ≪ d^{−3/4}(log H)^{1/4}loglog H·W^{−1/4}·HX.

**§4 five steps**: (a) IBP (4.2) kills e(θn); (b) residue split mod q,
d₀ := (b,q), 1_𝒮(d₀m)g(d₀m) = g(d₀)1_{𝒮'}(m)g(m) — **needs d₀ ≤ q ≤ W < P₁**;
orthogonality (1/φ(q₀))Σ_χ χ(b₀)χ̄(m); (c) c.o.v. y = x/(dd₀), trivial cut
y ≤ X/W^{10} (costs HX/(dW³)), dyadic blocks X'; (d) **Theorem A.2 at η = 1/20**
per block; P₁ = W^{200} ⟹ non-M terms ≪ W^{−5/2}; Mertens M(gχ̄;X') ≥
M(g;X,W) − O(1) + (2.3) ⟹ exp(−M)M ≪ W^{−5/2}; (e) CS ⟹ ≪ W^{−5/4}H'X'/d₀;
re-sum ⟹ (4.1) ≪ HX/(dW^{1/4}).

## The λ-license — what deletes, what does not

chowla.txt :743–750 (Tao): at g₁ = g₂ = λ, c_p = 1, only major-arc α needed.

**DELETED (Zeno-deletions, budget zero):**
- §3 minor arcs entirely (already retired on the ladder).
- Theorem 2.3's Möbius layer (g = g₁∗h): λ is completely multiplicative, d = 1.
  mathlib: `ArithmeticFunction.liouville_apply_mul` — NO coprimality hypothesis.
- Dirichlet approximation: the door fires only at α = −ξ.val/H (MRTDoor :109–111)
  — exactly rational. Do not import DiophantineApproximation.
- **The phase-freezing subdivision is VACUOUS**: θ = 0 identically ⟹ (4.2)'s
  drift term is zero. mr-freeze :19's "FLAW-1 REPAIR BUILT IN" is dead work for
  the Ξ-restricted door (struck deliberately — see the flags entry; it revives
  only if the full `MRTUniformity` door is ever targeted, which the ratified
  SALVAGE posture refuses).

**NOT deleted — the kill-check (A.1 cannot replace A.2):** A.1's middle term is
(loglog h/log h)² ≈ (log H)^{−2+o(1)}; A.2's is (log h)^{1/3}/P₁^{1/6−η} ≪ W^{−5/2}
— a power of W by knob. The residue sum costs q ≤ W, so the per-block grade must
beat δ/W. At W = (log H)^{B₅}: A.2 route q·W^{−5/4} ≤ W^{−1/4} → 0 for EVERY B₅;
A.1 route needs B₅ ≤ 1 (triangle) or ≤ 2 (CS/Parseval), while Vinogradov with a
constant relative saving forces B₅ ≈ 8. REFUSED with arithmetic. **1_𝒮 and
P₁ = W^{200} are essential; S9 rides thm_A2′.** (This answers door-road-0724
:92–96's secondary kill-check.) The 1_𝒮 is re-inserted by hand against the
door's raw λ-window (M4-1), the L¹ analogue of MRT §3.1's assembly of A.1.

## PRECONDITIONS (settle before dispatch)

- **P-1 — S7's exit shape.** The sealed opener delivers `NearRat` ("ξ/H within
  arcRadius of a/q, q ≤ arcDen") — `BigXiArc.lean` :169. S9 needs the EXACT
  reduced denominator: `bigXi_denominator_le : ξ ∈ bigXi eps H →
  (H / Nat.gcd ξ.val H : ℕ) ≤ W`. The near form does NOT imply it (|a'q − aq'| ≤
  Wq'/H < 1 only when q' ≤ H/W, and q' | H may exceed that). Since ξ/H IS
  rational, the Vinogradov contrapositive should be stated directly on q'.
  **PIN THIS IN S7's L-ladder brief** (an added ladder stone) or S9 inherits a gap.
- **P-2 — W is chosen, not inherited.** W := max((log H)⁵, (log H)^{B₅(S7)}),
  subject to W ≤ (log X)^{1/125} — `regime_W_headroom_of_floor`
  (DoorDischarge :42) supplies it at W = (log H₊)⁵ with 34 orders of headroom;
  re-run its arithmetic at the S7 exponent before freezing B₅.

## The stone ladder (ids M4-* — NOT "S9-*": `Sec9Glue.lean` uses S9-1/2/3 for
MR §9; the collision would send an executor to the wrong file)

| id | statement-shape | class | ln |
|---|---|---|---|
| M4-0 | ‖windowExpSum H n (−ξ.val/H)‖ = ‖Σ_{m∈Ioc n (n+H)} λ(m)e(am/q)‖ at q := H/gcd(ξ.val,H); q ∣ H ⟹ e(am/q) constant on residues mod q | B | 200–300 |
| M4-1 | the 1_𝒮 insert: ‖Σ λe‖ ≤ ‖Σ 1_𝒮 λe‖ + #{n ∈ window : n ∉ MemS}; complement integrates ≤ (1+1/100)(2/M)·H·X via `card_not_memS_le_sum` ∘ `sum_ratioK_le` ∘ hsieve | B/C | 250–400 |
| M4-2 | residue split + d₀-dilation: λ(d₀m) = λ(d₀)λ(m); 1_𝒮(d₀m) = 1_{𝒮'}(m) GATED on d₀ ≤ q ≤ W < P₁ | C | 450–700 |
| M4-3 | character expansion: mathlib `sum_char_inv_mul_char_eq` → (1/φ(q₀))Σ_χ χ(b₀)χ̄(m); the conjugation bridge ONCE, named | C | 300–450 |
| M4-4 | y = x/d₀ c.o.v.; trivial cut y ≤ X/W^{10} (≪ HX/W⁹); dyadic cover, ≪ 10 log W/log 2 blocks | C | 350–550 |
| M4-5 | per-block plug: thm_A2′ at f := λχ̄, h := H/d₀, X := X′, η = 1/20, P₁ = W^{200}, Q₁ = H/W³; then L²→L¹ CS | C | 300–500 |
| M4-6 | quality supply M(λχ̄;X′) ≥ 3 log W UNIFORMLY over q₀ ≤ W — the q-uniform region transport off L(1,χ) ≫ q^{−1/2} (→ LandauL1) | C | 400–700 |
| M4-7 | arithmetic close: φ(q₀) cancels, Σ_b = q, Σ_{d₀∣q}, dyadic re-sum ⟹ ≪ HX/W^{1/4} | C | 350–550 |
| M4-8 | door glue B3/B4/B6: logMeasure singleton mass → dyadic Ioc split → 1/n ≍ 1/X′ → integer-sum ↔ integral (±1 each side = the 2/H) → Z ≥ log ω − 1 | C | 500–800 |
| M4-9 | exit `mrtUniformityXi_of_arc : … → MRTUniformityXi R δ`, ∀ξ OUTSIDE the integral | B | 150–250 |

**File plan**: `Salt/MR/MajorArc.lean` (M4-0..3; imports Sec9Glue, MRTDoor,
DirichletCharacter.Orthogonality); `Salt/MR/ArcBlocks.lean` (M4-4/5/7; thm_A2′
carried as an explicit HYPOTHESIS in the frozen shape — s8-freeze :17 / MRT
p. 21 — until ThmA2.lean exists; iron rule 1 in force); `Salt/MR/DoorGlue.lean`
(M4-8); M4-9 appended to `DoorDischarge.lean` (the Salt.MR → Salt.Entropy.Chowla
import direction is established there); M4-6 appended to `Salt/MR/SiegelArm.lean`.

## Zeno lines (budget zero)

λ complete mult. (`liouville_apply_mul`, unconditional); orthogonality
(`DirichletCharacter.sum_char_inv_mul_char_eq`; HasEnoughRootsOfUnity ℂ n
automatic); Dirichlet approx NOT NEEDED; the subdivision NOT NEEDED; the g₁∗h
layer NOT NEEDED; `harmonic_window_bounds`/`logMeasure_apply`/`window_one_le`
landed; `renormalise_shifted` landed — do not re-derive.

## Port-specific traps

- **The S9 name collision** (above — hence M4-*).
- **Sign discipline**: three conventions coexist — eIu = y^{+iu}
  (Renormalise :497), costwist (n^{it}), windowExpSum's additive e(α(i+1))
  1-indexed. GS is n^{+iα}, MRT n^{−it}, the door additive. The phase re-basing
  Σ_{i<H}λ(n+i+1)e(α(i+1)) = e(−αn)·Σ_{m=n+1}^{n+H}λ(m)e(αm) is modulus-1 but
  must be a NAMED lemma proved once. The kernel cannot police a sign consumed
  only through a modulus — exactly how (A.8) survived peer review.
- **Conjugate bookkeeping**: mathlib gives Σ_χ χ(a⁻¹)χ(b) = φ(n)·1_{a=b}; MRT
  print (1/φ)Σ χ(b₀)χ̄(m). One bridge lemma (χ(a⁻¹) = conj χ(a) + the role
  swap); never inline twice with opposite orientation.
- **d₀ ≤ q ≤ W < P₁ is a hypothesis, not a comment** (MRT p. 14 says so).
- **Half-open**: door window Ioc (x/ω) x; inner Ioc n (n+H); MRT closed windows.
  The ±1 boundary is the 2/H of M4-8 — budget it explicitly.
- **ξ.val casts**: ξ.val ∈ [0,H); (−ξ).val ≠ −(ξ.val); NeZero q₀ threading for
  q₀ ∣ q ∣ H.
- **norm_num/simp must never see closed calP/calQK** (they unfold to 2^65536);
  M4-1 touches the K-ladder — explicit `show`-rewrites.
- **Q₁ cross-wiring**: four Q₁'s live in the campaign (H/W³ here; H^{1/2}/W³
  Prop 5.1; h in thm_A1′; h at η = 1/150 in MR §9). Pin the per-block instance
  in each file header.
- **Do not restate thm_A2′** — hypothesis-carry until stone 4 lands it.

## Register + risk items

- s8-freeze :61 (the general-f interface question): **RESOLVED against source**
  — §4 p. 15 applies A.2 to gχ̄ as a general-f black box; the χ-quality lives
  outside S8, supplied by M4-6. Register item closed as confirmed.
- mr-freeze :49's "FORBIDDEN pre-staging: S9 statement pinning": discharged by
  fact — 1503.05121v3 is staged and this scope read §4/App-A/Prop 2.4 rendered.
- **hsieve** (Friedlander–Iwaniec Thm 6.17 + Mertens product bound,
  Sec9Glue :83–86): an UNOWNED named external now on TWO critical paths (the
  §9 glue and M4-1). Not priced anywhere on the door road. Needs an owner and
  a price — surfaced to JYH.
- The upstream exits (lemma14 kernel forms, seam_row_number) are NEUTRAL for
  S9 pricing — they shorten stones 1–4 of the door road, not §4. Two notes for
  the stone-4 wave: MRT p. 21 needs the single-h (V(x)) Parseval form, not the
  landed h₁/h₂-difference form; the exits' hMsup binder ∀T ≥ X/h₁ fires once
  at T = Tann.
