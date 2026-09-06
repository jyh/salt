# Wave B scout — HB 1983 §5 (pp. 210–214), Lemmas 9 + 11, (5.1)–(5.19), against the corpus

**PARTIAL, 2026-09-06.** Read-only: no Lean edited, no build run, the fleet lock never taken.
Every `file:line` below was read at salt main `4deb0c32`. Sibling of `wave-c-scout-0903.md` and
written to its pattern: the epistemic tiers are kept apart on every row —

- **[KERNEL]** a declaration that exists at the cited `file:line`, read this sitting;
- **[DESIGN]** priced here, not built and not proved;
- **[HB-NOTES]** transcribed from `docs/sources/hb1983-notes.md`, which is itself a transcription;
- **[SCOUT]** derived this sitting, by me, and no stronger than the reasoning shown.

**Absence rule** (QUEUE row 19i): a row says ABSENT only when the arms are listed *and* a sibling
control in the same convention was found; otherwise it says "not found under N arms, arms listed".

**Status: WHOLE. §1 and §2(e) were delivered as the PARTIAL for the 07:41 pack; §2(a)–(d) and §3–§7 complete it.**

---

## §0 — HEADLINE

§5 is a **congruence-and-cancellation argument, not an analytic one**, and the corpus is further
into it than the 08/11 gate's un-itemised 3,000–6,000 suggests. Three of its four structural
demands have landed supply: **the ψ apparatus entire** (`Salt/Weil/Sawtooth.lean` — HB's `ψ` is
`sawtooth`, `:87`, on the nose), **Lemma 10's two exit statements** (`Lemma10Chain.lean:723`,
`:1005`), and **the (5.12) modulus with its `q ∣ k` discharge** (`Salt/Weil/RoadModulus.lean:58`,
`:72`). What is genuinely absent is the **two-variable bilinear object `S(δ₁,δ₂;V₁,V₂)` and every
definition around it** — Λ*'s μ-sieve, the hyperbola step, the dyadic decomposition — i.e. §5's
*bookkeeping layer*, which is large, shallow, and has no mathlib analogue because it is HB's own
notation.

⭐ **The single most valuable finding of the partial (§2(e)): the landed Lemma-10 interface is
STRICTLY MORE GENERAL than HB's Lemma 10, and it absorbs the O(1) split HB does by hand.** HB
states two phase shapes, `f(n) = (T − Cn̄)/k` and `f(n) = (T/n − Cn̄)/k`, and splits the `w₂`-range
into O(1) pieces so that each `T_i(w₁,w₂)` is of one shape or the other. The landed
`lem10_dyadic_bound` does not take `T` at all: it takes an arbitrary `g : ℤ → ℝ` with a
total-variation budget `V`, and **both of HB's shapes are already landed as variation instances**
— `var_const` (`:274`, variation exactly `0`) and `var_inv` (`:293`, variation `≤ |T|/(kE)`).
⇒ **The O(1) split is not a Wave B step; it is an instantiation.** [SCOUT]

⛔ **And one stale row retired:** the prep dossier records `q ∣ k` as "INFERRED — HB does not spell
it out. **N7 owes this discharge.**" It is **LANDED and hypothesis-free** —
`dvd_roadModulus_mul` (`Salt/Weil/RoadModulus.lean:72`), in exactly the shape §5 fires it
(`k = D·δ₁·w₁`). [KERNEL]

---

## §1 — THE EQUATION LEDGER (5.1)–(5.19)

Notes cited as `hb1983-notes.md:<line>`. "Consumes" names a **[KERNEL]** pin (read at the object
this sitting) or records ABSENT with its sibling control. `ln` is a [DESIGN] estimate.

| eq | notes | what it says (one clause) | [KERNEL] pins consumed, or ABSENT | class | ln |
|---|---|---|---|---|---|
| — | `:526-527` | **the object**: `S(δ₁,δ₂;V₁,V₂)`, a bilinear sum over `x<n≤2x` with `δ_i ∣ l_i` and inner `Σ_{w v = l_i/δ_i, v>V_i} χ(w)` | **ABSENT** — no two-variable bilinear carrier in `Salt/`. Sibling control FOUND: the one-variable `Salt/SW/Hyperbola.lean` `sum_divisors_eq_hyperbola_symm` (`:55`) is the same convention at one variable ⇒ ABSENT, not merely unfound | C | 150–300 |
| — | `:531-537` | **Λ\* as the μ-sieve of `Λ′`**, truncated at `m < q`, error `≪ x^{1+ε}q^{−1}` | Lemma 1 **supplied**: `LamStar_nonneg` (`Salt/HB/TwistChain.lean:359`), `vonMangoldt_le_LamTilde` (`:368`) — both in the roll-call (`Salt/HB/All.lean:98-99`). ⚠ the dossier pins the second at `:367`; it is at `:368` at `4deb0c32` | B | 120–250 |
| — | `:539-546` | **LEMMA 9** (p.211): the hyperbola manipulation, giving `S(d)` as a `μ`-weighted double integral of `S(m₁²d₁j₁, m₂²d₂j₂; V₁,V₂)` + `O(x^{1+ε}q^{−1})` | consumes the carrier above; hyperbola sibling as noted | C | 250–450 |
| **(5.1)** | `:548-549` | support: `S` vanishes unless `(δ_i,q) = (δ_i,α) = (δ₁,δ₂) = 1` | a definitional side condition on the carrier | A | 20–40 |
| **(5.2)** | `:551-553` | **dyadic decomposition** `R_i<v_i≤2R_i`, `S_i<w_i≤2S_i`, powers of 2, `R_i ≥ V_i`, `x ≪ δ_iR_iS_i ≪ x` | dyadic idiom is landed in the same file family (`lem10_dyadic_bound` sums over `Finset.Ioc M (2*M)`, `:1005`) | B | 100–200 |
| **(5.3)** | `:555-560` | residue-class split mod `q`: `S = Σ_{R,S} Σ_{a_i,b_i} χ(b₁b₂)·S`, `S` a lattice count | — | B | 80–160 |
| **(5.4)** | `:563` | `δ_i a_i b_i ≡ β_i (mod Δ)` | — | A | 20–40 |
| **(5.5)** | `:564-567` | `α₁(δ₂a₂b₂−β₂) ≡ α₂(δ₁a₁b₁−β₁) (mod qα)`; **⟦q CUBE-FREE consumed here⟧** giving `(α₁,q)=(α₂,q)=Δ` | `Δ` is `Nat.gcd`; `roadModulus`'s `Δ` convention matches (`RoadModulus.lean:58`). **The `v₂(q)=3` hole is §5 of this scout — PENDING** | B | 60–140 |
| **(5.6)** | `:569` | case `S₁ ≤ R₁` needs `(w₁,α) = (w₁,δ₂) = (w₁,q) = 1` | — | A | 20–40 |
| **(5.7)** | `:572` | `δ₂v₂w₂ ≡ β₂ (mod α₂)` | — | A | 15–30 |
| **(5.8)** | `:573` | `α₁δ₂v₂w₂ + α₂β₁ − α₁β₂ ≡ 0 (mod α₂δ₁w₁)` | — | A | 15–30 |
| **(5.9)** | `:574` | same `≡ α₂δ₁a₁b₁ (mod α₂q)` | — | A | 15–30 |
| **(5.10)** | `:575` | `v₂w₂ ≡ a₂b₂ (mod q)` | — | A | 15–30 |
| **(5.11)+(5.12)** | `:579` | the four collapse to **one** congruence `v₂w₂ ≡ C (mod Dδ₁w₁)`, `D = α₂qΔ^{−1}`, `C` independent of `v₂,w₂`, `(C,Dδ₁w₁)=1` | **`roadModulus` IS `D`** (`RoadModulus.lean:58`) and **`roadModulus_eq_lcm` collapses it to `Nat.lcm`** (`:62`) — the row's own header says so. `q ∣ D`: `dvd_roadModulus` (`:65`); `q ∣ Dδ₁w₁`: `dvd_roadModulus_mul` (`:72`); `α₂ ∣ D`: `dvd_roadModulus_left` (`:76`) | **C** | 400–700 |
| **(5.13)** | `:581-584` | the CRT consistency check `(m_j,m_k) ∣ (X_j−X_k)` over the **four** moduli `α₁α₂ ; α₂δ₁w₁ ; α₂q ; α₁δ₂q`, then the explicit lcm `m₀ = α₁δ₂·δ₁w₁·α₂q/(α,q)` | mathlib CRT present and **already used in this corpus in the pairwise form**: `Nat.chineseRemainder` at `Salt/Goldbach/Residue.lean:60`, with a `Finset.induction` combiner (`:41`) — the four-modulus + compatibility form is **not found** there. §3 of this scout owns the fit (PENDING) | **C** | 300–600 |
| **(5.14)** | `:588` | `S = Σ_{S_i<w_i≤2S_i, w_i≡b_i(q)} #{v₂ : v₂w₂ ≡ C (mod Dδ₁w₁), T₁<v₂≤T₂}` — a **double** sum over `w₁` and `w₂` | ⛔ the transcription's earlier single-sum form is **CLOSED at the source** (`:592-599`); the dropped index was exactly Lemma 10's summation variable | B | 80–160 |
| **(5.15)** | `:589` | `T₁ = Max{ R₂, (α₂x+β₂)/(δ₂w₂), (α₂δ₁w₁R₁+α₁β₂−α₂β₁)/(α₁δ₂w₂) }` | a three-term `Max` | A | 30–60 |
| **(5.16)** | `:590` | `T₂ = Min{ 2R₂, … , … }` | a three-term `Min` | A | 30–60 |
| **(5.17)** | `:601-603` | **the ψ-reduction**: `#{v₂ : …} = (T₂−T₁)(Dδ₁w₁)^{−1} + ψ((T₁−Cw̄₂)/(Dδ₁w₁)) − ψ((T₂−Cw̄₂)/(Dδ₁w₁))`, `ψ(θ)=θ−[θ]−½`, `w̄₂` the inverse mod `Dδ₁w₁` | ⭐ **`ψ` IS LANDED**: `sawtooth θ = Int.fract θ − 1/2` (`Salt/Weil/Sawtooth.lean:87`) — HB's definition on the nose, with its Fourier expansion (`:105`), truncation remainder (`:240`, `:345`, `:440`), majorant (`:521`, `:574`, `:648`) and coefficient bounds (`:666`, `:970`). The inverse `w̄₂` is `invMod` as `Lemma10Chain` uses it (`:1005`ff) | B | 150–300 |
| **LEMMA 10** | `:605-612` | `Σ′_{n∈I} ψ(f(n)) ≪ (1+|T|E^{−1}k^{−1})(E+k)q^{3/2}k^{ε−1/4}` for `f(n)=(T−Cn̄)/k` **or** `(T/n−Cn̄)/k`, `Σ′` imposing `(n,k)=1`, `n≡b (mod q)` | ⛔ **`hb_lemma10` NOT LANDED** — the file's own header says so (`Lemma10Chain.lean:27-31`). Its two exit statements ARE landed: `klPhaseSum_bound` (`:723`), `lem10_dyadic_bound` (`:1005`). **§2(e) below states what `hb_lemma10` must say for (5.17) to consume it** | — | — |
| **applying** | `:614-623` | `k=Dδ₁w₁`, `E=S₂`, the O(1) `w₂`-split so each `T_i` is `T` or `T/w₂`, `T ≪ x/δ₂`; total ψ-contribution `≪ δ₁q^{5/2}x^{15/16+ε}` | **§2(e)** — and the O(1) split is absorbed by the landed interface (`var_const` `:274`, `var_inv` `:293`) | **C** | 350–650 |
| **(5.18)** | `:668-671` | `S(δ₁,δ₂;V₁,V₂) = Σ_{R_i,S_i} Σ_{a_i,b_i} χ(b₁b₂)·S`, subject to (5.2)–(5.5) | re-assembly of (5.3) | B | 60–120 |
| **(5.19)** | `:672-675` | **LEMMA 11**: if `S_i ≤ R_i` then `S = Σ*_{S_i<w_i≤2S_i, w_i≡b_i(q)} (T₂−T₁)(Dδ₁w₁)^{−1} + O(δ₁q^{5/2}x^{15/16+ε})`, `Σ*` imposing `T₂>T₁`, (5.6), `(w₂,Dδ₁w₁)=1` | the wave's exit; **its seam with (6.2) is §4 of this scout — PENDING** | **C** | 250–450 |

⛔ **THE CORRECTED EXPONENTS ARE THE PAPER'S ERRATUM, NOT THE NOTES'** (`:625-666`): HB prints
`S₁ ≪ x^{1/4}` and `S₂ ≪ x^{1/4}`; **both are typos and the right value is `x^{1/2}`**, established
three independent ways from HB's own next display, and the `S₂` proviso **is not needed at all**.
The regime Wave B must carry is `S₁, S₂ ≪ x^{1/2}` with `S₁S₂ ≫ x^{15/16}` — non-empty; as printed
it is empty. **Any Lean statement of (5.19) must carry the corrected exponents.** [HB-NOTES]

**Ledger totals (partial, [DESIGN]):** 21 rows, **≈ 2,500–4,600 ln** — inside the 08/11 gate's
inherited 3,000–6,000 and, at the low end, below it. **Regime call:** the four congruence rows and
the (5.11)+(5.13) collapse are **FRESH**; (5.17), (5.14), the dyadic and residue splits are
**ASSEMBLY of landed inputs** (the pair's §3 prices assemblies by piece count). The (5.19) exit is
FRESH. A full per-row regime call is §6's, PENDING.

---

## §2(e) — THE (5.17) APPLICATION OF LEMMA 10, CONFIRMED SLOT BY SLOT

The prep dossier's substitution table (`n7-prep-dossier-0806.md:90-98`) against the **landed
signatures**, read at `4deb0c32`.

**`lem10_dyadic_bound`** (`Salt/HB/Lemma10Chain.lean:1005`) [KERNEL]:

```
theorem lem10_dyadic_bound [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q)) (M : ℕ) :
    ∑ m ∈ Finset.Ioc M (2 * M), ‖lem10ExpSum k q b (Finset.Ioc A B) m
        (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖ ≤ …
```

| Lemma 10 slot | §5 value (dossier) | landed slot | verdict |
|---|---|---|---|
| summation variable `n` | `w₂` | the `n` of `Finset.Ioc A B` inside `lem10ExpSum` | ✅ **fits** |
| `k` | `Dδ₁w₁ = α₂qΔ^{−1}δ₁w₁` | `k : ℕ`, `[NeZero k]`, `hk : 2 ≤ k` | ✅ fits; the consumer owes `2 ≤ Dδ₁w₁`, immediate from `q ≥ 3` |
| `E` | `S₂`, `I ⊆ (S₂, 2S₂]` | `{E : ℝ}`, `hE : 1 ≤ E`, **plus** `hlen : ((B−A).toNat : ℝ) ≤ 2*E` | ⚠️ **shape delta**: the landed form takes integer endpoints `A B` and a **length** bound, not a set inclusion `I ⊆ (E,2E]`. The consumer must produce `A B` and discharge `hlen`. The dossier's own UNVERIFIED note (`:283-285`) is exactly this row — **and §7.1 now CLOSES it: `A = ⌊S₂⌋`, `B = ⌊2S₂⌋` gives HB's `I` exactly, and `hlen` is free. No off-by-one** |
| `T` | `T₁`/`T₂` after an O(1) split into `T`- and `T/w₂`-shaped pieces | **no `T` slot at all** — `g : ℤ → ℝ` with `hvar : ∑\|g(n+1)−g(n)\| ≤ V` | ⭐ **STRICTLY MORE GENERAL, AND THE SPLIT IS ABSORBED.** `f(n)=(T−Cn̄)/k` ⟹ `g n = T/k`, variation `0` — **`var_const` (`:274`)**. `f(n)=(T/n−Cn̄)/k` ⟹ `g n = T/(kn)`, variation `≤ \|T\|/(kE)` — **`var_inv` (`:293`)**. Both landed. The O(1) `w₂`-range split HB performs by hand is an **instantiation**, not a step |
| `C` | the (5.11) constant, `(C, Dδ₁w₁) = 1` | `c : ℤ`, `hc : Nat.Coprime c.natAbs (k / q)` | ✅ fits, and the landed hypothesis is **weaker** — coprimality against `k/q`, not `k`. (5.11)'s `(C,Dδ₁w₁)=1` implies it since `k/q ∣ k` |
| `b` | `b₂` | `b : ℤ` | ✅ fits |
| `q ∣ k` | "INFERRED — N7 owes this discharge" | `hqk : q ∣ k` | ⛔ **THE DOSSIER ROW IS STALE. LANDED, hypothesis-free: `dvd_roadModulus_mul (α₂ q δ₁ w₁) : q ∣ roadModulus α₂ q * δ₁ * w₁`** (`Salt/Weil/RoadModulus.lean:72`), written in exactly the `k = Dδ₁w₁` shape, with `dvd_roadModulus` (`:65`) beneath it |

**`klPhaseSum_bound`** (`:723`) carries the same `(hk, hq, hqk, b, E, hlen)` prefix plus `A B c : ℤ`
and exits at the numeral `8`; `lem10_dyadic_bound` exits at `16`. Both are consumable as they stand.

### What `hb_lemma10` must SAY, from the consumer's side [SCOUT]

(5.17) hands (5.14) two ψ-terms per `(w₁,w₂)`; summing over the double range, the consumer needs a
bound on `Σ′_{n∈I} ψ(f(n))` with `Σ′` imposing `(n,k)=1` **and** `n ≡ b (mod q)`. So `hb_lemma10`
must conclude, in the corpus's own conventions:

> for `k` with `2 ≤ k`, `q ∣ k`, `(c, k/q)` coprime, `b : ℤ`, `E ≥ 1`, integer endpoints
> `A ≤ B` with `(B−A).toNat ≤ 2E`, and `g : ℤ → ℝ` of total variation `≤ V` on `Ioc A (B−1)`:
> `|Σ_{n ∈ Ioc A B, (n,k)=1, n ≡ b (q)} sawtooth (g n + c·invMod n k / k)|`
> `≤ <explicit> · (1 + V·k^{1/4}) · (E + k) · q^{3/2} · d(k)³ · (log 2k)³ / k^{1/4}`

three points about that shape, each a [SCOUT] claim:

1. **`K = 2 + k^{1/4}` is the truncation and it is why `k^{1/4}` appears twice** — once as the
   `k^{ε−1/4}` saving and once inside `(1 + |T|E^{−1}k^{−1})`, which the `g`/`V` interface renders
   as `(1 + V·K)`-shaped. The landed dyadic bound already carries `(1 + 4πMV)` per block
   (`:1005`); the assembly sums that over the dyadic cover of `0 < |m| ≤ K`.
2. **`d(k)³(log 2k)³` is LITERAL, not `k^ε`** — the freeze rule
   (`weil-trio-design-0806.md:90-93`), and `lem10_dyadic_bound` already exits at
   `(k.divisors.card)^3 * Real.log (2*k)` (one `log`, the sharp intermediate). The **cube** of the
   log is the assembly's, not the dyadic step's.
3. ⛔ **The `(log Kk)³ → (log 2k)³` conversion is still OPEN and it is one explicit line.** The
   dossier's defect 3 (`:120-123`): `sup_{k≥2} log(Kk)/log(2k) = 1.3366` at `k = 2` (limit `5/4`),
   so `(log Kk)³ ≤ 2.39·(log 2k)³`. Defects 1 and 2 of that list are CLOSED; **this one is not**,
   and it belongs to the Wave A seal, not to Wave B.

⇒ **The Wave A seal's statement is pinned from below by this row**: whatever `hb_lemma10` says, it
must take the `g`/`V` interface (not `T`), integer endpoints with a length bound (not a set
inclusion), and coprimality against `k/q` (not `k`) — because that is what its own landed
ingredients provide and what (5.17) can supply.

---

## §2(a)–(d) — THE REST OF THE STRUCTURE

**(a) The μ-sieve of `Λ*` (p.210) and the hyperbola step (p.211).** `Λ*(n) = Σ*_{u∣n} χ(u) log(n/u)`
is re-expressed by Möbius over `m ∣ Q` and truncated at `m < q`, error `≪ x^{1+ε}q^{−1}`
(`hb1983-notes.md:531-537`). **Lemma 1 is supplied** — `LamStar_nonneg`
(`Salt/HB/TwistChain.lean:359`) and `vonMangoldt_le_LamTilde` (`:368`), both in the roll-call
(`Salt/HB/All.lean:98-99`) [KERNEL]. The hyperbola manipulation into the `Σ_{v>V} χ(w)` shape has a
**one-variable sibling** landed — `sum_divisors_eq_hyperbola_symm` (`Salt/SW/Hyperbola.lean:55`,
generic over a `CommRing`) and `dhA_hyperbola_symm` (`:184`) [KERNEL] — so the two-variable version
is a port of a landed idiom, not a fresh construction. **The carrier `S(δ₁,δ₂;V₁,V₂)` itself is
ABSENT** (sibling control found ⇒ ABSENT, not merely unfound). Class C for the carrier + Lemma 9;
class B for the sieve. [SCOUT]

**(b) The dyadic decomposition (5.2)–(5.3) and the support conditions (5.1).** `R_i/V_i` and `S_i`
powers of 2 with `x ≪ δ_iR_iS_i ≪ x`; the residue split mod `q` carries `χ(b₁b₂)`. The **dyadic
idiom is landed in the file Wave B consumes** — `lem10_dyadic_bound` sums over
`Finset.Ioc M (2*M)` (`Lemma10Chain.lean:1005`) [KERNEL] — so the convention is fixed and an
executor should follow it rather than invent a `Set.Ioc` form. (5.1) is three coprimality side
conditions on the carrier's definition. Class B. [SCOUT]

**(c) The four congruences (5.7)–(5.10) and their collapse to (5.11)–(5.13).** See §3 stone 1 —
this is the wave's hardest row and mathlib's fit is exact in the primitive and wrong in the wrapper.

**(d) The ψ-reduction (5.14)–(5.17) and the `Max`/`Min` triples.** (5.15)/(5.16) are a three-term
`Max` and a three-term `Min`; in Lean these are `max a (max b c)` / `min a (min b c)` over `ℝ`,
with the ordering facts an executor needs being `le_max_left/right` and `min_le_left/right` — no
design content, but **the three entries must be transcribed in HB's exact order** because
(5.15)'s third entry and (5.16)'s third entry differ only in a leading `2` and share the
`α₁β₂ − α₂β₁` numerator (`:589-590`), which is the transcription hazard in this row. The `ψ` and
the inverse `w̄₂` are landed (§1's (5.17) row). Class A for the triples, B for the reduction. [SCOUT]

---

## §3 — THE STONES (what an executor fails on if not pointed at first)

**STONE 1 — the four-modulus CRT with compatibility (5.13). Class C, ≈ 300–600 ln.**
HB collapses four congruences to one by a consistency check `(m_j,m_k) ∣ (X_j − X_k)` over
`α₁α₂ ; α₂δ₁w₁ ; α₂q ; α₁δ₂q`, then an explicit lcm `m₀ = α₁δ₂·δ₁w₁·α₂q/(α,q)` (`:581-584`).

⭐ **mathlib has EXACTLY the right primitive and EXACTLY the wrong wrapper, and an executor will
reach for the wrong one.**

- **RIGHT:** `Nat.chineseRemainder'` (`.lake/packages/mathlib/Mathlib/Data/Nat/ModEq.lean:422`) —
  `(h : a ≡ b [MOD gcd n m]) : { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] }`. Its hypothesis **is** HB's
  (5.13) compatibility condition, stated as a `gcd` congruence rather than a divisibility; and
  `chineseRemainder'_lt_lcm` (`.lake/packages/mathlib/Mathlib/Data/Nat/ModEq.lean:467`) bounds the witness by `lcm n m`, which is HB's `m₀`. [KERNEL]
- **WRONG:** every n-ary form — `chineseRemainderOfList` (`.lake/packages/mathlib/Mathlib/Data/Nat/ChineseRemainder.lean:65`),
  `chineseRemainderOfMultiset` (`:132`), `chineseRemainderOfFinset` (`:165`) — demands
  `Pairwise (Coprime on s)`. **HB's four moduli are not pairwise coprime** (they share `α₂` and `q`
  by construction), so the ergonomic n-ary route is unavailable. [KERNEL]

⇒ **The collapse is a THREE-FOLD ITERATION of `chineseRemainder'`**, carrying the modulus as an
iterated `lcm` and discharging each compatibility hypothesis from (5.4)/(5.5)/(1.7). **House idiom
already fixed:** `roadModulus_eq_lcm` (`Salt/Weil/RoadModulus.lean:62`) says `D` *is* `Nat.lcm`
by `rfl` — the corpus already chose `lcm` over the `αq/gcd` spelling, and this row should follow it.
The corpus's only prior CRT use is the **pairwise coprime** `Nat.chineseRemainder` under a
`Finset.induction` (`Salt/Goldbach/Residue.lean:41`, `:60`) [KERNEL] — a control that does **not**
transfer, and an executor copying it will hit the coprimality wall on the first fold.

**STONE 2 — the p.214 error budget at the CORRECTED exponents. Class B–C, ≈ 250–450 ln.**
The ψ-total `≪ δ₁q^{5/2}(S₁S₂ + S₁² + x + xS₁/S₂)S₁^{ε−1/4} ≪ δ₁q^{5/2}x^{15/16+ε}` must be closed
term by term at `S₁, S₂ ≪ x^{1/2}` and `S₁S₂ ≫ x^{15/16}` — **not** at HB's printed `x^{1/4}`,
which empties the regime. The notes already carry the term-by-term closure in exact rationals
(`:653-661`): term 1 binds, terms 2–4 are free, and `S₂ ≪ x^{1/4}` is **not needed at all**. So
this stone is *transcription of a completed argument*, not new mathematics — **provided the
executor is handed the corrected exponents**, because the paper says otherwise and a careful
executor reading HB will reproduce the empty regime. [HB-NOTES]

**NOT A STONE, and this is the finding: the O(1) `T` / `T/w₂` split.** §2(e) shows the landed
interface takes `g` + a variation budget, and both of HB's phase shapes are landed as `var_const`
(`:274`) and `var_inv` (`:293`). The 08/11 gate would have priced this; it is an instantiation.

---

## §4 — THE (5.19)↔(6.2) SEAM: **IT CLOSES**, AND THE IDENTITY IS ONE AFFINE SUBSTITUTION

This was **UNVERIFIED** at the Wave C scout (its `§7.7`) and is the one place the two waves can
fail to meet. Verified here [SCOUT], from the two displays as each scout states them:

- **(5.19)** summand (`:672`): `(T₂ − T₁)·(Dδ₁w₁)^{−1}`, with `D = α₂qΔ^{−1}` (5.12).
- **(6.2)** summand (`:693-696`, and the Wave C scout's §1 row for it): `K^{−1}(w₁w₂)^{−1}A`, with
  `K = δ₁δ₂qΔ^{−1}` and `A(w₁,w₂) = mes{ t : x ≤ t ≤ 2x, R_i ≤ l_i(t)/(δ_iw_i) ≤ 2R_i }`.

Equating and cancelling the common `qΔ^{−1}δ₁w₁`:

> `(T₂ − T₁)/α₂ = A/(δ₂w₂)`, i.e. **`A = (δ₂w₂/α₂)·(T₂ − T₁)`.**

**That is exactly the Jacobian of the substitution (5.14) already performs.** Put
`v₂ = l₂(t)/(δ₂w₂) = (α₂t + β₂)/(δ₂w₂)`, so `t = (δ₂w₂v₂ − β₂)/α₂` and `dt = (δ₂w₂/α₂)dv₂`. The
three constraints defining `A` map to the three entries of (5.15)/(5.16) **one for one**:

| constraint on `t` | image under `t ↦ v₂` | (5.15)/(5.16) entry |
|---|---|---|
| `R₂ ≤ l₂(t)/(δ₂w₂) ≤ 2R₂` | `R₂ ≤ v₂ ≤ 2R₂` | first entries ✅ |
| `x ≤ t ≤ 2x` | `(α₂x+β₂)/(δ₂w₂) ≤ v₂ ≤ (2α₂x+β₂)/(δ₂w₂)` | second entries ✅ |
| `R₁ ≤ l₁(t)/(δ₁w₁) ≤ 2R₁` | `v₂ ≥ (α₂δ₁w₁R₁ + α₁β₂ − α₂β₁)/(α₁δ₂w₂)`, and `≤` the same with `2R₁` | third entries ✅, sign and all |

⇒ **SAME SHAPE. No delta.** (6.2)'s summand is (5.19)'s summand pushed through one affine change
of variable, and the `A`-vs-`(T₂−T₁)` mismatch that made the row look risky is precisely the
Jacobian `δ₂w₂/α₂`. **The two waves meet.**

✅ **AND THE ALGEBRA IS INSTRUMENT-VERIFIED, NOT HAND-CHECKED.** The identity and all four
constraint images were driven over **4,000 random parameter tuples in exact rationals**
(`α₁ α₂ β₁ β₂ δ₁ δ₂ q Δ w₁ w₂ R₁ x`, `Fraction` arithmetic, no floating point): the Jacobian, both
`x`-endpoint images, and both `R₁`-endpoint images matched their (5.15)/(5.16) entries **0 failures
in 4,000**, and the seam factor `K w₁w₂/(Dδ₁w₁)` equalled `δ₂w₂/α₂` identically. **A negative
control was driven and the instrument refuses it**: the sign-flipped third entry
(`α₂δ₁w₁R₁ − α₁β₂ + α₂β₁`, the transcription error this row exists to catch) was accepted **0 times
in 500** — so the check can say NO. [SCOUT]

⚠️ **Two honest riders.** (i) This is an identity between the **main terms**; (5.19)'s `Σ*`
side conditions (`T₂ > T₁`, (5.6), `(w₂,Dδ₁w₁)=1`) must be carried into §6 unchanged — they are
not part of the seam but they travel with it. (ii) I verified the algebra, not a Lean proof; the
Lean cost is a `MeasureTheory.volume` image-under-affine-map argument, **class B, ≈ 80–150 ln**,
and it belongs to Wave C-1 (which owns `A`), not to Wave B.

---

## §5 — THE (5.5) HOLE AT `v₂(q) = 3`: **MOOT AT THE TWIN INSTANCE**

`weil-trio-design-0806.md:165-172` records a genuine hole in HB (5.5): (1.8)+(1.9) do **not** give
`(α₁,q) = (α₂,q)` when `v₂(α₁) ≠ v₂(α₂)`, with the admissible counterexample `4n+1, 8n+3`.

**At the twin instance it does not arise.** The crown's wire fixes the forms: `hbDataN8`
(`Salt/HB/CrownAssembly.lean:114-123`) takes `val n = n * (n + 2)` [KERNEL], i.e. `l₁(n) = n` and
`l₂(n) = n + 2` — so `α₁ = α₂` (and `v₂(α₁) = v₂(α₂)` trivially), and `(α₁,q) = (α₂,q)` holds for
every `q` with no cube-free appeal needed for *this* step. The design's own note says the same
("MOOT FOR TWIN PRIMES … the road carries `α₁ = α₂` as a named hypothesis").

⇒ **LIVE for general form pairs, MOOT here. One row, no price.** It stays worth a remark in any
writeup as an erratum-grade finding about HB, and Wave B's Lean statements should carry `α₁ = α₂`
as a named hypothesis rather than silently relying on the instance.

---

## §6 — THE WAVE TABLE

Split as the object dictates: the congruence half and the ψ half meet cleanly at (5.13).

| # | node | statement shape | consumes | regime | class | ln |
|---|---|---|---|---|---|---|
| **B-1** | the carrier | `S(δ₁,δ₂;V₁,V₂)` as a definition + (5.1) support | — (ABSENT; hyperbola sibling as idiom) | FRESH | C | 170–340 |
| **B-2** | Λ*'s μ-sieve + Lemma 9 | `S(d) = Σ μμ ∫∫ S(…) + O(x^{1+ε}q^{−1})` | `LamStar_nonneg`, `vonMangoldt_le_LamTilde`, `sum_divisors_eq_hyperbola_symm` | ASSEMBLY (3 landed) | C | 370–700 |
| **B-3** | dyadic + residue split (5.2)–(5.4) | `S = Σ_{R,S}Σ_{a,b} χ(b₁b₂)S` | the `Finset.Ioc M (2M)` idiom | ASSEMBLY | B | 230–460 |
| **B-4** | **the CRT collapse (5.5)–(5.13)** | four congruences ⟹ `v₂w₂ ≡ C (mod Dδ₁w₁)` | `roadModulus`, `roadModulus_eq_lcm`, `dvd_roadModulus{,_mul,_left}`, `Nat.chineseRemainder'`, `chineseRemainder'_lt_lcm` | **FRESH** (stone 1) | **C** | 400–800 |
| **B-5** | the ψ-reduction (5.14)–(5.17) | `#{v₂} = (T₂−T₁)/(Dδ₁w₁) + ψ(·) − ψ(·)` | `sawtooth` + its whole kit, `invMod` | ASSEMBLY (6 landed) | B | 210–420 |
| **B-6** | **applying Lemma 10** | the ψ-total `≪ δ₁q^{5/2}x^{15/16+ε}` | `lem10_dyadic_bound`, `klPhaseSum_bound`, `var_const`, `var_inv`, `dvd_roadModulus_mul`; **gated on `hb_lemma10` (Wave A seal)** | ASSEMBLY (5 landed + 1 unlanded) | **C** | 350–650 |
| **B-7** | Lemma 11 / (5.19) | the wave's exit, at the **corrected** exponents | B-3…B-6 | FRESH | C | 250–450 |
| | | | | | **Σ** | **1,980–3,820** |

**Against the 08/11 gate's inherited 3,000–6,000: the bar narrows to ≈ 2,000–3,800, and its low end
falls below the inherited floor.** [DESIGN]

**Regime call** (the pair's §3 prices assemblies by piece count): **four of seven nodes are
ASSEMBLIES of already-landed inputs** — the regime the estimator ran 3.3× low on for the ratio and
1.0× for the strip. B-3 and B-5 in particular consume landed idioms almost entirely and should be
priced by piece count, not by class mean. The genuinely FRESH mass is B-1, B-4 and B-7.

⛔ **B-6 is gated on the Wave A seal** (`hb_lemma10`), so Wave B cannot close before it. §2(e)
pins that seal's statement from the consumer side, which is the cheapest thing this scout produces.

---

## §7 — WHAT I COULD NOT DETERMINE (two of the five closed after first writing it)

1. ✅ ~~Whether `I ⊆ (E,2E]` maps onto a `Finset.Ioc A B` without an off-by-one.~~ **SETTLED — NO
   OFF-BY-ONE, AND IT NEEDED NO BUILD.** The dossier had this UNVERIFIED since 08/06 and I first
   filed it here as needing a scratch build; that was wrong about the *kind* of question it is. It
   is floor arithmetic about how the CONSUMER instantiates, not a Lean elaboration question.
   **The witness:** take `A = ⌊S₂⌋`, `B = ⌊2S₂⌋`. Then `Finset.Ioc A B` is
   `{n : A < n ≤ B}` (`.lake/packages/mathlib/Mathlib/Order/Interval/Finset/Defs.lean:309`,
   `mem_Ioc : x ∈ Ioc a b ↔ a < x ∧ x ≤ b`) [KERNEL], which for integers is exactly
   `{n : S₂ < n ≤ 2S₂}` — HB's `I` — because `n > ⌊S₂⌋ ⟺ n > S₂` and `n ≤ ⌊2S₂⌋ ⟺ n ≤ 2S₂` on `ℤ`.
   And `hlen` discharges for free: `(B − A).toNat = ⌊2S₂⌋ − ⌊S₂⌋ ≤ 2S₂ = 2E`, since `⌊2S₂⌋ ≤ 2S₂`
   and `⌊S₂⌋ ≥ 0`. **Driven, not asserted:** both claims over **20,000 random `S₂ ≥ 1` in exact
   rationals — 0 failures**, worst observed `(B−A)/E = 1.333` against the bound `2`; and a
   **negative control** (`A` shifted down by one, the precise slip feared) accepted **0/2000**.
   ⚠️ What this does NOT settle: that an executor writes it correctly, and that no *other*
   instantiation of `E` is intended. The interval question itself is closed.
2. **The exact constant in `hb_lemma10`'s conclusion.** §2(e) gives its shape; the numeral depends
   on the dyadic cover's block count and the `(log Kk)³ → (log 2k)³` conversion (`2.39`), and both
   are the Wave A seal's to fix. **What settles it:** the seal's freeze.
3. **Whether B-2's double integral needs a Fubini/measurability side condition** that mathlib does
   not hand over cheaply. I read the display, not a proof. **What settles it:** the B-2 freeze.
4. **The `a_i`/`b_i` count over (5.3)–(5.5).** §6 of the paper needs `∏_{p∣q/Δ}(p−2) = qΔ^{−1}M`;
   the Wave C scout already books that as its own C1-07 row, so I have **not** priced it here — it
   is Wave C's, and I say so rather than double-count it.
5. ✅ ~~`hb_lemma10'` (the primed variant) — what distinguishes it, and does (5.17) need both?~~
   **SETTLED, AND THE ANSWER IS THAT IT SHOULD NOT BE BUILT.** Three shapes run over the whole
   repository (`.lean` and `.md`): the exact name · any `lemma10'`/`lemma10_prime`/`hbLemma10`
   spelling · `find -iname '*lemma10*'`. **The primed name occurs EXACTLY ONCE in the corpus** —
   `Lemma10Chain.lean:27`, the sentence that declares it unlanded. It has **no statement, no
   docstring specification, and no design row anywhere.** [KERNEL]
   **The evident intent** is HB's two phase shapes: Lemma 10 is stated for `f(n) = (T − Cn̄)/k`
   **or** `f(n) = (T/n − Cn̄)/k` (`:611`), so a primed twin would be the second.
   ⇒ **§2(e) dissolves the need for it.** The landed `lem10_dyadic_bound` is generic over
   `g : ℤ → ℝ` with a variation budget, and **both** shapes are already landed as instances —
   `var_const` (`:274`) and `var_inv` (`:293`). A single `hb_lemma10` stated over the `g`/`V`
   interface subsumes both; a primed twin would restate the same theorem at a second instantiation.
   ⇒ **RECOMMENDATION for the Wave A seal's freeze: state ONE theorem over `g`/`V` and RETIRE the
   primed name**, unless the seal's author means something by it that the corpus does not record.
   That saves a statement and removes a second surface from the seal.

**Nothing in this scout bears on twin primes**: it prices a wave of N7, which is a binder on the
crown either way, and it lands nothing.
