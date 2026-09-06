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

**Status: §1 and §2(e) are delivered (the pack's two rows). §2(a)–(d), §3–§7 are PENDING.**

---

## §0 — HEADLINE (partial)

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
| `E` | `S₂`, `I ⊆ (S₂, 2S₂]` | `{E : ℝ}`, `hE : 1 ≤ E`, **plus** `hlen : ((B−A).toNat : ℝ) ≤ 2*E` | ⚠️ **shape delta**: the landed form takes integer endpoints `A B` and a **length** bound, not a set inclusion `I ⊆ (E,2E]`. The consumer must produce `A B` and discharge `hlen`. The dossier's own UNVERIFIED note (`:283-285`, "nobody has checked that `I₀ ⊆ (E,2E]` maps onto a `Finset.Ioc M₁ M₂` without an off-by-one") **is exactly this row and is still open** |
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

## §2(a)–(d), §3, §4, §5, §6, §7 — PENDING (WHOLE due 09:30)

Named here so the partial's silence is not read as a hole: (a) the μ-sieve and hyperbola step;
(b) the dyadic decomposition and support conditions; (c) the four-congruence CRT collapse against
mathlib's forms; (d) the ψ-reduction's `Max`/`Min` triples; §3 the stones; §4 the (5.19)↔(6.2)
seam (UNVERIFIED at the Wave C scout §7.7); §5 the (5.5) hole at `v₂(q)=3`; §6 the wave table;
§7 what I could not determine.

**Nothing in this scout bears on twin primes**: it prices a wave of N7, which is a binder on the
crown either way, and it lands nothing.
