/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cMasterUncond
import Salt.HB.SieveWire
import Salt.HB.CharTrio
import Salt.HB.Lemma3Uncond
import Salt.HB.Lemma3Floor
import Salt.Maynard.Mertens

/-!
# N8 — THE §2 ASSEMBLY OF HEATH-BROWN 1983 (the crown campaign's first design block)

**STATUS: A DESIGN FREEZE.  Every theorem below is `sorry`-bodied by design.**  This file is
the wave table for node N8 of the Heath-Brown engine (`docs/sources/hb1983-notes.md` §1–§2,
pp.197–200): the reduction chain `S⁽⁰⁾ → S⁽³⁾` stated on ONE window, and the p.200 assembly
`S⁽³⁾ ≤ κS₁{(L′/L)² + O(BL) + O(B²e^{−z₀/4})} + O(xL⁸/z)` (both signs) from the landed
dimension-4 sieve, HB's Lemma 5 as an INTERFACE (N7's exit, Wave C-2 row C2-10), and HB's
Lemma 6 proved here.  Each docstring carries the row's **class**, its **line cap**, the
**red-first idea** (what the executor does first), and the **consumer** of the statement by
Lean name.  Nothing here bears on twin primes: N8 assembles nothing on its own — the dichotomy
`fulcrum_dichotomy` stays conditional on `hEngine` until N7 (Waves A/B/C), N8, N9, N10 and the
four joins all land.

## THE THREE DESIGN DECISIONS (seams S1, S2, S6 of the crown census)

**S1 — ONE WINDOW: `l2cWindow χ z x`.**  Four windows exist in the corpus (`l2cWindow`,
`honestWindow`, `HBSieveData.support`, `twinWindow`).  The chain is stated on
`l2cWindow χ z x = {n ∈ (x, 2x] : (n(n+2), q·excPrimorial χ z) = 1}` — HB's `(l, qP) = 1` at
the minimal honest modulus, the window the unconditional master `hb_l2c_master_unconditional`
is already proved on.  The star step reaches it for free (`S2_sub_S3_window` takes any
sub-window with `excPrimorial`-coprimality, which `l2cWindow_excPrimorial_coprime` supplies);
the sieve reaches it through a second wire `hbDataN8` (the `SieveWire` pattern at this window,
where the `(l, P) = 1` filter of `hbData_S3_eq` becomes VACUOUS — `hbDataN8_S3_eq`); the door
(`twinWindow (2x+2) = Ioc x (2x)`, `twinWindow_two_mul_add_two`) is reached by the
`S⁽⁰⁾ → S⁽¹⁾` swap `S1_Ioc_sub_S1_l2cWindow_le`.  `honestWindow` and `hbData` are thereby
SUPERSEDED for the crown path (they stay landed, untouched).

**S2 — ONE `S⁽³⁾`.**  `hbDataN8_S3_eq` identifies the interface's sifted sum with the star
step's `S3 χ z (l2cWindow χ z x)` with NO residual filter, so every sandwich conclusion is
literally about the object the reduction chain ends on.

**S6 — `S⁽⁰⁾ → S⁽¹⁾` NAMED.**  `S1_Ioc_sub_S1_l2cWindow_le`: the terms dropped by the
coprimality cut are prime-power pairs, at most two per prime of `q·excPrimorial`, so the swap
costs `≤ 2(ω(q) + z)·L′²` — sharper than HB's `O(L⁴z)`.

## WHAT N8 KEEPS SYMBOLIC (and why)

* `PretenseSum χ (2x+2)` stays a SYMBOL in the Lemma-4 error `lemma4Err` — N8's reduction is
  zero-free, exactly as HB's §2 is.  The zero enters only through
  `pretenseSum_at_repulsion_floor` (HB Lemma 3 at the pretense-sum level, the join the crown
  chain actually consumes — see the ⛔ below) and through the VALUES `LL = L′(1,χ)/L(1,χ)` and
  `kappa`, both free parameters here, identified by N9 with N4's terminals.
* `Lemma5Eval` is an interface: Wave C-2 (row C2-10) PRODUCES it at `H := hbDataN8 …`; the
  p.200 rows CONSUME it.  Its constants `CA CA' CC Cerr` are literal parameters — Wave C must
  print them; N8 never writes `≪`.
* `z` is free with the landed binders carried (`hz100 hz8 hzx` of the master, `hzt hs` of the
  sieve, and `3·sRatio·log z ≤ L` for HB's `D = q^{1/3}`); N9 discharges them at HB's
  `z = q^{1/z₀}`, `z₀ = A·log log η` (seam S3 is N9's, not N8's).

⛔ **A FINDING ABOUT THE LANDED N3 JOIN.**  `hb_lemma3_at_repulsion_floor`
(`Salt/HB/Lemma3Floor.lean`) joins Lemma 3 to the PARAMETRIC `hb_lemma2` shape: its antecedent
`hres : overshootMajorant χ A ≤ …` is the τ-crude majorant that the L2c campaign declared
"provably `L²`-inflated at the worst pattern and BYPASSED" (`Salt/HB/L2cCore.lean` header).  No
producer of `hres` at HB's grade exists or is planned, so that join has no consumer on the crown
path.  The join the path needs is one level down — the pretense sum itself at the floor —
and it is `pretenseSum_at_repulsion_floor` below (same binders, same route, one stage earlier).
The landed join stays; it is simply not on the road.

## THE ROWS (executor order; class per the salt CLAUDE.md table)

§1 window & wire · §2 the swap · §3 Lemma 4 on the window · §4 Lemma 3 at the pretense sum ·
§5 Lemma 6 (the densities) · §6 Lemma 5 interface + the p.200 assembly · §7 the `κS₁` wire.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius
open Salt.TwinBar
open Salt.BrunLower
open Salt.SW

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 — the window decision (S1) and the sieve wire at that window (S2) -/

/-- **`l2cWindow ⊆ honestWindow`.**  Coprimality to `q·excPrimorial` implies coprimality to
`excPrimorial`.  Class **A**, cap 30.  Red-first: `Finset.filter_subset_filter` +
`Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _)`.  Consumer: `S2_sub_S3_l2cWindow` (via
`l2cWindow_excPrimorial_coprime`, already landed; this row is the set-level form for N9). -/
theorem l2cWindow_subset_honestWindow (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    l2cWindow χ z x ⊆ honestWindow χ z x := by
  sorry

/-- **The `(l, P) = 1` filter is vacuous on the N8 window.**  Every prime of
`hbP (chiReChar χ hsq) z` is `2 < p < z` with `χ_ℝ(p) = 1 ≠ −1`, hence divides
`excPrimorial χ z`; so `excPrimorial`-coprimality gives `hbP`-coprimality.  Class **A**, cap 60.
Red-first: `Nat.Coprime.coprime_dvd_right` with `hbP ∣ excPrimorial` proved by
`Finset.prod_dvd_prod_of_subset` after `hbSiftSet_chiReChar`.  Consumer: `hbDataN8_S3_eq`. -/
theorem l2cWindow_coprime_hbP (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) :
    ∀ n ∈ l2cWindow χ z x, Nat.Coprime (n * (n + 2)) (hbP (chiReChar χ hsq) (z : ℝ)) := by
  sorry

/-- **THE N8 WIRE.**  The `HBSieveData` at the N8 window: character `chiReChar χ hsq`,
modulus `hbP`, `support := l2cWindow χ z x`, `val n = n(n+2)`, `a n = Λ*(n)Λ*(n+2)` with
HB's Lemma 1 (`LamStar_nonneg`) as `a_nonneg`.  A definition (no obligation).  This supersedes
`hbData` (`SieveWire.lean`) on the crown path; both are wires, neither is an estimate. -/
noncomputable def hbDataN8 (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ}
    (hz : 2 ≤ z) (x : ℕ) : HBSieveData :=
  HBSieveData.ofHbP (chiReChar χ hsq) (z := (z : ℝ)) (by exact_mod_cast hz)
    (l2cWindow χ z x) (fun n => n * (n + 2))
    (fun n => LamStar χ z n * LamStar χ z (n + 2))
    (fun n _ => mul_nonneg (LamStar_nonneg χ hsq z n) (LamStar_nonneg χ hsq z (n + 2)))

/-- The N8 wire sifts by HB's own modulus. -/
theorem hbDataN8_P (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (x : ℕ) : (hbDataN8 χ hsq hz x).P = hbP (chiReChar χ hsq) (z : ℝ) := rfl

/-- **ONE `S⁽³⁾` (seam S2 closed with no residual).**  The interface's sifted sum at the N8
wire IS the star step's `S3` on the N8 window — the `(l, P) = 1` filter is the identity there
(`l2cWindow_coprime_hbP`).  Class **A**, cap 40.  Red-first: unfold `HBSieveData.S3`, then
`Finset.filter_true_of_mem`.  Consumer: `hb_p200_upper`, `hb_p200_lower`. -/
theorem hbDataN8_S3_eq (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (x : ℕ) :
    (hbDataN8 χ hsq hz x).S3 = S3 χ z (l2cWindow χ z x) := by
  sorry

/-- **The N5 exit at the N8 wire** — `hbSieve_fl_sandwich` at `hbDataN8`, with the sifted sum
rewritten through `hbDataN8_S3_eq`.  Class **A**, cap 60 (the mirror of `hbData_fl_sandwich`,
mechanical).  Consumer: `hb_p200_upper`, `hb_p200_lower`.  Only conclusion (1) is restated
here; (2) and (3) are read directly off `hbSieve_fl_sandwich (hbDataN8 …)`. -/
theorem hbDataN8_sandwich (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ}
    (hz : 2 ≤ z) (x : ℕ) {lam sRatio : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hzt : zThresh lam ≤ (z : ℝ)) (hs : levelE (Lam4 lam (z : ℝ)) ≤ sRatio) :
    lamSum (Lam4 lam (z : ℝ)) (z : ℝ) 2 (flB sRatio (Lam4 lam (z : ℝ)))
          (hbP (chiReChar χ hsq) (z : ℝ)) (hbDataN8 χ hsq hz x).S
        ≤ S3 χ z (l2cWindow χ z x)
      ∧ S3 χ z (l2cWindow χ z x)
        ≤ lamSum (Lam4 lam (z : ℝ)) (z : ℝ) 1 (flB sRatio (Lam4 lam (z : ℝ)))
            (hbP (chiReChar χ hsq) (z : ℝ)) (hbDataN8 χ hsq hz x).S := by
  sorry

/-! ## §2 — the swap `S⁽⁰⁾ → S⁽¹⁾` (seam S6, HB p.197) -/

/-- **The cut only removes mass.**  `S1 (l2cWindow) ≤ S1 (Ioc x (2x))`: a sub-window of
nonnegative terms.  Class **A**, cap 20.  Red-first: `Finset.sum_le_sum_of_subset_of_nonneg`
with `l2cWindow_subset` and `vonMangoldt_nonneg`.  Consumer: `hb_lemma4_l2cWindow`. -/
theorem S1_l2cWindow_le_S1_Ioc (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    S1 (l2cWindow χ z x) ≤ S1 (Finset.Ioc x (2 * x)) := by
  sorry

/-- **HB p.197, `S⁽⁰⁾ = S⁽¹⁾ + O(L⁴z)`, sharpened.**  A term `Λ(n)Λ(n+2)` dropped by the
coprimality cut has some prime `p ∣ q·excPrimorial χ z` dividing `n` or `n+2`; both are prime
powers, so `n = p^e` or `n + 2 = p^e`, and a dyadic window holds at most ONE power of each
prime on each side.  Hence at most `2` dropped terms per prime, each `≤ L′²`, over at most
`ω(q) + #{p < z} ≤ ω(q) + z` primes.  Class **B**, cap 250.  Red-first: express the
difference as a sum over `(Ioc x (2x)) \ l2cWindow`, bound the index set's cardinality by a
`biUnion` over the primes of `q·excPrimorial` of the two singleton-or-empty fibres
`{n ∈ Ioc : n = p^e}` / `{n : n + 2 = p^e}`, each `≤ 1` (`Nat.pow_lt_pow_right`-style doubling).
`hq : 0 < q` is needed: at `q = 0` the window collapses and the bound is false.
Consumer: `hb_lemma4_l2cWindow`. -/
theorem S1_Ioc_sub_S1_l2cWindow_le (χ : DirichletCharacter ℂ q) (hq : 0 < q) (z x : ℕ) :
    S1 (Finset.Ioc x (2 * x)) - S1 (l2cWindow χ z x)
      ≤ 2 * ((q.primeFactors.card : ℝ) + (z : ℝ)) * Lwin x ^ 2 := by
  sorry

/-! ## §3 — HB Lemma 4 on the N8 window (`S⁽⁰⁾ = S⁽³⁾ + error`, the pretense sum symbolic) -/

/-- **The star step at the N8 window** — `S2_sub_S3_window` at `A := l2cWindow χ z x`.
Class **A**, cap 30.  Red-first: `S2_sub_S3_window χ hsq z x hz _ (l2cWindow_subset χ z x)
(l2cWindow_excPrimorial_coprime χ z x) ε hε`.  Consumer: `hb_lemma4_l2cWindow`. -/
theorem S2_sub_S3_l2cWindow (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ)
    (hz : 1 ≤ z) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      |S2 χ (l2cWindow χ z x) - S3 χ z (l2cWindow χ z x)|
        ≤ 2 * (C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2)) ^ 2
            * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)) := by
  sorry

/-- **THE LEMMA-4 ERROR ON THE N8 WINDOW**, the three landed pieces summed with the pretense
sum SYMBOLIC: the swap (§2), the unconditional master's three terms (`hb_l2c_master_unconditional`,
`L2cCmain = 2^31`), and the star step's `x^{1+2ε}L′²/z`-grade tail.  A definition.
N9 feeds `pretenseSum_at_repulsion_floor` into the middle term and chooses `z` so that the
whole is `O(x/z₀)` — HB's Lemma 4 at `z₀ ≤ A·log log η`. -/
noncomputable def lemma4Err (χ : DirichletCharacter ℂ q) (z x : ℕ) (C ε : ℝ) : ℝ :=
  2 * ((q.primeFactors.card : ℝ) + (z : ℝ)) * Lwin x ^ 2
  + (L2cCmain * ((x : ℝ) / z0 z x)
      + L2cCmain * ((x : ℝ) / Real.log x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2)
      + L2cCmain * Real.exp (2 * z0 z x)
          * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3)
  + 2 * (C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2)) ^ 2
      * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ))

/-- **HB LEMMA 4 ON THE N8 WINDOW — the reduction terminal.**  `|S⁽⁰⁾ − S⁽³⁾| ≤ lemma4Err`
from the bare master packet `{hsq, hz100, hz8, hzx}` and `hq`.  Class **B**, cap 150.
Red-first: `S⁽⁰⁾ − S⁽³⁾ = (S⁽⁰⁾ − S⁽¹⁾) + (S⁽¹⁾ − S⁽²⁾) + (S⁽²⁾ − S⁽³⁾)` on `W := l2cWindow`;
the first bracket is in `[0, swap]` (§2), the second in `[−master, 0]` (`S1_le_S2` and
`hb_l2c_master_unconditional`), the third `≤ star` in absolute value (`S2_sub_S3_l2cWindow`);
`abs_add` three times.  Consumer: **N9** (`hb_theorem1`, the next design block: HB Theorem 1
at `z = q^{1/z₀}`), thence `twinPrimeConjecture_of_frequently_S1` (`DoorBridge.lean`), which
consumes exactly a lower bound on `S1 (Ioc x (2x))`. -/
theorem hb_lemma4_l2cWindow (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (hq : 0 < q)
    {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      |S1 (Finset.Ioc x (2 * x)) - S3 χ z (l2cWindow χ z x)| ≤ lemma4Err χ z x C ε := by
  sorry

/-! ## §4 — HB Lemma 3 at the pretense-sum level, at the repulsion floor (the live N3 join) -/

/-- **THE PRETENSE SUM AT THE REPULSION FLOOR.**  `pretenseSum_unconditional_absorbed` fired
at HB's operating point `σ = 1 + 1/L`, `σ′ = 1 + √(log η)/L`, its three `r0`-binders supplied
by `repulsion_floor_gives_lemma3_binders` (landed, `Lemma3Floor.lean`) and its floor antecedent
discharged from `hceil` by `one_sub_ceiling_le_dist_one`, the rate absorbed by
`hbCoreRate_at_hb_optimum_absorbed`.  The conclusion's inner factor is character-for-character
the one `hb_lemma3_at_repulsion_floor` carries; here it bounds `PretenseSum χ N` ITSELF, which
is what `lemma4Err` holds.  Class **B**, cap 200.  Red-first: copy the §2 proof of
`Lemma3Floor.lean` with `pretenseSum_unconditional_absorbed` in place of
`hb_lemma3_unconditional_absorbed`; the operating-point side conditions `1 < σ ≤ σ′ ≤ 2` are
`hell`/`hηq` (`√ℓ ≤ L`).  Consumer: **N9** (into `lemma4Err`'s `PretenseSum χ (2x+2)`).
`Sinv` is deliberately still an antecedent (priced by `invSq_sum_split_le`; N9's). -/
theorem pretenseSum_at_repulsion_floor {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (N : ℕ)
    {β₀ Sinv Cs L η b c k Q u : ℝ}
    (hLpos : 0 < L) (hη : η = 1 / ((1 - β₀) * L))
    (hell : 1 ≤ Real.log η) (hηq : Real.log η ≤ L) (hCs : 0 ≤ Cs)
    (hSinvC : Sinv ≤ Cs * (L ^ 2 / Real.log η))
    (hCR : 1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f)) ≤ 800 * L)
    (hβlo : 1 / 2 < β₀) (hβ1 : β₀ < 1)
    (hβ0 : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0)
    (hb : 0 < b) (hQ : 1 < Q) (hu : u = 1 - β₀)
    (hD : 0 ≤ Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
    (hlarge : (2 * b * Real.log Q / L
        + (Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
            / (2 * b * Real.log Q / L)) ^ 2 ≤ Real.log η)
    (hceil : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ ≠ (β₀ : ℂ) →
        ρ.re ≤ repulsionCeiling b c k Q u) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (β₀ : ℂ) ∈ Z ∧ 1 ≤ m (β₀ : ℂ) ∧
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ Z, (m ρ : ℝ) ≤ (Salt.SW.zeroMult χ ρ : ℝ)) ∧
      ((∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv) →
        PretenseSum χ N
          ≤ (N : ℝ) ^ (1 / L) * ((1 - β₀) * L ^ 2
              + (2 + (802 + 4 * Cs) * (L / Real.sqrt (Real.log η)))) / 2) := by
  sorry

/-! ## §5 — HB Lemma 6 (pp.199, 204–206): the three densities and the per-δ bounds

The landed sieve (`RosserDim4FL`, `RosserDim4Instance`) proves the per-δ TRANSFER
(`hb_transfer`) for ANY density dominated per-δ by `ρ₁ = ν_G`; Lemma 6 is exactly the two
hypotheses it takes, and this section proves them for `ρ₂ = ν_G·A′` and `ρ₃ = ν_G·A²` with
`A, A′` additive on the divisors of `P` and bounded at primes.  The constants are literal;
HB's `≪ BL` becomes `64·B′·L` and his `≪ L²` becomes `(128·CA·L)²` (both with ample slack,
computed in the freeze brief §2; bounded numeral amendment is pre-authorised). -/

/-- **Additivity on the divisors of a squarefree modulus.**  Mathlib has `IsMultiplicative`
(`ArithmeticFunction/Defs.lean`) and no additive sibling (the Wave C scout, §0); this is the
one N8 and Wave C-2 (row C2-07) share — Wave C imports it from here. -/
def IsAdditiveOn (P : ℕ) (A : ℕ → ℝ) : Prop :=
  A 1 = 0 ∧ ∀ d e : ℕ, d ∣ P → e ∣ P → Nat.Coprime d e → A (d * e) = A d + A e

/-- **`S^{(1)}(δ)` in closed form** (HB p.204): `ν_G` multiplicative gives
`S^{(1)}(δ) = ν_G(δ)·∏_{p ∣ P, p < p(δ)} (1 − ν_G(p))`.  Class **B**, cap 150.  Red-first:
`deltaSum` unfolds to a sum over `lowDiv P δ`; `lowDiv P δ` is the divisor set of the product
of the primes of `P` below `δ.minFac` (`mem_lowDiv`), so `sum_divisors_eq_sum_powerset` +
`nuG_isMultiplicative` + `Finset.prod_one_sub`-shape (`moebSum_nu_eq_W`'s own proof is the
template).  Consumer: `deltaSum_nuG_nonneg`, `deltaSum_nuG_mul_additive`. -/
theorem deltaSum_nuG_eq (P : ℕ) (hP : Squarefree P) (δ : ℕ) (hδ : δ ∣ P) :
    deltaSum P δ (fun d => nuG d)
      = nuG δ * ∏ p ∈ P.primeFactors.filter (fun p => p < δ.minFac), (1 - nuG p) := by
  sorry

/-- **`S^{(1)}(δ) ≥ 0`** (HB p.204, "`0 ≤ G(p) ≤ p`").  Class **B**, cap 60.  Red-first:
`deltaSum_nuG_eq`, then `nuG_pos_of_prime`/`nuG_lt_one_of_prime` factorwise (`P` odd).
Consumer: `hb_transfer_additive`, `hb_transfer_sq_additive`, `lamSum_nuG_sub_W_bounds`. -/
theorem deltaSum_nuG_nonneg (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (δ : ℕ) (hδ : δ ∣ P) :
    0 ≤ deltaSum P δ (fun d => nuG d) := by
  sorry

/-- **The one-signedness of the FL defect at `ρ₁`.**  `S₁′⁺ − S₁ ≥ 0` and `S₁ − S₁′⁻ ≥ 0`, from
`mainSum_chi_eq_W_sub_correction` (`lamSum = W − (−1)^side·Σ_δ S^{(1)}(δ)`) and
`deltaSum_nuG_nonneg`.  Class **A**, cap 60.  Consumer: `hb_p200_upper`, `hb_p200_lower`
(it is what turns `|S₁′ − S₁|` into the FL defect of `hbSieve_fl_sandwich` (2)). -/
theorem lamSum_nuG_sub_W_bounds (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) {Lam z : ℝ} {b : ℕ} (hb : 1 ≤ b) :
    0 ≤ lamSum Lam z 1 b P (fun d => nuG d) - W (hbSieve P hP hPodd)
      ∧ 0 ≤ W (hbSieve P hP hPodd) - lamSum Lam z 2 b P (fun d => nuG d) := by
  sorry

/-- **HB (3.6), the additive-twist fibre identity.**  For `A′` additive on `P`'s divisors,
`S^{(2)}(δ) = S^{(1)}(δ)·(A′(δ) − Σ_{p ∣ P, p < p(δ)} A′(p)·ν_G(p)/(1 − ν_G(p)))`.
Class **C**, cap 300.  Red-first: on `lowDiv P δ` every `e` is coprime to `δ`, so
`ν_G(δe)A′(δe) = ν_G(δ)ν_G(e)(A′(δ) + A′(e))`; the `A′(δ)` part is `deltaSum_nuG_eq`; for the
`A′(e)` part write `A′(e) = Σ_{p ∣ e} A′(p)` (additivity + squarefree) and swap the sums:
`Σ_{e ∋ p} μ(e)ν_G(e) = −ν_G(p)·∏_{p′ ≠ p}(1 − ν_G(p′))`.  Consumer:
`deltaSum_nuG_mul_additive_le`. -/
theorem deltaSum_nuG_mul_additive (P : ℕ) (hP : Squarefree P) (A' : ℕ → ℝ)
    (hA' : IsAdditiveOn P A') (δ : ℕ) (hδ : δ ∣ P) :
    deltaSum P δ (fun d => nuG d * A' d)
      = deltaSum P δ (fun d => nuG d)
          * (A' δ - ∑ p ∈ P.primeFactors.filter (fun p => p < δ.minFac),
              A' p * (nuG p / (1 - nuG p))) := by
  sorry

/-- **HB LEMMA 6 at `ρ₂ = ν_G·A′` — the per-δ domination, literal constant.**  With
`|A′(p)| ≤ B′·log p`, `log δ ≤ L`, every prime of `P` below `e^L` and `3 ≤ L`:
`|S^{(2)}(δ)| ≤ 64·B′·L·S^{(1)}(δ)`.  The `64`: `|A′(δ)| ≤ B′·L`; at `p = 3`,
`ν/(1−ν) = 5`; for `p ≥ 5`, `ν/(1−ν) ≤ 4/(p−4) ≤ 20/p`; Mertens' first theorem
(`sum_log_div_prime_le`: `Σ_{p ≤ N} log p/p ≤ log N + log 4 + 4`) gives
`≤ B′(L + 5.5 + 20(L + 5.4)) ≤ B′(21L + 114) ≤ 64·B′·L` at `L ≥ 3`.  Class **C**, cap 350.
Red-first: `deltaSum_nuG_mul_additive`, `abs_mul`, then the prime sum.  Consumer:
`hb_transfer_additive`. -/
theorem deltaSum_nuG_mul_additive_le (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A' : ℕ → ℝ) (hA' : IsAdditiveOn P A')
    {B' L : ℝ} (hB' : 0 ≤ B') (hA'p : ∀ p ∈ P.primeFactors, |A' p| ≤ B' * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L)
    (δ : ℕ) (hδ : δ ∣ P) (hδL : Real.log δ ≤ L) :
    |deltaSum P δ (fun d => nuG d * A' d)| ≤ 64 * B' * L * deltaSum P δ (fun d => nuG d) := by
  sorry

/-- **HB LEMMA 6 at `ρ₃ = ν_G·A²` — the per-δ domination, literal constant** (HB (3.7)–(3.8),
the `L²` grade — sharper than his stated `BL`, as his p.206 remark notes).  Split
`A(δe)² = A(δ)² + 2A(δ)A(e) + A(e)²` and `A(e)² = Σ_{p∣e}A(p)² + Σ_{p≠p′∣e}A(p)A(p′)`; the
diagonal is additive with `A(p)² ≤ CA²·L·log p`, the off-diagonal expands to
`∏(1−ν)·Σ_{p≠p′} A(p)A(p′)·[ν/(1−ν)](p)[ν/(1−ν)](p′) ≤ ∏(1−ν)·(Σ_p |A(p)|ν/(1−ν))²`.  Totals
`≤ CA²(461L² + 4902L + 12996)·S^{(1)}(δ) ≤ (128·CA·L)²·S^{(1)}(δ)` at `L ≥ 3`.  Class **C**,
cap 500.  Consumer: `hb_transfer_sq_additive`. -/
theorem deltaSum_nuG_mul_sq_additive_le (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A : ℕ → ℝ) (hA : IsAdditiveOn P A)
    {CA L : ℝ} (hCA : 0 ≤ CA) (hAp : ∀ p ∈ P.primeFactors, |A p| ≤ CA * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L)
    (δ : ℕ) (hδ : δ ∣ P) (hδL : Real.log δ ≤ L) :
    |deltaSum P δ (fun d => nuG d * A d ^ 2)|
      ≤ (128 * CA * L) ^ 2 * deltaSum P δ (fun d => nuG d) := by
  sorry

/-- **HB Lemma 6, the δ-free sums `S₂ ≪ BL·S₁`, identity form.**  `moebSum P (ν_G·A′)
= −W·Σ_{p ∣ P} A′(p)ν_G(p)/(1 − ν_G(p))` (the `δ = 1`, `p(δ) = ∞` case of (3.6) — note
`deltaSum P 1` is NOT `moebSum P`, since `lowDiv P 1 = {1}`; hence a separate row).
Class **B**, cap 200.  Red-first: as `deltaSum_nuG_mul_additive` over `P.divisors` with
`moebSum_nu_eq_W`.  Consumer: `moebSum_nuG_mul_additive_le`. -/
theorem moebSum_nuG_mul_additive (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A' : ℕ → ℝ) (hA' : IsAdditiveOn P A') :
    moebSum P (fun d => nuG d * A' d)
      = - W (hbSieve P hP hPodd) * ∑ p ∈ P.primeFactors, A' p * (nuG p / (1 - nuG p)) := by
  sorry

/-- **`|S₂| ≤ 64·B′·L·S₁`.**  Class **B**, cap 150 (the prime sum of
`deltaSum_nuG_mul_additive_le` without the `A′(δ)` term; `moebSum P ν_G = W > 0` by
`moebSum_nu_eq_W`, `W_pos`).  Consumer: `hb_p200_upper`, `hb_p200_lower`. -/
theorem moebSum_nuG_mul_additive_le (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A' : ℕ → ℝ) (hA' : IsAdditiveOn P A')
    {B' L : ℝ} (hB' : 0 ≤ B') (hA'p : ∀ p ∈ P.primeFactors, |A' p| ≤ B' * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L) :
    |moebSum P (fun d => nuG d * A' d)| ≤ 64 * B' * L * moebSum P (fun d => nuG d) := by
  sorry

/-- **`|S₃| ≤ (128·CA·L)²·S₁`.**  Class **C**, cap 300 (the off-diagonal expansion of
`deltaSum_nuG_mul_sq_additive_le` over `P.divisors`).  Consumer: `hb_p200_upper`,
`hb_p200_lower`. -/
theorem moebSum_nuG_mul_sq_additive_le (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A : ℕ → ℝ) (hA : IsAdditiveOn P A)
    {CA L : ℝ} (hCA : 0 ≤ CA) (hAp : ∀ p ∈ P.primeFactors, |A p| ≤ CA * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L) :
    |moebSum P (fun d => nuG d * A d ^ 2)|
      ≤ (128 * CA * L) ^ 2 * moebSum P (fun d => nuG d) := by
  sorry

/-- **HB's "`δ ≤ q`" at the block-Brun weights** (p.199: "to obtain the bound `δ ≤ q` we need
the sieving limit `β ≥ 3`"; here the level bound does it).  A first-failure `δ` has `δ/p(δ)`
passing `χ_ν`, so `δ/p(δ) ≤ z^{sRatio}` (`flB_level_bound`) and `p(δ) < z`; hence
`log δ ≤ (sRatio + 1)·log z`.  Class **B**, cap 120.  Consumer: `hb_transfer_additive`,
`hb_transfer_sq_additive` (their `hδL`), and `hb_p200_*` via `3·sRatio·log z ≤ L`. -/
theorem failSet_log_le (P : ℕ) (hP : Squarefree P) {Lam z sRatio : ℝ} {side : ℕ}
    (hLam : 0 < Lam) (hz : 1 < z) (hside : 1 ≤ side) (hs : levelE Lam ≤ sRatio)
    (hPz : ∀ p ∈ P.primeFactors, (p : ℝ) < z) :
    ∀ δ ∈ failSet Lam z side (flB sRatio Lam) P,
      Real.log δ ≤ (sRatio + 1) * Real.log z := by
  sorry

/-- **The per-δ transfer at `ρ₂`** — `hb_transfer` fed Lemma 6.  Class **A**, cap 60.
Consumer: `hb_p200_upper`, `hb_p200_lower`. -/
theorem hb_transfer_additive (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) {Lam z : ℝ} {side b : ℕ}
    (hb : 1 ≤ b) (hside : side ≤ 2) (A' : ℕ → ℝ) (hA' : IsAdditiveOn P A')
    {B' L : ℝ} (hB' : 0 ≤ B') (hA'p : ∀ p ∈ P.primeFactors, |A' p| ≤ B' * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L)
    (hfailL : ∀ δ ∈ failSet Lam z side b P, Real.log δ ≤ L) :
    |lamSum Lam z side b P (fun d => nuG d * A' d) - moebSum P (fun d => nuG d * A' d)|
      ≤ 64 * B' * L
          * |lamSum Lam z side b P (fun d => nuG d) - moebSum P (fun d => nuG d)| := by
  sorry

/-- **The per-δ transfer at `ρ₃`** — `hb_transfer` fed Lemma 6.  Class **A**, cap 60.
Consumer: `hb_p200_upper`, `hb_p200_lower`. -/
theorem hb_transfer_sq_additive (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) {Lam z : ℝ} {side b : ℕ}
    (hb : 1 ≤ b) (hside : side ≤ 2) (A : ℕ → ℝ) (hA : IsAdditiveOn P A)
    {CA L : ℝ} (hCA : 0 ≤ CA) (hAp : ∀ p ∈ P.primeFactors, |A p| ≤ CA * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L)
    (hfailL : ∀ δ ∈ failSet Lam z side b P, Real.log δ ≤ L) :
    |lamSum Lam z side b P (fun d => nuG d * A d ^ 2) - moebSum P (fun d => nuG d * A d ^ 2)|
      ≤ (128 * CA * L) ^ 2
          * |lamSum Lam z side b P (fun d => nuG d) - moebSum P (fun d => nuG d)| := by
  sorry

/-! ## §6 — HB Lemma 5 as an INTERFACE (N7's exit) and the p.200 assembly -/

/-- **HB LEMMA 5, AS THE INTERFACE N7 FILLS AND N8 CONSUMES** (p.199; the Wave C scout's §1
says "write the exit to the consumer at `RosserDim4Instance.lean:558`, not invented" — this
is that consumer, made explicit).  For a sieve situation `H` (in practice `hbDataN8 …`):

    S(d) = κ·(G(d)/d)·{LL² + A(d)² + A′(d) + C₀} + O(x·L⁴·z⁻¹·d⁻¹·4^{ω(d)})

for `d ∣ P`, `(d, α) = 1`, `d ≤ q^{1/3}` (spelled `d³ ≤ e^L`, `L = log q`), with `A, A′`
additive on `P`'s divisors, `|A(p)| ≤ CA·log p`, `|A′(p)| ≤ CA′·B·log p`, `|C₀| ≤ CC·B·L`,
`B = L + |LL|`, `LL = L′(1,χ)/L(1,χ)` (a free real here; N9 identifies it with N4's `(L1)`
terminal).  Every `≪` of the paper is a literal parameter: **Wave C-2 (row C2-10) must print
`CA CA' CC Cerr`**, and the `x` is produced by the `t`-integration (scout §5), never carried.
Producer: Wave C-2 at `H := hbDataN8 χ hsq hz x`.  Consumers: `hb_p200_upper`, `hb_p200_lower`. -/
structure Lemma5Eval (H : HBSieveData) (α : ℕ) (x L LL kappa C₀ Cerr CA CA' CC : ℝ)
    (A A' : ℕ → ℝ) : Prop where
  A_add : IsAdditiveOn H.P A
  A'_add : IsAdditiveOn H.P A'
  A_prime : ∀ p ∈ H.P.primeFactors, |A p| ≤ CA * Real.log p
  A'_prime : ∀ p ∈ H.P.primeFactors, |A' p| ≤ CA' * (L + |LL|) * Real.log p
  C₀_le : |C₀| ≤ CC * (L + |LL|) * L
  eval : ∀ d ∈ H.P.divisors, Nat.Coprime d α → (d : ℝ) ^ 3 ≤ Real.exp L →
    |H.S d - kappa * (hbG α d / d) * (LL ^ 2 + A d ^ 2 + A' d + C₀)|
      ≤ Cerr * x * L ^ 4 / (H.z * d) * (4 : ℝ) ^ d.primeFactors.card

/-- **`G(d)/d = ν_G(d)` off `α`.**  `hbG α d = 2^{ω(d)}∏(2p−1)/(p+1) = ∏_{p∣d} G(p) = ω_G(d)`
when `(d, α) = 1`.  Class **A**, cap 60.  Red-first: `Finset.prod_mul_distrib` +
`Finset.prod_const` against `omegaG`/`Gdens`.  Consumer: `hb_p200_upper`, `hb_p200_lower`. -/
theorem hbG_div_eq_nuG {α d : ℕ} (hd : d ≠ 0) (hdα : Nat.Coprime d α) :
    hbG α d / (d : ℝ) = nuG d := by
  sorry

/-- **The (2.3) error sum** `Σ_{d ∣ P} 4^{ω(d)}/d` — a definition, so the p.200 rows carry it
by name and `n8ErrSum_le` prices it once. -/
noncomputable def n8ErrSum (P : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, (4 : ℝ) ^ d.primeFactors.card / (d : ℝ)

/-- **Mertens' second constant, explicit** — the `C` of `sum_inv_prime_le_aux`
(`Salt/Maynard/Mertens.lean`): `Σ_{p ≤ n} 1/p ≤ log log n + mertens2C` for `n ≥ 2`. -/
noncomputable def mertens2C : ℝ :=
  1 + 2 * (Real.log 4 + 4) / Real.log 2 - Real.log (Real.log 2)

/-- **HB (2.3): `Σ_{d∣P} 4^{ω(d)}/d ≪ L⁴`.**  `= ∏_{p ∣ P}(1 + 4/p) ≤ exp(4·Σ_{p<z} 1/p)
≤ exp(4·(log log z + mertens2C)) = e^{4·mertens2C}·(log z)⁴`.  Class **B**, cap 200.
Red-first: `sum_divisors_eq_sum_powerset` + `Finset.prod_add`-shape for the product identity,
`Real.add_one_le_exp` factorwise, `sum_inv_prime_le_aux`.  Consumer: `hb_p200_upper`,
`hb_p200_lower` (through N9's `log z ≤ L`). -/
theorem n8ErrSum_le (P : ℕ) (hP : Squarefree P) {z : ℕ} (hz : 2 ≤ z)
    (hPz : ∀ p ∈ P.primeFactors, p ≤ z) :
    n8ErrSum P ≤ Real.exp (4 * mertens2C) * Real.log z ^ 4 := by
  sorry

/-- **The N8 Lemma-6 constant**: `64·CA′ + (128·CA)² + CC` — the sum of the three
per-density constants, so that `S₂ + S₃ + C₀S₁ ≤ n8C6·B·L·S₁` (using `L² ≤ B·L`). -/
noncomputable def n8C6 (CA CA' CC : ℝ) : ℝ := 64 * CA' + (128 * CA) ^ 2 + CC

/-- **HB p.200, THE UPPER ASSEMBLY.**  From the sandwich (2.2) at the N8 wire, Lemma 5 as the
interface `Lemma5Eval`, Lemma 6 (§5), the FL defect (`hbSieve_fl_sandwich` (2), side 1:
`S₁′⁺ ≤ W(1 + λ·C·e^{−cs})`, `C = flConst λ Λ₄`, `c = flRate λ`) and the per-δ transfers:

    S⁽³⁾ ≤ κ·W·(1 + λCe^{−cs})·(LL² + n8C6·B·L) + Cerr·x·L⁴·z⁻¹·n8ErrSum P.

HB's form `κS₁{(L′/L)² + O(BL) + O(B²e^{−z₀/4})} + O(xL⁸z⁻¹)` is this at `S₁ = W`
(`hbS1_eq_W`), `LL² ≤ B²`, and `n8ErrSum ≤ e^{4·mertens2C}L⁴` (`n8ErrSum_le`).
Hypotheses: the sieve's operating packet (`hlam hlam' hzt hs`), HB's `D = q^{1/3}` as
`3·sRatio·log z ≤ L` (so every kept `d` has `d³ ≤ e^L` by `flB_level_bound`, and every
first-failure `δ` has `log δ ≤ L` by `failSet_log_le`), `1 < z`, `κ ≥ 0`, and
`(P, α) = 1` (true at the twin instance `α = 4`: `P` is odd).
Class **C**, cap 600.  Red-first: `Σ_d λ⁺_d S(d) = κ Σ_d λ⁺_d ν_G(d)(LL² + A² + A′ + C₀)
+ Σ_d λ⁺_d e_d` with `|e_d| ≤ Cerr·x·L⁴/(z·d)·4^{ω(d)}` and `|λ_d| ≤ 1`; the main sum is
`κ(LL²·S₁′ + S₃′ + S₂′ + C₀·S₁′)`; bound `S₂′ ≤ |S₂| + |S₂′ − S₂|` by
`moebSum_nuG_mul_additive_le` + `hb_transfer_additive` + `lamSum_nuG_sub_W_bounds`; same for
`S₃′`.  Consumer: **N9** (`hb_theorem1`, with `kappa := hbKappa χ α x (hbL1 χ z)` and
`LL` from N4's `(L1)`). -/
theorem hb_p200_upper (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz : 2 ≤ z) {lam sRatio : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hzt : zThresh lam ≤ (z : ℝ)) (hs : levelE (Lam4 lam (z : ℝ)) ≤ sRatio)
    {α : ℕ} {L LL kappa C₀ Cerr CA CA' CC : ℝ} {A A' : ℕ → ℝ}
    (hL3 : 3 ≤ L) (hD : 3 * sRatio * Real.log z ≤ L)
    (hPα : Nat.Coprime (hbDataN8 χ hsq hz x).P α) (hκ : 0 ≤ kappa)
    (hL5 : Lemma5Eval (hbDataN8 χ hsq hz x) α x L LL kappa C₀ Cerr CA CA' CC A A') :
    S3 χ z (l2cWindow χ z x)
      ≤ kappa * W (hbDataN8 χ hsq hz x).sieve
          * (1 + lam * flConst lam (Lam4 lam (z : ℝ)) * Real.exp (-(flRate lam) * sRatio))
          * (LL ^ 2 + n8C6 CA CA' CC * (L + |LL|) * L)
        + Cerr * x * L ^ 4 / (z : ℝ) * n8ErrSum (hbDataN8 χ hsq hz x).P := by
  sorry

/-- **HB p.200, THE LOWER ASSEMBLY** ("an analogous argument shows
`S⁽³⁾ ≥ x𝔖C(α) + O(xe^{−z₀/4})`").  Side 2 of the sandwich with the FL lower endpoint
`W(1 − C·e^{−cs}) ≤ S₁′⁻ ≤ W`:

    S⁽³⁾ ≥ κ·W·(LL²·(1 − Ce^{−cs}) − n8C6·B·L·(1 + Ce^{−cs})) − Cerr·x·L⁴·z⁻¹·n8ErrSum P.

Same hypotheses and route as `hb_p200_upper`; class **C**, cap 400 (the mirror, once the
upper's bookkeeping lemmas exist).  Consumer: **N9** (`hb_theorem1` — THIS is the sign the
door consumes: a LOWER bound on `S⁽³⁾`, hence on `S1 (Ioc x (2x))` through
`hb_lemma4_l2cWindow`, is what `twinPrimeConjecture_of_frequently_S1` needs). -/
theorem hb_p200_lower (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz : 2 ≤ z) {lam sRatio : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hzt : zThresh lam ≤ (z : ℝ)) (hs : levelE (Lam4 lam (z : ℝ)) ≤ sRatio)
    {α : ℕ} {L LL kappa C₀ Cerr CA CA' CC : ℝ} {A A' : ℕ → ℝ}
    (hL3 : 3 ≤ L) (hD : 3 * sRatio * Real.log z ≤ L)
    (hPα : Nat.Coprime (hbDataN8 χ hsq hz x).P α) (hκ : 0 ≤ kappa)
    (hL5 : Lemma5Eval (hbDataN8 χ hsq hz x) α x L LL kappa C₀ Cerr CA CA' CC A A') :
    kappa * W (hbDataN8 χ hsq hz x).sieve
        * (LL ^ 2 * (1 - flConst lam (Lam4 lam (z : ℝ)) * Real.exp (-(flRate lam) * sRatio))
            - n8C6 CA CA' CC * (L + |LL|) * L
                * (1 + flConst lam (Lam4 lam (z : ℝ)) * Real.exp (-(flRate lam) * sRatio)))
      - Cerr * x * L ^ 4 / (z : ℝ) * n8ErrSum (hbDataN8 χ hsq hz x).P
      ≤ S3 χ z (l2cWindow χ z x) := by
  sorry

/-! ## §7 — the `κS₁` wire: HB's `S₁` (p.207, N4's object) IS the sieve's `W` -/

/-- **`S₁ = W`.**  N4's `(L2)` terminal (`hb_L2_at_split_point_charTrio`) evaluates
`hbKappa · hbS1 χ α z`, where `hbS1` is the product over primes `p ≤ ⌊z⌋`, `χ_ℝ(p) = 1`,
`p ∤ α` of `(p−1)(p−2)/(p(p+1))`; the sieve's `W` is the product over `2 < p < z`,
`χ_ℝ(p) = 1` of `1 − G(p)/p`.  At an integer `z` the index sets agree at `hbS1`'s argument
`z − 1` once `p ∤ α ↔ 2 < p` on primes (`2 ∣ α` and every odd prime is prime to `α` — true at
the twin instance `α = 4`), and the factors agree by `one_sub_hbG_div_eq`.  Class **B**,
cap 200.  Red-first: `hbSiftSet_chiReChar` + `Finset.prod_congr` after an `ext` on the two
filters.  Consumer: **N9** (composes N4's `κS₁ = (1+δ)x𝔖C(α)/(ηL)²` into `hb_p200_*`'s
`kappa · W`). -/
theorem hbS1_eq_W (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (x : ℕ) {α : ℕ} (hα2 : 2 ∣ α) (hαodd : ∀ p : ℕ, p.Prime → p ∣ α → p = 2) :
    hbS1 χ α ((z : ℝ) - 1) = W (hbDataN8 χ hsq hz x).sieve := by
  sorry

end Salt.HB
