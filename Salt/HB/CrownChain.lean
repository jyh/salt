/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cMasterUncond
import Salt.HB.Lemma3Uncond
import Salt.HB.HSigmaComp

/-!
# N8, THE CHAIN HALF — HB 1983 §2's reduction `S⁽⁰⁾ → S⁽³⁾` on ONE window (design freeze v2)

**STATUS: A DESIGN FREEZE, v2 (after the refuter pass).  Every theorem below is
`sorry`-bodied by design.**  This file is one half of node N8 of the Heath-Brown engine
(`docs/sources/hb1983-notes.md` §1–§2, pp.197–198): the swap `S⁽⁰⁾ → S⁽¹⁾`, HB Lemma 4 on
the window with the pretense sum SYMBOLIC, and HB Lemma 3 at the pretense-sum level at the
repulsion floor.  The other half — the sieve wire at the window, HB Lemma 6, HB Lemma 5 as
an interface, and the p.200 assembly — is `Salt/HB/CrownAssembly.lean`; the two files share
no declaration and neither imports the other, so two executors can work them in parallel in
one checkout (one file each).  Each docstring carries the row's **class**, its **line cap**,
the **red-first idea**, and the **consumer** of the statement by Lean name.

Nothing here bears on twin primes: N8 assembles nothing on its own.  The dichotomy
`fulcrum_dichotomy` stays conditional on `hEngine` until N7 (Waves A/B/C), N8, N4's
composition wave, the `z` witness (seam S3), N9, N10 and N12 land.  N11 is closed
(`twinPrimeConjecture_of_frequently_S1`, `Salt/HB/DoorBridge.lean`, sorry-free).  The four
joins of PR #33 landed with it; one of them, `hb_lemma3_at_repulsion_floor`, is off the crown
path (see the ⛔ below).

## THE WINDOW DECISION (seam S1 of the crown census)

**ONE WINDOW: `l2cWindow χ z x`** `= {n ∈ (x, 2x] : (n(n+2), q·excPrimorial χ z) = 1}` —
HB's `(l, qP) = 1` at the minimal honest modulus, the window the unconditional master
`hb_l2c_master_unconditional` is already proved on.  The star step reaches it for free
(`S2_sub_S3_window` takes any sub-window with `excPrimorial`-coprimality, which
`l2cWindow_excPrimorial_coprime` supplies); the door (`twinWindow (2x+2) = Ioc x (2x)`,
`twinWindow_two_mul_add_two`) is reached by the swap `S1_Ioc_sub_S1_l2cWindow_le`; the
sieve reaches it through the wire `hbDataN8` (`CrownAssembly.lean`).  `honestWindow` is
SUPERSEDED for the crown path (it stays landed, untouched).

## THE TWO STATEMENT REPAIRS OF v2 (the refuter pass, 2026-09-03 18:1x)

* **The divisor-bound constant is bound BEFORE `z x`.**  v1's Lemma-4 rows concluded
  `∃ C, 0 < C ∧ …` inside the `z x` binders, so `C` could depend on `q, x` and N9 could not
  print an absolute `K₁`.  The uniformity exists in the corpus (`card_divisors_le_rpow`:
  `C` depends on `ε` alone) and the landed proof obtains `C` before touching `x` — only the
  STATEMENT threw it away.  v2 adds `S2_sub_S3_window_of_tau` (the star step with `C` a
  parameter and its defining hypothesis `hCtau`) and restates `S2_sub_S3_l2cWindow` and
  `hb_lemma4_l2cWindow` against it.  N9 calls `card_divisors_le_rpow` ONCE, outside every `x`.
* **Lemma 3 fires at `Lp := 2L`, on the `(L1)` join's packet.**  v1's
  `pretenseSum_at_repulsion_floor` inherited the N3 join's `hCR : 1600·log(80√f(1+log f))
  ≤ 800·L`, which is UNSATISFIABLE at `L = log q` (it says `6400·q·(1+log q)² ≤ q`); the
  corpus's own consumer fires the core at `Lp := 2L` (`two_mul_pretenseSum_le_at_window`,
  `Lemma7F.lean`).  v2 states the row on the zero-side packet of
  `hb_L1_one_sided_at_repulsion_floor` (`HSigmaComp.lean`) CHARACTER-FOR-CHARACTER — `hCR :
  log(80√f(1+log f)) ≤ L` (satisfiable at `L = log q` for `q ≥ 10^6`), `hSinvC` at `(2L)²`,
  `hlarge` at `B = b·log Q/L` — and fires the core at `Lp := 2L`.  So N9 hands ONE packet to
  both landed joins and to this row: the `L`-scale is `log q` everywhere, and the `η` of this
  file is the `η` of `CrownAssembly.lean` and of N9.

## WHAT N8 KEEPS SYMBOLIC (and why)

* `PretenseSum χ (2x+2)` stays a SYMBOL in the Lemma-4 error `lemma4Err` — N8's reduction is
  zero-free, exactly as HB's §2 is.  The zero enters only through
  `pretenseSum_at_repulsion_floor` (the join the crown chain actually consumes).
* `z` is free with the landed binders carried (`hz100 hz8 hzx` of the master); N9 discharges
  them at HB's `z = q^{1/z₀}`, `z₀ = A·log log η` (seam S3 is N9's, not N8's).

⛔ **A FINDING ABOUT THE LANDED N3 JOIN.**  `hb_lemma3_at_repulsion_floor`
(`Salt/HB/Lemma3Floor.lean`) joins Lemma 3 to the PARAMETRIC `hb_lemma2` shape: its antecedent
`hres : overshootMajorant χ A ≤ …` is the τ-crude majorant that the L2c campaign declared
"provably `L²`-inflated at the worst pattern and BYPASSED" (`Salt/HB/L2cCore.lean` header).  No
producer of `hres` at HB's grade exists or is planned, so that join has no consumer on the crown
path.  The join the path needs is one level down — the pretense sum itself at the floor —
and it is `pretenseSum_at_repulsion_floor` below.  The landed join stays; it is simply not on
the road.

## THE ROWS (executor order; class per the salt CLAUDE.md table)

§1 the window inclusion · §2 the swap · §3 the star step with a uniform constant, and
Lemma 4 on the window · §4 Lemma 3 at the pretense sum.
-/

open Finset
open Salt.SW

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 — the window inclusion (S1) -/

/-- **`l2cWindow ⊆ honestWindow`.**  Coprimality to `q·excPrimorial` implies coprimality to
`excPrimorial`.  Class **A**, cap 30.  Red-first: `intro n hn; exact Finset.mem_filter.mpr
⟨l2cWindow_subset χ z x hn, l2cWindow_excPrimorial_coprime χ z x n hn⟩` (both landed,
`L2cCore.lean`); or `Finset.monotone_filter_right` — NOT `filter_subset_filter`, which is
set-monotone at a fixed predicate and this is predicate-monotone at a fixed set.
Consumer: N9 (the set-level form). -/
theorem l2cWindow_subset_honestWindow (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    l2cWindow χ z x ⊆ honestWindow χ z x := by
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
Pre-authorised amendment: `2(ω(q)+z) → ≤ 4(ω(q)+z)`.  Consumer: `hb_lemma4_l2cWindow`. -/
theorem S1_Ioc_sub_S1_l2cWindow_le (χ : DirichletCharacter ℂ q) (hq : 0 < q) (z x : ℕ) :
    S1 (Finset.Ioc x (2 * x)) - S1 (l2cWindow χ z x)
      ≤ 2 * ((q.primeFactors.card : ℝ) + (z : ℝ)) * Lwin x ^ 2 := by
  sorry

/-! ## §3 — HB Lemma 4 on the N8 window (`S⁽⁰⁾ = S⁽³⁾ + error`, the pretense sum symbolic) -/

/-- **THE STAR STEP WITH A UNIFORM CONSTANT** — the landed `S2_sub_S3_window`
(`StarWindow.lean`) with the divisor-bound constant `C` a PARAMETER and its defining
hypothesis `hCtau` carried, instead of `∃ C` inside the `z x` binders.  Class **B**, cap 150.
Red-first: copy `hstar_window`'s proof (`StarWindow.lean`, from its `set Wcap` line on) with
the opening `obtain ⟨C, hC0, hCbound⟩ := card_divisors_le_rpow ε hε` DELETED — `C`, `hC0`,
`hCbound := hCtau` are now the binders — then compose with `S2_sub_S3_le` exactly as
`S2_sub_S3_window` does.  Landed files untouched.  Consumer: `S2_sub_S3_l2cWindow`. -/
theorem S2_sub_S3_window_of_tau (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ)
    (hz : 1 ≤ z) (A : Finset ℕ) (hAsub : A ⊆ Finset.Ioc x (2 * x))
    (hcop : ∀ n ∈ A, Nat.Coprime (n * (n + 2)) (excPrimorial χ z))
    {C ε : ℝ} (hε : 0 < ε) (hC0 : 0 < C)
    (hCtau : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε) :
    |S2 χ A - S3 χ z A|
      ≤ 2 * (C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2)) ^ 2
          * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)) := by
  sorry

/-- **The star step at the N8 window** — `S2_sub_S3_window_of_tau` at `A := l2cWindow χ z x`.
Class **A**, cap 30.  Red-first: `S2_sub_S3_window_of_tau χ hsq z x hz _ (l2cWindow_subset
χ z x) (l2cWindow_excPrimorial_coprime χ z x) hε hC0 hCtau`.  Consumer: `hb_lemma4_l2cWindow`. -/
theorem S2_sub_S3_l2cWindow (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ)
    (hz : 1 ≤ z) {C ε : ℝ} (hε : 0 < ε) (hC0 : 0 < C)
    (hCtau : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε) :
    |S2 χ (l2cWindow χ z x) - S3 χ z (l2cWindow χ z x)|
      ≤ 2 * (C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2)) ^ 2
          * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)) := by
  sorry

/-- **THE LEMMA-4 ERROR ON THE N8 WINDOW**, the three landed pieces summed with the pretense
sum SYMBOLIC: the swap (§2), the unconditional master's three terms (`hb_l2c_master_unconditional`,
`L2cMasterUncond.lean`, with `L2cCmain = 2^31` from `L2cMaster.lean`), and the star step's
`x^{1+2ε}L′²/z`-grade tail.  A definition (no obligation).  `C` is the divisor-bound
constant of `S2_sub_S3_window_of_tau` — a parameter, so N9 chooses it once.
N9 feeds `pretenseSum_at_repulsion_floor` into the middle term and chooses `z` so that the
whole is `O(x/z₀)` — HB's Lemma 4 at `z₀ ≤ A·log log η`.  ⚠ At N9's `z = ⌈q^{1/z₀}⌉` and
`x ∈ [q^250, q^500]` the corpus's `z0 z x = Lwin x / log z` is `≈ (250…500)·z₀`, so the
middle term's `exp(5·z0 z x)` is `(log η)^{≈2500·A}`; N9's design block must carry the two
inequalities this forces on `A` and on `C0 ≤ η` (the freeze brief §5). -/
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
from the bare master packet `{hsq, hz100, hz8, hzx}` (the landed master's binders verbatim,
`L2cMasterUncond.lean`), `hq`, and the divisor-bound packet `{hε, hC0, hCtau}` — `C` is
bound BEFORE `z x`, so the bound is uniform in `q, x` and N9 can print `K₁`.  Class **B**,
cap 150.  Red-first: `S⁽⁰⁾ − S⁽³⁾ = (S⁽⁰⁾ − S⁽¹⁾) + (S⁽¹⁾ − S⁽²⁾) + (S⁽²⁾ − S⁽³⁾)` on
`W := l2cWindow`; the first bracket is in `[0, swap]` (§2), the second in `[−master, 0]`
(`S1_le_S2` for the sign and `hb_l2c_master_unconditional` for the size — the master is
ONE-SIDED), the third `≤ star` in absolute value (`S2_sub_S3_l2cWindow`); `abs_add_le`
(NOT `abs_add`, which is not in the pin) three times.  Consumer: **N9** (`hb_theorem1`, the
next design block: HB Theorem 1 at `z = q^{1/z₀}`), thence
`twinPrimeConjecture_of_frequently_S1` (`DoorBridge.lean`), which consumes exactly a lower
bound on `S1 (Ioc x (2x))`. -/
theorem hb_lemma4_l2cWindow (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (hq : 0 < q)
    {C ε : ℝ} (hε : 0 < ε) (hC0 : 0 < C)
    (hCtau : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε)
    {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    |S1 (Finset.Ioc x (2 * x)) - S3 χ z (l2cWindow χ z x)| ≤ lemma4Err χ z x C ε := by
  sorry

/-! ## §4 — HB Lemma 3 at the pretense-sum level, at the repulsion floor (the live N3 join) -/

/-- **THE PRETENSE SUM AT THE REPULSION FLOOR, at `Lp := 2L`.**
`pretenseSum_unconditional_absorbed` (`Lemma3Uncond.lean`) fired at the corpus's operating
point `σ = 1 + 1/(2L)`, `σ′ = 1 + √(log η)/(2L)` — the point `two_mul_pretenseSum_le_at_window`
(`Lemma7F.lean`) fires it at, and the ONLY point at which the rate's `hCR` is satisfiable
with `L = log q` — with the floor antecedent discharged from `hceil` by
`one_sub_ceiling_le_dist_one` and the rate absorbed by `hbCoreRate_at_hb_optimum_absorbed`.

**The binder list is the zero-side packet of `hb_L1_one_sided_at_repulsion_floor`
(`HSigmaComp.lean`) character-for-character** — `hLpos hη hell hηq hCs hSinvC hCR hβlo hβ1
hβ0 hb hQ hu hD hlarge hceil` — so N9 instantiates the `(L1)` join and this row from ONE
packet at ONE `L`-scale (`L = log q`, `η = 1/((1−β₀)L)`).  Class **B**, cap 200.
Red-first: `repulsion_floor_gives_hsigma hb hLpos hQ hβ1 hη hu hD hlarge` gives `hr0` and
`hσ'r : √(log η)/(2L) ≤ r0/2`; `hσr : 1/(2L) ≤ r0/2` follows from `1 ≤ √(log η)` (`hell`);
the operating-point side conditions `1 < σ ≤ σ′ ≤ 2` are `hell`/`hηq` (`√ℓ ≤ ℓ ≤ L ≤ 2L`,
`L ≥ 1/2`); the rate: `hbCoreRate_at_hb_optimum_absorbed (Lp := 2 * L) (ell := Real.log η)`
with `hellL : log η ≤ 2L` and `hCR' : 1600·log(80√f(1+log f)) ≤ 800·(2L)`, both `linarith`
from the packet; finally `(1−β₀)/(1/(2L))² = (1−β₀)(2L)²` by `field_simp`.
Consumer: **N9** (into `lemma4Err`'s `PretenseSum χ (2x+2)`).  `Sinv` is deliberately still
an antecedent (priced by `invSq_sum_split_le`; N9's).  ⚠ Two A-class nodes N9 must BOOK
before the fulcrum hands this packet over: `fulcrum_zero_real_zfr`'s `hcal` (the owed numeral
`c₀ = 1/126848`) and `hq3 : 3 ≤ q` (`Fulcrum/Basic.lean`). -/
theorem pretenseSum_at_repulsion_floor {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (N : ℕ)
    {β₀ Sinv Cs L η b c k Q u : ℝ}
    (hLpos : 0 < L) (hη : η = 1 / ((1 - β₀) * L))
    (hell : 1 ≤ Real.log η) (hηq : Real.log η ≤ L) (hCs : 0 ≤ Cs)
    (hSinvC : Sinv ≤ Cs * ((2 * L) ^ 2 / Real.log η))
    (hCR : Real.log (80 * Real.sqrt f * (1 + Real.log f)) ≤ L)
    (hβlo : 1 / 2 < β₀) (hβ1 : β₀ < 1)
    (hβ0 : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0)
    (hb : 0 < b) (hQ : 1 < Q) (hu : u = 1 - β₀)
    (hD : 0 ≤ Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
    (hlarge : (b * Real.log Q / L
        + (Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
            / (b * Real.log Q / L)) ^ 2 ≤ Real.log η)
    (hceil : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ ≠ (β₀ : ℂ) →
        ρ.re ≤ repulsionCeiling b c k Q u) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (β₀ : ℂ) ∈ Z ∧ 1 ≤ m (β₀ : ℂ) ∧
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ Z, (m ρ : ℝ) ≤ (Salt.SW.zeroMult χ ρ : ℝ)) ∧
      ((∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv) →
        PretenseSum χ N
          ≤ (N : ℝ) ^ (1 / (2 * L)) * ((1 - β₀) * (2 * L) ^ 2
              + (2 + (802 + 4 * Cs) * ((2 * L) / Real.sqrt (Real.log η)))) / 2) := by
  sorry

end Salt.HB
