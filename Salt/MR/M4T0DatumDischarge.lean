/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4T0Datum
import Salt.MR.LambdaChiMask
import Salt.MR.RamareMassTail

/-!
# ⟦D3-DISCHARGE⟧ — the `T₀`-band's `hpiece` slot, DISCHARGED at the door datum

Design: the 0730 council's **C5** (`docs/blueprints/flags.md`, ⟦THE 0730 COUNCIL⟧).
`M4T0Datum.m4_hT0band_at_door` reduced the `hT0band` slot at the door's sieved χ-twisted datum
to ONE carried binder — `hpiece`, the per-piece per-frequency twisted partial sum bound

  `∀ 𝒥 ⊆ [1,2], ∀ |t| ≤ seamT0 X, ∀ X_d ≤ k ≤ N,`
  `  ‖∑_{n ≤ k} (λχ̄·g_𝒥)(n)·n^{−it}‖ ≤ S₀·k`.

This file discharges it from the carriers landed on 2026-07-30 (`LambdaChiRamare`,
`MobiusChiRamareUnion`, `RamareMassTail`) plus the λ-at-mask twin `LambdaChiMask` minted for
it.  Purely ADDITIVE: no landed declaration is touched, and `m4_hT0band_at_door`'s binder
shape is met EXACTLY (it is FROZEN — §5's statement is a literal copy of the slot).

## THE CHAIN, LINK BY LINK

1. **§1 — the piece IS the λ-datum at a mask.**  `pieceDatum χ 𝒥 = liouChi χ · g_𝒥`
   (`CofactorSupplier.lean:71`) and `Sec9Glue.gJ 𝒥` is the indicator "no prime factor in any
   block `j ∈ 𝒥`", i.e. `[ω(n; jMask 𝒥) = 0]` — which is `r^{ω}` at `r = 0`.  So

     `pieceDatum χ 𝒥 (n)·n^{−it} = (λ·g_0)(n)·χ̄(n)n^{i(−t)}`   at the mask `jMask 𝒥`

   (`pieceDatum_twist_eq`), and the door's partial sum IS `MlamGrChiMask χ (−t) (jMask 𝒥) 0 k`
   (`piece_partial_sum_eq`).  ⟦THE SIGN⟧ the band twist is `eIu (−t)` while `chiBarTwist χ s`
   carries `n^{is}`; the carrier is therefore read at the height `s = −t`, and `|−t| = |t|`
   leaves every gate unchanged.
2. **§2 — THE GAP, NAMED AND CLOSED.**  `LambdaChiRamare` landed λ at a SINGLE window,
   `MobiusChiRamareUnion` landed μ at a GENERAL mask; the λ-at-mask combination — which is
   what `𝒥 = {1,2}` needs, the union of two disjoint blocks being no interval — **was
   missing**.  It is minted in `Salt/MR/LambdaChiMask.lean` (`MlamGrChiMask_rate`), at the
   same prices as the single-window page.  The `𝒥`-cases route (∅ / singletons / the union)
   is NOT taken: one mask-general page covers all four uniformly and is the same length as
   the union instance alone.
3. **§3 — the window rows at the mask, from the LANDED single-window pages.**  The mask
   `jMask 𝒥` is contained in any interval `[P,Q]` covering the blocks it names, and at `r = 0`
   the mask carrier is then DOMINATED pointwise by the single-window carrier
   (`maskTailWeight_zero_le_ramTailWeight_zero`: both are `0/1` indicators, and
   mask-smooth ⟹ `[P,Q]`-smooth).  So `RamareMassTail.ramTailWeight_mass_le` and
   `ramTailWeight_htail_door` — stated at a single window — discharge the mask rows with no
   new arithmetic.  ⟦DEVIATION FROM THE LEDGER'S NAMED ITEM⟧ the first-bank ledger named
   "the `r = 0` UNION MASS = the product of the two block masses via
   `blockWindow_mertens_const`".  That product is the SHARP value; the covering-interval
   route above is strictly cheaper (no new Euler-product page) and pays only a constant:
   `windowMassConst P₁ Q₂ = e^{25c}(log Q₂/log P₁)^c` instead of
   `(log Q₁/log P₁)^c(log Q₂/log P₂)^c`.  Both are `X`-free and both enter `C'` linearly, so
   the exit is indifferent — the product form is not minted.  Recorded, not hidden.
4. **§4 — the quantifier order, moved honestly.**  `MlamGrChiMask_rate`'s `∃C', x₀` is
   uniform in the mask, `q`, `χ`, `t` and `r`, while `RamareMassTail`'s tail gates are
   `y`-dependent.  The composition therefore carries `x₀ ≤ X_d` and the three tail gates
   `∀ k ∈ [X_d, N]` in-statement (`piece_partial_sum_rate`); NOTHING is absorbed into an
   `O(·)` and no threshold is hidden.
5. **§5 — the range fit and THE EXIT.**  The two door-side fits:
   * **height** — `|t| ≤ seamT0 X = (log X)^{1/45}` against the carrier's `|t| ≤ ⌊√⌊√k⌋⌋`.
     ⚠ **NOT free at the small-`k` corner**: at `X = 3` the left side is `1.0245` and the
     right side is `⌊√⌊√3⌋⌋ = 1`.  `seamT0_le_sqrt_sqrt` proves the fit under the explicit
     threshold `400 ≤ X` (`(2·(log X)^{1/45})^4 ≤ 16·X^{4/45} ≤ X` once `16 ≤ X^{41/45}`),
     which is where the corner is paid.
   * **conductor** — the carrier asks `q ≤ (log k)^{10}`; carried as `q ≤ (log X)^{10}` and
     transported up the range by `log k ≥ log X`.  The door's own gate is
     `q ≤ arcDen 12 H ≍ (log H)^{12}`, and REF-A4-4's range fit
     (`(log H)^{12} ≤ (log X)^{10}` as soon as `log H ≤ (log X)^{5/6}`) is the consumer's
     step — stated here, not performed, because it couples `H` to `X`.
   The exit `m4_hT0band_at_door_discharged` composes with `M4T0Datum.m4_hT0band_at_door` at
   the grade `S₀ = C'/(log X)^A`, and `t0datum_grade_of_fit` reduces its `hSle` binder to the
   single arithmetic gate `C' ≤ (log X)^{A − 1/2 + 1/1000}` — the refuter's chain: at `A = 10`
   this reads `log C' ≤ 9.501·loglog X`, i.e. `loglog X ≥ 19 + 0.1·log C'` with room.

## ⟦THE TRAPS RESPECTED⟧

* **the four log scales** — `log k` (the carrier's statement scale, `k ≍ X`), `log⌊k/b⌋` (where
  the λ-rate fires, inside `LambdaChiMask`), `loglog k` (the Rankin calibration), and
  `log Q/log P` (the WINDOW scale, confined to the mass/tail constants).  `seamT0 X` is read
  only as a bound on `|t|` and never as a log scale.
* **`liouChi`, never `lamChi`** — the piece is the sum-side datum; nothing pretentious is
  touched here.
* **the frozen binder** — §5's `hpiece` reproduction is character-for-character
  `M4T0Datum.m4_hT0band_at_door`'s, including the strict `Xd ≤ k`, `k ≤ N` orientation.
* **`[NeZero q]`** is the ONE structural hypothesis added beyond `m4_hT0band_at_door`'s: the
  carrier chain (`MmuChiRate` downward) is stated at nonzero moduli.
-/

open scoped BigOperators

namespace Salt.MR

/-! ## §1 — THE PIECE IS THE λ-DATUM AT A PRIME MASK

`Sec9Glue.gJ 𝒥 Pseq Qseq` is the indicator of "`n` has no prime factor in any block indexed by
`𝒥`".  That is the `r = 0` damping at the union mask `⋃_{j ∈ 𝒥}[P_j,Q_j]` — the observation
that turns the door's four pieces into four instances of ONE carrier. -/

/-- **THE `𝒥`-MASK** `1_{⋃_{j ∈ 𝒥}[P_j, Q_j]}` on primes.  At `𝒥 = ∅` it is the empty mask
(and `λ·g_0 = λ`); at a singleton it is `MobiusChiRamareUnion.blockMask`; at `𝒥 = {1,2}` it is
`unionMask`.  One definition, all four door pieces. -/
def jMask (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) : ℕ → Bool :=
  fun p => decide (∃ j ∈ 𝒥, Pseq j ≤ p ∧ p ≤ Qseq j)

@[simp] lemma jMask_iff {𝒥 : Finset ℕ} {Pseq Qseq : ℕ → ℕ} {p : ℕ} :
    jMask 𝒥 Pseq Qseq p = true ↔ ∃ j ∈ 𝒥, Pseq j ≤ p ∧ p ≤ Qseq j := by
  simp [jMask]

/-- `ω(n; mask) = 0` iff no prime factor of `n` is masked. -/
theorem maskOmega_eq_zero_iff (mask : ℕ → Bool) (n : ℕ) :
    maskOmega mask n = 0 ↔ ∀ p ∈ n.primeFactors, ¬ (mask p = true) := by
  unfold maskOmega MaskPrimeDivs
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]

/-- `ω(n; P, Q) = 0` iff no prime factor of `n` lies in `[P,Q]`. -/
theorem blockOmega_eq_zero_iff (P Q n : ℕ) :
    blockOmega P Q n = 0 ↔ ∀ p ∈ n.primeFactors, ¬ (P ≤ p ∧ p ≤ Q) := by
  unfold blockOmega BlockPrimeDivs
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]

/-- **`g_𝒥` IS THE MASK INDICATOR AT `r = 0`** (`gJ_eq_jMask_indicator`).  The whole content
is a quantifier swap: "for every block `j ∈ 𝒥`, no prime factor of `n` lies in it" is "no
prime factor of `n` lies in any block `j ∈ 𝒥`". -/
theorem gJ_eq_jMask_indicator (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (n : ℕ) :
    gJ 𝒥 Pseq Qseq n = if maskOmega (jMask 𝒥 Pseq Qseq) n = 0 then 1 else 0 := by
  have hiff : (∀ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) n = 0)
      ↔ maskOmega (jMask 𝒥 Pseq Qseq) n = 0 := by
    rw [maskOmega_eq_zero_iff]
    constructor
    · intro h p hp hmask
      obtain ⟨j, hj, hpj⟩ := jMask_iff.mp hmask
      exact ((blockOmega_eq_zero_iff _ _ n).mp (h j hj)) p hp hpj
    · intro h j hj
      rw [blockOmega_eq_zero_iff]
      intro p hp hpj
      exact h p hp (jMask_iff.mpr ⟨j, hj, hpj⟩)
  unfold gJ
  by_cases h : ∀ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) n = 0
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]

/-- `(0 : ℝ)^m` is the indicator of `m = 0` — the `r = 0` reading of the damping. -/
theorem zero_pow_eq_ite (m : ℕ) : (0 : ℝ) ^ m = if m = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · simp
  · rw [if_neg (by omega), zero_pow (by omega)]

/-- **THE DATUM IDENTIFICATION** (`pieceDatum_twist_eq`).  At every `n` and every band
frequency `t`,

  `pieceDatum χ 𝒥 Pseq Qseq (n) · n^{−it} = (λ·g_0)(n)·χ̄(n)n^{−it}`   at the mask `jMask 𝒥`.

⟦THE SIGN⟧ `eIu (−t) n = n^{−it}` while `chiBarTwist χ s n = χ̄(n)n^{is}`, so the carrier is
read at `s = −t`.  No hypothesis: the identity holds at `n = 0` too (both sides vanish). -/
theorem pieceDatum_twist_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (𝒥 : Finset ℕ)
    (Pseq Qseq : ℕ → ℕ) (t : ℝ) (n : ℕ) :
    pieceDatum χ 𝒥 Pseq Qseq n * eIu (-t) n
      = ((lamGrMask (jMask 𝒥 Pseq Qseq) 0 n : ℝ) : ℂ) * chiBarTwist χ (-t) n := by
  have hexp : eIu (-t) (n : ℝ)
      = Complex.exp ((((-t) * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [eIu]
    congr 1
    push_cast
    ring
  unfold pieceDatum liouChi liouvilleC chiBarTwist
  rw [gJ_eq_jMask_indicator, lamGrMask_apply, hexp, zero_pow_eq_ite]
  by_cases hm : maskOmega (jMask 𝒥 Pseq Qseq) n = 0
  · rw [if_pos hm, if_pos hm]
    push_cast
    ring
  · rw [if_neg hm, if_neg hm]
    push_cast
    ring

/-- **THE PARTIAL SUM IS THE CARRIER'S SUMMATORY FUNCTION** (`piece_partial_sum_eq`) — the
door's `hpiece` integrand at the mask, read at the height `−t`. -/
theorem piece_partial_sum_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (𝒥 : Finset ℕ)
    (Pseq Qseq : ℕ → ℕ) (t : ℝ) (k : ℕ) :
    ∑ n ∈ Finset.Icc 1 k, pieceDatum χ 𝒥 Pseq Qseq n * eIu (-t) n
      = MlamGrChiMask χ (-t) (jMask 𝒥 Pseq Qseq) 0 k := by
  rw [MlamGrChiMask]
  exact Finset.sum_congr rfl fun n _ => pieceDatum_twist_eq χ 𝒥 Pseq Qseq t n

/-! ## §3 — THE WINDOW ROWS AT THE MASK, FROM THE LANDED SINGLE-WINDOW PAGES

At `r = 0` both carriers are `0/1` indicators of smoothness, so a containment of masks is a
pointwise domination of carriers.  `RamareMassTail`'s two pages then discharge the mask rows
with NO new arithmetic. -/

/-- **THE DOMINATION AT `r = 0`.**  If every masked prime lies in `[P,Q]` then the mask
carrier is dominated by the single-window carrier: mask-smooth ⟹ `[P,Q]`-smooth, and both
values on the support are `1`. -/
theorem maskTailWeight_zero_le_ramTailWeight_zero {mask : ℕ → Bool} {P Q : ℕ}
    (hcov : ∀ p : ℕ, mask p = true → P ≤ p ∧ p ≤ Q) (n : ℕ) :
    maskTailWeight mask 0 n ≤ ramTailWeight P Q 0 n := by
  rw [maskTailWeight_zero_param, ramTailWeight_zero_param]
  by_cases h : n ≠ 0 ∧ MaskSmooth mask n
  · have hw : n ≠ 0 ∧ WindowSmooth P Q n :=
      ⟨h.1, fun p hp => hcov p (h.2 p hp)⟩
    rw [if_pos h, if_pos hw]
  · rw [if_neg h]
    split_ifs <;> norm_num

/-- The `𝒥`-mask is covered by any interval containing every block it names. -/
theorem jMask_covered {𝒥 : Finset ℕ} {Pseq Qseq : ℕ → ℕ} {P Q : ℕ}
    (hP : ∀ j ∈ 𝒥, P ≤ Pseq j) (hQ : ∀ j ∈ 𝒥, Qseq j ≤ Q) :
    ∀ p : ℕ, jMask 𝒥 Pseq Qseq p = true → P ≤ p ∧ p ≤ Q := by
  intro p hp
  obtain ⟨j, hj, hpj⟩ := jMask_iff.mp hp
  exact ⟨le_trans (hP j hj) hpj.1, le_trans hpj.2 (hQ j hj)⟩

/-- **THE MASK'S ℓ¹(1/n) MASS**, from `RamareMassTail.ramTailWeight_mass_le` at a covering
window.  `z`-free, `y`-free, `X`-free. -/
theorem jMask_mass_le {𝒥 : Finset ℕ} {Pseq Qseq : ℕ → ℕ} {P Q : ℕ} (z : ℕ)
    (hP4 : 4 ≤ P) (hPQ : P ≤ Q)
    (hP : ∀ j ∈ 𝒥, P ≤ Pseq j) (hQ : ∀ j ∈ 𝒥, Qseq j ≤ Q) :
    ∑ b ∈ Finset.Icc 1 z, maskTailWeight (jMask 𝒥 Pseq Qseq) 0 b / (b : ℝ)
      ≤ windowMassConst P Q := by
  refine le_trans (Finset.sum_le_sum ?_) (ramTailWeight_mass_le P Q z hP4 hPQ le_rfl zero_le_one)
  intro b _
  exact div_le_div_of_nonneg_right
    (maskTailWeight_zero_le_ramTailWeight_zero (jMask_covered hP hQ) b) (Nat.cast_nonneg b)

/-- **THE MASK'S RANKIN TAIL**, from `RamareMassTail.ramTailWeight_htail_door` at a covering
window — the carrier's `htail` slot VERBATIM, under that page's own three explicit gates. -/
theorem jMask_htail_le {𝒥 : Finset ℕ} {Pseq Qseq : ℕ → ℕ} {P Q : ℕ} (y : ℕ) (A : ℝ)
    (hA : 0 < A) (hP4 : 4 ≤ P) (hPQ : P ≤ Q) (hy : 16 ≤ y)
    (hgateHalf : 16 * A * Real.log (Real.log (y : ℝ)) ≤ Real.log (y : ℝ))
    (hgateO1 : 8 * A * Real.log (Real.log (y : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (y : ℝ))
    (hgateWin : Real.exp (2 * Real.exp 1
        * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
      ≤ (Real.log (y : ℝ)) ^ A)
    (hP : ∀ j ∈ 𝒥, P ≤ Pseq j) (hQ : ∀ j ∈ 𝒥, Qseq j ≤ Q) :
    ∑ b ∈ Finset.Ioc (Nat.sqrt y) y, maskTailWeight (jMask 𝒥 Pseq Qseq) 0 b / (b : ℝ)
      ≤ 1 / (Real.log (y : ℝ)) ^ A := by
  refine le_trans (Finset.sum_le_sum ?_)
    (ramTailWeight_htail_door P Q y A hA hP4 hPQ hy hgateHalf hgateO1 hgateWin
      (r := 0) le_rfl zero_le_one)
  intro b _
  exact div_le_div_of_nonneg_right
    (maskTailWeight_zero_le_ramTailWeight_zero (jMask_covered hP hQ) b) (Nat.cast_nonneg b)

/-! ## §4 — THE PIECE'S PARTIAL-SUM RATE

`MlamGrChiMask_rate` composed with §1 and §3.  The `∃C', x₀` is hoisted OUT of `k`, `q`, `χ`,
`t`, `𝒥` and the block sequences — one threshold for the whole four-piece split at every band
frequency — while the tail gates, being `y`-dependent, are carried per-`k` in-statement.  That
quantifier move is the honest one D3-CARRIERS-2's residue named. -/

/-- **⟦D3⟧ THE PIECE'S TWISTED PARTIAL SUM, AT THE RATE** (`piece_partial_sum_rate`).

For every covering window `[P,Q]` (`4 ≤ P ≤ Q`) there is a constant `C' > 0` and a threshold
`x₀` with: at every scale `k ≥ x₀` clearing the Rankin gates, every modulus `q ≤ (log k)^{10}`,
every height `|t| ≤ ⌊√⌊√k⌋⌋` and every `𝒥` whose blocks sit inside `[P,Q]`,

  `‖∑_{n ≤ k} pieceDatum χ 𝒥 Pseq Qseq (n)·n^{−it}‖ ≤ C'·k/(log k)^A`.

`C' = C·4^A·windowMassConst P Q + 1` and `x₀` depend on nothing but `A` and the window. -/
theorem piece_partial_sum_rate (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) (P Q : ℕ)
    (hP4 : 4 ≤ P) (hPQ : P ≤ Q) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧ ∀ k : ℕ, x₀ ≤ k → 16 ≤ k →
      16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ) →
      8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ) →
      Real.exp (2 * Real.exp 1
          * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
        ≤ (Real.log (k : ℝ)) ^ A →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log k) ^ (10 : ℕ) →
        ∀ t : ℝ, |t| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) →
        ∀ (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ),
          (∀ j ∈ 𝒥, P ≤ Pseq j) → (∀ j ∈ 𝒥, Qseq j ≤ Q) →
          ‖∑ n ∈ Finset.Icc 1 k, pieceDatum χ 𝒥 Pseq Qseq n * eIu (-t) n‖
            ≤ C' * k / (Real.log k) ^ A := by
  obtain ⟨C', x₀, hC'pos, hrate⟩ :=
    MlamGrChiMask_rate hMmu A hA (M := windowMassConst P Q) (Real.exp_pos _).le
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro k hk hk16 hgHalf hgO1 hgWin q _ χ hq t ht 𝒥 Pseq Qseq hP hQ
  rw [piece_partial_sum_eq]
  have hts : |(-t)| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by rwa [abs_neg]
  exact hrate k hk q χ hq (-t) hts (jMask 𝒥 Pseq Qseq) 0 le_rfl zero_le_one
    (jMask_mass_le _ hP4 hPQ hP hQ)
    (jMask_htail_le k A hA hP4 hPQ hk16 hgHalf hgO1 hgWin hP hQ)

/-! ## §5 — THE RANGE FIT AND THE EXIT

Two door-side fits and one grade gate, then `M4T0Datum.m4_hT0band_at_door` composed. -/

/-- **THE HEIGHT FIT, AND THE SMALL-`k` CORNER** (`seamT0_le_sqrt_sqrt`).

  `seamT0 X = (log X)^{1/45} ≤ ⌊√⌊√X_d⌋⌋`   whenever `400 ≤ X = X_d`.

⚠ The fit is **NOT free at the bottom of `m4_hT0band_at_door`'s own range**: at `X = 3` the
left side is `(log 3)^{1/45} ≈ 1.0245` while `⌊√⌊√3⌋⌋ = 1`.  The threshold is where the corner
is paid, and `400` is not tuned — it is the first round number for which
`16 ≤ X^{41/45}` follows from `X^{41/45} ≥ X^{1/2} = √X ≥ 20`.  The chain is
`⌈seamT0 X⌉₊^4 ≤ (2·(log X)^{1/45})^4 = 16·(log X)^{4/45} ≤ 16·X^{4/45} ≤ X`, the middle step
being `log X ≤ X`. -/
theorem seamT0_le_sqrt_sqrt {Xd : ℕ} {X : ℝ} (hXd : ((Xd : ℕ) : ℝ) = X) (hX : (400 : ℝ) ≤ X) :
    seamT0 X ≤ (Nat.sqrt (Nat.sqrt Xd) : ℝ) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hLe : Real.exp 1 ≤ X := by
    have h := Real.exp_one_lt_d9
    linarith
  have hL : (1 : ℝ) ≤ Real.log X := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos 1) hLe
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hs1 : (1 : ℝ) ≤ seamT0 X := by
    rw [seamT0]
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / 45 : ℝ) := (Real.one_rpow _).symm
      _ ≤ (Real.log X) ^ (1 / 45 : ℝ) := Real.rpow_le_rpow zero_le_one hL (by norm_num)
  set m : ℕ := ⌈seamT0 X⌉₊ with hmdef
  have hsm : seamT0 X ≤ (m : ℝ) := Nat.le_ceil _
  have hmlt : (m : ℝ) < seamT0 X + 1 := Nat.ceil_lt_add_one (by linarith)
  -- `m^4 ≤ X`
  have hpow4 : ((m : ℝ)) ^ 4 ≤ X := by
    have hb : (m : ℝ) ≤ 2 * seamT0 X := by linarith
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hstep : ((m : ℝ)) ^ 4 ≤ (2 * seamT0 X) ^ 4 := by
      gcongr
    have hkey : (2 * seamT0 X) ^ 4 = 16 * (Real.log X) ^ (4 / 45 : ℝ) := by
      rw [seamT0, mul_pow, ← Real.rpow_natCast ((Real.log X) ^ (1 / 45 : ℝ)) 4,
        ← Real.rpow_mul hL0]
      norm_num
    have hlogle : Real.log X ≤ X := by
      have := Real.log_le_sub_one_of_pos hX0
      linarith
    have hmono : (Real.log X) ^ (4 / 45 : ℝ) ≤ X ^ (4 / 45 : ℝ) :=
      Real.rpow_le_rpow hL0 hlogle (by norm_num)
    have h16 : (16 : ℝ) ≤ X ^ (41 / 45 : ℝ) := by
      have hhalf : X ^ (1 / 2 : ℝ) ≤ X ^ (41 / 45 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
      have hsqrt : X ^ (1 / 2 : ℝ) = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
      have h400 : Real.sqrt 400 = 20 := by
        rw [show (400 : ℝ) = 20 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have h20 : (20 : ℝ) ≤ Real.sqrt X := by
        rw [← h400]
        exact Real.sqrt_le_sqrt hX
      rw [hsqrt] at hhalf
      linarith
    have hprod : 16 * X ^ (4 / 45 : ℝ) ≤ X := by
      have hXp : (0 : ℝ) < X ^ (4 / 45 : ℝ) := Real.rpow_pos_of_pos hX0 _
      have hcomb : X ^ (41 / 45 : ℝ) * X ^ (4 / 45 : ℝ) = X := by
        rw [← Real.rpow_add hX0]
        norm_num
      nlinarith [h16, hXp]
    have h16m : (0 : ℝ) ≤ (16 : ℝ) := by norm_num
    calc ((m : ℝ)) ^ 4 ≤ (2 * seamT0 X) ^ 4 := hstep
      _ = 16 * (Real.log X) ^ (4 / 45 : ℝ) := hkey
      _ ≤ 16 * X ^ (4 / 45 : ℝ) := by linarith
      _ ≤ X := hprod
  -- transport to ℕ and unfold the two floors
  have hnat : m ^ 4 ≤ Xd := by
    have hcast : ((m ^ 4 : ℕ) : ℝ) ≤ ((Xd : ℕ) : ℝ) := by
      rw [hXd]
      push_cast
      exact hpow4
    exact_mod_cast hcast
  have hmsq : m ≤ Nat.sqrt (Nat.sqrt Xd) := by
    rw [Nat.le_sqrt, Nat.le_sqrt]
    calc m * m * (m * m) = m ^ 4 := by ring
      _ ≤ Xd := hnat
  calc seamT0 X ≤ (m : ℝ) := hsm
    _ ≤ (Nat.sqrt (Nat.sqrt Xd) : ℝ) := by exact_mod_cast hmsq

/-- **THE GRADE GATE, REDUCED** (`t0datum_grade_of_fit`).  `m4_hT0band_at_door`'s `hSle` at
`S₀ = C'/(log X)^A` follows from the single arithmetic gate

  `C' ≤ (log X)^{A + (−1/2 + 1/1000)}`,

because the right side of `hSle` already contains `8·(log X)^{−1/2+1/1000}` and the `C₁·e^{·}`
summand is nonnegative.  ⟦THE REFUTER'S CHAIN⟧ at `A = 10` the gate reads
`log C' ≤ 9.501·loglog X`, i.e. `loglog X ≥ 19 + 0.1·log C'` with room to spare. -/
theorem t0datum_grade_of_fit {C' X C₁ M₀ A : ℝ} (hX3 : (3 : ℝ) ≤ X) (hC₁ : 1 ≤ C₁)
    (hfit : C' ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000))) :
    8 * (C' / (Real.log X) ^ A)
      ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
          + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
  have hLpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLA : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLpos A
  have hsplit : (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000))
      = (Real.log X) ^ A * (Real.log X) ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_add hLpos _ _
  have h1 : C' / (Real.log X) ^ A ≤ (Real.log X) ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    rw [div_le_iff₀ hLA]
    calc C' ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) := hfit
      _ = (Real.log X) ^ A * (Real.log X) ^ (-(1 : ℝ) / 2 + 1 / 1000) := hsplit
      _ = (Real.log X) ^ (-(1 : ℝ) / 2 + 1 / 1000) * (Real.log X) ^ A := by ring
  have hexp : 0 < Real.exp (-(1 / (2 * Real.exp 1)) * M₀) := Real.exp_pos _
  have hpos : (0 : ℝ) ≤ C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀) := by
    have : (0 : ℝ) < C₁ := by linarith
    positivity
  linarith

/-- **⟦D3-DISCHARGE⟧ THE `hpiece` SLOT AT THE DOOR DATUM** (`m4_hpiece_at_door`).

The FROZEN binder of `M4T0Datum.m4_hT0band_at_door`, met exactly, at the grade
`S₀ = C'/(log X)^A`.  Every remaining hypothesis is carried and named:

* `x₀ ≤ X_d` — the carrier's own eventual threshold (`MlamGrChiMask_rate`);
* `400 ≤ X` — the HEIGHT fit's small-`k` corner (`seamT0_le_sqrt_sqrt`);
* `q ≤ (log X)^{10}` — the CONDUCTOR fit, transported up the range by `log k ≥ log X`;
* the three Rankin gates, per `k ∈ [X_d, N]` — `RamareMassTail`'s own, `y`-dependent, hence
  quantified inside (the honest quantifier move);
* `∀ j ∈ [1,2], P ≤ P_j` and `Q_j ≤ Q` — the covering window for the mass/tail rows. -/
theorem m4_hpiece_at_door (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) (P Q : ℕ)
    (hP4 : 4 ≤ P) (hPQ : P ≤ Q) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X : ℝ},
        ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → x₀ ≤ Xd → 16 ≤ Xd →
        (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
        (∀ j ∈ Finset.Icc 1 2, P ≤ calP (Adoor M) (3072 * M) j) →
        (∀ j ∈ Finset.Icc 1 2, calQK (Adoor M) (3072 * M) M j ≤ Q) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          Real.exp (2 * Real.exp 1
              * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
            ≤ (Real.log (k : ℝ)) ^ A) →
        ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
          ∀ k : ℕ, Xd ≤ k → k ≤ N →
            ‖∑ n ∈ Finset.Icc 1 k,
                pieceDatum χ 𝒥 (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) n
                  * eIu (-t) n‖
              ≤ (C' / (Real.log X) ^ A) * (k : ℝ) := by
  obtain ⟨C', x₀, hC'pos, hrate⟩ := piece_partial_sum_rate hMmu A hA P Q hP4 hPQ
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro q _ χ M Xd N X hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin 𝒥 h𝒥 t ht k hk1 hk2
  have h𝒥sub : 𝒥 ⊆ Finset.Icc 1 2 := Finset.mem_powerset.mp h𝒥
  have hX0 : (0 : ℝ) < X := by linarith
  have hXk : X ≤ (k : ℝ) := by
    rw [← hXd]
    exact_mod_cast hk1
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLk : Real.log X ≤ Real.log (k : ℝ) := Real.log_le_log hX0 hXk
  have hLkpos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le hLXpos hLk
  have hk16 : 16 ≤ k := le_trans h16 hk1
  have hkx₀ : x₀ ≤ k := le_trans hx₀ hk1
  -- the conductor fit, transported up the range
  have hqk : (q : ℝ) ≤ (Real.log (k : ℝ)) ^ (10 : ℕ) := by
    refine le_trans hq ?_
    gcongr
  -- the height fit, through the small-`k` corner and `√√` monotonicity
  have hth : |t| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by
    refine le_trans ht (le_trans (seamT0_le_sqrt_sqrt hXd hX400) ?_)
    exact_mod_cast Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hk1)
  have hmain := hrate k hkx₀ hk16 (hgHalf k hk1 hk2) (hgO1 k hk1 hk2) (hgWin k hk1 hk2)
    q χ hqk t hth 𝒥 _ _ (fun j hj => hcovP j (h𝒥sub hj)) (fun j hj => hcovQ j (h𝒥sub hj))
  refine le_trans hmain ?_
  have hLAX : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hLAk : (Real.log X) ^ A ≤ (Real.log (k : ℝ)) ^ A :=
    Real.rpow_le_rpow hLXpos.le hLk hA.le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [show C' / (Real.log X) ^ A * (k : ℝ) = C' * (k : ℝ) / (Real.log X) ^ A from by ring]
  exact div_le_div_of_nonneg_left (mul_nonneg hC'pos.le hk0) hLAX hLAk

/-- **⟦D3-DISCHARGE — THE EXIT⟧** (`m4_hT0band_at_door_discharged`).  `m4_hpiece_at_door`
composed with `M4T0Datum.m4_hT0band_at_door`:

  `∫_{−T₀}^{T₀} ‖dpolyA (winCutH X_d (doorChiCoeff χ M)) (seamS0 N X) t‖² dt`
  `   ≤ t0BandB X (cfbC₁ X C₁) M₀`,   `T₀ = seamT0 X = (log X)^{1/45}`,

i.e. `M4MeanSq.m4_meansq_per_chi_gen`'s `hT0band` slot at the door's sieved χ-twisted un-phased
datum, WITHOUT any per-piece hand-off left in the middle.  The `hpiece` binder that
`M4T0Datum` carried is gone; what remains are the named gates of `m4_hpiece_at_door`, the
grade fit `C' ≤ (log X)^{A−1/2+1/1000}` (reduced by `t0datum_grade_of_fit`) and
`cfb_t0band_supply_of_sup`'s own `hErr`. -/
theorem m4_hT0band_at_door_discharged (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) (P Q : ℕ)
    (hP4 : 4 ≤ P) (hPQ : P ≤ Q) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X C₁ M₀ : ℝ},
        ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
        x₀ ≤ Xd → 16 ≤ Xd →
        (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
        (∀ j ∈ Finset.Icc 1 2, P ≤ calP (Adoor M) (3072 * M) j) →
        (∀ j ∈ Finset.Icc 1 2, calQK (Adoor M) (3072 * M) M j ≤ Q) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          Real.exp (2 * Real.exp 1
              * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
            ≤ (Real.log (k : ℝ)) ^ A) →
        8 * C' ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) →
        4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
            ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
        (∫ t in (-(seamT0 X))..(seamT0 X),
            ‖dpolyA (winCutH Xd (doorChiCoeff χ M)) (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨C', x₀, hC'pos, hpiece⟩ := m4_hpiece_at_door hMmu A hA P Q hP4 hPQ
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro q _ χ M Xd N X C₁ M₀ hXd hX400 hXdN hN hC₁ hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin
    hgrade hErr
  have hX3 : (3 : ℝ) ≤ X := by linarith
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLA : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hS₀ : (0 : ℝ) ≤ C' / (Real.log X) ^ A := le_of_lt (div_pos hC'pos hLA)
  have hSle : 8 * (C' / (Real.log X) ^ A)
      ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
          + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
    refine t0datum_grade_of_fit hX3 hC₁ ?_
    calc C' ≤ 8 * C' := by linarith
      _ ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) := hgrade
  exact m4_hT0band_at_door χ M hX3 hXd hXdN hN hC₁ hS₀ hSle
    (hpiece q χ M Xd N hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin) hErr

/-! ## §6 — THE DOOR'S OWN COVERING WINDOW

The door's calibrated ladder is monotone across the two blocks it uses, so `[P₁, Q₂]` covers
both — which is the covering window `m4_hpiece_at_door` reads.  Nothing here is tuned: `calE`
is `A·G^{j−1}(j!)²` and `1 ≤ G` is all that is used. -/

/-- `calP A G 1 ≤ calP A G j` for `j ∈ {1,2}`: the ladder's lower endpoints increase. -/
theorem calP_door_ge {A G : ℕ} (hG : 1 ≤ G) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ 2) :
    calP A G 1 ≤ calP A G j := by
  unfold calP
  refine Nat.pow_le_pow_right (by norm_num) ?_
  interval_cases j
  · exact le_rfl
  · unfold calE
    calc A * G ^ (1 - 1) * (Nat.factorial 1) ^ 2 = A * 1 * 1 := by
          simp [Nat.factorial]
      _ ≤ A * G * 4 := Nat.mul_le_mul (Nat.mul_le_mul_left _ hG) (by norm_num)
      _ = A * G ^ (2 - 1) * (Nat.factorial 2) ^ 2 := by
          simp [Nat.factorial]

/-- `calQK A G M j ≤ calQK A G M 2` for `j ∈ {1,2}`: the ladder's upper endpoints increase. -/
theorem calQK_door_le {A G M : ℕ} (hG : 1 ≤ G) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ 2) :
    calQK A G M j ≤ calQK A G M 2 := by
  unfold calQK
  refine Nat.pow_le_pow_right (by norm_num) ?_
  interval_cases j
  · unfold calE
    calc (1 ^ 2 * M) * (A * G ^ (1 - 1) * (Nat.factorial 1) ^ 2) = (1 * M) * (A * 1 * 1) := by
          simp [Nat.factorial]
      _ ≤ (4 * M) * (A * G * 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num))
            (Nat.mul_le_mul (Nat.mul_le_mul_left _ hG) (by norm_num))
      _ = (2 ^ 2 * M) * (A * G ^ (2 - 1) * (Nat.factorial 2) ^ 2) := by
          simp [Nat.factorial]
  · exact le_rfl

/-- **THE DOOR'S COVERING WINDOW** (`door_cover`): `[calP A G 1, calQK A G M 2]` contains every
block the door's `𝒥 ⊆ [1,2]` names. -/
theorem door_cover (M : ℕ) (hM : 1 ≤ M) :
    (∀ j ∈ Finset.Icc 1 2, calP (Adoor M) (3072 * M) 1 ≤ calP (Adoor M) (3072 * M) j)
      ∧ (∀ j ∈ Finset.Icc 1 2,
          calQK (Adoor M) (3072 * M) M j ≤ calQK (Adoor M) (3072 * M) M 2) := by
  have hG : 1 ≤ 3072 * M := by omega
  constructor
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact calP_door_ge hG hj.1 hj.2
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact calQK_door_le hG hj.1 hj.2

/-- **THE DOOR'S COVERING WINDOW IS ADMISSIBLE** (`door_window_bounds`): `4 ≤ P₁` and
`P₁ ≤ Q₂`, the two side conditions `m4_hpiece_at_door` reads on `[P,Q]`.  Both come from the
door's own ladder: `P₁ = 2^{Adoor M}` with `Adoor M ≥ 2^{18}` (`DoorFrame.Adoor_ge_old`), and
`Q₂ ≥ Q₁ = 2^{M·Adoor M} ≥ P₁`.  With `door_cover` this closes the door instantiation: no
window hypothesis of the exit is left for the consumer. -/
theorem door_window_bounds (M : ℕ) (hM : 1 ≤ M) :
    4 ≤ calP (Adoor M) (3072 * M) 1
      ∧ calP (Adoor M) (3072 * M) 1 ≤ calQK (Adoor M) (3072 * M) M 2 := by
  have hA : 2 ^ 18 ≤ Adoor M := Adoor_ge_old M
  have hPeq : calP (Adoor M) (3072 * M) 1 = 2 ^ (Adoor M) := by rw [calP, calE_one]
  refine ⟨?_, ?_⟩
  · rw [hPeq]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (Adoor M) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · refine le_trans ?_ (calQK_door_le (j := 1) (by omega : 1 ≤ 3072 * M) le_rfl (by norm_num))
    rw [hPeq, calQK, calE_one]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have h1 : 1 ≤ 1 ^ 2 * M := by simpa using hM
    calc Adoor M = 1 * Adoor M := (one_mul _).symm
      _ ≤ (1 ^ 2 * M) * Adoor M := Nat.mul_le_mul h1 le_rfl

/-! ## §7 — ⟦THE SPLIT-HOIST⟧ (R3, 2026-07-30): LINKS 2–4 OF THE SEVEN

`LambdaChiMask.MlamGrChiMask_rate_split` has the threshold `x₀` born before the mass budget.
This section carries that split up the door chain: at each link the `∃ x₀` moves in front of
the window `(P, Q)` — which is where all the `M`-dependence of the door instantiation lives,
since the door fires the window at `(calP (Adoor M) (3072M) 1, calQK (Adoor M) (3072M) M 2)`.

Each proof is the landed proof with the `obtain`/`refine` order changed and nothing else; the
conclusions, the gate lists and the constants are byte-identical to the unsplit twins. PURELY
ADDITIVE: `piece_partial_sum_rate`, `m4_hpiece_at_door` and `m4_hT0band_at_door_discharged`
are untouched. -/

/-- **⟦D3, SPLIT-HOISTED⟧ THE PIECE'S PARTIAL SUM** (`piece_partial_sum_rate_split`) —
`piece_partial_sum_rate` with ONE threshold `x₀` serving EVERY covering window, and `C'`
(which reads the window through `windowMassConst P Q`) left after it. -/
theorem piece_partial_sum_rate_split (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℕ, ∀ (P Q : ℕ), 4 ≤ P → P ≤ Q →
      ∃ C' : ℝ, 0 < C' ∧ ∀ k : ℕ, x₀ ≤ k → 16 ≤ k →
        16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ) →
        8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ) →
        Real.exp (2 * Real.exp 1
            * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
          ≤ (Real.log (k : ℝ)) ^ A →
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          (q : ℝ) ≤ (Real.log k) ^ (10 : ℕ) →
          ∀ t : ℝ, |t| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) →
          ∀ (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ),
            (∀ j ∈ 𝒥, P ≤ Pseq j) → (∀ j ∈ 𝒥, Qseq j ≤ Q) →
            ‖∑ n ∈ Finset.Icc 1 k, pieceDatum χ 𝒥 Pseq Qseq n * eIu (-t) n‖
              ≤ C' * k / (Real.log k) ^ A := by
  obtain ⟨x₀, hsplit⟩ := MlamGrChiMask_rate_split hMmu A hA
  refine ⟨x₀, ?_⟩
  intro P Q hP4 hPQ
  obtain ⟨C', hC'pos, hrate⟩ := hsplit (windowMassConst P Q) (Real.exp_pos _).le
  refine ⟨C', hC'pos, ?_⟩
  intro k hk hk16 hgHalf hgO1 hgWin q _ χ hq t ht 𝒥 Pseq Qseq hP hQ
  rw [piece_partial_sum_eq]
  have hts : |(-t)| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by rwa [abs_neg]
  exact hrate k hk q χ hq (-t) hts (jMask 𝒥 Pseq Qseq) 0 le_rfl zero_le_one
    (jMask_mass_le _ hP4 hPQ hP hQ)
    (jMask_htail_le k A hA hP4 hPQ hk16 hgHalf hgO1 hgWin hP hQ)

/-- **⟦D3-DISCHARGE, SPLIT-HOISTED⟧ THE `hpiece` SLOT** (`m4_hpiece_at_door_split`) —
`m4_hpiece_at_door` at the window-free threshold. -/
theorem m4_hpiece_at_door_split (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℕ, ∀ (P Q : ℕ), 4 ≤ P → P ≤ Q →
      ∃ C' : ℝ, 0 < C' ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X : ℝ},
          ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → x₀ ≤ Xd → 16 ≤ Xd →
          (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
          (∀ j ∈ Finset.Icc 1 2, P ≤ calP (Adoor M) (3072 * M) j) →
          (∀ j ∈ Finset.Icc 1 2, calQK (Adoor M) (3072 * M) M j ≤ Q) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            Real.exp (2 * Real.exp 1
                * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
              ≤ (Real.log (k : ℝ)) ^ A) →
          ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
            ∀ k : ℕ, Xd ≤ k → k ≤ N →
              ‖∑ n ∈ Finset.Icc 1 k,
                  pieceDatum χ 𝒥 (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) n
                    * eIu (-t) n‖
                ≤ (C' / (Real.log X) ^ A) * (k : ℝ) := by
  obtain ⟨x₀, hsplit⟩ := piece_partial_sum_rate_split hMmu A hA
  refine ⟨x₀, ?_⟩
  intro P Q hP4 hPQ
  obtain ⟨C', hC'pos, hrate⟩ := hsplit P Q hP4 hPQ
  refine ⟨C', hC'pos, ?_⟩
  intro q _ χ M Xd N X hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin 𝒥 h𝒥 t ht k hk1 hk2
  have h𝒥sub : 𝒥 ⊆ Finset.Icc 1 2 := Finset.mem_powerset.mp h𝒥
  have hX0 : (0 : ℝ) < X := by linarith
  have hXk : X ≤ (k : ℝ) := by
    rw [← hXd]
    exact_mod_cast hk1
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLk : Real.log X ≤ Real.log (k : ℝ) := Real.log_le_log hX0 hXk
  have hLkpos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le hLXpos hLk
  have hk16 : 16 ≤ k := le_trans h16 hk1
  have hkx₀ : x₀ ≤ k := le_trans hx₀ hk1
  have hqk : (q : ℝ) ≤ (Real.log (k : ℝ)) ^ (10 : ℕ) := by
    refine le_trans hq ?_
    gcongr
  have hth : |t| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by
    refine le_trans ht (le_trans (seamT0_le_sqrt_sqrt hXd hX400) ?_)
    exact_mod_cast Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hk1)
  have hmain := hrate k hkx₀ hk16 (hgHalf k hk1 hk2) (hgO1 k hk1 hk2) (hgWin k hk1 hk2)
    q χ hqk t hth 𝒥 _ _ (fun j hj => hcovP j (h𝒥sub hj)) (fun j hj => hcovQ j (h𝒥sub hj))
  refine le_trans hmain ?_
  have hLAX : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hLAk : (Real.log X) ^ A ≤ (Real.log (k : ℝ)) ^ A :=
    Real.rpow_le_rpow hLXpos.le hLk hA.le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [show C' / (Real.log X) ^ A * (k : ℝ) = C' * (k : ℝ) / (Real.log X) ^ A from by ring]
  exact div_le_div_of_nonneg_left (mul_nonneg hC'pos.le hk0) hLAX hLAk

/-- **⟦D3-DISCHARGE — THE EXIT, SPLIT-HOISTED⟧** (`m4_hT0band_at_door_discharged_split`) —
`m4_hT0band_at_door_discharged` at the window-free threshold.  This is the link the door's
band slot consumes: `x₀` is fixed once and for all, and only the grade constant `C'` is
allowed to read the door's `M`-dependent window. -/
theorem m4_hT0band_at_door_discharged_split (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℕ, ∀ (P Q : ℕ), 4 ≤ P → P ≤ Q →
      ∃ C' : ℝ, 0 < C' ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X C₁ M₀ : ℝ},
          ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
          x₀ ≤ Xd → 16 ≤ Xd →
          (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
          (∀ j ∈ Finset.Icc 1 2, P ≤ calP (Adoor M) (3072 * M) j) →
          (∀ j ∈ Finset.Icc 1 2, calQK (Adoor M) (3072 * M) M j ≤ Q) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            Real.exp (2 * Real.exp 1
                * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
              ≤ (Real.log (k : ℝ)) ^ A) →
          8 * C' ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) →
          4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
              ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
          (∫ t in (-(seamT0 X))..(seamT0 X),
              ‖dpolyA (winCutH Xd (doorChiCoeff χ M)) (seamS0 N X) t‖ ^ 2)
            ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨x₀, hsplit⟩ := m4_hpiece_at_door_split hMmu A hA
  refine ⟨x₀, ?_⟩
  intro P Q hP4 hPQ
  obtain ⟨C', hC'pos, hpiece⟩ := hsplit P Q hP4 hPQ
  refine ⟨C', hC'pos, ?_⟩
  intro q _ χ M Xd N X C₁ M₀ hXd hX400 hXdN hN hC₁ hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin
    hgrade hErr
  have hX3 : (3 : ℝ) ≤ X := by linarith
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLA : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hS₀ : (0 : ℝ) ≤ C' / (Real.log X) ^ A := le_of_lt (div_pos hC'pos hLA)
  have hSle : 8 * (C' / (Real.log X) ^ A)
      ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
          + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
    refine t0datum_grade_of_fit hX3 hC₁ ?_
    calc C' ≤ 8 * C' := by linarith
      _ ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) := hgrade
  exact m4_hT0band_at_door χ M hX3 hXd hXdN hN hC₁ hS₀ hSle
    (hpiece q χ M Xd N hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin) hErr

end Salt.MR
