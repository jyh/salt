/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.MediumFloor

/-!
# GBV5 — the √D e-fold variant closes catch #62 (`D < N` → `D < (N+1)²`)

Design: `docs/blueprints/flags.md`, the `2026-07-14 GBV4 … ★ CATCH #62 ★` entry and its
`FABLE ADJUDICATION + FIX (= GBV5)`.

## STEP 0 — the verified `D < N` use-table (traced from the LANDED files)

The terminal theorem is `WindowSmallChi.general_BV_cutoff_unconditional`; its proof runs on
the CUTOFF chain (WBV4/WBV5/WBV7), not the bilinear PE chain.  Every use of `D < N` in that
chain:

| # | declaration (file) | the use | gcd-support form? |
|---|---|---|---|
| 1 | `coprimeRestrict_blockPrimeInd` (AlphaSide, `hd : d < N`) | ROOT: block primes `p > N > d` cannot divide `d`, so `coprimeRestrict (blockPrimeInd N) d = blockPrimeInd N` | **YES** — pure gcd-support |
| 2 | `cutoffTwist_sub_efold_blockPrimeInd` (WindowErrFold, `hd : d < N`) | calls #1 at the imprimitive→primitive fold: the β-side of the correction is killed, the fold is purely α-side | inherits #1 |
| 3 | `norm_cutoffTwist_sub_le_efold_blockPrimeInd` (WindowErrFold, `hd : d < N`) | triangle over #2 | inherits |
| 4 | `cutoffEfoldTerm_reorg` (WindowErrFold, `hDN : D < N`) | per `d ∈ Dset`: `d ≤ D < N` feeds #3 | inherits |
| 5 | `hErrSum_cutoff_discharge` / `hErrSum_cutoff_final'` / `hErrSum_cutoff_of_thresholds` (WindowErrFold, `hDN`) | pass-through to #4 | inherits |
| 6 | `general_BV_cutoff_closed` (WindowErrFold, `hDN`) | pass-through to #5 — the `hErrSum` leg ONLY; the `hMainEnergy` leg does NOT use it | inherits |
| 7 | `general_BV_cutoff_unconditional` (WindowSmallChi, `hDN`) | pass-through to #6 | inherits |
| 8 | `medium_survivor_price` (MediumFloor, `hDN`) | pass-through to #7; the ONLY GBV4 feeder that carries `D < N` — `hHD_of_box_disc`, `Plo_sym_of_box_disc`, `Plo_low_of_box_disc`, `hNum_at_op` are price-abstract and `D < N`-FREE | inherits |

NOT in the terminal chain (the parallel, superseded bilinear track feeding
`general_BV_closed`/SW3): `EfoldTermBeta_eq_zero` + `hPerE_reduces_to_alpha` +
`general_BV_final'` (PerEEngine2 — the β-dilation kill under `e ≤ D < N`, and the
`log D ≤ log XM` derivation, which in the cutoff chain is the separate hypothesis `hDXM`),
`EfoldTermAlpha_eq_prim`/`efold_alpha_le` (AlphaSide), `general_BV_alpha_final`
(AlphaClose), `cutoff_BV_at_op` (GlueBV — a top-piece consumer, not re-threaded here).
`smallconductor_window_sum`'s `D0 ≤ N` (WBV3) is a DIFFERENT, polylog-scale row —
unproblematic at the operating point and kept verbatim.

**STEP 0 verdict: every terminal-chain use of `D < N` is the single root use #1, which is
exactly of the gcd-support form.  Proceed with the ratified single-term fix.**

## The fix (catch #62, ratified)

`D < N` was never the honest mechanism.  For `d ≥ N` the coprime restriction drops the
block primes `p ∣ d` with `p > N` — but TWO distinct primes `> √d` cannot both divide `d`
(their product would exceed `d`), so under `hDsq : D < (N+1)²` AT MOST ONE block prime
divides any modulus `d ≤ D`: the β-side of the fold correction is a SINGLE `n = p` term
(`efold_beta_le_single` below), not zero, bounded by the trivial α-side sum `≤ X`.
Moreover the single term VANISHES for every character whose conductor `f` is divisible by
`p` (`ψ(mp) = 0`), so per modulus `d = p·d'` only the characters with conductor dividing
`d'` contribute — at most `d/p ≤ D/(N+1)` of them
(`card_conductor_not_dvd_le`, via the conductor-primitive injection and
`card (DirichletCharacter ℂ f) = φ(f)`).  The total β-crumb over the `hErrSum` sum is
```
∑_{d ≤ D} (1/φd) · (D/(N+1)) · X ≤ 4(1+log D) · (D/(N+1)) · X      (`sum_inv_totient_le`)
```
absorbed by the ONE new named threshold
`habs : 4(1+log D)·D ≤ N·M/L^A` (constant `Kabs = 1`, folded as the `+ 1` in `Kerr`).

## GLU-2 obligations created by the new named rows

* `hDsq : D < (N+1)²` per application — at the sym-band carrier `N_thm = max y (pieceN k)
  ≥ y`, so it follows from the single numeric row `D < (y+1)²` via
  `hDsq_of_carrier_floor`/`hDsq_at_sym_carrier` (operating point: `D ~ √x·L^{-B}`,
  `y = x^{1/3}`, so `y² = x^{2/3} ≫ D` with `x^{1/6}` of room);
* `habs : 4(1+log D)·D ≤ N·M/L^A` per application (operating point: LHS `~ √x·L`,
  RHS `≳ x^{2/3}/L^A` — `x^{1/6}` of room).

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

1. (deliverable 1) `two_sqrt_primes_not_both_dvd` (the arithmetic core) +
   `block_prime_dvd_unique`; `blockDrop` + support/norm lemmas;
   `cutoffTwist_coprimeRestrict_sub_efold` (the α-side Möbius fold at a FIXED primitive
   pair, generic β — the `hd`-free content of the landed identity);
   `cutoffTwist_sub_efold_sqrtD` (the honest identity: landed e-fold MINUS the β-crumb);
   **`efold_beta_le_single`** (the single-term crumb bound, with the `p ∣ conductor`
   vanishing) and `norm_cutoffTwist_sub_le_efold_sqrtD` (the per-`(d,χ)` triangle).
2. (deliverable 2) `card_conductor_not_dvd_le` (the character count) +
   `crumb_chi_sum_le`; `cutoffEfoldTerm_reorg_sqrtD` / `hErrSum_cutoff_discharge_sqrtD` /
   `general_BV_cutoff_closed_sqrtD` / **`general_BV_cutoff_sqrtD`** — the terminal
   variant, conclusion shape identical to `general_BV_cutoff_unconditional` with
   `Kerr = 2^{A+5}·Kβ' + 15360 + 1`.
3. (deliverable 3) **`medium_survivor_price_sqrtD`** (the only feeder that carried
   `D < N`); `hDsq_of_carrier_floor`/`hDsq_at_sym_carrier` (the carrier discharges);
   the price-abstract feeders re-exported at the `_sqrtD` names
   (`hHD_of_box_disc_sqrtD`, `Plo_sym_of_box_disc_sqrtD`, `Plo_low_of_box_disc_sqrtD`,
   `hNum_at_op_sqrtD` — STEP 0 found them `D < N`-free, so they coincide with the landed
   ones); and the comment-documented `example` #check-chaining `hNum_at_op_sqrtD →
   hBlock_of_window_prices → hHDblocks_of_perBlock → hBVblocks_of_generalBV`, conclusion
   character-for-character the `hBVblocks` slot of `mainA3_of_block_remainders`.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## 1. The arithmetic core — two `> √e` primes cannot both divide `e` -/

/-- **The arithmetic core (deliverable 1).**  Two distinct primes `p ≠ q`, each with square
exceeding `e`, cannot both divide `e`: their product `p·q` would divide `e`, yet
`(p·q)² = p²·q² > e²`. -/
theorem two_sqrt_primes_not_both_dvd {e p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpe : p ∣ e) (hqe : q ∣ e) (he : 0 < e) (hpe2 : e < p * p) (hqe2 : e < q * q) : False := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hdvd : p * q ∣ e := hcop.mul_dvd_of_dvd_of_dvd hpe hqe
  have hle : p * q ≤ e := Nat.le_of_dvd he hdvd
  have h1 : (p * q) * (p * q) ≤ e * e := Nat.mul_le_mul hle hle
  have h2 : e * e < (p * p) * (q * q) :=
    mul_lt_mul'' hpe2 hqe2 (Nat.zero_le _) (Nat.zero_le _)
  have h3 : (p * p) * (q * q) = (p * q) * (p * q) := by ring
  rw [h3] at h2
  exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

/-- **At most one block prime divides a modulus below `(N+1)²`.**  For `d < (N+1)²`, any two
primes `p, q > N` dividing `d` coincide: `p, q ≥ N+1` gives `p², q² ≥ (N+1)² > d`, so
`two_sqrt_primes_not_both_dvd` applies. -/
theorem block_prime_dvd_unique {N d p q : ℕ} (hdsq : d < (N + 1) * (N + 1))
    (hp : p.Prime) (hq : q.Prime) (hNp : N < p) (hNq : N < q)
    (hpd : p ∣ d) (hqd : q ∣ d) (hd : 0 < d) : p = q := by
  by_contra hne
  have hp1 : N + 1 ≤ p := hNp
  have hq1 : N + 1 ≤ q := hNq
  have hp2 : d < p * p := lt_of_lt_of_le hdsq (Nat.mul_le_mul hp1 hp1)
  have hq2 : d < q * q := lt_of_lt_of_le hdsq (Nat.mul_le_mul hq1 hq1)
  exact two_sqrt_primes_not_both_dvd hp hq hne hpd hqd hd hp2 hq2

/-! ## 2. `blockDrop` — the part of `blockPrimeInd N` that `coprimeRestrict · d` drops -/

open Classical in
/-- The block-prime mass DROPPED by the coprime restriction mod `d`: the block primes that
divide `d`.  Under `d < (N+1)²` its support is at most the single point `p` (the unique
block prime dividing `d`). -/
noncomputable def blockDrop (N d : ℕ) (n : ℕ) : ℂ :=
  if IsUnit ((n : ℕ) : ZMod d) then 0 else blockPrimeInd N n

open Classical in
/-- Pointwise: `coprimeRestrict (blockPrimeInd N) d + blockDrop N d = blockPrimeInd N`. -/
lemma coprimeRestrict_add_blockDrop (N d n : ℕ) :
    coprimeRestrict (blockPrimeInd N) d n + blockDrop N d n = blockPrimeInd N n := by
  unfold coprimeRestrict blockDrop
  by_cases hu : IsUnit ((n : ℕ) : ZMod d)
  · rw [if_pos hu, if_pos hu, add_zero]
  · rw [if_neg hu, if_neg hu, zero_add]

/-- **Support of `blockDrop`:** a nonvanishing point is a block prime dividing `d`. -/
lemma blockDrop_ne_zero {N d n : ℕ} [NeZero d] (h : blockDrop N d n ≠ 0) :
    n.Prime ∧ N < n ∧ n ∣ d := by
  unfold blockDrop at h
  by_cases hu : IsUnit ((n : ℕ) : ZMod d)
  · rw [if_pos hu] at h; exact absurd rfl h
  · rw [if_neg hu] at h
    unfold blockPrimeInd at h
    by_cases hb : N < n ∧ n.Prime
    · refine ⟨hb.2, hb.1, ?_⟩
      have hnc : ¬ Nat.Coprime n d := fun hc => hu ((ZMod.isUnit_iff_coprime n d).mpr hc)
      exact not_not.mp (fun hnd => hnc ((hb.2.coprime_iff_not_dvd).mpr hnd))
    · rw [if_neg hb] at h; exact absurd rfl h

/-- `‖blockDrop‖ ≤ 1` (it is `0` or `blockPrimeInd`, and `‖blockPrimeInd‖ ≤ 1`). -/
lemma norm_blockDrop_le_one (N d n : ℕ) : ‖blockDrop N d n‖ ≤ 1 := by
  unfold blockDrop
  split_ifs
  · rw [norm_zero]; norm_num
  · exact blockPrimeInd_norm_le_one N n

/-! ## 3. The α-side Möbius fold at a fixed primitive pair (generic `β`)

The `hd`-free content of the landed `cutoffTwist_sub_efold_blockPrimeInd`: for ANY `β` and
ANY character `ψ mod f`, the coprime restriction of `α` mod `d` unfolds into the μ-weighted,
`ψ`-modulated sum of dilated-and-shrunk cutoff twists.  (In the landed lemma this was inlined
after the `d < N` collapse of the β-restriction; here it is exposed so the honest identity
can subtract the β-crumb separately.) -/

open Classical in
/-- **The α-side Möbius e-fold at a fixed primitive pair (FULL, generic `β`).**
`cutoffTwist (coprimeRestrict α d) β (f,ψ) − cutoffTwist α β (f,ψ)
  = ∑_{e∣d, e>1} μ(e)·ψ(e)·cutoffTwist (α∘(e·)) β (⌊X/e⌋, Y, ⌊T/e⌋) (f,ψ)`.
Byte-for-byte the landed steps 1–2 of `cutoffTwist_sub_efold_blockPrimeInd`
(`notUnit_eq_neg_sum_moebius` + `reindex_mult` + the cutoff reindex + `ψ` multiplicativity);
no hypothesis on `d`, `β`, `f`, `ψ` beyond `NeZero d`. -/
theorem cutoffTwist_coprimeRestrict_sub_efold (d : ℕ) [NeZero d] (α β : ℕ → ℂ)
    (X Y T f : ℕ) (ψ : DirichletCharacter ℂ f) :
    cutoffTwist (coprimeRestrict α d) β X Y T f ψ - cutoffTwist α β X Y T f ψ
      = ∑ e ∈ efoldSet d,
          (ArithmeticFunction.moebius e : ℂ) * ψ ((e : ℕ) : ZMod f)
            * cutoffTwist (fun m' => α (e * m')) β (X / e) Y (T / e) f ψ := by
  -- Step 1: rewrite the difference as `∑_m (∑_e [e∣m]μe) · Inner(m)`.
  have hstep1 : cutoffTwist (coprimeRestrict α d) β X Y T f ψ - cutoffTwist α β X Y T f ψ
      = ∑ m ∈ Finset.Icc 1 X,
          (∑ e ∈ efoldSet d, (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0))
            * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
                α m * β n * ψ ((m * n : ℕ) : ZMod f) := by
    unfold cutoffTwist
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hcoeff : coprimeRestrict α d m - α m
        = (∑ e ∈ efoldSet d, (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0)) * α m := by
      have hnu := notUnit_eq_neg_sum_moebius d m
      have hS : (∑ e ∈ efoldSet d, (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0))
          = -(if ¬ IsUnit ((m : ℕ) : ZMod d) then (1 : ℂ) else 0) := by rw [hnu]; ring
      rw [hS]; unfold coprimeRestrict
      by_cases hu : IsUnit ((m : ℕ) : ZMod d) <;> simp [hu]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [show coprimeRestrict α d m * β n * ψ ((m * n : ℕ) : ZMod f)
            - α m * β n * ψ ((m * n : ℕ) : ZMod f)
          = (coprimeRestrict α d m - α m) * (β n * ψ ((m * n : ℕ) : ZMod f)) by ring, hcoeff]
    ring
  rw [hstep1]
  -- Step 2: distribute the `∑_e` and swap to pull `e` outermost.
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have he0 : 0 < e := by
    simp only [efoldSet, Finset.mem_filter, Nat.mem_divisors] at he; omega
  have he1 : 1 ≤ e := he0
  have hmob : ∀ m,
      (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0)
          * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
              α m * β n * ψ ((m * n : ℕ) : ZMod f)
        = if e ∣ m then (ArithmeticFunction.moebius e : ℂ)
            * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
                α m * β n * ψ ((m * n : ℕ) : ZMod f) else 0 := by
    intro m; split <;> ring
  rw [Finset.sum_congr rfl (fun m _ => hmob m), ← Finset.sum_filter, ← Finset.mul_sum,
    reindex_mult e X he1 (fun m => ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
      α m * β n * ψ ((m * n : ℕ) : ZMod f))]
  -- per m': the cutoff reindex `e·m'·n ≤ T ⟺ m'·n ≤ T/e` and `ψ` multiplicativity.
  have hInner : ∀ m' : ℕ,
      (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => e * m' * n ≤ T),
          α (e * m') * β n * ψ ((e * m' * n : ℕ) : ZMod f))
        = ψ ((e : ℕ) : ZMod f) * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m' * n ≤ T / e),
            α (e * m') * β n * ψ ((m' * n : ℕ) : ZMod f) := by
    intro m'
    have hfe : (Finset.Icc 1 Y).filter (fun n => e * m' * n ≤ T)
        = (Finset.Icc 1 Y).filter (fun n => m' * n ≤ T / e) := by
      refine Finset.filter_congr (fun n _ => ?_)
      rw [show e * m' * n = m' * n * e by ring]
      exact (Nat.le_div_iff_mul_le he0).symm
    rw [hfe, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [show (e * m' * n : ℕ) = (e * (m' * n) : ℕ) by ring, Nat.cast_mul, map_mul]
    ring
  rw [Finset.sum_congr rfl (fun m' _ => hInner m'), ← Finset.mul_sum]
  rw [show cutoffTwist (fun m' => α (e * m')) β (X / e) Y (T / e) f ψ
        = ∑ m' ∈ Finset.Icc 1 (X / e),
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m' * n ≤ T / e),
              α (e * m') * β n * ψ ((m' * n : ℕ) : ZMod f) from rfl]
  ring

/-! ## 4. The honest e-fold identity and the single-term β-crumb (deliverable 1) -/

open Classical in
/-- **The honest cutoff e-fold identity (no `d < N`).**  For ANY modulus `d`, the
imprimitive-vs-primitive difference of the windowed twist is the landed α-side Möbius e-fold
MINUS the β-crumb — the primitive twist of the dropped block-prime mass `blockDrop N d`
against the coprime-restricted `α`:
```
cutoffTwist α β X Y T d χ − cutoffTwist α β X Y T (cond χ) χ⋆
  = ∑_{e∣d, e>1} μ(e)·χ⋆(e)·cutoffTwist (α∘(e·)) β (⌊X/e⌋, Y, ⌊T/e⌋) (cond χ) χ⋆
    − cutoffTwist (coprimeRestrict α d) (blockDrop N d) X Y T (cond χ) χ⋆.
```
Fold (`cutoffTwist_coprimeRestrict_primitive`) + β-linearity
(`coprimeRestrict_add_blockDrop`) + the generic α-fold
(`cutoffTwist_coprimeRestrict_sub_efold`).  Setting `d < N` kills the crumb
(`coprimeRestrict_blockPrimeInd`) and recovers the landed identity. -/
theorem cutoffTwist_sub_efold_sqrtD {d N : ℕ} [NeZero d] (α : ℕ → ℂ) (X Y T : ℕ)
    (χ : DirichletCharacter ℂ d) :
    cutoffTwist α (blockPrimeInd N) X Y T d χ
        - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter
      = (∑ e ∈ efoldSet d,
          (ArithmeticFunction.moebius e : ℂ)
            * χ.primitiveCharacter ((e : ℕ) : ZMod χ.conductor)
            * cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
                χ.conductor χ.primitiveCharacter)
        - cutoffTwist (coprimeRestrict α d) (blockDrop N d) X Y T
            χ.conductor χ.primitiveCharacter := by
  have hfold := cutoffTwist_coprimeRestrict_primitive α (blockPrimeInd N) X Y T χ
  have hβsplit : cutoffTwist (coprimeRestrict α d) (coprimeRestrict (blockPrimeInd N) d)
        X Y T χ.conductor χ.primitiveCharacter
      = cutoffTwist (coprimeRestrict α d) (blockPrimeInd N) X Y T
          χ.conductor χ.primitiveCharacter
        - cutoffTwist (coprimeRestrict α d) (blockDrop N d) X Y T
            χ.conductor χ.primitiveCharacter := by
    unfold cutoffTwist
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have h' : coprimeRestrict (blockPrimeInd N) d n = blockPrimeInd N n - blockDrop N d n := by
      linear_combination coprimeRestrict_add_blockDrop N d n
    rw [h']; ring
  have hgen := cutoffTwist_coprimeRestrict_sub_efold d α (blockPrimeInd N) X Y T
    χ.conductor χ.primitiveCharacter
  linear_combination hfold + hβsplit + hgen

open Classical in
/-- The single-term β-crumb envelope: `X` when the (unique) block prime of `d` avoids the
conductor `f`, else `0`.  (A named def so that consuming statements carry no `Classical`
`if` — keeping their `Finset.erase`/`filter` instances aligned with the landed files.) -/
noncomputable def crumbBound (N d f X : ℕ) : ℝ :=
  if ∃ p : ℕ, p.Prime ∧ N < p ∧ p ∣ d ∧ ¬ p ∣ f then (X : ℝ) else 0

lemma crumbBound_nonneg (N d f X : ℕ) : 0 ≤ crumbBound N d f X := by
  unfold crumbBound
  split_ifs
  · exact Nat.cast_nonneg X
  · exact le_refl 0

open Classical in
/-- **`efold_beta_le_single` (deliverable 1) — the single-term β-crumb bound.**  The
replacement for the PE2-era `≡ 0` kill: under the √D floor `d < (N+1)²`, the β-crumb of the
honest e-fold identity is bounded by ONE term — `‖blockDrop‖ ≤ 1` at the unique block prime
`p ∣ d` times the trivial α-side sum `≤ X` — and it VANISHES outright unless `d` has a block
prime divisor `p` with `p ∤ f` (if `p ∣ f` then `ψ(m·p) = 0` for every `m`; if no block
prime divides `d` then `blockDrop N d ≡ 0` on the support).  (In the terminal chain the
β-side enters through `coprimeRestrict` at the fold — this is the shape that composes; the
bilinear `EfoldTermBeta` lives on the superseded PE branch, see the module header.) -/
theorem efold_beta_le_single {d N f : ℕ} [NeZero d] (hfd : f ∣ d)
    (hdsq : d < (N + 1) * (N + 1))
    (a : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ 1) (X Y T : ℕ) (ψ : DirichletCharacter ℂ f) :
    ‖cutoffTwist a (blockDrop N d) X Y T f ψ‖ ≤ crumbBound N d f X := by
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0] at hfd
    exact NeZero.ne d (Nat.eq_zero_of_zero_dvd hfd)
  haveI : NeZero f := ⟨hf0⟩
  unfold crumbBound
  by_cases hex : ∃ p : ℕ, p.Prime ∧ N < p ∧ p ∣ d ∧ ¬ p ∣ f
  · rw [if_pos hex]
    obtain ⟨p, hp, hNp, hpd, _hpf⟩ := hex
    have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    calc ‖cutoffTwist a (blockDrop N d) X Y T f ψ‖
        ≤ ∑ m ∈ Finset.Icc 1 X,
            ‖∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
              a m * blockDrop N d n * ψ ((m * n : ℕ) : ZMod f)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 X, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          refine le_trans (norm_sum_le _ _) ?_
          calc ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
                  ‖a m * blockDrop N d n * ψ ((m * n : ℕ) : ZMod f)‖
              ≤ ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
                  (if n = p then (1 : ℝ) else 0) := by
                refine Finset.sum_le_sum (fun n _ => ?_)
                by_cases hz : blockDrop N d n = 0
                · rw [hz, mul_zero, zero_mul, norm_zero]
                  split_ifs <;> norm_num
                · obtain ⟨hnp, hNn, hnd⟩ := blockDrop_ne_zero hz
                  have hnep : n = p := block_prime_dvd_unique hdsq hnp hp hNn hNp hnd hpd hdpos
                  rw [if_pos hnep]
                  have h1 : ‖a m‖ ≤ 1 := ha m
                  have h2 : ‖blockDrop N d n‖ ≤ 1 := norm_blockDrop_le_one N d n
                  have h3 : ‖ψ ((m * n : ℕ) : ZMod f)‖ ≤ 1 :=
                    DirichletCharacter.norm_le_one _ _
                  calc ‖a m * blockDrop N d n * ψ ((m * n : ℕ) : ZMod f)‖
                      = ‖a m‖ * ‖blockDrop N d n‖ * ‖ψ ((m * n : ℕ) : ZMod f)‖ := by
                        rw [norm_mul, norm_mul]
                    _ ≤ 1 * 1 * 1 := by
                        apply mul_le_mul _ h3 (norm_nonneg _) (by norm_num)
                        exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
                    _ = 1 := by norm_num
            _ = if p ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T) then (1 : ℝ) else 0 :=
                Finset.sum_ite_eq' _ p (fun _ => (1 : ℝ))
            _ ≤ 1 := by split_ifs <;> norm_num
      _ = ((Finset.Icc 1 X).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = (X : ℝ) := by rw [Nat.card_Icc]; norm_num
  · rw [if_neg hex]
    have hzero : cutoffTwist a (blockDrop N d) X Y T f ψ = 0 := by
      unfold cutoffTwist
      refine Finset.sum_eq_zero (fun m _ => Finset.sum_eq_zero (fun n _ => ?_))
      by_cases hz : blockDrop N d n = 0
      · rw [hz, mul_zero, zero_mul]
      · obtain ⟨hnp, hNn, hnd⟩ := blockDrop_ne_zero hz
        have hnf : n ∣ f := by
          by_contra hnf
          exact hex ⟨n, hnp, hNn, hnd, hnf⟩
        have hnu : ¬ IsUnit ((m * n : ℕ) : ZMod f) := by
          rw [ZMod.isUnit_iff_coprime]
          intro hc
          have h1 : Nat.Coprime n f := Nat.Coprime.coprime_dvd_left (dvd_mul_left n m) hc
          have h2 : n = 1 := h1.eq_one_of_dvd hnf
          have := hnp.two_le
          omega
        rw [MulChar.map_nonunit ψ hnu, mul_zero]
    rw [hzero, norm_zero]

open Classical in
/-- **The per-`(d,χ)` triangle (deliverable 1, assembled).**  `‖A_d − A⋆‖ ≤ ∑_{e∣d,e>1}
‖A^{(e)}‖ + [single β-crumb]` — the honest replacement for
`norm_cutoffTwist_sub_le_efold_blockPrimeInd`, valid for ALL `d < (N+1)²` (no `d < N`). -/
theorem norm_cutoffTwist_sub_le_efold_sqrtD {d N : ℕ} [NeZero d]
    (hdsq : d < (N + 1) * (N + 1))
    (α : ℕ → ℂ) (hα : ∀ m, ‖α m‖ ≤ 1) (X Y T : ℕ) (χ : DirichletCharacter ℂ d) :
    ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
        - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
      ≤ (∑ e ∈ efoldSet d,
          ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
              χ.conductor χ.primitiveCharacter‖)
        + crumbBound N d χ.conductor X := by
  rw [cutoffTwist_sub_efold_sqrtD]
  refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun e _ => ?_)
    rw [norm_mul, norm_mul]
    have hμ : ‖(ArithmeticFunction.moebius e : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      have := ArithmeticFunction.abs_moebius_le_one (n := e)
      exact_mod_cast this
    have hψ : ‖χ.primitiveCharacter ((e : ℕ) : ZMod χ.conductor)‖ ≤ 1 :=
      DirichletCharacter.norm_le_one _ _
    have hT : (0 : ℝ)
        ≤ ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
            χ.conductor χ.primitiveCharacter‖ := norm_nonneg _
    calc ‖(ArithmeticFunction.moebius e : ℂ)‖
            * ‖χ.primitiveCharacter ((e : ℕ) : ZMod χ.conductor)‖
            * ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
                χ.conductor χ.primitiveCharacter‖
        ≤ 1 * 1 * ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
            χ.conductor χ.primitiveCharacter‖ := by
          apply mul_le_mul _ (le_refl _) hT (by positivity)
          exact mul_le_mul hμ hψ (norm_nonneg _) (by norm_num)
      _ = ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
            χ.conductor χ.primitiveCharacter‖ := by ring
  · exact efold_beta_le_single χ.conductor_dvd_level hdsq (coprimeRestrict α d)
      (fun m => norm_coprimeRestrict_le α d hα (by norm_num) m) X Y T χ.primitiveCharacter

/-! ## 5. The character count — conductors avoiding the block prime (deliverable 2, engine)

Only characters whose conductor is NOT divisible by the block prime `p ∣ d` carry a
nonvanishing crumb; via the conductor-primitive injection (the `regroup_cutoff` pattern) and
`card (DirichletCharacter ℂ f) = φ(f)` (mathlib), there are at most
`∑_{f ∣ d/p} φ(f) = d/p` of them. -/

open Classical in
/-- **The character count.**  For a prime `p ∣ d`, at most `d/p` characters mod `d` have a
conductor not divisible by `p`: such a conductor divides `d/p` (coprimality with `p`), the
map `χ ↦ (cond χ, χ⋆)` is injective, and level `f` carries `φ(f)` characters
(`card_eq_totient_of_hasEnoughRootsOfUnity`); `∑_{f ∣ d/p} φ(f) = d/p`. -/
theorem card_conductor_not_dvd_le {d p : ℕ} [NeZero d] (hp : p.Prime) (hpd : p ∣ d) :
    (((Finset.univ : Finset (DirichletCharacter ℂ d))).filter
        (fun χ => ¬ p ∣ χ.conductor)).card ≤ d / p := by
  set i : DirichletCharacter ℂ d → Σ f : ℕ, DirichletCharacter ℂ f :=
    fun χ => ⟨χ.conductor, χ.primitiveCharacter⟩ with hi
  set r : (Σ f : ℕ, DirichletCharacter ℂ f) → DirichletCharacter ℂ d :=
    fun pr => if h : pr.1 ∣ d then DirichletCharacter.changeLevel h pr.2 else 1 with hr
  have hri : ∀ χ : DirichletCharacter ℂ d, r (i χ) = χ := by
    intro χ
    simp only [hr, hi]
    rw [dif_pos χ.conductor_dvd_level]
    exact DirichletCharacter.changeLevel_primitiveCharacter (χ := χ)
  set S := ((Finset.univ : Finset (DirichletCharacter ℂ d))).filter
    (fun χ => ¬ p ∣ χ.conductor) with hS
  set T' := ((d / p).divisors).sigma
    (fun f => (Finset.univ : Finset (DirichletCharacter ℂ f))) with hT
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdp_pos : 0 < d / p := Nat.div_pos (Nat.le_of_dvd hdpos hpd) hp.pos
  have hmaps : ∀ χ ∈ S, i χ ∈ T' := by
    intro χ hχ
    rw [hS, Finset.mem_filter] at hχ
    obtain ⟨_, hnp⟩ := hχ
    have hcd : χ.conductor ∣ d := χ.conductor_dvd_level
    have hcop : Nat.Coprime χ.conductor p :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnp)
    have hcdp : χ.conductor ∣ d / p := by
      refine hcop.dvd_of_dvd_mul_left ?_
      rwa [Nat.mul_div_cancel' hpd]
    rw [hT, Finset.mem_sigma]
    exact ⟨Nat.mem_divisors.mpr ⟨hcdp, by omega⟩, Finset.mem_univ _⟩
  have hinj : Set.InjOn i (S : Set (DirichletCharacter ℂ d)) := by
    intro a _ b _ hab
    have h := congrArg r hab
    rwa [hri a, hri b] at h
  calc S.card ≤ T'.card := Finset.card_le_card_of_injOn i hmaps hinj
    _ = ∑ f ∈ (d / p).divisors,
          (Finset.univ : Finset (DirichletCharacter ℂ f)).card := Finset.card_sigma _ _
    _ = ∑ f ∈ (d / p).divisors, f.totient := by
        refine Finset.sum_congr rfl (fun f hf => ?_)
        have hf0 : f ≠ 0 := by
          rcases Nat.mem_divisors.mp hf with ⟨hfd, hne⟩
          intro h0; rw [h0] at hfd
          exact hne (Nat.eq_zero_of_zero_dvd hfd)
        haveI : NeZero f := ⟨hf0⟩
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    _ = d / p := sum_totient_divisors _

open Classical in
/-- **The per-`d` crumb χ-sum.**  Summed over the characters mod `d`, the single-term crumb
indicator is at most `(D/(N+1))·X`: the block prime of `d` is unique (`hdsq`), the crumb
survives only on the `≤ d/p ≤ D/(N+1)` characters whose conductor avoids it. -/
lemma crumb_chi_sum_le {d N D X : ℕ} (hd1 : 1 ≤ d) (hdsq : d < (N + 1) * (N + 1))
    (hdD : d ≤ D) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        crumbBound N d χ.conductor X
      ≤ ((D : ℝ) / ((N : ℝ) + 1)) * (X : ℝ) := by
  have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  by_cases hbp : ∃ p : ℕ, p.Prime ∧ N < p ∧ p ∣ d
  · obtain ⟨p₀, hp₀, hNp₀, hp₀d⟩ := hbp
    have hdpos : 0 < d := by omega
    have hpt : ∀ χ : DirichletCharacter ℂ d,
        crumbBound N d χ.conductor X
          ≤ (if ¬ p₀ ∣ χ.conductor then (X : ℝ) else 0) := by
      intro χ
      unfold crumbBound
      by_cases hex : ∃ p : ℕ, p.Prime ∧ N < p ∧ p ∣ d ∧ ¬ p ∣ χ.conductor
      · obtain ⟨p, hp, hNp, hpd, hpf⟩ := hex
        have hpp₀ : p = p₀ := block_prime_dvd_unique hdsq hp hp₀ hNp hNp₀ hpd hp₀d hdpos
        rw [if_pos ⟨p, hp, hNp, hpd, hpf⟩, if_pos (hpp₀ ▸ hpf)]
      · rw [if_neg hex]
        by_cases h : ¬ p₀ ∣ χ.conductor
        · rw [if_pos h]; exact hXnn
        · rw [if_neg h]
    calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            crumbBound N d χ.conductor X
        ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            (if ¬ p₀ ∣ χ.conductor then (X : ℝ) else 0) :=
          Finset.sum_le_sum (fun χ _ => hpt χ)
      _ ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)),
            (if ¬ p₀ ∣ χ.conductor then (X : ℝ) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun χ _ _ => ?_)
          by_cases h : ¬ p₀ ∣ χ.conductor
          · rw [if_pos h]; exact hXnn
          · rw [if_neg h]
      _ = ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ d))).filter
            (fun χ => ¬ p₀ ∣ χ.conductor), (X : ℝ) := (Finset.sum_filter _ _).symm
      _ = ((((Finset.univ : Finset (DirichletCharacter ℂ d))).filter
            (fun χ => ¬ p₀ ∣ χ.conductor)).card : ℝ) * (X : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((d / p₀ : ℕ) : ℝ) * (X : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hXnn
          haveI : NeZero d := ⟨by omega⟩
          exact_mod_cast card_conductor_not_dvd_le hp₀ hp₀d
      _ ≤ ((d : ℝ) / (p₀ : ℝ)) * (X : ℝ) :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le hXnn
      _ ≤ ((D : ℝ) / ((N : ℝ) + 1)) * (X : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hXnn
          have h1 : (d : ℝ) ≤ (D : ℝ) := Nat.cast_le.mpr hdD
          have h2 : ((N : ℝ) + 1) ≤ (p₀ : ℝ) := by
            have : N + 1 ≤ p₀ := hNp₀
            exact_mod_cast this
          have hp₀pos : (0 : ℝ) < (p₀ : ℝ) := by exact_mod_cast hp₀.pos
          rw [div_le_div_iff₀ hp₀pos (by positivity)]
          exact mul_le_mul h1 h2 (by positivity) (Nat.cast_nonneg D)
  · have hz : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        crumbBound N d χ.conductor X = 0 := by
      intro χ _
      unfold crumbBound
      rw [if_neg]
      rintro ⟨p, hp, hNp, hpd, _⟩
      exact hbp ⟨p, hp, hNp, hpd⟩
    rw [Finset.sum_eq_zero hz]
    positivity

/-! ## 6. The reorganized `hErrSum` with the β-crumb (deliverable 2, assembly) -/

open Classical in
/-- **The √D `hErrSum` reorganization.**  Mirror of `cutoffEfoldTerm_reorg` with `D < N`
replaced by `D < (N+1)²`: the α-side e-fold reorganizes exactly as landed, and the β-crumb
totals at most `4(1+log D)·(D/(N+1))·X` (`crumb_chi_sum_le` per `d`, then
`Salt.LS.sum_inv_totient_le`). -/
theorem cutoffEfoldTerm_reorg_sqrtD (α : ℕ → ℂ) (N X Y T D D0 : ℕ) (Dset : Finset ℕ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hD1 : 1 ≤ D)
    (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (hDsq : D < (N + 1) * (N + 1)) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
              - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
      ≤ (∑ e ∈ Finset.Icc 2 D, cutoffEfoldTerm α N X Y T D0 Dset e)
        + 4 * (1 + Real.log D) * ((D : ℝ) / ((N : ℝ) + 1)) * (X : ℝ) := by
  set Dset' := Dset.filter (fun d => ¬ d ≤ D0) with hDset'def
  set f : ℕ → ℕ → ℝ := fun d e =>
    (1 / (d.totient : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
            χ.conductor χ.primitiveCharacter‖
    with hfdef
  -- Step A: per-`d` split into the e-fold part + the β-crumb.
  have hstepA : ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
          ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
            - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
      ≤ ∑ d ∈ Dset', ((∑ e ∈ efoldSet d, f d e)
          + (1 / (d.totient : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
                crumbBound N d χ.conductor X) := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    rw [hDset'def, Finset.mem_filter] at hd
    have hd1 : 1 ≤ d := hDset1 d hd.1
    have hdD : d ≤ D := hDsetD d hd.1
    have hdsq_d : d < (N + 1) * (N + 1) := lt_of_le_of_lt hdD hDsq
    have step1 : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
            - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
          ≤ (∑ e ∈ efoldSet d,
              ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
                  χ.conductor χ.primitiveCharacter‖)
            + crumbBound N d χ.conductor X := by
      intro χ _
      haveI : NeZero d := ⟨by omega⟩
      exact norm_cutoffTwist_sub_le_efold_sqrtD hdsq_d α hα X Y T χ
    calc (1 / (d.totient : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
              ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
                - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
        ≤ (1 / (d.totient : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
              ((∑ e ∈ efoldSet d,
                  ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
                      χ.conductor χ.primitiveCharacter‖)
                + crumbBound N d χ.conductor X) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum step1) (by positivity)
      _ = (1 / (d.totient : ℝ)) *
            (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
              ∑ e ∈ efoldSet d,
                ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
                    χ.conductor χ.primitiveCharacter‖)
          + (1 / (d.totient : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
                crumbBound N d χ.conductor X := by
          rw [Finset.sum_add_distrib, mul_add]
      _ = (∑ e ∈ efoldSet d, f d e)
          + (1 / (d.totient : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
                crumbBound N d χ.conductor X := by
          rw [mul_double_sum_comm]
  refine le_trans hstepA ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  -- the e-fold half: the landed `(d,e)` swap, verbatim.
  · refine le_of_eq ?_
    calc ∑ d ∈ Dset', ∑ e ∈ efoldSet d, f d e
        = ∑ e ∈ Finset.Icc 2 D, ∑ d ∈ Dset'.filter (fun d => e ∣ d), f d e := by
          refine Finset.sum_comm' ?_
          intro d e
          constructor
          · rintro ⟨hd, he⟩
            have hdmem : d ∈ Dset := by rw [hDset'def, Finset.mem_filter] at hd; exact hd.1
            have hd1 : 1 ≤ d := hDset1 d hdmem
            have hdD : d ≤ D := hDsetD d hdmem
            simp only [efoldSet, Finset.mem_filter, Nat.mem_divisors] at he
            have hed : e ≤ d := Nat.le_of_dvd (by omega) he.1.1
            refine ⟨?_, ?_⟩
            · rw [Finset.mem_filter]; exact ⟨hd, he.1.1⟩
            · rw [Finset.mem_Icc]; omega
          · rintro ⟨hd, he⟩
            rw [Finset.mem_filter] at hd
            rw [Finset.mem_Icc] at he
            have hdmem : d ∈ Dset := by rw [hDset'def, Finset.mem_filter] at hd; exact hd.1.1
            have hd1 : 1 ≤ d := hDset1 d hdmem
            refine ⟨hd.1, ?_⟩
            simp only [efoldSet, Finset.mem_filter, Nat.mem_divisors]
            exact ⟨⟨hd.2, by omega⟩, by omega⟩
      _ = ∑ e ∈ Finset.Icc 2 D, cutoffEfoldTerm α N X Y T D0 Dset e := by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          simp only [cutoffEfoldTerm, hfdef, hDset'def]
  -- the β-crumb half: `crumb_chi_sum_le` per `d`, then the `∑ 1/φ` absorption.
  · calc ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
              crumbBound N d χ.conductor X
        ≤ ∑ d ∈ Dset', (1 / (d.totient : ℝ)) * (((D : ℝ) / ((N : ℝ) + 1)) * (X : ℝ)) := by
          refine Finset.sum_le_sum (fun d hd => ?_)
          rw [hDset'def, Finset.mem_filter] at hd
          have hd1 : 1 ≤ d := hDset1 d hd.1
          have hdD : d ≤ D := hDsetD d hd.1
          exact mul_le_mul_of_nonneg_left
            (crumb_chi_sum_le hd1 (lt_of_le_of_lt hdD hDsq) hdD) (by positivity)
      _ = (((D : ℝ) / ((N : ℝ) + 1)) * (X : ℝ)) * ∑ d ∈ Dset', (1 / (d.totient : ℝ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun d _ => by ring)
      _ ≤ (((D : ℝ) / ((N : ℝ) + 1)) * (X : ℝ)) * (4 * (1 + Real.log D)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ∑ d ∈ Dset', (1 / (d.totient : ℝ))
              ≤ ∑ d ∈ Finset.Icc 1 D, (1 / (d.totient : ℝ)) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => by positivity)
                intro d hd
                rw [hDset'def, Finset.mem_filter] at hd
                rw [Finset.mem_Icc]
                exact ⟨hDset1 d hd.1, hDsetD d hd.1⟩
            _ ≤ 4 * (1 + Real.log D) := Salt.LS.sum_inv_totient_le D hD1
      _ = 4 * (1 + Real.log D) * ((D : ℝ) / ((N : ℝ) + 1)) * (X : ℝ) := by ring

open Classical in
/-- **The √D `hErrSum` discharge.**  Mirror of `hErrSum_cutoff_discharge` with `D < N`
replaced by `hDsq` + the (raw-form) absorption `habs`; the crumb costs exactly `+ 1` in the
`Kerr` constant. -/
theorem hErrSum_cutoff_discharge_sqrtD (α : ℕ → ℂ) (N X Y T D D0 : ℕ) (Dset : Finset ℕ)
    {A Kerr : ℝ} (G : ℕ → ℝ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hD1 : 1 ≤ D)
    (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (hDsq : D < (N + 1) * (N + 1))
    (habs : 4 * (1 + Real.log D) * ((D : ℝ) / ((N : ℝ) + 1)) * (X : ℝ)
        ≤ ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A)
    (hGlue : ∀ e, 2 ≤ e → e ≤ D → cutoffEfoldTerm α N X Y T D0 Dset e ≤ G e)
    (hGsum : ∑ e ∈ Finset.Icc 2 D, G e
        ≤ Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
              - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
      ≤ (Kerr + 1) * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
  refine le_trans
    (cutoffEfoldTerm_reorg_sqrtD α N X Y T D D0 Dset hα hD1 hDset1 hDsetD hDsq) ?_
  have h1 : ∑ e ∈ Finset.Icc 2 D, cutoffEfoldTerm α N X Y T D0 Dset e
      ≤ ∑ e ∈ Finset.Icc 2 D, G e := by
    refine Finset.sum_le_sum (fun e he => ?_)
    rw [Finset.mem_Icc] at he
    exact hGlue e he.1 he.2
  calc (∑ e ∈ Finset.Icc 2 D, cutoffEfoldTerm α N X Y T D0 Dset e)
        + 4 * (1 + Real.log D) * ((D : ℝ) / ((N : ℝ) + 1)) * (X : ℝ)
      ≤ Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A
        + ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A :=
        add_le_add (le_trans h1 hGsum) habs
    _ = (Kerr + 1) * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by ring

/-! ## 7. `general_BV_cutoff_closed_sqrtD` — the fed windowed BV at the √D floor -/

open Classical in
/-- **The √D `general_BV_cutoff_closed`.**  Byte-for-byte the landed
`general_BV_cutoff_closed` with the single swap `D < N` → (`hDsq : D < (N+1)²` +
`habs : 4(1+log D)·D ≤ N·M/L^A`), the β-crumb folded as `Kerr + 1`.  The `hMainEnergy` leg
is UNCHANGED (STEP 0: it never used `D < N`). -/
theorem general_BV_cutoff_closed_sqrtD {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M T D0 D k0 Klog : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ) (Kβ Km Kerr B : ℝ)
        (G : ℕ → ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → 0 ≤ Km → N₀ ≤ N → M ≤ 2 * N → D0 ≤ N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (0 < Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        ((N : ℝ) ≤ (M : ℝ)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + C0) ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < (N + 1) * (N + 1) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ (N : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) →
        2 ≤ X → 2 ≤ M → A + 2 ≤ B → A + 2 ≤ C0 →
        D0 = 2 ^ k0 → 2 ≤ D0 → D0 ≤ D → Klog = Nat.log 2 D →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ B) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 2) ≤ 2 * (2 : ℝ) ^ k0) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt X) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt M) →
        (∑ f ∈ Finset.Icc 2 D0, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α (blockPrimeInd N) X M T f
            ≤ Km * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1)) →
        (∀ e, 2 ≤ e → e ≤ D → cutoffEfoldTerm α N X M T D0 Dset e ≤ G e) →
        (∑ e ∈ Finset.Icc 2 D, G e
            ≤ Kerr * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) →
        ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
          ≤ (Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26) + (Kerr + 1))) * ((X : ℝ) * (M : ℝ))
              / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K, N₀, hK0, hbody⟩ := general_BV_cutoff_final (A := A) (C0 := C0) hA hC0
  refine ⟨K, N₀, hK0, fun α X N M T D0 D k0 Klog Dset r Kβ Km Kerr B G hα hKβ hKm hN hM2N hD0N
    hDge1 hcop2 hLpos hD0 hD0N' hNM hscale hD1 hDsetD hDsq habs hX2 hM2 hBge hCge hD0eq h2D0
    hD0D hKeq hDscale hD0lo hXsqrt hMsqrt hSmallCut hGlue hGsum => ?_⟩
  have hβ1 : ∀ n, ‖blockPrimeInd N n‖ ≤ 1 := by
    intro n; unfold blockPrimeInd
    by_cases h : N < n ∧ n.Prime
    · rw [if_pos h, norm_one]
    · rw [if_neg h, norm_zero]; norm_num
  -- discharge `hMainEnergy` (UNCHANGED — no `D < N` on this leg).
  have hMainEnergy : 4 * (1 + Real.log D) *
        ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α (blockPrimeInd N) X M T f
      ≤ (6 * (Km + 448 + 32 * Real.sqrt 26)) * ((X : ℝ) * (M : ℝ))
          / (Real.log ((X : ℝ) * (M : ℝ))) ^ A :=
    hMainEnergy_cutoff_discharge hA.le hX2 hM2 hD1 hBge hCge hD0eq h2D0 hD0D hKeq hDscale hD0lo
      hXsqrt hMsqrt hKm α (blockPrimeInd N) hα hβ1 hSmallCut
  -- convert the named `N·M/L^A` absorption row into the raw crumb form.
  have habs_raw : 4 * (1 + Real.log D) * ((D : ℝ) / ((N : ℝ) + 1)) * (X : ℝ)
      ≤ ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
    have hLA : (0 : ℝ) < (Real.log ((X : ℝ) * (M : ℝ))) ^ A := Real.rpow_pos_of_pos hLpos A
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    calc 4 * (1 + Real.log D) * ((D : ℝ) / ((N : ℝ) + 1)) * (X : ℝ)
        = (4 * (1 + Real.log D) * (D : ℝ)) * ((X : ℝ) / ((N : ℝ) + 1)) := by ring
      _ ≤ ((N : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A)
            * ((X : ℝ) / ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right habs (by positivity)
      _ = (((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A)
            * ((N : ℝ) / ((N : ℝ) + 1)) := by ring
      _ ≤ (((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one hN1]
          linarith
      _ = ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := mul_one _
  -- discharge `hErrSum` with the β-crumb (`Kerr + 1`).
  have hErrSum : ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist α (blockPrimeInd N) X M T d χ
              - cutoffTwist α (blockPrimeInd N) X M T χ.conductor χ.primitiveCharacter‖
      ≤ (Kerr + 1) * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A :=
    hErrSum_cutoff_discharge_sqrtD α N X M T D D0 Dset G hα hD1 hDge1 hDsetD hDsq habs_raw
      hGlue hGsum
  exact hbody α X N M T D0 D Dset r Kβ (6 * (Km + 448 + 32 * Real.sqrt 26)) (Kerr + 1) hα hKβ hN
    hM2N hD0N hDge1 hcop2 hLpos hD0 hD0N' hNM hscale hD1 hDsetD hMainEnergy hErrSum

/-! ## 8. `general_BV_cutoff_sqrtD` — the terminal variant (deliverable 2) -/

open Classical in
/-- **`general_BV_cutoff_sqrtD` (deliverable 2) — the terminal windowed BV at the √D
floor.**  Byte-for-byte `general_BV_cutoff_unconditional` with the single swap
`D < N` → (`hDsq : D < (N+1)²` + the ONE new named absorption row
`habs : 4(1+log D)·D ≤ N·M/L^A`); conclusion IDENTICAL in shape, with
`Kerr = 2^{A+5}·Kβ' + 15360 + 1` (the `+ 1` is the absorbed β-crumb).  This is the variant
GBV4's feeders re-thread through — it covers the catch-#62 strip (high boxes at
`√(x/(4z)) < N ≤ D` and ALL live band boxes), where `D < N` fails but `D < (N+1)²` holds
with `x^{1/6}`-scale room.  The three dilated per-`e` rows (`herr_LEpos`/`herr_D0E`/`herr_scale`)
are GUARDED to the live range `e ≤ X` (catch #69, node PRICE-0): for `e > X` we have
`⌊X/e⌋ = 0`, so `log(⌊X/e⌋·M) = log 0 = 0` and the ungarded rows were FALSE (`0 < 0`); the
glue splits the `e`-sum at `X` and lands `cutoffEfoldTerm_eq_zero_of_gt` (the term vanishes)
on the `e > X` leg. -/
theorem general_BV_cutoff_sqrtD {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M T D0 D k0 Klog : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ) (Kβ Km Kβ' B : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → 0 ≤ Km → 0 ≤ Kβ' → N₀ ≤ N → M ≤ 2 * N → D0 ≤ N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (1 ≤ Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        ((N : ℝ) ≤ (M : ℝ)) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < (N + 1) * (N + 1) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ (N : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) →
        2 ≤ X → 2 ≤ M → A + 2 ≤ B → A + 2 ≤ C0 →
        D0 = 2 ^ k0 → 2 ≤ D0 → D0 ≤ D → Klog = Nat.log 2 D →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ B) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 2) ≤ 2 * (2 : ℝ) ^ k0) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt X) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt M) →
        -- error-side (`e`-fold) thresholds
        ((D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt ((X : ℝ) * (M : ℝ))) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 4) ≤ (D0 : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D →
            (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (X : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X → 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ C0) →
        ((D : ℝ) ≤ (X : ℝ) * (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        -- SW couplings (in the exposed `K`)
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + C0) ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1 + 2 * C0) ≤ Km * (Real.log N) ^ (A + 2 * C0)) →
        (∀ e, 2 ≤ e → e ≤ D →
            K * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (A + 1 + 1 + 2 * C0)
              ≤ Kβ' * (Real.log N) ^ (A + 1 + 2 * C0)) →
        ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
          ≤ (Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26)
                + ((2 : ℝ) ^ (A + 5) * Kβ' + 15360 + 1))) * ((X : ℝ) * (M : ℝ))
              / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K₃, N₀₃, hK3pos, hbody3⟩ := hSmallCut_discharge (A := A) (C0 := C0) hA hC0
  obtain ⟨K₄, N₀₄, hK4pos, hbody4⟩ := hsmall_pere_discharge (A := A) (C0 := C0) hA hC0
  obtain ⟨Kg, N₀g, hKgpos, hbodyg⟩ := general_BV_cutoff_closed_sqrtD (A := A) (C0 := C0) hA hC0
  refine ⟨K₃ + K₄ + Kg, max (max N₀₃ N₀₄) N₀g, by positivity,
    fun α X N M T D0 D k0 Klog Dset r Kβ Km Kβ' B hα hKβ hKm hKβ' hN hM2N hD0N hDge1 hcop2 hL1
      hD0 hD0N' hNM hD1 hDsetD hDsq habs hX2 hM2 hBge hCge hD0eq h2D0 hD0D hKlog hDscale
      hD0lo_main hXsqrt hMsqrt herr_lev herr_D0lo herr_Mlev herr_div herr_LEpos herr_D0E hDXM
      herr_scale hcoupG hcoup3 herr_book4 => ?_⟩
  set K := K₃ + K₄ + Kg with hKdef
  have hK3leK : K₃ ≤ K := by rw [hKdef]; linarith [hK4pos, hKgpos]
  have hK4leK : K₄ ≤ K := by rw [hKdef]; linarith [hK3pos, hKgpos]
  have hKgleK : Kg ≤ K := by rw [hKdef]; linarith [hK3pos, hK4pos]
  have hN₃ : N₀₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₄ : N₀₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNg : N₀g ≤ N := le_trans (le_max_right _ _) hN
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  have hLpos : (0 : ℝ) < L := by linarith
  have hXpos : 0 < X := by omega
  have hMpos : 0 < M := by omega
  have hLnn : (0 : ℝ) ≤ L := hLpos.le
  -- the item-4 output constant and the assembled envelope constant.
  set Ksm : ℝ := (2 : ℝ) ^ (A + 5) * Kβ' with hKsmdef
  set G : ℕ → ℝ := fun e => (Ksm + 15360) * ((X : ℝ) * (M : ℝ) / L ^ (A + 1)) * (1 / (e : ℝ))
    with hGdef
  -- `hSmallCut` via item 3 (landed, unchanged).
  have hSmallCut : ∑ f ∈ Finset.Icc 2 D0,
        (1 / (f.totient : ℝ)) * cutoffPrimEnergy α (blockPrimeInd N) X M T f
      ≤ Km * ((X : ℝ) * (M : ℝ)) / L ^ (A + 1) :=
    hbody3 α X N M T D0 Km hα hKm hN₃ hM2N hLpos hD0 hD0N' hNM
      (le_trans (mul_le_mul_of_nonneg_right hK3leK (Real.rpow_nonneg hLnn _)) hcoup3)
  -- the per-`e` envelope via item 4 + `cutoffEfold_alpha_le` (landed, unchanged).
  have hGlue : ∀ e, 2 ≤ e → e ≤ D → cutoffEfoldTerm α N X M T D0 Dset e ≤ G e := by
    intro e he2 heD
    by_cases hleX : e ≤ X
    · -- `e ≤ X` (the live range): the guarded per-`e` rows apply verbatim.
      have hLE0 : (0 : ℝ) ≤ Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)) :=
        (herr_LEpos e he2 heD hleX).le
      have hbook4e : K₄ * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (A + 1 + 1 + 2 * C0)
          ≤ Kβ' * (Real.log N) ^ (A + 1 + 2 * C0) :=
        le_trans (mul_le_mul_of_nonneg_right hK4leK (Real.rpow_nonneg hLE0 _))
          (herr_book4 e he2 heD)
      have hsmall := hbody4 α N X M T D0 D e Kβ' hα hKβ' hN₄ hM2N (by omega) hD1
        (herr_LEpos e he2 heD hleX) (herr_D0E e he2 heD hleX) hD0N' hNM hL1 hDXM
        (herr_scale e he2 heD hleX) hbook4e
      exact cutoffEfold_alpha_le α N X M T D0 D e k0 Klog Dset (A := A) (Ksmall := Ksm)
        hα he2 heD hD1 hDge1 hDsetD h2D0 hD0D hD0eq hKlog hMpos hXpos hA.le hL1 herr_lev herr_D0lo
        herr_Mlev (herr_div e he2 heD) hsmall
    · -- `e > X` (past the top): the `e`-fold term vanishes (`⌊X/e⌋ = 0`), and `G e ≥ 0`.
      have hgtX : X < e := by omega
      rw [cutoffEfoldTerm_eq_zero_of_gt α N X M T D0 Dset hgtX, hGdef]
      have hLA : (0 : ℝ) < L ^ (A + 1) := Real.rpow_pos_of_pos hLpos _
      have hKsmnn : (0 : ℝ) ≤ Ksm := by rw [hKsmdef]; positivity
      have hmid : (0 : ℝ) ≤ (X : ℝ) * (M : ℝ) / L ^ (A + 1) := div_nonneg (by positivity) hLA.le
      exact mul_nonneg (mul_nonneg (by linarith) hmid) (by positivity)
  -- the harmonic sum `∑ G e ≤ Kerr·XM/L^A`.
  have hC0nn : (0 : ℝ) ≤ (Ksm + 15360) * ((X : ℝ) * (M : ℝ) / L ^ (A + 1)) := by
    have : (0 : ℝ) ≤ Ksm := by rw [hKsmdef]; positivity
    have hLA : (0 : ℝ) < L ^ (A + 1) := Real.rpow_pos_of_pos hLpos _
    positivity
  have hlogDL : Real.log D ≤ L :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < D)) hDXM
  have hGsum : ∑ e ∈ Finset.Icc 2 D, G e
      ≤ ((2 : ℝ) ^ (A + 5) * Kβ' + 15360) * ((X : ℝ) * (M : ℝ)) / L ^ A := by
    calc ∑ e ∈ Finset.Icc 2 D, G e
        = ((Ksm + 15360) * ((X : ℝ) * (M : ℝ) / L ^ (A + 1)))
            * ∑ e ∈ Finset.Icc 2 D, (1 / (e : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ ((Ksm + 15360) * ((X : ℝ) * (M : ℝ) / L ^ (A + 1))) * Real.log D :=
          mul_le_mul_of_nonneg_left (sum_inv_Icc_le_log hD1) hC0nn
      _ ≤ ((Ksm + 15360) * ((X : ℝ) * (M : ℝ) / L ^ (A + 1))) * L :=
          mul_le_mul_of_nonneg_left hlogDL hC0nn
      _ = ((2 : ℝ) ^ (A + 5) * Kβ' + 15360) * ((X : ℝ) * (M : ℝ)) / L ^ A := by
          rw [hKsmdef, Real.rpow_add hLpos A 1, Real.rpow_one]
          field_simp
  -- assemble via `general_BV_cutoff_closed_sqrtD` (the β-crumb costs the `+ 1`).
  exact hbodyg α X N M T D0 D k0 Klog Dset r Kβ Km ((2 : ℝ) ^ (A + 5) * Kβ' + 15360) B G
    hα hKβ hKm hNg hM2N hD0N hDge1 hcop2 hLpos hD0 hD0N' hNM
    (le_trans (mul_le_mul_of_nonneg_right hKgleK (Real.rpow_nonneg hLnn _)) hcoupG)
    hD1 hDsetD hDsq habs hX2 hM2 hBge hCge hD0eq h2D0 hD0D hKlog hDscale hD0lo_main hXsqrt
    hMsqrt hSmallCut hGlue hGsum

/-! ## 9. `medium_survivor_price_sqrtD` — the re-threaded per-survivor supplier
(deliverable 3)

STEP 0 finding: `medium_survivor_price` is the ONLY GBV4 feeder that carries `D < N` (it
passes it verbatim to the terminal); `hHD_of_box_disc`, `Plo_sym_of_box_disc`,
`Plo_low_of_box_disc` and `hNum_at_op` are price-abstract and `D < N`-FREE.  So the
re-thread is: this variant + the `_sqrtD` re-exports below. -/

open Classical in
/-- **`medium_survivor_price_sqrtD` (deliverable 3).**  `medium_survivor_price` with
`D < N` replaced by `hDsq : D < (N+1)²` + `habs : 4(1+log D)·D ≤ N·M/L^A`
(the two GLU-2 rows of the module header); `herr_div` discharged by the landed
`hdiv_direct` exactly as in GBV4.  The conclusion is the same per-side price shape (the
`hprice` slot of `box_disc_three_way`), with the β-crumb's `+ 1` in the constant.  This
prices the catch-#62 strip: the medium/high boxes and ALL live band boxes at `N ≤ D`.
The three dilated per-`e` rows (`herr_LEpos`/`herr_D0E`/`herr_scale`) carry the `e ≤ X` guard
of catch #69 (node PRICE-0), passed straight through to `general_BV_cutoff_sqrtD`. -/
theorem medium_survivor_price_sqrtD {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (x Lb : ℝ) (F : ℕ) (α : ℕ → ℂ) (X N M T D0 D k0 Klog : ℕ) (Dset : Finset ℕ)
        (r : ℕ → ℕ) (Kβ Km Kβ' B : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → 0 ≤ Km → 0 ≤ Kβ' → N₀ ≤ N → M ≤ 2 * N → D0 ≤ N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (1 ≤ Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        ((N : ℝ) ≤ (M : ℝ)) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < (N + 1) * (N + 1) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ (N : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) →
        2 ≤ X → 2 ≤ M → A + 2 ≤ B → A + 2 ≤ C0 →
        D0 = 2 ^ k0 → 2 ≤ D0 → D0 ≤ D → Klog = Nat.log 2 D →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ B) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 2) ≤ 2 * (2 : ℝ) ^ k0) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt X) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt M) →
        ((D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt ((X : ℝ) * (M : ℝ))) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 4) ≤ (D0 : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (M : ℝ)) →
        -- the m-scale floor discharge of `herr_div` (GBV4's `hdiv_direct` route, unchanged)
        F ≤ X →
        ((D : ℝ) ≤ Real.sqrt x) →
        (Real.log ((X : ℝ) * (M : ℝ)) ≤ Lb) →
        (((3 : ℝ) / Real.log 2) ^ 8 * x ^ ((1 : ℝ) / 6) * Lb ^ (A + 5)
            ≤ Real.sqrt (F : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X → 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ C0) →
        ((D : ℝ) ≤ (X : ℝ) * (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + C0) ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1 + 2 * C0)
            ≤ Km * (Real.log N) ^ (A + 2 * C0)) →
        (∀ e, 2 ≤ e → e ≤ D →
            K * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (A + 1 + 1 + 2 * C0)
              ≤ Kβ' * (Real.log N) ^ (A + 1 + 2 * C0)) →
        ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
          ≤ (Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26)
                + ((2 : ℝ) ^ (A + 5) * Kβ' + 15360 + 1))) * ((X : ℝ) * (M : ℝ))
              / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K, N₀, hK0, hbody⟩ := general_BV_cutoff_sqrtD hA hC0
  refine ⟨K, N₀, hK0, fun x Lb F α X N M T D0 D k0 Klog Dset r Kβ Km Kβ' B hα hKβ hKm hKβ' hN
    hM2N hD0N hDge1 hcop2 hL1 hD0 hD0N' hNM hD1 hDsetD hDsq habs hX2 hM2 hBge hCge hD0eq h2D0
    hD0D hKlog hDscale hD0lo_main hXsqrt hMsqrt herr_lev herr_D0lo herr_Mlev hFX hDx hLbb
    hfloor herr_LEpos herr_D0E hDXM herr_scale hcoupG hcoup3 herr_book4 => ?_⟩
  have herr_div : ∀ e, 2 ≤ e → e ≤ D →
      (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5)
        ≤ Real.sqrt (X : ℝ) :=
    fun e he2 heD =>
      hdiv_direct hA.le x Lb F X M D hFX (by omega) (by omega) hDx hLbb hfloor e (by omega) heD
  exact hbody α X N M T D0 D k0 Klog Dset r Kβ Km Kβ' B hα hKβ hKm hKβ' hN hM2N hD0N hDge1 hcop2
    hL1 hD0 hD0N' hNM hD1 hDsetD hDsq habs hX2 hM2 hBge hCge hD0eq h2D0 hD0D hKlog hDscale
    hD0lo_main hXsqrt hMsqrt herr_lev herr_D0lo herr_Mlev herr_div herr_LEpos herr_D0E hDXM
    herr_scale hcoupG hcoup3 herr_book4

/-! ## 10. The carrier discharges of `hDsq` and the feeder re-exports (deliverable 3) -/

/-- **The carrier discharge of `hDsq`.**  The `hDsq` row is monotone in the block floor:
any carrier whose theorem-`N` sits above `y` inherits it from the single GLU-2 numeric row
`D < (y+1)²` (operating point: `y = x^{1/3}`, `D ~ √x·L^{-B}` — `x^{1/6}` of room). -/
theorem hDsq_of_carrier_floor {D y N : ℕ} (hyN : y ≤ N) (hDy : D < (y + 1) * (y + 1)) :
    D < (N + 1) * (N + 1) :=
  lt_of_lt_of_le hDy (Nat.mul_le_mul (by omega) (by omega))

/-- **`hDsq` at the sym-band carrier.**  The sym boxes run at `N_thm = max y (pieceN k) ≥ y`
(`BandIdent.blockAlphaSym` forces `p₂ > max y N`), so `hDsq` there follows from the single
`D < (y+1)²` row. -/
theorem hDsq_at_sym_carrier {D y N : ℕ} (hDy : D < (y + 1) * (y + 1)) :
    D < (max y N + 1) * (max y N + 1) :=
  hDsq_of_carrier_floor (le_max_left y N) hDy

/-- **`hHD_of_box_disc_sqrtD`** — re-export.  STEP 0: the landed `hHD_of_box_disc` is
price-abstract and never carried `D < N`; the `_sqrtD` re-thread coincides with it.  (The
`D`-side hypotheses live entirely in the `hdiff` price, now supplied through
`medium_survivor_price_sqrtD` + `box_disc_three_way`.) -/
theorem hHD_of_box_disc_sqrtD {x z y : ℕ} {ε₀ : ℝ} {j N M a b X : ℕ} (Dset : Finset ℕ)
    {P : ℝ}
    (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * N + 1) (hxlo : x / 2 + 1 ≤ x)
    (hdiff : ∑ d ∈ Dset,
        ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
            (blockPrimeInd N) X M 2 d x
          - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
            (blockPrimeInd N) X M 2 d (x / 2 + 1)‖ ≤ P) :
    ∑ d ∈ Dset, |blockBoxHonestDisc x z y ε₀ j N M a b d| ≤ P :=
  hHD_of_box_disc Dset hz hbX hord hxlo hdiff

/-- **`Plo_sym_of_box_disc_sqrtD`** — re-export (STEP 0: `D < N`-free; see
`hHD_of_box_disc_sqrtD`).  Note the sym carrier's block floor is `max y (pieceN k) ≥ y`, so
its per-`k` prices discharge `hDsq` via `hDsq_at_sym_carrier`. -/
theorem Plo_sym_of_box_disc_sqrtD {x z y : ℕ} {ε₀ : ℝ} {j X : ℕ} (Ps : ℕ) (bound : ℝ)
    (PsymK : ℕ → ℝ) (hxX : x ≤ X) (hxlo : x / 2 + 1 ≤ x)
    (hdiffK : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
            ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) 2 d x
              - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) 2 d (x / 2 + 1)‖)
          ≤ PsymK k) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandSymRectDisc x z y ε₀ j (pieceN k) (pieceM k) d| else 0)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK k :=
  Plo_sym_of_box_disc Ps bound PsymK hxX hxlo hdiffK

/-- **`Plo_low_of_box_disc_sqrtD`** — re-export (STEP 0: `D < N`-free; see
`hHD_of_box_disc_sqrtD`). -/
theorem Plo_low_of_box_disc_sqrtD {x z y : ℕ} {ε₀ : ℝ} {j X : ℕ} (Ps : ℕ) (bound : ℝ)
    (PlowK : ℕ → ℝ) (hxX : x ≤ X) (hxlo : x / 2 + 1 ≤ x)
    (hdiffK : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) 2 d x
              - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) 2 d (x / 2 + 1)‖)
          ≤ PlowK k) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandLowDisc x z y ε₀ j (pieceN k) (pieceM k)
            (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK k :=
  Plo_low_of_box_disc Ps bound PlowK hxX hxlo hdiffK

open Classical in
/-- **`hNum_at_op_sqrtD`** — re-export (STEP 0: `D < N`-free; see
`hHD_of_box_disc_sqrtD`).  The `Price i` slots are now dischargeable on the ENTIRE box
range: each is TWO `medium_survivor_price_sqrtD` applications (`T = x` and `T = x/2+1`,
same price) at `X := 2^{i+1} − 1`, with `hDsq`/`habs` in place of the failing `D < N`. -/
theorem hNum_at_op_sqrtD {x z y : ℕ} {ε₀ : ℝ} {j N M a b X : ℕ} (K Ps : ℕ) (bound : ℝ)
    (Price : ℕ → ℝ)
    (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * N + 1) (hxlo : x / 2 + 1 ≤ x)
    (hK : Nat.log 2 X ≤ K)
    (hiX : ∀ i ∈ dyadicBoundary N M (x / 2 + 1) x (z * y) K, 2 ^ (i + 1) ≤ X + 1)
    (hprice : ∀ i ∈ dyadicBoundary N M (x / 2 + 1) x (z * y) K,
        (∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) a b)
                (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd N) (2 ^ (i + 1) - 1) M 2 d x‖)
          + (∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) a b)
                  (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd N) (2 ^ (i + 1) - 1) M 2 d
                (x / 2 + 1)‖)
          ≤ Price i) :
    (∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |blockBoxHonestDisc x z y ε₀ j N M a b d| else 0)
      ≤ ∑ i ∈ dyadicBoundary N M (x / 2 + 1) x (z * y) K, Price i :=
  hNum_at_op K Ps bound Price hz hbX hord hxlo hK hiX hprice

/-! ## 11. Composition sanity — the #check-chain into the exact `hBVblocks` shape

The `example` below is the required composition demonstration at the `_sqrtD` feeders:
per `(j, k)` box, `hNum_at_op_sqrtD` supplies the VERBATIM `Phi k` slot of
`hBlock_of_window_prices`; `hHDblocks_of_perBlock` assembles the blocks; and
`hBVblocks_of_generalBV` emits a conclusion that is character-for-character the
`hBVblocks` hypothesis of `SwitchBlocks.mainA3_of_block_remainders`.  Each `Price j k i`
is TWO `medium_survivor_price_sqrtD` applications at the reduced top `2^{i+1}−1` (`≤ 3`
per box by `dyadicBoundary_card_le_three`, `O(log²x)` in total) — with `hDsq` + `habs`
replacing `D < N`, so the prices now cover the catch-#62 strip; `hSum`/`hNum` are GLU-2's
budget rows. -/

example (x z y : ℕ) (ε₀ : ℝ) (Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (Q : ℝ) (Dlev : ℕ) (X K : ℕ)
    (hz : 1 ≤ z) (hxlo : x / 2 + 1 ≤ x) (hxX : x ≤ X) (hK : Nat.log 2 X ≤ K)
    (hiX : ∀ k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        2 ^ (i + 1) ≤ X + 1)
    (Price : ℕ → ℕ → ℕ → ℝ)
    (hprice : ∀ j k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        (∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < Q * Dlev),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                  (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k) 2 d x‖)
          + (∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < Q * Dlev),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                    (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k) 2 d (x / 2 + 1)‖)
          ≤ Price j k i)
    (Plo : ℕ → ℝ)
    (hLow : ∀ j, (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < Q * Dlev then
          |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k)
            (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0) ≤ Plo j)
    (RHD RCE : ℝ)
    (hSum : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        ((∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
              Price j k i) + Plo j)) ≤ RHD)
    (hCE : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < Q * Dlev then blockConvErr x z y ε₀ j d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (x : ℝ) / (Real.log x) ^ 10) :
    -- the EXACT `hBVblocks` hypothesis of `mainA3_of_block_remainders`:
    (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        rosserRemainder (blockSwitchSieve x z y ε₀ j Ps hPs hPodd) (Q * Dlev))
      ≤ (x : ℝ) / (Real.log x) ^ 10 := by
  have hBlock : ∀ j ∈ Finset.range (maxBlock x z ε₀ + 1),
      (∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < Q * Dlev then |blockHonestDisc x z y ε₀ j d| else 0)
        ≤ (∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
              Price j k i) + Plo j := by
    intro j _
    refine hBlock_of_window_prices x z y ε₀ Ps (Q * Dlev) j
      (fun k => ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        Price j k i)
      (Plo j) ?_ (hLow j)
    intro k _
    exact hNum_at_op_sqrtD K Ps (Q * Dlev) (Price j k) hz
      (le_trans (min_le_right _ _) (Nat.add_le_add_right hxX 1)) (min_le_left _ _)
      hxlo hK (hiX k) (hprice j k)
  exact hBVblocks_of_generalBV x z y ε₀ Ps hPs hPodd Q Dlev
    (hHDblocks_of_perBlock x z y ε₀ Ps (Q * Dlev) _ hBlock hSum) hCE hNum

/-! ## Composition sanity -/

section CompositionSanity

-- deliverable 1: the single-term β-side
#check @Salt.Chen.two_sqrt_primes_not_both_dvd
#check @Salt.Chen.block_prime_dvd_unique
#check @Salt.Chen.blockDrop
#check @Salt.Chen.cutoffTwist_coprimeRestrict_sub_efold
#check @Salt.Chen.cutoffTwist_sub_efold_sqrtD
#check @Salt.Chen.efold_beta_le_single
#check @Salt.Chen.norm_cutoffTwist_sub_le_efold_sqrtD
-- deliverable 2: the terminal variant
#check @Salt.Chen.card_conductor_not_dvd_le
#check @Salt.Chen.crumb_chi_sum_le
#check @Salt.Chen.cutoffEfoldTerm_reorg_sqrtD
#check @Salt.Chen.hErrSum_cutoff_discharge_sqrtD
#check @Salt.Chen.general_BV_cutoff_closed_sqrtD
#check @Salt.Chen.general_BV_cutoff_sqrtD
-- deliverable 3: the re-threaded feeders
#check @Salt.Chen.medium_survivor_price_sqrtD
#check @Salt.Chen.hDsq_of_carrier_floor
#check @Salt.Chen.hDsq_at_sym_carrier
#check @Salt.Chen.hHD_of_box_disc_sqrtD
#check @Salt.Chen.Plo_sym_of_box_disc_sqrtD
#check @Salt.Chen.Plo_low_of_box_disc_sqrtD
#check @Salt.Chen.hNum_at_op_sqrtD
-- the landed consumers (the VERBATIM slots)
#check @Salt.Chen.hBlock_of_window_prices
#check @Salt.Chen.hHDblocks_of_perBlock
#check @Salt.Chen.hBVblocks_of_generalBV
#check @Salt.Chen.mainA3_of_block_remainders

end CompositionSanity

/-! ## 11b. The anti-#69 witness (node PRICE-0)

Catch #69: the OLD per-`e` rows `herr_LEpos`/`herr_D0E`/`herr_scale` (positivity and lower
bounds on `log(⌊X/e⌋·M)`) were UNSATISFIABLE for `e ∈ (X, D]` — there `⌊X/e⌋ = 0`, so the log
is `log 0 = 0` and the rows read `0 < 0`.  Since every medium-band box has `D ~ x^{0.497} > X`,
the range `(X, D]` is nonempty and the terminal was inapplicable.  The repair guards the three
rows with `e ≤ X`; past the top the summand they bound is handled instead by
`cutoffEfoldTerm_eq_zero_of_gt` (the term vanishes).  The two examples below positively witness
the repair at a medium-band shape `X < D` (`X = 2`, `M = 2`, `D = 4`): the guard `e ≤ X = 2`
leaves only `e = 2` live (`⌊2/2⌋ = 1`, so the rows are TRUE there), while `e ∈ {3, 4}` — where
the OLD rows demanded `0 < 0` — is now vacuous.  (`herr_D0E`'s `C0`-power needs the
operating-point log margin of `d0_window_nonempty`, PRICE-1's discharge, not a medium-band
triviality; but its guarded shape is likewise vacuous on `(X, D]`.) -/

/-- Anti-#69: the guarded `herr_LEpos` IS satisfiable at the medium-band shape `X = 2 < D = 4`
(the OLD unguarded row was false at `e ∈ {3, 4}` where `⌊2/e⌋ = 0`, `log 0 = 0`). -/
example : ∀ e, 2 ≤ e → e ≤ 4 → e ≤ 2 → 0 < Real.log (((2 / e : ℕ) : ℝ) * (2 : ℝ)) := by
  intro e he2 _ hle2
  have he : e = 2 := by omega
  subst he
  have hval : (((2 / 2 : ℕ) : ℝ) * (2 : ℝ)) = 2 := by norm_num
  rw [hval]
  exact Real.log_pos (by norm_num)

/-- Anti-#69: the guarded `herr_scale` IS satisfiable at the same shape (equality at `e = 2`,
`log 4 = 2·log 2`). -/
example : ∀ e, 2 ≤ e → e ≤ 4 → e ≤ 2 →
    Real.log (((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ))
      ≤ 2 * Real.log (((2 / e : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) := by
  intro e he2 _ hle2
  have he : e = 2 := by omega
  subst he
  have h1 : (((2 / 2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) = 2 := by norm_num
  have h2 : (((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) = 2 ^ 2 := by norm_num
  rw [h1, h2, Real.log_pow]
  exact le_of_eq (by push_cast; ring)

/-- Anti-#69 (the soundness underneath): past the top (`X = 2 < e = 3`) the per-`e` term is
identically `0`, so the guarded-away summands need no positivity. -/
example : cutoffEfoldTerm (fun _ => (0 : ℂ)) 5 2 7 9 1 {6} 3 = 0 :=
  cutoffEfoldTerm_eq_zero_of_gt (fun _ => 0) 5 2 7 9 1 {6} (by norm_num : (2 : ℕ) < 3)

/-! ## 12. The anti-#64 certificate — the decoupled `D0`-window is NONEMPTY at the
boundary boxes (node D0W)

Catch #64 (`GlueFinal.catch64_op_boundary_infeasible`) proved the OLD coupled rows
(`hD0lo_main` at the SW exponent `C0` jointly with `hD0N'` at `C0`) contradictory at every
`dyadicBoundary` box.  After the D0W repair (`hD0lo_main` weakened in place to the T4-tail
exponent `A+2` — the only power `EnergyClose.four_term_scale_le` ever consumed), the window
is restored.  This section certifies it kernel-checked, at the operating convention
`A = 13`, `C0 = 18 = A + 5` (so the rows below are at exponents `A+2 = 15`, `A+4 = 17`,
`C0 = 18`).

**The construction.**  `D0 = 2^{k0}` with `k0 = ⌈log₂⌈L^{17}⌉⌉`, so `L^{17} ≤ D0 ≤ 4·L^{17}`
(`L = log(X·M)`, the box's cutoff-mass log).  Against each binding row, with
`t = log x ≥ 10^9` (threshold dwarfed by the `w₀`-guard scale `x₀ ≈ exp(1.6·10^{10})`),
`L ∈ [t − 1, t + 3]` (boundary clauses 1+3 with `M ≤ 2N`), `log N ≥ (11/24)·t − 7` (the
`hNfloor` row — the operating floors put every priced box's block scale above `x^{11/24}/8`):

* `herr_D0lo` (`L^{17} ≤ D0`): by construction.
* `hD0lo_main`, DECOUPLED (`L^{15} ≤ 2·2^{k0}`): from `L^{17} ≤ D0`, `L ≥ 1`.
* `hD0` (`D0 ≤ L^{18}`): `4·L^{17} ≤ L^{18} ⟺ 4 ≤ L` — room factor `L/4 ~ 4·10^9`.
* `hD0N'` (`D0 ≤ (log N)^{18}`): `L ≤ (12/5)·W` at `W := (11/24)·t − 7 ≤ log N`, so it needs
  `W ≥ 4·(12/5)^{17} ≈ 1.17·10^7` — satisfied with factor `≈ 39` at `t = 10^9` (the OLD
  coupled shape needed `log N > 0.707·L`, impossible at `log N/L → 13/24 ≈ 0.5417`).
* **`herr_D0E` (per-`e`, dilated: `D0 ≤ (log(⌊X/e⌋·M))^{18}`) — the verdict: NO decoupling
  needed or possible.**  Traced use: `hsmall_pere_discharge` feeds it to
  `hSmallCut_discharge`'s `hD0` slot at the dilated carrier, where the `C0` power is
  load-bearing (the conductor count `D0 ≤ LE^{C0}` must cancel the SW denominator
  `LE^{A+1+C0}`); it is an UPPER-bound row of the `hD0N'` family, so catch #64's
  lower-bound mechanism never applied to it.  Feasibility at the boundary boxes goes
  through the landed `herr_scale` row (`LE ≥ L/2`, the dilated log loses at most a factor
  `2` — GLU-2's "pinches harder" ONLY bit against the old `C0`-coupled LOWER bound):
  `4·L^{17} ≤ (L/2)^{18} ⟺ L ≥ 4·2^{18} = 2^{20} ≈ 1.05·10^6` — factor `≈ 950` at
  `t = 10^9`.  Emitted below in exactly that `herr_scale`-shaped form.
* `hD0N` (`D0 ≤ N`) and the `x`-scale bound (`D0 ≤ x^{11/24}/8`, from which any level row
  `D0 ≤ D` follows at the operating `D ~ x^{1/2−ε}`): `4·L^{17} ≤ W^{18} ≤ e^W ≤ x^{11/24}/8`.

`h2D0` and `hD0eq` hold by construction; the `D0 ≤ D` adjacency chains from the
`x`-scale bound.  Consumed by the GLU-2 re-run when instantiating
`medium_survivor_price_sqrtD` at the boundary boxes (`norm_num` converts `15 = 13 + 2`,
`17 = 13 + 4`, `18` to the `A`-form exponents). -/

/-- **`d0_window_nonempty` (node D0W) — the anti-#64 certificate.**  At the operating point
(`x ≥ exp(10^9)`, `M ≤ 2N`, the block floor `N ≥ x^{11/24}/8`), EVERY `dyadicBoundary` box
(any m-floor `F`, at the mandated `X = 2^{i+1} − 1`) admits a `D0 = 2^{k0}` satisfying ALL
the `D0`-window rows of the repaired terminal family at `A = 13`, `C0 = 18`: the decoupled
`hD0lo_main` (exponent `A+2 = 15`), `herr_D0lo` (`A+4 = 17`), `hD0` and `hD0N'` (`C0 = 18`),
the per-`e` `herr_D0E` (via the `herr_scale` form `L ≤ 2·LE`), the scale bound
`D0 ≤ x^{11/24}/8`, and `hD0N : D0 ≤ N`.  See the section header for the margins. -/
theorem d0_window_nonempty {x N M K i X F : ℕ}
    (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hM2N : M ≤ 2 * N)
    (hNfloor : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (N : ℝ))
    (hi : i ∈ dyadicBoundary N M (x / 2 + 1) x F K)
    (hXsub : X = 2 ^ (i + 1) - 1) :
    ∃ D0 k0 : ℕ, D0 = 2 ^ k0 ∧ 2 ≤ D0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((15 : ℝ)) ≤ 2 * (2 : ℝ) ^ k0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((17 : ℝ)) ≤ (D0 : ℝ)
      ∧ (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((18 : ℝ))
      ∧ (D0 : ℝ) ≤ (Real.log N) ^ ((18 : ℝ))
      ∧ (∀ LE : ℝ, Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * LE → (D0 : ℝ) ≤ LE ^ ((18 : ℝ)))
      ∧ (D0 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) / 8
      ∧ D0 ≤ N := by
  -- ① the scale facts: `t ≥ 10^9`, `x ≥ 2`.
  have h109 : (10 : ℝ) ^ 9 = 1000000000 := by norm_num
  have ht : (10 : ℝ) ^ 9 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by
    have h1 := Real.add_one_le_exp ((10 : ℝ) ^ 9)
    linarith
  have hx2 : 2 ≤ x := by exact_mod_cast hxR2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  -- ② the boundary clauses: `x/2 < X·M ≤ 4x`.
  rw [dyadicBoundary, Finset.mem_filter] at hi
  obtain ⟨-, hcorner, -, hcutoff⟩ := hi
  have hXM : x / 2 + 1 < X * M := by rw [hXsub]; exact hcutoff
  have hXle : X ≤ 2 ^ (i + 1) := by rw [hXsub]; exact Nat.sub_le _ _
  have hXM4x : X * M ≤ 4 * x :=
    calc X * M ≤ 2 ^ (i + 1) * (2 * N) := Nat.mul_le_mul hXle hM2N
      _ = 4 * (2 ^ i * N) := by rw [pow_succ]; ring
      _ ≤ 4 * (2 ^ i * (N + 1)) :=
          Nat.mul_le_mul (le_refl 4) (Nat.mul_le_mul (le_refl (2 ^ i)) (Nat.le_succ N))
      _ ≤ 4 * x := Nat.mul_le_mul (le_refl 4) hcorner
  have hXMposN : 0 < X * M := by omega
  have hXMposR : (0 : ℝ) < (X : ℝ) * (M : ℝ) := by exact_mod_cast hXMposN
  have hXM4xR : (X : ℝ) * (M : ℝ) ≤ 4 * (x : ℝ) := by exact_mod_cast hXM4x
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  -- ③ `t − 1 ≤ L ≤ t + 3`.
  have hL_lo : Real.log x - 1 ≤ L := by
    have h1 : x < (x / 2 + 1) * 2 := by omega
    have h2 : x / 2 + 1 ≤ X * M := by omega
    have h1R : (x : ℝ) < ((x / 2 + 1 : ℕ) : ℝ) * 2 := by exact_mod_cast h1
    have h2R : ((x / 2 + 1 : ℕ) : ℝ) ≤ (X : ℝ) * (M : ℝ) := by exact_mod_cast h2
    push_cast at h1R h2R
    have hhalf : (x : ℝ) / 2 < (X : ℝ) * (M : ℝ) := by linarith
    have hlog : Real.log ((x : ℝ) / 2) ≤ L := Real.log_le_log (by linarith) hhalf.le
    rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)] at hlog
    have h2log : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith
  have hL_up : L ≤ Real.log x + 3 := by
    have h1 : L ≤ Real.log (4 * (x : ℝ)) := Real.log_le_log hXMposR hXM4xR
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hxpos)] at h1
    have h4log : Real.log 4 ≤ 3 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
    linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hLnn : (0 : ℝ) ≤ L := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hL4 : (4 : ℝ) ≤ L := by linarith
  have hL20 : (1048576 : ℝ) ≤ L := by linarith
  -- ④ the block-floor log: `W := (11/24)·t − 7 ≤ log N`.
  set W : ℝ := 11 / 24 * Real.log x - 7 with hWdef
  have hWlogN : W ≤ Real.log N := by
    have hlogN := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hxpos _) (by norm_num))
      hNfloor
    rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hxpos _)) (by norm_num : (8 : ℝ) ≠ 0),
      Real.log_rpow hxpos] at hlogN
    have h8log : Real.log 8 ≤ 7 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)]
    rw [hWdef]
    linarith
  have hWpos : (0 : ℝ) < W := by rw [hWdef]; linarith
  have hW1296 : (1296 : ℝ) ≤ W := by rw [hWdef]; linarith
  have hLW : L ≤ 12 / 5 * W := by rw [hWdef]; linarith
  have hW4 : 4 * ((12 : ℝ) / 5) ^ ((17 : ℝ)) ≤ W := by
    have hc : ((12 : ℝ) / 5) ^ ((17 : ℝ)) = ((12 : ℝ) / 5) ^ (17 : ℕ) := by
      rw [show ((17 : ℝ)) = ((17 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hnum : 4 * ((12 : ℝ) / 5) ^ (17 : ℕ) ≤ 11 / 24 * 10 ^ 9 - 7 := by norm_num
    rw [hc, hWdef]
    linarith
  -- ⑤ the dyadic window: `D0 = 2^{k0} ∈ [L^{17}, 4·L^{17}]`.
  have hL17_1 : (1 : ℝ) ≤ L ^ ((17 : ℝ)) := Real.one_le_rpow hL1 (by norm_num)
  have hL17_2 : (2 : ℝ) ≤ L ^ ((17 : ℝ)) := by
    calc (2 : ℝ) ≤ L := by linarith
      _ = L ^ ((1 : ℝ)) := (Real.rpow_one L).symm
      _ ≤ L ^ ((17 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  -- `n`/`k0` are introduced OPAQUELY (obtain, not set): their computational bodies
  -- (`Nat.ceil`/`Nat.clog` over noncomputable reals) must stay out of defeq reach.
  obtain ⟨n, hn_ge, hn_le⟩ :
      ∃ n : ℕ, L ^ ((17 : ℝ)) ≤ (n : ℝ) ∧ (n : ℝ) ≤ L ^ ((17 : ℝ)) + 1 :=
    ⟨⌈L ^ ((17 : ℝ))⌉₊, Nat.le_ceil _,
      le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg hLnn _))⟩
  have hn1 : 1 < n := by
    have h1R : (1 : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast h1R
  obtain ⟨k0, hnpow, hpow2n⟩ : ∃ k0 : ℕ, n ≤ 2 ^ k0 ∧ 2 ^ k0 ≤ 2 * n := by
    refine ⟨Nat.clog 2 n, Nat.le_pow_clog (by norm_num) n, ?_⟩
    have hk0pos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) hn1
    have hpow_lt : 2 ^ (Nat.clog 2 n - 1) < n :=
      Nat.pow_pred_clog_lt_self (by norm_num) hn1
    have hsplit : 2 * 2 ^ (Nat.clog 2 n - 1) = 2 ^ Nat.clog 2 n := by
      rw [← pow_succ']
      congr 1
      omega
    rw [← hsplit]
    exact Nat.mul_le_mul (le_refl 2) (le_of_lt hpow_lt)
  have hD0_lo : L ^ ((17 : ℝ)) ≤ ((2 ^ k0 : ℕ) : ℝ) := by
    refine le_trans hn_ge ?_
    exact_mod_cast hnpow
  have hD0_hi : ((2 ^ k0 : ℕ) : ℝ) ≤ 4 * L ^ ((17 : ℝ)) := by
    have h1 : ((2 ^ k0 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hpow2n
    linarith
  have hL18eq : L ^ ((18 : ℝ)) = L * L ^ ((17 : ℝ)) := by
    have hh := Real.rpow_add hLpos 1 17
    rw [Real.rpow_one] at hh
    rw [show (18 : ℝ) = 1 + 17 by norm_num, hh]
  have h17nn : (0 : ℝ) ≤ L ^ ((17 : ℝ)) := Real.rpow_nonneg hLnn _
  -- ⑥ the `hD0N'` leg: `4·L^{17} ≤ W^{18}` (the anti-#64 margin).
  have hW18 : 4 * L ^ ((17 : ℝ)) ≤ W ^ ((18 : ℝ)) := by
    have hW17 : L ^ ((17 : ℝ)) ≤ ((12 : ℝ) / 5) ^ ((17 : ℝ)) * W ^ ((17 : ℝ)) := by
      calc L ^ ((17 : ℝ)) ≤ (12 / 5 * W) ^ ((17 : ℝ)) :=
            Real.rpow_le_rpow hLnn hLW (by norm_num)
        _ = ((12 : ℝ) / 5) ^ ((17 : ℝ)) * W ^ ((17 : ℝ)) :=
            Real.mul_rpow (by norm_num) hWpos.le
    have hW18eq : W ^ ((18 : ℝ)) = W * W ^ ((17 : ℝ)) := by
      have hh := Real.rpow_add hWpos 1 17
      rw [Real.rpow_one] at hh
      rw [show (18 : ℝ) = 1 + 17 by norm_num, hh]
    have h17Wnn : (0 : ℝ) ≤ W ^ ((17 : ℝ)) := Real.rpow_nonneg hWpos.le _
    rw [hW18eq]
    calc 4 * L ^ ((17 : ℝ))
        ≤ 4 * (((12 : ℝ) / 5) ^ ((17 : ℝ)) * W ^ ((17 : ℝ))) := by linarith
      _ = (4 * ((12 : ℝ) / 5) ^ ((17 : ℝ))) * W ^ ((17 : ℝ)) := by ring
      _ ≤ W * W ^ ((17 : ℝ)) := mul_le_mul_of_nonneg_right hW4 h17Wnn
  -- ⑦ the `hD0N` leg: `W^{18} ≤ e^W ≤ x^{11/24}/8`.
  have hexpW : W ^ ((18 : ℝ)) ≤ Real.exp W := by
    have hunn : (0 : ℝ) ≤ W / 36 := by linarith
    have hquad : W ≤ (W / 36) ^ ((2 : ℝ)) := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hexpand : (W / 36) ^ (2 : ℕ) = W * W / 1296 := by ring
      rw [hexpand, le_div_iff₀ (by norm_num : (0 : ℝ) < 1296)]
      have keyq : (0 : ℝ) ≤ (W - 1296) * W := mul_nonneg (by linarith) hWpos.le
      linarith [keyq]
    have hu : W / 36 ≤ Real.exp (W / 36) := by linarith [Real.add_one_le_exp (W / 36)]
    calc W ^ ((18 : ℝ))
        ≤ ((W / 36) ^ ((2 : ℝ))) ^ ((18 : ℝ)) :=
          Real.rpow_le_rpow hWpos.le hquad (by norm_num)
      _ = (W / 36) ^ ((36 : ℝ)) := by
          rw [← Real.rpow_mul hunn]
          norm_num
      _ ≤ (Real.exp (W / 36)) ^ ((36 : ℝ)) := Real.rpow_le_rpow hunn hu (by norm_num)
      _ = Real.exp W := by
          rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
          congr 1
          ring
  have hexp_le : Real.exp W ≤ (x : ℝ) ^ ((11 : ℝ) / 24) / 8 := by
    have hEW : Real.exp W = (x : ℝ) ^ ((11 : ℝ) / 24) / Real.exp 7 := by
      rw [hWdef, Real.exp_sub, Real.rpow_def_of_pos hxpos]
      have hmul : Real.log (x : ℝ) * ((11 : ℝ) / 24) = 11 / 24 * Real.log x := by ring
      rw [hmul]
    rw [hEW]
    have h7 : (8 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hxpos.le _) (by norm_num) h7
  -- ⑧ emit the rows.
  have hcast : ((2 ^ k0 : ℕ) : ℝ) = (2 : ℝ) ^ k0 := by push_cast; ring
  refine ⟨2 ^ k0, k0, rfl, le_trans (by omega : 2 ≤ n) hnpow, ?_, hD0_lo, ?_, ?_, ?_, ?_, ?_⟩
  · -- `hD0lo_main`, the DECOUPLED row (exponent `A+2 = 15`)
    have h15 : L ^ ((15 : ℝ)) ≤ L ^ ((17 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h2k0pos : (0 : ℝ) < (2 : ℝ) ^ k0 := by positivity
    calc L ^ ((15 : ℝ)) ≤ L ^ ((17 : ℝ)) := h15
      _ ≤ ((2 ^ k0 : ℕ) : ℝ) := hD0_lo
      _ = (2 : ℝ) ^ k0 := hcast
      _ ≤ 2 * (2 : ℝ) ^ k0 := by linarith
  · -- `hD0` (`D0 ≤ L^{C0}`, `C0 = 18`)
    rw [hL18eq]
    have key : (0 : ℝ) ≤ (L - 4) * L ^ ((17 : ℝ)) := mul_nonneg (by linarith) h17nn
    linarith [hD0_hi, key]
  · -- `hD0N'` (`D0 ≤ (log N)^{C0}`, `C0 = 18`)
    have hmono : W ^ ((18 : ℝ)) ≤ (Real.log N) ^ ((18 : ℝ)) :=
      Real.rpow_le_rpow hWpos.le hWlogN (by norm_num)
    linarith [hD0_hi, hW18, hmono]
  · -- `herr_D0E` in the `herr_scale` form (`LE ≥ L/2`, exponent `C0 = 18`)
    intro LE hLE
    have hhalfpos : (0 : ℝ) < L / 2 := by linarith
    have hstep : 4 * L ^ ((17 : ℝ)) ≤ (L / 2) ^ ((18 : ℝ)) := by
      have hdiv : (L / 2) ^ ((18 : ℝ)) = L ^ ((18 : ℝ)) / (2 : ℝ) ^ ((18 : ℝ)) :=
        Real.div_rpow hLnn (by norm_num) _
      have h218 : (2 : ℝ) ^ ((18 : ℝ)) = 262144 := by
        rw [show ((18 : ℝ)) = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      rw [hdiv, h218, hL18eq, le_div_iff₀ (by norm_num : (0 : ℝ) < 262144)]
      have key : (0 : ℝ) ≤ (L - 1048576) * L ^ ((17 : ℝ)) := mul_nonneg (by linarith) h17nn
      linarith [key]
    have hmono : (L / 2) ^ ((18 : ℝ)) ≤ LE ^ ((18 : ℝ)) :=
      Real.rpow_le_rpow hhalfpos.le (by linarith) (by norm_num)
    linarith [hD0_hi]
  · -- the `x`-scale bound (`D0 ≤ x^{11/24}/8` — chains `hD0D : D0 ≤ D` at the operating level)
    linarith [hD0_hi, hW18, hexpW, hexp_le]
  · -- `hD0N` (`D0 ≤ N`)
    have hfin : ((2 ^ k0 : ℕ) : ℝ) ≤ (N : ℝ) := by
      linarith [hD0_hi, hW18, hexpW, hexp_le, hNfloor]
    exact_mod_cast hfin

end Salt.Chen
