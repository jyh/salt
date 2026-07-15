/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SwitchBlocks
import Salt.Chen.SwitchStrip
import Salt.Chen.AlphaClose

/-!
# BVP — pricing the narrow-block remainders (discharging `hBVblocks`)

Design: `docs/blueprints/flags.md`, entries "2026-07-13 NBL Opus done FULL", "2026-07-13 SW3
Opus done", "2026-07-13 THE PE3c-4 GATE" / "PE3c-4 Opus done FULL — KEYSTONE 2", and the
SW-fiber design block "2026-07-13 ★ THE SW-FIBER DESIGN BLOCK RESOLVED … + CATCH #53 ★" (the
**NBL** bullet).

This is the switch line's remainder close: the object
`hBVblocks : ∑_j rosserRemainder (blockSwitchSieve j …) (Q·Dlev) ≤ x/(log x)^10` that
`SwitchBlocks.mainA3_of_block_remainders` names.  We (a) re-run SW3's per-`d` remainder algebra
with the narrow-`p₁`-block filter added (**Floor A**, fully proven), reducing each block's Rosser
remainder to a summed honest-discrepancy sum plus a conversion-error sum; and (b) compose to the
exact `hBVblocks` shape under the NAMED analytic pricing of the honest discrepancy (via
`general_BV_alpha_final` at the block-narrow `blockAlpha`) and the conversion error (SW4's crude
bound) — **FULL** `hBVblocks_of_generalBV`.

## What the per-block remainder is (mirroring SW3's `switchSieve_rem_split`)

`blockSwitchSieve x z y ε₀ j Ps` shares `prodPrimes = Ps`, `nu = nuChen`, `support = twinWindow x`
with the monolithic `switchSieve`; only `weights = blockACount j`, `totalMass = blockTripleSum j`
carry the block-`j` filter `blockIdx z ε₀ (·.1) = j`.  So SW3's per-`d` machinery re-runs verbatim
with the block filter as an extra conjunct in every triple filter:

  `rem_j d = multSum_j d − ν(d)·totalMass_j`,
  `multSum_j d = #{t ∈ tripleSet : blockIdx (·.1) = j ∧ prod3 t ≡ 2 (mod d)}`,
  `rem_j d = (blockResCount − ν·blockUnitCount) − ν·blockNonUnitCount`,
  `|rem_j d| ≤ |blockHonestDisc_j d| + blockConvErr_j d`.

Summing over `d ∣ Ps, d < Q·Dlev` gives the switched L¹ reduction per block
(`blockRem_rosserRemainder_split_le`), and summing over the blocks (`sum_blockRem_split_le`)
feeds the composition.

## ★ THE NUMERIC PLAN (recorded FIRST — the piece/band accounting) ★

* **Blocks.**  `j ∈ range (maxBlock x z ε₀ + 1)`, `maxBlock = blockIdx z ε₀ x
  = ⌊log(x/z)/log(1+ε₀)⌋ = O(log x)` blocks (`ε₀` a fixed constant).
* **Dyadic `p₃`-pieces per block.**  Each block's honest discrepancy is decomposed over the
  `O(log x)` dyadic `p₃`-pieces `[N, M]`, `M ≤ 2N` (the `general_BV_alpha_final` `β`-side
  `blockPrimeInd N` lives on a dyadic prime block).  Total `blocks × pieces = O(log²x)`.
* **The window coupling → decided-α + band-α (everything an `apDiscBilin` term).**  Inside a
  fixed block the product window `x/2+2 ≤ p₁p₂·p₃ ≤ x` still couples `(m = p₁p₂, p = p₃)`
  (design/NBL: narrow does NOT eliminate it).  The honest resolution (design; SW3d-ii's wall
  dissolves): per `(j, piece)`, the `m`'s wholly decided in the window across the whole `p`-piece
  carry a decided `α = restrictAlpha (blockAlpha j) a b` (`‖·‖ ≤ 1`), and the residual factor-`2`
  crossing band carries its OWN band `α = restrictAlpha (blockAlpha j) a' b'` (`‖·‖ ≤ 1`).  BOTH
  are legal `0/1` `α`'s, and `apDiscBilin` is ADDITIVE in `α`
  (`SwitchStrip.apDiscBilin_sum_alpha`), so `blockHonestDisc_j d` is a SUM of
  `apDiscBilin (α_·) (blockPrimeInd N) X M 2 d` terms — the band is priced by ITS OWN discrepancy
  (small even though its count is large), never by count.
* **Per-piece pricing.**  Each `∑_d ‖apDiscBilin α (blockPrimeInd N) X M 2 d‖
  ≤ K·(XM)/(log XM)^A` by `general_BV_alpha_final` (`Coprime 2 d` FREE for the odd `d ∣ Ps` —
  `switch_dvd_coprime_two`; the residue `R₀ = 2` is a unit — `two_isUnit_of_dvd`).  With
  `XM ≍ x` (from `m·p ≍ x`), each price is `≤ K·x/(log x)^A`.
* **Composition.**  `O(log²x)` decided + `O(log²x)` band applications, each `≤ K·x/(log x)^A`,
  sum to `≤ 2K·log²x·x/(log x)^A = 2K·x/(log x)^{A−2}`.  To clear the `x/(log x)^10` budget with
  room for the constant `2K`: **`A − 2 ≥ 10 + slack`, i.e. `A ≥ 12 + slack`** — the design row.
* **Conversion error.**  `∑_j ∑_d ν(d)·blockNonUnitCount_j d` counts, per block, the triples with
  a product NOT coprime to `d` (odd `d ∣ Ps` ⟹ `p₁ ∣ d`); crude-bounded at the `x/(log x)^10`
  budget (SW4's `hCE` crumb).  This is `hCEblocks`, named.

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* **FLOOR A (FULL).**  `blockResCount`/`blockUnitCount`/`blockNonUnitCount`;
  `blockSwitchSieve_multSum`, `blockMultSum_eq_dvdCount`, `blockMultSum_eq_apCount`;
  `blockUnit_add_blockNonUnit`; `blockSwitchSieve_rem_split`, `blockSwitchSieve_abs_rem_le`;
  `blockHonestDisc`/`blockConvErr`; `blockRem_rosserRemainder_split_le`; `sum_blockRem_split_le`.
* **FLOOR B (the decided/band α, provable pieces).**  `blockPieceAlpha` (the decided-or-band `α`
  = `restrictAlpha (blockAlpha j) a b`) + `norm_blockPieceAlpha_le_one` — the exact `m`-side
  input `general_BV_alpha_final` consumes on each piece, `‖·‖ ≤ 1` intact.  The additivity
  backbone that makes the decided + band terms sum coherently is
  `SwitchStrip.apDiscBilin_sum_alpha` (landed, reused).  `hHDblocks_of_perBlock` — the reduction
  of the summed honest discrepancy to per-block prices (the `O(log²x)`-applications shape).
* **FULL.**  `hBVblocks_of_generalBV` — the composed reduction to the EXACT `hBVblocks` shape of
  `mainA3_of_block_remainders`, under the two summed NAMED bounds (`hHD` = the per-`(j, piece)`
  `apDiscBilin` prices from `general_BV_alpha_final`; `hCE` = the conversion error, SW4) + the
  numeric closure `hNum` (the `A ≥ 12 + slack` row above).

## What remains NAMED (the honest analytic obligation — flagged)

The one step NOT provable on the nose here is the per-`(j, piece)` **pair-bijection + window
identification** `blockHonestDisc_j d = ∑ apDiscBilin (α) (blockPrimeInd N) X M 2 d` over the
decided/band `α`'s — the `(p₁,p₂,p₃) ↦ (p₁p₂, p₃)` bijection (`semiprimeBlockInd`/`blockAlpha`
multiplicity) turning a `tripleSet` filter into `apDiscBilin`'s double sum (SW3d-iii, NOT in the
corpus), composed with the decided/band window classification
(`SwitchStrip.productInWindow_of_corners` &c. serve).  This is carried as the NAMED per-block
input `hHD` of `hBVblocks_of_generalBV` (its analytic content is one `general_BV_alpha_final`
application per decided/band `α` per `(j, piece)`); the H-glue discharges it together with the
four operating-point thresholds (`hlev`/`hD0lo`/`hMlev`/`hdiv`) and the scale conditions.  See
the closing flag `docs/blueprints/flags.md`, "2026-07-13 BVP".

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the per-block residue / unit / non-unit counts (the block filter added) -/

/-- **`blockResCount j d`** — the admissible triples in block `j` (`blockIdx z ε₀ p₁ = j`) with
`prod ≡ 2 (mod d)` (`= multSum_j d`, by `blockMultSum_eq_apCount`); the block's residue-class
count.  SW3's `switchResCount` with the narrow-`p₁`-block filter added. -/
noncomputable def blockResCount (x z y : ℕ) (ε₀ : ℝ) (j d : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧
        ((prod3 t : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))).card : ℝ)

open Classical in
/-- **`blockUnitCount j d`** — the admissible triples in block `j` whose product is a UNIT mod `d`
(coprime to `d`); the support of `apDiscBilin`'s coprime main term.  SW3's `switchUnitCount` with
the block filter. -/
noncomputable def blockUnitCount (x z y : ℕ) (ε₀ : ℝ) (j d : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧ IsUnit ((prod3 t : ℕ) : ZMod d))).card : ℝ)

open Classical in
/-- **`blockNonUnitCount j d`** — the admissible triples in block `j` whose product is NOT coprime
to `d`; the conversion-error support (for odd `d ∣ Ps` these have `p₁ ∣ d`).  SW3's
`switchNonUnitCount` with the block filter. -/
noncomputable def blockNonUnitCount (x z y : ℕ) (ε₀ : ℝ) (j d : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧ ¬ IsUnit ((prod3 t : ℕ) : ZMod d))).card : ℝ)

/-! ## Part B — the per-`d` AP-count reformulation of the block `multSum` -/

section BlockRem

variable (x z y : ℕ) (ε₀ : ℝ) (j Ps : ℕ) (hPs : Squarefree Ps)
  (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)

/-- **`multSum_j d` is the block-`j` window triple-mass in the class `d ∣ (prod−2)`.**  The block
sieve counts (with multiplicity `blockACount j`) the window points `n` with `d ∣ n`; by `rfl`
(support/weights unfold), mirroring `switchSieve_multSum`. -/
lemma blockSwitchSieve_multSum (d : ℕ) :
    (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).multSum d
      = ∑ n ∈ twinWindow x, if d ∣ n then blockACount x z y ε₀ j n else 0 := rfl

/-- **`multSum_j d` counts block-`j` triples with `d ∣ prod−2` (FULL).**  Fibering the block-`j`
triple set over `n = prod3 t − 2 ∈ twinWindow x` and matching the per-`n` fibre against
`blockACount j`.  SW3's `switchSieve_multSum_eq_dvdCount` with the block filter as an extra
conjunct. -/
theorem blockMultSum_eq_dvdCount (d : ℕ) :
    (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).multSum d
      = (((tripleSet x z y).filter
            (fun t => blockIdx z ε₀ t.1 = j ∧ d ∣ (prod3 t - 2))).card : ℝ) := by
  classical
  rw [blockSwitchSieve_multSum]
  have Hmem : ∀ t ∈ (tripleSet x z y).filter
        (fun t => blockIdx z ε₀ t.1 = j ∧ d ∣ (prod3 t - 2)),
      prod3 t - 2 ∈ twinWindow x := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have h := ht.1
    rw [tripleSet, Finset.mem_filter] at h
    obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := h
    rw [twinWindow, Finset.mem_Icc]; omega
  rw [Finset.card_eq_sum_card_fiberwise Hmem, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun n _hn => ?_)
  have hfib : (((tripleSet x z y).filter
          (fun t => blockIdx z ε₀ t.1 = j ∧ d ∣ (prod3 t - 2))).filter
          (fun t => prod3 t - 2 = n))
      = (tripleSet x z y).filter
          (fun t => (blockIdx z ε₀ t.1 = j ∧ d ∣ (prod3 t - 2)) ∧ prod3 t - 2 = n) := by
    rw [Finset.filter_filter]
  rw [hfib]
  by_cases hdn : d ∣ n
  · rw [if_pos hdn]
    unfold blockACount
    rw [Nat.cast_inj]
    refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
    rw [tripleSet, Finset.mem_filter] at ht
    obtain ⟨_, _, _, _, _, _, _, _, hlo, _⟩ := ht
    constructor
    · rintro ⟨hb, hpe⟩
      have hn : prod3 t - 2 = n := by omega
      exact ⟨⟨hb, by rw [hn]; exact hdn⟩, hn⟩
    · rintro ⟨⟨hb, _⟩, hpn⟩
      exact ⟨hb, by omega⟩
  · rw [if_neg hdn, eq_comm, Nat.cast_eq_zero, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro t _
    rintro ⟨⟨_, hdvd⟩, hpn⟩
    rw [hpn] at hdvd
    exact hdn hdvd

/-- **`multSum_j d = blockResCount j d` (FULL).**  Recasting `blockMultSum_eq_dvdCount` through
`d ∣ (prod − 2) ⟺ (prod : ZMod d) = (2 : ZMod d)` (valid since every admissible product `≥ 2`).
SW3's `switchSieve_multSum_eq_apCount`, block-filtered. -/
theorem blockMultSum_eq_apCount (d : ℕ) :
    (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).multSum d = blockResCount x z y ε₀ j d := by
  classical
  rw [blockMultSum_eq_dvdCount, blockResCount, Nat.cast_inj]
  refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
  rw [tripleSet, Finset.mem_filter] at ht
  obtain ⟨_, _, _, _, _, _, _, _, hlo, _⟩ := ht
  have hp2 : 2 ≤ prod3 t := by omega
  constructor
  · rintro ⟨hb, hdvd⟩
    refine ⟨hb, ?_⟩
    have : ((prod3 t - 2 : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub hp2, sub_eq_zero] at this
    exact this
  · rintro ⟨hb, hcong⟩
    refine ⟨hb, ?_⟩
    refine (ZMod.natCast_eq_zero_iff _ _).mp ?_
    rw [Nat.cast_sub hp2, sub_eq_zero]
    exact hcong

/-! ## Part C — the honest per-`d` remainder split (discrepancy + conversion error) -/

/-- `blockUnitCount j d + blockNonUnitCount j d = blockTripleSum j` — the block's coprime and
non-coprime triple counts partition the block count.  SW3's `switchUnit_add_switchNonUnit`. -/
theorem blockUnit_add_blockNonUnit (d : ℕ) :
    blockUnitCount x z y ε₀ j d + blockNonUnitCount x z y ε₀ j d
      = blockTripleSum x z y ε₀ j := by
  classical
  unfold blockUnitCount blockNonUnitCount
  rw [blockTripleSum_eq_card, ← Nat.cast_add]
  congr 1
  have hU : (tripleSet x z y).filter
        (fun t => blockIdx z ε₀ t.1 = j ∧ IsUnit ((prod3 t : ℕ) : ZMod d))
      = (blockTripleSet x z y ε₀ j).filter (fun t => IsUnit ((prod3 t : ℕ) : ZMod d)) := by
    rw [blockTripleSet, Finset.filter_filter]
  have hN : (tripleSet x z y).filter
        (fun t => blockIdx z ε₀ t.1 = j ∧ ¬ IsUnit ((prod3 t : ℕ) : ZMod d))
      = (blockTripleSet x z y ε₀ j).filter (fun t => ¬ IsUnit ((prod3 t : ℕ) : ZMod d)) := by
    rw [blockTripleSet, Finset.filter_filter]
  rw [hU, hN]
  exact Finset.card_filter_add_card_filter_not
    (s := blockTripleSet x z y ε₀ j) (p := fun t => IsUnit ((prod3 t : ℕ) : ZMod d))

/-- **The honest per-`d` block remainder split (FULL).**
`rem_j d = (blockResCount − ν(d)·blockUnitCount) − ν(d)·blockNonUnitCount`
= `(honest residue-class discrepancy against the coprime main term) − (conversion error)`.
SW3's `switchSieve_rem_split`, block-filtered. -/
theorem blockSwitchSieve_rem_split (d : ℕ) :
    (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).rem d
      = (blockResCount x z y ε₀ j d - nuChen d * blockUnitCount x z y ε₀ j d)
        - nuChen d * blockNonUnitCount x z y ε₀ j d := by
  rw [BoundingSieve.rem, blockSwitchSieve_nu, blockSwitchSieve_totalMass,
    ← blockUnit_add_blockNonUnit x z y ε₀ j d]
  have hM : (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).multSum d
      = blockResCount x z y ε₀ j d :=
    blockMultSum_eq_apCount x z y ε₀ j Ps hPs hPodd d
  rw [hM]
  ring

end BlockRem

/-- The block honest residue-class discrepancy against the coprime main term (the `apDiscBilin`
target after the decided/band decomposition, per `(j, piece)`). -/
noncomputable def blockHonestDisc (x z y : ℕ) (ε₀ : ℝ) (j d : ℕ) : ℝ :=
  blockResCount x z y ε₀ j d - nuChen d * blockUnitCount x z y ε₀ j d

/-- The block conversion error `ν(d)·(non-coprime block triple count)` (SW4's crude-bounded crumb;
`twinA1`'s `ω(d)·log/φ(d)` analogue). -/
noncomputable def blockConvErr (x z y : ℕ) (ε₀ : ℝ) (j d : ℕ) : ℝ :=
  nuChen d * blockNonUnitCount x z y ε₀ j d

section BlockRem2

variable (x z y : ℕ) (ε₀ : ℝ) (j Ps : ℕ) (hPs : Squarefree Ps)
  (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)

/-- **The per-`d` block bridge bound (FULL).**  `|rem_j d| ≤ |blockHonestDisc_j d| +
blockConvErr_j d`, the triangle inequality on `blockSwitchSieve_rem_split` (the conversion error
is `≥ 0`).  SW3's `switchSieve_abs_rem_le`, block-filtered. -/
theorem blockSwitchSieve_abs_rem_le (d : ℕ) :
    |(blockSwitchSieve x z y ε₀ j Ps hPs hPodd).rem d|
      ≤ |blockHonestDisc x z y ε₀ j d| + blockConvErr x z y ε₀ j d := by
  have hconv : 0 ≤ nuChen d * blockNonUnitCount x z y ε₀ j d := by
    apply mul_nonneg
    · rw [nuChen_apply]; positivity
    · unfold blockNonUnitCount; positivity
  rw [blockSwitchSieve_rem_split]
  have h := abs_sub (blockResCount x z y ε₀ j d - nuChen d * blockUnitCount x z y ε₀ j d)
      (nuChen d * blockNonUnitCount x z y ε₀ j d)
  rw [abs_of_nonneg hconv] at h
  exact h

/-- **The summed L¹ reduction of the block Rosser remainder (FULL).**  At any level `bound`,
`rosserRemainder (blockSwitchSieve j …) bound` is bounded by the summed honest discrepancy plus
the summed conversion error.  Termwise `blockSwitchSieve_abs_rem_le`, then `Finset.sum_add_distrib`.
SW3's `switchSieve_rosserRemainder_split_le`, block-filtered. -/
theorem blockRem_rosserRemainder_split_le (bound : ℝ) :
    rosserRemainder (blockSwitchSieve x z y ε₀ j Ps hPs hPodd) bound
      ≤ (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then |blockHonestDisc x z y ε₀ j d| else 0)
        + (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then blockConvErr x z y ε₀ j d else 0) := by
  rw [rosserRemainder, blockSwitchSieve_prodPrimes, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d _
  by_cases h : (d : ℝ) < bound
  · rw [if_pos h, if_pos h, if_pos h]
    exact blockSwitchSieve_abs_rem_le x z y ε₀ j Ps hPs hPodd d
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

end BlockRem2

/-- **The block sum of the L¹ reductions (FULL).**  `∑_j rosserRemainder (blockSwitchSieve j …)
bound` is bounded by the double sum of the honest discrepancies plus the double sum of the
conversion errors.  Termwise `blockRem_rosserRemainder_split_le`, then `Finset.sum_add_distrib`. -/
theorem sum_blockRem_split_le (x z y : ℕ) (ε₀ : ℝ) (Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (bound : ℝ) :
    (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        rosserRemainder (blockSwitchSieve x z y ε₀ j Ps hPs hPodd) bound)
      ≤ (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
            ∑ d ∈ Nat.divisors Ps,
              if (d : ℝ) < bound then |blockHonestDisc x z y ε₀ j d| else 0)
        + (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
            ∑ d ∈ Nat.divisors Ps,
              if (d : ℝ) < bound then blockConvErr x z y ε₀ j d else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  exact blockRem_rosserRemainder_split_le x z y ε₀ j Ps hPs hPodd bound

/-! ## Part D — the decided/band `α` (the `general_BV_alpha_final` `m`-side input per piece) -/

/-- **The decided-or-band `α` on a dyadic `m`-piece** — `blockAlpha j` truncated to the `m`-window
`[a, b)`.  On a `(j, p₃-piece)`, the `m`'s wholly decided in the product window (across the whole
`p`-piece) form one such `α` and the residual factor-`2` crossing band forms another; BOTH are
legal `0/1` coefficients, `‖·‖ ≤ 1` (`norm_blockPieceAlpha_le_one`), and `apDiscBilin` is additive
in `α` (`SwitchStrip.apDiscBilin_sum_alpha`), so `blockHonestDisc_j d` is a SUM of `apDiscBilin`s
over these pieces — every one of which `general_BV_alpha_final` prices (the band by its OWN
discrepancy, NOT by its count: SW3d-ii's wall dissolved). -/
noncomputable def blockPieceAlpha (z y : ℕ) (ε₀ : ℝ) (j a b : ℕ) : ℕ → ℂ :=
  restrictAlpha (blockAlpha z y ε₀ j) a b

/-- **`‖blockPieceAlpha‖ ≤ 1`.**  The decided-or-band `α` inherits the `0/1` bound of `blockAlpha`
(`norm_blockAlpha_le_one`) through `restrictAlpha` — the exact `hα : ∀ m, ‖α m‖ ≤ 1` hypothesis
`general_BV_alpha_final` consumes on the `m`-side of every piece. -/
theorem norm_blockPieceAlpha_le_one (z y : ℕ) (ε₀ : ℝ) (j a b m : ℕ) :
    ‖blockPieceAlpha z y ε₀ j a b m‖ ≤ 1 :=
  norm_restrictAlpha_le_one (fun m => norm_blockAlpha_le_one z y ε₀ j m) a b m

/-! ## Part E — the composition to the exact `hBVblocks` shape -/

/-- **`hHDblocks_of_perBlock` — the per-block reduction of the summed honest discrepancy (FULL).**
The `O(log²x)`-applications structure made explicit: from a per-block bound `hBlock` (each block's
`∑_d |blockHonestDisc_j d|` priced via the `O(log x)` dyadic `p₃`-pieces' decided/band
`apDiscBilin` terms through `general_BV_alpha_final`) plus a numeric closure `hSum`, the summed
honest discrepancy is bounded by `RHD`.  A clean `Finset.sum_le_sum` composition (SW3's
`hHD_of_generalBV_inputs`, per block). -/
theorem hHDblocks_of_perBlock (x z y : ℕ) (ε₀ : ℝ) (Ps : ℕ) (bound : ℝ)
    (RBlock : ℕ → ℝ) {RHD : ℝ}
    (hBlock : ∀ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then |blockHonestDisc x z y ε₀ j d| else 0) ≤ RBlock j)
    (hSum : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1), RBlock j) ≤ RHD) :
    (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then |blockHonestDisc x z y ε₀ j d| else 0)
      ≤ RHD :=
  le_trans (Finset.sum_le_sum hBlock) hSum

/-- **`hBVblocks_of_generalBV` — the composed block-remainder close (the BVP endpoint, FULL).**
Under the two summed NAMED bounds — `hHD` (the honest-discrepancy double sum, the output of
`general_BV_alpha_final` applied per decided/band `α` per `(j, p₃-piece)`; `hHDblocks_of_perBlock`
assembles it from the per-block prices) and `hCE` (the conversion-error double sum, SW4's crude
bound) — plus the numeric closure `hNum` (the `A ≥ 12 + slack` row of the module numeric plan: the
`O(log²x)` prices, each `≤ K·x/(log x)^A`, clear the `x/(log x)^10` budget), the block Rosser
remainders sum below `x/(log x)^10` — **the EXACT `hBVblocks` hypothesis that
`SwitchBlocks.mainA3_of_block_remainders` names**.  Composes `sum_blockRem_split_le` with the
three named obligations. -/
theorem hBVblocks_of_generalBV (x z y : ℕ) (ε₀ : ℝ) (Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (Q : ℝ) (Dlev : ℕ) {RHD RCE : ℝ}
    (hHD : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          ∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < Q * Dlev then |blockHonestDisc x z y ε₀ j d| else 0) ≤ RHD)
    (hCE : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          ∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < Q * Dlev then blockConvErr x z y ε₀ j d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (x : ℝ) / (Real.log x) ^ 10) :
    (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        rosserRemainder (blockSwitchSieve x z y ε₀ j Ps hPs hPodd) (Q * Dlev))
      ≤ (x : ℝ) / (Real.log x) ^ 10 := by
  refine le_trans (sum_blockRem_split_le x z y ε₀ Ps hPs hPodd (Q * Dlev)) ?_
  linarith [hHD, hCE, hNum]

-- Composition sanity (BVP switch line): the honest-discrepancy price `hHD` is one
-- `general_BV_alpha_final` application per decided/band `α` per `(j, p₃-piece)` (the completed
-- KEYSTONE 2, `blockPrimeInd`-`β`-side), and `hBVblocks_of_generalBV`'s conclusion is the EXACT
-- `hBVblocks` shape `mainA3_of_block_remainders` names.

end Salt.Chen
