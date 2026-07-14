/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SwitchBV

/-!
# NBL — the narrow-p₁-block decomposition of the switched sieve

Design: `docs/blueprints/flags.md`, entry "2026-07-13 ★ THE SW-FIBER DESIGN BLOCK RESOLVED
(BJS pp. 57–59 at page level) + CATCH #53 ★", the **NBL** bullet (the catch-#53 repair's
remainder side, superseding the catch-#50 dyadic boxes).  BJS pp. 57/59: `B̄ = ⋃_j B^{(j)}`
over narrow `p₁`-blocks `ω_j ≤ p₁ < ω_j·(1+ε₀)` (`ω_j = z·(1+ε₀)^j`, `j₀ ~ log(y/z)/log(1+ε₀)`
blocks); within a block the product window is a CLEAN `p₂p₃`-cutoff (the `ε₀`-slop rides into the
count's `(1+ε₀)`).  The per-block sieve is SW12's global pattern (`switchSieve`) with the block
`p₁`-filter added; the per-block remainder feeds `general_BV_alpha_final` with a BLOCK-narrow
semiprime `α`.

## The block index (floor-of-log — the geometric analogue of `SwitchDyadic`'s `Nat.log 2`)

`blockIdx z ε₀ p = ⌊log(p/z)/log(1+ε₀)⌋` — the unique `j` with `ω_j ≤ p < ω_{j+1}` for `z ≤ p`.
`blockTripleSet x z y ε₀ j = (tripleSet x z y).filter (blockIdx z ε₀ ·.1 = j)`; the partition
`tripleSet = ⨆_j blockTripleSet` is the fiberwise `Finset.card_eq_sum_card_fiberwise` over
`blockIdx z ε₀ ·.1` (`count_eq_sum_block`, mirroring `SwitchDyadic.count_eq_sum_box`) — every
triple's `p₁` lands in EXACTLY one block.  The count/weight split then transfers:
`aCount = ∑_j blockACount`, `tripleSum = ∑_j blockTripleSum`.

## ★ THE W-FACTORING FINDING (verified, load-bearing) ★

`W s = ∏_{p ∣ prodPrimes} (1 − ν(p))` and `maxDepth s = prodPrimes.primeFactors.card` depend ONLY
on `prodPrimes` and `nu`, and `blockSwitchSieve` shares `prodPrimes = Ps`, `nu = nuChen` with the
monolithic `switchSieve` — the block filter touches only `weights`/`totalMass`.  Hence
`W (blockSwitchSieve j) = W (switchSieve)` and `maxDepth (blockSwitchSieve j) = maxDepth
(switchSieve)` **by `rfl`, for every block `j`** (`blockSwitchSieve_W_eq`,
`blockSwitchSieve_maxDepth_eq`).  So the common carrier `W·(Fchain N s + slack)` factors OUT of
the `j`-sum, and `∑_j blockTripleSum_j = tripleSum` reassembles:

  **`mainA3_of_block_remainders`'s MAIN TERM is LITERALLY IDENTICAL to SW12's
  `mainA3_of_hBVswitch`** — same `W (switchSieve …)`, same `maxDepth (switchSieve …)`, same
  `tripleSum x z y`.

The ONLY delta versus the SW12 monolith is the *remainder side*: SW12's single named
`hBVswitch : rosserRemainder (switchSieve …) (Q·Dlev) ≤ x/(log x)^10` becomes NBL's single named
`hBVblocks : ∑_j rosserRemainder (blockSwitchSieve j …) (Q·Dlev) ≤ x/(log x)^10`.  The block route
buys the clean per-block windows for the eventual `general_BV_alpha_final` pricing (the
block-narrow `blockAlpha`, still `0/1`, `‖·‖ ≤ 1`); **SW4's numeric row is UNCHANGED** from the
CNT2-weighted form (the main term did not move).

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* FLOOR A — `blockIdx` / `maxBlock` / `omegaBlock`; `count_eq_sum_block`; the block partition
  (`tripleSum_eq_sum_blockTripleSum`, `aCount_eq_sum_blockACount`); the per-block sieve instance
  `blockSwitchSieve` with the `rfl` fact lemmas and `block_totalMass_nonneg`; the `W`/`maxDepth`
  collapse (`blockSwitchSieve_W_eq`, `blockSwitchSieve_maxDepth_eq`); guards delegate to
  `switch_hnu`/`switch_hguard` (Ps-based, identical).
* FLOOR B — `block_switch_upper_B` (the sharp cB upper keystone per block, a verbatim
  re-instantiation of `switch_upper_B`) + `triplePrimeSum_le_sum_blocks` (the summed Λ-bridge,
  `switch_siftedSum_eq_sum_blocks` composed with `triplePrimeSum_le_sifted`).
* FULL — `mainA3_of_block_remainders` (the composed conditional A₃ bound, main term identical to
  SW12) + `blockAlpha` / `norm_blockAlpha_le_one` (the block-narrow semiprime `α`, the
  `general_BV_alpha_final` `m`-side input for the later per-block BV pricing).

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the narrow `p₁`-block index and the block partition of `tripleSet` -/

/-- The narrow-block scale `ω_j = z·(1+ε₀)^j` (BJS's block left edge; block `j` is
`ω_j ≤ p₁ < ω_{j+1}`).  Recorded for design faithfulness; the partition uses `blockIdx`. -/
noncomputable def omegaBlock (z : ℕ) (ε₀ : ℝ) (j : ℕ) : ℝ := (z : ℝ) * (1 + ε₀) ^ j

/-- **The narrow-block index of a prime `p`.** `j = ⌊log(p/z)/log(1+ε₀)⌋`, i.e. the unique `j`
with `ω_j ≤ p < ω_{j+1}` (for `z ≤ p`).  Floor-of-log indexing — the geometric analogue of the
dyadic `Nat.log 2` used in `SwitchDyadic`. -/
noncomputable def blockIdx (z : ℕ) (ε₀ : ℝ) (p : ℕ) : ℕ :=
  ⌊Real.log ((p : ℝ) / z) / Real.log (1 + ε₀)⌋₊

/-- The top block index over `tripleSet` (all `p₁ ≤ x`): `j₀ = blockIdx z ε₀ x`.  Blocks range
over `Finset.range (maxBlock x z ε₀ + 1)`. -/
noncomputable def maxBlock (x z : ℕ) (ε₀ : ℝ) : ℕ := blockIdx z ε₀ x

/-- **`blockIdx` is monotone in `p`** (on `1 ≤ p`, for `1 ≤ z`, `0 < ε₀`): larger primes land in
higher (or equal) blocks.  The single fact powering the finite block range. -/
lemma blockIdx_le_of_le {z : ℕ} {ε₀ : ℝ} (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) : blockIdx z ε₀ p ≤ blockIdx z ε₀ q := by
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hden : (0 : ℝ) ≤ Real.log (1 + ε₀) := (Real.log_pos (by linarith)).le
  have hpz : (0 : ℝ) < (p : ℝ) / z := div_pos hpR hzR
  have hnum : Real.log ((p : ℝ) / z) ≤ Real.log ((q : ℝ) / z) :=
    Real.log_le_log hpz (div_le_div_of_nonneg_right (by exact_mod_cast hpq) hzR.le)
  unfold blockIdx
  exact Nat.floor_le_floor (div_le_div_of_nonneg_right hnum hden)

/-- **The block-partition kernel (Floor A).**  Any predicate-filtered count of `tripleSet`
partitions exactly over the narrow `p₁`-blocks `blockIdx z ε₀ (·.1) ∈ [0, maxBlock x z ε₀]`.
Every admissible triple has `1 ≤ p₁ ≤ x`, so `blockIdx z ε₀ p₁ ≤ blockIdx z ε₀ x`
(`blockIdx_le_of_le`); `Finset.card_eq_sum_card_fiberwise` over `blockIdx z ε₀ (·.1)` does the
rest.  The geometric analogue of `SwitchDyadic.count_eq_sum_box`. -/
private lemma count_eq_sum_block {x z y : ℕ} (ε₀ : ℝ) (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    (P : ℕ × ℕ × ℕ → Prop) [DecidablePred P] :
    (((tripleSet x z y).filter P).card : ℝ)
      = ∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          (((tripleSet x z y).filter
              (fun t => blockIdx z ε₀ t.1 = j ∧ P t)).card : ℝ) := by
  classical
  have hmaps : ∀ t ∈ (tripleSet x z y).filter P,
      blockIdx z ε₀ t.1 ∈ Finset.range (maxBlock x z ε₀ + 1) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have h1 : t.1 ∈ Finset.Icc 1 x := by
      have := ht.1
      rw [tripleSet, Finset.mem_filter] at this
      have := this.1
      rw [Finset.mem_product] at this
      exact this.1
    rw [Finset.mem_Icc] at h1
    rw [Finset.mem_range, Nat.lt_succ_iff, maxBlock]
    exact blockIdx_le_of_le hz hε₀ h1.1 h1.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hfilt : ((tripleSet x z y).filter P).filter (fun t => blockIdx z ε₀ t.1 = j)
      = (tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ P t) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro t _
    tauto
  rw [hfilt]

/-! ## Part B — the block-restricted count `blockACount` / `blockTripleSum` -/

/-- **The per-block switch weight** `blockACount j n = #{admissible triples in block `j` with
`prod = n + 2`}` — `aCount`'s block-`j` restriction. -/
noncomputable def blockACount (x z y : ℕ) (ε₀ : ℝ) (j n : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧ prod3 t = n + 2)).card : ℝ)

/-- `0 ≤ blockACount` — a cast card. -/
lemma blockACount_nonneg (x z y : ℕ) (ε₀ : ℝ) (j n : ℕ) : 0 ≤ blockACount x z y ε₀ j n := by
  rw [blockACount]; positivity

/-- **The block-`j` triple set** — the admissible triples whose `p₁` sits in block `j`. -/
noncomputable def blockTripleSet (x z y : ℕ) (ε₀ : ℝ) (j : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j)

/-- **The block-`j` triple count** `∑_{n ∈ window} blockACount j n` — the block's `totalMass`. -/
noncomputable def blockTripleSum (x z y : ℕ) (ε₀ : ℝ) (j : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, blockACount x z y ε₀ j n

/-- **The block Fubini reindex.**  `blockTripleSum j = #{triples in block j}`, mirroring
`tripleSum_eq_card`: the fibres over `n = prod − 2 ∈ twinWindow x` partition `blockTripleSet`. -/
theorem blockTripleSum_eq_card (x z y : ℕ) (ε₀ : ℝ) (j : ℕ) :
    blockTripleSum x z y ε₀ j = ((blockTripleSet x z y ε₀ j).card : ℝ) := by
  unfold blockTripleSum blockACount blockTripleSet
  rw [← Nat.cast_sum]
  congr 1
  have Hmem : ∀ t ∈ (tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j),
      prod3 t - 2 ∈ twinWindow x := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have htri := ht.1
    rw [tripleSet, Finset.mem_filter] at htri
    obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := htri
    rw [twinWindow, Finset.mem_Icc]; omega
  rw [Finset.card_eq_sum_card_fiberwise Hmem]
  refine Finset.sum_congr rfl (fun n _hn => ?_)
  rw [Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro t ht
  have htri := ht
  rw [tripleSet, Finset.mem_filter] at htri
  obtain ⟨_, _, _, _, _, _, _, _, hlo, _⟩ := htri
  constructor
  · rintro ⟨hb, hp⟩; exact ⟨hb, by omega⟩
  · rintro ⟨hb, hp⟩; exact ⟨hb, by omega⟩

/-- **The switch weight partitions over the blocks (Floor A).**  `aCount n = ∑_j blockACount j n`
— each triple with `prod = n + 2` lands in exactly one block. -/
theorem aCount_eq_sum_blockACount (x z y : ℕ) (ε₀ : ℝ) (hz : 1 ≤ z) (hε₀ : 0 < ε₀) (n : ℕ) :
    aCount x z y n
      = ∑ j ∈ Finset.range (maxBlock x z ε₀ + 1), blockACount x z y ε₀ j n := by
  unfold aCount blockACount
  exact count_eq_sum_block ε₀ hz hε₀ (fun t => prod3 t = n + 2)

/-- **The triple count partitions over the blocks (Floor A).**  `tripleSum = ∑_j blockTripleSum j`
— the block reassembly identity (the W-factoring's other half: it lets `∑_j blockTripleSum_j`
collapse back to `tripleSum` after the common carrier factors out). -/
theorem tripleSum_eq_sum_blockTripleSum (x z y : ℕ) (ε₀ : ℝ) (hz : 1 ≤ z) (hε₀ : 0 < ε₀) :
    tripleSum x z y
      = ∑ j ∈ Finset.range (maxBlock x z ε₀ + 1), blockTripleSum x z y ε₀ j := by
  unfold tripleSum blockTripleSum
  rw [show (∑ n ∈ twinWindow x, aCount x z y n)
        = ∑ n ∈ twinWindow x, ∑ j ∈ Finset.range (maxBlock x z ε₀ + 1), blockACount x z y ε₀ j n
      from Finset.sum_congr rfl (fun n _ => aCount_eq_sum_blockACount x z y ε₀ hz hε₀ n)]
  exact Finset.sum_comm

/-! ## Part C — the per-block switched `BoundingSieve` instance + guards -/

/-- **The per-block switched `BoundingSieve`.**  `switchSieve`'s construction with the block
`p₁`-filter added: support = the window points `n` (same as `switchSieve`), weight = the block
multiplicity `blockACount`, `totalMass` = the block count `blockTripleSum`, density `ν = nuChen`,
sifting modulus `Ps` — **`prodPrimes` and `nu` are block-independent**, exactly the W-factoring
premise.  The guards (`switch_hnu`/`switch_hguard`) are Ps-based, so they delegate verbatim. -/
noncomputable def blockSwitchSieve (x z y : ℕ) (ε₀ : ℝ) (j Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) : BoundingSieve where
  support := twinWindow x
  prodPrimes := Ps
  prodPrimes_squarefree := hPs
  weights := fun n => blockACount x z y ε₀ j n
  weights_nonneg := fun n => blockACount_nonneg x z y ε₀ j n
  totalMass := blockTripleSum x z y ε₀ j
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _p hp _ => nuChen_pos hp
  nu_lt_one_of_prime := fun p hp hpd =>
    nuChen_lt_one hp (hPodd p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hPs.ne_zero⟩))

section BlockFacts

variable (x z y : ℕ) (ε₀ : ℝ) (j Ps : ℕ) (hPs : Squarefree Ps)
  (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)

@[simp] lemma blockSwitchSieve_support :
    (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).support = twinWindow x := rfl

@[simp] lemma blockSwitchSieve_prodPrimes :
    (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).prodPrimes = Ps := rfl

@[simp] lemma blockSwitchSieve_nu :
    (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).nu = nuChen := rfl

@[simp] lemma blockSwitchSieve_totalMass :
    (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).totalMass = blockTripleSum x z y ε₀ j := rfl

lemma blockSwitchSieve_siftedSum :
    (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).siftedSum
      = ∑ n ∈ twinWindow x, if Nat.Coprime Ps n then blockACount x z y ε₀ j n else 0 := rfl

/-- `0 ≤ totalMass` — the block count is a cast card. -/
lemma block_totalMass_nonneg : 0 ≤ (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).totalMass := by
  rw [blockSwitchSieve_totalMass, blockTripleSum_eq_card]; positivity

end BlockFacts

/-- **★ THE W-FACTORING (density product).**  `W (blockSwitchSieve j) = W (switchSieve)` for every
block `j`, BY `rfl`: `W s = ∏_{p ∣ prodPrimes}(1 − ν(p))` sees only `prodPrimes = Ps` and
`nu = nuChen`, both block-independent.  This is why the carrier `W` factors out of the `j`-sum. -/
lemma blockSwitchSieve_W_eq (x z y : ℕ) (ε₀ : ℝ) (j Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    Salt.BrunLower.W (blockSwitchSieve x z y ε₀ j Ps hPs hPodd)
      = Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd) := rfl

/-- **★ THE W-FACTORING (sieve depth).**  `maxDepth (blockSwitchSieve j) = maxDepth (switchSieve)`
for every block `j`, BY `rfl`: `maxDepth s = prodPrimes.primeFactors.card`, both `= Ps`. -/
lemma blockSwitchSieve_maxDepth_eq (x z y : ℕ) (ε₀ : ℝ) (j Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    maxDepth (blockSwitchSieve x z y ε₀ j Ps hPs hPodd)
      = maxDepth (switchSieve x z y Ps hPs hPodd) := rfl

/-! ## Part D — the per-block sharp cB upper keystone -/

/-- **`block_switch_upper_B` — the sharp (cB) upper linear sieve, per block.**  A verbatim
re-instantiation of `switch_upper_B` at `sp0 = blockSwitchSieve j`: `twin_A2_per_prime_B` is
generic in the `BoundingSieve`, and the guards (`switch_hnu`/`switch_hguard`) and `totalMass ≥ 0`
are the only instance-specific inputs — the first two are Ps-based (block-independent), the third
is `block_totalMass_nonneg`.  SW12's machinery never used the support's global shape, so the
block filter is transparent.  Conclusion (block `W`/`maxDepth`; collapsed to the global values by
`blockSwitchSieve_W_eq`/`_maxDepth_eq` downstream):

  `siftedSum ≤ (blockTripleSum j · W)·(Fchain N s + ε·CsharpB ε·e²·hBJS s)
                + rosserRemainder (blockSwitchSieve j) (Q·Dlev)`. -/
theorem block_switch_upper_B (x z y : ℕ) (ε₀ : ℝ) (j Ps Dlev : ℕ) (ε K Q : ℝ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hD2 : 2 ≤ Dlev) (hQ : 1 ≤ Q)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev) :
    (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).siftedSum
      ≤ (blockTripleSum x z y ε₀ j
            * Salt.BrunLower.W (blockSwitchSieve x z y ε₀ j Ps hPs hPodd))
          * (Fchain (maxDepth (blockSwitchSieve x z y ε₀ j Ps hPs hPodd)) (logRatio y Dlev)
              + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
        + rosserRemainder (blockSwitchSieve x z y ε₀ j Ps hPs hPodd) (Q * Dlev) := by
  set s := blockSwitchSieve x z y ε₀ j Ps hPs hPodd with hs
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < y := hPy
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    switch_hguard hε hw0 hPodd hPlow
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := switch_hnu Ps
  have htm : 0 ≤ s.totalMass := block_totalMass_nonneg x z y ε₀ j Ps hPs hPodd
  have h := twin_A2_per_prime_B s y Dlev ε K Q hD2 htm hQ hzTop hguard hnu hε.le
    (lt_of_le_of_lt hεsmall (by norm_num)) hKe (stepHypWPC_sharpB ε hε.le hεsmall) h4 hStop
  have htm_eq : s.totalMass = blockTripleSum x z y ε₀ j := rfl
  rw [← htm_eq]
  exact h

/-! ## Part E — the summed Λ-bridge -/

/-- **The switch sifted sum splits over the blocks.**  `(switchSieve).siftedSum
= ∑_j (blockSwitchSieve j).siftedSum` — push the coprimality indicator through
`aCount = ∑_j blockACount` and swap the two sums. -/
lemma switch_siftedSum_eq_sum_blocks (x z y : ℕ) (ε₀ : ℝ) (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    (Ps : ℕ) (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    (switchSieve x z y Ps hPs hPodd).siftedSum
      = ∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).siftedSum := by
  rw [switchSieve_siftedSum]
  have hterm : ∀ n ∈ twinWindow x, (if Nat.Coprime Ps n then aCount x z y n else 0)
      = ∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          (if Nat.Coprime Ps n then blockACount x z y ε₀ j n else 0) := by
    intro n _
    by_cases hcop : Nat.Coprime Ps n
    · simp only [if_pos hcop]
      exact aCount_eq_sum_blockACount x z y ε₀ hz hε₀ n
    · simp only [if_neg hcop, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [blockSwitchSieve_siftedSum]

/-- **`triplePrimeSum_le_sum_blocks` — THE SUMMED BRIDGE (Floor B).**  The honest A₃ Λ-carrier is
dominated by `log x` times the SUM over blocks of the per-block sifted sums.  Composes SW12's
bridge `triplePrimeSum_le_sifted` with the block split `switch_siftedSum_eq_sum_blocks` (each
surviving prime `n` survives in ITS block). -/
theorem triplePrimeSum_le_sum_blocks (x z y P Ps : ℕ) (ε₀ : ℝ) (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hx : 2 ≤ x) (hyx2 : y ≤ x / 2)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P) :
    triplePrimeSum x P y
      ≤ Real.log x * ∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).siftedSum := by
  have hbridge := triplePrimeSum_le_sifted x z y P Ps hPs hPodd hPy hx hyx2 hPfull
  rwa [switch_siftedSum_eq_sum_blocks x z y ε₀ hz hε₀ Ps hPs hPodd] at hbridge

/-! ## Part F — the composed conditional A₃ bound + the block-narrow semiprime `α` -/

/-- **`blockRem j`** — the per-block switched Rosser remainder at level `Q·Dlev`.  The object
whose block sum NBL names (`hBVblocks`); each `blockRem j` feeds `general_BV_alpha_final` with the
block-narrow `blockAlpha` (the later per-block BV pricing, not this node). -/
noncomputable def blockRem (x z y : ℕ) (ε₀ : ℝ) (j Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (Q : ℝ) (Dlev : ℕ) : ℝ :=
  rosserRemainder (blockSwitchSieve x z y ε₀ j Ps hPs hPodd) (Q * Dlev)

open Classical in
/-- **The block-narrow semiprime indicator** `blockAlpha j m = [m = p₁·p₂, ω_j ≤ p₁ < ω_{j+1},
z ≤ p₁ ≤ y < p₂, both prime]` — `semiprimeBlockInd` with the block `p₁`-window filter
`blockIdx z ε₀ p₁ = j` added.  Still `0/1` (unique factorization pins `(p₁,p₂)`), the `m`-side
coefficient `general_BV_alpha_final` consumes for the per-block remainder. -/
noncomputable def blockAlpha (z y : ℕ) (ε₀ : ℝ) (j m : ℕ) : ℂ :=
  if (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧ p₁ * p₂ = m
      ∧ blockIdx z ε₀ p₁ = j) then 1 else 0

/-- **`‖blockAlpha‖ ≤ 1`.**  The block-narrow semiprime indicator is `0/1`-valued — the exact
`hα : ∀ m, ‖α m‖ ≤ 1` hypothesis `general_BV_alpha_final` consumes on the `m`-side. -/
theorem norm_blockAlpha_le_one (z y : ℕ) (ε₀ : ℝ) (j m : ℕ) :
    ‖blockAlpha z y ε₀ j m‖ ≤ 1 := by
  unfold blockAlpha
  split_ifs <;> simp

/-- **`mainA3_of_block_remainders` — the composed CONDITIONAL A₃ bound (the NBL endpoint).**
Bridge (`triplePrimeSum_le_sum_blocks`) + per-block sharp keystone (`block_switch_upper_B`) under
the SINGLE named remainder hypothesis

  `hBVblocks : ∑_j rosserRemainder (blockSwitchSieve j …) (Q·Dlev) ≤ x/(log x)^10`.

**The MAIN TERM is LITERALLY IDENTICAL to SW12's `mainA3_of_hBVswitch`** — the same
`W (switchSieve …)`, the same `maxDepth (switchSieve …)`, the same `tripleSum x z y`: the common
carrier `W·(Fchain N s + slack)` factors out of the `j`-sum (`blockSwitchSieve_W_eq`,
`blockSwitchSieve_maxDepth_eq`) and `∑_j blockTripleSum_j = tripleSum`
(`tripleSum_eq_sum_blockTripleSum`) reassembles.  The ONLY delta versus the monolith is the
remainder side (`hBVswitch → hBVblocks`, per-block CLEAN windows for the later
`general_BV_alpha_final` pricing).  SW4's numeric row is UNCHANGED. -/
theorem mainA3_of_block_remainders (x z y P Ps Dlev : ℕ) (ε₀ ε K Q : ℝ)
    (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hx : 2 ≤ x) (hyx2 : y ≤ x / 2)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P)
    (hD2 : 2 ≤ Dlev) (hQ : 1 ≤ Q)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev)
    (hBVblocks : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          rosserRemainder (blockSwitchSieve x z y ε₀ j Ps hPs hPodd) (Q * Dlev))
        ≤ (x : ℝ) / (Real.log x) ^ 10) :
    triplePrimeSum x P y
      ≤ Real.log x *
          (tripleSum x z y * Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd)
              * (Fchain (maxDepth (switchSieve x z y Ps hPs hPodd)) (logRatio y Dlev)
                + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
            + (x : ℝ) / (Real.log x) ^ 10) := by
  have hlogx : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  set Wswitch := Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd) with hWswitch
  set Ffac := Fchain (maxDepth (switchSieve x z y Ps hPs hPodd)) (logRatio y Dlev)
      + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev) with hFfac
  -- per-block upper bound with W and maxDepth collapsed to the global values (the W-factoring)
  have hblock : ∀ j, (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).siftedSum
      ≤ blockTripleSum x z y ε₀ j * Wswitch * Ffac
        + rosserRemainder (blockSwitchSieve x z y ε₀ j Ps hPs hPodd) (Q * Dlev) := by
    intro j
    have h := block_switch_upper_B x z y ε₀ j Ps Dlev ε K Q hPs hPodd hPy hPlow hD2 hQ hε hw0
      hεsmall hKe h4 hStop
    rwa [blockSwitchSieve_W_eq, blockSwitchSieve_maxDepth_eq, ← hWswitch, ← hFfac] at h
  -- sum the blocks: the carrier factors out, ∑ blockTripleSum reassembles, hBVblocks closes
  have hRHS : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).siftedSum)
      ≤ tripleSum x z y * Wswitch * Ffac + (x : ℝ) / (Real.log x) ^ 10 := by
    have hstep : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).siftedSum)
        ≤ ∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
            (blockTripleSum x z y ε₀ j * Wswitch * Ffac
              + rosserRemainder (blockSwitchSieve x z y ε₀ j Ps hPs hPodd) (Q * Dlev)) :=
      Finset.sum_le_sum (fun j _ => hblock j)
    rw [Finset.sum_add_distrib] at hstep
    have hfac : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          blockTripleSum x z y ε₀ j * Wswitch * Ffac)
        = tripleSum x z y * Wswitch * Ffac := by
      rw [← Finset.sum_mul, ← Finset.sum_mul,
        ← tripleSum_eq_sum_blockTripleSum x z y ε₀ hz hε₀]
    rw [hfac] at hstep
    linarith [hstep, hBVblocks]
  calc triplePrimeSum x P y
      ≤ Real.log x * ∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          (blockSwitchSieve x z y ε₀ j Ps hPs hPodd).siftedSum :=
        triplePrimeSum_le_sum_blocks x z y P Ps ε₀ hz hε₀ hPs hPodd hPy hx hyx2 hPfull
    _ ≤ Real.log x * (tripleSum x z y * Wswitch * Ffac + (x : ℝ) / (Real.log x) ^ 10) :=
        mul_le_mul_of_nonneg_left hRHS hlogx

end Salt.Chen
