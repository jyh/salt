/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.AggCE
import Salt.Goldbach.Density
import Salt.Goldbach.Residue

/-!
# G-SW — the Goldbach switch layer (instances + the sharp keystone), wave W2

Design: `docs/exploration/q1-design.md`, node **G-SW** (D3, gate finding: the `{q ∣ N}` unit
seam VANISHES — `goldPs` excludes `q ∣ N`, so `Coprime N d` is free on every `d ∣ Ps` coprime to
`N`; the Q-level residue is a unit via G-RES's `Coprime Q (N − a)`; the AggCE crumb is N-free).
This file mirrors the twin switch spine (`Salt/Chen/SwitchSieve.lean`, `SwitchW.lean`,
`SwitchBlocks.lean`) under the Goldbach substitution `n + 2 ↦ N − n`: the paired value is `N − n`
(running over the bottom half `[2, N/2]` as `n` sweeps the window `[N/2, N−2] = twinWindow N`),
and the switch congruence `d ∣ n` becomes `prod3 ≡ N (mod d)` (since `n = N − prod3`).

## What is REUSED (strong reuse per the gate)

* `BoundingSieve`/`W`/`maxDepth`/`rosserRemainder`/`Fchain`/`CsharpB`/`hBJS` (mathlib + 2A);
* the density `nuChen = 1/φ` VERBATIM (N-independent — the singular-series invariance);
* the sharp cB upper keystone `twin_A2_per_prime_B` (generic in the `BoundingSieve`) —
  INSTANTIATED, not re-proven;
* the guards `twinA1_hnu`/`twinA1_hguard`, `stepHypWPC_sharpB` (generic in the modulus);
* `prod3`/`blockIdx`/`maxBlock`/`twinWindow` (all N-free — reused verbatim).

## What is NEW (the Goldbach carriers)

* `goldTripleSet`/`goldACount`/`goldTripleSum` — the triple carriers at the reflected fibre
  `prod3 = N − n` and the bottom-half range `2 ≤ prod3 ≤ N/2` (so `N − prod3 ∈ twinWindow N`);
* `goldSwitchSieve`/`goldSwitchSieveW`/`goldBlockSwitchSieve`/`goldBlockSwitchSieveW` — the
  switched sieve instances (support `twinWindow N`, weight `goldACount`, modulus the abstract
  `Ps`, density `nuChen`) — byte-parallel to the twin (`x ↦ N`); the `W`/`maxDepth` transfers
  are `rfl`, exactly as the twin's (no carrier drift);
* `gold_switch_upper_B`/`gold_block_switch_upper_B(_W)` — the sharp keystone at the Goldbach
  instances (verbatim instantiations).

The BV bridge (`prod3 ≡ N (mod d)`, the unit fact `coprime_of_dvd_goldPs`) and the AggCE crumb
live in `Salt/Goldbach/SwitchBV.lean`.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.Chen

namespace Salt.Goldbach

/-! ## Part A — the Goldbach triple carriers (the reflected fibre `prod3 = N − n`) -/

/-- **The Goldbach admissible triple set** `(p₁, p₂, p₃)`: `z ≤ p₁ ≤ y < p₂ ≤ p₃`, all prime,
with product in the *bottom-half* window `[2, N/2]` (so `n = N − prod3` lies in `twinWindow N`).
Mirrors `Salt.Chen.tripleSet` with the twin's top-half range `[x/2+2, x]` reflected to `[2, N/2]`
(the Goldbach paired value runs over the bottom half). -/
def goldTripleSet (N z y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N)).filter
    (fun t => z ≤ t.1 ∧ t.1 ≤ y ∧ y < t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
      t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧
      2 ≤ prod3 t ∧ prod3 t ≤ N / 2)

/-- **The Goldbach switch weight** `aₙ = #{(p₁,p₂,p₃) admissible : p₁p₂p₃ = N − n}` — the fibre
of `goldTripleSet` over `n` at the reflected value `N − n` (mirrors `aCount` at `prod3 = n+2`). -/
noncomputable def goldACount (N z y n : ℕ) : ℝ :=
  (((goldTripleSet N z y).filter (fun t => prod3 t = N - n)).card : ℝ)

/-- **The Goldbach triple count** `∑_{n ∈ twinWindow N} aₙ` (mirrors `tripleSum`). -/
noncomputable def goldTripleSum (N z y : ℕ) : ℝ :=
  ∑ n ∈ Salt.Chen.twinWindow N, goldACount N z y n

/-- `0 ≤ goldACount` — the switch weight is a cast card. -/
lemma goldACount_nonneg (N z y n : ℕ) : 0 ≤ goldACount N z y n := by
  rw [goldACount]; positivity

/-- **The Goldbach Fubini reindex.**  `∑_{n ∈ window} aₙ = #{admissible triples}`: every
admissible triple has `N − prod ∈ twinWindow N` (`prod ∈ [2, N/2] ⟹ N − prod ∈ [N/2, N−2]`), so
the fibres over the window partition `goldTripleSet`.  Mirrors `tripleSum_eq_card`. -/
theorem goldTripleSum_eq_card (N z y : ℕ) :
    goldTripleSum N z y = ((goldTripleSet N z y).card : ℝ) := by
  unfold goldTripleSum goldACount
  rw [← Nat.cast_sum]
  congr 1
  have Hmem : ∀ t ∈ goldTripleSet N z y, N - prod3 t ∈ Salt.Chen.twinWindow N := by
    intro t ht
    rw [goldTripleSet, Finset.mem_filter] at ht
    obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := ht
    rw [twinWindow, Finset.mem_Icc]; omega
  rw [Finset.card_eq_sum_card_fiberwise Hmem]
  refine Finset.sum_congr rfl (fun n _hn => ?_)
  congr 1
  apply Finset.filter_congr
  intro t ht
  rw [goldTripleSet, Finset.mem_filter] at ht
  obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := ht
  constructor <;> (intro h; omega)

/-! ## Part A′ — the narrow-block carriers (`blockIdx` reused verbatim, N-free) -/

/-- **The per-block Goldbach switch weight** `blockACount j n = #{admissible triples in block `j`
with `prod = N − n`}` — `goldACount`'s block-`j` restriction (`blockIdx` reused, N-free). -/
noncomputable def goldBlockACount (N z y : ℕ) (ε₀ : ℝ) (j n : ℕ) : ℝ :=
  (((goldTripleSet N z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧ prod3 t = N - n)).card : ℝ)

/-- `0 ≤ goldBlockACount` — a cast card. -/
lemma goldBlockACount_nonneg (N z y : ℕ) (ε₀ : ℝ) (j n : ℕ) :
    0 ≤ goldBlockACount N z y ε₀ j n := by
  rw [goldBlockACount]; positivity

/-- **The block-`j` Goldbach triple set** — the admissible triples whose `p₁` sits in block `j`. -/
noncomputable def goldBlockTripleSet (N z y : ℕ) (ε₀ : ℝ) (j : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (goldTripleSet N z y).filter (fun t => blockIdx z ε₀ t.1 = j)

/-- **The block-`j` Goldbach triple count** — the block's `totalMass`. -/
noncomputable def goldBlockTripleSum (N z y : ℕ) (ε₀ : ℝ) (j : ℕ) : ℝ :=
  ∑ n ∈ Salt.Chen.twinWindow N, goldBlockACount N z y ε₀ j n

/-- **The block Fubini reindex.**  `goldBlockTripleSum j = #{triples in block j}` (mirrors
`goldTripleSum_eq_card` at the block filter). -/
theorem goldBlockTripleSum_eq_card (N z y : ℕ) (ε₀ : ℝ) (j : ℕ) :
    goldBlockTripleSum N z y ε₀ j = ((goldBlockTripleSet N z y ε₀ j).card : ℝ) := by
  unfold goldBlockTripleSum goldBlockACount goldBlockTripleSet
  rw [← Nat.cast_sum]
  congr 1
  have Hmem : ∀ t ∈ (goldTripleSet N z y).filter (fun t => blockIdx z ε₀ t.1 = j),
      N - prod3 t ∈ Salt.Chen.twinWindow N := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have htri := ht.1
    rw [goldTripleSet, Finset.mem_filter] at htri
    obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := htri
    rw [twinWindow, Finset.mem_Icc]; omega
  rw [Finset.card_eq_sum_card_fiberwise Hmem]
  refine Finset.sum_congr rfl (fun n _hn => ?_)
  rw [Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro t ht
  have htri := ht
  rw [goldTripleSet, Finset.mem_filter] at htri
  obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := htri
  constructor
  · rintro ⟨hb, hp⟩; exact ⟨hb, by omega⟩
  · rintro ⟨hb, hp⟩; exact ⟨hb, by omega⟩

/-- **The block-partition kernel.**  Any predicate-filtered count of `goldTripleSet` partitions
over the narrow `p₁`-blocks `[0, maxBlock N z ε₀]` (every admissible triple has `1 ≤ p₁ ≤ N`, so
`blockIdx z ε₀ p₁ ≤ blockIdx z ε₀ N`).  Mirrors `Salt.Chen.count_eq_sum_block`. -/
private lemma goldCount_eq_sum_block {N z y : ℕ} (ε₀ : ℝ) (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    (P : ℕ × ℕ × ℕ → Prop) [DecidablePred P] :
    (((goldTripleSet N z y).filter P).card : ℝ)
      = ∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
          (((goldTripleSet N z y).filter
              (fun t => blockIdx z ε₀ t.1 = j ∧ P t)).card : ℝ) := by
  classical
  have hmaps : ∀ t ∈ (goldTripleSet N z y).filter P,
      blockIdx z ε₀ t.1 ∈ Finset.range (maxBlock N z ε₀ + 1) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have h1 : t.1 ∈ Finset.Icc 1 N := by
      have := ht.1
      rw [goldTripleSet, Finset.mem_filter] at this
      have := this.1
      rw [Finset.mem_product] at this
      exact this.1
    rw [Finset.mem_Icc] at h1
    rw [Finset.mem_range, Nat.lt_succ_iff, maxBlock]
    exact blockIdx_le_of_le hz hε₀ h1.1 h1.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hfilt : ((goldTripleSet N z y).filter P).filter (fun t => blockIdx z ε₀ t.1 = j)
      = (goldTripleSet N z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ P t) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro t _
    tauto
  rw [hfilt]

/-- **The switch weight partitions over the blocks.**  `goldACount n = ∑_j goldBlockACount j n`. -/
theorem goldACount_eq_sum_blockACount (N z y : ℕ) (ε₀ : ℝ) (hz : 1 ≤ z) (hε₀ : 0 < ε₀) (n : ℕ) :
    goldACount N z y n
      = ∑ j ∈ Finset.range (maxBlock N z ε₀ + 1), goldBlockACount N z y ε₀ j n := by
  unfold goldACount goldBlockACount
  exact goldCount_eq_sum_block ε₀ hz hε₀ (fun t => prod3 t = N - n)

/-- **The triple count partitions over the blocks.**
`goldTripleSum = ∑_j goldBlockTripleSum j`. -/
theorem goldTripleSum_eq_sum_blockTripleSum (N z y : ℕ) (ε₀ : ℝ) (hz : 1 ≤ z) (hε₀ : 0 < ε₀) :
    goldTripleSum N z y
      = ∑ j ∈ Finset.range (maxBlock N z ε₀ + 1), goldBlockTripleSum N z y ε₀ j := by
  unfold goldTripleSum goldBlockTripleSum
  rw [show (∑ n ∈ Salt.Chen.twinWindow N, goldACount N z y n)
        = ∑ n ∈ Salt.Chen.twinWindow N,
            ∑ j ∈ Finset.range (maxBlock N z ε₀ + 1), goldBlockACount N z y ε₀ j n
      from Finset.sum_congr rfl (fun n _ => goldACount_eq_sum_blockACount N z y ε₀ hz hε₀ n)]
  exact Finset.sum_comm

/-! ## Part B — the monolithic switched `BoundingSieve` instance -/

/-- **The Goldbach switched `BoundingSieve`** (the SW12 carrier, `x ↦ N`).  Support = the window
points `n` (the sieve tests `q ∣ n`, i.e. `prod3 ≡ N (mod q)` on the product — the reflected
switch), weight = `goldACount`, `totalMass` = the Goldbach triple count, density `ν = nuChen`
(one residue class), sifting modulus the abstract `Ps` (all prime factors `≥ 3` via `hPodd`; the
caller supplies `goldPs`, whose `Coprime · N` makes the class `N mod d` a unit — SwitchBV). -/
noncomputable def goldSwitchSieve (N z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) : BoundingSieve where
  support := twinWindow N
  prodPrimes := Ps
  prodPrimes_squarefree := hPs
  weights := fun n => goldACount N z y n
  weights_nonneg := fun n => goldACount_nonneg N z y n
  totalMass := goldTripleSum N z y
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _p hp _ => nuChen_pos hp
  nu_lt_one_of_prime := fun p hp hpd =>
    nuChen_lt_one hp (hPodd p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hPs.ne_zero⟩))

section Facts

variable (N z y Ps : ℕ) (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)

@[simp] lemma goldSwitchSieve_support :
    (goldSwitchSieve N z y Ps hPs hPodd).support = twinWindow N := rfl

@[simp] lemma goldSwitchSieve_prodPrimes :
    (goldSwitchSieve N z y Ps hPs hPodd).prodPrimes = Ps := rfl

@[simp] lemma goldSwitchSieve_nu : (goldSwitchSieve N z y Ps hPs hPodd).nu = nuChen := rfl

@[simp] lemma goldSwitchSieve_totalMass :
    (goldSwitchSieve N z y Ps hPs hPodd).totalMass = goldTripleSum N z y := rfl

/-- **`multSum d`** — the window triple-mass in the divisibility class `d ∣ n`. -/
lemma goldSwitchSieve_multSum (d : ℕ) :
    (goldSwitchSieve N z y Ps hPs hPodd).multSum d
      = ∑ n ∈ twinWindow N, if d ∣ n then goldACount N z y n else 0 := rfl

/-- **`siftedSum`** — the `goldACount`-weighted count of window points `n` coprime to `Ps`. -/
lemma goldSwitchSieve_siftedSum :
    (goldSwitchSieve N z y Ps hPs hPodd).siftedSum
      = ∑ n ∈ twinWindow N, if Nat.Coprime Ps n then goldACount N z y n else 0 := rfl

/-- **`rem d`** — the switched AP-remainder `rem d = multSum d − ν(d)·totalMass`. -/
lemma goldSwitchSieve_rem (d : ℕ) :
    (goldSwitchSieve N z y Ps hPs hPodd).rem d
      = (∑ n ∈ twinWindow N, if d ∣ n then goldACount N z y n else 0)
        - nuChen d * goldTripleSum N z y := rfl

/-- `0 ≤ totalMass` — the triple count is a cast card. -/
lemma goldSwitch_totalMass_nonneg : 0 ≤ (goldSwitchSieve N z y Ps hPs hPodd).totalMass := by
  rw [goldSwitchSieve_totalMass, goldTripleSum_eq_card]; positivity

end Facts

/-! ## Part C — the sieve-class side conditions and the sharp cB upper keystone -/

/-- **`hnu`** — `ν(q) ≤ 1/(q−1)` at every sifting prime (the same `nuChen`, so `twinA1_hnu`
transfers verbatim). -/
lemma gold_switch_hnu (Ps : ℕ) : ∀ q ∈ Ps.primeFactors, nuChen q ≤ 1 / ((q : ℝ) - 1) :=
  twinA1_hnu Ps

/-- **`hguard`** — the hypothesis-(4) threshold guard at every sifting prime, from the ℚ-window
floor `q ≥ w₀(ε)` (the `twinA1_hguard` route; the guard is generic in the modulus). -/
lemma gold_switch_hguard {Ps : ℕ} {ε : ℝ} (hε : 0 < ε) (hw0 : 3 ≤ w0R ε)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ)) :
    ∀ q ∈ Ps.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
  twinA1_hguard hε hw0 hPodd hPlow

/-- **`gold_switch_upper_B` — the sharp (cB) upper linear sieve at the Goldbach switched
instance.**  A verbatim instantiation of `switch_upper_B`: `twin_A2_per_prime_B` is generic in
the `BoundingSieve`, the guards are Ps-based, and `totalMass ≥ 0` is `goldSwitch_totalMass_nonneg`.
Conclusion (`totalMass` unfolded to `goldTripleSum`). -/
theorem gold_switch_upper_B (N z y Ps Dlev : ℕ) (ε K Q : ℝ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hD2 : 2 ≤ Dlev) (hQ : 1 ≤ Q)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev) :
    (goldSwitchSieve N z y Ps hPs hPodd).siftedSum
      ≤ (goldTripleSum N z y * Salt.BrunLower.W (goldSwitchSieve N z y Ps hPs hPodd))
          * (Fchain (maxDepth (goldSwitchSieve N z y Ps hPs hPodd)) (logRatio y Dlev)
              + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
        + rosserRemainder (goldSwitchSieve N z y Ps hPs hPodd) (Q * Dlev) := by
  set s := goldSwitchSieve N z y Ps hPs hPodd with hs
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < y := hPy
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    gold_switch_hguard hε hw0 hPodd hPlow
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := gold_switch_hnu Ps
  have htm : 0 ≤ s.totalMass := goldSwitch_totalMass_nonneg N z y Ps hPs hPodd
  have h := twin_A2_per_prime_B s y Dlev ε K Q hD2 htm hQ hzTop hguard hnu hε.le
    (lt_of_le_of_lt hεsmall (by norm_num)) hKe (stepHypWPC_sharpB ε hε.le hεsmall) h4 hStop
  have htm_eq : s.totalMass = goldTripleSum N z y := rfl
  rw [← htm_eq]
  exact h

/-! ## Part D — the W- and block-restricted instances + the `rfl` W-factoring -/

/-- **The W-switched Goldbach `BoundingSieve`** — `goldSwitchSieve` with the support restricted
to the residue class `n ≡ a (mod Q)` and the SMOOTH `totalMass = goldTripleSum / φ(Q)`.
`weights`/`prodPrimes`/`nu` are UNCHANGED (the AP density cancels in the ν-ratio). -/
noncomputable def goldSwitchSieveW (N z y Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) : BoundingSieve where
  support := (twinWindow N).filter (fun n => n % Q = a % Q)
  prodPrimes := Ps
  prodPrimes_squarefree := hPs
  weights := fun n => goldACount N z y n
  weights_nonneg := fun n => goldACount_nonneg N z y n
  totalMass := goldTripleSum N z y / (Q.totient : ℝ)
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _p hp _ => nuChen_pos hp
  nu_lt_one_of_prime := fun p hp hpd =>
    nuChen_lt_one hp (hPodd p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hPs.ne_zero⟩))

/-- **The per-block switched Goldbach `BoundingSieve`** — `goldSwitchSieve` with the block
`p₁`-filter (`goldBlockACount`), block `totalMass = goldBlockTripleSum j`.  `prodPrimes`/`nu`
block-independent (the W-factoring premise). -/
noncomputable def goldBlockSwitchSieve (N z y : ℕ) (ε₀ : ℝ) (j Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) : BoundingSieve where
  support := twinWindow N
  prodPrimes := Ps
  prodPrimes_squarefree := hPs
  weights := fun n => goldBlockACount N z y ε₀ j n
  weights_nonneg := fun n => goldBlockACount_nonneg N z y ε₀ j n
  totalMass := goldBlockTripleSum N z y ε₀ j
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _p hp _ => nuChen_pos hp
  nu_lt_one_of_prime := fun p hp hpd =>
    nuChen_lt_one hp (hPodd p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hPs.ne_zero⟩))

/-- **The per-block W-switched Goldbach `BoundingSieve`** — `goldBlockSwitchSieve`
AP-restricted, smooth block `totalMass = goldBlockTripleSum j / φ(Q)`. -/
noncomputable def goldBlockSwitchSieveW (N z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) : BoundingSieve where
  support := (twinWindow N).filter (fun n => n % Q = a % Q)
  prodPrimes := Ps
  prodPrimes_squarefree := hPs
  weights := fun n => goldBlockACount N z y ε₀ j n
  weights_nonneg := fun n => goldBlockACount_nonneg N z y ε₀ j n
  totalMass := goldBlockTripleSum N z y ε₀ j / (Q.totient : ℝ)
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _p hp _ => nuChen_pos hp
  nu_lt_one_of_prime := fun p hp hpd =>
    nuChen_lt_one hp (hPodd p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hPs.ne_zero⟩))

section WBlockFacts

variable (N z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ) (hPs : Squarefree Ps)
  (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)

@[simp] lemma goldSwitchSieveW_support :
    (goldSwitchSieveW N z y Q a Ps hPs hPodd).support
      = (twinWindow N).filter (fun n => n % Q = a % Q) := rfl

@[simp] lemma goldSwitchSieveW_prodPrimes :
    (goldSwitchSieveW N z y Q a Ps hPs hPodd).prodPrimes = Ps := rfl

@[simp] lemma goldSwitchSieveW_nu :
    (goldSwitchSieveW N z y Q a Ps hPs hPodd).nu = nuChen := rfl

@[simp] lemma goldSwitchSieveW_totalMass :
    (goldSwitchSieveW N z y Q a Ps hPs hPodd).totalMass
      = goldTripleSum N z y / (Q.totient : ℝ) := rfl

lemma goldSwitchSieveW_siftedSum :
    (goldSwitchSieveW N z y Q a Ps hPs hPodd).siftedSum
      = ∑ n ∈ (twinWindow N).filter (fun n => n % Q = a % Q),
          if Nat.Coprime Ps n then goldACount N z y n else 0 := rfl

@[simp] lemma goldBlockSwitchSieve_support :
    (goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd).support = twinWindow N := rfl

@[simp] lemma goldBlockSwitchSieve_prodPrimes :
    (goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd).prodPrimes = Ps := rfl

@[simp] lemma goldBlockSwitchSieve_nu :
    (goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd).nu = nuChen := rfl

@[simp] lemma goldBlockSwitchSieve_totalMass :
    (goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd).totalMass
      = goldBlockTripleSum N z y ε₀ j := rfl

lemma goldBlockSwitchSieve_siftedSum :
    (goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd).siftedSum
      = ∑ n ∈ twinWindow N,
          if Nat.Coprime Ps n then goldBlockACount N z y ε₀ j n else 0 := rfl

@[simp] lemma goldBlockSwitchSieveW_support :
    (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).support
      = (twinWindow N).filter (fun n => n % Q = a % Q) := rfl

@[simp] lemma goldBlockSwitchSieveW_prodPrimes :
    (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).prodPrimes = Ps := rfl

@[simp] lemma goldBlockSwitchSieveW_nu :
    (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).nu = nuChen := rfl

@[simp] lemma goldBlockSwitchSieveW_totalMass :
    (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).totalMass
      = goldBlockTripleSum N z y ε₀ j / (Q.totient : ℝ) := rfl

lemma goldBlockSwitchSieveW_multSum (d : ℕ) :
    (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).multSum d
      = ∑ n ∈ (twinWindow N).filter (fun n => n % Q = a % Q),
          if d ∣ n then goldBlockACount N z y ε₀ j n else 0 := rfl

lemma goldBlockSwitchSieveW_siftedSum :
    (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).siftedSum
      = ∑ n ∈ (twinWindow N).filter (fun n => n % Q = a % Q),
          if Nat.Coprime Ps n then goldBlockACount N z y ε₀ j n else 0 := rfl

/-- `0 ≤ totalMass` for the block W-instance. -/
lemma goldBlockW_totalMass_nonneg :
    0 ≤ (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).totalMass := by
  rw [goldBlockSwitchSieveW_totalMass]
  refine div_nonneg ?_ (by positivity)
  rw [goldBlockTripleSum_eq_card]; positivity

/-- `0 ≤ totalMass` for the block instance. -/
lemma goldBlock_totalMass_nonneg :
    0 ≤ (goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd).totalMass := by
  rw [goldBlockSwitchSieve_totalMass, goldBlockTripleSum_eq_card]; positivity

end WBlockFacts

/-! ### The `rfl` W-factoring: `W`/`maxDepth` are block- AND Q-independent -/

/-- **★ THE W-FACTORING at the W-instance (density product).**  `rfl` — `W` sees only
`prodPrimes = Ps`, `nu = nuChen`. -/
lemma goldSwitchSieveW_W_eq (N z y Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    Salt.BrunLower.W (goldSwitchSieveW N z y Q a Ps hPs hPodd)
      = Salt.BrunLower.W (goldSwitchSieve N z y Ps hPs hPodd) := rfl

/-- **★ THE W-FACTORING at the W-instance (sieve depth).**  `rfl`. -/
lemma goldSwitchSieveW_maxDepth_eq (N z y Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    maxDepth (goldSwitchSieveW N z y Q a Ps hPs hPodd)
      = maxDepth (goldSwitchSieve N z y Ps hPs hPodd) := rfl

/-- **★ THE W-FACTORING, per block (density product).**  `rfl` for every block `j`. -/
lemma goldBlockSwitchSieve_W_eq (N z y : ℕ) (ε₀ : ℝ) (j Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    Salt.BrunLower.W (goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd)
      = Salt.BrunLower.W (goldSwitchSieve N z y Ps hPs hPodd) := rfl

/-- **★ THE W-FACTORING, per block (sieve depth).**  `rfl`. -/
lemma goldBlockSwitchSieve_maxDepth_eq (N z y : ℕ) (ε₀ : ℝ) (j Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    maxDepth (goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd)
      = maxDepth (goldSwitchSieve N z y Ps hPs hPodd) := rfl

/-- **★ THE W-FACTORING, per W-block (density product).**  `rfl`. -/
lemma goldBlockSwitchSieveW_W_eq (N z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    Salt.BrunLower.W (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd)
      = Salt.BrunLower.W (goldSwitchSieve N z y Ps hPs hPodd) := rfl

/-- **★ THE W-FACTORING, per W-block (sieve depth).**  `rfl`. -/
lemma goldBlockSwitchSieveW_maxDepth_eq (N z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    maxDepth (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd)
      = maxDepth (goldSwitchSieve N z y Ps hPs hPodd) := rfl

/-! ## Part E — the per-block sharp keystones (verbatim instantiations) -/

/-- **`gold_block_switch_upper_B` — the sharp (cB) upper linear sieve, per block.**  A verbatim
re-instantiation of `gold_switch_upper_B` at `sp0 = goldBlockSwitchSieve j`
(`twin_A2_per_prime_B` is generic in the `BoundingSieve`). -/
theorem gold_block_switch_upper_B (N z y : ℕ) (ε₀ : ℝ) (j Ps Dlev : ℕ) (ε K Q : ℝ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hD2 : 2 ≤ Dlev) (hQ : 1 ≤ Q)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev) :
    (goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd).siftedSum
      ≤ (goldBlockTripleSum N z y ε₀ j
            * Salt.BrunLower.W (goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd))
          * (Fchain (maxDepth (goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd)) (logRatio y Dlev)
              + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
        + rosserRemainder (goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd) (Q * Dlev) := by
  set s := goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd with hs
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < y := hPy
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    gold_switch_hguard hε hw0 hPodd hPlow
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := gold_switch_hnu Ps
  have htm : 0 ≤ s.totalMass := goldBlock_totalMass_nonneg N z y ε₀ j Ps hPs hPodd
  have h := twin_A2_per_prime_B s y Dlev ε K Q hD2 htm hQ hzTop hguard hnu hε.le
    (lt_of_le_of_lt hεsmall (by norm_num)) hKe (stepHypWPC_sharpB ε hε.le hεsmall) h4 hStop
  have htm_eq : s.totalMass = goldBlockTripleSum N z y ε₀ j := rfl
  rw [← htm_eq]
  exact h

/-- **`gold_block_switch_upper_B_W` — the sharp keystone at the W-block instance.**  Verbatim,
with `totalMass = goldBlockTripleSum j / φ(Q)`. -/
theorem gold_block_switch_upper_B_W (N z y : ℕ) (ε₀ : ℝ) (j Q a Ps Dlev : ℕ) (ε K QR : ℝ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hD2 : 2 ≤ Dlev) (hQR : 1 ≤ QR)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev) :
    (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).siftedSum
      ≤ (goldBlockTripleSum N z y ε₀ j / (Q.totient : ℝ)
            * Salt.BrunLower.W (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd))
          * (Fchain (maxDepth (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd))
                (logRatio y Dlev)
              + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
        + rosserRemainder (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd) (QR * Dlev) := by
  set s := goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd with hs
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < y := hPy
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    gold_switch_hguard hε hw0 hPodd hPlow
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := gold_switch_hnu Ps
  have htm : 0 ≤ s.totalMass := goldBlockW_totalMass_nonneg N z y ε₀ j Q a Ps hPs hPodd
  have h := twin_A2_per_prime_B s y Dlev ε K QR hD2 htm hQR hzTop hguard hnu hε.le
    (lt_of_le_of_lt hεsmall (by norm_num)) hKe (stepHypWPC_sharpB ε hε.le hεsmall) h4 hStop
  have htm_eq : s.totalMass = goldBlockTripleSum N z y ε₀ j / (Q.totient : ℝ) := rfl
  rw [← htm_eq]
  exact h

/-! ## Part F — the sifted-sum block splits + the composed A₃ hooks

The Goldbach A₃ Λ-carrier (the analogue of `triplePrimeSum`/`keepR`, and the survivor bridge
`triplePrimeSum_le_sifted`) lives in the Goldbach ASSEMBLY (node **G-ASM**, wave W4).  So the
composed `mainA3` bounds are stated here **hypothesis-parametrized over the Λ-bridge**
(`hbridge`), giving G-ASM the exact one-line plug: it supplies the bridge, this file supplies the
sharp-keystone upper bound + the block reassembly. -/

/-- **The switch sifted sum splits over the blocks.**  Mirrors
`switch_siftedSum_eq_sum_blocks`. -/
lemma gold_switch_siftedSum_eq_sum_blocks (N z y : ℕ) (ε₀ : ℝ) (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    (Ps : ℕ) (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    (goldSwitchSieve N z y Ps hPs hPodd).siftedSum
      = ∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
          (goldBlockSwitchSieve N z y ε₀ j Ps hPs hPodd).siftedSum := by
  rw [goldSwitchSieve_siftedSum]
  have hterm : ∀ n ∈ twinWindow N, (if Nat.Coprime Ps n then goldACount N z y n else 0)
      = ∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
          (if Nat.Coprime Ps n then goldBlockACount N z y ε₀ j n else 0) := by
    intro n _
    by_cases hcop : Nat.Coprime Ps n
    · simp only [if_pos hcop]
      exact goldACount_eq_sum_blockACount N z y ε₀ hz hε₀ n
    · simp only [if_neg hcop, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [goldBlockSwitchSieve_siftedSum]

/-- **The W-switch sifted sum splits over the blocks.**  Mirrors
`switchSieveW_siftedSum_eq_sum_blocks`. -/
lemma goldSwitchSieveW_siftedSum_eq_sum_blocks (N z y : ℕ) (ε₀ : ℝ) (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    (Q a Ps : ℕ) (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    (goldSwitchSieveW N z y Q a Ps hPs hPodd).siftedSum
      = ∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
          (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).siftedSum := by
  rw [goldSwitchSieveW_siftedSum]
  have hterm : ∀ n ∈ (twinWindow N).filter (fun n => n % Q = a % Q),
      (if Nat.Coprime Ps n then goldACount N z y n else 0)
        = ∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
            (if Nat.Coprime Ps n then goldBlockACount N z y ε₀ j n else 0) := by
    intro n _
    by_cases hcop : Nat.Coprime Ps n
    · simp only [if_pos hcop]
      exact goldACount_eq_sum_blockACount N z y ε₀ hz hε₀ n
    · simp only [if_neg hcop, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [goldBlockSwitchSieveW_siftedSum]

/-- **`gold_mainA3_of_hBVswitch` — the composed CONDITIONAL A₃ bound (the SW12 endpoint), the
Λ-bridge abstracted.**  Given the Goldbach survivor bridge `hbridge : LHS ≤ log N ·
(goldSwitchSieve …).siftedSum` (G-ASM supplies it at `LHS = goldTriplePrimeSum …`) and the NAMED
remainder bound `hBVswitch`, the sharp keystone folds to the exact `mainA3`-shape.  Mirrors
`mainA3_of_hBVswitch` (the `x ↦ N` carrier). -/
theorem gold_mainA3_of_hBVswitch (N z y Ps Dlev : ℕ) (ε K Q LHS : ℝ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hD2 : 2 ≤ Dlev) (hQ : 1 ≤ Q)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev)
    (hbridge : LHS ≤ Real.log N * (goldSwitchSieve N z y Ps hPs hPodd).siftedSum)
    (hBVswitch : rosserRemainder (goldSwitchSieve N z y Ps hPs hPodd) (Q * Dlev)
        ≤ (N : ℝ) / (Real.log N) ^ 10) :
    LHS
      ≤ Real.log N *
          (goldTripleSum N z y * Salt.BrunLower.W (goldSwitchSieve N z y Ps hPs hPodd)
              * (Fchain (maxDepth (goldSwitchSieve N z y Ps hPs hPodd)) (logRatio y Dlev)
                + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
            + (N : ℝ) / (Real.log N) ^ 10) := by
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hupper := gold_switch_upper_B N z y Ps Dlev ε K Q hPs hPodd hPy hPlow hD2 hQ hε hw0
    hεsmall hKe h4 hStop
  have hsift : (goldSwitchSieve N z y Ps hPs hPodd).siftedSum
      ≤ goldTripleSum N z y * Salt.BrunLower.W (goldSwitchSieve N z y Ps hPs hPodd)
          * (Fchain (maxDepth (goldSwitchSieve N z y Ps hPs hPodd)) (logRatio y Dlev)
            + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
        + (N : ℝ) / (Real.log N) ^ 10 := by linarith [hupper, hBVswitch]
  calc LHS
      ≤ Real.log N * (goldSwitchSieve N z y Ps hPs hPodd).siftedSum := hbridge
    _ ≤ Real.log N *
          (goldTripleSum N z y * Salt.BrunLower.W (goldSwitchSieve N z y Ps hPs hPodd)
              * (Fchain (maxDepth (goldSwitchSieve N z y Ps hPs hPodd)) (logRatio y Dlev)
                + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
            + (N : ℝ) / (Real.log N) ^ 10) := mul_le_mul_of_nonneg_left hsift hlogN

end Salt.Goldbach
