/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SqrtDFold

/-!
# A3W — the W-switch instances + the A₃ supplier mirror (H-AMENDMENT 2, D2/D3)

Design: `docs/blueprints/chen.md`, "H-AMENDMENT 2" (D1–D8) + "GATE RESULT" (C3 smooth
`totalMass`, C4 residue-function generalization); `docs/blueprints/flags.md`, the W-SURG and
H4C entries.  This file lands the A₃ half of the W-trick repair of catch #65: the switched
sieve instances restricted to the residue class `n ≡ a (mod Q)` (`Q = ∏_{p<w₀} p` at
instantiation, `a = Q − 1`), and the supplier mirror bounding Assembly's W-carrier
`triplePrimeSumW`.

## Part A — the W-instances (D2, C3)

`switchSieveW`/`blockSwitchSieveW` mirror SW12's `switchSieve` / NBL's `blockSwitchSieve` with

* **support** = `(twinWindow x).filter (n % Q = a % Q)` — the AP-restricted window points;
* **weights / prodPrimes / nu** UNCHANGED (`aCount`/`blockACount`, `Ps`, `nuChen`) — the AP
  density cancels in the ν-ratio (D2), so the dimension-1 density survives;
* **totalMass** = the SMOOTH convention (C3): `tripleSum x z y / φ(Q)` (blocks:
  `blockTripleSum j / φ(Q)`) — `rem d` is then EXACTLY the `Q·d`-discrepancy (Part C).

**The W-factoring survives verbatim**: `W`/`maxDepth` see only `prodPrimes`/`nu`, which are
shared with the LANDED monolith — `W (blockSwitchSieveW j) = W (switchSieve)` and
`maxDepth (blockSwitchSieveW j) = maxDepth (switchSieve)` **by `rfl`** (block- AND
Q-independence), so the keystone main term is byte-identical to the landed one at the AP
scale `tripleSum/φ(Q)`.

## Part B — the bridge + the per-block keystone + `mainA3_of_block_remainders_W`

`triplePrimeSumW_le_sifted` mirrors SW12's bridge at `keepW` (via `aCount_ge_one_of_W`, the
split sifting bridge `hQfull`/`hPfull'`/`hQa2` replacing the torn `hPfull` — catch #65);
`block_switch_upper_B_W` re-instantiates the sharp cB keystone (`twin_A2_per_prime_B`, generic
in the instance; `h4` in the H4C-conditioned form) at `blockSwitchSieveW`;
`mainA3_of_block_remainders_W` composes them under the single named slot

  `hBVblocksW : ∑_j rosserRemainder (blockSwitchSieveW j …) (QR·Dlev) ≤ x/(log x)^10`

with conclusion at the AP scale: `triplePrimeSumW Q a x P y ≤ log x ·
(tripleSum/φ(Q) · W · (Fchain N s + ε·CsharpB ε·e²·hBJS s) + x/(log x)^10)`.

## Part C — the remainder identification (D3): `rem_W d` is the `Q·d`-discrepancy

The support membership `n ≡ a (Q) ∧ d ∣ n` folds (CRT, `gcd(Q, d) = 1`) into the SINGLE
class `n + 2 ≡ c (mod Q·d)` at `c = crtClassW Q d a` — the class combining `a + 2 (mod Q)`
and `2 (mod d)`.  Hence `multSum_W d` counts the block triples with
`prod3 ≡ c (mod Q·d)` (`blockMultSumW_eq_apCount`), and — because the smooth `totalMass`
satisfies `ν(d)·tripleSum/φ(Q) = ν(Q·d)·tripleSum` (multiplicativity, `gcd(Q, d) = 1`) —
`rem_W d` splits EXACTLY as the landed `blockSwitchSieve_rem_split` at modulus `Q·d`:

  `rem_W d = (blockResCountM (Q·d) c − ν(Q·d)·blockUnitCountM (Q·d)) − ν(Q·d)·blockNonUnitCountM`.

`crtClassW_coprime` gives `gcd(c, Q·d) = 1` from `gcd(a+2, Q) = 1` (`residue_witness` at
`a = Q − 1`) and `d` odd (`switch_dvd_coprime_two`) — the `hr` input of the residue-function
generalized (C4) windowed chain, at the Q-SHIFTED family `Dset = {Q·d : d ∣ Ps, d < QR·Dlev}`
and residue function `r (Q·d) := crtClassW Q d a`.

## Part D — the discharge bridge (the `hBVblocksW` slot)

`hBVblocksW_of_generalBV` mirrors `BlockPricing.hBVblocks_of_generalBV`: the W block
remainders reduce (triangle) to the summed W honest discrepancies `|blockHonestDiscW|` plus
the W conversion errors, closed by the named `hHD_W`/`hCE_W`/`hNum` rows.  The composition
`example` lands the chain character-for-character in `mainA3_of_block_remainders_W`'s slot.
The box-level pricing of `|blockHonestDiscW|` is the C4-generalized windowed chain
(`blockBox_windowDisc_eq_res` at `d := Q·d'`, `R₀ := crtClassW Q d' a` identifies the box
pieces; `medium_survivor_price_sqrtD`/`general_BV_cutoff_sqrtD` price them at the shifted
moduli) — its named threshold rows are GLU-2W obligations, documented at the end of the file.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]`).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the W-switch `BoundingSieve` instances (D2, C3 smooth totalMass) -/

/-- **The W-switched `BoundingSieve`** (H-AMENDMENT 2 D2).  `switchSieve` with the support
restricted to the residue class `n ≡ a (mod Q)` and the SMOOTH `totalMass` convention (C3):
`tripleSum x z y / φ(Q)`.  `weights`/`prodPrimes`/`nu` are UNCHANGED — the AP density cancels
in the ν-ratio, and `rem d` becomes exactly the `Q·d`-discrepancy (Part C). -/
noncomputable def switchSieveW (x z y Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) : BoundingSieve where
  support := (twinWindow x).filter (fun n => n % Q = a % Q)
  prodPrimes := Ps
  prodPrimes_squarefree := hPs
  weights := fun n => aCount x z y n
  weights_nonneg := fun n => aCount_nonneg x z y n
  totalMass := tripleSum x z y / (Q.totient : ℝ)
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _p hp _ => nuChen_pos hp
  nu_lt_one_of_prime := fun p hp hpd =>
    nuChen_lt_one hp (hPodd p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hPs.ne_zero⟩))

/-- **The per-block W-switched `BoundingSieve`** — `blockSwitchSieve` AP-restricted, smooth
block `totalMass = blockTripleSum j / φ(Q)`.  `prodPrimes`/`nu` block- AND Q-independent. -/
noncomputable def blockSwitchSieveW (x z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) : BoundingSieve where
  support := (twinWindow x).filter (fun n => n % Q = a % Q)
  prodPrimes := Ps
  prodPrimes_squarefree := hPs
  weights := fun n => blockACount x z y ε₀ j n
  weights_nonneg := fun n => blockACount_nonneg x z y ε₀ j n
  totalMass := blockTripleSum x z y ε₀ j / (Q.totient : ℝ)
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _p hp _ => nuChen_pos hp
  nu_lt_one_of_prime := fun p hp hpd =>
    nuChen_lt_one hp (hPodd p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hPs.ne_zero⟩))

section WFacts

variable (x z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ) (hPs : Squarefree Ps)
  (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)

@[simp] lemma switchSieveW_support :
    (switchSieveW x z y Q a Ps hPs hPodd).support
      = (twinWindow x).filter (fun n => n % Q = a % Q) := rfl

@[simp] lemma switchSieveW_prodPrimes :
    (switchSieveW x z y Q a Ps hPs hPodd).prodPrimes = Ps := rfl

@[simp] lemma switchSieveW_nu : (switchSieveW x z y Q a Ps hPs hPodd).nu = nuChen := rfl

@[simp] lemma switchSieveW_totalMass :
    (switchSieveW x z y Q a Ps hPs hPodd).totalMass
      = tripleSum x z y / (Q.totient : ℝ) := rfl

lemma switchSieveW_siftedSum :
    (switchSieveW x z y Q a Ps hPs hPodd).siftedSum
      = ∑ n ∈ (twinWindow x).filter (fun n => n % Q = a % Q),
          if Nat.Coprime Ps n then aCount x z y n else 0 := rfl

@[simp] lemma blockSwitchSieveW_support :
    (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).support
      = (twinWindow x).filter (fun n => n % Q = a % Q) := rfl

@[simp] lemma blockSwitchSieveW_prodPrimes :
    (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).prodPrimes = Ps := rfl

@[simp] lemma blockSwitchSieveW_nu :
    (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).nu = nuChen := rfl

@[simp] lemma blockSwitchSieveW_totalMass :
    (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).totalMass
      = blockTripleSum x z y ε₀ j / (Q.totient : ℝ) := rfl

lemma blockSwitchSieveW_siftedSum :
    (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).siftedSum
      = ∑ n ∈ (twinWindow x).filter (fun n => n % Q = a % Q),
          if Nat.Coprime Ps n then blockACount x z y ε₀ j n else 0 := rfl

/-- **`multSum_W d`** — the AP-restricted window triple-mass with `d ∣ n`; by `rfl`. -/
lemma blockSwitchSieveW_multSum (d : ℕ) :
    (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).multSum d
      = ∑ n ∈ (twinWindow x).filter (fun n => n % Q = a % Q),
          if d ∣ n then blockACount x z y ε₀ j n else 0 := rfl

/-- `0 ≤ totalMass` for the block W-instance — a cast card over a nonnegative totient. -/
lemma blockW_totalMass_nonneg :
    0 ≤ (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).totalMass := by
  rw [blockSwitchSieveW_totalMass]
  refine div_nonneg ?_ (by positivity)
  rw [blockTripleSum_eq_card]; positivity

end WFacts

/-! ### The W-factoring mirrors (rfl-level): `W`/`maxDepth` are block- AND Q-independent -/

/-- **★ THE W-FACTORING at the W-instance (density product).**  `W (switchSieveW …) =
W (switchSieve …)` BY `rfl`: `W` sees only `prodPrimes = Ps`, `nu = nuChen` — the AP filter
touches only `support`/`totalMass`. -/
lemma switchSieveW_W_eq (x z y Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    Salt.BrunLower.W (switchSieveW x z y Q a Ps hPs hPodd)
      = Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd) := rfl

/-- **★ THE W-FACTORING at the W-instance (sieve depth).**  By `rfl`. -/
lemma switchSieveW_maxDepth_eq (x z y Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    maxDepth (switchSieveW x z y Q a Ps hPs hPodd)
      = maxDepth (switchSieve x z y Ps hPs hPodd) := rfl

/-- **★ THE W-FACTORING, per block (density product).**  `W (blockSwitchSieveW j) =
W (switchSieve)` for EVERY block `j` and EVERY `(Q, a)`, by `rfl` — the common carrier
factors out of the `j`-sum exactly as in the landed NBL route. -/
lemma blockSwitchSieveW_W_eq (x z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    Salt.BrunLower.W (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd)
      = Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd) := rfl

/-- **★ THE W-FACTORING, per block (sieve depth).**  By `rfl`. -/
lemma blockSwitchSieveW_maxDepth_eq (x z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    maxDepth (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd)
      = maxDepth (switchSieve x z y Ps hPs hPodd) := rfl

/-! ## Part B — the W-bridge, the per-block keystone, and the composed A₃ supplier -/

/-- **`triplePrimeSumW_le_sifted` — THE W-BRIDGE.**  The AP-restricted A₃ Λ-carrier
(Assembly's `triplePrimeSumW`) is dominated by `log x ·` the W-switched sifted sum: a window
point with positive `Λ·keepW·tripleT` mass is prime, AP-restricted (hence in the W-support),
`n + 2 = p₁p₂p₃` is an ADMISSIBLE triple (`aCount ≥ 1` via `aCount_ge_one_of_W` — the SPLIT
sifting bridge `hQfull`/`hPfull'`/`hQa2` supplies `z ≤ p₁`, catch #65's repair), and `n`
survives the switch sieve (`n` prime `≥ x/2 ≥ y >` every sifting prime).  Mirrors
`triplePrimeSum_le_sifted`. -/
theorem triplePrimeSumW_le_sifted (x z y P Q a w' Ps : ℕ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hx : 2 ≤ x) (hyx2 : y ≤ x / 2)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Q (a + 2)) :
    triplePrimeSumW Q a x P y
      ≤ Real.log x * (switchSieveW x z y Q a Ps hPs hPodd).siftedSum := by
  have hlogx : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  have hRHSnn : ∀ n : ℕ, (0 : ℝ)
      ≤ (if n % Q = a % Q then (if Nat.Coprime Ps n then aCount x z y n else 0) else 0) := by
    intro n
    split_ifs
    · exact aCount_nonneg x z y n
    · exact le_refl 0
    · exact le_refl 0
  rw [triplePrimeSumW, switchSieveW_siftedSum, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hk : Nat.Prime n ∧ Nat.Coprime P (n + 2) ∧ n % Q = a % Q
  · by_cases htp : TripleP y (n + 2)
    · -- the survivor case: keepW = 1, tripleT = 1, n coprime to Ps, aCount ≥ 1
      have hnmem := hn
      rw [twinWindow, Finset.mem_Icc] at hnmem
      have hkeep1 : keepW Q a P n = 1 := keepW_eq_one_iff.mpr hk
      have htT : tripleT y (n + 2) = 1 := tripleT_eq_one htp
      have hyn : y ≤ n := le_trans hyx2 hnmem.1
      have hcop : Nat.Coprime Ps n := by
        rw [Nat.coprime_comm]
        refine (hk.1.coprime_iff_not_dvd).mpr fun hdvd => ?_
        have hmem : n ∈ Ps.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hk.1, hdvd, hPs.ne_zero⟩
        exact absurd (hPy n hmem) (by omega)
      have hn1 : 1 ≤ n := hk.1.one_lt.le
      have hnx : n ≤ x := by omega
      have hΛle : vonMangoldt n ≤ Real.log x := by
        refine le_trans vonMangoldt_le_log (Real.log_le_log ?_ ?_)
        · exact_mod_cast hn1
        · exact_mod_cast hnx
      have hge1 : (1 : ℝ) ≤ aCount x z y n :=
        aCount_ge_one_of_W hx hn hk hQfull hPfull' hQa2 htp
      rw [hkeep1, htT, mul_one, mul_one, if_pos hk.2.2, if_pos hcop]
      calc vonMangoldt n ≤ Real.log x := hΛle
        _ = Real.log x * 1 := (mul_one _).symm
        _ ≤ Real.log x * aCount x z y n := mul_le_mul_of_nonneg_left hge1 hlogx
    · -- no triple pattern: LHS term vanishes
      have h0 : tripleT y (n + 2) = 0 := by unfold tripleT; rw [if_neg htp]
      rw [h0, mul_zero]
      exact mul_nonneg hlogx (hRHSnn n)
  · -- not kept: LHS term vanishes
    have hkeep0 : keepW Q a P n = 0 := by unfold keepW; rw [if_neg hk]
    rw [hkeep0, mul_zero, zero_mul]
    exact mul_nonneg hlogx (hRHSnn n)

/-- **The W-switch sifted sum splits over the blocks.**  Mirrors
`switch_siftedSum_eq_sum_blocks`: push the coprimality indicator through
`aCount = ∑_j blockACount` on the AP-restricted support and swap the sums. -/
lemma switchSieveW_siftedSum_eq_sum_blocks (x z y : ℕ) (ε₀ : ℝ) (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    (Q a Ps : ℕ) (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    (switchSieveW x z y Q a Ps hPs hPodd).siftedSum
      = ∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).siftedSum := by
  rw [switchSieveW_siftedSum]
  have hterm : ∀ n ∈ (twinWindow x).filter (fun n => n % Q = a % Q),
      (if Nat.Coprime Ps n then aCount x z y n else 0)
        = ∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
            (if Nat.Coprime Ps n then blockACount x z y ε₀ j n else 0) := by
    intro n _
    by_cases hcop : Nat.Coprime Ps n
    · simp only [if_pos hcop]
      exact aCount_eq_sum_blockACount x z y ε₀ hz hε₀ n
    · simp only [if_neg hcop, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [blockSwitchSieveW_siftedSum]

/-- **`block_switch_upper_B_W` — the sharp (cB) upper linear sieve at the W-block instance.**
A verbatim re-instantiation of `block_switch_upper_B`: `twin_A2_per_prime_B` is generic in
the `BoundingSieve`; the guards are Ps-based (`switch_hguard`/`switch_hnu`, block- and
Q-independent), and `totalMass ≥ 0` is `blockW_totalMass_nonneg`.  The `h4` slot is the
H4C-CONDITIONED form.  Conclusion at the smooth block mass `blockTripleSum j / φ(Q)`. -/
theorem block_switch_upper_B_W (x z y : ℕ) (ε₀ : ℝ) (j Q a Ps Dlev : ℕ) (ε K QR : ℝ)
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
    (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).siftedSum
      ≤ (blockTripleSum x z y ε₀ j / (Q.totient : ℝ)
            * Salt.BrunLower.W (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd))
          * (Fchain (maxDepth (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd))
                (logRatio y Dlev)
              + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
        + rosserRemainder (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd) (QR * Dlev) := by
  set s := blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd with hs
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < y := hPy
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    switch_hguard hε hw0 hPodd hPlow
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := switch_hnu Ps
  have htm : 0 ≤ s.totalMass := blockW_totalMass_nonneg x z y ε₀ j Q a Ps hPs hPodd
  have h := twin_A2_per_prime_B s y Dlev ε K QR hD2 htm hQR hzTop hguard hnu hε.le
    (lt_of_le_of_lt hεsmall (by norm_num)) hKe (stepHypWPC_sharpB ε hε.le hεsmall) h4 hStop
  have htm_eq : s.totalMass = blockTripleSum x z y ε₀ j / (Q.totient : ℝ) := rfl
  rw [← htm_eq]
  exact h

/-- **`mainA3_of_block_remainders_W` — the composed CONDITIONAL A₃ supplier mirror (the A3W
endpoint).**  W-bridge (`triplePrimeSumW_le_sifted` + the block split) + per-block sharp
keystone (`block_switch_upper_B_W`, `h4` H4C-conditioned) under the SINGLE named slot

  `hBVblocksW : ∑_j rosserRemainder (blockSwitchSieveW j …) (QR·Dlev) ≤ x/(log x)^10`

(the sum of Q-SHIFTED block remainders — each `rem_W d` is a `Q·d`-discrepancy, Part C).
**The main term is the landed one at the AP scale**: same `W (switchSieve …)`, same
`maxDepth (switchSieve …)` (the `rfl` W-factoring mirrors), with
`tripleSum ↦ tripleSum/φ(Q)` — exactly D2's ledger normalization `X_W/φ(Q)`.  This is the
supplier for `chen_of_hypotheses_W`'s `hA3` slot at the W-carrier `triplePrimeSumW`. -/
theorem mainA3_of_block_remainders_W (x z y P Q a w' Ps Dlev : ℕ) (ε₀ ε K QR : ℝ)
    (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hx : 2 ≤ x) (hyx2 : y ≤ x / 2)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Q (a + 2))
    (hD2 : 2 ≤ Dlev) (hQR : 1 ≤ QR)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev)
    (hBVblocksW : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          rosserRemainder (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd) (QR * Dlev))
        ≤ (x : ℝ) / (Real.log x) ^ 10) :
    triplePrimeSumW Q a x P y
      ≤ Real.log x *
          (tripleSum x z y / (Q.totient : ℝ)
              * Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd)
              * (Fchain (maxDepth (switchSieve x z y Ps hPs hPodd)) (logRatio y Dlev)
                + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
            + (x : ℝ) / (Real.log x) ^ 10) := by
  have hlogx : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  set Wswitch := Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd) with hWswitch
  set Ffac := Fchain (maxDepth (switchSieve x z y Ps hPs hPodd)) (logRatio y Dlev)
      + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev) with hFfac
  -- per-block upper bound with W and maxDepth collapsed to the global values (rfl mirrors)
  have hblock : ∀ j, (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).siftedSum
      ≤ blockTripleSum x z y ε₀ j / (Q.totient : ℝ) * Wswitch * Ffac
        + rosserRemainder (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd) (QR * Dlev) := by
    intro j
    have h := block_switch_upper_B_W x z y ε₀ j Q a Ps Dlev ε K QR hPs hPodd hPy hPlow hD2
      hQR hε hw0 hεsmall hKe h4 hStop
    rwa [blockSwitchSieveW_W_eq, blockSwitchSieveW_maxDepth_eq, ← hWswitch, ← hFfac] at h
  -- sum the blocks: the carrier factors out, ∑ blockTripleSum/φ(Q) reassembles, the slot closes
  have hRHS : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).siftedSum)
      ≤ tripleSum x z y / (Q.totient : ℝ) * Wswitch * Ffac
        + (x : ℝ) / (Real.log x) ^ 10 := by
    have hstep : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).siftedSum)
        ≤ ∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
            (blockTripleSum x z y ε₀ j / (Q.totient : ℝ) * Wswitch * Ffac
              + rosserRemainder (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd)
                  (QR * Dlev)) :=
      Finset.sum_le_sum (fun j _ => hblock j)
    rw [Finset.sum_add_distrib] at hstep
    have hfac : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          blockTripleSum x z y ε₀ j / (Q.totient : ℝ) * Wswitch * Ffac)
        = tripleSum x z y / (Q.totient : ℝ) * Wswitch * Ffac := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_div,
        ← tripleSum_eq_sum_blockTripleSum x z y ε₀ hz hε₀]
    rw [hfac] at hstep
    linarith [hstep, hBVblocksW]
  calc triplePrimeSumW Q a x P y
      ≤ Real.log x * (switchSieveW x z y Q a Ps hPs hPodd).siftedSum :=
        triplePrimeSumW_le_sifted x z y P Q a w' Ps hPs hPodd hPy hx hyx2 hQfull hPfull' hQa2
    _ = Real.log x * ∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).siftedSum := by
        rw [switchSieveW_siftedSum_eq_sum_blocks x z y ε₀ hz hε₀ Q a Ps hPs hPodd]
    _ ≤ Real.log x * (tripleSum x z y / (Q.totient : ℝ) * Wswitch * Ffac
          + (x : ℝ) / (Real.log x) ^ 10) := mul_le_mul_of_nonneg_left hRHS hlogx

/-! ## Part C — the remainder identification (D3): `rem_W d` IS the `Q·d`-discrepancy -/

open Classical in
/-- **The CRT residue of the W-switch (D3).**  The unique class mod `Q·d` combining
`a + 2 (mod Q)` (the AP-membership of `n + 2`) and `2 (mod d)` (the switch congruence
`d ∣ n`); `0` off the coprime case (never consumed there). -/
noncomputable def crtClassW (Q d a : ℕ) : ℕ :=
  if h : Nat.Coprime Q d then (Nat.chineseRemainder h (a + 2) 2).1 else 0

lemma crtClassW_modEq_left {Q d : ℕ} (a : ℕ) (h : Nat.Coprime Q d) :
    crtClassW Q d a ≡ a + 2 [MOD Q] := by
  unfold crtClassW
  rw [dif_pos h]
  exact (Nat.chineseRemainder h (a + 2) 2).2.1

lemma crtClassW_modEq_right {Q d : ℕ} (a : ℕ) (h : Nat.Coprime Q d) :
    crtClassW Q d a ≡ 2 [MOD d] := by
  unfold crtClassW
  rw [dif_pos h]
  exact (Nat.chineseRemainder h (a + 2) 2).2.2

/-- **`gcd(crtClassW, Q·d) = 1` (D3's coprimality).**  From `gcd(Q, a+2) = 1` (at the
instantiation `a = Q − 1` this is `residue_witness`) and `d` odd (`switch_dvd_coprime_two`
for `d ∣ Ps`): the class is `≡ a+2` mod `Q` and `≡ 2` mod `d`.  This is the `hr` input of
the C4 residue-function generalized windowed chain at the Q-shifted moduli. -/
theorem crtClassW_coprime {Q d a : ℕ} (hQd : Nat.Coprime Q d)
    (hQa2 : Nat.Coprime Q (a + 2)) (h2d : Nat.Coprime 2 d) :
    Nat.Coprime (crtClassW Q d a) (Q * d) := by
  have hmodL : crtClassW Q d a % Q = (a + 2) % Q := crtClassW_modEq_left a hQd
  have hmodR : crtClassW Q d a % d = 2 % d := crtClassW_modEq_right a hQd
  have hL : Nat.gcd Q (crtClassW Q d a) = Nat.gcd Q (a + 2) := by
    rw [Nat.gcd_rec Q (crtClassW Q d a), Nat.gcd_rec Q (a + 2), hmodL]
  have hR : Nat.gcd d (crtClassW Q d a) = Nat.gcd d 2 := by
    rw [Nat.gcd_rec d (crtClassW Q d a), Nat.gcd_rec d 2, hmodR]
  refine Nat.Coprime.mul_right ?_ ?_
  · refine Nat.coprime_comm.mp ?_
    unfold Nat.Coprime at hQa2 ⊢
    rw [hL]
    exact hQa2
  · refine Nat.coprime_comm.mp ?_
    unfold Nat.Coprime at h2d ⊢
    rw [hR, Nat.gcd_comm]
    exact h2d

/-- **The support fold (D3).**  On the W-support, the pair `(n ≡ a (mod Q), d ∣ n)` is the
SINGLE class `n + 2 ≡ crtClassW (mod Q·d)` — CRT at `gcd(Q, d) = 1`.  This is why `rem_W d`
is a `Q·d`-discrepancy and the windowed chain re-instantiates at the shifted moduli. -/
theorem memClassW_iff {Q d a n : ℕ} (hQd : Nat.Coprime Q d) :
    (n % Q = a % Q ∧ d ∣ n) ↔ (n + 2) ≡ crtClassW Q d a [MOD Q * d] := by
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hQd]
  constructor
  · rintro ⟨hap, hdvd⟩
    have hap' : n ≡ a [MOD Q] := hap
    have h0 : n ≡ 0 [MOD d] := (Nat.modEq_zero_iff_dvd).mpr hdvd
    exact ⟨(Nat.ModEq.add_right 2 hap').trans (crtClassW_modEq_left a hQd).symm,
      (Nat.ModEq.add_right 2 h0).trans (crtClassW_modEq_right a hQd).symm⟩
  · rintro ⟨hQside, hdside⟩
    have h1 : n ≡ a [MOD Q] :=
      Nat.ModEq.add_right_cancel' 2 (hQside.trans (crtClassW_modEq_left a hQd))
    have h2 : n + 2 ≡ 0 + 2 [MOD d] := hdside.trans (crtClassW_modEq_right a hQd)
    exact ⟨h1, (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_right_cancel' 2 h2)⟩

open Classical in
/-- **`blockResCountM`** — the block-`j` triples with `prod3 ≡ c (mod m)`, at a FREE modulus
`m` and class `c` (the `blockResCount` shape the W-route consumes at `m = Q·d`,
`c = crtClassW Q d a`; the landed `blockResCount j d = blockResCountM j d 2`). -/
noncomputable def blockResCountM (x z y : ℕ) (ε₀ : ℝ) (j m c : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧
        ((prod3 t : ℕ) : ZMod m) = ((c : ℕ) : ZMod m))).card : ℝ)

open Classical in
/-- **`blockUnitCountM`** — block-`j` triples with `prod3` a unit mod `m` (free modulus). -/
noncomputable def blockUnitCountM (x z y : ℕ) (ε₀ : ℝ) (j m : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧ IsUnit ((prod3 t : ℕ) : ZMod m))).card : ℝ)

open Classical in
/-- **`blockNonUnitCountM`** — block-`j` triples with `prod3` NOT coprime to `m`. -/
noncomputable def blockNonUnitCountM (x z y : ℕ) (ε₀ : ℝ) (j m : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧ ¬ IsUnit ((prod3 t : ℕ) : ZMod m))).card : ℝ)

/-- `blockUnitCountM + blockNonUnitCountM = blockTripleSum` at every modulus `m` — the
partition of the block count (mirror of `blockUnit_add_blockNonUnit`, free modulus). -/
theorem blockUnitM_add_blockNonUnitM (x z y : ℕ) (ε₀ : ℝ) (j m : ℕ) :
    blockUnitCountM x z y ε₀ j m + blockNonUnitCountM x z y ε₀ j m
      = blockTripleSum x z y ε₀ j := by
  classical
  unfold blockUnitCountM blockNonUnitCountM
  rw [blockTripleSum_eq_card, ← Nat.cast_add]
  congr 1
  have hU : (tripleSet x z y).filter
        (fun t => blockIdx z ε₀ t.1 = j ∧ IsUnit ((prod3 t : ℕ) : ZMod m))
      = (blockTripleSet x z y ε₀ j).filter (fun t => IsUnit ((prod3 t : ℕ) : ZMod m)) := by
    rw [blockTripleSet, Finset.filter_filter]
  have hN : (tripleSet x z y).filter
        (fun t => blockIdx z ε₀ t.1 = j ∧ ¬ IsUnit ((prod3 t : ℕ) : ZMod m))
      = (blockTripleSet x z y ε₀ j).filter
          (fun t => ¬ IsUnit ((prod3 t : ℕ) : ZMod m)) := by
    rw [blockTripleSet, Finset.filter_filter]
  rw [hU, hN]
  exact Finset.card_filter_add_card_filter_not
    (s := blockTripleSet x z y ε₀ j) (p := fun t => IsUnit ((prod3 t : ℕ) : ZMod m))

open Classical in
/-- **`multSum_W d` counts block triples in the CRT class mod `Q·d` (D3, FULL).**  The
W-instance's residue mass at `d` — the AP filter FOLDS into the class: fibering the block
triples over `n = prod3 − 2` and applying `memClassW_iff` per fibre.  Mirrors
`blockMultSum_eq_apCount`, with modulus `Q·d`, class `crtClassW Q d a`. -/
theorem blockMultSumW_eq_apCount (x z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (d : ℕ) (hQd : Nat.Coprime Q d) :
    (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).multSum d
      = blockResCountM x z y ε₀ j (Q * d) (crtClassW Q d a) := by
  classical
  set c := crtClassW Q d a with hc
  -- step 1: fold the AP filter + the divisibility into the single class mod `Q·d`
  rw [blockSwitchSieveW_multSum, Finset.sum_filter]
  have hmerge : ∀ n : ℕ,
      (if n % Q = a % Q then (if d ∣ n then blockACount x z y ε₀ j n else 0) else 0)
        = (if (n + 2) ≡ c [MOD Q * d] then blockACount x z y ε₀ j n else 0) := by
    intro n
    by_cases h1 : n % Q = a % Q
    · by_cases h2 : d ∣ n
      · rw [if_pos h1, if_pos h2, if_pos ((memClassW_iff hQd).mp ⟨h1, h2⟩)]
      · rw [if_pos h1, if_neg h2, if_neg (fun hcl => h2 (((memClassW_iff hQd).mpr hcl).2))]
    · rw [if_neg h1, if_neg (fun hcl => h1 (((memClassW_iff hQd).mpr hcl).1))]
  rw [Finset.sum_congr rfl (fun n _ => hmerge n)]
  -- step 2: fiber the class-count of block triples over `n = prod3 t − 2`
  have Hmem : ∀ t ∈ (tripleSet x z y).filter
        (fun t => blockIdx z ε₀ t.1 = j ∧ prod3 t ≡ c [MOD Q * d]),
      prod3 t - 2 ∈ twinWindow x := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have h := ht.1
    rw [tripleSet, Finset.mem_filter] at h
    obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := h
    rw [twinWindow, Finset.mem_Icc]; omega
  have hcard : (((tripleSet x z y).filter
        (fun t => blockIdx z ε₀ t.1 = j ∧ prod3 t ≡ c [MOD Q * d])).card : ℝ)
      = ∑ n ∈ twinWindow x,
          if (n + 2) ≡ c [MOD Q * d] then blockACount x z y ε₀ j n else 0 := by
    rw [Finset.card_eq_sum_card_fiberwise Hmem, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun n _hn => ?_)
    have hfib : (((tripleSet x z y).filter
            (fun t => blockIdx z ε₀ t.1 = j ∧ prod3 t ≡ c [MOD Q * d])).filter
            (fun t => prod3 t - 2 = n))
        = (tripleSet x z y).filter
            (fun t => (blockIdx z ε₀ t.1 = j ∧ prod3 t ≡ c [MOD Q * d])
              ∧ prod3 t - 2 = n) := by
      rw [Finset.filter_filter]
    rw [hfib]
    by_cases hcn : (n + 2) ≡ c [MOD Q * d]
    · rw [if_pos hcn]
      unfold blockACount
      rw [Nat.cast_inj]
      refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
      rw [tripleSet, Finset.mem_filter] at ht
      obtain ⟨_, _, _, _, _, _, _, _, hlo, _⟩ := ht
      constructor
      · rintro ⟨⟨hb, _⟩, hpn⟩
        exact ⟨hb, by omega⟩
      · rintro ⟨hb, hpe⟩
        have hn2 : prod3 t = n + 2 := by omega
        exact ⟨⟨hb, by rw [hn2]; exact hcn⟩, by omega⟩
    · rw [if_neg hcn, Nat.cast_eq_zero, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      intro t ht
      rintro ⟨⟨_, hcl⟩, hpn⟩
      rw [tripleSet, Finset.mem_filter] at ht
      obtain ⟨_, _, _, _, _, _, _, _, hlo, _⟩ := ht
      have hn2 : prod3 t = n + 2 := by omega
      rw [hn2] at hcl
      exact hcn hcl
  rw [← hcard]
  -- step 3: the ModEq predicate IS the ZMod cast form of `blockResCountM`
  unfold blockResCountM
  rw [Nat.cast_inj]
  refine congrArg Finset.card (Finset.filter_congr (fun t _ => ?_))
  constructor
  · rintro ⟨hb, hcl⟩
    exact ⟨hb, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcl⟩
  · rintro ⟨hb, hcl⟩
    exact ⟨hb, (ZMod.natCast_eq_natCast_iff _ _ _).mp hcl⟩

/-- **The W honest per-`d` discrepancy at modulus `Q·d`** — `blockHonestDisc`'s mirror at the
shifted modulus and CRT class; the object the C4-generalized windowed chain prices. -/
noncomputable def blockHonestDiscW (x z y : ℕ) (ε₀ : ℝ) (j Q a d : ℕ) : ℝ :=
  blockResCountM x z y ε₀ j (Q * d) (crtClassW Q d a)
    - nuChen (Q * d) * blockUnitCountM x z y ε₀ j (Q * d)

/-- **The W conversion error at modulus `Q·d`** — `ν(Q·d)·(non-coprime block count)`. -/
noncomputable def blockConvErrW (x z y : ℕ) (ε₀ : ℝ) (j Q d : ℕ) : ℝ :=
  nuChen (Q * d) * blockNonUnitCountM x z y ε₀ j (Q * d)

/-- **The honest W remainder split (D3 + C3, FULL).**  With the SMOOTH `totalMass` (C3),
`rem_W d` is EXACTLY the landed split shape at the shifted modulus:
`rem_W d = (blockResCountM (Q·d) c − ν(Q·d)·blockUnitCountM (Q·d)) − ν(Q·d)·blockNonUnitCountM`
— the smooth main term satisfies `ν(d)·(blockTripleSum/φ(Q)) = ν(Q·d)·blockTripleSum` by
multiplicativity at `gcd(Q, d) = 1`.  Mirrors `blockSwitchSieve_rem_split`. -/
theorem blockSwitchSieveW_rem_split (x z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (d : ℕ) (hQd : Nat.Coprime Q d) :
    (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).rem d
      = (blockResCountM x z y ε₀ j (Q * d) (crtClassW Q d a)
          - nuChen (Q * d) * blockUnitCountM x z y ε₀ j (Q * d))
        - nuChen (Q * d) * blockNonUnitCountM x z y ε₀ j (Q * d) := by
  have hmul : nuChen (Q * d) = nuChen Q * nuChen d := nuChen_mult.map_mul_of_coprime hQd
  rw [BoundingSieve.rem, blockSwitchSieveW_nu, blockSwitchSieveW_totalMass,
    blockMultSumW_eq_apCount x z y ε₀ j Q a Ps hPs hPodd d hQd,
    ← blockUnitM_add_blockNonUnitM x z y ε₀ j (Q * d), hmul, nuChen_apply Q]
  ring

/-- **The per-`d` W bridge bound.**  `|rem_W d| ≤ |blockHonestDiscW| + blockConvErrW` —
the triangle on the split (the conversion error is `≥ 0`).  Mirrors
`blockSwitchSieve_abs_rem_le` at the shifted modulus. -/
theorem blockSwitchSieveW_abs_rem_le (x z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (d : ℕ) (hQd : Nat.Coprime Q d) :
    |(blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd).rem d|
      ≤ |blockHonestDiscW x z y ε₀ j Q a d| + blockConvErrW x z y ε₀ j Q d := by
  have hconv : 0 ≤ nuChen (Q * d) * blockNonUnitCountM x z y ε₀ j (Q * d) := by
    apply mul_nonneg
    · rw [nuChen_apply]; positivity
    · unfold blockNonUnitCountM; positivity
  rw [blockSwitchSieveW_rem_split x z y ε₀ j Q a Ps hPs hPodd d hQd]
  have h := abs_sub (blockResCountM x z y ε₀ j (Q * d) (crtClassW Q d a)
      - nuChen (Q * d) * blockUnitCountM x z y ε₀ j (Q * d))
      (nuChen (Q * d) * blockNonUnitCountM x z y ε₀ j (Q * d))
  rw [abs_of_nonneg hconv] at h
  exact h

/-- **The summed L¹ reduction of the W block Rosser remainder.**  Per `d ∣ Ps` the
coprimality `gcd(Q, d) = 1` comes from `hQPs : gcd(Q, Ps) = 1` (at instantiation: `Q`'s
primes are `< w₀ ≤` every prime of `Ps`).  Mirrors `blockRem_rosserRemainder_split_le`. -/
theorem blockRemW_rosserRemainder_split_le (x z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hQPs : Nat.Coprime Q Ps) (bound : ℝ) :
    rosserRemainder (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd) bound
      ≤ (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then |blockHonestDiscW x z y ε₀ j Q a d| else 0)
        + (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then blockConvErrW x z y ε₀ j Q d else 0) := by
  rw [rosserRemainder, blockSwitchSieveW_prodPrimes, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have hQd : Nat.Coprime Q d := hQPs.coprime_dvd_right (Nat.mem_divisors.mp hd).1
  by_cases h : (d : ℝ) < bound
  · rw [if_pos h, if_pos h, if_pos h]
    exact blockSwitchSieveW_abs_rem_le x z y ε₀ j Q a Ps hPs hPodd d hQd
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

/-- **The block sum of the W L¹ reductions.**  Mirrors `sum_blockRem_split_le`. -/
theorem sum_blockRemW_split_le (x z y : ℕ) (ε₀ : ℝ) (Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (hQPs : Nat.Coprime Q Ps) (bound : ℝ) :
    (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        rosserRemainder (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd) bound)
      ≤ (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
            ∑ d ∈ Nat.divisors Ps,
              if (d : ℝ) < bound then |blockHonestDiscW x z y ε₀ j Q a d| else 0)
        + (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
            ∑ d ∈ Nat.divisors Ps,
              if (d : ℝ) < bound then blockConvErrW x z y ε₀ j Q d else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  exact blockRemW_rosserRemainder_split_le x z y ε₀ j Q a Ps hPs hPodd hQPs bound

/-- **`hBVblocksW_of_generalBV` — the composed W block-remainder close.**  Under the two
summed NAMED bounds `hHD_W` (the W honest-discrepancy double sum — priced by the C4
residue-function generalized windowed chain at the Q-shifted moduli `Q·d`, residues
`crtClassW Q d a`) and `hCE_W` (the W conversion-error double sum) plus the numeric closure
`hNum`, the W block Rosser remainders sum below `x/(log x)^10` — **the EXACT `hBVblocksW`
hypothesis `mainA3_of_block_remainders_W` names**.  Mirrors `hBVblocks_of_generalBV`. -/
theorem hBVblocksW_of_generalBV (x z y : ℕ) (ε₀ : ℝ) (Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (hQPs : Nat.Coprime Q Ps)
    (QR : ℝ) (Dlev : ℕ) {RHD RCE : ℝ}
    (hHD : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          ∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < QR * Dlev then |blockHonestDiscW x z y ε₀ j Q a d| else 0) ≤ RHD)
    (hCE : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
          ∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < QR * Dlev then blockConvErrW x z y ε₀ j Q d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (x : ℝ) / (Real.log x) ^ 10) :
    (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        rosserRemainder (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd) (QR * Dlev))
      ≤ (x : ℝ) / (Real.log x) ^ 10 := by
  refine le_trans (sum_blockRemW_split_le x z y ε₀ Q a Ps hPs hPodd hQPs (QR * Dlev)) ?_
  linarith [hHD, hCE, hNum]

/-! ## Part D — the discharge bridge: the composed chain into the `hBVblocksW` slot

The composition below lands character-for-character in `mainA3_of_block_remainders_W`'s
`hBVblocksW` slot.  The per-block W honest-discrepancy prices (`hBlockW`) are supplied — at
GLU-2W — by the C4 residue-function generalized windowed chain, exactly as the landed GBV5
composition supplies `hBlock` at the un-shifted moduli:

* **the box identification**: `blockBox_windowDisc_eq_res` at `d := Q·d'`,
  `R₀ := crtClassW Q d' a` turns each ordering-cleared box's W honest-disc piece (the raw
  `tripleSet` class-count difference at `prod3 ≡ crtClassW (mod Q·d')` — exactly
  `blockHonestDiscW`'s box restriction) into an `apDiscBilinCutoff` T-difference at the
  shifted modulus;
* **the box pricing**: `box_disc_three_way`/`medium_survivor_price_sqrtD`/
  `general_BV_cutoff_sqrtD` at `Dset := (Nat.divisors Ps).image (Q * ·)` (filtered to the
  level) and `r := fun m => crtClassW Q (m / Q) a`, with `hr` discharged by
  `crtClassW_coprime` (+ `residue_witness` for `gcd(Q, a+2) = 1` at `a = Q − 1` and
  `switch_dvd_coprime_two` for `d` odd);
* **the assembly**: the piece-decomposition per `(j, k)` box and the band/low residuals,
  mirroring `hBlock_of_window_prices` → `hHDblocks_of_perBlock` at the W objects.

### GLU-2W named threshold rows (the Q-shift costs — each documented, discharged at GLU-2W)

1. **the level row** (`hDscale`-form): the shifted moduli run to `Q·(QR·Dlev)` — the chain's
   `D ≤ √(XM)/L^B` row absorbs ONE extra factor `Q ≤ 4^{w₀} ≤ L` (C2's tower
   `x₀ ≥ exp(exp(2·w0N ε))`; the `L^10` sizing was bought for exactly this — D4/C7).
2. **the divisor row** (`herr_div`-form): the e-fold's `d(e)` at `e ∣ Q·d` costs
   `τ(Q·d) ≤ τ(Q)·τ(d) ≤ Q·τ(d) ≤ L·τ(d)` — one extra `L` power against the `x^{1/9}`+ room
   of `hdiv_direct`'s floor (`hfloor` at `F = z·y`).
3. **the BV crumb row** (`hNum`-form): the budget `x/L^10` is measured against the new main
   scale `X_W/φ(Q) ≥ 32e^{−70}·x/L³` (C7's honest crude scale) — `L⁷/e^{70}` of room.
4. **the `hr` row**: DISCHARGED HERE (`crtClassW_coprime`); no GLU-2W obligation remains.
5. **the coprimality row** (`hQPs`): `gcd(Q, Ps) = 1` — free at instantiation (`Q`'s primes
   `< w₀ ≤` every prime of `Ps`).
-/

section CompositionSanity

/-- **The discharge-bridge composition (the GLU-2W shape).**  Given the per-block W
honest-discrepancy prices `hBlockW` (the windowed-chain outputs at the shifted moduli), the
conversion-error row `hCE`, and the numeric closure rows `hSum`/`hNum`, the chain
`hBlockW → hBVblocksW_of_generalBV → mainA3_of_block_remainders_W` emits the A₃ supplier
bound at the W-carrier — character-for-character the `hA3`-shape `chen_of_hypotheses_W`
consumes at the AP scale `tripleSum/φ(Q)`. -/
example (x z y : ℕ) (ε₀ : ℝ) (P Q a w' Ps Dlev : ℕ) (ε K QR : ℝ)
    (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hx : 2 ≤ x) (hyx2 : y ≤ x / 2)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Q (a + 2)) (hQPs : Nat.Coprime Q Ps)
    (hD2 : 2 ≤ Dlev) (hQR : 1 ≤ QR)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev)
    (RBlock : ℕ → ℝ) (RHD RCE : ℝ)
    (hBlockW : ∀ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < QR * Dlev then |blockHonestDiscW x z y ε₀ j Q a d| else 0)
          ≤ RBlock j)
    (hSum : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1), RBlock j) ≤ RHD)
    (hCE : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < QR * Dlev then blockConvErrW x z y ε₀ j Q d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (x : ℝ) / (Real.log x) ^ 10) :
    -- the EXACT `hA3`-shape at the W-carrier (the AP-scale main term):
    triplePrimeSumW Q a x P y
      ≤ Real.log x *
          (tripleSum x z y / (Q.totient : ℝ)
              * Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd)
              * (Fchain (maxDepth (switchSieve x z y Ps hPs hPodd)) (logRatio y Dlev)
                + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
            + (x : ℝ) / (Real.log x) ^ 10) := by
  refine mainA3_of_block_remainders_W x z y P Q a w' Ps Dlev ε₀ ε K QR hz hε₀ hPs hPodd hPy
    hPlow hx hyx2 hQfull hPfull' hQa2 hD2 hQR hε hw0 hεsmall hKe h4 hStop ?_
  exact hBVblocksW_of_generalBV x z y ε₀ Q a Ps hPs hPodd hQPs QR Dlev
    (le_trans (Finset.sum_le_sum hBlockW) hSum) hCE hNum

-- the W-instances + the rfl W-factoring
#check @Salt.Chen.switchSieveW
#check @Salt.Chen.blockSwitchSieveW
#check @Salt.Chen.switchSieveW_W_eq
#check @Salt.Chen.blockSwitchSieveW_W_eq
#check @Salt.Chen.blockSwitchSieveW_maxDepth_eq
-- the supplier mirror
#check @Salt.Chen.triplePrimeSumW_le_sifted
#check @Salt.Chen.block_switch_upper_B_W
#check @Salt.Chen.mainA3_of_block_remainders_W
-- the remainder identification (D3)
#check @Salt.Chen.crtClassW_coprime
#check @Salt.Chen.memClassW_iff
#check @Salt.Chen.blockMultSumW_eq_apCount
#check @Salt.Chen.blockSwitchSieveW_rem_split
#check @Salt.Chen.hBVblocksW_of_generalBV
-- the box identification + the C4 residue-function generalized pricing chain (the
-- `hBlockW` suppliers at the shifted moduli, GLU-2W's obligations)
#check @Salt.Chen.blockBox_windowDisc_eq_res
#check @Salt.Chen.box_disc_three_way
#check @Salt.Chen.medium_survivor_price_sqrtD
#check @Salt.Chen.general_BV_cutoff_sqrtD
-- the landed consumers of the W-carrier (Assembly's H_W)
#check @Salt.Chen.aCount_ge_one_of_W
#check @Salt.Chen.chen_of_hypotheses_W
#check @Salt.Chen.residue_witness
#check @Salt.Chen.switch_dvd_coprime_two

end CompositionSanity

end Salt.Chen
