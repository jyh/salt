/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.PDiag
import Salt.Goldbach.CountFinal
import Salt.Goldbach.A1W
import Salt.Goldbach.A2W
import Salt.Goldbach.Residue
import Salt.Goldbach.WeightWindow
import Salt.Chen.HeadlineW2
import Salt.Chen.CountAtOp3

/-!
# The Goldbach operating-point layer (`chen_goldbach`, wave W4, node `G-OP`)

The penultimate node: instantiate the landed Goldbach interfaces at the frozen
operating point `x := N`, `z = N^{1/8}`, `y = N^{1/3}`, the fixed modulus `opQ`,
and the punctured sifting products `goldPs`.  Every heavy analytic fact has
already landed in the wave files (`Density`, `Residue`, `A1W`, `A2W`, `Switch`,
`SwitchBV`, `CountFinal`, `SW2`, `PDiag`); this file supplies the concrete
op-point substitutions the terminal assembly node `G-ASM` composes.

Reuse note: the scales `z = ⌊N^{1/8}⌋`, `y = ⌊N^{1/3}⌋`, `D`, and the modulus
`Q = opQ` are **shared byte-for-byte with the twin operating point**
(`Salt.Chen.HeadlineW2`), so the twin's scale/threshold lemmas
(`a12_zyD`, `a12_log_ge`, `opf_*`, `a12_eps_*`, `a12_hw0`, `a12_primeInv_le`)
are reused directly at `x := N`.  The only Goldbach-specific pieces are the
punctured modulus `goldPs`, the reflected residue witness, and the gold sieve
carriers.

No `sorry`, no `native_decide`, no new axioms
(`[propext, Classical.choice, Quot.sound]` only).
-/

namespace Salt.Goldbach

open Finset ArithmeticFunction Salt.LS Salt.BV Salt.Chen

/-! ## Part 1 — the operating-point definitions

`z = ⌊N^{1/8}⌋`, `y = ⌊N^{1/3}⌋` are the twin scales `opZ`/`opY` re-exported at
`x := N`; the sifting moduli are the **punctured** window products `goldPs`
(mirroring the twin's `opP`/`opPs` with the extra `¬ q ∣ N` factor). -/

/-- The Goldbach sieve lower cutoff `z = ⌊N^{1/8}⌋` (the twin scale at `x := N`). -/
noncomputable def goldOpZ (N : ℕ) : ℕ := opZ N

/-- The Goldbach sieve upper cutoff `y = ⌊N^{1/3}⌋` (the twin scale at `x := N`). -/
noncomputable def goldOpY (N : ℕ) : ℕ := opY N

/-- The A₁ sifting modulus: the punctured product of primes in `[opW', z)`. -/
noncomputable def goldOpP (N : ℕ) : ℕ := goldPs N (opZ N) opW'

/-- The A₂/switch sifting modulus: the punctured product of primes in `[opW', y)`. -/
noncomputable def goldOpPs (N : ℕ) : ℕ := goldPs N (opY N) opW'

theorem goldOpZ_eq (N : ℕ) : goldOpZ N = opZ N := rfl
theorem goldOpY_eq (N : ℕ) : goldOpY N = opY N := rfl

/-! ## Part 2 — the fixed modulus `opQ` (squarefree, even) -/

/-- `opQ` is squarefree (a product of distinct primes). -/
theorem gold_opQ_squarefree : Squarefree opQ := by
  have h : opQ = ∏ p ∈ (Finset.range opW').filter Nat.Prime, p := rfl
  rw [h]
  exact opf_prod_primes_squarefree fun p hp => (Finset.mem_filter.mp hp).2

/-- `opQ` is even (`2 < opW'`, so `2 ∣ opQ`). -/
theorem gold_opQ_even : Even opQ := by
  have h2 : (2 : ℕ) ∣ opQ :=
    opf_Qfull 2 Nat.prime_two (lt_of_lt_of_le (by norm_num) opf_w'3)
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, by omega⟩

/-! ## Part 3 — the punctured sifting moduli (squarefree, coprimality, window) -/

/-- The A₁ modulus `goldOpP` is squarefree. -/
theorem goldOpP_squarefree (N : ℕ) : Squarefree (goldOpP N) := goldPs_squarefree N (opZ N) opW'

/-- The A₂/switch modulus `goldOpPs` is squarefree. -/
theorem goldOpPs_squarefree (N : ℕ) : Squarefree (goldOpPs N) := goldPs_squarefree N (opY N) opW'

/-- Every prime factor of `goldOpP` is odd (`≥ 3`). -/
theorem goldOpP_odd (N : ℕ) : ∀ p ∈ (goldOpP N).primeFactors, 3 ≤ p :=
  goldPs_odd (N := N) (z := opZ N) (w' := opW') opf_w'3

/-- Every prime factor of `goldOpPs` is odd (`≥ 3`). -/
theorem goldOpPs_odd (N : ℕ) : ∀ p ∈ (goldOpPs N).primeFactors, 3 ≤ p :=
  goldPs_odd (N := N) (z := opY N) (w' := opW') opf_w'3

/-- `goldOpP` is coprime to `N` (the puncture: no prime factor divides `N`). -/
theorem goldOpP_coprime_N (N : ℕ) : Nat.Coprime (goldOpP N) N := goldPs_coprime_N N (opZ N) opW'

/-- `goldOpPs` is coprime to `N`. -/
theorem goldOpPs_coprime_N (N : ℕ) : Nat.Coprime (goldOpPs N) N := goldPs_coprime_N N (opY N) opW'

/-- The window facts for `goldOpP`: each prime factor lies in `[opW', z)` and misses `N`. -/
theorem goldOpP_window (N : ℕ) :
    ∀ q ∈ (goldOpP N).primeFactors, q.Prime ∧ opW' ≤ q ∧ q < opZ N ∧ ¬ q ∣ N :=
  goldPs_primeFactors_facts (N := N) (z := opZ N) (w' := opW')

/-- The window facts for `goldOpPs`. -/
theorem goldOpPs_window (N : ℕ) :
    ∀ q ∈ (goldOpPs N).primeFactors, q.Prime ∧ opW' ≤ q ∧ q < opY N ∧ ¬ q ∣ N :=
  goldPs_primeFactors_facts (N := N) (z := opY N) (w' := opW')

/-- `goldOpP ∣ opP` (the punctured product divides the full window product). -/
theorem goldOpP_dvd_opP (N : ℕ) : goldOpP N ∣ opP N := by
  unfold goldOpP goldPs opP
  refine Finset.prod_dvd_prod_of_subset _ _ (fun p => p) ?_
  intro q hq; rw [Finset.mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1⟩

/-- `goldOpPs ∣ opPs`. -/
theorem goldOpPs_dvd_opPs (N : ℕ) : goldOpPs N ∣ opPs N := by
  unfold goldOpPs goldPs opPs
  refine Finset.prod_dvd_prod_of_subset _ _ (fun p => p) ?_
  intro q hq; rw [Finset.mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1⟩

/-- `opQ` is coprime to the A₁ modulus (disjoint prime supports, via `opf_QP`). -/
theorem gold_opQ_coprime_P (N : ℕ) : Nat.Coprime opQ (goldOpP N) :=
  Nat.Coprime.coprime_dvd_right (goldOpP_dvd_opP N) (opf_QP N)

/-- `opQ` is coprime to the A₂/switch modulus (via `opf_QPs`). -/
theorem gold_opQ_coprime_Ps (N : ℕ) : Nat.Coprime opQ (goldOpPs N) :=
  Nat.Coprime.coprime_dvd_right (goldOpPs_dvd_opPs N) (opf_QPs N)

/-- The A₁ modulus prime factors are below `opZ N` (`hPz` slot). -/
theorem goldOpP_pz (N : ℕ) : ∀ p ∈ (goldOpP N).primeFactors, p < opZ N :=
  fun p hp => (goldOpP_window N p hp).2.2.1

/-- The A₁ modulus prime factors dominate `w0R opEps` (`hPlow` slot). -/
theorem goldOpP_plow (N : ℕ) : ∀ p ∈ (goldOpP N).primeFactors, w0R opEps ≤ (p : ℝ) :=
  fun p hp => le_trans (w0R_le_w0N opEps) (by exact_mod_cast (goldOpP_window N p hp).2.1)

/-- The A₂/switch modulus prime factors are below `opY N` (`hPy` slot). -/
theorem goldOpPs_py (N : ℕ) : ∀ p ∈ (goldOpPs N).primeFactors, p < opY N :=
  fun p hp => (goldOpPs_window N p hp).2.2.1

/-- The A₂/switch modulus prime factors dominate `w0R opEps`. -/
theorem goldOpPs_plow (N : ℕ) : ∀ p ∈ (goldOpPs N).primeFactors, w0R opEps ≤ (p : ℝ) :=
  fun p hp => le_trans (w0R_le_w0N opEps) (by exact_mod_cast (goldOpPs_window N p hp).2.1)

/-! ## Part 4 — the density threshold `N < (goldOpZ N)^9` (G-DENS's divisor route)

`z = ⌊N^{1/8}⌋ ≥ N^{1/8} − 1 ≥ ½N^{1/8}` (`N^{1/8} ≥ 10⁶ ≥ 2`), so
`z⁹ ≥ (N^{1/8}/2)⁹ = N^{9/8}/512 = N·N^{1/8}/512 ≥ N·10⁶/512 > N`.  This is the
`hN9` slot of `card_primesInWindow_dvd_le` (⟹ at most 8 window primes divide `N`,
the punctured correction stays bounded). -/
theorem gold_op_Zpow9 : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N → (N : ℝ) < ((opZ N : ℕ) : ℝ) ^ 9 := by
  refine ⟨10 ^ 48, fun N hN => ?_⟩
  have hx48R : (10 : ℝ) ^ 48 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by positivity) hx48R
  set s : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8) with hs
  have hpow8 : s ^ (8 : ℕ) = (N : ℝ) := by
    rw [hs, ← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 8)) 8, ← Real.rpow_mul hNpos.le]
    norm_num
  have h6 : (10 : ℝ) ^ 6 ≤ s := by
    have hmono : ((10 : ℝ) ^ 48) ^ ((1 : ℝ) / 8) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) :=
      Real.rpow_le_rpow (by positivity) hx48R (by norm_num)
    have hcompute : ((10 : ℝ) ^ 48) ^ ((1 : ℝ) / 8) = (10 : ℝ) ^ 6 := by
      rw [← Real.rpow_natCast (10 : ℝ) 48, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [hs]; linarith [hmono, hcompute.le, hcompute.ge]
  have hs2 : (2 : ℝ) ≤ s := le_trans (by norm_num) h6
  have hfloor : s - 1 < ((opZ N : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one s
    have : opZ N = ⌊s⌋₊ := by rw [hs]; rfl
    rw [this]; linarith [h]
  have hzhalf : s / 2 ≤ ((opZ N : ℕ) : ℝ) := by linarith [hfloor, hs2]
  have hznn : (0 : ℝ) ≤ s / 2 := by linarith [hs2]
  have hpow9 : (s / 2) ^ 9 ≤ ((opZ N : ℕ) : ℝ) ^ 9 := pow_le_pow_left₀ hznn hzhalf 9
  have hval : (s / 2) ^ 9 = (N : ℝ) * s / 512 := by
    rw [div_pow, show (9 : ℕ) = 8 + 1 by rfl, pow_succ, hpow8]; ring
  have hbig : (N : ℝ) < (N : ℝ) * s / 512 := by
    rw [lt_div_iff₀ (by norm_num)]
    nlinarith [hNpos, h6]
  linarith [hpow9, hval.le, hval.ge, hbig]

/-! ## Part 5 — the residue witness at the operating point (D1's `a`)

`goldbach_residue_witness` needs `Squarefree opQ`, `Even N`, and `opQ ≤ N`; the
first is `gold_opQ_squarefree`, the second is supplied by the (even) consumer,
the third is the free tower fact `opQ ≤ log N ≤ N`. -/
theorem gold_op_residue (N : ℕ) (hN : Even N) (hQN : opQ ≤ N) :
    ∃ a, a < opQ ∧ Nat.Coprime opQ a ∧ Nat.Coprime opQ (N - a) ∧
      ∀ q ∈ opQ.primeFactors, a % q ≠ 0 ∧ a % q ≠ N % q :=
  goldbach_residue_witness gold_opQ_squarefree hN hQN

/-! ## Part 6 — the A₁ Bombieri–Vinogradov row with `∃ B C` outside the `∀ N`

The Goldbach analogue of `a12_hBV_A1` (Finding-4 rederivation): `B, C` come from
the `N`-independent `psi_BV_of_siegelWalfisz'`, so the `∃x₁ ∀N` operating-point
consumer can choose its threshold as a function of `B, C`.  The body is
`goldBVSum_W`'s composition verbatim (the punctured-modulus split
`goldRosserRemainderW_le_split` + the shared `dispDiscW_filtered_le_Icc` /
`convSumW_le` legs). -/
set_option linter.unusedVariables false in
theorem gold_a12_hBV_A1 : ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
    ∀ (Qm a N z D P : ℕ) (ε Qlev : ℝ)
      (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
      (hPz : ∀ p ∈ P.primeFactors, p < z)
      (hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ (p : ℝ))
      (hx : 4 ≤ N) (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hwz : w0R ε ≤ (z : ℝ))
      (hQm1 : 1 ≤ Qm) (hQmP : Nat.Coprime Qm P) (hQma : Nat.Coprime Qm a)
      (hPN : Nat.Coprime P N) (hQlev : 1 ≤ Qlev) (hD : 1 ≤ D),
      (Qm : ℝ) * (Qlev * D) ≤ Real.sqrt (N : ℝ) / (Real.log N) ^ B →
      C * (N : ℝ) / (Real.log N) ^ (11 : ℝ) + C * (N : ℝ) / (Real.log N) ^ (11 : ℝ)
          + 2 * Real.log N
              * ((Qm.primeFactors.card : ℝ) + Real.log (Qlev * D) / Real.log 3)
              * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
        ≤ (N : ℝ) / (Real.log N) ^ 10 →
      rosserRemainder (goldA1SieveW Qm a N P hP hPodd) (Qlev * D)
        ≤ (N : ℝ) / (Real.log N) ^ 10 := by
  obtain ⟨B, C, hB, hC, hbv⟩ :=
    psi_BV_of_siegelWalfisz' Salt.SW.siegelWalfisz_holds 11 (by norm_num)
  refine ⟨B, C, hB, hC, ?_⟩
  intro Qm a N z D P ε Qlev hP hPodd hPz hPlow hx hε hw0 hwz hQm1 hQmP hQma hPN hQlev hD
    hlevel hclose
  have hx2 : 2 ≤ N := by omega
  have hsplit := goldRosserRemainderW_le_split Qm a N P hP hPodd hQm1 hQma hQmP hPN hx
    (Qlev * (D : ℝ))
  have hbv1 := hbv N (N - 2) hx2 (by omega : N - 2 ≤ N)
  have hbv2 := hbv N (N / 2 - 1) hx2 (by omega : N / 2 - 1 ≤ N)
  have hS1 : (∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (D : ℝ) then dispDisc (N - 2) (Qm * d) else 0)
      ≤ C * N / (Real.log N) ^ (11 : ℝ) :=
    le_trans (dispDiscW_filtered_le_Icc Qm (N - 2) hQm1 hlevel) hbv1
  have hS2 : (∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (D : ℝ) then dispDisc (N / 2 - 1) (Qm * d) else 0)
      ≤ C * N / (Real.log N) ^ (11 : ℝ) :=
    le_trans (dispDiscW_filtered_le_Icc Qm (N / 2 - 1) hQm1 hlevel) hbv2
  have hb1 : (1 : ℝ) ≤ Qlev * (D : ℝ) := by
    have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    nlinarith [hQlev, hD1]
  have hMbound : ∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)
      ≤ (1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε) := by
    have hvr := vratio_prod_le (goldA1SieveW Qm a N P hP hPodd) P.primeFactors hε.le hw0 hwz
      (w0R_threshold hε) (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hPlow p hp,
        by exact_mod_cast hPz p hp, twinA1_hnu P p hp⟩)
    exact le_trans (sum_inv_totient_le_Winv hP hPodd) hvr
  have hlogQD : 0 ≤ Real.log (Qlev * (D : ℝ)) := Real.log_nonneg hb1
  have hconvfac : 0 ≤ 2 * Real.log N
      * ((Qm.primeFactors.card : ℝ) + Real.log (Qlev * (D : ℝ)) / Real.log 3) := by
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hq : 0 ≤ Real.log (Qlev * (D : ℝ)) / Real.log 3 := div_nonneg hlogQD h3.le
    have hsum : 0 ≤ (Qm.primeFactors.card : ℝ) + Real.log (Qlev * (D : ℝ)) / Real.log 3 := by
      have hω : (0 : ℝ) ≤ (Qm.primeFactors.card : ℝ) := by positivity
      linarith
    exact mul_nonneg (by positivity) hsum
  have hConv : (∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (D : ℝ) then convTerm N (Qm * d) else 0)
      ≤ 2 * Real.log N
          * ((Qm.primeFactors.card : ℝ) + Real.log (Qlev * (D : ℝ)) / Real.log 3)
          * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε)) :=
    le_trans (convSumW_le Qm hP hPodd hQm1 hQmP hx hb1)
      (mul_le_mul_of_nonneg_left hMbound hconvfac)
  linarith [hsplit, hS1, hS2, hConv, hclose]

/-! ## Part 7 — the A₁ operating-point bundle (`gold_a12_hA1`)

The Goldbach analogue of `a12_hA1`: past a threshold the A₁ carrier `M1` is a
lower bound for the reflected coprime `Λ`-sum.  The abstract-`P` hypotheses of
the twin dissolve — `goldOpP N` is concrete, so `hP`/`hPodd`/`hPz`/… are
discharged from the landed op facts.  Composes `gold_A1_lower_B_W` (the sharp
sieve lower bound) with the BV row from `gold_a12_hBV_A1` at `B, C` and the
reused scale thresholds `a12_level`/`a12_close`. -/
set_option linter.unusedVariables false in
theorem gold_a12_hA1 : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    (goldA1SieveW opQ opA N (goldOpP N) (goldOpP_squarefree N) (goldOpP_odd N)).totalMass *
        (Salt.BrunLower.W (goldA1SieveW opQ opA N (goldOpP N)
              (goldOpP_squarefree N) (goldOpP_odd N)) *
          (fchain (maxDepth (goldA1SieveW opQ opA N (goldOpP N)
                (goldOpP_squarefree N) (goldOpP_odd N))) (logRatio (opZ N) (opD N))
            - opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opZ N) (opD N))))
      - (N : ℝ) / (Real.log N) ^ 10
    ≤ ∑ n ∈ twinWindow N,
        if n % opQ = opA % opQ ∧ Nat.Coprime (goldOpP N) (N - n) then vonMangoldt n else 0 := by
  obtain ⟨B, C, hB, hC, hbvfun⟩ := gold_a12_hBV_A1
  obtain ⟨x₂, hlev⟩ := a12_level B hB
  obtain ⟨x₃, hcl⟩ := a12_close C hC
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max (max (max x₂ x₃) xt) 4, fun N hN => ?_⟩
  have hx4 : 4 ≤ N := by omega
  obtain ⟨hQlog, hwz, hw'z, hz3, hzD, hD1, hzy, hyx2, hcube, hStop, hS2', hDlev2,
    hDhalf, hDlevlo, hRange, hDlevhalf, hx4'⟩ := htower N (by omega)
  have hQ1 : 1 ≤ opQ := by have := opf_Q2; omega
  have hQlevR : (1 : ℝ) ≤ (opQ : ℝ) := by exact_mod_cast hQ1
  have hz2 : 2 ≤ opZ N := by omega
  have hPz := goldOpP_pz N
  have hPlow := goldOpP_plow N
  have hlevel := hlev N (by omega) hQlog
  have hclose := hcl N (by omega) hQlog
  have hBV := hbvfun opQ opA N (opZ N) (opD N) (goldOpP N) opEps ((opQ : ℝ))
    (goldOpP_squarefree N) (goldOpP_odd N) hPz hPlow hx4 opf_eps_pos a12_hw0 hwz
    hQ1 (gold_opQ_coprime_P N) opf_Qma (goldOpP_coprime_N N) hQlevR hD1 hlevel hclose
  have hsup := gold_A1_lower_B_W opQ opA N (opZ N) (opD N) (goldOpP N) opEps (1 + opEps)
    ((opQ : ℝ)) (goldOpP_squarefree N) (goldOpP_odd N) hPz hPlow hz2 hzD hD1 hStop
    opf_eps_pos a12_hw0 (le_refl _) a12_eps_lt_249
    (stepHypWPC_sharpB opEps opf_eps_pos.le a12_eps_le_1000)
    (h4_cond_of_base opEps (1 + opEps) opf_eps_pos.le (le_refl _)) hQlevR hBV
  exact hsup

/-! ## Part 8 — the count-seam operating rows (`goldCount_bound_uniformK` / `_cbar_final`)

The scale bundle the count keystone consumes at the op point
(`zN := opZ N`, `yN := opY N`, `zR := N^{1/8}`, `yR := N^{1/3}`).  The
post-fix `hlogNz : log N ≤ 3·log(opY N) + log(opZ N)` is satisfiable here with
margin `≈ log N / 8 ≥ 12` (via `op_at_facts`'s floor-log lower bounds), resolving
the G-COUNT-2 op-satisfiability catch.  The Ifun/hbjs error terms in
`goldTripleSum_le_cbar_final`'s conclusion still need the `o(1)` fold to the
clean `hcount_seam` shape — that fold is the FinLed-tier Class-C follow-up
(see the module note and the G-OP report). -/
theorem gold_op_count_rows : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    6 ≤ opY N ∧
    Real.log N ≤ 3 * Real.log (opY N) + Real.log (opZ N) ∧
    (1 : ℝ) < (N : ℝ) ∧
    (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) ∧
    (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) ∧
    Real.log ((N : ℝ) ^ ((1 : ℝ) / 8)) = Real.log N / 8 ∧
    Real.log ((N : ℝ) ^ ((1 : ℝ) / 3)) = Real.log N / 3 ∧
    (opZ N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) ∧
    (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (opZ N : ℝ) + 1 ∧
    (opY N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) ∧
    (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (opY N : ℝ) + 1 := by
  obtain ⟨xF, hF⟩ := op_at_facts
  refine ⟨max xF (10 ^ 48), fun N hN => ?_⟩
  have hxF : xF ≤ N := le_trans (le_max_left _ _) hN
  have hx48 : 10 ^ 48 ≤ N := le_trans (le_max_right _ _) hN
  have hx48R : (10 : ℝ) ^ 48 ≤ (N : ℝ) := by exact_mod_cast hx48
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by positivity) hx48R
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := le_trans (by norm_num) hx48R
  obtain ⟨hL96, hlogN_zN, hlogN_yN, hZlog_le, hYlog_le, hZ1, hY1, hZlog_ge, hYlog_ge⟩ :=
    hF N hxF
  -- `6 ≤ opY N` (via `96 ≤ log N ≤ opY N`)
  have hy6 : 6 ≤ opY N := by
    have : (6 : ℝ) ≤ (opY N : ℝ) := le_trans (by norm_num) (le_trans hL96 hlogN_yN)
    exact_mod_cast this
  -- `hlogNz` (the resolved op-satisfiability row)
  have hlogNz : Real.log N ≤ 3 * Real.log (opY N) + Real.log (opZ N) := by
    linarith [hYlog_ge, hZlog_ge, hL96]
  -- the rpow scale rows
  have hlogz : Real.log ((N : ℝ) ^ ((1 : ℝ) / 8)) = Real.log N / 8 := by
    rw [Real.log_rpow hNpos]; ring
  have hlogy : Real.log ((N : ℝ) ^ ((1 : ℝ) / 3)) = Real.log N / 3 := by
    rw [Real.log_rpow hNpos]; ring
  have hzR2 : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
    have hmono : ((10 : ℝ) ^ 48) ^ ((1 : ℝ) / 8) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) :=
      Real.rpow_le_rpow (by positivity) hx48R (by norm_num)
    have heq : ((10 : ℝ) ^ 48) ^ ((1 : ℝ) / 8) = (10 : ℝ) ^ 6 := by
      rw [← Real.rpow_natCast (10 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10),
        show ((48 : ℕ) : ℝ) * (1 / 8) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [heq] at hmono; linarith
  have hzRyR : (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
  -- the floor rows
  have hzN_le : (opZ N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [opZ]; exact Nat.floor_le (Real.rpow_nonneg hNpos.le _)
  have hzN_ge : (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (opZ N : ℝ) + 1 := by
    rw [opZ]; exact (Nat.lt_floor_add_one _).le
  have hyN_le : (opY N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [opY]; exact Nat.floor_le (Real.rpow_nonneg hNpos.le _)
  have hyN_ge : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (opY N : ℝ) + 1 := by
    rw [opY]; exact (Nat.lt_floor_add_one _).le
  have hx1 : (1 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hx48R
  exact ⟨hy6, hlogNz, hx1, hzR2, hzRyR, hlogz, hlogy, hzN_le, hzN_ge, hyN_le, hyN_ge⟩

/-! ## Part 9 — the A₃/BV block conversion-error row at the op point (`gold_hCE_at_op`)

The `hCE` slot of `gold_hBVblocksW_of_generalBV` at the operating point
(`Q := opQ`, `Ps := goldOpPs N`, `z := opZ N`, `y := opY N`, `w' := opW'`,
`ε₀ := N`), with the modulus/coprimality/window hypotheses discharged from the
landed op facts.  The `hHD` (honest-disc) half and the full survivor-price rows
of `gold_hBVblocksW_discharge'` are the remaining Class-C annulus-pricing
instantiation (see the G-OP report). -/
theorem gold_op_hCE : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N → ∀ (QR : ℝ) (Dlev : ℕ),
    (∑ j ∈ Finset.range (maxBlock N (opZ N) (N : ℝ) + 1), ∑ d ∈ Nat.divisors (goldOpPs N),
        if (d : ℝ) < QR * Dlev then goldBlockConvErrW N (opZ N) (opY N) (N : ℝ) j opQ d else 0)
      ≤ nuChen opQ * (∑ d ∈ Nat.divisors (goldOpPs N), nuChen d)
          * goldTripleSum N (opZ N) (opY N) / ((opZ N : ℝ) - 1) := by
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max xt 4, fun N hN QR Dlev => ?_⟩
  obtain ⟨_, _, hw'z, hz3, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := htower N (by omega)
  have hQfac : ∀ p ∈ opQ.primeFactors, p < opW' := fun p hp => by
    rw [opf_Q_primeFactors] at hp; exact Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  exact gold_hCE_at_op N (opZ N) (opY N) opQ (goldOpPs N) opW' QR Dlev
    (goldOpPs_squarefree N) (by omega) (by omega) (by have := opf_Q2; omega)
    (gold_opQ_coprime_Ps N) hQfac (goldOpPs_py N) hw'z

/-! ## Part 10 — the `goldbach_of_hypotheses_W` consumption interface (for `G-ASM`)

The terminal node `G-ASM` composes an `H`-provider for `goldbach_of_hypotheses_W`,
the Goldbach analogue of `Salt.Chen.chen_of_hypotheses_W` (`Assembly.lean:715`).
That headline consumes, for every threshold `X`, an operating-point witness tuple
`(x, z, P, y, Q, a, w')` with three main terms `(mainA1, mainA2, mainA3)` and the
split hypotheses + ledger positivity.  At the Goldbach op point the slots are
filled as follows (all names below are this file's, unless noted):

* `x := N`, `z := opZ N` (`goldOpZ`), `y := opY N` (`goldOpY`),
  `P := goldOpP N`, `Q := opQ`, `a :=` the `gold_op_residue` witness, `w' := opW'`.
* scale conjuncts `2 ≤ x`, `2 ≤ z`, `3 ≤ w'`, `x < (y+1)^3`, `X ≤ x/2`,
  `opQ ≤ log N`, `w0R ≤ opZ`, `opZ ≤ opD`, … : the reused `opf_tower` bundle at
  `x := N` (`opf_w'3` for `3 ≤ w'`).
* `Q`-fullness `∀ q prime, q < w' → q ∣ Q` : `opf_Qfull`.
* `P`-fullness `∀ q prime, w' ≤ q → q < z → q ∣ P` : the punctured window — note
  `goldOpP` is punctured (`¬ q ∣ N`), so the fullness conjunct is over the
  survivor primes; supplied via `goldOpP_window` / `goldPs_primeFactors`.
* residue coprimality `Coprime Q (a+2)` and `Coprime Q a`, `Coprime Q P`,
  `Coprime P N` : `gold_op_residue` (the reflected `a`, needs `Even N`),
  `gold_opQ_coprime_P`, `goldOpP_coprime_N`.
* `mainA1 ≤` (the reflected coprime `Λ`-sum) : **`gold_a12_hA1`** (this file).
* the `A₂` upper `mainA2` : **GAP** — see the report; the twin's
  `omegaPrimeSumW`/`omegaPrimeSumW_decomp`/`twinA2W_hcoef` have no landed Goldbach
  carrier, and the design routes `A₂/A₃` through the switch instead
  (`gold_mainA3_of_hBVswitch` + the count seam).
* the `A₃` upper `mainA3` : `gold_mainA3_of_hBVswitch` with `hBVswitch` from
  `gold_hBVswitch_of_generalBV` (its `hCE` half at op is `gold_op_hCE`; the
  `hHD`/survivor-price rows are the remaining Class-C annulus instantiation).
* the count carrier `goldTripleSum N (opZ N) (opY N) ≤ (cbar/2)·(N/log N) + o(1)` :
  `goldTripleSum_le_cbar_final` fed by **`gold_op_count_rows`** (this file); the
  `o(1)` fold to the clean `hcount_seam` shape is the FinLed-tier follow-up. -/

end Salt.Goldbach
