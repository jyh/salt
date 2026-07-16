/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Asm4

/-!
# G-ASM §5 — the Λ-bridge and the A₃ bundle at the operating point

* **The Λ-bridge** (`goldTriplePrimeSumW_le_sifted`): the W-carrier A₃ Λ-sum is dominated
  by `log N ·` the W-switch sifted sum — the `triplePrimeSum_le_sifted` mirror at the
  reflected value with the AP filter.  Each kept window point with the triple pattern at
  `N − n` is an admissible `goldTripleSet` member (`z ≤ p₁` via the punctured split
  bridge) and survives the switch (`n` prime `≥ N/2 ≥ y`).  The bottom-half constraint
  `N − n ≤ N/2` needs `Even N`.
* **The A₃ bundle** (`gold_hA3_bundle`): the bridge + the closed block-BV terminal
  (`gold_hBVblocksW_at_op_closed`, §3) through the composed A₃ terminal
  `gold_mainA3_of_block_remainders_W`, at the op witnesses and a general residue `a` —
  concluding `goldTriplePrimeSumW ≤ M3G N` past the exposed threshold.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset Salt.Chen ArithmeticFunction

namespace Salt.Goldbach

/-! ## §A — the Λ-bridge -/

/-- **The Goldbach Λ-bridge (the W carrier).**  Mirrors `triplePrimeSum_le_sifted`: the
kept, AP-filtered window mass with the triple pattern at `N − n` is dominated by
`log N ·` the W-switch sifted sum. -/
theorem goldTriplePrimeSumW_le_sifted {N z y Q a w' P Ps : ℕ}
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPsy : ∀ p ∈ Ps.primeFactors, p < y)
    (hN2 : 2 ≤ N) (hEven : Even N) (hyx2 : y ≤ N / 2) (haN : a ≤ N) (hzN : 2 * z ≤ N)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → ¬ q ∣ N → q ∣ P)
    (hQNa : Nat.Coprime Q (N - a)) :
    goldTriplePrimeSumW Q a N P y
      ≤ Real.log N * (goldSwitchSieveW N z y Q a Ps hPs hPodd).siftedSum := by
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  rw [goldTriplePrimeSumW, goldSwitchSieveW_siftedSum, Finset.mul_sum]
  have hfold : ∑ n ∈ (twinWindow N).filter (fun n => n % Q = a % Q),
      vonMangoldt n * keepG Q a P N n * tripleT y (N - n)
      = ∑ n ∈ twinWindow N, vonMangoldt n * keepG Q a P N n * tripleT y (N - n) := by
    apply Finset.sum_filter_of_ne
    intro n _ hne
    by_contra hmod
    have h0 : keepG Q a P N n = 0 := by
      unfold keepG
      rw [if_neg (by rintro ⟨-, -, h⟩; exact hmod h)]
    rw [h0] at hne
    simp at hne
  rw [← hfold]
  apply Finset.sum_le_sum
  intro n hn
  have hnf := Finset.mem_filter.mp hn
  have hAP : n % Q = a % Q := hnf.2
  have hnw := hnf.1
  rw [twinWindow, Finset.mem_Icc] at hnw
  by_cases hk : Nat.Prime n ∧ Nat.Coprime P (N - n)
  · by_cases htp : TripleP y (N - n)
    · -- the survivor case
      have hkeep1 : keepG Q a P N n = 1 := keepG_eq_one_iff.mpr ⟨hk.1, hk.2, hAP⟩
      have htT : tripleT y (N - n) = 1 := tripleT_eq_one htp
      have hcopPs : Nat.Coprime Ps n := by
        rw [Nat.coprime_comm]
        refine (hk.1.coprime_iff_not_dvd).mpr fun hdvd => ?_
        have hmem : n ∈ Ps.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hk.1, hdvd, hPs.ne_zero⟩
        have := hPsy n hmem
        omega
      have hΛle : vonMangoldt n ≤ Real.log N := by
        refine le_trans vonMangoldt_le_log (Real.log_le_log ?_ ?_)
        · exact_mod_cast hk.1.one_lt.le
        · exact_mod_cast (by omega : n ≤ N)
      have hnN : n ≤ N := by omega
      have hzn : z ≤ n := by omega
      have hcopz := factors_ge_z_of_sift_G haN hnN hk.1 hzn hQfull hPfull' hQNa hk.2 hAP
      have hge1 : (1 : ℝ) ≤ goldACount N z y n := by
        obtain ⟨p₁, p₂, p₃, hp1, hp2, hp3, hprod, hp1y, hyp2, hp23⟩ := htp
        have hm0 : 0 < N - n := by omega
        have hp1dvd : p₁ ∣ (N - n) := ⟨p₂ * p₃, by rw [hprod]; ring⟩
        have hp2dvd : p₂ ∣ (N - n) := ⟨p₁ * p₃, by rw [hprod]; ring⟩
        have hp3dvd : p₃ ∣ (N - n) := ⟨p₁ * p₂, by rw [hprod]; ring⟩
        have hp1mem : p₁ ∈ (N - n).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp1, hp1dvd, by omega⟩
        have hzp1 : z ≤ p₁ := hcopz p₁ hp1mem
        have hub : N - n ≤ N / 2 := by
          obtain ⟨k, hkN⟩ := hEven
          omega
        have hp1N : p₁ ≤ N := le_trans (Nat.le_of_dvd hm0 hp1dvd) (by omega)
        have hp2N : p₂ ≤ N := le_trans (Nat.le_of_dvd hm0 hp2dvd) (by omega)
        have hp3N : p₃ ≤ N := le_trans (Nat.le_of_dvd hm0 hp3dvd) (by omega)
        have ht : (p₁, p₂, p₃) ∈ goldTripleSet N z y := by
          rw [goldTripleSet, Finset.mem_filter]
          refine ⟨?_, hzp1, hp1y, hyp2, hp23, hp1, hp2, hp3, ?_, ?_⟩
          · rw [Finset.mem_product, Finset.mem_product]
            refine ⟨?_, ?_, ?_⟩ <;> rw [Finset.mem_Icc]
            · exact ⟨hp1.one_lt.le, hp1N⟩
            · exact ⟨hp2.one_lt.le, hp2N⟩
            · exact ⟨hp3.one_lt.le, hp3N⟩
          · show 2 ≤ prod3 (p₁, p₂, p₃)
            rw [prod3, ← hprod]
            omega
          · show prod3 (p₁, p₂, p₃) ≤ N / 2
            rw [prod3, ← hprod]
            exact hub
        have hmem : (p₁, p₂, p₃) ∈ (goldTripleSet N z y).filter
            (fun t => prod3 t = N - n) := by
          rw [Finset.mem_filter]
          exact ⟨ht, by show prod3 (p₁, p₂, p₃) = N - n; rw [prod3, ← hprod]⟩
        rw [goldACount]
        have hcard : 0 < ((goldTripleSet N z y).filter
            (fun t => prod3 t = N - n)).card :=
          Finset.card_pos.mpr ⟨_, hmem⟩
        exact_mod_cast hcard
      rw [hkeep1, htT, mul_one, mul_one, if_pos hcopPs]
      calc vonMangoldt n ≤ Real.log N := hΛle
        _ = Real.log N * 1 := (mul_one _).symm
        _ ≤ Real.log N * goldACount N z y n := mul_le_mul_of_nonneg_left hge1 hlogN
    · -- no triple pattern: the LHS term vanishes
      have h0 : tripleT y (N - n) = 0 := by unfold tripleT; rw [if_neg htp]
      rw [h0, mul_zero]
      refine mul_nonneg hlogN ?_
      split_ifs
      · exact goldACount_nonneg N z y n
      · exact le_refl 0
  · -- not kept: the LHS term vanishes
    have hkeep0 : keepG Q a P N n = 0 := by
      unfold keepG
      rw [if_neg (by rintro ⟨h1, h2, -⟩; exact hk ⟨h1, h2⟩)]
    rw [hkeep0, mul_zero, zero_mul]
    refine mul_nonneg hlogN ?_
    split_ifs
    · exact goldACount_nonneg N z y n
    · exact le_refl 0

/-! ## §B — the carriers `M2G`/`M3G` and the A₃ bundle at op -/

/-- The A₂ main-term carrier: the `gold_a12_hA2` upper bound at the op proofs. -/
noncomputable def M2G (N a : ℕ) : ℝ :=
  ((goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N) (goldOpP_odd N)).totalMass
        * Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
            (goldOpP_squarefree N) (goldOpP_odd N)))
      * (A2grid ((Finset.Icc (opZ N) (opY N)).filter (fun p => p.Prime ∧ ¬ p ∣ N))
            (opZ N) (opD N)
            (fun p => maxDepth (goldA2SieveW opQ a N (goldOpP N) p
                (goldOpP_squarefree N) (goldOpP_odd N)))
          + ∑ p ∈ (Finset.Icc (opZ N) (opY N)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
              (1 / ((p : ℝ) - 1))
                * (opEps * CsharpB opEps * Real.exp 2
                    * hBJS (logRatio (opZ N) (cdiv (opD N) p))))
    + (N : ℝ) / (Real.log N) ^ 10

/-- The A₂ bundle at a general residue — `gold_a12_hA2` re-expressed at `M2G`. -/
theorem gold_hA2_bundle : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    ∀ a : ℕ, a ≤ N → Nat.Coprime opQ a → Nat.Coprime opQ (N - a) →
    goldOmegaPrimeSum opQ a N (goldOpP N) (opY N) ≤ M2G N a := by
  obtain ⟨x₁, h⟩ := gold_a12_hA2
  exact ⟨x₁, fun N hN a haN hQa hQNa => h N hN a haN hQa hQNa⟩

/-- The A₃ main-term carrier: the `gold_mainA3_of_block_remainders_W` output at the op
witnesses (`M3` mirror). -/
noncomputable def M3G (N : ℕ) : ℝ :=
  Real.log N *
      (goldTripleSum N (opZ N) (opY N) / (opQ.totient : ℝ)
          * Salt.BrunLower.W (goldSwitchSieve N (opZ N) (opY N) (goldOpPs N)
              (goldOpPs_squarefree N) (goldOpPs_odd N))
          * (Fchain (maxDepth (goldSwitchSieve N (opZ N) (opY N) (goldOpPs N)
                (goldOpPs_squarefree N) (goldOpPs_odd N))) (logRatio (opY N) (opDlev N))
            + opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opY N) (opDlev N)))
        + (N : ℝ) / (Real.log N) ^ 10)

/-- The punctured `[w', z)` fullness of `goldOpP` (the survivor primes divide it). -/
theorem goldOpP_full' (N : ℕ) :
    ∀ q, q.Prime → opW' ≤ q → q < opZ N → ¬ q ∣ N → q ∣ goldOpP N := by
  intro q hq hwq hqz hqN
  have hmem : q ∈ (goldOpP N).primeFactors := by
    rw [goldOpP, goldPs_primeFactors]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hwq, hqz⟩, hq, hqN⟩
  exact Nat.dvd_of_mem_primeFactors hmem

/-- **The A₃ bundle at op** — the Λ-bridge + the closed block-BV terminal through the
composed A₃ terminal, at a general residue `a`.  The exposed `CT` is §3's threshold. -/
theorem gold_hA3_bundle : ∃ (CT : ℝ) (x₁ : ℕ), 0 ≤ CT ∧ ∀ N : ℕ, x₁ ≤ N →
    CT ≤ Real.log N → Even N →
    ∀ a : ℕ, a ≤ N → Nat.Coprime opQ a → Nat.Coprime opQ (N - a) →
    goldTriplePrimeSumW opQ a N (goldOpP N) (opY N) ≤ M3G N := by
  obtain ⟨CT, xB, hCT0, hclosed⟩ := gold_hBVblocksW_at_op_closed
  obtain ⟨xt, -, htower⟩ := opf_tower
  obtain ⟨xsc, hsc⟩ := gold_op_scales
  refine ⟨CT, max (max xB xt) xsc, hCT0, ?_⟩
  intro N hN hthr hEven a haN hQa hQNa
  have hxB : xB ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hxt : xt ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hxsc : xsc ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hQlog, hwz, hw'z, hz3, hzD, hD1, hzy, hyx2, hcube, hStopA1, hS2', hDlev2,
    hDhalf, hDlevlo, hRange, hDlevhalf, hx4⟩ := htower N hxt
  obtain ⟨hN2, hz1, -, -, -, -, -, -, -, -, -, -, -⟩ := hsc N hxsc
  have hzN : 2 * opZ N ≤ N := by
    have h2 : opZ N ≤ N / 2 := le_trans hzy hyx2
    omega
  have hε₀ : (0 : ℝ) < (N : ℝ) := by
    have h0 : 0 < N := by omega
    exact_mod_cast h0
  have hbridge := goldTriplePrimeSumW_le_sifted (z := opZ N)
    (goldOpPs_squarefree N) (goldOpPs_odd N) (goldOpPs_py N)
    hN2 hEven hyx2 haN hzN opf_Qfull (goldOpP_full' N) hQNa
  have hBV := hclosed N hxB hthr a haN hQa hQNa
  exact gold_mainA3_of_block_remainders_W N (opZ N) (opY N) opQ a (goldOpPs N) (opDlev N)
    (N : ℝ) opEps (1 + opEps) 1 (goldTriplePrimeSumW opQ a N (goldOpP N) (opY N))
    hz1 hε₀ (goldOpPs_squarefree N) (goldOpPs_odd N) (goldOpPs_py N) (goldOpPs_plow N)
    hDlev2 (le_refl 1) opf_eps_pos opf_w0R3 a12_eps_le_1000 (le_refl _)
    (h4_cond_of_base opEps (1 + opEps) opf_eps_pos.le (le_refl _)) hS2' hbridge hBV

end Salt.Goldbach
