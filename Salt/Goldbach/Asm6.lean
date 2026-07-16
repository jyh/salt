/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Asm5

/-!
# G-ASM §6 — the general-`a` A₁ bundle and the final reduction

* **The A₁ prime-power bridge** (`goldA1PrimeSumW_bridge`): the AP-restricted coprime
  `Λ`-sum minus the prime-power mass `√N·(log₂N)·log N` lower-bounds the `keepG` carrier
  (`A1primeSumW_bridge` mirror; `primePowerMass_le` is window-generic and reused).
* **The general-`a` A₁ bundle** (`gold_hA1_bundle`): `gold_a12_hA1`'s body re-instantiated
  at the parametric residue (the `opf_Qma` slot generalised to `Coprime opQ a`), composed
  with the bridge — `M1G N a ≤ goldA1PrimeSumW` past a threshold.
* **The final reduction** (`chen_goldbach_of_ledger`): the frozen D0 conclusion
  `∃ N₀, ∀ N ≥ N₀, Even N → ∃ p q, N = p + q ∧ p.Prime ∧ IsP2 2 q` from ONE remaining
  analytic bundle — the F2-ledger mirror at the concrete carriers `M1G`/`M2G`/`M3G`.
  Everything else (the three main bundles, the residue witness, the tower rows, the
  survivor extraction) is discharged here.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset Salt.Chen ArithmeticFunction

namespace Salt.Goldbach

/-! ## §A — the A₁ prime-power bridge -/

/-- **The Goldbach Finding-6 bridge.**  The AP-restricted coprime `Λ`-sum, minus the
prime-power mass, lower-bounds the `keepG` A₁ carrier: on prime window points the two
agree, and the discrepancy is supported on non-prime prime powers. -/
theorem goldA1PrimeSumW_bridge (Q a N P : ℕ) (hx : 4 ≤ N) :
    (∑ n ∈ twinWindow N,
        if n % Q = a % Q ∧ Nat.Coprime P (N - n) then vonMangoldt n else 0)
      - Real.sqrt N * (Nat.log 2 N : ℝ) * Real.log N
    ≤ goldA1PrimeSumW Q a N P := by
  have hpt : ∀ n ∈ twinWindow N,
      (if n % Q = a % Q ∧ Nat.Coprime P (N - n) then vonMangoldt n else 0)
        - vonMangoldt n * keepG Q a P N n
      ≤ (if ¬ n.Prime then vonMangoldt n else 0) := by
    intro n _
    have hite0 : 0 ≤ (if ¬ n.Prime then vonMangoldt n else 0) := by
      split_ifs <;> simp [vonMangoldt_nonneg]
    by_cases hk : n % Q = a % Q ∧ Nat.Coprime P (N - n)
    · rw [if_pos hk]
      by_cases hp : n.Prime
      · have hkeep : keepG Q a P N n = 1 := keepG_eq_one_iff.mpr ⟨hp, hk.2, hk.1⟩
        rw [hkeep, mul_one, sub_self]
        exact hite0
      · have hkeep : keepG Q a P N n = 0 := by
          unfold keepG
          rw [if_neg (by rintro ⟨hp', -, -⟩; exact hp hp')]
        rw [hkeep, mul_zero, sub_zero, if_pos hp]
    · rw [if_neg hk]
      have h0 : 0 ≤ vonMangoldt n * keepG Q a P N n :=
        mul_nonneg vonMangoldt_nonneg (keepG_nonneg Q a P N n)
      linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib] at hsum
  have hmass := primePowerMass_le hx
  have hA1 : ∑ n ∈ twinWindow N, vonMangoldt n * keepG Q a P N n
      = goldA1PrimeSumW Q a N P := rfl
  rw [hA1] at hsum
  linarith [hsum, hmass]

/-! ## §B — the A₁ main-term carrier and the general-`a` bundle -/

/-- The A₁ main-term carrier: the `gold_a12_hA1` lower bound at the op proofs, minus the
prime-power mass (the `M1` mirror). -/
noncomputable def M1G (N a : ℕ) : ℝ :=
  (goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N) (goldOpP_odd N)).totalMass *
      (Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
            (goldOpP_squarefree N) (goldOpP_odd N)) *
        (fchain (maxDepth (goldA1SieveW opQ a N (goldOpP N)
              (goldOpP_squarefree N) (goldOpP_odd N))) (logRatio (opZ N) (opD N))
          - opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opZ N) (opD N))))
    - (N : ℝ) / (Real.log N) ^ 10
    - Real.sqrt N * (Nat.log 2 N : ℝ) * Real.log N

set_option linter.unusedVariables false in
/-- **The general-`a` A₁ bundle** — `gold_a12_hA1` re-instantiated at the parametric
residue (item 3 of the G-ASM job), composed with the Finding-6 bridge. -/
theorem gold_hA1_bundle : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    ∀ a : ℕ, Nat.Coprime opQ a →
    M1G N a ≤ goldA1PrimeSumW opQ a N (goldOpP N) := by
  obtain ⟨B, C, hB, hC, hbvfun⟩ := gold_a12_hBV_A1
  obtain ⟨x₂, hlev⟩ := a12_level B hB
  obtain ⟨x₃, hcl⟩ := a12_close C hC
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max (max (max x₂ x₃) xt) 4, fun N hN a hQa => ?_⟩
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
  have hBV := hbvfun opQ a N (opZ N) (opD N) (goldOpP N) opEps ((opQ : ℝ))
    (goldOpP_squarefree N) (goldOpP_odd N) hPz hPlow hx4 opf_eps_pos a12_hw0 hwz
    hQ1 (gold_opQ_coprime_P N) hQa (goldOpP_coprime_N N) hQlevR hD1 hlevel hclose
  have hsup := gold_A1_lower_B_W opQ a N (opZ N) (opD N) (goldOpP N) opEps (1 + opEps)
    ((opQ : ℝ)) (goldOpP_squarefree N) (goldOpP_odd N) hPz hPlow hz2 hzD hD1 hStop
    opf_eps_pos a12_hw0 (le_refl _) a12_eps_lt_249
    (stepHypWPC_sharpB opEps opf_eps_pos.le a12_eps_le_1000)
    (h4_cond_of_base opEps (1 + opEps) opf_eps_pos.le (le_refl _)) hQlevR hBV
  have hbridge := goldA1PrimeSumW_bridge opQ a N (goldOpP N) hx4
  rw [M1G]
  linarith [hsup, hbridge]

/-! ## §C — the final reduction: `chen_goldbach` from the F2 ledger -/

/-- **The final reduction.**  The frozen D0 conclusion from ONE remaining analytic
bundle: the F2-ledger positivity at the concrete carriers `M1G`/`M2G`/`M3G` (the
`normalized_package`-mirror obligation).  All structural wiring — the three main
bundles, the residue witness, the tower rows, the razor, the survivor — is
discharged. -/
theorem chen_goldbach_of_ledger
    (hL : ∃ (R : ℝ) (x₁ : ℕ), 0 ≤ R ∧ ∀ N : ℕ, x₁ ≤ N → R ≤ Real.log N → Even N →
        ∀ a : ℕ, a ≤ N → Nat.Coprime opQ a → Nat.Coprime opQ (N - a) →
        0 < M1G N a - M2G N a / 2 - M3G N / 2
          - Real.log N * (N : ℝ) / ((opZ N : ℝ) - 1) / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, N = p + q ∧ p.Prime ∧ IsP2 2 q := by
  obtain ⟨R, xl, hR0, hld⟩ := hL
  obtain ⟨x1, h1⟩ := gold_hA1_bundle
  obtain ⟨x2, h2⟩ := gold_hA2_bundle
  obtain ⟨CT, x3, hCT0, h3⟩ := gold_hA3_bundle
  obtain ⟨xt, -, htower⟩ := opf_tower
  obtain ⟨xsc, hsc⟩ := gold_op_scales
  apply goldbach_of_hypotheses_W
  refine ⟨max (max (max x1 x2) (max x3 xl)) (max (max xt xsc)
    (Nat.ceil (Real.exp (max R CT)))), fun N hN hEven => ?_⟩
  have hx1 : x1 ≤ N := by omega
  have hx2 : x2 ≤ N := by omega
  have hx3 : x3 ≤ N := by omega
  have hxl : xl ≤ N := by omega
  have hxt : xt ≤ N := by omega
  have hxsc : xsc ≤ N := by omega
  have hceil : Nat.ceil (Real.exp (max R CT)) ≤ N := by omega
  have hexpN : Real.exp (max R CT) ≤ (N : ℝ) := Nat.ceil_le.mp hceil
  have hlogthr : max R CT ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos _) hexpN
    rwa [Real.log_exp] at h
  have hRle : R ≤ Real.log N := le_trans (le_max_left _ _) hlogthr
  have hCTle : CT ≤ Real.log N := le_trans (le_max_right _ _) hlogthr
  obtain ⟨hQlog, hwz, hw'z, hz3, hzD, hD1, hzy, hyx2, hcube, hStopA1, hS2', hDlev2,
    hDhalf, hDlevlo, hRange, hDlevhalf, hx4⟩ := htower N hxt
  obtain ⟨hN2, hz1, -, -, -, -, -, -, -, -, -, -, -⟩ := hsc N hxsc
  have hQN : opQ ≤ N := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have h0 : 0 < N := by omega
      exact_mod_cast h0
    have hloglt : Real.log N ≤ (N : ℝ) - 1 := Real.log_le_sub_one_of_pos hNpos
    have hQltN : (opQ : ℝ) ≤ (N : ℝ) := by linarith [hQlog]
    exact_mod_cast hQltN
  obtain ⟨a, haQ, hQa, hQNa, -⟩ := gold_op_residue N hEven hQN
  have haN : a ≤ N := by omega
  have hzN : 2 * opZ N ≤ N := by
    have h2 : opZ N ≤ N / 2 := le_trans hzy hyx2
    omega
  exact ⟨opZ N, goldOpP N, opY N, opQ, a, opW', M1G N a, M2G N a, M3G N,
    hN2, (by omega : 2 ≤ opZ N), hcube, haN, hzN, opf_Qfull, goldOpP_full' N, hQNa,
    h1 N hx1 a hQa, h2 N hx2 a haN hQa hQNa, h3 N hx3 hCTle hEven a haN hQa hQNa,
    hld N hxl hRle hEven a haN hQa hQNa⟩

end Salt.Goldbach
