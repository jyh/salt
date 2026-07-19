/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cCore

/-!
# HB-L2c core surgery — Wave 2b: the `E_R` mirror families (node HB-L2c, rung R6)

The second summand of the exact overshoot, priced.  `overshootExact` splits as

`overshootExact χ n = (Λ̃−Λ)(n)·Λ̃(n+2)  +  Λ(n)·(Λ̃−Λ)(n+2)`,

the first summand being `E_L` (Wave 2a, `L2cEL.lean`) and the second being

`E_R χ z x = Σ_{n∈W} Λ(n)·(Λ̃−Λ)(n+2)`  (`E_R`),

this file's target.  Here the **left** factor `Λ(n)` is a clean prime-power weight
(nonzero only when `n` is a prime power `p^k`), and the **difference** sits on the
`n+2` side.  So `E_R` decomposes by the shape of `n` (not `n+2`):

* `n = p^k` with `k ≥ 2` (a *proper* prime power) — the **squarefull junk** row
  `ER_squarefull_junk`: `≤ 2·√(2x)·L'²·e^{0.7·z₀}` (the count of proper prime powers
  in `(x,2x]` is `≤ √(2x)`, each term capped by `Λ(n)·Λ̃(n+2) ≤ L'·e^{(log2)z₀}L'`).
* `n = p` prime (`k = 1`) — the **mirror families** `ER_T1'`/`ER_T2'`/`ER_T3'`/`ER_Tsw'`,
  the `E_L` `T1`–`T-sw` analysis with the roles of `n`, `n+2` swapped (RESTATED, not
  symmetry-hand-waved: `E_R` is not symmetric in `n ↔ n+2` because the window filter is
  not).  The left weight is `log p ≤ L'`; the right is the classified difference.
* `n` not a prime power — `Λ(n) = 0`, the term vanishes.

Single-writer file (`L2cER.lean`); it imports the Wave-1 surface `L2cCore` and touches
no other file.  It is NOT yet in the `Salt.HB.All` manifest (Wave 3's responsibility).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — the `E_R` sum and its shared window facts -/

/-- **The `E_R` overshoot sum.**  `Σ_{n∈W} Λ(n)·(Λ̃−Λ)(n+2)` — the second summand of the
    exact overshoot, summed over the honest window `W = l2cWindow χ z x`. -/
noncomputable def E_R (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ l2cWindow χ z x, Λ n * (LamTilde χ (n + 2) - Λ (n + 2))

/-- Window membership unpacked: `n ∈ (x,2x]` and `(n(n+2), q·P) = 1`. -/
lemma l2cWindow_mem_iff (χ : DirichletCharacter ℂ q) (z x n : ℕ) :
    n ∈ l2cWindow χ z x ↔
      (x < n ∧ n ≤ 2 * x) ∧ Nat.Coprime (n * (n + 2)) (q * excPrimorial χ z) := by
  simp only [l2cWindow, Finset.mem_filter, Finset.mem_Ioc]

/-- On a window element, `n+2` is coprime to `q`. -/
lemma l2cWindow_np2_coprime_q (χ : DirichletCharacter ℂ q) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : Nat.Coprime (n + 2) q := by
  rw [l2cWindow_mem_iff] at hn
  have h1 : Nat.Coprime (n + 2) (q * excPrimorial χ z) :=
    Nat.Coprime.coprime_dvd_left (Dvd.intro_left n rfl) hn.2
  exact Nat.Coprime.coprime_dvd_right (dvd_mul_right q _) h1

/-- **The `Λ̃(n+2)` window cap.**  For a window element `n`, `Λ̃(n+2) ≤ e^{(log2)z₀}·L'`
    (the roughness of `n+2` inherited from the window feeds `lamTilde_cap`). -/
lemma l2cWindow_lamTilde_np2_cap (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz2 : 2 ≤ z) {n : ℕ} (hn : n ∈ l2cWindow χ z x) :
    LamTilde χ (n + 2) ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x := by
  have hmem := (l2cWindow_mem_iff χ z x n).mp hn
  refine lamTilde_cap χ hsq z x hz2 (by omega) (l2cWindow_np2_coprime_q χ hn)
    (by omega) ?_
  intro p hp hpd hchi
  refine l2cWindow_roughness χ z x hn hp ?_ hchi
  exact hpd.mul_left n

/-- On a window element, the left weight is capped: `Λ(n) ≤ log n ≤ L'`.  Shared by the
    squarefull junk and every prime-family bound (`log p ≤ L'`). -/
lemma l2cWindow_vonMangoldt_cap (χ : DirichletCharacter ℂ q) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : Λ n ≤ Lwin x := by
  have hb := (l2cWindow_mem_iff χ z x n).mp hn
  refine le_trans vonMangoldt_le_log ?_
  rw [Lwin]
  refine Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) ?_
  have : (n : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hb.1.2
  linarith

/-! ## §1 — the proper-prime-power count `≤ √(2x)` -/

/-- **Proper prime powers are sparse.**  The number of `n ∈ (x,2x]` that are prime powers
    but not prime (`n = p^k`, `k ≥ 2`) is `≤ ⌊√(2x)⌋` — the `n ↦ minFac n` map is
    injective on `(x,2x]` (a dyadic range holds one power of each `p`) into
    `{p : p² ≤ 2x} ⊆ [1, √(2x)]`. -/
lemma properPrimePow_count (x : ℕ) :
    (((Finset.Ioc x (2 * x)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℕ)
      ≤ Nat.sqrt (2 * x) := by
  classical
  -- destructuring: a set element is `p^k` with `p` prime, `k ≥ 2`, `minFac = p`
  have hdes : ∀ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
      ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ p ^ k = n ∧ n.minFac = p := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨p, k, hp, hk, hpk⟩ := hn.2.1
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    have hk1 : k ≠ 1 := by
      rintro rfl; exact hn.2.2 (by rw [← hpk, pow_one]; exact hp')
    exact ⟨p, k, hp', by omega, hpk, by rw [← hpk]; exact hp'.pow_minFac (by omega)⟩
  have hle : ((Finset.Ioc x (2 * x)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)).card
      ≤ (Finset.Icc 1 (Nat.sqrt (2 * x))).card := by
    refine Finset.card_le_card_of_injOn Nat.minFac ?_ ?_
    · intro n hn
      have hnf := Finset.mem_coe.mp hn
      obtain ⟨p, k, hp, hk, hpk, hmf⟩ := hdes n hnf
      rw [Finset.mem_filter, Finset.mem_Ioc] at hnf
      rw [Finset.mem_coe, Finset.mem_Icc]
      refine ⟨by rw [hmf]; exact hp.pos, ?_⟩
      rw [hmf, Nat.le_sqrt']
      have hp2n : p ^ 2 ≤ n := by
        rw [← hpk]; exact Nat.pow_le_pow_right hp.pos hk
      omega
    · intro n hn n' hn' heq
      obtain ⟨p, k, hp, hk, hpk, hmf⟩ := hdes n (Finset.mem_coe.mp hn)
      obtain ⟨p', k', hp', hk', hpk', hmf'⟩ := hdes n' (Finset.mem_coe.mp hn')
      have hpp' : p = p' := by rw [← hmf, ← hmf', heq]
      subst hpp'
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ioc] at hn hn'
      -- both `p^k, p^{k'} ∈ (x,2x]`; the dyadic range forces `k = k'`
      have hkey : ∀ a b : ℕ, a ≤ b → p ^ b ≤ 2 * x → x < p ^ a → a = b := by
        intro a b hab hb ha
        by_contra hne
        have hab' : a + 1 ≤ b := by omega
        have hpow : p ^ (a + 1) ≤ p ^ b := Nat.pow_le_pow_right hp.pos hab'
        rw [pow_succ] at hpow
        have h2 : 2 * p ^ a ≤ p ^ a * p := by
          have hp2 := hp.two_le
          calc 2 * p ^ a = p ^ a * 2 := by ring
            _ ≤ p ^ a * p := by gcongr
        omega
      have hkk : k = k' := by
        rcases le_total k k' with h | h
        · exact hkey k k' h (by rw [hpk']; exact hn'.1.2) (by rw [hpk]; exact hn.1.1)
        · exact (hkey k' k h (by rw [hpk]; exact hn.1.2) (by rw [hpk']; exact hn'.1.1)).symm
      rw [← hpk, ← hpk', hkk]
  refine hle.trans ?_
  rw [Nat.card_Icc]
  omega

/-! ## §2 — the squarefull junk row (`k ≥ 2`) -/

/-- **The `E_R` squarefull junk row.**  The proper-prime-power part of `E_R`
    (`n = p^k`, `k ≥ 2`) is bounded by `2·√(2x)·L'²·e^{0.7·z₀}`: the count is `≤ √(2x)`
    (`properPrimePow_count`), each term `≤ Λ(n)·Λ̃(n+2) ≤ L'·e^{(log2)z₀}·L'`, and
    `log 2 ≤ 0.7`.  This is the `E_R` mirror of `E_L`'s corner squarefull junk. -/
theorem ER_squarefull_junk (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz2 : 2 ≤ z) :
    ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
        Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ 2 * Real.sqrt (2 * x) * Lwin x ^ 2 * Real.exp (0.7 * z0 z x) := by
  classical
  set S := (l2cWindow χ z x).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) with hS
  -- per-term cap: `Λ(n)·(Λ̃−Λ)(n+2) ≤ e^{(log2)z₀}·L'²`
  have hterm : ∀ n ∈ S, Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2 := by
    intro n hn
    have hnw : n ∈ l2cWindow χ z x := Finset.mem_of_mem_filter n hn
    have hΛn_le : Λ n ≤ Lwin x := l2cWindow_vonMangoldt_cap χ hnw
    have hcap := l2cWindow_lamTilde_np2_cap χ hsq hz2 hnw
    calc Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
        ≤ Λ n * LamTilde χ (n + 2) :=
          mul_le_mul_of_nonneg_left (sub_le_self _ vonMangoldt_nonneg) vonMangoldt_nonneg
      _ ≤ Lwin x * (Real.exp (Real.log 2 * z0 z x) * Lwin x) :=
          mul_le_mul hΛn_le hcap (LamTilde_nonneg χ hsq (n + 2)) (Lwin_nonneg x)
      _ = Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2 := by ring
  -- count and scalar facts
  have hcard_nat : S.card ≤ Nat.sqrt (2 * x) :=
    le_trans (Finset.card_le_card
      (Finset.filter_subset_filter _ (l2cWindow_subset χ z x))) (properPrimePow_count x)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * x) := Real.sqrt_nonneg _
  have hcard_real : (S.card : ℝ) ≤ Real.sqrt (2 * x) := by
    have h1 : (S.card : ℝ) ≤ (Nat.sqrt (2 * x) : ℝ) := by exact_mod_cast hcard_nat
    refine h1.trans (Real.le_sqrt_of_sq_le ?_)
    have := Nat.sqrt_le' (2 * x)
    calc ((Nat.sqrt (2 * x) : ℕ) : ℝ) ^ 2 = ((Nat.sqrt (2 * x) ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * x : ℕ) : ℝ) := by exact_mod_cast this
      _ = 2 * (x : ℝ) := by push_cast; ring
  have hLsq : (0 : ℝ) ≤ Lwin x ^ 2 := sq_nonneg _
  have hexp : Real.exp (Real.log 2 * z0 z x) ≤ Real.exp (0.7 * z0 z x) := by
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (z0_nonneg hz2))
    exact le_of_lt (Real.log_two_lt_d9.trans (by norm_num))
  calc ∑ n ∈ S, Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ ∑ _n ∈ S, Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2 :=
        Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.sqrt (2 * x) * (Real.exp (0.7 * z0 z x) * Lwin x ^ 2) := by gcongr
    _ ≤ 2 * Real.sqrt (2 * x) * Lwin x ^ 2 * Real.exp (0.7 * z0 z x) := by
        nlinarith [mul_nonneg (mul_nonneg hsqrt_nonneg hLsq)
          (Real.exp_pos (0.7 * z0 z x)).le]

/-! ## §3 — the `E_R` structural decomposition (prime part + squarefull junk) -/

/-- **`E_R` splits into its prime part and its squarefull-junk part.**  The `¬IsPrimePow`
    terms carry `Λ(n) = 0` and drop; the prime powers split into primes (`k=1`, the
    family part) and proper prime powers (`k≥2`, `ER_squarefull_junk`). -/
lemma E_R_split (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    E_R χ z x
      = (∑ n ∈ (l2cWindow χ z x).filter (fun n => n.Prime),
            Λ n * (LamTilde χ (n + 2) - Λ (n + 2)))
        + ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
            Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) := by
  classical
  rw [E_R, ← Finset.sum_filter_add_sum_filter_not (l2cWindow χ z x) (fun n => n.Prime)]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not
        ((l2cWindow χ z x).filter (fun n => ¬ n.Prime)) (fun n => IsPrimePow n)]
  have hz : ∑ n ∈ ((l2cWindow χ z x).filter (fun n => ¬ n.Prime)).filter
      (fun n => ¬ IsPrimePow n), Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) = 0 := by
    refine Finset.sum_eq_zero (fun n hn => ?_)
    rw [Finset.mem_filter] at hn
    rw [vonMangoldt_eq_zero_iff.mpr hn.2, zero_mul]
  rw [hz, add_zero, Finset.filter_filter]
  refine Finset.sum_congr (Finset.filter_congr (fun n _ => ?_)) (fun _ _ => rfl)
  exact and_comm

/-- **The prime part covers into its two structural subclasses.**  For `n` prime, the
    difference `(Λ̃−Λ)(n+2)` is nonzero only when `n+2` is a `χ=+1` composite
    (`(n+2)₋ = 1`) or has a single `χ=−1` prime-power block with `1 < (n+2)₊`
    (`lamTilde_sub_support_classification`).  These feed `ER_T1'` and `ER_T2'/T3'/Tsw'`
    respectively — the R6 cover, verified disjoint and complete here. -/
lemma ER_prime_cover (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) :
    (∑ n ∈ (l2cWindow χ z x).filter (fun n => n.Prime),
        Λ n * (LamTilde χ (n + 2) - Λ (n + 2)))
      = (∑ n ∈ (l2cWindow χ z x).filter
            (fun n => n.Prime ∧ nMinus χ (n + 2) = 1),
            Λ n * (LamTilde χ (n + 2) - Λ (n + 2)))
        + ∑ n ∈ (l2cWindow χ z x).filter
            (fun n => n.Prime ∧ IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2)),
            Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not ((l2cWindow χ z x).filter (fun n => n.Prime))
        (fun n => nMinus χ (n + 2) = 1)]
  congr 1
  · rw [Finset.filter_filter]
  -- the non-all-plus prime terms: split off the single-block subclass, drop the rest
  rw [← Finset.sum_filter_add_sum_filter_not
        (((l2cWindow χ z x).filter (fun n => n.Prime)).filter (fun n => ¬ nMinus χ (n + 2) = 1))
        (fun n => IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2))]
  have hz : ∑ n ∈ (((l2cWindow χ z x).filter (fun n => n.Prime)).filter
        (fun n => ¬ nMinus χ (n + 2) = 1)).filter
        (fun n => ¬ (IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2))),
      Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) = 0 := by
    refine Finset.sum_eq_zero (fun n hn => ?_)
    simp only [Finset.mem_filter] at hn
    obtain ⟨⟨⟨hnw, _⟩, hne1⟩, hnblk⟩ := hn
    have hcop : Nat.Coprime (n + 2) q := l2cWindow_np2_coprime_q χ hnw
    -- `(Λ̃−Λ)(n+2) = 0`: neither classification branch holds
    have hdiff : LamTilde χ (n + 2) - Λ (n + 2) = 0 := by
      by_contra hd
      obtain ⟨_, _, hcls⟩ :=
        lamTilde_sub_support_classification χ hsq (by omega) hcop hd
      rcases hcls with h1 | h2
      · exact hne1 h1
      · exact hnblk h2
    rw [hdiff, mul_zero]
  rw [hz, add_zero, Finset.filter_filter, Finset.filter_filter]
  refine Finset.sum_congr (Finset.filter_congr (fun n _ => ?_)) (fun _ _ => rfl)
  have hpow : IsPrimePow (nMinus χ (n + 2)) → ¬ nMinus χ (n + 2) = 1 :=
    fun h => h.one_lt.ne'
  tauto

/-! ## §4 — the crude `n`-side cap reduction (mirror of `EL_le_cap`)

The `E_R` mirror of `L2cEL.EL_le_cap`: cap the *left* factor `Λ(n) ≤ L'` (no `e^{z₀}`
needed — the difference is `≥ 0` by `Λ ≤ Λ̃`), leaving the single-variable right overshoot
sum `Σ_{n∈W}(Λ̃−Λ)(n+2)`, restricted to the classified `n+2` support.  This is the *crude*
route (it discards the `n`-side prime weight `log p`); the sharp family budgets that keep it
are the residual — see NOTES. -/

/-- The single-variable right overshoot sum `Σ_{n∈W}(Λ̃−Λ)(n+2)`. -/
noncomputable def rightOvershootSum (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ l2cWindow χ z x, (LamTilde χ (n + 2) - Λ (n + 2))

/-- **The crude `n`-side cap reduction.**  `E_R ≤ L'·Σ_{n∈W}(Λ̃−Λ)(n+2)` (the left prime
    weight `Λ(n) ≤ L'`, the right difference `≥ 0`). -/
lemma E_R_le_cap (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ} :
    E_R χ z x ≤ Lwin x * rightOvershootSum χ z x := by
  rw [E_R, rightOvershootSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn =>
    mul_le_mul_of_nonneg_right (l2cWindow_vonMangoldt_cap χ hn) ?_
  have := vonMangoldt_le_LamTilde χ hsq (n + 2)
  linarith

open Classical in
/-- **The support restriction.**  `rightOvershootSum` restricts to the classified `n+2`
    support: `n+2` composite with either `(n+2)₋ = 1` or `(n+2)₋` a prime power with
    `1 < (n+2)₊` (`lamTilde_sub_support_classification` on `n+2`). -/
lemma rightOvershoot_support (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) :
    rightOvershootSum χ z x
      = ∑ n ∈ (l2cWindow χ z x).filter
          (fun n => ¬ (n + 2).Prime ∧ n + 2 ≠ 1 ∧
            (nMinus χ (n + 2) = 1 ∨ (IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2)))),
          (LamTilde χ (n + 2) - Λ (n + 2)) := by
  rw [rightOvershootSum]
  refine (Finset.sum_filter_of_ne fun n hn hne => ?_).symm
  exact lamTilde_sub_support_classification χ hsq (by omega) (l2cWindow_np2_coprime_q χ hn) hne

/-! ## §5 — NOTES: the residual `E_R` family-budget interface (Wave 3 consumes these)

The `k ≥ 2` (squarefull) junk row is LANDED above (`ER_squarefull_junk`).  The `k = 1`
prime part (`E_R_split`'s first summand) covers into the two subclasses of `ER_prime_cover`,
each priced by the frozen S4 budgets with the roles of `n`, `n+2` swapped — the `E_R` mirror
of `L2cEL`'s residuals.  As in Wave 2a these are **named residuals** (NOT stubbed — no
`sorry`): each is a full joint pair-count fibration (fiber the `n+2` block `w = (n+2)₋` and
the `n`-side prime `p`; count each fiber with `L2cCore.l2c_pair_count_clean` at a
family-specific `(d₁,d₂)`; sum the `Λ(w)`-weights and the `log p ≤ L'` left weight via
Mertens / `PretenseSum`).  The target shapes, verbatim from freeze §S4 (E_R = roles-swapped
T1/T2/T3/T-sw), over `W := l2cWindow χ z x` under the master hypotheses
`(hz100 : 100^16 ≤ z) (hz8 : (Lwin x)^8 ≤ z) (hzx : (z:ℝ)^3 ≤ x)`:

* `ER_T1'_bound` — the all-plus subclass (`(n+2)₋ = 1`, `ER_prime_cover`'s first summand):
  `n = p` prime, `n+2 = M` a `χ=+1` composite (blocks trivial), left weight `log p ≤ L'`;
  fiber the `n+2` all-plus structure at `Zf`, NO `PretenseSum`:
  `≤ Cmain·(x / z0 z x)` (the `J1` row).
* `ER_T2'_bound` — single-block, `n+2` composite plus-part: `p'' := minFac((n+2)₊)`,
  `d₂ := w·p'' = (n+2)/c' ≤ (2x+2)/z`, `w` routed at `z^{1/4}`; `d₁ := p` (the `n`-side
  prime, `PretenseSum` via `∑1/p`):
  `≤ Cmain·(x / Lwin x)·exp(5·z0 z x)·PretenseSum χ (2x+2)` (the `J2` row).
* `ER_T3'_bound` — single-block, `(n+2)₊ = U` prime, `w := (n+2)₋ ≥ z`: `d₂ := U ≤ (2x+2)/z`
  (`PretenseSum` via `∑1/U`), `d₁ := p`:
  `≤ Cmain·(x / Lwin x)·exp(5·z0 z x)·PretenseSum χ (2x+2)` (the `J2` row).
* `ER_Tsw'_bound` — the swap block (`n`-side prime `p` paired with `n+2 = w·U`, `1<w<z`,
  `w` routed at `z^{1/4}`, `U ≥ z`): weights `2Λ(w)·L'`:
  `≤ Cmain·(x / Lwin x)·exp(5·z0 z x)·PretenseSum χ (2x+2)` (the `J2` row).

Corners (small `n`, the `2`-adic/parity `χ_ℝ(2)=−1` both-2-powers kill via
`l2cWindow_parity_link`, `n+2 = 1` pure-pp, `w > x^{1/4}` tails) fold into the `junkExpr`
`Cmain·exp(2·z0 z x)·(x/(z:ℝ)^(1/8:ℝ) + (x:ℝ)^(9/10:ℝ))·(Lwin x)^3` and the squarefull junk.
The `R6` cover is verified disjoint+complete by `ER_prime_cover` (subclass split) +
`E_R_split` (prime / squarefull split); no micro-subclass survives (freeze OPEN-RISK
"R6 COVER COMPLETENESS" discharged at Lean time). -/

end Salt.HB
