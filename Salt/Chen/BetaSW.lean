/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Gate
import Salt.SW.Psi1Transfer
import Salt.BV.Dispersion

/-!
# The Chen rung, node C3b — the β-SW derivation: primes-in-intervals are SW-regular

Design: `docs/blueprints/chen.md`, the C3b row. The general-BV consumer (C3a's
`hβSW` slot) needs the **unweighted prime indicator** on a block `[N, M]`
(`M ≤ 2N`, the fine-partition blocks) to be Siegel–Walfisz-regular: the count of
primes in `[N, M]` in a residue class `a mod q` matches the `φ(q)`-equidistributed
share of the total prime mass, up to `K·N/(log N)^A`.

This file *derives* that from the landed gate `Salt.SW.siegelWalfisz_holds` (the
ψ-form Siegel–Walfisz). The route (blueprint's ψ→θ + Abel log-removal):

1. **E_ψ (the ψ-level regularity).** From the gate at `(q,a)` and at `(1,0)` the
   main terms `x/φ(q)` cancel: `|ψ(x;q,a) − ψ(x)/φ(q)| ≤ 2K·x/(log x)^A`
   (`psiAP_sub_psiTot_bound`).

2. **The prime-power strip (ψ→θ).** `θ(x;q,a) := ∑_{p ≤ x, p≡a} log p` differs
   from `ψ(x;q,a)` only by the proper-prime-power mass, which is `≥ 0` and `≤`
   the total strip `SP(x) = ∑_{n≤x, ¬prime} Λ(n) ≤ √x·(1+log x)` (per-prime cap
   `Salt.SW.sum_vonMangoldt_multiples_le_log`, `#{p ≤ √x} ≤ √x`). Hence
   `thetaAP_SW` — the θ-form SW-regularity, cumulative.

3. **The Abel log-removal (θ→π).** Discrete summation by parts
   (`Finset.sum_Ioc_by_parts`) with the weight `1/log t` on the block `[N, M]`
   turns the θ-discrepancy into the prime-count discrepancy. Because the block is
   `[N, M]` with `N` large, *every* point of the Abel sum has `t ≥ N`, so the gate
   applies uniformly (this is the `(log N)^C` vs `(log t)^C` threading, resolved
   by staying at the `N`-scale); the endpoint `1/log M` and the telescoping inner
   weights recombine to `2/log N`, giving the extra log saving. `prime_indicator_SW`.

4. **The coprimality-to-`s` insertion (Thm-16 hyp (25)).** Excluding the finitely
   many primes dividing a fixed `s` is a cheap corollary
   (`prime_indicator_coprime_SW`).

No `sorry`, no `native_decide`, no new axioms.
-/

open Salt.LS Salt.BV ArithmeticFunction
open scoped BigOperators

namespace Salt.Chen

/-! ## Definitions: the θ-carriers (range-based, matching `primesCount`) -/

/-- `θ(x; q, a) = ∑_{n ≤ x, n prime, n ≡ a mod q} log n`. Range-based (over
`range (x+1)`) to align with `Finset.sum_Ioc_by_parts`' prefix sums and with the
`Salt.Maynard.primesCount` convention `n % q = a`. -/
noncomputable def thetaAP (x q a : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (x + 1), if n.Prime ∧ n % q = a then Real.log n else 0

/-- `θ(x) = ∑_{n ≤ x, n prime} log n = θ(x; 1, 0)` (every `n ≡ 0 mod 1`). -/
noncomputable def thetaTot (x : ℕ) : ℝ := thetaAP x 1 0

/-- The total proper-prime-power strip mass `SP(x) = ∑_{n ≤ x, ¬prime} Λ(n)`. -/
noncomputable def stripMass (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, if n.Prime then 0 else vonMangoldt n

/-! ## Small nonnegativity helpers -/

private lemma ite_dvd_nonneg (p n : ℕ) : (0 : ℝ) ≤ if p ∣ n then vonMangoldt n else 0 := by
  split_ifs with h
  · exact vonMangoldt_nonneg
  · exact le_refl 0

private lemma ite_notprime_nonneg (n : ℕ) :
    (0 : ℝ) ≤ if n.Prime then 0 else vonMangoldt n := by
  split_ifs with h
  · exact le_refl 0
  · exact vonMangoldt_nonneg

/-! ## Range↔Icc reconciliation -/

/-- A `range (x+1)` sum whose `n = 0` summand vanishes equals the `Icc 1 x` sum. -/
lemma sum_range_succ_eq_Icc (x : ℕ) (f : ℕ → ℝ) (h0 : f 0 = 0) :
    ∑ n ∈ Finset.range (x + 1), f n = ∑ n ∈ Finset.Icc 1 x, f n := by
  have hset : Finset.range (x + 1) = insert 0 (Finset.Icc 1 x) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hset, Finset.sum_insert (by simp), h0, zero_add]

/-! ## The prime-power strip bound -/

/-- **The strip is small.** `SP(x) ≤ √x·(1 + log x)`. Every `n ≤ x` with `Λ(n) ≠ 0`
and `n` not prime is a proper prime power `p^k` (`k ≥ 2`), so its base prime `p`
satisfies `p ≤ √x`; dominating each such term by the full divisor-`p` Λ-mass and
applying the per-prime cap (`≤ log x`) over the `≤ √x` primes `p ≤ √x` gives the
bound. -/
lemma stripMass_le (x : ℕ) (hx : 1 ≤ x) :
    stripMass x ≤ Real.sqrt x * (1 + Real.log x) := by
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hxR
  set m := ⌊Real.sqrt x⌋₊ with hm
  set P := (Finset.Icc 1 m).filter Nat.Prime with hP
  -- pointwise domination
  have hpt : ∀ n ∈ Finset.Icc 1 x, (if n.Prime then 0 else vonMangoldt n)
      ≤ ∑ p ∈ P, (if p ∣ n then vonMangoldt n else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    by_cases hnp : n.Prime
    · rw [if_pos hnp]
      exact Finset.sum_nonneg (fun p _ => ite_dvd_nonneg p n)
    · rw [if_neg hnp]
      by_cases hΛ : vonMangoldt n = 0
      · calc vonMangoldt n = 0 := hΛ
          _ ≤ ∑ p ∈ P, (if p ∣ n then vonMangoldt n else 0) :=
              Finset.sum_nonneg (fun p _ => ite_dvd_nonneg p n)
      · -- n = r^k, r prime, k ≥ 2 (since ¬prime)
        obtain ⟨r, k, hr, hk, hrk⟩ := vonMangoldt_ne_zero_iff.mp hΛ
        have hrp : r.Prime := Nat.prime_iff.mpr hr
        have hk2 : 2 ≤ k := by
          rcases Nat.lt_or_ge k 2 with h | h
          · exfalso
            have hk1 : k = 1 := by omega
            rw [hk1, pow_one] at hrk
            exact hnp (hrk ▸ hrp)
          · exact h
        have hrn : r ∣ n := hrk ▸ dvd_pow_self r hk.ne'
        -- r ≤ √x
        have hr2n : r ^ 2 ≤ n := by
          calc r ^ 2 ≤ r ^ k := Nat.pow_le_pow_right hrp.pos hk2
            _ = n := hrk
        have hr2x : (r : ℝ) ^ 2 ≤ (x : ℝ) := by
          have : r ^ 2 ≤ x := le_trans hr2n hn.2
          exact_mod_cast this
        have hrle : (r : ℝ) ≤ Real.sqrt x := by
          rw [show (r : ℝ) = Real.sqrt ((r : ℝ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
          exact Real.sqrt_le_sqrt hr2x
        have hrm : r ≤ m := Nat.le_floor hrle
        have hrmem : r ∈ P := by
          rw [hP, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hrp.one_lt.le, hrm⟩, hrp⟩
        calc vonMangoldt n = (if r ∣ n then vonMangoldt n else 0) := by rw [if_pos hrn]
          _ ≤ ∑ p ∈ P, (if p ∣ n then vonMangoldt n else 0) :=
              Finset.single_le_sum (fun p _ => ite_dvd_nonneg p n) hrmem
  calc stripMass x
      ≤ ∑ n ∈ Finset.Icc 1 x, ∑ p ∈ P, (if p ∣ n then vonMangoldt n else 0) :=
        Finset.sum_le_sum hpt
    _ = ∑ p ∈ P, ∑ n ∈ Finset.Icc 1 x, (if p ∣ n then vonMangoldt n else 0) := Finset.sum_comm
    _ ≤ ∑ _p ∈ P, Real.log x := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hpp : p.Prime := (Finset.mem_filter.mp hp).2
        have := Salt.SW.sum_vonMangoldt_multiples_le_log hpp hxR
        rwa [Nat.floor_natCast] at this
    _ = (P.card : ℝ) * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.sqrt x * (1 + Real.log x) := by
        have hcard : (P.card : ℝ) ≤ Real.sqrt x := by
          calc (P.card : ℝ) ≤ ((Finset.Icc 1 m).card : ℝ) := by
                exact_mod_cast Finset.card_filter_le _ _
            _ = (m : ℝ) := by rw [Nat.card_Icc]; push_cast; ring
            _ ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg _)
        calc (P.card : ℝ) * Real.log x ≤ Real.sqrt x * Real.log x :=
              mul_le_mul_of_nonneg_right hcard hlogx
          _ ≤ Real.sqrt x * (1 + Real.log x) :=
              mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)

/-! ## The ψ↔θ pointwise strip (per AP) -/

/-- `ψ(x; q, a) − θ(x; q, a)` is the proper-prime-power mass in the class, hence
in `[0, SP(x)]`, for a reduced residue `a < q`. -/
lemma psiAP_sub_thetaAP_mem (x q a : ℕ) (haq : a < q) :
    0 ≤ psiAP x q a - thetaAP x q a ∧ psiAP x q a - thetaAP x q a ≤ stripMass x := by
  -- rewrite psiAP and thetaAP over the common index set Icc 1 x
  have hamod : a % q = a := Nat.mod_eq_of_lt haq
  have hpsi : psiAP x q a = ∑ n ∈ Finset.Icc 1 x, (if n % q = a then vonMangoldt n else 0) := by
    unfold psiAP
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n _ => by rw [hamod])
  have htheta : thetaAP x q a
      = ∑ n ∈ Finset.Icc 1 x, (if n.Prime ∧ n % q = a then Real.log n else 0) := by
    unfold thetaAP
    exact sum_range_succ_eq_Icc x _ (by simp)
  have hdiff : psiAP x q a - thetaAP x q a
      = ∑ n ∈ Finset.Icc 1 x,
          ((if n % q = a then vonMangoldt n else 0)
            - (if n.Prime ∧ n % q = a then Real.log n else 0)) := by
    rw [hpsi, htheta, ← Finset.sum_sub_distrib]
  -- per-summand: 0 ≤ diff_n ≤ (if ¬prime then Λn else 0)
  have hterm : ∀ n ∈ Finset.Icc 1 x,
      0 ≤ ((if n % q = a then vonMangoldt n else 0)
            - (if n.Prime ∧ n % q = a then Real.log n else 0))
        ∧ ((if n % q = a then vonMangoldt n else 0)
            - (if n.Prime ∧ n % q = a then Real.log n else 0))
          ≤ (if n.Prime then 0 else vonMangoldt n) := by
    intro n _
    by_cases hres : n % q = a
    · rw [if_pos hres]
      by_cases hnp : n.Prime
      · rw [if_pos ⟨hnp, hres⟩, if_pos hnp,
          ArithmeticFunction.vonMangoldt_apply_prime hnp, sub_self]
        exact ⟨le_refl 0, le_refl 0⟩
      · rw [if_neg (fun h => hnp h.1), if_neg hnp, sub_zero]
        exact ⟨vonMangoldt_nonneg, le_refl _⟩
    · rw [if_neg hres, if_neg (fun h => hres h.2), sub_zero]
      exact ⟨le_refl 0, ite_notprime_nonneg n⟩
  constructor
  · rw [hdiff]; exact Finset.sum_nonneg (fun n hn => (hterm n hn).1)
  · rw [hdiff]
    exact le_trans (Finset.sum_le_sum (fun n hn => (hterm n hn).2)) (le_refl _)

/-! ## E_ψ — the ψ-level SW-regularity -/

/-- **The ψ-level regularity.** `|ψ(x;q,a) − ψ(x)/φ(q)| ≤ 2K·x/(log x)^A` for a
reduced residue `a`, `q ≤ (log x)^C`, `x ≥ 3`. The gate's main terms `x/φ(q)`
cancel between `ψ(x;q,a)` and `ψ(x)/φ(q) = ψ(x;1,0)/φ(q)`. -/
lemma psiAP_sub_psiTot_bound {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x q a : ℕ, 3 ≤ x → 0 < q → a < q → Nat.Coprime a q →
      ((q : ℝ) ≤ (Real.log x) ^ C) →
      |psiAP x q a - psiTot x / (q.totient : ℝ)| ≤ 2 * K * x / (Real.log x) ^ A := by
  obtain ⟨K, hK0, hK⟩ := Salt.SW.siegelWalfisz_holds A C hA hC
  refine ⟨K, hK0, fun x q a hx hq haq hcop hqlog => ?_⟩
  have hx2 : 2 ≤ x := by omega
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlog1 : 1 ≤ Real.log x := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
      _ ≤ (x : ℝ) := hxR
  have hlogpos : 0 < Real.log x := by linarith
  have hLApos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogpos A
  have hφ1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by linarith
  -- gate at (q, a)
  have hb1 := hK x q a hx2 hq hqlog hcop
  -- gate at (1, 0)
  have hq1cond : ((1 : ℕ) : ℝ) ≤ (Real.log x) ^ C := by
    simp only [Nat.cast_one]; exact Real.one_le_rpow hlog1 hC.le
  have hb0 := hK x 1 0 hx2 one_pos hq1cond (Nat.coprime_one_right 0)
  rw [psiAP_one x 0, Nat.totient_one, Nat.cast_one, div_one] at hb0
  -- combine: E_ψ = (ψAP − x/φ) − (ψTot − x)/φ
  set L := (Real.log x) ^ A with hL
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hsplit : psiAP x q a - psiTot x / (q.totient : ℝ)
      = (psiAP x q a - (x : ℝ) / (q.totient : ℝ))
        - (psiTot x - (x : ℝ)) / (q.totient : ℝ) := by field_simp; ring
  rw [hsplit]
  have hb0' : |psiTot x - (x : ℝ)| / (q.totient : ℝ) ≤ K * x / L := by
    rw [div_le_iff₀ hφpos]
    calc |psiTot x - (x : ℝ)| ≤ K * x / L := hb0
      _ ≤ K * x / L * (q.totient : ℝ) := by
          have : 0 ≤ K * x / L := by positivity
          nlinarith [this, hφ1]
  calc |(psiAP x q a - (x : ℝ) / (q.totient : ℝ)) - (psiTot x - (x : ℝ)) / (q.totient : ℝ)|
      ≤ |psiAP x q a - (x : ℝ) / (q.totient : ℝ)| + |(psiTot x - (x : ℝ)) / (q.totient : ℝ)| :=
        abs_sub _ _
    _ = |psiAP x q a - (x : ℝ) / (q.totient : ℝ)| + |psiTot x - (x : ℝ)| / (q.totient : ℝ) := by
        rw [abs_div, abs_of_pos hφpos]
    _ ≤ K * x / L + K * x / L := add_le_add hb1 hb0'
    _ = 2 * K * x / L := by ring

/-! ## θ-AP SW-regularity (cumulative) -/

/-- **The θ-form Siegel–Walfisz regularity (cumulative).** For every saving `A`
and range exponent `C`, there is `K > 0` and a threshold `x₀` with
`|θ(x;q,a) − θ(x)/φ(q)| ≤ K·x/(log x)^A` for `x ≥ x₀`, `q ≤ (log x)^C`, and a
reduced residue `a` coprime to `q`. Route: the ψ-level regularity
`psiAP_sub_psiTot_bound` (main terms cancel) minus the two prime-power strips,
each `≤ SP(x) ≤ √x·(1+log x) = o(x/(log x)^A)` (`stripMass_le` + `absorb_nat`). -/
theorem thetaAP_SW {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ (K : ℝ) (x₀ : ℕ), 0 < K ∧ ∀ x q a : ℕ, x₀ ≤ x → 0 < q → a < q → Nat.Coprime a q →
      ((q : ℝ) ≤ (Real.log x) ^ C) →
      |thetaAP x q a - thetaTot x / (q.totient : ℝ)| ≤ K * x / (Real.log x) ^ A := by
  obtain ⟨K, _hK0, hKb⟩ := psiAP_sub_psiTot_bound hA hC
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp
    (absorb_nat (θ := (1/2 : ℝ)) (k := (1 : ℝ)) (A := A) (M := (2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num))
  refine ⟨2 * K + 1, max x₁ 3, by positivity, fun x q a hx hq haq hcop hqlog => ?_⟩
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hlog1 : 1 ≤ Real.log x := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
      _ ≤ (x : ℝ) := hxR
  have hlogpos : 0 < Real.log x := by linarith
  have hLApos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogpos A
  have hφ1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by linarith
  set L := (Real.log x) ^ A with hL
  -- E_ψ bound
  have hEpsi := hKb x q a hx3 hq haq hcop hqlog
  -- the two strips
  obtain ⟨hs1lo, hs1hi⟩ := psiAP_sub_thetaAP_mem x q a haq
  obtain ⟨hs0lo, hs0hi⟩ := psiAP_sub_thetaAP_mem x 1 0 Nat.one_pos
  -- rewrite the (1,0) strip via psiAP x 1 0 = psiTot x, thetaAP x 1 0 = thetaTot x
  rw [psiAP_one x 0] at hs0lo hs0hi
  -- SP bound + absorption
  have hSP := stripMass_le x (by omega)
  have habs := hx₁ x hx1
  rw [Real.rpow_one, show ((x : ℝ) ^ (1/2 : ℝ)) = Real.sqrt x from (Real.sqrt_eq_rpow x).symm]
    at habs
  have hSPabs : 2 * stripMass x ≤ (x : ℝ) / L := by
    calc 2 * stripMass x ≤ 2 * (Real.sqrt x * (1 + Real.log x)) := by linarith [hSP]
      _ = 2 * Real.sqrt x * (1 + Real.log x) := by ring
      _ ≤ (x : ℝ) / L := habs
  -- the algebraic identity E_θ = E_ψ − s₁ + s₀/φ
  set s1 := psiAP x q a - thetaAP x q a with hs1
  set s0 := psiTot x - thetaTot x with hs0
  have hid : thetaAP x q a - thetaTot x / (q.totient : ℝ)
      = (psiAP x q a - psiTot x / (q.totient : ℝ)) - s1 + s0 / (q.totient : ℝ) := by
    rw [hs1, hs0]; ring
  -- s₀/φ facts
  have hs0φ_lo : 0 ≤ s0 / (q.totient : ℝ) := div_nonneg hs0lo hφpos.le
  have hs0φ_hi : s0 / (q.totient : ℝ) ≤ stripMass x :=
    le_trans (div_le_self hs0lo hφ1) hs0hi
  have hSPnn : 0 ≤ stripMass x := le_trans hs1lo hs1hi
  obtain ⟨hElo, hEhi⟩ := abs_le.mp hEpsi
  have hRHS : (2 * K + 1) * (x : ℝ) / L = 2 * K * (x : ℝ) / L + (x : ℝ) / L := by ring
  rw [hid, abs_le]
  refine ⟨?_, ?_⟩
  · rw [hRHS]; linarith [hElo, hs1hi, hs0φ_lo, hSPabs, hSPnn]
  · rw [hRHS]; linarith [hEhi, hs1lo, hs0φ_hi, hSPabs, hSPnn]

/-! ## The Abel log-removal (θ → π) -/

/-- The inverse-log Abel weights telescope: `∑_{N < i ≤ M-1} ((log i)⁻¹ − (log(i+1))⁻¹)
= (log N)⁻¹ − (log M)⁻¹`. Mirror of `Salt.BV.sum_w_telescope`, general base `N`. -/
lemma telescope_inv_log {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ i ∈ Finset.Ioc (N - 1) (M - 1), ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
      = (Real.log N)⁻¹ - (Real.log M)⁻¹ := by
  have hIco : Finset.Ioc (N - 1) (M - 1) = Finset.Ico N M := by
    ext n; rw [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hIco, Finset.sum_Ico_eq_sum_range]
  have hcongr : ∑ k ∈ Finset.range (M - N),
        ((Real.log ((N + k : ℕ) : ℝ))⁻¹ - (Real.log ((N + k + 1 : ℕ) : ℝ))⁻¹)
      = ∑ k ∈ Finset.range (M - N),
          ((fun j : ℕ => (Real.log ((N + j : ℕ) : ℝ))⁻¹) k
            - (fun j : ℕ => (Real.log ((N + j : ℕ) : ℝ))⁻¹) (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k _
    have hk : (N + k + 1 : ℕ) = N + (k + 1) := by omega
    simp only [hk]
  rw [hcongr, Finset.sum_range_sub']
  have h2 : N + (M - N) = M := by omega
  simp only [Nat.add_zero, h2]

/-- `(log(i+1))⁻¹ ≤ (log i)⁻¹` for `i ≥ 2` (log increasing and positive). -/
private lemma inv_log_succ_le {i : ℕ} (hi : 2 ≤ i) :
    (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ ≤ (Real.log i)⁻¹ := by
  have hli : 0 < Real.log i := Real.log_pos (by exact_mod_cast hi)
  have hmono : Real.log i ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < i by omega))
      (by exact_mod_cast (show i ≤ i + 1 by omega))
  exact inv_anti₀ hli hmono

/-- **The interval prime indicator is SW-regular (`prime_indicator_SW`).** For every
saving `A` and range exponent `C`, there is `K > 0` and a threshold `N₀` with: for
`N₀ ≤ N`, `N ≤ M ≤ 2N`, `q ≥ 1`, `a` coprime to `q`, and `q ≤ (log N)^C`, the count
of primes in the block `(N, M]` in the class `a mod q` matches the `φ(q)`-share of
the total prime count of `(N, M]`, up to `K·N/(log N)^A`:
`|#{p ∈ (N,M] : p prime, p ≡ a mod q} − #{p ∈ (N,M] : p prime}/φ(q)| ≤ K·N/(log N)^A`.

Route: discrete summation by parts (`Finset.sum_Ioc_by_parts`) with the weight
`(log t)⁻¹` on `(N, M]`. Every point `t ∈ [N, M]` has `t ≥ N`, so the θ-form
regularity `thetaAP_SW` applies uniformly (`q ≤ (log N)^C ≤ (log t)^C`), bounding
each cumulative θ-discrepancy by `2·Kθ·N/(log N)^A`; the endpoint `(log M)⁻¹` and
the telescoping inner weights recombine to `2·(log(N+1))⁻¹ ≤ 2·(log N)⁻¹`, yielding
the extra log saving.  (The closed block `[N, M]` differs by at most one prime — the
endpoint `N` — an `O(1)` term, immaterial for the fine-partition consumer.) -/
theorem prime_indicator_SW {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧ ∀ N M q a : ℕ, N₀ ≤ N → N ≤ M → M ≤ 2 * N →
      0 < q → Nat.Coprime a q → ((q : ℝ) ≤ (Real.log N) ^ C) →
      |(((Finset.Ioc N M).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ)
        - (((Finset.Ioc N M).filter (fun p => p.Prime)).card : ℝ) / (q.totient : ℝ)|
        ≤ K * N / (Real.log N) ^ A := by
  obtain ⟨Kθ, x₀θ, hKθ0, hθb⟩ := thetaAP_SW hA hC
  refine ⟨4 * Kθ, max x₀θ 3, by positivity, fun N M q a hN hNM hM2N hq hcop hqlog => ?_⟩
  classical
  set a' := a % q with ha'def
  have ha'q : a' < q := Nat.mod_lt a hq
  have hcop' : Nat.Coprime a' q := (coprime_mod_left a q).mp hcop
  set φ := (q.totient : ℝ) with hφdef
  have hNx₀ : x₀θ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogN1 : 1 ≤ Real.log N := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
      _ ≤ (N : ℝ) := hNR
  have hLNApos : 0 < (Real.log N) ^ A := Real.rpow_pos_of_pos hlogN A
  have hφpos : 0 < φ := by rw [hφdef]; exact_mod_cast Nat.totient_pos.mpr hq
  -- the uniform θ-discrepancy bound `B` on the block [N, M]
  set B := 2 * Kθ * (N : ℝ) / (Real.log N) ^ A with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hEB : ∀ t : ℕ, N ≤ t → t ≤ M → |thetaAP t q a' - thetaTot t / φ| ≤ B := by
    intro t hNt htM
    have hNtR : (N : ℝ) ≤ (t : ℝ) := by exact_mod_cast hNt
    have hlogt : 0 < Real.log t :=
      lt_of_lt_of_le hlogN (Real.log_le_log (by linarith) hNtR)
    have hLtge : (Real.log N) ^ A ≤ (Real.log t) ^ A :=
      Real.rpow_le_rpow hlogN.le (Real.log_le_log (by linarith) hNtR) hA.le
    have hLtApos : 0 < (Real.log t) ^ A := Real.rpow_pos_of_pos hlogt A
    have hqt : (q : ℝ) ≤ (Real.log t) ^ C :=
      le_trans hqlog (Real.rpow_le_rpow hlogN.le (Real.log_le_log (by linarith) hNtR) hC.le)
    have hbound := hθb t q a' (le_trans hNx₀ hNt) hq ha'q hcop' hqt
    rw [← hφdef] at hbound
    refine le_trans hbound ?_
    rw [hBdef, div_le_div_iff₀ hLtApos hLNApos]
    have htR : (t : ℝ) ≤ 2 * N := by
      have : t ≤ 2 * N := le_trans htM hM2N; exact_mod_cast this
    have h1 : Kθ * (t : ℝ) * (Real.log N) ^ A ≤ 2 * Kθ * N * (Real.log N) ^ A := by
      apply mul_le_mul_of_nonneg_right _ hLNApos.le; nlinarith [hKθ0, htR]
    have h2 : 2 * Kθ * (N : ℝ) * (Real.log N) ^ A ≤ 2 * Kθ * N * (Real.log t) ^ A := by
      apply mul_le_mul_of_nonneg_left hLtge; positivity
    linarith
  rcases lt_or_eq_of_le hNM with hlt | heq
  · -- main case: `N < M`
    set f : ℕ → ℝ := fun i => (Real.log i)⁻¹ with hfdef
    set g : ℕ → ℝ := fun i =>
      (if i.Prime ∧ i % q = a' then Real.log i else 0)
        - (if i.Prime then Real.log i else 0) / φ with hgdef
    -- prefix-sum closed form `G(k) = θ(k−1;q,a') − θ(k−1)/φ`
    have hG : ∀ k : ℕ, 1 ≤ k →
        (∑ i ∈ Finset.range k, g i) = thetaAP (k - 1) q a' - thetaTot (k - 1) / φ := by
      intro k hk
      have hk1 : k - 1 + 1 = k := by omega
      have hAP : ∑ i ∈ Finset.range k, (if i.Prime ∧ i % q = a' then Real.log i else 0)
          = thetaAP (k - 1) q a' := by rw [thetaAP, hk1]
      have hTot : ∑ i ∈ Finset.range k, (if i.Prime then Real.log i else 0)
          = thetaTot (k - 1) := by
        rw [thetaTot, thetaAP, hk1]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases hp : i.Prime
        · rw [if_pos hp, if_pos ⟨hp, Nat.mod_one i⟩]
        · rw [if_neg hp, if_neg (fun h => hp h.1)]
      simp only [hgdef]
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, hAP, hTot]
    have hbp := Finset.sum_Ioc_by_parts f g hlt
    simp only [smul_eq_mul] at hbp
    -- LHS of by-parts = the interval discrepancy
    have hLHS : ∑ i ∈ Finset.Ioc N M, f i * g i
        = (((Finset.Ioc N M).filter (fun p => p.Prime ∧ p % q = a')).card : ℝ)
          - (((Finset.Ioc N M).filter (fun p => p.Prime)).card : ℝ) / φ := by
      have hpt : ∀ i ∈ Finset.Ioc N M, f i * g i
          = (if i.Prime ∧ i % q = a' then (1 : ℝ) else 0)
            - (if i.Prime then (1 : ℝ) else 0) / φ := by
        intro i hi
        rw [Finset.mem_Ioc] at hi
        have hlogi : Real.log i ≠ 0 :=
          ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < i by omega)))
        have e1 : (Real.log i)⁻¹ * (if i.Prime ∧ i % q = a' then Real.log i else 0)
            = if i.Prime ∧ i % q = a' then (1 : ℝ) else 0 := by
          split_ifs with h
          · exact inv_mul_cancel₀ hlogi
          · rw [mul_zero]
        have e2 : (Real.log i)⁻¹ * (if i.Prime then Real.log i else 0)
            = if i.Prime then (1 : ℝ) else 0 := by
          split_ifs with h
          · exact inv_mul_cancel₀ hlogi
          · rw [mul_zero]
        simp only [hfdef, hgdef]
        rw [mul_sub, e1, ← mul_div_assoc, e2]
      rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.sum_div,
        Finset.sum_boole, Finset.sum_boole]
    -- rewrite the prefix sums to θ-discrepancies
    have hinner : ∑ i ∈ Finset.Ioc N (M - 1), (f (i + 1) - f i) * (∑ j ∈ Finset.range (i + 1), g j)
        = ∑ i ∈ Finset.Ioc N (M - 1),
            (f (i + 1) - f i) * (thetaAP i q a' - thetaTot i / φ) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have h := hG (i + 1) (by omega)
      rw [Nat.add_sub_cancel] at h
      rw [h]
    rw [hLHS, hG (M + 1) (by omega), hG (N + 1) (by omega), hinner] at hbp
    simp only [Nat.add_sub_cancel] at hbp
    rw [hbp]
    -- bound the pieces
    set EM := thetaAP M q a' - thetaTot M / φ with hEM
    set EN := thetaAP N q a' - thetaTot N / φ with hEN
    have hlogMpos : 0 < Real.log M :=
      lt_of_lt_of_le hlogN (Real.log_le_log (by linarith) (by exact_mod_cast (le_of_lt hlt)))
    have hlogN1pos : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le hlogN
        (Real.log_le_log (by linarith) (by exact_mod_cast (show N ≤ N + 1 by omega)))
    have hfMnn : 0 ≤ (Real.log M)⁻¹ := le_of_lt (inv_pos.mpr hlogMpos)
    have hfN1nn : 0 ≤ (Real.log ((N + 1 : ℕ) : ℝ))⁻¹ := le_of_lt (inv_pos.mpr hlogN1pos)
    -- inner-sum bound
    have htel : ∑ i ∈ Finset.Ioc N (M - 1),
          ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
        = (Real.log ((N + 1 : ℕ) : ℝ))⁻¹ - (Real.log M)⁻¹ := by
      have hset : Finset.Ioc N (M - 1) = Finset.Ioc ((N + 1) - 1) (M - 1) := by
        ext n; simp only [Finset.mem_Ioc]; omega
      rw [hset]; exact telescope_inv_log (N := N + 1) (by omega) (by omega)
    have hSbound :
        |∑ i ∈ Finset.Ioc N (M - 1), (f (i + 1) - f i) * (thetaAP i q a' - thetaTot i / φ)|
          ≤ B * ((Real.log ((N + 1 : ℕ) : ℝ))⁻¹ - (Real.log M)⁻¹) := by
      calc |∑ i ∈ Finset.Ioc N (M - 1),
                (f (i + 1) - f i) * (thetaAP i q a' - thetaTot i / φ)|
          ≤ ∑ i ∈ Finset.Ioc N (M - 1),
              |(f (i + 1) - f i) * (thetaAP i q a' - thetaTot i / φ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.Ioc N (M - 1),
              ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) * B := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            rw [Finset.mem_Ioc] at hi
            have hwnn : 0 ≤ (Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ := by
              have := inv_log_succ_le (show 2 ≤ i by omega); linarith
            have hfw : f (i + 1) - f i
                = -(((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)) := by rw [hfdef]; ring
            rw [abs_mul, hfw, abs_neg, abs_of_nonneg hwnn]
            exact mul_le_mul_of_nonneg_left (hEB i (by omega) (by omega)) hwnn
        _ = (∑ i ∈ Finset.Ioc N (M - 1),
              ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)) * B := by rw [← Finset.sum_mul]
        _ = ((Real.log ((N + 1 : ℕ) : ℝ))⁻¹ - (Real.log M)⁻¹) * B := by rw [htel]
        _ = B * ((Real.log ((N + 1 : ℕ) : ℝ))⁻¹ - (Real.log M)⁻¹) := by ring
    have hEMB : |EM| ≤ B := hEB M (le_of_lt hlt) (le_refl M)
    have hENB : |EN| ≤ B := hEB N (le_refl N) (le_of_lt hlt)
    have htriangle :
        |f M * EM - f (N + 1) * EN
          - ∑ i ∈ Finset.Ioc N (M - 1), (f (i + 1) - f i) * (thetaAP i q a' - thetaTot i / φ)|
        ≤ 2 * B * (Real.log ((N + 1 : ℕ) : ℝ))⁻¹ := by
      have h1 : |f M * EM| ≤ (Real.log M)⁻¹ * B := by
        rw [show f M = (Real.log M)⁻¹ from rfl, abs_mul, abs_of_nonneg hfMnn]
        exact mul_le_mul_of_nonneg_left hEMB hfMnn
      have h2 : |f (N + 1) * EN| ≤ (Real.log ((N + 1 : ℕ) : ℝ))⁻¹ * B := by
        rw [show f (N + 1) = (Real.log ((N + 1 : ℕ) : ℝ))⁻¹ from rfl, abs_mul,
          abs_of_nonneg hfN1nn]
        exact mul_le_mul_of_nonneg_left hENB hfN1nn
      have hab1 := abs_sub (f M * EM) (f (N + 1) * EN)
      have hab2 := abs_sub (f M * EM - f (N + 1) * EN)
        (∑ i ∈ Finset.Ioc N (M - 1), (f (i + 1) - f i) * (thetaAP i q a' - thetaTot i / φ))
      calc |f M * EM - f (N + 1) * EN
              - ∑ i ∈ Finset.Ioc N (M - 1), (f (i + 1) - f i) * (thetaAP i q a' - thetaTot i / φ)|
          ≤ (Real.log M)⁻¹ * B + (Real.log ((N + 1 : ℕ) : ℝ))⁻¹ * B
            + B * ((Real.log ((N + 1 : ℕ) : ℝ))⁻¹ - (Real.log M)⁻¹) := by
            linarith [hab1, hab2, h1, h2, hSbound]
        _ = 2 * B * (Real.log ((N + 1 : ℕ) : ℝ))⁻¹ := by ring
    refine le_trans htriangle ?_
    -- 2·B·(log(N+1))⁻¹ ≤ 4·Kθ·N/(log N)^A
    have hstep : (Real.log ((N + 1 : ℕ) : ℝ))⁻¹ ≤ (Real.log N)⁻¹ :=
      inv_log_succ_le (show 2 ≤ N by omega)
    have hpow : (Real.log N) ^ (A + 1) = (Real.log N) ^ A * Real.log N := by
      rw [Real.rpow_add hlogN, Real.rpow_one]
    have hlogNne : Real.log N ≠ 0 := ne_of_gt hlogN
    have hLNAne : (Real.log N) ^ A ≠ 0 := ne_of_gt hLNApos
    calc 2 * B * (Real.log ((N + 1 : ℕ) : ℝ))⁻¹
        ≤ 2 * B * (Real.log N)⁻¹ := by
          apply mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 4 * Kθ * N / (Real.log N) ^ (A + 1) := by rw [hBdef, hpow]; field_simp; ring
      _ ≤ 4 * Kθ * N / (Real.log N) ^ A :=
          div_le_div_of_nonneg_left
            (by have := hKθ0; positivity) hLNApos
            (Real.rpow_le_rpow_of_exponent_le hlogN1 (by linarith))
  · -- degenerate case `N = M`: the block `(N, M]` is empty
    subst heq
    simp only [Finset.Ioc_self, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      zero_div, sub_zero, abs_zero]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hKθ0.le) (Nat.cast_nonneg N)) hLNApos.le

/-! ## The coprimality-to-`s` insertion (Thm-16 hyp (25) shape) -/

/-- The primes in the class dividing a fixed nonzero `s` number at most `ω(s)` — a
finite exclusion (each such prime lies in `s.primeFactors`). -/
private lemma card_excluded_le {N M q a s : ℕ} (hs : s ≠ 0) :
    ((Finset.Ioc N M).filter
        (fun p => (p.Prime ∧ p % q = a % q) ∧ ¬ Nat.Coprime p s)).card
      ≤ s.primeFactors.card := by
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨_, ⟨hpp, _⟩, hncop⟩ := hp
  have hdvd : p ∣ s := by
    by_contra h; exact hncop (hpp.coprime_iff_not_dvd.mpr h)
  exact Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hs⟩

/-- **Coprimality-to-`s` insertion (Thm-16 hyp (25) shape).** Restricting the prime
indicator to residues coprime to a fixed `s ≠ 0` is a finite exclusion — only the
`≤ ω(s)` primes dividing `s` are removed — so SW-regularity survives up to the `O(ω(s))`
additive constant: the coprime-restricted count of primes in `(N, M]` in the class
`a mod q` still matches the `φ(q)`-share of the total prime count, up to
`K·N/(log N)^A + ω(s)`. Immediate from `prime_indicator_SW` plus `card_excluded_le`. -/
theorem prime_indicator_coprime_SW {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧ ∀ N M q a s : ℕ, N₀ ≤ N → N ≤ M → M ≤ 2 * N →
      0 < q → Nat.Coprime a q → s ≠ 0 → ((q : ℝ) ≤ (Real.log N) ^ C) →
      |(((Finset.Ioc N M).filter
            (fun p => (p.Prime ∧ p % q = a % q) ∧ Nat.Coprime p s)).card : ℝ)
        - (((Finset.Ioc N M).filter (fun p => p.Prime)).card : ℝ) / (q.totient : ℝ)|
        ≤ K * N / (Real.log N) ^ A + (s.primeFactors.card : ℝ) := by
  obtain ⟨K, N₀, hK0, hb⟩ := prime_indicator_SW hA hC
  refine ⟨K, N₀, hK0, fun N M q a s hN hNM hM2N hq hcop hs hqlog => ?_⟩
  classical
  set Aall := (Finset.Ioc N M).filter (fun p => p.Prime ∧ p % q = a % q) with hAall
  set Acop := (Finset.Ioc N M).filter
    (fun p => (p.Prime ∧ p % q = a % q) ∧ Nat.Coprime p s) with hAcop
  set Aex := (Finset.Ioc N M).filter
    (fun p => (p.Prime ∧ p % q = a % q) ∧ ¬ Nat.Coprime p s) with hAex
  set Tot := (Finset.Ioc N M).filter (fun p => p.Prime) with hTot
  set φ := (q.totient : ℝ) with hφdef
  -- Acop.card + Aex.card = Aall.card
  have hsplitnat : Acop.card + Aex.card = Aall.card := by
    rw [hAcop, hAex, hAall]
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.Ioc N M).filter (fun p => p.Prime ∧ p % q = a % q))
      (fun p => Nat.Coprime p s)
    rw [Finset.filter_filter, Finset.filter_filter] at h
    exact h
  have hsplit : (Acop.card : ℝ) = (Aall.card : ℝ) - (Aex.card : ℝ) := by
    have : ((Acop.card + Aex.card : ℕ) : ℝ) = (Aall.card : ℝ) := by exact_mod_cast hsplitnat
    push_cast at this; linarith
  have hexle : (Aex.card : ℝ) ≤ (s.primeFactors.card : ℝ) := by
    exact_mod_cast card_excluded_le hs
  have hex0 : (0 : ℝ) ≤ (Aex.card : ℝ) := by positivity
  -- the full-count regularity
  have hfull := hb N M q a hN hNM hM2N hq hcop hqlog
  rw [← hAall, ← hTot, ← hφdef] at hfull
  -- assemble
  have hid : (Acop.card : ℝ) - (Tot.card : ℝ) / φ
      = ((Aall.card : ℝ) - (Tot.card : ℝ) / φ) - (Aex.card : ℝ) := by rw [hsplit]; ring
  rw [hid]
  calc |((Aall.card : ℝ) - (Tot.card : ℝ) / φ) - (Aex.card : ℝ)|
      ≤ |(Aall.card : ℝ) - (Tot.card : ℝ) / φ| + |(Aex.card : ℝ)| := abs_sub _ _
    _ ≤ K * N / (Real.log N) ^ A + (s.primeFactors.card : ℝ) := by
        rw [abs_of_nonneg hex0]; linarith [hfull, hexle]

end Salt.Chen
