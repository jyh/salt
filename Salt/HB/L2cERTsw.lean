/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cER

/-!
# HB-L2c — the `E_R` T-sw mirror family budget (node HB-L2c-M-Tsw, Horn A mirror keystone)

Single writer of the **`E_R` swap-family budget** `ER_Tsw'_bound` — the `J2` `PretenseSum`
row of the *right*-overshoot family analysis (freeze §S4, `E_R` roles-swapped mirror of the
refuter-discovered `S₂⁴`-block repair; target shape recorded in `Salt.HB.L2cER` §5 NOTES).

The `E_R` T-sw' family is the sub-sum of `E_R = Σ_{n∈W} Λ(n)·(Λ̃−Λ)(n+2)` over window
elements `n` that are **prime** (`n = p`, the `E_R` prime part, weight `Λ(n) = log p ≤ L'`)
whose shifted partner has the **swap** shape `n+2 = w·U`:

* `w := (n+2)₋` a prime power with `1 < w < z` (the *small* `χ = −1` block, the
  `z^{1/4}`-routed block of this family), and
* `U := (n+2)₊` **prime** (a `χ = +1` prime; `z ≤ U` and in fact `x/z < U` automatically).

Complementary to `ER_T2'` (`(n+2)₊` composite) and `ER_T3'` (`(n+2)₊` prime, `w ≥ z`) inside
`ER_prime_cover`'s single-block class.  Per the 2026-07-19 HOUSE AMENDMENTS (catch #245) the
family carries the **inline junk-block guard** on `w`: blocks `w = p^e` with `p ≤ Zz z`,
`e ≥ 2`, `z^{1/4} < w` are excluded here (they belong to the junk row `ER_wJunk_bound`,
owned by the junk file); the guard is stated with the family-prefixed local predicate
`ERTswJunkBlock` (single-writer name law).

## What this file lands

1. `ERTswJunkBlock` / `IsERTsw` / `ER_Tsw'` — guard, family predicate, family sub-sum.
2. `erTsw_lamTilde_np2` — the **sharp single-block identity** `Λ̃(n+2) = 2·Λ(w)` on the
   family (`fChiSum(U) = 1 + χ(U) = 2` for the `χ=+1` prime `U`) — the amendment-3
   structural gift realized: the `n`-side is a bare prime, so both weight factors reduce
   without any weighted left fibration (`Λ(n) ≤ L'` crude, `Λ̃(n+2) = 2Λ(w)` sharp).
3. `ER_Tsw'_le_weightedCount` — the reduction `ER_Tsw' ≤ 2L'·Σ_{n∈Tsw'} Λ((n+2)₋)`.
4. `erTsw_weightedCount_le` — the **unconditional `PS`-carrying count**: fibering over the
   `χ=+1` prime `U = (n+2)₊` (`Finset.sum_fiberwise_of_maps_to`), the per-`U` fiber `w`-mass
   is `≤ ψ((2x+2)/U) ≤ (log4+4)·(2x+2)/U` (Chebyshev), and `Σ_U 1/U ≤ PS/log z`
   (`sum_inv_plusprime_le_pretense`): `Σ_{n∈Tsw'} Λ((n+2)₋) ≤ (log4+4)·(2x+2)·PS/log z`.
5. `ER_Tsw'_pretense_bound` — the unconditional budget `ER_Tsw' ≤ 56·x·z₀·PS` (one `n`-side
   sieve log short of the frozen `J2` row — see the NOTES block).
6. `ER_Tsw'_bound_of_count` — the **frozen `J2` conclusion**
   `ER_Tsw' ≤ Ccount·(x/L')·exp(5·z₀)·PretenseSum χ (2x+2)`, conditional on the named count
   residual `hcount : Σ_{n∈Tsw'} Λ((n+2)₋) ≤ Ccount·x·PS/(log z)²` (the same interface shape
   as `L2cELTsw.EL_Tsw_bound_of_count`, for a uniform Wave-3 consumption).

Single-writer file (`L2cERTsw.lean`); imports the frozen surfaces `Salt.HB.L2cER` /
`Salt.HB.L2cCore` and touches no other file (`Salt.HB.All` is Wave 3's manifest).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — the junk-block guard, the family predicate, and the family sub-sum -/

/-- **The T-sw' junk-block guard** (HOUSE AMENDMENTS, catch #245): a block `m` is a *junk
    block* when `m = p^e` with `p` prime, `p ≤ Zz z`, `e ≥ 2`, and `z^{1/4} < m` — the
    small-base squarefull corner that cannot fit the `J2` row and belongs to the junk row
    (`ER_wJunk_bound`).  Family-prefixed local predicate (single-writer name law). -/
def ERTswJunkBlock (z m : ℕ) : Prop :=
  ∃ p e : ℕ, p.Prime ∧ p ≤ Zz z ∧ 2 ≤ e ∧ m = p ^ e ∧ (z : ℝ) ^ ((1 : ℝ) / 4) < (m : ℝ)

/-- **The `E_R` T-sw' (swap) family predicate.**  On a window element `n`: `n` is prime
    (the `E_R` prime part), the `χ=−1` block `w := (n+2)₋` is a prime power with `w < z`
    (the small block; `1 < w` is automatic from `IsPrimePow`), the all-plus part
    `U := (n+2)₊` is **prime**, and `w` is not a junk block (the amendment-1 inline
    guard on this family's `z^{1/4}`-routed block). -/
def IsERTsw (χ : DirichletCharacter ℂ q) (z n : ℕ) : Prop :=
  n.Prime ∧ IsPrimePow (nMinus χ (n + 2)) ∧ nMinus χ (n + 2) < z ∧
    (nPlus χ (n + 2)).Prime ∧ ¬ ERTswJunkBlock z (nMinus χ (n + 2))

open Classical in
/-- **The T-sw' family sub-sum** `Σ_{n∈W, Tsw'(n)} Λ(n)·(Λ̃−Λ)(n+2)` — the swap block of
    the right overshoot `E_R` (`L2cER.E_R`) that this file prices. -/
noncomputable def ER_Tsw' (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsERTsw χ z n),
    Λ n * (LamTilde χ (n + 2) - Λ (n + 2))

/-! ## §1 — the sharp single-block identity `Λ̃(n+2) = 2·Λ(w)` on the family -/

/-- For a prime `m` with `χ(m) = 1`, the divisor weight is exactly `fChiSum χ m = 2`
    (`fChiArith(p^1) = 1 + χ(p)`). -/
lemma erTsw_fChiSum_eq_two (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ}
    (hm : m.Prime) (hchi : chiRe χ m = 1) : fChiSum χ m = 2 := by
  calc fChiSum χ m = fChiArith χ m := (fChiArith_eq_fChiSum χ m).symm
    _ = fChiArith χ (m ^ 1) := by rw [pow_one]
    _ = 1 + chiRe χ m := fChiArith_primePow_pos hm χ hsq one_ne_zero
    _ = 2 := by rw [hchi]; norm_num

/-- The all-plus part of `n+2` on a window element with `(n+2)₊` prime is a `χ=+1` prime
    (`nPlus_sign` at the prime itself). -/
lemma erTsw_chiRe_nPlus_eq_one (χ : DirichletCharacter ℂ q) {n : ℕ}
    (hUp : (nPlus χ (n + 2)).Prime) : chiRe χ (nPlus χ (n + 2)) = 1 :=
  nPlus_sign (Nat.mem_primeFactors.mpr ⟨hUp, dvd_rfl, hUp.pos.ne'⟩)

/-- **The sharp single-block identity.**  On a window element `n` whose block `(n+2)₋` is a
    prime power and whose all-plus part `(n+2)₊` is prime, `Λ̃(n+2) = 2·Λ((n+2)₋)` exactly
    (`LamTilde_eq_single_of_card_one` with `fChiSum((n+2)₊) = 2`). -/
lemma erTsw_lamTilde_np2 (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (hpp : IsPrimePow (nMinus χ (n + 2)))
    (hUp : (nPlus χ (n + 2)).Prime) :
    LamTilde χ (n + 2) = 2 * Λ (nMinus χ (n + 2)) := by
  rw [LamTilde_eq_single_of_card_one χ hsq (by omega) (l2cWindow_np2_coprime_q χ hn) hpp,
    erTsw_fChiSum_eq_two χ hsq hUp (erTsw_chiRe_nPlus_eq_one χ hUp)]

/-! ## §2 — the per-summand cap (the amendment-3 single-prime gift)

The `n`-side is a bare prime, so no weighted left fibration is needed: `Λ(n) ≤ L'` crude
(`l2cWindow_vonMangoldt_cap`) and the sharp `Λ̃(n+2) = 2Λ(w)` identity give the per-term
weight `2·L'·Λ(w)` — exactly the freeze's `2Λ(w)·L'` (the factor order swapped). -/

/-- **The per-summand cap.**  On the family, `Λ(n)·(Λ̃−Λ)(n+2) ≤ 2·L'·Λ((n+2)₋)`. -/
lemma erTsw_summand_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (h : IsERTsw χ z n) :
    Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) ≤ 2 * Lwin x * Λ (nMinus χ (n + 2)) := by
  have hcap : Λ n ≤ Lwin x := l2cWindow_vonMangoldt_cap χ hn
  have hΛw : (0 : ℝ) ≤ 2 * Λ (nMinus χ (n + 2)) :=
    mul_nonneg (by norm_num) vonMangoldt_nonneg
  calc Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ Λ n * LamTilde χ (n + 2) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ vonMangoldt_nonneg) vonMangoldt_nonneg
    _ = Λ n * (2 * Λ (nMinus χ (n + 2))) := by
        rw [erTsw_lamTilde_np2 χ hsq hn h.2.1 h.2.2.2.1]
    _ ≤ Lwin x * (2 * Λ (nMinus χ (n + 2))) := mul_le_mul_of_nonneg_right hcap hΛw
    _ = 2 * Lwin x * Λ (nMinus χ (n + 2)) := by ring

/-! ## §3 — the reduction to the weighted `χ=−1`-block count -/

open Classical in
/-- **The T-sw' reduction.**  Summing the per-summand cap,
    `ER_Tsw' ≤ 2·L'·Σ_{n∈Tsw'} Λ((n+2)₋)`. -/
lemma ER_Tsw'_le_weightedCount (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) :
    ER_Tsw' χ z x
      ≤ 2 * Lwin x
          * ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsERTsw χ z n),
              Λ (nMinus χ (n + 2)) := by
  rw [ER_Tsw', Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_filter] at hn
  exact erTsw_summand_le χ hsq hn.1 hn.2

/-! ## §4 — the `U`-fibration count (unconditional, `PretenseSum`-carrying)

The `χ=+1` prime `U = (n+2)₊` indexes the fibration: `n ↦ U` maps the family into the
`χ=+1` primes `z ≤ U ≤ 2x+2` (`Finset.sum_fiberwise_of_maps_to`).  Within a fiber the map
`n ↦ w = (n+2)₋` is injective (`n + 2 = U·w`), so the fiber's `Λ(w)`-mass is at most
`ψ((2x+2)/U) ≤ (log4+4)·(2x+2)/U` (Chebyshev, `Chebyshev.psi_le_const_mul_self`), and the
`U`-sum pays `Σ 1/U ≤ PretenseSum/log z` (`sum_inv_plusprime_le_pretense`).  This is the
sharpest unconditional count the landed engine yields — see NOTES for the one-log gap. -/

open Classical in
/-- **The fibration maps-to fact.**  On the family, `U = (n+2)₊` is a `χ=+1` prime with
    `z ≤ U ≤ 2x+2` — a member of the `PretenseSum` conversion's index set. -/
lemma erTsw_maps_to (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) :
    ∀ n ∈ (l2cWindow χ z x).filter (fun n => IsERTsw χ z n),
      nPlus χ (n + 2)
        ∈ (Finset.range (2 * x + 2 + 1)).filter
            (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p) := by
  intro n hn
  rw [Finset.mem_filter] at hn
  obtain ⟨hnW, hfam⟩ := hn
  have hUp : (nPlus χ (n + 2)).Prime := hfam.2.2.2.1
  have hUdvd : nPlus χ (n + 2) ∣ n + 2 :=
    ⟨nMinus χ (n + 2), eq_nPlus_mul_nMinus χ hsq (by omega) (l2cWindow_np2_coprime_q χ hnW)⟩
  have hchi : chiRe χ (nPlus χ (n + 2)) = 1 := erTsw_chiRe_nPlus_eq_one χ hUp
  have hUz : z ≤ nPlus χ (n + 2) :=
    l2cWindow_roughness χ z x hnW hUp (hUdvd.trans (dvd_mul_left (n + 2) n))
      (by rw [hchi]; norm_num)
  have hUle : nPlus χ (n + 2) ≤ 2 * x + 2 := by
    have h1 := Nat.le_of_dvd (by omega) hUdvd
    have h2 := ((l2cWindow_mem_iff χ z x n).mp hnW).1.2
    omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hUp, hchi, hUz⟩

open Classical in
/-- **The unconditional weighted count.**  `Σ_{n∈Tsw'} Λ((n+2)₋)
    ≤ (log4+4)·(2x+2)·PretenseSum χ (2x+2)/log z` — the `U`-fibration with the Chebyshev
    per-fiber `w`-mass and the `PretenseSum` conversion on `Σ 1/U`. -/
lemma erTsw_weightedCount_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz1 : 1 < z) :
    ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsERTsw χ z n), Λ (nMinus χ (n + 2))
      ≤ (Real.log 4 + 4) * (2 * (x : ℝ) + 2)
          * (PretenseSum χ (2 * x + 2) / Real.log z) := by
  have hlog4 : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have h0 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith only [h0]
  rw [← Finset.sum_fiberwise_of_maps_to (erTsw_maps_to χ hsq z x)
    (fun n => Λ (nMinus χ (n + 2)))]
  have hfiber : ∀ U ∈ (Finset.range (2 * x + 2 + 1)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p),
      (∑ n ∈ ((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
          (fun n => nPlus χ (n + 2) = U), Λ (nMinus χ (n + 2)))
        ≤ (Real.log 4 + 4) * (2 * (x : ℝ) + 2) * (1 / U) := by
    intro U hU
    rw [Finset.mem_filter] at hU
    have hUpos : 0 < U := hU.2.1.pos
    -- the block decomposition on a fiber element: `n + 2 = U·w`
    have hdec : ∀ n ∈ ((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
        (fun n => nPlus χ (n + 2) = U),
        n + 2 = U * nMinus χ (n + 2) ∧ n + 2 ≤ 2 * x + 2 := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_filter] at hn
      obtain ⟨⟨hnW, _⟩, hnU⟩ := hn
      constructor
      · rw [← hnU]
        exact eq_nPlus_mul_nMinus χ hsq (by omega) (l2cWindow_np2_coprime_q χ hnW)
      · have h2 := ((l2cWindow_mem_iff χ z x n).mp hnW).1.2
        omega
    -- injectivity of `n ↦ w` on the fiber
    have hinj : ∀ n ∈ ((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
        (fun n => nPlus χ (n + 2) = U),
        ∀ n' ∈ ((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
          (fun n => nPlus χ (n + 2) = U),
        nMinus χ (n + 2) = nMinus χ (n' + 2) → n = n' := by
      intro n hn n' hn' heq
      have h1 := (hdec n hn).1
      have h2 := (hdec n' hn').1
      rw [heq] at h1
      omega
    -- the image lands in `Ioc 0 ((2x+2)/U)`
    have himg : (((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
        (fun n => nPlus χ (n + 2) = U)).image (fun n => nMinus χ (n + 2))
          ⊆ Finset.Ioc 0 ((2 * x + 2) / U) := by
      intro w hw
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨h1, h2⟩ := hdec n hn
      rw [Finset.mem_Ioc]
      refine ⟨nMinus_pos χ (n + 2), (Nat.le_div_iff_mul_le hUpos).mpr ?_⟩
      rw [mul_comm]
      omega
    have hcast : (((2 * x + 2) / U : ℕ) : ℝ) ≤ (2 * (x : ℝ) + 2) / U := by
      refine le_trans Nat.cast_div_le (le_of_eq ?_)
      push_cast
      ring
    calc (∑ n ∈ ((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
          (fun n => nPlus χ (n + 2) = U), Λ (nMinus χ (n + 2)))
        = ∑ w ∈ (((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
            (fun n => nPlus χ (n + 2) = U)).image (fun n => nMinus χ (n + 2)), Λ w :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ w ∈ Finset.Ioc 0 ((2 * x + 2) / U), Λ w :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => vonMangoldt_nonneg)
      _ = Chebyshev.psi (((2 * x + 2) / U : ℕ) : ℝ) :=
          Salt.Maynard.sum_vonMangoldt_eq_psi _
      _ ≤ (Real.log 4 + 4) * (((2 * x + 2) / U : ℕ) : ℝ) :=
          Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)
      _ ≤ (Real.log 4 + 4) * ((2 * (x : ℝ) + 2) / U) :=
          mul_le_mul_of_nonneg_left hcast hlog4
      _ = (Real.log 4 + 4) * (2 * (x : ℝ) + 2) * (1 / U) := by ring
  calc (∑ U ∈ (Finset.range (2 * x + 2 + 1)).filter
        (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p),
        ∑ n ∈ ((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
          (fun n => nPlus χ (n + 2) = U), Λ (nMinus χ (n + 2)))
      ≤ ∑ U ∈ (Finset.range (2 * x + 2 + 1)).filter
          (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p),
          (Real.log 4 + 4) * (2 * (x : ℝ) + 2) * (1 / U) := Finset.sum_le_sum hfiber
    _ = (Real.log 4 + 4) * (2 * (x : ℝ) + 2)
          * ∑ U ∈ (Finset.range (2 * x + 2 + 1)).filter
              (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / U := by
        rw [Finset.mul_sum]
    _ ≤ (Real.log 4 + 4) * (2 * (x : ℝ) + 2)
          * (PretenseSum χ (2 * x + 2) / Real.log z) := by
        refine mul_le_mul_of_nonneg_left ?_ ?_
        · exact sum_inv_plusprime_le_pretense χ z (2 * x + 2) hz1
        · have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
          have h2x : (0 : ℝ) ≤ 2 * (x : ℝ) + 2 := by linarith only [hx0]
          exact mul_nonneg hlog4 h2x

/-! ## §5 — the unconditional pretense budget `≤ 56·x·z₀·PS` -/

/-- `PretenseSum χ N ≥ 0` (family-prefixed copy; single-writer name law). -/
lemma erTsw_pretenseSum_nonneg (χ : DirichletCharacter ℂ q) (N : ℕ) :
    0 ≤ PretenseSum χ N := by
  rw [PretenseSum]
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)) (Nat.cast_nonneg p)

/-- **The unconditional T-sw' pretense budget.**  `ER_Tsw' ≤ 56·x·z₀·PretenseSum χ (2x+2)`
    — the reduction times the `U`-fibration count (`2L'·(log4+4)(2x+2)·PS/log z`, and
    `L'/log z = z₀`, `log 4 + 4 ≤ 7`, `2x+2 ≤ 4x`).  This is `J2` with `e^{5z₀}/L'`
    replaced by `z₀·(L'/L') = z₀`: one `n`-side sieve log short of the frozen row. -/
theorem ER_Tsw'_pretense_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ER_Tsw' χ z x ≤ 56 * (x : ℝ) * z0 z x * PretenseSum χ (2 * x + 2) := by
  have hz1 : 1 < z := by omega
  have hlogz : 0 < Real.log z := Real.log_pos (by exact_mod_cast hz1)
  have hx8 : (8 : ℝ) ≤ (x : ℝ) := by
    have h2z : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 2 ≤ z)
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (z : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) h2z 3
      _ ≤ (x : ℝ) := hzx
  have hL0 : 0 ≤ Lwin x := Lwin_nonneg x
  refine le_trans (ER_Tsw'_le_weightedCount χ hsq z x) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (erTsw_weightedCount_le χ hsq hz1)
    (by linarith only [hL0] : (0 : ℝ) ≤ 2 * Lwin x)) ?_
  have hkey : 2 * Lwin x * ((Real.log 4 + 4) * (2 * (x : ℝ) + 2)
        * (PretenseSum χ (2 * x + 2) / Real.log z))
      = (Real.log 4 + 4) * (2 * (x : ℝ) + 2) * 2 * z0 z x
          * PretenseSum χ (2 * x + 2) := by
    rw [z0]
    field_simp
  rw [hkey]
  have hlog4 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith only [h]
  have hz0 : 0 ≤ z0 z x := z0_nonneg (by omega)
  have hPS : 0 ≤ PretenseSum χ (2 * x + 2) := erTsw_pretenseSum_nonneg χ _
  have h1 : (Real.log 4 + 4) * (2 * (x : ℝ) + 2) * 2 ≤ 56 * (x : ℝ) := by
    have hA : Real.log 4 + 4 ≤ 7 := by linarith only [hlog4]
    have hB : 2 * (x : ℝ) + 2 ≤ 4 * (x : ℝ) := by linarith only [hx8]
    have h2x : (0 : ℝ) ≤ 2 * (x : ℝ) + 2 := by linarith only [hx8]
    have hAB : (Real.log 4 + 4) * (2 * (x : ℝ) + 2) ≤ 7 * (4 * (x : ℝ)) :=
      mul_le_mul hA hB h2x (by norm_num)
    linarith only [hAB]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hz0) hPS

/-! ## §6 — the exp-arithmetic and the frozen `J2` conclusion from the count residual -/

/-- `3 ≤ z₀` in-regime (`z³ ≤ x` gives `3·log z ≤ log x ≤ L'`). -/
lemma erTsw_three_le_z0 {z x : ℕ} (hz1 : 1 < z) (hzx : (z : ℝ) ^ 3 ≤ x) : 3 ≤ z0 z x := by
  have hzr : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz1
  have hlogz : 0 < Real.log z := Real.log_pos hzr
  have hz3pos : (0 : ℝ) < (z : ℝ) ^ 3 := by positivity
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le hz3pos hzx
  have h1 : Real.log ((z : ℝ) ^ 3) ≤ Real.log (2 * (x : ℝ) + 2) :=
    Real.log_le_log hz3pos (by linarith only [hzx, hxpos])
  rw [Real.log_pow] at h1
  push_cast at h1
  rw [z0, le_div_iff₀ hlogz, Lwin]
  linarith only [h1]

/-- **The `Aexp = 5` budget arithmetic** for the T-sw' chain: `2·t² ≤ e^{5t}` for `t ≥ 3`
    (`t² ≤ e^{2t}` and `2 ≤ e^{3t}`). -/
lemma erTsw_two_z0sq_le_exp {t : ℝ} (h3 : 3 ≤ t) : 2 * t ^ 2 ≤ Real.exp (5 * t) := by
  have ht : 0 ≤ t := by linarith only [h3]
  have h1 : t ≤ Real.exp t := by
    have h := Real.add_one_le_exp t
    linarith only [h]
  have h2 : t ^ 2 ≤ Real.exp (2 * t) := by
    have hsq : Real.exp t ^ 2 = Real.exp (2 * t) := by rw [sq, ← Real.exp_add, two_mul]
    rw [← hsq]
    exact pow_le_pow_left₀ ht h1 2
  have h4 : (2 : ℝ) ≤ Real.exp (3 * t) := by
    have h9 : (9 : ℝ) ≤ 3 * t := by linarith only [h3]
    have hA : (10 : ℝ) ≤ Real.exp 9 := by
      have h := Real.add_one_le_exp (9 : ℝ)
      linarith only [h]
    have hB : Real.exp 9 ≤ Real.exp (3 * t) := Real.exp_le_exp.mpr h9
    linarith only [hA, hB]
  calc 2 * t ^ 2 ≤ 2 * Real.exp (2 * t) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ Real.exp (3 * t) * Real.exp (2 * t) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = Real.exp (5 * t) := by
        rw [← Real.exp_add]
        congr 1
        ring

open Classical in
/-- **`ER_Tsw'_bound` (the frozen `J2` conclusion), conditional on the count residual.**
    From the reduction `ER_Tsw' ≤ 2L'·Σ_{n∈Tsw'} Λ((n+2)₋)` and the count-engine residual
    `hcount : Σ_{n∈Tsw'} Λ((n+2)₋) ≤ Ccount·x·PS/(log z)²`, the T-sw' budget obeys the
    frozen swap-family shape

    `ER_Tsw' χ z x ≤ Ccount·(x / L')·exp(5·z₀)·PretenseSum χ (2x+2)`

    with `Cmain := Ccount` an absolute constant (the residual constant), via
    `2·z₀² ≤ e^{5z₀}` (`z₀ ≥ 3` in-regime).  The residual `hcount` is the joint
    "`n` prime × `(n+2)₊` a `χ=+1` prime" count at `(log z)²`-savings; its exact status
    against the landed engine is recorded in the NOTES block below (LOUD: it is
    engine-blocked, not merely unfinished — the unconditional landed count
    `erTsw_weightedCount_le` reaches `(log z)¹`). -/
theorem ER_Tsw'_bound_of_count (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (_hz8 : (Lwin x) ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    {Ccount : ℝ} (hCcount : 0 ≤ Ccount)
    (hcount : ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsERTsw χ z n),
        Λ (nMinus χ (n + 2))
        ≤ Ccount * x * PretenseSum χ (2 * x + 2) / (Real.log z) ^ 2) :
    ER_Tsw' χ z x
      ≤ Ccount * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by
  have hz1 : 1 < z := by omega
  have hlogz : 0 < Real.log z := Real.log_pos (by exact_mod_cast hz1)
  have hLpos : 0 < Lwin x := by
    rw [Lwin]
    have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
    exact Real.log_pos (by linarith only [hx0])
  have hPS : 0 ≤ PretenseSum χ (2 * x + 2) := erTsw_pretenseSum_nonneg χ _
  refine le_trans (ER_Tsw'_le_weightedCount χ hsq z x) ?_
  refine le_trans (mul_le_mul_of_nonneg_left hcount
    (by linarith only [hLpos] : (0 : ℝ) ≤ 2 * Lwin x)) ?_
  have halg : 2 * Lwin x * (Ccount * x * PretenseSum χ (2 * x + 2) / (Real.log z) ^ 2)
      = (Ccount * x * PretenseSum χ (2 * x + 2) / Lwin x) * (2 * z0 z x ^ 2) := by
    rw [z0]
    field_simp
  rw [halg]
  have hexp : 2 * z0 z x ^ 2 ≤ Real.exp (5 * z0 z x) :=
    erTsw_two_z0sq_le_exp (erTsw_three_le_z0 hz1 hzx)
  have hnn : 0 ≤ Ccount * x * PretenseSum χ (2 * x + 2) / Lwin x :=
    div_nonneg (mul_nonneg (mul_nonneg hCcount (Nat.cast_nonneg x)) hPS) hLpos.le
  calc (Ccount * x * PretenseSum χ (2 * x + 2) / Lwin x) * (2 * z0 z x ^ 2)
      ≤ (Ccount * x * PretenseSum χ (2 * x + 2) / Lwin x) * Real.exp (5 * z0 z x) :=
        mul_le_mul_of_nonneg_left hexp hnn
    _ = Ccount * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by ring

/-! ## §7 — NOTES: the T-sw' engine gap (LOUD; Wave-3 / count-engine consumption)

**The frozen unconditional row `ER_Tsw'_bound` is ENGINE-BLOCKED, not merely unfinished.**
The roles-swap inverts the freeze §S4 T-sw modulus law.  In `E_L` T-sw the big block
`w ≥ z` forces the `χ=+1` prime `U = (n+2)₊ ≤ (2x+2)/z` — small enough to be a *modulus*
(`d₂ := U`), so one pair-count application yields the sieve gain `(log Zz)⁻²` on the two
big cofactors *and* pays `PretenseSum` via `Σ 1/U`.  In `E_R` T-sw' the small block sits
on the `n+2` side, so the `χ=+1` prime is the HUGE cofactor `U = (n+2)/w > x/z` (the
`n`-side is the bare prime `n = p > x`): every legal modulus assignment loses one of the
two ingredients —

* `d₂ := w` (any `w < z`; both cofactors `p > x ≥ Zf`, `U > x/z ≥ Zf`, so the `Zf`-sift
  is *sound* per amendment 3): full sieve gain, but the count is `χ`-blind — no `PS`;
  totals `≤ C·x/z₀` (`J1`-shaped, NOT `≤ J2` — `PS` may vanish while `x/z₀` does not).
* `d₂ := U`: legality `U·Z⁸(log Z)² ≤ 32x` FAILS (`x/U < w < z ≪ Z⁸` for every landed
  floor `Zz`, `Zf`); the raw `2Z⁸` junk term times `#U ~ x·PS/L'` fibers is fatal.
* `d₂ := w·U = n+2`: singleton fibers, legality dead.
* `chebyshev_chi_count` on `U`: pays `PS` but is sieve-blind on the `n`-side prime;
  totals `≤ C·x·PS·log z` — off `J2` by `L'·log z/e^{5z₀}` (enemy regime `z₀ ~ 3`,
  `L' → ∞`, allowed by `hz8`).

The enemy configuration `z₀ ~ 3` (`z ~ x^{1/3}`), `PS → 0`, `L' → ∞` defeats every
combination (including `min`/interpolation — `J2` is linear in `PS`).  The landed
unconditional optimum is `erTsw_weightedCount_le` (the `U`-fibration with a Chebyshev
`ψ`-mass per fiber): `Σ_{Tsw'} Λ(w) ≤ (log4+4)(2x+2)·PS/log z` — `(log z)¹`-savings,
hence `ER_Tsw'_pretense_bound ≤ 56·x·z₀·PS`, exactly ONE `n`-side sieve log short of the
frozen `J2` (which needs `(log z)²`).  The missing log is the primality of `n = wU − 2`
inside each `U`-fiber: extracting it *while keeping the `χ=+1` restriction on `U`* needs
a `χ`-weighted one-form sieve count (a genuinely new S3-engine lemma of
`MixedCount`-grade — sift `wU−2` over `χ=+1 prime` moduli `U`, or a pretense-weighted
`hb_lemma8'` variant), or a Chen-track import — both statement-layer decisions above this
file's tier (freeze S3 pins the engine; iron rule 1).

**Interface landed for Wave 3** (uniform with `L2cELTsw`): the frozen `J2` conclusion is
`ER_Tsw'_bound_of_count`, conditional on the named residual
`hcount : Σ_{n∈Tsw'} Λ((n+2)₋) ≤ Ccount·x·PS(2x+2)/(log z)²`; the unconditional
`(log z)¹` fallback `ER_Tsw'_pretense_bound` is available should the master ledger accept
a `x·z₀·PS` row for this block.  Amendment compliance: the `w`-side junk blocks are
excluded by the inline `ERTswJunkBlock` guard in `IsERTsw` (they belong to
`ER_wJunk_bound`, the junk row, per amendment 2); NO sift floor is consumed by the landed
proofs (the `ψ`-route is sieve-free), and for any future `hcount` discharge both
cofactors are `≥ Zf`-scale as noted above.  W3 reconciles the cover
`ER_prime_cover = T1' ∪ T2' ∪ T3' ∪ (Tsw' ∪ w-junk)` via the trivial iff-lemmas of the
amendment ruling. -/

end Salt.HB
