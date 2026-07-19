/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cEL
import Salt.HB.L2cER

/-!
# HB-L2c — the EVEN-CORNER row: the structural layer (node HB-L2c, catch #246)

The sixth ledger line of the exact-overshoot surgery (house amendment 2): the even class
of BOTH overshoot summands over the honest window,

`evenCornerSum χ z x := Σ_{n ∈ W, ¬Odd n} overshootExact χ n`,

which is nonempty only when `χ_ℝ(2) = −1` (then `2 ∉ excPrimorial` and the window admits
even elements; `evenCornerSum_eq_zero_of_chiRe_two_ne` disposes of every other `χ`).

## What this file lands

The complete provable **structural layer** of the row — everything any pricing route
must consume:

* the character dichotomy (`evenCorner_chiRe_two`, `evenCornerSum_eq_zero_of_chiRe_two_ne`);
* **the even-survivor classification** (`evenCorner_survivor`, the house-verified core):
  a nonzero even term forces BOTH `χ=−1` blocks pure — `n₋ = 2^{e₁}`, `(n+2)₋ = 2^{e₂}`
  (any odd `χ=−1` block alongside a `2`-power dies by the two-block kill);
* **the exponent split** (`evenCorner_exponent_split`, the fiber law): `e₁ ≥ 2 ⟹ e₂ = 1`
  and `e₁ = 1 ⟹ e₂ ≥ 2` — one free exponent;
* **the sharp weight cap** (`evenCorner_term_le`): every even term is `≤ e^{2z₀}`
  (both factors `≤ e^{(log2)z₀}·log 2` by `lamTilde_single_block_le` at `Λ(2^e) = log 2`,
  and `2(log 2)² ≤ 1`);
* **the survivor-count reduction** (`evenCornerSum_le_survivor_card`, the Zeno cut) and
  the crude count/bound (`evenCornerSet_card_le`, `evenCornerSum_le_crude` — `x`-grade,
  clearly marked PARTIAL).

## What this file does NOT land

The catch-#246 FROZEN conclusion `≤ Cmain·e^{2z₀}·x^{9/10}·L'³` is **not** claimed: the
executor magnitude audit found it unreachable (the amendment's absorption step runs an
inequality backwards, and the `(d₁,d₂) = (1,1)` sift set excludes even `n` outright).
See the §5 NOTES block and the executor report; statement-layer resolution is
Fable/house-tier (iron rule 1).  No frozen statement is altered here — the row's bound
is simply left as the named residual.

Single-writer file (`L2cEven.lean`); imports the landed `L2cEL`/`L2cER`/`L2cCore`
surfaces and touches no other file (`Salt.HB.All` is Wave 3's manifest).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — the even slice and its sum -/

open Classical in
/-- **The even-corner slice** of the honest window: `{n ∈ W : ¬ Odd n}`.  By the parity
    link (`l2cWindow_parity_link`) this simultaneously captures both even sides
    (`n` even ⟺ `n+2` even). -/
noncomputable def evenCornerSet (χ : DirichletCharacter ℂ q) (z x : ℕ) : Finset ℕ :=
  (l2cWindow χ z x).filter (fun n => ¬ Odd n)

/-- Membership in the even slice, unpacked. -/
lemma evenCorner_mem (χ : DirichletCharacter ℂ q) {z x n : ℕ} :
    n ∈ evenCornerSet χ z x ↔ n ∈ l2cWindow χ z x ∧ ¬ Odd n := by
  unfold evenCornerSet
  rw [Finset.mem_filter]

/-- **The even-corner sum** `Σ_{n ∈ W, ¬Odd n} overshootExact χ n` — the even class of
    BOTH overshoot summands, the catch-#246 row's left-hand side. -/
noncomputable def evenCornerSum (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ evenCornerSet χ z x, overshootExact χ n

/-- Each overshoot term is nonnegative (Lemma 1(b) on all four factors). -/
lemma evenCorner_overshoot_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ overshootExact χ n := by
  unfold overshootExact
  exact add_nonneg (EL_summand_nonneg χ hsq n)
    (mul_nonneg vonMangoldt_nonneg (lamTilde_sub_nonneg χ hsq (n + 2)))

/-! ## §1 — the character dichotomy: the row lives only at `χ_ℝ(2) = −1` -/

/-- **Even window elements force `χ_ℝ(2) = −1`.**  Otherwise `2` sits in
    `excPrimorial χ z` (it is a small prime with `χ_ℝ(2) ≠ −1`), contradicting the
    window's coprimality. -/
lemma evenCorner_chiRe_two (χ : DirichletCharacter ℂ q) {z x n : ℕ} (hz2 : 2 < z)
    (hn : n ∈ l2cWindow χ z x) (hev : ¬ Odd n) : chiRe χ 2 = -1 := by
  by_contra hne
  have h2n : 2 ∣ n := by
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨r, hr⟩ := he; omega
    · exact absurd ho hev
  have hmem : 2 ∈ (Finset.range z).filter (fun p => p.Prime ∧ chiRe χ p ≠ -1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hz2, Nat.prime_two, hne⟩
  have hdvdP : 2 ∣ excPrimorial χ z := Finset.dvd_prod_of_mem _ hmem
  have hcop := l2cWindow_excPrimorial_coprime χ z x n hn
  have hgcd : 2 ∣ Nat.gcd (n * (n + 2)) (excPrimorial χ z) :=
    Nat.dvd_gcd (dvd_mul_of_dvd_left h2n (n + 2)) hdvdP
  have hc1 : Nat.gcd (n * (n + 2)) (excPrimorial χ z) = 1 := hcop
  rw [hc1] at hgcd
  omega

/-- **The dichotomy.**  When `χ_ℝ(2) ≠ −1` the even slice is empty and the row is `0`:
    the catch-#246 row is a `χ_ℝ(2) = −1` phenomenon exactly as amendment 2 rules. -/
theorem evenCornerSum_eq_zero_of_chiRe_two_ne (χ : DirichletCharacter ℂ q) {z x : ℕ}
    (hz2 : 2 < z) (hchi : chiRe χ 2 ≠ -1) : evenCornerSum χ z x = 0 := by
  rw [evenCornerSum]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [evenCorner_mem] at hn
  exact absurd (evenCorner_chiRe_two χ hz2 hn.1 hn.2) hchi

/-! ## §2 — the 2-adic block structure of even survivors -/

/-- On an even coprime `m` (with `χ_ℝ(2) = −1`), the prime `2` sits in the `χ=−1`
    block: `2 ∣ m₋` (it cannot divide `m₊`, whose primes all have `χ_ℝ = +1`). -/
lemma evenCorner_two_dvd_nMinus (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ}
    (hm0 : m ≠ 0) (hcop : Nat.Coprime m q) (h2 : 2 ∣ m) (hchi : chiRe χ 2 = -1) :
    2 ∣ nMinus χ m := by
  have hsplit := eq_nPlus_mul_nMinus χ hsq hm0 hcop
  rw [hsplit] at h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exfalso
    have hsign := nPlus_dvd_sign Nat.prime_two h
    rw [hchi] at hsign
    norm_num at hsign
  · exact h

/-- A prime power divisible by `2` is a pure `2`-power. -/
lemma evenCorner_pp_two {m : ℕ} (hpp : IsPrimePow m) (h2 : 2 ∣ m) :
    ∃ e, 1 ≤ e ∧ m = 2 ^ e := by
  obtain ⟨p, k, hp, hk, hpk⟩ := hpp
  have hpN : p.Prime := Nat.prime_iff.mpr hp
  have h2pk : (2 : ℕ) ∣ p ^ k := by rw [hpk]; exact h2
  have h2p : (2 : ℕ) ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2pk
  have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpN).mp h2p).symm
  exact ⟨k, by omega, by rw [← hpk, hp2]⟩

/-- **The block extractor.**  If `Λ̃(m) ≠ 0` on an even coprime `m` (with
    `χ_ℝ(2) = −1`), the `χ=−1` block is a pure `2`-power: `m₋ = 2^e`, `e ≥ 1`.
    (Two or more blocks kill `Λ̃`; the surviving single block contains `2`.) -/
lemma evenCorner_block_of_lamTilde_ne (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {m : ℕ} (hm0 : m ≠ 0) (hcop : Nat.Coprime m q) (h2 : 2 ∣ m) (hchi : chiRe χ 2 = -1)
    (hne : LamTilde χ m ≠ 0) : ∃ e, 1 ≤ e ∧ nMinus χ m = 2 ^ e := by
  have h2M : 2 ∣ nMinus χ m := evenCorner_two_dvd_nMinus χ hsq hm0 hcop h2 hchi
  have hM0 : nMinus χ m ≠ 0 := (nMinus_pos χ m).ne'
  have hmem2 : 2 ∈ (nMinus χ m).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2M, hM0⟩
  have hcard_le : (nMinus χ m).primeFactors.card ≤ 1 := by
    by_contra hgt
    exact hne (LamTilde_eq_zero_of_two_le_card χ hsq hm0 hcop (by omega))
  have hcard : (nMinus χ m).primeFactors.card = 1 := by
    have hpos : 0 < (nMinus χ m).primeFactors.card := Finset.card_pos.mpr ⟨2, hmem2⟩
    omega
  exact evenCorner_pp_two (isPrimePow_iff_card_primeFactors_eq_one.mpr hcard) h2M

/-- The `(Λ̃−Λ)`-difference version: `(Λ̃−Λ)(m) ≠ 0` forces `Λ̃(m) ≠ 0` (Lemma 1(b):
    `0 ≤ Λ ≤ Λ̃`), so the block is again a pure `2`-power. -/
lemma evenCorner_block_of_diff_ne (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {m : ℕ} (hm0 : m ≠ 0) (hcop : Nat.Coprime m q) (h2 : 2 ∣ m) (hchi : chiRe χ 2 = -1)
    (hne : LamTilde χ m - Λ m ≠ 0) : ∃ e, 1 ≤ e ∧ nMinus χ m = 2 ^ e := by
  refine evenCorner_block_of_lamTilde_ne χ hsq hm0 hcop h2 hchi fun h0 => hne ?_
  have hΛ : Λ m = 0 :=
    le_antisymm (h0 ▸ vonMangoldt_le_LamTilde χ hsq m) vonMangoldt_nonneg
  rw [h0, hΛ, sub_zero]

/-- **THE EVEN-SURVIVOR CLASSIFICATION** (the house-verified structural core of the
    catch-#246 row).  If an even window element carries a nonzero overshoot term, BOTH
    `χ=−1` blocks are pure `2`-powers: `n₋ = 2^{e₁}` and `(n+2)₋ = 2^{e₂}` with
    `e₁, e₂ ≥ 1`.  (First summand: the difference side classifies, the `Λ̃` side
    single-blocks; second summand: `Λ(n) ≠ 0` makes `n` itself an even prime power.) -/
theorem evenCorner_survivor (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hz2 : 2 < z) (hn : n ∈ l2cWindow χ z x) (hev : ¬ Odd n)
    (hne : overshootExact χ n ≠ 0) :
    ∃ e₁ e₂ : ℕ, 1 ≤ e₁ ∧ 1 ≤ e₂ ∧ nMinus χ n = 2 ^ e₁ ∧ nMinus χ (n + 2) = 2 ^ e₂ := by
  have hchi : chiRe χ 2 = -1 := evenCorner_chiRe_two χ hz2 hn hev
  have h2n : 2 ∣ n := by
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨r, hr⟩ := he; omega
    · exact absurd ho hev
  have h2n2 : 2 ∣ n + 2 := by omega
  have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hn
  have hcop : Nat.Coprime n q := l2cWindow_coprime χ hn
  have hcop2 : Nat.Coprime (n + 2) q := l2cWindow_coprime_add_two χ hn
  by_cases hA : (LamTilde χ n - Λ n) * LamTilde χ (n + 2) = 0
  · -- the second summand carries the term
    have hB : Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) ≠ 0 := by
      intro hB0
      refine hne ?_
      unfold overshootExact
      rw [hA, hB0, add_zero]
    obtain ⟨hΛn, hD⟩ := mul_ne_zero_iff.mp hB
    obtain ⟨e₂, he₂, hM2⟩ :=
      evenCorner_block_of_diff_ne χ hsq (by omega) hcop2 h2n2 hchi hD
    -- left side: `n` is an even prime power, so `n = 2^k`, and `n₋` is a `2`-power too
    have hpp : IsPrimePow n := by
      by_contra hcon
      exact hΛn (vonMangoldt_eq_zero_iff.mpr hcon)
    obtain ⟨k, _, hnk⟩ := evenCorner_pp_two hpp h2n
    have h2M : 2 ∣ nMinus χ n := evenCorner_two_dvd_nMinus χ hsq hn0 hcop h2n hchi
    have hMdvd : nMinus χ n ∣ n :=
      ⟨nPlus χ n, by rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq hn0 hcop⟩
    have hMd2 : nMinus χ n ∣ 2 ^ k := by rw [← hnk]; exact hMdvd
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hMd2
    have hj1 : 1 ≤ j := by
      by_contra hj0
      have hj0' : j = 0 := by omega
      rw [hj0', pow_zero] at hj
      rw [hj] at h2M
      omega
    exact ⟨j, e₂, hj1, he₂, hj, hM2⟩
  · obtain ⟨hL, hR⟩ := mul_ne_zero_iff.mp hA
    obtain ⟨e₁, he₁, hM1⟩ := evenCorner_block_of_diff_ne χ hsq hn0 hcop h2n hchi hL
    obtain ⟨e₂, he₂, hM2⟩ :=
      evenCorner_block_of_lamTilde_ne χ hsq (by omega) hcop2 h2n2 hchi hR
    exact ⟨e₁, e₂, he₁, he₂, hM1, hM2⟩

/-- Under `χ_ℝ(2) = −1` the `χ=+1` part of anything is odd. -/
lemma evenCorner_nPlus_odd (χ : DirichletCharacter ℂ q) (hchi : chiRe χ 2 = -1) (n : ℕ) :
    ¬ 2 ∣ nPlus χ n := by
  intro h
  have hsign := nPlus_dvd_sign Nat.prime_two h
  rw [hchi] at hsign
  norm_num at hsign

/-- **The exponent split** (the fiber law of the even corner): the two pure blocks
    interlock — `e₁ ≥ 2` forces `e₂ = 1` and `e₁ = 1` forces `e₂ ≥ 2` (`n` and `n+2`
    differ by `2` and both `+`-parts are odd, so exactly one side is `≡ 0 mod 4`).
    Effectively ONE free exponent — the fiber structure of any future counting route. -/
lemma evenCorner_exponent_split (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {z x n : ℕ} (hz2 : 2 < z) (hn : n ∈ l2cWindow χ z x) (hev : ¬ Odd n) {e₁ e₂ : ℕ}
    (_he₁ : 1 ≤ e₁) (he₂ : 1 ≤ e₂) (hM1 : nMinus χ n = 2 ^ e₁)
    (hM2 : nMinus χ (n + 2) = 2 ^ e₂) :
    (2 ≤ e₁ → e₂ = 1) ∧ (e₁ = 1 → 2 ≤ e₂) := by
  have hchi := evenCorner_chiRe_two χ hz2 hn hev
  have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hn
  have hsplit1 : n = nPlus χ n * 2 ^ e₁ := by
    have h := eq_nPlus_mul_nMinus χ hsq hn0 (l2cWindow_coprime χ hn)
    rw [hM1] at h; exact h
  have hsplit2 : n + 2 = nPlus χ (n + 2) * 2 ^ e₂ := by
    have h := eq_nPlus_mul_nMinus χ hsq (by omega) (l2cWindow_coprime_add_two χ hn)
    rw [hM2] at h; exact h
  have hodd1 : ¬ 2 ∣ nPlus χ n := evenCorner_nPlus_odd χ hchi n
  have hodd2 : ¬ 2 ∣ nPlus χ (n + 2) := evenCorner_nPlus_odd χ hchi (n + 2)
  constructor
  · intro h2e
    by_contra hne2
    have h2e2 : 2 ≤ e₂ := by omega
    have h4n : (2 : ℕ) ^ 2 ∣ n := by
      rw [hsplit1]; exact (pow_dvd_pow 2 h2e).mul_left _
    have h4n2 : (2 : ℕ) ^ 2 ∣ n + 2 := by
      rw [hsplit2]; exact (pow_dvd_pow 2 h2e2).mul_left _
    norm_num at h4n h4n2
    omega
  · intro he₁1
    by_contra hne2
    have he₂1 : e₂ = 1 := by omega
    rw [he₁1, pow_one] at hsplit1
    rw [he₂1, pow_one] at hsplit2
    omega

/-! ## §3 — the sharp weight cap: every even term is `≤ e^{2z₀}` -/

/-- `Λ(2^e) = log 2` for `e ≥ 1`. -/
lemma evenCorner_vonMangoldt_two_pow {e : ℕ} (he : 1 ≤ e) :
    Λ ((2 : ℕ) ^ e) = Real.log 2 := by
  rw [vonMangoldt_apply_pow (by omega : e ≠ 0), vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- **The survivor weight cap.**  On a window element whose blocks are pure `2`-powers,
    both overshoot factors obey the sharp single-block cap `Λ̃ ≤ e^{(log2)z₀}·log 2`
    (`lamTilde_single_block_le` with `Λ(2^e) = log 2`), so
    `overshootExact χ n ≤ 2(log2)²·e^{2(log2)z₀} ≤ e^{2z₀}`. -/
lemma evenCorner_survivor_term_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {z x n : ℕ} (hz2 : 2 ≤ z) (hn : n ∈ l2cWindow χ z x) {e₁ e₂ : ℕ}
    (he₁ : 1 ≤ e₁) (he₂ : 1 ≤ e₂) (hM1 : nMinus χ n = 2 ^ e₁)
    (hM2 : nMinus χ (n + 2) = 2 ^ e₂) :
    overshootExact χ n ≤ Real.exp (2 * z0 z x) := by
  have hlog2a : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have hlog2b : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hκ0 : (0 : ℝ) ≤ Real.exp (Real.log 2 * z0 z x) * Real.log 2 :=
    mul_nonneg (Real.exp_pos _).le hlog2b
  have hz00 : 0 ≤ z0 z x := z0_nonneg hz2
  -- the two single-block caps at `Λ(2^e) = log 2`
  have h₁ : LamTilde χ n ≤ Real.exp (Real.log 2 * z0 z x) * Real.log 2 := by
    have hcap := lamTilde_single_block_le χ hsq z x hz2 (l2cWindow_ne_zero χ hn)
      (l2cWindow_coprime χ hn) (by have := l2cWindow_le χ hn; omega)
      (fun p hp hpd hchi => l2cWindow_rough χ hn hp hpd hchi)
      (by rw [hM1]; exact ⟨2, e₁, Nat.prime_two.prime, by omega, rfl⟩)
    rwa [hM1, evenCorner_vonMangoldt_two_pow he₁] at hcap
  have h₂ : LamTilde χ (n + 2) ≤ Real.exp (Real.log 2 * z0 z x) * Real.log 2 := by
    have hcap := lamTilde_single_block_le χ hsq z x hz2 (by omega)
      (l2cWindow_coprime_add_two χ hn) (l2cWindow_add_two_le χ hn)
      (fun p hp hpd hchi => l2cWindow_rough_add_two χ hn hp hpd hchi)
      (by rw [hM2]; exact ⟨2, e₂, Nat.prime_two.prime, by omega, rfl⟩)
    rwa [hM2, evenCorner_vonMangoldt_two_pow he₂] at hcap
  -- the four factor bounds
  have ha : LamTilde χ n - Λ n ≤ Real.exp (Real.log 2 * z0 z x) * Real.log 2 :=
    le_trans (sub_le_self _ vonMangoldt_nonneg) h₁
  have hb0 : 0 ≤ LamTilde χ (n + 2) := lamTilde_nonneg χ hsq (n + 2)
  have hc : Λ n ≤ Real.exp (Real.log 2 * z0 z x) * Real.log 2 :=
    le_trans (vonMangoldt_le_LamTilde χ hsq n) h₁
  have hd : LamTilde χ (n + 2) - Λ (n + 2)
      ≤ Real.exp (Real.log 2 * z0 z x) * Real.log 2 :=
    le_trans (sub_le_self _ vonMangoldt_nonneg) h₂
  have hd0 : 0 ≤ LamTilde χ (n + 2) - Λ (n + 2) := lamTilde_sub_nonneg χ hsq (n + 2)
  have ht1 : (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ (Real.exp (Real.log 2 * z0 z x) * Real.log 2)
        * (Real.exp (Real.log 2 * z0 z x) * Real.log 2) := mul_le_mul ha h₂ hb0 hκ0
  have ht2 : Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ (Real.exp (Real.log 2 * z0 z x) * Real.log 2)
        * (Real.exp (Real.log 2 * z0 z x) * Real.log 2) := mul_le_mul hc hd hd0 hκ0
  have hsum : overshootExact χ n
      ≤ 2 * (Real.exp (Real.log 2 * z0 z x) * Real.log 2) ^ 2 := by
    unfold overshootExact
    calc (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
          + Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
        ≤ (Real.exp (Real.log 2 * z0 z x) * Real.log 2)
            * (Real.exp (Real.log 2 * z0 z x) * Real.log 2)
          + (Real.exp (Real.log 2 * z0 z x) * Real.log 2)
            * (Real.exp (Real.log 2 * z0 z x) * Real.log 2) := add_le_add ht1 ht2
      _ = 2 * (Real.exp (Real.log 2 * z0 z x) * Real.log 2) ^ 2 := by ring
  -- the exponential collapse: `2(log2)²·e^{2(log2)z₀} ≤ 1·e^{2z₀}`
  have hlog2c : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hsq2 : 2 * Real.log 2 ^ 2 ≤ 1 := by
    nlinarith [hlog2b, hlog2c, sq_nonneg (0.6931471808 - Real.log 2)]
  have hKK : Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x)
      = Real.exp (2 * Real.log 2 * z0 z x) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp : Real.exp (2 * Real.log 2 * z0 z x) ≤ Real.exp (2 * z0 z x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (by linarith only [hlog2a] : 2 * Real.log 2 ≤ 2) hz00)
  refine hsum.trans ?_
  calc 2 * (Real.exp (Real.log 2 * z0 z x) * Real.log 2) ^ 2
      = (2 * Real.log 2 ^ 2)
          * (Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x)) := by ring
    _ = (2 * Real.log 2 ^ 2) * Real.exp (2 * Real.log 2 * z0 z x) := by rw [hKK]
    _ ≤ 1 * Real.exp (2 * Real.log 2 * z0 z x) :=
        mul_le_mul_of_nonneg_right hsq2 (Real.exp_pos _).le
    _ = Real.exp (2 * Real.log 2 * z0 z x) := one_mul _
    _ ≤ Real.exp (2 * z0 z x) := hexp

/-- **The even-corner term cap.**  EVERY even window term obeys
    `overshootExact χ n ≤ e^{2z₀}` (zero terms trivially; survivors by the sharp
    single-block caps on both pure `2`-power blocks). -/
lemma evenCorner_term_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hz2 : 2 < z) (hn : n ∈ l2cWindow χ z x) (hev : ¬ Odd n) :
    overshootExact χ n ≤ Real.exp (2 * z0 z x) := by
  by_cases h0 : overshootExact χ n = 0
  · rw [h0]; exact (Real.exp_pos _).le
  · obtain ⟨e₁, e₂, he₁, he₂, hM1, hM2⟩ := evenCorner_survivor χ hsq hz2 hn hev h0
    exact evenCorner_survivor_term_le χ hsq (by omega) hn he₁ he₂ hM1 hM2

/-! ## §4 — the count reductions (the Zeno cut and the crude slice bound) -/

open Classical in
/-- **The survivor-count reduction** (the Zeno cut of the row): the even-corner sum is
    at most `e^{2z₀}` times the number of even SURVIVORS.  Everything above the count is
    landed; the count itself is the row's named residual (§5 NOTES). -/
theorem evenCornerSum_le_survivor_card (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {z x : ℕ} (hz2 : 2 < z) :
    evenCornerSum χ z x
      ≤ (((evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0)).card : ℝ)
          * Real.exp (2 * z0 z x) := by
  have hterm : ∀ n ∈ (evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0),
      overshootExact χ n ≤ Real.exp (2 * z0 z x) := by
    intro n hn
    rw [Finset.mem_filter, evenCorner_mem] at hn
    exact evenCorner_term_le χ hsq hz2 hn.1.1 hn.1.2
  have hle := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hle
  calc evenCornerSum χ z x
      = ∑ n ∈ (evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0),
          overshootExact χ n := by
        rw [evenCornerSum]
        exact (Finset.sum_filter_of_ne fun n _ h => h).symm
    _ ≤ _ := hle

/-- **The crude slice count** `#evenCornerSet ≤ x/2 + 1` (the even elements of a dyadic
    window; `window_dvd_count` at `d = 2`). -/
lemma evenCornerSet_card_le (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    ((evenCornerSet χ z x).card : ℝ) ≤ (x : ℝ) / 2 + 1 := by
  have hsub : evenCornerSet χ z x ⊆ (Finset.Ioc x (2 * x)).filter (fun n => 2 ∣ n) := by
    intro n hn
    rw [evenCorner_mem] at hn
    rw [Finset.mem_filter]
    refine ⟨l2cWindow_subset χ z x hn.1, ?_⟩
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨r, hr⟩ := he; omega
    · exact absurd ho hn.2
  have hcount := window_dvd_count x 2 (by norm_num)
  have hcard : ((evenCornerSet χ z x).card : ℝ)
      ≤ (((Finset.Ioc x (2 * x)).filter (fun n => 2 ∣ n)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine hcard.trans (hcount.trans_eq ?_)
  norm_num

/-- **The crude even-corner bound** (PARTIAL — `x`-grade, NOT the frozen `x^{9/10}` row):
    `evenCornerSum ≤ (x/2 + 1)·e^{2z₀}`.  The frozen catch-#246 conclusion
    `Cmain·e^{2z₀}·x^{9/10}·L'³` is NOT claimed anywhere in this file — the §5 NOTES
    record why no count of this class can reach it. -/
theorem evenCornerSum_le_crude (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz2 : 2 < z) :
    evenCornerSum χ z x ≤ ((x : ℝ) / 2 + 1) * Real.exp (2 * z0 z x) := by
  refine (evenCornerSum_le_survivor_card χ hsq hz2).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  refine le_trans ?_ (evenCornerSet_card_le χ z x)
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-! ## §5 — NOTES: the frozen row and its residual (statement-layer catch, house-tier)

The catch-#246 FROZEN conclusion for this row is

`evenCornerSum χ z x ≤ Cmain·exp(2·z0 z x)·(x:ℝ)^(9/10:ℝ)·(Lwin x)^3`.

It is NOT landed and NOT claimed.  The executor magnitude audit (see the report) found
it unreachable, for three independent reasons:

1. **The amendment's absorption runs backwards.**  Its own count output is
   `C·z0²·x/L'²`-grade; fitting under `x^{9/10}·L'³` needs `x^{1/10} ≤ L'⁵`, which is
   FALSE for large `x`.  The cited (true) inequality `x^{1/10} ≥ L'²` proves the
   *reverse* containment `x^{9/10} ≤ x/L'²`.
2. **The `(d₁,d₂) = (1,1)` sift excludes even `n`.**  The engine's sifted set requires
   `(n(n+2), primorial (Zz z)) = 1`, and `2` divides both sides for even `n` — the even
   fibers do not embed at all, and the engine's oddness side conditions bar the honest
   moduli `2^e` (amendment 2 itself cites this to excise even `n` from the families).
3. **Truth level.**  For `χ_ℝ(2) = −1` (e.g. the quadratic character mod 3) the
   survivors `n = 2P` — `P` a `χ=+1` prime with `odd(P+1)` a `χ=+1`-rough product —
   have Hardy–Littlewood-grade count `≍ x/polylog(x)`, each with weight `≥ 4(log 2)²`;
   the frozen right side is `≤ e^{2z₀}·x^{9/10}·L'³ = x^{9/10+o(1)}` under the packet
   (`hz8` forces `e^{2z₀} = x^{o(1)}`), short by `~x^{1/10−o(1)}`.

The class is NOT character-blind: its cofactors are `χ=+1`-products, and the honest
home of this row is a `J2`-shaped `PretenseSum` budget — exactly the pre-amendment
freeze §S4 CORNERS line (`8x·PS/L'` + junk), which amendment 2 superseded.  Re-freezing
the row's conclusion is a statement-layer, Fable/house-tier decision (iron rule 1);
this file therefore lands the full structural layer (dichotomy, survivor
classification, exponent split, sharp `e^{2z₀}` term cap, survivor-count reduction,
crude `x`-grade bound) and leaves the survivor COUNT as the named residual:

RESIDUAL `evenCorner_count` — bound
`#((evenCornerSet χ z x).filter (overshootExact χ · ≠ 0))` by the re-frozen row shape
(house to supply; the `J2`/`PretenseSum` route fibers on `evenCorner_exponent_split`'s
single free exponent and Chebyshev-counts the `χ=+1` cofactor). -/

/-! ## §6 — the RE-FROZEN row (House Amendment 4, catch #248): `J2 + junk`, engine-free

Amendment 4 re-froze the row's conclusion to the `J2 + standard-junk` shape and supplied
a house-verified route that uses **crude divisor counting only** (no pair-count engine —
the engine's primorial coprimality contains `2`, so even fibers never embed).  This
section lands that bound, `EL_evenCorner_bound`, with `Cmain = 2` (absolute).

The route (proven below):

* every nonzero even term is a survivor with `n₋ = 2^{e₁}`, `n₊` odd (`evenCorner_survivor`
  + `evenCorner_nPlus_odd`);
* **Group 1** (`n₊ > 1`): `p := (n₊).minFac` is an odd `χ=+1` prime `≥ z` dividing `n`;
  since `n` is even and `p` odd, `2p ∣ n ≤ 2x`, so **`p ≤ x`** — the decisive fact.  The
  fibre map `n ↦ p` sends Group 1 into the pretense-prime index set, and each fibre is
  bounded by `window_dvd_count` at `d = p`.  Because `p ≤ x`, the crude `x/p + 1`
  absorbs the `+1` into `2x/p` with NO leftover tail (this is where the amendment's own
  `2x/(2^e z)`-tail sketch was arithmetically off — see the report NOTES);
* **Group 2** (`n₊ = 1`, `n` a pure `2`-power): at most ONE element of `(x,2x]` — junk;
* summation: `Σ_p 1/p ≤ PretenseSum/log z = z₀·PS/L'`; the term cap `e^{2z₀}` times the
  count gives the `J2` line via `z₀·e^{2z₀} ≤ e^{5z₀}`.
-/

/-- `PretenseSum` is nonnegative (a sum of `log p / p ≥ 0`). -/
lemma PretenseSum_nonneg (χ : DirichletCharacter ℂ q) (N : ℕ) : 0 ≤ PretenseSum χ N := by
  rw [PretenseSum]
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)) (by positivity)

/-- `PretenseSum` is monotone in its cutoff (more nonnegative terms). -/
lemma PretenseSum_mono (χ : DirichletCharacter ℂ q) {M N : ℕ} (h : M ≤ N) :
    PretenseSum χ M ≤ PretenseSum χ N := by
  have hrange : Finset.range (M + 1) ⊆ Finset.range (N + 1) := by
    intro k hk; rw [Finset.mem_range] at hk ⊢; omega
  have hsub : (Finset.range (M + 1)).filter (fun p => Nat.Prime p ∧ chiRe χ p = 1)
      ⊆ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ chiRe χ p = 1) :=
    Finset.filter_subset_filter _ hrange
  rw [PretenseSum, PretenseSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
  rw [Finset.mem_filter] at hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)) (by positivity)

/-- **The Group-1 witness.**  For an even window element `n` whose `χ=+1` part is `> 1`,
    `p := (n₊).minFac` is a prime with `χ_ℝ(p) = 1`, `z ≤ p`, `p ∣ n`, and — crucially,
    since `n` is even and `p` is odd so `2p ∣ n ≤ 2x` — `p ≤ x`. -/
lemma evenCorner_witness (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hz2 : 2 < z) (hn : n ∈ l2cWindow χ z x) (hev : ¬ Odd n) (hnP1 : nPlus χ n ≠ 1) :
    (nPlus χ n).minFac.Prime ∧ chiRe χ (nPlus χ n).minFac = 1
      ∧ z ≤ (nPlus χ n).minFac ∧ (nPlus χ n).minFac ∣ n ∧ (nPlus χ n).minFac ≤ x := by
  have hpp : (nPlus χ n).minFac.Prime := Nat.minFac_prime hnP1
  have hpdvdP : (nPlus χ n).minFac ∣ nPlus χ n := Nat.minFac_dvd _
  have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hn
  have hcop : Nat.Coprime n q := l2cWindow_coprime χ hn
  have hPdvdn : nPlus χ n ∣ n := ⟨nMinus χ n, eq_nPlus_mul_nMinus χ hsq hn0 hcop⟩
  have hpdvdn : (nPlus χ n).minFac ∣ n := hpdvdP.trans hPdvdn
  have hsign : chiRe χ (nPlus χ n).minFac = 1 := nPlus_dvd_sign hpp hpdvdP
  have hzp : z ≤ (nPlus χ n).minFac :=
    l2cWindow_rough χ hn hpp hpdvdn (by rw [hsign]; norm_num)
  have h2n : 2 ∣ n := by
    rcases Nat.even_or_odd n with he | ho
    · exact he.two_dvd
    · exact absurd ho hev
  have hcop2p : Nat.Coprime 2 (nPlus χ n).minFac :=
    (Nat.coprime_primes Nat.prime_two hpp).mpr (by omega)
  have h2p_dvd : 2 * (nPlus χ n).minFac ∣ n := hcop2p.mul_dvd_of_dvd_of_dvd h2n hpdvdn
  have hnle : n ≤ 2 * x := l2cWindow_le χ hn
  have h2ple : 2 * (nPlus χ n).minFac ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h2p_dvd
  exact ⟨hpp, hsign, hzp, hpdvdn, by omega⟩

open Classical in
/-- **The Group-1 count.**  The even survivors with `n₊ > 1` number at most
    `2x·(PretenseSum χ (2x+2) / log z)`.  Fibre the class by the witness prime
    `p = (n₊).minFac` (which lands in the pretense index set, `z ≤ p ≤ x`); each fibre is
    `⊆ {n ∈ (x,2x] : p ∣ n}`, bounded by `window_dvd_count` as `x/p + 1 ≤ 2x/p` (the `+1`
    is absorbed because `p ≤ x`, so NO `+1` tail survives); sum `Σ 1/p ≤ PS/log z`. -/
lemma evenCorner_group1_card_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) :
    ((((evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0)).filter
        (fun n => nPlus χ n ≠ 1)).card : ℝ)
      ≤ 2 * (x : ℝ) * (PretenseSum χ (2 * x + 2) / Real.log z) := by
  have hz2 : 2 < z := lt_of_lt_of_le (by norm_num) hz100
  have hz1 : 1 < z := by omega
  have hlogz : 0 < Real.log z := Real.log_pos (by exact_mod_cast hz1)
  set G1 := (((evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0)).filter
      (fun n => nPlus χ n ≠ 1)) with hG1
  set Pset := (Finset.range (x + 1)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p) with hPset
  -- the fibre map lands in `Pset`
  have hmem : ∀ n ∈ G1, (nPlus χ n).minFac ∈ Pset := by
    intro n hn
    rw [hG1, Finset.mem_filter, Finset.mem_filter, evenCorner_mem] at hn
    obtain ⟨⟨⟨hnw, hev⟩, _⟩, hnP1⟩ := hn
    obtain ⟨hpp, hsign, hzp, _, hpx⟩ := evenCorner_witness χ hsq hz2 hnw hev hnP1
    rw [hPset, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpp, hsign, hzp⟩
  have hcard_eq : G1.card = ∑ p ∈ Pset, (G1.filter (fun n => (nPlus χ n).minFac = p)).card :=
    Finset.card_eq_sum_card_fiberwise hmem
  -- each fibre embeds in the divisor slice of `(x,2x]`
  have hfiber : ∀ p ∈ Pset, (G1.filter (fun n => (nPlus χ n).minFac = p)).card
      ≤ ((Finset.Ioc x (2 * x)).filter (fun n => p ∣ n)).card := by
    intro p _
    refine Finset.card_le_card fun n hn => ?_
    rw [Finset.mem_filter] at hn ⊢
    obtain ⟨hnG1, hfn⟩ := hn
    have hnw : n ∈ l2cWindow χ z x := by
      rw [hG1, Finset.mem_filter, Finset.mem_filter, evenCorner_mem] at hnG1
      exact hnG1.1.1.1
    refine ⟨l2cWindow_subset χ z x hnw, ?_⟩
    have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hnw
    have hPdvdn : nPlus χ n ∣ n :=
      ⟨nMinus χ n, eq_nPlus_mul_nMinus χ hsq hn0 (l2cWindow_coprime χ hnw)⟩
    rw [← hfn]; exact (Nat.minFac_dvd _).trans hPdvdn
  -- the ℕ count bound
  have hnat : G1.card ≤ ∑ p ∈ Pset, ((Finset.Ioc x (2 * x)).filter (fun n => p ∣ n)).card := by
    rw [hcard_eq]; exact Finset.sum_le_sum hfiber
  -- push to ℝ and sum the pretense tail
  have hcastR : (G1.card : ℝ)
      ≤ ∑ p ∈ Pset, (((Finset.Ioc x (2 * x)).filter (fun n => p ∣ n)).card : ℝ) := by
    calc (G1.card : ℝ)
        ≤ ((∑ p ∈ Pset, ((Finset.Ioc x (2 * x)).filter (fun n => p ∣ n)).card : ℕ) : ℝ) := by
          exact_mod_cast hnat
      _ = ∑ p ∈ Pset, (((Finset.Ioc x (2 * x)).filter (fun n => p ∣ n)).card : ℝ) := by
          push_cast; rfl
  refine hcastR.trans ?_
  calc ∑ p ∈ Pset, (((Finset.Ioc x (2 * x)).filter (fun n => p ∣ n)).card : ℝ)
      ≤ ∑ p ∈ Pset, ((x : ℝ) / p + 1) := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [hPset, Finset.mem_filter] at hp
        exact window_dvd_count x p hp.2.1.pos
    _ ≤ ∑ p ∈ Pset, (2 * (x : ℝ) / p) := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [hPset, Finset.mem_filter, Finset.mem_range] at hp
        obtain ⟨hplt, hpp, _, _⟩ := hp
        have hpposR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hxp1 : (1 : ℝ) ≤ (x : ℝ) / p := by
          rw [le_div_iff₀ hpposR, one_mul]; exact_mod_cast (by omega : p ≤ x)
        rw [show (2 : ℝ) * (x : ℝ) / p = (x : ℝ) / p + (x : ℝ) / p from by ring]
        linarith
    _ = 2 * (x : ℝ) * ∑ p ∈ Pset, (1 : ℝ) / p := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ 2 * (x : ℝ) * (PretenseSum χ x / Real.log z) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hPset]; exact sum_inv_plusprime_le_pretense χ z x hz1
    _ = (2 * (x : ℝ) / Real.log z) * PretenseSum χ x := by ring
    _ ≤ (2 * (x : ℝ) / Real.log z) * PretenseSum χ (2 * x + 2) := by
        exact mul_le_mul_of_nonneg_left (PretenseSum_mono χ (by omega))
          (div_nonneg (by positivity) hlogz.le)
    _ = 2 * (x : ℝ) * (PretenseSum χ (2 * x + 2) / Real.log z) := by ring

open Classical in
/-- **The Group-2 count.**  The even survivors with `n₊ = 1` are pure `2`-powers of
    `(x,2x]`; there is at most ONE (`2`-powers more than double).  Junk-grade. -/
lemma evenCorner_group2_card_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) :
    ((((evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0)).filter
        (fun n => ¬ (nPlus χ n ≠ 1))).card : ℝ) ≤ 1 := by
  have hz2 : 2 < z := lt_of_lt_of_le (by norm_num) hz100
  have hle1 : (((evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0)).filter
      (fun n => ¬ (nPlus χ n ≠ 1))).card ≤ 1 := by
    rw [Finset.card_le_one]
    -- every element is a `2`-power sitting in `(x,2x]`
    have hpow : ∀ c ∈ (((evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0)).filter
        (fun n => ¬ (nPlus χ n ≠ 1))), ∃ e, c = 2 ^ e ∧ x < c ∧ c ≤ 2 * x := by
      intro c hc
      rw [Finset.mem_filter, Finset.mem_filter, evenCorner_mem] at hc
      obtain ⟨⟨⟨hcw, hev⟩, hne⟩, hP1'⟩ := hc
      have hP1 : nPlus χ c = 1 := not_not.mp hP1'
      obtain ⟨e₁, _, _, _, hM1, _⟩ := evenCorner_survivor χ hsq hz2 hcw hev hne
      have hc0 : c ≠ 0 := l2cWindow_ne_zero χ hcw
      have hceq : c = 2 ^ e₁ := by
        have h := eq_nPlus_mul_nMinus χ hsq hc0 (l2cWindow_coprime χ hcw)
        rw [hP1, one_mul, hM1] at h; exact h
      exact ⟨e₁, hceq, l2cWindow_lt χ hcw, l2cWindow_le χ hcw⟩
    have key : ∀ i j : ℕ, x < 2 ^ i → 2 ^ i ≤ 2 * x → x < 2 ^ j → 2 ^ j ≤ 2 * x →
        (2 : ℕ) ^ i = 2 ^ j := by
      intro i j hai haj hbi hbj
      have hji : j ≤ i := by
        by_contra hlt
        have h2 : (2 : ℕ) ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at h2; omega
      have hij : i ≤ j := by
        by_contra hlt
        have h2 : (2 : ℕ) ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at h2; omega
      rw [le_antisymm hij hji]
    intro a ha b hb
    obtain ⟨i, haeq, haxlt, haxle⟩ := hpow a ha
    obtain ⟨j, hbeq, hbxlt, hbxle⟩ := hpow b hb
    rw [haeq] at haxlt haxle
    rw [hbeq] at hbxlt hbxle
    rw [haeq, hbeq]; exact key i j haxlt haxle hbxlt hbxle
  exact_mod_cast hle1

/-- **The survivor-count bound.**  Combining Groups 1 and 2:
    `#survivors ≤ 2x·(PretenseSum χ (2x+2)/log z) + 1`. -/
lemma evenCorner_survivor_card_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) :
    (((evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0)).card : ℝ)
      ≤ 2 * (x : ℝ) * (PretenseSum χ (2 * x + 2) / Real.log z) + 1 := by
  classical
  have hG1 := evenCorner_group1_card_le χ hsq (z := z) (x := x) hz100
  have hG2 := evenCorner_group2_card_le χ hsq (z := z) (x := x) hz100
  have hnat : ((evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0)).card
      = (((evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0)).filter
          (fun n => nPlus χ n ≠ 1)).card
        + (((evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0)).filter
          (fun n => ¬ (nPlus χ n ≠ 1))).card :=
    (Finset.card_filter_add_card_filter_not (fun n => nPlus χ n ≠ 1)).symm
  have hcast : (((evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0)).card : ℝ)
      = ((((evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0)).filter
            (fun n => nPlus χ n ≠ 1)).card : ℝ)
        + ((((evenCornerSet χ z x).filter (fun n => overshootExact χ n ≠ 0)).filter
            (fun n => ¬ (nPlus χ n ≠ 1))).card : ℝ) := by exact_mod_cast hnat
  rw [hcast]; linarith [hG1, hG2]

/-- **THE RE-FROZEN EVEN-CORNER ROW** (House Amendment 4, catch #248), landed with the
    absolute constant `Cmain = 2`.  Engine-free: crude divisor counting only.

    `evenCornerSum χ z x ≤ 2·(x/L')·e^{5z₀}·PretenseSum χ (2x+2)
        + 2·e^{2z₀}·(x / z^{1/8})·L'^3`.

    Route: `evenCornerSum ≤ #survivors·e^{2z₀}` (the landed Zeno cut); the survivor count
    splits as the `J2`-grade Group 1 (`2x·PS/log z = 2z₀·(x/L')·PS`) plus the single
    `2`-power of Group 2; then `z₀·e^{2z₀} ≤ e^{5z₀}` lifts Group 1 into the `J2` line and
    `1 ≤ (x/z^{1/8})·L'^3` lifts Group 2 into the junk line. -/
theorem EL_evenCorner_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (_hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    evenCornerSum χ z x
      ≤ 2 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2)
        + 2 * Real.exp (2 * z0 z x) * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ)) * (Lwin x) ^ 3 := by
  have hz2 : 2 < z := lt_of_lt_of_le (by norm_num) hz100
  have hz1 : 1 < z := by omega
  have hzR : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz1
  have hlogz : 0 < Real.log z := Real.log_pos hzR
  have hz2R : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show 2 ≤ z by omega)
  have hexp : (0 : ℝ) < Real.exp (2 * z0 z x) := Real.exp_pos _
  have ht0 : 0 ≤ z0 z x := z0_nonneg (by omega)
  have hPSnn : 0 ≤ PretenseSum χ (2 * x + 2) := PretenseSum_nonneg χ _
  -- window log-scale is `≥ 1`
  have hx8 : (8 : ℝ) ≤ (x : ℝ) := by
    have h23 : (2 : ℝ) ^ 3 ≤ (z : ℝ) ^ 3 := by gcongr
    nlinarith [hzx, h23]
  have hL1 : 1 ≤ Lwin x := by
    rw [Lwin, Real.le_log_iff_exp_le (by positivity)]
    nlinarith [hx8, Real.exp_one_lt_d9]
  have hLpos : 0 < Lwin x := by linarith
  -- the two conversion facts
  have hxln : (x : ℝ) / Real.log z = ((x : ℝ) / Lwin x) * z0 z x := by
    rw [z0, div_mul_div_comm, mul_comm (x : ℝ) (Lwin x),
        mul_div_mul_left (x : ℝ) (Real.log z) hLpos.ne']
  have ht_le : z0 z x ≤ Real.exp (3 * z0 z x) := by
    have h := Real.add_one_le_exp (3 * z0 z x); linarith [ht0, h]
  have hee : Real.exp (2 * z0 z x) * z0 z x ≤ Real.exp (5 * z0 z x) := by
    have h1 : Real.exp (2 * z0 z x) * z0 z x
        ≤ Real.exp (2 * z0 z x) * Real.exp (3 * z0 z x) :=
      mul_le_mul_of_nonneg_left ht_le hexp.le
    have h2 : Real.exp (2 * z0 z x) * Real.exp (3 * z0 z x) = Real.exp (5 * z0 z x) := by
      rw [← Real.exp_add]; congr 1; ring
    linarith [h1, h2.le]
  -- Group-1 lift into the `J2` line
  have ha : 2 * (x : ℝ) * PretenseSum χ (2 * x + 2) * Real.exp (2 * z0 z x) / Real.log z
      ≤ 2 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2) := by
    have hlhs : 2 * (x : ℝ) * PretenseSum χ (2 * x + 2) * Real.exp (2 * z0 z x) / Real.log z
        = (2 * PretenseSum χ (2 * x + 2) * ((x : ℝ) / Lwin x))
            * (Real.exp (2 * z0 z x) * z0 z x) := by
      rw [show 2 * (x : ℝ) * PretenseSum χ (2 * x + 2) * Real.exp (2 * z0 z x) / Real.log z
            = 2 * PretenseSum χ (2 * x + 2) * Real.exp (2 * z0 z x) * ((x : ℝ) / Real.log z)
          from by ring, hxln]; ring
    rw [hlhs]
    have hc : 0 ≤ 2 * PretenseSum χ (2 * x + 2) * ((x : ℝ) / Lwin x) :=
      mul_nonneg (mul_nonneg (by norm_num) hPSnn) (div_nonneg (Nat.cast_nonneg x) hLpos.le)
    calc (2 * PretenseSum χ (2 * x + 2) * ((x : ℝ) / Lwin x))
            * (Real.exp (2 * z0 z x) * z0 z x)
        ≤ (2 * PretenseSum χ (2 * x + 2) * ((x : ℝ) / Lwin x)) * Real.exp (5 * z0 z x) :=
          mul_le_mul_of_nonneg_left hee hc
      _ = 2 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2) := by ring
  -- Group-2 lift into the junk line
  have hA1 : (1 : ℝ) ≤ (x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) := by
    have hz18pos : (0 : ℝ) < (z : ℝ) ^ (1 / 8 : ℝ) :=
      Real.rpow_pos_of_pos (by linarith [hz2R]) _
    rw [le_div_iff₀ hz18pos, one_mul]
    have e1 : (z : ℝ) ^ (1 / 8 : ℝ) ≤ (z : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [hz2R]) (by norm_num)
    rw [Real.rpow_one] at e1
    have e2 : (z : ℝ) ≤ (z : ℝ) ^ 3 := le_self_pow₀ (by linarith [hz2R]) (by norm_num)
    linarith [e1, e2, hzx]
  have hL3 : (1 : ℝ) ≤ (Lwin x) ^ 3 := by
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ (Lwin x) ^ 3 := by gcongr
  have hb : Real.exp (2 * z0 z x)
      ≤ 2 * Real.exp (2 * z0 z x) * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ)) * (Lwin x) ^ 3 := by
    have hfac : (1 : ℝ) ≤ 2 * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ)) * (Lwin x) ^ 3 := by
      nlinarith [hA1, hL3, mul_nonneg (by linarith [hA1] :
        (0 : ℝ) ≤ (x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) - 1) (by linarith [hL3] :
        (0 : ℝ) ≤ (Lwin x) ^ 3 - 1)]
    calc Real.exp (2 * z0 z x) = Real.exp (2 * z0 z x) * 1 := (mul_one _).symm
      _ ≤ Real.exp (2 * z0 z x) * (2 * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ)) * (Lwin x) ^ 3) :=
          mul_le_mul_of_nonneg_left hfac hexp.le
      _ = 2 * Real.exp (2 * z0 z x) * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ)) * (Lwin x) ^ 3 := by
          ring
  -- assemble
  have hred := evenCornerSum_le_survivor_card (z := z) (x := x) χ hsq hz2
  have hcard := evenCorner_survivor_card_le χ hsq (z := z) (x := x) hz100
  calc evenCornerSum χ z x
      ≤ (2 * (x : ℝ) * (PretenseSum χ (2 * x + 2) / Real.log z) + 1)
          * Real.exp (2 * z0 z x) :=
        hred.trans (mul_le_mul_of_nonneg_right hcard hexp.le)
    _ = 2 * (x : ℝ) * PretenseSum χ (2 * x + 2) * Real.exp (2 * z0 z x) / Real.log z
          + Real.exp (2 * z0 z x) := by ring
    _ ≤ 2 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2)
          + 2 * Real.exp (2 * z0 z x) * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ)) * (Lwin x) ^ 3 := by
        linarith [ha, hb]

end Salt.HB
