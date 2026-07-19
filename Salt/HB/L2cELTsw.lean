/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cEL

/-!
# HB-L2c family estimates — the T-sw SWAP family budget (`EL_Tsw_bound`)

The **swap family** `T-sw` is the refuter-discovered missing `S₂⁴` block of the
exact-overshoot surgery (freeze §S4).  It collects the window elements `n` whose left
overshoot term `(Λ̃−Λ)(n)·Λ̃(n+2)` has the *swap* shape:

* `n₊ =: P` a prime (single `χ = +1` prime on the `n` side),
* `n₋ =: v` a prime power with `1 < v < z` (the small `χ = −1` block, routed at `z^{1/4}`),
* `(n+2)₋ =: w` a prime power `≥ z` (the large `χ = −1` block on the `n+2` side),
* `(n+2)₊ =: U` a prime — the modulus routed through the `n+2` side, `d₂ := U ≤ (2x+2)/z`.

This is a `J2` (`PretenseSum`) row: the frozen budget is

`EL_Tsw χ z x ≤ Cmain·(x / L')·exp(5·z₀)·PretenseSum χ (2x+2)`.

## What this file lands (COMPLETE — no residuals)

`EL_Tsw_bound` is proven in full, with the explicit absolute constant
`Cmain = 4718592 = 4608·1024`.  The chain:

1. `IsTsw` / `EL_Tsw` — the guarded family predicate and its overshoot sub-sum.  The
   slice carries the freeze §S4 conditions **plus** the house amendments: the catch-#245
   `(c)`-junk guard `¬ TswJunkV` on the `z^{1/4}`-routed block `v` (HOUSE AMENDMENTS
   ruling 1), the freeze's `w`-`Z_z`-roughness clause (making the `Z_z`-sift sound,
   ruling 3), and the catch-#246 parity guard `Odd n` (HOUSE AMENDMENT 2).
2. `tsw_summand_le` / `EL_Tsw_le_weightedCount` — the **sharp double single-block cap**
   (`L2cEL.lamTilde_single_block_le` on both factors) reducing
   `EL_Tsw ≤ e^{2(log2)z₀}·L'·Σ_{n∈Tsw} Λ(n₋)`.
3. `tsw_count` — the joint pair-count fibration of the weighted count, split at the
   `v`-routing threshold `v⁴ ≤ z`:
   * case A (`tsw_sumA_le`): fiber by `(v, U) = (n₋, (n+2)₊)`, modulus pair `(v, U)`,
     `l2c_pair_count_clean` at `Z_z`; `Σ_v Λ(v)/v ≤ 2 log z` (Mertens) ×
     `Σ_U 1/U ≤ PS/log z` (`sum_inv_plusprime_le_pretense` — the `J2` hook);
   * case B (`tsw_sumB_le`): fiber by `U` alone, modulus pair `(1, U)` (`v` rides the
     sifted cofactor via the #245 guard), crude weight `Λ(v) ≤ log z` cancelling against
     the `U`-sum's `1/log z`.
4. `EL_Tsw_bound_of_count` — the `Aexp = 5` budget arithmetic
   `z₀²·e^{2(log2)z₀} ≤ e^{5z₀}` assembling the frozen `J2` conclusion.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — the T-sw family predicate and its overshoot sub-sum -/

/-- **The T-sw (c)-junk guard block** (HOUSE AMENDMENT, catch #245, freeze ruling 1): a
    junk block is `m = p^e` with `p` prime `≤ Z_z`, `e ≥ 2`, and `z^{1/4} < m` — the
    small-base squarefull corner that cannot fit the `J2` row and is owned by the junk row.
    The T-sw family guards its `z^{1/4}`-routed block `v = n₋` with `¬ TswJunkV`.
    (Family-prefixed local predicate per the ruling — no shared def across in-flight files;
    W3 reconciles via iff-lemmas.) -/
def TswJunkV (z v : ℕ) : Prop :=
  ∃ p e, p.Prime ∧ p ≤ Zz z ∧ 2 ≤ e ∧ v = p ^ e ∧ (z : ℝ) ^ ((1 : ℝ) / 4) < (v : ℝ)

/-- **The T-sw (swap) family predicate.**  On a window element `n`: the `χ=+1` part `n₊` is
    a prime `P`, the `χ=−1` block `n₋ =: v` is a prime power with `1 < v < z` (the small
    block), the `χ=−1` block `(n+2)₋ =: w` is a prime power `≥ z`, and `(n+2)₊ =: U` is a
    prime.  These are the freeze §S4 defining conditions of the missing `S₂⁴` block, PLUS:

    * the freeze's own cofactor-roughness clause "`w` Z_z-rough" (every prime of `w` is
      `> Z_z`; for a prime power this excludes exactly the small-base squarefull-`≥z`
      corner, which is owned by `EL_corners_bound`'s squarefull-`≥z` row) — this is what
      makes the `Z_z`-sift sound on the `n+2` cofactor (amendment ruling 3),
    * the catch-#245 inline guard `¬ TswJunkV` on the `z^{1/4}`-routed block `v`
      (amendment ruling 1), and
    * the catch-#246 parity guard `Odd n` (HOUSE AMENDMENT 2: all family slices guard
      `n` odd; the even class — possible when `χ_ℝ(2) = −1` — is the sixth row
      `EL_evenCorner_bound`, owned elsewhere). -/
def IsTsw (χ : DirichletCharacter ℂ q) (z n : ℕ) : Prop :=
  (nPlus χ n).Prime ∧ IsPrimePow (nMinus χ n) ∧ 1 < nMinus χ n ∧ nMinus χ n < z ∧
    IsPrimePow (nMinus χ (n + 2)) ∧ z ≤ nMinus χ (n + 2) ∧ (nPlus χ (n + 2)).Prime ∧
    (∀ p, p.Prime → p ∣ nMinus χ (n + 2) → Zz z < p) ∧ ¬ TswJunkV z (nMinus χ n) ∧ Odd n

open Classical in
/-- **The T-sw family overshoot sub-sum** `Σ_{n∈W, T-sw(n)} (Λ̃−Λ)(n)·Λ̃(n+2)` — the swap
    block of the left overshoot `EL` (`L2cEL.EL`) that this file prices. -/
noncomputable def EL_Tsw (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsTsw χ z n),
    (LamTilde χ n - Λ n) * LamTilde χ (n + 2)

/-! ## §1 — the sharp double single-block cap on a family summand -/

/-- On a window element, `Λ((n+2)₋) ≤ L'` (the `χ=−1` block divides `n+2 ≤ 2x+2`). -/
lemma vonMangoldt_nMinus_add_two_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : Λ (nMinus χ (n + 2)) ≤ Lwin x := by
  have hMdvd : nMinus χ (n + 2) ∣ (n + 2) :=
    ⟨nPlus χ (n + 2), by
      rw [mul_comm]
      exact eq_nPlus_mul_nMinus χ hsq (by omega) (l2cWindow_coprime_add_two χ hn)⟩
  rw [Lwin]
  refine le_trans vonMangoldt_le_log (Real.log_le_log (by exact_mod_cast nMinus_pos χ (n + 2)) ?_)
  have hle : nMinus χ (n + 2) ≤ 2 * x + 2 :=
    le_trans (Nat.le_of_dvd (by omega) hMdvd) (l2cWindow_add_two_le χ hn)
  exact_mod_cast hle

/-- **The sharp double single-block cap.**  On the T-sw family both `Λ̃` factors are capped by
    `L2cEL.lamTilde_single_block_le` (the honest weight keeping the `Λ(n₋)` block), and
    `Λ((n+2)₋) ≤ L'`, so the summand obeys
    `(Λ̃−Λ)(n)·Λ̃(n+2) ≤ e^{(log2)z₀}·e^{(log2)z₀}·L'·Λ(n₋)`. -/
lemma tsw_summand_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ} (hz2 : 2 ≤ z)
    {n : ℕ} (hn : n ∈ l2cWindow χ z x) (htsw : IsTsw χ z n) :
    (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x) * Lwin x
          * Λ (nMinus χ n) := by
  set E := Real.exp (Real.log 2 * z0 z x) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  -- the two sharp caps
  have capn : LamTilde χ n ≤ E * Λ (nMinus χ n) :=
    lamTilde_single_block_le χ hsq z x hz2 (l2cWindow_ne_zero χ hn) (l2cWindow_coprime χ hn)
      (by have := l2cWindow_le χ hn; omega)
      (fun p hp hpd hchi => l2cWindow_rough χ hn hp hpd hchi) htsw.2.1
  have capn2 : LamTilde χ (n + 2) ≤ E * Λ (nMinus χ (n + 2)) :=
    lamTilde_single_block_le χ hsq z x hz2 (by omega) (l2cWindow_coprime_add_two χ hn)
      (l2cWindow_add_two_le χ hn)
      (fun p hp hpd hchi => l2cWindow_rough_add_two χ hn hp hpd hchi) htsw.2.2.2.2.1
  have hLt2_nonneg : 0 ≤ LamTilde χ (n + 2) := lamTilde_nonneg χ hsq (n + 2)
  have hΛv_nonneg : 0 ≤ Λ (nMinus χ n) := vonMangoldt_nonneg
  have hΛw_nonneg : 0 ≤ Λ (nMinus χ (n + 2)) := vonMangoldt_nonneg
  have hEv_nonneg : 0 ≤ E * Λ (nMinus χ n) := mul_nonneg hE0 hΛv_nonneg
  have hΛw_le : Λ (nMinus χ (n + 2)) ≤ Lwin x := vonMangoldt_nMinus_add_two_le χ hsq hn
  calc (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ LamTilde χ n * LamTilde χ (n + 2) :=
        mul_le_mul_of_nonneg_right (by linarith [vonMangoldt_nonneg (n := n)]) hLt2_nonneg
    _ ≤ (E * Λ (nMinus χ n)) * (E * Λ (nMinus χ (n + 2))) :=
        mul_le_mul capn capn2 hLt2_nonneg hEv_nonneg
    _ ≤ (E * Λ (nMinus χ n)) * (E * Lwin x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΛw_le hE0) hEv_nonneg
    _ = E * E * Lwin x * Λ (nMinus χ n) := by ring

/-! ## §2 — the reduction to the weighted `χ=−1`-block count -/

open Classical in
/-- **The T-sw reduction.**  Summing the sharp cap termwise,
    `EL_Tsw ≤ e^{2(log2)z₀}·L'·Σ_{n∈Tsw} Λ(n₋)`. -/
lemma EL_Tsw_le_weightedCount (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz2 : 2 ≤ z) :
    EL_Tsw χ z x
      ≤ Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x) * Lwin x
          * ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsTsw χ z n), Λ (nMinus χ n) := by
  rw [EL_Tsw, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_filter] at hn
  have := tsw_summand_le χ hsq hz2 hn.1 hn.2
  calc (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x) * Lwin x
          * Λ (nMinus χ n) := this
    _ = Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x) * Lwin x
          * Λ (nMinus χ n) := rfl

/-! ## §3 — the exp-arithmetic and the frozen `J2` conclusion from the count residual -/

/-- **The `Aexp = 5` budget arithmetic.**  `z₀²·e^{2(log2)z₀} ≤ e^{5z₀}` (from `z₀² ≤ e^{2z₀}`
    and `2 + 2·log 2 ≤ 5`) — this is what turns the reduction's `e^{2(log2)z₀}` prefactor and
    the count's `z₀²` (hidden in `L'²/(log z)²`) into the frozen `exp(5·z₀)`. -/
lemma z0sq_exp2log2_le {z x : ℕ} (hz2 : 2 ≤ z) :
    z0 z x ^ 2 * (Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x))
      ≤ Real.exp (5 * z0 z x) := by
  have hz0 : 0 ≤ z0 z x := z0_nonneg hz2
  have h1 : z0 z x ≤ Real.exp (z0 z x) := by
    have := Real.add_one_le_exp (z0 z x); linarith
  have h2 : z0 z x ^ 2 ≤ Real.exp (2 * z0 z x) := by
    have hsq : (Real.exp (z0 z x)) ^ 2 = Real.exp (2 * z0 z x) := by
      rw [sq, ← Real.exp_add, two_mul]
    rw [← hsq]; exact pow_le_pow_left₀ hz0 h1 2
  have hEE : Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x)
      = Real.exp (2 * Real.log 2 * z0 z x) := by rw [← Real.exp_add]; congr 1; ring
  rw [hEE]
  calc z0 z x ^ 2 * Real.exp (2 * Real.log 2 * z0 z x)
      ≤ Real.exp (2 * z0 z x) * Real.exp (2 * Real.log 2 * z0 z x) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (2 * z0 z x + 2 * Real.log 2 * z0 z x) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (5 * z0 z x) := by
        apply Real.exp_le_exp.mpr
        have hlog2 : Real.log 2 ≤ 1 := le_of_lt (by have := Real.log_two_lt_d9; linarith)
        nlinarith [hz0, hlog2]

/-- `PretenseSum χ N ≥ 0` (each term `log p / p ≥ 0`). -/
lemma pretenseSum_nonneg (χ : DirichletCharacter ℂ q) (N : ℕ) : 0 ≤ PretenseSum χ N := by
  rw [PretenseSum]
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)) (Nat.cast_nonneg p)

open Classical in
/-- **`EL_Tsw_bound` (the frozen `J2` conclusion), conditional on the count residual.**
    From the reduction `EL_Tsw ≤ e^{2(log2)z₀}·L'·Σ_{n∈Tsw} Λ(n₋)` and the `S3` count-engine
    output `hcount : Σ_{n∈Tsw} Λ(n₋) ≤ Ccount·x·PS/(log z)²`, the T-sw budget obeys the frozen
    swap-family shape

    `EL_Tsw χ z x ≤ Ccount·(x / L')·exp(5·z₀)·PretenseSum χ (2x+2)`

    with `Cmain := Ccount` an absolute constant (the `hcount` residual constant).  The residual
    `hcount` is the joint pair-count fibration (fiber by `(n₋, (n+2)₊)`, count via
    `l2c_pair_count_clean`, sum by Mertens/`sum_inv_plusprime_le_pretense`). -/
theorem EL_Tsw_bound_of_count (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (_hz8 : (Lwin x) ^ 8 ≤ z) (_hzx : (z : ℝ) ^ 3 ≤ x)
    {Ccount : ℝ} (hCcount : 0 ≤ Ccount)
    (hcount : ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsTsw χ z n), Λ (nMinus χ n)
        ≤ Ccount * x * PretenseSum χ (2 * x + 2) / (Real.log z) ^ 2) :
    EL_Tsw χ z x
      ≤ Ccount * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hlogz_pos : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show (1 : ℕ) < z by omega))
  have hLwin_pos : 0 < Lwin x := by
    rw [Lwin]; exact Real.log_pos (by have : (0 : ℝ) ≤ x := Nat.cast_nonneg x; linarith)
  have hPS_nonneg : 0 ≤ PretenseSum χ (2 * x + 2) := pretenseSum_nonneg χ _
  refine le_trans (EL_Tsw_le_weightedCount χ hsq hz2) ?_
  -- `E*E*L'*S ≤ Ccount*(x/L')*exp(5z0)*PS`, `S := Σ Λ(n₋)`
  have hEEL_nonneg :
      0 ≤ Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x) * Lwin x := by
    positivity
  refine le_trans (mul_le_mul_of_nonneg_left hcount hEEL_nonneg) ?_
  -- algebra: `L'/(log z)² = z0²/L'`, then apply `z0sq_exp2log2_le`
  have halg :
      Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x) * Lwin x
          * (Ccount * x * PretenseSum χ (2 * x + 2) / (Real.log z) ^ 2)
        = (Ccount * x * PretenseSum χ (2 * x + 2) / Lwin x)
            * (z0 z x ^ 2
                * (Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x))) := by
    rw [z0]; field_simp
  rw [halg]
  have hcnonneg : 0 ≤ Ccount * (x : ℝ) * PretenseSum χ (2 * x + 2) / Lwin x :=
    div_nonneg (mul_nonneg (mul_nonneg hCcount (Nat.cast_nonneg x)) hPS_nonneg) hLwin_pos.le
  calc (Ccount * (x : ℝ) * PretenseSum χ (2 * x + 2) / Lwin x)
          * (z0 z x ^ 2
              * (Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x)))
      ≤ (Ccount * (x : ℝ) * PretenseSum χ (2 * x + 2) / Lwin x) * Real.exp (5 * z0 z x) :=
        mul_le_mul_of_nonneg_left (z0sq_exp2log2_le hz2) hcnonneg
    _ = Ccount * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by ring

/-! ## §4 — `Z_z` arithmetic (the sift-floor toolbox)

The count-engine fibration sifts at `Z_z = ⌊z^{1/16}⌋` (amendment ruling 3).  All the
legality and conversion arithmetic reduces to two `ℕ`-clean facts (`Zz^16 ≤ z`,
`log z ≤ 32·log Zz`) plus `log t ≤ t`. -/

/-- `Zz z ^ 16 ≤ z` (the floor undoes the 16th root). -/
lemma Zz_pow16_le {z : ℕ} : Zz z ^ 16 ≤ z := by
  have h0 : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
  have hfl : (Zz z : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 16) := Nat.floor_le (Real.rpow_nonneg h0 _)
  have hcollapse : ((z : ℝ) ^ ((1 : ℝ) / 16)) ^ (16 : ℕ) = (z : ℝ) := by
    rw [← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 16)) 16, ← Real.rpow_mul h0]
    norm_num
  have : ((Zz z : ℝ)) ^ (16 : ℕ) ≤ (z : ℝ) := by
    calc ((Zz z : ℝ)) ^ (16 : ℕ) ≤ ((z : ℝ) ^ ((1 : ℝ) / 16)) ^ (16 : ℕ) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hfl 16
      _ = (z : ℝ) := hcollapse
  exact_mod_cast this

/-- `Zz z ≤ z`. -/
lemma Zz_le {z : ℕ} : Zz z ≤ z :=
  le_trans (Nat.le_self_pow (by norm_num) _) Zz_pow16_le

/-- `Zz z ^ 10 ≤ z` (the case-B legality power). -/
lemma Zz_pow10_le {z : ℕ} (hz1 : 1 ≤ z) : Zz z ^ 10 ≤ z := by
  have h : (Zz z ^ 10) ^ 8 ≤ z ^ 8 := by
    calc (Zz z ^ 10) ^ 8 = (Zz z ^ 16) ^ 5 := by ring
      _ ≤ z ^ 5 := Nat.pow_le_pow_left Zz_pow16_le 5
      _ ≤ z ^ 8 := Nat.pow_le_pow_right hz1 (by norm_num)
  exact (Nat.pow_le_pow_iff_left (by norm_num : (8 : ℕ) ≠ 0)).mp h

/-- **The log-scale conversion.**  `log z ≤ 32·log Zz` (so `(log z)² ≤ 1024·(log Zz)²`). -/
lemma log_le_32_mul_log_Zz {z : ℕ} (hz100 : 100 ^ 16 ≤ z) :
    Real.log z ≤ 32 * Real.log (Zz z) := by
  have hZ100 : 100 ≤ Zz z := Zz_ge_100 hz100
  have hz0 : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
  have hzpos : (0 : ℝ) < (z : ℝ) := by
    have : (0 : ℕ) < z := by positivity
    exact_mod_cast this
  have hfl : (z : ℝ) ^ ((1 : ℝ) / 16) < (Zz z : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2Z : ((Zz z : ℝ)) + 1 ≤ 2 * (Zz z : ℝ) := by
    have : (1 : ℝ) ≤ (Zz z : ℝ) := by exact_mod_cast le_trans (by norm_num) hZ100
    linarith
  have hcollapse : ((z : ℝ) ^ ((1 : ℝ) / 16)) ^ (16 : ℕ) = (z : ℝ) := by
    rw [← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 16)) 16, ← Real.rpow_mul hz0]
    norm_num
  have hzlt : (z : ℝ) < (2 * (Zz z : ℝ)) ^ (16 : ℕ) := by
    calc (z : ℝ) = ((z : ℝ) ^ ((1 : ℝ) / 16)) ^ (16 : ℕ) := hcollapse.symm
      _ < (2 * (Zz z : ℝ)) ^ (16 : ℕ) :=
          pow_lt_pow_left₀ (lt_of_lt_of_le hfl h2Z) (Real.rpow_nonneg hz0 _) (by norm_num)
  have hZpos : (0 : ℝ) < (Zz z : ℝ) := by
    have : (0 : ℕ) < Zz z := by omega
    exact_mod_cast this
  have hlog2Z : Real.log 2 ≤ Real.log (Zz z) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ Zz z))
  calc Real.log z ≤ Real.log ((2 * (Zz z : ℝ)) ^ (16 : ℕ)) :=
        Real.log_le_log hzpos hzlt.le
    _ = 16 * (Real.log 2 + Real.log (Zz z)) := by
        rw [Real.log_pow, Real.log_mul (by norm_num) hZpos.ne']; norm_num
    _ ≤ 16 * (Real.log (Zz z) + Real.log (Zz z)) := by
        have := hlog2Z; linarith
    _ = 32 * Real.log (Zz z) := by ring

/-- `0 < log Zz` (from `Zz ≥ 100`). -/
lemma log_Zz_pos {z : ℕ} (hz100 : 100 ^ 16 ≤ z) : 0 < Real.log (Zz z) :=
  Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by norm_num) (Zz_ge_100 hz100))

/-! ## §5 — primorial coprimality and totient-ratio helpers -/

/-- **The rough-sift discharge.**  If every prime of `m` exceeds `Z`, then `m` is coprime
    to `primorial Z` — the membership key for the `l2c_pair_count_clean` filter. -/
lemma tsw_coprime_primorial {Z m : ℕ} (h : ∀ p, p.Prime → p ∣ m → Z < p) :
    Nat.Coprime (primorial Z) m := by
  rw [primorial, Nat.coprime_prod_left_iff]
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  exact (hp.2.coprime_iff_not_dvd).mpr fun hdvd => absurd (h p hp.2 hdvd) (by omega)

/-- Prime-power totient ratio: `m ≤ 2·φ(m)` for `m` a prime power. -/
lemma pp_le_two_mul_totient {m : ℕ} (hm : IsPrimePow m) : m ≤ 2 * m.totient := by
  obtain ⟨p, e, hp, he, rfl⟩ := hm
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  rw [Nat.totient_prime_pow hp' he]
  calc p ^ e = p ^ (e - 1) * p := by rw [← pow_succ]; congr 1; omega
    _ ≤ p ^ (e - 1) * (2 * (p - 1)) :=
        Nat.mul_le_mul_left _ (by have := hp'.two_le; omega)
    _ = 2 * (p ^ (e - 1) * (p - 1)) := by ring

/-- The joint totient-ratio bound: `v·U ≤ 4·φ(v·U)` for coprime prime powers. -/
lemma tsw_mul_le_four_totient {v U : ℕ} (hv : IsPrimePow v) (hU : IsPrimePow U)
    (hcop : Nat.Coprime v U) : v * U ≤ 4 * (v * U).totient := by
  rw [Nat.totient_mul hcop]
  calc v * U ≤ (2 * v.totient) * (2 * U.totient) :=
        Nat.mul_le_mul (pp_le_two_mul_totient hv) (pp_le_two_mul_totient hU)
    _ = 4 * (v.totient * U.totient) := by ring

/-- The squared ratio form consumed by the count cleanup: `((v·U)/φ(v·U))² ≤ 16`. -/
lemma tsw_ratio_sq_le {v U : ℕ} (hv : IsPrimePow v) (hU : IsPrimePow U)
    (hcop : Nat.Coprime v U) :
    ((v * U : ℝ) / ((v * U : ℕ).totient : ℝ)) ^ 2 ≤ 16 := by
  have hvU : 0 < v * U := Nat.mul_pos hv.pos hU.pos
  have hφ : (0 : ℝ) < ((v * U : ℕ).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hvU
  have hratio : (v * U : ℝ) / ((v * U : ℕ).totient : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hφ]
    calc (v * U : ℝ) = ((v * U : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((4 * (v * U).totient : ℕ) : ℝ) := by
          exact_mod_cast tsw_mul_le_four_totient hv hU hcop
      _ = 4 * ((v * U : ℕ).totient : ℝ) := by push_cast; ring
  calc ((v * U : ℝ) / ((v * U : ℕ).totient : ℝ)) ^ 2 ≤ 4 ^ 2 :=
        pow_le_pow_left₀ (by positivity) hratio 2
    _ = 16 := by norm_num

/-! ## §6 — slice facts: the structural consequences of `n ∈ W ∧ IsTsw`

Notation throughout: `P := n₊`, `v := n₋`, `U := (n+2)₊`, `w := (n+2)₋`. -/

/-- `z³ ≤ x` in `ℕ` (cast of the master hypothesis). -/
lemma tsw_z3_le {z x : ℕ} (hzx : (z : ℝ) ^ 3 ≤ x) : z ^ 3 ≤ x := by
  have h : ((z ^ 3 : ℕ) : ℝ) ≤ (x : ℝ) := by push_cast; exact hzx
  exact_mod_cast h

/-- The `n`-side factorization `n = P·v`. -/
lemma tsw_n_eq (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : n = nPlus χ n * nMinus χ n :=
  eq_nPlus_mul_nMinus χ hsq (l2cWindow_ne_zero χ hn) (l2cWindow_coprime χ hn)

/-- The `n+2`-side factorization `n+2 = U·w`. -/
lemma tsw_n2_eq (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : n + 2 = nPlus χ (n + 2) * nMinus χ (n + 2) :=
  eq_nPlus_mul_nMinus χ hsq (by omega) (l2cWindow_coprime_add_two χ hn)

/-- **The `P`-cofactor size**: `z² < P` (from `x < n = P·v`, `v < z`, `z³ ≤ x`). -/
lemma tsw_P_gt (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hzx : (z : ℝ) ^ 3 ≤ x) (hn : n ∈ l2cWindow χ z x) (ht : IsTsw χ z n) :
    z ^ 2 < nPlus χ n := by
  have hPpos : 0 < nPlus χ n := nPlus_pos χ n
  have h1 : z ^ 2 * z ≤ x := by
    calc z ^ 2 * z = z ^ 3 := by ring
      _ ≤ x := tsw_z3_le hzx
  have h2 : x < nPlus χ n * z := by
    calc x < n := l2cWindow_lt χ hn
      _ = nPlus χ n * nMinus χ n := tsw_n_eq χ hsq hn
      _ ≤ nPlus χ n * z := Nat.mul_le_mul_left _ (le_of_lt ht.2.2.2.1)
  exact lt_of_mul_lt_mul_right (lt_of_le_of_lt h1 h2) (Nat.zero_le z)

/-- `U ∣ n+2`. -/
lemma tsw_U_dvd (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : nPlus χ (n + 2) ∣ n + 2 :=
  ⟨nMinus χ (n + 2), tsw_n2_eq χ hsq hn⟩

/-- `χ(U) = 1` (the `n+2`-side `χ=+1` prime — the `PretenseSum` hook). -/
lemma tsw_chiU (χ : DirichletCharacter ℂ q) {z n : ℕ} (ht : IsTsw χ z n) :
    chiRe χ (nPlus χ (n + 2)) = 1 := by
  have hUp : (nPlus χ (n + 2)).Prime := ht.2.2.2.2.2.2.1
  have hmem : nPlus χ (n + 2) ∈ (nPlus χ (n + 2)).primeFactors := by
    rw [hUp.primeFactors]; exact Finset.mem_singleton_self _
  exact nPlus_sign hmem

/-- **The modulus roughness**: `z ≤ U` (window roughness at the `χ=+1` prime `U`). -/
lemma tsw_U_ge (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (ht : IsTsw χ z n) : z ≤ nPlus χ (n + 2) :=
  l2cWindow_rough_add_two χ hn ht.2.2.2.2.2.2.1 (tsw_U_dvd χ hsq hn)
    (by rw [tsw_chiU χ ht]; norm_num)

/-- **The modulus law** `U·z ≤ 2x+2` (the swap `d₂ := U ≤ (2x+2)/z`, freeze §S4 T-sw). -/
lemma tsw_Uz_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (ht : IsTsw χ z n) :
    nPlus χ (n + 2) * z ≤ 2 * x + 2 := by
  calc nPlus χ (n + 2) * z ≤ nPlus χ (n + 2) * nMinus χ (n + 2) :=
        Nat.mul_le_mul_left _ ht.2.2.2.2.2.1
    _ = n + 2 := (tsw_n2_eq χ hsq hn).symm
    _ ≤ 2 * x + 2 := l2cWindow_add_two_le χ hn

/-- **`v` is odd** (an even `v` would force `2 ∣ w` against the `Z_z`-roughness of `w`,
    or `U = 2` against `z ≤ U`). -/
lemma tsw_odd_v (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hn : n ∈ l2cWindow χ z x) (ht : IsTsw χ z n) :
    Odd (nMinus χ n) := by
  rcases Nat.even_or_odd (nMinus χ n) with he | ho
  · exfalso
    have hvn : nMinus χ n ∣ n := ⟨nPlus χ n, by rw [mul_comm]; exact tsw_n_eq χ hsq hn⟩
    have h2n2 : 2 ∣ n + 2 := dvd_add (he.two_dvd.trans hvn) dvd_rfl
    rw [tsw_n2_eq χ hsq hn] at h2n2
    rcases (Nat.prime_two.dvd_mul).mp h2n2 with hU | hw
    · have : (2 : ℕ) = nPlus χ (n + 2) :=
        (Nat.prime_dvd_prime_iff_eq Nat.prime_two ht.2.2.2.2.2.2.1).mp hU
      have := tsw_U_ge χ hsq hn ht
      omega
    · have hZz2 : Zz z < 2 := ht.2.2.2.2.2.2.2.1 2 Nat.prime_two hw
      have := Zz_ge_100 hz100
      omega
  · exact ho

/-- `v` and `U` are coprime (`v < z ≤ U`, `U` prime). -/
lemma tsw_cop_vU (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (ht : IsTsw χ z n) :
    Nat.Coprime (nMinus χ n) (nPlus χ (n + 2)) := by
  have hUge := tsw_U_ge χ hsq hn ht
  have hv1 := ht.2.2.1
  have hvz := ht.2.2.2.1
  refine ((ht.2.2.2.2.2.2.1.coprime_iff_not_dvd).mpr fun hdvd => ?_).symm
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- The `n`-side cofactor identity `n / v = P`. -/
lemma tsw_div_v (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (ht : IsTsw χ z n) :
    n / nMinus χ n = nPlus χ n :=
  Nat.div_eq_of_eq_mul_left (by have := ht.2.2.1; omega) (tsw_n_eq χ hsq hn)

/-- The `n+2`-side cofactor identity `(n+2) / U = w`. -/
lemma tsw_div_U (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (ht : IsTsw χ z n) :
    (n + 2) / nPlus χ (n + 2) = nMinus χ (n + 2) :=
  Nat.div_eq_of_eq_mul_right ht.2.2.2.2.2.2.1.pos (tsw_n2_eq χ hsq hn)

/-- The `P`-cofactor is `Z_z`-rough (it is a prime `> z² ≥ Z_z`). -/
lemma tsw_P_rough (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hzx : (z : ℝ) ^ 3 ≤ x) (hn : n ∈ l2cWindow χ z x) (ht : IsTsw χ z n) :
    ∀ p, p.Prime → p ∣ nPlus χ n → Zz z < p := by
  intro p hp hpd
  have hpP : p = nPlus χ n := (Nat.prime_dvd_prime_iff_eq hp ht.1).mp hpd
  have h1 : Zz z ≤ z := Zz_le
  have h2 : z ≤ z ^ 2 := Nat.le_self_pow (by norm_num) z
  have h3 := tsw_P_gt χ hsq hzx hn ht
  omega

/-- **The case-A sift** `(primorial Z_z, P·w) = 1` — both cofactors are `Z_z`-rough. -/
lemma tsw_siftA (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hzx : (z : ℝ) ^ 3 ≤ x) (hn : n ∈ l2cWindow χ z x) (ht : IsTsw χ z n) :
    Nat.Coprime (primorial (Zz z)) (nPlus χ n * nMinus χ (n + 2)) :=
  Nat.Coprime.mul_right (tsw_coprime_primorial (tsw_P_rough χ hsq hzx hn ht))
    (tsw_coprime_primorial ht.2.2.2.2.2.2.2.1)

/-- **The guard discharge (cofactor route).**  When `z < v⁴` (case B), the `#245` guard
    forces every prime of `v` above `Z_z` (squarefull small-base is excluded by the guard;
    a prime `v > z^{1/4}` clears `Z_z ≤ z^{1/4}` automatically). -/
lemma tsw_v_rough (χ : DirichletCharacter ℂ q) {z n : ℕ} (ht : IsTsw χ z n)
    (hB : z < (nMinus χ n) ^ 4) :
    ∀ p, p.Prime → p ∣ nMinus χ n → Zz z < p := by
  obtain ⟨p₀, e, hp₀, he, hveq⟩ := ht.2.1
  have hp₀' : p₀.Prime := Nat.prime_iff.mpr hp₀
  suffices hZp : Zz z < p₀ by
    intro p hp hpd
    rw [← hveq] at hpd
    have : p = p₀ := (Nat.prime_dvd_prime_iff_eq hp hp₀').mp (hp.dvd_of_dvd_pow hpd)
    omega
  by_cases he2 : 2 ≤ e
  · refine (Nat.lt_or_ge (Zz z) p₀).resolve_right fun hle => ?_
    refine ht.2.2.2.2.2.2.2.2.1 ⟨p₀, e, hp₀', hle, he2, hveq.symm, ?_⟩
    have hzv : (z : ℝ) < ((nMinus χ n : ℝ)) ^ (4 : ℕ) := by exact_mod_cast hB
    have hcol : (((nMinus χ n : ℝ)) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = (nMinus χ n : ℝ) := by
      rw [← Real.rpow_natCast ((nMinus χ n : ℝ)) 4, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    calc (z : ℝ) ^ ((1 : ℝ) / 4)
        < (((nMinus χ n : ℝ)) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) :=
          Real.rpow_lt_rpow (Nat.cast_nonneg z) hzv (by norm_num)
      _ = (nMinus χ n : ℝ) := hcol
  · have he1 : e = 1 := by omega
    have hvp : nMinus χ n = p₀ := by rw [← hveq, he1, pow_one]
    refine (Nat.lt_or_ge (Zz z) p₀).resolve_right fun hle => ?_
    have hv4 : nMinus χ n ^ 4 ≤ Zz z ^ 4 := by
      rw [hvp]; exact Nat.pow_le_pow_left hle 4
    have h416 : Zz z ^ 4 ≤ Zz z ^ 16 :=
      Nat.pow_le_pow_right (by have := hp₀'.two_le; omega) (by norm_num)
    have h16 := Zz_pow16_le (z := z)
    omega

/-- **The case-B sift** `(primorial Z_z, n·w) = 1` — with `d₁ = 1` the whole of `n = P·v`
    is a cofactor; `P` is rough by size, `v` by the guard. -/
lemma tsw_siftB (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hzx : (z : ℝ) ^ 3 ≤ x) (hn : n ∈ l2cWindow χ z x) (ht : IsTsw χ z n)
    (hB : z < (nMinus χ n) ^ 4) :
    Nat.Coprime (primorial (Zz z)) (n * nMinus χ (n + 2)) := by
  refine Nat.Coprime.mul_right ?_ (tsw_coprime_primorial ht.2.2.2.2.2.2.2.1)
  refine tsw_coprime_primorial fun p hp hpd => ?_
  rw [tsw_n_eq χ hsq hn] at hpd
  rcases (hp.dvd_mul).mp hpd with hpP | hpv
  · exact tsw_P_rough χ hsq hzx hn ht p hp hpP
  · exact tsw_v_rough χ ht hB p hp hpv

/-! ## §7 — the fiber index sets, legality, and the per-fiber counts

Case A (`v⁴ ≤ z`): fiber by `(v, U)`, modulus pair `(d₁, d₂) = (v, U)`.
Case B (`z < v⁴`): fiber by `U` alone, modulus pair `(1, U)` (`v` rides the cofactor). -/

open Classical in
/-- The case-A `v`-index: odd prime powers `1 < v ≤ z` with `v⁴ ≤ z`. -/
noncomputable def TswVIndex (z : ℕ) : Finset ℕ :=
  (Finset.Ioc 1 z).filter (fun v => IsPrimePow v ∧ Odd v ∧ v ^ 4 ≤ z)

open Classical in
/-- The `U`-index: `χ=+1` primes `z ≤ U` obeying the swap modulus law `U·z ≤ 2x+2`. -/
noncomputable def TswUIndex (χ : DirichletCharacter ℂ q) (z x : ℕ) : Finset ℕ :=
  (Finset.range (2 * x + 2 + 1)).filter
    (fun U => U.Prime ∧ chiRe χ U = 1 ∧ z ≤ U ∧ U * z ≤ 2 * x + 2)

/-- `(log Z_z)² ≤ Z_z²` (crude but sufficient: the `z^{1/8}`-slack absorbs it). -/
lemma tsw_log_sq_le {z : ℕ} (hz100 : 100 ^ 16 ≤ z) :
    Real.log (Zz z) ^ 2 ≤ ((Zz z : ℕ) : ℝ) ^ 2 := by
  have h1 : (1 : ℝ) ≤ (Zz z : ℝ) := by
    exact_mod_cast le_trans (by norm_num) (Zz_ge_100 hz100)
  have hnn : 0 ≤ Real.log (Zz z) := Real.log_nonneg h1
  have hle : Real.log (Zz z) ≤ (Zz z : ℝ) :=
    le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
  exact pow_le_pow_left₀ hnn hle 2

/-- **Case-A legality** at `Z_z`: `v·U·Z_z⁸·(log Z_z)² ≤ 32x` (from `v⁴ ≤ z`, `U·z ≤ 2x+2`,
    `Z_z^16 ≤ z` — the amendment's "legality at `Z_z` holds comfortably"). -/
lemma tsw_legalityA {z x v U : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (hv4 : v ^ 4 ≤ z) (hUz : U * z ≤ 2 * x + 2) :
    ((v : ℝ) * (U : ℝ)) * ((Zz z : ℕ) : ℝ) ^ 8 * Real.log (Zz z) ^ 2 ≤ 32 * (x : ℝ) := by
  have hz1 : 1 ≤ z := le_trans (Nat.one_le_pow _ _ (by norm_num)) hz100
  -- ℕ core: v·Zz¹⁰ ≤ z, hence v·U·Zz¹⁰ ≤ U·z ≤ 2x+2
  have hkey : v * Zz z ^ 10 ≤ z := by
    have h8 : (v * Zz z ^ 10) ^ 8 ≤ z ^ 8 := by
      calc (v * Zz z ^ 10) ^ 8 = (v ^ 4) ^ 2 * (Zz z ^ 16) ^ 5 := by ring
        _ ≤ z ^ 2 * z ^ 5 :=
            Nat.mul_le_mul (Nat.pow_le_pow_left hv4 2) (Nat.pow_le_pow_left Zz_pow16_le 5)
        _ = z ^ 7 := by ring
        _ ≤ z ^ 8 := Nat.pow_le_pow_right hz1 (by norm_num)
    exact (Nat.pow_le_pow_iff_left (by norm_num : (8 : ℕ) ≠ 0)).mp h8
  have hcore : v * U * Zz z ^ 10 ≤ 2 * x + 2 := by
    calc v * U * Zz z ^ 10 = U * (v * Zz z ^ 10) := by ring
      _ ≤ U * z := Nat.mul_le_mul_left _ hkey
      _ ≤ 2 * x + 2 := hUz
  have hx1 : 1 ≤ x := by
    have h3 : z ^ 3 ≤ x := tsw_z3_le hzx
    have : 1 ≤ z ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  calc ((v : ℝ) * (U : ℝ)) * ((Zz z : ℕ) : ℝ) ^ 8 * Real.log (Zz z) ^ 2
      ≤ ((v : ℝ) * (U : ℝ)) * ((Zz z : ℕ) : ℝ) ^ 8 * ((Zz z : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (tsw_log_sq_le hz100) (by positivity)
    _ = ((v * U * Zz z ^ 10 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 * x + 2 : ℕ) : ℝ) := by exact_mod_cast hcore
    _ ≤ 32 * (x : ℝ) := by
        have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
        push_cast; linarith

/-- **Case-B legality** at `Z_z`: `1·U·Z_z⁸·(log Z_z)² ≤ 32x`. -/
lemma tsw_legalityB {z x U : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (hUz : U * z ≤ 2 * x + 2) :
    (((1 : ℕ) : ℝ) * (U : ℝ)) * ((Zz z : ℕ) : ℝ) ^ 8 * Real.log (Zz z) ^ 2
      ≤ 32 * (x : ℝ) := by
  have hz1 : 1 ≤ z := le_trans (Nat.one_le_pow _ _ (by norm_num)) hz100
  have hcore : U * Zz z ^ 10 ≤ 2 * x + 2 := by
    calc U * Zz z ^ 10 ≤ U * z := Nat.mul_le_mul_left _ (Zz_pow10_le hz1)
      _ ≤ 2 * x + 2 := hUz
  have hx1 : 1 ≤ x := by
    have h3 : z ^ 3 ≤ x := tsw_z3_le hzx
    have : 1 ≤ z ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  calc (((1 : ℕ) : ℝ) * (U : ℝ)) * ((Zz z : ℕ) : ℝ) ^ 8 * Real.log (Zz z) ^ 2
      ≤ (((1 : ℕ) : ℝ) * (U : ℝ)) * ((Zz z : ℕ) : ℝ) ^ 8 * ((Zz z : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (tsw_log_sq_le hz100) (by positivity)
    _ = ((U * Zz z ^ 10 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 * x + 2 : ℕ) : ℝ) := by exact_mod_cast hcore
    _ ≤ 32 * (x : ℝ) := by
        have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
        push_cast; linarith

open Classical in
/-- **The case-A fiber count.**  For `(v, U)` in the index sets, the sifted `(v,U)`-pair
    window holds at most `2048·x/(v·U·(log Z_z)²)` elements
    (`l2c_pair_count_clean` at `(d₁,d₂) = (v,U)`, `Z = Z_z`; `φ`-ratio `≤ 16`). -/
lemma tsw_countA (χ : DirichletCharacter ℂ q) {z x : ℕ} (hz100 : 100 ^ 16 ≤ z)
    (hzx : (z : ℝ) ^ 3 ≤ x) {v U : ℕ} (hv : v ∈ TswVIndex z) (hU : U ∈ TswUIndex χ z x) :
    (((baseSet x v U).filter
        (fun n => Nat.Coprime (primorial (Zz z)) ((n / v) * ((n + 2) / U)))).card : ℝ)
      ≤ 2048 * (x : ℝ) / ((v : ℝ) * (U : ℝ) * Real.log (Zz z) ^ 2) := by
  simp only [TswVIndex, TswUIndex, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hv hU
  obtain ⟨⟨hv1, hvz⟩, hppv, hoddv, hv4⟩ := hv
  obtain ⟨_, hUp, _, hzU, hUz⟩ := hU
  have hZ := Zz_ge_100 hz100
  have hd₁ : 0 < v := by omega
  have hoU : Odd U := hUp.odd_of_ne_two (by
    have h3 : (3 : ℕ) ≤ z := le_trans (by norm_num) hz100
    omega)
  have hvltU : v < U := by
    rcases Nat.lt_or_ge v U with h | h
    · exact h
    · exfalso
      have hv4v : v ^ 4 ≤ v := le_trans hv4 (le_trans hzU h)
      have h2 : v * v ≤ v := by
        calc v * v = v ^ 2 := (pow_two v).symm
          _ ≤ v ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
          _ ≤ v := hv4v
      have := Nat.le_of_mul_le_mul_left (by omega : v * v ≤ v * 1) (by omega : 0 < v)
      omega
  have hcop : Nat.Coprime v U :=
    ((hUp.coprime_iff_not_dvd).mpr fun hdvd => by
      have := Nat.le_of_dvd hd₁ hdvd
      omega).symm
  have hcount := l2c_pair_count_clean (x := x) (d₁ := v) (d₂ := U) (Z := Zz z) hZ hd₁
    hUp.pos hoddv hoU hcop (tsw_legalityA hz100 hzx hv4 hUz)
  refine le_trans hcount ?_
  have hr := tsw_ratio_sq_le hppv hUp.isPrimePow hcop
  have hL2 : (0 : ℝ) < Real.log (Zz z) ^ 2 := by
    have := log_Zz_pos hz100
    positivity
  have hstep : 128 * ((v * U : ℝ) / ((v * U : ℕ).totient : ℝ)) ^ 2 * ((x : ℝ) / (v * U))
      ≤ 2048 * ((x : ℝ) / (v * U)) := by
    have hxvU : (0 : ℝ) ≤ (x : ℝ) / (v * U) := by positivity
    calc 128 * ((v * U : ℝ) / ((v * U : ℕ).totient : ℝ)) ^ 2 * ((x : ℝ) / (v * U))
        ≤ 128 * 16 * ((x : ℝ) / (v * U)) := by
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 128)) hxvU
          linarith
      _ = 2048 * ((x : ℝ) / (v * U)) := by norm_num
  calc 128 * ((v * U : ℝ) / ((v * U : ℕ).totient : ℝ)) ^ 2 * ((x : ℝ) / (v * U))
        / Real.log (Zz z) ^ 2
      ≤ 2048 * ((x : ℝ) / (v * U)) / Real.log (Zz z) ^ 2 :=
        div_le_div_of_nonneg_right hstep hL2.le
    _ = 2048 * (x : ℝ) / ((v : ℝ) * (U : ℝ) * Real.log (Zz z) ^ 2) := by
        have hv0 : (v : ℝ) ≠ 0 := by positivity
        have hU0 : (U : ℝ) ≠ 0 := by
          have := hUp.pos
          positivity
        field_simp

open Classical in
/-- **The case-B fiber count.**  For `U` in the index set, the sifted `(1,U)`-pair window
    holds at most `512·x/(U·(log Z_z)²)` elements. -/
lemma tsw_countB (χ : DirichletCharacter ℂ q) {z x : ℕ} (hz100 : 100 ^ 16 ≤ z)
    (hzx : (z : ℝ) ^ 3 ≤ x) {U : ℕ} (hU : U ∈ TswUIndex χ z x) :
    (((baseSet x 1 U).filter
        (fun n => Nat.Coprime (primorial (Zz z)) ((n / 1) * ((n + 2) / U)))).card : ℝ)
      ≤ 512 * (x : ℝ) / ((U : ℝ) * Real.log (Zz z) ^ 2) := by
  simp only [TswUIndex, Finset.mem_filter, Finset.mem_range] at hU
  obtain ⟨_, hUp, _, hzU, hUz⟩ := hU
  have hZ := Zz_ge_100 hz100
  have hoU : Odd U := hUp.odd_of_ne_two (by
    have h3 : (3 : ℕ) ≤ z := le_trans (by norm_num) hz100
    omega)
  have hcop : Nat.Coprime 1 U := Nat.coprime_one_left U
  have hcount := l2c_pair_count_clean (x := x) (d₁ := 1) (d₂ := U) (Z := Zz z) hZ
    (by norm_num) hUp.pos odd_one hoU hcop (tsw_legalityB hz100 hzx hUz)
  simp only [Nat.cast_one, one_mul] at hcount
  refine le_trans hcount ?_
  have hφpos : (0 : ℝ) < ((U : ℕ).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hUp.pos
  have hr : ((U : ℝ) / ((U : ℕ).totient : ℝ)) ^ 2 ≤ 4 := by
    have hratio : (U : ℝ) / ((U : ℕ).totient : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hφpos]
      calc (U : ℝ) ≤ ((2 * U.totient : ℕ) : ℝ) := by
            exact_mod_cast pp_le_two_mul_totient hUp.isPrimePow
        _ = 2 * ((U : ℕ).totient : ℝ) := by push_cast; ring
    calc ((U : ℝ) / ((U : ℕ).totient : ℝ)) ^ 2 ≤ 2 ^ 2 :=
          pow_le_pow_left₀ (by positivity) hratio 2
      _ = 4 := by norm_num
  have hL2 : (0 : ℝ) < Real.log (Zz z) ^ 2 := by
    have := log_Zz_pos hz100
    positivity
  have hstep : 128 * ((U : ℝ) / ((U : ℕ).totient : ℝ)) ^ 2 * ((x : ℝ) / U)
      ≤ 512 * ((x : ℝ) / U) := by
    have hxU : (0 : ℝ) ≤ (x : ℝ) / U := by positivity
    calc 128 * ((U : ℝ) / ((U : ℕ).totient : ℝ)) ^ 2 * ((x : ℝ) / U)
        ≤ 128 * 4 * ((x : ℝ) / U) := by
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 128)) hxU
          linarith
      _ = 512 * ((x : ℝ) / U) := by norm_num
  calc 128 * ((U : ℝ) / ((U : ℕ).totient : ℝ)) ^ 2 * ((x : ℝ) / U)
        / Real.log (Zz z) ^ 2
      ≤ 512 * ((x : ℝ) / U) / Real.log (Zz z) ^ 2 :=
        div_le_div_of_nonneg_right hstep hL2.le
    _ = 512 * (x : ℝ) / ((U : ℝ) * Real.log (Zz z) ^ 2) := by
        have hU0 : (U : ℝ) ≠ 0 := by
          have := hUp.pos
          positivity
        field_simp

/-! ## §8 — the analytic sums: Mertens over `v`, `PretenseSum` over `U` -/

/-- `16 ≤ log z` (from `z ≥ 100^16` and `log 100 ≥ 1`). -/
lemma tsw_sixteen_le_log {z : ℕ} (hz100 : 100 ^ 16 ≤ z) : (16 : ℝ) ≤ Real.log z := by
  have h100 : (1 : ℝ) ≤ Real.log 100 :=
    (Real.le_log_iff_exp_le (by norm_num)).mpr
      (le_trans Real.exp_one_lt_d9.le (by norm_num))
  have hcast : ((100 ^ 16 : ℕ) : ℝ) = (100 : ℝ) ^ (16 : ℕ) := by push_cast; ring
  have hle : Real.log ((100 : ℝ) ^ (16 : ℕ)) ≤ Real.log z := by
    rw [← hcast]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hz100)
  rw [Real.log_pow] at hle
  push_cast at hle
  linarith

/-- **The Mertens `v`-sum**: `Σ_{v ∈ V} Λ(v)/v ≤ 2·log z`. -/
lemma tsw_vsum_le {z : ℕ} (hz100 : 100 ^ 16 ≤ z) :
    ∑ v ∈ TswVIndex z, Λ v / v ≤ 2 * Real.log z := by
  have hz1 : 1 ≤ z := le_trans (Nat.one_le_pow _ _ (by norm_num)) hz100
  have hsub : TswVIndex z ⊆ Finset.Ioc 0 z := by
    intro v hv
    simp only [TswVIndex, Finset.mem_filter, Finset.mem_Ioc] at hv ⊢
    omega
  have h1 : ∑ v ∈ TswVIndex z, Λ v / v ≤ ∑ d ∈ Finset.Ioc 0 z, Λ d / d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun d _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg d))
  have h2 := mertens_vonMangoldt_div_le (N := z) hz1
  have h3 := tsw_sixteen_le_log hz100
  have h4 : Real.log 4 ≤ 3 :=
    le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)
  linarith

/-- **The `PretenseSum` `U`-sum**: `Σ_{U ∈ 𝒰} 1/U ≤ PS(2x+2)/log z` — the swap's `J2` hook
    (`d₂ := U` a `χ=+1` prime `≥ z`, `sum_inv_plusprime_le_pretense`). -/
lemma tsw_Usum_le (χ : DirichletCharacter ℂ q) {z : ℕ} (x : ℕ) (hz1 : 1 < z) :
    ∑ U ∈ TswUIndex χ z x, (1 : ℝ) / U
      ≤ PretenseSum χ (2 * x + 2) / Real.log z := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    (sum_inv_plusprime_le_pretense χ z (2 * x + 2) hz1)
  · intro U hU
    simp only [TswUIndex, Finset.mem_filter, Finset.mem_range] at hU ⊢
    exact ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2.1⟩
  · intro U _ _
    positivity

/-! ## §9 — the fibration sums -/

open Classical in
/-- **The case-A fibration sum** (`v⁴ ≤ z`, modulus pair `(v, U)`):
    `Σ_A Λ(n₋) ≤ 4096·x·PS(2x+2)/(log Z_z)²` — fiber by `(v, U)`, count each fiber by
    `tsw_countA`, then `Σ_v Λ(v)/v ≤ 2 log z` (Mertens) times `Σ_U 1/U ≤ PS/log z`. -/
lemma tsw_sumA_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ ((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
        (fun n => nMinus χ n ^ 4 ≤ z), Λ (nMinus χ n)
      ≤ 4096 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log (Zz z) ^ 2 := by
  have hz1 : (1 : ℕ) < z := lt_of_lt_of_le (by norm_num) hz100
  have hlogz_pos : (0 : ℝ) < Real.log z := by
    have := tsw_sixteen_le_log hz100
    linarith
  have hLZpos := log_Zz_pos hz100
  have hmaps : ∀ n ∈ ((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
      (fun n => nMinus χ n ^ 4 ≤ z),
      (nMinus χ n, nPlus χ (n + 2)) ∈ TswVIndex z ×ˢ TswUIndex χ z x := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    obtain ⟨⟨hnW, hnT⟩, hp4⟩ := hn
    rw [Finset.mem_product]
    constructor
    · simp only [TswVIndex, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hnT.2.2.1, le_of_lt hnT.2.2.2.1⟩, hnT.2.1,
        tsw_odd_v χ hsq hz100 hnW hnT, hp4⟩
    · simp only [TswUIndex, Finset.mem_filter, Finset.mem_range]
      have hUz := tsw_Uz_le χ hsq hnW hnT
      have hUle : nPlus χ (n + 2) ≤ nPlus χ (n + 2) * z :=
        Nat.le_mul_of_pos_right _ (by omega)
      exact ⟨by omega, hnT.2.2.2.2.2.2.1, tsw_chiU χ hnT,
        tsw_U_ge χ hsq hnW hnT, hUz⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => Λ (nMinus χ n))]
  have hfiber : ∀ p ∈ TswVIndex z ×ˢ TswUIndex χ z x,
      (∑ n ∈ (((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
          (fun n => nMinus χ n ^ 4 ≤ z)).filter
          (fun n => (nMinus χ n, nPlus χ (n + 2)) = p), Λ (nMinus χ n))
        ≤ 2048 * (x : ℝ) / Real.log (Zz z) ^ 2 * (Λ p.1 / (p.1 : ℝ))
            * (1 / (p.2 : ℝ)) := by
    rintro ⟨v, U⟩ hp
    rw [Finset.mem_product] at hp
    obtain ⟨hvI, hUI⟩ := hp
    have hv0 : (0 : ℝ) < (v : ℝ) := by
      have := (Finset.mem_filter.mp hvI).1
      have := (Finset.mem_Ioc.mp this).1
      exact_mod_cast by omega
    have hU0 : (0 : ℝ) < (U : ℝ) := by
      have := ((Finset.mem_filter.mp hUI).2).1.pos
      exact_mod_cast this
    have hterm : ∀ n ∈ (((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
        (fun n => nMinus χ n ^ 4 ≤ z)).filter
        (fun n => (nMinus χ n, nPlus χ (n + 2)) = (v, U)), Λ (nMinus χ n) = Λ v := by
      intro n hn
      have hg := (Finset.mem_filter.mp hn).2
      rw [show nMinus χ n = v from congrArg Prod.fst hg]
    have hsub : (((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
        (fun n => nMinus χ n ^ 4 ≤ z)).filter
        (fun n => (nMinus χ n, nPlus χ (n + 2)) = (v, U))
        ⊆ (baseSet x v U).filter
            (fun n => Nat.Coprime (primorial (Zz z)) ((n / v) * ((n + 2) / U))) := by
      intro m hm
      simp only [Finset.mem_filter] at hm
      obtain ⟨⟨⟨hmW, hmT⟩, _⟩, hg⟩ := hm
      have hveq : nMinus χ m = v := congrArg Prod.fst hg
      have hUeq : nPlus χ (m + 2) = U := congrArg Prod.snd hg
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [baseSet, Finset.mem_filter]
        refine ⟨l2cWindow_subset χ z x hmW, ?_, ?_⟩
        · exact hveq ▸ ⟨nPlus χ m, by rw [mul_comm]; exact tsw_n_eq χ hsq hmW⟩
        · exact hUeq ▸ tsw_U_dvd χ hsq hmW
      · rw [← hveq, ← hUeq, tsw_div_v χ hsq hmW hmT, tsw_div_U χ hsq hmW hmT]
        exact tsw_siftA χ hsq hzx hmW hmT
    have hcard : ((((((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
        (fun n => nMinus χ n ^ 4 ≤ z)).filter
        (fun n => (nMinus χ n, nPlus χ (n + 2)) = (v, U))).card : ℕ) : ℝ)
        ≤ 2048 * (x : ℝ) / ((v : ℝ) * (U : ℝ) * Real.log (Zz z) ^ 2) :=
      le_trans (Nat.cast_le.mpr (Finset.card_le_card hsub)) (tsw_countA χ hz100 hzx hvI hUI)
    calc (∑ n ∈ (((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
          (fun n => nMinus χ n ^ 4 ≤ z)).filter
          (fun n => (nMinus χ n, nPlus χ (n + 2)) = (v, U)), Λ (nMinus χ n))
        = ((((((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
            (fun n => nMinus χ n ^ 4 ≤ z)).filter
            (fun n => (nMinus χ n, nPlus χ (n + 2)) = (v, U))).card : ℕ) : ℝ) * Λ v := by
          rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2048 * (x : ℝ) / ((v : ℝ) * (U : ℝ) * Real.log (Zz z) ^ 2) * Λ v :=
          mul_le_mul_of_nonneg_right hcard vonMangoldt_nonneg
      _ = 2048 * (x : ℝ) / Real.log (Zz z) ^ 2 * (Λ v / (v : ℝ)) * (1 / (U : ℝ)) := by
          have hLZ0 : Real.log (Zz z) ≠ 0 := hLZpos.ne'
          field_simp
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  rw [Finset.sum_product]
  dsimp only
  rw [Finset.sum_congr rfl
        (fun v _ => (Finset.mul_sum (TswUIndex χ z x)
          (fun U => (1 : ℝ) / (U : ℝ))
          (2048 * (x : ℝ) / Real.log (Zz z) ^ 2 * (Λ v / (v : ℝ)))).symm),
      ← Finset.sum_mul, ← Finset.mul_sum]
  have hSa_nonneg : 0 ≤ ∑ v ∈ TswVIndex z, Λ v / (v : ℝ) :=
    Finset.sum_nonneg fun v _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg v)
  have hSb_nonneg : 0 ≤ ∑ U ∈ TswUIndex χ z x, (1 : ℝ) / U :=
    Finset.sum_nonneg fun U _ => by positivity
  have hC : (0 : ℝ) ≤ 2048 * (x : ℝ) / Real.log (Zz z) ^ 2 := by positivity
  have hSa := tsw_vsum_le hz100
  have hSb := tsw_Usum_le χ x hz1
  have hPS := pretenseSum_nonneg χ (2 * x + 2)
  calc (2048 * (x : ℝ) / Real.log (Zz z) ^ 2 * ∑ v ∈ TswVIndex z, Λ v / (v : ℝ))
        * (∑ U ∈ TswUIndex χ z x, (1 : ℝ) / U)
      ≤ (2048 * (x : ℝ) / Real.log (Zz z) ^ 2 * (2 * Real.log z))
          * (PretenseSum χ (2 * x + 2) / Real.log z) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hSa hC) hSb hSb_nonneg (by positivity)
    _ = 4096 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log (Zz z) ^ 2 := by
        field_simp
        ring

open Classical in
/-- **The case-B fibration sum** (`z < v⁴`, cofactor route, modulus pair `(1, U)`):
    `Σ_B Λ(n₋) ≤ 512·x·PS(2x+2)/(log Z_z)²` — fiber by `U` alone, weight `Λ(v) ≤ log z`
    crude, count by `tsw_countB`; the `log z` cancels against the `U`-sum's `1/log z`. -/
lemma tsw_sumB_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ ((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
        (fun n => ¬ nMinus χ n ^ 4 ≤ z), Λ (nMinus χ n)
      ≤ 512 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log (Zz z) ^ 2 := by
  have hz1 : (1 : ℕ) < z := lt_of_lt_of_le (by norm_num) hz100
  have hlogz_pos : (0 : ℝ) < Real.log z := by
    have := tsw_sixteen_le_log hz100
    linarith
  have hLZpos := log_Zz_pos hz100
  have hmaps : ∀ n ∈ ((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
      (fun n => ¬ nMinus χ n ^ 4 ≤ z), nPlus χ (n + 2) ∈ TswUIndex χ z x := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    obtain ⟨⟨hnW, hnT⟩, _⟩ := hn
    simp only [TswUIndex, Finset.mem_filter, Finset.mem_range]
    have hUz := tsw_Uz_le χ hsq hnW hnT
    have hUle : nPlus χ (n + 2) ≤ nPlus χ (n + 2) * z :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact ⟨by omega, hnT.2.2.2.2.2.2.1, tsw_chiU χ hnT,
      tsw_U_ge χ hsq hnW hnT, hUz⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => Λ (nMinus χ n))]
  have hfiber : ∀ U ∈ TswUIndex χ z x,
      (∑ n ∈ (((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
          (fun n => ¬ nMinus χ n ^ 4 ≤ z)).filter
          (fun n => nPlus χ (n + 2) = U), Λ (nMinus χ n))
        ≤ 512 * (x : ℝ) * Real.log z / Real.log (Zz z) ^ 2 * (1 / (U : ℝ)) := by
    intro U hUI
    have hU0 : (0 : ℝ) < (U : ℝ) := by
      have := ((Finset.mem_filter.mp hUI).2).1.pos
      exact_mod_cast this
    have hbound : ∀ n ∈ (((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
        (fun n => ¬ nMinus χ n ^ 4 ≤ z)).filter
        (fun n => nPlus χ (n + 2) = U), Λ (nMinus χ n) ≤ Real.log z := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      obtain ⟨⟨⟨_, hnT⟩, _⟩, _⟩ := hn
      refine le_trans vonMangoldt_le_log ?_
      have hvz : nMinus χ n < z := hnT.2.2.2.1
      have hvpos : 0 < nMinus χ n := by have := hnT.2.2.1; omega
      exact Real.log_le_log (by exact_mod_cast hvpos) (by exact_mod_cast le_of_lt hvz)
    have hsub : (((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
        (fun n => ¬ nMinus χ n ^ 4 ≤ z)).filter
        (fun n => nPlus χ (n + 2) = U)
        ⊆ (baseSet x 1 U).filter
            (fun n => Nat.Coprime (primorial (Zz z)) ((n / 1) * ((n + 2) / U))) := by
      intro m hm
      simp only [Finset.mem_filter] at hm
      obtain ⟨⟨⟨hmW, hmT⟩, hm4⟩, hUeq⟩ := hm
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [baseSet, Finset.mem_filter]
        exact ⟨l2cWindow_subset χ z x hmW, one_dvd _, hUeq ▸ tsw_U_dvd χ hsq hmW⟩
      · rw [Nat.div_one, ← hUeq, tsw_div_U χ hsq hmW hmT]
        exact tsw_siftB χ hsq hzx hmW hmT (by omega)
    have hcard : ((((((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
        (fun n => ¬ nMinus χ n ^ 4 ≤ z)).filter
        (fun n => nPlus χ (n + 2) = U)).card : ℕ) : ℝ)
        ≤ 512 * (x : ℝ) / ((U : ℝ) * Real.log (Zz z) ^ 2) :=
      le_trans (Nat.cast_le.mpr (Finset.card_le_card hsub)) (tsw_countB χ hz100 hzx hUI)
    calc (∑ n ∈ (((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
          (fun n => ¬ nMinus χ n ^ 4 ≤ z)).filter
          (fun n => nPlus χ (n + 2) = U), Λ (nMinus χ n))
        ≤ (((((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
            (fun n => ¬ nMinus χ n ^ 4 ≤ z)).filter
            (fun n => nPlus χ (n + 2) = U)).card : ℕ) • Real.log z :=
          Finset.sum_le_card_nsmul _ _ _ hbound
      _ = ((((((l2cWindow χ z x).filter (fun n => IsTsw χ z n)).filter
            (fun n => ¬ nMinus χ n ^ 4 ≤ z)).filter
            (fun n => nPlus χ (n + 2) = U)).card : ℕ) : ℝ) * Real.log z := by
          rw [nsmul_eq_mul]
      _ ≤ 512 * (x : ℝ) / ((U : ℝ) * Real.log (Zz z) ^ 2) * Real.log z :=
          mul_le_mul_of_nonneg_right hcard (by linarith)
      _ = 512 * (x : ℝ) * Real.log z / Real.log (Zz z) ^ 2 * (1 / (U : ℝ)) := by
          have hLZ0 : Real.log (Zz z) ≠ 0 := hLZpos.ne'
          field_simp
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  rw [← Finset.mul_sum]
  have hSb := tsw_Usum_le χ x hz1
  have hC : (0 : ℝ) ≤ 512 * (x : ℝ) * Real.log z / Real.log (Zz z) ^ 2 := by positivity
  calc 512 * (x : ℝ) * Real.log z / Real.log (Zz z) ^ 2
        * (∑ U ∈ TswUIndex χ z x, (1 : ℝ) / U)
      ≤ 512 * (x : ℝ) * Real.log z / Real.log (Zz z) ^ 2
          * (PretenseSum χ (2 * x + 2) / Real.log z) :=
        mul_le_mul_of_nonneg_left hSb hC
    _ = 512 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log (Zz z) ^ 2 := by
        field_simp

/-! ## §10 — the assembled count and the frozen `EL_Tsw_bound` -/

open Classical in
/-- **The T-sw weighted count** (the `hcount` discharge): splitting the guarded slice at
    `v⁴ ≤ z` and summing the two fibrations,
    `Σ_{n∈Tsw} Λ(n₋) ≤ 4718592·x·PS(2x+2)/(log z)²`
    (`4608 = 4096 + 512` at scale `log Z_z`, and `(log z)² ≤ 1024·(log Z_z)²`). -/
lemma tsw_count (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsTsw χ z n), Λ (nMinus χ n)
      ≤ 4718592 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log z ^ 2 := by
  have hA := tsw_sumA_le χ hsq hz100 hzx
  have hB := tsw_sumB_le χ hsq hz100 hzx
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((l2cWindow χ z x).filter (fun n => IsTsw χ z n))
    (fun n => nMinus χ n ^ 4 ≤ z) (fun n => Λ (nMinus χ n))
  have hLZpos := log_Zz_pos hz100
  have hlogz_pos : (0 : ℝ) < Real.log z := by
    have := tsw_sixteen_le_log hz100
    linarith
  have hPS := pretenseSum_nonneg χ (2 * x + 2)
  have hconv : Real.log z ^ 2 ≤ 1024 * Real.log (Zz z) ^ 2 := by
    have h := log_le_32_mul_log_Zz hz100
    calc Real.log z ^ 2 ≤ (32 * Real.log (Zz z)) ^ 2 :=
          pow_le_pow_left₀ (by linarith) h 2
      _ = 1024 * Real.log (Zz z) ^ 2 := by ring
  have hstep : (4608 : ℝ) * x * PretenseSum χ (2 * x + 2) / Real.log (Zz z) ^ 2
      ≤ 4718592 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log z ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc 4608 * (x : ℝ) * PretenseSum χ (2 * x + 2) * Real.log z ^ 2
        ≤ 4608 * (x : ℝ) * PretenseSum χ (2 * x + 2) * (1024 * Real.log (Zz z) ^ 2) :=
          mul_le_mul_of_nonneg_left hconv (by positivity)
      _ = 4718592 * (x : ℝ) * PretenseSum χ (2 * x + 2) * Real.log (Zz z) ^ 2 := by ring
  have hsum : (4096 : ℝ) * x * PretenseSum χ (2 * x + 2) / Real.log (Zz z) ^ 2
        + 512 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log (Zz z) ^ 2
      = 4608 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log (Zz z) ^ 2 := by
    ring
  rw [← hsplit]
  linarith [hA, hB, hstep, hsum]

/-- **`EL_Tsw_bound` — the frozen T-sw swap-family budget (freeze §S4 + house amendments;
    the `J2` row).**  Over the guarded swap slice (`n₊ = P` prime, `1 < v < z`, `m = U`
    prime, `d₂ := U ≤ (2x+2)/z`, `v` routed at `z^{1/4}`), under the master hypothesis
    packet,

    `EL_Tsw χ z x ≤ Cmain·(x / L')·exp(5·z₀)·PretenseSum χ (2x+2)`

    with the explicit absolute constant `Cmain = 4718592 = 4608·1024` (no dependence on
    `χ`, `z`, `x`).  Aexp `= 5` closes via `z₀²·e^{2(log2)z₀} ≤ e^{5z₀}`. -/
theorem EL_Tsw_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : (Lwin x) ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    EL_Tsw χ z x
      ≤ 4718592 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) :=
  EL_Tsw_bound_of_count χ hsq hz100 hz8 hzx (by norm_num) (tsw_count χ hsq hz100 hzx)

end Salt.HB
