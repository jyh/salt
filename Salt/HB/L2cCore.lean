/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.TransferFull
import Salt.HB.MixedCount
import Salt.HB.StarWindow
import Salt.Maynard.Mertens

/-!
# HB-L2c core surgery — Wave 1 (node HB-L2c, Horn A keystone)

The first stones of Heath-Brown's Lemma-2c exact-overshoot surgery.  Instead of the
τ-crude majorant slot (`hres` / `hb_lemma2`, which is provably `L²`-inflated at the
worst pattern and is BYPASSED per the L2c freeze), we work with the **exact** per-term
difference

`overshootExact χ n = (Λ̃−Λ)(n)·Λ̃(n+2) + Λ(n)·(Λ̃−Λ)(n+2)`,

which is *identically* the term of `S⁽²⁾ − S⁽¹⁾` (`S2_sub_S1_eq`, the exported ring
identity of `Salt.HB.Transfer`).  This file supplies the four surgery rungs feeding the
downstream `E_L`/`E_R` family analysis (Wave 2) and the master assembly (Wave 3):

* **R1** `overshootExact` + `S2_sub_S1_eq`/`_exact` + the exact vanishing lemmas
  (`Λ̃−Λ = 0` at primes / `1` / pure `χ=−1` prime powers / `ω(n₋) ≥ 2`) and the
  support classification.
* **R2** `l2cWindow` + the `CoprimeSupport`/`excPrimorial`-coprimality glue + the
  roughness cap, the `2^{ω(n₊)}` cap `≤ e^{(log2)z₀}`, the single/all-block `Λ̃` cap
  `≤ e^{(log2)z₀}·L'`, and the parity link.
* **R3** `l2c_pair_count` (from `hb_lemma8'_unconditional`) + the legality-absorbed
  clean 128-form + the `Zz = ⌊z^{1/16}⌋` / `Zf = ⌊x^{1/48}⌋` `100`-gates.
* **R4** the `χ=+1` prime counters: the `PretenseSum` conversion, the Chebyshev-`χ`
  count, and the Mertens re-exports.

`z₀ := log(2x+2)/log z` and `L' := log(2x+2)` are the shared window scales (`z0`, `Lwin`).

Single-writer file (`L2cCore.lean`); it touches no landed file and is NOT yet in the
`Salt.HB.All` manifest (that is Wave 3's responsibility).  It builds standalone via its
imports.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — shared window scales and the exact overshoot -/

/-- `L' := log(2x+2)` — the window log-scale. -/
noncomputable def Lwin (x : ℕ) : ℝ := Real.log (2 * (x : ℝ) + 2)

/-- `z₀ := log(2x+2)/log z` — the small-prime exponent scale. -/
noncomputable def z0 (z x : ℕ) : ℝ := Lwin x / Real.log z

lemma Lwin_nonneg (x : ℕ) : 0 ≤ Lwin x := by
  rw [Lwin]; exact Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) x; linarith)

lemma z0_nonneg {z x : ℕ} (hz2 : 2 ≤ z) : 0 ≤ z0 z x := by
  rw [z0]
  exact div_nonneg (Lwin_nonneg x) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z)))

/-- The **exact** per-term transfer difference `Λ̃(n)Λ̃(n+2) − Λ(n)Λ(n+2)`, written in the
    Lemma-2 split form `(Λ̃−Λ)(n)·Λ̃(n+2) + Λ(n)·(Λ̃−Λ)(n+2)`. -/
noncomputable def overshootExact (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  (LamTilde χ n - Λ n) * LamTilde χ (n + 2) + Λ n * (LamTilde χ (n + 2) - Λ (n + 2))

/-! ## §1 (R1) — the exact identity, vanishing lemmas, support classification -/

/-- **The exported ring identity (exact).**  `S⁽²⁾ − S⁽¹⁾ = Σ_{n∈A} overshootExact χ n`.
    This is the honest replacement for the bypassed `hb_lemma2`/`hres` reduction — the
    surgery consumes this *equality*, not a τ-crude majorant. -/
theorem S2_sub_S1_eq (χ : DirichletCharacter ℂ q) (A : Finset ℕ) :
    S2 χ A - S1 A = ∑ n ∈ A, overshootExact χ n := by
  unfold S2 S1 overshootExact
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- The `≤` form of `S2_sub_S1_eq` (the interface shape the master consumes). -/
theorem S2_sub_S1_exact (χ : DirichletCharacter ℂ q) (A : Finset ℕ) :
    S2 χ A - S1 A ≤ ∑ n ∈ A, overshootExact χ n :=
  le_of_eq (S2_sub_S1_eq χ A)

/-- **Vanishing at primes.**  `Λ̃(p) = Λ(p)` for any prime `p` (the only surviving
    convolution terms are `a = 1` — `f(1)=1`, `n/1 = p` — and `a = p` — `Λ(1)=0`). -/
lemma lamTilde_sub_vonMangoldt_eq_zero_of_prime (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) : LamTilde χ p - Λ p = 0 := by
  have h1 : LamTilde χ p = Λ p := by
    rw [LamTilde_eq_sum_div, hp.divisors, Finset.sum_pair hp.one_lt.ne,
        Nat.div_one, Nat.div_self hp.pos, vonMangoldt_apply_one, mul_zero, add_zero,
        (fChiArith_mult χ hsq).map_one, one_mul]
  rw [h1, sub_self]

/-- **Vanishing at `1`.**  `Λ̃(1) = 0 = Λ(1)`. -/
lemma lamTilde_sub_vonMangoldt_eq_zero_of_one (χ : DirichletCharacter ℂ q) :
    LamTilde χ 1 - Λ 1 = 0 := by
  have h1 : LamTilde χ 1 = 0 := by
    rw [LamTilde_eq_sum_div, Nat.divisors_one, Finset.sum_singleton, Nat.div_one,
        vonMangoldt_apply_one, mul_zero]
  rw [h1, vonMangoldt_apply_one, sub_self]

/-- **Vanishing on the pure `χ=−1` part.**  If `n₊ = 1` and `n₋` is a prime power then
    `n = n₋` and `Λ̃(n) = f(n₊)·Λ(n₋) = 1·Λ(n) = Λ(n)`. -/
lemma lamTilde_sub_vonMangoldt_eq_zero_of_pure_minus (χ : DirichletCharacter ℂ q)
    (hsq : χ ^ 2 = 1) {n : ℕ} (hn : n ≠ 0) (hcop : Nat.Coprime n q)
    (hP1 : nPlus χ n = 1) (hM1 : IsPrimePow (nMinus χ n)) : LamTilde χ n - Λ n = 0 := by
  have hnM : n = nMinus χ n := by
    have h := eq_nPlus_mul_nMinus χ hsq hn hcop; rw [hP1, one_mul] at h; exact h
  have hf1 : fChiSum χ (nPlus χ n) = 1 := by
    rw [hP1, ← fChiArith_eq_fChiSum]; exact (fChiArith_mult χ hsq).map_one
  rw [LamTilde_eq_single_of_card_one χ hsq hn hcop hM1, hf1, one_mul, ← hnM, sub_self]

/-- **Vanishing when `ω(n₋) ≥ 2`.**  Then `Λ̃(n) = 0` (two-block kill) and `Λ(n) = 0`
    (`n` inherits two distinct primes, so is not a prime power). -/
lemma lamTilde_sub_vonMangoldt_eq_zero_of_two_le_card (χ : DirichletCharacter ℂ q)
    (hsq : χ ^ 2 = 1) {n : ℕ} (hn : n ≠ 0) (hcop : Nat.Coprime n q)
    (hM : 2 ≤ (nMinus χ n).primeFactors.card) : LamTilde χ n - Λ n = 0 := by
  have hLt : LamTilde χ n = 0 := LamTilde_eq_zero_of_two_le_card χ hsq hn hcop hM
  have hMdvd : nMinus χ n ∣ n :=
    ⟨nPlus χ n, by rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq hn hcop⟩
  have hnp : ¬ IsPrimePow n := not_isPrimePow_of_two_le_card hn hMdvd hM
  rw [hLt, vonMangoldt_eq_zero_iff.mpr hnp, sub_self]

/-- **Support classification of `Λ̃−Λ`.**  If `Λ̃(n) − Λ(n) ≠ 0` then `n` is composite
    (`¬ n.Prime`, `n ≠ 1`) and either `n₋ = 1` (a `χ=+1` composite) or `n₋` is a single
    prime power with `n₊ > 1` — exactly HB's `L₂`–`L₄` surviving shapes. -/
lemma lamTilde_sub_support_classification (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {n : ℕ} (hn : n ≠ 0) (hcop : Nat.Coprime n q) (hne : LamTilde χ n - Λ n ≠ 0) :
    ¬ n.Prime ∧ n ≠ 1 ∧
      (nMinus χ n = 1 ∨ (IsPrimePow (nMinus χ n) ∧ 1 < nPlus χ n)) := by
  refine ⟨fun hp => hne (lamTilde_sub_vonMangoldt_eq_zero_of_prime χ hsq hp), ?_, ?_⟩
  · rintro rfl; exact hne (lamTilde_sub_vonMangoldt_eq_zero_of_one χ)
  · by_contra hcon
    have hM1 : nMinus χ n ≠ 1 := fun h => hcon (Or.inl h)
    have hcon2 : IsPrimePow (nMinus χ n) → nPlus χ n ≤ 1 := fun hpp => by
      by_contra hlt; exact hcon (Or.inr ⟨hpp, by omega⟩)
    by_cases hpp : IsPrimePow (nMinus χ n)
    · have hle := hcon2 hpp
      have hP1 : nPlus χ n = 1 := by have := nPlus_pos χ n; omega
      exact hne (lamTilde_sub_vonMangoldt_eq_zero_of_pure_minus χ hsq hn hcop hP1 hpp)
    · have hcard : 2 ≤ (nMinus χ n).primeFactors.card := by
        rcases Nat.lt_trichotomy (nMinus χ n).primeFactors.card 1 with h | h | h
        · have hc0 : (nMinus χ n).primeFactors.card = 0 := by omega
          rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hc0) with h0 | h1
          · exact absurd h0 (nMinus_pos χ n).ne'
          · exact absurd h1 hM1
        · exact absurd (isPrimePow_iff_card_primeFactors_eq_one.mpr h) hpp
        · omega
      exact hne (lamTilde_sub_vonMangoldt_eq_zero_of_two_le_card χ hsq hn hcop hcard)

/-! ## §2 (R2) — the honest window, its support glue, roughness, and the caps -/

/-- **The L2c honest window** `W = {n ∈ (x,2x] : (n(n+2), q·excPrimorial χ z) = 1}` — HB's
    support `(n(n+2), qP)=1` realized with the minimal honest modulus (including the
    `q`-part), so a single window serves both the transfer step and the star step. -/
noncomputable def l2cWindow (χ : DirichletCharacter ℂ q) (z x : ℕ) : Finset ℕ :=
  (Finset.Ioc x (2 * x)).filter (fun n => Nat.Coprime (n * (n + 2)) (q * excPrimorial χ z))

lemma l2cWindow_subset (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    l2cWindow χ z x ⊆ Finset.Ioc x (2 * x) := Finset.filter_subset _ _

/-- The window feeds `CoprimeSupport q` (via `coprimeSupport_window`, `q ∣ q·P`). -/
lemma l2cWindow_coprimeSupport (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    CoprimeSupport q (l2cWindow χ z x) :=
  coprimeSupport_window x (q * excPrimorial χ z) (dvd_mul_right q _)

/-- Per-element `excPrimorial`-coprimality (via `excPrimorial χ z ∣ q·excPrimorial χ z`) —
    the hypothesis of the parametric `S2_sub_S3_window`, so one window serves WP3. -/
lemma l2cWindow_excPrimorial_coprime (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    ∀ n ∈ l2cWindow χ z x, Nat.Coprime (n * (n + 2)) (excPrimorial χ z) := by
  intro n hn
  simp only [l2cWindow, Finset.mem_filter] at hn
  exact Nat.Coprime.coprime_dvd_right (dvd_mul_left (excPrimorial χ z) q) hn.2

/-- **Window roughness.**  Every `χ ≠ −1` prime of `n(n+2)` for `n` in the window is `≥ z`
    (the small `χ ≠ −1` primes are all removed by the `excPrimorial`-coprimality). -/
lemma l2cWindow_roughness (χ : DirichletCharacter ℂ q) (z x : ℕ) {n : ℕ}
    (hn : n ∈ l2cWindow χ z x) {p : ℕ} (hp : p.Prime) (hpd : p ∣ n * (n + 2))
    (hchi : chiRe χ p ≠ -1) : z ≤ p := by
  by_contra hlt
  have hpz : p < z := not_le.mp hlt
  have hcop := l2cWindow_excPrimorial_coprime χ z x n hn
  have hmem : p ∈ (Finset.range z).filter (fun p => p.Prime ∧ chiRe χ p ≠ -1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpz, hp, hchi⟩
  have hdvdP : p ∣ excPrimorial χ z := Finset.dvd_prod_of_mem _ hmem
  have hgcd : p ∣ Nat.gcd (n * (n + 2)) (excPrimorial χ z) := Nat.dvd_gcd hpd hdvdP
  have hc1 : Nat.gcd (n * (n + 2)) (excPrimorial χ z) = 1 := hcop
  rw [hc1] at hgcd
  exact hp.ne_one (Nat.dvd_one.mp hgcd)

/-- **The `ω(m₊)` cap.**  If every prime of `m₊` is `≥ z` and `m ≤ 2x+2`, then
    `2^{ω(m₊)} ≤ e^{(log 2)·z₀}` (the `z^{ω} ≤ m₊ ≤ 2x+2` count, `z₀ = log(2x+2)/log z`). -/
lemma omega_cap (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) (hz2 : 2 ≤ z)
    {m : ℕ} (hm0 : m ≠ 0) (hcop : Nat.Coprime m q) (hmle : m ≤ 2 * x + 2)
    (hrough : ∀ p ∈ (nPlus χ m).primeFactors, z ≤ p) :
    (2 : ℝ) ^ (nPlus χ m).primeFactors.card ≤ Real.exp (Real.log 2 * z0 z x) := by
  have hzR : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hlogz : 0 < Real.log z := Real.log_pos hzR
  have hmP_dvd : nPlus χ m ∣ m := ⟨nMinus χ m, eq_nPlus_mul_nMinus χ hsq hm0 hcop⟩
  have hmP_le : nPlus χ m ≤ 2 * x + 2 :=
    le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hmP_dvd) hmle
  have hrad_le : (∏ p ∈ (nPlus χ m).primeFactors, p) ≤ nPlus χ m :=
    Nat.le_of_dvd (nPlus_pos χ m) (Nat.prod_primeFactors_dvd _)
  have hzc_pos : (0 : ℝ) < (z : ℝ) ^ (nPlus χ m).primeFactors.card :=
    pow_pos (by exact_mod_cast (by omega : 0 < z)) _
  have hzc_le : (z : ℝ) ^ (nPlus χ m).primeFactors.card ≤ 2 * (x : ℝ) + 2 := by
    calc (z : ℝ) ^ (nPlus χ m).primeFactors.card
        = ∏ _p ∈ (nPlus χ m).primeFactors, (z : ℝ) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ (nPlus χ m).primeFactors, (p : ℝ) :=
          Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => by exact_mod_cast hrough p hp)
      _ ≤ 2 * (x : ℝ) + 2 := by rw [← Nat.cast_prod]; exact_mod_cast le_trans hrad_le hmP_le
  have hc_le : ((nPlus χ m).primeFactors.card : ℝ) ≤ z0 z x := by
    rw [z0, le_div_iff₀ hlogz, Lwin, ← Real.log_pow]
    exact Real.log_le_log hzc_pos hzc_le
  rw [show (2 : ℝ) ^ (nPlus χ m).primeFactors.card
      = Real.exp (((nPlus χ m).primeFactors.card : ℝ) * Real.log 2) from by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]]
  refine Real.exp_le_exp.mpr ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left hc_le (Real.log_nonneg (by norm_num))

/-- **The `Λ̃` cap.**  On a window element `m` (`m ≤ 2x+2`, every `χ ≠ −1` prime of `m`
    is `≥ z`), the single/all-block value obeys `Λ̃(m) ≤ e^{(log 2)·z₀}·L'`. -/
lemma lamTilde_cap (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) (hz2 : 2 ≤ z)
    {m : ℕ} (hm0 : m ≠ 0) (hcop : Nat.Coprime m q) (hmle : m ≤ 2 * x + 2)
    (hrough : ∀ p, p.Prime → p ∣ m → chiRe χ p ≠ -1 → z ≤ p) :
    LamTilde χ m ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x := by
  have hmP_dvd : nPlus χ m ∣ m := ⟨nMinus χ m, eq_nPlus_mul_nMinus χ hsq hm0 hcop⟩
  have hroughP : ∀ p ∈ (nPlus χ m).primeFactors, z ≤ p := fun p hp =>
    hrough p (Nat.prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hmP_dvd) (by rw [nPlus_sign hp]; norm_num)
  have hcap := omega_cap χ hsq z x hz2 hm0 hcop hmle hroughP
  have hexp0 : 0 ≤ Real.exp (Real.log 2 * z0 z x) := (Real.exp_pos _).le
  have hfP : fChiSum χ (nPlus χ m) = (2 : ℝ) ^ (nPlus χ m).primeFactors.card := by
    rw [← fChiArith_eq_fChiSum]
    exact fChiArith_eq_two_pow χ hsq (nPlus_pos χ m).ne' (fun p hp => nPlus_sign hp)
  have hlogm_le : Real.log m ≤ Lwin x := by
    rw [Lwin]
    exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hm0) (by exact_mod_cast hmle)
  rcases lt_trichotomy (nMinus χ m).primeFactors.card 1 with hc | hc | hc
  · have hM1 : nMinus χ m = 1 := by
      have hc0 : (nMinus χ m).primeFactors.card = 0 := by omega
      rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hc0) with h0 | h1
      · exact absurd h0 (nMinus_pos χ m).ne'
      · exact h1
    have hPm : nPlus χ m = m := by
      have h := eq_nPlus_mul_nMinus χ hsq hm0 hcop; rw [hM1, mul_one] at h; exact h.symm
    calc LamTilde χ m ≤ fChiSum χ m * Real.log m := LamTilde_le_of_nMinus_one χ hsq hm0 hcop hM1
      _ = fChiSum χ (nPlus χ m) * Real.log m := by rw [hPm]
      _ = (2 : ℝ) ^ (nPlus χ m).primeFactors.card * Real.log m := by rw [hfP]
      _ ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x := mul_le_mul hcap hlogm_le
          (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0)) hexp0
  · have hM1 : IsPrimePow (nMinus χ m) := isPrimePow_iff_card_primeFactors_eq_one.mpr hc
    have hMdvd : nMinus χ m ∣ m :=
      ⟨nPlus χ m, by rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq hm0 hcop⟩
    have hMle : nMinus χ m ≤ 2 * x + 2 :=
      le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hMdvd) hmle
    have hLamM : Λ (nMinus χ m) ≤ Lwin x := by
      rw [Lwin]
      exact le_trans vonMangoldt_le_log
        (Real.log_le_log (by exact_mod_cast nMinus_pos χ m) (by exact_mod_cast hMle))
    calc LamTilde χ m = fChiSum χ (nPlus χ m) * Λ (nMinus χ m) :=
          LamTilde_eq_single_of_card_one χ hsq hm0 hcop hM1
      _ = (2 : ℝ) ^ (nPlus χ m).primeFactors.card * Λ (nMinus χ m) := by rw [hfP]
      _ ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x :=
          mul_le_mul hcap hLamM vonMangoldt_nonneg hexp0
  · rw [LamTilde_eq_zero_of_two_le_card χ hsq hm0 hcop hc]
    exact mul_nonneg hexp0 (Lwin_nonneg x)

/-- **The parity link.**  `n` is even iff `n+2` is even — the honest twin case forces
    both odd unless `χ_ℝ(2) = −1` (then `2 ∉ excPrimorial`, the both-2-powers corner). -/
lemma l2cWindow_parity_link (n : ℕ) : Even n ↔ Even (n + 2) := by
  constructor
  · intro h; exact Even.add h even_two
  · intro h; exact (Nat.even_add.mp h).mpr even_two

/-! ## §3 (R3) — the cofactor pair count and the sieve-floor gates -/

/-- **The L2c pair count** (from `hb_lemma8'_unconditional`).  For `Z ≥ 100` and a positive
    odd coprime pair `d₁,d₂`, the cofactor-sifted count over `baseSet x d₁ d₂` obeys HB's
    (3.3):  `≤ 64·(d₁d₂/φ)²·(x/(d₁d₂))/(log Z)² + 2 Z⁸`. -/
theorem l2c_pair_count {x d₁ d₂ Z : ℕ} (hZ : 100 ≤ Z)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (ho1 : Odd d₁) (ho2 : Odd d₂) (hcop12 : Nat.Coprime d₁ d₂) :
    (((baseSet x d₁ d₂).filter
        (fun n => Nat.Coprime (primorial Z) ((n / d₁) * ((n + 2) / d₂)))).card : ℝ)
      ≤ 64 * ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂))) ^ 2 * ((x : ℝ) / (d₁ * d₂))
          / (Real.log Z) ^ 2 + 2 * (Z : ℝ) ^ 8 :=
  hb_lemma8'_unconditional hZ (by omega) hd₁ hd₂ ho1 ho2 hcop12

/-- **The clean (legality-absorbed) form.**  Under the legality
    `d₁d₂·Z⁸·(log Z)² ≤ 32x`, the `2 Z⁸` junk is dominated (`(d₁d₂/φ)² ≥ 1`) and the count
    obeys the sharp `≤ 128·(d₁d₂/φ)²·(x/(d₁d₂))/(log Z)²`. -/
theorem l2c_pair_count_clean {x d₁ d₂ Z : ℕ} (hZ : 100 ≤ Z)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (ho1 : Odd d₁) (ho2 : Odd d₂) (hcop12 : Nat.Coprime d₁ d₂)
    (hleg : (d₁ * d₂ : ℝ) * (Z : ℝ) ^ 8 * (Real.log Z) ^ 2 ≤ 32 * x) :
    (((baseSet x d₁ d₂).filter
        (fun n => Nat.Coprime (primorial Z) ((n / d₁) * ((n + 2) / d₂)))).card : ℝ)
      ≤ 128 * ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂))) ^ 2 * ((x : ℝ) / (d₁ * d₂))
          / (Real.log Z) ^ 2 := by
  have hbase := l2c_pair_count (x := x) hZ hd₁ hd₂ ho1 ho2 hcop12
  have hd1r : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
  have hd2r : (0 : ℝ) < d₂ := by exact_mod_cast hd₂
  have hDpos : (0 : ℝ) < (d₁ : ℝ) * d₂ := mul_pos hd1r hd2r
  have hLz2 : (0 : ℝ) < (Real.log Z) ^ 2 :=
    pow_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < Z))) 2
  have hPpos : (0 : ℝ) < (Nat.totient (d₁ * d₂) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hd₁ hd₂)
  have hPleD : (Nat.totient (d₁ * d₂) : ℝ) ≤ (d₁ : ℝ) * d₂ := by
    calc (Nat.totient (d₁ * d₂) : ℝ) ≤ ((d₁ * d₂ : ℕ) : ℝ) := by exact_mod_cast Nat.totient_le _
      _ = (d₁ : ℝ) * d₂ := by push_cast; ring
  have hkey : 2 * (Z : ℝ) ^ 8
      ≤ 64 * ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂))) ^ 2 * ((x : ℝ) / (d₁ * d₂))
          / (Real.log Z) ^ 2 := by
    rw [le_div_iff₀ hLz2,
        show 64 * ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂))) ^ 2 * ((x : ℝ) / (d₁ * d₂))
            = 64 * (x : ℝ) * ((d₁ : ℝ) * d₂) / (Nat.totient (d₁ * d₂)) ^ 2 from by
          field_simp [hDpos.ne', hPpos.ne'],
        le_div_iff₀ (by positivity : (0 : ℝ) < (Nat.totient (d₁ * d₂) : ℝ) ^ 2)]
    calc 2 * (Z : ℝ) ^ 8 * (Real.log Z) ^ 2 * (Nat.totient (d₁ * d₂) : ℝ) ^ 2
        ≤ 2 * (Z : ℝ) ^ 8 * (Real.log Z) ^ 2 * ((d₁ : ℝ) * d₂) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hPpos.le hPleD 2) (by positivity)
      _ = ((d₁ : ℝ) * d₂) * (((d₁ : ℝ) * d₂) * (Z : ℝ) ^ 8 * (Real.log Z) ^ 2) * 2 := by ring
      _ ≤ ((d₁ : ℝ) * d₂) * (32 * x) * 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hleg hDpos.le) (by norm_num)
      _ = 64 * (x : ℝ) * ((d₁ : ℝ) * d₂) := by ring
  rw [show 128 * ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂))) ^ 2 * ((x : ℝ) / (d₁ * d₂))
          / (Real.log Z) ^ 2
        = 2 * (64 * ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂))) ^ 2 * ((x : ℝ) / (d₁ * d₂))
            / (Real.log Z) ^ 2) from by ring]
  linarith [hbase, hkey]

/-- The inner-sieve floor `Z_z := ⌊z^{1/16}⌋` (the `z`-rough cofactor gate). -/
noncomputable def Zz (z : ℕ) : ℕ := ⌊(z : ℝ) ^ ((1 : ℝ) / 16)⌋₊

/-- The inner-sieve floor `Z_f := ⌊x^{1/48}⌋` (the modulus-route gate; repaired exponent
    `1/48`, healing the `100`-gate at `x ≥ z³ ≥ 100^48`). -/
noncomputable def Zf (x : ℕ) : ℕ := ⌊(x : ℝ) ^ ((1 : ℝ) / 48)⌋₊

/-- **The `Z_z` gate.**  `100 ≤ Z_z` exactly when `100^16 ≤ z`. -/
lemma Zz_ge_100 {z : ℕ} (hz100 : 100 ^ 16 ≤ z) : 100 ≤ Zz z := by
  have hzr : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
  have h100 : ((100 : ℝ) ^ 16) ^ ((1 : ℝ) / 16) = (100 : ℝ) := by
    rw [← Real.rpow_natCast (100 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100),
        show ((16 : ℕ) : ℝ) * ((1 : ℝ) / 16) = 1 by norm_num, Real.rpow_one]
  rw [Zz]
  refine Nat.le_floor ?_
  rw [show ((100 : ℕ) : ℝ) = (100 : ℝ) by norm_num, ← h100]
  exact Real.rpow_le_rpow (by positivity) hzr (by norm_num)

/-- **The `Z_f` gate.**  `100 ≤ Z_f` from `100^16 ≤ z` and `z³ ≤ x` (so `x ≥ 100^48`). -/
lemma Zf_ge_100 {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) : 100 ≤ Zf x := by
  have hzr : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
  have hx48 : (100 : ℝ) ^ 48 ≤ (x : ℝ) := by
    calc (100 : ℝ) ^ 48 = ((100 : ℝ) ^ 16) ^ 3 := by rw [show (48 : ℕ) = 16 * 3 from rfl, pow_mul]
      _ ≤ (z : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hzr 3
      _ ≤ (x : ℝ) := hzx
  have h100 : ((100 : ℝ) ^ 48) ^ ((1 : ℝ) / 48) = (100 : ℝ) := by
    rw [← Real.rpow_natCast (100 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100),
        show ((48 : ℕ) : ℝ) * ((1 : ℝ) / 48) = 1 by norm_num, Real.rpow_one]
  rw [Zf]
  refine Nat.le_floor ?_
  rw [show ((100 : ℕ) : ℝ) = (100 : ℝ) by norm_num, ← h100]
  exact Real.rpow_le_rpow (by positivity) hx48 (by norm_num)

/-! ## §4 (R4) — the χ=+1 prime counters and the Mertens re-exports -/

/-- **The `PretenseSum` conversion.**  `Σ_{z≤p≤N, χ=1} 1/p ≤ PretenseSum χ N / log z`
    (termwise `log p / p ≥ (log z)·(1/p)`); equivalently `≤ z₀·PS/L'`. -/
lemma sum_inv_plusprime_le_pretense (χ : DirichletCharacter ℂ q) (z N : ℕ) (hz : 1 < z) :
    ∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p),
        (1 : ℝ) / p
      ≤ PretenseSum χ N / Real.log z := by
  have hlogz : 0 < Real.log z := Real.log_pos (by exact_mod_cast hz)
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  rw [le_div_iff₀ hlogz, Finset.sum_mul, PretenseSum]
  refine le_trans (Finset.sum_le_sum ?_) (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨_, hpp, _, hzp⟩ := hp
    have hlogzp : Real.log z ≤ Real.log p := Real.log_le_log hz0 (by exact_mod_cast hzp)
    calc (1 : ℝ) / p * Real.log z = Real.log z * (1 / p) := by ring
      _ ≤ Real.log p * (1 / p) := mul_le_mul_of_nonneg_right hlogzp (by positivity)
      _ = Real.log p / p := by ring
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  · intro p hp _
    rw [Finset.mem_filter] at hp
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)) (by positivity)

/-- **The Chebyshev-`χ` count.**  `#{p ∈ (a,b], prime, χ=1} ≤ (b/log a)·PretenseSum χ N`
    for `1 < a`, `b ≤ N` (termwise `1 ≤ (b/p)·(log p/log a)`). -/
lemma chebyshev_chi_count (χ : DirichletCharacter ℂ q) {a b N : ℕ} (ha : 1 < a) (hbN : b ≤ N) :
    (((Finset.Ioc a b).filter (fun p => Nat.Prime p ∧ chiRe χ p = 1)).card : ℝ)
      ≤ ((b : ℝ) / Real.log a) * PretenseSum χ N := by
  have hloga : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha)
  have hcard : (((Finset.Ioc a b).filter (fun p => Nat.Prime p ∧ chiRe χ p = 1)).card : ℝ)
      = ∑ _p ∈ (Finset.Ioc a b).filter (fun p => Nat.Prime p ∧ chiRe χ p = 1), (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard]
  calc (∑ _p ∈ (Finset.Ioc a b).filter (fun p => Nat.Prime p ∧ chiRe χ p = 1), (1 : ℝ))
      ≤ ∑ p ∈ (Finset.Ioc a b).filter (fun p => Nat.Prime p ∧ chiRe χ p = 1),
          ((b : ℝ) / Real.log a) * (Real.log p / p) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter, Finset.mem_Ioc] at hp
        obtain ⟨⟨hap, hpb⟩, hpp, _⟩ := hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hap' : (a : ℝ) ≤ p := by exact_mod_cast (by omega : a ≤ p)
        have hlogap : Real.log a ≤ Real.log p :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < a)) hap'
        have e1 : (1 : ℝ) ≤ Real.log p / Real.log a := (one_le_div hloga).mpr hlogap
        have e2 : (1 : ℝ) ≤ (b : ℝ) / p := (one_le_div hp0).mpr (by exact_mod_cast hpb)
        calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ (b : ℝ) / p * (Real.log p / Real.log a) :=
              mul_le_mul e2 e1 (by norm_num) (by positivity)
          _ = (b : ℝ) / Real.log a * (Real.log p / p) := by ring
    _ = ((b : ℝ) / Real.log a) * ∑ p ∈ (Finset.Ioc a b).filter
          (fun p => Nat.Prime p ∧ chiRe χ p = 1), (Real.log p / p) := by rw [Finset.mul_sum]
    _ ≤ ((b : ℝ) / Real.log a) * PretenseSum χ N := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (Nat.cast_nonneg b) hloga.le)
        rw [PretenseSum]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_filter, Finset.mem_Ioc] at hp
          rw [Finset.mem_filter, Finset.mem_range]
          obtain ⟨⟨hap, hpb⟩, hpp, hchi⟩ := hp
          exact ⟨by omega, hpp, hchi⟩
        · intro p hp _
          rw [Finset.mem_filter] at hp
          exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)) (by positivity)

/-- Re-export: Mertens' first theorem (von Mangoldt form). -/
lemma mertens_vonMangoldt_div_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Ioc 0 N, Λ d / d ≤ Real.log N + (Real.log 4 + 4) :=
  Salt.Maynard.sum_vonMangoldt_div_le hN

/-- Re-export: Mertens' first theorem (prime form). -/
lemma mertens_log_div_prime_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / p
      ≤ Real.log N + (Real.log 4 + 4) :=
  Salt.Maynard.sum_log_div_prime_le hN

end Salt.HB
