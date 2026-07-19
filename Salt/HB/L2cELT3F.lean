/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cELT3
import Salt.HB.L2cELT2

/-!
# HB-L2c — the `E_L` T3 weighted fibration (node `L2c-T3-fib`; the `J2` `PretenseSum` row)

This file lands the frozen `EL_T3F_bound` — the guarded `T3` budget on top of the landed
reduction layer `Salt.HB.L2cELT3` (`lamTilde_sub_eq_two_mul_of_biprime`, the exact `2·Λ(n₋)`
identity).  The `T3` family (freeze §S4) is the biprime support of `E_L`:

* `n₊ = P` a single **χ=+1 prime** (`f(P) = 2`), and
* `n₋ = v` a single **χ=−1 prime** with `z ≤ v`,

so `n = P·v` is a squarefree biprime of opposite signs.  On this support `(Λ̃−Λ)(n) = 2·Λ(v)`
**EXACTLY** (the landed biprime identity — NO `e^{z₀}` factor, so the freeze's T3 `e^{0.7z₀}`
vs T2's `e^{1.4z₀}`).  The `n+2` block `w := (n+2)₋` is routed at `z^{1/4}`.

## The route (freeze §S4 T3 + the T3 §NOTES + the T2 template)

The window roughness forces `P ≥ z`, so `P = n/v ≤ 2x/z` — the freeze's `d₁ := P` cofactor,
whose reciprocals sum to the `PretenseSum` slot via `sum_inv_plusprime_le_pretense`.  **PS-source
soundness (catch — LOUD):** unlike the T2′ line (which needed the `minFac((n+2)₊)` repair), the
T3 PS-source `P = nPlus χ n` is a *genuine* `χ=+1` prime — `chiRe χ P = 1` by `nPlus_dvd_sign`
on `P ∣ P`, `z ≤ P` by `l2cWindow_rough`.  So `Σ 1/P ≤ z₀·PS/L'` is applied directly.

The `Λ(v)` weight varies within each `d₁ = P` fiber (`v = n/P` is the sifted cofactor, NOT a
summable coordinate — the original T3 executor's *catch 1*), so it is crude-bounded
`Λ(v) ≤ L'`; this is compensated by keeping `Λ̃(n+2)` **sharp** (`w` in the modulus `d₂`, the
`1/(log Zz)²` pair-count saving).  The result is a *single-weight* `Σ T2Wt(w)` fibration:
route A (`w ≤ z^{1/4}`, `d₂ := w`) + route B (`w > z^{1/4}` prime power, `d₂ := 1`), sifted at
`Zz` everywhere (amendment 3 — `v ≥ z ≥ Zz`, `Zf` would be unsound).  Budget
`≤ C·x·z₀³·e^{0.7z₀}·PS/L'`, absorbed by `Aexp = 5`.

## House amendments baked

* #245: family-local junk guard `T3FJunkBlock` on `w = (n+2)₋` (verbatim shape); sift at `Zz`.
* #246: the `Odd n` guard on the slice (excises the even-block corner from both sums).

## Reuse note (LOUD — a deviation from the literal import list)

The task's import list was `L2cELT3 + L2cEL`; this file ALSO imports the landed, frozen sibling
`Salt.HB.L2cELT2` to reuse its **generic** engine (`t2_count_kernel` is generic in `(d₁,d₂)`;
`t2_totient_ge`, `exp_absorption`, `t2_inv_logZz_sq`, `t2_wt_sum_le`, `T2Wt`, the `Zz`/scale
lemmas).  Importing a landed file is not editing it; no cycle is created (this file is a leaf).
The junk predicate is re-defined family-locally (`T3FJunkBlock`) per #245; W3 reconciles via a
trivial `iff`.  All new helpers are `t3f_`/`T3F`-prefixed (single-writer law extends to names).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — the junk guard, the guarded T3 slice, and its family sum -/

/-- **The T3 junk-block guard** (family-local per catch #245, verbatim shape): the small-base
    squarefull corner `m = p^e`, `p` prime `≤ Zz z`, `e ≥ 2`, `z^{1/4} < m`.  Excluded from the
    T3 slice — the junk row owns them (`J2` cannot absorb them). -/
def T3FJunkBlock (z m : ℕ) : Prop :=
  ∃ p e : ℕ, p.Prime ∧ p ≤ Zz z ∧ 2 ≤ e ∧ m = p ^ e ∧ (z : ℝ) ^ ((1 : ℝ) / 4) < (m : ℝ)

open Classical in
/-- **The guarded T3 slice** — the biprime support (`n₊`, `n₋` both prime, `z ≤ n₋`) with the
    house-mandated `Odd n` guard (#246) and the junk guard on `w = (n+2)₋` (#245). -/
noncomputable def T3FSet (χ : DirichletCharacter ℂ q) (z x : ℕ) : Finset ℕ :=
  (l2cWindow χ z x).filter (fun n =>
    (nPlus χ n).Prime ∧ (nMinus χ n).Prime ∧ z ≤ nMinus χ n ∧ Odd n ∧
      ¬ T3FJunkBlock z (nMinus χ (n + 2)))

/-- **The guarded T3 family sum.** -/
noncomputable def EL_T3F (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ T3FSet χ z x, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)

open Classical in
lemma T3FSet_subset_window (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    T3FSet χ z x ⊆ l2cWindow χ z x := Finset.filter_subset _ _

open Classical in
/-- Unpack membership in the guarded T3 slice. -/
lemma T3FSet_mem (χ : DirichletCharacter ℂ q) {z x m : ℕ} (hm : m ∈ T3FSet χ z x) :
    m ∈ l2cWindow χ z x ∧ (nPlus χ m).Prime ∧ (nMinus χ m).Prime ∧ z ≤ nMinus χ m ∧
      Odd m ∧ ¬ T3FJunkBlock z (nMinus χ (m + 2)) := by
  rw [T3FSet, Finset.mem_filter] at hm
  exact ⟨hm.1, hm.2⟩

open Classical in
/-- The `Odd n` guard in divisibility form. -/
lemma T3FSet_not_two_dvd (χ : DirichletCharacter ℂ q) {z x m : ℕ} (hm : m ∈ T3FSet χ z x) :
    ¬ 2 ∣ m := by
  have hodd := (T3FSet_mem χ hm).2.2.2.2.1
  rw [Nat.odd_iff] at hodd
  omega

/-! ## §1 — the exact biprime left factor and the per-summand cap

On the biprime support `(Λ̃−Λ)(n) = 2·Λ(n₋)` EXACTLY (the landed
`lamTilde_sub_eq_two_mul_of_biprime`), with NO `e^{z₀}` factor.  Crude-bounding `Λ(n₋) ≤ L'`
(the χ=−1 prime `n₋` is the fibration COFACTOR, not a summable coordinate) and capping
`Λ̃(n+2)` sharply gives the per-summand bound with the `T2Wt` weight on `w = (n+2)₋`. -/

/-- **The left-factor bound.**  On the biprime support, `(Λ̃−Λ)(n) ≤ 2·L'`. -/
lemma t3f_left_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (hP : (nPlus χ n).Prime) (hM : (nMinus χ n).Prime) :
    LamTilde χ n - Λ n ≤ 2 * Lwin x := by
  have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hn
  have hcop : Nat.Coprime n q := l2cWindow_coprime χ hn
  rw [lamTilde_sub_eq_two_mul_of_biprime χ hsq hn0 hcop hP hM]
  have hvpos : 0 < nMinus χ n := nMinus_pos χ n
  have hvdvd : nMinus χ n ∣ n :=
    ⟨nPlus χ n, by rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq hn0 hcop⟩
  have hvle : (nMinus χ n : ℝ) ≤ 2 * (x : ℝ) + 2 := by
    have h2 : nMinus χ n ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hvdvd
    have h3 : n ≤ 2 * x := l2cWindow_le χ hn
    have h4 : (nMinus χ n : ℝ) ≤ ((2 * x : ℕ) : ℝ) := by exact_mod_cast le_trans h2 h3
    push_cast at h4; linarith
  have hcap : Λ (nMinus χ n) ≤ Lwin x := by
    calc Λ (nMinus χ n) ≤ Real.log (nMinus χ n) := vonMangoldt_le_log
      _ ≤ Lwin x := by rw [Lwin]; exact Real.log_le_log (by exact_mod_cast hvpos) hvle
  linarith

/-- **The per-summand cap.**  On the biprime support,
    `(Λ̃−Λ)(n)·Λ̃(n+2) ≤ e^{(log2)z₀}·(2·L')·T2Wt(w)` (`w = (n+2)₋`; only ONE `e^{(log2)z₀}`). -/
lemma t3f_summand_cap (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ} (hz2 : 2 ≤ z)
    (hn : n ∈ l2cWindow χ z x) (hP : (nPlus χ n).Prime) (hM : (nMinus χ n).Prime) :
    (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ Real.exp (Real.log 2 * z0 z x) * (2 * Lwin x)
          * T2Wt x (nMinus χ (n + 2)) := by
  have hleft := t3f_left_le χ hsq hn hP hM
  have hright := t2_right_cap χ hsq hz2 hn
  have hLt0 : 0 ≤ LamTilde χ (n + 2) := lamTilde_nonneg χ hsq (n + 2)
  have h2L0 : (0 : ℝ) ≤ 2 * Lwin x := by have := Lwin_nonneg x; linarith
  calc (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ (2 * Lwin x) * LamTilde χ (n + 2) := mul_le_mul_of_nonneg_right hleft hLt0
    _ ≤ (2 * Lwin x) * (Real.exp (Real.log 2 * z0 z x) * T2Wt x (nMinus χ (n + 2))) :=
        mul_le_mul_of_nonneg_left hright h2L0
    _ = Real.exp (Real.log 2 * z0 z x) * (2 * Lwin x) * T2Wt x (nMinus χ (n + 2)) := by ring

/-! ## §2 — the T3 two-factor totient ratio and the fiber machinery

The modulus is `d₁ := P` (a single χ=+1 prime — the PS source), `d₂ := w` (route A) or `1`
(route B).  Both factors are odd; the totient ratio `(d/φ)² ≤ 729/64` holds with room (two
factors, each local ratio `≤ 3/2`, so `≤ (9/4)² = 81/16 ≤ 729/64`). -/

/-- **The T3 totient-ratio bound.**  `(P·w/φ(P·w))² ≤ 729/64` for `P` an odd prime, `w` odd
    (`1`-or-prime-power), coprime — the form `t2_count_kernel` consumes. -/
lemma t3f_totient_ratio {P w : ℕ} (hP : P.Prime) (hw : w = 1 ∨ IsPrimePow w)
    (hoP : ¬ 2 ∣ P) (how : ¬ 2 ∣ w) (hcop : Nat.Coprime P w) :
    ((P * w : ℝ) / (Nat.totient (P * w) : ℝ)) ^ 2 ≤ (729 / 64 : ℝ) := by
  have hPpos : 0 < P := hP.pos
  have hwpos : 0 < w := by
    rcases hw with rfl | h
    · omega
    · exact h.pos
  have htP := t2_totient_ge (Or.inr hP.isPrimePow) hoP
  have htw := t2_totient_ge hw how
  have hmul : Nat.totient (P * w) = Nat.totient P * Nat.totient w := Nat.totient_mul hcop
  have hphi : (4 / 9 : ℝ) * ((P : ℝ) * w) ≤ (Nat.totient (P * w) : ℝ) := by
    have h12 : ((2 / 3 : ℝ) * P) * ((2 / 3 : ℝ) * w)
        ≤ (Nat.totient P : ℝ) * (Nat.totient w : ℝ) :=
      mul_le_mul htP htw (by positivity) (Nat.cast_nonneg _)
    calc (4 / 9 : ℝ) * ((P : ℝ) * w)
        = ((2 / 3 : ℝ) * P) * ((2 / 3 : ℝ) * w) := by ring
      _ ≤ (Nat.totient P : ℝ) * (Nat.totient w : ℝ) := h12
      _ = (Nat.totient (P * w) : ℝ) := by rw [hmul, Nat.cast_mul]
  have hφpos : (0 : ℝ) < (Nat.totient (P * w) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by positivity)
  have hr : (P * w : ℝ) / (Nat.totient (P * w) : ℝ) ≤ 9 / 4 := by
    rw [div_le_iff₀ hφpos]; nlinarith [hphi]
  calc ((P * w : ℝ) / (Nat.totient (P * w) : ℝ)) ^ 2
      ≤ (9 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hr 2
    _ = (81 / 16 : ℝ) := by norm_num
    _ ≤ (729 / 64 : ℝ) := by norm_num

/-- Divisors of odd numbers are odd. -/
lemma t3f_odd_of_dvd {d m : ℕ} (hdm : d ∣ m) (hm : ¬ 2 ∣ m) : Odd d := by
  rcases Nat.even_or_odd d with he | ho
  · obtain ⟨t, rfl⟩ := he
    exact absurd (Dvd.dvd.trans ⟨t, by ring⟩ hdm) hm
  · exact ho

open Classical in
/-- **Route-A fiber subset.**  The `(w, P)`-fiber (`w ≤ z^{1/4}`) lands in the `Zz`-sifted base
    set at `(d₁, d₂) = (P, w)`: the `n`-cofactor is the χ=−1 prime `n₋ = v ≥ z`, the `n+2`
    cofactor is `(n+2)₊`, both `Zz`-rough (`v` prime `≥ z > Zz`; `(n+2)₊` by roughness). -/
lemma t3f_fiberA_subset (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (w P : ℕ) :
    ((T3FSet χ z x).filter (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => (nMinus χ (n + 2), nPlus χ n) = (w, P))
      ⊆ (baseSet x P w).filter
          (fun n => Nat.Coprime (primorial (Zz z)) ((n / P) * ((n + 2) / w))) := by
  intro m hm
  simp only [Finset.mem_filter] at hm
  obtain ⟨⟨hmT3, _hrouteA⟩, hkey⟩ := hm
  rw [Prod.mk.injEq] at hkey
  obtain ⟨hkw, hkP⟩ := hkey
  subst hkw; subst hkP
  obtain ⟨hwin, hP, hM, hzv, _hodd, _hguard⟩ := T3FSet_mem χ hmT3
  have hm0 : m ≠ 0 := l2cWindow_ne_zero χ hwin
  have hcopq : Nat.Coprime m q := l2cWindow_coprime χ hwin
  have hcopq2 : Nat.Coprime (m + 2) q := l2cWindow_coprime_add_two χ hwin
  have hfact : m = nPlus χ m * nMinus χ m := eq_nPlus_mul_nMinus χ hsq hm0 hcopq
  have hPdvd : nPlus χ m ∣ m := ⟨nMinus χ m, hfact⟩
  have hwdvd : nMinus χ (m + 2) ∣ m + 2 :=
    ⟨nPlus χ (m + 2), by rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩
  have hZzz : Zz z < z := Zz_lt_z (le_trans (by norm_num) hz100)
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [baseSet, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨l2cWindow_lt χ hwin, l2cWindow_le χ hwin⟩, hPdvd, hwdvd⟩
  · have hPpos : 0 < nPlus χ m := nPlus_pos χ m
    have hwpos : 0 < nMinus χ (m + 2) := nMinus_pos χ (m + 2)
    have hdiv1 : m / nPlus χ m = nMinus χ m :=
      Nat.div_eq_of_eq_mul_left hPpos (hfact.trans (mul_comm _ _))
    have hdiv2 : (m + 2) / nMinus χ (m + 2) = nPlus χ (m + 2) :=
      Nat.div_eq_of_eq_mul_left hwpos (eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2)
    rw [hdiv1, hdiv2]
    refine Nat.Coprime.mul_right (t2_coprime_primorial fun r hr hrdvd => ?_)
      (t2_coprime_primorial fun r hr hrdvd => ?_)
    · have hreq : r = nMinus χ m := (Nat.prime_dvd_prime_iff_eq hr hM).mp hrdvd
      omega
    · have hrsign : chiRe χ r = 1 := nPlus_dvd_sign hr hrdvd
      have hrn2 : r ∣ m + 2 :=
        hrdvd.trans ⟨nMinus χ (m + 2), eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩
      have hzr : z ≤ r := l2cWindow_rough_add_two χ hwin hr hrn2 (by rw [hrsign]; norm_num)
      omega

open Classical in
/-- **The route-A fiber count.**  Under the weight-structure hypothesis on `w` (and `P` prime),
    the `(w, P)`-fiber (`w ≤ z^{1/4}`) has `≤ 1458·(x/(P·w))/(log Zz)²` elements. -/
lemma t3f_fiberA_card (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) {w P : ℕ} (hw : w = 1 ∨ IsPrimePow w) (hP : P.Prime) :
    ((((T3FSet χ z x).filter
          (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => (nMinus χ (n + 2), nPlus χ n) = (w, P))).card : ℝ)
      ≤ 1458 * ((x : ℝ) / ((P : ℝ) * w)) / (Real.log (Zz z)) ^ 2 := by
  rcases Finset.eq_empty_or_nonempty ((((T3FSet χ z x).filter
      (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
      (fun n => (nMinus χ (n + 2), nPlus χ n) = (w, P)))) with he | ⟨n₀, hn₀⟩
  · rw [he]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  · simp only [Finset.mem_filter] at hn₀
    obtain ⟨⟨hn₀T3, hrouteA⟩, hkey⟩ := hn₀
    rw [Prod.mk.injEq] at hkey
    obtain ⟨hkw, hkP⟩ := hkey
    subst hkw; subst hkP
    obtain ⟨hwin, hPp, hMp, hzv, _hodd, _hguard⟩ := T3FSet_mem χ hn₀T3
    have hodd' : ¬ 2 ∣ n₀ := T3FSet_not_two_dvd χ hn₀T3
    have hm0 : n₀ ≠ 0 := l2cWindow_ne_zero χ hwin
    have hcopq : Nat.Coprime n₀ q := l2cWindow_coprime χ hwin
    have hcopq2 : Nat.Coprime (n₀ + 2) q := l2cWindow_coprime_add_two χ hwin
    have hodd2 : ¬ 2 ∣ (n₀ + 2) := by omega
    have hfact : n₀ = nPlus χ n₀ * nMinus χ n₀ := eq_nPlus_mul_nMinus χ hsq hm0 hcopq
    have hPdvd : nPlus χ n₀ ∣ n₀ := ⟨nMinus χ n₀, hfact⟩
    have hwdvd : nMinus χ (n₀ + 2) ∣ n₀ + 2 :=
      ⟨nPlus χ (n₀ + 2), by rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩
    have hPpos : 0 < nPlus χ n₀ := nPlus_pos χ n₀
    have hwpos : 0 < nMinus χ (n₀ + 2) := nMinus_pos χ (n₀ + 2)
    have ho1 : Odd (nPlus χ n₀) := t3f_odd_of_dvd hPdvd hodd'
    have ho2 : Odd (nMinus χ (n₀ + 2)) := t3f_odd_of_dvd hwdvd hodd2
    have hP2 : ¬ 2 ∣ nPlus χ n₀ := fun h => hodd' (h.trans hPdvd)
    have hw2 : ¬ 2 ∣ nMinus χ (n₀ + 2) := fun h => hodd2 (h.trans hwdvd)
    have hcop : Nat.Coprime (nPlus χ n₀) (nMinus χ (n₀ + 2)) := by
      by_contra hnc
      obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd hnc
      have h1 : r ∣ n₀ := (hrg.trans (Nat.gcd_dvd_left _ _)).trans hPdvd
      have h2 : r ∣ n₀ + 2 := (hrg.trans (Nat.gcd_dvd_right _ _)).trans hwdvd
      have h3 : r ∣ 2 := by
        have := Nat.dvd_sub h2 h1; rwa [Nat.add_sub_cancel_left] at this
      have hr2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h3
      exact hodd' (hr2 ▸ h1)
    have hratio := t3f_totient_ratio hPp hw hP2 hw2 hcop
    have hmod : ((nPlus χ n₀ : ℕ) : ℝ) * z ≤ 2 * x := by
      have hle : nPlus χ n₀ * z ≤ 2 * x := by
        calc nPlus χ n₀ * z ≤ nPlus χ n₀ * nMinus χ n₀ := Nat.mul_le_mul_left _ hzv
          _ = n₀ := hfact.symm
          _ ≤ 2 * x := l2cWindow_le χ hwin
      exact_mod_cast hle
    have hkernel := t2_count_kernel hz100 hPpos hwpos ho1 ho2 hcop hratio hmod hrouteA
    have hsub := t3f_fiberA_subset (x := x) χ hsq hz100 (nMinus χ (n₀ + 2)) (nPlus χ n₀)
    calc ((((T3FSet χ z x).filter
          (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
          (fun n => (nMinus χ (n + 2), nPlus χ n)
            = (nMinus χ (n₀ + 2), nPlus χ n₀))).card : ℝ)
        ≤ (((baseSet x (nPlus χ n₀) (nMinus χ (n₀ + 2))).filter
            (fun n => Nat.Coprime (primorial (Zz z))
              ((n / nPlus χ n₀) * ((n + 2) / nMinus χ (n₀ + 2))))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 1458 * ((x : ℝ) / ((nPlus χ n₀ : ℝ) * nMinus χ (n₀ + 2)))
            / (Real.log (Zz z)) ^ 2 := hkernel

open Classical in
/-- **Route-B fiber subset.**  On the cofactor route (`w > z^{1/4}`, `w` a prime power) the
    `P`-fiber lands in the `Zz`-sifted base set at `(d₁, d₂) = (P, 1)`: the whole cofactor
    `n = P·v` and `n+2` are `Zz`-rough (`v` prime `≥ z`; `(n+2)₊` by roughness; the block `w`
    because the junk guard + primality push its base above `Zz`). -/
lemma t3f_fiberB_subset (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (P : ℕ) :
    (((T3FSet χ z x).filter
          (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => IsPrimePow (nMinus χ (n + 2)))).filter (fun n => nPlus χ n = P)
      ⊆ (baseSet x P 1).filter
          (fun n => Nat.Coprime (primorial (Zz z)) ((n / P) * ((n + 2) / 1))) := by
  intro m hm
  simp only [Finset.mem_filter] at hm
  obtain ⟨⟨⟨hmT3, hrouteB⟩, hppw⟩, hkey⟩ := hm
  subst hkey
  obtain ⟨hwin, hPp, hMp, hzv, _hodd, hguard⟩ := T3FSet_mem χ hmT3
  have hm0 : m ≠ 0 := l2cWindow_ne_zero χ hwin
  have hcopq : Nat.Coprime m q := l2cWindow_coprime χ hwin
  have hcopq2 : Nat.Coprime (m + 2) q := l2cWindow_coprime_add_two χ hwin
  have hodd' : ¬ 2 ∣ m := T3FSet_not_two_dvd χ hmT3
  have hfact : m = nPlus χ m * nMinus χ m := eq_nPlus_mul_nMinus χ hsq hm0 hcopq
  have hPdvd : nPlus χ m ∣ m := ⟨nMinus χ m, hfact⟩
  have hZzz : Zz z < z := Zz_lt_z (le_trans (by norm_num) hz100)
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [baseSet, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨l2cWindow_lt χ hwin, l2cWindow_le χ hwin⟩, hPdvd, one_dvd _⟩
  · have hPpos : 0 < nPlus χ m := nPlus_pos χ m
    have hdiv1 : m / nPlus χ m = nMinus χ m :=
      Nat.div_eq_of_eq_mul_left hPpos (hfact.trans (mul_comm _ _))
    rw [hdiv1, Nat.div_one]
    refine Nat.Coprime.mul_right (t2_coprime_primorial fun r hr hrdvd => ?_)
      (t2_coprime_primorial fun r hr hrdvd => ?_)
    · have hreq : r = nMinus χ m := (Nat.prime_dvd_prime_iff_eq hr hMp).mp hrdvd
      omega
    · have hsplit := eq_nPlus_mul_nMinus χ hsq (show m + 2 ≠ 0 by omega) hcopq2
      have hrPw : r ∣ nPlus χ (m + 2) * nMinus χ (m + 2) := hsplit ▸ hrdvd
      rcases hr.dvd_mul.mp hrPw with hrP | hrw
      · have hrsign : chiRe χ r = 1 := nPlus_dvd_sign hr hrP
        have hrm2 : r ∣ m + 2 :=
          hrP.trans ⟨nMinus χ (m + 2), eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩
        have hzr : z ≤ r := l2cWindow_rough_add_two χ hwin hr hrm2 (by rw [hrsign]; norm_num)
        omega
      · obtain ⟨s, k, hs, hk, hsk⟩ := (isPrimePow_nat_iff _).mp hppw
        rw [← hsk] at hrw
        have hrs : r = s := (Nat.prime_dvd_prime_iff_eq hr hs).mp (hr.dvd_of_dvd_pow hrw)
        have hs_gt : Zz z < s := by
          rcases eq_or_lt_of_le (show 1 ≤ k by omega) with hk1 | hk2
          · have hws : nMinus χ (m + 2) = s := by rw [← hsk, ← hk1, pow_one]
            have hwR : (z : ℝ) ^ ((1 : ℝ) / 4) < (nMinus χ (m + 2) : ℝ) := not_le.mp hrouteB
            have hZzR : (Zz z : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) :=
              Zz_le_quarter (le_trans (by norm_num) hz100)
            have hlt : (Zz z : ℝ) < (s : ℝ) := by rw [← hws]; exact lt_of_le_of_lt hZzR hwR
            exact_mod_cast hlt
          · rcases Nat.lt_or_ge (Zz z) s with hgt | hle
            · exact hgt
            · exact absurd ⟨s, k, hs, hle, by omega, hsk.symm, not_le.mp hrouteB⟩ hguard
        rw [hrs]; exact hs_gt

open Classical in
/-- **The route-B fiber count.**  The `P`-fiber of the cofactor route (`w > z^{1/4}`, prime
    power) has `≤ 1458·(x/P)/(log Zz)²` elements. -/
lemma t3f_fiberB_card (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (P : ℕ) :
    (((((T3FSet χ z x).filter
          (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => IsPrimePow (nMinus χ (n + 2)))).filter (fun n => nPlus χ n = P)).card : ℝ)
      ≤ 1458 * ((x : ℝ) / P) / (Real.log (Zz z)) ^ 2 := by
  rcases Finset.eq_empty_or_nonempty (((((T3FSet χ z x).filter
      (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
      (fun n => IsPrimePow (nMinus χ (n + 2)))).filter (fun n => nPlus χ n = P)))
    with he | ⟨n₀, hn₀⟩
  · rw [he]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  · simp only [Finset.mem_filter] at hn₀
    obtain ⟨⟨⟨hn₀T3, _⟩, _⟩, hkey⟩ := hn₀
    subst hkey
    obtain ⟨hwin, hPp, hMp, hzv, _hodd, _hguard⟩ := T3FSet_mem χ hn₀T3
    have hodd' : ¬ 2 ∣ n₀ := T3FSet_not_two_dvd χ hn₀T3
    have hm0 : n₀ ≠ 0 := l2cWindow_ne_zero χ hwin
    have hcopq : Nat.Coprime n₀ q := l2cWindow_coprime χ hwin
    have hfact : n₀ = nPlus χ n₀ * nMinus χ n₀ := eq_nPlus_mul_nMinus χ hsq hm0 hcopq
    have hPdvd : nPlus χ n₀ ∣ n₀ := ⟨nMinus χ n₀, hfact⟩
    have hPpos : 0 < nPlus χ n₀ := nPlus_pos χ n₀
    have ho1 : Odd (nPlus χ n₀) := t3f_odd_of_dvd hPdvd hodd'
    have hP2 : ¬ 2 ∣ nPlus χ n₀ := fun h => hodd' (h.trans hPdvd)
    have hcop1 : Nat.Coprime (nPlus χ n₀) 1 := Nat.coprime_one_right _
    have hratio := t3f_totient_ratio hPp (Or.inl rfl) hP2 (by norm_num) hcop1
    have hmod : ((nPlus χ n₀ : ℕ) : ℝ) * z ≤ 2 * x := by
      have hle : nPlus χ n₀ * z ≤ 2 * x := by
        calc nPlus χ n₀ * z ≤ nPlus χ n₀ * nMinus χ n₀ := Nat.mul_le_mul_left _ hzv
          _ = n₀ := hfact.symm
          _ ≤ 2 * x := l2cWindow_le χ hwin
      exact_mod_cast hle
    have hone : ((1 : ℕ) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [Nat.cast_one]
      calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 4) := (Real.one_rpow _).symm
        _ ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by norm_num)
            (by exact_mod_cast le_trans (by norm_num : 1 ≤ 100 ^ 16) hz100) (by norm_num)
    have hkernel := t2_count_kernel hz100 hPpos (by omega : 0 < 1) ho1 odd_one hcop1
      hratio hmod hone
    have hsub := t3f_fiberB_subset (x := x) χ hsq hz100 (nPlus χ n₀)
    calc (((((T3FSet χ z x).filter
          (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => IsPrimePow (nMinus χ (n + 2)))).filter
          (fun n => nPlus χ n = nPlus χ n₀)).card : ℝ)
        ≤ (((baseSet x (nPlus χ n₀) 1).filter
            (fun n => Nat.Coprime (primorial (Zz z))
              ((n / nPlus χ n₀) * ((n + 2) / 1)))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 1458 * ((x : ℝ) / ((nPlus χ n₀ : ℝ) * ((1 : ℕ) : ℝ))) / (Real.log (Zz z)) ^ 2 :=
          hkernel
      _ = 1458 * ((x : ℝ) / (nPlus χ n₀ : ℝ)) / (Real.log (Zz z)) ^ 2 := by
          rw [Nat.cast_one, mul_one]

/-! ## §3 — the two route sums

The `Σ_n T2Wt(w)` fibration.  Route A (`w ≤ z^{1/4}`, `d₂ := w`) fibers over `(w, P)` and prices
`Σ_w T2Wt(w)/w ≤ 3L'` (Mertens) × `Σ_P 1/P ≤ z₀·PS/L'` (`P` the χ=+1 modulus/PS source).
Route B (`w > z^{1/4}`, prime-power `w`, `d₂ := 1`) crude-caps `T2Wt(w) ≤ L'` and fibers over
`P`.  Both give the `x·z₀³·PS/L'²` shape (the master multiplies by `2L'·e^{(log2)z₀}`). -/

open Classical in
/-- **The route-A sum.**  `≤ 4478976·x·z₀³·PS/L'²`. -/
lemma t3f_routeA_sum (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ (T3FSet χ z x).filter
        (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
      T2Wt x (nMinus χ (n + 2))
      ≤ 4478976 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / (Lwin x) ^ 2 := by
  have hL : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hmaps : ∀ n ∈ (T3FSet χ z x).filter
      (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
      (nMinus χ (n + 2), nPlus χ n)
        ∈ (Finset.range (2 * x + 3)) ×ˢ ((Finset.range (2 * x + 3)).filter
            (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p)) := by
    intro n hn
    have hnT3 : n ∈ T3FSet χ z x := Finset.mem_of_mem_filter n hn
    obtain ⟨hwin, hPp, hMp, hzv, _hodd, _hguard⟩ := T3FSet_mem χ hnT3
    have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hwin
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnle : n ≤ 2 * x := l2cWindow_le χ hwin
    have hcopq : Nat.Coprime n q := l2cWindow_coprime χ hwin
    have hcopq2 : Nat.Coprime (n + 2) q := l2cWindow_coprime_add_two χ hwin
    have hPdvd : nPlus χ n ∣ n := ⟨nMinus χ n, eq_nPlus_mul_nMinus χ hsq hn0 hcopq⟩
    have hwdvd : nMinus χ (n + 2) ∣ n + 2 :=
      ⟨nPlus χ (n + 2), by rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩
    have hPle : nPlus χ n ≤ n := Nat.le_of_dvd hnpos hPdvd
    have hwle : nMinus χ (n + 2) ≤ n + 2 := Nat.le_of_dvd (by omega) hwdvd
    have hPsign : chiRe χ (nPlus χ n) = 1 := nPlus_dvd_sign hPp (dvd_refl _)
    have hzP : z ≤ nPlus χ n := l2cWindow_rough χ hwin hPp hPdvd (by rw [hPsign]; norm_num)
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_filter]
    exact ⟨by omega, by omega, hPp, hPsign, hzP⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => T2Wt x (nMinus χ (n + 2)))]
  have hperk : ∀ k ∈ (Finset.range (2 * x + 3)) ×ˢ ((Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p)),
      (∑ n ∈ ((T3FSet χ z x).filter
          (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
          (fun n => (nMinus χ (n + 2), nPlus χ n) = k),
        T2Wt x (nMinus χ (n + 2)))
      ≤ (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2)
          * ((T2Wt x k.1 / k.1) * (1 / k.2)) := by
    intro k hk
    obtain ⟨w, P⟩ := k
    have hPmem : P ∈ (Finset.range (2 * x + 3)).filter
        (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p) := (Finset.mem_product.mp hk).2
    have hP : P.Prime := (Finset.mem_filter.mp hPmem).2.1
    have hconst : ∀ n ∈ ((T3FSet χ z x).filter
        (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => (nMinus χ (n + 2), nPlus χ n) = (w, P)),
        T2Wt x (nMinus χ (n + 2)) = T2Wt x w := by
      intro n hn
      have hk' := (Finset.mem_filter.mp hn).2
      rw [Prod.mk.injEq] at hk'
      rw [hk'.1]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    by_cases hWw : T2Wt x w = 0
    · simp [hWw]
    have hw : w = 1 ∨ IsPrimePow w := by
      rcases eq_or_ne w 1 with h1 | h1
      · exact Or.inl h1
      · refine Or.inr (by_contra fun hnp => hWw ?_)
        rw [T2Wt, if_neg h1]; exact vonMangoldt_eq_zero_iff.mpr hnp
    have hcard := t3f_fiberA_card (x := x) χ hsq hz100 hw hP
    have hWnn : (0 : ℝ) ≤ T2Wt x w := T2Wt_nonneg x w
    have hconv := t2_inv_logZz_sq hz100 hzx
    have hfac : (0 : ℝ) ≤ 1458 * (x : ℝ) * T2Wt x w / ((P : ℝ) * w) := by
      apply div_nonneg _ (by positivity)
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg x)) hWnn
    calc ((((T3FSet χ z x).filter
          (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
          (fun n => (nMinus χ (n + 2), nPlus χ n) = (w, P))).card : ℝ) * T2Wt x w
        ≤ (1458 * ((x : ℝ) / ((P : ℝ) * w)) / (Real.log (Zz z)) ^ 2) * T2Wt x w :=
          mul_le_mul_of_nonneg_right hcard hWnn
      _ = (1458 * (x : ℝ) * T2Wt x w / ((P : ℝ) * w)) * (1 / (Real.log (Zz z)) ^ 2) := by ring
      _ ≤ (1458 * (x : ℝ) * T2Wt x w / ((P : ℝ) * w)) * (1024 * (z0 z x / Lwin x) ^ 2) :=
          mul_le_mul_of_nonneg_left hconv hfac
      _ = (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * ((T2Wt x w / w) * (1 / P)) := by
          ring
  refine le_trans (Finset.sum_le_sum hperk) ?_
  have hfactor : ∑ k ∈ (Finset.range (2 * x + 3)) ×ˢ ((Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p)),
      (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * ((T2Wt x k.1 / k.1) * (1 / k.2))
      = (∑ w ∈ Finset.range (2 * x + 3),
          (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x w / w))
        * (∑ p ∈ (Finset.range (2 * x + 3)).filter
            (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p) := by
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_product]
    refine Finset.sum_congr rfl fun w _ => ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hfactor]
  have hz1' : 1 < z := lt_of_lt_of_le (by norm_num) hz100
  have hh : ∑ w ∈ Finset.range (2 * x + 3), T2Wt x w / w ≤ 3 * Lwin x := by
    have := t2_wt_sum_le (N := 2 * x + 2) hz100 hzx (by omega) (by omega)
    simpa using this
  have hp : ∑ p ∈ (Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p
      ≤ PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x) := by
    have hps := sum_inv_plusprime_le_pretense χ z (2 * x + 2) hz1'
    have hconv : PretenseSum χ (2 * x + 2) / Real.log z
        = PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x) := by
      rw [div_eq_mul_one_div, t2_inv_log_z hz100 hzx]
    rw [← hconv]; exact hps
  have hSp0 : (0 : ℝ) ≤ ∑ p ∈ (Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p :=
    Finset.sum_nonneg fun p _ => by positivity
  have hL0 : Lwin x ≠ 0 := by linarith
  have hC0 : (0 : ℝ) ≤ 1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2 := by positivity
  have hgC : ∑ w ∈ Finset.range (2 * x + 3),
        (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x w / w)
      ≤ (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (3 * Lwin x) := by
    rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hh hC0
  calc (∑ w ∈ Finset.range (2 * x + 3),
        (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x w / w))
        * (∑ p ∈ (Finset.range (2 * x + 3)).filter
            (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p)
      ≤ ((1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (3 * Lwin x))
          * (PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x)) :=
        mul_le_mul hgC hp hSp0 (mul_nonneg hC0 (by linarith))
    _ = 4478976 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / (Lwin x) ^ 2 := by
        field_simp; ring

open Classical in
/-- **The route-B sum.**  Cofactor route (`w > z^{1/4}`): the vanishing reduction to prime-power
    `w`, the crude `L'` cap on the `w`-weight, and the `P`-fibration: `≤ 1492992·x·z₀³·PS/L'²`. -/
lemma t3f_routeB_sum (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ (T3FSet χ z x).filter
        (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
      T2Wt x (nMinus χ (n + 2))
      ≤ 1492992 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / (Lwin x) ^ 2 := by
  have hL : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hz14 : (1 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 4) := (Real.one_rpow _).symm
      _ ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by norm_num)
          (by exact_mod_cast le_trans (by norm_num : 1 ≤ 100 ^ 16) hz100) (by norm_num)
  have hvanish : ∀ n ∈ (T3FSet χ z x).filter
      (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
      T2Wt x (nMinus χ (n + 2)) ≠ 0 → IsPrimePow (nMinus χ (n + 2)) := by
    intro n hn hne
    have hB : ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := (Finset.mem_filter.mp hn).2
    have hne1 : nMinus χ (n + 2) ≠ 1 := by
      rintro h1; exact hB (by rw [h1, Nat.cast_one]; exact hz14)
    rw [T2Wt, if_neg hne1] at hne
    by_contra hnp
    exact hne (vonMangoldt_eq_zero_iff.mpr hnp)
  rw [← Finset.sum_filter_of_ne hvanish]
  have hcapw : ∀ n ∈ ((T3FSet χ z x).filter
      (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
      (fun n => IsPrimePow (nMinus χ (n + 2))),
      T2Wt x (nMinus χ (n + 2)) ≤ Lwin x := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnSB, _hppw⟩ := hn
    have hB : ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := (Finset.mem_filter.mp hnSB).2
    have hnT3 : n ∈ T3FSet χ z x := Finset.mem_of_mem_filter n hnSB
    obtain ⟨hwin, _, _, _, _, _⟩ := T3FSet_mem χ hnT3
    have hcopq2 : Nat.Coprime (n + 2) q := l2cWindow_coprime_add_two χ hwin
    have hne1 : nMinus χ (n + 2) ≠ 1 := by
      rintro h1; exact hB (by rw [h1, Nat.cast_one]; exact hz14)
    have hwle : nMinus χ (n + 2) ≤ 2 * x + 2 :=
      le_trans (Nat.le_of_dvd (by omega)
        ⟨nPlus χ (n + 2), by rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩)
        (l2cWindow_add_two_le χ hwin)
    rw [T2Wt, if_neg hne1]
    calc Λ (nMinus χ (n + 2)) ≤ Real.log (nMinus χ (n + 2)) := vonMangoldt_le_log
      _ ≤ Lwin x := by
          rw [Lwin]
          exact Real.log_le_log (by exact_mod_cast nMinus_pos χ (n + 2)) (by exact_mod_cast hwle)
  refine le_trans (Finset.sum_le_sum hcapw) ?_
  have hmaps : ∀ n ∈ ((T3FSet χ z x).filter
      (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
      (fun n => IsPrimePow (nMinus χ (n + 2))),
      nPlus χ n ∈ (Finset.range (2 * x + 3)).filter
          (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p) := by
    intro n hn
    have hnT3 : n ∈ T3FSet χ z x :=
      Finset.mem_of_mem_filter n (Finset.mem_of_mem_filter n hn)
    obtain ⟨hwin, hPp, hMp, hzv, _hodd, _hguard⟩ := T3FSet_mem χ hnT3
    have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hwin
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnle : n ≤ 2 * x := l2cWindow_le χ hwin
    have hcopq : Nat.Coprime n q := l2cWindow_coprime χ hwin
    have hPdvd : nPlus χ n ∣ n := ⟨nMinus χ n, eq_nPlus_mul_nMinus χ hsq hn0 hcopq⟩
    have hPle : nPlus χ n ≤ n := Nat.le_of_dvd hnpos hPdvd
    have hPsign : chiRe χ (nPlus χ n) = 1 := nPlus_dvd_sign hPp (dvd_refl _)
    have hzP : z ≤ nPlus χ n := l2cWindow_rough χ hwin hPp hPdvd (by rw [hPsign]; norm_num)
    simp only [Finset.mem_range, Finset.mem_filter]
    exact ⟨by omega, hPp, hPsign, hzP⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun _ => Lwin x)]
  have hperk : ∀ P ∈ (Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p),
      (∑ _n ∈ (((T3FSet χ z x).filter
          (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
          (fun n => IsPrimePow (nMinus χ (n + 2)))).filter (fun n => nPlus χ n = P),
        Lwin x)
      ≤ (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2 * Lwin x) * (1 / P) := by
    intro P hPmem
    have hP : P.Prime := (Finset.mem_filter.mp hPmem).2.1
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard := t3f_fiberB_card (x := x) χ hsq hz100 P
    have hconv := t2_inv_logZz_sq hz100 hzx
    have hLnn : (0 : ℝ) ≤ Lwin x := Lwin_nonneg x
    have hfac : (0 : ℝ) ≤ 1458 * (x : ℝ) * Lwin x / P := by
      apply div_nonneg _ (Nat.cast_nonneg P)
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg x)) hLnn
    calc ((((((T3FSet χ z x).filter
          (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
          (fun n => IsPrimePow (nMinus χ (n + 2)))).filter
          (fun n => nPlus χ n = P)).card : ℝ)) * Lwin x
        ≤ (1458 * ((x : ℝ) / P) / (Real.log (Zz z)) ^ 2) * Lwin x :=
          mul_le_mul_of_nonneg_right hcard hLnn
      _ = (1458 * (x : ℝ) * Lwin x / P) * (1 / (Real.log (Zz z)) ^ 2) := by ring
      _ ≤ (1458 * (x : ℝ) * Lwin x / P) * (1024 * (z0 z x / Lwin x) ^ 2) :=
          mul_le_mul_of_nonneg_left hconv hfac
      _ = (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2 * Lwin x) * (1 / P) := by ring
  refine le_trans (Finset.sum_le_sum hperk) ?_
  rw [← Finset.mul_sum]
  have hz1' : 1 < z := lt_of_lt_of_le (by norm_num) hz100
  have hp : ∑ p ∈ (Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p
      ≤ PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x) := by
    have hps := sum_inv_plusprime_le_pretense χ z (2 * x + 2) hz1'
    have hconv : PretenseSum χ (2 * x + 2) / Real.log z
        = PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x) := by
      rw [div_eq_mul_one_div, t2_inv_log_z hz100 hzx]
    rw [← hconv]; exact hps
  have hC0 : (0 : ℝ) ≤ 1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2 * Lwin x := by
    have := Lwin_nonneg x; positivity
  have hL0 : Lwin x ≠ 0 := by linarith
  calc (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2 * Lwin x)
        * (∑ p ∈ (Finset.range (2 * x + 3)).filter
            (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p)
      ≤ (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2 * Lwin x)
          * (PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x)) :=
        mul_le_mul_of_nonneg_left hp hC0
    _ = 1492992 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / (Lwin x) ^ 2 := by
        field_simp; ring

/-! ## §4 — the frozen guarded T3 family budget -/

open Classical in
/-- **The guarded T3 family budget** (the frozen `EL_T3F_bound`; the `J2` `PretenseSum` row;
    house amendments #245/#246 baked).  Over the guarded T3 slice (`n₊`, `n₋` both prime with
    `z ≤ n₋`, `n` odd, junk guard on `(n+2)₋`), under the master hypothesis packet:

    `E_L^{T3F} ≤ Cmain·(x/L')·e^{5z₀}·PS(2x+2)`,  `Cmain = 11943936` absolute.

    Route A (`w ≤ z^{1/4}`) + route B (`w > z^{1/4}`) price `Σ_n T2Wt(w) ≤ 5971968·x·z₀³·PS/L'²`;
    the EXACT biprime left factor `2·Λ(v) ≤ 2L'` and the sharp `n+2` cap give the `2L'·e^{(log2)z₀}`
    multiplier (only ONE `e^{(log2)z₀}` — the freeze's T3 `e^{0.7z₀}`); the `Aexp = 5` budget
    absorbs `z₀³·e^{(log2)z₀} ≤ e^{5z₀}` (`exp_absorption`). -/
theorem EL_T3F_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : (Lwin x) ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    EL_T3F χ z x
      ≤ 11943936 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by
  have _ := hz8
  have hL : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hPS0 : 0 ≤ PretenseSum χ (2 * x + 2) := t2_pretenseSum_nonneg χ _
  have hL0 : Lwin x ≠ 0 := by linarith
  have hcap : EL_T3F χ z x
      ≤ Real.exp (Real.log 2 * z0 z x) * (2 * Lwin x)
          * ∑ n ∈ T3FSet χ z x, T2Wt x (nMinus χ (n + 2)) := by
    rw [EL_T3F, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hmem := T3FSet_mem χ hn
    exact t3f_summand_cap χ hsq hz2 hmem.1 hmem.2.1 hmem.2.2.1
  have hsplit : ∑ n ∈ T3FSet χ z x, T2Wt x (nMinus χ (n + 2))
      = (∑ n ∈ (T3FSet χ z x).filter
            (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
          T2Wt x (nMinus χ (n + 2)))
        + ∑ n ∈ (T3FSet χ z x).filter
            (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
          T2Wt x (nMinus χ (n + 2)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hmain : ∑ n ∈ T3FSet χ z x, T2Wt x (nMinus χ (n + 2))
      ≤ 5971968 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / (Lwin x) ^ 2 := by
    rw [hsplit]
    refine le_trans (add_le_add (t3f_routeA_sum χ hsq hz100 hzx)
      (t3f_routeB_sum χ hsq hz100 hzx)) (le_of_eq ?_)
    ring
  have h2Lnn : (0 : ℝ) ≤ Real.exp (Real.log 2 * z0 z x) * (2 * Lwin x) :=
    mul_nonneg (Real.exp_pos _).le (by linarith)
  have hxLPS0 : (0 : ℝ) ≤ 11943936 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2) := by
    have hxL : (0 : ℝ) ≤ (x : ℝ) / Lwin x := div_nonneg (Nat.cast_nonneg x) (by linarith)
    positivity
  calc EL_T3F χ z x
      ≤ Real.exp (Real.log 2 * z0 z x) * (2 * Lwin x)
          * ∑ n ∈ T3FSet χ z x, T2Wt x (nMinus χ (n + 2)) := hcap
    _ ≤ Real.exp (Real.log 2 * z0 z x) * (2 * Lwin x)
          * (5971968 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / (Lwin x) ^ 2) :=
        mul_le_mul_of_nonneg_left hmain h2Lnn
    _ = 11943936 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2)
          * ((z0 z x) ^ 3 * Real.exp (Real.log 2 * z0 z x)) := by field_simp; ring
    _ ≤ 11943936 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2) * Real.exp (5 * z0 z x) := by
        refine mul_le_mul_of_nonneg_left ?_ hxLPS0
        calc (z0 z x) ^ 3 * Real.exp (Real.log 2 * z0 z x)
            ≤ (z0 z x) ^ 3 * Real.exp (2 * Real.log 2 * z0 z x) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
                (pow_nonneg (z0_nonneg (x := x) hz2) 3)
              have hz0 := z0_nonneg (x := x) hz2
              have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
              nlinarith [mul_nonneg hl2 hz0]
          _ ≤ Real.exp (5 * z0 z x) := exp_absorption hz2
    _ = 11943936 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2) := by
        ring

end Salt.HB
