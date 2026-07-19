/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cEL

/-!
# HB-L2c — the T2 family budget (node HB-L2c-F-T2, Horn A keystone)

This file is the single writer of the **T2 family budget** `EL_T2_bound` — the `J2`
`PretenseSum` row of the left-overshoot family analysis (freeze §S4, target shape recorded
as a named residual in `Salt.HB.L2cEL` §5 NOTES).

The T2 family is the sub-sum of `E_L = Σ_{n∈W} (Λ̃−Λ)(n)·Λ̃(n+2)` over window elements `n`
whose all-plus part `n₊ := nPlus χ n` is **composite**.  On this family the freeze's
REPAIRED modulus law applies: with `p' := minFac n₊` (a `χ=+1` prime, since every prime of
`n₊` has `chiRe = +1`) and `c := n₊ / p'`, one has `c ≥ z` (every prime of `c` is `≥ z` by
window roughness, and `c > 1` as `n₊` is composite), hence the `n`-side modulus
`d₁ := v·p' = n/c ≤ 2x/z` (`v := n₋`).  The `n+2` block `w := (n+2)₋` is routed at `z^{1/4}`.
The `χ=+1` prime `p'` pays the `PretenseSum` factor via `Σ 1/p' ≤ z₀·PS/L'`, and the fiber
count is `l2c_pair_count_clean`.  The frozen conclusion:

`EL_T2 χ z x ≤ Cmain·(x / Lwin x)·exp(5·z₀ z x)·PretenseSum χ (2x+2)`  (the `J2` row),

with `Cmain` an explicit absolute constant.

Single-writer file (`L2cELT2.lean`); it imports the frozen surfaces `Salt.HB.L2cEL` /
`Salt.HB.L2cCore` and touches no other file (`Salt.HB.All` is Wave 3's manifest).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — the junk-block guard, the T2 family sum, and its nonnegativity

The T2 family is the sub-sum of `E_L = Σ_{n∈W} (Λ̃−Λ)(n)·Λ̃(n+2)` over **odd** window
elements `n` whose all-plus part `n₊ := nPlus χ n` is composite, carrying the HOUSE-mandated
inline guard (catch #245 amendment 1) excluding the junk blocks on `w := nMinus χ (n+2)` —
the small-base squarefull corner shapes `w = p^e`, `p ≤ Zz z`, `e ≥ 2`, `z^{1/4} < w`, which
the junk row prices (`J2` provably cannot absorb them).  The parity condition is the
freeze's own partition: the even-block class (`chiRe χ 2 = −1` with both blocks 2-powers)
belongs to the `EL_corners_bound` e-split row, and `Odd d₁, Odd d₂` are structural
hypotheses of the pair-count engine.  Inside the proof `w` routes at `z^{1/4}`: `w ≤ z^{1/4}`
into the modulus (`d₂ := w`), `w > z^{1/4}` into the sifted cofactor (`d₂ := 1`; the guard
plus primality force the base of `w` above `Zz`, per amendment 3 the sift floor is `Zz`). -/

/-- **The T2 junk-block guard** (family-local per catch #245 amendment 1): the small-base
    squarefull corner shape `m = p^e`, `p` prime `≤ Zz z`, `e ≥ 2`, `z^{1/4} < m`.  These
    are excluded from the T2 slice; the junk row owns them. -/
def T2JunkBlock (z m : ℕ) : Prop :=
  ∃ p e : ℕ, p.Prime ∧ p ≤ Zz z ∧ 2 ≤ e ∧ m = p ^ e ∧ (z : ℝ) ^ ((1 : ℝ) / 4) < (m : ℝ)

open Classical in
/-- **The T2 slice** — the odd window elements with `n₊` composite, carrying the inline
    junk guard on `w = (n+2)₋`. -/
noncomputable def T2Set (χ : DirichletCharacter ℂ q) (z x : ℕ) : Finset ℕ :=
  (l2cWindow χ z x).filter (fun n =>
    Odd n ∧ 1 < nPlus χ n ∧ ¬ (nPlus χ n).Prime ∧ ¬ T2JunkBlock z (nMinus χ (n + 2)))

open Classical in
lemma T2Set_subset_window (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    T2Set χ z x ⊆ l2cWindow χ z x := Finset.filter_subset _ _

/-- **The T2 family sum** — `n` odd, `n₊` composite, `w := (n+2)₋` not a junk block. -/
noncomputable def EL_T2 (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ T2Set χ z x, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)

/-- `E_L^{T2} ≥ 0` (each summand `≥ 0` by Lemma 1(b)). -/
lemma EL_T2_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) :
    0 ≤ EL_T2 χ z x := by
  rw [EL_T2]; exact Finset.sum_nonneg fun n _ => EL_summand_nonneg χ hsq n

/-! ## §1 — the REPAIRED modulus law (freeze §S4 T2)

The heart of the T2 family: with `p' := minFac n₊` (a `χ=+1` prime, since every prime of the
all-plus part `n₊` has `chiRe = +1`) and `c := n₊ / p'`, one has `c ≥ z` (any prime of `c`
divides `n₊ ∣ n` and is `χ ≠ −1`, hence `≥ z` by window roughness, and `c > 1` as `n₊` is
composite), whence the `n`-side modulus `d₁ := v·p' = n/c` satisfies `d₁·z ≤ n ≤ 2x`, i.e.
`d₁ ≤ 2x/z`.  This is the frozen "REPAIRED law d₁ = n/c ≤ 2x/z via ≥ z cofactor". -/

/-- **The T2 REPAIRED modulus law.**  For a window element `n` with `n₊` composite there is a
    `χ=+1` prime `p'` and a cofactor `c ≥ z` with `p' ≥ z`, `c·(n₋·p') = n`, and
    `(n₋·p')·z ≤ 2x` (the modulus `d₁ := n₋·p' = n/c ≤ 2x/z). -/
lemma t2_modulus_law (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (hn1 : 1 < nPlus χ n) (hcomp : ¬ (nPlus χ n).Prime) :
    ∃ p' c : ℕ, p' = (nPlus χ n).minFac ∧ p'.Prime ∧ chiRe χ p' = 1 ∧ z ≤ p' ∧ z ≤ c ∧
      c ∣ nPlus χ n ∧ c * (nMinus χ n * p') = n ∧ (nMinus χ n * p') * z ≤ 2 * x := by
  have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hn
  have hcop : Nat.Coprime n q := l2cWindow_coprime χ hn
  have hfact : n = nPlus χ n * nMinus χ n := eq_nPlus_mul_nMinus χ hsq hn0 hcop
  have hnP0 : nPlus χ n ≠ 0 := (nPlus_pos χ n).ne'
  have hnP1 : nPlus χ n ≠ 1 := by omega
  have hPdvdn : nPlus χ n ∣ n := ⟨nMinus χ n, hfact⟩
  set p' := (nPlus χ n).minFac with hp'def
  have hp'prime : p'.Prime := Nat.minFac_prime hnP1
  have hp'dvdP : p' ∣ nPlus χ n := Nat.minFac_dvd _
  have hp'dvdn : p' ∣ n := hp'dvdP.trans hPdvdn
  have hp'mem : p' ∈ (nPlus χ n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp'prime, hp'dvdP, hnP0⟩
  have hp'sign : chiRe χ p' = 1 := nPlus_sign hp'mem
  have hzp' : z ≤ p' := l2cWindow_rough χ hn hp'prime hp'dvdn (by rw [hp'sign]; norm_num)
  set c := nPlus χ n / p' with hcdef
  have hpc : p' * c = nPlus χ n := by rw [hcdef]; exact Nat.mul_div_cancel' hp'dvdP
  clear_value c
  have hc2 : 2 ≤ c := by
    by_contra hcon
    have hcc : c = 0 ∨ c = 1 := by omega
    rcases hcc with h0 | h1
    · rw [h0, mul_zero] at hpc; exact hnP0 hpc.symm
    · rw [h1, mul_one] at hpc; exact hcomp (hpc ▸ hp'prime)
  have hcne1 : c ≠ 1 := by omega
  obtain ⟨r, hr, hrc⟩ := Nat.exists_prime_and_dvd hcne1
  have hcdvdP : c ∣ nPlus χ n := ⟨p', by rw [mul_comm]; exact hpc.symm⟩
  have hrdvdP : r ∣ nPlus χ n := hrc.trans hcdvdP
  have hrmem : r ∈ (nPlus χ n).primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrdvdP, hnP0⟩
  have hrsign : chiRe χ r = 1 := nPlus_sign hrmem
  have hrdvdn : r ∣ n := hrdvdP.trans hPdvdn
  have hzr : z ≤ r := l2cWindow_rough χ hn hr hrdvdn (by rw [hrsign]; norm_num)
  have hzc : z ≤ c := le_trans hzr (Nat.le_of_dvd (by omega) hrc)
  have hcprod : c * (nMinus χ n * p') = n := by
    calc c * (nMinus χ n * p') = (p' * c) * nMinus χ n := by ring
      _ = nPlus χ n * nMinus χ n := by rw [hpc]
      _ = n := hfact.symm
  refine ⟨p', c, hp'def, hp'prime, hp'sign, hzp', hzc, hcdvdP, hcprod, ?_⟩
  have hnle : n ≤ 2 * x := l2cWindow_le χ hn
  calc (nMinus χ n * p') * z ≤ (nMinus χ n * p') * c :=
        Nat.mul_le_mul (le_refl _) hzc
    _ = c * (nMinus χ n * p') := by ring
    _ = n := hcprod
    _ ≤ 2 * x := hnle

/-! ## §2 — the exponent-absorption law (freeze §S4 budget: `z₀³·e^{1.4z₀} ≤ e^{5z₀}`)

The two crude caps `Λ̃(n), Λ̃(n+2) ≤ e^{(log2)z₀}·L'` produce the exponent `e^{2·log2·z₀}`
(`2·log2 ≈ 1.386 ≈ 1.4`), and the `1/(log z)²` sieve floor and the `Σ1/p'` conversion
produce a `z₀³` factor.  The freeze's `Aexp = 5` budget absorbs both: `z₀³ ≤ e^{3z₀}`
(from `t ≤ e^t`) and `3 + 2·log2 < 5` (as `log2 < 1`). -/

/-- **Exponent absorption.**  `z₀³·e^{2·log2·z₀} ≤ e^{5·z₀}` — the frozen `Aexp = 5` budget. -/
lemma exp_absorption {z x : ℕ} (hz2 : 2 ≤ z) :
    (z0 z x) ^ 3 * Real.exp (2 * Real.log 2 * z0 z x) ≤ Real.exp (5 * z0 z x) := by
  have hz0 : 0 ≤ z0 z x := z0_nonneg hz2
  have ht : z0 z x ≤ Real.exp (z0 z x) := by linarith [Real.add_one_le_exp (z0 z x)]
  have hcube : Real.exp (z0 z x) ^ 3 = Real.exp (3 * z0 z x) := by
    rw [← Real.exp_nat_mul]; norm_num
  have h1 : (z0 z x) ^ 3 ≤ Real.exp (3 * z0 z x) := by
    calc (z0 z x) ^ 3 ≤ Real.exp (z0 z x) ^ 3 := by
          apply pow_le_pow_left₀ hz0 ht
      _ = Real.exp (3 * z0 z x) := hcube
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  calc (z0 z x) ^ 3 * Real.exp (2 * Real.log 2 * z0 z x)
      ≤ Real.exp (3 * z0 z x) * Real.exp (2 * Real.log 2 * z0 z x) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (3 * z0 z x + 2 * Real.log 2 * z0 z x) := by rw [← Real.exp_add]
    _ ≤ Real.exp (5 * z0 z x) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hz0, hlog2, mul_nonneg hz0 (sub_nonneg.mpr hlog2)]

/-! ## §3 — the modulus-route legality gate (freeze §S4 T2: `(log z)² ≤ 4096·z^{1/4}`)

The `l2c_pair_count_clean` fiber count requires the legality `d₁·d₂·Zz⁸·(log Zz)² ≤ 32x`.
Under the T2 modulus law (`d₁·z ≤ 2x`) and the w-route (`d₂ ≤ z^{1/4}`) this reduces to the
freeze's real-analysis claim `(log z)² ≤ 4096·z^{1/4}`, comfortably true for `z ≥ 100^16`
(indeed `(log z)² ≤ 64·z^{1/4}` via `log t ≤ 8·t^{1/8}`). -/

/-- `log z ≤ 8·z^{1/8}` (`log z = 8·log z^{1/8} ≤ 8·(z^{1/8} − 1)`). -/
lemma log_le_rpow_eighth {z : ℕ} (hz1 : 1 ≤ z) :
    Real.log z ≤ 8 * (z : ℝ) ^ ((1 : ℝ) / 8) := by
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have hr : (0 : ℝ) < (z : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hzpos _
  have hstep : Real.log ((z : ℝ) ^ ((1 : ℝ) / 8)) ≤ (z : ℝ) ^ ((1 : ℝ) / 8) - 1 :=
    Real.log_le_sub_one_of_pos hr
  rw [Real.log_rpow hzpos] at hstep
  linarith [hstep]

/-- `(log z)² ≤ 64·z^{1/4}` — the freeze's `4096`-legality core (with room to spare). -/
lemma log_sq_le_rpow_quarter {z : ℕ} (hz1 : 1 ≤ z) :
    (Real.log z) ^ 2 ≤ 64 * (z : ℝ) ^ ((1 : ℝ) / 4) := by
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have hlognn : 0 ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz1)
  have h8 := log_le_rpow_eighth hz1
  have hr8 : (0 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 8) := (Real.rpow_pos_of_pos hzpos _).le
  have hsq : (Real.log z) ^ 2 ≤ (8 * (z : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 :=
    sq_le_sq' (by nlinarith [hlognn, hr8]) h8
  have ht2 : ((z : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 = (z : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 8)) 2, ← Real.rpow_mul hzpos.le]; norm_num
  have hpow : (8 * (z : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 = 64 * (z : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [mul_pow, ht2]; norm_num
  rw [hpow] at hsq; exact hsq

/-- `Zz z ≤ z^{1/16}` (floor bound). -/
lemma Zz_le_rpow {z : ℕ} : (Zz z : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 16) := by
  rw [Zz]; exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg z) _)

/-- `Zz z⁸ ≤ z^{1/2}`. -/
lemma Zz_pow8_le {z : ℕ} (hz1 : 1 ≤ z) : (Zz z : ℝ) ^ 8 ≤ (z : ℝ) ^ ((1 : ℝ) / 2) := by
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have h1 : (Zz z : ℝ) ^ 8 ≤ ((z : ℝ) ^ ((1 : ℝ) / 16)) ^ 8 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) Zz_le_rpow 8
  have h2 : ((z : ℝ) ^ ((1 : ℝ) / 16)) ^ 8 = (z : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 16)) 8, ← Real.rpow_mul hzpos.le]; norm_num
  rw [h2] at h1; exact h1

/-- `(log Zz)² ≤ (log z)²/256`. -/
lemma logsq_Zz_le {z : ℕ} (hz100 : 100 ^ 16 ≤ z) :
    (Real.log (Zz z)) ^ 2 ≤ (Real.log z) ^ 2 / 256 := by
  have hz1 : 1 ≤ z := le_trans (Nat.one_le_pow _ _ (by norm_num)) hz100
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have hZz100 : 100 ≤ Zz z := Zz_ge_100 hz100
  have hZzpos : (0 : ℝ) < (Zz z : ℝ) := by exact_mod_cast (by omega : 0 < Zz z)
  have hlogle : Real.log (Zz z) ≤ (1 / 16) * Real.log z := by
    have h := Real.log_le_log hZzpos Zz_le_rpow
    rwa [Real.log_rpow hzpos] at h
  have hlognn : 0 ≤ Real.log (Zz z) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Zz z))
  have hlogznn : 0 ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz1)
  have hsq : (Real.log (Zz z)) ^ 2 ≤ ((1 / 16) * Real.log z) ^ 2 :=
    sq_le_sq' (by nlinarith [hlognn, hlogznn]) hlogle
  calc (Real.log (Zz z)) ^ 2 ≤ ((1 / 16) * Real.log z) ^ 2 := hsq
    _ = (Real.log z) ^ 2 / 256 := by ring

/-- `Zz z ≤ z^{1/4}` (so a prime `> z^{1/4}` clears the `Zz`-sift floor). -/
lemma Zz_le_quarter {z : ℕ} (hz1 : 1 ≤ z) : (Zz z : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := by
  refine le_trans Zz_le_rpow ?_
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hz1) (by norm_num)

/-- **The sift-floor conversion.**  `(log z)/32 ≤ log (Zz z)` for `z ≥ 100^16`
    (`⌊z^{1/16}⌋ ≥ z^{1/16}/2` and `(1/32)·log z ≥ log 2` in range) — the lower bound
    that converts the `1/(log Zz)²` of the pair count into `≤ 1024·z₀²/L'²`. -/
lemma log_Zz_ge {z : ℕ} (hz100 : 100 ^ 16 ≤ z) : Real.log z / 32 ≤ Real.log (Zz z) := by
  have hz1 : 1 ≤ z := le_trans (Nat.one_le_pow _ _ (by norm_num)) hz100
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have hZz100 : 100 ≤ Zz z := Zz_ge_100 hz100
  have hfl : (z : ℝ) ^ ((1 : ℝ) / 16) - 1 ≤ (Zz z : ℝ) := by
    rw [Zz]; exact le_of_lt (Nat.sub_one_lt_floor _)
  have hr2 : (2 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 16) := by
    have : ((100 : ℕ) : ℝ) ≤ (Zz z : ℝ) := by exact_mod_cast hZz100
    have hle : (Zz z : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 16) := Zz_le_rpow
    calc (2 : ℝ) ≤ ((100 : ℕ) : ℝ) := by norm_num
      _ ≤ (Zz z : ℝ) := this
      _ ≤ (z : ℝ) ^ ((1 : ℝ) / 16) := hle
  have hhalf : (z : ℝ) ^ ((1 : ℝ) / 16) / 2 ≤ (Zz z : ℝ) := by linarith [hfl, hr2]
  have hZzpos : (0 : ℝ) < (Zz z : ℝ) := by exact_mod_cast (by omega : 0 < Zz z)
  have hlog1 : Real.log ((z : ℝ) ^ ((1 : ℝ) / 16) / 2) ≤ Real.log (Zz z) :=
    Real.log_le_log (by positivity) hhalf
  have hlog2 : Real.log ((z : ℝ) ^ ((1 : ℝ) / 16) / 2)
      = (1 / 16) * Real.log z - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hzpos]
  have hlz : 32 * Real.log 2 ≤ Real.log z := by
    have h216 : ((2 : ℝ) ^ 32) ≤ ((100 : ℝ) ^ 16) := by norm_num
    have hz100R : ((100 : ℝ) ^ 16) ≤ (z : ℝ) := by exact_mod_cast hz100
    calc 32 * Real.log 2 = Real.log ((2 : ℝ) ^ 32) := by
          rw [Real.log_pow]; push_cast; ring
      _ ≤ Real.log ((100 : ℝ) ^ 16) := Real.log_le_log (by positivity) h216
      _ ≤ Real.log z := Real.log_le_log (by positivity) hz100R
  calc Real.log z / 32 = (1 / 16) * Real.log z - Real.log z / 32 := by ring
    _ ≤ (1 / 16) * Real.log z - Real.log 2 := by linarith [hlz]
    _ = Real.log ((z : ℝ) ^ ((1 : ℝ) / 16) / 2) := hlog2.symm
    _ ≤ Real.log (Zz z) := hlog1

/-- `Zz z < z` (so `z`-rough cofactors clear the `Zz`-sift floor). -/
lemma Zz_lt_z {z : ℕ} (hz2 : 2 ≤ z) : Zz z < z := by
  have hz1 : 1 ≤ z := by omega
  have hzR : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have h1 : (Zz z : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := Zz_le_quarter hz1
  have h2 : (z : ℝ) ^ ((1 : ℝ) / 4) < (z : ℝ) := by
    have := Real.rpow_lt_rpow_of_exponent_lt hzR (by norm_num : (1 : ℝ) / 4 < 1)
    rwa [Real.rpow_one] at this
  exact_mod_cast lt_of_le_of_lt h1 h2

/-! ## §4 — the family weight and the uniform per-summand cap

The fibration weighs each `n` by `Wt(v)·Wt(w)` (`v = n₋`, `w = (n+2)₋`), where `Wt` is `Λ`
on blocks `> 1` and the crude scale `L'` on the degenerate block `1`.  The caps below hold
for EVERY window element: in the `ω(block) ≥ 2` cases both sides vanish (`Λ̃−Λ = 0` resp.
`Λ̃ = 0` by the two-block kill, and `Λ(block) = 0` as the block is not a prime power). -/

/-- **The T2 family weight** (family-local): `Λ(u)` for `u ≠ 1`, `L'` for `u = 1`. -/
noncomputable def T2Wt (x u : ℕ) : ℝ := if u = 1 then Lwin x else Λ u

lemma T2Wt_nonneg (x u : ℕ) : 0 ≤ T2Wt x u := by
  rw [T2Wt]; split
  · exact Lwin_nonneg x
  · exact vonMangoldt_nonneg

/-- A block that is neither `1` nor a prime power has `ω ≥ 2`. -/
lemma t2_two_le_card {χ : DirichletCharacter ℂ q} {m : ℕ} (h1 : nMinus χ m ≠ 1)
    (hpp : ¬ IsPrimePow (nMinus χ m)) : 2 ≤ (nMinus χ m).primeFactors.card := by
  rcases Nat.lt_trichotomy (nMinus χ m).primeFactors.card 1 with h | h | h
  · have hc0 : (nMinus χ m).primeFactors.card = 0 := by omega
    rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hc0) with h0 | hone
    · exact absurd h0 (nMinus_pos χ m).ne'
    · exact absurd hone h1
  · exact absurd (isPrimePow_iff_card_primeFactors_eq_one.mpr h) hpp
  · omega

/-- **The left cap.**  On a window element, `(Λ̃−Λ)(n) ≤ e^{(log2)z₀}·Wt(n₋)`. -/
lemma t2_left_cap (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ} (hz2 : 2 ≤ z)
    (hn : n ∈ l2cWindow χ z x) :
    LamTilde χ n - Λ n ≤ Real.exp (Real.log 2 * z0 z x) * T2Wt x (nMinus χ n) := by
  have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hn
  have hcop : Nat.Coprime n q := l2cWindow_coprime χ hn
  rcases eq_or_ne (nMinus χ n) 1 with h1 | h1
  · rw [T2Wt, if_pos h1]
    calc LamTilde χ n - Λ n ≤ LamTilde χ n := by
          linarith [vonMangoldt_nonneg (n := n)]
      _ ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x := lamTilde_cap_window χ hsq hz2 hn
  · rw [T2Wt, if_neg h1]
    by_cases hpp : IsPrimePow (nMinus χ n)
    · calc LamTilde χ n - Λ n ≤ LamTilde χ n := by
            linarith [vonMangoldt_nonneg (n := n)]
        _ ≤ Real.exp (Real.log 2 * z0 z x) * Λ (nMinus χ n) :=
            lamTilde_single_block_le χ hsq z x hz2 hn0 hcop
              (by have := l2cWindow_le χ hn; omega)
              (fun p hp hpd hchi => l2cWindow_rough χ hn hp hpd hchi) hpp
    · have h0 := lamTilde_sub_vonMangoldt_eq_zero_of_two_le_card χ hsq hn0 hcop
        (t2_two_le_card h1 hpp)
      rw [h0]
      exact mul_nonneg (Real.exp_pos _).le vonMangoldt_nonneg

/-- **The right cap.**  On a window element, `Λ̃(n+2) ≤ e^{(log2)z₀}·Wt((n+2)₋)`. -/
lemma t2_right_cap (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ} (hz2 : 2 ≤ z)
    (hn : n ∈ l2cWindow χ z x) :
    LamTilde χ (n + 2) ≤ Real.exp (Real.log 2 * z0 z x) * T2Wt x (nMinus χ (n + 2)) := by
  have hn0 : n + 2 ≠ 0 := by omega
  have hcop : Nat.Coprime (n + 2) q := l2cWindow_coprime_add_two χ hn
  rcases eq_or_ne (nMinus χ (n + 2)) 1 with h1 | h1
  · rw [T2Wt, if_pos h1]
    exact lamTilde_cap_window_add_two χ hsq hz2 hn
  · rw [T2Wt, if_neg h1]
    by_cases hpp : IsPrimePow (nMinus χ (n + 2))
    · exact lamTilde_single_block_le χ hsq z x hz2 hn0 hcop
        (l2cWindow_add_two_le χ hn)
        (fun p hp hpd hchi => l2cWindow_rough_add_two χ hn hp hpd hchi) hpp
    · rw [LamTilde_eq_zero_of_two_le_card χ hsq hn0 hcop (t2_two_le_card h1 hpp)]
      exact mul_nonneg (Real.exp_pos _).le vonMangoldt_nonneg

/-- **The per-summand cap.**  On a window element,
    `(Λ̃−Λ)(n)·Λ̃(n+2) ≤ e^{2(log2)z₀}·Wt(n₋)·Wt((n+2)₋)`. -/
lemma t2_summand_cap (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ} (hz2 : 2 ≤ z)
    (hn : n ∈ l2cWindow χ z x) :
    (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ Real.exp (2 * Real.log 2 * z0 z x)
          * (T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))) := by
  have h1 := t2_left_cap χ hsq hz2 hn
  have h2 := t2_right_cap χ hsq hz2 hn
  have hL : 0 ≤ LamTilde χ (n + 2) := lamTilde_nonneg χ hsq (n + 2)
  have hR : 0 ≤ Real.exp (Real.log 2 * z0 z x) * T2Wt x (nMinus χ n) :=
    mul_nonneg (Real.exp_pos _).le (T2Wt_nonneg x _)
  calc (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ (Real.exp (Real.log 2 * z0 z x) * T2Wt x (nMinus χ n))
          * (Real.exp (Real.log 2 * z0 z x) * T2Wt x (nMinus χ (n + 2))) :=
        mul_le_mul h1 h2 hL hR
    _ = Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x)
          * (T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))) := by ring
    _ = Real.exp (2 * Real.log 2 * z0 z x)
          * (T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))) := by
        rw [← Real.exp_add]; ring_nf

/-! ## §5 — regime scales, the weight-Mertens sum, and the scale identities -/

/-- `100 ≤ L'` in the master regime (`x ≥ 100^48`). -/
lemma t2_Lwin_ge {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    100 ≤ Lwin x := by
  have hzr : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
  have hx48 : (100 : ℝ) ^ 48 ≤ (x : ℝ) := by
    calc (100 : ℝ) ^ 48 = ((100 : ℝ) ^ 16) ^ 3 := by
          rw [show (48 : ℕ) = 16 * 3 from rfl, pow_mul]
      _ ≤ (z : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hzr 3
      _ ≤ (x : ℝ) := hzx
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx48
  have hlog100 : (4 : ℝ) ≤ Real.log 100 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 100)]
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h4 : Real.exp 4 = (Real.exp 1) ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    calc (Real.exp 1) ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 4
      _ ≤ 100 := by norm_num
  have h1 : Real.log ((100 : ℝ) ^ 48) ≤ Real.log x := Real.log_le_log (by positivity) hx48
  rw [Real.log_pow] at h1
  have h2 : Real.log x ≤ Lwin x := by
    rw [Lwin]
    exact Real.log_le_log hxpos (by linarith [Nat.cast_nonneg (α := ℝ) x])
  have h3 : (100 : ℝ) ≤ 48 * Real.log 100 := by nlinarith [hlog100]
  push_cast at h1
  linarith [h1, h2, h3]

/-- **The weight-Mertens sum.**  `Σ_{u ≤ N} Wt(u)/u ≤ 3·L'` for `1 ≤ N ≤ 2x+2` in-regime
    (the `u = 1` row pays `L'`, the rest is Mertens `≤ log N + log 4 + 4 ≤ L' + 7`). -/
lemma t2_wt_sum_le {z x N : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (hN1 : 1 ≤ N) (hNle : N ≤ 2 * x + 2) :
    ∑ u ∈ Finset.range (N + 1), T2Wt x u / u ≤ 3 * Lwin x := by
  have hL : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hterm : ∀ u ∈ Finset.range (N + 1),
      T2Wt x u / u ≤ (if u = 1 then Lwin x else 0) + Λ u / u := by
    intro u _
    rcases eq_or_ne u 1 with rfl | hu
    · rw [T2Wt, if_pos rfl, if_pos rfl, vonMangoldt_apply_one]
      norm_num
    · rw [T2Wt, if_neg hu, if_neg hu, zero_add]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib]
  have h1 : (∑ u ∈ Finset.range (N + 1), if u = 1 then Lwin x else 0) = Lwin x := by
    rw [Finset.sum_ite_eq' (Finset.range (N + 1)) 1 (fun _ => Lwin x),
        if_pos (Finset.mem_range.mpr (by omega))]
  have h2 : (∑ u ∈ Finset.range (N + 1), Λ u / u) = ∑ u ∈ Finset.Ioc 0 N, Λ u / u := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro u hu; rw [Finset.mem_Ioc] at hu; rw [Finset.mem_range]; omega
    · intro u hu hnot
      rw [Finset.mem_range] at hu; rw [Finset.mem_Ioc] at hnot
      have hu0 : u = 0 := by omega
      subst hu0; simp
  rw [h1, h2]
  have h3 : ∑ u ∈ Finset.Ioc 0 N, Λ u / u ≤ Real.log N + (Real.log 4 + 4) :=
    mertens_vonMangoldt_div_le hN1
  have h4 : Real.log N ≤ Lwin x := by
    rw [Lwin]
    refine Real.log_le_log (by exact_mod_cast hN1) ?_
    exact_mod_cast hNle
  have h5 : Real.log 4 + 4 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  linarith [h3, h4, h5, hL]

/-- The scale identity `1/log z = z₀/L'`. -/
lemma t2_inv_log_z {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    1 / Real.log z = z0 z x / Lwin x := by
  have hL : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hz1 : (1 : ℝ) < (z : ℝ) := by
    exact_mod_cast (by calc 1 < 100 ^ 16 := by norm_num
                        _ ≤ z := hz100 : 1 < z)
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hL0 : Lwin x ≠ 0 := by linarith
  have hlz0 : Real.log z ≠ 0 := hlogz.ne'
  rw [z0]
  field_simp

/-- **The sift-floor count conversion.**  `1/(log Zz)² ≤ 1024·(z₀/L')²`. -/
lemma t2_inv_logZz_sq {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    1 / (Real.log (Zz z)) ^ 2 ≤ 1024 * (z0 z x / Lwin x) ^ 2 := by
  have hz1 : (1 : ℝ) < (z : ℝ) := by
    exact_mod_cast (by calc 1 < 100 ^ 16 := by norm_num
                        _ ≤ z := hz100 : 1 < z)
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hZzlog : Real.log z / 32 ≤ Real.log (Zz z) := log_Zz_ge hz100
  have hpos : (0 : ℝ) < Real.log z / 32 := by linarith
  have hsq : (Real.log z / 32) ^ 2 ≤ (Real.log (Zz z)) ^ 2 :=
    pow_le_pow_left₀ hpos.le hZzlog 2
  calc 1 / (Real.log (Zz z)) ^ 2 ≤ 1 / (Real.log z / 32) ^ 2 :=
        one_div_le_one_div_of_le (pow_pos hpos 2) hsq
    _ = 1024 * (1 / Real.log z) ^ 2 := by
        rw [div_pow]; rw [one_div, one_div]; ring_nf
    _ = 1024 * (z0 z x / Lwin x) ^ 2 := by rw [t2_inv_log_z hz100 hzx]

/-- `PretenseSum χ N ≥ 0` (a sum of `log p/p ≥ 0`). -/
lemma t2_pretenseSum_nonneg (χ : DirichletCharacter ℂ q) (N : ℕ) :
    0 ≤ PretenseSum χ N := by
  rw [PretenseSum]
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)) (by positivity)

/-! ## §6 — the count kernel

The `Zz`-sifted pair count at a T2-legal modulus pair, folded into a single explicit
constant: `l2c_pair_count_clean` + the totient-ratio bound `(d/φ)² ≤ 729/64` (three odd
pairwise-coprime prime-power-or-1 factors) + the amendment-3 legality at the `Zz` floor. -/

/-- Roughness beats the primorial: if every prime of `M` exceeds `Z`, `(primorial Z, M)=1`. -/
lemma t2_coprime_primorial {Z M : ℕ}
    (h : ∀ r : ℕ, r.Prime → r ∣ M → Z < r) : Nat.Coprime (primorial Z) M := by
  rw [primorial]
  refine Nat.coprime_prod_left_iff.mpr fun p hp => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hp
  refine (Nat.Prime.coprime_iff_not_dvd hp.2).mpr fun hdvd => ?_
  exact absurd (h p hp.2 hdvd) (by omega)

/-- `φ(u) ≥ (2/3)·u` for odd `u` equal to `1` or a prime power. -/
lemma t2_totient_ge {u : ℕ} (hu : u = 1 ∨ IsPrimePow u) (ho : ¬ 2 ∣ u) :
    (2 / 3 : ℝ) * u ≤ (Nat.totient u : ℝ) := by
  rcases hu with rfl | hpp
  · rw [Nat.totient_one]; norm_num
  · obtain ⟨p, k, hp, hk, huk⟩ := (isPrimePow_nat_iff u).mp hpp
    subst huk
    have hp3 : 3 ≤ p := by
      rcases Nat.lt_or_ge p 3 with h | h
      · exfalso
        have hp2 : p = 2 := by have := hp.two_le; omega
        exact ho (hp2 ▸ dvd_pow_self p hk.ne')
      · exact h
    have hnat : 2 * p ^ k ≤ 3 * Nat.totient (p ^ k) := by
      rw [Nat.totient_prime_pow hp hk]
      have h2p : 2 * p ≤ 3 * (p - 1) := by omega
      calc 2 * p ^ k = p ^ (k - 1) * (2 * p) := by
            conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
            ring
        _ ≤ p ^ (k - 1) * (3 * (p - 1)) := Nat.mul_le_mul_left _ h2p
        _ = 3 * (p ^ (k - 1) * (p - 1)) := by ring
    have hcast : (2 * p ^ k : ℝ) ≤ 3 * (Nat.totient (p ^ k) : ℝ) := by exact_mod_cast hnat
    push_cast
    linarith

/-- **The totient-ratio bound.**  `(d/φ(d))² ≤ 729/64` for `d = v·p'·w` with `v, w` odd
    `1`-or-prime-powers, `p'` an odd prime, pairwise coprime. -/
lemma t2_totient_ratio {v p' w : ℕ} (hv : v = 1 ∨ IsPrimePow v) (hw : w = 1 ∨ IsPrimePow w)
    (hp' : p'.Prime) (hov : ¬ 2 ∣ v) (how : ¬ 2 ∣ w) (hop' : ¬ 2 ∣ p')
    (hcvp : Nat.Coprime v p') (hcw : Nat.Coprime (v * p') w) :
    ((v * p' * w : ℝ) / (Nat.totient (v * p' * w) : ℝ)) ^ 2 ≤ (729 / 64 : ℝ) := by
  have hvpos : 0 < v := by
    rcases hv with rfl | h
    · omega
    · exact h.pos
  have hwpos : 0 < w := by
    rcases hw with rfl | h
    · omega
    · exact h.pos
  have hp'pos : 0 < p' := hp'.pos
  have htv := t2_totient_ge hv hov
  have htw := t2_totient_ge hw how
  have htp := t2_totient_ge (Or.inr hp'.isPrimePow) hop'
  have hmul : Nat.totient (v * p' * w) = Nat.totient v * Nat.totient p' * Nat.totient w := by
    rw [Nat.totient_mul hcw, Nat.totient_mul hcvp]
  have hphi : (8 / 27 : ℝ) * ((v : ℝ) * p' * w) ≤ (Nat.totient (v * p' * w) : ℝ) := by
    have h12 : (2 / 3 : ℝ) * v * ((2 / 3 : ℝ) * p')
        ≤ (Nat.totient v : ℝ) * (Nat.totient p' : ℝ) :=
      mul_le_mul htv htp (by positivity) (Nat.cast_nonneg _)
    have h123 : ((2 / 3 : ℝ) * v * ((2 / 3 : ℝ) * p')) * ((2 / 3 : ℝ) * w)
        ≤ ((Nat.totient v : ℝ) * (Nat.totient p' : ℝ)) * (Nat.totient w : ℝ) :=
      mul_le_mul h12 htw (by positivity) (by positivity)
    calc (8 / 27 : ℝ) * ((v : ℝ) * p' * w)
        = ((2 / 3 : ℝ) * v * ((2 / 3 : ℝ) * p')) * ((2 / 3 : ℝ) * w) := by ring
      _ ≤ ((Nat.totient v : ℝ) * (Nat.totient p' : ℝ)) * (Nat.totient w : ℝ) := h123
      _ = (Nat.totient (v * p' * w) : ℝ) := by rw [hmul, Nat.cast_mul, Nat.cast_mul]
  have hφpos : (0 : ℝ) < (Nat.totient (v * p' * w) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by positivity)
  have hr : (v * p' * w : ℝ) / (Nat.totient (v * p' * w) : ℝ) ≤ 27 / 8 := by
    rw [div_le_iff₀ hφpos]
    nlinarith [hphi]
  calc ((v * p' * w : ℝ) / (Nat.totient (v * p' * w) : ℝ)) ^ 2
      ≤ (27 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hr 2
    _ = (729 / 64 : ℝ) := by norm_num

/-- **The T2 legality at the `Zz` floor** (amendment 3).  With the repaired modulus law
    `d₁·z ≤ 2x` and the w-route `d₂ ≤ z^{1/4}`:
    `d₁d₂·Zz⁸·(log Zz)² ≤ (2x/z)·z^{1/4}·z^{1/2}·(z^{1/4}/4) = x/2 ≤ 32x`. -/
lemma t2_legality {z x d₁ d₂ : ℕ} (hz100 : 100 ^ 16 ≤ z)
    (hmod : (d₁ : ℝ) * z ≤ 2 * x) (hd₂4 : (d₂ : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)) :
    (d₁ * d₂ : ℝ) * (Zz z : ℝ) ^ 8 * (Real.log (Zz z)) ^ 2 ≤ 32 * x := by
  have hz1 : 1 ≤ z := le_trans (Nat.one_le_pow _ _ (by norm_num)) hz100
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hA0 : (0 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := (Real.rpow_pos_of_pos hzpos _).le
  have hB0 : (0 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 2) := (Real.rpow_pos_of_pos hzpos _).le
  have h3 : (Zz z : ℝ) ^ 8 ≤ (z : ℝ) ^ ((1 : ℝ) / 2) := Zz_pow8_le hz1
  have h4 : (Real.log (Zz z)) ^ 2 ≤ (z : ℝ) ^ ((1 : ℝ) / 4) / 4 := by
    have ha := logsq_Zz_le hz100
    have hb := log_sq_le_rpow_quarter hz1
    linarith
  have hd₁0 : (0 : ℝ) ≤ (d₁ : ℝ) := Nat.cast_nonneg _
  have hABA : (z : ℝ) ^ ((1 : ℝ) / 4) * (z : ℝ) ^ ((1 : ℝ) / 2) * (z : ℝ) ^ ((1 : ℝ) / 4)
      = (z : ℝ) := by
    rw [← Real.rpow_add hzpos, ← Real.rpow_add hzpos]
    norm_num
  have s1 : (d₁ * d₂ : ℝ) ≤ (d₁ : ℝ) * (z : ℝ) ^ ((1 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_left hd₂4 hd₁0
  have s2 : (d₁ * d₂ : ℝ) * (Zz z : ℝ) ^ 8
      ≤ ((d₁ : ℝ) * (z : ℝ) ^ ((1 : ℝ) / 4)) * (z : ℝ) ^ ((1 : ℝ) / 2) :=
    mul_le_mul s1 h3 (by positivity) (by positivity)
  have s3 : (d₁ * d₂ : ℝ) * (Zz z : ℝ) ^ 8 * (Real.log (Zz z)) ^ 2
      ≤ ((d₁ : ℝ) * (z : ℝ) ^ ((1 : ℝ) / 4)) * (z : ℝ) ^ ((1 : ℝ) / 2)
          * ((z : ℝ) ^ ((1 : ℝ) / 4) / 4) :=
    mul_le_mul s2 h4 (sq_nonneg _) (by positivity)
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg _
  calc (d₁ * d₂ : ℝ) * (Zz z : ℝ) ^ 8 * (Real.log (Zz z)) ^ 2
      ≤ ((d₁ : ℝ) * (z : ℝ) ^ ((1 : ℝ) / 4)) * (z : ℝ) ^ ((1 : ℝ) / 2)
          * ((z : ℝ) ^ ((1 : ℝ) / 4) / 4) := s3
    _ = (d₁ : ℝ) * ((z : ℝ) ^ ((1 : ℝ) / 4) * (z : ℝ) ^ ((1 : ℝ) / 2)
          * (z : ℝ) ^ ((1 : ℝ) / 4)) / 4 := by ring
    _ = (d₁ : ℝ) * z / 4 := by rw [hABA]
    _ ≤ 2 * (x : ℝ) / 4 := by linarith [hmod]
    _ ≤ 32 * x := by linarith [hx0]

open Classical in
/-- **The T2 count kernel.**  The `Zz`-sifted pair count at a T2-legal pair
    `(d₁, d₂)`: `≤ 1458·(x/(d₁d₂))/(log Zz)²` (`128·(729/64) = 1458`). -/
lemma t2_count_kernel {z x d₁ d₂ : ℕ} (hz100 : 100 ^ 16 ≤ z)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (ho1 : Odd d₁) (ho2 : Odd d₂)
    (hcop : Nat.Coprime d₁ d₂)
    (hratio : ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂) : ℝ)) ^ 2 ≤ (729 / 64 : ℝ))
    (hmod : (d₁ : ℝ) * z ≤ 2 * x) (hd₂4 : (d₂ : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)) :
    (((baseSet x d₁ d₂).filter
        (fun n => Nat.Coprime (primorial (Zz z)) ((n / d₁) * ((n + 2) / d₂)))).card : ℝ)
      ≤ 1458 * ((x : ℝ) / (d₁ * d₂)) / (Real.log (Zz z)) ^ 2 := by
  have hZz := Zz_ge_100 hz100
  have hleg := t2_legality hz100 hmod hd₂4
  have hcount := l2c_pair_count_clean (x := x) hZz hd₁ hd₂ ho1 ho2 hcop hleg
  refine le_trans hcount ?_
  have hlogZzpos : (0 : ℝ) < (Real.log (Zz z)) ^ 2 := by
    have h1 : (1 : ℝ) < (Zz z : ℝ) := by exact_mod_cast (by omega : 1 < Zz z)
    exact pow_pos (Real.log_pos h1) 2
  rw [div_le_div_iff₀ hlogZzpos hlogZzpos]
  have h128 : 128 * ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂) : ℝ)) ^ 2 ≤ 1458 := by
    linarith [hratio]
  have hstep : 128 * ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂) : ℝ)) ^ 2
        * ((x : ℝ) / (d₁ * d₂))
      ≤ 1458 * ((x : ℝ) / (d₁ * d₂)) :=
    mul_le_mul_of_nonneg_right h128 (by positivity)
  exact mul_le_mul_of_nonneg_right hstep hlogZzpos.le

/-! ## §7 — the member packet and the two fiber bounds

Route A (`w ≤ z^{1/4}`) fibers by `(v, w, p')` at `(d₁, d₂) = (v·p', w)`; route B
(`w > z^{1/4}`, block a prime power by the vanishing reduction) fibers by `(v, p')` at
`(d₁, d₂) = (v·p', 1)` — the guard + primality push the base of `w` above `Zz`, so the
whole cofactor `n+2` survives the `Zz`-sift (amendment 3). -/

open Classical in
/-- Unpack membership in the T2 slice. -/
lemma T2Set_mem (χ : DirichletCharacter ℂ q) {z x m : ℕ} (hm : m ∈ T2Set χ z x) :
    m ∈ l2cWindow χ z x ∧ Odd m ∧ 1 < nPlus χ m ∧ ¬ (nPlus χ m).Prime ∧
      ¬ T2JunkBlock z (nMinus χ (m + 2)) := by
  rw [T2Set, Finset.mem_filter] at hm
  exact ⟨hm.1, hm.2⟩

/-- The `Odd n` guard in divisibility form. -/
lemma T2Set_not_two_dvd (χ : DirichletCharacter ℂ q) {z x m : ℕ} (hm : m ∈ T2Set χ z x) :
    ¬ 2 ∣ m := by
  have hodd := (T2Set_mem χ hm).2.1
  rw [Nat.odd_iff] at hodd
  omega

/-- Divisors of odd numbers are odd. -/
lemma t2_odd_of_dvd {d m : ℕ} (hdm : d ∣ m) (hm : ¬ 2 ∣ m) : Odd d := by
  rcases Nat.even_or_odd d with he | ho
  · obtain ⟨t, rfl⟩ := he
    exact absurd (Dvd.dvd.trans ⟨t, by ring⟩ hdm) hm
  · exact ho

/-- `n₋ ∣ n` (for `n` coprime to `q`). -/
lemma t2_nMinus_dvd (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ} (hm0 : m ≠ 0)
    (hcop : Nat.Coprime m q) : nMinus χ m ∣ m :=
  ⟨nPlus χ m, by rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq hm0 hcop⟩

/-- **The per-element T2 packet.**  Every element of the T2 slice carries the REPAIRED
    modulus law at its own `p' = minFac n₊` and `c`. -/
lemma T2Set_packet (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x m : ℕ}
    (hm : m ∈ T2Set χ z x) :
    ∃ c : ℕ, (nPlus χ m).minFac.Prime ∧ chiRe χ ((nPlus χ m).minFac) = 1 ∧
      z ≤ (nPlus χ m).minFac ∧ z ≤ c ∧ c ∣ nPlus χ m ∧
      c * (nMinus χ m * (nPlus χ m).minFac) = m ∧
      (nMinus χ m * (nPlus χ m).minFac) * z ≤ 2 * x := by
  obtain ⟨hwin, _, hn1, hcomp, _⟩ := T2Set_mem χ hm
  obtain ⟨p', c, hpdef, hpp, hsign, hzp, hzc, hcdvd, hcprod, hmodz⟩ :=
    t2_modulus_law χ hsq hwin hn1 hcomp
  subst hpdef
  exact ⟨c, hpp, hsign, hzp, hzc, hcdvd, hcprod, hmodz⟩

open Classical in
/-- **Route-A fiber subset.**  The `(v, w, p')`-fiber of the T2 slice lands in the
    `Zz`-sifted base set at `(d₁, d₂) = (v·p', w)`: the `n`-side cofactor is the `≥ z`
    factor `c` of the REPAIRED law, the `n+2`-side cofactor is the all-plus `(n+2)₊`. -/
lemma t2_fiberA_subset (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (v w p' : ℕ) :
    ((T2Set χ z x).filter
        (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ n).minFac) = (v, w, p')))
      ⊆ (baseSet x (v * p') w).filter
          (fun n => Nat.Coprime (primorial (Zz z)) ((n / (v * p')) * ((n + 2) / w))) := by
  intro m hm
  rw [Finset.mem_filter] at hm
  obtain ⟨hmT2, hkey⟩ := hm
  rw [Prod.mk.injEq, Prod.mk.injEq] at hkey
  obtain ⟨hkv, hkw, hkp⟩ := hkey
  subst hkv; subst hkw; subst hkp
  obtain ⟨hwin, hodd, hn1, hcomp, hguard⟩ := T2Set_mem χ hmT2
  obtain ⟨c, hpp, hsign, hzp, hzc, hcdvd, hcprod, hmodz⟩ := T2Set_packet χ hsq hmT2
  have hm0 : m ≠ 0 := l2cWindow_ne_zero χ hwin
  have hcopq : Nat.Coprime m q := l2cWindow_coprime χ hwin
  have hcopq2 : Nat.Coprime (m + 2) q := l2cWindow_coprime_add_two χ hwin
  have hd₁dvd : nMinus χ m * (nPlus χ m).minFac ∣ m :=
    ⟨c, by rw [mul_comm]; exact hcprod.symm⟩
  have hwdvd : nMinus χ (m + 2) ∣ m + 2 := t2_nMinus_dvd χ hsq (by omega) hcopq2
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [baseSet, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨l2cWindow_lt χ hwin, l2cWindow_le χ hwin⟩, hd₁dvd, hwdvd⟩
  · have hd₁pos : 0 < nMinus χ m * (nPlus χ m).minFac :=
      Nat.mul_pos (nMinus_pos χ m) hpp.pos
    have hdiv1 : m / (nMinus χ m * (nPlus χ m).minFac) = c :=
      Nat.div_eq_of_eq_mul_left hd₁pos hcprod.symm
    have hdiv2 : (m + 2) / nMinus χ (m + 2) = nPlus χ (m + 2) :=
      Nat.div_eq_of_eq_mul_left (nMinus_pos χ (m + 2))
        (eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2)
    rw [hdiv1, hdiv2]
    refine t2_coprime_primorial fun r hr hrdvd => ?_
    have hZzz : Zz z < z := Zz_lt_z (le_trans (by norm_num) hz100)
    rcases hr.dvd_mul.mp hrdvd with hrc | hrP
    · have hrnP : r ∣ nPlus χ m := hrc.trans hcdvd
      have hrsign : chiRe χ r = 1 := nPlus_dvd_sign hr hrnP
      have hrm : r ∣ m := hrnP.trans ⟨nMinus χ m, eq_nPlus_mul_nMinus χ hsq hm0 hcopq⟩
      have hzr : z ≤ r := l2cWindow_rough χ hwin hr hrm (by rw [hrsign]; norm_num)
      omega
    · have hrsign : chiRe χ r = 1 := nPlus_dvd_sign hr hrP
      have hrm2 : r ∣ m + 2 :=
        hrP.trans ⟨nMinus χ (m + 2), eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩
      have hzr : z ≤ r := l2cWindow_rough_add_two χ hwin hr hrm2 (by rw [hrsign]; norm_num)
      omega

open Classical in
/-- **The route-A fiber count.**  Under the weight-structure hypotheses on `(v, w)`, the
    `(v, w, p')`-fiber of the modulus route (`w ≤ z^{1/4}`) has
    `≤ 1458·(x/(v·p'·w))/(log Zz)²` elements. -/
lemma t2_fiberA_card (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) {v w p' : ℕ}
    (hv : v = 1 ∨ IsPrimePow v) (hw : w = 1 ∨ IsPrimePow w) :
    ((((T2Set χ z x).filter
          (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ n).minFac) = (v, w, p'))).card : ℝ)
      ≤ 1458 * ((x : ℝ) / ((v : ℝ) * p' * w)) / (Real.log (Zz z)) ^ 2 := by
  rcases Finset.eq_empty_or_nonempty (((T2Set χ z x).filter
      (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
      (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ n).minFac) = (v, w, p')))
    with he | ⟨n₀, hn₀⟩
  · rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · rw [Finset.mem_filter] at hn₀
    obtain ⟨hn₀SA, hkey⟩ := hn₀
    rw [Finset.mem_filter] at hn₀SA
    obtain ⟨hn₀T2, hrouteA⟩ := hn₀SA
    rw [Prod.mk.injEq, Prod.mk.injEq] at hkey
    obtain ⟨hkv, hkw, hkp⟩ := hkey
    subst hkv; subst hkw; subst hkp
    obtain ⟨hwin, hodd, hn1, hcomp, hguard⟩ := T2Set_mem χ hn₀T2
    have hodd' : ¬ 2 ∣ n₀ := T2Set_not_two_dvd χ hn₀T2
    obtain ⟨c, hpp, hsign, hzp, hzc, hcdvd, hcprod, hmodz⟩ := T2Set_packet χ hsq hn₀T2
    have hm0 : n₀ ≠ 0 := l2cWindow_ne_zero χ hwin
    have hcopq : Nat.Coprime n₀ q := l2cWindow_coprime χ hwin
    have hcopq2 : Nat.Coprime (n₀ + 2) q := l2cWindow_coprime_add_two χ hwin
    have hodd2 : ¬ 2 ∣ (n₀ + 2) := by omega
    have hvdvd : nMinus χ n₀ ∣ n₀ := t2_nMinus_dvd χ hsq hm0 hcopq
    have hwdvd : nMinus χ (n₀ + 2) ∣ n₀ + 2 := t2_nMinus_dvd χ hsq (by omega) hcopq2
    have hPdvd : nPlus χ n₀ ∣ n₀ := ⟨nMinus χ n₀, eq_nPlus_mul_nMinus χ hsq hm0 hcopq⟩
    have hp'dvd : (nPlus χ n₀).minFac ∣ n₀ := (Nat.minFac_dvd _).trans hPdvd
    have hd₁dvd : nMinus χ n₀ * (nPlus χ n₀).minFac ∣ n₀ :=
      ⟨c, by rw [mul_comm]; exact hcprod.symm⟩
    have hd₁pos : 0 < nMinus χ n₀ * (nPlus χ n₀).minFac :=
      Nat.mul_pos (nMinus_pos χ n₀) hpp.pos
    have hwpos : 0 < nMinus χ (n₀ + 2) := nMinus_pos χ (n₀ + 2)
    have ho1 : Odd (nMinus χ n₀ * (nPlus χ n₀).minFac) := t2_odd_of_dvd hd₁dvd hodd'
    have ho2 : Odd (nMinus χ (n₀ + 2)) := t2_odd_of_dvd hwdvd hodd2
    have hv2 : ¬ 2 ∣ nMinus χ n₀ := fun h => hodd' (h.trans hvdvd)
    have hw2 : ¬ 2 ∣ nMinus χ (n₀ + 2) := fun h => hodd2 (h.trans hwdvd)
    have hp2 : ¬ 2 ∣ (nPlus χ n₀).minFac := fun h => hodd' (h.trans hp'dvd)
    have hcvp : Nat.Coprime (nMinus χ n₀) ((nPlus χ n₀).minFac) := by
      refine Nat.Coprime.symm ((hpp.coprime_iff_not_dvd).mpr fun hdvd => ?_)
      have hneg := nMinus_dvd_sign hpp hdvd
      rw [hsign] at hneg
      norm_num at hneg
    have hcop12 : Nat.Coprime (nMinus χ n₀ * (nPlus χ n₀).minFac) (nMinus χ (n₀ + 2)) := by
      by_contra hnc
      obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd hnc
      have h1 : r ∣ n₀ := (hrg.trans (Nat.gcd_dvd_left _ _)).trans hd₁dvd
      have h2 : r ∣ n₀ + 2 := (hrg.trans (Nat.gcd_dvd_right _ _)).trans hwdvd
      have h3 : r ∣ 2 := by
        have := Nat.dvd_sub h2 h1
        rwa [Nat.add_sub_cancel_left] at this
      have hr2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h3
      exact hodd' (hr2 ▸ h1)
    have hratio := t2_totient_ratio hv hw hpp hv2 hw2 hp2 hcvp hcop12
    have hratio' : (((nMinus χ n₀ * (nPlus χ n₀).minFac : ℕ) : ℝ) * (nMinus χ (n₀ + 2) : ℕ)
          / (Nat.totient (nMinus χ n₀ * (nPlus χ n₀).minFac * nMinus χ (n₀ + 2)) : ℝ)) ^ 2
        ≤ (729 / 64 : ℝ) := by
      rw [show (((nMinus χ n₀ * (nPlus χ n₀).minFac : ℕ) : ℝ) * (nMinus χ (n₀ + 2) : ℕ))
          = ((nMinus χ n₀ : ℝ) * ((nPlus χ n₀).minFac : ℝ) * (nMinus χ (n₀ + 2) : ℝ)) from by
        push_cast; ring]
      exact hratio
    have hmod : ((nMinus χ n₀ * (nPlus χ n₀).minFac : ℕ) : ℝ) * z ≤ 2 * x := by
      exact_mod_cast hmodz
    have hkernel := t2_count_kernel hz100 hd₁pos hwpos ho1 ho2 hcop12 hratio'
      hmod hrouteA
    have hsub : (((T2Set χ z x).filter
          (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ n).minFac)
          = (nMinus χ n₀, nMinus χ (n₀ + 2), (nPlus χ n₀).minFac)))
        ⊆ (baseSet x (nMinus χ n₀ * (nPlus χ n₀).minFac) (nMinus χ (n₀ + 2))).filter
          (fun n => Nat.Coprime (primorial (Zz z))
            ((n / (nMinus χ n₀ * (nPlus χ n₀).minFac)) * ((n + 2) / nMinus χ (n₀ + 2)))) := by
      refine Finset.Subset.trans ?_ (t2_fiberA_subset χ hsq hz100 _ _ _)
      exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    calc ((((T2Set χ z x).filter
          (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ n).minFac)
          = (nMinus χ n₀, nMinus χ (n₀ + 2), (nPlus χ n₀).minFac))).card : ℝ)
        ≤ (((baseSet x (nMinus χ n₀ * (nPlus χ n₀).minFac) (nMinus χ (n₀ + 2))).filter
            (fun n => Nat.Coprime (primorial (Zz z))
              ((n / (nMinus χ n₀ * (nPlus χ n₀).minFac))
                * ((n + 2) / nMinus χ (n₀ + 2))))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 1458 * ((x : ℝ) / ((nMinus χ n₀ * (nPlus χ n₀).minFac : ℕ) * (nMinus χ (n₀ + 2))))
            / (Real.log (Zz z)) ^ 2 := hkernel
      _ = 1458 * ((x : ℝ) / ((nMinus χ n₀ : ℝ) * ((nPlus χ n₀).minFac : ℝ)
            * (nMinus χ (n₀ + 2) : ℝ))) / (Real.log (Zz z)) ^ 2 := by
          rw [show ((nMinus χ n₀ * (nPlus χ n₀).minFac : ℕ) : ℝ) * ((nMinus χ (n₀ + 2) : ℕ) : ℝ)
              = ((nMinus χ n₀ : ℝ) * ((nPlus χ n₀).minFac : ℝ)
                * (nMinus χ (n₀ + 2) : ℝ)) from by push_cast; ring]

open Classical in
/-- **Route-B fiber subset.**  On the cofactor route (`w > z^{1/4}`, `w` a prime power) the
    `(v, p')`-fiber lands in the `Zz`-sifted base set at `(d₁, d₂) = (v·p', 1)`: the whole
    cofactor `n+2 = (n+2)₊·w` is `Zz`-rough — the all-plus part by window roughness, the
    block `w` because the junk guard (+ primality at `e = 1`) pushes its base above `Zz`. -/
lemma t2_fiberB_subset (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (v p' : ℕ) :
    ((((T2Set χ z x).filter
          (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => IsPrimePow (nMinus χ (n + 2)))).filter
        (fun n => (nMinus χ n, (nPlus χ n).minFac) = (v, p')))
      ⊆ (baseSet x (v * p') 1).filter
          (fun n => Nat.Coprime (primorial (Zz z)) ((n / (v * p')) * ((n + 2) / 1))) := by
  intro m hm
  simp only [Finset.mem_filter] at hm
  obtain ⟨⟨⟨hmT2, hrouteB⟩, hppw⟩, hkey⟩ := hm
  rw [Prod.mk.injEq] at hkey
  obtain ⟨hkv, hkp⟩ := hkey
  subst hkv; subst hkp
  obtain ⟨hwin, hodd, hn1, hcomp, hguard⟩ := T2Set_mem χ hmT2
  obtain ⟨c, hpp, hsign, hzp, hzc, hcdvd, hcprod, hmodz⟩ := T2Set_packet χ hsq hmT2
  have hm0 : m ≠ 0 := l2cWindow_ne_zero χ hwin
  have hcopq : Nat.Coprime m q := l2cWindow_coprime χ hwin
  have hcopq2 : Nat.Coprime (m + 2) q := l2cWindow_coprime_add_two χ hwin
  have hd₁dvd : nMinus χ m * (nPlus χ m).minFac ∣ m :=
    ⟨c, by rw [mul_comm]; exact hcprod.symm⟩
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [baseSet, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨l2cWindow_lt χ hwin, l2cWindow_le χ hwin⟩, hd₁dvd, one_dvd _⟩
  · have hd₁pos : 0 < nMinus χ m * (nPlus χ m).minFac :=
      Nat.mul_pos (nMinus_pos χ m) hpp.pos
    have hdiv1 : m / (nMinus χ m * (nPlus χ m).minFac) = c :=
      Nat.div_eq_of_eq_mul_left hd₁pos hcprod.symm
    rw [hdiv1, Nat.div_one]
    refine t2_coprime_primorial fun r hr hrdvd => ?_
    have hZzz : Zz z < z := Zz_lt_z (le_trans (by norm_num) hz100)
    rcases hr.dvd_mul.mp hrdvd with hrc | hrm2
    · have hrnP : r ∣ nPlus χ m := hrc.trans hcdvd
      have hrsign : chiRe χ r = 1 := nPlus_dvd_sign hr hrnP
      have hrm : r ∣ m := hrnP.trans ⟨nMinus χ m, eq_nPlus_mul_nMinus χ hsq hm0 hcopq⟩
      have hzr : z ≤ r := l2cWindow_rough χ hwin hr hrm (by rw [hrsign]; norm_num)
      omega
    · have hsplit := eq_nPlus_mul_nMinus χ hsq (show m + 2 ≠ 0 by omega) hcopq2
      have hrPw : r ∣ nPlus χ (m + 2) * nMinus χ (m + 2) := hsplit ▸ hrm2
      rcases hr.dvd_mul.mp hrPw with hrP | hrw
      · have hrsign : chiRe χ r = 1 := nPlus_dvd_sign hr hrP
        have hrm2' : r ∣ m + 2 :=
          hrP.trans ⟨nMinus χ (m + 2), eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩
        have hzr : z ≤ r :=
          l2cWindow_rough_add_two χ hwin hr hrm2' (by rw [hrsign]; norm_num)
        omega
      · obtain ⟨s, k, hs, hk, hsk⟩ := (isPrimePow_nat_iff _).mp hppw
        rw [← hsk] at hrw
        have hrs : r = s :=
          (Nat.prime_dvd_prime_iff_eq hr hs).mp (hr.dvd_of_dvd_pow hrw)
        have hs_gt : Zz z < s := by
          rcases eq_or_lt_of_le (show 1 ≤ k by omega) with hk1 | hk2
          · have hws : nMinus χ (m + 2) = s := by rw [← hsk, ← hk1, pow_one]
            have hwR : (z : ℝ) ^ ((1 : ℝ) / 4) < (nMinus χ (m + 2) : ℝ) := not_le.mp hrouteB
            have hZzR : (Zz z : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) :=
              Zz_le_quarter (le_trans (by norm_num) hz100)
            have hlt : (Zz z : ℝ) < (s : ℝ) := by
              rw [← hws]; exact lt_of_le_of_lt hZzR hwR
            exact_mod_cast hlt
          · rcases Nat.lt_or_ge (Zz z) s with hgt | hle
            · exact hgt
            · exact absurd ⟨s, k, hs, hle, by omega, hsk.symm, not_le.mp hrouteB⟩ hguard
        rw [hrs]
        exact hs_gt

open Classical in
/-- **The route-B fiber count.**  Under the weight-structure hypothesis on `v`, the
    `(v, p')`-fiber of the cofactor route has `≤ 1458·(x/(v·p'))/(log Zz)²` elements. -/
lemma t2_fiberB_card (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) {v p' : ℕ} (hv : v = 1 ∨ IsPrimePow v) :
    (((((T2Set χ z x).filter
          (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => IsPrimePow (nMinus χ (n + 2)))).filter
        (fun n => (nMinus χ n, (nPlus χ n).minFac) = (v, p'))).card : ℝ)
      ≤ 1458 * ((x : ℝ) / ((v : ℝ) * p')) / (Real.log (Zz z)) ^ 2 := by
  rcases Finset.eq_empty_or_nonempty ((((T2Set χ z x).filter
      (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
      (fun n => IsPrimePow (nMinus χ (n + 2)))).filter
      (fun n => (nMinus χ n, (nPlus χ n).minFac) = (v, p')))
    with he | ⟨n₀, hn₀⟩
  · rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · simp only [Finset.mem_filter] at hn₀
    obtain ⟨⟨⟨hn₀T2, _⟩, _⟩, hkey⟩ := hn₀
    rw [Prod.mk.injEq] at hkey
    obtain ⟨hkv, hkp⟩ := hkey
    subst hkv; subst hkp
    obtain ⟨hwin, hodd, hn1, hcomp, hguard⟩ := T2Set_mem χ hn₀T2
    have hodd' : ¬ 2 ∣ n₀ := T2Set_not_two_dvd χ hn₀T2
    obtain ⟨c, hpp, hsign, hzp, hzc, hcdvd, hcprod, hmodz⟩ := T2Set_packet χ hsq hn₀T2
    have hm0 : n₀ ≠ 0 := l2cWindow_ne_zero χ hwin
    have hcopq : Nat.Coprime n₀ q := l2cWindow_coprime χ hwin
    have hvdvd : nMinus χ n₀ ∣ n₀ := t2_nMinus_dvd χ hsq hm0 hcopq
    have hPdvd : nPlus χ n₀ ∣ n₀ := ⟨nMinus χ n₀, eq_nPlus_mul_nMinus χ hsq hm0 hcopq⟩
    have hp'dvd : (nPlus χ n₀).minFac ∣ n₀ := (Nat.minFac_dvd _).trans hPdvd
    have hd₁dvd : nMinus χ n₀ * (nPlus χ n₀).minFac ∣ n₀ :=
      ⟨c, by rw [mul_comm]; exact hcprod.symm⟩
    have hd₁pos : 0 < nMinus χ n₀ * (nPlus χ n₀).minFac :=
      Nat.mul_pos (nMinus_pos χ n₀) hpp.pos
    have ho1 : Odd (nMinus χ n₀ * (nPlus χ n₀).minFac) := t2_odd_of_dvd hd₁dvd hodd'
    have hv2 : ¬ 2 ∣ nMinus χ n₀ := fun h => hodd' (h.trans hvdvd)
    have hp2 : ¬ 2 ∣ (nPlus χ n₀).minFac := fun h => hodd' (h.trans hp'dvd)
    have hcvp : Nat.Coprime (nMinus χ n₀) ((nPlus χ n₀).minFac) := by
      refine Nat.Coprime.symm ((hpp.coprime_iff_not_dvd).mpr fun hdvd => ?_)
      have hneg := nMinus_dvd_sign hpp hdvd
      rw [hsign] at hneg
      norm_num at hneg
    have hcop12 : Nat.Coprime (nMinus χ n₀ * (nPlus χ n₀).minFac) 1 :=
      Nat.coprime_one_right _
    have hratio := t2_totient_ratio hv (Or.inl rfl) hpp hv2 (by norm_num) hp2 hcvp hcop12
    have hratio' : (((nMinus χ n₀ * (nPlus χ n₀).minFac : ℕ) : ℝ) * ((1 : ℕ) : ℝ)
          / (Nat.totient (nMinus χ n₀ * (nPlus χ n₀).minFac * 1) : ℝ)) ^ 2
        ≤ (729 / 64 : ℝ) := by
      rw [show (((nMinus χ n₀ * (nPlus χ n₀).minFac : ℕ) : ℝ) * ((1 : ℕ) : ℝ))
          = ((nMinus χ n₀ : ℝ) * ((nPlus χ n₀).minFac : ℝ) * ((1 : ℕ) : ℝ)) from by
        push_cast; ring]
      exact hratio
    have hmod : ((nMinus χ n₀ * (nPlus χ n₀).minFac : ℕ) : ℝ) * z ≤ 2 * x := by
      exact_mod_cast hmodz
    have hone : ((1 : ℕ) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [Nat.cast_one]
      calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 4) := (Real.one_rpow _).symm
        _ ≤ (z : ℝ) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow (by norm_num)
              (by exact_mod_cast le_trans (by norm_num : 1 ≤ 100 ^ 16) hz100) (by norm_num)
    have hkernel := t2_count_kernel hz100 hd₁pos (by omega : 0 < 1) ho1 odd_one hcop12
      hratio' hmod hone
    have hsub := t2_fiberB_subset (x := x) χ hsq hz100 (nMinus χ n₀) ((nPlus χ n₀).minFac)
    calc ((((((T2Set χ z x).filter
          (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => IsPrimePow (nMinus χ (n + 2)))).filter
        (fun n => (nMinus χ n, (nPlus χ n).minFac)
          = (nMinus χ n₀, (nPlus χ n₀).minFac))).card : ℕ) : ℝ)
        ≤ (((baseSet x (nMinus χ n₀ * (nPlus χ n₀).minFac) 1).filter
            (fun n => Nat.Coprime (primorial (Zz z))
              ((n / (nMinus χ n₀ * (nPlus χ n₀).minFac)) * ((n + 2) / 1)))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 1458 * ((x : ℝ) / ((nMinus χ n₀ * (nPlus χ n₀).minFac : ℕ) * ((1 : ℕ) : ℝ)))
            / (Real.log (Zz z)) ^ 2 := hkernel
      _ = 1458 * ((x : ℝ) / ((nMinus χ n₀ : ℝ) * ((nPlus χ n₀).minFac : ℝ)))
            / (Real.log (Zz z)) ^ 2 := by
          rw [show ((nMinus χ n₀ * (nPlus χ n₀).minFac : ℕ) : ℝ) * ((1 : ℕ) : ℝ)
              = ((nMinus χ n₀ : ℝ) * ((nPlus χ n₀).minFac : ℝ)) from by push_cast; ring]

/-! ## §8 — the two route sums and the family budget -/

open Classical in
/-- **The route-A sum.**  The modulus route (`w ≤ z^{1/4}`), fibered over `(v, w, p')` and
    priced by Mertens × Mertens × PretenseSum: `≤ 13436928·x·z₀³·PS/L'`. -/
lemma t2_routeA_sum (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ (T2Set χ z x).filter
        (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
      T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))
      ≤ 13436928 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / Lwin x := by
  have hL : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hmaps : ∀ n ∈ (T2Set χ z x).filter
      (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
      (nMinus χ n, nMinus χ (n + 2), (nPlus χ n).minFac)
        ∈ (Finset.range (2 * x + 1)) ×ˢ ((Finset.range (2 * x + 3))
            ×ˢ ((Finset.range (2 * x + 3)).filter
              (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p))) := by
    intro n hn
    have hnT2 : n ∈ T2Set χ z x := Finset.mem_of_mem_filter n hn
    obtain ⟨hwin, hodd, hn1, hcomp, hguard⟩ := T2Set_mem χ hnT2
    obtain ⟨c, hpp, hsign, hzp, hzc, hcdvd, hcprod, hmodz⟩ := T2Set_packet χ hsq hnT2
    have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hwin
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnle : n ≤ 2 * x := l2cWindow_le χ hwin
    have hcopq : Nat.Coprime n q := l2cWindow_coprime χ hwin
    have hcopq2 : Nat.Coprime (n + 2) q := l2cWindow_coprime_add_two χ hwin
    have hvle : nMinus χ n ≤ n := Nat.le_of_dvd hnpos (t2_nMinus_dvd χ hsq hn0 hcopq)
    have hwle : nMinus χ (n + 2) ≤ n + 2 :=
      Nat.le_of_dvd (by omega) (t2_nMinus_dvd χ hsq (by omega) hcopq2)
    have hple : (nPlus χ n).minFac ≤ n :=
      Nat.le_of_dvd hnpos ((Nat.minFac_dvd _).trans
        ⟨nMinus χ n, eq_nPlus_mul_nMinus χ hsq hn0 hcopq⟩)
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_filter]
    exact ⟨by omega, by omega, by omega, hpp, hsign, hzp⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun n => T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)))]
  have hperk : ∀ k ∈ (Finset.range (2 * x + 1)) ×ˢ ((Finset.range (2 * x + 3))
      ×ˢ ((Finset.range (2 * x + 3)).filter
        (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p))),
      (∑ n ∈ ((T2Set χ z x).filter
          (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
          (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ n).minFac) = k),
        T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)))
      ≤ (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2)
          * ((T2Wt x k.1 / k.1) * ((T2Wt x k.2.1 / k.2.1) * (1 / k.2.2))) := by
    intro k _
    obtain ⟨v, w, p'⟩ := k
    have hconst : ∀ n ∈ ((T2Set χ z x).filter
        (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ n).minFac) = (v, w, p')),
        T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)) = T2Wt x v * T2Wt x w := by
      intro n hn
      have hk := (Finset.mem_filter.mp hn).2
      rw [Prod.mk.injEq, Prod.mk.injEq] at hk
      rw [hk.1, hk.2.1]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    by_cases hWv : T2Wt x v = 0
    · simp [hWv]
    by_cases hWw : T2Wt x w = 0
    · simp [hWw]
    have hv : v = 1 ∨ IsPrimePow v := by
      rcases eq_or_ne v 1 with h1 | h1
      · exact Or.inl h1
      · refine Or.inr (by_contra fun hnp => hWv ?_)
        rw [T2Wt, if_neg h1]
        exact vonMangoldt_eq_zero_iff.mpr hnp
    have hw : w = 1 ∨ IsPrimePow w := by
      rcases eq_or_ne w 1 with h1 | h1
      · exact Or.inl h1
      · refine Or.inr (by_contra fun hnp => hWw ?_)
        rw [T2Wt, if_neg h1]
        exact vonMangoldt_eq_zero_iff.mpr hnp
    have hcard := t2_fiberA_card (x := x) (p' := p') χ hsq hz100 hv hw
    have hWnn : (0 : ℝ) ≤ T2Wt x v * T2Wt x w :=
      mul_nonneg (T2Wt_nonneg x v) (T2Wt_nonneg x w)
    have hconv := t2_inv_logZz_sq hz100 hzx
    have hfac : (0 : ℝ) ≤ 1458 * (x : ℝ) * (T2Wt x v * T2Wt x w) / ((v : ℝ) * p' * w) := by
      apply div_nonneg _ (by positivity)
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg x)) hWnn
    calc ((((T2Set χ z x).filter
          (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
          (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ n).minFac)
            = (v, w, p'))).card : ℝ) * (T2Wt x v * T2Wt x w)
        ≤ (1458 * ((x : ℝ) / ((v : ℝ) * p' * w)) / (Real.log (Zz z)) ^ 2)
            * (T2Wt x v * T2Wt x w) := mul_le_mul_of_nonneg_right hcard hWnn
      _ = (1458 * (x : ℝ) * (T2Wt x v * T2Wt x w) / ((v : ℝ) * p' * w))
            * (1 / (Real.log (Zz z)) ^ 2) := by ring
      _ ≤ (1458 * (x : ℝ) * (T2Wt x v * T2Wt x w) / ((v : ℝ) * p' * w))
            * (1024 * (z0 z x / Lwin x) ^ 2) := mul_le_mul_of_nonneg_left hconv hfac
      _ = (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2)
            * ((T2Wt x v / v) * ((T2Wt x w / w) * (1 / p'))) := by ring
  refine le_trans (Finset.sum_le_sum hperk) ?_
  have hfact : ∑ k ∈ (Finset.range (2 * x + 1)) ×ˢ ((Finset.range (2 * x + 3))
      ×ˢ ((Finset.range (2 * x + 3)).filter
        (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p))),
      (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2)
        * ((T2Wt x k.1 / k.1) * ((T2Wt x k.2.1 / k.2.1) * (1 / k.2.2)))
      = (∑ v ∈ Finset.range (2 * x + 1),
          (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x v / v))
        * ((∑ w ∈ Finset.range (2 * x + 3), T2Wt x w / w)
          * (∑ p ∈ (Finset.range (2 * x + 3)).filter
              (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [Finset.sum_product]
    refine Finset.sum_congr rfl fun v _ => ?_
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hfact]
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h0 | h1
    · exfalso
      rw [h0] at hzx
      have hz1R : (1 : ℝ) ≤ (z : ℝ) := by
        exact_mod_cast le_trans (by norm_num : 1 ≤ 100 ^ 16) hz100
      have hcube : (1 : ℝ) ≤ (z : ℝ) ^ 3 :=
        one_le_pow₀ hz1R
      push_cast at hzx
      linarith
    · exact h1
  have hz1' : 1 < z := lt_of_lt_of_le (by norm_num) hz100
  have hg : ∑ v ∈ Finset.range (2 * x + 1), T2Wt x v / v ≤ 3 * Lwin x :=
    t2_wt_sum_le hz100 hzx (by omega) (by omega)
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
    rw [← hconv]
    exact hps
  have hSg0 : (0 : ℝ) ≤ ∑ v ∈ Finset.range (2 * x + 1), T2Wt x v / v :=
    Finset.sum_nonneg fun v _ => div_nonneg (T2Wt_nonneg x v) (Nat.cast_nonneg v)
  have hSh0 : (0 : ℝ) ≤ ∑ w ∈ Finset.range (2 * x + 3), T2Wt x w / w :=
    Finset.sum_nonneg fun w _ => div_nonneg (T2Wt_nonneg x w) (Nat.cast_nonneg w)
  have hSp0 : (0 : ℝ) ≤ ∑ p ∈ (Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p :=
    Finset.sum_nonneg fun p _ => by positivity
  have hL0 : Lwin x ≠ 0 := by linarith
  have hin : (∑ w ∈ Finset.range (2 * x + 3), T2Wt x w / w)
        * (∑ p ∈ (Finset.range (2 * x + 3)).filter
          (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p)
      ≤ (3 * Lwin x) * (PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x)) :=
    mul_le_mul hh hp hSp0 (by linarith)
  have hC0 : (0 : ℝ) ≤ 1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2 := by positivity
  have hgC : ∑ v ∈ Finset.range (2 * x + 1),
        (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x v / v)
      ≤ (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (3 * Lwin x) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hg hC0
  calc (∑ v ∈ Finset.range (2 * x + 1),
        (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x v / v))
        * ((∑ w ∈ Finset.range (2 * x + 3), T2Wt x w / w)
          * (∑ p ∈ (Finset.range (2 * x + 3)).filter
              (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p))
      ≤ ((1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (3 * Lwin x))
          * ((3 * Lwin x) * (PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x))) :=
        mul_le_mul hgC hin (mul_nonneg hSh0 hSp0)
          (mul_nonneg hC0 (by linarith))
    _ = 13436928 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / Lwin x := by
        field_simp
        ring

open Classical in
/-- **The route-B sum.**  The cofactor route (`w > z^{1/4}`): the vanishing reduction to
    prime-power `w`, the crude `L'` cap on the `w`-weight, and the `(v, p')`-fibration:
    `≤ 4478976·x·z₀³·PS/L'`. -/
lemma t2_routeB_sum (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ (T2Set χ z x).filter
        (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
      T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))
      ≤ 4478976 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / Lwin x := by
  have hL : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hz14 : (1 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 4) := (Real.one_rpow _).symm
      _ ≤ (z : ℝ) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (by norm_num)
            (by exact_mod_cast le_trans (by norm_num : 1 ≤ 100 ^ 16) hz100) (by norm_num)
  have hvanish : ∀ n ∈ (T2Set χ z x).filter
      (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
      T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)) ≠ 0
        → IsPrimePow (nMinus χ (n + 2)) := by
    intro n hn hne
    have hB : ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) :=
      (Finset.mem_filter.mp hn).2
    have hWw : T2Wt x (nMinus χ (n + 2)) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hne1 : nMinus χ (n + 2) ≠ 1 := by
      rintro h1
      exact hB (by rw [h1, Nat.cast_one]; exact hz14)
    rw [T2Wt, if_neg hne1] at hWw
    by_contra hnp
    exact hWw (vonMangoldt_eq_zero_iff.mpr hnp)
  rw [← Finset.sum_filter_of_ne hvanish]
  have hcapw : ∀ n ∈ ((T2Set χ z x).filter
      (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
      (fun n => IsPrimePow (nMinus χ (n + 2))),
      T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))
        ≤ T2Wt x (nMinus χ n) * Lwin x := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnSB, hppw⟩ := hn
    have hB : ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) :=
      (Finset.mem_filter.mp hnSB).2
    have hnT2 : n ∈ T2Set χ z x := Finset.mem_of_mem_filter n hnSB
    obtain ⟨hwin, _, _, _, _⟩ := T2Set_mem χ hnT2
    have hcopq2 : Nat.Coprime (n + 2) q := l2cWindow_coprime_add_two χ hwin
    have hne1 : nMinus χ (n + 2) ≠ 1 := by
      rintro h1
      exact hB (by rw [h1, Nat.cast_one]; exact hz14)
    have hwle : nMinus χ (n + 2) ≤ 2 * x + 2 :=
      le_trans (Nat.le_of_dvd (by omega) (t2_nMinus_dvd χ hsq (by omega) hcopq2))
        (l2cWindow_add_two_le χ hwin)
    have hcap : T2Wt x (nMinus χ (n + 2)) ≤ Lwin x := by
      rw [T2Wt, if_neg hne1]
      calc Λ (nMinus χ (n + 2)) ≤ Real.log (nMinus χ (n + 2)) := vonMangoldt_le_log
        _ ≤ Lwin x := by
            rw [Lwin]
            exact Real.log_le_log (by exact_mod_cast nMinus_pos χ (n + 2))
              (by exact_mod_cast hwle)
    exact mul_le_mul_of_nonneg_left hcap (T2Wt_nonneg x _)
  refine le_trans (Finset.sum_le_sum hcapw) ?_
  rw [← Finset.sum_mul]
  have hmaps : ∀ n ∈ ((T2Set χ z x).filter
      (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
      (fun n => IsPrimePow (nMinus χ (n + 2))),
      (nMinus χ n, (nPlus χ n).minFac)
        ∈ (Finset.range (2 * x + 1)) ×ˢ ((Finset.range (2 * x + 3)).filter
            (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p)) := by
    intro n hn
    have hnT2 : n ∈ T2Set χ z x :=
      Finset.mem_of_mem_filter n (Finset.mem_of_mem_filter n hn)
    obtain ⟨hwin, _, _, _, _⟩ := T2Set_mem χ hnT2
    obtain ⟨c, hpp, hsign, hzp, _, _, _, _⟩ := T2Set_packet χ hsq hnT2
    have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hwin
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnle : n ≤ 2 * x := l2cWindow_le χ hwin
    have hcopq : Nat.Coprime n q := l2cWindow_coprime χ hwin
    have hvle : nMinus χ n ≤ n := Nat.le_of_dvd hnpos (t2_nMinus_dvd χ hsq hn0 hcopq)
    have hple : (nPlus χ n).minFac ≤ n :=
      Nat.le_of_dvd hnpos ((Nat.minFac_dvd _).trans
        ⟨nMinus χ n, eq_nPlus_mul_nMinus χ hsq hn0 hcopq⟩)
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_filter]
    exact ⟨by omega, by omega, hpp, hsign, hzp⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => T2Wt x (nMinus χ n))]
  have hperk : ∀ k ∈ (Finset.range (2 * x + 1)) ×ˢ ((Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p)),
      (∑ n ∈ (((T2Set χ z x).filter
          (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
          (fun n => IsPrimePow (nMinus χ (n + 2)))).filter
          (fun n => (nMinus χ n, (nPlus χ n).minFac) = k),
        T2Wt x (nMinus χ n))
      ≤ (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2)
          * ((T2Wt x k.1 / k.1) * (1 / k.2)) := by
    intro k _
    obtain ⟨v, p'⟩ := k
    have hconst : ∀ n ∈ (((T2Set χ z x).filter
        (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => IsPrimePow (nMinus χ (n + 2)))).filter
        (fun n => (nMinus χ n, (nPlus χ n).minFac) = (v, p')),
        T2Wt x (nMinus χ n) = T2Wt x v := by
      intro n hn
      have hk := (Finset.mem_filter.mp hn).2
      rw [Prod.mk.injEq] at hk
      rw [hk.1]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    by_cases hWv : T2Wt x v = 0
    · simp [hWv]
    have hv : v = 1 ∨ IsPrimePow v := by
      rcases eq_or_ne v 1 with h1 | h1
      · exact Or.inl h1
      · refine Or.inr (by_contra fun hnp => hWv ?_)
        rw [T2Wt, if_neg h1]
        exact vonMangoldt_eq_zero_iff.mpr hnp
    have hcard := t2_fiberB_card (x := x) (p' := p') χ hsq hz100 hv
    have hWnn : (0 : ℝ) ≤ T2Wt x v := T2Wt_nonneg x v
    have hconv := t2_inv_logZz_sq hz100 hzx
    have hfac : (0 : ℝ) ≤ 1458 * (x : ℝ) * T2Wt x v / ((v : ℝ) * p') := by
      apply div_nonneg _ (by positivity)
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg x)) hWnn
    calc ((((((T2Set χ z x).filter
          (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
          (fun n => IsPrimePow (nMinus χ (n + 2)))).filter
          (fun n => (nMinus χ n, (nPlus χ n).minFac) = (v, p'))).card : ℕ) : ℝ)
          * T2Wt x v
        ≤ (1458 * ((x : ℝ) / ((v : ℝ) * p')) / (Real.log (Zz z)) ^ 2) * T2Wt x v :=
          mul_le_mul_of_nonneg_right hcard hWnn
      _ = (1458 * (x : ℝ) * T2Wt x v / ((v : ℝ) * p')) * (1 / (Real.log (Zz z)) ^ 2) := by
          ring
      _ ≤ (1458 * (x : ℝ) * T2Wt x v / ((v : ℝ) * p'))
            * (1024 * (z0 z x / Lwin x) ^ 2) := mul_le_mul_of_nonneg_left hconv hfac
      _ = (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2)
            * ((T2Wt x v / v) * (1 / p')) := by ring
  refine le_trans (mul_le_mul_of_nonneg_right (Finset.sum_le_sum hperk)
    (Lwin_nonneg x)) ?_
  have hfact : ∑ k ∈ (Finset.range (2 * x + 1)) ×ˢ ((Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p)),
      (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2)
        * ((T2Wt x k.1 / k.1) * (1 / k.2))
      = (∑ v ∈ Finset.range (2 * x + 1),
          (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x v / v))
        * (∑ p ∈ (Finset.range (2 * x + 3)).filter
            (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p) := by
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_product]
    refine Finset.sum_congr rfl fun v _ => ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hfact]
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h0 | h1
    · exfalso
      rw [h0] at hzx
      have hz1R : (1 : ℝ) ≤ (z : ℝ) := by
        exact_mod_cast le_trans (by norm_num : 1 ≤ 100 ^ 16) hz100
      have hcube : (1 : ℝ) ≤ (z : ℝ) ^ 3 := one_le_pow₀ hz1R
      push_cast at hzx
      linarith
    · exact h1
  have hz1' : 1 < z := lt_of_lt_of_le (by norm_num) hz100
  have hg : ∑ v ∈ Finset.range (2 * x + 1), T2Wt x v / v ≤ 3 * Lwin x :=
    t2_wt_sum_le hz100 hzx (by omega) (by omega)
  have hp : ∑ p ∈ (Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p
      ≤ PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x) := by
    have hps := sum_inv_plusprime_le_pretense χ z (2 * x + 2) hz1'
    have hconv : PretenseSum χ (2 * x + 2) / Real.log z
        = PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x) := by
      rw [div_eq_mul_one_div, t2_inv_log_z hz100 hzx]
    rw [← hconv]
    exact hps
  have hSp0 : (0 : ℝ) ≤ ∑ p ∈ (Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p :=
    Finset.sum_nonneg fun p _ => by positivity
  have hL0 : Lwin x ≠ 0 := by linarith
  have hC0 : (0 : ℝ) ≤ 1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2 := by positivity
  have hgC : ∑ v ∈ Finset.range (2 * x + 1),
        (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x v / v)
      ≤ (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (3 * Lwin x) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hg hC0
  calc ((∑ v ∈ Finset.range (2 * x + 1),
        (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x v / v))
        * (∑ p ∈ (Finset.range (2 * x + 3)).filter
            (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p)) * Lwin x
      ≤ (((1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (3 * Lwin x))
          * (PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x))) * Lwin x := by
        refine mul_le_mul_of_nonneg_right ?_ (Lwin_nonneg x)
        exact mul_le_mul hgC hp hSp0 (mul_nonneg hC0 (by linarith))
    _ = 4478976 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / Lwin x := by
        field_simp
        ring

/-! ## §9 — the frozen T2 family budget -/

open Classical in
/-- **The T2 family budget** (freeze §S4, the `J2` row; house amendments #245/#246 baked).
    Over the T2 slice (`n` odd, `n₊` composite, junk guard on `(n+2)₋`), under the master
    hypothesis packet:

    `E_L^{T2} ≤ Cmain·(x/L')·e^{5z₀}·PS(2x+2)`,  `Cmain = 17915904` absolute.

    Route A (`w ≤ z^{1/4}`) prices `13436928·x·z₀³·PS/L'`, route B (`w > z^{1/4}`)
    `4478976·x·z₀³·PS/L'`; the `Aexp = 5` budget absorbs `z₀³·e^{2(log2)z₀} ≤ e^{5z₀}`. -/
theorem EL_T2_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : (Lwin x) ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    EL_T2 χ z x
      ≤ 17915904 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by
  -- `hz8` is carried as part of the frozen master packet (T2's routes do not consume it).
  have _ := hz8
  have hL : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hPS0 : 0 ≤ PretenseSum χ (2 * x + 2) := t2_pretenseSum_nonneg χ _
  have hcap : EL_T2 χ z x
      ≤ Real.exp (2 * Real.log 2 * z0 z x) * ∑ n ∈ T2Set χ z x,
          T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)) := by
    rw [EL_T2, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    exact t2_summand_cap χ hsq hz2 (T2Set_subset_window χ z x hn)
  have hsplit : ∑ n ∈ T2Set χ z x, T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))
      = (∑ n ∈ (T2Set χ z x).filter
            (fun n => (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
          T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)))
        + ∑ n ∈ (T2Set χ z x).filter
            (fun n => ¬ (nMinus χ (n + 2) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
          T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hmain : ∑ n ∈ T2Set χ z x, T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))
      ≤ 17915904 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / Lwin x := by
    rw [hsplit]
    refine le_trans (add_le_add (t2_routeA_sum χ hsq hz100 hzx)
      (t2_routeB_sum χ hsq hz100 hzx)) (le_of_eq ?_)
    ring
  have hxL0 : (0 : ℝ) ≤ (x : ℝ) / Lwin x :=
    div_nonneg (Nat.cast_nonneg x) (by linarith)
  calc EL_T2 χ z x
      ≤ Real.exp (2 * Real.log 2 * z0 z x) * ∑ n ∈ T2Set χ z x,
          T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)) := hcap
    _ ≤ Real.exp (2 * Real.log 2 * z0 z x)
          * (17915904 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / Lwin x) :=
        mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le
    _ = 17915904 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2)
          * ((z0 z x) ^ 3 * Real.exp (2 * Real.log 2 * z0 z x)) := by ring
    _ ≤ 17915904 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2)
          * Real.exp (5 * z0 z x) := by
        refine mul_le_mul_of_nonneg_left (exp_absorption hz2) ?_
        exact mul_nonneg (mul_nonneg (by norm_num) hxL0) hPS0
    _ = 17915904 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by ring

end Salt.HB
