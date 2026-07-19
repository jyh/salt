/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cEL

/-!
# HB-L2c — the `E_L` T1 family budget (node HB-L2c, Wave 3 input; the `J1` row)

The `T1` family of the left overshoot `E_L = Σ_{n∈W} (Λ̃−Λ)(n)·Λ̃(n+2)`: the terms with

* `n₊ = P` a single **prime** (`f(P) = 2`),
* `(n+2)₊ = U` a single **prime** (`f(U) = 2`),
* `n₋ = v` with `1 < v < z`, odd,
* `(n+2)₋ = w < z`, odd — either a prime power (the *main* row) or `1` (the *edge* row);
  blocks with `ω ≥ 2` vanish identically (two-block kill).

On this family the term collapses to the **absolute** weight `4Λ(v)Λ(w)` (main) resp.
`2Λ(v)·L'` (edge): no `PretenseSum`, no `e^{z₀}` — HB's `(3.3)` reborn.  Fibering by the
`χ=−1` blocks `(v,w)`, counting each fiber with `L2cCore.l2c_pair_count_clean` at
`(d₁,d₂) = (v,w)` and `Z := Zf x`, and summing the block weights by Mertens gives the
`J1` budget `≤ T1Cmain·(x / z₀)` (`EL_T1_bound`).

**Sift-floor soundness** (house amendment, catch #245): the sifted cofactors are the
primes `n₊, (n+2)₊ > x/z ≥ Zf` — proven explicitly (`T1_cofactor_gt_Zf`, from `z³ ≤ x`:
`Zf·z ≤ x^{1/48}·x^{1/3} ≤ x < n = n₊·n₋ ≤ n₊·z`), so the `Zf`-sift is genuinely sound
for this family.  The legality `v·w·Zf⁸·(log Zf)² ≤ 32x` follows from
`hz8 : (L')⁸ ≤ z` and `hzx : z³ ≤ x` (`T1_legality`, total exponent `11/12 < 1`).

Single-writer file (`L2cELT1.lean`); imports the frozen surfaces `L2cEL`/`L2cCore` and
touches no other file.  All helpers are `T1_`-prefixed (the single-writer law extends to
names, catch #245).  Not yet in the `Salt.HB.All` manifest (Wave 3's responsibility).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — totient and primorial arithmetic helpers -/

/-- A prime power (or `1`) satisfies `d ≤ 2·φ(d)` (`d/φ(d) = p/(p−1) ≤ 2`). -/
lemma T1_le_two_mul_totient {d : ℕ} (hd : IsPrimePow d ∨ d = 1) :
    d ≤ 2 * Nat.totient d := by
  rcases hd with hd | rfl
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hd
    rw [Nat.totient_prime_pow hp hk]
    have hp2 : 2 ≤ p := hp.two_le
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hple : p ≤ 2 * (p - 1) := by omega
    calc p ^ (k' + 1) = p ^ k' * p := pow_succ p k'
      _ ≤ p ^ k' * (2 * (p - 1)) := Nat.mul_le_mul (le_refl _) hple
      _ = 2 * (p ^ ((k' + 1) - 1) * (p - 1)) := by rw [Nat.add_sub_cancel]; ring
  · simp [Nat.totient_one]

/-- Positivity of a prime power (or `1`). -/
lemma T1_pos_of_pp_or_one {d : ℕ} (hd : IsPrimePow d ∨ d = 1) : 0 < d := by
  rcases hd with hd | rfl
  · exact hd.pos
  · norm_num

/-- For coprime prime-power-or-one moduli `d₁,d₂`, `(d₁d₂/φ(d₁d₂))² ≤ 16`
    (each local ratio is `≤ 2`). -/
lemma T1_totient_ratio_sq_le {d₁ d₂ : ℕ} (h1 : IsPrimePow d₁ ∨ d₁ = 1)
    (h2 : IsPrimePow d₂ ∨ d₂ = 1) (hcop : Nat.Coprime d₁ d₂) :
    ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂))) ^ 2 ≤ 16 := by
  have hφ : Nat.totient (d₁ * d₂) = Nat.totient d₁ * Nat.totient d₂ := Nat.totient_mul hcop
  have hd1 : (d₁ : ℝ) ≤ 2 * Nat.totient d₁ := by exact_mod_cast T1_le_two_mul_totient h1
  have hd2 : (d₂ : ℝ) ≤ 2 * Nat.totient d₂ := by exact_mod_cast T1_le_two_mul_totient h2
  have hφ1 : (0 : ℝ) < Nat.totient d₁ := by
    exact_mod_cast Nat.totient_pos.mpr (T1_pos_of_pp_or_one h1)
  have hφ2 : (0 : ℝ) < Nat.totient d₂ := by
    exact_mod_cast Nat.totient_pos.mpr (T1_pos_of_pp_or_one h2)
  have hφpos : (0 : ℝ) < (Nat.totient (d₁ * d₂) : ℝ) := by
    rw [hφ]; push_cast; positivity
  have hratio : (d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂)) ≤ 4 := by
    rw [div_le_iff₀ hφpos, hφ]
    push_cast
    nlinarith [hd1, hd2, hφ1, hφ2]
  have hnn : (0 : ℝ) ≤ (d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂)) := by positivity
  calc ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂))) ^ 2 ≤ (4 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hnn hratio 2
    _ = 16 := by norm_num

/-- A prime `P` exceeding `Z` is coprime to `primorial Z` (its only prime factor is
    `P > Z`). -/
lemma T1_coprime_primorial_of_prime_lt {P Z : ℕ} (hP : P.Prime) (hZP : Z < P) :
    Nat.Coprime (primorial Z) P := by
  rw [primorial]
  refine Nat.Coprime.prod_left fun p hp => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hp
  exact (Nat.coprime_primes hp.2 hP).mpr (by omega)

/-! ## §1 — the T1 scale facts

The regime `100^16 ≤ z`, `(L')⁸ ≤ z`, `z³ ≤ x` pins every scale this family needs:
`x ≥ 100^48`, `z ≤ x^{1/3}`, `log x ≤ 96·log Zf` (so `L' ≤ 192·log Zf` and
`log z ≤ 32·log Zf`), the pair-count legality at `(v,w)`, the explicit sift-floor
soundness `Zf < n₊` (house amendment catch #245), and the Mertens absorb `≤ 2·log z`. -/

/-- The `x`-floor: `x ≥ 100^48` (from `z ≥ 100^16` and `x ≥ z³`). -/
lemma T1_x_ge {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    (100 : ℝ) ^ 48 ≤ x := by
  have hzr : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
  calc (100 : ℝ) ^ 48 = ((100 : ℝ) ^ 16) ^ 3 := by
        rw [show (48 : ℕ) = 16 * 3 from rfl, pow_mul]
    _ ≤ (z : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hzr 3
    _ ≤ (x : ℝ) := hzx

/-- The scale `z ≤ x^{1/3}` (from `z³ ≤ x`). -/
lemma T1_z_le_rpow {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    (z : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  have h3 : (((z : ℝ) ^ 3) ^ ((1 : ℝ) / 3)) = z := by
    rw [← Real.rpow_natCast (z : ℝ) 3, ← Real.rpow_mul hz0,
        show ((3 : ℕ) : ℝ) * ((1 : ℝ) / 3) = 1 by norm_num, Real.rpow_one]
  rw [← h3]
  exact Real.rpow_le_rpow (by positivity) hzx (by norm_num)

/-- `log Zf > 0` (`Zf ≥ 100`). -/
lemma T1_logZf_pos {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    0 < Real.log (Zf x) := by
  have h100 : 100 ≤ Zf x := Zf_ge_100 hz100 hzx
  exact Real.log_pos (by exact_mod_cast (by omega : 1 < Zf x))

/-- **The sift-floor soundness** (house amendment catch #245): a cofactor `P` with
    `P·v = n > x` and `v ≤ z` exceeds `Zf` — `Zf·z ≤ x^{1/48}·x^{1/3} ≤ x < P·v ≤ P·z`. -/
lemma T1_cofactor_gt_Zf {z x P v : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (hxP : x < P * v) (hvz : v ≤ z) : Zf x < P := by
  have hz0 : (0 : ℝ) < z := by
    have h : (0 : ℕ) < z := lt_of_lt_of_le (by norm_num) hz100
    exact_mod_cast h
  have h1x : (1 : ℝ) ≤ x := le_trans (by norm_num) (T1_x_ge hz100 hzx)
  have hx0 : (0 : ℝ) < x := by linarith
  have hZfle : ((Zf x : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 48) :=
    Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have hmulle : ((Zf x : ℕ) : ℝ) * z ≤ (x : ℝ) := by
    calc ((Zf x : ℕ) : ℝ) * z ≤ (x : ℝ) ^ ((1 : ℝ) / 48) * (x : ℝ) ^ ((1 : ℝ) / 3) :=
          mul_le_mul hZfle (T1_z_le_rpow hz100 hzx) hz0.le (by positivity)
      _ = (x : ℝ) ^ ((1 : ℝ) / 48 + (1 : ℝ) / 3) := (Real.rpow_add hx0 _ _).symm
      _ ≤ (x : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1x (by norm_num)
      _ = x := Real.rpow_one _
  have hPz : (x : ℝ) < (P : ℝ) * z := by
    have hPv : (x : ℝ) < (P : ℝ) * v := by exact_mod_cast hxP
    have hle : (P : ℝ) * v ≤ (P : ℝ) * z :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hvz) (Nat.cast_nonneg P)
    linarith
  have hfin : ((Zf x : ℕ) : ℝ) < P :=
    lt_of_mul_lt_mul_right (lt_of_le_of_lt hmulle hPz) hz0.le
  exact_mod_cast hfin

/-- `log x ≤ 96·log Zf` (`x^{1/48} < Zf + 1 ≤ Zf²`, so `x ≤ Zf^96`). -/
lemma T1_logx_le_logZf {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    Real.log x ≤ 96 * Real.log (Zf x) := by
  have h1x : (1 : ℝ) ≤ x := le_trans (by norm_num) (T1_x_ge hz100 hzx)
  have hx0 : (0 : ℝ) < x := by linarith
  have h100 : 100 ≤ Zf x := Zf_ge_100 hz100 hzx
  have hfl : (x : ℝ) ^ ((1 : ℝ) / 48) < (Zf x : ℝ) + 1 := Nat.lt_floor_add_one _
  have hZf2 : ((Zf x : ℕ) : ℝ) + 1 ≤ ((Zf x : ℕ) : ℝ) ^ 2 := by
    have h2 : (2 : ℝ) ≤ ((Zf x : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ Zf x)
    nlinarith
  have hxle : (x : ℝ) ≤ ((Zf x : ℕ) : ℝ) ^ 96 := by
    have hxeq : ((x : ℝ) ^ ((1 : ℝ) / 48)) ^ (48 : ℕ) = x := by
      rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 48)) 48, ← Real.rpow_mul hx0.le,
          show (1 : ℝ) / 48 * ((48 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    calc (x : ℝ) = ((x : ℝ) ^ ((1 : ℝ) / 48)) ^ (48 : ℕ) := hxeq.symm
      _ ≤ (((Zf x : ℕ) : ℝ) ^ 2) ^ (48 : ℕ) :=
          pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) (le_trans hfl.le hZf2) 48
      _ = ((Zf x : ℕ) : ℝ) ^ 96 := by rw [← pow_mul]
  calc Real.log x ≤ Real.log (((Zf x : ℕ) : ℝ) ^ 96) := Real.log_le_log hx0 hxle
    _ = 96 * Real.log (Zf x) := by rw [Real.log_pow]; norm_num

/-- `L' = log(2x+2) ≤ 192·log Zf` (`2x+2 ≤ x²` at `x ≥ 3`). -/
lemma T1_Lwin_le_logZf {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    Lwin x ≤ 192 * Real.log (Zf x) := by
  have h3x : (3 : ℝ) ≤ x := le_trans (by norm_num) (T1_x_ge hz100 hzx)
  have hx0 : (0 : ℝ) < x := by linarith
  have hsq : 2 * (x : ℝ) + 2 ≤ (x : ℝ) ^ 2 := by nlinarith
  have hL2 : Lwin x ≤ 2 * Real.log x := by
    rw [Lwin]
    calc Real.log (2 * (x : ℝ) + 2) ≤ Real.log ((x : ℝ) ^ 2) :=
          Real.log_le_log (by linarith) hsq
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  calc Lwin x ≤ 2 * Real.log x := hL2
    _ ≤ 2 * (96 * Real.log (Zf x)) := by
        have := T1_logx_le_logZf hz100 hzx; linarith
    _ = 192 * Real.log (Zf x) := by ring

/-- `log z ≤ 32·log Zf` (`3·log z = log z³ ≤ log x ≤ 96·log Zf`). -/
lemma T1_logz_le_logZf {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    Real.log z ≤ 32 * Real.log (Zf x) := by
  have h1x : (1 : ℝ) ≤ x := le_trans (by norm_num) (T1_x_ge hz100 hzx)
  have hz0 : (0 : ℝ) < z := by
    have h : (0 : ℕ) < z := lt_of_lt_of_le (by norm_num) hz100
    exact_mod_cast h
  have h3 : 3 * Real.log z = Real.log ((z : ℝ) ^ 3) := by rw [Real.log_pow]; norm_num
  have hle : Real.log ((z : ℝ) ^ 3) ≤ Real.log x := Real.log_le_log (by positivity) hzx
  have := T1_logx_le_logZf hz100 hzx
  linarith

/-- `6 ≤ log z` (`z ≥ 100^16` and `e² < 10`). -/
lemma T1_log_z_ge {z : ℕ} (hz100 : 100 ^ 16 ≤ z) : 6 ≤ Real.log z := by
  have hexp2 : Real.exp 2 < 10 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have hlog10 : (2 : ℝ) ≤ Real.log 10 :=
    (Real.le_log_iff_exp_le (by norm_num)).mpr hexp2.le
  have hz : ((100 : ℝ) ^ 16) ≤ (z : ℝ) := by exact_mod_cast hz100
  have hlog : Real.log ((100 : ℝ) ^ 16) ≤ Real.log z :=
    Real.log_le_log (by positivity) hz
  have h100 : Real.log ((100 : ℝ) ^ 16) = 32 * Real.log 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, ← pow_mul, Real.log_pow]
    norm_num
  rw [h100] at hlog
  linarith

/-- **The pair-count legality at `(v,w)`.**  For `v,w ≤ z`:
    `v·w·Zf⁸·(log Zf)² ≤ x^{2/3}·x^{1/6}·x^{1/12} = x^{11/12} ≤ 32x` (using
    `(log x)² ≤ z^{1/4} ≤ x^{1/12}` from `hz8`). -/
lemma T1_legality {z x v w : ℕ} (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z)
    (hzx : (z : ℝ) ^ 3 ≤ x) (hv : (v : ℝ) ≤ z) (hw : (w : ℝ) ≤ z) :
    (v : ℝ) * w * (Zf x : ℝ) ^ 8 * Real.log (Zf x) ^ 2 ≤ 32 * x := by
  have h1x : (1 : ℝ) ≤ x := le_trans (by norm_num) (T1_x_ge hz100 hzx)
  have hx0 : (0 : ℝ) < x := by linarith
  have hz0 : (0 : ℝ) < z := by
    have h : (0 : ℕ) < z := lt_of_lt_of_le (by norm_num) hz100
    exact_mod_cast h
  have hzle := T1_z_le_rpow hz100 hzx
  have hv' : (v : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := hv.trans hzle
  have hw' : (w : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := hw.trans hzle
  -- `Zf⁸ ≤ x^{1/6}`
  have hZf8 : ((Zf x : ℕ) : ℝ) ^ 8 ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := by
    have hle : ((Zf x : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 48) :=
      Nat.floor_le (Real.rpow_nonneg hx0.le _)
    calc ((Zf x : ℕ) : ℝ) ^ 8 ≤ ((x : ℝ) ^ ((1 : ℝ) / 48)) ^ (8 : ℕ) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hle 8
      _ = (x : ℝ) ^ ((1 : ℝ) / 48 * ((8 : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 48)) 8, ← Real.rpow_mul hx0.le]
      _ = (x : ℝ) ^ ((1 : ℝ) / 6) := by norm_num
  -- `(log Zf)² ≤ (log x)² ≤ z^{1/4} ≤ x^{1/12}`
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg h1x
  have hlogZf2 : Real.log (Zf x) ^ 2 ≤ (x : ℝ) ^ ((1 : ℝ) / 12) := by
    have hZfx : ((Zf x : ℕ) : ℝ) ≤ x :=
      le_trans (Nat.floor_le (Real.rpow_nonneg hx0.le _))
        (by calc (x : ℝ) ^ ((1 : ℝ) / 48) ≤ (x : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1x (by norm_num)
            _ = x := Real.rpow_one _)
    have h100 : 100 ≤ Zf x := Zf_ge_100 hz100 hzx
    have hZf1 : (1 : ℝ) ≤ ((Zf x : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ Zf x)
    have hlogZf_le : Real.log (Zf x) ≤ Real.log x := Real.log_le_log (by linarith) hZfx
    have hlx2 : Real.log x ^ 2 ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := by
      have hlogxLwin : Real.log x ≤ Lwin x := by
        rw [Lwin]; exact Real.log_le_log hx0 (by linarith)
      have hpow8 : Real.log x ^ 8 ≤ (z : ℝ) :=
        le_trans (pow_le_pow_left₀ hlogx0 hlogxLwin 8) hz8
      have hq : ((z : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = z := by
        rw [← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hz0.le,
            show (1 : ℝ) / 4 * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
      refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (Real.rpow_nonneg hz0.le _) ?_
      rw [hq, ← pow_mul]
      exact hpow8
    calc Real.log (Zf x) ^ 2 ≤ Real.log x ^ 2 :=
          pow_le_pow_left₀ (Real.log_nonneg hZf1) hlogZf_le 2
      _ ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := hlx2
      _ ≤ ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow hz0.le hzle (by norm_num)
      _ = (x : ℝ) ^ ((1 : ℝ) / 12) := by
          rw [← Real.rpow_mul hx0.le]; norm_num
  -- combine the four factors
  have hA : (v : ℝ) * w ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3) :=
    mul_le_mul hv' hw' (Nat.cast_nonneg w) (by positivity)
  have hB : (v : ℝ) * w * ((Zf x : ℕ) : ℝ) ^ 8
      ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 6) :=
    mul_le_mul hA hZf8 (by positivity) (by positivity)
  calc (v : ℝ) * w * (Zf x : ℝ) ^ 8 * Real.log (Zf x) ^ 2
      ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 6)
          * (x : ℝ) ^ ((1 : ℝ) / 12) :=
        mul_le_mul hB hlogZf2 (sq_nonneg _) (by positivity)
    _ = (x : ℝ) ^ ((1 : ℝ) / 3 + (1 : ℝ) / 3 + (1 : ℝ) / 6 + (1 : ℝ) / 12) := by
        rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_add hx0]
    _ ≤ (x : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1x (by norm_num)
    _ = x := Real.rpow_one _
    _ ≤ 32 * x := by linarith

/-- **The Mertens absorb.**  `Σ_{1<v<z} Λ(v)/v ≤ log z + (log 4 + 4) ≤ 2·log z`. -/
lemma T1_mertens_le {z : ℕ} (hz100 : 100 ^ 16 ≤ z) :
    ∑ v ∈ Finset.Ioo 1 z, Λ v / v ≤ 2 * Real.log z := by
  have h6 := T1_log_z_ge hz100
  have hsub : Finset.Ioo 1 z ⊆ Finset.Ioc 0 z := fun v hv => by
    rw [Finset.mem_Ioo] at hv; rw [Finset.mem_Ioc]; omega
  have h1 : ∑ v ∈ Finset.Ioo 1 z, Λ v / v ≤ ∑ d ∈ Finset.Ioc 0 z, Λ d / d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg i))
  have h2 := mertens_vonMangoldt_div_le (N := z) (by omega : 1 ≤ z)
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    norm_num
    linarith
  linarith

/-! ## §2 — the T1 per-term structure

On the T1 family the left factor collapses exactly: `Λ̃(m) = f(m₊)·Λ(m₋) = 2·Λ(m₋)` when
`m₊` is prime and `m₋` a prime power; blocks with `ω(m₋) ≥ 2` kill the term. -/

/-- `1 < d` not a prime power forces `ω(d) ≥ 2`. -/
lemma T1_two_le_card_of_not_pp {d : ℕ} (h1 : 1 < d) (hnpp : ¬ IsPrimePow d) :
    2 ≤ d.primeFactors.card := by
  rcases Nat.lt_trichotomy d.primeFactors.card 1 with hc | hc | hc
  · have hc0 : d.primeFactors.card = 0 := by omega
    rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hc0) with h | h <;> omega
  · exact absurd (isPrimePow_iff_card_primeFactors_eq_one.mpr hc) hnpp
  · omega

/-- `m₋ ∣ m`. -/
lemma T1_nMinus_dvd (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ}
    (hm0 : m ≠ 0) (hcop : Nat.Coprime m q) : nMinus χ m ∣ m :=
  ⟨nPlus χ m, by rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq hm0 hcop⟩

/-- **The T1 collapse.**  `m₊` prime and `m₋` a prime power give `Λ̃(m) = 2·Λ(m₋)`
    (`f(m₊) = 2^{ω(m₊)} = 2`). -/
lemma T1_lamTilde_eq_two_mul (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ}
    (hm0 : m ≠ 0) (hcop : Nat.Coprime m q) (hP : (nPlus χ m).Prime)
    (hpp : IsPrimePow (nMinus χ m)) :
    LamTilde χ m = 2 * Λ (nMinus χ m) := by
  have hf : fChiSum χ (nPlus χ m) = 2 := by
    rw [← fChiArith_eq_fChiSum,
        fChiArith_eq_two_pow χ hsq (nPlus_pos χ m).ne' (fun p hp => nPlus_sign hp),
        hP.primeFactors, Finset.card_singleton, pow_one]
  rw [LamTilde_eq_single_of_card_one χ hsq hm0 hcop hpp, hf]

/-- A divisor of an odd number is odd. -/
lemma T1_odd_of_dvd {d n : ℕ} (hdvd : d ∣ n) (hn : Odd n) : Odd d := by
  rcases Nat.even_or_odd d with he | ho
  · exfalso
    obtain ⟨c, hc⟩ := (even_iff_two_dvd.mp he).trans hdvd
    obtain ⟨k, hk⟩ := hn
    omega
  · exact ho

/-- `m₋ = 1` gives `m = m₊` (the edge shape: `m` itself is the `χ=+1` part). -/
lemma T1_eq_nPlus_of_nMinus_one (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ}
    (hm0 : m ≠ 0) (hcop : Nat.Coprime m q) (hM1 : nMinus χ m = 1) : m = nPlus χ m := by
  have h := eq_nPlus_mul_nMinus χ hsq hm0 hcop
  rw [hM1, mul_one] at h
  exact h

/-! ## §3 — the fiber machinery

A T1 fiber at `(v,w)` embeds in the pair-count set at `(d₁,d₂) = (v,w)`, `Z = Zf x`:
the base conditions `v ∣ n`, `w ∣ n+2` hold by the block identities, and the sifted
cofactor product `(n/v)·((n+2)/w) = n₊·(n+2)₊` is a product of primes `> Zf`
(sift-floor soundness). -/

/-- **The fiber embedding.**  A T1 fiber at `(v,w)` sits inside the pair-count filter. -/
lemma T1_fiber_subset (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x v w : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) (hvz : v ≤ z) (hwz : w ≤ z)
    {S : Finset ℕ} (hS : S ⊆ l2cWindow χ z x)
    (hmem : ∀ n ∈ S, (nPlus χ n).Prime ∧ (nPlus χ (n + 2)).Prime ∧
      nMinus χ n = v ∧ nMinus χ (n + 2) = w) :
    S ⊆ (baseSet x v w).filter
      (fun n => Nat.Coprime (primorial (Zf x)) ((n / v) * ((n + 2) / w))) := by
  intro n hn
  obtain ⟨hP, hU, hveq, hweq⟩ := hmem n hn
  have hnw := hS hn
  have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hnw
  have hcopn : Nat.Coprime n q := l2cWindow_coprime χ hnw
  have hcopn2 : Nat.Coprime (n + 2) q := l2cWindow_coprime_add_two χ hnw
  have hv0 : 0 < v := hveq ▸ nMinus_pos χ n
  have hw0 : 0 < w := hweq ▸ nMinus_pos χ (n + 2)
  have hfn : n = nPlus χ n * v := by
    have h := eq_nPlus_mul_nMinus χ hsq hn0 hcopn
    rw [hveq] at h; exact h
  have hfn2 : n + 2 = nPlus χ (n + 2) * w := by
    have h := eq_nPlus_mul_nMinus χ hsq (by omega : n + 2 ≠ 0) hcopn2
    rw [hweq] at h; exact h
  have hxlt : x < n := l2cWindow_lt χ hnw
  have hdivn : n / v = nPlus χ n := Nat.div_eq_of_eq_mul_left hv0 hfn
  have hdivn2 : (n + 2) / w = nPlus χ (n + 2) := Nat.div_eq_of_eq_mul_left hw0 hfn2
  have hPZf : Zf x < nPlus χ n :=
    T1_cofactor_gt_Zf hz100 hzx (by omega : x < nPlus χ n * v) hvz
  have hUZf : Zf x < nPlus χ (n + 2) :=
    T1_cofactor_gt_Zf hz100 hzx (by omega : x < nPlus χ (n + 2) * w) hwz
  rw [Finset.mem_filter, baseSet, Finset.mem_filter]
  refine ⟨⟨l2cWindow_subset χ z x hnw, ?_, ?_⟩, ?_⟩
  · exact ⟨nPlus χ n, by conv_lhs => rw [hfn, Nat.mul_comm]⟩
  · exact ⟨nPlus χ (n + 2), by conv_lhs => rw [hfn2, Nat.mul_comm]⟩
  · rw [hdivn, hdivn2]
    exact (T1_coprime_primorial_of_prime_lt hP hPZf).mul_right
      (T1_coprime_primorial_of_prime_lt hU hUZf)

/-- **The fiber count.**  A T1 fiber at `(v,w)` has at most `2048·x/(vw·(log Zf)²)`
    elements (`l2c_pair_count_clean` at `Z = Zf` + the totient ratio `≤ 16`). -/
lemma T1_fiber_card_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x v w : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (hvz : v ≤ z) (hwz : w ≤ z)
    (hppv : IsPrimePow v ∨ v = 1) (hppw : IsPrimePow w ∨ w = 1)
    (hov : Odd v) (how : Odd w) (hcop : Nat.Coprime v w)
    {S : Finset ℕ} (hS : S ⊆ l2cWindow χ z x)
    (hmem : ∀ n ∈ S, (nPlus χ n).Prime ∧ (nPlus χ (n + 2)).Prime ∧
      nMinus χ n = v ∧ nMinus χ (n + 2) = w) :
    (S.card : ℝ) ≤ 2048 * x / ((v : ℝ) * w * Real.log (Zf x) ^ 2) := by
  have hv0 : 0 < v := T1_pos_of_pp_or_one hppv
  have hw0 : 0 < w := T1_pos_of_pp_or_one hppw
  have hcard : (S.card : ℝ)
      ≤ (((baseSet x v w).filter
          (fun n => Nat.Coprime (primorial (Zf x)) ((n / v) * ((n + 2) / w)))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (T1_fiber_subset χ hsq hz100 hzx hvz hwz hS hmem)
  have hcount := l2c_pair_count_clean (x := x) (d₁ := v) (d₂ := w) (Z := Zf x)
    (Zf_ge_100 hz100 hzx) hv0 hw0 hov how hcop
    (T1_legality hz100 hz8 hzx (by exact_mod_cast hvz) (by exact_mod_cast hwz))
  have hratio := T1_totient_ratio_sq_le hppv hppw hcop
  have hxvw0 : (0 : ℝ) ≤ (x : ℝ) / ((v : ℝ) * w) := by positivity
  have hmono : 128 * ((v * w : ℝ) / (Nat.totient (v * w))) ^ 2 * ((x : ℝ) / ((v : ℝ) * w))
        / Real.log (Zf x) ^ 2
      ≤ 128 * 16 * ((x : ℝ) / ((v : ℝ) * w)) / Real.log (Zf x) ^ 2 := by
    gcongr
  calc (S.card : ℝ)
      ≤ 128 * ((v * w : ℝ) / (Nat.totient (v * w))) ^ 2 * ((x : ℝ) / ((v : ℝ) * w))
          / Real.log (Zf x) ^ 2 := hcard.trans hcount
    _ ≤ 128 * 16 * ((x : ℝ) / ((v : ℝ) * w)) / Real.log (Zf x) ^ 2 := hmono
    _ = 2048 * x / ((v : ℝ) * w * Real.log (Zf x) ^ 2) := by ring

/-- **The main per-fiber bound.**  On a fiber at `(v,w)`, `1 < v,w`, every term is
    `≤ 2Λ(v)·2Λ(w)` (T1 collapse; zero unless both blocks are prime powers), so the fiber
    sum is `≤ 2048·x/(vw·(log Zf)²)·4Λ(v)Λ(w)`. -/
lemma T1_fiber_sum_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x v w : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (hv1 : 1 < v) (hvz : v ≤ z) (hw1 : 1 < w) (hwz : w ≤ z)
    {S : Finset ℕ} (hS : S ⊆ l2cWindow χ z x)
    (hmem : ∀ n ∈ S, (nPlus χ n).Prime ∧ (nPlus χ (n + 2)).Prime ∧
      Odd v ∧ Odd w ∧ nMinus χ n = v ∧ nMinus χ (n + 2) = w) :
    ∑ n ∈ S, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ 2048 * x / ((v : ℝ) * w * Real.log (Zf x) ^ 2) * (4 * (Λ v * Λ w)) := by
  have hb0 : (0 : ℝ) ≤ 4 * (Λ v * Λ w) :=
    mul_nonneg (by norm_num) (mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)
  have hRHS0 : (0 : ℝ) ≤ 2048 * x / ((v : ℝ) * w * Real.log (Zf x) ^ 2)
      * (4 * (Λ v * Λ w)) :=
    mul_nonneg (div_nonneg (by positivity) (by positivity)) hb0
  rcases S.eq_empty_or_nonempty with rfl | ⟨n₀, hn₀⟩
  · simpa using hRHS0
  obtain ⟨hP₀, hU₀, hov, how, hveq₀, hweq₀⟩ := hmem n₀ hn₀
  by_cases hppv : IsPrimePow v
  swap
  · -- `ω(v) ≥ 2`: every left factor vanishes
    have hzero : ∀ n ∈ S, (LamTilde χ n - Λ n) * LamTilde χ (n + 2) = 0 := by
      intro n hn
      obtain ⟨_, _, _, _, hveq, _⟩ := hmem n hn
      have hnw := hS hn
      have hcardn : 2 ≤ (nMinus χ n).primeFactors.card := by
        rw [hveq]; exact T1_two_le_card_of_not_pp hv1 hppv
      rw [lamTilde_sub_vonMangoldt_eq_zero_of_two_le_card χ hsq (l2cWindow_ne_zero χ hnw)
          (l2cWindow_coprime χ hnw) hcardn, zero_mul]
    calc ∑ n ∈ S, (LamTilde χ n - Λ n) * LamTilde χ (n + 2) = 0 := Finset.sum_eq_zero hzero
      _ ≤ _ := hRHS0
  by_cases hppw : IsPrimePow w
  swap
  · -- `ω(w) ≥ 2`: every right factor vanishes
    have hzero : ∀ n ∈ S, (LamTilde χ n - Λ n) * LamTilde χ (n + 2) = 0 := by
      intro n hn
      obtain ⟨_, _, _, _, _, hweq⟩ := hmem n hn
      have hnw := hS hn
      have hcardn : 2 ≤ (nMinus χ (n + 2)).primeFactors.card := by
        rw [hweq]; exact T1_two_le_card_of_not_pp hw1 hppw
      rw [LamTilde_eq_zero_of_two_le_card χ hsq (by omega : n + 2 ≠ 0)
          (l2cWindow_coprime_add_two χ hnw) hcardn, mul_zero]
    calc ∑ n ∈ S, (LamTilde χ n - Λ n) * LamTilde χ (n + 2) = 0 := Finset.sum_eq_zero hzero
      _ ≤ _ := hRHS0
  -- main case: both blocks prime powers
  have hcop : Nat.Coprime v w := by
    have hnw₀ := hS hn₀
    have hvd : v ∣ n₀ := hveq₀ ▸ T1_nMinus_dvd χ hsq (l2cWindow_ne_zero χ hnw₀)
      (l2cWindow_coprime χ hnw₀)
    have hwd : w ∣ n₀ + 2 := hweq₀ ▸ T1_nMinus_dvd χ hsq (by omega)
      (l2cWindow_coprime_add_two χ hnw₀)
    have hg2 : Nat.gcd v w ∣ 2 := by
      have h1 : Nat.gcd v w ∣ n₀ := (Nat.gcd_dvd_left v w).trans hvd
      have h2 : Nat.gcd v w ∣ n₀ + 2 := (Nat.gcd_dvd_right v w).trans hwd
      simpa using Nat.dvd_sub h2 h1
    rcases (Nat.dvd_prime Nat.prime_two).mp hg2 with h1 | h2
    · exact h1
    · exfalso
      obtain ⟨c, hc⟩ : (2 : ℕ) ∣ v := h2 ▸ Nat.gcd_dvd_left v w
      obtain ⟨k, hk⟩ := hov
      omega
  have hterm : ∀ n ∈ S, (LamTilde χ n - Λ n) * LamTilde χ (n + 2) ≤ 4 * (Λ v * Λ w) := by
    intro n hn
    obtain ⟨hP, hU, _, _, hveq, hweq⟩ := hmem n hn
    have hnw := hS hn
    have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hnw
    have h1 : LamTilde χ n = 2 * Λ v := by
      rw [← hveq]
      exact T1_lamTilde_eq_two_mul χ hsq hn0 (l2cWindow_coprime χ hnw) hP
        (by rw [hveq]; exact hppv)
    have h2 : LamTilde χ (n + 2) = 2 * Λ w := by
      rw [← hweq]
      exact T1_lamTilde_eq_two_mul χ hsq (by omega) (l2cWindow_coprime_add_two χ hnw) hU
        (by rw [hweq]; exact hppw)
    have hsub : LamTilde χ n - Λ n ≤ 2 * Λ v := by
      rw [← h1]; exact sub_le_self _ vonMangoldt_nonneg
    calc (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
        = (LamTilde χ n - Λ n) * (2 * Λ w) := by rw [h2]
      _ ≤ (2 * Λ v) * (2 * Λ w) := mul_le_mul_of_nonneg_right hsub
          (mul_nonneg (by norm_num) vonMangoldt_nonneg)
      _ = 4 * (Λ v * Λ w) := by ring
  have hsum := Finset.sum_le_card_nsmul S _ _ hterm
  rw [nsmul_eq_mul] at hsum
  have hcount := T1_fiber_card_le χ hsq hz100 hz8 hzx hvz hwz (Or.inl hppv) (Or.inl hppw)
    hov how hcop hS (fun n hn => by
      obtain ⟨a, b, _, _, c, d⟩ := hmem n hn; exact ⟨a, b, c, d⟩)
  calc ∑ n ∈ S, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ (S.card : ℝ) * (4 * (Λ v * Λ w)) := hsum
    _ ≤ 2048 * x / ((v : ℝ) * w * Real.log (Zf x) ^ 2) * (4 * (Λ v * Λ w)) :=
        mul_le_mul_of_nonneg_right hcount hb0

/-- **The edge per-fiber bound** (`w = 1`: `n+2` prime).  Every term is `≤ 2Λ(v)·L'`,
    so the fiber sum is `≤ 2048·x/(v·(log Zf)²)·2Λ(v)L'`. -/
lemma T1_edge_fiber_sum_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x v : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (hv1 : 1 < v) (hvz : v ≤ z)
    {S : Finset ℕ} (hS : S ⊆ l2cWindow χ z x)
    (hmem : ∀ n ∈ S, (nPlus χ n).Prime ∧ (nPlus χ (n + 2)).Prime ∧
      Odd v ∧ nMinus χ n = v ∧ nMinus χ (n + 2) = 1) :
    ∑ n ∈ S, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ 2048 * x / ((v : ℝ) * Real.log (Zf x) ^ 2) * (2 * Λ v * Lwin x) := by
  have hb0 : (0 : ℝ) ≤ 2 * Λ v * Lwin x :=
    mul_nonneg (mul_nonneg (by norm_num) vonMangoldt_nonneg) (Lwin_nonneg x)
  have hRHS0 : (0 : ℝ) ≤ 2048 * x / ((v : ℝ) * Real.log (Zf x) ^ 2)
      * (2 * Λ v * Lwin x) :=
    mul_nonneg (div_nonneg (by positivity) (by positivity)) hb0
  rcases S.eq_empty_or_nonempty with rfl | ⟨n₀, hn₀⟩
  · simpa using hRHS0
  obtain ⟨hP₀, hU₀, hov, hveq₀, hweq₀⟩ := hmem n₀ hn₀
  by_cases hppv : IsPrimePow v
  swap
  · have hzero : ∀ n ∈ S, (LamTilde χ n - Λ n) * LamTilde χ (n + 2) = 0 := by
      intro n hn
      obtain ⟨_, _, _, hveq, _⟩ := hmem n hn
      have hnw := hS hn
      have hcardn : 2 ≤ (nMinus χ n).primeFactors.card := by
        rw [hveq]; exact T1_two_le_card_of_not_pp hv1 hppv
      rw [lamTilde_sub_vonMangoldt_eq_zero_of_two_le_card χ hsq (l2cWindow_ne_zero χ hnw)
          (l2cWindow_coprime χ hnw) hcardn, zero_mul]
    calc ∑ n ∈ S, (LamTilde χ n - Λ n) * LamTilde χ (n + 2) = 0 := Finset.sum_eq_zero hzero
      _ ≤ _ := hRHS0
  have hterm : ∀ n ∈ S, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ (2 * Λ v) * Lwin x := by
    intro n hn
    obtain ⟨hP, hU, _, hveq, hweq⟩ := hmem n hn
    have hnw := hS hn
    have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hnw
    have h1 : LamTilde χ n = 2 * Λ v := by
      rw [← hveq]
      exact T1_lamTilde_eq_two_mul χ hsq hn0 (l2cWindow_coprime χ hnw) hP
        (by rw [hveq]; exact hppv)
    have hsub : LamTilde χ n - Λ n ≤ 2 * Λ v := by
      rw [← h1]; exact sub_le_self _ vonMangoldt_nonneg
    -- `n+2` is prime (edge shape), so `Λ̃(n+2) = Λ(n+2) ≤ log(n+2) ≤ L'`
    have hnp2 : (n + 2).Prime := by
      have h := T1_eq_nPlus_of_nMinus_one χ hsq (by omega : n + 2 ≠ 0)
        (l2cWindow_coprime_add_two χ hnw) hweq
      rw [h]; exact hU
    have h2 : LamTilde χ (n + 2) ≤ Lwin x := by
      have heq : LamTilde χ (n + 2) = Λ (n + 2) :=
        sub_eq_zero.mp (lamTilde_sub_vonMangoldt_eq_zero_of_prime χ hsq hnp2)
      rw [heq, Lwin]
      refine le_trans vonMangoldt_le_log (Real.log_le_log (by positivity) ?_)
      have hle : ((n : ℕ) : ℝ) ≤ 2 * x := by exact_mod_cast l2cWindow_le χ hnw
      push_cast
      linarith
    exact mul_le_mul hsub h2 (lamTilde_nonneg χ hsq (n + 2))
      (mul_nonneg (by norm_num) vonMangoldt_nonneg)
  have hsum := Finset.sum_le_card_nsmul S _ _ hterm
  rw [nsmul_eq_mul] at hsum
  have hcount := T1_fiber_card_le χ hsq hz100 hz8 hzx hvz
    (by have : 0 < z := lt_of_lt_of_le (by norm_num) hz100; omega : 1 ≤ z)
    (Or.inl hppv) (Or.inr rfl) hov odd_one (Nat.coprime_one_right v) hS
    (fun n hn => by obtain ⟨a, b, _, c, d⟩ := hmem n hn; exact ⟨a, b, c, d⟩)
  calc ∑ n ∈ S, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ (S.card : ℝ) * ((2 * Λ v) * Lwin x) := hsum
    _ ≤ 2048 * x / ((v : ℝ) * ((1 : ℕ) : ℝ) * Real.log (Zf x) ^ 2)
          * ((2 * Λ v) * Lwin x) := mul_le_mul_of_nonneg_right hcount hb0
    _ = 2048 * x / ((v : ℝ) * Real.log (Zf x) ^ 2) * (2 * Λ v * Lwin x) := by
        norm_num

/-! ## §4 — the J1 scale comparisons

`x·(log z)²/(log Zf)² ≤ C·x·log z/L'` and `x·L'·log z/(log Zf)² ≤ C·x·log z/L'` — the
two shapes the fiberwise sums reduce to, both absolute multiples of `x/z₀ = x·log z/L'`. -/

/-- The main-row comparison: `8192·(x/(log Zf)²)·(2 log z)² ≤ 2^28·(x·log z/L')`. -/
lemma T1_scale_main {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    8192 * (x : ℝ) / Real.log (Zf x) ^ 2 * (2 * Real.log z * (2 * Real.log z))
      ≤ 2 ^ 28 * ((x : ℝ) * Real.log z / Lwin x) := by
  have hLZ := T1_logZf_pos hz100 hzx
  have h1x : (1 : ℝ) ≤ x := le_trans (by norm_num) (T1_x_ge hz100 hzx)
  have hLwin : 0 < Lwin x := by
    rw [Lwin]; exact Real.log_pos (by linarith)
  have hLwin' := T1_Lwin_le_logZf hz100 hzx
  have hlogz' := T1_logz_le_logZf hz100 hzx
  have hlogz0 : (0 : ℝ) ≤ Real.log z := by linarith [T1_log_z_ge hz100]
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hCB : Real.log z * Lwin x ≤ 6144 * Real.log (Zf x) ^ 2 := by
    calc Real.log z * Lwin x ≤ 32 * Real.log (Zf x) * (192 * Real.log (Zf x)) :=
          mul_le_mul hlogz' hLwin' (Lwin_nonneg x) (by positivity)
      _ = 6144 * Real.log (Zf x) ^ 2 := by ring
  rw [div_mul_eq_mul_div, ← mul_div_assoc,
      div_le_div_iff₀ (pow_pos hLZ 2) hLwin]
  have hint1 := mul_le_mul_of_nonneg_left hCB
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32768) hx0) hlogz0)
  have hint2 : (0 : ℝ) ≤ x * Real.log z * Real.log (Zf x) ^ 2 :=
    mul_nonneg (mul_nonneg hx0 hlogz0) (by positivity)
  nlinarith [hint1, hint2]

/-- The edge-row comparison: `4096·(x·L'/(log Zf)²)·(2 log z) ≤ 2^29·(x·log z/L')`. -/
lemma T1_scale_edge {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    4096 * (x : ℝ) * Lwin x / Real.log (Zf x) ^ 2 * (2 * Real.log z)
      ≤ 2 ^ 29 * ((x : ℝ) * Real.log z / Lwin x) := by
  have hLZ := T1_logZf_pos hz100 hzx
  have h1x : (1 : ℝ) ≤ x := le_trans (by norm_num) (T1_x_ge hz100 hzx)
  have hLwin : 0 < Lwin x := by
    rw [Lwin]; exact Real.log_pos (by linarith)
  have hLwin' := T1_Lwin_le_logZf hz100 hzx
  have hlogz0 : (0 : ℝ) ≤ Real.log z := by linarith [T1_log_z_ge hz100]
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hB2 : Lwin x ^ 2 ≤ 36864 * Real.log (Zf x) ^ 2 := by
    calc Lwin x ^ 2 ≤ (192 * Real.log (Zf x)) ^ 2 :=
          pow_le_pow_left₀ (Lwin_nonneg x) hLwin' 2
      _ = 36864 * Real.log (Zf x) ^ 2 := by ring
  rw [div_mul_eq_mul_div, ← mul_div_assoc,
      div_le_div_iff₀ (pow_pos hLZ 2) hLwin]
  have hint1 := mul_le_mul_of_nonneg_left hB2
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8192) hx0) hlogz0)
  have hint2 : (0 : ℝ) ≤ x * Real.log z * Real.log (Zf x) ^ 2 :=
    mul_nonneg (mul_nonneg hx0 hlogz0) (by positivity)
  nlinarith [hint1, hint2]

/-! ## §5 — the T1 slice, its sum, and the frozen `J1` bound -/

open Classical in
/-- **The T1 family slice** of the window: `n` odd (the explicit even-class guard, house
    amendment #246 — the even-block corner is a separate row), `n₊` and `(n+2)₊` both
    prime, blocks `1 < n₋ < z` and `(n+2)₋ < z` (odd automatically, `n₋ ∣ n`; `ω ≥ 2`
    blocks are retained — their terms vanish identically). -/
noncomputable def T1slice (χ : DirichletCharacter ℂ q) (z x : ℕ) : Finset ℕ :=
  (l2cWindow χ z x).filter (fun n =>
    Odd n ∧ (nPlus χ n).Prime ∧ (nPlus χ (n + 2)).Prime ∧
    1 < nMinus χ n ∧ nMinus χ n < z ∧ nMinus χ (n + 2) < z)

lemma T1slice_subset (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    T1slice χ z x ⊆ l2cWindow χ z x := Finset.filter_subset _ _

/-- **The T1 family sum** `Σ_{n ∈ T1slice} (Λ̃−Λ)(n)·Λ̃(n+2)` — the `E_L` T1 row. -/
noncomputable def ELT1 (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ T1slice χ z x, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)

open Classical in
/-- **The main half** (`1 < w`): fiber over `(v,w) ∈ (1,z)²`, count at `Zf`, weights
    `4Λ(v)Λ(w)`, Mertens twice: `≤ 2^28·x·log z/L'`. -/
lemma EL_T1_main_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ (T1slice χ z x).filter (fun n => 1 < nMinus χ (n + 2)),
      (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ 2 ^ 28 * ((x : ℝ) * Real.log z / Lwin x) := by
  classical
  have hmap : ∀ n ∈ (T1slice χ z x).filter (fun n => 1 < nMinus χ (n + 2)),
      (nMinus χ n, nMinus χ (n + 2)) ∈ Finset.Ioo 1 z ×ˢ Finset.Ioo 1 z := by
    intro n hn
    rw [Finset.mem_filter, T1slice, Finset.mem_filter] at hn
    obtain ⟨⟨_, _, _, _, hv1, hvz, hwz⟩, hw1⟩ := hn
    rw [Finset.mem_product]
    exact ⟨Finset.mem_Ioo.mpr ⟨hv1, hvz⟩, Finset.mem_Ioo.mpr ⟨hw1, hwz⟩⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hfiber : ∀ p ∈ Finset.Ioo 1 z ×ˢ Finset.Ioo 1 z,
      (∑ n ∈ ((T1slice χ z x).filter (fun n => 1 < nMinus χ (n + 2))).filter
          (fun n => (nMinus χ n, nMinus χ (n + 2)) = p),
        (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
      ≤ 2048 * x / ((p.1 : ℝ) * p.2 * Real.log (Zf x) ^ 2) * (4 * (Λ p.1 * Λ p.2)) := by
    intro p hp
    obtain ⟨v, w⟩ := p
    simp only [Finset.mem_product, Finset.mem_Ioo] at hp
    refine T1_fiber_sum_le χ hsq hz100 hz8 hzx hp.1.1 hp.1.2.le hp.2.1 hp.2.2.le
      (fun n hn => T1slice_subset χ z x
        (Finset.filter_subset _ _ (Finset.filter_subset _ _ hn)))
      (fun n hn => ?_)
    rw [Finset.mem_filter] at hn
    obtain ⟨hn', hpeq⟩ := hn
    rw [Prod.mk.injEq] at hpeq
    rw [Finset.mem_filter, T1slice, Finset.mem_filter] at hn'
    obtain ⟨⟨hnw, hodd, hP, hU, _, _, _⟩, _⟩ := hn'
    have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hnw
    have hov : Odd (nMinus χ n) :=
      T1_odd_of_dvd (T1_nMinus_dvd χ hsq hn0 (l2cWindow_coprime χ hnw)) hodd
    have hodd2 : Odd (n + 2) := by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩
    have how : Odd (nMinus χ (n + 2)) :=
      T1_odd_of_dvd (T1_nMinus_dvd χ hsq (by omega)
        (l2cWindow_coprime_add_two χ hnw)) hodd2
    exact ⟨hP, hU, hpeq.1 ▸ hov, hpeq.2 ▸ how, hpeq.1, hpeq.2⟩
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  have hcongr : ∑ p ∈ Finset.Ioo 1 z ×ˢ Finset.Ioo 1 z,
      2048 * (x : ℝ) / ((p.1 : ℝ) * p.2 * Real.log (Zf x) ^ 2) * (4 * (Λ p.1 * Λ p.2))
      = 8192 * x / Real.log (Zf x) ^ 2
        * ((∑ v ∈ Finset.Ioo 1 z, Λ v / (v : ℝ))
            * ∑ w ∈ Finset.Ioo 1 z, Λ w / (w : ℝ)) := by
    rw [Finset.sum_mul_sum, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    dsimp only
    ring
  rw [hcongr]
  have hmert := T1_mertens_le hz100
  have hsum0 : 0 ≤ ∑ v ∈ Finset.Ioo 1 z, Λ v / (v : ℝ) :=
    Finset.sum_nonneg fun i _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg i)
  have hlogz0 : (0 : ℝ) ≤ Real.log z := by linarith [T1_log_z_ge hz100]
  have hSS : (∑ v ∈ Finset.Ioo 1 z, Λ v / (v : ℝ)) * ∑ w ∈ Finset.Ioo 1 z, Λ w / (w : ℝ)
      ≤ 2 * Real.log z * (2 * Real.log z) :=
    mul_le_mul hmert hmert hsum0 (by linarith)
  calc 8192 * (x : ℝ) / Real.log (Zf x) ^ 2
        * ((∑ v ∈ Finset.Ioo 1 z, Λ v / (v : ℝ))
            * ∑ w ∈ Finset.Ioo 1 z, Λ w / (w : ℝ))
      ≤ 8192 * (x : ℝ) / Real.log (Zf x) ^ 2 * (2 * Real.log z * (2 * Real.log z)) :=
        mul_le_mul_of_nonneg_left hSS (by positivity)
    _ ≤ 2 ^ 28 * ((x : ℝ) * Real.log z / Lwin x) := T1_scale_main hz100 hzx

open Classical in
/-- **The edge half** (`w = 1`, so `n+2` prime): fiber over `v ∈ (1,z)`, count at `Zf`
    with `d₂ = 1`, weight `2Λ(v)·L'`, Mertens once: `≤ 2^29·x·log z/L'`. -/
lemma EL_T1_edge_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ (T1slice χ z x).filter (fun n => ¬ 1 < nMinus χ (n + 2)),
      (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ 2 ^ 29 * ((x : ℝ) * Real.log z / Lwin x) := by
  classical
  have hmap : ∀ n ∈ (T1slice χ z x).filter (fun n => ¬ 1 < nMinus χ (n + 2)),
      nMinus χ n ∈ Finset.Ioo 1 z := by
    intro n hn
    rw [Finset.mem_filter, T1slice, Finset.mem_filter] at hn
    obtain ⟨⟨_, _, _, _, hv1, hvz, _⟩, _⟩ := hn
    exact Finset.mem_Ioo.mpr ⟨hv1, hvz⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hfiber : ∀ v ∈ Finset.Ioo 1 z,
      (∑ n ∈ ((T1slice χ z x).filter (fun n => ¬ 1 < nMinus χ (n + 2))).filter
          (fun n => nMinus χ n = v),
        (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
      ≤ 2048 * x / ((v : ℝ) * Real.log (Zf x) ^ 2) * (2 * Λ v * Lwin x) := by
    intro v hv
    rw [Finset.mem_Ioo] at hv
    refine T1_edge_fiber_sum_le χ hsq hz100 hz8 hzx hv.1 hv.2.le
      (fun n hn => T1slice_subset χ z x
        (Finset.filter_subset _ _ (Finset.filter_subset _ _ hn)))
      (fun n hn => ?_)
    rw [Finset.mem_filter] at hn
    obtain ⟨hn', hveq⟩ := hn
    rw [Finset.mem_filter, T1slice, Finset.mem_filter] at hn'
    obtain ⟨⟨hnw, hodd, hP, hU, _, _, _⟩, hw1⟩ := hn'
    have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hnw
    have hov : Odd (nMinus χ n) :=
      T1_odd_of_dvd (T1_nMinus_dvd χ hsq hn0 (l2cWindow_coprime χ hnw)) hodd
    have hweq : nMinus χ (n + 2) = 1 := by
      have := nMinus_pos χ (n + 2); omega
    exact ⟨hP, hU, hveq ▸ hov, hveq, hweq⟩
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  have hcongr : ∑ v ∈ Finset.Ioo 1 z,
      2048 * (x : ℝ) / ((v : ℝ) * Real.log (Zf x) ^ 2) * (2 * Λ v * Lwin x)
      = 4096 * x * Lwin x / Real.log (Zf x) ^ 2
        * ∑ v ∈ Finset.Ioo 1 z, Λ v / (v : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [hcongr]
  have hmert := T1_mertens_le hz100
  have hc0 : (0 : ℝ) ≤ 4096 * (x : ℝ) * Lwin x / Real.log (Zf x) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg x)) (Lwin_nonneg x))
      (by positivity)
  calc 4096 * (x : ℝ) * Lwin x / Real.log (Zf x) ^ 2 * ∑ v ∈ Finset.Ioo 1 z, Λ v / (v : ℝ)
      ≤ 4096 * (x : ℝ) * Lwin x / Real.log (Zf x) ^ 2 * (2 * Real.log z) :=
        mul_le_mul_of_nonneg_left hmert hc0
    _ ≤ 2 ^ 29 * ((x : ℝ) * Real.log z / Lwin x) := T1_scale_edge hz100 hzx

/-- **The absolute T1 constant** `Cmain = 2^30` (main `2^28` + edge `2^29`; generous,
    no dependence on `χ`, `z`, `x`). -/
noncomputable def T1Cmain : ℝ := 2 ^ 30

lemma T1Cmain_pos : 0 < T1Cmain := by rw [T1Cmain]; positivity

/-- **`EL_T1_bound` — the frozen `J1` family budget** (freeze §S4, T1 row).  On the T1
    family (`n₊ = P` prime, `(n+2)₊ = U` prime, blocks `v,w < z`, `v > 1`, odd), the
    left-overshoot sum is absolutely bounded:

    `Σ_{T1} (Λ̃−Λ)(n)·Λ̃(n+2) ≤ Cmain·(x / z₀)`

    with `Cmain = T1Cmain = 2^30` absolute — NO `PretenseSum`, no `e^{z₀}`. -/
theorem EL_T1_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ELT1 χ z x ≤ T1Cmain * ((x : ℝ) / z0 z x) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (T1slice χ z x)
    (fun n => 1 < nMinus χ (n + 2)) (fun n => (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
  have hmain := EL_T1_main_le χ hsq hz100 hz8 hzx
  have hedge := EL_T1_edge_le χ hsq hz100 hz8 hzx
  have hz0eq : (x : ℝ) / z0 z x = (x : ℝ) * Real.log z / Lwin x := by
    rw [z0, div_div_eq_mul_div]
  have hQ0 : 0 ≤ (x : ℝ) * Real.log z / Lwin x := by
    have hlogz0 : (0 : ℝ) ≤ Real.log z := by linarith [T1_log_z_ge hz100]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg x) hlogz0) (Lwin_nonneg x)
  rw [ELT1, ← hsplit, T1Cmain, hz0eq]
  linarith [hmain, hedge, hQ0]

end Salt.HB
