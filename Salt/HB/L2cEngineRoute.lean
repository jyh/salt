/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cMop
import Salt.HB.MixedCount

/-!
# HB-L2c — the χ-blind engine route (CHI-SIEVE freeze, Wave 1)

This leaf routes **both** CHI-SIEVE sibling counts through the frozen unconditional
engine `hb_lemma8'_unconditional` (`MixedCount.lean`) at the small-prime-power modulus,
landing them in the master's `J1` row — chi-blind, `PretenseSum`-free.

* **R1 — the floors and the engine instantiations.**  The sieve-floor arithmetic
  (`Lwin ≤ 60·log(Z_f)`, the Mertens absorption `log z + log4+4 ≤ (9/8)log z`, the crude
  `ψ(z) ≤ z·L'`) plus both orientations of the general engine lemma
  (`engineRoute_card_right`/`_left`) with the totient fold `64·(m/φ m)² ≤ 144` for odd
  prime powers.
* **R2 — the `E_R` swap family.**  `erTsw_weightedCount_unconditional` fibers the
  `χ=−1`-block count over `w = (n+2)₋` into `engineRoute_card_right`, then Mertens + the
  floors give the `J1` row; `ER_Tsw'_bound_unconditional` peels via
  `ER_Tsw'_le_weightedCount`.
* **R3 — the class-(c) minus-prime-pair family.**  The sharp per-summand cap
  `cpair_summand_sharp` (no `exp` factor), then the complete dichotomy on the base prime
  `q'` of `(n+2)₋` vs `Z_f`: the rough branch fibers over `v = n₋` into
  `engineRoute_card_left`, the small branch is squarefull junk.

Single-writer file (`L2cEngineRoute.lean`); imports `L2cMop` and `MixedCount`, touches no
other file, and adds no axioms.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 (R1) — numeric log floors -/

/-- `4 ≤ log 100` (via `e⁴ < 100`). -/
lemma log_hundred_ge : (4 : ℝ) ≤ Real.log 100 := by
  have hexp4 : Real.exp 4 ≤ 100 := by
    have h1 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    calc Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := by
          exact pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 4
      _ ≤ 100 := by norm_num
  exact (Real.le_log_iff_exp_le (by norm_num)).mpr hexp4

/-- `log 2 ≤ 0.6932`. -/
lemma log_two_le : Real.log 2 ≤ 0.6932 := by
  have := Real.log_two_lt_d9; linarith

/-- `log 4 = 2·log 2`. -/
lemma log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

/-- In-regime lower floor on `x`: `100⁴⁸ ≤ x` from `100¹⁶ ≤ z` and `z³ ≤ x`. -/
lemma engine_x_ge {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    (100 : ℝ) ^ 48 ≤ (x : ℝ) := by
  have hzr : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
  calc (100 : ℝ) ^ 48 = ((100 : ℝ) ^ 16) ^ 3 := by rw [show (48 : ℕ) = 16 * 3 from rfl, pow_mul]
    _ ≤ (z : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hzr 3
    _ ≤ (x : ℝ) := hzx

/-! ## §1 (R1) — the sieve-floor gates -/

/-- **The `Z_f`/`L'` floor.**  `L' = log(2x+2) ≤ 60·log(Z_f x)` in-regime.  The floor loss
    `Z_f ≥ x^{1/48}/2` costs a `−log 2`; the `log x ≥ 192` margin absorbs it (`248·log2 <
    172 ≤ 192`). -/
lemma sixty_mul_log_Zf_ge_Lwin {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    Lwin x ≤ 60 * Real.log (Zf x) := by
  have hx48 : (100 : ℝ) ^ 48 ≤ (x : ℝ) := engine_x_ge hz100 hzx
  have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx48
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 100)) hx48
  -- `log x ≥ 192`
  have hlogx : (192 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (100 : ℝ) ^ 48) hx48
    rw [Real.log_pow] at h
    push_cast at h
    nlinarith [h, log_hundred_ge]
  -- `Lwin x ≤ 2·log2 + log x`
  have hLwin_ub : Lwin x ≤ 2 * Real.log 2 + Real.log x := by
    rw [Lwin]
    have h4x : (2 * (x : ℝ) + 2) ≤ 4 * x := by linarith
    calc Real.log (2 * (x : ℝ) + 2) ≤ Real.log (4 * x) :=
          Real.log_le_log (by positivity) h4x
      _ = Real.log 4 + Real.log x := by rw [Real.log_mul (by norm_num) (by positivity)]
      _ = 2 * Real.log 2 + Real.log x := by rw [log_four_eq]
  -- `log(Z_f x) ≥ (1/48)·log x − log 2`
  have hy100 : (100 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 48) := by
    have h100 : (100 : ℝ) = ((100 : ℝ) ^ 48) ^ ((1 : ℝ) / 48) := by
      rw [← Real.rpow_natCast (100 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100)]
      norm_num
    rw [h100]; exact Real.rpow_le_rpow (by positivity) hx48 (by norm_num)
  have hZf_gt : (x : ℝ) ^ ((1 : ℝ) / 48) - 1 < (Zf x : ℝ) := by
    have h := Nat.lt_floor_add_one ((x : ℝ) ^ ((1 : ℝ) / 48))
    rw [Zf]; linarith [h]
  have hZf_half : (x : ℝ) ^ ((1 : ℝ) / 48) / 2 ≤ (Zf x : ℝ) := by
    have : (x : ℝ) ^ ((1 : ℝ) / 48) / 2 ≤ (x : ℝ) ^ ((1 : ℝ) / 48) - 1 := by linarith [hy100]
    linarith [hZf_gt, this]
  have hZf_lb : (1 / 48) * Real.log x - Real.log 2 ≤ Real.log (Zf x) := by
    have hlogy : Real.log ((x : ℝ) ^ ((1 : ℝ) / 48)) = (1 / 48) * Real.log x := by
      rw [Real.log_rpow hx0]
    have hpos : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 48) / 2 := by positivity
    have h2 : Real.log ((x : ℝ) ^ ((1 : ℝ) / 48) / 2) ≤ Real.log (Zf x) :=
      Real.log_le_log hpos hZf_half
    rw [Real.log_div (by positivity) (by norm_num), hlogy] at h2
    linarith [h2]
  have hlog2 := log_two_le
  linarith [hLwin_ub, hZf_lb, hlogx, hlog2]

/-- **The Mertens absorption floor.**  `log z + (log4+4) ≤ (9/8)·log z` at `z ≥ 100¹⁶`
    (equivalently `8(log4+4) ≤ log z`; `log z ≥ 64`, `8(log4+4) ≤ 44`). -/
lemma mertens_absorb {z : ℕ} (hz100 : 100 ^ 16 ≤ z) :
    Real.log z + (Real.log 4 + 4) ≤ 9 / 8 * Real.log z := by
  have hlogz : (64 : ℝ) ≤ Real.log z := by
    have hz16 : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (100 : ℝ) ^ 16) hz16
    rw [Real.log_pow] at h
    push_cast at h
    nlinarith [h, log_hundred_ge]
  have hlog2 := log_two_le
  have hlog4 := log_four_eq
  linarith [hlogz, hlog2, hlog4]

/-- **The crude `ψ(z)` bound.**  `Σ_{d≤z} Λ(d) ≤ z·L'` (each `Λ(d) ≤ log d ≤ L'`, `z` terms). -/
lemma psi_crude {z x : ℕ} (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ d ∈ Finset.Ioc 0 z, Λ d ≤ (z : ℝ) * Lwin x := by
  have hzx' : (z : ℝ) ≤ (x : ℝ) := by
    rcases Nat.eq_zero_or_pos z with hz0 | hzp
    · simp [hz0]
    · have h1 : (z : ℝ) ≤ (z : ℝ) ^ 3 :=
        le_self_pow₀ (by exact_mod_cast hzp) (by norm_num)
      linarith [hzx, h1]
  have hterm : ∀ d ∈ Finset.Ioc 0 z, Λ d ≤ Lwin x := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    rw [Lwin]
    refine le_trans vonMangoldt_le_log (Real.log_le_log (by exact_mod_cast hd.1) ?_)
    have hdz : (d : ℝ) ≤ (z : ℝ) := by exact_mod_cast hd.2
    linarith [hzx', hdz]
  calc ∑ d ∈ Finset.Ioc 0 z, Λ d ≤ ∑ _d ∈ Finset.Ioc 0 z, Lwin x := Finset.sum_le_sum hterm
    _ = ((Finset.Ioc 0 z).card : ℝ) * Lwin x := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (z : ℝ) * Lwin x := by rw [Nat.card_Ioc]; norm_num

/-! ## §2 (R1) — the totient fold and both engine orientations -/

/-- **The odd-prime-power totient fold.**  `64·(m/φ m)² ≤ 144` for an odd prime power `m`
    (`m = pᵉ`, `p ≥ 3` odd, `m/φ m = p/(p−1) ≤ 3/2`). -/
lemma engine_totient_fold {m : ℕ} (hm : IsPrimePow m) (ho : Odd m) :
    64 * ((m : ℝ) / (Nat.totient m : ℝ)) ^ 2 ≤ 144 := by
  obtain ⟨p, e, hp, he, hpe⟩ := (isPrimePow_nat_iff m).mp hm
  have hpne2 : p ≠ 2 := by
    rintro rfl
    have he2 : Even ((2 : ℕ) ^ e) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    rw [hpe] at he2
    simp only [Nat.even_iff, Nat.odd_iff] at he2 ho
    omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hphi : Nat.totient m = p ^ (e - 1) * (p - 1) := by
    rw [← hpe]; exact Nat.totient_prime_pow hp he
  have hphipos : 0 < Nat.totient m := Nat.totient_pos.mpr hm.pos
  have hpe1 : p ^ e = p * p ^ (e - 1) := by
    conv_lhs => rw [show e = (e - 1) + 1 by omega]
    rw [pow_succ']
  have hkey : 2 * m ≤ 3 * Nat.totient m := by
    rw [hphi, ← hpe, hpe1]
    have hpp : 2 * p ≤ 3 * (p - 1) := by omega
    calc 2 * (p * p ^ (e - 1)) = (2 * p) * p ^ (e - 1) := by ring
      _ ≤ (3 * (p - 1)) * p ^ (e - 1) := by gcongr
      _ = 3 * (p ^ (e - 1) * (p - 1)) := by ring
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.pos
  have hphiR : (0 : ℝ) < (Nat.totient m : ℝ) := by exact_mod_cast hphipos
  have hratio : (m : ℝ) / (Nat.totient m : ℝ) ≤ 3 / 2 := by
    rw [div_le_iff₀ hphiR]
    have : (2 : ℝ) * m ≤ 3 * Nat.totient m := by exact_mod_cast hkey
    linarith
  have h0 : (0 : ℝ) ≤ (m : ℝ) / (Nat.totient m : ℝ) := by positivity
  nlinarith [hratio, h0]

/-- **The engine, right orientation** (`d₁ = 1`, `d₂ = m` the small odd prime-power block). -/
theorem engineRoute_card_right {x m : ℕ} (hZ : 100 ≤ Zf x) (hm : IsPrimePow m) (ho : Odd m) :
    (((baseSet x 1 m).filter
        (fun n => Nat.Coprime (primorial (Zf x)) (n / 1 * ((n + 2) / m)))).card : ℝ)
      ≤ 144 * ((x : ℝ) / m) / Real.log (Zf x) ^ 2 + 2 * (Zf x : ℝ) ^ 8 := by
  have hmpos : 0 < m := hm.pos
  have h := hb_lemma8'_unconditional (x := x) (d₁ := 1) (d₂ := m) (Z := Zf x)
    hZ (by omega) one_pos hmpos odd_one ho (Nat.coprime_one_left m)
  refine le_trans h ?_
  simp only [Nat.cast_one, one_mul]
  have hfold := engine_totient_fold hm ho
  have hbase : (0 : ℝ) ≤ (x : ℝ) / m / Real.log (Zf x) ^ 2 := by positivity
  have key : 64 * ((m : ℝ) / (Nat.totient m : ℝ)) ^ 2 * ((x : ℝ) / m) / Real.log (Zf x) ^ 2
      ≤ 144 * ((x : ℝ) / m) / Real.log (Zf x) ^ 2 :=
    calc 64 * ((m : ℝ) / (Nat.totient m : ℝ)) ^ 2 * ((x : ℝ) / m) / Real.log (Zf x) ^ 2
        = (64 * ((m : ℝ) / (Nat.totient m : ℝ)) ^ 2) * ((x : ℝ) / m / Real.log (Zf x) ^ 2) := by
          ring
      _ ≤ 144 * ((x : ℝ) / m / Real.log (Zf x) ^ 2) := mul_le_mul_of_nonneg_right hfold hbase
      _ = 144 * ((x : ℝ) / m) / Real.log (Zf x) ^ 2 := by ring
  linarith [key]

/-- **The engine, left orientation** (`d₁ = m` the small odd prime-power block, `d₂ = 1`). -/
theorem engineRoute_card_left {x m : ℕ} (hZ : 100 ≤ Zf x) (hm : IsPrimePow m) (ho : Odd m) :
    (((baseSet x m 1).filter
        (fun n => Nat.Coprime (primorial (Zf x)) (n / m * ((n + 2) / 1)))).card : ℝ)
      ≤ 144 * ((x : ℝ) / m) / Real.log (Zf x) ^ 2 + 2 * (Zf x : ℝ) ^ 8 := by
  have hmpos : 0 < m := hm.pos
  have h := hb_lemma8'_unconditional (x := x) (d₁ := m) (d₂ := 1) (Z := Zf x)
    hZ (by omega) hmpos one_pos ho odd_one (Nat.coprime_one_right m)
  refine le_trans h ?_
  simp only [Nat.cast_one, mul_one]
  have hfold := engine_totient_fold hm ho
  have hbase : (0 : ℝ) ≤ (x : ℝ) / m / Real.log (Zf x) ^ 2 := by positivity
  have key : 64 * ((m : ℝ) / (Nat.totient m : ℝ)) ^ 2 * ((x : ℝ) / m) / Real.log (Zf x) ^ 2
      ≤ 144 * ((x : ℝ) / m) / Real.log (Zf x) ^ 2 :=
    calc 64 * ((m : ℝ) / (Nat.totient m : ℝ)) ^ 2 * ((x : ℝ) / m) / Real.log (Zf x) ^ 2
        = (64 * ((m : ℝ) / (Nat.totient m : ℝ)) ^ 2) * ((x : ℝ) / m / Real.log (Zf x) ^ 2) := by
          ring
      _ ≤ 144 * ((x : ℝ) / m / Real.log (Zf x) ^ 2) := mul_le_mul_of_nonneg_right hfold hbase
      _ = 144 * ((x : ℝ) / m) / Real.log (Zf x) ^ 2 := by ring
  linarith [key]

/-! ## §3 (R1) — the engine junk floor (consumed by R2/R3) -/

/-- **The engine junk floor.**  `2·Z_f⁸·z ≤ x^{9/10}` (`Z_f⁸ ≤ x^{1/6}`, `z ≤ x^{1/3}`,
    `2 ≤ x^{2/5}`). -/
lemma engine_junk_bound {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    2 * (Zf x : ℝ) ^ 8 * (z : ℝ) ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := by
  have hx48 : (100 : ℝ) ^ 48 ≤ (x : ℝ) := engine_x_ge hz100 hzx
  have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx48
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 100)) hx48
  have hZf : (Zf x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 48) := by
    rw [Zf]; exact Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have hZf8 : (Zf x : ℝ) ^ 8 ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := by
    calc (Zf x : ℝ) ^ 8 ≤ ((x : ℝ) ^ ((1 : ℝ) / 48)) ^ 8 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hZf 8
      _ = (x : ℝ) ^ ((1 : ℝ) / 6) := by
          rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 48)) 8, ← Real.rpow_mul hx0.le,
            show (1 : ℝ) / 48 * ((8 : ℕ) : ℝ) = 1 / 6 by norm_num]
  have hz13 : (z : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (z : ℝ) ^ 3) hzx
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
    have he : ((z : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (z : ℝ) := by
      rw [← Real.rpow_natCast (z : ℝ) 3, ← Real.rpow_mul (by positivity),
        show ((3 : ℕ) : ℝ) * ((1 : ℝ) / 3) = 1 by norm_num, Real.rpow_one]
    rwa [he] at h
  have hxfloor : (100 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 48) := by
    have h100 : (100 : ℝ) = ((100 : ℝ) ^ 48) ^ ((1 : ℝ) / 48) := by
      rw [← Real.rpow_natCast (100 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100)]
      norm_num
    rw [h100]; exact Real.rpow_le_rpow (by positivity) hx48 (by norm_num)
  have hx25 : (2 : ℝ) ≤ (x : ℝ) ^ ((2 : ℝ) / 5) := by
    have hmono : (x : ℝ) ^ ((1 : ℝ) / 48) ≤ (x : ℝ) ^ ((2 : ℝ) / 5) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    linarith [hxfloor, hmono]
  calc 2 * (Zf x : ℝ) ^ 8 * (z : ℝ)
      ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 3) := by gcongr
    _ = 2 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [mul_assoc, ← Real.rpow_add hx0, show (1 : ℝ) / 6 + (1 : ℝ) / 3 = 1 / 2 by norm_num]
    _ ≤ (x : ℝ) ^ ((2 : ℝ) / 5) * (x : ℝ) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hx25 (by positivity)
    _ = (x : ℝ) ^ ((9 : ℝ) / 10) := by
        rw [← Real.rpow_add hx0, show (2 : ℝ) / 5 + (1 : ℝ) / 2 = 9 / 10 by norm_num]

/-! ## §4 (R2) — the `E_R` swap family, routed through the right engine -/

open Classical in
/-- **The T-sw' fiber embedding.**  For a fixed block `w`, the fiber
    `{n ∈ Tsw' : (n+2)₋ = w}` sits inside `engineRoute_card_right`'s sifted base set at
    modulus `w`: `n` (prime, `> x > Z_f`) and `U = (n+2)₊` (prime, `> x/z > Z_f`) are both
    `Z_f`-rough, so `n·U = (n/1)·((n+2)/w)` is coprime to `primorial (Z_f x)`. -/
lemma erTsw_fiber_subset (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x w : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter (fun n => nMinus χ (n + 2) = w)
      ⊆ (baseSet x 1 w).filter
          (fun n => Nat.Coprime (primorial (Zf x)) (n / 1 * ((n + 2) / w))) := by
  intro n hn
  rw [Finset.mem_filter, Finset.mem_filter] at hn
  obtain ⟨⟨hnw, hfam⟩, hweq⟩ := hn
  have hnp : n.Prime := hfam.1
  have hUp : (nPlus χ (n + 2)).Prime := hfam.2.2.2.1
  have hcop2 : Nat.Coprime (n + 2) q := l2cWindow_np2_coprime_q χ hnw
  have hxlt : x < n := l2cWindow_lt χ hnw
  have hw0 : 0 < w := hweq ▸ nMinus_pos χ (n + 2)
  have hfn2 : n + 2 = nPlus χ (n + 2) * w := by
    have h := eq_nPlus_mul_nMinus χ hsq (by omega : n + 2 ≠ 0) hcop2
    rw [hweq] at h; exact h
  have hdivU : (n + 2) / w = nPlus χ (n + 2) := Nat.div_eq_of_eq_mul_left hw0 hfn2
  have hZfn : Zf x < n :=
    T1_cofactor_gt_Zf hz100 hzx (by omega : x < n * 1) (by omega : 1 ≤ z)
  have hZfU : Zf x < nPlus χ (n + 2) :=
    T1_cofactor_gt_Zf hz100 hzx (by omega : x < nPlus χ (n + 2) * w)
      (hweq ▸ le_of_lt hfam.2.2.1)
  rw [Finset.mem_filter, baseSet, Finset.mem_filter]
  refine ⟨⟨l2cWindow_subset χ z x hnw, one_dvd _, ⟨nPlus χ (n + 2), by
      rw [Nat.mul_comm]; exact hfn2⟩⟩, ?_⟩
  rw [Nat.div_one, hdivU]
  exact (T1_coprime_primorial_of_prime_lt hnp hZfn).mul_right
    (T1_coprime_primorial_of_prime_lt hUp hZfU)

open Classical in
/-- **The unconditional weighted `χ=−1`-block count (`J1` shape).**  Fibering over
    `w = (n+2)₋` into the right engine, Mertens + the floors give
    `Σ_{Tsw'} Λ((n+2)₋) ≤ 583200·x·log z/L'² + x^{9/10}·L'`. -/
theorem erTsw_weightedCount_unconditional (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsERTsw χ z n), Λ (nMinus χ (n + 2))
      ≤ 583200 * x * Real.log z / Lwin x ^ 2 + x ^ ((9 : ℝ) / 10) * Lwin x := by
  classical
  have hZ : 100 ≤ Zf x := Zf_ge_100 hz100 hzx
  have hx2 : 2 ≤ x := by
    have h := engine_x_ge hz100 hzx
    have : (2 : ℝ) ≤ x := le_trans (by norm_num) h
    exact_mod_cast this
  have hz1 : 1 ≤ z := le_trans (Nat.one_le_pow 16 100 (by norm_num)) hz100
  have hzR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
  have hzpos : 0 < Real.log z := Real.log_pos (by
    have : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
    nlinarith [this])
  have hLwinpos : 0 < Lwin x := by have := t2_Lwin_ge hz100 hzx; linarith
  have hLZpos : 0 < Real.log (Zf x) := by
    have h100 : (100 : ℝ) ≤ (Zf x : ℝ) := by exact_mod_cast hZ
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 100) h100
    linarith [log_hundred_ge, this]
  have hmaps : ∀ n ∈ (l2cWindow χ z x).filter (fun n => IsERTsw χ z n),
      nMinus χ (n + 2) ∈ Finset.Ioc 0 z := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_Ioc]
    exact ⟨nMinus_pos χ (n + 2), le_of_lt hn.2.2.2.1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => Λ (nMinus χ (n + 2)))]
  -- per-fiber bound by `g(w) = 144·(x/log Z_f²)·(Λw/w) + 2·Z_f⁸·Λw`
  have hfiber : ∀ w ∈ Finset.Ioc 0 z,
      (∑ n ∈ ((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
          (fun n => nMinus χ (n + 2) = w), Λ (nMinus χ (n + 2)))
        ≤ 144 * ((x : ℝ) / Real.log (Zf x) ^ 2) * (Λ w / w) + 2 * (Zf x : ℝ) ^ 8 * Λ w := by
    intro w _
    have hconst : (∑ n ∈ ((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
        (fun n => nMinus χ (n + 2) = w), Λ (nMinus χ (n + 2)))
          = ((((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
              (fun n => nMinus χ (n + 2) = w)).card : ℝ) * Λ w := by
      rw [Finset.sum_congr rfl (fun n hn => by rw [(Finset.mem_filter.mp hn).2]),
        Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    have hcard : ((((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
        (fun n => nMinus χ (n + 2) = w)).card : ℝ)
          ≤ 144 * ((x : ℝ) / w) / Real.log (Zf x) ^ 2 + 2 * (Zf x : ℝ) ^ 8 := by
      by_cases hne : (((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
          (fun n => nMinus χ (n + 2) = w)).Nonempty
      · obtain ⟨n, hn⟩ := hne
        rw [Finset.mem_filter, Finset.mem_filter] at hn
        obtain ⟨⟨hnw, hfam⟩, hweq⟩ := hn
        have hwpp : IsPrimePow w := hweq ▸ hfam.2.1
        have hnodd : Odd n := hfam.1.odd_of_ne_two (by have := l2cWindow_lt χ hnw; omega)
        have hwdvd : w ∣ (n + 2) := hweq ▸
          t2_nMinus_dvd χ hsq (by omega) (l2cWindow_np2_coprime_q χ hnw)
        have hwodd : Odd w := T1_odd_of_dvd hwdvd (hnodd.add_even even_two)
        calc ((((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
              (fun n => nMinus χ (n + 2) = w)).card : ℝ)
            ≤ (((baseSet x 1 w).filter (fun n =>
                Nat.Coprime (primorial (Zf x)) (n / 1 * ((n + 2) / w)))).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (erTsw_fiber_subset χ hsq hz100 hzx)
          _ ≤ 144 * ((x : ℝ) / w) / Real.log (Zf x) ^ 2 + 2 * (Zf x : ℝ) ^ 8 :=
              engineRoute_card_right hZ hwpp hwodd
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
        positivity
    calc ((((l2cWindow χ z x).filter (fun n => IsERTsw χ z n)).filter
          (fun n => nMinus χ (n + 2) = w)).card : ℝ) * Λ w
        ≤ (144 * ((x : ℝ) / w) / Real.log (Zf x) ^ 2 + 2 * (Zf x : ℝ) ^ 8) * Λ w :=
          mul_le_mul_of_nonneg_right hcard vonMangoldt_nonneg
      _ = 144 * ((x : ℝ) / Real.log (Zf x) ^ 2) * (Λ w / w) + 2 * (Zf x : ℝ) ^ 8 * Λ w := by ring
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- main term (Mertens) and junk term (ψ)
  have hmert : ∑ w ∈ Finset.Ioc 0 z, Λ w / w ≤ 9 / 8 * Real.log z :=
    le_trans (mertens_vonMangoldt_div_le hz1) (mertens_absorb hz100)
  have hsixty := sixty_mul_log_Zf_ge_Lwin hz100 hzx
  have hLsq : Lwin x ^ 2 ≤ 3600 * Real.log (Zf x) ^ 2 := by
    nlinarith [pow_le_pow_left₀ (Lwin_nonneg x) hsixty 2]
  have hmain : 144 * ((x : ℝ) / Real.log (Zf x) ^ 2) * ∑ w ∈ Finset.Ioc 0 z, Λ w / w
      ≤ 583200 * x * Real.log z / Lwin x ^ 2 := by
    have hfactnn : 0 ≤ 144 * ((x : ℝ) / Real.log (Zf x) ^ 2) := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hmert hfactnn) ?_
    rw [show 144 * ((x : ℝ) / Real.log (Zf x) ^ 2) * (9 / 8 * Real.log z)
        = 162 * (x : ℝ) * Real.log z / Real.log (Zf x) ^ 2 from by ring,
      div_le_div_iff₀ (pow_pos hLZpos 2) (pow_pos hLwinpos 2)]
    have hxz0 : 0 ≤ (x : ℝ) * Real.log z := mul_nonneg (Nat.cast_nonneg x) hzpos.le
    nlinarith [hLsq, mul_nonneg hxz0 (sub_nonneg.mpr hLsq)]
  have hjunk : 2 * (Zf x : ℝ) ^ 8 * ∑ w ∈ Finset.Ioc 0 z, Λ w
      ≤ x ^ ((9 : ℝ) / 10) * Lwin x := by
    calc 2 * (Zf x : ℝ) ^ 8 * ∑ w ∈ Finset.Ioc 0 z, Λ w
        ≤ 2 * (Zf x : ℝ) ^ 8 * ((z : ℝ) * Lwin x) :=
          mul_le_mul_of_nonneg_left (psi_crude hzx) (by positivity)
      _ = (2 * (Zf x : ℝ) ^ 8 * (z : ℝ)) * Lwin x := by ring
      _ ≤ x ^ ((9 : ℝ) / 10) * Lwin x :=
          mul_le_mul_of_nonneg_right (engine_junk_bound hz100 hzx) (Lwin_nonneg x)
  linarith [hmain, hjunk]

/-- **The frozen `E_R` swap-family bound (`J1` row).**  Peeling the reduction
    `ER_Tsw' ≤ 2L'·Σ Λ((n+2)₋)` against the unconditional weighted count:
    `ER_Tsw' ≤ 2²¹·(x/z₀) + x^{9/10}·L'³`. -/
theorem ER_Tsw'_bound_unconditional (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ER_Tsw' χ z x ≤ 2 ^ 21 * (x / z0 z x) + x ^ ((9 : ℝ) / 10) * Lwin x ^ 3 := by
  have hzpos : 0 < Real.log z := Real.log_pos (by
    have : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
    nlinarith [this])
  have hLwinpos : 0 < Lwin x := by have := t2_Lwin_ge hz100 hzx; linarith
  have hLwin100 : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hxlogz : (0 : ℝ) ≤ (x : ℝ) * Real.log z := mul_nonneg (Nat.cast_nonneg x) hzpos.le
  have hpeel := ER_Tsw'_le_weightedCount χ hsq z x
  have hwc := erTsw_weightedCount_unconditional χ hsq hz100 hzx
  have hLnn : (0 : ℝ) ≤ 2 * Lwin x := by positivity
  have hLHS : 2 * Lwin x
      * (583200 * (x : ℝ) * Real.log z / Lwin x ^ 2 + (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x)
      = 1166400 * ((x : ℝ) * Real.log z) / Lwin x
          + 2 * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 2 := by
    field_simp
    ring
  refine le_trans hpeel (le_trans (mul_le_mul_of_nonneg_left hwc hLnn) ?_)
  rw [z0, div_div_eq_mul_div, hLHS]
  apply add_le_add
  · rw [show (2 : ℝ) ^ 21 * ((x : ℝ) * Real.log z / Lwin x)
        = 2 ^ 21 * ((x : ℝ) * Real.log z) / Lwin x from by ring,
      div_le_div_iff₀ hLwinpos hLwinpos]
    nlinarith [mul_nonneg hxlogz hLwinpos.le]
  · calc 2 * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 2
        = 2 * ((x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 2) := by ring
      _ ≤ Lwin x * ((x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith [hLwin100]) (by positivity)
      _ = (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3 := by ring

/-! ## §5 (R3) — the class-(c) family, routed through the left engine -/

/-- **The sharp class-(c) per-summand cap** (no `exp` factor).  On `cPairSet`, `n₊` is a
    `χ=+1` prime (so `Λ̃(n) = 2·Λ(n₋)`) and `(n+2)₊ = 1` (so `Λ̃(n+2) = Λ(n+2) ≤ L'`):
    `(Λ̃−Λ)(n)·Λ̃(n+2) ≤ 2·Λ(n₋)·L'`. -/
lemma cpair_summand_sharp (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ cPairSet χ z x) :
    (LamTilde χ n - Λ n) * LamTilde χ (n + 2) ≤ 2 * Λ (nMinus χ n) * Lwin x := by
  simp only [cPairSet, Finset.mem_filter] at hn
  obtain ⟨hnw, _hodd, hAp, hvpp, _hvz, hB1, hppn2⟩ := hn
  have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hnw
  have hcop : Nat.Coprime n q := l2cWindow_coprime χ hnw
  have hcop2 : Nat.Coprime (n + 2) q := l2cWindow_coprime_add_two χ hnw
  -- `n`-side: `Λ̃(n) = 2·Λ(n₋)`
  have hchiP : chiRe χ (nPlus χ n) = 1 :=
    nPlus_sign (Nat.mem_primeFactors.mpr ⟨hAp, dvd_rfl, hAp.pos.ne'⟩)
  have hfP2 : fChiSum χ (nPlus χ n) = 2 := erTsw_fChiSum_eq_two χ hsq hAp hchiP
  have hLn : LamTilde χ n = 2 * Λ (nMinus χ n) := by
    rw [LamTilde_eq_single_of_card_one χ hsq hn0 hcop hvpp, hfP2]
  -- `(n+2)`-side: `Λ̃(n+2) = Λ(n+2)`
  have hn2minus : nMinus χ (n + 2) = n + 2 := by
    have h := eq_nPlus_mul_nMinus χ hsq (by omega : n + 2 ≠ 0) hcop2
    rw [hB1, one_mul] at h; exact h.symm
  have hf1 : fChiSum χ 1 = 1 := by simp [fChiSum]
  have hR : LamTilde χ (n + 2) = Λ (n + 2) := by
    rw [LamTilde_eq_single_of_card_one χ hsq (by omega : n + 2 ≠ 0) hcop2
        (by rw [hn2minus]; exact hppn2), hB1, hf1, hn2minus, one_mul]
  -- combine
  have hRle : LamTilde χ (n + 2) ≤ Lwin x := by
    rw [hR, Lwin]
    refine le_trans vonMangoldt_le_log
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < n + 2)) ?_)
    have h := l2cWindow_le χ hnw
    have hnr : (n : ℝ) ≤ 2 * x := by exact_mod_cast h
    push_cast; linarith
  have hRnn : 0 ≤ LamTilde χ (n + 2) := lamTilde_nonneg χ hsq (n + 2)
  have hLnle : LamTilde χ n - Λ n ≤ 2 * Λ (nMinus χ n) := by
    rw [hLn]; linarith [vonMangoldt_nonneg (n := n)]
  calc (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ (2 * Λ (nMinus χ n)) * Lwin x :=
        mul_le_mul hLnle hRle hRnn (mul_nonneg (by norm_num) vonMangoldt_nonneg)
    _ = 2 * Λ (nMinus χ n) * Lwin x := by ring

/-- **The class-(c) fiber embedding** (rough branch `Z_f < minFac(n+2)`).  For a fixed block
    `v`, the fiber `{n : n₋ = v}` sits inside `engineRoute_card_left`'s sifted base set at
    modulus `v`: `P = n₊` (prime, `> x/z > Z_f`) and `n+2` (all of whose primes exceed
    `minFac(n+2) > Z_f`) are both `Z_f`-rough, so `P·(n+2) = (n/v)·((n+2)/1)` is coprime to
    `primorial (Z_f x)`. -/
lemma cpair_fiber_subset (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x v : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ((cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2))).filter
        (fun n => nMinus χ n = v)
      ⊆ (baseSet x v 1).filter
          (fun n => Nat.Coprime (primorial (Zf x)) (n / v * ((n + 2) / 1))) := by
  intro n hn
  rw [Finset.mem_filter, Finset.mem_filter] at hn
  obtain ⟨⟨hnc, hminfac⟩, hveq⟩ := hn
  simp only [cPairSet, Finset.mem_filter] at hnc
  obtain ⟨hnw, _hodd, hAp, hvpp, hvz, _hB1, _hppn2⟩ := hnc
  have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hnw
  have hcop : Nat.Coprime n q := l2cWindow_coprime χ hnw
  have hxlt : x < n := l2cWindow_lt χ hnw
  have hv0 : 0 < v := hveq ▸ nMinus_pos χ n
  have hfn : n = nPlus χ n * v := by
    have h := eq_nPlus_mul_nMinus χ hsq hn0 hcop
    rw [hveq] at h; exact h
  have hdivP : n / v = nPlus χ n := Nat.div_eq_of_eq_mul_left hv0 hfn
  have hZfP : Zf x < nPlus χ n :=
    T1_cofactor_gt_Zf hz100 hzx (by omega : x < nPlus χ n * v) (hveq ▸ le_of_lt hvz)
  have hvdvd : v ∣ n := hveq ▸ t2_nMinus_dvd χ hsq hn0 hcop
  rw [Finset.mem_filter, baseSet, Finset.mem_filter]
  refine ⟨⟨l2cWindow_subset χ z x hnw, hvdvd, one_dvd _⟩, ?_⟩
  rw [Nat.div_one, hdivP]
  exact (T1_coprime_primorial_of_prime_lt hAp hZfP).mul_right
    (t2_coprime_primorial (fun r hr hrd =>
      lt_of_lt_of_le hminfac (Nat.minFac_le_of_dvd hr.two_le hrd)))

/-- **The rough-branch weighted `n₋`-count (`J1` shape).**  Fibering over `v = n₋` into the
    left engine, Mertens + the floors give
    `Σ_{(c), Z_f<minFac(n+2)} Λ(n₋) ≤ 583200·x·log z/L'² + x^{9/10}·L'`. -/
theorem cpairA_weightedCount (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ (cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2)), Λ (nMinus χ n)
      ≤ 583200 * x * Real.log z / Lwin x ^ 2 + x ^ ((9 : ℝ) / 10) * Lwin x := by
  classical
  have hZ : 100 ≤ Zf x := Zf_ge_100 hz100 hzx
  have hz1 : 1 ≤ z := le_trans (Nat.one_le_pow 16 100 (by norm_num)) hz100
  have hzpos : 0 < Real.log z := Real.log_pos (by
    have : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
    nlinarith [this])
  have hLwinpos : 0 < Lwin x := by have := t2_Lwin_ge hz100 hzx; linarith
  have hLZpos : 0 < Real.log (Zf x) := by
    have h100 : (100 : ℝ) ≤ (Zf x : ℝ) := by exact_mod_cast hZ
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 100) h100
    linarith [log_hundred_ge, this]
  have hmaps : ∀ n ∈ (cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2)),
      nMinus χ n ∈ Finset.Ioc 0 z := by
    intro n hn
    have hnc := Finset.mem_of_mem_filter n hn
    simp only [cPairSet, Finset.mem_filter] at hnc
    rw [Finset.mem_Ioc]
    exact ⟨nMinus_pos χ n, le_of_lt hnc.2.2.2.2.1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => Λ (nMinus χ n))]
  have hfiber : ∀ v ∈ Finset.Ioc 0 z,
      (∑ n ∈ ((cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2))).filter
          (fun n => nMinus χ n = v), Λ (nMinus χ n))
        ≤ 144 * ((x : ℝ) / Real.log (Zf x) ^ 2) * (Λ v / v) + 2 * (Zf x : ℝ) ^ 8 * Λ v := by
    intro v _
    have hconst : (∑ n ∈ ((cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2))).filter
        (fun n => nMinus χ n = v), Λ (nMinus χ n))
          = ((((cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2))).filter
              (fun n => nMinus χ n = v)).card : ℝ) * Λ v := by
      rw [Finset.sum_congr rfl (fun n hn => by rw [(Finset.mem_filter.mp hn).2]),
        Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    have hcard : ((((cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2))).filter
        (fun n => nMinus χ n = v)).card : ℝ)
          ≤ 144 * ((x : ℝ) / v) / Real.log (Zf x) ^ 2 + 2 * (Zf x : ℝ) ^ 8 := by
      by_cases hne : (((cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2))).filter
          (fun n => nMinus χ n = v)).Nonempty
      · obtain ⟨n, hn⟩ := hne
        have hnc := Finset.mem_of_mem_filter n (Finset.mem_of_mem_filter n hn)
        have hveq : nMinus χ n = v := (Finset.mem_filter.mp hn).2
        simp only [cPairSet, Finset.mem_filter] at hnc
        obtain ⟨hnw, hodd, _hAp, hvpp, _hvz, _hB1, _hppn2⟩ := hnc
        have hvpp' : IsPrimePow v := hveq ▸ hvpp
        have hvdvd : v ∣ n := hveq ▸ t2_nMinus_dvd χ hsq (l2cWindow_ne_zero χ hnw)
          (l2cWindow_coprime χ hnw)
        have hvodd : Odd v := T1_odd_of_dvd hvdvd hodd
        calc ((((cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2))).filter
              (fun n => nMinus χ n = v)).card : ℝ)
            ≤ (((baseSet x v 1).filter (fun n =>
                Nat.Coprime (primorial (Zf x)) (n / v * ((n + 2) / 1)))).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (cpair_fiber_subset χ hsq hz100 hzx)
          _ ≤ 144 * ((x : ℝ) / v) / Real.log (Zf x) ^ 2 + 2 * (Zf x : ℝ) ^ 8 :=
              engineRoute_card_left hZ hvpp' hvodd
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
        positivity
    calc ((((cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2))).filter
          (fun n => nMinus χ n = v)).card : ℝ) * Λ v
        ≤ (144 * ((x : ℝ) / v) / Real.log (Zf x) ^ 2 + 2 * (Zf x : ℝ) ^ 8) * Λ v :=
          mul_le_mul_of_nonneg_right hcard vonMangoldt_nonneg
      _ = 144 * ((x : ℝ) / Real.log (Zf x) ^ 2) * (Λ v / v) + 2 * (Zf x : ℝ) ^ 8 * Λ v := by ring
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hmert : ∑ v ∈ Finset.Ioc 0 z, Λ v / v ≤ 9 / 8 * Real.log z :=
    le_trans (mertens_vonMangoldt_div_le hz1) (mertens_absorb hz100)
  have hsixty := sixty_mul_log_Zf_ge_Lwin hz100 hzx
  have hLsq : Lwin x ^ 2 ≤ 3600 * Real.log (Zf x) ^ 2 := by
    nlinarith [pow_le_pow_left₀ (Lwin_nonneg x) hsixty 2]
  have hmain : 144 * ((x : ℝ) / Real.log (Zf x) ^ 2) * ∑ v ∈ Finset.Ioc 0 z, Λ v / v
      ≤ 583200 * x * Real.log z / Lwin x ^ 2 := by
    have hfactnn : 0 ≤ 144 * ((x : ℝ) / Real.log (Zf x) ^ 2) := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hmert hfactnn) ?_
    rw [show 144 * ((x : ℝ) / Real.log (Zf x) ^ 2) * (9 / 8 * Real.log z)
        = 162 * (x : ℝ) * Real.log z / Real.log (Zf x) ^ 2 from by ring,
      div_le_div_iff₀ (pow_pos hLZpos 2) (pow_pos hLwinpos 2)]
    have hxz0 : 0 ≤ (x : ℝ) * Real.log z := mul_nonneg (Nat.cast_nonneg x) hzpos.le
    nlinarith [hLsq, mul_nonneg hxz0 (sub_nonneg.mpr hLsq)]
  have hjunk : 2 * (Zf x : ℝ) ^ 8 * ∑ v ∈ Finset.Ioc 0 z, Λ v
      ≤ x ^ ((9 : ℝ) / 10) * Lwin x := by
    calc 2 * (Zf x : ℝ) ^ 8 * ∑ v ∈ Finset.Ioc 0 z, Λ v
        ≤ 2 * (Zf x : ℝ) ^ 8 * ((z : ℝ) * Lwin x) :=
          mul_le_mul_of_nonneg_left (psi_crude hzx) (by positivity)
      _ = (2 * (Zf x : ℝ) ^ 8 * (z : ℝ)) * Lwin x := by ring
      _ ≤ x ^ ((9 : ℝ) / 10) * Lwin x :=
          mul_le_mul_of_nonneg_right (engine_junk_bound hz100 hzx) (Lwin_nonneg x)
  linarith [hmain, hjunk]

/-- **The frozen class-(c) bound (`J1` row).**  The sharp cap plus the complete `q'` (base
    prime of `n+2`) dichotomy: the rough branch `Z_f < minFac(n+2)` fibers through the left
    engine (mirroring the swap family), the small branch is squarefull junk
    (`erT1_shifted_properPrimePow_count`).  `cPairSum ≤ 2²¹·(x/z₀) + x^{9/10}·L'³`. -/
theorem cPairSum_bound_unconditional (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    cPairSum χ z x ≤ 2 ^ 21 * (x / z0 z x) + x ^ ((9 : ℝ) / 10) * Lwin x ^ 3 := by
  have hzpos : 0 < Real.log z := Real.log_pos (by
    have : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
    nlinarith [this])
  have hLwinpos : 0 < Lwin x := by have := t2_Lwin_ge hz100 hzx; linarith
  have hLwin100 : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) (engine_x_ge hz100 hzx)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 100))
    (engine_x_ge hz100 hzx)
  have hx9nn : (0 : ℝ) ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := Real.rpow_nonneg hx0.le _
  have hxlogz : (0 : ℝ) ≤ (x : ℝ) * Real.log z := mul_nonneg (Nat.cast_nonneg x) hzpos.le
  have hLHS : 2 * Lwin x
      * (583200 * (x : ℝ) * Real.log z / Lwin x ^ 2 + (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x)
      = 1166400 * ((x : ℝ) * Real.log z) / Lwin x
          + 2 * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 2 := by
    field_simp; ring
  -- part A: the rough branch, routed through the left engine
  have hApeel : (∑ n ∈ (cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2)),
        (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
      ≤ 1166400 * ((x : ℝ) * Real.log z) / Lwin x
          + 2 * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 2 := by
    have hcap : (∑ n ∈ (cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2)),
          (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
        ≤ 2 * Lwin x * ∑ n ∈ (cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2)),
            Λ (nMinus χ n) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun n hn =>
        le_trans (cpair_summand_sharp χ hsq (Finset.mem_of_mem_filter n hn)) (le_of_eq (by ring)))
    calc (∑ n ∈ (cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2)),
          (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
        ≤ 2 * Lwin x * ∑ n ∈ (cPairSet χ z x).filter (fun n => Zf x < Nat.minFac (n + 2)),
            Λ (nMinus χ n) := hcap
      _ ≤ 2 * Lwin x
            * (583200 * x * Real.log z / Lwin x ^ 2 + x ^ ((9 : ℝ) / 10) * Lwin x) :=
          mul_le_mul_of_nonneg_left (cpairA_weightedCount χ hsq hz100 hzx)
            (by linarith [hLwinpos])
      _ = 1166400 * ((x : ℝ) * Real.log z) / Lwin x
            + 2 * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 2 := hLHS
  -- part B: the small branch is squarefull junk
  have hB : (∑ n ∈ (cPairSet χ z x).filter (fun n => ¬ Zf x < Nat.minFac (n + 2)),
        (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
      ≤ 2 * Lwin x ^ 2 * Real.sqrt (2 * (x : ℝ) + 2) := by
    have hcardnat : ((cPairSet χ z x).filter (fun n => ¬ Zf x < Nat.minFac (n + 2))).card
        ≤ Nat.sqrt (2 * x + 2) := by
      refine le_trans (Finset.card_le_card ?_) (erT1_shifted_properPrimePow_count x)
      intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨hnc, hnf⟩ := hn
      have hnc' := hnc
      simp only [cPairSet, Finset.mem_filter] at hnc'
      obtain ⟨hnw, _, _, _, _, _, hppn2⟩ := hnc'
      rw [Finset.mem_filter]
      refine ⟨l2cWindow_subset χ z x hnw, hppn2, fun hp2 => hnf ?_⟩
      have hZflt : Zf x < n + 2 :=
        T1_cofactor_gt_Zf hz100 hzx (by have := l2cWindow_lt χ hnw; omega : x < (n + 2) * 1)
          (by omega : (1 : ℕ) ≤ z)
      rw [(Nat.prime_def_minFac.mp hp2).2]; exact hZflt
    have hterm : ∀ n ∈ (cPairSet χ z x).filter (fun n => ¬ Zf x < Nat.minFac (n + 2)),
        (LamTilde χ n - Λ n) * LamTilde χ (n + 2) ≤ 2 * Lwin x ^ 2 := by
      intro n hn
      have hmem : n ∈ cPairSet χ z x := Finset.mem_of_mem_filter n hn
      have hnw : n ∈ l2cWindow χ z x := by
        simp only [cPairSet, Finset.mem_filter] at hmem; exact hmem.1
      have hΛv : Λ (nMinus χ n) ≤ Lwin x := by
        rw [Lwin]
        refine le_trans vonMangoldt_le_log
          (Real.log_le_log (by exact_mod_cast nMinus_pos χ n) ?_)
        have hle : nMinus χ n ≤ 2 * x :=
          le_trans (Nat.le_of_dvd (by have := l2cWindow_lt χ hnw; omega)
            (t2_nMinus_dvd χ hsq (l2cWindow_ne_zero χ hnw) (l2cWindow_coprime χ hnw)))
            (l2cWindow_le χ hnw)
        have hnr : (nMinus χ n : ℝ) ≤ 2 * x := by exact_mod_cast hle
        linarith
      calc (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
          ≤ 2 * Λ (nMinus χ n) * Lwin x := cpair_summand_sharp χ hsq hmem
        _ ≤ 2 * Lwin x * Lwin x := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hΛv) (Lwin_nonneg x)]
        _ = 2 * Lwin x ^ 2 := by ring
    calc (∑ n ∈ (cPairSet χ z x).filter (fun n => ¬ Zf x < Nat.minFac (n + 2)),
          (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
        ≤ ∑ _n ∈ (cPairSet χ z x).filter (fun n => ¬ Zf x < Nat.minFac (n + 2)),
            2 * Lwin x ^ 2 := Finset.sum_le_sum hterm
      _ = (((cPairSet χ z x).filter (fun n => ¬ Zf x < Nat.minFac (n + 2))).card : ℝ)
            * (2 * Lwin x ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.sqrt (2 * (x : ℝ) + 2) * (2 * Lwin x ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h1 : (((cPairSet χ z x).filter (fun n => ¬ Zf x < Nat.minFac (n + 2))).card : ℝ)
              ≤ (Nat.sqrt (2 * x + 2) : ℝ) := by exact_mod_cast hcardnat
          refine h1.trans (Real.le_sqrt_of_sq_le ?_)
          calc ((Nat.sqrt (2 * x + 2) : ℕ) : ℝ) ^ 2
              = ((Nat.sqrt (2 * x + 2) ^ 2 : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((2 * x + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.sqrt_le' (2 * x + 2)
            _ = 2 * (x : ℝ) + 2 := by push_cast; ring
      _ = 2 * Lwin x ^ 2 * Real.sqrt (2 * (x : ℝ) + 2) := by ring
  -- junk arithmetic
  have hsqrt_le : Real.sqrt (2 * (x : ℝ) + 2) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
    have h1 : Real.sqrt (2 * (x : ℝ) + 2) ≤ Real.sqrt (4 * (x : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith [hx1])
    have h2 : Real.sqrt (4 * (x : ℝ)) = 2 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [show (4 : ℝ) * (x : ℝ) = 2 ^ 2 * x by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num), Real.sqrt_eq_rpow]
    rw [h2] at h1; exact h1
  have hJ1 : 2 * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 2
      ≤ 1 / 2 * ((x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3) := by
    calc 2 * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 2
        = 2 * ((x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 2) := by ring
      _ ≤ (1 / 2 * Lwin x) * ((x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith [hLwin100]) (mul_nonneg hx9nn (sq_nonneg _))
      _ = 1 / 2 * ((x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3) := by ring
  have hJ2 : 2 * Lwin x ^ 2 * Real.sqrt (2 * (x : ℝ) + 2)
      ≤ 1 / 2 * ((x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3) := by
    have hxhalf : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ ((9 : ℝ) / 10) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hxhalf0 : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
    have hstep : 8 * (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxhalf) (show (0 : ℝ) ≤ Lwin x by linarith [hLwin100]),
        mul_nonneg (show (0 : ℝ) ≤ Lwin x - 100 by linarith [hLwin100]) hxhalf0]
    calc 2 * Lwin x ^ 2 * Real.sqrt (2 * (x : ℝ) + 2)
        ≤ 2 * Lwin x ^ 2 * (2 * (x : ℝ) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
      _ = Lwin x ^ 2 * (4 * (x : ℝ) ^ ((1 : ℝ) / 2)) := by ring
      _ ≤ Lwin x ^ 2 * (1 / 2 * ((x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x)) :=
          mul_le_mul_of_nonneg_left (by linarith [hstep]) (sq_nonneg _)
      _ = 1 / 2 * ((x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3) := by ring
  -- assemble
  rw [cPairSum, ← Finset.sum_filter_add_sum_filter_not (cPairSet χ z x)
      (fun n => Zf x < Nat.minFac (n + 2)), z0, div_div_eq_mul_div]
  have hMain : 1166400 * ((x : ℝ) * Real.log z) / Lwin x
      ≤ 2 ^ 21 * ((x : ℝ) * Real.log z / Lwin x) := by
    rw [show (2 : ℝ) ^ 21 * ((x : ℝ) * Real.log z / Lwin x)
        = 2 ^ 21 * ((x : ℝ) * Real.log z) / Lwin x from by ring,
      div_le_div_iff₀ hLwinpos hLwinpos]
    nlinarith [mul_nonneg hxlogz hLwinpos.le]
  linarith [hApeel, hB, hMain, hJ1, hJ2]

end Salt.HB
