/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cER
import Salt.HB.L2cEL

/-!
# HB-L2c — the `E_R` T2′ family budget (node HB-L2c-F-ER-T2′, Horn A keystone)

Single writer of the **`E_R` T2′ family budget** `ER_T2'_bound` — the `J2` `PretenseSum`
row of the right-overshoot family analysis (freeze §S4, `E_R` mirror; target shape recorded
in `Salt.HB.L2cER` §5 NOTES, amended per catch #245).

The T2′ family is the sub-sum of `E_R = Σ_{n∈W} Λ(n)·(Λ̃−Λ)(n+2)` over window elements `n`
with `n` **prime** whose `n+2` is single-block (`w := (n+2)₋` a prime power, `1 < (n+2)₊`)
with **composite plus-part** `M := (n+2)₊`, under the catch-#245 inline junk-block guard on
`w` (`¬ ERT2'JunkBlock`).  The roles-swapped repaired modulus law: `p'' := minFac M` is a
`χ=+1` prime `≥ z`, and `c' := M/p'' ≥ z` (every prime of `c'` is `≥ z` by window roughness
and `c' > 1` since `M` is composite), so the `n+2`-side modulus `d₂ := w·p'' = (n+2)/c'`
obeys `d₂·z ≤ 2x+2`.  The `n`-side is the prime `n` itself — `> x`, hence coprime to every
sift primorial for free — so the fibration runs at `d₁ = 1` (house-ratified simplification).
`w` is routed at `z^{1/4}` (`ert2K`): `w ≤ z^{1/4}` joins the modulus (route A), larger `w`
rides in the sifted cofactor (route B, sound by the guard: its base exceeds `Zz`).  The sift
floor is `Zz = ⌊z^{1/16}⌋` throughout (catch #245 sift-floor rule; cofactors here are only
guaranteed `≥ z`-rough, never `≥ Zf`-sized).  The `χ=+1` prime `p''` pays the `PretenseSum`
factor via `Σ 1/p'' ≤ PS/log z`; the fiber count is `l2c_pair_count_clean`.  Frozen
conclusion:

`Σ_{T2′} Λ(n)·(Λ̃−Λ)(n+2) ≤ Cmain·(x / L')·exp(5·z₀)·PretenseSum χ (2x+2)`  (the `J2` row),

with `Cmain = 2²² = 4194304` explicit and absolute.

Single-writer file (`L2cERT2.lean`); it imports only the frozen surfaces `Salt.HB.L2cER` /
`Salt.HB.L2cEL` (both over `Salt.HB.L2cCore`) and touches no other file (`Salt.HB.All` is
Wave 3's manifest).  Helper names carry the `ert2` family prefix (single-writer name law).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — the catch-#245 junk-block guard and the `z^{1/4}` routing threshold -/

/-- **The T2′ junk-block guard** (house amendment, catch #245): a small-base squarefull
    block past the `z^{1/4}` routing threshold — `w = p^e` with `p ≤ Zz z` prime, `e ≥ 2`,
    `z^{1/4} < w`.  Such blocks belong to the junk row (`ER_wJunk_bound`), not to `J2`;
    the T2′ family carries the inline exclusion `¬ ERT2'JunkBlock`. -/
def ERT2'JunkBlock (z w : ℕ) : Prop :=
  ∃ p e : ℕ, p.Prime ∧ p ≤ Zz z ∧ 2 ≤ e ∧ w = p ^ e ∧ (z : ℝ) ^ ((1 : ℝ) / 4) < (w : ℝ)

/-- The T2′ `w`-routing threshold `K := ⌊z^{1/4}⌋` (blocks `≤ K` join the modulus). -/
noncomputable def ert2K (z : ℕ) : ℕ := ⌊(z : ℝ) ^ ((1 : ℝ) / 4)⌋₊

/-! ## §1 — the scalar layer: floor bounds, legality arithmetic, exponent absorption -/

/-- `64 ≤ log z` for `z ≥ 100^16` (via `4 ≤ log 100`). -/
lemma ert2_logz_ge {z : ℕ} (hz100 : 100 ^ 16 ≤ z) : (64 : ℝ) ≤ Real.log z := by
  have hzr : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
  have hlog100 : (4 : ℝ) ≤ Real.log 100 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 100)]
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    calc Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
      _ ≤ 100 := by norm_num
  have hlog : Real.log ((100 : ℝ) ^ 16) ≤ Real.log z := Real.log_le_log (by positivity) hzr
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- `Zz z ≤ z^{1/16}` (floor bound; T2′-local copy). -/
lemma ert2_Zz_le_rpow {z : ℕ} : (Zz z : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 16) := by
  rw [Zz]; exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg z) _)

/-- `Zz z⁸ ≤ z^{1/2}` (T2′-local copy). -/
lemma ert2_Zz_pow8_le {z : ℕ} (hz1 : 1 ≤ z) : (Zz z : ℝ) ^ 8 ≤ (z : ℝ) ^ ((1 : ℝ) / 2) := by
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have h1 : (Zz z : ℝ) ^ 8 ≤ ((z : ℝ) ^ ((1 : ℝ) / 16)) ^ 8 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) ert2_Zz_le_rpow 8
  have h2 : ((z : ℝ) ^ ((1 : ℝ) / 16)) ^ 8 = (z : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 16)) 8, ← Real.rpow_mul hzpos.le]; norm_num
  rw [h2] at h1; exact h1

/-- `log z ≤ 8·z^{1/8}` (T2′-local copy). -/
lemma ert2_log_le_rpow_eighth {z : ℕ} (hz1 : 1 ≤ z) :
    Real.log z ≤ 8 * (z : ℝ) ^ ((1 : ℝ) / 8) := by
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have hr : (0 : ℝ) < (z : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hzpos _
  have hstep : Real.log ((z : ℝ) ^ ((1 : ℝ) / 8)) ≤ (z : ℝ) ^ ((1 : ℝ) / 8) - 1 :=
    Real.log_le_sub_one_of_pos hr
  rw [Real.log_rpow hzpos] at hstep
  linarith

/-- `(log z)² ≤ 64·z^{1/4}` (T2′-local copy). -/
lemma ert2_log_sq_le {z : ℕ} (hz1 : 1 ≤ z) :
    Real.log z ^ 2 ≤ 64 * (z : ℝ) ^ ((1 : ℝ) / 4) := by
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have hlognn : 0 ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz1)
  have h8 := ert2_log_le_rpow_eighth hz1
  have hr8 : (0 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 8) := (Real.rpow_pos_of_pos hzpos _).le
  have hsq : Real.log z ^ 2 ≤ (8 * (z : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 :=
    sq_le_sq' (by nlinarith) h8
  have ht2 : ((z : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 = (z : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 8)) 2, ← Real.rpow_mul hzpos.le]; norm_num
  calc Real.log z ^ 2 ≤ (8 * (z : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 := hsq
    _ = 64 * (z : ℝ) ^ ((1 : ℝ) / 4) := by rw [mul_pow, ht2]; norm_num

/-- `Zz z < z` (T2′-local copy: `z^{1/16} < z` for `z ≥ 2`). -/
lemma ert2_Zz_lt_z {z : ℕ} (hz2 : 2 ≤ z) : Zz z < z := by
  have hzR : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have h2 : (z : ℝ) ^ ((1 : ℝ) / 16) < (z : ℝ) := by
    have := Real.rpow_lt_rpow_of_exponent_lt hzR (by norm_num : (1 : ℝ) / 16 < 1)
    rwa [Real.rpow_one] at this
  exact_mod_cast lt_of_le_of_lt ert2_Zz_le_rpow h2

/-- `K ≤ z^{1/4}` (floor bound). -/
lemma ert2_K_le_rpow {z : ℕ} : (ert2K z : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [ert2K]; exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg z) _)

/-- `K < z` (`z^{1/4} < z` for `z ≥ 2`) — so modulus-routed blocks sit below `z ≤ p''`. -/
lemma ert2_K_lt_z {z : ℕ} (hz2 : 2 ≤ z) : ert2K z < z := by
  have hzR : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have h2 : (z : ℝ) ^ ((1 : ℝ) / 4) < (z : ℝ) := by
    have := Real.rpow_lt_rpow_of_exponent_lt hzR (by norm_num : (1 : ℝ) / 4 < 1)
    rwa [Real.rpow_one] at this
  exact_mod_cast lt_of_le_of_lt ert2_K_le_rpow h2

/-- `1 ≤ K` in-regime. -/
lemma ert2_one_le_K {z : ℕ} (hz100 : 100 ^ 16 ≤ z) : 1 ≤ ert2K z := by
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast le_trans (Nat.one_le_pow _ _ (by norm_num)) hz100
  rw [ert2K]
  refine Nat.le_floor ?_
  calc ((1 : ℕ) : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 4) := by rw [Real.one_rpow]; norm_num
    _ ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by norm_num) hz1 (by norm_num)

/-- **The sift-floor conversion** (T2′-local copy): `(log z)/32 ≤ log (Zz z)`. -/
lemma ert2_log_Zz_ge {z : ℕ} (hz100 : 100 ^ 16 ≤ z) : Real.log z / 32 ≤ Real.log (Zz z) := by
  have hz1 : 1 ≤ z := le_trans (Nat.one_le_pow _ _ (by norm_num)) hz100
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have hZz100 : 100 ≤ Zz z := Zz_ge_100 hz100
  have hfl : (z : ℝ) ^ ((1 : ℝ) / 16) - 1 ≤ (Zz z : ℝ) := by
    rw [Zz]; exact le_of_lt (Nat.sub_one_lt_floor _)
  have hr2 : (2 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 16) := by
    have h100 : ((100 : ℕ) : ℝ) ≤ (Zz z : ℝ) := by exact_mod_cast hZz100
    calc (2 : ℝ) ≤ ((100 : ℕ) : ℝ) := by norm_num
      _ ≤ (Zz z : ℝ) := h100
      _ ≤ (z : ℝ) ^ ((1 : ℝ) / 16) := ert2_Zz_le_rpow
  have hhalf : (z : ℝ) ^ ((1 : ℝ) / 16) / 2 ≤ (Zz z : ℝ) := by linarith
  have hlog1 : Real.log ((z : ℝ) ^ ((1 : ℝ) / 16) / 2) ≤ Real.log (Zz z) :=
    Real.log_le_log (by positivity) hhalf
  have hlog2 : Real.log ((z : ℝ) ^ ((1 : ℝ) / 16) / 2)
      = (1 / 16) * Real.log z - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hzpos]
  have hlz : 32 * Real.log 2 ≤ Real.log z := by
    have h216 : ((2 : ℝ) ^ 32) ≤ ((100 : ℝ) ^ 16) := by norm_num
    have hz100R : ((100 : ℝ) ^ 16) ≤ (z : ℝ) := by exact_mod_cast hz100
    calc 32 * Real.log 2 = Real.log ((2 : ℝ) ^ 32) := by rw [Real.log_pow]; push_cast; ring
      _ ≤ Real.log ((100 : ℝ) ^ 16) := Real.log_le_log (by positivity) h216
      _ ≤ Real.log z := Real.log_le_log (by positivity) hz100R
  calc Real.log z / 32 = (1 / 16) * Real.log z - Real.log z / 32 := by ring
    _ ≤ (1 / 16) * Real.log z - Real.log 2 := by linarith
    _ = Real.log ((z : ℝ) ^ ((1 : ℝ) / 16) / 2) := hlog2.symm
    _ ≤ Real.log (Zz z) := hlog1

/-- `z ≤ x` in-regime (`z ≤ z³ ≤ x`). -/
lemma ert2_z_le_x {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) : z ≤ x := by
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast le_trans (Nat.one_le_pow _ _ (by norm_num)) hz100
  have h3 : (z : ℝ) ≤ (z : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (z : ℝ) - 1) (sq_nonneg (z : ℝ)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (z : ℝ) - 1) (by linarith : (0 : ℝ) ≤ (z : ℝ))]
  exact_mod_cast le_trans h3 hzx

/-- `100 ≤ L'` in the master regime (T2′-local copy; `x ≥ 100^48`). -/
lemma ert2_Lwin_ge {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
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
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    calc Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
      _ ≤ 100 := by norm_num
  have h1 : Real.log ((100 : ℝ) ^ 48) ≤ Real.log x := Real.log_le_log (by positivity) hx48
  rw [Real.log_pow] at h1
  have h2 : Real.log x ≤ Lwin x := by
    rw [Lwin]
    exact Real.log_le_log hxpos (by linarith [Nat.cast_nonneg (α := ℝ) x])
  have h3 : (100 : ℝ) ≤ 48 * Real.log 100 := by nlinarith
  push_cast at h1
  linarith

/-- The scale identity `1/log z = z₀/L'` (T2′-local copy). -/
lemma ert2_inv_log_z {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    1 / Real.log z = z0 z x / Lwin x := by
  have hL : 100 ≤ Lwin x := ert2_Lwin_ge hz100 hzx
  have hz1 : (1 : ℝ) < (z : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 100 ^ 16) hz100
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hL0 : Lwin x ≠ 0 := by linarith
  have hlz0 : Real.log z ≠ 0 := hlogz.ne'
  rw [z0]
  field_simp

/-- **The sift-floor count conversion** (T2′-local copy): `1/(log Zz)² ≤ 1024·(z₀/L')²`. -/
lemma ert2_inv_logZz_sq {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    1 / Real.log (Zz z) ^ 2 ≤ 1024 * (z0 z x / Lwin x) ^ 2 := by
  have hz1 : (1 : ℝ) < (z : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 100 ^ 16) hz100
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hZzlog : Real.log z / 32 ≤ Real.log (Zz z) := ert2_log_Zz_ge hz100
  have hpos : (0 : ℝ) < Real.log z / 32 := by linarith
  have hsq : (Real.log z / 32) ^ 2 ≤ Real.log (Zz z) ^ 2 := pow_le_pow_left₀ hpos.le hZzlog 2
  calc 1 / Real.log (Zz z) ^ 2 ≤ 1 / (Real.log z / 32) ^ 2 :=
        one_div_le_one_div_of_le (pow_pos hpos 2) hsq
    _ = 1024 * (1 / Real.log z) ^ 2 := by rw [div_pow, one_div, one_div]; ring
    _ = 1024 * (z0 z x / Lwin x) ^ 2 := by rw [ert2_inv_log_z hz100 hzx]

/-- `PretenseSum χ N ≥ 0` (T2′-local copy). -/
lemma ert2_PS_nonneg (χ : DirichletCharacter ℂ q) (N : ℕ) : 0 ≤ PretenseSum χ N := by
  rw [PretenseSum]
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)) (by positivity)

/-- **The `Zz`-legality gate.**  For any modulus `d` obeying the T2′ law `d·z ≤ 2x+2`,
    the `l2c_pair_count_clean` legality holds at the `Zz` sift floor:
    `d·Zz⁸·(log Zz)² ≤ 32x` (with `z^{3/4}` room: `(log z)² ≤ 64·z^{1/4}`). -/
lemma ert2_legality {z x d : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (hd : d * z ≤ 2 * x + 2) :
    (d : ℝ) * (Zz z : ℝ) ^ 8 * Real.log (Zz z) ^ 2 ≤ 32 * x := by
  have hz1 : 1 ≤ z := le_trans (Nat.one_le_pow _ _ (by norm_num)) hz100
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    calc (1 : ℝ) ≤ (z : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hz1)
      _ ≤ (x : ℝ) := hzx
  have hdR : (d : ℝ) * z ≤ 2 * x + 2 := by exact_mod_cast hd
  have hdnn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hZz100 : 100 ≤ Zz z := Zz_ge_100 hz100
  have hZzpos : (0 : ℝ) < (Zz z : ℝ) := by exact_mod_cast (by omega : 0 < Zz z)
  have hZzle : (Zz z : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast (ert2_Zz_lt_z (by omega : 2 ≤ z)).le
  have hlogZznn : 0 ≤ Real.log (Zz z) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Zz z))
  have hlogsq : Real.log (Zz z) ^ 2 ≤ Real.log z ^ 2 :=
    pow_le_pow_left₀ hlogZznn (Real.log_le_log hZzpos hZzle) 2
  have hY : Real.log (Zz z) ^ 2 ≤ 64 * (z : ℝ) ^ ((1 : ℝ) / 4) :=
    hlogsq.trans (ert2_log_sq_le hz1)
  have hq_pos : (0 : ℝ) < (z : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hzpos _
  have h34 : (z : ℝ) ^ ((1 : ℝ) / 2) * (z : ℝ) ^ ((1 : ℝ) / 4) = (z : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hzpos]; norm_num
  have hzsplit : (z : ℝ) ^ ((3 : ℝ) / 4) * (z : ℝ) ^ ((1 : ℝ) / 4) = (z : ℝ) := by
    rw [← Real.rpow_add hzpos, show (3 : ℝ) / 4 + 1 / 4 = 1 by norm_num, Real.rpow_one]
  have hz14 : (10 : ℝ) ^ 8 ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := by
    have h4 : ((100 : ℝ) ^ 16) ^ ((1 : ℝ) / 4) = (100 : ℝ) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast (100 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100),
          show ((16 : ℕ) : ℝ) * ((1 : ℝ) / 4) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hzr : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
    calc (10 : ℝ) ^ 8 = (100 : ℝ) ^ (4 : ℕ) := by norm_num
      _ = ((100 : ℝ) ^ 16) ^ ((1 : ℝ) / 4) := h4.symm
      _ ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) hzr (by norm_num)
  have step3 : (d : ℝ) * (z : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 * x + 2) / (z : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [le_div_iff₀ hq_pos]
    calc (d : ℝ) * (z : ℝ) ^ ((3 : ℝ) / 4) * (z : ℝ) ^ ((1 : ℝ) / 4)
        = (d : ℝ) * ((z : ℝ) ^ ((3 : ℝ) / 4) * (z : ℝ) ^ ((1 : ℝ) / 4)) := by ring
      _ = (d : ℝ) * z := by rw [hzsplit]
      _ ≤ 2 * x + 2 := hdR
  calc (d : ℝ) * (Zz z : ℝ) ^ 8 * Real.log (Zz z) ^ 2
      ≤ (d : ℝ) * (z : ℝ) ^ ((1 : ℝ) / 2) * (64 * (z : ℝ) ^ ((1 : ℝ) / 4)) := by
        refine mul_le_mul ?_ hY (sq_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left (ert2_Zz_pow8_le hz1) hdnn
    _ = 64 * ((d : ℝ) * (z : ℝ) ^ ((3 : ℝ) / 4)) := by rw [← h34]; ring
    _ ≤ 64 * ((2 * x + 2) / (z : ℝ) ^ ((1 : ℝ) / 4)) := by
        exact mul_le_mul_of_nonneg_left step3 (by norm_num)
    _ = 64 * (2 * x + 2) / (z : ℝ) ^ ((1 : ℝ) / 4) := by ring
    _ ≤ 32 * x := by
        rw [div_le_iff₀ hq_pos]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 32 * (x : ℝ))
          (by linarith : (0 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) - 10 ^ 8)]

/-- **Exponent absorption (square form).**  `z₀²·e^{(log2)z₀} ≤ e^{5z₀}`. -/
lemma ert2_absorb2 {z x : ℕ} (hz2 : 2 ≤ z) :
    z0 z x ^ 2 * Real.exp (Real.log 2 * z0 z x) ≤ Real.exp (5 * z0 z x) := by
  have hz0 : 0 ≤ z0 z x := z0_nonneg hz2
  have ht : z0 z x ≤ Real.exp (z0 z x) := by linarith [Real.add_one_le_exp (z0 z x)]
  have h1 : z0 z x ^ 2 ≤ Real.exp (2 * z0 z x) := by
    calc z0 z x ^ 2 ≤ Real.exp (z0 z x) ^ 2 := pow_le_pow_left₀ hz0 ht 2
      _ = Real.exp (2 * z0 z x) := by rw [← Real.exp_nat_mul]; norm_num
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  calc z0 z x ^ 2 * Real.exp (Real.log 2 * z0 z x)
      ≤ Real.exp (2 * z0 z x) * Real.exp (Real.log 2 * z0 z x) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (2 * z0 z x + Real.log 2 * z0 z x) := by rw [← Real.exp_add]
    _ ≤ Real.exp (5 * z0 z x) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hlog2)]

/-- **Exponent absorption (cube form).**  `z₀³·e^{(log2)z₀} ≤ e^{5z₀}`. -/
lemma ert2_absorb3 {z x : ℕ} (hz2 : 2 ≤ z) :
    z0 z x ^ 3 * Real.exp (Real.log 2 * z0 z x) ≤ Real.exp (5 * z0 z x) := by
  have hz0 : 0 ≤ z0 z x := z0_nonneg hz2
  have ht : z0 z x ≤ Real.exp (z0 z x) := by linarith [Real.add_one_le_exp (z0 z x)]
  have h1 : z0 z x ^ 3 ≤ Real.exp (3 * z0 z x) := by
    calc z0 z x ^ 3 ≤ Real.exp (z0 z x) ^ 3 := pow_le_pow_left₀ hz0 ht 3
      _ = Real.exp (3 * z0 z x) := by rw [← Real.exp_nat_mul]; norm_num
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  calc z0 z x ^ 3 * Real.exp (Real.log 2 * z0 z x)
      ≤ Real.exp (3 * z0 z x) * Real.exp (Real.log 2 * z0 z x) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (3 * z0 z x + Real.log 2 * z0 z x) := by rw [← Real.exp_add]
    _ ≤ Real.exp (5 * z0 z x) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hlog2)]

/-! ## §2 — the structural layer: parity, the `χ=+1` packet, the swapped modulus law -/

/-- Divisors of odd numbers are odd. -/
lemma ert2_odd_of_dvd {a b : ℕ} (hb : Odd b) (h : a ∣ b) : Odd a := by
  rcases Nat.even_or_odd a with he | ho
  · exfalso
    obtain ⟨c, rfl⟩ := h
    rw [Nat.odd_iff, Nat.mul_mod, Nat.even_iff.mp he] at hb
    simp at hb
  · exact ho

/-- Odd times odd is odd. -/
lemma ert2_odd_mul {a b : ℕ} (ha : Odd a) (hb : Odd b) : Odd (a * b) := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  exact ⟨2 * i * j + i + j, by subst hi hj; ring⟩

/-- **The E_R parity gift.**  A prime window element exceeds `x ≥ 2`, so `n` is odd and
    `n+2` is odd — the even-block corner is empty in every `E_R` prime family. -/
lemma ert2_np2_odd {χ : DirichletCharacter ℂ q} {z x n : ℕ} (hx2 : 2 ≤ x)
    (hn : n ∈ l2cWindow χ z x) (hp : n.Prime) : Odd (n + 2) := by
  have hxn : x < n := ((l2cWindow_mem_iff χ z x n).mp hn).1.1
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
  exact ⟨k + 1, by omega⟩

/-- `Λ(w) ≤ L'` for a divisor `w` of an in-window value `m ≤ 2x+2`. -/
lemma ert2_vonMangoldt_le_Lwin {x w m : ℕ} (hm0 : 0 < m) (hw : w ∣ m)
    (hm : m ≤ 2 * x + 2) : Λ w ≤ Lwin x := by
  have hw0 : 0 < w := Nat.pos_of_dvd_of_pos hw hm0
  have hwle : w ≤ 2 * x + 2 := le_trans (Nat.le_of_dvd hm0 hw) hm
  refine le_trans vonMangoldt_le_log ?_
  rw [Lwin]
  refine Real.log_le_log (by exact_mod_cast hw0) ?_
  have h : (w : ℝ) ≤ ((2 * x + 2 : ℕ) : ℝ) := by exact_mod_cast hwle
  push_cast at h
  linarith

/-- The `χ=−1` block divides `n+2`. -/
lemma ert2_w_dvd (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : nMinus χ (n + 2) ∣ n + 2 :=
  ⟨nPlus χ (n + 2), by
    rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq (by omega) (l2cWindow_np2_coprime_q χ hn)⟩

/-- **The `χ=+1` packet.**  On a window element with `1 < (n+2)₊`, the least prime
    `p'' := minFac (n+2)₊` is a `χ=+1` prime `≥ z` (window roughness). -/
lemma ert2_pplus_packet (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (h1 : 1 < nPlus χ (n + 2)) :
    (nPlus χ (n + 2)).minFac.Prime ∧ chiRe χ ((nPlus χ (n + 2)).minFac) = 1 ∧
      z ≤ (nPlus χ (n + 2)).minFac := by
  have hcop2 : Nat.Coprime (n + 2) q := l2cWindow_np2_coprime_q χ hn
  have hfact : n + 2 = nPlus χ (n + 2) * nMinus χ (n + 2) :=
    eq_nPlus_mul_nMinus χ hsq (by omega) hcop2
  have hM0 : nPlus χ (n + 2) ≠ 0 := by omega
  have hpf : (nPlus χ (n + 2)).minFac.Prime := Nat.minFac_prime (by omega)
  have hdvdM : (nPlus χ (n + 2)).minFac ∣ nPlus χ (n + 2) := Nat.minFac_dvd _
  have hmem : (nPlus χ (n + 2)).minFac ∈ (nPlus χ (n + 2)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpf, hdvdM, hM0⟩
  have hsign : chiRe χ ((nPlus χ (n + 2)).minFac) = 1 := nPlus_sign hmem
  have hdvdn2 : (nPlus χ (n + 2)).minFac ∣ n + 2 :=
    hdvdM.trans ⟨nMinus χ (n + 2), hfact⟩
  exact ⟨hpf, hsign,
    l2cWindow_roughness χ z x hn hpf (hdvdn2.mul_left n) (by rw [hsign]; norm_num)⟩

/-- **The T2′ (roles-swapped) REPAIRED modulus law.**  On a window element whose plus-part
    `M := (n+2)₊` is composite, the cofactor `c := M/minFac M` satisfies `c ≥ z`, is
    `z`-rough, and `w·p''·c = n+2` — whence the modulus `d₂ := w·p'' = (n+2)/c` obeys
    `d₂·z ≤ 2x+2` (freeze §S4, `E_R` T2-mirror). -/
lemma ert2_cofactor_law (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (h1 : 1 < nPlus χ (n + 2))
    (hcomp : ¬ (nPlus χ (n + 2)).Prime) :
    ∃ c : ℕ, nMinus χ (n + 2) * (nPlus χ (n + 2)).minFac * c = n + 2 ∧ z ≤ c ∧
      ∀ r : ℕ, r.Prime → r ∣ c → z ≤ r := by
  have hcop2 : Nat.Coprime (n + 2) q := l2cWindow_np2_coprime_q χ hn
  have hfact : n + 2 = nPlus χ (n + 2) * nMinus χ (n + 2) :=
    eq_nPlus_mul_nMinus χ hsq (by omega) hcop2
  have hM0 : nPlus χ (n + 2) ≠ 0 := by omega
  have hPdvd : nPlus χ (n + 2) ∣ n + 2 := ⟨nMinus χ (n + 2), hfact⟩
  have hpf : (nPlus χ (n + 2)).minFac.Prime := Nat.minFac_prime (by omega)
  have hpc : (nPlus χ (n + 2)).minFac * (nPlus χ (n + 2) / (nPlus χ (n + 2)).minFac)
      = nPlus χ (n + 2) := Nat.mul_div_cancel' (Nat.minFac_dvd _)
  set c := nPlus χ (n + 2) / (nPlus χ (n + 2)).minFac with hcdef
  clear_value c
  have hc2 : 2 ≤ c := by
    by_contra hcon
    rcases (by omega : c = 0 ∨ c = 1) with h0 | h1'
    · rw [h0, mul_zero] at hpc; exact hM0 hpc.symm
    · rw [h1', mul_one] at hpc; exact hcomp (hpc ▸ hpf)
  have hcdvdM : c ∣ nPlus χ (n + 2) := ⟨(nPlus χ (n + 2)).minFac, by rw [mul_comm]; exact hpc.symm⟩
  have hrough : ∀ r : ℕ, r.Prime → r ∣ c → z ≤ r := by
    intro r hr hrc
    have hrM : r ∣ nPlus χ (n + 2) := hrc.trans hcdvdM
    have hrmem : r ∈ (nPlus χ (n + 2)).primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrM, hM0⟩
    have hrsign : chiRe χ r = 1 := nPlus_sign hrmem
    exact l2cWindow_roughness χ z x hn hr ((hrM.trans hPdvd).mul_left n)
      (by rw [hrsign]; norm_num)
  obtain ⟨r, hr, hrc⟩ := Nat.exists_prime_and_dvd (by omega : c ≠ 1)
  have hzc : z ≤ c := le_trans (hrough r hr hrc) (Nat.le_of_dvd (by omega) hrc)
  refine ⟨c, ?_, hzc, hrough⟩
  calc nMinus χ (n + 2) * (nPlus χ (n + 2)).minFac * c
      = nMinus χ (n + 2) * ((nPlus χ (n + 2)).minFac * c) := by ring
    _ = nMinus χ (n + 2) * nPlus χ (n + 2) := by rw [hpc]
    _ = n + 2 := by rw [mul_comm]; exact hfact.symm

/-- **The guard pays route B.**  A non-junk prime-power block past the `z^{1/4}` threshold
    has base `> Zz` — so it rides the sifted cofactor at the `Zz` floor (catch #245). -/
lemma ert2_base_rough {z w : ℕ} (hz100 : 100 ^ 16 ≤ z) (hpp : IsPrimePow w)
    (hK : ert2K z < w) (hnj : ¬ ERT2'JunkBlock z w) : Zz z < w.minFac := by
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast le_trans (Nat.one_le_pow _ _ (by norm_num)) hz100
  obtain ⟨p, e, hp, he, hpe⟩ := hpp
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  have hmf : w.minFac = p := by rw [← hpe]; exact hp'.pow_minFac (by omega)
  have hwR : (z : ℝ) ^ ((1 : ℝ) / 4) < (w : ℝ) := by
    have hfl : (z : ℝ) ^ ((1 : ℝ) / 4) < (ert2K z : ℝ) + 1 := by
      rw [ert2K]; exact Nat.lt_floor_add_one _
    have h2 : ((ert2K z + 1 : ℕ) : ℝ) ≤ (w : ℝ) := by exact_mod_cast (by omega : ert2K z + 1 ≤ w)
    push_cast at h2
    linarith
  rcases Nat.lt_or_ge (Zz z) p with hlt | hge
  · rw [hmf]; exact hlt
  · rcases eq_or_lt_of_le (by omega : 1 ≤ e) with he1 | he2
    · exfalso
      have hwp : w = p := by rw [← hpe, ← he1, pow_one]
      have hZle : (Zz z : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) :=
        le_trans ert2_Zz_le_rpow (Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num))
      have hpZ : (p : ℝ) ≤ (Zz z : ℝ) := by exact_mod_cast hge
      rw [hwp] at hwR
      linarith
    · exact absurd ⟨p, e, hp', hge, by omega, hpe.symm, hwR⟩ hnj

/-- **The primorial coprimality builder.**  A number all of whose prime divisors exceed `Z`
    is coprime to `primorial Z` — the sift-floor soundness discharge (catch #245). -/
lemma ert2_coprime_primorial {Z m : ℕ} (h : ∀ r : ℕ, r.Prime → r ∣ m → Z < r) :
    Nat.Coprime (primorial Z) m := by
  unfold primorial
  refine Nat.Coprime.prod_left ?_
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  refine (Nat.Prime.coprime_iff_not_dvd hp.2).mpr fun hd => ?_
  have := h p hp.2 hd
  omega

/-- **The T2′ per-term cap.**  `Λ(n)·(Λ̃−Λ)(n+2) ≤ e^{(log2)z₀}·L'·Λ(w)` on the
    single-block class (the sharp cap that keeps `Λ(w)` — mandatory per T3 catch 1). -/
lemma ert2_term_cap (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hz2 : 2 ≤ z) (hn : n ∈ l2cWindow χ z x) (hpp : IsPrimePow (nMinus χ (n + 2))) :
    Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x * Λ (nMinus χ (n + 2)) := by
  have hΛn : Λ n ≤ Lwin x := l2cWindow_vonMangoldt_cap χ hn
  have hsharp : LamTilde χ (n + 2) ≤ Real.exp (Real.log 2 * z0 z x) * Λ (nMinus χ (n + 2)) :=
    lamTilde_single_block_le χ hsq z x hz2 (by omega) (l2cWindow_np2_coprime_q χ hn)
      (l2cWindow_add_two_le χ hn)
      (fun p hp hpd hchi => l2cWindow_rough_add_two χ hn hp hpd hchi) hpp
  calc Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ Λ n * LamTilde χ (n + 2) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ vonMangoldt_nonneg) vonMangoldt_nonneg
    _ ≤ Lwin x * (Real.exp (Real.log 2 * z0 z x) * Λ (nMinus χ (n + 2))) :=
        mul_le_mul hΛn hsharp (lamTilde_nonneg χ hsq (n + 2)) (Lwin_nonneg x)
    _ = Real.exp (Real.log 2 * z0 z x) * Lwin x * Λ (nMinus χ (n + 2)) := by ring

/-! ## §3 — the fiber counts (`l2c_pair_count_clean` at `d₁ = 1`, sift floor `Zz`) -/

/-- A prime divisor of a prime power is its base (`minFac`). -/
lemma ert2_pp_prime_dvd {w r : ℕ} (hpp : IsPrimePow w) (hr : r.Prime) (hrd : r ∣ w) :
    r = w.minFac := by
  obtain ⟨ρ, e, hρ, he, hρe⟩ := hpp
  have hρ' : ρ.Prime := Nat.prime_iff.mpr hρ
  have hmf : w.minFac = ρ := by rw [← hρe]; exact hρ'.pow_minFac (by omega)
  rw [hmf]
  have hpow : r ∣ ρ ^ e := hρe ▸ hrd
  exact (Nat.prime_dvd_prime_iff_eq hr hρ').mp (hr.dvd_of_dvd_pow hpow)

/-- **The clean count wrapper.**  For an odd modulus `d₂` obeying the T2′ law
    `d₂·z ≤ 2x+2` and a totient-ratio budget `(d₂/φ(d₂))² ≤ C`, the `Zz`-sifted
    `d₁ = 1` pair count is `≤ 128·C·(x/d₂)/(log Zz)²`. -/
lemma ert2_clean_count {z x d₂ : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (hd₂ : 0 < d₂) (ho2 : Odd d₂) (hdz : d₂ * z ≤ 2 * x + 2) {C : ℝ}
    (hratio : ((d₂ : ℝ) / (Nat.totient d₂ : ℝ)) ^ 2 ≤ C) :
    (((baseSet x 1 d₂).filter
        (fun n => Nat.Coprime (primorial (Zz z)) ((n / 1) * ((n + 2) / d₂)))).card : ℝ)
      ≤ 128 * C * ((x : ℝ) / (d₂ : ℝ)) / Real.log (Zz z) ^ 2 := by
  have hZz := Zz_ge_100 hz100
  have hlegR : ((1 : ℕ) : ℝ) * ((d₂ : ℕ) : ℝ) * (Zz z : ℝ) ^ 8 * Real.log (Zz z) ^ 2
      ≤ 32 * x := by
    rw [Nat.cast_one, one_mul]
    exact ert2_legality hz100 hzx hdz
  have hcount := l2c_pair_count_clean (x := x) hZz Nat.one_pos hd₂ odd_one ho2
    (Nat.coprime_one_left d₂) hlegR
  simp only [Nat.cast_one, one_mul] at hcount
  have hlogsqpos : (0 : ℝ) < Real.log (Zz z) ^ 2 :=
    pow_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < Zz z))) 2
  have hxd : (0 : ℝ) ≤ (x : ℝ) / (d₂ : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h1 : 128 * ((d₂ : ℝ) / (Nat.totient d₂ : ℝ)) ^ 2 * ((x : ℝ) / (d₂ : ℝ))
      ≤ 128 * C * ((x : ℝ) / (d₂ : ℝ)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio) hxd]
  refine le_trans hcount ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hlogsqpos.le)

open Classical in
/-- **The route-A fiber count.**  A set of T2′ elements sharing the block pair
    `(w₀, p₀)` (with `w₀ ≤ K` modulus-routed) has `≤ 2048·(x/(w₀p₀))/(log Zz)²`
    elements: each lies in the `Zz`-sifted `baseSet x 1 (w₀·p₀)` (`n` prime `> x` and the
    `z`-rough cofactor `c` clear the floor), and `(w₀p₀/φ)² ≤ 16`. -/
lemma ert2_fiberA_card (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x w₀ p₀ : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) {T : Finset ℕ}
    (hT : ∀ n ∈ T, n ∈ l2cWindow χ z x ∧ n.Prime ∧ IsPrimePow (nMinus χ (n + 2)) ∧
      1 < nPlus χ (n + 2) ∧ ¬ (nPlus χ (n + 2)).Prime ∧ nMinus χ (n + 2) = w₀ ∧
      (nPlus χ (n + 2)).minFac = p₀ ∧ w₀ ≤ ert2K z) :
    (T.card : ℝ) ≤ 2048 * ((x : ℝ) / ((w₀ : ℝ) * (p₀ : ℝ))) / Real.log (Zz z) ^ 2 := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨n₀, hn₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (by positivity) (sq_nonneg _)
  obtain ⟨hn₀w, hn₀p, hn₀pp, hn₀1, hn₀c, hn₀eq, hn₀mf, hwK⟩ := hT n₀ hn₀
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hzlex : z ≤ x := ert2_z_le_x hz100 hzx
  have hx2 : 2 ≤ x := le_trans (le_trans (by norm_num) hz100) hzlex
  -- the χ=+1 packet at p₀ and the witness cofactor
  have hpk := ert2_pplus_packet χ hsq hn₀w hn₀1
  rw [hn₀mf] at hpk
  obtain ⟨hp₀, hchi₀, hzp₀⟩ := hpk
  obtain ⟨c₀, hc₀, hzc₀, _⟩ := ert2_cofactor_law χ hsq hn₀w hn₀1 hn₀c
  rw [hn₀eq, hn₀mf] at hc₀
  have hpp₀ : IsPrimePow w₀ := hn₀eq ▸ hn₀pp
  have hw₀pos : 0 < w₀ := hpp₀.pos
  have hd₂pos : 0 < w₀ * p₀ := Nat.mul_pos hw₀pos hp₀.pos
  -- parity and coprimality of the modulus
  have hoddn₂ : Odd (n₀ + 2) := ert2_np2_odd hx2 hn₀w hn₀p
  have hoddw : Odd w₀ := ert2_odd_of_dvd hoddn₂ (hn₀eq ▸ ert2_w_dvd χ hsq hn₀w)
  have hoddp : Odd p₀ := hp₀.odd_of_ne_two (by omega)
  have hodd₂ : Odd (w₀ * p₀) := ert2_odd_mul hoddw hoddp
  -- the modulus law
  have hdz : (w₀ * p₀) * z ≤ 2 * x + 2 := by
    calc (w₀ * p₀) * z ≤ (w₀ * p₀) * c₀ := Nat.mul_le_mul_left _ hzc₀
      _ = n₀ + 2 := hc₀
      _ ≤ 2 * x + 2 := by have := l2cWindow_le χ hn₀w; omega
  -- the totient-ratio budget
  have hKz : ert2K z < z := ert2_K_lt_z hz2
  have hcopwp : Nat.Coprime w₀ p₀ := by
    refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp₀).mpr fun hdvd => ?_)
    have hle : p₀ ≤ w₀ := Nat.le_of_dvd hw₀pos hdvd
    omega
  have h2w : w₀ ≤ 2 * Nat.totient w₀ := by
    obtain ⟨ρ, e, hρ, he, hρe⟩ := hpp₀
    have hρ' : ρ.Prime := Nat.prime_iff.mpr hρ
    rw [← hρe, Nat.totient_prime_pow hρ' he]
    have h2ρ : ρ ≤ 2 * (ρ - 1) := by have := hρ'.two_le; omega
    calc ρ ^ e = ρ ^ (e - 1) * ρ := by rw [← pow_succ]; congr 1; omega
      _ ≤ ρ ^ (e - 1) * (2 * (ρ - 1)) := Nat.mul_le_mul_left _ h2ρ
      _ = 2 * (ρ ^ (e - 1) * (ρ - 1)) := by ring
  have h2p : p₀ ≤ 2 * Nat.totient p₀ := by
    rw [Nat.totient_prime hp₀]
    have := hp₀.two_le
    omega
  have hphiN : w₀ * p₀ ≤ 4 * Nat.totient (w₀ * p₀) := by
    rw [Nat.totient_mul hcopwp]
    calc w₀ * p₀ ≤ (2 * Nat.totient w₀) * (2 * Nat.totient p₀) := Nat.mul_le_mul h2w h2p
      _ = 4 * (Nat.totient w₀ * Nat.totient p₀) := by ring
  have hφpos : (0 : ℝ) < (Nat.totient (w₀ * p₀) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hd₂pos
  have hratio : (((w₀ * p₀ : ℕ) : ℝ) / (Nat.totient (w₀ * p₀) : ℝ)) ^ 2 ≤ (16 : ℝ) := by
    have hle : ((w₀ * p₀ : ℕ) : ℝ) / (Nat.totient (w₀ * p₀) : ℝ) ≤ 4 := by
      rw [div_le_iff₀ hφpos]
      exact_mod_cast hphiN
    have hnn : (0 : ℝ) ≤ ((w₀ * p₀ : ℕ) : ℝ) / (Nat.totient (w₀ * p₀) : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) hφpos.le
    calc (((w₀ * p₀ : ℕ) : ℝ) / (Nat.totient (w₀ * p₀) : ℝ)) ^ 2 ≤ 4 ^ 2 :=
          pow_le_pow_left₀ hnn hle 2
      _ = 16 := by norm_num
  -- the fiber sits inside the sifted baseSet
  have hsub : T ⊆ (baseSet x 1 (w₀ * p₀)).filter
      (fun n => Nat.Coprime (primorial (Zz z)) ((n / 1) * ((n + 2) / (w₀ * p₀)))) := by
    intro n hn
    obtain ⟨hnw, hnp, _, hn1, hnc, hneq, hnmf, _⟩ := hT n hn
    have hmem := (l2cWindow_mem_iff χ z x n).mp hnw
    obtain ⟨c, hc, hzc, hcrough⟩ := ert2_cofactor_law χ hsq hnw hn1 hnc
    rw [hneq, hnmf] at hc
    have hdvd : w₀ * p₀ ∣ n + 2 := ⟨c, hc.symm⟩
    have hquot : (n + 2) / (w₀ * p₀) = c := by
      rw [← hc]
      exact Nat.mul_div_cancel_left c hd₂pos
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [baseSet, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hmem.1.1, hmem.1.2⟩, one_dvd n, hdvd⟩
    · rw [Nat.div_one, hquot]
      refine ert2_coprime_primorial fun r hr hrd => ?_
      have hZzz : Zz z < z := ert2_Zz_lt_z hz2
      rcases (Nat.Prime.dvd_mul hr).mp hrd with hrn | hrc
      · have hrn' : r = n := (Nat.prime_dvd_prime_iff_eq hr hnp).mp hrn
        have hxn : x < n := hmem.1.1
        omega
      · have := hcrough r hr hrc
        omega
  -- count and constants
  calc (T.card : ℝ)
      ≤ (((baseSet x 1 (w₀ * p₀)).filter (fun n =>
          Nat.Coprime (primorial (Zz z)) ((n / 1) * ((n + 2) / (w₀ * p₀))))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ 128 * 16 * ((x : ℝ) / ((w₀ * p₀ : ℕ) : ℝ)) / Real.log (Zz z) ^ 2 :=
        ert2_clean_count hz100 hzx hd₂pos hodd₂ hdz hratio
    _ = 2048 * ((x : ℝ) / ((w₀ : ℝ) * (p₀ : ℝ))) / Real.log (Zz z) ^ 2 := by
        push_cast
        ring

open Classical in
/-- **The route-B fiber count.**  T2′ elements sharing the `χ=+1` prime `p₀`, with the
    block `w > K` riding the sifted cofactor (its base `> Zz` by the catch-#245 guard),
    number `≤ 512·(x/p₀)/(log Zz)²`. -/
lemma ert2_fiberB_card (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x p₀ : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) {T : Finset ℕ}
    (hT : ∀ n ∈ T, n ∈ l2cWindow χ z x ∧ n.Prime ∧ IsPrimePow (nMinus χ (n + 2)) ∧
      1 < nPlus χ (n + 2) ∧ ¬ (nPlus χ (n + 2)).Prime ∧
      ¬ ERT2'JunkBlock z (nMinus χ (n + 2)) ∧ ert2K z < nMinus χ (n + 2) ∧
      (nPlus χ (n + 2)).minFac = p₀) :
    (T.card : ℝ) ≤ 512 * ((x : ℝ) / (p₀ : ℝ)) / Real.log (Zz z) ^ 2 := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨n₀, hn₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (by positivity) (sq_nonneg _)
  obtain ⟨hn₀w, hn₀p, hn₀pp, hn₀1, hn₀c, _, hn₀K, hn₀mf⟩ := hT n₀ hn₀
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hzlex : z ≤ x := ert2_z_le_x hz100 hzx
  have hx2 : 2 ≤ x := le_trans (le_trans (by norm_num) hz100) hzlex
  have hpk := ert2_pplus_packet χ hsq hn₀w hn₀1
  rw [hn₀mf] at hpk
  obtain ⟨hp₀, hchi₀, hzp₀⟩ := hpk
  obtain ⟨c₀, hc₀, hzc₀, _⟩ := ert2_cofactor_law χ hsq hn₀w hn₀1 hn₀c
  rw [hn₀mf] at hc₀
  have hw₀pos : 0 < nMinus χ (n₀ + 2) := nMinus_pos χ (n₀ + 2)
  have hoddp : Odd p₀ := hp₀.odd_of_ne_two (by omega)
  have hdz : p₀ * z ≤ 2 * x + 2 := by
    calc p₀ * z ≤ p₀ * c₀ := Nat.mul_le_mul_left _ hzc₀
      _ ≤ nMinus χ (n₀ + 2) * (p₀ * c₀) := Nat.le_mul_of_pos_left _ hw₀pos
      _ = nMinus χ (n₀ + 2) * p₀ * c₀ := by ring
      _ = n₀ + 2 := hc₀
      _ ≤ 2 * x + 2 := by have := l2cWindow_le χ hn₀w; omega
  have h2p : p₀ ≤ 2 * Nat.totient p₀ := by
    rw [Nat.totient_prime hp₀]
    have := hp₀.two_le
    omega
  have hφpos : (0 : ℝ) < (Nat.totient p₀ : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hp₀.pos
  have hratio : ((p₀ : ℝ) / (Nat.totient p₀ : ℝ)) ^ 2 ≤ (4 : ℝ) := by
    have hle : (p₀ : ℝ) / (Nat.totient p₀ : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hφpos]
      exact_mod_cast h2p
    have hnn : (0 : ℝ) ≤ (p₀ : ℝ) / (Nat.totient p₀ : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) hφpos.le
    calc ((p₀ : ℝ) / (Nat.totient p₀ : ℝ)) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ hnn hle 2
      _ = 4 := by norm_num
  have hsub : T ⊆ (baseSet x 1 p₀).filter
      (fun n => Nat.Coprime (primorial (Zz z)) ((n / 1) * ((n + 2) / p₀))) := by
    intro n hn
    obtain ⟨hnw, hnp, hnpp, hn1, hnc, hnj, hnK, hnmf⟩ := hT n hn
    have hmem := (l2cWindow_mem_iff χ z x n).mp hnw
    obtain ⟨c, hc, hzc, hcrough⟩ := ert2_cofactor_law χ hsq hnw hn1 hnc
    rw [hnmf] at hc
    have hprod : p₀ * (nMinus χ (n + 2) * c) = n + 2 := by
      calc p₀ * (nMinus χ (n + 2) * c) = nMinus χ (n + 2) * p₀ * c := by ring
        _ = n + 2 := hc
    have hdvd : p₀ ∣ n + 2 := ⟨nMinus χ (n + 2) * c, hprod.symm⟩
    have hquot : (n + 2) / p₀ = nMinus χ (n + 2) * c := by
      have h := Nat.mul_div_cancel_left (nMinus χ (n + 2) * c) hp₀.pos
      rw [hprod] at h
      exact h
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [baseSet, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hmem.1.1, hmem.1.2⟩, one_dvd n, hdvd⟩
    · rw [Nat.div_one, hquot]
      refine ert2_coprime_primorial fun r hr hrd => ?_
      have hZzz : Zz z < z := ert2_Zz_lt_z hz2
      rcases (Nat.Prime.dvd_mul hr).mp hrd with hrn | hrwc
      · have hrn' : r = n := (Nat.prime_dvd_prime_iff_eq hr hnp).mp hrn
        have hxn : x < n := hmem.1.1
        omega
      · rcases (Nat.Prime.dvd_mul hr).mp hrwc with hrw | hrc
        · have hbase : Zz z < (nMinus χ (n + 2)).minFac :=
            ert2_base_rough hz100 hnpp hnK hnj
          have hreq : r = (nMinus χ (n + 2)).minFac := ert2_pp_prime_dvd hnpp hr hrw
          omega
        · have := hcrough r hr hrc
          omega
  calc (T.card : ℝ)
      ≤ (((baseSet x 1 p₀).filter
          (fun n => Nat.Coprime (primorial (Zz z)) ((n / 1) * ((n + 2) / p₀)))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ 128 * 4 * ((x : ℝ) / (p₀ : ℝ)) / Real.log (Zz z) ^ 2 :=
        ert2_clean_count hz100 hzx hp₀.pos hoddp hdz hratio
    _ = 512 * ((x : ℝ) / (p₀ : ℝ)) / Real.log (Zz z) ^ 2 := by ring

/-! ## §4 — the route sums and the family budget

The T2′ family (with the catch-#245 junk guard on `w` and the catch-#246 `Odd n` guard)
splits at the `z^{1/4}` threshold `K`: route A (`w ≤ K`) fibers over the pair `(w, p'')`
with modulus `w·p''`; route B (`w > K`) fibers over `p''` alone, the block riding the
sifted cofactor.  Mertens pays `ΣΛ(w)/w ≤ log z`, the `χ=+1` conversion pays
`Σ1/p'' ≤ PS/log z`, and the `Aexp = 5` budget absorbs `z₀^{2,3}·e^{(log2)z₀}`. -/

/-- **The Mertens block cap.**  `Σ_{0<w≤K} Λ(w)/w ≤ log z` (Mertens up to `z^{1/4}`). -/
lemma ert2_mertens_cap {z : ℕ} (hz100 : 100 ^ 16 ≤ z) :
    ∑ w ∈ Finset.Ioc 0 (ert2K z), Λ w / (w : ℝ) ≤ Real.log z := by
  have hz1 : 1 ≤ z := le_trans (Nat.one_le_pow _ _ (by norm_num)) hz100
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have hK1 : 1 ≤ ert2K z := ert2_one_le_K hz100
  have h := mertens_vonMangoldt_div_le hK1
  have hKpos : (0 : ℝ) < (ert2K z : ℝ) := by exact_mod_cast hK1
  have hKz : Real.log (ert2K z) ≤ 1 / 4 * Real.log z := by
    have hlog := Real.log_le_log hKpos ert2_K_le_rpow
    rwa [Real.log_rpow hzpos] at hlog
  have hlog4 : Real.log 4 + 4 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have h64 : (64 : ℝ) ≤ Real.log z := ert2_logz_ge hz100
  linarith

open Classical in
/-- **The route-A sub-sum** (`w ≤ K`, modulus-routed): fibered over `(w, p'')`,
    counted by `ert2_fiberA_card`, summed by Mertens and the `PretenseSum`
    conversion; lands in the `J2` shape with constant `2²¹`. -/
lemma ert2_routeA_sum (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ ((l2cWindow χ z x).filter (fun n =>
        n.Prime ∧ Odd n ∧ IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2) ∧
          ¬ (nPlus χ (n + 2)).Prime ∧ ¬ ERT2'JunkBlock z (nMinus χ (n + 2)))).filter
        (fun n => nMinus χ (n + 2) ≤ ert2K z),
      Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ 2097152 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hz1lt : (1 : ℝ) < (z : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 100 ^ 16) hz100
  have hlogzpos : (0 : ℝ) < Real.log z := Real.log_pos hz1lt
  set S := ((l2cWindow χ z x).filter (fun n =>
      n.Prime ∧ Odd n ∧ IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2) ∧
        ¬ (nPlus χ (n + 2)).Prime ∧ ¬ ERT2'JunkBlock z (nMinus χ (n + 2)))).filter
      (fun n => nMinus χ (n + 2) ≤ ert2K z) with hS
  have hSfacts : ∀ n ∈ S, n ∈ l2cWindow χ z x ∧ n.Prime ∧ IsPrimePow (nMinus χ (n + 2)) ∧
      1 < nPlus χ (n + 2) ∧ ¬ (nPlus χ (n + 2)).Prime ∧ nMinus χ (n + 2) ≤ ert2K z := by
    intro n hn
    rw [hS, Finset.mem_filter] at hn
    obtain ⟨hn1, hnK⟩ := hn
    rw [Finset.mem_filter] at hn1
    exact ⟨hn1.1, hn1.2.1, hn1.2.2.2.1, hn1.2.2.2.2.1, hn1.2.2.2.2.2.1, hnK⟩
  -- Step 1: the sharp per-term cap
  have hstep1 : ∑ n ∈ S, Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ ∑ n ∈ S, Real.exp (Real.log 2 * z0 z x) * Lwin x * Λ (nMinus χ (n + 2)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hnw, _, hnpp, _, _, _⟩ := hSfacts n hn
    exact ert2_term_cap χ hsq hz2 hnw hnpp
  -- Step 2: fiber the weight sum over (w, p'')
  have hmaps : ∀ n ∈ S, (nMinus χ (n + 2), (nPlus χ (n + 2)).minFac)
      ∈ Finset.Ioc 0 (ert2K z) ×ˢ (Finset.range (2 * x + 2 + 1)).filter
        (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p) := by
    intro n hn
    obtain ⟨hnw, hnp, hnpp, hn1, hnc, hnK⟩ := hSfacts n hn
    rw [Finset.mem_product]
    refine ⟨Finset.mem_Ioc.mpr ⟨hnpp.pos, hnK⟩, ?_⟩
    obtain ⟨hpf, hsign, hzp⟩ := ert2_pplus_packet χ hsq hnw hn1
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hpf, hsign, hzp⟩
    have hMle : nPlus χ (n + 2) ≤ n + 2 := Nat.le_of_dvd (by omega)
      ⟨nMinus χ (n + 2), eq_nPlus_mul_nMinus χ hsq (by omega) (l2cWindow_np2_coprime_q χ hnw)⟩
    have hmfle : (nPlus χ (n + 2)).minFac ≤ nPlus χ (n + 2) := Nat.minFac_le (by omega)
    have hle2x := l2cWindow_le χ hnw
    omega
  have hfib : ∑ n ∈ S, Λ (nMinus χ (n + 2))
      = ∑ y ∈ Finset.Ioc 0 (ert2K z) ×ˢ (Finset.range (2 * x + 2 + 1)).filter
          (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p),
          ∑ n ∈ S.filter (fun n => (nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = y),
            Λ (nMinus χ (n + 2)) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  -- Step 3: the per-fiber count
  have hfiber : ∀ y ∈ Finset.Ioc 0 (ert2K z) ×ˢ (Finset.range (2 * x + 2 + 1)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p),
      ∑ n ∈ S.filter (fun n => (nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = y),
        Λ (nMinus χ (n + 2))
      ≤ Λ y.1 * (2048 * ((x : ℝ) / ((y.1 : ℝ) * (y.2 : ℝ))) / Real.log (Zz z) ^ 2) := by
    intro y _
    set F := S.filter (fun n => (nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = y) with hF
    have hcard : (F.card : ℝ)
        ≤ 2048 * ((x : ℝ) / ((y.1 : ℝ) * (y.2 : ℝ))) / Real.log (Zz z) ^ 2 := by
      refine ert2_fiberA_card χ hsq hz100 hzx ?_
      intro n hn
      rw [hF, Finset.mem_filter] at hn
      obtain ⟨hnS, hneq⟩ := hn
      obtain ⟨hnw, hnp, hnpp, hn1, hnc, hnK⟩ := hSfacts n hnS
      have h1 : nMinus χ (n + 2) = y.1 := by rw [← hneq]
      have h2 : (nPlus χ (n + 2)).minFac = y.2 := by rw [← hneq]
      exact ⟨hnw, hnp, hnpp, hn1, hnc, h1, h2, h1 ▸ hnK⟩
    have hconst : ∀ n ∈ F, Λ (nMinus χ (n + 2)) = Λ y.1 := by
      intro n hn
      rw [hF, Finset.mem_filter] at hn
      rw [← hn.2]
    calc ∑ n ∈ F, Λ (nMinus χ (n + 2)) = ∑ _n ∈ F, Λ y.1 := Finset.sum_congr rfl hconst
      _ = (F.card : ℝ) * Λ y.1 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2048 * ((x : ℝ) / ((y.1 : ℝ) * (y.2 : ℝ))) / Real.log (Zz z) ^ 2) * Λ y.1 :=
          mul_le_mul_of_nonneg_right hcard vonMangoldt_nonneg
      _ = Λ y.1 * (2048 * ((x : ℝ) / ((y.1 : ℝ) * (y.2 : ℝ))) / Real.log (Zz z) ^ 2) :=
          mul_comm _ _
  -- Step 4: factor the fibered bound
  have hstep4 : ∑ y ∈ Finset.Ioc 0 (ert2K z) ×ˢ (Finset.range (2 * x + 2 + 1)).filter
        (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p),
        Λ y.1 * (2048 * ((x : ℝ) / ((y.1 : ℝ) * (y.2 : ℝ))) / Real.log (Zz z) ^ 2)
      = 2048 * (x : ℝ) / Real.log (Zz z) ^ 2
          * ((∑ w ∈ Finset.Ioc 0 (ert2K z), Λ w / (w : ℝ))
            * ∑ p ∈ (Finset.range (2 * x + 2 + 1)).filter
                (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), 1 / (p : ℝ)) := by
    calc ∑ y ∈ Finset.Ioc 0 (ert2K z) ×ˢ (Finset.range (2 * x + 2 + 1)).filter
          (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p),
          Λ y.1 * (2048 * ((x : ℝ) / ((y.1 : ℝ) * (y.2 : ℝ))) / Real.log (Zz z) ^ 2)
        = ∑ w ∈ Finset.Ioc 0 (ert2K z), ∑ p ∈ (Finset.range (2 * x + 2 + 1)).filter
            (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p),
            Λ w * (2048 * ((x : ℝ) / ((w : ℝ) * (p : ℝ))) / Real.log (Zz z) ^ 2) :=
          Finset.sum_product _ _ _
      _ = 2048 * (x : ℝ) / Real.log (Zz z) ^ 2
            * ((∑ w ∈ Finset.Ioc 0 (ert2K z), Λ w / (w : ℝ))
              * ∑ p ∈ (Finset.range (2 * x + 2 + 1)).filter
                  (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), 1 / (p : ℝ)) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
  -- Step 5: the two caps and the final budget
  have hcapw : ∑ w ∈ Finset.Ioc 0 (ert2K z), Λ w / (w : ℝ) ≤ Real.log z :=
    ert2_mertens_cap hz100
  have hcapp := sum_inv_plusprime_le_pretense χ z (2 * x + 2)
    (lt_of_lt_of_le (by norm_num) hz100)
  have hSp_nn : 0 ≤ ∑ p ∈ (Finset.range (2 * x + 2 + 1)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), 1 / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hPS : 0 ≤ PretenseSum χ (2 * x + 2) := ert2_PS_nonneg χ _
  have hprod : (∑ w ∈ Finset.Ioc 0 (ert2K z), Λ w / (w : ℝ))
      * (∑ p ∈ (Finset.range (2 * x + 2 + 1)).filter
          (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), 1 / (p : ℝ))
      ≤ PretenseSum χ (2 * x + 2) := by
    calc _ ≤ Real.log z * (PretenseSum χ (2 * x + 2) / Real.log z) :=
          mul_le_mul hcapw hcapp hSp_nn hlogzpos.le
      _ = PretenseSum χ (2 * x + 2) := by
          rw [mul_comm]
          exact div_mul_cancel₀ _ hlogzpos.ne'
  have hL : 100 ≤ Lwin x := ert2_Lwin_ge hz100 hzx
  have hLpos : (0 : ℝ) < Lwin x := by linarith
  have hL0 : Lwin x ≠ 0 := hLpos.ne'
  have hinv := ert2_inv_logZz_sq hz100 hzx
  have habs := ert2_absorb2 (z := z) (x := x) hz2
  calc ∑ n ∈ S, Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ ∑ n ∈ S, Real.exp (Real.log 2 * z0 z x) * Lwin x * Λ (nMinus χ (n + 2)) := hstep1
    _ = Real.exp (Real.log 2 * z0 z x) * Lwin x * ∑ n ∈ S, Λ (nMinus χ (n + 2)) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x
          * (2048 * (x : ℝ) / Real.log (Zz z) ^ 2 * PretenseSum χ (2 * x + 2)) := by
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (Real.exp_pos _).le (Lwin_nonneg x))
        rw [hfib]
        refine le_trans (Finset.sum_le_sum hfiber) ?_
        rw [hstep4]
        refine mul_le_mul_of_nonneg_left hprod ?_
        positivity
    _ = (2048 * Real.exp (Real.log 2 * z0 z x) * Lwin x
          * ((x : ℝ) * PretenseSum χ (2 * x + 2))) * (1 / Real.log (Zz z) ^ 2) := by
        ring
    _ ≤ (2048 * Real.exp (Real.log 2 * z0 z x) * Lwin x
          * ((x : ℝ) * PretenseSum χ (2 * x + 2))) * (1024 * (z0 z x / Lwin x) ^ 2) := by
        refine mul_le_mul_of_nonneg_left hinv ?_
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
          (Lwin_nonneg x)) (mul_nonneg (Nat.cast_nonneg x) hPS)
    _ = 2097152 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2)
          * (z0 z x ^ 2 * Real.exp (Real.log 2 * z0 z x)) := by
        field_simp
        ring
    _ ≤ 2097152 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2)
          * Real.exp (5 * z0 z x) := by
        refine mul_le_mul_of_nonneg_left habs ?_
        exact mul_nonneg (mul_nonneg (by norm_num)
          (div_nonneg (Nat.cast_nonneg x) hLpos.le)) hPS
    _ = 2097152 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by ring

open Classical in
/-- **The route-B sub-sum** (`w > K`, cofactor-routed — sound by the catch-#245 guard):
    fibered over `p''` alone with the crude `Λ(w) ≤ L'` cap; lands in the `J2` shape
    with constant `2¹⁹`. -/
lemma ert2_routeB_sum (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ ((l2cWindow χ z x).filter (fun n =>
        n.Prime ∧ Odd n ∧ IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2) ∧
          ¬ (nPlus χ (n + 2)).Prime ∧ ¬ ERT2'JunkBlock z (nMinus χ (n + 2)))).filter
        (fun n => ¬ nMinus χ (n + 2) ≤ ert2K z),
      Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ 524288 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hz1lt : (1 : ℝ) < (z : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 100 ^ 16) hz100
  have hlogzpos : (0 : ℝ) < Real.log z := Real.log_pos hz1lt
  have hL : 100 ≤ Lwin x := ert2_Lwin_ge hz100 hzx
  have hLpos : (0 : ℝ) < Lwin x := by linarith
  have hL0 : Lwin x ≠ 0 := hLpos.ne'
  have hPS : 0 ≤ PretenseSum χ (2 * x + 2) := ert2_PS_nonneg χ _
  have hz0nn : 0 ≤ z0 z x := z0_nonneg hz2
  set S := ((l2cWindow χ z x).filter (fun n =>
      n.Prime ∧ Odd n ∧ IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2) ∧
        ¬ (nPlus χ (n + 2)).Prime ∧ ¬ ERT2'JunkBlock z (nMinus χ (n + 2)))).filter
      (fun n => ¬ nMinus χ (n + 2) ≤ ert2K z) with hS
  have hSfacts : ∀ n ∈ S, n ∈ l2cWindow χ z x ∧ n.Prime ∧ IsPrimePow (nMinus χ (n + 2)) ∧
      1 < nPlus χ (n + 2) ∧ ¬ (nPlus χ (n + 2)).Prime ∧
      ¬ ERT2'JunkBlock z (nMinus χ (n + 2)) ∧ ert2K z < nMinus χ (n + 2) := by
    intro n hn
    rw [hS, Finset.mem_filter] at hn
    obtain ⟨hn1, hnK⟩ := hn
    rw [Finset.mem_filter] at hn1
    exact ⟨hn1.1, hn1.2.1, hn1.2.2.2.1, hn1.2.2.2.2.1, hn1.2.2.2.2.2.1,
      hn1.2.2.2.2.2.2, Nat.lt_of_not_le hnK⟩
  -- the crude per-term cap E·L²
  have hstep1 : ∑ n ∈ S, Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ ∑ _n ∈ S, Real.exp (Real.log 2 * z0 z x) * Lwin x * Lwin x := by
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hnw, _, hnpp, _, _, _, _⟩ := hSfacts n hn
    refine le_trans (ert2_term_cap χ hsq hz2 hnw hnpp) ?_
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (Real.exp_pos _).le (Lwin_nonneg x))
    exact ert2_vonMangoldt_le_Lwin (by omega) (ert2_w_dvd χ hsq hnw)
      (l2cWindow_add_two_le χ hnw)
  -- the fibered cardinality bound over p''
  have hmaps : ∀ n ∈ S, (nPlus χ (n + 2)).minFac ∈ (Finset.range (2 * x + 2 + 1)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p) := by
    intro n hn
    obtain ⟨hnw, _, _, hn1, _, _, _⟩ := hSfacts n hn
    obtain ⟨hpf, hsign, hzp⟩ := ert2_pplus_packet χ hsq hnw hn1
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hpf, hsign, hzp⟩
    have hMle : nPlus χ (n + 2) ≤ n + 2 := Nat.le_of_dvd (by omega)
      ⟨nMinus χ (n + 2), eq_nPlus_mul_nMinus χ hsq (by omega) (l2cWindow_np2_coprime_q χ hnw)⟩
    have hmfle : (nPlus χ (n + 2)).minFac ≤ nPlus χ (n + 2) := Nat.minFac_le (by omega)
    have hle2x := l2cWindow_le χ hnw
    omega
  have hcard : (S.card : ℝ) ≤ 512 * (x : ℝ) / Real.log (Zz z) ^ 2
      * ∑ p ∈ (Finset.range (2 * x + 2 + 1)).filter
          (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), 1 / (p : ℝ) := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (fun n hn => Finset.mem_coe.mpr (hmaps n (Finset.mem_coe.mp hn)))
    have hcast : (S.card : ℝ) = ∑ p ∈ (Finset.range (2 * x + 2 + 1)).filter
        (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p),
        ((S.filter (fun n => (nPlus χ (n + 2)).minFac = p)).card : ℝ) := by
      rw [hfib]
      push_cast
      rfl
    rw [hcast]
    calc ∑ p ∈ (Finset.range (2 * x + 2 + 1)).filter
              (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p),
            ((S.filter (fun n => (nPlus χ (n + 2)).minFac = p)).card : ℝ)
        ≤ ∑ p ∈ (Finset.range (2 * x + 2 + 1)).filter
              (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p),
            512 * ((x : ℝ) / (p : ℝ)) / Real.log (Zz z) ^ 2 := by
          refine Finset.sum_le_sum fun p _ => ?_
          refine ert2_fiberB_card χ hsq hz100 hzx ?_
          intro n hn
          rw [Finset.mem_filter] at hn
          obtain ⟨hnS, hneq⟩ := hn
          obtain ⟨hnw, hnp, hnpp, hn1, hnc, hnj, hnK⟩ := hSfacts n hnS
          exact ⟨hnw, hnp, hnpp, hn1, hnc, hnj, hnK, hneq⟩
      _ = 512 * (x : ℝ) / Real.log (Zz z) ^ 2
            * ∑ p ∈ (Finset.range (2 * x + 2 + 1)).filter
                (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), 1 / (p : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
  -- assemble
  have hcapp := sum_inv_plusprime_le_pretense χ z (2 * x + 2)
    (lt_of_lt_of_le (by norm_num) hz100)
  have hinv := ert2_inv_logZz_sq hz100 hzx
  have habs := ert2_absorb3 (z := z) (x := x) hz2
  calc ∑ n ∈ S, Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ (S.card : ℝ) * (Real.exp (Real.log 2 * z0 z x) * Lwin x * Lwin x) := by
        refine le_trans hstep1 ?_
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (512 * (x : ℝ) / Real.log (Zz z) ^ 2
          * ∑ p ∈ (Finset.range (2 * x + 2 + 1)).filter
              (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), 1 / (p : ℝ))
          * (Real.exp (Real.log 2 * z0 z x) * Lwin x * Lwin x) := by
        refine mul_le_mul_of_nonneg_right hcard ?_
        exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Lwin_nonneg x)) (Lwin_nonneg x)
    _ ≤ (512 * (x : ℝ) / Real.log (Zz z) ^ 2 * (PretenseSum χ (2 * x + 2) / Real.log z))
          * (Real.exp (Real.log 2 * z0 z x) * Lwin x * Lwin x) := by
        refine mul_le_mul_of_nonneg_right ?_ ?_
        · refine mul_le_mul_of_nonneg_left hcapp ?_
          positivity
        · exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Lwin_nonneg x)) (Lwin_nonneg x)
    _ = (512 * (x : ℝ) * PretenseSum χ (2 * x + 2) * Lwin x ^ 2
          * Real.exp (Real.log 2 * z0 z x) * (1 / Real.log z))
          * (1 / Real.log (Zz z) ^ 2) := by ring
    _ = (512 * (x : ℝ) * PretenseSum χ (2 * x + 2) * Lwin x ^ 2
          * Real.exp (Real.log 2 * z0 z x) * (z0 z x / Lwin x))
          * (1 / Real.log (Zz z) ^ 2) := by
        rw [ert2_inv_log_z hz100 hzx]
    _ ≤ (512 * (x : ℝ) * PretenseSum χ (2 * x + 2) * Lwin x ^ 2
          * Real.exp (Real.log 2 * z0 z x) * (z0 z x / Lwin x))
          * (1024 * (z0 z x / Lwin x) ^ 2) := by
        refine mul_le_mul_of_nonneg_left hinv ?_
        refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          (Nat.cast_nonneg x)) hPS) (sq_nonneg _)) (Real.exp_pos _).le) ?_
        exact div_nonneg hz0nn hLpos.le
    _ = 524288 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2)
          * (z0 z x ^ 3 * Real.exp (Real.log 2 * z0 z x)) := by
        field_simp
        ring
    _ ≤ 524288 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2)
          * Real.exp (5 * z0 z x) := by
        refine mul_le_mul_of_nonneg_left habs ?_
        exact mul_nonneg (mul_nonneg (by norm_num)
          (div_nonneg (Nat.cast_nonneg x) hLpos.le)) hPS
    _ = 524288 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by ring

open Classical in
/-- **The `E_R` T2′ family budget** (node HB-L2c-F-ER-T2′; freeze §S4 `J2` row, `E_R`
    mirror, house amendments #245/#246).  Over the honest window, the T2′ family —
    `n` prime (odd), `n+2` single-block with composite plus-part, junk blocks excluded —
    obeys the frozen `J2` bound with `Cmain = 2²² = 4194304`:

    `Σ_{T2′} Λ(n)·(Λ̃−Λ)(n+2) ≤ Cmain·(x/L')·e^{5z₀}·PretenseSum χ (2x+2)`. -/
theorem ER_T2'_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (_hz8 : Lwin x ^ 8 ≤ (z : ℝ)) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ (l2cWindow χ z x).filter (fun n =>
        n.Prime ∧ Odd n ∧ IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2) ∧
          ¬ (nPlus χ (n + 2)).Prime ∧ ¬ ERT2'JunkBlock z (nMinus χ (n + 2))),
      Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ 4194304 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by
  have hL : 100 ≤ Lwin x := ert2_Lwin_ge hz100 hzx
  have hY : (0 : ℝ) ≤ (x : ℝ) / Lwin x * Real.exp (5 * z0 z x)
      * PretenseSum χ (2 * x + 2) :=
    mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg x) (by linarith))
      (Real.exp_pos _).le) (ert2_PS_nonneg χ _)
  rw [← Finset.sum_filter_add_sum_filter_not ((l2cWindow χ z x).filter (fun n =>
      n.Prime ∧ Odd n ∧ IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2) ∧
        ¬ (nPlus χ (n + 2)).Prime ∧ ¬ ERT2'JunkBlock z (nMinus χ (n + 2))))
      (fun n => nMinus χ (n + 2) ≤ ert2K z)]
  have hA := ert2_routeA_sum χ hsq hz100 hzx
  have hB := ert2_routeB_sum χ hsq hz100 hzx
  nlinarith [hA, hB, hY]

end Salt.HB
