/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.TypeII

/-!
# V2b-close — the closed-form Type II bilinear estimate

Pure real-analysis close-out of node `V2b` (`docs/blueprints/bv.md`).  Starting from the
landed reduction `typeII_disc_reduce` (`Salt/BV/TypeII.lean`), which bounds the
`(1/φf)`-weighted primitive-character `L¹` Type II discrepancy by a numeric geometric
double-sum of `blockBound`, this file assembles the four-regime geometric sum into the
closed form.
-/

namespace Salt.BV

open Finset Salt.LS ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius

/-! ## Section 1 — standalone real-analysis helpers -/

/-- Subadditivity of `√`. -/
lemma sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have hab : 0 ≤ Real.sqrt a * Real.sqrt b := by positivity
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, hab]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-- `√(2^j) = (√2)^j`. -/
lemma sqrt_two_pow (j : ℕ) : Real.sqrt ((2 : ℝ) ^ j) = Real.sqrt 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, pow_succ, Real.sqrt_mul (by positivity), ih]

/-- From `2^k ≤ n` (reals) deduce `k ≤ 2 log n`.  The `2` absorbs `1/log 2 < 2`. -/
lemma pow_le_two_log {k n : ℕ} (h : (2 : ℝ) ^ k ≤ (n : ℝ)) :
    (k : ℝ) ≤ 2 * Real.log n := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2' : (1 : ℝ) ≤ 2 * Real.log 2 := by nlinarith [Real.log_two_gt_d9]
  have hpk : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans hpk h
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hkey : (k : ℝ) * Real.log 2 ≤ Real.log n := by
    calc (k : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ k) := by rw [Real.log_pow]
      _ ≤ Real.log n := Real.log_le_log (by positivity) h
  nlinarith [hkey, mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr h2'), hlogn]

/-- `2 ^ clog 2 m ≤ 2 m` for `m ≥ 1`. -/
lemma two_pow_clog_le (m : ℕ) (hm : 1 ≤ m) : 2 ^ (Nat.clog 2 m) ≤ 2 * m := by
  rcases Nat.lt_or_ge m 2 with h | h
  · interval_cases m
    simp [Nat.clog_one_right]
  · have hlt : 2 ^ ((Nat.clog 2 m).pred) < m := Nat.pow_pred_clog_lt_self (by norm_num) h
    have hpos : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) h
    obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 m = k + 1 :=
      ⟨(Nat.clog 2 m).pred, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hk] at hlt ⊢
    simp only [Nat.pred_succ] at hlt
    rw [pow_succ]
    omega

/-- Exact geometric partial sum with base `1/2` over an `Icc`. -/
lemma sum_half_Icc (a b : ℕ) (hab : a ≤ b) :
    ∑ i ∈ Finset.Icc a b, (1 / 2 : ℝ) ^ i = 2 * (1 / 2) ^ a - 2 * (1 / 2) ^ (b + 1) := by
  induction b, hab using Nat.le_induction with
  | base => rw [Finset.Icc_self, Finset.sum_singleton]; ring
  | succ b hab ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

/-- `∑_{i∈Icc a b} (1/2)^i ≤ 2 (1/2)^a`. -/
lemma sum_half_Icc_le (a b : ℕ) : ∑ i ∈ Finset.Icc a b, (1 / 2 : ℝ) ^ i ≤ 2 * (1 / 2) ^ a := by
  rcases le_or_gt a b with h | h
  · rw [sum_half_Icc a b h]
    have : 0 ≤ 2 * (1 / 2 : ℝ) ^ (b + 1) := by positivity
    linarith
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; positivity

/-- `∑_{i∈Icc a b} 2^i ≤ 2 Q` when `2^b ≤ Q`. -/
lemma sum_two_pow_Icc_le (a b Q : ℕ) (hb : 2 ^ b ≤ Q) :
    ∑ i ∈ Finset.Icc a b, (2 : ℝ) ^ i ≤ 2 * (Q : ℝ) := by
  calc ∑ i ∈ Finset.Icc a b, (2 : ℝ) ^ i
      ≤ ∑ i ∈ Finset.range (b + 1), (2 : ℝ) ^ i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi; rw [Finset.mem_Icc] at hi; rw [Finset.mem_range]; omega
        · intro i _ _; positivity
    _ = (2 : ℝ) ^ (b + 1) - 1 := by rw [geom_sum_eq (by norm_num)]; norm_num
    _ ≤ 2 * (Q : ℝ) := by
        have hbQ : (2 : ℝ) ^ b ≤ (Q : ℝ) := by exact_mod_cast hb
        have : (2 : ℝ) ^ (b + 1) = 2 * (2 : ℝ) ^ b := by rw [pow_succ]; ring
        nlinarith [hbQ]

/-- √2 facts. -/
lemma sqrt_two_ge : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2:ℝ)]

lemma sqrt_two_gt_one : (1 : ℝ) < Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2:ℝ)]

/-- Decreasing dyadic geometric sum: `∑_{j<J} 1/√(U 2^j) ≤ 4/√U`. -/
lemma sum_inv_sqrt_dyadic (U J : ℕ) (hU : 1 ≤ U) :
    ∑ j ∈ Finset.range J, (Real.sqrt ((U : ℝ) * 2 ^ j))⁻¹ ≤ 4 / Real.sqrt U := by
  have hUpos : (0 : ℝ) < Real.sqrt U := Real.sqrt_pos.mpr (by exact_mod_cast hU)
  have hr0 : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
  have hr1 : (1 / Real.sqrt 2 : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]; exact sqrt_two_gt_one
  have hterm : ∀ j, (Real.sqrt ((U : ℝ) * 2 ^ j))⁻¹ = (Real.sqrt U)⁻¹ * (1 / Real.sqrt 2) ^ j := by
    intro j
    rw [Real.sqrt_mul (by positivity), sqrt_two_pow, mul_inv, one_div, inv_pow]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hgeom : ∑ j ∈ Finset.range J, (1 / Real.sqrt 2 : ℝ) ^ j ≤ (1 - 1 / Real.sqrt 2)⁻¹ := by
    have hsum := sum_le_hasSum (Finset.range J)
      (fun j _ => pow_nonneg hr0 j) (hasSum_geometric_of_lt_one hr0 hr1)
    simpa using hsum
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hinv4 : (1 - 1 / Real.sqrt 2 : ℝ)⁻¹ ≤ 4 := by
    have hd : (1 - 1 / Real.sqrt 2 : ℝ) = (Real.sqrt 2 - 1) / Real.sqrt 2 := by field_simp
    rw [hd, inv_div, div_le_iff₀ (by nlinarith [sqrt_two_gt_one] : (0:ℝ) < Real.sqrt 2 - 1)]
    nlinarith [sqrt_two_ge]
  calc (Real.sqrt U)⁻¹ * ∑ j ∈ Finset.range J, (1 / Real.sqrt 2 : ℝ) ^ j
      ≤ (Real.sqrt U)⁻¹ * (1 - 1 / Real.sqrt 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ (Real.sqrt U)⁻¹ * 4 := mul_le_mul_of_nonneg_left hinv4 (by positivity)
    _ = 4 / Real.sqrt U := by rw [mul_comm]; rw [div_eq_mul_inv]

/-- Increasing dyadic geometric sum: `∑_{j<J} √(U 2^j) ≤ 3 √(U 2^J)`. -/
lemma sum_sqrt_dyadic (U J : ℕ) :
    ∑ j ∈ Finset.range J, Real.sqrt ((U : ℝ) * 2 ^ j) ≤ 3 * Real.sqrt ((U : ℝ) * 2 ^ J) := by
  have hterm : ∀ j, Real.sqrt ((U : ℝ) * 2 ^ j) = Real.sqrt U * Real.sqrt 2 ^ j := by
    intro j; rw [Real.sqrt_mul (by positivity), sqrt_two_pow]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hgeom : ∑ j ∈ Finset.range J, Real.sqrt 2 ^ j ≤ 3 * Real.sqrt 2 ^ J := by
    rw [geom_sum_eq (by nlinarith [sqrt_two_gt_one] : Real.sqrt 2 ≠ 1)]
    rw [div_le_iff₀ (by nlinarith [sqrt_two_gt_one] : (0:ℝ) < Real.sqrt 2 - 1)]
    have hpow : (0 : ℝ) ≤ Real.sqrt 2 ^ J := by positivity
    nlinarith [mul_nonneg hpow (by nlinarith [sqrt_two_ge] : (0:ℝ) ≤ 3 * Real.sqrt 2 - 4)]
  calc Real.sqrt U * ∑ j ∈ Finset.range J, Real.sqrt 2 ^ j
      ≤ Real.sqrt U * (3 * Real.sqrt 2 ^ J) := mul_le_mul_of_nonneg_left hgeom (Real.sqrt_nonneg _)
    _ = 3 * (Real.sqrt U * Real.sqrt 2 ^ J) := by ring

/-- The diagonal geometric factor is `≤ 8/(log x)^C`, uniformly for `x ≥ 2`, `C > 0`. -/
lemma diag_bound (x : ℕ) (C : ℝ) (hx : 2 ≤ x) :
    2 * (1 / 2 : ℝ) ^ (Nat.log 2 ⌊(Real.log x) ^ C⌋₊) ≤ 8 / (Real.log x) ^ C := by
  have hxR : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hlogpos : 0 < Real.log x := Real.log_pos hxR
  have hrpos : (0 : ℝ) < (Real.log x) ^ C := Real.rpow_pos_of_pos hlogpos C
  set r := (Real.log x) ^ C with hr
  set n := ⌊r⌋₊ with hn
  set im := Nat.log 2 n with him
  have h2im_pos : (0 : ℝ) < (2 : ℝ) ^ im := by positivity
  have hlt : (n : ℝ) < 2 * (2 : ℝ) ^ im := by
    have h := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) n
    calc (n : ℝ) < ((2 ^ (im + 1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = 2 * (2 : ℝ) ^ im := by push_cast [pow_succ]; ring
  have hfloor : r - 1 < (n : ℝ) := by rw [hn]; exact Nat.sub_one_lt_floor r
  have hfin : 2 * r ≤ 8 * (2 : ℝ) ^ im := by
    rcases le_or_gt 2 r with hcase | hcase
    · nlinarith [hlt, hfloor, hcase, h2im_pos]
    · have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ im := one_le_pow₀ (by norm_num)
      nlinarith [h1, hcase, hrpos]
  have hgoal : 2 * (1 / 2 : ℝ) ^ im ≤ 8 / r := by
    have he : 2 * (1 / 2 : ℝ) ^ im = 2 / (2 : ℝ) ^ im := by rw [div_pow, one_pow, mul_one_div]
    rw [he, div_le_div_iff₀ h2im_pos hrpos]
    exact hfin
  simpa [hr] using hgoal

/-! ## Section 2 — the pointwise four-regime bound on `blockBound` -/

/-- Split `√((2F)² + 13(2D+1))·√((2F)² + 13(y/D+1))` into the four regime products and
simplify each: `blockBound x y D F` is bounded by the sum of the four regime terms
(for `1 ≤ D ≤ y`, `1 ≤ F`).  `RA` (`8L²√y·F`) is the diagonal top; `RB` (`4√26 L²y/√D`)
the `U`-boundary; `RC` (`4√39 L²√y√D`) the `V`-boundary; `RD` (`2√1014 L²y/F`) the diagonal. -/
lemma blockBound_le_regimes (x y D F : ℕ) (hD1 : 1 ≤ D) (hDy : D ≤ y) (hF1 : 1 ≤ F) :
    blockBound x y D F
      ≤ 8 * (1 + Real.log x) ^ 2 * Real.sqrt y * (F : ℝ)
        + 4 * Real.sqrt 26 * (1 + Real.log x) ^ 2 * (y : ℝ) / Real.sqrt D
        + 4 * Real.sqrt 39 * (1 + Real.log x) ^ 2 * Real.sqrt y * Real.sqrt D
        + 2 * Real.sqrt 1014 * (1 + Real.log x) ^ 2 * (y : ℝ) / (F : ℝ) := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD1
  have hD1R : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hFR : (0 : ℝ) < (F : ℝ) := by exact_mod_cast hF1
  have hFne : (F : ℝ) ≠ 0 := ne_of_gt hFR
  have hyDnat : 1 ≤ y / D := Nat.one_le_div_iff (by omega : 0 < D) |>.mpr hDy
  -- Abbreviations.
  set sD := Real.sqrt (D : ℝ) with hsDdef
  set syD := Real.sqrt ((y / D : ℕ) : ℝ) with hsyDdef
  set sy := Real.sqrt (y : ℝ) with hsydef
  set Lx := (1 + Real.log (x : ℝ)) with hLxdef
  -- Nonnegativity/square facts.
  have hsDpos : 0 < sD := Real.sqrt_pos.mpr hDR
  have hsD_eq : sD * sD = (D : ℝ) := Real.mul_self_sqrt hDR.le
  have hsyD_eq : syD * syD = ((y / D : ℕ) : ℝ) := Real.mul_self_sqrt (by positivity)
  have hDyDnat : (D : ℝ) * ((y / D : ℕ) : ℝ) ≤ (y : ℝ) := by
    have : D * (y / D) ≤ y := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self y D
    exact_mod_cast this
  have hDyD : sD * syD ≤ sy := by
    rw [hsDdef, hsyDdef, hsydef, ← Real.sqrt_mul hDR.le]
    exact Real.sqrt_le_sqrt hDyDnat
  -- `√A ≤ √39·√D`, `√B ≤ √26·√yD`.
  have hAle : Real.sqrt (13 * (((2 * D : ℕ) : ℝ) + 1)) ≤ Real.sqrt 39 * sD := by
    rw [hsDdef, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 39)]
    apply Real.sqrt_le_sqrt
    have : ((2 * D : ℕ) : ℝ) = 2 * (D : ℝ) := by push_cast; ring
    rw [this]; nlinarith [hD1R]
  have hBle : Real.sqrt (13 * (((y / D : ℕ) : ℝ) + 1)) ≤ Real.sqrt 26 * syD := by
    rw [hsyDdef, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 26)]
    apply Real.sqrt_le_sqrt
    have hyD1R : (1 : ℝ) ≤ ((y / D : ℕ) : ℝ) := by exact_mod_cast hyDnat
    nlinarith [hyD1R]
  -- Bound the two big square roots.
  set P := ((2 * F : ℕ) : ℝ) with hPdef
  have hP2 : P = 2 * (F : ℝ) := by rw [hPdef]; push_cast; ring
  have hPnn : 0 ≤ P := by rw [hPdef]; positivity
  set A := 13 * (((2 * D : ℕ) : ℝ) + 1) with hAdef
  set B := 13 * (((y / D : ℕ) : ℝ) + 1) with hBdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hM1 : Real.sqrt (P ^ 2 + A) ≤ P + Real.sqrt A := by
    calc Real.sqrt (P ^ 2 + A) ≤ Real.sqrt (P ^ 2) + Real.sqrt A :=
          sqrt_add_le _ _ (by positivity) hAnn
      _ = P + Real.sqrt A := by rw [Real.sqrt_sq hPnn]
  have hM2 : Real.sqrt (P ^ 2 + B) ≤ P + Real.sqrt B := by
    calc Real.sqrt (P ^ 2 + B) ≤ Real.sqrt (P ^ 2) + Real.sqrt B :=
          sqrt_add_le _ _ (by positivity) hBnn
      _ = P + Real.sqrt B := by rw [Real.sqrt_sq hPnn]
  -- The product-of-square-roots bound.
  have hprod : (1 / (F : ℝ)) * Real.sqrt (P ^ 2 + A) * Real.sqrt (P ^ 2 + B)
      ≤ (1 / (F : ℝ)) * (P + Real.sqrt A) * (P + Real.sqrt B) := by
    have h1F : (0 : ℝ) ≤ 1 / (F : ℝ) := by positivity
    calc (1 / (F : ℝ)) * Real.sqrt (P ^ 2 + A) * Real.sqrt (P ^ 2 + B)
        ≤ (1 / (F : ℝ)) * (P + Real.sqrt A) * Real.sqrt (P ^ 2 + B) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left hM1 h1F
      _ ≤ (1 / (F : ℝ)) * (P + Real.sqrt A) * (P + Real.sqrt B) := by
          apply mul_le_mul_of_nonneg_left hM2
          positivity
  -- The algebraic identity clearing `1/F`.
  have hexpand : (1 / (F : ℝ)) * (P + Real.sqrt A) * (P + Real.sqrt B)
      = 4 * (F : ℝ) + 2 * Real.sqrt A + 2 * Real.sqrt B
        + (1 / (F : ℝ)) * Real.sqrt A * Real.sqrt B := by
    rw [hP2]; field_simp; ring
  -- Four term facts.
  have hsDsyDy : (D : ℝ) * ((y / D : ℕ) : ℝ) ≤ (y : ℝ) := hDyDnat
  have tA : 8 * Lx ^ 2 * sD * syD * (F : ℝ) ≤ 8 * Lx ^ 2 * sy * (F : ℝ) := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 8 * Lx ^ 2 * (F : ℝ) by positivity)
      (sub_nonneg.mpr hDyD)]
  have hDsyD : (D : ℝ) * syD ≤ sy * sD := by
    have hrw : (D : ℝ) * syD = sD * (sD * syD) := by rw [← hsD_eq]; ring
    rw [hrw]
    calc sD * (sD * syD) ≤ sD * sy := mul_le_mul_of_nonneg_left hDyD hsDpos.le
      _ = sy * sD := by ring
  have tC : 4 * Lx ^ 2 * sD * syD * Real.sqrt A ≤ 4 * Real.sqrt 39 * Lx ^ 2 * sy * sD := by
    calc 4 * Lx ^ 2 * sD * syD * Real.sqrt A
        ≤ 4 * Lx ^ 2 * sD * syD * (Real.sqrt 39 * sD) := by
          apply mul_le_mul_of_nonneg_left hAle; positivity
      _ = 4 * Real.sqrt 39 * Lx ^ 2 * (D : ℝ) * syD := by rw [← hsD_eq]; ring
      _ ≤ 4 * Real.sqrt 39 * Lx ^ 2 * (sy * sD) := by
          nlinarith [mul_nonneg (show (0:ℝ) ≤ 4 * Real.sqrt 39 * Lx ^ 2 by positivity)
            (sub_nonneg.mpr hDsyD)]
      _ = 4 * Real.sqrt 39 * Lx ^ 2 * sy * sD := by ring
  have hsDyDdiv : sD * ((y / D : ℕ) : ℝ) ≤ (y : ℝ) / sD := by
    rw [le_div_iff₀ hsDpos]
    have : sD * ((y / D : ℕ) : ℝ) * sD = (D : ℝ) * ((y / D : ℕ) : ℝ) := by rw [← hsD_eq]; ring
    rw [this]; exact hDyDnat
  have tB : 4 * Lx ^ 2 * sD * syD * Real.sqrt B ≤ 4 * Real.sqrt 26 * Lx ^ 2 * (y : ℝ) / sD := by
    calc 4 * Lx ^ 2 * sD * syD * Real.sqrt B
        ≤ 4 * Lx ^ 2 * sD * syD * (Real.sqrt 26 * syD) := by
          apply mul_le_mul_of_nonneg_left hBle; positivity
      _ = 4 * Real.sqrt 26 * Lx ^ 2 * (sD * ((y / D : ℕ) : ℝ)) := by rw [← hsyD_eq]; ring
      _ ≤ 4 * Real.sqrt 26 * Lx ^ 2 * ((y : ℝ) / sD) := by
          apply mul_le_mul_of_nonneg_left hsDyDdiv; positivity
      _ = 4 * Real.sqrt 26 * Lx ^ 2 * (y : ℝ) / sD := by ring
  have hABle : Real.sqrt A * Real.sqrt B ≤ Real.sqrt 1014 * (sD * syD) := by
    have h1 : Real.sqrt 39 * Real.sqrt 26 = Real.sqrt 1014 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    calc Real.sqrt A * Real.sqrt B ≤ (Real.sqrt 39 * sD) * (Real.sqrt 26 * syD) := by
          apply mul_le_mul hAle hBle (Real.sqrt_nonneg _) (by positivity)
      _ = Real.sqrt 1014 * (sD * syD) := by rw [← h1]; ring
  have tD : 2 * Lx ^ 2 * sD * syD * (1 / (F : ℝ)) * Real.sqrt A * Real.sqrt B
      ≤ 2 * Real.sqrt 1014 * Lx ^ 2 * (y : ℝ) / (F : ℝ) := by
    calc 2 * Lx ^ 2 * sD * syD * (1 / (F : ℝ)) * Real.sqrt A * Real.sqrt B
        = 2 * Lx ^ 2 * sD * syD * (1 / (F : ℝ)) * (Real.sqrt A * Real.sqrt B) := by ring
      _ ≤ 2 * Lx ^ 2 * sD * syD * (1 / (F : ℝ)) * (Real.sqrt 1014 * (sD * syD)) := by
          apply mul_le_mul_of_nonneg_left hABle; positivity
      _ = 2 * Real.sqrt 1014 * Lx ^ 2 * (1 / (F : ℝ)) * ((D : ℝ) * ((y / D : ℕ) : ℝ)) := by
          rw [← hsD_eq, ← hsyD_eq]; ring
      _ ≤ 2 * Real.sqrt 1014 * Lx ^ 2 * (1 / (F : ℝ)) * (y : ℝ) := by
          apply mul_le_mul_of_nonneg_left hDyDnat; positivity
      _ = 2 * Real.sqrt 1014 * Lx ^ 2 * (y : ℝ) / (F : ℝ) := by ring
  -- Assemble.
  calc blockBound x y D F
      = 2 * Lx ^ 2 * sD * syD
          * ((1 / (F : ℝ)) * Real.sqrt (P ^ 2 + A) * Real.sqrt (P ^ 2 + B)) := by
        rw [blockBound]
        simp only [hsDdef, hsyDdef, hLxdef, hPdef, hAdef, hBdef]
        ring
    _ ≤ 2 * Lx ^ 2 * sD * syD
          * ((1 / (F : ℝ)) * (P + Real.sqrt A) * (P + Real.sqrt B)) := by
        apply mul_le_mul_of_nonneg_left hprod; positivity
    _ = 2 * Lx ^ 2 * sD * syD
          * (4 * (F : ℝ) + 2 * Real.sqrt A + 2 * Real.sqrt B
            + (1 / (F : ℝ)) * Real.sqrt A * Real.sqrt B) := by rw [hexpand]
    _ = 8 * Lx ^ 2 * sD * syD * (F : ℝ) + 4 * Lx ^ 2 * sD * syD * Real.sqrt B
          + 4 * Lx ^ 2 * sD * syD * Real.sqrt A
          + 2 * Lx ^ 2 * sD * syD * (1 / (F : ℝ)) * Real.sqrt A * Real.sqrt B := by ring
    _ ≤ 8 * Lx ^ 2 * sy * (F : ℝ) + 4 * Real.sqrt 26 * Lx ^ 2 * (y : ℝ) / sD
          + 4 * Real.sqrt 39 * Lx ^ 2 * sy * sD
          + 2 * Real.sqrt 1014 * Lx ^ 2 * (y : ℝ) / (F : ℝ) := by
        linarith [tA, tB, tC, tD]

/-! ## Section 3 — block vanishing, `j`-truncation, and the cutoff-aware reduction -/

/-- The dyadic block vanishes once `D·V ≥ y`: any nonzero summand needs `d ≥ D+1`,
`m ≥ V+1`, `d·m ≤ y`, forcing `y ≥ (D+1)(V+1) > D·V ≥ y`. -/
theorem typeIIBlock_eq_zero_of_prod {V y D : ℕ} (hV : 1 ≤ V) (h : y ≤ D * V) {q : ℕ}
    (χ : DirichletCharacter ℂ q) : typeIIBlock V y D χ = 0 := by
  rw [typeIIBlock]
  apply Finset.sum_eq_zero
  intro d hd
  rw [Finset.mem_Ioc] at hd
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro m hm
  rw [Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨_hm1, _hmy⟩, _hVdm, hdmy⟩ := hm
  rcases le_or_gt m V with hmV | hmV
  · rw [typeIIData_eq_zero_of_le hmV]; simp
  · exfalso
    have hd1 : D + 1 ≤ d := by omega
    have hm1' : V + 1 ≤ m := by omega
    have hprod : D * V < d * m := by
      calc D * V < (D + 1) * (V + 1) := by nlinarith
        _ ≤ d * m := Nat.mul_le_mul hd1 hm1'
    omega

/-- **`j`-truncated dyadic decomposition.**  For `1 ≤ U`, `1 ≤ V`, and any `J₁` with
`y ≤ U·2^{J₁}·V`, the blocks beyond `J₁` vanish, so `‖typeII‖ ≤ ∑_{j<J₁} ‖block_j‖`. -/
theorem typeII_le_sum_blocks_trunc (U V y : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) (J₁ : ℕ)
    (hcov : y ≤ U * 2 ^ J₁ * V) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖typeII U V y χ‖ ≤ ∑ j ∈ Finset.range J₁, ‖typeIIBlock V y (U * 2 ^ j) χ‖ := by
  have hJ₀ : y ≤ U * 2 ^ (J₁ + y) := by
    calc y ≤ 2 ^ y := (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ (J₁ + y) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ U * 2 ^ (J₁ + y) := Nat.le_mul_of_pos_left _ (by omega)
  refine le_trans (typeII_le_sum_blocks U V y (J₁ + y) hJ₀ χ) ?_
  apply le_of_eq
  symm
  apply Finset.sum_subset
  · intro a ha; simp only [Finset.mem_range] at *; omega
  · intro j _hj hj'
    rw [Finset.mem_range, not_lt] at hj'
    rw [typeIIBlock_eq_zero_of_prod hV ?_, norm_zero]
    calc y ≤ U * 2 ^ J₁ * V := hcov
      _ ≤ U * 2 ^ j * V := by
          gcongr
          omega

open Classical in
/-- **Cutoff-aware reduction.**  For a conductor set `S ⊆ Icc 1 Q` (`f ≥ 2`) whose members
all exceed `(log x)^C`, and any truncation `J₁` with `y ≤ U·2^{J₁}·V`, the `(1/φf)`-weighted
`L¹` Type II discrepancy is bounded by the double `blockBound`-sum over `j < J₁` and
`i ∈ [i_min, log₂(Q-1)]`, with `i_min = log₂⌊(log x)^C⌋`. -/
theorem typeII_disc_reduce_cutoff (U V x y Q : ℕ) (C : ℝ) (_hx : 2 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hyx : y ≤ x) (J₁ : ℕ) (hcov : y ≤ U * 2 ^ J₁ * V)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q) (hS2 : ∀ f ∈ S, 2 ≤ f)
    (hScut : ∀ f ∈ S, (Real.log x) ^ C < (f : ℝ)) :
    (∑ f ∈ S, (1 / (f.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
          ‖typeII U V y χ‖)
      ≤ ∑ j ∈ Finset.range J₁,
          ∑ i ∈ Finset.Icc (Nat.log 2 ⌊(Real.log x) ^ C⌋₊) (Nat.log 2 (Q - 1)),
            blockBound x y (U * 2 ^ j) (2 ^ i) := by
  classical
  set I := Nat.log 2 (Q - 1) with hIdef
  set imin := Nat.log 2 ⌊(Real.log x) ^ C⌋₊ with himindef
  have hlogxnn : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  have hrpownn : 0 ≤ (Real.log x) ^ C := Real.rpow_nonneg hlogxnn C
  calc ∑ f ∈ S, (1 / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ‖typeII U V y χ‖
      ≤ ∑ f ∈ S, (1 / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ∑ j ∈ Finset.range J₁, ‖typeIIBlock V y (U * 2 ^ j) χ‖ := by
        refine Finset.sum_le_sum (fun f _ => ?_)
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => ?_)) (by positivity)
        exact typeII_le_sum_blocks_trunc U V y hU hV J₁ hcov χ
    _ = ∑ j ∈ Finset.range J₁, ∑ f ∈ S, (1 / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ‖typeIIBlock V y (U * 2 ^ j) χ‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun f _ => ?_)
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range J₁, ∑ i ∈ Finset.Icc imin I,
          blockBound x y (U * 2 ^ j) (2 ^ i) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hmaps : ∀ f ∈ S, Nat.log 2 (f - 1) ∈ Finset.Icc imin I := by
          intro f hf
          have hfIcc := hS hf; rw [Finset.mem_Icc] at hfIcc
          have hf2 := hS2 f hf
          rw [Finset.mem_Icc, himindef, hIdef]
          refine ⟨Nat.log_mono_right ?_, Nat.log_mono_right ?_⟩
          · have hfloor : ⌊(Real.log x) ^ C⌋₊ < f := by
              rw [Nat.floor_lt hrpownn]; exact hScut f hf
            omega
          · omega
        rw [← Finset.sum_fiberwise_of_maps_to hmaps
          (fun f => (1 / (f.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
              ‖typeIIBlock V y (U * 2 ^ j) χ‖)]
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hUj : 1 ≤ U * 2 ^ j := by
          calc 1 = 1 * 1 := by ring
            _ ≤ U * 2 ^ j := Nat.mul_le_mul hU Nat.one_le_two_pow
        have hFi : 1 ≤ 2 ^ i := Nat.one_le_two_pow
        calc ∑ f ∈ S.filter (fun f => Nat.log 2 (f - 1) = i),
                (1 / (f.totient : ℝ)) *
                  ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
                    ‖typeIIBlock V y (U * 2 ^ j) χ‖
            ≤ ∑ f ∈ Finset.Icc (2 ^ i) (2 * 2 ^ i),
                (1 / (f.totient : ℝ)) *
                  ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
                    ‖typeIIBlock V y (U * 2 ^ j) χ‖ := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro f hf
                rw [Finset.mem_filter] at hf
                obtain ⟨hfS, hflog⟩ := hf
                have hf2' := hS2 f hfS
                rw [Finset.mem_Icc]
                refine ⟨?_, ?_⟩
                · have hle := Nat.pow_log_le_self 2 (show f - 1 ≠ 0 by omega)
                  rw [hflog] at hle; omega
                · have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (f - 1)
                  rw [hflog, pow_succ] at hlt; omega
              · intro f _ _
                exact mul_nonneg (by positivity)
                  (Finset.sum_nonneg (fun χ _ => norm_nonneg _))
          _ ≤ blockBound x y (U * 2 ^ j) (2 ^ i) :=
              typeII_block_le V x y (U * 2 ^ j) (2 ^ i) hyx hUj hFi

/-! ## Section 4 — the closed form -/

/-- Package a per-regime bound `c·T·p ≤ 2048·T'·p` from `c ≤ 2048`, `T ≤ T'`, and
nonnegativity. -/
private lemma final_le (c T Twin p : ℝ) (hc : c ≤ 2048) (hT : T ≤ Twin)
    (hTnn : 0 ≤ T) (hp : 0 ≤ p) : c * T * p ≤ 2048 * Twin * p :=
  mul_le_mul_of_nonneg_right (mul_le_mul hc hT hTnn (by norm_num)) hp

private lemma sqrtLe {a b : ℝ} (hb : 0 ≤ b) (h : a ≤ b ^ 2) : Real.sqrt a ≤ b := by
  rw [show b = Real.sqrt (b ^ 2) from (Real.sqrt_sq hb).symm]; exact Real.sqrt_le_sqrt h

/-- DS1 (the `√x·Q` top regime). -/
private lemma dsA_bound (x Q y J₁ imin I : ℕ) (hJ1 : (J₁ : ℝ) ≤ 4 * (1 + Real.log x))
    (hisum : ∑ i ∈ Finset.Icc imin I, (2 : ℝ) ^ i ≤ 2 * (Q : ℝ))
    (hsy : Real.sqrt y ≤ Real.sqrt x) (h1L : (0 : ℝ) < 1 + Real.log x) :
    ∑ _j ∈ Finset.range J₁, ∑ i ∈ Finset.Icc imin I,
        (8 * (1 + Real.log x) ^ 2 * Real.sqrt y * ((2 ^ i : ℕ) : ℝ))
      ≤ 2048 * (Real.sqrt x * Q) * (1 + Real.log x) ^ 3 := by
  have hinner : ∀ (j : ℕ), ∑ i ∈ Finset.Icc imin I,
        (8 * (1 + Real.log x) ^ 2 * Real.sqrt y * ((2 ^ i : ℕ) : ℝ))
      = 8 * (1 + Real.log x) ^ 2 * Real.sqrt y * ∑ i ∈ Finset.Icc imin I, (2 : ℝ) ^ i := by
    intro _; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by push_cast; ring)
  rw [Finset.sum_congr rfl (fun j _ => hinner j), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmid : 8 * (1 + Real.log x) ^ 2 * Real.sqrt y * (∑ i ∈ Finset.Icc imin I, (2 : ℝ) ^ i)
      ≤ 8 * (1 + Real.log x) ^ 2 * Real.sqrt x * (2 * (Q : ℝ)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hsy (by positivity)) hisum (by positivity) (by positivity)
  calc (J₁ : ℝ) * (8 * (1 + Real.log x) ^ 2 * Real.sqrt y * ∑ i ∈ Finset.Icc imin I, (2 : ℝ) ^ i)
      ≤ (4 * (1 + Real.log x)) * (8 * (1 + Real.log x) ^ 2 * Real.sqrt x * (2 * (Q : ℝ))) :=
        mul_le_mul hJ1 hmid (by positivity) (by linarith)
    _ = 64 * (Real.sqrt x * Q) * (1 + Real.log x) ^ 3 := by ring
    _ ≤ 2048 * (Real.sqrt x * Q) * (1 + Real.log x) ^ 3 :=
        final_le 64 _ _ _ (by norm_num) (le_refl _) (by positivity) (pow_nonneg h1L.le 3)

/-- DS2 (the `x/√U` Vaughan boundary). -/
private lemma dsB_bound (x U y J₁ imin I : ℕ) (hU : 1 ≤ U)
    (hIcard : ((Finset.Icc imin I).card : ℝ) ≤ 2 * (1 + Real.log x))
    (hyx' : (y : ℝ) ≤ (x : ℝ)) (h1L : (0 : ℝ) < 1 + Real.log x) :
    ∑ j ∈ Finset.range J₁, ∑ _i ∈ Finset.Icc imin I,
        (4 * Real.sqrt 26 * (1 + Real.log x) ^ 2 * (y : ℝ) / Real.sqrt ((U * 2 ^ j : ℕ) : ℝ))
      ≤ 2048 * ((x : ℝ) / Real.sqrt U) * (1 + Real.log x) ^ 3 := by
  have hs26 : Real.sqrt 26 ≤ 6 := sqrtLe (by norm_num) (by norm_num)
  have hinner : ∀ (j : ℕ), ∑ i ∈ Finset.Icc imin I,
        (4 * Real.sqrt 26 * (1 + Real.log x) ^ 2 * (y : ℝ) / Real.sqrt ((U * 2 ^ j : ℕ) : ℝ))
      = ((Finset.Icc imin I).card : ℝ)
        * (4 * Real.sqrt 26 * (1 + Real.log x) ^ 2 * (y : ℝ) / Real.sqrt ((U * 2 ^ j : ℕ) : ℝ)) :=
    fun _ => by rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => hinner j), ← Finset.mul_sum]
  have hpull : ∑ j ∈ Finset.range J₁,
        (4 * Real.sqrt 26 * (1 + Real.log x) ^ 2 * (y : ℝ) / Real.sqrt ((U * 2 ^ j : ℕ) : ℝ))
      = 4 * Real.sqrt 26 * (1 + Real.log x) ^ 2 * (y : ℝ)
        * ∑ j ∈ Finset.range J₁, (Real.sqrt ((U : ℝ) * 2 ^ j))⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show ((U * 2 ^ j : ℕ) : ℝ) = (U : ℝ) * 2 ^ j from by push_cast; ring, div_eq_mul_inv]
  rw [hpull]
  have hmid : 4 * Real.sqrt 26 * (1 + Real.log x) ^ 2 * (y : ℝ)
        * (∑ j ∈ Finset.range J₁, (Real.sqrt ((U : ℝ) * 2 ^ j))⁻¹)
      ≤ 4 * Real.sqrt 26 * (1 + Real.log x) ^ 2 * (x : ℝ) * (4 / Real.sqrt U) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hyx' (by positivity)) (sum_inv_sqrt_dyadic U J₁ hU)
      (by positivity) (by positivity)
  calc ((Finset.Icc imin I).card : ℝ) * (4 * Real.sqrt 26 * (1 + Real.log x) ^ 2 * (y : ℝ)
          * ∑ j ∈ Finset.range J₁, (Real.sqrt ((U : ℝ) * 2 ^ j))⁻¹)
      ≤ (2 * (1 + Real.log x))
          * (4 * Real.sqrt 26 * (1 + Real.log x) ^ 2 * (x : ℝ) * (4 / Real.sqrt U)) :=
        mul_le_mul hIcard hmid (by positivity) (by linarith)
    _ = 32 * Real.sqrt 26 * ((x : ℝ) / Real.sqrt U) * (1 + Real.log x) ^ 3 := by ring
    _ ≤ 2048 * ((x : ℝ) / Real.sqrt U) * (1 + Real.log x) ^ 3 :=
        final_le _ _ _ _ (by nlinarith [hs26]) (le_refl _) (by positivity) (pow_nonneg h1L.le 3)

/-- DS3 (the `x/√V` Vaughan boundary — the `V`-term from the `j`-truncation). -/
private lemma dsC_bound (x U V y J₁ imin I : ℕ) (hV : 1 ≤ V)
    (htight : (U : ℝ) * 2 ^ J₁ ≤ 2 * (y : ℝ) / (V : ℝ))
    (hIcard : ((Finset.Icc imin I).card : ℝ) ≤ 2 * (1 + Real.log x))
    (hyx' : (y : ℝ) ≤ (x : ℝ)) (h1L : (0 : ℝ) < 1 + Real.log x) :
    ∑ j ∈ Finset.range J₁, ∑ _i ∈ Finset.Icc imin I,
        (4 * Real.sqrt 39 * (1 + Real.log x) ^ 2 * Real.sqrt y * Real.sqrt ((U * 2 ^ j : ℕ) : ℝ))
      ≤ 2048 * ((x : ℝ) / Real.sqrt V) * (1 + Real.log x) ^ 3 := by
  have hsVpos : (0 : ℝ) < Real.sqrt V := Real.sqrt_pos.mpr (by exact_mod_cast hV)
  have hs39 : Real.sqrt 39 ≤ 7 := sqrtLe (by norm_num) (by norm_num)
  have hs2' : Real.sqrt 2 ≤ 2 := sqrtLe (by norm_num) (by norm_num)
  have hinner : ∀ (j : ℕ), ∑ i ∈ Finset.Icc imin I,
        (4 * Real.sqrt 39 * (1 + Real.log x) ^ 2 * Real.sqrt y * Real.sqrt ((U * 2 ^ j : ℕ) : ℝ))
      = ((Finset.Icc imin I).card : ℝ)
        * (4 * Real.sqrt 39 * (1 + Real.log x) ^ 2 * Real.sqrt y
          * Real.sqrt ((U * 2 ^ j : ℕ) : ℝ)) :=
    fun _ => by rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => hinner j), ← Finset.mul_sum]
  have hpull : ∑ j ∈ Finset.range J₁,
        (4 * Real.sqrt 39 * (1 + Real.log x) ^ 2 * Real.sqrt y * Real.sqrt ((U * 2 ^ j : ℕ) : ℝ))
      = 4 * Real.sqrt 39 * (1 + Real.log x) ^ 2 * Real.sqrt y
        * ∑ j ∈ Finset.range J₁, Real.sqrt ((U : ℝ) * 2 ^ j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show ((U * 2 ^ j : ℕ) : ℝ) = (U : ℝ) * 2 ^ j from by push_cast; ring]
  rw [hpull]
  have hUJ : Real.sqrt ((U : ℝ) * 2 ^ J₁) ≤ Real.sqrt 2 * Real.sqrt y / Real.sqrt V := by
    have h := Real.sqrt_le_sqrt htight
    rwa [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 * (y : ℝ)),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hgeom2 : ∑ j ∈ Finset.range J₁, Real.sqrt ((U : ℝ) * 2 ^ j)
      ≤ 3 * (Real.sqrt 2 * Real.sqrt y / Real.sqrt V) :=
    le_trans (sum_sqrt_dyadic U J₁) (mul_le_mul_of_nonneg_left hUJ (by norm_num))
  have hmid : 4 * Real.sqrt 39 * (1 + Real.log x) ^ 2 * Real.sqrt y
        * (∑ j ∈ Finset.range J₁, Real.sqrt ((U : ℝ) * 2 ^ j))
      ≤ 4 * Real.sqrt 39 * (1 + Real.log x) ^ 2 * Real.sqrt y
        * (3 * (Real.sqrt 2 * Real.sqrt y / Real.sqrt V)) :=
    mul_le_mul_of_nonneg_left hgeom2 (by positivity)
  have hT : (y : ℝ) / Real.sqrt V ≤ (x : ℝ) / Real.sqrt V := by gcongr
  calc ((Finset.Icc imin I).card : ℝ) * (4 * Real.sqrt 39 * (1 + Real.log x) ^ 2 * Real.sqrt y
          * ∑ j ∈ Finset.range J₁, Real.sqrt ((U : ℝ) * 2 ^ j))
      ≤ (2 * (1 + Real.log x)) * (4 * Real.sqrt 39 * (1 + Real.log x) ^ 2 * Real.sqrt y
          * (3 * (Real.sqrt 2 * Real.sqrt y / Real.sqrt V))) :=
        mul_le_mul hIcard hmid (by positivity) (by linarith)
    _ = 24 * Real.sqrt 39 * Real.sqrt 2 * (Real.sqrt y ^ 2 / Real.sqrt V)
          * (1 + Real.log x) ^ 3 := by ring
    _ = 24 * Real.sqrt 39 * Real.sqrt 2 * ((y : ℝ) / Real.sqrt V) * (1 + Real.log x) ^ 3 := by
        rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (y : ℝ))]
    _ ≤ 2048 * ((x : ℝ) / Real.sqrt V) * (1 + Real.log x) ^ 3 :=
        final_le _ _ _ _
          (by nlinarith [hs39, hs2', Real.sqrt_nonneg (39 : ℝ), Real.sqrt_nonneg (2 : ℝ)])
          hT (by positivity) (pow_nonneg h1L.le 3)

/-- DS4 (the diagonal `x/(log x)^C`, saved by the conductor cutoff). -/
private lemma dsD_bound (x y J₁ imin I : ℕ) (C : ℝ)
    (hJ1 : (J₁ : ℝ) ≤ 4 * (1 + Real.log x))
    (hdiag : ∑ i ∈ Finset.Icc imin I, (1 / 2 : ℝ) ^ i ≤ 8 / (Real.log x) ^ C)
    (hyx' : (y : ℝ) ≤ (x : ℝ)) (h1L : (0 : ℝ) < 1 + Real.log x)
    (hLCpos : (0 : ℝ) < (Real.log x) ^ C) :
    ∑ _j ∈ Finset.range J₁, ∑ i ∈ Finset.Icc imin I,
        (2 * Real.sqrt 1014 * (1 + Real.log x) ^ 2 * (y : ℝ) / ((2 ^ i : ℕ) : ℝ))
      ≤ 2048 * ((x : ℝ) / (Real.log x) ^ C) * (1 + Real.log x) ^ 3 := by
  have hs1014 : Real.sqrt 1014 ≤ 32 := sqrtLe (by norm_num) (by norm_num)
  have hinner : ∀ (j : ℕ), ∑ i ∈ Finset.Icc imin I,
        (2 * Real.sqrt 1014 * (1 + Real.log x) ^ 2 * (y : ℝ) / ((2 ^ i : ℕ) : ℝ))
      = 2 * Real.sqrt 1014 * (1 + Real.log x) ^ 2 * (y : ℝ)
        * ∑ i ∈ Finset.Icc imin I, (1 / 2 : ℝ) ^ i := by
    intro _; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [show ((2 ^ i : ℕ) : ℝ) = (2 : ℝ) ^ i from by push_cast; ring, div_pow, one_pow,
        mul_one_div]
  rw [Finset.sum_congr rfl (fun j _ => hinner j), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmid : 2 * Real.sqrt 1014 * (1 + Real.log x) ^ 2 * (y : ℝ)
        * (∑ i ∈ Finset.Icc imin I, (1 / 2 : ℝ) ^ i)
      ≤ 2 * Real.sqrt 1014 * (1 + Real.log x) ^ 2 * (x : ℝ) * (8 / (Real.log x) ^ C) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hyx' (by positivity)) hdiag (by positivity)
      (by positivity)
  calc (J₁ : ℝ) * (2 * Real.sqrt 1014 * (1 + Real.log x) ^ 2 * (y : ℝ)
          * ∑ i ∈ Finset.Icc imin I, (1 / 2 : ℝ) ^ i)
      ≤ (4 * (1 + Real.log x)) * (2 * Real.sqrt 1014 * (1 + Real.log x) ^ 2 * (x : ℝ)
          * (8 / (Real.log x) ^ C)) := mul_le_mul hJ1 hmid (by positivity) (by linarith)
    _ = 64 * Real.sqrt 1014 * ((x : ℝ) / (Real.log x) ^ C) * (1 + Real.log x) ^ 3 := by ring
    _ ≤ 2048 * ((x : ℝ) / (Real.log x) ^ C) * (1 + Real.log x) ^ 3 :=
        final_le _ _ _ _ (by nlinarith [hs1014]) (le_refl _)
          (div_nonneg (by positivity) hLCpos.le) (pow_nonneg h1L.le 3)

open Classical in
/-- **V2b-close.**  The four-regime geometric sum of `blockBound`, packaged as the closed
form: with `κ = 3` and `C₃ = 2048`, the cutoff `(log x)^C < f` Type II discrepancy is
`≤ C₃·(√x·Q + x/√U + x/√V + x/(log x)^C)·(1+log x)^3`.  The `x/√U`, `x/√V` terms are the
Vaughan boundary terms (the `V`-term via the `j`-truncation `typeII_le_sum_blocks_trunc`);
the `x/(log x)^C` diagonal is saved by the conductor cutoff. -/
theorem typeII_disc_le {x U V Q : ℕ} (hx : 2 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hQ : 2 ≤ Q) (hQx : Q ≤ x) {C : ℝ} (_hC : 0 < C) (y : ℕ) (hyx : y ≤ x) :
    (∑ f ∈ (Finset.Icc 1 Q).filter (fun (f : ℕ) => 2 ≤ f ∧ (Real.log x) ^ C < (f : ℝ)),
        (1 / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ‖typeII U V y χ‖)
      ≤ 2048 * (Real.sqrt x * Q + x / Real.sqrt U + x / Real.sqrt V + x / (Real.log x) ^ C)
          * (1 + Real.log x) ^ 3 := by
  classical
  -- Scalar facts.
  have hxR : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hLpos : 0 < Real.log x := Real.log_pos hxR
  have h1L : (0 : ℝ) < 1 + Real.log x := by linarith
  have hLCpos : (0 : ℝ) < (Real.log x) ^ C := Real.rpow_pos_of_pos hLpos C
  have hsUpos : (0 : ℝ) < Real.sqrt U := Real.sqrt_pos.mpr (by exact_mod_cast hU)
  have hsVpos : (0 : ℝ) < Real.sqrt V := Real.sqrt_pos.mpr (by exact_mod_cast hV)
  have hTnn : (0 : ℝ) ≤ 2048 * (Real.sqrt x * Q + x / Real.sqrt U + x / Real.sqrt V
      + x / (Real.log x) ^ C) * (1 + Real.log x) ^ 3 := by
    apply mul_nonneg (mul_nonneg (by norm_num) ?_) (pow_nonneg h1L.le 3)
    have : (0:ℝ) ≤ (x:ℝ) / (Real.log x) ^ C := by positivity
    have h2 : (0:ℝ) ≤ (x:ℝ) / Real.sqrt U := by positivity
    have h3 : (0:ℝ) ≤ (x:ℝ) / Real.sqrt V := by positivity
    have h4 : (0:ℝ) ≤ Real.sqrt x * Q := by positivity
    linarith
  -- The set `S` and the reduce.
  set S := (Finset.Icc 1 Q).filter (fun (f : ℕ) => 2 ≤ f ∧ (Real.log x) ^ C < (f : ℝ)) with hSdef
  have hSsub : S ⊆ Finset.Icc 1 Q := Finset.filter_subset _ _
  have hS2 : ∀ f ∈ S, 2 ≤ f := by intro f hf; rw [hSdef, Finset.mem_filter] at hf; exact hf.2.1
  have hScut : ∀ f ∈ S, (Real.log x) ^ C < (f : ℝ) := by
    intro f hf; rw [hSdef, Finset.mem_filter] at hf; exact hf.2.2
  have hcov : y ≤ U * 2 ^ (Nat.clog 2 (y / (U * V) + 1)) * V := by
    have hle : y / (U * V) + 1 ≤ 2 ^ (Nat.clog 2 (y / (U * V) + 1)) :=
      Nat.le_pow_clog (by norm_num) _
    have hnpos : 0 < U * V := by positivity
    have hkey : y < U * V * (y / (U * V) + 1) := by
      have h1 := Nat.div_add_mod y (U * V)
      have h2 := Nat.mod_lt y hnpos
      rw [Nat.mul_add, Nat.mul_one]
      omega
    calc y ≤ U * V * (y / (U * V) + 1) := hkey.le
      _ ≤ U * V * 2 ^ (Nat.clog 2 (y / (U * V) + 1)) := Nat.mul_le_mul (le_refl _) hle
      _ = U * 2 ^ (Nat.clog 2 (y / (U * V) + 1)) * V := by ring
  have hred := typeII_disc_reduce_cutoff U V x y Q C hx hU hV hyx
    (Nat.clog 2 (y / (U * V) + 1)) hcov S hSsub hS2 hScut
  refine le_trans hred ?_
  set J₁ := Nat.clog 2 (y / (U * V) + 1) with hJ₁def
  set imin := Nat.log 2 ⌊(Real.log x) ^ C⌋₊ with himindef
  set I := Nat.log 2 (Q - 1) with hIdef
  -- Scalar bounds for the geometric sums.
  have hJ1bd : (J₁ : ℝ) ≤ 4 * (1 + Real.log x) := by
    have h2J1 : 2 ^ J₁ ≤ 4 * x := by
      have h := two_pow_clog_le (y / (U * V) + 1) (Nat.le_add_left 1 _)
      have hyn : y / (U * V) ≤ y := Nat.div_le_self y (U * V)
      rw [← hJ₁def] at h
      omega
    have h1 : (2 : ℝ) ^ J₁ ≤ ((4 * x : ℕ) : ℝ) := by exact_mod_cast h2J1
    have h2 := pow_le_two_log h1
    have hlog4x : Real.log ((4 * x : ℕ) : ℝ) ≤ 2 + Real.log x := by
      have he : ((4 * x : ℕ) : ℝ) = 4 * (x : ℝ) := by push_cast; ring
      rw [he, Real.log_mul (by norm_num) (by positivity)]
      have hlog4 : Real.log 4 ≤ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        nlinarith [Real.log_two_lt_d9]
      linarith
    nlinarith [h2, hlog4x, hLpos]
  have hIcard : ((Finset.Icc imin I).card : ℝ) ≤ 2 * (1 + Real.log x) := by
    have hIle : (I : ℝ) ≤ 2 * Real.log x := by
      have h2I : 2 ^ I ≤ Q - 1 := Nat.pow_log_le_self 2 (by omega)
      have h1 : (2 : ℝ) ^ I ≤ ((Q - 1 : ℕ) : ℝ) := by exact_mod_cast h2I
      have h2 := pow_le_two_log h1
      have h3 : Real.log ((Q - 1 : ℕ) : ℝ) ≤ Real.log x :=
        Real.log_le_log (by exact_mod_cast (show 0 < Q - 1 by omega))
          (by exact_mod_cast (by omega : Q - 1 ≤ x))
      linarith
    rw [Nat.card_Icc]
    have hc : ((I + 1 - imin : ℕ) : ℝ) ≤ (I : ℝ) + 1 := by
      have : I + 1 - imin ≤ I + 1 := by omega
      calc ((I + 1 - imin : ℕ) : ℝ) ≤ ((I + 1 : ℕ) : ℝ) := by exact_mod_cast this
        _ = (I : ℝ) + 1 := by push_cast; ring
    linarith [hIle]
  have hisum : ∑ i ∈ Finset.Icc imin I, (2 : ℝ) ^ i ≤ 2 * (Q : ℝ) :=
    sum_two_pow_Icc_le imin I Q (le_trans (Nat.pow_log_le_self 2 (by omega)) (by omega))
  have hdiag : ∑ i ∈ Finset.Icc imin I, (1 / 2 : ℝ) ^ i ≤ 8 / (Real.log x) ^ C := by
    refine le_trans (sum_half_Icc_le imin I) ?_
    have hd := diag_bound x C hx
    rw [← himindef] at hd
    exact hd
  -- Case J₁ = 0: the double sum is empty.
  rcases Nat.eq_zero_or_pos J₁ with hJ0 | hJpos
  · rw [hJ0]; simp only [Finset.range_zero, Finset.sum_empty]; exact hTnn
  -- Main case J₁ ≥ 1: the tightness fact and D-range fact.
  have hUV2J : U * V * 2 ^ J₁ ≤ 2 * y := by
    have hm2 : 1 < y / (U * V) + 1 := by
      rcases Nat.lt_or_ge (y / (U * V) + 1) 2 with h | h
      · exfalso
        have hz : Nat.clog 2 (y / (U * V) + 1) = 0 := Nat.clog_of_right_le_one (by omega) _
        rw [← hJ₁def] at hz; omega
      · omega
    obtain ⟨k, hk⟩ : ∃ k, J₁ = k + 1 := ⟨J₁ - 1, by omega⟩
    have hpk : 2 ^ k < y / (U * V) + 1 := by
      have hp := Nat.pow_pred_clog_lt_self (show 1 < 2 by norm_num) hm2
      rw [← hJ₁def, hk] at hp; simpa using hp
    have hle : 2 ^ k ≤ y / (U * V) := by omega
    have hnyn : U * V * (y / (U * V)) ≤ y := by
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self y (U * V)
    calc U * V * 2 ^ J₁ = 2 * (U * V * 2 ^ k) := by rw [hk, pow_succ]; ring
      _ ≤ 2 * (U * V * (y / (U * V))) :=
          Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (le_refl _) hle)
      _ ≤ 2 * y := by omega
  have htight : (U : ℝ) * 2 ^ J₁ ≤ 2 * (y : ℝ) / (V : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hV : (0 : ℝ) < V)]
    have : ((U * V * 2 ^ J₁ : ℕ) : ℝ) ≤ ((2 * y : ℕ) : ℝ) := by exact_mod_cast hUV2J
    push_cast at this ⊢; nlinarith [this]
  have hDley : ∀ j ∈ Finset.range J₁, U * 2 ^ j ≤ y := by
    intro j hj
    rw [Finset.mem_range, hJ₁def] at hj
    have h2j : 2 ^ j < y / (U * V) + 1 := Nat.pow_lt_of_lt_clog hj
    have hle : 2 ^ j ≤ y / (U * V) := by omega
    have hUUV : U ≤ U * V := Nat.le_mul_of_pos_right U (by omega)
    calc U * 2 ^ j ≤ U * (y / (U * V)) := Nat.mul_le_mul (le_refl _) hle
      _ ≤ U * V * (y / (U * V)) := Nat.mul_le_mul hUUV (le_refl _)
      _ ≤ y := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self y (U * V)
  -- Pointwise regime bound.
  have hstep : ∑ j ∈ Finset.range J₁, ∑ i ∈ Finset.Icc imin I,
        blockBound x y (U * 2 ^ j) (2 ^ i)
      ≤ ∑ j ∈ Finset.range J₁, ∑ i ∈ Finset.Icc imin I,
        (8 * (1 + Real.log x) ^ 2 * Real.sqrt y * ((2 ^ i : ℕ) : ℝ)
          + 4 * Real.sqrt 26 * (1 + Real.log x) ^ 2 * (y : ℝ) / Real.sqrt ((U * 2 ^ j : ℕ) : ℝ)
          + 4 * Real.sqrt 39 * (1 + Real.log x) ^ 2 * Real.sqrt y * Real.sqrt ((U * 2 ^ j : ℕ) : ℝ)
          + 2 * Real.sqrt 1014 * (1 + Real.log x) ^ 2 * (y : ℝ) / ((2 ^ i : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun i _ => ?_))
    have hUj : 1 ≤ U * 2 ^ j := by
      calc 1 = 1 * 1 := by ring
        _ ≤ U * 2 ^ j := Nat.mul_le_mul hU Nat.one_le_two_pow
    exact blockBound_le_regimes x y (U * 2 ^ j) (2 ^ i) hUj (hDley j hj) Nat.one_le_two_pow
  refine le_trans hstep ?_
  have hsy : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt (by exact_mod_cast hyx)
  have hyx' : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hyx
  have hb1 := dsA_bound x Q y J₁ imin I hJ1bd hisum hsy h1L
  have hb2 := dsB_bound x U y J₁ imin I hU hIcard hyx' h1L
  have hb3 := dsC_bound x U V y J₁ imin I hV htight hIcard hyx' h1L
  have hb4 := dsD_bound x y J₁ imin I C hJ1bd hdiag hyx' h1L hLCpos
  simp only [Finset.sum_add_distrib]
  have hcombine : 2048 * (Real.sqrt x * Q + x / Real.sqrt U + x / Real.sqrt V
        + x / (Real.log x) ^ C) * (1 + Real.log x) ^ 3
      = 2048 * (Real.sqrt x * Q) * (1 + Real.log x) ^ 3
        + 2048 * ((x : ℝ) / Real.sqrt U) * (1 + Real.log x) ^ 3
        + 2048 * ((x : ℝ) / Real.sqrt V) * (1 + Real.log x) ^ 3
        + 2048 * ((x : ℝ) / (Real.log x) ^ C) * (1 + Real.log x) ^ 3 := by ring
  rw [hcombine]
  linarith [hb1, hb2, hb3, hb4]

end Salt.BV
