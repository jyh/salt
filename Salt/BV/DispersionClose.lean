/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.Dispersion

/-!
# V3.1-close — discharging the large-`y` rpow budget

Design: `docs/blueprints/bv.md`, node `V3.1` (PB-floor `hlargeY`). This file
lands the deferred large-`y` branch arithmetic of `Salt.BV.psi_BV_of_siegelWalfisz`
(see `Salt/BV/Dispersion.lean`), then composes it into the **unconditional** ψ-form
dispersion keystone `psi_BV_of_siegelWalfisz'`.

`largeY_bound` proves EXACTLY the `hlargeY` hypothesis of `psi_BV_of_siegelWalfisz`
by applying the landed explicit split bound `dispSum_split_le` at the operating point
`Q = ⌊√x/(log x)^{A+6}⌋`, `U = V = ⌊x^{1/10}⌋`, conductor cutoff `Cc = A+6`,
Siegel–Walfisz saving `D = 2A+7`, and dominating each of the ≈9 RHS terms by either an
`x^{19/20}(1+log x)^4`-share (descent, head, Type I₁, Type I₂, the `x/√U`,`x/√V` Type II
tails) or an `x/(log x)^A`-share (`√x·Q`, `x/(log x)^{Cc}`, small-conductor). Constants:
`Mc = 26 + 16384√2`, `Kc = 262144 + 8K·2^{2A+7}`.

Siegel–Walfisz range alignment uses cutoff `C_sw = 2(A+6)` (invoking SW at
`A_sw = 4A+19`), so the only lower bound on `log x` required is `log x ≥ 4`, which
follows from `x ≥ 1024` — no unavailable `log x ≥ 2^{A+7}` threshold is needed.
-/

namespace Salt.BV

open Finset Salt.LS
open scoped BigOperators

/-! ## Pure real-analysis atoms -/

/-- `1 ≤ x^e` for `x ≥ 1`, `e ≥ 0` (via `1 = 1^e ≤ x^e`; avoids the ambiguous
`← Real.one_rpow` rewrite). -/
private lemma one_le_rpow' {x e : ℝ} (hx : 1 ≤ x) (he : 0 ≤ e) : 1 ≤ x ^ e := by
  calc (1 : ℝ) = (1 : ℝ) ^ e := (Real.one_rpow e).symm
    _ ≤ x ^ e := Real.rpow_le_rpow (by norm_num) hx he

/-- For `t ≥ 1`, `⌊t⌋₊ ≥ t/2` (floor loses at most a factor of two above `1`). -/
private lemma floor_ge_half {t : ℝ} (ht : 1 ≤ t) : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
  have h1 : (1 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast (Nat.one_le_floor_iff t).mpr ht
  have h2 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  linarith

/-- SW range alignment atom: for `L ≥ 4` and `0 ≤ m`, `L^m ≤ (L/2)^{2m}`. The extra
power absorbs the `4^m` mismatch since `L^2/4 ≥ L`. -/
private lemma align_pow {L m : ℝ} (hL4 : 4 ≤ L) (hm : 0 ≤ m) : L ^ m ≤ (L / 2) ^ (2 * m) := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hbase : L ≤ (L / 2) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith [hL4, hLpos]
  calc L ^ m ≤ ((L / 2) ^ (2 : ℝ)) ^ m := Real.rpow_le_rpow hLpos.le hbase hm
    _ = (L / 2) ^ (2 * m) := (Real.rpow_mul (by linarith : (0 : ℝ) ≤ L / 2) 2 m).symm

/-- `∑_{f∈[1,Q]} √f ≤ Q·√Q` (each term `≤ √Q`, and there are `Q` of them). -/
private lemma Sf_le_QsqrtQ (Q : ℕ) :
    (∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ)) ≤ (Q : ℝ) * Real.sqrt Q := by
  have h := Finset.sum_le_card_nsmul (Finset.Icc 1 Q) (fun f => Real.sqrt (f : ℝ))
    (Real.sqrt Q) (fun f hf => by
      rw [Finset.mem_Icc] at hf
      exact Real.sqrt_le_sqrt (by exact_mod_cast hf.2))
  rwa [nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] at h

/-- `Q·√Q ≤ x^{3/4}` given `Q ≤ x^{1/2}`. -/
private lemma QsqrtQ_le {x Q : ℝ} (hx : 1 ≤ x) (hQ0 : 0 ≤ Q) (hQ : Q ≤ x ^ (1 / 2 : ℝ)) :
    Q * Real.sqrt Q ≤ x ^ (3 / 4 : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsqQ : Real.sqrt Q ≤ x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc Q ^ (1 / 2 : ℝ) ≤ (x ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hQ0 hQ (by norm_num)
      _ = x ^ (1 / 4 : ℝ) := by rw [← Real.rpow_mul hx0.le]; norm_num
  calc Q * Real.sqrt Q ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) :=
        mul_le_mul hQ hsqQ (Real.sqrt_nonneg _) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num

/-- `x/√U ≤ √2·x^{19/20}` given `U ≥ x^{1/10}/2`. -/
private lemma invSqrt_le {x U : ℝ} (hx : 0 < x) (hU : x ^ (1 / 10 : ℝ) / 2 ≤ U) :
    x / Real.sqrt U ≤ Real.sqrt 2 * x ^ (19 / 20 : ℝ) := by
  have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hx10 : (0 : ℝ) < x ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hx _
  have hsqU : x ^ (1 / 20 : ℝ) / Real.sqrt 2 ≤ Real.sqrt U := by
    have h1 : Real.sqrt (x ^ (1 / 10 : ℝ) / 2) ≤ Real.sqrt U := Real.sqrt_le_sqrt hU
    have h2 : Real.sqrt (x ^ (1 / 10 : ℝ) / 2) = x ^ (1 / 20 : ℝ) / Real.sqrt 2 := by
      rw [Real.sqrt_div hx10.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]; norm_num
    linarith [h1, h2.ge, h2.le]
  have hsqUpos : (0 : ℝ) < Real.sqrt U := lt_of_lt_of_le (by positivity) hsqU
  have hlow : Real.sqrt 2 * x ^ (19 / 20 : ℝ) * (x ^ (1 / 20 : ℝ) / Real.sqrt 2)
      = x ^ (19 / 20 : ℝ) * x ^ (1 / 20 : ℝ) := by field_simp [h2pos.ne']
  have hlow2 : x ^ (19 / 20 : ℝ) * x ^ (1 / 20 : ℝ) = x := by rw [← Real.rpow_add hx]; norm_num
  rw [div_le_iff₀ hsqUpos]
  calc x = Real.sqrt 2 * x ^ (19 / 20 : ℝ) * (x ^ (1 / 20 : ℝ) / Real.sqrt 2) := by rw [hlow, hlow2]
    _ ≤ Real.sqrt 2 * x ^ (19 / 20 : ℝ) * Real.sqrt U :=
        mul_le_mul_of_nonneg_left hsqU (by positivity)

/-- Type II diagonal tail: `(x/L^{A+6})·(1+L)^4 ≤ 16·(x/L^A)` (the `(1+L)^4` polylog is
eaten by the two spare log powers). -/
private lemma IItail_le {x L A : ℝ} (hx : 0 ≤ x) (hL : 1 ≤ L) :
    (x / L ^ (A + 6)) * (1 + L) ^ 4 ≤ 16 * (x / L ^ A) := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hLsplit : L ^ (A + 6) = L ^ A * L ^ 6 := by
    rw [show (L : ℝ) ^ 6 = L ^ (6 : ℝ) by rw [← Real.rpow_natCast L 6]; norm_num,
      ← Real.rpow_add hLpos]
  have h16 : (1 + L) ^ 4 / L ^ 6 ≤ 16 := by
    rw [div_le_iff₀ (by positivity)]
    calc (1 + L) ^ 4 ≤ 16 * L ^ 4 := by
          nlinarith [pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + L by positivity)
            (show 1 + L ≤ 2 * L by linarith) 4]
      _ ≤ 16 * L ^ 6 := by nlinarith [pow_le_pow_right₀ hL (show 4 ≤ 6 by norm_num)]
  rw [hLsplit, show (x / (L ^ A * L ^ 6)) * (1 + L) ^ 4 = (x / L ^ A) * ((1 + L) ^ 4 / L ^ 6) by
    field_simp]
  calc (x / L ^ A) * ((1 + L) ^ 4 / L ^ 6) ≤ (x / L ^ A) * 16 :=
        mul_le_mul_of_nonneg_left h16 (div_nonneg hx (Real.rpow_nonneg hLpos.le A))
    _ = 16 * (x / L ^ A) := by ring

/-- Small-conductor term budget: `4(1+L)·L^{A+6}·(K·y/(log y)^{2A+7}) ≤ 8K·2^{2A+7}·(x/L^A)`,
using only `log y ≥ L/2` (no SW alignment threshold). -/
private lemma small_term_le {x y L A K : ℝ} (hx : 0 ≤ x) (hyx : y ≤ x) (hy : 0 ≤ y)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hL4 : 4 ≤ L) (hly : L / 2 ≤ Real.log y) :
    4 * (1 + L) * (L ^ (A + 6) * (K * y / (Real.log y) ^ (2 * A + 7)))
      ≤ 8 * K * (2 : ℝ) ^ (2 * A + 7) * (x / L ^ A) := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL2pos : (0 : ℝ) < L / 2 := by linarith
  have hlogypos : (0 : ℝ) < Real.log y := by linarith
  have he0 : (0 : ℝ) ≤ 2 * A + 7 := by linarith
  have h1 : (L / 2) ^ (2 * A + 7) ≤ (Real.log y) ^ (2 * A + 7) :=
    Real.rpow_le_rpow hL2pos.le hly he0
  have hLh_pos : (0 : ℝ) < (L / 2) ^ (2 * A + 7) := Real.rpow_pos_of_pos hL2pos _
  have hLA6pos : (0 : ℝ) < L ^ (A + 6) := Real.rpow_pos_of_pos hLpos _
  have h2 : K * y / (Real.log y) ^ (2 * A + 7)
      ≤ (2 : ℝ) ^ (2 * A + 7) * (K * y) / L ^ (2 * A + 7) := by
    have hstep : K * y / (Real.log y) ^ (2 * A + 7) ≤ K * y / (L / 2) ^ (2 * A + 7) :=
      div_le_div_of_nonneg_left (mul_nonneg hK hy) hLh_pos h1
    rw [Real.div_rpow hLpos.le (by norm_num), div_div_eq_mul_div] at hstep
    calc K * y / (Real.log y) ^ (2 * A + 7)
        ≤ K * y * (2 : ℝ) ^ (2 * A + 7) / L ^ (2 * A + 7) := hstep
      _ = (2 : ℝ) ^ (2 * A + 7) * (K * y) / L ^ (2 * A + 7) := by ring
  have hLquot : L ^ (A + 6) / L ^ (2 * A + 7) = 1 / L ^ (A + 1) := by
    rw [← Real.rpow_sub hLpos, show (A + 6) - (2 * A + 7) = -(A + 1) by ring,
      Real.rpow_neg hLpos.le, one_div]
  calc 4 * (1 + L) * (L ^ (A + 6) * (K * y / (Real.log y) ^ (2 * A + 7)))
      ≤ 4 * (1 + L) * (L ^ (A + 6) * ((2 : ℝ) ^ (2 * A + 7) * (K * y) / L ^ (2 * A + 7))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hLA6pos.le) (by positivity)
    _ = (2 : ℝ) ^ (2 * A + 7) * K * y * (4 * (1 + L)) * (L ^ (A + 6) / L ^ (2 * A + 7)) := by ring
    _ = (2 : ℝ) ^ (2 * A + 7) * K * y * (4 * (1 + L)) * (1 / L ^ (A + 1)) := by rw [hLquot]
    _ = (2 : ℝ) ^ (2 * A + 7) * K * y * (4 * (1 + L) / L ^ (A + 1)) := by ring
    _ ≤ (2 : ℝ) ^ (2 * A + 7) * K * x * (8 / L ^ A) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hyx (by positivity)
        · rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hLpos _) (Real.rpow_pos_of_pos hLpos _),
            show L ^ (A + 1) = L ^ A * L by rw [Real.rpow_add hLpos, Real.rpow_one]]
          nlinarith [mul_nonneg (show (0 : ℝ) ≤ 4 * L - 4 by linarith)
            (Real.rpow_pos_of_pos hLpos A).le]
        · exact div_nonneg (by linarith) (Real.rpow_nonneg hLpos.le _)
        · positivity
    _ = 8 * K * (2 : ℝ) ^ (2 * A + 7) * (x / L ^ A) := by ring

/-! ## The large-`y` branch bound (the `hlargeY` PB-floor) -/

set_option maxHeartbeats 1000000 in
-- Raised limit: this single theorem assembles the ~9-term explicit `dispSum_split_le`
-- bound plus its Siegel–Walfisz discharge in one proof; the many `rpow`/`Real.log`
-- subterms make the default budget insufficient for the closing reassociation.
open Filter Topology in
/-- **The deferred large-`y` term arithmetic.** Proves EXACTLY the `hlargeY` hypothesis of
`psi_BV_of_siegelWalfisz`: at the operating point `B = A+6`, `U = V = ⌊x^{1/10}⌋`, the
explicit split bound `dispSum_split_le` is dominated by `Mc·x^{19/20}(1+log x)^4 +
Kc·x/(log x)^A` with `Mc = 26 + 16384√2` and `Kc = 262144 + 8K·2^{2A+7}` (`K` the
Siegel–Walfisz constant at saving `4A+19`). -/
theorem largeY_bound (hSW : SiegelWalfisz) :
    ∀ A : ℝ, 0 < A → ∃ Mc Kc : ℝ, 0 ≤ Mc ∧ 0 ≤ Kc ∧
      ∀ x y : ℕ, 1024 ≤ x → 1 ≤ Real.log x →
        2 ≤ ⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊ →
        ⌊Real.sqrt x⌋₊ < y → y ≤ x → Real.log x / 2 ≤ Real.log y →
        ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊, dispDisc y q
          ≤ Mc * (x : ℝ) ^ (19 / 20 : ℝ) * (1 + Real.log x) ^ (4 : ℝ)
            + Kc * (x : ℝ) / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨K, hK0, hKb⟩ := psiChi_le_of_siegelWalfisz_absorbed hSW
    (A := 2 * A + 7 + 2 * (A + 6)) (C := 2 * (A + 6)) (by linarith) (by linarith)
  refine ⟨26 + 16384 * Real.sqrt 2, 262144 + 8 * K * (2 : ℝ) ^ (2 * A + 7),
    by positivity,
    add_nonneg (by norm_num) (by
      exact mul_nonneg (mul_nonneg (by norm_num) hK0) (Real.rpow_nonneg (by norm_num) _)), ?_⟩
  intro x y hx1024 hLx1 hQ2 hyfl hyx hly
  set L := Real.log (x : ℝ) with hLdef
  -- convert the goal's `(1+L)^(4:ℝ)` to npow
  rw [show (1 + L) ^ (4 : ℝ) = (1 + L) ^ 4 by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
  set Q := ⌊Real.sqrt (x : ℝ) / L ^ (A + 6)⌋₊ with hQdef
  set U := ⌊(x : ℝ) ^ (1 / 10 : ℝ)⌋₊ with hUdef
  -- make the floor terms opaque so tactics don't repeatedly whnf them
  clear_value Q U
  -- basic reals
  have hxR : (1024 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1024
  have hx2 : 2 ≤ x := by omega
  have hxr1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hxr0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := hLx1
  have hL0 : (0 : ℝ) ≤ 1 + L := by linarith
  have hL0' : (1 : ℝ) ≤ 1 + L := by linarith
  have hpow13 : (1 + L) ≤ (1 + L) ^ 3 := by
    calc (1 + L) = (1 + L) ^ 1 := (pow_one _).symm
      _ ≤ (1 + L) ^ 3 := pow_le_pow_right₀ hL0' (by norm_num)
  have hL4 : (4 : ℝ) ≤ L := by
    have h1024 : Real.log (1024 : ℝ) ≤ L := by rw [hLdef]; exact Real.log_le_log (by norm_num) hxR
    have h2 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
      rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    have h3 := Real.log_two_gt_d9
    linarith
  have hsx0 : (0 : ℝ) ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
  have hsxsx : Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) = (x : ℝ) := Real.mul_self_sqrt hxr0.le
  have hsx_eq : Real.sqrt (x : ℝ) = (x : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hLA6pos : (0 : ℝ) < L ^ (A + 6) := Real.rpow_pos_of_pos hLpos _
  have hLA6_1 : (1 : ℝ) ≤ L ^ (A + 6) := one_le_rpow' hL1 (by linarith)
  -- Q atoms
  have hQr_nn : (0 : ℝ) ≤ (Q : ℝ) := by positivity
  have hQr_le_frac : (Q : ℝ) ≤ Real.sqrt (x : ℝ) / L ^ (A + 6) := by
    rw [hQdef]; exact Nat.floor_le (by positivity)
  have hfrac_le_sqrt : Real.sqrt (x : ℝ) / L ^ (A + 6) ≤ Real.sqrt (x : ℝ) := by
    rw [div_le_iff₀ hLA6pos]; exact le_mul_of_one_le_right hsx0 hLA6_1
  have hQr_le_sqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ) := hQr_le_frac.trans hfrac_le_sqrt
  have hQr_le_x12 : (Q : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := by rw [← hsx_eq]; exact hQr_le_sqrt
  have hsxQ : Real.sqrt (x : ℝ) * (Q : ℝ) ≤ (x : ℝ) / L ^ (A + 6) := by
    calc Real.sqrt (x : ℝ) * (Q : ℝ) ≤ Real.sqrt (x : ℝ) * (Real.sqrt (x : ℝ) / L ^ (A + 6)) :=
          mul_le_mul_of_nonneg_left hQr_le_frac hsx0
      _ = (x : ℝ) / L ^ (A + 6) := by rw [← mul_div_assoc, hsxsx]
  have hsx_le_x : Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
    rw [hsx_eq]
    calc (x : ℝ) ^ (1 / 2 : ℝ) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hxr1 (by norm_num)
      _ = (x : ℝ) := Real.rpow_one _
  -- U atoms
  have hx10_1 : (1 : ℝ) ≤ (x : ℝ) ^ (1 / 10 : ℝ) := one_le_rpow' hxr1 (by norm_num)
  have hUr_le : (U : ℝ) ≤ (x : ℝ) ^ (1 / 10 : ℝ) := by
    rw [hUdef]; exact Nat.floor_le (by positivity)
  have hUr_ge : (x : ℝ) ^ (1 / 10 : ℝ) / 2 ≤ (U : ℝ) := by rw [hUdef]; exact floor_ge_half hx10_1
  have hUr_nn : (0 : ℝ) ≤ (U : ℝ) := by positivity
  -- dispSum_split_le sub-hypotheses
  have hU1 : 1 ≤ U := by rw [hUdef]; exact (Nat.one_le_floor_iff _).mpr hx10_1
  have hQx : Q ≤ x := by
    rw [hQdef]
    calc ⌊Real.sqrt (x : ℝ) / L ^ (A + 6)⌋₊ ≤ ⌊(x : ℝ)⌋₊ :=
          Nat.floor_mono (hfrac_le_sqrt.trans hsx_le_x)
      _ = x := Nat.floor_natCast x
  have hx10_le_sqrt : (x : ℝ) ^ (1 / 10 : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [hsx_eq]; exact Real.rpow_le_rpow_of_exponent_le hxr1 (by norm_num)
  have hVy : U ≤ y := by
    have : U ≤ ⌊Real.sqrt (x : ℝ)⌋₊ := by rw [hUdef]; exact Nat.floor_mono hx10_le_sqrt
    omega
  have h1_le_flsqrt : 1 ≤ ⌊Real.sqrt (x : ℝ)⌋₊ := by
    apply (Nat.one_le_floor_iff _).mpr
    rw [hsx_eq]; exact one_le_rpow' hxr1 (by norm_num)
  have hy1 : 1 ≤ y := by omega
  have hy2 : 2 ≤ y := by omega
  have hCc : (0 : ℝ) < A + 6 := by linarith
  have hLCnn : (0 : ℝ) ≤ L ^ (A + 6) := hLA6pos.le
  have hlogy1 : (1 : ℝ) ≤ Real.log (y : ℝ) := by linarith
  have hlogy_nn : (0 : ℝ) ≤ Real.log (y : ℝ) := by linarith
  have hlogy_pos : (0 : ℝ) < Real.log (y : ℝ) := by linarith
  have hLApos : (0 : ℝ) < L ^ (2 * A + 7) := Real.rpow_pos_of_pos hLpos _
  have hval : (0 : ℝ) ≤ K * (y : ℝ) / (Real.log (y : ℝ)) ^ (2 * A + 7) :=
    div_nonneg (by positivity) (Real.rpow_nonneg hlogy_nn _)
  -- localized Siegel–Walfisz (SW cutoff C_sw = 2(A+6), no `log x ≥ 2^{A+7}` needed)
  have hSWloc : ∀ (f : ℕ), 2 ≤ f → ∀ χ : DirichletCharacter ℂ f, χ ≠ 1 →
      (f : ℝ) ≤ L ^ (A + 6) → ‖psiChi y χ‖ ≤ K * y / (Real.log (y : ℝ)) ^ (2 * A + 7) := by
    intro f hf2 χ hχ hfLC
    have halign : (f : ℝ) ≤ (Real.log (y : ℝ)) ^ (2 * (A + 6)) := by
      refine hfLC.trans ?_
      calc L ^ (A + 6) ≤ (L / 2) ^ (2 * (A + 6)) := align_pow hL4 (by linarith)
        _ ≤ (Real.log (y : ℝ)) ^ (2 * (A + 6)) := Real.rpow_le_rpow (by linarith) hly (by linarith)
    have hb := hKb f hf2 χ hχ y hy2 hlogy1 halign
    rwa [show (2 * A + 7 + 2 * (A + 6) - 2 * (A + 6) : ℝ) = 2 * A + 7 by ring] at hb
  -- the landed explicit split bound
  have hsplit := dispSum_split_le (x := x) (y := y) (Q := Q) (U := U) (V := U)
    (Cc := A + 6) (K := K) (D := 2 * A + 7)
    hx2 hU1 hU1 hQ2 hQx hCc hyx hVy hy1 hLCnn hval hSWloc
  rw [← hLdef] at hsplit
  -- `L` is opaque from here (its defeq to `Real.log x` is no longer needed); this stops
  -- tactics from repeatedly whnf-unfolding it across the assembly.
  clear_value L
  -- abbreviate the Type I √f-sum
  set Sf := ∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ) with hSfdef
  have hSf_nn : (0 : ℝ) ≤ Sf := Finset.sum_nonneg (fun f _ => Real.sqrt_nonneg _)
  have hSf_x34 : Sf ≤ (x : ℝ) ^ (3 / 4 : ℝ) :=
    (Sf_le_QsqrtQ Q).trans (QsqrtQ_le hxr1 hQr_nn hQr_le_x12)
  -- product atoms
  have hQU : (Q : ℝ) * (U : ℝ) ≤ (x : ℝ) ^ (3 / 5 : ℝ) := by
    calc (Q : ℝ) * (U : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) * (x : ℝ) ^ (1 / 10 : ℝ) :=
          mul_le_mul hQr_le_x12 hUr_le hUr_nn (Real.rpow_nonneg hxr0.le _)
      _ = (x : ℝ) ^ (3 / 5 : ℝ) := by rw [← Real.rpow_add hxr0]; norm_num
  have hUSf : (U : ℝ) * Sf ≤ (x : ℝ) ^ (17 / 20 : ℝ) := by
    calc (U : ℝ) * Sf ≤ (x : ℝ) ^ (1 / 10 : ℝ) * (x : ℝ) ^ (3 / 4 : ℝ) :=
          mul_le_mul hUr_le hSf_x34 hSf_nn (Real.rpow_nonneg hxr0.le _)
      _ = (x : ℝ) ^ (17 / 20 : ℝ) := by rw [← Real.rpow_add hxr0]; norm_num
  have hUU : (U : ℝ) * (U : ℝ) ≤ (x : ℝ) ^ (1 / 5 : ℝ) := by
    calc (U : ℝ) * (U : ℝ) ≤ (x : ℝ) ^ (1 / 10 : ℝ) * (x : ℝ) ^ (1 / 10 : ℝ) :=
          mul_le_mul hUr_le hUr_le hUr_nn (Real.rpow_nonneg hxr0.le _)
      _ = (x : ℝ) ^ (1 / 5 : ℝ) := by rw [← Real.rpow_add hxr0]; norm_num
  have hUUSf : (U : ℝ) * (U : ℝ) * Sf ≤ (x : ℝ) ^ (19 / 20 : ℝ) := by
    calc (U : ℝ) * (U : ℝ) * Sf ≤ (x : ℝ) ^ (1 / 5 : ℝ) * (x : ℝ) ^ (3 / 4 : ℝ) :=
          mul_le_mul hUU hSf_x34 hSf_nn (Real.rpow_nonneg hxr0.le _)
      _ = (x : ℝ) ^ (19 / 20 : ℝ) := by rw [← Real.rpow_add hxr0]; norm_num
  -- log Q ≤ L, logb 2 Q ≤ 2L, log y ≤ L
  have hlogQ_le_L : Real.log (Q : ℝ) ≤ L := by
    rw [hLdef]; exact Real.log_le_log (by exact_mod_cast (by omega : 0 < Q)) (by exact_mod_cast hQx)
  have hlogy_le_L : Real.log (y : ℝ) ≤ L := by
    rw [hLdef]; exact Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) (by exact_mod_cast hyx)
  have hQR2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2
  have hlogbQ_nn : (0 : ℝ) ≤ Real.logb 2 (Q : ℝ) := Real.logb_nonneg (by norm_num) (by linarith)
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogbQ : Real.logb 2 (Q : ℝ) ≤ 2 * L := by
    rw [Real.logb]
    calc Real.log (Q : ℝ) / Real.log 2 ≤ L / Real.log 2 := by gcongr
      _ ≤ 2 * L := by
          rw [div_le_iff₀ hlog2pos]
          calc L ≤ (2 * Real.log 2) * L :=
                le_mul_of_one_le_left (by linarith) (by linarith [Real.log_two_gt_d9])
            _ = 2 * L * Real.log 2 := by ring
  -- shares
  have hsh_desc : (Q : ℝ) * Real.logb 2 (Q : ℝ) * Real.log (y : ℝ)
      ≤ 2 * ((x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 4) := by
    have hstep1 : (Q : ℝ) * Real.logb 2 (Q : ℝ) * Real.log (y : ℝ)
        ≤ (x : ℝ) ^ (1 / 2 : ℝ) * (2 * (1 + L)) * (1 + L) := by
      apply mul_le_mul
      · exact mul_le_mul hQr_le_x12 (by linarith [hlogbQ]) hlogbQ_nn (Real.rpow_nonneg hxr0.le _)
      · linarith [hlogy_le_L]
      · exact hlogy_nn
      · exact mul_nonneg (Real.rpow_nonneg hxr0.le _) (by linarith)
    calc (Q : ℝ) * Real.logb 2 (Q : ℝ) * Real.log (y : ℝ)
        ≤ (x : ℝ) ^ (1 / 2 : ℝ) * (2 * (1 + L)) * (1 + L) := hstep1
      _ = 2 * ((x : ℝ) ^ (1 / 2 : ℝ) * (1 + L) ^ 2) := by ring
      _ ≤ 2 * ((x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 4) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul (Real.rpow_le_rpow_of_exponent_le hxr1 (by norm_num))
            (pow_le_pow_right₀ hL0' (by norm_num)) (pow_nonneg hL0 2) (Real.rpow_nonneg hxr0.le _)
  have hsh_head : 4 * (1 + L) * ((Q : ℝ) * (U : ℝ) * L)
      ≤ 4 * ((x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 4) := by
    have hbase : (Q : ℝ) * (U : ℝ) * L ≤ (x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 3 := by
      calc (Q : ℝ) * (U : ℝ) * L ≤ (x : ℝ) ^ (3 / 5 : ℝ) * (1 + L) :=
            mul_le_mul hQU (by linarith) (by linarith) (Real.rpow_nonneg hxr0.le _)
        _ ≤ (x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 3 := by
            exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hxr1 (by norm_num)) hpow13
              (by linarith) (Real.rpow_nonneg hxr0.le _)
    calc 4 * (1 + L) * ((Q : ℝ) * (U : ℝ) * L)
        ≤ 4 * (1 + L) * ((x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 3) :=
          mul_le_mul_of_nonneg_left hbase (by linarith)
      _ = 4 * ((x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 4) := by ring
  have hcore1 : (U : ℝ) * Sf * (1 + L) ^ 3 ≤ (x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 4 := by
    calc (U : ℝ) * Sf * (1 + L) ^ 3 ≤ (x : ℝ) ^ (17 / 20 : ℝ) * (1 + L) ^ 3 :=
          mul_le_mul_of_nonneg_right hUSf (pow_nonneg hL0 3)
      _ ≤ (x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 4 := by
          apply mul_le_mul (Real.rpow_le_rpow_of_exponent_le hxr1 (by norm_num))
            (pow_le_pow_right₀ hL0' (by norm_num)) (pow_nonneg hL0 3) (Real.rpow_nonneg hxr0.le _)
  have hsh_I1 : 4 * (1 + L) * (3 * (U : ℝ) * Sf * (1 + L) ^ 2)
      ≤ 12 * ((x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 4) := by
    rw [show 4 * (1 + L) * (3 * (U : ℝ) * Sf * (1 + L) ^ 2) = 12 * ((U : ℝ) * Sf * (1 + L) ^ 3) by
      ring]
    exact mul_le_mul_of_nonneg_left hcore1 (by norm_num)
  have hcore2 : (U : ℝ) * (U : ℝ) * Sf * (1 + L) ^ 3 ≤ (x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 4 := by
    calc (U : ℝ) * (U : ℝ) * Sf * (1 + L) ^ 3 ≤ (x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 3 :=
          mul_le_mul_of_nonneg_right hUUSf (pow_nonneg hL0 3)
      _ ≤ (x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL0' (by norm_num))
            (Real.rpow_nonneg hxr0.le _)
  have hsh_I2 : 4 * (1 + L) * (2 * ((U : ℝ) * (U : ℝ)) * Sf * (1 + L) ^ 2)
      ≤ 8 * ((x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 4) := by
    rw [show 4 * (1 + L) * (2 * ((U : ℝ) * (U : ℝ)) * Sf * (1 + L) ^ 2)
        = 8 * ((U : ℝ) * (U : ℝ) * Sf * (1 + L) ^ 3) by ring]
    exact mul_le_mul_of_nonneg_left hcore2 (by norm_num)
  have hxU : (x : ℝ) / Real.sqrt (U : ℝ) ≤ Real.sqrt 2 * (x : ℝ) ^ (19 / 20 : ℝ) :=
    invSqrt_le hxr0 hUr_ge
  have hIItail : ((x : ℝ) / L ^ (A + 6)) * (1 + L) ^ 4 ≤ 16 * ((x : ℝ) / L ^ A) :=
    IItail_le hxr0.le hL1
  have hbracket : Real.sqrt (x : ℝ) * (Q : ℝ) + (x : ℝ) / Real.sqrt (U : ℝ)
        + (x : ℝ) / Real.sqrt (U : ℝ) + (x : ℝ) / L ^ (A + 6)
      ≤ 2 * Real.sqrt 2 * (x : ℝ) ^ (19 / 20 : ℝ) + 2 * ((x : ℝ) / L ^ (A + 6)) := by
    linarith [hsxQ, hxU]
  have hsh_II : 4 * (1 + L) * (2048 * (Real.sqrt (x : ℝ) * (Q : ℝ) + (x : ℝ) / Real.sqrt (U : ℝ)
        + (x : ℝ) / Real.sqrt (U : ℝ) + (x : ℝ) / L ^ (A + 6)) * (1 + L) ^ 3)
      ≤ 16384 * Real.sqrt 2 * ((x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 4)
        + 262144 * ((x : ℝ) / L ^ A) := by
    rw [show 4 * (1 + L) * (2048 * (Real.sqrt (x : ℝ) * (Q : ℝ) + (x : ℝ) / Real.sqrt (U : ℝ)
          + (x : ℝ) / Real.sqrt (U : ℝ) + (x : ℝ) / L ^ (A + 6)) * (1 + L) ^ 3)
        = 8192 * ((Real.sqrt (x : ℝ) * (Q : ℝ) + (x : ℝ) / Real.sqrt (U : ℝ)
          + (x : ℝ) / Real.sqrt (U : ℝ) + (x : ℝ) / L ^ (A + 6)) * (1 + L) ^ 4) by ring]
    have hstep : (Real.sqrt (x : ℝ) * (Q : ℝ) + (x : ℝ) / Real.sqrt (U : ℝ)
          + (x : ℝ) / Real.sqrt (U : ℝ) + (x : ℝ) / L ^ (A + 6)) * (1 + L) ^ 4
        ≤ (2 * Real.sqrt 2 * (x : ℝ) ^ (19 / 20 : ℝ) + 2 * ((x : ℝ) / L ^ (A + 6))) * (1 + L) ^ 4 :=
      mul_le_mul_of_nonneg_right hbracket (pow_nonneg hL0 4)
    calc 8192 * ((Real.sqrt (x : ℝ) * (Q : ℝ) + (x : ℝ) / Real.sqrt (U : ℝ)
          + (x : ℝ) / Real.sqrt (U : ℝ) + (x : ℝ) / L ^ (A + 6)) * (1 + L) ^ 4)
        ≤ 8192 * ((2 * Real.sqrt 2 * (x : ℝ) ^ (19 / 20 : ℝ)
            + 2 * ((x : ℝ) / L ^ (A + 6))) * (1 + L) ^ 4) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = 16384 * Real.sqrt 2 * ((x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 4)
            + 16384 * (((x : ℝ) / L ^ (A + 6)) * (1 + L) ^ 4) := by ring
      _ ≤ 16384 * Real.sqrt 2 * ((x : ℝ) ^ (19 / 20 : ℝ) * (1 + L) ^ 4)
            + 262144 * ((x : ℝ) / L ^ A) := by linarith [hIItail]
  have hsh_small : 4 * (1 + L) * (L ^ (A + 6) * (K * y / (Real.log (y : ℝ)) ^ (2 * A + 7)))
      ≤ 8 * K * (2 : ℝ) ^ (2 * A + 7) * ((x : ℝ) / L ^ A) :=
    small_term_le hxr0.le (by exact_mod_cast hyx) (by positivity) hK0 (by linarith) hL4 hly
  -- outer factor bound and final assembly
  have hINNER_nn : (0 : ℝ) ≤ ((Q : ℝ) * (U : ℝ) * L + 3 * (U : ℝ) * Sf * (1 + L) ^ 2
        + 2 * ((U : ℝ) * (U : ℝ)) * Sf * (1 + L) ^ 2
        + 2048 * (Real.sqrt (x : ℝ) * (Q : ℝ) + (x : ℝ) / Real.sqrt (U : ℝ)
            + (x : ℝ) / Real.sqrt (U : ℝ) + (x : ℝ) / L ^ (A + 6)) * (1 + L) ^ 3)
      + L ^ (A + 6) * (K * y / (Real.log (y : ℝ)) ^ (2 * A + 7)) := by
    have hd1 : (0 : ℝ) ≤ (x : ℝ) / Real.sqrt (U : ℝ) := by positivity
    have hd2 : (0 : ℝ) ≤ (x : ℝ) / L ^ (A + 6) := by positivity
    have hd3 : (0 : ℝ) ≤ K * y / (Real.log (y : ℝ)) ^ (2 * A + 7) := hval
    have hb1 : (0 : ℝ) ≤ (Q : ℝ) * (U : ℝ) * L := by positivity
    have hb2 : (0 : ℝ) ≤ 3 * (U : ℝ) * Sf * (1 + L) ^ 2 := by positivity
    have hb3 : (0 : ℝ) ≤ 2 * ((U : ℝ) * (U : ℝ)) * Sf * (1 + L) ^ 2 := by positivity
    have hb4 : (0 : ℝ) ≤ 2048 * (Real.sqrt (x : ℝ) * (Q : ℝ) + (x : ℝ) / Real.sqrt (U : ℝ)
        + (x : ℝ) / Real.sqrt (U : ℝ) + (x : ℝ) / L ^ (A + 6)) * (1 + L) ^ 3 := by positivity
    have hb5 : (0 : ℝ) ≤ L ^ (A + 6) * (K * y / (Real.log (y : ℝ)) ^ (2 * A + 7)) := by positivity
    linarith [hb1, hb2, hb3, hb4, hb5]
  have hfac : 4 * (1 + Real.log (Q : ℝ)) ≤ 4 * (1 + L) := by linarith [hlogQ_le_L]
  -- `ring`-bridges (which handle the irrational `√2` coefficient in `Mc`, unlike `linarith`)
  -- reassociate the split RHS into the five shares; no term needs to be transcribed.
  refine le_trans hsplit (le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hfac hINNER_nn))
    (le_trans (le_of_eq (by ring))
      (le_trans (add_le_add hsh_desc (add_le_add (add_le_add (add_le_add
          (add_le_add hsh_head hsh_I1) hsh_I2) hsh_II) hsh_small))
        (le_of_eq (by ring)))))

/-! ## The unconditional keystone -/

open Filter Topology in
/-- **V3.1 — unconditional ψ-form BV dispersion.** Given only `SiegelWalfisz`, the frozen
dispersion estimate holds: for every saving `A`, there are `B, C ≥ 0` with the `∀-fixed-y`
summed maximal discrepancy `≤ C·x/(log x)^A` over the haircut range `q ≤ √x/(log x)^B`.
Obtained by composing the landed keystone `psi_BV_of_siegelWalfisz` with the discharged
large-`y` term budget `largeY_bound`. -/
theorem psi_BV_of_siegelWalfisz' (hSW : SiegelWalfisz) :
    ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ x y : ℕ, 2 ≤ x → y ≤ x →
      ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊, dispDisc y q
        ≤ C * x / (Real.log x) ^ A :=
  psi_BV_of_siegelWalfisz hSW (largeY_bound hSW)

end Salt.BV
