import Mathlib

/-!
# Budget-floor analytic core (SPINE-BUDGET wave 1a)

Freestanding real-analysis lemmas for the SPINE-BUDGET head.  This file imports
`Mathlib` only.

* `budgetX` / `budgetFloor` — the budget exponent and its triple-exponential
  ceiling floor (rung R1).
* `budgetX_le_logloglog` — the transfer lemma (rung R1).
* `budget_facts` — the five budget facts (rung R2).
* `bracket_close` — the sqrt product/quotient bracket inequality (rung R3).

`budgetX` is internal; per the freeze it may be *enlarged* only, never shrunk.
-/

namespace Salt.Entropy.Chowla

/-- The budget exponent `X ε β`.  Internal (enlargeable, never shrinkable). -/
noncomputable def budgetX (ε β : ℝ) : ℝ :=
  3000 * Real.log 4 * (1 / β ^ 2 + 1 / β + 1) * (1 / ε ^ 6 + 1) + 3

/-- The budget floor: the triple-exponential ceiling of `budgetX`. -/
noncomputable def budgetFloor (ε β : ℝ) : ℕ :=
  ⌈Real.exp (Real.exp (Real.exp (budgetX ε β)))⌉₊

/-- A crude quadratic lower bound for `Real.exp`, from `add_one_le_exp`. -/
theorem sq_div_four_le_exp {t : ℝ} (ht : 0 ≤ t) : t ^ 2 / 4 ≤ Real.exp t := by
  have h1 : t / 2 + 1 ≤ Real.exp (t / 2) := Real.add_one_le_exp (t / 2)
  have h2 : (0 : ℝ) ≤ t / 2 + 1 := by linarith
  have h3 : (t / 2 + 1) * (t / 2 + 1) ≤ Real.exp (t / 2) * Real.exp (t / 2) :=
    mul_self_le_mul_self h2 h1
  have h4 : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  nlinarith [h3, h4]

/-- `0 < Real.log 2`. -/
theorem log_two_pos_aux : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- `0 < Real.log 4`. -/
theorem log_four_pos_aux : 0 < Real.log 4 := Real.log_pos (by norm_num)

/-- `Real.log 4 = 2 * Real.log 2`. -/
theorem log_four_eq_aux : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

/-- `1 ≤ Real.log 4`. -/
theorem one_le_log_four_aux : 1 ≤ Real.log 4 := by
  rw [log_four_eq_aux]; linarith [Real.log_two_gt_d9]

/-- The triple-log tower: `H ≥ budgetFloor ε β` forces `logloglog H ≥ X`
(plus the two intermediate exponential bounds and positivity of `H`). -/
theorem budget_tower (ε β : ℝ) (H : ℕ) (hH : budgetFloor ε β ≤ H) :
    0 < (H : ℝ) ∧
    Real.exp (Real.exp (budgetX ε β)) ≤ Real.log H ∧
    Real.exp (budgetX ε β) ≤ Real.log (Real.log H) ∧
    budgetX ε β ≤ Real.log (Real.log (Real.log H)) := by
  have hcast : Real.exp (Real.exp (Real.exp (budgetX ε β))) ≤ (H : ℝ) := by
    calc Real.exp (Real.exp (Real.exp (budgetX ε β)))
        ≤ (⌈Real.exp (Real.exp (Real.exp (budgetX ε β)))⌉₊ : ℝ) := Nat.le_ceil _
      _ = (budgetFloor ε β : ℝ) := by rw [budgetFloor]
      _ ≤ (H : ℝ) := by exact_mod_cast hH
  have hHpos : 0 < (H : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hcast
  have hlogH : Real.exp (Real.exp (budgetX ε β)) ≤ Real.log H := by
    have h := Real.log_le_log (Real.exp_pos _) hcast
    rwa [Real.log_exp] at h
  have hll : Real.exp (budgetX ε β) ≤ Real.log (Real.log H) := by
    have h := Real.log_le_log (Real.exp_pos _) hlogH
    rwa [Real.log_exp] at h
  have hlll : budgetX ε β ≤ Real.log (Real.log (Real.log H)) := by
    have h := Real.log_le_log (Real.exp_pos _) hll
    rwa [Real.log_exp] at h
  exact ⟨hHpos, hlogH, hll, hlll⟩

/-- Transfer lemma (rung R1): `H ≥ budgetFloor ε β → X ε β ≤ logloglog H`. -/
theorem budgetX_le_logloglog (ε β : ℝ) (H : ℕ) (hH : budgetFloor ε β ≤ H) :
    budgetX ε β ≤ Real.log (Real.log (Real.log H)) :=
  (budget_tower ε β H hH).2.2.2

/-- The sqrt product/quotient bracket inequality (rung R3). -/
theorem bracket_close (g β κ κD : ℝ) (hg : 0 < g) (hβ : 0 < β)
    (hs : 0 < κ + Real.log 2) (hκD : κD ≤ κ + Real.log 2)
    (hiv : (κ + Real.log 2) / g ≤ (β / 4) ^ 2)
    (hv : 2 * Real.log 2 / g ≤ β / 2) :
    (Real.sqrt (g * (κ + Real.log 2)) + 2 * Real.log 2) / g
      + κD / Real.sqrt (g * (κ + Real.log 2)) ≤ β := by
  set s := κ + Real.log 2 with hs_def
  have hgs : 0 < g * s := mul_pos hg hs
  set t := Real.sqrt (g * s) with ht_def
  have ht_pos : 0 < t := Real.sqrt_pos.mpr hgs
  have hsg : 0 ≤ s / g := le_of_lt (div_pos hs hg)
  set r := Real.sqrt (s / g) with hr_def
  have hr_sq : r ^ 2 = s / g := Real.sq_sqrt hsg
  -- t / g = r
  have htg_sq : (t / g) ^ 2 = s / g := by
    rw [div_pow, ht_def, Real.sq_sqrt hgs.le]; field_simp [hg.ne']
  have htg_nonneg : 0 ≤ t / g := div_nonneg ht_pos.le hg.le
  have htg : t / g = r := by rw [hr_def, ← htg_sq, Real.sqrt_sq htg_nonneg]
  -- s / t = r
  have hst_sq : (s / t) ^ 2 = s / g := by
    rw [div_pow, ht_def, Real.sq_sqrt hgs.le]; field_simp [hs.ne', hg.ne']
  have hst_nonneg : 0 ≤ s / t := div_nonneg hs.le ht_pos.le
  have hst : s / t = r := by rw [hr_def, ← hst_sq, Real.sqrt_sq hst_nonneg]
  -- κD / t ≤ r
  have hκDt : κD / t ≤ s / t := by gcongr
  have hκDr : κD / t ≤ r := hst ▸ hκDt
  -- r ≤ β / 4
  have hr_le : r ≤ β / 4 := by
    rw [hr_def]
    have h1 : Real.sqrt (s / g) ≤ Real.sqrt ((β / 4) ^ 2) := Real.sqrt_le_sqrt hiv
    rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ β / 4)] at h1
  rw [add_div, htg]
  linarith [hr_le, hv, hκDr]

/-- A single β-monomial with coefficient `≤ 3000·log 4` is dominated by `X ε β`. -/
theorem monomial_le_budgetX (ε β : ℝ) (_hε : 0 < ε) (_hβ : 0 < β) (m K : ℝ)
    (hm_le : m ≤ 1 / β ^ 2 + 1 / β + 1) (hm_nonneg : 0 ≤ m)
    (hK : K ≤ 3000 * Real.log 4) (_hK0 : 0 ≤ K) :
    K * (m / ε ^ 6) ≤ budgetX ε β := by
  have hlog4_pos := log_four_pos_aux
  have hmε : m / ε ^ 6 ≤ (1 / β ^ 2 + 1 / β + 1) * (1 / ε ^ 6 + 1) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hm_le (le_add_of_nonneg_right (by norm_num)) (by positivity)
      (by linarith [hm_le, hm_nonneg])
  have hmε_nonneg : 0 ≤ m / ε ^ 6 := div_nonneg hm_nonneg (by positivity)
  calc K * (m / ε ^ 6)
      ≤ (3000 * Real.log 4) * (m / ε ^ 6) := mul_le_mul_of_nonneg_right hK hmε_nonneg
    _ ≤ (3000 * Real.log 4) * ((1 / β ^ 2 + 1 / β + 1) * (1 / ε ^ 6 + 1)) :=
        mul_le_mul_of_nonneg_left hmε (mul_nonneg (by norm_num) hlog4_pos.le)
    _ ≤ budgetX ε β := by
        rw [budgetX]
        have h : (3000 * Real.log 4) * ((1 / β ^ 2 + 1 / β + 1) * (1 / ε ^ 6 + 1))
            = 3000 * Real.log 4 * (1 / β ^ 2 + 1 / β + 1) * (1 / ε ^ 6 + 1) := by ring
        linarith [h]

/-- The five budget facts (rung R2). -/
theorem budget_facts (ε β : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hβ : 0 < β)
    (H : ℕ) (hH : budgetFloor ε β ≤ H) :
    1 ≤ Real.log H ∧
    0 < ε ^ 6 * (H : ℝ) / (18 * (2 * Real.log 4) * Real.log H) - Real.log 2 ∧
    0 < Real.log (Real.log (Real.log H)) ∧
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) + Real.log 2)
        / (ε ^ 6 * (H : ℝ) / (18 * (2 * Real.log 4) * Real.log H) - Real.log 2)
      ≤ (β / 4) ^ 2 ∧
    2 * Real.log 2 / (ε ^ 6 * (H : ℝ) / (18 * (2 * Real.log 4) * Real.log H) - Real.log 2)
      ≤ β / 2 := by
  obtain ⟨hHpos, hE2, hE1, hLLL⟩ := budget_tower ε β H hH
  have hlog2_pos := log_two_pos_aux
  have hlog4_pos := log_four_pos_aux
  have hlog4_ge1 := one_le_log_four_aux
  have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hε_ne : ε ≠ 0 := hε.ne'
  have hβ_ne : β ≠ 0 := hβ.ne'
  have hε6_pos : (0 : ℝ) < ε ^ 6 := by positivity
  set L := Real.log (H : ℝ) with hL_def
  set L2 := Real.log L with hL2_def
  set L3 := Real.log L2 with hL3_def
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hE2
  have hXpos : 0 < budgetX ε β := by
    rw [budgetX]
    have h0 : (0 : ℝ) ≤ 3000 * Real.log 4 * (1 / β ^ 2 + 1 / β + 1) * (1 / ε ^ 6 + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlog4_pos.le) (by positivity))
        (by positivity)
    linarith
  have hL3pos : 0 < L3 := lt_of_lt_of_le hXpos hLLL
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (Real.exp_pos _).le) hE2
  have hHexp : Real.exp L = (H : ℝ) := by rw [hL_def]; exact Real.exp_log hHpos
  -- the tower is enormous: 4·X ≤ L
  have hX16 : 16 ≤ budgetX ε β := by
    rw [budgetX]
    have hA1 : (1 : ℝ) ≤ 1 / β ^ 2 + 1 / β + 1 := by
      have h1b : (0 : ℝ) < 1 / β ^ 2 := by positivity
      have h2b : (0 : ℝ) < 1 / β := by positivity
      linarith
    have hB1 : (1 : ℝ) ≤ 1 / ε ^ 6 + 1 := le_add_of_nonneg_left (by positivity)
    have hprod1 : (1 : ℝ) ≤ Real.log 4 * (1 / β ^ 2 + 1 / β + 1) * (1 / ε ^ 6 + 1) := by
      have t1 : (1 : ℝ) ≤ Real.log 4 * (1 / β ^ 2 + 1 / β + 1) :=
        calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ Real.log 4 * (1 / β ^ 2 + 1 / β + 1) :=
              mul_le_mul hlog4_ge1 hA1 (by norm_num) hlog4_pos.le
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ Real.log 4 * (1 / β ^ 2 + 1 / β + 1) * (1 / ε ^ 6 + 1) :=
            mul_le_mul t1 hB1 (by norm_num) (by linarith)
    nlinarith [hprod1]
  have hexpX4X : 4 * budgetX ε β ≤ Real.exp (budgetX ε β) := by
    nlinarith [sq_div_four_le_exp hXpos.le, hX16, hXpos]
  have hX_le_expX : budgetX ε β ≤ Real.exp (budgetX ε β) := by
    linarith [Real.add_one_le_exp (budgetX ε β)]
  have h4XL : 4 * budgetX ε β ≤ L :=
    le_trans hexpX4X (le_trans (Real.exp_le_exp.mpr hX_le_expX) hE2)
  have hcore : ∀ c : ℝ, 4 * c ≤ L → c * L ≤ (H : ℝ) := by
    intro c h4c
    calc c * L ≤ (L / 4) * L := mul_le_mul_of_nonneg_right (by linarith) hLpos.le
      _ = L ^ 2 / 4 := by ring
      _ ≤ Real.exp L := sq_div_four_le_exp hLpos.le
      _ = (H : ℝ) := hHexp
  -- Demand A: 2304·log 4 ≤ β²·ε⁶·L3
  have hmono_A := monomial_le_budgetX ε β hε hβ (1 / β ^ 2) (2304 * Real.log 4)
    (by have h := one_div_pos.mpr hβ; linarith) (by positivity)
    (by nlinarith [hlog4_pos]) (mul_nonneg (by norm_num) hlog4_pos.le)
  have hA_demand : 2304 * Real.log 4 ≤ β ^ 2 * ε ^ 6 * L3 := by
    have hstep : (2304 * Real.log 4) * (1 / β ^ 2 / ε ^ 6) ≤ L3 := le_trans hmono_A hLLL
    have hc : β ^ 2 * ε ^ 6 * ((2304 * Real.log 4) * (1 / β ^ 2 / ε ^ 6)) = 2304 * Real.log 4 := by
      field_simp
    calc 2304 * Real.log 4 = β ^ 2 * ε ^ 6 * ((2304 * Real.log 4) * (1 / β ^ 2 / ε ^ 6)) := hc.symm
      _ ≤ β ^ 2 * ε ^ 6 * L3 := mul_le_mul_of_nonneg_left hstep (by positivity)
  -- Demand ii: 72·log2·log4·L ≤ ε⁶·H
  have hmono_ii := monomial_le_budgetX ε β hε hβ 1 (72 * Real.log 2 * Real.log 4)
    (by have h1 : (0 : ℝ) < 1 / β ^ 2 := by positivity
        have h2 : (0 : ℝ) < 1 / β := by positivity
        linarith) (by norm_num) (by nlinarith [hlog2_le1, hlog4_pos])
    (mul_nonneg (mul_nonneg (by norm_num) hlog2_pos.le) hlog4_pos.le)
  have D_ii : 72 * Real.log 2 * Real.log 4 * L ≤ ε ^ 6 * (H : ℝ) := by
    have hcL : (72 * Real.log 2 * Real.log 4 * (1 / ε ^ 6)) * L ≤ (H : ℝ) :=
      hcore _ (by linarith [hmono_ii, h4XL])
    have hc : ε ^ 6 * ((72 * Real.log 2 * Real.log 4 * (1 / ε ^ 6)) * L)
        = 72 * Real.log 2 * Real.log 4 * L := by field_simp
    calc 72 * Real.log 2 * Real.log 4 * L
        = ε ^ 6 * ((72 * Real.log 2 * Real.log 4 * (1 / ε ^ 6)) * L) := hc.symm
      _ ≤ ε ^ 6 * (H : ℝ) := mul_le_mul_of_nonneg_left hcL hε6_pos.le
  -- Demand iv: 2304·log2·log4·L ≤ β²·ε⁶·H
  have hmono_iv := monomial_le_budgetX ε β hε hβ (1 / β ^ 2) (2304 * Real.log 2 * Real.log 4)
    (by have h := one_div_pos.mpr hβ; linarith) (by positivity)
    (by nlinarith [hlog2_le1, hlog4_pos])
    (mul_nonneg (mul_nonneg (by norm_num) hlog2_pos.le) hlog4_pos.le)
  have D_iv : 2304 * Real.log 2 * Real.log 4 * L ≤ β ^ 2 * ε ^ 6 * (H : ℝ) := by
    have hcL : (2304 * Real.log 2 * Real.log 4 * (1 / β ^ 2 / ε ^ 6)) * L ≤ (H : ℝ) :=
      hcore _ (by linarith [hmono_iv, h4XL])
    have hc : β ^ 2 * ε ^ 6 * ((2304 * Real.log 2 * Real.log 4 * (1 / β ^ 2 / ε ^ 6)) * L)
        = 2304 * Real.log 2 * Real.log 4 * L := by field_simp
    calc 2304 * Real.log 2 * Real.log 4 * L
        = β ^ 2 * ε ^ 6 * ((2304 * Real.log 2 * Real.log 4 * (1 / β ^ 2 / ε ^ 6)) * L) := hc.symm
      _ ≤ β ^ 2 * ε ^ 6 * (H : ℝ) := mul_le_mul_of_nonneg_left hcL (by positivity)
  -- Demand v: 288·log2·log4·L ≤ β·ε⁶·H
  have hmono_v := monomial_le_budgetX ε β hε hβ (1 / β) (288 * Real.log 2 * Real.log 4)
    (by have h1 : (0 : ℝ) < 1 / β ^ 2 := by positivity
        have h2 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
        linarith) (by positivity) (by nlinarith [hlog2_le1, hlog4_pos])
    (mul_nonneg (mul_nonneg (by norm_num) hlog2_pos.le) hlog4_pos.le)
  have D_v : 288 * Real.log 2 * Real.log 4 * L ≤ β * ε ^ 6 * (H : ℝ) := by
    have hcL : (288 * Real.log 2 * Real.log 4 * (1 / β / ε ^ 6)) * L ≤ (H : ℝ) :=
      hcore _ (by linarith [hmono_v, h4XL])
    have hc : β * ε ^ 6 * ((288 * Real.log 2 * Real.log 4 * (1 / β / ε ^ 6)) * L)
        = 288 * Real.log 2 * Real.log 4 * L := by field_simp
    calc 288 * Real.log 2 * Real.log 4 * L
        = β * ε ^ 6 * ((288 * Real.log 2 * Real.log 4 * (1 / β / ε ^ 6)) * L) := hc.symm
      _ ≤ β * ε ^ 6 * (H : ℝ) := mul_le_mul_of_nonneg_left hcL (by positivity)
  -- Assemble the gcap facts
  set F := ε ^ 6 * (H : ℝ) / (18 * (2 * Real.log 4) * L) with hF_def
  have hDL_pos : (0 : ℝ) < 18 * (2 * Real.log 4) * L :=
    mul_pos (mul_pos (by norm_num) (mul_pos (by norm_num) hlog4_pos)) hLpos
  have hfirst : 2 * Real.log 2 ≤ F := by
    rw [hF_def, le_div_iff₀ hDL_pos]
    have hr : 2 * Real.log 2 * (18 * (2 * Real.log 4) * L) = 72 * Real.log 2 * Real.log 4 * L := by
      ring
    rw [hr]; exact D_ii
  have hgcap_pos : 0 < F - Real.log 2 := by linarith [hfirst, hlog2_pos]
  have hgcap_ge : F / 2 ≤ F - Real.log 2 := by linarith [hfirst]
  refine ⟨hL1, hgcap_pos, hL3pos, ?_, ?_⟩
  · -- (iv)
    rw [div_le_iff₀ hgcap_pos]
    have e1 : (H : ℝ) / (L * L3) ≤ (β / 4) ^ 2 * (F / 2) / 2 := by
      have he : (β / 4) ^ 2 * (F / 2) / 2
          = β ^ 2 * ε ^ 6 * (H : ℝ) / (64 * (18 * (2 * Real.log 4) * L)) := by
        rw [hF_def]; field_simp; ring
      rw [he, div_le_div_iff₀ (mul_pos hLpos hL3pos) (mul_pos (by norm_num) hDL_pos)]
      have hg1 : (H : ℝ) * (64 * (18 * (2 * Real.log 4) * L))
          = 2304 * Real.log 4 * ((H : ℝ) * L) := by ring
      have hg2 : β ^ 2 * ε ^ 6 * (H : ℝ) * (L * L3)
          = β ^ 2 * ε ^ 6 * L3 * ((H : ℝ) * L) := by ring
      rw [hg1, hg2]
      exact mul_le_mul_of_nonneg_right hA_demand (mul_nonneg hHpos.le hLpos.le)
    have e2 : Real.log 2 ≤ (β / 4) ^ 2 * (F / 2) / 2 := by
      have he : (β / 4) ^ 2 * (F / 2) / 2
          = β ^ 2 * ε ^ 6 * (H : ℝ) / (64 * (18 * (2 * Real.log 4) * L)) := by
        rw [hF_def]; field_simp; ring
      rw [he, le_div_iff₀ (mul_pos (by norm_num) hDL_pos)]
      have hr : Real.log 2 * (64 * (18 * (2 * Real.log 4) * L))
          = 2304 * Real.log 2 * Real.log 4 * L := by ring
      rw [hr]; exact D_iv
    calc (H : ℝ) / (L * L3) + Real.log 2 ≤ (β / 4) ^ 2 * (F / 2) := by linarith [e1, e2]
      _ ≤ (β / 4) ^ 2 * (F - Real.log 2) := mul_le_mul_of_nonneg_left hgcap_ge (by positivity)
  · -- (v)
    rw [div_le_iff₀ hgcap_pos]
    have h8 : 2 * Real.log 2 ≤ β / 2 * (F / 2) := by
      have he : β / 2 * (F / 2) = β * ε ^ 6 * (H : ℝ) / (4 * (18 * (2 * Real.log 4) * L)) := by
        rw [hF_def]; field_simp; ring
      rw [he, le_div_iff₀ (mul_pos (by norm_num) hDL_pos)]
      have hr : 2 * Real.log 2 * (4 * (18 * (2 * Real.log 4) * L))
          = 288 * Real.log 2 * Real.log 4 * L := by ring
      rw [hr]; exact D_v
    calc 2 * Real.log 2 ≤ β / 2 * (F / 2) := h8
      _ ≤ β / 2 * (F - Real.log 2) := mul_le_mul_of_nonneg_left hgcap_ge (by linarith)

end Salt.Entropy.Chowla
