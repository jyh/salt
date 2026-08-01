/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# THE FLAT BUDGET FLOOR — HEIGHT 1 (freeze item F-3)

The landed `budgetFloor ε β = ⌈exp (exp (exp (budgetX ε β)))⌉₊` is a HEIGHT-3
tower — the second face of the `Hcap` wall.  At the flat threshold
`κ = H/(A·log H)` the third exponential is unnecessary: fact (iii) of
`budget_facts` degenerates from `0 < logloglog H` to `0 < A`, and the only
`H`-dependent demand that read `L3` (fact (iv)) reads the design constant `A`
instead.  What is left is HEIGHT 1:

    budgetXFlat ε β       = budgetX ε β                            (unchanged)
    budgetAFlat ε β       = 2304·log 4 / (ε⁶·β²)                   (the (iv) demand)
    budgetFloorFlat ε β A = ⌈exp (max (4·budgetXFlat ε β) (2·log A + 2))⌉₊

The `max`'s first arm funds the four surviving demands through the landed
`hcore` route (`c·L ≤ H` whenever `4c ≤ L`); its second arm funds the one NEW
side condition the flat road carries, `A·L·log 2 ≤ H` (`budgetFloorFlat_side`).

Facts (i)/(ii)/(v) of `budget_factsFlat` are byte-identical to `budget_facts`;
(iii) is `0 < A`; (iv) is the landed statement with `L·L3` replaced by `A·L`.
Everything is ADDITIVE: `BudgetCore.lean` is untouched and its
`monomial_le_budgetX` / `sq_div_four_le_exp` are reused verbatim.
-/
import Salt.Entropy.Chowla.BudgetCore

namespace Salt.Entropy.Chowla

/-- The flat budget exponent — UNCHANGED from the landed `budgetX` (freeze F-3);
    named separately so the flat cone reads in its own glyphs. -/
noncomputable def budgetXFlat (ε β : ℝ) : ℝ := budgetX ε β

/-- **The flat design constant's demand.**  Fact (iv) at the flat threshold asks
    exactly `2304·log 4 ≤ A·β²·ε⁶`; `budgetAFlat` is the least `A` clearing it.
    (The landed height-3 road spent this demand on `logloglog H` instead.) -/
noncomputable def budgetAFlat (ε β : ℝ) : ℝ := 2304 * Real.log 4 / (ε ^ 6 * β ^ 2)

/-- **THE FLAT BUDGET FLOOR — HEIGHT 1.**  The triple exponential of
    `budgetFloor` collapses to a single one; the second `max` arm funds the flat
    road's new side condition `A·log H·log 2 ≤ H`. -/
noncomputable def budgetFloorFlat (ε β A : ℝ) : ℕ :=
  ⌈Real.exp (max (4 * budgetXFlat ε β) (2 * Real.log A + 2))⌉₊

/-- The height-1 tower: `H ≥ budgetFloorFlat ε β A` forces both `max` arms below
    `log H` (and `H > 0`). -/
theorem budget_towerFlat (ε β A : ℝ) (H : ℕ) (hH : budgetFloorFlat ε β A ≤ H) :
    0 < (H : ℝ) ∧ 4 * budgetX ε β ≤ Real.log H ∧ 2 * Real.log A + 2 ≤ Real.log H := by
  have hcast : Real.exp (max (4 * budgetXFlat ε β) (2 * Real.log A + 2)) ≤ (H : ℝ) := by
    calc Real.exp (max (4 * budgetXFlat ε β) (2 * Real.log A + 2))
        ≤ (⌈Real.exp (max (4 * budgetXFlat ε β) (2 * Real.log A + 2))⌉₊ : ℝ) := Nat.le_ceil _
      _ = (budgetFloorFlat ε β A : ℝ) := by rw [budgetFloorFlat]
      _ ≤ (H : ℝ) := by exact_mod_cast hH
  have hHpos : 0 < (H : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hcast
  have hmax : max (4 * budgetXFlat ε β) (2 * Real.log A + 2) ≤ Real.log H := by
    have h := Real.log_le_log (Real.exp_pos _) hcast
    rwa [Real.log_exp] at h
  exact ⟨hHpos, le_trans (le_max_left _ _) hmax, le_trans (le_max_right _ _) hmax⟩

/-- **The flat road's one new side condition** (FLAT-REF §1): `A·log H·log 2 ≤ H`,
    funded by the second `max` arm `2·log A + 2 ≤ log H`. -/
theorem budgetFloorFlat_side (ε β A : ℝ) (hA : 1 ≤ A) (H : ℕ)
    (hH : budgetFloorFlat ε β A ≤ H) : A * Real.log H * Real.log 2 ≤ (H : ℝ) := by
  obtain ⟨hHpos, _h4X, hAarm⟩ := budget_towerFlat ε β A H hH
  have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlog2_pos : 0 < Real.log 2 := log_two_pos_aux
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  set L := Real.log (H : ℝ) with hL_def
  have hL2 : (2 : ℝ) ≤ L := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hHexp : Real.exp L = (H : ℝ) := by rw [hL_def]; exact Real.exp_log hHpos
  -- `log L ≤ L/2`
  have hlogL : Real.log L ≤ L / 2 := by
    have hhalf : Real.log (L / 2) ≤ L / 2 - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have hsplit : Real.log L = Real.log 2 + Real.log (L / 2) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      congr 1
      field_simp
    linarith
  -- `log (A·L) ≤ L − 1`
  have hAL_pos : (0 : ℝ) < A * L := by positivity
  have hlogAL : Real.log (A * L) ≤ L - 1 := by
    rw [Real.log_mul (by linarith) (ne_of_gt hLpos)]
    linarith
  have hALle : A * L ≤ Real.exp (L - 1) := by
    rw [← Real.log_le_iff_le_exp hAL_pos]; exact hlogAL
  have hexpmono : Real.exp (L - 1) ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
  have hfinal : A * L ≤ (H : ℝ) := by rw [← hHexp]; linarith
  nlinarith [hfinal, hAL_pos, hlog2_le1, hlog2_pos]

/-- **THE FIVE FLAT BUDGET FACTS** (freeze F-3).  (i)/(ii)/(v) are byte-identical
    to `budget_facts`; (iii) is `0 < A`; (iv) carries the flat threshold
    `κ = H/(A·log H)` in place of `H/(log H·logloglog H)`.  HEIGHT 1: the
    hypothesis is `budgetFloorFlat ε β A ≤ H`, plus the design demand
    `budgetAFlat ε β ≤ A`. -/
theorem budget_factsFlat (ε β A : ℝ) (hε : 0 < ε) (_hε2 : ε ≤ 1 / 2) (hβ : 0 < β)
    (hApos : 0 < A) (hAge : budgetAFlat ε β ≤ A)
    (H : ℕ) (hH : budgetFloorFlat ε β A ≤ H) :
    1 ≤ Real.log H ∧
    0 < ε ^ 6 * (H : ℝ) / (18 * (2 * Real.log 4) * Real.log H) - Real.log 2 ∧
    0 < A ∧
    ((H : ℝ) / (A * Real.log H) + Real.log 2)
        / (ε ^ 6 * (H : ℝ) / (18 * (2 * Real.log 4) * Real.log H) - Real.log 2)
      ≤ (β / 4) ^ 2 ∧
    2 * Real.log 2 / (ε ^ 6 * (H : ℝ) / (18 * (2 * Real.log 4) * Real.log H) - Real.log 2)
      ≤ β / 2 := by
  obtain ⟨hHpos, h4XL, _hAarm⟩ := budget_towerFlat ε β A H hH
  have hlog2_pos := log_two_pos_aux
  have hlog4_pos := log_four_pos_aux
  have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hε6_pos : (0 : ℝ) < ε ^ 6 := by positivity
  set L := Real.log (H : ℝ) with hL_def
  have hX3 : 3 ≤ budgetX ε β := by
    rw [budgetX]
    have h0 : (0 : ℝ) ≤ 3000 * Real.log 4 * (1 / β ^ 2 + 1 / β + 1) * (1 / ε ^ 6 + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlog4_pos.le) (by positivity))
        (by positivity)
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hHexp : Real.exp L = (H : ℝ) := by rw [hL_def]; exact Real.exp_log hHpos
  have hcore : ∀ c : ℝ, 4 * c ≤ L → c * L ≤ (H : ℝ) := by
    intro c h4c
    calc c * L ≤ (L / 4) * L := mul_le_mul_of_nonneg_right (by linarith) hLpos.le
      _ = L ^ 2 / 4 := by ring
      _ ≤ Real.exp L := sq_div_four_le_exp hLpos.le
      _ = (H : ℝ) := hHexp
  -- THE FLAT DEMAND A: `2304·log 4 ≤ β²·ε⁶·A`
  have hA_demand : 2304 * Real.log 4 ≤ β ^ 2 * ε ^ 6 * A := by
    have h := hAge
    rw [budgetAFlat, div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 6 * β ^ 2)] at h
    have heq : A * (ε ^ 6 * β ^ 2) = β ^ 2 * ε ^ 6 * A := by ring
    linarith
  -- Demand ii: `72·log2·log4·L ≤ ε⁶·H`
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
  -- Demand iv: `2304·log2·log4·L ≤ β²·ε⁶·H`
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
  -- Demand v: `288·log2·log4·L ≤ β·ε⁶·H`
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
  -- Assemble the gcap facts (byte-identical to the landed route)
  set F := ε ^ 6 * (H : ℝ) / (18 * (2 * Real.log 4) * L) with hF_def
  have hDL_pos : (0 : ℝ) < 18 * (2 * Real.log 4) * L :=
    mul_pos (mul_pos (by norm_num) (mul_pos (by norm_num) hlog4_pos)) hLpos
  have hfirst : 2 * Real.log 2 ≤ F := by
    rw [hF_def, le_div_iff₀ hDL_pos]
    have hr : 2 * Real.log 2 * (18 * (2 * Real.log 4) * L)
        = 72 * Real.log 2 * Real.log 4 * L := by ring
    rw [hr]; exact D_ii
  have hgcap_pos : 0 < F - Real.log 2 := by linarith [hfirst, hlog2_pos]
  have hgcap_ge : F / 2 ≤ F - Real.log 2 := by linarith [hfirst]
  refine ⟨hL1, hgcap_pos, hApos, ?_, ?_⟩
  · -- (iv), at the FLAT threshold `H/(A·L)`
    rw [div_le_iff₀ hgcap_pos]
    have e1 : (H : ℝ) / (A * L) ≤ (β / 4) ^ 2 * (F / 2) / 2 := by
      have he : (β / 4) ^ 2 * (F / 2) / 2
          = β ^ 2 * ε ^ 6 * (H : ℝ) / (64 * (18 * (2 * Real.log 4) * L)) := by
        rw [hF_def]; field_simp; ring
      rw [he, div_le_div_iff₀ (mul_pos hApos hLpos) (mul_pos (by norm_num) hDL_pos)]
      have hg1 : (H : ℝ) * (64 * (18 * (2 * Real.log 4) * L))
          = 2304 * Real.log 4 * ((H : ℝ) * L) := by ring
      have hg2 : β ^ 2 * ε ^ 6 * (H : ℝ) * (A * L)
          = β ^ 2 * ε ^ 6 * A * ((H : ℝ) * L) := by ring
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
    calc (H : ℝ) / (A * L) + Real.log 2 ≤ (β / 4) ^ 2 * (F / 2) := by linarith [e1, e2]
      _ ≤ (β / 4) ^ 2 * (F - Real.log 2) := mul_le_mul_of_nonneg_left hgcap_ge (by positivity)
  · -- (v), byte-identical to the landed route
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

