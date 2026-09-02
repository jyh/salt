/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.GoldbachEnergyKc
import Salt.Entropy.Chowla.ShiftFork

/-!
# ⟦THE LARGE-SPECTRUM COUNT CONSTANT AT SHIFT `h`⟧ — wave H2a, word 1(a)–(c)

`bigXi_bounded_ceiling_of_pin` (`GoldbachEnergyKc.lean:231`) carries the terminal road's rider
`C ≤ 2^539`, and it is pinned BY HYPOTHESIS at the literal `ε = 1/500`.  The `h` lane pins
`ε = 1/(500·h)`, so that lemma does not apply and the `h` head reached instead for the
EXISTENTIAL `bigXi_bounded` — which exports only `0 < C`.  That is why `Kc ≤ 2^539` was
unreachable on the `h` lane, and it is the same defect as wave H1's `Cg` artifact: one `obtain`
reaching for the unbounded sibling.  This file removes it.

⟦THE ARITHMETIC, AND WHY IT IS TWO CASES AND NOT ONE⟧  At `ε = 1/(500·h)` the sieve threshold
must move with the shift.  `T := 2^41·h²` is the choice that keeps `hTA : 4 ≤ ε²·T` **`h`-FREE**
(`ε²·T = 2^41/250000 = 8 796 093.02`), which `T := 2^41·h³` does not.  The `C₁` payoff is then

  `C₁'(h) ≤ 1.58277·10^10 + 2.58249·10^10·h²`   against   `2^35·h² = 3.43597·10^10·h²`,

which holds for every `h ≥ 2` (ratio 0.867 at `h = 2`, 0.752 at `h = 1096`) and **FAILS at
`h = 1` by 1.212×** — because at `h = 1` the uniform `(log T)² ≤ 1799.4` is far looser than the
true `807.70`.  So `h = 1` is discharged by the LANDED `hpt_const_le_pow35`
(`GoldbachEnergyN0.lean:809`, ratio 0.955) and `h ≥ 2` by the uniform bound.  Two cases, forced.

⟦THE TOTAL⟧  The count witness is `h · 32·exp 40·(2^35·h²)²/ε^10 = 32·exp 40·2^70·500^10·h^15`.
⚠️ The exponent is `h^15`, not `h^11`: `ε^{-10}` gives ten, the squared constant `C₁(h)² = 2^70·h^4`
gives four, and the fiber bound gives one.  At `h ≤ 1096` that is `2^379.53` against `2^539` —
**159.47 bits of headroom.**

Nothing here bears on twin primes: the count is a bound on `|Ξ_H(h)|`, conditional on nothing.
-/

noncomputable section

namespace Salt.Entropy.Chowla

open scoped BigOperators

/-! ## §1 — the `C₁` numeral at shift `h` -/

/-- **⟦THE `C₁` NUMERAL AT SHIFT `h`⟧** (`hpt_const_le_pow35_h`) — `hpt_const_le_pow35`
(`GoldbachEnergyN0.lean:809`) at `ε = 1/(500·h)`, `T = 2^41·h²`, `c₀ = 1/256`.

The two cases are forced, not stylistic: the `hh7`-uniform `(log T)² ≤ 1799.4` overshoots at
`h = 1` (giving `4.166·10^10 > 3.436·10^10`), while at `h = 1` the landed lemma's own tight
`(log T)² = 807.70` gives `3.283·10^10 ≤ 3.436·10^10`. -/
theorem hpt_const_le_pow35_h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) :
    (800 / (1 / 256 : ℝ) + 102400 / (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) ^ 2)
        + ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) ^ 2 * ((2 ^ 41 * h ^ 2 : ℕ) : ℝ) + 2
            + 1 / (2 * ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ)) ^ 2))
          * (Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ)) ^ 2
      ≤ 2 ^ 35 * (h : ℝ) ^ 2 := by
  have hx0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hcast : (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) := by
    push_cast; ring
  have hTcast : ((2 ^ 41 * h ^ 2 : ℕ) : ℝ) = (2 : ℝ) ^ (41 : ℕ) * (h : ℝ) ^ 2 := by
    push_cast; ring
  rcases Nat.lt_or_ge h 2 with h1 | h2
  · -- ⟦h = 1⟧ the landed lemma, whose tight `(log T)² = 807.70` is what carries it
    have : h = 1 := by omega
    subst this
    have hl := hpt_const_le_pow35
    norm_num at hl ⊢
    convert hl using 3 <;> norm_num
  · -- ⟦h ≥ 2⟧ the uniform bound, with `h² ≥ 4` paying the `h`-free residue
    have hx2 : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast h2
    have hsq4 : (4 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith [hx2]
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hlogh0 : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_nonneg (by linarith)
    have hlogT : Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ) = 41 * Real.log 2 + 2 * Real.log (h : ℝ) := by
      rw [hTcast, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast; ring
    have hLnn : (0 : ℝ) ≤ Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ) := by
      rw [hlogT]; nlinarith [Real.log_two_gt_d9, hlogh0]
    have hLub : Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ) ≤ 42.42 := by
      rw [hlogT]; linarith
    have hLsq : (Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ)) ^ 2 ≤ 1799.4564 := by
      have := pow_le_pow_left₀ hLnn hLub 2
      calc (Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ)) ^ 2 ≤ (42.42 : ℝ) ^ 2 := this
        _ = 1799.4564 := by norm_num
    -- ⚠️ the goal's log stays at the ℕ-CAST argument throughout: rewriting it to the ℝ form
    -- would make `hLsq` speak about a DIFFERENT atom and `nlinarith` could not use it.
    rw [hcast]
    have e1 : (102400 : ℝ) / (1 / (500 * (h : ℝ))) ^ 2 = 25600000000 * (h : ℝ) ^ 2 := by
      field_simp; ring
    have e2 : (1 / (500 * (h : ℝ))) ^ 2 * ((2 ^ 41 * h ^ 2 : ℕ) : ℝ)
        = 2199023255552 / 250000 := by
      rw [hTcast]; field_simp; ring
    have e3 : (1 : ℝ) / (2 * (1 / (500 * (h : ℝ))) ^ 2) = 125000 * (h : ℝ) ^ 2 := by
      field_simp; ring
    have e0 : (800 : ℝ) / (1 / 256 : ℝ) = 204800 := by norm_num
    rw [e0, e1, e2, e3]
    -- `204800 + 2.56e10·h² + (8796093.02 + 2 + 125000·h²)·L² ≤ 2^35·h²` at `L² ≤ 1799.4564`
    nlinarith [hLsq, hsq4, sq_nonneg (Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ))]

/-! ## §2 — the shift's own `ℕ` bound -/

/-- `hh7 : log h ≤ 7` gives `h ≤ 1096` (`e^7 = 1096.63…`).  ⚠️ `Salt.MR.h_le_1096_of_hh7`
(wave H1, `S16ProducersH.lean`) is the MR-side twin of this; the MR side imports Entropy and not
the reverse, so the Entropy-side copy is stated here rather than reached for.  A later wave may
collapse them — recorded so the duplication is deliberate and visible, not discovered. -/
theorem h_le_1096_of_log_le_seven {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) :
    h ≤ 1096 := by
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hhle : (h : ℝ) ≤ Real.exp 7 := by
    rw [← Real.exp_log hh0]; exact Real.exp_le_exp.mpr hh7
  have he7 : Real.exp 7 < 1097 := by
    have h3 : Real.exp 7 = (Real.exp 1) ^ (7 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h5 : (Real.exp 1) ^ (7 : ℕ) < (2.7182818286 : ℝ) ^ (7 : ℕ) :=
      pow_lt_pow_left₀ h4 (Real.exp_pos 1).le (by norm_num)
    have h6 : (2.7182818286 : ℝ) ^ (7 : ℕ) < 1097 := by norm_num
    rw [h3]; linarith
  have : (h : ℝ) < 1097 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-! ## §3 — the `hpt` twin at `ε = 1/(500·h)` -/

set_option exponentiation.threshold 4000 in
/-- **⟦THE `hpt` TWIN AT SHIFT `h`⟧** (`hpt_holds_500h`) — `hpt_holds_500`
(`GoldbachEnergyN0.lean:829`) at `ε = 1/(500·h)` and `T = 2^41·h²`, with the numeral constant
`2^35·h²` from §1.  The four threshold side conditions and their `h`-powers:
`hT0 : 2^20 ≤ 2^41·h²` (h², slack `2^21·h²`) · **`hTA : 4 ≤ ε²·T = 2^41/250000 = 8 796 093.02`
— `h`-FREE, and that is exactly what `T := 2^41·h²` buys over `2^41·h³`** ·
`hTB : 16^10 = 2^40 ≤ 2^41·h²` (h², slack `2h²`) ·
`hTD : (500000·h²)^10 ≤ (2^41·h²)^9`, i.e. `500000^10·h² ≤ 2^369`, i.e. `h² ≤ 1.23·10^54`
(slack `1.02·10^48` at `h = 1096`). -/
theorem hpt_holds_500h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) :
    ∀ H n : ℕ,
      (repCount (primeWindow (1 / (500 * (h : ℚ))) H)
          (primeWindow (1 / (500 * (h : ℚ))) H) n : ℝ)
        ≤ ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2)
            * ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by
  have hx0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hq0 : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  have hq1 : (1 : ℚ) ≤ (h : ℚ) := by exact_mod_cast hh
  have hx1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hcast : (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) := by push_cast; ring
  have hTcast : ((2 ^ 41 * h ^ 2 : ℕ) : ℝ) = (2 : ℝ) ^ (41 : ℕ) * (h : ℝ) ^ 2 := by
    push_cast; ring
  have h1096 : (h : ℝ) ≤ 1096 := by exact_mod_cast h_le_1096_of_log_le_seven hh hh7
  intro H n
  refine le_trans (hpt_holds_thr (1 / (500 * (h : ℚ))) (by positivity) ?_ (1 / 256)
    (by norm_num) 16 repCount_even_le_primorial_sixteen (2 ^ 41 * h ^ 2) ?_ ?_ ?_ ?_ H n) ?_
  · -- `heps2 : ε² < 1/2`
    rw [hcast]
    have : (1 : ℝ) / (500 * (h : ℝ)) ≤ 1 / 500 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hx1]
    have h0 : (0 : ℝ) < 1 / (500 * (h : ℝ)) := by positivity
    nlinarith [this, h0]
  · -- `hT0 : N0' ≤ T`
    have : (2 : ℕ) ^ 20 ≤ 2 ^ 41 * h ^ 2 := by
      have hh2 : 1 ≤ h ^ 2 := Nat.one_le_pow _ _ hh
      calc (2 : ℕ) ^ 20 ≤ 2 ^ 41 := by norm_num
        _ = 2 ^ 41 * 1 := by ring
        _ ≤ 2 ^ 41 * h ^ 2 := Nat.mul_le_mul_left _ hh2
    simpa [N0'] using this
  · -- `hTA : 4 ≤ ε²·T` — h-FREE
    have hTq : (((2 ^ 41 * h ^ 2 : ℕ) : ℚ)) = 2 ^ 41 * (h : ℚ) ^ 2 := by push_cast; ring
    rw [hTq]
    have hid : (1 / (500 * (h : ℚ))) ^ 2 * (2 ^ 41 * (h : ℚ) ^ 2) = 2 ^ 41 / 250000 := by
      field_simp; ring
    rw [hid]; norm_num
  · -- `hTB : 16^10 ≤ T`
    rw [hTcast]
    have hsq1 : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith [hx1]
    have h16 : ((16 : ℕ) : ℝ) ^ (10 : ℕ) = 1099511627776 := by norm_num
    have h41 : (2 : ℝ) ^ (41 : ℕ) = 2199023255552 := by norm_num
    rw [h16, h41]
    nlinarith [hsq1]
  · -- `hTD : (2/ε²)^10 ≤ T^9`
    rw [hcast, hTcast]
    have hsq1 : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith [hx1]
    have hsqb : (h : ℝ) ^ 2 ≤ 1201216 := by nlinarith [hx1, h1096]
    have hL : (2 : ℝ) / (1 / (500 * (h : ℝ))) ^ 2 = 500000 * (h : ℝ) ^ 2 := by
      field_simp; ring
    rw [hL]
    have hexp : ((500000 : ℝ) * (h : ℝ) ^ 2) ^ (10 : ℕ)
        = 500000 ^ (10 : ℕ) * ((h : ℝ) ^ 2) ^ (10 : ℕ) := by ring
    have hexp9 : ((2 : ℝ) ^ (41 : ℕ) * (h : ℝ) ^ 2) ^ (9 : ℕ)
        = (2 : ℝ) ^ (369 : ℕ) * ((h : ℝ) ^ 2) ^ (9 : ℕ) := by
      rw [mul_pow, ← pow_mul]
    rw [hexp, hexp9]
    have hp9 : (0 : ℝ) < ((h : ℝ) ^ 2) ^ (9 : ℕ) := by positivity
    have hsplit : ((h : ℝ) ^ 2) ^ (10 : ℕ) = ((h : ℝ) ^ 2) ^ (9 : ℕ) * (h : ℝ) ^ 2 := by ring
    rw [hsplit]
    -- `500000^10 · (h²)^9 · h² ≤ 2^369 · (h²)^9`  ⟸  `500000^10 · h² ≤ 2^369`
    have hnum : (500000 : ℝ) ^ (10 : ℕ) * (h : ℝ) ^ 2 ≤ (2 : ℝ) ^ (369 : ℕ) := by
      have hb : (500000 : ℝ) ^ (10 : ℕ) * 1201216 ≤ (2 : ℝ) ^ (369 : ℕ) := by norm_num
      nlinarith [hsqb, hsq1]
    calc (500000 : ℝ) ^ (10 : ℕ) * (((h : ℝ) ^ 2) ^ (9 : ℕ) * (h : ℝ) ^ 2)
        = ((500000 : ℝ) ^ (10 : ℕ) * (h : ℝ) ^ 2) * ((h : ℝ) ^ 2) ^ (9 : ℕ) := by ring
      _ ≤ (2 : ℝ) ^ (369 : ℕ) * ((h : ℝ) ^ 2) ^ (9 : ℕ) :=
          mul_le_mul_of_nonneg_right hnum hp9.le
  · -- the constant, from §1
    have hnn : (0 : ℝ) ≤ ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) ^ 2 * H / (Real.log H) ^ 2)
        * sTrunc2 n :=
      mul_nonneg (div_nonneg (by positivity) (sq_nonneg _)) (sTrunc2_nonneg n)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hpt_const_le_pow35_h h hh hh7) (by positivity))
      (sTrunc2_nonneg n)

/-! ## §4 — the count ceiling at shift `h` -/

set_option exponentiation.threshold 4000 in
/-- **⟦THE COMPOSE HOOK AT SHIFT `h`⟧** (`bigXiH_bounded_ceiling_of_pin`) —
`bigXi_bounded_ceiling_of_pin` (`GoldbachEnergyKc.lean:231`) at the `h` lane's own pin
`ε = 1/(500·h)`, carrying the terminal road's rider `C ≤ 2^539`.

**This is the lemma whose absence made `Kc ≤ 2^539` unreachable at `h`.** The `h` head obtains
`bigXiH_bounded` (`ShiftFork.lean:253`), which routes through the EXISTENTIAL `bigXi_bounded`
and exports only `0 < C`; the `h = 1` head obtains the pinned hook and gets the ceiling with it.
One `obtain` — the same shape as wave H1's `Cg` artifact.

⟦THE WITNESS AND ITS SIZE⟧ `h · 32·exp 40·(2^35·h²)²·(500h)^10 = 32·exp 40·2^70·500^10·h^15`.
The exponent is **`h^15`**: `ε^{-10}` gives ten, the squared constant `C₁(h)² = 2^70·h^4` gives
four, the fiber bound `bigXiH_card_le_mul` gives one. On the corpus's own chain
(`exp 40 ≤ 3^40`) that is `2^379.53` at `h ≤ 1096`, against `2^539` — **159.47 bits spare**. -/
theorem bigXiH_bounded_ceiling_of_pin (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    (ε : ℚ) (hε : ε = 1 / (500 * (h : ℚ))) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 539 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((bigXiH h ε H).card : ℝ) ≤ C := by
  subst hε
  have hx0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hx1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hq0 : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  have h1096 : (h : ℝ) ≤ 1096 := by exact_mod_cast h_le_1096_of_log_le_seven hh hh7
  have hcast : (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) := by push_cast; ring
  have heps2 : ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ)) ^ 2 < 1 / 2 := by
    rw [hcast]
    have hle : (1 : ℝ) / (500 * (h : ℝ)) ≤ 1 / 500 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hx1]
    have h0 : (0 : ℝ) < 1 / (500 * (h : ℝ)) := by positivity
    nlinarith [hle, h0]
  have hbase := bigXi_bounded_explicit (1 / (500 * (h : ℚ))) (by positivity) heps2
    ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) (Real.exp 40) (Real.exp_pos _) hFac2_lcm_sum_le_exp40
    (hpt_holds_500h h hh hh7)
  -- ⟦THE WITNESS, DIVISION-FREE⟧
  refine ⟨32 * Real.exp 40 * ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) ^ 2 * (500 * (h : ℝ)) ^ (10 : ℕ)
      * (h : ℝ), by positivity, ?_, 2, le_rfl, ?_⟩
  · -- ⟦THE CEILING⟧ `32·exp 40·2^70·500^10·h^15 ≤ 2^539`
    have h40 : Real.exp 40 ≤ 3 ^ (40 : ℕ) := by
      simpa using exp_forty_le_pow40
    have hexp0 : (0 : ℝ) < Real.exp 40 := Real.exp_pos _
    have hfold : 32 * Real.exp 40 * ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) ^ 2 * (500 * (h : ℝ)) ^ (10 : ℕ)
        * (h : ℝ)
        = (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * Real.exp 40 * (h : ℝ) ^ (15 : ℕ) := by
      ring
    have hp15 : (h : ℝ) ^ (15 : ℕ) ≤ (1096 : ℝ) ^ (15 : ℕ) :=
      pow_le_pow_left₀ hx0.le h1096 15
    have hnn : (0 : ℝ) ≤ 32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ) := by positivity
    have hnum : (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * 3 ^ (40 : ℕ) * (1096 : ℝ) ^ (15 : ℕ)
        ≤ 2 ^ 539 := by norm_num
    rw [hfold]
    calc (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * Real.exp 40 * (h : ℝ) ^ (15 : ℕ)
        ≤ (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * 3 ^ (40 : ℕ) * (1096 : ℝ) ^ (15 : ℕ) := by
          have h1 : (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * Real.exp 40
              ≤ (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * 3 ^ (40 : ℕ) :=
            mul_le_mul_of_nonneg_left h40 hnn
          have h2 : (0 : ℝ) ≤ (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * 3 ^ (40 : ℕ) := by positivity
          nlinarith [h1, h2, hp15, pow_nonneg hx0.le 15]
      _ ≤ 2 ^ 539 := hnum
  · -- ⟦THE BOUND⟧ the fiber times the pinned count
    intro H _ hH2
    have hfib : ((bigXiH h (1 / (500 * (h : ℚ))) H).card : ℝ)
        ≤ (h : ℝ) * ((bigXi (1 / (500 * (h : ℚ))) H).card : ℝ) := by
      exact_mod_cast bigXiH_card_le_mul h hh (1 / (500 * (h : ℚ))) H
    have hb := hbase H hH2
    have hden : 32 * Real.exp 40 * ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) ^ 2
          / ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ)) ^ 10
        = 32 * Real.exp 40 * ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) ^ 2 * (500 * (h : ℝ)) ^ (10 : ℕ) := by
      rw [hcast]; field_simp
    rw [hden] at hb
    calc ((bigXiH h (1 / (500 * (h : ℚ))) H).card : ℝ)
        ≤ (h : ℝ) * ((bigXi (1 / (500 * (h : ℚ))) H).card : ℝ) := hfib
      _ ≤ (h : ℝ) * (32 * Real.exp 40 * ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) ^ 2
            * (500 * (h : ℝ)) ^ (10 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hb hx0.le
      _ = 32 * Real.exp 40 * ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) ^ 2 * (500 * (h : ℝ)) ^ (10 : ℕ)
            * (h : ℝ) := by ring

end Salt.Entropy.Chowla

end
