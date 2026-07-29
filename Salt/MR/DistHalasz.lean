/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.OneLinePowGrowth
import Salt.MR.PrimeTail
import Salt.SW.DHBalance

/-!
# S8 MR-CORE wave-2 rungs R1.1/R1.2/R1.4 — the pretentious-distance floor machinery

This file houses the wave-2 Dist-lane rungs of the S8 freeze:

* **R1.1** the pretentious triangle inequality + the halving `dist_mul_half`;
* **R1.2** `dist_one_floor_pow` — the D3 extreme-`t` distance floor
  `𝔻(1, n^{ib}; x)² ≥ loglog x − (3/4)loglog(|b|+3) − 5·logloglog(|b|+16) − C`,
  consuming the H1.0 power-growth stone (`one_line_pow_growth`) and the H0 λ-side
  Euler-oscillation bridge (`log_euler_osc_zeta_unconditional`);
* **R1.4** the capped `M_range` def + `Mrange_one_floor` (the `1/4 − o(1)` floor).

The `−5·logloglog(|b|+16)` correction is the honest `o(loglog x)` shape and is carried
IN-STATEMENT (S5 law: never absorbed into `C`).
-/

namespace Salt.MR

open scoped BigOperators

/-! ## The `𝔻(1, ·)`-distance unfolding -/

/-- **The `𝔻(1, n^{ib})²` split.**  `𝔻(1, n^{ib}; x)² = SPartial x − ∑_{p≤x} cos(b·log p)/p`
(the divergent Mertens part minus the oscillation part). -/
theorem pretDistSq_one_split (b : ℝ) (x : ℝ) :
    pretDistSq (fun _ => 1) (costwist b) x
      = Salt.Mertens.SPartial x
        - ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
            Real.cos (b * Real.log p) / (p : ℝ) := by
  have hSP : Salt.Mertens.SPartial x
      = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := rfl
  have hpd : pretDistSq (fun _ => 1) (costwist b) x
      = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
          (1 - Real.cos (b * Real.log p)) / (p : ℝ) := by
    unfold pretDistSq
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [one_mul, Complex.conj_re, costwist_re]
  rw [hpd, hSP, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  ring

/-! ## R1.2 — the extreme-`t` distance floor (large `|b|` core) -/

/-- **The `log‖ζ`‖ upper expansion.**  For `|b| ≥ T₀` (the H1.0 threshold) and `x ≥ e`,
`log‖ζ(1+1/log x+ib)‖ ≤ log C + (3/4)·loglog|b| + 4·logloglog|b|`, the log of the H1.0
power-growth bound. -/
theorem log_zeta_growth_le {C T₀ : ℝ} (hCpos : 0 < C)
    (hgrowth : ∀ d' t : ℝ, 0 ≤ d' → d' ≤ 1 → T₀ ≤ |t| →
      ‖riemannZeta (((1 + d' : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * ((Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ)))
    {x b : ℝ} (hx : Real.exp 1 ≤ x) (hexp100 : Real.exp (Real.exp 100) ≤ |b|)
    (hbT0 : T₀ ≤ |b|) :
    Real.log ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + (b : ℝ) * Complex.I)‖
      ≤ Real.log C + (3 / 4) * Real.log (Real.log |b|)
          + 4 * Real.log (Real.log (Real.log |b|)) := by
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hd0 : (0 : ℝ) ≤ 1 / Real.log x := by positivity
  have hd1 : 1 / Real.log x ≤ 1 := (div_le_one hLpos).mpr hlogx1
  -- `|b| ≥ e^{e^100}` ⟹ `log|b| ≥ e^100 > 1`, `loglog|b| ≥ 100 > 0`
  have hbpos : (0 : ℝ) < |b| := lt_of_lt_of_le (Real.exp_pos _) hexp100
  have hLb100 : Real.exp 100 ≤ Real.log |b| := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 100)) hexp100
    rwa [Real.log_exp] at h
  have hexp100gt : (1 : ℝ) < Real.exp 100 := by
    have := Real.add_one_le_exp (100 : ℝ); linarith
  have hLb1 : (1 : ℝ) < Real.log |b| := lt_of_lt_of_le hexp100gt hLb100
  have hLbpos : (0 : ℝ) < Real.log |b| := by linarith
  have hℓb100 : (100 : ℝ) ≤ Real.log (Real.log |b|) := by
    have h := Real.log_le_log (Real.exp_pos 100) hLb100
    rwa [Real.log_exp] at h
  have hℓbpos : (0 : ℝ) < Real.log (Real.log |b|) := by linarith
  -- the H1.0 bound at `d' = 1/log x`, `t = b`
  have hgr := hgrowth (1 / Real.log x) b hd0 hd1 hbT0
  -- the `ζ` value is nonzero (Re > 1), so `‖ζ‖ > 0`
  set s : ℂ := ((1 + 1 / Real.log x : ℝ) : ℂ) + (b : ℝ) * Complex.I with hsdef
  have hsre : s.re = 1 + 1 / Real.log x := by
    rw [hsdef]; simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hs1 : 1 < s.re := by rw [hsre]; have : (0 : ℝ) < 1 / Real.log x := by positivity
                            linarith
  have hzne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hznormpos : (0 : ℝ) < ‖riemannZeta s‖ := by positivity
  -- `‖ζ‖ ≤ C·(log|b|)^{3/4}(loglog|b|)^4`; the `s` matches H1.0's argument
  have hgr' : ‖riemannZeta s‖
      ≤ C * ((Real.log |b|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |b|)) ^ (4 : ℕ)) := by
    rw [hsdef]; exact hgr
  -- take logs and expand
  have hApow : (0 : ℝ) < (Real.log |b|) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hLbpos _
  have hBpow : (0 : ℝ) < (Real.log (Real.log |b|)) ^ (4 : ℕ) := pow_pos hℓbpos 4
  have hlog := Real.log_le_log hznormpos hgr'
  rw [Real.log_mul (ne_of_gt hCpos) (ne_of_gt (mul_pos hApow hBpow)),
      Real.log_mul (ne_of_gt hApow) (ne_of_gt hBpow),
      Real.log_rpow hLbpos, Real.log_pow] at hlog
  push_cast at hlog
  linarith [hlog]

/-- **The small-`|b|` `log‖ζ`‖ bound.**  For `1 ≤ |b| ≤ Bhi` and `x ≥ e`,
`log‖ζ(1+1/log x+ib)‖ ≤ log(5 + 2·Bhi)`, a UNIFORM constant on the bounded-`b` range.
Uses the closed-form corpus bound `Salt.SW.norm_riemannZeta_le` (valid off the pole), so no
compactness argument is needed — this closes the `1 ≤ |b| < T₀` regime H1.0 cannot reach. -/
theorem log_zeta_small_b_le {Bhi : ℝ} (hBhi1 : 1 ≤ Bhi) {x b : ℝ}
    (hx : Real.exp 1 ≤ x) (hb1 : 1 ≤ |b|) (hbBhi : |b| ≤ Bhi) :
    Real.log ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + (b : ℝ) * Complex.I)‖
      ≤ Real.log (5 + 2 * Bhi) := by
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hdpos : (0 : ℝ) < 1 / Real.log x := div_pos one_pos hLpos
  have hd1 : 1 / Real.log x ≤ 1 := (div_le_one hLpos).mpr hlogx1
  set s : ℂ := ((1 + 1 / Real.log x : ℝ) : ℂ) + (b : ℝ) * Complex.I with hsdef
  have hsre : s.re = 1 + 1 / Real.log x := by
    rw [hsdef]; simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hsim : s.im = b := by
    rw [hsdef]; simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hσ : (0 : ℝ) < s.re := by rw [hsre]; linarith
  have hs1re : (1 : ℝ) < s.re := by rw [hsre]; linarith
  have hbne : b ≠ 0 := by
    intro h; rw [h] at hb1; simp at hb1; linarith
  have hs1 : s ≠ 1 := by
    intro h; apply hbne; have := congrArg Complex.im h; rw [hsim] at this; simpa using this
  have hbnd := Salt.SW.norm_riemannZeta_le hσ hs1
  -- `‖s − 1‖ ≥ |b| ≥ 1`
  have hsubim : (s - 1).im = b := by rw [Complex.sub_im, hsim, Complex.one_im]; ring
  have hsub1 : (1 : ℝ) ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    rw [hsubim] at h; linarith [hb1, h]
  have hsubpos : (0 : ℝ) < ‖s - 1‖ := by linarith
  -- `‖s‖ ≤ 2 + Bhi`
  have hsnorm : ‖s‖ ≤ 2 + Bhi := by
    have h1 : ‖(((1 + 1 / Real.log x : ℝ)) : ℂ)‖ = 1 + 1 / Real.log x := by
      rw [Complex.norm_real,
        Real.norm_of_nonneg (by linarith [hdpos] : (0 : ℝ) ≤ 1 + 1 / Real.log x)]
    have h2 : ‖((b : ℝ) : ℂ) * Complex.I‖ = |b| := by
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    have hle := norm_add_le (((1 + 1 / Real.log x : ℝ)) : ℂ) (((b : ℝ) : ℂ) * Complex.I)
    rw [h1, h2] at hle
    rw [hsdef]; linarith [hle, hd1, hbBhi]
  -- `1 + 1/Re s ≤ 2`
  have hReinv : 1 + 1 / s.re ≤ 2 := by
    have : 1 / s.re ≤ 1 := (div_le_one hσ).mpr (by linarith [hs1re])
    linarith
  have hReinvpos : (0 : ℝ) ≤ 1 + 1 / s.re := by positivity
  have hznpos : (0 : ℝ) < ‖riemannZeta s‖ := by
    rw [norm_pos_iff]; exact riemannZeta_ne_zero_of_one_lt_re hs1re
  -- assemble `‖ζ‖ ≤ 5 + 2·Bhi`
  have hBD : ‖s‖ * (1 + 1 / s.re) ≤ 4 + 2 * Bhi := by
    nlinarith [hsnorm, hReinv, norm_nonneg s, hReinvpos, hBhi1]
  have hζle : ‖riemannZeta s‖ ≤ 5 + 2 * Bhi := by
    refine le_trans hbnd ?_
    rw [div_le_iff₀ hsubpos]
    nlinarith [mul_le_mul_of_nonneg_left hBD hsubpos.le, hsub1, hBhi1]
  exact Real.log_le_log hznpos hζle

/-- **R1.2 — the D3 extreme-`t` distance floor (`dist_one_floor_pow`).**  For `x ≥ e` and
`1 ≤ |b|`,

  `𝔻(1, n^{ib}; x)² ≥ loglog x − (3/4)·loglog(|b|+3) − 5·logloglog(|b|+16) − C`,

with a uniform constant `C`.  The `1/4`-grounding content: over the range the `−(3/4)loglog`
correction (with `|b|` up to `x`) eats `3/4` of the leading `loglog x`, leaving `1/4 − o(1)`
(consumed by R1.4).  Large `|b| ≥ T₀` uses the H1.0 power-growth stone (`one_line_pow_growth`,
giving `log‖ζ‖ ≤ log C + (3/4)loglog|b| + 4logloglog|b|`), chained through the H0 λ-side bridge
`log_euler_osc_zeta_unconditional` (`∑cos ≤ log‖ζ‖ + K`) and the sharp real Mertens lower bound;
small `1 ≤ |b| < T₀` uses the closed-form `log_zeta_small_b_le`.  The `−5logloglog(|b|+16)` term
is the honest `o(loglog)` shape, carried IN-STATEMENT (S5 law). -/
theorem dist_one_floor_pow :
    ∃ C : ℝ, ∀ x b : ℝ, Real.exp 1 ≤ x → 1 ≤ |b| →
      Real.log (Real.log x)
          - (3 / 4) * Real.log (Real.log (|b| + 3))
          - 5 * Real.log (Real.log (Real.log (|b| + 16))) - C
        ≤ pretDistSq (fun _ => 1) (costwist b) x := by
  obtain ⟨Cζ, T₀, hCζpos, _hT0pos, hgrowth⟩ := one_line_pow_growth
  obtain ⟨K, hK⟩ := log_euler_osc_zeta_unconditional
  set Bhi : ℝ := max T₀ (Real.exp (Real.exp 100)) with hBhidef
  have hBhiT0 : T₀ ≤ Bhi := le_max_left _ _
  have hBhiexp : Real.exp (Real.exp 100) ≤ Bhi := le_max_right _ _
  have hBhi1 : (1 : ℝ) ≤ Bhi := by
    have h := Real.add_one_le_exp (Real.exp 100)
    have hp := Real.exp_pos (100 : ℝ)
    linarith [hBhiexp]
  refine ⟨max (12 + Real.log Cζ + K - Salt.Mertens.mertensM)
      (12 + Real.log (5 + 2 * Bhi) + K - Salt.Mertens.mertensM
        - (3 / 4) * Real.log (Real.log 4)
        - 5 * Real.log (Real.log (Real.log 17))), fun x b hx hb1 => ?_⟩
  -- common facts
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hx2 : (2 : ℝ) ≤ x := le_trans h2e hx
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have h12 : 12 / Real.log x ≤ 12 := by rw [div_le_iff₀ hLpos]; nlinarith [hlogx1]
  have hmert := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hx2)
  have hbr := hK x b hx
  have hbpos : (0 : ℝ) < |b| := by linarith [hb1]
  rw [pretDistSq_one_split b x]
  rcases le_or_gt Bhi |b| with hbig | hsmall
  · -- large `|b|`: H1.0 power-growth route
    have hbT0 : T₀ ≤ |b| := le_trans hBhiT0 hbig
    have hexp100b : Real.exp (Real.exp 100) ≤ |b| := le_trans hBhiexp hbig
    have hgrowthlog := log_zeta_growth_le hCζpos hgrowth hx hexp100b hbT0
    have hLb100 : Real.exp 100 ≤ Real.log |b| := by
      have h := Real.log_le_log (Real.exp_pos (Real.exp 100)) hexp100b
      rwa [Real.log_exp] at h
    have hexp100gt1 : (1 : ℝ) < Real.exp 100 := by
      have := Real.add_one_le_exp (100 : ℝ); linarith
    have hLbpos : (0 : ℝ) < Real.log |b| := by linarith
    have hℓb100 : (100 : ℝ) ≤ Real.log (Real.log |b|) := by
      have h := Real.log_le_log (Real.exp_pos 100) hLb100
      rwa [Real.log_exp] at h
    have hℓbpos : (0 : ℝ) < Real.log (Real.log |b|) := by linarith
    have hm1 : Real.log (Real.log |b|) ≤ Real.log (Real.log (|b| + 3)) :=
      Real.log_le_log hLbpos (Real.log_le_log hbpos (by linarith))
    have hℓb16ge : Real.log (Real.log |b|) ≤ Real.log (Real.log (|b| + 16)) :=
      Real.log_le_log hLbpos (Real.log_le_log hbpos (by linarith))
    have hm2 : Real.log (Real.log (Real.log |b|))
        ≤ Real.log (Real.log (Real.log (|b| + 16))) := Real.log_le_log hℓbpos hℓb16ge
    have hm3 : (0 : ℝ) ≤ Real.log (Real.log (Real.log (|b| + 16))) :=
      Real.log_nonneg (by linarith [hℓb100, hℓb16ge])
    linarith [hmert.1, hbr, h12, hgrowthlog, hm1, hm2, hm3,
      le_max_left (12 + Real.log Cζ + K - Salt.Mertens.mertensM)
        (12 + Real.log (5 + 2 * Bhi) + K - Salt.Mertens.mertensM
          - (3 / 4) * Real.log (Real.log 4)
          - 5 * Real.log (Real.log (Real.log 17)))]
  · -- small `|b|`: closed-form ζ bound route
    have hzsb := log_zeta_small_b_le hBhi1 hx hb1 (le_of_lt hsmall)
    have hlog4pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    have hm1 : Real.log (Real.log 4) ≤ Real.log (Real.log (|b| + 3)) :=
      Real.log_le_log hlog4pos (Real.log_le_log (by norm_num) (by linarith))
    have hexp1lt17 : Real.exp 1 < 17 := by have := Real.exp_one_lt_d9; linarith
    have hlog17gt1 : (1 : ℝ) < Real.log 17 := by
      have h := Real.log_lt_log (Real.exp_pos 1) hexp1lt17; rwa [Real.log_exp] at h
    have hℓ17pos : (0 : ℝ) < Real.log (Real.log 17) := Real.log_pos hlog17gt1
    have hℓb16ge17 : Real.log (Real.log 17) ≤ Real.log (Real.log (|b| + 16)) :=
      Real.log_le_log (by linarith) (Real.log_le_log (by norm_num) (by linarith))
    have hm2 : Real.log (Real.log (Real.log 17))
        ≤ Real.log (Real.log (Real.log (|b| + 16))) := Real.log_le_log hℓ17pos hℓb16ge17
    linarith [hmert.1, hbr, h12, hzsb, hm1, hm2,
      le_max_right (12 + Real.log Cζ + K - Salt.Mertens.mertensM)
        (12 + Real.log (5 + 2 * Bhi) + K - Salt.Mertens.mertensM
          - (3 / 4) * Real.log (Real.log 4)
          - 5 * Real.log (Real.log (Real.log 17)))]

/-! ## R1.4 — the capped `M_range` minimum + its `1/4 − o(1)` floor -/

/-- **The capped range minimum `M_range` (D4).**  `M_range(f; X, T)` is the infimum of
`𝔻(f, n^{it}; X)²` over the frequency range `(logX)^{1/45} ≤ |t| ≤ T + (logX)^{1/46}`,
intersected with the cap `|t| ≤ X`.  The `(logX)^{1/46}` widening keeps the ball/range
separation `1/46 < 1/45`; the `|t| ≤ X` cap is what makes the terminal `prop_A3'` `T`-uniform. -/
noncomputable def M_range (f : ℕ → ℂ) (X T : ℝ) : ℝ :=
  sInf ((fun t : ℝ => pretDistSq f (costwist t) X) ''
    {t : ℝ | (Real.log X) ^ (1 / 45 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 46 : ℝ) ∧ |t| ≤ X})

/-- **R1.4 — the `M_range(1)` floor (`Mrange_one_floor`).**  For `X ≥ e` and a nonempty range
(`(logX)^{1/45} ≤ T ≤ X`),

  `M_range(1; X, T) ≥ (1/4)·loglog X − (3/4)·(loglog(X+3) − loglog X) − 5·logloglog(X+16) − C`,

the `1/4 − o(1)` floor: the `−(3/4)loglog` correction (with `|t|` capped at `X`) eats `3/4` of
the leading `loglog X`.  The `−(3/4)(loglog(X+3) − loglog X)`, `−5logloglog(X+16)` and `−C`
corrections are all `o(loglog X)`.  Every `t` in the range obeys the per-`t` floor
`dist_one_floor_pow` (with `|t| ≤ X`), so the infimum inherits it. -/
theorem Mrange_one_floor :
    ∃ C : ℝ, ∀ X T : ℝ, Real.exp 1 ≤ X → (Real.log X) ^ (1 / 45 : ℝ) ≤ T → T ≤ X →
      (1 / 4) * Real.log (Real.log X)
          - (3 / 4) * (Real.log (Real.log (X + 3)) - Real.log (Real.log X))
          - 5 * Real.log (Real.log (Real.log (X + 16))) - C
        ≤ M_range (fun _ => 1) X T := by
  obtain ⟨C, hC⟩ := dist_one_floor_pow
  refine ⟨C, fun X T hX hT hTX => ?_⟩
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hLXpos : (0 : ℝ) < Real.log X := by linarith
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hr15_1 : (1 : ℝ) ≤ (Real.log X) ^ (1 / 45 : ℝ) := Real.one_le_rpow hlogX1 (by norm_num)
  have hexp1lt17 : Real.exp 1 < 17 := by have := Real.exp_one_lt_d9; linarith
  have hlog17gt1 : (1 : ℝ) < Real.log 17 := by
    have h := Real.log_lt_log (Real.exp_pos 1) hexp1lt17; rwa [Real.log_exp] at h
  -- the `t`-independent floor for every frequency in the (capped) range
  have hfloor : ∀ t : ℝ,
      (Real.log X) ^ (1 / 45 : ℝ) ≤ |t| ∧ |t| ≤ T + (Real.log X) ^ (1 / 46 : ℝ) ∧ |t| ≤ X →
      (1 / 4) * Real.log (Real.log X)
          - (3 / 4) * (Real.log (Real.log (X + 3)) - Real.log (Real.log X))
          - 5 * Real.log (Real.log (Real.log (X + 16))) - C
        ≤ pretDistSq (fun _ => 1) (costwist t) X := by
    rintro t ⟨htlo, _, htX⟩
    have ht1 : (1 : ℝ) ≤ |t| := le_trans hr15_1 htlo
    have hd := hC X t hX ht1
    have hm1 : Real.log (Real.log (|t| + 3)) ≤ Real.log (Real.log (X + 3)) :=
      Real.log_le_log (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) (by linarith))
    have hm2 : Real.log (Real.log (Real.log (|t| + 16)))
        ≤ Real.log (Real.log (Real.log (X + 16))) :=
      Real.log_le_log (Real.log_pos (by
          have : (1 : ℝ) < Real.log (|t| + 16) :=
            lt_of_lt_of_le hlog17gt1 (Real.log_le_log (by norm_num) (by linarith))
          linarith))
        (Real.log_le_log (Real.log_pos (by
          have : (1 : ℝ) < Real.log (|t| + 16) :=
            lt_of_lt_of_le hlog17gt1 (Real.log_le_log (by norm_num) (by linarith))
          linarith)) (Real.log_le_log (by linarith) (by linarith)))
    linarith [hd, hm1, hm2]
  -- the range is nonempty (witness `t = (logX)^{1/45}`)
  have hr15X : (Real.log X) ^ (1 / 45 : ℝ) ≤ X := by
    calc (Real.log X) ^ (1 / 45 : ℝ) ≤ (Real.log X) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlogX1 (by norm_num)
      _ = Real.log X := Real.rpow_one _
      _ ≤ X := by linarith [Real.log_le_sub_one_of_pos hXpos]
  have hne : ({t : ℝ | (Real.log X) ^ (1 / 45 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 46 : ℝ) ∧ |t| ≤ X}).Nonempty := by
    refine ⟨(Real.log X) ^ (1 / 45 : ℝ), ?_⟩
    have habs : |(Real.log X) ^ (1 / 45 : ℝ)| = (Real.log X) ^ (1 / 45 : ℝ) :=
      abs_of_nonneg (Real.rpow_nonneg hLXpos.le _)
    have h16nn : (0 : ℝ) ≤ (Real.log X) ^ (1 / 46 : ℝ) := Real.rpow_nonneg hLXpos.le _
    rw [Set.mem_setOf_eq, habs]
    exact ⟨le_refl _, by linarith [hT, h16nn], hr15X⟩
  unfold M_range
  refine le_csInf (hne.image _) ?_
  rintro v ⟨t, ht, rfl⟩
  exact hfloor t ht

end Salt.MR
