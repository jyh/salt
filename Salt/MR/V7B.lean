/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RiderTrace
import Salt.MR.RegisterCompose

/-!
# `V7B` — ⟦CS-THREAD⟧ the `e^{-100} ≤ cs` rider of `logChowla2_ineffective_v6`, DISCHARGED
and carried up the mint chain as a conjunct

`RegisterCompose.logChowla2_ineffective_v6` carries five inner hypotheses.  The first,
`Real.exp (-100) ≤ cs`, is a rider on a constant the theorem's own `∃`-prefix mints, and
`RiderTrace` already pinned in the kernel what that constant IS:

```
cs = min (min (c_vk / (2·K₄)) (c₀ / (2·Cκ))) (1/10) = 3.716·10^{-11}
```

against `e^{-100} = 3.72·10^{-44}` — **33 orders of room** (`cs_closed_form_ge_exp_neg_hundred`,
`RiderTrace.lean:132`).  What `RiderTrace` left open was the CARRY: the closed form is visible
only inside the mint's proof, and every hop above it exports `0 < cs` alone, so the floor could
not be read at the terminal.

This file closes that gap.  The route is the one `RiderTrace`'s closing note names — **conjunct
carry**, the same genre as `NumeralKq`'s `Kq ≤ 126848/10^8` twins — run over the two remaining
leaves and the nine hops above them:

```
§1  per_pair_contour_floored                       1/10^9 ≤ c₀     (off RiderTrace §4)
§2  halaszPrimesChiGated_of_price_floored          e^{-100} ≤ c    (THE MINT)
§3  halasz_primes_chi_pair_of_gates_bounded_cs     ⌉
    halaszPrimesChi_holds_gated_bounded_cs         │
    halaszPrimesChi_pointwise_of_gates_bounded_cs  │  six pass-throughs,
    usetGChi_window_meansq_gated_family_..._cs     │  bodies verbatim + one conjunct
    usetGChi_row_exit_perChi_perBlock_bounded_cs   │
    m4_rowChi_capstone_perBlock_bounded_cs         ⌋
§4  m4_hcap_at_door_perBlock_L_gk_bounded_khoist_cs
    m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs
    s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree   ⟵ the rider is CONSUMED here
    logChowla2_witnessed_scale_flat_..._cqhoist_csfree         ⟵ what a `v7` mint reads
```

⟦WHY THE CARRY IS THE ONLY ROUTE⟧ every statement in the chain is ANTITONE in `cs` (the
decay constant sits in `exp(−cs·log P/D₄)` at the bottom and in `420·L·… ≤ cs·(log Q)²` at
the top: shrinking `cs` weakens), so an `∃ cs, 0 < cs ∧ P cs` can always be re-witnessed at a
SMALLER `cs` and never at a larger one.  A LOWER bound therefore cannot be manufactured above
the mint by any monotonicity argument — it has to be exported from the leaves, which is what
§1–§2 do and what §3–§4 forward.

⟦WHERE THE RIDER DIES⟧ `S16ComposeV4.s16_capGate_supply_L_gk_sharpT0` spends `e^{-100} ≤ cs`
at exactly one field — `gate := s16_capGrid_gate_cs hcs …` (`S16Budget.lean:2298`).  §4's
`…_csfree` twins feed it the carried conjunct instead of an antecedent, so the hypothesis
leaves the statement.

**PURELY ADDITIVE.**  No landed declaration is touched; every twin sits beside its original,
and `logChowla2_ineffective_v6` is byte-untouched.  Minting `v7` off §4's terminal is a
separate node.
-/

namespace Salt.MR

/-! ## §0 — THE FLOOR, AT THE LEAVES' OWN VALUES -/

/-- **⟦THE `cs` FLOOR, GENERALISED TO THE LEAF BOUNDS⟧** `RiderTrace`'s
`cs_closed_form_ge_exp_neg_hundred` pins the floor at the two leaf LITERALS `c_vk = 1/10^8`
and `c₀ = 1/10^9`; the mint only ever knows the leaves through INEQUALITIES (`c_vk` is the
call site's literal, `c₀` is `per_pair_contour`'s existential).  Both slots are monotone, so
the pinned numeral carries. -/
theorem cs_floor_of_leaves {c_vk c₀ : ℝ} (h8 : 1 / 10 ^ 8 ≤ c_vk) (h9 : 1 / 10 ^ 9 ≤ c₀) :
    Real.exp (-100) ≤ min (min (c_vk / (2 * K₄)) (c₀ / (2 * Cκ))) (1 / 10) := by
  have hK : (0 : ℝ) < 2 * K₄ := by rw [K₄]; positivity
  have hC : (0 : ℝ) < 2 * Cκ := by rw [Cκ]; positivity
  have h1 : (1 / 10 ^ 8 : ℝ) / (2 * K₄) ≤ c_vk / (2 * K₄) := by
    rw [div_le_div_iff₀ hK hK]; nlinarith
  have h2 : (1 / 10 ^ 9 : ℝ) / (2 * Cκ) ≤ c₀ / (2 * Cκ) := by
    rw [div_le_div_iff₀ hC hC]; nlinarith
  exact le_trans cs_closed_form_ge_exp_neg_hundred (min_le_min (min_le_min h1 h2) le_rfl)

end Salt.MR

namespace Salt.MR

open scoped BigOperators
open Complex MeasureTheory Set ArithmeticFunction
open scoped LSeries.notation

/-! ## §1 — RUNG 4: the per-pair contour, `c₀`'s floor carried

`per_pair_contour` passes `shifted_edge_price_strip`'s `c_vk` through verbatim, so
`RiderTrace.shifted_edge_price_strip_bounded`'s `1/10^9 ≤ c_vk` survives the whole assembly.
Body verbatim from `HalaszPrimesCore.lean:2403`, with the one `obtain` re-pointed at the
bounded twin and the new conjunct threaded through the `refine`. -/

section V7BPerPair
open Complex Salt.SW Salt.Vk Metric intervalIntegral

set_option maxHeartbeats 12800000 in
-- The full contour assembly (four sub-bounds + orientation glue) is heavy; the disc-core-grade
-- 12.8M budget is warranted for the whole-theorem elaboration.
theorem per_pair_contour_floored :
    ∃ (c_vk C₁ C₂ C₃ T₀ : ℝ), 0 < c_vk ∧ 1 / 10 ^ 9 ≤ c_vk ∧
      0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 3 ≤ T₀ ∧
      ∀ (T P u : ℝ), T₀ ≤ T → 2 ≤ P → |u| ≤ 2 * T →
        ‖(∑' n, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
              - windowKernel P 1 u‖
          ≤ C₁ * P * Real.exp (-(c_vk / 2) * Real.log P
                / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                    * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)))
              * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                  * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ))
            + C₂ * P * Real.log P / T
            + C₃ * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                  * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) * P / T ^ 2 := by
  obtain ⟨c_vk, CE, T₀s, hc_vk0, hc_vk9, hCE0, hT₀s3, -, hmargin, hstrip⟩ :=
    shifted_edge_price_strip_bounded
  obtain ⟨C₀, hC₀0, hcline⟩ := sum_vonMangoldt_cline_bound
  -- constants
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set Kc : ℝ := (2 * 9 * (3 : ℝ) ^ ((Real.log 2)⁻¹) + 4) * Real.exp 1 with hKcdef
  have hKcpos : 0 < Kc := by rw [hKcdef]; positivity
  set Cζ : ℝ := 2 / c_vk + CE + 1 with hCζdef
  have hCζpos : 0 < Cζ := by rw [hCζdef]; positivity
  set CL : ℝ := 44 * Real.pi * (2 / c_vk + CE) with hCLdef
  have hCLpos : 0 < CL := by rw [hCLdef]; positivity
  set CH : ℝ := Cζ * Kc * (1 / Real.log 2 + 1 / 2) / 9 with hCHdef
  have hCHpos : 0 < CH := by rw [hCHdef]; positivity
  set CT : ℝ := 2 / 3 * Kc * (1 + C₀ / Real.log 2) with hCTdef
  have hCTpos : 0 < CT := by rw [hCTdef]; positivity
  refine ⟨c_vk, CL / (2 * Real.pi), CT / (2 * Real.pi), 2 * CH / (2 * Real.pi),
    max (max T₀s 3) (Real.exp (Real.exp (c_vk + 1))), hc_vk0, hc_vk9,
    div_pos hCLpos (by positivity), div_pos hCTpos (by positivity),
    div_pos (by positivity) (by positivity), ?_, ?_⟩
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  intro T P u hT hP hu
  -- unpack the T-threshold
  have hTT₀s : T₀s ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTexp : Real.exp (Real.exp (c_vk + 1)) ≤ T := le_trans (le_max_right _ _) hT
  have hT3 : (3 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hP0 : (0 : ℝ) < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  -- abbreviations D3, D4, w, σ₀, c, T'
  set LT : ℝ := Real.log (5 * T + 1) with hLTdef
  set ℓT : ℝ := Real.log LT with hℓTdef
  set D3 : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) with hD3def
  set D4 : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ) with hD4def
  have h5T1 : (1 : ℝ) < 5 * T + 1 := by linarith
  have hLTpos : 0 < LT := Real.log_pos h5T1
  -- loglog bound from the threshold
  have hTlogexp : Real.exp (c_vk + 1) ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp (c_vk + 1))]; exact Real.log_le_log (Real.exp_pos _) hTexp
  have hLTge : Real.exp (c_vk + 1) ≤ LT := by
    rw [hLTdef]; exact le_trans hTlogexp (Real.log_le_log hT0 (by linarith))
  have hℓTge : c_vk + 1 ≤ ℓT := by
    rw [hℓTdef, ← Real.log_exp (c_vk + 1)]; exact Real.log_le_log (Real.exp_pos _) hLTge
  have hℓT1 : (1 : ℝ) ≤ ℓT := by linarith
  have hℓTpos : 0 < ℓT := by linarith
  have hD3pos : 0 < D3 := by rw [hD3def]; positivity
  have hD4pos : 0 < D4 := by rw [hD4def]; positivity
  set w : ℝ := (c_vk / 2) / D3 with hwdef
  have hw0 : 0 < w := by rw [hwdef]; positivity
  -- D3 ≥ c_vk (so w ≤ 1/2, σ₀ ≥ 1/2)
  have hLT34ge : (1 : ℝ) ≤ LT ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow (by linarith [hLTge, Real.exp_pos (c_vk+1), Real.add_one_le_exp (c_vk+1)])
      (by norm_num)
  have hℓT3ge : c_vk ≤ ℓT ^ (3 : ℕ) := by
    have : c_vk + 1 ≤ ℓT ^ (3 : ℕ) := by
      calc c_vk + 1 ≤ ℓT := hℓTge
        _ = ℓT ^ 1 := (pow_one _).symm
        _ ≤ ℓT ^ (3 : ℕ) := pow_le_pow_right₀ hℓT1 (by norm_num)
    linarith
  have hD3gecvk : c_vk ≤ D3 := by
    rw [hD3def]
    calc c_vk ≤ ℓT ^ (3 : ℕ) := hℓT3ge
      _ = 1 * ℓT ^ (3 : ℕ) := (one_mul _).symm
      _ ≤ LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) := by
          apply mul_le_mul_of_nonneg_right hLT34ge (by positivity)
  have hwle : w ≤ 1 / 2 := by
    rw [hwdef, div_le_div_iff₀ hD3pos (by norm_num)]; nlinarith [hD3gecvk, hc_vk0]
  set σ₀ : ℝ := 1 - w with hσ₀def
  have hσ₀_eq : σ₀ = 1 - (c_vk / 2) / D3 := by rw [hσ₀def, hwdef]
  have hσ₀half : (1 : ℝ) / 2 ≤ σ₀ := by rw [hσ₀def]; linarith
  have hσ₀0 : 0 < σ₀ := by linarith
  have hσ₀1 : σ₀ < 1 := by rw [hσ₀def]; linarith
  have hσ₀xlb : 1 - (c_vk / 2) / D3 ≤ σ₀ := le_of_eq hσ₀_eq.symm
  have hσ₀xub : σ₀ ≤ 1 + (c_vk / 2) / D3 := by
    rw [hσ₀_eq]
    have hpos : (0 : ℝ) < (c_vk / 2) / D3 := by positivity
    linarith
  set c : ℝ := 1 + (Real.log P)⁻¹ with hcdef
  have hc1 : 1 < c := by rw [hcdef]; have := inv_pos.mpr hlogP; linarith
  have hcpos : 0 < c := by linarith
  set Tp : ℝ := 3 * T with hTpdef
  have hTp0 : 0 < Tp := by rw [hTpdef]; linarith
  have huTp : |u| < Tp := by rw [hTpdef]; linarith [hu, abs_nonneg u]
  -- the contour integrand F
  set F : ℂ → ℂ := fun s => (- logDeriv riemannZeta (s - (u : ℂ) * I)) * windowMellin P s with hFdef
  -- the rectangle corners
  set zc : ℂ := (σ₀ : ℂ) + ((-Tp : ℝ) : ℂ) * I with hzc
  set wc : ℂ := (c : ℂ) + (Tp : ℂ) * I with hwc
  have hzc_re : zc.re = σ₀ := by rw [hzc]; simp
  have hzc_im : zc.im = -Tp := by rw [hzc]; simp
  have hwc_re : wc.re = c := by rw [hwc]; simp
  have hwc_im : wc.im = Tp := by rw [hwc]; simp
  -- ζ zero-freeness on the shifted rectangle
  have hzf : ∀ s : ℂ, s ∈ closedRect zc wc → riemannZeta (s - (u : ℂ) * I) ≠ 0 := by
    intro s hs
    rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm,
      Set.uIcc_of_le (by linarith : σ₀ ≤ c),
      Set.uIcc_of_le (by linarith : -Tp ≤ Tp)] at hs
    obtain ⟨hsre, hsim⟩ := hs
    simp only [Set.mem_Icc] at hsre hsim
    have hshim : |(s - (u : ℂ) * I).im| ≤ 5 * T + 1 := by
      have him : (s - (u : ℂ) * I).im = s.im - u := by simp
      have hb := abs_le.mp hu
      rw [hTpdef] at hsim
      rw [him, abs_le]
      constructor <;> nlinarith [hsim.1, hsim.2, hb.1, hb.2]
    intro hz0
    by_cases h1 : (1 : ℝ) ≤ (s - (u : ℂ) * I).re
    · exact riemannZeta_ne_zero_of_one_le_re h1 hz0
    · have hsre' : (s - (u : ℂ) * I).re = s.re := by simp
      have hmr := hmargin T hTT₀s (s - (u : ℂ) * I) hz0 hshim
      rw [hsre'] at hmr
      have : s.re < 1 := by rw [hsre'] at h1; linarith [not_le.mp h1]
      have hlt : (c_vk / 2) / D3 < c_vk / D3 := by
        rw [div_lt_div_iff₀ hD3pos hD3pos]; nlinarith [hc_vk0, hD3pos]
      rw [← hD3def] at hmr
      have : σ₀ ≤ s.re := hsre.1
      rw [hσ₀def, hwdef] at this
      linarith [hmr, hlt]
  -- pole residue term
  have hpr0 := pole_residue_term (P := P) (σ₀ := σ₀) (c := c) (u := u) (T' := Tp)
    hP0 hσ₀0 hσ₀1 hc1 huTp hzf
  -- the four edges
  set BOT : ℂ := ∫ x in σ₀..c, F ((x : ℂ) + ((-Tp : ℝ) : ℂ) * I) with hBOTdef
  set TOP : ℂ := ∫ x in σ₀..c, F ((x : ℂ) + (Tp : ℂ) * I) with hTOPdef
  set RIGHT : ℂ := ∫ v in (-Tp)..Tp, F ((c : ℂ) + (v : ℂ) * I) with hRIGHTdef
  set LEFT : ℂ := ∫ v in (-Tp)..Tp, F ((σ₀ : ℂ) + (v : ℂ) * I) with hLEFTdef
  set wK : ℂ := windowKernel P 1 u with hwKdef
  have hwM : windowMellin P ((1 : ℂ) + (u : ℂ) * I) = wK := by
    rw [hwKdef, windowKernel_eq_windowMellin]; norm_num
  rw [hwM] at hpr0
  -- unfold rectBI to the four edges
  have hunf : rectBI zc wc F = BOT - TOP + I * RIGHT - I * LEFT := by
    rw [rectBI, hzc_re, hzc_im, hwc_re, hwc_im, hBOTdef, hTOPdef, hRIGHTdef, hLEFTdef]
  rw [hunf] at hpr0
  -- hpr0 : BOT - TOP + I * RIGHT - I * LEFT = 2 * ↑π * I * wK
  -- residue rearrangement
  have hrearr : RIGHT - (2 * (Real.pi : ℂ)) * wK = LEFT - I * (TOP - BOT) := by
    have key : I * (RIGHT - (2 * (Real.pi : ℂ)) * wK) = I * (LEFT - I * (TOP - BOT)) := by
      have expand : I * (LEFT - I * (TOP - BOT)) = I * LEFT + (TOP - BOT) := by
        have hII : I * (I * (TOP - BOT)) = -(TOP - BOT) := by
          rw [← mul_assoc, Complex.I_mul_I]; ring
        rw [mul_sub, hII]; ring
      rw [expand]; linear_combination hpr0
    exact mul_left_cancel₀ Complex.I_ne_zero key
  -- the REP bridge
  set a : ℕ → ℂ := fun n => (vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I) with hadef
  have ha0 : a 0 = 0 := by rw [hadef]; simp
  have hnorm_a : ∀ n : ℕ, ‖a n‖ = vonMangoldt n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ha0]; simp
    · rw [hadef]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      rw [← Complex.ofReal_natCast (n := n),
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
      simp
  have hsum : Summable (fun n => ‖a n‖ / (n : ℝ) ^ c) := by
    refine (summable_vonMangoldt_div_rpow hc1).congr (fun n => ?_)
    rw [hnorm_a n]
  -- Dirichlet ↔ ζ conversion (per t)
  have hdir : ∀ v : ℝ, (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
      = - logDeriv riemannZeta ((c : ℂ) + (v : ℂ) * I - (u : ℂ) * I) := by
    intro v
    set wv : ℂ := (c : ℂ) + (v : ℂ) * I - (u : ℂ) * I with hwvdef
    have hwvre : 1 < wv.re := by rw [hwvdef]; simp; linarith
    have hterm : ∀ n : ℕ, a n / (n : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)
        = LSeries.term ↗vonMangoldt wv n := by
      intro n
      rw [LSeries.term_def₀ (by simp) wv n]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [ha0]; simp
      · have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
        rw [hadef]; simp only; rw [mul_div_assoc]; congr 1
        rw [div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hne]
        congr 1; rw [hwvdef]; ring
    have hLSeries : (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)) = LSeries ↗vonMangoldt wv :=
      tsum_congr hterm
    rw [hLSeries, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hwvre, logDeriv_apply, neg_div]
  -- F(c+vI) equals the Dirichlet integrand
  have hFdir : ∀ v : ℝ, F ((c : ℂ) + (v : ℂ) * I)
      = (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)) * windowKernel P c v := by
    intro v
    rw [hFdef, hdir v, windowKernel_eq_windowMellin]
  -- the bridge
  have hbridge : (∑' n, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
      = (1 / (2 * Real.pi)) • ∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I) := by
    rw [show (∑' n, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
        = ∑' n, a n * (primeWindow P n : ℂ) from rfl,
      primeWindow_contour_rep a ha0 hP hcpos hsum]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    exact (hFdir v).symm
  -- truncation via rep_truncated
  have htrunc := rep_truncated a ha0 hP hcpos hTp0 hsum
  -- identify the two integrals in htrunc with ∫F and RIGHT
  have hI1 : (∫ t : ℝ, (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * windowKernel P c t)
      = ∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_)); exact (hFdir v).symm
  have hI2 : (∫ t in Set.Icc (-Tp) Tp,
        (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * windowKernel P c t) = RIGHT := by
    rw [hRIGHTdef, intervalIntegral.integral_of_le (by linarith : (-Tp : ℝ) ≤ Tp),
      ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc (fun v _ => ?_); exact (hFdir v).symm
  rw [hI1, hI2] at htrunc
  set TAILval : ℂ := (∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I)) - RIGHT with hTAILdef
  have hInt_split : (∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I)) = RIGHT + TAILval := by
    rw [hTAILdef]; ring
  -- htrunc : ‖TAILval‖ ≤ tailbound  (after rewriting)
  have hTAILnorm : ‖TAILval‖ ≤ (∑' n, ‖a n‖ / (n : ℝ) ^ c)
      * (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2)) * (2 / Tp) := by
    rw [hTAILdef]; exact htrunc
  -- SUB-BOUNDS (to be proven)
  have hLEFTb : ‖LEFT‖
      ≤ CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4 := by
    have hPσ0nn : (0 : ℝ) ≤ (P : ℝ) ^ σ₀ := Real.rpow_nonneg hP0.le σ₀
    have hPσ₀ : (P : ℝ) ^ σ₀ = P * Real.exp (-(c_vk / 2) * Real.log P / D3) := by
      rw [Real.rpow_def_of_pos hP0, hσ₀_eq,
        show Real.log P * (1 - (c_vk / 2) / D3)
          = Real.log P + (-(c_vk / 2) * Real.log P / D3) by ring, Real.exp_add]
      congr 1; exact Real.exp_log hP0
    set Bσ : ℝ := 1 / w + CE * D4 with hBσdef
    have hBσ0 : 0 ≤ Bσ := by rw [hBσdef]; positivity
    -- kernel bound
    have hkerL : ∀ v : ℝ, ‖windowMellin P ((σ₀ : ℂ) + (v : ℂ) * I)‖
        ≤ 22 * (P : ℝ) ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
      intro v
      rw [← windowKernel_eq_windowMellin]
      refine le_trans (norm_windowKernel_le hP hσ₀0 v) ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h3Pσ : ((3 : ℝ) * P) ^ (σ₀ + 1) = (3 : ℝ) ^ (σ₀ + 1) * (P : ℝ) ^ (σ₀ + 1) :=
        Real.mul_rpow (by norm_num) hP0.le
      have hPσ1 : (P : ℝ) ^ (σ₀ + 1) = (P : ℝ) ^ σ₀ * P := by
        rw [Real.rpow_add hP0, Real.rpow_one]
      have e1 : 2 * (2 * P + P) ^ (σ₀ + 1) / P = 2 * (3 : ℝ) ^ (σ₀ + 1) * (P : ℝ) ^ σ₀ := by
        rw [show 2 * P + P = 3 * P by ring, h3Pσ, hPσ1]; field_simp
      have e2 : 2 * (P / 2 + P / 2) ^ (σ₀ + 1) / (P / 2) = 4 * (P : ℝ) ^ σ₀ := by
        rw [show P / 2 + P / 2 = P by ring, hPσ1]; field_simp; ring
      rw [e1, e2]
      have h3 : (3 : ℝ) ^ (σ₀ + 1) ≤ 9 := by
        rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hσ₀1])
      nlinarith [h3, hPσ0nn]
    -- ζ'/ζ bound on the left edge
    have hzetaL : ∀ v : ℝ, v ∈ Set.Icc (-Tp) Tp →
        ‖(- logDeriv riemannZeta (((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I))‖ ≤ Bσ := by
      intro v hv
      simp only [Set.mem_Icc] at hv
      set s' : ℂ := ((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I with hs'def
      have hs'eq : s' = (σ₀ : ℂ) + ((v - u : ℝ) : ℂ) * I := by rw [hs'def]; push_cast; ring
      have hs're : s'.re = σ₀ := by rw [hs'eq]; simp
      have hvu5T : |v - u| ≤ 5 * T := by
        have hb := abs_le.mp hu; rw [hTpdef] at hv; rw [abs_le]; constructor <;> nlinarith [hv.1, hv.2, hb.1, hb.2]
      have hmem : ((σ₀ : ℂ) + (v : ℂ) * I) ∈ closedRect zc wc := by
        rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm,
          Set.uIcc_of_le (by linarith : σ₀ ≤ c), Set.uIcc_of_le (by linarith : -Tp ≤ Tp)]
        refine ⟨?_, ?_⟩
        · rw [Set.mem_Icc]; exact ⟨by simp, by simp; linarith [hσ₀1]⟩
        · rw [Set.mem_Icc]; simp; exact ⟨hv.1, hv.2⟩
      have hζs' : riemannZeta s' ≠ 0 := hzf _ hmem
      have hs'ne1 : s' ≠ 1 := by
        intro h; rw [h] at hs're; simp at hs're; linarith [hσ₀1]
      have hsplit : (- logDeriv riemannZeta s') = 1 / (s' - 1) - logDeriv Zc s' := by
        rw [logDeriv_zeta_eq hs'ne1 hζs']; ring
      rw [hsplit]
      refine le_trans (norm_sub_le _ _) ?_
      have hpole : ‖(1 : ℂ) / (s' - 1)‖ ≤ 1 / w := by
        rw [norm_div, norm_one]
        have hge : w ≤ ‖s' - 1‖ := by
          have h := Complex.abs_re_le_norm (s' - 1)
          rw [Complex.sub_re, hs're, Complex.one_re,
            show σ₀ - 1 = -w by rw [hσ₀def]; ring, abs_neg, abs_of_pos hw0] at h
          exact h
        exact one_div_le_one_div_of_le hw0 hge
      have hZc : ‖logDeriv Zc s'‖ ≤ CE * D4 := by
        rw [hs'eq]
        have h := hstrip T σ₀ (v - u) hTT₀s hσ₀xlb hσ₀xub hvu5T
        rw [← hLTdef, ← hℓTdef, ← hD4def] at h
        exact h
      rw [hBσdef]; linarith [hpole, hZc]
    -- pointwise ‖F‖ bound and the integral
    have hg_int : Integrable (fun v : ℝ => Bσ * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹) :=
      (Salt.SW.integrable_inv_c_sq_add_sq hσ₀0).const_mul _
    have hgnn : ∀ v : ℝ, (0 : ℝ) ≤ Bσ * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
      fun v => by positivity
    have hpt : ∀ v ∈ Set.Icc (-Tp) Tp,
        ‖F ((σ₀ : ℂ) + (v : ℂ) * I)‖ ≤ Bσ * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
      intro v hv
      rw [hFdef]
      simp only
      rw [norm_mul]
      calc ‖(- logDeriv riemannZeta (((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I))‖
              * ‖windowMellin P ((σ₀ : ℂ) + (v : ℂ) * I)‖
          ≤ Bσ * (22 * (P : ℝ) ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹) :=
            mul_le_mul (hzetaL v hv) (hkerL v) (norm_nonneg _) hBσ0
        _ = Bσ * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by ring
    have hFleft_ii : IntervalIntegrable (fun v : ℝ => F ((σ₀ : ℂ) + (v : ℂ) * I)) volume (-Tp) Tp := by
      have hζAON : AnalyticOnNhd ℂ riemannZeta (({(1 : ℂ)} : Set ℂ)ᶜ) := by
        apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
        intro z hz; exact (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
      apply ContinuousOn.intervalIntegrable
      intro v hv
      rw [Set.uIcc_of_le (by linarith : (-Tp : ℝ) ≤ Tp), Set.mem_Icc] at hv
      have hs0mem : ((σ₀ : ℂ) + (v : ℂ) * I) ∈ closedRect zc wc := by
        rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm,
          Set.uIcc_of_le (by linarith : σ₀ ≤ c), Set.uIcc_of_le (by linarith : (-Tp : ℝ) ≤ Tp)]
        refine ⟨?_, ?_⟩
        · rw [Set.mem_Icc]; exact ⟨by simp, by simp; linarith [hσ₀1]⟩
        · rw [Set.mem_Icc]; simp; exact hv
      have hs0re : ((σ₀ : ℂ) + (v : ℂ) * I).re = σ₀ := by simp
      have hζ : riemannZeta (((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I) ≠ 0 := hzf _ hs0mem
      have hne1 : ((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I ≠ 1 := by
        intro h; have hre := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, mul_zero, mul_one, sub_zero,
          add_zero] at hre
        linarith [hσ₀1]
      have hw_mem : (((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I) ∈ (({(1 : ℂ)} : Set ℂ)ᶜ) := by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hne1
      have hlogDζ : AnalyticAt ℂ (logDeriv riemannZeta) (((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I) := by
        rw [show logDeriv riemannZeta = fun z => deriv riemannZeta z / riemannZeta z from rfl]
        exact (hζAON.deriv _ hw_mem).div (hζAON _ hw_mem) hζ
      have hldζ : DifferentiableAt ℂ
          (fun z => - logDeriv riemannZeta (z - (u : ℂ) * I)) ((σ₀ : ℂ) + (v : ℂ) * I) := by
        have hg : DifferentiableAt ℂ (fun z : ℂ => z - (u : ℂ) * I) ((σ₀ : ℂ) + (v : ℂ) * I) := by
          fun_prop
        exact (DifferentiableAt.comp ((σ₀ : ℂ) + (v : ℂ) * I) (hlogDζ.differentiableAt) hg).neg
      have hWM : DifferentiableAt ℂ (windowMellin P) ((σ₀ : ℂ) + (v : ℂ) * I) := by
        apply windowMellin_differentiableAt hP0
        · intro h; rw [h] at hs0re; simp at hs0re; linarith [hσ₀0]
        · intro h; have hre : (((σ₀ : ℂ) + (v : ℂ) * I) + 1).re = 0 := by rw [h]; simp
          rw [Complex.add_re, Complex.one_re, hs0re] at hre; linarith [hσ₀0]
      have hFdiffC : DifferentiableAt ℂ F ((σ₀ : ℂ) + (v : ℂ) * I) := by
        rw [hFdef]; exact hldζ.mul hWM
      have hgdiff : DifferentiableAt ℝ (fun v : ℝ => (σ₀ : ℂ) + (v : ℂ) * I) v := by
        apply DifferentiableAt.const_add
        exact (Complex.ofRealCLM.differentiable.differentiableAt).mul_const I
      exact (((hFdiffC.restrictScalars ℝ).comp v hgdiff).continuousAt).continuousWithinAt
    calc ‖LEFT‖
        = ‖∫ v in (-Tp)..Tp, F ((σ₀ : ℂ) + (v : ℂ) * I)‖ := by rw [hLEFTdef]
      _ ≤ ∫ v in (-Tp)..Tp, ‖F ((σ₀ : ℂ) + (v : ℂ) * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ v in (-Tp)..Tp, Bσ * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
          intervalIntegral.integral_mono_on (by linarith) hFleft_ii.norm
            hg_int.intervalIntegrable hpt
      _ ≤ ∫ v : ℝ, Bσ * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
          rw [intervalIntegral.integral_of_le (by linarith : (-Tp : ℝ) ≤ Tp)]
          exact setIntegral_le_integral hg_int (Filter.Eventually.of_forall hgnn)
      _ = Bσ * (22 * (P : ℝ) ^ σ₀) * (Real.pi / σ₀) := by
          rw [MeasureTheory.integral_const_mul, Salt.SW.integral_inv_sq_add hσ₀0]
      _ ≤ CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4 := by
          have hD3leD4 : D3 ≤ D4 := by
            rw [hD3def, hD4def]
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hLTpos.le _)
            exact pow_le_pow_right₀ hℓT1 (by norm_num)
          have hBσle : Bσ ≤ (2 / c_vk + CE) * D4 := by
            rw [hBσdef, add_mul]
            have he : (1 : ℝ) / w = 2 * D3 / c_vk := by rw [hwdef, one_div_div]; ring
            have h1 : (1 : ℝ) / w ≤ 2 / c_vk * D4 := by
              rw [he, show (2 : ℝ) / c_vk * D4 = 2 * D4 / c_vk by ring,
                div_le_div_iff₀ hc_vk0 hc_vk0]
              nlinarith [hD3leD4, hc_vk0]
            linarith [h1]
          have hπσ₀ : Real.pi / σ₀ ≤ 2 * Real.pi := by
            rw [div_le_iff₀ hσ₀0]; nlinarith [Real.pi_pos, hσ₀half]
          have hexpnn : (0 : ℝ) ≤ Real.exp (-(c_vk / 2) * Real.log P / D3) := (Real.exp_pos _).le
          rw [hPσ₀]
          have hfac_nn : (0 : ℝ) ≤ 22 * (P * Real.exp (-(c_vk / 2) * Real.log P / D3)) := by
            apply mul_nonneg (by norm_num); exact mul_nonneg hP0.le hexpnn
          have hD4nn : (0 : ℝ) ≤ D4 := hD4pos.le
          have hCEfac_nn : (0 : ℝ) ≤ (2 / c_vk + CE) * D4 :=
            mul_nonneg (by positivity) hD4nn
          calc Bσ * (22 * (P * Real.exp (-(c_vk / 2) * Real.log P / D3))) * (Real.pi / σ₀)
              ≤ ((2 / c_vk + CE) * D4) * (22 * (P * Real.exp (-(c_vk / 2) * Real.log P / D3)))
                  * (2 * Real.pi) := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right hBσle hfac_nn) hπσ₀
                  (div_nonneg Real.pi_pos.le hσ₀0.le)
                  (mul_nonneg hCEfac_nn hfac_nn)
            _ = CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4 := by rw [hCLdef]; ring
  -- === HORIZONTAL sub-bound infrastructure ===
  have hD41 : (1 : ℝ) ≤ D4 := by
    rw [hD4def]; nlinarith [hLT34ge, one_le_pow₀ hℓT1 (n := 4), Real.rpow_nonneg hLTpos.le ((3:ℝ)/4)]
  have hTle : (1 : ℝ) ≤ T := by linarith [hT3]
  have hD3leD4' : D3 ≤ D4 := by
    rw [hD3def, hD4def]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hLTpos.le _)
    exact pow_le_pow_right₀ hℓT1 (by norm_num)
  have h1w_inv : (1 : ℝ) / w ≤ 2 / c_vk * D4 := by
    have he : (1 : ℝ) / w = 2 * D3 / c_vk := by rw [hwdef, one_div_div]; ring
    rw [he, show (2 : ℝ) / c_vk * D4 = 2 * D4 / c_vk by ring, div_le_div_iff₀ hc_vk0 hc_vk0]
    nlinarith [hD3leD4', hc_vk0]
  -- ζ'/ζ bound on both horizontals
  have hζhoriz : ∀ x τ : ℝ, σ₀ ≤ x → x ≤ c → |τ| = Tp →
      ‖(- logDeriv riemannZeta (((x : ℂ) + (τ : ℂ) * I) - (u : ℂ) * I))‖ ≤ Cζ * D4 := by
    intro x τ hxl hxu hτ
    set s' : ℂ := ((x : ℂ) + (τ : ℂ) * I) - (u : ℂ) * I with hs'def
    have hs'eq : s' = (x : ℂ) + ((τ - u : ℝ) : ℂ) * I := by rw [hs'def]; push_cast; ring
    have hs're : s'.re = x := by rw [hs'eq]; simp
    have hs'im : s'.im = τ - u := by rw [hs'eq]; simp
    have hτuge : (T : ℝ) ≤ |τ - u| := by
      have h1 : |τ| - |u| ≤ |τ - u| := abs_sub_abs_le_abs_sub τ u
      rw [hτ, hTpdef] at h1
      linarith [hu]
    have hτule : |τ - u| ≤ 5 * T := by
      have hb := abs_le.mp hu
      rw [abs_le]; rw [abs_eq (by linarith [hTp0] : (0:ℝ) ≤ Tp)] at hτ
      rcases hτ with h | h <;> rw [hTpdef] at h <;> constructor <;> nlinarith [hb.1, hb.2]
    by_cases hx1w : x ≤ 1 + w
    · have hmem : ((x : ℂ) + (τ : ℂ) * I) ∈ closedRect zc wc := by
        rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm,
          Set.uIcc_of_le (by linarith : σ₀ ≤ c), Set.uIcc_of_le (by linarith : -Tp ≤ Tp)]
        refine ⟨?_, ?_⟩
        · rw [Set.mem_Icc]; exact ⟨by simp; linarith, by simp; linarith⟩
        · rw [Set.mem_Icc]
          rw [abs_eq (by linarith [hTp0] : (0:ℝ) ≤ Tp)] at hτ
          rcases hτ with h | h <;> simp <;> constructor <;> linarith
      have hζs' : riemannZeta s' ≠ 0 := hzf _ hmem
      have hs'ne1 : s' ≠ 1 := by
        intro h; have := congrArg Complex.im h; rw [hs'im] at this; simp at this
        rw [this] at hτuge; simp at hτuge; linarith [hTle]
      have hsplit : (- logDeriv riemannZeta s') = 1 / (s' - 1) - logDeriv Zc s' := by
        rw [logDeriv_zeta_eq hs'ne1 hζs']; ring
      rw [hsplit]
      refine le_trans (norm_sub_le _ _) ?_
      have hpole : ‖(1 : ℂ) / (s' - 1)‖ ≤ 1 / T := by
        rw [norm_div, norm_one]
        have hge : T ≤ ‖s' - 1‖ := by
          have h := Complex.abs_im_le_norm (s' - 1)
          rw [Complex.sub_im, hs'im, Complex.one_im, sub_zero] at h
          linarith [h, hτuge, le_abs_self (τ - u), neg_abs_le (τ - u)]
        exact one_div_le_one_div_of_le hT0 hge
      have hZc : ‖logDeriv Zc s'‖ ≤ CE * D4 := by
        rw [hs'eq]
        have h := hstrip T x (τ - u) hTT₀s (le_trans hσ₀xlb hxl)
          (by rw [← hwdef]; exact hx1w) hτule
        rw [← hLTdef, ← hℓTdef, ← hD4def] at h
        exact h
      have hTinv : (1 : ℝ) / T ≤ D4 := le_trans (by rw [div_le_one hT0]; linarith [hTle]) hD41
      have hchain : ‖(1 : ℂ) / (s' - 1)‖ ≤ D4 := le_trans hpole hTinv
      have h2cD4 : (0 : ℝ) ≤ 2 / c_vk * D4 := mul_nonneg (by positivity) hD4pos.le
      rw [hCζdef, show (2 / c_vk + CE + 1) * D4 = 2 / c_vk * D4 + CE * D4 + D4 by ring]
      linarith [hchain, hZc, h2cD4]
    · rw [not_le] at hx1w
      have hx1 : (1 : ℝ) < x := by linarith [hw0]
      rw [norm_neg]
      have hcl := norm_logDeriv_zeta_cline_le hx1 (τ - u)
      have hmatch : ((x : ℂ) + ((τ - u : ℝ) : ℂ) * I) = s' := hs'eq.symm
      rw [hmatch] at hcl
      -- Σ Λ/n^x ≤ Σ Λ/n^{1+w}
      have h1w1 : (1 : ℝ) < 1 + w := by linarith [hw0]
      have hmono : (∑' n, vonMangoldt n / (n : ℝ) ^ x)
          ≤ ∑' n, vonMangoldt n / (n : ℝ) ^ (1 + w) := by
        refine (summable_vonMangoldt_div_rpow hx1).tsum_le_tsum (fun n => ?_)
          (summable_vonMangoldt_div_rpow h1w1)
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · have hle : (n : ℝ) ^ (1 + w) ≤ (n : ℝ) ^ x :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
          exact div_le_div_of_nonneg_left vonMangoldt_nonneg
            (Real.rpow_pos_of_pos (by exact_mod_cast hn) _) hle
      have hpole1w := sum_vonMangoldt_le_pole_add_Zc h1w1
      have hZc1w : ‖logDeriv Zc ((1 + w : ℝ) : ℂ)‖ ≤ CE * D4 := by
        have h := hstrip T (1 + w) 0 hTT₀s
          (by rw [← hwdef]; linarith [hw0]) (by rw [← hwdef])
          (by rw [abs_zero]; linarith [hT0])
        rw [← hLTdef, ← hℓTdef, ← hD4def] at h
        simpa using h
      have hpole1w2 : (1 : ℝ) / ((1 + w) - 1) = 1 / w := by ring_nf
      refine le_trans hcl ?_
      calc (∑' n, vonMangoldt n / (n : ℝ) ^ x)
          ≤ ∑' n, vonMangoldt n / (n : ℝ) ^ (1 + w) := hmono
        _ ≤ 1 / ((1 + w) - 1) + ‖logDeriv Zc ((1 + w : ℝ) : ℂ)‖ := hpole1w
        _ ≤ 1 / w + CE * D4 := by rw [hpole1w2]; linarith [hZc1w]
        _ ≤ 2 / c_vk * D4 + CE * D4 := by linarith [h1w_inv]
        _ ≤ Cζ * D4 := by rw [hCζdef]; nlinarith [hD41, hc_vk0, hCE0]
  -- kernel bound on both horizontals
  have hkerhoriz : ∀ x τ : ℝ, σ₀ ≤ x → x ≤ c → |τ| = Tp →
      ‖windowMellin P ((x : ℂ) + (τ : ℂ) * I)‖ ≤ Kc * P / (9 * T ^ 2) := by
    intro x τ hxl hxu hτ
    rw [← windowKernel_eq_windowMellin]
    have hx0 : 0 < x := by linarith [hσ₀0]
    refine le_trans (norm_windowKernel_le hP hx0 τ) ?_
    have hτ2 : τ ^ 2 = 9 * T ^ 2 := by
      have : |τ| ^ 2 = τ ^ 2 := sq_abs τ
      rw [← this, hτ, hTpdef]; ring
    have hCkx : 2 * (2 * P + P) ^ (x + 1) / P + 2 * (P / 2 + P / 2) ^ (x + 1) / (P / 2) ≤ Kc * P := by
      have h3Px : ((3 : ℝ) * P) ^ (x + 1) = (3 : ℝ) ^ (x + 1) * (P : ℝ) ^ (x + 1) :=
        Real.mul_rpow (by norm_num) hP0.le
      have hPx1 : (P : ℝ) ^ (x + 1) = (P : ℝ) ^ x * P := by rw [Real.rpow_add hP0, Real.rpow_one]
      have e1 : 2 * (2 * P + P) ^ (x + 1) / P = 2 * (3 : ℝ) ^ (x + 1) * (P : ℝ) ^ x := by
        rw [show 2 * P + P = 3 * P by ring, h3Px, hPx1]; field_simp
      have e2 : 2 * (P / 2 + P / 2) ^ (x + 1) / (P / 2) = 4 * (P : ℝ) ^ x := by
        rw [show P / 2 + P / 2 = P by ring, hPx1]; field_simp; ring
      rw [e1, e2]
      have hlog2P : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
      have hxc : x + 1 ≤ 2 + (Real.log 2)⁻¹ := by
        have : (Real.log P)⁻¹ ≤ (Real.log 2)⁻¹ := inv_anti₀ hlog2 hlog2P
        rw [hcdef] at hxu; linarith
      have h3x : (3 : ℝ) ^ (x + 1) ≤ 9 * (3 : ℝ) ^ ((Real.log 2)⁻¹) := by
        rw [show (9 : ℝ) * (3 : ℝ) ^ ((Real.log 2)⁻¹) = (3 : ℝ) ^ (2 + (Real.log 2)⁻¹) by
          rw [Real.rpow_add (by norm_num),
            show (3 : ℝ) ^ (2 : ℝ) = 9 by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hxc
      have hPxc : (P : ℝ) ^ x ≤ Real.exp 1 * P := by
        have hPc : (P : ℝ) ^ c = Real.exp 1 * P := by
          rw [hcdef, Real.rpow_add hP0, Real.rpow_one, mul_comm]; congr 1
          rw [Real.rpow_def_of_pos hP0, mul_inv_cancel₀ hlogP.ne']
        calc (P : ℝ) ^ x ≤ (P : ℝ) ^ c := Real.rpow_le_rpow_of_exponent_le (by linarith [hP]) hxu
          _ = Real.exp 1 * P := hPc
      have hPxnn : (0 : ℝ) ≤ (P : ℝ) ^ x := Real.rpow_nonneg hP0.le x
      rw [hKcdef]
      nlinarith [h3x, hPxc, hPxnn, Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) ((Real.log 2)⁻¹),
        mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) ((Real.log 2)⁻¹)) hP0.le]
    have hinv : (x ^ 2 + τ ^ 2)⁻¹ ≤ (9 * T ^ 2)⁻¹ := by
      rw [hτ2]; apply inv_anti₀ (by positivity); nlinarith [sq_nonneg x]
    calc (2 * (2 * P + P) ^ (x + 1) / P + 2 * (P / 2 + P / 2) ^ (x + 1) / (P / 2))
            * (x ^ 2 + τ ^ 2)⁻¹
        ≤ (Kc * P) * (9 * T ^ 2)⁻¹ :=
          mul_le_mul hCkx hinv (by positivity) (by positivity)
      _ = Kc * P / (9 * T ^ 2) := by ring
  -- pointwise F bound on the horizontals
  have hFhoriz : ∀ τ : ℝ, |τ| = Tp → ∀ x ∈ Set.uIoc σ₀ c,
      ‖F ((x : ℂ) + (τ : ℂ) * I)‖ ≤ Cζ * D4 * (Kc * P / (9 * T ^ 2)) := by
    intro τ hτ x hx
    rw [Set.uIoc_of_le (by linarith : σ₀ ≤ c), Set.mem_Ioc] at hx
    rw [hFdef]; simp only; rw [norm_mul]
    exact mul_le_mul (hζhoriz x τ (le_of_lt hx.1) hx.2 hτ) (hkerhoriz x τ (le_of_lt hx.1) hx.2 hτ)
      (norm_nonneg _) (by positivity)
  -- c − σ₀ width
  have hcσ₀w : c - σ₀ ≤ 1 / Real.log 2 + 1 / 2 := by
    have hlogPinv : (Real.log P)⁻¹ ≤ (Real.log 2)⁻¹ :=
      inv_anti₀ hlog2 (Real.log_le_log (by norm_num) hP)
    rw [hcdef, hσ₀def, one_div]; linarith [hlogPinv, hwle]
  have hCbnd_nn : (0 : ℝ) ≤ Cζ * D4 * (Kc * P / (9 * T ^ 2)) := by positivity
  have hTOPb : ‖TOP‖ ≤ CH * D4 * P / T ^ 2 := by
    rw [hTOPdef]
    have hτ : |Tp| = Tp := abs_of_pos hTp0
    calc ‖∫ x in σ₀..c, F ((x : ℂ) + (Tp : ℂ) * I)‖
        ≤ (Cζ * D4 * (Kc * P / (9 * T ^ 2))) * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hFhoriz Tp hτ)
      _ ≤ (Cζ * D4 * (Kc * P / (9 * T ^ 2))) * (1 / Real.log 2 + 1 / 2) := by
          apply mul_le_mul_of_nonneg_left _ hCbnd_nn
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c - σ₀)]; exact hcσ₀w
      _ = CH * D4 * P / T ^ 2 := by rw [hCHdef]; field_simp
  have hBOTb : ‖BOT‖ ≤ CH * D4 * P / T ^ 2 := by
    rw [hBOTdef]
    have hτ : |(-Tp : ℝ)| = Tp := by rw [abs_neg]; exact abs_of_pos hTp0
    calc ‖∫ x in σ₀..c, F ((x : ℂ) + ((-Tp : ℝ) : ℂ) * I)‖
        ≤ (Cζ * D4 * (Kc * P / (9 * T ^ 2))) * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hFhoriz (-Tp) hτ)
      _ ≤ (Cζ * D4 * (Kc * P / (9 * T ^ 2))) * (1 / Real.log 2 + 1 / 2) := by
          apply mul_le_mul_of_nonneg_left _ hCbnd_nn
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c - σ₀)]; exact hcσ₀w
      _ = CH * D4 * P / T ^ 2 := by rw [hCHdef]; field_simp
  have hTAILb : ‖TAILval‖ ≤ CT * P * Real.log P / T := by
    have hsuma : (∑' n, ‖a n‖ / (n : ℝ) ^ c) ≤ Real.log P + C₀ := by
      have hcong : (∑' n, ‖a n‖ / (n : ℝ) ^ c) = ∑' n, vonMangoldt n / (n : ℝ) ^ c :=
        tsum_congr (fun n => by rw [hnorm_a n])
      rw [hcong, hcdef]; exact hcline hP
    have hsuma0 : (0 : ℝ) ≤ ∑' n, ‖a n‖ / (n : ℝ) ^ c := tsum_nonneg (fun n => by positivity)
    have hCk : (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2)) ≤ Kc * P := by
      rw [hcdef, hKcdef]; exact truncKernel_const_le hP
    have hCk0 : (0 : ℝ) ≤ 2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2) := by
      have : (0 : ℝ) < P := hP0; positivity
    have h2Tp : (2 : ℝ) / Tp = 2 / (3 * T) := by rw [hTpdef]
    have hstep : (∑' n, ‖a n‖ / (n : ℝ) ^ c)
          * (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2)) * (2 / Tp)
        ≤ (Real.log P + C₀) * (Kc * P) * (2 / (3 * T)) := by
      rw [h2Tp]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hsuma hCk hCk0 (by linarith [hlogP, hC₀0])) (by positivity)
    have hkeylog : Real.log P + C₀ ≤ (1 + C₀ / Real.log 2) * Real.log P := by
      have hlog2P : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
      have hh : C₀ * Real.log 2 ≤ C₀ * Real.log P := by nlinarith [hC₀0, hlog2P]
      rw [add_mul, one_mul, div_mul_eq_mul_div]
      have : C₀ ≤ C₀ * Real.log P / Real.log 2 := by rw [le_div_iff₀ hlog2]; linarith [hh]
      linarith
    refine le_trans hTAILnorm (le_trans hstep ?_)
    calc (Real.log P + C₀) * (Kc * P) * (2 / (3 * T))
        ≤ ((1 + C₀ / Real.log 2) * Real.log P) * (Kc * P) * (2 / (3 * T)) := by
          apply mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hkeylog (by positivity)) (by positivity)
      _ = CT * P * Real.log P / T := by rw [hCTdef]; field_simp
  -- assemble
  rw [hbridge, hInt_split]
  have hval : (1 / (2 * Real.pi)) • (RIGHT + TAILval) - wK
      = (1 / (2 * Real.pi) : ℝ) • (LEFT - I * (TOP - BOT) + TAILval) := by
    rw [Complex.real_smul, Complex.real_smul]
    have hrw : wK = (↑(1 / (2 * Real.pi)) : ℂ) * ((2 * (Real.pi : ℂ)) * wK) := by
      have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast; field_simp
    rw [hrw, ← mul_sub]
    congr 1
    rw [show (RIGHT + TAILval) - (2 * (Real.pi : ℂ)) * wK
        = (RIGHT - (2 * (Real.pi : ℂ)) * wK) + TAILval by ring, hrearr]
  rw [hval, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have htri : ‖LEFT - I * (TOP - BOT) + TAILval‖ ≤ ‖LEFT‖ + ‖TOP‖ + ‖BOT‖ + ‖TAILval‖ := by
    calc ‖LEFT - I * (TOP - BOT) + TAILval‖
        ≤ ‖LEFT - I * (TOP - BOT)‖ + ‖TAILval‖ := norm_add_le _ _
      _ ≤ (‖LEFT‖ + ‖I * (TOP - BOT)‖) + ‖TAILval‖ := by linarith [norm_sub_le LEFT (I * (TOP - BOT))]
      _ = ‖LEFT‖ + ‖TOP - BOT‖ + ‖TAILval‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ‖LEFT‖ + ‖TOP‖ + ‖BOT‖ + ‖TAILval‖ := by linarith [norm_sub_le TOP BOT]
  -- final arithmetic
  have hN : ‖LEFT - I * (TOP - BOT) + TAILval‖
      ≤ CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4
        + CT * P * Real.log P / T + 2 * CH * D4 * P / T ^ 2 := by
    calc ‖LEFT - I * (TOP - BOT) + TAILval‖
        ≤ ‖LEFT‖ + ‖TOP‖ + ‖BOT‖ + ‖TAILval‖ := htri
      _ ≤ (CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4)
            + (CH * D4 * P / T ^ 2) + (CH * D4 * P / T ^ 2) + (CT * P * Real.log P / T) := by
          linarith [hLEFTb, hTOPb, hBOTb, hTAILb]
      _ = CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4
            + CT * P * Real.log P / T + 2 * CH * D4 * P / T ^ 2 := by ring
  calc (1 / (2 * Real.pi)) * ‖LEFT - I * (TOP - BOT) + TAILval‖
      ≤ (1 / (2 * Real.pi)) * (CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4
          + CT * P * Real.log P / T + 2 * CH * D4 * P / T ^ 2) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ = CL / (2 * Real.pi) * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4
          + CT / (2 * Real.pi) * P * Real.log P / T
          + 2 * CH / (2 * Real.pi) * D4 * P / T ^ 2 := by ring

end V7BPerPair

end Salt.MR

namespace Salt.MR

open scoped BigOperators
open Complex MeasureTheory Set ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

/-! ## §2 — THE MINT, WITH THE FLOOR EXPORTED

`halaszPrimesChiGated_of_price` is where `cs` is born, as
`min (min (c_vk/(2·K₄)) (c₀/(2·Cκ))) (1/10)`.  This twin asks the call site's own literal
`1/10^8 ≤ c_vk` instead of bare positivity, reads `1/10^9 ≤ c₀` off §1, and exports the floor.
Body verbatim from `PortAssembly.lean:802`. -/

set_option maxHeartbeats 6400000 in
-- The assembly threads seven absorption bounds against one `∃`-packaged constant; the
-- elaborator needs headroom past the default — and the twin re-elaborates the whole packaged
-- statement with one extra conjunct, so it needs DOUBLE the landed declaration's 3.2M.
/-- **A1 — THE PAIR DUAL, ASSEMBLED.**  `HalaszPrimesChiGated` from the twisted edge price
(`TwistedWindowPriceGated`, at any admissible constants) and the landed untwisted per-pair
price (`per_pair_contour`).  This is stone C's residue discharged: the socket's diagonal term
is `P`, not `φ(q)·P`.

The decay constant is `c = min(c_vk/(2K₄), c₀/(2Cκ), 1/10)`: the first two match the two
prices' contour depths against the socket's `D₄(qT)` (via `D4_5T1_le_D4` and `D3_5T1_le`,
then `logDn_mono` for `D₄(T) ≤ D₄(qT)`), the third is what makes `1/T ≤ exp(−c log P/D₄(qT))`
at `P ≤ T^10`.  The `(log qT)²` factor absorbs `D₅(5T+1)` and `D₄(5T+1)` (`D5_5T1_le`,
`D4_5T1_le`) and — through `√P ≤ P·exp(−c log P/D₄(qT))` — the Euler debit. -/
theorem halaszPrimesChiGated_of_price_floored {c_vk C₁ C₂ C₃ T₀e : ℝ}
    (hc_vk8 : 1 / 10 ^ 8 ≤ c_vk) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃)
    (hT₀e : Real.exp (Real.exp 100) ≤ T₀e)
    (hprice : TwistedWindowPriceGated c_vk C₁ C₂ C₃ T₀e) :
    ∃ C c T₀ : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (-100) ≤ c ∧ 3 ≤ T₀ ∧
      HalaszPrimesChiGated c_vk C c T₀ := by
  have hc_vk : 0 < c_vk := lt_of_lt_of_le (by norm_num) hc_vk8
  obtain ⟨c₀, E₁, E₂, E₃, T₀z, hc₀, hc₀9, hE₁, hE₂, hE₃, hT₀z, hpp⟩ :=
    per_pair_contour_floored
  have hK₂0 : 0 < K₂ := by rw [K₂]; positivity
  have hK₄0 : 0 < K₄ := by rw [K₄]; positivity
  have hK₅0 : 0 < K₅ := by rw [K₅]; positivity
  have hCκ0 : 0 < Cκ := by rw [Cκ]; positivity
  set c : ℝ := min (min (c_vk / (2 * K₄)) (c₀ / (2 * Cκ))) (1 / 10) with hcdef
  have hc0 : 0 < c := by
    rw [hcdef]
    exact lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have hcK₄ : c * K₄ ≤ c_vk / 2 := by
    have h : c ≤ c_vk / (2 * K₄) := by
      rw [hcdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 : c * (2 * K₄) ≤ c_vk := (le_div_iff₀ (by positivity)).mp h
    linarith
  have hcCκ : c * Cκ ≤ c₀ / 2 := by
    have h : c ≤ c₀ / (2 * Cκ) := by
      rw [hcdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have h2 : c * (2 * Cκ) ≤ c₀ := (le_div_iff₀ (by positivity)).mp h
    linarith
  have hc10 : c ≤ 1 / 10 := by rw [hcdef]; exact min_le_right _ _
  set Cε : ℝ := C₁ * K₅ + C₂ * 10 + C₃ * K₅ + E₁ * K₂ + E₂ * 10 + E₃ * K₂ + 9 with hCεdef
  have hCε0 : 0 < Cε := by rw [hCεdef]; positivity
  have hcfloor : Real.exp (-100) ≤ c := by
    rw [hcdef]; exact cs_floor_of_leaves hc_vk8 hc₀9
  refine ⟨44 * Real.pi + Cε, c, max T₀e T₀z, by positivity, hc0, hcfloor,
    le_trans hT₀z (le_max_right _ _), ?_⟩
  intro q hq T P hT hP hPT10 hgate hregion ℰ hws hsub S hS a
  -- ⟦the scales⟧
  have hT₀e' : T₀e ≤ T := le_trans (le_max_left _ _) hT
  have hT₀z' : T₀z ≤ T := le_trans (le_max_right _ _) hT
  have hE101 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hTE : Real.exp (Real.exp 100) ≤ T := le_trans hT₀e hT₀e'
  have hT6 : (6 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hP0 : (0 : ℝ) < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hLT100 : Real.exp 100 ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp 100)]; exact Real.log_le_log (Real.exp_pos _) hTE
  have hLT1 : (1 : ℝ) ≤ Real.log T := by linarith
  have hllT100 : (100 : ℝ) ≤ Real.log (Real.log T) := by
    rw [← Real.log_exp 100]; exact Real.log_le_log (Real.exp_pos _) hLT100
  have hllT1 : (1 : ℝ) ≤ Real.log (Real.log T) := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqT : T ≤ (q : ℝ) * T := by nlinarith
  have hlogq0 : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hlogP10 : Real.log P ≤ 10 * Real.log T := by
    have h := Real.log_le_log (by positivity) hPT10
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  -- ⟦the three prices, pulled BEFORE the abbreviations so that `set` folds them⟧
  have hedgeB : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ u : ℝ, |u| ≤ 2 * T →
      ‖∑' n : ℕ, ((ψ (n : ZMod q) * (vonMangoldt n : ℂ)) * (n : ℂ) ^ ((u : ℂ) * I))
          * (primeWindow P n : ℂ)‖
        ≤ C₁ * P * Real.exp (-(c_vk / 2) * Real.log P
                / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                    * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)))
              * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                  * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ))
          + C₂ * P * Real.log P / T
          + C₃ * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ)) * P / T ^ 2 :=
    fun ψ hψ1 u hu => hprice q ψ hψ1 T P u hT₀e' hP hu hgate (hregion ψ hψ1)
  have hppB : ∀ u : ℝ, |u| ≤ 2 * T →
      ‖(∑' n : ℕ, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
            - windowKernel P 1 u‖
        ≤ E₁ * P * Real.exp (-(c₀ / 2) * Real.log P
                / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                    * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)))
              * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                  * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ))
          + E₂ * P * Real.log P / T
          + E₃ * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) * P / T ^ 2 :=
    fun u hu => hpp T P u hT₀z' hP hu
  have hdebitB : ∀ u : ℝ,
      ‖(∑' n : ℕ, (((1 : DirichletCharacter ℂ q) (n : ZMod q) * (vonMangoldt n : ℂ))
              * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
          - (∑' n : ℕ, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I))
              * (primeWindow P n : ℂ))‖
        ≤ ((Nat.log 2 ⌊3 * P⌋₊ : ℝ) + 1) * Real.log q :=
    fun u => norm_principal_sub_untwisted_le hP u
  -- ⟦the four log-scale abbreviations⟧
  set Lg : ℝ := Real.log (5 * T + 1) with hLgdef
  set ℓ : ℝ := Real.log (Real.log (5 * T + 1)) with hℓdef
  set Lq : ℝ := Real.log ((q : ℝ) * T) with hLqdef
  set ℓq : ℝ := Real.log (Real.log ((q : ℝ) * T)) with hℓqdef
  have hLqT : Real.log T ≤ Lq := by rw [hLqdef]; exact Real.log_le_log hT0 hqT
  have hLq1 : (1 : ℝ) ≤ Lq := by linarith
  have hLqsq : Lq ≤ Lq ^ 2 := by nlinarith
  have hLg100 : Real.exp 100 ≤ Lg := by
    rw [hLgdef]
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLg1 : (1 : ℝ) ≤ Lg := by linarith
  have hℓ100 : (100 : ℝ) ≤ ℓ := by
    rw [hℓdef, ← hLgdef, ← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLg100
  set D4g : ℝ := Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) with hD4gdef
  set D5g : ℝ := Lg ^ ((3 : ℝ) / 4) * ℓ ^ (5 : ℕ) with hD5gdef
  set D3g : ℝ := Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ) with hD3gdef
  set D4q : ℝ := Lq ^ ((3 : ℝ) / 4) * ℓq ^ (4 : ℕ) with hD4qdef
  have hLgrp : (0 : ℝ) < Lg ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
  have hD4gpos : (0 : ℝ) < D4g := by rw [hD4gdef]; positivity
  have hD5gpos : (0 : ℝ) < D5g := by rw [hD5gdef]; positivity
  have hD3gpos : (0 : ℝ) < D3g := by rw [hD3gdef]; positivity
  have hD4T1 : (1 : ℝ) ≤ (Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ) := by
    have h1 : (1 : ℝ) ≤ (Real.log T) ^ ((3 : ℝ) / 4) := Real.one_le_rpow hLT1 (by norm_num)
    have h2 : (1 : ℝ) ≤ (Real.log (Real.log T)) ^ (4 : ℕ) := one_le_pow₀ hllT1
    nlinarith
  have hD4Tq : (Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ) ≤ D4q := by
    rw [hD4qdef, hLqdef, hℓqdef]
    exact logDn_mono 4 (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ T) hqT
  have hD4q1 : (1 : ℝ) ≤ D4q := le_trans hD4T1 hD4Tq
  have hD4qpos : (0 : ℝ) < D4q := by linarith
  -- ⟦the decay factor⟧
  set expc : ℝ := Real.exp (-c * Real.log P / D4q) with hexpcdef
  have hexpc0 : (0 : ℝ) < expc := by rw [hexpcdef]; exact Real.exp_pos _
  -- ⟦the four decay/height comparisons⟧
  have hcmp_edge : Real.exp (-(c_vk / 2) * Real.log P / D4g) ≤ expc := by
    rw [hexpcdef]
    refine Real.exp_le_exp.mpr ?_
    rw [neg_mul, neg_div, neg_mul, neg_div, neg_le_neg_iff, div_le_div_iff₀ hD4qpos hD4gpos]
    have h1 : D4g ≤ K₄ * D4q := by
      rw [hD4gdef, hLgdef, hℓdef]
      refine le_trans (D4_5T1_le_D4 hT6 hLT1 hllT1) ?_
      exact mul_le_mul_of_nonneg_left hD4Tq hK₄0.le
    have h2 : c * Real.log P * D4g ≤ c * Real.log P * (K₄ * D4q) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : c * K₄ * (Real.log P * D4q) ≤ (c_vk / 2) * (Real.log P * D4q) :=
      mul_le_mul_of_nonneg_right hcK₄ (by positivity)
    nlinarith [h2, h3]
  have hcmp_pp : Real.exp (-(c₀ / 2) * Real.log P / D3g) ≤ expc := by
    rw [hexpcdef]
    refine Real.exp_le_exp.mpr ?_
    rw [neg_mul, neg_div, neg_mul, neg_div, neg_le_neg_iff, div_le_div_iff₀ hD4qpos hD3gpos]
    have h1 : D3g ≤ Cκ * D4q := by
      rw [hD3gdef, hLgdef, hℓdef]
      refine le_trans (D3_5T1_le hT6 hLT1 hllT1) ?_
      exact mul_le_mul_of_nonneg_left hD4Tq hCκ0.le
    have h2 : c * Real.log P * D3g ≤ c * Real.log P * (Cκ * D4q) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : c * Cκ * (Real.log P * D4q) ≤ (c₀ / 2) * (Real.log P * D4q) :=
      mul_le_mul_of_nonneg_right hcCκ (by positivity)
    nlinarith [h2, h3]
  have hD5Lq : D5g ≤ K₅ * Lq ^ 2 := by
    have h1 : D5g ≤ K₅ * (Real.log T) ^ 2 := by
      rw [hD5gdef, hLgdef, hℓdef]; exact D5_5T1_le hT6 hLT1 hllT1
    have h2 : K₅ * (Real.log T) ^ 2 ≤ K₅ * Lq ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hK₅0.le
      nlinarith [hLqT, hLT1]
    linarith
  have hD4Lq : D4g ≤ K₂ * Lq ^ 2 := by
    have h1 : D4g ≤ K₂ * (Real.log T) ^ 2 := by
      rw [hD4gdef, hLgdef, hℓdef]; exact D4_5T1_le hT6 hLT1 hllT1
    have h2 : K₂ * (Real.log T) ^ 2 ≤ K₂ * Lq ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hK₂0.le
      nlinarith [hLqT, hLT1]
    linarith
  have hlogPLq : Real.log P ≤ 10 * Lq ^ 2 := by nlinarith [hlogP10, hLqT, hLqsq]
  have hTinv : 1 / T ≤ expc := by
    rw [hexpcdef, show (1 : ℝ) / T = Real.exp (-Real.log T) by
      rw [Real.exp_neg, Real.exp_log hT0, one_div]]
    refine Real.exp_le_exp.mpr ?_
    rw [neg_mul, neg_div, neg_le_neg_iff, div_le_iff₀ hD4qpos]
    have s1 : c * Real.log P ≤ (1 / 10) * Real.log P :=
      mul_le_mul_of_nonneg_right hc10 hlogP.le
    have s2 : (1 / 10 : ℝ) * Real.log P ≤ Real.log T := by linarith
    have s3 : Real.log T ≤ Real.log T * D4q := by nlinarith [hD4q1, hLT1]
    linarith
  have hT2inv : 1 / T ^ 2 ≤ expc := by
    have h : 1 / T ^ 2 ≤ 1 / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]; nlinarith
    linarith [hTinv]
  have hsqrtP : Real.sqrt P ≤ P * expc := by
    have hs : Real.sqrt P = Real.exp (Real.log P / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hP0]
      congr 1; ring
    have hPe : P * expc = Real.exp (Real.log P + -c * Real.log P / D4q) := by
      rw [Real.exp_add, Real.exp_log hP0, hexpcdef]
    rw [hs, hPe]
    refine Real.exp_le_exp.mpr ?_
    have h1 : c * Real.log P / D4q ≤ Real.log P / 2 := by
      rw [div_le_div_iff₀ hD4qpos (by norm_num : (0:ℝ) < 2)]
      have s1 : c * Real.log P * 2 ≤ (1 / 5) * Real.log P := by nlinarith [hc10, hlogP]
      have s2 : (1 / 5 : ℝ) * Real.log P ≤ Real.log P * D4q := by nlinarith [hD4q1, hlogP]
      linarith
    have h2 : -c * Real.log P / D4q = -(c * Real.log P / D4q) := by ring
    rw [h2]
    linarith
  -- ⟦the single error level `ε`⟧
  set εE : ℝ := C₁ * P * Real.exp (-(c_vk / 2) * Real.log P / D4g) * D5g
      + C₂ * P * Real.log P / T + C₃ * D5g * P / T ^ 2 with hεEdef
  set εZ : ℝ := E₁ * P * Real.exp (-(c₀ / 2) * Real.log P / D3g) * D4g
      + E₂ * P * Real.log P / T + E₃ * D4g * P / T ^ 2 with hεZdef
  set εD : ℝ := ((Nat.log 2 ⌊3 * P⌋₊ : ℝ) + 1) * Real.log q with hεDdef
  have hεE0 : (0 : ℝ) ≤ εE := by
    rw [hεEdef]
    have h1 : (0:ℝ) ≤ C₁ * P * Real.exp (-(c_vk / 2) * Real.log P / D4g) * D5g := by positivity
    have h2 : (0:ℝ) ≤ C₂ * P * Real.log P / T := by positivity
    have h3 : (0:ℝ) ≤ C₃ * D5g * P / T ^ 2 := by positivity
    linarith
  have hεZ0 : (0 : ℝ) ≤ εZ := by
    rw [hεZdef]
    have h1 : (0:ℝ) ≤ E₁ * P * Real.exp (-(c₀ / 2) * Real.log P / D3g) * D4g := by positivity
    have h2 : (0:ℝ) ≤ E₂ * P * Real.log P / T := by positivity
    have h3 : (0:ℝ) ≤ E₃ * D4g * P / T ^ 2 := by positivity
    linarith
  have hεD0 : (0 : ℝ) ≤ εD := by rw [hεDdef]; positivity
  set ε : ℝ := εE + εZ + εD with hεdef
  have hε0 : (0 : ℝ) ≤ ε := by rw [hεdef]; linarith
  -- ⟦the two price hypotheses of the pair dual⟧
  have hcross : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ u : ℝ, |u| ≤ 2 * T →
      ‖∑' n : ℕ, ((ψ (n : ZMod q) * (vonMangoldt n : ℂ)) * (n : ℂ) ^ ((u : ℂ) * I))
          * (primeWindow P n : ℂ)‖ ≤ ε := by
    intro ψ hψ1 u hu
    have h := hedgeB ψ hψ1 u hu
    rw [hεdef]
    linarith [h, hεZ0, hεD0]
  have hdiag : ∀ u : ℝ, |u| ≤ 2 * T →
      ‖(∑' n : ℕ, (((1 : DirichletCharacter ℂ q) (n : ZMod q) * (vonMangoldt n : ℂ))
            * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ)) - windowKernel P 1 u‖ ≤ ε := by
    intro u hu
    have h1 := hdebitB u
    have h2 := hppB u hu
    have hid : (∑' n : ℕ, (((1 : DirichletCharacter ℂ q) (n : ZMod q) * (vonMangoldt n : ℂ))
            * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ)) - windowKernel P 1 u
        = ((∑' n : ℕ, (((1 : DirichletCharacter ℂ q) (n : ZMod q) * (vonMangoldt n : ℂ))
              * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
            - (∑' n : ℕ, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I))
              * (primeWindow P n : ℂ)))
          + ((∑' n : ℕ, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I))
              * (primeWindow P n : ℂ)) - windowKernel P 1 u) := by ring
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    rw [hεdef]
    linarith [h1, h2, hεE0]
  -- ⟦the dual bound, then the duality gateway⟧
  have hdual := dual_core_pair hP hT0.le hws hsub hS hcross hdiag
  have hΔ0 : (0 : ℝ) ≤ (44 * Real.pi * P + ε * (ℰ.card : ℝ)) / Real.log P := by
    have h1 : (0:ℝ) ≤ 44 * Real.pi * P := by positivity
    have h2 : (0:ℝ) ≤ ε * (ℰ.card : ℝ) := mul_nonneg hε0 (by positivity)
    exact div_nonneg (by linarith) hlogP.le
  have hS1 : ∀ n ∈ S, 1 ≤ n := fun n hn => le_trans (by norm_num) (hS n hn).1.two_le
  have hprim := primal_of_dual_pair hS1 hΔ0 hdual a
  -- ⟦the absorption: `ε ≤ Cε·P·expc·(log qT)²`⟧
  have b1 : C₁ * P * Real.exp (-(c_vk / 2) * Real.log P / D4g) * D5g
      ≤ C₁ * K₅ * (P * expc * Lq ^ 2) :=
    absorb_exp_term hC₁.le hP0.le hcmp_edge hD5Lq hD5gpos.le hexpc0.le
  have b2 : C₂ * P * Real.log P / T ≤ C₂ * 10 * (P * expc * Lq ^ 2) := by
    have h := absorb_exp_term (Cc := C₂) (Pv := P) (x := 1 / T) (e := expc)
      (D := Real.log P) (K := 10) (Lv := Lq ^ 2) hC₂.le hP0.le hTinv hlogPLq hlogP.le hexpc0.le
    calc C₂ * P * Real.log P / T = C₂ * P * (1 / T) * Real.log P := by ring
      _ ≤ C₂ * 10 * (P * expc * Lq ^ 2) := h
  have b3 : C₃ * D5g * P / T ^ 2 ≤ C₃ * K₅ * (P * expc * Lq ^ 2) := by
    have h := absorb_exp_term (Cc := C₃) (Pv := P) (x := 1 / T ^ 2) (e := expc)
      (D := D5g) (K := K₅) (Lv := Lq ^ 2) hC₃.le hP0.le hT2inv hD5Lq hD5gpos.le hexpc0.le
    calc C₃ * D5g * P / T ^ 2 = C₃ * P * (1 / T ^ 2) * D5g := by ring
      _ ≤ C₃ * K₅ * (P * expc * Lq ^ 2) := h
  have b4 : E₁ * P * Real.exp (-(c₀ / 2) * Real.log P / D3g) * D4g
      ≤ E₁ * K₂ * (P * expc * Lq ^ 2) :=
    absorb_exp_term hE₁.le hP0.le hcmp_pp hD4Lq hD4gpos.le hexpc0.le
  have b5 : E₂ * P * Real.log P / T ≤ E₂ * 10 * (P * expc * Lq ^ 2) := by
    have h := absorb_exp_term (Cc := E₂) (Pv := P) (x := 1 / T) (e := expc)
      (D := Real.log P) (K := 10) (Lv := Lq ^ 2) hE₂.le hP0.le hTinv hlogPLq hlogP.le hexpc0.le
    calc E₂ * P * Real.log P / T = E₂ * P * (1 / T) * Real.log P := by ring
      _ ≤ E₂ * 10 * (P * expc * Lq ^ 2) := h
  have b6 : E₃ * D4g * P / T ^ 2 ≤ E₃ * K₂ * (P * expc * Lq ^ 2) := by
    have h := absorb_exp_term (Cc := E₃) (Pv := P) (x := 1 / T ^ 2) (e := expc)
      (D := D4g) (K := K₂) (Lv := Lq ^ 2) hE₃.le hP0.le hT2inv hD4Lq hD4gpos.le hexpc0.le
    calc E₃ * D4g * P / T ^ 2 = E₃ * P * (1 / T ^ 2) * D4g := by ring
      _ ≤ E₃ * K₂ * (P * expc * Lq ^ 2) := h
  have b7 : εD ≤ 9 * (P * expc * Lq ^ 2) := by
    rw [hεDdef]
    have hd1 : ((Nat.log 2 ⌊3 * P⌋₊ : ℝ) + 1) ≤ 9 * Real.sqrt P := natLog2_floor_le_sqrt hP
    have hd2 : Real.log q ≤ Lq ^ 2 := by
      have h : Real.log q ≤ Lq := by
        rw [hLqdef]; exact Real.log_le_log (by linarith) (by nlinarith)
      linarith [hLqsq]
    have hstep : ((Nat.log 2 ⌊3 * P⌋₊ : ℝ) + 1) * Real.log q ≤ (9 * Real.sqrt P) * Lq ^ 2 :=
      mul_le_mul hd1 hd2 hlogq0 (by positivity)
    refine hstep.trans ?_
    have h9 : (9 : ℝ) * Real.sqrt P ≤ 9 * (P * expc) := by linarith [hsqrtP]
    calc (9 * Real.sqrt P) * Lq ^ 2 ≤ (9 * (P * expc)) * Lq ^ 2 :=
          mul_le_mul_of_nonneg_right h9 (by positivity)
      _ = 9 * (P * expc * Lq ^ 2) := by ring
  have habs : ε ≤ Cε * (P * expc * Lq ^ 2) := by
    have hsum : εE + εZ + εD
        ≤ C₁ * K₅ * (P * expc * Lq ^ 2) + C₂ * 10 * (P * expc * Lq ^ 2)
          + C₃ * K₅ * (P * expc * Lq ^ 2) + E₁ * K₂ * (P * expc * Lq ^ 2)
          + E₂ * 10 * (P * expc * Lq ^ 2) + E₃ * K₂ * (P * expc * Lq ^ 2)
          + 9 * (P * expc * Lq ^ 2) := by
      rw [hεEdef, hεZdef]
      linarith [b1, b2, b3, b4, b5, b6, b7]
    have heq : C₁ * K₅ * (P * expc * Lq ^ 2) + C₂ * 10 * (P * expc * Lq ^ 2)
          + C₃ * K₅ * (P * expc * Lq ^ 2) + E₁ * K₂ * (P * expc * Lq ^ 2)
          + E₂ * 10 * (P * expc * Lq ^ 2) + E₃ * K₂ * (P * expc * Lq ^ 2)
          + 9 * (P * expc * Lq ^ 2)
        = Cε * (P * expc * Lq ^ 2) := by rw [hCεdef]; ring
    calc ε = εE + εZ + εD := hεdef
      _ ≤ _ := hsum
      _ = Cε * (P * expc * Lq ^ 2) := heq
  -- ⟦the final repackaging⟧
  refine hprim.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [div_le_div_iff₀ hlogP hlogP]
  have hmass : (0 : ℝ) ≤ (ℰ.card : ℝ) := by positivity
  have hstep1 : ε * (ℰ.card : ℝ) ≤ Cε * (P * expc * Lq ^ 2) * (ℰ.card : ℝ) :=
    mul_le_mul_of_nonneg_right habs hmass
  have hgoal : 44 * Real.pi * P + ε * (ℰ.card : ℝ)
      ≤ (44 * Real.pi + Cε) * (P + (ℰ.card : ℝ) * P * expc * Lq ^ 2) := by
    have hexpand : (44 * Real.pi + Cε) * (P + (ℰ.card : ℝ) * P * expc * Lq ^ 2)
        = 44 * Real.pi * P + Cε * P + 44 * Real.pi * ((ℰ.card : ℝ) * P * expc * Lq ^ 2)
          + Cε * (P * expc * Lq ^ 2) * (ℰ.card : ℝ) := by ring
    have h1 : (0 : ℝ) ≤ Cε * P := by positivity
    have h2 : (0 : ℝ) ≤ 44 * Real.pi * ((ℰ.card : ℝ) * P * expc * Lq ^ 2) := by positivity
    rw [hexpand]
    linarith [hstep1]
  exact mul_le_mul_of_nonneg_right hgoal hlogP.le

end Salt.MR

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §3 — THE SIX PASS-THROUGHS

`NumeralKq`'s `_bounded` family, each twin re-run with the `cs` floor riding beside the `Kq`
ceiling.  Bodies verbatim from `NumeralKq.lean:668-1068`; the only edits are the extra
conjunct in the `∃`-prefix, the extra name in each `obtain`/`refine` tuple, and the callee
re-pointed at its own `_cs` twin. -/

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open Complex MeasureTheory Set ArithmeticFunction DirichletCharacter in
open scoped LSeries.notation in
/-- **⟦cs-FLOORED TWIN⟧** `halasz_primes_chi_pair_of_gates_bounded`
+ the conjunct `Real.exp (-100) ≤ cs` (§2's floor, carried).
the port's pair row; pass-through. -/
theorem halasz_primes_chi_pair_of_gates_bounded_cs {C₁ C₂ C₃ T₀e : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃)
    (hT₀e : Real.exp (Real.exp 100) ≤ T₀e)
    (hprice : TwistedWindowPriceGated (1 / 10 ^ 8) C₁ C₂ C₃ T₀e) :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (-100) ≤ c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
        (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * Complex.I) * chiBarCoeff q r.1 a n‖ ^ 2
          ≤ C * (P + (ℰ.card : ℝ) * P
                  * Real.exp (-c * Real.log P
                      / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                          * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
                  * (Real.log ((q : ℝ) * T)) ^ 2)
              / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C, c, T₀, hC, hc, hcf, hT₀, hgated⟩ :=
    halaszPrimesChiGated_of_price_floored (by norm_num) hC₁ hC₂ hC₃ hT₀e hprice
  obtain ⟨Kq, Ks, hKq, hKqb, hKs, hreg⟩ := twisted_rect_zero_free_siegel_bounded
  refine ⟨C, c, max T₀ T₀e, Kq, Ks, hC, hc, hcf, le_trans hT₀ (le_max_left _ _), hKq, hKqb,
    hKs, ?_⟩
  intro q hq T P hT hP hPT10 hG1 hG2 hG3 hG4 ℰ hws hsub S hS a
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hTfloor : Real.exp (Real.exp 100) ≤ T := le_trans hT₀e (le_trans (le_max_right _ _) hT)
  -- the `A`-instantiation that makes stone C's own `hAq` free
  set A : ℝ := 1 + Real.log (20000 * (vkStripConst q + 8104)) / 100 with hAdef
  have hCq1 : (1 : ℝ) ≤ vkStripConst q := one_le_vkStripConst
  have hlogA0 : (0 : ℝ) ≤ Real.log (20000 * (vkStripConst q + 8104)) :=
    Real.log_nonneg (by linarith)
  have hA1 : (1 : ℝ) ≤ A := by rw [hAdef]; linarith
  have hAq : Real.log (20000 * (vkStripConst q + 8104)) ≤ A * 100 := by
    rw [hAdef]; linarith
  have hAabs : A + 7 ≤ Real.log (Real.log (5 * T + 1)) := by rw [hAdef]; linarith [hG2]
  exact hgated q T P hTT₀ hP hPT10 hG1
    (fun ψ hψ1 => hreg q ψ hψ1 A T hA1 hTfloor hAq hAabs hG3 hG4) ℰ hws hsub S hS a

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open Complex DirichletCharacter in
/-- **⟦cs-FLOORED TWIN⟧** `halaszPrimesChi_holds_gated_bounded`
+ the conjunct `Real.exp (-100) ≤ cs` (§2's floor, carried).
the gated socket row; pass-through. -/
theorem halaszPrimesChi_holds_gated_bounded_cs :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (-100) ≤ c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
        (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * Complex.I) * chiBarCoeff q r.1 a n‖ ^ 2
          ≤ C * (P + (ℰ.card : ℝ) * P
                  * Real.exp (-c * Real.log P
                      / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                          * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
                  * (Real.log ((q : ℝ) * T)) ^ 2)
              / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C₁, C₂, C₃, T₀e, hC₁, hC₂, hC₃, hT₀e, hprice⟩ := twisted_window_price_gated_holds
  exact halasz_primes_chi_pair_of_gates_bounded_cs hC₁ hC₂ hC₃ hT₀e hprice

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open Complex DirichletCharacter in
/-- **⟦cs-FLOORED TWIN⟧** `halaszPrimesChi_pointwise_of_gates_bounded`
+ the conjunct `Real.exp (-100) ≤ cs` (§2's floor, carried).
the pointwise socket; pass-through. -/
theorem halaszPrimesChi_pointwise_of_gates_bounded_cs :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (-100) ≤ c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T : ℝ), T₀ ≤ T →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      HalaszPrimesChi C c q T := by
  obtain ⟨C, c, T₀, Kq, Ks, hC, hc, hcf, hT₀, hKq, hKqb, hKs, hrow⟩ :=
    halaszPrimesChi_holds_gated_bounded_cs
  refine ⟨C, c, T₀, Kq, Ks, hC, hc, hcf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ T hT hG1 hG2 hG3 hG4 P hP hPT10 ℰ hws hsub S hS a
  exact hrow q T P hT hP hPT10 hG1 hG2 hG3 hG4 ℰ hws hsub S hS a

set_option maxHeartbeats 2400000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open MeasureTheory in
/-- **⟦cs-FLOORED TWIN⟧** `usetGChi_window_meansq_gated_family_perBlock_bounded`
+ the conjunct `Real.exp (-100) ≤ cs` (§2's floor, carried).
the χ-summed window mean square, gated; pass-through. -/
theorem usetGChi_window_meansq_gated_family_perBlock_bounded_cs :
    ∃ Cs cs T₀ Kq Ks : ℝ, 0 < Cs ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (f : ℕ → ℂ), (∀ n : ℕ, ‖f n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (T VJ V L X : ℝ), 1 ≤ T → 1 < (q : ℝ) * T →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T →
        30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * T)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → T ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        -- ⟦THE PER-`(q,T)` FLOOR — what the socket's discharge costs⟧
        T₀ ≤ T →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * T) → Real.log ((q : ℝ) * T) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ),
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q,
          thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, H ≤ (j : ℝ)) →
        (∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * T) →
        (∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * T) / Real.log (ramQbase H P j)) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ T ^ 10) →
        (∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L) →
        (∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase H P j)) ^ 2) →
      ∀ Rbd : ℝ, 0 ≤ Rbd →
      ∀ 𝔄 : Set (DirichletCharacter ℂ q × ℝ),
        (∀ χ : DirichletCharacter ℂ q, MeasurableSet {t : ℝ | (χ, t) ∈ 𝔄}) →
        (∀ r ∈ 𝔄, r.2 ∈ Set.Icc (-T) T) →
        𝔄 ⊆ UsetGChi q f Pseq Qseq Hseq αseq J →
        (∀ j ∈ ramI H P Q, ∀ r ∈ 𝔄,
          ‖ramR H N Xd P Q j (chiBarCoeff q r.1 b) r.2‖ ≤ Rbd) →
      ∀ E : ℝ, (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
          ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
        (∑ χ : DirichletCharacter ℂ q,
            ∫ t in {t : ℝ | (χ, t) ∈ 𝔄}, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (∑ j ∈ ramI H P Q,
                  (5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ)
                        * (1 + Real.log (2 * T))
                      * (∑ m ∈ Finset.Icc 1 (Ms j),
                          ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
                    + 81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2))
            + 2 * E := by
  obtain ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hcsf, hT₀, hKq, hKqb, hKs, hpt⟩ :=
    halaszPrimesChi_pointwise_of_gates_bounded_cs
  refine ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hcsf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 T VJ V L X hT1 hqT hP3 hPQ
    hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL
    hgate Rbd hRbd 𝔄 hAm hAsub hUA hR E herr
  exact usetGChi_window_meansq_of_socket_family_perBlock hCs hcs q f hf1 Pseq Qseq Hseq αseq
    J Jb hJb1 hJbJ hH2seq hα0 T VJ V L X (hpt q T hT₀T hG1 hG2 hG3 hG4) hT1 hqT hP3 hPQ hQT
    hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hlogT1 hTL hLe hlogV
    H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate Rbd hRbd
    𝔄 hAm hAsub hUA hR E herr

set_option maxHeartbeats 2400000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open MeasureTheory in
/-- **⟦cs-FLOORED TWIN⟧** `usetGChi_row_exit_perChi_perBlock_bounded`
+ the conjunct `Real.exp (-100) ≤ cs` (§2's floor, carried).
the per-χ row exit; pass-through (only `Cs` rescales). -/
theorem usetGChi_row_exit_perChi_perBlock_bounded_cs :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (Tann VJ V L X : ℝ), 1 ≤ Tann → 1 < (q : ℝ) * Tann →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann →
        30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * Tann)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → Tann ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        T₀ ≤ Tann →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * Tann + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * Tann) → Real.log ((q : ℝ) * Tann) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ),
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q,
          thinBundleGChi ((q : ℝ) * Tann) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, H ≤ (j : ℝ)) →
        (∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * Tann) →
        (∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * Tann) / Real.log (ramQbase H P j)) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ Tann ^ 10) →
        (∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L) →
        (∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase H P j)) ^ 2) →
      ∀ Rbd : ℝ, 0 ≤ Rbd →
      ∀ t₁ : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ j ∈ ramI H P Q,
          ∀ t ∈ seamAnn X Tann \ seamBall X (t₁ χ),
            ‖ramR H N Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd) →
      ∀ E : ℝ, (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
          ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
      ∀ KS : ℝ,
        (∀ j ∈ ramI H P Q,
          5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
              * (∑ m ∈ Finset.Icc 1 (Ms j),
                  ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
            ≤ KS) →
        2 ≤ ⌊H * Real.log (P : ℝ)⌋₊ →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (seamAnn X Tann \ seamBall X (t₁ χ))
            ∩ UsetG (chiBarCoeff q χ c) Pseq Qseq Hseq αseq J,
            ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (((ramI H P Q).card : ℝ) * KS
                  + 54 * Cq * Rbd ^ 2 * H ^ 2
                      / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E := by
  obtain ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hcsf, hT₀, hKq, hKqb, hKs, hfam⟩ :=
    usetGChi_window_meansq_gated_family_perBlock_bounded_cs
  refine ⟨3 * Cs / 2, cs, T₀, Kq, Ks, by linarith, hcs, hcsf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X hT1 hqT hP3
    hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL
    hgate Rbd hRbd t₁ hR E herr KS hKS hj₀ χ
  -- ⟦the Σ_χ exit at the row's own pair set⟧
  have hsum := hfam q c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X
    hT1 hqT hP3 hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T
    hG1 hG2 hG3 hG4 hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3
    hBT hκ30 hBT10 hWL hgate Rbd hRbd
    (rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁)
    (measurableSet_rowPairSetG_fibre q c Pseq Qseq Hseq αseq J X Tann t₁)
    (rowPairSetG_sub q c Pseq Qseq Hseq αseq J X Tann t₁)
    (rowPairSetG_subset_UsetGChi q c Pseq Qseq Hseq αseq J X Tann t₁)
    (fun j hj r hr => hR r.1 j hj r.2 hr.1) E herr
  -- ⟦the per-χ read: every fibre integral is nonnegative, so one is at most the sum⟧
  have hnn : ∀ χ' ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      (0 : ℝ) ≤ ∫ t in {t : ℝ | (χ', t) ∈ rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁},
        ‖spoly N (chiBarCoeff q χ' a) t‖ ^ 2 := by
    intro χ' _
    exact setIntegral_nonneg
      (measurableSet_rowPairSetG_fibre q c Pseq Qseq Hseq αseq J X Tann t₁ χ')
      (fun _ _ => by positivity)
  have hsingle := Finset.single_le_sum hnn (Finset.mem_univ χ)
  -- ⟦the ⟦ii-8⟧ block price, per block⟧
  have hprice := usetGChi_block_price_perBlock H N Xd P Q Ms b X Tann KS Cs Rbd hCs.le hRbd
    hj₀ hKS
  have hcard0 : (0 : ℝ) ≤ 4 * ((ramI H P Q).card : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hprice hcard0
  rw [rowPairSetG_fibre] at hsingle
  linarith

set_option maxHeartbeats 3200000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open MeasureTheory in
/-- **⟦cs-FLOORED TWIN⟧** `m4_rowChi_capstone_perBlock_bounded`
+ the conjunct `Real.exp (-100) ≤ cs` (§2's floor, carried).
the per-χ capstone row, per block; pass-through. -/
theorem m4_rowChi_capstone_perBlock_bounded_cs :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (Tann VJ V L X : ℝ), 1 ≤ Tann → 1 < (q : ℝ) * Tann →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann →
        30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * Tann)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → Tann ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        T₀ ≤ Tann →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * Tann + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * Tann) → Real.log ((q : ℝ) * Tann) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
        -- ⟦THE `X`-SIDE FRAME⟧
        2 ≤ H83 X theta293 → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann →
      ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleGChi ((q : ℝ) * Tann) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, H83 X theta293 ≤ (j : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 3 ≤ ramQbase (H83 X theta293) P j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          (ramQbase (H83 X theta293) P j : ℝ) ≤ (q : ℝ) * Tann) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          30 ≤ Real.log ((q : ℝ) * Tann) / Real.log (ramQbase (H83 X theta293) P j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          (ramQbase (H83 X theta293) P j : ℝ) ≤ Tann ^ 10) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          Real.log (ramQbase (H83 X theta293) P j) ≤ L) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase (H83 X theta293) P j)) ^ 2) →
      ∀ (Rbd CR : ℝ), 0 ≤ Rbd → Rbd ≤ CR * (Real.log X) ^ (-rho293) →
        1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
      ∀ t₁ : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ j ∈ ramI (H83 X theta293) P Q,
          ∀ t ∈ seamAnn X Tann \ seamBall X (t₁ χ),
            ‖ramR (H83 X theta293) N Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd) →
      ∀ KS : ℝ, 0 ≤ KS →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
              * (∑ m ∈ Finset.Icc 1 (Ms j),
                  ‖ramRcoeff (H83 X theta293) N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
            ≤ KS) →
        32 * (Real.log X) ^ (2 + 2 * theta293) * KS ≤ (Real.log X) ^ (-theta293) →
      ∀ (E EP2 εr : ℝ), 0 ≤ εr → 8640 ≤ (Real.log X) ^ εr →
        12 * EP2 ≤ (Real.log X) ^ (-theta293 + εr) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
          ‖ramErr (H83 X theta293) N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
      ∀ S : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann →
          |t - t₁ χ| ≤ seamRad X → ∀ m : ℕ, m ≤ N →
            ‖spolyA (chiBarCoeff q χ a) t m‖ ≤ S χ * m / (1 + |t - t₁ χ|)) →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 8 * S χ ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X (t₁ χ))
                ∩ seamTtotG (chiBarCoeff q χ c) Pseq Qseq Hseq αseq J,
                ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + εr)) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, hexit⟩ :=
    usetGChi_row_exit_perChi_perBlock_bounded_cs
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X hT1 hqT hP3
    hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV hH2 hLXe hL4 hTgate
    N Xd P Q Ms a b cf hcf1 hPlow hQ0 hQhigh hM hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate
    Rbd CR hRbd hRgrade hCqgate t₁ hR KS hKS0 hKS hKSgate E EP2 εr hεr habs hEP2 hErow herr
    hXN hN2 hsupp S hSup χ
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hH0 : (0 : ℝ) ≤ H83 X theta293 := by linarith
  have hHeq : H83 X theta293 = (Real.log X) ^ theta293 := by rw [H83]
  have hTann0 : (0 : ℝ) ≤ Tann := by linarith
  have hfl := floor_pin X P hL4 hPlow
  -- ⟦the per-χ `𝒰` exit, per block⟧
  have hU := hexit q c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X
    hT1 hqT hP3 hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T
    hG1 hG2 hG3 hG4 hlogT1 hTL hLe hlogV (H83 X theta293) hH2 N Xd P Q Ms a b cf hcf1 hM
    hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate Rbd hRbd t₁ hR E herr KS hKS hfl.1 χ
  -- ⟦the block leg, priced at `θ₂₉₃`⟧
  have hmain := balance_priced_main X (H83 X theta293) Cq CR KS Rbd P Q hL0 hH0
    (ramI_card_le_pin X P Q hQ0 hQhigh hLXe) (le_of_eq hHeq) hfl.2
    hCq.le hKS0 hRbd hRgrade hKSgate hCqgate
  -- ⟦Lemma 12's error leg, absorbed⟧
  have hrem := rem_priced X Tann (H83 X theta293) εr EP2 E hL1 hX0 hTann0
    (le_of_eq hHeq.symm) habs hEP2 hErow
  -- ⟦the balance⟧
  have hbal := hUG_balance (chiBarCoeff q χ a) (chiBarCoeff q χ c) N Pseq Qseq Hseq αseq J
    X Tann (t₁ χ) εr _ _ hεr hL1 hX0 hTgate hU hmain hrem
  exact prop_A3_T1_row_split_weightedG (chiBarCoeff q χ a) N (chiBarCoeff q χ c) Pseq Qseq
    Hseq αseq J X Tann (t₁ χ) (S χ) _ hL0.le hTann0 hX0 hXN hN2
    (chiBarCoeff_seam_supp χ hsupp) (hSup χ) hbal

end Salt.MR

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla
open scoped BigOperators

/-! ## §4 — THE FOUR TOP HOPS, AND THE RIDER'S DEATH

Hops 7–8 carry the conjunct through `RegisterCompose`'s `∀K`-hoisted twins.  Hop 9 is where
the rider is SPENT: `s16_capGate_supply_L_gk_sharpT0`'s `hcs` argument is fed the carried
conjunct instead of an antecedent, so `Real.exp (-100) ≤ cs` leaves the statement.  Hop 10
forwards the now-hypothesis-free shape through the flat terminal — **this is the declaration a
`v7` mint reads in place of
`logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist`.**

Bodies verbatim from `RegisterCompose.lean:52-300`. -/

set_option maxHeartbeats 3200000 in
-- Same cause as the landed original: one application of a ~45-binder capstone.
/-- ⟦cs-FLOORED TWIN⟧ `RegisterCompose.m4_hcap_at_door_perBlock_L_gk_bounded_khoist`
+ the conjunct `Real.exp (-100) ≤ cs`.  Body verbatim off §3's capstone twin. -/
theorem m4_hcap_at_door_perBlock_L_gk_bounded_khoist_cs :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (K : ℕ) (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 : ℝ),
              DoorCapBasePerBlock_L_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf (2 * T)
                VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, hcapstone⟩ :=
    m4_rowChi_capstone_perBlock_bounded_cs
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro K R M cU ε hcU hfam H L q j A s hb χ T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, hd⟩ :=
    hfam H L q j A s hb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hlogX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := hd.logX_four
    linarith
  have hres := hcapstone q cU hcU (calP (AdoorL M) (s13GK K M))
    (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M)) (mrAlpha (1 / 12)) 2 Jb
    hd.Jb_lo hd.Jb_hi hd.Hseq_two hd.alpha_nonneg
    (2 * T) VJ V Lr (((A + s : ℕ)) : ℝ) hd.Tann_one hd.qTann_one hd.P_three hd.PQ hd.QTann
    hd.kappa30Q hd.loglog5 hd.VJ_bound η εd hd.alpha_eta hd.eta_half hd.Tann_X hd.X_pos
    hd.debit hd.logX_pos hd.q_logX hd.V_one hd.V_inv hd.T0_Tann hd.floor1 hd.floor2
    hd.floor3 hd.floor4 hd.logqT_one hd.logqT_L hd.L_exp hd.logV_L
    hd.H83_two hd.logX_exp hd.logX_four hTgate
    (2 * (A + s)) Xd P Q Mr (winCutH (A + s) (doorCoeffU_L_gk K M)) b cf hd.cf_one hd.P_low
    hd.Q_pos hd.Q_high hd.range hd.budget hd.Hj hd.B3 hd.BT hd.kappa30 hd.BT10 hd.WL hd.gate
    Rbd CR hd.Rbd_nonneg hd.Rbd_grade hd.Cq_gate
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ)) hd.Rbd_binder
    KS hd.KS_nonneg hd.KS_binder hd.KS_gate E EP2 (ε (A + s)) hd.epsr_nonneg hd.abs8640
    hd.EP2_gate hd.E_row hd.E_binder (doorCap_hXN (A + s)) (doorCap_hN2 (A + s))
    (fun n hn => doorRowDatumU_supp0_L_gk K M (A + s) hn)
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ))
    (m4_hSup_door_at_zero q (winCutH (A + s) (doorCoeffU_L_gk K M)) (2 * (A + s)) hlogX1) χ
  rw [chiBarCoeff_doorRowDatum_L_gk] at hres
  simpa using hres

set_option maxHeartbeats 3200000 in
-- Same cause as the landed original: the wire's own statement re-elaborates.
/-- ⟦cs-FLOORED TWIN⟧ `RegisterCompose.m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist`
+ the conjunct `Real.exp (-100) ≤ cs`.  Body verbatim. -/
theorem m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ Real.exp 100 ∧ 0 < Ks ∧
      ∀ (K : ℕ) (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
              G2Scaffold.DoorCapErrWS_L_gk K M (A + s) q Xd P Q b cf (2 * T) E Mtail
                ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                      ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                        (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU_L_gk K M)))
                        (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                    → DoorCapBasePerBlock_L_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                        (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, hwire⟩ :=
    m4_hcap_at_door_perBlock_L_gk_bounded_khoist_cs
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq,
    le_trans hKqb kq_closed_form_le_exp_hundred, hKs, ?_⟩
  intro K R M cU ε hc1 hcapWS
  refine hwire K R M cU ε hc1 ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (G2Scaffold.m4_capE_at_door_L_gk K hws)⟩

set_option maxHeartbeats 3200000 in
-- Same cause as the landed original: the eighteen-slot `hcapWS` family re-elaborates.
/-- **⟦THE RIDER DIES HERE⟧** `RegisterCompose.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist`
with `Real.exp (-100) ≤ cs` MOVED from an antecedent of the inner implication to a CONJUNCT of
the `∃`-prefix — i.e. from something the caller must supply to something this theorem delivers.
`s16_capGate_supply_L_gk_sharpT0`, the only consumer of the rider, is fed the carried conjunct.
Body otherwise verbatim. -/
theorem s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree :
    ∃ Cq cs T₀ Kq Ks C : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ Real.exp 100 ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      ∀ K : ℕ,
        (Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ (R : ChowlaRegime) (M : ℕ), 1 ≤ M → loglogFloor50 ≤ R.Hlo →
          T₀ ≤ Real.exp (Real.sqrt ((R.Hlo : ℕ) : ℝ) / 2) →
          (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → s13BlockFloor_L_gk K M ≤ A + s) →
          S16CofactorSupply_L_gk K Cq R M → S16BaseScaleCap96_L_gk K R M →
          S15CrossingBound_L_gk K R M) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hwire⟩ :=
    m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs
  obtain ⟨C, hC0, hC40, hband⟩ := m4_tail_mass_at_band_bounded
  refine ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40, ?_⟩
  intro K hKq hKs R M hM hfl hT₀ hblk hcof hcap
  -- ⟦THE RIDER, SPENT FROM THE PREFIX⟧ `hcsf` is the carried conjunct, not an antecedent
  have hgate := s16_capGate_supply_L_gk_sharpT0 K hM hfl hcsf hblk hT₀ hKq hKs hC0 hC40
    (fun _ => le_rfl) hcap hcof
  refine hwire K R M liouvilleC (fun _ => theta293 - 1 / 500) liouvilleC_norm_le_one ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨P, Q, Rrad, Rbd, CR, EP2, hg⟩ := hgate H L q j A s hsb T hTlo hThi hTgate hTll
  have hq : 1 ≤ q := hsb.2.2.2.1
  have hA : 0 < A := hsb.2.2.2.2.2.2.2.1
  have hNd : 1 ≤ A + s := by omega
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by have := hg.logX_eight; linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
  have hT1 : (1 : ℝ) < 2 * T := by linarith
  exact doorCapBundle_at_workingPoint_perBlock_L_gk K hband hM hNd hq hg hT1 hThi hTll

/-! ### hop 10 — ⟦THE FLAT TERMINAL, cs-FREE⟧ -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 3200000 in
-- Same cause as the landed original: the hoisted prefix plus the three window discharges
-- re-elaborate the terminal's conclusion.
/-- **⟦THE cs-FREE FLAT TERMINAL⟧**
`RegisterCompose.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist` with the `cs`
rider gone from the inner implication and delivered as a prefix conjunct instead.  **This is
the declaration a `v7` mint reads**: replaying `logChowla2_ineffective_v6`'s body against it
drops `Real.exp (-100) ≤ cs` from the terminal's surviving list, leaving four inner items.
Body otherwise verbatim. -/
theorem logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_winU Awin) :
    ∃ (ε : ℚ) (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧
        ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
          K ≤ 170000000 * flatDoorM A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          T₀ ≤ Real.exp (Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ) / 2) →
          Real.exp (-100) ≤ Ks →
          ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            (S16CofactorSupply_L_gk K Cq R (flatDoorM A) →
              S16BaseScaleCap96_L_gk K R (flatDoorM A) →
                ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, hcondU⟩ :=
    flat_conditional_uniform_win_xceil_kwide_khoist Awin hband
  -- ⟦THE CROSSING CONSTANTS, HOISTED ABOVE THE LEVER⟧ — §1's twin
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40,
    hsupplyU⟩ := s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  obtain ⟨_Ct0, -, -, hcond0⟩ := hcondU 0
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond0 (max 162 (budgetAFlat (ε : ℝ) β)) (le_max_left _ _) (le_max_right _ _)
  have hzero : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := by
    intro Hhi ω hgate
    obtain ⟨-, -, hωw⟩ := hgate
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [Real.log_natCast_nonneg ω]
  obtain ⟨R0, hR0eps, -, -, -, -, -⟩ :=
    hbody0 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) hzero le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have hεR : (1 : ℝ) / 500 ≤ (ε : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hεpin
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
    exact h
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  have hsupply := hsupplyU K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA26 hAwin hAge hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge
  refine ⟨fun hopq => flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hx0win hopq hT₀ hKs g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g hg (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by
    rw [hReps]
    have : (1 : ℚ) / 2 ^ 9 ≤ 1 / 500 := by norm_num
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win (c := 1) hA26 K hKw (by norm_num) (by norm_num) (by simp) hδ₀ (by simpa using hδpin) hKc hKcb
    hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win (by simpa using heps) hlo hwin
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk K (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel hKw
    (hsupply hKqb hKs R (flatDoorM A) hM1 hfl (by rw [hHlo]; exact hT₀) hblk hcof hcapsc)


/-! ## §5 — ⟦THE DELIVERABLE⟧ `v6` WITH THE `cs` RIDER GONE

Body verbatim from `RegisterCompose.lean:345-446`, with the terminal re-pointed at §4's
`_csfree` twin and the rider's arrow removed.  This is NOT the `v7` mint — four inner items
remain — it is the demonstration that the carry reaches `v6`'s own statement. -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 3200000 in
-- Same cause as `v5`: the `∃`-prefix and the four window discharges re-elaborate the
-- conclusion under the raised lever, now with the co-factor supply discharged inside.
/-- **⟦`v6` WITH RIDER 1 DISCHARGED⟧** (`logChowla2_ineffective_v6_csarm`) — `v6` verbatim
with the `cs` arrow GONE from the inner implication.

⟦WHAT CHANGED⟧ `v6`'s first surviving inner item, `Real.exp (-100) ≤ cs`, was a rider on a
constant `v6`'s own `∃`-prefix mints — and `RiderTrace` had already pinned that constant's
closed form (`3.716·10^{-11}`, 33 orders above `e^{-100}`).  §1–§4 carry the floor from the
two leaves that produce it (`c_vk = 1/10^8`, `c₀ = 1/10^9`) up all nine hops as a CONJUNCT, so
the terminal now DELIVERS `Real.exp (-100) ≤ cs` instead of asking for it.  The list of inner
items drops from five to **four**: `T₀`-sharp, `Ks`, `XCeilRiderStrict ε g`, the `K_vt`
cushion.  Outer: still nothing.

`v6` is byte-untouched and remains citable; this is the form V7-E's mint consumes (composing
with V7-C's `_T0arm` arm leaves three).  V7-E is HELD and is not minted here. -/
theorem logChowla2_ineffective_v6_csarm (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) →
        Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
              + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
            ≤ Real.log (R.Hhi : ℝ) / 4 →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  -- ⟦THE REPAIRED CO-FACTOR SUPPLY⟧ its four Skolem constants, minted outside everything
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ := cofkR_cofactorSupply_L_gk
  obtain ⟨Awin, -, hband⟩ := s16_bandLaneWinL_holdsU
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ :=
    logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree Awin hband
  -- ⟦THE DESIGN CONSTANT⟧ chosen above all four fixed constants AND above the co-factor
  -- threshold — legal exactly because `C_q` is now minted BEFORE the lever (§1)
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
      (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))) := ⟨_, rfl⟩
  have hA162 : (162 : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)
  have hA₀A : A₀ ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)
  have hAwinA : Awin ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    rw [hAdef]
    exact le_trans (le_max_right (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
      (le_max_left _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    rw [hAdef]
    exact le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
    have h2 : Real.exp (3.2 * A) / 10 + 1 ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
      Real.add_one_le_exp _
    linarith
  have hopq : Hopq ≤ flatDesignBase A := by
    have h2 : Real.exp (3.2 * A) + 1 ≤ Real.exp (Real.exp (3.2 * A)) := Real.add_one_le_exp _
    have hR : ((Hopq : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by linarith
    have hceil := le_trans hR (Nat.le_ceil (Real.exp (Real.exp (3.2 * A))))
    rw [flatDesignBase]; exact_mod_cast hceil
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, hCt, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hKw
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A, hKvt0, ?_⟩
  intro hT₀ hKs g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKs g hg
  refine ⟨R, hReps, by rw [hHlo]; exact hbase hopq, hRg, hRtow, hdes, hwin, ?_⟩
  intro hKvtcush
  -- ⟦ITEM 3, DISCHARGED⟧ the base-scale cap at `K = KlevF A`
  have heps500 : (1 : ℚ) / 500 ≤ R.eps := by rw [hReps]; exact hεpin
  have hxceil : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [hReps]; exact hRx
  -- ⟦RULING 9, DISCHARGED⟧ the co-factor supply at the repaired ladder
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA26
  have heps500R : (1 : ℝ) / 500 ≤ (R.eps : ℝ) := by
    rw [hReps]
    have h := (Rat.cast_le (K := ℝ)).mpr hεpin
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
    exact h
  have h518 : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by nlinarith [hdes, hA162]
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA162
  have hthrgate : cofkRThr Cq Cb Xsk Y0 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    linarith [hthrA, hlo, hexp1]
  have hcofsupply : S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) :=
    hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush
  exact hfire2 hcofsupply
    (s16_baseScaleCap96_L_at_klevF hA26 (flatDoorM_one_le hA26) heps500 hxceil hwin)

end Salt.MR

end
