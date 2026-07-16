/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.Defs
import Salt.SW.CharDispatch
import Salt.SW.Psi1Transfer
import Salt.SW.SiegelClose

/-!
# The SW rung, node S6c — the orthogonality fold + the Siegel exceptional-term bound

Design: `docs/blueprints/sw.md`, S6 row (the S6c cell). This module folds the per-character
`psi1Chi` bounds (S6b `psi1_char_bound`/`psi1_trivchar_bound`) through the orthogonality identity
`psi1_fold` (S0) — transferring imprimitive characters to their primitive inducers via
`psi1_transfer` (S6a) — and kills the Siegel exceptional term with `siegel_theorem` (S4) at
`ε := 1/(4C)`, producing
the per-`(q,a)` Siegel–Walfisz estimate the S6d sandwich consumes:

* `psi1AP_main_bound` — for every `A, C > 0` there is `K, x₀ > 0` with
  `|φ(q)·ψ₁(x; q, a) − x²/2| ≤ K·x²/(log x)^A` uniformly for reduced `a` and `q ≤ (log x)^C`,
  `x ≥ x₀`. (The φ(q)-multiplied form matching the fold identity; S6d divides by `φ(q)`.)

## Route

`φ(q)·ψ₁(x; q, a) = ∑_χ χ̄(a)·ψ₁(x, χ)` (`psi1_fold`). Split off the principal `χ₀ = 1`: its main
term `x²/2` is subtracted by `psi1_trivchar_bound` (error `≤ K₄·x²·e^{−c₄√L}`). Each non-principal
`χ` is transferred to its primitive `χ₁ = χ.primitiveCharacter` (cost `≤ ω(q)·log x·x`), where the
S6b dispatcher gives either a clean `e^{−c₄√L}`-decay bound or an exceptional real quadratic zero
`β₁` with `‖ψ₁(x,χ₁) + x^{β₁+1}/(β₁(β₁+1))‖` small. The exceptional term is killed by Siegel: at
`ε = 1/(4C)`, `1−β₁ ≥ C_ε/f^ε ≥ C_ε·(log x)^{−1/4}` (as `f ≤ q ≤ (log x)^C`), so
`x^{β₁+1}/(β₁(β₁+1)) ≤ x²·e^{−C_ε(log x)^{3/4}} ≤ x²·e^{−C_ε√L}`. Summing `≤ φ(q) ≤ q ≤ (log x)^C`
characters and absorbing `(log x)^m·e^{−c√L} → 0` and `(log x)^m/x → 0` (the two named absorption
tendsto's below), the total is `≤ K·x²/(log x)^A` for `x` large — the ineffective Siegel `C_ε`
flowing harmlessly into `x₀`.
-/

open Complex Filter DirichletCharacter Asymptotics
open scoped Topology

namespace Salt.SW

/-! ## 1. The two absorption tendsto's -/

/-- **Absorption A** (`(log x)^p · e^{−b√log x} → 0`). Substituting `u = √log x` this is
`u^{2p}·e^{−bu} → 0` (mathlib `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`), composed with
`√∘log → ∞`. -/
theorem log_rpow_mul_exp_neg_sqrt_tendsto (p b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (Real.log x) ^ p * Real.exp (-(b * Real.sqrt (Real.log x))))
      atTop (𝓝 0) := by
  have hsqrtlog : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop := by
    have hsqrt : Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop := by
      have := tendsto_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)
      simpa only [← Real.sqrt_eq_rpow] using this
    exact hsqrt.comp Real.tendsto_log_atTop
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * p) b hb
  refine (h0.comp hsqrtlog).congr' ?_
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hLnn : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx
  simp only [Function.comp_apply]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hLnn, neg_mul]
  congr 2
  ring

/-- **Absorption B** (`(log x)^p / x → 0`). Substituting `v = log x` this is `v^p·e^{−v} → 0`
(mathlib `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, `b = 1`), composed with `log → ∞`. -/
theorem log_rpow_div_tendsto (p : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ p / x) atTop (𝓝 0) := by
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p 1 (by norm_num)
  refine (h0.comp Real.tendsto_log_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  simp only [Function.comp_apply]
  rw [neg_one_mul, Real.exp_neg, Real.exp_log hx, div_eq_mul_inv]

/-- The smallness-arithmetic base: `C·log L + log 2 ≤ √L` eventually (`log =o[atTop] (·)^{1/2}`). -/
theorem smallness_base {C : ℝ} (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, C * Real.log L + Real.log 2 ≤ Real.sqrt L := by
  have hlit : (Real.log : ℝ → ℝ) =o[atTop] (fun x => x ^ (1/2 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have h1 : ∀ᶠ L : ℝ in atTop, ‖Real.log L‖ ≤ (1/(2*C)) * ‖L ^ (1/2:ℝ)‖ :=
    hlit.def (by positivity)
  have h2 : ∀ᶠ L : ℝ in atTop, Real.log 2 ≤ (1/2) * Real.sqrt L := by
    have hst : Tendsto (fun L : ℝ => (1/2) * Real.sqrt L) atTop atTop := by
      have hsqrt : Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop := by
        have := tendsto_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)
        simpa only [← Real.sqrt_eq_rpow] using this
      exact hsqrt.const_mul_atTop (by norm_num)
    exact hst.eventually_ge_atTop _
  filter_upwards [h1, h2, eventually_ge_atTop (1:ℝ)] with L hL1 hL2 hLge
  have hsqeq : L ^ (1/2:ℝ) = Real.sqrt L := (Real.sqrt_eq_rpow L).symm
  have hlognn : 0 ≤ Real.log L := Real.log_nonneg hLge
  have hsqnn : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  rw [Real.norm_of_nonneg hlognn, hsqeq, Real.norm_of_nonneg hsqnn] at hL1
  have hkey : C * Real.log L ≤ (1/2) * Real.sqrt L := by
    have h3 := mul_le_mul_of_nonneg_left hL1 hC.le
    rw [← mul_assoc] at h3
    have hCC : C * (1/(2*C)) = 1/2 := by field_simp
    rw [hCC] at h3
    linarith
  linarith

/-! ## 2. Two small counting facts -/

/-- `ω(q) = |primeFactors q| ≤ q`. -/
theorem primeFactors_card_le_self (q : ℕ) [NeZero q] : (q.primeFactors.card : ℝ) ≤ q := by
  have hsub : q.primeFactors ⊆ Finset.Icc 1 q := by
    intro p hp
    rw [Finset.mem_Icc]
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact ⟨hpp.one_lt.le,
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.dvd_of_mem_primeFactors hp)⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hle : q.primeFactors.card ≤ q := by omega
  exact_mod_cast hle

/-- The number of Dirichlet characters mod `q` is `φ(q) ≤ q`. -/
theorem card_dirichletCharacter_le (q : ℕ) [NeZero q] :
    (Fintype.card (DirichletCharacter ℂ q) : ℝ) ≤ q := by
  have h1 : Nat.card (DirichletCharacter ℂ q) = q.totient :=
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [Nat.card_eq_fintype_card] at h1
  rw [show Fintype.card (DirichletCharacter ℂ q) = q.totient from h1]
  exact_mod_cast Nat.totient_le q

/-- The exceptional Riesz-residue term's norm: for `x, β > 0`,
`‖x^{β+1}/(β(β+1))‖ = x^{β+1}/(β(β+1))` (positive reals). -/
theorem norm_exc_term (x β : ℝ) (hx : 0 < x) (hβ : 0 < β) :
    ‖(x : ℂ) ^ ((β : ℂ) + 1) / ((β : ℂ) * ((β : ℂ) + 1))‖
      = x ^ (β + 1) / (β * (β + 1)) := by
  have hnum : ‖(x:ℂ)^((β:ℂ)+1)‖ = x^(β+1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
  have hden : ‖(β:ℂ)*((β:ℂ)+1)‖ = β*(β+1) := by
    rw [norm_mul]
    have h1 : ‖(β:ℂ)‖ = β := by rw [Complex.norm_real, Real.norm_of_nonneg hβ.le]
    have h2 : ‖(β:ℂ)+1‖ = β+1 := by
      rw [show (β:ℂ)+1 = ((β+1:ℝ):ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    rw [h1, h2]
  rw [norm_div, hnum, hden]

/-! ## 3. The S6c per-`(q,a)` bound -/

set_option maxHeartbeats 1600000 in
-- The proof threads the fold, the per-character dispatcher across every character (with the Siegel
-- exceptional branch), the transfer, the counting and two absorption steps through one large term;
-- the elaborator needs headroom past the default to check it in a single pass.
/-- **S6c — the folded Siegel–Walfisz estimate.** For every `A, C > 0` there are `K, x₀ > 0` such
that for every modulus `q`, every reduced residue `a` (`a < q`, `gcd(q,a) = 1`), and every
`x ≥ x₀` with `q ≤ (log x)^C`,
`|φ(q)·ψ₁(x; q, a) − x²/2| ≤ K·x²/(log x)^A`. Route: the orthogonality fold `psi1_fold`, the S6b
per-character dispatcher on each primitive inducer (`psi1_transfer` bridging the imprimitive ones),
and `siegel_theorem` at `ε = 1/(4C)` killing the exceptional term; the counting and the two
absorption tendsto's collapse everything into `x₀`. `K = 1`. -/
theorem psi1AP_main_bound : ∀ A C : ℝ, 0 < A → 0 < C → ∃ K x₀ : ℝ, 0 < K ∧
    ∀ (q : ℕ) [NeZero q] {a : ℕ}, a < q → Nat.Coprime q a → ∀ {x : ℝ}, x₀ ≤ x →
      (q : ℝ) ≤ (Real.log x) ^ C →
      |(q.totient : ℝ) * psi1AP x q a - x ^ 2 / 2| ≤ K * x ^ 2 / (Real.log x) ^ A := by
  intro A C hA hC
  -- constants
  have hCne : C ≠ 0 := ne_of_gt hC
  set ε : ℝ := 1 / (4 * C) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hCε : C * ε = 1 / 4 := by rw [hεdef]; field_simp
  obtain ⟨Cₛ, hCₛpos, hCₛ⟩ := siegel_theorem ε hεpos
  obtain ⟨cc, Kc, hccpos, hKcpos, hchar⟩ := psi1_char_bound
  obtain ⟨ct, Kt, hctpos, hKtpos, htriv⟩ := psi1_trivchar_bound
  set c5 : ℝ := min (min cc ct) Cₛ with hc5def
  have hc5pos : 0 < c5 := lt_min (lt_min hccpos hctpos) hCₛpos
  have hc5cc : c5 ≤ cc := le_trans (min_le_left _ _) (min_le_left _ _)
  have hc5ct : c5 ≤ ct := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc5Cs : c5 ≤ Cₛ := min_le_right _ _
  set Kbig : ℝ := max Kc Kt with hKbigdef
  have hKbigpos : 0 < Kbig := lt_of_lt_of_le hKcpos (le_max_left _ _)
  have hKcKbig : Kc ≤ Kbig := le_max_left _ _
  have hKtKbig : Kt ≤ Kbig := le_max_right _ _
  -- the eventually facts, extracted into x₀
  have hTA : Tendsto (fun x : ℝ => (2 * Kbig + 1) * (Real.log x) ^ (C + A)
      * Real.exp (-(c5 * Real.sqrt (Real.log x)))) atTop (𝓝 0) := by
    have := (log_rpow_mul_exp_neg_sqrt_tendsto (C + A) c5 hc5pos).const_mul (2 * Kbig + 1)
    simpa only [mul_zero, mul_assoc] using this
  have hEvA : ∀ᶠ x : ℝ in atTop, (2 * Kbig + 1) * (Real.log x) ^ (C + A)
      * Real.exp (-(c5 * Real.sqrt (Real.log x))) ≤ 1 / 2 :=
    ((tendsto_order.1 hTA).2 (1/2) (by norm_num)).mono (fun x h => h.le)
  have hEvB : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ (2 * C + 1 + A) / x ≤ 1 / 2 :=
    ((tendsto_order.1 (log_rpow_div_tendsto (2 * C + 1 + A))).2 (1/2) (by norm_num)).mono
      (fun x h => h.le)
  have hSmallEv : ∀ᶠ x : ℝ in atTop,
      C * Real.log (Real.log x) + Real.log 2 ≤ Real.sqrt (Real.log x) :=
    Real.tendsto_log_atTop.eventually (smallness_base hC)
  have hLog4Ev : ∀ᶠ x : ℝ in atTop, (4:ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4:ℝ))
  obtain ⟨x₀, hx₀⟩ := (hEvA.and (hEvB.and (hSmallEv.and (hLog4Ev.and (eventually_ge_atTop (3:ℝ)))))
    ).exists_forall_of_atTop
  refine ⟨1, x₀, one_pos, ?_⟩
  intro q iq a ha hcop x hxx hqLC
  obtain ⟨hEvA', hEvB', hSmall', hLog4', hX3'⟩ := hx₀ x hxx
  -- basic x facts
  have hxpos : 0 < x := by linarith
  have hLogpos : 0 < Real.log x := by linarith
  have hLognn : 0 ≤ Real.log x := le_of_lt hLogpos
  have hLog1 : 1 ≤ Real.log x := by linarith
  have hspos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLogpos
  have hLApos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hLogpos A
  have hLC1 : 1 ≤ (Real.log x) ^ C := by
    have := Real.rpow_le_rpow (zero_le_one) hLog1 hC.le; rwa [Real.one_rpow] at this
  -- q facts
  have hqpos_nat : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : 1 ≤ q := hqpos_nat
  have hqpos : 0 < (q:ℝ) := by exact_mod_cast hqpos_nat
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  -- T := exp(√log x)
  set T : ℝ := Real.exp (Real.sqrt (Real.log x)) with hTdef
  have hTpos : 0 < T := by rw [hTdef]; exact Real.exp_pos _
  have hs2 : (2:ℝ) ≤ Real.sqrt (Real.log x) := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    calc (2:ℝ) = Real.sqrt 4 := h4.symm
      _ ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt (by linarith)
  have hexp2 : (4:ℝ) ≤ Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [h, Real.exp_pos 1]
  have hTge4 : (4:ℝ) ≤ T := by
    rw [hTdef]
    exact le_trans hexp2 (Real.exp_le_exp.mpr hs2)
  -- smallness: log(q(T+4)) ≤ 2√log x
  have hsmall : Real.log ((q:ℝ) * (T + 4)) ≤ 2 * Real.sqrt (Real.log x) := by
    have hlogmul : Real.log ((q:ℝ) * (T + 4)) = Real.log q + Real.log (T + 4) :=
      Real.log_mul hqpos.ne' (by positivity)
    have hlogq : Real.log q ≤ C * Real.log (Real.log x) := by
      calc Real.log q ≤ Real.log ((Real.log x) ^ C) := Real.log_le_log hqpos hqLC
        _ = C * Real.log (Real.log x) := Real.log_rpow hLogpos C
    have hlogT4 : Real.log (T + 4) ≤ Real.log 2 + Real.sqrt (Real.log x) := by
      have hT2T : T + 4 ≤ 2 * T := by linarith
      calc Real.log (T + 4) ≤ Real.log (2 * T) := Real.log_le_log (by positivity) hT2T
        _ = Real.log 2 + Real.log T := Real.log_mul (by norm_num) (ne_of_gt hTpos)
        _ = Real.log 2 + Real.sqrt (Real.log x) := by rw [hTdef, Real.log_exp]
    rw [hlogmul]; linarith [hlogq, hlogT4, hSmall']
  -- unit witness
  have hau : IsUnit (a : ZMod q) := by rw [ZMod.isUnit_iff_coprime]; exact hcop.symm
  -- the two rpow-power identities used in the counting
  have hLC2 : ((Real.log x) ^ C) ^ 2 = (Real.log x) ^ (2 * C) := by
    rw [← Real.rpow_natCast ((Real.log x) ^ C) 2, ← Real.rpow_mul hLognn]
    congr 1; push_cast; ring
  -- per-character psi1Chi bound for non-principal χ
  have hpsi1_bound : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖psi1Chi x χ‖ ≤ (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x)))
        + (q:ℝ) * Real.log x * x := by
    intro χ hχ1
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hχp_prim : χ.primitiveCharacter.IsPrimitive := χ.primitiveCharacter_isPrimitive
    have hχp_ne1 : χ.primitiveCharacter ≠ 1 := fun h =>
      hχ1 (by rw [← changeLevel_primitiveCharacter χ, h, changeLevel_one])
    have hcond_le : χ.conductor ≤ q := Nat.le_of_dvd hqpos_nat χ.conductor_dvd_level
    have hcondR : (χ.conductor : ℝ) ≤ (q:ℝ) := by exact_mod_cast hcond_le
    have hcondpos : 0 < (χ.conductor : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    have hsmall_p : Real.log ((χ.conductor : ℝ) * (T + 4)) ≤ 2 * Real.sqrt (Real.log x) := by
      have hmono : Real.log ((χ.conductor : ℝ) * (T + 4)) ≤ Real.log ((q:ℝ) * (T + 4)) :=
        Real.log_le_log (mul_pos hcondpos (by linarith [hTge4]))
          (mul_le_mul_of_nonneg_right hcondR (by linarith [hTge4]))
      linarith [hmono, hsmall]
    have hdisp := hchar χ.conductor χ.primitiveCharacter hχp_prim hχp_ne1 hX3' hTdef hsmall_p
    -- ‖ψ₁(x, χ₁)‖ ≤ (Kbig+1) x² e^{−c5√L}
    have hchip_bound : ‖psi1Chi x χ.primitiveCharacter‖
        ≤ (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
      rcases hdisp with hclean | ⟨β₁, hz, _horder, hsq, ⟨hβlo, hβhi⟩, _hβwin, hbnd⟩
      · -- clean branch
        calc ‖psi1Chi x χ.primitiveCharacter‖
            ≤ Kc * x ^ 2 * Real.exp (-(cc * Real.sqrt (Real.log x))) := hclean
          _ ≤ (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
              apply mul_le_mul
              · apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
              · exact Real.exp_le_exp.mpr (by nlinarith [hc5cc, hspos])
              · positivity
              · positivity
      · -- exceptional branch: kill the residue term with Siegel
        have hβpos : 0 < β₁ := by linarith
        have hsieg := hCₛ χ.conductor χ.primitiveCharacter hχp_prim hsq hχp_ne1 hz hβhi
        have h1mβ : Cₛ / (χ.conductor : ℝ) ^ ε ≤ 1 - β₁ := by linarith [hsieg]
        have hcondge1 : (1:ℝ) ≤ (χ.conductor : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne χ.conductor)
        have hfεpos : 0 < (χ.conductor : ℝ) ^ ε := Real.rpow_pos_of_pos (by linarith) ε
        have hfε : (χ.conductor : ℝ) ^ ε ≤ (Real.log x) ^ ((1:ℝ)/4) := by
          calc (χ.conductor : ℝ) ^ ε ≤ (q:ℝ) ^ ε :=
                Real.rpow_le_rpow (by linarith) hcondR hεpos.le
            _ ≤ ((Real.log x) ^ C) ^ ε := Real.rpow_le_rpow (by positivity) hqLC hεpos.le
            _ = (Real.log x) ^ (C * ε) := (Real.rpow_mul hLognn C ε).symm
            _ = (Real.log x) ^ ((1:ℝ)/4) := by rw [hCε]
        have hL14pos : 0 < (Real.log x) ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hLogpos _
        have h1mβ2 : Cₛ / (Real.log x) ^ ((1:ℝ)/4) ≤ 1 - β₁ := by
          have hle : Cₛ / (Real.log x) ^ ((1:ℝ)/4) ≤ Cₛ / (χ.conductor : ℝ) ^ ε := by
            gcongr
          linarith [hle, h1mβ]
        -- Cₛ√L ≤ (1−β₁)L
        have hsLL : Real.log x / (Real.log x) ^ ((1:ℝ)/4) = (Real.log x) ^ ((3:ℝ)/4) := by
          rw [show (3:ℝ)/4 = 1 - 1/4 by norm_num, Real.rpow_sub hLogpos, Real.rpow_one]
        have hCₛL : Cₛ / (Real.log x) ^ ((1:ℝ)/4) * Real.log x
            = Cₛ * (Real.log x) ^ ((3:ℝ)/4) := by
          rw [div_mul_eq_mul_div, mul_div_assoc, hsLL]
        have h34 : Real.sqrt (Real.log x) ≤ (Real.log x) ^ ((3:ℝ)/4) := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_le hLog1 (by norm_num)
        have hstep : Cₛ * Real.sqrt (Real.log x) ≤ (1 - β₁) * Real.log x := by
          calc Cₛ * Real.sqrt (Real.log x)
              ≤ Cₛ * (Real.log x) ^ ((3:ℝ)/4) := mul_le_mul_of_nonneg_left h34 hCₛpos.le
            _ = Cₛ / (Real.log x) ^ ((1:ℝ)/4) * Real.log x := hCₛL.symm
            _ ≤ (1 - β₁) * Real.log x := mul_le_mul_of_nonneg_right h1mβ2 hLognn
        -- the residue-term norm bound
        have hden1 : (1:ℝ) ≤ β₁ * (β₁ + 1) := by nlinarith [hβlo]
        have hnorm_exc : ‖(x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1))‖
            = x ^ (β₁ + 1) / (β₁ * (β₁ + 1)) := norm_exc_term x β₁ hxpos hβpos
        have hexc1 : ‖(x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1))‖ ≤ x ^ (β₁ + 1) := by
          rw [hnorm_exc]; exact div_le_self (Real.rpow_nonneg hxpos.le _) hden1
        have hxβ : x ^ (β₁ + 1) = x ^ 2 * Real.exp (-((1 - β₁) * Real.log x)) := by
          rw [show β₁ + 1 = (2:ℝ) + (β₁ - 1) by ring, Real.rpow_add hxpos]
          congr 1
          · rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
          · rw [Real.rpow_def_of_pos hxpos]; congr 1; ring
        have hexc_le : ‖(x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1))‖
            ≤ x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
          have hxβ_le : x ^ (β₁ + 1) ≤ x ^ 2 * Real.exp (-(Cₛ * Real.sqrt (Real.log x))) := by
            rw [hxβ]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.exp_le_exp.mpr (by linarith [hstep])
          have hstep2 : x ^ 2 * Real.exp (-(Cₛ * Real.sqrt (Real.log x)))
              ≤ x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.exp_le_exp.mpr (by nlinarith [hc5Cs, hspos])
          linarith [hexc1, hxβ_le, hstep2]
        -- combine: ‖ψ₁(χ₁)‖ ≤ ‖ψ₁(χ₁)+exc‖ + ‖exc‖
        have heq2 : psi1Chi x χ.primitiveCharacter
            = (psi1Chi x χ.primitiveCharacter
                + (x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1)))
              - (x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1)) := by abel
        calc ‖psi1Chi x χ.primitiveCharacter‖
            = ‖(psi1Chi x χ.primitiveCharacter
                  + (x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1)))
                - (x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1))‖ := by rw [← heq2]
          _ ≤ ‖psi1Chi x χ.primitiveCharacter
                  + (x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1))‖
                + ‖(x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1))‖ := norm_sub_le _ _
          _ ≤ Kc * x ^ 2 * Real.exp (-(cc * Real.sqrt (Real.log x)))
                + x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := add_le_add hbnd hexc_le
          _ ≤ (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
              have hkc : Kc * x ^ 2 * Real.exp (-(cc * Real.sqrt (Real.log x)))
                  ≤ Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_right hKcKbig (by positivity)
                · exact Real.exp_le_exp.mpr (by nlinarith [hc5cc, hspos])
                · positivity
                · positivity
              nlinarith [hkc]
    -- transfer to χ
    have htransfer := psi1_transfer χ (by linarith : (1:ℝ) ≤ x)
    have htr2 : ‖psi1Chi x χ - psi1Chi x χ.primitiveCharacter‖ ≤ (q:ℝ) * Real.log x * x := by
      calc ‖psi1Chi x χ - psi1Chi x χ.primitiveCharacter‖
          ≤ (q.primeFactors.card : ℝ) * Real.log x * x := htransfer
        _ ≤ (q:ℝ) * Real.log x * x := by
            apply mul_le_mul_of_nonneg_right _ hxpos.le
            exact mul_le_mul_of_nonneg_right (primeFactors_card_le_self q) hLognn
    have heq1 : psi1Chi x χ.primitiveCharacter
        + (psi1Chi x χ - psi1Chi x χ.primitiveCharacter) = psi1Chi x χ := by abel
    calc ‖psi1Chi x χ‖
        = ‖psi1Chi x χ.primitiveCharacter
            + (psi1Chi x χ - psi1Chi x χ.primitiveCharacter)‖ := by rw [heq1]
      _ ≤ ‖psi1Chi x χ.primitiveCharacter‖
            + ‖psi1Chi x χ - psi1Chi x χ.primitiveCharacter‖ := norm_add_le _ _
      _ ≤ (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x)))
            + (q:ℝ) * Real.log x * x := add_le_add hchip_bound htr2
  -- the χ₀ (principal) main-term bound
  have hχ0bound : ‖psi1Chi x (1 : DirichletCharacter ℂ q) - (x:ℂ) ^ 2 / 2‖
      ≤ Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
    calc ‖psi1Chi x (1 : DirichletCharacter ℂ q) - (x:ℂ) ^ 2 / 2‖
        ≤ Kt * x ^ 2 * Real.exp (-(ct * Real.sqrt (Real.log x))) := htriv q hX3' hTdef hsmall
      _ ≤ Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hKtKbig (by positivity)
          · exact Real.exp_le_exp.mpr (by nlinarith [hc5ct, hspos])
          · positivity
          · positivity
  -- assemble the sum bound
  set Gval : ℝ := (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x)))
    + (q:ℝ) * Real.log x * x with hGvaldef
  have hGnn : 0 ≤ Gval := by rw [hGvaldef]; positivity
  have hsumbound : ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖ ≤ (q:ℝ) * Gval := by
    have hper : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        ‖(starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖ ≤ Gval := by
      intro χ hχ
      have hχ1 : χ ≠ 1 := Finset.ne_of_mem_erase hχ
      have hcoef : ‖(starRingEnd ℂ) (χ (a : ZMod q))‖ ≤ 1 := by
        rw [Complex.norm_conj]; exact DirichletCharacter.norm_le_one χ _
      calc ‖(starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖
          = ‖(starRingEnd ℂ) (χ (a : ZMod q))‖ * ‖psi1Chi x χ‖ := norm_mul _ _
        _ ≤ 1 * ‖psi1Chi x χ‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
        _ = ‖psi1Chi x χ‖ := one_mul _
        _ ≤ Gval := hpsi1_bound χ hχ1
    calc ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖
        ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖(starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖ := norm_sum_le _ _
      _ ≤ ∑ _χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), Gval := Finset.sum_le_sum hper
      _ = ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) * Gval := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q:ℝ) * Gval := by
          apply mul_le_mul_of_nonneg_right _ hGnn
          calc ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ)
              ≤ (Fintype.card (DirichletCharacter ℂ q) : ℝ) := by
                exact_mod_cast le_trans (Finset.card_erase_le)
                  (le_of_eq (Finset.card_univ))
            _ ≤ (q:ℝ) := card_dirichletCharacter_le q
  -- the fold identity and the principal-character extraction
  have hf1val : (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) (a : ZMod q))
      * psi1Chi x (1 : DirichletCharacter ℂ q) = psi1Chi x (1 : DirichletCharacter ℂ q) := by
    rw [MulChar.one_apply hau, map_one, one_mul]
  have hDnorm : |(q.totient : ℝ) * psi1AP x q a - x ^ 2 / 2|
      = ‖(q.totient : ℂ) * (psi1AP x q a : ℂ) - (x:ℂ) ^ 2 / 2‖ := by
    rw [show (q.totient : ℂ) * (psi1AP x q a : ℂ) - (x:ℂ) ^ 2 / 2
          = (((q.totient : ℝ) * psi1AP x q a - x ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  -- the master estimate
  have hmaster : ‖(q.totient : ℂ) * (psi1AP x q a : ℂ) - (x:ℂ) ^ 2 / 2‖
      ≤ Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) + (q:ℝ) * Gval := by
    rw [← psi1_fold x ha hcop]
    calc ‖(∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ)
            - (x:ℂ) ^ 2 / 2‖
        = ‖(psi1Chi x (1 : DirichletCharacter ℂ q) - (x:ℂ) ^ 2 / 2)
            + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖ := by
          rw [← Finset.add_sum_erase Finset.univ
            (fun χ => (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ)
            (Finset.mem_univ (1 : DirichletCharacter ℂ q))]
          rw [hf1val]; ring_nf
      _ ≤ ‖psi1Chi x (1 : DirichletCharacter ℂ q) - (x:ℂ) ^ 2 / 2‖
            + ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖ := norm_add_le _ _
      _ ≤ Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) + (q:ℝ) * Gval :=
          add_le_add hχ0bound hsumbound
  -- the final absorption arithmetic
  rw [hDnorm]
  refine le_trans hmaster ?_
  -- Kbig x² e + q Gval ≤ (2Kbig+1) L^C x² e + L^{2C+1} x
  have hbound1 : Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) + (q:ℝ) * Gval
      ≤ (2 * Kbig + 1) * (Real.log x) ^ C * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x)))
        + (Real.log x) ^ (2 * C + 1) * x := by
    have he : 0 ≤ Real.exp (-(c5 * Real.sqrt (Real.log x))) := (Real.exp_pos _).le
    have hx2 : 0 ≤ x ^ 2 := by positivity
    -- term-by-term
    have ht1 : Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x)))
        ≤ Kbig * (Real.log x) ^ C * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
      have hkb : Kbig ≤ Kbig * (Real.log x) ^ C := by nlinarith [hLC1, hKbigpos]
      nlinarith [hkb, mul_nonneg hx2 he]
    have ht2 : (q:ℝ) * ((Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))))
        ≤ (Real.log x) ^ C * (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
      have hM : 0 ≤ (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by positivity
      calc (q:ℝ) * ((Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))))
          ≤ (Real.log x) ^ C * ((Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x)))) :=
            mul_le_mul_of_nonneg_right hqLC hM
        _ = (Real.log x) ^ C * (Kbig + 1) * x ^ 2
            * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by ring
    have ht3 : (q:ℝ) * ((q:ℝ) * Real.log x * x) ≤ (Real.log x) ^ (2 * C + 1) * x := by
      have hq2 : (q:ℝ) * (q:ℝ) ≤ (Real.log x) ^ (2 * C) := by
        calc (q:ℝ) * (q:ℝ) ≤ (Real.log x) ^ C * (Real.log x) ^ C := by nlinarith [hqLC, hqpos, hLC1]
          _ = ((Real.log x) ^ C) ^ 2 := by ring
          _ = (Real.log x) ^ (2 * C) := hLC2
      have hLprod : (Real.log x) ^ (2 * C) * Real.log x = (Real.log x) ^ (2 * C + 1) := by
        rw [show (2 * C + 1 : ℝ) = 2 * C + 1 by ring, Real.rpow_add hLogpos, Real.rpow_one]
      calc (q:ℝ) * ((q:ℝ) * Real.log x * x) = ((q:ℝ) * (q:ℝ)) * Real.log x * x := by ring
        _ ≤ (Real.log x) ^ (2 * C) * Real.log x * x := by
            apply mul_le_mul_of_nonneg_right _ hxpos.le
            exact mul_le_mul_of_nonneg_right hq2 hLognn
        _ = (Real.log x) ^ (2 * C + 1) * x := by rw [hLprod]
    have hGexp : (q:ℝ) * Gval
        = (q:ℝ) * ((Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))))
          + (q:ℝ) * ((q:ℝ) * Real.log x * x) := by rw [hGvaldef]; ring
    rw [hGexp]
    nlinarith [ht1, ht2, ht3]
  refine le_trans hbound1 ?_
  -- (2Kbig+1) L^C x² e + L^{2C+1} x ≤ x²/L^A
  have hLApos2 : (0:ℝ) < 2 * (Real.log x) ^ A := by positivity
  have hA1 : (2 * Kbig + 1) * (Real.log x) ^ C * x ^ 2
        * Real.exp (-(c5 * Real.sqrt (Real.log x)))
      ≤ x ^ 2 / (2 * (Real.log x) ^ A) := by
    rw [le_div_iff₀ hLApos2]
    calc (2 * Kbig + 1) * (Real.log x) ^ C * x ^ 2
            * Real.exp (-(c5 * Real.sqrt (Real.log x))) * (2 * (Real.log x) ^ A)
        = ((2 * Kbig + 1) * ((Real.log x) ^ C * (Real.log x) ^ A)
            * Real.exp (-(c5 * Real.sqrt (Real.log x)))) * (2 * x ^ 2) := by ring
      _ = ((2 * Kbig + 1) * (Real.log x) ^ (C + A)
            * Real.exp (-(c5 * Real.sqrt (Real.log x)))) * (2 * x ^ 2) := by
            rw [← Real.rpow_add hLogpos]
      _ ≤ (1/2) * (2 * x ^ 2) := by
            apply mul_le_mul_of_nonneg_right hEvA' (by positivity)
      _ = x ^ 2 := by ring
  have hB1 : (Real.log x) ^ (2 * C + 1) * x ≤ x ^ 2 / (2 * (Real.log x) ^ A) := by
    rw [le_div_iff₀ hLApos2]
    calc (Real.log x) ^ (2 * C + 1) * x * (2 * (Real.log x) ^ A)
        = (2 * ((Real.log x) ^ (2 * C + 1) * (Real.log x) ^ A)) * x := by ring
      _ = (2 * (Real.log x) ^ (2 * C + 1 + A)) * x := by rw [← Real.rpow_add hLogpos]
      _ ≤ x * x := by
          apply mul_le_mul_of_nonneg_right _ hxpos.le
          have hb := hEvB'
          rw [div_le_iff₀ hxpos] at hb
          linarith [hb]
      _ = x ^ 2 := by ring
  have hhalf : x ^ 2 / (2 * (Real.log x) ^ A) + x ^ 2 / (2 * (Real.log x) ^ A)
      = 1 * x ^ 2 / (Real.log x) ^ A := by
    field_simp
    ring
  rw [← hhalf]
  linarith [hA1, hB1]

end Salt.SW
