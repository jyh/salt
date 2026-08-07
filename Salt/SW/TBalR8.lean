/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.TBalR7
import Salt.SW.DHBalance

/-!
# T-BAL R8 — `dh_repulsion_ordered` (the parameter-selection + ledger-inversion endgame)

The single remaining rung of the T-BAL campaign.  The target is the reversed-Jutila repulsion
contract (`DHRepulsion.lean:267`): for a real primitive `χ` with a real zero `β₀ ∈ (1/2, 1)` and a
non-real zero `ρ` with `16/17 ≤ Re ρ < 1`, `Re ρ ≤ β₀`,

  `1 − β₀ ≥ c·(q(|Im ρ|+2))^{−b(1−Re ρ)}/(log(q(|Im ρ|+2))+2)^k`,   `b=680, k=14`, `c` the
  explicit `min` tower of `dh_repulsion_ordered` below.

**Mechanism (the freeze master, `docs/exploration/tbal-s0-freeze.md`:11 + AMENDMENT 1).**
Write `u := 1−β₀`, `σ := Re ρ`, `Q := q(|Im ρ|+2)`, `L₂ := log Q + 2`, `τ := c·Q^{−bu_σ}/L₂^k`
with `u_σ := 1−σ`.  The contract is `u ≥ τ`, split at the trivial floor `1/(40 L₂)`:

* **trivial branch** `u ≥ 1/(40 L₂)`: since `τ ≤ 1/(40 L₂)` (`tbal_tau_le_split`), done directly;
* **deep branch** `u < 1/(40 L₂)`, `by_contra u < τ`: at the ledger scales the detector balance
  forces `3/4 ≤ (five small rows)`, each `≤ 10^{−5.65}` on the ray `u < τ`, summing `< 3/4` —
  the contradiction.  The rows are the `dh_balance` chain kept in TIGHT form (the `x^u−1 ≈ u·ln x`
  cancellation retained, not discarded as in `dh_balance`'s loose bracket), the ρ-main injected
  with its `u` factor via `H_lower` (`L₁·selMainTerm ≤ u(2−β₀)`).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open Complex Finset

noncomputable section

namespace Salt.SW

/-! ## §1 — the trivial-branch arithmetic -/

/-- **Trivial-branch bound.** The contract RHS `τ = c·Q^{−680w}/L₂^{14}` (`L₂ = log Q + 2`) is
`≤ 1/(40 L₂)` for any `Q ≥ 1`, `w > 0` and ANY `0 ≤ c ≤ 1`.  Hence in the trivial branch
`1/(40 L₂) ≤ u` the target `u ≥ τ` is immediate.  Pure `rpow` arithmetic: `Q^{−680w} ≤ 1`,
`40·c ≤ 40 < 8192 ≤ L₂^{13}`, `L₂^{14} = L₂^{13}·L₂`.

**TAU-SHARP S1.** The `c` was formerly the hard-wired literal `2^{−250}`; the proof only ever
used `0 ≤ c` and `c ≤ 1`, so it is now stated at that honest hypothesis set.  This retires the
`2^{−250}` arm of the `c`-min tower (which becomes the inert `1/40`) without disturbing a single
`min`-projection index, and it is already the shape a later `(b, k)`-parametrisation wants. -/
lemma tbal_tau_le_split {Q w c : ℝ} (hQ : 1 ≤ Q) (hw : 0 < w) (hc0 : 0 ≤ c) (hc : c ≤ 1) :
    c * Q ^ (-(680 * w)) / (Real.log Q + 2) ^ (14 : ℝ)
      ≤ 1 / (40 * (Real.log Q + 2)) := by
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hL2 : (2 : ℝ) ≤ Real.log Q + 2 := by linarith
  have hLpos : (0 : ℝ) < Real.log Q + 2 := by linarith
  have hQpow : Q ^ (-(680 * w)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hQ (by nlinarith [hw])
  have hQpownn : (0 : ℝ) ≤ Q ^ (-(680 * w)) := (Real.rpow_pos_of_pos (by linarith) _).le
  have hL14pos : (0 : ℝ) < (Real.log Q + 2) ^ (14 : ℝ) := Real.rpow_pos_of_pos hLpos _
  -- `L₂^{13} ≥ 2^{13} = 8192`
  have hL13 : (8192 : ℝ) ≤ (Real.log Q + 2) ^ (13 : ℝ) := by
    have h2 : (2 : ℝ) ^ (13 : ℝ) ≤ (Real.log Q + 2) ^ (13 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hL2 (by norm_num)
    have : (2 : ℝ) ^ (13 : ℝ) = 8192 := by
      rw [show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    linarith [this ▸ h2]
  -- `L₂^{14} = L₂^{13}·L₂`
  have hsplit : (Real.log Q + 2) ^ (14 : ℝ)
      = (Real.log Q + 2) ^ (13 : ℝ) * (Real.log Q + 2) := by
    rw [show (14 : ℝ) = 13 + 1 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
  rw [div_le_div_iff₀ hL14pos (by positivity : (0 : ℝ) < 40 * (Real.log Q + 2))]
  -- goal: c·Q^{−680w}·(40 L₂) ≤ 1·L₂^{14}
  rw [hsplit]
  have hstep : c * Q ^ (-(680 * w)) * (40 * (Real.log Q + 2))
      ≤ 8192 * (Real.log Q + 2) := by
    have h1 : c * Q ^ (-(680 * w)) ≤ 1 := by
      calc c * Q ^ (-(680 * w))
          ≤ 1 * 1 := mul_le_mul hc hQpow hQpownn (by norm_num)
        _ = 1 := by norm_num
    nlinarith [mul_nonneg hc0 hQpownn, hLpos]
  calc c * Q ^ (-(680 * w)) * (40 * (Real.log Q + 2))
      ≤ 8192 * (Real.log Q + 2) := hstep
    _ ≤ (Real.log Q + 2) ^ (13 : ℝ) * (Real.log Q + 2) := by
        apply mul_le_mul_of_nonneg_right hL13 hLpos.le
    _ = 1 * ((Real.log Q + 2) ^ (13 : ℝ) * (Real.log Q + 2)) := by ring

/-! ## §2 — the TIGHT master (the freeze `3/4 ≤ rows`, ready for the on-ray caps) -/

variable {q : ℕ}

set_option maxHeartbeats 1600000 in
-- The balance chain threads floor + shift + β₀-cancellation + ρ-norm over the
-- `(1−ρ)(2−ρ)`/selMainTerm denominators; the rearrangement exceeds the default budget (as in
-- `dh_balance`).
/-- **The tight ray master.** Same guards as `dh_balance`, but the balance is kept in TIGHT form:
the `x^u−1` cancellation (`tail_shift_to_beta0`, the `−(1−1/Y)`) is RETAINED, and the ρ-main term
`L₁·selMainTerm·Y^{1−σ}/(‖1−ρ‖‖2−ρ‖)` is bounded via `H_lower` (`L₁·selMainTerm ≤ (1−β₀)(2−β₀)`),
injecting its `u = 1−β₀` factor.  The result is the freeze master `1 − 1/Y ≤ (ρ-row) + (Eρ-row) +
Y^{β₀−σ}((Y^{1−β₀}+Eβ) − (1−1/Y))`, each RHS row small on the ray `u < τ` (the on-ray caps of §3
close the contradiction). -/
theorem dh_master_ray [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β₀ : ℝ}
    (hzeroβ : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0) (hloβ : 1 / 2 ≤ β₀) (hhiβ : β₀ < 1)
    {ρ : ℂ} (hzeroρ : DirichletCharacter.LFunction χ ρ = 0) (hloρ : 1 / 2 ≤ ρ.re) (hhiρ : ρ.re < 1)
    (himρ : |ρ.im| ≤ 1) (hord : ρ.re ≤ β₀)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {N : ℕ} (hN : 4 ≤ N) (hscale : (N : ℝ) ^ (1 - β₀) ≤ Real.exp 1)
    (hguard : 2 * (34 + 12 * (Real.sqrt q * (1 + Real.log q))
        + 12 * (Real.sqrt q * (1 + Real.log q)) * Z₀
        + 36 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀)) * (N : ℝ) ^ (1 / 2 - β₀) ≤ 1 / 64)
    {z Y : ℕ} (hz : 2 ≤ z) (hY : 2 * z ^ 4 ≤ Y)
    (hcov : crushErr q Z₀ β₀ z ≤ 27 / 100 * ((1 - β₀) * (z : ℝ) ^ (1 - β₀))) :
    1 - 1 / (Y : ℝ)
      ≤ (1 - β₀) * (2 - β₀) * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖)
        + C2Rho q Z₀ ρ * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - ρ.re)
        + (Y : ℝ) ^ (β₀ - ρ.re) * ((Y : ℝ) ^ (1 - β₀)
            + (136 + 48 * (Real.sqrt q * (1 + Real.log q))
                + 48 * (Real.sqrt q * (1 + Real.log q)) * Z₀
                + 144 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀))
              * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀)
            - (1 - 1 / (Y : ℝ))) := by
  set L₁re : ℝ := (DirichletCharacter.LFunction χ 1).re with hL1re
  set Eβ : ℝ := (136 + 48 * (Real.sqrt q * (1 + Real.log q))
      + 48 * (Real.sqrt q * (1 + Real.log q)) * Z₀
      + 144 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀))
    * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀) with hEβ
  set Eρ : ℝ := C2Rho q Z₀ ρ * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9
    * (Y : ℝ) ^ (1 / 2 - ρ.re) with hEρ
  have hσ0 : 0 < ρ.re := by linarith
  have hu : 0 < 1 - β₀ := by linarith
  have hu2 : 0 < 2 - β₀ := by linarith
  have hDpos : 0 < (1 - β₀) * (2 - β₀) := mul_pos hu hu2
  have hz1 : 1 ≤ z := by omega
  have hY1 : 1 ≤ Y := by have := Nat.one_le_pow 4 z (by omega); omega
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY1
  have hne : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hhiρ; simp at hhiρ
  have hsne : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (fun h => hρ1 h.symm)
  have hnpos : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hsne
  have h2ρne : (2 - ρ) ≠ 0 := by
    intro h; have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, Complex.re_ofNat] at this; linarith
  have h2npos : 0 < ‖2 - ρ‖ := norm_pos_iff.mpr h2ρne
  have hselM : 0 < selMainTerm χ z := by
    rw [selberg_opt_eq χ hsq hz1]; exact one_div_pos.mpr (selHSum_pos χ hsq hz1)
  -- coefficient facts
  have hcnn : ∀ n, 0 ≤ dhCoeffW χ (selWeight χ z) n := by
    intro n; rcases eq_or_ne n 0 with rfl | hn
    · simp [dhCoeffW, dhWeightSqW, dhA]
    · exact dhCoeffW_nonneg χ hsq _ hn
  have hc1 : dhCoeffW χ (selWeight χ z) 1 = 1 := by
    rw [dhCoeffW_one, selWeight_apply_one χ hsq hz1, one_pow]
  -- floor : 1 − 1/Y ≤ ‖D_ρ‖ + S₀
  have hfloor := dhW_detector_floor_rho χ hsq hσ0 hz1 hY1
  -- R1 shift (TIGHT) : S₀ ≤ Y^{β₀−σ}·(D₀^{β₀} − (1−1/Y))
  have hshift := tail_shift_to_beta0 (c := dhCoeffW χ (selWeight χ z)) hcnn hc1
    (x := (Y : ℝ)) (by exact_mod_cast hY1) (N := Y) hY1 (σ := ρ.re) (β₀ := β₀) hord
  -- β₀-side : D₀^{β₀} ≤ Y^{1−β₀} + E(β₀)
  have hR6β := dh_extraction_upper_W χ hχ hsq hq hzeroβ hloβ hhiβ hZ hz1 hY
  have hHl := H_lower χ hχ hsq hq hzeroβ hloβ hhiβ hZ hN hscale hguard hz hcov
  have hopt := selberg_opt_eq χ hsq hz1
  have hHpos := selHSum_pos χ hsq hz1
  have hYβrp : (0 : ℝ) ≤ (Y : ℝ) ^ (1 - β₀) := Real.rpow_nonneg hYpos.le _
  have hcancel : L₁re * selMainTerm χ z * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))
      ≤ (Y : ℝ) ^ (1 - β₀) := by
    rw [hopt]
    have hrw : L₁re * (1 / selHSum χ z) * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))
        = (L₁re / ((1 - β₀) * (2 - β₀)) / selHSum χ z) * (Y : ℝ) ^ (1 - β₀) := by field_simp
    rw [hrw]
    calc (L₁re / ((1 - β₀) * (2 - β₀)) / selHSum χ z) * (Y : ℝ) ^ (1 - β₀)
        ≤ 1 * (Y : ℝ) ^ (1 - β₀) :=
          mul_le_mul_of_nonneg_right ((div_le_one hHpos).mpr hHl) hYβrp
      _ = (Y : ℝ) ^ (1 - β₀) := one_mul _
  have hD0β : ∑ n ∈ Finset.Icc 1 Y, dhCoeffW χ (selWeight χ z) n * (n : ℝ) ^ (-β₀)
        * dhKernR ((n : ℝ) / (Y : ℝ))
      ≤ (Y : ℝ) ^ (1 - β₀) + Eβ := by
    rw [← hL1re, ← hEβ] at *
    linarith [(abs_le.mp hR6β).2, hcancel]
  -- the ρ-main norm identity and the u-injection
  have hR6ρ := dh_extraction_upper_rho χ hχ hsq hq hzeroρ hloρ hhiρ himρ hZ hz1 hY
  rw [← hEρ] at hR6ρ
  have hmain_norm : ‖DirichletCharacter.LFunction χ 1 * (selMainTerm χ z : ℂ) * (Y : ℂ) ^ (1 - ρ)
        / ((1 - ρ) * (2 - ρ))‖
      = L₁re * selMainTerm χ z * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_LFunction_one_eq_re χ hne hsq, ← hL1re,
      show ‖(selMainTerm χ z : ℂ)‖ = selMainTerm χ z from by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hselM.le],
      show ‖(Y : ℂ) ^ (1 - ρ)‖ = (Y : ℝ) ^ (1 - ρ.re) from by
        rw [show (Y : ℂ) = ((Y : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
        rw [Complex.sub_re, Complex.one_re]]
  have hDρnorm : ‖∑ n ∈ Finset.Icc 1 Y, (dhCoeffW χ (selWeight χ z) n : ℂ) * (n : ℂ) ^ (-ρ)
        * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ)‖
      ≤ L₁re * selMainTerm χ z * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖) + Eρ := by
    have htri := norm_sub_norm_le (∑ n ∈ Finset.Icc 1 Y, (dhCoeffW χ (selWeight χ z) n : ℂ)
        * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ))
      (DirichletCharacter.LFunction χ 1 * (selMainTerm χ z : ℂ) * (Y : ℂ) ^ (1 - ρ)
        / ((1 - ρ) * (2 - ρ)))
    rw [hmain_norm] at htri
    linarith [htri, hR6ρ]
  -- u-injection : L₁re·selMainTerm ≤ (1−β₀)(2−β₀)
  have hLselM : L₁re * selMainTerm χ z ≤ (1 - β₀) * (2 - β₀) := by
    have hle : L₁re ≤ selHSum χ z * ((1 - β₀) * (2 - β₀)) := (div_le_iff₀ hDpos).mp hHl
    rw [hopt, mul_one_div, div_le_iff₀ hHpos]
    nlinarith [hle]
  have hKnn : (0 : ℝ) ≤ (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖) := by positivity
  have hmainρ_le : L₁re * selMainTerm χ z * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖)
      ≤ (1 - β₀) * (2 - β₀) * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖) := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hLselM hKnn
  -- combine : the tight master
  have hYβσ : (0 : ℝ) ≤ (Y : ℝ) ^ (β₀ - ρ.re) := Real.rpow_nonneg hYpos.le _
  have hSshift : ∑ n ∈ Finset.Icc 2 Y, dhCoeffW χ (selWeight χ z) n * (n : ℝ) ^ (-ρ.re)
        * dhKernR ((n : ℝ) / (Y : ℝ))
      ≤ (Y : ℝ) ^ (β₀ - ρ.re) * (((Y : ℝ) ^ (1 - β₀) + Eβ) - (1 - 1 / (Y : ℝ))) := by
    refine le_trans hshift ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hD0β]) hYβσ
  linarith [hfloor, hSshift, hDρnorm, hmainρ_le]

/-! ## §3 — the transcendental on-ray helpers (log → pure rpow, the crude-δ trick) -/

/-- `exp s − 1 ≤ e·s` on `[0,1]`.  From `1−s ≤ exp(−s)` (`add_one_le_exp`) times `exp s`:
`exp s·(1−s) ≤ 1`, so `exp s − 1 ≤ s·exp s ≤ s·exp 1`. -/
lemma exp_sub_one_le_e_mul {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp s - 1 ≤ Real.exp 1 * s := by
  have hexps : 0 < Real.exp s := Real.exp_pos s
  have h1 : 1 - s ≤ Real.exp (-s) := by linarith [Real.add_one_le_exp (-s)]
  have h2 : Real.exp s * (1 - s) ≤ 1 := by
    calc Real.exp s * (1 - s) ≤ Real.exp s * Real.exp (-s) :=
          mul_le_mul_of_nonneg_left h1 hexps.le
      _ = 1 := by rw [← Real.exp_add]; simp
  have h3 : Real.exp s - 1 ≤ s * Real.exp s := by nlinarith [h2]
  have h4 : Real.exp s ≤ Real.exp 1 := Real.exp_le_exp.mpr hs1
  calc Real.exp s - 1 ≤ s * Real.exp s := h3
    _ ≤ s * Real.exp 1 := mul_le_mul_of_nonneg_left h4 hs0
    _ = Real.exp 1 * s := by ring

/-- **`a^t − 1 ≤ e·(t·log a)`** for `a ≥ 1`, `t ≥ 0`, `t·log a ≤ 1`.  The `Y^u − 1 ≈ u·ln Y`
cancellation that makes the A-row `u`-small on the ray. -/
lemma rpow_sub_one_le {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) (hprod : t * Real.log a ≤ 1) :
    a ^ t - 1 ≤ Real.exp 1 * (t * Real.log a) := by
  have hapos : 0 < a := by linarith
  have hloga : 0 ≤ Real.log a := Real.log_nonneg ha
  have hs0 : 0 ≤ t * Real.log a := mul_nonneg ht hloga
  have heq : a ^ t = Real.exp (t * Real.log a) := by
    rw [Real.rpow_def_of_pos hapos]; ring_nf
  rw [heq]
  exact exp_sub_one_le_e_mul hs0 hprod

/-- **`−log u ≤ u^{−δ}/δ`** for `0 < u`, `δ > 0`.  The crude sub-power bound on `log(1/u)`
(mathlib `Real.log_le_rpow_div`) that turns every on-ray `log(1/u)` factor into a pure
(monotone-in-`u`) power `u^{−δ}`. -/
lemma neg_log_le_rpow {u δ : ℝ} (hu0 : 0 < u) (hδ : 0 < δ) :
    -Real.log u ≤ u ^ (-δ) / δ := by
  have hstep : Real.log u⁻¹ ≤ (u⁻¹) ^ δ / δ := Real.log_le_rpow_div (inv_pos.mpr hu0).le hδ
  rw [Real.log_inv] at hstep
  rwa [Real.inv_rpow hu0.le, ← Real.rpow_neg hu0.le] at hstep

/-- **`−log u ≤ u^{−δ}/(e·δ)`** for `0 < u`, `δ > 0` — the SHARP form of `neg_log_le_rpow`,
a factor `e = 2.718…` better.  (TAU-SHARP S5(a).)  Proof: `log y ≤ y/e` for `y > 0` — apply
`Real.log_le_sub_one_of_pos` at `y/e` to get `log y − 1 ≤ y/e − 1` — then take `y = u^{−δ}`,
whose log is `−δ·log u`.  Landed additively: `neg_log_le_rpow` keeps its callers at
`δ = 1/50` (`row_A_cap`) and `δ = 1/2` (the crush bookkeeping), where the constant is inert. -/
lemma neg_log_le_rpow' {u δ : ℝ} (hu0 : 0 < u) (hδ : 0 < δ) :
    -Real.log u ≤ u ^ (-δ) / (Real.exp 1 * δ) := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hy : (0 : ℝ) < u ^ (-δ) := Real.rpow_pos_of_pos hu0 _
  -- `log y ≤ y/e` for `y > 0`, from `log(y/e) ≤ y/e − 1`
  have hle : Real.log (u ^ (-δ)) ≤ u ^ (-δ) / Real.exp 1 := by
    have hd := Real.log_le_sub_one_of_pos (div_pos hy he)
    rw [Real.log_div hy.ne' he.ne', Real.log_exp] at hd
    linarith
  rw [Real.log_rpow hu0, le_div_iff₀ he] at hle
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.exp 1 * δ)]
  calc -Real.log u * (Real.exp 1 * δ) = -δ * Real.log u * Real.exp 1 := by ring
    _ ≤ u ^ (-δ) := hle

/-! ## §4 — the on-ray row caps (the exponent-balance; `b = 680` absorbs the `Q`/`L₂` powers) -/

/-- **The ρ-row on-ray cap (the exponent-balance template).** For `0 < w ≤ 1/17` (`w = 1−σ`),
`Q ≥ 4`, `0 < u ≤ τ := c·Q^{−680w}/(log Q+2)^{14}`, and a detector length `0 < Y ≤ 2Q^{104}u^{−14}`,
the ρ-row's crude upper bound `2u·Y^{w}·(log Q/c₀)` is `≤ (4/c₀)·c^{1−14w}`.

This is THE reusable template for all five master rows: `Y^w ≤ 2^w Q^{104w}u^{−14w}`, then
`u^{1−14w} ≤ τ^{1−14w}` (pure `rpow` monotonicity, `1−14w ≥ 3/17 > 0`), then the `Q`-power
`104w−680w(1−14w) = w(−576+9520w) ≤ 0` and the `L₂`-power `1−14(1−14w) = −13+196w ≤ 0` are BOTH
nonpositive on `w ≤ 1/17` — the `b = 680`/`k = 14`/`σ₀ = 16/17` window law — so `Q^{…}, L₂^{…} ≤ 1`,
leaving only the constant `(4/c₀)·c^{1−14w}`.  The remaining rows (Eρ, A, Eβ, 1/x) follow the
same skeleton with `rpow_sub_one_le`/`neg_log_le_rpow` handling their `Y^u−1`/`log z` factors. -/
lemma rho_row_power_bound {w Q u c c₀ Y : ℝ} (hw0 : 0 < w) (hw : w ≤ 1 / 17) (hQ : 4 ≤ Q)
    (hu0 : 0 < u) (hc0 : 0 < c₀) (hcc : 0 < c) (hY0 : 0 < Y)
    (hYub : Y ≤ 2 * Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)))
    (huτ : u ≤ c * Q ^ (-(680 * w)) / (Real.log Q + 2) ^ (14 : ℝ)) :
    2 * u * Y ^ w * (Real.log Q / c₀) ≤ 4 / c₀ * c ^ (1 - 14 * w) := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hL2 : (2 : ℝ) ≤ Real.log Q + 2 := by linarith
  have hLpos : (0 : ℝ) < Real.log Q + 2 := by linarith
  have hexp : (0 : ℝ) ≤ 1 - 14 * w := by nlinarith
  set τ : ℝ := c * Q ^ (-(680 * w)) / (Real.log Q + 2) ^ (14 : ℝ) with hτdef
  have hτpos : 0 < τ := by
    rw [hτdef]; positivity
  -- step 1 : Y^w ≤ 2^w · Q^{104w} · u^{−14w}
  have hYw : Y ^ w ≤ 2 ^ w * Q ^ (104 * w) * u ^ (-(14 * w)) := by
    have heq : (2 * Q ^ (104 : ℝ) * u ^ (-(14 : ℝ))) ^ w
        = 2 ^ w * Q ^ (104 * w) * u ^ (-(14 * w)) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hu0.le]
      rw [show (104 : ℝ) * w = 104 * w by ring, show -(14 : ℝ) * w = -(14 * w) by ring]
    rw [← heq]; exact Real.rpow_le_rpow hY0.le hYub hw0.le
  -- step 2 : u · u^{−14w} = u^{1−14w}, and u^{1−14w} ≤ τ^{1−14w}
  have huu : u * u ^ (-(14 * w)) = u ^ (1 - 14 * w) := by
    rw [show (1 : ℝ) - 14 * w = 1 + -(14 * w) by ring, Real.rpow_add hu0, Real.rpow_one]
  have huτpow : u ^ (1 - 14 * w) ≤ τ ^ (1 - 14 * w) :=
    Real.rpow_le_rpow hu0.le huτ hexp
  -- step 3 : τ^{1−14w} = c^{1−14w} · Q^{−680w(1−14w)} · (log Q+2)^{−14(1−14w)}
  have hτpow : τ ^ (1 - 14 * w)
      = c ^ (1 - 14 * w) * Q ^ (-(680 * w) * (1 - 14 * w))
        * (Real.log Q + 2) ^ (-(14 : ℝ) * (1 - 14 * w)) := by
    rw [hτdef, Real.div_rpow (by positivity) (Real.rpow_nonneg hLpos.le _),
      Real.mul_rpow hcc.le (Real.rpow_nonneg hQ0.le _),
      ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hLpos.le,
      div_eq_mul_inv, ← Real.rpow_neg hLpos.le,
      show -(680 * w) * (1 - 14 * w) = -(680 * w) * (1 - 14 * w) by ring,
      show -((14 : ℝ) * (1 - 14 * w)) = -(14 : ℝ) * (1 - 14 * w) by ring]
  -- step 4 : the Q-power and L₂-power are ≤ 1 on the window (b=680/k=14/σ₀=16/17 law)
  have hQpow : Q ^ (104 * w + -(680 * w) * (1 - 14 * w)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by nlinarith [sq_nonneg w])
  have hQprod : Q ^ (104 * w) * Q ^ (-(680 * w) * (1 - 14 * w)) ≤ 1 := by
    rw [← Real.rpow_add hQ0]; exact hQpow
  have hLpow : Real.log Q * (Real.log Q + 2) ^ (-(14 : ℝ) * (1 - 14 * w)) ≤ 1 := by
    calc Real.log Q * (Real.log Q + 2) ^ (-(14 : ℝ) * (1 - 14 * w))
        ≤ (Real.log Q + 2) * (Real.log Q + 2) ^ (-(14 : ℝ) * (1 - 14 * w)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_pos_of_pos hLpos _).le
      _ = (Real.log Q + 2) ^ (1 + -(14 : ℝ) * (1 - 14 * w)) := by
          rw [Real.rpow_add hLpos, Real.rpow_one]
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by nlinarith)
  -- step 5 : assemble
  have hLprodnn : 0 ≤ Real.log Q * (Real.log Q + 2) ^ (-(14 : ℝ) * (1 - 14 * w)) :=
    mul_nonneg hlogQ (Real.rpow_pos_of_pos hLpos _).le
  have hXnn : 0 ≤ 2 ^ (1 + w) * c ^ (1 - 14 * w) := by positivity
  have hmain : 2 * u * Y ^ w * Real.log Q ≤ 4 * c ^ (1 - 14 * w) := by
    have hb1 : 2 * u * Y ^ w * Real.log Q
        ≤ 2 * u * (2 ^ w * Q ^ (104 * w) * u ^ (-(14 * w))) * Real.log Q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hYw (by linarith [hu0])) hlogQ
    have hb2 : 2 * u * (2 ^ w * Q ^ (104 * w) * u ^ (-(14 * w))) * Real.log Q
        = 2 ^ (1 + w) * u ^ (1 - 14 * w) * (Q ^ (104 * w) * Real.log Q) := by
      rw [show (2 : ℝ) ^ (1 + w) = 2 * 2 ^ w by rw [Real.rpow_add (by norm_num), Real.rpow_one],
        ← huu]; ring
    have hb3 : 2 ^ (1 + w) * u ^ (1 - 14 * w) * (Q ^ (104 * w) * Real.log Q)
        ≤ 2 ^ (1 + w) * τ ^ (1 - 14 * w) * (Q ^ (104 * w) * Real.log Q) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left huτpow (by positivity))
        (mul_nonneg (Real.rpow_pos_of_pos hQ0 _).le hlogQ)
    have hPeq : 2 ^ (1 + w) * τ ^ (1 - 14 * w) * (Q ^ (104 * w) * Real.log Q)
        = 2 ^ (1 + w) * c ^ (1 - 14 * w) * (Q ^ (104 * w) * Q ^ (-(680 * w) * (1 - 14 * w)))
          * (Real.log Q * (Real.log Q + 2) ^ (-(14 : ℝ) * (1 - 14 * w))) := by
      rw [hτpow]; ring
    have hb4 : 2 ^ (1 + w) * c ^ (1 - 14 * w)
          * (Q ^ (104 * w) * Q ^ (-(680 * w) * (1 - 14 * w)))
          * (Real.log Q * (Real.log Q + 2) ^ (-(14 : ℝ) * (1 - 14 * w)))
        ≤ 2 ^ (1 + w) * c ^ (1 - 14 * w) := by
      calc 2 ^ (1 + w) * c ^ (1 - 14 * w)
              * (Q ^ (104 * w) * Q ^ (-(680 * w) * (1 - 14 * w)))
              * (Real.log Q * (Real.log Q + 2) ^ (-(14 : ℝ) * (1 - 14 * w)))
          ≤ 2 ^ (1 + w) * c ^ (1 - 14 * w) * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hQprod hXnn) hLpow hLprodnn
              (mul_nonneg hXnn (by norm_num))
        _ = 2 ^ (1 + w) * c ^ (1 - 14 * w) := by ring
    have hb5 : 2 ^ (1 + w) * c ^ (1 - 14 * w) ≤ 4 * c ^ (1 - 14 * w) := by
      have h24 : (2 : ℝ) ^ (1 + w) ≤ 4 := by
        calc (2 : ℝ) ^ (1 + w) ≤ (2 : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 4 := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      exact mul_le_mul_of_nonneg_right h24 (Real.rpow_pos_of_pos hcc _).le
    linarith [hb1, hb2 ▸ hb3, hPeq ▸ hb4, hb5]
  -- reduce the /c₀ goal to `hmain`
  rw [show 2 * u * Y ^ w * (Real.log Q / c₀) = (2 * u * Y ^ w * Real.log Q) * c₀⁻¹ by ring,
    show 4 / c₀ * c ^ (1 - 14 * w) = (4 * c ^ (1 - 14 * w)) * c₀⁻¹ by ring]
  exact mul_le_mul_of_nonneg_right hmain (inv_nonneg.mpr hc0.le)

/-- **The on-ray monomial engine.**  For a base pair `Q ≥ 1`, `L₂ ≥ 1`, on the ray
`u ≤ τ = c·Q^{−680w}/L₂^{14}` (`0 < c`, `0 < u`), any monomial `Q^α·u^γ·L₂^ε` with a *positive*
`u`-power `γ` and *nonpositive net* `Q`- and `L₂`-exponents (`α ≤ 680wγ`, `ε ≤ 14γ`) collapses to
`≤ c^γ`.  This is the exponent-balance skeleton of `rho_row_power_bound`, abstracted: `u^γ ≤ τ^γ`
substitutes the ray bound, and the window law makes the residual `Q`/`L₂` powers `≤ 1`. -/
lemma ray_pow_bound {Q L₂ c u w α γ ε : ℝ} (hQ1 : 1 ≤ Q) (hL2 : 1 ≤ L₂) (hcc : 0 < c)
    (hu0 : 0 < u) (hγ : 0 < γ)
    (huτ : u ≤ c * Q ^ (-(680 * w)) / L₂ ^ (14 : ℝ))
    (hα : α ≤ 680 * w * γ) (hε : ε ≤ 14 * γ) :
    Q ^ α * u ^ γ * L₂ ^ ε ≤ c ^ γ := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hL0 : (0 : ℝ) < L₂ := by linarith
  have hcγ : (0 : ℝ) < c ^ γ := Real.rpow_pos_of_pos hcc _
  set τ : ℝ := c * Q ^ (-(680 * w)) / L₂ ^ (14 : ℝ) with hτdef
  have h2 : τ ^ γ = c ^ γ * Q ^ (-(680 * w) * γ) * L₂ ^ (-(14 * γ)) := by
    rw [hτdef, Real.div_rpow (by positivity) (Real.rpow_nonneg hL0.le _),
      Real.mul_rpow hcc.le (Real.rpow_nonneg hQ0.le _),
      ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hL0.le, div_eq_mul_inv,
      ← Real.rpow_neg hL0.le]
  have huτpow : u ^ γ ≤ c ^ γ * Q ^ (-(680 * w) * γ) * L₂ ^ (-(14 * γ)) := by
    rw [← h2]; exact Real.rpow_le_rpow hu0.le huτ hγ.le
  have hQnn : (0 : ℝ) ≤ Q ^ α := (Real.rpow_pos_of_pos hQ0 _).le
  have hLnn : (0 : ℝ) ≤ L₂ ^ ε := (Real.rpow_pos_of_pos hL0 _).le
  have hQ1' : Q ^ (α + -(680 * w) * γ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by nlinarith)
  have hL1' : L₂ ^ (ε + -(14 * γ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL2 (by nlinarith)
  calc Q ^ α * u ^ γ * L₂ ^ ε
      ≤ Q ^ α * (c ^ γ * Q ^ (-(680 * w) * γ) * L₂ ^ (-(14 * γ))) * L₂ ^ ε :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huτpow hQnn) hLnn
    _ = c ^ γ * (Q ^ α * Q ^ (-(680 * w) * γ)) * (L₂ ^ ε * L₂ ^ (-(14 * γ))) := by ring
    _ = c ^ γ * Q ^ (α + -(680 * w) * γ) * L₂ ^ (ε + -(14 * γ)) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hL0]
    _ ≤ c ^ γ * 1 * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hQ1' hcγ.le) hL1'
          (Real.rpow_nonneg hL0.le _) (by positivity)
    _ = c ^ γ := by ring

/-! ## §5 — the on-ray row caps (each master row `≤ 1/8` on the ray `u < τ`) -/

/-- **The 1/x row cap.** `Y^{β₀−σ−1} ≤ 1/8` on the ray.  Net `u`-power `14(σ+u) ≥ 13 > 0`
(the exponent is `≤ 0`, so the lower bound `Y ≥ Q^{104}u^{−14}` upper-bounds `Y^{β₀−σ−1}`);
`ray_pow_bound` collapses it to `c^{14(σ+u)} ≤ c^{13} ≤ (1/2)^{13} ≤ 1/8`. -/
lemma row_1x_cap {Q L₂ c u w σ β₀ Y : ℝ}
    (hQ4 : 4 ≤ Q) (hL2 : 1 ≤ L₂) (hcc : 0 < c) (hchalf : c ≤ 1 / 2)
    (hu0 : 0 < u) (hwdef : w = 1 - σ) (hσlo : 16 / 17 ≤ σ) (hσ1 : σ < 1) (hσβ : σ ≤ β₀)
    (hβ1 : β₀ < 1)
    (hYlo : Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) ≤ Y)
    (huτ : u ≤ c * Q ^ (-(680 * w)) / L₂ ^ (14 : ℝ)) :
    Y ^ (β₀ - σ - 1) ≤ 1 / 8 := by
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hw0 : 0 < w := by rw [hwdef]; linarith
  set e : ℝ := β₀ - σ - 1 with he
  have hene : e < 0 := by rw [he]; linarith
  have hbaselo : (0 : ℝ) < Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by positivity
  have hstep1 : Y ^ e ≤ (Q ^ (104 : ℝ) * u ^ (-(14 : ℝ))) ^ e :=
    Real.rpow_le_rpow_of_nonpos hbaselo hYlo hene.le
  have hexp : (Q ^ (104 : ℝ) * u ^ (-(14 : ℝ))) ^ e = Q ^ (104 * e) * u ^ (-(14 * e)) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hu0.le _),
      ← Real.rpow_mul (by linarith), ← Real.rpow_mul hu0.le,
      show -(14 : ℝ) * e = -(14 * e) by ring]
  have hγpos : (0 : ℝ) < -(14 * e) := by nlinarith
  have hmono := ray_pow_bound (Q := Q) (L₂ := L₂) (c := c) (u := u) (w := w)
    (α := 104 * e) (γ := -(14 * e)) (ε := 0) hQ1 hL2 hcc hu0 hγpos huτ
    (by nlinarith [hw0, hγpos, hene]) (by nlinarith [hene])
  rw [Real.rpow_zero, mul_one] at hmono
  rw [hexp] at hstep1
  have hchain : Y ^ e ≤ c ^ (-(14 * e)) := le_trans hstep1 hmono
  have hge : c ^ (-(14 * e)) ≤ c ^ (13 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hcc (by linarith) (by nlinarith)
  have h12 : c ^ (13 : ℝ) ≤ (1 / 2 : ℝ) ^ (13 : ℝ) := Real.rpow_le_rpow hcc.le hchalf (by norm_num)
  have h13 : (1 / 2 : ℝ) ^ (13 : ℝ) ≤ 1 / 8 := by
    rw [show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  linarith [hchain, hge, h12, h13]

set_option maxHeartbeats 1600000 in
-- The log-crush chain (`log Y` bound → `rpow_sub_one_le` guard → the collected monomial through
-- `ray_pow_bound`) threads several nested `nlinarith`/`ring` normalizations over `rpow` atoms; the
-- rearrangement exceeds the default budget (as in `dh_master_ray`).
/-- **The A-row cap** (the `Y^u−1 ≈ u·ln Y` cancellation).  `Y^{β₀−σ}·(Y^{1−β₀}−1) ≤ 1/8` on the
ray.  `rpow_sub_one_le` turns `Y^u−1` into `e·u·ln Y`; `ln Y ≤ ln 2 + 104 log Q + 14·(−log u)` is
crushed by `neg_log_le_rpow` to a `u^{−δ}` power, then `ray_pow_bound` closes with net
`u`-power `1 − 14(w−u) − δ ≥ 3/17 − δ > 0`. -/
lemma row_A_cap {Q L₂ c u w σ β₀ Y : ℝ}
    (hQ4 : 4 ≤ Q) (hL2 : Real.log Q + 2 ≤ L₂) (hcc : 0 < c) (hc1 : c ≤ 1)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hwdef : w = 1 - σ) (hσlo : 16 / 17 ≤ σ) (hσ1 : σ < 1)
    (hσβ : σ ≤ β₀) (_hβ1 : β₀ < 1) (huβ : 1 - β₀ = u)
    (hYlo : Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) ≤ Y)
    (hYhi : Y ≤ 2 * Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)))
    (huτ : u ≤ c * Q ^ (-(680 * w)) / L₂ ^ (14 : ℝ))
    (hg1 : 805 * c ^ (49 / 50 : ℝ) ≤ 1)
    (hg2 : 1610 * Real.exp 1 * c ^ (133 / 850 : ℝ) ≤ 1 / 8) :
    Y ^ (β₀ - σ) * (Y ^ (1 - β₀) - 1) ≤ 1 / 8 := by
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hL2' : (1 : ℝ) ≤ L₂ := by linarith
  have hw0 : 0 < w := by rw [hwdef]; linarith
  have hbaselo : (0 : ℝ) < Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by positivity
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le hbaselo hYlo
  have hY1 : (1 : ℝ) ≤ Y := by
    refine le_trans ?_ hYlo
    have h1 : (1 : ℝ) ≤ Q ^ (104 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
    have h2 : (1 : ℝ) ≤ u ^ (-(14 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
    nlinarith [h1, h2]
  have hlogYnn : 0 ≤ Real.log Y := Real.log_nonneg hY1
  have hp : β₀ - σ = w - u := by rw [hwdef]; linarith
  have hpnn : 0 ≤ β₀ - σ := by linarith
  have hu50 : (1 : ℝ) ≤ u ^ (-(1 / 50 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
  -- Step 1 : `log Y ≤ 805·u^{−1/50}·L₂`
  have hlogY : Real.log Y ≤ 805 * u ^ (-(1 / 50 : ℝ)) * L₂ := by
    have hle : Real.log Y ≤ Real.log (2 * Q ^ (104 : ℝ) * u ^ (-(14 : ℝ))) :=
      Real.log_le_log hYpos hYhi
    have hexp : Real.log (2 * Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)))
        = Real.log 2 + 104 * Real.log Q + -14 * Real.log u := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_rpow hQ0, Real.log_rpow hu0]
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    have hnlogu : -Real.log u ≤ u ^ (-(1 / 50 : ℝ)) / (1 / 50) := neg_log_le_rpow hu0 (by norm_num)
    have hstep : Real.log 2 + 104 * Real.log Q + -14 * Real.log u
        ≤ 805 * u ^ (-(1 / 50 : ℝ)) * L₂ := by
      have e1 : (1 : ℝ) ≤ u ^ (-(1 / 50 : ℝ)) * L₂ := by nlinarith [hu50, hL2']
      have e2 : 104 * Real.log Q ≤ 104 * (u ^ (-(1 / 50 : ℝ)) * L₂) := by
        have : Real.log Q ≤ L₂ := by linarith
        nlinarith [hu50, this, Real.log_nonneg hQ1]
      have e3 : -14 * Real.log u ≤ 700 * u ^ (-(1 / 50 : ℝ)) := by
        have : -14 * Real.log u = 14 * (-Real.log u) := by ring
        rw [this]; nlinarith [hnlogu]
      have e4 : 700 * u ^ (-(1 / 50 : ℝ)) ≤ 700 * (u ^ (-(1 / 50 : ℝ)) * L₂) := by
        nlinarith [hL2', Real.rpow_nonneg hu0.le (-(1 / 50 : ℝ))]
      nlinarith [hlog2, e1, e2, e3, e4]
    linarith [hle, hexp ▸ hstep]
  -- Step 2 : `u·log Y ≤ 1` (the `rpow_sub_one_le` guard)
  have hulogY : u * Real.log Y ≤ 1 := by
    have hb := ray_pow_bound (Q := Q) (L₂ := L₂) (c := c) (u := u) (w := w)
      (α := 0) (γ := 49 / 50) (ε := 1) hQ1 hL2' hcc hu0 (by norm_num) huτ
      (by positivity) (by norm_num)
    rw [Real.rpow_zero, one_mul, Real.rpow_one] at hb
    have hmul : u * Real.log Y ≤ u * (805 * u ^ (-(1 / 50 : ℝ)) * L₂) :=
      mul_le_mul_of_nonneg_left hlogY hu0.le
    have heq : u * (805 * u ^ (-(1 / 50 : ℝ)) * L₂) = 805 * (u ^ (49 / 50 : ℝ) * L₂) := by
      rw [show (49 / 50 : ℝ) = 1 + -(1 / 50 : ℝ) by norm_num, Real.rpow_add hu0, Real.rpow_one]
      ring
    rw [heq] at hmul
    nlinarith [hmul, hb, hg1]
  -- Step 3 : the cancellation and the final monomial bound
  have hYu : Y ^ u - 1 ≤ Real.exp 1 * (u * Real.log Y) := rpow_sub_one_le hY1 hu0.le hulogY
  rw [huβ]
  have hYpnn : (0 : ℝ) ≤ Y ^ (β₀ - σ) := Real.rpow_nonneg hYpos.le _
  have hfin : Y ^ (β₀ - σ) * (Real.exp 1 * (u * Real.log Y)) ≤ 1 / 8 := by
    -- bound `u·log Y ≤ 805·u^{49/50}·L₂` and `Y^{β₀−σ} ≤ 2^p Q^{104p} u^{−14p}`
    have hulY : u * Real.log Y ≤ 805 * (u ^ (49 / 50 : ℝ) * L₂) := by
      have hmul : u * Real.log Y ≤ u * (805 * u ^ (-(1 / 50 : ℝ)) * L₂) :=
        mul_le_mul_of_nonneg_left hlogY hu0.le
      have heq : u * (805 * u ^ (-(1 / 50 : ℝ)) * L₂) = 805 * (u ^ (49 / 50 : ℝ) * L₂) := by
        rw [show (49 / 50 : ℝ) = 1 + -(1 / 50 : ℝ) by norm_num, Real.rpow_add hu0, Real.rpow_one]
        ring
      rwa [heq] at hmul
    have hYp : Y ^ (β₀ - σ)
        ≤ 2 ^ (β₀ - σ) * Q ^ (104 * (β₀ - σ)) * u ^ (-(14 * (β₀ - σ))) := by
      have h1 : Y ^ (β₀ - σ) ≤ (2 * Q ^ (104 : ℝ) * u ^ (-(14 : ℝ))) ^ (β₀ - σ) :=
        Real.rpow_le_rpow hYpos.le hYhi hpnn
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hu0.le _),
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg hQ0.le _),
        ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hu0.le,
        show -(14 : ℝ) * (β₀ - σ) = -(14 * (β₀ - σ)) by ring] at h1
      exact h1
    -- the monomial `Q^{104p}·u^{49/50−14p}·L₂ ≤ c^{49/50−14p}`
    have hmono := ray_pow_bound (Q := Q) (L₂ := L₂) (c := c) (u := u) (w := w)
      (α := 104 * (β₀ - σ)) (γ := 49 / 50 - 14 * (β₀ - σ)) (ε := 1) hQ1 hL2' hcc hu0
      (by rw [hp]; nlinarith [hw0, hu0, mul_nonneg hw0.le hw0.le])
      huτ
      (by rw [hp]; nlinarith [hw0, hu0, mul_nonneg hw0.le hw0.le,
        mul_nonneg hw0.le hu0.le])
      (by rw [hp]; nlinarith [hw0, hu0])
    rw [Real.rpow_one] at hmono
    -- TAU-SHARP S2: the A row's **own** γ-floor, not the uniform `1/8`.  `γ_A(σ,β₀) =
    -- 49/50 − 14(β₀−σ)` is decreasing in `β₀−σ`, and `β₀ − σ = w − u < w ≤ 1/17` on the window
    -- (`hσlo : 16/17 ≤ σ`, `hu0 : 0 < u`), so `γ_A > 49/50 − 14/17 = 133/850` — the closed-endpoint
    -- infimum, exact as a rational.  `linarith` (not `nlinarith`): the goal is linear in `σ`, `u`.
    have hγ8 : c ^ (49 / 50 - 14 * (β₀ - σ)) ≤ c ^ (133 / 850 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hcc hc1 (by rw [hp]; linarith [hσlo, hw0, hu0])
    have h2p : (2 : ℝ) ^ (β₀ - σ) ≤ 2 := by
      calc (2 : ℝ) ^ (β₀ - σ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hp]; linarith)
        _ = 2 := Real.rpow_one 2
    -- assemble
    have hEnn : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    have hchain : Y ^ (β₀ - σ) * (Real.exp 1 * (u * Real.log Y))
        ≤ 1610 * Real.exp 1 * c ^ (133 / 850 : ℝ) := by
      have hstep1 : Y ^ (β₀ - σ) * (Real.exp 1 * (u * Real.log Y))
          ≤ (2 ^ (β₀ - σ) * Q ^ (104 * (β₀ - σ)) * u ^ (-(14 * (β₀ - σ))))
            * (Real.exp 1 * (805 * (u ^ (49 / 50 : ℝ) * L₂))) := by
        apply mul_le_mul hYp _ (mul_nonneg hEnn (mul_nonneg hu0.le hlogYnn)) (by positivity)
        exact mul_le_mul_of_nonneg_left hulY hEnn
      refine le_trans hstep1 ?_
      have hcollect : (2 ^ (β₀ - σ) * Q ^ (104 * (β₀ - σ)) * u ^ (-(14 * (β₀ - σ))))
            * (Real.exp 1 * (805 * (u ^ (49 / 50 : ℝ) * L₂)))
          = 805 * Real.exp 1 * 2 ^ (β₀ - σ)
            * (Q ^ (104 * (β₀ - σ)) * (u ^ (-(14 * (β₀ - σ))) * u ^ (49 / 50 : ℝ)) * L₂) := by
        ring
      rw [hcollect]
      have hupow : u ^ (-(14 * (β₀ - σ))) * u ^ (49 / 50 : ℝ)
          = u ^ (49 / 50 - 14 * (β₀ - σ)) := by
        rw [← Real.rpow_add hu0]; ring_nf
      rw [hupow]
      have hmono' : Q ^ (104 * (β₀ - σ)) * u ^ (49 / 50 - 14 * (β₀ - σ)) * L₂
          ≤ c ^ (49 / 50 - 14 * (β₀ - σ)) := hmono
      have hA : (0 : ℝ) ≤ 805 * Real.exp 1 := by positivity
      have hBnn : (0 : ℝ) ≤ Q ^ (104 * (β₀ - σ)) * u ^ (49 / 50 - 14 * (β₀ - σ)) * L₂ := by
        positivity
      have hB : Q ^ (104 * (β₀ - σ)) * u ^ (49 / 50 - 14 * (β₀ - σ)) * L₂
          ≤ c ^ (133 / 850 : ℝ) := le_trans hmono' hγ8
      have hinner : 2 ^ (β₀ - σ)
            * (Q ^ (104 * (β₀ - σ)) * u ^ (49 / 50 - 14 * (β₀ - σ)) * L₂)
          ≤ 2 * c ^ (133 / 850 : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_right h2p hBnn) (mul_le_mul_of_nonneg_left hB (by norm_num))
      calc 805 * Real.exp 1 * 2 ^ (β₀ - σ)
            * (Q ^ (104 * (β₀ - σ)) * u ^ (49 / 50 - 14 * (β₀ - σ)) * L₂)
          = (805 * Real.exp 1) * (2 ^ (β₀ - σ)
              * (Q ^ (104 * (β₀ - σ)) * u ^ (49 / 50 - 14 * (β₀ - σ)) * L₂)) := by ring
        _ ≤ (805 * Real.exp 1) * (2 * c ^ (133 / 850 : ℝ)) := mul_le_mul_of_nonneg_left hinner hA
        _ = 1610 * Real.exp 1 * c ^ (133 / 850 : ℝ) := by ring
    linarith [hchain, hg2]
  calc Y ^ (β₀ - σ) * (Y ^ u - 1)
      ≤ Y ^ (β₀ - σ) * (Real.exp 1 * (u * Real.log Y)) :=
        mul_le_mul_of_nonneg_left hYu hYpnn
    _ ≤ 1 / 8 := hfin

set_option maxHeartbeats 800000 in
-- The residue-row reduction threads the pole-distance ZFR bound through the `ray_pow_bound`
-- monomial and several `rpow`-atom `ring`/`nlinarith` normalizations, exceeding the default budget.
/-- **The ρ-main row cap** (the residue row — where the zero-free region enters).  The master's
leading row `(1−β₀)(2−β₀)·Y^{1−σ}/(‖1−ρ‖‖2−ρ‖) ≤ 1/8` on the ray.  The pole-distance
`1/‖1−ρ‖ ≤ L₂/c₀` (ZFR floor) and `‖2−ρ‖ ≥ 1` reduce it to `(2/c₀)·u·Y^{w}·L₂`, which
`ray_pow_bound` (α=104w, γ=1−14w, ε=1) collapses to `(4/c₀)·c^{1−14w} ≤ (4/c₀)·c^{3/17}`. -/
lemma row_rho_main_cap {Q L₂ c c₀ u w σ β₀ Y n1 n2 : ℝ}
    (hQ4 : 4 ≤ Q) (hL2 : 1 ≤ L₂) (hcc : 0 < c) (hc1 : c ≤ 1) (hc0 : 0 < c₀)
    (hu0 : 0 < u) (hwdef : w = 1 - σ) (hσlo : 16 / 17 ≤ σ) (hσ1 : σ < 1)
    (hβ0 : 0 ≤ β₀) (hβ1 : β₀ < 1)
    (hn2 : 1 ≤ n2) (hn1inv : 1 / n1 ≤ L₂ / c₀)
    (hYlo : Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) ≤ Y) (hYhi : Y ≤ 2 * Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)))
    (huτ : u ≤ c * Q ^ (-(680 * w)) / L₂ ^ (14 : ℝ))
    (hg : 4 / c₀ * c ^ (3 / 17 : ℝ) ≤ 1 / 8) :
    u * (2 - β₀) * Y ^ w / (n1 * n2) ≤ 1 / 8 := by
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hw0 : 0 < w := by rw [hwdef]; linarith
  have hn2pos : (0 : ℝ) < n2 := by linarith
  have hbaselo : (0 : ℝ) < Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by positivity
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le hbaselo hYlo
  have hYwnn : (0 : ℝ) ≤ Y ^ w := (Real.rpow_pos_of_pos hYpos _).le
  -- `Y^w ≤ 2^w Q^{104w} u^{−14w}`
  have hYw : Y ^ w ≤ 2 ^ w * Q ^ (104 * w) * u ^ (-(14 * w)) := by
    have h1 : Y ^ w ≤ (2 * Q ^ (104 : ℝ) * u ^ (-(14 : ℝ))) ^ w :=
      Real.rpow_le_rpow hYpos.le hYhi hw0.le
    rwa [Real.mul_rpow (by positivity) (Real.rpow_nonneg hu0.le _),
      Real.mul_rpow (by norm_num) (Real.rpow_nonneg hQ0.le _),
      ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hu0.le,
      show -(14 : ℝ) * w = -(14 * w) by ring] at h1
  -- the monomial collapse
  have hmono := ray_pow_bound (Q := Q) (L₂ := L₂) (c := c) (u := u) (w := w)
    (α := 104 * w) (γ := 1 - 14 * w) (ε := 1) hQ1 hL2 hcc hu0
    (by rw [hwdef] at *; nlinarith [hw0]) huτ (by nlinarith [hw0]) (by nlinarith [hw0])
  rw [Real.rpow_one] at hmono
  -- `1/(n1 n2) ≤ L₂/c₀`
  have hfrac : 1 / (n1 * n2) ≤ L₂ / c₀ := by
    have hsplit : 1 / (n1 * n2) = 1 / n1 * (1 / n2) := by rw [one_div, one_div, one_div, mul_inv]
    rw [hsplit]
    have h2le : 1 / n2 ≤ 1 := (div_le_one hn2pos).mpr hn2
    calc 1 / n1 * (1 / n2) ≤ L₂ / c₀ * 1 :=
          mul_le_mul hn1inv h2le (by positivity) (by positivity)
      _ = L₂ / c₀ := by ring
  -- assemble
  have hnum_nn : (0 : ℝ) ≤ u * (2 - β₀) * Y ^ w := by
    apply mul_nonneg (mul_nonneg hu0.le (by linarith)) hYwnn
  have hstep1 : u * (2 - β₀) * Y ^ w / (n1 * n2)
      ≤ u * (2 - β₀) * Y ^ w * (L₂ / c₀) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hfrac hnum_nn
  have hstep2 : u * (2 - β₀) * Y ^ w * (L₂ / c₀) ≤ 2 / c₀ * (u * Y ^ w * L₂) := by
    have hTnn : (0 : ℝ) ≤ u * Y ^ w * (L₂ / c₀) :=
      mul_nonneg (mul_nonneg hu0.le hYwnn) (div_nonneg (by linarith) hc0.le)
    have hb2 : 2 - β₀ ≤ 2 := by linarith
    calc u * (2 - β₀) * Y ^ w * (L₂ / c₀) = (2 - β₀) * (u * Y ^ w * (L₂ / c₀)) := by ring
      _ ≤ 2 * (u * Y ^ w * (L₂ / c₀)) := mul_le_mul_of_nonneg_right hb2 hTnn
      _ = 2 / c₀ * (u * Y ^ w * L₂) := by ring
  -- `u·Y^w·L₂ ≤ 2^w c^{1−14w}`, and `2^w ≤ 2`, `c^{1−14w} ≤ c^{3/17}`
  have huYL : u * Y ^ w * L₂ ≤ 2 ^ w * c ^ (1 - 14 * w) := by
    have hbnd : u * Y ^ w * L₂ ≤ u * (2 ^ w * Q ^ (104 * w) * u ^ (-(14 * w))) * L₂ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYw hu0.le) (by linarith)
    have heq : u * (2 ^ w * Q ^ (104 * w) * u ^ (-(14 * w))) * L₂
        = 2 ^ w * (Q ^ (104 * w) * u ^ (1 - 14 * w) * L₂) := by
      rw [show (1 : ℝ) - 14 * w = 1 + -(14 * w) by ring, Real.rpow_add hu0, Real.rpow_one]; ring
    rw [heq] at hbnd
    have : 2 ^ w * (Q ^ (104 * w) * u ^ (1 - 14 * w) * L₂) ≤ 2 ^ w * c ^ (1 - 14 * w) :=
      mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg (by norm_num) _)
    linarith [hbnd, this]
  have h2w : (2 : ℝ) ^ w ≤ 2 := by
    calc (2 : ℝ) ^ w ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hwdef]; linarith)
      _ = 2 := Real.rpow_one 2
  have hcw : c ^ (1 - 14 * w) ≤ c ^ (3 / 17 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hcc hc1 (by rw [hwdef] at *; nlinarith [hw0])
  -- final chain
  have hfin : 2 / c₀ * (u * Y ^ w * L₂) ≤ 4 / c₀ * c ^ (3 / 17 : ℝ) := by
    have h2c0 : (0 : ℝ) ≤ 2 / c₀ := by positivity
    calc 2 / c₀ * (u * Y ^ w * L₂) ≤ 2 / c₀ * (2 ^ w * c ^ (1 - 14 * w)) :=
          mul_le_mul_of_nonneg_left huYL h2c0
      _ ≤ 2 / c₀ * (2 * c ^ (3 / 17 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ h2c0
          exact le_trans (mul_le_mul_of_nonneg_right h2w (Real.rpow_nonneg hcc.le _))
            (mul_le_mul_of_nonneg_left hcw (by norm_num))
      _ = 4 / c₀ * c ^ (3 / 17 : ℝ) := by ring
  linarith [hstep1, hstep2, hfin, hg]

/-- **The polylog factor bound.**  `1 + log(z²) ≤ 248·u^{−1/100}·L₂` at the crush scale
`z ≤ 2Q^{12}u^{−3}`.  `log z ≤ log 2 + 12 log Q − 3 log u`, then `−log u ≤ (100/e)·u^{−1/100}`
(`neg_log_le_rpow'`) and `log Q ≤ L₂` fold every term into the single `u^{−1/100}·L₂` shape.
The constant is `3 + 2g + 2n/(eδ) = 3 + 24 + 600/e ≤ 248` at `(g, n, δ) = (12, 3, 1/100)`.

**TAU-SHARP S5(a).**  Was `627`, from the crude `neg_log_le_rpow` (`600` in place of `600/e`).
The gain propagates through `logz_factor_pow9_le` as `248^9` in `KEβ`/`KEρ`, i.e. `−66.78` on
`log(1/c)` in BOTH `c`-min towers. -/
lemma logz_factor_le {Q L₂ z u : ℝ} (hQ4 : 4 ≤ Q) (hL2 : Real.log Q + 2 ≤ L₂)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hzpos : 0 < z)
    (hzhi : z ≤ 2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) :
    1 + Real.log (z ^ 2) ≤ 248 * u ^ (-(1 / 100 : ℝ)) * L₂ := by
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hL2' : (1 : ℝ) ≤ L₂ := by linarith
  have hu100 : (1 : ℝ) ≤ u ^ (-(1 / 100 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
  have hlogz2 : Real.log (z ^ 2) = 2 * Real.log z := by
    rw [Real.log_pow]; push_cast; ring
  have hlogz : Real.log z ≤ Real.log 2 + 12 * Real.log Q + -3 * Real.log u := by
    have hle : Real.log z ≤ Real.log (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) :=
      Real.log_le_log hzpos hzhi
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow hQ0, Real.log_rpow hu0] at hle
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hnlognn : 0 ≤ -Real.log u := by
    have := Real.log_nonpos hu0.le hu1; linarith
  have hnlogu : -Real.log u * (Real.exp 1 / 100) ≤ u ^ (-(1 / 100 : ℝ)) := by
    have h := neg_log_le_rpow' (u := u) (δ := 1 / 100) hu0 (by norm_num)
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.exp 1 * (1 / 100))] at h
    calc -Real.log u * (Real.exp 1 / 100)
        = -Real.log u * (Real.exp 1 * (1 / 100)) := by ring
      _ ≤ _ := h
  have he9 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  rw [hlogz2]
  have e1 : (1 : ℝ) ≤ u ^ (-(1 / 100 : ℝ)) * L₂ := by nlinarith [hu100, hL2']
  have e2 : 24 * Real.log Q ≤ 24 * (u ^ (-(1 / 100 : ℝ)) * L₂) := by
    have hlogQL : Real.log Q ≤ L₂ := by linarith
    nlinarith [hu100, hlogQL, hlogQ0]
  -- `−6·log u ≤ (600/e)·u^{−1/100} ≤ 221·u^{−1/100}` (S5(a); was `600` with the crude bound)
  have e3 : -6 * Real.log u ≤ 221 * u ^ (-(1 / 100 : ℝ)) := by
    nlinarith [hnlogu, mul_nonneg hnlognn
      (by linarith [he9] : (0 : ℝ) ≤ Real.exp 1 - 2.7182818283)]
  have e4 : 221 * u ^ (-(1 / 100 : ℝ)) ≤ 221 * (u ^ (-(1 / 100 : ℝ)) * L₂) := by
    nlinarith [hL2', Real.rpow_nonneg hu0.le (-(1 / 100 : ℝ))]
  nlinarith [hlogz, hlog2, e1, e2, e3, e4]

/-- **The polylog^9 factor bound (pure rpow).** `(1 + log(z²))^9 ≤ 248^9·u^{−9/100}·L₂^9`. -/
lemma logz_factor_pow9_le {Q L₂ z u : ℝ} (hQ4 : 4 ≤ Q) (hL2 : Real.log Q + 2 ≤ L₂)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hz1 : 1 ≤ z)
    (hzhi : z ≤ 2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) :
    (1 + Real.log (z ^ 2)) ^ 9 ≤ 248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ) := by
  have hzpos : 0 < z := by linarith
  have hbase := logz_factor_le hQ4 hL2 hu0 hu1 hzpos hzhi
  have hlz2 : 0 ≤ Real.log (z ^ 2) := by
    apply Real.log_nonneg; nlinarith [hz1]
  have hbnn : 0 ≤ 1 + Real.log (z ^ 2) := by linarith
  have hstep : (1 + Real.log (z ^ 2)) ^ 9
      ≤ (248 * u ^ (-(1 / 100 : ℝ)) * L₂) ^ 9 := by
    apply pow_le_pow_left₀ hbnn hbase
  refine le_trans hstep ?_
  rw [mul_pow, mul_pow]
  have hupow : (u ^ (-(1 / 100 : ℝ))) ^ 9 = u ^ (-(9 / 100 : ℝ)) := by
    rw [← Real.rpow_natCast (u ^ (-(1 / 100 : ℝ))) 9, ← Real.rpow_mul hu0.le]
    norm_num
  have hL2pow : L₂ ^ 9 = L₂ ^ (9 : ℝ) := by
    rw [← Real.rpow_natCast L₂ 9]; norm_num
  rw [hupow, hL2pow]

set_option maxHeartbeats 1600000 in
-- The four-factor monomial collection (`← Real.rpow_add` groups + `ring`) plus the nested
-- `nlinarith` window checks exceed the default budget (as in `dh_master_ray`).
/-- **The Eβ-row cap.** `Y^{β₀−σ}·Eβ ≤ 1/8` on the ray. -/
lemma row_Eβ_cap {Q L₂ c u w σ β₀ Y z M Z₀ : ℝ}
    (hQ4 : 4 ≤ Q) (hL2 : Real.log Q + 2 ≤ L₂) (hcc : 0 < c) (hc1 : c ≤ 1)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hwdef : w = 1 - σ) (hσlo : 16 / 17 ≤ σ) (hσ1 : σ < 1)
    (hσβ : σ ≤ β₀) (_hβ1 : β₀ < 1) (huβ : 1 - β₀ = u)
    (hMnn : 0 ≤ M) (hM : M ≤ Real.sqrt Q * L₂) (hZ0 : 0 ≤ Z₀)
    (hz1 : 1 ≤ z) (hzhi : z ≤ 2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
    (hYlo : Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) ≤ Y)
    (_hYhi : Y ≤ 2 * Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)))
    (huτ : u ≤ c * Q ^ (-(680 * w)) / L₂ ^ (14 : ℝ))
    (hg : 2 * (328 + 48 * Z₀) * 248 ^ 9 * c ^ (3547 / 1700 : ℝ) ≤ 1 / 8) :
    Y ^ (β₀ - σ) * ((136 + 48 * M + 48 * M * Z₀ + 144 * M / (1 - β₀))
        * z * (1 + Real.log (z ^ 2)) ^ 9 * Y ^ (1 / 2 - β₀)) ≤ 1 / 8 := by
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hL2' : (1 : ℝ) ≤ L₂ := by linarith
  have hL0 : (0 : ℝ) < L₂ := by linarith
  have hw0 : 0 < w := by rw [hwdef]; linarith
  have hbaselo : (0 : ℝ) < Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by positivity
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le hbaselo hYlo
  have hzpos : (0 : ℝ) < z := by linarith
  have hsqQ : Real.sqrt Q = Q ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow Q
  have hpoly := logz_factor_pow9_le hQ4 hL2 hu0 hu1 hz1 hzhi
  have hMB : M ≤ Q ^ (1 / 2 : ℝ) * L₂ := by rw [← hsqQ]; exact hM
  have hui : u ^ (-(1 : ℝ)) = 1 / u := by rw [Real.rpow_neg hu0.le, Real.rpow_one, one_div]
  have hB1 : (1 : ℝ) ≤ Q ^ (1 / 2 : ℝ) * L₂ := by
    have h1 : (1 : ℝ) ≤ Q ^ (1 / 2 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
    nlinarith [h1, hL2']
  -- K bound : K ≤ (328+48Z₀)·(Q^{1/2}·L₂)·u^{−1}
  set K : ℝ := 136 + 48 * M + 48 * M * Z₀ + 144 * M / (1 - β₀) with hKdef
  have hKu : K * u ≤ (328 + 48 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂) := by
    rw [hKdef, huβ]
    have h144 : 144 * M / u * u = 144 * M := by
      rw [div_mul_eq_mul_div, mul_div_assoc, div_self hu0.ne', mul_one]
    nlinarith [hMB, hB1, hu0, hu1, hZ0, hMnn, h144,
      mul_nonneg hMnn (by linarith : (0 : ℝ) ≤ 1 - u),
      mul_nonneg (mul_nonneg hMnn hZ0) (by linarith : (0 : ℝ) ≤ 1 - u),
      mul_nonneg hZ0 (by linarith : (0 : ℝ) ≤ Q ^ (1 / 2 : ℝ) * L₂ - M)]
  have hKle : K ≤ (328 + 48 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂) * u ^ (-(1 : ℝ)) := by
    rw [hui, mul_one_div, le_div_iff₀ hu0]; exact hKu
  -- combine Y powers, then bound Y^{1/2−σ}
  rw [show Y ^ (β₀ - σ) * (K * z * (1 + Real.log (z ^ 2)) ^ 9 * Y ^ (1 / 2 - β₀))
      = K * z * (1 + Real.log (z ^ 2)) ^ 9 * (Y ^ (β₀ - σ) * Y ^ (1 / 2 - β₀)) by ring,
    ← Real.rpow_add hYpos, show (β₀ - σ) + (1 / 2 - β₀) = 1 / 2 - σ by ring]
  have hYexp : (1 : ℝ) / 2 - σ < 0 := by linarith
  have hYb : Y ^ (1 / 2 - σ) ≤ Q ^ (104 * (1 / 2 - σ)) * u ^ (-(14 * (1 / 2 - σ))) := by
    have h1 : Y ^ (1 / 2 - σ) ≤ (Q ^ (104 : ℝ) * u ^ (-(14 : ℝ))) ^ (1 / 2 - σ) :=
      Real.rpow_le_rpow_of_nonpos hbaselo hYlo hYexp.le
    rwa [Real.mul_rpow (Real.rpow_nonneg hQ0.le _) (Real.rpow_nonneg hu0.le _),
      ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hu0.le,
      show -(14 : ℝ) * (1 / 2 - σ) = -(14 * (1 / 2 - σ)) by ring] at h1
  -- monomial collapse via ray_pow_bound
  have hγpos : (0 : ℝ) < -(1 : ℝ) + -(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ)) := by
    nlinarith [hσlo]
  have hmono := ray_pow_bound (Q := Q) (L₂ := L₂) (c := c) (u := u) (w := w)
    (α := 1 / 2 + 12 + 104 * (1 / 2 - σ))
    (γ := -(1 : ℝ) + -(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ)))
    (ε := 1 + 9) hQ1 hL2' hcc hu0 hγpos huτ
    (by rw [hwdef] at *; nlinarith [hw0, hσlo]) (by nlinarith [hσlo])
  -- collect the product into the monomial
  have hQg : Q ^ (1 / 2 : ℝ) * Q ^ (12 : ℝ) * Q ^ (104 * (1 / 2 - σ))
      = Q ^ (1 / 2 + 12 + 104 * (1 / 2 - σ)) := by
    rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
  have hug : u ^ (-(1 : ℝ)) * u ^ (-(3 : ℝ)) * u ^ (-(9 / 100 : ℝ)) * u ^ (-(14 * (1 / 2 - σ)))
      = u ^ (-(1 : ℝ) + -(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ))) := by
    rw [← Real.rpow_add hu0, ← Real.rpow_add hu0, ← Real.rpow_add hu0]
  have hLg : L₂ * L₂ ^ (9 : ℝ) = L₂ ^ (1 + 9 : ℝ) := by
    rw [Real.rpow_add hL0, Real.rpow_one]
  have hcollect : ((328 + 48 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂) * u ^ (-(1 : ℝ)))
        * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
        * (248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ))
        * (Q ^ (104 * (1 / 2 - σ)) * u ^ (-(14 * (1 / 2 - σ))))
      = 2 * (328 + 48 * Z₀) * 248 ^ 9
        * (Q ^ (1 / 2 + 12 + 104 * (1 / 2 - σ))
          * u ^ (-(1 : ℝ) + -(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ)))
          * L₂ ^ (1 + 9 : ℝ)) := by
    rw [← hQg, ← hug, ← hLg]; ring
  -- final chain
  have hCnn : (0 : ℝ) ≤ 2 * (328 + 48 * Z₀) * 248 ^ 9 := by positivity
  -- TAU-SHARP S2: the Eβ row's **own** γ-floor.  `γ_Eβ(σ) = 14σ − 1109/100` is strictly increasing
  -- in `σ`, so its infimum over the window sits at the CLOSED endpoint `hσlo : 16/17 ≤ σ`, where it
  -- equals `3547/1700` EXACTLY (`14·16/17 − 1109/100 = 22400/1700 − 18853/1700`).  The freeze's
  -- decimal `2.0865` exceeds this by `2.941e−5` and is FALSE at the endpoint — the rational is the
  -- only admissible numeral.  `linarith` (not `nlinarith`): linear in `σ`, tight at equality.
  have hcγ : c ^ (-(1 : ℝ) + -(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ)))
      ≤ c ^ (3547 / 1700 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hcc hc1 (by linarith [hσlo])
  have hbnn : (0 : ℝ) ≤ 1 + Real.log (z ^ 2) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ z ^ 2 by nlinarith [hz1]); linarith
  have hpolynn : (0 : ℝ) ≤ (1 + Real.log (z ^ 2)) ^ 9 := pow_nonneg hbnn 9
  have hYsnn : (0 : ℝ) ≤ Y ^ (1 / 2 - σ) := Real.rpow_nonneg hYpos.le _
  have hKbarnn : (0 : ℝ) ≤ (328 + 48 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂) * u ^ (-(1 : ℝ)) := by
    positivity
  have hzbarnn : (0 : ℝ) ≤ 2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) := by positivity
  have hPbarnn : (0 : ℝ) ≤ 248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ) := by positivity
  have hprod : K * z * (1 + Real.log (z ^ 2)) ^ 9 * Y ^ (1 / 2 - σ)
      ≤ ((328 + 48 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂) * u ^ (-(1 : ℝ)))
          * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
          * (248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ))
          * (Q ^ (104 * (1 / 2 - σ)) * u ^ (-(14 * (1 / 2 - σ)))) := by
    have h1 : K * z
        ≤ (328 + 48 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂) * u ^ (-(1 : ℝ))
          * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) :=
      mul_le_mul hKle hzhi hzpos.le hKbarnn
    have h2 : K * z * (1 + Real.log (z ^ 2)) ^ 9
        ≤ (328 + 48 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂) * u ^ (-(1 : ℝ))
          * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
          * (248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ)) :=
      mul_le_mul h1 hpoly hpolynn (mul_nonneg hKbarnn hzbarnn)
    exact mul_le_mul h2 hYb hYsnn (mul_nonneg (mul_nonneg hKbarnn hzbarnn) hPbarnn)
  calc K * z * (1 + Real.log (z ^ 2)) ^ 9 * Y ^ (1 / 2 - σ)
      ≤ ((328 + 48 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂) * u ^ (-(1 : ℝ)))
          * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
          * (248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ))
          * (Q ^ (104 * (1 / 2 - σ)) * u ^ (-(14 * (1 / 2 - σ)))) := hprod
    _ = 2 * (328 + 48 * Z₀) * 248 ^ 9
        * (Q ^ (1 / 2 + 12 + 104 * (1 / 2 - σ))
          * u ^ (-(1 : ℝ) + -(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ)))
          * L₂ ^ (1 + 9 : ℝ)) := hcollect
    _ ≤ 2 * (328 + 48 * Z₀) * 248 ^ 9
        * c ^ (-(1 : ℝ) + -(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ))) :=
        mul_le_mul_of_nonneg_left hmono hCnn
    _ ≤ 2 * (328 + 48 * Z₀) * 248 ^ 9 * c ^ (3547 / 1700 : ℝ) :=
        mul_le_mul_of_nonneg_left hcγ hCnn
    _ ≤ 1 / 8 := hg

set_option maxHeartbeats 1600000 in
-- The four-factor monomial collection (`← Real.rpow_add` groups + `ring`) plus the nested
-- `nlinarith` window checks exceed the default budget (as in `dh_master_ray`).
/-- **The Eρ-row cap.** `Eρ = Cρ·z·(1+log z²)^9·Y^{1/2−σ} ≤ 1/8` on the ray, where the
extraction constant `Cρ` (`= C2Rho q Z₀ ρ`) obeys the ZFR-folded bound `Cρ ≤ (564+72Z₀)√Q·L₂²/c₀`
(proven in the assembly by unpacking `C2Rho`/`CwRho` against the pole floors). -/
lemma row_Eρ_cap {Q L₂ c c₀ u w σ Y z Cρ Z₀ : ℝ}
    (hQ4 : 4 ≤ Q) (hL2 : Real.log Q + 2 ≤ L₂) (hcc : 0 < c) (hc1 : c ≤ 1) (hc0 : 0 < c₀)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hwdef : w = 1 - σ) (hσlo : 16 / 17 ≤ σ) (hσ1 : σ < 1)
    (_hCρnn : 0 ≤ Cρ)
    (hCρ : Cρ ≤ (564 + 72 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀))
    (hZ0 : 0 ≤ Z₀)
    (hz1 : 1 ≤ z) (hzhi : z ≤ 2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
    (hYlo : Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) ≤ Y)
    (huτ : u ≤ c * Q ^ (-(680 * w)) / L₂ ^ (14 : ℝ))
    (hg : 2 * (564 + 72 * Z₀) * 248 ^ 9 / c₀ * c ^ (5247 / 1700 : ℝ) ≤ 1 / 8) :
    Cρ * z * (1 + Real.log (z ^ 2)) ^ 9 * Y ^ (1 / 2 - σ) ≤ 1 / 8 := by
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hL2' : (1 : ℝ) ≤ L₂ := by linarith
  have hL0 : (0 : ℝ) < L₂ := by linarith
  have hw0 : 0 < w := by rw [hwdef]; linarith
  have hbaselo : (0 : ℝ) < Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by positivity
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le hbaselo hYlo
  have hzpos : (0 : ℝ) < z := by linarith
  have hpoly := logz_factor_pow9_le hQ4 hL2 hu0 hu1 hz1 hzhi
  have hYexp : (1 : ℝ) / 2 - σ < 0 := by linarith
  have hYb : Y ^ (1 / 2 - σ) ≤ Q ^ (104 * (1 / 2 - σ)) * u ^ (-(14 * (1 / 2 - σ))) := by
    have h1 : Y ^ (1 / 2 - σ) ≤ (Q ^ (104 : ℝ) * u ^ (-(14 : ℝ))) ^ (1 / 2 - σ) :=
      Real.rpow_le_rpow_of_nonpos hbaselo hYlo hYexp.le
    rwa [Real.mul_rpow (Real.rpow_nonneg hQ0.le _) (Real.rpow_nonneg hu0.le _),
      ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hu0.le,
      show -(14 : ℝ) * (1 / 2 - σ) = -(14 * (1 / 2 - σ)) by ring] at h1
  -- monomial collapse via ray_pow_bound
  have hγpos : (0 : ℝ) < -(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ)) := by nlinarith [hσlo]
  have hmono := ray_pow_bound (Q := Q) (L₂ := L₂) (c := c) (u := u) (w := w)
    (α := 1 / 2 + 12 + 104 * (1 / 2 - σ))
    (γ := -(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ)))
    (ε := 2 + 9) hQ1 hL2' hcc hu0 hγpos huτ
    (by nlinarith [hσlo, mul_pos hw0 hγpos]) (by nlinarith [hσlo])
  have hQg : Q ^ (1 / 2 : ℝ) * Q ^ (12 : ℝ) * Q ^ (104 * (1 / 2 - σ))
      = Q ^ (1 / 2 + 12 + 104 * (1 / 2 - σ)) := by
    rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
  have hug : u ^ (-(3 : ℝ)) * u ^ (-(9 / 100 : ℝ)) * u ^ (-(14 * (1 / 2 - σ)))
      = u ^ (-(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ))) := by
    rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]
  have hLg : L₂ ^ (2 : ℝ) * L₂ ^ (9 : ℝ) = L₂ ^ (2 + 9 : ℝ) := by rw [← Real.rpow_add hL0]
  have hcollect : ((564 + 72 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀))
        * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
        * (248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ))
        * (Q ^ (104 * (1 / 2 - σ)) * u ^ (-(14 * (1 / 2 - σ))))
      = 2 * (564 + 72 * Z₀) * 248 ^ 9 / c₀
        * (Q ^ (1 / 2 + 12 + 104 * (1 / 2 - σ))
          * u ^ (-(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ)))
          * L₂ ^ (2 + 9 : ℝ)) := by
    rw [← hQg, ← hug, ← hLg]; ring
  -- nonneg facts and the product bound
  have hbnn : (0 : ℝ) ≤ 1 + Real.log (z ^ 2) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ z ^ 2 by nlinarith [hz1]); linarith
  have hpolynn : (0 : ℝ) ≤ (1 + Real.log (z ^ 2)) ^ 9 := pow_nonneg hbnn 9
  have hYsnn : (0 : ℝ) ≤ Y ^ (1 / 2 - σ) := Real.rpow_nonneg hYpos.le _
  have hCbarnn : (0 : ℝ) ≤ (564 + 72 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀) := by
    positivity
  have hzbarnn : (0 : ℝ) ≤ 2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) := by positivity
  have hPbarnn : (0 : ℝ) ≤ 248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ) := by positivity
  have hprod : Cρ * z * (1 + Real.log (z ^ 2)) ^ 9 * Y ^ (1 / 2 - σ)
      ≤ ((564 + 72 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀))
          * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
          * (248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ))
          * (Q ^ (104 * (1 / 2 - σ)) * u ^ (-(14 * (1 / 2 - σ)))) := by
    have h1 : Cρ * z
        ≤ (564 + 72 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀)
          * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) :=
      mul_le_mul hCρ hzhi hzpos.le hCbarnn
    have h2 : Cρ * z * (1 + Real.log (z ^ 2)) ^ 9
        ≤ (564 + 72 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀)
          * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
          * (248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ)) :=
      mul_le_mul h1 hpoly hpolynn (mul_nonneg hCbarnn hzbarnn)
    exact mul_le_mul h2 hYb hYsnn (mul_nonneg (mul_nonneg hCbarnn hzbarnn) hPbarnn)
  have hCnn : (0 : ℝ) ≤ 2 * (564 + 72 * Z₀) * 248 ^ 9 / c₀ := by positivity
  -- TAU-SHARP S2: the Eρ row's **own** γ-floor.  `γ_Eρ(σ) = 14σ − 1009/100` is strictly increasing
  -- in `σ`, so its infimum over the window sits at the CLOSED endpoint `hσlo : 16/17 ≤ σ`, where it
  -- equals `5247/1700` EXACTLY (`14·16/17 − 1009/100 = 22400/1700 − 17153/1700`).  The freeze's
  -- decimal `3.0865` exceeds this by `2.941e−5` and is FALSE at the endpoint — the rational is the
  -- only admissible numeral.  `linarith` (not `nlinarith`): linear in `σ`, tight at equality.
  have hcγ : c ^ (-(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ))) ≤ c ^ (5247 / 1700 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hcc hc1 (by linarith [hσlo])
  calc Cρ * z * (1 + Real.log (z ^ 2)) ^ 9 * Y ^ (1 / 2 - σ)
      ≤ ((564 + 72 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀))
          * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
          * (248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ))
          * (Q ^ (104 * (1 / 2 - σ)) * u ^ (-(14 * (1 / 2 - σ)))) := hprod
    _ = 2 * (564 + 72 * Z₀) * 248 ^ 9 / c₀
        * (Q ^ (1 / 2 + 12 + 104 * (1 / 2 - σ))
          * u ^ (-(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ)))
          * L₂ ^ (2 + 9 : ℝ)) := hcollect
    _ ≤ 2 * (564 + 72 * Z₀) * 248 ^ 9 / c₀
        * c ^ (-(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ))) :=
        mul_le_mul_of_nonneg_left hmono hCnn
    _ ≤ 2 * (564 + 72 * Z₀) * 248 ^ 9 / c₀ * c ^ (5247 / 1700 : ℝ) :=
        mul_le_mul_of_nonneg_left hcγ hCnn
    _ ≤ 1 / 8 := hg

/-- **The `hguard` discharge.** Given `hscale` (`Nr^{1−β₀} ≤ e`) and `Nr ≥ (256G)^4` with
`G ≥ 34`, the R2-error guard `2G·Nr^{1/2−β₀} ≤ 1/64` holds. -/
lemma tbal_hguard {G Nr β₀ : ℝ}
    (hG34 : 34 ≤ G) (hNlo : (256 * G) ^ (4 : ℝ) ≤ Nr) (hscale : Nr ^ (1 - β₀) ≤ Real.exp 1) :
    2 * G * Nr ^ (1 / 2 - β₀) ≤ 1 / 64 := by
  have hG0 : 0 < G := by linarith
  have h256G : 0 < 256 * G := by linarith
  have hNrpos : 0 < Nr := lt_of_lt_of_le (Real.rpow_pos_of_pos h256G _) hNlo
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hsplit : Nr ^ (1 / 2 - β₀) = Nr ^ (1 - β₀) * Nr ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hNrpos]; congr 1; ring
  have hNr12 : Nr ^ (-(1 / 2 : ℝ)) ≤ (256 * G) ^ (-(2 : ℝ)) := by
    have h1 : Nr ^ (-(1 / 2 : ℝ)) ≤ ((256 * G) ^ (4 : ℝ)) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos h256G _) hNlo (by norm_num)
    rwa [← Real.rpow_mul h256G.le, show (4 : ℝ) * (-(1 / 2 : ℝ)) = -(2 : ℝ) by ring] at h1
  have h256Gsq : (256 * G) ^ (-(2 : ℝ)) = 1 / (256 * G) ^ 2 := by
    rw [Real.rpow_neg h256G.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      one_div]
  have hNr12nn : 0 ≤ Nr ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hNrpos _).le
  have hbound : Nr ^ (1 / 2 - β₀) ≤ Real.exp 1 * (256 * G) ^ (-(2 : ℝ)) := by
    rw [hsplit]; exact mul_le_mul hscale hNr12 hNr12nn hepos.le
  have hfin : 2 * G * (Real.exp 1 * (256 * G) ^ (-(2 : ℝ))) ≤ 1 / 64 := by
    rw [h256Gsq,
      show 2 * G * (Real.exp 1 * (1 / (256 * G) ^ 2)) = 2 * G * Real.exp 1 / (256 * G) ^ 2 by ring,
      div_le_iff₀ (by positivity : (0 : ℝ) < (256 * G) ^ 2)]
    have hexp9 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    nlinarith [hexp9, hG34, hG0, mul_nonneg (show (0 : ℝ) ≤ G - 34 by linarith) hG0.le,
      mul_nonneg hG0.le (show (0 : ℝ) ≤ 2.7182818286 - Real.exp 1 by linarith)]
  calc 2 * G * Nr ^ (1 / 2 - β₀)
      ≤ 2 * G * (Real.exp 1 * (256 * G) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ 1 / 64 := hfin

set_option maxHeartbeats 800000 in
-- The log/rpow crush bookkeeping (log_mul/log_div/log_pow chain + the neg_log_le_rpow sub-power
-- bound + the three 1/3-share estimates) exceeds the default budget.
/-- **The `hscale` discharge (log-crush).** On the ray (via `huA/huL2/hsqrt`), `Nr^{1−β₀} ≤ e`
for `Nr ≤ 2(256G)^4`, `G = 34+12M+12MZ₀+36M/u`. -/
lemma tbal_hscale {Q L₂ G Nr β₀ u M Z₀ : ℝ}
    (hu0 : 0 < u) (hu1 : u ≤ 1) (huβ : 1 - β₀ = u)
    (hMnn : 0 ≤ M) (hMB : M ≤ Q ^ (1 / 2 : ℝ) * L₂) (hB1 : 1 ≤ Q ^ (1 / 2 : ℝ) * L₂)
    (hZ0 : 0 ≤ Z₀) (_hL2' : 1 ≤ L₂)
    (hlnB : Real.log (Q ^ (1 / 2 : ℝ) * L₂) ≤ 3 / 2 * L₂)
    (hG : G = 34 + 12 * M + 12 * M * Z₀ + 36 * M / u)
    (hNle : Nr ≤ 2 * (256 * G) ^ 4) (hNpos : 0 < Nr)
    (huA : u * (Real.log 2 + 4 * Real.log (256 * (82 + 12 * Z₀))) ≤ 1 / 3)
    (huL2 : u * L₂ ≤ 1 / 18)
    (hsqrt : Real.sqrt u ≤ 1 / 24) :
    Nr ^ (1 - β₀) ≤ Real.exp 1 := by
  set B : ℝ := Q ^ (1 / 2 : ℝ) * L₂ with hBdef
  have hB0 : 0 < B := by rw [hBdef]; positivity
  have hGpos : 0 < G := by rw [hG]; positivity
  have h256G : 0 < 256 * G := by positivity
  have h2G4 : 0 < 2 * (256 * G) ^ 4 := by positivity
  -- STEP 1 : G ≤ (82+12Z₀)*B/u
  have hGle : G ≤ (82 + 12 * Z₀) * B / u := by
    rw [le_div_iff₀ hu0]
    have h36 : 36 * M / u * u = 36 * M := by
      rw [div_mul_eq_mul_div, mul_div_assoc, div_self hu0.ne', mul_one]
    rw [hG]
    nlinarith [hMB, hB1, hu0, hu1, hZ0, hMnn, h36,
      mul_nonneg hMnn (by linarith : (0 : ℝ) ≤ 1 - u),
      mul_nonneg (mul_nonneg hMnn hZ0) (by linarith : (0 : ℝ) ≤ 1 - u),
      mul_nonneg hZ0 (by linarith : (0 : ℝ) ≤ B - M)]
  -- STEP 2 : log bound
  have hlogbound : Real.log (2 * (256 * G) ^ 4)
      ≤ (Real.log 2 + 4 * Real.log (256 * (82 + 12 * Z₀)))
        + 4 * Real.log B + 4 * (-Real.log u) := by
    have e1 : Real.log (2 * (256 * G) ^ 4) = Real.log 2 + 4 * Real.log (256 * G) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    have hlogG : Real.log (256 * G)
        ≤ Real.log (256 * (82 + 12 * Z₀)) + Real.log B + (-Real.log u) := by
      have hle : Real.log (256 * G) ≤ Real.log (256 * ((82 + 12 * Z₀) * B / u)) := by
        apply Real.log_le_log h256G
        exact mul_le_mul_of_nonneg_left hGle (by norm_num)
      have heq : Real.log (256 * ((82 + 12 * Z₀) * B / u))
          = Real.log (256 * (82 + 12 * Z₀)) + Real.log B + (-Real.log u) := by
        rw [show 256 * ((82 + 12 * Z₀) * B / u) = 256 * (82 + 12 * Z₀) * B / u by ring,
          Real.log_div (by positivity) hu0.ne',
          Real.log_mul (by positivity) hB0.ne']
        ring
      rw [heq] at hle; exact hle
    rw [e1]; linarith [hlogG]
  -- STEP 3 : u * log(...) ≤ 1
  have hlog : u * Real.log (2 * (256 * G) ^ 4) ≤ 1 := by
    have hmul : u * Real.log (2 * (256 * G) ^ 4)
        ≤ u * ((Real.log 2 + 4 * Real.log (256 * (82 + 12 * Z₀)))
          + 4 * Real.log B + 4 * (-Real.log u)) :=
      mul_le_mul_of_nonneg_left hlogbound hu0.le
    -- piece 2 : 4*u*log B ≤ 6*u*L₂ ≤ 1/3
    have hp2 : 4 * u * Real.log B ≤ 1 / 3 := by
      have : 4 * u * Real.log B ≤ 4 * u * (3 / 2 * L₂) :=
        mul_le_mul_of_nonneg_left hlnB (by positivity)
      nlinarith [this, huL2, hu0]
    -- piece 3 : 4*u*(-log u) ≤ 8*sqrt u ≤ 1/3
    have hnlogu : -Real.log u ≤ u ^ (-(1 / 2 : ℝ)) / (1 / 2) := neg_log_le_rpow hu0 (by norm_num)
    have hp3 : 4 * u * (-Real.log u) ≤ 1 / 3 := by
      have huu : u * u ^ (-(1 / 2 : ℝ)) = Real.sqrt u := by
        rw [Real.sqrt_eq_rpow,
          show u * u ^ (-(1 / 2 : ℝ)) = u ^ (1 : ℝ) * u ^ (-(1 / 2 : ℝ)) by rw [Real.rpow_one],
          ← Real.rpow_add hu0, show (1 : ℝ) + -(1 / 2 : ℝ) = 1 / 2 by norm_num]
      have hstep : 4 * u * (-Real.log u) ≤ 4 * u * (2 * u ^ (-(1 / 2 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : u ^ (-(1 / 2 : ℝ)) / (1 / 2) = 2 * u ^ (-(1 / 2 : ℝ)) := by ring
        linarith [hnlogu, this ▸ hnlogu]
      have heq2 : 4 * u * (2 * u ^ (-(1 / 2 : ℝ))) = 8 * (u * u ^ (-(1 / 2 : ℝ))) := by ring
      rw [heq2, huu] at hstep
      linarith [hstep, hsqrt]
    -- combine
    have hexpand : u * ((Real.log 2 + 4 * Real.log (256 * (82 + 12 * Z₀)))
          + 4 * Real.log B + 4 * (-Real.log u))
        = u * (Real.log 2 + 4 * Real.log (256 * (82 + 12 * Z₀)))
          + 4 * u * Real.log B + 4 * u * (-Real.log u) := by ring
    rw [hexpand] at hmul
    linarith [hmul, huA, hp2, hp3]
  -- STEP 0 : assemble
  rw [huβ]
  calc Nr ^ u ≤ (2 * (256 * G) ^ 4) ^ u := Real.rpow_le_rpow hNpos.le hNle hu0.le
    _ = Real.exp (u * Real.log (2 * (256 * G) ^ 4)) := by
        rw [Real.rpow_def_of_pos h2G4, mul_comm]
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hlog

set_option maxHeartbeats 1600000 in
-- heavy Nat.sqrt casting + 4-term ray bookkeeping
/-- **The `hcov` crux.** `crushErr ≤ 0.27·u·z^{1−β₀}` at the ledger scale `z ≍ Q¹²u⁻³`. -/
lemma tbal_hcov {q : ℕ} {Z₀ β₀ Q u : ℝ} {z : ℕ}
    (hZ0 : 0 ≤ Z₀) (hlo : 1 / 2 ≤ β₀) (hhi : β₀ < 1) (huβ : 1 - β₀ = u)
    (hQ4 : 4 ≤ Q)
    (hM4Q : Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) ≤ 4 * Q)
    (hMnn : 0 ≤ Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)))
    (hz2 : 2 ≤ z)
    (hzlo : Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) ≤ (z : ℝ))
    (hzhi : (z : ℝ) ≤ 2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
    (hcue : ⌈(1 : ℝ) / (1 - β₀)⌉₊ ≤ z)
    (hZray : Z₀ * u ≤ 1) :
    crushErr q Z₀ β₀ z ≤ 27 / 100 * ((1 - β₀) * (z : ℝ) ^ (1 - β₀)) := by
  set M : ℝ := Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) with hMdef
  have hu0 : 0 < u := by rw [← huβ]; linarith
  have hu1 : u ≤ 1 := by rw [← huβ]; linarith
  have hQ0 : 0 < Q := by linarith
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hzR2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith
  set S : ℝ := (z : ℝ) ^ (1 - β₀) with hSdef
  have hSpos : 0 < S := Real.rpow_pos_of_pos hzpos _
  have hQ6pos : (0 : ℝ) < Q ^ (6 : ℝ) := Real.rpow_pos_of_pos hQ0 _
  have hu2pos : (0 : ℝ) < u ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hu0 _
  -- ===== crush cut and its bounds =====
  set c1 : ℕ := ⌈(1 : ℝ) / (1 - β₀)⌉₊ with hc1def
  have hDeq : crushCut β₀ z = Nat.sqrt (z * c1) := by
    rw [crushCut, min_eq_left hcue]
  set D : ℕ := Nat.sqrt (z * c1) with hDdef
  have h1eq : (1 : ℝ) / (1 - β₀) = 1 / u := by rw [huβ]
  have hc1lo : (1 : ℝ) / u ≤ (c1 : ℝ) := by
    rw [hc1def, ← h1eq]; exact Nat.le_ceil _
  have hc1hi : (c1 : ℝ) ≤ 1 / u + 1 := by
    rw [hc1def, ← h1eq]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hc1pos : 0 < c1 := by
    have : (0 : ℝ) < (c1 : ℝ) := lt_of_lt_of_le (by positivity) hc1lo
    exact_mod_cast this
  have hu4 : u ^ (-(3 : ℝ)) * (1 / u) = u ^ (-(4 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hu0]; norm_num
  have hzc1lo : Q ^ (12 : ℝ) * u ^ (-(4 : ℝ)) ≤ (z : ℝ) * (c1 : ℝ) := by
    calc Q ^ (12 : ℝ) * u ^ (-(4 : ℝ))
        = (Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) * (1 / u) := by rw [mul_assoc, hu4]
      _ ≤ (z : ℝ) * (c1 : ℝ) := mul_le_mul hzlo hc1lo (by positivity) (by positivity)
  have hzc1hi : (z : ℝ) * (c1 : ℝ) ≤ 4 * Q ^ (12 : ℝ) * u ^ (-(4 : ℝ)) := by
    have hc1hi2 : (c1 : ℝ) ≤ 2 * (1 / u) := by
      have : (1 : ℝ) ≤ 1 / u := by rw [le_div_iff₀ hu0]; linarith
      linarith [hc1hi]
    calc (z : ℝ) * (c1 : ℝ)
        ≤ (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) * (2 * (1 / u)) :=
          mul_le_mul hzhi hc1hi2 (by positivity) (by positivity)
      _ = 4 * Q ^ (12 : ℝ) * u ^ (-(4 : ℝ)) := by
          rw [show (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) * (2 * (1 / u))
              = 4 * Q ^ (12 : ℝ) * (u ^ (-(3 : ℝ)) * (1 / u)) by ring, hu4]
  have hsq2 : (2 * Q ^ (6 : ℝ) * u ^ (-(2 : ℝ))) ^ 2 = 4 * Q ^ (12 : ℝ) * u ^ (-(4 : ℝ)) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (Q ^ (6 : ℝ)) 2, ← Real.rpow_mul hQ0.le,
      ← Real.rpow_natCast (u ^ (-(2 : ℝ))) 2, ← Real.rpow_mul hu0.le]
    push_cast; ring_nf
  have hsq1 : (Q ^ (6 : ℝ) * u ^ (-(2 : ℝ))) ^ 2 = Q ^ (12 : ℝ) * u ^ (-(4 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (Q ^ (6 : ℝ)) 2, ← Real.rpow_mul hQ0.le,
      ← Real.rpow_natCast (u ^ (-(2 : ℝ))) 2, ← Real.rpow_mul hu0.le]
    push_cast; ring_nf
  have hDsqle : (D : ℝ) * (D : ℝ) ≤ (z : ℝ) * (c1 : ℝ) := by
    have hh := Nat.sqrt_le' (z * c1)
    rw [← hDdef, pow_two] at hh
    exact_mod_cast hh
  have hDsqgt : (z : ℝ) * (c1 : ℝ) < ((D : ℝ) + 1) * ((D : ℝ) + 1) := by
    have hh := Nat.lt_succ_sqrt' (z * c1)
    rw [← hDdef, pow_two] at hh
    exact_mod_cast hh
  have hDnat_le_z : D ≤ z := by
    rw [hDdef]
    calc Nat.sqrt (z * c1) ≤ Nat.sqrt (z * z) :=
          Nat.sqrt_le_sqrt (Nat.mul_le_mul_left z hcue)
      _ = z := by rw [← pow_two]; exact Nat.sqrt_eq' z
  have hzc1_one : 1 ≤ z * c1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hc1pos.ne')
  have hDposN : 0 < D := by
    rw [hDdef]
    have h := Nat.sqrt_le_sqrt hzc1_one
    rw [Nat.sqrt_one] at h; omega
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDposN
  have hDlez : (D : ℝ) ≤ (z : ℝ) := by exact_mod_cast hDnat_le_z
  have hbig : (0 : ℝ) < 2 * Q ^ (6 : ℝ) * u ^ (-(2 : ℝ)) := by positivity
  have hDup : (D : ℝ) ≤ 2 * Q ^ (6 : ℝ) * u ^ (-(2 : ℝ)) := by
    have h1 : (D : ℝ) * (D : ℝ) ≤ (2 * Q ^ (6 : ℝ) * u ^ (-(2 : ℝ))) ^ 2 := by
      rw [hsq2]; exact le_trans hDsqle hzc1hi
    nlinarith [hDpos, hbig, h1]
  have hQ6u2ge : (4 : ℝ) ≤ Q ^ (6 : ℝ) * u ^ (-(2 : ℝ)) := by
    have h1 : (4 : ℝ) ^ (6 : ℝ) ≤ Q ^ (6 : ℝ) := Real.rpow_le_rpow (by norm_num) hQ4 (by norm_num)
    have h2 : (1 : ℝ) ≤ u ^ (-(2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
    have h46 : (4096 : ℝ) ≤ (4 : ℝ) ^ (6 : ℝ) := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    nlinarith [h1, h2, h46, Real.rpow_pos_of_pos hQ0 (6 : ℝ)]
  have hDlo : (3 / 4 : ℝ) * (Q ^ (6 : ℝ) * u ^ (-(2 : ℝ))) ≤ (D : ℝ) := by
    have h1 : (Q ^ (6 : ℝ) * u ^ (-(2 : ℝ))) ^ 2 ≤ ((D : ℝ) + 1) * ((D : ℝ) + 1) := by
      rw [hsq1]; exact le_of_lt (lt_of_le_of_lt hzc1lo hDsqgt)
    have hbase : Q ^ (6 : ℝ) * u ^ (-(2 : ℝ)) ≤ (D : ℝ) + 1 := by
      nlinarith [hDpos, Real.rpow_pos_of_pos hQ0 (6 : ℝ), hu2pos, h1]
    nlinarith [hbase, hQ6u2ge]
  -- ===== rpow identities =====
  have hzneg : (z : ℝ) ^ (-β₀) = S / (z : ℝ) := by
    rw [hSdef, show -β₀ = (1 - β₀) + (-1 : ℝ) by ring, Real.rpow_add hzpos, Real.rpow_neg_one,
      div_eq_mul_inv]
  have hDrpow_le : (D : ℝ) ^ (-β₀) ≤ S / (D : ℝ) := by
    have hDu : (D : ℝ) ^ (1 - β₀) ≤ S := by
      rw [hSdef]; exact Real.rpow_le_rpow hDpos.le hDlez (by rw [huβ]; exact hu0.le)
    rw [show -β₀ = (1 - β₀) + (-1 : ℝ) by ring, Real.rpow_add hDpos, Real.rpow_neg_one,
      div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hDu (by positivity)
  -- ===== per-term bounds =====
  have hDz : (D : ℝ) / (z : ℝ) ≤ 2 * u / Q ^ (6 : ℝ) := by
    rw [div_le_div_iff₀ hzpos hQ6pos]
    have hQ12 : Q ^ (6 : ℝ) * Q ^ (6 : ℝ) = Q ^ (12 : ℝ) := by rw [← Real.rpow_add hQ0]; norm_num
    have hu23 : u ^ (-(2 : ℝ)) = u * u ^ (-(3 : ℝ)) := by
      rw [show (-(2 : ℝ)) = 1 + -(3 : ℝ) by norm_num, Real.rpow_add hu0, Real.rpow_one]
    calc (D : ℝ) * Q ^ (6 : ℝ) ≤ (2 * Q ^ (6 : ℝ) * u ^ (-(2 : ℝ))) * Q ^ (6 : ℝ) :=
          mul_le_mul_of_nonneg_right hDup hQ6pos.le
      _ = 2 * u * (Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) := by rw [hu23, ← hQ12]; ring
      _ ≤ 2 * u * (z : ℝ) := mul_le_mul_of_nonneg_left hzlo (by positivity)
  have hDinv : 1 / (D : ℝ) ≤ (4 / 3) * u ^ (2 : ℝ) / Q ^ (6 : ℝ) := by
    rw [div_le_div_iff₀ hDpos (by positivity)]
    have hu22 : u ^ (2 : ℝ) * u ^ (-(2 : ℝ)) = 1 := by rw [← Real.rpow_add hu0]; norm_num
    calc (1 : ℝ) * Q ^ (6 : ℝ) = Q ^ (6 : ℝ) := one_mul _
      _ = (4 / 3) * u ^ (2 : ℝ) * ((3 / 4) * (Q ^ (6 : ℝ) * u ^ (-(2 : ℝ)))) := by
          rw [show (4 / 3 : ℝ) * u ^ (2 : ℝ) * ((3 / 4) * (Q ^ (6 : ℝ) * u ^ (-(2 : ℝ))))
              = Q ^ (6 : ℝ) * (u ^ (2 : ℝ) * u ^ (-(2 : ℝ))) by ring, hu22, mul_one]
      _ ≤ (4 / 3) * u ^ (2 : ℝ) * (D : ℝ) := mul_le_mul_of_nonneg_left hDlo (by positivity)
  -- ===== shared numeric facts =====
  have h1βpos : (0 : ℝ) < 1 - β₀ := by rw [huβ]; exact hu0
  have hS1 : (1 : ℝ) ≤ S := by
    rw [hSdef]; exact Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ z)) h1βpos.le
  have hQ6 : (4096 : ℝ) ≤ Q ^ (6 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num) hQ4 (by norm_num : (0 : ℝ) ≤ 6)
    rwa [show (4 : ℝ) ^ (6 : ℝ) = 4096 from by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num] at h
  have hQ5 : (1024 : ℝ) ≤ Q ^ (5 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num) hQ4 (by norm_num : (0 : ℝ) ≤ 5)
    rwa [show (4 : ℝ) ^ (5 : ℝ) = 1024 from by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num] at h
  have hQ65 : Q ^ (6 : ℝ) = Q ^ (5 : ℝ) * Q := by
    rw [show (6 : ℝ) = 5 + 1 by norm_num, Real.rpow_add hQ0, Real.rpow_one]
  have huu2 : u * u * u ^ (-(2 : ℝ)) = 1 := by
    rw [show u * u = u ^ (2 : ℝ) from by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring,
      ← Real.rpow_add hu0, show (2 : ℝ) + -(2 : ℝ) = 0 by norm_num, Real.rpow_zero]
  have hUD : (3 / 4 : ℝ) * Q ^ (6 : ℝ) ≤ u * u * (D : ℝ) := by
    calc (3 / 4 : ℝ) * Q ^ (6 : ℝ)
        = u * u * ((3 / 4) * (Q ^ (6 : ℝ) * u ^ (-(2 : ℝ)))) := by
          rw [show u * u * ((3 / 4) * (Q ^ (6 : ℝ) * u ^ (-(2 : ℝ))))
              = (3 / 4) * Q ^ (6 : ℝ) * (u * u * u ^ (-(2 : ℝ))) by ring, huu2, mul_one]
      _ ≤ u * u * (D : ℝ) := mul_le_mul_of_nonneg_left hDlo (by positivity)
  have hXnn : (0 : ℝ) ≤ (1 - β₀) * S := mul_nonneg h1βpos.le hSpos.le
  -- ===== the four term bounds =====
  have hT1 : 34 * (D : ℝ) * (z : ℝ) ^ (-β₀) ≤ 2 / 100 * ((1 - β₀) * S) := by
    rw [hzneg, huβ]
    rw [show 34 * (D : ℝ) * (S / (z : ℝ)) = 34 * S * ((D : ℝ) / (z : ℝ)) by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring]
    refine le_trans (mul_le_mul_of_nonneg_left hDz (by positivity)) ?_
    rw [show 34 * S * (2 * u / Q ^ (6 : ℝ)) = 68 * (u * S) / Q ^ (6 : ℝ) by ring,
      div_le_iff₀ hQ6pos]
    nlinarith [mul_le_mul_of_nonneg_left hQ6 (mul_pos hu0 hSpos).le]
  have hkey12 : 12 * M * S ≤ 7 / 100 * (u * S) * (u * (D : ℝ)) := by
    have hA : 12 * M * S ≤ 48 * Q * S := by
      nlinarith [mul_le_mul_of_nonneg_right hM4Q hSpos.le]
    have hB : 48 * Q * S ≤ (21 / 400) * (Q ^ (6 : ℝ) * S) := by
      have hb0 : 48 * Q ≤ (21 / 400) * Q ^ (6 : ℝ) := by
        have hb : (1024 : ℝ) * Q ≤ Q ^ (6 : ℝ) := by
          rw [hQ65]; exact mul_le_mul_of_nonneg_right hQ5 hQ0.le
        nlinarith [hb, hQ0.le]
      nlinarith [mul_le_mul_of_nonneg_right hb0 hSpos.le]
    have hC : (21 / 400) * (Q ^ (6 : ℝ) * S) ≤ 7 / 100 * (u * S) * (u * (D : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_right hUD hSpos.le]
    nlinarith [hA, hB, hC]
  have hT2 : 12 * M * S / ((1 - β₀) * (D : ℝ)) ≤ 7 / 100 * ((1 - β₀) * S) := by
    rw [huβ, div_le_iff₀ (mul_pos hu0 hDpos)]; exact hkey12
  have hT3 : 12 * M * S / (D : ℝ) ≤ 7 / 100 * ((1 - β₀) * S) := by
    refine le_trans ?_ hT2
    rw [div_le_div_iff₀ hDpos (by rw [huβ]; exact mul_pos hu0 hDpos)]
    have h1β : (1 - β₀) ≤ 1 := by rw [huβ]; exact hu1
    nlinarith [h1β, mul_nonneg (mul_nonneg hMnn hSpos.le) hDpos.le]
  have hT4 : 6 * M * (Z₀ + 1 / (1 - β₀)) * (D : ℝ) ^ (-β₀) ≤ 7 / 100 * ((1 - β₀) * S) := by
    have hcoefnn : 0 ≤ 6 * M * (Z₀ + 1 / (1 - β₀)) :=
      mul_nonneg (mul_nonneg (by norm_num) hMnn)
        (add_nonneg hZ0 (div_nonneg (by norm_num) h1βpos.le))
    refine le_trans (mul_le_mul_of_nonneg_left hDrpow_le hcoefnn) ?_
    have hune : u ≠ 0 := hu0.ne'
    have hDne : (D : ℝ) ≠ 0 := hDpos.ne'
    rw [huβ, show 6 * M * (Z₀ + 1 / u) * (S / (D : ℝ))
        = 6 * M * (Z₀ * u + 1) * S / (u * (D : ℝ)) from by
      field_simp]
    rw [div_le_iff₀ (mul_pos hu0 hDpos)]
    have e0 : 6 * M * (Z₀ * u + 1) * S ≤ 12 * M * S := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hMnn) hSpos.le)
        (by linarith [hZray] : (0 : ℝ) ≤ 1 - Z₀ * u)]
    exact le_trans e0 hkey12
  -- ===== combine =====
  simp only [crushErr, hDeq, ← hMdef, ← hSdef]
  linarith [hT1, hT2, hT3, hT4, hXnn]

set_option maxHeartbeats 800000 in
-- The C2Rho/CwRho unfolding produces a 6-term sum whose per-term division bounds + the two folds
-- (into `r = L₂/c₀`, then `M ≤ Q^{1/2}L₂`) exceed the default budget.
/-- **The ρ-extraction constant bound.** `C2Rho q Z₀ ρ ≤ (564+72Z₀)·√Q·L₂²/c₀` via the ZFR pole
floors `1/‖1−ρ‖, 1/(1−σ) ≤ L₂/c₀` and the crude `‖ρ‖ ≤ 2`. -/
lemma C2Rho_le {q : ℕ} {Z₀ Q L₂ c₀ : ℝ} {ρ : ℂ}
    (hσlo : 16 / 17 ≤ ρ.re) (hσ1 : ρ.re < 1) (him : |ρ.im| ≤ 1)
    (hZ0 : 0 ≤ Z₀) (hc0 : 0 < c₀) (hLc : 1 ≤ L₂ / c₀) (hL2' : 1 ≤ L₂)
    (hMQ : Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) ≤ Q ^ (1 / 2 : ℝ) * L₂)
    (hMnn : 0 ≤ Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)))
    (hBpos : 1 ≤ Q ^ (1 / 2 : ℝ) * L₂)
    (hpole : 1 / ‖1 - ρ‖ ≤ L₂ / c₀) (hsig : 1 / (1 - ρ.re) ≤ L₂ / c₀)
    (hnpos : 0 < ‖1 - ρ‖) :
    C2Rho q Z₀ ρ ≤ (564 + 72 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀) := by
  rw [C2Rho, CwRho]
  set M : ℝ := Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) with hMdef
  set B : ℝ := Q ^ (1 / 2 : ℝ) * L₂ with hBdef
  set r : ℝ := L₂ / c₀ with hrdef
  have hσ0 : 0 < ρ.re := by linarith
  have hσn : 0 < 1 - ρ.re := by linarith
  have hr1 : 1 ≤ r := hLc
  have hrnn : 0 ≤ r := by linarith
  have hρ2 : ‖ρ‖ ≤ 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im ρ
    rw [abs_of_pos hσ0] at h; linarith [him, hσ1]
  have hρnn : 0 ≤ ‖ρ‖ := norm_nonneg _
  -- P := 3M(1+‖ρ‖/σ), 0 ≤ P ≤ 12M
  have hρσ : ‖ρ‖ / ρ.re ≤ 3 := by rw [div_le_iff₀ hσ0]; nlinarith [hρ2, hσlo]
  have hρσnn : 0 ≤ ‖ρ‖ / ρ.re := div_nonneg hρnn hσ0.le
  set P : ℝ := 3 * M * (1 + ‖ρ‖ / ρ.re) with hPdef
  have hPnn : 0 ≤ P := by rw [hPdef]; positivity
  have hPle : P ≤ 12 * M := by rw [hPdef]; nlinarith [hρσ, hMnn, hρσnn]
  -- per-term bounds (into r)
  have hA : 12 * M / ‖1 - ρ‖ ≤ 12 * M * r := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hpole (by positivity)
  have hB : 2 * (9 + 8 * ‖ρ‖) ≤ 50 := by nlinarith [hρ2]
  have hC : 2 * (Z₀ + 1 / ‖1 - ρ‖) * P ≤ 24 * M * Z₀ + 24 * M * r := by
    have h1 : Z₀ + 1 / ‖1 - ρ‖ ≤ Z₀ + r := by linarith [hpole]
    have h2 : 2 * (Z₀ + 1 / ‖1 - ρ‖) * P ≤ 2 * (Z₀ + r) * (12 * M) := by
      apply mul_le_mul _ hPle hPnn (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    nlinarith [h2]
  have hD : 2 * P ≤ 24 * M := by linarith [hPle]
  have hE : 2 * P / (1 - ρ.re) ≤ 24 * M * r := by
    rw [div_eq_mul_one_div]
    have h1 : 2 * P * (1 / (1 - ρ.re)) ≤ 2 * (12 * M) * r := by
      apply mul_le_mul _ hsig (by positivity) (by positivity)
      linarith [hPle]
    linarith [h1]
  have hExtra : 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) ≤ 162 * M * r := by
    have hdist : 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re))
        = 90 * M / ‖1 - ρ‖ + 72 * M / (1 - ρ.re) := by
      field_simp; ring
    rw [hdist]
    have h1 : 90 * M / ‖1 - ρ‖ ≤ 90 * M * r := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hpole (by positivity)
    have h2 : 72 * M / (1 - ρ.re) ≤ 72 * M * r := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hsig (by positivity)
    linarith [h1, h2]
  -- combine : LHS ≤ 150 + 72M + 72MZ₀ + 342Mr
  have hLHS1 : 3 * (12 * M / ‖1 - ρ‖ + 2 * (9 + 8 * ‖ρ‖) + 2 * (Z₀ + 1 / ‖1 - ρ‖) * P + 2 * P
        + 2 * P / (1 - ρ.re)) + 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re))
      ≤ 150 + 72 * M + 72 * M * Z₀ + 342 * (M * r) := by
    nlinarith [hA, hB, hC, hD, hE, hExtra]
  -- fold 1 : ≤ (150+414M+72MZ₀)*r
  have hfold1 : 150 + 72 * M + 72 * M * Z₀ + 342 * (M * r) ≤ (150 + 414 * M + 72 * M * Z₀) * r := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 150 by norm_num) (by linarith : (0 : ℝ) ≤ r - 1),
      mul_nonneg hMnn (by linarith : (0 : ℝ) ≤ r - 1),
      mul_nonneg (mul_nonneg hMnn hZ0) (by linarith : (0 : ℝ) ≤ r - 1)]
  -- fold 2 : (150+414M+72MZ₀) ≤ (564+72Z₀)*B
  have hfold2 : 150 + 414 * M + 72 * M * Z₀ ≤ (564 + 72 * Z₀) * B := by
    nlinarith [hMQ, hBpos, hZ0, hMnn,
      mul_nonneg hZ0 (by linarith [hMQ] : (0 : ℝ) ≤ B - M)]
  have hfold2r : (150 + 414 * M + 72 * M * Z₀) * r ≤ (564 + 72 * Z₀) * B * r :=
    mul_le_mul_of_nonneg_right hfold2 hrnn
  -- final identity : (564+72Z₀)*B*r = RHS
  have hL2sq : L₂ ^ (2 : ℝ) = L₂ * L₂ := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have hfinaleq : (564 + 72 * Z₀) * B * r
      = (564 + 72 * Z₀) * (Q ^ (1 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀) := by
    rw [hBdef, hrdef, hL2sq]; field_simp
  linarith [hLHS1, hfold1, hfold2r, hfinaleq ▸ le_refl ((564 + 72 * Z₀) * B * r)]

/-- ceil bounds: `x ≤ ⌈x⌉ ≤ 2x` for `x ≥ 1`. -/
private lemma ceil_dbl {x : ℝ} (hx : 1 ≤ x) : x ≤ (⌈x⌉₊ : ℝ) ∧ (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  refine ⟨Nat.le_ceil x, ?_⟩
  have h1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  linarith

set_option maxHeartbeats 3200000 in
-- The per-instance assembly threads the 5 row caps + 6 guard discharges through `dh_master_ray`;
-- the accumulated `rpow`/`nlinarith` elaboration exceeds the default budget.
/-- The per-instance body of `dh_repulsion_ordered` (light context: `c` opaque, all `c`-thresholds
as hypotheses). -/
private lemma dh_repulsion_inst {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (_hχ1 : χ ≠ 1) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q)
    {β₀ : ℝ} (hβ0zero : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0)
    (hβ0lo : 1 / 2 < β₀) (hβ0hi : β₀ < 1)
    {ρ : ℂ} (hρzero : DirichletCharacter.LFunction χ ρ = 0) (hρim : ρ.im ≠ 0)
    (himρ : |ρ.im| ≤ 1) (hσlo : 16 / 17 ≤ ρ.re) (hσ1 : ρ.re < 1) (hord : ρ.re ≤ β₀)
    {c₀ Z₀ c : ℝ}
    (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    (hc₀pos : 0 < c₀) (hc₀le1 : c₀ ≤ 1) (hZ0nn : 0 ≤ Z₀)
    (hfloor : ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)))
    (hcpos : 0 < c) (hc1 : c ≤ 1) (hc_t1 : c ≤ 1 / 40)
    (hc_t2 : c ≤ (c₀ / 32) ^ (17 / 3 : ℝ))
    (hc_t3 : c ≤ (1 / 805 : ℝ) ^ (50 / 49 : ℝ))
    (hc_t4 : c ≤ (1 / (8 * 1610 * Real.exp 1)) ^ (850 / 133 : ℝ)) (hc_t5 : c ≤ 1 / 2)
    (hc_t6 : c ≤ (1 / (16 * (328 + 48 * Z₀) * 248 ^ 9)) ^ (1700 / 3547 : ℝ))
    (hc_t7 : c ≤ (c₀ / (16 * (564 + 72 * Z₀) * 248 ^ 9)) ^ (1700 / 5247 : ℝ))
    (hc_t8 : c ≤ 1 / (3 * (Real.log 2 + 4 * Real.log (256 * (82 + 12 * Z₀)))))
    (hc_t9 : c ≤ 1 / 18) (hc_t10 : c ≤ 1 / 576) (hc_t11 : c ≤ 1 / (Z₀ + 1)) :
    (1 - β₀) ≥ c * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(680 * (1 - ρ.re)))
      / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ (14 : ℝ) := by
  set Q : ℝ := (q : ℝ) * (|ρ.im| + 2) with hQdef
  set L₂ : ℝ := Real.log Q + 2 with hL₂def
  set u : ℝ := 1 - β₀ with hudef
  set σ : ℝ := ρ.re with hσdef
  set w : ℝ := 1 - σ with hwdef
  set M : ℝ := Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) with hMdef
  have hu0 : 0 < u := by rw [hudef]; linarith only [hβ0hi]
  have hu_half : u ≤ 1 / 2 := by rw [hudef]; linarith only [hβ0lo]
  have hu1 : u ≤ 1 := by linarith only [hu_half]
  have huβ : 1 - β₀ = u := hudef.symm
  have hσlo' : 16 / 17 ≤ σ := hσlo
  have hσ1' : σ < 1 := hσ1
  have hσβ : σ ≤ β₀ := hord
  have hw0 : 0 < w := by rw [hwdef]; linarith only [hσ1']
  have hwle : w ≤ 1 / 17 := by rw [hwdef]; linarith only [hσlo']
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQ4 : 4 ≤ Q := by rw [hQdef]; nlinarith only [hqR, abs_nonneg ρ.im]
  have hQ0 : 0 < Q := by linarith only [hQ4]
  have hQ1 : (1 : ℝ) ≤ Q := by linarith only [hQ4]
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hlogQpos : 0 < Real.log Q := Real.log_pos (by linarith only [hQ4])
  have hL₂ge2 : (2 : ℝ) ≤ L₂ := by rw [hL₂def]; linarith only [hlogQ0]
  have hL₂1 : (1 : ℝ) ≤ L₂ := by linarith only [hL₂ge2]
  have hL₂pos : (0 : ℝ) < L₂ := by linarith only [hL₂ge2]
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hβ0 : 0 ≤ β₀ := by linarith only [hβ0lo]
  rw [ge_iff_le]
  by_cases htriv : 1 / (40 * L₂) ≤ u
  · -- trivial branch (TAU-SHARP S1: the generalised split takes `c` itself, via `c ≤ 1/40 ≤ 1`)
    have hsplit := tbal_tau_le_split (c := c) hQ1 hw0 hcpos.le (le_trans hc_t1 (by norm_num))
    rw [← hL₂def] at hsplit
    linarith only [hsplit, htriv]
  · -- deep branch
    rw [not_le] at htriv
    by_contra hcon
    rw [not_le] at hcon
    have huτ : u ≤ c * Q ^ (-(680 * w)) / L₂ ^ (14 : ℝ) := le_of_lt hcon
    -- ray facts
    have hQpow_le1 : Q ^ (-(680 * w)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by nlinarith only [hw0])
    have hL14pos : (0 : ℝ) < L₂ ^ (14 : ℝ) := Real.rpow_pos_of_pos hL₂pos _
    have hL14ge1 : (1 : ℝ) ≤ L₂ ^ (14 : ℝ) := Real.one_le_rpow hL₂1 (by norm_num)
    have hL2leL14 : L₂ ≤ L₂ ^ (14 : ℝ) := by
      calc L₂ = L₂ ^ (1 : ℝ) := (Real.rpow_one L₂).symm
        _ ≤ L₂ ^ (14 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL₂1 (by norm_num)
    have huL14c : u * L₂ ^ (14 : ℝ) ≤ c := by
      have h1 := mul_le_mul_of_nonneg_right huτ hL14pos.le
      rw [div_mul_cancel₀ _ hL14pos.ne'] at h1
      nlinarith only [h1, hQpow_le1, hcpos.le]
    have hu_le_c : u ≤ c := by
      nlinarith only [huL14c, mul_nonneg hu0.le (show (0 : ℝ) ≤ L₂ ^ (14 : ℝ) - 1 by linarith)]
    have huL2c : u * L₂ ≤ c :=
      le_trans (by nlinarith only [mul_le_mul_of_nonneg_left hL2leL14 hu0.le]) huL14c
    -- guard thresholds
    have hZray : Z₀ * u ≤ 1 := by
      have h11 : u ≤ 1 / (Z₀ + 1) := le_trans hu_le_c hc_t11
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < Z₀ + 1)] at h11
      nlinarith only [h11, hu0.le, hZ0nn]
    have huA : u * (Real.log 2 + 4 * Real.log (256 * (82 + 12 * Z₀))) ≤ 1 / 3 := by
      have h8 : u ≤ 1 / (3 * (Real.log 2 + 4 * Real.log (256 * (82 + 12 * Z₀)))) :=
        le_trans hu_le_c hc_t8
      have hApos : (0 : ℝ) < 3 * (Real.log 2 + 4 * Real.log (256 * (82 + 12 * Z₀))) := by
        have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have h2 : 0 ≤ Real.log (256 * (82 + 12 * Z₀)) := Real.log_nonneg (by nlinarith only [hZ0nn])
        nlinarith
      rw [le_div_iff₀ hApos] at h8; nlinarith only [h8]
    have huL2g : u * L₂ ≤ 1 / 18 := le_trans huL2c hc_t9
    have hsqrtg : Real.sqrt u ≤ 1 / 24 := by
      have h10 : u ≤ 1 / 576 := le_trans hu_le_c hc_t10
      calc Real.sqrt u ≤ Real.sqrt (1 / 576) := Real.sqrt_le_sqrt h10
        _ = 1 / 24 := by
            rw [show (1 / 576 : ℝ) = (1 / 24) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    -- scales
    set z : ℕ := ⌈Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))⌉₊ with hzdef
    set Y : ℕ := ⌈Q ^ (104 : ℝ) * u ^ (-(14 : ℝ))⌉₊ with hYdef
    set G : ℝ := 34 + 12 * M + 12 * M * Z₀ + 36 * M / (1 - β₀) with hGdef
    set N : ℕ := ⌈(256 * G) ^ (4 : ℝ)⌉₊ with hNdef
    have hzarg1 : (1 : ℝ) ≤ Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) := by
      have h1 : (1 : ℝ) ≤ Q ^ (12 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
      have h2 : (1 : ℝ) ≤ u ^ (-(3 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
      nlinarith only [h1, h2]
    have hYarg1 : (1 : ℝ) ≤ Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by
      have h1 : (1 : ℝ) ≤ Q ^ (104 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
      have h2 : (1 : ℝ) ≤ u ^ (-(14 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
      nlinarith only [h1, h2]
    have hGdiv : (0 : ℝ) ≤ 36 * M / (1 - β₀) :=
      div_nonneg (mul_nonneg (by norm_num) hMnn) (by linarith)
    have hG34 : 34 ≤ G := by rw [hGdef]; nlinarith only [hMnn, hZ0nn, hGdiv, mul_nonneg hMnn hZ0nn]
    have hNarg1 : (1 : ℝ) ≤ (256 * G) ^ (4 : ℝ) :=
      Real.one_le_rpow (by nlinarith only [hG34]) (by norm_num)
    have hzlo_r : Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) ≤ (z : ℝ) := by
      rw [hzdef]; exact (ceil_dbl hzarg1).1
    have hzhi_r : (z : ℝ) ≤ 2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) := by
      rw [hzdef, mul_assoc]; exact (ceil_dbl hzarg1).2
    have hYlo_r : Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) ≤ (Y : ℝ) := by
      rw [hYdef]; exact (ceil_dbl hYarg1).1
    have hYhi_r : (Y : ℝ) ≤ 2 * Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by
      rw [hYdef, mul_assoc]; exact (ceil_dbl hYarg1).2
    have h4eq : (256 * G) ^ (4 : ℝ) = (256 * G) ^ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hNlo_r : (256 * G) ^ (4 : ℝ) ≤ (N : ℝ) := by rw [hNdef]; exact (ceil_dbl hNarg1).1
    have hNhi_npow : (N : ℝ) ≤ 2 * (256 * G) ^ 4 := by
      rw [← h4eq, hNdef]; exact (ceil_dbl hNarg1).2
    have hQ12ge4 : (4 : ℝ) ≤ Q ^ (12 : ℝ) := by
      calc (4 : ℝ) ≤ Q := hQ4
        _ = Q ^ (1 : ℝ) := (Real.rpow_one Q).symm
        _ ≤ Q ^ (12 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
    have hu3ge1 : (1 : ℝ) ≤ u ^ (-(3 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
    have hz2 : 2 ≤ z := by
      have hge : (2 : ℝ) ≤ Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) := by
        nlinarith only [hQ12ge4, mul_nonneg (Real.rpow_pos_of_pos hQ0 (12 : ℝ)).le
          (show (0 : ℝ) ≤ u ^ (-(3 : ℝ)) - 1 by linarith only [hu3ge1])]
      have : (2 : ℝ) ≤ (z : ℝ) := le_trans hge hzlo_r
      exact_mod_cast this
    have hQ104ge4 : (4 : ℝ) ≤ Q ^ (104 : ℝ) := by
      calc (4 : ℝ) ≤ Q := hQ4
        _ = Q ^ (1 : ℝ) := (Real.rpow_one Q).symm
        _ ≤ Q ^ (104 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
    have hu14ge1 : (1 : ℝ) ≤ u ^ (-(14 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
    have hY4 : 4 ≤ Y := by
      have hge : (4 : ℝ) ≤ Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by
        nlinarith only [hQ104ge4, mul_nonneg (Real.rpow_pos_of_pos hQ0 (104 : ℝ)).le
          (show (0 : ℝ) ≤ u ^ (-(14 : ℝ)) - 1 by linarith only [hu14ge1])]
      have : (4 : ℝ) ≤ (Y : ℝ) := le_trans hge hYlo_r
      exact_mod_cast this
    have h256G1 : (1 : ℝ) ≤ 256 * G := by nlinarith only [hG34]
    have hN4 : 4 ≤ N := by
      have hge : (4 : ℝ) ≤ (256 * G) ^ (4 : ℝ) := by
        calc (4 : ℝ) ≤ 256 * G := by nlinarith only [hG34]
          _ = (256 * G) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (256 * G) ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le h256G1 (by norm_num)
      have : (4 : ℝ) ≤ (N : ℝ) := le_trans hge hNlo_r
      exact_mod_cast this
    -- ===== derived facts =====
    have hqQ : (q : ℝ) ≤ Q := by rw [hQdef]; nlinarith only [hqR, abs_nonneg ρ.im]
    have hsqrtqQ : Real.sqrt (q : ℝ) ≤ Q ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt hqQ
    have hlogqL2 : 1 + Real.log (q : ℝ) ≤ L₂ := by
      rw [hL₂def]
      have hll : Real.log (q : ℝ) ≤ Real.log Q := Real.log_le_log (by positivity) hqQ
      linarith only [hll]
    have hMB : M ≤ Q ^ (1 / 2 : ℝ) * L₂ := by
      rw [hMdef]; exact mul_le_mul hsqrtqQ hlogqL2 (by positivity) (by positivity)
    have hsq1 : (1 : ℝ) ≤ Q ^ (1 / 2 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
    have hB1 : (1 : ℝ) ≤ Q ^ (1 / 2 : ℝ) * L₂ := by nlinarith only [hsq1, hL₂1]
    have hQsqsq : Q ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) = Q := by rw [← Real.rpow_add hQ0]; norm_num
    have hlogQ2 : Real.log Q ≤ 2 * Q ^ (1 / 2 : ℝ) := by
      have h := Real.log_le_rpow_div hQ0.le (show (0 : ℝ) < 1 / 2 by norm_num)
      linarith only [h, show Q ^ (1 / 2 : ℝ) / (1 / 2) = 2 * Q ^ (1 / 2 : ℝ) by ring]
    have hM4Q : M ≤ 4 * Q := by
      have hL2le : L₂ ≤ 4 * Q ^ (1 / 2 : ℝ) := by rw [hL₂def]; linarith only [hlogQ2, hsq1]
      calc M ≤ Q ^ (1 / 2 : ℝ) * L₂ := hMB
        _ ≤ Q ^ (1 / 2 : ℝ) * (4 * Q ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hL2le (by positivity)
        _ = 4 * Q := by
            rw [show Q ^ (1 / 2 : ℝ) * (4 * Q ^ (1 / 2 : ℝ))
              = 4 * (Q ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ)) by ring, hQsqsq]
    have hlnB : Real.log (Q ^ (1 / 2 : ℝ) * L₂) ≤ 3 / 2 * L₂ := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hQ0]
      have hL2log : Real.log L₂ ≤ L₂ := by
        have := Real.log_le_sub_one_of_pos hL₂pos; linarith only [this]
      have hlogQL2 : Real.log Q ≤ L₂ := by rw [hL₂def]; linarith only [hlogQ0]
      linarith only [hL2log, hlogQL2]
    have hLc : (1 : ℝ) ≤ L₂ / c₀ := by
      rw [le_div_iff₀ hc₀pos]; nlinarith only [hL₂ge2, hc₀le1]
    -- ZFR floors
    have hn1re : (1 - ρ).re = w := by rw [Complex.sub_re, Complex.one_re, ← hσdef, ← hwdef]
    have hn1 : w ≤ ‖1 - ρ‖ := by
      have h := Complex.abs_re_le_norm (1 - ρ)
      rw [hn1re, abs_of_pos hw0] at h; exact h
    have hnpos : 0 < ‖1 - ρ‖ := lt_of_lt_of_le hw0 hn1
    have hn2re : (2 - ρ).re = 2 - σ := by rw [Complex.sub_re, Complex.re_ofNat, ← hσdef]
    have hn2 : (1 : ℝ) ≤ ‖2 - ρ‖ := by
      have h := Complex.abs_re_le_norm (2 - ρ)
      rw [hn2re, abs_of_pos (by linarith only [hσ1'])] at h; linarith only [h, hσ1']
    have hwZFR : c₀ / Real.log Q ≤ w := by
      rw [hwdef, hσdef]; linarith only [hfloor]
    have hlogQL2' : Real.log Q ≤ L₂ := by rw [hL₂def]; linarith only [hlogQ0]
    have hinvw : 1 / w ≤ L₂ / c₀ := by
      have h2 : 1 / w ≤ Real.log Q / c₀ := by
        rw [div_le_div_iff₀ hw0 hc₀pos]
        have hwZFR' : c₀ ≤ w * Real.log Q := by
          rw [div_le_iff₀ hlogQpos] at hwZFR; linarith only [hwZFR]
        nlinarith only [hwZFR']
      have h3 : Real.log Q / c₀ ≤ L₂ / c₀ := by gcongr
      linarith only [h2, h3]
    have hn1inv : 1 / ‖1 - ρ‖ ≤ L₂ / c₀ :=
      le_trans (one_div_le_one_div_of_le hw0 hn1) hinvw
    have hsig : 1 / (1 - ρ.re) ≤ L₂ / c₀ := by
      rw [show 1 - ρ.re = w by rw [← hσdef, ← hwdef]]; exact hinvw
    have hCρ := C2Rho_le hσlo hσ1 himρ hZ0nn hc₀pos hLc hL₂1 hMB hMnn hB1 hn1inv hsig hnpos
    -- ===== 2 z^4 ≤ Y  and  ⌈1/(1-β₀)⌉ ≤ z =====
    have hexp4 : (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) ^ 4 = 16 * Q ^ (48 : ℝ) * u ^ (-(12 : ℝ)) := by
      rw [mul_pow, mul_pow, ← Real.rpow_natCast (Q ^ (12 : ℝ)) 4, ← Real.rpow_mul hQ0.le,
        ← Real.rpow_natCast (u ^ (-(3 : ℝ))) 4, ← Real.rpow_mul hu0.le]
      push_cast; ring_nf
    have hQ56ge : (32 : ℝ) ≤ Q ^ (56 : ℝ) * u ^ (-(2 : ℝ)) := by
      have hQ3 : (64 : ℝ) ≤ Q ^ (56 : ℝ) := by
        have h1 : (4 : ℝ) ^ (3 : ℝ) ≤ Q ^ (3 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hQ4 (by norm_num)
        have h2 : Q ^ (3 : ℝ) ≤ Q ^ (56 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
        rw [show (4 : ℝ) ^ (3 : ℝ) = 64 from by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num] at h1
        linarith only [h1, h2]
      have hu2 : (1 : ℝ) ≤ u ^ (-(2 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
      nlinarith only [hQ3, hu2, Real.rpow_pos_of_pos hQ0 (56 : ℝ)]
    have hfactor : Q ^ (104 : ℝ) * u ^ (-(14 : ℝ))
        = (Q ^ (56 : ℝ) * u ^ (-(2 : ℝ))) * (Q ^ (48 : ℝ) * u ^ (-(12 : ℝ))) := by
      rw [show (Q ^ (56 : ℝ) * u ^ (-(2 : ℝ))) * (Q ^ (48 : ℝ) * u ^ (-(12 : ℝ)))
          = (Q ^ (56 : ℝ) * Q ^ (48 : ℝ)) * (u ^ (-(2 : ℝ)) * u ^ (-(12 : ℝ))) by ring,
        ← Real.rpow_add hQ0, ← Real.rpow_add hu0]; norm_num
    have hY_nat : 2 * z ^ 4 ≤ Y := by
      have hzr4 : (z : ℝ) ^ 4 ≤ (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hzhi_r 4
      have hQ48pos : (0 : ℝ) ≤ Q ^ (48 : ℝ) * u ^ (-(12 : ℝ)) := by positivity
      have hchain : 2 * (z : ℝ) ^ 4 ≤ (Y : ℝ) := by
        calc 2 * (z : ℝ) ^ 4 ≤ 2 * (16 * Q ^ (48 : ℝ) * u ^ (-(12 : ℝ))) := by
              rw [← hexp4]; linarith only [hzr4]
          _ = 32 * (Q ^ (48 : ℝ) * u ^ (-(12 : ℝ))) := by ring
          _ ≤ (Q ^ (56 : ℝ) * u ^ (-(2 : ℝ))) * (Q ^ (48 : ℝ) * u ^ (-(12 : ℝ))) :=
              mul_le_mul_of_nonneg_right hQ56ge hQ48pos
          _ = Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := hfactor.symm
          _ ≤ (Y : ℝ) := hYlo_r
      have : (2 * z ^ 4 : ℕ) ≤ ((Y : ℕ) : ℝ) := by push_cast; linarith only [hchain]
      exact_mod_cast this
    have hcue : ⌈(1 : ℝ) / (1 - β₀)⌉₊ ≤ z := by
      have h1u : (1 : ℝ) / (1 - β₀) = 1 / u := by rw [huβ]
      have hceil : (⌈(1 : ℝ) / (1 - β₀)⌉₊ : ℝ) ≤ 1 / u + 1 := by
        rw [h1u]; exact (Nat.ceil_lt_add_one (by positivity)).le
      have h2u : 1 / u + 1 ≤ 2 * (1 / u) := by
        have : (1 : ℝ) ≤ 1 / u := by rw [le_div_iff₀ hu0]; linarith only [hu1]
        linarith only [this]
      have hu32 : u ^ (-(3 : ℝ)) * u = u ^ (-(2 : ℝ)) := by
        rw [show (-(3 : ℝ)) = -(2 : ℝ) + -(1 : ℝ) by norm_num, Real.rpow_add hu0]
        rw [show u ^ (-(2 : ℝ)) * u ^ (-(1 : ℝ)) * u
            = u ^ (-(2 : ℝ)) * (u ^ (-(1 : ℝ)) * u) by ring,
          show u ^ (-(1 : ℝ)) * u = 1 by rw [Real.rpow_neg_one, inv_mul_cancel₀ hu0.ne'], mul_one]
      have hu2ge : (2 : ℝ) ≤ Q ^ (12 : ℝ) * u ^ (-(2 : ℝ)) := by
        nlinarith only [hQ12ge4,
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (show -(2 : ℝ) ≤ 0 by norm_num),
          Real.rpow_pos_of_pos hQ0 (12 : ℝ)]
      have hzge : 2 * (1 / u) ≤ Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) := by
        rw [mul_one_div, div_le_iff₀ hu0, mul_assoc, hu32]; exact hu2ge
      have : (⌈(1 : ℝ) / (1 - β₀)⌉₊ : ℝ) ≤ (z : ℝ) := by
        linarith only [hceil, h2u, hzge, hzlo_r]
      exact_mod_cast this
    -- ===== guards + master =====
    have hGu : G = 34 + 12 * M + 12 * M * Z₀ + 36 * M / u := by rw [hGdef, huβ]
    have hNpos_r : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hscale := tbal_hscale hu0 hu1 huβ hMnn hMB hB1 hZ0nn hL₂1 hlnB hGu hNhi_npow hNpos_r
      huA huL2g hsqrtg
    have hguard := tbal_hguard hG34 hNlo_r hscale
    have hcov := tbal_hcov hZ0nn (le_of_lt hβ0lo) hβ0hi huβ hQ4 hM4Q hMnn hz2 hzlo_r hzhi_r hcue
      hZray
    have hmaster := dh_master_ray χ hχ hsq hq hβ0zero (le_of_lt hβ0lo) hβ0hi hρzero
      (by linarith only [hσlo] : 1 / 2 ≤ ρ.re) hσ1 himρ hord hZ hN4 hscale hguard hz2 hY_nat hcov
    rw [← hMdef] at hmaster
    -- ===== row hg's from the c-thresholds =====
    have hcollapse : ∀ X pinv p : ℝ, 0 ≤ X → 0 < p → c ≤ X ^ pinv → pinv * p = 1 → c ^ p ≤ X := by
      intro X pinv p hX hp hcX hpp
      calc c ^ p ≤ (X ^ pinv) ^ p := Real.rpow_le_rpow hcpos.le hcX hp.le
        _ = X ^ (pinv * p) := (Real.rpow_mul hX pinv p).symm
        _ = X := by rw [hpp, Real.rpow_one]
    have hgρ : 4 / c₀ * c ^ (3 / 17 : ℝ) ≤ 1 / 8 := by
      have hp : c ^ (3 / 17 : ℝ) ≤ c₀ / 32 :=
        hcollapse (c₀ / 32) (17 / 3) (3 / 17) (by positivity) (by norm_num) hc_t2 (by norm_num)
      have heq : 4 / c₀ * (c₀ / 32) = 1 / 8 := by field_simp; ring
      nlinarith only [mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 4 / c₀ by positivity), heq]
    have hg1A : 805 * c ^ (49 / 50 : ℝ) ≤ 1 := by
      have hp : c ^ (49 / 50 : ℝ) ≤ 1 / 805 :=
        hcollapse (1 / 805) (50 / 49) (49 / 50) (by norm_num) (by norm_num) hc_t3 (by norm_num)
      nlinarith only [mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 805 by norm_num)]
    have hg2A : 1610 * Real.exp 1 * c ^ (133 / 850 : ℝ) ≤ 1 / 8 := by
      have hp : c ^ (133 / 850 : ℝ) ≤ 1 / (8 * 1610 * Real.exp 1) :=
        hcollapse (1 / (8 * 1610 * Real.exp 1)) (850 / 133) (133 / 850) (by positivity)
          (by norm_num) hc_t4 (by norm_num)
      have hepos : 0 < Real.exp 1 := Real.exp_pos 1
      have heq : 1610 * Real.exp 1 * (1 / (8 * 1610 * Real.exp 1)) = 1 / 8 := by field_simp
      nlinarith only
        [mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 1610 * Real.exp 1 by positivity), heq]
    have hg1x : c ≤ 1 / 2 := hc_t5
    have hgEβ : 2 * (328 + 48 * Z₀) * 248 ^ 9 * c ^ (3547 / 1700 : ℝ) ≤ 1 / 8 := by
      have hp : c ^ (3547 / 1700 : ℝ) ≤ 1 / (16 * (328 + 48 * Z₀) * 248 ^ 9) :=
        hcollapse (1 / (16 * (328 + 48 * Z₀) * 248 ^ 9)) (1700 / 3547) (3547 / 1700)
          (by positivity) (by norm_num)
          hc_t6
          (by norm_num)
      have heq : 2 * (328 + 48 * Z₀) * 248 ^ 9 * (1 / (16 * (328 + 48 * Z₀) * 248 ^ 9))
          = 1 / 8 := by
        field_simp; ring
      nlinarith only [mul_le_mul_of_nonneg_left hp
        (show (0 : ℝ) ≤ 2 * (328 + 48 * Z₀) * 248 ^ 9 by positivity), heq]
    have hgEρ : 2 * (564 + 72 * Z₀) * 248 ^ 9 / c₀ * c ^ (5247 / 1700 : ℝ) ≤ 1 / 8 := by
      have hp : c ^ (5247 / 1700 : ℝ) ≤ c₀ / (16 * (564 + 72 * Z₀) * 248 ^ 9) :=
        hcollapse (c₀ / (16 * (564 + 72 * Z₀) * 248 ^ 9)) (1700 / 5247) (5247 / 1700)
          (by positivity) (by norm_num)
          hc_t7
          (by norm_num)
      have heq : 2 * (564 + 72 * Z₀) * 248 ^ 9 / c₀ * (c₀ / (16 * (564 + 72 * Z₀) * 248 ^ 9))
          = 1 / 8 := by
        field_simp; ring
      nlinarith only [mul_le_mul_of_nonneg_left hp
        (show (0 : ℝ) ≤ 2 * (564 + 72 * Z₀) * 248 ^ 9 / c₀ by positivity), heq]
    -- ===== derived shapes + row caps =====
    have hlogL2 : Real.log Q + 2 ≤ L₂ := le_of_eq hL₂def.symm
    have hMB' : M ≤ Real.sqrt Q * L₂ := by rw [Real.sqrt_eq_rpow]; exact hMB
    have hYpos : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (show 0 < Y by omega)
    have hz1r : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show 1 ≤ z by omega)
    have hrow1 : (1 - β₀) * (2 - β₀) * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖) ≤ 1 / 8 :=
      row_rho_main_cap (Q := Q) (L₂ := L₂) (c := c) (c₀ := c₀) (u := 1 - β₀) (w := 1 - ρ.re)
        (σ := ρ.re) (β₀ := β₀) (Y := Y) (n1 := ‖1 - ρ‖) (n2 := ‖2 - ρ‖)
        hQ4 hL₂1 hcpos hc1 hc₀pos hu0 rfl hσlo hσ1 hβ0 hβ0hi hn2 hn1inv hYlo_r hYhi_r huτ hgρ
    have hσ0 : 0 < ρ.re := by linarith only [hσlo]
    have hCρnn : 0 ≤ C2Rho q Z₀ ρ := by
      rw [C2Rho, CwRho]
      have h1 : (0 : ℝ) ≤ ‖ρ‖ / ρ.re := div_nonneg (norm_nonneg _) hσ0.le
      positivity
    have hrow2 : C2Rho q Z₀ ρ * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9
        * (Y : ℝ) ^ (1 / 2 - ρ.re) ≤ 1 / 8 :=
      row_Eρ_cap (Q := Q) (L₂ := L₂) (c := c) (c₀ := c₀) (u := 1 - β₀) (w := 1 - ρ.re) (σ := ρ.re)
        (Y := Y) (z := (z : ℝ)) (Cρ := C2Rho q Z₀ ρ) (Z₀ := Z₀) hQ4 hlogL2 hcpos hc1 hc₀pos hu0 hu1
        rfl hσlo hσ1 hCρnn hCρ hZ0nn hz1r hzhi_r hYlo_r huτ hgEρ
    have hrowA : (Y : ℝ) ^ (β₀ - ρ.re) * ((Y : ℝ) ^ (1 - β₀) - 1) ≤ 1 / 8 :=
      row_A_cap (Q := Q) (L₂ := L₂) (c := c) (u := 1 - β₀) (w := 1 - ρ.re) (σ := ρ.re) (β₀ := β₀)
        (Y := Y) hQ4 hlogL2 hcpos hc1 hu0 hu1 rfl hσlo hσ1 hσβ hβ0hi rfl hYlo_r hYhi_r huτ hg1A hg2A
    have hrow1x : (Y : ℝ) ^ (β₀ - ρ.re - 1) ≤ 1 / 8 :=
      row_1x_cap (Q := Q) (L₂ := L₂) (c := c) (u := 1 - β₀) (w := 1 - ρ.re) (σ := ρ.re) (β₀ := β₀)
        (Y := Y) hQ4 hL₂1 hcpos hg1x hu0 rfl hσlo hσ1 hσβ hβ0hi hYlo_r huτ
    have hrowEβ : (Y : ℝ) ^ (β₀ - ρ.re) * ((136 + 48 * M + 48 * M * Z₀ + 144 * M / (1 - β₀))
        * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀)) ≤ 1 / 8 :=
      row_Eβ_cap (Q := Q) (L₂ := L₂) (c := c) (u := 1 - β₀) (w := 1 - ρ.re) (σ := ρ.re) (β₀ := β₀)
        (Y := Y) (z := (z : ℝ)) (M := M) (Z₀ := Z₀) hQ4 hlogL2 hcpos hc1 hu0 hu1 rfl hσlo hσ1 hσβ
        hβ0hi rfl hMnn hMB' hZ0nn hz1r hzhi_r hYlo_r hYhi_r huτ hgEβ
    -- ===== ROW3 decomposition + contradiction =====
    have hYdiv : (Y : ℝ) ^ (β₀ - ρ.re) / (Y : ℝ) = (Y : ℝ) ^ (β₀ - ρ.re - 1) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one (Y : ℝ), ← Real.rpow_add hYpos,
        show β₀ - ρ.re + -1 = β₀ - ρ.re - 1 by ring]
    have hROW3 : (Y : ℝ) ^ (β₀ - ρ.re) * (((Y : ℝ) ^ (1 - β₀)
          + (136 + 48 * M + 48 * M * Z₀ + 144 * M / (1 - β₀))
            * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀))
          - (1 - 1 / (Y : ℝ)))
        = (Y : ℝ) ^ (β₀ - ρ.re) * ((Y : ℝ) ^ (1 - β₀) - 1)
          + (Y : ℝ) ^ (β₀ - ρ.re) * ((136 + 48 * M + 48 * M * Z₀ + 144 * M / (1 - β₀))
            * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀))
          + (Y : ℝ) ^ (β₀ - ρ.re - 1) := by rw [← hYdiv]; ring
    have hYbig : (1 : ℝ) / (Y : ℝ) ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le (by norm_num)
      calc (4 : ℝ) ≤ Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by nlinarith only [hQ104ge4, hu14ge1]
        _ ≤ (Y : ℝ) := hYlo_r
    rw [hROW3] at hmaster
    linarith only [hmaster, hrow1, hrow2, hrowA, hrowEβ, hrow1x, hYbig]

theorem dh_repulsion_ordered : ∃ b c k : ℝ, 0 < b ∧ 0 < c ∧ 0 ≤ k ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → 2 ≤ q →
      ∀ β₀ : ℝ, DirichletCharacter.LFunction χ (β₀ : ℂ) = 0 → 1 / 2 < β₀ → β₀ < 1 →
      ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.im ≠ 0 → |ρ.im| ≤ 1 →
        16 / 17 ≤ ρ.re → ρ.re < 1 → ρ.re ≤ β₀ →
        (1 - β₀) ≥ c * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(b * (1 - ρ.re)))
          / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ k := by
  obtain ⟨c₀', hc₀'pos, hZFR⟩ := zero_free_region_all
  obtain ⟨Z₀, hZ⟩ := zetaHol_bound
  set c₀ : ℝ := min c₀' 1 with hc₀def
  have hc₀pos : 0 < c₀ := lt_min hc₀'pos one_pos
  have hc₀le1 : c₀ ≤ 1 := min_le_right _ _
  have hc₀lec₀' : c₀ ≤ c₀' := min_le_left _ _
  have hZ0nn : 0 ≤ Z₀ := le_trans (norm_nonneg _)
    (hZ (1 / 2) (by norm_num) (by norm_num) (by norm_num))
  set KEβ : ℝ := 16 * (328 + 48 * Z₀) * 248 ^ 9 with hKEβdef
  set KEρ : ℝ := 16 * (564 + 72 * Z₀) * 248 ^ 9 with hKEρdef
  set A₀ : ℝ := Real.log 2 + 4 * Real.log (256 * (82 + 12 * Z₀)) with hA₀def
  have hA₀pos : 0 < A₀ := by
    rw [hA₀def]
    have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : 0 ≤ Real.log (256 * (82 + 12 * Z₀)) := Real.log_nonneg (by nlinarith only [hZ0nn])
    linarith only [h1, h2]
  -- **THE ARM TABLE** (`log(1/arm)`; the BINDING arm is the largest).  Arms 6, 7, 8, 11 carry the
  -- FREE variable `Z₀`, so this tower cannot be priced numerically; the figures below are that
  -- pricing **evaluated at `Z₀ ⇝ 5`**, purely for comparison with the tall twin (`TBalTall:2105`),
  -- whose `Eρ` arm is genuinely `Z₀`-free.  REALISED post-TAU-SHARP TS-1 (S1: arm 1
  -- `2^{−250} ⇝ 1/40`; S5(a): `627 ⇝ 248` inside `KEβ`/`KEρ`; S6 is TALL-ONLY — `C2Rho_le` here is
  -- tight already) **and TS-2** (S2: arms 4/6/7 carry each row's own γ-floor in place of the
  -- uniform `1/8`, so the exponent `8 ⇝ 1/γ₀`):
  --                                after TS-1     **after TS-2 (REALISED)**
  --   1. `1/40`                        3.6889          3.6889
  --   2. `(c₀/32)^{17/3}`             86.2267         86.2267  ← **BINDING**
  --   3. `(1/805)^{50/49}`             6.8274          6.8274
  --   4. `(1/(8·1610·e))^{850/133}`   83.7074         66.8716   (γ_A = 133/850)
  --   5. `1/2`                         0.6931          0.6931
  --   6. `(1/KEβ)^{1700/3547}`       469.8846         28.1507   (γ_Eβ = 3547/1700)
  --   7. `(c₀/KEρ)^{1700/5247}`      567.7832 ←BIND   22.9948   (γ_Eρ = 5247/1700)
  --   8. `1/(3A₀)`                     4.8527          4.8527
  --   9. `1/18`                        2.8904          2.8904
  --  10. `1/576`                       6.3561          6.3561
  --  11. `1/(Z₀+1)`                    1.7918          1.7918
  -- `log(1/c)` = the MAX = **86.2267** at `Z₀ ⇝ 5` (was 567.7832 after TS-1, 634.5645 landed).
  -- The binding arm moves from 7 to 2: `(c₀/32)^{17/3}`, which is the ρ-main row and is NOT a
  -- γ-collapse — retiring it is TS-3's, not this wave's.  The `1/40` arm stays inert (dominated by
  -- arm 10, `log 576 = 6.3561`).  Every projection index below is hand-built and depth-sensitive,
  -- so keep this tower ELEVEN deep and replace numerals in place — never delete an arm.
  set c : ℝ := min (1 / 40 : ℝ) (min ((c₀ / 32) ^ (17 / 3 : ℝ))
    (min ((1 / 805 : ℝ) ^ (50 / 49 : ℝ)) (min ((1 / (8 * 1610 * Real.exp 1)) ^ (850 / 133 : ℝ))
    (min (1 / 2 : ℝ) (min ((1 / KEβ) ^ (1700 / 3547 : ℝ)) (min ((c₀ / KEρ) ^ (1700 / 5247 : ℝ))
    (min (1 / (3 * A₀)) (min (1 / 18 : ℝ) (min (1 / 576 : ℝ) (1 / (Z₀ + 1))))))))))) with hcdef
  have hp1 : (0 : ℝ) < 1 / 40 := by norm_num
  have hp2 : (0 : ℝ) < (c₀ / 32) ^ (17 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (div_pos hc₀pos (by norm_num)) _
  have hp3 : (0 : ℝ) < (1 / 805 : ℝ) ^ (50 / 49 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hp4 : (0 : ℝ) < (1 / (8 * 1610 * Real.exp 1)) ^ (850 / 133 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hp6 : (0 : ℝ) < (1 / KEβ) ^ (1700 / 3547 : ℝ) :=
    Real.rpow_pos_of_pos (by rw [hKEβdef]; positivity) _
  have hp7 : (0 : ℝ) < (c₀ / KEρ) ^ (1700 / 5247 : ℝ) :=
    Real.rpow_pos_of_pos (div_pos hc₀pos (by rw [hKEρdef]; positivity)) _
  have hp8 : (0 : ℝ) < 1 / (3 * A₀) := div_pos one_pos (by linarith only [hA₀pos])
  have hp11 : (0 : ℝ) < 1 / (Z₀ + 1) := div_pos one_pos (by linarith only [hZ0nn])
  have hcpos : 0 < c := by
    rw [hcdef]
    exact lt_min hp1 (lt_min hp2 (lt_min hp3 (lt_min hp4 (lt_min (by norm_num) (lt_min hp6
      (lt_min hp7 (lt_min hp8 (lt_min (by norm_num) (lt_min (by norm_num) hp11)))))))))
  have hc_t1 : c ≤ 1 / 40 := by rw [hcdef]; exact min_le_left _ _
  have hc_t2 : c ≤ (c₀ / 32) ^ (17 / 3 : ℝ) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hc_t3 : c ≤ (1 / 805 : ℝ) ^ (50 / 49 : ℝ) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc_t4 : c ≤ (1 / (8 * 1610 * Real.exp 1)) ^ (850 / 133 : ℝ) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hc_t5 : c ≤ (1 / 2 : ℝ) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hc_t6 : c ≤ (1 / KEβ) ^ (1700 / 3547 : ℝ) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hc_t7 : c ≤ (c₀ / KEρ) ^ (1700 / 5247 : ℝ) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))))))
  have hc_t8 : c ≤ 1 / (3 * A₀) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))))
  have hc_t9 : c ≤ 1 / 18 := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _))))))))
  have hc_t10 : c ≤ 1 / 576 := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _)))))))))
  have hc_t11 : c ≤ 1 / (Z₀ + 1) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_right _ _)))))))))
  have hc1 : c ≤ 1 := le_trans hc_t5 (by norm_num)
  clear_value c c₀
  refine ⟨680, c, 14, by norm_num, hcpos, by norm_num, ?_⟩
  intro q _instNe χ hχ hχ1 hsq hq β₀ hβ0zero hβ0lo hβ0hi ρ hρzero hρim himρ hσlo hσ1 hord
  have hfloor : ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
    have h := hZFR q χ hχ hχ1 hρzero (by linarith only [hσlo] : 1 / 2 ≤ ρ.re) (Or.inr hρim)
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hlogpos : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) :=
      Real.log_pos (by nlinarith only [hqR, abs_nonneg ρ.im])
    have hdiv : c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2))
        ≤ c₀' / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by gcongr
    linarith only [h, hdiv]
  exact dh_repulsion_inst χ hχ hχ1 hsq hq hβ0zero hβ0lo hβ0hi hρzero hρim himρ hσlo hσ1 hord hZ
    hc₀pos hc₀le1 hZ0nn hfloor hcpos hc1 hc_t1 hc_t2 hc_t3 hc_t4 hc_t5 hc_t6 hc_t7 hc_t8 hc_t9
    hc_t10 hc_t11

end Salt.SW

end
