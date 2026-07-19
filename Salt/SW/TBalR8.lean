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

  `1 − β₀ ≥ c·(q(|Im ρ|+2))^{−b(1−Re ρ)}/(log(q(|Im ρ|+2))+2)^k`,   `b=680, c=2^{−250}, k=14`.

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

/-- **Trivial-branch bound.** The contract RHS `τ = c·Q^{−680w}/L₂^{14}` (`c = 2^{−250}`,
`L₂ = log Q + 2`) is `≤ 1/(40 L₂)` for any `Q ≥ 1`, `w > 0`.  Hence in the trivial branch
`1/(40 L₂) ≤ u` the target `u ≥ τ` is immediate.  Pure `rpow` arithmetic: `Q^{−680w} ≤ 1`,
`40·2^{−250} < 8192 ≤ L₂^{13}`, `L₂^{14} = L₂^{13}·L₂`. -/
lemma tbal_tau_le_split {Q w : ℝ} (hQ : 1 ≤ Q) (hw : 0 < w) :
    (2 : ℝ) ^ (-(250 : ℝ)) * Q ^ (-(680 * w)) / (Real.log Q + 2) ^ (14 : ℝ)
      ≤ 1 / (40 * (Real.log Q + 2)) := by
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hL2 : (2 : ℝ) ≤ Real.log Q + 2 := by linarith
  have hLpos : (0 : ℝ) < Real.log Q + 2 := by linarith
  have hcpos : (0 : ℝ) < (2 : ℝ) ^ (-(250 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hclt1 : (2 : ℝ) ^ (-(250 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
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
  have hstep : (2 : ℝ) ^ (-(250 : ℝ)) * Q ^ (-(680 * w)) * (40 * (Real.log Q + 2))
      ≤ 8192 * (Real.log Q + 2) := by
    have h1 : (2 : ℝ) ^ (-(250 : ℝ)) * Q ^ (-(680 * w)) ≤ 1 := by
      calc (2 : ℝ) ^ (-(250 : ℝ)) * Q ^ (-(680 * w))
          ≤ 1 * 1 := mul_le_mul hclt1 hQpow hQpownn (by norm_num)
        _ = 1 := by norm_num
    nlinarith [mul_nonneg hcpos.le hQpownn, hLpos]
  calc (2 : ℝ) ^ (-(250 : ℝ)) * Q ^ (-(680 * w)) * (40 * (Real.log Q + 2))
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
    (hg2 : 1610 * Real.exp 1 * c ^ (1 / 8 : ℝ) ≤ 1 / 8) :
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
    have hγ8 : c ^ (49 / 50 - 14 * (β₀ - σ)) ≤ c ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hcc hc1 (by rw [hp]; nlinarith [hw0, hu0])
    have h2p : (2 : ℝ) ^ (β₀ - σ) ≤ 2 := by
      calc (2 : ℝ) ^ (β₀ - σ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hp]; linarith)
        _ = 2 := Real.rpow_one 2
    -- assemble
    have hEnn : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    have hchain : Y ^ (β₀ - σ) * (Real.exp 1 * (u * Real.log Y))
        ≤ 1610 * Real.exp 1 * c ^ (1 / 8 : ℝ) := by
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
          ≤ c ^ (1 / 8 : ℝ) := le_trans hmono' hγ8
      have hinner : 2 ^ (β₀ - σ)
            * (Q ^ (104 * (β₀ - σ)) * u ^ (49 / 50 - 14 * (β₀ - σ)) * L₂)
          ≤ 2 * c ^ (1 / 8 : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_right h2p hBnn) (mul_le_mul_of_nonneg_left hB (by norm_num))
      calc 805 * Real.exp 1 * 2 ^ (β₀ - σ)
            * (Q ^ (104 * (β₀ - σ)) * u ^ (49 / 50 - 14 * (β₀ - σ)) * L₂)
          = (805 * Real.exp 1) * (2 ^ (β₀ - σ)
              * (Q ^ (104 * (β₀ - σ)) * u ^ (49 / 50 - 14 * (β₀ - σ)) * L₂)) := by ring
        _ ≤ (805 * Real.exp 1) * (2 * c ^ (1 / 8 : ℝ)) := mul_le_mul_of_nonneg_left hinner hA
        _ = 1610 * Real.exp 1 * c ^ (1 / 8 : ℝ) := by ring
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

/-- **The polylog factor bound.**  `1 + log(z²) ≤ 627·u^{−1/100}·L₂` at the crush scale
`z ≤ 2Q^{12}u^{−3}`.  `log z ≤ log 2 + 12 log Q − 3 log u`, then `−log u ≤ 100·u^{−1/100}`
(`neg_log_le_rpow`) and `log Q ≤ L₂` fold every term into the single `u^{−1/100}·L₂` shape. -/
lemma logz_factor_le {Q L₂ z u : ℝ} (hQ4 : 4 ≤ Q) (hL2 : Real.log Q + 2 ≤ L₂)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hzpos : 0 < z)
    (hzhi : z ≤ 2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) :
    1 + Real.log (z ^ 2) ≤ 627 * u ^ (-(1 / 100 : ℝ)) * L₂ := by
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
  have hnlogu : -Real.log u ≤ u ^ (-(1 / 100 : ℝ)) / (1 / 100) := neg_log_le_rpow hu0 (by norm_num)
  rw [hlogz2]
  have e1 : (1 : ℝ) ≤ u ^ (-(1 / 100 : ℝ)) * L₂ := by nlinarith [hu100, hL2']
  have e2 : 24 * Real.log Q ≤ 24 * (u ^ (-(1 / 100 : ℝ)) * L₂) := by
    have hlogQL : Real.log Q ≤ L₂ := by linarith
    nlinarith [hu100, hlogQL, hlogQ0]
  have e3 : -6 * Real.log u ≤ 600 * u ^ (-(1 / 100 : ℝ)) := by nlinarith [hnlogu]
  have e4 : 600 * u ^ (-(1 / 100 : ℝ)) ≤ 600 * (u ^ (-(1 / 100 : ℝ)) * L₂) := by
    nlinarith [hL2', Real.rpow_nonneg hu0.le (-(1 / 100 : ℝ))]
  nlinarith [hlogz, hlog2, e1, e2, e3, e4]

end Salt.SW

end
