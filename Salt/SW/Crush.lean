/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHExtractW
import Salt.SW.EulerLink
import Salt.SW.Hyperbola

/-!
# T-BAL R5 — THE CRUSH WAVE (`H_lower` via the crush mechanism)

The retune's R5: a LOWER bound `H(z) ≥ L₁/(u·(2−β₀))` for the Selberg mean `H(z) = selHSum χ z`,
built by the **crush mechanism** rather than the dead primorial-Rankin route (flags R5-FINISH; do
NOT resurrect `δ_b`). The crush is the chain

  `H(z) = selHSum χ z  ≥  Σ_{n≤z} dhA(n)/n  ≥  z^{−u}·A(z)  ≥  z^{−u}(L₁z^{1−β₀}/u − err)`

with `A(z) = Σ_{n≤z} dhA χ n · n^{−β₀}`, `u = 1−β₀`. The first step is `selHSum ≥ Σ_{n≤z}dhA/n`
(the radical-support superset, R5c); the second is the per-term crush `n^{−1} ≥ z^{−u}n^{−β₀}` on
`n ≤ z` (R5d); the third is the two-sided lower Abel bound (R5e). The `z^{−u}·z^{1−β₀} = 1`
collapse delivers `L₁/u`, which beats the target `L₁/(u(2−β₀))` by the `(2−β₀)` gap, absorbing the
crush error under the coverage condition (R5f). Verified 0/2 by two refuter panels (the W=14
retune; audit scripts `scripts/tbal_ledgers/refuter1_*.py`).

Rungs: R5b `selG_ge_partial_geom`, R5c `selHSum_ge_dhA_div_sum`, R5d `crush_pointwise`,
R5e `dhAbel_inner_ge`, R5f `R5_crush_wing`, R5h `H_lower`; grafts G1 `selHSum_le_primorial`,
G2 `selHSum_ge_one`.
-/

namespace Salt.SW

open Finset

variable {q : ℕ} [NeZero q]

/-! ## Grafts — cheap permanent stones -/

omit [NeZero q] in
/-- **G2 (`selHSum_ge_one`).** `H(z) ≥ 1` for `z ≥ 1`: the `r = 1` term is `g(1) = 1` (empty
product) and every other term is `≥ 0` (`selGmul_pos`). -/
lemma selHSum_ge_one (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 1 ≤ z) :
    1 ≤ selHSum χ z := by
  rw [selHSum]
  have hg1 : selGmul χ 1 = 1 := by rw [selGmul, Nat.primeFactors_one, Finset.prod_empty]
  have h1mem : (1 : ℕ) ∈ (Finset.Icc 1 z).filter Squarefree := by
    rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨le_refl 1, hz⟩, squarefree_one⟩
  calc (1 : ℝ) = selGmul χ 1 := hg1.symm
    _ ≤ ∑ r ∈ (Finset.Icc 1 z).filter Squarefree, selGmul χ r :=
        Finset.single_le_sum (fun r _ => (selGmul_pos χ hsq r).le) h1mem

omit [NeZero q] in
/-- **G1 (`selHSum_le_primorial`).** `H(z) ≤ P(z) = selHFull χ z`: the `r ≤ z` truncation is
dominated by the full `z`-smooth product (add back the nonnegative `z`-smooth tail). -/
lemma selHSum_le_primorial (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ) :
    selHSum χ z ≤ selHFull χ z := by
  rw [selHSum_eq_primorial_le χ z, selHFull]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun a _ _ => (selGmul_pos χ hsq a).le)

/-! ## R5b — the per-prime geometric floor -/

omit [NeZero q] in
/-- **R5b (`selG_ge_partial_geom`).** The per-prime geometric floor: for `p ≥ 2` and any cutoff
`K`, the truncated local Euler factor is dominated by `g(p)`,
`Σ_{e=1}^{K} dhA(p^e)·p^{−e} ≤ selG χ p`. Route: with `x = 1/p`, `c = χ_ℝ(p)`, `a_e = dhA(p^e) =
Σ_{j≤e} c^j` obeys `a_{e+1} = 1 + c·a_e`, whence the exact truncation identity
`(1−x)(1−cx)·Σ_{e≤K} a_e x^e = 1 − x^{K+1}(a_{K+1} − c·a_K·x)` (induction), and the bracket
`a_{K+1} − c·a_K·x ≥ 0`, so the partial sum `≤ 1/((1−x)(1−cx)) = 1 + selG χ p`
(`one_add_selG_eq_local_inv`); subtract the `e=0` term `a_0 = 1`. -/
lemma selG_ge_partial_geom (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (K : ℕ) :
    ∑ e ∈ Finset.Icc 1 K, dhA χ (p ^ e) * (p : ℝ) ^ (-(e : ℝ)) ≤ selG χ p := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  set x : ℝ := (p : ℝ)⁻¹ with hxdef
  set c : ℝ := chiRe χ p with hcdef
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hxle : x ≤ 1 / 2 := by
    rw [hxdef, ← one_div]; exact one_div_le_one_div_of_le (by norm_num) hpR
  have hc1 : |c| ≤ 1 := by rw [hcdef]; exact chiRe_abs_le_one χ p
  have hcabs : -1 ≤ c ∧ c ≤ 1 := abs_le.mp hc1
  have h1x : 0 < 1 - x := by linarith
  have h1cx : 0 < 1 - c * x := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 - c by linarith [hcabs.2]) hx0.le, hxle]
  set a : ℕ → ℝ := fun e => dhA χ (p ^ e) with hadef
  have ha0 : a 0 = 1 := by simp only [hadef]; rw [pow_zero, dhA_one]
  have hanneg : ∀ e, 0 ≤ a e := fun e => by
    simp only [hadef]; exact dhA_nonneg χ hsq (pow_ne_zero e hp.pos.ne')
  -- the geometric closed form and the recurrence `a (e+1) = 1 + c · a e`
  have haval : ∀ e, a e = ∑ j ∈ Finset.range (e + 1), c ^ j := fun e => by
    simp only [hadef, hcdef]; exact dhA_prime_pow χ hsq hp e
  have hrec : ∀ e, a (e + 1) = 1 + c * a e := fun e => by
    rw [haval (e + 1), haval e, Finset.sum_range_succ' (fun j => c ^ j) (e + 1), pow_zero,
      add_comm, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [pow_succ, mul_comm])
  -- powers: `p^{−e} = x^e`
  have hxpow : ∀ e : ℕ, (p : ℝ) ^ (-(e : ℝ)) = x ^ e := fun e => by
    rw [hxdef, inv_pow, Real.rpow_neg hp0.le, Real.rpow_natCast]
  -- the exact truncation identity
  have hid : ∀ K, (1 - x) * (1 - c * x) * (∑ e ∈ Finset.range (K + 1), a e * x ^ e)
      = 1 - x ^ (K + 1) * (a (K + 1) - c * a K * x) := by
    intro K
    induction K with
    | zero =>
      rw [Finset.sum_range_one, pow_zero, mul_one, ha0, hrec 0, ha0]; ring
    | succ K ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have hr1 := hrec (K + 1)
      have hr2 := hrec K
      have hpow : x ^ (K + 1 + 1) = x ^ (K + 1) * x := by rw [pow_succ]
      rw [hpow, hr1, hr2]; ring
  -- bracket nonnegativity: `a (K+1) − c · a K · x = (1−x)(1 + c a_K) + x ≥ 0`
  have h1 : 0 ≤ 1 + c * a K := by have := hanneg (K + 1); rwa [hrec K] at this
  have hbrack : 0 ≤ a (K + 1) - c * a K * x := by
    rw [hrec K]; nlinarith [mul_nonneg h1x.le h1, hx0.le]
  -- the partial sum `≤ 1/((1−x)(1−cx))`
  have hden : 0 < (1 - x) * (1 - c * x) := mul_pos h1x h1cx
  have hpartial : ∑ e ∈ Finset.range (K + 1), a e * x ^ e ≤ 1 / ((1 - x) * (1 - c * x)) := by
    rw [le_div_iff₀ hden]
    have hnn : 0 ≤ x ^ (K + 1) * (a (K + 1) - c * a K * x) :=
      mul_nonneg (pow_nonneg hx0.le _) hbrack
    nlinarith [hid K, hnn]
  -- convert to `1 + selG` and peel the `e=0` term
  have hden_eq : (1 - x) * (1 - c * x)
      = (1 - 1 / (p : ℝ)) * (1 - chiRe χ p / (p : ℝ)) := by rw [hxdef, hcdef]; ring
  have hlocal : 1 + selG χ p = 1 / ((1 - x) * (1 - c * x)) := by
    rw [hden_eq]; exact one_add_selG_eq_local_inv χ hsq hp.two_le
  have hsplit : ∑ e ∈ Finset.range (K + 1), a e * x ^ e
      = 1 + ∑ e ∈ Finset.Icc 1 K, a e * x ^ e := by
    have hIcc : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
      ext e; simp [Finset.mem_Icc, Finset.mem_Ico]
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    rw [Finset.sum_range_succ' (fun e => a e * x ^ e) K, pow_zero, ha0, mul_one, add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm 1 i])
  have hconv : ∑ e ∈ Finset.Icc 1 K, dhA χ (p ^ e) * (p : ℝ) ^ (-(e : ℝ))
      = ∑ e ∈ Finset.Icc 1 K, a e * x ^ e := by
    refine Finset.sum_congr rfl (fun e _ => ?_)
    change dhA χ (p ^ e) * (p : ℝ) ^ (-(e : ℝ)) = dhA χ (p ^ e) * x ^ e
    rw [hxpow]
  rw [hconv]
  have hpk := hpartial
  rw [hsplit, ← hlocal] at hpk
  linarith

/-! ## R5d — the per-term crush -/

/-- **R5d (`crush_pointwise`).** For `1 ≤ n ≤ z` and `β₀ < 1`, `z^{−(1−β₀)}·n^{−β₀} ≤ n^{−1}`.
Since `n^{−1} = n^{−β₀}·n^{−(1−β₀)}` and `z^{−(1−β₀)} ≤ n^{−(1−β₀)}` (a nonpositive exponent on
`n ≤ z`), the claim is one `Real.rpow_le_rpow_of_nonpos`. This is the crush's engine: it trades the
size cut `n ≤ z` for the zero-shift factor `z^{−u}`. -/
lemma crush_pointwise {β₀ : ℝ} (hβ1 : β₀ < 1) {n z : ℕ} (hn : 1 ≤ n) (hnz : n ≤ z) :
    (z : ℝ) ^ (-(1 - β₀)) * (n : ℝ) ^ (-β₀) ≤ (n : ℝ) ^ (-(1 : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnzR : (n : ℝ) ≤ (z : ℝ) := by exact_mod_cast hnz
  have hbase : (z : ℝ) ^ (-(1 - β₀)) ≤ (n : ℝ) ^ (-(1 - β₀)) :=
    Real.rpow_le_rpow_of_nonpos hn0 hnzR (by linarith)
  calc (z : ℝ) ^ (-(1 - β₀)) * (n : ℝ) ^ (-β₀)
      ≤ (n : ℝ) ^ (-(1 - β₀)) * (n : ℝ) ^ (-β₀) :=
        mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hn0.le _)
    _ = (n : ℝ) ^ (-(1 : ℝ)) := by
        rw [← Real.rpow_add hn0]; congr 1; ring

/-! ## The crush composition — `H_lower` given the three inputs -/

/-- **The crush composition (the R5h glue).** Given the three crush inputs — the radical-superset
bound (R5c, `hsum`: `Σ_{n≤z} dhA(n)/n ≤ H(z)`), the two-sided lower Abel bound (R5e, `habel`:
`L₁·z^{1−β₀}/(1−β₀) − E ≤ A(z)` with `A(z) = Σ_{n≤z} dhA(n)·n^{−β₀}`), and the coverage condition
(R5f, `hcov`: `z^{−(1−β₀)}·E ≤ L₁/(2−β₀)`) — the Selberg mean clears the freeze target
`L₁/((1−β₀)(2−β₀)) ≤ H(z)`. Pure algebra: the per-term crush `n^{−1} ≥ z^{−u}n^{−β₀}`
(`crush_pointwise`) times `dhA ≥ 0` gives `z^{−u}·A(z) ≤ Σ dhA/n ≤ H(z)`; the collapse
`z^{−u}·z^{1−β₀} = 1` turns `z^{−u}(L₁z^{1−β₀}/u − E)` into `L₁/u − z^{−u}E`, and
`L₁/u − L₁/(2−β₀) = L₁/(u(2−β₀))` (since `(2−β₀)−(1−β₀)=1`). -/
theorem H_lower_of_parts (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {β₀ : ℝ} {z : ℕ} {E : ℝ}
    (hz : 1 ≤ z) (hβlo : 0 < β₀) (hβhi : β₀ < 1)
    (hsum : ∑ n ∈ Finset.Icc 1 z, dhA χ n * (n : ℝ) ^ (-(1 : ℝ)) ≤ selHSum χ z)
    (habel : (DirichletCharacter.LFunction χ 1).re * (z : ℝ) ^ (1 - β₀) / (1 - β₀) - E
        ≤ ∑ n ∈ Finset.Icc 1 z, dhA χ n * (n : ℝ) ^ (-β₀))
    (hcov : (z : ℝ) ^ (-(1 - β₀)) * E ≤ (DirichletCharacter.LFunction χ 1).re / (2 - β₀)) :
    (DirichletCharacter.LFunction χ 1).re / ((1 - β₀) * (2 - β₀)) ≤ selHSum χ z := by
  set L₁ : ℝ := (DirichletCharacter.LFunction χ 1).re with hL1
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have hzu : (0 : ℝ) ≤ (z : ℝ) ^ (-(1 - β₀)) := Real.rpow_nonneg hzR.le _
  have hne1 : (1 - β₀) ≠ 0 := by linarith
  have hne2 : (2 - β₀) ≠ 0 := by linarith
  -- the crush: `z^{−u}·A(z) ≤ Σ dhA/n`
  have hcrush : (z : ℝ) ^ (-(1 - β₀)) * (∑ n ∈ Finset.Icc 1 z, dhA χ n * (n : ℝ) ^ (-β₀))
      ≤ ∑ n ∈ Finset.Icc 1 z, dhA χ n * (n : ℝ) ^ (-(1 : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun n hn => ?_)
    rw [Finset.mem_Icc] at hn
    have hdhA : 0 ≤ dhA χ n := dhA_nonneg χ hsq (by omega)
    have hcp := crush_pointwise hβhi hn.1 hn.2
    calc (z : ℝ) ^ (-(1 - β₀)) * (dhA χ n * (n : ℝ) ^ (-β₀))
        = dhA χ n * ((z : ℝ) ^ (-(1 - β₀)) * (n : ℝ) ^ (-β₀)) := by ring
      _ ≤ dhA χ n * (n : ℝ) ^ (-(1 : ℝ)) := mul_le_mul_of_nonneg_left hcp hdhA
  have hchain1 : (z : ℝ) ^ (-(1 - β₀)) * (∑ n ∈ Finset.Icc 1 z, dhA χ n * (n : ℝ) ^ (-β₀))
      ≤ selHSum χ z := le_trans hcrush hsum
  have hmul : (z : ℝ) ^ (-(1 - β₀)) * (L₁ * (z : ℝ) ^ (1 - β₀) / (1 - β₀) - E)
      ≤ (z : ℝ) ^ (-(1 - β₀)) * (∑ n ∈ Finset.Icc 1 z, dhA χ n * (n : ℝ) ^ (-β₀)) :=
    mul_le_mul_of_nonneg_left habel hzu
  have hZW : (z : ℝ) ^ (-(1 - β₀)) * (z : ℝ) ^ (1 - β₀) = 1 := by
    rw [← Real.rpow_add hzR]; simp
  have hexpand : (z : ℝ) ^ (-(1 - β₀)) * (L₁ * (z : ℝ) ^ (1 - β₀) / (1 - β₀) - E)
      = L₁ / (1 - β₀) - (z : ℝ) ^ (-(1 - β₀)) * E := by
    have hstep : (z : ℝ) ^ (-(1 - β₀)) * (L₁ * (z : ℝ) ^ (1 - β₀) / (1 - β₀) - E)
        = L₁ * ((z : ℝ) ^ (-(1 - β₀)) * (z : ℝ) ^ (1 - β₀)) / (1 - β₀)
          - (z : ℝ) ^ (-(1 - β₀)) * E := by ring
    rw [hstep, hZW, mul_one]
  rw [hexpand] at hmul
  have hstep : L₁ / (1 - β₀) - (z : ℝ) ^ (-(1 - β₀)) * E ≤ selHSum χ z := le_trans hmul hchain1
  have hid : L₁ / (1 - β₀) - L₁ / (2 - β₀) = L₁ / ((1 - β₀) * (2 - β₀)) := by
    field_simp; ring
  linarith [hstep, hcov, hid]

/-! ## R5f — the coverage core -/

/-- **R5f (`crush_coverage`, the coverage core).** The `hcov` hypothesis of `H_lower_of_parts`,
reduced to the coverage-sufficient error bound `E ≤ (27/100)·(1−β₀)·z^{1−β₀}` (delivered by R5e's
free cut) plus the effective-Siegel floor `L1_lower_siegel` (`(27/100)(1−β₀)(2−β₀) ≤ L₁`). Then
`z^{−(1−β₀)}·E ≤ (27/100)(1−β₀) ≤ L₁/(2−β₀)`: the `z^{−u}·z^{1−β₀}=1` collapse cancels the
scale, and the `(27/100)(1−β₀)` floor is exactly `L₁/(2−β₀)`'s guaranteed lower bound. -/
theorem crush_coverage (χ : DirichletCharacter ℂ q) {β₀ : ℝ} {z : ℕ} {E : ℝ}
    (hz : 1 ≤ z) (hβhi : β₀ < 1)
    (hE : E ≤ 27 / 100 * ((1 - β₀) * (z : ℝ) ^ (1 - β₀)))
    (hL1 : 27 / 100 * ((1 - β₀) * (2 - β₀)) ≤ (DirichletCharacter.LFunction χ 1).re) :
    (z : ℝ) ^ (-(1 - β₀)) * E ≤ (DirichletCharacter.LFunction χ 1).re / (2 - β₀) := by
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have hzu : (0 : ℝ) ≤ (z : ℝ) ^ (-(1 - β₀)) := Real.rpow_nonneg hzR.le _
  have hu2 : (0 : ℝ) < 2 - β₀ := by linarith
  have hZW : (z : ℝ) ^ (-(1 - β₀)) * (z : ℝ) ^ (1 - β₀) = 1 := by
    rw [← Real.rpow_add hzR]; simp
  -- `z^{−u}·E ≤ (27/100)(1−β₀)`
  have hstep : (z : ℝ) ^ (-(1 - β₀)) * E ≤ 27 / 100 * (1 - β₀) := by
    calc (z : ℝ) ^ (-(1 - β₀)) * E
        ≤ (z : ℝ) ^ (-(1 - β₀)) * (27 / 100 * ((1 - β₀) * (z : ℝ) ^ (1 - β₀))) :=
          mul_le_mul_of_nonneg_left hE hzu
      _ = 27 / 100 * (1 - β₀) * ((z : ℝ) ^ (-(1 - β₀)) * (z : ℝ) ^ (1 - β₀)) := by ring
      _ = 27 / 100 * (1 - β₀) := by rw [hZW, mul_one]
  -- `(27/100)(1−β₀) ≤ L₁/(2−β₀)`
  have hfloor : 27 / 100 * (1 - β₀) ≤ (DirichletCharacter.LFunction χ 1).re / (2 - β₀) := by
    rw [le_div_iff₀ hu2]; nlinarith [hL1]
  linarith [hstep, hfloor]

end Salt.SW
