/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Summit
import Salt.Vmvt.PrimeEff

/-!
# Theorem 24.5 — THE SUMMIT INDUCTION (VMVT-SUMMIT-2)

The full Vinogradov Mean Value Theorem `vmvt`, assembled by induction on `r`:
the medium-`x` trivial branch (`vmvt_trivial_branch`) below `Xmed = k^{24·max(k,r)}`
and the large-`x` transversal step (`vmvt_step_transversal_large`) above it, whose
prime pigeonhole is supplied by `exists_transversal_prime_set'` — the effective
re-supply of `PrimeEff.primes_in_Ioc_eff`.

The bridge is the two-arm check (both arms clear at `k ≥ 2`): from `x > Xmed` and
`x ≤ y^k` (`y = vmvtScale k x`) one gets `y^k > Xmed ≥ Y'(k)^k`, hence `y > Y'(k)`,
so the pigeonhole applies; and `hreg` follows from `(k²+4E)^k ≤ k^{8·max} ≤ Xmed`.
The re-grade to `k^{24k²}` (`MeanValue.vmvtC0`) is exactly what makes both arms clear.
-/

open Finset

namespace Salt.Vmvt

/-! ## Arithmetic helpers: `n^k ≤ k^{2n}` for `2 ≤ k ≤ n` -/

/-- `(a+1)^b ≤ b²·a^b` for `2 ≤ b ≤ a`.  Real route: `((a+1)/a)^b = (1+1/a)^b ≤
(1+1/a)^a ≤ e < 4 ≤ b²` (`add_one_le_exp` + `exp_one_lt_d9`). -/
lemma succ_pow_le_sq_mul {a b : ℕ} (hb : 2 ≤ b) (hab : b ≤ a) :
    (a + 1) ^ b ≤ b ^ 2 * a ^ b := by
  have ha1 : 1 ≤ a := le_trans (by omega) hab
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have key : ((a : ℝ) + 1) ^ b ≤ (b : ℝ) ^ 2 * (a : ℝ) ^ b := by
    have hfac : ((a : ℝ) + 1) ^ b = (a : ℝ) ^ b * (1 + 1 / (a : ℝ)) ^ b := by
      rw [← mul_pow]; congr 1; field_simp
    rw [hfac]
    have h1 : (1 : ℝ) + 1 / (a : ℝ) ≤ Real.exp (1 / (a : ℝ)) := by
      have := Real.add_one_le_exp (1 / (a : ℝ)); linarith
    have hexp : (1 + 1 / (a : ℝ)) ^ b ≤ Real.exp 1 := by
      calc (1 + 1 / (a : ℝ)) ^ b ≤ (Real.exp (1 / (a : ℝ))) ^ b := by
            gcongr
        _ = Real.exp ((b : ℝ) * (1 / (a : ℝ))) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp 1 := by
            apply Real.exp_le_exp.mpr
            rw [mul_one_div, div_le_one haR]; exact_mod_cast hab
    have hb24 : Real.exp 1 ≤ (b : ℝ) ^ 2 := by
      nlinarith [Real.exp_one_lt_d9, hbR]
    have hh := mul_le_mul_of_nonneg_left (le_trans hexp hb24) (pow_nonneg haR.le b)
    nlinarith [hh]
  exact_mod_cast key

/-- `n^k ≤ k^{2n}` for `2 ≤ k ≤ n` (the tight base-vs-exponent trade). -/
lemma pow_le_pow_base {a b : ℕ} (hb : 2 ≤ b) (hab : b ≤ a) : a ^ b ≤ b ^ (2 * a) := by
  induction a, hab using Nat.le_induction with
  | base => exact Nat.pow_le_pow_right (by omega) (by omega)
  | succ n hn ih =>
    calc (n + 1) ^ b ≤ b ^ 2 * n ^ b := succ_pow_le_sq_mul hb hn
      _ ≤ b ^ 2 * b ^ (2 * n) := Nat.mul_le_mul (le_refl _) ih
      _ = b ^ (2 * (n + 1)) := by rw [← pow_add]; congr 1; omega

/-- `(9k²r)^k ≤ k^{8·max(k,r)}` for `2 ≤ k`, `1 ≤ r` (the medium-`x` regularity fuel). -/
lemma nine_ksq_r_pow_le {k r : ℕ} (hk : 2 ≤ k) :
    (9 * k ^ 2 * r) ^ k ≤ k ^ (8 * max k r) := by
  have hkpos : 1 ≤ k := by omega
  have h9 : (9 : ℕ) ≤ k ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hk 4)
  have hrpow : r ^ k ≤ k ^ (2 * max k r) := by
    rcases le_total r k with hrk | hkr
    · calc r ^ k ≤ k ^ k := Nat.pow_le_pow_left hrk k
        _ ≤ k ^ (2 * max k r) := Nat.pow_le_pow_right hkpos (by omega)
    · calc r ^ k ≤ k ^ (2 * r) := pow_le_pow_base hk hkr
        _ ≤ k ^ (2 * max k r) := Nat.pow_le_pow_right hkpos (by omega)
  calc (9 * k ^ 2 * r) ^ k = 9 ^ k * (k ^ 2) ^ k * r ^ k := by rw [mul_pow, mul_pow]
    _ ≤ (k ^ 4) ^ k * (k ^ 2) ^ k * k ^ (2 * max k r) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h9 k) (le_refl _)) hrpow
    _ = k ^ (4 * k) * k ^ (2 * k) * k ^ (2 * max k r) := by rw [← pow_mul, ← pow_mul]
    _ = k ^ (4 * k + 2 * k + 2 * max k r) := by rw [← pow_add, ← pow_add]
    _ ≤ k ^ (8 * max k r) := Nat.pow_le_pow_right hkpos (by
        have : k ≤ max k r := le_max_left k r; omega)

/-! ## The effective pigeonhole prime set (Stone A2) -/

/-- **The pigeonhole prime set, effectively.**  The re-supply of the landed
`exists_transversal_prime_set` with the effective count `primes_in_Ioc_eff`: for
`k ≥ 2` there is a threshold `Y ≤ 2²⁴ ⊔ 64k⁶` such that for every `y ≥ Y`, the
interval `(y, 2y]` holds more than `½k²(k−1)` primes (`k·k·(k−1) < 2·#P`). -/
theorem exists_transversal_prime_set' {k : ℕ} (hk : 2 ≤ k) :
    ∃ Y : ℕ, Y ≤ 2 ^ 24 ⊔ (64 * k ^ 6) ∧ 2 ≤ Y ∧ ∀ y : ℕ, Y ≤ y →
      k * k * (k - 1) < 2 * ((Finset.Ioc y (2 * y)).filter Nat.Prime).card := by
  obtain ⟨y₁, hy1cap, hy1⟩ := primes_in_Ioc_eff
  set M : ℝ := ((k * k * (k - 1) : ℕ) : ℝ) with hMdef
  refine ⟨max (max y₁ (64 * k ^ 6)) 2, ?_, le_max_right _ _, fun y hy => ?_⟩
  · refine max_le (max_le ?_ (le_max_right _ _)) (le_trans (by norm_num) (le_max_left _ _))
    exact le_trans hy1cap (le_max_left _ _)
  have hy1y : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hNy : 64 * k ^ 6 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy2 : 2 ≤ y := le_trans (le_max_right _ _) hy
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  have hlogpos : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hlog_le : Real.log (y : ℝ) ≤ 2 * Real.sqrt (y : ℝ) := Salt.SW.log_le_two_sqrt hypos
  set P : ℕ := ((Finset.Ioc y (2 * y)).filter Nat.Prime).card with hPdef
  have hPge : (y : ℝ) / (8 * Real.log (y : ℝ)) ≤ (P : ℝ) := hy1 y hy1y
  -- `√y / 16 ≤ P`
  have hcross : Real.sqrt (y : ℝ) * Real.log (y : ℝ) ≤ 2 * (y : ℝ) := by
    have h1 : Real.sqrt (y : ℝ) * Real.log (y : ℝ)
        ≤ Real.sqrt (y : ℝ) * (2 * Real.sqrt (y : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_le (Real.sqrt_nonneg _)
    nlinarith [h1, Real.mul_self_sqrt hypos.le]
  have hstep1 : Real.sqrt (y : ℝ) / 16 ≤ (P : ℝ) := by
    have hle : Real.sqrt (y : ℝ) / 16 ≤ (y : ℝ) / (8 * Real.log (y : ℝ)) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith [hcross]
    linarith [hle, hPge]
  -- `8(M+1) ≤ √y`, from `y ≥ 64k⁶` and `k·k·(k−1)+1 ≤ k³`
  have hnat3 : k * k * (k - 1) + 1 ≤ k ^ 3 := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; nlinarith [Nat.zero_le m]
  have hMval : M + 1 = ((k * k * (k - 1) + 1 : ℕ) : ℝ) := by
    rw [hMdef, Nat.cast_add, Nat.cast_one]
  have h8k3 : (8 : ℝ) * (k : ℝ) ^ 3 ≤ Real.sqrt (y : ℝ) := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 8 * (k : ℝ) ^ 3 by positivity)]
    apply Real.sqrt_le_sqrt
    have hcast : (8 * (k : ℝ) ^ 3) ^ 2 = ((64 * k ^ 6 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]; exact_mod_cast hNy
  have hMk3 : M + 1 ≤ (k : ℝ) ^ 3 := by
    rw [hMval]
    calc ((k * k * (k - 1) + 1 : ℕ) : ℝ) ≤ ((k ^ 3 : ℕ) : ℝ) := by exact_mod_cast hnat3
      _ = (k : ℝ) ^ 3 := by push_cast; ring
  have h8M : 8 * (M + 1) ≤ Real.sqrt (y : ℝ) := by linarith [hMk3, h8k3]
  -- assemble: `M + 1 ≤ 2P`, hence `M < 2P`
  have hfinalR : M < 2 * (P : ℝ) := by
    have h1 : M + 1 ≤ Real.sqrt (y : ℝ) / 8 := by linarith [h8M]
    have h2 : Real.sqrt (y : ℝ) / 8 ≤ 2 * (P : ℝ) := by linarith [hstep1]
    linarith
  rw [hMdef] at hfinalR
  exact_mod_cast hfinalR

/-! ## THE SUMMIT: the Vinogradov Mean Value Theorem -/

/-- **THE VINOGRADOV MEAN VALUE THEOREM (Theorem 24.5).**  For `k ≥ 2`, `r ≥ 1`,
`x ≥ 1`, `J_k(x, kr) ≤ D(k,r)·x^{E(k,r)}` (`VmvtBound k r x`), with the exponent
`E(k,r) = 2rk − ½k(k+1) + η(k,r)` source-EXACT and the constant `D(k,r) = k^{24k²r}`
free.  Induction on `r`: base `r = 1` = `vmvt_base`; the step splits at
`Xmed = k^{24·max(k,r+1)}` — below, the trivial branch; above, the transversal
step, whose pigeonhole is the effective supply `exists_transversal_prime_set'`
reached because `x > Xmed ≥ Y'(k)^k` forces `vmvtScale k x > Y'(k)`, and whose
regularity `k²+4E(k,r) ≤ x^{1/k}` follows from `(k²+4E)^k ≤ k^{8·max} ≤ Xmed < x`. -/
theorem vmvt (k r x : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) (hx : 1 ≤ x) : VmvtBound k r x := by
  suffices H : ∀ r', 1 ≤ r' → ∀ x', 1 ≤ x' → VmvtBound k r' x' from H r hr x hx
  intro r' hr'
  induction r', hr' using Nat.le_induction with
  | base => intro x' hx'; exact vmvt_base hk hx'
  | succ n hn ih =>
    intro x' hx'
    by_cases hmed : x' ≤ Xmed k (n + 1)
    · exact vmvt_trivial_branch hk (by omega) hx' hmed
    · rw [not_le] at hmed
      have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
      have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hxlarge : k ^ (24 * max k (n + 1)) < x' := hmed
      have hyx : x' ≤ (vmvtScale k x') ^ k := le_scale_pow (by omega)
      set y := vmvtScale k x' with hy
      have hylt : k ^ (24 * max k (n + 1)) < y ^ k := lt_of_lt_of_le hxlarge hyx
      have hkm : k ≤ max k (n + 1) := le_max_left _ _
      -- `k < y`, hence `hyk`, `hy2`
      have hky : k < y := by
        by_contra h; rw [not_lt] at h
        have h1 : y ^ k ≤ k ^ k := Nat.pow_le_pow_left h k
        have h2 : k ^ k ≤ k ^ (24 * max k (n + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hyk : k ≤ y := le_of_lt hky
      have hy2 : 2 ≤ y := by omega
      -- `hpig` via the effective supply (pure-nat bridge `y^k > Xmed ≥ Y'^k`)
      obtain ⟨Y, hYbound, _hY2, hYcount⟩ := exists_transversal_prime_set' hk
      have hYk24 : Y ≤ k ^ 24 := by
        refine le_trans hYbound (max_le (Nat.pow_le_pow_left hk 24) ?_)
        calc 64 * k ^ 6 ≤ k ^ 6 * k ^ 6 :=
              Nat.mul_le_mul (le_trans (by norm_num) (Nat.pow_le_pow_left hk 6)) (le_refl _)
          _ = k ^ 12 := by rw [← pow_add]
          _ ≤ k ^ 24 := Nat.pow_le_pow_right (by omega) (by omega)
      have hYpow : Y ^ k ≤ k ^ (24 * max k (n + 1)) := by
        calc Y ^ k ≤ (k ^ 24) ^ k := Nat.pow_le_pow_left hYk24 k
          _ = k ^ (24 * k) := by rw [← pow_mul]
          _ ≤ k ^ (24 * max k (n + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
      have hyY : Y < y := by
        by_contra h; rw [not_lt] at h
        have h1 : y ^ k ≤ Y ^ k := Nat.pow_le_pow_left h k
        omega
      have hpig : k * k * (k - 1)
          < 2 * ((Finset.Ioc y (2 * y)).filter Nat.Prime).card := hYcount y (le_of_lt hyY)
      -- `hreg` from `(k²+4E)^k ≤ k^{8·max} ≤ Xmed < x'`
      have hEnn : 0 ≤ vmvtExp k n := vmvtExp_nonneg hk hn
      have hEle : vmvtExp k n ≤ 2 * (n : ℝ) * (k : ℝ) := by
        have hη := vmvtEta_le (k := k) (r := n) (by omega) hn
        unfold vmvtExp; nlinarith [hη, hk1R]
      have hbase_nn : (0 : ℝ) ≤ (k : ℝ) ^ 2 + 4 * vmvtExp k n := by
        nlinarith [hEnn, sq_nonneg (k : ℝ)]
      have hklin : (k : ℝ) ^ 2 + 4 * vmvtExp k n ≤ 9 * (k : ℝ) ^ 2 * (n : ℝ) := by
        nlinarith [hEle, hk1R, hn1R]
      have hcube : ((k : ℝ) ^ 2 + 4 * vmvtExp k n) ^ k ≤ (x' : ℝ) := by
        have hexp_le : 8 * max k n ≤ 24 * max k (n + 1) := by
          have : max k n ≤ max k (n + 1) := by omega
          omega
        have h4 : k ^ (8 * max k n) ≤ x' :=
          le_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hexp_le) hxlarge)
        calc ((k : ℝ) ^ 2 + 4 * vmvtExp k n) ^ k
            ≤ (9 * (k : ℝ) ^ 2 * (n : ℝ)) ^ k := pow_le_pow_left₀ hbase_nn hklin k
          _ = (((9 * k ^ 2 * n) ^ k : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((k ^ (8 * max k n) : ℕ) : ℝ) := by exact_mod_cast nine_ksq_r_pow_le hk
          _ ≤ (x' : ℝ) := by exact_mod_cast h4
      have hreg : (k : ℝ) ^ 2 + 4 * vmvtExp k n ≤ (x' : ℝ) ^ ((1 : ℝ) / (k : ℝ)) := by
        rw [one_div]
        calc (k : ℝ) ^ 2 + 4 * vmvtExp k n
            = (((k : ℝ) ^ 2 + 4 * vmvtExp k n) ^ k) ^ ((k : ℝ)⁻¹) :=
              (Real.pow_rpow_inv_natCast hbase_nn (by omega)).symm
          _ ≤ (x' : ℝ) ^ ((k : ℝ)⁻¹) :=
              Real.rpow_le_rpow (by positivity) hcube (by positivity)
      -- assemble the transversal step
      have hkle : k ≤ k * (n + 1) := Nat.le_mul_of_pos_right k (Nat.succ_pos n)
      have hrange : ((k * (n + 1) : ℕ) : ℝ) ≤ vmvtExp k (n + 1) := b_le_vmvtExp hk (by omega)
      exact vmvt_step_transversal_large x' (Fin.castLE hkle) hk hn (Fin.castLE_injective hkle)
        hrange hx' hyk hy2 hpig hreg ih

end Salt.Vmvt
