/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun.M3
import Salt.Brun.M3Expansion

/-!
# N3.6 — assembling `G(z) ≥ c₀(log z)²`

Chains N3.2 (`nuStar_sum_le_gTwin_sum`), N3.3/N3.4 (`card_divisors_le_two_pow_cardFactors`,
`N3_4`) and N3.5 (`oddHarmonicSum_ge`) into the final quantitative lower bound
on the (concrete, twin-sieve) Selberg main term `mainTermSum z`.
-/

open ArithmeticFunction Finset Salt.M3Expansion
open scoped ArithmeticFunction.Omega

namespace Salt.M3Assembly

/-- The Selberg main term (as the concrete twin `gTwin` sum over odd
squarefree `ℓ < z`) grows like `(log z)²`. -/
noncomputable def mainTermSum (z : ℕ) : ℝ :=
  ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ), gTwin ℓ

/-! ## Step A — termwise bound `τ(m)/m ≤ ν*(m)` on odd `m` -/

lemma term_bound {m : ℕ} (hm : Odd m) : (m.divisors.card : ℝ) / m ≤ nuStar m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have h := card_divisors_le_two_pow_cardFactors hm0
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hcast : (m.divisors.card : ℝ) ≤ (2 : ℝ) ^ (Ω m) := by exact_mod_cast h
  rw [nuStar]
  gcongr

/-! ## Step B — chain to `mainTermSum` -/

lemma divSum_le_nuStar_sum (z : ℕ) :
    divSum ((Finset.range z).filter Odd) ≤ ∑ m ∈ (Finset.range z).filter Odd, nuStar m := by
  unfold divSum
  apply Finset.sum_le_sum
  intro m hm
  simp only [Finset.mem_filter] at hm
  exact term_bound hm.2

theorem mainTermSum_ge_sq (z : ℕ) :
    mainTermSum z ≥ (∑ a ∈ (Finset.range z.sqrt).filter Odd, (1 : ℝ) / a) ^ 2 := by
  unfold mainTermSum
  calc (∑ a ∈ (Finset.range z.sqrt).filter Odd, (1 : ℝ) / a) ^ 2
      ≤ divSum ((Finset.range z).filter Odd) := N3_4 z
    _ ≤ ∑ m ∈ (Finset.range z).filter Odd, nuStar m := divSum_le_nuStar_sum z
    _ ≤ ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ), gTwin ℓ :=
        nuStar_sum_le_gTwin_sum z

/-! ## Step C — reindex `range z.sqrt` to `Icc 1 (z.sqrt - 1)` -/

lemma range_odd_eq_Icc_odd {n : ℕ} (hn : 1 ≤ n) :
    (Finset.range n).filter Odd = (Finset.Icc 1 (n - 1)).filter Odd := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨ha, hodd⟩
    obtain ⟨k, hk⟩ := hodd
    exact ⟨⟨by omega, by omega⟩, ⟨k, hk⟩⟩
  · rintro ⟨⟨ha1, ha2⟩, hodd⟩
    exact ⟨by omega, hodd⟩

lemma stepC (z : ℕ) (hz : 1 ≤ z.sqrt) :
    ∑ a ∈ (Finset.range z.sqrt).filter Odd, (1 : ℝ) / a = oddHarmonicSum (z.sqrt - 1) := by
  unfold oddHarmonicSum
  rw [range_odd_eq_Icc_odd hz]
  apply Finset.sum_congr rfl
  intro i _
  rw [one_div]

theorem mainTermSum_ge_oddHarmonicSum_sq {z : ℕ} (hz : 1 ≤ z.sqrt) :
    mainTermSum z ≥ (oddHarmonicSum (z.sqrt - 1)) ^ 2 := by
  rw [← stepC z hz]
  exact mainTermSum_ge_sq z

/-! ## Step D — the asymptotic bridge -/

/-- (D1) `√z < z.sqrt + 1` for every natural `z`. -/
lemma sqrt_real_lt_nat_sqrt_succ (z : ℕ) : Real.sqrt (z : ℝ) < (z.sqrt : ℝ) + 1 := by
  have h : z < (z.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' z
  have hR : (z : ℝ) < ((z.sqrt : ℝ) + 1) ^ 2 := by exact_mod_cast h
  have hstep := Real.sqrt_lt_sqrt (by positivity : (0 : ℝ) ≤ (z : ℝ)) hR
  rwa [Real.sqrt_sq (by positivity)] at hstep

/-- The concrete threshold used for `z₀`. -/
def z0 : ℕ := 100

/-- `log z ≥ 4` for `z ≥ z0 = 100`, via `exp 4 = (exp 1)^4 < 2.72^4 < 100`. -/
lemma log_ge_four {z : ℕ} (hz : z0 ≤ z) : (4 : ℝ) ≤ Real.log z := by
  have hexp1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp1pos : (0:ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hpow : Real.exp 1 ^ 4 < (2.7182818286 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hexp1 hexp1pos (by norm_num)
  have hexp4 : Real.exp (4 : ℝ) = Real.exp 1 ^ 4 := by
    rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  have hbound : Real.exp (4 : ℝ) < 100 := by
    rw [hexp4]
    calc Real.exp 1 ^ 4 < (2.7182818286 : ℝ) ^ 4 := hpow
      _ < 100 := by norm_num
  have hz0 : (100 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith
  exact (Real.le_log_iff_exp_le hzpos).mpr (by linarith : Real.exp 4 ≤ (z : ℝ))

/-- The concrete numeric core of Step D: for `z ≥ z0`,
`Real.log (√z / 2) / 2 - (1 - Real.log 2) / 2 ≥ (1/8) * Real.log z`. -/
lemma D3 {z : ℕ} (hz : z0 ≤ z) :
    Real.log (Real.sqrt (z:ℝ) / 2) / 2 - (1 - Real.log 2) / 2 ≥ (1/8 : ℝ) * Real.log z := by
  have hzR : (0:ℝ) ≤ (z:ℝ) := by positivity
  have hlogsqrt : Real.log (Real.sqrt (z:ℝ)) = Real.log z / 2 := Real.log_sqrt hzR
  have hzpos : (0:ℝ) < (z:ℝ) := by
    have : (100:ℝ) ≤ (z:ℝ) := by exact_mod_cast hz
    linarith
  have hsqrtpos : (0:ℝ) < Real.sqrt (z:ℝ) := Real.sqrt_pos.mpr hzpos
  have hlogdiv : Real.log (Real.sqrt (z:ℝ) / 2) = Real.log (Real.sqrt (z:ℝ)) - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num)]
  have hlog4 : (4:ℝ) ≤ Real.log z := log_ge_four hz
  rw [hlogdiv, hlogsqrt]
  linarith

/-- Step D, fully assembled: `oddHarmonicSum (z.sqrt - 1) ≥ (1/8) * log z` for `z ≥ z0`. -/
theorem stepD {z : ℕ} (hz : z0 ≤ z) :
    oddHarmonicSum (z.sqrt - 1) ≥ (1/8 : ℝ) * Real.log z := by
  have hzge16 : (16:ℕ) ≤ z := by unfold z0 at hz; omega
  have hsqrt_ge4 : (4:ℕ) ≤ z.sqrt := Nat.le_sqrt.mpr (by omega)
  have hsqrt_ge1 : (1:ℕ) ≤ z.sqrt := by omega
  -- D2: (z.sqrt : ℝ) > √z - 1
  have hD2 : (z.sqrt : ℝ) > Real.sqrt (z:ℝ) - 1 := by
    have := sqrt_real_lt_nat_sqrt_succ z
    linarith
  -- cast the nat subtraction cleanly
  have hcast : ((z.sqrt - 1 : ℕ) : ℝ) = (z.sqrt : ℝ) - 1 := by
    have : (1:ℕ) ≤ z.sqrt := hsqrt_ge1
    push_cast [Nat.cast_sub this]
    ring
  -- √z ≥ 4, so √z - 2 ≥ √z / 2
  have hsqrtR_ge4 : (4:ℝ) ≤ Real.sqrt (z:ℝ) := by
    have h16 : (16:ℝ) ≤ (z:ℝ) := by exact_mod_cast hzge16
    have := Real.sqrt_le_sqrt h16
    have h4 : Real.sqrt (16:ℝ) = 4 := by
      rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h4] at this
  have hhalf : Real.sqrt (z:ℝ) - 2 ≥ Real.sqrt (z:ℝ) / 2 := by linarith
  -- combine: (z.sqrt - 1 : ℕ) ≥ √z / 2 > 0
  have hkey : ((z.sqrt - 1 : ℕ) : ℝ) ≥ Real.sqrt (z:ℝ) / 2 := by
    rw [hcast]; linarith
  have hhalfpos : (0:ℝ) < Real.sqrt (z:ℝ) / 2 := by
    have : (0:ℝ) < Real.sqrt (z:ℝ) := by linarith
    linarith
  -- N3.5 + monotonicity of log + D3
  have hN35 := oddHarmonicSum_ge (z.sqrt - 1)
  have hmono : Real.log (Real.sqrt (z:ℝ) / 2) ≤ Real.log ((z.sqrt - 1 : ℕ) : ℝ) :=
    Real.log_le_log hhalfpos hkey
  have hD3 := D3 hz
  linarith

/-! ## Step E — square and conclude -/

theorem exists_const_mainTermSum_ge :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ z₀ : ℕ, ∀ z ≥ z₀, mainTermSum z ≥ c₀ * (Real.log z) ^ 2 := by
  refine ⟨1/64, by norm_num, z0, ?_⟩
  intro z hz
  have hz16 : (16:ℕ) ≤ z := by unfold z0 at hz; omega
  have hsqrt_ge4 : (4:ℕ) ≤ z.sqrt := Nat.le_sqrt.mpr (by omega)
  have hsqrt_ge1 : (1:ℕ) ≤ z.sqrt := by omega
  have hlog4 : (4:ℝ) ≤ Real.log z := log_ge_four hz
  have hD := stepD hz
  have hpos : (0:ℝ) ≤ (1/8 : ℝ) * Real.log z := by linarith
  have hsq : ((1/8 : ℝ) * Real.log z) ^ 2 ≤ (oddHarmonicSum (z.sqrt - 1)) ^ 2 :=
    pow_le_pow_left₀ hpos hD 2
  have hchain := mainTermSum_ge_oddHarmonicSum_sq hsqrt_ge1
  have heq : ((1/8 : ℝ) * Real.log z) ^ 2 = (1/64 : ℝ) * (Real.log z) ^ 2 := by ring
  rw [heq] at hsq
  linarith

end Salt.M3Assembly
