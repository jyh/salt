/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.GRHPsi
import Salt.RH.MillerRabin

/-!
# O106 row R5b, node M8 — `GRHDirichlet → SmallNonMemberLog 6`, and R5 at `log⁶`

Let `H` be a proper subgroup of `(ZMod n)ˣ`, and suppose every unit `u` with `2 ≤ u.val < B` lies
in `H`, where `B = C (log n)^6`. Take a Dirichlet character `χ ≠ 1` mod `n` trivial on `H`
(Mathlib's duality, `MulChar.subgroupOrderIsoSubgroupMulChar`). At `x = B/2`, every prime
`p ≤ x` with `p ∤ n` is a unit of value `p` in `H`, so `χ(p) = 1`; a prime `p ∣ n` has `χ(p) = 0`.
Hence `θ(x) ≤ ‖θ(x, χ)‖ + log n`. With `ψ − θ ≤ 2√x log x` (Mathlib), von Koch under RH (R1; RH
follows from `GRHDirichlet` by R0b) and `‖ψ(x, χ)‖ ≤ C₂ √x log³(nx)` (M7):
`x ≤ D √x (log n)³`, so `x ≤ D² (log n)⁶`, which contradicts `x = (D² + 2)(log n)⁶`.

The exponent is `6`, against Bach's `2` (his `C(log n)²` needs a smoothed explicit formula).
`GRHDirichlet` is carried as a NAMED HYPOTHESIS (the O106 exception).
-/

namespace Salt.RH

open Complex DirichletCharacter ArithmeticFunction

/-- The twisted prime sum `θ(x, χ) = ∑_{p ≤ x} χ(p) log p`. -/
noncomputable def thetaChi {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, χ (p : ZMod q) * (Real.log p : ℂ)

/-- `‖ψ(x, χ) − θ(x, χ)‖ ≤ ψ(x) − θ(x)`. -/
theorem norm_psiChi_sub_thetaChi_le {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ‖psiChi χ x - thetaChi χ x‖ ≤ Chebyshev.psi x - Chebyshev.theta x := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  have h : psiChi χ x - thetaChi χ x
      = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬ m.Prime, χ (m : ZMod q) * (Λ m : ℂ) := by
    unfold psiChi thetaChi
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hm
    · rw [vonMangoldt_apply_prime hm]; simp
    · simp
  rw [h]
  exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => norm_twist_le χ m)

/-- If `χ(p) = 1` for every prime `p ≤ x` not dividing `n`, then `θ(x) ≤ ‖θ(x, χ)‖ + log n`. -/
theorem theta_le_norm_thetaChi_add {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) {x : ℝ}
    (hall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬ p ∣ n → χ (p : ZMod n) = 1) :
    Chebyshev.theta x ≤ ‖thetaChi χ x‖ + Real.log n := by
  have hn0 : n ≠ 0 := NeZero.ne n
  set S := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime with hS
  have hsplit : ((Chebyshev.theta x : ℝ) : ℂ)
      = thetaChi χ x + ∑ p ∈ S, (1 - χ (p : ZMod n)) * (Real.log p : ℂ) := by
    unfold Chebyshev.theta thetaChi
    push_cast
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hpt : ∀ p ∈ S, ‖(1 - χ (p : ZMod n)) * (Real.log p : ℂ)‖
      ≤ if p ∣ n then Real.log p else 0 := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
    have hpx : (p : ℝ) ≤ x := by
      have hx0 : 0 ≤ x := by
        by_contra h
        have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        rw [this] at hpI
        simp at hpI
      exact (Nat.le_floor_iff hx0).mp (Finset.mem_Ioc.mp hpI).2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    split_ifs with hd
    · have hnu : ¬ IsUnit (p : ZMod n) := by
        rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hpp]
        exact not_not.mpr hd
      rw [MulChar.map_nonunit χ hnu, sub_zero, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hlog]
    · rw [hall p hpp hpx hd, sub_self, zero_mul, norm_zero]
  have hbad : ‖∑ p ∈ S, (1 - χ (p : ZMod n)) * (Real.log p : ℂ)‖ ≤ Real.log n := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ p ∈ S, ‖(1 - χ (p : ZMod n)) * (Real.log p : ℂ)‖
        ≤ ∑ p ∈ S, (if p ∣ n then Real.log p else 0) := Finset.sum_le_sum hpt
      _ = ∑ p ∈ S with p ∣ n, Real.log p := (Finset.sum_filter _ _).symm
      _ ≤ ∑ p ∈ n.primeFactors, Real.log p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro p hp
            obtain ⟨hpS, hpd⟩ := Finset.mem_filter.mp hp
            exact Nat.mem_primeFactors.mpr ⟨(Finset.mem_filter.mp hpS).2, hpd, hn0⟩
          · intro p hp _
            exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
      _ = Real.log ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) := by
          rw [Nat.cast_prod, Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      _ ≤ Real.log n := by
          have hle : (∏ p ∈ n.primeFactors, p) ≤ n :=
            Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.prod_primeFactors_dvd n)
          have hpos : 0 < (∏ p ∈ n.primeFactors, p) :=
            Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
          exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
  have hθ : Chebyshev.theta x = ‖((Chebyshev.theta x : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.theta_nonneg x)]
  rw [hθ, hsplit]
  exact le_trans (norm_add_le _ _) (by linarith)

/-- A proper subgroup of `(ZMod n)ˣ` is killed by some non-principal Dirichlet character. -/
theorem exists_char_trivial_on {n : ℕ} [NeZero n] {H : Subgroup (ZMod n)ˣ} (hH : H ≠ ⊤) :
    ∃ χ : DirichletCharacter ℂ n, χ ≠ 1 ∧ ∀ u ∈ H, χ (u : ZMod n) = 1 := by
  set e := MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ with he
  rcases Subgroup.bot_or_exists_ne_one (e H).ofDual with h | ⟨χ, hχ, hχ1⟩
  · exfalso
    apply hH
    apply e.injective
    rw [OrderIso.map_top]
    change e H = OrderDual.toDual ⊥
    rw [← h]
    rfl
  · exact ⟨χ, hχ1, MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff.mp hχ⟩

/-- The closing real arithmetic of M8: `s² ≤ D s l³` and `s² = (D² + 2) l⁶` are incompatible. -/
theorem m8_final {D s l : ℝ} (hs1 : 1 ≤ s) (hl1 : 1 ≤ l)
    (hmain : s ^ 2 ≤ D * s * l ^ 3) (hxB : s ^ 2 = (D ^ 2 + 2) * l ^ 6) : False := by
  have hs0 : 0 < s := by linarith
  have hsD : s ≤ D * l ^ 3 := by
    have h1 : s * s ≤ (D * l ^ 3) * s := by
      have e : D * s * l ^ 3 = (D * l ^ 3) * s := by ring
      rw [sq] at hmain; linarith
    exact le_of_mul_le_mul_right h1 hs0
  have hfin : s ^ 2 ≤ D ^ 2 * l ^ 6 := by
    calc s ^ 2 ≤ (D * l ^ 3) ^ 2 := pow_le_pow_left₀ hs0.le hsD 2
      _ = D ^ 2 * l ^ 6 := by ring
  have hl6 : 1 ≤ l ^ 6 := one_le_pow₀ hl1
  linarith

/-- **M8.** `GRHDirichlet → SmallNonMemberLog 6`. -/
theorem smallNonMemberLog_six_of_GRH (hGRH : GRHDirichlet) : SmallNonMemberLog 6 := by
  obtain ⟨C₁, hC₁⟩ := vonKochPsi_three_of_RH (riemannHypothesis_of_GRHDirichlet hGRH)
  obtain ⟨C₂, hC₂0, hC₂⟩ := psiChi_le_of_GRH hGRH
  set D : ℝ := |C₁| + 5 + 8 * C₂ with hD
  refine ⟨2 * D ^ 2 + 4, fun n hn H hH => ?_⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set l : ℝ := Real.log n with hl
  have hl1 : 1 ≤ l := by
    rw [hl, Real.le_log_iff_exp_le hn0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hl6 : 1 ≤ l ^ 6 := one_le_pow₀ hl1
  set B : ℝ := (2 * D ^ 2 + 4) * l ^ 6 with hB
  by_contra hcon
  push Not at hcon
  -- a non-member, and every non-member has value at least `2`
  obtain ⟨u0, hu0⟩ : ∃ u : (ZMod n)ˣ, u ∉ H := by
    by_contra h
    push Not at h
    exact hH (eq_top_iff.mpr fun u _ => h u)
  have hval2 : ∀ u : (ZMod n)ˣ, u ∉ H → 2 ≤ (u : ZMod n).val := by
    intro u hu
    have hu1 : u ≠ 1 := fun h => hu (h ▸ H.one_mem)
    have h0 : (u : ZMod n).val ≠ 0 := by
      intro h
      rw [ZMod.val_eq_zero] at h
      exact (Units.ne_zero u) h
    have h1 : (u : ZMod n).val ≠ 1 := by
      intro h
      apply hu1
      ext
      have : (u : ZMod n) = ((u : ZMod n).val : ZMod n) := (ZMod.natCast_zmod_val _).symm
      rw [this, h]
      simp
    omega
  have hBn : B ≤ n := by
    have h1 := hcon u0 hu0 (hval2 u0 hu0)
    have h2 : ((u0 : ZMod n).val : ℝ) < n := by exact_mod_cast ZMod.val_lt _
    linarith
  -- the character
  obtain ⟨χ, hχ1, hχH⟩ := exists_char_trivial_on hH
  set x : ℝ := B / 2 with hx
  have hx2 : 2 ≤ x := by
    rw [hx, hB]
    have : 0 ≤ 2 * D ^ 2 * l ^ 6 := by positivity
    nlinarith
  have hxn : x < n := by
    have : 0 < B := by linarith
    linarith
  have hall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬ p ∣ n → χ (p : ZMod n) = 1 := by
    intro p hp hpx hpn
    have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
    have hpn' : p < n := by exact_mod_cast (lt_of_le_of_lt hpx hxn)
    have hval : (ZMod.unitOfCoprime p hcop : ZMod n).val = p := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hpn']
    have huH : ZMod.unitOfCoprime p hcop ∈ H := by
      by_contra h
      have h1 := hcon _ h (by rw [hval]; exact hp.two_le)
      rw [hval] at h1
      have : 0 < B := by linarith
      linarith
    have := hχH _ huH
    rwa [ZMod.coe_unitOfCoprime] at this
  -- the inequalities
  have hx0 : 0 < x := by linarith
  have h1 := hC₁ x hx2
  have h2 := hC₂ n χ hχ1 x hx2
  have h3 := norm_psiChi_sub_thetaChi_le χ x
  have h4 := Chebyshev.psi_sub_theta_le (show (1 : ℝ) ≤ x by linarith)
  have h5 := theta_le_norm_thetaChi_add χ hall
  have h6 : ‖thetaChi χ x‖ ≤ ‖psiChi χ x‖ + ‖psiChi χ x - thetaChi χ x‖ := by
    have := norm_sub_le (psiChi χ x) (psiChi χ x - thetaChi χ x)
    rwa [sub_sub_cancel] at this
  set s : ℝ := Real.sqrt x with hs
  have hs1 : 1 ≤ s := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hss : s ^ 2 = x := by rw [hs]; exact Real.sq_sqrt hx0.le
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlx : Real.log x ≤ l := Real.log_le_log hx0 hxn.le
  have hlnx : Real.log (n * x) ≤ 2 * l := by
    rw [Real.log_mul hn0.ne' hx0.ne', ← hl]; linarith
  have hlnx0 : 0 ≤ Real.log (n * x) := Real.log_nonneg (by nlinarith)
  have hl3 : l ≤ l ^ 3 := le_self_pow₀ hl1 (by norm_num)
  have hl3' : 1 ≤ l ^ 3 := one_le_pow₀ hl1
  have e1 : C₁ * s * Real.log x ^ 3 ≤ |C₁| * s * l ^ 3 := by
    have : Real.log x ^ 3 ≤ l ^ 3 := pow_le_pow_left₀ hlx0 hlx 3
    have h0 : C₁ * s * Real.log x ^ 3 ≤ |C₁| * s * Real.log x ^ 3 := by
      have : 0 ≤ s * Real.log x ^ 3 := by positivity
      nlinarith [le_abs_self C₁]
    have : |C₁| * s * Real.log x ^ 3 ≤ |C₁| * s * l ^ 3 := by
      have : 0 ≤ |C₁| * s := by positivity
      exact mul_le_mul_of_nonneg_left (by assumption) this
    linarith
  have e2 : C₂ * s * Real.log (n * x) ^ 3 ≤ 8 * C₂ * s * l ^ 3 := by
    have : Real.log (n * x) ^ 3 ≤ (2 * l) ^ 3 := pow_le_pow_left₀ hlnx0 hlnx 3
    have : 0 ≤ C₂ * s := by positivity
    nlinarith
  have e3 : 2 * s * Real.log x ≤ 2 * s * l ^ 3 := by
    have : 0 ≤ 2 * s := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  have e4 : l ≤ s * l ^ 3 := by nlinarith
  have habs := (abs_le.mp h1).1
  -- `x ≤ D · s · l³`
  have hmain : s ^ 2 ≤ D * s * l ^ 3 := by
    rw [hss]
    have : D * s * l ^ 3 = |C₁| * s * l ^ 3 + 4 * (s * l ^ 3) + s * l ^ 3
        + 8 * C₂ * s * l ^ 3 := by rw [hD]; ring
    rw [this]
    have h4' : Chebyshev.psi x - Chebyshev.theta x ≤ 2 * s * Real.log x := by
      rw [hs]; linarith
    linarith
  have hxB : s ^ 2 = (D ^ 2 + 2) * l ^ 6 := by rw [hss, hx, hB]; ring
  exact m8_final hs1 hl1 hmain hxB

/-- **R5 at `log⁶`.** `GRHDirichlet → DeterministicMRLog 6`: under GRH, an odd `n ≥ 3` that passes
the Miller–Rabin test at every base `2 ≤ a < min(n, C (log n)⁶)` is prime. -/
theorem deterministicMRLog_six_of_GRH (hGRH : GRHDirichlet) : DeterministicMRLog 6 :=
  deterministicMRLog_of_smallNonMemberLog (smallNonMemberLog_six_of_GRH hGRH)

end Salt.RH
