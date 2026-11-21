/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# O106 — the target statements (row R0)

Classical consequences of the Riemann hypothesis, and of GRH for Dirichlet `L`-functions, written
as **statements only**: each target is a `def … : Prop`, and nothing in this file asserts one of
them. The theorems that discharge them are later rows of the plan. Each one carries
`RiemannHypothesis` (Mathlib's own, `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`) or
`GRHDirichlet` below as a NAMED HYPOTHESIS.

Statement choices that a reader should check (the audit list):
* `GRHDirichlet` restricts to the open strip `0 < re s < 1`. An imprimitive `χ` has extra zeros
  on `re s = 0` (from the Euler factors it drops), and the trivial zeros lie in `re s ≤ 0`, so the
  strip is where the hypothesis has content. The principal character mod `N` has a pole at `1`,
  which is outside the open strip.
* `li` is the PRINCIPAL-VALUE logarithmic integral
  `lim_{ε→0⁺} (∫₀^{1-ε} + ∫_{1+ε}^x) dt / log t`, for `x > 1` only (for `x ≤ 1` the limit
  diverges and `limUnder` returns junk; every target binds `x ≥ 2`). Schoenfeld's bound is
  stated with it. `Li2` (`∫₂^x`) differs by the constant `li 2 ≈ 1.045` and is the form the
  `O(·)` targets use.
* `π(x)` is `Nat.primeCounting ⌊x⌋₊`. The `n`-th prime is `Nat.nth Nat.Prime n`
  (0-indexed: `2` at `0`).
* `StrongProbablePrime n a` is the Miller–Rabin test at base `a`: write `n - 1 = 2^s · d` with
  `d` odd; then `a^d = 1` or `a^(2^r · d) = -1` for some `r < s`, in `ZMod n`.
-/

namespace Salt.RH

open Real

/-- **GRH for Dirichlet `L`-functions**: every zero of `L(s, χ)` in the open critical strip lies
on the critical line, for every modulus `N` and every character `χ` mod `N`. -/
def GRHDirichlet : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-! ## The prime-counting targets -/

/-- von Koch's form at log power `k`: `|ψ(x) − x| ≤ C √x (log x)^k` for `x ≥ 2`.
RH gives `k = 2` (von Koch 1901). Row R1 targets `k = 3` or `k = 2` by its route. -/
def VonKochPsi (k : ℕ) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * Real.sqrt x * Real.log x ^ k

/-- The offset logarithmic integral `∫₂^x dt / log t`. -/
noncomputable def Li2 (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- The principal-value logarithmic integral
`li x = lim_{ε→0⁺} (∫₀^{1-ε} + ∫_{1+ε}^x) dt / log t`, meaningful for `x > 1` only. -/
noncomputable def li (x : ℝ) : ℝ :=
  Filter.limUnder (nhdsWithin (0 : ℝ) (Set.Ioi 0)) fun ε : ℝ =>
    (∫ t in (0 : ℝ)..(1 - ε), 1 / Real.log t) + ∫ t in (1 + ε)..x, 1 / Real.log t

/-- The `π`-form at log power `k`: `|π(x) − Li₂(x)| ≤ C √x (log x)^k` for `x ≥ 2` (row R2). -/
def PiLi2 (k : ℕ) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li2 x| ≤ C * Real.sqrt x * Real.log x ^ k

/-- **Schoenfeld (1976)**, the explicit form: `|π(x) − li(x)| < √x log x / (8π)` for `x ≥ 2657`
(row R2-S; class D, a statement only). -/
def Schoenfeld : Prop :=
  ∀ x : ℝ, 2657 ≤ x →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - li x| < Real.sqrt x * Real.log x / (8 * Real.pi)

/-- **Cramér's gap bound** at log power `k`: `p_{n+1} − p_n ≤ C √p_n (log p_n)^k`.
Cramér (1920) under RH: `k = 1` (row R3-S); the weak form `k = 3` is row R3. -/
def CramerGap (k : ℕ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ,
    ((Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n)
      ≤ C * Real.sqrt (Nat.nth Nat.Prime n) * Real.log (Nat.nth Nat.Prime n) ^ k

/-- **Robin's inequality** (1984): `σ(n) < e^γ n log log n` for every `n > 5040`.
Robin: RH implies it, and conversely. Row R4; class D, a statement only. -/
def RobinInequality : Prop :=
  ∀ n : ℕ, 5040 < n →
    (ArithmeticFunction.sigma 1 n : ℝ)
      < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)

/-! ## Miller–Rabin -/

/-- The **strong probable-prime test** (Miller–Rabin) for `n` at base `a`: with
`n − 1 = 2^s · d`, `d` odd, either `a^d = 1` or `a^(2^r · d) = −1` for some `r < s`, in `ZMod n`. -/
def StrongProbablePrime (n a : ℕ) : Prop :=
  (a : ZMod n) ^ ((n - 1) / 2 ^ (n - 1).factorization 2) = 1 ∨
    ∃ r < (n - 1).factorization 2,
      (a : ZMod n) ^ (2 ^ r * ((n - 1) / 2 ^ (n - 1).factorization 2)) = -1

/-- **Miller's algebraic half** (unconditional; row R5a): for odd composite `n`, every unit that
passes the test lies in one proper subgroup of `(ZMod n)ˣ`. -/
def MillerAlgebraic : Prop :=
  ∀ n : ℕ, 3 ≤ n → Odd n → ¬ n.Prime →
    ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧
      ∀ u : (ZMod n)ˣ, StrongProbablePrime n (u : ZMod n).val → u ∈ H

/-- A **small unit outside any proper subgroup** at scale `C (log n)^2` (row R5b; Ankeny–Montgomery
shape). The UNIT form asked here is Bach's at `C = 3`; his `C = 2` is the least INTEGER outside `H`
with no coprimality asked (Lamzouri–Li–Soundararajan, arXiv 1309.3595 §1.1). -/
def SmallNonMember (C : ℝ) : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ →
    ∃ u : (ZMod n)ˣ, u ∉ H ∧ 2 ≤ (u : ZMod n).val ∧
      ((u : ZMod n).val : ℝ) < C * Real.log n ^ 2

/-- **Deterministic Miller–Rabin** at scale `C (log n)^2` (row R5): an odd `n ≥ 3` that passes the
test at every base `2 ≤ a < min(n, C (log n)^2)` is prime. Bach (1990), under GRH: `C = 2`. -/
def DeterministicMR (C : ℝ) : Prop :=
  ∀ n : ℕ, 3 ≤ n → Odd n →
    (∀ a : ℕ, 2 ≤ a → a < n → (a : ℝ) < C * Real.log n ^ 2 → StrongProbablePrime n a) →
      n.Prime

/-- The POLYLOG form of `SmallNonMember` at log power `k` (O106 plan, arm (b)): the unsmoothed
R1 route ported to `L(s, χ)` reaches it at `k = 6` with `ψ(x, χ) ≪ √x log³(qx)`, and at `k = 3`
with the finer shape `ψ(x, χ) ≪ √x log(qx) (log x)²` (`Salt.RH.GRHMiller`); Bach's `C (log n)²`
needs a smoothed explicit formula. -/
def SmallNonMemberLog (k : ℕ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → ∀ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ →
    ∃ u : (ZMod n)ˣ, u ∉ H ∧ 2 ≤ (u : ZMod n).val ∧
      ((u : ZMod n).val : ℝ) < C * Real.log n ^ k

/-- Deterministic Miller–Rabin with bases below `C (log n)^k`. -/
def DeterministicMRLog (k : ℕ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → Odd n →
    (∀ a : ℕ, 2 ≤ a → a < n → (a : ℝ) < C * Real.log n ^ k → StrongProbablePrime n a) →
      n.Prime

/-! ## R0b — the GRH Prop has the content it should: it implies Mathlib's RH -/

/-- A zero of `ζ` in the closed left half-plane `re s ≤ 0` is a trivial zero `-2(n+1)`.
From the functional equation at `w = 1 - s` (where `re w ≥ 1`, so `ζ w ≠ 0` and `Γ w ≠ 0`):
the factor `cos (π w / 2)` must vanish. -/
theorem riemannZeta_trivial_of_re_nonpos {s : ℂ} (hs : riemannZeta s = 0) (hre : s.re ≤ 0) :
    ∃ n : ℕ, s = -2 * (n + 1) := by
  set w : ℂ := 1 - s with hw
  have hwre : 1 ≤ w.re := by simp [hw]; linarith
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hs
    norm_num at hs
  have hwnat : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hw1 : w ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  have hfe := riemannZeta_one_sub hwnat hw1
  have h1w : 1 - w = s := by simp [hw]
  rw [h1w, hs] at hfe
  have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hGw : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwnat
  have hpow : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
    apply (Complex.cpow_ne_zero_iff_of_exponent_ne_zero _).mpr
    · exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    · intro h
      have := congrArg Complex.re h
      simp at this
      linarith
  have hcos : Complex.cos (Real.pi * w / 2) = 0 := by
    have := hfe.symm
    simp only [mul_eq_zero, hzw, hGw, hpow, two_ne_zero, or_false, false_or] at this
    exact this
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hwk : w = 2 * k + 1 := by
    have := hk
    field_simp at this
    linear_combination this
  have hsk : s = -2 * k := by
    have : s = 1 - w := by simp [hw]
    rw [this, hwk]; ring
  have hkre : (k : ℝ) ≥ 0 := by
    have := congrArg Complex.re hsk
    simp at this
    linarith
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_zero] at hsk
    exact hs0 hsk
  have hk1 : 1 ≤ k := by
    have : (0 : ℤ) ≤ k := by exact_mod_cast hkre
    omega
  refine ⟨(k - 1).toNat, ?_⟩
  rw [hsk]
  have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
  have hc : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
    have := congrArg (fun z : ℤ => (z : ℂ)) this
    push_cast at this
    exact_mod_cast this
  rw [hc]; ring

/-- **R0b.** `GRHDirichlet` implies Mathlib's `RiemannHypothesis` (take `χ` the character mod 1,
whose `L`-function is `ζ`). -/
theorem riemannHypothesis_of_GRHDirichlet (h : GRHDirichlet) : RiemannHypothesis := by
  intro s hs htriv _hs1
  have hre1 : s.re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hs
  have hre0 : 0 < s.re := by
    by_contra hle
    exact htriv (riemannZeta_trivial_of_re_nonpos hs (not_lt.mp hle))
  exact h 1 (1 : DirichletCharacter ℂ 1) s
    (by rwa [DirichletCharacter.LFunction_modOne_eq]) hre0 hre1

/-! ## Row 337 — the all-characters form is the primitive form -/

/-- GRH for PRIMITIVE Dirichlet characters only. -/
def GRHPrimitive : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ s : ℂ,
    DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- **`GRHDirichlet` is no stronger than its primitive form.** An imprimitive `L(s, χ)` is
`L(s, χ*) · ∏_{p ∣ N} (1 − χ*(p) p^{−s})` (`LFunction_changeLevel`), and in the open strip each
factor is nonzero because `‖χ*(p) p^{−s}‖ ≤ p^{−re s} < 1`. -/
theorem grhDirichlet_iff_primitive : GRHDirichlet ↔ GRHPrimitive := by
  constructor
  · intro h N _ χ _ s
    exact h N χ s
  · intro h N _ χ s hs h0 h1
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hs1 : s ≠ 1 := by
      rintro rfl
      simp at h1
    rw [← χ.changeLevel_primitiveCharacter,
      DirichletCharacter.LFunction_changeLevel _ _ (Or.inr hs1)] at hs
    rcases mul_eq_zero.mp hs with h' | h'
    · exact h _ _ χ.primitiveCharacter_isPrimitive s h' h0 h1
    · exfalso
      obtain ⟨p, hp, hp0⟩ := Finset.prod_eq_zero_iff.mp h'
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hx : χ.primitiveCharacter p * (p : ℂ) ^ (-s) = 1 := by linear_combination -hp0
      have hn := congrArg norm hx
      rw [norm_mul, norm_one] at hn
      have hA : ‖χ.primitiveCharacter p‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
      have hB : ‖(p : ℂ) ^ (-s)‖ < 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re]
        exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by linarith)
      nlinarith [norm_nonneg (χ.primitiveCharacter p), norm_nonneg ((p : ℂ) ^ (-s))]

end Salt.RH
