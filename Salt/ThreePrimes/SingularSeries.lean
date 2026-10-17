/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude

Proofs in this file are adapted from gersh/ternary-goldbach-lean,
commit 27df23af6a712895f22204d0d81102baa74f0ebe,
Math/Problems/TernaryGoldbach/CircleMethodDecomposition/Core.lean and
Math/Problems/TernaryGoldbach/Core/Lemmas.lean,
Copyright (c) 2026 Gershon Bialer, released under Apache 2.0.
-/
import Mathlib
import Salt.ThreePrimes.Ramanujan

/-!
# Three primes: the singular series

These are lemmas L11–L13 of the three-primes plan (`docs/plans/three-primes-PLAN.md`, Steps 4
and 5).

When the major arcs are cubed and integrated, the arc at `a/q` contributes
`(μ(q)/φ(q))³ e(−Na/q)` times the singular integral. Summing over the `a` coprime to `q` turns the
phases into the Ramanujan sum `c_q(N)`, and `μ(q)³ = μ(q)`. Summing over `q` gives the **singular
series**

  `𝔖(N) = Σ_{q ≥ 1} μ(q) c_q(N) / φ(q)³`,

the arithmetic density of representations of `N` as a sum of three primes. This file shows what
the main term needs from it.

* **It converges absolutely.** Its `q`-th term is at most `μ(q)²/φ(q)²` in size, by the trivial
  bound `|c_q(N)| ≤ φ(q)`, and `Σ_q μ(q)²/φ(q)²` converges.
* **It is an Euler product.** The term is multiplicative in `q`: `μ` and `φ` are, and so is `c_q(N)`
  (`ramanujanSum_mul_of_coprime`). It also vanishes unless `q` is squarefree. So the series is a
  product over primes of `1 + μ(p) c_p(N)/φ(p)³`, and with `c_p(N) = p − 1` or `−1` that factor is
  `1 − 1/(p−1)²` if `p ∣ N` and `1 + 1/(p−1)³` if `p ∤ N`.
* **It vanishes for even `N` and is bounded below for odd `N`.** At `p = 2` the factor is `0` when
  `2 ∣ N`, which is the parity obstruction: three odd primes have an odd sum. When `N` is odd that
  factor is `2`, and every other factor is at least `1 − 1/(p−1)² ≥ 3/4`. Their product converges,
  so it is at least a constant `c₀ > 0` that does not depend on `N`. This is the only place in the
  proof that uses `N` odd.

The tail `Σ_{q > P}` that completes the truncated series (plan, Step 4b) is bounded where it is
used, with the major arcs.
-/

namespace Salt.ThreePrimes

open ArithmeticFunction

/-- **The `q`-th term of the singular series**, `μ(q) c_q(N) / φ(q)³`. -/
noncomputable def singularTerm (N q : ℕ) : ℂ :=
  ((moebius q : ℂ) / (Nat.totient q : ℂ) ^ 3) * ramanujanSum q N

/-- **The singular series** `𝔖(N) = Σ_q μ(q) c_q(N) / φ(q)³`. -/
noncomputable def singularSeries (N : ℕ) : ℂ :=
  ∑' q : ℕ, singularTerm N q

/-- **The local factor at a prime `p`**: `1 − 1/(p−1)²` if `p ∣ N`, and `1 + 1/(p−1)³` otherwise. At
`p = 2` it is `0` for even `N` and `2` for odd `N`. -/
noncomputable def localFactor (N p : ℕ) : ℝ :=
  if p ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 + 1 / ((p : ℝ) - 1) ^ 3

/-- The phase `e(k)` at a natural number `k` is `1`. -/
theorem eR_natCast_eq_one (k : ℕ) : Salt.ExpSum.eR (k : ℝ) = 1 := by
  rw [Salt.ExpSum.eR, show 2 * (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ)
      = (k : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_nat_mul_two_pi_mul_I k

/-- The phase `e(nx/M)` depends only on `x mod M`. -/
theorem eR_mod_eq {M : ℕ} (hM : 0 < M) (n x : ℕ) :
    Salt.ExpSum.eR ((n : ℝ) * ((x % M : ℕ) : ℝ) / M) = Salt.ExpSum.eR ((n : ℝ) * x / M) := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hx : (x : ℝ) = M * ((x / M : ℕ) : ℝ) + ((x % M : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod x M).symm
  have h : (n : ℝ) * x / M = (n : ℝ) * ((x % M : ℕ) : ℝ) / M + ((n * (x / M) : ℕ) : ℝ) := by
    rw [hx, Nat.cast_mul]
    field_simp
    ring
  rw [h, Salt.ExpSum.eR_add, eR_natCast_eq_one, mul_one]

/-- The phases multiply as the Chinese remainder theorem predicts:
`e(na/q₁) e(nb/q₂) = e(n(aq₂ + bq₁)/(q₁q₂))`. -/
theorem eR_mul_crt {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (n a b : ℕ) :
    Salt.ExpSum.eR ((n : ℝ) * a / q₁) * Salt.ExpSum.eR ((n : ℝ) * b / q₂)
      = Salt.ExpSum.eR ((n : ℝ) * ((a * q₂ + b * q₁ : ℕ) : ℝ) / ((q₁ * q₂ : ℕ) : ℝ)) := by
  have h₁ : (q₁ : ℝ) ≠ 0 := by exact_mod_cast hq₁.ne'
  have h₂ : (q₂ : ℝ) ≠ 0 := by exact_mod_cast hq₂.ne'
  rw [← Salt.ExpSum.eR_add]
  congr 1
  push_cast
  field_simp

/-- The Chinese-remainder map `(a, b) ↦ (aq₂ + bq₁) mod q₁q₂`, which pairs a residue mod `q₁` and a
residue mod `q₂` with a residue mod `q₁q₂`. -/
def crtPair (q₁ q₂ : ℕ) (p : ℕ × ℕ) : ℕ := (p.1 * q₂ + p.2 * q₁) % (q₁ * q₂)

/-- The Chinese-remainder map sends a pair of reduced residues to a reduced residue. -/
theorem crtPair_mem {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hcop : q₁.Coprime q₂)
    {p : ℕ × ℕ}
    (hp : p ∈ ((Finset.range q₁).filter (fun a => Nat.Coprime q₁ a)) ×ˢ
        ((Finset.range q₂).filter (fun b => Nat.Coprime q₂ b))) :
    crtPair q₁ q₂ p ∈ (Finset.range (q₁ * q₂)).filter (fun x => Nat.Coprime (q₁ * q₂) x) := by
  rcases p with ⟨a, b⟩
  simp only [crtPair, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hp ⊢
  refine ⟨Nat.mod_lt _ (Nat.mul_pos hq₁ hq₂), ?_⟩
  have hExpr : (a * q₂ + b * q₁).Coprime (q₁ * q₂) := by
    rw [Nat.coprime_mul_iff_right]
    constructor
    · rw [Nat.add_coprime_iff_left (show q₁ ∣ b * q₁ from ⟨b, by rw [mul_comm]⟩),
        Nat.coprime_mul_iff_left]
      exact ⟨hp.1.2.symm, hcop.symm⟩
    · rw [Nat.add_coprime_iff_right (show q₂ ∣ a * q₂ from ⟨a, by rw [mul_comm]⟩),
        Nat.coprime_mul_iff_left]
      exact ⟨hp.2.2.symm, hcop⟩
  have hmod := Nat.mod_modEq (a * q₂ + b * q₁) (q₁ * q₂)
  exact Nat.Coprime.symm (Nat.coprime_iff_gcd_eq_one.mpr (by
    rw [hmod.gcd_eq]; exact Nat.coprime_iff_gcd_eq_one.mp hExpr))

/-- The Chinese-remainder map is injective on pairs of residues `a < q₁`, `b < q₂`. -/
theorem crtPair_injOn {q₁ q₂ : ℕ} (hcop : q₁.Coprime q₂) :
    Set.InjOn (crtPair q₁ q₂)
      ((((Finset.range q₁).filter (fun a => Nat.Coprime q₁ a)) ×ˢ
        ((Finset.range q₂).filter (fun b => Nat.Coprime q₂ b)) : Finset (ℕ × ℕ)) :
          Set (ℕ × ℕ)) := by
  intro x hx y hy hxy
  rcases x with ⟨a, b⟩
  rcases y with ⟨a', b'⟩
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_range] at hx hy
  have hmodeqM : a * q₂ + b * q₁ ≡ a' * q₂ + b' * q₁ [MOD q₁ * q₂] := hxy
  have hmodeq1 : a * q₂ + b * q₁ ≡ a' * q₂ + b' * q₁ [MOD q₁] :=
    hmodeqM.of_dvd (dvd_mul_right q₁ q₂)
  have htail1 : b * q₁ ≡ b' * q₁ [MOD q₁] :=
    (Nat.modEq_zero_iff_dvd.mpr ⟨b, by rw [mul_comm]⟩).trans
      (Nat.modEq_zero_iff_dvd.mpr ⟨b', by rw [mul_comm]⟩).symm
  have ha_modeq : a ≡ a' [MOD q₁] :=
    Nat.ModEq.cancel_right_of_coprime (Nat.coprime_iff_gcd_eq_one.mp hcop)
      (htail1.add_right_cancel hmodeq1)
  have haeq : a = a' := Nat.ModEq.eq_of_lt_of_lt ha_modeq hx.1.1 hy.1.1
  have hmodeq2 : a * q₂ + b * q₁ ≡ a' * q₂ + b' * q₁ [MOD q₂] :=
    hmodeqM.of_dvd (by rw [mul_comm]; exact dvd_mul_right q₂ q₁)
  have htail2 : a * q₂ ≡ a' * q₂ [MOD q₂] :=
    (Nat.modEq_zero_iff_dvd.mpr ⟨a, by rw [mul_comm]⟩).trans
      (Nat.modEq_zero_iff_dvd.mpr ⟨a', by rw [mul_comm]⟩).symm
  have hb_modeq : b ≡ b' [MOD q₂] :=
    Nat.ModEq.cancel_right_of_coprime (Nat.coprime_iff_gcd_eq_one.mp hcop.symm)
      (htail2.add_left_cancel hmodeq2)
  have hbeq : b = b' := Nat.ModEq.eq_of_lt_of_lt hb_modeq hx.2.1 hy.2.1
  subst haeq
  subst hbeq
  rfl

/-- **The Ramanujan sum is multiplicative in the modulus:** `c_{q₁q₂}(n) = c_{q₁}(n) c_{q₂}(n)` when
`gcd(q₁, q₂) = 1`. By the Chinese remainder theorem, a residue coprime to `q₁q₂` is a pair of
residues coprime to `q₁` and to `q₂`, and the phase `e(na/(q₁q₂))` factors accordingly. -/
theorem ramanujanSum_mul_of_coprime {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hcop : Nat.Coprime q₁ q₂) (n : ℕ) :
    ramanujanSum (q₁ * q₂) n = ramanujanSum q₁ n * ramanujanSum q₂ n := by
  classical
  unfold ramanujanSum
  set s₁ := (Finset.range q₁).filter (fun a => Nat.Coprime q₁ a) with hs₁
  set s₂ := (Finset.range q₂).filter (fun b => Nat.Coprime q₂ b) with hs₂
  set t := (Finset.range (q₁ * q₂)).filter (fun x => Nat.Coprime (q₁ * q₂) x) with ht
  have hinj : Set.InjOn (crtPair q₁ q₂) ((s₁ ×ˢ s₂ : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) :=
    crtPair_injOn hcop
  have hcard : (s₁ ×ˢ s₂).card = t.card := by
    rw [Finset.card_product, hs₁, hs₂, ht, card_coprime_filter, card_coprime_filter,
      card_coprime_filter, Nat.totient_mul hcop]
  have himg : (s₁ ×ˢ s₂).image (crtPair q₁ q₂) = t := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      exact crtPair_mem hq₁ hq₂ hcop hp
    · rw [Finset.card_image_of_injOn hinj]
      exact hcard.ge
  rw [← himg, Finset.sum_image hinj, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun p _ => ?_
  rcases p with ⟨a, b⟩
  simp only [crtPair]
  rw [eR_mod_eq (Nat.mul_pos hq₁ hq₂), eR_mul_crt hq₁ hq₂]

/-- **The size of a term:** `|μ(q) c_q(N)/φ(q)³| ≤ μ(q)²/φ(q)²`, from `|c_q(N)| ≤ φ(q)` and
`|μ(q)| = μ(q)²`. (Both sides are `0` at `q = 0`.) -/
theorem norm_singularTerm_le (N q : ℕ) :
    ‖singularTerm N q‖ ≤ ((moebius q : ℝ)) ^ 2 / (Nat.totient q : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [singularTerm]
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hμ : ‖(moebius q : ℂ)‖ = (moebius q : ℝ) ^ 2 := by
    rw [Complex.norm_intCast]
    by_cases h0 : moebius q = 0
    · simp [h0]
    · rcases moebius_ne_zero_iff_eq_or.mp h0 with h | h <;> simp [h]
  calc ‖singularTerm N q‖
      = (moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 3 * ‖ramanujanSum q N‖ := by
        rw [singularTerm, norm_mul, norm_div, norm_pow, hμ, Complex.norm_natCast]
    _ ≤ (moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 3 * (Nat.totient q : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_ramanujanSum_le q N) (by positivity)
    _ = (moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 := by
        field_simp

/-- The term at `q = 1` is `1`. -/
theorem singularTerm_one (N : ℕ) : singularTerm N 1 = 1 := by
  simp [singularTerm, ramanujanSum, Salt.ExpSum.eR]

/-- The term is multiplicative in `q` on coprime arguments, since `μ`, `φ` and `c_q(N)` are. -/
theorem singularTerm_mul (N : ℕ) {q₁ q₂ : ℕ} (hcop : q₁.Coprime q₂) :
    singularTerm N (q₁ * q₂) = singularTerm N q₁ * singularTerm N q₂ := by
  rcases Nat.eq_zero_or_pos q₁ with rfl | hq₁
  · simp [singularTerm]
  rcases Nat.eq_zero_or_pos q₂ with rfl | hq₂
  · simp [singularTerm]
  have hmu : moebius (q₁ * q₂) = moebius q₁ * moebius q₂ :=
    isMultiplicative_moebius.map_mul_of_coprime hcop
  have h₁ : (Nat.totient q₁ : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq₁).ne'
  have h₂ : (Nat.totient q₂ : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq₂).ne'
  unfold singularTerm
  rw [ramanujanSum_mul_of_coprime hq₁ hq₂ hcop, hmu, Nat.totient_mul hcop]
  push_cast
  field_simp

/-- At a prime `p` the term is the local factor minus one: `−1/(p−1)²` if `p ∣ N`, and
`1/(p−1)³` otherwise. -/
theorem singularTerm_prime {N p : ℕ} (hp : p.Prime) :
    singularTerm N p = ((localFactor N p - 1 : ℝ) : ℂ) := by
  have hd : ((p : ℂ) - 1) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.one_lt.ne')
  unfold singularTerm localFactor
  rw [ramanujanSum_prime hp, moebius_apply_prime hp, Nat.totient_prime hp]
  split_ifs with h
  · push_cast [Nat.cast_sub hp.one_le]
    field_simp
    ring
  · push_cast [Nat.cast_sub hp.one_le]
    field_simp
    ring

/-- At a prime power `p^k` with `k ≥ 2` the term vanishes, because `μ(p^k) = 0`. -/
theorem singularTerm_prime_pow_eq_zero {N p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    singularTerm N (p ^ k) = 0 := by
  unfold singularTerm
  rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
  simp

/-- The local factor is `1 + O(1/p²)`: `|(local factor at p) − 1| ≤ 4/p²`. -/
theorem abs_localFactor_sub_one_le (N : ℕ) {p : ℕ} (hp : p.Prime) :
    |localFactor N p - 1| ≤ 4 / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hd : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have hsq : 1 / ((p : ℝ) - 1) ^ 2 ≤ 4 / (p : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  unfold localFactor
  split_ifs with h
  · rw [show 1 - 1 / ((p : ℝ) - 1) ^ 2 - 1 = -(1 / ((p : ℝ) - 1) ^ 2) by ring, abs_neg,
      abs_of_pos (by positivity)]
    exact hsq
  · rw [add_sub_cancel_left, abs_of_pos (by positivity)]
    refine le_trans ?_ hsq
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- `Σ_p c/p²` over the primes converges. -/
theorem summable_div_sq_primes (c : ℝ) :
    Summable (fun p : Nat.Primes => c / ((p : ℕ) : ℝ) ^ 2) := by
  have h := ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left c).comp_injective
    (Subtype.val_injective (p := Nat.Prime))
  refine h.congr fun p => ?_
  simp [Function.comp, div_eq_mul_inv]

/-- **The singular series converges absolutely.** -/
theorem summable_norm_singularTerm (N : ℕ) : Summable (fun q : ℕ => ‖singularTerm N q‖) := by
  classical
  set g : ℕ → ℝ := fun q => ‖singularTerm N q‖ with hg
  have hg0 : ∀ q, 0 ≤ g q := fun q => norm_nonneg _
  have hg1 : g 1 = 1 := by simp [hg, singularTerm_one]
  have hgz : g 0 = 0 := by simp [hg, singularTerm]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → g (m * n) = g m * g n := by
    intro m n h
    simp only [hg, singularTerm_mul N h, norm_mul]
  have hzero : ∀ {p : ℕ}, p.Prime → ∀ k ∉ ({0, 1} : Finset ℕ), g (p ^ k) = 0 := by
    intro p hp k hk
    have : 2 ≤ k := by simp at hk; omega
    simp [hg, singularTerm_prime_pow_eq_zero hp this]
  have hloc : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => ‖g (p ^ k)‖) := by
    intro p hp
    apply summable_of_ne_finset_zero (s := {0, 1})
    intro k hk
    simp [hzero hp k hk]
  have hlocsum : ∀ {p : ℕ}, p.Prime → ∑' k : ℕ, g (p ^ k) ≤ 1 + 4 / (p : ℝ) ^ 2 := by
    intro p hp
    rw [tsum_eq_sum (s := {0, 1}) (hzero hp), Finset.sum_pair (by norm_num), pow_zero,
      pow_one, hg1]
    have := abs_localFactor_sub_one_le N hp
    simp only [hg, singularTerm_prime hp, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hS : Summable (fun n : ℕ => 4 / (n : ℝ) ^ 2) :=
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 4).congr fun n => by ring
  refine summable_of_sum_range_le hg0 (c := Real.exp (∑' n : ℕ, 4 / (n : ℝ) ^ 2))
    (fun M => ?_)
  obtain ⟨-, hsum⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := g) hg1 hmul hloc M
  calc ∑ q ∈ Finset.range M, g q
      = ∑ q ∈ (Finset.range M).filter (· ∈ M.smoothNumbers), g q := by
        rw [Finset.sum_filter_of_ne]
        intro q hq hne
        have hq0 : q ≠ 0 := by rintro rfl; exact hne hgz
        exact Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hq0) (Finset.mem_range.mp hq)
    _ = ∑ q ∈ (Finset.range M).subtype (· ∈ M.smoothNumbers), g q :=
        (Finset.sum_subtype_eq_sum_filter _).symm
    _ ≤ ∏ p ∈ M.primesBelow, ∑' k : ℕ, g (p ^ k) :=
        sum_le_hasSum _ (fun _ _ => hg0 _) hsum
    _ ≤ ∏ p ∈ M.primesBelow, Real.exp (4 / (p : ℝ) ^ 2) := by
        apply Finset.prod_le_prod (fun p _ => tsum_nonneg fun k => hg0 _)
        intro p hp
        refine (hlocsum (Nat.mem_primesBelow.mp hp).2).trans ?_
        linarith [Real.add_one_le_exp (4 / (p : ℝ) ^ 2)]
    _ = Real.exp (∑ p ∈ M.primesBelow, 4 / (p : ℝ) ^ 2) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' n : ℕ, 4 / (n : ℝ) ^ 2) :=
        Real.exp_le_exp.mpr (hS.sum_le_tsum _ (fun n _ => by positivity))

/-- The deviations `(local factor at p) − 1` are summable over the primes, being `O(1/p²)`. -/
theorem summable_localFactor_sub_one (N : ℕ) :
    Summable (fun p : Nat.Primes => localFactor N p - 1) :=
  Summable.of_norm_bounded (summable_div_sq_primes 4) (fun p => by
    rw [Real.norm_eq_abs]; exact abs_localFactor_sub_one_le N p.prop)

/-- **The Euler product:** `𝔖(N) = Π_p (local factor at p)`. -/
theorem singularSeries_eq_tprod (N : ℕ) :
    singularSeries N = ((∏' p : Nat.Primes, localFactor N p : ℝ) : ℂ) := by
  have hmult : Multipliable (fun p : Nat.Primes => localFactor N p) :=
    (Real.multipliable_one_add_of_summable (summable_localFactor_sub_one N)).congr
      (fun p => by ring)
  unfold singularSeries
  rw [← EulerProduct.eulerProduct_tprod (f := singularTerm N) (singularTerm_one N)
    (singularTerm_mul N) (summable_norm_singularTerm N) (by simp [singularTerm])]
  have hmap := Multipliable.map_tprod hmult Complex.ofRealHom Complex.continuous_ofReal
  simp only [Complex.ofRealHom_eq_coe] at hmap
  rw [hmap]
  refine tprod_congr fun p => ?_
  have hzero : ∀ k ∉ ({0, 1} : Finset ℕ), singularTerm N ((p : ℕ) ^ k) = 0 := by
    intro k hk
    have : 2 ≤ k := by simp at hk; omega
    exact singularTerm_prime_pow_eq_zero p.prop this
  rw [tsum_eq_sum hzero, Finset.sum_pair (by norm_num), pow_zero, pow_one, singularTerm_one,
    singularTerm_prime p.prop]
  push_cast
  ring

/-- **For even `N` the singular series vanishes**, through its factor at `p = 2`. -/
theorem singularSeries_eq_zero_of_even {N : ℕ} (hN : Even N) : singularSeries N = 0 := by
  rw [singularSeries_eq_tprod, tprod_of_exists_eq_zero ⟨⟨2, Nat.prime_two⟩, ?_⟩,
    Complex.ofReal_zero]
  norm_num [localFactor, even_iff_two_dvd.mp hN]

/-- A prime dividing an odd number is at least `3`. -/
theorem three_le_of_dvd_odd {N p : ℕ} (hN : Odd N) (hp : p.Prime) (hpN : p ∣ N) : 3 ≤ p := by
  have h2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr hpN)
  have := hp.two_le
  omega

/-- For odd `N` every local factor is positive: at least `3/4` if `p ∣ N`, above `1` otherwise. -/
theorem localFactor_pos {N p : ℕ} (hN : Odd N) (hp : p.Prime) : 0 < localFactor N p := by
  unfold localFactor
  split_ifs with h
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_dvd_odd hN hp h
    have hu : 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
      rw [div_lt_one (by nlinarith)]
      nlinarith
    linarith
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have : 0 < 1 / ((p : ℝ) - 1) ^ 3 := by
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    linarith

/-- For odd `N` the logarithm of a local factor is at least `−8/p²`. -/
theorem neg_le_log_localFactor {N p : ℕ} (hN : Odd N) (hp : p.Prime) :
    -(8 / (p : ℝ) ^ 2) ≤ Real.log (localFactor N p) := by
  unfold localFactor
  split_ifs with h
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast three_le_of_dvd_odd hN hp h
    generalize hu_def : 1 / ((p : ℝ) - 1) ^ 2 = u
    have hd : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hu0 : 0 < u := by rw [← hu_def]; positivity
    have hu4 : u ≤ 4 / (p : ℝ) ^ 2 := by
      rw [← hu_def, div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith
    have hu14 : u ≤ 1 / 4 := by
      rw [← hu_def, div_le_div_iff₀ (by nlinarith) (by norm_num)]
      nlinarith
    have hinv : (1 - u)⁻¹ ≤ 1 + 2 * u := by
      rw [inv_le_iff_one_le_mul₀ (by linarith)]
      nlinarith
    have hlog := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 - u)
    have h1 : -(8 / (p : ℝ) ^ 2) ≤ -(2 * u) := by
      rw [show 8 / (p : ℝ) ^ 2 = 2 * (4 / (p : ℝ) ^ 2) by ring]
      linarith
    have h2 : -(2 * u) ≤ 1 - (1 - u)⁻¹ := by linarith
    exact h1.trans (h2.trans hlog)
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have h1 : 0 ≤ 1 / ((p : ℝ) - 1) ^ 3 := by
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + 1 / ((p : ℝ) - 1) ^ 3)
    have : 0 ≤ 8 / (p : ℝ) ^ 2 := by positivity
    linarith

/-- **For odd `N` the singular series is bounded below** by a constant `c₀ > 0` independent of
`N`. -/
theorem singularSeries_lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ N : ℕ, Odd N → c₀ ≤ ∏' p : Nat.Primes, localFactor N p := by
  refine ⟨Real.exp (-∑' p : Nat.Primes, 8 / ((p : ℕ) : ℝ) ^ 2), Real.exp_pos _, fun N hN => ?_⟩
  have hpos : ∀ p : Nat.Primes, 0 < localFactor N p := fun p => localFactor_pos hN p.prop
  have hlog : Summable (fun p : Nat.Primes => Real.log (localFactor N p)) :=
    (Real.summable_log_one_add_of_summable (summable_localFactor_sub_one N)).congr
      (fun p => by rw [add_sub_cancel])
  rw [← Real.rexp_tsum_eq_tprod hpos hlog, Real.exp_le_exp, ← tsum_neg]
  exact Summable.tsum_le_tsum (fun p => neg_le_log_localFactor hN p.prop)
    (summable_div_sq_primes 8).neg hlog

end Salt.ThreePrimes
