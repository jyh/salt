/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.MomentEigen
import Salt.Weil.CurveBridge
import Salt.Weil.MultiExtract
import Mathlib

/-!
# Weil track, node W-DESCENT — the Weil bound `‖S(a, b; p)‖ ≤ 2√p`

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder). The summit assembly: the four
landed faces compose into the Weil bound for Kloosterman sums.

* **The eigenvalue family** (`descentRoot`): for each nonzero twist `m ∈ 𝔽_p` the two local
  roots `α_m, β_m` of the twisted sum `S(m·a, m·b; p)`, indexed by `{m // m ≠ 0} × Bool`.
* **The power-sum identity** (`sum_descentRoot_pow`): for `n ≥ 1`,
  `∑_m (α_m^n + β_m^n) = #𝔽_{p^n}ˣ − #curve` — Theorem 6 per twist
  (`kloostermanMoment_eq_neg_localPowerSum`) glued to Corollary 3
  (`sum_kloostermanMoment_erase_zero_eq`).
* **The uniform bound** (`norm_sum_descentRoot_pow_le`): for `n ≥ 6` Theorem 7
  (`weil_stepanov`) applied to the Cor 3 curve `y² = (x^p − x)² − 4ab` bounds the identity's
  right side by `33p·(√p)^n`.
* **The descent** (`norm_localRoots_eq_sqrt`, `norm_kloosterman_le_two_sqrt`): the master
  extraction `forall_norm_le_of_powerSum_bound` forces `‖α_m‖, ‖β_m‖ ≤ √p`; Vieta
  (`localRootPair_mul`) upgrades to equality at `m = 1`; Vieta (`localRootPair_add`) converts
  back through `S(a, b; p) = −(α₁ + β₁)`, whence `‖S(a, b; p)‖ ≤ 2√p`.
-/

namespace Salt.Weil

open scoped BigOperators

section Descent

variable {p : ℕ} [Fact p.Prime]

/-- **The eigenvalue family of the descent.** For each nonzero twist `m` the two local roots
`α_m` (at `false`) and `β_m` (at `true`) of the twisted Kloosterman sum `S(m·a, m·b; p)`. -/
private noncomputable def descentRoot (a b : ZMod p) :
    {m : ZMod p // m ≠ 0} × Bool → ℂ
  | (m, false) => localAlpha (kloosterman ((m : ZMod p) * a) ((m : ZMod p) * b)).re p
  | (m, true) => localBeta (kloosterman ((m : ZMod p) * a) ((m : ZMod p) * b)).re p

private theorem descentRoot_false (a b : ZMod p) (m : {m : ZMod p // m ≠ 0}) :
    descentRoot a b (m, false)
      = localAlpha (kloosterman ((m : ZMod p) * a) ((m : ZMod p) * b)).re p := rfl

private theorem descentRoot_true (a b : ZMod p) (m : {m : ZMod p // m ≠ 0}) :
    descentRoot a b (m, true)
      = localBeta (kloosterman ((m : ZMod p) * a) ((m : ZMod p) * b)).re p := rfl

/-- **The power-sum identity.** For `n ≥ 1` the `n`-th power sum of the eigenvalue family is
the deviation of the Cor 3 curve count from `#𝔽_{p^n}ˣ`: Theorem 6 turns each
`α_m^n + β_m^n` into `−M_n(m·a, m·b)`, and Corollary 3 collapses the twisted-moment sum to
`#curve − #𝔽_{p^n}ˣ`. -/
private theorem sum_descentRoot_pow (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 1 ≤ n) :
    ∑ i, descentRoot a b i ^ n
      = (Fintype.card (GaloisField p n)ˣ : ℂ) - (pointCount (curvePoly a b n) : ℂ) := by
  have h1 : ∑ i, descentRoot a b i ^ n
      = -∑ m : {m : ZMod p // m ≠ 0},
          kloostermanMoment ((m : ZMod p) * a) ((m : ZMod p) * b) n := by
    rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Fintype.sum_bool, descentRoot_true, descentRoot_false]
    rw [kloostermanMoment_eq_neg_localPowerSum ((m : ZMod p) * a) ((m : ZMod p) * b)
      (mul_ne_zero m.2 ha) (mul_ne_zero m.2 hb) hn, neg_neg]
    unfold localPowerSum
    exact add_comm _ _
  have hsub : ∑ m : {m : ZMod p // m ≠ 0},
      kloostermanMoment ((m : ZMod p) * a) ((m : ZMod p) * b) n
        = ∑ m ∈ Finset.univ.erase (0 : ZMod p), kloostermanMoment (m * a) (m * b) n := by
    refine (Finset.sum_subtype (p := fun m : ZMod p => m ≠ 0)
      (Finset.univ.erase (0 : ZMod p)) (fun x => ?_)
      (fun m => kloostermanMoment (m * a) (m * b) n)).symm
    simp
  rw [h1, hsub, sum_kloostermanMoment_erase_zero_eq a b ha hb hp2 (by omega : n ≠ 0)]
  ring

/-- **The Weil–Stepanov numeric input, ℤ level.** For `n ≥ 6` and odd `p`, the deviation of
the Cor 3 curve count from `#𝔽_{p^n}ˣ` is at most `16p(√(p^n) + 1) + 1`: Theorem 7
(`weil_stepanov`) at `deg f = 2p` — its gate `16(2p)² = 64p² ≤ p^n` holds since `p ≥ 3` and
`n ≥ 6` — plus `1` for trading `p^n` against `#𝔽_{p^n}ˣ = p^n − 1`. -/
private theorem descent_int_bound (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 6 ≤ n) :
    |(Fintype.card (GaloisField p n)ˣ : ℤ) - (pointCount (curvePoly a b n) : ℤ)|
      ≤ 16 * (p : ℤ) * ((Nat.sqrt (p ^ n) : ℤ) + 1) + 1 := by
  have hp3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    omega
  have hn0 : n ≠ 0 := by omega
  have hcard : Fintype.card (GaloisField p n) = p ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p n hn0]
  have hdeg : (curvePoly a b n).natDegree = 2 * p := curvePoly_natDegree a b
  have hqodd : Odd (Fintype.card (GaloisField p n)) := by
    rw [hcard]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hm : 1 ≤ (curvePoly a b n).natDegree := by rw [hdeg]; omega
  have hq : 16 * (curvePoly a b n).natDegree ^ 2 ≤ Fintype.card (GaloisField p n) := by
    rw [hdeg, hcard]
    calc 16 * (2 * p) ^ 2 = 64 * p ^ 2 := by ring
      _ ≤ 3 ^ 4 * p ^ 2 := Nat.mul_le_mul (by norm_num) le_rfl
      _ ≤ p ^ 4 * p ^ 2 := Nat.mul_le_mul (Nat.pow_le_pow_left hp3 4) le_rfl
      _ = p ^ 6 := by ring
      _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
  have hws := weil_stepanov (curvePoly a b n) hqodd hm
    (curvePoly_coeff_zero_ne_zero a b ha hb hp2) (curvePoly_not_isSquare a b ha hb hp2) hq
  rw [hdeg, hcard] at hws
  have hpow1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hunits : (Fintype.card (GaloisField p n)ˣ : ℤ) = ((p ^ n : ℕ) : ℤ) - 1 := by
    rw [Fintype.card_units, hcard, Nat.cast_sub hpow1, Nat.cast_one]
  have h1 : (Fintype.card (GaloisField p n)ˣ : ℤ) - (pointCount (curvePoly a b n) : ℤ)
      = -(((pointCount (curvePoly a b n) : ℤ) - ((p ^ n : ℕ) : ℤ)) + 1) := by
    rw [hunits]; ring
  rw [h1, abs_neg]
  calc |((pointCount (curvePoly a b n) : ℤ) - ((p ^ n : ℕ) : ℤ)) + 1|
      ≤ |(pointCount (curvePoly a b n) : ℤ) - ((p ^ n : ℕ) : ℤ)| + |1| := abs_add_le _ _
    _ ≤ 8 * ((2 * p : ℕ) : ℤ) * ((Nat.sqrt (p ^ n) : ℤ) + 1) + 1 := by
        rw [abs_one]
        exact add_le_add hws le_rfl
    _ = 16 * (p : ℤ) * ((Nat.sqrt (p ^ n) : ℤ) + 1) + 1 := by push_cast; ring

/-- **The uniform bound (hbound).** For `n ≥ 6` the `n`-th power sum of the eigenvalue family
is bounded by `33p·(√p)^n`: the identity `sum_descentRoot_pow` feeds the ℤ-level
Weil–Stepanov bound, with `Nat.sqrt (p^n) ≤ (√p)^n` and the tail `16p + 1 ≤ 17p·(√p)^n`
absorbed into the constant `33p`. -/
private theorem norm_sum_descentRoot_pow_le (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (hp2 : p ≠ 2) : ∀ n : ℕ, 6 ≤ n →
    ‖∑ i, descentRoot a b i ^ n‖ ≤ 33 * (p : ℝ) * Real.sqrt (p : ℝ) ^ n := by
  intro n hn
  rw [sum_descentRoot_pow a b ha hb hp2 (by omega : 1 ≤ n)]
  have hzc : (Fintype.card (GaloisField p n)ˣ : ℂ) - (pointCount (curvePoly a b n) : ℂ)
      = ((((Fintype.card (GaloisField p n)ˣ : ℤ)
          - (pointCount (curvePoly a b n) : ℤ)) : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hzc, Complex.norm_intCast]
  have hR : |(((Fintype.card (GaloisField p n)ˣ : ℤ)
        - (pointCount (curvePoly a b n) : ℤ) : ℤ) : ℝ)|
      ≤ 16 * (p : ℝ) * ((Nat.sqrt (p ^ n) : ℝ) + 1) + 1 := by
    exact_mod_cast descent_int_bound a b ha hb hp2 hn
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hsqrt_pow : Real.sqrt (p : ℝ) ^ n = Real.sqrt ((p : ℝ) ^ n) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt (p : ℝ) ^ n)]
    congr 1
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt hp0]
  have hs_le : ((Nat.sqrt (p ^ n) : ℝ)) ≤ Real.sqrt (p : ℝ) ^ n := by
    rw [hsqrt_pow]
    have h := Real.nat_sqrt_le_real_sqrt (a := p ^ n)
    have hcast : (((p ^ n : ℕ) : ℝ)) = (p : ℝ) ^ n := by push_cast; ring
    rwa [hcast] at h
  have hone : (1 : ℝ) ≤ Real.sqrt (p : ℝ) ^ n := by
    refine one_le_pow₀ ?_
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hp1
  have hps : (p : ℝ) * (Nat.sqrt (p ^ n) : ℝ) ≤ (p : ℝ) * Real.sqrt (p : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left hs_le hp0
  have hpt : (p : ℝ) * 1 ≤ (p : ℝ) * Real.sqrt (p : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left hone hp0
  refine hR.trans ?_
  nlinarith [hps, hpt, hp1]

/-- **The extraction.** Every eigenvalue of the family has modulus `≤ √p`: the master lemma
`forall_norm_le_of_powerSum_bound` applied to the uniform bound, at `N₀ = 6`, `C = 33p`,
`ρ = √p`. -/
private theorem norm_descentRoot_le (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hp2 : p ≠ 2) :
    ∀ i, ‖descentRoot a b i‖ ≤ Real.sqrt (p : ℝ) :=
  forall_norm_le_of_powerSum_bound (descentRoot a b) (33 * (p : ℝ)) (Real.sqrt (p : ℝ))
    (Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)) 6
    (norm_sum_descentRoot_pow_le a b ha hb hp2)

/-- **The `m = 1` specialization.** Both local roots of `S(a, b; p)` itself have modulus
`≤ √p`. -/
private theorem norm_localRoots_le (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hp2 : p ≠ 2) :
    ‖localAlpha (kloosterman a b).re p‖ ≤ Real.sqrt (p : ℝ)
      ∧ ‖localBeta (kloosterman a b).re p‖ ≤ Real.sqrt (p : ℝ) := by
  have hα := norm_descentRoot_le a b ha hb hp2 (⟨1, one_ne_zero⟩, false)
  have hβ := norm_descentRoot_le a b ha hb hp2 (⟨1, one_ne_zero⟩, true)
  rw [descentRoot_false] at hα
  rw [descentRoot_true] at hβ
  exact ⟨by simpa using hα, by simpa using hβ⟩

end Descent

/-- **The eigenvalue equality** (the "Riemann hypothesis" for the Kloosterman local factor).
For an odd prime `p` and `a, b ≠ 0`, both local roots of `S(a, b; p)` lie exactly on the
circle `|z| = √p`: the extraction gives `≤ √p` for each, and Vieta's `α·β = p` forces
equality. -/
theorem norm_localRoots_eq_sqrt {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖localAlpha (kloosterman a b).re p‖ = Real.sqrt p
      ∧ ‖localBeta (kloosterman a b).re p‖ = Real.sqrt p := by
  obtain ⟨hα, hβ⟩ := norm_localRoots_le a b ha hb hp2
  refine norm_eq_sqrt_of_pair_of_le _ _ (p : ℝ) (by positivity) ?_ hα hβ
  rw [localRootPair_mul]
  exact Complex.norm_natCast p

/-- **The Weil bound** (Harcos Theorem 1; Weil 1948). For an odd prime `p` and `a, b ≠ 0`,
the Kloosterman sum satisfies `‖S(a, b; p)‖ ≤ 2√p`: the two local roots have modulus exactly
`√p` (`norm_localRoots_eq_sqrt`), and their sum is `−S(a, b; p)` by Vieta plus reality. -/
theorem norm_kloosterman_le_two_sqrt {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖kloosterman a b‖ ≤ 2 * Real.sqrt p := by
  obtain ⟨hα, hβ⟩ := norm_localRoots_eq_sqrt hp2 a b ha hb
  have hreal : kloosterman a b = ((kloosterman a b).re : ℂ) := by
    refine Complex.ext ?_ ?_
    · simp
    · simp [kloosterman_im a b]
  have hnorm : ‖kloosterman a b‖
      = ‖localAlpha (kloosterman a b).re p + localBeta (kloosterman a b).re p‖ := by
    rw [localRootPair_add, norm_neg, ← hreal]
  rw [hnorm]
  exact norm_add_le_two_mul_sqrt _ _ _ hα.le hβ.le

/-- **The Weil bound, all primes.** The `hp2`-free version: at `p = 2` the trivial bound
`‖S‖ ≤ p − 1 = 1 ≤ 2√2` (`norm_kloosterman_le_sub_one`) already suffices. -/
theorem norm_kloosterman_le_two_sqrt' {p : ℕ} [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖kloosterman a b‖ ≤ 2 * Real.sqrt p := by
  by_cases hp2 : p = 2
  · subst hp2
    refine (norm_kloosterman_le_sub_one a b).trans ?_
    have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by norm_num)
    push_cast
    linarith [h1]
  · exact norm_kloosterman_le_two_sqrt hp2 a b ha hb

end Salt.Weil
