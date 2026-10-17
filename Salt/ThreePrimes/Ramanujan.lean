/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude

The proof of `ramanujanSum_of_coprime` and its helper lemmas (`geom_sum_root_of_unity`,
`sum_filter_dvd_reindex`, `moebius_sum_indicator`, `divisors_gcd_eq_filter`,
`coprime_indicator`, `inner_sum_value`) are adapted from gersh/ternary-goldbach-lean,
commit 27df23af6a712895f22204d0d81102baa74f0ebe,
ext/analytic_nt/AnalyticNT/MeanValue/RamanujanSumCoprimeValue.lean,
Copyright (c) 2026 Gershon Bialer, released under Apache 2.0.
-/
import Mathlib
import Salt.ExpSum.Basic

/-!
# Three primes: Ramanujan sums

This is lemma L5 of the three-primes plan (`docs/plans/three-primes-PLAN.md`).

On a major arc, near a fraction `a/q`, the sum `S(α) = Σ_{n ≤ N} Λ(n) e(nα)` is split by the residue
of `n` mod `q`. Siegel–Walfisz says the primes are spread evenly over the `φ(q)` residues coprime to
`q`, each carrying a share `1/φ(q)`. What remains is the phase each residue `r` contributes,
`e(ar/q)`, summed over the residues coprime to `q`. That sum is a **Ramanujan sum**,

  `c_q(n) = Σ_{0 ≤ a < q, gcd(a, q) = 1} e(na/q)`,

and its value at a coprime argument is the Möbius function: `c_q(a) = μ(q)` when `gcd(a, q) = 1`.
This is where `μ(q)/φ(q)` comes from on a major arc (plan, Step 3b).

The same sum appears a second time, at the argument `N`, in the singular series
`𝔖(N) = Σ_q μ(q) c_q(N) / φ(q)³` (plan, Steps 4 and 5). There we need its trivial bound
`|c_q(N)| ≤ φ(q)` (Step 4b) and its value at a prime, `c_p(N) = p − 1` if `p ∣ N` and `−1`
otherwise (Step 5).

**Why `c_q(n) = μ(q)` when `gcd(q, n) = 1`.** Write `ω = e(1/q)`, a primitive `q`-th root of unity,
so the summand is `ω^{na}`. Detect the condition `gcd(a, q) = 1` with Möbius,
`Σ_{e ∣ gcd(q, a)} μ(e) = [gcd(q, a) = 1]`, and swap the two sums. For each divisor `e` of `q` the
inner sum runs over the multiples `a = eb` with `b < q/e`. It is a complete geometric sum of the
root of unity `ω^{ne}`, so it is `q/e` if `ω^{ne} = 1` and `0` otherwise. Since `gcd(q, n) = 1`,
`ω^{ne} = 1` only when `e = q`, and there the inner sum is `1`. Only the term `e = q` survives, and
it is `μ(q)`.
-/

namespace Salt.ThreePrimes

open Finset ArithmeticFunction
open Salt.ExpSum (eR norm_eR)

/-- **The Ramanujan sum** `c_q(n) = Σ_{0 ≤ a < q, gcd(q, a) = 1} e(na/q)`: the phases of the
residues coprime to `q`, at frequency `n`. -/
noncomputable def ramanujanSum (q n : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime q a), eR ((n : ℝ) * a / q)

/-- The primitive `q`-th root of unity `ω = e(1/q)`. -/
noncomputable def om (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (q : ℂ))

/-- A complete geometric sum of a root of unity: if `x ^ M = 1`, then `Σ_{a < M} x ^ a` is `M` when
`x = 1` and `0` otherwise. -/
theorem geom_sum_root_of_unity (x : ℂ) (M : ℕ) (hxM : x ^ M = 1) :
    (∑ a ∈ range M, x ^ a) = if x = 1 then (M : ℂ) else 0 := by
  by_cases hx : x = 1
  · simp [hx]
  · rw [if_neg hx, geom_sum_eq hx, hxM, sub_self, zero_div]

/-- The multiples of `e` below `q` (for `e ∣ q`) are `e·b` for `b < q/e`: reindex the sum. -/
theorem sum_filter_dvd_reindex {M : Type*} [AddCommMonoid M]
    (e q : ℕ) (he : 1 ≤ e) (heq : e ∣ q) (f : ℕ → M) :
    (∑ a ∈ (range q).filter (fun a => e ∣ a), f a) = ∑ b ∈ range (q / e), f (e * b) := by
  have hset : (range q).filter (fun a => e ∣ a) = (range (q / e)).image (fun b => e * b) := by
    ext a
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨halt, b, rfl⟩
      refine ⟨b, ?_, rfl⟩
      have hq' : e * (q / e) = q := Nat.mul_div_cancel' heq
      have : e * b < e * (q / e) := by rw [hq']; exact halt
      exact Nat.lt_of_mul_lt_mul_left this
    · rintro ⟨b, hb, rfl⟩
      refine ⟨?_, Dvd.intro b rfl⟩
      have hq' : e * (q / e) = q := Nat.mul_div_cancel' heq
      calc e * b < e * (q / e) := (Nat.mul_lt_mul_left he).mpr hb
        _ = q := hq'
  rw [hset, sum_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left he h

/-- Möbius detects `1`: for `g ≠ 0`, `Σ_{e ∣ g} μ(e) = [g = 1]`. -/
theorem moebius_sum_indicator (g : ℕ) (_hg : g ≠ 0) :
    (∑ e ∈ g.divisors, (moebius e : ℂ)) = if g = 1 then 1 else 0 := by
  have key : ((moebius : ArithmeticFunction ℂ) * (zeta : ArithmeticFunction ℂ)) g
      = (1 : ArithmeticFunction ℂ) g := by
    rw [coe_moebius_mul_coe_zeta]
  rw [coe_mul_zeta_apply, one_apply] at key
  rw [← key]
  apply sum_congr rfl
  intro e _
  rw [intCoe_apply]

/-- The divisors of `gcd(q, a)` are the divisors of `q` that divide `a`. -/
theorem divisors_gcd_eq_filter (q a : ℕ) (hq : q ≠ 0) :
    (q.gcd a).divisors = q.divisors.filter (· ∣ a) := by
  ext e
  simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨heq, hea⟩, _⟩
    exact ⟨⟨heq, hq⟩, hea⟩
  · rintro ⟨⟨heq, _⟩, hea⟩
    exact ⟨⟨heq, hea⟩, Nat.gcd_ne_zero_left hq⟩

/-- `ω = e(1/q)` is a primitive `q`-th root of unity. -/
theorem isPrimitiveRoot_om (q : ℕ) (hq : 1 ≤ q) : IsPrimitiveRoot (om q) q := by
  have : om q = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ)) := rfl
  rw [this]
  exact Complex.isPrimitiveRoot_exp q (by omega)

/-- The summand as a power of the root of unity: `e(na/q) = ω^{na}`. -/
theorem eR_eq_om_pow (q n a : ℕ) (hq : 1 ≤ q) :
    eR ((n : ℝ) * a / q) = (om q) ^ (n * a) := by
  have hq0 : (q : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  unfold eR om
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- The coprimality condition, written with Möbius over the divisors of `q` that divide `a`. -/
theorem coprime_indicator (q a : ℕ) (hq : q ≠ 0) :
    (if Nat.Coprime q a then (1 : ℂ) else 0)
      = ∑ e ∈ q.divisors.filter (· ∣ a), (moebius e : ℂ) := by
  rw [← divisors_gcd_eq_filter q a hq, moebius_sum_indicator _ (Nat.gcd_ne_zero_left hq)]

/-- The inner geometric sum over the multiples of `e ∣ q` is `[e = q]`, because `gcd(q, n) = 1`
makes `ω^{ne} = 1` only at `e = q`. -/
theorem inner_sum_value (q n e : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime q n) (heq : e ∣ q) :
    (∑ a ∈ (range q).filter (fun a => e ∣ a), (om q) ^ (n * a)) = if e = q then (1 : ℂ) else 0 := by
  have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos heq (by omega)
  have hcomp : IsPrimitiveRoot (om q) q := isPrimitiveRoot_om q hq
  rw [sum_filter_dvd_reindex e q he1 heq (fun a => (om q) ^ (n * a))]
  have hrw : ∀ b, (om q) ^ (n * (e * b)) = ((om q) ^ (n * e)) ^ b := by
    intro b; rw [← pow_mul]; ring_nf
  simp only [hrw]
  set x : ℂ := (om q) ^ (n * e) with hxdef
  have hxM : x ^ (q / e) = 1 := by
    rw [hxdef, ← pow_mul]
    have : n * e * (q / e) = n * q := by rw [mul_assoc, Nat.mul_div_cancel' heq]
    rw [this, mul_comm, pow_mul, hcomp.pow_eq_one, one_pow]
  rw [geom_sum_root_of_unity x (q / e) hxM]
  have hx1 : x = 1 ↔ e = q := by
    rw [hxdef, hcomp.pow_eq_one_iff_dvd]
    constructor
    · intro hdvd
      obtain ⟨k, hk⟩ := heq
      have hkpos : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; simp at hk; omega
        · exact h
      have hkn : k ∣ n := by
        have h1 : e * k ∣ e * n := by rw [← hk, mul_comm e n]; exact hdvd
        exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < e)).mp h1
      have hkq : k ∣ q := ⟨e, by rw [hk]; ring⟩
      have : k ∣ Nat.gcd q n := Nat.dvd_gcd hkq hkn
      rw [hcop] at this
      have : k = 1 := Nat.dvd_one.mp this
      rw [this, mul_one] at hk
      omega
    · intro heq'
      subst heq'
      exact Dvd.intro_left n rfl
  by_cases hcase : e = q
  · rw [if_pos hcase, if_pos (hx1.mpr hcase)]
    have : q / e = 1 := by rw [hcase, Nat.div_self (by omega)]
    rw [this]; norm_num
  · rw [if_neg hcase, if_neg (fun h => hcase (hx1.mp h))]

/-- **The Ramanujan sum at a coprime argument is the Möbius function:** `c_q(n) = μ(q)` when
`gcd(q, n) = 1`. On a major arc this is the factor `μ(q)` in `S(a/q + β) ≈ (μ(q)/φ(q)) v(β)`
(plan, Step 3b). -/
theorem ramanujanSum_of_coprime {q n : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime q n) :
    ramanujanSum q n = (moebius q : ℂ) := by
  have hq0 : q ≠ 0 := by omega
  have step1 : ramanujanSum q n
      = ∑ a ∈ (range q).filter (fun a => Nat.Coprime q a), (om q) ^ (n * a) := by
    unfold ramanujanSum
    exact sum_congr rfl (fun a _ => eR_eq_om_pow q n a hq)
  rw [step1, sum_filter]
  have step2 : (∑ a ∈ range q, if Nat.Coprime q a then (om q) ^ (n * a) else 0)
      = ∑ a ∈ range q,
          (∑ e ∈ q.divisors.filter (· ∣ a), (moebius e : ℂ)) * (om q) ^ (n * a) := by
    apply sum_congr rfl
    intro a _
    rw [← coprime_indicator q a hq0]
    by_cases h : Nat.Coprime q a
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [step2]
  have step3 : (∑ a ∈ range q,
        (∑ e ∈ q.divisors.filter (· ∣ a), (moebius e : ℂ)) * (om q) ^ (n * a))
      = ∑ e ∈ q.divisors,
          (moebius e : ℂ) * ∑ a ∈ (range q).filter (fun a => e ∣ a), (om q) ^ (n * a) := by
    simp only [sum_mul, mul_sum]
    apply sum_comm'
    intro a e
    simp only [mem_filter, mem_range, Nat.mem_divisors]
    constructor
    · rintro ⟨ha, ⟨heq, _⟩, hea⟩
      exact ⟨⟨ha, hea⟩, heq, hq0⟩
    · rintro ⟨⟨ha, hea⟩, heq, _⟩
      exact ⟨ha, ⟨heq, hq0⟩, hea⟩
  rw [step3]
  have step4 : (∑ e ∈ q.divisors,
        (moebius e : ℂ) * ∑ a ∈ (range q).filter (fun a => e ∣ a), (om q) ^ (n * a))
      = ∑ e ∈ q.divisors, (moebius e : ℂ) * (if e = q then (1 : ℂ) else 0) := by
    apply sum_congr rfl
    intro e he
    rw [inner_sum_value q n e hq hcop (Nat.mem_divisors.mp he).1]
  rw [step4, sum_eq_single q]
  · rw [if_pos rfl, mul_one]
  · intro e _ hne
    rw [if_neg hne, mul_zero]
  · intro hq'
    exact absurd (Nat.mem_divisors_self q hq0) hq'

/-- The residues coprime to `q` number `φ(q)`. -/
theorem card_coprime_filter (q : ℕ) :
    ((range q).filter (fun a => Nat.Coprime q a)).card = Nat.totient q := by
  rw [Nat.totient]

/-- **The trivial bound** `|c_q(n)| ≤ φ(q)`: `φ(q)` phases of modulus one. It is the only
bound on the Ramanujan sum that the singular series' tail needs (plan, Step 4b). -/
theorem norm_ramanujanSum_le (q n : ℕ) : ‖ramanujanSum q n‖ ≤ Nat.totient q := by
  unfold ramanujanSum
  calc ‖∑ a ∈ (range q).filter (fun a => Nat.Coprime q a), eR ((n : ℝ) * a / q)‖
      ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime q a), ‖eR ((n : ℝ) * a / q)‖ :=
        norm_sum_le _ _
    _ = Nat.totient q := by
        simp only [norm_eR, sum_const, card_coprime_filter, nsmul_eq_mul, mul_one]

/-- **The Ramanujan sum at a prime**, the local factor of the singular series (plan, Step 5):
`c_p(n) = p − 1` if `p ∣ n` (every phase is `1`), and `c_p(n) = μ(p) = −1` otherwise. -/
theorem ramanujanSum_prime {p n : ℕ} (hp : p.Prime) :
    ramanujanSum p n = if p ∣ n then ((p : ℂ) - 1) else -1 := by
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    obtain ⟨k, rfl⟩ := hpn
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hone : ∀ a ∈ (range p).filter (fun a => Nat.Coprime p a),
        eR (((p * k : ℕ) : ℝ) * a / p) = 1 := by
      intro a _
      have : ((p * k : ℕ) : ℝ) * a / p = ((k * a : ℕ) : ℤ) := by
        push_cast; field_simp
      rw [this, Salt.ExpSum.eR]
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (((k * a : ℕ) : ℤ) : ℝ)
          = ((k * a : ℕ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_nat_mul_two_pi_mul_I (k * a)
    unfold ramanujanSum
    rw [sum_congr rfl hone, sum_const, card_coprime_filter, Nat.totient_prime hp, nsmul_eq_mul,
      mul_one]
    push_cast [Nat.cast_sub hp.one_le]
    ring
  · rw [if_neg hpn]
    have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
    rw [ramanujanSum_of_coprime hp.one_le hcop, moebius_apply_prime hp]
    push_cast
    ring

end Salt.ThreePrimes
