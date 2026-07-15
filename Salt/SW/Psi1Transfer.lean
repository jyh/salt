/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Defs

/-!
# The SW rung, node S6a — the imprimitive ψ₁-transfer

Design: `docs/blueprints/sw.md`, wave S6 (the S6a row). The SW gate quantifies over
**all** `χ mod q`, whereas the S1–S5 analytic chain produces its shifted bounds for the
*primitive* character `χ₁ := χ.primitiveCharacter` (level `f := χ.conductor`). This module
is the algebraic bridge that lets S6b transfer a `psi1Chi`-bound from `χ₁` back to `χ`,
controlling the finite prime-power correction with an explicit `ω(q)·log x·x` bound.

## The support analysis (where `χ` and `χ₁` differ)

For `n : ℕ`, with `χ = changeLevel χ₁` (`changeLevel_primitiveCharacter`):

* If `gcd(n, q) = 1` then also `gcd(n, f) = 1` (as `f ∣ q`), and mathlib's
  `primitiveCharacter_apply_of_isCoprime` gives `χ(n) = χ₁(n)` — the summand **cancels**.
* If `gcd(n, q) ≠ 1` then `χ(n) = 0` (non-unit, `MulChar.map_nonunit`), while `χ₁(n)`
  may be nonzero; the difference `χ(n) − χ₁(n) = −χ₁(n)` has norm `≤ 1`.

So `‖χ(n) − χ₁(n)‖ ≤ 𝟙[¬ coprime(n, q)]`, and — since `Λ` is supported on prime powers —
the difference `ψ₁(x, χ) − ψ₁(x, χ₁)` is supported on prime powers `p^k` with `p ∣ q`
(`Λ(p^k) = log p`, `(x − p^k)₊ ≤ x`).

## The bound

`‖ψ₁(x, χ) − ψ₁(x, χ₁)‖ ≤ x · ∑_{p∣q} ∑_{k: p^k ≤ x} log p ≤ x · ∑_{p∣q} log x = ω(q)·log x·x`,
where `ω(q) = q.primeFactors.card` and the per-prime cap `∑_{k: p^k ≤ x} log p ≤ log x`
is exactly `∑_{d ∣ p^K} Λ(d) = log(p^K) ≤ log x` with `K = Nat.log p ⌊x⌋₊`
(mathlib `vonMangoldt_sum`). Constant `C = 1`, and the shape `ω(q) ≤ log q / log 2`.

**Why the crude bound suffices for S6:** the fold's error budget (design-frozen S6) is
`x²·e^{−c√log x}`; this transfer error is `ω(q)·log x·x ≤ (log q)·(log x)·x ≪ x^{1.1}`
for `q ≤ (log x)^C`, which is beaten by `x²·e^{−c√log x}` trivially.

## Exports (what S6b consumes)

* `psi1_transfer` — the `‖ψ₁(x, χ) − ψ₁(x, χ₁)‖ ≤ ω(q)·log x·x` bound (main deliverable).
* `psi1_transfer_one` — the specialization to `χ = 1 mod q` (dispatcher case (i)).
* `psi1Chi_one_primitive` — the `χ₀`-alignment: `ψ₁(x, (1 mod q).primitiveCharacter) =
  ψ₁(x, 1 mod 1)` (the ζ-carrier), via `conductor 1 = 1` (`DirichletCharacter.conductor_one`).
-/

namespace Salt.SW

open Salt.LS ArithmeticFunction Finset

/-! ## 1. The per-prime restricted von Mangoldt cap `∑_{k: p^k ≤ x} log p ≤ log x` -/

/-- **Per-prime cap.** For a prime `p` and `x ≥ 1`, the Λ-mass carried by the multiples of
`p` in `[1, ⌊x⌋₊]` (i.e. the powers `p, p², …, p^K` with `K = Nat.log p ⌊x⌋₊`) is at most
`log x`. Proof: this sum equals `∑_{d ∣ p^K} Λ(d) = log(p^K)` (mathlib `vonMangoldt_sum`,
after discarding the vanishing terms), and `p^K ≤ ⌊x⌋₊ ≤ x`. -/
theorem sum_vonMangoldt_multiples_le_log {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if p ∣ n then vonMangoldt n else 0) ≤ Real.log x := by
  set m := ⌊x⌋₊ with hm
  have hxpos : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hx)
  have hm0 : m ≠ 0 := by omega
  set K := Nat.log p m with hK
  have hpK_le : p ^ K ≤ m := Nat.pow_log_le_self p hm0
  -- The prime-power divisors of `p^K` all lie in `[1, m]`.
  have hsub : (p ^ K).divisors ⊆ Finset.Icc 1 m := by
    intro d hd
    rw [Finset.mem_Icc]
    refine ⟨Nat.pos_of_mem_divisors hd, ?_⟩
    exact le_trans (Nat.le_of_dvd (pow_pos hp.pos K) (Nat.dvd_of_mem_divisors hd)) hpK_le
  -- Terms of `[1, m]` outside `p^K`'s divisors carry no Λ-mass.
  have hzero : ∀ n ∈ Finset.Icc 1 m, n ∉ (p ^ K).divisors →
      (if p ∣ n then vonMangoldt n else 0) = 0 := by
    intro n hn hnd
    by_cases hpn : p ∣ n
    · rw [if_pos hpn]
      by_contra hΛ
      apply hnd
      obtain ⟨r, k, hr, hk, hrk⟩ := vonMangoldt_ne_zero_iff.mp hΛ
      have hrp : r.Prime := Nat.prime_iff.mpr hr
      have hpr : p = r :=
        (Nat.prime_dvd_prime_iff_eq hp hrp).mp (hp.dvd_of_dvd_pow (hrk ▸ hpn))
      have hnpk : n = p ^ k := by rw [hpr, hrk]
      have hkK : k ≤ K := by
        rw [hK]
        exact (Nat.le_log_iff_pow_le hp.one_lt hm0).mpr (hnpk ▸ (Finset.mem_Icc.mp hn).2)
      exact (Nat.mem_divisors_prime_pow hp K).mpr ⟨k, hkK, hnpk⟩
    · rw [if_neg hpn]
  -- Collapse to the divisor sum and evaluate.
  rw [← Finset.sum_subset hsub hzero]
  have hcongr : ∑ d ∈ (p ^ K).divisors, (if p ∣ d then vonMangoldt d else 0)
      = ∑ d ∈ (p ^ K).divisors, vonMangoldt d := by
    refine Finset.sum_congr rfl (fun d hd => ?_)
    obtain ⟨j, hjK, rfl⟩ := (Nat.mem_divisors_prime_pow hp K).mp hd
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [pow_zero, if_neg (by simp [Nat.dvd_one, hp.ne_one]), vonMangoldt_apply_one]
    · rw [if_pos (dvd_pow_self p hjpos.ne')]
  rw [hcongr, vonMangoldt_sum]
  have hle : ((p ^ K : ℕ) : ℝ) ≤ x :=
    le_trans (by exact_mod_cast hpK_le) (Nat.floor_le hxpos)
  exact Real.log_le_log (by exact_mod_cast pow_pos hp.pos K) hle

/-! ## 2. The character-difference norm bound -/

/-- **Character-difference bound.** For `χ : DirichletCharacter ℂ q` and `n : ℕ`,
`‖χ(n) − χ₁(n)‖ ≤ 𝟙[¬ coprime(n, q)]`, where `χ₁ = χ.primitiveCharacter`: the difference
vanishes on coprime residues (`primitiveCharacter_apply_of_isCoprime`) and has norm `≤ 1`
otherwise (`χ(n) = 0` at a non-unit, `‖χ₁(n)‖ ≤ 1`). -/
theorem norm_char_sub_primitiveCharacter_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (n : ℕ) :
    ‖χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor)‖
      ≤ (if Nat.Coprime n q then (0 : ℝ) else 1) := by
  by_cases hcop : Nat.Coprime n q
  · rw [if_pos hcop]
    have h := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ)) hcop.isCoprime
    simp only [Int.cast_natCast] at h
    rw [← h, sub_self, norm_zero]
  · rw [if_neg hcop]
    have hnu : ¬ IsUnit (n : ZMod q) := fun h => hcop ((ZMod.isUnit_iff_coprime n q).mp h)
    rw [MulChar.map_nonunit χ hnu, zero_sub, norm_neg]
    exact χ.primitiveCharacter.norm_le_one _

/-! ## 3. The aggregate `∑_{n ≤ x, ¬coprime} Λ(n) ≤ ω(q)·log x` -/

/-- **The non-coprime Λ-mass bound.** The Λ-mass on `[1, ⌊x⌋₊]` restricted to residues
sharing a factor with `q` is at most `ω(q)·log x`. Each such prime power `p^k` (`p ∣ q`)
is covered by its prime `p ∈ q.primeFactors`; swap the order and apply the per-prime cap. -/
theorem sum_vonMangoldt_not_coprime_le {q : ℕ} [NeZero q] {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (0 : ℝ) else vonMangoldt n)
      ≤ (q.primeFactors.card : ℝ) * Real.log x := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hnn : ∀ (p' k : ℕ), (0 : ℝ) ≤ if p' ∣ k then vonMangoldt k else 0 := by
    intro p' k; split_ifs with h
    · exact vonMangoldt_nonneg
    · exact le_refl 0
  -- Pointwise: each non-coprime term is dominated by its prime-factor fibres.
  have hpt : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (if Nat.Coprime n q then (0 : ℝ) else vonMangoldt n)
        ≤ ∑ p ∈ q.primeFactors, (if p ∣ n then vonMangoldt n else 0) := by
    intro n _
    by_cases hcop : Nat.Coprime n q
    · rw [if_pos hcop]
      exact Finset.sum_nonneg (fun p _ => hnn p n)
    · rw [if_neg hcop]
      have hg1 : Nat.gcd n q ≠ 1 := hcop
      have hpp : (Nat.gcd n q).minFac.Prime := Nat.minFac_prime hg1
      have hpg : (Nat.gcd n q).minFac ∣ Nat.gcd n q := Nat.minFac_dvd _
      have hpn : (Nat.gcd n q).minFac ∣ n := hpg.trans (Nat.gcd_dvd_left n q)
      have hpq : (Nat.gcd n q).minFac ∣ q := hpg.trans (Nat.gcd_dvd_right n q)
      have hpmem : (Nat.gcd n q).minFac ∈ q.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp, hpq, hq0⟩
      calc vonMangoldt n
          = (if (Nat.gcd n q).minFac ∣ n then vonMangoldt n else 0) := (if_pos hpn).symm
        _ ≤ ∑ p ∈ q.primeFactors, (if p ∣ n then vonMangoldt n else 0) :=
            Finset.single_le_sum (fun p _ => hnn p n) hpmem
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (0 : ℝ) else vonMangoldt n)
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ p ∈ q.primeFactors, (if p ∣ n then vonMangoldt n else 0) :=
        Finset.sum_le_sum hpt
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if p ∣ n then vonMangoldt n else 0) :=
        Finset.sum_comm
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log x :=
        Finset.sum_le_sum (fun p hp =>
          sum_vonMangoldt_multiples_le_log (Nat.prime_of_mem_primeFactors hp) hx)
    _ = (q.primeFactors.card : ℝ) * Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## 4. The main transfer bound -/

/-- **The imprimitive ψ₁-transfer (S6a).** For any `χ : DirichletCharacter ℂ q` and `x ≥ 1`,
`‖ψ₁(x, χ) − ψ₁(x, χ.primitiveCharacter)‖ ≤ ω(q)·log x·x` (constant `C = 1`,
`ω(q) = q.primeFactors.card ≤ log q / log 2`). The difference is a single Riesz sum over
`[1, ⌊x⌋₊]`; its `n`-th summand has norm `Λ(n)·‖χ(n) − χ₁(n)‖·(x − n) ≤ Λ(n)·𝟙[¬coprime]·x`,
and the non-coprime Λ-mass is capped by `ω(q)·log x`. -/
theorem psi1_transfer {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) :
    ‖psi1Chi x χ - psi1Chi x χ.primitiveCharacter‖
      ≤ (q.primeFactors.card : ℝ) * Real.log x * x := by
  have hxpos : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  -- Combine the two Riesz means (same index set `[1, ⌊x⌋₊]`) into one sum.
  have hcomb : psi1Chi x χ - psi1Chi x χ.primitiveCharacter
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (vonMangoldt n : ℂ) * (χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor))
            * ((x : ℂ) - n) := by
    simp only [psi1Chi]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [hcomb]
  calc ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (vonMangoldt n : ℂ) * (χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor))
            * ((x : ℂ) - n)‖
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ‖(vonMangoldt n : ℂ) * (χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor))
            * ((x : ℂ) - n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          vonMangoldt n * (if Nat.Coprime n q then (0 : ℝ) else 1) * x := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hnx : (n : ℝ) ≤ x :=
          le_trans (by exact_mod_cast (Finset.mem_Icc.mp hn).2) (Nat.floor_le hxpos)
        have hxn0 : 0 ≤ x - (n : ℝ) := by linarith
        rw [norm_mul, norm_mul]
        have hΛnorm : ‖(vonMangoldt n : ℂ)‖ = vonMangoldt n := by
          rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
        have hxnnorm : ‖((x : ℂ) - (n : ℂ))‖ = x - n := by
          rw [show ((x : ℂ) - (n : ℂ)) = (((x - n : ℝ)) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_of_nonneg hxn0]
        rw [hΛnorm, hxnnorm]
        have hind : 0 ≤ (if Nat.Coprime n q then (0 : ℝ) else 1) := by
          split_ifs <;> norm_num
        have h1 : vonMangoldt n
              * ‖χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor)‖ * (x - n)
            ≤ vonMangoldt n * (if Nat.Coprime n q then (0 : ℝ) else 1) * (x - n) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (norm_char_sub_primitiveCharacter_le χ n)
              vonMangoldt_nonneg) hxn0
        exact le_trans h1 (mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg vonMangoldt_nonneg hind))
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (0 : ℝ) else vonMangoldt n) * x := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        split_ifs <;> ring
    _ = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (0 : ℝ) else vonMangoldt n)) * x := by
        rw [Finset.sum_mul]
    _ ≤ (q.primeFactors.card : ℝ) * Real.log x * x :=
        mul_le_mul_of_nonneg_right (sum_vonMangoldt_not_coprime_le hx) hxpos

/-! ## 5. The `χ₀`-alignment (trivial character ↦ the mod-1 ζ-carrier) -/

/-- **`χ₀`-alignment.** The primitive character of the trivial character `1 mod q` is the
trivial character `1 mod 1` (the ζ-carrier), so their Riesz means agree:
`ψ₁(x, (1 mod q).primitiveCharacter) = ψ₁(x, 1 mod 1)`. Uses mathlib's
`primitiveCharacter_one` and `conductor_one` (`conductor 1 = 1`). -/
theorem psi1Chi_one_primitive {q : ℕ} [NeZero q] (x : ℝ) :
    psi1Chi x ((1 : DirichletCharacter ℂ q).primitiveCharacter)
      = psi1Chi x (1 : DirichletCharacter ℂ 1) := by
  have key : ∀ (m : ℕ), m = 1 →
      psi1Chi x (1 : DirichletCharacter ℂ m) = psi1Chi x (1 : DirichletCharacter ℂ 1) := by
    intro m h; subst h; rfl
  rw [DirichletCharacter.primitiveCharacter_one]
  exact key _ DirichletCharacter.conductor_one

/-- **The transfer at `χ = 1 mod q`** (S6b dispatcher case (i)): the bound between the
mod-`q` trivial character and its primitive (conductor-1) character. Combine with
`psi1Chi_one_primitive` to reach the mod-1 ζ-carrier. -/
theorem psi1_transfer_one {q : ℕ} [NeZero q] {x : ℝ} (hx : 1 ≤ x) :
    ‖psi1Chi x (1 : DirichletCharacter ℂ q) - psi1Chi x (1 : DirichletCharacter ℂ 1)‖
      ≤ (q.primeFactors.card : ℝ) * Real.log x * x := by
  have h := psi1_transfer (1 : DirichletCharacter ℂ q) hx
  rwa [psi1Chi_one_primitive] at h

end Salt.SW
