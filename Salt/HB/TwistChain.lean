/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.TwistedSieve
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Field.GeomSum

/-!
# The χ-twisted von-Mangoldt chain and Heath-Brown's Lemma 1 (HB-ENGINE, node HB-1)

Formalizes the definitions of §2–§3 of Heath-Brown 1983 ("Prime twins and Siegel
zeros", PLMS) and **Lemma 1** (p.198, proof p.201). The real character `χ` is
carried in the corpus convention (`Salt.TwinBar.chiRe`, a `DirichletCharacter ℂ q`
read through `Complex.re`, quadratic via `χ² = 1`); no new character framework is
introduced.

## The objects

* `fChiSum χ n = ∑_{d ∣ n} μ²(d)·χ(d)` — the multiplicative `f`; `f(p^e) = 1 + χ(p)`.
* `LamTilde χ n = ∑_{d ∣ n} μ²(d)·χ(d)·log(n/d)` — the twisted von Mangoldt `Λ̃`.
* `LamStar χ z n = ∑*_{d ∣ n} χ(d)·log(n/d)` — the sieve-truncated `Λ*`, where `∑*`
  drops any `d` divisible by `p²` for some prime `p < z` with `χ(p) = −1`.
* `nPlus χ n`, `nMinus χ n` — the `±` factorization (2.1).

## The engine

Both `Λ̃` and `Λ*` are Dirichlet convolutions of a **nonnegative** multiplicative
function with the (nonnegative) von Mangoldt `Λ`: writing `log = ζ * Λ`
(`zeta_mul_vonMangoldt`) and using associativity,
`Λ̃ = (μ²χ ∗ ζ) ∗ Λ = f ∗ Λ` and `Λ* = (h ∗ ζ) ∗ Λ = f* ∗ Λ`, where `f` and `f*`
are `≥ 0` (each local factor is a geometric sum `∑ r^k` with `|r| ≤ 1`). This yields
Lemma 1(a) `Λ*(n) ≥ 0` and (b) `Λ(n) ≤ Λ̃(n)` directly, without the coprimality
hypothesis `(n,q)=1`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — character and geometric-sum helpers -/

/-- `|χ_ℝ(n)| ≤ 1` (termwise `|Re χ| ≤ ‖χ‖ ≤ 1`; no reality hypothesis). -/
lemma chiRe_abs_le_one (χ : DirichletCharacter ℂ q) (n : ℕ) : |chiRe χ n| ≤ 1 :=
  calc |chiRe χ n| = |(χ (n : ZMod q)).re| := rfl
    _ ≤ ‖χ (n : ZMod q)‖ := Complex.abs_re_le_norm _
    _ ≤ 1 := χ.norm_le_one _

/-- `χ_ℝ` is completely multiplicative on powers: `χ_ℝ(a^k) = χ_ℝ(a)^k` (needs `χ² = 1`). -/
lemma chiRe_pow (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (a k : ℕ) :
    chiRe χ (a ^ k) = (chiRe χ a) ^ k := by
  induction k with
  | zero => simp [chiRe_one]
  | succ k ih => rw [pow_succ, chiRe_mul χ hsq, ih, pow_succ]

/-- A geometric sum with ratio bounded by `1` in absolute value is nonnegative:
    `0 ≤ ∑_{k<m} r^k` when `|r| ≤ 1`. (The workhorse behind `f, f* ≥ 0`.) -/
lemma geomSum_nonneg {r : ℝ} (hr : |r| ≤ 1) (m : ℕ) :
    0 ≤ ∑ k ∈ range m, r ^ k := by
  rcases eq_or_ne r 1 with h | h
  · subst h; simp
  · rw [geom_sum_eq h]
    have hr1 : r < 1 := lt_of_le_of_ne (abs_le.mp hr).2 h
    have hrm : r ^ m ≤ 1 :=
      le_trans (le_abs_self _) (by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hr)
    rw [div_nonneg_iff]
    right
    exact ⟨by linarith, by linarith⟩

/-- `0 ≤ ∑_{k<N} (if k < m then r^k else 0)` for `|r| ≤ 1`: the truncated geometric
    sum, `∑_{k < min N m} r^k`. This packages the "cap the exponent" step used at the
    `χ(p) = −1`, `p < z` primes and at the squarefree cap of `μ²`. -/
lemma sum_ite_lt_pow_nonneg {r : ℝ} (hr : |r| ≤ 1) (N m : ℕ) :
    0 ≤ ∑ k ∈ range N, (if k < m then r ^ k else 0) := by
  rw [← Finset.sum_filter]
  have hfilter : (range N).filter (· < m) = range (min N m) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  rw [hfilter]
  exact geomSum_nonneg hr _

/-! ## §1 — the objects (paper §2–§3)

`f`, `Λ̃` are transcribed as their divisor sums. `Λ*` carries the sieve parameter
`z` and the truncation `Admissible`. Each is also packaged as an `ArithmeticFunction`
(`gChi`, `hChiArith`, and the convolutions `fChiArith = ζ ∗ gChi`,
`fStarArith = ζ ∗ hChiArith`) for the multiplicative machinery. -/

/-- `f(n) = ∑_{d ∣ n} μ²(d)·χ(d)` — the multiplicative twisted divisor count. -/
noncomputable def fChiSum (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (μ d : ℝ) ^ 2 * chiRe χ d

/-- `Λ̃(n) = ∑_{d ∣ n} μ²(d)·χ(d)·log(n/d)` — the twisted von Mangoldt function. -/
noncomputable def LamTilde (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (μ d : ℝ) ^ 2 * chiRe χ d * Real.log ((n / d : ℕ) : ℝ)

/-- The `∑*` admissibility predicate: `d` survives iff `p² ∤ d` for every prime
    `p < z` with `χ(p) = −1`. -/
def Admissible (χ : DirichletCharacter ℂ q) (z d : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p < z → chiRe χ p = -1 → ¬ p ^ 2 ∣ d

/-- `Admissible` is a `Prop` over an unbounded prime range (and about the noncomputable
    `χ_ℝ`), so we equip it with a classical decidability instance; every `∑*`/`if`
    below uses this one instance uniformly. -/
noncomputable instance instDecidableAdmissible (χ : DirichletCharacter ℂ q) (z d : ℕ) :
    Decidable (Admissible χ z d) := Classical.propDecidable _

/-- `Λ*(n) = ∑*_{d ∣ n} χ(d)·log(n/d)` — the sieve-truncated twisted von Mangoldt
    function (depends on the sieve parameter `z`). -/
noncomputable def LamStar (χ : DirichletCharacter ℂ q) (z n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, if Admissible χ z d then chiRe χ d * Real.log ((n / d : ℕ) : ℝ) else 0

/-- `μ²·χ_ℝ` as an `ArithmeticFunction ℝ` (value `0` at `0`). -/
noncomputable def gChi (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℝ :=
  ⟨fun n => (μ n : ℝ) ^ 2 * chiRe χ n, by simp⟩

@[simp] lemma gChi_apply (χ : DirichletCharacter ℂ q) (n : ℕ) :
    gChi χ n = (μ n : ℝ) ^ 2 * chiRe χ n := rfl

/-- `χ_ℝ` restricted to the admissible divisors, as an `ArithmeticFunction ℝ`. -/
noncomputable def hChiArith (χ : DirichletCharacter ℂ q) (z : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else if Admissible χ z n then chiRe χ n else 0, by simp⟩

lemma hChiArith_apply (χ : DirichletCharacter ℂ q) (z n : ℕ) :
    hChiArith χ z n = if n = 0 then 0 else if Admissible χ z n then chiRe χ n else 0 := rfl

lemma hChiArith_apply_of_ne (χ : DirichletCharacter ℂ q) (z : ℕ) {n : ℕ} (hn : n ≠ 0) :
    hChiArith χ z n = if Admissible χ z n then chiRe χ n else 0 := by
  rw [hChiArith_apply, if_neg hn]

/-- `f = ζ ∗ (μ²χ)` — the multiplicative packaging of `fChiSum`. -/
noncomputable def fChiArith (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℝ := ζ * gChi χ

/-- `f* = ζ ∗ (χ·𝟙_admissible)` — the multiplicative packaging behind `Λ*`. -/
noncomputable def fStarArith (χ : DirichletCharacter ℂ q) (z : ℕ) : ArithmeticFunction ℝ :=
  ζ * hChiArith χ z

lemma fChiArith_apply (χ : DirichletCharacter ℂ q) (n : ℕ) :
    fChiArith χ n = ∑ d ∈ n.divisors, gChi χ d := by rw [fChiArith, coe_zeta_mul_apply]

lemma fStarArith_apply (χ : DirichletCharacter ℂ q) (z n : ℕ) :
    fStarArith χ z n = ∑ d ∈ n.divisors, hChiArith χ z d := by rw [fStarArith, coe_zeta_mul_apply]

/-- The multiplicative packaging agrees with the paper divisor sum `f`. -/
lemma fChiArith_eq_fChiSum (χ : DirichletCharacter ℂ q) (n : ℕ) :
    fChiArith χ n = fChiSum χ n := by rw [fChiArith_apply]; rfl

/-! ### Admissibility is a multiplicative truncation -/

/-- `1` is always admissible (no prime square divides it). -/
lemma admissible_one (χ : DirichletCharacter ℂ q) (z : ℕ) : Admissible χ z 1 := by
  intro p hp _ _ hdvd
  exact hp.ne_one (Nat.dvd_one.mp ((dvd_pow_self p (two_ne_zero)).trans hdvd))

/-- Admissibility factors through coprime products: `p² ∣ mn ↔ p² ∣ m ∨ p² ∣ n`. -/
lemma admissible_mul (χ : DirichletCharacter ℂ q) (z : ℕ) {m n : ℕ} (hmn : Nat.Coprime m n) :
    Admissible χ z (m * n) ↔ Admissible χ z m ∧ Admissible χ z n := by
  constructor
  · intro h
    refine ⟨fun p hp hpz hpc hdvd => h p hp hpz hpc (hdvd.trans (dvd_mul_right m n)),
            fun p hp hpz hpc hdvd => h p hp hpz hpc (hdvd.trans (dvd_mul_left n m))⟩
  · rintro ⟨hm, hn⟩ p hp hpz hpc hdvd
    have hpmn : p ∣ m * n := (dvd_pow_self p (two_ne_zero)).trans hdvd
    rcases (hp.dvd_mul.mp hpmn) with hpm | hpn
    · have hpn' : ¬ p ∣ n := fun hd => Nat.Prime.not_dvd_one hp
        (hmn ▸ Nat.dvd_gcd hpm hd)
      have hcop : Nat.Coprime (p ^ 2) n := (hp.coprime_iff_not_dvd.mpr hpn').pow_left 2
      exact hm p hp hpz hpc (hcop.dvd_of_dvd_mul_right hdvd)
    · have hpm' : ¬ p ∣ m := fun hd => Nat.Prime.not_dvd_one hp
        (hmn ▸ Nat.dvd_gcd hd hpn)
      have hcop : Nat.Coprime (p ^ 2) m := (hp.coprime_iff_not_dvd.mpr hpm').pow_left 2
      exact hn p hp hpz hpc (hcop.dvd_of_dvd_mul_left hdvd)

/-! ## §2 — multiplicativity -/

/-- `μ²·χ_ℝ` is multiplicative (for real `χ`). -/
lemma gChi_mult (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) :
    (gChi χ).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [chiRe_one], ?_⟩
  intro m n hm hn hmn
  have hmu : (μ (m * n) : ℤ) = μ m * μ n := isMultiplicative_moebius.map_mul_of_coprime hmn
  simp only [gChi_apply]
  rw [chiRe_mul χ hsq, hmu]
  push_cast
  ring

/-- The admissible-restricted `χ_ℝ` is multiplicative (uses `admissible_mul`). -/
lemma hChiArith_mult (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ) :
    (hChiArith χ z).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [hChiArith_apply_of_ne _ _ one_ne_zero, if_pos (admissible_one χ z), chiRe_one]
  · intro m n hm hn hmn
    rw [hChiArith_apply_of_ne _ _ (Nat.mul_ne_zero hm hn),
        hChiArith_apply_of_ne _ _ hm, hChiArith_apply_of_ne _ _ hn]
    by_cases hA : Admissible χ z (m * n)
    · obtain ⟨hAm, hAn⟩ := (admissible_mul χ z hmn).mp hA
      rw [if_pos hA, if_pos hAm, if_pos hAn, chiRe_mul χ hsq]
    · rw [if_neg hA]
      rw [admissible_mul χ z hmn] at hA
      rcases not_and_or.mp hA with hAm | hAn
      · rw [if_neg hAm, zero_mul]
      · rw [if_neg hAn, mul_zero]

/-- `f = ζ ∗ (μ²χ)` is multiplicative. -/
lemma fChiArith_mult (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) :
    (fChiArith χ).IsMultiplicative := by
  unfold fChiArith
  exact ArithmeticFunction.isMultiplicative_zeta.natCast.mul (gChi_mult χ hsq)

/-- `f* = ζ ∗ (χ·𝟙_admissible)` is multiplicative. -/
lemma fStarArith_mult (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ) :
    (fStarArith χ z).IsMultiplicative := by
  unfold fStarArith
  exact ArithmeticFunction.isMultiplicative_zeta.natCast.mul (hChiArith_mult χ hsq z)

/-! ## §3 — the local factors are nonnegative

`f(p^e)` and `f*(p^e)` are geometric sums `∑ r^k` (possibly truncated at the
squarefree / small-`χ(p)=−1` cap), with `|r| = |χ(p)| ≤ 1`, hence `≥ 0`. Feeding
this through `multiplicative_factorization` gives `f, f* ≥ 0` on all of `ℕ`. -/

/-- `μ²(p^k) = [k < 2]` (in `ℝ`): `μ²` is the squarefree indicator. -/
lemma moebius_sq_primePow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((μ (p ^ k) : ℝ)) ^ 2 = if k < 2 then 1 else 0 := by
  rcases k with _ | _ | k
  · simp
  · simp [ArithmeticFunction.moebius_apply_prime hp]
  · rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp

/-- `f`'s local factor: `f(p^k) = [k < 2]·χ(p)^k` (`= 1` at `k=0`, `1+χ(p)` capped). -/
lemma gChi_primePow {p : ℕ} (hp : p.Prime) (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (k : ℕ) : gChi χ (p ^ k) = if k < 2 then (chiRe χ p) ^ k else 0 := by
  rw [gChi_apply, moebius_sq_primePow hp, chiRe_pow χ hsq]
  by_cases h : k < 2 <;> simp [h]

/-- `f(p^e) ≥ 0` (a truncated geometric sum in `χ(p)`, `|χ(p)| ≤ 1`). -/
lemma fChiArith_primePow_nonneg {p : ℕ} (hp : p.Prime) (χ : DirichletCharacter ℂ q)
    (hsq : χ ^ 2 = 1) (e : ℕ) : 0 ≤ fChiArith χ (p ^ e) := by
  rw [fChiArith_apply, Nat.sum_divisors_prime_pow hp]
  simp_rw [gChi_primePow hp χ hsq]
  exact sum_ite_lt_pow_nonneg (chiRe_abs_le_one χ p) (e + 1) 2

/-- `f ≥ 0` on all of `ℕ` (multiplicative with nonnegative local factors). -/
lemma fChiArith_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ fChiArith χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [(fChiArith_mult χ hsq).multiplicative_factorization (fChiArith χ) hn, Finsupp.prod]
    apply Finset.prod_nonneg
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)
    exact fChiArith_primePow_nonneg hpp χ hsq _

/-- `f*(p^e) ≥ 0`: at a small `χ(p)=−1` prime the exponent is capped at `1`
    (truncated geometric sum), otherwise it is the full geometric sum `∑ χ(p)^k`;
    either way `|χ(p)| ≤ 1` makes it nonnegative. -/
lemma fStarArith_primePow_nonneg {p : ℕ} (hp : p.Prime) (χ : DirichletCharacter ℂ q)
    (hsq : χ ^ 2 = 1) (z e : ℕ) : 0 ≤ fStarArith χ z (p ^ e) := by
  rw [fStarArith_apply, Nat.sum_divisors_prime_pow hp]
  by_cases H : p < z ∧ chiRe χ p = -1
  · -- small `χ(p) = −1` prime: admissible ⇔ `k < 2`
    have hterm : ∀ k, hChiArith χ z (p ^ k) = if k < 2 then (chiRe χ p) ^ k else 0 := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp only [pow_zero]
        rw [hChiArith_apply_of_ne _ _ one_ne_zero, if_pos (admissible_one χ z), chiRe_one]
        simp
      · rw [hChiArith_apply_of_ne _ _ (pow_ne_zero _ hp.ne_zero)]
        by_cases hk : k < 2
        · have hAdm : Admissible χ z (p ^ k) := by
            intro r hr _ _ hrdvd
            have hk1 : k = 1 := by omega
            have hsf : Squarefree (p ^ k) := by rw [hk1, pow_one]; exact hp.squarefree
            exact hr.ne_one (Nat.isUnit_iff.mp (hsf r (pow_two r ▸ hrdvd)))
          rw [if_pos hAdm, if_pos hk, chiRe_pow χ hsq]
        · have hnAdm : ¬ Admissible χ z (p ^ k) :=
            fun hAdm => hAdm p hp H.1 H.2 (pow_dvd_pow p (by omega))
          rw [if_neg hnAdm, if_neg hk]
    simp_rw [hterm]
    exact sum_ite_lt_pow_nonneg (chiRe_abs_le_one χ p) (e + 1) 2
  · -- ordinary prime: every `p^k` is admissible
    have hterm : ∀ k, hChiArith χ z (p ^ k) = (chiRe χ p) ^ k := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp only [pow_zero]
        rw [hChiArith_apply_of_ne _ _ one_ne_zero, if_pos (admissible_one χ z), chiRe_one]
      · rw [hChiArith_apply_of_ne _ _ (pow_ne_zero _ hp.ne_zero)]
        have hAdm : Admissible χ z (p ^ k) := by
          intro r hr hrz hrc hrdvd
          have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp
            (hr.dvd_of_dvd_pow ((dvd_pow_self r two_ne_zero).trans hrdvd))
          subst hrp
          exact H ⟨hrz, hrc⟩
        rw [if_pos hAdm, chiRe_pow χ hsq]
    simp_rw [hterm]
    exact geomSum_nonneg (chiRe_abs_le_one χ p) (e + 1)

/-- `f* ≥ 0` on all of `ℕ`. -/
lemma fStarArith_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z n : ℕ) :
    0 ≤ fStarArith χ z n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [(fStarArith_mult χ hsq z).multiplicative_factorization (fStarArith χ z) hn, Finsupp.prod]
    apply Finset.prod_nonneg
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)
    exact fStarArith_primePow_nonneg hpp χ hsq _ _

/-! ## §4 — Lemma 1(a),(b) via the convolution identities

`Λ̃ = f ∗ Λ` and `Λ* = f* ∗ Λ` (from `log = ζ ∗ Λ` and commutativity). Since `f`,
`f*`, and `Λ` are all `≥ 0`, part (a) `Λ*(n) ≥ 0` is a sum of nonnegative terms, and
part (b) `Λ(n) ≤ Λ̃(n)` follows because the `(1, n)` term of the convolution is
exactly `f(1)·Λ(n) = Λ(n)`. Neither needs `(n, q) = 1`. -/

/-- `Λ̃` as the Dirichlet convolution `(μ²χ) ∗ log`. -/
lemma LamTilde_eq_conv (χ : DirichletCharacter ℂ q) (n : ℕ) :
    LamTilde χ n = (gChi χ * ArithmeticFunction.log) n := by
  rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => gChi χ a * ArithmeticFunction.log b), LamTilde]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [gChi_apply, ArithmeticFunction.log_apply, mul_assoc]

/-- `Λ*` as the Dirichlet convolution `(χ·𝟙_admissible) ∗ log`. -/
lemma LamStar_eq_conv (χ : DirichletCharacter ℂ q) (z n : ℕ) :
    LamStar χ z n = (hChiArith χ z * ArithmeticFunction.log) n := by
  rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => hChiArith χ z a * ArithmeticFunction.log b), LamStar]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hChiArith_apply_of_ne _ _ (Nat.pos_of_mem_divisors hd).ne', ArithmeticFunction.log_apply,
      ite_mul, zero_mul]

/-- The key associativity: `(μ²χ) ∗ log = f ∗ Λ`, using `log = ζ ∗ Λ`. -/
lemma gChi_mul_log (χ : DirichletCharacter ℂ q) :
    gChi χ * ArithmeticFunction.log = fChiArith χ * Λ := by
  rw [fChiArith, ← zeta_mul_vonMangoldt]; ring

/-- The key associativity: `(χ·𝟙_admissible) ∗ log = f* ∗ Λ`. -/
lemma hChiArith_mul_log (χ : DirichletCharacter ℂ q) (z : ℕ) :
    hChiArith χ z * ArithmeticFunction.log = fStarArith χ z * Λ := by
  rw [fStarArith, ← zeta_mul_vonMangoldt]; ring

/-- `Λ̃ = f ∗ Λ` at every argument. -/
lemma LamTilde_eq_fChi_conv (χ : DirichletCharacter ℂ q) (n : ℕ) :
    LamTilde χ n = (fChiArith χ * Λ) n := by rw [LamTilde_eq_conv, gChi_mul_log]

/-- `Λ* = f* ∗ Λ` at every argument. -/
lemma LamStar_eq_fStar_conv (χ : DirichletCharacter ℂ q) (z n : ℕ) :
    LamStar χ z n = (fStarArith χ z * Λ) n := by rw [LamStar_eq_conv, hChiArith_mul_log]

/-- **Lemma 1(a).** `Λ*(n) ≥ 0` for every `n` (no coprimality needed). -/
theorem LamStar_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z n : ℕ) :
    0 ≤ LamStar χ z n := by
  rw [LamStar_eq_fStar_conv, ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (fStarArith_nonneg χ hsq z x.1) vonMangoldt_nonneg

/-- **Lemma 1(b).** `Λ(n) ≤ Λ̃(n)` for every `n` (no coprimality needed): the
    `(1, n)` term of `f ∗ Λ` already contributes `f(1)·Λ(n) = Λ(n)`, and every term
    is nonnegative. -/
theorem vonMangoldt_le_LamTilde (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    Λ n ≤ LamTilde χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LamTilde]
  · rw [LamTilde_eq_fChi_conv, ArithmeticFunction.mul_apply]
    have hmem : (1, n) ∈ n.divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, hn⟩
    have h1 : fChiArith χ 1 = 1 := (fChiArith_mult χ hsq).map_one
    calc Λ n = fChiArith χ (1, n).1 * Λ (1, n).2 := by simp [h1]
      _ ≤ ∑ x ∈ n.divisorsAntidiagonal, fChiArith χ x.1 * Λ x.2 :=
          Finset.single_le_sum
            (fun x _ => mul_nonneg (fChiArith_nonneg χ hsq x.1) vonMangoldt_nonneg) hmem

/-! ## §5 — the `±` factorization (2.1)

For `(n, q) = 1` every prime `p ∣ n` has `χ(p) = ±1`, so `n` splits as `n₊·n₋`
with `n₊ = ∏_{χ(p)=1} p^{e_p}`, `n₋ = ∏_{χ(p)=−1} p^{e_p}`, and `n₊`, `n₋` coprime. -/

open Classical in
/-- `n₊ = ∏_{p ∣ n, χ(p) = 1} p^{v_p(n)}`. -/
noncomputable def nPlus (χ : DirichletCharacter ℂ q) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => chiRe χ p = 1), p ^ (n.factorization p)

open Classical in
/-- `n₋ = ∏_{p ∣ n, χ(p) = −1} p^{v_p(n)}`. -/
noncomputable def nMinus (χ : DirichletCharacter ℂ q) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => chiRe χ p = -1), p ^ (n.factorization p)

/-- On divisors coprime to `q` a real character takes the values `±1` (never `0`). -/
lemma chiRe_eq_one_or_neg_one (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {p : ℕ}
    (hp : Nat.Coprime p q) : chiRe χ p = 1 ∨ chiRe χ p = -1 := by
  have hu : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).mpr hp
  have hne : χ (p : ZMod q) ≠ 0 := MulChar.apply_ne_zero_iff.mpr hu
  have hQ : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq
  rcases hQ (p : ZMod q) with h | h | h
  · exact absurd h hne
  · left; change (χ (p : ZMod q)).re = 1; rw [h]; simp
  · right; change (χ (p : ZMod q)).re = -1; rw [h]; simp

/-- **The `±` factorization (2.1).** For `(n, q) = 1`, `n = n₊·n₋`. -/
theorem eq_nPlus_mul_nMinus (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hn : n ≠ 0) (hcop : Nat.Coprime n q) : n = nPlus χ n * nMinus χ n := by
  classical
  have hself : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
  have hfeq : n.primeFactors.filter (fun p => ¬ chiRe χ p = 1)
            = n.primeFactors.filter (fun p => chiRe χ p = -1) := by
    apply Finset.filter_congr
    intro p hp
    have hpc : Nat.Coprime p q :=
      Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hcop
    rcases chiRe_eq_one_or_neg_one χ hsq hpc with h1 | h1 <;> rw [h1] <;> norm_num
  rw [nPlus, nMinus, ← hfeq, Finset.prod_filter_mul_prod_filter_not, ← hself]

/-- **`n₊` and `n₋` are coprime.** -/
theorem coprime_nPlus_nMinus (χ : DirichletCharacter ℂ q) (n : ℕ) :
    Nat.Coprime (nPlus χ n) (nMinus χ n) := by
  classical
  rw [nPlus, nMinus]
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro r hr
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hr)
  have hpr : p ≠ r := by
    rintro rfl
    have h1 : chiRe χ p = 1 := (Finset.mem_filter.mp hp).2
    have h2 : chiRe χ p = -1 := (Finset.mem_filter.mp hr).2
    rw [h1] at h2; norm_num at h2
  exact ((Nat.coprime_primes hpp hrp).mpr hpr).pow _ _

end Salt.HB
