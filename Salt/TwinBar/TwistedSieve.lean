/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.LinearSieve
import Salt.TwinBar.SiegelCorrStrong

/-!
# The χ-twisted sieve weight (S3-HB-R3c, wave 1)

Design: `docs/exploration/s3-hb3-design.md` (FROZEN, gate `S3-HB3C-GATE`
GO-WITH-BLOCK, 2026-07-16). This module is the **boundary-entry rung**: it builds
the character-twisted sieve weight `λ_χ = (χ_ℝ ∗ 1)` as a Lean object on top of
mathlib's `BoundingSieve` combinators, lands the τ-weighted remainder (node b) and
the sparse-product Euler factorization (node a1), and STOPS at the R4 wall.

## The reuse seam (why this is not new bookkeeping)

`BoundingSieve.mainSum`/`errSum` are `(ℕ → ℝ) → ℝ`, i.e. WEIGHT-GENERIC. So the
twisted main/error sums are the abstract mathlib combinators AT the signed weight
`lamChi χ` on ANY landed sieve `s`; no mirror of the stratum-0 plumbing is needed.
The obstruction is the two downstream consumers (`errSum_lam_le`, `linear_sieve_lower`),
re-derived here for the τ-bound (node b) — never `|λ| ≤ 1`, which is FALSE for `λ_χ`.

## Honesty / death map (R4 — no twin claim, no branch smuggled)

* **This is NOT a proof of the Twin Prime Conjecture.** The deliverable is the
  partial landing (defs + `lamChi_mult` + node b + node a1); it inherits the R3b
  `SiegelSequence` honesty discipline (strictly-stronger hypothesis, one-way, no
  branch selection smuggled — see `SiegelCorrStrong`'s honesty block).
* **Node (a1)'s structural witness.** The local Euler factor is
  `(1 + (1 + χ_ℝ(p))·ν(p))`: it is `1` when `χ(p) = −1` and `1 + 2ν(p)` when
  `χ(p) = +1`, so the twisted main sum is a product over the SPARSE `{χ = +1}`
  primes. This is exactly the mechanism a Siegel zero would exploit AND the source
  of the (a3) difficulty below.
* **Node (a2) — the L(1,χ) tail — is NOT landed here.** Identifying the finite
  product with `L(1,χ)`·(twin singular series) needs a twisted-Mertens
  finite→infinite passage; class C/D, the analytic seam, left to a later wave.
* **Node (a3) — the lower bound — is PROSE-ONLY [gate BLOCK-2].** The frozen
  `∃ cLow > 0, cLow·(L(1,χ)).re ≤ twistedMainSum` is a proven `swat_vacuous` trap
  (it follows from `0 < twistedMainSum` alone, with `cLow = M/(2L)`), so committing
  it as a Lean theorem would let O2/O3 masquerade as O1. It is therefore recorded
  ONLY as prose: the honest map is that the D-difficulty is the CONJUNCTION of
  (i) `siegel_L_one_lower_near` needing a DISTINCT target (`hdist : χ₁ ≠ χ`) — it
  does not apply to the self-same exceptional χ, whose floor is Dirichlet's √q —
  and (ii) domination of the τ-error by the `{χ=+1}`-sparse (hence `q^{−O(1)}`-small)
  main term re-colliding with the beyond-½ / Kloosterman wall. That collision IS
  the R4 death rung; node (b) below stops at level ½ (the `char_LS` τ-coverage
  ceiling) and does not budget beyond-½ error control (unreachable this sprint).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace Salt.TwinBar

/-! ## §1 — the twisted weight as a Lean object (frozen §1 defs) -/

/-- The real quadratic-character value `χ_ℝ(n) = Re χ(n) ∈ {−1,0,1}` (χ real,
    `χ² = 1`). Real-valued so the sieve weight lives in `ℝ` (the abstract
    `mainSum`/`errSum` are `ℝ`-valued). -/
noncomputable def chiRe {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  (χ (n : ZMod q)).re

/-- **The χ-twisted sieve weight** `λ_χ(d) = (χ_ℝ ∗ 1)(d) = Σ_{e∣d} χ_ℝ(e)`.
    Multiplicative (for real χ), SIGNED, and τ-bounded — `|λ_χ(d)| ≤ τ(d)`, NEVER
    `≤ 1`. This is the object that CANNOT be a `BoundingSieve.weights` (signed) nor a
    `TruncSieve.lam` (`|·| ≤ 1` fails); it lives OUTSIDE both structures. -/
noncomputable def lamChi {q : ℕ} (χ : DirichletCharacter ℂ q) (d : ℕ) : ℝ :=
  ∑ e ∈ d.divisors, chiRe χ e

/-- **The twisted main sum** `M_χ(s) = Σ_{d ∣ P} λ_χ(d)·ν(d)` — the abstract
    `mainSum` AT the signed weight (weight-generic reuse; no new bookkeeping). -/
noncomputable def twistedMainSum {q : ℕ}
    (s : BoundingSieve) (χ : DirichletCharacter ℂ q) : ℝ :=
  s.mainSum (lamChi χ)

/-- **The twisted error sum** `E_χ(s) = Σ_{d ∣ P} |λ_χ(d)|·|rem(d)|` — the abstract
    `errSum` AT the signed weight (the τ-weighted remainder, node b). -/
noncomputable def twistedErrSum {q : ℕ}
    (s : BoundingSieve) (χ : DirichletCharacter ℂ q) : ℝ :=
  s.errSum (lamChi χ)

/-! ## Multiplicativity infrastructure (helpers, node R3c-1)

`χ_ℝ` is completely multiplicative when χ is quadratic, so `λ_χ = χ_ℝ ∗ 1` is a
Dirichlet convolution of multiplicative functions. We package `χ_ℝ` as an honest
`ArithmeticFunction` [gate BLOCK-3] (guarding value `0` at `0`, so `q = 1` is fine),
convolve with `ζ`, and read off multiplicativity from mathlib. -/

/-- `χ_ℝ` bundled as an `ArithmeticFunction ℝ` (value `0` at `0`). -/
noncomputable def chiReArith {q : ℕ} (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else chiRe χ n, rfl⟩

@[simp] lemma chiReArith_apply {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    chiReArith χ n = if n = 0 then 0 else chiRe χ n := rfl

/-- `λ_χ = χ_ℝ ∗ 1` as an `ArithmeticFunction ℝ` (the convolution `ζ * χ_ℝ`). -/
noncomputable def lamChiArith {q : ℕ} (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℝ :=
  ζ * chiReArith χ

@[simp] lemma chiRe_one {q : ℕ} (χ : DirichletCharacter ℂ q) : chiRe χ 1 = 1 := by
  simp [chiRe]

/-- `χ_ℝ` is completely multiplicative when `χ² = 1` (values lie in `{−1,0,1}`). -/
lemma chiRe_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (a b : ℕ) :
    chiRe χ (a * b) = chiRe χ a * chiRe χ b := by
  have hQ : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq
  unfold chiRe
  rw [Nat.cast_mul, map_mul]
  rcases hQ ((a : ZMod q)) with h | h | h <;> rcases hQ ((b : ZMod q)) with h' | h' | h' <;>
    rw [h, h'] <;> simp

lemma chiReArith_mult {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) :
    (chiReArith χ).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [chiReArith_apply, if_neg one_ne_zero, chiRe_one]
  · intro m n hm hn _
    rw [chiReArith_apply, if_neg (Nat.mul_ne_zero hm hn), chiReArith_apply, if_neg hm,
        chiReArith_apply, if_neg hn]
    exact chiRe_mul χ hsq m n

lemma lamChiArith_mult {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) :
    (lamChiArith χ).IsMultiplicative := by
  unfold lamChiArith
  exact ArithmeticFunction.isMultiplicative_zeta.natCast.mul (chiReArith_mult χ hsq)

/-- The bundled convolution agrees with `λ_χ` at every argument. -/
lemma lamChiArith_apply {q : ℕ} (χ : DirichletCharacter ℂ q) (d : ℕ) :
    lamChiArith χ d = lamChi χ d := by
  unfold lamChiArith lamChi
  rw [coe_zeta_mul_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [chiReArith_apply, if_neg (Nat.pos_of_mem_divisors hi).ne']

/-- `λ_χ(p) = 1 + χ_ℝ(p)` at a prime (divisors of `p` are `{1, p}`). -/
lemma lamChi_prime {q : ℕ} (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : p.Prime) :
    lamChi χ p = 1 + chiRe χ p := by
  unfold lamChi
  rw [hp.divisors, Finset.sum_pair hp.one_lt.ne, chiRe_one]

/-- **Node R3c-1 (the load-bearing multiplicativity, BLOCK-1 + BLOCK-3).** For a
    real (`χ² = 1`) character, `λ_χ` is multiplicative on coprime arguments. Stated
    as the coprime-product equation (the directly-usable form for node a1). The
    reality hypothesis is REQUIRED: for complex χ, `Re(χ(m)χ(n)) ≠ Re χ(m)·Re χ(n)`
    and `λ_χ` fails to factor. -/
lemma lamChi_mult {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) :
    ∀ m n, Nat.Coprime m n → lamChi χ (m * n) = lamChi χ m * lamChi χ n := by
  intro m n hcop
  have h := (lamChiArith_mult χ hsq).map_mul_of_coprime hcop
  rwa [lamChiArith_apply, lamChiArith_apply, lamChiArith_apply] at h

/-! ## §2 — node (b): the τ-weighted remainder (stops at level ½)

`λ_χ` is τ-bounded, not `1`-bounded: `|λ_χ(d)| ≤ τ(d)`. This is the signed-weight
replacement for `abs_lam_le_one`, and it needs NO reality hypothesis — the bound is
a boundedness (`|Re χ| ≤ ‖χ‖ ≤ 1`) fact, not a multiplicativity one [gate BLOCK-1].
The τ-weighted Rosser remainder that follows is controlled to level ½ by the
corpus's `char_LS`; pushing it past ½ is the Kloosterman wall (R4), not budgeted. -/

/-- **(b.1)** `|λ_χ(d)| ≤ τ(d)` — the signed-weight replacement for `abs_lam_le_one`.
    No reality hypothesis (this is `|Re χ| ≤ ‖χ‖ ≤ 1` termwise, true for any χ). -/
lemma abs_lamChi_le_tau {q : ℕ} (χ : DirichletCharacter ℂ q) (d : ℕ) :
    |lamChi χ d| ≤ (d.divisors.card : ℝ) := by
  have hb : ∀ e : ℕ, |chiRe χ e| ≤ 1 := by
    intro e
    calc |chiRe χ e| = |(χ (e : ZMod q)).re| := rfl
      _ ≤ ‖χ (e : ZMod q)‖ := Complex.abs_re_le_norm _
      _ ≤ 1 := χ.norm_le_one _
  unfold lamChi
  calc |∑ e ∈ d.divisors, chiRe χ e|
      ≤ ∑ e ∈ d.divisors, |chiRe χ e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ d.divisors, (1 : ℝ) := Finset.sum_le_sum fun e _ => hb e
    _ = (d.divisors.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **(b.2)** `E_χ(s) ≤ Σ_{d∣P, d<bound} τ(d)·|rem(d)|` — the τ-weighted Rosser
    remainder, the signed analogue of `errSum_lam_le` with `τ(d)` for `1`. `λ_χ` is
    full-support on `divisors P`, so the only hypothesis is the level cap. -/
lemma twistedErrSum_le_tauRemainder {q : ℕ}
    (s : BoundingSieve) (χ : DirichletCharacter ℂ q) {bound : ℝ}
    (hsupp : ∀ d, d ∣ s.prodPrimes → (d : ℝ) < bound) :
    twistedErrSum s χ ≤ ∑ d ∈ s.prodPrimes.divisors,
      if (d : ℝ) < bound then (d.divisors.card : ℝ) * |s.rem d| else 0 := by
  unfold twistedErrSum
  rw [BoundingSieve.errSum]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [if_pos (hsupp d (Nat.dvd_of_mem_divisors hd))]
  exact mul_le_mul_of_nonneg_right (abs_lamChi_le_tau χ d) (abs_nonneg _)

/-! ## §3 — node (a1): the sparse-product Euler factorization (BLOCK-1)

Since `P` is squarefree and `λ_χ(d)·ν(d)` is multiplicative (for real χ), the twisted
main sum FACTORS over prime factors. The local factor `1 + (1 + χ_ℝ(p))·ν(p)` is `1`
exactly when `χ(p) = −1`, so the sum is a product over the SPARSE `{χ = +1}` primes —
the Siegel-zero mechanism and the (a3) death source (see the module honesty block). -/

/-- **(a1)** `M_χ(s) = ∏_{p∣P} (1 + (1 + χ_ℝ(p))·ν(p))` [gate BLOCK-1: `χ² = 1`
    is REQUIRED — the factorization is false for complex χ]. -/
theorem twistedMainSum_euler {q : ℕ}
    (s : BoundingSieve) (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) :
    twistedMainSum s χ
      = ∏ p ∈ s.prodPrimes.primeFactors, (1 + (1 + chiRe χ p) * s.nu p) := by
  have hg : (ArithmeticFunction.pmul (lamChiArith χ) s.nu).IsMultiplicative :=
    (lamChiArith_mult χ hsq).pmul s.nu_mult
  have hsum := hg.prodPrimeFactors_one_add_of_squarefree s.prodPrimes_squarefree
  calc twistedMainSum s χ
      = ∑ d ∈ s.prodPrimes.divisors, (ArithmeticFunction.pmul (lamChiArith χ) s.nu) d := by
        unfold twistedMainSum
        rw [BoundingSieve.mainSum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [ArithmeticFunction.pmul_apply, lamChiArith_apply]
    _ = ∏ p ∈ s.prodPrimes.primeFactors,
          (1 + (ArithmeticFunction.pmul (lamChiArith χ) s.nu) p) := hsum.symm
    _ = ∏ p ∈ s.prodPrimes.primeFactors, (1 + (1 + chiRe χ p) * s.nu p) := by
        refine Finset.prod_congr rfl fun p hp => ?_
        rw [ArithmeticFunction.pmul_apply, lamChiArith_apply,
            lamChi_prime χ (Nat.prime_of_mem_primeFactors hp)]

end Salt.TwinBar

