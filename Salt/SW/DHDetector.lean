/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The Deuring–Heilbronn detector foundation — the `1∗χ` divisor sum (HB-ENGINE, WP2, node DH-1)

Design: `docs/exploration/s3-hb3-design.md`, "THE WP2 NODE TABLE — FROZEN" (DH-1),
under the HB-ENGINE campaign (`SiegelSequence`/`InfinitelyManySiegelZeros ⟹
TwinPrimeConjecture`, Heath-Brown 1983, formal-first). This module lands the
foundation of the reversed-form soft-Perron detector: the real-valued divisor sum

  `a(n) = dhA χ n = Σ_{d ∣ n} χ_ℝ(d) = (1 ∗ χ_ℝ)(n)`   (`χ_ℝ = Re ∘ χ`, χ real),

its basic API, the **positivity floor** (`dhA_nonneg`, the load-bearing `1∗χ`
positivity the elementary detector consumes — the Siegel skeleton's own pattern),
the **square floor** (`dhA_square_ge_one`), the **mass floor** (`dhA_mass_floor`:
`Σ_{n≤N} a(n) ≥ √N − 1`), and the **log-average floor** toward `L(1,χ)`.

## Convention (mirrored, not imported)

`χ_ℝ = chiRe` and `a = dhA` reuse the corpus convention (`Salt.TwinBar.chiRe` /
`Salt.TwinBar.lamChi` in `TwistedSieve.lean`, and the HB geometric-block positivity
of `Salt.HB.TwistChain`). Those live in `Salt.TwinBar` / `Salt.HB`, which sit ABOVE
`Salt.SW` in the import graph (`TwistedSieve` imports `SiegelCorrStrong`, which imports
SW). So this SW-level file **re-declares** the same definitional shapes in namespace
`Salt.SW` to avoid a dependency inversion; a downstream bridge `Salt.SW.dhA χ =
Salt.TwinBar.lamChi χ` is definitional and cheap where needed.

## The `L(1,χ)` seam (documented for DH-4)

DH-4 combines this floor with the DH-2 damping to squeeze `L(1,χ)`. The relevant
objects here:

* `dhA_mass_floor` / `dhA_mass_floor_real`: `Σ_{n≤N} a(n) ≥ √N − 1` (the classical
  square-support floor — parity-free, holds for any real χ).
* `dhA_log_average_floor`: `Σ_{n≤N} a(n)/n ≥ 1` (an explicit positive constant; the
  `n = 1` term plus termwise nonnegativity). The sharper `Σ_{n≤N} a(n)/n ≥
  Σ_{m≤√N} 1/m²` refinement rides on the same square support and is recorded in
  `dhA_log_average_square_floor`.
* `dhA_hyperbola`: the EXACT hyperbola identity `Σ_{n≤N} a(n) = Σ_{d≤N} χ_ℝ(d)·⌊N/d⌋`
  — the seam through which DH-4 links `Σ_{d≤N} χ_ℝ(d)/d → L(1,χ)` (Tao's (9), the
  main asymptotic of the twisted Dirichlet sum).
* `dhLSeries_target` (definition + docstring, NOT a theorem): the Dirichlet-series
  target `Σ a(n) n^{-s} = ζ(s)·L(s,χ)`. Landing the composed `LSeries` identity is
  DEFERRED to DH-2 (the contour node) — see its docstring for why (real-vs-complex
  bridge + `LSeries` convolution assembly). This is the Mellin seam.

## Honesty / death map (HB-ENGINE, R4 — no twin claim)

* **This is NOT a proof of the Twin Prime Conjecture.** The deliverable is the
  detector foundation; the campaign target is the conditional
  `InfinitelyManySiegelZeros → TwinPrimeConjecture` (the landed `HeathBrownStatement`
  shape), a strictly-conditional bridge, no branch smuggled.
* **The predicted death rung is R4** (beyond-level-½ / Kloosterman error control):
  the detector supplies the parity-break floor, but the distribution input past
  level ½ is the documented wall. This node stops at the elementary floor; the
  analytic linkage (`L(1,χ)` squeeze, the density/repulsion machinery) is WP2's
  later nodes (DH-2..4 and the Jutila/D-H core).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace Salt.SW

variable {q : ℕ}

/-! ## §0 — the real character value `χ_ℝ` and geometric-sum helpers

Mirrors `Salt.TwinBar.chiRe` and the `Salt.HB.TwistChain` geometric-block positivity
(re-declared here for the SW import level; see the module header). -/

/-- The real quadratic-character value `χ_ℝ(n) = Re χ(n)` (∈ `{−1,0,1}` for χ real). -/
noncomputable def chiRe (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ := (χ (n : ZMod q)).re

@[simp] lemma chiRe_one (χ : DirichletCharacter ℂ q) : chiRe χ 1 = 1 := by simp [chiRe]

/-- `|χ_ℝ(n)| ≤ 1` (termwise `|Re χ| ≤ ‖χ‖ ≤ 1`; no reality hypothesis). -/
lemma chiRe_abs_le_one (χ : DirichletCharacter ℂ q) (n : ℕ) : |chiRe χ n| ≤ 1 :=
  calc |chiRe χ n| = |(χ (n : ZMod q)).re| := rfl
    _ ≤ ‖χ (n : ZMod q)‖ := Complex.abs_re_le_norm _
    _ ≤ 1 := χ.norm_le_one _

/-- `χ_ℝ` is completely multiplicative when `χ² = 1` (values in `{−1,0,1}`). -/
lemma chiRe_mul (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (a b : ℕ) :
    chiRe χ (a * b) = chiRe χ a * chiRe χ b := by
  have hQ : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq
  unfold chiRe
  rw [Nat.cast_mul, map_mul]
  rcases hQ ((a : ZMod q)) with h | h | h <;> rcases hQ ((b : ZMod q)) with h' | h' | h' <;>
    rw [h, h'] <;> simp

/-- `χ_ℝ(a^k) = χ_ℝ(a)^k` (needs `χ² = 1`). -/
lemma chiRe_pow (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (a k : ℕ) :
    chiRe χ (a ^ k) = (chiRe χ a) ^ k := by
  induction k with
  | zero => simp [chiRe_one]
  | succ k ih => rw [pow_succ, chiRe_mul χ hsq, ih, pow_succ]

/-- For real χ (`χ² = 1`), `χ_ℝ(n) ∈ {0, 1, −1}`. -/
lemma chiRe_values (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    chiRe χ n = 0 ∨ chiRe χ n = 1 ∨ chiRe χ n = -1 := by
  have hQ : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq
  rcases hQ (n : ZMod q) with h | h | h
  · left; simp [chiRe, h]
  · right; left; simp [chiRe, h]
  · right; right; simp [chiRe, h]

/-- A geometric sum with ratio bounded by `1` in absolute value is nonnegative. -/
lemma geomSum_nonneg {r : ℝ} (hr : |r| ≤ 1) (m : ℕ) : 0 ≤ ∑ k ∈ range m, r ^ k := by
  rcases eq_or_ne r 1 with h | h
  · subst h; simp
  · rw [geom_sum_eq h]
    have hr1 : r < 1 := lt_of_le_of_ne (abs_le.mp hr).2 h
    have hrm : r ^ m ≤ 1 :=
      le_trans (le_abs_self _) (by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hr)
    rw [div_nonneg_iff]; right; exact ⟨by linarith, by linarith⟩

/-- A geometric block over an EVEN exponent, ratio in `{0,1,−1}`, is `≥ 1`. The square
    floor's engine: `Σ_{j≤2e} r^j = 1` for `r ∈ {0,−1}` and `= 2e+1` for `r = 1`. -/
lemma geomSum_sq_ge_one {r : ℝ} (hr : r = 0 ∨ r = 1 ∨ r = -1) (e : ℕ) :
    1 ≤ ∑ j ∈ range (2 * e + 1), r ^ j := by
  rcases hr with h | h | h
  · subst h
    have : ∑ j ∈ range (2 * e + 1), (0 : ℝ) ^ j = 1 := by
      rw [Finset.sum_range_succ']; simp
    rw [this]
  · subst h
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast Nat.le_add_left 1 (2 * e)
  · subst h
    have hne : ¬ Even (2 * e + 1) := by simp
    simp [neg_one_geom_sum, hne]

/-! ## §1 — the detector `a(n) = dhA χ n = Σ_{d ∣ n} χ_ℝ(d)` -/

/-- The Deuring–Heilbronn detector `a(n) = (1 ∗ χ_ℝ)(n) = Σ_{d ∣ n} χ_ℝ(d)`. -/
noncomputable def dhA (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ := ∑ d ∈ n.divisors, chiRe χ d

@[simp] lemma dhA_one (χ : DirichletCharacter ℂ q) : dhA χ 1 = 1 := by simp [dhA]

/-- At a prime power, `a(p^k) = Σ_{j≤k} χ_ℝ(p)^j` — the geometric block. -/
lemma dhA_prime_pow (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    dhA χ (p ^ k) = ∑ j ∈ range (k + 1), (chiRe χ p) ^ j := by
  unfold dhA
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [chiRe_pow χ hsq]

/-! ### Multiplicativity bundle (for the factorization behind the floors)

`χ_ℝ` is completely multiplicative (χ real), so `a = χ_ℝ ∗ 1 = ζ * χ_ℝ` is a
convolution of multiplicative functions, hence multiplicative. Packaged as an
`ArithmeticFunction` [the mathlib factorization vehicle]. -/

/-- `χ_ℝ` bundled as an `ArithmeticFunction ℝ` (value `0` at `0`). -/
noncomputable def chiReArith (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else chiRe χ n, rfl⟩

@[simp] lemma chiReArith_apply (χ : DirichletCharacter ℂ q) (n : ℕ) :
    chiReArith χ n = if n = 0 then 0 else chiRe χ n := rfl

lemma chiReArith_mult (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) :
    (chiReArith χ).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [chiReArith_apply, if_neg one_ne_zero, chiRe_one]
  · intro m n hm hn _
    rw [chiReArith_apply, if_neg (Nat.mul_ne_zero hm hn), chiReArith_apply, if_neg hm,
        chiReArith_apply, if_neg hn]
    exact chiRe_mul χ hsq m n

/-- `a = ζ * χ_ℝ` as an `ArithmeticFunction ℝ`. -/
noncomputable def dhAArith (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℝ :=
  ζ * chiReArith χ

lemma dhAArith_mult (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) :
    (dhAArith χ).IsMultiplicative := by
  unfold dhAArith
  exact ArithmeticFunction.isMultiplicative_zeta.natCast.mul (chiReArith_mult χ hsq)

/-- The bundle agrees with `dhA` at every argument. -/
lemma dhAArith_apply (χ : DirichletCharacter ℂ q) (n : ℕ) : dhAArith χ n = dhA χ n := by
  unfold dhAArith dhA
  rw [coe_zeta_mul_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [chiReArith_apply, if_neg (Nat.pos_of_mem_divisors hi).ne']

/-! ## §2 — the positivity floor and the square floor -/

/-- At a prime power, `a(p^k) ≥ 0` (the geometric block is nonnegative). -/
lemma dhA_prime_pow_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : 0 ≤ dhA χ (p ^ k) := by
  rw [dhA_prime_pow χ hsq hp]
  exact geomSum_nonneg (chiRe_abs_le_one χ p) _

/-- **The `1∗χ` positivity floor.** For χ real (`χ² = 1`) and `n ≠ 0`, `a(n) ≥ 0`.
    Multiplicativity + the per-prime-power geometric block `Σ_{j≤k} χ_ℝ(p)^j ≥ 0`
    (the Siegel skeleton's own pattern; the load-bearing detector primitive). -/
lemma dhA_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ} (hn : n ≠ 0) :
    0 ≤ dhA χ n := by
  rw [← dhAArith_apply χ n,
      (dhAArith_mult χ hsq).multiplicative_factorization (dhAArith χ) hn, Finsupp.prod]
  refine Finset.prod_nonneg fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)
  rw [dhAArith_apply]
  exact dhA_prime_pow_nonneg χ hsq hpp _

/-- **The square floor.** For χ real and `m ≥ 1`, `a(m²) ≥ 1`: every geometric block
    over `m²` has an EVEN exponent, and `Σ_{j≤2e} χ_ℝ(p)^j ≥ 1` for `χ_ℝ(p) ∈ {0,1,−1}`
    (`χ_ℝ(p) = −1`: alternating sum over an odd length `= 1`; `= 0`: `= 1`; `= 1`:
    `= 2e+1`). This is the source of the mass floor `√N`. -/
lemma dhA_square_ge_one (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ}
    (hm : 1 ≤ m) : 1 ≤ dhA χ (m ^ 2) := by
  have hm0 : m ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  rw [← dhAArith_apply χ (m ^ 2),
      (dhAArith_mult χ hsq).multiplicative_factorization (dhAArith χ) hm0, Finsupp.prod]
  calc (1 : ℝ) = ∏ _p ∈ (m ^ 2).factorization.support, (1 : ℝ) := by rw [Finset.prod_const_one]
    _ ≤ ∏ p ∈ (m ^ 2).factorization.support, dhAArith χ (p ^ (m ^ 2).factorization p) := by
        refine Finset.prod_le_prod (fun _ _ => zero_le_one) (fun p hp => ?_)
        have hpp : p.Prime :=
          Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)
        have hev : (m ^ 2).factorization p = 2 * m.factorization p := by
          rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        rw [dhAArith_apply, dhA_prime_pow χ hsq hpp, hev]
        exact geomSum_sq_ge_one (chiRe_values χ hsq p) _

/-! ## §3 — the mass floor `Σ_{n≤N} a(n) ≥ √N − 1` -/

/-- **The mass floor (`Nat.sqrt` form).** `Σ_{n≤N} a(n) ≥ ⌊√N⌋`. All `a(n) ≥ 0`
    (positivity floor), so the full sum dominates its restriction to the perfect
    squares `m² ≤ N` (`m ≤ ⌊√N⌋`), each of which contributes `a(m²) ≥ 1`. -/
lemma dhA_mass_floor (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (N : ℕ) :
    (Nat.sqrt N : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, dhA χ n := by
  have hsub : (Finset.Icc 1 (Nat.sqrt N)).image (fun m => m ^ 2) ⊆ Finset.Icc 1 N := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Icc] at hx
    obtain ⟨m, ⟨hm1, hmM⟩, rfl⟩ := hx
    rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_pow _ _ (by omega), ?_⟩
    calc m ^ 2 ≤ Nat.sqrt N ^ 2 := Nat.pow_le_pow_left hmM 2
      _ ≤ N := Nat.sqrt_le' N
  calc (Nat.sqrt N : ℝ)
      = ∑ _m ∈ Finset.Icc 1 (Nat.sqrt N), (1 : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
    _ ≤ ∑ m ∈ Finset.Icc 1 (Nat.sqrt N), dhA χ (m ^ 2) := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mem_Icc] at hm
        exact dhA_square_ge_one χ hsq hm.1
    _ = ∑ x ∈ (Finset.Icc 1 (Nat.sqrt N)).image (fun m => m ^ 2), dhA χ x :=
        (Finset.sum_image (fun a _ b _ hab => Nat.pow_left_injective (by norm_num) hab)).symm
    _ ≤ ∑ n ∈ Finset.Icc 1 N, dhA χ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n hn _ => dhA_nonneg χ hsq (by rw [Finset.mem_Icc] at hn; omega))

/-- **The mass floor (`Real.sqrt` form).** `Σ_{n≤N} a(n) ≥ √N − 1` — the classical
    floor, parity-free (holds for any real χ). The `L(1,χ)` seam consumes this. -/
lemma dhA_mass_floor_real (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (N : ℕ) :
    Real.sqrt N - 1 ≤ ∑ n ∈ Finset.Icc 1 N, dhA χ n := by
  have hlt : Real.sqrt N < (Nat.sqrt N : ℝ) + 1 := by
    have h1 : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
      have h2 := Nat.lt_succ_sqrt N
      have : (N : ℝ) < (Nat.sqrt N + 1 : ℕ) * (Nat.sqrt N + 1 : ℕ) := by exact_mod_cast h2
      push_cast at this; nlinarith [this]
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N), Real.sqrt_nonneg (N : ℝ),
      Nat.cast_nonneg (α := ℝ) (Nat.sqrt N)]
  linarith [dhA_mass_floor χ hsq N]

/-! ## §4 — the log-average floor (toward `L(1,χ)`) -/

/-- **The log-average floor.** For `N ≥ 1`, `Σ_{n≤N} a(n)/n ≥ 1` (the `n = 1` term
    `a(1)/1 = 1` plus termwise nonnegativity). Any explicit positive constant suffices
    for the DH-4 squeeze; the sharper `Σ 1/m²` refinement is `dhA_log_average_square_floor`. -/
lemma dhA_log_average_floor (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {N : ℕ}
    (hN : 1 ≤ N) : 1 ≤ ∑ n ∈ Finset.Icc 1 N, dhA χ n / (n : ℝ) := by
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 N := by rw [Finset.mem_Icc]; omega
  have hnn : ∀ n ∈ Finset.Icc 1 N, 0 ≤ dhA χ n / (n : ℝ) := by
    intro n hn; rw [Finset.mem_Icc] at hn
    exact div_nonneg (dhA_nonneg χ hsq (by omega)) (by positivity)
  calc (1 : ℝ) = dhA χ 1 / ((1 : ℕ) : ℝ) := by rw [dhA_one]; norm_num
    _ ≤ ∑ n ∈ Finset.Icc 1 N, dhA χ n / (n : ℝ) := Finset.single_le_sum hnn h1mem

/-- **The sharper log-average floor.** `Σ_{n≤N} a(n)/n ≥ Σ_{m≤√N} 1/m²` — the square
    support with weight `1/n` (each square `m² ≤ N` contributes `a(m²)/m² ≥ 1/m²`, all
    other terms `≥ 0`). Refines `dhA_log_average_floor` toward the `L(1,χ)` seam. -/
lemma dhA_log_average_square_floor (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 (Nat.sqrt N), 1 / ((m ^ 2 : ℕ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 N, dhA χ n / (n : ℝ) := by
  have hsub : (Finset.Icc 1 (Nat.sqrt N)).image (fun m => m ^ 2) ⊆ Finset.Icc 1 N := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Icc] at hx
    obtain ⟨m, ⟨hm1, hmM⟩, rfl⟩ := hx
    rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_pow _ _ (by omega), ?_⟩
    calc m ^ 2 ≤ Nat.sqrt N ^ 2 := Nat.pow_le_pow_left hmM 2
      _ ≤ N := Nat.sqrt_le' N
  calc ∑ m ∈ Finset.Icc 1 (Nat.sqrt N), 1 / ((m ^ 2 : ℕ) : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 (Nat.sqrt N), dhA χ (m ^ 2) / ((m ^ 2 : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mem_Icc] at hm
        have h1 : (1 : ℝ) ≤ dhA χ (m ^ 2) := dhA_square_ge_one χ hsq hm.1
        have hpos : (0 : ℝ) < ((m ^ 2 : ℕ) : ℝ) := by
          exact_mod_cast Nat.one_le_pow 2 m (by omega)
        gcongr
    _ = ∑ x ∈ (Finset.Icc 1 (Nat.sqrt N)).image (fun m => m ^ 2), dhA χ x / (x : ℝ) := by
        rw [Finset.sum_image
          (fun a _ b _ hab => Nat.pow_left_injective (n := 2) (by norm_num) hab)]
    _ ≤ ∑ n ∈ Finset.Icc 1 N, dhA χ n / (n : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ =>
          div_nonneg (dhA_nonneg χ hsq (by rw [Finset.mem_Icc] at hn; omega)) (by positivity)

/-! ## §5 — the hyperbola identity (the `L(1,χ)` seam) -/

/-- **The hyperbola identity.** `Σ_{n≤N} a(n) = Σ_{d≤N} χ_ℝ(d)·⌊N/d⌋` — the exact
    Dirichlet hyperbola: each `d` contributes `χ_ℝ(d)` once for every multiple `n ≤ N`
    of `d`, and there are `⌊N/d⌋` such. This is the seam DH-4 uses to link the partial
    sums `Σ_{d≤N} χ_ℝ(d)/d` to `L(1,χ)` (Tao's (9) main asymptotic). No reality
    hypothesis (pure reindexing). -/
lemma dhA_hyperbola (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, dhA χ n
      = ∑ d ∈ Finset.Icc 1 N, chiRe χ d * ((N / d : ℕ) : ℝ) := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; rw [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hstep : ∀ n ∈ Finset.Icc 1 N,
      dhA χ n = ∑ d ∈ Finset.Icc 1 N, (if d ∣ n then chiRe χ d else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hset : n.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ n) := by
      ext d
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) hn.2⟩, hdvd⟩
      · rintro ⟨_, hdvd⟩; exact ⟨hdvd, by omega⟩
    unfold dhA
    rw [hset, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hIcc,
      Nat.Ioc_filter_dvd_card_eq_div, mul_comm]

/-! ## §6 — the Mellin seam (interface only; contour work is DH-2)

The Dirichlet-series identity `Σ a(n) n^{-s} = ζ(s)·L(s,χ)` is the analytic content
DH-2 exploits (the reversed-form soft-Perron / contour node). It is recorded HERE as
a target `Prop`, NOT proved: the composed `LSeries` identity needs (i) the real→complex
bridge `(chiRe χ n : ℂ) = χ(n)` for quadratic χ (values in `{−1,0,1} ⊂ ℝ`), and then
(ii) the `LSeries` convolution assembly `LSeries (f ∗ g) = LSeries f · LSeries g` with
`f = 1` (`ζ`) and `g = χ` (`L(·,χ)`). Both are available in mathlib but the assembly
exceeds this node's foundational scope; it is amortized into DH-2's explicit-formula
rebuild (catch #47) per the WP2 node table. -/

/-- **The Mellin seam (target, DH-2).** The Dirichlet series of the detector equals
    `ζ(s)·L(s,χ)`. A documented target `Prop`, not a theorem — see the §6 header. -/
noncomputable def dhLSeries_target [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : Prop :=
  LSeries (fun n => (dhA χ n : ℂ)) s = riemannZeta s * DirichletCharacter.LFunction χ s

end Salt.SW
